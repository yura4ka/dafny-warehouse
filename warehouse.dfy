datatype Property = Fragile | Hazardous | Cold

class Item {
  var id: nat
  var weight: int
  var volume: int
  var properties: set<Property>

  constructor(id: nat, weight: int, volume: int, properties: set<Property>)
    requires weight > 0 && volume > 0
    ensures Valid()
    ensures this.id == id
    ensures this.weight == weight
    ensures this.volume == volume
    ensures this.properties == properties
  {
    this.id := id;
    this.weight := weight;
    this.volume := volume;
    this.properties := properties;
  }

  predicate Valid()
    reads this
  {
    this.weight > 0 && this.volume > 0
  }
}

class Cell {
  var id: nat
  var maxWeight: int
  var maxVolume: int
  var permittedProps: set<Property>
  var item: Item?

  constructor (id: nat, maxWeight: int, maxVolume: int, permittedProps: set<Property>)
    requires maxWeight > 0 && maxVolume > 0
    ensures Valid()
    ensures this.id == id
    ensures this.maxWeight == maxWeight
    ensures this.maxVolume == maxVolume
    ensures this.permittedProps == permittedProps
    ensures item == null
  {
    this.id := id;
    this.maxWeight := maxWeight;
    this.maxVolume := maxVolume;
    this.permittedProps := permittedProps;
    this.item := null;
  }

  ghost predicate ValidItem()
    reads this, item
  {
    item != null ==> item.Valid()
  }

  ghost predicate ValidConstraints()
    reads this, item
  {
    if item != null
    then 0 < item.weight <= maxWeight && 0 < item.volume <= maxVolume
    else maxWeight > 0 && maxVolume > 0
  }

  ghost predicate ValidProps()
    reads this, item
  {
    item != null ==> item.properties <= permittedProps
  }

  ghost predicate Valid()
    reads this, item
  {
    ValidItem() &&
    ValidConstraints() &&
    ValidProps()
  }

  predicate CellCanAccept(newItem: Item)
    reads this, newItem
  {
    item == null &&
    newItem.Valid() &&
    newItem.properties <= permittedProps &&
    newItem.weight <= maxWeight &&
    newItem.volume <= maxVolume
  }

  method AddItem(item: Item)
    requires Valid()
    requires CellCanAccept(item)
    ensures Valid()
    ensures this.item != null
    ensures this.item == item
    ensures this.id == old(this.id)
    ensures this.maxWeight == old(this.maxWeight)
    ensures this.maxVolume == old(this.maxVolume)
    ensures this.permittedProps == old(this.permittedProps)
    modifies this
  {
    this.item := item;
  }

  method RemoveItem() returns (oldItem: Item)
    requires Valid()
    requires item != null
    ensures Valid()
    ensures item == null
    ensures oldItem == old(this.item)
    ensures this.id == old(this.id)
    ensures this.maxWeight == old(this.maxWeight)
    ensures this.maxVolume == old(this.maxVolume)
    ensures this.permittedProps == old(this.permittedProps)
    modifies this
  {
    oldItem := this.item;
    this.item := null;
  }
}

class Warehouse {
  var cells: seq<Cell>

  constructor(cells: seq<Cell>)
    requires |cells| > 0
    requires forall i, j :: 0 <= i < j < |cells| ==> cells[i].id != cells[j].id
    requires forall i :: 0 <= i < |cells| ==> cells[i].Valid() && cells[i].item == null
    ensures Valid()
    ensures this.cells == cells
  {
    this.cells := cells;
  }

  ghost predicate DistinctCells()
    reads this,
          set i | 0 <= i < |cells| :: cells[i]
  {
    forall i, j :: 0 <= i < j < |cells| ==> cells[i].id != cells[j].id
  }

  ghost predicate NoDuplicateIds()
    reads this,
          set i | 0 <= i < |cells| :: cells[i],
          set i | 0 <= i < |cells| && cells[i].item != null :: cells[i].item
  {
    forall i, j :: 0 <= i < j < |cells| ==>
                     cells[i].item != null && cells[j].item != null ==> cells[i].item.id != cells[j].item.id
  }

  ghost predicate Valid()
    reads this,
          set i | 0 <= i < |cells| :: cells[i],
          set i | 0 <= i < |cells| && cells[i].item != null :: cells[i].item
  {
    |cells| > 0 &&
    (forall i :: 0 <= i < |cells| ==> cells[i].Valid()) &&
    DistinctCells() &&
    NoDuplicateIds()
  }

  method AddItem(newItem: Item) returns (added: bool)
    requires newItem.Valid()
    requires forall i :: 0 <= i < |cells| ==> cells[i].item == null || cells[i].item.id != newItem.id
    requires Valid()
    ensures Valid()
    ensures forall i :: 0 <= i < |cells| ==> cells[i].item == old(cells[i].item) || cells[i].item == newItem
    ensures added ==> exists i :: 0 <= i < |cells| && cells[i].item == newItem
    ensures !added ==> forall i :: 0 <= i < |cells| ==> !cells[i].CellCanAccept(newItem)
    modifies set i | 0 <= i < |cells| :: cells[i]
  {
    var i := 0;
    while i < |cells|
      invariant 0 <= i <= |cells|
      invariant forall j :: 0 <= j < |cells| ==> cells[j].Valid()
      invariant DistinctCells()
      invariant NoDuplicateIds()
      invariant forall j :: 0 <= j < i ==> !cells[j].CellCanAccept(newItem)
    {
      if cells[i].CellCanAccept(newItem) {
        cells[i].AddItem(newItem);
        added := true;
        return;
      }
      i := i + 1;
    }
    added := false;
  }

  method RemoveItem(itemId: nat) returns (removedItem: Item?)
    requires Valid()
    ensures DistinctCells()
    ensures Valid()
    ensures removedItem != null ==> removedItem.id == itemId
    ensures removedItem == null ==> forall i :: 0 <= i < |cells| ==> cells[i].item == null || cells[i].item.id != itemId
    ensures forall i :: 0 <= i < |cells| ==> cells[i].item == null || cells[i].item.id != itemId
    modifies set i | 0 <= i < |cells| :: cells[i]
  {
    removedItem := null;
    var i := 0;
    while i < |cells|
      invariant 0 <= i <= |cells|
      invariant forall j :: 0 <= j < |cells| ==> cells[j].Valid()
      invariant DistinctCells()
      invariant NoDuplicateIds()
      invariant removedItem != null ==> removedItem.Valid() && removedItem.id == itemId
      invariant forall j :: 0 <= j < i ==> cells[j].item == null || cells[j].item.id != itemId
      modifies set k | 0 <= k < |cells| :: cells[k]
    {
      if cells[i].item != null && cells[i].item.id == itemId {
        removedItem := cells[i].RemoveItem();
      }
      i := i + 1;
    }
  }

  method FindItemCell(itemId: nat) returns (index: int)
    requires Valid()
    ensures -1 <= index < |cells|
    ensures index >= 0 ==> cells[index].item != null && cells[index].item.id == itemId
    ensures index == -1 ==> forall i :: 0 <= i < |cells| ==> cells[i].item == null || cells[i].item.id != itemId
  {
    index := -1;
    var i := 0;
    while i < |cells| && index == -1
      invariant 0 <= i <= |cells|
      invariant -1 <= index < |cells|
      invariant index >= 0 ==> 0 <= index < i && cells[index].item != null && cells[index].item.id == itemId
      invariant index == -1 ==> forall j :: 0 <= j < i ==> cells[j].item == null || cells[j].item.id != itemId
    {
      if cells[i].item != null && cells[i].item.id == itemId {
        index := i;
      }
      i := i + 1;
    }
  }
}

method Main() {
  var cellA := new Cell(1, 15, 10, {Fragile, Cold});
  var cellB := new Cell(2, 30, 20, {Cold, Hazardous});
  var warehouse := new Warehouse([cellA, cellB]);

  var item1 := new Item(101, 10, 5, {Fragile});

  var before := warehouse.FindItemCell(item1.id);
  print "Item 101 before add: ", before, "\n";

  var added1 := warehouse.AddItem(item1);
  print "Add item 101: ", added1, "\n";

  var item2 := new Item(102, 100, 100, {Cold});
  var added2 := warehouse.AddItem(item2);
  print "Add item 102: ", added2, "\n";

  var index1 := warehouse.FindItemCell(101);
  print "Item 101 is in cell index: ", index1, "\n";

  var removed1 := warehouse.RemoveItem(item1.id);
  print "Remove item 101: ", removed1 != null, "\n";


  var indexAfterRemoval := warehouse.FindItemCell(101);
  print "Item 101 after removal: ", indexAfterRemoval, "\n";
}

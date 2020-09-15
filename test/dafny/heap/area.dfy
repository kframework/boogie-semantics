class Rectangle {
  
    var x: int; 
    var y: int; 

    constructor Init(x: int, y: int) 
        ensures this.x == x
        ensures this.y == y
    {
        this.x := x; 
        this.y := y;
    }
    
    method area() returns (a: int) ensures a == this.x * this.y {
        a := this.x * this.y;
    }

}

method Main() {
    var r: Rectangle := new Rectangle.Init(4, 5);
    var a: int := r.area();
    assert a == 20;
}

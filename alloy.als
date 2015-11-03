abstract sig User{
	username : MString,
	mail : MString
}{
	username != mail
}

sig MString{}
sig Float{}

sig Position{
	x : Float,
	y : Float
}

abstract sig Customer extends User{}
abstract sig Boolean{}
one sig True extends Boolean {}
one sig False extends Boolean {}

sig Passenger extends Customer{}

sig TaxiDriver extends User{
	available : Boolean
}

sig Ride{
	start : one Position,
	destinations : some Position,
	transport : set Passenger,
	hasDriver : one TaxiDriver
}{
	all d:destinations | different[d, start] = True
}

sig Queue{
	contains : set TaxiDriver
}

one sig QueueManager{
	manage : set Queue
}

fact {
	Passenger = Customer
}

fact {
	User = TaxiDriver + Customer
}

fact{
	all u,w : User | (u.username = w.username or u.mail = w.mail) iff u=w
}

fact{
	all m: MString | ( one u:User | (u.username = m or u.mail = m))
}

fact{
	all t:TaxiDriver | t in Queue.contains implies t.available = True else t.available = False
}

fact{
	all q,p:Queue | q!=p implies (all t:q.contains | !t in p.contains)
}

fact exacltyOneManager{
	all q:Queue | (one m:QueueManager | q in m.manage)
}

fact {
	all m:QueueManager | #m.manage > 0
}

fact maxPassenger{
	all r:Ride  | #r.transport > 0 and #r.transport <= 4
}

fun different[p1,p2 : Position] : Boolean{
	(p1.x != p2.x or p1.y != p2.y) implies True else False
}

pred numPassenger{
	#Passenger > 3
	#Queue < 5
}

pred show{}

run numPassenger for 10

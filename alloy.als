abstract sig User{}
abstract sig Customer extends User{}
abstract sig Boolean{}
one sig True extends Boolean {}
one sig False extends Boolean {}

sig Passenger extends Customer{}

sig TaxiDriver extends User{
	available : Boolean
}

sig Ride{
	transport : set Passenger,
	hasDriver : one TaxiDriver
}

sig Queue{
	contains : set TaxiDriver
}

sig QueueManager{
	manage : set Queue
}

fact {
	Customer = Passenger
}

fact {
	User = TaxiDriver + Customer
}

fact{
	all t:Queue.contains | t.available = True
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

fact {
	all r:Ride | #r.transport > 0
}

fact maxPassenger{
	all r:Ride  | #r.transport <= 4
}

pred show{}

run show for 3

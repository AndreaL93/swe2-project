/**Signatures**/

//Sig for Users, having username and mail
abstract sig User{
	username : MString,
	mail : MString
}{
	username != mail
}

//Sig to identify Customers
abstract sig Customer extends User{}

//Passenger is a Customer how request a taxi
sig Passenger extends Customer{}

//Taxi Driver can be Available
sig TaxiDriver extends User{
	license : MString,
	available : Boolean
}

//Ride has: one TaxiDriver, one Starting position, a set of Passenger and some destination positions
sig Ride{
	start : one Position,
	destinations : some Position,
	transport : set Passenger,
	hasDriver : lone TaxiDriver,
	pending : Boolean
}{
	#transport >= 1 and #transport <= 4 and
	all d:destinations | different[d, start] = True and
	#hasDriver = 1 iff pending = True 
}

//Queue for each city Zone
sig Queue{
	contains : set TaxiDriver
}

//Manager of Queues
one sig QueueManager{
	manage : some Queue
}

/**Support Signatures**/
sig MString{}
sig Float{}

sig Position{
	x : Float,
	y : Float
}

abstract sig Boolean{}
one sig True extends Boolean {}
one sig False extends Boolean {}

/**Facts**/

//All the Passengers are Customers (and also Users)
fact {
	Passenger in Customer
}

//Users are composed by all the TaxiDrivers and Customers
fact {
	User = TaxiDriver + Customer
}

//No repeteaded Positions
fact uniquePositions{
	all p,q:Position | p!=q implies different[p,q] = True 
}

//All the Positions are used in the Ride sig
fact noUselessPositions{
	Ride.start + Ride.destinations = Position
}

//No useless Float sig
fact onlyUsedFloat{
	Position.x + Position.y = Float
}

//A User has unique username and mail
fact uniqueUsers{
	all u,w : User | (u.username = w.username or u.mail = w.mail) iff u=w
}

//A TaxiDriver is identified by his own license
fact uniqueLicense{
	all t1,t2 : TaxiDriver | t1.license = t2.license iff t1 = t2
}

//There are no username equals to mail
fact{
	User.username & User.mail = none
}

//Not exists license equals to username and mail
fact{
	(User.username + User.mail) & TaxiDriver.license = none
 }

//The String used are used only for username, mail and license
fact{
	User.username + User.mail + TaxiDriver.license = MString
}

//a User can be transported at most by one pending Ride
fact{
	all u:Ride.transport | (lone r:Ride | r.pending = True and u in r.transport)
}

//If a Taxi Driver is in a Queue implies his availability
fact taxiInQueueIsAvailable{
	all t:TaxiDriver | t in Queue.contains implies t.available = True else t.available = False
}

//Every Taxi Driver belogns at most to one Queue
fact taxiContainedInOneQueue{
	all q,p:Queue | q!=p implies (all t:q.contains | !t in p.contains)
}

//Every Queue belongs to the QueueManager
fact exacltyOneManager{
	all q:Queue | (one m:QueueManager | q in m.manage)
}

//For each Ride the number of destinations belongs to the # of Passenger
fact maxDestinations{
	all r:Ride | #r.destinations <= #r.transport
}

/**Functions **/

//True if the Positions are different, False otherwise
fun different[p1,p2 : Position] : Boolean{
	(p1.x != p2.x or p1.y != p2.y) implies True else False
}

/**Assertions**/

assert differentsUsernames{
	no u1,u2:User | u1.username = u2.username and u1 != u2
}

assert differentsMail{
	no u1,u2:User | u1.mail = u2.mail and u1 != u2
}

/**Predicates**/

pred taxiDriverAvailable{
	all t:TaxiDriver | t.available = True implies (one q:Queue | t in q.contains)
}

pred intrestingPred{
	#Passenger > 1
	#Position < 3
	#Queue = 2
	#Ride > 0 and #Ride < 3
	#TaxiDriver > 1
	one t:TaxiDriver | t.available = True
	one r:Ride | r.pending = True
}

pred show{}

/**Executions**/

run taxiDriverAvailable for 5

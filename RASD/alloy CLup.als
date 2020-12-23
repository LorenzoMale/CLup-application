open util/Time

sig Customer{
	physBook: set PhysicalBooking
}

sig QRcode{}

sig User extends Customer{ 
	userQRcode: one QRcode,	
	take: set Ticket,
	book: set Booking
}

abstract sig VisitMethod{
	vmState: State lone -> Time,
	haveVisit: lone Visit
}

abstract sig State{}
one sig VALID 	extends State{}
one sig INUSE 	extends State{}
one sig EXPIRED 	extends State{}

sig Ticket extends VisitMethod{
	queue: Queue one -> one Store
}{#queue<=1}


sig Booking extends VisitMethod{ 
	indicateBook: set CategoryOfItems,
	scheduleBook:  TimeSlot one -> lone Calendar 
}

sig PhysicalBooking extends VisitMethod{
	randomQRcode: one QRcode,
	indicatePBook: set CategoryOfItems,
	schedulePBook: TimeSlot one -> lone Calendar
}

sig Queue {
	belongQ: one Store
}

sig Calendar { 
	timeSlots: some TimeSlot,
	belongC: one Store,
}

abstract sig TimeSlotState{}
one sig AVAILABLE        extends TimeSlotState{}
one sig BUSY         extends TimeSlotState{}


 sig TimeSlot{
	TSstate: TimeSlotState lone -> Time,
}

sig Store { 
	sell: set CategoryOfItems, 
	haveC: one Calendar,
	haveQ: one Queue,
	works : some Employee,
	monitors : one StoreManager,
	maxCapacity:Int,
	haveV:some Visit
}{maxCapacity>0
#haveV<=maxCapacity}

sig Visit {
	entranceTime: one Time,  
	exitTime: lone Time,
	storeVisit: one Store
}

sig CategoryOfItems {}

sig Employee {}

sig StoreManager{}





///////////////////////////////////////////////////////////////// FACTS\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\



////////////////TIMESLOTS\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\
//Each time slot is related to only one calendar 
fact everyTimeSlotToOnecalendar{  
	all ts:TimeSlot | one c:Calendar | ts in c.timeSlots
}

fact timeSlotStateChart{
//ogni ticket creato come valid
all ts:TimeSlot | one t0:Time | ts.TSstate.t0=AVAILABLE
all ts:TimeSlot, t1:Time | 
	(ts.TSstate.t1=BUSY implies 
		all t2:Time | gte[t2,t1] implies ts.TSstate.t2=BUSY)
}






/////////////////////////QRCODES\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\

//every User’s QR code is unique and belongs to only one user
fact noEqualUserQRcode{
	all disj u, u' : User |  u.userQRcode != u'.userQRcode
}

//every Physical booking’s QR code is unique and belongs to only one Physical booking
fact noEqualPBookingQRcode{
	all disj pb, pb' : PhysicalBooking | pb.randomQRcode != pb'.randomQRcode
}

//User’s QR codes and Physical bookings QR codes are different
fact noUserQRforPhysicalBook{
	all u: User | all pb: PhysicalBooking |	 no (u.userQRcode & pb.randomQRcode)
}


// every QR code must be related to an User or a Physical Booking
fact noQRcodeWOUserOrPB{
all qr:QRcode | let u=User, pb=PhysicalBooking | ((qr in u.userQRcode) or (qr in pb.randomQRcode))
}


/////////////////////////////////STORE\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\

fact {
haveC=~belongC and haveQ=~belongQ
and 
	all v:Visit | one s:Store | s in v.storeVisit implies v in s.haveV
and
	all s:Store | all v:Visit | v in s.haveV implies s in v.storeVisit
}


//every Category is sold at least by one store
fact noCategoryWOStore{
	all coi:CategoryOfItems | some s:Store | coi in s.sell
}

fact storeManagerStore{
	// no Store Manager that works for different stores
	all sm : StoreManager | (no disj s1,s2: Store | sm in s1.monitors and sm in s2.monitors) 
and //no store without a StoreManager
	all s : Store | one sm: StoreManager | sm in s.monitors
and //no StoreManager without a store
	all sm: StoreManager | one s:Store | sm in s.monitors
}

fact employeeStore{
	// no Employee that works for different stores
	all e : Employee | (no disj s1,s2: Store | e in s1.works and e in s2.works) 
and //no store without an employee
	all s : Store | some e:  Employee | e in s.works
and //no Employee without a store
	all e: Employee | one s:Store | e in s.works
}




///////////////////////////VISIT METHOD\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\


//If a Visit Method has as state; “INUSE”, then it is linked to one and only one Visit
fact allINUSEVMhasVisit{

	all v:Visit| one vm:VisitMethod | v in vm.haveVisit

}


fact visitMethodStateChart{
//ogni visitMethod creato come valid
all vm:VisitMethod | one t0:Time | vm.vmState.t0=VALID
and
all vm:VisitMethod, t1:Time | 
	(vm.vmState.t1=EXPIRED implies 
		all t2:Time | gte[t2,t1] implies vm.vmState.t2=EXPIRED)
and
	(vm.vmState.t1=INUSE implies
		 all t2:Time | gte[t2,t1] implies vm.vmState.t2!=VALID) 

}



/////////TICKETS\\\\\\\\\\\\\


//each Ticket is taken by only one User
fact ticketUser{
		(all t:Ticket | no disj u1, u2:User | t in u1.take and t in u2.take)
and //No ticket without an User
		(all t: Ticket | one u: User | t in u.take)
}



///////BOOKINGS\\\\\\\\\\\


//every Category of Items that is indicated in a booking, is sold by the store related to that booking
fact indicateOnlyStoreCategories{
	all b:Booking, ts:TimeSlot  | all coi:CategoryOfItems | (coi in b.indicateBook) implies (coi in sell[belongC[ts.(b.scheduleBook)]])
}


//each Booking is booked by only one User
fact bookingUser{
	(all b: Booking | no disj u1,u2: User | b in u1.book and b in u2.book)
and //No booking without an User
	(all b: Booking | one u: User | b in u.book)
}

// if  Booking has a relation that maps Timeslot to calendar, that timeslot has to be in that calendar
fact allBookingsSlotRelatedCalendar{
all b:Booking, c:Calendar | all ts:TimeSlot | (ts in (b.scheduleBook).c) implies (ts in c.timeSlots)
}


///////PHYSBOOKING\\\\\\\\\



//every Category of Items that is indicated in a physical booking is sold by the store related to that physical booking
fact indicateOnlyStoreCategoriesPB{
	all pb:PhysicalBooking, ts:TimeSlot  | all coi:CategoryOfItems | (coi in pb.indicatePBook) implies (coi in sell[belongC[ts.(pb.schedulePBook)]])
}


//each physical Booking is booked by only one customer
fact physicalBookingCustomer{
	(all pb: PhysicalBooking | no disj cu1, cu2: Customer | pb in cu1.physBook and pb in cu2.physBook)
and //no physical booking without customer
	(all pb: PhysicalBooking | one cu: Customer | pb in cu.physBook)
}

//user can't take a physical booking
fact userNoPhysicalBooking{
all u:User | #u.physBook=0
}

// if  PhysicalBooking has a relation that maps Timeslot to calendar, that timeslot has to be in that calendar
fact allPBookingsSlotRelatedCalendar{
all pb:PhysicalBooking, c:Calendar | all ts:TimeSlot | (ts in (pb.schedulePBook).c) implies (ts in c.timeSlots)
}



//////////////////predicates\\\\\\\\\\\\\\\\\\





///////////////////booking of a slot
pred isTimeSlotAvailable[ts:TimeSlot, t:Time]{

ts.TSstate.t=AVAILABLE

}


pred makeABooking[u:User, b:Booking, ts:TimeSlot, c:Calendar, t:Time]{
//preconditions
isTimeSlotAvailable[ts, t]
//postconditions
u.book=b
b.scheduleBook.c = ts
not isTimeSlotAvailable[ts,t.next]
ts.TSstate.(t.next)=BUSY
}


/////////////////////////taking a ticket

pred userTakesATicket[u:User, tick:Ticket, q:Queue, s:Store]{
//preconditions

//postconditions
u.take=tick
tick.queue.s= q
#Booking=0
#PhysicalBooking=0
}


/////////////////////////////////////////////user  enters a store

pred userReadyToEnter[u:User, tick:Ticket, q:Queue, s:Store, t:Time]{

u.take=tick
tick.queue.s=q
tick.vmState.t=VALID

}

pred userEntersAStoreWATicket[u:User, tick:Ticket, q:Queue, s:Store, v:Visit, t:Time]{
//preconditions
userReadyToEnter[u, tick, q, s, t]
//postconditions
v.entranceTime=t
#v.exitTime=0
not userReadyToEnter[u, tick, q, s, t.next]
tick.vmState.(t.next)=INUSE
tick.haveVisit=v

}

///////////////////////////// user exits from a store

pred userReadyToExit[u:User, tick:Ticket, v:Visit, t1:Time, t:Time]{

u.take=tick
tick.vmState.t=INUSE
tick.haveVisit=v

gte[t, t1]
v.entranceTime=t1
}



pred userExitsAStore[u:User, tick:Ticket, v:Visit, t1:Time, t:Time]{
//
userReadyToExit[u, tick, v, t1, t]
//

v.exitTime=t.next
not userReadyToExit[u, tick, v, t1, t.next]
tick.vmState.(t.next)=EXPIRED

}


////////no entrances allowed

pred storeIsFull [s:Store, disj v1, v2:Visit]{
	s.maxCapacity=2 // to change to "3" to prove the visit is allowed in that case
	v1.storeVisit=s
	v2.storeVisit=s	
}


pred tryToEnterFullStore[ s:Store, disj v1,v2, v3:Visit]{

//precondition
storeIsFull[s, v1, v2]

//postcondition
v3.storeVisit=s
}

pred show{
}




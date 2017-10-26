//Alloy Model fo Travlendar+

//_____________________________________________________________
//__________________________DATATYPE___________________________
//_____________________________________________________________


//Importing Time-realated DataTypes
open util/time

//Datatype representing alphanumeric strings 
sig Strings{}

//Datatype representing integer numbers
sig Integer {}

//Datatype representing boolean numbers
sig Bool {}


//Datatype representing floats
sig Floats{}


//___________________________________________________________
//____________________SIGNATURE______________________________
//___________________________________________________________


//Calendar

 sig Calendar {
	appointments : seq Appointment,
	breaks : seq Break,
	trips : seq Trip
} {
	not appointments.hasDups
	not breaks.hasDups
	not trips.hasDups
}

//Break

sig Break {
	frameStart : one Time,
	frameEnd : one Time,
	minimumDuration : one Time,
	breakStart : one Time,
	breakEnd : one Time
}

//Appointment

sig Appointment {
	name : one Strings,
	date : one Time,
	time : one Time,
	address : one Strings,
	favouredVehicle : one Strings,
	type : one Strings
}


//Trip

sig Trip {
	departureAddress : one Strings,
	destinationAddress : one Strings,
	transportationMean : some TransportationMean,
	startTime : one Time,
	arrivalTime : one Time,
	calendar : one Calendar,
	carbonFootprints : lone Integer,
	eventId : one Strings
}


//Transportation Means and its related subclasses

abstract sig TransportationMean {}

sig SharedVehicle extends TransportationMean {
	type : one Strings,
	company : one Strings,
	sharing : one SharingManager,
}

sig Train extends TransportationMean {
	public : one PublicServiceManager
}
sig Tram extends TransportationMean {
	public : one PublicServiceManager
}
sig Bus extends TransportationMean {
	public : one PublicServiceManager
}
sig Car extends TransportationMean {
	distance : one DistanceManager	
}
sig Bike extends TransportationMean {
	distance : one DistanceManager
}
sig Walking extends TransportationMean {
	distance : one DistanceManager
}

//User Management

abstract sig GeneralUser {}
sig Guest extends GeneralUser {}

sig User extends GeneralUser {
	name : one Strings,
	surname : one Strings,
	username : one Strings,
	password : one Strings,
	calendar : one Calendar,
	creditCard : set CreditCard,
	seasonPass : set SeasonPass,
	preference : set Preference,
	tickets : set Ticket
} 

//User settings

sig CreditCard {
	cardNumber : one Integer,
	expirationDate : one Time,
	cvv : one Integer
}

sig SeasonPass {
	companyName : one Strings,
	validityTime : one Integer,
}

sig Ticket {
	companyName : one Strings,
	type : one Strings,
	date : one Time,
	name : lone Strings,
	reservedSeat : lone Strings
}

//Preference Management

sig Preference {
	type : one Strings,
	description : one Strings,
	selected : one Bool,
	scheduler : one Scheduler
}

lone sig CarbonPreference extends Preference {
	quantity : one Integer
}


//Travel Scheduling and Warning notifications

sig Scheduler {
	notify : some Notification,
	trips : set Trip,
	weatherForecaster : one WeatherForecaster,
	sharingManager : one SharingManager,
	publicServiceManager : one PublicServiceManager,
	distanceManager: one DistanceManager,
	excludedVehicles : set TransportationMean
}



sig Notification {
	id : one Strings,
	message : one Strings,
	journey : one Trip
}
	


//External Modules 

sig WeatherForecaster {	scheduler : one Scheduler}
sig SharingManager {scheduler : one Scheduler}
sig PublicServiceManager {scheduler : one Scheduler}
sig DistanceManager {scheduler : one Scheduler}	

//Reservation of Shared Vehicles

sig Reservation {
	date : one Time,
	cCard : one CreditCard,
	sharedVehicle : lone SharedVehicle
}

//Purchase of public transportation tickets

sig TicketPurchase {
	ticketCode : one Strings,
	company : one Strings,
	price : one Floats,
	start : one Strings,
	destination : one Strings,
	cCard : one CreditCard
}




//______________________________________________________________
//__________________________FACTS_______________________________
//______________________________________________________________


//All user's preferences can't exist without the corresponding user

fact creditCardsDependency {
	all c : CreditCard | some u : User | c in u.creditCard
}

fact seasonPassDependency {
	all s : SeasonPass | some u: User | s in u.seasonPass 
}

fact preferenceDependences {
	all p : Preference | some u : User | p in u.preference 
}

fact ticketDependency {
	all t : Ticket | some u: User | t in u.tickets
}


//All the breaks and the appointments can't exist without a Calendar to refer to

fact appointmentsDependency {
	all a : Appointment | some c : Calendar | a in univ.(c.appointments)
} 

fact breaksDependency {
	all b : Break | some c : Calendar | b in univ.(c.breaks)
}

//All notifications must refer to a Scheduler

fact notificationDependency {
	all n : Notification | some s : Scheduler |
		n in s.notify
}


//All transportation means must refer to a trip

fact tripRequired {
	all t : TransportationMean | some tr : Trip | t in tr.transportationMean
}


//User must allow at least a transportation mean when looking for travel solutions

fact oneTravelMean {
	all s : Scheduler | some t : TransportationMean | t not in s.excludedVehicles
}

//Two notifications with the same id can't possibily cohexist

fact noIdenticalNotify {
	no disjoint n1,n2 : Notification | n1.id = n2.id
}

// Trip's got to be directly related to the Scheduler

fact allTripsAreLinked {
	all t : Trip | some s : Scheduler | t in s.trips
}

//Non posso avere due veicoli esclusi uguali nello stesso scheduler

fact noTwoIdenticalTransportationMeans {
	all s : Scheduler | all disjoint t1,t2 : s.excludedVehicles |
	 t1 != t2
}

//User must have always "walking" active in his travel mean preferences

fact walkingActive{
		all t : Trip | all id :  Trip.eventId | some w : Walking | w in t.transportationMean and t.eventId = id
}



//Trips are not allowed during break time

fact noTripDuringBreak {
	no t : Trip | some b : Break | (gte[t.arrivalTime, b.breakStart] and lte[t.arrivalTime, b.breakStart + b.minimumDuration]) or
																 (gte[t.startTime, b.breakStart] and lte[t.startTime, b.breakStart + b.minimumDuration])
}

//I trips devono essere inclusi nel frame time

fact withinFrame {
	no b : Break | lt [b.breakStart, b.frameStart] or gt[b.breakEnd, b.frameEnd]
}


//Every trip has to show carbon footprints if I expressed a preference regarding carbon footprints

fact showCarbonFootprints  {
	all t: Trip | some CarbonPreference implies #t.carbonFootprints > 0 else #t.carbonFootprints = 0
}


//____________________________________________________
//____________________Predicates______________________
//____________________________________________________


// The predicate shows whether an appointment overlaps with the ones already registered in the calendar, i.e is a duplicate

pred overlaps [ a : Appointment, c : Calendar] {
	no ac : univ.(c.appointments) | ac.time = a.time and ac.date = a.date
}


// Inserting a new appointment into the calendar 

pred insertAppointment [a : Appointment, c : Calendar , c' : Calendar] {
	//preconditions
	not overlaps[a,c]
	//postconditions
	univ.(c'.appointments) = univ.(c.appointments) +  a
	c'.breaks = c.breaks
	c'.trips = c.trips
}




// Excluding a transportation mean 

pred excludeTransportationMean [ t : TransportationMean, s,s' : Scheduler] {
	//preconditions	
	#s.excludedVehicles = 0
	//postconditions
	s'.excludedVehicles = s.excludedVehicles + t
	s'.notify = s.notify
	s'.trips = s.trips
	s'.weatherForecaster = s.weatherForecaster
	s'.sharingManager = s.sharingManager
	s'.publicServiceManager = s.publicServiceManager
	s'.distanceManager = s.distanceManager

}



// Reserving a Car

pred reserving [ s : SharedVehicle, r' : Reservation, r : Reservation] {
	//no preconditions
	#r.sharedVehicle = 0
	//postconditions
	r'.date = r.date 
	r'.cCard = r.cCard 
	r'.sharedVehicle = r.sharedVehicle + s

}





// Ticket purchasing

pred	ticketPurchase [ t : Ticket, u1 : User, u2 : User ] {
	//preconditions
	not t in u1.tickets
	//postconditions
	u2.name = u1.name
	u2.surname = u1.surname
	u2.username = u1.username
	u2.password = u1.password
	u2.calendar = u1.calendar
	u2.creditCard = u1.creditCard
	u2.seasonPass = u1.seasonPass
	u2.preference = u1.preference
	u2.tickets = u1.tickets + t
}

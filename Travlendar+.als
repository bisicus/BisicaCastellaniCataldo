//Alloy Model fo Travlendar+

//Importing DataTypes with Time 
open util/time
//Datatype representing alphanumeric strings 
sig Strings{}

//Datatype representing integer numbers
sig Integer {}

//Datatype representing boolean numbers
sig Bool {}


//Datatype representing floats
sig Floats{}


//The Calendar
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
	carbonFootprints : lone Integer
}


//Mezzi di trasporto

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
}
sig Bike extends TransportationMean {
}

//Gestione Utente

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
	preference : set Preference
} 

// Gestione "Possessi dell'utente"

sig CreditCard {
	cardNumber : one Integer,
	expirationDate : one Time,
	cvv : one Integer
}

sig SeasonPass {
	companyName : one Strings,
	validityTime : one Integer,
}

//Gestione Preferenze

sig Preference {
	type : one Strings,
	description : one Strings,
	selected : one Bool,
	scheduler : one Scheduler
}

lone sig CarbonPreference extends Preference {
	quantity : one Integer
}


//Gestione Scheduling dei viaggi

sig Scheduler {
	notify : one Notification,
	trips : some Trip,
	weatherForecaster : one WeatherForecaster,
	sharingManager : one SharingManager,
	publicServiceManager : one PublicServiceManager,
	distanceManager: one DistanceManager,
	excludedVehicles : seq TransportationMean
}
	{ not excludedVehicles.hasDups }

sig WeatherForecaster {}
sig SharingManager {}
sig PublicServiceManager {}
sig DistanceManager {}	

sig Notification {
	id : one Strings,
	message : one Strings,
	journey : one Trip
}
	

//Da collegare a credit card?
sig Reservation {
	date : one Time,
	cCard : one CreditCard,
	sharedVehicle : lone SharedVehicle
}

sig TicketPurchase {
	ticketCode : one Strings,
	company : one Strings,
	price : one Floats,
	start : one Strings,
	destination : one Strings,
	cCard : one CreditCard
}



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


//All the breaks and the appointments can't exist without a Calendar to refer to

fact appointmentsDependency {
	all a : Appointment | some c : Calendar | a in univ.(c.appointments)
} 

fact breaksDependency {
	all b : Break | some c : Calendar | b in univ.(c.breaks)
}


//All transportation means must refer to a trip

fact tripRequired {
	all t : TransportationMean | some tr : Trip | t in tr.transportationMean
}


//User must always allow at least a transportation mean when looking for travel solutions
fact oneTravelMean {
	all s : Scheduler | some t : TransportationMean | t not in univ.(s.excludedVehicles)
}

//Two notifications with the same id can't possibily cohexist
fact noIdenticalNotify {
	no disjoint n1,n2 : Notification | n1.id = n2.id
}

//Trip non può essere collegato a Scheduler tramite Notify
fact allTripsAreLinked {
	all t : Trip, s: Scheduler | t in s.trips
}


//Non possono esserci più reservations con la stessa data

fact noReservationsOverlapping {
	all disjoint r1,r2 : Reservation | r1.date != r2.date
}

//Vorrei fare dei fact sui break ma è praticamente impossibile

fact noTripDuringBreak {
	no t : Trip | some b : Break | (gte[t.arrivalTime, b.breakStart] and lte[t.arrivalTime, b.breakStart + b.minimumDuration]) and
																 (gte[t.startTime, b.breakStart] and lte[t.startTime, b.breakStart + b.minimumDuration])
}

//I trips devono essere inclusi nel frame time

fact withinFrame {
	no b : Break | lt [b.breakStart, b.frameStart] or gt[b.breakEnd, b.frameEnd]
}

//Non può esserci un trip con veicoli bloccati (il nome va cambiato)

fact noTripForTravel {
	all s : Scheduler, tmeans : univ.(s.excludedVehicles) | no tr : Trip |
	tmeans in tr.transportationMean
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

//run insertAppointment for 2



// Excluding a transportation mean 

pred excludeTransportationMean [ t : TransportationMean, s,s' : Scheduler] {
	//preconditions	
	t not in univ.(s.excludedVehicles)
	//postconditions
	univ.(s'.excludedVehicles) = univ.(s.excludedVehicles) + t
	s'.notify = s.notify
	s'.trips = s.trips
	s'.weatherForecaster = s.weatherForecaster
	s'.sharingManager = s.sharingManager
	s'.publicServiceManager = s.publicServiceManager
	s'.distanceManager = s.distanceManager

}

run excludeTransportationMean for 3

// Reserving a Car

pred reserving [ s : SharedVehicle, r' : Reservation, r : Reservation] {
	//no preconditions
	#r.sharedVehicle = 1
	//postconditions
	r'.date = r.date 
	r'.cCard = r.cCard 
	r'.sharedVehicle = r.sharedVehicle + s

}

run reserving for 3

pred show{}
run show for 3 but exactly 2 Reservation, 2 SharedVehicle

// Travel Logic 







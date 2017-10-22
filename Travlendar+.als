//Alloy Model fo Travlendar+

//Datatype representing alphanumeric strings 
sig Strings{}

//Datatype representing integer numbers
sig Integer {}

//Datatype representing boolean numbers
sig Bool {}

//Datatype representing dates
sig DateTime{}

//Datatype representing floats
sig Floats{}


//The Calendar
one sig Calendar {
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
	frameStart : one DateTime,
	frameEnd : one DateTime,
	minimumDuration : one Integer,
	startTime : one DateTime
}

//Appointment

sig Appointment {
	name : one Strings,
	date : one DateTime,
	time : one Integer,
	address : one Strings,
	favouredVehicle : one Strings,
	type : one Strings
}

//Trip

sig Trip {
	departureAddress : one Strings,
	destinationAddress : one Strings,
	transportationMean : some TransportationMean,
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

one sig User extends GeneralUser {
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
	expirationDate : one DateTime,
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

one sig Scheduler {
	notify : one Notification,
	trips : some Trip,
	weatherForecaster : one WeatherForecaster,
	sharingManager : one SharingManager,
	publicServiceManager : one PublicServiceManager,
	distanceManager: one DistanceManager,
	excludedVehicles : seq TransportationMean
}
	{ not excludedVehicles.hasDups }

one sig WeatherForecaster {}
one sig SharingManager {}
one sig PublicServiceManager {}
one sig DistanceManager {}	

sig Notification {
	id : one Strings,
	message : one Strings,
	journey : one Trip
}
	

//Da collegare a credit card?
sig Reservation {
	date : one DateTime,
	cCard : one CreditCard,
	sharedVehicle : one SharedVehicle
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


//Non può esserci un trip con veicoli bloccati (il nome va cambiato)

fact noTripForTravel {
	all s : Scheduler, tmeans : univ.(s.excludedVehicles) | no tr : Trip |
	tmeans in tr.transportationMean
}

//Every trip has to show carbon footprints if I expressed a preference regarding carbon footprints

fact asdasd  {
	all t: Trip | some CarbonPreference implies #t.carbonFootprints > 0 else #t.carbonFootprints = 0
}


//____________________Predicates______________________

//Insert an appointment into the Calendar

pred insertAppointment [a : Appointment, c : Calendar, c': Calendar] {
	//preconditions
	c != c' and
	a not in univ.(c.appointments)
	//postconditions
	c'.breaks = c.breaks and
	c'.trips = c.trips and
	univ.(c.appointments) in univ.(c'.appointments) and
 	a in univ.(c'.appointments)
}

//Exclude a Transportation Mean from the Scheduler 

pred excludeTransportationMean [ t : TransportationMean, s : Scheduler] {
	//preconditions
	t not in univ.(s.excludedVehicles)
	//postconditions
	t in univ.(s.excludedVehicles)
}


//Making a reservation on a shared vehicle that's already been rented by the user?? Nope
/*
pred reserving [ s : SharedVehicle, r : Reservation] {
	//no preconditions
	//postconditions
	r.sharedVehicle = s	
}
*/

//run excludeTransportationMean {} for 3
/*
fact carbon {
	all c : CarbonPreference, s : Scheduler, t : s.trips | c.quantity >= t.carbonFootprints
}
*/


// Procedura inserimento evento





/*
pred isTimeEnough [a1 : Appointment, a2 : Appointment]	{


pred startWarning { }
	//precondition
	
*/


run reserving for 2


//pred show{}
//run show for 2 but exactly 2 Reservation, 2 SharedVehicle


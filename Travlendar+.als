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
	carbonFootprint : one Integer
}


//Mezzi di trasporto

abstract sig TransportationMean {}
sig SharedVechicle extends TransportationMean {
	type : one Strings,
	company : one Strings
}



sig SharedVehicle extends TransportationMean {
	sharing : one SharingManager,
	reservation : set Reservation,
	traffic : one TrafficManager	
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
	traffic : one TrafficManager	
}
sig Bike extends TransportationMean {
traffic : one TrafficManager	
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

sig CarbonPreference extends Preference {
	quantity : one Integer
}


//Gestione Scheduling dei viaggi

one sig Scheduler {
	notify : one Notify,
	trips : set Trip,
	weatherForecaster : one WeatherForecaster,
	sharingManager : one SharingManager,
	publicServiceManager : one PublicServiceManager,
	trafficManager : one TrafficManager,
	excludedVehicles : seq TransportationMean
}
	{ not excludedVehicles.hasDups }

sig WeatherForecaster {
	scheduler : one Scheduler
}
sig SharingManager {
	scheduler : one Scheduler
}
sig PublicServiceManager {
		scheduler : one Scheduler
}
sig TrafficManager {
		scheduler : one Scheduler
}
	
sig Notify {
	id : one Strings,
	message : one Strings,
	journey : one Trip
}
	

//Da collegare a credit card?
sig Reservation {
	date : one DateTime,
	cCard : one CreditCard
}

sig TicketPurchase {
	ticketCode : one Strings,
	company : one Strings,
	price : one Floats,
	start : one Strings,
	destination : one Strings,
	cCard : one CreditCard
}



//Tutte le preferenze utente devono dipendere da un utente

fact creditCardsDependency {
	all c : CreditCard | some u : User | c in u.creditCard
}

fact seasonPassDependency {
	all s : SeasonPass | some u: User | s in u.seasonPass 
}

fact preferenceDependences {
	all p : Preference | some u : User | p in u.preference 
}


//Tutti gli appuntamenti e i breaks devono dipendere da un Calendar

fact appointmentsDependency {
	all a : Appointment | some c : Calendar | a in univ.(c.appointments)
} 

fact breaksDependency {
	all b : Break | some c : Calendar | b in univ.(c.breaks)
}



//L'utente deve almeno lasciare un mezzo sempre disponibile nelle scelte
fact oneTravelMean {
	all s : Scheduler | some t : TransportationMean | t not in univ.(s.excludedVehicles)
}

fact noIdenticalNotify {
	no disjoint n1,n2 : Notify | n1.id = n2.id
}

//Insert an appointment into the Calendar

pred insertAppointment [a : Appointment, c : Calendar, c': Calendar] {
	//preconditions
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
pred show {}
run show for 2 but exactly 1 SeasonPass, 1 CreditCard, 1 Reservation, 1 Trip
	

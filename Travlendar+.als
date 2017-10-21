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
	startTime : one DateTime,
	endTime : one DateTime,
	minimumDuration : one Integer
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
	transportationMean : seq TransportationMean,
	calendar : one Calendar,
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


//Gestione Scheduling dei viaggi

one sig Scheduler {
	notify : one Notify,
	trips : set Trip,
	weatherForecaster : one WeatherForecaster,
	sharingManager : one SharingManager,
	publicServiceManager : one PublicServiceManager,
	trafficManager : one TrafficManager	
}

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
	
sig Notify {}
	

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


//Tutti gli appuntamenti 



//Requirements rubati dal nostro RASD 

	




// procedura cambio utente?



run showWorld {}

	

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
sig Calendar {
	appointments : seq Appointment,
	breaks : seq Break,
	trips : seq Trip
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
	transportationMean : seq TransportationMean
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

sig User extends GeneralUser {
	calendar : one Calendar,
	name : one Strings,
	surname : one Strings,
	username : one Strings,
	password : one Strings,
	creditcards : seq CreditCard, 
	seasonPass : set SeasonPass,
	preferences : set Preference
}

// Gestione "Possessi dell'utente"

sig CreditCard {
	cardNumber : one Integer,
	expirationDate : one DateTime,
	cvv : one Integer
}

sig SeasonPass {
	companyName : one Strings,
	validityTime : one Integer
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
	weather : one WeatherForecaster,
	sharing : one SharingManager,
	public : one PublicServiceManager,
	traffic : one TrafficManager,
	notify : one Notify,
	trips : set Trip
}

sig WeatherForecaster {}
sig SharingManager {}
sig PublicServiceManager {}
sig TrafficManager {}
	

//Sistema di notifica, rivedere
sig Notify {
	id : one String,
	message : one String,
//	trip : //da fare,
	user : one User 
}
	

//Da collegare a credit card?
sig Reservation {
	date : one DateTime,
	cCard : one CreditCard
}

sig TicketPurchase {
	ticketCode : one Strings,
	company : one String,
	price : one Floats,
	start : one Strings,
	destination : one Strings,
	cCard : one CreditCard
}


	


// procedura cambio utente?



run showWorld {}

	

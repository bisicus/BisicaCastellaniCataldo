//Alloy Model fo Travlendar+

//Datatype representing alphanumeric strings 
sig Strings{}

//Datatype representing integer numbers
sig Integer {}

//Datatype representing boolean numbers
sig bool {}

//Datatype representing dates
sig DateTime{}

//Datatype representing travels
sig Travel {
	location : one Strings,
	destination : one Strings,
	startTime : one DateTime,
	expectedDuration : one Integer
}


//We implement both the guest and the registered user starting from an abstract sig
abstract sig GeneralUser {}

//The Guest user of Travlendar+
sig Guest extends GeneralUser{}

//The User of Travlendar+
sig User  extends  GeneralUser{
	name : one Strings,
	surname : one Strings,
	username : one Strings,
	password : one Strings,
	creditcard : lone CreditCard,
	seasonPass : lone SeasonPass,
	preference : one Preference
}

//Credit Card linked to a user
sig CreditCard {
	cardNumber : one Integer,
	expirationDate : one DateTime,
	cvv : one Integer
}

//Season Pass linked to a user
sig SeasonPass {
	companyName : one Strings,
	validityTime : one Integer
}


//Preference linked to a user
sig Preference {
	type : one Strings,
	description : one Strings,
	selected : one bool
}

//Transportation means signatures 
abstract sig TransportationMean {}

sig  sharedVehicle extends TransportationMean{
	type : one String,
	company : one String
}

sig Train extends TransportationMean{}
sig Tram extends TransportationMean{}
sig Bus extends TransportationMean{}
sig Car extends TransportationMean{}
sig Bike extends TransportationMean{}


//The trip made by a user
sig Trip {
	sourceAddress : one Strings,
	destinationAddress : one Strings,
	adoptedTravelMeans : TransportationMean
}


//The appointment, or event, that users can create
sig Appointment {
	name : one Strings,
	date : one DateTime,
	address : one Strings,
	favouredVehicle : one Strings,
	type :  one Strings
}
	
//Reserved time spans for the users
sig break {

	startTime : one DateTime,
	endTime : one DateTime,
	minimumDuration : one Strings
}


//The Scheduler
sig scheduler {
	weather : one WheatherForecaster,
	sharingManager : one SharingManager,
	publicServiceManager : one PublicServiceManager,
	trafficManager : one TrafficManager
}

//The components of the scheduler
sig WheatherForecaster {}
sig SharingManager {}
sig PublicServiceManager{}
sig TrafficManager{}


run showWorld{}


	

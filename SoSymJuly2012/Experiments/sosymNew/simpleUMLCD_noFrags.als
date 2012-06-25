
module tmp/simpleUMLCD
open util/boolean as Bool

sig ClassModel {
	classifier: set Classifier,
	association: set Association
}

abstract sig Classifier {
      name :  Int
	
	}

sig PrimitiveDataType extends Classifier {}

sig Class extends Classifier {
	is_persistent: one Bool,
	parent : lone Class,
	attrs : some Attribute //atleast one attribute, chnqge to set if not necessary
}

sig Association {
	name: Int,
	dest: one Class,
	src: one Class
}


sig Attribute {
	name: Int,
	is_primary : Bool,
	type: one Classifier
}


//Meta-model constraints//

//There must be no cyclic inheritance in the generated UML class diagram
fact noCyclicInheritance {
	no c: Class | c in c.^parent
}

//All the attributes in a Class must have unique attribute names
fact uniqueAttributeNames {
all c:Class |  all a1:  c.attrs , a2 : c.attrs |a1.name==a2.name => a1 = a2  
}

//An attribute object can be contained by only one class
fact attributeContainment {
all c1:Class, c2:Class | all a1:c1.attrs, a2:c2.attrs | a1==a2 => c1=c2
}

//There is exactly one ClassModel object
fact oneClassModel {
 one ClassModel
}

//All Classifier objects are contained in a ClassModel
fact classifierContainment {
all c:Classifier | c in ClassModel.classifier
}

//All Association objects are contained in a ClassModel
fact associationContainment {
all a:Association | a in ClassModel.association
}



//A Classifier must have a unique name in the class diagram
fact uniqueClassifierName {
all c1:Classifier, c2:Classifier | c1.name==c2.name => c1=c2
}



//An associations have the same name either they are the same association or they have different sources
fact uniqeNameAssocSrc {
all a1:Association, a2:Association | a1.name == a2.name => (a1 = a2 or a1.src != a2.src)
}


//Model Transformation UMLCD to RDBMS Pre-condition
fact atleastOnePrimaryAttribute {
    all c:Class| one a:c.attrs | a.is_primary==True
}


//Improved Model Transformation pre-conditions
fact no4CyclicClassAttribute{
	all a:Attribute | a.type in Class => all a1:a.type.attrs|a1.type in Class => all a2:a.type.attrs|a2.type in Class => all a3:a.type.attrs|a3.type in Class => all a4:a.type.attrs|a4.type in PrimitiveDataType
}

//A Class cannot have an association and an attribute of the same name 
fact noAttribAndAssocSameName{
	all c:Class, assoc:Association | all a : c.attrs | (assoc.src == c) => a.name != assoc.name
}


//No cycles between non-persistent classes



fact no1CycleNonPersistent
{
      all a: Association | (a.dest == a.src) => a.dest.is_persistent= True 
}



fact no2CycleNonPersistent
{
      all a1: Association, a2:Association | (a1.dest == a2.src and a2.dest==a1.src) => a1.src.is_persistent= True or a2.src.is_persistent=True  
}

/*
fact no3CycleNonPersistent
{
      all a1: Association, a2:Association, a3:Association | (a1.dest == a2.src and a2.dest==a3.src and a3.dest==a1.src) => a1.src.is_persistent= True or a2.src.is_persistent=True  or a3.src.is_persistent=True
}

fact no4CycleNonPersistent
{
      all a1: Association, a2:Association, a3:Association, a4:Association | (a1.dest == a2.src and a2.dest==a3.src and a3.dest == a4.src and a4.dest==a1.src ) => a1.src.is_persistent= True or a2.src.is_persistent=True  or a3.src.is_persistent=True or a4.src.is_persistent=True
}

*/

//New pre-conditions obtained by Jean-Marie Mottu


//	1. A persistent class can't have an association to one of its parent

fact assocPersistentClass
{
	all a:Association | a.src.is_persistent=True implies a.dest not in a.src.^parent
}

//2. in the classes of an inheritance tree, two associations with the same 
//name can't point to classes that have (or their parent) attributes with same names

/*
fact twoAssocSameNamePointToClassWithSameNames
{
	all c:Class |all a1:Association, a2:Association | (a1.src in c and a2.src in c.^parent and a1.name==a2.name) 
implies ((no att1:a1.dest.attrs, att2:a2.dest.attrs|att1.name=a1.name and att2.name = a2.name) and
  ( all p1: a1.dest.^parent, p2:a2.dest.^parent | (no att1:p1.attrs, att2:p2.attrs|att1.name=a1.name and att2.name = a2.name)))

}*/

/*
fact twoAssocSameNamePointToClassWithSameNames
{
    all c:Class |
    all a1:Association, a2:Association |
    (a1.src in c and a2.src in c.^parent and a1.name==a2.name) implies
    
		all p1: a1.dest+a1.dest.^parent, p2:a2.dest+a2.dest.^parent |
             (no att1:p1.attrs, att2:p2.attrs|att1.name=att2.name)
     
 }
*/
//Unique association names in a class hierarchy

fact uniqueAssocNamesInInHeritanceTree
{
     all c:Class |
    all a1:Association, a2:Association |
    (a1.src in c and a2.src in c.^parent and a1!=a2) implies (a1.name!=a2.name)
    
   
 }


//3."a class can't be the type of one of its attributes (amoung all its attributes)"


fact classCantTypeOfAllofItsAttribute
{
 all c:Class | all a: (c.attrs+c.^parent.attrs) | a.type !=c
} 
//4."a class A which inherits from a persistent class B can't have an outgoing association with the same name
// that one association of that persistent class B"

fact classInheritsOutgoingNotSameNameAssoc
{
	all A:Class | all B:A.^parent | B.is_persistent == True implies (no a1: Association, a2:Association | 
(a1.src = A and a2.src=B and a1.name=a2.name))
}

//5. "a class A which inherits from a persistent class B can't have an attribute with the same name 
//that one attribute of that persistent class B"


fact classInheritsOutgoingNotSameNameAttrib
{
	all A:Class | all B:A.^parent | B.is_persistent == True implies (no a1: A.attrs, a2:B.attrs | 
(a1.name=a2.name))
}

//6. No association between two classes of an inheritance tree

fact noAssocBetweenClassInHierarchy
{
	all a : Association | all c: Class | (a.src =c implies a.dest not in c.^parent) and (a.dest =c implies a.src not in c.^parent)
}

pred noFrags
{}

//Set 1 [5,5,25,4]


//All Partitions

run noFrags for 1 ClassModel,5 int,exactly 5 Class,exactly 25 Attribute,exactly 4 PrimitiveDataType,exactly 5 Association


// Set 2 [5,15,25,4]


run noFrags for 1 ClassModel,5 int,exactly 5 Class,exactly 25 Attribute,exactly 4 PrimitiveDataType,exactly 15 Association


//Set 3 [15,5,25,4]


run noFrags for 1 ClassModel,5 int,exactly 15 Class,exactly 25 Attribute,exactly 4 PrimitiveDataType,exactly 5 Association

//Set 4 [15,15,25,4]



run noFrags for 1 ClassModel,5 int,exactly 15 Class,exactly 25 Attribute,exactly 4 PrimitiveDataType,exactly 15 Association

//Set 5[5,5,30,4]



run noFrags for 1 ClassModel,5 int,exactly 5 Class,exactly 30 Attribute,exactly 4 PrimitiveDataType,exactly 5 Association


//Set 6 [15,5,30,4]



run noFrags for 1 ClassModel,5 int,exactly 15 Class,exactly 30 Attribute,exactly 4 PrimitiveDataType,exactly 5 Association


//Set  7 [5,15,30,4]



run noFrags for 1 ClassModel,5 int,exactly 5 Class,exactly 30 Attribute,exactly 4 PrimitiveDataType,exactly 15 Association

//Set 8 [15,15,30,4]



run noFrags for 1 ClassModel,5 int,exactly 15 Class,exactly 30 Attribute,exactly 4 PrimitiveDataType,exactly 15 Association


#include "Interpreter.h"
#include "Parameter.h"
using namespace std;

Interpreter::Interpreter(DatalogParser parser, string fileName) {
	Database database;
	output.open(fileName);
	schemesList = parser.getSchemesList();
	factsList = parser.getFactsList();
	rulesList = parser.getRulesList();
	queriesList = parser.getQueriesList();
}

void Interpreter::evaluateSchemes() {
	output << "Scheme Evaluation" << endl << endl;
    for (unsigned int i = 0; i < schemesList.size(); ++i) {
		Relation newRelation;
		string name = schemesList[i].getID();
		newRelation.setName(name);
        for (unsigned int j = 0; j < schemesList[i].getParams().size(); j++) {
			Parameter p = schemesList[i].getParams()[j];
			string value = p.getValue();
			newRelation.setScheme(value);
		}
        pair<string, Relation> p1 = {name, newRelation};
        database.initializeRelations(p1);
	}
}

void Interpreter::evaluateFacts() {
	output << "Fact Evaluation" << endl << endl;
	set<string> factNames;
    for (unsigned int i = 0; i < schemesList.size(); ++i) {
        string factName = schemesList[i].getID();
        factNames.insert(factName);
    }
    for (unsigned int i = 0; i < factsList.size(); ++i) {
		Tuple tuple;
		string factName = factsList[i].getID();
		factNames.insert(factName);
        for (unsigned int j = 0; j < factsList[i].getParams().size(); ++j) {
			Parameter p = factsList[i].getParams()[j];
			string value = p.getValue();
			tuple.push_back(value);
        }
		database.setTuple(factName, tuple);
	}
	for (auto& names : factNames) {
        output << database.getRelations()[names].toString(true) << endl;
	}
}

void Interpreter::evaluateQueries() {
    output << "Query Evaluation" << endl << endl;
	for (unsigned int i = 0; i < queriesList.size(); i++) {
		output << queriesList[i].toString() << "?";
		string name = queriesList[i].getID();
		Relation r = database.getRelations()[name];
		bool found = false;
		vector<int> varPos;
		vector<string> varName;
		map<string, int> variables;
		//select for loops
		int paramSize = queriesList[i].getParams().size();
        for (int j = 0; j < paramSize; ++j) {
			Parameter p1 = queriesList[i].getParams()[j];
			string value = p1.getValue();
			if (variables.count(value) == 0 && p1.getisID()) {
				variables[value] = j;
				varPos.push_back(j);
				varName.push_back(value);
			}
			else if (!p1.getisID()) {
				found = r.selectValue(j, p1.getValue());
			}
			else {
				found = r.selectVariables(variables[p1.getValue()], j);
			}
		}
        interpPrint(found, varName, r, i);
        //project for loops
        interpProject(found, varName, varPos, r);
        //rename
        interpRename(found,varName,varPos,r);
    }
    output.close();
}

void Interpreter::evaluateRules() {
	output << "Rule Evaluation" << endl << endl;
	int ruleSize = rulesList.size();
    int tupleCount = -1;
    int converge = 0;
	while (tupleCount != database.getTupleCount()) {
		converge++;
		tupleCount = database.getTupleCount();
		for (int i = 0; i < ruleSize; ++i) {
			map<string, Relation> relations = database.getRelations();
			Predicate pred1 = rulesList[i].getPred();
			vector<Parameter> params = pred1.getParams();
			vector<Predicate> preds = rulesList[i].getPreds();
			vector<pair<int, int>> matches;
			vector<string> varNames;
			Relation newRelation;
			vector<int> varPos;
			int schemeSize = 0; 
			int predSize = preds.size();
			output << rulesList[i].toString() << endl;

			if (predSize == 1) {
				onePredicate(varNames, preds, varPos, pred1, newRelation, relations);
				newRelation.setName(pred1.getID());
				if (newRelation.getTupleCount() != 0) {
					newRelation.project(varPos);
					newRelation.rename(varPos, varNames);
				}
			}
			else {
				evaluatePredicateJoins(i, schemeSize, matches, newRelation, relations);
				setNewSchemes(params, varPos, newRelation);
				newRelation.project(varPos);
				findRenameSchemes(pred1,varNames);
				newRelation.rename(varPos, varNames);
			}
			Relation tempR = findNewFacts(newRelation, newRelation.getName());
			Scheme newScheme = newRelation.getScheme();
            for (unsigned int j = 0; j < newScheme.size(); ++j) {
				tempR.setScheme(newScheme[j]);
			}
			tempR.setName(newRelation.getName());
			unionFacts(newRelation, relations);
			if (tupleCount != database.getTupleCount()) {
				output << tempR.toString(false);
			}			
		}
	}
	output << endl << "Converged after " << to_string(converge) << " passes through the Rules." << endl << endl;
	output << database.toString();
}

void Interpreter::interpPrint(bool &found, vector<string>& varName, Relation& r, unsigned int& i) {
    if (queriesList[i].getParams().size() == r.getScheme().size() && factsList.size() > 0) {
        found = true;
		int size = r.getTuples().size();
        r.setMatches(size);
    }
    if (found && r.getMatches() > 0) {
        output << " Yes(" << to_string(r.getMatches()) << ")" << endl << "select" << endl << r.toString(false);
    }
    else {
        found = false;
        output << " No" << endl << endl;
    }
}

void Interpreter::interpProject(bool& found, vector<string>& varName, vector<int>& varPos, Relation &r) {
    if (found && varName.size() > 0) {
        r.project(varPos);
        output << "project" << endl << r.toString(false);
    }
    else if(found)
        output << "project" << endl;
}

void Interpreter::interpRename(bool& found, vector<string>& varName, vector<int>& varPos, Relation &r) {
    if (found && varName.size() > 0) {
        r.rename(varPos, varName);
        output << "rename" << endl << r.toString(false) << endl;
    }
    else if(found)
        output << "rename" << endl << endl;
}

void Interpreter::onePredicate(vector<string>& varNames, vector<Predicate>& preds, vector<int>& varPos, Predicate& pred, Relation& newRelation, map<string, Relation>& relations) {
	
	Relation r = relations.at(preds[0].getID());
	vector<Parameter> params1 = pred.getParams();
	vector<Parameter> params2 = preds[0].getParams();
	int param1Size = params1.size();
	int param2Size = params2.size();
	set<string> variables;
	for (int i = 0; i < param1Size; ++i) {
        string value1 = params1[i].getValue();

		varPos.push_back(i);
		for (int j = 0; j < param2Size; ++j) {
			string value2 = params2[j].getValue();
			if (i == param1Size - 1) {
				newRelation.setScheme(value2);
			}
			if (value1 == value2) {
			}
		}
	}

	findRenameSchemes(pred,varNames);
	selectLiterals(r,params2, pred);
	set<Tuple> tuples = r.getTuples();
	for (set<Tuple>::iterator it = tuples.begin(); it != tuples.end(); ++it) {
		Tuple t1 = *it;
		newRelation.setTuples(t1);
	}	
}

vector<Parameter> Interpreter::combineSchemes(Relation& r1, Relation& r2, vector<pair<int,int>>& matches, vector<string>& schemes, Relation& newRelation) {
	vector<Parameter> params;
	Scheme scheme1 = r1.getScheme();
	Scheme scheme2 = r2.getScheme();
	int scheme1Size = scheme1.size();
	int scheme2Size = scheme2.size();
	for (int i = 0; i < scheme1Size; ++i) {
		string v1 = scheme1[i];
		schemes.push_back(v1);
		for (int j = 0; j < scheme2Size; ++j) {
			string v2 = scheme2[j];
			if (v1 == v2) {
				pair<int, int> match1 = { i, j };
				matches.push_back(match1);
			}
			if (i == scheme1Size - 1) {
				schemes.push_back(scheme2[j]);
			}
		}
	}
    handleDuplicateMatches(schemes, newRelation, params,matches);
	return params;
}

void Interpreter::interpJoin(vector<pair<int,int>>& matches, Relation& newRelation,set<Tuple>& tuples1, set<Tuple>& tuples2) {
	map<string, Relation> relations = database.getRelations();
	newRelation.clearTuples();
	if(matches.size() == 0)
	matchlessJoin(tuples1, tuples2, newRelation);
	else
	iterateTuples(matches, newRelation, tuples1, tuples2);
}

void Interpreter::relationJoin(Tuple& t1, Tuple& t2, Relation& newRelation,vector<bool>& match) {
	int tupleSize1 = t1.size();
	int tupleSize2 = t2.size();
	Tuple newTuple;
	for (int i = 0; i < tupleSize1; ++i) {
		newTuple.push_back(t1[i]);
	}
	for (int i = 0; i < tupleSize2; ++i) {
		if(match[i])
		newTuple.push_back(t2[i]);		
	}
	newRelation.setTuples(newTuple);
}

Relation Interpreter::unionFacts(Relation& newRelation, map<string,Relation>& relations) {
    set<Tuple> tuples = newRelation.getTuples();
	Relation tempR = relations.at(newRelation.getName());
	for (set<Tuple>::iterator it = tuples.begin(); it != tuples.end(); ++it) {
		Tuple t = *it;
		tempR.setTuples(t);
	}
	pair<string, Relation> pair = { newRelation.getName(), tempR };
	database.setRelations(pair);
	return tempR;
}

void Interpreter::setNewSchemes(vector<Parameter>& parameter, vector<int>& varPos, Relation& newRelation) {

	vector<string> projectVars;
	for (unsigned int i = 0; i < parameter.size(); ++i) {
		string param = parameter[i].getValue();
		projectVars.push_back(param);
	}
	Scheme schemes = newRelation.getScheme();
	int schemeSize = newRelation.getScheme().size();
	int varSize = projectVars.size();
	for (int i = 0; i < varSize; ++i) {
		for (int j = 0; j < schemeSize; ++j) {
			if (projectVars[i] == schemes[j]) {
				varPos.push_back(j);
				break;
			}
		}
	}
		
}

Relation Interpreter::findNewFacts(Relation& r1,string name) {
	Relation tempR;
	map<string, Relation> relations = database.getRelations();
	Relation rData = relations.at(name);
	set<Tuple> tData = rData.getTuples();
	set<Tuple> t1 = r1.getTuples();
	for (set<Tuple>::iterator it = tData.begin(); it != tData.end(); ++it) {
		Tuple t = *it;
		t1.erase(t);
	}
	for (set<Tuple>::iterator it = t1.begin(); it != t1.end(); ++it) {
		Tuple t = *it;
		tempR.setTuples(t);
	}
	return tempR;
}
/*
string Interpreter::createName(vector<string>& v) {
	string output;
	for (unsigned int i = 0; i < v.size(); ++i) {
		output += v[i];
	}
	return output;
}

void Interpreter::makeVarNames(Relation& newRelation, vector<string>& varNames) {
	for (unsigned int j = 0; j < schemesList.size(); ++j) {
		if (schemesList[j].getID() == newRelation.getName()) {
			vector<Parameter> p1 = schemesList[j].getParams();
			int paramSize = p1.size();
			for (int k = 0; k < paramSize; ++k) {
				string values = p1[k].getValue();
				varNames.push_back(values);
			}
		}
	}
}*/

void Interpreter::evaluatePredicateJoins(int& i, int& schemeSize, vector<pair<int,int>>& matches, Relation& newRelation, map<string, Relation>& relations) {
	vector<string> schemes;
	vector<Parameter> params1;
	vector<Predicate> preds = rulesList[i].getPreds();
	Predicate pred1 = rulesList[i].getPred();
	string predName1;
	map<string, int> match;
	Relation r1;
	set<Tuple> tuples1;

	for (unsigned int j = 0; j < preds.size(); ++j) {
		if (j == 0) {
			params1 = preds[j].getParams();
			predName1 = preds[j].getID();
			r1 = relations.at(predName1);
			findLiterals(r1, params1, pred1);
			tuples1 = r1.getTuples();
		}
		if (j + 1 < preds.size()) {
			tuples1 = r1.getTuples();
			vector<Parameter> params2 = preds[j + 1].getParams();
			string predName2 = preds[j + 1].getID();
			Relation r2 = relations.at(predName2);
				
			findLiterals(r2, params2, pred1);
			set<Tuple> tuples2 = r2.getTuples();
			params1 = combineSchemes(r1, r2, matches, schemes, newRelation);
			//predName1 = createName(schemes);
			interpJoin(matches, newRelation,tuples1, tuples2);
			newRelation.setName(rulesList[i].getPred().getID());
			schemeSize = schemes.size();
			r1 = newRelation;

			//r1.setName(predName1);
			if (j != preds.size() - 2) {
                schemes.clear();
				newRelation.clearSchemes();
			}
		}
		matches.clear();
	}
}
/*
void Interpreter::removeTempRelations() {
	map<string, Relation> relations = database.getRelations();
	for (map<string, Relation>::iterator it = relations.begin(); it != relations.end(); ++it) {
		bool found = false;
		pair<string, Relation> p = *it;
		int fake = p.second.getScheme().size();
		if (fake == 0) {
			database.removeRelation(p.first);
		}
	}
}*/

void Interpreter::matchlessJoin(set<Tuple>& tuples1, set<Tuple>& tuples2, Relation& newRelation) {

	for (set<Tuple>::iterator it1 = tuples1.begin(); it1 != tuples1.end(); ++it1) {
		Tuple t1 = *it1;
		for (set<Tuple>::iterator it2 = tuples2.begin(); it2 != tuples2.end(); ++it2) {
			Tuple t2 = *it2;
			for (unsigned int j = 0; j < t2.size(); ++j) {
				t1.push_back(t2[j]);
			}
			newRelation.setTuples(t1);
			t1 = *it1;
		}
	}
}

void Interpreter::joinable(vector<pair<int, int>>& matches, Tuple& t1, Tuple& t2, Relation& newRelation,vector<bool>& match) {
	bool join = true;
	int matchSize = matches.size();
	for (int i = 0; i < matchSize; ++i) {
		pair<int, int> pair1 = matches[i];
		match[pair1.second] = false;
		if (t1[pair1.first] != t2[pair1.second]) {
			join = false;
			break;
		}
	}
	if (join) {
		relationJoin(t1, t2, newRelation, match);
	}
}

void Interpreter::findLiterals(Relation& r, vector<Parameter>& params, Predicate& pred) {
	Scheme scheme = r.getScheme();
	if (scheme.size() == 0)
        return;
	vector<int> varPos;
    set<string> varName;
	vector<string> varNames;
	map<string, int> schemeMatch;
	/*
	vector<Parameter> params1 = pred.getParams();
	for (int i = 0; i < params.size(); ++i) {
		string v1 = params[i].getValue();
		for (int j = 0; j < params2.size(); ++j) {
			string v2 = params2[j].getValue();
			if (v1 == v2) {
				schemes.insert(params[i].getValue());
			}
		}
	}*/
	/*
	for (int i = 0; i < paramSize; ++i) {
	string v1 = params[i].getValue();
	int count = 0;
	for (int j = 0; j < paramSize; ++j) {
	string v2 = params[j].getValue();
	if (v1 == v2 && params[i].getisID())
	count++;
	}
	pair<string, int> num = { v1, count };
	schemeNum.insert(num);
	}
	*/

	doSelect(r, params, varName, varPos, schemeMatch);

	/*
	for (set<string>::iterator it = varName.begin(); it != varName.end(); ++it) {
		string s = *it;
		if (schemes.count(s) > 0)
			varNames.push_back(*it);
	}

	if (varPos.size() == 0) {
		for (int i = 0; i < pred.getParams().size(); ++i) {
			string v1 = params1[i].getValue();
			for (int j = 0; j < paramSize; ++j) {
				string v2 = params[j].getValue();
				if (v1 == v2)
					varPos.push_back(j);
			}
		}
	}
	*/

    for (size_t i = 0; i < params.size(); ++i) {
		varNames.push_back(params[i].getValue());
	}
	r.rename(varPos, varNames);
	
}

void Interpreter::iterateTuples(vector<pair<int, int>>&matches,Relation& newRelation, set<Tuple>& tuples1, set<Tuple>& tuples2) {
	Tuple t1;
	Tuple t2;
	vector<bool> match;	
	set<Tuple>::iterator it = tuples2.begin();
	if (it != tuples2.end()) {
		Tuple t = *it;
		int size = t.size();
		for (int i = 0; i < size; ++i) {
			match.push_back(true);
		}
	}
		for (set<Tuple>::iterator it1 = tuples1.begin(); it1 != tuples1.end(); ++it1) {
			t1 = *it1;
			for (set<Tuple>::iterator it2 = tuples2.begin(); it2 != tuples2.end(); ++it2) {
				t2 = *it2;
				joinable(matches, t1, t2, newRelation, match);
			}
		}
}

void Interpreter::selectLiterals(Relation& r, vector<Parameter>& params, Predicate& pred) {
	if (r.getScheme().size() == 0)
        return;
	vector<int> varPos;
	set<string> varName;
	set<string> schemes;
	vector<string> varNames;
    map<string,int> schemeMatch;
	
	vector<Parameter> params1 = pred.getParams();
    for (size_t i = 0; i < params1.size(); ++i) {
		schemes.insert(params1[i].getValue());
	}
	/*
	for (int i = 0; i < paramSize; ++i) {
		string v1 = params[i].getValue();
		int count = 0;
		for (int j = 0; j < paramSize; ++j) {
			string v2 = params[j].getValue();
			if (v1 == v2 && params[i].getisID())
				count++;
		}
		pair<string, int> num = { v1, count };
		schemeNum.insert(num);
	}
	*/

	doSelect(r, params, varName, varPos, schemeMatch);


	for (set<string>::iterator it = varName.begin(); it != varName.end(); ++it) {
		string s = *it;
		if(schemes.count(s) > 0) 
			varNames.push_back(*it);
	}

    noliterals(pred,varPos,params, params1);

		r.project(varPos);
		r.rename(varPos, varNames);

}

void Interpreter::findRenameSchemes(Predicate& pred, vector<string>& names) {
    string name = pred.getID();
    vector<Parameter> params;
        for (unsigned int i = 0; i < schemesList.size(); ++i) {
            if (schemesList[i].getID() == name) {
                params = schemesList[i].getParams();
                break;
            }
        }
        for (unsigned int i = 0; i < params.size(); ++i) {
           names.push_back(params[i].getValue());
        }
}

void Interpreter::doSelect(Relation& r, vector<Parameter>& params, set<string>& varName, vector<int>& varPos, map<string,int>& schemeMatch) {
	int paramSize = params.size();
	for (int i = 0; i < paramSize; ++i) {
		bool select = params[i].getisID();
		string value = params[i].getValue();
		if (!select) {
			r.selectValue(i, value);
		}
		else {
            size_t varSize = varName.size();
			varName.insert(value);
			if (varSize == varName.size())
				varPos.push_back(i);
		}
	}
    size_t schemeSize = schemeMatch.size();
	for (int i = 0; i < paramSize; ++i) {
		string value = params[i].getValue();
		pair<string, int> pair1 = { value, i };
		schemeMatch.insert(pair1);
		schemeSize++;
		if (schemeSize != schemeMatch.size()) {
			int pos = schemeMatch.at(value);
			r.selectVariables(i, pos);
		}
	}
}

void Interpreter::noliterals(Predicate& pred, vector<int>& varPos, vector<Parameter>& params,vector<Parameter>& params1){
    if (varPos.size() == 0) {
        int paramSize = params.size();
        for (size_t i = 0; i < pred.getParams().size(); ++i) {
            string v1 = params1[i].getValue();
            for (int j = 0; j < paramSize; ++j) {
                string v2 = params[j].getValue();
                if(v1 == v2)
                    varPos.push_back(j);
            }
        }
    }
}

void Interpreter::handleDuplicateMatches(vector<string>&schemes,Relation& newRelation, vector<Parameter>& params,vector<pair<int,int>>& matches) {
    map<string, int> schemeMap;
    int tempSize = 0;
    if (matches.size() != 0) {
        string name;
        for (unsigned int i = 0; i < schemes.size(); ++i) {
            string scheme = schemes[i];
            Parameter p;
            pair <string, int> schemePos = { scheme, i };
            schemeMap.insert(schemePos);
            tempSize++;
            int mapSize = schemeMap.size();
            if (tempSize == mapSize) {
                name += scheme;
                newRelation.setScheme(scheme);
                p.setValue(scheme);
                p.setisID(true);
                params.push_back(p);
                continue;
            }
            else {
                schemes.erase(schemes.begin() + i);
                tempSize--;
                i--;
            }
        }

        newRelation.setName(name);
    }
    else {

        for (unsigned int i = 0; i < schemes.size(); ++i) {
            newRelation.setScheme(schemes[i]);
        }
    }
}

module dranges.properties;

// TODO: suppressProperty?
import std.stdio: writeln;
import std.conv: to;

public import std.variant;

template addProperties() {

    Variant[] propertiesValues;
    int[string] propertiesNames;

    bool hasProperty(string propertyName) {
        if (propertyName in propertiesNames) return true;
        return false;
    }

    bool hasProperties() {
        return (propertiesValues.length == 0 ? false : true);
    }

    void addProperty(T)(string propertyName, T val) {
        if (hasProperty(propertyName)) {
            throw new Exception("Property " ~ propertyName ~ " already existing.");
        } else {
            propertiesNames[propertyName] = propertiesValues.length; // index in the 'propertiesValues' array
            propertiesValues ~= Variant(val);
        }
    }

    void addProperties(T, R...)(string propertyName, T val, R rest) {
        addProperty(propertyName, val);
        static if (rest.length>1)
            addProperties(rest);
        static if (rest.length == 1)
            throw new Exception("addProperties: the arguments list has not a ('name', value) form.");
    }

    void changeProperty(T)(string propertyName, T newVal) {
        if (hasProperty(propertyName)) {
            propertiesValues[propertiesNames[propertyName]] = newVal;
        }
        else {
            addProperty(propertyName, newVal);
        }
    }

    T getProperty(T)(string propertyName) {
        if (hasProperty(propertyName)) {
            return propertiesValues[propertiesNames[propertyName]].get!(T);
        }
        else {
            throw new Exception(propertyName ~ ": no such property.");
        }
    }

    string name() {
        return hasProperty("name") ? getProperty!string("name")
                                   : "anonymous " ~ typeof(this).stringof;
    }

    /// todo : change this function's name
    string[] getPropertiesNames() {
        return propertiesNames.keys;
    }

    /// To be tested!
    void copyProperties(T)(T source) {
        if (source.hasProperties) {
            propertiesValues = source.propertiesValues;
            propertiesNames = source.propertiesNames;
        }
    }

    void writeProperties() {
        string ts;
        foreach(string name; propertiesNames.keys) {
//            int p =
            ts ~= name ~ ": " ~ std.conv.to!string(propertiesNames[name]) ~ " ";
        }
        writeln(ts);
    }

}

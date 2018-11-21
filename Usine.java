/*@ predicate tache(Tache t; int temps_necessaire, int gain) = 
		t.temps_necessaire |-> temps_necessaire 
		&*& t.gain |-> gain
		&*& gain >= 0
		&*& temps_necessaire >= 0 ; @*/

class Tache
{
	private int temps_necessaire;
	private int gain;
	
	
	
	public Tache(int temps_necessaire, int gain)
	//@requires true;
	//@ensures this.temps_necessaire |-> temps_necessaire &*& this.gain |-> gain;
	{
		this.temps_necessaire = temps_necessaire;
		this.gain = gain;
	}
	
	
	public int get_temps_necessaire()
	//@requires tache(this, ?t, _);
	//@ensures tache(this, t, _) &*& result == t &*& result >= 0;
	{
		return this.temps_necessaire;
	}
	
	
	
	public int get_gain()
	//@requires tache(this, _, ?g);
	//@ensures tache(this, _, g) &*& result == g &*& result >= 0;
	{
		return this.gain;
	}
	
}


/*@predicate travailleur(Travailleur t; int temps_dispo, int salaire_horaire, int salaire_percu) = t.temps_dispo |-> temps_dispo 
												   &*& t.salaire_horaire |-> salaire_horaire
												   &*& t.salaire_percu |-> salaire_percu;@*/
												   
class Travailleur
{
	private int temps_dispo;
	private int salaire_horaire;
	private int salaire_percu;
	
	public Travailleur(int temps_dispo, int salaire_horaire)
	//@requires true;
	//@ensures this.salaire_horaire |-> salaire_horaire &*& this.temps_dispo |-> temps_dispo &*& this.salaire_percu |-> 0;
	{
		this.temps_dispo = temps_dispo;
		this.salaire_horaire = salaire_horaire;
		this.salaire_percu = 0;
	}
	
	public int get_temps_dispo()
	//@requires travailleur(this, ?t, _, _);
	//@ensures travailleur(this, t, _, _) &*& result == t;
	{
		return this.temps_dispo;
	}
	
	public int get_salaire_horaire()
	//@requires travailleur(this, _, ?s, _);
	//@ensures travailleur(this, _, s, _) &*& result == s;
	{
		return this.salaire_horaire;
	}
	
	public int get_salaire_percu()
	//@requires travailleur(this, _, _, ?s);
	//@ensures travailleur(this, _, _, s) &*& result == s;
	{
		return this.salaire_percu;
	}
	
	public int travailler(int t)
	//@requires travailleur(this, _, ?s1, ?s2) &*& t > 0;
	//@ensures travailleur(this, _, s1, s2 + (t*s1));
	{
		int salaire_calculé = t*this.salaire_horaire;
		this.salaire_percu += salaire_calculé;
		return salaire_calculé;
	}
}







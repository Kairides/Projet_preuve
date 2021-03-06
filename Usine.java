/*@ predicate tache(Tache t; int temps_necessaire, int gain) = 
		t.temps_necessaire |-> temps_necessaire 
		  &*& t.gain |-> gain
		  &*& gain > 0
		  &*& temps_necessaire > 0 ; @*/

class Tache
{
	private int temps_necessaire;
	private int gain;
	
	
	
	public Tache(int t, int g)
	//@requires t> 0 &*& g > 0;
	//@ensures tache(this, t, g);
	{
		this.temps_necessaire = t;
		this.gain = g;
	}
	
	
	public int get_temps_necessaire()
	//@requires tache(this, ?t, ?g);
	//@ensures tache(this, t, g) &*& result == t;
	{
		return this.temps_necessaire;
	}
	
	
	
	public int get_gain()
	//@requires tache(this, ?t, ?g);
	//@ensures tache(this, t, g) &*& result == g;
	{
		return this.gain;
	}
	
}


/*@predicate travailleur(Travailleur t; int temps_dispo, int salaire_horaire, int salaire_percu) = t.temps_dispo |-> temps_dispo 
												   &*& t.salaire_horaire |-> salaire_horaire
												   &*& t.salaire_percu |-> salaire_percu
												   &*& temps_dispo >= 0
												   &*& salaire_horaire > 0;@*/
												   
class Travailleur
{
	private int temps_dispo;
	private int salaire_horaire;
	private int salaire_percu;
	
	public Travailleur(int temps_dispo, int salaire_horaire)
	//@requires temps_dispo > 0 && salaire_horaire > 0;
	//@ensures travailleur(this,temps_dispo, salaire_horaire, 0);
	{
		this.temps_dispo = temps_dispo;
		this.salaire_horaire = salaire_horaire;
		this.salaire_percu = 0;
	}
	
	public int get_temps_dispo()
	//@requires travailleur(this, ?t, ?s, ?sp);
	//@ensures travailleur(this, t, s, sp) &*& result == t;
	{
		return this.temps_dispo;
	}
	
	public int get_salaire_horaire()
	//@requires travailleur(this, ?t, ?s, ?sp);
	//@ensures travailleur(this, t, s, sp) &*& result == s;
	{
		return this.salaire_horaire;
	}
	
	public int get_salaire_percu()
	//@requires travailleur(this, ?t, ?s, ?sp);
	//@ensures travailleur(this, t, s, sp) &*& result == sp;
	{
		return this.salaire_percu;
	}
	
	public int travailler(int t1)
	//@requires travailleur(this, ?t, ?s1, ?s2) &*& t1 > 0 &*& t >= t1;
	//@ensures travailleur(this, t -t1, s1, s2 + (t1*s1)) &*& result == s1*t1;
	{
		int salaire_calcul� = t1*this.salaire_horaire;
		this.salaire_percu += salaire_calcul�;
		this.temps_dispo -= t1;
		return salaire_calcul�;
	}
}


/*@predicate usine(Usine this; int b) = this.money |-> b;@*/

class Usine
{
	private int money;
	
	public Usine(int depot_initial)
	//@requires true;
	//@ensures usine(this, depot_initial);
	{
		this.money = depot_initial;
	}
	
	public int get_balance()
	//@requires usine(this, ?b);
	//@ensures usine(this, b) &*& result == b;
	{
		return this.money;
	}
	
	public void depot(int montant)
	//@requires usine(this, ?yves);
	//@ensures usine(this, yves + montant);
	{
		this.money += montant;
	}
	
	public void effectuer_tache(Tache tache, Travailleur travailleur)
	//@requires usine(this, ?yves) &*& tache(tache,?t,?g) &*& travailleur(travailleur,?t1,?s1,?sp1) &*& t1 >= t;
	/*@ensures (g>t*s1) == true ? usine(this, yves - t*s1 + g) &*& tache(tache,t,g) &*& travailleur(travailleur, t1 - t, s1, sp1 + t*s1) :
				      usine(this, yves) &*& tache(tache,t,g) &*& travailleur(travailleur,t1,s1,sp1) ;@*/
	{
		//@open tache(tache, _,_);
		//@open travailleur(travailleur,_,_,_);
		if (est_rentable(tache, travailleur)){
			depot(-travailleur.travailler(tache.get_temps_necessaire()));
			depot(tache.get_gain());
		}
	}
	
	public static boolean est_rentable(Tache tache, Travailleur travailleur)
	//@requires tache(tache, ?t, ?g) &*& travailleur(travailleur, ?t1, ?s1, ?sp1) &*& tache != null &*& travailleur != null;
	//@ensures tache(tache, t, g) &*& travailleur(travailleur, t1,s1,sp1) &*& result == (g>t*s1);
	{
		return (tache.get_gain() > travailleur.get_salaire_horaire()*tache.get_temps_necessaire());
	}
	
}

class UsineTest
{
	public static void main(String[] args)
	//@requires true;
	//@ensures true;
	{
		Usine usine = new Usine(5000);
		Tache tache = new Tache(25,1000);
		Travailleur travailleur = new Travailleur(50,10);
		
		int toi = usine.get_balance();
		assert toi == 5000;
		
		int thunes = travailleur.get_salaire_percu();
		assert thunes == 0;
		
		int temps_init = travailleur.get_temps_dispo();
		assert temps_init == 50;
		
		boolean rentable = usine.est_rentable(tache, travailleur);
		
		assert rentable;

		usine.effectuer_tache(tache, travailleur);
		
		toi = usine.get_balance();
		assert toi == 5750;
		
		int temps_apres = travailleur.get_temps_dispo();
		assert temps_apres == 25;
		
		thunes = travailleur.get_salaire_percu();
		assert thunes == 250;
		
	}
}







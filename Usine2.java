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
	//@ensures tache(this, t, g) &*& estEffectuée(this);
	{
		this.temps_necessaire = t;
		this.gain = g;
		//@close estEffectuée(this);
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

//@predicate estEmbauché(Usine usine, Travailleur travailleur) = true;
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
		int salaire_calculé = t1*this.salaire_horaire;
		this.salaire_percu += salaire_calculé;
		this.temps_dispo -= t1;
		return salaire_calculé;
	}
}


//@predicate estEffectuée(Tache tache) = true; 
/*@predicate usine(Usine this; int b, int a) = this.gains_accumulés |-> b &*& this.depenses_salaires |-> a &*& b > 0;@*/

class Usine
{
	int gains_accumulés, depenses_salaires;
	
	public Usine(int depot_initial)
	//@requires depot_initial > 0;
	//@ensures usine(this, depot_initial, 0);
	{
		this.gains_accumulés = depot_initial;
	}
	
	public int get_balance()
	//@requires usine(this, ?b, ?a);
	//@ensures usine(this, b, a) &*& result == b -a;
	{
		return this.gains_accumulés - this.depenses_salaires;
	}
	
	public void depot(int montant)
	//@requires usine(this, ?yves, ?a) &*& montant > 0;
	//@ensures usine(this, yves + montant, a);
	{
		this.gains_accumulés += montant;
	}
	
	public void retrait(int montant)
	//@requires usine(this, ?b, ?yves);
	//@ensures usine(this, b, yves + montant);
	{
		this.depenses_salaires += montant;
	}
	
	
	public void effectuer_tache(Tache tache, Travailleur travailleur)
	/*@requires usine(this, ?yves, ?b) &*& tache(tache,?t,?g) 
					   &*& travailleur(travailleur,?t1,?s1,?sp1) 
					   &*& t1 >= t &*& estEffectuée(tache)
					   &*& estEmbauché(this, travailleur);@*/
	/*@ensures (g>t*s1) == true ? usine(this, yves + g, b + t*s1) &*& tache(tache,t,g) &*& travailleur(travailleur, t1 - t, s1, sp1 + t*s1) &*& estEmbauché(this, travailleur):
				      usine(this, yves, b) &*& tache(tache,t,g) &*& travailleur(travailleur,t1,s1,sp1) ;@*/
	{
		//@open tache(tache, _,_);
		//@open travailleur(travailleur,_,_,_);
		if (est_rentable(tache, travailleur)){
			retrait(travailleur.travailler(tache.get_temps_necessaire()));
			depot(tache.get_gain());
		}
	}
	
	public static boolean est_rentable(Tache tache, Travailleur travailleur)
	//@requires tache(tache, ?t, ?g) &*& travailleur(travailleur, ?t1, ?s1, ?sp1) &*& tache != null &*& travailleur != null;
	//@ensures tache(tache, t, g) &*& travailleur(travailleur, t1,s1,sp1) &*& result == (g>t*s1);
	{
		return (tache.get_gain() > travailleur.get_salaire_horaire()*tache.get_temps_necessaire());
	}
	
	public void embaucher(Travailleur travailleur)
	//@requires travailleur(travailleur, ?temps_dispo, ?salaire_horaire, ?salaire_percu);
	//@ensures travailleur(travailleur, temps_dispo, salaire_horaire, salaire_percu) &*& estEmbauché(this, travailleur);
	{
		//@close estEmbauché(this, travailleur);
	}
	
	public void licencier(Travailleur travailleur)
	//@requires travailleur(travailleur, ?temps_dispo, ?salaire_horaire, ?salaire_percu) &*& estEmbauché(this, travailleur);
	//@ensures travailleur(travailleur, temps_dispo, salaire_horaire, salaire_percu);
	{
		//@open estEmbauché(this, travailleur);
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
		Tache tache2 = new Tache(2, 47000);
		Travailleur travailleur = new Travailleur(50,10);
		usine.embaucher(travailleur);
		//usine.licencier(travailleur);
		
		int toi = usine.get_balance();
		assert toi == 5000;
		
		int thunes = travailleur.get_salaire_percu();
		assert thunes == 0;
		
		int temps_init = travailleur.get_temps_dispo();
		assert temps_init == 50;
		
		boolean rentable = usine.est_rentable(tache, travailleur);
		
		assert rentable;
		
		usine.effectuer_tache(tache, travailleur);
		usine.effectuer_tache(tache2, travailleur);
		
		toi = usine.get_balance();
		assert toi == 5750;
		
		int temps_apres = travailleur.get_temps_dispo();
		assert temps_apres == 25;
		
		thunes = travailleur.get_salaire_percu();
		assert thunes == 250;
		
		//usine.effectuer_tache(tache, travailleur);
		
	}
}







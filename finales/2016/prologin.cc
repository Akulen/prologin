#include <algorithm>
#include <cstdio>
#include <queue>

#include <ctime>

#include "prologin.hh"

using namespace std;

const int oo = 1E9;
const int MOI = 1;
const int ADV = 0;

int id, adv;

int idDejaVu = 0;

// Structure rassemblant les infos calculiees sur les cases (pour chaque tableau [2], [ADV] est relatif a l'adversaire et [MOI] a moi) :
// distBase : distance a la base la plus proche du joueur par rapport a un bfs
// dejaVu marqueur utilise par les bfs, dijkstras et dfs
// prof, remontee, nbVoisins et essentiel servent pour determiner les tuyaux essentiels de chaque joueur
// flot represente la quantite de plasma qui circulera par cette case si le reseau n'evolue plus (sans prendre en compte les supertuyaux)

struct Case
{
	int distBase[2], dejaVu;
	int prof[2], remontee[2];
	bool essentiel[2];
	int nbVoisins[2];
	double flot[2];
	Case() {}
	void reset(bool full = false)
	{
		distBase[ADV] = oo;
		distBase[MOI] = oo;
		if(full)
		{
			nbVoisins[MOI] = 0;
			prof[MOI] = -1;
		}
		prof[ADV] = -1;
		nbVoisins[ADV] = 0;
		dejaVu = 0;
		flot[MOI] = 0;
		flot[ADV] = 0;
	}
};

Case grille[TAILLE_TERRAIN][TAILLE_TERRAIN];

// Reecriture de la classe position ajoutant des fonctions utiles :
// l'operateur +
// determiner si la position est valide (dans la grille)
// convertir en position pour les fonctions de la lib
// retourner la liste des voisins valides
// getGrille retourne la case correspondante du tableau grille
// newPlasma retourne la somme du plasma qui apparaitra sur cette case durant le reste de la partie

struct Position
{
	int x, y;
	Position(int x = 0, int y = 0) : x(x), y(y) {}
	Position operator+(const Position& droite) const
	{
		return Position(x + droite.x, y + droite.y);
	}
	bool withinBounds()
	{
		return (x >= 0 && x < TAILLE_TERRAIN && y >= 0 && y < TAILLE_TERRAIN && type_case(*this) != INTERDIT);
	}
	vector<Position> voisins();
	position pos()
	{
		position retour;
		retour.x = x;
		retour.y = y;
		return retour;
	}
	Case getGrille() const
	{
		return grille[x][y];
	}
	int newPlasma()
	{
		int plasma = 0;
		auto neighbours = this->voisins();
		for(auto voisin = neighbours.begin(); voisin != neighbours.end(); ++voisin)
			if(est_pulsar(voisin->pos()))
				plasma += plasmaRestant(*voisin);
		return plasma;
	}
};

Position dirs[4] = {Position(-1,0), Position(1,0), Position(0,-1), Position(0,1)};

vector<Position> Position::voisins()
{
	vector<Position> retour;
	for(int iDir = 0; iDir < 4; ++iDir)
		if((*this + dirs[iDir]).withinBounds())
			retour.push_back(*this + dirs[iDir]);
	return retour;
}

// Structure permettant de choisir le tuyau essentiel a rendre non essentiel ou le tuyau a detruire

struct Cible
{
	Position pos;
	double gain;
	Cible(Position pos = Position(-1, -1), double gain = -oo) : pos(pos), gain(gain) {}
	bool operator < (const Cible & droite) const
	{
		return gain < droite.gain;
	}
};

// structure permettant de connaitre le premier deplacement ayant amene a cette position dans un dijkstra ou un bfs
// voisins retourne la liste des voisins

struct Chemin
{
	Position pos;
	int longueur;
	int score;
	int dist;
	Position depart;
	Chemin(Position pos = Position(-1,-1), int longueur = 0, int score = 0, int dist = 0, Position depart = Position(-1,-1)) : pos(pos), longueur(longueur), score(score), dist(dist), depart(depart) {}
	Chemin operator + (const Chemin& droite) const
	{
		return Chemin(pos + droite.pos, longueur + droite.longueur, score + droite.score, (depart.x == -1) ? (pos + droite.pos).getGrille().distBase[MOI] : dist + droite.dist, (depart.x == -1) ? pos + droite.pos : depart);
	}
	bool operator < (const Chemin& droite) const
	{
		// ATTENTION : SegFault Quantique non causatif (ne respectant pas la loi de la causalite)
		// il est hautement probable que si les deux prochaines variables intermediaires sont retirees, ce programme segfault.
		int diff1 = longueur - score;
		int diff2 = droite.longueur - droite.score;
		/*if((pos.x == 9 && pos.y == 30) || (pos.x == 10 && pos.y == 29))
			printf("%d : (%d %d %d) %d %d\n", pos.x, depart.x, depart.y, depart.getGrille().distBase[MOI], longueur, score);
		if((droite.pos.x == 9 && droite.pos.y == 30) || (droite.pos.x == 10 && droite.pos.y == 29))
			printf("%d : (%d %d %d) %d %d\n", droite.pos.x, droite.depart.x, droite.depart.y, droite.depart.getGrille().distBase[MOI], droite.longueur, droite.score);
		*/
		if(2*diff1 + dist != 2*diff2 + droite.dist)
			return 2*diff1 + dist > 2*diff2 + droite.dist;
		if(diff1 != diff2)
			return diff1 > diff2;
		return longueur > droite.longueur;
	}
	vector<Chemin> voisins()
	{
		vector<Chemin> retour;
		for(int iDir = 0; iDir < 4; ++iDir)
			if((this->pos + dirs[iDir]).withinBounds())
				retour.push_back(*this + Chemin(dirs[iDir], 1));
		return retour;
	}
};

void partie_init()
{
	id = moi();
	adv = adversaire();
}

void jouer_tour()
{
	//printf("\n");
	//auto debutTime = clock();
	
	//// Etape 1 : remplir grille

	idDejaVu = 0;
	for(int x = 0; x < TAILLE_TERRAIN; ++x)
		for(int y = 0; y < TAILLE_TERRAIN; ++y)
			grille[x][y].reset(true);
	// calcul de mes tuyaux essentiels
	auto base = ma_base();
	for(auto pos = base.begin(); pos != base.end(); ++pos)
		calculerEssentiel(Position(pos->x, pos->y), id, Position(-1, -1));
	// calcul des distances (bfs) aux bases
	calculerDistBase(id);
	calculerDistBase(adv);
	// on reconstruit mes tuyaux detruits
	for(int x = 0; x < TAILLE_TERRAIN; ++x)
		for(int y = 0; y < TAILLE_TERRAIN; ++y)
			if(type_case(Position(x, y)) == DEBRIS && grille[x][y].distBase[MOI] < grille[x][y].distBase[ADV])
			{
				deblayer(Position(x, y).pos());
				construire(Position(x, y).pos());
			}
	idDejaVu = 0;
	for(int x = 0; x < TAILLE_TERRAIN; ++x)
		for(int y = 0; y < TAILLE_TERRAIN; ++y)
			grille[x][y].reset(true);
	base = ma_base();
	for(auto pos = base.begin(); pos != base.end(); ++pos)
		calculerEssentiel(Position(pos->x, pos->y), id, Position(-1, -1));

	//// Etape 2 : reduire le nombre de tuyaux inutiles ou detruire un tuyau essentiel aidant l'adversaire, puis on construit des tuyaux pour se rapprocher des pulsars
	for(int iAction = 0; iAction < 5 && points_action(); ++iAction)
	{
		// remplissage de grille
		idDejaVu = 0;
		for(int x = 0; x < TAILLE_TERRAIN; ++x)
			for(int y = 0; y < TAILLE_TERRAIN; ++y)
				grille[x][y].reset();
		calculerDistBase(id);
		calculerDistBase(adv);
		calculerFlots(id);
		calculerFlots(adv);
		base = base_ennemie();
		for(auto pos = base.begin(); pos != base.end(); ++pos)
			calculerEssentiel(Position(pos->x, pos->y), adv, Position(-1, -1));

		// On cherche le point faible (un tuyau essentiel qui transportera le plus de plasma) du reseau adverse
		double bestDestru = -oo;
		int xD = -1, yD = -1;
		for(int x = 0; x < TAILLE_TERRAIN; ++x)
			for(int y = 0; y < TAILLE_TERRAIN; ++y)
				if(grille[x][y].essentiel[ADV] && grille[x][y].flot[ADV] > 0 && (grille[x][y].flot[MOI] == 0 || !grille[x][y].essentiel[MOI]))
					if(bestDestru < grille[x][y].flot[ADV])
					{
						bestDestru = grille[x][y].flot[ADV];
						xD = x; yD = y;
					}
		if(!iAction)
		{
			// Si un de mes noeuds est plus faible que celui adverse, je le rend non essentiel
			reparerEssentiel(bestDestru / 2);
			// Sinon, je detruit son point faible
			detruire(Position(xD, yD).pos());
			//printf("Destruction : %d %d\n", xD, yD);
		}
		else
		{
			vector<Position> myNetwork;
			for(int x = 0; x < TAILLE_TERRAIN; ++x)
				for(int y = 0; y < TAILLE_TERRAIN; ++y)
					if(grille[x][y].distBase[MOI] != oo && grille[x][y].distBase[MOI] < grille[x][y].distBase[ADV] && (est_tuyau(Position(x,y).pos()) || type_case(Position(x,y)) == BASE))
						myNetwork.push_back(Position(x, y));
			
			// on cherche tous les meilleurs moyens de relier mes bases a des pulsars
			priority_queue<Chemin> coups = reliures(myNetwork);
			if(coups.size())  // on applique le "meilleur" selon l'operateur < de Chemin s'il y en a un
			{
				Chemin coup = coups.top();
				deblayer(coup.depart.pos());
				construire(coup.depart.pos());
				//printf("Pulsar %d %d : %d %d\n", coup.pos.x, coup.pos.y, coup.depart.x, coup.depart.y);
			}
			/*
			while(coups.size())
			{
				Chemin coup = coups.top();
				coups.pop();
				printf("%d %d / %d / %d %d\n", coup.depart.x, coup.depart.y, coup.longueur, coup.pos.x, coup.pos.y);
			}
			printf("\n");
			//*/
		}
	}
	// Avec les PA restants, on ameliore les tuyaux me servant (le choix intelligent n'est pas implemente)
	for(int x = 0; x < TAILLE_TERRAIN; ++x)
		for(int y = 0; y < TAILLE_TERRAIN; ++y)
			if(x + y % 2 && grille[x][y].flot[MOI] > 0)
				ameliorer(Position(x, y).pos());
	// finalement, on transfere les puissances d'aspiration pour optimiser ma zone. Ceci est a la fin car le premier transfert est gratuit
	base = ma_base();
	for(auto pos = base.begin(); pos != base.end(); ++pos)
		if(puissance_aspiration(*pos) < LIMITE_ASPIRATION)
		{
			if(baseUtile(Position(pos->x, pos->y)))
				for(int i = 2; i < 13; ++i)
					for(int iDir = 0; iDir < 4; ++iDir)
					{
						Position newPos = Position(pos->x, pos->y);
						for(int j = 0; j < i; ++j)
							newPos = newPos + dirs[iDir];
						if(type_case(newPos) == BASE && !baseUtile(newPos))
							deplacer_aspiration(newPos.pos(), *pos);
					}
		}
	//printf("%lf\n", double(clock() - debutTime) / CLOCKS_PER_SEC);
	//for(int i = 0; i < 100; ++i)
	//	printf("coucou\n");
}

void partie_fin()
{
}

// Dijkstra calculant les distances des tuyaux aux bases, prenant en compte les puissances d'aspiration

void calculerDistBase(int joueur)
{
	++idDejaVu;
	priority_queue<Chemin> file;
	vector<position> base = (joueur == id) ? ma_base() : base_ennemie();
	for(auto pos = base.begin(); pos != base.end(); ++pos)
	{
		//printf("%d\n", file.size());
		Chemin nouveau = Chemin(Position(pos->x, pos->y), -puissance_aspiration(*pos));
		file.push(nouveau);
	}
	while(file.size())
	{
		//printf(" %d\n", file.size());
		Chemin curPos = file.top();
		file.pop();
		if(curPos.pos.getGrille().dejaVu < idDejaVu)
		{
			grille[curPos.pos.x][curPos.pos.y].dejaVu = idDejaVu;
			grille[curPos.pos.x][curPos.pos.y].distBase[joueur == id] = curPos.longueur;
			if(type_case(curPos.pos) == BASE || est_tuyau(curPos.pos.pos()))
			{
				auto voisins = curPos.voisins();
				for(vector<Chemin>::iterator voisin = voisins.begin(); voisin != voisins.end(); ++voisin)
					file.push(*voisin);
			}
		}
	}
}

// On determine la quantite de plasma qui passera par chaque case lors du reste de la partie si le reseau n'evolue plus
// Cela se base sur les resultats de calculerDistBase et tourne sur un bfs partant des cases les plus eloignees des bases

void calculerFlots(int joueur)
{
	queue<Position> file;
	int maxDist = -oo;
	for(int x = 0; x < TAILLE_TERRAIN; ++x)
		for(int y = 0; y < TAILLE_TERRAIN; ++y)
			if(est_tuyau(Position(x, y).pos()) && grille[x][y].distBase[joueur == id] != oo)
			{
				maxDist = max(maxDist, grille[x][y].distBase[joueur == id]);
				grille[x][y].flot[joueur == id] = Position(x, y).newPlasma();
			}
	for(int x = 0; x < TAILLE_TERRAIN; ++x)
		for(int y = 0; y < TAILLE_TERRAIN; ++y)
			if(est_tuyau(Position(x, y).pos()) && grille[x][y].distBase[joueur == id] == maxDist)
				file.push(Position(x, y));
	++idDejaVu;
	while(file.size())
	{
		Position curPos = file.front();
		file.pop();
		if(curPos.getGrille().dejaVu < idDejaVu)
		{
			grille[curPos.x][curPos.y].dejaVu = idDejaVu;
			int nbVoisins = 0;
			auto voisins = curPos.voisins();
			for(auto voisin : voisins)
				nbVoisins += (curPos.getGrille().distBase[joueur == id] > voisin.getGrille().distBase[joueur == id]);
			for(auto voisin : voisins)
				if(curPos.getGrille().distBase[joueur == id] > voisin.getGrille().distBase[joueur == id])
				{
					grille[voisin.x][voisin.y].flot[joueur == id] += curPos.getGrille().flot[joueur == id] / nbVoisins;
					file.push(voisin);
				}
		}
	}
}

// Dijkstra calculant les meilleurs manieres de relier mes bases aux pulsars (symbolises par les cases adjacentes aux pulsars grace a la methode newPlasma

priority_queue<Chemin> reliures(vector<Position> departs)
{
	bool enablePipes = true;
	auto pulsars = liste_pulsars();
	for(auto pulsar = pulsars.begin(); pulsar != pulsars.end(); ++pulsar)
		enablePipes = enablePipes && !pulsarAccessible(Position(pulsar->x, pulsar->y));
	++idDejaVu;
	priority_queue<Chemin> file;
	priority_queue<Chemin> reponse;
	for(auto depart = departs.begin(); depart != departs.end(); ++depart)
		file.push(Chemin(*depart));
	while(file.size())
	{
		Chemin curPos = file.top();
		file.pop();
		if(curPos.pos.getGrille().dejaVu < idDejaVu)
		{
			grille[curPos.pos.x][curPos.pos.y].dejaVu = idDejaVu;
			if(curPos.longueur > 0 && !est_tuyau(curPos.pos.pos()))
			{
				curPos.score = curPos.pos.newPlasma();
				if(curPos.pos.newPlasma())
					reponse.push(curPos);
				//curPos.score = -curPos.pos.getGrille().distBase[MOI];
				//if(enablePipes && curPos.depart.x != -1 && est_tuyau(curPos.pos.pos()))
				//	reponse.push(curPos);
			}
			if(curPos.longueur == 0 || type_case(curPos.pos) == VIDE || type_case(curPos.pos) == DEBRIS || (curPos.depart.x != -1 && est_tuyau(curPos.pos.pos())))
			{
				auto voisins = curPos.voisins();
				for(auto voisin = voisins.begin(); voisin != voisins.end(); ++voisin)
						file.push(*voisin);
			}
		}
	}
	return reponse;
}

// Calcul des tuyaux essentiels grace au dfs Tarjan 

int calculerEssentiel(Position noeud, int joueur, Position pere, int prof)
{
	if(noeud.getGrille().prof[joueur == id] != -1)
		return noeud.getGrille().prof[joueur == id];
	grille[noeud.x][noeud.y].prof[joueur == id] = prof;
	grille[noeud.x][noeud.y].remontee[joueur == id] = prof;
	grille[noeud.x][noeud.y].essentiel[joueur == id] = false;
	auto voisins = noeud.voisins();
	for(auto voisin = voisins.begin(); voisin != voisins.end(); ++voisin)
		if(est_tuyau(voisin->pos()) || type_case(*voisin) == BASE)
		{
			if(voisin->x == pere.x && voisin->y == pere.y)
				++grille[noeud.x][noeud.y].nbVoisins[joueur == id];
			else
			{
				bool nouveau = voisin->getGrille().prof[joueur == id] == -1;
				int remontee = calculerEssentiel(*voisin, joueur, noeud, prof + 1);
				grille[noeud.x][noeud.y].remontee[joueur == id] = min(noeud.getGrille().remontee[joueur == id], remontee);
				grille[noeud.x][noeud.y].essentiel[joueur == id] = noeud.getGrille().essentiel[joueur == id] || remontee >= prof;
				if(nouveau && remontee >= noeud.getGrille().prof[joueur == id])
					++grille[noeud.x][noeud.y].nbVoisins[joueur == id];
			}
		}
	grille[noeud.x][noeud.y].essentiel[joueur == id] = noeud.getGrille().essentiel[joueur == id]
		&& type_case(noeud) != BASE
		&& grille[noeud.x][noeud.y].nbVoisins[joueur == id] > 1;
	//if(joueur == id)
	//	printf("%d %d -> %d %d %d %d\n", noeud.x, noeud.y, grille[noeud.x][noeud.y].prof[joueur == id], grille[noeud.x][noeud.y].remontee[joueur == id], grille[noeud.x][noeud.y].nbVoisins[joueur == id], grille[noeud.x][noeud.y].essentiel[joueur == id]);
	return noeud.getGrille().remontee[joueur == id];
}

// On determine la plus grande composante reliee au bases sans "utiliser" de voisins de tuyaux essentiel, puis on rend le tuyau essentiel de cette composant qui fera passer le plus de plasma dans le futur non essentiel grace a un bfs

void reparerEssentiel(double bestDestru)
{
	++idDejaVu;
	priority_queue<Cible> essentiels;
	queue<Position> file;
	auto base = ma_base();
	for(auto pos = base.begin(); pos != base.end(); ++pos)
		if(pos->x < TAILLE_TERRAIN - 1 && pos->y < TAILLE_TERRAIN - 1)
			file.push(Position(pos->x, pos->y));
	while(file.size())
	{
		Position curPos = file.front();
		file.pop();
		if(curPos.getGrille().dejaVu < idDejaVu)
		{
			grille[curPos.x][curPos.y].dejaVu = idDejaVu;
			if(curPos.getGrille().essentiel[MOI])
			{
				if(curPos.getGrille().flot[MOI] > 0)
					essentiels.push(Cible(curPos, curPos.getGrille().flot[MOI]));
			}
			else
			{
				auto voisins = curPos.voisins();
				for(auto voisin = voisins.begin(); voisin != voisins.end(); ++voisin)
					if(est_tuyau(voisin->pos()))
						file.push(*voisin);
			}
		}
	}
	for(auto pos = base.begin(); pos != base.end(); ++pos)
		if(pos->x > 0 && pos->y > 0)
			file.push(Position(pos->x, pos->y));
	while(file.size())
	{
		Position curPos = file.front();
		file.pop();
		if(curPos.getGrille().dejaVu < idDejaVu)
		{
			grille[curPos.x][curPos.y].dejaVu = idDejaVu;
			if(curPos.getGrille().essentiel[MOI])
			{
				//printf("-> %d %d %lf\n", curPos.x, curPos.y, curPos.getGrille().flot[MOI]);
				if(curPos.getGrille().flot[MOI] > 0)
					essentiels.push(Cible(curPos, curPos.getGrille().flot[MOI]));
			}
			else
			{
				auto voisins = curPos.voisins();
				for(auto voisin = voisins.begin(); voisin != voisins.end(); ++voisin)
					if(est_tuyau(voisin->pos()))
						file.push(*voisin);
			}
		}
	}	
	if(essentiels.size() && essentiels.top().gain >= bestDestru)
	{
		Position essentielle = essentiels.top().pos;
		//printf("%d %d\n", essentielle.x, essentielle.y);
		queue<Chemin> file2;
		/*for(int x = 0; x < TAILLE_TERRAIN; ++x)
			for(int y = 0; y < TAILLE_TERRAIN; ++y)
				if(grille[x][y].dejaVu == idDejaVu && (x != essentiels.front().x || y != essentiels.front().y))
					file2.push(Chemin(Position(x, y)));
		*/
		int goal = idDejaVu;
		auto departs = essentielle.voisins();
		for(auto depart : departs)
			if(!depart.getGrille().essentiel[MOI] && depart.getGrille().dejaVu == goal)
				file2.push(Chemin(depart));
		for(int iAction = 0; iAction < 3; ++iAction)
		{
			++idDejaVu;
			while(file2.size())
			{
				Chemin curPos = file2.front();
				file2.pop();
				if(est_tuyau(curPos.depart.pos()) || type_case(curPos.depart) == BASE)
					curPos.depart = curPos.pos;
				if(curPos.pos.getGrille().dejaVu < goal && est_tuyau(curPos.pos.pos()))
				{
					if(est_tuyau(curPos.depart.pos()))
						return;
					deblayer(curPos.depart.pos());
					construire(curPos.depart.pos());
					//printf("Essentiel: %d %d\n", curPos.depart.x, curPos.depart.y);
					while(file2.size())
						file2.pop();
					file2.push(Chemin(curPos.depart));
					break;
				}
				if(curPos.pos.getGrille().dejaVu < idDejaVu)
				{
					grille[curPos.pos.x][curPos.pos.y].dejaVu = idDejaVu;
					auto voisins = curPos.voisins();
					for(auto voisin = voisins.begin(); voisin != voisins.end(); ++voisin)
						if((!voisin->pos.getGrille().essentiel[MOI] || voisin->pos.getGrille().dejaVu < goal) && !est_pulsar(voisin->pos.pos()))
							file2.push(*voisin);
				}
			}
		}
	}
}

// fonctions utiles:
// surcharge de type_case pour la struct Position

case_type type_case(Position pos)
{
	return type_case(pos.pos());
}

// deterermine le plasma qu'un pulsar peut encore emettre

int plasmaRestant(Position pulsar)
{
	pulsar_info info = info_pulsar(pulsar.pos());
	return info.pulsations_restantes * info.puissance;
}

// determine si le pulsar est entierement entoure de tuyaux ou pas

bool pulsarAccessible(Position pulsar)
{
	auto voisins = pulsar.voisins();
	for(auto voisin = voisins.begin(); voisin != voisins.end(); ++voisin)
		if(est_libre(voisin->pos()))
			return true;
	return false;
}

// determine si la case de la base est reliee a un tuyaux, pour pouvoir augmenter sa puissance d'aspiration

bool baseUtile(Position base)
{
	auto voisins = base.voisins();
	for(auto voisin = voisins.begin(); voisin != voisins.end(); ++voisin)
		if(est_tuyau(voisin->pos()))
			return true;
	return false;
}

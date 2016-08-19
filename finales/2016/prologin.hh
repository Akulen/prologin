/// This file has been generated, if you wish to
/// modify it in a permanent way, please refer
/// to the script file : gen/generator_cxx.rb

#ifndef PROLOGIN_HH_
# define PROLOGIN_HH_

# include <functional>

# include <string>

# include <queue>

# include <vector>

/// Taille du terrain (longueur et largeur).
# define TAILLE_TERRAIN            39

/// Longueur de chacune de vos deux bases.
# define LONGUEUR_BASE             13

/// Nombre de tours à jouer avant la fin de la partie.
# define NB_TOURS                  100

/// Nombre de points d'action par tour.
# define NB_POINTS_ACTION          4

/// Nombre de points d'action que coûte la construction d'un tuyau.
# define COUT_CONSTRUCTION         1

/// Nombre de points d'action que coûte l'amélioration d'un tuyau.
# define COUT_AMELIORATION         1

/// Nombre de points d'action que coûte la destruction d'un tuyau.
# define COUT_DESTRUCTION          3

/// Nombre de points d'action que coûte la destruction d'un Super Tuyau™.
# define COUT_DESTRUCTION_SUPER_TUYAU 4

/// Charge en plasma nécessaire pour la destruction d'un tuyau ou d'un Super Tuyau™.
# define CHARGE_DESTRUCTION        2.0

/// Nombre de points d'action que coûte le déblayage d'une case de débris.
# define COUT_DEBLAYAGE            2

/// Nombre de points d'action que coûte le déplacement d'une unité de puissance d'aspiration de la base (la première modification de chaque tour est offerte).
# define COUT_MODIFICATION_ASPIRATION 1

/// Limite de puissance d'aspiration sur une case de base.
# define LIMITE_ASPIRATION         5

/// Vitesse du plasma dans un tuyau normal, en nombre de cases par tour.
# define VITESSE_TUYAU             1

/// Multiplicateur de la vitesse du plasma dans un Super Tuyau™.
# define MULTIPLICATEUR_VITESSE_SUPER_TUYAU 2

/// Erreurs possibles
typedef enum erreur {
  OK, /* <- L'action a été exécutée avec succès. */
  PA_INSUFFISANTS, /* <- Vous ne possédez pas assez de points d'action pour cette action. */
  AUCUN_TUYAU, /* <- Il n'y a pas de tuyau à la position spécifiée. */
  POSITION_INVALIDE, /* <- La position spécifiée est hors de la carte. */
  PUISSANCE_INSUFFISANTE, /* <- Vous ne possédez pas assez de puissance d'asipration sur cette partie de la base. */
  DEPLACEMENT_INVALIDE, /* <- Vous ne pouvez pas déplacer de la puissance d'aspiration d'une case à elle-même. */
  PAS_DANS_BASE, /* <- Cette case n'appartient pas à votre base. */
  AMELIORATION_IMPOSSIBLE, /* <- Il y a déjà un Super Tuyau™ sur cette case. */
  CONSTRUCTION_IMPOSSIBLE, /* <- Il est impossible de construire un tuyau à la position indiquée. */
  DESTRUCTION_IMPOSSIBLE, /* <- Il n'y a pas de tuyau à la position spécifiée. */
  PAS_DE_PULSAR, /* <- Il n'y a pas de pulsar à la position spécifiée. */
  PAS_DE_DEBRIS, /* <- Il n'y a pas de débris à la position spécifiée. */
  CHARGE_INSUFFISANTE, /* <- Vous ne possédez pas assez de plasma pour lancer une destruction. */
  LIMITE_ASPIRATION_ATTEINTE, /* <- Vous avez atteint la limite d'aspiration sur cette case. */
} erreur;


/// Types de cases
typedef enum case_type {
  VIDE, /* <- Case vide */
  TUYAU, /* <- Case contenant un tuyau */
  SUPER_TUYAU, /* <- Case contenant un Super Tuyau™ */
  DEBRIS, /* <- Case contenant des débris à déblayer */
  PULSAR, /* <- Case contenant un pulsar */
  BASE, /* <- Case appartenant à une base d'un des joueurs */
  INTERDIT, /* <- Case où aucune action n'est possible */
} case_type;


/// Position sur la carte, donnée par deux coordonnées.
typedef struct position {
  int x;  /* <- Coordonnée en X */
  int y;  /* <- Coordonnée en Y */
} position;


/// Représente un pulsar existant.
typedef struct pulsar_info {
  int periode;  /* <- Période de pulsation du pulsar */
  double puissance;  /* <- Quantité de plasma émise par chaque pulsation dans chaque direction */
  int pulsations_restantes;  /* <- Nombre de pulsations restantes */
  int pulsations_totales;  /* <- Nombre total de pulsations au début de la partie */
} pulsar_info;


/// Construit un tuyau sur une case donnée.
extern "C" erreur api_construire(position pos);
static inline erreur construire(position pos)
{
  return api_construire(pos);
}


/// Améliore un tuyau en Super Tuyau™.
extern "C" erreur api_ameliorer(position pos);
static inline erreur ameliorer(position pos)
{
  return api_ameliorer(pos);
}


/// Détruit un tuyau sur une case donnée.
extern "C" erreur api_detruire(position pos);
static inline erreur detruire(position pos)
{
  return api_detruire(pos);
}


/// Déplace une unité de puissance d'aspiration d'une case de votre base vers une autre.
extern "C" erreur api_deplacer_aspiration(position source, position destination);
static inline erreur deplacer_aspiration(position source, position destination)
{
  return api_deplacer_aspiration(source, destination);
}


/// Déblaye une case de débris.
extern "C" erreur api_deblayer(position pos);
static inline erreur deblayer(position pos)
{
  return api_deblayer(pos);
}


/// Renvoie le type d'une case donnée.
extern "C" case_type api_type_case(position pos);
static inline case_type type_case(position pos)
{
  return api_type_case(pos);
}


/// Renvoie la liste de tous les pulsars présents.
extern "C" std::vector<position> api_liste_pulsars();
static inline std::vector<position> liste_pulsars()
{
  return api_liste_pulsars();
}


/// Renvoie la liste des cases contenant du plasma.
extern "C" std::vector<position> api_liste_plasmas();
static inline std::vector<position> liste_plasmas()
{
  return api_liste_plasmas();
}


/// Renvoie la liste des cases contenant un tuyau ou Super Tuyau™.
extern "C" std::vector<position> api_liste_tuyaux();
static inline std::vector<position> liste_tuyaux()
{
  return api_liste_tuyaux();
}


/// Renvoie la liste des cases contenant un Super Tuyau™.
extern "C" std::vector<position> api_liste_super_tuyaux();
static inline std::vector<position> liste_super_tuyaux()
{
  return api_liste_super_tuyaux();
}


/// Renvoie la liste des cases contenant des débris.
extern "C" std::vector<position> api_liste_debris();
static inline std::vector<position> liste_debris()
{
  return api_liste_debris();
}


/// Renvoie vrai si et seulement si la case contient un pulsar.
extern "C" bool api_est_pulsar(position pos);
static inline bool est_pulsar(position pos)
{
  return api_est_pulsar(pos);
}


/// Renvoie vrai si et seulement si la case contient un tuyau ou un Super Tuyau™.
extern "C" bool api_est_tuyau(position pos);
static inline bool est_tuyau(position pos)
{
  return api_est_tuyau(pos);
}


/// Renvoie vrai si et seulement si la case contient un simple tuyau.
extern "C" bool api_est_simple_tuyau(position pos);
static inline bool est_simple_tuyau(position pos)
{
  return api_est_simple_tuyau(pos);
}


/// Renvoie vrai si et seulement si la case contient un Super Tuyau™.
extern "C" bool api_est_super_tuyau(position pos);
static inline bool est_super_tuyau(position pos)
{
  return api_est_super_tuyau(pos);
}


/// Renvoie vrai si et seulement si la case contient un débris.
extern "C" bool api_est_debris(position pos);
static inline bool est_debris(position pos)
{
  return api_est_debris(pos);
}


/// Renvoie vrai si et seulement s'il est possible de construire sur cette case.
extern "C" bool api_est_libre(position pos);
static inline bool est_libre(position pos)
{
  return api_est_libre(pos);
}


/// Renvoie les informations propres au pulsar à la position donnée.
extern "C" pulsar_info api_info_pulsar(position pos);
static inline pulsar_info info_pulsar(position pos)
{
  return api_info_pulsar(pos);
}


/// Renvoie la quantité de plasma sur une case donnée.
extern "C" double api_charges_presentes(position pos);
static inline double charges_presentes(position pos)
{
  return api_charges_presentes(pos);
}


/// Renvoie le numéro du joueur ayant dernièrement construit ou amélioré un tuyau sur une case.
extern "C" int api_constructeur_tuyau(position pos);
static inline int constructeur_tuyau(position pos)
{
  return api_constructeur_tuyau(pos);
}


/// Renvoie le numéro du propriétaire d'une case de base.
extern "C" int api_proprietaire_base(position pos);
static inline int proprietaire_base(position pos)
{
  return api_proprietaire_base(pos);
}


/// Renvoie la liste des cases composant votre base.
extern "C" std::vector<position> api_ma_base();
static inline std::vector<position> ma_base()
{
  return api_ma_base();
}


/// Renvoie la liste des cases composant la base de votre ennemi.
extern "C" std::vector<position> api_base_ennemie();
static inline std::vector<position> base_ennemie()
{
  return api_base_ennemie();
}


/// Renvoie la puissance d'aspiration d'une case de base donnée. Renvoie -1 si la position n'est pas celle d'une base.
extern "C" int api_puissance_aspiration(position pos);
static inline int puissance_aspiration(position pos)
{
  return api_puissance_aspiration(pos);
}


/// Renvoie pour une case donnée la liste des cases vers lesquelles le plasma se propagera. Renvoie la liste vide si la case n'est pas une case contenant un tuyau ou si elle n'est reliée à aucune base.
extern "C" std::vector<position> api_directions_plasma(position pos);
static inline std::vector<position> directions_plasma(position pos)
{
  return api_directions_plasma(pos);
}


/// Renvoie la valeur du coût de la prochaine modification de vos puissances d'aspiration.
extern "C" int api_cout_prochaine_modification_aspiration();
static inline int cout_prochaine_modification_aspiration()
{
  return api_cout_prochaine_modification_aspiration();
}


/// Renvoie la liste des tuyaux construits par votre adversaire au dernier tour.
extern "C" std::vector<position> api_hist_tuyaux_construits();
static inline std::vector<position> hist_tuyaux_construits()
{
  return api_hist_tuyaux_construits();
}


/// Renvoie la liste des tuyaux détruits par votre adversaire au dernier tour.
extern "C" std::vector<position> api_hist_tuyaux_detruits();
static inline std::vector<position> hist_tuyaux_detruits()
{
  return api_hist_tuyaux_detruits();
}


/// Renvoie la liste des tuyaux améliorés par votre adversaire au dernier tour.
extern "C" std::vector<position> api_hist_tuyaux_ameliores();
static inline std::vector<position> hist_tuyaux_ameliores()
{
  return api_hist_tuyaux_ameliores();
}


/// Renvoie la liste des débris déblayés par votre adversaire au dernier tour.
extern "C" std::vector<position> api_hist_debris_deblayes();
static inline std::vector<position> hist_debris_deblayes()
{
  return api_hist_debris_deblayes();
}


/// Renvoie la liste des cases de base de votre adversaire qui ont reçu un point d'aspiration (une même case peut apparaître plusieurs fois).
extern "C" std::vector<position> api_hist_points_aspiration_ajoutes();
static inline std::vector<position> hist_points_aspiration_ajoutes()
{
  return api_hist_points_aspiration_ajoutes();
}


/// Renvoie la liste des cases de base de votre adversaire qui ont perdu un point d'aspiration (une même case peut apparaître plusieurs fois).
extern "C" std::vector<position> api_hist_points_aspiration_retires();
static inline std::vector<position> hist_points_aspiration_retires()
{
  return api_hist_points_aspiration_retires();
}


/// Renvoie votre numéro de joueur.
extern "C" int api_moi();
static inline int moi()
{
  return api_moi();
}


/// Renvoie le numéro de votre adversaire.
extern "C" int api_adversaire();
static inline int adversaire()
{
  return api_adversaire();
}


/// Indique votre nombre de points d'actions restants pour ce tour-ci.
extern "C" int api_points_action();
static inline int points_action()
{
  return api_points_action();
}


/// Renvoie le score du joueur désigné par le numéro ``id_joueur``. Renvoie -1 si ``id_joueur`` est invalide.
extern "C" int api_score(int id_joueur);
static inline int score(int id_joueur)
{
  return api_score(id_joueur);
}


/// Renvoie le numéro du tour actuel.
extern "C" int api_tour_actuel();
static inline int tour_actuel()
{
  return api_tour_actuel();
}


/// Annule la dernière action. Renvoie ``false`` quand il n'y a pas d'action à annuler ce tour-ci.
extern "C" bool api_annuler();
static inline bool annuler()
{
  return api_annuler();
}


/// Affiche le contenu d'une valeur de type erreur
extern "C" void api_afficher_erreur(erreur v);
static inline void afficher_erreur(erreur v)
{
  api_afficher_erreur(v);
}


/// Affiche le contenu d'une valeur de type case_type
extern "C" void api_afficher_case_type(case_type v);
static inline void afficher_case_type(case_type v)
{
  api_afficher_case_type(v);
}


/// Affiche le contenu d'une valeur de type position
extern "C" void api_afficher_position(position v);
static inline void afficher_position(position v)
{
  api_afficher_position(v);
}


/// Affiche le contenu d'une valeur de type pulsar_info
extern "C" void api_afficher_pulsar_info(pulsar_info v);
static inline void afficher_pulsar_info(pulsar_info v)
{
  api_afficher_pulsar_info(v);
}


// Les fonctions suivantes définissent les opérations de comparaison, d'égalité
// et de hachage sur les structures du sujet.

namespace std {
  template <typename T>
  struct hash<std::vector<T>>
  {
    std::size_t operator()(const std::vector<T>& v)
    {
      std::size_t res = v.size();
      for (const auto& e : v)
        res ^= std::hash<T>()(e) + 0x9e3779b9 + (res << 6) + (res >> 2);
      return res;
    }
  };
}

inline bool operator==(const position& a, const position& b) {
  if (a.x != b.x) return false;
  if (a.y != b.y) return false;
  return true;
}

inline bool operator<(const position& a, const position& b) {
  if (a.x < b.x) return true;
  if (a.x > b.x) return false;
  if (a.y < b.y) return true;
  if (a.y > b.y) return false;
  return false;
}

namespace std {
  template <>
  struct hash<position>
  {
    std::size_t operator()(const position& s)
    {
      std::size_t res = 0;
      res ^= 0x9e3779b9 + (res << 6) + (res >> 2) + std::hash<int>()(s.x);
      res ^= 0x9e3779b9 + (res << 6) + (res >> 2) + std::hash<int>()(s.y);
      return res;
    }
  };
}

inline bool operator==(const pulsar_info& a, const pulsar_info& b) {
  if (a.periode != b.periode) return false;
  if (a.puissance != b.puissance) return false;
  if (a.pulsations_restantes != b.pulsations_restantes) return false;
  if (a.pulsations_totales != b.pulsations_totales) return false;
  return true;
}

inline bool operator<(const pulsar_info& a, const pulsar_info& b) {
  if (a.periode < b.periode) return true;
  if (a.periode > b.periode) return false;
  if (a.puissance < b.puissance) return true;
  if (a.puissance > b.puissance) return false;
  if (a.pulsations_restantes < b.pulsations_restantes) return true;
  if (a.pulsations_restantes > b.pulsations_restantes) return false;
  if (a.pulsations_totales < b.pulsations_totales) return true;
  if (a.pulsations_totales > b.pulsations_totales) return false;
  return false;
}

namespace std {
  template <>
  struct hash<pulsar_info>
  {
    std::size_t operator()(const pulsar_info& s)
    {
      std::size_t res = 0;
      res ^= 0x9e3779b9 + (res << 6) + (res >> 2) + std::hash<int>()(s.periode);
      res ^= 0x9e3779b9 + (res << 6) + (res >> 2) + std::hash<double>()(s.puissance);
      res ^= 0x9e3779b9 + (res << 6) + (res >> 2) + std::hash<int>()(s.pulsations_restantes);
      res ^= 0x9e3779b9 + (res << 6) + (res >> 2) + std::hash<int>()(s.pulsations_totales);
      return res;
    }
  };
}


extern "C" {

void partie_init();

void jouer_tour();

void partie_fin();

struct Case;
struct Position;
struct Cible;
struct Chemin;

case_type type_case(Position pos);
int plasmaRestant(Position pulsar);
bool pulsarAccessible(Position pulsar);
bool baseUtile(Position base);

void calculerDistBase(int joueur);
void calculerFlots(int joueur);
std::priority_queue<Chemin> reliures(std::vector<Position> departs);
int calculerEssentiel(Position noeud, int joueur, Position pere, int prof = 0);
void reparerEssentiel(double bestDestru);

}
#endif

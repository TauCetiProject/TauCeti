/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.Sporadic.HigmanSims.Basic
public import TauCeti.GroupTheory.GroupAction.Stabilizer.Chain
public import Mathlib.GroupTheory.GroupAction.Transitive

/-!
# Basic orbits of the Higman--Sims model

The ATLAS permutation model `TauCeti.Sporadic.HS` is transitive on its 100 points. The
stabilizer of `0` has an orbit of length 77 containing `1`. Consequently the order of `HS` is
7700 times the order of its pointwise stabilizer of `{0, 1}`. These are the first two factors
in an order calculation along the points `0, 1, 2, 3, 4`.

Explicit words in the ATLAS generators witness both lower bounds. For the second upper bound,
a binary relation is checked to be invariant under both generators, hence under their closure.
Its row at `0` contains exactly the 77 points reached by the second set of words. The relation
and words are finite proof data; neither the group order nor the orbit computation is assumed.
All finite checks are performed in the Lean kernel.

The pointwise stabilizer of `0, 1, 2` has a 32-point orbit containing `3`, giving the fourth
factor in the order calculation. Its upper bound uses the invariant pair of common neighbors
of the three fixed points: the orbit consists of the points related to all three fixed points
and to exactly one member of that pair. Explicit words fixing the three points reach every
point in this set.

## References

* R. A. Wilson, R. A. Parker, J. N. Bray et al., *ATLAS of Finite Group Representations*,
  version 3, representation `HSG1-p100B0`,
  <https://brauer.maths.qmul.ac.uk/Atlas/v3/permrep/HSG1-p100B0>.
* Á. Seress, *Permutation Group Algorithms*, Cambridge Tracts in Mathematics 152,
  Cambridge University Press, 2003, §4.1.
-/

public section

namespace TauCeti.Sporadic.HS

open MulAction

/-! ### Reachability in the ATLAS generators -/

-- A word is read in Mathlib's product convention: its last letter acts first.
private def wordValue (w : List ℕ) : Equiv.Perm (Fin 100) :=
  (w.map fun i => if i = 0 then a else b).prod

private theorem wordValue_mem (w : List ℕ) : wordValue w ∈ HS := by
  apply HS.list_prod_mem
  simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  intro i _
  split <;> simp

-- Breadth-first paths from 0. Letter 0 denotes a and letter 1 denotes b.
private def orbitWords : Fin 100 → List ℕ :=
  ![[],
    [0, 1, 1, 0],
    [1, 1, 0, 1, 1, 0, 1, 1],
    [0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1],
    [1, 1, 0, 1, 0, 1, 1, 0, 1, 0],
    [0, 1, 1, 1, 0, 1, 0],
    [1, 0, 1, 1],
    [1, 1, 1, 0, 1, 1, 0],
    [1, 1, 1, 1, 0, 1, 1, 1, 1],
    [1, 1, 1],
    [1, 1, 1, 1, 0, 1, 0, 1, 0, 1],
    [1, 0, 1, 1, 1, 1, 0],
    [1, 1],
    [1, 1, 0, 1, 1, 1, 1, 0],
    [1, 0, 1, 0, 1],
    [1, 1, 1, 0, 1, 1],
    [1, 0, 1, 1, 0, 1, 1],
    [0, 1, 1, 0, 1, 0, 1, 1, 0],
    [1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1],
    [1, 1, 1, 1, 0, 1, 1],
    [1, 1, 0, 1, 1, 0, 1, 1, 0],
    [1, 1, 1, 0, 1, 1, 0, 1, 1, 0],
    [0, 1, 1, 1, 1],
    [1, 0, 1, 1, 0, 1, 0],
    [0, 1, 1, 0, 1, 1],
    [0, 1, 1, 1, 1, 0, 1, 0],
    [1, 0, 1, 1, 1, 0, 1, 0],
    [0, 1, 1],
    [0, 1, 0, 1, 1, 1, 1],
    [1, 1, 0, 1, 1, 0],
    [1, 1, 1, 0, 1, 0, 1],
    [1, 1, 1, 0, 1, 0, 1, 0, 1],
    [0, 1, 1, 1, 0, 1, 1, 1, 1],
    [1, 0, 1, 0],
    [0, 1, 1, 1, 1, 0, 1, 0, 1],
    [1, 1, 1, 0],
    [0, 1, 0, 1],
    [1, 1, 1, 1, 0, 1, 1, 0],
    [0, 1, 1, 0, 1, 1, 0],
    [1, 1, 1, 0, 1, 1, 0, 1, 1],
    [1, 1, 0, 1],
    [0, 1, 0, 1, 0, 1],
    [1, 1, 1, 0, 1, 0, 1, 1, 1, 1],
    [0, 1, 0, 1, 1, 0, 1, 0, 1],
    [0, 1, 1, 0, 1, 0, 1, 1, 1, 1],
    [1, 0, 1, 0, 1, 0, 1],
    [1, 1, 1, 1],
    [1, 1, 1, 1, 0, 1, 1, 0, 1, 1],
    [0, 1],
    [0, 1, 0],
    [1, 1, 0, 1, 1, 1, 0, 1, 0],
    [1, 0, 1, 1, 1, 0, 1, 1, 1, 1],
    [1, 0, 1, 1, 0],
    [0, 1, 0, 1, 1, 0, 1, 0],
    [1, 1, 1, 1, 0, 1, 1, 1, 1, 0],
    [1, 1, 1, 1, 0, 1, 0, 1],
    [1, 1, 0, 1, 0, 1, 1, 0],
    [1, 0, 1, 1, 1, 1, 0, 1, 0],
    [0, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1],
    [0],
    [1, 1, 1, 0, 1, 1, 1, 1],
    [1, 1, 0, 1, 0],
    [1, 1, 1, 0, 1, 0, 1, 1, 0],
    [1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 0],
    [1, 0, 1, 0, 1, 1, 0, 1, 0],
    [0, 1, 1, 0, 1, 1, 1, 0, 1, 0],
    [1, 0, 1],
    [0, 1, 1, 1, 1, 0],
    [1, 0, 1, 1, 0, 1, 0, 1, 1, 0],
    [1, 1, 1, 1, 0, 1],
    [0, 1, 1, 0, 1, 1, 1, 1, 0],
    [1, 1, 0],
    [0, 1, 1, 0, 1, 0],
    [1, 0],
    [1, 0, 1, 0, 1, 1, 0, 1, 1, 0],
    [1, 0, 1, 1, 0, 1, 0, 1],
    [0, 1, 0, 1, 0, 1, 1, 1, 1],
    [1, 1, 1, 1, 0, 1, 0],
    [0, 1, 0, 1, 0, 1, 1, 0, 1, 0],
    [1, 1, 1, 0, 1],
    [1, 1, 1, 0, 1, 1, 1, 1, 0],
    [1, 1, 1, 1, 0],
    [1, 1, 0, 1, 1],
    [0, 1, 1, 0, 1, 0, 1],
    [1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0],
    [1],
    [1, 1, 1, 0, 1, 0],
    [1, 1, 0, 1, 0, 1, 1, 1, 1],
    [1, 0, 1, 1, 1, 1],
    [1, 1, 0, 1, 0, 1],
    [1, 1, 0, 1, 0, 1, 0, 1],
    [1, 0, 1, 0, 1, 1, 1, 1],
    [1, 0, 1, 1, 1, 1, 0, 1, 0, 1],
    [0, 1, 0, 1, 1, 0, 1, 1, 0],
    [1, 1, 0, 1, 1, 1, 1],
    [1, 1, 0, 1, 1, 1, 1, 0, 1, 0],
    [1, 0, 1, 0, 1, 1, 0],
    [1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0],
    [0, 1, 0, 1, 1, 0],
    [1, 0, 1, 1, 0, 1, 1, 0]]

private theorem orbitWords_apply : ∀ x, wordValue (orbitWords x) 0 = x := by
  decide +kernel

/-- The exact ATLAS Higman--Sims model is transitive on its 100 points. -/
instance : IsPretransitive HS (Fin 100) :=
  (isPretransitive_iff_base (0 : Fin 100)).mpr fun x =>
    ⟨⟨wordValue (orbitWords x), wordValue_mem _⟩, orbitWords_apply x⟩

/-- The point sequence `0, 1, 2, …` (modulo 100) used for the Higman--Sims stabilizer chain.
The first five points are the prescribed points for the order calculation. -/
def pointSequence (i : ℕ) : Fin 100 := Fin.ofNat 100 i

/-- Evaluation of the point sequence modulo 100. -/
@[simp]
theorem pointSequence_apply (i : ℕ) : pointSequence i = Fin.ofNat 100 i := (rfl)

/-- The first basic orbit of the Higman--Sims model has length 100. -/
@[simp]
theorem ncard_orbit_stabilizerChain_zero :
    (orbit (HS.stabilizerChain pointSequence 0) (0 : Fin 100)).ncard = 100 := by
  rw [Subgroup.stabilizerChain_zero]
  simp [orbit_eq_univ]

/-! ### An invariant relation bounds the second orbit -/

-- Row x is a bit mask: bit y records the relation on (x, y). The data were generated by
-- breadth-first search from (0, 1), applying a or b simultaneously to both coordinates.
-- Only the invariance and row checks below are used in the proof.
private def relationRows : Fin 100 → ℕ :=
  ![1265174716386516497202218524910,
    1267635771404108665038146762749,
    1148186628575017032573865950379,
    1012160975295063997165265484279,
    1099198267014438172431057928170,
    945778931699707542083086530655,
    947865527647925406995329799099,
    1264468603283772337952434941791,
    623757129175961082622981299930,
    1246488334275437750001606655442,
    633184663569792769665575943062,
    1171667707773122411180698089404,
    1178050415513787755605433175934,
    1262036329674851068227052359359,
    630885125669702468652222035919,
    1099134803370428807114460594079,
    950108855368530058161623051775,
    1185017453963068401546725784829,
    315670629301680490728300076903,
    1266404782797404416638648254135,
    592354307468366527521524543365,
    791947054889778686394771698815,
    1267221069996858141949629038335,
    475363760116058763505552059839,
    1247727423621044460048774015993,
    1228017166632543639075020396487,
    1143227950148087533312347947006,
    633819853304206105130114643827,
    1247688760388920852947050168254,
    1252735928828835854814749769595,
    1267649384990163414752908255219,
    1216805595745405638962090712063,
    1010003649526545095149884211100,
    1187453708568774811141256249295,
    1267176075429364883539495745499,
    1142268065259339582518358604397,
    1174175699520073387710198317023,
    623763823567443670945574681917,
    153039123698011396631051108216,
    419637494800667002518583967550,
    1168576219723557642367249383294,
    1257623683887434523695765060607,
    308846460870262127227554983405,
    941123344201340841871158542063,
    988794632421790082509509222366,
    625149875622847704959058669563,
    1267611753491579382507147096017,
    1262326386687588859381874851834,
    1257103250137053751468799802815,
    929672871051328779465925795696,
    1217069096683856922964294631388,
    1256156131559975893342976211835,
    594131377511701703915059699700,
    1255251658258549334124702719487,
    593882047479237534827693954415,
    950037372927050021251097542389,
    1188409212424488908339989650943,
    461343542794396295657076744153,
    1022537258431716200284997746431,
    950271219758681288905471285741,
    1245270301961300820727184389887,
    768683393122922733129623923453,
    620748305245896483993619529727,
    1164901499592637596009651657711,
    628715073845325140338126159791,
    435667546530097884476296521695,
    314650956968303530853351260158,
    772376283585793566801844871166,
    930776166151733400810695291759,
    1064609087638061955847657598141,
    945619177606406020506409893886,
    950114127272945025783500374006,
    1246547036238034248372341043087,
    1008919003410301455395777920575,
    980448486228210316045907892605,
    786077304493788250281806244859,
    1228036400662111053606859830903,
    1069188344958246123243919045375,
    1250164380516424545122740009977,
    1223045459204892326381588179951,
    1228020793319608510657133765119,
    1086889592554296423834365192155,
    1165978538543187263998066679757,
    1247774611757669224659818577445,
    1188236257676181982094987099135,
    155776736226982774603710977535,
    1183238412417219438923369938223,
    1225884327285965557954823270135,
    1247533923399585408406716788663,
    1088613519606961926047909335931,
    1266257865652538853614959195647,
    1225514397462190988804384210742,
    1242813481927147290300921141207,
    921027068102633618850996774631,
    558603503143549237257098493439,
    888684146122992873095176388603,
    237582909430162807897311799283,
    1108533983695831468686178222055,
    821953458619130366248655454111,
    534751411211151042357588900607]

private def related (x y : Fin 100) : Bool := (relationRows x).testBit y.val

private theorem related_a : ∀ x y, related (a x) (a y) = related x y := by
  decide +kernel

private theorem related_b : ∀ x y, related (b x) (b y) = related x y := by
  decide +kernel

private theorem related_apply {g : Equiv.Perm (Fin 100)} (hg : g ∈ HS) :
    ∀ x y, related (g x) (g y) = related x y := by
  rw [HS_def] at hg
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    rcases hg with rfl | rfl
    · exact related_a
    · exact related_b
  | one => simp
  | mul g h _ _ hg hh =>
    intro x y
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hg, hh]
  | inv g _ hg =>
    intro x y
    simpa using (hg (g⁻¹ x) (g⁻¹ y)).symm

private def suborbit : Finset (Fin 100) :=
  {1, 2, 3, 5, 6, 7, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 27, 29, 30, 31,
    33, 34, 35, 36, 37, 41, 42, 43, 45, 46, 48, 51, 53, 54, 55, 56, 57, 58, 59, 60, 61,
    62, 63, 64, 65, 68, 69, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86,
    87, 88, 89, 90, 92, 93, 94, 95, 96, 97, 98, 99}

private theorem suborbit_eq : (suborbit : Set (Fin 100)) =
    (↑({1, 2, 3, 5, 6, 7, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 27, 29, 30,
      31, 33, 34, 35, 36, 37, 41, 42, 43, 45, 46, 48, 51, 53, 54, 55, 56, 57, 58, 59, 60,
      61, 62, 63, 64, 65, 68, 69, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85,
      86, 87, 88, 89, 90, 92, 93, 94, 95, 96, 97, 98, 99} :
      Finset (Fin 100)) : Set (Fin 100)) := (rfl)

private theorem related_zero : ∀ x, related 0 x = true ↔ x ∈ suborbit := by
  decide +kernel

-- Paths from (0, 1) to (0, x). Entries outside suborbit are unused.
private def stabilizerWords : Fin 100 → List ℕ :=
  ![[],
    [],
    [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1],
    [1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1],
    [],
    [1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0],
    [0, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0],
    [1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1],
    [],
    [],
    [],
    [],
    [],
    [0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 1, 0],
    [1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1],
    [1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0],
    [1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1],
    [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 0],
    [1, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1],
    [1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1],
    [1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1],
    [1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1],
    [1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1],
    [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0],
    [1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 0],
    [1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0],
    [],
    [0, 1, 1, 0, 1, 1, 1, 0],
    [],
    [0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0],
    [0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0],
    [1, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1],
    [],
    [1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0],
    [1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1],
    [1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1],
    [0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1],
    [1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1],
    [],
    [],
    [],
    [0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 0],
    [1, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1],
    [1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1],
    [],
    [1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0],
    [1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0],
    [],
    [0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1],
    [],
    [],
    [1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 0],
    [],
    [1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0],
    [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0],
    [1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1],
    [1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1],
    [1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1],
    [0, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0],
    [0, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1],
    [1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1],
    [1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1],
    [1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 0],
    [0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1],
    [0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0],
    [1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1],
    [],
    [],
    [1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 0],
    [0, 1, 0, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0],
    [],
    [],
    [0, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1],
    [0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1],
    [1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1],
    [1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1],
    [1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0],
    [1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1],
    [1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 1],
    [0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0],
    [1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1],
    [1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1],
    [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 0],
    [1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1],
    [0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0],
    [1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1],
    [0, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0],
    [0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 1, 0],
    [0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0],
    [1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 0, 1],
    [1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0],
    [],
    [0, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0],
    [0, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1],
    [1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 0],
    [0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0],
    [1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0],
    [1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0],
    [0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1],
    [1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0]]

private theorem stabilizerWords_apply : ∀ x ∈ suborbit,
    wordValue (stabilizerWords x) 0 = 0 ∧ wordValue (stabilizerWords x) 1 = x := by
  decide +kernel

/-- The complete orbit of `1` under the stabilizer of `0` in the ATLAS model. -/
theorem orbit_stabilizerChain_one :
    orbit (HS.stabilizerChain pointSequence 1) (1 : Fin 100) =
      (↑({1, 2, 3, 5, 6, 7, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 27, 29, 30,
        31, 33, 34, 35, 36, 37, 41, 42, 43, 45, 46, 48, 51, 53, 54, 55, 56, 57, 58, 59, 60,
        61, 62, 63, 64, 65, 68, 69, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85,
        86, 87, 88, 89, 90, 92, 93, 94, 95, 96, 97, 98, 99} :
        Finset (Fin 100)) : Set (Fin 100)) := by
  rw [← suborbit_eq, Subgroup.stabilizerChain_succ, Subgroup.stabilizerChain_zero]
  ext x
  constructor
  · rintro ⟨g, rfl⟩
    have hg0 : (g : Equiv.Perm (Fin 100)) 0 = 0 := mem_stabilizer_iff.mp g.2.2
    have h := related_apply g.2.1 0 1
    rw [hg0] at h
    exact (related_zero _).mp (h.trans (by decide +kernel))
  · intro hx
    obtain ⟨h0, h1⟩ := stabilizerWords_apply x hx
    exact mem_orbit_iff.mpr
      ⟨⟨wordValue (stabilizerWords x), wordValue_mem _, mem_stabilizer_iff.mpr h0⟩, h1⟩

/-- The second basic orbit along `0, 1` has length 77, not 99. -/
@[simp]
theorem ncard_orbit_stabilizerChain_one :
    (orbit (HS.stabilizerChain pointSequence 1) (1 : Fin 100)).ncard = 77 := by
  rw [orbit_stabilizerChain_one, Set.ncard_coe_finset]
  decide +kernel

/-- The order of the ATLAS Higman--Sims model is 7700 times the order of its two-point
stabilizer. In particular, determining that remaining order to be 5760 gives order 44352000. -/
theorem card_eq_7700_mul_card_stabilizerChain :
    Nat.card HS = 7700 * Nat.card (HS.stabilizerChain pointSequence 2) := by
  have h0 : pointSequence 0 = 0 := rfl
  have h1 : pointSequence 1 = 1 := rfl
  simpa only [Finset.prod_range_succ, Finset.range_zero, Finset.prod_empty, one_mul,
    h0, h1, ncard_orbit_stabilizerChain_zero, ncard_orbit_stabilizerChain_one,
    Nat.reduceMul] using
    (HS.prod_ncard_orbit_mul_card_stabilizerChain pointSequence 2).symm

/-! ### The fourth basic orbit -/

-- The two points unrelated to all of 0, 1, 2 form an invariant pair under their stabilizer.
private def commonNeighbors : Finset (Fin 100) := {38, 49}

private theorem mem_commonNeighbors : ∀ x : Fin 100,
    x ∈ commonNeighbors ↔
      related 0 x = false ∧ related 1 x = false ∧ related 2 x = false := by
  decide +kernel

private theorem commonNeighbors_apply {g : Equiv.Perm (Fin 100)}
    (hg : g ∈ HS.stabilizerChain pointSequence 3) {x : Fin 100}
    (hx : x ∈ commonNeighbors) : g x ∈ commonNeighbors := by
  obtain ⟨hg, hfix⟩ := (Subgroup.mem_stabilizerChain_iff _ _).mp hg
  have h0 : g 0 = 0 := hfix 0 (by omega)
  have h1 : g 1 = 1 := hfix 1 (by omega)
  have h2 : g 2 = 2 := hfix 2 (by omega)
  have hr0 := related_apply hg 0 x
  have hr1 := related_apply hg 1 x
  have hr2 := related_apply hg 2 x
  rw [h0] at hr0
  rw [h1] at hr1
  rw [h2] at hr2
  rw [mem_commonNeighbors] at hx ⊢
  simpa only [hr0, hr1, hr2] using hx

private def fourthOrbit : Finset (Fin 100) :=
  {3, 13, 14, 15, 19, 22, 23, 25, 31, 33, 36, 48, 53, 56, 58, 60, 62, 63, 64, 65, 72, 77,
    79, 80, 84, 87, 88, 90, 92, 94, 97, 99}

-- Among the points related to 0, 1, 2, these are exactly those related to one member of the
-- invariant pair and unrelated to the other.
private theorem mem_fourthOrbit : ∀ x : Fin 100,
    x ∈ fourthOrbit ↔ related 0 x = true ∧ related 1 x = true ∧ related 2 x = true ∧
      related x 38 ≠ related x 49 := by
  decide +kernel

-- Words from (0, 1, 2, 3) to (0, 1, 2, x), with 0 denoting a and 1 denoting b.
-- They were found by collisions in a breadth-first search on ordered triples. Only the word
-- equations below, rather than correctness of the search, enter the proof.
private def fourthOrbitWords : Fin 100 → List ℕ :=
  ![[],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 0,
      1, 1, 1, 1],
    [0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1,
      0, 1, 1, 1, 1, 0, 1, 0],
    [0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1,
      1, 0, 1, 1, 1, 0],
    [],
    [],
    [],
    [1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1,
      0, 1, 0, 1, 1, 1, 1],
    [],
    [],
    [0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1],
    [0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 0,
      1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0],
    [],
    [1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1,
      1],
    [],
    [],
    [],
    [],
    [],
    [0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 0],
    [],
    [1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1,
      0, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1],
    [],
    [],
    [1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1,
      1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 1, 0],
    [],
    [],
    [],
    [],
    [1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1,
      1],
    [],
    [],
    [1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1,
      0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0],
    [],
    [1, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1,
      1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0],
    [],
    [1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1,
      1, 0, 1, 0, 1],
    [],
    [0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0,
      1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0],
    [1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1],
    [0, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 0,
      1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0],
    [0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1,
      1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1],
    [],
    [],
    [],
    [],
    [],
    [],
    [1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0,
      1, 0, 1, 0, 1, 1, 1, 0],
    [],
    [],
    [],
    [],
    [0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0,
      1, 0, 1, 1, 1, 0],
    [],
    [1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0,
      1, 1, 1, 0],
    [0, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1,
      1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0],
    [],
    [],
    [],
    [0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1,
      0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0],
    [],
    [],
    [1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1,
      1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1],
    [1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1,
      0, 1, 1, 1, 1, 0, 1, 1, 0],
    [],
    [1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1,
      0, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1],
    [],
    [0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1,
      0],
    [],
    [0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0,
      1, 1, 1, 1, 0],
    [],
    [],
    [0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1,
      0, 1, 0, 1, 1, 0, 1, 1],
    [],
    [1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1]]

private theorem fourthOrbitWords_apply : ∀ x ∈ fourthOrbit,
    wordValue (fourthOrbitWords x) 0 = 0 ∧ wordValue (fourthOrbitWords x) 1 = 1 ∧
      wordValue (fourthOrbitWords x) 2 = 2 ∧ wordValue (fourthOrbitWords x) 3 = x := by
  decide +kernel

/-- The complete orbit of `3` under the pointwise stabilizer of `0, 1, 2` in the ATLAS model. -/
theorem orbit_stabilizerChain_three :
    orbit (HS.stabilizerChain pointSequence 3) (3 : Fin 100) =
      (↑({3, 13, 14, 15, 19, 22, 23, 25, 31, 33, 36, 48, 53, 56, 58, 60, 62, 63, 64, 65, 72, 77,
        79, 80, 84, 87, 88, 90, 92, 94, 97, 99} : Finset (Fin 100)) : Set (Fin 100)) := by
  suffices orbit (HS.stabilizerChain pointSequence 3) (3 : Fin 100) =
      (↑fourthOrbit : Set (Fin 100)) by
    simpa only [fourthOrbit] using this
  ext x
  constructor
  · rintro ⟨g, rfl⟩
    obtain ⟨hg, hfix⟩ := (Subgroup.mem_stabilizerChain_iff _ _).mp g.2
    have h0 : (g : Equiv.Perm (Fin 100)) 0 = 0 := hfix 0 (by omega)
    have h1 : (g : Equiv.Perm (Fin 100)) 1 = 1 := hfix 1 (by omega)
    have h2 : (g : Equiv.Perm (Fin 100)) 2 = 2 := hfix 2 (by omega)
    have hr0 := related_apply hg 0 3
    have hr1 := related_apply hg 1 3
    have hr2 := related_apply hg 2 3
    rw [h0] at hr0
    rw [h1] at hr1
    rw [h2] at hr2
    have h38 := commonNeighbors_apply g.2 (x := 38) (by decide)
    have h49 := commonNeighbors_apply g.2 (x := 49) (by decide)
    have hne : related ((g : Equiv.Perm (Fin 100)) 3) ((g : Equiv.Perm (Fin 100)) 38) ≠
        related ((g : Equiv.Perm (Fin 100)) 3) ((g : Equiv.Perm (Fin 100)) 49) := by
      rw [related_apply hg, related_apply hg]
      decide +kernel
    simp only [commonNeighbors, Finset.mem_insert, Finset.mem_singleton] at h38 h49
    have hx : related ((g : Equiv.Perm (Fin 100)) 3) 38 ≠
        related ((g : Equiv.Perm (Fin 100)) 3) 49 := by
      rcases h38 with h38 | h38 <;> rcases h49 with h49 | h49 <;> grind
    exact (mem_fourthOrbit _).mpr ⟨hr0.trans (by decide +kernel),
      hr1.trans (by decide +kernel), hr2.trans (by decide +kernel), hx⟩
  · intro hx
    obtain ⟨h0, h1, h2, h3⟩ := fourthOrbitWords_apply x hx
    refine mem_orbit_iff.mpr ⟨⟨wordValue (fourthOrbitWords x), ?_⟩, h3⟩
    refine (Subgroup.mem_stabilizerChain_iff _ _).mpr ⟨wordValue_mem _, ?_⟩
    intro j hj
    interval_cases j <;> assumption

/-- The fourth basic orbit along `0, 1, 2, 3` has length 32. -/
@[simp]
theorem ncard_orbit_stabilizerChain_three :
    (orbit (HS.stabilizerChain pointSequence 3) (3 : Fin 100)).ncard = 32 := by
  rw [orbit_stabilizerChain_three, Set.ncard_coe_finset]
  decide +kernel

/-- The three-point stabilizer has order 32 times the order of the four-point stabilizer. -/
theorem card_stabilizerChain_three_eq :
    Nat.card (HS.stabilizerChain pointSequence 3) =
      32 * Nat.card (HS.stabilizerChain pointSequence 4) := by
  simpa only [pointSequence_apply, Fin.reduceOfNat, ncard_orbit_stabilizerChain_three] using
    (HS.ncard_orbit_mul_card_stabilizerChain_succ pointSequence 3).symm

end TauCeti.Sporadic.HS

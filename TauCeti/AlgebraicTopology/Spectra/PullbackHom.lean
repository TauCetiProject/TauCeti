/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.LiftingProperties.ParametrizedAdjunction
public import TauCeti.AlgebraicTopology.SimplicialSet.Pointed.TrivialFibration
public import TauCeti.AlgebraicTopology.Spectra.Cotensor
public import TauCeti.AlgebraicTopology.Spectra.LevelFactorization

import Mathlib.CategoryTheory.Monoidal.Closed.Braided

/-!
# Simplicial pullback-hom and pushout-product lifting for symmetric spectra

This file establishes the simplicial pushout-product and pullback-hom lifting properties for the
two level projective weak factorization systems `(projectiveCofibrations, levelTrivialFibrations)`
and `(levelFibrations.llp, levelFibrations)` on symmetric spectra.

First, level evaluation preserves pullbacks and `SymmetricSpectrum.cotensorLevelIso` identifies
`(E^K)_n` with the pointed mapping simplicial set `Map_*(K, E_n)`. Any pullback-hom corner for
`SymmetricSpectrum.cotensorFunctor` therefore induces a pointed simplicial pullback-hom corner in
every level (`SymmetricSpectrum.cotensorPullbackObjObjLevel`), transferring the three pointed
simplicial pullback-hom theorems to levelwise cotensors:

* a based monomorphism and a level fibration give a level fibration;
* a based anodyne extension and a level fibration give a level trivial fibration;
* a based monomorphism and a level trivial fibration give a level trivial fibration.

Second, `SymmetricSpectrum.levelSmashCotensorAdjunction₂` transports these three cotensor corner
results to pushout-product corners for `SymmetricSpectrum.levelSmashFunctor`:

* a projective cofibration smashed with a based monomorphism is a projective cofibration;
* a projective cofibration smashed with a based anodyne extension lies in `levelFibrations.llp`;
* a map in `levelFibrations.llp` smashed with a based monomorphism lies in `levelFibrations.llp`.

Third, adjoining a disjoint basepoint preserves monomorphisms and anodyne extensions, so
`PointedSSet.addBasepointForgetAdjunction` and
`SymmetricSpectrum.levelSmashMappingSpaceAdjunction₂` yield the three simplicial pullback-hom
theorems for `SymmetricSpectrum.mappingSpaceFunctor`:

* a projective cofibration and a level fibration give a Kan fibration of mapping spaces;
* a map in `levelFibrations.llp` and a level fibration give a map lifting against all
  monomorphisms (in particular a weak equivalence of simplicial sets);
* a projective cofibration and a level trivial fibration give a map lifting against all
  monomorphisms (in particular a weak equivalence of simplicial sets).

Specializing to initial and terminal objects shows in particular that `Map(X, E)` is a Kan complex
whenever `initial.to X` is a projective cofibration and every level of `E` is a Kan complex.
No model-category instance on simplicial sets or identification of `levelFibrations.llp` with
projective cofibrations that are level equivalences is assumed.

The proofs reuse Mathlib's `ParametrizedAdjunction.hasLiftingProperty_iff` by Joël Riou together
with the based simplicial pullback-hom theorems, and follow Proposition 5.2.2 of Hovey, Shipley
and Smith.

## Main definitions

* `SymmetricSpectrum.cotensorPullbackObjObjLevel`: level `n` of a cotensor pullback-hom corner as a
  based simplicial pullback-hom corner via `SymmetricSpectrum.cotensorLevelIso`.

## Main statements

* `SymmetricSpectrum.levelFibrations_cotensorFunctor_pullbackObjObjπ`,
  `SymmetricSpectrum.levelTrivialFibrations_cotensorFunctor_pullbackObjObjπ`, and
  `levelTrivialFibrations_cotensorFunctor_pullbackObjObjπ_of_levelTrivialFibrations`:
  the three cotensor pullback-hom lifting theorems.
* `SymmetricSpectrum.projectiveCofibrations_levelSmashFunctor_pushoutObjObjι`,
  `SymmetricSpectrum.llp_levelFibrations_levelSmashFunctor_pushoutObjObjι_of_anodyneExtensions`,
  and `SymmetricSpectrum.llp_levelFibrations_levelSmashFunctor_pushoutObjObjι`: the three
  levelwise-smash pushout-product lifting theorems.
* `SymmetricSpectrum.fibration_mappingSpaceFunctor_pullbackObjObjπ`,
  `SymmetricSpectrum.rlp_monomorphisms_mappingSpaceFunctor_pullbackObjObjπ_of_llp`, and
  `SymmetricSpectrum.rlp_monomorphisms_mappingSpaceFunctor_pullbackObjObjπ`: the three
  mapping-space pullback-hom lifting theorems.
* `SymmetricSpectrum.kanComplex_evaluation_cotensor` and
  `SymmetricSpectrum.kanComplex_mappingSpace`: Kan-complex closure for cotensor levels and mapping
  spaces.

## References

* M. Hovey, B. Shipley and J. Smith, *Symmetric spectra*, J. Amer. Math. Soc. 13 (2000),
  Sections 3.1, 5.1 and 5.2, Proposition 5.2.2.
* M. Hovey, *Model categories*, Mathematical Surveys and Monographs 63, American Mathematical
  Society, 1999, Section 4.2.
-/

public section

open CategoryTheory MonoidalCategory MonoidalClosed Limits MorphismProperty HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial

namespace TauCeti.SymmetricSpectrum

/-! ### Fibrant levels and levelwise cotensor corners -/

/-- If level `n` of `E` is a Kan complex, then level `n` of the cotensor `E^K` is a Kan complex,
with no hypothesis on `K` or on the other levels of `E`. -/
instance kanComplex_evaluation_cotensor (K : PointedSSet.{0}) (E : SymmetricSpectrum) (n : ℕ)
    [SSet.KanComplex ((evaluation n).obj E).right] :
    SSet.KanComplex ((evaluation n).obj ((cotensor K).obj E)).right := by
  let e : ((evaluation n).obj ((cotensor K).obj E)).right ≅
      ((PointedSSet.ihom K).obj ((evaluation n).obj E)).right :=
    PointedSSet.forgetBasepoint.mapIso (cotensorLevelIso K E n)
  exact isFibrant_of_fibration e.hom

/-- Evaluating a cotensor pullback-hom corner `E^L ⟶ E^K ×[B^K] B^L` at level `n` gives a pointed
simplicial pullback-hom corner `Map_*(L, E_n) ⟶ Map_*(K, E_n) ×[Map_*(K, B_n)] Map_*(L, B_n)` via
`cotensorLevelIso`. The body is exposed so that its pullback carrier `(evaluation n).obj P.pt`
agrees definitionally with level `n` of `P.pt`. -/
@[expose, simps pt fst snd π]
noncomputable def cotensorPullbackObjObjLevel {K L : PointedSSet.{0}} {i : K ⟶ L}
    {E B : SymmetricSpectrum} {p : E ⟶ B} (P : cotensorFunctor.PullbackObjObj i p) (n : ℕ) :
    MonoidalClosed.internalHom.PullbackObjObj i ((evaluation n).map p) where
  pt := (evaluation n).obj P.pt
  fst := (evaluation n).map P.fst ≫ (cotensorLevelIso K E n).hom
  snd := (evaluation n).map P.snd ≫ (cotensorLevelIso L B n).hom
  isPullback := by
    have : (evaluation n).IsRightAdjoint := (freeEvaluationAdjunction n).isRightAdjoint
    exact (P.isPullback.map (evaluation n)).of_iso
      (Iso.refl _) (cotensorLevelIso K E n) (cotensorLevelIso L B n) (cotensorLevelIso K B n)
      (Category.id_comp _).symm
      (Category.id_comp _).symm
      (cotensorLevelIso_hom_naturality K p n)
      (cotensorLevelIso_hom_naturality_left i B n)
  π := (cotensorLevelIso L E n).inv ≫ (evaluation n).map P.π
  π_fst :=
    (Category.assoc _ _ _).trans <|
      (Iso.inv_comp_eq _).2 <|
        (Category.assoc _ _ _).symm.trans <|
          (congrArg (· ≫ (cotensorLevelIso K E n).hom)
            (((evaluation n).map_comp P.π P.fst).symm.trans
              (congrArg (evaluation n).map P.π_fst))).trans
            (cotensorLevelIso_hom_naturality_left i E n)
  π_snd :=
    (Category.assoc _ _ _).trans <|
      (Iso.inv_comp_eq _).2 <|
        (Category.assoc _ _ _).symm.trans <|
          (congrArg (· ≫ (cotensorLevelIso L B n).hom)
            (((evaluation n).map_comp P.π P.snd).symm.trans
              (congrArg (evaluation n).map P.π_snd))).trans
            (cotensorLevelIso_hom_naturality L p n)

/-- In level `n`, the corner map of `P` factors as `cotensorLevelIso` followed by the pointed
simplicial corner map of `cotensorPullbackObjObjLevel P n`. -/
@[reassoc]
lemma cotensorLevelIso_hom_comp_cotensorPullbackObjObjLevel_π {K L : PointedSSet.{0}}
    {i : K ⟶ L} {E B : SymmetricSpectrum} {p : E ⟶ B}
    (P : cotensorFunctor.PullbackObjObj i p) (n : ℕ) :
    (cotensorLevelIso L E n).hom ≫ (cotensorPullbackObjObjLevel P n).π =
      (evaluation n).map P.π :=
  Iso.hom_inv_id_assoc (cotensorLevelIso L E n) ((evaluation n).map P.π)

/-- For any isomorphism-invariant class `W` of simplicial maps, level `n` of the corner map `P.π`
lies in `W` on underlying simplicial sets exactly when the pointed simplicial corner map of
`cotensorPullbackObjObjLevel P n` does. -/
lemma cotensorPullbackObjObjLevel_mem_iff (W : MorphismProperty SSet.{0}) [W.RespectsIso]
    {K L : PointedSSet.{0}} {i : K ⟶ L} {E B : SymmetricSpectrum} {p : E ⟶ B}
    (P : cotensorFunctor.PullbackObjObj i p) (n : ℕ) :
    W ((evaluation n).map P.π).right ↔ W (cotensorPullbackObjObjLevel P n).π.right := by
  let e : ((evaluation n).obj ((cotensor L).obj E)).right ≅
      ((MonoidalClosed.internalHom.obj (Opposite.op L)).obj ((evaluation n).obj E)).right :=
    PointedSSet.forgetBasepoint.mapIso (cotensorLevelIso L E n)
  have h : ((evaluation n).map P.π).right = e.hom ≫ (cotensorPullbackObjObjLevel P n).π.right :=
    congrArg Under.Hom.right (cotensorLevelIso_hom_comp_cotensorPullbackObjObjLevel_π P n).symm
  exact h ▸ W.cancel_left_of_respectsIso e.hom (cotensorPullbackObjObjLevel P n).π.right

/-- The cotensor pullback-hom corner of a based monomorphism and a level fibration is a level
fibration. -/
lemma levelFibrations_cotensorFunctor_pullbackObjObjπ {K L : PointedSSet.{0}} (i : K ⟶ L)
    [Mono i.right] {E B : SymmetricSpectrum} {p : E ⟶ B} (hp : levelFibrations p)
    (P : cotensorFunctor.PullbackObjObj i p) : levelFibrations P.π := by
  rw [levelFibrations_iff]
  intro n
  have := (levelFibrations_iff p).1 hp n
  have hπ : Fibration (cotensorPullbackObjObjLevel P n).π.right :=
    PointedSSet.fibration_pullbackObjObjπ i ((evaluation n).map p)
      (cotensorPullbackObjObjLevel P n)
  exact (HomotopicalAlgebra.fibration_iff _).2
    ((cotensorPullbackObjObjLevel_mem_iff (fibrations SSet.{0}) P n).2 hπ.mem)

/-- The cotensor pullback-hom corner of a based anodyne extension and a level fibration is a level
trivial fibration. -/
lemma levelTrivialFibrations_cotensorFunctor_pullbackObjObjπ {K L : PointedSSet.{0}} {i : K ⟶ L}
    (hi : SSet.anodyneExtensions i.right) {E B : SymmetricSpectrum} {p : E ⟶ B}
    (hp : levelFibrations p) (P : cotensorFunctor.PullbackObjObj i p) :
    levelTrivialFibrations P.π := by
  rw [levelTrivialFibrations_iff]
  intro n
  have := (levelFibrations_iff p).1 hp n
  exact (cotensorPullbackObjObjLevel_mem_iff (monomorphisms SSet.{0}).rlp P n).2
    (PointedSSet.rlp_monomorphisms_pullbackObjObjπ i ((evaluation n).map p) hi
      (cotensorPullbackObjObjLevel P n))

/-- The cotensor pullback-hom corner of a based monomorphism and a level trivial fibration is a
level trivial fibration. -/
lemma levelTrivialFibrations_cotensorFunctor_pullbackObjObjπ_of_levelTrivialFibrations
    {K L : PointedSSet.{0}} (i : K ⟶ L) [Mono i.right] {E B : SymmetricSpectrum} {p : E ⟶ B}
    (hp : levelTrivialFibrations p) (P : cotensorFunctor.PullbackObjObj i p) :
    levelTrivialFibrations P.π := by
  rw [levelTrivialFibrations_iff]
  intro n
  exact (cotensorPullbackObjObjLevel_mem_iff (monomorphisms SSet.{0}).rlp P n).2
    (PointedSSet.rlp_monomorphisms_pullbackObjObjπ_of_rlp i ((evaluation n).map p)
      ((levelTrivialFibrations_iff p).1 hp n) (cotensorPullbackObjObjLevel P n))

/-- Cotensoring with any pointed simplicial set preserves level fibrations. -/
lemma levelFibrations_cotensor_map (K : PointedSSet.{0}) {E B : SymmetricSpectrum} {p : E ⟶ B}
    (hp : levelFibrations p) : levelFibrations ((cotensor K).map p) := by
  let i : Under.mk (𝟙 (Δ[0] : SSet.{0})) ⟶ K := Under.homMk K.hom
  have : Mono i.right := SSet.stdSimplex.isTerminalObj₀.mono_from K.hom
  exact levelFibrations_cotensorFunctor_pullbackObjObjπ i hp
    (Functor.PullbackObjObj.ofIsInitial cotensorFunctor i p Under.mkIdInitial)

/-- Cotensoring with any pointed simplicial set preserves level trivial fibrations. -/
lemma levelTrivialFibrations_cotensor_map (K : PointedSSet.{0}) {E B : SymmetricSpectrum}
    {p : E ⟶ B} (hp : levelTrivialFibrations p) : levelTrivialFibrations ((cotensor K).map p) := by
  let i : Under.mk (𝟙 (Δ[0] : SSet.{0})) ⟶ K := Under.homMk K.hom
  have : Mono i.right := SSet.stdSimplex.isTerminalObj₀.mono_from K.hom
  exact levelTrivialFibrations_cotensorFunctor_pullbackObjObjπ_of_levelTrivialFibrations i hp
    (Functor.PullbackObjObj.ofIsInitial cotensorFunctor i p Under.mkIdInitial)

/-- Restricting a cotensor along a based monomorphism gives a level fibration whenever every level
of the target spectrum is a Kan complex. -/
lemma levelFibrations_cotensorFunctor_map_app {K L : PointedSSet.{0}} (i : K ⟶ L) [Mono i.right]
    {E : SymmetricSpectrum} (hE : ∀ n, SSet.KanComplex ((evaluation n).obj E).right) :
    levelFibrations ((cotensorFunctor.map i.op).app E) :=
  levelFibrations_cotensorFunctor_pullbackObjObjπ i ((levelFibrations_terminal_from_iff E).2 hE)
    (Functor.PullbackObjObj.ofIsTerminal cotensorFunctor i (terminal.from E) terminalIsTerminal)

/-- Restricting a cotensor along a based anodyne extension gives a level trivial fibration whenever
every level of the target spectrum is a Kan complex. -/
lemma levelTrivialFibrations_cotensorFunctor_map_app {K L : PointedSSet.{0}} {i : K ⟶ L}
    (hi : SSet.anodyneExtensions i.right) {E : SymmetricSpectrum}
    (hE : ∀ n, SSet.KanComplex ((evaluation n).obj E).right) :
    levelTrivialFibrations ((cotensorFunctor.map i.op).app E) :=
  levelTrivialFibrations_cotensorFunctor_pullbackObjObjπ hi
    ((levelFibrations_terminal_from_iff E).2 hE)
    (Functor.PullbackObjObj.ofIsTerminal cotensorFunctor i (terminal.from E) terminalIsTerminal)

/-- Restricting a cotensor along a based anodyne extension gives a level equivalence whenever every
level of the target spectrum is a Kan complex. -/
lemma levelEquivalences_cotensorFunctor_map_app {K L : PointedSSet.{0}} {i : K ⟶ L}
    (hi : SSet.anodyneExtensions i.right) {E : SymmetricSpectrum}
    (hE : ∀ n, SSet.KanComplex ((evaluation n).obj E).right) :
    levelEquivalences ((cotensorFunctor.map i.op).app E) :=
  levelTrivialFibrations_le_levelEquivalences _
    (levelTrivialFibrations_cotensorFunctor_map_app hi hE)

/-! ### Pushout-products for smashing spectra with pointed simplicial sets -/

/-- The pushout-product of a projective cofibration of symmetric spectra with a based monomorphism
is a projective cofibration. -/
lemma projectiveCofibrations_levelSmashFunctor_pushoutObjObjι {X Y : SymmetricSpectrum}
    {f : X ⟶ Y} (hf : projectiveCofibrations f) {K L : PointedSSet.{0}} (i : K ⟶ L) [Mono i.right]
    (Q : levelSmashFunctor.PushoutObjObj f i) : projectiveCofibrations Q.ι := by
  rw [← llp_eq_of_wfs projectiveCofibrations levelTrivialFibrations]
  intro E B p hp
  let P := Functor.PullbackObjObj.ofHasPullback cotensorFunctor i p
  have : HasLiftingProperty f P.π := hasLiftingProperty_of_wfs f P.π hf
    (levelTrivialFibrations_cotensorFunctor_pullbackObjObjπ_of_levelTrivialFibrations i hp P)
  exact (levelSmashCotensorAdjunction₂.hasLiftingProperty_iff Q.flip P).2 this

/-- The pushout-product of a projective cofibration of symmetric spectra with a based anodyne
extension lifts against every level fibration. -/
lemma llp_levelFibrations_levelSmashFunctor_pushoutObjObjι_of_anodyneExtensions
    {X Y : SymmetricSpectrum} {f : X ⟶ Y} (hf : projectiveCofibrations f)
    {K L : PointedSSet.{0}} {i : K ⟶ L} (hi : SSet.anodyneExtensions i.right)
    (Q : levelSmashFunctor.PushoutObjObj f i) : levelFibrations.llp Q.ι := by
  intro E B p hp
  let P := Functor.PullbackObjObj.ofHasPullback cotensorFunctor i p
  have : HasLiftingProperty f P.π := hasLiftingProperty_of_wfs f P.π hf
    (levelTrivialFibrations_cotensorFunctor_pullbackObjObjπ hi hp P)
  exact (levelSmashCotensorAdjunction₂.hasLiftingProperty_iff Q.flip P).2 this

/-- The pushout-product of a map lifting against all level fibrations with a based monomorphism
also lifts against all level fibrations. -/
lemma llp_levelFibrations_levelSmashFunctor_pushoutObjObjι {X Y : SymmetricSpectrum} {f : X ⟶ Y}
    (hf : levelFibrations.llp f) {K L : PointedSSet.{0}} (i : K ⟶ L) [Mono i.right]
    (Q : levelSmashFunctor.PushoutObjObj f i) : levelFibrations.llp Q.ι := by
  intro E B p hp
  let P := Functor.PullbackObjObj.ofHasPullback cotensorFunctor i p
  have : HasLiftingProperty f P.π :=
    hf P.π (levelFibrations_cotensorFunctor_pullbackObjObjπ i hp P)
  exact (levelSmashCotensorAdjunction₂.hasLiftingProperty_iff Q.flip P).2 this

/-- Smashing any pointed simplicial set on the right preserves projective cofibrations. -/
lemma projectiveCofibrations_levelSmashRight_map {X Y : SymmetricSpectrum} {f : X ⟶ Y}
    (hf : projectiveCofibrations f) (K : PointedSSet.{0}) :
    projectiveCofibrations ((levelSmashRight K).map f) := by
  let i : Under.mk (𝟙 (Δ[0] : SSet.{0})) ⟶ K := Under.homMk K.hom
  have : Mono i.right := SSet.stdSimplex.isTerminalObj₀.mono_from K.hom
  exact projectiveCofibrations_levelSmashFunctor_pushoutObjObjι hf i
    (Functor.PushoutObjObj.ofIsInitialRight levelSmashFunctor f i Under.mkIdInitial)

/-- Smashing any pointed simplicial set on the right preserves the maps lifting against all level
fibrations. -/
lemma llp_levelFibrations_levelSmashRight_map {X Y : SymmetricSpectrum} {f : X ⟶ Y}
    (hf : levelFibrations.llp f) (K : PointedSSet.{0}) :
    levelFibrations.llp ((levelSmashRight K).map f) := by
  let i : Under.mk (𝟙 (Δ[0] : SSet.{0})) ⟶ K := Under.homMk K.hom
  have : Mono i.right := SSet.stdSimplex.isTerminalObj₀.mono_from K.hom
  exact llp_levelFibrations_levelSmashFunctor_pushoutObjObjι hf i
    (Functor.PushoutObjObj.ofIsInitialRight levelSmashFunctor f i Under.mkIdInitial)

/-- Smashing a projectively cofibrant spectrum `X` with a based monomorphism gives a projective
cofibration. -/
lemma projectiveCofibrations_levelSmash_map {X : SymmetricSpectrum}
    (hX : projectiveCofibrations (initial.to X)) {K L : PointedSSet.{0}} (i : K ⟶ L)
    [Mono i.right] : projectiveCofibrations ((levelSmash X).map i) :=
  projectiveCofibrations_levelSmashFunctor_pushoutObjObjι hX i
    (Functor.PushoutObjObj.ofIsInitialLeft levelSmashFunctor (initial.to X) i initialIsInitial)

/-- Smashing a projectively cofibrant spectrum `X` with a based anodyne extension gives a map
lifting against all level fibrations. -/
lemma llp_levelFibrations_levelSmash_map_of_anodyneExtensions {X : SymmetricSpectrum}
    (hX : projectiveCofibrations (initial.to X)) {K L : PointedSSet.{0}} {i : K ⟶ L}
    (hi : SSet.anodyneExtensions i.right) : levelFibrations.llp ((levelSmash X).map i) :=
  llp_levelFibrations_levelSmashFunctor_pushoutObjObjι_of_anodyneExtensions hX hi
    (Functor.PushoutObjObj.ofIsInitialLeft levelSmashFunctor (initial.to X) i initialIsInitial)

/-- If `⊥ ⟶ X` lifts against all level fibrations, then smashing `X` with any based monomorphism
lifts against all level fibrations. -/
lemma llp_levelFibrations_levelSmash_map {X : SymmetricSpectrum}
    (hX : levelFibrations.llp (initial.to X)) {K L : PointedSSet.{0}} (i : K ⟶ L) [Mono i.right] :
    levelFibrations.llp ((levelSmash X).map i) :=
  llp_levelFibrations_levelSmashFunctor_pushoutObjObjι hX i
    (Functor.PushoutObjObj.ofIsInitialLeft levelSmashFunctor (initial.to X) i initialIsInitial)

/-- The pushout-product of a projective cofibration `f` with `j₊` for an anodyne extension `j` of
simplicial sets lifts against all level fibrations. -/
lemma llp_levelFibrations_levelSmashFunctor_pushoutObjObjι_addBasepoint_map
    {X Y : SymmetricSpectrum} {f : X ⟶ Y} (hf : projectiveCofibrations f)
    {A B : SSet.{0}} {j : A ⟶ B} (hj : SSet.anodyneExtensions j)
    (Q : levelSmashFunctor.PushoutObjObj f (PointedSSet.addBasepoint.map j)) :
    levelFibrations.llp Q.ι :=
  llp_levelFibrations_levelSmashFunctor_pushoutObjObjι_of_anodyneExtensions hf
    (PointedSSet.anodyneExtensions_addBasepoint_map_right hj) Q

/-- Smashing a projectively cofibrant spectrum `X` with `j₊` for an anodyne extension `j` gives a
map lifting against all level fibrations; in particular this applies to cylinder endpoint
inclusions `X ∧ Δ[0]₊ ⟶ X ∧ Δ[1]₊`. -/
lemma llp_levelFibrations_levelSmash_addBasepoint_map {X : SymmetricSpectrum}
    (hX : projectiveCofibrations (initial.to X)) {A B : SSet.{0}} {j : A ⟶ B}
    (hj : SSet.anodyneExtensions j) :
    levelFibrations.llp ((levelSmash X).map (PointedSSet.addBasepoint.map j)) :=
  llp_levelFibrations_levelSmashFunctor_pushoutObjObjι_addBasepoint_map hX hj
    (Functor.PushoutObjObj.ofIsInitialLeft levelSmashFunctor (initial.to X)
      (PointedSSet.addBasepoint.map j) initialIsInitial)

/-! ### Mapping-space pullback-hom corners -/

/-- A map `j` of simplicial sets lifts against the underlying map of a mapping-space pullback-hom
corner `Map(Y, E) ⟶ Map(X, E) ×[Map(X, B)] Map(Y, B)` exactly when the pushout-product of `f` and
`j₊` lifts against `p`. -/
lemma hasLiftingProperty_mappingSpaceFunctor_pullbackObjObjπ_iff {X Y E B : SymmetricSpectrum}
    {f : X ⟶ Y} {p : E ⟶ B} (P : mappingSpaceFunctor.PullbackObjObj f p)
    {A C : SSet.{0}} (j : A ⟶ C)
    (Q : levelSmashFunctor.PushoutObjObj f (PointedSSet.addBasepoint.map j)) :
    HasLiftingProperty j P.π.right ↔ HasLiftingProperty Q.ι p :=
  (PointedSSet.addBasepointForgetAdjunction.hasLiftingProperty_iff j P.π).symm.trans
    (levelSmashMappingSpaceAdjunction₂.hasLiftingProperty_iff Q P).symm

/-- The mapping-space pullback-hom corner of a projective cofibration and a level fibration is a
Kan fibration on underlying simplicial sets. -/
lemma fibration_mappingSpaceFunctor_pullbackObjObjπ {X Y : SymmetricSpectrum} {f : X ⟶ Y}
    (hf : projectiveCofibrations f) {E B : SymmetricSpectrum} {p : E ⟶ B} (hp : levelFibrations p)
    (P : mappingSpaceFunctor.PullbackObjObj f p) : Fibration P.π.right := by
  rw [SSet.modelCategoryQuillen.fibration_iff]
  intro A C j hj
  let Q := Functor.PushoutObjObj.ofHasPushout levelSmashFunctor f (PointedSSet.addBasepoint.map j)
  have : HasLiftingProperty Q.ι p :=
    llp_levelFibrations_levelSmashFunctor_pushoutObjObjι_addBasepoint_map hf
      (SSet.anodyneExtensions_eq_llp_rlp.symm ▸ le_llp_rlp _ _ hj) Q p hp
  exact (hasLiftingProperty_mappingSpaceFunctor_pullbackObjObjπ_iff P j Q).2 this

/-- The mapping-space pullback-hom corner of a map lifting against all level fibrations and a level
fibration lifts against all monomorphisms of simplicial sets. -/
lemma rlp_monomorphisms_mappingSpaceFunctor_pullbackObjObjπ_of_llp {X Y : SymmetricSpectrum}
    {f : X ⟶ Y} (hf : levelFibrations.llp f) {E B : SymmetricSpectrum} {p : E ⟶ B}
    (hp : levelFibrations p) (P : mappingSpaceFunctor.PullbackObjObj f p) :
    (monomorphisms SSet.{0}).rlp P.π.right := by
  intro A C j hj
  have : Mono j := hj
  let Q := Functor.PushoutObjObj.ofHasPushout levelSmashFunctor f (PointedSSet.addBasepoint.map j)
  have : HasLiftingProperty Q.ι p :=
    llp_levelFibrations_levelSmashFunctor_pushoutObjObjι hf (PointedSSet.addBasepoint.map j) Q p hp
  exact (hasLiftingProperty_mappingSpaceFunctor_pullbackObjObjπ_iff P j Q).2 this

/-- The mapping-space pullback-hom corner of a projective cofibration and a level trivial fibration
lifts against all monomorphisms of simplicial sets. -/
lemma rlp_monomorphisms_mappingSpaceFunctor_pullbackObjObjπ {X Y : SymmetricSpectrum} {f : X ⟶ Y}
    (hf : projectiveCofibrations f) {E B : SymmetricSpectrum} {p : E ⟶ B}
    (hp : levelTrivialFibrations p) (P : mappingSpaceFunctor.PullbackObjObj f p) :
    (monomorphisms SSet.{0}).rlp P.π.right := by
  intro A C j hj
  have : Mono j := hj
  let Q := Functor.PushoutObjObj.ofHasPushout levelSmashFunctor f (PointedSSet.addBasepoint.map j)
  have : HasLiftingProperty Q.ι p :=
    hasLiftingProperty_of_wfs Q.ι p
      (projectiveCofibrations_levelSmashFunctor_pushoutObjObjι hf
        (PointedSSet.addBasepoint.map j) Q) hp
  exact (hasLiftingProperty_mappingSpaceFunctor_pullbackObjObjπ_iff P j Q).2 this

/-- Precomposition `Map(Y, E) ⟶ Map(X, E)` along a projective cofibration `f : X ⟶ Y` is a Kan
fibration whenever every level of `E` is a Kan complex. -/
lemma fibration_mappingSpaceFunctor_map_app {X Y : SymmetricSpectrum} {f : X ⟶ Y}
    (hf : projectiveCofibrations f) {E : SymmetricSpectrum}
    (hE : ∀ n, SSet.KanComplex ((evaluation n).obj E).right) :
    Fibration ((mappingSpaceFunctor.map f.op).app E).right :=
  fibration_mappingSpaceFunctor_pullbackObjObjπ hf ((levelFibrations_terminal_from_iff E).2 hE)
    (Functor.PullbackObjObj.ofIsTerminal mappingSpaceFunctor f (terminal.from E) terminalIsTerminal)

/-- Precomposition `Map(Y, E) ⟶ Map(X, E)` along a map `f : X ⟶ Y` in `levelFibrations.llp` lifts
against all monomorphisms whenever every level of `E` is a Kan complex. -/
lemma rlp_monomorphisms_mappingSpaceFunctor_map_app {X Y : SymmetricSpectrum} {f : X ⟶ Y}
    (hf : levelFibrations.llp f) {E : SymmetricSpectrum}
    (hE : ∀ n, SSet.KanComplex ((evaluation n).obj E).right) :
    (monomorphisms SSet.{0}).rlp ((mappingSpaceFunctor.map f.op).app E).right :=
  rlp_monomorphisms_mappingSpaceFunctor_pullbackObjObjπ_of_llp hf
    ((levelFibrations_terminal_from_iff E).2 hE)
    (Functor.PullbackObjObj.ofIsTerminal mappingSpaceFunctor f (terminal.from E) terminalIsTerminal)

/-- Precomposition `Map(Y, E) ⟶ Map(X, E)` along a map `f : X ⟶ Y` in `levelFibrations.llp` is a
weak equivalence of simplicial sets whenever every level of `E` is a Kan complex. -/
lemma weakEquivalence_mappingSpaceFunctor_map_app {X Y : SymmetricSpectrum} {f : X ⟶ Y}
    (hf : levelFibrations.llp f) {E : SymmetricSpectrum}
    (hE : ∀ n, SSet.KanComplex ((evaluation n).obj E).right) :
    WeakEquivalence ((mappingSpaceFunctor.map f.op).app E).right :=
  weakEquivalence_of_rlp_monomorphisms (rlp_monomorphisms_mappingSpaceFunctor_map_app hf hE)

/-- Mapping out of a projectively cofibrant spectrum sends level fibrations to Kan fibrations. -/
lemma fibration_mappingSpace_map {X : SymmetricSpectrum}
    (hX : projectiveCofibrations (initial.to X)) {E B : SymmetricSpectrum} {p : E ⟶ B}
    (hp : levelFibrations p) : Fibration ((mappingSpace X).map p).right :=
  fibration_mappingSpaceFunctor_pullbackObjObjπ hX hp
    (Functor.PullbackObjObj.ofIsInitial mappingSpaceFunctor (initial.to X) p initialIsInitial)

/-- Mapping out of a projectively cofibrant spectrum sends level trivial fibrations to maps lifting
against all monomorphisms of simplicial sets. -/
lemma rlp_monomorphisms_mappingSpace_map {X : SymmetricSpectrum}
    (hX : projectiveCofibrations (initial.to X)) {E B : SymmetricSpectrum} {p : E ⟶ B}
    (hp : levelTrivialFibrations p) :
    (monomorphisms SSet.{0}).rlp ((mappingSpace X).map p).right :=
  rlp_monomorphisms_mappingSpaceFunctor_pullbackObjObjπ hX hp
    (Functor.PullbackObjObj.ofIsInitial mappingSpaceFunctor (initial.to X) p initialIsInitial)

/-- Mapping out of a projectively cofibrant spectrum sends level trivial fibrations to weak
equivalences of simplicial sets. -/
lemma weakEquivalence_mappingSpace_map {X : SymmetricSpectrum}
    (hX : projectiveCofibrations (initial.to X)) {E B : SymmetricSpectrum} {p : E ⟶ B}
    (hp : levelTrivialFibrations p) :
    WeakEquivalence ((mappingSpace X).map p).right :=
  weakEquivalence_of_rlp_monomorphisms (rlp_monomorphisms_mappingSpace_map hX hp)

/-- For a projectively cofibrant symmetric spectrum `X` and a spectrum `E` whose levels are Kan
complexes, the mapping space `Map(X, E)` is a Kan complex. -/
lemma kanComplex_mappingSpace {X : SymmetricSpectrum}
    (hX : projectiveCofibrations (initial.to X)) {E : SymmetricSpectrum}
    (hE : ∀ n, SSet.KanComplex ((evaluation n).obj E).right) :
    SSet.KanComplex ((mappingSpace X).obj E).right := by
  have hf : Fibration ((mappingSpaceFunctor.map (initial.to X).op).app E).right :=
    fibration_mappingSpaceFunctor_map_app hX hE
  have hT₀ : IsTerminal
      ((mappingSpaceFunctor.flip.obj E).obj (Opposite.op (⊥_ SymmetricSpectrum))) :=
    initialIsInitial.op.isTerminalObj (mappingSpaceFunctor.flip.obj E) _
  have hT : IsTerminal
      (((mappingSpaceFunctor.obj (Opposite.op (⊥_ SymmetricSpectrum))).obj E).right) :=
    hT₀.isTerminalObj PointedSSet.forgetBasepoint _
  exact (isFibrant_iff_of_isTerminal _ hT).2 hf

end TauCeti.SymmetricSpectrum

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialSet.Pointed.TrivialFibration
public import TauCeti.AlgebraicTopology.Spectra.LevelFactorization
public import TauCeti.AlgebraicTopology.Spectra.Limits
public import TauCeti.AlgebraicTopology.Spectra.Suspension
public import TauCeti.AlgebraicTopology.Spectra.Tensor
public import TauCeti.CategoryTheory.LiftingProperties.Under
public import Mathlib.CategoryTheory.LiftingProperties.ParametrizedAdjunction

/-!
# Pushout-products and pullback-hom lifting for symmetric spectra

For the level projective weak factorization systems on `SymmetricSpectrum`
(`projectiveCofibrations` against `levelTrivialFibrations`, and `levelFibrations.llp` against
`levelFibrations`), the point-set simplicial tensors, cotensors, and mapping spaces satisfy all
relative lifting axioms:

* **Cotensor pullback-hom corners**: for a pointed or unpointed simplicial map `j` and a spectrum
  map `p`, the cotensor corner is
  - a level fibration when `j` is a monomorphism and `p` is a level fibration;
  - a level trivial fibration (hence a level fibration and a level equivalence) when `j` is
    anodyne and `p` is a level fibration, or when `j` is a monomorphism and `p` is a level
    trivial fibration.
* **Smash and simplicial-tensor pushout-products**: for a spectrum map `i` and a pointed or
  unpointed simplicial map `j`, the pushout-product lies in
  - `projectiveCofibrations` when `i ∈ projectiveCofibrations` and `j` is a monomorphism;
  - `levelFibrations.llp` when `i ∈ projectiveCofibrations` and `j` is anodyne, or when
    `i ∈ levelFibrations.llp` and `j` is a monomorphism.
* **Mapping-space pullback-hom corners**: for spectrum maps `i : A ⟶ B` and `p : E ⟶ F`, the
  mapping-space corner `Map(B, E) ⟶ Map(A, E) ×[Map(A, F)] Map(B, F)` is
  - a Kan fibration when `i ∈ projectiveCofibrations` and `p ∈ levelFibrations`;
  - a map lifting against all monomorphisms (hence a Kan fibration and a weak equivalence of
    simplicial sets) when `i ∈ projectiveCofibrations` and `p ∈ levelTrivialFibrations`, or when
    `i ∈ levelFibrations.llp` and `p ∈ levelFibrations`.

Specializing to initial and terminal objects shows in particular that free spectra `F_n K` on all
pointed simplicial sets `K` and the sphere spectrum `𝟙_ SymmetricSpectrum` are projectively
cofibrant, that `E` is level-fibrant precisely when every level `E_n` is a Kan complex, and that
`Map(X, E)` is a Kan complex whenever `X` is projectively cofibrant and every level of `E` is a Kan
complex.

No identification of arbitrary weak equivalences with anodyne extensions and no full model-category
structure is assumed here: every statement is proved directly from the levelwise pointed
pullback-hom theorems and Mathlib's `ParametrizedAdjunction.hasLiftingProperty_iff`.

## References

* M. Hovey, B. Shipley and J. Smith, *Symmetric spectra*, J. Amer. Math. Soc. 13 (2000),
  Proposition 5.1.4 and Lemma 5.1.5.
-/

public section

open CategoryTheory MonoidalCategory MonoidalClosed Limits MorphismProperty HomotopicalAlgebra
open Opposite SSet.modelCategoryQuillen
open scoped Simplicial

namespace TauCeti.SymmetricSpectrum

open PointedSSet

/-! ### Level fibrancy and free projective cofibrations -/

/-- The free spectrum functor at level `n` preserves all small colimits. -/
instance free_preservesColimits (n : ℕ) : PreservesColimitsOfSize.{0, 0} (free n) :=
  (freeEvaluationAdjunction n).leftAdjoint_preservesColimits

/-- Level evaluation preserves all small limits of symmetric spectra. -/
instance evaluation_preservesLimits (n : ℕ) : PreservesLimitsOfSize.{0, 0} (evaluation n) :=
  (freeEvaluationAdjunction n).rightAdjoint_preservesLimits

/-- A symmetric spectrum `E` has `E ⟶ ⊤` in `levelFibrations` if and only if every level `E_n` is
a Kan complex. -/
lemma levelFibrations_terminal_from_iff (E : SymmetricSpectrum) :
    levelFibrations (terminal.from E) ↔
      ∀ n, SSet.KanComplex ((evaluation n).obj E).right := by
  rw [levelFibrations_iff]
  refine forall_congr' fun n ↦ ?_
  have : PreservesLimitsOfSize.{0, 0} (evaluation n ⋙ forgetBasepoint) :=
    (freeAddBasepointAdjunction n).rightAdjoint_preservesLimits
  have hT := terminalIsTerminal.isTerminalObj (evaluation n ⋙ forgetBasepoint)
    (⊤_ SymmetricSpectrum)
  exact (isFibrant_iff_of_isTerminal ((evaluation n).map (terminal.from E)).right hT).symm

/-- For every based map `j : K ⟶ L` of pointed simplicial sets whose underlying map is a
monomorphism, the free spectrum map `F_n j` is a projective cofibration. -/
lemma free_map_mem_projectiveCofibrations {K L : PointedSSet.{0}} (j : K ⟶ L) [Mono j.right]
    (n : ℕ) : projectiveCofibrations ((free n).map j) := by
  rw [projectiveCofibrations_iff]
  intro E F p hp
  rw [(freeEvaluationAdjunction n).hasLiftingProperty_iff]
  have : HasLiftingProperty j.right ((evaluation n).map p).right :=
    (levelTrivialFibrations_iff p).1 hp n j.right (.infer_property j.right)
  exact HasLiftingProperty.under j ((evaluation n).map p)

/-- For every based map `j : K ⟶ L` of pointed simplicial sets whose underlying map is an anodyne
extension, the free spectrum map `F_n j` lifts against all level fibrations. -/
lemma free_map_mem_llp_levelFibrations {K L : PointedSSet.{0}} {j : K ⟶ L}
    (hj : SSet.anodyneExtensions j.right) (n : ℕ) :
    levelFibrations.llp ((free n).map j) := by
  intro E F p hp
  rw [(freeEvaluationAdjunction n).hasLiftingProperty_iff]
  have : HasLiftingProperty j.right ((evaluation n).map p).right :=
    hj _ ((levelFibrations_iff p).1 hp n).mem
  exact HasLiftingProperty.under j ((evaluation n).map p)

/-- Every free symmetric spectrum `F_n K` on a pointed simplicial set `K` is projectively
cofibrant. -/
lemma projectiveCofibrations_initial_to_free (K : PointedSSet.{0}) (n : ℕ) :
    projectiveCofibrations (initial.to ((free n).obj K)) := by
  let u : Under.mk (𝟙 (Δ[0] : SSet.{0})) ⟶ K := Under.homMk K.hom
  have : Mono u.right := SSet.stdSimplex.isTerminalObj₀.mono_from K.hom
  let hI := Under.mkIdInitial.isInitialObj (free n) (Under.mk (𝟙 (Δ[0] : SSet.{0})))
  let e : (free n).obj (Under.mk (𝟙 (Δ[0] : SSet.{0}))) ≅ ⊥_ SymmetricSpectrum :=
    hI.uniqueUpToIso initialIsInitial
  have he : e.inv ≫ (free n).map u = initial.to ((free n).obj K) :=
    initialIsInitial.hom_ext _ _
  rw [← he, projectiveCofibrations.cancel_left_of_respectsIso]
  exact free_map_mem_projectiveCofibrations u n

/-- The sphere spectrum `𝟙_ SymmetricSpectrum` is projectively cofibrant. -/
lemma projectiveCofibrations_initial_to_unit :
    projectiveCofibrations (initial.to (𝟙_ SymmetricSpectrum)) := by
  have he : initial.to ((free 0).obj (𝟙_ PointedSSet.{0})) ≫ suspensionUnitIso.hom =
      initial.to (𝟙_ SymmetricSpectrum) :=
    initialIsInitial.hom_ext _ _
  rw [← he, projectiveCofibrations.cancel_right_of_respectsIso]
  exact projectiveCofibrations_initial_to_free (𝟙_ PointedSSet.{0}) 0

/-! ### Pullback-hom corners for cotensors -/

/-- Evaluating a spectral cotensor pullback-hom corner at level `n` yields a pointed simplicial
pullback-hom corner whose comparison map differs from `(evaluation n).map P.π` by the isomorphism
`(cotensorLevelIso L E n).inv`. -/
private noncomputable def cotensorPullbackObjObjLevel
    {K L : PointedSSet.{0}} {j : K ⟶ L} {E F : SymmetricSpectrum} {p : E ⟶ F}
    (P : cotensorBifunctor.PullbackObjObj j p) (n : ℕ) :
    MonoidalClosed.internalHom.PullbackObjObj j ((evaluation n).map p) where
  pt := (evaluation n).obj P.pt
  fst := (evaluation n).map P.fst ≫ (cotensorLevelIso K E n).hom
  snd := (evaluation n).map P.snd ≫ (cotensorLevelIso L F n).hom
  isPullback :=
    (P.isPullback.map (evaluation n)).of_iso
      (Iso.refl _) (cotensorLevelIso K E n) (cotensorLevelIso L F n)
      (cotensorLevelIso K F n)
      (Category.id_comp _).symm
      (Category.id_comp _).symm
      (cotensorLevelIso_hom_naturality K p n)
      (cotensorLevelIso_hom_naturality_left j F n)
  π := (cotensorLevelIso L E n).inv ≫ (evaluation n).map P.π
  π_fst := by
    let π' : (cotensor L).obj E ⟶ P.pt := P.π
    let fst' : P.pt ⟶ (cotensor K).obj E := P.fst
    let preE : (cotensor L).obj E ⟶ (cotensor K).obj E :=
      (MonoidalClosed.pre ((free 0).map j)).app E
    have h : (evaluation n).map π' ≫ (evaluation n).map fst' = (evaluation n).map preE :=
      ((evaluation n).map_comp π' fst').symm.trans (congrArg (evaluation n).map P.π_fst)
    calc ((cotensorLevelIso L E n).inv ≫ (evaluation n).map π') ≫
          ((evaluation n).map fst' ≫ (cotensorLevelIso K E n).hom)
      _ = (cotensorLevelIso L E n).inv ≫
            ((evaluation n).map π' ≫ (evaluation n).map fst') ≫
            (cotensorLevelIso K E n).hom := by
          simp only [Category.assoc]
      _ = (cotensorLevelIso L E n).inv ≫
            (evaluation n).map preE ≫ (cotensorLevelIso K E n).hom := by
          rw [h]
      _ = (MonoidalClosed.pre j).app ((evaluation n).obj E) :=
          (congrArg ((cotensorLevelIso L E n).inv ≫ ·)
            (cotensorLevelIso_hom_naturality_left j E n)).trans (Iso.inv_hom_id_assoc _ _)
  π_snd := by
    let π' : (cotensor L).obj E ⟶ P.pt := P.π
    let snd' : P.pt ⟶ (cotensor L).obj F := P.snd
    have h : (evaluation n).map π' ≫ (evaluation n).map snd' =
        (evaluation n).map ((cotensor L).map p) :=
      ((evaluation n).map_comp π' snd').symm.trans (congrArg (evaluation n).map P.π_snd)
    calc ((cotensorLevelIso L E n).inv ≫ (evaluation n).map π') ≫
          ((evaluation n).map snd' ≫ (cotensorLevelIso L F n).hom)
      _ = (cotensorLevelIso L E n).inv ≫
            ((evaluation n).map π' ≫ (evaluation n).map snd') ≫
            (cotensorLevelIso L F n).hom := by
          simp only [Category.assoc]
      _ = (cotensorLevelIso L E n).inv ≫
            (evaluation n).map ((cotensor L).map p) ≫ (cotensorLevelIso L F n).hom := by
          rw [h]
      _ = (CategoryTheory.ihom L).map ((evaluation n).map p) :=
          (congrArg ((cotensorLevelIso L E n).inv ≫ ·)
            (cotensorLevelIso_hom_naturality L p n)).trans (Iso.inv_hom_id_assoc _ _)

/-- The cotensor pullback-hom corner of a based monomorphism and a level fibration is a level
fibration. -/
lemma levelFibrations_cotensorBifunctor_pullbackObjObjπ
    {K L : PointedSSet.{0}} {j : K ⟶ L} [Mono j.right]
    {E F : SymmetricSpectrum} {p : E ⟶ F} (hp : levelFibrations p)
    (P : cotensorBifunctor.PullbackObjObj j p) :
    levelFibrations P.π := by
  rw [levelFibrations_iff]
  intro n
  have : Fibration ((evaluation n).map p).right := (levelFibrations_iff p).1 hp n
  have hP := PointedSSet.fibration_pullbackObjObjπ j ((evaluation n).map p)
    (cotensorPullbackObjObjLevel P n)
  have : IsIso ((cotensorLevelIso L E n).inv).right :=
    inferInstanceAs (IsIso (forgetBasepoint.map (cotensorLevelIso L E n).inv))
  rw [HomotopicalAlgebra.fibration_iff]
  exact ((fibrations SSet.{0}).cancel_left_of_respectsIso
    ((cotensorLevelIso L E n).inv).right (((evaluation n).map P.π).right)).1 hP.mem

/-- The cotensor pullback-hom corner of an anodyne based map and a level fibration is a level
trivial fibration. -/
lemma levelTrivialFibrations_cotensorBifunctor_pullbackObjObjπ_of_anodyne
    {K L : PointedSSet.{0}} {j : K ⟶ L} (hj : SSet.anodyneExtensions j.right)
    {E F : SymmetricSpectrum} {p : E ⟶ F} (hp : levelFibrations p)
    (P : cotensorBifunctor.PullbackObjObj j p) :
    levelTrivialFibrations P.π := by
  rw [levelTrivialFibrations_iff]
  intro n
  have : Fibration ((evaluation n).map p).right := (levelFibrations_iff p).1 hp n
  have hP := PointedSSet.rlp_monomorphisms_pullbackObjObjπ j ((evaluation n).map p) hj
    (cotensorPullbackObjObjLevel P n)
  have : IsIso ((cotensorLevelIso L E n).inv).right :=
    inferInstanceAs (IsIso (forgetBasepoint.map (cotensorLevelIso L E n).inv))
  exact ((monomorphisms SSet.{0}).rlp.cancel_left_of_respectsIso
    ((cotensorLevelIso L E n).inv).right (((evaluation n).map P.π).right)).1 hP

/-- The cotensor pullback-hom corner of a based monomorphism and a level trivial fibration is a
level trivial fibration. -/
lemma levelTrivialFibrations_cotensorBifunctor_pullbackObjObjπ_of_levelTrivialFibrations
    {K L : PointedSSet.{0}} {j : K ⟶ L} [Mono j.right]
    {E F : SymmetricSpectrum} {p : E ⟶ F} (hp : levelTrivialFibrations p)
    (P : cotensorBifunctor.PullbackObjObj j p) :
    levelTrivialFibrations P.π := by
  rw [levelTrivialFibrations_iff]
  intro n
  have hP := PointedSSet.rlp_monomorphisms_pullbackObjObjπ_of_rlp j ((evaluation n).map p)
    ((levelTrivialFibrations_iff p).1 hp n) (cotensorPullbackObjObjLevel P n)
  have : IsIso ((cotensorLevelIso L E n).inv).right :=
    inferInstanceAs (IsIso (forgetBasepoint.map (cotensorLevelIso L E n).inv))
  exact ((monomorphisms SSet.{0}).rlp.cancel_left_of_respectsIso
    ((cotensorLevelIso L E n).inv).right (((evaluation n).map P.π).right)).1 hP

/-- An unpointed simplicial cotensor pullback-hom corner is a pointed cotensor pullback-hom corner
for the induced map `g₊`. -/
private noncomputable def simplicialCotensorPullbackObjObjToPointed
    {K L : SSet.{0}} {g : K ⟶ L} {E F : SymmetricSpectrum} {p : E ⟶ F}
    (P : simplicialCotensor.PullbackObjObj g p) :
    cotensorBifunctor.PullbackObjObj (addBasepoint.map g) p where
  pt := P.pt
  fst := P.fst
  snd := P.snd
  isPullback := P.isPullback
  π := P.π
  π_fst := P.π_fst
  π_snd := P.π_snd

/-- The simplicial cotensor pullback-hom corner of a simplicial monomorphism and a level fibration
is a level fibration. -/
lemma levelFibrations_simplicialCotensor_pullbackObjObjπ
    {K L : SSet.{0}} {g : K ⟶ L} [Mono g]
    {E F : SymmetricSpectrum} {p : E ⟶ F} (hp : levelFibrations p)
    (P : simplicialCotensor.PullbackObjObj g p) :
    levelFibrations P.π :=
  levelFibrations_cotensorBifunctor_pullbackObjObjπ hp
    (simplicialCotensorPullbackObjObjToPointed P)

/-- The simplicial cotensor pullback-hom corner of an anodyne extension and a level fibration is a
level trivial fibration. -/
lemma levelTrivialFibrations_simplicialCotensor_pullbackObjObjπ_of_anodyne
    {K L : SSet.{0}} {g : K ⟶ L} (hg : SSet.anodyneExtensions g)
    {E F : SymmetricSpectrum} {p : E ⟶ F} (hp : levelFibrations p)
    (P : simplicialCotensor.PullbackObjObj g p) :
    levelTrivialFibrations P.π :=
  levelTrivialFibrations_cotensorBifunctor_pullbackObjObjπ_of_anodyne
    (addBasepoint_map_right_mem SSet.anodyneExtensions hg) hp
    (simplicialCotensorPullbackObjObjToPointed P)

/-- The simplicial cotensor pullback-hom corner of a simplicial monomorphism and a level trivial
fibration is a level trivial fibration. -/
lemma levelTrivialFibrations_simplicialCotensor_pullbackObjObjπ_of_levelTrivialFibrations
    {K L : SSet.{0}} {g : K ⟶ L} [Mono g]
    {E F : SymmetricSpectrum} {p : E ⟶ F} (hp : levelTrivialFibrations p)
    (P : simplicialCotensor.PullbackObjObj g p) :
    levelTrivialFibrations P.π :=
  levelTrivialFibrations_cotensorBifunctor_pullbackObjObjπ_of_levelTrivialFibrations hp
    (simplicialCotensorPullbackObjObjToPointed P)

/-- Point-set cotensoring by any pointed simplicial set preserves level fibrations. -/
lemma levelFibrations_cotensor_map (K : PointedSSet.{0}) {E F : SymmetricSpectrum} {p : E ⟶ F}
    (hp : levelFibrations p) : levelFibrations ((cotensor K).map p) := by
  let u : Under.mk (𝟙 (Δ[0] : SSet.{0})) ⟶ K := Under.homMk K.hom
  have : Mono u.right := SSet.stdSimplex.isTerminalObj₀.mono_from K.hom
  exact levelFibrations_cotensorBifunctor_pullbackObjObjπ hp
    (Functor.PullbackObjObj.ofIsInitial cotensorBifunctor u p Under.mkIdInitial)

/-- Point-set cotensoring by any pointed simplicial set preserves level trivial fibrations. -/
lemma levelTrivialFibrations_cotensor_map (K : PointedSSet.{0}) {E F : SymmetricSpectrum}
    {p : E ⟶ F} (hp : levelTrivialFibrations p) :
    levelTrivialFibrations ((cotensor K).map p) := by
  let u : Under.mk (𝟙 (Δ[0] : SSet.{0})) ⟶ K := Under.homMk K.hom
  have : Mono u.right := SSet.stdSimplex.isTerminalObj₀.mono_from K.hom
  exact levelTrivialFibrations_cotensorBifunctor_pullbackObjObjπ_of_levelTrivialFibrations hp
    (Functor.PullbackObjObj.ofIsInitial cotensorBifunctor u p Under.mkIdInitial)

/-- Precomposing a cotensor `E^L ⟶ E^K` along a based monomorphism `j : K ⟶ L` gives a level
fibration whenever every level of `E` is a Kan complex. -/
lemma levelFibrations_cotensorBifunctor_map_app {K L : PointedSSet.{0}} (j : K ⟶ L) [Mono j.right]
    (E : SymmetricSpectrum) [∀ n, SSet.KanComplex ((evaluation n).obj E).right] :
    levelFibrations ((cotensorBifunctor.map j.op).app E) :=
  levelFibrations_cotensorBifunctor_pullbackObjObjπ
    ((levelFibrations_terminal_from_iff E).2 inferInstance)
    (Functor.PullbackObjObj.ofIsTerminal cotensorBifunctor j (terminal.from E) terminalIsTerminal)

/-- Precomposing a cotensor `E^L ⟶ E^K` along an anodyne based map `j : K ⟶ L` gives a level
trivial fibration whenever every level of `E` is a Kan complex. -/
lemma levelTrivialFibrations_cotensorBifunctor_map_app {K L : PointedSSet.{0}} {j : K ⟶ L}
    (hj : SSet.anodyneExtensions j.right) (E : SymmetricSpectrum)
    [∀ n, SSet.KanComplex ((evaluation n).obj E).right] :
    levelTrivialFibrations ((cotensorBifunctor.map j.op).app E) :=
  levelTrivialFibrations_cotensorBifunctor_pullbackObjObjπ_of_anodyne hj
    ((levelFibrations_terminal_from_iff E).2 inferInstance)
    (Functor.PullbackObjObj.ofIsTerminal cotensorBifunctor j (terminal.from E) terminalIsTerminal)

/-- Level `n` of the cotensor `E^K` is a Kan complex whenever level `n` of `E` is a Kan
complex. -/
instance kanComplex_cotensor_level (K : PointedSSet.{0}) (E : SymmetricSpectrum) (n : ℕ)
    [SSet.KanComplex ((evaluation n).obj E).right] :
    SSet.KanComplex ((evaluation n).obj ((cotensor K).obj E)).right := by
  let e : ((evaluation n).obj ((cotensor K).obj E)).right ≅
      ((PointedSSet.ihom K).obj ((evaluation n).obj E)).right :=
    forgetBasepoint.mapIso (cotensorLevelIso K E n)
  have : Fibration e.hom :=
    (HomotopicalAlgebra.fibration_iff _).2 ((fibrations SSet.{0}).of_isIso e.hom)
  exact isFibrant_of_fibration e.hom

/-! ### Pushout-products for levelwise smash and simplicial tensors -/

/-- The pushout-product of a projective cofibration of symmetric spectra with a based monomorphism
of pointed simplicial sets is a projective cofibration. -/
lemma projectiveCofibrations_levelSmashBifunctor_pushoutObjObjι
    {A B : SymmetricSpectrum} {i : A ⟶ B} (hi : projectiveCofibrations i)
    {K L : PointedSSet.{0}} {j : K ⟶ L} [Mono j.right]
    (Q : levelSmashBifunctor.PushoutObjObj i j) :
    projectiveCofibrations Q.ι := by
  rw [projectiveCofibrations_iff]
  intro E F p hp
  let P := Functor.PullbackObjObj.ofHasPullback cotensorBifunctor j p
  change HasLiftingProperty Q.flip.ι p
  rw [levelSmashCotensorAdjunction₂.hasLiftingProperty_iff Q.flip P]
  exact (projectiveCofibrations_iff i).1 hi P.π
    (levelTrivialFibrations_cotensorBifunctor_pullbackObjObjπ_of_levelTrivialFibrations hp P)

/-- The pushout-product of a projective cofibration of symmetric spectra with an anodyne based map
lifts against all level fibrations. -/
lemma llp_levelFibrations_levelSmashBifunctor_pushoutObjObjι_of_anodyne
    {A B : SymmetricSpectrum} {i : A ⟶ B} (hi : projectiveCofibrations i)
    {K L : PointedSSet.{0}} {j : K ⟶ L} (hj : SSet.anodyneExtensions j.right)
    (Q : levelSmashBifunctor.PushoutObjObj i j) :
    levelFibrations.llp Q.ι := by
  intro E F p hp
  let P := Functor.PullbackObjObj.ofHasPullback cotensorBifunctor j p
  change HasLiftingProperty Q.flip.ι p
  rw [levelSmashCotensorAdjunction₂.hasLiftingProperty_iff Q.flip P]
  exact (projectiveCofibrations_iff i).1 hi P.π
    (levelTrivialFibrations_cotensorBifunctor_pullbackObjObjπ_of_anodyne hj hp P)

/-- The pushout-product of a spectrum map lifting against level fibrations with a based
monomorphism also lifts against all level fibrations. -/
lemma llp_levelFibrations_levelSmashBifunctor_pushoutObjObjι_of_llp
    {A B : SymmetricSpectrum} {i : A ⟶ B} (hi : levelFibrations.llp i)
    {K L : PointedSSet.{0}} {j : K ⟶ L} [Mono j.right]
    (Q : levelSmashBifunctor.PushoutObjObj i j) :
    levelFibrations.llp Q.ι := by
  intro E F p hp
  let P := Functor.PullbackObjObj.ofHasPullback cotensorBifunctor j p
  change HasLiftingProperty Q.flip.ι p
  rw [levelSmashCotensorAdjunction₂.hasLiftingProperty_iff Q.flip P]
  exact hi P.π (levelFibrations_cotensorBifunctor_pullbackObjObjπ hp P)

/-- The pushout-product of a simplicial monomorphism and a projective cofibration of symmetric
spectra is a projective cofibration. -/
lemma projectiveCofibrations_simplicialTensor_pushoutObjObjι
    {K L : SSet.{0}} {g : K ⟶ L} [Mono g]
    {A B : SymmetricSpectrum} {i : A ⟶ B} (hi : projectiveCofibrations i)
    (Q : simplicialTensor.PushoutObjObj g i) :
    projectiveCofibrations Q.ι := by
  rw [projectiveCofibrations_iff]
  intro E F p hp
  let P := Functor.PullbackObjObj.ofHasPullback simplicialCotensor g p
  rw [simplicialTensorCotensorAdjunction₂.hasLiftingProperty_iff Q P]
  exact (projectiveCofibrations_iff i).1 hi P.π
    (levelTrivialFibrations_simplicialCotensor_pullbackObjObjπ_of_levelTrivialFibrations hp P)

/-- The pushout-product of an anodyne extension and a projective cofibration of symmetric spectra
lifts against all level fibrations. -/
lemma llp_levelFibrations_simplicialTensor_pushoutObjObjι_of_anodyne
    {K L : SSet.{0}} {g : K ⟶ L} (hg : SSet.anodyneExtensions g)
    {A B : SymmetricSpectrum} {i : A ⟶ B} (hi : projectiveCofibrations i)
    (Q : simplicialTensor.PushoutObjObj g i) :
    levelFibrations.llp Q.ι := by
  intro E F p hp
  let P := Functor.PullbackObjObj.ofHasPullback simplicialCotensor g p
  rw [simplicialTensorCotensorAdjunction₂.hasLiftingProperty_iff Q P]
  exact (projectiveCofibrations_iff i).1 hi P.π
    (levelTrivialFibrations_simplicialCotensor_pullbackObjObjπ_of_anodyne hg hp P)

/-- The pushout-product of a simplicial monomorphism and a spectrum map lifting against level
fibrations also lifts against all level fibrations. -/
lemma llp_levelFibrations_simplicialTensor_pushoutObjObjι_of_llp
    {K L : SSet.{0}} {g : K ⟶ L} [Mono g]
    {A B : SymmetricSpectrum} {i : A ⟶ B} (hi : levelFibrations.llp i)
    (Q : simplicialTensor.PushoutObjObj g i) :
    levelFibrations.llp Q.ι := by
  intro E F p hp
  let P := Functor.PullbackObjObj.ofHasPullback simplicialCotensor g p
  rw [simplicialTensorCotensorAdjunction₂.hasLiftingProperty_iff Q P]
  exact hi P.π (levelFibrations_simplicialCotensor_pullbackObjObjπ hp P)

/-- Smashing with any pointed simplicial set preserves projective cofibrations of symmetric
spectra. -/
lemma projectiveCofibrations_levelSmashRight_map (K : PointedSSet.{0})
    {A B : SymmetricSpectrum} {i : A ⟶ B} (hi : projectiveCofibrations i) :
    projectiveCofibrations ((levelSmashRight K).map i) := by
  let u : Under.mk (𝟙 (Δ[0] : SSet.{0})) ⟶ K := Under.homMk K.hom
  have : Mono u.right := SSet.stdSimplex.isTerminalObj₀.mono_from K.hom
  exact projectiveCofibrations_levelSmashBifunctor_pushoutObjObjι hi
    (Functor.PushoutObjObj.ofIsInitialRight levelSmashBifunctor i u Under.mkIdInitial)

/-- Smashing with any pointed simplicial set preserves spectrum maps that lift against level
fibrations. -/
lemma llp_levelFibrations_levelSmashRight_map (K : PointedSSet.{0})
    {A B : SymmetricSpectrum} {i : A ⟶ B} (hi : levelFibrations.llp i) :
    levelFibrations.llp ((levelSmashRight K).map i) := by
  let u : Under.mk (𝟙 (Δ[0] : SSet.{0})) ⟶ K := Under.homMk K.hom
  have : Mono u.right := SSet.stdSimplex.isTerminalObj₀.mono_from K.hom
  exact llp_levelFibrations_levelSmashBifunctor_pushoutObjObjι_of_llp hi
    (Functor.PushoutObjObj.ofIsInitialRight levelSmashBifunctor i u Under.mkIdInitial)

/-- Smashing a projectively cofibrant spectrum `X` with a based monomorphism gives a projective
cofibration. -/
lemma projectiveCofibrations_levelSmash_map {X : SymmetricSpectrum}
    (hX : projectiveCofibrations (initial.to X)) {K L : PointedSSet.{0}} (j : K ⟶ L)
    [Mono j.right] : projectiveCofibrations ((levelSmash X).map j) :=
  projectiveCofibrations_levelSmashBifunctor_pushoutObjObjι hX
    (Functor.PushoutObjObj.ofIsInitialLeft levelSmashBifunctor (initial.to X) j initialIsInitial)

/-- Smashing a projectively cofibrant spectrum `X` with an anodyne based map gives a map lifting
against all level fibrations. -/
lemma llp_levelFibrations_levelSmash_map_of_anodyne {X : SymmetricSpectrum}
    (hX : projectiveCofibrations (initial.to X)) {K L : PointedSSet.{0}} {j : K ⟶ L}
    (hj : SSet.anodyneExtensions j.right) :
    levelFibrations.llp ((levelSmash X).map j) :=
  llp_levelFibrations_levelSmashBifunctor_pushoutObjObjι_of_anodyne hX hj
    (Functor.PushoutObjObj.ofIsInitialLeft levelSmashBifunctor (initial.to X) j initialIsInitial)

/-! ### Pullback-hom corners for mapping spaces -/

/-- The unpointed mapping-space pullback-hom corner `Map(B, E) ⟶ Map(A, E) ×[Map(A, F)] Map(B, F)`
of a projective cofibration `i : A ⟶ B` and a level fibration `p : E ⟶ F` is a Kan fibration. -/
lemma fibration_simplicialMappingSpace_pullbackObjObjπ
    {A B E F : SymmetricSpectrum} {i : A ⟶ B} {p : E ⟶ F}
    (hi : projectiveCofibrations i) (hp : levelFibrations p)
    (P : simplicialMappingSpace.PullbackObjObj i p) :
    Fibration P.π := by
  rw [SSet.modelCategoryQuillen.fibration_iff]
  intro K L g hg
  have hga : SSet.anodyneExtensions g := by
    rw [SSet.anodyneExtensions_eq_llp_rlp]
    exact le_llp_rlp _ _ hg
  let Q := Functor.PushoutObjObj.ofHasPushout simplicialTensor g i
  rw [← simplicialTensorMappingSpaceAdjunction₂.hasLiftingProperty_iff Q.flip P]
  exact llp_levelFibrations_simplicialTensor_pushoutObjObjι_of_anodyne hga hi Q p hp

/-- The unpointed mapping-space pullback-hom corner of a projective cofibration and a level
trivial fibration lifts against all monomorphisms of simplicial sets. -/
lemma rlp_monomorphisms_simplicialMappingSpace_pullbackObjObjπ_of_levelTrivialFibrations
    {A B E F : SymmetricSpectrum} {i : A ⟶ B} {p : E ⟶ F}
    (hi : projectiveCofibrations i) (hp : levelTrivialFibrations p)
    (P : simplicialMappingSpace.PullbackObjObj i p) :
    (monomorphisms SSet.{0}).rlp P.π := by
  intro K L g (_ : Mono g)
  let Q := Functor.PushoutObjObj.ofHasPushout simplicialTensor g i
  rw [← simplicialTensorMappingSpaceAdjunction₂.hasLiftingProperty_iff Q.flip P]
  exact (projectiveCofibrations_iff Q.ι).1
    (projectiveCofibrations_simplicialTensor_pushoutObjObjι hi Q) p hp

/-- The unpointed mapping-space pullback-hom corner of a spectrum map lifting against level
fibrations and a level fibration lifts against all monomorphisms of simplicial sets. -/
lemma rlp_monomorphisms_simplicialMappingSpace_pullbackObjObjπ_of_llp
    {A B E F : SymmetricSpectrum} {i : A ⟶ B} {p : E ⟶ F}
    (hi : levelFibrations.llp i) (hp : levelFibrations p)
    (P : simplicialMappingSpace.PullbackObjObj i p) :
    (monomorphisms SSet.{0}).rlp P.π := by
  intro K L g (_ : Mono g)
  let Q := Functor.PushoutObjObj.ofHasPushout simplicialTensor g i
  rw [← simplicialTensorMappingSpaceAdjunction₂.hasLiftingProperty_iff Q.flip P]
  exact llp_levelFibrations_simplicialTensor_pushoutObjObjι_of_llp hi Q p hp

/-- The unpointed mapping-space pullback-hom corner of a projective cofibration and a level
trivial fibration is a weak equivalence of simplicial sets. -/
lemma weakEquivalence_simplicialMappingSpace_pullbackObjObjπ_of_levelTrivialFibrations
    {A B E F : SymmetricSpectrum} {i : A ⟶ B} {p : E ⟶ F}
    (hi : projectiveCofibrations i) (hp : levelTrivialFibrations p)
    (P : simplicialMappingSpace.PullbackObjObj i p) :
    WeakEquivalence P.π :=
  weakEquivalence_of_rlp_monomorphisms
    (rlp_monomorphisms_simplicialMappingSpace_pullbackObjObjπ_of_levelTrivialFibrations hi hp P)

/-- The unpointed mapping-space pullback-hom corner of a spectrum map lifting against level
fibrations and a level fibration is a weak equivalence of simplicial sets. -/
lemma weakEquivalence_simplicialMappingSpace_pullbackObjObjπ_of_llp
    {A B E F : SymmetricSpectrum} {i : A ⟶ B} {p : E ⟶ F}
    (hi : levelFibrations.llp i) (hp : levelFibrations p)
    (P : simplicialMappingSpace.PullbackObjObj i p) :
    WeakEquivalence P.π :=
  weakEquivalence_of_rlp_monomorphisms
    (rlp_monomorphisms_simplicialMappingSpace_pullbackObjObjπ_of_llp hi hp P)

/-- Forgetting the basepoint sends a pointed mapping-space pullback-hom corner to an unpointed
mapping-space pullback-hom corner with the same underlying comparison map `P.π.right`. -/
private noncomputable def mappingSpacePullbackObjObjForget
    {A B E F : SymmetricSpectrum} {i : A ⟶ B} {p : E ⟶ F}
    (P : mappingSpaceBifunctor.PullbackObjObj i p) :
    simplicialMappingSpace.PullbackObjObj i p where
  pt := P.pt.right
  fst := P.fst.right
  snd := P.snd.right
  isPullback := by
    have : PreservesLimitsOfSize.{0, 0} forgetBasepoint.{0} :=
      addBasepointForgetAdjunction.rightAdjoint_preservesLimits
    exact P.isPullback.map forgetBasepoint.{0}
  π := P.π.right
  π_fst := congrArg Under.Hom.right P.π_fst
  π_snd := congrArg Under.Hom.right P.π_snd

/-- The pointed mapping-space pullback-hom corner of a projective cofibration and a level
fibration is a Kan fibration on underlying simplicial sets. -/
lemma fibration_mappingSpaceBifunctor_pullbackObjObjπ
    {A B E F : SymmetricSpectrum} {i : A ⟶ B} {p : E ⟶ F}
    (hi : projectiveCofibrations i) (hp : levelFibrations p)
    (P : mappingSpaceBifunctor.PullbackObjObj i p) :
    Fibration P.π.right :=
  fibration_simplicialMappingSpace_pullbackObjObjπ hi hp (mappingSpacePullbackObjObjForget P)

/-- The pointed mapping-space pullback-hom corner of a projective cofibration and a level trivial
fibration lifts against all monomorphisms on underlying simplicial sets. -/
lemma rlp_monomorphisms_mappingSpaceBifunctor_pullbackObjObjπ_of_levelTrivialFibrations
    {A B E F : SymmetricSpectrum} {i : A ⟶ B} {p : E ⟶ F}
    (hi : projectiveCofibrations i) (hp : levelTrivialFibrations p)
    (P : mappingSpaceBifunctor.PullbackObjObj i p) :
    (monomorphisms SSet.{0}).rlp P.π.right :=
  rlp_monomorphisms_simplicialMappingSpace_pullbackObjObjπ_of_levelTrivialFibrations hi hp
    (mappingSpacePullbackObjObjForget P)

/-- The pointed mapping-space pullback-hom corner of a spectrum map lifting against level
fibrations and a level fibration lifts against all monomorphisms on underlying simplicial sets. -/
lemma rlp_monomorphisms_mappingSpaceBifunctor_pullbackObjObjπ_of_llp
    {A B E F : SymmetricSpectrum} {i : A ⟶ B} {p : E ⟶ F}
    (hi : levelFibrations.llp i) (hp : levelFibrations p)
    (P : mappingSpaceBifunctor.PullbackObjObj i p) :
    (monomorphisms SSet.{0}).rlp P.π.right :=
  rlp_monomorphisms_simplicialMappingSpace_pullbackObjObjπ_of_llp hi hp
    (mappingSpacePullbackObjObjForget P)

/-- The pointed mapping-space pullback-hom corner of a projective cofibration and a level trivial
fibration is a weak equivalence on underlying simplicial sets. -/
lemma weakEquivalence_mappingSpaceBifunctor_pullbackObjObjπ_of_levelTrivialFibrations
    {A B E F : SymmetricSpectrum} {i : A ⟶ B} {p : E ⟶ F}
    (hi : projectiveCofibrations i) (hp : levelTrivialFibrations p)
    (P : mappingSpaceBifunctor.PullbackObjObj i p) :
    WeakEquivalence P.π.right :=
  weakEquivalence_simplicialMappingSpace_pullbackObjObjπ_of_levelTrivialFibrations hi hp
    (mappingSpacePullbackObjObjForget P)

/-- The pointed mapping-space pullback-hom corner of a spectrum map lifting against level
fibrations and a level fibration is a weak equivalence on underlying simplicial sets. -/
lemma weakEquivalence_mappingSpaceBifunctor_pullbackObjObjπ_of_llp
    {A B E F : SymmetricSpectrum} {i : A ⟶ B} {p : E ⟶ F}
    (hi : levelFibrations.llp i) (hp : levelFibrations p)
    (P : mappingSpaceBifunctor.PullbackObjObj i p) :
    WeakEquivalence P.π.right :=
  weakEquivalence_simplicialMappingSpace_pullbackObjObjπ_of_llp hi hp
    (mappingSpacePullbackObjObjForget P)

/-! ### Mapping spaces out of projectively cofibrant spectra and into Kan-level spectra -/

/-- For a projectively cofibrant spectrum `X`, postcomposition on `Map(X, -)` sends level
fibrations to Kan fibrations. -/
lemma fibration_mappingSpace_map {X E F : SymmetricSpectrum}
    (hX : projectiveCofibrations (initial.to X)) {p : E ⟶ F} (hp : levelFibrations p) :
    Fibration ((mappingSpace X).map p).right :=
  fibration_mappingSpaceBifunctor_pullbackObjObjπ hX hp
    (Functor.PullbackObjObj.ofIsInitial mappingSpaceBifunctor (initial.to X) p initialIsInitial)

/-- For a projectively cofibrant spectrum `X`, postcomposition on `Map(X, -)` sends level trivial
fibrations to maps lifting against all monomorphisms of simplicial sets. -/
lemma rlp_monomorphisms_mappingSpace_map {X E F : SymmetricSpectrum}
    (hX : projectiveCofibrations (initial.to X)) {p : E ⟶ F} (hp : levelTrivialFibrations p) :
    (monomorphisms SSet.{0}).rlp ((mappingSpace X).map p).right :=
  rlp_monomorphisms_mappingSpaceBifunctor_pullbackObjObjπ_of_levelTrivialFibrations hX hp
    (Functor.PullbackObjObj.ofIsInitial mappingSpaceBifunctor (initial.to X) p initialIsInitial)

/-- For a projectively cofibrant spectrum `X`, postcomposition on `Map(X, -)` sends level trivial
fibrations to weak equivalences of simplicial sets. -/
lemma weakEquivalence_mappingSpace_map {X E F : SymmetricSpectrum}
    (hX : projectiveCofibrations (initial.to X)) {p : E ⟶ F} (hp : levelTrivialFibrations p) :
    WeakEquivalence ((mappingSpace X).map p).right :=
  weakEquivalence_of_rlp_monomorphisms (rlp_monomorphisms_mappingSpace_map hX hp)

/-- Whenever `X` is projectively cofibrant and every level of `E` is a Kan complex (in particular,
whenever `E` is an Ω-spectrum), the mapping space `Map(X, E)` is a Kan complex. -/
lemma kanComplex_mappingSpace {X E : SymmetricSpectrum}
    (hX : projectiveCofibrations (initial.to X))
    [∀ n, SSet.KanComplex ((evaluation n).obj E).right] :
    SSet.KanComplex ((mappingSpace X).obj E).right := by
  have : Fibration ((simplicialMappingSpace.obj (op X)).map (terminal.from E)) :=
    fibration_mappingSpace_map hX ((levelFibrations_terminal_from_iff E).2 inferInstance)
  let hT := terminalIsTerminal.isTerminalObj (simplicialMappingSpace.obj (op X))
    (⊤_ SymmetricSpectrum)
  exact (isFibrant_iff_of_isTerminal
    ((simplicialMappingSpace.obj (op X)).map (terminal.from E)) hT).2 inferInstance

/-- Precomposition `Map(B, E) ⟶ Map(A, E)` along a projective cofibration `i : A ⟶ B` is a Kan
fibration whenever every level of `E` is a Kan complex. -/
lemma fibration_mappingSpaceBifunctor_map_app {A B E : SymmetricSpectrum} {i : A ⟶ B}
    (hi : projectiveCofibrations i)
    [∀ n, SSet.KanComplex ((evaluation n).obj E).right] :
    Fibration ((mappingSpaceBifunctor.map i.op).app E).right :=
  fibration_mappingSpaceBifunctor_pullbackObjObjπ hi
    ((levelFibrations_terminal_from_iff E).2 inferInstance)
    (Functor.PullbackObjObj.ofIsTerminal mappingSpaceBifunctor i (terminal.from E)
      terminalIsTerminal)

/-- Precomposition `Map(B, E) ⟶ Map(A, E)` along a map `i : A ⟶ B` lifting against level
fibrations lifts against all monomorphisms whenever every level of `E` is a Kan complex. -/
lemma rlp_monomorphisms_mappingSpaceBifunctor_map_app {A B E : SymmetricSpectrum} {i : A ⟶ B}
    (hi : levelFibrations.llp i)
    [∀ n, SSet.KanComplex ((evaluation n).obj E).right] :
    (monomorphisms SSet.{0}).rlp ((mappingSpaceBifunctor.map i.op).app E).right :=
  rlp_monomorphisms_mappingSpaceBifunctor_pullbackObjObjπ_of_llp hi
    ((levelFibrations_terminal_from_iff E).2 inferInstance)
    (Functor.PullbackObjObj.ofIsTerminal mappingSpaceBifunctor i (terminal.from E)
      terminalIsTerminal)

/-- Precomposition `Map(B, E) ⟶ Map(A, E)` along a map `i : A ⟶ B` lifting against level
fibrations is a weak equivalence of simplicial sets whenever every level of `E` is a Kan
complex. -/
lemma weakEquivalence_mappingSpaceBifunctor_map_app {A B E : SymmetricSpectrum} {i : A ⟶ B}
    (hi : levelFibrations.llp i)
    [∀ n, SSet.KanComplex ((evaluation n).obj E).right] :
    WeakEquivalence ((mappingSpaceBifunctor.map i.op).app E).right :=
  weakEquivalence_of_rlp_monomorphisms (rlp_monomorphisms_mappingSpaceBifunctor_map_app hi)

end TauCeti.SymmetricSpectrum

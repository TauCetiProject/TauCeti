/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialSet.Factorization
public import TauCeti.AlgebraicTopology.SimplicialSet.PrismRealization
public import TauCeti.AlgebraicTopology.Spectra.Colimits
public import TauCeti.AlgebraicTopology.Spectra.Limits
public import TauCeti.AlgebraicTopology.Spectra.Suspension
public import TauCeti.CategoryTheory.LiftingProperties.Under
public import TauCeti.CategoryTheory.MorphismProperty.LiftingProperty
public import Mathlib.CategoryTheory.Presentable.Finite

import Mathlib.AlgebraicTopology.SimplicialSet.Presentable

/-!
# The level projective weak factorization systems of symmetric spectra

A map of symmetric spectra is a *level fibration* when its underlying map of simplicial sets in
every level is a Kan fibration, and a *level trivial fibration* when every level has the right
lifting property against all monomorphisms. The *projective cofibrations* are the maps with the
left lifting property against the level trivial fibrations.

Both right classes are detected by free cells. Write `F_n` for the free symmetric spectrum on a
pointed simplicial set in level `n` and `K₊` for `K` with a disjoint basepoint. The functor
`K ↦ F_n (K₊)` is left adjoint to the underlying simplicial set of level `n`, so a map has the
right lifting property against `F_n (i₊)` exactly when its level `n` has the right lifting
property against `i` (`SymmetricSpectrum.rlp_freeCells`). Taking for `i` the boundary inclusions
`∂Δ[m] ⟶ Δ[m]`, respectively the horn inclusions `Λ[m, k] ⟶ Δ[m]`, recovers the level trivial
fibrations, respectively the level fibrations. The domains of these free cells are finitely
presentable, since `F_n (K₊)` is the image of a finite simplicial set under a left adjoint whose
right adjoint preserves filtered colimits, so both families admit the small object argument. This
gives the two weak factorization systems of the level projective model structure of Hovey,
Shipley and Smith:

* projective cofibrations and level trivial fibrations;
* the maps lifting against level fibrations, and level fibrations.

The left classes are retracts of relative cell complexes built from free cells. Every level
trivial fibration is a level fibration and a *level equivalence*, a map whose levels are weak
equivalences of simplicial sets. The converse, and the identification of the second left class
with the projective cofibrations that are level equivalences, rest on the Kan–Quillen model
structure on simplicial sets and are not proved here.

The constructions reuse Mathlib's small object argument by Joël Riou, together with its
transfer of presentability along adjunctions, and follow the corresponding weak factorization
systems on simplicial sets.

## Main definitions

* `SymmetricSpectrum.levelwise W`: the maps whose underlying levels lie in `W`.
* `SymmetricSpectrum.freeCells T`: the free cells `F_n (i₊)` on the maps `i` of `T`.
* `SymmetricSpectrum.levelFibrations`, `SymmetricSpectrum.levelTrivialFibrations`,
  `SymmetricSpectrum.levelEquivalences` and `SymmetricSpectrum.projectiveCofibrations`.

## Main statements

* `SymmetricSpectrum.rlp_freeCells`: lifting against free cells is detected levelwise.
* `SymmetricSpectrum.isWeakFactorizationSystem_projectiveCofibrations` and
  `SymmetricSpectrum.isWeakFactorizationSystem_levelFibrations`: the two weak factorization
  systems, with functorial factorizations.
* `SymmetricSpectrum.levelTrivialFibrations_le_levelFibrations` and
  `SymmetricSpectrum.levelTrivialFibrations_le_levelEquivalences`: level trivial fibrations are
  level fibrations and level equivalences.
* `SymmetricSpectrum.levelFibrations_terminal_from_iff`: `E ⟶ ⊤` is a level fibration precisely
  when every level of `E` is a Kan complex.
* `SymmetricSpectrum.free_map_mem_projectiveCofibrations`,
  `SymmetricSpectrum.free_map_mem_llp_levelFibrations`,
  `SymmetricSpectrum.projectiveCofibrations_initial_to_free`, and
  `SymmetricSpectrum.projectiveCofibrations_initial_to_unit`: free maps on based monomorphisms and
  anodyne maps, and projective cofibrancy of all free spectra `F_n K` and the sphere spectrum.

## References

* M. Hovey, B. Shipley and J. Smith, *Symmetric spectra*, J. Amer. Math. Soc. 13 (2000),
  Section 5.1.
* M. Hovey, *Model categories*, Mathematical Surveys and Monographs 63, American Mathematical
  Society, 1999, Section 2.1.
-/

public section

open CategoryTheory MonoidalCategory MorphismProperty HomotopicalAlgebra Limits
open SSet.modelCategoryQuillen
open scoped Simplicial

namespace TauCeti.SymmetricSpectrum

open PointedSSet

/-- The maps of symmetric spectra whose underlying map of simplicial sets lies in `W` in every
level. -/
def levelwise (W : MorphismProperty SSet.{0}) : MorphismProperty SymmetricSpectrum :=
  ⨅ n, W.inverseImage (evaluation n ⋙ forgetBasepoint)

@[simp]
lemma levelwise_iff (W : MorphismProperty SSet.{0}) {E E' : SymmetricSpectrum} (f : E ⟶ E') :
    levelwise W f ↔ ∀ n, W ((evaluation n).map f).right := by
  simp [levelwise]

/-- `levelwise` is monotone in the class of maps of simplicial sets. -/
lemma levelwise_monotone : Monotone levelwise :=
  fun _ _ h _ _ f hf ↦ (levelwise_iff _ f).2 fun n ↦ h _ ((levelwise_iff _ f).1 hf n)

instance (W : MorphismProperty SSet.{0}) [W.RespectsIso] : (levelwise W).RespectsIso := by
  rw [levelwise]
  infer_instance

instance (W : MorphismProperty SSet.{0}) [W.IsMultiplicative] :
    (levelwise W).IsMultiplicative := by
  rw [levelwise]
  infer_instance

instance (W : MorphismProperty SSet.{0}) [W.HasTwoOutOfThreeProperty] :
    (levelwise W).HasTwoOutOfThreeProperty where
  comp_mem f g hf hg := by
    simp only [levelwise, iInf_iff] at hf hg ⊢
    exact fun n ↦ (W.inverseImage _).comp_mem f g (hf n) (hg n)
  of_postcomp f g hg hfg := by
    simp only [levelwise, iInf_iff] at hg hfg ⊢
    exact fun n ↦ (W.inverseImage _).of_postcomp f g (hg n) (hfg n)
  of_precomp f g hf hfg := by
    simp only [levelwise, iInf_iff] at hf hfg ⊢
    exact fun n ↦ (W.inverseImage _).of_precomp f g (hf n) (hfg n)

instance (W : MorphismProperty SSet.{0}) [W.IsStableUnderRetracts] :
    (levelwise W).IsStableUnderRetracts where
  of_retract h hg := by
    simp only [levelwise, iInf_iff] at hg ⊢
    exact fun n ↦ (W.inverseImage _).of_retract h (hg n)

/-- The free cells `F_n (i₊) : F_n (A₊) ⟶ F_n (B₊)` on the maps `i : A ⟶ B` of `T`, in all
levels `n`. -/
def freeCells (T : MorphismProperty SSet.{0}) : MorphismProperty SymmetricSpectrum :=
  ⨆ n, T.strictMap (addBasepoint ⋙ free n)

/-- A map is a free cell on `T` exactly when it is the image of a map of `T` under
`K ↦ F_n (K₊)` for some level `n`. -/
lemma freeCells_iff {T : MorphismProperty SSet.{0}} {E E' : SymmetricSpectrum} (f : E ⟶ E') :
    freeCells T f ↔ ∃ n, T.strictMap (addBasepoint ⋙ free n) f := by
  simp only [freeCells, iSup_iff]

/-- The free cell `F_n (i₊)` on a map `i` of `T`. -/
lemma map_mem_freeCells {T : MorphismProperty SSet.{0}} {A B : SSet.{0}} {i : A ⟶ B} (hi : T i)
    (n : ℕ) : freeCells T ((free n).map (addBasepoint.map i)) :=
  (freeCells_iff _).2 ⟨n, ⟨hi⟩⟩

/-- A map has the right lifting property against the free cells on `T` exactly when the
underlying map of each of its levels has the right lifting property against `T`. -/
lemma rlp_freeCells (T : MorphismProperty SSet.{0}) : (freeCells T).rlp = levelwise T.rlp := by
  simp only [freeCells, rlp_iSup, levelwise, (freeAddBasepointAdjunction _).rlp_strictMap]

instance (T : MorphismProperty SSet.{0}) [IsSmall.{0} T] : IsSmall.{0} (freeCells T) := by
  dsimp only [freeCells]
  infer_instance

section SmallObject

attribute [local instance] Cardinal.fact_isRegular_aleph0
  Cardinal.orderBotAleph0OrdToType

/-- Free cells on maps with finitely presentable domains admit the small object argument with
countable cell attachments. -/
lemma isCardinalForSmallObjectArgument_freeCells (T : MorphismProperty SSet.{0}) [IsSmall.{0} T]
    (hT : ∀ ⦃A B : SSet.{0}⦄ (i : A ⟶ B), T i → IsFinitelyPresentable.{0} A) :
    IsCardinalForSmallObjectArgument (freeCells T) Cardinal.aleph0.{0} where
  preservesColimit {A B X Y} i hi f hf := by
    have : IsFinitelyPresentable.{0} A := by
      obtain ⟨n, ⟨hT'⟩⟩ := (freeCells_iff _).1 hi
      have := hT _ hT'
      exact isFinitelyPresentable_free_obj_addBasepoint n _
    infer_instance

/-- Free cells on maps with finitely presentable domains admit the small object argument. -/
lemma hasSmallObjectArgument_freeCells (T : MorphismProperty SSet.{0}) [IsSmall.{0} T]
    (hT : ∀ ⦃A B : SSet.{0}⦄ (i : A ⟶ B), T i → IsFinitelyPresentable.{0} A) :
    HasSmallObjectArgument.{0} (freeCells T) :=
  have := isCardinalForSmallObjectArgument_freeCells T hT
  ⟨.aleph0, inferInstance, inferInstance, inferInstance⟩

/-- The free cells on the boundary inclusions admit the small object argument. -/
instance hasSmallObjectArgument_freeCells_I : HasSmallObjectArgument.{0} (freeCells I.{0}) :=
  hasSmallObjectArgument_freeCells _ (by
    rintro _ _ _ ⟨n⟩
    infer_instance)

/-- The free cells on the horn inclusions admit the small object argument. -/
instance hasSmallObjectArgument_freeCells_J : HasSmallObjectArgument.{0} (freeCells J.{0}) :=
  hasSmallObjectArgument_freeCells _ (by
    intro A B i hi
    simp only [J, iSup_iff] at hi
    obtain ⟨n, ⟨i⟩⟩ := hi
    infer_instance)

end SmallObject

/-- Level fibrations: the maps whose underlying map in every level is a Kan fibration. -/
def levelFibrations : MorphismProperty SymmetricSpectrum :=
  levelwise (fibrations SSet.{0})

/-- Level trivial fibrations: the maps whose underlying map in every level has the right lifting
property against all monomorphisms of simplicial sets. -/
def levelTrivialFibrations : MorphismProperty SymmetricSpectrum :=
  levelwise (monomorphisms SSet.{0}).rlp

/-- Level equivalences: the maps whose underlying map in every level is a weak equivalence of
simplicial sets, that is, its geometric realization is a weak homotopy equivalence. -/
def levelEquivalences : MorphismProperty SymmetricSpectrum :=
  levelwise (weakEquivalences SSet.{0})

/-- Projective cofibrations: the maps with the left lifting property against all level trivial
fibrations. -/
def projectiveCofibrations : MorphismProperty SymmetricSpectrum :=
  levelTrivialFibrations.llp

/-- A map is a projective cofibration exactly when it lifts on the left against all level trivial
fibrations. -/
lemma projectiveCofibrations_iff {E E' : SymmetricSpectrum} (f : E ⟶ E') :
    projectiveCofibrations f ↔ levelTrivialFibrations.llp f :=
  Iff.rfl

/-- A map is a level fibration exactly when its underlying map in every level is a Kan
fibration. -/
@[simp]
lemma levelFibrations_iff {E E' : SymmetricSpectrum} (f : E ⟶ E') :
    levelFibrations f ↔ ∀ n, Fibration ((evaluation n).map f).right := by
  simp only [levelFibrations, levelwise_iff, HomotopicalAlgebra.fibration_iff]

/-- A map is a level trivial fibration exactly when its underlying map in every level lifts
against all monomorphisms. -/
@[simp]
lemma levelTrivialFibrations_iff {E E' : SymmetricSpectrum} (f : E ⟶ E') :
    levelTrivialFibrations f ↔ ∀ n, (monomorphisms SSet.{0}).rlp ((evaluation n).map f).right :=
  levelwise_iff _ f

/-- A map is a level equivalence exactly when its underlying map in every level is a weak
equivalence of simplicial sets. -/
@[simp]
lemma levelEquivalences_iff {E E' : SymmetricSpectrum} (f : E ⟶ E') :
    levelEquivalences f ↔ ∀ n, WeakEquivalence ((evaluation n).map f).right := by
  simp only [levelEquivalences, levelwise_iff, HomotopicalAlgebra.weakEquivalence_iff]

/-- The level trivial fibrations are the maps lifting against the free cells on the boundary
inclusions. -/
lemma rlp_freeCells_I : (freeCells I.{0}).rlp = levelTrivialFibrations := by
  rw [rlp_freeCells, levelTrivialFibrations, SSet.rlp_monomorphisms]

/-- The level fibrations are the maps lifting against the free cells on the horn inclusions. -/
lemma rlp_freeCells_J : (freeCells J.{0}).rlp = levelFibrations := by
  rw [rlp_freeCells, levelFibrations, fibrations_eq]

/-- The projective cofibrations are generated by the free cells on the boundary inclusions. -/
lemma llp_rlp_freeCells_I : (freeCells I.{0}).rlp.llp = projectiveCofibrations := by
  rw [rlp_freeCells_I, projectiveCofibrations]

instance : levelFibrations.IsMultiplicative := by
  rw [← rlp_freeCells_J]
  infer_instance

instance : levelFibrations.IsStableUnderRetracts := by
  rw [← rlp_freeCells_J]
  infer_instance

instance : levelFibrations.IsStableUnderBaseChange := by
  rw [← rlp_freeCells_J]
  infer_instance

instance : levelTrivialFibrations.IsMultiplicative := by
  rw [← rlp_freeCells_I]
  infer_instance

instance : levelTrivialFibrations.IsStableUnderRetracts := by
  rw [← rlp_freeCells_I]
  infer_instance

instance : levelTrivialFibrations.IsStableUnderBaseChange := by
  rw [← rlp_freeCells_I]
  infer_instance

instance : levelEquivalences.RespectsIso := by
  rw [levelEquivalences]
  infer_instance

instance : levelEquivalences.IsMultiplicative := by
  rw [levelEquivalences]
  infer_instance

instance : levelEquivalences.HasTwoOutOfThreeProperty := by
  rw [levelEquivalences]
  infer_instance

instance : levelEquivalences.IsStableUnderRetracts := by
  rw [levelEquivalences]
  infer_instance

instance : projectiveCofibrations.IsMultiplicative := by
  rw [projectiveCofibrations]
  infer_instance

instance : projectiveCofibrations.IsStableUnderRetracts := by
  rw [projectiveCofibrations]
  infer_instance

instance : projectiveCofibrations.IsStableUnderCobaseChange := by
  rw [projectiveCofibrations]
  infer_instance

/-- Projective cofibrations are the retracts of relative cell complexes built from free cells on
the boundary inclusions. -/
lemma projectiveCofibrations_eq_retracts_transfiniteCompositions :
    projectiveCofibrations =
      (transfiniteCompositions.{0} (coproducts.{0} (freeCells I.{0})).pushouts).retracts := by
  rw [← llp_rlp_freeCells_I, llp_rlp_of_hasSmallObjectArgument]

/-- The maps lifting against level fibrations are the retracts of relative cell complexes built
from free cells on the horn inclusions. -/
lemma llp_levelFibrations_eq_retracts_transfiniteCompositions :
    levelFibrations.llp =
      (transfiniteCompositions.{0} (coproducts.{0} (freeCells J.{0})).pushouts).retracts := by
  rw [← rlp_freeCells_J, llp_rlp_of_hasSmallObjectArgument]

/-- Every map of symmetric spectra factors functorially as a projective cofibration followed by
a level trivial fibration. -/
instance hasFunctorialFactorization_projectiveCofibrations :
    HasFunctorialFactorization projectiveCofibrations levelTrivialFibrations := by
  rw [← llp_rlp_freeCells_I, ← rlp_freeCells_I]
  infer_instance

/-- Projective cofibrations and level trivial fibrations form a weak factorization system. -/
instance isWeakFactorizationSystem_projectiveCofibrations :
    IsWeakFactorizationSystem projectiveCofibrations levelTrivialFibrations where
  rlp := by rw [← llp_rlp_freeCells_I, rlp_llp_rlp, rlp_freeCells_I]
  llp := rfl

/-- Every map of symmetric spectra factors functorially as a map lifting against all level
fibrations followed by a level fibration. -/
instance hasFunctorialFactorization_levelFibrations :
    HasFunctorialFactorization levelFibrations.llp levelFibrations := by
  rw [← rlp_freeCells_J]
  infer_instance

/-- The maps lifting against level fibrations and the level fibrations form a weak factorization
system. -/
instance isWeakFactorizationSystem_levelFibrations :
    IsWeakFactorizationSystem levelFibrations.llp levelFibrations where
  rlp := by rw [← rlp_freeCells_J, rlp_llp_rlp]
  llp := rfl

/-- Level trivial fibrations are level fibrations. -/
lemma levelTrivialFibrations_le_levelFibrations : levelTrivialFibrations ≤ levelFibrations := by
  rw [levelTrivialFibrations, levelFibrations, fibrations_eq]
  exact levelwise_monotone (antitone_rlp J_le_monomorphisms)

/-- Level trivial fibrations are level equivalences. -/
lemma levelTrivialFibrations_le_levelEquivalences : levelTrivialFibrations ≤ levelEquivalences :=
  levelwise_monotone fun _ _ _ hp ↦
    have := weakEquivalence_of_rlp_monomorphisms hp
    mem_weakEquivalences _

/-- The maps lifting against level fibrations are projective cofibrations. -/
lemma llp_levelFibrations_le_projectiveCofibrations :
    levelFibrations.llp ≤ projectiveCofibrations :=
  antitone_llp levelTrivialFibrations_le_levelFibrations

/-- A symmetric spectrum `E` has `E ⟶ ⊤` in `levelFibrations` if and only if every level `E_n` is
a Kan complex. -/
lemma levelFibrations_terminal_from_iff (E : SymmetricSpectrum) :
    levelFibrations (terminal.from E) ↔
      ∀ n, SSet.KanComplex ((evaluation n).obj E).right := by
  rw [levelFibrations_iff]
  refine forall_congr' fun n ↦ ?_
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

end TauCeti.SymmetricSpectrum

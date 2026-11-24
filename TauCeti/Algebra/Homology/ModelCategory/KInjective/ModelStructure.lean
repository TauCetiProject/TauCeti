/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.ModelCategory.Basic
public import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant
public import TauCeti.Algebra.Homology.ModelCategory.KInjective.Resolution

import Mathlib.Algebra.Homology.Factorizations.CM5b
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import TauCeti.Algebra.Homology.HomologySequenceLemmas
import TauCeti.Algebra.Homology.Homotopy
import TauCeti.Algebra.Homology.HomotopyCofiber
import TauCeti.Algebra.Homology.HomotopyCategory.KInjective
import TauCeti.CategoryTheory.Limits.Shapes.Pullback.Kernel

/-!
# The injective model structure on unbounded cochain complexes

Let `C` be a Grothendieck abelian category. The category of unbounded cochain complexes in `C`
carries the *injective model structure*: the weak equivalences are the quasi-isomorphisms, the
cofibrations are the monomorphisms, and the fibrations are the morphisms with the right lifting
property with respect to the monomorphic quasi-isomorphisms. Concretely, a morphism is a
fibration exactly when it is degreewise an epimorphism with an injective kernel and its kernel is
K-injective (`CochainComplex.modelCategoryInjective.fibration_iff`), and an object is fibrant
exactly when it is a K-injective complex of injective objects
(`CochainComplex.modelCategoryInjective.isFibrant_iff`). Every object is cofibrant.

As in Mathlib's model structure on bounded below complexes
(`CochainComplex.Plus.modelCategoryQuillen`), the `ModelCategory` instance and the classes of
morphisms are scoped, here in the namespace `CochainComplex.modelCategoryInjective`. No
boundedness assumption is made: the fibrant objects need not be bounded below, and the
factorization into a trivial cofibration followed by a fibration comes from the small object
argument (`CochainComplex.monoQuasiIsoMapFactorizationDataRlp`).

## Main results

All in the namespace `CochainComplex.modelCategoryInjective`:

* `instModelCategory`: the injective model structure on `CochainComplex C ℤ` for a Grothendieck
  abelian category `C`, for instance sheaves of modules over a sheaf of rings on a small site.
* `trivialFibrations_eq`: the trivial fibrations are exactly the morphisms with the right lifting
  property with respect to all monomorphisms. This holds in any abelian category.
* `exists_hasSmallObjectArgument_rlp_eq_trivialFibrations_and_fibrations`: the model structure is
  cofibrantly generated, by families of cofibrations and of trivial cofibrations to which the
  small object argument applies.

## References

* J. Lurie, *Higher Algebra*, Proposition 1.3.5.3.
* [Stacks: Theorem 079P](https://stacks.math.columbia.edu/tag/079P).
* Mathlib's model structure on bounded below complexes
  `CochainComplex.Plus.modelCategoryQuillen` in
  `Mathlib.Algebra.Homology.ModelCategory.Injective`, by Joël Riou, whose structure is followed
  here.
* The constructions `CochainComplex.cm5b.i` and `CochainComplex.cm5b.p` in
  `Mathlib.Algebra.Homology.Factorizations.CM5b`, by Joël Riou, which are reused here for the
  factorization into a cofibration followed by a trivial fibration; they need no boundedness
  assumption.
-/

public section

universe w v u

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra ZeroObject

namespace CochainComplex.modelCategoryInjective

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The weak equivalences of the injective model structure are the quasi-isomorphisms. -/
scoped instance instCategoryWithWeakEquivalences :
    CategoryWithWeakEquivalences (CochainComplex C ℤ) where
  weakEquivalences := HomologicalComplex.quasiIso C (.up ℤ)

/-- The cofibrations of the injective model structure are the monomorphisms. -/
scoped instance instCategoryWithCofibrations : CategoryWithCofibrations (CochainComplex C ℤ) where
  cofibrations := monomorphisms _

/-- The fibrations of the injective model structure are the morphisms with the right lifting
property with respect to the monomorphic quasi-isomorphisms. -/
scoped instance instCategoryWithFibrations : CategoryWithFibrations (CochainComplex C ℤ) where
  fibrations := (monomorphisms _ ⊓ HomologicalComplex.quasiIso C (.up ℤ)).rlp

/-- The weak equivalences of the injective model structure are the quasi-isomorphisms. -/
lemma weakEquivalences_eq :
    weakEquivalences (CochainComplex C ℤ) = HomologicalComplex.quasiIso C (.up ℤ) := (rfl)

/-- The cofibrations of the injective model structure are the monomorphisms. -/
lemma cofibrations_eq : cofibrations (CochainComplex C ℤ) = monomorphisms _ := (rfl)

/-- The fibrations of the injective model structure are the morphisms with the right lifting
property with respect to the monomorphic quasi-isomorphisms. -/
lemma fibrations_eq :
    fibrations (CochainComplex C ℤ) =
      (monomorphisms _ ⊓ HomologicalComplex.quasiIso C (.up ℤ)).rlp := (rfl)

/-- The trivial cofibrations of the injective model structure are the monomorphic
quasi-isomorphisms. -/
lemma trivialCofibrations_eq :
    trivialCofibrations (CochainComplex C ℤ) =
      monomorphisms _ ⊓ HomologicalComplex.quasiIso C (.up ℤ) := (rfl)

/-- A morphism is a weak equivalence of the injective model structure if and only if it is a
quasi-isomorphism. -/
lemma weakEquivalence_iff {X Y : CochainComplex C ℤ} (f : X ⟶ Y) :
    WeakEquivalence f ↔ QuasiIso f := by
  rw [HomotopicalAlgebra.weakEquivalence_iff, weakEquivalences_eq,
    HomologicalComplex.mem_quasiIso_iff]

/-- A morphism is a cofibration of the injective model structure if and only if it is a
monomorphism. -/
lemma cofibration_iff {X Y : CochainComplex C ℤ} (f : X ⟶ Y) : Cofibration f ↔ Mono f := by
  rw [HomotopicalAlgebra.cofibration_iff, cofibrations_eq, monomorphisms.iff]

/-- A morphism of cochain complexes is a fibration of the injective model structure if and only
if it is degreewise an epimorphism with an injective kernel and its kernel is K-injective. -/
lemma fibration_iff {X Y : CochainComplex C ℤ} (f : X ⟶ Y) :
    Fibration f ↔ degreewiseEpiWithInjectiveKernel f ∧ (kernel f).IsKInjective := by
  rw [HomotopicalAlgebra.fibration_iff, fibrations_eq, rlp_monomorphisms_inf_quasiIso_iff]

/-- A cochain complex is fibrant for the injective model structure if and only if it is a
K-injective complex of injective objects. -/
lemma isFibrant_iff (X : CochainComplex C ℤ) :
    IsFibrant X ↔ (∀ n, Injective (X.X n)) ∧ X.IsKInjective := by
  rw [HomotopicalAlgebra.isFibrant_iff, HomotopicalAlgebra.fibration_iff, fibrations_eq,
    rlp_monomorphisms_inf_quasiIso_iff_of_isZero _
      ((isZero_zero _).of_iso (terminalIsoIsTerminal HasZeroObject.zeroIsTerminal))]

scoped instance {X Y : CochainComplex C ℤ} (f : X ⟶ Y) [Cofibration f] : Mono f :=
  (cofibration_iff f).1 ‹_›

scoped instance {X Y : CochainComplex C ℤ} (f : X ⟶ Y) [WeakEquivalence f] : QuasiIso f :=
  (weakEquivalence_iff f).1 ‹_›

/-- Every cochain complex is cofibrant for the injective model structure. -/
scoped instance (X : CochainComplex C ℤ) : IsCofibrant X := by
  rw [isCofibrant_iff, cofibration_iff]
  infer_instance

scoped instance : (weakEquivalences (CochainComplex C ℤ)).HasTwoOutOfThreeProperty :=
  inferInstanceAs (HomologicalComplex.quasiIso C (.up ℤ)).HasTwoOutOfThreeProperty

scoped instance : (weakEquivalences (CochainComplex C ℤ)).IsStableUnderRetracts :=
  inferInstanceAs (HomologicalComplex.quasiIso C (.up ℤ)).IsStableUnderRetracts

scoped instance : (cofibrations (CochainComplex C ℤ)).IsStableUnderRetracts :=
  inferInstanceAs (monomorphisms (CochainComplex C ℤ)).IsStableUnderRetracts

scoped instance : (fibrations (CochainComplex C ℤ)).IsStableUnderRetracts :=
  inferInstanceAs
    (monomorphisms _ ⊓ HomologicalComplex.quasiIso C (.up ℤ)).rlp.IsStableUnderRetracts

/-- A trivial cofibration has the left lifting property with respect to every fibration of the
injective model structure. -/
scoped instance {A B X Y : CochainComplex C ℤ} (i : A ⟶ B) (p : X ⟶ Y) [Cofibration i]
    [WeakEquivalence i] [Fibration p] : HasLiftingProperty i p := by
  have hp := mem_fibrations p
  rw [fibrations_eq] at hp
  exact hp i ⟨(cofibration_iff i).1 ‹_›, (HomologicalComplex.mem_quasiIso_iff i).2 inferInstance⟩

/-- A cofibration has the left lifting property with respect to every trivial fibration of the
injective model structure. -/
scoped instance {A B X Y : CochainComplex C ℤ} (i : A ⟶ B) (p : X ⟶ Y) [Cofibration i]
    [Fibration p] [WeakEquivalence p] : HasLiftingProperty i p := by
  -- The kernel of `p` is an acyclic K-injective complex, so the obstruction to lifting, a
  -- cocycle into that kernel, is a coboundary.
  obtain ⟨hp, _⟩ := (fibration_iff p).1 ‹_›
  have := hp.epi
  have hS : (ShortComplex.mk _ _ (kernel.condition p)).ShortExact :=
    { exact := ShortComplex.exact_kernel p }
  exact hasLiftingProperty_of_forall_eq_δ i p hp (hι := kernel.condition p) (kernelIsKernel p)
    fun z ↦ IsKInjective.eq_δ_of_cocycle' z (hS.acyclic_X₁ (by dsimp; infer_instance)) 0 (by simp)

/-- The trivial fibrations of the injective model structure have the right lifting property with
respect to all monomorphisms. -/
lemma trivialFibrations_le_rlp_monomorphisms :
    trivialFibrations (CochainComplex C ℤ) ≤ (monomorphisms _).rlp := by
  intro X Y p hp A B i (_ : Mono i)
  rw [mem_trivialFibrations_iff] at hp
  obtain ⟨_, _⟩ := hp
  have : Cofibration i := (cofibration_iff i).2 ‹_›
  infer_instance

/-- A morphism with the right lifting property with respect to all monomorphisms is a trivial
fibration of the injective model structure. -/
lemma rlp_monomorphisms_le_trivialFibrations :
    (monomorphisms (CochainComplex C ℤ)).rlp ≤ trivialFibrations _ := by
  -- The kernel of `p` inherits the lifting property, so its identity factors through the
  -- contractible mapping cone of that identity; hence the kernel is acyclic.
  intro X Y p hp
  have hfib : Fibration p := by
    rw [HomotopicalAlgebra.fibration_iff, fibrations_eq]
    exact antitone_rlp inf_le_left _ hp
  have hK : (monomorphisms _).rlp (0 : kernel p ⟶ 0) :=
    IsStableUnderBaseChange.of_isPullback (IsPullback.kernel_ι p) hp
  have := hK (HomologicalComplex.homotopyCofiber.inr (𝟙 (kernel p))) (inferInstanceAs (Mono _))
  have hacyc : (kernel p).Acyclic := Homotopy.acyclic
    (nonempty_homotopy_zero_of_hasLiftingProperty (𝟙 (kernel p)) (p := 0) (isZero_zero _)).some
  have := ((fibration_iff p).1 hfib).1.epi
  have hS : (ShortComplex.mk _ _ (kernel.condition p)).ShortExact :=
    { exact := ShortComplex.exact_kernel p }
  rw [mem_trivialFibrations_iff, weakEquivalence_iff]
  exact ⟨hfib, hS.quasiIso_g_iff.2 hacyc⟩

/-- **Trivial fibrations of the injective model structure.** A morphism of cochain complexes is a
trivial fibration of the injective model structure if and only if it has the right lifting
property with respect to all monomorphisms. -/
theorem trivialFibrations_eq :
    trivialFibrations (CochainComplex C ℤ) = (monomorphisms _).rlp :=
  le_antisymm trivialFibrations_le_rlp_monomorphisms rlp_monomorphisms_le_trivialFibrations

section EnoughInjectives

variable [EnoughInjectives C]

/-- The projection `mappingCone (𝟙 (cm5b.I K)) ⊞ L ⟶ L` of Mathlib's factorization
`CochainComplex.cm5b` is a trivial fibration of the injective model structure. -/
private lemma trivialFibrations_cm5b_p (K L : CochainComplex C ℤ) :
    trivialFibrations (CochainComplex C ℤ) (cm5b.p K L) := by
  -- the kernel is the mapping cone of an identity, which is contractible, hence K-injective
  have : (kernel (cm5b.p K L)).IsKInjective := by
    have := isKInjective_of_homotopy_id_zero (mappingCone.homotopyToZeroOfId (cm5b.I K))
    exact isKInjective_of_iso (L₁ := mappingCone (𝟙 (cm5b.I K)))
      ((biprod.isKernelSndKernelFork _ _).conePointUniqueUpToIso (limit.isLimit _))
  rw [mem_trivialFibrations_iff, fibration_iff, weakEquivalence_iff]
  exact ⟨⟨cm5b.degreewiseEpiWithInjectiveKernel_p K L, this⟩, inferInstance⟩

/-- Every morphism of cochain complexes factors as a monomorphism followed by a trivial fibration
of the injective model structure. -/
scoped instance : (cofibrations (CochainComplex C ℤ)).HasFactorization
    (trivialFibrations (CochainComplex C ℤ)) where
  nonempty_mapFactorizationData f := ⟨{
    Z := _
    i := cm5b.i f
    p := cm5b.p _ _
    hi := monomorphisms.infer_property (cm5b.i f)
    hp := trivialFibrations_cm5b_p _ _ }⟩

end EnoughInjectives

variable [IsGrothendieckAbelian.{w} C]

/-- Every morphism of cochain complexes over a Grothendieck abelian category factors as a
trivial cofibration followed by a fibration of the injective model structure. -/
scoped instance : (trivialCofibrations (CochainComplex C ℤ)).HasFactorization
    (fibrations (CochainComplex C ℤ)) := by
  rw [trivialCofibrations_eq, fibrations_eq]
  infer_instance

/-- **The injective model structure.** For a Grothendieck abelian category `C`, the unbounded
cochain complexes in `C` form a model category whose weak equivalences are the
quasi-isomorphisms, whose cofibrations are the monomorphisms, and whose fibrations are the
morphisms with the right lifting property with respect to the monomorphic quasi-isomorphisms. -/
scoped instance instModelCategory : ModelCategory (CochainComplex C ℤ) where

/-- **The injective model structure is cofibrantly generated.** There are a family `I` of
cofibrations and a family `J` of trivial cofibrations, both admitting the small object argument,
such that the trivial fibrations are the morphisms with the right lifting property with respect to
`I`, and the fibrations those with the right lifting property with respect to `J`. -/
theorem exists_hasSmallObjectArgument_rlp_eq_trivialFibrations_and_fibrations :
    ∃ I J : MorphismProperty (CochainComplex C ℤ),
      HasSmallObjectArgument.{w} I ∧ I ≤ cofibrations _ ∧ I.rlp = trivialFibrations _ ∧
        HasSmallObjectArgument.{w} J ∧ J ≤ trivialCofibrations _ ∧ J.rlp = fibrations _ := by
  obtain ⟨J, _, hJ, hJrlp⟩ :=
    exists_hasSmallObjectArgument_le_monomorphisms_inf_quasiIso_and_rlp_eq.{w} (C := C)
  have hG := isSeparator_separator (CochainComplex C ℤ)
  refine ⟨IsGrothendieckAbelian.generatingMonomorphisms (separator _), J, inferInstance,
    IsGrothendieckAbelian.generatingMonomorphisms_le_monomorphisms _, ?_, inferInstance, hJ,
    hJrlp⟩
  rw [IsGrothendieckAbelian.generatingMonomorphisms_rlp.{w} hG, trivialFibrations_eq]

end CochainComplex.modelCategoryInjective

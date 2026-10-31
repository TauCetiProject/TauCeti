/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Tower.KInjective
public import TauCeti.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
import Mathlib.Algebra.Homology.Factorizations.CM5a
import Mathlib.CategoryTheory.Functor.OfSequence

/-!
# Unbounded K-injective replacements of module complexes

Every cochain complex of modules over an associative unital ring admits a quasi-isomorphism
into a K-injective complex. No boundedness assumption is imposed. This existence result allows
one to compute morphisms in the unbounded derived category using homotopy classes of chain maps.

The construction resolves the truncations `τ^{≥ -n} K` by bounded-below complexes of injectives,
with degreewise split epimorphic transition maps. Their inverse limit is K-injective and the
map from `K` to that limit is a quasi-isomorphism. We use Joël Riou's bounded-below factorization
`CochainComplex.Plus.modelCategoryQuillen.cm5a` from Mathlib and the module tower limit and
Milnor comparison in `TauCeti.Algebra.Category.ModuleCat.Tower.KInjective`.

Hence module categories have K-injective resolutions (`TauCeti.HasKInjectiveResolutions`), so
the replacement functor `TauCeti.kInjectiveReplacement` of
`TauCeti.Algebra.Homology.DerivedCategory.KInjective` is defined on the unbounded derived
category of modules, with values in the homotopy category.

## References

* N. Spaltenstein, *Resolutions of unbounded complexes*, Compositio Math. 65 (1988), 121–154.
* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P).
-/

public section

noncomputable section

open CategoryTheory Limits Opposite HomologicalComplex ZeroObject

namespace CochainComplex

universe v u

variable {R : Type u} [Ring R] (K : CochainComplex (ModuleCat.{max v u} R) ℤ)

/-- A bounded-below injective model for one truncation, used in the inverse-limit construction. -/
private structure InjectiveTruncation (n : ℕ) where
  complex : CochainComplex (ModuleCat.{max v u} R) ℤ
  bounded : complex.IsStrictlyGE (-(n : ℤ) - 1)
  injective : ∀ i, Injective (complex.X i)
  map : K.truncGE (-(n : ℤ)) ⟶ complex
  quasiIso : QuasiIso map

attribute [instance] InjectiveTruncation.bounded InjectiveTruncation.injective
  InjectiveTruncation.quasiIso

variable {K}

private def InjectiveTruncation.ι {n : ℕ} (I : InjectiveTruncation K n) : K ⟶ I.complex :=
  K.πTruncGE (-(n : ℤ)) ≫ I.map

private theorem InjectiveTruncation.quasiIsoAt_ι {n : ℕ} (I : InjectiveTruncation K n)
    (j : ℤ) (hj : -(n : ℤ) ≤ j) : QuasiIsoAt I.ι j := by
  have := K.quasiIsoAt_πTruncGE (-(n : ℤ)) j hj
  dsimp [InjectiveTruncation.ι]
  infer_instance

variable (K) in
private def InjectiveTruncation.zero : InjectiveTruncation K 0 := Classical.choice <| by
  obtain ⟨I, i, _, hi, hinj, hI⟩ :=
    Plus.modelCategoryQuillen.exists_mono_quasiIso_injective (K.truncGE 0) (-1) 0 (by omega)
  exact ⟨⟨I, hI, hinj, i, hi⟩⟩

/-- Resolve the next truncation over the preceding model, rather than resolving it independently.
The injective-kernel condition on the factorization gives split transitions in every degree. -/
private theorem InjectiveTruncation.exists_next {n : ℕ} (I : InjectiveTruncation K n) :
    ∃ (J : InjectiveTruncation K (n + 1)) (p : J.complex ⟶ I.complex),
      J.ι ≫ p = I.ι ∧ ∀ j, IsSplitEpi (p.f j) := by
  let a : ℤ := -((n + 1 : ℕ) : ℤ)
  have hI : I.complex.IsStrictlyGE a := by
    convert I.bounded using 1; dsimp [a]; omega
  let f : K.truncGE a ⟶ I.complex :=
    truncGEMap I.ι a ≫ inv (I.complex.πTruncGE a)
  have hf : K.πTruncGE a ≫ f = I.ι := by
    simp [f]
  have hsource : (K.truncGE a).IsStrictlyGE (a - 1 + 1) := by
    simpa using (inferInstance : (K.truncGE a).IsStrictlyGE a)
  have htarget : I.complex.IsStrictlyGE (a - 1) :=
    I.complex.isStrictlyGE_of_ge _ a (by omega)
  obtain ⟨J, hJ, i, p, _, hi, hp, hip⟩ := Plus.modelCategoryQuillen.cm5a f (a - 1)
  have hinj : ∀ j, Injective (J.X j) := by
    have hz := MorphismProperty.comp_mem degreewiseEpiWithInjectiveKernel p
      (0 : I.complex ⟶ 0) hp
      ((degreewiseEpiWithInjectiveKernel_iff_of_isZero _ (isZero_zero _)).2 I.injective)
    exact (degreewiseEpiWithInjectiveKernel_iff_of_isZero _ (isZero_zero _)).1 hz
  refine ⟨⟨J, hJ, hinj, i, hi⟩, p, ?_, fun j ↦ ?_⟩
  · simpa only [InjectiveTruncation.ι, Category.assoc, hip] using hf
  · obtain ⟨E, _, e, w, ⟨s⟩⟩ := (Abelian.epiWithInjectiveKernel_iff _).1 (hp j)
    exact ⟨s.s, s.s_g⟩

private def InjectiveTruncation.next {n : ℕ} (I : InjectiveTruncation K n) :
    InjectiveTruncation K (n + 1) := I.exists_next.choose

private def InjectiveTruncation.transition {n : ℕ} (I : InjectiveTruncation K n) :
    I.next.complex ⟶ I.complex := I.exists_next.choose_spec.choose

private theorem InjectiveTruncation.ι_transition {n : ℕ} (I : InjectiveTruncation K n) :
    I.next.ι ≫ I.transition = I.ι := I.exists_next.choose_spec.choose_spec.1

private theorem InjectiveTruncation.isSplitEpi_transition {n : ℕ}
    (I : InjectiveTruncation K n) (j : ℤ) : IsSplitEpi (I.transition.f j) :=
  I.exists_next.choose_spec.choose_spec.2 j

variable (K)

private def injectiveTruncations : ∀ n, InjectiveTruncation K n
  | 0 => InjectiveTruncation.zero K
  | n + 1 => (injectiveTruncations n).next

private def injectiveTruncationTower :
    TauCeti.ComplexTower.{max v u} R (ComplexShape.up ℤ) :=
  Functor.ofOpSequence (X := fun n ↦ (injectiveTruncations K n).complex)
    fun n ↦ (injectiveTruncations K n).transition

private theorem injectiveTruncationTower_map (n : ℕ) :
    (injectiveTruncationTower K).map (homOfLE (Nat.le_succ n)).op =
      (injectiveTruncations K n).transition :=
  Functor.ofOpSequence_map_homOfLE_succ _ n

private def injectiveTruncationCone : Cone (injectiveTruncationTower K) :=
  Cone.mk K <| NatTrans.ofOpSequence (fun n ↦ (injectiveTruncations K n).ι)
    (fun n ↦ by
      rw [injectiveTruncationTower_map]
      exact (Category.id_comp _).trans (injectiveTruncations K n).ι_transition.symm)

private theorem injectiveTruncationTower_split (n : ℕ) (j : ℤ) :
    IsSplitEpi (((injectiveTruncationTower K).map (homOfLE (Nat.le_succ n)).op).f j) := by
  rw [injectiveTruncationTower_map]
  exact (injectiveTruncations K n).isSplitEpi_transition j

/-- Every possibly unbounded complex of left modules admits a quasi-isomorphism into a
K-injective complex. The ring need not be commutative. -/
theorem exists_quasiIso_isKInjective :
    ∃ (I : CochainComplex (ModuleCat.{max v u} R) ℤ) (i : K ⟶ I),
      QuasiIso i ∧ I.IsKInjective := by
  let C := injectiveTruncationTower K
  have hsplit := injectiveTruncationTower_split K
  have hki (n : ℕ) : CochainComplex.IsKInjective (C.obj (op n)) := by
    have : CochainComplex.IsStrictlyGE (C.obj (op n)) (-(n : ℤ) - 1) :=
      (injectiveTruncations K n).bounded
    have (j : ℤ) : Injective ((C.obj (op n)).X j) :=
      (injectiveTruncations K n).injective j
    exact isKInjective_of_injective _ (-(n : ℤ) - 1)
  have hsurj (j : ℤ) : Function.Surjective (C.term j).shift := by
    apply TauCeti.ModuleTower.shift_surjective
    intro n
    have := hsplit n j
    rw [TauCeti.ModuleTower.transition_def]
    exact (ModuleCat.epi_iff_surjective ((C.map (homOfLE (Nat.le_succ n)).op).f j)).1
      inferInstance
  refine ⟨C.limComplex, C.isLimitLimComplexCone.lift (injectiveTruncationCone K), ?_,
    C.isKInjective_limComplex hsplit⟩
  apply C.quasiIso_isLimitLimComplexCone_lift hsurj
  intro j
  refine ⟨j.natAbs, fun n hn ↦ ?_⟩
  exact (injectiveTruncations K n).quasiIsoAt_ι j (by omega)

end CochainComplex

namespace TauCeti

universe v u

variable (R : Type u) [Ring R]

instance : HasKInjectiveResolutions (ModuleCat.{max v u} R) :=
  ⟨CochainComplex.exists_quasiIso_isKInjective⟩

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Tower.KInjective
public import TauCeti.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
public import TauCeti.Algebra.Homology.ModelCategory.KInjective.Tower
public import TauCeti.Algebra.Homology.Embedding.CochainComplex
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

private abbrev injectiveTruncationTower :
    TauCeti.ComplexTower.{max v u} R (ComplexShape.up ℤ) :=
  Functor.ofOpSequence (towerResolutionπ (fun n ↦ K.truncGE (-(n : ℤ)))
    (fun n ↦ K.truncGETransition (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) (by lia)))

private abbrev injectiveTruncationι (n : ℕ) :
    K ⟶ (injectiveTruncationTower K).obj (op n) :=
  K.πTruncGE (-(n : ℤ)) ≫ towerResolutionι (fun n ↦ K.truncGE (-(n : ℤ)))
    (fun n ↦ K.truncGETransition (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) (by lia)) n

private theorem injectiveTruncationι_transition (n : ℕ) :
    injectiveTruncationι K (n + 1) ≫
      (injectiveTruncationTower K).map (homOfLE (Nat.le_succ n)).op =
        injectiveTruncationι K n := by
  rw [Functor.ofOpSequence_map_homOfLE_succ]
  -- State the compatibility using the resolving complexes before passing to tower objects.
  have h : (K.πTruncGE (-((n + 1 : ℕ) : ℤ)) ≫
      towerResolutionι (fun n ↦ K.truncGE (-(n : ℤ)))
        (fun n ↦ K.truncGETransition (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) (by lia)) (n + 1)) ≫
      towerResolutionπ (fun n ↦ K.truncGE (-(n : ℤ)))
        (fun n ↦ K.truncGETransition (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) (by lia)) n =
      injectiveTruncationι K n := by
    rw [Category.assoc, towerResolutionι_comp_towerResolutionπ, πTruncGE_truncGETransition_assoc]
    rfl
  exact h

private def injectiveTruncationCone : Cone (injectiveTruncationTower K) :=
  Cone.mk K <| NatTrans.ofOpSequence (injectiveTruncationι K)
    (fun n ↦ (Category.id_comp _).trans (injectiveTruncationι_transition K n).symm)

private theorem injectiveTruncationTower_split (n : ℕ) (j : ℤ) :
    IsSplitEpi (((injectiveTruncationTower K).map (homOfLE (Nat.le_succ n)).op).f j) := by
  rw [Functor.ofOpSequence_map_homOfLE_succ]
  obtain ⟨E, _, e, w, ⟨s⟩⟩ := (Abelian.epiWithInjectiveKernel_iff _).1
    (degreewiseEpiWithInjectiveKernel_towerResolutionπ (fun n ↦ K.truncGE (-(n : ℤ)))
      (fun n ↦ K.truncGETransition (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) (by lia)) n j)
  exact ⟨s.s, s.s_g⟩

/-- Every possibly unbounded complex of left modules admits a quasi-isomorphism into a
K-injective complex. The ring need not be commutative. -/
theorem exists_quasiIso_isKInjective :
    ∃ (I : CochainComplex (ModuleCat.{max v u} R) ℤ) (i : K ⟶ I),
      QuasiIso i ∧ I.IsKInjective := by
  let C := injectiveTruncationTower K
  have hsplit := injectiveTruncationTower_split K
  have (n : ℕ) : IsKInjective (C.obj (op n)) :=
    inferInstanceAs (IsKInjective (towerResolution (fun n ↦ K.truncGE (-(n : ℤ)))
      (fun n ↦ K.truncGETransition (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) (by lia)) n))
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
  have := K.quasiIsoAt_πTruncGE (-(n : ℤ)) j (by omega)
  exact quasiIsoAt_comp (K.πTruncGE (-(n : ℤ)))
    (towerResolutionι (fun n ↦ K.truncGE (-(n : ℤ)))
      (fun n ↦ K.truncGETransition (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) (by lia)) n) j

end CochainComplex

namespace TauCeti

universe v u

variable (R : Type u) [Ring R]

instance : HasKInjectiveResolutions (ModuleCat.{max v u} R) :=
  ⟨CochainComplex.exists_quasiIso_isKInjective⟩

end TauCeti

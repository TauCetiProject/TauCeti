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

/-- Every possibly unbounded complex of left modules admits a quasi-isomorphism into a
K-injective complex. The ring need not be commutative. -/
theorem exists_quasiIso_isKInjective :
    ∃ (I : CochainComplex (ModuleCat.{max v u} R) ℤ) (i : K ⟶ I),
      QuasiIso i ∧ I.IsKInjective := by
  let C : TauCeti.ComplexTower.{max v u} R (ComplexShape.up ℤ) := K.truncGETower
  have hsplit := K.isSplitEpi_truncGETower_map_f
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
  refine ⟨C.limComplex, C.isLimitLimComplexCone.lift K.truncGETowerCone, ?_,
    C.isKInjective_limComplex hsplit⟩
  apply C.quasiIso_isLimitLimComplexCone_lift hsurj
  intro j
  exact ⟨j.natAbs, fun n hn ↦ K.quasiIsoAt_truncGETowerι n j (by omega)⟩

end CochainComplex

namespace TauCeti

universe v u

variable (R : Type u) [Ring R]

instance : HasKInjectiveResolutions (ModuleCat.{max v u} R) :=
  ⟨CochainComplex.exists_quasiIso_isKInjective⟩

end TauCeti

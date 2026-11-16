/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
public import Mathlib.LinearAlgebra.Pi
import TauCeti.LinearAlgebra.LinearIndependent.Fin

/-!
# Exterior products in a product of modules

For a family of modules `U i`, an exterior product of vectors of `U i` maps into the exterior
algebra of `Πⱼ U j` along the inclusion `LinearMap.single R U i` of the `i`th factor. The product of
such exterior products over distinct factors is again an exterior product, of the concatenated
family, and that family is linearly independent when each of the original families is: the
families lie in distinct factors.

## Main results

* `TauCeti.ExteriorAlgebra.exists_linearIndependent_prod_ιMulti_single_eq_ιMulti`: the product,
  along a list of distinct indices, of the exterior products of linearly independent families of the
  factors is the exterior product of a linearly independent family of `Πⱼ U j` vanishing at the
  indices off the list.
-/

public section

namespace TauCeti

namespace ExteriorAlgebra

variable {R ι : Type*} [CommRing R] [DecidableEq ι] {U : ι → Type*} [∀ i, AddCommGroup (U i)]
  [∀ i, Module R (U i)]

/-- Let `b i` be a linearly independent family of `n i` vectors of `U i` for each `i`. Multiplying
the exterior products of the families `b i`, pushed into `Πⱼ U j` by the inclusions of the factors,
along a list of distinct indices gives the exterior product of a linearly independent family of
vectors of `Πⱼ U j` vanishing at the indices off the list. -/
theorem exists_linearIndependent_prod_ιMulti_single_eq_ιMulti {n : ι → ℕ}
    {b : (i : ι) → Fin (n i) → U i} (hb : ∀ i, LinearIndependent R (b i)) {l : List ι}
    (hl : l.Nodup) :
    ∃ N, ∃ v : Fin N → ((i : ι) → U i), LinearIndependent R v ∧ (∀ k, ∀ j ∉ l, v k j = 0) ∧
      (l.map fun i ↦ _root_.ExteriorAlgebra.ιMulti R (n i) (LinearMap.single R U i ∘ b i)).prod =
        _root_.ExteriorAlgebra.ιMulti R N v := by
  induction l with
  | nil => exact ⟨0, Fin.elim0, linearIndependent_empty_type, fun k ↦ k.elim0, by simp⟩
  | cons a l ih =>
    rw [List.nodup_cons] at hl
    obtain ⟨N, v, hv, hsupp, heq⟩ := ih hl.2
    refine ⟨_, Fin.append (LinearMap.single R U a ∘ b a) v, ?_, ?_, ?_⟩
    · refine linearIndependent_fin_append.2 ⟨(hb a).map'
        _ (LinearMap.ker_eq_bot.2 fun x y hxy ↦ by simpa using congrFun hxy a), hv, ?_⟩
      -- The first block lies in the `a`th factor, the second vanishes at `a`.
      have h₁ : Submodule.span R (Set.range (LinearMap.single R U a ∘ b a)) ≤
          LinearMap.range (LinearMap.single R U a) :=
        Submodule.span_le.2 (Set.range_subset_iff.2 fun k ↦ LinearMap.mem_range_self _ _)
      have h₂ : Submodule.span R (Set.range v) ≤ LinearMap.ker (LinearMap.proj a) :=
        Submodule.span_le.2 (Set.range_subset_iff.2 fun k ↦ hsupp k a hl.1)
      refine Submodule.disjoint_def.2 fun x hx hx' ↦ ?_
      obtain ⟨y, rfl⟩ := h₁ hx
      have hy : y = 0 := by simpa using h₂ hx'
      simp [hy]
    · intro k j hj
      rw [List.mem_cons, not_or] at hj
      induction k using Fin.addCases with
      | left k => simp [hj.1]
      | right k => simpa using hsupp k j hj.2
    · rw [List.map_cons, List.prod_cons, heq, _root_.ExteriorAlgebra.ιMulti_mul_ιMulti]

end ExteriorAlgebra

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.LinearAlgebra.Span.Basic

/-!
# Endomorphisms commuting with a family that has a cyclic vector

Let `f : ι → Module.End R M` be a family of endomorphisms and `v : M` a vector such that the
vectors `f i v` span `M`. An endomorphism commuting with every `f i` is determined by its value at
`v`. If moreover `ι` is finite and the `f i` commute with each other, every endomorphism commuting
with every `f i` is a linear combination of the `f i`.

## Main results

* `Module.End.eq_of_commute_of_span_eq_top`: two endomorphisms commuting with every `f i` that agree
  at `v` are equal.
* `Module.End.exists_eq_sum_smul_of_commute`: for a finite commuting family, the endomorphisms
  commuting with every `f i` are the linear combinations of the `f i`.
-/

public section

namespace Module.End

variable {R M ι : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  {f : ι → Module.End R M} {v : M}

/-- If the vectors `f i v` span `M`, two endomorphisms commuting with every `f i` that agree at `v`
are equal. -/
theorem eq_of_commute_of_span_eq_top (hv : Submodule.span R (Set.range fun i ↦ f i v) = ⊤)
    {β γ : Module.End R M} (hβ : ∀ i, Commute (f i) β) (hγ : ∀ i, Commute (f i) γ)
    (h : β v = γ v) : β = γ :=
  LinearMap.ext_on_range hv fun i ↦ by
    rw [← mul_apply_eq_comp, ← (hβ i).eq, mul_apply_eq_comp, h, ← mul_apply_eq_comp, (hγ i).eq,
      mul_apply_eq_comp]

/-- **The commutant of a family with a cyclic vector.** Let `f : ι → Module.End R M` be a finite
family of pairwise commuting endomorphisms such that the vectors `f i v` span `M`. Then every
endomorphism commuting with every `f i` is a linear combination of the `f i`. -/
theorem exists_eq_sum_smul_of_commute [Fintype ι]
    (hv : Submodule.span R (Set.range fun i ↦ f i v) = ⊤) (hf : ∀ i j, Commute (f i) (f j))
    {β : Module.End R M} (hβ : ∀ i, Commute (f i) β) : ∃ c : ι → R, β = ∑ i, c i • f i := by
  obtain ⟨c, hc⟩ :=
    (Submodule.mem_span_range_iff_exists_fun R).1 (hv ▸ Submodule.mem_top (x := β v))
  refine ⟨c, eq_of_commute_of_span_eq_top hv hβ
    (fun i ↦ Commute.sum_right _ _ _ fun j _ ↦ (hf i j).smul_right _) ?_⟩
  rw [← hc, LinearMap.sum_apply]
  simp only [LinearMap.smul_apply]

end Module.End

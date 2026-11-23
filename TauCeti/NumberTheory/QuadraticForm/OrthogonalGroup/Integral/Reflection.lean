/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.QuadraticForm.OrthogonalGroup.Integral.Basic

/-!
# Reflections in integral orthogonal subgroups

Let `b` be a basis of a quadratic space `(V, Q)` over `ℚ_[p]`, and let `Λ` be the `ℤ_[p]`-span of
`b`. The reflection in a vector `v` with `Q v ≠ 0` is `x ↦ x - (polar Q v x / Q v) • v`. If `v`
lies in `Λ` and `‖polar Q v (b i)‖ ≤ ‖Q v‖` for every basis vector, then the coefficient
`polar Q v x / Q v` is a `p`-adic integer for every `x ∈ Λ`, so the reflection preserves `Λ` and
lies in the integral orthogonal subgroup of `b`
(`TauCeti.QuadraticMap.reflectionOrthogonal_mem_integralOrthogonalSubgroup_of_norm_polar_le`).

Such a vector exists for every nonzero form, at every prime, `p = 2` included. Among the
finitely many vectors `b i` and `b i + b j`, take one, `v`, whose norm has the largest absolute
value `‖Q v‖`.
The identity `polar Q x y = Q (x + y) - Q x - Q y` and the ultrametric inequality bound every
`polar Q (b i) (b j)`, hence every `polar Q v (b k)`, by `‖Q v‖`; and `Q v ≠ 0`, since otherwise
the polar form, and with it `Q`, would vanish. In the language of lattices, `Q v` generates the
norm ideal of `Λ`, which contains twice its scale ideal. Since a reflection has determinant `-1`,
the integral orthogonal subgroup of a nonzero form always contains an improper isometry. This
needs no hypothesis that some integral vector has unit norm, which fails for instance for `⟨4⟩`
over `ℤ_[2]`, where the reflection in the basis vector is `-1`.

## Main results

* `TauCeti.QuadraticMap.reflectionOrthogonal_mem_integralOrthogonalSubgroup_of_norm_polar_le`:
  the reflection in an integral vector `v` with `‖polar Q v (b i)‖ ≤ ‖Q v‖` for all `i` is an
  integral isometry.
* `TauCeti.QuadraticMap.exists_reflectionOrthogonal_mem_integralOrthogonalSubgroup`: for a nonzero
  form the integral orthogonal subgroup contains the reflection in some integral vector.
* `TauCeti.QuadraticMap.exists_mem_integralOrthogonalSubgroup_orthogonalDet_eq_neg_one`: for a
  nonzero form the integral orthogonal subgroup contains an isometry of determinant `-1`.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms* (1963), §82E for the scale and norm ideals
  and §102A for the stabilizers of a lattice.
-/

public section

namespace TauCeti
namespace QuadraticMap

open _root_.QuadraticMap Module

variable {p : ℕ} [Fact p.Prime] {V ι : Type*} [AddCommGroup V] [Module ℚ_[p] V]
  {Q : QuadraticForm ℚ_[p] V} {b : Basis ι ℚ_[p] V}

/-- For a nonzero form, some vector `v` of the `ℤ_[p]`-span of `b` has `Q v ≠ 0` and
`‖polar Q v (b i)‖ ≤ ‖Q v‖` for every `i`: among the vectors `b i` and `b i + b j`, take one whose
norm has the largest absolute value. -/
private theorem exists_mem_span_ne_zero_norm_polar_le [Finite ι] (hQ : Q ≠ 0) :
    ∃ v ∈ Submodule.span (PadicInt.subring p) (Set.range b), Q v ≠ 0 ∧
      ∀ i, ‖polar Q v (b i)‖ ≤ ‖Q v‖ := by
  obtain ⟨x, hx⟩ : ∃ x, Q x ≠ 0 := by
    by_contra! h
    exact hQ (QuadraticMap.ext h)
  have : Nontrivial V := ⟨⟨x, 0, fun h ↦ hx (by rw [h, QuadraticMap.map_zero])⟩⟩
  have : Nonempty ι := b.index_nonempty
  have := Fintype.ofFinite ι
  let w : ι ⊕ ι × ι → V := Sum.elim b fun ij ↦ b ij.1 + b ij.2
  obtain ⟨s, -, hs⟩ :=
    Finset.exists_max_image Finset.univ (fun s ↦ ‖Q (w s)‖) Finset.univ_nonempty
  -- The polar form on two basis vectors is bounded by the three norms it is made of.
  have hpol (i j : ι) : ‖polar Q (b i) (b j)‖ ≤ ‖Q (w s)‖ := by
    have hi := hs (Sum.inl i) (Finset.mem_univ _)
    have hj := hs (Sum.inl j) (Finset.mem_univ _)
    have hij := hs (Sum.inr (i, j)) (Finset.mem_univ _)
    simp only [w, Sum.elim_inl, Sum.elim_inr] at hi hj hij
    have hsub (a c : ℚ_[p]) : ‖a - c‖ ≤ max ‖a‖ ‖c‖ := by
      simpa [sub_eq_add_neg] using Padic.nonarchimedean a (-c)
    rw [polar]
    exact (hsub _ _).trans (max_le ((hsub _ _).trans (max_le hij hi)) hj)
  have hbound (k : ι) : ‖polar Q (w s) (b k)‖ ≤ ‖Q (w s)‖ := by
    rcases s with i | ⟨i, j⟩
    · exact hpol i k
    · simp only [w, Sum.elim_inr]
      rw [polar_add_left]
      exact (Padic.nonarchimedean _ _).trans (max_le (hpol i k) (hpol j k))
  refine ⟨w s, ?_, fun h0 ↦ hx ?_, hbound⟩
  · rcases s with i | ⟨i, j⟩
    · exact Submodule.subset_span ⟨i, rfl⟩
    · exact add_mem (Submodule.subset_span ⟨i, rfl⟩) (Submodule.subset_span ⟨j, rfl⟩)
  · -- Otherwise the polar form vanishes on the basis, hence everywhere, and so does `Q`.
    have hzero : polarBilin Q = 0 := LinearMap.ext_basis b b fun i j ↦ by
      simpa [h0] using hpol i j
    have h2 : polar Q x x = 0 := by
      simpa using LinearMap.congr_fun₂ hzero x x
    rw [polar_self, two_nsmul, ← two_mul] at h2
    exact (mul_eq_zero.mp h2).resolve_left two_ne_zero

variable [Fintype ι] [DecidableEq ι]

/-- **Integral reflections.** The reflection in a vector `v` of the `ℤ_[p]`-span of `b` lies in
the integral orthogonal subgroup of `b` as soon as `‖polar Q v (b i)‖ ≤ ‖Q v‖` for every `i`. -/
theorem reflectionOrthogonal_mem_integralOrthogonalSubgroup_of_norm_polar_le {v : V}
    [Invertible (Q v)] (hv : v ∈ Submodule.span (PadicInt.subring p) (Set.range b))
    (hpolar : ∀ i, ‖polar Q v (b i)‖ ≤ ‖Q v‖) :
    reflectionOrthogonal Q v ∈ integralOrthogonalSubgroup Q b := by
  have hmem (x : V) (hx : x ∈ Submodule.span (PadicInt.subring p) (Set.range b)) :
      reflection Q v x ∈ Submodule.span (PadicInt.subring p) (Set.range b) := by
    have hle : ‖polar Q v x‖ ≤ ‖Q v‖ := by
      simpa using PadicInt.norm_apply_le_of_mem_span_subring (f := polarBilin Q v)
        (norm_nonneg _) (by simpa using hpolar) hx
    have hc : ⅟(Q v) * polar Q v x ∈ PadicInt.subring p := by
      rw [PadicInt.mem_subring_iff p, norm_mul, invOf_eq_inv, norm_inv]
      exact inv_mul_le_one_of_le₀ hle (norm_nonneg _)
    rw [reflection_apply]
    exact sub_mem hx (Submodule.smul_mem _ (⟨_, hc⟩ : PadicInt.subring p) hv)
  rw [mem_integralOrthogonalSubgroup_iff_mem_span, reflectionOrthogonal_inv,
    coe_reflectionOrthogonal]
  exact ⟨hmem, hmem⟩

/-- **A reflection in an integral vector.** For a nonzero quadratic form over `ℚ_[p]`, at every
prime `p`, the integral orthogonal subgroup of a basis `b` contains the reflection in some vector
of the `ℤ_[p]`-span of `b`. -/
theorem exists_reflectionOrthogonal_mem_integralOrthogonalSubgroup (hQ : Q ≠ 0) :
    ∃ (v : V) (_ : Invertible (Q v)), v ∈ Submodule.span (PadicInt.subring p) (Set.range b) ∧
      reflectionOrthogonal Q v ∈ integralOrthogonalSubgroup Q b := by
  obtain ⟨v, hv, hQv, hpolar⟩ := exists_mem_span_ne_zero_norm_polar_le (b := b) hQ
  let _ : Invertible (Q v) := invertibleOfNonzero hQv
  exact ⟨v, inferInstance, hv,
    reflectionOrthogonal_mem_integralOrthogonalSubgroup_of_norm_polar_le hv hpolar⟩

/-- **An improper integral isometry.** For a nonzero quadratic form over `ℚ_[p]`, at every prime
`p`, the integral orthogonal subgroup of a basis contains an isometry of determinant `-1`. -/
theorem exists_mem_integralOrthogonalSubgroup_orthogonalDet_eq_neg_one (hQ : Q ≠ 0) :
    ∃ g ∈ integralOrthogonalSubgroup Q b, orthogonalDet Q g = -1 := by
  obtain ⟨v, _, -, hmem⟩ := exists_reflectionOrthogonal_mem_integralOrthogonalSubgroup (b := b) hQ
  have := Module.Finite.of_basis b
  exact ⟨_, hmem, orthogonalDet_reflectionOrthogonal Q v⟩

end QuadraticMap
end TauCeti

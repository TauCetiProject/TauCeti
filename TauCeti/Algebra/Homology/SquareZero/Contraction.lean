/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.SquareZero
public import TauCeti.LinearAlgebra.End.LocallyNilpotent

/-!
# Exactness from a contracting homotopy up to lower-order terms

A square-zero endomorphism `d` of a module is exact, `ker d ≤ range d`, as soon as some `h` makes
`d h + h d` invertible: `d h + h d` commutes with `d`, so its inverse sends cycles to cycles, and
every cycle `x = (d h + h d) y` with `d y = 0` is the boundary `d (h y)`
(`LinearMap.ker_le_range_of_isUnit`). Invertibility holds when `d h + h d` differs from the
identity by a locally nilpotent endomorphism, and on a free module `ι →₀ S` that is the case when
the difference strictly lowers a weight on the basis whose strict order is well-founded
(`Module.End.exists_pow_apply_eq_zero_of_forall_mem_support_lt`,
`LinearMap.ker_le_range_of_forall_mem_support_lt`).

This is the algebraic core of the discrete Morse theory (algebraic Gaussian elimination) used to
compute grid homology: `h` reverses a matching of generators joined by the leading part of `d`,
and the remaining terms of `d h + h d - 1` are of lower order for a filtration.

## Main results

* `LinearMap.ker_le_range_of_isUnit`: a square-zero endomorphism `d` is exact if `d h + h d` is a
  unit for some `h`.
* `LinearMap.ker_le_range_of_forall_mem_support_lt`: a square-zero endomorphism `d` of `ι →₀ S`
  is exact if `d h + h d - 1` strictly lowers a well-founded weight on the basis.
* `LinearMap.ker_le_range_of_matching`: a square-zero endomorphism of `ι →₀ S` is exact if its
  terms of leading (well-founded) weight form a perfect matching of the generators with unit
  coefficients.

## References

The matching criterion is the case of a perfect matching in algebraic discrete Morse theory:
E. Sköldberg, *Morse theory from an algebraic viewpoint*, Trans. Amer. Math. Soc. 358 (2006),
and M. Jöllenbeck, V. Welker, *Minimal resolutions via algebraic discrete Morse theory*,
Mem. Amer. Math. Soc. 197 (2009), no. 923.
-/

public section

open Finsupp

namespace LinearMap

section Semiring

variable {S M : Type*} [Semiring S] [AddCommMonoid M] [Module S M]

/-- **A contracting homotopy up to a unit makes a square-zero endomorphism exact.** If `d ∘ d = 0`
and `d h + h d` is invertible for some `h`, then every element of the kernel of `d` is in its
image. -/
theorem ker_le_range_of_isUnit (d : M →ₗ[S] M) (hd : d ∘ₗ d = 0) (h : M →ₗ[S] M)
    (hu : IsUnit (d * h + h * d : Module.End S M)) : ker d ≤ range d := by
  intro x hx
  rw [mem_ker] at hx
  have hd' : d * d = 0 := by rwa [Module.End.mul_eq_comp]
  have hcomm : Commute d (d * h + h * d) := by
    simp only [Commute, SemiconjBy, mul_add, add_mul, ← mul_assoc, hd', zero_mul, zero_add]
    simp only [mul_assoc, hd', mul_zero, add_zero]
  obtain ⟨u, hu⟩ := hu
  have hinv : Commute d ↑u⁻¹ := (hu ▸ hcomm).units_inv_right
  have hy : d ((↑u⁻¹ : Module.End S M) x) = 0 := by
    rw [← mul_apply_eq_comp, hinv.eq, mul_apply_eq_comp, hx, map_zero]
  refine ⟨h ((↑u⁻¹ : Module.End S M) x), ?_⟩
  have hx' : ((u : Module.End S M) * ↑u⁻¹) x = x := by rw [Units.mul_inv, one_apply_eq_self]
  rw [hu] at hx'
  simpa only [mul_apply_eq_comp, LinearMap.add_apply, hy, map_zero, add_zero] using hx'

end Semiring

variable {S M : Type*} [Ring S] [AddCommGroup M] [Module S M]

/-- A square-zero endomorphism `d` is exact if `d h + h d - 1` is locally nilpotent for some
`h`. -/
theorem ker_le_range_of_forall_exists_pow_apply_eq_zero (d : M →ₗ[S] M) (hd : d ∘ₗ d = 0)
    (h : M →ₗ[S] M) (hν : ∀ x, ∃ k, ((d * h + h * d - 1 : Module.End S M) ^ k) x = 0) :
    ker d ≤ range d := by
  have hu := Module.End.isUnit_one_add_of_forall_exists_pow_apply_eq_zero _ hν
  rw [add_sub_cancel] at hu
  exact d.ker_le_range_of_isUnit hd h hu

/-- **Exactness from a contracting homotopy up to lower-order terms.** A square-zero endomorphism
`d` of `ι →₀ S` is exact if for some `h` the endomorphism `d h + h d - 1` sends each basis
vector into the span of the basis vectors of strictly smaller weight, for a weight `w` whose strict
order `w j < w i` is well-founded (for instance any weight when `ι` is finite). -/
theorem ker_le_range_of_forall_mem_support_lt {ι α : Type*} [LT α]
    (d : (ι →₀ S) →ₗ[S] (ι →₀ S)) (hd : d ∘ₗ d = 0) {h : (ι →₀ S) →ₗ[S] (ι →₀ S)} (w : ι → α)
    (hw : WellFounded (InvImage (· < ·) w))
    (hlow : ∀ i, ∀ j ∈ ((d * h + h * d - 1 : Module.End S (ι →₀ S)) (Finsupp.single i 1)).support,
      w j < w i) :
    ker d ≤ range d :=
  d.ker_le_range_of_forall_exists_pow_apply_eq_zero hd h
    (Module.End.exists_pow_apply_eq_zero_of_forall_mem_support_lt _ w hw hlow)

section Matching

variable {ι α : Type*} [LT α]

/-- The terms of `d` on `k`, apart from the matching term, have weight below `w k`. -/
private theorem sub_single_mem_supported_of_matching (d : (ι →₀ S) →ₗ[S] (ι →₀ S)) (w : ι → α)
    (p : ι → ι) (src : ι → Prop)
    (hsupp : ∀ i, ∀ j ∈ (d (Finsupp.single i 1)).support, w j < w i ∨ (src i ∧ j = p i))
    (k : ι) :
    d (Finsupp.single k 1) - Finsupp.single (p k) (d (Finsupp.single k 1) (p k)) ∈
      supported S S {j | w j < w k} := by
  classical
  refine (mem_supported S _).2 fun j hj ↦ ?_
  rw [Finset.mem_coe, Finsupp.mem_support_iff, Finsupp.sub_apply] at hj
  by_cases hjk : j = p k
  · subst hjk
    simp at hj
  · rw [Finsupp.single_eq_of_ne hjk, sub_zero] at hj
    exact (hsupp k j (Finsupp.mem_support_iff.2 hj)).resolve_right fun h' ↦ hjk h'.2

/-- A homotopy that kills the sources and sends a non-source to its partner, scaled by `c`,
preserves the span of the basis vectors of weight below `a`, when the partner map preserves `w`. -/
private theorem map_mem_supported_of_matching (h : (ι →₀ S) →ₗ[S] (ι →₀ S)) (w : ι → α)
    (p : ι → ι) (src : ι → Prop) [DecidablePred src] (hwp : ∀ i, w (p i) = w i) (c : ι → S)
    (hh : ∀ j x, h (Finsupp.single j x) = if src j then 0 else Finsupp.single (p j) (x * c j))
    (a : α) (v : ι →₀ S) (hv : v ∈ supported S S {j | w j < a}) :
    h v ∈ supported S S {j | w j < a} := by
  rw [← Finsupp.sum_single v, map_finsuppSum]
  refine Submodule.sum_mem _ fun j hj ↦ ?_
  dsimp only
  rw [hh]
  split_ifs
  · exact Submodule.zero_mem _
  · refine single_mem_supported S _ ?_
    rw [Set.mem_ofPred_eq, hwp]
    exact (mem_supported S v).1 hv hj

variable (d : (ι →₀ S) →ₗ[S] (ι →₀ S)) (h : (ι →₀ S) →ₗ[S] (ι →₀ S)) (w : ι → α) (p : ι → ι)
  (src : ι → Prop) [DecidablePred src] (hp : Function.Involutive p) (hwp : ∀ i, w (p i) = w i)
  (hsrc : ∀ i, src i ↔ ¬src (p i))
  (hh : ∀ j x, h (Finsupp.single j x) = if src j then 0 else
    Finsupp.single (p j) (x * Ring.inverse (d (Finsupp.single (p j) 1) j)))
  (hlow : ∀ a v, v ∈ supported S S {j | w j < a} → h v ∈ supported S S {j | w j < a})
  (hcoef : ∀ i, src i → IsUnit (d (Finsupp.single i 1) (p i)))
  (hsupp : ∀ i, ∀ j ∈ (d (Finsupp.single i 1)).support, w j < w i ∨ (src i ∧ j = p i))

include hp hsrc hh hlow hcoef hsupp in
/-- At a source `i`, `d h + h d - 1` lowers the weight: `h` kills `i` and sends the matching term
of `d i` back to `i`. -/
private theorem matching_homotopy_mem_supported_of_src (i : ι) (hi : src i) :
    d (h (Finsupp.single i 1)) + h (d (Finsupp.single i 1)) - Finsupp.single i 1 ∈
      supported S S {j | w j < w i} := by
  have hpi : ¬src (p i) := (hsrc i).1 hi
  have hpair : h (Finsupp.single (p i) (d (Finsupp.single i 1) (p i))) = Finsupp.single i 1 := by
    rw [hh, ite_eq_right hpi, hp i, Ring.mul_inverse_cancel _ (hcoef i hi)]
  have heq : d (h (Finsupp.single i 1)) + h (d (Finsupp.single i 1)) - Finsupp.single i 1 =
      h (d (Finsupp.single i 1) - Finsupp.single (p i) (d (Finsupp.single i 1) (p i))) := by
    rw [map_sub, hpair]
    simp [hh, hi]
  rw [heq]
  exact hlow _ _ (sub_single_mem_supported_of_matching d w p src hsupp i)

include hp hsrc hh hlow hcoef hsupp hwp in
/-- At a non-source `i`, `d h + h d - 1` lowers the weight: `h` sends `i` to `u⁻¹ • p i`, where
`u` is the coefficient of `i` in `d (p i)`, and `d (u⁻¹ • p i)` is `i` up to lower terms. -/
private theorem matching_homotopy_mem_supported_of_not_src (i : ι) (hi : ¬src i) :
    d (h (Finsupp.single i 1)) + h (d (Finsupp.single i 1)) - Finsupp.single i 1 ∈
      supported S S {j | w j < w i} := by
  have hpi : src (p i) := by rw [hsrc (p i), hp i]; exact hi
  have hu : IsUnit (d (Finsupp.single (p i) 1) i) := by simpa only [hp i] using hcoef (p i) hpi
  have hr : d (Finsupp.single (p i) 1) - Finsupp.single i (d (Finsupp.single (p i) 1) i) ∈
      supported S S {j | w j < w i} := by
    simpa only [hp i, hwp] using sub_single_mem_supported_of_matching d w p src hsupp (p i)
  have hdh : d (h (Finsupp.single i 1)) =
      Ring.inverse (d (Finsupp.single (p i) 1) i) • d (Finsupp.single (p i) 1) := by
    rw [hh, ite_eq_right hi, one_mul, ← map_smul, Finsupp.smul_single_one]
  have hcancel : Ring.inverse (d (Finsupp.single (p i) 1) i) •
      Finsupp.single i (d (Finsupp.single (p i) 1) i) = Finsupp.single i 1 := by
    rw [Finsupp.smul_single, smul_eq_mul, Ring.inverse_mul_cancel _ hu]
  have heq : d (h (Finsupp.single i 1)) + h (d (Finsupp.single i 1)) - Finsupp.single i 1 =
      Ring.inverse (d (Finsupp.single (p i) 1) i) •
          (d (Finsupp.single (p i) 1) - Finsupp.single i (d (Finsupp.single (p i) 1) i)) +
        h (d (Finsupp.single i 1)) := by
    rw [hdh, smul_sub, hcancel]
    abel
  rw [heq]
  refine Submodule.add_mem _ (Submodule.smul_mem _ _ hr)
    (hlow _ _ ((mem_supported S _).2 fun j hj ↦ ?_))
  exact (hsupp i j hj).resolve_right fun h' ↦ hi h'.1

end Matching

/-- **Exactness from a weight-preserving matching of generators.** Let `d` be a square-zero
endomorphism of `ι →₀ S`, where `ι` is weighted by `w` with a well-founded strict order
`w j < w i` (for instance any weight when `ι` is finite), and let `p` be an involution of `ι`
preserving `w` that pairs each generator marked as a *source* with one that is not. Suppose
that every term of `d` strictly lowers the weight, except the term from each source `i` to its
partner `p i`, whose coefficient is a unit `u`. Then `d` is exact: the homotopy `h` sending each
non-source `p i` to `u⁻¹ • i` makes `d h + h d - 1` strictly lower the weight.

This is algebraic discrete Morse theory in its simplest form, a perfect matching of the generators
by the leading part of `d`. -/
theorem ker_le_range_of_matching {ι α : Type*} [LT α] (d : (ι →₀ S) →ₗ[S] (ι →₀ S))
    (hd : d ∘ₗ d = 0) (w : ι → α) (hw : WellFounded (InvImage (· < ·) w)) (p : ι → ι)
    (src : ι → Prop) (hp : Function.Involutive p) (hwp : ∀ i, w (p i) = w i)
    (hsrc : ∀ i, src i ↔ ¬src (p i))
    (hcoef : ∀ i, src i → IsUnit (d (Finsupp.single i 1) (p i)))
    (hsupp : ∀ i, ∀ j ∈ (d (Finsupp.single i 1)).support, w j < w i ∨ (src i ∧ j = p i)) :
    ker d ≤ range d := by
  classical
  -- `h` sends a non-source `j` to its partner `p j`, scaled by the inverse of the coefficient
  -- `d (single (p j) 1) j` of the matching term of the source `p j`.
  let h : (ι →₀ S) →ₗ[S] (ι →₀ S) := Finsupp.linearCombination S fun j ↦
    if src j then 0 else Finsupp.single (p j) (Ring.inverse (d (Finsupp.single (p j) 1) j))
  have hh : ∀ j c, h (Finsupp.single j c) = if src j then 0 else
      Finsupp.single (p j) (c * Ring.inverse (d (Finsupp.single (p j) 1) j)) := by
    intro j c
    simp only [h, Finsupp.linearCombination_single]
    split_ifs
    · exact smul_zero c
    · rw [Finsupp.smul_single, smul_eq_mul]
  have hlow := map_mem_supported_of_matching h w p src hwp
    (fun j ↦ Ring.inverse (d (Finsupp.single (p j) 1) j)) hh
  refine d.ker_le_range_of_forall_mem_support_lt hd (h := h) w hw fun i ↦ ?_
  suffices H : (d * h + h * d - 1 : Module.End S (ι →₀ S)) (Finsupp.single i 1) ∈
      supported S S {j | w j < w i} from fun j hj ↦ (mem_supported S _).1 H hj
  simp only [LinearMap.sub_apply, LinearMap.add_apply, mul_apply_eq_comp,
    one_apply_eq_self]
  by_cases hi : src i
  · exact matching_homotopy_mem_supported_of_src d h w p src hp hsrc hh hlow hcoef hsupp i hi
  · exact matching_homotopy_mem_supported_of_not_src d h w p src hp hwp hsrc hh hlow hcoef hsupp
      i hi

end LinearMap

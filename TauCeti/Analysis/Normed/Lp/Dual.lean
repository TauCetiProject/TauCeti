/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Normed.Operator.Mul

/-!
# The continuous dual of `ℓᵖ`

Let `p` and `q` be Hölder conjugate exponents with `q < ∞`. Over real or complex scalars, the
pairing `∑' i, a i * x i` identifies `ℓᵖ` with the continuous dual of `ℓ^q`, isometrically. The
inverse records the values of a functional on the unit coordinate vectors. This covers both the
identification `(ℓ¹)* = ℓ∞` (for `q = 1`) and the reflexive range `(ℓ^q)* = ℓᵖ` for
`1 < q < ∞`. The index type is arbitrary, including empty and uncountable types; no enumeration
is chosen.

`lp.dualEquiv` uses Mathlib's `lp.dualPairing` for the pairing, whose norm bound is Hölder's
inequality, and `lp.hasSum_single` for the coordinate expansion. The pairing is bilinear,
including over complex scalars: the coefficients of a functional are its values on coordinate
vectors, without conjugation.

This identification describes the dual of the sequence spaces `ℓ^q` and makes its norm and the
action of its functionals accessible through coordinates.

## Main declarations

* `ContinuousLinearMap.hasSum_lp_single_mul`: every continuous linear functional on `ℓ^q`,
  `q < ∞`, is given by its coordinate series.
* `ContinuousLinearMap.sum_norm_lp_single_rpow_le`: for `1 < q < ∞`, the coordinate values of a
  functional on `ℓ^q` have finite partial sums of `p`-th powers of norms bounded by the `p`-th
  power of its norm.
* `lp.dualEquiv`: the isometric equivalence `ℓᵖ ≃ₗᵢ (ℓ^q)*`.
* `ContinuousLinearMap.norm_eq_ciSup_norm_lp_single`: the norm of a functional on ℓ¹ is the
  supremum of the norms of its coordinate values.
* `ContinuousLinearMap.norm_rpow_eq_tsum_norm_lp_single_rpow`: for `1 < q < ∞`, the `p`-th
  power of the norm of a functional on `ℓ^q` is the sum of the `p`-th powers of the norms of its
  coordinate values.

## References

* F. Albiac and N. J. Kalton, *Topics in Banach Space Theory*, Chapter 1.
-/

public section

noncomputable section

open scoped ENNReal ComplexConjugate

namespace ContinuousLinearMap

variable {𝕜 ι : Type*} [NontriviallyNormedField 𝕜] [DecidableEq ι] {q : ℝ≥0∞} [Fact (1 ≤ q)]

/-- The value of a continuous linear functional on `ℓ^q` at a unit coordinate vector has norm at
most the norm of the functional. -/
theorem norm_apply_lp_single_le (f : StrongDual 𝕜 (lp (fun _ : ι ↦ 𝕜) q)) (i : ι) :
    ‖f (lp.single q i 1)‖ ≤ ‖f‖ := by
  simpa [lp.norm_single (zero_lt_one.trans_le Fact.out)] using
    f.le_opNorm (lp.single q i (1 : 𝕜))

/-- Every continuous linear functional on `ℓ^q`, `q < ∞`, is given by its coordinate series. -/
theorem hasSum_lp_single_mul (hq : q ≠ ∞) (f : StrongDual 𝕜 (lp (fun _ : ι ↦ 𝕜) q))
    (x : lp (fun _ : ι ↦ 𝕜) q) :
    HasSum (fun i ↦ f (lp.single q i 1) * x i) (f x) := by
  convert (lp.hasSum_single hq x).map f f.continuous using 1
  ext i
  simp only [Function.comp_apply]
  simpa [← lp.single_smul, mul_comm] using
    (f.map_smul (x i) (lp.single q i 1)).symm

end ContinuousLinearMap

namespace ContinuousLinearMap

variable {𝕜 ι : Type*} [RCLike 𝕜] [DecidableEq ι] {p q : ℝ≥0∞} [Fact (1 ≤ q)]
  [p.HolderConjugate q]

/-- For Hölder conjugate exponents `1 < p, q < ∞`, the values of a continuous linear functional
`f` on `ℓ^q` at the unit coordinate vectors `eᵢ` satisfy `∑ i ∈ s, ‖f eᵢ‖ ^ p ≤ ‖f‖ ^ p` on
every finite set `s`. -/
theorem sum_norm_lp_single_rpow_le (hp : p ≠ ∞) (hq : q ≠ ∞)
    (f : StrongDual 𝕜 (lp (fun _ : ι ↦ 𝕜) q)) (s : Finset ι) :
    ∑ i ∈ s, ‖f (lp.single q i 1)‖ ^ p.toReal ≤ ‖f‖ ^ p.toReal := by
  have h := ENNReal.HolderConjugate.toReal_of_ne_top hp hq
  have hp₀ : 0 < p.toReal := h.pos
  have hq₁ : 1 < q.toReal := h.symm.lt
  set c : ι → 𝕜 := fun i ↦ f (lp.single q i 1)
  -- Test `f` against the extremal vector with coordinates `conj (c i) * ‖c i‖ ^ (p - 2)` on `s`.
  set x : ι → 𝕜 := fun i ↦ conj (c i) * ((‖c i‖ ^ (p.toReal - 2) : ℝ) : 𝕜)
  have hcx (i : ι) : c i * x i = ((‖c i‖ ^ p.toReal : ℝ) : 𝕜) := by
    rcases eq_or_ne (c i) 0 with hc | hc
    · simp [x, hc, Real.zero_rpow hp₀.ne']
    · rw [← mul_assoc, RCLike.mul_conj, ← RCLike.ofReal_pow, ← RCLike.ofReal_mul,
        ← Real.rpow_two, ← Real.rpow_add (norm_pos_iff.2 hc), add_sub_cancel]
  have hx (i : ι) : ‖x i‖ ^ q.toReal = ‖c i‖ ^ p.toReal := by
    rcases eq_or_ne (c i) 0 with hc | hc
    · simp [x, hc, Real.zero_rpow hp₀.ne', Real.zero_rpow (zero_lt_one.trans hq₁).ne']
    · have hc' := norm_pos_iff.2 hc
      have he : ‖c i‖ * ‖c i‖ ^ (p.toReal - 2) = ‖c i‖ ^ (p.toReal - 1) := by
        rw [mul_comm, ← Real.rpow_add_one hc'.ne']
        congr 1
        ring
      rw [norm_mul, RCLike.norm_conj, RCLike.norm_ofReal, abs_of_nonneg (by positivity), he,
        ← Real.rpow_mul hc'.le, h.sub_one_mul_conj]
  set v : lp (fun _ : ι ↦ 𝕜) q := ∑ i ∈ s, lp.single q i (x i)
  set S := ∑ i ∈ s, ‖c i‖ ^ p.toReal
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ ↦ by positivity
  have hv : ‖v‖ ^ q.toReal = S := by
    rw [lp.norm_sum_single (zero_lt_one.trans hq₁)]
    exact Finset.sum_congr rfl fun i _ ↦ hx i
  have hfx (i : ι) : f (lp.single q i (x i)) = c i * x i := by
    have hsingle : lp.single (E := fun _ : ι ↦ 𝕜) q i (x i) = x i • lp.single q i 1 := by
      rw [← lp.single_smul, smul_eq_mul, mul_one]
    rw [hsingle, map_smul, smul_eq_mul, mul_comm]
  have hfv : f v = (S : 𝕜) := by
    simp [v, S, map_sum, hfx, hcx]
  have hSv : ‖v‖ ^ q.toReal ≤ ‖f‖ * ‖v‖ := by
    rw [hv]
    simpa [hfv, abs_of_nonneg hS] using f.le_opNorm v
  -- From `‖v‖ ^ q ≤ ‖f‖ ‖v‖` deduce `‖v‖ ^ (q - 1) ≤ ‖f‖`, then raise to the power `p`.
  rcases (norm_nonneg v).eq_or_lt with hv₀ | hv₀
  · rw [← hv, ← hv₀, Real.zero_rpow (zero_lt_one.trans hq₁).ne']
    positivity
  have hle : ‖v‖ ^ (q.toReal - 1) ≤ ‖f‖ := by
    rw [Real.rpow_sub_one hv₀.ne', div_le_iff₀ hv₀]
    exact hSv
  calc S = (‖v‖ ^ (q.toReal - 1)) ^ p.toReal := by
        rw [← Real.rpow_mul hv₀.le, h.symm.sub_one_mul_conj, hv]
    _ ≤ ‖f‖ ^ p.toReal := Real.rpow_le_rpow (by positivity) hle hp₀.le

end ContinuousLinearMap

namespace lp

variable {𝕜 ι : Type*} [RCLike 𝕜] {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
  [p.HolderConjugate q]

section Coordinates

variable [DecidableEq ι]

/-- The coordinate values of a functional on `ℓ^q`, `q < ∞`, form an `ℓᵖ` family. -/
private theorem memℓp_lp_single (hq : q ≠ ∞) (f : StrongDual 𝕜 (lp (fun _ : ι ↦ 𝕜) q)) :
    Memℓp (fun i ↦ f (lp.single q i 1)) p := by
  rcases eq_or_ne p ∞ with rfl | hp
  · refine memℓp_infty ⟨‖f‖, ?_⟩
    rintro _ ⟨i, rfl⟩
    exact f.norm_apply_lp_single_le i
  · exact memℓp_gen' (f.sum_norm_lp_single_rpow_le hp hq)

/-- An `ℓᵖ` family of coordinate values of a functional on `ℓ^q`, `q < ∞`, has norm at most the
norm of the functional. -/
private theorem norm_le_of_forall_eq_lp_single (hq : q ≠ ∞)
    (f : StrongDual 𝕜 (lp (fun _ : ι ↦ 𝕜) q)) (a : lp (fun _ : ι ↦ 𝕜) p)
    (ha : ∀ i, a i = f (lp.single q i 1)) : ‖a‖ ≤ ‖f‖ := by
  rcases eq_or_ne p ∞ with rfl | hp
  · exact norm_le_of_forall_le (norm_nonneg f) fun i ↦ ha i ▸ f.norm_apply_lp_single_le i
  · have hp₀ : 0 < p.toReal := ENNReal.toReal_pos (ENNReal.HolderConjugate.ne_zero p q) hp
    refine norm_le_of_forall_sum_le hp₀ (norm_nonneg f) fun s ↦ ?_
    simpa only [ha] using f.sum_norm_lp_single_rpow_le hp hq s

end Coordinates

variable (𝕜 ι p q)

/-- The isometric duality between `ℓᵖ` and the continuous dual of `ℓ^q`, for Hölder conjugate
exponents `p` and `q` with `q < ∞`. It sends `a` to the functional `x ↦ ∑' i, a i * x i`. -/
def dualEquiv (hq : q ≠ ∞) :
    lp (fun _ : ι ↦ 𝕜) p ≃ₗᵢ[𝕜] StrongDual 𝕜 (lp (fun _ : ι ↦ 𝕜) q) := by
  classical
  have hmul : ‖ContinuousLinearMap.mul 𝕜 𝕜‖ ≤ ((1 : NNReal) : ℝ) := by
    simpa only [NNReal.coe_one] using ContinuousLinearMap.opNorm_mul_le 𝕜 𝕜
  let P : lp (fun _ : ι ↦ 𝕜) p →L[𝕜] StrongDual 𝕜 (lp (fun _ : ι ↦ 𝕜) q) :=
    dualPairing (𝕜 := 𝕜) p q (fun _ : ι ↦ ContinuousLinearMap.mul 𝕜 𝕜) (fun _ ↦ hmul)
  have hP (a : lp (fun _ : ι ↦ 𝕜) p) (i : ι) : P a (lp.single q i 1) = a i := by
    simp only [P, dualPairing_apply, ContinuousLinearMap.mul_apply', lp.single_apply,
      Pi.single_apply, mul_ite, mul_one, mul_zero, tsum_ite_eq]
  have hnorm (a : lp (fun _ : ι ↦ 𝕜) p) : ‖P a‖ = ‖a‖ := by
    refine le_antisymm ((P.le_opNorm a).trans ?_)
      (norm_le_of_forall_eq_lp_single hq (P a) a fun i ↦ (hP a i).symm)
    simpa using mul_le_mul_of_nonneg_right
      (norm_dualPairing (p := p) (q := q) (fun _ : ι ↦ ContinuousLinearMap.mul 𝕜 𝕜)
        (fun _ ↦ hmul)) (norm_nonneg a)
  refine LinearIsometryEquiv.ofSurjective { P.toLinearMap with norm_map' := hnorm } fun f ↦ ?_
  refine ⟨⟨fun i ↦ f (lp.single q i 1), memℓp_lp_single hq f⟩, ContinuousLinearMap.ext fun x ↦ ?_⟩
  simp only [LinearIsometry.coe_mk, ContinuousLinearMap.coe_coe, P, dualPairing_apply,
    ContinuousLinearMap.mul_apply']
  exact (f.hasSum_lp_single_mul hq x).tsum_eq

variable {𝕜 ι p q}

/-- The forward duality map is the scalar series pairing. -/
theorem dualEquiv_apply (hq : q ≠ ∞) (a : lp (fun _ : ι ↦ 𝕜) p) (x : lp (fun _ : ι ↦ 𝕜) q) :
    dualEquiv 𝕜 ι p q hq a x = ∑' i, a i * x i := by
  rfl

variable [DecidableEq ι]

/-- On a coordinate vector, the functional of an `ℓᵖ` family is multiplication by that
coordinate. -/
@[simp]
theorem dualEquiv_apply_single (hq : q ≠ ∞) (a : lp (fun _ : ι ↦ 𝕜) p) (i : ι) (z : 𝕜) :
    dualEquiv 𝕜 ι p q hq a (lp.single q i z) = a i * z := by
  simp [dualEquiv_apply, lp.single_apply, Pi.single_apply]

/-- The inverse duality map records a functional's values on the unit coordinate vectors. -/
@[simp]
theorem dualEquiv_symm_apply (hq : q ≠ ∞) (f : StrongDual 𝕜 (lp (fun _ : ι ↦ 𝕜) q))
    (i : ι) : (dualEquiv 𝕜 ι p q hq).symm f i = f (lp.single q i 1) := by
  have h := congrArg (fun g : StrongDual 𝕜 (lp (fun _ : ι ↦ 𝕜) q) ↦
    g (lp.single q i 1)) ((dualEquiv 𝕜 ι p q hq).apply_symm_apply f)
  rwa [dualEquiv_apply_single, mul_one] at h

end lp

namespace ContinuousLinearMap

variable {𝕜 ι : Type*} [RCLike 𝕜] [DecidableEq ι] {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
  [p.HolderConjugate q]

/-- For Hölder conjugate exponents `1 < p, q < ∞`, the `p`-th power of the norm of a functional
on `ℓ^q` is the sum of the `p`-th powers of the norms of its coordinate values. -/
theorem norm_rpow_eq_tsum_norm_lp_single_rpow (hp : p ≠ ∞) (hq : q ≠ ∞)
    (f : StrongDual 𝕜 (lp (fun _ : ι ↦ 𝕜) q)) :
    ‖f‖ ^ p.toReal = ∑' i, ‖f (lp.single q i 1)‖ ^ p.toReal := by
  rw [← (lp.dualEquiv 𝕜 ι p q hq).symm.norm_map f,
    lp.norm_rpow_eq_tsum (ENNReal.toReal_pos (ENNReal.HolderConjugate.ne_zero p q) hp)]
  simp only [lp.dualEquiv_symm_apply]

/-- The norm of a functional on ℓ¹ is the supremum of the norms of its coordinate values. -/
theorem norm_eq_ciSup_norm_lp_single (f : StrongDual 𝕜 (lp (fun _ : ι ↦ 𝕜) 1)) :
    ‖f‖ = ⨆ i, ‖f (lp.single 1 i 1)‖ := by
  rw [← (lp.dualEquiv 𝕜 ι ∞ 1 ENNReal.one_ne_top).symm.norm_map f, lp.norm_eq_ciSup]
  simp only [lp.dualEquiv_symm_apply]

end ContinuousLinearMap

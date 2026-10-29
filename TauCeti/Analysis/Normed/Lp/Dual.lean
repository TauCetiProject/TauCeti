/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The continuous duals of `ℓᵖ` for `1 ≤ p < ∞`

Over real or complex scalars, the pairing `∑' i, a i * x i` identifies `ℓᑫ` with the continuous
dual of `ℓᵖ`, isometrically, for Hölder conjugate exponents `p` and `q` with `p` finite:

* `lp.dualOneEquiv`: bounded families are the continuous dual of `ℓ¹`;
* `lp.dualEquiv`: for `1 < p < ∞`, `ℓᑫ` is the continuous dual of `ℓᵖ`.

The inverses record the coordinate values of a functional. The index type is arbitrary,
including empty and uncountable types; no enumeration is chosen.

Both equivalences use Mathlib's `lp.dualPairing` for the pairing and `lp.hasSum_single` for the
coordinate expansion. The pairing is bilinear, including over complex scalars: the coefficients
of a functional are its values on coordinate vectors, without conjugation. For `1 < p < ∞`, the
`ℓᑫ` norm of these coefficients is bounded by testing the functional against the finitely
supported vectors with coordinates `conj aᵢ * ‖aᵢ‖ ^ (q - 2)`.

These identifications describe the duals of the sequence spaces and make their norms and the
action of their functionals accessible through coordinates.

## References

* F. Albiac and N. J. Kalton, *Topics in Banach Space Theory*, Chapter 1.
-/

public section

noncomputable section

open scoped ENNReal ComplexConjugate

namespace ContinuousLinearMap

variable {𝕜 ι : Type*} [NontriviallyNormedField 𝕜] [DecidableEq ι] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A continuous linear functional on `ℓᵖ` maps the coordinate vector `lp.single p i z` to `z`
times its value on `lp.single p i 1`. -/
theorem apply_lp_single (f : StrongDual 𝕜 (lp (fun _ : ι ↦ 𝕜) p)) (i : ι) (z : 𝕜) :
    f (lp.single p i z) = z * f (lp.single p i 1) := by
  simpa [← lp.single_smul] using f.map_smul z (lp.single p i 1)

/-- For finite `p`, every continuous linear functional on `ℓᵖ` is given by its coordinate
series. -/
theorem hasSum_lp_single_mul (hp : p ≠ ∞) (f : StrongDual 𝕜 (lp (fun _ : ι ↦ 𝕜) p))
    (x : lp (fun _ : ι ↦ 𝕜) p) :
    HasSum (fun i ↦ f (lp.single p i 1) * x i) (f x) := by
  convert (lp.hasSum_single hp x).map f f.continuous using 1
  ext i
  rw [Function.comp_apply, f.apply_lp_single i (x i), mul_comm]

end ContinuousLinearMap

namespace lp

variable {𝕜 ι : Type*} [RCLike 𝕜] {p q : ℝ≥0∞} [Fact (1 ≤ p)] [p.HolderConjugate q]

/-- Testing a continuous linear functional `f` on `ℓᵖ`, for Hölder conjugate finite exponents
`p` and `q`, against the vector with coordinates `conj aᵢ * ‖aᵢ‖ ^ (q - 2)` on a finite set `s`,
where `aᵢ = f eᵢ`, bounds the finite `ℓᑫ` sums of its coordinate values by `‖f‖ ^ q`. -/
private theorem sum_norm_lp_single_rpow_le [DecidableEq ι] (hp : p ≠ ∞) (hq : q ≠ ∞)
    (f : StrongDual 𝕜 (lp (fun _ : ι ↦ 𝕜) p)) (s : Finset ι) :
    ∑ i ∈ s, ‖f (lp.single p i 1)‖ ^ q.toReal ≤ ‖f‖ ^ q.toReal := by
  have hpq := ENNReal.HolderConjugate.toReal_of_ne_top hp hq
  have hp₀ : 0 < p.toReal := hpq.pos
  have hq₀ : 0 < q.toReal := hpq.symm.pos
  set a : ι → 𝕜 := fun i ↦ f (lp.single p i 1)
  let c : ι → 𝕜 := fun i ↦ conj (a i) * ((‖a i‖ ^ (q.toReal - 2) : ℝ) : 𝕜)
  have hca (i : ι) : c i * a i = ((‖a i‖ ^ q.toReal : ℝ) : 𝕜) := by
    rcases eq_or_ne (a i) 0 with h | h
    · simp [c, h, Real.zero_rpow hq₀.ne']
    · rw [show q.toReal = 2 + (q.toReal - 2) by ring, Real.rpow_add (norm_pos_iff.2 h),
        Real.rpow_two]
      simp only [c]
      rw [mul_right_comm, RCLike.conj_mul]
      push_cast
      ring
  have hc (i : ι) : ‖c i‖ ^ p.toReal = ‖a i‖ ^ q.toReal := by
    rcases eq_or_ne (a i) 0 with h | h
    · simp [c, h, Real.zero_rpow hp₀.ne', Real.zero_rpow hq₀.ne']
    · have h₀ : 0 < ‖a i‖ := norm_pos_iff.2 h
      have : ‖c i‖ = ‖a i‖ ^ (q.toReal - 1) := by
        rw [show q.toReal - 1 = 1 + (q.toReal - 2) by ring, Real.rpow_add h₀, Real.rpow_one]
        simp [c, abs_of_pos (Real.rpow_pos_of_pos h₀ _)]
      rw [this, ← Real.rpow_mul h₀.le, hpq.symm.sub_one_mul_conj]
  set S := ∑ i ∈ s, ‖a i‖ ^ q.toReal
  let x : lp (fun _ : ι ↦ 𝕜) p := ∑ i ∈ s, lp.single p i (c i)
  have hx : ‖x‖ ^ p.toReal = S := by
    rw [lp.norm_sum_single hp₀]
    exact Finset.sum_congr rfl fun i _ ↦ hc i
  have hSx : S ≤ ‖f‖ * ‖x‖ := by
    have hfx : f x = (S : 𝕜) := by
      simp only [x, map_sum, S]
      exact Finset.sum_congr rfl fun i _ ↦ by rw [f.apply_lp_single i (c i), hca]
    have hS : 0 ≤ S := Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (norm_nonneg _) _
    simpa [hfx, RCLike.norm_ofReal, abs_of_nonneg hS] using f.le_opNorm x
  -- Write `S = ‖x‖ ^ p`, so `S ≤ ‖f‖ ‖x‖` gives `‖x‖ ^ (p - 1) ≤ ‖f‖`, and `(p - 1) q = p`.
  rcases (norm_nonneg x).eq_or_lt with hx₀ | hx₀
  · rw [← hx, ← hx₀, Real.zero_rpow hp₀.ne']
    exact Real.rpow_nonneg (norm_nonneg f) _
  have hxf : ‖x‖ ^ (p.toReal - 1) ≤ ‖f‖ := by
    refine le_of_mul_le_mul_right ?_ hx₀
    rwa [← Real.rpow_add_one hx₀.ne', sub_add_cancel, hx]
  calc S = (‖x‖ ^ (p.toReal - 1)) ^ q.toReal := by
        rw [← Real.rpow_mul (norm_nonneg x), hpq.sub_one_mul_conj, hx]
    _ ≤ ‖f‖ ^ q.toReal := by gcongr

variable [Fact (1 ≤ q)]

/-- The scalar series pairing of `ℓᑫ` with `ℓᵖ`, for finite `p`, is an isometric equivalence
onto the continuous dual of `ℓᵖ` as soon as the coordinate values of every functional form an
`ℓᑫ` family whose norm is at most that of the functional. -/
private def dualEquivOfForallNormLe [DecidableEq ι] (hp : p ≠ ∞)
    (h : ∀ f : StrongDual 𝕜 (lp (fun _ : ι ↦ 𝕜) p), ∃ a : lp (fun _ : ι ↦ 𝕜) q,
      (∀ i, a i = f (lp.single p i 1)) ∧ ‖a‖ ≤ ‖f‖) :
    lp (fun _ : ι ↦ 𝕜) q ≃ₗᵢ[𝕜] StrongDual 𝕜 (lp (fun _ : ι ↦ 𝕜) p) := by
  have hmul : ‖ContinuousLinearMap.mul 𝕜 𝕜‖ ≤ ((1 : NNReal) : ℝ) := by
    simpa only [NNReal.coe_one] using ContinuousLinearMap.opNorm_mul_le 𝕜 𝕜
  let P : lp (fun _ : ι ↦ 𝕜) q →L[𝕜] StrongDual 𝕜 (lp (fun _ : ι ↦ 𝕜) p) :=
    dualPairing (𝕜 := 𝕜) q p (fun _ : ι ↦ ContinuousLinearMap.mul 𝕜 𝕜) (fun _ ↦ hmul)
  have hP (a : lp (fun _ : ι ↦ 𝕜) q) (i : ι) : P a (lp.single p i 1) = a i := by
    simp only [P, dualPairing_apply, ContinuousLinearMap.mul_apply', lp.single_apply,
      Pi.single_apply, mul_ite, mul_one, mul_zero, tsum_ite_eq]
  have hnorm (a : lp (fun _ : ι ↦ 𝕜) q) : ‖P a‖ = ‖a‖ := by
    apply le_antisymm
    · exact (P.le_opNorm a).trans (by
        simpa using mul_le_mul_of_nonneg_right
          (norm_dualPairing (p := q) (q := p)
            (fun _ : ι ↦ ContinuousLinearMap.mul 𝕜 𝕜) (fun _ ↦ hmul)) (norm_nonneg a))
    · obtain ⟨b, hb, hbf⟩ := h (P a)
      have hba : b = a := lp.ext <| funext fun i ↦ (hb i).trans (hP a i)
      exact hba ▸ hbf
  refine LinearIsometryEquiv.ofSurjective
    { P.toLinearMap with norm_map' := hnorm } ?_
  intro f
  obtain ⟨a, ha, -⟩ := h f
  refine ⟨a, ContinuousLinearMap.ext fun x ↦ ?_⟩
  simp only [LinearIsometry.coe_mk, ContinuousLinearMap.coe_coe, P, dualPairing_apply,
    ContinuousLinearMap.mul_apply', ha]
  exact (f.hasSum_lp_single_mul hp x).tsum_eq

variable (𝕜 ι)

/-- The isometric duality between bounded scalar families and the continuous dual of ℓ¹.
It sends `a` to the functional `x ↦ ∑' i, a i * x i`. -/
def dualOneEquiv : lp (fun _ : ι ↦ 𝕜) ∞ ≃ₗᵢ[𝕜] StrongDual 𝕜 (lp (fun _ : ι ↦ 𝕜) 1) := by
  classical
  refine dualEquivOfForallNormLe ENNReal.one_ne_top fun f ↦ ?_
  have hbound (i : ι) : ‖f (lp.single 1 i (1 : 𝕜))‖ ≤ ‖f‖ := by
    simpa [lp.norm_single] using f.le_opNorm (lp.single 1 i (1 : 𝕜))
  exact ⟨⟨fun i ↦ f (lp.single 1 i 1), memℓp_infty ⟨‖f‖, by
    rintro _ ⟨i, rfl⟩
    exact hbound i⟩⟩, fun _ ↦ rfl, norm_le_of_forall_le (norm_nonneg f) hbound⟩

variable (p q) in
/-- For Hölder conjugate exponents `1 < p, q < ∞`, the isometric duality between `ℓᑫ` and the
continuous dual of `ℓᵖ`. It sends `a` to the functional `x ↦ ∑' i, a i * x i`. -/
def dualEquiv (hp : p ≠ ∞) (hq : q ≠ ∞) :
    lp (fun _ : ι ↦ 𝕜) q ≃ₗᵢ[𝕜] StrongDual 𝕜 (lp (fun _ : ι ↦ 𝕜) p) := by
  classical
  have hq₀ : 0 < q.toReal := (ENNReal.HolderConjugate.toReal_of_ne_top hp hq).symm.pos
  refine dualEquivOfForallNormLe hp fun f ↦ ?_
  exact ⟨⟨fun i ↦ f (lp.single p i 1), memℓp_gen' (sum_norm_lp_single_rpow_le hp hq f)⟩,
    fun _ ↦ rfl, norm_le_of_forall_sum_le hq₀ (norm_nonneg f) (sum_norm_lp_single_rpow_le hp hq f)⟩

variable {𝕜 ι}

/-- The forward duality map is the scalar series pairing. -/
theorem dualOneEquiv_apply (a : lp (fun _ : ι ↦ 𝕜) ∞) (x : lp (fun _ : ι ↦ 𝕜) 1) :
    dualOneEquiv 𝕜 ι a x = ∑' i, a i * x i := by
  rfl

/-- The forward duality map is the scalar series pairing. -/
theorem dualEquiv_apply (hp : p ≠ ∞) (hq : q ≠ ∞) (a : lp (fun _ : ι ↦ 𝕜) q)
    (x : lp (fun _ : ι ↦ 𝕜) p) :
    dualEquiv 𝕜 ι p q hp hq a x = ∑' i, a i * x i := by
  rfl

variable [DecidableEq ι]

/-- On a coordinate vector, a bounded family's functional is multiplication by that coordinate. -/
@[simp]
theorem dualOneEquiv_apply_single (a : lp (fun _ : ι ↦ 𝕜) ∞) (i : ι) (z : 𝕜) :
    dualOneEquiv 𝕜 ι a (lp.single 1 i z) = a i * z := by
  simp [dualOneEquiv_apply, lp.single_apply, Pi.single_apply]

/-- On a coordinate vector, the functional of an `ℓᑫ` family is multiplication by that
coordinate. -/
@[simp]
theorem dualEquiv_apply_single (hp : p ≠ ∞) (hq : q ≠ ∞) (a : lp (fun _ : ι ↦ 𝕜) q) (i : ι)
    (z : 𝕜) : dualEquiv 𝕜 ι p q hp hq a (lp.single p i z) = a i * z := by
  simp [dualEquiv_apply, lp.single_apply, Pi.single_apply]

end lp

namespace ContinuousLinearMap

variable {𝕜 ι : Type*} [RCLike 𝕜] [DecidableEq ι]

/-- The inverse duality map records a functional's values on the unit coordinate vectors. -/
@[simp]
theorem lp_dualOneEquiv_symm_apply (f : StrongDual 𝕜 (lp (fun _ : ι ↦ 𝕜) 1)) (i : ι) :
    (lp.dualOneEquiv 𝕜 ι).symm f i = f (lp.single 1 i 1) := by
  have h := congrArg (fun g : StrongDual 𝕜 (lp (fun _ : ι ↦ 𝕜) 1) ↦
    g (lp.single 1 i 1)) ((lp.dualOneEquiv 𝕜 ι).apply_symm_apply f)
  rwa [lp.dualOneEquiv_apply_single, mul_one] at h

/-- The norm of a functional on ℓ¹ is the supremum of the norms of its coordinate values. -/
theorem norm_eq_ciSup_norm_lp_single (f : StrongDual 𝕜 (lp (fun _ : ι ↦ 𝕜) 1)) :
    ‖f‖ = ⨆ i, ‖f (lp.single 1 i 1)‖ := by
  rw [← (lp.dualOneEquiv 𝕜 ι).symm.norm_map f, lp.norm_eq_ciSup]
  simp only [lp_dualOneEquiv_symm_apply]

variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]

/-- The inverse duality map records a functional's values on the unit coordinate vectors. -/
@[simp]
theorem lp_dualEquiv_symm_apply (hp : p ≠ ∞) (hq : q ≠ ∞)
    (f : StrongDual 𝕜 (lp (fun _ : ι ↦ 𝕜) p)) (i : ι) :
    (lp.dualEquiv 𝕜 ι p q hp hq).symm f i = f (lp.single p i 1) := by
  have h := congrArg (fun g : StrongDual 𝕜 (lp (fun _ : ι ↦ 𝕜) p) ↦
    g (lp.single p i 1)) ((lp.dualEquiv 𝕜 ι p q hp hq).apply_symm_apply f)
  rwa [lp.dualEquiv_apply_single, mul_one] at h

/-- For Hölder conjugate exponents `1 < p, q < ∞`, the norm of a functional on `ℓᵖ` is the `ℓᑫ`
norm of its coordinate values. -/
theorem norm_eq_tsum_norm_lp_single_rpow (hp : p ≠ ∞) (hq : q ≠ ∞)
    (f : StrongDual 𝕜 (lp (fun _ : ι ↦ 𝕜) p)) :
    ‖f‖ = (∑' i, ‖f (lp.single p i 1)‖ ^ q.toReal) ^ (1 / q.toReal) := by
  have hq₀ : 0 < q.toReal := (ENNReal.HolderConjugate.toReal_of_ne_top hp hq).symm.pos
  rw [← (lp.dualEquiv 𝕜 ι p q hp hq).symm.norm_map f, lp.norm_eq_tsum_rpow hq₀]
  simp only [lp_dualEquiv_symm_apply]

end ContinuousLinearMap

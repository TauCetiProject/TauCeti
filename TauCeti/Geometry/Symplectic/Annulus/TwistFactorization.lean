/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Topology.Algebra.Module.Determinant
public import TauCeti.Geometry.Symplectic.StripShear
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Topology.UniformSpace.HeineCantor
import TauCeti.Analysis.Normed.Operator.Prod
import TauCeti.Topology.Algebra.Module.Determinant

/-!
# Twist factorization of maps of the strip with near-identity derivative

Let `R_c(x, y) = (x + c y, y)` be the shear of the plane `ℝ × ℝ` with twist `c`
(`TauCeti.stripShear c`). For `c > 0` it is a positive twist map: writing `X` for the first
component of a map, `R_c` has `∂ₓ X = 1 > 0` and `∂_y X = c > 0`.

Every map `H` of the strip is `R_c ∘ N` for `N = R_c⁻¹ ∘ H`. This file shows that where the
derivative of `H` is close to the identity, the first component `X` of `N` has the derivative
signs of a *negative* twist map, `∂ₓ X > 0` and `∂_y X < 0`. Precisely, if `‖DH(q) - 1‖ ≤ δ` then
the first component of `N` satisfies

`∂ₓ X ≥ 1 - δ (1 + c)` and `∂_y X ≤ δ (1 + c) - c`

at `q` (`TauCeti.one_sub_mul_le_fderiv_stripShear_symm_comp_apply_fst`,
`TauCeti.fderiv_stripShear_symm_comp_apply_fst_le`), so both signs are strict once
`δ (1 + c) < min 1 c`. These follow from the formula `∂X - c ∂Y` for the derivative of the first
component of `N`, where `(X, Y)` are the components of `H`
(`TauCeti.fderiv_stripShear_symm_comp_apply_fst`). The factor `N` has the same Jacobian
determinant as `H` (`TauCeti.det_fderiv_stripShear_symm_comp`). Since
`R_c⁻¹ = R_(-c)` (`TauCeti.stripShear_symm`) leaves second coordinates unchanged
(`TauCeti.stripShear_symm_apply`) and commutes with the deck translation
(`TauCeti.stripShear_add_fst`), `N` maps each boundary line of the strip into itself and commutes
with the deck translation whenever `H` does.

The second half supplies the smallness. Let `t ↦ h_t`, `t ∈ [0, 1]`, be a path of maps of the
plane whose derivatives `Dh_t(p)` are jointly continuous and invertible over the unit square and
periodic under `(x, y) ↦ (x + 1, y)`, as for the lifts to the strip of an isotopy of the annulus.
For `s, t ∈ [0, 1]` an *increment* is a map `H` with `H ∘ h_s = h_t` near a point `p`, for
instance `h_t ∘ h_s⁻¹`. Its derivative at `h_s(p)` is `Dh_t(p) Dh_s(p)⁻¹`, and uniform
continuity on the compact set of times and points of the unit square makes it uniformly close to
the identity when `|t - s|` is small (`TauCeti.exists_pos_forall_norm_fderiv_sub_one_lt`).
Hence for every `c > 0` there is a mesh below which every increment `H` is `R_c ∘ N` where the
first component of `N = R_c⁻¹ ∘ H` has `∂ₓ X > 0` and `∂_y X < 0` at every point `h_s(p)` with
`p` in the strip (`TauCeti.exists_pos_forall_fderiv_stripShear_symm_comp_apply_fst_pos_and_neg`),
and in particular one uniform partition `t_j = j / K` of `[0, 1]` works for all its increments
(`TauCeti.exists_pos_forall_lt_fderiv_stripShear_symm_comp_div_apply_fst_pos_and_neg`). This is
the intended use: when the maps `h_t` preserve the strip, composing the increments writes the
time-one map `h_1 ∘ h_0⁻¹` as a composition of `2K` maps alternating between the factors `N_j`
and the shear `R_c`, whose derivatives have these signs. Such factors are the ones whose generating
functions enter the finite-dimensional action of the generating-function proof of the
Poincaré–Birkhoff theorem.

The shear `R_c` must be fixed relative to the size of the increments: for the increment
`H(x, y) = (x + (2y - 1) / 8, y)`, the factor `R_c⁻¹ ∘ H` has `∂_y X = 1 / 4 - c`, which is
negative for `c = 1` but positive for `c = 1 / 8` (see the examples at the end of the file).

## Main results

* `TauCeti.fderiv_stripShear_symm_comp_apply_fst`: the first component of the derivative of
  `R_c⁻¹ ∘ H`.
* `TauCeti.one_sub_mul_le_fderiv_stripShear_symm_comp_apply_fst`,
  `TauCeti.fderiv_stripShear_symm_comp_apply_fst_le`: the twist bounds of `R_c⁻¹ ∘ H` at a point
  where the derivative of `H` is within `δ` of the identity.
* `TauCeti.exists_pos_forall_norm_fderiv_sub_one_lt`: increments of a `C¹` path of maps of the
  strip over short time intervals have derivative uniformly close to the identity.
* `TauCeti.exists_pos_forall_fderiv_stripShear_symm_comp_apply_fst_pos_and_neg`,
  `TauCeti.exists_pos_forall_lt_fderiv_stripShear_symm_comp_div_apply_fst_pos_and_neg`: the finite
  twist factorization: the first component of each factor `R_c⁻¹ ∘ H` has `∂ₓ X > 0` and
  `∂_y X < 0` at `h_s(p)`.

## References

* C. Conley and E. Zehnder, *The Birkhoff–Lewis fixed point theorem and a conjecture of
  V. I. Arnold*, Invent. Math. 73 (1983), 33–49.
-/

public section

noncomputable section

open Filter Set
open scoped Topology

namespace TauCeti

/-! ### Twist bounds for maps near the identity -/

/-- The first component of the derivative of `R_c⁻¹ ∘ H` is `∂X - c ∂Y`, where `(X, Y)` are the
components of `H`. -/
@[simp]
theorem fderiv_stripShear_symm_comp_apply_fst (c : ℝ) (H : ℝ × ℝ → ℝ × ℝ) (q v : ℝ × ℝ) :
    (fderiv ℝ ((stripShear c).symm ∘ H) q v).1 = (fderiv ℝ H q v).1 - c * (fderiv ℝ H q v).2 := by
  rw [ContinuousLinearEquiv.comp_fderiv, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, stripShear_symm_apply]

/-- The second component of `R_c⁻¹ ∘ H` has the same derivative as that of `H`. -/
@[simp]
theorem fderiv_stripShear_symm_comp_apply_snd (c : ℝ) (H : ℝ × ℝ → ℝ × ℝ) (q v : ℝ × ℝ) :
    (fderiv ℝ ((stripShear c).symm ∘ H) q v).2 = (fderiv ℝ H q v).2 := by
  rw [ContinuousLinearEquiv.comp_fderiv, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, stripShear_symm_apply]

/-- If `‖DH(q) - 1‖ ≤ δ`, the first component `X` of `R_c⁻¹ ∘ H` has
`∂ₓ X ≥ 1 - δ (1 + c)` at `q`. -/
theorem one_sub_mul_le_fderiv_stripShear_symm_comp_apply_fst {H : ℝ × ℝ → ℝ × ℝ} {q : ℝ × ℝ}
    {c δ : ℝ} (hc : 0 ≤ c) (hH : ‖fderiv ℝ H q - 1‖ ≤ δ) :
    1 - δ * (1 + c) ≤ (fderiv ℝ ((stripShear c).symm ∘ H) q (1, 0)).1 := by
  have h₁ := (fderiv ℝ H q).norm_apply_fst_sub_fst_le (1, 0)
  have h₂ := (fderiv ℝ H q).norm_apply_snd_sub_snd_le (1, 0)
  simp only [Prod.norm_mk, norm_one, norm_zero, zero_le_one, sup_of_le_left, mul_one, sub_zero,
    Real.norm_eq_abs] at h₁ h₂
  rw [fderiv_stripShear_symm_comp_apply_fst]
  nlinarith [(abs_le.1 (h₁.trans hH)).1, (abs_le.1 (h₂.trans hH)).2]

/-- If `‖DH(q) - 1‖ ≤ δ`, the first component `X` of `R_c⁻¹ ∘ H` has
`∂_y X ≤ δ (1 + c) - c` at `q`. -/
theorem fderiv_stripShear_symm_comp_apply_fst_le {H : ℝ × ℝ → ℝ × ℝ} {q : ℝ × ℝ} {c δ : ℝ}
    (hc : 0 ≤ c) (hH : ‖fderiv ℝ H q - 1‖ ≤ δ) :
    (fderiv ℝ ((stripShear c).symm ∘ H) q (0, 1)).1 ≤ δ * (1 + c) - c := by
  have h₁ := (fderiv ℝ H q).norm_apply_fst_sub_fst_le (0, 1)
  have h₂ := (fderiv ℝ H q).norm_apply_snd_sub_snd_le (0, 1)
  simp only [Prod.norm_mk, norm_one, norm_zero, zero_le_one, sup_of_le_right, mul_one, sub_zero,
    Real.norm_eq_abs] at h₁ h₂
  rw [fderiv_stripShear_symm_comp_apply_fst]
  nlinarith [(abs_le.1 (h₁.trans hH)).2, (abs_le.1 (h₂.trans hH)).1]

/-- The factor `R_c⁻¹ ∘ H` has the same Jacobian determinant as `H`; in particular it preserves
area wherever `H` does. -/
@[simp]
theorem det_fderiv_stripShear_symm_comp (c : ℝ) (H : ℝ × ℝ → ℝ × ℝ) (q : ℝ × ℝ) :
    (fderiv ℝ ((stripShear c).symm ∘ H) q).det = (fderiv ℝ H q).det := by
  rw [ContinuousLinearEquiv.comp_fderiv, ContinuousLinearMap.det_comp, stripShear_symm,
    det_stripShear, one_mul]

/-! ### Increments of a path of maps of the strip -/

variable {h : ℝ → ℝ × ℝ → ℝ × ℝ}

/-- On the unit square, `Dh_t(p) Dh_s(p)⁻¹` is uniformly close to the identity for `|t - s|`
small. -/
private theorem exists_pos_forall_norm_mul_inverse_sub_one_lt
    (hD : ContinuousOn (fun q : ℝ × ℝ × ℝ ↦ fderiv ℝ (h q.1) q.2)
      (Icc 0 1 ×ˢ (Icc 0 1 ×ˢ Icc 0 1)))
    (hunit : ∀ t ∈ Icc (0 : ℝ) 1, ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
      IsUnit (fderiv ℝ (h t) p))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ η > 0, ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, |t - s| < η →
      ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
        ‖fderiv ℝ (h t) p * Ring.inverse (fderiv ℝ (h s) p) - 1‖ < δ := by
  set S : Set (ℝ × ℝ × (ℝ × ℝ)) := Icc 0 1 ×ˢ (Icc 0 1 ×ˢ (Icc 0 1 ×ˢ Icc 0 1))
  -- `G (s, t, p) = Dh_t(p) Dh_s(p)⁻¹` is continuous on the compact set `S`, and equal to `1`
  -- on its diagonal `s = t`.
  have hcont : ContinuousOn (fun q : ℝ × ℝ × (ℝ × ℝ) ↦
      fderiv ℝ (h q.2.1) q.2.2 * Ring.inverse (fderiv ℝ (h q.1) q.2.2)) S := by
    have hs : ContinuousOn (fun q : ℝ × ℝ × (ℝ × ℝ) ↦ fderiv ℝ (h q.1) q.2.2) S :=
      hD.comp (continuous_fst.prodMk continuous_snd.snd).continuousOn
        fun q (hq : q ∈ S) ↦ ⟨hq.1, hq.2.2⟩
    have hinv : ContinuousOn (fun q : ℝ × ℝ × (ℝ × ℝ) ↦
        Ring.inverse (fderiv ℝ (h q.1) q.2.2)) S := fun q hq ↦ by
      have hu := hunit q.1 hq.1 q.2.2 hq.2.2
      have hi : ContinuousAt Ring.inverse (fderiv ℝ (h q.1) q.2.2) :=
        hu.unit_spec ▸ NormedRing.inverse_continuousAt hu.unit
      exact ContinuousAt.comp_continuousWithinAt (g := Ring.inverse)
        (f := fun q : ℝ × ℝ × (ℝ × ℝ) ↦ fderiv ℝ (h q.1) q.2.2) hi (hs q hq)
    exact (hD.comp continuous_snd.continuousOn fun q (hq : q ∈ S) ↦ hq.2).mul hinv
  have hcompact : IsCompact S :=
    isCompact_Icc.prod (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc))
  obtain ⟨η, hη, hG⟩ :=
    Metric.uniformContinuousOn_iff.1 (hcompact.uniformContinuousOn_of_continuous hcont) δ hδ
  refine ⟨η, hη, fun s hs t ht hst p hp ↦ ?_⟩
  have hd : dist (s, t, p) (s, s, p) < η := by
    rw [Prod.dist_eq, Prod.dist_eq, dist_self, dist_self, Real.dist_eq]
    exact max_lt hη (max_lt hst hη)
  have := hG _ ⟨hs, ht, hp⟩ _ ⟨hs, hs, hp⟩ hd
  rwa [Ring.mul_inverse_cancel _ (hunit s hs p hp), dist_eq_norm] at this

/-- **Increments of a path of maps of the strip have derivative uniformly close to the identity.**
Let `t ↦ h_t` be a path of maps of the plane whose derivatives `Dh_t(p)` depend continuously on
`(t, p)` and are invertible for `t ∈ [0, 1]` and `p` in the unit square, and are invariant under
the deck translation `(x, y) ↦ (x + 1, y)` of the strip `ℝ × [0, 1]`. Then for every `δ > 0`
there is `η > 0` such that for `s, t ∈ [0, 1]` with `|t - s| < η`, every increment `H` with
`H ∘ h_s = h_t` near a point `p` of the strip, differentiable at `h_s(p)`, has
`‖DH(h_s(p)) - 1‖ < δ`. -/
theorem exists_pos_forall_norm_fderiv_sub_one_lt
    (hD : ContinuousOn (fun q : ℝ × ℝ × ℝ ↦ fderiv ℝ (h q.1) q.2)
      (Icc 0 1 ×ˢ (Icc 0 1 ×ˢ Icc 0 1)))
    (hunit : ∀ t ∈ Icc (0 : ℝ) 1, ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
      IsUnit (fderiv ℝ (h t) p))
    (hper : ∀ t ∈ Icc (0 : ℝ) 1, ∀ p : ℝ × ℝ, p.2 ∈ Icc (0 : ℝ) 1 →
      fderiv ℝ (h t) (p + (1, 0)) = fderiv ℝ (h t) p)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ η > 0, ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, |t - s| < η →
      ∀ p : ℝ × ℝ, p.2 ∈ Icc (0 : ℝ) 1 → ∀ H : ℝ × ℝ → ℝ × ℝ,
        DifferentiableAt ℝ H (h s p) → H ∘ h s =ᶠ[𝓝 p] h t →
          ‖fderiv ℝ H (h s p) - 1‖ < δ := by
  obtain ⟨η, hη, hsmall⟩ := exists_pos_forall_norm_mul_inverse_sub_one_lt hD hunit hδ
  refine ⟨η, hη, fun s hs t ht hst p hp H hH hHp ↦ ?_⟩
  -- By periodicity the derivatives at `p` are those at the point `(fract p.1, p.2)` of the
  -- unit square.
  have hfract (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) :
      fderiv ℝ (h r) p = fderiv ℝ (h r) (Int.fract p.1, p.2) := by
    have hP : Function.Periodic (fun x ↦ fderiv ℝ (h r) (x, p.2)) 1 := fun x ↦ by
      have := hper r hr (x, p.2) hp
      rwa [Prod.mk_add_mk, add_zero] at this
    have := hP.sub_int_mul_eq ⌊p.1⌋ (x := p.1)
    rw [mul_one, Int.self_sub_floor] at this
    exact this.symm
  have hsq : (Int.fract p.1, p.2) ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 :=
    ⟨⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩, hp⟩
  have hu : IsUnit (fderiv ℝ (h s) p) := hfract s hs ▸ hunit s hs _ hsq
  -- A unit is nonzero, so `h_s` is differentiable at `p`, and the chain rule identifies the
  -- derivative of the increment with `Dh_t(p) Dh_s(p)⁻¹`.
  have hds : DifferentiableAt ℝ (h s) p := by
    by_contra hnd
    exact not_isUnit_zero (fderiv_zero_of_not_differentiableAt hnd ▸ hu)
  have hchain : fderiv ℝ H (h s p) * fderiv ℝ (h s) p = fderiv ℝ (h t) p := by
    rw [ContinuousLinearMap.mul_def, ← fderiv_comp p hH hds, hHp.fderiv_eq]
  rw [← Ring.mul_inverse_cancel_right _ (fderiv ℝ H (h s p)) hu, hchain, hfract s hs,
    hfract t ht]
  exact hsmall s hs t ht hst _ hsq

/-- **The finite twist factorization.** Under the hypotheses of
`TauCeti.exists_pos_forall_norm_fderiv_sub_one_lt` and for a twist `c > 0`, there is `η > 0`
such that for `s, t ∈ [0, 1]` with `|t - s| < η` every increment `H`, with `H ∘ h_s = h_t` near a
point `p` of the strip, is `R_c ∘ N` where the first component `X` of `N = R_c⁻¹ ∘ H` has
`∂ₓ X > 0` and `∂_y X < 0` at `h_s(p)`. -/
theorem exists_pos_forall_fderiv_stripShear_symm_comp_apply_fst_pos_and_neg
    (hD : ContinuousOn (fun q : ℝ × ℝ × ℝ ↦ fderiv ℝ (h q.1) q.2)
      (Icc 0 1 ×ˢ (Icc 0 1 ×ˢ Icc 0 1)))
    (hunit : ∀ t ∈ Icc (0 : ℝ) 1, ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
      IsUnit (fderiv ℝ (h t) p))
    (hper : ∀ t ∈ Icc (0 : ℝ) 1, ∀ p : ℝ × ℝ, p.2 ∈ Icc (0 : ℝ) 1 →
      fderiv ℝ (h t) (p + (1, 0)) = fderiv ℝ (h t) p)
    {c : ℝ} (hc : 0 < c) :
    ∃ η > 0, ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, |t - s| < η →
      ∀ p : ℝ × ℝ, p.2 ∈ Icc (0 : ℝ) 1 → ∀ H : ℝ × ℝ → ℝ × ℝ,
        DifferentiableAt ℝ H (h s p) → H ∘ h s =ᶠ[𝓝 p] h t →
          0 < (fderiv ℝ ((stripShear c).symm ∘ H) (h s p) (1, 0)).1 ∧
            (fderiv ℝ ((stripShear c).symm ∘ H) (h s p) (0, 1)).1 < 0 := by
  -- Any `δ` with `δ (1 + c) < min 1 c` makes both twist bounds strict.
  set δ := min 1 c / (2 * (1 + c)) with hδ
  have hδpos : 0 < δ := div_pos (lt_min one_pos hc) (by positivity)
  have hδc : δ * (1 + c) = min 1 c / 2 := by
    rw [hδ]
    field_simp
  obtain ⟨η, hη, hsmall⟩ := exists_pos_forall_norm_fderiv_sub_one_lt hD hunit hper hδpos
  refine ⟨η, hη, fun s hs t ht hst p hp H hH hHp ↦ ?_⟩
  have hH' := (hsmall s hs t ht hst p hp H hH hHp).le
  have h₁ := one_sub_mul_le_fderiv_stripShear_symm_comp_apply_fst hc.le hH'
  have h₂ := fderiv_stripShear_symm_comp_apply_fst_le hc.le hH'
  have := min_le_left 1 c
  have := min_le_right 1 c
  constructor <;> linarith

/-- **The finite twist factorization along a uniform partition.** Under the hypotheses of
`TauCeti.exists_pos_forall_norm_fderiv_sub_one_lt` and for a twist `c > 0`, there is `K > 0`
such that for the partition `t_j = j / K` of `[0, 1]`, every increment `H_j`, with
`H_j ∘ h_(t_j) = h_(t_(j+1))` near a point `p` of the strip, is `R_c ∘ N_j` where the first
component `X` of `N_j = R_c⁻¹ ∘ H_j` has `∂ₓ X > 0` and `∂_y X < 0` at `h_(t_j)(p)`. -/
theorem exists_pos_forall_lt_fderiv_stripShear_symm_comp_div_apply_fst_pos_and_neg
    (hD : ContinuousOn (fun q : ℝ × ℝ × ℝ ↦ fderiv ℝ (h q.1) q.2)
      (Icc 0 1 ×ˢ (Icc 0 1 ×ˢ Icc 0 1)))
    (hunit : ∀ t ∈ Icc (0 : ℝ) 1, ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
      IsUnit (fderiv ℝ (h t) p))
    (hper : ∀ t ∈ Icc (0 : ℝ) 1, ∀ p : ℝ × ℝ, p.2 ∈ Icc (0 : ℝ) 1 →
      fderiv ℝ (h t) (p + (1, 0)) = fderiv ℝ (h t) p)
    {c : ℝ} (hc : 0 < c) :
    ∃ K : ℕ, 0 < K ∧ ∀ j < K, ∀ p : ℝ × ℝ, p.2 ∈ Icc (0 : ℝ) 1 → ∀ H : ℝ × ℝ → ℝ × ℝ,
      DifferentiableAt ℝ H (h (j / K) p) → H ∘ h (j / K) =ᶠ[𝓝 p] h ((j + 1) / K) →
        0 < (fderiv ℝ ((stripShear c).symm ∘ H) (h (j / K) p) (1, 0)).1 ∧
          (fderiv ℝ ((stripShear c).symm ∘ H) (h (j / K) p) (0, 1)).1 < 0 := by
  obtain ⟨η, hη, htwist⟩ :=
    exists_pos_forall_fderiv_stripShear_symm_comp_apply_fst_pos_and_neg hD hunit hper hc
  obtain ⟨K, hK⟩ := exists_nat_one_div_lt hη
  refine ⟨K + 1, K.succ_pos, fun j hj p hp H hH hHp ↦ ?_⟩
  have hK0 : (0 : ℝ) < (K + 1 : ℕ) := by positivity
  have hj' : (j + 1 : ℝ) ≤ (K + 1 : ℕ) := by exact_mod_cast hj
  have hmem (r : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ (K + 1 : ℕ)) : r / (K + 1 : ℕ) ∈ Icc (0 : ℝ) 1 :=
    ⟨by positivity, (div_le_one hK0).2 hr⟩
  refine htwist _ (hmem j j.cast_nonneg (by linarith)) _ (hmem (j + 1) (by positivity) hj') ?_
    p hp H hH hHp
  rw [← sub_div, add_sub_cancel_left, abs_of_pos (by positivity)]
  simpa using hK

/-! ### Examples

For the increment `H(x, y) = (x + (2y - 1) / 8, y)` the factor `R_c⁻¹ ∘ H` has
`∂_y X = 1 / 4 - c`. For `c = 1` this is `-3 / 4`, a negative twist, while for `c = 1 / 8`, a
shear smaller than the twist of the increment, it is `1 / 8 > 0`. -/

example (c : ℝ) (p : ℝ × ℝ) :
    (fderiv ℝ ((stripShear c).symm ∘ fun q : ℝ × ℝ ↦ (q.1 + (2 * q.2 - 1) / 8, q.2)) p
      (0, 1)).1 = 1 / 4 - c := by
  have hH : (fun q : ℝ × ℝ ↦ (q.1 + (2 * q.2 - 1) / 8, q.2)) =
      fun q ↦ stripShear (1 / 4) q - ((1 : ℝ) / 8, (0 : ℝ)) := by
    ext q <;> simp only [stripShear_apply, Prod.fst_sub, Prod.snd_sub, sub_zero]; ring
  rw [ContinuousLinearEquiv.comp_fderiv, hH, fderiv_sub_const, ContinuousLinearEquiv.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, stripShear_apply,
    stripShear_symm_apply]
  ring

end TauCeti

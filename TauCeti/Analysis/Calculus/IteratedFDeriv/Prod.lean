/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import TauCeti.Analysis.Calculus.IteratedFDeriv.CompLinear
import Mathlib.Analysis.Calculus.FDeriv.Equiv

/-!
# Iterated derivatives in one variable of a product

The iterated derivative of a slice `x ↦ f (p, x)` is the total iterated derivative of `f`
restricted to directions in the second factor. Consequently these partial derivatives vary
continuously in both variables when `f` is sufficiently differentiable. This gives the
joint derivative continuity needed for smooth families in function spaces.

The within-set versions require unique derivatives only on the product,
so they also handle coordinate domains of manifolds with boundary or corners.

For a function `g` on a normed space `E` and a normed algebra `A`, the product
`z ↦ z.2 * g z.1` on `E × A` is linear in its second variable. By the Leibniz rule, its `k`-th
iterated derivative has norm at most `‖z.2‖ ‖D^k g (z.1)‖ + k ‖D^(k-1) g (z.1)‖`
(`TauCeti.norm_iteratedFDeriv_snd_mul_comp_fst_le`). The fibrewise multiplication
`z ↦ (z.1, z.2 * g z.1)` therefore has `k`-th iterated derivative of norm at most the maximum of `1`
and this bound when `1 ≤ k` (`TauCeti.norm_iteratedFDeriv_fst_prodMk_snd_mul_comp_fst_le`).
-/

public section

namespace _root_.ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {P : Type*} [NormedAddCommGroup P] [NormedSpace 𝕜 P]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {n : WithTop ℕ∞} {f : P × E → F}

/-- The iterated derivative in the second variable is the total iterated derivative restricted
to directions with zero first component. -/
theorem iteratedFDeriv_prod_right (hf : ContDiff 𝕜 n f) (m : ℕ) (hm : m ≤ n)
    (p : P) (x : E) :
    iteratedFDeriv 𝕜 m (fun y ↦ f (p, y)) x =
      (iteratedFDeriv 𝕜 m f (p, x)).compContinuousLinearMap
        (fun _ ↦ ContinuousLinearMap.inr 𝕜 P E) := by
  have h := (ContinuousLinearMap.inr 𝕜 P E).iteratedFDeriv_comp_right
    (hf.comp (contDiff_const.add contDiff_id) :
      ContDiff 𝕜 n (fun z : P × E ↦ f ((p, 0) + z))) x hm
  simpa only [Function.comp_def, ContinuousLinearMap.inr_apply, Prod.mk_add_mk,
    add_zero, zero_add, iteratedFDeriv_comp_add_left] using h

/-- The iterated derivatives in the second variable of a `C^n` function are jointly continuous
in the parameter and the evaluation point, through order `n`. -/
theorem continuous_iteratedFDeriv_prod_right (hf : ContDiff 𝕜 n f) (m : ℕ) (hm : m ≤ n) :
    Continuous (fun z : P × E ↦ iteratedFDeriv 𝕜 m (fun y ↦ f (z.1, y)) z.2) := by
  simp_rw [iteratedFDeriv_prod_right hf m hm]
  exact (ContinuousMultilinearMap.compContinuousLinearMapL
    (fun _ : Fin m ↦ ContinuousLinearMap.inr 𝕜 P E)).continuous.comp
      (hf.continuous_iteratedFDeriv hm)

end ContDiff
end _root_

namespace ContDiffOn

open Set

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {P : Type*} [NormedAddCommGroup P] [NormedSpace 𝕜 P]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {n : WithTop ℕ∞} {f : P × E → F} {s : Set P} {t : Set E}

/-- When the product has unique derivatives, differentiation in the second variable restricts
the total derivative to directions with zero first component. -/
theorem iteratedFDerivWithin_prod_right (hf : ContDiffOn 𝕜 n f (s ×ˢ t))
    (hst : UniqueDiffOn 𝕜 (s ×ˢ t)) (m : ℕ) (hm : m ≤ n)
    {p : P} (hp : p ∈ s) {x : E} (hx : x ∈ t) :
    iteratedFDerivWithin 𝕜 m (fun y ↦ f (p, y)) t x =
      (iteratedFDerivWithin 𝕜 m f (s ×ˢ t) (p, x)).compContinuousLinearMap
        (fun _ ↦ ContinuousLinearMap.inr 𝕜 P E) := by
  have ht : UniqueDiffOn 𝕜 t := by
    have hsnd : Function.Surjective (ContinuousLinearMap.snd 𝕜 P E) :=
      fun y ↦ ⟨(p, y), rfl⟩
    have h := hst.image (fun _ _ ↦ hasFDerivWithinAt_snd (𝕜 := 𝕜))
      (fun _ _ ↦ hsnd.denseRange)
    simpa only [snd_image_prod ⟨p, hp⟩] using h
  let g : E →ᴬ[𝕜] P × E :=
    (ContinuousAffineMap.const 𝕜 E p).prod (ContinuousAffineMap.id 𝕜 E)
  have hpre : g ⁻¹' (s ×ˢ t) = t := by ext y; simp [g, hp]
  have hg : g.contLinear = ContinuousLinearMap.inr 𝕜 P E := by
    ext y : 1
    simpa [g] using g.contLinear_apply_vsub y 0
  have h := ((hf.of_le hm).ftaylorSeriesWithin hst).comp_continuousAffineMap g
  rw [hpre] at h
  simpa only [hg, ftaylorSeriesWithin, g, ContinuousAffineMap.prod_apply,
    ContinuousAffineMap.coe_const, ContinuousAffineMap.coe_id, Function.const_apply,
    id_eq, Function.comp_def] using
    (h.eq_iteratedFDerivWithin_of_uniqueDiffOn le_rfl ht hx).symm

/-- When the product has unique derivatives, partial iterated derivatives
vary jointly continuously, including at boundary points of either set. -/
theorem continuousOn_iteratedFDerivWithin_prod_right (hf : ContDiffOn 𝕜 n f (s ×ˢ t))
    (hst : UniqueDiffOn 𝕜 (s ×ˢ t)) (m : ℕ) (hm : m ≤ n) :
    ContinuousOn (fun z : P × E ↦ iteratedFDerivWithin 𝕜 m (fun y ↦ f (z.1, y)) t z.2)
      (s ×ˢ t) := by
  refine ((ContinuousMultilinearMap.compContinuousLinearMapL
    (fun _ : Fin m ↦ ContinuousLinearMap.inr 𝕜 P E)).continuous.comp_continuousOn
      (hf.continuousOn_iteratedFDerivWithin hm hst)).congr ?_
  intro z hz
  exact hf.iteratedFDerivWithin_prod_right hst m hm hz.1 hz.2

end ContDiffOn

namespace TauCeti

section Product

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {A : Type*} [NormedRing A] [NormedAlgebra 𝕜 A]

/-- **Leibniz bound for a product linear in one variable.** For `g : E → A` of class `C^k`, the
`k`-th iterated derivative of `z ↦ z.2 * g z.1` on `E × A` has norm at most
`‖z.2‖ ‖D^k g (z.1)‖ + k ‖D^(k-1) g (z.1)‖`. -/
theorem norm_iteratedFDeriv_snd_mul_comp_fst_le {g : E → A} {k : ℕ} (hg : ContDiff 𝕜 k g)
    (z : E × A) :
    ‖iteratedFDeriv 𝕜 k (fun w : E × A ↦ w.2 * g w.1) z‖ ≤
      ‖z.2‖ * ‖iteratedFDeriv 𝕜 k g z.1‖ + k * ‖iteratedFDeriv 𝕜 (k - 1) g z.1‖ := by
  have hsnd : ContDiff 𝕜 k (Prod.snd : E × A → A) := contDiff_snd
  have hgf : ContDiff 𝕜 k (g ∘ Prod.fst : E × A → A) := hg.comp contDiff_fst
  have hle (i : ℕ) (hi : i ≤ k) :
      ‖iteratedFDeriv 𝕜 i (g ∘ Prod.fst : E × A → A) z‖ ≤ ‖iteratedFDeriv 𝕜 i g z.1‖ :=
    norm_iteratedFDeriv_comp_fst_le hg z (by exact_mod_cast hi)
  refine (norm_iteratedFDeriv_mul_le hsnd hgf z le_rfl).trans ?_
  rcases k with _ | m
  · simp
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  have hrest : ∑ i ∈ Finset.range m, ((m + 1).choose (i + 1 + 1) : ℝ) *
      ‖iteratedFDeriv 𝕜 (i + 1 + 1) (Prod.snd : E × A → A) z‖ *
      ‖iteratedFDeriv 𝕜 (m + 1 - (i + 1 + 1)) (g ∘ Prod.fst : E × A → A) z‖ = 0 :=
    Finset.sum_eq_zero fun i _ ↦ by
      have h := (ContinuousLinearMap.snd 𝕜 E A).iteratedFDeriv_add_two i z
      rw [ContinuousLinearMap.coe_snd'] at h
      simp [h]
  have h1 : ‖iteratedFDeriv 𝕜 1 (Prod.snd : E × A → A) z‖ ≤ 1 :=
    norm_iteratedFDeriv_snd_le_one le_rfl z
  rw [hrest, zero_add]
  refine le_of_le_of_eq (add_le_add ?_ ?_) (add_comm _ _)
  · simp only [zero_add, Nat.choose_one_right]
    calc ((m + 1 : ℕ) : ℝ) * ‖iteratedFDeriv 𝕜 1 (Prod.snd : E × A → A) z‖ *
          ‖iteratedFDeriv 𝕜 m (g ∘ Prod.fst : E × A → A) z‖
        ≤ ((m + 1 : ℕ) : ℝ) * 1 * ‖iteratedFDeriv 𝕜 m g z.1‖ := by
          gcongr
          exact hle m (Nat.le_succ m)
      _ = ((m + 1 : ℕ) : ℝ) * ‖iteratedFDeriv 𝕜 m g z.1‖ := by ring
  · simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero,
      norm_iteratedFDeriv_zero]
    gcongr
    exact hle _ le_rfl

/-- **Derivative bound for a fibrewise multiplication.** For `g : E → A` of class `C^k` with
`1 ≤ k`, the `k`-th iterated derivative of `z ↦ (z.1, z.2 * g z.1)` on `E × A` has norm at most
`max 1 (‖z.2‖ ‖D^k g (z.1)‖ + k ‖D^(k-1) g (z.1)‖)`. -/
theorem norm_iteratedFDeriv_fst_prodMk_snd_mul_comp_fst_le {g : E → A} {k : ℕ}
    (hg : ContDiff 𝕜 k g) (hk : 1 ≤ k) (z : E × A) :
    ‖iteratedFDeriv 𝕜 k (fun w : E × A ↦ (w.1, w.2 * g w.1)) z‖ ≤
      max 1 (‖z.2‖ * ‖iteratedFDeriv 𝕜 k g z.1‖ + k * ‖iteratedFDeriv 𝕜 (k - 1) g z.1‖) := by
  have hmul : ContDiff 𝕜 k (fun w : E × A ↦ w.2 * g w.1) :=
    contDiff_snd.mul (hg.comp contDiff_fst)
  rw [iteratedFDeriv_prodMk (f := Prod.fst) contDiff_fst.contDiffAt hmul.contDiffAt le_rfl,
    ContinuousMultilinearMap.opNorm_prod]
  exact max_le_max (norm_iteratedFDeriv_fst_le_one hk z)
    (norm_iteratedFDeriv_snd_mul_comp_fst_le hg z)

end Product

end TauCeti

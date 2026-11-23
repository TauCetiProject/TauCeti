/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giada Franz
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Bilinear
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
public import TauCeti.Geometry.Manifold.Riemannian.Sphere.Basic

/-!
# The Veronese map of the two-sphere into the four-sphere

The degree-two map `V : ℝ³ → ℝ⁵`,

`V(x, y, z) = (√3 (x² - y²) / 2, √3 xy, √3 xz, √3 yz, (2z² - x² - y²) / 2)`,

is `V(p) = B(p, p)` for an explicit symmetric bilinear map `B`. It satisfies `‖V(p)‖ = ‖p‖²`, so
it maps the unit sphere `S²` into the unit sphere `S⁴`, and the Gram identity
`⟪dV_p v, dV_p w⟫ = 3 ‖p‖² ⟪v, w⟫ + ⟪p, v⟫ ⟪p, w⟫` shows that the induced metric on `S²` is three
times the round metric. Two points of `S²` have the same image exactly when they are equal or
antipodal: `V(p)` determines the products `pᵢ pⱼ`, hence `p` up to sign.

## Main definitions

* `TauCeti.Manifold.Veronese.bilin`: the symmetric bilinear map `B : ℝ³ × ℝ³ → ℝ⁵`.
* `TauCeti.Manifold.Veronese.veroneseMap`: the polynomial map `V(p) = B(p, p)`.
* `TauCeti.Manifold.Veronese.veronese`: its restriction `S² → S⁴`.

## Main results

* `TauCeti.Manifold.Veronese.norm_veroneseMap`: `‖V(p)‖ = ‖p‖²`.
* `TauCeti.Manifold.Veronese.inner_bilin_bilin`: the Gram identity of the differential.
* `TauCeti.Manifold.Veronese.inner_mfderiv_veronese`: the induced metric is three times the
  round metric.
* `TauCeti.Manifold.Veronese.veronese_eq_veronese_iff`: the fibers are antipodal pairs.

## References

* T. Takahashi, *Minimal immersions of Riemannian manifolds*, J. Math. Soc. Japan 18 (1966),
  380–385.
-/

public section

open Bundle Function Manifold Metric Module Set
open scoped ContDiff InnerProductSpace Manifold

noncomputable section

namespace TauCeti.Manifold.Veronese

local notation "E₃" => EuclideanSpace ℝ (Fin 3)
local notation "E₅" => EuclideanSpace ℝ (Fin 5)
local notation "S²" => sphere (0 : E₃) 1
local notation "S⁴" => sphere (0 : E₅) 1

/-- `ℝ³` has dimension `2 + 1`, so its unit sphere is a surface. -/
local instance instFactFinrankThreeVeronese : Fact (finrank ℝ E₃ = 2 + 1) := ⟨by simp⟩

/-- `ℝ⁵` has dimension `4 + 1`, so its unit sphere is a four-manifold. -/
local instance instFactFinrankFiveVeronese : Fact (finrank ℝ E₅ = 4 + 1) := ⟨by simp⟩

/-- The symmetric bilinear map whose diagonal is the Veronese map. -/
def bilinFun (p q : E₃) : E₅ :=
  !₂[√3 / 2 * (p 0 * q 0 - p 1 * q 1), √3 / 2 * (p 0 * q 1 + p 1 * q 0),
    √3 / 2 * (p 0 * q 2 + p 2 * q 0), √3 / 2 * (p 1 * q 2 + p 2 * q 1),
    (2 * (p 2 * q 2) - p 0 * q 0 - p 1 * q 1) / 2]

private def bilinLin : E₃ →ₗ[ℝ] E₃ →ₗ[ℝ] E₅ :=
  LinearMap.mk₂ ℝ bilinFun
    (fun p p' q ↦ by ext i; fin_cases i <;> simp [bilinFun] <;> ring)
    (fun c p q ↦ by ext i; fin_cases i <;> simp [bilinFun] <;> ring)
    (fun p q q' ↦ by ext i; fin_cases i <;> simp [bilinFun] <;> ring)
    (fun c p q ↦ by ext i; fin_cases i <;> simp [bilinFun] <;> ring)

/-- The symmetric bilinear map `B : ℝ³ × ℝ³ → ℝ⁵` with `V(p) = B(p, p)`. -/
def bilin : E₃ →L[ℝ] E₃ →L[ℝ] E₅ :=
  LinearMap.toContinuousLinearMap (LinearMap.toContinuousLinearMap.toLinearMap ∘ₗ bilinLin)

theorem bilin_apply (p q : E₃) : bilin p q = bilinFun p q := by
  simp [bilin, bilinLin]

theorem bilin_comm (p q : E₃) : bilin p q = bilin q p := by
  rw [bilin_apply, bilin_apply]
  ext i
  fin_cases i <;> simp [bilinFun] <;> ring

/-- **The Veronese map** `V(p) = B(p, p)` of `ℝ³` into `ℝ⁵`. -/
def veroneseMap (p : E₃) : E₅ := bilin p p

theorem veroneseMap_apply (p : E₃) :
    veroneseMap p = !₂[√3 / 2 * (p 0 ^ 2 - p 1 ^ 2), √3 * (p 0 * p 1), √3 * (p 0 * p 2),
      √3 * (p 1 * p 2), (2 * p 2 ^ 2 - p 0 ^ 2 - p 1 ^ 2) / 2] := by
  rw [veroneseMap, bilin_apply]
  ext i
  fin_cases i <;> simp [bilinFun] <;> ring

private theorem sqrt_three_mul_self : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)

private theorem inner_euclidean_three (p q : E₃) :
    ⟪p, q⟫_ℝ = p 0 * q 0 + p 1 * q 1 + p 2 * q 2 := by
  simp [PiLp.inner_apply, Fin.sum_univ_three, mul_comm]

private theorem inner_bilinFun (p q p' q' : E₃) :
    ⟪bilinFun p q, bilinFun p' q'⟫_ℝ =
      3 / 4 * ((p 0 * q 0 - p 1 * q 1) * (p' 0 * q' 0 - p' 1 * q' 1) +
        (p 0 * q 1 + p 1 * q 0) * (p' 0 * q' 1 + p' 1 * q' 0) +
        (p 0 * q 2 + p 2 * q 0) * (p' 0 * q' 2 + p' 2 * q' 0) +
        (p 1 * q 2 + p 2 * q 1) * (p' 1 * q' 2 + p' 2 * q' 1)) +
      (2 * (p 2 * q 2) - p 0 * q 0 - p 1 * q 1) * (2 * (p' 2 * q' 2) - p' 0 * q' 0 - p' 1 * q' 1) /
        4 := by
  simp [bilinFun, PiLp.inner_apply, Fin.sum_univ_five]
  linear_combination ((p' 0 * q' 0 - p' 1 * q' 1) * (p 0 * q 0 - p 1 * q 1) +
    (p' 0 * q' 1 + p' 1 * q' 0) * (p 0 * q 1 + p 1 * q 0) +
    (p' 0 * q' 2 + p' 2 * q' 0) * (p 0 * q 2 + p 2 * q 0) +
    (p' 1 * q' 2 + p' 2 * q' 1) * (p 1 * q 2 + p 2 * q 1)) / 4 * sqrt_three_mul_self

/-- `‖V(p)‖² = ‖p‖⁴`. -/
theorem inner_veroneseMap_self (p : E₃) : ⟪veroneseMap p, veroneseMap p⟫_ℝ = ⟪p, p⟫_ℝ ^ 2 := by
  rw [veroneseMap, bilin_apply, inner_bilinFun, inner_euclidean_three]
  ring

/-- `‖V(p)‖ = ‖p‖²`. -/
theorem norm_veroneseMap (p : E₃) : ‖veroneseMap p‖ = ‖p‖ ^ 2 := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (by positivity), ← real_inner_self_eq_norm_sq,
    inner_veroneseMap_self, real_inner_self_eq_norm_sq]

/-- **The Gram identity**: `⟪B(p, v), B(p, w)⟫ = (3 ‖p‖² ⟪v, w⟫ + ⟪p, v⟫ ⟪p, w⟫) / 4`. -/
theorem inner_bilin_bilin (p v w : E₃) :
    ⟪bilin p v, bilin p w⟫_ℝ = (3 * ⟪p, p⟫_ℝ * ⟪v, w⟫_ℝ + ⟪p, v⟫_ℝ * ⟪p, w⟫_ℝ) / 4 := by
  rw [bilin_apply, bilin_apply, inner_bilinFun, inner_euclidean_three, inner_euclidean_three,
    inner_euclidean_three, inner_euclidean_three]
  ring

theorem contDiff_veroneseMap {n : WithTop ℕ∞} : ContDiff ℝ n veroneseMap :=
  bilin.isBoundedBilinearMap.contDiff.comp (contDiff_id.prodMk contDiff_id)

/-- The differential of the Veronese map is `v ↦ 2 B(p, v)`. -/
theorem hasFDerivAt_veroneseMap (p : E₃) : HasFDerivAt veroneseMap ((2 : ℝ) • bilin p) p := by
  have h := bilin.hasFDerivAt.clm_apply (hasFDerivAt_id p)
  have heq : (bilin p).comp (ContinuousLinearMap.id ℝ E₃) + bilin.flip (id p) =
      (2 : ℝ) • bilin p := by
    ext v
    simp [two_smul, bilin_comm v p]
  rw [heq] at h
  exact h

theorem fderiv_veroneseMap_apply (p v : E₃) : fderiv ℝ veroneseMap p v = (2 : ℝ) • bilin p v := by
  rw [(hasFDerivAt_veroneseMap p).fderiv, smul_apply]

/-- **The Veronese map** `S² → S⁴`. -/
def veronese (p : S²) : S⁴ :=
  ⟨veroneseMap p, by
    rw [mem_sphere_zero_iff_norm, norm_veroneseMap, norm_eq_of_mem_sphere p, one_pow]⟩

@[simp]
theorem coe_veronese (p : S²) : (veronese p : E₅) = veroneseMap p := (rfl)

theorem contMDiff_veronese (k : ℕ∞ω) : ContMDiff (𝓡 2) (𝓡 4) k veronese :=
  (contDiff_veroneseMap.contMDiff.comp contMDiff_coe_sphere).codRestrict_sphere _

/-- A tangent vector of `S²` at `p`, read in `ℝ³`, is orthogonal to `p`. -/
theorem inner_mvfderiv_coe_sphere (p : S²) (v : TangentSpace (𝓡 2) p) :
    ⟪(p : E₃), mvfderiv (𝓡 2) ((↑) : S² → E₃) p v⟫_ℝ = 0 := by
  have h : mvfderiv (𝓡 2) ((↑) : S² → E₃) p v ∈ (ℝ ∙ (p : E₃))ᗮ := by
    rw [← range_mvfderiv_subtypeVal (n := 2)]
    exact LinearMap.mem_range_self _ v
  exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp h

/-- The differential of the Veronese map of spheres, read in `ℝ⁵`, is `2 B(p, ·)` applied to the
tangent vector read in `ℝ³`. -/
theorem mvfderiv_coe_veronese (p : S²) (v : TangentSpace (𝓡 2) p) :
    mvfderiv (𝓡 4) ((↑) : S⁴ → E₅) (veronese p) (mfderiv (𝓡 2) (𝓡 4) veronese p v) =
      (2 : ℝ) • bilin p (mvfderiv (𝓡 2) ((↑) : S² → E₃) p v) := by
  have hcoe : MDifferentiableAt (𝓡 4) 𝓘(ℝ, E₅) ((↑) : S⁴ → E₅) (veronese p) :=
    ((contMDiff_coe_sphere (m := 1) (veronese p)).mdifferentiableAt one_ne_zero)
  rw [← mvfderiv_comp_apply (g := ((↑) : S⁴ → E₅)) p hcoe
    ((contMDiff_veronese 1).mdifferentiableAt one_ne_zero) v]
  have h := mvfderiv_comp_apply_of_differentiableAt (φ := veroneseMap)
    (hasFDerivAt_veroneseMap p).differentiableAt
    ((contMDiff_coe_sphere (m := 1) p).mdifferentiableAt one_ne_zero) v
  rw [fderiv_veroneseMap_apply] at h
  exact h

/-- **The induced metric of the Veronese map is three times the round metric.** -/
theorem inner_mfderiv_veronese (p : S²) (v w : TangentSpace (𝓡 2) p) :
    ⟪mfderiv (𝓡 2) (𝓡 4) veronese p v, mfderiv (𝓡 2) (𝓡 4) veronese p w⟫_ℝ = 3 * ⟪v, w⟫_ℝ := by
  rw [inner_tangentSpace_sphere, mvfderiv_coe_veronese, mvfderiv_coe_veronese, inner_smul_left,
    inner_smul_right, inner_bilin_bilin, inner_mvfderiv_coe_sphere, real_inner_self_eq_norm_sq,
    norm_eq_of_mem_sphere p, inner_tangentSpace_sphere p v w]
  simp only [conj_trivial]
  ring

private theorem eq_or_eq_neg_of_mul_eq_mul {a b c a' b' c' : ℝ} (haa : a * a = a' * a')
    (hbb : b * b = b' * b') (hcc : c * c = c' * c') (hab : a * b = a' * b')
    (hac : a * c = a' * c') (hbc : b * c = b' * c') :
    (a' = a ∧ b' = b ∧ c' = c) ∨ (a' = -a ∧ b' = -b ∧ c' = -c) := by
  by_cases ha : a = 0
  · subst ha
    have ha' : a' = 0 := mul_self_eq_zero.mp (by linarith)
    subst ha'
    by_cases hb : b = 0
    · subst hb
      have hb' : b' = 0 := mul_self_eq_zero.mp (by linarith)
      subst hb'
      rcases mul_self_eq_mul_self_iff.mp hcc with h | h
      · exact Or.inl ⟨rfl, rfl, h.symm⟩
      · exact Or.inr ⟨by ring, by ring, by linarith⟩
    · rcases mul_self_eq_mul_self_iff.mp hbb with h | h
      · subst h
        exact Or.inl ⟨rfl, rfl, (mul_left_cancel₀ hb hbc).symm⟩
      · have hb'' : b' = -b := by linarith
        subst hb''
        refine Or.inr ⟨by ring, rfl, ?_⟩
        have : b * c = b * -c' := by linarith
        linarith [mul_left_cancel₀ hb this]
  · rcases mul_self_eq_mul_self_iff.mp haa with h | h
    · subst h
      exact Or.inl ⟨rfl, (mul_left_cancel₀ ha hab).symm, (mul_left_cancel₀ ha hac).symm⟩
    · have ha'' : a' = -a := by linarith
      subst ha''
      refine Or.inr ⟨rfl, ?_, ?_⟩
      · have : a * b = a * -b' := by linarith
        linarith [mul_left_cancel₀ ha this]
      · have : a * c = a * -c' := by linarith
        linarith [mul_left_cancel₀ ha this]

private theorem eq_or_eq_neg_of_veronese_eq {p q : S²} (hpq : veronese p = veronese q) :
    q = p ∨ q = -p := by
  have hv : veroneseMap p = veroneseMap q := congrArg Subtype.val hpq
  rw [veroneseMap_apply, veroneseMap_apply] at hv
  have hs : √3 ≠ 0 := by positivity
  have hp := norm_eq_of_mem_sphere p
  have hq := norm_eq_of_mem_sphere q
  rw [← sq_eq_sq₀ (norm_nonneg _) zero_le_one, ← real_inner_self_eq_norm_sq,
    inner_euclidean_three] at hp hq
  have h0 := congrArg (fun v : E₅ ↦ v 0) hv
  have h1 := congrArg (fun v : E₅ ↦ v 1) hv
  have h2 := congrArg (fun v : E₅ ↦ v 2) hv
  have h3 := congrArg (fun v : E₅ ↦ v 3) hv
  have h4 := congrArg (fun v : E₅ ↦ v 4) hv
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
  replace h4 : (2 * (p : E₃) 2 ^ 2 - (p : E₃) 0 ^ 2 - (p : E₃) 1 ^ 2) / 2 =
      (2 * (q : E₃) 2 ^ 2 - (q : E₃) 0 ^ 2 - (q : E₃) 1 ^ 2) / 2 := h4
  have e01 := mul_left_cancel₀ hs h1
  have e02 := mul_left_cancel₀ hs h2
  have e12 := mul_left_cancel₀ hs h3
  have d01 := mul_left_cancel₀ (div_ne_zero hs two_ne_zero) h0
  have e22 : (p : E₃) 2 * (p : E₃) 2 = (q : E₃) 2 * (q : E₃) 2 := by
    linear_combination (2 / 3 : ℝ) * h4 + (1 / 3 : ℝ) * hp - (1 / 3 : ℝ) * hq
  have e00 : (p : E₃) 0 * (p : E₃) 0 = (q : E₃) 0 * (q : E₃) 0 := by
    linear_combination (1 / 2 : ℝ) * d01 + (1 / 2 : ℝ) * hp - (1 / 2 : ℝ) * hq -
      (1 / 2 : ℝ) * e22
  have e11 : (p : E₃) 1 * (p : E₃) 1 = (q : E₃) 1 * (q : E₃) 1 := by
    linear_combination -(1 / 2 : ℝ) * d01 + (1 / 2 : ℝ) * hp - (1 / 2 : ℝ) * hq -
      (1 / 2 : ℝ) * e22
  rcases eq_or_eq_neg_of_mul_eq_mul e00 e11 e22 e01 e02 e12 with ⟨c0, c1, c2⟩ | ⟨c0, c1, c2⟩
  · left
    ext i
    fin_cases i
    · exact c0
    · exact c1
    · exact c2
  · right
    ext i
    fin_cases i
    · simpa using c0
    · simpa using c1
    · simpa using c2

/-- **The fibers of the Veronese map are antipodal pairs.** -/
theorem veronese_eq_veronese_iff {p q : S²} : veronese p = veronese q ↔ q = p ∨ q = -p := by
  constructor
  · exact eq_or_eq_neg_of_veronese_eq
  · rintro (rfl | rfl)
    · rfl
    · apply Subtype.ext
      simp only [coe_veronese, veroneseMap, coe_neg_sphere, map_neg, neg_apply, neg_neg]

end TauCeti.Manifold.Veronese

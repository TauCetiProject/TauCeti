/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giada Franz
-/
module

public import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear
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
antipodal, as follows from the polarization identity and the equality case of Cauchy–Schwarz.

## Main definitions

* `TauCeti.Manifold.Veronese.bilin`: the symmetric bilinear map `B : ℝ³ × ℝ³ → ℝ⁵`.
* `TauCeti.Manifold.Veronese.veroneseMap`: the polynomial map `V(p) = B(p, p)`.
* `TauCeti.Manifold.Veronese.veronese`: its restriction `S² → S⁴`.

## Main results

* `TauCeti.Manifold.Veronese.norm_veroneseMap`: `‖V(p)‖ = ‖p‖²`.
* `TauCeti.Manifold.Veronese.inner_bilin_bilin`: the polarization identity of the bilinear model.
* `TauCeti.Manifold.Veronese.inner_bilin_bilin_left`: the Gram identity of the differential.
* `TauCeti.Manifold.Veronese.inner_mfderiv_veronese`: the induced metric is three times the
  round metric.
* `TauCeti.Manifold.Veronese.veroneseMap_eq_veroneseMap_iff`: the fibers on `ℝ³` are antipodal
  pairs.
* `TauCeti.Manifold.Veronese.veronese_eq_veronese_iff`: the corresponding result on `S²`.

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
private def bilinFun (p q : E₃) : E₅ :=
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
  bilinLin.toContinuousBilinearMap

theorem bilin_apply (p q : E₃) :
    bilin p q = !₂[√3 / 2 * (p 0 * q 0 - p 1 * q 1), √3 / 2 * (p 0 * q 1 + p 1 * q 0),
      √3 / 2 * (p 0 * q 2 + p 2 * q 0), √3 / 2 * (p 1 * q 2 + p 2 * q 1),
      (2 * (p 2 * q 2) - p 0 * q 0 - p 1 * q 1) / 2] := by
  simp [bilin, LinearMap.toContinuousBilinearMap_apply, bilinLin, bilinFun]

theorem bilin_comm (p q : E₃) : bilin p q = bilin q p := by
  rw [bilin_apply, bilin_apply]
  ext i
  fin_cases i <;> simp <;> ring

/-- **The Veronese map** `V(p) = B(p, p)` of `ℝ³` into `ℝ⁵`. -/
def veroneseMap (p : E₃) : E₅ := bilin p p

/-- The Veronese map is the diagonal of its symmetric bilinear model. -/
theorem veroneseMap_def (p : E₃) : veroneseMap p = bilin p p := (rfl)

/-- The Veronese map is homogeneous of degree two. -/
theorem veroneseMap_smul (c : ℝ) (p : E₃) :
    veroneseMap (c • p) = c ^ 2 • veroneseMap p := by
  simp [veroneseMap_def, smul_smul, pow_two]

@[simp]
theorem veroneseMap_neg (p : E₃) : veroneseMap (-p) = veroneseMap p := by
  simp [veroneseMap_def]

theorem veroneseMap_apply (p : E₃) :
    veroneseMap p = !₂[√3 / 2 * (p 0 ^ 2 - p 1 ^ 2), √3 * (p 0 * p 1), √3 * (p 0 * p 2),
      √3 * (p 1 * p 2), (2 * p 2 ^ 2 - p 0 ^ 2 - p 1 ^ 2) / 2] := by
  rw [veroneseMap_def, bilin_apply]
  ext i
  fin_cases i <;> simp <;> ring

private theorem inner_bilin_coordinates (p q p' q' : E₃) :
    ⟪bilin p q, bilin p' q'⟫_ℝ =
      3 / 4 * ((p 0 * q 0 - p 1 * q 1) * (p' 0 * q' 0 - p' 1 * q' 1) +
        (p 0 * q 1 + p 1 * q 0) * (p' 0 * q' 1 + p' 1 * q' 0) +
        (p 0 * q 2 + p 2 * q 0) * (p' 0 * q' 2 + p' 2 * q' 0) +
        (p 1 * q 2 + p 2 * q 1) * (p' 1 * q' 2 + p' 2 * q' 1)) +
      (2 * (p 2 * q 2) - p 0 * q 0 - p 1 * q 1) * (2 * (p' 2 * q' 2) - p' 0 * q' 0 - p' 1 * q' 1) /
        4 := by
  simp [bilin_apply, PiLp.inner_apply, Fin.sum_univ_five]
  linear_combination ((p' 0 * q' 0 - p' 1 * q' 1) * (p 0 * q 0 - p 1 * q 1) +
    (p' 0 * q' 1 + p' 1 * q' 0) * (p 0 * q 1 + p 1 * q 0) +
    (p' 0 * q' 2 + p' 2 * q' 0) * (p 0 * q 2 + p 2 * q 0) +
    (p' 1 * q' 2 + p' 2 * q' 1) * (p 1 * q 2 + p 2 * q 1)) / 4 *
      (Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 3))

/-- The polarization identity for the bilinear model of the Veronese map. -/
theorem inner_bilin_bilin (p q p' q' : E₃) :
    ⟪bilin p q, bilin p' q'⟫_ℝ =
      (3 * (⟪p, p'⟫_ℝ * ⟪q, q'⟫_ℝ + ⟪p, q'⟫_ℝ * ⟪q, p'⟫_ℝ) -
        2 * (⟪p, q⟫_ℝ * ⟪p', q'⟫_ℝ)) / 4 := by
  rw [inner_bilin_coordinates]
  simp [PiLp.inner_apply, Fin.sum_univ_three, mul_comm]
  ring

/-- `‖V(p)‖² = ‖p‖⁴`. -/
theorem inner_veroneseMap_self (p : E₃) : ⟪veroneseMap p, veroneseMap p⟫_ℝ = ⟪p, p⟫_ℝ ^ 2 := by
  rw [veroneseMap_def, inner_bilin_bilin]
  ring

/-- `‖V(p)‖ = ‖p‖²`. -/
@[simp]
theorem norm_veroneseMap (p : E₃) : ‖veroneseMap p‖ = ‖p‖ ^ 2 := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (by positivity), ← real_inner_self_eq_norm_sq,
    inner_veroneseMap_self, real_inner_self_eq_norm_sq]

/-- **The Gram identity**: `⟪B(p, v), B(p, w)⟫ = (3 ‖p‖² ⟪v, w⟫ + ⟪p, v⟫ ⟪p, w⟫) / 4`. -/
theorem inner_bilin_bilin_left (p v w : E₃) :
    ⟪bilin p v, bilin p w⟫_ℝ = (3 * ⟪p, p⟫_ℝ * ⟪v, w⟫_ℝ + ⟪p, v⟫_ℝ * ⟪p, w⟫_ℝ) / 4 := by
  rw [inner_bilin_bilin, real_inner_comm v p]
  ring

theorem contDiff_veroneseMap {n : WithTop ℕ∞} : ContDiff ℝ n veroneseMap :=
  bilin.contDiff_apply_self

/-- The differential of the Veronese map is `v ↦ 2 B(p, v)`. -/
theorem hasFDerivAt_veroneseMap (p : E₃) : HasFDerivAt veroneseMap ((2 : ℝ) • bilin p) p := by
  have heq : bilin.flip p + bilin p = (2 : ℝ) • bilin p := by
    ext v
    simp [two_smul, bilin_comm v p]
  rw [← heq]
  exact bilin.hasFDerivAt_apply_self p

@[simp]
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

@[simp]
theorem veronese_neg (p : S²) : veronese (-p) = veronese p := by
  apply Subtype.ext
  simp only [coe_veronese, coe_neg_sphere, veroneseMap_neg]

/-- The differential of the Veronese map of spheres, read in `ℝ⁵`, is `2 B(p, ·)` applied to the
tangent vector read in `ℝ³`. -/
theorem mvfderiv_subtypeVal_mfderiv_veronese (p : S²) (v : TangentSpace (𝓡 2) p) :
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
  rw [inner_tangentSpace_sphere, mvfderiv_subtypeVal_mfderiv_veronese,
    mvfderiv_subtypeVal_mfderiv_veronese, inner_smul_left,
    inner_smul_right, inner_bilin_bilin_left, inner_coe_mvfderiv_subtypeVal_sphere,
    real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere p, inner_tangentSpace_sphere p v w]
  simp only [conj_trivial]
  ring

/-- The fibers of the Veronese map on `ℝ³` are antipodal pairs. -/
theorem veroneseMap_eq_veroneseMap_iff {p q : E₃} :
    veroneseMap p = veroneseMap q ↔ q = p ∨ q = -p := by
  constructor
  · intro hpq
    have hn : ‖p‖ = ‖q‖ := by
      have h := congrArg norm hpq
      rw [norm_veroneseMap, norm_veroneseMap] at h
      exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h
    by_cases hp : p = 0
    · subst p
      exact Or.inl (norm_eq_zero.mp (by simpa using hn.symm))
    have hi := inner_bilin_bilin p p q q
    rw [← veroneseMap_def, ← veroneseMap_def, ← hpq, inner_veroneseMap_self,
      real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
      ← hn] at hi
    have hi2 : ⟪p, q⟫_ℝ ^ 2 = (‖p‖ * ‖q‖) ^ 2 := by
      rw [← hn]
      nlinarith [hi]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hi2 with hpos | hneg
    · left
      have h := inner_eq_norm_mul_iff_real.mp hpos
      rw [← hn] at h
      exact (smul_right_injective _ (norm_ne_zero_iff.mpr hp) h).symm
    · right
      have h : ⟪p, -q⟫_ℝ = ‖p‖ * ‖-q‖ := by
        simpa using congrArg Neg.neg hneg
      have heq := inner_eq_norm_mul_iff_real.mp h
      rw [norm_neg, ← hn] at heq
      exact neg_eq_iff_eq_neg.mp (smul_right_injective _ (norm_ne_zero_iff.mpr hp) heq).symm
  · rintro (rfl | rfl)
    · rfl
    · exact (veroneseMap_neg p).symm

/-- **The fibers of the Veronese map are antipodal pairs.** -/
theorem veronese_eq_veronese_iff {p q : S²} : veronese p = veronese q ↔ q = p ∨ q = -p := by
  simp only [Subtype.ext_iff, coe_veronese, veroneseMap_eq_veroneseMap_iff, coe_neg_sphere]

end TauCeti.Manifold.Veronese

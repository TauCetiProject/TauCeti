/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.HodgeStar.Kahler
public import Mathlib.Order.Bounds.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
import TauCeti.LinearAlgebra.Matrix.UnitaryFrame
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The Hermitian part of a two-form in dimension four

Let `V` be an oriented four-dimensional real inner product space with an orthogonal complex
structure `J` whose orientation is the complex one, and let `ω` be its Kähler two-vector, with
`‖ω‖² = 2`. A two-vector `F ∈ ⋀² V` is read as the two-form `F(v, w) = ⟪F, v ∧ w⟫`. Its
**Hermitian part** is the `J`-invariant symmetric bilinear form
`B(v, w) = (F(v, J w) + F(w, J v)) / 2`, whose quadratic form is `B(v, v) = F(v, J v)`.

Split `F = c ω + F⁺₀ + F⁻`, where `c = ⟪ω, F⟫ / 2`, `F⁻ = (F - ⋆F) / 2` is the anti-self-dual
part, and `F⁺₀` is the self-dual part orthogonal to `ω`. The self-dual part of `v ∧ J v` is
`‖v‖² ω / 2` (`ιMulti_apply_add_hodgeStar`). Consequently

`F(v, J v) = c ‖v‖² + ⟪F⁻, v ∧ J v⟫`,

so the anti-`J`-invariant self-dual summand `F⁺₀` contributes nothing to `B`, and the minimum
and maximum of `B(v, v)` over unit vectors are `c ∓ ‖F⁻‖ / √2`. Since `B` is symmetric, its
smallest eigenvalue is `λ_min(B) = c - ‖F⁻‖ / √2`. A lower bound `B ≥ -K g` therefore controls
the anti-self-dual part of `F` by its `ω`-component: `‖F⁻‖ ≤ √2 (c + K)`.

For a curvature form `F = i F_a` of the Seiberg–Witten equations on a symplectic four-manifold,
`c` is controlled by the curvature equation, and this converts a one-sided bound on the
Hermitian part of the curvature into a bound on its anti-self-dual part.

Statements take a positively oriented orthonormal basis `e` with `J e₀ = e₁` and `J e₂ = e₃`
as a witness that the orientation is the complex one, as in
`TauCeti.Analysis.InnerProductSpace.HodgeStar.Kahler`.
The eigenvalue bounds are deduced from their matrix form in
`TauCeti.LinearAlgebra.Matrix.UnitaryFrame`, applied to the matrix `Fᵢⱼ = ⟪F, eᵢ ∧ eⱼ⟫` of `F`
in the frame `e`. The anti-self-dual frame expansion of `F - ⋆F`
(`Orientation.norm_sub_hodgeStar_sq_eq_sum`) identifies `‖F - ⋆F‖` with the norm of the
anti-self-dual part of that matrix.

## Main results

In the namespace `TauCeti.AlmostComplexStructure`:

* `inner_ιMulti_apply_eq`: `F(v, J v) = c ‖v‖² + ⟪F⁻, v ∧ J v⟫`.
* `inner_ιMulti_apply_eq_zero_of_hodgeStar_eq_self`: a self-dual two-form orthogonal to `ω`
  has zero Hermitian part.
* `mul_norm_sq_le_inner_ιMulti_apply` and `inner_ιMulti_apply_le_mul_norm_sq`:
  `(c - ‖F⁻‖ / √2) ‖v‖² ≤ F(v, J v) ≤ (c + ‖F⁻‖ / √2) ‖v‖²`.
* `isLeast_inner_ιMulti_apply`: the minimum of `F(v, J v)` over unit vectors is
  `c - ‖F⁻‖ / √2`, and `isGreatest_inner_ιMulti_apply`: its maximum is `c + ‖F⁻‖ / √2`.
* `norm_sub_hodgeStar_le_of_forall_le`: if `F(v, J v) ≥ -K ‖v‖²` for all `v`, then
  `‖F⁻‖ ≤ √2 (c + K)`.

## References

* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
* S. K. Donaldson and P. B. Kronheimer, *The Geometry of Four-Manifolds*, Oxford (1990).
-/

public section

noncomputable section

open Module exteriorPower
open scoped RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

namespace TauCeti.AlmostComplexStructure

variable [Fact (finrank ℝ V = 4)] {e : OrthonormalBasis (Fin 4) ℝ V}
  {J : AlmostComplexStructure V} {o : Orientation ℝ V (Fin 4)}
  (h₀ : J (e 0) = e 1) (h₂ : J (e 2) = e 3) (hkl : 2 + 2 = finrank ℝ V)
  (he : e.toBasis.orientation = o)

include h₀ h₂ he in
/-- **The Hermitian part of a two-form**: `F(v, J v) = c ‖v‖² + ⟪F⁻, v ∧ J v⟫`, where
`c = ⟪ω, F⟫ / 2` and `F⁻ = (F - ⋆F) / 2` is the anti-self-dual part of `F`. -/
theorem inner_ιMulti_apply_eq (F : ⋀[ℝ]^2 V) (v : V) :
    ⟪F, ιMulti ℝ 2 ![v, J v]⟫ = ⟪J.kahlerForm, F⟫ / 2 * ‖v‖ ^ 2 +
      ⟪(2⁻¹ : ℝ) • (F - o.hodgeStar hkl F), ιMulti ℝ 2 ![v, J v]⟫ := by
  have hx := eq_sub_of_add_eq' (ιMulti_apply_add_hodgeStar h₀ h₂ hkl he v)
  have hsym := o.isSymmetric_hodgeStar_of_even (by decide) hkl F (ιMulti ℝ 2 ![v, J v])
  rw [LinearEquiv.coe_coe, hx] at hsym
  rw [real_inner_smul_left, inner_sub_left, hsym, inner_sub_right, real_inner_smul_right,
    real_inner_comm F J.kahlerForm]
  ring

include h₀ h₂ he in
/-- **A self-dual two-form orthogonal to `ω` has zero Hermitian part**: if `⋆η = η` and
`⟪ω, η⟫ = 0`, then `η(v, J v) = 0` for every `v`. These are the anti-`J`-invariant self-dual
forms. -/
theorem inner_ιMulti_apply_eq_zero_of_hodgeStar_eq_self {η : ⋀[ℝ]^2 V}
    (hη : o.hodgeStar hkl η = η) (hω : ⟪J.kahlerForm, η⟫ = 0) (v : V) :
    ⟪η, ιMulti ℝ 2 ![v, J v]⟫ = 0 := by
  rw [inner_ιMulti_apply_eq h₀ h₂ hkl he, hη, hω, sub_self, smul_zero, inner_zero_left]
  ring

/-! ### The matrix of a two-form in a unitary frame

The eigenvalue bounds are read off from the matrix form in
`TauCeti.LinearAlgebra.Matrix.UnitaryFrame`, through the matrix `Fᵢⱼ = ⟪F, eᵢ ∧ eⱼ⟫`. -/

open Matrix

/-- The matrix `Fᵢⱼ = ⟪F, eᵢ ∧ eⱼ⟫` of a two-vector in the frame `e`. -/
private def frameMatrix (e : OrthonormalBasis (Fin 4) ℝ V) (F : ⋀[ℝ]^2 V) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun i j ↦ ⟪F, ιMulti ℝ 2 ![e i, e j]⟫

omit [Fact (finrank ℝ V = 4)] in
/-- The matrix of a two-vector is skew-symmetric. -/
private theorem transpose_frameMatrix (F : ⋀[ℝ]^2 V) :
    (frameMatrix e F)ᵀ = -frameMatrix e F := by
  ext i j
  have hswap : ιMulti ℝ 2 ![e j, e i] = -ιMulti ℝ 2 ![e i, e j] :=
    ext_inner_ιMulti_two fun u w ↦ by
      simp only [inner_neg_left, inner_ιMulti_two]
      ring
  simp only [frameMatrix, transpose_apply, of_apply, Matrix.neg_apply, hswap,
    inner_neg_right]

omit [FiniteDimensional ℝ V] [Fact (finrank ℝ V = 4)] in
/-- `‖∑ᵢ cᵢ eᵢ‖² = c ⬝ c`. -/
private theorem norm_sum_smul_sq (c : Fin 4 → ℝ) : ‖∑ i, c i • e i‖ ^ 2 = c ⬝ᵥ c := by
  rw [← real_inner_self_eq_norm_sq, e.orthonormal.inner_sum]
  simp only [conj_trivial, dotProduct]

omit [Fact (finrank ℝ V = 4)] in
/-- `(∑ᵢ cᵢ eᵢ) ∧ (∑ⱼ dⱼ eⱼ) = ∑ᵢ ∑ⱼ cᵢ dⱼ eᵢ ∧ eⱼ`. -/
private theorem ιMulti_sum_smul (c d : Fin 4 → ℝ) :
    ιMulti ℝ 2 ![∑ i, c i • e i, ∑ j, d j • e j] =
      ∑ i, ∑ j, (c i * d j) • ιMulti ℝ 2 ![e i, e j] := by
  refine ext_inner_ιMulti_two fun u w ↦ ?_
  simp only [inner_ιMulti_two, real_inner_smul_left, Fin.sum_univ_four, inner_add_left]
  ring

omit [Fact (finrank ℝ V = 4)] in
include h₀ h₂ in
/-- `F(v, J v) = c ⬝ B c` for `v = ∑ᵢ cᵢ eᵢ`, where `B` is the Hermitian part of the matrix of
`F`. -/
private theorem inner_ιMulti_sum_smul (F : ⋀[ℝ]^2 V) (c : Fin 4 → ℝ) :
    ⟪F, ιMulti ℝ 2 ![∑ i, c i • e i, J (∑ i, c i • e i)]⟫ =
      c ⬝ᵥ ((frameMatrix e F).frameHermitianForm *ᵥ c) := by
  have h₁ : J (e 1) = -e 0 := by rw [← h₀, J.apply_apply]
  have h₃ : J (e 3) = -e 2 := by rw [← h₂, J.apply_apply]
  have hd : TauCeti.frameComplexStructure *ᵥ c = ![-c 1, c 0, -c 3, c 2] := by
    ext i
    fin_cases i <;>
      simp [TauCeti.frameComplexStructure_def, mulVec, dotProduct, Fin.sum_univ_four]
  -- The coordinates of `J v` are given by the matrix of `J`.
  have hJ : J (∑ i, c i • e i) = ∑ j, (TauCeti.frameComplexStructure *ᵥ c) j • e j := by
    rw [hd, map_sum]
    simp only [map_smul, Fin.sum_univ_four, h₀, h₁, h₂, h₃, cons_val_zero, cons_val_one,
      cons_val_two, cons_val_three, head_cons, tail_cons, smul_neg, neg_smul]
    abel
  rw [dotProduct_frameHermitianForm_mulVec, hJ, ιMulti_sum_smul]
  generalize TauCeti.frameComplexStructure *ᵥ c = d
  simp only [Fin.sum_univ_four, inner_add_right, real_inner_smul_right, frameMatrix, dotProduct,
    mulVec, of_apply]
  ring

include h₀ h₂ he in
/-- The smallest eigenvalue `c - |F⁻| / √2` of the Hermitian part of the matrix of `F` is
`⟪ω, F⟫ / 2 - ‖F - ⋆F‖ / (2 √2)`. -/
private theorem frameMatrix_eigenvalue_eq (F : ⋀[ℝ]^2 V) :
    (frameMatrix e F).frameInner TauCeti.frameKahlerForm / 2 -
        √((frameMatrix e F).frameAntiSelfDualPart.frameInner
          (frameMatrix e F).frameAntiSelfDualPart) / √2 =
      ⟪J.kahlerForm, F⟫ / 2 - ‖F - o.hodgeStar hkl F‖ / (2 * √2) := by
  have hF := transpose_frameMatrix (e := e) F
  have hω : (frameMatrix e F).frameInner TauCeti.frameKahlerForm = ⟪J.kahlerForm, F⟫ := by
    rw [Matrix.frameInner_frameKahlerForm hF, kahlerForm_eq_ιMulti_add_ιMulti h₀ h₂,
      inner_add_left, real_inner_comm F, real_inner_comm F]
    simp only [frameMatrix, of_apply]
  have hn : ‖F - o.hodgeStar hkl F‖ = 2 * √((frameMatrix e F).frameAntiSelfDualPart.frameInner
      (frameMatrix e F).frameAntiSelfDualPart) := by
    rw [← sq_eq_sq₀ (norm_nonneg _) (by positivity), mul_pow,
      Real.sq_sqrt (Matrix.frameInner_self_nonneg _),
      Matrix.frameInner_frameAntiSelfDualPart_self hF, o.norm_sub_hodgeStar_sq_eq_sum hkl he]
    simp only [Fin.sum_univ_three, OrthonormalBasis.antiSelfDualFrame, cons_val_zero,
      cons_val_one, cons_val_two, head_cons, tail_cons, real_inner_comm F,
      inner_sub_right, inner_add_right, frameMatrix, of_apply]
    ring
  rw [hω, hn]
  ring

/-- The bound for `-F`: the lower constant `c - ‖F⁻‖ / √2` of `-F` is minus the upper constant
`c + ‖F⁻‖ / √2` of `F`. -/
private theorem neg_eigenvalue (F : ⋀[ℝ]^2 V) :
    ⟪J.kahlerForm, -F⟫ / 2 - ‖-F - o.hodgeStar hkl (-F)‖ / (2 * √2) =
      -(⟪J.kahlerForm, F⟫ / 2 + ‖F - o.hodgeStar hkl F‖ / (2 * √2)) := by
  rw [inner_neg_right, map_neg, ← neg_add', norm_neg, ← sub_eq_add_neg]
  ring

include h₀ h₂ he in
/-- **The lower bound of the Hermitian part**: `F(v, J v) ≥ (c - ‖F⁻‖ / √2) ‖v‖²`, where
`c = ⟪ω, F⟫ / 2` and `‖F⁻‖ = ‖F - ⋆F‖ / 2`. -/
theorem mul_norm_sq_le_inner_ιMulti_apply (F : ⋀[ℝ]^2 V) (v : V) :
    (⟪J.kahlerForm, F⟫ / 2 - ‖F - o.hodgeStar hkl F‖ / (2 * √2)) * ‖v‖ ^ 2 ≤
      ⟪F, ιMulti ℝ 2 ![v, J v]⟫ := by
  set c : Fin 4 → ℝ := fun i ↦ e.repr v i
  have hv : ∑ i, c i • e i = v := e.sum_repr v
  have h := ((Matrix.posSemidef_frameHermitianForm_sub_smul_one_iff
    (transpose_frameMatrix (e := e) F)).2 le_rfl).dotProduct_mulVec_nonneg c
  rw [star_trivial, sub_mulVec, smul_mulVec, one_mulVec,
    dotProduct_sub, dotProduct_smul, smul_eq_mul, frameMatrix_eigenvalue_eq h₀ h₂ hkl he,
    ← inner_ιMulti_sum_smul h₀ h₂, ← norm_sum_smul_sq (e := e), hv] at h
  linarith

include h₀ h₂ he in
/-- **The upper bound of the Hermitian part**: `F(v, J v) ≤ (c + ‖F⁻‖ / √2) ‖v‖²`, where
`c = ⟪ω, F⟫ / 2` and `‖F⁻‖ = ‖F - ⋆F‖ / 2`. -/
theorem inner_ιMulti_apply_le_mul_norm_sq (F : ⋀[ℝ]^2 V) (v : V) :
    ⟪F, ιMulti ℝ 2 ![v, J v]⟫ ≤
      (⟪J.kahlerForm, F⟫ / 2 + ‖F - o.hodgeStar hkl F‖ / (2 * √2)) * ‖v‖ ^ 2 := by
  have h := mul_norm_sq_le_inner_ιMulti_apply h₀ h₂ hkl he (-F) v
  rw [neg_eigenvalue, inner_neg_left] at h
  linarith

include h₀ h₂ he in
/-- **The least eigenvalue of the Hermitian part of a two-form**: the minimum of `F(v, J v)` over
unit vectors `v` is `c - ‖F⁻‖ / √2`, where `c = ⟪ω, F⟫ / 2` and `‖F⁻‖ = ‖F - ⋆F‖ / 2`. Since
`F(v, J v) = B(v, v)` for the symmetric form `B(v, w) = (F(v, J w) + F(w, J v)) / 2`, this is
`λ_min(B) = c - ‖F⁻‖ / √2`. -/
theorem isLeast_inner_ιMulti_apply (F : ⋀[ℝ]^2 V) :
    IsLeast ((fun v ↦ ⟪F, ιMulti ℝ 2 ![v, J v]⟫) '' Metric.sphere 0 1)
      (⟪J.kahlerForm, F⟫ / 2 - ‖F - o.hodgeStar hkl F‖ / (2 * √2)) := by
  refine ⟨?_, ?_⟩
  · -- Normalize an eigenvector of the Hermitian part of the matrix of `F`.
    obtain ⟨c, hc0, hc⟩ :=
      Matrix.exists_frameHermitianForm_mulVec_eq (transpose_frameMatrix (e := e) F)
    rw [frameMatrix_eigenvalue_eq h₀ h₂ hkl he] at hc
    have hpos : 0 < c ⬝ᵥ c := lt_of_le_of_ne (dotProduct_self_star_nonneg c)
      (Ne.symm (dotProduct_self_eq_zero.not.2 hc0))
    set t := (√(c ⬝ᵥ c))⁻¹
    have ht : t ^ 2 * (c ⬝ᵥ c) = 1 := by
      rw [inv_pow, Real.sq_sqrt hpos.le, inv_mul_cancel₀ hpos.ne']
    refine ⟨∑ i, (t • c) i • e i, ?_, ?_⟩
    · rw [mem_sphere_zero_iff_norm, ← pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero,
        norm_sum_smul_sq, smul_dotProduct, dotProduct_smul, smul_eq_mul,
        smul_eq_mul]
      linear_combination ht
    · dsimp only
      rw [inner_ιMulti_sum_smul h₀ h₂, mulVec_smul, hc, smul_dotProduct,
        dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul, smul_eq_mul]
      linear_combination (⟪J.kahlerForm, F⟫ / 2 - ‖F - o.hodgeStar hkl F‖ / (2 * √2)) * ht
  · rintro _ ⟨v, hv, rfl⟩
    have h := mul_norm_sq_le_inner_ιMulti_apply h₀ h₂ hkl he F v
    rwa [show ‖v‖ = 1 by simpa using hv, one_pow, mul_one] at h

include h₀ h₂ he in
/-- **The greatest eigenvalue of the Hermitian part of a two-form**: the maximum of `F(v, J v)`
over unit vectors `v` is `c + ‖F⁻‖ / √2`, where `c = ⟪ω, F⟫ / 2` and `‖F⁻‖ = ‖F - ⋆F‖ / 2`. -/
theorem isGreatest_inner_ιMulti_apply (F : ⋀[ℝ]^2 V) :
    IsGreatest ((fun v ↦ ⟪F, ιMulti ℝ 2 ![v, J v]⟫) '' Metric.sphere 0 1)
      (⟪J.kahlerForm, F⟫ / 2 + ‖F - o.hodgeStar hkl F‖ / (2 * √2)) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨v, hv, h⟩ := (isLeast_inner_ιMulti_apply h₀ h₂ hkl he (-F)).1
    refine ⟨v, hv, ?_⟩
    dsimp only at h ⊢
    rw [neg_eigenvalue, inner_neg_left] at h
    linarith
  · rintro _ ⟨v, hv, rfl⟩
    have h := inner_ιMulti_apply_le_mul_norm_sq h₀ h₂ hkl he F v
    rwa [show ‖v‖ = 1 by simpa using hv, one_pow, mul_one] at h

include h₀ h₂ he in
/-- **A lower bound on the Hermitian part controls the anti-self-dual part**: if
`F(v, J v) ≥ -K ‖v‖²` for every `v`, then `‖F⁻‖ ≤ √2 (c + K)`, where `c = ⟪ω, F⟫ / 2` and
`F⁻ = (F - ⋆F) / 2`. -/
theorem norm_sub_hodgeStar_le_of_forall_le {F : ⋀[ℝ]^2 V} {K : ℝ}
    (h : ∀ v, -K * ‖v‖ ^ 2 ≤ ⟪F, ιMulti ℝ 2 ![v, J v]⟫) :
    ‖F - o.hodgeStar hkl F‖ / 2 ≤ √2 * (⟪J.kahlerForm, F⟫ / 2 + K) := by
  obtain ⟨v, hv, hmin⟩ := (isLeast_inner_ιMulti_apply h₀ h₂ hkl he F).1
  have hv1 : ‖v‖ = 1 := by simpa using hv
  have hK := h v
  rw [hv1, one_pow, mul_one] at hK
  dsimp only at hmin
  have h2 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs : 0 < √2 := by positivity
  have : ‖F - o.hodgeStar hkl F‖ / 2 = √2 * (‖F - o.hodgeStar hkl F‖ / (2 * √2)) := by
    field_simp
  rw [this]
  exact mul_le_mul_of_nonneg_left (by linarith) hs.le

end TauCeti.AlmostComplexStructure

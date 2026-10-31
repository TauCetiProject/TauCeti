/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.HodgeStar.Kahler
public import Mathlib.Order.Bounds.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Sum
import TauCeti.LinearAlgebra.Matrix.Determinant.FinFour
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The Hermitian part of a two-form in dimension four

Let `V` be an oriented four-dimensional real inner product space with an orthogonal complex
structure `J` whose orientation is the complex one, and let `ω` be its Kähler two-vector, with
`‖ω‖² = 2`. A two-vector `F ∈ ⋀² V` is read as the two-form `F(v, w) = ⟪F, v ∧ w⟫`. Its
**Hermitian part** is the `J`-invariant symmetric bilinear form
`B(v, w) = (F(v, J w) + F(w, J v)) / 2`, whose quadratic form is `B(v, v) = F(v, J v)`.

Split `F = c ω + F⁺₀ + F⁻`, where `c = ⟪ω, F⟫ / 2`, `F⁻ = (F - ⋆F) / 2` is the anti-self-dual
part, and `F⁺₀` is the self-dual part orthogonal to `ω`. The basic identity is that the
anti-self-dual part of `v ∧ J v` is `v ∧ J v - ‖v‖² ω / 2`, of norm `‖v‖² / √2`. Consequently

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

omit [Fact (finrank ℝ V = 4)] in
/-- `J v ∧ v = -(v ∧ J v)`. -/
private theorem ιMulti_apply_swap (v : V) :
    ιMulti ℝ 2 ![J v, v] = -ιMulti ℝ 2 ![v, J v] :=
  ext_inner_ιMulti_two fun u w ↦ by
    simp only [inner_neg_left, inner_ιMulti_two]
    ring

include h₀ h₂ he in
/-- The self-dual part of `v ∧ J v` is `‖v‖² ω / 2`: `v ∧ J v + ⋆(v ∧ J v) = ‖v‖² ω`. This is
`ιMulti_sub_ιMulti_add_hodgeStar` with `a = ξ = v`. -/
private theorem ιMulti_apply_add_hodgeStar (v : V) :
    ιMulti ℝ 2 ![v, J v] + o.hodgeStar hkl (ιMulti ℝ 2 ![v, J v]) =
      ‖v‖ ^ 2 • J.kahlerForm := by
  have h := ιMulti_sub_ιMulti_add_hodgeStar h₀ h₂ hkl he v v
  rw [ιMulti_apply_swap, sub_neg_eq_add, map_add, real_inner_self_eq_norm_sq] at h
  linear_combination (norm := module) (2⁻¹ : ℝ) • h

include h₀ h₂ he in
/-- `v ∧ J v - ‖v‖² ω / 2`, the anti-self-dual part of `v ∧ J v`, is anti-self-dual. -/
private theorem hodgeStar_asd (v : V) :
    o.hodgeStar hkl (ιMulti ℝ 2 ![v, J v] - (‖v‖ ^ 2 / 2) • J.kahlerForm) =
      -(ιMulti ℝ 2 ![v, J v] - (‖v‖ ^ 2 / 2) • J.kahlerForm) := by
  have h := ιMulti_apply_add_hodgeStar h₀ h₂ hkl he v
  rw [map_sub, map_smul, hodgeStar_kahlerForm h₀ h₂ hkl he]
  linear_combination (norm := module) h

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

include h₀ h₂ he in
/-- `F(v, J v) = c ‖v‖² + ⟪F⁻, v ∧ J v - ‖v‖² ω / 2⟫`, pairing `F⁻` with the anti-self-dual
part of `v ∧ J v`. -/
private theorem inner_ιMulti_apply_eq_add_inner_asd (F : ⋀[ℝ]^2 V) (v : V) :
    ⟪F, ιMulti ℝ 2 ![v, J v]⟫ = ⟪J.kahlerForm, F⟫ / 2 * ‖v‖ ^ 2 +
      ⟪(2⁻¹ : ℝ) • (F - o.hodgeStar hkl F),
        ιMulti ℝ 2 ![v, J v] - (‖v‖ ^ 2 / 2) • J.kahlerForm⟫ := by
  have hsym := o.isSymmetric_hodgeStar_of_even (by decide) hkl F J.kahlerForm
  rw [LinearEquiv.coe_coe, hodgeStar_kahlerForm h₀ h₂ hkl he] at hsym
  rw [inner_ιMulti_apply_eq h₀ h₂ hkl he, inner_sub_right, real_inner_smul_right,
    real_inner_smul_left (r := (2⁻¹ : ℝ)) (y := J.kahlerForm), inner_sub_left, hsym]
  ring

include h₀ h₂ in
/-- `‖v ∧ J v - ‖v‖² ω / 2‖ = ‖v‖² / √2`. -/
private theorem norm_asd (v : V) :
    ‖ιMulti ℝ 2 ![v, J v] - (‖v‖ ^ 2 / 2) • J.kahlerForm‖ = ‖v‖ ^ 2 / √2 := by
  have hJ := inner_apply_apply_of_orthonormalBasis h₀ h₂
  have hvJ : ⟪v, J v⟫ = 0 := by
    have := inner_apply_left hJ v v
    rw [real_inner_comm] at this
    linarith
  have h4 : (finrank ℝ V : ℝ) = 4 := by exact_mod_cast (Fact.out : finrank ℝ V = 4)
  have hxx : ⟪ιMulti ℝ 2 ![v, J v], ιMulti ℝ 2 ![v, J v]⟫ = ‖v‖ ^ 4 := by
    rw [inner_ιMulti_two, hJ, hvJ, real_inner_self_eq_norm_sq]
    ring
  have hxω : ⟪ιMulti ℝ 2 ![v, J v], J.kahlerForm⟫ = ‖v‖ ^ 2 := by
    rw [real_inner_comm, inner_kahlerForm_ιMulti hJ, hJ, real_inner_self_eq_norm_sq]
  rw [← sq_eq_sq₀ (norm_nonneg _) (by positivity), div_pow, Real.sq_sqrt (by norm_num),
    ← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right, real_inner_smul_left, real_inner_smul_right,
    hxx, hxω, real_inner_comm, hxω, inner_kahlerForm_self hJ, h4]
  ring

/-- The anti-self-dual frame `e₀ ∧ e₁ - e₂ ∧ e₃`, `e₀ ∧ e₂ + e₁ ∧ e₃`, `e₀ ∧ e₃ - e₁ ∧ e₂`. -/
private def asdFrame (e : OrthonormalBasis (Fin 4) ℝ V) : Fin 3 → ⋀[ℝ]^2 V :=
  ![ιMulti ℝ 2 ![e 0, e 1] - ιMulti ℝ 2 ![e 2, e 3],
    ιMulti ℝ 2 ![e 0, e 2] + ιMulti ℝ 2 ![e 1, e 3],
    ιMulti ℝ 2 ![e 0, e 3] - ιMulti ℝ 2 ![e 1, e 2]]

include he in
/-- `F - ⋆F = ∑ₖ ⟪φₖ, F⟫ φₖ` for the anti-self-dual frame `φ`. -/
private theorem sub_hodgeStar_eq_sum (F : ⋀[ℝ]^2 V) :
    F - o.hodgeStar hkl F = ∑ k, ⟪asdFrame e k, F⟫ • asdFrame e k := by
  have key : (LinearMap.id - (o.hodgeStar hkl).toLinearMap : ⋀[ℝ]^2 V →ₗ[ℝ] ⋀[ℝ]^2 V) =
      ∑ k, (innerₗ _ (asdFrame e k)).smulRight (asdFrame e k) := by
    refine linearMap_ext_inner_ιMulti_two fun a b u w ↦ ?_
    simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearEquiv.coe_coe,
      LinearMap.add_apply, LinearMap.smulRight_apply, innerₗ_apply_apply,
      real_inner_smul_left, Fin.sum_univ_three, asdFrame, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
      Matrix.tail_cons, inner_sub_left, inner_add_left, o.inner_hodgeStar_ιMulti_two hkl,
      inner_ιMulti_two, o.volumeForm_robust e he, Basis.det_apply, Matrix.det_fin_four,
      Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply]
    -- Write every pairing in the coordinates of `e`; the identity is then polynomial.
    simp only [← e.repr_apply_apply]
    simp only [e.inner_eq_sum_repr, conj_trivial, Fin.sum_univ_four]
    ring
  simpa using LinearMap.congr_fun key F

omit [Fact (finrank ℝ V = 4)] in
/-- The anti-self-dual frame is orthogonal, with `‖φₖ‖² = 2`. -/
private theorem inner_asdFrame (k l : Fin 3) :
    ⟪asdFrame e k, asdFrame e l⟫ = if k = l then 2 else 0 := by
  fin_cases k <;> fin_cases l <;>
    simp only [asdFrame, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
      inner_ιMulti_two, OrthonormalBasis.inner_eq_ite] <;>
    norm_num

include he in
/-- `‖F - ⋆F‖² = 2 ∑ₖ ⟪φₖ, F⟫²`. -/
private theorem norm_sub_hodgeStar_sq (F : ⋀[ℝ]^2 V) :
    ‖F - o.hodgeStar hkl F‖ ^ 2 = 2 * ∑ k, ⟪asdFrame e k, F⟫ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, sub_hodgeStar_eq_sum hkl he F]
  simp only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right, inner_asdFrame,
    mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp only [Fin.sum_univ_three]
  ring

/-- A vector in the coordinates of the frame `e`. -/
private def frameVec (e : OrthonormalBasis (Fin 4) ℝ V) (c : Fin 4 → ℝ) : V := ∑ i, c i • e i

omit [FiniteDimensional ℝ V] [Fact (finrank ℝ V = 4)] in
/-- `‖∑ᵢ cᵢ eᵢ‖² = ∑ᵢ cᵢ²`. -/
private theorem norm_frameVec_sq (c : Fin 4 → ℝ) :
    ‖frameVec e c‖ ^ 2 = c 0 ^ 2 + c 1 ^ 2 + c 2 ^ 2 + c 3 ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [frameVec, Fin.sum_univ_four, inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right, OrthonormalBasis.inner_eq_ite]
  simp
  ring

omit [Fact (finrank ℝ V = 4)] in
include h₀ h₂ in
/-- The pairings of the anti-self-dual frame with `v ∧ J v - ‖v‖² ω / 2` in coordinates. -/
private theorem inner_asdFrame_asd (c : Fin 4 → ℝ) (k : Fin 3) :
    ⟪asdFrame e k, ιMulti ℝ 2 ![frameVec e c, J (frameVec e c)] -
        (‖frameVec e c‖ ^ 2 / 2) • J.kahlerForm⟫ =
      ![c 0 ^ 2 + c 1 ^ 2 - c 2 ^ 2 - c 3 ^ 2, 2 * (c 1 * c 2 - c 0 * c 3),
        2 * (c 0 * c 2 + c 1 * c 3)] k := by
  have h₁ : J (e 1) = -e 0 := by rw [← h₀, J.apply_apply]
  have h₃ : J (e 3) = -e 2 := by rw [← h₂, J.apply_apply]
  have hJv : J (frameVec e c) = c 0 • e 1 - c 1 • e 0 + c 2 • e 3 - c 3 • e 2 := by
    simp only [frameVec, Fin.sum_univ_four, map_add, map_smul, h₀, h₁, h₂, h₃, smul_neg]
    abel
  rw [hJv, kahlerForm_eq_ιMulti_add_ιMulti h₀ h₂, norm_frameVec_sq]
  fin_cases k <;>
    simp only [asdFrame, frameVec, Fin.sum_univ_four, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
      Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, inner_add_left, inner_add_right, inner_sub_left,
      inner_sub_right, real_inner_smul_right, inner_ιMulti_two, OrthonormalBasis.inner_eq_ite] <;>
    simp <;> ring

include h₀ h₂ he in
/-- The pairing of `F` with the anti-self-dual part of `v ∧ J v` only sees `F⁻ = (F - ⋆F) / 2`. -/
private theorem inner_asd_eq (F : ⋀[ℝ]^2 V) (v : V) :
    ⟪F, ιMulti ℝ 2 ![v, J v] - (‖v‖ ^ 2 / 2) • J.kahlerForm⟫ =
      ⟪(2⁻¹ : ℝ) • (F - o.hodgeStar hkl F),
        ιMulti ℝ 2 ![v, J v] - (‖v‖ ^ 2 / 2) • J.kahlerForm⟫ := by
  have hsym := o.isSymmetric_hodgeStar_of_even (by decide) hkl F
    (ιMulti ℝ 2 ![v, J v] - (‖v‖ ^ 2 / 2) • J.kahlerForm)
  rw [LinearEquiv.coe_coe, hodgeStar_asd h₀ h₂ hkl he, inner_neg_right] at hsym
  rw [real_inner_smul_left, inner_sub_left, hsym]
  ring

include h₀ h₂ hkl he in
/-- The value of `⟪F, v ∧ J v - ‖v‖² ω / 2⟫` in the coordinates of the frame. -/
private theorem inner_asd_frameVec (F : ⋀[ℝ]^2 V) (c : Fin 4 → ℝ) :
    ⟪F, ιMulti ℝ 2 ![frameVec e c, J (frameVec e c)] -
        (‖frameVec e c‖ ^ 2 / 2) • J.kahlerForm⟫ =
      (⟪asdFrame e 0, F⟫ * (c 0 ^ 2 + c 1 ^ 2 - c 2 ^ 2 - c 3 ^ 2) +
        ⟪asdFrame e 1, F⟫ * (2 * (c 1 * c 2 - c 0 * c 3)) +
        ⟪asdFrame e 2, F⟫ * (2 * (c 0 * c 2 + c 1 * c 3))) / 2 := by
  rw [inner_asd_eq h₀ h₂ hkl he, sub_hodgeStar_eq_sum hkl he F, real_inner_smul_left, sum_inner,
    Fin.sum_univ_three]
  simp only [real_inner_smul_left, inner_asdFrame_asd h₀ h₂]
  simp
  ring

include h₀ h₂ he in
/-- The minimum `-‖F⁻‖ / √2` of `⟪F, v ∧ J v - ‖v‖² ω / 2⟫` over unit vectors is attained. -/
private theorem exists_inner_asd_eq (F : ⋀[ℝ]^2 V) :
    ∃ v : V, ‖v‖ = 1 ∧ ⟪F, ιMulti ℝ 2 ![v, J v] - (‖v‖ ^ 2 / 2) • J.kahlerForm⟫ =
      -(‖F - o.hodgeStar hkl F‖ / (2 * √2)) := by
  set R := ‖F - o.hodgeStar hkl F‖ / (2 * √2)
  set A := ⟪asdFrame e 0, F⟫ / 2
  set B := ⟪asdFrame e 1, F⟫ / 2
  set C := ⟪asdFrame e 2, F⟫ / 2
  have hR0 : 0 ≤ R := by positivity
  have hR : R ^ 2 = A ^ 2 + B ^ 2 + C ^ 2 := by
    have h := norm_sub_hodgeStar_sq hkl he F
    simp only [Fin.sum_univ_three] at h
    rw [div_pow, h, mul_pow, Real.sq_sqrt (by norm_num)]
    ring
  -- An eigenvector of the quadratic form for its least eigenvalue `-R`, before normalization.
  obtain ⟨c, hc, hval⟩ : ∃ c : Fin 4 → ℝ, 0 < c 0 ^ 2 + c 1 ^ 2 + c 2 ^ 2 + c 3 ^ 2 ∧
      A * (c 0 ^ 2 + c 1 ^ 2 - c 2 ^ 2 - c 3 ^ 2) + B * (2 * (c 1 * c 2 - c 0 * c 3)) +
        C * (2 * (c 0 * c 2 + c 1 * c 3)) = -R * (c 0 ^ 2 + c 1 ^ 2 + c 2 ^ 2 + c 3 ^ 2) := by
    rcases hR0.eq_or_lt with h0 | hpos
    · refine ⟨![1, 0, 0, 0], by simp, ?_⟩
      have hA : A = 0 := by nlinarith
      simp [hA, ← h0]
    rcases lt_or_ge A R with hA | hA
    · refine ⟨![R - A, 0, -C, B], ?_, ?_⟩
      · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
        nlinarith
      · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
        linear_combination (R - A) * hR
    · refine ⟨![-C, -B, R + A, 0], ?_, ?_⟩
      · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
        nlinarith
      · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
        linear_combination (R + A) * hR
  -- Normalize the eigenvector.
  set S := c 0 ^ 2 + c 1 ^ 2 + c 2 ^ 2 + c 3 ^ 2
  set t := (√S)⁻¹
  have ht : t ^ 2 * S = 1 := by
    rw [inv_pow, Real.sq_sqrt hc.le, inv_mul_cancel₀ hc.ne']
  refine ⟨frameVec e fun i ↦ t * c i, ?_, ?_⟩
  · rw [← pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero, norm_frameVec_sq]
    linear_combination ht
  · rw [inner_asd_frameVec h₀ h₂ hkl he]
    linear_combination t ^ 2 * hval - R * ht

include h₀ h₂ he in
/-- **The lower bound of the Hermitian part**: `F(v, J v) ≥ (c - ‖F⁻‖ / √2) ‖v‖²`, where
`c = ⟪ω, F⟫ / 2` and `‖F⁻‖ = ‖F - ⋆F‖ / 2`. -/
theorem mul_norm_sq_le_inner_ιMulti_apply (F : ⋀[ℝ]^2 V) (v : V) :
    (⟪J.kahlerForm, F⟫ / 2 - ‖F - o.hodgeStar hkl F‖ / (2 * √2)) * ‖v‖ ^ 2 ≤
      ⟪F, ιMulti ℝ 2 ![v, J v]⟫ := by
  rw [inner_ιMulti_apply_eq_add_inner_asd h₀ h₂ hkl he]
  have h := abs_real_inner_le_norm ((2⁻¹ : ℝ) • (F - o.hodgeStar hkl F))
    (ιMulti ℝ 2 ![v, J v] - (‖v‖ ^ 2 / 2) • J.kahlerForm)
  rw [norm_smul, norm_asd h₀ h₂, Real.norm_of_nonneg (by norm_num)] at h
  have h' := neg_abs_le ⟪(2⁻¹ : ℝ) • (F - o.hodgeStar hkl F),
    ιMulti ℝ 2 ![v, J v] - (‖v‖ ^ 2 / 2) • J.kahlerForm⟫
  have : 2⁻¹ * ‖F - o.hodgeStar hkl F‖ * (‖v‖ ^ 2 / √2) =
      ‖F - o.hodgeStar hkl F‖ / (2 * √2) * ‖v‖ ^ 2 := by
    ring
  linarith

include h₀ h₂ he in
/-- **The upper bound of the Hermitian part**: `F(v, J v) ≤ (c + ‖F⁻‖ / √2) ‖v‖²`, where
`c = ⟪ω, F⟫ / 2` and `‖F⁻‖ = ‖F - ⋆F‖ / 2`. -/
theorem inner_ιMulti_apply_le_mul_norm_sq (F : ⋀[ℝ]^2 V) (v : V) :
    ⟪F, ιMulti ℝ 2 ![v, J v]⟫ ≤
      (⟪J.kahlerForm, F⟫ / 2 + ‖F - o.hodgeStar hkl F‖ / (2 * √2)) * ‖v‖ ^ 2 := by
  have h := mul_norm_sq_le_inner_ιMulti_apply h₀ h₂ hkl he (-F) v
  rw [inner_neg_left, inner_neg_right, map_neg, ← neg_add', norm_neg, ← sub_eq_add_neg] at h
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
  · obtain ⟨v, hv, h⟩ := exists_inner_asd_eq h₀ h₂ hkl he F
    refine ⟨v, by simpa using hv, ?_⟩
    dsimp only
    rw [inner_ιMulti_apply_eq_add_inner_asd h₀ h₂ hkl he, ← inner_asd_eq h₀ h₂ hkl he, h, hv]
    ring
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
    rw [inner_neg_left, inner_neg_right, map_neg, ← neg_add', norm_neg,
      ← sub_eq_add_neg] at h
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

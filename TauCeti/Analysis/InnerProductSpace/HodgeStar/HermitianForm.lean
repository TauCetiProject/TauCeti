/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.HodgeStar.ComplexStructure

/-!
# The eigenvalues of the `J`-Hermitian part of a two-form in dimension four

Let `V` be an oriented four-dimensional real inner product space and `J` an orthogonal almost
complex structure inducing the orientation, with Kähler two-vector `ω`
(`TauCeti.AlmostComplexStructure.kahlerForm`), so that `‖ω‖² = 2`. A two-vector `F` represents
the two-form `F(u, w) = ⟪F, u ∧ w⟫`, and its **`J`-Hermitian part** is the symmetric bilinear form

`B(v, w) = (F(v, J w) + F(w, J v)) / 2`.

Its quadratic form is `B(v, v) = F(v, J v) = ⟪F, v ∧ J v⟫`, which determines `B` by
polarization, so the eigenvalues of `B` relative to the inner product are the critical values of
`v ↦ ⟪F, v ∧ J v⟫` on the unit sphere. Split `F = F⁺ + F⁻` into its self-dual and anti-self-dual
parts `F^± = (F ± ⋆F) / 2` and put `c = ⟪ω, F⟫ / 2`. This file proves

`λ_min(B) = c - ‖F⁻‖ / √2`,  `λ_max(B) = c + ‖F⁻‖ / √2`.

The self-dual part enters only through `c`: `⟪F⁺, v ∧ J v⟫ = c ‖v‖²`, so the component of `F⁺`
orthogonal to `ω` (its anti-`J`-invariant part) contributes nothing to `B`. The anti-self-dual
part satisfies `|⟪F⁻, v ∧ J v⟫| ≤ (‖F⁻‖ / √2) ‖v‖²`, and both signs of this bound are attained:
anti-self-dual forms are `J`-invariant, the operator `T = J ∘ (· ⌟ F⁻)` is symmetric with
`T² = ‖F⁻‖² / 2`, and `T` is not a multiple of the identity since `⟪ω, F⁻⟫ = 0`.

In Taubes's analysis of the Seiberg–Witten equations on a symplectic four-manifold, `F` is the
curvature form `i F_a` of a connection. A lower bound `B ≥ -C g` on its Hermitian part then gives
the bound `‖F⁻‖ ≤ √2 (c + C)` on the anti-self-dual curvature, and conversely bounds on `c` and
`‖F⁻‖` bound `F(v, J v)` from below on every `J`-complex line
(`forall_mul_norm_sq_le_inner_ιMulti_apply_iff`).

As in `TauCeti.Analysis.InnerProductSpace.HodgeStar.Kahler`, statements take a positively
oriented orthonormal basis `e` with `J e₀ = e₁` and `J e₂ = e₃` as a witness that the orientation
is the complex one; the conclusions do not depend on the choice of such a frame.

## Main results

In the namespace `TauCeti.AlmostComplexStructure`:

* `inner_add_hodgeStar_ιMulti_apply`: `⟪F + ⋆F, v ∧ J v⟫ = ‖v‖² ⟪ω, F⟫`.
* `inner_ιMulti_apply_eq_zero`: anti-`J`-invariant self-dual forms (`⋆η = η`, `⟪ω, η⟫ = 0`)
  vanish on every `v ∧ J v`.
* `inner_ιMulti_apply_eq_add`: `⟪F, v ∧ J v⟫ = c ‖v‖² + ⟪F⁻, v ∧ J v⟫`.
* `exists_norm_eq_one_inner_ιMulti_apply_eq_neg`: an anti-self-dual `η` takes the value
  `-‖η‖ / √2` on `v ∧ J v` for some unit vector `v`.
* `isLeast_inner_ιMulti_apply`, `isGreatest_inner_ιMulti_apply`: the minimum and maximum of
  `⟪F, v ∧ J v⟫` over unit vectors are `c ∓ ‖F⁻‖ / √2`.
* `forall_mul_norm_sq_le_inner_ιMulti_apply_iff`: `a ‖v‖² ≤ ⟪F, v ∧ J v⟫` for all `v` if and only
  if `a ≤ c - ‖F⁻‖ / √2`.

## References

* C. H. Taubes, *SW ⇒ Gr: From the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
* S. K. Donaldson and P. B. Kronheimer, *The Geometry of Four-Manifolds*, Oxford (1990).
-/

public section

noncomputable section

open Module exteriorPower
open scoped RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [Fact (finrank ℝ V = 4)]

namespace TauCeti.AlmostComplexStructure

variable {e : OrthonormalBasis (Fin 4) ℝ V} {J : AlmostComplexStructure V}
  (h₀ : J (e 0) = e 1) (h₂ : J (e 2) = e 3) {o : Orientation ℝ V (Fin 4)}
  (hkl : 2 + 2 = finrank ℝ V) (he : e.toBasis.orientation = o)

include he h₀ h₂ in
/-- **Only the `ω`-component of the self-dual part pairs with `v ∧ J v`**:
`⟪F + ⋆F, v ∧ J v⟫ = ‖v‖² ⟪ω, F⟫`. -/
theorem inner_add_hodgeStar_ιMulti_apply (F : ⋀[ℝ]^2 V) (v : V) :
    ⟪F + o.hodgeStar hkl F, ιMulti ℝ 2 ![v, J v]⟫ = ‖v‖ ^ 2 * ⟪J.kahlerForm, F⟫ := by
  have hswap : ιMulti ℝ 2 ![J v, v] = -ιMulti ℝ 2 ![v, J v] :=
    ext_inner_ιMulti_two fun a b ↦ by
      rw [inner_neg_left, inner_ιMulti_two, inner_ιMulti_two]
      ring
  -- The self-dual part of `v ∧ J v` is `(‖v‖² / 2) ω`.
  have h := ιMulti_sub_ιMulti_add_hodgeStar h₀ h₂ hkl he v v
  rw [hswap, sub_neg_eq_add, ← two_smul ℝ, map_smul, ← smul_add, real_inner_self_eq_norm_sq,
    mul_smul] at h
  have hsd := smul_right_injective _ two_ne_zero h
  have hs := o.isSymmetric_hodgeStar_of_even even_two hkl F (ιMulti ℝ 2 ![v, J v])
  simp only [LinearEquiv.coe_coe] at hs
  rw [inner_add_left, hs, ← inner_add_right, hsd, real_inner_smul_right, real_inner_comm]

include he h₀ h₂ in
/-- **Anti-`J`-invariant self-dual forms do not contribute to the `J`-Hermitian part**: for
`⋆η = η` with `⟪ω, η⟫ = 0`, `⟪η, v ∧ J v⟫ = 0`. -/
theorem inner_ιMulti_apply_eq_zero {η : ⋀[ℝ]^2 V} (hη : o.hodgeStar hkl η = η)
    (hω : ⟪J.kahlerForm, η⟫ = 0) (v : V) : ⟪η, ιMulti ℝ 2 ![v, J v]⟫ = 0 := by
  have h := inner_add_hodgeStar_ιMulti_apply h₀ h₂ hkl he η v
  rw [hη, hω, mul_zero, inner_add_left] at h
  linarith

include he h₀ h₂ in
/-- **The `J`-Hermitian part of a two-form**: with `c = ⟪ω, F⟫ / 2` and the anti-self-dual part
`F⁻ = (F - ⋆F) / 2`, `⟪F, v ∧ J v⟫ = c ‖v‖² + ⟪F⁻, v ∧ J v⟫`. -/
theorem inner_ιMulti_apply_eq_add (F : ⋀[ℝ]^2 V) (v : V) :
    ⟪F, ιMulti ℝ 2 ![v, J v]⟫ = ⟪J.kahlerForm, F⟫ / 2 * ‖v‖ ^ 2 +
      ⟪(2⁻¹ : ℝ) • (F - o.hodgeStar hkl F), ιMulti ℝ 2 ![v, J v]⟫ := by
  have h := inner_add_hodgeStar_ιMulti_apply h₀ h₂ hkl he F v
  rw [inner_add_left] at h
  rw [real_inner_smul_left, inner_sub_left]
  linarith

include he h₀ h₂ in
/-- **The extreme value of an anti-self-dual form on `J`-complex lines**: for `⋆η = -η` there is a
unit vector `v` with `⟪η, v ∧ J v⟫ = -‖η‖ / √2`. -/
theorem exists_norm_eq_one_inner_ιMulti_apply_eq_neg {η : ⋀[ℝ]^2 V}
    (hη : o.hodgeStar hkl η = -η) :
    ∃ v : V, ‖v‖ = 1 ∧ ⟪η, ιMulti ℝ 2 ![v, J v]⟫ = -(‖η‖ / √2) := by
  have hJ := inner_apply_apply_of_orthonormalBasis h₀ h₂
  rcases eq_or_ne η 0 with rfl | hη₀
  · exact ⟨e 0, e.orthonormal.1 0, by simp⟩
  set K := twoVectorContraction η
  set l := ‖η‖ / √2
  -- `⟪η, v ∧ J v⟫ = -⟪T v, v⟫` for the operator `T = J ∘ K`.
  have hQ (v : V) : ⟪η, ιMulti ℝ 2 ![v, J v]⟫ = -⟪J (K v), v⟫ := by
    rw [← inner_twoVectorContraction_apply, inner_apply_left hJ, neg_neg]
  -- Since `K` commutes with `J`, `T² = -K² = l²`.
  have hTT (w : V) : J (K (J (K w))) = l ^ 2 • w := by
    have hc := LinearMap.congr_fun
      (twoVectorContraction_comp_comm_of_hodgeStar_eq_neg h₀ h₂ hkl he hη) (K w)
    have hK := LinearMap.congr_fun (twoVectorContraction_comp_self o hkl (Or.inr hη)) w
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply] at hc hK
    rw [hc, J.apply_apply, hK, div_pow, Real.sq_sqrt zero_le_two, neg_smul, neg_neg]
  -- `T` is not `-l`: otherwise `⟪η, ω⟫ = ⟪η, e₀ ∧ e₁⟫ + ⟪η, e₂ ∧ e₃⟫ = 2 l > 0`.
  obtain ⟨w, hw⟩ : ∃ w, J (K w) + l • w ≠ 0 := by
    by_contra! h
    have hl : 0 < l := by
      have := norm_pos_iff.2 hη₀
      positivity
    have hω := inner_kahlerForm_eq_zero_of_hodgeStar_eq_neg h₀ h₂ hkl he hη
    have hT (v : V) : ⟪η, ιMulti ℝ 2 ![v, J v]⟫ = l * ‖v‖ ^ 2 := by
      rw [hQ, eq_neg_of_add_eq_zero_left (h v), inner_neg_left, neg_neg, real_inner_smul_left,
        real_inner_self_eq_norm_sq]
    rw [kahlerForm_eq_ιMulti_add_ιMulti h₀ h₂, inner_add_left, real_inner_comm η,
      real_inner_comm η, ← h₀, ← h₂, hT, hT, e.orthonormal.1 0,
      e.orthonormal.1 2] at hω
    linarith
  -- Then `x = T w + l w` is an eigenvector of `T` with eigenvalue `l`.
  set x := J (K w) + l • w
  have hx : J (K x) = l • x := by
    simp only [x, map_add, map_smul, hTT, J.apply_smul, smul_add, smul_smul, pow_two]
    abel
  have hx₀ : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hw
  refine ⟨‖x‖⁻¹ • x, by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hx₀], ?_⟩
  rw [hQ, map_smul, J.apply_smul, hx, real_inner_smul_left, real_inner_smul_right,
    real_inner_smul_left, real_inner_self_eq_norm_sq]
  field_simp

include he h₀ h₂ in
/-- **The lower bound of the `J`-Hermitian part**:
`(c - ‖F⁻‖ / √2) ‖v‖² ≤ ⟪F, v ∧ J v⟫`, where `c = ⟪ω, F⟫ / 2` and `F⁻ = (F - ⋆F) / 2`. -/
theorem le_inner_ιMulti_apply (F : ⋀[ℝ]^2 V) (v : V) :
    (⟪J.kahlerForm, F⟫ / 2 - ‖(2⁻¹ : ℝ) • (F - o.hodgeStar hkl F)‖ / √2) * ‖v‖ ^ 2 ≤
      ⟪F, ιMulti ℝ 2 ![v, J v]⟫ := by
  have h := TauCeti.abs_inner_ιMulti_le o hkl
    (Or.inr (o.hodgeStar_smul_sub_hodgeStar even_two hkl 2⁻¹ F)) v (J v)
  rw [norm_apply (inner_apply_apply_of_orthonormalBasis h₀ h₂), mul_assoc, ← pow_two] at h
  rw [inner_ιMulti_apply_eq_add h₀ h₂ hkl he F v]
  linarith [neg_abs_le ⟪(2⁻¹ : ℝ) • (F - o.hodgeStar hkl F), ιMulti ℝ 2 ![v, J v]⟫]

include he h₀ h₂ in
/-- **The upper bound of the `J`-Hermitian part**:
`⟪F, v ∧ J v⟫ ≤ (c + ‖F⁻‖ / √2) ‖v‖²`, where `c = ⟪ω, F⟫ / 2` and `F⁻ = (F - ⋆F) / 2`. -/
theorem inner_ιMulti_apply_le (F : ⋀[ℝ]^2 V) (v : V) :
    ⟪F, ιMulti ℝ 2 ![v, J v]⟫ ≤
      (⟪J.kahlerForm, F⟫ / 2 + ‖(2⁻¹ : ℝ) • (F - o.hodgeStar hkl F)‖ / √2) * ‖v‖ ^ 2 := by
  have h := le_inner_ιMulti_apply h₀ h₂ hkl he (-F) v
  have hneg : (2⁻¹ : ℝ) • (-F - o.hodgeStar hkl (-F)) = -((2⁻¹ : ℝ) • (F - o.hodgeStar hkl F)) := by
    rw [map_neg]
    module
  rw [hneg, norm_neg, inner_neg_right, inner_neg_left] at h
  linarith

include he h₀ h₂ in
/-- **The smallest eigenvalue of the `J`-Hermitian part of a two-form**: the minimum of
`⟪F, v ∧ J v⟫` over unit vectors `v` is `λ_min(B) = c - ‖F⁻‖ / √2`, where `c = ⟪ω, F⟫ / 2` and
`F⁻ = (F - ⋆F) / 2` is the anti-self-dual part of `F`. -/
theorem isLeast_inner_ιMulti_apply (F : ⋀[ℝ]^2 V) :
    IsLeast ((fun v ↦ ⟪F, ιMulti ℝ 2 ![v, J v]⟫) '' Metric.sphere 0 1)
      (⟪J.kahlerForm, F⟫ / 2 - ‖(2⁻¹ : ℝ) • (F - o.hodgeStar hkl F)‖ / √2) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨v, hv, h⟩ := exists_norm_eq_one_inner_ιMulti_apply_eq_neg h₀ h₂ hkl he
      (o.hodgeStar_smul_sub_hodgeStar even_two hkl 2⁻¹ F)
    refine ⟨v, mem_sphere_zero_iff_norm.2 hv, ?_⟩
    dsimp only
    rw [inner_ιMulti_apply_eq_add h₀ h₂ hkl he F v, h, hv]
    ring
  · rintro _ ⟨v, hv, rfl⟩
    simpa [mem_sphere_zero_iff_norm.1 hv] using le_inner_ιMulti_apply h₀ h₂ hkl he F v

include he h₀ h₂ in
/-- **The largest eigenvalue of the `J`-Hermitian part of a two-form**: the maximum of
`⟪F, v ∧ J v⟫` over unit vectors `v` is `λ_max(B) = c + ‖F⁻‖ / √2`, where `c = ⟪ω, F⟫ / 2` and
`F⁻ = (F - ⋆F) / 2` is the anti-self-dual part of `F`. -/
theorem isGreatest_inner_ιMulti_apply (F : ⋀[ℝ]^2 V) :
    IsGreatest ((fun v ↦ ⟪F, ιMulti ℝ 2 ![v, J v]⟫) '' Metric.sphere 0 1)
      (⟪J.kahlerForm, F⟫ / 2 + ‖(2⁻¹ : ℝ) • (F - o.hodgeStar hkl F)‖ / √2) := by
  refine ⟨?_, ?_⟩
  · have hη := o.hodgeStar_smul_sub_hodgeStar even_two hkl 2⁻¹ F
    obtain ⟨v, hv, h⟩ := exists_norm_eq_one_inner_ιMulti_apply_eq_neg h₀ h₂ hkl he
      (η := -((2⁻¹ : ℝ) • (F - o.hodgeStar hkl F))) (by rw [map_neg, hη])
    rw [inner_neg_left, norm_neg, neg_inj] at h
    refine ⟨v, mem_sphere_zero_iff_norm.2 hv, ?_⟩
    dsimp only
    rw [inner_ιMulti_apply_eq_add h₀ h₂ hkl he F v, h, hv]
    ring
  · rintro _ ⟨v, hv, rfl⟩
    simpa [mem_sphere_zero_iff_norm.1 hv] using inner_ιMulti_apply_le h₀ h₂ hkl he F v

include he h₀ h₂ in
/-- **Lower bounds of the `J`-Hermitian part**: `a ‖v‖² ≤ ⟪F, v ∧ J v⟫` holds for every `v` if and
only if `a ≤ c - ‖F⁻‖ / √2`, where `c = ⟪ω, F⟫ / 2` and `F⁻ = (F - ⋆F) / 2`. With `a = -C`, the
Hermitian part satisfies `B ≥ -C g` exactly when `‖F⁻‖ ≤ √2 (c + C)`. -/
theorem forall_mul_norm_sq_le_inner_ιMulti_apply_iff (F : ⋀[ℝ]^2 V) {a : ℝ} :
    (∀ v, a * ‖v‖ ^ 2 ≤ ⟪F, ιMulti ℝ 2 ![v, J v]⟫) ↔
      a ≤ ⟪J.kahlerForm, F⟫ / 2 - ‖(2⁻¹ : ℝ) • (F - o.hodgeStar hkl F)‖ / √2 := by
  refine ⟨fun h ↦ ?_, fun h v ↦ ?_⟩
  · obtain ⟨v, hv, hv'⟩ := (isLeast_inner_ιMulti_apply h₀ h₂ hkl he F).1
    have h' := h v
    rw [mem_sphere_zero_iff_norm.1 hv, one_pow, mul_one] at h'
    exact h'.trans_eq hv'
  · exact (mul_le_mul_of_nonneg_right h (sq_nonneg _)).trans
      (le_inner_ιMulti_apply h₀ h₂ hkl he F v)

end TauCeti.AlmostComplexStructure

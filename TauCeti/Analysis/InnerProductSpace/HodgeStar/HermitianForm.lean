/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.HodgeStar.ComplexStructure

/-!
# The Hermitian form of a two-form and its extreme eigenvalues

Let `V` be a real inner product space with an orthogonal almost complex structure `J`, and let a
two-vector `F ∈ ⋀² V` represent the two-form `F(v, w) = ⟪F, v ∧ w⟫`. The **Hermitian form** of
`F` is the symmetric bilinear form
`B(v, w) = (F(v, J w) + F(w, J v)) / 2`
(`TauCeti.AlmostComplexStructure.hermitianForm`), so that `B(v, v) = F(v, J v)`. It only sees the
`J`-invariant part of `F`: for the Kähler form `ω` it is the metric, `B_ω = g`, and in dimension
four the self-dual forms orthogonal to `ω`, which are anti-`J`-invariant, contribute zero.

In dimension four, for the complex orientation, write `F = F⁺ + F⁻` with `F⁻ = (F - ⋆F) / 2`
anti-self-dual and put `c = ⟪F, ω⟫ / 2`, so that `‖ω‖² = 2` and `ω = e¹² + e³⁴` in a unitary
frame. Then
`B(v, v) = c ‖v‖² + ⟪F⁻, v ∧ J v⟫`,
because the self-dual part of `v ∧ J v` is `‖v‖² ω / 2`. The anti-self-dual forms are
`J`-invariant, so the contraction `A = (· ⌟ F⁻)` commutes with `J` and satisfies
`A² = -(‖F⁻‖² / 2)`. Thus `J A` is a symmetric operator with eigenvalues `±‖F⁻‖ / √2`, and
`⟪F⁻, v ∧ J v⟫ = -⟪J A v, v⟫`. Consequently the extreme eigenvalues of `B` are
`λ_min(B) = c - ‖F⁻‖ / √2`,  `λ_max(B) = c + ‖F⁻‖ / √2`.

This is the pointwise linear algebra behind Taubes's estimate of the anti-self-dual curvature of
Seiberg–Witten solutions on a symplectic four-manifold: for the curvature `F = i F_a`, a lower
bound `B ≥ m g` gives `‖F⁻‖ ≤ √2 (c - m)`, so a bound on the Hermitian form converts the control
of `c = ⟪i F_a, ω⟫ / 2` supplied by the curvature equation into control of `F_a⁻`.

Statements in dimension four take a positively oriented orthonormal basis `e` with
`J e₀ = e₁` and `J e₂ = e₃` as a witness that the orientation is the complex one.

## Main definitions

* `TauCeti.AlmostComplexStructure.hermitianForm J F`: the symmetric bilinear form
  `B(v, w) = (F(v, J w) + F(w, J v)) / 2`, linear in `F`.

## Main results

In the namespace `TauCeti.AlmostComplexStructure`:

* `hermitianForm_apply_self`: `B(v, v) = F(v, J v)`; `isSymm_hermitianForm`: `B` is symmetric.
* `hermitianForm_kahlerForm`: the Hermitian form of `ω` is the inner product.
* `hermitianForm_apply_self_eq`: `B(v, v) = c ‖v‖² + ⟪F⁻, v ∧ J v⟫`.
* `hermitianForm_eq_zero_of_hodgeStar_eq_self`: self-dual forms orthogonal to `ω` have zero
  Hermitian form.
* `abs_inner_ιMulti_apply_le` and `exists_inner_ιMulti_apply_eq_neg`: for anti-self-dual `η`,
  `|⟪η, v ∧ J v⟫| ≤ ‖η‖ ‖v‖² / √2`, with equality `⟪η, v ∧ J v⟫ = -‖η‖ / √2` for some unit `v`.
* `isLeast_hermitianForm_apply_self`, `isGreatest_hermitianForm_apply_self`: on the unit sphere
  the minimum of `B(v, v)` is `c - ‖F⁻‖ / √2` and the maximum is `c + ‖F⁻‖ / √2`.
* `norm_le_of_forall_le_hermitianForm_apply_self`: `B ≥ m g` implies `‖F⁻‖ ≤ √2 (c - m)`.

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

namespace TauCeti.AlmostComplexStructure

/-- The **Hermitian form** of a two-vector `F` with respect to an almost complex structure `J`:
the symmetric bilinear form `B(v, w) = (F(v, J w) + F(w, J v)) / 2`, where `F(v, w) = ⟪F, v ∧ w⟫`
is the two-form represented by `F` (`hermitianForm_apply`). Its quadratic form is
`B(v, v) = F(v, J v)`. It depends linearly on `F`. -/
def hermitianForm (J : AlmostComplexStructure V) :
    ⋀[ℝ]^2 V →ₗ[ℝ] LinearMap.BilinForm ℝ V where
  toFun F := LinearMap.mk₂ ℝ
    (fun v w ↦ (⟪twoVectorContraction F v, J w⟫ + ⟪twoVectorContraction F w, J v⟫) / 2)
    (fun _ _ _ ↦ by simp only [map_add, inner_add_left, inner_add_right]; ring)
    (fun _ _ _ ↦ by simp only [map_smul, J.apply_smul, real_inner_smul_left,
      real_inner_smul_right]; ring)
    (fun _ _ _ ↦ by simp only [map_add, inner_add_left, inner_add_right]; ring)
    (fun _ _ _ ↦ by simp only [map_smul, J.apply_smul, real_inner_smul_left,
      real_inner_smul_right]; ring)
  map_add' F G := by
    ext v w
    simp only [LinearMap.mk₂_apply, LinearMap.add_apply, twoVectorContraction_add,
      inner_add_left]
    ring
  map_smul' c F := by
    ext v w
    simp only [LinearMap.mk₂_apply, LinearMap.smul_apply, twoVectorContraction_smul,
      real_inner_smul_left, RingHom.id_apply, smul_eq_mul]
    ring

/-- The Hermitian form in terms of the two-form: `B(v, w) = (F(v, J w) + F(w, J v)) / 2`. -/
theorem hermitianForm_apply (J : AlmostComplexStructure V) (F : ⋀[ℝ]^2 V) (v w : V) :
    J.hermitianForm F v w =
      (⟪F, ιMulti ℝ 2 ![v, J w]⟫ + ⟪F, ιMulti ℝ 2 ![w, J v]⟫) / 2 := by
  simp [hermitianForm]

/-- The quadratic form of the Hermitian form: `B(v, v) = F(v, J v)`. -/
@[simp]
theorem hermitianForm_apply_self (J : AlmostComplexStructure V) (F : ⋀[ℝ]^2 V) (v : V) :
    J.hermitianForm F v v = ⟪F, ιMulti ℝ 2 ![v, J v]⟫ := by
  rw [hermitianForm_apply]
  ring

/-- The Hermitian form is symmetric. -/
theorem isSymm_hermitianForm (J : AlmostComplexStructure V) (F : ⋀[ℝ]^2 V) :
    (J.hermitianForm F).IsSymm :=
  ⟨fun v w ↦ by rw [hermitianForm_apply, hermitianForm_apply, add_comm]⟩

/-- **The Hermitian form of the Kähler form is the metric**: for orthogonal `J`,
`B_ω(v, w) = ⟪v, w⟫`. -/
theorem hermitianForm_kahlerForm {J : AlmostComplexStructure V}
    (hJ : ∀ v w, ⟪J v, J w⟫ = ⟪v, w⟫) : J.hermitianForm J.kahlerForm = innerₗ V := by
  ext v w
  rw [hermitianForm_apply, inner_kahlerForm_ιMulti hJ, inner_kahlerForm_ιMulti hJ, hJ, hJ,
    innerₗ_apply_apply, real_inner_comm v w]
  ring

/-! ### Anti-self-dual two-forms in dimension four -/

section AntiSelfDual

variable [Fact (finrank ℝ V = 4)] {o : Orientation ℝ V (Fin 4)} (hkl : 2 + 2 = finrank ℝ V)
  {J : AlmostComplexStructure V} {η : ⋀[ℝ]^2 V}

include hkl in
/-- For a self-dual or anti-self-dual `η` in dimension four and orthogonal `J`,
`|⟪η, v ∧ J v⟫| ≤ (‖η‖ / √2) ‖v‖²`. -/
theorem abs_inner_ιMulti_apply_le (hJ : ∀ v w, ⟪J v, J w⟫ = ⟪v, w⟫)
    (hη : o.hodgeStar hkl η = η ∨ o.hodgeStar hkl η = -η) (v : V) :
    |⟪η, ιMulti ℝ 2 ![v, J v]⟫| ≤ ‖η‖ / √2 * ‖v‖ ^ 2 := by
  -- The contraction by `η` is `‖η‖ / √2` times an isometry, and `J` is an isometry.
  have hA : ‖twoVectorContraction η v‖ = ‖η‖ / √2 * ‖v‖ := by
    rw [← pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero,
      norm_twoVectorContraction_apply_sq o hkl hη, mul_pow, div_pow,
      Real.sq_sqrt zero_le_two]
  rw [← inner_twoVectorContraction_apply]
  calc |⟪twoVectorContraction η v, J v⟫|
      ≤ ‖twoVectorContraction η v‖ * ‖J v‖ := abs_real_inner_le_norm _ _
    _ = ‖η‖ / √2 * ‖v‖ ^ 2 := by rw [hA, norm_apply hJ]; ring

variable {e : OrthonormalBasis (Fin 4) ℝ V} (h₀ : J (e 0) = e 1) (h₂ : J (e 2) = e 3)
  (he : e.toBasis.orientation = o)

include h₀ h₂ he in
/-- **The bound on `⟪η, v ∧ J v⟫` is attained**: for the complex orientation and anti-self-dual
`η`, some unit vector `v` has `⟪η, v ∧ J v⟫ = -‖η‖ / √2`. Indeed `J A`, with `A = (· ⌟ η)`, is a
symmetric operator squaring to `‖η‖² / 2`, and `v` is an eigenvector of `J A` for the eigenvalue
`‖η‖ / √2`. -/
theorem exists_inner_ιMulti_apply_eq_neg (hη : o.hodgeStar hkl η = -η) :
    ∃ v : V, ‖v‖ = 1 ∧ ⟪η, ιMulti ℝ 2 ![v, J v]⟫ = -(‖η‖ / √2) := by
  have hJ := inner_apply_apply_of_orthonormalBasis h₀ h₂
  rcases eq_or_ne η 0 with rfl | hη₀
  · exact ⟨e 0, e.orthonormal.1 0, by simp⟩
  set A := twoVectorContraction η
  set l := ‖η‖ / √2 with hl
  have hl₀ : 0 < l := by positivity
  have hAJ (u : V) : A (J u) = J (A u) :=
    twoVectorContraction_apply_apply_of_hodgeStar_eq_neg h₀ h₂ hkl he hη u
  have hAA (u : V) : A (A u) = -(l ^ 2) • u := by
    have h := LinearMap.congr_fun (twoVectorContraction_comp_self o hkl (Or.inr hη)) u
    rw [hl, div_pow, Real.sq_sqrt zero_le_two]
    simpa using h
  -- `J A` is not `-l`: otherwise `A = l J`, so `η = l ω` would be self-dual.
  obtain ⟨w, hw⟩ : ∃ w : V, J (A w) + l • w ≠ 0 := by
    by_contra! h
    have hA (u : V) : A u = l • J u := by
      have := congrArg J (h u)
      rwa [J.apply_add, J.apply_apply, J.apply_smul, J.apply_zero, neg_add_eq_zero] at this
    have hηω : η = l • J.kahlerForm := by
      refine ext_inner_ιMulti_two fun u w ↦ ?_
      rw [← inner_twoVectorContraction_apply, hA, real_inner_smul_left, real_inner_smul_left,
        inner_kahlerForm_ιMulti hJ]
    have hω := hodgeStar_kahlerForm h₀ h₂ hkl he
    have : (2 * l) • J.kahlerForm = 0 := by
      rw [hηω, map_smul, hω] at hη
      linear_combination (norm := module) hη
    have hω₀ : J.kahlerForm ≠ 0 := by
      intro h0
      have := norm_kahlerForm_sq hJ
      rw [h0, norm_zero, (Fact.out : finrank ℝ V = 4)] at this
      norm_num at this
    exact absurd ((smul_eq_zero.1 this).resolve_right hω₀) (by positivity)
  -- `v₀ = J A w + l w` is an eigenvector of `J A` for the eigenvalue `l`.
  set v₀ := J (A w) + l • w with hv₀
  have hJA : J (A v₀) = l • v₀ := by
    rw [hv₀, map_add, map_smul, hAJ, hAA, J.apply_add, J.apply_apply, J.apply_smul]
    module
  have hAv₀ : ⟪A v₀, J v₀⟫ = -⟪J (A v₀), v₀⟫ := by
    rw [inner_apply_left hJ, real_inner_comm, neg_neg]
  have hq (c : ℝ) : ⟪η, ιMulti ℝ 2 ![c • v₀, J (c • v₀)]⟫ = -(l * (c ^ 2 * ‖v₀‖ ^ 2)) := by
    rw [← inner_twoVectorContraction_apply, J.apply_smul, map_smul, real_inner_smul_left,
      real_inner_smul_right, hAv₀, hJA, real_inner_smul_left, real_inner_self_eq_norm_sq]
    ring
  have hv₀n : ‖v₀‖ ≠ 0 := norm_ne_zero_iff.2 hw
  refine ⟨‖v₀‖⁻¹ • v₀, ?_, ?_⟩
  · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hv₀n]
  · rw [hq, inv_pow, inv_mul_cancel₀ (pow_ne_zero 2 hv₀n), mul_one]

/-! ### The Hermitian form of a general two-form -/

include h₀ h₂ he in
/-- **The Hermitian form splits along `Λ⁺ ⊕ Λ⁻`**: for the complex orientation,
`B(v, v) = c ‖v‖² + ⟪F⁻, v ∧ J v⟫` with `c = ⟪F, ω⟫ / 2` and `F⁻ = (F - ⋆F) / 2`. -/
theorem hermitianForm_apply_self_eq (F : ⋀[ℝ]^2 V) (v : V) :
    J.hermitianForm F v v = ⟪F, J.kahlerForm⟫ / 2 * ‖v‖ ^ 2 +
      ⟪(2⁻¹ : ℝ) • (F - o.hodgeStar hkl F), ιMulti ℝ 2 ![v, J v]⟫ := by
  have h := congrArg (⟪F, ·⟫) (ιMulti_apply_add_hodgeStar h₀ h₂ hkl he v)
  have hsymm := o.isSymmetric_hodgeStar_of_even even_two hkl F (ιMulti ℝ 2 ![v, J v])
  simp only [LinearEquiv.coe_coe] at hsymm
  simp only [inner_add_right, real_inner_smul_right] at h
  rw [hermitianForm_apply_self, real_inner_smul_left, inner_sub_left, hsymm]
  linarith

include h₀ h₂ he in
/-- **Anti-`J`-invariant self-dual forms do not contribute to the Hermitian form**: for the
complex orientation, a self-dual `η` orthogonal to `ω` has `B_η = 0`. -/
theorem hermitianForm_eq_zero_of_hodgeStar_eq_self (hη : o.hodgeStar hkl η = η)
    (hηω : ⟪η, J.kahlerForm⟫ = 0) : J.hermitianForm η = 0 := by
  refine LinearMap.BilinForm.ext_of_isSymm (isSymm_hermitianForm J η)
    LinearMap.BilinForm.isSymm_zero fun v ↦ ?_
  rw [hermitianForm_apply_self_eq hkl h₀ h₂ he, hη, hηω, sub_self, smul_zero, inner_zero_left]
  simp

include h₀ h₂ he in
/-- **Lower bound for the Hermitian form**: for the complex orientation,
`B(v, v) ≥ (c - ‖F⁻‖ / √2) ‖v‖²` with `c = ⟪F, ω⟫ / 2` and `F⁻ = (F - ⋆F) / 2`. -/
theorem le_hermitianForm_apply_self (F : ⋀[ℝ]^2 V) (v : V) :
    (⟪F, J.kahlerForm⟫ / 2 - ‖(2⁻¹ : ℝ) • (F - o.hodgeStar hkl F)‖ / √2) * ‖v‖ ^ 2 ≤
      J.hermitianForm F v v := by
  have h := abs_inner_ιMulti_apply_le hkl (inner_apply_apply_of_orthonormalBasis h₀ h₂)
    (Or.inr (o.hodgeStar_smul_sub_hodgeStar_of_even even_two hkl 2⁻¹ F)) v
  rw [hermitianForm_apply_self_eq hkl h₀ h₂ he]
  linarith [neg_abs_le ⟪(2⁻¹ : ℝ) • (F - o.hodgeStar hkl F), ιMulti ℝ 2 ![v, J v]⟫]

include h₀ h₂ he in
/-- **Upper bound for the Hermitian form**: for the complex orientation,
`B(v, v) ≤ (c + ‖F⁻‖ / √2) ‖v‖²` with `c = ⟪F, ω⟫ / 2` and `F⁻ = (F - ⋆F) / 2`. -/
theorem hermitianForm_apply_self_le (F : ⋀[ℝ]^2 V) (v : V) :
    J.hermitianForm F v v ≤
      (⟪F, J.kahlerForm⟫ / 2 + ‖(2⁻¹ : ℝ) • (F - o.hodgeStar hkl F)‖ / √2) * ‖v‖ ^ 2 := by
  have h := abs_inner_ιMulti_apply_le hkl (inner_apply_apply_of_orthonormalBasis h₀ h₂)
    (Or.inr (o.hodgeStar_smul_sub_hodgeStar_of_even even_two hkl 2⁻¹ F)) v
  rw [hermitianForm_apply_self_eq hkl h₀ h₂ he]
  linarith [le_abs_self ⟪(2⁻¹ : ℝ) • (F - o.hodgeStar hkl F), ιMulti ℝ 2 ![v, J v]⟫]

include h₀ h₂ he in
/-- **The smallest eigenvalue of the Hermitian form**: for the complex orientation, the minimum
of `B(v, v)` over unit vectors is `λ_min(B) = c - ‖F⁻‖ / √2`, where `c = ⟪F, ω⟫ / 2` and
`F⁻ = (F - ⋆F) / 2`. -/
theorem isLeast_hermitianForm_apply_self (F : ⋀[ℝ]^2 V) :
    IsLeast ((fun v ↦ J.hermitianForm F v v) '' Metric.sphere 0 1)
      (⟪F, J.kahlerForm⟫ / 2 - ‖(2⁻¹ : ℝ) • (F - o.hodgeStar hkl F)‖ / √2) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨v, hv, hq⟩ := exists_inner_ιMulti_apply_eq_neg hkl h₀ h₂ he
      (o.hodgeStar_smul_sub_hodgeStar_of_even even_two hkl 2⁻¹ F)
    refine ⟨v, mem_sphere_zero_iff_norm.2 hv, ?_⟩
    simp only
    rw [hermitianForm_apply_self_eq hkl h₀ h₂ he, hv, hq]
    ring
  · rintro _ ⟨v, hv, rfl⟩
    simpa [mem_sphere_zero_iff_norm.1 hv] using le_hermitianForm_apply_self hkl h₀ h₂ he F v

include h₀ h₂ he in
/-- **The largest eigenvalue of the Hermitian form**: for the complex orientation, the maximum
of `B(v, v)` over unit vectors is `λ_max(B) = c + ‖F⁻‖ / √2`, where `c = ⟪F, ω⟫ / 2` and
`F⁻ = (F - ⋆F) / 2`. -/
theorem isGreatest_hermitianForm_apply_self (F : ⋀[ℝ]^2 V) :
    IsGreatest ((fun v ↦ J.hermitianForm F v v) '' Metric.sphere 0 1)
      (⟪F, J.kahlerForm⟫ / 2 + ‖(2⁻¹ : ℝ) • (F - o.hodgeStar hkl F)‖ / √2) := by
  refine ⟨?_, ?_⟩
  · have hneg : o.hodgeStar hkl (-((2⁻¹ : ℝ) • (F - o.hodgeStar hkl F))) =
        -(-((2⁻¹ : ℝ) • (F - o.hodgeStar hkl F))) := by
      rw [map_neg, o.hodgeStar_smul_sub_hodgeStar_of_even even_two hkl 2⁻¹ F]
    obtain ⟨v, hv, hq⟩ := exists_inner_ιMulti_apply_eq_neg hkl h₀ h₂ he hneg
    rw [inner_neg_left, norm_neg, neg_inj] at hq
    refine ⟨v, mem_sphere_zero_iff_norm.2 hv, ?_⟩
    simp only
    rw [hermitianForm_apply_self_eq hkl h₀ h₂ he, hv, hq]
    ring
  · rintro _ ⟨v, hv, rfl⟩
    simpa [mem_sphere_zero_iff_norm.1 hv] using hermitianForm_apply_self_le hkl h₀ h₂ he F v

include h₀ h₂ he in
/-- **A lower bound on the Hermitian form controls the anti-self-dual part**: for the complex
orientation, if `B(v, v) ≥ m ‖v‖²` for all `v`, then `‖F⁻‖ ≤ √2 (c - m)`, where
`c = ⟪F, ω⟫ / 2` and `F⁻ = (F - ⋆F) / 2`. -/
theorem norm_le_of_forall_le_hermitianForm_apply_self {F : ⋀[ℝ]^2 V} {m : ℝ}
    (hm : ∀ v, m * ‖v‖ ^ 2 ≤ J.hermitianForm F v v) :
    ‖(2⁻¹ : ℝ) • (F - o.hodgeStar hkl F)‖ ≤ √2 * (⟪F, J.kahlerForm⟫ / 2 - m) := by
  obtain ⟨⟨v, hv, hq⟩, -⟩ := isLeast_hermitianForm_apply_self hkl h₀ h₂ he F
  have h := hm v
  simp only at hq
  rw [mem_sphere_zero_iff_norm.1 hv, one_pow, mul_one, hq] at h
  have hs : (0 : ℝ) < √2 := by positivity
  rw [← div_le_iff₀' hs]
  linarith

end AntiSelfDual

end TauCeti.AlmostComplexStructure

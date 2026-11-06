/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.HodgeStar.ComplexStructure

/-!
# The Hermitian part of a two-form and its least eigenvalue

Let `J` be an almost complex structure on a finite-dimensional real inner product space `V`, and
let `F ∈ ⋀² V` represent the two-form `F(u, w) = ⟪F, u ∧ w⟫`. The **`J`-Hermitian part** of `F`
is the symmetric bilinear form

`B(v, w) = (F(v, J w) + F(w, J v)) / 2`

(`TauCeti.AlmostComplexStructure.hermitianForm`), so that `B(v, v) = F(v, J v)`. It is
`J`-invariant, linear in `F`, equal to the metric for the Kähler two-vector `ω` of an orthogonal
`J`, and zero on the image of the derivation action `D_J` of `J` on two-forms, that is on the
anti-`J`-invariant forms.

In dimension four, for the complex orientation, the two-forms split as
`ℝ ω ⊕ (ℝ ω)ᗮ ∩ Λ⁺ ⊕ Λ⁻`. The middle summand consists of anti-`J`-invariant forms and contributes
nothing to `B`, while the anti-self-dual forms are `J`-invariant, so their contraction operators
commute with `J`. Writing `F⁻ = (F - ⋆F) / 2` and `c = ⟪ω, F⟫ / 2`, this gives

`B = c g + B(F⁻)` (`TauCeti.AlmostComplexStructure.hermitianForm_eq_add`),

and the eigenvalues of `B(F⁻)` are `± ‖F⁻‖ / √2`. Hence the least eigenvalue of `B`, the
minimum of `B(v, v)` over unit vectors, is

`λ_min(B) = ⟪ω, F⟫ / 2 - ‖F⁻‖ / √2`

(`TauCeti.AlmostComplexStructure.isLeast_hermitianForm_apply_self`). Consequently a lower bound
`B ≥ -C g` bounds the anti-self-dual part by the `ω`-component,
`‖F⁻‖ / √2 ≤ ⟪ω, F⟫ / 2 + C`. Applied to the real curvature form `F = i F_a` of a connection on
a symplectic four-manifold, with `|ω| = √2`, this is the pointwise algebra by which a lower bound
on the Hermitian curvature controls the anti-self-dual curvature `F_a⁻` in Taubes's analysis of
the Seiberg–Witten equations for large perturbation parameter.

## Main results

In the namespace `TauCeti.AlmostComplexStructure`:

* `hermitianForm_apply_self`: `B(v, v) = F(v, J v)`.
* `hermitianForm_apply_apply`: `B(J v, J w) = B(v, w)`.
* `hermitianForm_kahlerForm`: `B(ω) = g`.
* `hermitianForm_lieMap`: `B(D_J F) = 0`.
* `twoVectorContraction_apply_of_lieMap_eq_zero`: the contraction by a `J`-invariant two-form
  commutes with `J`.
* `hermitianForm_eq_zero_of_hodgeStar_eq_self`: in dimension four, a self-dual form orthogonal to
  `ω` has zero Hermitian part.
* `abs_hermitianForm_apply_self_le`: `|B(v, v)| ≤ ‖F‖ / √2 · ‖v‖²` when `⋆F = ±F`.
* `exists_hermitianForm_apply_self_eq_neg`: for anti-self-dual `F` the value `-‖F‖ / √2` is
  attained on a unit vector.
* `hermitianForm_eq_add`: `B(F) = (⟪ω, F⟫ / 2) g + B(F⁻)`.
* `isLeast_hermitianForm_apply_self`: the least eigenvalue of `B` is `⟪ω, F⟫ / 2 - ‖F⁻‖ / √2`.
* `norm_smul_sub_hodgeStar_div_sqrt_two_le`: `B ≥ -C g` implies
  `‖F⁻‖ / √2 ≤ ⟪ω, F⟫ / 2 + C`.

## References

* C. H. Taubes, *SW ⇒ Gr: From the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
* S. K. Donaldson and P. B. Kronheimer, *The Geometry of Four-Manifolds*, Oxford (1990),
  Section 1.1.
-/

public section

noncomputable section

open Module exteriorPower
open scoped RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

namespace TauCeti.AlmostComplexStructure

/-- The **`J`-Hermitian part** of the two-form `F(u, w) = ⟪F, u ∧ w⟫` represented by a
two-vector `F`: the symmetric bilinear form `B(v, w) = (F(v, J w) + F(w, J v)) / 2`
(`hermitianForm_apply`). It is linear in `F` and `J`-invariant. For an orthogonal `J` it is the
metric for the Kähler two-vector, and it vanishes on anti-`J`-invariant forms. -/
def hermitianForm (J : AlmostComplexStructure V) : ⋀[ℝ]^2 V →ₗ[ℝ] LinearMap.BilinForm ℝ V where
  toFun F := (2⁻¹ : ℝ) • ((innerₗ V).compl₁₂ (twoVectorContraction F) J.toLinearMap +
    ((innerₗ V).compl₁₂ (twoVectorContraction F) J.toLinearMap).flip)
  map_add' F G := by
    ext v w
    simp
    ring
  map_smul' c F := by
    ext v w
    simp
    ring

variable (J : AlmostComplexStructure V) (F : ⋀[ℝ]^2 V)

/-- The Hermitian part in terms of the contraction `A u = u ⌟ F`:
`B(v, w) = (⟪A v, J w⟫ + ⟪A w, J v⟫) / 2`. -/
private theorem hermitianForm_apply_eq_inner (v w : V) :
    J.hermitianForm F v w =
      (⟪twoVectorContraction F v, J w⟫ + ⟪twoVectorContraction F w, J v⟫) / 2 := by
  simp only [hermitianForm, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.flip_apply, LinearMap.compl₁₂_apply, innerₗ_apply_apply,
    smul_eq_mul]
  ring

/-- **The Hermitian part of a two-form**: `B(v, w) = (F(v, J w) + F(w, J v)) / 2`. -/
@[simp]
theorem hermitianForm_apply (v w : V) :
    J.hermitianForm F v w = (⟪F, ιMulti ℝ 2 ![v, J w]⟫ + ⟪F, ιMulti ℝ 2 ![w, J v]⟫) / 2 := by
  rw [hermitianForm_apply_eq_inner, inner_twoVectorContraction_apply,
    inner_twoVectorContraction_apply]

/-- On the diagonal the Hermitian part is `B(v, v) = F(v, J v)`. -/
theorem hermitianForm_apply_self (v : V) :
    J.hermitianForm F v v = ⟪F, ιMulti ℝ 2 ![v, J v]⟫ := by
  rw [hermitianForm_apply]
  ring

/-- The Hermitian part is a symmetric bilinear form. -/
theorem isSymm_hermitianForm : (J.hermitianForm F).IsSymm :=
  LinearMap.BilinForm.isSymm_def.2 fun v w ↦ by
    rw [hermitianForm_apply, hermitianForm_apply, add_comm]

/-- **The Hermitian part is `J`-invariant**: `B(J v, J w) = B(v, w)`. -/
theorem hermitianForm_apply_apply (v w : V) :
    J.hermitianForm F (J v) (J w) = J.hermitianForm F v w := by
  rw [hermitianForm_apply_eq_inner, hermitianForm_apply_eq_inner, J.apply_apply, J.apply_apply,
    inner_neg_right, inner_neg_right, inner_twoVectorContraction_apply_left F (J v) w,
    inner_twoVectorContraction_apply_left F (J w) v, real_inner_comm (J v),
    real_inner_comm (J w)]
  ring

section Orthogonal

variable {J} (hJ : ∀ v w, ⟪J v, J w⟫ = ⟪v, w⟫)
include hJ

/-- **The Hermitian part of the Kähler two-vector is the metric**: `B(ω) = g`, since
`ω(v, J w) = ⟪J v, J w⟫ = ⟪v, w⟫`. -/
theorem hermitianForm_kahlerForm : J.hermitianForm J.kahlerForm = innerₗ V := by
  ext v w
  rw [hermitianForm_apply, inner_kahlerForm_ιMulti hJ, inner_kahlerForm_ιMulti hJ, hJ, hJ,
    innerₗ_apply_apply, real_inner_comm w v]
  ring

/-- **Anti-`J`-invariant forms have zero Hermitian part**: `B(D_J F) = 0`, where
`D_J (u ∧ w) = J u ∧ w + u ∧ J w` is the derivation action of `J` on two-forms. -/
theorem hermitianForm_lieMap :
    J.hermitianForm (exteriorPower.lieMap 2 J.toLinearMap F) = 0 := by
  ext v w
  -- Move `D_J` to the right, where it acts on the wedges `v ∧ J w` and `w ∧ J v`.
  rw [hermitianForm_apply, inner_lieMap_left (inner_apply_left hJ),
    inner_lieMap_left (inner_apply_left hJ), lieMap_two_apply_ιMulti, lieMap_two_apply_ιMulti]
  simp only [AlmostComplexStructure.apply_apply, inner_add_right, inner_neg_right,
    ← inner_twoVectorContraction_apply, LinearMap.zero_apply]
  rw [inner_twoVectorContraction_apply_left F (J w), inner_twoVectorContraction_apply_left F w,
    real_inner_comm (J w), real_inner_comm w]
  ring

/-- **The contraction by a `J`-invariant two-form commutes with `J`**: if `D_J F = 0` then
`(J v) ⌟ F = J (v ⌟ F)`. -/
theorem twoVectorContraction_apply_of_lieMap_eq_zero
    (hF : exteriorPower.lieMap 2 J.toLinearMap F = 0) (v : V) :
    twoVectorContraction F (J v) = J (twoVectorContraction F v) := by
  refine ext_inner_right ℝ fun w ↦ ?_
  have h := inner_lieMap_left (inner_apply_left hJ) F (ιMulti ℝ 2 ![v, w])
  rw [hF, inner_zero_left, lieMap_two_apply_ιMulti, inner_add_right,
    ← inner_twoVectorContraction_apply, ← inner_twoVectorContraction_apply] at h
  rw [inner_apply_left hJ]
  linarith

/-- For a `J`-invariant two-form, `B(v, w) = -⟪J (v ⌟ F), w⟫`. -/
private theorem hermitianForm_apply_of_lieMap_eq_zero
    (hF : exteriorPower.lieMap 2 J.toLinearMap F = 0) (v w : V) :
    J.hermitianForm F v w = -⟪J (twoVectorContraction F v), w⟫ := by
  have h := inner_apply_left hJ (twoVectorContraction F v) w
  rw [hermitianForm_apply_eq_inner, inner_twoVectorContraction_apply_left F w,
    twoVectorContraction_apply_of_lieMap_eq_zero F hJ hF]
  linarith [real_inner_comm w (J (twoVectorContraction F v))]

end Orthogonal

/-! ### Dimension four -/

section Four

variable {J} {F} [Fact (finrank ℝ V = 4)] {o : Orientation ℝ V (Fin 4)}
  (hkl : 2 + 2 = finrank ℝ V)

/-- **The Hermitian part of a self-dual or anti-self-dual form is bounded by its norm**: in
dimension four, for an orthogonal `J` and `⋆F = ±F`, `|B(v, v)| ≤ ‖F‖ / √2 · ‖v‖²`. -/
theorem abs_hermitianForm_apply_self_le (hJ : ∀ v w, ⟪J v, J w⟫ = ⟪v, w⟫)
    (hF : o.hodgeStar hkl F = F ∨ o.hodgeStar hkl F = -F) (v : V) :
    |J.hermitianForm F v v| ≤ ‖F‖ / √2 * ‖v‖ ^ 2 := by
  have hA : ‖twoVectorContraction F v‖ = ‖F‖ / √2 * ‖v‖ := by
    refine (sq_eq_sq₀ (norm_nonneg _) (by positivity)).1 ?_
    rw [norm_twoVectorContraction_apply_sq o hkl hF, mul_pow, div_pow,
      Real.sq_sqrt zero_le_two]
  rw [hermitianForm_apply_self, ← inner_twoVectorContraction_apply]
  calc |⟪twoVectorContraction F v, J v⟫|
      ≤ ‖twoVectorContraction F v‖ * ‖J v‖ := abs_real_inner_le_norm _ _
    _ = ‖F‖ / √2 * ‖v‖ ^ 2 := by rw [hA, norm_apply hJ]; ring

variable {e : OrthonormalBasis (Fin 4) ℝ V} (h₀ : J (e 0) = e 1) (h₂ : J (e 2) = e 3)
  (he : e.toBasis.orientation = o)

include he h₀ h₂

/-- **Self-dual forms orthogonal to `ω` have zero Hermitian part**: for the complex orientation,
if `⋆η = η` and `⟪ω, η⟫ = 0` then `B(η) = 0`. Such an `η` is anti-`J`-invariant,
`η = D_J (-D_J η / 4)`. -/
theorem hermitianForm_eq_zero_of_hodgeStar_eq_self {η : ⋀[ℝ]^2 V}
    (hη : o.hodgeStar hkl η = η) (hω : ⟪J.kahlerForm, η⟫ = 0) : J.hermitianForm η = 0 := by
  have hJ := inner_apply_apply_of_orthonormalBasis h₀ h₂
  have h := lieMap_lieMap_of_hodgeStar_eq_self h₀ h₂ hkl he hη
  rw [hω, mul_zero, zero_smul, zero_sub] at h
  have hη' : η = exteriorPower.lieMap 2 J.toLinearMap
      ((-4⁻¹ : ℝ) • exteriorPower.lieMap 2 J.toLinearMap η) := by
    rw [map_smul, h, smul_neg, smul_smul]
    norm_num
  rw [hη']
  exact hermitianForm_lieMap _ hJ

/-- **The least eigenvalue of the Hermitian part of an anti-self-dual form**: for the complex
orientation and `⋆F = -F`, there is a unit vector `v` with `B(v, v) = -‖F‖ / √2`. The eigenvalues
of `B` are `± ‖F‖ / √2`, each of multiplicity two. -/
theorem exists_hermitianForm_apply_self_eq_neg (hF : o.hodgeStar hkl F = -F) :
    ∃ v, ‖v‖ = 1 ∧ J.hermitianForm F v v = -(‖F‖ / √2) := by
  have hJ := inner_apply_apply_of_orthonormalBasis h₀ h₂
  have hD := lieMap_eq_zero_of_hodgeStar_eq_neg h₀ h₂ hkl he hF
  set A := twoVectorContraction F
  set l := ‖F‖ / √2 with hl
  -- `T = J ∘ A` is the symmetric operator of `-B`, and `T² = l²`.
  have hl2 : l ^ 2 = ‖F‖ ^ 2 / 2 := by rw [hl, div_pow, Real.sq_sqrt zero_le_two]
  have hTT (w : V) : J (A (J (A w))) = l ^ 2 • w := by
    have h := LinearMap.congr_fun (twoVectorContraction_comp_self o hkl (Or.inr hF)) w
    rw [LinearMap.comp_apply] at h
    rw [twoVectorContraction_apply_of_lieMap_eq_zero F hJ hD, J.apply_apply, h, hl2]
    simp
  -- On an eigenvector `J (A u) = μ u` the Hermitian part is `-μ ‖u‖²`.
  have hB (u : V) (μ : ℝ) (hu : J (A u) = μ • u) : J.hermitianForm F u u = -μ * ‖u‖ ^ 2 := by
    rw [hermitianForm_apply_of_lieMap_eq_zero F hJ hD, hu, real_inner_smul_left,
      real_inner_self_eq_norm_sq]
    ring
  -- For any `w`, `u = J (A w) + l w` satisfies `J (A u) = l u`.
  have hu (w : V) : J (A (J (A w) + l • w)) = l • (J (A w) + l • w) := by
    rw [map_add, map_smul, J.apply_add, hTT, map_smul, smul_add, smul_smul, ← sq, add_comm]
  -- Normalize an eigenvector for the eigenvalue `l` of `J A`.
  have hnorm (u : V) (hu0 : u ≠ 0) (hJu : J (A u) = l • u) :
      ∃ v, ‖v‖ = 1 ∧ J.hermitianForm F v v = -l := by
    have hu' : ‖u‖ ≠ 0 := norm_ne_zero_iff.2 hu0
    refine ⟨‖u‖⁻¹ • u, by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hu'], ?_⟩
    rw [LinearMap.map_smul₂, LinearMap.map_smul, hB u l hJu, smul_eq_mul, smul_eq_mul]
    field_simp
  by_cases h0 : J (A (e 0)) + l • e 0 = 0
  · by_cases h2 : J (A (e 2)) + l • e 2 = 0
    · -- Then `B(e₀, e₀) = B(e₂, e₂) = l`, while their sum is `⟪F, ω⟫ = 0`, so `l = 0`.
      have hB0 := hB (e 0) (-l) (by rw [neg_smul]; exact eq_neg_of_add_eq_zero_left h0)
      have hB2 := hB (e 2) (-l) (by rw [neg_smul]; exact eq_neg_of_add_eq_zero_left h2)
      have hω : ⟪F, J.kahlerForm⟫ = 0 := by
        have h := o.inner_hodgeStar_hodgeStar hkl F J.kahlerForm
        rw [hodgeStar_kahlerForm h₀ h₂ hkl he, hF, inner_neg_left] at h
        linarith
      rw [kahlerForm_eq_ιMulti_add_ιMulti h₀ h₂, inner_add_right, ← h₀, ← h₂,
        ← hermitianForm_apply_self, ← hermitianForm_apply_self, hB0, hB2, e.orthonormal.1 0,
        e.orthonormal.1 2] at hω
      have hl0 : l = 0 := by linarith
      refine ⟨e 0, e.orthonormal.1 0, ?_⟩
      rw [hB0, e.orthonormal.1 0, hl0]
      ring
    · exact hnorm _ h2 (hu (e 2))
  · exact hnorm _ h0 (hu (e 0))

/-- **The Hermitian part splits off the `ω`-component**: for the complex orientation,
`B(F) = (⟪ω, F⟫ / 2) g + B(F⁻)` with `F⁻ = (F - ⋆F) / 2` the anti-self-dual part of `F`. The
self-dual part orthogonal to `ω` contributes nothing. -/
theorem hermitianForm_eq_add (F : ⋀[ℝ]^2 V) :
    J.hermitianForm F = (⟪J.kahlerForm, F⟫ / 2) • innerₗ V +
      J.hermitianForm ((2⁻¹ : ℝ) • (F - o.hodgeStar hkl F)) := by
  have hJ := inner_apply_apply_of_orthonormalBasis h₀ h₂
  have hω := hodgeStar_kahlerForm h₀ h₂ hkl he
  set c := ⟪J.kahlerForm, F⟫ / 2
  set η := (2⁻¹ : ℝ) • (F + o.hodgeStar hkl F) - c • J.kahlerForm
  have hηself : o.hodgeStar hkl η = η := by
    simp only [η, map_sub, map_smul, map_add, o.hodgeStar_hodgeStar_of_even even_two hkl, hω,
      add_comm (o.hodgeStar hkl F)]
  have hηω : ⟪J.kahlerForm, η⟫ = 0 := by
    have hsymm := o.inner_hodgeStar_hodgeStar hkl J.kahlerForm F
    rw [hω] at hsymm
    have hωω : ⟪J.kahlerForm, J.kahlerForm⟫ = 2 := by
      rw [inner_kahlerForm_self hJ, (Fact.out : finrank ℝ V = 4)]
      norm_num
    simp only [η, inner_sub_right, inner_smul_right, inner_add_right, hsymm, hωω, c]
    ring
  have hF : F = c • J.kahlerForm + η + (2⁻¹ : ℝ) • (F - o.hodgeStar hkl F) := by
    simp only [η]
    module
  conv_lhs => rw [hF]
  rw [map_add, map_add, map_smul, hermitianForm_kahlerForm hJ,
    hermitianForm_eq_zero_of_hodgeStar_eq_self hkl h₀ h₂ he hηself hηω, add_zero]

/-- **The least eigenvalue of the Hermitian part of a two-form**: for the complex orientation,
the minimum of `B(v, v)` over unit vectors `v` is `⟪ω, F⟫ / 2 - ‖F⁻‖ / √2`, where
`F⁻ = (F - ⋆F) / 2` is the anti-self-dual part of `F`. -/
theorem isLeast_hermitianForm_apply_self (F : ⋀[ℝ]^2 V) :
    IsLeast ((fun v ↦ J.hermitianForm F v v) '' Metric.sphere 0 1)
      (⟪J.kahlerForm, F⟫ / 2 - ‖(2⁻¹ : ℝ) • (F - o.hodgeStar hkl F)‖ / √2) := by
  have hJ := inner_apply_apply_of_orthonormalBasis h₀ h₂
  set Fm := (2⁻¹ : ℝ) • (F - o.hodgeStar hkl F)
  have hFm : o.hodgeStar hkl Fm = -Fm := by
    simp only [Fm, map_smul, map_sub, o.hodgeStar_hodgeStar_of_even even_two hkl, ← smul_neg,
      neg_sub]
  have hB (v : V) (hv : ‖v‖ = 1) :
      J.hermitianForm F v v = ⟪J.kahlerForm, F⟫ / 2 + J.hermitianForm Fm v v := by
    rw [hermitianForm_eq_add hkl h₀ h₂ he F]
    simp only [LinearMap.add_apply, LinearMap.smul_apply, innerₗ_apply_apply,
      real_inner_self_eq_norm_sq, hv, smul_eq_mul]
    ring
  refine ⟨?_, ?_⟩
  · obtain ⟨v, hv, hBv⟩ := exists_hermitianForm_apply_self_eq_neg hkl h₀ h₂ he hFm
    exact ⟨v, mem_sphere_zero_iff_norm.2 hv, by beta_reduce; rw [hB v hv, hBv, sub_eq_add_neg]⟩
  · rintro _ ⟨v, hv, rfl⟩
    rw [mem_sphere_zero_iff_norm] at hv
    beta_reduce
    have h := abs_hermitianForm_apply_self_le hkl hJ (Or.inr hFm) v
    rw [hv, one_pow, mul_one] at h
    rw [hB v hv]
    linarith [neg_abs_le (J.hermitianForm Fm v v)]

/-- **A lower bound on the Hermitian part bounds the anti-self-dual part**: for the complex
orientation, if `B(v, v) ≥ -C ‖v‖²` for all `v`, then `‖F⁻‖ / √2 ≤ ⟪ω, F⟫ / 2 + C`, where
`F⁻ = (F - ⋆F) / 2`. -/
theorem norm_smul_sub_hodgeStar_div_sqrt_two_le (F : ⋀[ℝ]^2 V) {C : ℝ}
    (hC : ∀ v, -C * ‖v‖ ^ 2 ≤ J.hermitianForm F v v) :
    ‖(2⁻¹ : ℝ) • (F - o.hodgeStar hkl F)‖ / √2 ≤ ⟪J.kahlerForm, F⟫ / 2 + C := by
  obtain ⟨v, hv, hBv⟩ := (isLeast_hermitianForm_apply_self hkl h₀ h₂ he F).1
  rw [mem_sphere_zero_iff_norm] at hv
  have h := hC v
  beta_reduce at hBv
  rw [hv, hBv] at h
  linarith

end Four

end TauCeti.AlmostComplexStructure

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import TauCeti.Analysis.InnerProductSpace.Complexification
public import TauCeti.Analysis.InnerProductSpace.LyapunovForm.Basic

/-!
# Hyperbolic operators have Lyapunov forms

In finite dimensions, a bounded operator `A` on a real inner product space has a Lyapunov form
(`ContinuousLinearMap.HasLyapunovForm`: a symmetric `S` and `c > 0` with
`c ‖v‖² ≤ ⟪S (A v), v⟫`) exactly when `A` is *hyperbolic*, that is, when its complexification has
no eigenvalue on the imaginary axis. In real terms, there are no `ω : ℝ` and `v, w : E`, not both
zero, with `A v = -ω w` and `A w = ω v`. The forward implication is
`ContinuousLinearMap.HasLyapunovForm.eq_zero_of_apply_eq_neg_smul_of_apply_eq_smul`; this file
proves the converse, the existence half of the inertia theorem of Ostrowski and Schneider.

The construction is first carried out over `ℂ`, by induction on the dimension, along a unitary
triangularization. Let `u` be a unit eigenvector of `A`, with eigenvalue `λ`, and let `K = u^⊥`.
In the splitting `F = ℂ u ⊕ K`, `A` is block upper triangular,

`A (a u + k) = (λ a + ⟪u, A k⟫) u + Q k`,

where `Q` is the compression of `A` to `K`. Every eigenvalue of `Q` is an eigenvalue of `A`, so `Q`
has a Lyapunov form `S_K` by induction. Then `S = re λ • P_u + t • S_K P_K`, with `P_u` and `P_K`
the orthogonal projections, satisfies

`re ⟪S (A v), v⟫ ≥ (re λ)² |a|² - |re λ| ‖A‖ |a| ‖k‖ + t c_K ‖k‖²`,

and for `t` large the right side is at least `(re λ)² ‖v‖² / 2`. Over `ℝ`, the operator is
complexified (`ContinuousLinearMap.complexifyL2`); the absence of imaginary eigen-pairs says that
the complexification has no eigenvalue on the imaginary axis, and the real part of its complex
Lyapunov form, restricted to real vectors, is a real Lyapunov form of `A`.

Combined with `TauCeti.WeakDerivStep.isFredholm_trajectoryOperator_of_hasLyapunovForm`, this shows
that `d/ds + A(s)` is Fredholm from `W^{1,2}` to `L²` for every continuous family `A` whose limits
at `±∞` are hyperbolic.

## Main declarations

* `ContinuousLinearMap.exists_isSymmetric_forall_mul_norm_sq_le_re_inner_of_re_ne_zero`: an
  operator on a finite-dimensional complex inner product space without eigenvalues on the
  imaginary axis has a self-adjoint `S` and `c > 0` with `c ‖v‖² ≤ re ⟪S (A v), v⟫`.
* `ContinuousLinearMap.hasLyapunovForm_iff_forall_eq_zero_of_apply_eq_neg_smul_of_apply_eq_smul`:
  on a finite-dimensional real inner product space, `A` has a Lyapunov form if and only if it has
  no purely imaginary eigenvalue.

## References

* A. Ostrowski and H. Schneider, *Some theorems on the inertia of general matrices*, J. Math. Anal.
  Appl. **4** (1962), 72–84.
* R. A. Horn and C. R. Johnson, *Topics in Matrix Analysis*, Cambridge University Press, 1991,
  §2.4 (the inertia theorem).
-/

public section

open Module Submodule TauCeti
open scoped InnerProductSpace ComplexConjugate

namespace ContinuousLinearMap

section Complex

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- Every eigenvalue of the compression of `A` to the orthogonal complement of an eigenvector of
`A` is an eigenvalue of `A`; so if no eigenvalue of `A` lies on the imaginary axis, neither does any
eigenvalue of the compression. -/
private theorem re_ne_zero_of_hasEigenvalue_compression {A : F →L[ℂ] F} {u : F} {lam : ℂ}
    (hu : ‖u‖ = 1) (hAu : A u = lam • u)
    (hA : ∀ μ, Module.End.HasEigenvalue (A : Module.End ℂ F) μ → μ.re ≠ 0) {μ : ℂ}
    (hμ : Module.End.HasEigenvalue (((ℂ ∙ u)ᗮ.orthogonalProjectionOnto ∘L A ∘L
      (ℂ ∙ u)ᗮ.subtypeL : (ℂ ∙ u)ᗮ →L[ℂ] (ℂ ∙ u)ᗮ) : Module.End ℂ (ℂ ∙ u)ᗮ) μ) :
    μ.re ≠ 0 := by
  set K := (ℂ ∙ u)ᗮ
  obtain ⟨k, hk, hk0⟩ := hμ.exists_hasEigenvector
  have hQk : K.orthogonalProjectionOnto (A k) = μ • k := Module.End.mem_eigenspace_iff.mp hk
  set b := ⟪u, A k⟫_ℂ
  -- Splitting `A k` along `ℂ u ⊕ K`.
  have hAk : A k = b • u + μ • (k : F) := by
    conv_lhs => rw [← (ℂ ∙ u).starProjection_add_starProjection_orthogonal (A k)]
    rw [starProjection_unit_singleton ℂ hu, starProjection_apply, hQk, coe_smul]
  have hu0 : u ≠ 0 := by
    rintro rfl
    simp at hu
  by_cases hμl : μ = lam
  · subst hμl
    exact hA μ (Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.mpr hAu, hu0⟩)
  -- Otherwise `k + b / (μ - λ) • u` is an eigenvector of `A` with eigenvalue `μ`.
  have hne : μ - lam ≠ 0 := sub_ne_zero.mpr hμl
  set z : F := (k : F) + (b / (μ - lam)) • u
  have hAz : A z = μ • z := by
    simp only [z, map_add, map_smul, hAk, hAu, smul_add, smul_smul]
    have : b + b / (μ - lam) * lam = μ * (b / (μ - lam)) := by
      field_simp
      ring
    rw [← this, add_smul]
    abel
  have hz0 : z ≠ 0 := by
    intro hz
    apply hk0
    have := congrArg K.orthogonalProjectionOnto hz
    rwa [map_add, map_smul, orthogonalProjectionOnto_mem_subspace_eq_self,
      orthogonalProjectionOnto_orthogonalComplement_singleton_eq_zero, smul_zero, add_zero,
      map_zero] at this
  exact hA μ (Module.End.hasEigenvalue_of_hasEigenvector
    ⟨Module.End.mem_eigenspace_iff.mpr hAz, hz0⟩)

/-- The block form of the quadratic form `re ⟪S (A v), v⟫` along `F = ℂ u ⊕ u^⊥`, for a unit
eigenvector `u` of `A` and `S = s • P_u + t • S_K P_K`: writing `v = a u + k` with `k ∈ u^⊥` and
`b = ⟪u, A k⟫`, it equals `s (re λ |a|² + re (conj b * a)) + t re ⟪S_K (Q k), k⟫`, where `Q` is the
compression of `A` to `u^⊥`. -/
private theorem re_inner_apply_eq_of_compression {A : F →L[ℂ] F} {u : F} {lam : ℂ}
    (hu : ‖u‖ = 1) (hAu : A u = lam • u) (SK : (ℂ ∙ u)ᗮ →L[ℂ] (ℂ ∙ u)ᗮ) (s t : ℝ) (v : F) :
    (⟪((s : ℂ) • (ℂ ∙ u).starProjection + (t : ℂ) •
      ((ℂ ∙ u)ᗮ.subtypeL ∘L SK ∘L (ℂ ∙ u)ᗮ.orthogonalProjectionOnto)) (A v), v⟫_ℂ).re =
      s * (lam.re * ‖⟪u, v⟫_ℂ‖ ^ 2 +
        (conj ⟪u, A ((ℂ ∙ u)ᗮ.orthogonalProjectionOnto v)⟫_ℂ * ⟪u, v⟫_ℂ).re) +
      t * (⟪SK (((ℂ ∙ u)ᗮ.orthogonalProjectionOnto ∘L A ∘L (ℂ ∙ u)ᗮ.subtypeL)
        ((ℂ ∙ u)ᗮ.orthogonalProjectionOnto v)), (ℂ ∙ u)ᗮ.orthogonalProjectionOnto v⟫_ℂ).re := by
  set K := (ℂ ∙ u)ᗮ
  set p := K.orthogonalProjectionOnto
  set a := ⟪u, v⟫_ℂ
  set k := p v
  set b := ⟪u, A k⟫_ℂ
  have hAv : A v = a • lam • u + A k := by
    conv_lhs => rw [← (ℂ ∙ u).starProjection_add_starProjection_orthogonal v]
    rw [starProjection_unit_singleton ℂ hu, starProjection_apply, map_add, map_smul, hAu]
  have hinner_u : ⟪u, A v⟫_ℂ = a * lam + b := by
    rw [hAv, inner_add_right, inner_smul_right, inner_smul_right, inner_self_eq_norm_sq_to_K, hu]
    simp [b]
  have hpAv : p (A v) = p (A k) := by
    rw [hAv, map_add, map_smul, map_smul,
      orthogonalProjectionOnto_orthogonalComplement_singleton_eq_zero, smul_zero, smul_zero,
      zero_add]
  simp only [add_apply, smul_apply, comp_apply, coe_subtypeL, Submodule.coe_subtype,
    inner_add_left, inner_smul_left, Complex.conj_ofReal, Complex.add_re, Complex.re_ofReal_mul]
  rw [starProjection_unit_singleton ℂ hu, inner_smul_left, hinner_u, hpAv,
    ← inner_orthogonalProjectionOnto_eq_of_mem_left]
  congr 2
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [map_add, map_mul, Complex.mul_re, Complex.add_re, Complex.mul_im, Complex.add_im,
    Complex.conj_re, Complex.conj_im]
  ring

/-- **The inductive step.** If `u` is a unit eigenvector of `A`, with eigenvalue `λ`, and `S_K` is a
Lyapunov form, with constant `c_K`, of the compression of `A` to `u^⊥`, then
`S = re λ • P_u + t • S_K P_K` with `t = ((re λ)² + ‖A‖²) / (2 c_K)` satisfies
`(re λ)² / 2 • ‖v‖² ≤ re ⟪S (A v), v⟫`. -/
private theorem mul_norm_sq_le_re_inner_of_compression {A : F →L[ℂ] F} {u : F} {lam : ℂ}
    (hu : ‖u‖ = 1) (hAu : A u = lam • u) {SK : (ℂ ∙ u)ᗮ →L[ℂ] (ℂ ∙ u)ᗮ} {cK : ℝ} (hcK : 0 < cK)
    (hQ : ∀ k, cK * ‖k‖ ^ 2 ≤
      (⟪SK (((ℂ ∙ u)ᗮ.orthogonalProjectionOnto ∘L A ∘L (ℂ ∙ u)ᗮ.subtypeL) k), k⟫_ℂ).re)
    (v : F) :
    lam.re ^ 2 / 2 * ‖v‖ ^ 2 ≤ (⟪((lam.re : ℂ) • (ℂ ∙ u).starProjection +
      (((lam.re ^ 2 + ‖A‖ ^ 2) / (2 * cK) : ℝ) : ℂ) •
        ((ℂ ∙ u)ᗮ.subtypeL ∘L SK ∘L (ℂ ∙ u)ᗮ.orthogonalProjectionOnto)) (A v), v⟫_ℂ).re := by
  rw [re_inner_apply_eq_of_compression hu hAu]
  set a := ⟪u, v⟫_ℂ
  set k := (ℂ ∙ u)ᗮ.orthogonalProjectionOnto v
  set b := ⟪u, A k⟫_ℂ
  set M := ‖A‖
  set t := (lam.re ^ 2 + M ^ 2) / (2 * cK)
  -- `‖v‖² = |a|² + ‖k‖²`, and the off-diagonal entry is bounded by `|b| ≤ ‖A‖ ‖k‖`.
  have hnorm : ‖v‖ ^ 2 = ‖a‖ ^ 2 + ‖k‖ ^ 2 := by
    rw [norm_sq_eq_add_norm_sq_starProjection v (ℂ ∙ u), starProjection_unit_singleton ℂ hu,
      starProjection_apply, norm_smul, hu, mul_one, norm_coe]
  have hb : ‖b‖ ≤ M * ‖k‖ := by
    calc ‖b‖ ≤ ‖u‖ * ‖A k‖ := norm_inner_le_norm _ _
      _ ≤ 1 * (M * ‖(k : F)‖) := by rw [hu]; gcongr; exact A.le_opNorm _
      _ = M * ‖k‖ := by rw [one_mul, norm_coe]
  have hcross : -(|lam.re| * (M * ‖k‖) * ‖a‖) ≤ lam.re * (conj b * a).re := by
    have h1 : |(conj b * a).re| ≤ M * ‖k‖ * ‖a‖ := by
      calc |(conj b * a).re| ≤ ‖conj b * a‖ := Complex.abs_re_le_norm _
        _ = ‖b‖ * ‖a‖ := by rw [norm_mul, Complex.norm_conj]
        _ ≤ M * ‖k‖ * ‖a‖ := by gcongr
    have h2 := neg_abs_le (lam.re * (conj b * a).re)
    rw [abs_mul] at h2
    nlinarith [abs_nonneg lam.re, abs_nonneg (conj b * a).re]
  have hQk := mul_le_mul_of_nonneg_left (hQ k) (by positivity : 0 ≤ t)
  have htc : t * cK = (lam.re ^ 2 + M ^ 2) / 2 := by
    simp only [t]
    field_simp
  have hsq : |lam.re| ^ 2 = lam.re ^ 2 := sq_abs _
  -- The form is at least `(re λ)² |a|² - |re λ| ‖A‖ |a| ‖k‖ + ((re λ)² + ‖A‖²) ‖k‖² / 2`.
  rw [hnorm]
  nlinarith [sq_nonneg (|lam.re| * ‖a‖ - M * ‖k‖)]

/-- The induction on the dimension behind
`ContinuousLinearMap.exists_isSymmetric_forall_mul_norm_sq_le_re_inner_of_re_ne_zero`. -/
private theorem exists_isSymmetric_forall_mul_norm_sq_le_re_inner_aux (n : ℕ) :
    ∀ (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F],
      finrank ℂ F = n → ∀ A : F →L[ℂ] F,
        (∀ μ, Module.End.HasEigenvalue (A : Module.End ℂ F) μ → μ.re ≠ 0) →
          ∃ S : F →L[ℂ] F, (S : F →ₗ[ℂ] F).IsSymmetric ∧
            ∃ c > 0, ∀ v, c * ‖v‖ ^ 2 ≤ (⟪S (A v), v⟫_ℂ).re := by
  induction n with
  | zero =>
    intro F _ _ _ hF A _
    have : Subsingleton F := finrank_zero_iff.mp hF
    refine ⟨0, fun _ _ ↦ by simp, 1, one_pos, fun v ↦ ?_⟩
    simp [Subsingleton.elim v 0]
  | succ n ih =>
    intro F _ _ _ hF A hA
    have : Nontrivial F := Module.nontrivial_of_finrank_eq_succ hF
    have : Fact (finrank ℂ F = n + 1) := ⟨hF⟩
    -- A unit eigenvector `u` of `A`, with eigenvalue `lam`.
    obtain ⟨lam, hlam⟩ := Module.End.exists_eigenvalue (A : Module.End ℂ F)
    obtain ⟨u₀, hu₀, hu₀0⟩ := hlam.exists_hasEigenvector
    have hAu₀ : A u₀ = lam • u₀ := Module.End.mem_eigenspace_iff.mp hu₀
    set u : F := ((‖u₀‖⁻¹ : ℝ) : ℂ) • u₀
    have hu : ‖u‖ = 1 := by
      simp [u, norm_smul, norm_ne_zero_iff.mpr hu₀0]
    have hAu : A u = lam • u := by
      simp only [u, map_smul, hAu₀, smul_comm lam]
    have hu0 : u ≠ 0 := norm_ne_zero_iff.mp (by rw [hu]; exact one_ne_zero)
    have hre : lam.re ≠ 0 := hA lam (Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.mpr hAu, hu0⟩)
    -- The compression of `A` to `K = u^⊥` has a Lyapunov form `SK`, by induction.
    set K := (ℂ ∙ u)ᗮ
    obtain ⟨SK, hSK, cK, hcK, hQ⟩ := ih K (finrank_orthogonal_span_singleton hu0)
      (K.orthogonalProjectionOnto ∘L A ∘L K.subtypeL)
      fun μ hμ ↦ re_ne_zero_of_hasEigenvalue_compression hu hAu hA hμ
    refine ⟨_, ?_, lam.re ^ 2 / 2, by positivity,
      mul_norm_sq_le_re_inner_of_compression hu hAu hcK hQ⟩
    -- The form `re λ • P_u + t • S_K P_K` is symmetric.
    intro x y
    simp only [coe_coe, add_apply, smul_apply, comp_apply, coe_subtypeL, Submodule.coe_subtype,
      inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, Complex.conj_ofReal]
    congr 2
    · exact (starProjection_isSymmetric (ℂ ∙ u)) x y
    · rw [← inner_orthogonalProjectionOnto_eq_of_mem_left, hSK.apply_clm,
        inner_orthogonalProjectionOnto_eq_of_mem_right]

/-- **Lyapunov forms over `ℂ`.** If no eigenvalue of an operator `A` on a finite-dimensional
complex inner product space lies on the imaginary axis, then there are a self-adjoint `S` and
`c > 0` with `c ‖v‖² ≤ re ⟪S (A v), v⟫` for every `v`. -/
theorem exists_isSymmetric_forall_mul_norm_sq_le_re_inner_of_re_ne_zero [FiniteDimensional ℂ F]
    (A : F →L[ℂ] F) (hA : ∀ μ, Module.End.HasEigenvalue (A : Module.End ℂ F) μ → μ.re ≠ 0) :
    ∃ S : F →L[ℂ] F, (S : F →ₗ[ℂ] F).IsSymmetric ∧
      ∃ c > 0, ∀ v, c * ‖v‖ ^ 2 ≤ (⟪S (A v), v⟫_ℂ).re :=
  exists_isSymmetric_forall_mul_norm_sq_le_re_inner_aux _ F rfl A hA

end Complex

section Real

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {A : E →L[ℝ] E}

/-- **Hyperbolic operators have Lyapunov forms.** On a finite-dimensional real inner product
space, an operator `A` has a Lyapunov form if and only if it has no purely imaginary eigenvalue:
there are no `ω` and `v, w`, not both zero, with `A v = -ω • w` and `A w = ω • v`. This is the
existence half of the inertia theorem of Ostrowski and Schneider. -/
theorem hasLyapunovForm_iff_forall_eq_zero_of_apply_eq_neg_smul_of_apply_eq_smul :
    A.HasLyapunovForm ↔
      ∀ (ω : ℝ) (v w : E), A v = -ω • w → A w = ω • v → v = 0 ∧ w = 0 := by
  refine ⟨fun h ω v w hv hw ↦ h.eq_zero_of_apply_eq_neg_smul_of_apply_eq_smul hv hw, fun h ↦ ?_⟩
  have : FiniteDimensional ℝ (WithLp 2 (Complexification E)) :=
    (WithLp.complexificationEquivProd E).toLinearEquiv.symm.finiteDimensional
  have : FiniteDimensional ℂ (WithLp 2 (Complexification E)) :=
    Module.Finite.of_restrictScalars_finite ℝ ℂ _
  -- The complexification of `A` has no eigenvalue on the imaginary axis.
  obtain ⟨Sc, hSc, c, hc, hcS⟩ :=
    exists_isSymmetric_forall_mul_norm_sq_le_re_inner_of_re_ne_zero A.complexifyL2
      fun μ hμ hre ↦ by
        obtain ⟨z, hz, hz0⟩ := hμ.exists_hasEigenvector
        have hAz : A.complexifyL2 z = μ • z := Module.End.mem_eigenspace_iff.mp hz
        have hre' : A z.ofLp.re = -μ.im • z.ofLp.im := by
          simpa [hre] using congrArg (fun w ↦ w.ofLp.re) hAz
        have him' : A z.ofLp.im = μ.im • z.ofLp.re := by
          simpa [hre] using congrArg (fun w ↦ w.ofLp.im) hAz
        obtain ⟨h₁, h₂⟩ := h μ.im _ _ hre' him'
        exact hz0 (WithLp.ofLp_injective 2 (Complexification.ext h₁ h₂))
  -- The real part of `Sc` on real vectors is a Lyapunov form of `A`.
  let S : E →L[ℝ] E := LinearMap.toContinuousLinearMap
    { toFun x := (Sc (WithLp.toLp 2 (Complexification.ofReal x))).ofLp.re
      map_add' x y := by
        have : Complexification.ofReal (x + y) =
            Complexification.ofReal x + Complexification.ofReal y := by
          ext <;> simp
        rw [this, WithLp.toLp_add, map_add, WithLp.ofLp_add, Complexification.add_re]
      map_smul' r x := by
        have : Complexification.ofReal (r • x) = (r : ℂ) • Complexification.ofReal x := by
          ext <;> simp
        rw [this, WithLp.toLp_smul, map_smul, WithLp.ofLp_smul, Complexification.smul_re]
        simp }
  have hS (x : E) : S x = (Sc (WithLp.toLp 2 (Complexification.ofReal x))).ofLp.re := rfl
  have hinner (x y : E) : ⟪S x, y⟫_ℝ =
      (⟪Sc (WithLp.toLp 2 (Complexification.ofReal x)),
        WithLp.toLp 2 (Complexification.ofReal y)⟫_ℂ).re := by
    simp [hS]
  refine hasLyapunovForm_iff.mpr ⟨S, fun x y ↦ ?_, c, hc, fun v ↦ ?_⟩
  · simp only [coe_coe]
    rw [hinner, hSc.apply_clm, ← Complex.conj_re, inner_conj_symm, real_inner_comm, hinner]
  · simpa [hinner] using hcS (WithLp.toLp 2 (Complexification.ofReal v))

end Real

end ContinuousLinearMap

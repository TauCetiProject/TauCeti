/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Adjoint
public import TauCeti.Analysis.Pseudodifferential.SchwartzMapping
public import TauCeti.Analysis.Pseudodifferential.Symbol.Classical
import TauCeti.Analysis.Fourier.ChangeOfVariables
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Deriv

/-!
# Pseudodifferential operators under linear changes of coordinates

Let `e` be a linear automorphism of `ℝⁿ`, and write `e^* u = u ∘ e` for the pullback of functions.
A linear change of coordinates conjugates a pseudodifferential operator into another one, with no
remainder: positions move by `e` and frequencies by the transpose of `e⁻¹`. In the Kohn–Nirenberg
quantization `Op(a) u (x) = (2π)⁻ⁿ ∫∫ exp(i ⟪x - y, ξ⟫) a(x, ξ) u(y) dy dξ`,

`Op(e^* a) (e^* u) = e^* (Op(a) u)`, where `(e^* a)(x, ξ) = a(e x, (e⁻¹)ᵀ ξ)`.

That is, the symbol is pulled back along the cotangent lift `(x, ξ) ↦ (e x, (e⁻¹)ᵀ ξ)` of `e`,
which is how covectors transform. The identity is exact because the phase is preserved:
`⟪e x - e y, (e⁻¹)ᵀ ξ⟫ = ⟪x - y, ξ⟫`, and the Jacobians `|det e|` of the substitutions in `y` and
in `ξ` cancel. For a general diffeomorphism the phase is only preserved to first order at the
diagonal, and the transformed symbol is determined by the old one modulo lower order terms.

## Main declarations

* `TauCeti.quantizeSchwartzValue_compCLMOfContinuousLinearEquiv`: the identity above for an
  arbitrary coefficient `a : E × E → (V →L[ℂ] W)` on a finite-dimensional real inner product
  space `E`, with no growth or regularity assumption on `a`.
* `TauCeti.Symbol.compContinuousLinearEquiv e`: the pullback `a ↦ e^* a`, a linear equivalence of
  the symbol class `S^m_{1,0}` onto itself, with inverse the pullback along `e⁻¹`
  (`TauCeti.Symbol.compContinuousLinearEquiv_symm`), contravariant in `e`
  (`TauCeti.Symbol.compContinuousLinearEquiv_trans`).
* `TauCeti.Symbol.IsUniform.compContinuousLinearEquiv`,
  `TauCeti.Symbol.HasCompactSpatialSupport.compContinuousLinearEquiv`,
  `TauCeti.Symbol.IsSmoothing.compContinuousLinearEquiv`: the pullback preserves uniform
  estimates, compact spatial support and smoothing symbols. It commutes with pointwise
  composition of symbols (`TauCeti.Symbol.compContinuousLinearEquiv_comp`) and with order
  inclusions.
* `TauCeti.Symbol.quantizeSchwartzValue_compContinuousLinearEquiv`: the identity above for a
  symbol, and `TauCeti.Symbol.quantizeUniformCLM_comp_compCLMOfContinuousLinearEquiv`, its form
  as an identity of continuous linear operators on Schwartz space for a uniform symbol.
* `TauCeti.ClassicalSymbol.compContinuousLinearEquiv e`: the pullback of classical symbols, whose
  homogeneous terms are the pullbacks `a_{m-j}(e x, (e⁻¹)ᵀ ξ)` of the homogeneous terms. In
  particular the principal symbol transforms as a function of covectors
  (`TauCeti.ClassicalSymbol.principal_compContinuousLinearEquiv`), and ellipticity is preserved
  (`TauCeti.ClassicalSymbol.IsElliptic.compContinuousLinearEquiv`).

## Proof outline

On the Fourier side, `𝓕 (u ∘ e) = |det e|⁻¹ 𝓕 u ∘ (e⁻¹)ᵀ` (`ContinuousLinearEquiv.fourier_comp`),
and the inverse Fourier transform transforms in the same way, so both Jacobian factors appear and
cancel. The symbol estimates of `e^* a` follow from the chain rule: a coordinate derivative of
`(x, ξ) ↦ a(e x, A ξ)` is a fixed linear combination of coordinate derivatives of `a` at
`(e x, A ξ)`, and the weights `⟨A ξ⟩` and `⟨ξ⟩` are comparable for a linear automorphism `A`.
For classical symbols the pulled back expansion carries the cutoff `χ((e⁻¹)ᵀ ξ)` instead of
`χ(ξ)`; the two cutoffs agree at large frequencies, so exchanging them costs smoothing terms only.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1 (invariance
  of pseudodifferential operators under changes of variables, whose principal part is the
  pullback along the cotangent lift).
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, §8.
-/

public section

noncomputable section

open scoped FourierTransform SchwartzMap RealInnerProductSpace InnerProduct ContDiff
open MeasureTheory Real FourierTransform

namespace TauCeti

/-! ### The quantization identity -/

section Quantization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]

/-- **Linear change of coordinates in the quantization.** Pulling back the input along a linear
automorphism `e` and the coefficient along the cotangent lift `(x, ξ) ↦ (e x, (e⁻¹)ᵀ ξ)` pulls
back the output along `e`: `Op(a ∘ (e × (e⁻¹)ᵀ)) (u ∘ e) (x) = Op(a) u (e x)`. No growth or
regularity of `a` is needed: both sides are the same integral after a linear substitution. -/
theorem quantizeSchwartzValue_compCLMOfContinuousLinearEquiv (a : E × E → V →L[ℂ] W)
    (e : E ≃L[ℝ] E) (u : 𝓢(E, V)) (x : E) :
    quantizeSchwartzValue (fun p ↦ a (e p.1, ((e.symm : E →L[ℝ] E)†) p.2))
        (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e u) x =
      quantizeSchwartzValue a u (e x) := by
  set A : E ≃L[ℝ] E := e.symm.adjointEquiv
  set g : E → W := fun η ↦ a (e x, (2 * π) • η) (𝓕 (u : E → V) η)
  have hA (ξ : E) : ((e.symm : E →L[ℝ] E)†) ξ = A ξ := (e.symm.adjointEquiv_apply ξ).symm
  -- The adjoint of the inverse of `A` is `e`.
  have hAe : ((A.symm : E →L[ℝ] E))† = (e : E →L[ℝ] E) := by
    have h : (A.symm : E →L[ℝ] E) = (e : E →L[ℝ] E)† := by
      ext ξ
      simp [A, ContinuousLinearEquiv.adjointEquiv_apply]
    rw [h, ContinuousLinearMap.adjoint_adjoint]
  -- The Jacobians of `e` and of `A = (e⁻¹)ᵀ` are inverse to each other.
  have hdet : |(e : E →ₗ[ℝ] E).det|⁻¹ * |A.toLinearEquiv.toLinearMap.det|⁻¹ = 1 := by
    have h1 : A.toLinearEquiv.toLinearMap.det = (e.symm : E →ₗ[ℝ] E).det := by
      have : A.toLinearEquiv.toLinearMap = LinearMap.adjoint (e.symm : E →ₗ[ℝ] E) := by
        ext ξ
        rw [LinearMap.adjoint_eq_toCLM_adjoint]
        simp only [A, LinearEquiv.coe_coe, ContinuousLinearEquiv.coe_toLinearEquiv,
          ContinuousLinearEquiv.adjointEquiv_apply]
        congr 2
      rw [this, LinearMap.det_adjoint, star_trivial]
    have h2 : (e : E →ₗ[ℝ] E).det * (e.symm : E →ₗ[ℝ] E).det = 1 := by
      rw [← LinearMap.det_comp]
      have : (e : E →ₗ[ℝ] E) ∘ₗ (e.symm : E →ₗ[ℝ] E) = LinearMap.id := by
        ext ξ
        simp
      rw [this, LinearMap.det_id]
    rw [h1, ← mul_inv, ← abs_mul, h2, abs_one, inv_one]
  have hu : (𝓕 ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e u : 𝓢(E, V)) : E → V)) =
      fun ζ ↦ |(e : E →ₗ[ℝ] E).det|⁻¹ • 𝓕 (u : E → V) (A ζ) := by
    funext ζ
    rw [← hA, ← e.fourier_comp (u : E → V) ζ, SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
  rw [quantizeSchwartzValue_eq_fourierInv, quantizeSchwartzValue_eq_fourierInv]
  simp only [SchwartzMap.fourier_coe]
  have hint : (fun ζ ↦ a (e x, ((e.symm : E →L[ℝ] E)†) ((2 * π) • ζ))
      (𝓕 ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e u : 𝓢(E, V)) : E → V) ζ)) =
      (fun η ↦ (|(e : E →ₗ[ℝ] E).det|⁻¹ : ℝ) • g η) ∘ A := by
    funext ζ
    simp only [hu, hA, map_smul, ContinuousLinearMap.map_smul_of_tower, Function.comp_apply, g]
  rw [hint, A.fourierInv_comp, hAe, ContinuousLinearEquiv.coe_coe, Real.fourierInv_eq,
    Real.fourierInv_eq]
  simp only [smul_comm _ (|(e : E →ₗ[ℝ] E).det|⁻¹ : ℝ), integral_smul, smul_smul]
  rw [hdet, one_smul]

end Quantization

namespace Symbol

variable {n : ℕ} {V W U : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] [NormedAddCommGroup U] [NormedSpace ℂ U] {m m' : ℝ}

/-! ### Symbol estimates under linear maps of positions and frequencies -/

section Estimates

variable (B C : CoordinateSpace n →L[ℝ] CoordinateSpace n)

private theorem contDiff_comp_prodMap (a : Symbol n V W m) :
    ContDiff ℝ ∞ fun p : CoordinateSpace n × CoordinateSpace n ↦ a.coefficient (B p.1, C p.2) :=
  a.contDiff_coefficient.comp
    ((B.contDiff.comp contDiff_fst).prodMk (C.contDiff.comp contDiff_snd))

private theorem fderiv_comp_prodMap (a : Symbol n V W m)
    (p v : CoordinateSpace n × CoordinateSpace n) :
    fderiv ℝ (fun q : CoordinateSpace n × CoordinateSpace n ↦ a.coefficient (B q.1, C q.2)) p v =
      fderiv ℝ a.coefficient (B p.1, C p.2) (B v.1, C v.2) := by
  have hd : DifferentiableAt ℝ a.coefficient (B p.1, C p.2) :=
    (a.contDiff_coefficient.differentiable (by simp)).differentiableAt
  have h := (hd.hasFDerivAt.comp p (B.prodMap C).hasFDerivAt).fderiv
  exact congrArg (fun L ↦ L v) h

/-- **Chain rule in the frequency.** A frequency derivative of `(x, ξ) ↦ a(B x, C ξ)` is the
combination of the frequency derivatives of `a` with the coordinates of `C e_j`. -/
private theorem coordinateDeriv_snd_comp_prodMap (a : Symbol n V W m) (j : Fin n) :
    (fun p : CoordinateSpace n × CoordinateSpace n ↦
        coordinateDeriv [j] (fun η ↦ a.coefficient (B p.1, C η)) p.2) =
      ∑ l, (C (EuclideanSpace.single j 1)) l •
        fun p : CoordinateSpace n × CoordinateSpace n ↦
          (frequencyDeriv l a).coefficient (B p.1, C p.2) := by
  funext p
  have hf := (contDiff_comp_prodMap B C a).differentiable (by simp) p
  have h := coordinateDeriv_snd_eq_fderiv hf j
  simp only at h
  rw [h, fderiv_comp_prodMap, fderiv_apply_eq_sum_coordinateDeriv
    ((a.contDiff_coefficient.differentiable (by simp)) _)]
  simp [Finset.sum_apply]

/-- **Chain rule in the position.** A position derivative of `(x, ξ) ↦ a(B x, C ξ)` is the
combination of the position derivatives of `a` with the coordinates of `B e_j`. -/
private theorem coordinateDeriv_fst_comp_prodMap (a : Symbol n V W m) (j : Fin n) :
    (fun p : CoordinateSpace n × CoordinateSpace n ↦
        coordinateDeriv [j] (fun y ↦ a.coefficient (B y, C p.2)) p.1) =
      ∑ l, (B (EuclideanSpace.single j 1)) l •
        fun p : CoordinateSpace n × CoordinateSpace n ↦
          (spatialDeriv l a).coefficient (B p.1, C p.2) := by
  funext p
  have hf := (contDiff_comp_prodMap B C a).differentiable (by simp) p
  have h := coordinateDeriv_fst_eq_fderiv hf j
  simp only at h
  rw [h, fderiv_comp_prodMap, fderiv_apply_eq_sum_coordinateDeriv
    ((a.contDiff_coefficient.differentiable (by simp)) _)]
  simp [Finset.sum_apply]

/-- **Symbol estimates under linear maps.** If the weights `⟨C ξ⟩ ^ s` and `⟨ξ⟩ ^ s` are
comparable for every real `s`, and `a` satisfies its estimates of order `m` for positions in `T`,
then `(x, ξ) ↦ a(B x, C ξ)` satisfies the estimates of order `m` for positions in `S`, where `B`
maps `S` into `T`. The proof is an induction on the number of derivatives, peeling off the
innermost one with the chain rules above. -/
private theorem exists_bound_mixedDeriv_comp_prodMap
    (hC : ∀ s : ℝ, ∃ c, ∀ ξ, (1 + ‖C ξ‖ ^ 2) ^ (s / 2) ≤ c * (1 + ‖ξ‖ ^ 2) ^ (s / 2))
    {S T : Set (CoordinateSpace n)} (hST : Set.MapsTo B S T) (k : ℕ) :
    ∀ {m : ℝ} (a : Symbol n V W m), (∀ α β : List (Fin n), ∃ D, 0 ≤ D ∧ ∀ y ∈ T, ∀ η,
      ‖mixedDeriv α β a.coefficient y η‖ ≤ D * (1 + ‖η‖ ^ 2) ^ ((m - β.length) / 2)) →
    ∀ α β : List (Fin n), α.length + β.length = k → ∃ D, 0 ≤ D ∧ ∀ x ∈ S, ∀ ξ,
      ‖mixedDeriv α β (fun p ↦ a.coefficient (B p.1, C p.2)) x ξ‖ ≤
        D * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2) := by
  induction k with
  | zero =>
    intro m a ha α β hk
    obtain ⟨rfl, rfl⟩ : α = [] ∧ β = [] := by
      simpa only [Nat.add_eq_zero_iff, List.length_eq_zero_iff] using hk
    obtain ⟨D, hD, hDa⟩ := ha [] []
    obtain ⟨c, hcC⟩ := hC m
    -- At `ξ = 0` the comparison reads `1 ≤ c`.
    have hc : 0 ≤ c := by simpa using (zero_lt_one.trans_le (by simpa using hcC 0)).le
    refine ⟨D * c, mul_nonneg hD hc, fun x hx ξ ↦ ?_⟩
    have h := hDa (B x) (hST hx) (C ξ)
    simp only [mixedDeriv_nil_nil, List.length_nil, Nat.cast_zero, sub_zero] at h ⊢
    calc ‖a.coefficient (B x, C ξ)‖ ≤ D * (1 + ‖C ξ‖ ^ 2) ^ (m / 2) := h
      _ ≤ D * (c * (1 + ‖ξ‖ ^ 2) ^ (m / 2)) := mul_le_mul_of_nonneg_left (hcC ξ) hD
      _ = D * c * (1 + ‖ξ‖ ^ 2) ^ (m / 2) := by ring
  | succ k ih =>
    intro m a ha α β hk
    rcases β.eq_nil_or_concat with rfl | ⟨β', j, rfl⟩
    · -- No frequency derivative: peel off the innermost position derivative.
      rcases α.eq_nil_or_concat with rfl | ⟨α', j, rfl⟩
      · simp at hk
      rw [List.concat_eq_append] at hk ⊢
      have ha' (l : Fin n) : ∀ α β : List (Fin n), ∃ D, 0 ≤ D ∧ ∀ y ∈ T, ∀ η,
          ‖mixedDeriv α β (spatialDeriv l a).coefficient y η‖ ≤
            D * (1 + ‖η‖ ^ 2) ^ ((m - β.length) / 2) := fun α β ↦ by
        simpa only [mixedDeriv_spatialDeriv] using ha (α ++ [l]) β
      choose D hD0 hD using fun l ↦
        ih (spatialDeriv l a) (ha' l) α' [] (by simpa using hk)
      refine ⟨‖B (EuclideanSpace.single j 1)‖ * ∑ l, D l,
        mul_nonneg (norm_nonneg _) (Finset.sum_nonneg fun l _ ↦ hD0 l), fun x hx ξ ↦ ?_⟩
      have smooth_smul_spatial (l : Fin n) : ContDiff ℝ ∞ ((B (EuclideanSpace.single j 1)) l •
          fun p : CoordinateSpace n × CoordinateSpace n ↦
            (spatialDeriv l a).coefficient (B p.1, C p.2)) :=
        (contDiff_comp_prodMap B C (spatialDeriv l a)).const_smul
          ((B (EuclideanSpace.single j 1)) l)
      rw [← mixedDeriv_coordinateDeriv_fst (contDiff_comp_prodMap B C a),
        coordinateDeriv_fst_comp_prodMap,
        mixedDeriv_sum fun l _ ↦ smooth_smul_spatial l]
      simp only [mixedDeriv_const_smul]
      refine (CoordinateSpace.norm_sum_smul_le _ _).trans ?_
      rw [mul_assoc, Finset.sum_mul]
      gcongr with l
      exact hD l x hx ξ
    · -- Peel off the innermost frequency derivative, which lowers the order by one.
      rw [List.concat_eq_append] at hk ⊢
      have ha' (l : Fin n) : ∀ α β : List (Fin n), ∃ D, 0 ≤ D ∧ ∀ y ∈ T, ∀ η,
          ‖mixedDeriv α β (frequencyDeriv l a).coefficient y η‖ ≤
            D * (1 + ‖η‖ ^ 2) ^ ((m - 1 - β.length) / 2) := fun α β ↦ by
        rw [order_sub_one_sub_length m β l]
        simpa only [mixedDeriv_frequencyDeriv] using ha α (β ++ [l])
      choose D hD0 hD using fun l ↦
        ih (frequencyDeriv l a) (ha' l) α β' (by simpa [← add_assoc] using hk)
      refine ⟨‖C (EuclideanSpace.single j 1)‖ * ∑ l, D l,
        mul_nonneg (norm_nonneg _) (Finset.sum_nonneg fun l _ ↦ hD0 l), fun x hx ξ ↦ ?_⟩
      have smooth_smul_frequency (l : Fin n) : ContDiff ℝ ∞ ((C (EuclideanSpace.single j 1)) l •
          fun p : CoordinateSpace n × CoordinateSpace n ↦
            (frequencyDeriv l a).coefficient (B p.1, C p.2)) :=
        (contDiff_comp_prodMap B C (frequencyDeriv l a)).const_smul
          ((C (EuclideanSpace.single j 1)) l)
      rw [← mixedDeriv_coordinateDeriv_snd, coordinateDeriv_snd_comp_prodMap,
        mixedDeriv_sum fun l _ ↦ smooth_smul_frequency l,
        ← order_sub_one_sub_length]
      simp only [mixedDeriv_const_smul]
      refine (CoordinateSpace.norm_sum_smul_le _ _).trans ?_
      rw [mul_assoc, Finset.sum_mul]
      gcongr with l
      exact hD l x hx ξ

end Estimates

/-! ### The pullback of symbols -/

/-- The pullback `(x, ξ) ↦ a(e x, (e⁻¹)ᵀ ξ)` of a symbol of order `m`, as a symbol of order `m`. -/
private def pullback (e : CoordinateSpace n ≃L[ℝ] CoordinateSpace n) (a : Symbol n V W m) :
    Symbol n V W m where
  coefficient p :=
    a.coefficient (e p.1, ((e.symm : CoordinateSpace n →L[ℝ] CoordinateSpace n)†) p.2)
  contDiff_coefficient := contDiff_comp_prodMap (e : CoordinateSpace n →L[ℝ] CoordinateSpace n)
    ((e.symm : CoordinateSpace n →L[ℝ] CoordinateSpace n)†) a
  exists_bound K hK α β := by
    refine exists_bound_mixedDeriv_comp_prodMap (e : CoordinateSpace n →L[ℝ] CoordinateSpace n)
      _ (fun s ↦ ?_) (Set.mapsTo_image _ K) _ a
      (a.exists_bound _ (hK.image e.continuous)) α β rfl
    simpa only [ContinuousLinearEquiv.adjointEquiv_apply] using
      e.symm.adjointEquiv.exists_one_add_norm_apply_sq_rpow_le (s / 2)

private theorem coefficient_pullback (e : CoordinateSpace n ≃L[ℝ] CoordinateSpace n)
    (a : Symbol n V W m) (p : CoordinateSpace n × CoordinateSpace n) :
    (pullback e a).coefficient p =
      a.coefficient (e p.1, ((e.symm : CoordinateSpace n →L[ℝ] CoordinateSpace n)†) p.2) :=
  (rfl)

private theorem pullback_pullback (e₁ e₂ : CoordinateSpace n ≃L[ℝ] CoordinateSpace n)
    (a : Symbol n V W m) : pullback e₂ (pullback e₁ a) = pullback (e₂.trans e₁) a := by
  ext1
  funext p
  simp only [coefficient_pullback, ContinuousLinearEquiv.trans_apply]
  have h : (((e₂.trans e₁).symm : CoordinateSpace n ≃L[ℝ] CoordinateSpace n) :
      CoordinateSpace n →L[ℝ] CoordinateSpace n) =
      (e₂.symm : CoordinateSpace n →L[ℝ] CoordinateSpace n) ∘L
        (e₁.symm : CoordinateSpace n →L[ℝ] CoordinateSpace n) :=
    ContinuousLinearMap.ext fun ξ ↦ ContinuousLinearEquiv.symm_trans_apply _ _ _
  rw [h, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_apply]

private theorem pullback_refl (a : Symbol n V W m) :
    pullback (ContinuousLinearEquiv.refl ℝ (CoordinateSpace n)) a = a := by
  ext1
  funext p
  simp [coefficient_pullback, ContinuousLinearEquiv.refl_symm, ContinuousLinearMap.adjoint_id]

/-- The **pullback of symbols along a linear change of coordinates** `e`:
`(e^* a)(x, ξ) = a(e x, (e⁻¹)ᵀ ξ)`, the pullback along the cotangent lift of `e`. It is a linear
automorphism of `S^m_{1,0}`, and its quantization is the conjugate of `Op(a)` by the pullback of
functions along `e` (`TauCeti.Symbol.quantizeSchwartzValue_compContinuousLinearEquiv`). The
transpose of `e⁻¹` is written as the adjoint of `e⁻¹` for the Euclidean inner product. -/
def compContinuousLinearEquiv (e : CoordinateSpace n ≃L[ℝ] CoordinateSpace n) :
    Symbol n V W m ≃ₗ[ℂ] Symbol n V W m where
  toFun := pullback e
  invFun := pullback e.symm
  map_add' a b := (rfl)
  map_smul' c a := (rfl)
  left_inv a := by rw [pullback_pullback, ContinuousLinearEquiv.symm_trans_self, pullback_refl]
  right_inv a := by rw [pullback_pullback, ContinuousLinearEquiv.self_trans_symm, pullback_refl]

@[simp]
theorem coefficient_compContinuousLinearEquiv (e : CoordinateSpace n ≃L[ℝ] CoordinateSpace n)
    (a : Symbol n V W m) (p : CoordinateSpace n × CoordinateSpace n) :
    (compContinuousLinearEquiv e a).coefficient p =
      a.coefficient (e p.1, ((e.symm : CoordinateSpace n →L[ℝ] CoordinateSpace n)†) p.2) :=
  (rfl)

/-- The inverse of the pullback along `e` is the pullback along `e⁻¹`. -/
@[simp]
theorem compContinuousLinearEquiv_symm (e : CoordinateSpace n ≃L[ℝ] CoordinateSpace n) :
    (compContinuousLinearEquiv e : Symbol n V W m ≃ₗ[ℂ] Symbol n V W m).symm =
      compContinuousLinearEquiv e.symm :=
  (rfl)

/-- The pullback along the identity is the identity. -/
@[simp]
theorem compContinuousLinearEquiv_refl :
    (compContinuousLinearEquiv (ContinuousLinearEquiv.refl ℝ (CoordinateSpace n)) :
      Symbol n V W m ≃ₗ[ℂ] Symbol n V W m) = LinearEquiv.refl ℂ _ :=
  LinearEquiv.ext pullback_refl

/-- **Functoriality.** Pulling back along `e₂ ∘ e₁` is pulling back along `e₂`, then along `e₁`. -/
theorem compContinuousLinearEquiv_trans (e₁ e₂ : CoordinateSpace n ≃L[ℝ] CoordinateSpace n) :
    (compContinuousLinearEquiv (e₁.trans e₂) : Symbol n V W m ≃ₗ[ℂ] Symbol n V W m) =
      (compContinuousLinearEquiv e₂).trans (compContinuousLinearEquiv e₁) :=
  LinearEquiv.ext fun a ↦ (pullback_pullback e₂ e₁ a).symm

/-- The pullback commutes with order inclusions. -/
theorem compContinuousLinearEquiv_inclusion (e : CoordinateSpace n ≃L[ℝ] CoordinateSpace n)
    (h : m ≤ m') (a : Symbol n V W m) :
    compContinuousLinearEquiv e (inclusion h a) = inclusion h (compContinuousLinearEquiv e a) := by
  ext1
  funext p
  simp [coefficient_inclusion]

/-- The pullback commutes with the pointwise composition of symbols. -/
theorem compContinuousLinearEquiv_comp (e : CoordinateSpace n ≃L[ℝ] CoordinateSpace n)
    (b : Symbol n W U m') (a : Symbol n V W m) :
    compContinuousLinearEquiv e (b.comp a) =
      (compContinuousLinearEquiv e b).comp (compContinuousLinearEquiv e a) := by
  ext1
  funext p
  simp [coefficient_comp]

/-- The pullback of a symbol with uniform estimates has uniform estimates. -/
theorem IsUniform.compContinuousLinearEquiv {a : Symbol n V W m} (ha : a.IsUniform)
    (e : CoordinateSpace n ≃L[ℝ] CoordinateSpace n) :
    (compContinuousLinearEquiv e a).IsUniform := by
  refine isUniform_iff.2 fun α β ↦ ?_
  refine exists_bound_mixedDeriv_comp_prodMap (e : CoordinateSpace n →L[ℝ] CoordinateSpace n)
    _ (fun s ↦ ?_) (Set.mapsTo_univ _ Set.univ) _ a
    (fun α β ↦ ?_) α β rfl |>.imp fun D hD ↦ ⟨hD.1, fun x ξ ↦ hD.2 x (Set.mem_univ x) ξ⟩
  · simpa only [ContinuousLinearEquiv.adjointEquiv_apply] using
      e.symm.adjointEquiv.exists_one_add_norm_apply_sq_rpow_le (s / 2)
  · obtain ⟨D, hD, h⟩ := isUniform_iff.1 ha α β
    exact ⟨D, hD, fun y _ η ↦ h y η⟩

/-- The pullback along `e` of a symbol vanishing at positions outside a compact set `K` vanishes
at positions outside the compact set `e⁻¹ K`. -/
theorem HasCompactSpatialSupport.compContinuousLinearEquiv {a : Symbol n V W m}
    (ha : a.HasCompactSpatialSupport) (e : CoordinateSpace n ≃L[ℝ] CoordinateSpace n) :
    (compContinuousLinearEquiv e a).HasCompactSpatialSupport := by
  obtain ⟨K, hK, hKa⟩ := hasCompactSpatialSupport_iff.1 ha
  refine hasCompactSpatialSupport_iff.2
    ⟨e.symm '' K, hK.image e.symm.continuous, fun x hx ξ ↦ hKa _ (fun hxK ↦ hx ?_) _⟩
  exact ⟨e x, hxK, e.symm_apply_apply x⟩

/-- The pullback of a smoothing symbol is smoothing. -/
theorem IsSmoothing.compContinuousLinearEquiv {a : Symbol n V W m} (ha : a.IsSmoothing)
    (e : CoordinateSpace n ≃L[ℝ] CoordinateSpace n) :
    (compContinuousLinearEquiv e a).IsSmoothing := isSmoothing_iff.2 fun m' ↦ by
  obtain ⟨b, hb⟩ := isSmoothing_iff.1 ha m'
  exact ⟨Symbol.compContinuousLinearEquiv e b, by
    funext p
    simp only [coefficient_compContinuousLinearEquiv, hb]⟩

/-! ### Quantization of the pullback -/

/-- **Linear change of coordinates for pseudodifferential operators.** For a symbol `a` and a
linear automorphism `e` of `ℝⁿ`, `Op(e^* a) (u ∘ e) = Op(a) u ∘ e` on Schwartz functions `u`,
exactly. -/
theorem quantizeSchwartzValue_compContinuousLinearEquiv
    (e : CoordinateSpace n ≃L[ℝ] CoordinateSpace n) (a : Symbol n V W m)
    (u : 𝓢(CoordinateSpace n, V)) (x : CoordinateSpace n) :
    quantizeSchwartzValue (compContinuousLinearEquiv e a).coefficient
        (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e u) x =
      quantizeSchwartzValue a.coefficient u (e x) :=
  quantizeSchwartzValue_compCLMOfContinuousLinearEquiv a.coefficient e u x

/-- **Linear change of coordinates, operator form.** For a symbol `a` with uniform estimates, the
quantization of its pullback along `e` is the conjugate of `Op(a)` by the pullback of Schwartz
functions along `e`: `Op(e^* a) ∘ e^* = e^* ∘ Op(a)`. -/
theorem quantizeUniformCLM_comp_compCLMOfContinuousLinearEquiv
    (e : CoordinateSpace n ≃L[ℝ] CoordinateSpace n) {a : Symbol n V W m} (ha : a.IsUniform) :
    (quantizeUniformCLM (compContinuousLinearEquiv e a) (ha.compContinuousLinearEquiv e)).comp
        (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e) =
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e).comp (quantizeUniformCLM a ha) := by
  ext u x
  simp [quantizeSchwartzValue_compContinuousLinearEquiv]

end Symbol

/-! ### Classical symbols -/

namespace ClassicalSymbol

open HomogeneousSymbol

variable {n : ℕ} {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] {m : ℝ}

/-- The pullback `(x, ξ) ↦ a(e x, (e⁻¹)ᵀ ξ)` of a homogeneous symbol along the cotangent lift of
`e`. -/
private abbrev homogeneousPullback (e : CoordinateSpace n ≃L[ℝ] CoordinateSpace n) {d : ℝ}
    (a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W d) :
    HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W d :=
  (a.compPosition e e.contDiff).compFrequency _ (e.symm.adjoint_bijective.1)

/-- Pulling back a cut-off term along `e` gives the cut-off term of the pulled back homogeneous
symbol, up to a smoothing symbol: the cutoffs `χ ∘ (e⁻¹)ᵀ` and `χ` are both `1` at all large
frequencies. -/
private theorem isSmoothing_compContinuousLinearEquiv_cutoffSymbol_sub
    (e : CoordinateSpace n ≃L[ℝ] CoordinateSpace n) (χ : FrequencyCutoff (CoordinateSpace n))
    {d : ℝ} (a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W d) :
    (Symbol.compContinuousLinearEquiv e (cutoffSymbol χ a) -
      cutoffSymbol χ (homogeneousPullback e a)).IsSmoothing := by
  set B := e.symm.adjointEquiv
  refine Symbol.isSmoothing_of_coefficient_eq_zero
    (2 * (‖(B.symm : CoordinateSpace n →L[ℝ] CoordinateSpace n)‖ + 1)) fun x ξ hξ ↦ ?_
  have hc := norm_nonneg (B.symm : CoordinateSpace n →L[ℝ] CoordinateSpace n)
  -- `‖ξ‖ ≤ ‖(e⁻¹)ᵀ⁻¹‖ ‖B ξ‖`, so `B ξ` is also beyond the transition annulus of `χ`.
  have hBξ : 2 ≤ ‖B ξ‖ := by
    have h := (B.symm : CoordinateSpace n →L[ℝ] CoordinateSpace n).le_opNorm (B ξ)
    rw [ContinuousLinearEquiv.coe_coe, B.symm_apply_apply] at h
    nlinarith [norm_nonneg (B ξ)]
  have hξ2 : 2 ≤ ‖ξ‖ := by nlinarith
  have hB : ((e.symm : CoordinateSpace n →L[ℝ] CoordinateSpace n)†) ξ = B ξ :=
    (e.symm.adjointEquiv_apply ξ).symm
  simp [coefficient_cutoffSymbol, hB, χ.apply_eq_one_of_two_le_norm hBξ,
    χ.apply_eq_one_of_two_le_norm hξ2]

/-- The pullback of a classical symbol along a linear change of coordinates `e`, as a map. -/
private def pullback (e : CoordinateSpace n ≃L[ℝ] CoordinateSpace n)
    (a : ClassicalSymbol n V W m) : ClassicalSymbol n V W m where
  toSymbol := Symbol.compContinuousLinearEquiv e a.toSymbol
  term j := homogeneousPullback e (a.term j)
  exists_remainder' := by
    obtain ⟨χ, -⟩ := a.exists_remainder'
    refine ⟨χ, fun N ↦ ?_⟩
    -- The pulled back remainder uses the cutoff `χ ∘ (e⁻¹)ᵀ`; returning to `χ` costs smoothing
    -- terms, which have order `m - N` like the remainder.
    choose s hs using fun j ↦ Symbol.isSmoothing_iff.1
      (isSmoothing_compContinuousLinearEquiv_cutoffSymbol_sub e χ (a.term j)) (m - N)
    refine ⟨Symbol.compContinuousLinearEquiv e (a.remainder χ N) + ∑ j ∈ Finset.range N, s j,
      fun p ↦ ?_⟩
    simp only [Symbol.coefficient_add, Pi.add_apply, Symbol.coefficient_sum, Finset.sum_apply, hs,
      Symbol.coefficient_sub, Pi.sub_apply, Symbol.coefficient_compContinuousLinearEquiv,
      coefficient_remainder, coefficient_cutoffSymbol, Finset.sum_sub_distrib]
    abel

/-- The **pullback of classical symbols along a linear change of coordinates** `e`: the full
symbol is pulled back by `TauCeti.Symbol.compContinuousLinearEquiv e`, and so is each homogeneous
term, `a_{m-j}(e x, (e⁻¹)ᵀ ξ)`. In particular the principal symbol transforms as a function on
covectors (`TauCeti.ClassicalSymbol.principal_compContinuousLinearEquiv`). -/
def compContinuousLinearEquiv (e : CoordinateSpace n ≃L[ℝ] CoordinateSpace n) :
    ClassicalSymbol n V W m ≃ₗ[ℂ] ClassicalSymbol n V W m where
  toFun := pullback e
  invFun := pullback e.symm
  map_add' a b :=
    ClassicalSymbol.ext (map_add (Symbol.compContinuousLinearEquiv e) a.toSymbol b.toSymbol)
  map_smul' c a := ClassicalSymbol.ext (map_smul (Symbol.compContinuousLinearEquiv e) c a.toSymbol)
  left_inv a := ClassicalSymbol.ext
    ((Symbol.compContinuousLinearEquiv e).symm_apply_apply a.toSymbol)
  right_inv a := ClassicalSymbol.ext
    ((Symbol.compContinuousLinearEquiv e).apply_symm_apply a.toSymbol)

@[simp]
theorem toSymbol_compContinuousLinearEquiv (e : CoordinateSpace n ≃L[ℝ] CoordinateSpace n)
    (a : ClassicalSymbol n V W m) :
    (compContinuousLinearEquiv e a).toSymbol = Symbol.compContinuousLinearEquiv e a.toSymbol :=
  (rfl)

/-- The homogeneous terms of the pullback are the pullbacks of the homogeneous terms. -/
@[simp]
theorem term_compContinuousLinearEquiv (e : CoordinateSpace n ≃L[ℝ] CoordinateSpace n)
    (a : ClassicalSymbol n V W m) (j : ℕ) :
    (compContinuousLinearEquiv e a).term j =
      ((a.term j).compPosition e e.contDiff).compFrequency _ (e.symm.adjoint_bijective.1) :=
  (rfl)

/-- **The principal symbol transforms as a function on covectors**: the principal symbol of the
pullback along `e` is `σ(a)(e x, (e⁻¹)ᵀ ξ)`. -/
theorem principal_compContinuousLinearEquiv (e : CoordinateSpace n ≃L[ℝ] CoordinateSpace n)
    (a : ClassicalSymbol n V W m) :
    (compContinuousLinearEquiv e a).principal =
      (a.principal.compPosition e e.contDiff).compFrequency _ (e.symm.adjoint_bijective.1) := by
  ext1
  funext p
  simp [coefficient_principal]

/-- The pullback of an elliptic classical symbol is elliptic. -/
theorem IsElliptic.compContinuousLinearEquiv {a : ClassicalSymbol n V W m} (ha : a.IsElliptic)
    (e : CoordinateSpace n ≃L[ℝ] CoordinateSpace n) :
    (ClassicalSymbol.compContinuousLinearEquiv e a).IsElliptic := by
  rw [isElliptic_def, principal_compContinuousLinearEquiv, HomogeneousSymbol.isElliptic_iff]
  intro x ξ hξ
  rw [coefficient_compFrequency, coefficient_compPosition]
  exact HomogeneousSymbol.isElliptic_iff.1 (isElliptic_def.1 ha) _ _
    ((map_ne_zero_iff _ (e.symm.adjoint_bijective.1)).2 hξ)

end ClassicalSymbol

end TauCeti

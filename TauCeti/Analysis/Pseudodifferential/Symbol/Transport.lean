/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Quantization
import TauCeti.Analysis.InnerProductSpace.Adjoint
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Peetre

/-!
# Symbols under linear changes of coordinates

Let `A` be a linear automorphism of `ℝⁿ` and `y = A x` the new coordinates it defines. A covector
`ξ` at `x` has components `η = (A⁻¹)ᵀ ξ` in the coordinates `y`, so a symbol `a(x, ξ)` written in
the coordinates `y` is

`a_A(y, η) = a(A⁻¹ y, Aᵀ η)`,

the transport `TauCeti.Symbol.transport A a`. This is exactly the symbol of the operator `Op(a)`
written in the coordinates `y`: for linear changes of coordinates the Kohn–Nirenberg quantization
transforms with no lower-order correction, `Op(a) (u ∘ A) = (Op(a_A) u) ∘ A`
(`TauCeti.Symbol.quantizeSchwartzValue_transport`, from the general
`TauCeti.quantizeSchwartzValue_compCLMOfContinuousLinearEquiv`).

The transport preserves the order `m`. By the chain rule a derivative of `a_A` in a coordinate
direction is a linear combination of transported derivatives of `a` of the same kind:

`∂_{η_j} a_A = ∑ₖ (Aᵀ eⱼ)ₖ (∂_{ξ_k} a)_A` and `∂_{y_j} a_A = ∑ₖ (A⁻¹ eⱼ)ₖ (∂_{x_k} a)_A`

(`TauCeti.Symbol.frequencyDeriv_transport`, `TauCeti.Symbol.spatialDeriv_transport`), so by
induction every mixed derivative `∂_y^α ∂_η^β a_A (y, η)` is bounded by a multiple of
`⟨Aᵀ η⟩ ^ (m - |β|)`, which is comparable to `⟨η⟩ ^ (m - |β|)` since `Aᵀ` is invertible. The same
induction preserves estimates uniform in the position (`TauCeti.Symbol.IsUniform.transport`).

The transport is linear, functorial (`TauCeti.Symbol.transport_refl`,
`TauCeti.Symbol.transport_trans`), and commutes with the order inclusions and with composition of
symbols (`TauCeti.Symbol.inclusion_transport`, `TauCeti.Symbol.comp_transport`). It preserves
compact spatial support, moving the support by `A`, and smoothing symbols, with converses since
`transport A⁻¹` inverts `transport A`.

## Main declarations

* `TauCeti.Symbol.transport`: the symbol `a(A⁻¹ y, Aᵀ η)` in the coordinates `y = A x`.
* `TauCeti.Symbol.quantizeSchwartzValue_transport`: `Op(a_A) u (A x) = Op(a) (u ∘ A) (x)`.
* `TauCeti.Symbol.frequencyDeriv_transport`, `TauCeti.Symbol.spatialDeriv_transport`: the chain
  rule for frequency and position derivatives.
* `TauCeti.Symbol.isUniform_transport_iff`, `TauCeti.Symbol.hasCompactSpatialSupport_transport_iff`,
  `TauCeti.Symbol.isSmoothing_transport_iff`: the transport preserves and reflects uniform
  estimates, compact spatial support and smoothing.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1
  (pseudodifferential operators under changes of variables; for a linear change the asymptotic
  expansion of the transformed symbol reduces to its first term).
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, §8.
-/

public section

noncomputable section

open scoped ContDiff SchwartzMap

namespace TauCeti

namespace Symbol

variable {n : ℕ} {V W U : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] [NormedAddCommGroup U] [NormedSpace ℂ U] {m m' : ℝ}

/-! ### Derivatives after a linear substitution -/

section Substitution

variable (L₁ L₂ : CoordinateSpace n →L[ℝ] CoordinateSpace n)

/-- The frequency derivative of `(y, η) ↦ a(L₁ y, L₂ η)` along `eⱼ` is the coefficient of
`∑ₖ (L₂ eⱼ)ₖ ∂_{ξ_k} a` at `(L₁ y, L₂ η)`. -/
private theorem coordinateDeriv_coefficient_comp_snd (a : Symbol n V W m) (j : Fin n)
    (y ξ : CoordinateSpace n) :
    coordinateDeriv [j] (fun η ↦ a.coefficient (L₁ y, L₂ η)) ξ =
      (∑ k, (L₂ (EuclideanSpace.single j 1) k : ℂ) • frequencyDeriv k a).coefficient
        (L₁ y, L₂ ξ) := by
  have hd : DifferentiableAt ℝ (fun η ↦ a.coefficient (L₁ y, η)) (L₂ ξ) :=
    (a.contDiff_coefficient.comp (contDiff_prodMk_right (L₁ y))).differentiable (by simp) _
  have hcomp : (fun η ↦ a.coefficient (L₁ y, L₂ η)) = (fun η ↦ a.coefficient (L₁ y, η)) ∘ L₂ :=
    rfl
  rw [coordinateDeriv_cons, coordinateDeriv_nil, hcomp,
    (hd.hasFDerivAt.comp ξ L₂.hasFDerivAt).fderiv, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.apply_eq_sum_single, coefficient_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [coefficient_smul, Pi.smul_apply, fderiv_coefficient_slice_single, Complex.coe_smul]

/-- The position derivative of `(y, η) ↦ a(L₁ y, L₂ η)` along `eⱼ` is the coefficient of
`∑ₖ (L₁ eⱼ)ₖ ∂_{x_k} a` at `(L₁ y, L₂ η)`. -/
private theorem coordinateDeriv_coefficient_comp_fst (a : Symbol n V W m) (j : Fin n)
    (x η : CoordinateSpace n) :
    coordinateDeriv [j] (fun y ↦ a.coefficient (L₁ y, L₂ η)) x =
      (∑ k, (L₁ (EuclideanSpace.single j 1) k : ℂ) • spatialDeriv k a).coefficient
        (L₁ x, L₂ η) := by
  have hd : DifferentiableAt ℝ (fun y ↦ a.coefficient (y, L₂ η)) (L₁ x) :=
    (a.contDiff_coefficient.comp (contDiff_prodMk_left (L₂ η))).differentiable (by simp) _
  have hcomp : (fun y ↦ a.coefficient (L₁ y, L₂ η)) = (fun y ↦ a.coefficient (y, L₂ η)) ∘ L₁ :=
    rfl
  rw [coordinateDeriv_cons, coordinateDeriv_nil, hcomp,
    (hd.hasFDerivAt.comp x L₁.hasFDerivAt).fderiv, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.apply_eq_sum_single, coefficient_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [coefficient_smul, Pi.smul_apply, fderiv_coefficient_single, Complex.coe_smul]

/-- **Symbol estimates after a linear substitution.** Let `P` be a predicate on symbols that is
stable under the combinations `∑ₖ cₖ ∂_{x_k} a` and `∑ₖ cₖ ∂_{ξ_k} a`. If every symbol `a` with
`P a` satisfies `‖a(L₁ x, L₂ ξ)‖ ≤ C ⟨L₂ ξ⟩ ^ m` for `x ∈ K`, then so does every mixed derivative
`∂_x^α ∂_ξ^β` of `(x, ξ) ↦ a(L₁ x, L₂ ξ)`, with the weight `⟨L₂ ξ⟩ ^ (m - |β|)`.

Taking `P` trivial and `K` compact gives the local estimates, and taking for `P` the estimates
uniform in the position and `K = univ` gives uniform ones. -/
private theorem exists_norm_mixedDeriv_comp_le (P : ∀ {m : ℝ}, Symbol n V W m → Prop)
    (hPspatial : ∀ {m : ℝ} {a : Symbol n V W m}, P a → ∀ c : Fin n → ℂ,
      P (∑ k, c k • spatialDeriv k a))
    (hPfrequency : ∀ {m : ℝ} {a : Symbol n V W m}, P a → ∀ c : Fin n → ℂ,
      P (∑ k, c k • frequencyDeriv k a))
    {K : Set (CoordinateSpace n)}
    (hbound : ∀ {m : ℝ} (a : Symbol n V W m), P a → ∃ C, 0 ≤ C ∧ ∀ x ∈ K, ∀ ξ,
      ‖a.coefficient (L₁ x, L₂ ξ)‖ ≤ C * (1 + ‖L₂ ξ‖ ^ 2) ^ (m / 2))
    (a : Symbol n V W m) (ha : P a) (α β : List (Fin n)) :
    ∃ C, 0 ≤ C ∧ ∀ x ∈ K, ∀ ξ,
      ‖mixedDeriv α β (fun p ↦ a.coefficient (L₁ p.1, L₂ p.2)) x ξ‖ ≤
        C * (1 + ‖L₂ ξ‖ ^ 2) ^ ((m - β.length) / 2) := by
  obtain ⟨D, hD⟩ : ∃ D, α.length + β.length = D := ⟨_, rfl⟩
  induction D generalizing m α β with
  | zero =>
    obtain ⟨rfl, rfl⟩ : α = [] ∧ β = [] := by
      simpa [List.length_eq_zero_iff] using hD
    obtain ⟨C, hC0, hC⟩ := hbound a ha
    exact ⟨C, hC0, fun x hx ξ ↦ by simpa using hC x hx ξ⟩
  | succ D ih =>
    -- Peel off the derivative taken first: a frequency derivative if there is one, otherwise a
    -- position derivative, and rewrite it by the chain rule as a combination of derivatives of `a`.
    rcases List.eq_nil_or_concat' β with rfl | ⟨β', j, rfl⟩
    · rcases List.eq_nil_or_concat' α with rfl | ⟨α', j, rfl⟩
      · simp at hD
      · obtain ⟨C, hC0, hC⟩ := ih _
          (hPspatial ha fun k ↦ (L₁ (EuclideanSpace.single j 1) k : ℂ)) α' [] (by simpa using hD)
        refine ⟨C, hC0, fun x hx ξ ↦ ?_⟩
        have hsmooth : ContDiff ℝ ∞ fun p : CoordinateSpace n × CoordinateSpace n ↦
            a.coefficient (L₁ p.1, L₂ p.2) :=
          a.contDiff_coefficient.comp (L₁.prodMap L₂).contDiff
        have hfun : (fun q : CoordinateSpace n × CoordinateSpace n ↦
            coordinateDeriv [j] (fun y ↦ a.coefficient (L₁ y, L₂ q.2)) q.1) =
              fun q ↦ (∑ k, (L₁ (EuclideanSpace.single j 1) k : ℂ) •
                spatialDeriv k a).coefficient (L₁ q.1, L₂ q.2) :=
          funext fun q ↦ coordinateDeriv_coefficient_comp_fst L₁ L₂ a j q.1 q.2
        rw [← mixedDeriv_coordinateDeriv_fst hsmooth, hfun]
        exact hC x hx ξ
    · have hlen : α.length + β'.length = D := by
        simp only [List.length_append, List.length_singleton] at hD
        omega
      obtain ⟨C, hC0, hC⟩ := ih _
        (hPfrequency ha fun k ↦ (L₂ (EuclideanSpace.single j 1) k : ℂ)) α β' hlen
      refine ⟨C, hC0, fun x hx ξ ↦ ?_⟩
      have hfun : (fun q : CoordinateSpace n × CoordinateSpace n ↦
          coordinateDeriv [j] (fun η ↦ a.coefficient (L₁ q.1, L₂ η)) q.2) =
            fun q ↦ (∑ k, (L₂ (EuclideanSpace.single j 1) k : ℂ) •
              frequencyDeriv k a).coefficient (L₁ q.1, L₂ q.2) :=
        funext fun q ↦ coordinateDeriv_coefficient_comp_snd L₁ L₂ a j q.1 q.2
      have e : (m - 1 - β'.length) / 2 = (m - (β' ++ [j]).length) / 2 := by
        simp only [List.length_append, List.length_singleton, Nat.cast_add, Nat.cast_one]
        ring
      have h := hC x hx ξ
      rw [e] at h
      rw [← mixedDeriv_coordinateDeriv_snd, hfun]
      exact h

end Substitution

/-! ### The transport -/

section Transport

variable (A B : CoordinateSpace n ≃L[ℝ] CoordinateSpace n)

/-- A bound with the weight `⟨Aᵀ ξ⟩ ^ r` gives one with the weight `⟨ξ⟩ ^ r`, since `Aᵀ` is an
equivalence. -/
private theorem exists_le_mul_one_add_norm_sq_rpow_of_adjoint {K : Set (CoordinateSpace n)}
    {f : CoordinateSpace n → CoordinateSpace n → ℝ} {r : ℝ}
    (h : ∃ C, 0 ≤ C ∧ ∀ x ∈ K, ∀ ξ, f x ξ ≤ C * (1 + ‖ContinuousLinearMap.adjoint
      (A : CoordinateSpace n →L[ℝ] CoordinateSpace n) ξ‖ ^ 2) ^ (r / 2)) :
    ∃ C, 0 ≤ C ∧ ∀ x ∈ K, ∀ ξ, f x ξ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (r / 2) := by
  obtain ⟨C, hC0, hC⟩ := h
  obtain ⟨c, hc0, hc⟩ := A.adjointEquiv.exists_one_add_norm_apply_sq_rpow_le r
  refine ⟨C * c, mul_nonneg hC0 hc0, fun x hx ξ ↦ (hC x hx ξ).trans ?_⟩
  rw [mul_assoc, ← ContinuousLinearEquiv.adjointEquiv_apply]
  exact mul_le_mul_of_nonneg_left (hc ξ) hC0

/-- The **transport** of a symbol `a` along the linear change of coordinates `y = A x`: the symbol
`a_A(y, η) = a(A⁻¹ y, Aᵀ η)` of the same order, which is `a` written in the coordinates `y`.
Its quantization is `Op(a)` written in the coordinates `y`
(`TauCeti.Symbol.quantizeSchwartzValue_transport`). -/
def transport : Symbol n V W m →ₗ[ℂ] Symbol n V W m where
  toFun a :=
    { coefficient := fun p ↦ a.coefficient (A.symm p.1,
        ContinuousLinearMap.adjoint (A : CoordinateSpace n →L[ℝ] CoordinateSpace n) p.2)
      contDiff_coefficient := a.contDiff_coefficient.comp
        ((A.symm : CoordinateSpace n →L[ℝ] CoordinateSpace n).prodMap
          (ContinuousLinearMap.adjoint (A : CoordinateSpace n →L[ℝ] CoordinateSpace n))).contDiff
      exists_bound := fun K hK α β ↦ exists_le_mul_one_add_norm_sq_rpow_of_adjoint A <|
        exists_norm_mixedDeriv_comp_le
          (A.symm : CoordinateSpace n →L[ℝ] CoordinateSpace n)
          (ContinuousLinearMap.adjoint (A : CoordinateSpace n →L[ℝ] CoordinateSpace n))
          (fun _ ↦ True) (fun _ _ ↦ trivial) (fun _ _ ↦ trivial)
          (K := K) (fun a _ ↦ by
            obtain ⟨C, hC0, hC⟩ := a.exists_bound_coefficient _ (hK.image A.symm.continuous)
            exact ⟨C, hC0, fun x hx ξ ↦ hC _ (Set.mem_image_of_mem _ hx) _⟩) a trivial α β }
  map_add' _ _ := (rfl)
  map_smul' _ _ := (rfl)

/-- The coefficient of the transported symbol at `(y, η)` is `a(A⁻¹ y, Aᵀ η)`. -/
@[simp]
theorem coefficient_transport (a : Symbol n V W m) (p : CoordinateSpace n × CoordinateSpace n) :
    (transport A a).coefficient p = a.coefficient (A.symm p.1,
      ContinuousLinearMap.adjoint (A : CoordinateSpace n →L[ℝ] CoordinateSpace n) p.2) :=
  (rfl)

/-- Transport along the identity is the identity. -/
@[simp]
theorem transport_refl :
    transport (ContinuousLinearEquiv.refl ℝ (CoordinateSpace n)) =
      (LinearMap.id : Symbol n V W m →ₗ[ℂ] Symbol n V W m) := by
  ext a p
  simp [ContinuousLinearMap.adjoint_id]

/-- **Functoriality.** Transporting along `A` and then along `B` is transporting along `B ∘ A`. -/
theorem transport_trans (a : Symbol n V W m) :
    transport (A.trans B) a = transport B (transport A a) := by
  have hAB : ((A.trans B : CoordinateSpace n ≃L[ℝ] CoordinateSpace n) :
      CoordinateSpace n →L[ℝ] CoordinateSpace n) =
        (B : CoordinateSpace n →L[ℝ] CoordinateSpace n).comp
          (A : CoordinateSpace n →L[ℝ] CoordinateSpace n) := by
    ext1 x
    simp [ContinuousLinearEquiv.trans_apply]
  refine Symbol.ext (funext fun p ↦ ?_)
  simp only [coefficient_transport, hAB, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.symm_trans_apply]

/-- Transport along `A⁻¹` inverts transport along `A`. -/
@[simp]
theorem transport_symm_transport (a : Symbol n V W m) :
    transport A.symm (transport A a) = a := by
  rw [← transport_trans, ContinuousLinearEquiv.self_trans_symm, transport_refl, LinearMap.id_apply]

/-- Transport along `A` inverts transport along `A⁻¹`. -/
@[simp]
theorem transport_transport_symm (a : Symbol n V W m) :
    transport A (transport A.symm a) = a := by
  simpa using transport_symm_transport A.symm a

/-- Transport commutes with the inclusion of a symbol of order `m` into the symbols of order
`m' ≥ m`. -/
@[simp]
theorem inclusion_transport (h : m ≤ m') (a : Symbol n V W m) :
    inclusion h (transport A a) = transport A (inclusion h a) := by
  ext p
  simp [coefficient_inclusion]

/-- Transport commutes with the pointwise composition of symbols. -/
@[simp]
theorem comp_transport (b : Symbol n W U m') (a : Symbol n V W m) :
    (transport A b).comp (transport A a) = transport A (b.comp a) := by
  ext p
  simp [coefficient_comp]

/-- **The chain rule in the frequency.** The frequency derivative `∂_{η_j}` of the transported
symbol is `∑ₖ (Aᵀ eⱼ)ₖ (∂_{ξ_k} a)_A`. -/
theorem frequencyDeriv_transport (j : Fin n) (a : Symbol n V W m) :
    frequencyDeriv j (transport A a) = ∑ k,
      (ContinuousLinearMap.adjoint (A : CoordinateSpace n →L[ℝ] CoordinateSpace n)
        (EuclideanSpace.single j 1) k : ℂ) • transport A (frequencyDeriv k a) := by
  refine Symbol.ext (funext fun ⟨x, ξ⟩ ↦ ?_)
  have h := coordinateDeriv_coefficient_comp_snd
    (A.symm : CoordinateSpace n →L[ℝ] CoordinateSpace n)
    (ContinuousLinearMap.adjoint (A : CoordinateSpace n →L[ℝ] CoordinateSpace n)) a j x ξ
  simp only [ContinuousLinearEquiv.coe_coe] at h
  simp only [coefficient_frequencyDeriv, coefficient_transport]
  rw [h, coefficient_sum, coefficient_sum, Finset.sum_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [coefficient_smul, coefficient_smul, Pi.smul_apply, Pi.smul_apply, coefficient_transport]

/-- **The chain rule in the position.** The position derivative `∂_{y_j}` of the transported
symbol is `∑ₖ (A⁻¹ eⱼ)ₖ (∂_{x_k} a)_A`. -/
theorem spatialDeriv_transport (j : Fin n) (a : Symbol n V W m) :
    spatialDeriv j (transport A a) = ∑ k,
      (A.symm (EuclideanSpace.single j 1) k : ℂ) • transport A (spatialDeriv k a) := by
  refine Symbol.ext (funext fun ⟨x, ξ⟩ ↦ ?_)
  have h := coordinateDeriv_coefficient_comp_fst
    (A.symm : CoordinateSpace n →L[ℝ] CoordinateSpace n)
    (ContinuousLinearMap.adjoint (A : CoordinateSpace n →L[ℝ] CoordinateSpace n)) a j x ξ
  simp only [ContinuousLinearEquiv.coe_coe] at h
  simp only [coefficient_spatialDeriv, coefficient_transport]
  rw [h, coefficient_sum, coefficient_sum, Finset.sum_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [coefficient_smul, coefficient_smul, Pi.smul_apply, Pi.smul_apply, coefficient_transport]

/-- Transport preserves estimates uniform in the position. -/
theorem IsUniform.transport {a : Symbol n V W m} (ha : a.IsUniform) :
    (Symbol.transport A a).IsUniform := by
  refine isUniform_iff.2 fun α β ↦ ?_
  obtain ⟨C, hC0, hC⟩ := exists_le_mul_one_add_norm_sq_rpow_of_adjoint A <|
    exists_norm_mixedDeriv_comp_le
      (A.symm : CoordinateSpace n →L[ℝ] CoordinateSpace n)
      (ContinuousLinearMap.adjoint (A : CoordinateSpace n →L[ℝ] CoordinateSpace n))
      IsUniform
      (fun ha c ↦ IsUniform.sum fun k _ ↦ (ha.spatialDeriv k).smul (c k))
      (fun ha c ↦ IsUniform.sum fun k _ ↦ (ha.frequencyDeriv k).smul (c k))
      (K := Set.univ) (fun a ha ↦ by
        obtain ⟨C, hC0, hC⟩ := ha.exists_bound_coefficient
        exact ⟨C, hC0, fun x _ ξ ↦ hC _ _⟩) a ha α β
  exact ⟨C, hC0, fun x ξ ↦ hC x trivial ξ⟩

/-- A transported symbol has estimates uniform in the position exactly when the symbol does. -/
@[simp]
theorem isUniform_transport_iff {a : Symbol n V W m} :
    (transport A a).IsUniform ↔ a.IsUniform :=
  ⟨fun h ↦ by simpa using h.transport A.symm, fun h ↦ h.transport A⟩

/-- Transport preserves compact spatial support: the support moves by `A`. -/
theorem HasCompactSpatialSupport.transport {a : Symbol n V W m}
    (ha : a.HasCompactSpatialSupport) : (Symbol.transport A a).HasCompactSpatialSupport := by
  obtain ⟨K, hK, hKa⟩ := hasCompactSpatialSupport_iff.1 ha
  exact hasCompactSpatialSupport_iff.2 ⟨A '' K, hK.image A.continuous,
    fun y hy ξ ↦ hKa _ (fun hK' ↦ hy ⟨_, hK', by simp⟩) _⟩

/-- A transported symbol has compact spatial support exactly when the symbol does. -/
@[simp]
theorem hasCompactSpatialSupport_transport_iff {a : Symbol n V W m} :
    (transport A a).HasCompactSpatialSupport ↔ a.HasCompactSpatialSupport :=
  ⟨fun h ↦ by simpa using h.transport A.symm, fun h ↦ h.transport A⟩

/-- Transport preserves smoothing symbols. -/
theorem IsSmoothing.transport {a : Symbol n V W m} (ha : a.IsSmoothing) :
    (Symbol.transport A a).IsSmoothing := isSmoothing_iff.2 fun m' ↦ by
  obtain ⟨b, hb⟩ := isSmoothing_iff.1 ha m'
  exact ⟨Symbol.transport A b, by ext p; simp [hb]⟩

/-- A transported symbol is smoothing exactly when the symbol is. -/
@[simp]
theorem isSmoothing_transport_iff {a : Symbol n V W m} :
    (transport A a).IsSmoothing ↔ a.IsSmoothing :=
  ⟨fun h ↦ by simpa using h.transport A.symm, fun h ↦ h.transport A⟩

/-- **Quantization under a linear change of coordinates.** The quantization of the transported
symbol `a_A(y, η) = a(A⁻¹ y, Aᵀ η)` is `Op(a)` written in the coordinates `y = A x`:
`Op(a_A) u (A x) = Op(a) (u ∘ A) (x)` for every Schwartz function `u`. -/
theorem quantizeSchwartzValue_transport (a : Symbol n V W m) (u : 𝓢(CoordinateSpace n, V))
    (x : CoordinateSpace n) :
    quantizeSchwartzValue (transport A a).coefficient u (A x) =
      quantizeSchwartzValue a.coefficient (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A u) x :=
  (quantizeSchwartzValue_compCLMOfContinuousLinearEquiv A a.coefficient u x).symm

end Transport

end Symbol

end TauCeti

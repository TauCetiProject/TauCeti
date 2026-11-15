/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Adjoint
public import TauCeti.Analysis.Pseudodifferential.OutputSupport
public import TauCeti.Analysis.Pseudodifferential.SchwartzMapping
public import TauCeti.Analysis.Pseudodifferential.Symbol.Classical
import TauCeti.Analysis.Fourier.ChangeOfVariables
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Peetre

/-!
# Linear changes of coordinates for pseudodifferential operators

A linear isomorphism `A` of `ℝⁿ` acts on functions by the pullback `A^* u = u ∘ A`. Conjugating
the quantization of a symbol `a` by this pullback gives the quantization of the symbol

`(A^* a)(x, ξ) = a(A x, (A⁻¹)ᵀ ξ)`,

with no remainder: `A^* ∘ Op(a) ∘ (A^*)⁻¹ = Op(A^* a)`. The position moves by `A` and the
frequency, a covector, by the inverse transpose `(A⁻¹)ᵀ`, so `(x, ξ) ↦ (A x, (A⁻¹)ᵀ ξ)` is the
cotangent lift of `A`. This is the transformation law of symbols under changes of coordinates
in the exact case of linear changes, where the amplitude calculus of a nonlinear change of
coordinates contributes no lower-order terms. In particular the principal symbol of a classical
symbol transforms as a function on the cotangent bundle.

## Main declarations

* `TauCeti.quantizeSchwartzValue_comp_prodMap_adjoint`: for any coefficient `a` on a
  finite-dimensional inner product space, `Op(a(A ·, (A⁻¹)ᵀ ·)) u (x) = Op(a) (u ∘ A⁻¹) (A x)`.
  The proof is the linear change of variables in the Fourier transform,
  `ContinuousLinearEquiv.fourier_comp` and `ContinuousLinearEquiv.fourierInv_comp` from
  `TauCeti.Analysis.Fourier.ChangeOfVariables`.
* `TauCeti.Symbol.linearPullback`: the symbol `A^* a` of the same order, with
  `TauCeti.Symbol.quantizeSchwartzValue_linearPullback` and the operator identity
  `TauCeti.Symbol.quantizeUniformCLM_linearPullback` on Schwartz space. The pullback preserves
  uniform estimates, compact spatial support and smoothing symbols, in both directions; it is
  compatible with sums, the pointwise composition and the order inclusions, and it is functorial
  (`TauCeti.Symbol.linearPullback_linearPullback`).
* `TauCeti.Symbol.linearPullback_eq_self_iff`: a pseudodifferential operator commutes with the
  pullback along `A` exactly when its symbol is invariant under the cotangent lift of `A`.
* `TauCeti.ClassicalSymbol.linearPullback`: classical symbols pull back to classical symbols,
  termwise and compatibly with sums, composition and the order inclusions, so that the principal
  symbol transforms by the cotangent lift (`TauCeti.ClassicalSymbol.principal_linearPullback`)
  and ellipticity is preserved (`TauCeti.ClassicalSymbol.isElliptic_linearPullback_iff`).

The symbol estimates of `A^* a` come from `TauCeti.norm_mixedDeriv_comp_prodMap_le`, which bounds
the mixed derivatives of `a(L x, M ξ)` by those of `a` at `(L x, M ξ)`, and from the comparison
of the weights `⟨(A⁻¹)ᵀ ξ⟩` and `⟨ξ⟩` (`TauCeti.one_add_norm_sq_rpow_le_of_norm_le_mul`).

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Theorem 18.1.17.
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, (8.1)–(8.3).
-/

public section

noncomputable section

open MeasureTheory Real FourierTransform
open scoped ContDiff SchwartzMap InnerProduct

namespace TauCeti

/-! ### The quantization of a pulled-back coefficient -/

section Quantization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]

/-- **Quantization under a linear change of coordinates.** For a linear isomorphism `A`, the
quantization of the coefficient `a(A x, (A⁻¹)ᵀ ξ)` at `x` is the quantization of `a` applied to
`u ∘ A⁻¹`, evaluated at `A x`. -/
theorem quantizeSchwartzValue_comp_prodMap_adjoint (A : E ≃L[ℝ] E) (a : E × E → V →L[ℂ] W)
    (u : 𝓢(E, V)) (x : E) :
    quantizeSchwartzValue (a ∘ Prod.map A ((A.symm : E →L[ℝ] E)†)) u x =
      quantizeSchwartzValue a (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.symm u) (A x) := by
  -- `B = Aᵀ` is the adjoint of `A`, with inverse `(A⁻¹)ᵀ`.
  set B : E ≃L[ℝ] E := A.adjointEquiv
  set g : E → W := fun η ↦ a (A x, (2 * π) • B.symm η) (𝓕 u η)
  have hdet : |LinearMap.det (A.symm : E →ₗ[ℝ] E)|⁻¹ * |LinearMap.det (B : E →ₗ[ℝ] E)|⁻¹ = 1 := by
    have hB : (B : E →ₗ[ℝ] E) = LinearMap.adjoint (A : E →ₗ[ℝ] E) := by
      refine (LinearMap.eq_adjoint_iff _ _).2 fun y z ↦ ?_
      simp [B, ContinuousLinearMap.adjoint_inner_left]
    have hA : LinearMap.det (A : E →ₗ[ℝ] E) ≠ 0 := A.toLinearEquiv.isUnit_det'.ne_zero
    have hAs : LinearMap.det (A.symm : E →ₗ[ℝ] E) = (LinearMap.det (A : E →ₗ[ℝ] E))⁻¹ :=
      A.toLinearEquiv.det_coe_symm
    rw [hB, LinearMap.det_adjoint, star_trivial, hAs, abs_inv, inv_inv,
      mul_inv_cancel₀ (abs_ne_zero.2 hA)]
  -- The Fourier transform of `u ∘ A⁻¹` at `ζ` is `|det A⁻¹|⁻¹ 𝓕 u (Aᵀ ζ)`.
  have hF (ζ : E) : 𝓕 (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.symm u) ζ =
      |LinearMap.det (A.symm : E →ₗ[ℝ] E)|⁻¹ • 𝓕 u (B ζ) := by
    rw [SchwartzMap.fourier_coe, SchwartzMap.fourier_coe]
    rw [SchwartzMap.compCLMOfContinuousLinearEquiv_apply, A.symm.fourier_comp]
    simp [B]
  -- The integrand on the left is `g`, and the one on the right is a multiple of `g ∘ Aᵀ`.
  have hleft : (fun ζ ↦ (a ∘ Prod.map A ((A.symm : E →L[ℝ] E)†)) (x, (2 * π) • ζ) (𝓕 u ζ)) =
      g := by
    funext ζ
    simp [g, B]
  have hright : (fun ζ ↦ a (A x, (2 * π) • ζ)
      (𝓕 (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.symm u) ζ)) =
      fun ζ ↦ |LinearMap.det (A.symm : E →ₗ[ℝ] E)|⁻¹ • (g ∘ B) ζ := by
    funext ζ
    simp [g, hF]
  -- Constants come out of the inverse Fourier transform.
  have hsmul (c : ℝ) (f : E → W) (w : E) : 𝓕⁻ (fun v ↦ c • f v) w = c • 𝓕⁻ f w := by
    simp only [Real.fourierInv_eq, smul_comm _ c, integral_smul]
  have hBsymm : ((B.symm : E ≃L[ℝ] E) : E →L[ℝ] E) = (A.symm : E →L[ℝ] E)† := by
    ext1 y
    simp [B]
  rw [quantizeSchwartzValue_eq_fourierInv, quantizeSchwartzValue_eq_fourierInv, hleft, hright,
    hsmul, B.fourierInv_comp, smul_smul, hdet, one_smul]
  simp [hBsymm]

omit [MeasurableSpace E] [BorelSpace E] in
/-- `(A⁻¹)ᵀ` is inverted by `Aᵀ`, so `‖ξ‖ ≤ ‖Aᵀ‖ ‖(A⁻¹)ᵀ ξ‖`. -/
private theorem norm_le_norm_adjoint_mul_norm_adjoint_symm_apply (A : E ≃L[ℝ] E) (ξ : E) :
    ‖ξ‖ ≤ ‖(A : E →L[ℝ] E)†‖ * ‖((A.symm : E →L[ℝ] E)†) ξ‖ := by
  calc ‖ξ‖ = ‖((A : E →L[ℝ] E)†) (((A.symm : E →L[ℝ] E)†) ξ)‖ := by
        simpa using congrArg norm (A.symm.adjoint_symm_adjoint_apply ξ).symm
    _ ≤ _ := ContinuousLinearMap.le_opNorm _ _

end Quantization

namespace Symbol

variable {n : ℕ} {V W U : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] [NormedAddCommGroup U] [NormedSpace ℂ U] {m m' : ℝ}

/-! ### The pullback of a symbol -/

section Pullback

/-- The symbol estimates of `(x, ξ) ↦ a(A x, (A⁻¹)ᵀ ξ)` at the positions `x` with `A x ∈ T`, from
those of `a` at the positions in `T`. -/
private theorem exists_bound_comp_prodMap_adjoint (a : Symbol n V W m)
    (A : CoordinateSpace n ≃L[ℝ] CoordinateSpace n) (T : Set (CoordinateSpace n))
    (hT : ∀ α β : List (Fin n), ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ T, ∀ η,
      ‖mixedDeriv α β a.coefficient y η‖ ≤ C * (1 + ‖η‖ ^ 2) ^ ((m - β.length) / 2))
    (α β : List (Fin n)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, A x ∈ T → ∀ ξ,
      ‖mixedDeriv α β (fun p ↦ a.coefficient (A p.1, ((A.symm : _ →L[ℝ] _)†) p.2)) x ξ‖ ≤
        C * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2) := by
  set M : CoordinateSpace n →L[ℝ] CoordinateSpace n := (A.symm : _ →L[ℝ] _)†
  set L : CoordinateSpace n →L[ℝ] CoordinateSpace n :=
    (A : CoordinateSpace n →L[ℝ] CoordinateSpace n)
  -- `M = (A⁻¹)ᵀ` is inverted by `Aᵀ`, so `‖ξ‖` and `‖M ξ‖` are comparable.
  set c := max 1 (max ‖M‖ ‖(A : CoordinateSpace n →L[ℝ] CoordinateSpace n)†‖)
  have hc : 1 ≤ c := le_max_left _ _
  have hweight (t : ℝ) (ξ : CoordinateSpace n) :
      (1 + ‖M ξ‖ ^ 2) ^ (t / 2) ≤ c ^ |t| * (1 + ‖ξ‖ ^ 2) ^ (t / 2) := by
    refine one_add_norm_sq_rpow_le_of_norm_le_mul hc t
      ((M.le_opNorm ξ).trans (by gcongr; exact (le_max_left _ _).trans (le_max_right _ _))) ?_
    exact (norm_le_norm_adjoint_mul_norm_adjoint_symm_apply A ξ).trans
      (by gcongr; exact (le_max_right _ _).trans (le_max_right _ _))
  choose C hC0 hC using fun (r : Fin α.length → Fin n) (s : Fin β.length → Fin n) ↦
    hT (List.ofFn r) (List.ofFn s)
  have hC0' : 0 ≤ ∑ r, ∑ s, C r s :=
    Finset.sum_nonneg fun r _ ↦ Finset.sum_nonneg fun s _ ↦ hC0 r s
  refine ⟨‖L‖ ^ α.length * ‖M‖ ^ β.length * (∑ r, ∑ s, C r s) * c ^ |m - β.length|,
    by positivity, fun x hx ξ ↦ ?_⟩
  have hcomp : (fun p : CoordinateSpace n × CoordinateSpace n ↦ a.coefficient (A p.1, M p.2)) =
      a.coefficient ∘ L.prodMap M := by
    funext ⟨y, η⟩
    simp [L]
  rw [hcomp]
  refine (norm_mixedDeriv_comp_prodMap_le L M α β
    (a.contDiff_coefficient.of_le (by exact_mod_cast le_top)) x ξ).trans ?_
  calc ‖L‖ ^ α.length * ‖M‖ ^ β.length *
        ∑ r : Fin α.length → Fin n, ∑ s : Fin β.length → Fin n,
          ‖mixedDeriv (List.ofFn r) (List.ofFn s) a.coefficient (L x) (M ξ)‖
      ≤ ‖L‖ ^ α.length * ‖M‖ ^ β.length *
        ∑ r : Fin α.length → Fin n, ∑ s : Fin β.length → Fin n,
          C r s * (1 + ‖M ξ‖ ^ 2) ^ ((m - β.length) / 2) := by
        gcongr with r _ s _
        simpa using hC r s (L x) hx (M ξ)
    _ = ‖L‖ ^ α.length * ‖M‖ ^ β.length * (∑ r, ∑ s, C r s) *
          (1 + ‖M ξ‖ ^ 2) ^ ((m - β.length) / 2) := by
        simp only [Finset.sum_mul, mul_assoc]
    _ ≤ ‖L‖ ^ α.length * ‖M‖ ^ β.length * (∑ r, ∑ s, C r s) *
          (c ^ |m - β.length| * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2)) := by
        gcongr
        exact hweight _ ξ
    _ = _ := by ring

/-- The **pullback** of a symbol along a linear change of coordinates `A` of `ℝⁿ`: the symbol
`(A^* a)(x, ξ) = a(A x, (A⁻¹)ᵀ ξ)` of the same order, composed with the cotangent lift of `A`.
Its quantization is `A^* ∘ Op(a) ∘ (A^*)⁻¹`, where `A^* u = u ∘ A`
(`TauCeti.Symbol.quantizeSchwartzValue_linearPullback`). -/
def linearPullback (a : Symbol n V W m) (A : CoordinateSpace n ≃L[ℝ] CoordinateSpace n) :
    Symbol n V W m where
  coefficient p := a.coefficient (A p.1, ((A.symm : _ →L[ℝ] _)†) p.2)
  contDiff_coefficient :=
    a.contDiff_coefficient.comp ((A.contDiff.comp contDiff_fst).prodMk
      (((A.symm : CoordinateSpace n →L[ℝ] CoordinateSpace n)†).contDiff.comp contDiff_snd))
  exists_bound K hK α β := by
    obtain ⟨C, hC0, hC⟩ := exists_bound_comp_prodMap_adjoint a A (A '' K)
      (fun α β ↦ a.exists_bound _ (hK.image A.continuous) α β) α β
    exact ⟨C, hC0, fun x hx ξ ↦ hC x (Set.mem_image_of_mem _ hx) ξ⟩

@[simp]
theorem coefficient_linearPullback (a : Symbol n V W m)
    (A : CoordinateSpace n ≃L[ℝ] CoordinateSpace n) (x ξ : CoordinateSpace n) :
    (a.linearPullback A).coefficient (x, ξ) = a.coefficient (A x, ((A.symm : _ →L[ℝ] _)†) ξ) :=
  (rfl)

variable (A B : CoordinateSpace n ≃L[ℝ] CoordinateSpace n)

@[simp]
theorem linearPullback_refl (a : Symbol n V W m) :
    a.linearPullback (ContinuousLinearEquiv.refl ℝ _) = a := by
  ext1
  funext ⟨x, ξ⟩
  simp [ContinuousLinearMap.adjoint_id]

/-- Pulling back along `A`, then along `B`, is pulling back along `A ∘ B`. -/
@[simp]
theorem linearPullback_linearPullback (a : Symbol n V W m) :
    (a.linearPullback A).linearPullback B = a.linearPullback (B.trans A) := by
  ext1
  funext ⟨x, ξ⟩
  have h : (((B.trans A).symm : CoordinateSpace n ≃L[ℝ] CoordinateSpace n) :
      CoordinateSpace n →L[ℝ] CoordinateSpace n) =
      (B.symm : CoordinateSpace n →L[ℝ] CoordinateSpace n) ∘L (A.symm : _ →L[ℝ] _) := by
    ext1 y
    simp
  simp only [coefficient_linearPullback, h, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.trans_apply]

theorem linearPullback_linearPullback_symm (a : Symbol n V W m) :
    (a.linearPullback A).linearPullback A.symm = a := by
  simp

theorem linearPullback_symm_linearPullback (a : Symbol n V W m) :
    (a.linearPullback A.symm).linearPullback A = a := by
  simp

theorem linearPullback_injective :
    Function.Injective fun a : Symbol n V W m ↦ a.linearPullback A :=
  fun a b h ↦ by simpa using congrArg (fun c : Symbol n V W m ↦ c.linearPullback A.symm) h

@[simp]
theorem zero_linearPullback : (0 : Symbol n V W m).linearPullback A = 0 :=
  (rfl)

@[simp]
theorem add_linearPullback (a b : Symbol n V W m) :
    (a + b).linearPullback A = a.linearPullback A + b.linearPullback A :=
  (rfl)

@[simp]
theorem smul_linearPullback (c : ℂ) (a : Symbol n V W m) :
    (c • a).linearPullback A = c • a.linearPullback A :=
  (rfl)

@[simp]
theorem neg_linearPullback (a : Symbol n V W m) : (-a).linearPullback A = -a.linearPullback A :=
  (rfl)

@[simp]
theorem sub_linearPullback (a b : Symbol n V W m) :
    (a - b).linearPullback A = a.linearPullback A - b.linearPullback A :=
  Symbol.ext <| funext fun ⟨_, _⟩ ↦ by simp

@[simp]
theorem inclusion_linearPullback (h : m ≤ m') (a : Symbol n V W m) :
    (inclusion h a).linearPullback A = inclusion h (a.linearPullback A) :=
  Symbol.ext <| funext fun ⟨_, _⟩ ↦ by simp

/-- The pullback is compatible with the pointwise composition of symbols. -/
@[simp]
theorem comp_linearPullback (b : Symbol n W U m') (a : Symbol n V W m) :
    (b.comp a).linearPullback A = (b.linearPullback A).comp (a.linearPullback A) :=
  Symbol.ext <| funext fun ⟨_, _⟩ ↦ by simp

theorem IsUniform.linearPullback {a : Symbol n V W m} (ha : a.IsUniform) :
    (a.linearPullback A).IsUniform := isUniform_iff.2 fun α β ↦ by
  obtain ⟨C, hC0, hC⟩ := exists_bound_comp_prodMap_adjoint a A Set.univ
    (fun α β ↦ (isUniform_iff.1 ha α β).imp fun _ h ↦ ⟨h.1, fun y _ η ↦ h.2 y η⟩) α β
  exact ⟨C, hC0, fun x ξ ↦ hC x trivial ξ⟩

@[simp]
theorem isUniform_linearPullback_iff {a : Symbol n V W m} :
    (a.linearPullback A).IsUniform ↔ a.IsUniform :=
  ⟨fun h ↦ by simpa using h.linearPullback A.symm, fun h ↦ h.linearPullback A⟩

theorem HasCompactSpatialSupport.linearPullback {a : Symbol n V W m}
    (ha : a.HasCompactSpatialSupport) : (a.linearPullback A).HasCompactSpatialSupport := by
  obtain ⟨K, hK, hKa⟩ := hasCompactSpatialSupport_iff.1 ha
  refine hasCompactSpatialSupport_iff.2 ⟨A.symm '' K, hK.image A.symm.continuous,
    fun x hx ξ ↦ hKa _ (fun hAx ↦ hx ⟨A x, hAx, A.symm_apply_apply x⟩) _⟩

@[simp]
theorem hasCompactSpatialSupport_linearPullback_iff {a : Symbol n V W m} :
    (a.linearPullback A).HasCompactSpatialSupport ↔ a.HasCompactSpatialSupport :=
  ⟨fun h ↦ by simpa using h.linearPullback A.symm, fun h ↦ h.linearPullback A⟩

theorem IsSmoothing.linearPullback {a : Symbol n V W m} (ha : a.IsSmoothing) :
    (a.linearPullback A).IsSmoothing := isSmoothing_iff.2 fun m' ↦ by
  obtain ⟨b, hb⟩ := isSmoothing_iff.1 ha m'
  exact ⟨b.linearPullback A, by funext ⟨x, ξ⟩; simp [hb]⟩

@[simp]
theorem isSmoothing_linearPullback_iff {a : Symbol n V W m} :
    (a.linearPullback A).IsSmoothing ↔ a.IsSmoothing :=
  ⟨fun h ↦ by simpa using h.linearPullback A.symm, fun h ↦ h.linearPullback A⟩

end Pullback

/-! ### The quantization of the pullback -/

section Quantization

variable (A : CoordinateSpace n ≃L[ℝ] CoordinateSpace n)

/-- **Quantization of the pullback.** `Op(A^* a) u (x) = Op(a) (u ∘ A⁻¹) (A x)`, that is,
`Op(A^* a) = A^* ∘ Op(a) ∘ (A^*)⁻¹` with `A^* u = u ∘ A`. -/
theorem quantizeSchwartzValue_linearPullback (a : Symbol n V W m)
    (u : 𝓢(CoordinateSpace n, V)) (x : CoordinateSpace n) :
    quantizeSchwartzValue (a.linearPullback A).coefficient u x =
      quantizeSchwartzValue a.coefficient
        (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.symm u) (A x) :=
  quantizeSchwartzValue_comp_prodMap_adjoint A a.coefficient u x

/-- The quantization of `a` applied to `u ∘ A` is the pullback along `A` of the quantization of
the pullback of `a` along `A⁻¹`. -/
theorem quantizeSchwartzValue_compCLMOfContinuousLinearEquiv (a : Symbol n V W m)
    (u : 𝓢(CoordinateSpace n, V)) (x : CoordinateSpace n) :
    quantizeSchwartzValue a.coefficient (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A u) x =
      quantizeSchwartzValue (a.linearPullback A.symm).coefficient u (A x) := by
  simp [quantizeSchwartzValue_linearPullback]

/-- **Conjugation of the operator.** For a symbol with uniform estimates, the operator on Schwartz
space of the pullback `A^* a` is `A^* ∘ Op(a) ∘ (A^*)⁻¹`. -/
theorem quantizeUniformCLM_linearPullback {a : Symbol n V W m} (ha : a.IsUniform) :
    quantizeUniformCLM (a.linearPullback A) (ha.linearPullback A) =
      SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A ∘L quantizeUniformCLM a ha ∘L
        SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.symm := by
  ext u x
  simp [quantizeSchwartzValue_linearPullback]

/-- **Invariant operators have invariant symbols.** The quantization of `a` commutes with the
pullback `u ↦ u ∘ A` exactly when `a` is invariant under the cotangent lift of `A`,
`a(A x, (A⁻¹)ᵀ ξ) = a(x, ξ)`. -/
theorem linearPullback_eq_self_iff [CompleteSpace V] [CompleteSpace W] {a : Symbol n V W m} :
    a.linearPullback A = a ↔ ∀ (u : 𝓢(CoordinateSpace n, V)) (x : CoordinateSpace n),
      quantizeSchwartzValue a.coefficient (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A u) x =
        quantizeSchwartzValue a.coefficient u (A x) := by
  -- Both sides say that the pullback of `a` along `A⁻¹` is `a`.
  have key : a.linearPullback A = a ↔ a.linearPullback A.symm = a := by
    constructor <;> intro h
    · conv_lhs => rw [← h]
      simp
    · conv_lhs => rw [← h]
      simp
  rw [key]
  refine ⟨fun h u x ↦ ?_, fun h ↦ quantizeSchwartzValue_injective ?_⟩
  · rw [quantizeSchwartzValue_compCLMOfContinuousLinearEquiv, h]
  · funext u y
    simpa [quantizeSchwartzValue_compCLMOfContinuousLinearEquiv] using h u (A.symm y)

end Quantization

end Symbol

/-! ### Classical symbols -/

namespace ClassicalSymbol

open HomogeneousSymbol

variable {n : ℕ} {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] {m : ℝ} (A : CoordinateSpace n ≃L[ℝ] CoordinateSpace n)

/-- The cotangent lift of `A` on a homogeneous symbol: the position moves by `A` and the frequency
by `(A⁻¹)ᵀ`. -/
private abbrev homogeneousPullback {d : ℝ}
    (h : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W d) :
    HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W d :=
  (h.compPosition A A.contDiff).compFrequency A.symm.adjointEquiv

/-- The truncated expansions of the pulled-back symbol: since `(A⁻¹)ᵀ` and its inverse `Aᵀ` are
bounded, both `χ(ξ)` and `χ((A⁻¹)ᵀ ξ)` are `1` at all large frequencies, where the remainder
after `N` terms is the pullback of the remainder of `a`. -/
private theorem exists_remainder_linearPullback (a : ClassicalSymbol n V W m)
    (χ : FrequencyCutoff (CoordinateSpace n)) (N : ℕ) :
    ∃ r : Symbol n V W (m - N), ∀ p, r.coefficient p =
      (a.toSymbol.linearPullback A).coefficient p -
        ∑ j ∈ Finset.range N, χ p.2 • (homogeneousPullback A (a.term j)).coefficient p := by
  set M : CoordinateSpace n →L[ℝ] CoordinateSpace n := (A.symm : _ →L[ℝ] _)†
  set At : CoordinateSpace n →L[ℝ] CoordinateSpace n :=
    (A : CoordinateSpace n →L[ℝ] CoordinateSpace n)†
  have hM (ξ : CoordinateSpace n) : ‖ξ‖ ≤ ‖At‖ * ‖M ξ‖ :=
    norm_le_norm_adjoint_mul_norm_adjoint_symm_apply A ξ
  obtain ⟨r, hr⟩ := Symbol.exists_coefficient_eq_of_forall_le_norm
    (a.toSymbol.linearPullback A - ∑ j ∈ Finset.range N, Symbol.inclusion (by simp)
      (cutoffSymbol χ (homogeneousPullback A (a.term j)))).contDiff_coefficient
    ((a.remainder χ N).linearPullback A) (2 * (1 + ‖At‖)) fun x ξ hξ ↦ by
      have h2 : 2 ≤ ‖ξ‖ := by nlinarith [norm_nonneg At]
      have h2' : 2 ≤ ‖M ξ‖ := by nlinarith [norm_nonneg At, norm_nonneg (M ξ), hM ξ]
      simp [χ.apply_eq_one_of_two_le_norm h2, χ.apply_eq_one_of_two_le_norm h2', M]
  exact ⟨r, fun p ↦ by simp [hr]⟩

/-- The pullback of a classical symbol along a linear change of coordinates `A`: the full symbol
is `TauCeti.Symbol.linearPullback`, and each homogeneous term is pulled back in the same way,
`a_{m-j}(A x, (A⁻¹)ᵀ ξ)`. -/
def linearPullback (a : ClassicalSymbol n V W m) (A : CoordinateSpace n ≃L[ℝ] CoordinateSpace n) :
    ClassicalSymbol n V W m where
  toSymbol := a.toSymbol.linearPullback A
  term j := homogeneousPullback A (a.term j)
  exists_remainder' := ⟨default, exists_remainder_linearPullback A a default⟩

@[simp]
theorem toSymbol_linearPullback (a : ClassicalSymbol n V W m) :
    (a.linearPullback A).toSymbol = a.toSymbol.linearPullback A :=
  (rfl)

theorem term_linearPullback (a : ClassicalSymbol n V W m) (j : ℕ) :
    (a.linearPullback A).term j =
      ((a.term j).compPosition A A.contDiff).compFrequency A.symm.adjointEquiv :=
  (rfl)

@[simp]
theorem coefficient_term_linearPullback (a : ClassicalSymbol n V W m) (j : ℕ)
    (x ξ : CoordinateSpace n) :
    ((a.linearPullback A).term j).coefficient (x, ξ) =
      (a.term j).coefficient (A x, ((A.symm : _ →L[ℝ] _)†) ξ) := by
  simp [term_linearPullback]

/-- **The principal symbol transforms by the cotangent lift**:
`σ(A^* a)(x, ξ) = σ(a)(A x, (A⁻¹)ᵀ ξ)`. -/
@[simp]
theorem principal_linearPullback (a : ClassicalSymbol n V W m) :
    (a.linearPullback A).principal =
      (a.principal.compPosition A A.contDiff).compFrequency A.symm.adjointEquiv := by
  ext1
  funext ⟨x, ξ⟩
  simp [coefficient_principal]

@[simp]
theorem linearPullback_refl (a : ClassicalSymbol n V W m) :
    a.linearPullback (ContinuousLinearEquiv.refl ℝ _) = a :=
  ext <| by simp

@[simp]
theorem linearPullback_linearPullback (B : CoordinateSpace n ≃L[ℝ] CoordinateSpace n)
    (a : ClassicalSymbol n V W m) :
    (a.linearPullback A).linearPullback B = a.linearPullback (B.trans A) :=
  ext <| by simp

@[simp]
theorem zero_linearPullback : (0 : ClassicalSymbol n V W m).linearPullback A = 0 :=
  ext <| by simp

@[simp]
theorem add_linearPullback (a b : ClassicalSymbol n V W m) :
    (a + b).linearPullback A = a.linearPullback A + b.linearPullback A :=
  ext <| by simp

@[simp]
theorem smul_linearPullback (c : ℂ) (a : ClassicalSymbol n V W m) :
    (c • a).linearPullback A = c • a.linearPullback A :=
  ext <| by simp

@[simp]
theorem neg_linearPullback (a : ClassicalSymbol n V W m) :
    (-a).linearPullback A = -a.linearPullback A :=
  ext <| by simp

@[simp]
theorem sub_linearPullback (a b : ClassicalSymbol n V W m) :
    (a - b).linearPullback A = a.linearPullback A - b.linearPullback A :=
  ext <| by simp

@[simp]
theorem inclusion_linearPullback {m' : ℝ} (k : ℕ) (hk : m' = m - k)
    (a : ClassicalSymbol n V W m') :
    (inclusion k hk a).linearPullback A = inclusion k hk (a.linearPullback A) :=
  ext <| by simp

/-- The pullback is compatible with the composition of classical symbols. -/
@[simp]
theorem comp_linearPullback {U : Type*} [NormedAddCommGroup U] [NormedSpace ℂ U] {m' : ℝ}
    (b : ClassicalSymbol n W U m') (a : ClassicalSymbol n V W m) :
    (b.comp a).linearPullback A = (b.linearPullback A).comp (a.linearPullback A) :=
  ext <| by simp

/-- **Ellipticity is invariant under linear changes of coordinates.** -/
@[simp]
theorem isElliptic_linearPullback_iff {a : ClassicalSymbol n V W m} :
    (a.linearPullback A).IsElliptic ↔ a.IsElliptic := by
  rw [isElliptic_def, isElliptic_def, principal_linearPullback, isElliptic_compFrequency_iff]
  refine ⟨fun h ↦ HomogeneousSymbol.isElliptic_iff.2 fun x ξ hξ ↦ ?_, fun h ↦ h.compPosition _ _⟩
  simpa using HomogeneousSymbol.isElliptic_iff.1 h (A.symm x) ξ hξ

end ClassicalSymbol

end TauCeti

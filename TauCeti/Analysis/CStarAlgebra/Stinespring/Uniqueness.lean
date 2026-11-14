/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.PositiveLinearFunctional
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import TauCeti.Analysis.CStarAlgebra.GNS.Uniqueness
public import TauCeti.Analysis.CStarAlgebra.Stinespring.Basic
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Operator.Mul
import TauCeti.Analysis.CStarAlgebra.CStarMatrix

/-!
# Unitary uniqueness of minimal Stinespring dilations

Any minimal Stinespring dilation `(K, π, V)` of a completely positive map `φ : A →CP (H →L[ℂ] H)`
from a (possibly nonunital) C⋆-algebra `A` is unitarily equivalent to the canonical dilation
`(φ.Stinespring, φ.stinespringHom, φ.stinespringOp)` by a unique unitary
`U : φ.Stinespring ≃ₗᵢ[ℂ] K` (`CompletelyPositiveMap.stinespringEquiv`, generalizing the cyclic GNS
equivalence `PositiveLinearMap.gnsEquiv` of `TauCeti.Analysis.CStarAlgebra.GNS.Uniqueness`)
satisfying `U (φ.stinespringOp ξ) = V ξ` and `U (φ.stinespringHom a x) = π a (U x)`. Consequently,
any two minimal Stinespring dilations of `φ` are intertwined by a unique unitary preserving both
the `⋆`-representation and the compression operator.

Two concrete boundary checks illustrate the theorem and its minimality hypothesis:

* **Positive functionals (`H = ℂ`):** every positive linear functional `ω : A →ₚ[ℂ] ℂ` defines a
  completely positive map `ω.toCompletelyPositiveMap : A →CP ℂ` and hence
  `ω.toCompletelyPositiveMapCLM : A →CP (ℂ →L[ℂ] ℂ)`, `a ↦ ω a • 1`. When the domain is unital,
  the GNS triple `(ω.GNS, ω.gnsStarAlgHom, ContinuousLinearMap.toSpanSingleton ℂ ω.gnsVector)` is
  a minimal Stinespring dilation of `ω.toCompletelyPositiveMapCLM` with
  `‖toSpanSingleton ℂ ω.gnsVector‖ ^ 2 = ‖ω.gnsVector‖ ^ 2 = ‖ω‖`, hence unitarily equivalent to
  the canonical Stinespring space by `CompletelyPositiveMap.stinespringEquiv`.
* **Minimal vs. non-minimal dilations of `id_{B(H)}`:** `(H, id, 1)` is a minimal Stinespring
  dilation of `CompletelyPositiveMap.id (H →L[ℂ] H)`, whereas the doubled dilation
  `(WithLp 2 (H × H), id ⊕ id, ξ ↦ (ξ, 0))` satisfies the dilation identity and norm equality
  `‖V‖ ^ 2 = 1` on any nontrivial Hilbert space `H` yet has spanning closure `H × {0} ≠ H ⊕ H`.

## References

* W. F. Stinespring, *Positive functions on C⋆-algebras*, Proc. Amer. Math. Soc. 6 (1955),
  211–216, Theorem 1 and Theorem 3.
* B. Blackadar, *Operator Algebras: Theory of C⋆-Algebras and von Neumann Algebras*, II.6.9.7.
* V. Paulsen, *Completely Bounded Maps and Operator Algebras*, Proposition 4.2.
-/

public section

universe u v w w'

open Filter Topology TensorProduct
open scoped CStarAlgebra ComplexOrder InnerProductSpace NNReal

namespace CompletelyPositiveMap

section Lift

variable {A : Type u} [NonUnitalCStarAlgebra A]
  {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {K : Type w} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (π : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)) (V : H →L[ℂ] K)

/-- The algebraic evaluation map `A ⊗[ℂ] H →ₗ[ℂ] K` associated with a representation `π` and an
operator `V : H →L[ℂ] K`, sending `a ⊗ₜ ξ` to `π a (V ξ)`. -/
noncomputable def stinespringLiftLinear : (A ⊗[ℂ] H) →ₗ[ℂ] K :=
  TensorProduct.lift <| LinearMap.mk₂ ℂ (fun a ξ => π a (V ξ))
    (fun a b ξ => by simp)
    (fun c a ξ => by simp)
    (fun a ξ η => by simp)
    (fun c a ξ => by simp)

@[simp]
theorem stinespringLiftLinear_tmul (a : A) (ξ : H) :
    stinespringLiftLinear π V (a ⊗ₜ[ℂ] ξ) = π a (V ξ) := (rfl)

theorem range_stinespringLiftLinear :
    LinearMap.range (stinespringLiftLinear π V) =
      Submodule.span ℂ {x : K | ∃ (a : A) (ξ : H), x = π a (V ξ)} := by
  rw [← Submodule.map_top, ← TensorProduct.span_tmul_eq_top, Submodule.map_span]
  congr 1
  ext x
  simp [stinespringLiftLinear_tmul, eq_comm]

theorem denseRange_stinespringLiftLinear
    (hmin : (Submodule.span ℂ {x : K | ∃ (a : A) (ξ : H), x = π a (V ξ)}).topologicalClosure = ⊤) :
    DenseRange (stinespringLiftLinear π V) := by
  rw [DenseRange, ← LinearMap.coe_range, range_stinespringLiftLinear π V,
    Submodule.dense_iff_topologicalClosure_eq_top]
  exact hmin

/-- In any minimal dilation `(K, π, V)`, the `⋆`-representation `π` is automatically
nondegenerate. -/
theorem isNondegenerate_of_minimal
    (hmin : (Submodule.span ℂ {x : K | ∃ (a : A) (ξ : H), x = π a (V ξ)}).topologicalClosure = ⊤) :
    π.IsNondegenerate := by
  rw [NonUnitalStarAlgHom.isNondegenerate_iff_dense, Submodule.dense_iff_topologicalClosure_eq_top,
    eq_top_iff, ← hmin]
  refine Submodule.topologicalClosure_mono (Submodule.span_mono ?_)
  rintro _ ⟨a, ξ, rfl⟩
  exact Set.mem_iUnion.mpr ⟨a, V ξ, rfl⟩

end Lift

section NonUnital

variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {K : Type w} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (φ : A →CP (H →L[ℂ] H)) (π : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)) (V : H →L[ℂ] K)

/-- Any dilation `(K, π, V)` of `φ` induces the exact same inner product on `A ⊗[ℂ] H` as the
canonical Stinespring space; minimality is not needed. -/
theorem inner_stinespringLiftLinear_eq (hφ : ∀ a, φ a = V.adjoint.comp ((π a).comp V))
    (s t : A ⊗[ℂ] H) :
    ⟪stinespringLiftLinear π V s, stinespringLiftLinear π V t⟫_ℂ =
      ⟪φ.toStinespringLinearMap s, φ.toStinespringLinearMap t⟫_ℂ := by
  induction s using TensorProduct.inductionOn with
  | tmul a ξ =>
    induction t using TensorProduct.inductionOn with
    | tmul b η =>
      calc ⟪stinespringLiftLinear π V (a ⊗ₜ[ℂ] ξ), stinespringLiftLinear π V (b ⊗ₜ[ℂ] η)⟫_ℂ
          = ⟪π a (V ξ), π b (V η)⟫_ℂ := rfl
        _ = ⟪V ξ, (π a).adjoint (π b (V η))⟫_ℂ :=
            (ContinuousLinearMap.adjoint_inner_right (π a) (V ξ) (π b (V η))).symm
        _ = ⟪V ξ, π (star a * b) (V η)⟫_ℂ := by
            rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star, ← ContinuousLinearMap.comp_apply,
              ← ContinuousLinearMap.mul_def, ← map_mul]
        _ = ⟪ξ, (V.adjoint.comp ((π (star a * b)).comp V)) η⟫_ℂ := by
            rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
              ContinuousLinearMap.adjoint_inner_right]
        _ = ⟪ξ, φ (star a * b) η⟫_ℂ := by rw [hφ (star a * b)]
        _ = ⟪φ.toStinespringLinearMap (a ⊗ₜ[ℂ] ξ), φ.toStinespringLinearMap (b ⊗ₜ[ℂ] η)⟫_ℂ := by
            rw [toStinespringLinearMap_apply, toStinespringLinearMap_apply,
              UniformSpace.Completion.inner_coe, inner_toPreStinespring_tmul]
    | add t₁ t₂ ht₁ ht₂ =>
      rw [map_add, map_add, inner_add_right, inner_add_right, ht₁, ht₂]
  | add s₁ s₂ hs₁ hs₂ =>
    rw [map_add, map_add, inner_add_left, inner_add_left, hs₁, hs₂]

/-- Any dilation `(K, π, V)` of `φ` preserves the Stinespring norm on `A ⊗[ℂ] H`. -/
theorem norm_stinespringLiftLinear_eq (hφ : ∀ a, φ a = V.adjoint.comp ((π a).comp V))
    (t : A ⊗[ℂ] H) :
    ‖stinespringLiftLinear π V t‖ = ‖φ.toStinespringLinearMap t‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), ← RCLike.ofReal_inj (K := ℂ),
    RCLike.ofReal_pow, RCLike.ofReal_pow, ← inner_self_eq_norm_sq_to_K,
    ← inner_self_eq_norm_sq_to_K]
  exact φ.inner_stinespringLiftLinear_eq π V hφ t t

/-- The canonical unitary equivalence from `φ.Stinespring` to any minimal Stinespring dilation
`(K, π, V)` of `φ`, characterized on spanning vectors by `[a ⊗ ξ] ↦ π a (V ξ)`. -/
noncomputable def stinespringEquiv
    (hφ : ∀ a, φ a = V.adjoint.comp ((π a).comp V))
    (hmin : (Submodule.span ℂ {x : K | ∃ (a : A) (ξ : H), x = π a (V ξ)}).topologicalClosure = ⊤) :
    φ.Stinespring ≃ₗᵢ[ℂ] K :=
  (LinearEquiv.refl ℂ (A ⊗[ℂ] H)).extendOfIsometry
    φ.toStinespringLinearMap (stinespringLiftLinear π V)
    φ.denseRange_toStinespringLinearMap (denseRange_stinespringLiftLinear π V hmin)
    (φ.norm_stinespringLiftLinear_eq π V hφ)

theorem stinespringEquiv_toStinespringLinearMap
    (hφ : ∀ a, φ a = V.adjoint.comp ((π a).comp V))
    (hmin : (Submodule.span ℂ {x : K | ∃ (a : A) (ξ : H), x = π a (V ξ)}).topologicalClosure = ⊤)
    (t : A ⊗[ℂ] H) :
    φ.stinespringEquiv π V hφ hmin (φ.toStinespringLinearMap t) = stinespringLiftLinear π V t :=
  LinearEquiv.extendOfIsometry_eq _ _ _ _ _ _ t

@[simp]
theorem stinespringEquiv_apply_coe
    (hφ : ∀ a, φ a = V.adjoint.comp ((π a).comp V))
    (hmin : (Submodule.span ℂ {x : K | ∃ (a : A) (ξ : H), x = π a (V ξ)}).topologicalClosure = ⊤)
    (t : A ⊗[ℂ] H) :
    φ.stinespringEquiv π V hφ hmin (φ.toPreStinespring t : φ.Stinespring) =
      stinespringLiftLinear π V t := by
  rw [← toStinespringLinearMap_apply]
  exact φ.stinespringEquiv_toStinespringLinearMap π V hφ hmin t

theorem stinespringEquiv_toStinespring
    (hφ : ∀ a, φ a = V.adjoint.comp ((π a).comp V))
    (hmin : (Submodule.span ℂ {x : K | ∃ (a : A) (ξ : H), x = π a (V ξ)}).topologicalClosure = ⊤)
    (a : A) (ξ : H) :
    φ.stinespringEquiv π V hφ hmin (φ.toStinespring a ξ) = π a (V ξ) := by
  simp

@[simp]
theorem stinespringEquiv_intertwines
    (hφ : ∀ a, φ a = V.adjoint.comp ((π a).comp V))
    (hmin : (Submodule.span ℂ {x : K | ∃ (a : A) (ξ : H), x = π a (V ξ)}).topologicalClosure = ⊤)
    (a : A) (x : φ.Stinespring) :
    φ.stinespringEquiv π V hφ hmin (φ.stinespringHom a x) =
      π a (φ.stinespringEquiv π V hφ hmin x) := by
  let U := φ.stinespringEquiv π V hφ hmin
  refine φ.denseRange_toStinespringLinearMap.induction_on x ?_ fun t => ?_
  · exact isClosed_eq (U.continuous.comp (φ.stinespringHom a).continuous)
      ((π a).continuous.comp U.continuous)
  · induction t using TensorProduct.inductionOn with
    | tmul b ξ =>
      have hbt : φ.toStinespringLinearMap (b ⊗ₜ[ℂ] ξ) = φ.toStinespring b ξ := by simp
      rw [hbt, stinespringHom_toStinespring, stinespringEquiv_toStinespring,
        stinespringEquiv_toStinespring, map_mul, ContinuousLinearMap.mul_def,
        ContinuousLinearMap.comp_apply]
    | add s₁ s₂ hs₁ hs₂ =>
      rw [map_add, map_add, map_add, hs₁, hs₂, ← map_add, ← map_add]

@[simp]
theorem stinespringEquiv_stinespringOp
    (hφ : ∀ a, φ a = V.adjoint.comp ((π a).comp V))
    (hmin : (Submodule.span ℂ {x : K | ∃ (a : A) (ξ : H), x = π a (V ξ)}).topologicalClosure = ⊤)
    (ξ : H) :
    φ.stinespringEquiv π V hφ hmin (φ.stinespringOp ξ) = V ξ := by
  let U := φ.stinespringEquiv π V hφ hmin
  have hl := CStarAlgebra.increasingApproximateUnit A
  have := hl.neBot
  have h₁ : Tendsto (fun e => U (φ.toStinespring e ξ)) (CStarAlgebra.approximateUnit A)
      (𝓝 (U (φ.stinespringOp ξ))) :=
    (U.continuous.tendsto _).comp (φ.tendsto_toStinespring_approximateUnit ξ)
  have h₂ : Tendsto (fun e => π e (V ξ)) (CStarAlgebra.approximateUnit A) (𝓝 (V ξ)) :=
    (NonUnitalStarAlgHom.isNondegenerate_iff_tendsto hl).mp
      (isNondegenerate_of_minimal π V hmin) (V ξ)
  exact tendsto_nhds_unique h₁ (by simpa only [U, stinespringEquiv_toStinespring] using h₂)

theorem stinespringEquiv_symm_apply
    (hφ : ∀ a, φ a = V.adjoint.comp ((π a).comp V))
    (hmin : (Submodule.span ℂ {x : K | ∃ (a : A) (ξ : H), x = π a (V ξ)}).topologicalClosure = ⊤)
    (a : A) (ξ : H) :
    (φ.stinespringEquiv π V hφ hmin).symm (π a (V ξ)) = φ.toStinespring a ξ := by
  apply (φ.stinespringEquiv π V hφ hmin).injective
  simp

@[simp]
theorem stinespringEquiv_symm_intertwines
    (hφ : ∀ a, φ a = V.adjoint.comp ((π a).comp V))
    (hmin : (Submodule.span ℂ {x : K | ∃ (a : A) (ξ : H), x = π a (V ξ)}).topologicalClosure = ⊤)
    (a : A) (y : K) :
    (φ.stinespringEquiv π V hφ hmin).symm (π a y) =
      φ.stinespringHom a ((φ.stinespringEquiv π V hφ hmin).symm y) := by
  apply (φ.stinespringEquiv π V hφ hmin).injective
  simp

@[simp]
theorem stinespringEquiv_symm_apply_op
    (hφ : ∀ a, φ a = V.adjoint.comp ((π a).comp V))
    (hmin : (Submodule.span ℂ {x : K | ∃ (a : A) (ξ : H), x = π a (V ξ)}).topologicalClosure = ⊤)
    (ξ : H) :
    (φ.stinespringEquiv π V hφ hmin).symm (V ξ) = φ.stinespringOp ξ := by
  apply (φ.stinespringEquiv π V hφ hmin).injective
  simp

/-- Any unitary `U : φ.Stinespring ≃ₗᵢ[ℂ] K` sending `φ.stinespringOp` to `V` and intertwining
`φ.stinespringHom` with `π` equals `φ.stinespringEquiv`. -/
theorem stinespringEquiv_unique
    (hφ : ∀ a, φ a = V.adjoint.comp ((π a).comp V))
    (hmin : (Submodule.span ℂ {x : K | ∃ (a : A) (ξ : H), x = π a (V ξ)}).topologicalClosure = ⊤)
    (U : φ.Stinespring ≃ₗᵢ[ℂ] K)
    (hV : ∀ ξ, U (φ.stinespringOp ξ) = V ξ)
    (hπ : ∀ a x, U (φ.stinespringHom a x) = π a (U x)) :
    U = φ.stinespringEquiv π V hφ hmin := by
  ext x
  refine congrFun (φ.denseRange_toStinespringLinearMap.equalizer U.continuous
    (φ.stinespringEquiv π V hφ hmin).continuous ?_) x
  funext t
  induction t using TensorProduct.inductionOn with
  | tmul a ξ =>
    have hbt : φ.toStinespringLinearMap (a ⊗ₜ[ℂ] ξ) = φ.stinespringHom a (φ.stinespringOp ξ) := by
      rw [toStinespringLinearMap_apply, ← toStinespring_apply,
        ← φ.stinespringHom_apply_stinespringOp]
    rw [Function.comp_apply, Function.comp_apply, hbt, hπ, hV,
      φ.stinespringHom_apply_stinespringOp, φ.stinespringEquiv_toStinespring]
  | add s₁ s₂ hs₁ hs₂ =>
    simp only [Function.comp_apply, map_add] at hs₁ hs₂ ⊢
    rw [hs₁, hs₂]

/-- Existence and uniqueness of a unitary intertwiner from the canonical Stinespring dilation to
any minimal Stinespring dilation `(K, π, V)` of `φ`. -/
theorem existsUnique_stinespringEquiv
    (hφ : ∀ a, φ a = V.adjoint.comp ((π a).comp V))
    (hmin : (Submodule.span ℂ {x : K | ∃ (a : A) (ξ : H), x = π a (V ξ)}).topologicalClosure = ⊤) :
    ∃! U : φ.Stinespring ≃ₗᵢ[ℂ] K,
      (∀ ξ, U (φ.stinespringOp ξ) = V ξ) ∧
      ∀ (a : A) (x : φ.Stinespring), U (φ.stinespringHom a x) = π a (U x) :=
  ⟨φ.stinespringEquiv π V hφ hmin,
    ⟨φ.stinespringEquiv_stinespringOp π V hφ hmin, φ.stinespringEquiv_intertwines π V hφ hmin⟩,
    fun U ⟨hV, hπ⟩ => φ.stinespringEquiv_unique π V hφ hmin U hV hπ⟩

/-- Any two minimal Stinespring dilations `(K₁, π₁, V₁)` and `(K₂, π₂, V₂)` of `φ` are
intertwined by a unique unitary preserving both `π` and `V`. -/
theorem existsUnique_unitary_of_minimal
    {K₂ : Type w'} [NormedAddCommGroup K₂] [InnerProductSpace ℂ K₂] [CompleteSpace K₂]
    (π₂ : A →⋆ₙₐ[ℂ] (K₂ →L[ℂ] K₂)) (V₂ : H →L[ℂ] K₂)
    (hφ₁ : ∀ a, φ a = V.adjoint.comp ((π a).comp V))
    (hmin₁ :
      (Submodule.span ℂ {x : K | ∃ (a : A) (ξ : H), x = π a (V ξ)}).topologicalClosure = ⊤)
    (hφ₂ : ∀ a, φ a = V₂.adjoint.comp ((π₂ a).comp V₂))
    (hmin₂ :
      (Submodule.span ℂ {x : K₂ | ∃ (a : A) (ξ : H), x = π₂ a (V₂ ξ)}).topologicalClosure = ⊤) :
    ∃! U : K ≃ₗᵢ[ℂ] K₂,
      (∀ ξ, U (V ξ) = V₂ ξ) ∧ ∀ (a : A) (x : K), U (π a x) = π₂ a (U x) := by
  let U₁ := φ.stinespringEquiv π V hφ₁ hmin₁
  let U₂ := φ.stinespringEquiv π₂ V₂ hφ₂ hmin₂
  refine ⟨U₁.symm.trans U₂, ⟨fun ξ => ?_, fun a x => ?_⟩, fun U ⟨hUV, hUπ⟩ => ?_⟩
  · simp [U₁, U₂]
  · simp [U₁, U₂]
  · have hcomp : U₁.trans U = U₂ := by
      refine φ.stinespringEquiv_unique π₂ V₂ hφ₂ hmin₂ (U₁.trans U) (fun ξ => ?_) (fun a x => ?_)
      · simp [U₁, hUV]
      · simp [U₁, hUπ]
    ext x
    have hx := LinearIsometryEquiv.congr_fun hcomp (U₁.symm x)
    simpa [U₁] using hx

/-- In any minimal Stinespring dilation `(K, π, V)` of `φ`, `‖V‖ ^ 2 = ‖φ‖`. -/
theorem norm_op_sq_of_minimal
    (hφ : ∀ a, φ a = V.adjoint.comp ((π a).comp V))
    (hmin : (Submodule.span ℂ {x : K | ∃ (a : A) (ξ : H), x = π a (V ξ)}).topologicalClosure = ⊤) :
    ‖V‖ ^ 2 = ‖φ.toContinuousLinearMap‖ := by
  let U := φ.stinespringEquiv π V hφ hmin
  have hV : V = U.toLinearIsometry.toContinuousLinearMap.comp φ.stinespringOp := by
    ext ξ
    exact (φ.stinespringEquiv_stinespringOp π V hφ hmin ξ).symm
  have hnorm : ‖V‖ = ‖φ.stinespringOp‖ := by
    rw [hV]
    exact U.toLinearIsometry.norm_toContinuousLinearMap_comp
  rw [hnorm, φ.norm_stinespringOp_sq]

end NonUnital

section Unital

variable {D : Type u} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
  {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {K : Type w} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (φ : D →CP (H →L[ℂ] H)) (π : D →⋆ₐ[ℂ] (K →L[ℂ] K)) (V : H →L[ℂ] K)

/-- Unital form of `CompletelyPositiveMap.existsUnique_stinespringEquiv`: any minimal unital
Stinespring dilation `(K, π, V)` is intertwined with `(φ.Stinespring, φ.stinespringStarAlgHom,
φ.stinespringOp)` by a unique unitary. -/
theorem existsUnique_stinespringEquiv_unital
    (hφ : ∀ a, φ a = V.adjoint.comp ((π a).comp V))
    (hmin : (Submodule.span ℂ {x : K | ∃ (a : D) (ξ : H), x = π a (V ξ)}).topologicalClosure = ⊤) :
    ∃! U : φ.Stinespring ≃ₗᵢ[ℂ] K,
      (∀ ξ, U (φ.stinespringOp ξ) = V ξ) ∧
      ∀ (a : D) (x : φ.Stinespring), U (φ.stinespringStarAlgHom a x) = π a (U x) := by
  simpa only [coe_stinespringStarAlgHom, StarAlgHom.coe_toNonUnitalStarAlgHom] using
    φ.existsUnique_stinespringEquiv π.toNonUnitalStarAlgHom V hφ hmin

/-- Unital form of `CompletelyPositiveMap.existsUnique_unitary_of_minimal`. -/
theorem existsUnique_unitary_of_minimal_unital
    {K₂ : Type w'} [NormedAddCommGroup K₂] [InnerProductSpace ℂ K₂] [CompleteSpace K₂]
    (π₂ : D →⋆ₐ[ℂ] (K₂ →L[ℂ] K₂)) (V₂ : H →L[ℂ] K₂)
    (hφ₁ : ∀ a, φ a = V.adjoint.comp ((π a).comp V))
    (hmin₁ :
      (Submodule.span ℂ {x : K | ∃ (a : D) (ξ : H), x = π a (V ξ)}).topologicalClosure = ⊤)
    (hφ₂ : ∀ a, φ a = V₂.adjoint.comp ((π₂ a).comp V₂))
    (hmin₂ :
      (Submodule.span ℂ {x : K₂ | ∃ (a : D) (ξ : H), x = π₂ a (V₂ ξ)}).topologicalClosure = ⊤) :
    ∃! U : K ≃ₗᵢ[ℂ] K₂,
      (∀ ξ, U (V ξ) = V₂ ξ) ∧ ∀ (a : D) (x : K), U (π a x) = π₂ a (U x) := by
  simpa only [StarAlgHom.coe_toNonUnitalStarAlgHom] using
    φ.existsUnique_unitary_of_minimal π.toNonUnitalStarAlgHom V π₂.toNonUnitalStarAlgHom V₂
      hφ₁ hmin₁ hφ₂ hmin₂

end Unital

end CompletelyPositiveMap

namespace PositiveLinearMap

section NonUnital

variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- Every positive linear functional `ω : A →ₚ[ℂ] ℂ` on a (possibly nonunital) C⋆-algebra is
completely positive (Stinespring 1955, Theorem 3). -/
noncomputable def toCompletelyPositiveMap (ω : A →ₚ[ℂ] ℂ) : A →CP ℂ where
  toLinearMap := ω.toLinearMap
  map_cstarMatrix_nonneg' k M hM := by
    obtain ⟨R, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hM
    refine CStarMatrix.nonneg_iff_forall_sum_nonneg.mpr fun z => ?_
    have hsum :
        (∑ i, ∑ j, star (z i) * (star R * R).map ω.toLinearMap i j * z j) =
          ∑ l, ω (star (∑ i, z i • R l i) * ∑ j, z j • R l j) := by
      have hLHS :
          (∑ i, ∑ j, star (z i) * (star R * R).map ω.toLinearMap i j * z j) =
            ∑ l, ∑ i, ∑ j, (star (z i) * z j) * ω (star (R l i) * R l j) := by
        calc (∑ i, ∑ j, star (z i) * (star R * R).map ω.toLinearMap i j * z j)
            = ∑ i, ∑ j, ∑ l, (star (z i) * z j) * ω (star (R l i) * R l j) := by
                refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
                simp only [CStarMatrix.map_apply, PositiveLinearMap.coe_toLinearMap,
                  CStarMatrix.mul_apply, CStarMatrix.star_apply, map_sum, Finset.mul_sum,
                  Finset.sum_mul]
                exact Finset.sum_congr rfl fun l _ => by ring
          _ = ∑ i, ∑ l, ∑ j, (star (z i) * z j) * ω (star (R l i) * R l j) :=
                Finset.sum_congr rfl fun _ _ => Finset.sum_comm
          _ = ∑ l, ∑ i, ∑ j, (star (z i) * z j) * ω (star (R l i) * R l j) := Finset.sum_comm
      rw [hLHS]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [star_sum, Finset.sum_mul, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [star_smul, smul_mul_assoc, mul_smul_comm, map_smul, smul_eq_mul]
      ring
    rw [hsum]
    exact Finset.sum_nonneg fun l _ => map_nonneg ω (star_mul_self_nonneg _)

@[simp]
theorem toCompletelyPositiveMap_apply (ω : A →ₚ[ℂ] ℂ) (a : A) :
    ω.toCompletelyPositiveMap a = ω a := (rfl)

/-- A positive linear functional `ω : A →ₚ[ℂ] ℂ` viewed as a completely positive map
`A →CP (ℂ →L[ℂ] ℂ)` via `a ↦ ω a • 1`. -/
noncomputable def toCompletelyPositiveMapCLM (ω : A →ₚ[ℂ] ℂ) : A →CP (ℂ →L[ℂ] ℂ) :=
  CompletelyPositiveMap.comp
    (CompletelyPositiveMapClass.toCompletelyPositiveLinearMap (StarAlgHom.ofId ℂ (ℂ →L[ℂ] ℂ)))
    ω.toCompletelyPositiveMap

@[simp]
theorem toCompletelyPositiveMapCLM_apply (ω : A →ₚ[ℂ] ℂ) (a : A) :
    ω.toCompletelyPositiveMapCLM a = ω a • (1 : ℂ →L[ℂ] ℂ) := by
  rw [toCompletelyPositiveMapCLM, CompletelyPositiveMap.comp_apply, toCompletelyPositiveMap_apply]
  exact (StarAlgHom.ofId_apply ℂ (ℂ →L[ℂ] ℂ) (ω a)).trans
    (Algebra.algebraMap_eq_smul_one (ω a))

end NonUnital

section Unital

variable {D : Type u} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] (ω : D →ₚ[ℂ] ℂ)

/-- The GNS triple `(ω.GNS, ω.gnsStarAlgHom, toSpanSingleton ℂ ω.gnsVector)` satisfies the
Stinespring dilation identity for `ω.toCompletelyPositiveMapCLM`. -/
theorem gns_dilation_eq (a : D) :
    ω.toCompletelyPositiveMapCLM a =
      (ContinuousLinearMap.toSpanSingleton ℂ ω.gnsVector).adjoint.comp
        ((ω.gnsStarAlgHom a).comp (ContinuousLinearMap.toSpanSingleton ℂ ω.gnsVector)) := by
  refine ContinuousLinearMap.ext fun z => ?_
  simp [ContinuousLinearMap.adjoint_toSpanSingleton, innerSL_apply_apply,
    gnsStarAlgHom_apply, gnsNonUnitalStarAlgHom_apply_gnsVector, mul_comm]

/-- The GNS triple `(ω.GNS, ω.gnsStarAlgHom, toSpanSingleton ℂ ω.gnsVector)` is minimal as a
Stinespring dilation. -/
theorem gns_dilation_minimal :
    (Submodule.span ℂ {x : ω.GNS | ∃ (a : D) (z : ℂ),
      x = ω.gnsStarAlgHom a (ContinuousLinearMap.toSpanSingleton ℂ ω.gnsVector z)}
      ).topologicalClosure = ⊤ := by
  rw [← Submodule.dense_iff_topologicalClosure_eq_top]
  refine ω.denseRange_gnsStarAlgHom_gnsVector.mono ?_
  rintro _ ⟨a, rfl⟩
  exact Submodule.subset_span ⟨a, 1, by simp⟩

/-- The canonical Stinespring dilation of a positive functional `ω : D →ₚ[ℂ] ℂ` (`H = ℂ`) is
unitarily equivalent to its GNS representation. -/
noncomputable def gnsStinespringEquiv :
    ω.toCompletelyPositiveMapCLM.Stinespring ≃ₗᵢ[ℂ] ω.GNS :=
  ω.toCompletelyPositiveMapCLM.stinespringEquiv ω.gnsStarAlgHom.toNonUnitalStarAlgHom
    (ContinuousLinearMap.toSpanSingleton ℂ ω.gnsVector) ω.gns_dilation_eq ω.gns_dilation_minimal

-- Rewrite before `coe_stinespringStarAlgHom` replaces `stinespringStarAlgHom` with
-- `stinespringHom`.
@[simp↓]
theorem gnsStinespringEquiv_intertwines (a : D)
    (x : ω.toCompletelyPositiveMapCLM.Stinespring) :
    ω.gnsStinespringEquiv (ω.toCompletelyPositiveMapCLM.stinespringStarAlgHom a x) =
      ω.gnsStarAlgHom a (ω.gnsStinespringEquiv x) := by
  simpa only [gnsStinespringEquiv, CompletelyPositiveMap.coe_stinespringStarAlgHom,
    StarAlgHom.coe_toNonUnitalStarAlgHom] using
    ω.toCompletelyPositiveMapCLM.stinespringEquiv_intertwines
      ω.gnsStarAlgHom.toNonUnitalStarAlgHom (ContinuousLinearMap.toSpanSingleton ℂ ω.gnsVector)
      ω.gns_dilation_eq ω.gns_dilation_minimal a x

@[simp]
theorem gnsStinespringEquiv_stinespringOp (z : ℂ) :
    ω.gnsStinespringEquiv (ω.toCompletelyPositiveMapCLM.stinespringOp z) = z • ω.gnsVector :=
  ω.toCompletelyPositiveMapCLM.stinespringEquiv_stinespringOp
    ω.gnsStarAlgHom.toNonUnitalStarAlgHom (ContinuousLinearMap.toSpanSingleton ℂ ω.gnsVector)
    ω.gns_dilation_eq ω.gns_dilation_minimal z

/-- The squared norm of the GNS cyclic vector of `ω : D →ₚ[ℂ] ℂ` equals the operator norm of `ω`. -/
theorem norm_gnsVector_sq_eq_opNorm :
    ‖ω.gnsVector‖ ^ 2 = ‖(PositiveContinuousLinearMap.ofClass (R := ℂ) ω : D →L[ℂ] ℂ)‖ := by
  let f : D →P[ℂ] ℂ := PositiveContinuousLinearMap.ofClass (R := ℂ) ω
  have hf1 : (‖(f : D →L[ℂ] ℂ)‖ : ℂ) = ω 1 := by
    simpa only [f, PositiveContinuousLinearMap.coe_ofClass] using f.ofReal_opNorm_eq_map_one
  have hsq : ((‖ω.gnsVector‖ ^ 2 : ℝ) : ℂ) = ω 1 := by
    simpa only [Complex.ofReal_pow] using ω.norm_gnsVector_sq
  exact Complex.ofReal_inj.mp (hsq.trans hf1.symm)

/-- In the GNS model of Stinespring dilation for `ω : D →ₚ[ℂ] ℂ`, the squared operator norm of the
compression `toSpanSingleton ℂ ω.gnsVector` equals the operator norm of `ω`. -/
theorem norm_toSpanSingleton_gnsVector_sq :
    ‖ContinuousLinearMap.toSpanSingleton ℂ ω.gnsVector‖ ^ 2 =
      ‖(PositiveContinuousLinearMap.ofClass (R := ℂ) ω : D →L[ℂ] ℂ)‖ := by
  have hV : ‖ContinuousLinearMap.toSpanSingleton ℂ ω.gnsVector‖ = ‖ω.gnsVector‖ := by
    simpa only [ContinuousLinearMap.toSpanSingletonLIE_apply] using
      (ContinuousLinearMap.toSpanSingletonLIE ℂ ω.GNS).norm_map ω.gnsVector
  rw [hV, ω.norm_gnsVector_sq_eq_opNorm]

end Unital

end PositiveLinearMap

namespace WithLp

variable (H : Type v) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The isometric embedding `ξ ↦ (ξ, 0)` of `H` into the first summand of `WithLp 2 (H × H)`. -/
noncomputable def inlL2 : H →L[ℂ] WithLp 2 (H × H) :=
  (WithLp.fstL 2 ℂ H H).adjoint

@[simp]
theorem inlL2_apply (ξ : H) : inlL2 H ξ = WithLp.toLp 2 (ξ, 0) := by
  refine ext_inner_left ℂ fun y => ?_
  rw [inlL2, ContinuousLinearMap.adjoint_inner_right]
  simp

@[simp]
theorem adjoint_inlL2 : (inlL2 H).adjoint = WithLp.fstL 2 ℂ H H :=
  ContinuousLinearMap.adjoint_adjoint _

/-- The isometric embedding `ξ ↦ (0, ξ)` of `H` into the second summand of `WithLp 2 (H × H)`. -/
noncomputable def inrL2 : H →L[ℂ] WithLp 2 (H × H) :=
  (WithLp.sndL 2 ℂ H H).adjoint

@[simp]
theorem inrL2_apply (ξ : H) : inrL2 H ξ = WithLp.toLp 2 (0, ξ) := by
  refine ext_inner_left ℂ fun y => ?_
  rw [inrL2, ContinuousLinearMap.adjoint_inner_right]
  simp

@[simp]
theorem adjoint_inrL2 : (inrL2 H).adjoint = WithLp.sndL 2 ℂ H H :=
  ContinuousLinearMap.adjoint_adjoint _

theorem adjoint_inlL2_comp_self : (inlL2 H).adjoint.comp (inlL2 H) = 1 := by
  ext ξ
  simp

theorem norm_inlL2_sq [Nontrivial H] : ‖inlL2 H‖ ^ 2 = 1 := by
  rw [sq, ← ContinuousLinearMap.norm_adjoint_comp_self, adjoint_inlL2_comp_self, norm_one]

end WithLp

namespace CompletelyPositiveMap

section IdentityDilation

variable (H : Type v) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- `(H, id, 1)` satisfies the Stinespring dilation identity for `CompletelyPositiveMap.id`. -/
theorem id_dilation_eq (a : H →L[ℂ] H) :
    CompletelyPositiveMap.id (H →L[ℂ] H) a =
      (ContinuousLinearMap.id ℂ H).adjoint.comp
        ((StarAlgHom.id ℂ (H →L[ℂ] H) a).comp (ContinuousLinearMap.id ℂ H)) := by
  simp [ContinuousLinearMap.adjoint_id]

/-- `(H, id, 1)` is a minimal Stinespring dilation of `CompletelyPositiveMap.id (H →L[ℂ] H)`. -/
theorem id_dilation_minimal :
    (Submodule.span ℂ {x : H | ∃ (a : H →L[ℂ] H) (ξ : H),
      x = StarAlgHom.id ℂ (H →L[ℂ] H) a (ContinuousLinearMap.id ℂ H ξ)}
      ).topologicalClosure = ⊤ := by
  rw [eq_top_iff]
  intro x _
  exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨1, x, by simp⟩)

/-- The diagonal `⋆`-representation `a ↦ a ⊕ a` of `H →L[ℂ] H` on `WithLp 2 (H × H)`. -/
noncomputable def prodDiagStarAlgHom :
    (H →L[ℂ] H) →⋆ₐ[ℂ] (WithLp 2 (H × H) →L[ℂ] WithLp 2 (H × H)) where
  toFun a :=
    (WithLp.inlL2 H).comp (a.comp (WithLp.fstL 2 ℂ H H)) +
      (WithLp.inrL2 H).comp (a.comp (WithLp.sndL 2 ℂ H H))
  map_one' := by
    ext x
    refine ext_inner_left ℂ fun y => ?_
    simp
  map_mul' a b := by
    ext x
    refine ext_inner_left ℂ fun y => ?_
    simp [ContinuousLinearMap.mul_def]
  map_zero' := by simp
  map_add' a b := by
    simp only [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add]
    abel
  commutes' r := by
    ext x
    refine ext_inner_left ℂ fun y => ?_
    simp [Algebra.algebraMap_eq_smul_one, mul_add]
  map_star' a := by
    simp [ContinuousLinearMap.star_eq_adjoint, WithLp.inlL2, WithLp.inrL2,
      ContinuousLinearMap.comp_assoc]

@[simp]
theorem prodDiagStarAlgHom_apply (a : H →L[ℂ] H) (x : WithLp 2 (H × H)) :
    prodDiagStarAlgHom H a x = WithLp.toLp 2 (a x.fst, a x.snd) := by
  have hdef : prodDiagStarAlgHom H a =
      (WithLp.inlL2 H).comp (a.comp (WithLp.fstL 2 ℂ H H)) +
        (WithLp.inrL2 H).comp (a.comp (WithLp.sndL 2 ℂ H H)) := rfl
  rw [hdef]
  refine ext_inner_left ℂ fun y => ?_
  simp

/-- The doubled dilation `(WithLp 2 (H × H), id ⊕ id, ξ ↦ (ξ, 0))` still satisfies the
Stinespring dilation identity for `CompletelyPositiveMap.id (H →L[ℂ] H)`. -/
theorem prodDiag_dilation_eq (a : H →L[ℂ] H) :
    CompletelyPositiveMap.id (H →L[ℂ] H) a =
      (WithLp.inlL2 H).adjoint.comp ((prodDiagStarAlgHom H a).comp (WithLp.inlL2 H)) := by
  ext ξ
  simp

/-- On any nontrivial Hilbert space `H`, the doubled dilation
`(WithLp 2 (H × H), id ⊕ id, ξ ↦ (ξ, 0))` of `CompletelyPositiveMap.id (H →L[ℂ] H)` is **not**
minimal: its spanning subspace is contained in `H × {0}`. -/
theorem topologicalClosure_span_prodDiag_ne_top [Nontrivial H] :
    (Submodule.span ℂ
      {x : WithLp 2 (H × H) | ∃ (a : H →L[ℂ] H) (ξ : H),
        x = prodDiagStarAlgHom H a (WithLp.inlL2 H ξ)}).topologicalClosure ≠ ⊤ := by
  intro htop
  obtain ⟨η, hη⟩ := exists_ne (0 : H)
  have hle : (Submodule.span ℂ
      {x : WithLp 2 (H × H) | ∃ (a : H →L[ℂ] H) (ξ : H),
        x = prodDiagStarAlgHom H a (WithLp.inlL2 H ξ)}).topologicalClosure ≤
      (WithLp.sndL 2 ℂ H H).ker := by
    refine Submodule.topologicalClosure_minimal _ (Submodule.span_le.mpr ?_)
      (WithLp.sndL 2 ℂ H H).isClosed_ker
    rintro _ ⟨a, ξ, rfl⟩
    simp
  have hmem : WithLp.toLp 2 ((0 : H), η) ∈ (WithLp.sndL 2 ℂ H H).ker :=
    hle (htop ▸ Submodule.mem_top)
  exact hη (by simpa using hmem)

end IdentityDilation

end CompletelyPositiveMap

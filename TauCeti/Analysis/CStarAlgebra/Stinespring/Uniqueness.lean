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

Any minimal Stinespring dilation `(K, π, V)` of `φ : A →CP (H →L[ℂ] H)` is unitarily equivalent to
the canonical dilation `(φ.Stinespring, φ.stinespringHom, φ.stinespringOp)` by a unique unitary
`U : φ.Stinespring ≃ₗᵢ[ℂ] K` (`CompletelyPositiveMap.stinespringEquiv`) satisfying
`U (φ.stinespringOp ξ) = V ξ` and `U (φ.stinespringHom a x) = π a (U x)`.

We also relate scalar positive functionals (`H = ℂ`) to their GNS representation
(`PositiveLinearMap.toCompletelyPositiveMap`, `PositiveLinearMap.gnsStinespringEquiv`) and contrast
the minimal dilation `(H, id, 1)` of `id_{B(H)}` with the non-minimal doubled dilation on `H ⊕ H`.

## References

* W. F. Stinespring, *Positive functions on C⋆-algebras*, Proc. Amer. Math. Soc. 6 (1955),
  Theorems 1 and 3.
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

/-- The algebraic evaluation map `A ⊗[ℂ] H →ₗ[ℂ] K` sending `a ⊗ₜ ξ` to `π a (V ξ)`. -/
noncomputable def stinespringLiftLinear : (A ⊗[ℂ] H) →ₗ[ℂ] K :=
  TensorProduct.lift <| LinearMap.mk₂ ℂ (fun a ξ => π a (V ξ))
    (fun _ _ _ => by simp) (fun _ _ _ => by simp) (fun _ _ _ => by simp) (fun _ _ _ => by simp)

@[simp] theorem stinespringLiftLinear_tmul (a : A) (ξ : H) :
    stinespringLiftLinear π V (a ⊗ₜ[ℂ] ξ) = π a (V ξ) := (rfl)

theorem range_stinespringLiftLinear :
    LinearMap.range (stinespringLiftLinear π V) =
      Submodule.span ℂ {x : K | ∃ (a : A) (ξ : H), x = π a (V ξ)} := by
  rw [← Submodule.map_top, ← TensorProduct.span_tmul_eq_top, Submodule.map_span]
  congr 1; ext; simp [stinespringLiftLinear_tmul, eq_comm]

theorem denseRange_stinespringLiftLinear
    (hmin : (Submodule.span ℂ {x : K | ∃ (a : A) (ξ : H), x = π a (V ξ)}).topologicalClosure = ⊤) :
    DenseRange (stinespringLiftLinear π V) := by
  rwa [DenseRange, ← LinearMap.coe_range, range_stinespringLiftLinear π V,
    Submodule.dense_iff_topologicalClosure_eq_top]

/-- In any minimal dilation `(K, π, V)`, `π` is automatically nondegenerate. -/
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

/-- Any dilation `(K, π, V)` of `φ` induces the canonical Stinespring inner product on
`A ⊗[ℂ] H`. -/
theorem inner_stinespringLiftLinear_eq (hφ : ∀ a, φ a = V.adjoint.comp ((π a).comp V))
    (s t : A ⊗[ℂ] H) :
    ⟪stinespringLiftLinear π V s, stinespringLiftLinear π V t⟫_ℂ =
      ⟪φ.toStinespringLinearMap s, φ.toStinespringLinearMap t⟫_ℂ := by
  induction s using TensorProduct.inductionOn with
  | tmul a ξ =>
    induction t using TensorProduct.inductionOn with
    | tmul b η =>
      calc ⟪π a (V ξ), π b (V η)⟫_ℂ
          = ⟪V ξ, π (star a * b) (V η)⟫_ℂ := by
              rw [← ContinuousLinearMap.adjoint_inner_right (π a),
                ← ContinuousLinearMap.star_eq_adjoint, ← map_star,
                ← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.mul_def, ← map_mul]
        _ = ⟪ξ, φ (star a * b) η⟫_ℂ := by
              rw [hφ (star a * b), ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
                ContinuousLinearMap.adjoint_inner_right]
        _ = ⟪φ.toStinespringLinearMap (a ⊗ₜ[ℂ] ξ), φ.toStinespringLinearMap (b ⊗ₜ[ℂ] η)⟫_ℂ := by
              simp
    | add t₁ t₂ ht₁ ht₂ => rw [map_add, map_add, inner_add_right, inner_add_right, ht₁, ht₂]
  | add s₁ s₂ hs₁ hs₂ => rw [map_add, map_add, inner_add_left, inner_add_left, hs₁, hs₂]

/-- Any dilation `(K, π, V)` of `φ` preserves the Stinespring norm on `A ⊗[ℂ] H`. -/
theorem norm_stinespringLiftLinear_eq (hφ : ∀ a, φ a = V.adjoint.comp ((π a).comp V))
    (t : A ⊗[ℂ] H) : ‖stinespringLiftLinear π V t‖ = ‖φ.toStinespringLinearMap t‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), ← RCLike.ofReal_inj (K := ℂ),
    RCLike.ofReal_pow, RCLike.ofReal_pow, ← inner_self_eq_norm_sq_to_K,
    ← inner_self_eq_norm_sq_to_K]
  exact φ.inner_stinespringLiftLinear_eq π V hφ t t

section Minimal

variable (hφ : ∀ a, φ a = V.adjoint.comp ((π a).comp V))
  (hmin : (Submodule.span ℂ {x : K | ∃ (a : A) (ξ : H), x = π a (V ξ)}).topologicalClosure = ⊤)

/-- The canonical unitary equivalence from `φ.Stinespring` to any minimal Stinespring dilation
`(K, π, V)` of `φ`, sending `[a ⊗ ξ]` to `π a (V ξ)`. -/
noncomputable def stinespringEquiv : φ.Stinespring ≃ₗᵢ[ℂ] K :=
  (LinearEquiv.refl ℂ (A ⊗[ℂ] H)).extendOfIsometry
    φ.toStinespringLinearMap (stinespringLiftLinear π V)
    φ.denseRange_toStinespringLinearMap (denseRange_stinespringLiftLinear π V hmin)
    (φ.norm_stinespringLiftLinear_eq π V hφ)

theorem stinespringEquiv_toStinespringLinearMap (t : A ⊗[ℂ] H) :
    φ.stinespringEquiv π V hφ hmin (φ.toStinespringLinearMap t) = stinespringLiftLinear π V t :=
  LinearEquiv.extendOfIsometry_eq _ _ _ _ _ _ t

@[simp] theorem stinespringEquiv_apply_coe (t : A ⊗[ℂ] H) :
    φ.stinespringEquiv π V hφ hmin (φ.toPreStinespring t : φ.Stinespring) =
      stinespringLiftLinear π V t := by
  rw [← toStinespringLinearMap_apply]
  exact φ.stinespringEquiv_toStinespringLinearMap π V hφ hmin t

theorem stinespringEquiv_toStinespring (a : A) (ξ : H) :
    φ.stinespringEquiv π V hφ hmin (φ.toStinespring a ξ) = π a (V ξ) := by simp

@[simp] theorem stinespringEquiv_intertwines (a : A) (x : φ.Stinespring) :
    φ.stinespringEquiv π V hφ hmin (φ.stinespringHom a x) =
      π a (φ.stinespringEquiv π V hφ hmin x) := by
  let U := φ.stinespringEquiv π V hφ hmin
  refine φ.denseRange_toStinespringLinearMap.induction_on x
    (isClosed_eq (U.continuous.comp (φ.stinespringHom a).continuous)
      ((π a).continuous.comp U.continuous)) fun t => ?_
  induction t using TensorProduct.inductionOn with
  | tmul b ξ =>
    have hbt : φ.toStinespringLinearMap (b ⊗ₜ[ℂ] ξ) = φ.toStinespring b ξ := by simp
    rw [hbt, stinespringHom_toStinespring, stinespringEquiv_toStinespring,
      stinespringEquiv_toStinespring, map_mul, ContinuousLinearMap.mul_def,
      ContinuousLinearMap.comp_apply]
  | add s₁ s₂ hs₁ hs₂ => rw [map_add, map_add, map_add, hs₁, hs₂, ← map_add, ← map_add]

@[simp] theorem stinespringEquiv_stinespringOp (ξ : H) :
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

theorem stinespringEquiv_symm_apply (a : A) (ξ : H) :
    (φ.stinespringEquiv π V hφ hmin).symm (π a (V ξ)) = φ.toStinespring a ξ :=
  (φ.stinespringEquiv π V hφ hmin).injective (by simp)

@[simp] theorem stinespringEquiv_symm_intertwines (a : A) (y : K) :
    (φ.stinespringEquiv π V hφ hmin).symm (π a y) =
      φ.stinespringHom a ((φ.stinespringEquiv π V hφ hmin).symm y) :=
  (φ.stinespringEquiv π V hφ hmin).injective (by simp)

@[simp] theorem stinespringEquiv_symm_apply_op (ξ : H) :
    (φ.stinespringEquiv π V hφ hmin).symm (V ξ) = φ.stinespringOp ξ :=
  (φ.stinespringEquiv π V hφ hmin).injective (by simp)

/-- Any unitary sending `φ.stinespringOp` to `V` and intertwining `φ.stinespringHom` with `π`
equals `φ.stinespringEquiv`. -/
theorem stinespringEquiv_unique (U : φ.Stinespring ≃ₗᵢ[ℂ] K)
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
    simp only [Function.comp_apply, map_add] at hs₁ hs₂ ⊢; rw [hs₁, hs₂]

include hφ hmin in
/-- Existence and uniqueness of a unitary intertwiner from `φ.Stinespring` to any minimal
Stinespring dilation `(K, π, V)` of `φ`. -/
theorem existsUnique_stinespringEquiv :
    ∃! U : φ.Stinespring ≃ₗᵢ[ℂ] K, (∀ ξ, U (φ.stinespringOp ξ) = V ξ) ∧
      ∀ (a : A) (x : φ.Stinespring), U (φ.stinespringHom a x) = π a (U x) :=
  ⟨φ.stinespringEquiv π V hφ hmin,
    ⟨φ.stinespringEquiv_stinespringOp π V hφ hmin, φ.stinespringEquiv_intertwines π V hφ hmin⟩,
    fun U ⟨hV, hπ⟩ => φ.stinespringEquiv_unique π V hφ hmin U hV hπ⟩

include hφ hmin in
/-- In any minimal Stinespring dilation `(K, π, V)` of `φ`, `‖V‖ ^ 2 = ‖φ‖`. -/
theorem norm_op_sq_of_minimal : ‖V‖ ^ 2 = ‖φ.toContinuousLinearMap‖ := by
  let U := φ.stinespringEquiv π V hφ hmin
  have hV : V = U.toLinearIsometry.toContinuousLinearMap.comp φ.stinespringOp :=
    ContinuousLinearMap.ext fun ξ => (φ.stinespringEquiv_stinespringOp π V hφ hmin ξ).symm
  rw [hV, U.toLinearIsometry.norm_toContinuousLinearMap_comp, φ.norm_stinespringOp_sq]

end Minimal

/-- Any two minimal Stinespring dilations of `φ` are intertwined by a unique unitary preserving
both `π` and `V`. -/
theorem existsUnique_unitary_of_minimal
    {K₂ : Type w'} [NormedAddCommGroup K₂] [InnerProductSpace ℂ K₂] [CompleteSpace K₂]
    (π₂ : A →⋆ₙₐ[ℂ] (K₂ →L[ℂ] K₂)) (V₂ : H →L[ℂ] K₂)
    (hφ₁ : ∀ a, φ a = V.adjoint.comp ((π a).comp V))
    (hmin₁ : (Submodule.span ℂ {x : K | ∃ (a : A) (ξ : H), x = π a (V ξ)}).topologicalClosure = ⊤)
    (hφ₂ : ∀ a, φ a = V₂.adjoint.comp ((π₂ a).comp V₂))
    (hmin₂ :
      (Submodule.span ℂ {x : K₂ | ∃ (a : A) (ξ : H), x = π₂ a (V₂ ξ)}).topologicalClosure = ⊤) :
    ∃! U : K ≃ₗᵢ[ℂ] K₂,
      (∀ ξ, U (V ξ) = V₂ ξ) ∧ ∀ (a : A) (x : K), U (π a x) = π₂ a (U x) := by
  let U₁ := φ.stinespringEquiv π V hφ₁ hmin₁
  let U₂ := φ.stinespringEquiv π₂ V₂ hφ₂ hmin₂
  refine ⟨U₁.symm.trans U₂, ⟨fun _ => by simp [U₁, U₂], fun _ _ => by simp [U₁, U₂]⟩,
    fun U ⟨hUV, hUπ⟩ => ?_⟩
  have hcomp : U₁.trans U = U₂ :=
    φ.stinespringEquiv_unique π₂ V₂ hφ₂ hmin₂ (U₁.trans U)
      (fun _ => by simp [U₁, hUV]) (fun _ _ => by simp [U₁, hUπ])
  ext x
  simpa [U₁] using LinearIsometryEquiv.congr_fun hcomp (U₁.symm x)

end NonUnital

section Unital

variable {D : Type u} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
  {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {K : Type w} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (φ : D →CP (H →L[ℂ] H)) (π : D →⋆ₐ[ℂ] (K →L[ℂ] K)) (V : H →L[ℂ] K)

/-- Unital form of `CompletelyPositiveMap.existsUnique_stinespringEquiv`. -/
theorem existsUnique_stinespringEquiv_unital
    (hφ : ∀ a, φ a = V.adjoint.comp ((π a).comp V))
    (hmin : (Submodule.span ℂ {x : K | ∃ (a : D) (ξ : H), x = π a (V ξ)}).topologicalClosure = ⊤) :
    ∃! U : φ.Stinespring ≃ₗᵢ[ℂ] K, (∀ ξ, U (φ.stinespringOp ξ) = V ξ) ∧
      ∀ (a : D) (x : φ.Stinespring), U (φ.stinespringStarAlgHom a x) = π a (U x) := by
  simpa only [coe_stinespringStarAlgHom, StarAlgHom.coe_toNonUnitalStarAlgHom] using
    φ.existsUnique_stinespringEquiv π.toNonUnitalStarAlgHom V hφ hmin

/-- Unital form of `CompletelyPositiveMap.existsUnique_unitary_of_minimal`. -/
theorem existsUnique_unitary_of_minimal_unital
    {K₂ : Type w'} [NormedAddCommGroup K₂] [InnerProductSpace ℂ K₂] [CompleteSpace K₂]
    (π₂ : D →⋆ₐ[ℂ] (K₂ →L[ℂ] K₂)) (V₂ : H →L[ℂ] K₂)
    (hφ₁ : ∀ a, φ a = V.adjoint.comp ((π a).comp V))
    (hmin₁ : (Submodule.span ℂ {x : K | ∃ (a : D) (ξ : H), x = π a (V ξ)}).topologicalClosure = ⊤)
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

/-- Every positive linear functional `ω : A →ₚ[ℂ] ℂ` is completely positive
(Stinespring 1955, Theorem 3). -/
noncomputable def toCompletelyPositiveMap (ω : A →ₚ[ℂ] ℂ) : A →CP ℂ where
  toLinearMap := ω.toLinearMap
  map_cstarMatrix_nonneg' _ M hM := by
    obtain ⟨R, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hM
    refine CStarMatrix.nonneg_iff_forall_sum_nonneg.mpr fun z => ?_
    have hsum : (∑ i, ∑ j, star (z i) * (star R * R).map ω.toLinearMap i j * z j) =
        ∑ l, ω (star (∑ i, z i • R l i) * ∑ j, z j • R l j) := by
      have hLHS : (∑ i, ∑ j, star (z i) * (star R * R).map ω.toLinearMap i j * z j) =
          ∑ l, ∑ i, ∑ j, (star (z i) * z j) * ω (star (R l i) * R l j) := by
        refine (Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_).trans
          ((Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm)
        simp only [CStarMatrix.map_apply, PositiveLinearMap.coe_toLinearMap, CStarMatrix.mul_apply,
          CStarMatrix.star_apply, map_sum, Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun _ _ => by ring
      rw [hLHS]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [star_sum, Finset.sum_mul, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [star_smul, smul_mul_assoc, mul_smul_comm, map_smul, smul_eq_mul]; ring
    exact hsum ▸ Finset.sum_nonneg fun _ _ => map_nonneg ω (star_mul_self_nonneg _)

@[simp] theorem toCompletelyPositiveMap_apply (ω : A →ₚ[ℂ] ℂ) (a : A) :
    ω.toCompletelyPositiveMap a = ω a := (rfl)

/-- A positive linear functional `ω : A →ₚ[ℂ] ℂ` viewed as `A →CP (ℂ →L[ℂ] ℂ)` via `a ↦ ω a • 1`. -/
noncomputable def toCompletelyPositiveMapCLM (ω : A →ₚ[ℂ] ℂ) : A →CP (ℂ →L[ℂ] ℂ) :=
  CompletelyPositiveMap.comp
    (CompletelyPositiveMapClass.toCompletelyPositiveLinearMap (StarAlgHom.ofId ℂ (ℂ →L[ℂ] ℂ)))
    ω.toCompletelyPositiveMap

@[simp] theorem toCompletelyPositiveMapCLM_apply (ω : A →ₚ[ℂ] ℂ) (a : A) :
    ω.toCompletelyPositiveMapCLM a = ω a • (1 : ℂ →L[ℂ] ℂ) := by
  rw [toCompletelyPositiveMapCLM, CompletelyPositiveMap.comp_apply, toCompletelyPositiveMap_apply]
  exact (StarAlgHom.ofId_apply ℂ (ℂ →L[ℂ] ℂ) (ω a)).trans (Algebra.algebraMap_eq_smul_one (ω a))

end NonUnital

section Unital

variable {D : Type u} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] (ω : D →ₚ[ℂ] ℂ)

/-- `(ω.GNS, ω.gnsStarAlgHom, toSpanSingleton ℂ ω.gnsVector)` dilates
`ω.toCompletelyPositiveMapCLM`. -/
theorem gns_dilation_eq (a : D) :
    ω.toCompletelyPositiveMapCLM a =
      (ContinuousLinearMap.toSpanSingleton ℂ ω.gnsVector).adjoint.comp
        ((ω.gnsStarAlgHom a).comp (ContinuousLinearMap.toSpanSingleton ℂ ω.gnsVector)) := by
  refine ContinuousLinearMap.ext fun z => ?_
  simp [ContinuousLinearMap.adjoint_toSpanSingleton, innerSL_apply_apply,
    gnsStarAlgHom_apply, gnsNonUnitalStarAlgHom_apply_gnsVector, mul_comm]

/-- `(ω.GNS, ω.gnsStarAlgHom, toSpanSingleton ℂ ω.gnsVector)` is minimal as a Stinespring
dilation. -/
theorem gns_dilation_minimal :
    (Submodule.span ℂ {x : ω.GNS | ∃ (a : D) (z : ℂ),
      x = ω.gnsStarAlgHom a (ContinuousLinearMap.toSpanSingleton ℂ ω.gnsVector z)}
      ).topologicalClosure = ⊤ := by
  rw [← Submodule.dense_iff_topologicalClosure_eq_top]
  refine ω.denseRange_gnsStarAlgHom_gnsVector.mono ?_
  rintro _ ⟨a, rfl⟩
  exact Submodule.subset_span ⟨a, 1, by simp⟩

/-- The canonical Stinespring dilation of `ω : D →ₚ[ℂ] ℂ` (`H = ℂ`) is unitarily equivalent to
GNS. -/
noncomputable def gnsStinespringEquiv : ω.toCompletelyPositiveMapCLM.Stinespring ≃ₗᵢ[ℂ] ω.GNS :=
  ω.toCompletelyPositiveMapCLM.stinespringEquiv ω.gnsStarAlgHom.toNonUnitalStarAlgHom
    (ContinuousLinearMap.toSpanSingleton ℂ ω.gnsVector) ω.gns_dilation_eq ω.gns_dilation_minimal

@[simp↓] theorem gnsStinespringEquiv_intertwines (a : D)
    (x : ω.toCompletelyPositiveMapCLM.Stinespring) :
    ω.gnsStinespringEquiv (ω.toCompletelyPositiveMapCLM.stinespringStarAlgHom a x) =
      ω.gnsStarAlgHom a (ω.gnsStinespringEquiv x) := by
  simpa only [gnsStinespringEquiv, CompletelyPositiveMap.coe_stinespringStarAlgHom,
    StarAlgHom.coe_toNonUnitalStarAlgHom] using
    ω.toCompletelyPositiveMapCLM.stinespringEquiv_intertwines
      ω.gnsStarAlgHom.toNonUnitalStarAlgHom (ContinuousLinearMap.toSpanSingleton ℂ ω.gnsVector)
      ω.gns_dilation_eq ω.gns_dilation_minimal a x

@[simp] theorem gnsStinespringEquiv_stinespringOp (z : ℂ) :
    ω.gnsStinespringEquiv (ω.toCompletelyPositiveMapCLM.stinespringOp z) = z • ω.gnsVector :=
  ω.toCompletelyPositiveMapCLM.stinespringEquiv_stinespringOp
    ω.gnsStarAlgHom.toNonUnitalStarAlgHom (ContinuousLinearMap.toSpanSingleton ℂ ω.gnsVector)
    ω.gns_dilation_eq ω.gns_dilation_minimal z

/-- `‖ω.gnsVector‖ ^ 2` equals the operator norm of `ω`. -/
theorem norm_gnsVector_sq_eq_opNorm :
    ‖ω.gnsVector‖ ^ 2 = ‖(PositiveContinuousLinearMap.ofClass (R := ℂ) ω : D →L[ℂ] ℂ)‖ := by
  let f : D →P[ℂ] ℂ := PositiveContinuousLinearMap.ofClass (R := ℂ) ω
  have hf1 : (‖(f : D →L[ℂ] ℂ)‖ : ℂ) = ω 1 := f.ofReal_opNorm_eq_map_one
  have hsq : ((‖ω.gnsVector‖ ^ 2 : ℝ) : ℂ) = ω 1 := by simpa using ω.norm_gnsVector_sq
  exact Complex.ofReal_inj.mp (hsq.trans hf1.symm)

/-- The squared operator norm of `toSpanSingleton ℂ ω.gnsVector` equals the operator norm of `ω`. -/
theorem norm_toSpanSingleton_gnsVector_sq :
    ‖ContinuousLinearMap.toSpanSingleton ℂ ω.gnsVector‖ ^ 2 =
      ‖(PositiveContinuousLinearMap.ofClass (R := ℂ) ω : D →L[ℂ] ℂ)‖ := by
  have hV : ‖ContinuousLinearMap.toSpanSingleton ℂ ω.gnsVector‖ = ‖ω.gnsVector‖ :=
    (ContinuousLinearMap.toSpanSingletonLIE ℂ ω.GNS).norm_map ω.gnsVector
  rw [hV, ω.norm_gnsVector_sq_eq_opNorm]

end Unital

end PositiveLinearMap

namespace WithLp

variable (H : Type v) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The isometric embedding `ξ ↦ (ξ, 0)` of `H` into `WithLp 2 (H × H)`. -/
noncomputable def inlL2 : H →L[ℂ] WithLp 2 (H × H) := (WithLp.fstL 2 ℂ H H).adjoint

@[simp] theorem inlL2_apply (ξ : H) : inlL2 H ξ = WithLp.toLp 2 (ξ, 0) :=
  ext_inner_left ℂ fun y => by rw [inlL2, ContinuousLinearMap.adjoint_inner_right]; simp

@[simp] theorem adjoint_inlL2 : (inlL2 H).adjoint = WithLp.fstL 2 ℂ H H :=
  ContinuousLinearMap.adjoint_adjoint _

/-- The isometric embedding `ξ ↦ (0, ξ)` of `H` into `WithLp 2 (H × H)`. -/
noncomputable def inrL2 : H →L[ℂ] WithLp 2 (H × H) := (WithLp.sndL 2 ℂ H H).adjoint

@[simp] theorem inrL2_apply (ξ : H) : inrL2 H ξ = WithLp.toLp 2 (0, ξ) :=
  ext_inner_left ℂ fun y => by rw [inrL2, ContinuousLinearMap.adjoint_inner_right]; simp

@[simp] theorem adjoint_inrL2 : (inrL2 H).adjoint = WithLp.sndL 2 ℂ H H :=
  ContinuousLinearMap.adjoint_adjoint _

theorem adjoint_inlL2_comp_self : (inlL2 H).adjoint.comp (inlL2 H) = 1 := by ext; simp

theorem norm_inlL2_sq [Nontrivial H] : ‖inlL2 H‖ ^ 2 = 1 := by
  rw [sq, ← ContinuousLinearMap.norm_adjoint_comp_self, adjoint_inlL2_comp_self, norm_one]

end WithLp

namespace CompletelyPositiveMap

section IdentityDilation

variable (H : Type v) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- `(H, id, 1)` dilates `CompletelyPositiveMap.id (H →L[ℂ] H)`. -/
theorem id_dilation_eq (a : H →L[ℂ] H) :
    CompletelyPositiveMap.id (H →L[ℂ] H) a =
      (ContinuousLinearMap.id ℂ H).adjoint.comp
        ((StarAlgHom.id ℂ (H →L[ℂ] H) a).comp (ContinuousLinearMap.id ℂ H)) := by
  simp [ContinuousLinearMap.adjoint_id]

/-- `(H, id, 1)` is a minimal Stinespring dilation of `CompletelyPositiveMap.id (H →L[ℂ] H)`. -/
theorem id_dilation_minimal :
    (Submodule.span ℂ {x : H | ∃ (a : H →L[ℂ] H) (ξ : H),
      x = StarAlgHom.id ℂ (H →L[ℂ] H) a (ContinuousLinearMap.id ℂ H ξ)}
      ).topologicalClosure = ⊤ :=
  eq_top_iff.mpr fun x _ =>
    Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨1, x, by simp⟩)

/-- The diagonal `⋆`-representation `a ↦ a ⊕ a` of `H →L[ℂ] H` on `WithLp 2 (H × H)`. -/
noncomputable def prodDiagStarAlgHom :
    (H →L[ℂ] H) →⋆ₐ[ℂ] (WithLp 2 (H × H) →L[ℂ] WithLp 2 (H × H)) where
  toFun a := (WithLp.inlL2 H).comp (a.comp (WithLp.fstL 2 ℂ H H)) +
    (WithLp.inrL2 H).comp (a.comp (WithLp.sndL 2 ℂ H H))
  map_one' := ContinuousLinearMap.ext fun _ => ext_inner_left ℂ fun _ => by simp
  map_mul' _ _ := ContinuousLinearMap.ext fun _ => ext_inner_left ℂ fun _ => by
    simp [ContinuousLinearMap.mul_def]
  map_zero' := by simp
  map_add' _ _ := by simp only [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add]; abel
  commutes' _ := ContinuousLinearMap.ext fun _ => ext_inner_left ℂ fun _ => by
    simp [Algebra.algebraMap_eq_smul_one, mul_add]
  map_star' _ := by
    simp [ContinuousLinearMap.star_eq_adjoint, WithLp.inlL2, WithLp.inrL2,
      ContinuousLinearMap.comp_assoc]

@[simp] theorem prodDiagStarAlgHom_apply (a : H →L[ℂ] H) (x : WithLp 2 (H × H)) :
    prodDiagStarAlgHom H a x = WithLp.toLp 2 (a x.fst, a x.snd) := by
  change ((WithLp.inlL2 H).comp (a.comp (WithLp.fstL 2 ℂ H H)) +
    (WithLp.inrL2 H).comp (a.comp (WithLp.sndL 2 ℂ H H))) x = _
  exact ext_inner_left ℂ fun _ => by simp

/-- `(WithLp 2 (H × H), id ⊕ id, ξ ↦ (ξ, 0))` dilates `CompletelyPositiveMap.id (H →L[ℂ] H)`. -/
theorem prodDiag_dilation_eq (a : H →L[ℂ] H) :
    CompletelyPositiveMap.id (H →L[ℂ] H) a =
      (WithLp.inlL2 H).adjoint.comp ((prodDiagStarAlgHom H a).comp (WithLp.inlL2 H)) := by
  ext; simp

/-- On any nontrivial `H`, the doubled dilation `(WithLp 2 (H × H), id ⊕ id, inlL2 H)` is not
minimal. -/
theorem topologicalClosure_span_prodDiag_ne_top [Nontrivial H] :
    (Submodule.span ℂ
      {x : WithLp 2 (H × H) | ∃ (a : H →L[ℂ] H) (ξ : H),
        x = prodDiagStarAlgHom H a (WithLp.inlL2 H ξ)}).topologicalClosure ≠ ⊤ := by
  intro htop
  obtain ⟨η, hη⟩ := exists_ne (0 : H)
  have hle : (Submodule.span ℂ
      {x : WithLp 2 (H × H) | ∃ (a : H →L[ℂ] H) (ξ : H),
        x = prodDiagStarAlgHom H a (WithLp.inlL2 H ξ)}).topologicalClosure ≤
      (WithLp.sndL 2 ℂ H H).ker :=
    Submodule.topologicalClosure_minimal _
      (Submodule.span_le.mpr fun _ ⟨a, ξ, h⟩ => by subst h; simp)
      (WithLp.sndL 2 ℂ H H).isClosed_ker
  exact hη (by simpa using (hle (htop ▸ Submodule.mem_top) :
    WithLp.toLp 2 ((0 : H), η) ∈ (WithLp.sndL 2 ℂ H H).ker))

end IdentityDilation

end CompletelyPositiveMap

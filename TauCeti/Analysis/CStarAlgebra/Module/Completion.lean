/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Extend
public import TauCeti.Analysis.CStarAlgebra.Module.Self
public import TauCeti.Analysis.CStarAlgebra.Module.Semidefinite
public import TauCeti.Analysis.Normed.Operator.Completion
public import TauCeti.Topology.Algebra.NonUnitalStarAlgebra
import TauCeti.Topology.Algebra.LinearMapCompletion

/-!
# Completions of pre-Hilbert and positive semidefinite C⋆-modules

Completing a pre-Hilbert or positive semidefinite C⋆-module produces a Hilbert C⋆-module,
canonically isometric to the completion of its separation quotient. When `E` is acted on by a dense
`⋆`-subalgebra `A₀` of `A` along `φ : A₀ →⋆ₙₐ[ℂ] A`, `UniformSpace.Completion E` carries a unique
continuous `A`-action extending `A₀` and making `Completion E` a Hilbert `A`-module.

## Main declarations

* `TauCeti.SemiCStarModuleAlong.{semiCStarModuleAlong_completion, inner_self_eq_zero_completion}`:
  `Completion E` inherits `SemiCStarModuleAlong φ` with definite `A`-valued inner product.
* `TauCeti.SemiCStarModuleAlong.{extendSMulCLM, eq_extendSMulCLM_iff, completedCStarModule}`:
  unique contractive extension `A →L[ℂ] Completion E →L[ℂ] Completion E` along dense `φ`.
* `UniformSpace.Completion.instCStarModule`: global `CStarModule A (Completion E)` instance.
* `inner_separationQuotientEquiv`, `inner_separationQuotientEquiv_symm`, and preservation of
  fullness (`topologicalClosure_span_range_inner_completion` and right-module variants).
* Universal properties for continuous maps (`fromCompletion_extendSMulCLM_iff`) and plain
  inner-preserving maps (`fromCompletionInnerₗᵢ`, `equivOfDenseInner`).
* `NonUnitalStarSubalgebra.completionEquiv`: `Completion S ≃ₗᵢ[ℂ] A` for dense `S ⊆ A`.

## References

* E. Christopher Lance, *Hilbert C⋆-Modules: A Toolkit for Operator Algebraists*, Chapter 1.
* Iain Raeburn and Dana P. Williams, *Morita Equivalence and Continuous-Trace C⋆-Algebras*, Ch. 2.
* `Mathlib.Analysis.InnerProductSpace.Completion` and `Mathlib.Analysis.Normed.Operator.Extend`.
-/

public section

open MulOpposite UniformSpace Filter Topology

namespace TauCeti.SemiCStarModuleAlong

/-! ### Inner product, definiteness, and extended action on `Completion E` -/

section CompletionAlong

variable {A₀ A E : Type*} [NonUnitalSemiring A₀] [StarRing A₀] [Module ℂ A₀]
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {φ : A₀ →⋆ₙₐ[ℂ] A} [SeminormedAddCommGroup E] [NormedSpace ℂ E] [SMul A₀ E] [Inner A E]
  [SemiCStarModuleAlong φ E]
include φ

/-- On vectors from `E`, the `A`-valued inner product on `Completion E` agrees with that of `E`. -/
theorem inner_coe_coe (hφ : DenseRange φ) (x y : E) :
    inner A (x : Completion E) (y : Completion E) = inner A x y :=
  (Completion.isDenseInducing_coe.prodMap Completion.isDenseInducing_coe).extend_eq
    (continuous_inner hφ) (x, y)

/-- The `A`-valued inner product on `Completion E` is jointly continuous. -/
theorem continuous_inner_completion (hφ : DenseRange φ) :
    Continuous (fun p : Completion E × Completion E ↦ inner A p.1 p.2) := by
  let inner' : E →+ E →+ A :=
    { toFun x := { toFun y := inner A x y, map_zero' := inner_zero_right φ x,
                   map_add' _ _ := inner_add_right (φ := φ) }
      map_zero' := by ext y; exact inner_zero_left φ y
      map_add' x y := by ext z; exact inner_add_left φ x y z }
  have hcont : Continuous (fun p : E × E ↦ inner' p.1 p.2) := continuous_inner hφ
  exact (Completion.isDenseInducing_toCompl E).extend_Z_bilin
    (Completion.isDenseInducing_toCompl E) hcont

private lemma continuous_inner_pair {α : Type*} [TopologicalSpace α] (hφ : DenseRange φ)
    {f g : α → Completion E} (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun a ↦ inner A (f a) (g a)) := (continuous_inner_completion hφ).comp (hf.prodMk hg)

/-- The norm on `Completion E` is `√‖⟪x, x⟫_A‖`. -/
theorem norm_eq_sqrt_norm_inner_self_completion (hφ : DenseRange φ) (x : Completion E) :
    ‖x‖ = √‖inner A x x‖ := by
  refine Completion.induction_on x (isClosed_eq continuous_norm (Real.continuous_sqrt.comp
    (continuous_norm.comp (continuous_inner_pair hφ continuous_id continuous_id)))) fun a ↦ ?_
  rw [Completion.norm_coe, inner_coe_coe hφ, norm_eq_sqrt_norm_inner_self (φ := φ) a]

/-- Self-inner products on `Completion E` are nonnegative in `A`. -/
theorem inner_self_nonneg_completion (hφ : DenseRange φ) (x : Completion E) : 0 ≤ inner A x x := by
  refine Completion.induction_on x
    (isClosed_le continuous_const (continuous_inner_pair hφ continuous_id continuous_id)) fun a ↦ ?_
  rw [inner_coe_coe hφ]; exact inner_self_nonneg (φ := φ)

/-- Additivity of the `A`-valued inner product on `Completion E` in the right variable. -/
theorem inner_add_right_completion (hφ : DenseRange φ) (x y z : Completion E) :
    inner A x (y + z) = inner A x y + inner A x z := by
  refine Completion.induction_on₃ x y z (isClosed_eq
    (continuous_inner_pair hφ continuous_fst (continuous_snd.fst.add continuous_snd.snd))
    ((continuous_inner_pair hφ continuous_fst continuous_snd.fst).add
      (continuous_inner_pair hφ continuous_fst continuous_snd.snd))) fun a b c ↦ ?_
  rw [← Completion.coe_add, inner_coe_coe hφ, inner_coe_coe hφ, inner_coe_coe hφ,
    inner_add_right (φ := φ)]

/-- Conjugate symmetry `⟪x, y⟫_A⋆ = ⟪y, x⟫_A` on `Completion E`. -/
theorem star_inner_completion (hφ : DenseRange φ) (x y : Completion E) :
    star (inner A x y) = inner A y x := by
  refine Completion.induction_on₂ x y (isClosed_eq
    (continuous_star.comp (continuous_inner_pair hφ continuous_fst continuous_snd))
    (continuous_inner_pair hφ continuous_snd continuous_fst)) fun a b ↦ ?_
  rw [inner_coe_coe hφ, inner_coe_coe hφ, star_inner (φ := φ)]

/-- Complex homogeneity in the right variable on `Completion E`. -/
theorem inner_smul_right_complex_completion (hφ : DenseRange φ) (c : ℂ) (x y : Completion E) :
    inner A x (c • y) = c • inner A x y := by
  refine Completion.induction_on₂ x y (isClosed_eq
    (continuous_inner_pair hφ continuous_fst (continuous_snd.const_smul c))
    ((continuous_inner_pair hφ continuous_fst continuous_snd).const_smul c)) fun a b ↦ ?_
  rw [← Completion.coe_smul, inner_coe_coe hφ, inner_coe_coe hφ, inner_smul_right_complex (φ := φ)]

/-- The coercion `E → Completion E` commutes with `A₀`, without assuming `DistribSMul`. -/
theorem coe_smul_along (a₀ : A₀) (x : E) :
    ((a₀ • x : E) : Completion E) = a₀ • (x : Completion E) := by
  let _ := uniformContinuousConstSMul (φ := φ) (E := E)
  exact Completion.coe_smul a₀ x

/-- Compatibility `⟪x, a₀ • y⟫_A = φ a₀ * ⟪x, y⟫_A` on `Completion E`. -/
theorem inner_op_smul_right_completion (hφ : DenseRange φ) (a₀ : A₀) (x y : Completion E) :
    inner A x (a₀ • y) = φ a₀ * inner A x y := by
  refine Completion.induction_on₂ x y (isClosed_eq
    (continuous_inner_pair hφ continuous_fst (continuous_snd.const_smul a₀))
    ((continuous_const_mul (φ a₀)).comp (continuous_inner_pair hφ continuous_fst continuous_snd)))
    fun u v ↦ ?_
  rw [← coe_smul_along (φ := φ) a₀ v, inner_coe_coe hφ, inner_coe_coe hφ,
    inner_op_smul_right (φ := φ)]

variable (E) in
/-- `Completion E` inherits `SemiCStarModuleAlong φ` when `φ` has dense range. -/
theorem semiCStarModuleAlong_completion (hφ : DenseRange φ) :
    SemiCStarModuleAlong φ (Completion E) where
  inner_add_right := inner_add_right_completion hφ _ _ _
  inner_self_nonneg := inner_self_nonneg_completion hφ _
  inner_op_smul_right := inner_op_smul_right_completion hφ _ _ _
  inner_smul_right_complex := inner_smul_right_complex_completion hφ _ _ _
  star_inner := star_inner_completion hφ
  norm_eq_sqrt_norm_inner_self := norm_eq_sqrt_norm_inner_self_completion hφ

/-- Definiteness of the `A`-valued inner product on `Completion E`: `⟪x, x⟫_A = 0 ↔ x = 0`. -/
theorem inner_self_eq_zero_completion (hφ : DenseRange φ) (x : Completion E) :
    inner A x x = 0 ↔ x = 0 := by
  have := semiCStarModuleAlong_completion E hφ
  exact ⟨fun hx ↦ norm_eq_zero.mp <| (norm_eq_zero_iff_inner_self_eq_zero φ x).mpr hx,
    fun hx ↦ hx ▸ inner_zero_right φ 0⟩

/-- Vectors in `Completion E` with equal inner products against all `w : Completion E` are equal. -/
theorem ext_inner_left_completion (hφ : DenseRange φ) {x y : Completion E}
    (h : ∀ w : Completion E, inner A w x = inner A w y) : x = y := by
  have := semiCStarModuleAlong_completion E hφ
  rw [← sub_eq_zero, ← inner_self_eq_zero_completion hφ, inner_sub_right φ, h, sub_self]

/-- Norm bound `‖a₀ • x‖ ≤ ‖φ a₀‖ * ‖x‖` for the `A₀`-action on `Completion E`. -/
theorem norm_smul_along_completion_le (a₀ : A₀) (x : Completion E) : ‖a₀ • x‖ ≤ ‖φ a₀‖ * ‖x‖ := by
  refine Completion.induction_on x (isClosed_le (continuous_norm.comp (continuous_const_smul a₀))
    ((continuous_const_mul _).comp continuous_norm)) fun u ↦ ?_
  rw [← coe_smul_along (φ := φ) a₀ u, Completion.norm_coe, Completion.norm_coe]
  exact norm_smul_le φ a₀ u

variable (E) in
/-- The `A₀`-action on `Completion E` as a `ℂ`-linear map into `Completion E →L[ℂ] Completion E`
(strictly bilinear by definiteness of the completed inner product, even without `DistribSMul`). -/
private noncomputable def smulAlongCLM (hφ : DenseRange φ) :
    A₀ →ₗ[ℂ] Completion E →L[ℂ] Completion E where
  toFun a₀ := LinearMap.mkContinuous
    { toFun x := a₀ • x
      map_add' x y := ext_inner_left_completion hφ fun w ↦ by
        simp [inner_add_right_completion hφ, inner_op_smul_right_completion hφ, mul_add]
      map_smul' c x := ext_inner_left_completion hφ fun w ↦ by
        simp [inner_smul_right_complex_completion hφ, inner_op_smul_right_completion hφ,
          mul_smul_comm] }
    ‖φ a₀‖ (fun x ↦ norm_smul_along_completion_le (φ := φ) a₀ x)
  map_add' a₀ b₀ := by
    ext x; exact ext_inner_left_completion hφ fun w ↦ by
      simp [inner_add_right_completion hφ, inner_op_smul_right_completion hφ, add_mul]
  map_smul' c a₀ := by
    ext x; exact ext_inner_left_completion hφ fun w ↦ by
      simp [inner_smul_right_complex_completion hφ, inner_op_smul_right_completion hφ,
        smul_mul_assoc]

private theorem smulAlongCLM_apply (hφ : DenseRange φ) (a₀ : A₀) (x : Completion E) :
    smulAlongCLM E hφ a₀ x = a₀ • x := (rfl)

variable (E) in
private theorem norm_smulAlongCLM_le (hφ : DenseRange φ) (a₀ : A₀) :
    ‖smulAlongCLM E hφ a₀‖ ≤ ‖φ a₀‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (_root_.norm_nonneg _) fun x ↦
    norm_smul_along_completion_le (φ := φ) a₀ x

variable (E) in
/-- Completion preserves the closed complex linear span of `A`-valued inner products. -/
theorem topologicalClosure_span_range_inner_completion (hφ : DenseRange φ) :
    (Submodule.span ℂ
        (Set.range fun p : Completion E × Completion E ↦ inner A p.1 p.2)).topologicalClosure =
      (Submodule.span ℂ (Set.range fun p : E × E ↦ inner A p.1 p.2)).topologicalClosure := by
  refine le_antisymm
    (Submodule.topologicalClosure_minimal _ ?_ (Submodule.isClosed_topologicalClosure _))
    (Submodule.topologicalClosure_mono <| Submodule.span_mono ?_)
  · rw [Submodule.span_le]; rintro _ ⟨⟨x, y⟩, rfl⟩
    refine Completion.induction_on₂ x y
      ((Submodule.isClosed_topologicalClosure _).preimage (continuous_inner_completion hφ))
      fun u v ↦ ?_
    simp only [inner_coe_coe hφ]
    exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨(u, v), rfl⟩)
  · rintro _ ⟨⟨u, v⟩, rfl⟩; exact ⟨((u : Completion E), (v : Completion E)), inner_coe_coe hφ u v⟩

end CompletionAlong

section ExtendSMul

variable {A₀ A E : Type*} [NonUnitalRing A₀] [StarRing A₀] [Module ℂ A₀]
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {φ : A₀ →⋆ₙₐ[ℂ] A} [SeminormedAddCommGroup E] [NormedSpace ℂ E] [SMul A₀ E] [Inner A E]
  [SemiCStarModuleAlong φ E]
include φ

variable (E) in
/-- Continuous extension of the `A₀`-action along dense `φ : A₀ →⋆ₙₐ[ℂ] A` to a contractive
`ℂ`-linear action `A →L[ℂ] Completion E →L[ℂ] Completion E` of the C⋆-completion `A`. -/
noncomputable def extendSMulCLM (hφ : DenseRange φ) : A →L[ℂ] Completion E →L[ℂ] Completion E :=
  (smulAlongCLM E hφ).extendOfNorm (φ : A₀ →ₗ[ℂ] A)

variable (E) in
private theorem extendSMulCLM_map (hφ : DenseRange φ) (a₀ : A₀) :
    extendSMulCLM E hφ (φ a₀) = smulAlongCLM E hφ a₀ :=
  LinearMap.extendOfNorm_eq hφ ⟨1, fun b₀ ↦ by simpa using norm_smulAlongCLM_le E hφ b₀⟩ a₀
@[simp] theorem extendSMulCLM_map_apply (hφ : DenseRange φ) (a₀ : A₀) (x : Completion E) :
    extendSMulCLM E hφ (φ a₀) x = a₀ • x := by rw [extendSMulCLM_map, smulAlongCLM_apply]
theorem extendSMulCLM_map_coe (hφ : DenseRange φ) (a₀ : A₀) (x : E) :
    extendSMulCLM E hφ (φ a₀) (x : Completion E) = ((a₀ • x : E) : Completion E) := by
  rw [extendSMulCLM_map_apply, coe_smul_along (φ := φ)]
variable (E) in
theorem norm_extendSMulCLM_le (hφ : DenseRange φ) : ‖extendSMulCLM E hφ‖ ≤ 1 :=
  LinearMap.opNorm_extendOfNorm_le hφ zero_le_one fun a₀ ↦ by
    simpa using norm_smulAlongCLM_le E hφ a₀
variable (E) in
theorem norm_extendSMulCLM_apply_le (hφ : DenseRange φ) (a : A) :
    ‖extendSMulCLM E hφ a‖ ≤ ‖a‖ :=
  LinearMap.norm_extendOfNorm_apply_le hφ 1
    (fun a₀ ↦ by simpa using norm_smulAlongCLM_le E hφ a₀) a |>.trans_eq (one_mul _)
theorem norm_extendSMulCLM_apply_apply_le (hφ : DenseRange φ) (a : A) (x : Completion E) :
    ‖extendSMulCLM E hφ a x‖ ≤ ‖a‖ * ‖x‖ :=
  ((extendSMulCLM E hφ a).le_opNorm x).trans <|
    mul_le_mul_of_nonneg_right (norm_extendSMulCLM_apply_le E hφ a) (_root_.norm_nonneg x)

/-- The extended `A`-action satisfies `⟪x, a • y⟫_A = a * ⟪x, y⟫_A` on `Completion E`. -/
@[simp] theorem inner_extendSMulCLM_right (hφ : DenseRange φ) (a : A) (x y : Completion E) :
    inner A x (extendSMulCLM E hφ a y) = a * inner A x y := by
  refine hφ.induction (fun a ⟨a₀, ha₀⟩ ↦ ?_) (isClosed_eq
    (continuous_inner_pair hφ continuous_const
      ((ContinuousLinearMap.apply ℂ (Completion E) y).continuous.comp
        (extendSMulCLM E hφ).continuous)) (continuous_mul_const _)) a
  subst ha₀; rw [extendSMulCLM_map_apply, inner_op_smul_right_completion hφ]

@[simp] theorem inner_extendSMulCLM_left (hφ : DenseRange φ) (a : A) (x y : Completion E) :
    inner A (extendSMulCLM E hφ a x) y = inner A x y * star a := by
  rw [← star_inner_completion hφ y, inner_extendSMulCLM_right hφ, star_mul,
    star_inner_completion hφ]

/-- The extended `A`-action on `Completion E` is multiplicative: `(a * b) • x = a • (b • x)`. -/
@[simp] theorem extendSMulCLM_mul (hφ : DenseRange φ) (a b : A) (x : Completion E) :
    extendSMulCLM E hφ (a * b) x = extendSMulCLM E hφ a (extendSMulCLM E hφ b x) :=
  ext_inner_left_completion hφ fun w ↦ by simp [inner_extendSMulCLM_right hφ, mul_assoc]
variable (E) in
theorem extendSMulCLM_mul_eq_comp (hφ : DenseRange φ) (a b : A) :
    extendSMulCLM E hφ (a * b) = (extendSMulCLM E hφ a).comp (extendSMulCLM E hφ b) := by
  ext x; exact extendSMulCLM_mul hφ a b x

/-- Uniqueness of `extendSMulCLM E hφ`: a continuous linear operator-valued map `Ψ` equals
`extendSMulCLM E hφ` iff it extends the `A₀`-action on vectors from `E`. -/
theorem eq_extendSMulCLM_iff (hφ : DenseRange φ)
    (Ψ : A →L[ℂ] Completion E →L[ℂ] Completion E) :
    Ψ = extendSMulCLM E hφ ↔
      ∀ (a₀ : A₀) (x : E), Ψ (φ a₀) (x : Completion E) = ((a₀ • x : E) : Completion E) := by
  refine ⟨fun h a₀ x ↦ by rw [h, extendSMulCLM_map_coe], fun hΨ ↦ ?_⟩
  symm
  refine LinearMap.extendOfNorm_unique hφ 1
    (fun a₀ ↦ by simpa using norm_smulAlongCLM_le E hφ a₀) Ψ ?_
  ext a₀ x
  exact Completion.induction_on x
    (isClosed_eq (Ψ (φ a₀)).continuous (smulAlongCLM E hφ a₀).continuous)
    fun u ↦ (hΨ a₀ u).trans (coe_smul_along (φ := φ) a₀ u)

variable (E)

/-- Reducible `SMul A (Completion E)` given by `extendSMulCLM E hφ`. Kept as an `abbrev` rather than
a global instance so that when `A₀ = A` it does not compete with `Completion`'s existing `SMul`
instance (with which it agrees by `extendSMulCLM_id_apply`). -/
noncomputable abbrev completedSMul (hφ : DenseRange φ) : SMul A (Completion E) where
  smul a x := extendSMulCLM E hφ a x

/-- Boundedness of `completedSMul E hφ` on `Completion E`. -/
theorem completedIsBoundedSMul (hφ : DenseRange φ) :
    @IsBoundedSMul A (Completion E) _ _ _ _ (completedSMul E hφ) := by
  let _ : SMul A (Completion E) := completedSMul E hφ
  have hsmul (c : A) (z : Completion E) : c • z = extendSMulCLM E hφ c z := rfl
  exact
    { dist_smul_pair' a x y := by
        rw [dist_zero_right, dist_eq_norm, dist_eq_norm, hsmul, hsmul, ← map_sub]
        exact norm_extendSMulCLM_apply_apply_le hφ a (x - y)
      dist_pair_smul' a b x := by
        rw [dist_zero_right, dist_eq_norm, dist_eq_norm, hsmul, hsmul, ← sub_apply, ← map_sub]
        exact norm_extendSMulCLM_apply_apply_le hφ (a - b) x }

/-- Hilbert `A`-module structure on `Completion E` obtained by extending the `A₀`-action along a
dense-range `⋆`-homomorphism `φ : A₀ →⋆ₙₐ[ℂ] A`. -/
noncomputable abbrev completedCStarModule (hφ : DenseRange φ) :
    @CStarModule A (Completion E) _ _ _ _ _ _ (completedSMul E hφ) _ _ := by
  letI : SMul A (Completion E) := completedSMul E hφ
  exact
    { toInner := Completion.toInner
      inner_add_right := inner_add_right_completion hφ _ _ _
      inner_self_nonneg := inner_self_nonneg_completion hφ _
      inner_self := inner_self_eq_zero_completion hφ _
      inner_op_smul_right := inner_extendSMulCLM_right hφ _ _ _
      inner_smul_right_complex := inner_smul_right_complex_completion hφ _ _ _
      star_inner := star_inner_completion hφ
      norm_eq_sqrt_norm_inner_self := norm_eq_sqrt_norm_inner_self_completion hφ }

end ExtendSMul

/-- When `A` already acts on `E`, `extendSMulCLM` along `id` coincides with `Completion E`'s
standard `SMul A (Completion E)`. -/
@[simp] theorem extendSMulCLM_id_apply {A E : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [SeminormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E]
    [TauCeti.SemiCStarModule A E] (a : A) (x : Completion E) :
    extendSMulCLM E (φ := NonUnitalStarAlgHom.id ℂ A) Function.surjective_id.denseRange a x =
      a • x :=
  extendSMulCLM_map_apply Function.surjective_id.denseRange a x

/-- Right-module form of `topologicalClosure_span_range_inner_completion`: completion preserves the
closed complex linear span of `⟨x, y⟩_A = unop (inner Aᵐᵒᵖ x y)`. -/
theorem topologicalClosure_span_range_unop_inner_mulOpposite_completion {A₀ A : Type*} (E : Type*)
    [NonUnitalSemiring A₀] [StarRing A₀] [Module ℂ A₀]
    [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {φ : A₀ →⋆ₙₐ[ℂ] Aᵐᵒᵖ} [SeminormedAddCommGroup E] [NormedSpace ℂ E] [SMul A₀ E]
    [Inner Aᵐᵒᵖ E] [SemiCStarModuleAlong φ E] (hφ : DenseRange φ) :
    (Submodule.span ℂ (Set.range fun p : Completion E × Completion E ↦
        unop (inner Aᵐᵒᵖ p.1 p.2))).topologicalClosure =
      (Submodule.span ℂ
        (Set.range fun p : E × E ↦ unop (inner Aᵐᵒᵖ p.1 p.2))).topologicalClosure := by
  have h := congrArg (fun S : Submodule ℂ Aᵐᵒᵖ ↦
      (MulOpposite.opHomeomorph.symm : Aᵐᵒᵖ ≃ₜ A) '' (S : Set Aᵐᵒᵖ))
    (topologicalClosure_span_range_inner_completion E hφ)
  have himg (s : Set Aᵐᵒᵖ) : (MulOpposite.opHomeomorph.symm : Aᵐᵒᵖ ≃ₜ A) ''
      ((Submodule.span ℂ s).topologicalClosure : Set Aᵐᵒᵖ) =
        ((Submodule.span ℂ (unop '' s)).topologicalClosure : Set A) := by
    rw [Submodule.topologicalClosure_coe, Submodule.topologicalClosure_coe,
      Homeomorph.image_closure]
    congr 1
    have hcoe : ((MulOpposite.opHomeomorph.symm : Aᵐᵒᵖ ≃ₜ A) : Aᵐᵒᵖ → A) =
        ((MulOpposite.opLinearEquiv ℂ (M := A)).symm.toLinearMap : Aᵐᵒᵖ → A) := by ext x; simp
    have hcoe' : ((MulOpposite.opLinearEquiv ℂ (M := A)).symm.toLinearMap : Aᵐᵒᵖ → A) = unop := by
      ext x; simp
    rw [hcoe, ← Submodule.map_coe, Submodule.map_span, hcoe']
  exact SetLike.coe_injective <| by
    simpa only [himg, ← Set.range_comp, Function.comp_def] using h

/-! ### Universal properties along a dense `⋆`-subalgebra homomorphism -/

section ExtendSMulUniversal

variable {A₀ A E F : Type*} [NonUnitalRing A₀] [StarRing A₀] [Module ℂ A₀]
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {φ : A₀ →⋆ₙₐ[ℂ] A} [SeminormedAddCommGroup E] [NormedSpace ℂ E] [SMul A₀ E] [Inner A E]
  [SemiCStarModuleAlong φ E]
  [UniformSpace F] [AddCommGroup F] [IsUniformAddGroup F] [Module ℂ F]
  [UniformContinuousConstSMul ℂ F] [T0Space F] [CompleteSpace F] [SMul A F] [ContinuousSMul A F]
include φ

/-- `f.fromCompletion : Completion E →L[ℂ] F` intertwines `extendSMulCLM` with the `A`-action on
`F` if and only if `f : E →L[ℂ] F` intertwines `A₀` with `A` along `φ` on `E`. -/
theorem fromCompletion_extendSMulCLM_iff (hφ : DenseRange φ) (f : E →L[ℂ] F) :
    (∀ (a : A) (x : Completion E),
        f.fromCompletion (extendSMulCLM E hφ a x) = a • f.fromCompletion x) ↔
      ∀ (a₀ : A₀) (x : E), f (a₀ • x) = φ a₀ • f x := by
  refine ⟨fun h a₀ x ↦ ?_, fun h a x ↦ ?_⟩
  · simpa only [extendSMulCLM_map_coe, ContinuousLinearMap.fromCompletion_apply_coe]
      using h (φ a₀) (x : Completion E)
  · refine hφ.induction (fun a ⟨a₀, ha₀⟩ ↦ ?_) (isClosed_eq
      (f.fromCompletion.continuous.comp
        ((ContinuousLinearMap.apply ℂ (Completion E) x).continuous.comp
          (extendSMulCLM E hφ).continuous)) (by fun_prop)) a
    subst ha₀
    refine Completion.induction_on x
      (isClosed_eq (f.fromCompletion.continuous.comp (extendSMulCLM E hφ (φ a₀)).continuous)
        (by fun_prop)) fun u ↦ ?_
    rw [extendSMulCLM_map_coe, ContinuousLinearMap.fromCompletion_apply_coe,
      ContinuousLinearMap.fromCompletion_apply_coe, h a₀ u]

end ExtendSMulUniversal

section Algebraic

variable {A₀ A E F : Type*} [NonUnitalSemiring A₀] [StarRing A₀] [Module ℂ A₀]
  [NonUnitalRing A] [StarRing A] [Module ℂ A] [StarModule ℂ A] [PartialOrder A] [Norm A]
  (φ : A₀ →⋆ₙₐ[ℂ] A) [SeminormedAddCommGroup E] [NormedSpace ℂ E] [SMul A₀ E] [Inner A E]
  [SemiCStarModuleAlong φ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] [SMul A F] [CStarModule A F]
  (f : E → F) (hf : ∀ x y : E, inner A (f x) (f y) = inner A x y)

/-- Extend any plain inner-product-preserving `f : E → F` into a complete `CStarModule A F` to a
`ℂ`-linear isometry `Completion E →ₗᵢ[ℂ] F`. -/
noncomputable def fromCompletionInnerₗᵢ : Completion E →ₗᵢ[ℂ] F :=
  (linearIsometryOfInner φ f hf).fromCompletion

@[simp] theorem fromCompletionInnerₗᵢ_coe (x : E) :
    fromCompletionInnerₗᵢ φ f hf (x : Completion E) = f x :=
  (LinearIsometry.fromCompletion_apply_coe _ x).trans (linearIsometryOfInner_apply φ f hf x)

/-- Uniqueness in the universal property of `Completion E` for inner-product-preserving maps. -/
theorem eq_fromCompletionInnerₗᵢ_iff (g : Completion E →ₗᵢ[ℂ] F) :
    g = fromCompletionInnerₗᵢ φ f hf ↔ ∀ x : E, g (x : Completion E) = f x :=
  ⟨fun h x ↦ by rw [h, fromCompletionInnerₗᵢ_coe], fun h ↦
    LinearIsometry.toContinuousLinearMap_injective <| by
      rw [fromCompletionInnerₗᵢ, LinearIsometry.toContinuousLinearMap_fromCompletion]
      exact (ContinuousLinearMap.fromCompletion_unique
        (linearIsometryOfInner φ f hf).toContinuousLinearMap g.toContinuousLinearMap fun u ↦ by
          rw [LinearIsometry.coe_toContinuousLinearMap,
            LinearIsometry.coe_toContinuousLinearMap, linearIsometryOfInner_apply, h u]).symm⟩

/-- `fromCompletionInnerₗᵢ` intertwines the `A₀`-action with the `A`-action on `F` along `φ`. -/
@[simp] theorem fromCompletionInnerₗᵢ_smul [UniformContinuousConstSMul A₀ E]
    [ContinuousConstSMul A F] (a₀ : A₀) (x : Completion E) :
    fromCompletionInnerₗᵢ φ f hf (a₀ • x) = φ a₀ • fromCompletionInnerₗᵢ φ f hf x := by
  have hclm := (ContinuousLinearMap.fromCompletion_smul_iff φ
    (linearIsometryOfInner φ f hf).toContinuousLinearMap).mpr fun b₀ u ↦ by
      rw [LinearIsometry.coe_toContinuousLinearMap, linearIsometryOfInner_apply,
        linearIsometryOfInner_apply]
      exact map_smul_along_of_inner φ hf b₀ u
  simpa only [fromCompletionInnerₗᵢ, ← LinearIsometry.coe_toContinuousLinearMap,
    LinearIsometry.toContinuousLinearMap_fromCompletion] using hclm a₀ x

/-- Any plain inner-product-preserving map `f : E → F` with dense range into a complete
`CStarModule A F` induces a `ℂ`-linear isometric equivalence `Completion E ≃ₗᵢ[ℂ] F`. -/
noncomputable def equivOfDenseInner (hdf : DenseRange f) : Completion E ≃ₗᵢ[ℂ] F :=
  LinearIsometryEquiv.ofSurjective (fromCompletionInnerₗᵢ φ f hf) <| by
    have hdense : DenseRange (fromCompletionInnerₗᵢ φ f hf) := hdf.mono <| by
      rintro _ ⟨x, rfl⟩; exact ⟨(x : Completion E), fromCompletionInnerₗᵢ_coe φ f hf x⟩
    have hclosed : IsClosed (Set.range (fromCompletionInnerₗᵢ φ f hf)) :=
      (fromCompletionInnerₗᵢ φ f hf).isometry.isUniformInducing.isComplete_range.isClosed
    exact Set.range_eq_univ.mp (hclosed.closure_eq.symm.trans hdense.closure_eq)

theorem equivOfDenseInner_apply (hdf : DenseRange f) (x : Completion E) :
    equivOfDenseInner φ f hf hdf x = fromCompletionInnerₗᵢ φ f hf x := (rfl)
@[simp] theorem equivOfDenseInner_coe (hdf : DenseRange f) (x : E) :
    equivOfDenseInner φ f hf hdf (x : Completion E) = f x := fromCompletionInnerₗᵢ_coe φ f hf x
@[simp] theorem equivOfDenseInner_symm_apply (hdf : DenseRange f) (x : E) :
    (equivOfDenseInner φ f hf hdf).symm (f x) = (x : Completion E) :=
  (equivOfDenseInner φ f hf hdf).symm_apply_eq.mpr (equivOfDenseInner_coe φ f hf hdf x).symm
@[simp] theorem equivOfDenseInner_smul [UniformContinuousConstSMul A₀ E] [ContinuousConstSMul A F]
    (hdf : DenseRange f) (a₀ : A₀) (x : Completion E) :
    equivOfDenseInner φ f hf hdf (a₀ • x) = φ a₀ • equivOfDenseInner φ f hf hdf x :=
  fromCompletionInnerₗᵢ_smul φ f hf a₀ x

end Algebraic

section CStar

variable {A₀ A E F : Type*} [NonUnitalSemiring A₀] [StarRing A₀] [Module ℂ A₀]
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {φ : A₀ →⋆ₙₐ[ℂ] A} [SeminormedAddCommGroup E] [NormedSpace ℂ E] [SMul A₀ E] [Inner A E]
  [SemiCStarModuleAlong φ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] [SMul A F] [CStarModule A F]
  (hφ : DenseRange φ) (f : E → F) (hf : ∀ x y : E, inner A (f x) (f y) = inner A x y)
include hφ

@[simp] theorem inner_fromCompletionInnerₗᵢ (x y : Completion E) :
    inner A (fromCompletionInnerₗᵢ φ f hf x) (fromCompletionInnerₗᵢ φ f hf y) = inner A x y := by
  refine Completion.induction_on₂ x y (isClosed_eq
    ((CStarModule.continuous_inner (A := A) (E := F)).comp
      (((fromCompletionInnerₗᵢ φ f hf).continuous.comp continuous_fst).prodMk
        ((fromCompletionInnerₗᵢ φ f hf).continuous.comp continuous_snd)))
    (continuous_inner_completion hφ)) fun u v ↦ ?_
  rw [fromCompletionInnerₗᵢ_coe, fromCompletionInnerₗᵢ_coe, inner_coe_coe hφ, hf]
@[simp] theorem inner_equivOfDenseInner (hdf : DenseRange f) (x y : Completion E) :
    inner A (equivOfDenseInner φ f hf hdf x) (equivOfDenseInner φ f hf hdf y) = inner A x y :=
  inner_fromCompletionInnerₗᵢ hφ f hf x y
@[simp] theorem inner_equivOfDenseInner_symm (hdf : DenseRange f) (x y : F) :
    inner A ((equivOfDenseInner φ f hf hdf).symm x)
      ((equivOfDenseInner φ f hf hdf).symm y) = inner A x y := by
  rw [← inner_equivOfDenseInner hφ f hf hdf, LinearIsometryEquiv.apply_symm_apply,
    LinearIsometryEquiv.apply_symm_apply]

end CStar

section CStarExtendSMul

variable {A₀ A E F : Type*} [NonUnitalRing A₀] [StarRing A₀] [Module ℂ A₀]
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {φ : A₀ →⋆ₙₐ[ℂ] A} [SeminormedAddCommGroup E] [NormedSpace ℂ E] [SMul A₀ E] [Inner A E]
  [SemiCStarModuleAlong φ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] [SMul A F] [CStarModule A F]
  (hφ : DenseRange φ) (f : E → F) (hf : ∀ x y : E, inner A (f x) (f y) = inner A x y)
include hφ

@[simp] theorem fromCompletionInnerₗᵢ_extendSMulCLM (a : A) (x : Completion E) :
    fromCompletionInnerₗᵢ φ f hf (extendSMulCLM E hφ a x) =
      a • fromCompletionInnerₗᵢ φ f hf x := by
  rw [fromCompletionInnerₗᵢ, ← LinearIsometry.coe_toContinuousLinearMap,
    LinearIsometry.toContinuousLinearMap_fromCompletion]
  exact (fromCompletion_extendSMulCLM_iff hφ
    (linearIsometryOfInner φ f hf).toContinuousLinearMap).mpr
    (fun a₀ u ↦ by
      rw [LinearIsometry.coe_toContinuousLinearMap, linearIsometryOfInner_apply,
        linearIsometryOfInner_apply]
      exact map_smul_along_of_inner φ hf a₀ u) a x
@[simp] theorem equivOfDenseInner_extendSMulCLM (hdf : DenseRange f) (a : A) (x : Completion E) :
    equivOfDenseInner φ f hf hdf (extendSMulCLM E hφ a x) =
      a • equivOfDenseInner φ f hf hdf x :=
  fromCompletionInnerₗᵢ_extendSMulCLM hφ f hf a x
@[simp] theorem equivOfDenseInner_symm_smul (hdf : DenseRange f) (a : A) (y : F) :
    (equivOfDenseInner φ f hf hdf).symm (a • y) =
      extendSMulCLM E hφ a ((equivOfDenseInner φ f hf hdf).symm y) :=
  (equivOfDenseInner φ f hf hdf).symm_apply_eq.mpr <| by
    rw [equivOfDenseInner_extendSMulCLM hφ f hf hdf, LinearIsometryEquiv.apply_symm_apply]

end CStarExtendSMul
end TauCeti.SemiCStarModuleAlong

/-! ### Global `CStarModule` instance on `UniformSpace.Completion` -/

namespace UniformSpace.Completion

variable {A E : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [SeminormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [TauCeti.SemiCStarModule A E]

@[simp] theorem inner_coe_of_semiCStarModule (x y : E) :
    inner A (x : Completion E) (y : Completion E) = inner A x y :=
  TauCeti.SemiCStarModuleAlong.inner_coe_coe
    (φ := NonUnitalStarAlgHom.id ℂ A) Function.surjective_id.denseRange x y

open TauCeti.SemiCStarModuleAlong in
/-- The completion of any pre-Hilbert or positive semidefinite `A`-module is a Hilbert `A`-module
(`CStarModule A (Completion E)`). -/
noncomputable instance instCStarModule : CStarModule A (Completion E) :=
  let h : DenseRange (NonUnitalStarAlgHom.id ℂ A) := Function.surjective_id.denseRange
  { toInner := Completion.toInner
    inner_add_right := inner_add_right_completion h _ _ _
    inner_self_nonneg := inner_self_nonneg_completion h _
    inner_self := inner_self_eq_zero_completion h _
    inner_op_smul_right := inner_op_smul_right_completion h _ _ _
    inner_smul_right_complex := inner_smul_right_complex_completion h _ _ _
    star_inner := star_inner_completion h
    norm_eq_sqrt_norm_inner_self := norm_eq_sqrt_norm_inner_self_completion h }

open scoped ComplexOrder in
-- Verify definitional equality with `WithCStarModule.instCStarModuleComplex` on `Completion H`.
example {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    (instCStarModule : CStarModule ℂ (Completion H)) = WithCStarModule.instCStarModuleComplex := by
  with_reducible_and_instances rfl

/-- `separationQuotientEquiv ℂ E` preserves `A`-valued inner products. -/
@[simp] theorem inner_separationQuotientEquiv (x y : Completion (SeparationQuotient E)) :
    inner A (separationQuotientEquiv ℂ E x) (separationQuotientEquiv ℂ E y) = inner A x y := by
  refine Completion.induction_on₂ x y (isClosed_eq
    ((CStarModule.continuous_inner (A := A) (E := Completion E)).comp
      (((separationQuotientEquiv ℂ E).continuous.comp continuous_fst).prodMk
        ((separationQuotientEquiv ℂ E).continuous.comp continuous_snd)))
    (CStarModule.continuous_inner (A := A) (E := Completion (SeparationQuotient E))))
    (SeparationQuotient.surjective_mk.forall₂.2 fun u v ↦ ?_)
  rw [separationQuotientEquiv_coe_mk, separationQuotientEquiv_coe_mk,
    inner_coe_of_semiCStarModule, ← SeparationQuotient.inner_mk_mk_of_semiCStarModule (A := A)]
  exact (inner_coe_of_semiCStarModule (A := A) (E := SeparationQuotient E) _ _).symm

/-- The inverse of `separationQuotientEquiv ℂ E` preserves `A`-valued inner products. -/
@[simp] theorem inner_separationQuotientEquiv_symm (x y : Completion E) :
    inner A ((separationQuotientEquiv ℂ E).symm x)
      ((separationQuotientEquiv ℂ E).symm y) = inner A x y := by
  rw [← inner_separationQuotientEquiv, LinearIsometryEquiv.apply_symm_apply,
    LinearIsometryEquiv.apply_symm_apply]

end UniformSpace.Completion

/-! ### Fullness and completion universal properties for `TauCeti.SemiCStarModule` -/

namespace TauCeti.SemiCStarModule

/-- Completion preserves the closed complex linear span of inner products, so `Completion E` is
full if and only if `E` has dense inner-product span. -/
theorem topologicalClosure_span_range_inner_completion {A : Type*} (E : Type*)
    [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [SeminormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [SemiCStarModule A E] :
    (Submodule.span ℂ
        (Set.range fun p : Completion E × Completion E ↦ inner A p.1 p.2)).topologicalClosure =
      (Submodule.span ℂ (Set.range fun p : E × E ↦ inner A p.1 p.2)).topologicalClosure :=
  SemiCStarModuleAlong.topologicalClosure_span_range_inner_completion
    (φ := .id ℂ A) E Function.surjective_id.denseRange

/-- Right-module form of `topologicalClosure_span_range_inner_completion`: completing a right
module preserves the closed complex linear span of `⟨x, y⟩_A = unop (inner Aᵐᵒᵖ x y)`. -/
theorem topologicalClosure_span_range_unop_inner_mulOpposite_completion {A : Type*} (E : Type*)
    [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [SeminormedAddCommGroup E] [NormedSpace ℂ E] [SMul Aᵐᵒᵖ E] [SemiCStarModule Aᵐᵒᵖ E] :
    (Submodule.span ℂ (Set.range fun p : Completion E × Completion E ↦
        unop (inner Aᵐᵒᵖ p.1 p.2))).topologicalClosure =
      (Submodule.span ℂ
        (Set.range fun p : E × E ↦ unop (inner Aᵐᵒᵖ p.1 p.2))).topologicalClosure :=
  SemiCStarModuleAlong.topologicalClosure_span_range_unop_inner_mulOpposite_completion
    (φ := .id ℂ Aᵐᵒᵖ) E Function.surjective_id.denseRange

section Algebraic

variable {A E F : Type*} [NonUnitalRing A] [StarRing A] [Module ℂ A] [StarModule ℂ A]
  [PartialOrder A] [Norm A]
  [SeminormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [SemiCStarModule A E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] [SMul A F] [CStarModule A F]
  (f : E → F) (hf : ∀ x y : E, inner A (f x) (f y) = inner A x y)

/-- Extend any plain inner-product-preserving function `f : E → F` into a complete
`CStarModule A F` to a `ℂ`-linear isometry `Completion E →ₗᵢ[ℂ] F`. -/
noncomputable def fromCompletionInnerₗᵢ : Completion E →ₗᵢ[ℂ] F :=
  SemiCStarModuleAlong.fromCompletionInnerₗᵢ (.id ℂ A) f hf

@[simp] theorem fromCompletionInnerₗᵢ_coe (x : E) :
    fromCompletionInnerₗᵢ f hf (x : Completion E) = f x :=
  SemiCStarModuleAlong.fromCompletionInnerₗᵢ_coe (.id ℂ A) f hf x
theorem eq_fromCompletionInnerₗᵢ_iff (g : Completion E →ₗᵢ[ℂ] F) :
    g = fromCompletionInnerₗᵢ f hf ↔ ∀ x : E, g (x : Completion E) = f x :=
  SemiCStarModuleAlong.eq_fromCompletionInnerₗᵢ_iff (.id ℂ A) f hf g
@[simp] theorem fromCompletionInnerₗᵢ_smul [UniformContinuousConstSMul A E]
    [ContinuousConstSMul A F] (a : A) (x : Completion E) :
    fromCompletionInnerₗᵢ f hf (a • x) = a • fromCompletionInnerₗᵢ f hf x :=
  SemiCStarModuleAlong.fromCompletionInnerₗᵢ_smul (.id ℂ A) f hf a x

/-- Any plain inner-product-preserving function `f : E → F` with dense range into a complete
`CStarModule A F` induces a `ℂ`-linear isometric equivalence `Completion E ≃ₗᵢ[ℂ] F`. Under
`[NonUnitalCStarAlgebra A] [StarOrderedRing A]` it preserves `A`-valued inner products
(`inner_equivOfDenseInner`), and under `[UniformContinuousConstSMul A E] [ContinuousConstSMul A F]`
it commutes with the `A`-action (`equivOfDenseInner_smul`). -/
noncomputable def equivOfDenseInner (hdf : DenseRange f) : Completion E ≃ₗᵢ[ℂ] F :=
  SemiCStarModuleAlong.equivOfDenseInner (.id ℂ A) f hf hdf

theorem equivOfDenseInner_apply (hdf : DenseRange f) (x : Completion E) :
    equivOfDenseInner f hf hdf x = fromCompletionInnerₗᵢ f hf x := (rfl)
@[simp] theorem equivOfDenseInner_coe (hdf : DenseRange f) (x : E) :
    equivOfDenseInner f hf hdf (x : Completion E) = f x := fromCompletionInnerₗᵢ_coe f hf x
@[simp] theorem equivOfDenseInner_symm_apply (hdf : DenseRange f) (x : E) :
    (equivOfDenseInner f hf hdf).symm (f x) = (x : Completion E) :=
  SemiCStarModuleAlong.equivOfDenseInner_symm_apply (.id ℂ A) f hf hdf x
@[simp] theorem equivOfDenseInner_smul [UniformContinuousConstSMul A E] [ContinuousConstSMul A F]
    (hdf : DenseRange f) (a : A) (x : Completion E) :
    equivOfDenseInner f hf hdf (a • x) = a • equivOfDenseInner f hf hdf x :=
  fromCompletionInnerₗᵢ_smul f hf a x
@[simp] theorem equivOfDenseInner_symm_smul [UniformContinuousConstSMul A E]
    [ContinuousConstSMul A F] (hdf : DenseRange f) (a : A) (y : F) :
    (equivOfDenseInner f hf hdf).symm (a • y) = a • (equivOfDenseInner f hf hdf).symm y :=
  (equivOfDenseInner f hf hdf).symm_apply_eq.mpr <| by
    rw [equivOfDenseInner_smul, LinearIsometryEquiv.apply_symm_apply]

end Algebraic

section CStar

variable {A E F : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [SeminormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [SemiCStarModule A E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] [SMul A F] [CStarModule A F]
  (f : E → F) (hf : ∀ x y : E, inner A (f x) (f y) = inner A x y)

@[simp] theorem inner_fromCompletionInnerₗᵢ (x y : Completion E) :
    inner A (fromCompletionInnerₗᵢ f hf x) (fromCompletionInnerₗᵢ f hf y) = inner A x y :=
  SemiCStarModuleAlong.inner_fromCompletionInnerₗᵢ Function.surjective_id.denseRange f hf x y
@[simp] theorem inner_equivOfDenseInner (hdf : DenseRange f) (x y : Completion E) :
    inner A (equivOfDenseInner f hf hdf x) (equivOfDenseInner f hf hdf y) = inner A x y :=
  inner_fromCompletionInnerₗᵢ f hf x y
@[simp] theorem inner_equivOfDenseInner_symm (hdf : DenseRange f) (x y : F) :
    inner A ((equivOfDenseInner f hf hdf).symm x)
      ((equivOfDenseInner f hf hdf).symm y) = inner A x y :=
  SemiCStarModuleAlong.inner_equivOfDenseInner_symm Function.surjective_id.denseRange f hf hdf x y

end CStar

end TauCeti.SemiCStarModule

/-! ### Completion of a dense nonunital `⋆`-subalgebra as a right Hilbert `A`-module -/

namespace NonUnitalStarSubalgebra

open TauCeti.SemiCStarModuleAlong NonUnitalStarSubalgebraClass

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (S : NonUnitalStarSubalgebra ℂ A) (hS : Dense (S : Set A))

/-- The completion of a dense nonunital `⋆`-subalgebra `S ⊆ A` (viewed as a right `S`-module with
positivity and norm measured in `A`) is canonically unitarily equivalent to the right Hilbert
self-module `A`, intertwining the extended right `A`-action with multiplication in `A`. -/
noncomputable def completionEquiv : Completion S ≃ₗᵢ[ℂ] A :=
  equivOfDenseInner (subtype S).op Subtype.val
    (fun _ _ ↦ by rw [CStarModule.inner_mulOpposite, inner_mulOpposite_apply])
    (denseRange_subtypeVal.mpr hS)

@[simp] theorem completionEquiv_coe (x : S) : S.completionEquiv hS (x : Completion S) = (x : A) :=
  equivOfDenseInner_coe _ _ _ _ x
@[simp] theorem completionEquiv_symm_coe (x : S) :
    (S.completionEquiv hS).symm (x : A) = (x : Completion S) :=
  equivOfDenseInner_symm_apply _ _ _ _ x
@[simp] theorem inner_completionEquiv (x y : Completion S) :
    inner Aᵐᵒᵖ (S.completionEquiv hS x) (S.completionEquiv hS y) = inner Aᵐᵒᵖ x y :=
  inner_equivOfDenseInner ((denseRange_subtype_op_iff S).mpr hS) _ _ _ x y
@[simp] theorem inner_completionEquiv_symm (x y : A) :
    inner Aᵐᵒᵖ ((S.completionEquiv hS).symm x) ((S.completionEquiv hS).symm y) = inner Aᵐᵒᵖ x y :=
  inner_equivOfDenseInner_symm ((denseRange_subtype_op_iff S).mpr hS) _ _ _ x y
@[simp] theorem completionEquiv_extendSMulCLM (a : A) (x : Completion S) :
    S.completionEquiv hS
        (extendSMulCLM S ((denseRange_subtype_op_iff S).mpr hS) (op a) x) =
      S.completionEquiv hS x * a :=
  (equivOfDenseInner_extendSMulCLM ((denseRange_subtype_op_iff S).mpr hS) _ _ _ (op a) x).trans
    (op_smul_eq_mul a _)
@[simp] theorem completionEquiv_symm_mul (y a : A) :
    (S.completionEquiv hS).symm (y * a) =
      extendSMulCLM S ((denseRange_subtype_op_iff S).mpr hS) (op a)
        ((S.completionEquiv hS).symm y) := by
  rw [← op_smul_eq_mul a y]
  exact equivOfDenseInner_symm_smul ((denseRange_subtype_op_iff S).mpr hS) _ _ _ (op a) y

end NonUnitalStarSubalgebra

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Extend
public import TauCeti.Analysis.CStarAlgebra.Module.Semidefinite
public import TauCeti.Topology.Algebra.NonUnitalStarAlgebra

/-!
# Completions of pre-Hilbert and positive semidefinite C⋆-modules

Completing a pre-Hilbert C⋆-module or a positive semidefinite C⋆-module produces a Hilbert
C⋆-module, canonically isometric to the completion of its separation quotient. When a module `E` is
defined only over a dense `⋆`-subalgebra `A₀` of a C⋆-algebra `A` (with positivity and seminorm
measured in `A` along `φ : A₀ →⋆ₙₐ[ℂ] A`), its completion `UniformSpace.Completion E` carries a
unique continuous `A`-action extending the `A₀`-action and making `Completion E` a Hilbert
`A`-module.

This file establishes:

* `TauCeti.SemiCStarModuleAlong.semiCStarModuleAlong_completion`: `Completion E` inherits
  `SemiCStarModuleAlong φ` with definite `A`-valued inner product (`inner_self_eq_zero_completion`).
* `TauCeti.SemiCStarModuleAlong.extendSMulCLM`: continuous extension of the `A₀`-action along a
  dense-range `φ : A₀ →⋆ₙₐ[ℂ] A` to a contractive multiplicative action
  `A →L[ℂ] Completion E →L[ℂ] Completion E`, together with uniqueness (`eq_extendSMulCLM_iff`) and
  the resulting `CStarModule A (Completion E)` (`completedCStarModule`).
* `UniformSpace.Completion.instCStarModule`: global `CStarModule A (Completion E)` instance for any
  seminormed `SemiCStarModule A E` (covering both pre-Hilbert modules and positive semidefinite
  modules, left or right via `Aᵐᵒᵖ`).
* Compatibility of `UniformSpace.Completion.separationQuotientEquiv` with the `A`-action and
  `A`-valued inner product, and invariance of the closed linear span of inner products (fullness)
  under completion.
* Universal properties of `Completion E` into any complete `CStarModule A F` for bounded module maps
  (`TauCeti.SemiCStarModuleAlong.fromCompletion_extendSMulCLM_iff`,
  `ContinuousLinearMap.fromCompletion_smul_iff`, `ContinuousLinearMap.comp_toComplL_eq_iff`) and for
  plain inner-product-preserving maps (`TauCeti.SemiCStarModuleAlong.fromCompletionInnerₗᵢ`,
  `UniformSpace.Completion.fromCompletionInnerₗᵢ`, `UniformSpace.Completion.equivOfDenseInner`).
* `NonUnitalStarSubalgebra.completionEquiv`: for any dense nonunital `⋆`-subalgebra `S` of `A`, the
  completion `Completion S` is unitarily equivalent as a right Hilbert `A`-module to `A`.

## References

* E. Christopher Lance, *Hilbert C⋆-Modules: A Toolkit for Operator Algebraists*, Chapter 1.
* Iain Raeburn and Dana P. Williams, *Morita Equivalence and Continuous-Trace C⋆-Algebras*,
  Chapter 2.
* `Mathlib.Analysis.InnerProductSpace.Completion` (`UniformSpace.Completion.toInner`,
  `UniformSpace.Completion.continuous_inner`), which provides the extended inner product and the
  `ℤ`-bilinear extension pattern adapted here to C⋆-algebra-valued inner products, and
  `Mathlib.Analysis.Normed.Operator.Extend` (`LinearMap.extendOfNorm`), which extends the dense
  subalgebra action to the C⋆-completion.
-/

public section

open MulOpposite UniformSpace Filter Topology

namespace TauCeti.SemiCStarModuleAlong

/-! ### Inner product, definiteness, and extended action on `Completion E` -/

section CompletionAlong

variable {A₀ A E : Type*} [NonUnitalRing A₀] [StarRing A₀] [Module ℂ A₀]
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
    { toFun x :=
        { toFun y := inner A x y
          map_zero' := inner_zero_right φ x
          map_add' _ _ := inner_add_right (φ := φ) }
      map_zero' := by ext y; exact inner_zero_left φ y
      map_add' x y := by ext z; exact inner_add_left φ x y z }
  have hcont : Continuous (fun p : E × E ↦ inner' p.1 p.2) := continuous_inner hφ
  exact (Completion.isDenseInducing_toCompl E).extend_Z_bilin
    (Completion.isDenseInducing_toCompl E) hcont

private lemma continuous_inner_pair {α : Type*} [TopologicalSpace α] (hφ : DenseRange φ)
    {f g : α → Completion E} (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun a ↦ inner A (f a) (g a)) :=
  (continuous_inner_completion hφ).comp (hf.prodMk hg)

/-- The norm on `Completion E` is `√‖⟪x, x⟫_A‖`. -/
theorem norm_eq_sqrt_norm_inner_self_completion (hφ : DenseRange φ) (x : Completion E) :
    ‖x‖ = √‖inner A x x‖ := by
  refine Completion.induction_on x
    (isClosed_eq continuous_norm (Real.continuous_sqrt.comp
      (continuous_norm.comp (continuous_inner_pair hφ continuous_id continuous_id)))) fun a ↦ ?_
  rw [Completion.norm_coe, inner_coe_coe hφ, norm_eq_sqrt_norm_inner_self (φ := φ) a]

/-- Self-inner products on `Completion E` are nonnegative in `A`. -/
theorem inner_self_nonneg_completion (hφ : DenseRange φ) (x : Completion E) :
    0 ≤ inner A x x := by
  refine Completion.induction_on x
    (isClosed_le continuous_const (continuous_inner_pair hφ continuous_id continuous_id)) fun a ↦ ?_
  rw [inner_coe_coe hφ]
  exact inner_self_nonneg (φ := φ)

/-- Additivity of the `A`-valued inner product on `Completion E` in the right variable. -/
theorem inner_add_right_completion (hφ : DenseRange φ) (x y z : Completion E) :
    inner A x (y + z) = inner A x y + inner A x z := by
  refine Completion.induction_on₃ x y z
    (isClosed_eq
      (continuous_inner_pair hφ continuous_fst (continuous_snd.fst.add continuous_snd.snd))
      ((continuous_inner_pair hφ continuous_fst continuous_snd.fst).add
        (continuous_inner_pair hφ continuous_fst continuous_snd.snd)))
    fun a b c ↦ ?_
  rw [← Completion.coe_add, inner_coe_coe hφ, inner_coe_coe hφ, inner_coe_coe hφ,
    inner_add_right (φ := φ)]

/-- Conjugate symmetry `⟪x, y⟫_A⋆ = ⟪y, x⟫_A` on `Completion E`. -/
theorem star_inner_completion (hφ : DenseRange φ) (x y : Completion E) :
    star (inner A x y) = inner A y x := by
  refine Completion.induction_on₂ x y
    (isClosed_eq (continuous_star.comp (continuous_inner_pair hφ continuous_fst continuous_snd))
      (continuous_inner_pair hφ continuous_snd continuous_fst))
    fun a b ↦ ?_
  rw [inner_coe_coe hφ, inner_coe_coe hφ, star_inner (φ := φ)]

/-- Complex homogeneity in the right variable on `Completion E`. -/
theorem inner_smul_right_complex_completion (hφ : DenseRange φ) (c : ℂ) (x y : Completion E) :
    inner A x (c • y) = c • inner A x y := by
  refine Completion.induction_on₂ x y
    (isClosed_eq
      (continuous_inner_pair hφ continuous_fst (continuous_snd.const_smul c))
      ((continuous_inner_pair hφ continuous_fst continuous_snd).const_smul c))
    fun a b ↦ ?_
  rw [← Completion.coe_smul, inner_coe_coe hφ, inner_coe_coe hφ,
    inner_smul_right_complex (φ := φ)]

/-- Definiteness of the `A`-valued inner product on `Completion E`: `⟪x, x⟫_A = 0 ↔ x = 0`. -/
theorem inner_self_eq_zero_completion (hφ : DenseRange φ) (x : Completion E) :
    inner A x x = 0 ↔ x = 0 := by
  refine ⟨fun hx ↦ norm_eq_zero.mp ?_, fun hx ↦ ?_⟩
  · rw [norm_eq_sqrt_norm_inner_self_completion hφ x, hx, _root_.norm_zero, Real.sqrt_zero]
  · subst hx
    have h0 : inner A (0 : Completion E) 0 + inner A (0 : Completion E) 0 =
        inner A (0 : Completion E) 0 + 0 := by
      rw [← inner_add_right_completion hφ, add_zero, add_zero]
    exact add_left_cancel h0

/-- Vectors in `Completion E` with equal inner products against all `w : Completion E` are equal. -/
theorem ext_inner_left_completion (hφ : DenseRange φ) {x y : Completion E}
    (h : ∀ w : Completion E, inner A w x = inner A w y) : x = y := by
  rw [← sub_eq_zero, ← inner_self_eq_zero_completion hφ]
  have hneg (u v : Completion E) : inner A u (-v) = -inner A u v := by
    apply eq_neg_of_add_eq_zero_left
    rw [← inner_add_right_completion hφ, neg_add_cancel]
    have h0 : inner A u 0 + inner A u 0 = inner A u 0 + 0 := by
      rw [← inner_add_right_completion hφ, add_zero, add_zero]
    exact add_left_cancel h0
  rw [sub_eq_add_neg, inner_add_right_completion hφ, hneg, h, add_neg_cancel]

/-- The coercion `E → Completion E` commutes with the `A₀`-action, without assuming `DistribSMul`
on null vectors. -/
theorem coe_smul_along (a₀ : A₀) (x : E) :
    ((a₀ • x : E) : Completion E) = a₀ • (x : Completion E) := by
  let _ := uniformContinuousConstSMul (φ := φ) (E := E)
  exact Completion.coe_smul a₀ x

/-- Compatibility `⟪x, a₀ • y⟫_A = φ a₀ * ⟪x, y⟫_A` on `Completion E`. -/
theorem inner_op_smul_right_completion (hφ : DenseRange φ) (a₀ : A₀) (x y : Completion E) :
    inner A x (a₀ • y) = φ a₀ * inner A x y := by
  refine Completion.induction_on₂ x y
    (isClosed_eq
      (continuous_inner_pair hφ continuous_fst (continuous_snd.const_smul a₀))
      ((continuous_const_mul (φ a₀)).comp
        (continuous_inner_pair hφ continuous_fst continuous_snd)))
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

/-- Norm bound `‖a₀ • x‖ ≤ ‖φ a₀‖ * ‖x‖` for the `A₀`-action on `Completion E`. -/
theorem norm_smul_along_completion_le (a₀ : A₀) (x : Completion E) :
    ‖a₀ • x‖ ≤ ‖φ a₀‖ * ‖x‖ := by
  refine Completion.induction_on x
    (isClosed_le (continuous_norm.comp (continuous_const_smul a₀))
      ((continuous_const_mul _).comp continuous_norm)) fun u ↦ ?_
  rw [← coe_smul_along (φ := φ) a₀ u, Completion.norm_coe, Completion.norm_coe]
  exact norm_smul_le φ a₀ u

variable (E) in
/-- The `A₀`-action on `Completion E` bundled as a `ℂ`-linear map into bounded operators
`Completion E →L[ℂ] Completion E`. Even when `E` is non-separated and the `A₀`-action on `E` fails
to distribute on null vectors, definiteness of the completed inner product makes the induced action
on `Completion E` strictly `ℂ`-linear in both variables. -/
noncomputable def smulAlongCLM (hφ : DenseRange φ) :
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
    ext x
    exact ext_inner_left_completion hφ fun w ↦ by
      simp [inner_add_right_completion hφ, inner_op_smul_right_completion hφ, add_mul]
  map_smul' c a₀ := by
    ext x
    exact ext_inner_left_completion hφ fun w ↦ by
      simp [inner_smul_right_complex_completion hφ, inner_op_smul_right_completion hφ,
        smul_mul_assoc]

@[simp]
theorem smulAlongCLM_apply (hφ : DenseRange φ) (a₀ : A₀) (x : Completion E) :
    smulAlongCLM E hφ a₀ x = a₀ • x :=
  (rfl)

variable (E) in
theorem norm_smulAlongCLM_le (hφ : DenseRange φ) (a₀ : A₀) :
    ‖smulAlongCLM E hφ a₀‖ ≤ ‖φ a₀‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (_root_.norm_nonneg _) fun x ↦
    norm_smul_along_completion_le (φ := φ) a₀ x

variable (E) in
/-- Continuous extension of the `A₀`-action along `φ : A₀ →⋆ₙₐ[ℂ] A` (`DenseRange φ`) to a
contractive `ℂ`-linear action `A →L[ℂ] Completion E →L[ℂ] Completion E` of the C⋆-completion `A`. -/
noncomputable def extendSMulCLM (hφ : DenseRange φ) :
    A →L[ℂ] Completion E →L[ℂ] Completion E :=
  (smulAlongCLM E hφ).extendOfNorm (φ : A₀ →ₗ[ℂ] A)

variable (E) in
@[simp]
theorem extendSMulCLM_map (hφ : DenseRange φ) (a₀ : A₀) :
    extendSMulCLM E hφ (φ a₀) = smulAlongCLM E hφ a₀ :=
  LinearMap.extendOfNorm_eq hφ
    ⟨1, fun b₀ ↦ by simpa using norm_smulAlongCLM_le E hφ b₀⟩ a₀

theorem extendSMulCLM_map_apply (hφ : DenseRange φ) (a₀ : A₀) (x : Completion E) :
    extendSMulCLM E hφ (φ a₀) x = a₀ • x := by
  rw [extendSMulCLM_map, smulAlongCLM_apply]

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
@[simp]
theorem inner_extendSMulCLM_right (hφ : DenseRange φ) (a : A) (x y : Completion E) :
    inner A x (extendSMulCLM E hφ a y) = a * inner A x y := by
  refine hφ.induction (fun a ⟨a₀, ha₀⟩ ↦ ?_)
    (isClosed_eq
      (continuous_inner_pair hφ continuous_const
        ((ContinuousLinearMap.apply ℂ (Completion E) y).continuous.comp
          (extendSMulCLM E hφ).continuous))
      (continuous_mul_const _)) a
  subst ha₀
  rw [extendSMulCLM_map_apply, inner_op_smul_right_completion hφ]

@[simp]
theorem inner_extendSMulCLM_left (hφ : DenseRange φ) (a : A) (x y : Completion E) :
    inner A (extendSMulCLM E hφ a x) y = inner A x y * star a := by
  rw [← star_inner_completion hφ y, inner_extendSMulCLM_right hφ, star_mul,
    star_inner_completion hφ]

/-- The extended `A`-action on `Completion E` is multiplicative: `(a * b) • x = a • (b • x)`. -/
@[simp]
theorem extendSMulCLM_mul (hφ : DenseRange φ) (a b : A) (x : Completion E) :
    extendSMulCLM E hφ (a * b) x = extendSMulCLM E hφ a (extendSMulCLM E hφ b x) :=
  ext_inner_left_completion hφ fun w ↦ by
    simp [inner_extendSMulCLM_right hφ, mul_assoc]

variable (E) in
theorem extendSMulCLM_mul_eq_comp (hφ : DenseRange φ) (a b : A) :
    extendSMulCLM E hφ (a * b) = (extendSMulCLM E hφ a).comp (extendSMulCLM E hφ b) := by
  ext x
  exact extendSMulCLM_mul hφ a b x

/-- Uniqueness of the extended `A`-action on `Completion E`: a continuous linear operator-valued map
`Ψ : A →L[ℂ] Completion E →L[ℂ] Completion E` equals `extendSMulCLM E hφ` if and only if it extends
the `A₀`-action on vectors from `E`. -/
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

variable (E) in
/-- Reducible `SMul A (Completion E)` given by `extendSMulCLM E hφ`. Kept as an `abbrev` rather than
a global instance so that when `A₀ = A` it does not compete with `Completion`'s existing `SMul`
instance (with which it agrees by `UniformSpace.Completion.extendSMulCLM_id_apply`). -/
noncomputable abbrev completedSMul (hφ : DenseRange φ) : SMul A (Completion E) where
  smul a x := extendSMulCLM E hφ a x

variable (E) in
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

variable (E) in
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

variable (E) in
/-- Completion preserves the closed complex linear span of `A`-valued inner products. -/
theorem topologicalClosure_span_range_inner_completion (hφ : DenseRange φ) :
    (Submodule.span ℂ
        (Set.range fun p : Completion E × Completion E ↦ inner A p.1 p.2)).topologicalClosure =
      (Submodule.span ℂ (Set.range fun p : E × E ↦ inner A p.1 p.2)).topologicalClosure := by
  refine le_antisymm
    (Submodule.topologicalClosure_minimal _ ?_ (Submodule.isClosed_topologicalClosure _))
    (Submodule.topologicalClosure_mono <| Submodule.span_mono ?_)
  · rw [Submodule.span_le]
    rintro _ ⟨⟨x, y⟩, rfl⟩
    refine Completion.induction_on₂ x y
      ((Submodule.isClosed_topologicalClosure _).preimage (continuous_inner_completion hφ))
      fun u v ↦ ?_
    simp only [inner_coe_coe hφ]
    exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨(u, v), rfl⟩)
  · rintro _ ⟨⟨u, v⟩, rfl⟩
    exact ⟨((u : Completion E), (v : Completion E)), inner_coe_coe hφ u v⟩

end CompletionAlong

/-! ### Universal properties along a dense `⋆`-subalgebra homomorphism -/

section UniversalAlong

variable {A₀ A E F : Type*} [NonUnitalRing A₀] [StarRing A₀] [Module ℂ A₀]
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {φ : A₀ →⋆ₙₐ[ℂ] A} [SeminormedAddCommGroup E] [NormedSpace ℂ E] [SMul A₀ E] [Inner A E]
  [SemiCStarModuleAlong φ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] [SMul A F] [CStarModule A F]

include φ

/-- A bounded `ℂ`-linear map `f : E →L[ℂ] F` into a complete `CStarModule A F` extends to a bounded
map `f.fromCompletion : Completion E →L[ℂ] F` intertwining the extended `A`-action `extendSMulCLM`
if and only if `f` intertwines `A₀` with `A` along `φ` on `E`. -/
theorem fromCompletion_extendSMulCLM_iff (hφ : DenseRange φ) (f : E →L[ℂ] F) :
    (∀ (a : A) (x : Completion E),
        f.fromCompletion (extendSMulCLM E hφ a x) = a • f.fromCompletion x) ↔
      ∀ (a₀ : A₀) (x : E), f (a₀ • x) = φ a₀ • f x := by
  refine ⟨fun h a₀ x ↦ ?_, fun h a x ↦ ?_⟩
  · simpa only [extendSMulCLM_map_coe, ContinuousLinearMap.fromCompletion_apply_coe]
      using h (φ a₀) (x : Completion E)
  · refine hφ.induction (fun a ⟨a₀, ha₀⟩ ↦ ?_)
      (isClosed_eq
        (f.fromCompletion.continuous.comp
          ((ContinuousLinearMap.apply ℂ (Completion E) x).continuous.comp
            (extendSMulCLM E hφ).continuous))
        (by fun_prop)) a
    subst ha₀
    refine Completion.induction_on x
      (isClosed_eq (f.fromCompletion.continuous.comp (extendSMulCLM E hφ (φ a₀)).continuous)
        (by fun_prop)) fun u ↦ ?_
    rw [extendSMulCLM_map_coe, ContinuousLinearMap.fromCompletion_apply_coe,
      ContinuousLinearMap.fromCompletion_apply_coe, h a₀ u]

omit [StarOrderedRing A] in
variable (φ) in
/-- Extend any plain function `f : E → F` into a complete `CStarModule A F` preserving `A`-valued
inner products to a `ℂ`-linear isometry `Completion E →ₗᵢ[ℂ] F`. -/
noncomputable def fromCompletionInnerₗᵢ (f : E → F)
    (hf : ∀ x y : E, inner A (f x) (f y) = inner A x y) :
    Completion E →ₗᵢ[ℂ] F :=
  (linearIsometryOfInner φ f hf).fromCompletion

omit [StarOrderedRing A] in
variable (φ) in
@[simp]
theorem fromCompletionInnerₗᵢ_coe (f : E → F)
    (hf : ∀ x y : E, inner A (f x) (f y) = inner A x y) (x : E) :
    fromCompletionInnerₗᵢ φ f hf (x : Completion E) = f x := by
  rw [fromCompletionInnerₗᵢ, LinearIsometry.fromCompletion_apply_coe, linearIsometryOfInner_apply]

@[simp]
theorem inner_fromCompletionInnerₗᵢ (hφ : DenseRange φ) (f : E → F)
    (hf : ∀ x y : E, inner A (f x) (f y) = inner A x y) (x y : Completion E) :
    inner A (fromCompletionInnerₗᵢ φ f hf x) (fromCompletionInnerₗᵢ φ f hf y) = inner A x y := by
  refine Completion.induction_on₂ x y
    (isClosed_eq
      ((CStarModule.continuous_inner (A := A) (E := F)).comp
        (((fromCompletionInnerₗᵢ φ f hf).continuous.comp continuous_fst).prodMk
          ((fromCompletionInnerₗᵢ φ f hf).continuous.comp continuous_snd)))
      (continuous_inner_completion hφ))
    fun u v ↦ ?_
  rw [fromCompletionInnerₗᵢ_coe, fromCompletionInnerₗᵢ_coe, inner_coe_coe hφ, hf]

@[simp]
theorem fromCompletionInnerₗᵢ_extendSMulCLM (hφ : DenseRange φ) (f : E → F)
    (hf : ∀ x y : E, inner A (f x) (f y) = inner A x y) (a : A) (x : Completion E) :
    fromCompletionInnerₗᵢ φ f hf (extendSMulCLM E hφ a x) =
      a • fromCompletionInnerₗᵢ φ f hf x := by
  have hf' : ∀ u v : E, inner A ((linearIsometryOfInner φ f hf).toContinuousLinearMap u)
      ((linearIsometryOfInner φ f hf).toContinuousLinearMap v) = inner A u v := by
    simpa using hf
  exact (fromCompletion_extendSMulCLM_iff hφ
    (linearIsometryOfInner φ f hf).toContinuousLinearMap).mpr
    (map_smul_along_of_inner φ hf') a x

omit [StarOrderedRing A] in
variable (φ) in
/-- Uniqueness in the universal property of `Completion E` for inner-product-preserving maps. -/
theorem eq_fromCompletionInnerₗᵢ_iff (f : E → F)
    (hf : ∀ x y : E, inner A (f x) (f y) = inner A x y) (g : Completion E →ₗᵢ[ℂ] F) :
    g = fromCompletionInnerₗᵢ φ f hf ↔ ∀ x : E, g (x : Completion E) = f x := by
  refine ⟨fun h x ↦ by rw [h, fromCompletionInnerₗᵢ_coe], fun h ↦ ?_⟩
  ext x
  exact Completion.induction_on x
    (isClosed_eq g.continuous (fromCompletionInnerₗᵢ φ f hf).continuous)
    fun u ↦ (h u).trans (fromCompletionInnerₗᵢ_coe φ f hf u).symm

omit [StarOrderedRing A] in
variable (φ) in
/-- Any plain inner-product-preserving map `f : E → F` with dense range into a complete
`CStarModule A F` induces a `ℂ`-linear isometric equivalence `Completion E ≃ₗᵢ[ℂ] F`. -/
noncomputable def equivOfDenseInner (f : E → F)
    (hf : ∀ x y : E, inner A (f x) (f y) = inner A x y) (hdf : DenseRange f) :
    Completion E ≃ₗᵢ[ℂ] F :=
  LinearIsometryEquiv.ofSurjective (fromCompletionInnerₗᵢ φ f hf) <| by
    have hdense : DenseRange (fromCompletionInnerₗᵢ φ f hf) := by
      refine hdf.mono ?_
      rintro _ ⟨x, rfl⟩
      exact ⟨(x : Completion E), fromCompletionInnerₗᵢ_coe φ f hf x⟩
    have hclosed : IsClosed (Set.range (fromCompletionInnerₗᵢ φ f hf)) :=
      (fromCompletionInnerₗᵢ φ f hf).isometry.isUniformInducing.isComplete_range.isClosed
    exact Set.range_eq_univ.mp (hclosed.closure_eq.symm.trans hdense.closure_eq)

omit [StarOrderedRing A] in
variable (φ) in
theorem equivOfDenseInner_apply (f : E → F)
    (hf : ∀ x y : E, inner A (f x) (f y) = inner A x y) (hdf : DenseRange f)
    (x : Completion E) :
    equivOfDenseInner φ f hf hdf x = fromCompletionInnerₗᵢ φ f hf x :=
  (rfl)

omit [StarOrderedRing A] in
variable (φ) in
@[simp]
theorem equivOfDenseInner_coe (f : E → F)
    (hf : ∀ x y : E, inner A (f x) (f y) = inner A x y) (hdf : DenseRange f) (x : E) :
    equivOfDenseInner φ f hf hdf (x : Completion E) = f x :=
  fromCompletionInnerₗᵢ_coe φ f hf x

@[simp]
theorem inner_equivOfDenseInner (hφ : DenseRange φ) (f : E → F)
    (hf : ∀ x y : E, inner A (f x) (f y) = inner A x y) (hdf : DenseRange f)
    (x y : Completion E) :
    inner A (equivOfDenseInner φ f hf hdf x) (equivOfDenseInner φ f hf hdf y) = inner A x y :=
  inner_fromCompletionInnerₗᵢ hφ f hf x y

@[simp]
theorem equivOfDenseInner_extendSMulCLM (hφ : DenseRange φ) (f : E → F)
    (hf : ∀ x y : E, inner A (f x) (f y) = inner A x y) (hdf : DenseRange f)
    (a : A) (x : Completion E) :
    equivOfDenseInner φ f hf hdf (extendSMulCLM E hφ a x) =
      a • equivOfDenseInner φ f hf hdf x :=
  fromCompletionInnerₗᵢ_extendSMulCLM hφ f hf a x

end UniversalAlong

end TauCeti.SemiCStarModuleAlong

/-! ### Bounded module maps on completions -/

namespace ContinuousLinearMap

variable {A E F : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E]
  [SMul A E] [UniformContinuousConstSMul A E]
  [SeminormedAddCommGroup F] [NormedSpace ℂ F] [SMul A F]

/-- `f.fromCompletion : Completion E →L[ℂ] F` commutes with `A` if and only if `f` does. -/
@[simp]
theorem fromCompletion_smul_iff [T2Space F] [CompleteSpace F] [ContinuousConstSMul A F]
    (f : E →L[ℂ] F) :
    (∀ (a : A) (x : Completion E), f.fromCompletion (a • x) = a • f.fromCompletion x) ↔
      ∀ (a : A) (x : E), f (a • x) = a • f x := by
  refine ⟨fun h a x ↦ ?_, fun h a x ↦ ?_⟩
  · simpa only [← Completion.coe_smul, fromCompletion_apply_coe] using h a x
  · refine Completion.induction_on x
      (isClosed_eq (f.fromCompletion.continuous.comp (continuous_const_smul a))
        ((continuous_const_smul a).comp f.fromCompletion.continuous)) fun u ↦ ?_
    simp [← Completion.coe_smul, h a u]

/-- If `f : E →L[ℂ] F` commutes with `A`, then so does `f.completion : Completion E →L[ℂ]
Completion F`. -/
theorem completion_smul [UniformContinuousConstSMul A F] (f : E →L[ℂ] F)
    (hf : ∀ (a : A) (x : E), f (a • x) = a • f x) (a : A) (x : Completion E) :
    f.completion (a • x) = a • f.completion x := by
  refine Completion.induction_on x
    (isClosed_eq (f.completion.continuous.comp (continuous_const_smul a))
      ((continuous_const_smul a).comp f.completion.continuous)) fun u ↦ ?_
  simp [← Completion.coe_smul, hf a u]

/-- When `F` is separated, `f.completion : Completion E →L[ℂ] Completion F` commutes with `A` if and
only if `f` does. -/
@[simp]
theorem completion_smul_iff [T0Space F] [UniformContinuousConstSMul A F] (f : E →L[ℂ] F) :
    (∀ (a : A) (x : Completion E), f.completion (a • x) = a • f.completion x) ↔
      ∀ (a : A) (x : E), f (a • x) = a • f x := by
  refine ⟨fun h a x ↦ ?_, completion_smul f⟩
  have hcoe := h a (x : Completion E)
  rwa [← Completion.coe_smul, completion_apply_coe, completion_apply_coe,
    ← Completion.coe_smul, Completion.coe_inj] at hcoe

/-- Universal property of `Completion E` for bounded linear maps into a complete separated space
`G`: `g : Completion E →L[ℂ] G` factors `f : E →L[ℂ] G` through `Completion.toComplL` if and only if
`g = f.fromCompletion`. -/
theorem comp_toComplL_eq_iff {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]
    (f : E →L[ℂ] G) (g : Completion E →L[ℂ] G) :
    g.comp Completion.toComplL = f ↔ g = f.fromCompletion := by
  refine ⟨fun h ↦ ?_, fun h ↦ by ext x; simp [h]⟩
  ext x
  exact Completion.induction_on x (isClosed_eq g.continuous f.fromCompletion.continuous)
    fun u ↦ by simpa using LinearMap.congr_fun (congr_arg toLinearMap h) u

end ContinuousLinearMap

/-! ### Global `CStarModule` instance and universal properties on `UniformSpace.Completion` -/

namespace UniformSpace.Completion

section SemiCStarModule

variable {A E : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [SeminormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [TauCeti.SemiCStarModule A E]

@[simp]
theorem inner_coe_of_semiCStarModule (x y : E) :
    inner A (x : Completion E) (y : Completion E) = inner A x y :=
  TauCeti.SemiCStarModuleAlong.inner_coe_coe
    (φ := NonUnitalStarAlgHom.id ℂ A) Function.surjective_id.denseRange x y

/-- When `A` already acts on `E`, the extended action `extendSMulCLM` along `id` coincides with
`Completion E`'s standard `SMul A (Completion E)`. -/
@[simp]
theorem extendSMulCLM_id_apply (a : A) (x : Completion E) :
    TauCeti.SemiCStarModuleAlong.extendSMulCLM E
      (φ := NonUnitalStarAlgHom.id ℂ A) Function.surjective_id.denseRange a x = a • x :=
  TauCeti.SemiCStarModuleAlong.extendSMulCLM_map_apply
    (φ := NonUnitalStarAlgHom.id ℂ A) Function.surjective_id.denseRange a x

/-- The completion of any pre-Hilbert or positive semidefinite `A`-module is a Hilbert `A`-module
(`CStarModule A (Completion E)`). -/
noncomputable instance instCStarModule : CStarModule A (Completion E) where
  toInner := Completion.toInner
  inner_add_right := TauCeti.SemiCStarModuleAlong.inner_add_right_completion
    (φ := NonUnitalStarAlgHom.id ℂ A) Function.surjective_id.denseRange _ _ _
  inner_self_nonneg := TauCeti.SemiCStarModuleAlong.inner_self_nonneg_completion
    (φ := NonUnitalStarAlgHom.id ℂ A) Function.surjective_id.denseRange _
  inner_self := TauCeti.SemiCStarModuleAlong.inner_self_eq_zero_completion
    (φ := NonUnitalStarAlgHom.id ℂ A) Function.surjective_id.denseRange _
  inner_op_smul_right := TauCeti.SemiCStarModuleAlong.inner_op_smul_right_completion
    (φ := NonUnitalStarAlgHom.id ℂ A) Function.surjective_id.denseRange _ _ _
  inner_smul_right_complex := TauCeti.SemiCStarModuleAlong.inner_smul_right_complex_completion
    (φ := NonUnitalStarAlgHom.id ℂ A) Function.surjective_id.denseRange _ _ _
  star_inner := TauCeti.SemiCStarModuleAlong.star_inner_completion
    (φ := NonUnitalStarAlgHom.id ℂ A) Function.surjective_id.denseRange
  norm_eq_sqrt_norm_inner_self :=
    TauCeti.SemiCStarModuleAlong.norm_eq_sqrt_norm_inner_self_completion
      (φ := NonUnitalStarAlgHom.id ℂ A) Function.surjective_id.denseRange

open scoped ComplexOrder in
-- Verify definitional equality with `WithCStarModule.instCStarModuleComplex` on `Completion H`.
example {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    (instCStarModule : CStarModule ℂ (Completion H)) =
      WithCStarModule.instCStarModuleComplex := by
  with_reducible_and_instances rfl

/-- `separationQuotientEquiv ℂ E : Completion (SeparationQuotient E) ≃ₗᵢ[ℂ] Completion E` preserves
`A`-valued inner products. -/
@[simp]
theorem inner_separationQuotientEquiv (x y : Completion (SeparationQuotient E)) :
    inner A (separationQuotientEquiv ℂ E x) (separationQuotientEquiv ℂ E y) = inner A x y := by
  refine Completion.induction_on₂ x y
    (isClosed_eq
      ((CStarModule.continuous_inner (A := A) (E := Completion E)).comp
        (((separationQuotientEquiv ℂ E).continuous.comp continuous_fst).prodMk
          ((separationQuotientEquiv ℂ E).continuous.comp continuous_snd)))
      (CStarModule.continuous_inner (A := A) (E := Completion (SeparationQuotient E))))
    fun q₁ q₂ ↦ ?_
  obtain ⟨u, rfl⟩ := SeparationQuotient.surjective_mk q₁
  obtain ⟨v, rfl⟩ := SeparationQuotient.surjective_mk q₂
  rw [separationQuotientEquiv_coe_mk, separationQuotientEquiv_coe_mk,
    inner_coe_of_semiCStarModule, ← SeparationQuotient.inner_mk_mk_of_semiCStarModule (A := A)]
  exact (inner_coe_of_semiCStarModule (A := A) (E := SeparationQuotient E)
    (SeparationQuotient.mk u) (SeparationQuotient.mk v)).symm

/-- `separationQuotientEquiv ℂ E : Completion (SeparationQuotient E) ≃ₗᵢ[ℂ] Completion E` commutes
with the `A`-action. -/
@[simp]
theorem separationQuotientEquiv_smul (a : A) (x : Completion (SeparationQuotient E)) :
    separationQuotientEquiv ℂ E (a • x) = a • separationQuotientEquiv ℂ E x := by
  refine Completion.induction_on x
    (isClosed_eq ((separationQuotientEquiv ℂ E).continuous.comp (continuous_const_smul a))
      ((continuous_const_smul a).comp (separationQuotientEquiv ℂ E).continuous))
    fun q ↦ ?_
  obtain ⟨u, rfl⟩ := SeparationQuotient.surjective_mk q
  rw [← Completion.coe_smul, ← SeparationQuotient.mk_smul, separationQuotientEquiv_coe_mk,
    separationQuotientEquiv_coe_mk, Completion.coe_smul]

/-- Completion preserves the closed complex linear span of inner products, so `Completion E` is full
if and only if `E` has dense inner-product span. -/
theorem topologicalClosure_span_range_inner :
    (Submodule.span ℂ
        (Set.range fun p : Completion E × Completion E ↦ inner A p.1 p.2)).topologicalClosure =
      (Submodule.span ℂ (Set.range fun p : E × E ↦ inner A p.1 p.2)).topologicalClosure :=
  TauCeti.SemiCStarModuleAlong.topologicalClosure_span_range_inner_completion E
    (φ := NonUnitalStarAlgHom.id ℂ A) Function.surjective_id.denseRange

end SemiCStarModule

section RightFull

variable {A E : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [SeminormedAddCommGroup E] [NormedSpace ℂ E] [SMul Aᵐᵒᵖ E] [TauCeti.SemiCStarModule Aᵐᵒᵖ E]

/-- Right-module form of `topologicalClosure_span_range_inner`: completing a right module preserves
the closed complex linear span of `⟨x, y⟩_A = unop (inner Aᵐᵒᵖ x y)`. -/
theorem topologicalClosure_span_range_unop_inner_mulOpposite :
    (Submodule.span ℂ
        (Set.range fun p : Completion E × Completion E ↦
          unop (inner Aᵐᵒᵖ p.1 p.2))).topologicalClosure =
      (Submodule.span ℂ
        (Set.range fun p : E × E ↦ unop (inner Aᵐᵒᵖ p.1 p.2))).topologicalClosure := by
  refine le_antisymm
    (Submodule.topologicalClosure_minimal _ ?_ (Submodule.isClosed_topologicalClosure _))
    (Submodule.topologicalClosure_mono <| Submodule.span_mono ?_)
  · rw [Submodule.span_le]
    rintro _ ⟨⟨x, y⟩, rfl⟩
    refine Completion.induction_on₂ x y
      ((Submodule.isClosed_topologicalClosure _).preimage
        (continuous_unop.comp (CStarModule.continuous_inner (A := Aᵐᵒᵖ) (E := Completion E))))
      fun u v ↦ ?_
    simp only [inner_coe_of_semiCStarModule]
    exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨(u, v), rfl⟩)
  · rintro _ ⟨⟨u, v⟩, rfl⟩
    exact ⟨((u : Completion E), (v : Completion E)),
      congr_arg unop (inner_coe_of_semiCStarModule u v)⟩

end RightFull

section UniversalInner

variable {A E F : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A]
  [SeminormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [TauCeti.SemiCStarModule A E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] [SMul A F] [CStarModule A F]

/-- Extend any plain inner-product-preserving function `f : E → F` into a complete
`CStarModule A F` to a `ℂ`-linear isometry `Completion E →ₗᵢ[ℂ] F`. -/
noncomputable def fromCompletionInnerₗᵢ (f : E → F)
    (hf : ∀ x y : E, inner A (f x) (f y) = inner A x y) :
    Completion E →ₗᵢ[ℂ] F :=
  TauCeti.SemiCStarModuleAlong.fromCompletionInnerₗᵢ (NonUnitalStarAlgHom.id ℂ A) f hf

@[simp]
theorem fromCompletionInnerₗᵢ_coe (f : E → F)
    (hf : ∀ x y : E, inner A (f x) (f y) = inner A x y) (x : E) :
    fromCompletionInnerₗᵢ f hf (x : Completion E) = f x :=
  TauCeti.SemiCStarModuleAlong.fromCompletionInnerₗᵢ_coe (NonUnitalStarAlgHom.id ℂ A) f hf x

@[simp]
theorem inner_fromCompletionInnerₗᵢ [StarOrderedRing A] (f : E → F)
    (hf : ∀ x y : E, inner A (f x) (f y) = inner A x y) (x y : Completion E) :
    inner A (fromCompletionInnerₗᵢ f hf x) (fromCompletionInnerₗᵢ f hf y) = inner A x y :=
  TauCeti.SemiCStarModuleAlong.inner_fromCompletionInnerₗᵢ
    (φ := NonUnitalStarAlgHom.id ℂ A) Function.surjective_id.denseRange f hf x y

@[simp]
theorem fromCompletionInnerₗᵢ_smul [StarOrderedRing A] (f : E → F)
    (hf : ∀ x y : E, inner A (f x) (f y) = inner A x y) (a : A) (x : Completion E) :
    fromCompletionInnerₗᵢ f hf (a • x) = a • fromCompletionInnerₗᵢ f hf x := by
  refine Completion.induction_on x
    (isClosed_eq ((fromCompletionInnerₗᵢ f hf).continuous.comp (continuous_const_smul a))
      ((continuous_const_smul a).comp (fromCompletionInnerₗᵢ f hf).continuous))
    fun u ↦ ?_
  rw [← Completion.coe_smul, fromCompletionInnerₗᵢ_coe, fromCompletionInnerₗᵢ_coe]
  exact TauCeti.SemiCStarModuleAlong.map_smul_along_of_inner
    (NonUnitalStarAlgHom.id ℂ A) hf a u

theorem eq_fromCompletionInnerₗᵢ_iff (f : E → F)
    (hf : ∀ x y : E, inner A (f x) (f y) = inner A x y) (g : Completion E →ₗᵢ[ℂ] F) :
    g = fromCompletionInnerₗᵢ f hf ↔ ∀ x : E, g (x : Completion E) = f x :=
  TauCeti.SemiCStarModuleAlong.eq_fromCompletionInnerₗᵢ_iff (NonUnitalStarAlgHom.id ℂ A) f hf g

/-- Any plain inner-product-preserving function `f : E → F` with dense range into a complete
`CStarModule A F` induces a unitary equivalence `Completion E ≃ₗᵢ[ℂ] F`. -/
noncomputable def equivOfDenseInner (f : E → F)
    (hf : ∀ x y : E, inner A (f x) (f y) = inner A x y) (hdf : DenseRange f) :
    Completion E ≃ₗᵢ[ℂ] F :=
  TauCeti.SemiCStarModuleAlong.equivOfDenseInner (NonUnitalStarAlgHom.id ℂ A) f hf hdf

@[simp]
theorem equivOfDenseInner_coe (f : E → F)
    (hf : ∀ x y : E, inner A (f x) (f y) = inner A x y) (hdf : DenseRange f) (x : E) :
    equivOfDenseInner f hf hdf (x : Completion E) = f x :=
  fromCompletionInnerₗᵢ_coe f hf x

@[simp]
theorem inner_equivOfDenseInner [StarOrderedRing A] (f : E → F)
    (hf : ∀ x y : E, inner A (f x) (f y) = inner A x y) (hdf : DenseRange f)
    (x y : Completion E) :
    inner A (equivOfDenseInner f hf hdf x) (equivOfDenseInner f hf hdf y) = inner A x y :=
  inner_fromCompletionInnerₗᵢ f hf x y

@[simp]
theorem equivOfDenseInner_smul [StarOrderedRing A] (f : E → F)
    (hf : ∀ x y : E, inner A (f x) (f y) = inner A x y) (hdf : DenseRange f)
    (a : A) (x : Completion E) :
    equivOfDenseInner f hf hdf (a • x) = a • equivOfDenseInner f hf hdf x :=
  fromCompletionInnerₗᵢ_smul f hf a x

end UniversalInner

end UniformSpace.Completion

/-! ### Completion of a dense nonunital `⋆`-subalgebra as a right Hilbert `A`-module -/

namespace NonUnitalStarSubalgebra

variable {A : Type*} [NonUnitalCStarAlgebra A]

/-- If `S` is a dense nonunital `⋆`-subalgebra of `A`, then `(NonUnitalStarSubalgebraClass.subtype
S).op : Sᵐᵒᵖ →⋆ₙₐ[ℂ] Aᵐᵒᵖ` has dense range. -/
theorem denseRange_subtype_op (S : NonUnitalStarSubalgebra ℂ A) (hS : Dense (S : Set A)) :
    DenseRange (NonUnitalStarSubalgebraClass.subtype S).op := by
  rw [NonUnitalStarAlgHom.denseRange_op_iff]
  exact denseRange_subtype_val.mpr hS

variable [PartialOrder A] [StarOrderedRing A]

/-- The completion of a dense nonunital `⋆`-subalgebra `S ⊆ A` (viewed as a right `S`-module with
positivity and norm measured in `A`) is canonically unitarily equivalent to the right Hilbert
self-module `A`, intertwining the extended right `A`-action with multiplication in `A`. -/
noncomputable def completionEquiv (S : NonUnitalStarSubalgebra ℂ A) (hS : Dense (S : Set A)) :
    Completion S ≃ₗᵢ[ℂ] A :=
  TauCeti.SemiCStarModuleAlong.equivOfDenseInner
    (NonUnitalStarSubalgebraClass.subtype S).op Subtype.val
    (fun _ _ ↦ rfl) (denseRange_subtype_val.mpr hS)

@[simp]
theorem completionEquiv_coe (S : NonUnitalStarSubalgebra ℂ A) (hS : Dense (S : Set A)) (x : S) :
    S.completionEquiv hS (x : Completion S) = (x : A) :=
  TauCeti.SemiCStarModuleAlong.equivOfDenseInner_coe _ _ _ _ x

@[simp]
theorem inner_completionEquiv (S : NonUnitalStarSubalgebra ℂ A) (hS : Dense (S : Set A))
    (x y : Completion S) :
    inner Aᵐᵒᵖ (S.completionEquiv hS x) (S.completionEquiv hS y) = inner Aᵐᵒᵖ x y :=
  TauCeti.SemiCStarModuleAlong.inner_equivOfDenseInner
    (S.denseRange_subtype_op hS) _ _ _ x y

@[simp]
theorem completionEquiv_extendSMulCLM (S : NonUnitalStarSubalgebra ℂ A) (hS : Dense (S : Set A))
    (a : A) (x : Completion S) :
    S.completionEquiv hS
        (TauCeti.SemiCStarModuleAlong.extendSMulCLM S (S.denseRange_subtype_op hS) (op a) x) =
      S.completionEquiv hS x * a :=
  TauCeti.SemiCStarModuleAlong.equivOfDenseInner_extendSMulCLM
    (S.denseRange_subtype_op hS) _ _ _ (op a) x

end NonUnitalStarSubalgebra

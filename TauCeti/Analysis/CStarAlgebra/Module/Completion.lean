/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Module.Self
public import TauCeti.Analysis.CStarAlgebra.Module.Semidef
public import TauCeti.Analysis.Normed.Operator.Completion

/-!
# Completions of pre-Hilbert and positive semidefinite C⋆-modules

For `E` carrying `TauCeti.IsPosSemidefCStarModuleAlong ι E` along dense `ι : A₀ →⋆ₙₐ[ℂ] A`,
`UniformSpace.Completion.toInner` extends `⟪·, ·⟫_A` continuously to `Completion E` with
`‖z‖ = √‖⟪z, z⟫_A‖` and definiteness `⟪z, z⟫_A = 0 ↔ z = 0`. At `ι = id`,
`UniformSpace.Completion.instCStarModule` gives a global `CStarModule A` instance; for general
dense `ι`, `extAction` extends the `A₀`-action (`cstarModuleOfDense`).

## Main declarations

* `UniformSpace.Completion.instCStarModule`, `inner_completionSeparationQuotientₗᵢ`.
* `TauCeti.IsPosSemidefCStarModuleAlong.extAction`, `extSMul`, `cstarModuleOfDense`,
  `ContinuousLinearMap.fromCompletion_extAction`, `fromCompletion_extAction_iff`, `liftOfInner`,
  `equivOfInner`.
* `TauCeti.IsPosSemidefCStarModuleAlong.topologicalClosure_span_range_inner_completion` and
  `topologicalClosure_span_range_unop_inner_completion`: completion preserves fullness.
* `TauCeti.IsPosSemidefCStarModuleAlong.completionRightModuleEquiv`: completing a dense
  `⋆`-subalgebra `s` of `A` as a right `s`-module recovers `A` as a right Hilbert `A`-module.

## References

* E. Christopher Lance, *Hilbert C⋆-Modules: A Toolkit for Operator Algebraists*, Chapter 1.
* Iain Raeburn and Dana P. Williams, *Morita Equivalence and Continuous-Trace C⋆-Algebras*,
  Chapter 2, Lemma 2.16.
* `inner_coe`, `continuous_inner_completion`, and the `Completion.induction_on₂` laws adapt
  `Mathlib.Analysis.InnerProductSpace.Completion`.
-/

public section

open MulOpposite UniformSpace
open scoped ComplexOrder

/-! ### Inner product extension, definiteness, and extended action over a dense `⋆`-subalgebra -/

namespace TauCeti.IsPosSemidefCStarModuleAlong

section LiftOfInnerBasic

variable {A₀ A E F : Type*} [NonUnitalSemiring A₀] [StarRing A₀] [Module ℂ A₀]
  [NonUnitalCStarAlgebra A] [PartialOrder A] (ι : A₀ →⋆ₙₐ[ℂ] A)
  [SeminormedAddCommGroup E] [NormedSpace ℂ E] [SMul A₀ E] [Inner A E]
  [IsPosSemidefCStarModuleAlong ι E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] [SMul A F] [CStarModule A F]
  (f : E →ₗ[ℂ] F) (hf : ∀ x y : E, inner A (f x) (f y) = inner A x y)
include ι

/-- **Universal property of `Completion E` for inner-product-preserving maps:** any `ℂ`-linear map
`f : E →ₗ[ℂ] F` into a complete Hilbert `A`-module `F` preserving `inner A` (without assuming
continuity or module linearity in advance) extends to a linear isometry `Completion E →ₗᵢ[ℂ] F`. -/
noncomputable def liftOfInner : Completion E →ₗᵢ[ℂ] F :=
  LinearIsometry.fromCompletion ⟨f, fun x ↦ by
    rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := A) (f x), hf,
      norm_eq_sqrt_norm_inner_self (ι := ι) x]⟩

@[simp] theorem liftOfInner_coe (x : E) : liftOfInner ι f hf (x : Completion E) = f x :=
  LinearIsometry.fromCompletion_apply_coe _ x
theorem eq_liftOfInner_iff (g : Completion E →ₗᵢ[ℂ] F) :
    g = liftOfInner ι f hf ↔ ∀ x : E, g (x : Completion E) = f x :=
  ⟨fun h x ↦ by rw [h, liftOfInner_coe], fun h ↦ LinearIsometry.toContinuousLinearMap_inj.mp
    (ContinuousLinearMap.fromCompletion_unique _ g.toContinuousLinearMap fun x ↦ (h x).symm).symm⟩

/-- When an `inner A`-preserving linear map `f : E →ₗ[ℂ] F` into a complete Hilbert `A`-module `F`
has dense range, `liftOfInner` upgrades to `Completion E ≃ₗᵢ[ℂ] F`. -/
noncomputable def equivOfInner (hdense : DenseRange f) : Completion E ≃ₗᵢ[ℂ] F :=
  LinearIsometryEquiv.ofSurjective (liftOfInner ι f hf)
    (LinearIsometry.fromCompletion_surjective_of_denseRange _ hdense)

@[simp] theorem toLinearIsometry_equivOfInner (hdense : DenseRange f) :
    (equivOfInner ι f hf hdense).toLinearIsometry = liftOfInner ι f hf :=
  LinearIsometry.ext fun _ ↦ rfl
theorem coe_equivOfInner (hdense : DenseRange f) :
    (equivOfInner ι f hf hdense : Completion E → F) = liftOfInner ι f hf :=
  LinearIsometryEquiv.coe_ofSurjective _ _
@[simp] theorem equivOfInner_coe (hdense : DenseRange f) (x : E) :
    equivOfInner ι f hf hdense (x : Completion E) = f x := liftOfInner_coe ι f hf x
@[simp] theorem equivOfInner_symm_apply (hdense : DenseRange f) (x : E) :
    (equivOfInner ι f hf hdense).symm (f x) = (x : Completion E) :=
  (equivOfInner ι f hf hdense).injective <| by simp

end LiftOfInnerBasic

section InnerCompletion

section Semiring

variable {A₀ A E : Type*} [NonUnitalSemiring A₀] [StarRing A₀] [Module ℂ A₀]
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A] {ι : A₀ →⋆ₙₐ[ℂ] A}
  [SeminormedAddCommGroup E] [NormedSpace ℂ E] [SMul A₀ E] [Inner A E]
  [IsPosSemidefCStarModuleAlong ι E]

/-- On `Completion E`, the extended `A`-valued inner product agrees with `inner A` on `E`. -/
theorem inner_coe (hι : DenseRange ι) (x y : E) :
    inner A (x : Completion E) (y : Completion E) = inner A x y :=
  (Completion.isDenseInducing_coe.prodMap Completion.isDenseInducing_coe).extend_eq
    (continuous_inner hι) (x, y)

/-- Joint continuity of the extended `A`-valued inner product on `Completion E`. -/
theorem continuous_inner_completion (hι : DenseRange ι) :
    Continuous (Function.uncurry (inner A (E := Completion E))) := by
  let inner' : E →+ E →+ A :=
    { toFun x := (innerₛₗ ι x).toAddMonoidHom, map_zero' := by ext z; simp,
      map_add' x y := by ext z; simp }
  have hcont : Continuous fun p : E × E ↦ inner' p.1 p.2 := by
    simpa [inner'] using continuous_inner hι
  -- `Completion.toInner` has no unfolding lemma; unfold it to expose `IsDenseInducing.extend`.
  rw [Completion.toInner, inner, Function.uncurry_curry _]
  convert (Completion.isDenseInducing_toCompl E).extend_Z_bilin
    (Completion.isDenseInducing_toCompl E) hcont using 2
  · ext ⟨x, y⟩ <;> simp
  · ext ⟨x, y⟩; simp [inner']

theorem continuous_inner_completion_comp (hι : DenseRange ι) {α : Type*} [TopologicalSpace α]
    {f g : α → Completion E} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun t ↦ inner A (f t) (g t) :=
  (continuous_inner_completion hι).comp (hf.prodMk hg)
theorem inner_add_right_completion (hι : DenseRange ι) (x y z : Completion E) :
    inner A x (y + z) = inner A x y + inner A x z :=
  Completion.induction_on₃ x y z
    (isClosed_eq (continuous_inner_completion_comp hι continuous_fst (by fun_prop))
      ((continuous_inner_completion_comp hι continuous_fst (by fun_prop)).add
        (continuous_inner_completion_comp hι continuous_fst (by fun_prop))))
    fun _ _ _ ↦ by
      rw [← Completion.coe_add, inner_coe hι, inner_coe hι, inner_coe hι, inner_add_right (ι := ι)]
theorem inner_self_nonneg_completion (hι : DenseRange ι) (x : Completion E) :
    0 ≤ inner A x x :=
  Completion.induction_on x
    (isClosed_le continuous_const (continuous_inner_completion_comp hι continuous_id continuous_id))
    fun _ ↦ by rw [inner_coe hι]; exact inner_self_nonneg (ι := ι)
theorem star_inner_completion (hι : DenseRange ι) (x y : Completion E) :
    star (inner A x y) = inner A y x :=
  Completion.induction_on₂ x y
    (isClosed_eq (continuous_star.comp <|
      continuous_inner_completion_comp hι continuous_fst continuous_snd)
      (continuous_inner_completion_comp hι continuous_snd continuous_fst))
    fun _ _ ↦ by rw [inner_coe hι, inner_coe hι, star_inner (ι := ι)]
theorem inner_add_left_completion (hι : DenseRange ι) (x y z : Completion E) :
    inner A (x + y) z = inner A x z + inner A y z := by
  rw [← star_inner_completion hι z (x + y), inner_add_right_completion hι, star_add,
    star_inner_completion hι, star_inner_completion hι]
theorem inner_zero_right_completion (hι : DenseRange ι) (x : Completion E) :
    inner A x (0 : Completion E) = 0 :=
  Completion.induction_on x
    (isClosed_eq (continuous_inner_completion_comp hι continuous_id continuous_const)
      continuous_const)
    fun _ ↦ by rw [← Completion.coe_zero, inner_coe hι, inner_zero_right ι]
theorem inner_zero_left_completion (hι : DenseRange ι) (x : Completion E) :
    inner A (0 : Completion E) x = 0 := by
  rw [← star_inner_completion hι x 0, inner_zero_right_completion hι, star_zero]
theorem inner_neg_right_completion (hι : DenseRange ι) (x y : Completion E) :
    inner A x (-y) = -inner A x y :=
  eq_neg_of_add_eq_zero_left <| by
    rw [← inner_add_right_completion hι, neg_add_cancel, inner_zero_right_completion hι]
theorem inner_sub_right_completion (hι : DenseRange ι) (x y z : Completion E) :
    inner A x (y - z) = inner A x y - inner A x z := by
  rw [sub_eq_add_neg, inner_add_right_completion hι, inner_neg_right_completion hι, sub_eq_add_neg]
theorem inner_smul_right_complex_completion (hι : DenseRange ι) (c : ℂ) (x y : Completion E) :
    inner A x (c • y) = c • inner A x y :=
  Completion.induction_on₂ x y
    (isClosed_eq (continuous_inner_completion_comp hι continuous_fst (by fun_prop))
      ((continuous_const_smul c).comp <|
        continuous_inner_completion_comp hι continuous_fst continuous_snd))
    fun _ _ ↦ by
      rw [← Completion.coe_smul, inner_coe hι, inner_coe hι, inner_smul_right_complex (ι := ι)]
theorem inner_op_smul_right_completion (hι : DenseRange ι) (a₀ : A₀) (x y : Completion E) :
    inner A x (a₀ • y) = ι a₀ * inner A x y := by
  have : UniformContinuousConstSMul A₀ E := uniformContinuousConstSMul ι
  exact Completion.induction_on₂ x y
    (isClosed_eq (continuous_inner_completion_comp hι continuous_fst (by fun_prop))
      (continuous_const.mul <| continuous_inner_completion_comp hι continuous_fst continuous_snd))
    fun _ _ ↦ by
      rw [← Completion.coe_smul, inner_coe hι, inner_coe hι, inner_op_smul_right (ι := ι)]
theorem norm_eq_sqrt_norm_inner_self_completion (hι : DenseRange ι) (x : Completion E) :
    ‖x‖ = √‖inner A x x‖ :=
  Completion.induction_on x
    (isClosed_eq continuous_norm (Real.continuous_sqrt.comp <|
      (continuous_inner_completion_comp hι continuous_id continuous_id).norm))
    fun _ ↦ by rw [Completion.norm_coe, inner_coe hι, norm_eq_sqrt_norm_inner_self (ι := ι)]

/-- Definiteness of the extended `A`-valued inner product on `Completion E`: `⟪x, x⟫_A = 0 ↔ x = 0`
even when `E` has nonzero null vectors. -/
theorem inner_self_eq_zero_completion (hι : DenseRange ι) {x : Completion E} :
    inner A x x = 0 ↔ x = 0 := by
  rw [← norm_eq_zero (a := x), norm_eq_sqrt_norm_inner_self_completion hι,
    Real.sqrt_eq_zero (norm_nonneg _), norm_eq_zero]
theorem ext_inner_left_completion (hι : DenseRange ι) {z₁ z₂ : Completion E}
    (h : ∀ w : Completion E, inner A w z₁ = inner A w z₂) : z₁ = z₂ := by
  rw [← sub_eq_zero, ← inner_self_eq_zero_completion hι, inner_sub_right_completion hι,
    h (z₁ - z₂), sub_self]

/-- Testing inner products against vectors from `E` already separates elements of `Completion E`. -/
theorem ext_inner_coe_left_completion (hι : DenseRange ι) {z₁ z₂ : Completion E}
    (h : ∀ x : E, inner A (x : Completion E) z₁ = inner A (x : Completion E) z₂) : z₁ = z₂ :=
  ext_inner_left_completion hι fun w ↦ Completion.induction_on w
    (isClosed_eq (continuous_inner_completion_comp hι continuous_id continuous_const)
      (continuous_inner_completion_comp hι continuous_id continuous_const)) h

variable (E) in
/-- Completion preserves the closed complex linear span of the `A`-valued inner products, so
`Completion E` is full if and only if the inner products of `E` span a dense subspace of `A`. -/
theorem topologicalClosure_span_range_inner_completion (hι : DenseRange ι) :
    (Submodule.span ℂ
        (Set.range fun p : Completion E × Completion E ↦ inner A p.1 p.2)).topologicalClosure =
      (Submodule.span ℂ (Set.range fun p : E × E ↦ inner A p.1 p.2)).topologicalClosure := by
  refine le_antisymm
    (Submodule.topologicalClosure_minimal _ ?_ (Submodule.isClosed_topologicalClosure _))
    (Submodule.topologicalClosure_mono <| Submodule.span_mono ?_)
  · rw [Submodule.span_le]; rintro _ ⟨⟨x, y⟩, rfl⟩
    refine Completion.induction_on₂ x y
      ((Submodule.isClosed_topologicalClosure _).preimage (continuous_inner_completion hι))
      fun u v ↦ ?_
    simp only [inner_coe hι]
    exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨(u, v), rfl⟩)
  · rintro _ ⟨⟨u, v⟩, rfl⟩; exact ⟨((u : Completion E), (v : Completion E)), inner_coe hι u v⟩

/-! #### Inner-product preservation of `liftOfInner` and `equivOfInner` -/

section LiftOfInnerInner

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  [SMul A F] [CStarModule A F] (hι : DenseRange ι)
  (f : E →ₗ[ℂ] F) (hf : ∀ x y : E, inner A (f x) (f y) = inner A x y)
include hι

/-- `liftOfInner` preserves the extended `A`-valued inner product on `Completion E`. -/
@[simp] theorem inner_liftOfInner (u v : Completion E) :
    inner A (liftOfInner ι f hf u) (liftOfInner ι f hf v) = inner A u v := by
  let L := liftOfInner ι f hf
  have hcontF : Continuous fun p : F × F ↦ inner A p.1 p.2 :=
    PosSemidefCStarModule.continuous_inner (A := A) (E := F)
  exact Completion.induction_on₂ u v
    (isClosed_eq
      (hcontF.comp ((L.continuous.comp continuous_fst).prodMk (L.continuous.comp continuous_snd)))
      (continuous_inner_completion hι))
    fun _ _ ↦ by rw [liftOfInner_coe, liftOfInner_coe, inner_coe hι, hf]
@[simp] theorem inner_equivOfInner (hdense : DenseRange f) (u v : Completion E) :
    inner A (equivOfInner ι f hf hdense u) (equivOfInner ι f hf hdense v) = inner A u v :=
  inner_liftOfInner hι f hf u v
@[simp] theorem inner_equivOfInner_symm (hdense : DenseRange f) (u v : F) :
    inner A ((equivOfInner ι f hf hdense).symm u) ((equivOfInner ι f hf hdense).symm v) =
      inner A u v := by
  simpa only [LinearIsometryEquiv.apply_symm_apply] using
    (inner_equivOfInner hι f hf hdense ((equivOfInner ι f hf hdense).symm u)
      ((equivOfInner ι f hf hdense).symm v)).symm

end LiftOfInnerInner

/-! #### Extending the action of a dense `⋆`-subalgebra to `Completion E` -/

private lemma smul_add_completion (hι : DenseRange ι) (a₀ : A₀) (y z : Completion E) :
    a₀ • (y + z) = a₀ • y + a₀ • z :=
  ext_inner_left_completion hι fun _ ↦ by
    rw [inner_op_smul_right_completion hι, inner_add_right_completion hι, mul_add,
      inner_add_right_completion hι, inner_op_smul_right_completion hι,
      inner_op_smul_right_completion hι]
private lemma smul_comm_complex_completion (hι : DenseRange ι) (a₀ : A₀) (c : ℂ)
    (y : Completion E) : a₀ • (c • y) = c • (a₀ • y) :=
  ext_inner_left_completion hι fun _ ↦ by
    rw [inner_op_smul_right_completion hι, inner_smul_right_complex_completion hι, mul_smul_comm,
      inner_smul_right_complex_completion hι, inner_op_smul_right_completion hι]
private lemma norm_smul_completion_le (a₀ : A₀) (y : Completion E) :
    ‖a₀ • y‖ ≤ ‖ι a₀‖ * ‖y‖ := by
  have : UniformContinuousConstSMul A₀ E := uniformContinuousConstSMul ι
  refine Completion.induction_on y
    (isClosed_le (continuous_norm.comp (continuous_const_smul a₀))
      (continuous_const.mul continuous_norm)) fun x ↦ ?_
  simpa only [← Completion.coe_smul, Completion.norm_coe] using
    IsPosSemidefCStarModuleAlong.norm_smul_le ι a₀ x
variable (E) in
private noncomputable def actCLM (hι : DenseRange ι) (a₀ : A₀) : Completion E →L[ℂ] Completion E :=
  LinearMap.mkContinuous ⟨⟨(a₀ • ·), smul_add_completion hι a₀⟩,
    smul_comm_complex_completion hι a₀⟩ ‖ι a₀‖ (norm_smul_completion_le a₀)
variable (E) in
private lemma norm_actCLM_le (hι : DenseRange ι) (a₀ : A₀) :
    ‖actCLM E hι a₀‖ ≤ 1 * ‖LinearMap.ofClass ι a₀‖ := by
  rw [one_mul]; exact LinearMap.mkContinuous_norm_le _ (norm_nonneg _) _

end Semiring

section Ring

variable {A₀ A E : Type*} [NonUnitalRing A₀] [StarRing A₀] [Module ℂ A₀]
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A] {ι : A₀ →⋆ₙₐ[ℂ] A}
  [SeminormedAddCommGroup E] [NormedSpace ℂ E] [SMul A₀ E] [Inner A E]
  [IsPosSemidefCStarModuleAlong ι E]

variable (E) in
private noncomputable def actLM (hι : DenseRange ι) :
    A₀ →ₗ[ℂ] Completion E →L[ℂ] Completion E where
  toFun := actCLM E hι
  map_add' _ _ := ContinuousLinearMap.ext fun _ ↦ ext_inner_left_completion hι fun _ ↦ by
    simp [actCLM, inner_op_smul_right_completion hι, inner_add_right_completion hι, add_mul]
  map_smul' _ _ := ContinuousLinearMap.ext fun _ ↦ ext_inner_left_completion hι fun _ ↦ by
    simp [actCLM, inner_op_smul_right_completion hι, inner_smul_right_complex_completion hι,
      smul_mul_assoc]

variable (E) in
/-- Extension of the `A₀`-action on `E` along a dense `⋆`-algebra homomorphism `ι : A₀ →⋆ₙₐ[ℂ] A`
to a contractive continuous bilinear action `A →L[ℂ] (Completion E →L[ℂ] Completion E)` on
`Completion E`. -/
noncomputable def extAction (hι : DenseRange ι) : A →L[ℂ] Completion E →L[ℂ] Completion E :=
  (actLM E hι).extendOfNorm (LinearMap.ofClass ι)

@[simp] theorem extAction_iota_apply (hι : DenseRange ι) (a₀ : A₀) (z : Completion E) :
    extAction E hι (ι a₀) z = a₀ • z :=
  DFunLike.congr_fun (LinearMap.extendOfNorm_eq (f := actLM E hι) (e := LinearMap.ofClass ι) hι
    ⟨1, norm_actCLM_le E hι⟩ a₀) z
theorem extAction_iota_coe (hι : DenseRange ι) (a₀ : A₀) (x : E) :
    extAction E hι (ι a₀) (x : Completion E) = ((a₀ • x : E) : Completion E) := by
  have : UniformContinuousConstSMul A₀ E := uniformContinuousConstSMul ι
  rw [extAction_iota_apply, Completion.coe_smul]
variable (E) in
theorem norm_extAction_apply_le (hι : DenseRange ι) (a : A) : ‖extAction E hι a‖ ≤ ‖a‖ := by
  simpa only [extAction, one_mul] using
    LinearMap.norm_extendOfNorm_apply_le (e := LinearMap.ofClass ι) hι 1 (norm_actCLM_le E hι) a
theorem norm_extAction_apply_apply_le (hι : DenseRange ι) (a : A) (z : Completion E) :
    ‖extAction E hι a z‖ ≤ ‖a‖ * ‖z‖ :=
  ((extAction E hι a).le_opNorm z).trans <|
    mul_le_mul_of_nonneg_right (norm_extAction_apply_le E hι a) (norm_nonneg z)
variable (E) in
theorem norm_extAction_le (hι : DenseRange ι) : ‖extAction E hι‖ ≤ 1 :=
  LinearMap.opNorm_extendOfNorm_le (e := LinearMap.ofClass ι) hι zero_le_one (norm_actCLM_le E hι)
@[simp] theorem inner_extAction_right (hι : DenseRange ι) (a : A) (u v : Completion E) :
    inner A u (extAction E hι a v) = a * inner A u v := by
  let P (b : A) : Prop := inner A u (extAction E hι b v) = b * inner A u v
  have hcont : Continuous fun b : A ↦ extAction E hι b v :=
    (ContinuousLinearMap.apply ℂ (Completion E) v).continuous.comp (extAction E hι).continuous
  refine hι.induction (P := P) ?_
    (isClosed_eq (continuous_inner_completion_comp hι continuous_const hcont)
      (continuous_id.mul continuous_const)) a
  rintro _ ⟨a₀, rfl⟩; simp only [P, extAction_iota_apply, inner_op_smul_right_completion hι]
@[simp] theorem inner_extAction_left (hι : DenseRange ι) (a : A) (u v : Completion E) :
    inner A (extAction E hι a u) v = inner A u v * star a := by
  rw [← star_inner_completion hι v, inner_extAction_right hι, star_mul, star_inner_completion hι]
@[simp] theorem extAction_mul (hι : DenseRange ι) (a b : A) (z : Completion E) :
    extAction E hι (a * b) z = extAction E hι a (extAction E hι b z) :=
  ext_inner_left_completion hι fun _ ↦ by
    rw [inner_extAction_right hι, inner_extAction_right hι, inner_extAction_right hι, mul_assoc]

theorem extAction_mul_eq_comp (hι : DenseRange ι) (a b : A) :
    extAction E hι (a * b) = (extAction E hι a).comp (extAction E hι b) :=
  ContinuousLinearMap.ext (extAction_mul hι a b)

/-- Uniqueness of the extended action on `Completion E` from its values on `(ι a₀, x)`. -/
theorem eq_extAction_iff (hι : DenseRange ι) (g : A →L[ℂ] Completion E →L[ℂ] Completion E) :
    g = extAction E hι ↔
      ∀ (a₀ : A₀) (x : E), g (ι a₀) (x : Completion E) = ((a₀ • x : E) : Completion E) := by
  have : UniformContinuousConstSMul A₀ E := uniformContinuousConstSMul ι
  refine ⟨fun h a₀ x ↦ by rw [h, extAction_iota_apply, Completion.coe_smul], fun h ↦ ?_⟩
  symm
  refine LinearMap.extendOfNorm_unique (e := LinearMap.ofClass ι) hι 1 (norm_actCLM_le E hι) g ?_
  exact LinearMap.ext fun a₀ ↦ DFunLike.ext' <|
    Completion.ext (g (ι a₀)).continuous (actCLM E hι a₀).continuous fun x ↦
      (h a₀ x).trans (Completion.coe_smul a₀ x)

variable (E) in
/-- Scalar multiplication of `A` on `Completion E` extending the `A₀`-action along dense `ι`
(kept as a reducible non-instance because `ι` is not determined by `A` and `Completion E`). -/
noncomputable abbrev extSMul (hι : DenseRange ι) : SMul A (Completion E) := ⟨(extAction E hι · ·)⟩
@[simp] theorem extSMul_smul (hι : DenseRange ι) (a : A) (z : Completion E) :
    (letI := extSMul E hι; a • z) = extAction E hι a z := (rfl)

variable (E) in
/-- Equipped with `extSMul E hι`, `Completion E` is a complete Hilbert `A`-module. -/
noncomputable abbrev cstarModuleOfDense (hι : DenseRange ι) :
    letI : SMul A (Completion E) := extSMul E hι; CStarModule A (Completion E) :=
  letI : SMul A (Completion E) := extSMul E hι
  { toInner := Completion.toInner, inner_add_right := inner_add_right_completion hι _ _ _,
    inner_self_nonneg := inner_self_nonneg_completion hι _,
    inner_self := inner_self_eq_zero_completion hι,
    inner_op_smul_right := inner_extAction_right hι _ _ _,
    inner_smul_right_complex := inner_smul_right_complex_completion hι _ _ _,
    star_inner := star_inner_completion hι,
    norm_eq_sqrt_norm_inner_self := norm_eq_sqrt_norm_inner_self_completion hι }

/-! #### Bounded module map extension and action equivariance on `Completion E` -/

/-- **Universal property of `Completion E` for bounded module maps over a dense `⋆`-subalgebra:**
if `f : E →L[ℂ] F` into a complete normed space `F` carrying a continuous `A`-action intertwines the
`A₀`-action with `ι`, then `f.fromCompletion` intertwines `extAction E hι` with `A` on `F`. -/
theorem _root_.ContinuousLinearMap.fromCompletion_extAction {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] [SMul A F] [ContinuousSMul A F]
    (f : E →L[ℂ] F) (hι : DenseRange ι)
    (hf : ∀ (a₀ : A₀) (x : E), f (a₀ • x) = ι a₀ • f x) (a : A) (z : Completion E) :
    f.fromCompletion (extAction E hι a z) = a • f.fromCompletion z := by
  have : UniformContinuousConstSMul A₀ E := uniformContinuousConstSMul ι
  let P (b : A) : Prop := f.fromCompletion (extAction E hι b z) = b • f.fromCompletion z
  have hcontL : Continuous fun b : A ↦ f.fromCompletion (extAction E hι b z) :=
    f.fromCompletion.continuous.comp
      ((ContinuousLinearMap.apply ℂ (Completion E) z).continuous.comp (extAction E hι).continuous)
  refine hι.induction (P := P) ?_ (isClosed_eq hcontL (continuous_id.smul continuous_const)) a
  rintro _ ⟨a₀, rfl⟩
  simpa only [P, extAction_iota_apply] using f.fromCompletion_smul (hf a₀) z

/-- `f.fromCompletion` intertwines `extAction E hι` with the `A`-action on `F` if and only if
`f : E →L[ℂ] F` intertwines the `A₀`-action with `ι`. -/
theorem _root_.ContinuousLinearMap.fromCompletion_extAction_iff {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] [SMul A F] [ContinuousSMul A F]
    (f : E →L[ℂ] F) (hι : DenseRange ι) :
    (∀ (a : A) (z : Completion E),
        f.fromCompletion (extAction E hι a z) = a • f.fromCompletion z) ↔
      ∀ (a₀ : A₀) (x : E), f (a₀ • x) = ι a₀ • f x :=
  ⟨fun h a₀ x ↦ by
      simpa only [extAction_iota_coe, ContinuousLinearMap.fromCompletion_apply_coe] using
        h (ι a₀) x,
    fun h ↦ f.fromCompletion_extAction hι h⟩

section LiftOfInnerExtAction

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  [SMul A F] [CStarModule A F] (hι : DenseRange ι)
  (f : E →ₗ[ℂ] F) (hf : ∀ x y : E, inner A (f x) (f y) = inner A x y)

@[simp] theorem liftOfInner_extAction (a : A) (z : Completion E) :
    liftOfInner ι f hf (extAction E hι a z) = a • liftOfInner ι f hf z :=
  ContinuousLinearMap.fromCompletion_extAction _ hι (map_smul_of_inner_eq ι hf) a z
@[simp] theorem equivOfInner_extAction (hdense : DenseRange f) (a : A) (z : Completion E) :
    equivOfInner ι f hf hdense (extAction E hι a z) = a • equivOfInner ι f hf hdense z :=
  liftOfInner_extAction hι f hf a z
@[simp] theorem equivOfInner_symm_extAction (hdense : DenseRange f) (a : A) (y : F) :
    (equivOfInner ι f hf hdense).symm (a • y) =
      extAction E hι a ((equivOfInner ι f hf hdense).symm y) :=
  (equivOfInner ι f hf hdense).injective <| by simp

end LiftOfInnerExtAction
end Ring
end InnerCompletion

/-- Over a unital C⋆-algebra `A`, `extAction` sends `1 : A` to the identity on `Completion E`. -/
@[simp] theorem extAction_one {A₀ A E : Type*} [NonUnitalRing A₀] [StarRing A₀] [Module ℂ A₀]
    [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] {ι : A₀ →⋆ₙₐ[ℂ] A}
    [SeminormedAddCommGroup E] [NormedSpace ℂ E] [SMul A₀ E] [Inner A E]
    [IsPosSemidefCStarModuleAlong ι E] (hι : DenseRange ι) (z : Completion E) :
    extAction E hι (1 : A) z = z :=
  ext_inner_left_completion hι fun _ ↦ by rw [inner_extAction_right hι, one_mul]

/-- Right-module form of `topologicalClosure_span_range_inner_completion`: completion preserves
the closed complex linear span of the `A`-valued inner products `⟨x, y⟩_A = unop ⟪x, y⟫_Aᵐᵒᵖ`. -/
theorem topologicalClosure_span_range_unop_inner_completion {A₀ A : Type*} (E : Type*)
    [NonUnitalSemiring A₀] [StarRing A₀] [Module ℂ A₀]
    [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A] {ι : A₀ →⋆ₙₐ[ℂ] Aᵐᵒᵖ}
    [SeminormedAddCommGroup E] [NormedSpace ℂ E] [SMul A₀ E] [Inner Aᵐᵒᵖ E]
    [IsPosSemidefCStarModuleAlong ι E] (hι : DenseRange ι) :
    (Submodule.span ℂ (Set.range fun p : Completion E × Completion E ↦
        unop (inner Aᵐᵒᵖ p.1 p.2))).topologicalClosure =
      (Submodule.span ℂ
        (Set.range fun p : E × E ↦ unop (inner Aᵐᵒᵖ p.1 p.2))).topologicalClosure := by
  have h := congrArg (fun S : Submodule ℂ Aᵐᵒᵖ ↦
      (MulOpposite.opHomeomorph.symm : Aᵐᵒᵖ ≃ₜ A) '' (S : Set Aᵐᵒᵖ))
    (topologicalClosure_span_range_inner_completion E hι)
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

end TauCeti.IsPosSemidefCStarModuleAlong

/-! ### Global `CStarModule` instance and universal properties for `Completion E` -/

namespace UniformSpace.Completion

open TauCeti IsPosSemidefCStarModuleAlong

/-- The completion of any positive semidefinite `A`-module (and hence of any pre-Hilbert
`A`-module `CStarModule A E`) is a complete Hilbert `A`-module. -/
noncomputable instance instCStarModule {A E : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [SeminormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E]
    [PosSemidefCStarModule A E] : CStarModule A (Completion E) :=
  { toInner := Completion.toInner,
    inner_add_right := inner_add_right_completion (ι := .id ℂ A) denseRange_id _ _ _,
    inner_self_nonneg := inner_self_nonneg_completion (ι := .id ℂ A) denseRange_id _,
    inner_self := inner_self_eq_zero_completion (ι := .id ℂ A) denseRange_id,
    inner_op_smul_right := inner_op_smul_right_completion (ι := .id ℂ A) denseRange_id _ _ _,
    inner_smul_right_complex :=
      inner_smul_right_complex_completion (ι := .id ℂ A) denseRange_id _ _ _,
    star_inner := star_inner_completion (ι := .id ℂ A) denseRange_id,
    norm_eq_sqrt_norm_inner_self :=
      norm_eq_sqrt_norm_inner_self_completion (ι := .id ℂ A) denseRange_id }

-- Ensures `instCStarModule` at `A = ℂ` is defeq to `WithCStarModule.instCStarModuleComplex`.
example {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℂ H] :
    (instCStarModule : CStarModule ℂ (Completion H)) = WithCStarModule.instCStarModuleComplex := by
  with_reducible_and_instances rfl

end UniformSpace.Completion

namespace TauCeti.PosSemidefCStarModule

variable {A E : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [SeminormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [PosSemidefCStarModule A E]

@[simp] theorem inner_coe (x y : E) :
    inner A (x : Completion E) (y : Completion E) = inner A x y :=
  IsPosSemidefCStarModuleAlong.inner_coe (ι := .id ℂ A) denseRange_id x y
theorem continuous_inner_completion :
    Continuous (Function.uncurry (inner A (E := Completion E))) :=
  IsPosSemidefCStarModuleAlong.continuous_inner_completion (ι := .id ℂ A) denseRange_id
@[fun_prop] theorem continuous_inner_completion_comp {α : Type*} [TopologicalSpace α]
    {f g : α → Completion E} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun t ↦ inner A (f t) (g t) :=
  IsPosSemidefCStarModuleAlong.continuous_inner_completion_comp (ι := .id ℂ A) denseRange_id hf hg

/-- `Completion.completionSeparationQuotientₗᵢ ℂ E` preserves the `A`-valued inner product,
identifying `Completion (SeparationQuotient E)` with `Completion E` as Hilbert `A`-modules. -/
@[simp] theorem inner_completionSeparationQuotientₗᵢ (u v : Completion (SeparationQuotient E)) :
    inner A (Completion.completionSeparationQuotientₗᵢ ℂ E u)
      (Completion.completionSeparationQuotientₗᵢ ℂ E v) = inner A u v := by
  let f : SeparationQuotient E →ₗ[ℂ] Completion E :=
    (SeparationQuotient.liftₗᵢ (Completion.toComplₗᵢ : E →ₗᵢ[ℂ] Completion E)).toLinearMap
  have hf : ∀ p q : SeparationQuotient E, inner A (f p) (f q) = inner A p q :=
    SeparationQuotient.surjective_mk.forall₂.2 fun _ _ ↦ by simp [f]
  have heq : (Completion.completionSeparationQuotientₗᵢ ℂ E).toLinearIsometry =
      IsPosSemidefCStarModuleAlong.liftOfInner (.id ℂ A) f hf :=
    (IsPosSemidefCStarModuleAlong.eq_liftOfInner_iff (.id ℂ A) f hf _).mpr <|
      SeparationQuotient.surjective_mk.forall.2 fun _ ↦ by simp [f]
  simpa only [← LinearIsometryEquiv.coe_toLinearIsometry, heq] using
    IsPosSemidefCStarModuleAlong.inner_liftOfInner (ι := .id ℂ A) denseRange_id f hf u v
@[simp] theorem inner_completionSeparationQuotientₗᵢ_symm (u v : Completion E) :
    inner A ((Completion.completionSeparationQuotientₗᵢ ℂ E).symm u)
      ((Completion.completionSeparationQuotientₗᵢ ℂ E).symm v) = inner A u v := by
  simpa only [LinearIsometryEquiv.apply_symm_apply] using
    (inner_completionSeparationQuotientₗᵢ
      ((Completion.completionSeparationQuotientₗᵢ ℂ E).symm u)
      ((Completion.completionSeparationQuotientₗᵢ ℂ E).symm v)).symm

variable (E) in
/-- Completion preserves the closed complex linear span of the `A`-valued inner products. -/
theorem topologicalClosure_span_range_inner_completion :
    (Submodule.span ℂ
        (Set.range fun p : Completion E × Completion E ↦ inner A p.1 p.2)).topologicalClosure =
      (Submodule.span ℂ (Set.range fun p : E × E ↦ inner A p.1 p.2)).topologicalClosure :=
  IsPosSemidefCStarModuleAlong.topologicalClosure_span_range_inner_completion (ι := .id ℂ A) E
    denseRange_id

end TauCeti.PosSemidefCStarModule

namespace TauCeti.IsPosSemidefCStarModuleAlong

section IdSMul

variable {A E F : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [SeminormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [PosSemidefCStarModule A E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] [SMul A F] [CStarModule A F]

@[simp] theorem extAction_id_apply (hι : DenseRange (NonUnitalStarAlgHom.id ℂ A))
    (a : A) (z : Completion E) : extAction E hι a z = a • z := extAction_iota_apply hι a z
@[simp] theorem liftOfInner_smul (f : E →ₗ[ℂ] F)
    (hf : ∀ x y : E, inner A (f x) (f y) = inner A x y) (a : A) (z : Completion E) :
    liftOfInner (.id ℂ A) f hf (a • z) = a • liftOfInner (.id ℂ A) f hf z := by
  rw [← extAction_id_apply denseRange_id a z]
  exact liftOfInner_extAction (ι := .id ℂ A) denseRange_id f hf a z
@[simp] theorem equivOfInner_smul (f : E →ₗ[ℂ] F)
    (hf : ∀ x y : E, inner A (f x) (f y) = inner A x y) (hdense : DenseRange f)
    (a : A) (z : Completion E) :
    equivOfInner (.id ℂ A) f hf hdense (a • z) = a • equivOfInner (.id ℂ A) f hf hdense z := by
  rw [← extAction_id_apply denseRange_id a z]
  exact equivOfInner_extAction (ι := .id ℂ A) denseRange_id f hf hdense a z
@[simp] theorem equivOfInner_symm_smul (f : E →ₗ[ℂ] F)
    (hf : ∀ x y : E, inner A (f x) (f y) = inner A x y) (hdense : DenseRange f)
    (a : A) (y : F) :
    (equivOfInner (.id ℂ A) f hf hdense).symm (a • y) =
      a • (equivOfInner (.id ℂ A) f hf hdense).symm y :=
  (equivOfInner (.id ℂ A) f hf hdense).injective <| by simp
@[simp] theorem inner_liftOfInner_id (f : E →ₗ[ℂ] F)
    (hf : ∀ x y : E, inner A (f x) (f y) = inner A x y) (u v : Completion E) :
    inner A (liftOfInner (.id ℂ A) f hf u) (liftOfInner (.id ℂ A) f hf v) = inner A u v :=
  inner_liftOfInner denseRange_id f hf u v
@[simp] theorem inner_equivOfInner_id (f : E →ₗ[ℂ] F)
    (hf : ∀ x y : E, inner A (f x) (f y) = inner A x y) (hdense : DenseRange f)
    (u v : Completion E) :
    inner A (equivOfInner (.id ℂ A) f hf hdense u) (equivOfInner (.id ℂ A) f hf hdense v) =
      inner A u v :=
  inner_equivOfInner denseRange_id f hf hdense u v
@[simp] theorem inner_equivOfInner_symm_id (f : E →ₗ[ℂ] F)
    (hf : ∀ x y : E, inner A (f x) (f y) = inner A x y) (hdense : DenseRange f) (u v : F) :
    inner A ((equivOfInner (.id ℂ A) f hf hdense).symm u)
      ((equivOfInner (.id ℂ A) f hf hdense).symm v) = inner A u v :=
  inner_equivOfInner_symm denseRange_id f hf hdense u v

end IdSMul
/-! ### Completing a dense `⋆`-subalgebra as a right Hilbert module -/

section SubalgebraRightModule

variable {A S : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [SetLike S A] [NonUnitalSubringClass S A] [SMulMemClass S ℂ A] [StarMemClass S A]

private lemma inner_subtype_eq (s : S) (x y : s) :
    inner Aᵐᵒᵖ (LinearMap.ofClass (NonUnitalStarSubalgebraClass.subtype s) x)
      (LinearMap.ofClass (NonUnitalStarSubalgebraClass.subtype s) y) = inner Aᵐᵒᵖ x y := by
  rw [CStarModule.inner_mulOpposite]
  exact (PosSemidefCStarModule.rightModuleCoreAlong_inner s x y).symm

/-- Completing a dense `⋆`-subalgebra `s` of a C⋆-algebra `A` in its right-module inner product
recovers `A` as a right Hilbert `A`-module via `equivOfInner`, intertwining `extAction` with right
multiplication in `A`. -/
noncomputable def completionRightModuleEquiv (s : S) (hs : Dense (s : Set A)) :
    Completion s ≃ₗᵢ[ℂ] A :=
  equivOfInner (NonUnitalStarSubalgebraClass.subtype s).op
    (LinearMap.ofClass (NonUnitalStarSubalgebraClass.subtype s)) (inner_subtype_eq s)
    ((NonUnitalStarSubalgebraClass.denseRange_subtype s).mpr hs)

@[simp] theorem completionRightModuleEquiv_coe (s : S) (hs : Dense (s : Set A)) (x : s) :
    completionRightModuleEquiv s hs (x : Completion s) = (x : A) :=
  equivOfInner_coe (NonUnitalStarSubalgebraClass.subtype s).op
    (LinearMap.ofClass (NonUnitalStarSubalgebraClass.subtype s)) (inner_subtype_eq s)
    ((NonUnitalStarSubalgebraClass.denseRange_subtype s).mpr hs) x
@[simp] theorem completionRightModuleEquiv_symm_coe (s : S) (hs : Dense (s : Set A)) (x : s) :
    (completionRightModuleEquiv s hs).symm (x : A) = (x : Completion s) :=
  equivOfInner_symm_apply (NonUnitalStarSubalgebraClass.subtype s).op
    (LinearMap.ofClass (NonUnitalStarSubalgebraClass.subtype s)) (inner_subtype_eq s)
    ((NonUnitalStarSubalgebraClass.denseRange_subtype s).mpr hs) x
@[simp] theorem inner_completionRightModuleEquiv (s : S) (hs : Dense (s : Set A))
    (u v : Completion s) :
    inner Aᵐᵒᵖ (completionRightModuleEquiv s hs u) (completionRightModuleEquiv s hs v) =
      inner Aᵐᵒᵖ u v :=
  inner_equivOfInner ((NonUnitalStarSubalgebraClass.denseRange_subtype_op s).mpr hs)
    (LinearMap.ofClass (NonUnitalStarSubalgebraClass.subtype s)) (inner_subtype_eq s)
    ((NonUnitalStarSubalgebraClass.denseRange_subtype s).mpr hs) u v
@[simp] theorem completionRightModuleEquiv_extAction (s : S) (hs : Dense (s : Set A))
    (hι : DenseRange (NonUnitalStarSubalgebraClass.subtype s).op) (a : A) (z : Completion s) :
    completionRightModuleEquiv s hs (extAction s hι (op a) z) =
      completionRightModuleEquiv s hs z * a :=
  equivOfInner_extAction hι
    (LinearMap.ofClass (NonUnitalStarSubalgebraClass.subtype s)) (inner_subtype_eq s)
    ((NonUnitalStarSubalgebraClass.denseRange_subtype s).mpr hs) (op a) z
@[simp] theorem completionRightModuleEquiv_symm_mul (s : S) (hs : Dense (s : Set A)) (b a : A) :
    (completionRightModuleEquiv s hs).symm (b * a) =
      extAction s ((NonUnitalStarSubalgebraClass.denseRange_subtype_op s).mpr hs) (op a)
        ((completionRightModuleEquiv s hs).symm b) :=
  equivOfInner_symm_extAction ((NonUnitalStarSubalgebraClass.denseRange_subtype_op s).mpr hs)
    (LinearMap.ofClass (NonUnitalStarSubalgebraClass.subtype s)) (inner_subtype_eq s)
    ((NonUnitalStarSubalgebraClass.denseRange_subtype s).mpr hs) (op a) b

end SubalgebraRightModule
end TauCeti.IsPosSemidefCStarModuleAlong

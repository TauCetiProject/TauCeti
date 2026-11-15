/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Module.Self
public import TauCeti.Analysis.CStarAlgebra.Module.Semidef

/-!
# Completions of pre-Hilbert and positive semidefinite C⋆-modules

This file constructs Hilbert C⋆-module completions of pre-Hilbert and positive semidefinite
modules, extends dense `⋆`-subalgebra actions to their C⋆-completion, and proves the universal
properties for bounded module maps and inner-product-preserving maps.

For `E` carrying `TauCeti.PosSemidefCStarModuleAlong ι E` along dense `ι : A₀ →⋆ₙₐ[ℂ] A`,
`UniformSpace.Completion.toInner` extends `⟪·, ·⟫_A` continuously to `Completion E` with
`‖z‖ = √‖⟪z, z⟫_A‖` and definiteness `⟪z, z⟫_A = 0 ↔ z = 0`, killing null vectors and completing in
one step. At `ι = id`, `UniformSpace.Completion.instCStarModule` equips `Completion E` with a global
`CStarModule A` instance (definitionally equal at `A = ℂ` to
`WithCStarModule.instCStarModuleComplex`) compatible with `completionSeparationQuotientₗᵢ`. For
general dense `ι`, `PosSemidefCStarModuleAlong.extAction` extends the `A₀`-action to a unique
contractive bilinear action `A →L[ℂ] Completion E →L[ℂ] Completion E` (`cstarModuleOfDense`).

## Main declarations

* `UniformSpace.Completion.instCStarModule` and
  `UniformSpace.Completion.inner_completionSeparationQuotientₗᵢ`: global `CStarModule A` instance on
  `Completion E` and compatibility with `completionSeparationQuotientₗᵢ`.
* `TauCeti.PosSemidefCStarModuleAlong.extAction`, `extSMul`, and `cstarModuleOfDense`: unique
  extension of a dense `⋆`-subalgebra action to a Hilbert `A`-module structure on `Completion E`.
* `ContinuousLinearMap.fromCompletion_extAction`: universal property of `Completion E` for bounded
  module maps over a dense `⋆`-subalgebra.
* `TauCeti.PosSemidefCStarModuleAlong.liftOfInner`, `equivOfInner` and
  `UniformSpace.Completion.liftOfInner`, `equivOfInner`: universal property of `Completion E` for
  inner-product-preserving linear maps and isometric equivalence under dense range.
* `NonUnitalStarSubalgebra.completionRightModuleEquiv`: completing a dense nonunital `⋆`-subalgebra
  `S` of `A` as a right `S`-module recovers `A` as a right Hilbert `A`-module.

## References

* E. Christopher Lance, *Hilbert C⋆-Modules: A Toolkit for Operator Algebraists*, Chapter 1.
* Iain Raeburn and Dana P. Williams, *Morita Equivalence and Continuous-Trace C⋆-Algebras*,
  Chapter 2, Lemma 2.16.
-/

public section

open MulOpposite UniformSpace
open scoped ComplexOrder

/-! ### Inner product extension, definiteness, and extended action over a dense `⋆`-subalgebra -/

namespace TauCeti.PosSemidefCStarModuleAlong

section LiftOfInnerBasic

variable {A₀ A E F : Type*} [NonUnitalSemiring A₀] [StarRing A₀] [Module ℂ A₀]
  [NonUnitalCStarAlgebra A] [PartialOrder A] {ι : A₀ →⋆ₙₐ[ℂ] A}
  [SeminormedAddCommGroup E] [NormedSpace ℂ E] [SMul A₀ E] [Inner A E]
  [PosSemidefCStarModuleAlong ι E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] [SMul A F] [CStarModule A F]
  (f : E →ₗ[ℂ] F) (hf : ∀ x y : E, inner A (f x) (f y) = inner A x y)

/-- **Universal property of `Completion E` for inner-product-preserving maps:** any `ℂ`-linear map
`f : E →ₗ[ℂ] F` into a complete Hilbert `A`-module `F` preserving `inner A` (without assuming
continuity or module linearity in advance) extends to a linear isometry `Completion E →ₗᵢ[ℂ] F`. -/
noncomputable def liftOfInner : Completion E →ₗᵢ[ℂ] F :=
  LinearIsometry.fromCompletion
    { f with
      norm_map' x := by
        rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := A) (f x), hf,
          norm_eq_sqrt_norm_inner_self (ι := ι) x] }

@[simp] theorem liftOfInner_coe (x : E) : liftOfInner (ι := ι) f hf (x : Completion E) = f x :=
  LinearIsometry.fromCompletion_apply_coe _ x

/-- Uniqueness of `liftOfInner` on `Completion E`. -/
theorem eq_liftOfInner_iff (g : Completion E →ₗᵢ[ℂ] F) :
    g = liftOfInner (ι := ι) f hf ↔ ∀ x : E, g (x : Completion E) = f x :=
  ⟨fun h x ↦ by rw [h, liftOfInner_coe], fun h ↦ LinearIsometry.ext fun z ↦
    Completion.induction_on z (isClosed_eq g.continuous (liftOfInner (ι := ι) f hf).continuous)
      fun x ↦ by rw [h, liftOfInner_coe]⟩

/-- When an `inner A`-preserving linear map `f : E →ₗ[ℂ] F` into a complete Hilbert `A`-module `F`
has dense range, `liftOfInner` upgrades to a linear isometric equivalence
`Completion E ≃ₗᵢ[ℂ] F`. -/
noncomputable def equivOfInner (hdense : DenseRange f) : Completion E ≃ₗᵢ[ℂ] F :=
  LinearIsometryEquiv.ofSurjective (liftOfInner (ι := ι) f hf)
    (LinearIsometry.surjective_fromCompletion_of_denseRange _ hdense)

theorem coe_equivOfInner (hdense : DenseRange f) :
    (equivOfInner (ι := ι) f hf hdense : Completion E → F) = liftOfInner (ι := ι) f hf :=
  LinearIsometryEquiv.coe_ofSurjective _ _

@[simp] theorem equivOfInner_coe (hdense : DenseRange f) (x : E) :
    equivOfInner (ι := ι) f hf hdense (x : Completion E) = f x :=
  liftOfInner_coe (ι := ι) f hf x

end LiftOfInnerBasic

section InnerCompletion

variable {A₀ A E : Type*} [NonUnitalRing A₀] [StarRing A₀] [Module ℂ A₀]
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A] {ι : A₀ →⋆ₙₐ[ℂ] A}
  [SeminormedAddCommGroup E] [NormedSpace ℂ E] [SMul A₀ E] [Inner A E]
  [PosSemidefCStarModuleAlong ι E]

/-- On `Completion E`, the extended `A`-valued inner product agrees with `inner A` on `E`. -/
theorem inner_coe (hι : DenseRange ι) (x y : E) :
    inner A (x : Completion E) (y : Completion E) = inner A x y :=
  (Completion.isDenseInducing_coe.prodMap Completion.isDenseInducing_coe).extend_eq
    (continuous_inner hι) (x, y)

/-- Joint continuity of the extended `A`-valued inner product on `Completion E`. -/
theorem continuous_inner_completion (hι : DenseRange ι) :
    Continuous (Function.uncurry (inner A (E := Completion E))) := by
  let inner' : E →+ E →+ A :=
    { toFun x :=
        { toFun y := inner A x y
          map_zero' := inner_zero_right (ι := ι) x
          map_add' _ _ := inner_add_right (ι := ι) }
      map_zero' := AddMonoidHom.ext <| inner_zero_left (ι := ι)
      map_add' x y := AddMonoidHom.ext <| inner_add_left (ι := ι) x y }
  have heq : Function.uncurry (inner A (E := Completion E)) =
      ((Completion.isDenseInducing_toCompl E).prodMap
        (Completion.isDenseInducing_toCompl E)).extend (fun p : E × E ↦ inner' p.1 p.2) := by
    rw [Completion.toInner, inner, Function.uncurry_curry _]; rfl
  rw [heq]
  exact (Completion.isDenseInducing_toCompl E).extend_Z_bilin
    (Completion.isDenseInducing_toCompl E) (continuous_inner hι)

/-- Continuity of `t ↦ ⟪f t, g t⟫_A` for maps into `Completion E`. -/
theorem continuous_inner_completion_comp (hι : DenseRange ι) {α : Type*} [TopologicalSpace α]
    {f g : α → Completion E} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun t ↦ inner A (f t) (g t) :=
  (continuous_inner_completion hι).comp (hf.prodMk hg)

theorem inner_add_right_completion (hι : DenseRange ι) (x y z : Completion E) :
    inner A x (y + z) = inner A x y + inner A x z := by
  refine Completion.induction_on₃ x y z (isClosed_eq ?_ ?_) fun a b c ↦ ?_
  · exact continuous_inner_completion_comp hι continuous_fst (by fun_prop)
  · exact (continuous_inner_completion_comp hι continuous_fst (by fun_prop)).add
      (continuous_inner_completion_comp hι continuous_fst (by fun_prop))
  · rw [← Completion.coe_add, inner_coe hι, inner_coe hι, inner_coe hι, inner_add_right (ι := ι)]

theorem inner_self_nonneg_completion (hι : DenseRange ι) (x : Completion E) :
    0 ≤ inner A x x :=
  Completion.induction_on x
    (isClosed_le continuous_const (continuous_inner_completion_comp hι continuous_id continuous_id))
    fun a ↦ by rw [inner_coe hι]; exact inner_self_nonneg (ι := ι)

theorem star_inner_completion (hι : DenseRange ι) (x y : Completion E) :
    star (inner A x y) = inner A y x :=
  Completion.induction_on₂ x y
    (isClosed_eq (continuous_star.comp <|
      continuous_inner_completion_comp hι continuous_fst continuous_snd)
      (continuous_inner_completion_comp hι continuous_snd continuous_fst))
    fun a b ↦ by rw [inner_coe hι, inner_coe hι, star_inner (ι := ι)]

theorem inner_add_left_completion (hι : DenseRange ι) (x y z : Completion E) :
    inner A (x + y) z = inner A x z + inner A y z := by
  rw [← star_inner_completion hι z (x + y), inner_add_right_completion hι, star_add,
    star_inner_completion hι, star_inner_completion hι]

theorem inner_zero_right_completion (hι : DenseRange ι) (x : Completion E) :
    inner A x (0 : Completion E) = 0 :=
  Completion.induction_on x
    (isClosed_eq (continuous_inner_completion_comp hι continuous_id continuous_const)
      continuous_const)
    fun a ↦ by rw [← Completion.coe_zero, inner_coe hι, inner_zero_right (ι := ι)]

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
    fun a b ↦ by
      rw [← Completion.coe_smul, inner_coe hι, inner_coe hι, inner_smul_right_complex (ι := ι)]

theorem inner_op_smul_right_completion (hι : DenseRange ι) (a₀ : A₀) (x y : Completion E) :
    inner A x (a₀ • y) = ι a₀ * inner A x y := by
  have : UniformContinuousConstSMul A₀ E := uniformContinuousConstSMul (ι := ι)
  exact Completion.induction_on₂ x y
    (isClosed_eq (continuous_inner_completion_comp hι continuous_fst (by fun_prop))
      (continuous_const.mul <|
        continuous_inner_completion_comp hι continuous_fst continuous_snd))
    fun a b ↦ by
      rw [← Completion.coe_smul, inner_coe hι, inner_coe hι, inner_op_smul_right (ι := ι)]

theorem norm_eq_sqrt_norm_inner_self_completion (hι : DenseRange ι) (x : Completion E) :
    ‖x‖ = √‖inner A x x‖ :=
  Completion.induction_on x
    (isClosed_eq continuous_norm (Real.continuous_sqrt.comp <|
      (continuous_inner_completion_comp hι continuous_id continuous_id).norm))
    fun a ↦ by rw [Completion.norm_coe, inner_coe hι, norm_eq_sqrt_norm_inner_self (ι := ι)]

/-- Definiteness of the extended `A`-valued inner product on `Completion E`: because `Completion E`
separates points by its norm, `⟪x, x⟫_A = 0 ↔ x = 0` holds even when `E` has nonzero null
vectors. -/
theorem inner_self_eq_zero_completion (hι : DenseRange ι) {x : Completion E} :
    inner A x x = 0 ↔ x = 0 := by
  rw [← norm_eq_zero (a := x), norm_eq_sqrt_norm_inner_self_completion hι,
    Real.sqrt_eq_zero (norm_nonneg _), norm_eq_zero]

/-- Vectors in `Completion E` are separated by their `A`-valued inner products. -/
theorem ext_inner_left_completion (hι : DenseRange ι) {z₁ z₂ : Completion E}
    (h : ∀ w : Completion E, inner A w z₁ = inner A w z₂) : z₁ = z₂ := by
  rw [← sub_eq_zero, ← inner_self_eq_zero_completion hι, inner_sub_right_completion hι,
    h (z₁ - z₂), sub_self]

/-- Testing inner products against vectors from the dense image of `E` already separates elements of
`Completion E`. -/
theorem ext_inner_coe_left_completion (hι : DenseRange ι) {z₁ z₂ : Completion E}
    (h : ∀ x : E, inner A (x : Completion E) z₁ = inner A (x : Completion E) z₂) : z₁ = z₂ :=
  ext_inner_left_completion hι fun w ↦ Completion.induction_on w
    (isClosed_eq (continuous_inner_completion_comp hι continuous_id continuous_const)
      (continuous_inner_completion_comp hι continuous_id continuous_const)) h

/-! #### Extending the action of a dense `⋆`-subalgebra to `Completion E` -/

private lemma smul_add_completion (hι : DenseRange ι) (a₀ : A₀) (y z : Completion E) :
    a₀ • (y + z) = a₀ • y + a₀ • z :=
  ext_inner_left_completion hι fun x ↦ by
    rw [inner_op_smul_right_completion hι, inner_add_right_completion hι, mul_add,
      inner_add_right_completion hι, inner_op_smul_right_completion hι,
      inner_op_smul_right_completion hι]

private lemma smul_comm_complex_completion (hι : DenseRange ι) (a₀ : A₀) (c : ℂ)
    (y : Completion E) : a₀ • (c • y) = c • (a₀ • y) :=
  ext_inner_left_completion hι fun x ↦ by
    rw [inner_op_smul_right_completion hι, inner_smul_right_complex_completion hι, mul_smul_comm,
      inner_smul_right_complex_completion hι, inner_op_smul_right_completion hι]

private lemma norm_smul_completion_le (a₀ : A₀) (y : Completion E) :
    ‖a₀ • y‖ ≤ ‖ι a₀‖ * ‖y‖ := by
  have : UniformContinuousConstSMul A₀ E := uniformContinuousConstSMul (ι := ι)
  refine Completion.induction_on y
    (isClosed_le (continuous_norm.comp (continuous_const_smul a₀))
      (continuous_const.mul continuous_norm)) fun x ↦ ?_
  simpa only [← Completion.coe_smul, Completion.norm_coe] using
    PosSemidefCStarModuleAlong.norm_smul_le (ι := ι) a₀ x

variable (E) in
private noncomputable def actCLM (hι : DenseRange ι) (a₀ : A₀) :
    Completion E →L[ℂ] Completion E :=
  LinearMap.mkContinuous
    { toFun y := a₀ • y
      map_add' := smul_add_completion hι a₀
      map_smul' c y := smul_comm_complex_completion hι a₀ c y }
    ‖ι a₀‖ (norm_smul_completion_le a₀)

variable (E) in
private lemma norm_actCLM_le (hι : DenseRange ι) (a₀ : A₀) :
    ‖actCLM E hι a₀‖ ≤ 1 * ‖LinearMap.ofClass ι a₀‖ := by
  rw [one_mul]; exact LinearMap.mkContinuous_norm_le _ (norm_nonneg _) _

variable (E) in
private noncomputable def actLM (hι : DenseRange ι) :
    A₀ →ₗ[ℂ] Completion E →L[ℂ] Completion E where
  toFun := actCLM E hι
  map_add' _ _ := ContinuousLinearMap.ext fun _ ↦ ext_inner_left_completion hι fun _ ↦ by
    simp [actCLM, inner_op_smul_right_completion hι, inner_add_right_completion hι, add_mul]
  map_smul' _ _ := ContinuousLinearMap.ext fun _ ↦ ext_inner_left_completion hι fun _ ↦ by
    simp [actCLM, inner_op_smul_right_completion hι, inner_smul_right_complex_completion hι,
      smul_mul_assoc]

omit [PartialOrder A] [StarOrderedRing A] in
private lemma denseRange_ofClass (hι : DenseRange ι) :
    DenseRange (LinearMap.ofClass ι : A₀ →ₗ[ℂ] A) := by
  rwa [LinearMap.coe_ofClass]

variable (E) in
/-- Extension of the `A₀`-action on `E` along a dense `⋆`-algebra homomorphism `ι : A₀ →⋆ₙₐ[ℂ] A`
to a contractive continuous bilinear action `A →L[ℂ] (Completion E →L[ℂ] Completion E)` on
`Completion E`. -/
noncomputable def extAction (hι : DenseRange ι) : A →L[ℂ] Completion E →L[ℂ] Completion E :=
  (actLM E hι).extendOfNorm (LinearMap.ofClass ι)

@[simp] theorem extAction_iot_apply (hι : DenseRange ι) (a₀ : A₀) (z : Completion E) :
    extAction E hι (ι a₀) z = a₀ • z :=
  DFunLike.congr_fun
    (LinearMap.extendOfNorm_eq (f := actLM E hι) (denseRange_ofClass hι)
      ⟨1, norm_actCLM_le E hι⟩ a₀) z

theorem extAction_iot_coe (hι : DenseRange ι) (a₀ : A₀) (x : E) :
    extAction E hι (ι a₀) (x : Completion E) = ((a₀ • x : E) : Completion E) := by
  have : UniformContinuousConstSMul A₀ E := uniformContinuousConstSMul (ι := ι)
  rw [extAction_iot_apply, Completion.coe_smul]

variable (E) in
theorem norm_extAction_apply_le (hι : DenseRange ι) (a : A) : ‖extAction E hι a‖ ≤ ‖a‖ := by
  simpa only [extAction, one_mul] using
    LinearMap.norm_extendOfNorm_apply_le (denseRange_ofClass hι) 1 (norm_actCLM_le E hι) a

theorem norm_extAction_apply_apply_le (hι : DenseRange ι) (a : A) (z : Completion E) :
    ‖extAction E hι a z‖ ≤ ‖a‖ * ‖z‖ :=
  ((extAction E hι a).le_opNorm z).trans <|
    mul_le_mul_of_nonneg_right (norm_extAction_apply_le E hι a) (norm_nonneg z)

variable (E) in
theorem norm_extAction_le (hι : DenseRange ι) : ‖extAction E hι‖ ≤ 1 :=
  LinearMap.opNorm_extendOfNorm_le (denseRange_ofClass hι) zero_le_one (norm_actCLM_le E hι)

@[simp] theorem inner_extAction_right (hι : DenseRange ι) (a : A) (u v : Completion E) :
    inner A u (extAction E hι a v) = a * inner A u v := by
  let P (b : A) : Prop := inner A u (extAction E hι b v) = b * inner A u v
  have hcont : Continuous fun b : A ↦ extAction E hι b v :=
    (ContinuousLinearMap.apply ℂ (Completion E) v).continuous.comp (extAction E hι).continuous
  refine hι.induction (P := P) ?_
    (isClosed_eq (continuous_inner_completion_comp hι continuous_const hcont)
      (continuous_id.mul continuous_const)) a
  rintro _ ⟨a₀, rfl⟩
  simp only [P, extAction_iot_apply, inner_op_smul_right_completion hι]

@[simp] theorem inner_extAction_left (hι : DenseRange ι) (a : A) (u v : Completion E) :
    inner A (extAction E hι a u) v = inner A u v * star a := by
  rw [← star_inner_completion hι v, inner_extAction_right hι, star_mul, star_inner_completion hι]

@[simp] theorem extAction_mul (hι : DenseRange ι) (a b : A) (z : Completion E) :
    extAction E hι (a * b) z = extAction E hι a (extAction E hι b z) :=
  ext_inner_left_completion hι fun _ ↦ by
    rw [inner_extAction_right hι, inner_extAction_right hι, inner_extAction_right hι, mul_assoc]

/-- Uniqueness of the extended action: a continuous `ℂ`-linear action
`g : A →L[ℂ] (Completion E →L[ℂ] Completion E)` equals `extAction E hι` if and only if it agrees
with the `A₀`-action on `(ι a₀, x)` for all `a₀ : A₀` and `x : E`. -/
theorem eq_extAction_iff (hι : DenseRange ι) (g : A →L[ℂ] Completion E →L[ℂ] Completion E) :
    g = extAction E hι ↔
      ∀ (a₀ : A₀) (x : E), g (ι a₀) (x : Completion E) = ((a₀ • x : E) : Completion E) := by
  have : UniformContinuousConstSMul A₀ E := uniformContinuousConstSMul (ι := ι)
  refine ⟨fun h a₀ x ↦ by rw [h, extAction_iot_apply, Completion.coe_smul], fun h ↦ ?_⟩
  symm
  refine LinearMap.extendOfNorm_unique (denseRange_ofClass hι) 1 (norm_actCLM_le E hι) g ?_
  ext a₀ z
  exact Completion.induction_on z (isClosed_eq (g (ι a₀)).continuous (actCLM E hι a₀).continuous)
    fun x ↦ by simpa [actLM, actCLM, Completion.coe_smul] using h a₀ x

variable (E) in
/-- Scalar multiplication of `A` on `Completion E` obtained by extending the `A₀`-action along a
dense `⋆`-algebra homomorphism `ι : A₀ →⋆ₙₐ[ℂ] A`. Kept as a reducible non-instance because `ι`
cannot be inferred from `A` and `Completion E`. -/
noncomputable abbrev extSMul (hι : DenseRange ι) : SMul A (Completion E) where
  smul a z := extAction E hι a z

variable (E) in
/-- Equipped with `extSMul E hι`, `Completion E` is a complete Hilbert `A`-module. -/
noncomputable abbrev cstarModuleOfDense (hι : DenseRange ι) :
    letI : SMul A (Completion E) := extSMul E hι
    CStarModule A (Completion E) :=
  letI : SMul A (Completion E) := extSMul E hι
  { toInner := Completion.toInner
    inner_add_right := inner_add_right_completion hι _ _ _
    inner_self_nonneg := inner_self_nonneg_completion hι _
    inner_self := inner_self_eq_zero_completion hι
    inner_op_smul_right := inner_extAction_right hι _ _ _
    inner_smul_right_complex := inner_smul_right_complex_completion hι _ _ _
    star_inner := star_inner_completion hι
    norm_eq_sqrt_norm_inner_self := norm_eq_sqrt_norm_inner_self_completion hι }

/-! #### Bounded module map extension and inner-product preservation on `Completion E` -/

/-- **Universal property of `Completion E` for bounded module maps over a dense `⋆`-subalgebra:**
if `f : E →L[ℂ] F` into a complete normed space `F` carrying a continuous `A`-action intertwines the
`A₀`-action with `ι`, then `f.fromCompletion` intertwines `PosSemidefCStarModuleAlong.extAction`
with the `A`-action on `F` (and satisfies `‖f.fromCompletion‖ = ‖f‖` by
`ContinuousLinearMap.norm_fromCompletion`). -/
theorem _root_.ContinuousLinearMap.fromCompletion_extAction {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] [SMul A F] [ContinuousSMul A F]
    (hι : DenseRange ι) (f : E →L[ℂ] F)
    (hf : ∀ (a₀ : A₀) (x : E), f (a₀ • x) = ι a₀ • f x) (a : A) (z : Completion E) :
    f.fromCompletion (extAction E hι a z) = a • f.fromCompletion z := by
  have : UniformContinuousConstSMul A₀ E := uniformContinuousConstSMul (ι := ι)
  have hsmul_iot (a₀ : A₀) (w : Completion E) :
      f.fromCompletion (a₀ • w) = ι a₀ • f.fromCompletion w :=
    Completion.induction_on w
      (isClosed_eq (f.fromCompletion.continuous.comp (continuous_const_smul a₀))
        ((continuous_const_smul (ι a₀)).comp f.fromCompletion.continuous))
      fun x ↦ by rw [← Completion.coe_smul, ContinuousLinearMap.fromCompletion_apply_coe,
        ContinuousLinearMap.fromCompletion_apply_coe, hf]
  let P (b : A) : Prop := f.fromCompletion (extAction E hι b z) = b • f.fromCompletion z
  have hcontL : Continuous fun b : A ↦ f.fromCompletion (extAction E hι b z) :=
    f.fromCompletion.continuous.comp
      ((ContinuousLinearMap.apply ℂ (Completion E) z).continuous.comp (extAction E hι).continuous)
  refine hι.induction (P := P) ?_ (isClosed_eq hcontL (continuous_id.smul continuous_const)) a
  rintro _ ⟨a₀, rfl⟩
  simp only [P, extAction_iot_apply, hsmul_iot]

section LiftOfInnerCompletion

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  [SMul A F] [CStarModule A F] (hι : DenseRange ι)
  (f : E →ₗ[ℂ] F) (hf : ∀ x y : E, inner A (f x) (f y) = inner A x y)

include hι in
@[simp] theorem inner_liftOfInner (u v : Completion E) :
    inner A (liftOfInner (ι := ι) f hf u) (liftOfInner (ι := ι) f hf v) = inner A u v := by
  let L := liftOfInner (ι := ι) f hf
  have hcontF : Continuous fun p : F × F ↦ inner A p.1 p.2 :=
    PosSemidefCStarModule.continuous_inner (A := A) (E := F)
  exact Completion.induction_on₂ u v
    (isClosed_eq
      (hcontF.comp ((L.continuous.comp continuous_fst).prodMk (L.continuous.comp continuous_snd)))
      (continuous_inner_completion hι))
    fun x y ↦ by rw [liftOfInner_coe, liftOfInner_coe, inner_coe hι, hf]

/-- `liftOfInner` automatically intertwines the extended `A`-action `extAction E hι` with the
`A`-action on `F`. -/
@[simp] theorem liftOfInner_extAction (a : A) (z : Completion E) :
    liftOfInner (ι := ι) f hf (extAction E hι a z) = a • liftOfInner (ι := ι) f hf z :=
  ContinuousLinearMap.fromCompletion_extAction hι _ (map_smul_of_inner_eq (ι := ι) f hf) a z

include hι in
@[simp] theorem inner_equivOfInner (hdense : DenseRange f) (u v : Completion E) :
    inner A (equivOfInner (ι := ι) f hf hdense u) (equivOfInner (ι := ι) f hf hdense v) =
      inner A u v :=
  inner_liftOfInner hι f hf u v

@[simp] theorem equivOfInner_extAction (hdense : DenseRange f) (a : A) (z : Completion E) :
    equivOfInner (ι := ι) f hf hdense (extAction E hι a z) =
      a • equivOfInner (ι := ι) f hf hdense z :=
  liftOfInner_extAction hι f hf a z

end LiftOfInnerCompletion

end InnerCompletion

/-- Over a unital C⋆-algebra `A`, the extended action sends `1 : A` to the identity on
`Completion E`, even when `A₀` itself is nonunital. -/
@[simp] theorem extAction_one {A₀ A E : Type*} [NonUnitalRing A₀] [StarRing A₀] [Module ℂ A₀]
    [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] {ι : A₀ →⋆ₙₐ[ℂ] A}
    [SeminormedAddCommGroup E] [NormedSpace ℂ E] [SMul A₀ E] [Inner A E]
    [PosSemidefCStarModuleAlong ι E] (hι : DenseRange ι) (z : Completion E) :
    extAction E hι (1 : A) z = z :=
  ext_inner_left_completion hι fun _ ↦ by rw [inner_extAction_right hι, one_mul]

end TauCeti.PosSemidefCStarModuleAlong

/-! ### Global `CStarModule` instance and universal properties for `Completion E` -/

namespace UniformSpace.Completion

open TauCeti

section PosSemidefCStarModule

variable {A E : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A]
  [SeminormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [PosSemidefCStarModule A E]

section StarOrdered

variable [StarOrderedRing A]

/-- On `Completion E`, the `A`-valued inner product restricts to the inner product on `E`. -/
@[simp] theorem cstarInner_coe (x y : E) :
    inner A (x : Completion E) (y : Completion E) = inner A x y :=
  PosSemidefCStarModuleAlong.inner_coe (ι := NonUnitalStarAlgHom.id ℂ A) denseRange_id x y

/-- Joint continuity of the `A`-valued inner product on `Completion E`. -/
theorem continuous_cstarInner : Continuous (Function.uncurry (inner A (E := Completion E))) :=
  PosSemidefCStarModuleAlong.continuous_inner_completion
    (ι := NonUnitalStarAlgHom.id ℂ A) denseRange_id

/-- Continuity of `t ↦ ⟪f t, g t⟫_A` for maps into `Completion E`. -/
@[fun_prop]
theorem _root_.Continuous.cstarInner_completion (A : Type*) [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] [SMul A E] [PosSemidefCStarModule A E]
    {α : Type*} [TopologicalSpace α] {f g : α → Completion E}
    (hf : Continuous f) (hg : Continuous g) : Continuous fun t ↦ inner A (f t) (g t) :=
  PosSemidefCStarModuleAlong.continuous_inner_completion_comp
    (ι := NonUnitalStarAlgHom.id ℂ A) denseRange_id hf hg

/-- The completion of any positive semidefinite `A`-module (and hence of any pre-Hilbert
`A`-module `CStarModule A E`) is a complete Hilbert `A`-module. -/
noncomputable instance instCStarModule : CStarModule A (Completion E) where
  toInner := Completion.toInner
  inner_add_right := PosSemidefCStarModuleAlong.inner_add_right_completion
    (ι := NonUnitalStarAlgHom.id ℂ A) denseRange_id _ _ _
  inner_self_nonneg := PosSemidefCStarModuleAlong.inner_self_nonneg_completion
    (ι := NonUnitalStarAlgHom.id ℂ A) denseRange_id _
  inner_self := PosSemidefCStarModuleAlong.inner_self_eq_zero_completion
    (ι := NonUnitalStarAlgHom.id ℂ A) denseRange_id
  inner_op_smul_right := PosSemidefCStarModuleAlong.inner_op_smul_right_completion
    (ι := NonUnitalStarAlgHom.id ℂ A) denseRange_id _ _ _
  inner_smul_right_complex := PosSemidefCStarModuleAlong.inner_smul_right_complex_completion
    (ι := NonUnitalStarAlgHom.id ℂ A) denseRange_id _ _ _
  star_inner := PosSemidefCStarModuleAlong.star_inner_completion
    (ι := NonUnitalStarAlgHom.id ℂ A) denseRange_id
  norm_eq_sqrt_norm_inner_self := PosSemidefCStarModuleAlong.norm_eq_sqrt_norm_inner_self_completion
    (ι := NonUnitalStarAlgHom.id ℂ A) denseRange_id

-- Ensures that at `A = ℂ`, `Completion.instCStarModule` is definitionally equal to
-- `WithCStarModule.instCStarModuleComplex` on `Completion H`.
example {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℂ H] :
    (instCStarModule : CStarModule ℂ (Completion H)) =
      WithCStarModule.instCStarModuleComplex := by
  with_reducible_and_instances rfl

/-- When `A₀ = A` and `ι = id`, `PosSemidefCStarModuleAlong.extAction` agrees with the standard
uniform-completion scalar multiplication on `Completion E`. -/
@[simp] theorem _root_.TauCeti.PosSemidefCStarModuleAlong.extAction_id_apply
    (hι : DenseRange (NonUnitalStarAlgHom.id ℂ A)) (a : A) (z : Completion E) :
    PosSemidefCStarModuleAlong.extAction E hι a z = a • z :=
  CStarModule.ext_inner_left (A := A) fun _ ↦ by
    rw [PosSemidefCStarModuleAlong.inner_extAction_right hι, CStarModule.inner_op_smul_right]

/-! #### Compatibility between `Completion (SeparationQuotient E)` and `Completion E` -/

/-- `completionSeparationQuotientₗᵢ ℂ E` preserves the `A`-valued inner product, identifying the
completion of the separated quotient with the uniform completion of `E` as Hilbert `A`-modules. -/
@[simp] theorem inner_completionSeparationQuotientₗᵢ (u v : Completion (SeparationQuotient E)) :
    inner A (completionSeparationQuotientₗᵢ ℂ E u) (completionSeparationQuotientₗᵢ ℂ E v) =
      inner A u v := by
  let e := completionSeparationQuotientₗᵢ ℂ E
  refine Completion.induction_on₂ u v
    (isClosed_eq
      ((continuous_cstarInner (A := A) (E := E)).comp (e.continuous.prodMap e.continuous))
      (continuous_cstarInner (A := A) (E := SeparationQuotient E))) <|
    SeparationQuotient.surjective_mk.forall₂.2 fun x y ↦ ?_
  rw [completionSeparationQuotientₗᵢ_coe_mk, completionSeparationQuotientₗᵢ_coe_mk,
    cstarInner_coe, ← SeparationQuotient.cstarInner_mk_mk x y]
  exact (cstarInner_coe (A := A) (SeparationQuotient.mk x) (SeparationQuotient.mk y)).symm

@[simp] theorem inner_completionSeparationQuotientₗᵢ_symm (u v : Completion E) :
    inner A ((completionSeparationQuotientₗᵢ ℂ E).symm u)
      ((completionSeparationQuotientₗᵢ ℂ E).symm v) = inner A u v := by
  simpa only [LinearIsometryEquiv.apply_symm_apply] using
    (inner_completionSeparationQuotientₗᵢ
      ((completionSeparationQuotientₗᵢ ℂ E).symm u)
      ((completionSeparationQuotientₗᵢ ℂ E).symm v)).symm

end StarOrdered

section LiftOfInner

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  [SMul A F] [CStarModule A F]
  (f : E →ₗ[ℂ] F) (hf : ∀ x y : E, inner A (f x) (f y) = inner A x y)

/-- **Universal property of `Completion E` for inner-product-preserving maps:** any `ℂ`-linear map
`f : E →ₗ[ℂ] F` into a complete Hilbert `A`-module `F` preserving `inner A` extends uniquely to a
linear isometry `Completion E →ₗᵢ[ℂ] F`. -/
noncomputable def liftOfInner : Completion E →ₗᵢ[ℂ] F :=
  PosSemidefCStarModuleAlong.liftOfInner (ι := NonUnitalStarAlgHom.id ℂ A) f hf

@[simp] theorem liftOfInner_coe (x : E) : liftOfInner f hf (x : Completion E) = f x :=
  PosSemidefCStarModuleAlong.liftOfInner_coe (ι := NonUnitalStarAlgHom.id ℂ A) f hf x

theorem eq_liftOfInner_iff (g : Completion E →ₗᵢ[ℂ] F) :
    g = liftOfInner f hf ↔ ∀ x : E, g (x : Completion E) = f x :=
  PosSemidefCStarModuleAlong.eq_liftOfInner_iff (ι := NonUnitalStarAlgHom.id ℂ A) f hf g

/-- Any `inner A`-preserving linear map `f : E →ₗ[ℂ] F` with dense range into a complete Hilbert
`A`-module `F` induces a canonical linear isometric equivalence `Completion E ≃ₗᵢ[ℂ] F`. -/
noncomputable def equivOfInner (hdense : DenseRange f) : Completion E ≃ₗᵢ[ℂ] F :=
  PosSemidefCStarModuleAlong.equivOfInner (ι := NonUnitalStarAlgHom.id ℂ A) f hf hdense

theorem coe_equivOfInner (hdense : DenseRange f) :
    (equivOfInner f hf hdense : Completion E → F) = liftOfInner f hf :=
  PosSemidefCStarModuleAlong.coe_equivOfInner (ι := NonUnitalStarAlgHom.id ℂ A) f hf hdense

@[simp] theorem equivOfInner_coe (hdense : DenseRange f) (x : E) :
    equivOfInner f hf hdense (x : Completion E) = f x :=
  PosSemidefCStarModuleAlong.equivOfInner_coe (ι := NonUnitalStarAlgHom.id ℂ A) f hf hdense x

variable [StarOrderedRing A]

@[simp] theorem inner_liftOfInner (u v : Completion E) :
    inner A (liftOfInner f hf u) (liftOfInner f hf v) = inner A u v :=
  PosSemidefCStarModuleAlong.inner_liftOfInner
    (ι := NonUnitalStarAlgHom.id ℂ A) denseRange_id f hf u v

@[simp] theorem liftOfInner_smul (a : A) (z : Completion E) :
    liftOfInner f hf (a • z) = a • liftOfInner f hf z := by
  have hι : DenseRange (NonUnitalStarAlgHom.id ℂ A) := denseRange_id
  have h := PosSemidefCStarModuleAlong.liftOfInner_extAction hι f hf a z
  rw [liftOfInner]
  rwa [PosSemidefCStarModuleAlong.extAction_id_apply] at h

@[simp] theorem inner_equivOfInner (hdense : DenseRange f) (u v : Completion E) :
    inner A (equivOfInner f hf hdense u) (equivOfInner f hf hdense v) = inner A u v :=
  PosSemidefCStarModuleAlong.inner_equivOfInner
    (ι := NonUnitalStarAlgHom.id ℂ A) denseRange_id f hf hdense u v

@[simp] theorem equivOfInner_smul (hdense : DenseRange f) (a : A) (z : Completion E) :
    equivOfInner f hf hdense (a • z) = a • equivOfInner f hf hdense z := by
  have hι : DenseRange (NonUnitalStarAlgHom.id ℂ A) := denseRange_id
  have h := PosSemidefCStarModuleAlong.equivOfInner_extAction hι f hf hdense a z
  rw [equivOfInner]
  rwa [PosSemidefCStarModuleAlong.extAction_id_apply] at h

end LiftOfInner

end PosSemidefCStarModule

end UniformSpace.Completion

/-! ### Completing a dense `⋆`-subalgebra as a right Hilbert module -/

namespace NonUnitalStarSubalgebra

open TauCeti

variable {A : Type*} [NonUnitalCStarAlgebra A] (S : NonUnitalStarSubalgebra ℂ A)

theorem denseRange_subtype :
    DenseRange (NonUnitalStarSubalgebraClass.subtype S) ↔ Dense (S : Set A) := by
  rw [DenseRange, NonUnitalStarSubalgebraClass.coe_subtype, Subtype.range_coe_subtype,
    SetLike.setOfPred_mem_eq]

theorem denseRange_subtype_op :
    DenseRange (NonUnitalStarSubalgebraClass.subtype S).op ↔ Dense (S : Set A) :=
  (NonUnitalStarAlgHom.denseRange_op _).trans S.denseRange_subtype

private lemma denseRange_subtype_ofClass (hS : Dense (S : Set A)) :
    DenseRange (LinearMap.ofClass (NonUnitalStarSubalgebraClass.subtype S)) := by
  rwa [LinearMap.coe_ofClass, S.denseRange_subtype]

variable [PartialOrder A] [StarOrderedRing A]

/-- With its subtype norm and right multiplication over `Sᵐᵒᵖ`, any nonunital `⋆`-subalgebra `S`
of a C⋆-algebra `A` satisfies `PosSemidefCStarModuleAlong (subtype S).op S` with respect to
`S.rightModuleDenseCore.toInner`. -/
theorem posSemidefCStarModuleAlong_op :
    letI : Inner Aᵐᵒᵖ S := S.rightModuleDenseCore.toInner
    PosSemidefCStarModuleAlong (NonUnitalStarSubalgebraClass.subtype S).op S := by
  let : Inner Aᵐᵒᵖ S := S.rightModuleDenseCore.toInner
  refine
    { inner_add_right := S.rightModuleDenseCore.inner_add_right
      inner_self_nonneg := S.rightModuleDenseCore.inner_self_nonneg
      inner_op_smul_right := S.rightModuleDenseCore.inner_op_smul_right
      inner_smul_right_complex := S.rightModuleDenseCore.inner_smul_right_complex
      star_inner := S.rightModuleDenseCore.star_inner
      norm_eq_sqrt_norm_inner_self := fun x ↦ ?_ }
  have h : inner Aᵐᵒᵖ x x = op (star (x : A) * (x : A)) := S.rightModuleDenseCore_inner x x
  rw [h, AddSubgroupClass.coe_norm, MulOpposite.norm_op, CStarRing.norm_star_mul_self,
    Real.sqrt_mul_self (norm_nonneg _)]

private lemma inner_subtype_eq (x y : S) :
    letI : Inner Aᵐᵒᵖ S := S.rightModuleDenseCore.toInner
    inner Aᵐᵒᵖ (LinearMap.ofClass (NonUnitalStarSubalgebraClass.subtype S) x)
      (LinearMap.ofClass (NonUnitalStarSubalgebraClass.subtype S) y) = inner Aᵐᵒᵖ x y := by
  rw [CStarModule.inner_mulOpposite]; exact (S.rightModuleDenseCore_inner x y).symm

/-- Completing a dense `⋆`-subalgebra `S` of a C⋆-algebra `A` in its right-module inner product
recovers `A` as a right Hilbert `A`-module via `equivOfInner`, intertwining `extAction` with right
multiplication in `A`. -/
noncomputable def completionRightModuleEquiv (hS : Dense (S : Set A)) : Completion S ≃ₗᵢ[ℂ] A :=
  letI : Inner Aᵐᵒᵖ S := S.rightModuleDenseCore.toInner
  haveI := S.posSemidefCStarModuleAlong_op
  PosSemidefCStarModuleAlong.equivOfInner (ι := (NonUnitalStarSubalgebraClass.subtype S).op)
    (LinearMap.ofClass (NonUnitalStarSubalgebraClass.subtype S)) S.inner_subtype_eq
    (S.denseRange_subtype_ofClass hS)

@[simp] theorem completionRightModuleEquiv_coe (hS : Dense (S : Set A)) (x : S) :
    S.completionRightModuleEquiv hS (x : Completion S) = (x : A) := by
  let : Inner Aᵐᵒᵖ S := S.rightModuleDenseCore.toInner
  have := S.posSemidefCStarModuleAlong_op
  exact PosSemidefCStarModuleAlong.equivOfInner_coe
    (ι := (NonUnitalStarSubalgebraClass.subtype S).op)
    (LinearMap.ofClass (NonUnitalStarSubalgebraClass.subtype S)) S.inner_subtype_eq
    (S.denseRange_subtype_ofClass hS) x

/-- Under `completionRightModuleEquiv`, the extended right `A`-action on `Completion S` becomes
right multiplication in `A`. -/
theorem completionRightModuleEquiv_extAction (hS : Dense (S : Set A)) (a : A) (z : Completion S) :
    letI : Inner Aᵐᵒᵖ S := S.rightModuleDenseCore.toInner
    haveI := S.posSemidefCStarModuleAlong_op
    S.completionRightModuleEquiv hS
      (PosSemidefCStarModuleAlong.extAction S (S.denseRange_subtype_op.mpr hS) (op a) z) =
      S.completionRightModuleEquiv hS z * a := by
  let : Inner Aᵐᵒᵖ S := S.rightModuleDenseCore.toInner
  have := S.posSemidefCStarModuleAlong_op
  exact PosSemidefCStarModuleAlong.equivOfInner_extAction
    (ι := (NonUnitalStarSubalgebraClass.subtype S).op)
    (S.denseRange_subtype_op.mpr hS)
    (LinearMap.ofClass (NonUnitalStarSubalgebraClass.subtype S)) S.inner_subtype_eq
    (S.denseRange_subtype_ofClass hS) (op a) z

end NonUnitalStarSubalgebra

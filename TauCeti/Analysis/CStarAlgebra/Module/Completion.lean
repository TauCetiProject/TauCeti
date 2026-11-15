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

This file constructs the Hilbert C⋆-module completion of a pre-Hilbert module and of a positive
semidefinite module, extends coefficient actions from dense `⋆`-subalgebras to their C⋆-completion,
and establishes the universal properties of the completion for bounded module maps and
inner-product-preserving maps.

## Mathematical overview

Let `E` be a complex seminormed space carrying a positive semidefinite `A`-valued pairing over a
`⋆`-algebra `A₀` along a dense `⋆`-algebra homomorphism `ι : A₀ →⋆ₙₐ[ℂ] A` into a C⋆-algebra `A`
(`TauCeti.PosSemidefCStarModuleAlong ι E` with `DenseRange ι`). Because `⟪·, ·⟫_A : E × E → A` is
jointly continuous (`PosSemidefCStarModuleAlong.continuous_inner`), Bourbaki's bilinear extension
theorem (`IsDenseInducing.extend_Z_bilin`) extends it continuously to `UniformSpace.Completion E`
via Mathlib's `UniformSpace.Completion.toInner`. Passing the algebraic, positivity, and norm
identities to the completion by density shows `‖z‖ = √‖⟪z, z⟫_A‖` on `Completion E`. Since
`Completion E` is separated (`NormedAddCommGroup`), this automatically yields definiteness
`⟪z, z⟫_A = 0 ↔ z = 0`: uniform completion kills null vectors and completes in one step.

Specializing to `ι = NonUnitalStarAlgHom.id ℂ A` equips `Completion E` with a global
`CStarModule A (Completion E)` instance (`UniformSpace.Completion.instCStarModule`) for any
positive semidefinite `A`-module `E`, and in particular for any pre-Hilbert `A`-module
(`CStarModule A E`). At `A = ℂ`, this instance is definitionally equal to
`WithCStarModule.instCStarModuleComplex`. Moreover, the canonical isometric equivalence
`UniformSpace.Completion.completionSeparationQuotientₗᵢ ℂ E :
Completion (SeparationQuotient E) ≃ₗᵢ[ℂ] Completion E` preserves both `inner A` and scalar
multiplication, identifying the completion of the separated quotient with `Completion E`.

For a general dense `⋆`-subalgebra action (`ι : A₀ →⋆ₙₐ[ℂ] A`, `DenseRange ι`), separation of
vectors on `Completion E` by `inner A` shows without any module-associativity hypothesis on `E` that
the induced `A₀`-action on `Completion E` is complex-linear in both variables with operator norm
`‖a₀ • ·‖ ≤ ‖ι a₀‖`. Extending along `ι` via `LinearMap.extendOfNorm` produces a unique contractive
continuous bilinear action `PosSemidefCStarModuleAlong.extAction :
A →L[ℂ] (Completion E →L[ℂ] Completion E)` satisfying `⟪u, extAction E hι a v⟫_A = a * ⟪u, v⟫_A`
and `extAction E hι (a * b) z = extAction E hι a (extAction E hι b z)`, making `Completion E` a
complete Hilbert `A`-module (`PosSemidefCStarModuleAlong.cstarModuleOfDense`).

## Main declarations

* `UniformSpace.Completion.instCStarModule`: `CStarModule A (Completion E)` for any positive
  semidefinite (in particular, any pre-Hilbert) `A`-module `E`.
* `UniformSpace.Completion.inner_completionSeparationQuotientₗᵢ`: compatibility of
  `completionSeparationQuotientₗᵢ` with the `A`-valued inner product.
* `TauCeti.PosSemidefCStarModuleAlong.extAction`, `extSMul`, and `cstarModuleOfDense`: unique
  extension of an action of a dense `⋆`-subalgebra `A₀` to a Hilbert `A`-module structure on
  `Completion E`.
* `ContinuousLinearMap.fromCompletion_extAction` (together with
  `ContinuousLinearMap.fromCompletion_smul` and `ContinuousLinearMap.fromCompletion_unique`):
  universal property of `Completion E` for bounded module maps.
* `TauCeti.PosSemidefCStarModuleAlong.liftOfInner`, `equivOfInner`, and
  `UniformSpace.Completion.liftOfInner`, `equivOfInner`: universal property of `Completion E` for
  inner-product-preserving complex-linear maps, upgrading to an isometric isomorphism when the map
  has dense range.
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

/-! ### Dense-range helpers for identity, opposite homomorphisms, and `⋆`-subalgebras -/

namespace NonUnitalStarAlgHom

/-- The identity `⋆`-homomorphism `id R A : A →⋆ₙₐ[R] A` has dense range. -/
theorem denseRange_id (R A : Type*) [CommSemiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [Star A] [TopologicalSpace A] :
    DenseRange (NonUnitalStarAlgHom.id R A) := by
  simpa only [NonUnitalStarAlgHom.coe_id] using _root_.denseRange_id

/-- `f.op : Aᵐᵒᵖ →⋆ₙₐ[R] Bᵐᵒᵖ` has dense range if and only if `f : A →⋆ₙₐ[R] B` does. -/
@[simp]
theorem denseRange_op {R A B : Type*} [CommSemiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [Star A]
    [NonUnitalNonAssocSemiring B] [Module R B] [Star B] [TopologicalSpace B]
    (f : A →⋆ₙₐ[R] B) :
    DenseRange f.op ↔ DenseRange f := by
  have hrange : Set.range (f.op : Aᵐᵒᵖ → Bᵐᵒᵖ) = MulOpposite.op '' Set.range f := by
    ext b
    simp only [Set.mem_range, Set.mem_image]
    refine ⟨fun ⟨a, ha⟩ ↦ ⟨f a.unop, ⟨a.unop, rfl⟩, ?_⟩,
      fun ⟨y, ⟨a, ha⟩, hy⟩ ↦ ⟨MulOpposite.op a, ?_⟩⟩
    · rwa [← f.op_apply_apply a]
    · rw [f.op_apply_apply, unop_op, ha, hy]
  rw [DenseRange, DenseRange, hrange]
  exact MulOpposite.opHomeomorph.isDenseEmbedding.dense_image

end NonUnitalStarAlgHom

namespace NonUnitalStarSubalgebra

variable {R A : Type*} [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A] [Star A]
  [TopologicalSpace A]

/-- The canonical `⋆`-homomorphism `S →⋆ₙₐ[R] A` has dense range iff `S` is dense in `A`. -/
theorem denseRange_subtype (S : NonUnitalStarSubalgebra R A) :
    DenseRange (NonUnitalStarSubalgebraClass.subtype S) ↔ Dense (S : Set A) := by
  simp only [NonUnitalStarSubalgebraClass.coe_subtype, denseRange_subtype_val,
    SetLike.setOfPred_mem_eq]

/-- The opposite inclusion `S.op →⋆ₙₐ[R] Aᵐᵒᵖ` (written `(subtype S).op`) has dense range iff `S`
is dense in `A`. -/
theorem denseRange_subtype_op (S : NonUnitalStarSubalgebra R A) :
    DenseRange (NonUnitalStarSubalgebraClass.subtype S).op ↔ Dense (S : Set A) := by
  rw [NonUnitalStarAlgHom.denseRange_op, denseRange_subtype]

end NonUnitalStarSubalgebra

/-! ### Inner product extension, definiteness, and extended action over a dense `⋆`-subalgebra -/

namespace TauCeti.PosSemidefCStarModuleAlong

section LiftOfInnerBasic

variable {A₀ A E : Type*} [NonUnitalSemiring A₀] [StarRing A₀] [Module ℂ A₀]
  [NonUnitalCStarAlgebra A] [PartialOrder A]
  {ι : A₀ →⋆ₙₐ[ℂ] A}
  [SeminormedAddCommGroup E] [NormedSpace ℂ E] [SMul A₀ E] [Inner A E]
  [PosSemidefCStarModuleAlong ι E]

/-- **Universal property of `Completion E` for inner-product-preserving maps:** any `ℂ`-linear map
`f : E →ₗ[ℂ] F` into a complete Hilbert `A`-module `F` preserving `inner A` (without assuming
continuity or module linearity in advance) extends to a linear isometry `Completion E →ₗᵢ[ℂ] F`. -/
noncomputable def liftOfInner {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F] [SMul A F] [CStarModule A F]
    (f : E →ₗ[ℂ] F) (hf : ∀ x y : E, inner A (f x) (f y) = inner A x y) :
    Completion E →ₗᵢ[ℂ] F :=
  LinearIsometry.fromCompletion
    { f with
      norm_map' x := by
        rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := A) (f x), hf,
          norm_eq_sqrt_norm_inner_self (ι := ι) x] }

@[simp]
theorem liftOfInner_coe {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F] [SMul A F] [CStarModule A F]
    (f : E →ₗ[ℂ] F) (hf : ∀ x y : E, inner A (f x) (f y) = inner A x y) (x : E) :
    liftOfInner (ι := ι) f hf (x : Completion E) = f x :=
  LinearIsometry.fromCompletion_apply_coe _ x

/-- Uniqueness of `liftOfInner` on `Completion E`. -/
theorem eq_liftOfInner_iff {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F] [SMul A F] [CStarModule A F]
    (f : E →ₗ[ℂ] F) (hf : ∀ x y : E, inner A (f x) (f y) = inner A x y)
    (g : Completion E →ₗᵢ[ℂ] F) :
    g = liftOfInner (ι := ι) f hf ↔ ∀ x : E, g (x : Completion E) = f x := by
  refine ⟨fun h x ↦ by rw [h, liftOfInner_coe], fun h ↦ ?_⟩
  ext z
  exact Completion.induction_on z
    (isClosed_eq g.continuous (liftOfInner (ι := ι) f hf).continuous)
    fun x ↦ by rw [h, liftOfInner_coe]

/-- When an `inner A`-preserving linear map `f : E →ₗ[ℂ] F` into a complete Hilbert `A`-module `F`
has dense range, `liftOfInner` upgrades to a linear isometric equivalence
`Completion E ≃ₗᵢ[ℂ] F`. -/
noncomputable def equivOfInner {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F] [SMul A F] [CStarModule A F]
    (f : E →ₗ[ℂ] F) (hf : ∀ x y : E, inner A (f x) (f y) = inner A x y)
    (hdense : DenseRange f) : Completion E ≃ₗᵢ[ℂ] F :=
  LinearIsometryEquiv.ofSurjective (liftOfInner (ι := ι) f hf)
    (LinearIsometry.surjective_fromCompletion_of_denseRange _ hdense)

theorem coe_equivOfInner {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F] [SMul A F] [CStarModule A F]
    (f : E →ₗ[ℂ] F) (hf : ∀ x y : E, inner A (f x) (f y) = inner A x y)
    (hdense : DenseRange f) :
    (equivOfInner (ι := ι) f hf hdense : Completion E → F) = liftOfInner (ι := ι) f hf :=
  LinearIsometryEquiv.coe_ofSurjective _ _

@[simp]
theorem equivOfInner_coe {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F] [SMul A F] [CStarModule A F]
    (f : E →ₗ[ℂ] F) (hf : ∀ x y : E, inner A (f x) (f y) = inner A x y)
    (hdense : DenseRange f) (x : E) :
    equivOfInner (ι := ι) f hf hdense (x : Completion E) = f x :=
  liftOfInner_coe (ι := ι) f hf x

end LiftOfInnerBasic

section InnerCompletion

variable {A₀ A E : Type*} [NonUnitalRing A₀] [StarRing A₀] [Module ℂ A₀]
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {ι : A₀ →⋆ₙₐ[ℂ] A}
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
      map_zero' := by ext y; exact inner_zero_left (ι := ι) y
      map_add' x y := by ext z; exact inner_add_left (ι := ι) x y z }
  have hcont : Continuous fun p : E × E ↦ inner' p.1 p.2 := continuous_inner hι
  have heq : Function.uncurry (inner A (E := Completion E)) =
      ((Completion.isDenseInducing_toCompl E).prodMap
        (Completion.isDenseInducing_toCompl E)).extend (fun p : E × E ↦ inner' p.1 p.2) := by
    rw [Completion.toInner, inner, Function.uncurry_curry _]
    rfl
  rw [heq]
  exact (Completion.isDenseInducing_toCompl E).extend_Z_bilin
    (Completion.isDenseInducing_toCompl E) hcont

/-- Continuity of `t ↦ ⟪f t, g t⟫_A` for maps into `Completion E`. -/
theorem continuous_inner_completion_comp (hι : DenseRange ι) {α : Type*} [TopologicalSpace α]
    {f g : α → Completion E} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun t ↦ inner A (f t) (g t) :=
  (continuous_inner_completion hι).comp (hf.prodMk hg)

theorem inner_add_right_completion (hι : DenseRange ι) (x y z : Completion E) :
    inner A x (y + z) = inner A x y + inner A x z := by
  refine Completion.induction_on₃ x y z
    (isClosed_eq
      (continuous_inner_completion_comp hι continuous_fst
        ((continuous_fst.comp continuous_snd).add (continuous_snd.comp continuous_snd)))
      ((continuous_inner_completion_comp hι continuous_fst
          (continuous_fst.comp continuous_snd)).add
        (continuous_inner_completion_comp hι continuous_fst
          (continuous_snd.comp continuous_snd))))
    fun a b c ↦ ?_
  rw [← Completion.coe_add, inner_coe hι, inner_coe hι, inner_coe hι, inner_add_right (ι := ι)]

theorem inner_self_nonneg_completion (hι : DenseRange ι) (x : Completion E) :
    0 ≤ inner A x x := by
  refine Completion.induction_on x
    (isClosed_le continuous_const
      (continuous_inner_completion_comp hι continuous_id continuous_id))
    fun a ↦ ?_
  rw [inner_coe hι]
  exact inner_self_nonneg (ι := ι)

theorem star_inner_completion (hι : DenseRange ι) (x y : Completion E) :
    star (inner A x y) = inner A y x := by
  refine Completion.induction_on₂ x y
    (isClosed_eq
      (continuous_star.comp (continuous_inner_completion_comp hι continuous_fst continuous_snd))
      (continuous_inner_completion_comp hι continuous_snd continuous_fst))
    fun a b ↦ ?_
  rw [inner_coe hι, inner_coe hι, star_inner (ι := ι)]

theorem inner_add_left_completion (hι : DenseRange ι) (x y z : Completion E) :
    inner A (x + y) z = inner A x z + inner A y z := by
  rw [← star_inner_completion hι z (x + y), inner_add_right_completion hι, star_add,
    star_inner_completion hι, star_inner_completion hι]

theorem inner_zero_right_completion (hι : DenseRange ι) (x : Completion E) :
    inner A x (0 : Completion E) = 0 := by
  refine Completion.induction_on x
    (isClosed_eq (continuous_inner_completion_comp hι continuous_id continuous_const)
      continuous_const)
    fun a ↦ ?_
  rw [← Completion.coe_zero, inner_coe hι, inner_zero_right (ι := ι)]

theorem inner_zero_left_completion (hι : DenseRange ι) (x : Completion E) :
    inner A (0 : Completion E) x = 0 := by
  rw [← star_inner_completion hι x 0, inner_zero_right_completion hι, star_zero]

theorem inner_neg_right_completion (hι : DenseRange ι) (x y : Completion E) :
    inner A x (-y) = -inner A x y := by
  apply eq_neg_of_add_eq_zero_left
  rw [← inner_add_right_completion hι, neg_add_cancel, inner_zero_right_completion hι]

theorem inner_sub_right_completion (hι : DenseRange ι) (x y z : Completion E) :
    inner A x (y - z) = inner A x y - inner A x z := by
  rw [sub_eq_add_neg, inner_add_right_completion hι, inner_neg_right_completion hι,
    sub_eq_add_neg]

theorem inner_smul_right_complex_completion (hι : DenseRange ι) (c : ℂ) (x y : Completion E) :
    inner A x (c • y) = c • inner A x y := by
  refine Completion.induction_on₂ x y
    (isClosed_eq
      (continuous_inner_completion_comp hι continuous_fst (continuous_snd.const_smul c))
      ((continuous_inner_completion_comp hι continuous_fst continuous_snd).const_smul c))
    fun a b ↦ ?_
  rw [← Completion.coe_smul, inner_coe hι, inner_coe hι, inner_smul_right_complex (ι := ι)]

theorem inner_op_smul_right_completion (hι : DenseRange ι) (a₀ : A₀) (x y : Completion E) :
    inner A x (a₀ • y) = ι a₀ * inner A x y := by
  have : UniformContinuousConstSMul A₀ E := uniformContinuousConstSMul (ι := ι)
  refine Completion.induction_on₂ x y
    (isClosed_eq
      (continuous_inner_completion_comp hι continuous_fst (continuous_snd.const_smul a₀))
      (continuous_const.mul (continuous_inner_completion_comp hι continuous_fst continuous_snd)))
    fun a b ↦ ?_
  rw [← Completion.coe_smul, inner_coe hι, inner_coe hι, inner_op_smul_right (ι := ι)]

theorem norm_eq_sqrt_norm_inner_self_completion (hι : DenseRange ι) (x : Completion E) :
    ‖x‖ = √‖inner A x x‖ := by
  refine Completion.induction_on x
    (isClosed_eq continuous_norm
      (Real.continuous_sqrt.comp
        (continuous_norm.comp (continuous_inner_completion_comp hι continuous_id continuous_id))))
    fun a ↦ ?_
  rw [Completion.norm_coe, inner_coe hι, norm_eq_sqrt_norm_inner_self (ι := ι)]

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
    (h : ∀ x : E, inner A (x : Completion E) z₁ = inner A (x : Completion E) z₂) : z₁ = z₂ := by
  refine ext_inner_left_completion hι fun w ↦ ?_
  exact Completion.induction_on w
    (isClosed_eq (continuous_inner_completion_comp hι continuous_id continuous_const)
      (continuous_inner_completion_comp hι continuous_id continuous_const)) h

/-! #### Extending the action of a dense `⋆`-subalgebra to `Completion E` -/

private lemma smul_add_completion (hι : DenseRange ι) (a₀ : A₀) (y z : Completion E) :
    a₀ • (y + z) = a₀ • y + a₀ • z := by
  apply ext_inner_left_completion hι
  intro x
  rw [inner_op_smul_right_completion hι, inner_add_right_completion hι, mul_add,
    inner_add_right_completion hι, inner_op_smul_right_completion hι,
    inner_op_smul_right_completion hι]

private lemma smul_comm_complex_completion (hι : DenseRange ι) (a₀ : A₀) (c : ℂ)
    (y : Completion E) : a₀ • (c • y) = c • (a₀ • y) := by
  apply ext_inner_left_completion hι
  intro x
  rw [inner_op_smul_right_completion hι, inner_smul_right_complex_completion hι, mul_smul_comm,
    inner_smul_right_complex_completion hι, inner_op_smul_right_completion hι]

private lemma norm_smul_completion_le (a₀ : A₀) (y : Completion E) :
    ‖a₀ • y‖ ≤ ‖ι a₀‖ * ‖y‖ := by
  have : UniformContinuousConstSMul A₀ E := uniformContinuousConstSMul (ι := ι)
  refine Completion.induction_on y
    (isClosed_le (continuous_norm.comp (continuous_const_smul a₀))
      (continuous_const.mul continuous_norm))
    fun x ↦ ?_
  rw [← Completion.coe_smul, Completion.norm_coe, Completion.norm_coe]
  exact PosSemidefCStarModuleAlong.norm_smul_le (ι := ι) a₀ x

private noncomputable def actCLM (E : Type*) [SeminormedAddCommGroup E] [NormedSpace ℂ E]
    [SMul A₀ E] [Inner A E] [PosSemidefCStarModuleAlong ι E]
    (hι : DenseRange ι) (a₀ : A₀) :
    Completion E →L[ℂ] Completion E :=
  LinearMap.mkContinuous
    { toFun y := a₀ • y
      map_add' := smul_add_completion hι a₀
      map_smul' c y := by
        simp only [RingHom.id_apply]
        exact smul_comm_complex_completion hι a₀ c y }
    ‖ι a₀‖ (norm_smul_completion_le a₀)

private lemma norm_actCLM_le (E : Type*) [SeminormedAddCommGroup E] [NormedSpace ℂ E]
    [SMul A₀ E] [Inner A E] [PosSemidefCStarModuleAlong ι E]
    (hι : DenseRange ι) (a₀ : A₀) :
    ‖actCLM E hι a₀‖ ≤ 1 * ‖LinearMap.ofClass ι a₀‖ := by
  rw [one_mul]
  exact LinearMap.mkContinuous_norm_le _ (norm_nonneg _) _

private noncomputable def actLM (E : Type*) [SeminormedAddCommGroup E] [NormedSpace ℂ E]
    [SMul A₀ E] [Inner A E] [PosSemidefCStarModuleAlong ι E] (hι : DenseRange ι) :
    A₀ →ₗ[ℂ] Completion E →L[ℂ] Completion E where
  toFun := actCLM E hι
  map_add' a₀ b₀ := by
    ext y
    apply ext_inner_left_completion hι
    intro x
    simp only [add_apply, actCLM, LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk,
      inner_op_smul_right_completion hι, inner_add_right_completion hι, map_add, add_mul]
  map_smul' c a₀ := by
    ext y
    apply ext_inner_left_completion hι
    intro x
    simp only [smul_apply, RingHom.id_apply, actCLM, LinearMap.mkContinuous_apply,
      LinearMap.coe_mk, AddHom.coe_mk, inner_op_smul_right_completion hι,
      inner_smul_right_complex_completion hι, map_smul, smul_mul_assoc]

/-- Extension of the `A₀`-action on `E` along a dense `⋆`-algebra homomorphism `ι : A₀ →⋆ₙₐ[ℂ] A`
to a contractive continuous bilinear action `A →L[ℂ] (Completion E →L[ℂ] Completion E)` on
`Completion E`. -/
noncomputable def extAction (E : Type*) [SeminormedAddCommGroup E] [NormedSpace ℂ E]
    [SMul A₀ E] [Inner A E] [PosSemidefCStarModuleAlong ι E] (hι : DenseRange ι) :
    A →L[ℂ] Completion E →L[ℂ] Completion E :=
  (actLM E hι).extendOfNorm (LinearMap.ofClass ι)

@[simp]
theorem extAction_iot_apply (hι : DenseRange ι) (a₀ : A₀) (z : Completion E) :
    extAction E hι (ι a₀) z = a₀ • z := by
  have hι' : DenseRange (LinearMap.ofClass ι : A₀ →ₗ[ℂ] A) := by
    rwa [LinearMap.coe_ofClass]
  have heq : extAction E hι (LinearMap.ofClass ι a₀) = actLM E hι a₀ :=
    LinearMap.extendOfNorm_eq hι' ⟨1, norm_actCLM_le E hι⟩ a₀
  exact DFunLike.congr_fun heq z

theorem extAction_iot_coe (hι : DenseRange ι) (a₀ : A₀) (x : E) :
    extAction E hι (ι a₀) (x : Completion E) = ((a₀ • x : E) : Completion E) := by
  have : UniformContinuousConstSMul A₀ E := uniformContinuousConstSMul (ι := ι)
  rw [extAction_iot_apply, Completion.coe_smul]

theorem norm_extAction_apply_le (E : Type*) [SeminormedAddCommGroup E] [NormedSpace ℂ E]
    [SMul A₀ E] [Inner A E] [PosSemidefCStarModuleAlong ι E] (hι : DenseRange ι) (a : A) :
    ‖extAction E hι a‖ ≤ ‖a‖ := by
  have hι' : DenseRange (LinearMap.ofClass ι : A₀ →ₗ[ℂ] A) := by
    rwa [LinearMap.coe_ofClass]
  rw [extAction]
  simpa only [one_mul] using
    LinearMap.norm_extendOfNorm_apply_le hι' 1 (norm_actCLM_le E hι) a

theorem norm_extAction_apply_apply_le (hι : DenseRange ι) (a : A) (z : Completion E) :
    ‖extAction E hι a z‖ ≤ ‖a‖ * ‖z‖ :=
  calc ‖extAction E hι a z‖ ≤ ‖extAction E hι a‖ * ‖z‖ := (extAction E hι a).le_opNorm z
    _ ≤ ‖a‖ * ‖z‖ := mul_le_mul_of_nonneg_right (norm_extAction_apply_le E hι a) (norm_nonneg z)

theorem norm_extAction_le (E : Type*) [SeminormedAddCommGroup E] [NormedSpace ℂ E]
    [SMul A₀ E] [Inner A E] [PosSemidefCStarModuleAlong ι E] (hι : DenseRange ι) :
    ‖extAction E hι‖ ≤ 1 := by
  have hι' : DenseRange (LinearMap.ofClass ι : A₀ →ₗ[ℂ] A) := by
    rwa [LinearMap.coe_ofClass]
  exact LinearMap.opNorm_extendOfNorm_le hι' zero_le_one (norm_actCLM_le E hι)

@[simp]
theorem inner_extAction_right (hι : DenseRange ι) (a : A) (u v : Completion E) :
    inner A u (extAction E hι a v) = a * inner A u v := by
  let P (b : A) : Prop := inner A u (extAction E hι b v) = b * inner A u v
  have hcont : Continuous fun b : A ↦ extAction E hι b v :=
    (ContinuousLinearMap.apply ℂ (Completion E) v).continuous.comp (extAction E hι).continuous
  have hclosed : IsClosed {b : A | P b} :=
    isClosed_eq (continuous_inner_completion_comp hι continuous_const hcont)
      (continuous_id.mul continuous_const)
  refine hι.induction (P := P) ?_ hclosed a
  rintro _ ⟨a₀, rfl⟩
  simp only [P, extAction_iot_apply, inner_op_smul_right_completion hι]

@[simp]
theorem inner_extAction_left (hι : DenseRange ι) (a : A) (u v : Completion E) :
    inner A (extAction E hι a u) v = inner A u v * star a := by
  rw [← star_inner_completion hι v, inner_extAction_right hι, star_mul, star_inner_completion hι]

@[simp]
theorem extAction_mul (hι : DenseRange ι) (a b : A) (z : Completion E) :
    extAction E hι (a * b) z = extAction E hι a (extAction E hι b z) := by
  apply ext_inner_left_completion hι
  intro w
  rw [inner_extAction_right hι, inner_extAction_right hι, inner_extAction_right hι, mul_assoc]

/-- Uniqueness of the extended action: a continuous `ℂ`-linear action
`g : A →L[ℂ] (Completion E →L[ℂ] Completion E)` equals `extAction E hι` if and only if it agrees
with the `A₀`-action on `(ι a₀, x)` for all `a₀ : A₀` and `x : E`. -/
theorem eq_extAction_iff (hι : DenseRange ι)
    (g : A →L[ℂ] Completion E →L[ℂ] Completion E) :
    g = extAction E hι ↔
      ∀ (a₀ : A₀) (x : E), g (ι a₀) (x : Completion E) = ((a₀ • x : E) : Completion E) := by
  have : UniformContinuousConstSMul A₀ E := uniformContinuousConstSMul (ι := ι)
  refine ⟨fun h a₀ x ↦ by rw [h, extAction_iot_apply, Completion.coe_smul], fun h ↦ ?_⟩
  symm
  have hι' : DenseRange (LinearMap.ofClass ι : A₀ →ₗ[ℂ] A) := by
    rwa [LinearMap.coe_ofClass]
  refine LinearMap.extendOfNorm_unique hι' 1 (norm_actCLM_le E hι) g ?_
  ext a₀ z
  refine Completion.induction_on z (isClosed_eq (g (ι a₀)).continuous (actCLM E hι a₀).continuous)
    fun x ↦ ?_
  simpa only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, LinearMap.coe_ofClass, actLM,
    LinearMap.coe_mk, AddHom.coe_mk, actCLM, LinearMap.mkContinuous_apply,
    Completion.coe_smul] using h a₀ x

/-- Scalar multiplication of `A` on `Completion E` obtained by extending the `A₀`-action along a
dense `⋆`-algebra homomorphism `ι : A₀ →⋆ₙₐ[ℂ] A`. Kept as a reducible non-instance because `ι`
cannot be inferred from `A` and `Completion E`. -/
noncomputable abbrev extSMul (E : Type*) [SeminormedAddCommGroup E] [NormedSpace ℂ E]
    [SMul A₀ E] [Inner A E] [PosSemidefCStarModuleAlong ι E] (hι : DenseRange ι) :
    SMul A (Completion E) where
  smul a z := extAction E hι a z

/-- Equipped with `extSMul E hι`, `Completion E` is a complete Hilbert `A`-module. -/
noncomputable abbrev cstarModuleOfDense (E : Type*) [SeminormedAddCommGroup E] [NormedSpace ℂ E]
    [SMul A₀ E] [Inner A E] [PosSemidefCStarModuleAlong ι E] (hι : DenseRange ι) :
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

/-! #### Inner-product and action preservation of `liftOfInner` and `equivOfInner` -/

@[simp]
theorem inner_liftOfInner {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F] [SMul A F] [CStarModule A F] (hι : DenseRange ι)
    (f : E →ₗ[ℂ] F) (hf : ∀ x y : E, inner A (f x) (f y) = inner A x y)
    (u v : Completion E) :
    inner A (liftOfInner (ι := ι) f hf u) (liftOfInner (ι := ι) f hf v) = inner A u v := by
  let L := liftOfInner (ι := ι) f hf
  have hcontF : Continuous fun p : F × F ↦ inner A p.1 p.2 :=
    PosSemidefCStarModule.continuous_inner (A := A) (E := F)
  refine Completion.induction_on₂ u v
    (isClosed_eq
      (hcontF.comp ((L.continuous.comp continuous_fst).prodMk (L.continuous.comp continuous_snd)))
      (continuous_inner_completion hι))
    fun x y ↦ ?_
  rw [liftOfInner_coe, liftOfInner_coe, inner_coe hι, hf]

/-- `liftOfInner` automatically intertwines the extended `A`-action `extAction E hι` with the
`A`-action on `F`. -/
@[simp]
theorem liftOfInner_extAction {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F] [SMul A F] [CStarModule A F] (hι : DenseRange ι)
    (f : E →ₗ[ℂ] F) (hf : ∀ x y : E, inner A (f x) (f y) = inner A x y)
    (a : A) (z : Completion E) :
    liftOfInner (ι := ι) f hf (extAction E hι a z) = a • liftOfInner (ι := ι) f hf z := by
  let L := liftOfInner (ι := ι) f hf
  have hsmul_iot (a₀ : A₀) (w : Completion E) : L (a₀ • w) = ι a₀ • L w := by
    have : UniformContinuousConstSMul A₀ E := uniformContinuousConstSMul (ι := ι)
    refine Completion.induction_on w
      (isClosed_eq (L.continuous.comp (continuous_const_smul a₀))
        ((continuous_const_smul (ι a₀)).comp L.continuous))
      fun x ↦ ?_
    rw [← Completion.coe_smul, liftOfInner_coe, liftOfInner_coe,
      map_smul_of_inner_eq (ι := ι) f hf a₀ x]
  let P (b : A) : Prop := L (extAction E hι b z) = b • L z
  have hcontL : Continuous fun b : A ↦ L (extAction E hι b z) :=
    L.continuous.comp
      ((ContinuousLinearMap.apply ℂ (Completion E) z).continuous.comp (extAction E hι).continuous)
  have hclosed : IsClosed {b : A | P b} :=
    isClosed_eq hcontL (continuous_id.smul continuous_const)
  refine hι.induction (P := P) ?_ hclosed a
  rintro _ ⟨a₀, rfl⟩
  simp only [P, extAction_iot_apply, hsmul_iot]

@[simp]
theorem inner_equivOfInner {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F] [SMul A F] [CStarModule A F] (hι : DenseRange ι)
    (f : E →ₗ[ℂ] F) (hf : ∀ x y : E, inner A (f x) (f y) = inner A x y)
    (hdense : DenseRange f) (u v : Completion E) :
    inner A (equivOfInner (ι := ι) f hf hdense u) (equivOfInner (ι := ι) f hf hdense v) =
      inner A u v :=
  inner_liftOfInner (ι := ι) hι f hf u v

@[simp]
theorem equivOfInner_extAction {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F] [SMul A F] [CStarModule A F] (hι : DenseRange ι)
    (f : E →ₗ[ℂ] F) (hf : ∀ x y : E, inner A (f x) (f y) = inner A x y)
    (hdense : DenseRange f) (a : A) (z : Completion E) :
    equivOfInner (ι := ι) f hf hdense (extAction E hι a z) =
      a • equivOfInner (ι := ι) f hf hdense z :=
  liftOfInner_extAction (ι := ι) hι f hf a z

end InnerCompletion

section UnitalExtAction

variable {A₀ E : Type*} [NonUnitalRing A₀] [StarRing A₀] [Module ℂ A₀]
  [SeminormedAddCommGroup E] [NormedSpace ℂ E] [SMul A₀ E]

/-- Over a unital C⋆-algebra `A`, the extended action sends `1 : A` to the identity on
`Completion E`, even when `A₀` itself is nonunital. -/
@[simp]
theorem extAction_one {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {ι : A₀ →⋆ₙₐ[ℂ] A} [Inner A E] [PosSemidefCStarModuleAlong ι E]
    (hι : DenseRange ι) (z : Completion E) :
    extAction E hι (1 : A) z = z := by
  apply ext_inner_left_completion hι
  intro w
  rw [inner_extAction_right hι, one_mul]

end UnitalExtAction

end TauCeti.PosSemidefCStarModuleAlong

/-! ### Bounded module map extension for dense `⋆`-subalgebra actions -/

namespace ContinuousLinearMap

open TauCeti

/-- **Universal property of `Completion E` for bounded module maps over a dense `⋆`-subalgebra:**
if `f : E →L[ℂ] F` into a complete normed space `F` carrying a continuous `A`-action intertwines the
`A₀`-action with `ι`, then `f.fromCompletion` intertwines `PosSemidefCStarModuleAlong.extAction`
with the `A`-action on `F` (and satisfies `‖f.fromCompletion‖ = ‖f‖` by
`ContinuousLinearMap.norm_fromCompletion`). -/
theorem fromCompletion_extAction {A₀ A E F : Type*}
    [NonUnitalRing A₀] [StarRing A₀] [Module ℂ A₀]
    [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {ι : A₀ →⋆ₙₐ[ℂ] A}
    [SeminormedAddCommGroup E] [NormedSpace ℂ E] [SMul A₀ E] [Inner A E]
    [PosSemidefCStarModuleAlong ι E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    [SMul A F] [ContinuousSMul A F]
    (hι : DenseRange ι) (f : E →L[ℂ] F)
    (hf : ∀ (a₀ : A₀) (x : E), f (a₀ • x) = ι a₀ • f x)
    (a : A) (z : Completion E) :
    f.fromCompletion (PosSemidefCStarModuleAlong.extAction E hι a z) =
      a • f.fromCompletion z := by
  have : UniformContinuousConstSMul A₀ E :=
    PosSemidefCStarModuleAlong.uniformContinuousConstSMul (ι := ι)
  have hsmul_iot (a₀ : A₀) (w : Completion E) :
      f.fromCompletion (a₀ • w) = ι a₀ • f.fromCompletion w := by
    refine Completion.induction_on w
      (isClosed_eq (f.fromCompletion.continuous.comp (continuous_const_smul a₀))
        ((continuous_const_smul (ι a₀)).comp f.fromCompletion.continuous))
      fun x ↦ ?_
    rw [← Completion.coe_smul, fromCompletion_apply_coe, fromCompletion_apply_coe, hf]
  let P (b : A) : Prop :=
    f.fromCompletion (PosSemidefCStarModuleAlong.extAction E hι b z) = b • f.fromCompletion z
  have hcontL : Continuous fun b : A ↦
      f.fromCompletion (PosSemidefCStarModuleAlong.extAction E hι b z) :=
    f.fromCompletion.continuous.comp
      ((ContinuousLinearMap.apply ℂ (Completion E) z).continuous.comp
        (PosSemidefCStarModuleAlong.extAction E hι).continuous)
  have hclosed : IsClosed {b : A | P b} :=
    isClosed_eq hcontL (continuous_id.smul continuous_const)
  refine hι.induction (P := P) ?_ hclosed a
  rintro _ ⟨a₀, rfl⟩
  simp only [P, PosSemidefCStarModuleAlong.extAction_iot_apply, hsmul_iot]

end ContinuousLinearMap

/-! ### Global `CStarModule` instance and universal properties for `Completion E` -/

namespace UniformSpace.Completion

open TauCeti

section LiftBasic

variable {A E : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A]
  [SeminormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [PosSemidefCStarModule A E]

/-- **Universal property of `Completion E` for inner-product-preserving maps:** any `ℂ`-linear map
`f : E →ₗ[ℂ] F` into a complete Hilbert `A`-module `F` preserving `inner A` extends uniquely to a
linear isometry `Completion E →ₗᵢ[ℂ] F`. -/
noncomputable def liftOfInner {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F] [SMul A F] [CStarModule A F]
    (f : E →ₗ[ℂ] F) (hf : ∀ x y : E, inner A (f x) (f y) = inner A x y) :
    Completion E →ₗᵢ[ℂ] F :=
  PosSemidefCStarModuleAlong.liftOfInner (ι := NonUnitalStarAlgHom.id ℂ A) f hf

@[simp]
theorem liftOfInner_coe {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F] [SMul A F] [CStarModule A F]
    (f : E →ₗ[ℂ] F) (hf : ∀ x y : E, inner A (f x) (f y) = inner A x y) (x : E) :
    liftOfInner f hf (x : Completion E) = f x :=
  PosSemidefCStarModuleAlong.liftOfInner_coe (ι := NonUnitalStarAlgHom.id ℂ A) f hf x

theorem eq_liftOfInner_iff {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F] [SMul A F] [CStarModule A F]
    (f : E →ₗ[ℂ] F) (hf : ∀ x y : E, inner A (f x) (f y) = inner A x y)
    (g : Completion E →ₗᵢ[ℂ] F) :
    g = liftOfInner f hf ↔ ∀ x : E, g (x : Completion E) = f x :=
  PosSemidefCStarModuleAlong.eq_liftOfInner_iff (ι := NonUnitalStarAlgHom.id ℂ A) f hf g

/-- Any `inner A`-preserving linear map `f : E →ₗ[ℂ] F` with dense range into a complete Hilbert
`A`-module `F` induces a canonical linear isometric equivalence `Completion E ≃ₗᵢ[ℂ] F`. -/
noncomputable def equivOfInner {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F] [SMul A F] [CStarModule A F]
    (f : E →ₗ[ℂ] F) (hf : ∀ x y : E, inner A (f x) (f y) = inner A x y)
    (hdense : DenseRange f) : Completion E ≃ₗᵢ[ℂ] F :=
  PosSemidefCStarModuleAlong.equivOfInner (ι := NonUnitalStarAlgHom.id ℂ A) f hf hdense

theorem coe_equivOfInner {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F] [SMul A F] [CStarModule A F]
    (f : E →ₗ[ℂ] F) (hf : ∀ x y : E, inner A (f x) (f y) = inner A x y)
    (hdense : DenseRange f) :
    (equivOfInner f hf hdense : Completion E → F) = liftOfInner f hf :=
  PosSemidefCStarModuleAlong.coe_equivOfInner (ι := NonUnitalStarAlgHom.id ℂ A) f hf hdense

@[simp]
theorem equivOfInner_coe {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F] [SMul A F] [CStarModule A F]
    (f : E →ₗ[ℂ] F) (hf : ∀ x y : E, inner A (f x) (f y) = inner A x y)
    (hdense : DenseRange f) (x : E) :
    equivOfInner f hf hdense (x : Completion E) = f x :=
  PosSemidefCStarModuleAlong.equivOfInner_coe (ι := NonUnitalStarAlgHom.id ℂ A) f hf hdense x

end LiftBasic

section PosSemidefCStarModule

variable {A E : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [SeminormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [PosSemidefCStarModule A E]

/-- On `Completion E`, the `A`-valued inner product restricts to the inner product on `E`. -/
@[simp]
theorem cstarInner_coe (x y : E) :
    inner A (x : Completion E) (y : Completion E) = inner A x y :=
  PosSemidefCStarModuleAlong.inner_coe (NonUnitalStarAlgHom.denseRange_id ℂ A) x y

/-- Joint continuity of the `A`-valued inner product on `Completion E`. -/
theorem continuous_cstarInner :
    Continuous (Function.uncurry (inner A (E := Completion E))) :=
  PosSemidefCStarModuleAlong.continuous_inner_completion (NonUnitalStarAlgHom.denseRange_id ℂ A)

/-- Continuity of `t ↦ ⟪f t, g t⟫_A` for maps into `Completion E`. -/
@[fun_prop]
theorem _root_.Continuous.cstarInner_completion (A : Type*) [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] [SMul A E] [PosSemidefCStarModule A E]
    {α : Type*} [TopologicalSpace α] {f g : α → Completion E}
    (hf : Continuous f) (hg : Continuous g) :
    Continuous fun t ↦ inner A (f t) (g t) :=
  PosSemidefCStarModuleAlong.continuous_inner_completion_comp
    (NonUnitalStarAlgHom.denseRange_id ℂ A) hf hg

/-- The completion of any positive semidefinite `A`-module (and hence of any pre-Hilbert
`A`-module `CStarModule A E`) is a complete Hilbert `A`-module. -/
noncomputable instance instCStarModule : CStarModule A (Completion E) where
  toInner := Completion.toInner
  inner_add_right :=
    PosSemidefCStarModuleAlong.inner_add_right_completion
      (NonUnitalStarAlgHom.denseRange_id ℂ A) _ _ _
  inner_self_nonneg :=
    PosSemidefCStarModuleAlong.inner_self_nonneg_completion
      (NonUnitalStarAlgHom.denseRange_id ℂ A) _
  inner_self :=
    PosSemidefCStarModuleAlong.inner_self_eq_zero_completion
      (NonUnitalStarAlgHom.denseRange_id ℂ A)
  inner_op_smul_right :=
    PosSemidefCStarModuleAlong.inner_op_smul_right_completion
      (NonUnitalStarAlgHom.denseRange_id ℂ A) _ _ _
  inner_smul_right_complex :=
    PosSemidefCStarModuleAlong.inner_smul_right_complex_completion
      (NonUnitalStarAlgHom.denseRange_id ℂ A) _ _ _
  star_inner :=
    PosSemidefCStarModuleAlong.star_inner_completion
      (NonUnitalStarAlgHom.denseRange_id ℂ A)
  norm_eq_sqrt_norm_inner_self :=
    PosSemidefCStarModuleAlong.norm_eq_sqrt_norm_inner_self_completion
      (NonUnitalStarAlgHom.denseRange_id ℂ A)

-- Ensures that at `A = ℂ`, `Completion.instCStarModule` is definitionally equal to
-- `WithCStarModule.instCStarModuleComplex` on `Completion H`.
example {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℂ H] :
    (instCStarModule : CStarModule ℂ (Completion H)) =
      WithCStarModule.instCStarModuleComplex := by
  with_reducible_and_instances rfl

/-- When `A₀ = A` and `ι = id`, `PosSemidefCStarModuleAlong.extAction` agrees with the standard
uniform-completion scalar multiplication on `Completion E`. -/
@[simp]
theorem _root_.TauCeti.PosSemidefCStarModuleAlong.extAction_id_apply
    (hι : DenseRange (NonUnitalStarAlgHom.id ℂ A)) (a : A) (z : Completion E) :
    PosSemidefCStarModuleAlong.extAction E hι a z = a • z := by
  apply CStarModule.ext_inner_left (A := A)
  intro w
  rw [PosSemidefCStarModuleAlong.inner_extAction_right hι, CStarModule.inner_op_smul_right]

/-! #### Compatibility between `Completion (SeparationQuotient E)` and `Completion E` -/

/-- `completionSeparationQuotientₗᵢ ℂ E` preserves the `A`-valued inner product, identifying the
completion of the separated quotient with the uniform completion of `E` as Hilbert `A`-modules. -/
@[simp]
theorem inner_completionSeparationQuotientₗᵢ (u v : Completion (SeparationQuotient E)) :
    inner A (completionSeparationQuotientₗᵢ ℂ E u) (completionSeparationQuotientₗᵢ ℂ E v) =
      inner A u v := by
  let e := completionSeparationQuotientₗᵢ ℂ E
  refine Completion.induction_on₂ u v
    (isClosed_eq
      ((continuous_cstarInner (A := A) (E := E)).comp (e.continuous.prodMap e.continuous))
      (continuous_cstarInner (A := A) (E := SeparationQuotient E)))
    fun x y ↦ ?_
  obtain ⟨x, rfl⟩ := SeparationQuotient.surjective_mk x
  obtain ⟨y, rfl⟩ := SeparationQuotient.surjective_mk y
  rw [completionSeparationQuotientₗᵢ_coe_mk, completionSeparationQuotientₗᵢ_coe_mk,
    cstarInner_coe, ← SeparationQuotient.cstarInner_mk_mk x y]
  exact (cstarInner_coe (A := A) (SeparationQuotient.mk x) (SeparationQuotient.mk y)).symm

@[simp]
theorem inner_completionSeparationQuotientₗᵢ_symm (u v : Completion E) :
    inner A ((completionSeparationQuotientₗᵢ ℂ E).symm u)
      ((completionSeparationQuotientₗᵢ ℂ E).symm v) = inner A u v := by
  simpa only [LinearIsometryEquiv.apply_symm_apply] using
    (inner_completionSeparationQuotientₗᵢ
      ((completionSeparationQuotientₗᵢ ℂ E).symm u)
      ((completionSeparationQuotientₗᵢ ℂ E).symm v)).symm

@[simp]
theorem inner_liftOfInner {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F] [SMul A F] [CStarModule A F]
    (f : E →ₗ[ℂ] F) (hf : ∀ x y : E, inner A (f x) (f y) = inner A x y)
    (u v : Completion E) :
    inner A (liftOfInner f hf u) (liftOfInner f hf v) = inner A u v :=
  PosSemidefCStarModuleAlong.inner_liftOfInner
    (NonUnitalStarAlgHom.denseRange_id ℂ A) f hf u v

@[simp]
theorem liftOfInner_smul {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F] [SMul A F] [CStarModule A F]
    (f : E →ₗ[ℂ] F) (hf : ∀ x y : E, inner A (f x) (f y) = inner A x y)
    (a : A) (z : Completion E) :
    liftOfInner f hf (a • z) = a • liftOfInner f hf z := by
  have h := PosSemidefCStarModuleAlong.liftOfInner_extAction
    (NonUnitalStarAlgHom.denseRange_id ℂ A) f hf a z
  rwa [PosSemidefCStarModuleAlong.extAction_id_apply] at h

@[simp]
theorem inner_equivOfInner {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F] [SMul A F] [CStarModule A F]
    (f : E →ₗ[ℂ] F) (hf : ∀ x y : E, inner A (f x) (f y) = inner A x y)
    (hdense : DenseRange f) (u v : Completion E) :
    inner A (equivOfInner f hf hdense u) (equivOfInner f hf hdense v) = inner A u v :=
  PosSemidefCStarModuleAlong.inner_equivOfInner
    (NonUnitalStarAlgHom.denseRange_id ℂ A) f hf hdense u v

@[simp]
theorem equivOfInner_smul {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F] [SMul A F] [CStarModule A F]
    (f : E →ₗ[ℂ] F) (hf : ∀ x y : E, inner A (f x) (f y) = inner A x y)
    (hdense : DenseRange f) (a : A) (z : Completion E) :
    equivOfInner f hf hdense (a • z) = a • equivOfInner f hf hdense z := by
  have h := PosSemidefCStarModuleAlong.equivOfInner_extAction
    (NonUnitalStarAlgHom.denseRange_id ℂ A) f hf hdense a z
  rwa [PosSemidefCStarModuleAlong.extAction_id_apply] at h

end PosSemidefCStarModule

end UniformSpace.Completion

/-! ### Completing a dense `⋆`-subalgebra as a right Hilbert module -/

namespace NonUnitalStarSubalgebra

open TauCeti

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- With its subtype norm and right multiplication over `Sᵐᵒᵖ`, any nonunital `⋆`-subalgebra `S`
of a C⋆-algebra `A` satisfies `PosSemidefCStarModuleAlong (subtype S).op S` with respect to
`S.rightModuleDenseCore.toInner`. -/
theorem posSemidefCStarModuleAlong_op (S : NonUnitalStarSubalgebra ℂ A) :
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
  have hinner : inner Aᵐᵒᵖ x x = op (star (x : A) * (x : A)) :=
    S.rightModuleDenseCore_inner x x
  rw [hinner, AddSubgroupClass.coe_norm, MulOpposite.norm_op, CStarRing.norm_star_mul_self,
    Real.sqrt_mul_self (norm_nonneg _)]

/-- Completing a dense `⋆`-subalgebra `S` of a C⋆-algebra `A` in its right-module inner product
recovers `A` as a right Hilbert `A`-module via `equivOfInner`, intertwining `extAction` with right
multiplication in `A`. -/
noncomputable def completionRightModuleEquiv (S : NonUnitalStarSubalgebra ℂ A)
    (hS : Dense (S : Set A)) :
    Completion S ≃ₗᵢ[ℂ] A :=
  letI : Inner Aᵐᵒᵖ S := S.rightModuleDenseCore.toInner
  haveI : PosSemidefCStarModuleAlong (NonUnitalStarSubalgebraClass.subtype S).op S :=
    S.posSemidefCStarModuleAlong_op
  PosSemidefCStarModuleAlong.equivOfInner
    (ι := (NonUnitalStarSubalgebraClass.subtype S).op)
    (LinearMap.ofClass (NonUnitalStarSubalgebraClass.subtype S))
    (fun x y ↦ by
      rw [CStarModule.inner_mulOpposite]
      exact (S.rightModuleDenseCore_inner x y).symm)
    (S.denseRange_subtype.mpr hS)

@[simp]
theorem completionRightModuleEquiv_coe (S : NonUnitalStarSubalgebra ℂ A)
    (hS : Dense (S : Set A)) (x : S) :
    S.completionRightModuleEquiv hS (x : Completion S) = (x : A) := by
  let : Inner Aᵐᵒᵖ S := S.rightModuleDenseCore.toInner
  have : PosSemidefCStarModuleAlong (NonUnitalStarSubalgebraClass.subtype S).op S :=
    S.posSemidefCStarModuleAlong_op
  exact PosSemidefCStarModuleAlong.equivOfInner_coe
    (ι := (NonUnitalStarSubalgebraClass.subtype S).op)
    (LinearMap.ofClass (NonUnitalStarSubalgebraClass.subtype S))
    (fun u v ↦ by
      rw [CStarModule.inner_mulOpposite]
      exact (S.rightModuleDenseCore_inner u v).symm)
    (S.denseRange_subtype.mpr hS) x

/-- Under `completionRightModuleEquiv`, the extended right `A`-action on `Completion S` becomes
right multiplication in `A`. -/
theorem completionRightModuleEquiv_extAction (S : NonUnitalStarSubalgebra ℂ A)
    (hS : Dense (S : Set A)) (a : A) (z : Completion S) :
    letI : Inner Aᵐᵒᵖ S := S.rightModuleDenseCore.toInner
    haveI : PosSemidefCStarModuleAlong (NonUnitalStarSubalgebraClass.subtype S).op S :=
      S.posSemidefCStarModuleAlong_op
    S.completionRightModuleEquiv hS
      (PosSemidefCStarModuleAlong.extAction S (S.denseRange_subtype_op.mpr hS) (op a) z) =
      S.completionRightModuleEquiv hS z * a := by
  let : Inner Aᵐᵒᵖ S := S.rightModuleDenseCore.toInner
  have : PosSemidefCStarModuleAlong (NonUnitalStarSubalgebraClass.subtype S).op S :=
    S.posSemidefCStarModuleAlong_op
  exact PosSemidefCStarModuleAlong.equivOfInner_extAction
    (ι := (NonUnitalStarSubalgebraClass.subtype S).op)
    (S.denseRange_subtype_op.mpr hS)
    (LinearMap.ofClass (NonUnitalStarSubalgebraClass.subtype S))
    (fun u v ↦ by
      rw [CStarModule.inner_mulOpposite]
      exact (S.rightModuleDenseCore_inner u v).symm)
    (S.denseRange_subtype.mpr hS) (op a) z

end NonUnitalStarSubalgebra

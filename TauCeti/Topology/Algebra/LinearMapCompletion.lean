/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.StarAlgHom
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Topology.Algebra.LinearMapCompletion
public import Mathlib.Topology.Algebra.Module.Equiv.Basic
public import TauCeti.Topology.Algebra.UniformRing

/-!
# Completions of continuous semilinear maps, homomorphisms, and equivalences

A continuous semilinear map between uniform additive groups extends to completions (`completion`
and `fromCompletion`), preserving equivariance for any auxiliary uniformly continuous scalar
actions (`ContinuousLinearMap.completion_smul` and `ContinuousLinearMap.fromCompletion_smul`),
and reflecting it (`completion_smul_iff`, `fromCompletion_smul_iff`). `fromCompletion` is
characterized by `ContinuousLinearMap.comp_toComplL_eq_iff`.
Subtraction of continuous semilinear maps between uniform modules commutes with extension to the
separated completions (`ContinuousLinearMap.completion_sub`). Extending a compact operator into a
complete Hausdorff space to the completion of its domain preserves compactness
(`IsCompactOperator.fromCompletion`). Bundling continuous nonunital algebra and `⋆`-algebra
homomorphisms into complete separated targets yields `NonUnitalAlgHom.fromCompletion` and
`NonUnitalStarAlgHom.fromCompletion`.

A continuous semilinear equivalence of uniform additive groups extends to their separated
completions (`ContinuousLinearEquiv.completion`) by completing its forward and inverse continuous
semilinear maps using Mathlib's `ContinuousLinearMap.completion`. No separation or completeness
assumption on the original spaces is needed.

Multiplicative (and star-preserving) `R`-continuous linear maps bundle directly as continuous
nonunital (`⋆`-)algebra homomorphisms via `ContinuousLinearMap.toNonUnitalAlgHomOfMul` and
`ContinuousLinearMap.toNonUnitalStarAlgHomOfMulStar`.
-/

public section

open UniformSpace

namespace ContinuousLinearMap

section Sub

variable {R S E F : Type*} [Ring R] [Ring S]
  [AddCommGroup E] [UniformSpace E] [IsUniformAddGroup E]
  [AddCommGroup F] [UniformSpace F] [IsUniformAddGroup F]
  [Module R E] [UniformContinuousConstSMul R E]
  [Module S F] [UniformContinuousConstSMul S F]
  {σ : R →+* S}

/-- Completing a difference of continuous semilinear maps is the difference of their
completions. -/
@[simp]
theorem completion_sub (f g : E →SL[σ] F) : (f - g).completion = f.completion - g.completion := by
  ext x
  induction x using Completion.induction_on with
  | hp => exact isClosed_eq (f - g).completion.continuous (f.completion - g.completion).continuous
  | ih x => simp [← Completion.coe_sub]

end Sub

section SMul

variable {R S A B α β : Type*} [UniformSpace α] [AddCommGroup α] [IsUniformAddGroup α]
  [Semiring S] [Module S α] [UniformContinuousConstSMul S α]
  [Semiring R] [UniformSpace β] [AddCommGroup β] [IsUniformAddGroup β]
  [Module R β] [UniformContinuousConstSMul R β] {σ : S →+* R}

/-- Extending a continuous semilinear map to completions preserves equivariance between auxiliary
uniformly continuous scalar actions. -/
theorem completion_smul [SMul A α] [UniformContinuousConstSMul A α]
    [SMul B β] [UniformContinuousConstSMul B β]
    (f : α →SL[σ] β) {a : A} {b : B} (hf : ∀ x : α, f (a • x) = b • f x) (z : Completion α) :
    f.completion (a • z) = b • f.completion z :=
  Completion.induction_on z
    (isClosed_eq (f.completion.continuous.comp (continuous_const_smul a))
      ((continuous_const_smul b).comp f.completion.continuous))
    fun x ↦ by rw [← Completion.coe_smul, completion_apply_coe, hf, Completion.coe_smul,
      completion_apply_coe]

/-- Extending a continuous semilinear map into a complete Hausdorff group from the completion of its
domain preserves equivariance between auxiliary scalar actions. -/
theorem fromCompletion_smul [T0Space β] [CompleteSpace β]
    [SMul A α] [UniformContinuousConstSMul A α] [SMul B β] [ContinuousConstSMul B β]
    (f : α →SL[σ] β) {a : A} {b : B} (hf : ∀ x : α, f (a • x) = b • f x) (z : Completion α) :
    f.fromCompletion (a • z) = b • f.fromCompletion z :=
  Completion.induction_on z
    (isClosed_eq (f.fromCompletion.continuous.comp (continuous_const_smul a))
      ((continuous_const_smul b).comp f.fromCompletion.continuous))
    fun x ↦ by rw [← Completion.coe_smul, fromCompletion_apply_coe, hf, fromCompletion_apply_coe]

/-- For a separated codomain `β`, `f.completion` intertwines an `A`-action with a `B`-action along
`ψ : A → B` if and only if `f` does. -/
theorem completion_smul_iff [T0Space β] [SMul A α] [UniformContinuousConstSMul A α]
    [SMul B β] [UniformContinuousConstSMul B β] (ψ : A → B) (f : α →SL[σ] β) :
    (∀ (a : A) (z : Completion α), f.completion (a • z) = ψ a • f.completion z) ↔
      ∀ (a : A) (x : α), f (a • x) = ψ a • f x :=
  ⟨fun h a x ↦ Completion.coe_injective β <| by
      rw [Completion.coe_smul, ← completion_apply_coe, ← completion_apply_coe, ← h,
        Completion.coe_smul],
    fun h a ↦ f.completion_smul (h a)⟩

/-- `f.fromCompletion` intertwines an `A`-action with a `B`-action along `ψ : A → B` if and only if
`f` does. -/
theorem fromCompletion_smul_iff [T0Space β] [CompleteSpace β]
    [SMul A α] [UniformContinuousConstSMul A α] [SMul B β] [ContinuousConstSMul B β]
    (ψ : A → B) (f : α →SL[σ] β) :
    (∀ (a : A) (z : Completion α), f.fromCompletion (a • z) = ψ a • f.fromCompletion z) ↔
      ∀ (a : A) (x : α), f (a • x) = ψ a • f x :=
  ⟨fun h a x ↦ by simpa only [← Completion.coe_smul, fromCompletion_apply_coe] using h a x,
    fun h a ↦ f.fromCompletion_smul (h a)⟩

/-- Universal property of `Completion α` for continuous semilinear maps into a complete separated
module `β`: `g ∘ toComplL = f` if and only if `g = f.fromCompletion`. -/
theorem comp_toComplL_eq_iff [T0Space β] [CompleteSpace β]
    (f : α →SL[σ] β) (g : Completion α →SL[σ] β) :
    g.comp (Completion.toComplL (S := S)) = f ↔ g = f.fromCompletion :=
  ⟨fun h ↦ (f.fromCompletion_unique g fun x ↦ (DFunLike.congr_fun h x).symm).symm,
    fun h ↦ by ext x; simp [h]⟩

end SMul

section AlgHomExtension

variable {R A B : Type*} [Semiring R]
  [TopologicalSpace A] [NonUnitalNonAssocSemiring A] [Module R A]
  [TopologicalSpace B] [NonUnitalNonAssocSemiring B] [Module R B]

/-- Bundle a multiplicative continuous linear map `f : A →L[R] B` as a nonunital `R`-algebra
homomorphism. -/
def toNonUnitalAlgHomOfMul (f : A →L[R] B) (hf_mul : ∀ x y : A, f (x * y) = f x * f y) :
    A →ₙₐ[R] B where
  toFun := f
  map_zero' := map_zero _
  map_add' := map_add _
  map_smul' := map_smul _
  map_mul' := hf_mul

@[simp]
theorem toNonUnitalAlgHomOfMul_apply (f : A →L[R] B)
    (hf_mul : ∀ x y : A, f (x * y) = f x * f y) (x : A) :
    f.toNonUnitalAlgHomOfMul hf_mul x = f x :=
  (rfl)

theorem coe_toNonUnitalAlgHomOfMul (f : A →L[R] B)
    (hf_mul : ∀ x y : A, f (x * y) = f x * f y) :
    ⇑(f.toNonUnitalAlgHomOfMul hf_mul) = f :=
  (rfl)

@[fun_prop]
theorem continuous_toNonUnitalAlgHomOfMul (f : A →L[R] B)
    (hf_mul : ∀ x y : A, f (x * y) = f x * f y) :
    Continuous (f.toNonUnitalAlgHomOfMul hf_mul) :=
  f.continuous

end AlgHomExtension

section StarAlgHomExtension

variable {R A B : Type*} [Semiring R]
  [TopologicalSpace A] [NonUnitalNonAssocSemiring A] [Module R A] [Star A]
  [TopologicalSpace B] [NonUnitalNonAssocSemiring B] [Module R B] [Star B]

/-- Bundle a multiplicative star-preserving continuous linear map `f : A →L[R] B` as a nonunital
`⋆`-algebra homomorphism. -/
def toNonUnitalStarAlgHomOfMulStar (f : A →L[R] B)
    (hf_mul : ∀ x y : A, f (x * y) = f x * f y) (hf_star : ∀ x : A, f (star x) = star (f x)) :
    A →⋆ₙₐ[R] B where
  __ := f.toNonUnitalAlgHomOfMul hf_mul
  map_star' := hf_star

/-- The underlying nonunital algebra homomorphism of `f.toNonUnitalStarAlgHomOfMulStar` is
`f.toNonUnitalAlgHomOfMul`. -/
@[simp]
theorem toNonUnitalAlgHom_toNonUnitalStarAlgHomOfMulStar (f : A →L[R] B)
    (hf_mul : ∀ x y : A, f (x * y) = f x * f y) (hf_star : ∀ x : A, f (star x) = star (f x)) :
    (f.toNonUnitalStarAlgHomOfMulStar hf_mul hf_star).toNonUnitalAlgHom =
      f.toNonUnitalAlgHomOfMul hf_mul :=
  (rfl)

@[simp]
theorem toNonUnitalStarAlgHomOfMulStar_apply (f : A →L[R] B)
    (hf_mul : ∀ x y : A, f (x * y) = f x * f y) (hf_star : ∀ x : A, f (star x) = star (f x))
    (x : A) :
    f.toNonUnitalStarAlgHomOfMulStar hf_mul hf_star x = f x :=
  (rfl)

theorem coe_toNonUnitalStarAlgHomOfMulStar (f : A →L[R] B)
    (hf_mul : ∀ x y : A, f (x * y) = f x * f y) (hf_star : ∀ x : A, f (star x) = star (f x)) :
    ⇑(f.toNonUnitalStarAlgHomOfMulStar hf_mul hf_star) = f :=
  (rfl)

@[fun_prop]
theorem continuous_toNonUnitalStarAlgHomOfMulStar (f : A →L[R] B)
    (hf_mul : ∀ x y : A, f (x * y) = f x * f y) (hf_star : ∀ x : A, f (star x) = star (f x)) :
    Continuous (f.toNonUnitalStarAlgHomOfMulStar hf_mul hf_star) :=
  f.continuous

end StarAlgHomExtension

end ContinuousLinearMap

namespace IsCompactOperator

variable {R S α β : Type*} [Semiring R] [Semiring S] {σ : R →+* S}
  [UniformSpace α] [AddCommGroup α] [IsUniformAddGroup α] [Module R α]
  [UniformContinuousConstSMul R α]
  [UniformSpace β] [AddCommGroup β] [IsUniformAddGroup β] [Module S β]
  [UniformContinuousConstSMul S β] [T0Space β] [CompleteSpace β]

/-- Extending a compact operator into a complete Hausdorff space to the completion of its domain
gives a compact operator. -/
theorem fromCompletion {f : α →SL[σ] β} (hf : IsCompactOperator f) :
    IsCompactOperator f.fromCompletion := by
  obtain ⟨K, hK, hKf⟩ := hf
  refine ⟨K, hK, ?_⟩
  have hU := Completion.isDenseInducing_coe.closure_image_mem_nhds hKf
  rw [Completion.coe_zero] at hU
  refine Filter.mem_of_superset hU
    (closure_minimal ?_ (hK.isClosed.preimage f.fromCompletion.continuous))
  rintro _ ⟨x, hx, rfl⟩
  simpa [ContinuousLinearMap.fromCompletion_apply_coe] using hx

end IsCompactOperator

namespace ContinuousLinearEquiv

variable {R S E F : Type*} [Semiring R] [Semiring S]
  [AddCommGroup E] [UniformSpace E] [IsUniformAddGroup E]
  [AddCommGroup F] [UniformSpace F] [IsUniformAddGroup F]
  [Module R E] [UniformContinuousConstSMul R E]
  [Module S F] [UniformContinuousConstSMul S F]
  {σ : R →+* S} {τ : S →+* R} [RingHomInvPair σ τ] [RingHomInvPair τ σ]

/-- Extend a continuous semilinear equivalence to the separated completions. -/
noncomputable def completion (e : E ≃SL[σ] F) : Completion E ≃SL[σ] Completion F := by
  let f := e.toContinuousLinearMap.completion
  let g := e.symm.toContinuousLinearMap.completion
  refine ContinuousLinearEquiv.ofContinuousLinearMap f g ?_ ?_
  · exact ContinuousLinearMap.ext (congr_fun (Completion.ext (f.continuous.comp g.continuous)
      continuous_id (fun x => by simp [f, g])))
  · exact ContinuousLinearMap.ext (congr_fun (Completion.ext (g.continuous.comp f.continuous)
      continuous_id (fun x => by simp [f, g])))

/-- On the original space, the completed equivalence agrees with the original equivalence. -/
@[simp]
theorem completion_apply_coe (e : E ≃SL[σ] F) (x : E) : e.completion x = e x :=
  e.toContinuousLinearMap.completion_apply_coe x

/-- Completing an equivalence commutes with taking its inverse. -/
@[simp]
theorem completion_symm (e : E ≃SL[σ] F) : e.completion.symm = e.symm.completion := by
  rfl

end ContinuousLinearEquiv

namespace NonUnitalAlgHom

section FromCompletion

variable {R S E F : Type*} [Monoid R] [Monoid S] {φ : R →* S}
  [NonUnitalNonAssocRing E] [UniformSpace E] [IsUniformAddGroup E] [IsTopologicalRing E]
  [DistribMulAction R E] [UniformContinuousConstSMul R E]
  [NonUnitalNonAssocRing F] [UniformSpace F] [IsUniformAddGroup F] [ContinuousMul F]
  [DistribMulAction S F] [ContinuousConstSMul S F] [T0Space F] [CompleteSpace F]

/-- Extend a continuous semilinear nonunital algebra homomorphism `f : E →ₛₙₐ[φ] F` into a
complete separated target to the completion `UniformSpace.Completion E →ₛₙₐ[φ] F`. -/
noncomputable def fromCompletion (f : E →ₛₙₐ[φ] F) (hf : Continuous f) :
    Completion E →ₛₙₐ[φ] F where
  __ := f.toAddMonoidHom.extension hf
  map_smul' c x := Completion.induction_on x
    (isClosed_eq ((AddMonoidHom.continuous_extension f.toAddMonoidHom hf).comp
        (continuous_const_smul c))
      ((continuous_const_smul (φ c)).comp
        (AddMonoidHom.continuous_extension f.toAddMonoidHom hf)))
    fun a ↦ by
      simp only [AddMonoidHom.toFun_eq_coe, ← Completion.coe_smul,
        AddMonoidHom.extension_coe f.toAddMonoidHom hf]
      exact map_smulₛₗ f c a
  map_mul' x y := Completion.extension_mul
    (uniformContinuous_addMonoidHom_of_continuous (f := f.toAddMonoidHom) hf) (map_mul f) x y

/-- As a function, `f.fromCompletion hf` is `UniformSpace.Completion.extension f`. -/
theorem coe_fromCompletion (f : E →ₛₙₐ[φ] F) (hf : Continuous f) :
    ⇑(f.fromCompletion hf) = Completion.extension f :=
  (rfl)

/-- On `E`, the extension of `f` to the completion agrees with `f`. -/
@[simp]
theorem fromCompletion_apply_coe (f : E →ₛₙₐ[φ] F) (hf : Continuous f) (x : E) :
    f.fromCompletion hf x = f x :=
  f.toAddMonoidHom.extension_coe hf x

/-- Extending a continuous semilinear nonunital algebra homomorphism to the completion yields a
continuous homomorphism. -/
@[fun_prop, continuity]
theorem continuous_fromCompletion (f : E →ₛₙₐ[φ] F) (hf : Continuous f) :
    Continuous (f.fromCompletion hf) :=
  AddMonoidHom.continuous_extension (f := f.toAddMonoidHom) hf

/-- Any continuous semilinear nonunital algebra homomorphism out of `Completion E` agreeing with `f`
on `E` equals `f.fromCompletion hf`. -/
theorem fromCompletion_unique (f : E →ₛₙₐ[φ] F) (hf : Continuous f)
    (g : Completion E →ₛₙₐ[φ] F) (hg : Continuous g) (h : ∀ x : E, f x = g x) :
    f.fromCompletion hf = g :=
  DFunLike.coe_injective <| (coe_fromCompletion f hf).trans <|
    Completion.extension_unique
      (uniformContinuous_addMonoidHom_of_continuous (f := f.toAddMonoidHom) hf)
      (uniformContinuous_addMonoidHom_of_continuous (f := g.toAddMonoidHom) hg) h

end FromCompletion

end NonUnitalAlgHom

namespace NonUnitalStarAlgHom

section FromCompletion

variable {R E F : Type*} [Monoid R]
  [NonUnitalNonAssocRing E] [UniformSpace E] [IsUniformAddGroup E] [IsTopologicalRing E]
  [StarAddMonoid E] [ContinuousStar E] [DistribMulAction R E] [UniformContinuousConstSMul R E]
  [NonUnitalNonAssocRing F] [UniformSpace F] [IsUniformAddGroup F] [ContinuousMul F]
  [Star F] [ContinuousStar F] [DistribMulAction R F] [ContinuousConstSMul R F]
  [T0Space F] [CompleteSpace F]

/-- Extend a continuous nonunital `⋆`-algebra homomorphism `f : E →⋆ₙₐ[R] F` into a complete
separated target to the completion `UniformSpace.Completion E →⋆ₙₐ[R] F`. -/
noncomputable def fromCompletion (f : E →⋆ₙₐ[R] F) (hf : Continuous f) :
    Completion E →⋆ₙₐ[R] F where
  __ := f.toNonUnitalAlgHom.fromCompletion hf
  map_star' x :=
    Completion.extension_star TauCeti.uniformContinuous_star
      (uniformContinuous_addMonoidHom_of_continuous (f := f.toAddMonoidHom) hf) (map_star f) x

/-- The underlying nonunital algebra homomorphism of `f.fromCompletion hf` is the completion
extension of `f.toNonUnitalAlgHom`. -/
@[simp]
theorem toNonUnitalAlgHom_fromCompletion (f : E →⋆ₙₐ[R] F) (hf : Continuous f) :
    (f.fromCompletion hf).toNonUnitalAlgHom = f.toNonUnitalAlgHom.fromCompletion hf :=
  (rfl)

/-- As a function, `f.fromCompletion hf` is `UniformSpace.Completion.extension f`. -/
theorem coe_fromCompletion (f : E →⋆ₙₐ[R] F) (hf : Continuous f) :
    ⇑(f.fromCompletion hf) = Completion.extension f :=
  f.toNonUnitalAlgHom.coe_fromCompletion hf

/-- On `E`, the extension of `f` to the completion agrees with `f`. -/
@[simp]
theorem fromCompletion_apply_coe (f : E →⋆ₙₐ[R] F) (hf : Continuous f) (x : E) :
    f.fromCompletion hf x = f x :=
  f.toNonUnitalAlgHom.fromCompletion_apply_coe hf x

/-- Extending a continuous nonunital `⋆`-algebra homomorphism to the completion yields a continuous
homomorphism. -/
@[fun_prop, continuity]
theorem continuous_fromCompletion (f : E →⋆ₙₐ[R] F) (hf : Continuous f) :
    Continuous (f.fromCompletion hf) :=
  f.toNonUnitalAlgHom.continuous_fromCompletion hf

/-- Any continuous nonunital `⋆`-algebra homomorphism out of `Completion E` agreeing with `f` on
`E` equals `f.fromCompletion hf`. -/
theorem fromCompletion_unique (f : E →⋆ₙₐ[R] F) (hf : Continuous f)
    (g : Completion E →⋆ₙₐ[R] F) (hg : Continuous g) (h : ∀ x : E, f x = g x) :
    f.fromCompletion hf = g :=
  DFunLike.coe_injective <| congr_arg (DFunLike.coe : (Completion E →ₙₐ[R] F) → _) <|
    (f.toNonUnitalAlgHom_fromCompletion hf).trans <|
      f.toNonUnitalAlgHom.fromCompletion_unique hf g.toNonUnitalAlgHom hg h

end FromCompletion

end NonUnitalStarAlgHom

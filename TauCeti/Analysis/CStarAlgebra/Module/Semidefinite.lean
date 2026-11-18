/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.InnerProductSpace.Completion
public import Mathlib.Analysis.Normed.Group.NullSubmodule
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
public import TauCeti.Algebra.Star.Opposite

/-!
# Positive semidefinite C⋆-modules and their separation quotients

We develop positive semidefinite C⋆-algebra-valued inner-product modules prior to separation and
completion at two levels:

* `TauCeti.SemiCStarModuleAlong φ E`: complex module `E` with an `A₀`-action and an `A`-valued
  positive semidefinite inner product and seminorm along `φ : A₀ →⋆ₙₐ[ℂ] A`.
* `TauCeti.SemiCStarModule A E`: the case `φ = NonUnitalStarAlgHom.id ℂ A`, omitting only
  definiteness `inner x x = 0 ↔ x = 0` from `CStarModule A E`. Every `CStarModule` is a
  `SemiCStarModule`, so shared lemmas (polarization, right-module inner-product/Cauchy–Schwarz
  identities, and action norm bounds) live here rather than duplicating them in `CStarModule`.

Over a C⋆-algebra `A`, `A₀` acts `‖φ a₀‖`-Lipschitzly (`dist_smul_le`, without assuming
`DistribSMul` or density). When `φ` has dense range, density transfers
`0 ≤ ⟪a₀ • x - y, a₀ • x - y⟫_A` from `A₀` to `A`, yielding C⋆-valued Cauchy–Schwarz without
definiteness (`inner_mul_inner_swap_le`), `SeminormedSpace.Core ℂ E`, and `continuous_inner`. For
`φ = id` this yields `instIsBoundedSMul` and the definite `SeparationQuotient.instCStarModule`.
Without density or C⋆-structure, any plain inner-product-preserving map into a definite
`CStarModule A F` is `ℂ`-linear, intertwines `A₀` along `φ`, yields `linearIsometryOfInner`, and
factors uniquely through `SeparationQuotient E` (`liftInnerₗᵢ`).

## Main declarations

* `TauCeti.SemiCStarModuleAlong`, `TauCeti.SemiCStarModule`: positive semidefinite C⋆-modules.
* `NonUnitalStarSubalgebra.instSemiCStarModuleAlongOp`: `S ⊆ A` as a right pre-Hilbert `S`-module.
* `inner_mul_inner_swap_le`, `seminormedSpaceCore` (in both `SemiCStarModuleAlong` and
  `SemiCStarModule`): C⋆-valued Cauchy–Schwarz without definiteness and induced seminormed core.
* `TauCeti.SemiCStarModule.instIsBoundedSMul`, `SeparationQuotient.instCStarModule`.
* `linearIsometryOfInner`, `liftInnerₗᵢ` (in both `SemiCStarModuleAlong` and `SemiCStarModule`).

## References

* E. Christopher Lance, *Hilbert C⋆-Modules: A Toolkit for Operator Algebraists*, Chapter 1.
* Iain Raeburn and Dana P. Williams, *Morita Equivalence and Continuous-Trace C⋆-Algebras*, Ch. 2.
* `Mathlib.Analysis.CStarAlgebra.Module.Defs` (`CStarModule`), adapted without definiteness.
-/

public section

open MulOpposite Filter Topology Complex

namespace TauCeti

/-! ### Classes and basic constructors -/

/-- A positive semidefinite module `E` over a nonunital `⋆`-algebra `A₀` whose inner product and
seminorm take values in `A` along `φ : A₀ →⋆ₙₐ[ℂ] A`: `⟪x, a₀ • y⟫_A = φ a₀ * ⟪x, y⟫_A`,
`0 ≤ ⟪x, x⟫_A`, and `‖x‖ = √‖⟪x, x⟫_A‖`. -/
class SemiCStarModuleAlong {A₀ A : Type*} [NonUnitalSemiring A₀] [StarRing A₀] [Module ℂ A₀]
    [NonUnitalSemiring A] [StarRing A] [Module ℂ A] [PartialOrder A] [Norm A]
    (φ : A₀ →⋆ₙₐ[ℂ] A) (E : Type*) [AddCommGroup E] [Module ℂ E] [SMul A₀ E] [Norm E]
    [Inner A E] : Prop where
  inner_add_right {x y z : E} : inner A x (y + z) = inner A x y + inner A x z
  inner_self_nonneg {x : E} : 0 ≤ inner A x x
  inner_op_smul_right {a₀ : A₀} {x y : E} : inner A x (a₀ • y) = φ a₀ * inner A x y
  inner_smul_right_complex {z : ℂ} {x y : E} : inner A x (z • y) = z • inner A x y
  star_inner (x y : E) : star (inner A x y) = inner A y x
  norm_eq_sqrt_norm_inner_self (x : E) : ‖x‖ = √‖inner A x x‖

/-- A positive semidefinite C⋆-module over `A`: a complex module `E` with an `A`-action, an
`A`-valued positive semidefinite inner product, and seminorm `‖x‖ = √‖⟪x, x⟫_A‖`. Unlike
`CStarModule A E`, vectors of zero seminorm need not vanish. -/
class SemiCStarModule (A E : Type*) [NonUnitalSemiring A] [StarRing A] [Module ℂ A]
    [AddCommGroup E] [Module ℂ E] [PartialOrder A] [SMul A E] [Norm A] [Norm E]
    extends Inner A E where
  inner_add_right {x y z : E} : inner x (y + z) = inner x y + inner x z
  inner_self_nonneg {x : E} : 0 ≤ inner x x
  inner_op_smul_right {a : A} {x y : E} : inner x (a • y) = a * inner x y
  inner_smul_right_complex {z : ℂ} {x y : E} : inner x (z • y) = z • inner x y
  star_inner (x y : E) : star (inner x y) = inner y x
  norm_eq_sqrt_norm_inner_self (x : E) : ‖x‖ = √‖inner x x‖

attribute [simp] SemiCStarModule.inner_add_right SemiCStarModule.star_inner
  SemiCStarModule.inner_op_smul_right SemiCStarModule.inner_smul_right_complex

/-- Every definite `CStarModule` is a `SemiCStarModule`. -/
instance {A E : Type*} [NonUnitalSemiring A] [StarRing A] [Module ℂ A]
    [AddCommGroup E] [Module ℂ E] [PartialOrder A] [SMul A E] [Norm A] [Norm E]
    [CStarModule A E] : SemiCStarModule A E where
  toInner := inferInstance
  inner_add_right := CStarModule.inner_add_right
  inner_self_nonneg := CStarModule.inner_self_nonneg
  inner_op_smul_right := CStarModule.inner_op_smul_right
  inner_smul_right_complex := CStarModule.inner_smul_right_complex
  star_inner := CStarModule.star_inner
  norm_eq_sqrt_norm_inner_self := CStarModule.norm_eq_sqrt_norm_inner_self

/-- A `SemiCStarModule A E` is a `SemiCStarModuleAlong` the identity homomorphism of `A`. -/
instance {A E : Type*} [NonUnitalSemiring A] [StarRing A] [Module ℂ A]
    [AddCommGroup E] [Module ℂ E] [PartialOrder A] [SMul A E] [Norm A] [Norm E]
    [SemiCStarModule A E] : SemiCStarModuleAlong (NonUnitalStarAlgHom.id ℂ A) E where
  inner_add_right := SemiCStarModule.inner_add_right
  inner_self_nonneg := SemiCStarModule.inner_self_nonneg
  inner_op_smul_right := SemiCStarModule.inner_op_smul_right
  inner_smul_right_complex := SemiCStarModule.inner_smul_right_complex
  star_inner := SemiCStarModule.star_inner
  norm_eq_sqrt_norm_inner_self := SemiCStarModule.norm_eq_sqrt_norm_inner_self

/-- Construct `SemiCStarModuleAlong φ E` from an `A₀`-valued sesquilinear form whose diagonal
images `φ (inner A₀ x x)` are nonnegative in `A`. -/
theorem SemiCStarModuleAlong.ofMapInner {A₀ A E : Type*}
    [NonUnitalSemiring A₀] [StarRing A₀] [Module ℂ A₀]
    [NonUnitalSemiring A] [StarRing A] [Module ℂ A] [PartialOrder A] [Norm A]
    (φ : A₀ →⋆ₙₐ[ℂ] A) [AddCommGroup E] [Module ℂ E] [SMul A₀ E] [Norm E]
    [Inner A₀ E] [Inner A E]
    (hmap : ∀ x y : E, inner A x y = φ (inner A₀ x y))
    (hadd : ∀ x y z : E, inner A₀ x (y + z) = inner A₀ x y + inner A₀ x z)
    (hnonneg : ∀ x : E, 0 ≤ φ (inner A₀ x x))
    (hsmul : ∀ (a₀ : A₀) (x y : E), inner A₀ x (a₀ • y) = a₀ * inner A₀ x y)
    (hcpx : ∀ (z : ℂ) (x y : E), inner A₀ x (z • y) = z • inner A₀ x y)
    (hstar : ∀ x y : E, star (inner A₀ x y) = inner A₀ y x)
    (hnorm : ∀ x : E, ‖x‖ = √‖φ (inner A₀ x x)‖) : SemiCStarModuleAlong φ E where
  inner_add_right := by simp [hmap, hadd]
  inner_self_nonneg {x} := by rw [hmap]; exact hnonneg x
  inner_op_smul_right := by simp [hmap, hsmul]
  inner_smul_right_complex := by simp [hmap, hcpx]
  star_inner x y := by rw [hmap, hmap, ← map_star, hstar]
  norm_eq_sqrt_norm_inner_self x := by rw [hmap, hnorm]

/-- Pull back a `SemiCStarModule A F` structure along an `A`-equivariant `ℂ`-linear map `f : E → F`
to a `SemiCStarModule A E` structure with `⟪x, y⟫_A = ⟪f x, f y⟫_A` and `‖x‖ = ‖f x‖`. -/
abbrev SemiCStarModule.ofLinearMap {A E F : Type*} [NonUnitalSemiring A] [StarRing A]
    [Module ℂ A] [PartialOrder A] [Norm A] [AddCommGroup E] [Module ℂ E] [SMul A E] [Norm E]
    [AddCommGroup F] [Module ℂ F] [SMul A F] [Norm F] [SemiCStarModule A F]
    (f : E →ₗ[ℂ] F) (hf_smul : ∀ (a : A) (x : E), f (a • x) = a • f x)
    (hf_norm : ∀ x : E, ‖x‖ = ‖f x‖) : SemiCStarModule A E where
  inner x y := inner A (f x) (f y)
  inner_add_right := by simp
  inner_self_nonneg := SemiCStarModule.inner_self_nonneg (A := A)
  inner_op_smul_right := by simp [hf_smul]
  inner_smul_right_complex := by simp
  star_inner x y := by simp
  norm_eq_sqrt_norm_inner_self x := by
    rw [hf_norm, SemiCStarModule.norm_eq_sqrt_norm_inner_self (A := A) (f x)]

/-- Upgrade a `SemiCStarModule A E` in which `‖x‖ = 0 → x = 0` (and `‖(0 : A)‖ = 0`) to a
definite `CStarModule A E`. -/
abbrev SemiCStarModule.toCStarModule {A E : Type*} [NonUnitalRing A] [StarRing A] [Module ℂ A]
    [PartialOrder A] [Norm A] [AddCommGroup E] [Module ℂ E] [SMul A E] [Norm E]
    [SemiCStarModule A E] (hA : ‖(0 : A)‖ = 0)
    (hsep : ∀ x : E, ‖x‖ = 0 → x = 0) : CStarModule A E where
  toInner := inferInstance
  inner_add_right := SemiCStarModule.inner_add_right
  inner_self_nonneg := SemiCStarModule.inner_self_nonneg
  inner_self {x} :=
    ⟨fun hx ↦ hsep x <| by
      rw [SemiCStarModule.norm_eq_sqrt_norm_inner_self (A := A) x, hx, hA, Real.sqrt_zero],
    fun hx ↦ by
      subst hx
      exact add_left_cancel (a := inner A (0 : E) 0) <| by
        rw [← SemiCStarModule.inner_add_right, add_zero, add_zero]⟩
  inner_op_smul_right := SemiCStarModule.inner_op_smul_right
  inner_smul_right_complex := SemiCStarModule.inner_smul_right_complex
  star_inner := SemiCStarModule.star_inner
  norm_eq_sqrt_norm_inner_self := SemiCStarModule.norm_eq_sqrt_norm_inner_self

/-- Upgrade a `SemiCStarModule A E` on a separated normed group `E` to `CStarModule A E`. -/
abbrev SemiCStarModule.toCStarModuleOfNormed {A E : Type*} [NonUnitalSeminormedRing A]
    [StarRing A] [Module ℂ A] [PartialOrder A] [NormedAddCommGroup E] [Module ℂ E] [SMul A E]
    [SemiCStarModule A E] : CStarModule A E :=
  SemiCStarModule.toCStarModule norm_zero fun _ hx ↦ norm_eq_zero.mp hx

end TauCeti

/-! ### Nonunital `⋆`-subalgebras as right modules with positivity measured in `A` -/

namespace NonUnitalStarSubalgebra

variable {A : Type*} [NonUnitalCStarAlgebra A] (S : NonUnitalStarSubalgebra ℂ A)

/-- A nonunital `⋆`-subalgebra `S` of a C⋆-algebra `A` carries the `Aᵐᵒᵖ`-valued inner product
`⟨x, y⟩_A = star x * y` of the ambient right self-module. -/
instance instInnerMulOpposite : Inner Aᵐᵒᵖ S where
  inner x y := op (star (x : A) * (y : A))

@[simp] theorem inner_mulOpposite_apply (x y : S) :
    inner Aᵐᵒᵖ x y = op (star (x : A) * (y : A)) := rfl

theorem unop_inner_mulOpposite_apply (x y : S) :
    unop (inner Aᵐᵒᵖ x y) = star (x : A) * (y : A) := rfl

variable [PartialOrder A] [StarOrderedRing A]

/-- Every nonunital `⋆`-subalgebra `S` of a C⋆-algebra `A` is a right pre-Hilbert `S`-module with
positivity and norm measured in `A` along `(NonUnitalStarSubalgebraClass.subtype S).op`. -/
instance instSemiCStarModuleAlongOp :
    TauCeti.SemiCStarModuleAlong (NonUnitalStarSubalgebraClass.subtype S).op S where
  inner_add_right := by simp [mul_add]
  inner_self_nonneg {x} := op_nonneg.mpr (star_mul_self_nonneg (x : A))
  inner_op_smul_right := unop_injective <| by simp [MulOpposite.smul_eq_mul_unop, mul_assoc]
  inner_smul_right_complex := by simp [mul_smul_comm]
  star_inner _ _ := by simp
  norm_eq_sqrt_norm_inner_self x := by
    simp only [inner_mulOpposite_apply, MulOpposite.norm_op, CStarRing.norm_star_mul_self,
      AddSubgroupClass.coe_norm]
    exact (Real.sqrt_mul_self (_root_.norm_nonneg (x : A))).symm

end NonUnitalStarSubalgebra

namespace TauCeti

/-! ### Algebraic sesquilinearity -/

namespace SemiCStarModuleAlong

variable {A₀ A E : Type*} [NonUnitalSemiring A₀] [StarRing A₀] [Module ℂ A₀]
  [NonUnitalRing A] [StarRing A] [Module ℂ A] [PartialOrder A] [Norm A]
  (φ : A₀ →⋆ₙₐ[ℂ] A) [AddCommGroup E] [Module ℂ E] [SMul A₀ E] [Norm E]
  [Inner A E] [SemiCStarModuleAlong φ E]
include φ

lemma inner_add_left (x y z : E) : inner A (x + y) z = inner A x z + inner A y z := by
  rw [← star_star (inner A (x + y) z), star_inner (φ := φ), inner_add_right (φ := φ), star_add,
    star_inner (φ := φ), star_inner (φ := φ)]
lemma inner_op_smul_left (a₀ : A₀) (x y : E) :
    inner A (a₀ • x) y = inner A x y * star (φ a₀) := by
  rw [← star_inner (φ := φ) y, inner_op_smul_right (φ := φ), star_mul, star_inner (φ := φ)]
lemma isSelfAdjoint_inner_self (x : E) : IsSelfAdjoint (inner A x x) := star_inner (φ := φ) x x
lemma inner_smul_right_real (r : ℝ) (x y : E) : inner A x (r • y) = r • inner A x y := by
  rw [← Complex.coe_smul, inner_smul_right_complex (φ := φ)]; simp
lemma inner_zero_right (x : E) : inner A x 0 = 0 :=
  add_left_cancel (a := inner A x 0) <| by rw [← inner_add_right (φ := φ), add_zero, add_zero]
lemma inner_zero_left (x : E) : inner A 0 x = 0 := by
  rw [← star_inner (φ := φ) x 0, inner_zero_right φ, star_zero]

variable [StarModule ℂ A]

lemma inner_smul_left_complex (z : ℂ) (x y : E) :
    inner A (z • x) y = star z • inner A x y := by
  rw [← star_inner (φ := φ) y, inner_smul_right_complex (φ := φ), star_smul, star_inner (φ := φ)]
lemma inner_smul_left_real (r : ℝ) (x y : E) : inner A (r • x) y = r • inner A x y := by
  rw [← Complex.coe_smul, inner_smul_left_complex φ]; simp

/-- The `A`-valued semi-inner product bundled as a `ℂ`-sesquilinear map. -/
def innerₛₗ : E →ₗ⋆[ℂ] E →ₗ[ℂ] A where
  toFun x :=
    { toFun y := inner A x y
      map_add' _ _ := inner_add_right (φ := φ)
      map_smul' _ _ := inner_smul_right_complex (φ := φ) }
  map_add' x y := by ext z; exact inner_add_left φ x y z
  map_smul' c x := by ext z; exact inner_smul_left_complex φ c x z

@[simp] lemma innerₛₗ_apply (x y : E) : innerₛₗ φ x y = inner A x y := (rfl)
lemma inner_neg_right (x y : E) : inner A x (-y) = -inner A x y := map_neg (innerₛₗ φ x) y
lemma inner_neg_left (x y : E) : inner A (-x) y = -inner A x y :=
  LinearMap.congr_fun (map_neg (innerₛₗ φ) x) y
lemma inner_sub_right (x y z : E) : inner A x (y - z) = inner A x y - inner A x z :=
  map_sub (innerₛₗ φ x) y z
lemma inner_sub_left (x y z : E) : inner A (x - y) z = inner A x z - inner A y z :=
  LinearMap.congr_fun (map_sub (innerₛₗ φ) x y) z

end SemiCStarModuleAlong

namespace SemiCStarModule

variable {A E : Type*} [NonUnitalRing A] [StarRing A] [Module ℂ A] [PartialOrder A] [Norm A]
  [AddCommGroup E] [Module ℂ E] [SMul A E] [Norm E] [SemiCStarModule A E]

@[simp] lemma inner_add_left {x y z : E} : inner A (x + y) z = inner A x z + inner A y z :=
  SemiCStarModuleAlong.inner_add_left (.id ℂ A) x y z
@[simp] lemma inner_op_smul_left {a : A} {x y : E} : inner A (a • x) y = inner A x y * star a :=
  SemiCStarModuleAlong.inner_op_smul_left (.id ℂ A) a x y
@[simp] lemma isSelfAdjoint_inner_self {x : E} : IsSelfAdjoint (inner A x x) :=
  SemiCStarModuleAlong.isSelfAdjoint_inner_self (.id ℂ A) x
@[simp] lemma inner_zero_right {x : E} : inner A x 0 = 0 :=
  SemiCStarModuleAlong.inner_zero_right (.id ℂ A) x
@[simp] lemma inner_zero_left {x : E} : inner A 0 x = 0 :=
  SemiCStarModuleAlong.inner_zero_left (.id ℂ A) x
@[simp] lemma inner_smul_right_real {r : ℝ} {x y : E} : inner A x (r • y) = r • inner A x y :=
  SemiCStarModuleAlong.inner_smul_right_real (.id ℂ A) r x y

section StarModule

variable [StarModule ℂ A]

@[simp] lemma inner_smul_left_complex {z : ℂ} {x y : E} :
    inner A (z • x) y = star z • inner A x y :=
  SemiCStarModuleAlong.inner_smul_left_complex (.id ℂ A) z x y
@[simp] lemma inner_smul_left_real {r : ℝ} {x y : E} : inner A (r • x) y = r • inner A x y :=
  SemiCStarModuleAlong.inner_smul_left_real (.id ℂ A) r x y

/-- The semi-inner product bundled as a `ℂ`-sesquilinear map. -/
def innerₛₗ : E →ₗ⋆[ℂ] E →ₗ[ℂ] A := SemiCStarModuleAlong.innerₛₗ (.id ℂ A)

@[simp] lemma innerₛₗ_apply {x y : E} : innerₛₗ x y = inner A x y := (rfl)
@[simp] lemma inner_neg_right {x y : E} : inner A x (-y) = -inner A x y :=
  SemiCStarModuleAlong.inner_neg_right (.id ℂ A) x y
@[simp] lemma inner_neg_left {x y : E} : inner A (-x) y = -inner A x y :=
  SemiCStarModuleAlong.inner_neg_left (.id ℂ A) x y
@[simp] lemma inner_sub_right {x y z : E} : inner A x (y - z) = inner A x y - inner A x z :=
  SemiCStarModuleAlong.inner_sub_right (.id ℂ A) x y z
@[simp] lemma inner_sub_left {x y z : E} : inner A (x - y) z = inner A x z - inner A y z :=
  SemiCStarModuleAlong.inner_sub_left (.id ℂ A) x y z
@[simp] lemma inner_sum_right {ι : Type*} {s : Finset ι} {x : E} {y : ι → E} :
    inner A x (∑ i ∈ s, y i) = ∑ i ∈ s, inner A x (y i) := map_sum (innerₛₗ x) y s
@[simp] lemma inner_sum_left {ι : Type*} {s : Finset ι} {x : ι → E} {y : E} :
    inner A (∑ i ∈ s, x i) y = ∑ i ∈ s, inner A (x i) y := map_sum (innerₛₗ.flip y) x s

/-- Polarization identity for positive semidefinite modules. -/
lemma inner_polarization (x y : E) :
    inner A x y = (4 : ℂ)⁻¹ • (inner A (x + y) (x + y) - inner A (x - y) (x - y) -
      I • inner A (x + I • y) (x + I • y) + I • inner A (x - I • y) (x - I • y)) := by
  simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
    inner_smul_left_complex, inner_smul_right_complex, Complex.star_def, conj_I, smul_add,
    smul_sub, smul_neg, smul_smul, neg_smul, I_mul_I]
  module

end StarModule

section Right

variable {A E : Type*} [NonUnitalSeminormedRing A] [StarRing A] [Module ℂ A] [PartialOrder A]
  [AddCommGroup E] [Module ℂ E] [SMul Aᵐᵒᵖ E] [Norm E] [SemiCStarModule Aᵐᵒᵖ E]

/-- Conjugate-linearity of the right-module inner product in the first slot:
`⟨x a, y⟩_A = a⋆ ⟨x, y⟩_A`. -/
lemma unop_inner_op_smul_left (a : A) (x y : E) :
    unop (inner Aᵐᵒᵖ (op a • x) y) = star a * unop (inner Aᵐᵒᵖ x y) := by simp

/-- Linearity of the right-module inner product in the second slot: `⟨x, y a⟩_A = ⟨x, y⟩_A a`. -/
lemma unop_inner_op_smul_right (a : A) (x y : E) :
    unop (inner Aᵐᵒᵖ x (op a • y)) = unop (inner Aᵐᵒᵖ x y) * a := by simp

end Right
end SemiCStarModule

/-! ### Action norm bounds, Cauchy–Schwarz without definiteness, and seminormed structure -/

namespace SemiCStarModuleAlong

section CStar

variable {A₀ A E : Type*} [NonUnitalSemiring A₀] [StarRing A₀] [Module ℂ A₀]
  [NonUnitalCStarAlgebra A] [PartialOrder A] (φ : A₀ →⋆ₙₐ[ℂ] A)
  [AddCommGroup E] [Module ℂ E] [SMul A₀ E] [Norm E] [Inner A E] [SemiCStarModuleAlong φ E]

include φ

lemma norm_sq_eq (x : E) : ‖x‖ ^ 2 = ‖inner A x x‖ := by
  simp [norm_eq_sqrt_norm_inner_self (φ := φ) x]
lemma norm_nonneg (x : E) : 0 ≤ ‖x‖ :=
  (norm_eq_sqrt_norm_inner_self (φ := φ) x).symm ▸ Real.sqrt_nonneg _
lemma norm_zero : ‖(0 : E)‖ = 0 := by
  simp [norm_eq_sqrt_norm_inner_self (φ := φ) (0 : E), inner_zero_right φ]

/-- A vector has seminorm zero if and only if its self-inner product vanishes. -/
theorem norm_eq_zero_iff_inner_self_eq_zero (x : E) : ‖x‖ = 0 ↔ inner A x x = 0 := by
  rw [norm_eq_sqrt_norm_inner_self (φ := φ) x, Real.sqrt_eq_zero (_root_.norm_nonneg _),
    norm_eq_zero]

/-- Any vector annihilated on the right by all inner products has seminorm zero. -/
lemma norm_eq_zero_of_forall_inner_eq_zero {z : E} (hz : ∀ w : E, inner A w z = 0) : ‖z‖ = 0 :=
  (norm_eq_zero_iff_inner_self_eq_zero φ z).mpr (hz z)

lemma norm_smul_sub_sub_eq_zero (a₀ : A₀) (x y : E) : ‖a₀ • x - a₀ • y - a₀ • (x - y)‖ = 0 :=
  norm_eq_zero_of_forall_inner_eq_zero φ fun w ↦ by
    simp [inner_sub_right φ, inner_op_smul_right (φ := φ), mul_sub]

omit [NonUnitalSemiring A₀] [StarRing A₀] [Module ℂ A₀] [SemiCStarModuleAlong φ E] φ in
lemma norm_sub_smul_sub_eq_zero {A₀ : Type*} [NonUnitalRing A₀] [StarRing A₀] [Module ℂ A₀]
    (φ : A₀ →⋆ₙₐ[ℂ] A) [SMul A₀ E] [SemiCStarModuleAlong φ E] (a₀ b₀ : A₀) (x : E) :
    ‖a₀ • x - b₀ • x - (a₀ - b₀) • x‖ = 0 :=
  norm_eq_zero_of_forall_inner_eq_zero φ fun w ↦ by
    simp [inner_sub_right φ, inner_op_smul_right (φ := φ), sub_mul]

variable [StarOrderedRing A]

/-- `⟪a₀ • x, a₀ • x⟫_A = (φ a₀ * |x|) (φ a₀ * |x|)⋆`, where `|x| = CFC.sqrt ⟪x, x⟫_A`. -/
lemma inner_smul_smul (a₀ : A₀) (x : E) :
    inner A (a₀ • x) (a₀ • x) =
      (φ a₀ * CFC.sqrt (inner A x x)) * star (φ a₀ * CFC.sqrt (inner A x x)) := by
  set s := CFC.sqrt (inner A x x)
  have hs : s * s = inner A x x := CFC.sqrt_mul_sqrt_self _ (inner_self_nonneg (φ := φ))
  have hs' : star s = s := (CFC.sqrt_nonneg _).isSelfAdjoint.star_eq
  rw [inner_op_smul_left φ, inner_op_smul_right (φ := φ), star_mul, hs', ← hs]
  noncomm_ring

/-- The seminorm of `a₀ • x` equals `‖φ a₀ * CFC.sqrt ⟪x, x⟫_A‖` in `A`. -/
theorem norm_smul (a₀ : A₀) (x : E) : ‖a₀ • x‖ = ‖φ a₀ * CFC.sqrt (inner A x x)‖ := by
  rw [norm_eq_sqrt_norm_inner_self (φ := φ) (a₀ • x), inner_smul_smul φ,
    CStarRing.norm_self_mul_star, Real.sqrt_mul_self (_root_.norm_nonneg _)]

/-- The action of `A₀` is bounded in seminorm by `‖φ a₀‖`: `‖a₀ • x‖ ≤ ‖φ a₀‖ * ‖x‖`. -/
theorem norm_smul_le (a₀ : A₀) (x : E) : ‖a₀ • x‖ ≤ ‖φ a₀‖ * ‖x‖ := by
  rw [norm_smul φ]
  refine (norm_mul_le _ _).trans_eq ?_
  rw [CFC.norm_sqrt _ (inner_self_nonneg (φ := φ)), ← norm_eq_sqrt_norm_inner_self (φ := φ) x]

/-! #### Cauchy–Schwarz when `φ` has dense range -/

variable {φ}

/-- Extending `0 ≤ ⟪a₀ • x - y, a₀ • x - y⟫_A` from the dense range of `φ` to all `a ∈ A`. -/
private lemma quadratic_nonneg_of_denseRange (hφ : DenseRange φ) (x y : E) (a : A) :
    (0 : A) ≤ ‖x‖ ^ 2 • (a * star a) - a * inner A y x - inner A x y * star a + inner A y y := by
  refine hφ.induction (fun a ⟨a₀, ha₀⟩ ↦ ?_) (isClosed_le (by fun_prop) (by fun_prop)) a
  subst ha₀
  calc (0 : A) ≤ inner A (a₀ • x - y) (a₀ • x - y) := inner_self_nonneg (φ := φ)
    _ = φ a₀ * inner A x x * star (φ a₀) - φ a₀ * inner A y x -
          inner A x y * star (φ a₀) + inner A y y := by
      simp only [inner_sub_right φ, inner_sub_left φ, inner_op_smul_right (φ := φ),
        inner_op_smul_left φ, mul_assoc]; abel
    _ ≤ ‖x‖ ^ 2 • (φ a₀ * star (φ a₀)) - φ a₀ * inner A y x -
          inner A x y * star (φ a₀) + inner A y y := by
      gcongr; rw [norm_sq_eq φ x]
      exact CStarAlgebra.star_right_conjugate_le_norm_smul (φ a₀) (inner A x x)
        (isSelfAdjoint_inner_self φ x)

/-- Vectors of seminorm zero are left-orthogonal to all vectors when `φ` has dense range. -/
theorem inner_eq_zero_of_norm_eq_zero_left (hφ : DenseRange φ) {x : E} (hx : ‖x‖ = 0) (y : E) :
    inner A x y = 0 := by
  set w := inner A x y
  by_contra hw
  have hw_pos : 0 < 2 * ‖w‖ ^ 2 := by positivity
  set t : ℝ := (‖inner A y y‖ + 1) / (2 * ‖w‖ ^ 2)
  have hle : (2 * t) • (w * star w) ≤ inner A y y := sub_nonneg.mp <| by
    have hq := quadratic_nonneg_of_denseRange hφ x y (t • w)
    simp [hx, ← star_inner (φ := φ) x y, smul_mul_assoc, mul_smul_comm, w] at hq
    exact hq.trans_eq (by dsimp only [w]; module)
  have hnorm_le := CStarAlgebra.norm_le_norm_of_le_of_nonneg hle
    (smul_nonneg (by positivity) (mul_star_self_nonneg w))
  have ht : 2 * t * ‖w‖ ^ 2 = ‖inner A y y‖ + 1 := calc
    2 * t * ‖w‖ ^ 2 = t * (2 * ‖w‖ ^ 2) := by ring
    _ = ‖inner A y y‖ + 1 := div_mul_cancel₀ _ hw_pos.ne'
  rw [_root_.norm_smul, Real.norm_of_nonneg (by positivity), CStarRing.norm_self_mul_star,
    ← sq, ht] at hnorm_le
  linarith

/-- Vectors of seminorm zero are right-orthogonal to all vectors when `φ` has dense range. -/
theorem inner_eq_zero_of_norm_eq_zero_right (hφ : DenseRange φ) (x : E) {y : E} (hy : ‖y‖ = 0) :
    inner A x y = 0 := by
  rw [← star_inner (φ := φ) y x, inner_eq_zero_of_norm_eq_zero_left hφ hy x, star_zero]

/-- C⋆-valued Cauchy–Schwarz inequality for positive semidefinite modules along dense `φ`. -/
theorem inner_mul_inner_swap_le (hφ : DenseRange φ) (x y : E) :
    inner A x y * inner A y x ≤ ‖x‖ ^ 2 • inner A y y := by
  rcases (norm_nonneg φ x).eq_or_lt with hx | hx
  · rw [inner_eq_zero_of_norm_eq_zero_left hφ hx.symm y, ← hx, zero_mul,
      zero_pow two_ne_zero, zero_smul]
  · have hquad := quadratic_nonneg_of_denseRange hφ x (‖x‖ ^ 2 • y) (inner A x y)
    simp only [inner_smul_left_real φ, inner_smul_right_real φ, star_inner (φ := φ),
      mul_smul_comm, smul_mul_assoc, sub_self, zero_sub, le_neg_add_iff_add_le, add_zero] at hquad
    exact (smul_le_smul_iff_of_pos_left (sq_pos_of_pos hx)).mp hquad

/-- Norm Cauchy–Schwarz inequality `‖⟪x, y⟫_A‖ ≤ ‖x‖ * ‖y‖` along dense `φ`. -/
theorem norm_inner_le (hφ : DenseRange φ) (x y : E) : ‖inner A x y‖ ≤ ‖x‖ * ‖y‖ := by
  refine (pow_le_pow_iff_left₀ (_root_.norm_nonneg _)
    (mul_nonneg (norm_nonneg φ x) (norm_nonneg φ y)) two_ne_zero).mp ?_
  calc ‖inner A x y‖ ^ 2 = ‖inner A x y * inner A y x‖ := by
        rw [← star_inner (φ := φ) x y, CStarRing.norm_self_mul_star, sq]
    _ ≤ ‖‖x‖ ^ 2 • inner A y y‖ := CStarAlgebra.norm_le_norm_of_le_of_nonneg
        (inner_mul_inner_swap_le hφ x y) (star_inner (φ := φ) x y ▸ mul_star_self_nonneg _)
    _ = (‖x‖ * ‖y‖) ^ 2 := by simp [_root_.norm_smul, ← norm_sq_eq φ y, mul_pow]

/-- Triangle inequality for the module seminorm `‖x‖ = √‖⟪x, x⟫_A‖`. -/
theorem norm_triangle (hφ : DenseRange φ) (x y : E) : ‖x + y‖ ≤ ‖x‖ + ‖y‖ := by
  refine (pow_le_pow_iff_left₀ (norm_nonneg φ (x + y))
    (add_nonneg (norm_nonneg φ x) (norm_nonneg φ y)) two_ne_zero).mp ?_
  calc ‖x + y‖ ^ 2 = ‖inner A x x + inner A y x + inner A x y + inner A y y‖ := by
        rw [norm_sq_eq φ (x + y), inner_add_right (φ := φ), inner_add_left φ, inner_add_left φ,
          ← add_assoc]
    _ ≤ ‖inner A x x‖ + ‖inner A y x‖ + ‖inner A x y‖ + ‖inner A y y‖ :=
        norm_add₃_le.trans (by gcongr; exact norm_add_le _ _)
    _ ≤ ‖inner A x x‖ + ‖y‖ * ‖x‖ + ‖x‖ * ‖y‖ + ‖inner A y y‖ := by
        gcongr <;> exact norm_inner_le hφ _ _
    _ = (‖x‖ + ‖y‖) ^ 2 := by rw [← norm_sq_eq φ x, ← norm_sq_eq φ y]; ring

/-- `SeminormedSpace.Core ℂ E` from `‖x‖ = √‖⟪x, x⟫_A‖`, for use with
`SeminormedAddCommGroup.ofCore` (or `ofCoreReplaceAll`). -/
lemma seminormedSpaceCore (hφ : DenseRange φ) : SeminormedSpace.Core ℂ E where
  norm_nonneg := norm_nonneg φ
  norm_smul c x := by
    rw [norm_eq_sqrt_norm_inner_self (φ := φ) (c • x), norm_eq_sqrt_norm_inner_self (φ := φ) x]
    simp [inner_smul_left_complex φ, inner_smul_right_complex (φ := φ), _root_.norm_smul,
      ← mul_assoc]
  norm_triangle := norm_triangle hφ

/-- Equip `E` with the `SeminormedAddCommGroup` induced by `‖x‖ = √‖⟪x, x⟫_A‖`. Not registered as
an instance so existing topologies or uniformities on `E` are not shadowed. -/
noncomputable abbrev seminormedAddCommGroup (hφ : DenseRange φ) : SeminormedAddCommGroup E :=
  SeminormedAddCommGroup.ofCore (seminormedSpaceCore hφ)

end CStar

/-! #### Continuity, null submodule, and uniform continuity on seminormed modules -/

section Seminormed

variable {A₀ A E : Type*} [NonUnitalSemiring A₀] [StarRing A₀] [Module ℂ A₀]
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {φ : A₀ →⋆ₙₐ[ℂ] A} [SeminormedAddCommGroup E] [SMul A₀ E] [Inner A E]

section Module

variable [Module ℂ E] [SemiCStarModuleAlong φ E]
include φ

/-- Each `a₀ : A₀` acts `‖φ a₀‖`-Lipschitzly on `E` (without assuming `DistribSMul`). -/
theorem dist_smul_le (a₀ : A₀) (x y : E) : dist (a₀ • x) (a₀ • y) ≤ ‖φ a₀‖ * dist x y := by
  rw [dist_eq_norm, dist_eq_norm, norm_eq_sqrt_norm_inner_self (φ := φ)]
  have h : inner A (a₀ • x - a₀ • y) (a₀ • x - a₀ • y) = inner A (a₀ • (x - y)) (a₀ • (x - y)) := by
    simp only [inner_sub_left φ, inner_sub_right φ, inner_op_smul_left φ,
      inner_op_smul_right (φ := φ), mul_sub, sub_mul]
  rw [h, ← norm_eq_sqrt_norm_inner_self (φ := φ)]
  exact norm_smul_le φ a₀ (x - y)

/-- Reducible `UniformContinuousConstSMul A₀ E` from `dist_smul_le`, letting `Completion` and
`SeparationQuotient` inherit the `A₀`-action without assuming `DistribSMul A₀ E`. -/
abbrev uniformContinuousConstSMul : UniformContinuousConstSMul A₀ E where
  uniformContinuous_const_smul a₀ :=
    LipschitzWith.uniformContinuous (K := ⟨‖φ a₀‖, _root_.norm_nonneg _⟩)
      (LipschitzWith.of_dist_le_mul fun x y ↦ dist_smul_le (φ := φ) a₀ x y)

end Module

section NormedSpace

variable [NormedSpace ℂ E] [SemiCStarModuleAlong φ E]
include φ

omit [StarOrderedRing A] in
/-- Membership in `nullSubmodule ℂ E` is equivalent to vanishing of the self-inner product. -/
theorem mem_nullSubmodule_iff_inner_self_eq_zero (x : E) :
    x ∈ nullSubmodule ℂ E ↔ inner A x x = 0 := by
  rw [mem_nullSubmodule_iff, norm_eq_zero_iff_inner_self_eq_zero φ]

/-- Along dense `φ`, `nullSubmodule ℂ E` consists of vectors orthogonal to all of `E`. -/
theorem mem_nullSubmodule_iff_forall_inner_eq_zero (hφ : DenseRange φ) (x : E) :
    x ∈ nullSubmodule ℂ E ↔ ∀ y : E, inner A x y = 0 :=
  ⟨fun hx y ↦ inner_eq_zero_of_norm_eq_zero_left hφ (mem_nullSubmodule_iff.mp hx) y,
    fun h ↦ (mem_nullSubmodule_iff_inner_self_eq_zero (φ := φ) x).mpr (h x)⟩

/-- `nullSubmodule ℂ E` is invariant under the action of `A₀`. -/
theorem smul_mem_nullSubmodule (a₀ : A₀) {x : E} (hx : x ∈ nullSubmodule ℂ E) :
    a₀ • x ∈ nullSubmodule ℂ E := by
  rw [mem_nullSubmodule_iff] at hx ⊢
  exact le_antisymm ((norm_smul_le φ a₀ x).trans_eq (by rw [hx, mul_zero])) (_root_.norm_nonneg _)

/-- The `A`-valued semi-inner product bundled as a continuous `ℂ`-sesquilinear map. -/
noncomputable def innerSL (hφ : DenseRange φ) : E →L⋆[ℂ] E →L[ℂ] A :=
  LinearMap.mkContinuous₂ (innerₛₗ φ) 1 fun x y ↦ by simpa [one_mul] using norm_inner_le hφ x y

@[simp] lemma innerSL_apply (hφ : DenseRange φ) (x y : E) : innerSL hφ x y = inner A x y := (rfl)

/-- Joint continuity of the `A`-valued semi-inner product when `φ` has dense range. -/
theorem continuous_inner (hφ : DenseRange φ) : Continuous (fun p : E × E ↦ inner A p.1 p.2) := by
  simp_rw [← innerSL_apply hφ]; fun_prop

/-- Inseparable pairs have equal `A`-valued inner products when `φ` has dense range. -/
theorem inner_eq_inner_of_inseparable (hφ : DenseRange φ) {x₁ x₂ y₁ y₂ : E}
    (hx : Inseparable x₁ x₂) (hy : Inseparable y₁ y₂) : inner A x₁ y₁ = inner A x₂ y₂ :=
  ((hx.prod hy).map (continuous_inner hφ)).eq

end NormedSpace
end Seminormed
end SemiCStarModuleAlong

namespace SemiCStarModule

variable {A E : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A]

private lemma denseRange_id (A : Type*) [NonUnitalCStarAlgebra A] :
    DenseRange (NonUnitalStarAlgHom.id ℂ A) := Function.surjective_id.denseRange

section Norm

variable [AddCommGroup E] [Module ℂ E] [SMul A E] [Norm E] [SemiCStarModule A E]

theorem norm_eq_zero_iff_inner_self_eq_zero (x : E) : ‖x‖ = 0 ↔ inner A x x = 0 :=
  SemiCStarModuleAlong.norm_eq_zero_iff_inner_self_eq_zero (.id ℂ A) x

section ExplicitA
include A
variable (A)

lemma norm_sq_eq (x : E) : ‖x‖ ^ 2 = ‖inner A x x‖ :=
  SemiCStarModuleAlong.norm_sq_eq (.id ℂ A) x
protected lemma norm_nonneg (x : E) : 0 ≤ ‖x‖ := SemiCStarModuleAlong.norm_nonneg (.id ℂ A) x
protected lemma norm_zero : ‖(0 : E)‖ = 0 := SemiCStarModuleAlong.norm_zero (.id ℂ A)

variable [StarOrderedRing A]

protected theorem norm_triangle (x y : E) : ‖x + y‖ ≤ ‖x‖ + ‖y‖ :=
  SemiCStarModuleAlong.norm_triangle (denseRange_id A) x y

/-- `SeminormedSpace.Core ℂ E` for a positive semidefinite `A`-module. -/
lemma seminormedSpaceCore : SeminormedSpace.Core ℂ E :=
  SemiCStarModuleAlong.seminormedSpaceCore (denseRange_id A)

/-- Equip `E` with the `SeminormedAddCommGroup` induced by `‖x‖ = √‖⟪x, x⟫_A‖`. -/
noncomputable abbrev seminormedAddCommGroup : SeminormedAddCommGroup E :=
  SeminormedAddCommGroup.ofCore (seminormedSpaceCore A)

end ExplicitA

variable [StarOrderedRing A]

/-- `⟪a • x, a • x⟫_A = (a * |x|) (a * |x|)⋆`, where `|x| = CFC.sqrt ⟪x, x⟫_A`. -/
lemma inner_smul_smul (a : A) (x : E) :
    inner A (a • x) (a • x) =
      (a * CFC.sqrt (inner A x x)) * star (a * CFC.sqrt (inner A x x)) :=
  SemiCStarModuleAlong.inner_smul_smul (.id ℂ A) a x

/-- The seminorm of `a • x` equals `‖a * CFC.sqrt ⟪x, x⟫_A‖` in `A`. -/
protected theorem norm_smul (a : A) (x : E) : ‖a • x‖ = ‖a * CFC.sqrt (inner A x x)‖ :=
  SemiCStarModuleAlong.norm_smul (.id ℂ A) a x

/-- Action of a C⋆-algebra on a positive semidefinite module is bounded: `‖a • x‖ ≤ ‖a‖ * ‖x‖`. -/
protected theorem norm_smul_le (a : A) (x : E) : ‖a • x‖ ≤ ‖a‖ * ‖x‖ :=
  SemiCStarModuleAlong.norm_smul_le (.id ℂ A) a x

/-- C⋆-algebra-valued Cauchy–Schwarz inequality for positive semidefinite `A`-modules. -/
theorem inner_mul_inner_swap_le {x y : E} : inner A x y * inner A y x ≤ ‖x‖ ^ 2 • inner A y y :=
  SemiCStarModuleAlong.inner_mul_inner_swap_le (denseRange_id A) x y

variable (E) in
/-- Norm Cauchy–Schwarz `‖⟪x, y⟫_A‖ ≤ ‖x‖ * ‖y‖` for positive semidefinite `A`-modules. -/
theorem norm_inner_le {x y : E} : ‖inner A x y‖ ≤ ‖x‖ * ‖y‖ :=
  SemiCStarModuleAlong.norm_inner_le (denseRange_id A) x y

theorem inner_eq_zero_of_norm_eq_zero_left {x : E} (hx : ‖x‖ = 0) (y : E) : inner A x y = 0 :=
  SemiCStarModuleAlong.inner_eq_zero_of_norm_eq_zero_left (denseRange_id A) hx y
theorem inner_eq_zero_of_norm_eq_zero_right (x : E) {y : E} (hy : ‖y‖ = 0) : inner A x y = 0 :=
  SemiCStarModuleAlong.inner_eq_zero_of_norm_eq_zero_right (denseRange_id A) x hy

end Norm

section Right

variable [StarOrderedRing A] [AddCommGroup E] [Module ℂ E] [SMul Aᵐᵒᵖ E] [Norm E]
  [SemiCStarModule Aᵐᵒᵖ E]

/-- Right-module Cauchy–Schwarz: `⟨x, y⟩_A⋆ ⟨x, y⟩_A ≤ ‖x‖² • ⟨y, y⟩_A`. -/
theorem star_unop_inner_mul_unop_inner_le (x y : E) :
    star (unop (inner Aᵐᵒᵖ x y)) * unop (inner Aᵐᵒᵖ x y) ≤ ‖x‖ ^ 2 • unop (inner Aᵐᵒᵖ y y) := by
  have h := unop_le_unop.mpr (inner_mul_inner_swap_le (A := Aᵐᵒᵖ) (x := x) (y := y))
  rwa [unop_mul, unop_smul, ← star_inner x y, unop_star] at h

/-- Right-module norm Cauchy–Schwarz: `‖⟨x, y⟩_A‖ ≤ ‖x‖ * ‖y‖`. -/
theorem norm_unop_inner_le (x y : E) : ‖unop (inner Aᵐᵒᵖ x y)‖ ≤ ‖x‖ * ‖y‖ := by
  rw [norm_unop]; exact norm_inner_le E

/-- Right-module action norm bound: `‖op a • x‖ ≤ ‖x‖ * ‖a‖`. -/
theorem norm_op_smul_le (a : A) (x : E) : ‖op a • x‖ ≤ ‖x‖ * ‖a‖ := by
  rw [mul_comm, ← norm_op a]; exact SemiCStarModule.norm_smul_le _ x

end Right

section Seminormed

variable [StarOrderedRing A] [SeminormedAddCommGroup E] [SMul A E]

/-- The action of `A` on any seminormed `SemiCStarModule A E` is bounded, without requiring
`DistribSMul A E` or definiteness of the inner product. -/
instance instIsBoundedSMul [Module ℂ E] [SemiCStarModule A E] : IsBoundedSMul A E where
  dist_smul_pair' a x y := by
    simpa [dist_zero_right] using SemiCStarModuleAlong.dist_smul_le (φ := .id ℂ A) a x y
  dist_pair_smul' a b x := by
    rw [dist_eq_norm, dist_eq_norm, dist_zero_right,
      SemiCStarModule.norm_eq_sqrt_norm_inner_self (A := A)]
    have h : inner A (a • x - b • x) (a • x - b • x) = inner A ((a - b) • x) ((a - b) • x) := by
      simp only [inner_sub_left, inner_sub_right, inner_op_smul_left, inner_op_smul_right,
        star_sub, mul_sub, sub_mul]; abel
    rw [h, ← SemiCStarModule.norm_eq_sqrt_norm_inner_self (A := A)]
    exact SemiCStarModule.norm_smul_le (a - b) x

section NormedSpace

variable [NormedSpace ℂ E] [SemiCStarModule A E]

omit [StarOrderedRing A] in
/-- Membership in `nullSubmodule ℂ E` is equivalent to vanishing of the self-inner product. -/
theorem mem_nullSubmodule_iff_inner_self_eq_zero (x : E) :
    x ∈ nullSubmodule ℂ E ↔ inner A x x = 0 :=
  SemiCStarModuleAlong.mem_nullSubmodule_iff_inner_self_eq_zero (φ := .id ℂ A) x

/-- `nullSubmodule ℂ E` consists precisely of the vectors orthogonal to all of `E`. -/
theorem mem_nullSubmodule_iff_forall_inner_eq_zero (x : E) :
    x ∈ nullSubmodule ℂ E ↔ ∀ y : E, inner A x y = 0 :=
  SemiCStarModuleAlong.mem_nullSubmodule_iff_forall_inner_eq_zero (denseRange_id A) x

/-- `nullSubmodule ℂ E` is invariant under the action of `A`. -/
theorem smul_mem_nullSubmodule (a : A) {x : E} (hx : x ∈ nullSubmodule ℂ E) :
    a • x ∈ nullSubmodule ℂ E :=
  SemiCStarModuleAlong.smul_mem_nullSubmodule (φ := .id ℂ A) a hx

/-- The `A`-valued semi-inner product as a continuous sesquilinear map. -/
noncomputable def innerSL : E →L⋆[ℂ] E →L[ℂ] A := SemiCStarModuleAlong.innerSL (denseRange_id A)

@[simp] lemma innerSL_apply {x y : E} : innerSL x y = inner A x y := (rfl)

@[continuity, fun_prop]
lemma continuous_inner : Continuous (fun p : E × E ↦ inner A p.1 p.2) :=
  SemiCStarModuleAlong.continuous_inner (denseRange_id A)

/-- Inseparable pairs have equal `A`-valued inner products. -/
theorem inner_eq_inner_of_inseparable {x₁ x₂ y₁ y₂ : E} (hx : Inseparable x₁ x₂)
    (hy : Inseparable y₁ y₂) : inner A x₁ y₁ = inner A x₂ y₂ :=
  SemiCStarModuleAlong.inner_eq_inner_of_inseparable (denseRange_id A) hx hy

end NormedSpace
end Seminormed
end SemiCStarModule

/-! ### Automatic linearity, isometry, and separation-quotient lifts of inner-preserving maps -/

namespace SemiCStarModuleAlong

variable {A₀ A : Type*} [NonUnitalSemiring A₀] [StarRing A₀] [Module ℂ A₀]
  [NonUnitalRing A] [StarRing A] [Module ℂ A] [PartialOrder A] [Norm A] (φ : A₀ →⋆ₙₐ[ℂ] A)

section Algebraic

variable {E F : Type*} [AddCommGroup E] [Module ℂ E] [SMul A₀ E] [Norm E] [Inner A E]
  [SemiCStarModuleAlong φ E] [AddCommGroup F] [Module ℂ F] [SMul A F] [Norm F] [CStarModule A F]
  {f : E → F} (hf : ∀ x y : E, inner A (f x) (f y) = inner A x y)
include φ hf

/-- An inner-product-preserving map into a definite `CStarModule A F` preserves `0`. -/
theorem map_zero_of_inner : f 0 = 0 :=
  CStarModule.inner_self (A := A).mp <| by rw [hf, inner_zero_right φ]

/-- An inner-product-preserving map into a definite `CStarModule A F` preserves norms. -/
theorem norm_map_of_inner (x : E) : ‖f x‖ = ‖x‖ := by
  rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := A) (f x), hf,
    SemiCStarModuleAlong.norm_eq_sqrt_norm_inner_self (φ := φ) x]

variable [StarModule ℂ A]

/-- An inner-product-preserving map into a definite `CStarModule A F` is additive. -/
theorem map_add_of_inner (x y : E) : f (x + y) = f x + f y := by
  rw [← sub_eq_zero, ← CStarModule.inner_self (A := A)]
  simp only [CStarModule.inner_sub_left, CStarModule.inner_sub_right, CStarModule.inner_add_left,
    CStarModule.inner_add_right, hf, inner_add_left φ, inner_add_right (φ := φ)]
  abel

/-- An inner-product-preserving map into a definite `CStarModule A F` is `ℂ`-homogeneous. -/
theorem map_smul_complex_of_inner (c : ℂ) (x : E) : f (c • x) = c • f x := by
  rw [← sub_eq_zero, ← CStarModule.inner_self (A := A)]
  simp [CStarModule.inner_sub_left, CStarModule.inner_sub_right,
    CStarModule.inner_smul_left_complex, CStarModule.inner_smul_right_complex, hf,
    inner_smul_left_complex φ, inner_smul_right_complex (φ := φ), smul_smul]

/-- An inner-product-preserving map into a definite `CStarModule A F` intertwines `A₀` along `φ`. -/
theorem map_smul_along_of_inner (a₀ : A₀) (x : E) : f (a₀ • x) = φ a₀ • f x := by
  rw [← sub_eq_zero, ← CStarModule.inner_self (A := A)]
  simp [CStarModule.inner_sub_left, CStarModule.inner_sub_right,
    CStarModule.inner_op_smul_left, CStarModule.inner_op_smul_right, hf,
    inner_op_smul_left φ, inner_op_smul_right (φ := φ), mul_assoc]

end Algebraic

variable [StarModule ℂ A] {E F : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E]
  [SMul A₀ E] [Inner A E] [SemiCStarModuleAlong φ E]

section Seminormed

variable [SeminormedAddCommGroup F] [NormedSpace ℂ F] [SMul A F] [CStarModule A F]
  (f : E → F) (hf : ∀ x y : E, inner A (f x) (f y) = inner A x y)
include φ

/-- Bundle an inner-product-preserving map into a definite `CStarModule` as a `LinearIsometry`. -/
def linearIsometryOfInner : E →ₗᵢ[ℂ] F where
  toFun := f
  map_add' := map_add_of_inner φ hf
  map_smul' := map_smul_complex_of_inner φ hf
  norm_map' := norm_map_of_inner φ hf

@[simp] theorem linearIsometryOfInner_apply (x : E) : linearIsometryOfInner φ f hf x = f x := (rfl)

end Seminormed

section LiftInner

variable [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul A F] [CStarModule A F]
  (f : E → F) (hf : ∀ x y : E, inner A (f x) (f y) = inner A x y)
include φ

/-- An inner-product-preserving map `f : E → F` into a separated `CStarModule A F` descends to a
`ℂ`-linear isometry `SeparationQuotient E →ₗᵢ[ℂ] F`. -/
noncomputable def liftInnerₗᵢ : SeparationQuotient E →ₗᵢ[ℂ] F :=
  let fₗᵢ := linearIsometryOfInner φ f hf
  { toLinearMap := (SeparationQuotient.liftCLM fₗᵢ.toContinuousLinearMap
      fun _ _ h ↦ (h.map fₗᵢ.toContinuousLinearMap.continuous).eq).toLinearMap
    norm_map' := SeparationQuotient.surjective_mk.forall.2 fun x ↦ by
      rw [ContinuousLinearMap.coe_coe, SeparationQuotient.liftCLM_mk,
        LinearIsometry.coe_toContinuousLinearMap, fₗᵢ.norm_map, SeparationQuotient.norm_mk] }

@[simp] theorem liftInnerₗᵢ_mk (x : E) :
    liftInnerₗᵢ φ f hf (SeparationQuotient.mk x) = f x := (rfl)

/-- The separation-quotient lift of an inner-product-preserving map intertwines `A₀` along `φ`. -/
@[simp] theorem liftInnerₗᵢ_smul [ContinuousConstSMul A₀ E] (a₀ : A₀) (q : SeparationQuotient E) :
    liftInnerₗᵢ φ f hf (a₀ • q) = φ a₀ • liftInnerₗᵢ φ f hf q := by
  obtain ⟨x, rfl⟩ := SeparationQuotient.surjective_mk q
  rw [← SeparationQuotient.mk_smul, liftInnerₗᵢ_mk, liftInnerₗᵢ_mk]
  exact map_smul_along_of_inner φ hf a₀ x

/-- Uniqueness in the universal property of `SeparationQuotient E` for inner-preserving maps. -/
theorem eq_liftInnerₗᵢ_iff (g : SeparationQuotient E →ₗᵢ[ℂ] F) :
    g = liftInnerₗᵢ φ f hf ↔ ∀ x : E, g (SeparationQuotient.mk x) = f x :=
  ⟨fun h x ↦ by rw [h, liftInnerₗᵢ_mk], fun h ↦ LinearIsometry.ext <|
    SeparationQuotient.surjective_mk.forall.2 fun x ↦ (h x).trans (liftInnerₗᵢ_mk φ f hf x).symm⟩

end LiftInner
end SemiCStarModuleAlong

namespace SemiCStarModule

variable {A : Type*} [NonUnitalRing A] [StarRing A] [Module ℂ A] [StarModule ℂ A]
  [PartialOrder A] [Norm A]

/-- An inner-product-preserving map into a definite `CStarModule A F` intertwines the `A`-action. -/
theorem map_smul_of_inner {E F : Type*} [AddCommGroup E] [Module ℂ E] [SMul A E] [Norm E]
    [SemiCStarModule A E] [AddCommGroup F] [Module ℂ F] [SMul A F] [Norm F] [CStarModule A F]
    {f : E → F} (hf : ∀ x y : E, inner A (f x) (f y) = inner A x y) (a : A) (x : E) :
    f (a • x) = a • f x :=
  SemiCStarModuleAlong.map_smul_along_of_inner (.id ℂ A) hf a x

variable {E F : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E]
  [SemiCStarModule A E]

section Seminormed
variable [SeminormedAddCommGroup F] [NormedSpace ℂ F] [SMul A F] [CStarModule A F]
  (f : E → F) (hf : ∀ x y : E, inner A (f x) (f y) = inner A x y)

/-- Bundle an inner-product-preserving map into a definite `CStarModule` as a `LinearIsometry`. -/
def linearIsometryOfInner : E →ₗᵢ[ℂ] F :=
  SemiCStarModuleAlong.linearIsometryOfInner (.id ℂ A) f hf
@[simp] theorem linearIsometryOfInner_apply (x : E) : linearIsometryOfInner f hf x = f x := (rfl)
end Seminormed

section LiftInner
variable [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul A F] [CStarModule A F]
  (f : E → F) (hf : ∀ x y : E, inner A (f x) (f y) = inner A x y)

/-- An inner-product-preserving map `f : E → F` into a separated `CStarModule A F` descends to a
`ℂ`-linear isometry `SeparationQuotient E →ₗᵢ[ℂ] F`. -/
noncomputable def liftInnerₗᵢ : SeparationQuotient E →ₗᵢ[ℂ] F :=
  SemiCStarModuleAlong.liftInnerₗᵢ (.id ℂ A) f hf
@[simp] theorem liftInnerₗᵢ_mk (x : E) : liftInnerₗᵢ f hf (SeparationQuotient.mk x) = f x := (rfl)

/-- The separation-quotient lift of an inner-product-preserving map commutes with the `A`-action. -/
@[simp] theorem liftInnerₗᵢ_smul [ContinuousConstSMul A E] (a : A) (q : SeparationQuotient E) :
    liftInnerₗᵢ f hf (a • q) = a • liftInnerₗᵢ f hf q :=
  SemiCStarModuleAlong.liftInnerₗᵢ_smul (.id ℂ A) f hf a q

/-- Uniqueness in the universal property of `SeparationQuotient E` for inner-preserving maps. -/
theorem eq_liftInnerₗᵢ_iff (g : SeparationQuotient E →ₗᵢ[ℂ] F) :
    g = liftInnerₗᵢ f hf ↔ ∀ x : E, g (SeparationQuotient.mk x) = f x :=
  SemiCStarModuleAlong.eq_liftInnerₗᵢ_iff (.id ℂ A) f hf g
end LiftInner
end SemiCStarModule
end TauCeti

/-! ### The separation quotient of a positive semidefinite module -/

namespace SeparationQuotient

variable {A E : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [SeminormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [TauCeti.SemiCStarModule A E]

/-- The `A`-valued inner product on `SeparationQuotient E` for a `SemiCStarModule A E`. -/
noncomputable instance instInnerOfSemiCStarModule : Inner A (SeparationQuotient E) where
  inner := SeparationQuotient.lift₂ (inner A) fun _ _ _ _ hx hy ↦
    TauCeti.SemiCStarModule.inner_eq_inner_of_inseparable hx hy

@[simp] theorem inner_mk_mk_of_semiCStarModule (x y : E) :
    inner A (mk x : SeparationQuotient E) (mk y) = inner A x y := rfl

open scoped ComplexOrder in
-- Verify definitional equality with `InnerProductSpace`'s `SeparationQuotient` `Inner ℂ` instance.
example {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    (instInnerOfSemiCStarModule : Inner ℂ (SeparationQuotient H)) =
      SeparationQuotient.instInner := rfl

/-- The separation quotient of a positive semidefinite `A`-module is a definite `CStarModule A`. -/
noncomputable instance instCStarModule : CStarModule A (SeparationQuotient E) where
  toInner := instInnerOfSemiCStarModule
  inner_add_right {x y z} := by
    obtain ⟨x, rfl⟩ := surjective_mk x; obtain ⟨y, rfl⟩ := surjective_mk y
    obtain ⟨z, rfl⟩ := surjective_mk z
    rw [← mk_add]; exact TauCeti.SemiCStarModule.inner_add_right (A := A)
  inner_self_nonneg {x} := by
    obtain ⟨x, rfl⟩ := surjective_mk x; exact TauCeti.SemiCStarModule.inner_self_nonneg (A := A)
  inner_self {x} := by
    obtain ⟨x, rfl⟩ := surjective_mk x
    rw [inner_mk_mk_of_semiCStarModule,
      ← TauCeti.SemiCStarModule.norm_eq_zero_iff_inner_self_eq_zero (A := A), ← norm_mk,
      norm_eq_zero]
  inner_op_smul_right {a x y} := by
    obtain ⟨x, rfl⟩ := surjective_mk x; obtain ⟨y, rfl⟩ := surjective_mk y
    rw [← mk_smul]; exact TauCeti.SemiCStarModule.inner_op_smul_right (A := A)
  inner_smul_right_complex {z x y} := by
    obtain ⟨x, rfl⟩ := surjective_mk x; obtain ⟨y, rfl⟩ := surjective_mk y
    rw [← mk_smul]; exact TauCeti.SemiCStarModule.inner_smul_right_complex (A := A)
  star_inner := surjective_mk.forall₂.2 TauCeti.SemiCStarModule.star_inner
  norm_eq_sqrt_norm_inner_self := surjective_mk.forall.2 fun x ↦ by
    rw [norm_mk, inner_mk_mk_of_semiCStarModule,
      TauCeti.SemiCStarModule.norm_eq_sqrt_norm_inner_self (A := A) x]

end SeparationQuotient

namespace TauCeti.SemiCStarModule

/-- The separation-quotient lift of an inner-product-preserving map preserves inner products. -/
@[simp] theorem inner_liftInnerₗᵢ {A E F : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [SeminormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E]
    [SemiCStarModule A E] [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul A F] [CStarModule A F]
    (f : E → F) (hf : ∀ x y : E, inner A (f x) (f y) = inner A x y)
    (q₁ q₂ : SeparationQuotient E) :
    inner A (liftInnerₗᵢ f hf q₁) (liftInnerₗᵢ f hf q₂) = inner A q₁ q₂ := by
  obtain ⟨x, rfl⟩ := SeparationQuotient.surjective_mk q₁
  obtain ⟨y, rfl⟩ := SeparationQuotient.surjective_mk q₂
  rw [liftInnerₗᵢ_mk, liftInnerₗᵢ_mk, SeparationQuotient.inner_mk_mk_of_semiCStarModule, hf]

end TauCeti.SemiCStarModule

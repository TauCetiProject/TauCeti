/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Completion
public import Mathlib.Topology.Algebra.LinearMapCompletion
public import TauCeti.Analysis.InnerProductSpace.LinearPMap.ClosedForm
import TauCeti.Analysis.InnerProductSpace.LinearPMap.SelfAdjoint

/-!
# The Friedrichs extension by form completion

Let `S` be a densely defined symmetric partial linear operator on a Hilbert space `E` over
`𝕜` (`[RCLike 𝕜]`) with lower bound `γ : ℝ`, that is `γ * ‖x‖ ^ 2 ≤ re ⟪S x, x⟫_𝕜` on its domain
(`LinearPMap.IsSymmetricBoundedBelow S γ`). This file constructs the **Friedrichs extension** of
`S` by completing its form (Teschl, Theorem 2.12 through Lemma 2.10; Kato, Chapter VI,
Theorem 2.11).

The domain of `S` carries the positive definite form
`⟪x, y⟫_S = ⟪S x, y⟫_𝕜 + (1 - γ) * ⟪x, y⟫_𝕜`, whose norm dominates the norm of `E`. Its completion
`LinearPMap.FriedrichsSpace S γ hS` is a Hilbert space, the inclusion of the domain extends to a
contraction `LinearPMap.friedrichsInclusion` into `E`, and this contraction is injective
(`LinearPMap.friedrichsInclusion_injective`): this is the closability of the form `⟪S x, y⟫_𝕜`.
The completed form, shifted back by `γ - 1`, is the closed form `LinearPMap.friedrichsForm`, and
`LinearPMap.friedrichsExtension` is the operator it represents
(`ContinuousLinearMap.closedFormOperator`). It is self-adjoint, extends `S`, and keeps the lower
bound `γ`.

The construction works uniformly over `[RCLike 𝕜]`, so the real case needs no complexification.

## Main declarations

* `LinearPMap.IsSymmetricBoundedBelow`: a symmetric partial operator with lower bound `γ`.
* `LinearPMap.FriedrichsSpace`: the form completion of the domain.
* `LinearPMap.friedrichsInclusion`: its contractive inclusion into `E`, with
  `LinearPMap.friedrichsInclusion_injective` (closability) and
  `LinearPMap.denseRange_friedrichsInclusion`.
* `LinearPMap.friedrichsForm`: the closed form, with
  `LinearPMap.friedrichsForm_toFriedrichsSpace_left` and `_right` (it extends `⟪S x, y⟫_𝕜`).
* `LinearPMap.friedrichsExtension`: the Friedrichs extension, with
  `LinearPMap.mem_graph_friedrichsExtension_iff`, `LinearPMap.isSelfAdjoint_friedrichsExtension`,
  `LinearPMap.le_friedrichsExtension`,
  `LinearPMap.mul_norm_sq_le_re_inner_friedrichsExtension` and the uniqueness statement
  `LinearPMap.eq_friedrichsExtension_of_isSelfAdjoint`.
* `LinearPMap.exists_isSelfAdjoint_extension_of_isSymmetricBoundedBelow`: every densely defined
  symmetric operator with lower bound `γ` has a self-adjoint extension with lower bound `γ`.

## References

* G. Teschl, *Mathematical Methods in Quantum Mechanics*, 2nd ed., AMS (2014), §2.3,
  Lemma 2.10 and Theorem 2.12.
* T. Kato, *Perturbation Theory for Linear Operators*, Springer (1995), Chapter VI, §2.3,
  Theorem 2.11.
-/

public section

noncomputable section

open scoped InnerProductSpace

namespace LinearPMap

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- A partial linear operator `S` on `E` is symmetric with lower bound `γ` if it is formally
self-adjoint and `γ * ‖x‖ ^ 2 ≤ re ⟪S x, x⟫_𝕜` for every `x` in its domain. -/
structure IsSymmetricBoundedBelow (S : E →ₗ.[𝕜] E) (γ : ℝ) : Prop where
  /-- `S` is symmetric. -/
  isFormalAdjoint : S.IsFormalAdjoint S
  /-- `γ` is a lower bound of `S`. -/
  mul_norm_sq_le_re_inner : ∀ x : S.domain, γ * ‖(x : E)‖ ^ 2 ≤ RCLike.re ⟪S x, (x : E)⟫_𝕜

variable {S : E →ₗ.[𝕜] E} {γ : ℝ}

/-! ### The form pre-Hilbert space on the domain -/

/-- The domain of `S`, to be equipped with the form inner product
`⟪x, y⟫_S = ⟪S x, y⟫_𝕜 + (1 - γ) * ⟪x, y⟫_𝕜`. -/
@[ext]
structure FriedrichsPre (S : E →ₗ.[𝕜] E) (γ : ℝ) (hS : S.IsSymmetricBoundedBelow γ) where
  /-- Construct an element of `FriedrichsPre` from a vector of the domain. -/
  ofDomain ::
  /-- The underlying vector of the domain. -/
  toDomain : S.domain

namespace FriedrichsPre

variable (hS : S.IsSymmetricBoundedBelow γ)

/-- `FriedrichsPre.toDomain` is injective. -/
theorem toDomain_injective : Function.Injective (toDomain : FriedrichsPre S γ hS → S.domain) :=
  fun _ _ => FriedrichsPre.ext

/-- `ofDomain` is a left inverse of `toDomain`. -/
@[simp]
theorem ofDomain_toDomain (x : FriedrichsPre S γ hS) : ofDomain x.toDomain = x :=
  (rfl)

/-- `toDomain` is a left inverse of `ofDomain`. -/
theorem toDomain_ofDomain (x : S.domain) : (ofDomain x : FriedrichsPre S γ hS).toDomain = x :=
  (rfl)

instance instZero : Zero (FriedrichsPre S γ hS) := ⟨⟨0⟩⟩
instance instAdd : Add (FriedrichsPre S γ hS) := ⟨fun x y => ⟨x.toDomain + y.toDomain⟩⟩
instance instNeg : Neg (FriedrichsPre S γ hS) := ⟨fun x => ⟨-x.toDomain⟩⟩
instance instSub : Sub (FriedrichsPre S γ hS) := ⟨fun x y => ⟨x.toDomain - y.toDomain⟩⟩
instance instSMulNat : SMul ℕ (FriedrichsPre S γ hS) := ⟨fun n x => ⟨n • x.toDomain⟩⟩
instance instSMulInt : SMul ℤ (FriedrichsPre S γ hS) := ⟨fun n x => ⟨n • x.toDomain⟩⟩
instance instSMul : SMul 𝕜 (FriedrichsPre S γ hS) := ⟨fun c x => ⟨c • x.toDomain⟩⟩

/-- `toDomain` sends `0` to `0`. -/
@[simp]
theorem toDomain_zero : (0 : FriedrichsPre S γ hS).toDomain = 0 :=
  (rfl)

/-- `toDomain` is additive. -/
@[simp]
theorem toDomain_add (x y : FriedrichsPre S γ hS) : (x + y).toDomain = x.toDomain + y.toDomain :=
  (rfl)

/-- `toDomain` commutes with negation. -/
@[simp]
theorem toDomain_neg (x : FriedrichsPre S γ hS) : (-x).toDomain = -x.toDomain :=
  (rfl)

/-- `toDomain` commutes with subtraction. -/
@[simp]
theorem toDomain_sub (x y : FriedrichsPre S γ hS) : (x - y).toDomain = x.toDomain - y.toDomain :=
  (rfl)

/-- `toDomain` commutes with scalar multiplication. -/
@[simp]
theorem toDomain_smul (c : 𝕜) (x : FriedrichsPre S γ hS) : (c • x).toDomain = c • x.toDomain :=
  (rfl)

/-- `ofDomain` sends `0` to `0`. -/
@[simp]
theorem ofDomain_zero : (ofDomain 0 : FriedrichsPre S γ hS) = 0 :=
  (rfl)

/-- `ofDomain` is additive. -/
@[simp]
theorem ofDomain_add (x y : S.domain) :
    (ofDomain (x + y) : FriedrichsPre S γ hS) = ofDomain x + ofDomain y :=
  (rfl)

/-- `ofDomain` commutes with negation. -/
@[simp]
theorem ofDomain_neg (x : S.domain) : (ofDomain (-x) : FriedrichsPre S γ hS) = -ofDomain x :=
  (rfl)

/-- `ofDomain` commutes with subtraction. -/
@[simp]
theorem ofDomain_sub (x y : S.domain) :
    (ofDomain (x - y) : FriedrichsPre S γ hS) = ofDomain x - ofDomain y :=
  (rfl)

/-- `ofDomain` commutes with scalar multiplication. -/
@[simp]
theorem ofDomain_smul (c : 𝕜) (x : S.domain) :
    (ofDomain (c • x) : FriedrichsPre S γ hS) = c • ofDomain x :=
  (rfl)

instance instAddCommGroup : AddCommGroup (FriedrichsPre S γ hS) :=
  (toDomain_injective hS).addCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl)

instance instModule : Module 𝕜 (FriedrichsPre S γ hS) :=
  (toDomain_injective hS).module 𝕜 ⟨⟨toDomain, rfl⟩, fun _ _ => rfl⟩ fun _ _ => rfl

/-- `FriedrichsPre` is linearly equivalent to the domain of `S`. -/
def linearEquivDomain : FriedrichsPre S γ hS ≃ₗ[𝕜] S.domain where
  toFun := toDomain
  invFun := ofDomain
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- `linearEquivDomain` sends `x` to `x.toDomain`. -/
@[simp]
theorem linearEquivDomain_apply (x : FriedrichsPre S γ hS) :
    linearEquivDomain hS x = x.toDomain :=
  (rfl)

/-- The inverse of `linearEquivDomain` is `ofDomain`. -/
@[simp]
theorem linearEquivDomain_symm_apply (x : S.domain) :
    (linearEquivDomain hS).symm x = ofDomain x :=
  (rfl)

/-- The form inner product `⟪x, y⟫_S = ⟪S x, y⟫_𝕜 + (1 - γ) * ⟪x, y⟫_𝕜` on `FriedrichsPre` as a
pre-inner-product core. -/
abbrev preInnerCore : PreInnerProductSpace.Core 𝕜 (FriedrichsPre S γ hS) where
  inner x y :=
    ⟪S x.toDomain, (y.toDomain : E)⟫_𝕜 + ((1 - γ : ℝ) : 𝕜) * ⟪(x.toDomain : E), (y.toDomain : E)⟫_𝕜
  conj_inner_symm x y := by
    simp [hS.isFormalAdjoint x.toDomain y.toDomain]
  re_inner_nonneg x := by
    simp only [_root_.map_add, RCLike.re_ofReal_mul, inner_self_eq_norm_sq]
    linarith [hS.mul_norm_sq_le_re_inner x.toDomain, sq_nonneg ‖(x.toDomain : E)‖]
  add_left x y z := by
    simp only [toDomain_add, LinearPMap.map_add, Submodule.coe_add, inner_add_left]
    ring
  smul_left x y r := by
    simp only [toDomain_smul, LinearPMap.map_smul, Submodule.coe_smul, inner_smul_left]
    ring

instance instSeminormedAddCommGroup : SeminormedAddCommGroup (FriedrichsPre S γ hS) :=
  InnerProductSpace.Core.toSeminormedAddCommGroup (c := preInnerCore hS)

instance instInnerProductSpace : InnerProductSpace 𝕜 (FriedrichsPre S γ hS) :=
  InnerProductSpace.ofCore (preInnerCore hS)

/-- The inner product of `FriedrichsPre` is the form inner product. -/
theorem inner_def (x y : FriedrichsPre S γ hS) :
    ⟪x, y⟫_𝕜 = ⟪S x.toDomain, (y.toDomain : E)⟫_𝕜 +
      ((1 - γ : ℝ) : 𝕜) * ⟪(x.toDomain : E), (y.toDomain : E)⟫_𝕜 :=
  (rfl)

/-- The diagonal real part of the form inner product. -/
theorem re_inner_self (x : FriedrichsPre S γ hS) :
    RCLike.re ⟪x, x⟫_𝕜 =
      RCLike.re ⟪S x.toDomain, (x.toDomain : E)⟫_𝕜 + (1 - γ) * ‖(x.toDomain : E)‖ ^ 2 := by
  rw [inner_def, _root_.map_add, RCLike.re_ofReal_mul, inner_self_eq_norm_sq]

/-- The form inner product dominates the square of the norm of `E` on the diagonal. -/
theorem norm_sq_le_re_inner_self (x : FriedrichsPre S γ hS) :
    ‖(x.toDomain : E)‖ ^ 2 ≤ RCLike.re ⟪x, x⟫_𝕜 := by
  rw [re_inner_self]
  linarith [hS.mul_norm_sq_le_re_inner x.toDomain]

/-- The norm of `E` is dominated by the form norm. -/
theorem norm_toDomain_le (x : FriedrichsPre S γ hS) : ‖(x.toDomain : E)‖ ≤ ‖x‖ := by
  refine le_of_sq_le_sq ?_ (norm_nonneg _)
  rw [norm_sq_eq_re_inner (𝕜 := 𝕜) x]
  exact norm_sq_le_re_inner_self hS x

/-- The inclusion of `FriedrichsPre` into `E`, a contraction. -/
def inclusion : FriedrichsPre S γ hS →L[𝕜] E :=
  LinearMap.mkContinuous (S.domain.subtype ∘ₗ (linearEquivDomain hS).toLinearMap) 1 fun x => by
    simpa using norm_toDomain_le hS x

/-- `FriedrichsPre.inclusion` sends `x` to its underlying vector. -/
@[simp]
theorem inclusion_apply (x : FriedrichsPre S γ hS) : inclusion hS x = x.toDomain :=
  (rfl)

end FriedrichsPre

/-! ### The form completion -/

variable (S γ) in
/-- The **form domain** of the Friedrichs extension: the completion of the domain of `S` in the
form norm `(re ⟪S x, x⟫_𝕜 + (1 - γ) * ‖x‖ ^ 2) ^ (1 / 2)`. -/
abbrev FriedrichsSpace (hS : S.IsSymmetricBoundedBelow γ) : Type _ :=
  UniformSpace.Completion (FriedrichsPre S γ hS)

variable (hS : S.IsSymmetricBoundedBelow γ)

/-- The linear map sending a vector of the domain of `S` to its image in the form completion. -/
def toFriedrichsSpace : S.domain →ₗ[𝕜] FriedrichsSpace S γ hS :=
  (UniformSpace.Completion.toComplL : FriedrichsPre S γ hS →L[𝕜] _).toLinearMap ∘ₗ
    (FriedrichsPre.linearEquivDomain hS).symm.toLinearMap

/-- `toFriedrichsSpace` is the coercion into the completion of `FriedrichsPre.ofDomain`. -/
theorem toFriedrichsSpace_apply (x : S.domain) :
    toFriedrichsSpace hS x = ((FriedrichsPre.ofDomain x : FriedrichsPre S γ hS) :
      FriedrichsSpace S γ hS) :=
  (rfl)

/-- Every element of `FriedrichsPre` maps into the form completion through `toFriedrichsSpace`. -/
theorem coe_eq_toFriedrichsSpace_toDomain (y : FriedrichsPre S γ hS) :
    (y : FriedrichsSpace S γ hS) = toFriedrichsSpace hS y.toDomain :=
  (rfl)

/-- The inner product of the form completion on vectors of the domain of `S`. -/
@[simp]
theorem inner_toFriedrichsSpace (x y : S.domain) :
    ⟪toFriedrichsSpace hS x, toFriedrichsSpace hS y⟫_𝕜 =
      ⟪S x, (y : E)⟫_𝕜 + ((1 - γ : ℝ) : 𝕜) * ⟪(x : E), (y : E)⟫_𝕜 := by
  simp only [toFriedrichsSpace_apply, UniformSpace.Completion.inner_coe, FriedrichsPre.inner_def]

/-- The squared form norm of a vector of the domain of `S`. -/
theorem norm_toFriedrichsSpace_sq (x : S.domain) :
    ‖toFriedrichsSpace hS x‖ ^ 2 = RCLike.re ⟪S x, (x : E)⟫_𝕜 + (1 - γ) * ‖(x : E)‖ ^ 2 := by
  rw [toFriedrichsSpace_apply, UniformSpace.Completion.norm_coe, norm_sq_eq_re_inner (𝕜 := 𝕜),
    FriedrichsPre.re_inner_self]

/-- The domain of `S` is dense in its form completion. -/
theorem denseRange_toFriedrichsSpace : DenseRange (toFriedrichsSpace hS) :=
  UniformSpace.Completion.denseRange_coe.comp
    (FriedrichsPre.linearEquivDomain hS).symm.surjective.denseRange
    (UniformSpace.Completion.continuous_coe _)

variable [CompleteSpace E]

/-- The inclusion of the form completion into `E`: the continuous extension of the inclusion of
the domain of `S`. -/
def friedrichsInclusion : FriedrichsSpace S γ hS →L[𝕜] E :=
  (FriedrichsPre.inclusion hS).fromCompletion

/-- `friedrichsInclusion` sends an element of `FriedrichsPre` to its underlying vector. -/
@[simp]
theorem friedrichsInclusion_coe (y : FriedrichsPre S γ hS) :
    friedrichsInclusion hS y = y.toDomain := by
  rw [friedrichsInclusion, ContinuousLinearMap.fromCompletion_apply_coe,
    FriedrichsPre.inclusion_apply]

/-- `friedrichsInclusion` restricts to the inclusion of the domain of `S`. -/
@[simp]
theorem friedrichsInclusion_toFriedrichsSpace (x : S.domain) :
    friedrichsInclusion hS (toFriedrichsSpace hS x) = x := by
  rw [toFriedrichsSpace_apply, friedrichsInclusion_coe, FriedrichsPre.toDomain_ofDomain]

/-- `toFriedrichsSpace` is injective. -/
theorem toFriedrichsSpace_injective : Function.Injective (toFriedrichsSpace hS) := fun x y h =>
  Subtype.ext <| by
    rw [← friedrichsInclusion_toFriedrichsSpace hS x, h, friedrichsInclusion_toFriedrichsSpace]

/-- The inclusion of the form completion is a contraction. -/
theorem norm_friedrichsInclusion_apply_le (u : FriedrichsSpace S γ hS) :
    ‖friedrichsInclusion hS u‖ ≤ ‖u‖ := by
  induction u using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_le (by fun_prop) continuous_norm
  | ih x =>
    rw [friedrichsInclusion_coe, UniformSpace.Completion.norm_coe]
    exact FriedrichsPre.norm_toDomain_le hS x

/-- The form inner product against a vector of the domain of `S` is computed in `E`:
`⟪u, x⟫_S = ⟪j u, S x + (1 - γ) • x⟫_𝕜`. -/
theorem inner_toFriedrichsSpace_right (u : FriedrichsSpace S γ hS) (x : S.domain) :
    ⟪u, toFriedrichsSpace hS x⟫_𝕜 =
      ⟪friedrichsInclusion hS u, S x + ((1 - γ : ℝ) : 𝕜) • (x : E)⟫_𝕜 := by
  induction u using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih y =>
    rw [coe_eq_toFriedrichsSpace_toDomain]
    simp [inner_add_right, inner_smul_right, hS.isFormalAdjoint y.toDomain x]

/-- **Closability of the form of `S`** (Teschl, Lemma 2.10): the inclusion of the form completion
into `E` is injective. -/
theorem friedrichsInclusion_injective : Function.Injective (friedrichsInclusion hS) := by
  refine (injective_iff_map_eq_zero _).mpr fun u hu => ?_
  refine (denseRange_toFriedrichsSpace hS).eq_zero_of_inner_left (𝕜 := 𝕜) fun x => ?_
  rw [inner_toFriedrichsSpace_right, hu, inner_zero_left]

/-- The inclusion of the form completion has dense range when `S` is densely defined. -/
theorem denseRange_friedrichsInclusion (hdense : Dense (S.domain : Set E)) :
    DenseRange (friedrichsInclusion hS) :=
  hdense.mono fun x hx => ⟨toFriedrichsSpace hS ⟨x, hx⟩, by simp⟩

/-- The closed form of the Friedrichs extension on the form completion:
`q(u, v) = ⟪u, v⟫_S + (γ - 1) * ⟪j u, j v⟫_𝕜`. -/
def friedrichsForm : FriedrichsSpace S γ hS →L⋆[𝕜] FriedrichsSpace S γ hS →L[𝕜] 𝕜 :=
  (friedrichsInclusion hS).shiftedForm (innerSL 𝕜) (γ - 1)

/-- Pointwise evaluation of `friedrichsForm`. -/
theorem friedrichsForm_apply (u v : FriedrichsSpace S γ hS) :
    friedrichsForm hS u v =
      ⟪u, v⟫_𝕜 + ((γ - 1 : ℝ) : 𝕜) * ⟪friedrichsInclusion hS u, friedrichsInclusion hS v⟫_𝕜 := by
  rw [friedrichsForm, ContinuousLinearMap.shiftedForm_apply, innerSL_apply_apply]

/-- The closed form of the Friedrichs extension is Hermitian. -/
theorem friedrichsForm_eq_star (u v : FriedrichsSpace S γ hS) :
    friedrichsForm hS u v = star (friedrichsForm hS v u) :=
  ContinuousLinearMap.shiftedForm_eq_star _
    (fun u v => by rw [innerSL_apply_apply, innerSL_apply_apply, RCLike.star_def,
      inner_conj_symm]) _ u v

/-- The closed form extends the form of `S`: `q(x, v) = ⟪S x, j v⟫_𝕜` for `x` in the domain of `S`
and every `v` in the form completion. -/
@[simp]
theorem friedrichsForm_toFriedrichsSpace_left (x : S.domain) (v : FriedrichsSpace S γ hS) :
    friedrichsForm hS (toFriedrichsSpace hS x) v = ⟪S x, friedrichsInclusion hS v⟫_𝕜 := by
  rw [friedrichsForm_apply, ← inner_conj_symm, inner_toFriedrichsSpace_right]
  simp only [inner_add_left, inner_smul_left, friedrichsInclusion_toFriedrichsSpace,
    inner_conj_symm, RCLike.conj_ofReal]
  push_cast
  ring

/-- The closed form extends the form of `S` in its second argument: `q(v, x) = ⟪j v, S x⟫_𝕜` for
`x` in the domain of `S` and every `v` in the form completion. -/
@[simp]
theorem friedrichsForm_toFriedrichsSpace_right (v : FriedrichsSpace S γ hS) (x : S.domain) :
    friedrichsForm hS v (toFriedrichsSpace hS x) = ⟪friedrichsInclusion hS v, S x⟫_𝕜 := by
  rw [friedrichsForm_eq_star, friedrichsForm_toFriedrichsSpace_left, RCLike.star_def,
    inner_conj_symm]

/-- The diagonal of the closed form: `re q(u, u) = ‖u‖ ^ 2 + (γ - 1) ‖j u‖ ^ 2`. -/
theorem re_friedrichsForm_self (u : FriedrichsSpace S γ hS) :
    RCLike.re (friedrichsForm hS u u) = ‖u‖ ^ 2 + (γ - 1) * ‖friedrichsInclusion hS u‖ ^ 2 := by
  rw [friedrichsForm, ContinuousLinearMap.re_shiftedForm_self, innerSL_apply_apply,
    inner_self_eq_norm_sq]

/-- The closed form of the Friedrichs extension is coercive after shifting by `1 - γ`. -/
theorem one_mul_norm_sq_le_re_friedrichsForm_add (u : FriedrichsSpace S γ hS) :
    1 * ‖u‖ ^ 2 ≤
      RCLike.re (friedrichsForm hS u u) + (1 - γ) * ‖friedrichsInclusion hS u‖ ^ 2 := by
  rw [re_friedrichsForm_self]
  linarith

/-- The closed form of the Friedrichs extension is bounded below by `γ`. -/
theorem mul_norm_sq_le_re_friedrichsForm (u : FriedrichsSpace S γ hS) :
    γ * ‖friedrichsInclusion hS u‖ ^ 2 ≤ RCLike.re (friedrichsForm hS u u) := by
  rw [re_friedrichsForm_self]
  have h := norm_friedrichsInclusion_apply_le hS u
  have h0 := norm_nonneg (friedrichsInclusion hS u)
  nlinarith

/-! ### The Friedrichs extension -/

/-- The **Friedrichs extension** of a densely defined symmetric operator `S` with lower bound `γ`:
the self-adjoint operator represented by the closure of the form `⟪S x, y⟫_𝕜`. -/
def friedrichsExtension (hdense : Dense (S.domain : Set E)) : E →ₗ.[𝕜] E :=
  (friedrichsInclusion hS).closedFormOperator (friedrichsInclusion_injective hS)
    (denseRange_friedrichsInclusion hS hdense) (friedrichsForm hS)

/-- The Friedrichs extension is the operator represented by `friedrichsForm`. -/
theorem friedrichsExtension_eq_closedFormOperator (hdense : Dense (S.domain : Set E)) :
    friedrichsExtension hS hdense =
      (friedrichsInclusion hS).closedFormOperator (friedrichsInclusion_injective hS)
        (denseRange_friedrichsInclusion hS hdense) (friedrichsForm hS) :=
  (rfl)

/-- **Domain of the Friedrichs extension.** A vector `x` lies in it exactly when `x = j u` for a
vector `u` of the form completion such that `q(u, ·)` is represented by some `h : E`. -/
theorem mem_domain_friedrichsExtension_iff (hdense : Dense (S.domain : Set E)) {x : E} :
    x ∈ (friedrichsExtension hS hdense).domain ↔
      ∃ u : FriedrichsSpace S γ hS, friedrichsInclusion hS u = x ∧
        ∃ h : E, ∀ v, friedrichsForm hS u v = ⟪h, friedrichsInclusion hS v⟫_𝕜 :=
  ContinuousLinearMap.mem_domain_closedFormOperator_iff _ _ _ _

/-- If `q(u, v) = ⟪h, j v⟫_𝕜` for all `v`, then `j u` lies in the domain of the Friedrichs
extension. -/
theorem apply_mem_domain_friedrichsExtension (hdense : Dense (S.domain : Set E))
    {u : FriedrichsSpace S γ hS} {h : E}
    (hu : ∀ v, friedrichsForm hS u v = ⟪h, friedrichsInclusion hS v⟫_𝕜) :
    friedrichsInclusion hS u ∈ (friedrichsExtension hS hdense).domain :=
  ContinuousLinearMap.apply_mem_domain_closedFormOperator _ _ _ _ hu

/-- **Action of the Friedrichs extension.** If `x = j u` and `q(u, v) = ⟪h, j v⟫_𝕜` for all `v`,
then the Friedrichs extension sends `x` to `h`. -/
theorem friedrichsExtension_apply_eq (hdense : Dense (S.domain : Set E))
    {x : (friedrichsExtension hS hdense).domain} {u : FriedrichsSpace S γ hS} {h : E}
    (hx : friedrichsInclusion hS u = x)
    (hu : ∀ v, friedrichsForm hS u v = ⟪h, friedrichsInclusion hS v⟫_𝕜) :
    friedrichsExtension hS hdense x = h :=
  ContinuousLinearMap.closedFormOperator_apply_eq _ _ _ _ hx hu

/-- **Form identity of the Friedrichs extension.** If `x = j u`, then
`⟪T x, j v⟫_𝕜 = q(u, v)` for every `v` of the form completion. -/
theorem inner_friedrichsExtension (hdense : Dense (S.domain : Set E))
    {x : (friedrichsExtension hS hdense).domain} {u : FriedrichsSpace S γ hS}
    (hx : friedrichsInclusion hS u = x) (v : FriedrichsSpace S γ hS) :
    ⟪friedrichsExtension hS hdense x, friedrichsInclusion hS v⟫_𝕜 = friedrichsForm hS u v :=
  ContinuousLinearMap.inner_closedFormOperator _ _ _ _ hx v

/-- **Graph characterization of the Friedrichs extension.** The pair `(x, h)` lies in its graph
exactly when `x = j u` for a vector `u` of the form completion with `q(u, v) = ⟪h, j v⟫_𝕜` for all
`v`. -/
theorem mem_graph_friedrichsExtension_iff (hdense : Dense (S.domain : Set E)) {p : E × E} :
    p ∈ (friedrichsExtension hS hdense).graph ↔
      ∃ u : FriedrichsSpace S γ hS, friedrichsInclusion hS u = p.1 ∧
        ∀ v, friedrichsForm hS u v = ⟪p.2, friedrichsInclusion hS v⟫_𝕜 :=
  ContinuousLinearMap.mem_graph_closedFormOperator_iff _ _ _ _

/-- The Friedrichs extension is self-adjoint. -/
theorem isSelfAdjoint_friedrichsExtension (hdense : Dense (S.domain : Set E)) :
    IsSelfAdjoint (friedrichsExtension hS hdense) :=
  ContinuousLinearMap.isSelfAdjoint_closedFormOperator _ _ _ _ (friedrichsForm_eq_star hS)
    (ContinuousLinearMap.isUnit_continuousLinearMapOfBilin_shiftedForm _ one_pos le_rfl
      (one_mul_norm_sq_le_re_friedrichsForm_add hS))

/-- The Friedrichs extension extends `S`. -/
theorem le_friedrichsExtension (hdense : Dense (S.domain : Set E)) :
    S ≤ friedrichsExtension hS hdense := by
  refine le_of_le_graph fun p hp => ?_
  obtain ⟨x, hx, hSx⟩ := (mem_graph_iff S).mp hp
  rw [← Prod.mk.eta (p := p), ← hx, ← hSx]
  exact (mem_graph_friedrichsExtension_iff hS hdense).mpr
    ⟨toFriedrichsSpace hS x, friedrichsInclusion_toFriedrichsSpace hS x,
      friedrichsForm_toFriedrichsSpace_left hS x⟩

/-- **Uniqueness of the Friedrichs extension** (Kato, Chapter VI, Theorem 2.11). A self-adjoint
extension of `S` whose domain lies in the image of the form completion is the Friedrichs
extension. -/
theorem eq_friedrichsExtension_of_isSelfAdjoint (hdense : Dense (S.domain : Set E))
    {T : E →ₗ.[𝕜] E} (hT : IsSelfAdjoint T) (hST : S ≤ T)
    (hrange : ∀ x : T.domain, (x : E) ∈ Set.range (friedrichsInclusion hS)) :
    T = friedrichsExtension hS hdense := by
  refine ContinuousLinearMap.eq_closedFormOperator_of_isSelfAdjoint _ _ _ _
    (friedrichsForm_eq_star hS) hT fun x => ?_
  obtain ⟨u, hu⟩ := hrange x
  refine ⟨u, hu, fun v => ?_⟩
  refine (denseRange_toFriedrichsSpace hS).induction_on v
    (isClosed_eq (by fun_prop) (by fun_prop)) fun y => ?_
  have hy : (y : E) ∈ T.domain := hST.1 y.property
  rw [friedrichsForm_toFriedrichsSpace_right, friedrichsInclusion_toFriedrichsSpace, hu,
    hST.2 (x := y) (y := ⟨y, hy⟩) rfl]
  exact (hT.isFormalAdjoint x ⟨y, hy⟩).symm

/-- The Friedrichs extension keeps the lower bound `γ` of `S`. -/
theorem mul_norm_sq_le_re_inner_friedrichsExtension (hdense : Dense (S.domain : Set E))
    (x : (friedrichsExtension hS hdense).domain) :
    γ * ‖(x : E)‖ ^ 2 ≤ RCLike.re ⟪friedrichsExtension hS hdense x, (x : E)⟫_𝕜 :=
  ContinuousLinearMap.mul_norm_sq_le_re_inner_closedFormOperator _ _ _ _
    (mul_norm_sq_le_re_friedrichsForm hS) x

/-- **Existence of the Friedrichs extension** (Teschl, Theorem 2.12). A densely defined symmetric
partial operator with lower bound `γ` on a Hilbert space has a self-adjoint extension with the same
lower bound. -/
theorem exists_isSelfAdjoint_extension_of_isSymmetricBoundedBelow
    (hS : S.IsSymmetricBoundedBelow γ) (hdense : Dense (S.domain : Set E)) :
    ∃ T : E →ₗ.[𝕜] E, IsSelfAdjoint T ∧ S ≤ T ∧
      ∀ x : T.domain, γ * ‖(x : E)‖ ^ 2 ≤ RCLike.re ⟪T x, (x : E)⟫_𝕜 :=
  ⟨friedrichsExtension hS hdense, isSelfAdjoint_friedrichsExtension hS hdense,
    le_friedrichsExtension hS hdense, mul_norm_sq_le_re_inner_friedrichsExtension hS hdense⟩

end LinearPMap

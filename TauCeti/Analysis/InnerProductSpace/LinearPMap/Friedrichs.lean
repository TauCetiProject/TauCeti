/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Completion
public import Mathlib.Topology.Algebra.LinearMapCompletion
public import TauCeti.Analysis.InnerProductSpace.LinearPMap.ClosedForm

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
(`LinearPMap.injective_friedrichsInclusion`): this is the closability of the form `⟪S x, y⟫_𝕜`.
The completed form, shifted back by `γ - 1`, is the closed form `LinearPMap.friedrichsForm`, and
`LinearPMap.friedrichsExtension` is the operator it represents
(`ContinuousLinearMap.closedFormOperator`). It is self-adjoint, extends `S`, and keeps the lower
bound `γ`.

The construction works uniformly over `[RCLike 𝕜]`, so the real case needs no complexification.

## Main declarations

* `LinearPMap.IsSymmetricBoundedBelow`: a symmetric partial operator with lower bound `γ`.
* `LinearPMap.FriedrichsSpace`: the form completion of the domain.
* `LinearPMap.friedrichsInclusion`: its contractive inclusion into `E`, with
  `LinearPMap.injective_friedrichsInclusion` (closability) and
  `LinearPMap.denseRange_friedrichsInclusion`.
* `LinearPMap.friedrichsForm`: the closed form, with
  `LinearPMap.friedrichsForm_toFriedrichsSpace_left` (it extends `⟪S x, y⟫_𝕜`).
* `LinearPMap.friedrichsExtension`: the Friedrichs extension, with
  `LinearPMap.mem_graph_friedrichsExtension_iff`, `LinearPMap.isSelfAdjoint_friedrichsExtension`,
  `LinearPMap.le_friedrichsExtension` and
  `LinearPMap.mul_norm_sq_le_re_inner_friedrichsExtension`.
* `LinearPMap.exists_isSelfAdjoint_extension_of_isSymmetricBoundedBelow`: every densely defined
  symmetric operator with lower bound `γ` has a self-adjoint extension with lower bound `γ`.

## References

* G. Teschl, *Mathematical Methods in Quantum Mechanics*, 2nd ed., AMS (2014), §2.3,
  Lemma 2.10 and Theorem 2.12.
* T. Kato, *Perturbation Theory for Linear Operators*, Springer (1995), Chapter VI, §2.3,
  Theorem 2.11.
-/

@[expose] public section

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
structure FriedrichsPre (S : E →ₗ.[𝕜] E) (γ : ℝ) (hS : S.IsSymmetricBoundedBelow γ) where
  /-- Construct an element of `FriedrichsPre` from a vector of the domain. -/
  ofDomain ::
  /-- The underlying vector of the domain. -/
  toDomain : S.domain

namespace FriedrichsPre

variable (hS : S.IsSymmetricBoundedBelow γ)

/-- `FriedrichsPre.toDomain` is injective. -/
theorem toDomain_injective : Function.Injective (toDomain : FriedrichsPre S γ hS → S.domain) :=
  fun ⟨_⟩ ⟨_⟩ h => by cases h; rfl

instance instZero : Zero (FriedrichsPre S γ hS) := ⟨⟨0⟩⟩
instance instAdd : Add (FriedrichsPre S γ hS) := ⟨fun x y => ⟨x.toDomain + y.toDomain⟩⟩
instance instNeg : Neg (FriedrichsPre S γ hS) := ⟨fun x => ⟨-x.toDomain⟩⟩
instance instSub : Sub (FriedrichsPre S γ hS) := ⟨fun x y => ⟨x.toDomain - y.toDomain⟩⟩
instance instSMulNat : SMul ℕ (FriedrichsPre S γ hS) := ⟨fun n x => ⟨n • x.toDomain⟩⟩
instance instSMulInt : SMul ℤ (FriedrichsPre S γ hS) := ⟨fun n x => ⟨n • x.toDomain⟩⟩
instance instSMul : SMul 𝕜 (FriedrichsPre S γ hS) := ⟨fun c x => ⟨c • x.toDomain⟩⟩

/-- `toDomain` is additive. -/
@[simp]
theorem toDomain_add (x y : FriedrichsPre S γ hS) : (x + y).toDomain = x.toDomain + y.toDomain :=
  rfl

/-- `toDomain` commutes with scalar multiplication. -/
@[simp]
theorem toDomain_smul (c : 𝕜) (x : FriedrichsPre S γ hS) : (c • x).toDomain = c • x.toDomain :=
  rfl

instance instAddCommGroup : AddCommGroup (FriedrichsPre S γ hS) :=
  (toDomain_injective hS).addCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl)

/-- `FriedrichsPre.toDomain` as an additive monoid homomorphism. -/
def toDomainAddMonoidHom : FriedrichsPre S γ hS →+ S.domain where
  toFun := toDomain
  map_zero' := rfl
  map_add' _ _ := rfl

instance instModule : Module 𝕜 (FriedrichsPre S γ hS) :=
  (toDomain_injective hS).module 𝕜 (toDomainAddMonoidHom hS) fun _ _ => rfl

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
  rfl

/-- The inverse of `linearEquivDomain` is `ofDomain`. -/
@[simp]
theorem linearEquivDomain_symm_apply (x : S.domain) :
    (linearEquivDomain hS).symm x = ofDomain x :=
  rfl

/-- The form inner product `⟪x, y⟫_S = ⟪S x, y⟫_𝕜 + (1 - γ) * ⟪x, y⟫_𝕜` on `FriedrichsPre`. -/
def preInner (x y : FriedrichsPre S γ hS) : 𝕜 :=
  ⟪S x.toDomain, (y.toDomain : E)⟫_𝕜 + ((1 - γ : ℝ) : 𝕜) * ⟪(x.toDomain : E), (y.toDomain : E)⟫_𝕜

/-- The diagonal real part of the form inner product. -/
theorem re_preInner_self (x : FriedrichsPre S γ hS) :
    RCLike.re (preInner hS x x) =
      RCLike.re ⟪S x.toDomain, (x.toDomain : E)⟫_𝕜 + (1 - γ) * ‖(x.toDomain : E)‖ ^ 2 := by
  rw [preInner, _root_.map_add, RCLike.re_ofReal_mul, inner_self_eq_norm_sq]

/-- The form inner product dominates the square of the norm of `E` on the diagonal. -/
theorem norm_sq_le_re_preInner_self (x : FriedrichsPre S γ hS) :
    ‖(x.toDomain : E)‖ ^ 2 ≤ RCLike.re (preInner hS x x) := by
  rw [re_preInner_self]
  linarith [hS.mul_norm_sq_le_re_inner x.toDomain]

/-- The form inner product on `FriedrichsPre` as a pre-inner-product core. -/
abbrev preInnerCore : PreInnerProductSpace.Core 𝕜 (FriedrichsPre S γ hS) where
  inner := preInner hS
  conj_inner_symm x y := by
    rw [preInner, preInner, _root_.map_add, _root_.map_mul, RCLike.conj_ofReal, inner_conj_symm,
      inner_conj_symm, hS.isFormalAdjoint x.toDomain y.toDomain]
  re_inner_nonneg x := (sq_nonneg _).trans (norm_sq_le_re_preInner_self hS x)
  add_left x y z := by
    simp only [preInner, toDomain_add, LinearPMap.map_add, Submodule.coe_add, inner_add_left]
    ring
  smul_left x y r := by
    simp only [preInner, toDomain_smul, LinearPMap.map_smul, Submodule.coe_smul, inner_smul_left]
    ring

instance instSeminormedAddCommGroup : SeminormedAddCommGroup (FriedrichsPre S γ hS) :=
  InnerProductSpace.Core.toSeminormedAddCommGroup (c := preInnerCore hS)

instance instInnerProductSpace : InnerProductSpace 𝕜 (FriedrichsPre S γ hS) :=
  InnerProductSpace.ofCore (preInnerCore hS)

/-- The inner product of `FriedrichsPre` is the form inner product. -/
theorem inner_def (x y : FriedrichsPre S γ hS) :
    ⟪x, y⟫_𝕜 = ⟪S x.toDomain, (y.toDomain : E)⟫_𝕜 +
      ((1 - γ : ℝ) : 𝕜) * ⟪(x.toDomain : E), (y.toDomain : E)⟫_𝕜 :=
  rfl

/-- The norm of `E` is dominated by the form norm. -/
theorem norm_toDomain_le (x : FriedrichsPre S γ hS) : ‖(x.toDomain : E)‖ ≤ ‖x‖ := by
  refine le_of_sq_le_sq ?_ (norm_nonneg _)
  have h : ‖x‖ ^ 2 = RCLike.re (preInner hS x x) := @norm_sq_eq_re_inner 𝕜 _ _ _ _ x
  exact h ▸ norm_sq_le_re_preInner_self hS x

/-- The inclusion of `FriedrichsPre` into `E`, a contraction. -/
def inclusion : FriedrichsPre S γ hS →L[𝕜] E :=
  LinearMap.mkContinuous (S.domain.subtype ∘ₗ (linearEquivDomain hS).toLinearMap) 1 fun x => by
    simpa using norm_toDomain_le hS x

/-- `FriedrichsPre.inclusion` sends `x` to its underlying vector. -/
@[simp]
theorem inclusion_apply (x : FriedrichsPre S γ hS) : inclusion hS x = x.toDomain :=
  rfl

end FriedrichsPre

/-! ### The form completion -/

variable (S γ) in
/-- The **form domain** of the Friedrichs extension: the completion of the domain of `S` in the
form norm `(re ⟪S x, x⟫_𝕜 + (1 - γ) * ‖x‖ ^ 2) ^ (1 / 2)`. -/
abbrev FriedrichsSpace (hS : S.IsSymmetricBoundedBelow γ) : Type _ :=
  UniformSpace.Completion (FriedrichsPre S γ hS)

variable (hS : S.IsSymmetricBoundedBelow γ)

/-- The image of a vector of the domain of `S` in the form completion. -/
def toFriedrichsSpace (x : S.domain) : FriedrichsSpace S γ hS :=
  (FriedrichsPre.ofDomain x : FriedrichsPre S γ hS)

/-- The inner product of the form completion on vectors of the domain of `S`. -/
theorem inner_toFriedrichsSpace (x y : S.domain) :
    ⟪toFriedrichsSpace hS x, toFriedrichsSpace hS y⟫_𝕜 =
      ⟪S x, (y : E)⟫_𝕜 + ((1 - γ : ℝ) : 𝕜) * ⟪(x : E), (y : E)⟫_𝕜 := by
  rw [toFriedrichsSpace, toFriedrichsSpace, UniformSpace.Completion.inner_coe,
    FriedrichsPre.inner_def]

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

/-- `friedrichsInclusion` restricts to the inclusion of the domain of `S`. -/
@[simp]
theorem friedrichsInclusion_toFriedrichsSpace (x : S.domain) :
    friedrichsInclusion hS (toFriedrichsSpace hS x) = x := by
  rw [friedrichsInclusion, toFriedrichsSpace, ContinuousLinearMap.fromCompletion_apply_coe,
    FriedrichsPre.inclusion_apply]

/-- The inclusion of the form completion is a contraction. -/
theorem norm_friedrichsInclusion_apply_le (u : FriedrichsSpace S γ hS) :
    ‖friedrichsInclusion hS u‖ ≤ ‖u‖ := by
  induction u using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_le (by fun_prop) continuous_norm
  | ih x =>
    rw [friedrichsInclusion, ContinuousLinearMap.fromCompletion_apply_coe,
      UniformSpace.Completion.norm_coe]
    exact FriedrichsPre.norm_toDomain_le hS x

/-- The form inner product against a vector of the domain of `S` is computed in `E`:
`⟪u, x⟫_S = ⟪j u, S x + (1 - γ) • x⟫_𝕜`. -/
theorem inner_toFriedrichsSpace_right (u : FriedrichsSpace S γ hS) (x : S.domain) :
    ⟪u, toFriedrichsSpace hS x⟫_𝕜 =
      ⟪friedrichsInclusion hS u, S x + ((1 - γ : ℝ) : 𝕜) • (x : E)⟫_𝕜 := by
  induction u using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih y =>
    have h := inner_toFriedrichsSpace hS y.toDomain x
    rw [toFriedrichsSpace] at h
    rw [h, friedrichsInclusion, ContinuousLinearMap.fromCompletion_apply_coe,
      FriedrichsPre.inclusion_apply, inner_add_right, inner_smul_right,
      hS.isFormalAdjoint y.toDomain x]

/-- **Closability of the form of `S`** (Teschl, Lemma 2.10): the inclusion of the form completion
into `E` is injective. -/
theorem injective_friedrichsInclusion : Function.Injective (friedrichsInclusion hS) := by
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

/-- The closed form extends the form of `S`: `q(x, v) = ⟪S x, j v⟫_𝕜` for `x` in the domain of `S`
and every `v` in the form completion. -/
theorem friedrichsForm_toFriedrichsSpace_left (x : S.domain) (v : FriedrichsSpace S γ hS) :
    friedrichsForm hS (toFriedrichsSpace hS x) v = ⟪S x, friedrichsInclusion hS v⟫_𝕜 := by
  rw [friedrichsForm_apply, ← inner_conj_symm, inner_toFriedrichsSpace_right,
    friedrichsInclusion_toFriedrichsSpace, inner_conj_symm, inner_add_left, inner_smul_left,
    RCLike.conj_ofReal, RCLike.ofReal_sub, RCLike.ofReal_sub, RCLike.ofReal_one]
  ring

/-- The closed form of the Friedrichs extension is Hermitian. -/
theorem friedrichsForm_eq_star (u v : FriedrichsSpace S γ hS) :
    friedrichsForm hS u v = star (friedrichsForm hS v u) :=
  ContinuousLinearMap.shiftedForm_eq_star _
    (fun u v => by rw [innerSL_apply_apply, innerSL_apply_apply, RCLike.star_def,
      inner_conj_symm]) _ u v

/-- The closed form of the Friedrichs extension is coercive after shifting by `1 - γ`. -/
theorem norm_sq_le_re_friedrichsForm (u : FriedrichsSpace S γ hS) :
    1 * ‖u‖ ^ 2 ≤
      RCLike.re (friedrichsForm hS u u) + (1 - γ) * ‖friedrichsInclusion hS u‖ ^ 2 := by
  rw [friedrichsForm, ContinuousLinearMap.re_shiftedForm_self, innerSL_apply_apply,
    inner_self_eq_norm_sq]
  linarith

/-- The closed form of the Friedrichs extension is bounded below by `γ`. -/
theorem mul_norm_sq_le_re_friedrichsForm (u : FriedrichsSpace S γ hS) :
    γ * ‖friedrichsInclusion hS u‖ ^ 2 ≤ RCLike.re (friedrichsForm hS u u) := by
  rw [friedrichsForm, ContinuousLinearMap.re_shiftedForm_self, innerSL_apply_apply,
    inner_self_eq_norm_sq]
  have h := norm_friedrichsInclusion_apply_le hS u
  have h0 := norm_nonneg (friedrichsInclusion hS u)
  nlinarith

/-! ### The Friedrichs extension -/

/-- The **Friedrichs extension** of a densely defined symmetric operator `S` with lower bound `γ`:
the self-adjoint operator represented by the closure of the form `⟪S x, y⟫_𝕜`. -/
def friedrichsExtension (hdense : Dense (S.domain : Set E)) : E →ₗ.[𝕜] E :=
  (friedrichsInclusion hS).closedFormOperator (injective_friedrichsInclusion hS)
    (denseRange_friedrichsInclusion hS hdense) (friedrichsForm hS)

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
      (norm_sq_le_re_friedrichsForm hS))

/-- The Friedrichs extension extends `S`. -/
theorem le_friedrichsExtension (hdense : Dense (S.domain : Set E)) :
    S ≤ friedrichsExtension hS hdense := by
  refine le_of_le_graph fun p hp => ?_
  obtain ⟨x, hx, hSx⟩ := (mem_graph_iff S).mp hp
  rw [← Prod.mk.eta (p := p), ← hx, ← hSx]
  exact (mem_graph_friedrichsExtension_iff hS hdense).mpr
    ⟨toFriedrichsSpace hS x, friedrichsInclusion_toFriedrichsSpace hS x,
      friedrichsForm_toFriedrichsSpace_left hS x⟩

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

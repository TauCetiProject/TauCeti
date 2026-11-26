/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.LinearMap.DivisionRing
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Module.Equiv.Basic

/-!
# Basic facts about continuous linear maps

A commutative square of continuous (semi)linear maps between topological modules is also a
commutative square of the underlying (semi)linear maps. This lets results about commuting squares
of linear maps, such as the module snake lemma, be applied to continuous linear maps.

Precomposing with a continuous linear equivalence does not change whether a continuous linear map
vanishes. A continuous semilinear map whose scalar ring homomorphism is surjective vanishes exactly
when the submodule range of its underlying semilinear map is trivial.

A continuous linear map out of `κ → R`, with `κ` finite, is determined by its values on the
coordinate vectors `Pi.single k 1`, and expands as `f x = ∑ k, x k • f (Pi.single k 1)`.

A semilinear family `μ : M₁ →ₛₗ[σ₁₃] M₂ →SL[σ₂₃] M₃` of continuous semilinear maps becomes a
family of semilinear maps after composing with the coercion `ContinuousLinearMap.coeLMₛₗ`, and
then Mathlib's algebraic flip `LinearMap.flip` applies to it.

## Main results

* `ContinuousLinearMap.toLinearMap_comp_eq`: a commutative square of continuous semilinear maps
  commutes after coercion to semilinear maps.
* `ContinuousLinearMap.comp_continuousLinearEquiv_eq_zero_iff`: `L ∘ e = 0` exactly when `L = 0`,
  for a continuous semilinear equivalence `e`.
* `ContinuousLinearMap.range_toLinearMap_eq_bot`: for a surjective scalar ring homomorphism, a
  continuous semilinear map is zero exactly when the submodule range of its underlying semilinear
  map is `⊥`.
* `ContinuousLinearMap.surjective_iff_ne_zero`: a continuous linear functional is surjective
  exactly when it is nonzero.
* `ContinuousLinearMap.pi_ext_single_one`: a continuous linear map out of `κ → R`, `κ` finite, is
  determined by its values on the coordinate vectors.
* `ContinuousLinearMap.eqRec_section`: transporting a dependent section of continuous semilinear
  maps along an equality of image base points recovers the target value when the base points agree.
* `ContinuousLinearMap.eqRec_eqRec`: transporting both the domain and codomain fibres of a
  continuous semilinear map along equalities `a = b` agrees with diagonal transport.
* `ContinuousLinearMap.apply_eq_sum_smul_single`: the expansion
  `f x = ∑ k, x k • f (Pi.single k 1)` of such a map in the coordinate vectors.
* `ContinuousLinearMap.units_inv_apply_apply`, `ContinuousLinearMap.units_apply_inv_apply`: a
  unit continuous linear endomorphism and its inverse undo each other pointwise.
* `ContinuousLinearMap.mul_self_eq_neg_one_iff_comp_eq_neg_id`: `A * A = -1` in the ring of
  continuous linear endomorphisms is `A ∘ A = -id`.
* `LinearMap.flip_coeLMₛₗ_comp_apply`: evaluation of the algebraic flip of such a family `μ`,
  `((ContinuousLinearMap.coeLMₛₗ σ₂₃).comp μ).flip y x = μ x y`.
-/

public section

namespace ContinuousLinearMap

variable {R₁ R₂ R₃ R₄ : Type*} [Semiring R₁] [Semiring R₂] [Semiring R₃] [Semiring R₄]
  {σ₁₂ : R₁ →+* R₂} {σ₁₃ : R₁ →+* R₃} {σ₂₄ : R₂ →+* R₄} {σ₃₄ : R₃ →+* R₄} {σ₁₄ : R₁ →+* R₄}
  [RingHomCompTriple σ₁₂ σ₂₄ σ₁₄] [RingHomCompTriple σ₁₃ σ₃₄ σ₁₄]
  {M₁ M₂ M₃ M₄ : Type*}
  [TopologicalSpace M₁] [AddCommMonoid M₁] [Module R₁ M₁]
  [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R₂ M₂]
  [TopologicalSpace M₃] [AddCommMonoid M₃] [Module R₃ M₃]
  [TopologicalSpace M₄] [AddCommMonoid M₄] [Module R₄ M₄]

/-- A commutative square of continuous semilinear maps commutes as a square of semilinear
maps. -/
theorem toLinearMap_comp_eq {f : M₁ →SL[σ₁₂] M₂} {g : M₃ →SL[σ₃₄] M₄} {i : M₁ →SL[σ₁₃] M₃}
    {i' : M₂ →SL[σ₂₄] M₄} (h : g ∘SL i = i' ∘SL f) :
    (g : M₃ →ₛₗ[σ₃₄] M₄) ∘ₛₗ (i : M₁ →ₛₗ[σ₁₃] M₃) =
      (i' : M₂ →ₛₗ[σ₂₄] M₄) ∘ₛₗ (f : M₁ →ₛₗ[σ₁₂] M₂) := by
  rw [← toLinearMap_comp, h, toLinearMap_comp]

/-- Precomposing with a continuous semilinear equivalence gives the zero map exactly when the
original map is zero. -/
theorem comp_continuousLinearEquiv_eq_zero_iff {σ₂₁ : R₂ →+* R₁} [RingHomInvPair σ₁₂ σ₂₁]
    [RingHomInvPair σ₂₁ σ₁₂] (L : M₂ →SL[σ₂₄] M₄)
    (e : M₁ ≃SL[σ₁₂] M₂) : L.comp (e : M₁ →SL[σ₁₂] M₂) = 0 ↔ L = 0 := by
  refine ⟨fun h ↦ ext fun v ↦ ?_, fun h ↦ by rw [h, zero_comp]⟩
  simpa using congr($h (e.symm v))

/-- A continuous semilinear map `f`, along a surjective scalar ring homomorphism `σ₁₂`, is the
zero map exactly when the submodule range of its underlying semilinear map is `⊥`. Surjectivity of
`σ₁₂` is what makes `LinearMap.range` a submodule of the target. -/
@[simp]
theorem range_toLinearMap_eq_bot [RingHomSurjective σ₁₂] {f : M₁ →SL[σ₁₂] M₂} :
    (f : M₁ →ₛₗ[σ₁₂] M₂).range = ⊥ ↔ f = 0 := by
  rw [LinearMap.range_eq_bot, ← toLinearMap_zero, coe_inj]

/-- A continuous linear functional with values in a division semiring is surjective exactly when
it is nonzero. -/
theorem surjective_iff_ne_zero {R M : Type*} [DivisionSemiring R] [TopologicalSpace R]
    [TopologicalSpace M] [AddCommMonoid M] [Module R M] {f : M →L[R] R} :
    Function.Surjective f ↔ f ≠ 0 :=
  LinearMap.surjective_iff_ne_zero.trans (not_congr (coe_inj (g := 0)))

/-- A continuous linear map out of `κ → R`, with `κ` finite, is determined by its values on the
coordinate vectors `Pi.single k 1`. -/
theorem pi_ext_single_one {R M κ : Type*} [Semiring R] [TopologicalSpace R] [TopologicalSpace M]
    [AddCommMonoid M] [Module R M] [Finite κ] [DecidableEq κ] {f g : (κ → R) →L[R] M}
    (h : ∀ k, f (Pi.single k 1) = g (Pi.single k 1)) : f = g :=
  coe_injective <| LinearMap.pi_ext' fun k ↦ LinearMap.ext_ring <| h k

/-- Transporting the value at `a'` of a dependent section `s : ∀ x, V (p x) →SL[σ] W (p x)` along
`hp : p a' = p a` recovers `s a` whenever `a' = a`. -/
theorem eqRec_section {R₁ R₂ α β : Type*} [Semiring R₁] [Semiring R₂] {σ : R₁ →+* R₂}
    {V W : β → Type*} [∀ b, TopologicalSpace (V b)] [∀ b, AddCommMonoid (V b)]
    [∀ b, Module R₁ (V b)] [∀ b, TopologicalSpace (W b)] [∀ b, AddCommMonoid (W b)]
    [∀ b, Module R₂ (W b)] {p : α → β} {a' a : α} (ha : a' = a) (hp : p a' = p a)
    (s : ∀ x, V (p x) →SL[σ] W (p x)) :
    (show V (p a) →SL[σ] W (p a) from hp ▸ s a') = s a := by
  cases ha
  rfl

/-- Transporting both the domain and codomain fibres of a continuous semilinear map along equalities
`hx hy : a = b` agrees with transporting the map type along `hx`. -/
theorem eqRec_eqRec {R₁ R₂ β : Type*} [Semiring R₁] [Semiring R₂] {σ : R₁ →+* R₂}
    {V W : β → Type*} [∀ b, TopologicalSpace (V b)] [∀ b, AddCommMonoid (V b)]
    [∀ b, Module R₁ (V b)] [∀ b, TopologicalSpace (W b)] [∀ b, AddCommMonoid (W b)]
    [∀ b, Module R₂ (W b)] {a b : β} (hx hy : a = b) (T : V a →SL[σ] W a) :
    (show V b →SL[σ] W b from
      @Eq.rec β a (fun x _ ↦ V x →SL[σ] W b)
        (@Eq.rec β a (fun y _ ↦ V a →SL[σ] W y) T b hy) b hx) =
      (show V b →SL[σ] W b from hx ▸ T) := by
  cases hx
  rfl

/-- A continuous linear map out of `κ → R`, with `κ` finite, expanded in the coordinate vectors:
`f x = ∑ k, x k • f (Pi.single k 1)`. -/
theorem apply_eq_sum_smul_single {R M κ : Type*} [Semiring R] [TopologicalSpace R]
    [TopologicalSpace M] [AddCommMonoid M] [Module R M] [Fintype κ] [DecidableEq κ]
    (f : (κ → R) →L[R] M) (x : κ → R) : f x = ∑ k, x k • f (Pi.single k 1) := by
  conv_lhs => rw [pi_eq_sum_univ' x]
  simp [map_sum]

/-- Applying the inverse of a unit continuous linear endomorphism undoes applying the unit. -/
@[simp]
theorem units_inv_apply_apply (u : (M₁ →L[R₁] M₁)ˣ) (x : M₁) :
    (↑u⁻¹ : M₁ →L[R₁] M₁) ((u : M₁ →L[R₁] M₁) x) = x := by
  rw [← mul_apply_eq_comp, Units.inv_mul, one_apply_eq_self]

/-- Applying a unit continuous linear endomorphism undoes applying its inverse. -/
@[simp]
theorem units_apply_inv_apply (u : (M₁ →L[R₁] M₁)ˣ) (x : M₁) :
    (u : M₁ →L[R₁] M₁) ((↑u⁻¹ : M₁ →L[R₁] M₁) x) = x := by
  rw [← mul_apply_eq_comp, Units.mul_inv, one_apply_eq_self]

/-- `A * A = -1` in the ring of continuous linear endomorphisms is `A ∘ A = -id`. -/
theorem mul_self_eq_neg_one_iff_comp_eq_neg_id {R M : Type*} [Ring R] [TopologicalSpace M]
    [AddCommGroup M] [Module R M] [IsTopologicalAddGroup M] {A : M →L[R] M} :
    A * A = -1 ↔ A.comp A = -ContinuousLinearMap.id R M := by
  rw [mul_def, one_def]

end ContinuousLinearMap

namespace LinearMap

variable {R₁ R₂ R₃ : Type*} [Semiring R₁] [Semiring R₂] [Semiring R₃]
  {σ₁₃ : R₁ →+* R₃} {σ₂₃ : R₂ →+* R₃} {M₁ M₂ M₃ : Type*}
  [AddCommMonoid M₁] [Module R₁ M₁]
  [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R₂ M₂]
  [TopologicalSpace M₃] [AddCommMonoid M₃] [Module R₃ M₃] [ContinuousAdd M₃]
  [ContinuousConstSMul R₃ M₃] [SMulCommClass R₃ R₃ M₃]

/-- Evaluation of the algebraic flip of a semilinear family `μ` of continuous semilinear maps,
with each `μ x` viewed as a semilinear map through `ContinuousLinearMap.coeLMₛₗ`: it sends `y`
and then `x` to `μ x y`. -/
theorem flip_coeLMₛₗ_comp_apply (μ : M₁ →ₛₗ[σ₁₃] M₂ →SL[σ₂₃] M₃) (y : M₂) (x : M₁) :
    ((ContinuousLinearMap.coeLMₛₗ σ₂₃).comp μ).flip y x = μ x y := by
  rw [flip_apply, comp_apply, ContinuousLinearMap.coeLMₛₗ_apply, ContinuousLinearMap.coe_coe]

end LinearMap

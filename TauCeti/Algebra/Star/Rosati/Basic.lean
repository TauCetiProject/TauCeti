/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Algebra.Star.Module
public import Mathlib.Algebra.Star.StarAlgHom
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import TauCeti.Algebra.Star.SelfAdjoint.LinearMap

/-!
# Rosati positivity, the Rosati inner product, and the left-regular representation

Defines `TauCeti.IsRosatiPositive` and its cone, unit, and transport properties, and constructs
the inner product `TauCeti.rosatiInnerProductCore` and inner product space `TauCeti.RosatiSpace`
(when `E` satisfies `[NonUnitalNonAssocRing E] [Module ℝ E] [IsScalarTower ℝ E E] [StarRing E]`
and `t : E →ₗ[ℝ] ℝ` is star-invariant and strictly positive on `x * star x`) and the faithful
star regular representation `TauCeti.rosatiRegularRepresentation` (when `E` is a finite-dimensional
real star algebra and `t` is cyclic).

## References

* J. Voight, *Quaternion Algebras*, GTM 288, Springer (2021), §8.4.
* M. Lipnowski and J. Tsimerman, *How large is A_g(F_q)?*, arXiv:1511.02212v1, §4.3.2.
-/

public section

open scoped InnerProductSpace

namespace TauCeti

section IsRosatiPositive

variable {E : Type*}

/-- An element `s` of a real star algebra is **Rosati-positive** with respect to a linear
functional `t : E →ₗ[ℝ] ℝ` if `s` is self-adjoint and `t (s * x * star x) > 0` for all
`x ≠ 0`. -/
def IsRosatiPositive [AddCommMonoid E] [Mul E] [Module ℝ E] [Star E] (t : E →ₗ[ℝ] ℝ)
    (s : E) : Prop :=
  IsSelfAdjoint s ∧ ∀ x : E, x ≠ 0 → 0 < t (s * x * star x)

theorem isRosatiPositive_iff [AddCommMonoid E] [Mul E] [Module ℝ E] [Star E]
    {t : E →ₗ[ℝ] ℝ} {s : E} :
    IsRosatiPositive t s ↔ IsSelfAdjoint s ∧ ∀ x : E, x ≠ 0 → 0 < t (s * x * star x) :=
  Iff.rfl

theorem IsRosatiPositive.isSelfAdjoint [AddCommMonoid E] [Mul E] [Module ℝ E] [Star E]
    {t : E →ₗ[ℝ] ℝ} {s : E} (hs : IsRosatiPositive t s) : IsSelfAdjoint s := hs.1

theorem IsRosatiPositive.apply_mul_mul_star_pos [AddCommMonoid E] [Mul E] [Module ℝ E] [Star E]
    {t : E →ₗ[ℝ] ℝ} {s : E} (hs : IsRosatiPositive t s) {x : E} (hx : x ≠ 0) :
    0 < t (s * x * star x) := hs.2 x hx

/-- The sum of two Rosati-positive elements is Rosati-positive. -/
theorem IsRosatiPositive.add [NonUnitalNonAssocSemiring E] [Module ℝ E] [StarAddMonoid E]
    {t : E →ₗ[ℝ] ℝ} {s₁ s₂ : E} (h₁ : IsRosatiPositive t s₁)
    (h₂ : IsRosatiPositive t s₂) : IsRosatiPositive t (s₁ + s₂) :=
  ⟨h₁.1.add h₂.1, fun x hx ↦ by simpa [add_mul] using add_pos (h₁.2 x hx) (h₂.2 x hx)⟩

/-- A positive real multiple of a Rosati-positive element is Rosati-positive. -/
theorem IsRosatiPositive.smul [AddCommMonoid E] [Mul E] [Module ℝ E] [IsScalarTower ℝ E E]
    [Star E] [StarModule ℝ E] {t : E →ₗ[ℝ] ℝ} {c : ℝ} {s : E} (hc : 0 < c)
    (hs : IsRosatiPositive t s) : IsRosatiPositive t (c • s) :=
  ⟨by rw [IsSelfAdjoint, star_smul, star_trivial, hs.1.star_eq],
    fun x hx ↦ by simpa [smul_mul_assoc, smul_eq_mul] using mul_pos hc (hs.2 x hx)⟩

/-- `1` is Rosati-positive with respect to `t` iff `t (x * star x) > 0` for all `x ≠ 0`. -/
@[simp] theorem isRosatiPositive_one_iff [Semiring E] [Module ℝ E] [StarRing E]
    {t : E →ₗ[ℝ] ℝ} :
    IsRosatiPositive t 1 ↔ ∀ x : E, x ≠ 0 → 0 < t (x * star x) := by
  simp only [IsRosatiPositive, IsSelfAdjoint.one, one_mul, true_and]

/-- For a cyclic trace functional `t`, congruence `s ↦ star u * s * u` by a unit preserves
`IsRosatiPositive`. -/
theorem IsRosatiPositive.star_left_conjugate [Semiring E] [Module ℝ E] [StarRing E]
    {t : E →ₗ[ℝ] ℝ} (hcyc : ∀ x y : E, t (x * y) = t (y * x)) (u : Eˣ) {s : E}
    (hs : IsRosatiPositive t s) : IsRosatiPositive t (star (u : E) * s * u) := by
  refine ⟨by rw [IsSelfAdjoint, star_mul, star_mul, star_star, hs.1.star_eq, mul_assoc],
    fun x hx ↦ ?_⟩
  have hassoc :
      star (u : E) * s * u * x * star x = star (u : E) * (s * ((u : E) * x) * star x) := by
    simp only [mul_assoc]
  rw [hassoc, hcyc]
  simpa only [mul_assoc, star_mul] using
    hs.2 ((u : E) * x) fun h ↦ hx (by simpa using congrArg ((↑u⁻¹ : E) * ·) h)

/-- Every Rosati-positive element of a finite-dimensional real algebra with star is a unit. -/
theorem IsRosatiPositive.isUnit [Ring E] [Algebra ℝ E] [Star E] [Module.Finite ℝ E]
    {t : E →ₗ[ℝ] ℝ} {s : E} (hs : IsRosatiPositive t s) : IsUnit s :=
  Algebra.lmul_isUnit_iff.mp <| (LinearMap.isUnit_iff_ker_eq_bot _).mpr <|
    LinearMap.ker_eq_bot.mpr <| (injective_iff_map_eq_zero (Algebra.lmul ℝ E s)).mpr
      fun x hx ↦ by_contra fun hx0 ↦ (hs.2 x hx0).ne' (by
        simp only [Algebra.coe_lmul_eq_mul, LinearMap.mul_apply'] at hx
        rw [hx, zero_mul, map_zero])

/-- For cyclic `t`, replacing `t` by its star-symmetrization `t' x = (t x + t (star x)) / 2`
leaves `IsRosatiPositive` unchanged. -/
theorem isRosatiPositive_iff_of_symmetrize [Semiring E] [Module ℝ E] [StarRing E]
    {t t' : E →ₗ[ℝ] ℝ} (ht' : ∀ x : E, t' x = (t x + t (star x)) / 2)
    (hcyc : ∀ x y : E, t (x * y) = t (y * x)) {s : E} :
    IsRosatiPositive t' s ↔ IsRosatiPositive t s := by
  refine and_congr_right fun hs ↦ forall₂_congr fun x _ ↦ ?_
  have hst : t (star (s * x * star x)) = t (s * x * star x) := by
    simp only [star_mul, star_star, hs.star_eq]; rw [← mul_assoc, hcyc, mul_assoc]
  rw [ht', hst]; constructor <;> intro h <;> linarith

/-- For cyclic `t : E →ₗ[ℝ] ℝ`, replacing `t` by its star-symmetrization
`(t.comp (selfAdjoint.submodule ℝ E).subtype).comp (selfAdjointPart ℝ)` leaves `IsRosatiPositive`
unchanged. -/
theorem isRosatiPositive_comp_selfAdjointPart_iff [Ring E] [Module ℝ E] [StarRing E]
    [StarModule ℝ E] {t : E →ₗ[ℝ] ℝ} (hcyc : ∀ x y : E, t (x * y) = t (y * x)) {s : E} :
    IsRosatiPositive ((t.comp (selfAdjoint.submodule ℝ E).subtype).comp (selfAdjointPart ℝ)) s ↔
      IsRosatiPositive t s :=
  isRosatiPositive_iff_of_symmetrize
    (fun x ↦ by simpa [div_eq_inv_mul] using LinearMap.comp_selfAdjointPart_apply t x) hcyc

/-- On a finite product of star algebras, `IsRosatiPositive t s` holds iff each coordinate `s i`
is `IsRosatiPositive` for the restricted functional `t.comp (LinearMap.single ℝ B i)`. -/
theorem isRosatiPositive_pi_iff {ι : Type*} [DecidableEq ι] [Finite ι] {B : ι → Type*}
    [∀ i, NonUnitalNonAssocSemiring (B i)] [∀ i, Module ℝ (B i)] [∀ i, StarAddMonoid (B i)]
    (t : (∀ i, B i) →ₗ[ℝ] ℝ) (s : ∀ i, B i) :
    IsRosatiPositive t s ↔ ∀ i : ι, IsRosatiPositive (t.comp (LinearMap.single ℝ B i)) (s i) := by
  cases nonempty_fintype ι
  have hsum (y : ∀ i, B i) :
      t (s * y * star y) = ∑ i : ι, t (Pi.single i (s i * y i * star (y i))) := by
    conv_lhs => rw [← LinearMap.sum_single_apply B (s * y * star y)]
    simp only [Pi.mul_apply, Pi.star_apply, map_sum]
  have hsa : IsSelfAdjoint s ↔ ∀ i : ι, IsSelfAdjoint (s i) := ⟨fun h i ↦ congrFun h i, funext⟩
  rw [isRosatiPositive_iff]; simp only [isRosatiPositive_iff, forall_and, ← hsa]
  refine and_congr_right fun _ ↦ ⟨fun h i a ha ↦ ?_, fun h x hx ↦ ?_⟩
  · have h1 := h (Pi.single i a) fun h0 ↦ ha (by simpa using congrFun h0 i)
    rw [hsum, Finset.sum_eq_single i (fun j _ hji ↦ by simp [Pi.single_eq_of_ne hji])
      (fun hi ↦ absurd (Finset.mem_univ i) hi)] at h1
    simpa [LinearMap.single_apply] using h1
  · rw [hsum]; obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hx
    refine Finset.sum_pos' (fun i _ ↦ ?_) ⟨i₀, Finset.mem_univ i₀, h i₀ (x i₀) hi₀⟩
    rcases eq_or_ne (x i) 0 with h0 | hne <;> [simp [h0]; exact (h i (x i) hne).le]

end IsRosatiPositive

section InnerProduct

section Core

variable {E : Type*} [NonUnitalNonAssocRing E] [Module ℝ E] [IsScalarTower ℝ E E] [StarRing E]

/-- The positive definite real inner product `⟪x, y⟫ = t (x * star y)` determined by a
star-invariant linear functional `t : E →ₗ[ℝ] ℝ` strictly positive on `x * star x`. -/
abbrev rosatiInnerProductCore (t : E →ₗ[ℝ] ℝ) (hstar : ∀ x : E, t (star x) = t x)
    (hpos : ∀ x : E, x ≠ 0 → 0 < t (x * star x)) : InnerProductSpace.Core ℝ E where
  inner x y := t (x * star y)
  conj_inner_symm x y := by simp [← hstar (x * star y)]
  re_inner_nonneg x := by rcases eq_or_ne x 0 with rfl | hx <;> [simp; exact (hpos x hx).le]
  add_left x y z := by rw [add_mul, map_add]
  smul_left x y r := by simp [smul_mul_assoc]
  definite x hx := by_contra fun hne ↦ (hpos x hne).ne' hx

@[simp] theorem rosatiInnerProductCore_inner (t : E →ₗ[ℝ] ℝ)
    (hstar : ∀ x : E, t (star x) = t x) (hpos : ∀ x : E, x ≠ 0 → 0 < t (x * star x)) (x y : E) :
    (rosatiInnerProductCore t hstar hpos).inner x y = t (x * star y) := rfl

end Core

/-- Type synonym for `E`. When `[NonUnitalNonAssocRing E] [Module ℝ E] [IsScalarTower ℝ E E]`
`[StarRing E]` holds and `t : E →ₗ[ℝ] ℝ` is star-invariant and strictly positive on `x * star x`,
`RosatiSpace t hstar hpos` carries the real inner product `⟪x, y⟫_ℝ = t (x * star y)`. -/
structure RosatiSpace {E : Type*} [AddCommMonoid E] [Mul E] [Module ℝ E] [Star E]
    (t : E →ₗ[ℝ] ℝ) (_hstar : ∀ x : E, t (star x) = t x)
    (_hpos : ∀ x : E, x ≠ 0 → 0 < t (x * star x)) : Type _ where
  /-- The underlying element of `E`. -/
  val : E

namespace RosatiSpace

section Instances

variable {E : Type*} [AddCommGroup E] [Mul E] [Module ℝ E] [Star E]

instance (t : E →ₗ[ℝ] ℝ) (hstar : ∀ x : E, t (star x) = t x)
    (hpos : ∀ x : E, x ≠ 0 → 0 < t (x * star x)) :
    AddCommGroup (RosatiSpace t hstar hpos) :=
  Equiv.addCommGroup
    { toFun := val, invFun := mk, left_inv := fun _ ↦ rfl, right_inv := fun _ ↦ rfl }

instance (t : E →ₗ[ℝ] ℝ) (hstar : ∀ x : E, t (star x) = t x)
    (hpos : ∀ x : E, x ≠ 0 → 0 < t (x * star x)) :
    Module ℝ (RosatiSpace t hstar hpos) :=
  AddEquiv.module ℝ
    ({ toFun := val, invFun := mk, left_inv := fun _ ↦ rfl, right_inv := fun _ ↦ rfl,
       map_add' := fun _ _ ↦ rfl } : RosatiSpace t hstar hpos ≃+ E)

/-- The canonical `ℝ`-linear equivalence identifying `E` with `TauCeti.RosatiSpace t hstar hpos`. -/
def of (t : E →ₗ[ℝ] ℝ) (hstar : ∀ x : E, t (star x) = t x)
    (hpos : ∀ x : E, x ≠ 0 → 0 < t (x * star x)) :
    E ≃ₗ[ℝ] RosatiSpace t hstar hpos where
  toFun := mk
  invFun := val
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

instance [FiniteDimensional ℝ E] (t : E →ₗ[ℝ] ℝ) (hstar : ∀ x : E, t (star x) = t x)
    (hpos : ∀ x : E, x ≠ 0 → 0 < t (x * star x)) :
    FiniteDimensional ℝ (RosatiSpace t hstar hpos) :=
  (of t hstar hpos).finiteDimensional

end Instances

section Inner

variable {E : Type*} [NonUnitalNonAssocRing E] [Module ℝ E] [IsScalarTower ℝ E E] [StarRing E]

noncomputable instance (t : E →ₗ[ℝ] ℝ) (hstar : ∀ x : E, t (star x) = t x)
    (hpos : ∀ x : E, x ≠ 0 → 0 < t (x * star x)) :
    NormedAddCommGroup (RosatiSpace t hstar hpos) :=
  let c := rosatiInnerProductCore t hstar hpos
  let core : InnerProductSpace.Core ℝ (RosatiSpace t hstar hpos) :=
    { inner x y := c.inner x.val y.val
      conj_inner_symm _ _ := c.conj_inner_symm _ _
      re_inner_nonneg _ := c.re_inner_nonneg _
      add_left _ _ _ := c.add_left _ _ _
      smul_left _ _ r := c.smul_left _ _ r
      definite x hx := by cases x; exact congrArg mk (c.definite _ hx) }
  core.toNormedAddCommGroup

noncomputable instance (t : E →ₗ[ℝ] ℝ) (hstar : ∀ x : E, t (star x) = t x)
    (hpos : ∀ x : E, x ≠ 0 → 0 < t (x * star x)) :
    InnerProductSpace ℝ (RosatiSpace t hstar hpos) :=
  let c := rosatiInnerProductCore t hstar hpos
  InnerProductSpace.ofCore
    { inner x y := c.inner (RosatiSpace.val x) (RosatiSpace.val y)
      conj_inner_symm _ _ := c.conj_inner_symm _ _
      re_inner_nonneg _ := c.re_inner_nonneg _
      add_left _ _ _ := c.add_left _ _ _
      smul_left _ _ r := c.smul_left _ _ r }

/-- Evaluation of the inner product on `TauCeti.RosatiSpace` via `TauCeti.RosatiSpace.of`. -/
@[simp] theorem inner_of (t : E →ₗ[ℝ] ℝ) (hstar : ∀ x : E, t (star x) = t x)
    (hpos : ∀ x : E, x ≠ 0 → 0 < t (x * star x)) (x y : E) :
    ⟪of t hstar hpos x, of t hstar hpos y⟫_ℝ = t (x * star y) := (rfl)

/-- Evaluation of the squared norm on `TauCeti.RosatiSpace` via `TauCeti.RosatiSpace.of`. -/
@[simp] theorem norm_sq_of (t : E →ₗ[ℝ] ℝ) (hstar : ∀ x : E, t (star x) = t x)
    (hpos : ∀ x : E, x ≠ 0 → 0 < t (x * star x)) (x : E) :
    ‖of t hstar hpos x‖ ^ 2 = t (x * star x) := by
  rw [← real_inner_self_eq_norm_sq, inner_of]

/-- Evaluation of the inner product on `TauCeti.RosatiSpace`. -/
theorem inner_def (t : E →ₗ[ℝ] ℝ) (hstar : ∀ x : E, t (star x) = t x)
    (hpos : ∀ x : E, x ≠ 0 → 0 < t (x * star x)) (x y : RosatiSpace t hstar hpos) :
    ⟪x, y⟫_ℝ = t ((of t hstar hpos).symm x * star ((of t hstar hpos).symm y)) := (rfl)

end Inner

section Lmul

variable {E : Type*} [Ring E] [Algebra ℝ E] [Star E]

/-- Left multiplication by elements of `E` acting as `ℝ`-linear endomorphisms on
`TauCeti.RosatiSpace t hstar hpos`. -/
def lmul (t : E →ₗ[ℝ] ℝ) (hstar : ∀ x : E, t (star x) = t x)
    (hpos : ∀ x : E, x ≠ 0 → 0 < t (x * star x)) :
    E →ₐ[ℝ] (RosatiSpace t hstar hpos →ₗ[ℝ] RosatiSpace t hstar hpos) where
  toFun s :=
    (of t hstar hpos).toLinearMap.comp
      ((Algebra.lmul ℝ E s).comp (of t hstar hpos).symm.toLinearMap)
  map_one' := by ext x; simp
  map_mul' a b := by ext x; simp [mul_assoc]
  map_zero' := by ext x; simp
  map_add' a b := by ext x; simp
  commutes' r := by ext x; simp

/-- Evaluation of `TauCeti.RosatiSpace.lmul` on `TauCeti.RosatiSpace.of`. -/
@[simp] theorem lmul_apply (t : E →ₗ[ℝ] ℝ) (hstar : ∀ x : E, t (star x) = t x)
    (hpos : ∀ x : E, x ≠ 0 → 0 < t (x * star x)) (s x : E) :
    lmul t hstar hpos s (of t hstar hpos x) = of t hstar hpos (s * x) := (rfl)

/-- `TauCeti.RosatiSpace.lmul` is injective. -/
theorem lmul_injective (t : E →ₗ[ℝ] ℝ) (hstar : ∀ x : E, t (star x) = t x)
    (hpos : ∀ x : E, x ≠ 0 → 0 < t (x * star x)) :
    Function.Injective (lmul t hstar hpos) :=
  fun _ _ h ↦ by
    simpa using (of t hstar hpos).injective
      (by simpa using LinearMap.congr_fun h (of t hstar hpos 1))

end Lmul

end RosatiSpace

variable {E : Type*} [Ring E] [Algebra ℝ E] [StarRing E]

/-- Left multiplication by `s` has `star s` as its formal adjoint on `TauCeti.RosatiSpace`
whenever `t` is cyclic. -/
theorem inner_lmul_left (t : E →ₗ[ℝ] ℝ) (hcyc : ∀ x y : E, t (x * y) = t (y * x))
    (hstar : ∀ x : E, t (star x) = t x) (hpos : ∀ x : E, x ≠ 0 → 0 < t (x * star x))
    (s : E) (x y : RosatiSpace t hstar hpos) :
    ⟪RosatiSpace.lmul t hstar hpos s x, y⟫_ℝ =
      ⟪x, RosatiSpace.lmul t hstar hpos (star s) y⟫_ℝ := by
  obtain ⟨x, rfl⟩ := (RosatiSpace.of t hstar hpos).surjective x
  obtain ⟨y, rfl⟩ := (RosatiSpace.of t hstar hpos).surjective y
  simp only [RosatiSpace.lmul_apply, RosatiSpace.inner_of, star_mul, star_star, mul_assoc]
  rw [hcyc s (x * star y), mul_assoc]

/-- In finite dimension, when `t` is cyclic, the Hilbert-space adjoint of
`TauCeti.RosatiSpace.lmul t hstar hpos s` on `TauCeti.RosatiSpace` is
`TauCeti.RosatiSpace.lmul t hstar hpos (star s)`. -/
@[simp] theorem adjoint_lmul_eq_lmul_star [FiniteDimensional ℝ E] (t : E →ₗ[ℝ] ℝ)
    (hcyc : ∀ x y : E, t (x * y) = t (y * x)) (hstar : ∀ x : E, t (star x) = t x)
    (hpos : ∀ x : E, x ≠ 0 → 0 < t (x * star x)) (s : E) :
    (RosatiSpace.lmul t hstar hpos s).adjoint = RosatiSpace.lmul t hstar hpos (star s) :=
  ((LinearMap.eq_adjoint_iff (RosatiSpace.lmul t hstar hpos (star s))
    (RosatiSpace.lmul t hstar hpos s)).mpr
      fun x y ↦ by simpa only [star_star] using inner_lmul_left t hcyc hstar hpos (star s) x y).symm

/-- When `t` is cyclic, the left-regular representation as a faithful star algebra homomorphism
from `E` into the endomorphisms of `TauCeti.RosatiSpace t hstar hpos`. -/
noncomputable def rosatiRegularRepresentation [FiniteDimensional ℝ E]
    (t : E →ₗ[ℝ] ℝ) (hcyc : ∀ x y : E, t (x * y) = t (y * x))
    (hstar : ∀ x : E, t (star x) = t x) (hpos : ∀ x : E, x ≠ 0 → 0 < t (x * star x)) :
    E →⋆ₐ[ℝ] (RosatiSpace t hstar hpos →ₗ[ℝ] RosatiSpace t hstar hpos) :=
  { RosatiSpace.lmul t hstar hpos with
    map_star' := fun s ↦ ((LinearMap.star_eq_adjoint (RosatiSpace.lmul t hstar hpos s)).trans
      (adjoint_lmul_eq_lmul_star t hcyc hstar hpos s)).symm }

/-- Evaluation of `TauCeti.rosatiRegularRepresentation` as `TauCeti.RosatiSpace.lmul`. -/
@[simp] theorem rosatiRegularRepresentation_apply [FiniteDimensional ℝ E] (t : E →ₗ[ℝ] ℝ)
    (hcyc : ∀ x y : E, t (x * y) = t (y * x)) (hstar : ∀ x : E, t (star x) = t x)
    (hpos : ∀ x : E, x ≠ 0 → 0 < t (x * star x)) (s : E) :
    rosatiRegularRepresentation t hcyc hstar hpos s = RosatiSpace.lmul t hstar hpos s := (rfl)

/-- `TauCeti.rosatiRegularRepresentation` is injective. -/
theorem rosatiRegularRepresentation_injective [FiniteDimensional ℝ E] (t : E →ₗ[ℝ] ℝ)
    (hcyc : ∀ x y : E, t (x * y) = t (y * x)) (hstar : ∀ x : E, t (star x) = t x)
    (hpos : ∀ x : E, x ≠ 0 → 0 < t (x * star x)) :
    Function.Injective (rosatiRegularRepresentation t hcyc hstar hpos) :=
  RosatiSpace.lmul_injective t hstar hpos

/-- When `t` is cyclic, left multiplication by `s` is symmetric on `TauCeti.RosatiSpace` iff
`s` is self-adjoint. -/
theorem isSymmetric_lmul_iff (t : E →ₗ[ℝ] ℝ) (hcyc : ∀ x y : E, t (x * y) = t (y * x))
    (hstar : ∀ x : E, t (star x) = t x) (hpos : ∀ x : E, x ≠ 0 → 0 < t (x * star x))
    (s : E) :
    (RosatiSpace.lmul t hstar hpos s).IsSymmetric ↔ IsSelfAdjoint s := by
  refine ⟨fun hsym ↦ (sub_eq_zero.mp ((RosatiSpace.of t hstar hpos).injective
      ((inner_self_eq_zero (𝕜 := ℝ)).mp ?_))).symm,
    fun hs x y ↦ by rw [inner_lmul_left t hcyc hstar hpos s x y, hs.star_eq]⟩
  rw [map_sub, inner_sub_left, sub_eq_zero]
  simpa [RosatiSpace.lmul_apply, mul_one, one_mul] using
    (hsym (RosatiSpace.of t hstar hpos 1) (RosatiSpace.of t hstar hpos (s - star s))).trans
      (by simpa [star_star] using (inner_lmul_left t hcyc hstar hpos (star s)
        (RosatiSpace.of t hstar hpos 1) (RosatiSpace.of t hstar hpos (s - star s))).symm)

/-- When `t` is cyclic, a Rosati-positive element acts as a positive operator on
`TauCeti.RosatiSpace`. -/
theorem isPositive_lmul_of_isRosatiPositive (t : E →ₗ[ℝ] ℝ)
    (hcyc : ∀ x y : E, t (x * y) = t (y * x)) (hstar : ∀ x : E, t (star x) = t x)
    (hpos : ∀ x : E, x ≠ 0 → 0 < t (x * star x)) {s : E} (hs : IsRosatiPositive t s) :
    (RosatiSpace.lmul t hstar hpos s).IsPositive := by
  refine ⟨(isSymmetric_lmul_iff t hcyc hstar hpos s).mpr hs.1, fun x ↦ ?_⟩
  obtain ⟨x, rfl⟩ := (RosatiSpace.of t hstar hpos).surjective x
  rw [RCLike.re_to_real, RosatiSpace.lmul_apply, RosatiSpace.inner_of]
  rcases eq_or_ne x 0 with rfl | hx <;> [simp; exact (hs.2 x hx).le]

/-- When `t` is cyclic, an element whose left-multiplication operator is injective and positive on
`TauCeti.RosatiSpace` is Rosati-positive. -/
theorem isRosatiPositive_of_isPositive_lmul_of_injective (t : E →ₗ[ℝ] ℝ)
    (hcyc : ∀ x y : E, t (x * y) = t (y * x)) (hstar : ∀ x : E, t (star x) = t x)
    (hpos : ∀ x : E, x ≠ 0 → 0 < t (x * star x)) {s : E}
    (hsPos : (RosatiSpace.lmul t hstar hpos s).IsPositive)
    (hinj : Function.Injective (RosatiSpace.lmul t hstar hpos s)) : IsRosatiPositive t s := by
  refine ⟨(isSymmetric_lmul_iff t hcyc hstar hpos s).mp hsPos.isSymmetric, fun x hx ↦ ?_⟩
  have hne : RosatiSpace.of t hstar hpos x ≠ 0 :=
    fun h ↦ hx ((RosatiSpace.of t hstar hpos).injective (by simpa using h))
  refine lt_of_le_of_ne (by simpa [RosatiSpace.lmul_apply, RosatiSpace.inner_of] using
      hsPos.re_inner_nonneg_left (RosatiSpace.of t hstar hpos x)) fun hzero ↦ hne ?_
  let B := (innerₗ (RosatiSpace t hstar hpos)).compl₁₂
    (RosatiSpace.lmul t hstar hpos s) LinearMap.id
  have hzero' : B (RosatiSpace.of t hstar hpos x) (RosatiSpace.of t hstar hpos x) = 0 := by
    simpa [B, RosatiSpace.lmul_apply, RosatiSpace.inner_of] using hzero.symm
  have hlmul0 : RosatiSpace.lmul t hstar hpos s (RosatiSpace.of t hstar hpos x) = 0 :=
    (inner_self_eq_zero (𝕜 := ℝ)).mp (by
      simpa [B] using LinearMap.congr_fun (LinearMap.mem_ker.mp
        ((LinearMap.BilinForm.apply_apply_same_eq_zero_iff B hsPos.re_inner_nonneg_left
          ⟨fun a b ↦ by simpa [B] using (hsPos.isSymmetric a b).trans (real_inner_comm _ _)⟩).mp
          hzero')) (RosatiSpace.lmul t hstar hpos s (RosatiSpace.of t hstar hpos x)))
  exact hinj (by simpa using hlmul0)

/-- When `t` is cyclic, `s` is Rosati-positive iff `TauCeti.RosatiSpace.lmul t hstar hpos s` is
positive and injective on `TauCeti.RosatiSpace`. -/
theorem isRosatiPositive_iff_isPositive_lmul_and_injective (t : E →ₗ[ℝ] ℝ)
    (hcyc : ∀ x y : E, t (x * y) = t (y * x)) (hstar : ∀ x : E, t (star x) = t x)
    (hpos : ∀ x : E, x ≠ 0 → 0 < t (x * star x)) (s : E) :
    IsRosatiPositive t s ↔
      (RosatiSpace.lmul t hstar hpos s).IsPositive ∧
        Function.Injective (RosatiSpace.lmul t hstar hpos s) := by
  refine ⟨fun hs ↦ ⟨isPositive_lmul_of_isRosatiPositive t hcyc hstar hpos hs, fun x y hxy ↦ ?_⟩,
    fun ⟨hsPos, hinj⟩ ↦
      isRosatiPositive_of_isPositive_lmul_of_injective t hcyc hstar hpos hsPos hinj⟩
  have hsub : RosatiSpace.lmul t hstar hpos s (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  obtain ⟨z, hz⟩ := (RosatiSpace.of t hstar hpos).surjective (x - y)
  rw [← hz, RosatiSpace.lmul_apply] at hsub
  have hsz : s * z = 0 := by simpa using (RosatiSpace.of t hstar hpos).injective hsub
  have hz0 : z = 0 := by_contra fun hz0 ↦ (hs.2 z hz0).ne' (by rw [hsz, zero_mul, map_zero])
  exact sub_eq_zero.mp (by rw [← hz, hz0, map_zero])

end InnerProduct

end TauCeti

namespace StarAlgEquiv

open TauCeti

/-- Transport of `TauCeti.IsRosatiPositive` along a real star-algebra isomorphism. -/
theorem isRosatiPositive_comp_iff {E F : Type*} [Semiring E] [Algebra ℝ E] [Star E]
    [Semiring F] [Algebra ℝ F] [Star F] (e : E ≃⋆ₐ[ℝ] F) (tF : F →ₗ[ℝ] ℝ) (s : E) :
    IsRosatiPositive (tF.comp e.toAlgEquiv.toLinearMap) s ↔ IsRosatiPositive tF (e s) :=
  ⟨fun ⟨hs, hp⟩ ↦ ⟨by rw [IsSelfAdjoint, ← map_star e, hs.star_eq], fun y hy ↦ by
      simpa [map_mul, map_star] using hp (e.symm y) fun h ↦ hy (by simpa using congrArg e h)⟩,
    fun ⟨hs, hp⟩ ↦ ⟨EquivLike.injective e (by rw [map_star e, hs.star_eq]), fun x hx ↦ by
      simpa [map_mul, map_star] using
        hp (e x) fun h ↦ hx (EquivLike.injective e (by simpa using h))⟩⟩

end StarAlgEquiv

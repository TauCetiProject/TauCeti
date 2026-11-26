/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Algebra.Star.StarAlgHom
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Positive traces, the Rosati inner product, and the trace regular representation

Defines `TauCeti.IsRosatiPositive` and its cone, unit, and transport properties, and constructs
the trace inner product `TauCeti.rosatiInnerProductCore` (when `t` is star-invariant and strictly
positive on `x * star x`) and faithful star regular representation
`TauCeti.rosatiRegularRepresentation` (when `E` is finite-dimensional and `t` is cyclic).

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

theorem IsRosatiPositive.trace_mul_mul_star_pos [AddCommMonoid E] [Mul E] [Module ℝ E] [Star E]
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
  rw [show star (u : E) * s * u * x * star x = star (u : E) * (s * ((u : E) * x) * star x)
    by simp only [mul_assoc], hcyc]
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

/-- Evaluation of the inner product installed from `TauCeti.rosatiInnerProductCore`. -/
@[simp] theorem rosatiInnerProductCore_inner_eq (t : E →ₗ[ℝ] ℝ)
    (hstar : ∀ x : E, t (star x) = t x) (hpos : ∀ x : E, x ≠ 0 → 0 < t (x * star x)) (x y : E) :
    letI := (rosatiInnerProductCore t hstar hpos).toNormedAddCommGroup
    letI := InnerProductSpace.ofCore (rosatiInnerProductCore t hstar hpos).toCore
    ⟪x, y⟫_ℝ = t (x * star y) := rfl

end Core

variable {E : Type*} [Ring E] [Algebra ℝ E] [StarRing E]

/-- Left multiplication by `s` has `star s` as its formal adjoint for the trace inner product
whenever `t` is cyclic. -/
theorem inner_lmul_left (t : E →ₗ[ℝ] ℝ) (hcyc : ∀ x y : E, t (x * y) = t (y * x))
    (hstar : ∀ x : E, t (star x) = t x) (hpos : ∀ x : E, x ≠ 0 → 0 < t (x * star x))
    (s x y : E) :
    letI := (rosatiInnerProductCore t hstar hpos).toNormedAddCommGroup
    letI := InnerProductSpace.ofCore (rosatiInnerProductCore t hstar hpos).toCore
    ⟪Algebra.lmul ℝ E s x, y⟫_ℝ = ⟪x, Algebra.lmul ℝ E (star s) y⟫_ℝ := by
  let _ := (rosatiInnerProductCore t hstar hpos).toNormedAddCommGroup
  let _ := InnerProductSpace.ofCore (rosatiInnerProductCore t hstar hpos).toCore
  simp only [rosatiInnerProductCore_inner_eq, Algebra.coe_lmul_eq_mul, LinearMap.mul_apply',
    star_mul, star_star, mul_assoc]; rw [hcyc s (x * star y), mul_assoc]

/-- In finite dimension, the Hilbert-space adjoint of `Algebra.lmul ℝ E s` on the trace inner
product space is `Algebra.lmul ℝ E (star s)`. -/
theorem adjoint_lmul_eq_lmul_star [FiniteDimensional ℝ E] (t : E →ₗ[ℝ] ℝ)
    (hcyc : ∀ x y : E, t (x * y) = t (y * x)) (hstar : ∀ x : E, t (star x) = t x)
    (hpos : ∀ x : E, x ≠ 0 → 0 < t (x * star x)) (s : E) :
    letI := (rosatiInnerProductCore t hstar hpos).toNormedAddCommGroup
    letI := InnerProductSpace.ofCore (rosatiInnerProductCore t hstar hpos).toCore
    (Algebra.lmul ℝ E s).adjoint = Algebra.lmul ℝ E (star s) := by
  let _ := (rosatiInnerProductCore t hstar hpos).toNormedAddCommGroup
  let _ := InnerProductSpace.ofCore (rosatiInnerProductCore t hstar hpos).toCore
  exact ((LinearMap.eq_adjoint_iff (Algebra.lmul ℝ E (star s)) (Algebra.lmul ℝ E s)).mpr
    fun x y ↦ by simpa only [star_star] using inner_lmul_left t hcyc hstar hpos (star s) x y).symm

/-- The left-regular representation as a faithful star algebra homomorphism from `E` into the
endomorphisms of the trace inner product space. -/
@[expose] noncomputable def rosatiRegularRepresentation [FiniteDimensional ℝ E]
    (t : E →ₗ[ℝ] ℝ) (hcyc : ∀ x y : E, t (x * y) = t (y * x))
    (hstar : ∀ x : E, t (star x) = t x) (hpos : ∀ x : E, x ≠ 0 → 0 < t (x * star x)) :
    letI := (rosatiInnerProductCore t hstar hpos).toNormedAddCommGroup
    letI := InnerProductSpace.ofCore (rosatiInnerProductCore t hstar hpos).toCore
    E →⋆ₐ[ℝ] (E →ₗ[ℝ] E) :=
  let _ := (rosatiInnerProductCore t hstar hpos).toNormedAddCommGroup
  let _ := InnerProductSpace.ofCore (rosatiInnerProductCore t hstar hpos).toCore
  { Algebra.lmul ℝ E with
    map_star' := fun s ↦ ((LinearMap.star_eq_adjoint (Algebra.lmul ℝ E s)).trans
      (adjoint_lmul_eq_lmul_star t hcyc hstar hpos s)).symm }

@[simp] theorem rosatiRegularRepresentation_apply [FiniteDimensional ℝ E] (t : E →ₗ[ℝ] ℝ)
    (hcyc : ∀ x y : E, t (x * y) = t (y * x)) (hstar : ∀ x : E, t (star x) = t x)
    (hpos : ∀ x : E, x ≠ 0 → 0 < t (x * star x)) (s : E) :
    rosatiRegularRepresentation t hcyc hstar hpos s = Algebra.lmul ℝ E s := rfl

theorem rosatiRegularRepresentation_injective [FiniteDimensional ℝ E] (t : E →ₗ[ℝ] ℝ)
    (hcyc : ∀ x y : E, t (x * y) = t (y * x)) (hstar : ∀ x : E, t (star x) = t x)
    (hpos : ∀ x : E, x ≠ 0 → 0 < t (x * star x)) :
    Function.Injective (rosatiRegularRepresentation t hcyc hstar hpos) := Algebra.lmul_injective

/-- Left multiplication by `s` is symmetric on the trace inner product space iff `s` is
self-adjoint. -/
theorem isSymmetric_lmul_iff (t : E →ₗ[ℝ] ℝ) (hcyc : ∀ x y : E, t (x * y) = t (y * x))
    (hstar : ∀ x : E, t (star x) = t x) (hpos : ∀ x : E, x ≠ 0 → 0 < t (x * star x))
    (s : E) :
    letI := (rosatiInnerProductCore t hstar hpos).toNormedAddCommGroup
    letI := InnerProductSpace.ofCore (rosatiInnerProductCore t hstar hpos).toCore
    (Algebra.lmul ℝ E s).IsSymmetric ↔ IsSelfAdjoint s := by
  let _ := (rosatiInnerProductCore t hstar hpos).toNormedAddCommGroup
  let _ := InnerProductSpace.ofCore (rosatiInnerProductCore t hstar hpos).toCore
  refine ⟨fun hsym ↦ (sub_eq_zero.mp ((inner_self_eq_zero (𝕜 := ℝ)).mp ?_)).symm,
    fun hs x y ↦ by rw [inner_lmul_left t hcyc hstar hpos s x y, hs.star_eq]⟩
  rw [inner_sub_left, sub_eq_zero]
  simpa using (hsym 1 (s - star s)).trans (by simpa [star_star] using
    (inner_lmul_left t hcyc hstar hpos (star s) 1 (s - star s)).symm)

/-- A Rosati-positive element acts as a positive operator on the trace inner product space. -/
theorem isPositive_lmul_of_isRosatiPositive (t : E →ₗ[ℝ] ℝ)
    (hcyc : ∀ x y : E, t (x * y) = t (y * x)) (hstar : ∀ x : E, t (star x) = t x)
    (hpos : ∀ x : E, x ≠ 0 → 0 < t (x * star x)) {s : E} (hs : IsRosatiPositive t s) :
    letI := (rosatiInnerProductCore t hstar hpos).toNormedAddCommGroup
    letI := InnerProductSpace.ofCore (rosatiInnerProductCore t hstar hpos).toCore
    (Algebra.lmul ℝ E s).IsPositive := by
  let _ := (rosatiInnerProductCore t hstar hpos).toNormedAddCommGroup
  let _ := InnerProductSpace.ofCore (rosatiInnerProductCore t hstar hpos).toCore
  refine ⟨(isSymmetric_lmul_iff t hcyc hstar hpos s).mpr hs.1, fun x ↦ ?_⟩
  rw [RCLike.re_to_real, rosatiInnerProductCore_inner_eq, Algebra.coe_lmul_eq_mul,
    LinearMap.mul_apply']
  rcases eq_or_ne x 0 with rfl | hx <;> [simp; exact (hs.2 x hx).le]

/-- An element whose left-multiplication operator is injective and positive on the trace inner
product space is Rosati-positive. -/
theorem isRosatiPositive_of_isPositive_lmul (t : E →ₗ[ℝ] ℝ)
    (hcyc : ∀ x y : E, t (x * y) = t (y * x)) (hstar : ∀ x : E, t (star x) = t x)
    (hpos : ∀ x : E, x ≠ 0 → 0 < t (x * star x)) {s : E}
    (hsPos :
      letI := (rosatiInnerProductCore t hstar hpos).toNormedAddCommGroup
      letI := InnerProductSpace.ofCore (rosatiInnerProductCore t hstar hpos).toCore
      (Algebra.lmul ℝ E s).IsPositive)
    (hinj : Function.Injective (Algebra.lmul ℝ E s)) : IsRosatiPositive t s := by
  let _ := (rosatiInnerProductCore t hstar hpos).toNormedAddCommGroup
  let _ := InnerProductSpace.ofCore (rosatiInnerProductCore t hstar hpos).toCore
  refine ⟨(isSymmetric_lmul_iff t hcyc hstar hpos s).mp hsPos.isSymmetric, fun x hx ↦
    lt_of_le_of_ne (hsPos.re_inner_nonneg_left x) fun hzero ↦ hx ?_⟩
  let B := (innerₗ E).compl₁₂ (Algebra.lmul ℝ E s) LinearMap.id
  exact hinj (by simpa [B] using congrArg (· (Algebra.lmul ℝ E s x)) (LinearMap.mem_ker.mp
    ((LinearMap.BilinForm.apply_apply_same_eq_zero_iff B hsPos.re_inner_nonneg_left
      ⟨fun a b ↦ by simpa [B] using (hsPos.isSymmetric a b).trans (real_inner_comm _ _)⟩).mp
      hzero.symm)))

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

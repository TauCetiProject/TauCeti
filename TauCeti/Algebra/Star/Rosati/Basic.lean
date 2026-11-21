/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.Algebra.Module.Rat
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.RingTheory.Adjoin.Polynomial.Basic
import TauCeti.Analysis.InnerProductSpace.Positive.SquareRoot
import TauCeti.Analysis.InnerProductSpace.Symmetric.FunctionalCalculus

/-!
# Positive traces, the Rosati inner product, and internal positive square roots

Let `E` be an associative real star algebra equipped with a linear functional `t : E →ₗ[ℝ] ℝ`
that is strictly positive on `x * star x` for nonzero `x`.  Such a pair models the real
endomorphism algebra of a polarized abelian variety with its Rosati involution and reduced trace,
as well as finite-dimensional real C*-algebras with a faithful tracial state.

## Main definitions

* `TauCeti.IsRosatiPositive`: self-adjointness and strict positivity of the trace quadratic form
  `x ↦ t (s * x * star x)`.
* `TauCeti.rosatiInnerProductCore`: the positive definite real inner product
  `⟪x, y⟫ = t (x * star y)` determined by a star-invariant positive linear functional `t`.

## Main results

* `TauCeti.starModule_of_trace_mul_star_pos`: positivity of `t (x * star x)` on nonzero elements
  forces the involution `star` to be `ℝ`-linear, so `StarModule ℝ E` holds automatically without
  assuming finiteness, cyclicity, or star-invariance of `t`.
* `TauCeti.IsRosatiPositive.isUnit`: in finite dimension, every `IsRosatiPositive` element is a
  unit.
* `TauCeti.inner_lmul_left`, `TauCeti.adjoint_lmul_eq_lmul_star`,
  `TauCeti.isSymmetric_lmul_iff`, `TauCeti.isPositive_lmul_of_isRosatiPositive`,
  `TauCeti.isRosatiPositive_of_isPositive_lmul_of_isUnit`: the left-regular representation
  `Algebra.lmul ℝ E` intertwines the algebra involution `star` with the Hilbert-space adjoint on
  the trace inner product space and identifies `IsRosatiPositive` elements with positive invertible
  left-multiplication operators.
* `TauCeti.rosatiPositiveSquareRoot`: in a finite-dimensional real star algebra with a cyclic
  linear functional `t` strictly positive on `x * star x`, every `IsRosatiPositive` element `s`
  is a unit and admits a unique `IsRosatiPositive` square root `r`; both `r` and `r⁻¹` lie in
  `ℝ[s]` and therefore commute with the centralizer of `s`.

## Implementation notes

Positivity of `x ↦ t (x * star x)` automatically forces `StarModule ℝ E`: the additive map
`a ↦ t (star (algebraMap ℝ E a))` is positive on `(0, ∞)`, hence linear, and applying `t` to
`star (r²) - r²` shows `u = star (algebraMap ℝ E r) - algebraMap ℝ E r` satisfies
`t (u * star u) = 0`.
Furthermore, symmetrizing `t` to `t' x = (t x + t (star x)) / 2` preserves cyclicity, positivity,
and the predicate `IsRosatiPositive` identically, so neither `[StarModule ℝ E]` nor star-invariance
`∀ x, t (star x) = t x` needs to be assumed for `rosatiPositiveSquareRoot`.

For the internal square root, we pass through the left-regular representation `Algebra.lmul ℝ E`,
take the operator square root `LinearMap.IsPositive.sqrt`, and use Lagrange interpolation on the
finite spectrum of `Algebra.lmul ℝ E s` to express both the operator square root and its inverse
as real polynomials in `Algebra.lmul ℝ E s`.  Faithfulness of `Algebra.lmul ℝ E` then transfers all
identities and uniqueness back to `E`.

## References

* J. Voight, *Quaternion Algebras*, Graduate Texts in Mathematics 288, Springer (2021), §8.4.
* M. Lipnowski and J. Tsimerman, *Algorithms for abelian varieties*, §4.3.2.
-/

public section

open scoped InnerProductSpace Polynomial

namespace TauCeti

/-! ### Positivity with respect to a trace functional -/

section IsRosatiPositive

/-- An element `s` of a real star algebra is **Rosati-positive** with respect to a linear
functional `t : E →ₗ[ℝ] ℝ` if `s` is self-adjoint and `t (s * x * star x) > 0` for all `x ≠ 0`. -/
def IsRosatiPositive {E : Type*} [AddCommMonoid E] [Mul E] [Module ℝ E] [Star E]
    (t : E →ₗ[ℝ] ℝ) (s : E) : Prop :=
  IsSelfAdjoint s ∧ ∀ x : E, x ≠ 0 → 0 < t (s * x * star x)

theorem isRosatiPositive_iff {E : Type*} [AddCommMonoid E] [Mul E] [Module ℝ E] [Star E]
    {t : E →ₗ[ℝ] ℝ} {s : E} :
    IsRosatiPositive t s ↔ IsSelfAdjoint s ∧ ∀ x : E, x ≠ 0 → 0 < t (s * x * star x) :=
  Iff.rfl

theorem IsRosatiPositive.isSelfAdjoint {E : Type*} [AddCommMonoid E] [Mul E] [Module ℝ E]
    [Star E] {t : E →ₗ[ℝ] ℝ} {s : E} (hs : IsRosatiPositive t s) : IsSelfAdjoint s :=
  hs.1

theorem IsRosatiPositive.trace_mul_mul_star_pos {E : Type*} [AddCommMonoid E] [Mul E]
    [Module ℝ E] [Star E] {t : E →ₗ[ℝ] ℝ} {s : E} (hs : IsRosatiPositive t s) {x : E}
    (hx : x ≠ 0) : 0 < t (s * x * star x) :=
  hs.2 x hx

/-- The sum of two Rosati-positive elements is Rosati-positive. -/
theorem IsRosatiPositive.add {E : Type*} [NonUnitalNonAssocSemiring E] [Module ℝ E]
    [StarAddMonoid E] {t : E →ₗ[ℝ] ℝ} {s₁ s₂ : E} (h₁ : IsRosatiPositive t s₁)
    (h₂ : IsRosatiPositive t s₂) : IsRosatiPositive t (s₁ + s₂) :=
  ⟨h₁.1.add h₂.1, fun x hx ↦ by simpa [add_mul] using add_pos (h₁.2 x hx) (h₂.2 x hx)⟩

/-- A positive real multiple of a Rosati-positive element is Rosati-positive. -/
theorem IsRosatiPositive.smul {E : Type*} [AddCommMonoid E] [Mul E] [Module ℝ E]
    [IsScalarTower ℝ E E] [Star E] [StarModule ℝ E] {t : E →ₗ[ℝ] ℝ} {c : ℝ} {s : E}
    (hc : 0 < c) (hs : IsRosatiPositive t s) : IsRosatiPositive t (c • s) :=
  ⟨by rw [IsSelfAdjoint, star_smul, star_trivial, hs.1.star_eq], fun x hx ↦ by
    simpa [smul_mul_assoc, smul_eq_mul] using mul_pos hc (hs.2 x hx)⟩

/-- `1` is Rosati-positive with respect to `t` iff `t (x * star x) > 0` for all `x ≠ 0`. -/
theorem isRosatiPositive_one_iff {E : Type*} [Semiring E] [Module ℝ E] [StarRing E]
    {t : E →ₗ[ℝ] ℝ} :
    IsRosatiPositive t 1 ↔ ∀ x : E, x ≠ 0 → 0 < t (x * star x) := by
  simp only [IsRosatiPositive, IsSelfAdjoint.one, one_mul, true_and]

/-- For a cyclic trace functional `t`, congruence `s ↦ star u * s * u` by a unit preserves
`IsRosatiPositive`. -/
theorem IsRosatiPositive.conj_unit {E : Type*} [Semiring E] [Module ℝ E] [StarRing E]
    {t : E →ₗ[ℝ] ℝ} (hcyclic : ∀ x y : E, t (x * y) = t (y * x))
    (u : Eˣ) {s : E} (hs : IsRosatiPositive t s) :
    IsRosatiPositive t (star (u : E) * s * u) := by
  refine ⟨by rw [IsSelfAdjoint, star_mul, star_mul, star_star, hs.1.star_eq, mul_assoc],
    fun x hx ↦ ?_⟩
  have hux : (u : E) * x ≠ 0 := fun h ↦ hx (by simpa using congrArg ((↑u⁻¹ : E) * ·) h)
  rw [show star (u : E) * s * u * x * star x = star (u : E) * (s * ((u : E) * x) * star x) by
    simp only [mul_assoc], hcyclic]
  simpa only [mul_assoc, star_mul] using hs.2 ((u : E) * x) hux

/-- Every Rosati-positive element of a finite-dimensional real algebra with star is a unit. -/
theorem IsRosatiPositive.isUnit {E : Type*} [Ring E] [Algebra ℝ E] [Star E]
    [Module.Finite ℝ E] {t : E →ₗ[ℝ] ℝ} {s : E} (hs : IsRosatiPositive t s) :
    IsUnit s := by
  have hinj : Function.Injective (Algebra.lmul ℝ E s) := (injective_iff_map_eq_zero _).mpr
    fun x hx ↦ by_contra fun hx0 ↦
      (hs.2 x hx0).ne' (by rw [show s * x = 0 from hx, zero_mul, map_zero])
  obtain ⟨y, hy⟩ := (LinearMap.injective_iff_surjective.mp hinj) 1
  exact ⟨⟨s, y, hy, hinj (by simp [← mul_assoc, show s * y = 1 from hy])⟩, rfl⟩

/-- Transport of `IsRosatiPositive` along a star-preserving `ℝ`-algebra isomorphism. -/
theorem isRosatiPositive_iff_of_algEquiv {E F : Type*} [Semiring E] [Algebra ℝ E] [Star E]
    [Semiring F] [Algebra ℝ F] [Star F] (e : E ≃ₐ[ℝ] F) (he : ∀ x : E, e (star x) = star (e x))
    (tF : F →ₗ[ℝ] ℝ) (s : E) :
    IsRosatiPositive (tF.comp e.toLinearMap) s ↔ IsRosatiPositive tF (e s) :=
  ⟨fun ⟨hs, hp⟩ ↦ ⟨by rw [IsSelfAdjoint, ← he, hs.star_eq], fun y hy ↦ by
      simpa [LinearMap.comp_apply, map_mul, he] using
        hp (e.symm y) fun h ↦ hy (by simpa using congrArg e h)⟩,
    fun ⟨hs, hp⟩ ↦ ⟨e.injective (by rw [he, hs.star_eq]), fun x hx ↦ by
      simpa [LinearMap.comp_apply, map_mul, he] using
        hp (e x) fun h ↦ hx (e.injective (by simpa using h))⟩⟩

/-- For a cyclic linear functional `t`, replacing `t` by its star-symmetrization
`t' x = (t x + t (star x)) / 2` leaves `IsRosatiPositive` unchanged. -/
theorem isRosatiPositive_iff_of_symmetrize {E : Type*} [Semiring E] [Module ℝ E] [StarRing E]
    {t t' : E →ₗ[ℝ] ℝ} (ht' : ∀ x : E, t' x = (t x + t (star x)) / 2)
    (hcyclic : ∀ x y : E, t (x * y) = t (y * x)) {s : E} :
    IsRosatiPositive t' s ↔ IsRosatiPositive t s := by
  refine and_congr_right fun hs ↦ forall₂_congr fun x _ ↦ ?_
  have hst : t (star (s * x * star x)) = t (s * x * star x) := by
    rw [star_mul, star_mul, star_star, hs.star_eq, ← mul_assoc, hcyclic, mul_assoc]
  rw [ht', hst]; constructor <;> intro h <;> linarith

/-- Evaluating `(t.comp (selfAdjoint.submodule ℝ E).subtype).comp (selfAdjointPart ℝ)` gives
`(t x + t (star x)) / 2`. -/
theorem comp_selfAdjointPart_apply {E : Type*} [AddCommGroup E] [Module ℝ E] [StarAddMonoid E]
    [StarModule ℝ E] (t : E →ₗ[ℝ] ℝ) (x : E) :
    ((t.comp (selfAdjoint.submodule ℝ E).subtype).comp (selfAdjointPart ℝ)) x =
      (t x + t (star x)) / 2 := by
  change t (selfAdjointPart ℝ x : E) = (t x + t (star x)) / 2
  rw [selfAdjointPart_apply_coe, map_smul, map_add, smul_eq_mul, invOf_eq_inv, div_eq_inv_mul]

/-- The symmetrization `(t.comp (selfAdjoint.submodule ℝ E).subtype).comp (selfAdjointPart ℝ)` is
star-invariant. -/
theorem comp_selfAdjointPart_star {E : Type*} [AddCommGroup E] [Module ℝ E] [StarAddMonoid E]
    [StarModule ℝ E] (t : E →ₗ[ℝ] ℝ) (x : E) :
    ((t.comp (selfAdjoint.submodule ℝ E).subtype).comp (selfAdjointPart ℝ)) (star x) =
      ((t.comp (selfAdjoint.submodule ℝ E).subtype).comp (selfAdjointPart ℝ)) x := by
  simp only [comp_selfAdjointPart_apply, star_star, add_comm]

/-- The symmetrization `(t.comp (selfAdjoint.submodule ℝ E).subtype).comp (selfAdjointPart ℝ)`
inherits cyclicity from `t`. -/
theorem comp_selfAdjointPart_cyclic {E : Type*} [NonUnitalNonAssocRing E] [Module ℝ E] [StarRing E]
    [StarModule ℝ E] {t : E →ₗ[ℝ] ℝ} (hcyclic : ∀ x y : E, t (x * y) = t (y * x)) (x y : E) :
    ((t.comp (selfAdjoint.submodule ℝ E).subtype).comp (selfAdjointPart ℝ)) (x * y) =
      ((t.comp (selfAdjoint.submodule ℝ E).subtype).comp (selfAdjointPart ℝ)) (y * x) := by
  simp only [comp_selfAdjointPart_apply, star_mul, hcyclic x y, hcyclic (star y) (star x)]

/-- The symmetrization `(t.comp (selfAdjoint.submodule ℝ E).subtype).comp (selfAdjointPart ℝ)`
inherits strict positivity on `x * star x` from `t`. -/
theorem comp_selfAdjointPart_mul_star_pos {E : Type*} [NonUnitalNonAssocRing E] [Module ℝ E]
    [StarRing E] [StarModule ℝ E] {t : E →ₗ[ℝ] ℝ}
    (hpos : ∀ x : E, x ≠ 0 → 0 < t (x * star x)) {x : E} (hx : x ≠ 0) :
    0 < ((t.comp (selfAdjoint.submodule ℝ E).subtype).comp (selfAdjointPart ℝ)) (x * star x) := by
  have h := hpos x hx
  simp only [comp_selfAdjointPart_apply, star_mul, star_star]
  linarith

end IsRosatiPositive

/-! ### Automatic real-linearity of the involution -/

section StarModule

/-- An additive map `ℝ →+ ℝ` sending positive reals to positive reals is linear. -/
private theorem addMonoidHom_real_eq_mul_one (f : ℝ →+ ℝ) (hf : ∀ r : ℝ, 0 < r → 0 < f r)
    (r : ℝ) : f r = r * f 1 := by
  have hmono : StrictMono f := fun a b hab ↦
    sub_pos.mp (by rw [← map_sub]; exact hf _ (sub_pos.mpr hab))
  have hrat (q : ℚ) : f q = (q : ℝ) * f 1 := by simpa [Rat.smul_def] using map_rat_smul f q 1
  have hf1 : 0 < f 1 := hf 1 one_pos
  refine le_antisymm (le_of_not_gt fun hlt ↦ ?_) (le_of_not_gt fun hlt ↦ ?_)
  · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn ((lt_div_iff₀ hf1).mpr hlt)
    linarith [hmono hq1, (lt_div_iff₀ hf1).mp hq2, hrat q]
  · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn ((div_lt_iff₀ hf1).mpr hlt)
    linarith [hmono hq2, (div_lt_iff₀ hf1).mp hq1, hrat q]

/-- **Automatic real-linearity of the involution.** If a real star algebra admits a linear
functional `t : E →ₗ[ℝ] ℝ` with `t (x * star x) > 0` for all `x ≠ 0`, then `star` fixes every real
scalar and hence `StarModule ℝ E` holds. -/
theorem starModule_of_trace_mul_star_pos {E : Type*} [Ring E] [Algebra ℝ E] [StarRing E]
    (t : E →ₗ[ℝ] ℝ) (hpos : ∀ x : E, x ≠ 0 → 0 < t (x * star x)) :
    StarModule ℝ E := by
  by_cases hsub : Subsingleton E
  · exact ⟨fun _ _ ↦ Subsingleton.elim _ _⟩
  have : Nontrivial E := not_subsingleton_iff_nontrivial.mp hsub
  let f : ℝ →+ ℝ := ⟨⟨fun a ↦ t (star (algebraMap ℝ E a)), by simp⟩, fun a b ↦ by simp⟩
  have htf (a : ℝ) : t (star (algebraMap ℝ E a)) = t (algebraMap ℝ E a) := by
    have h1 := addMonoidHom_real_eq_mul_one f (fun b hb ↦ by
      have h := hpos (algebraMap ℝ E b) (by simpa using (algebraMap ℝ E).injective.ne hb.ne')
      rw [← Algebra.smul_def, map_smul, smul_eq_mul] at h
      exact pos_of_mul_pos_right (by simpa [f] using h) hb.le) a
    simpa [f, Algebra.algebraMap_eq_smul_one, smul_eq_mul] using h1
  have hstar_alg (r : ℝ) : star (algebraMap ℝ E r) = algebraMap ℝ E r := by
    set u : E := star (algebraMap ℝ E r) - algebraMap ℝ E r
    have htu : t u = 0 := by simp [u, htf]
    have hsq : star (algebraMap ℝ E (r * r)) - algebraMap ℝ E (r * r) =
        (2 * r) • u + u * u := by
      have hsum : star (algebraMap ℝ E r) = algebraMap ℝ E r + u := by simp [u]
      rw [map_mul, star_mul, hsum, add_mul, mul_add, mul_add, (Algebra.commutes r u).symm,
        two_mul, add_smul]
      simp only [← Algebra.smul_def]; abel
    have htu2 : t (u * u) = 0 := by
      have h0 : t (star (algebraMap ℝ E (r * r)) - algebraMap ℝ E (r * r)) = 0 := by
        rw [map_sub, htf, sub_self]
      rwa [hsq, map_add, map_smul, htu, smul_zero, zero_add] at h0
    refine sub_eq_zero.mp (by_contra fun hne ↦ ?_)
    have h := hpos u hne
    rw [show star u = -u by simp [u], mul_neg, map_neg, htu2, neg_zero] at h
    exact lt_irrefl 0 h
  exact ⟨fun r x ↦ by
    rw [Algebra.smul_def, star_mul, hstar_alg, ← Algebra.commutes, ← Algebra.smul_def,
      star_trivial r]⟩

end StarModule

/-! ### The trace inner product and left-regular representation -/

section InnerProduct

/-- The positive definite real inner product `⟪x, y⟫ = t (x * star y)` determined by a
star-invariant linear functional `t : E →ₗ[ℝ] ℝ` that is strictly positive on `x * star x`.
This core is not installed as a global instance, avoiding conflicts with existing norms. -/
abbrev rosatiInnerProductCore {E : Type*} [NonUnitalNonAssocRing E] [Module ℝ E]
    [IsScalarTower ℝ E E] [StarRing E] (t : E →ₗ[ℝ] ℝ)
    (hstar : ∀ x : E, t (star x) = t x)
    (hpos : ∀ x : E, x ≠ 0 → 0 < t (x * star x)) :
    InnerProductSpace.Core ℝ E where
  inner x y := t (x * star y)
  conj_inner_symm x y := by
    simp only [starRingEnd_apply, star_trivial]; rw [← hstar (x * star y), star_mul, star_star]
  re_inner_nonneg x := by
    rcases eq_or_ne x 0 with rfl | hx <;> [simp; exact (hpos x hx).le]
  add_left x y z := by rw [add_mul, map_add]
  smul_left x y r := by simp [smul_mul_assoc]
  definite x hx := by_contra fun hne ↦ (hpos x hne).ne' hx

@[simp]
theorem rosatiInnerProductCore_inner {E : Type*} [NonUnitalNonAssocRing E] [Module ℝ E]
    [IsScalarTower ℝ E E] [StarRing E] (t : E →ₗ[ℝ] ℝ)
    (hstar : ∀ x : E, t (star x) = t x)
    (hpos : ∀ x : E, x ≠ 0 → 0 < t (x * star x)) (x y : E) :
    (rosatiInnerProductCore t hstar hpos).inner x y = t (x * star y) :=
  rfl

variable {E : Type*} [Ring E] [Algebra ℝ E] [StarRing E]

/-- Left multiplication by `s` has `star s` as its formal adjoint for the trace inner product
`⟪x, y⟫ = t (x * star y)` whenever `t` is cyclic. -/
theorem inner_lmul_left (t : E →ₗ[ℝ] ℝ) (hcyclic : ∀ x y : E, t (x * y) = t (y * x))
    (hstar : ∀ x : E, t (star x) = t x) (hpos : ∀ x : E, x ≠ 0 → 0 < t (x * star x))
    (s x y : E) :
    letI := (rosatiInnerProductCore t hstar hpos).toNormedAddCommGroup
    letI := InnerProductSpace.ofCore (rosatiInnerProductCore t hstar hpos).toCore
    ⟪Algebra.lmul ℝ E s x, y⟫_ℝ = ⟪x, Algebra.lmul ℝ E (star s) y⟫_ℝ := by
  let _ := (rosatiInnerProductCore t hstar hpos).toNormedAddCommGroup
  let _ := InnerProductSpace.ofCore (rosatiInnerProductCore t hstar hpos).toCore
  change t ((s * x) * star y) = t (x * star (star s * y))
  rw [star_mul, star_star, mul_assoc, hcyclic s (x * star y), mul_assoc]

/-- In finite dimension, the Hilbert-space adjoint of `Algebra.lmul ℝ E s` on the trace inner
product space is `Algebra.lmul ℝ E (star s)`. -/
theorem adjoint_lmul_eq_lmul_star [FiniteDimensional ℝ E] (t : E →ₗ[ℝ] ℝ)
    (hcyclic : ∀ x y : E, t (x * y) = t (y * x)) (hstar : ∀ x : E, t (star x) = t x)
    (hpos : ∀ x : E, x ≠ 0 → 0 < t (x * star x)) (s : E) :
    letI := (rosatiInnerProductCore t hstar hpos).toNormedAddCommGroup
    letI := InnerProductSpace.ofCore (rosatiInnerProductCore t hstar hpos).toCore
    (Algebra.lmul ℝ E s).adjoint = Algebra.lmul ℝ E (star s) := by
  let _ := (rosatiInnerProductCore t hstar hpos).toNormedAddCommGroup
  let _ := InnerProductSpace.ofCore (rosatiInnerProductCore t hstar hpos).toCore
  refine ((LinearMap.eq_adjoint_iff (Algebra.lmul ℝ E (star s)) (Algebra.lmul ℝ E s)).mpr
    fun x y ↦ ?_).symm
  simpa only [star_star] using inner_lmul_left t hcyclic hstar hpos (star s) x y

/-- Left multiplication by `s` is symmetric on the trace inner product space iff `s` is
self-adjoint. -/
theorem isSymmetric_lmul_iff (t : E →ₗ[ℝ] ℝ) (hcyclic : ∀ x y : E, t (x * y) = t (y * x))
    (hstar : ∀ x : E, t (star x) = t x) (hpos : ∀ x : E, x ≠ 0 → 0 < t (x * star x)) (s : E) :
    letI := (rosatiInnerProductCore t hstar hpos).toNormedAddCommGroup
    letI := InnerProductSpace.ofCore (rosatiInnerProductCore t hstar hpos).toCore
    (Algebra.lmul ℝ E s).IsSymmetric ↔ IsSelfAdjoint s := by
  let _ := (rosatiInnerProductCore t hstar hpos).toNormedAddCommGroup
  let _ := InnerProductSpace.ofCore (rosatiInnerProductCore t hstar hpos).toCore
  refine ⟨fun hsym ↦ (sub_eq_zero.mp ((inner_self_eq_zero (𝕜 := ℝ)).mp ?_)).symm,
    fun hs x y ↦ by rw [inner_lmul_left t hcyclic hstar hpos s x y, hs.star_eq]⟩
  rw [inner_sub_left, sub_eq_zero]
  have h1 : ⟪s, s - star s⟫_ℝ = ⟪1, Algebra.lmul ℝ E s (s - star s)⟫_ℝ := by
    simpa using hsym 1 (s - star s)
  have h2 : ⟪star s, s - star s⟫_ℝ = ⟪1, Algebra.lmul ℝ E s (s - star s)⟫_ℝ := by
    simpa [star_star] using inner_lmul_left t hcyclic hstar hpos (star s) 1 (s - star s)
  exact h1.trans h2.symm

/-- A Rosati-positive element acts as a positive operator on the trace inner product space. -/
theorem isPositive_lmul_of_isRosatiPositive (t : E →ₗ[ℝ] ℝ)
    (hcyclic : ∀ x y : E, t (x * y) = t (y * x)) (hstar : ∀ x : E, t (star x) = t x)
    (hpos : ∀ x : E, x ≠ 0 → 0 < t (x * star x)) {s : E} (hs : IsRosatiPositive t s) :
    letI := (rosatiInnerProductCore t hstar hpos).toNormedAddCommGroup
    letI := InnerProductSpace.ofCore (rosatiInnerProductCore t hstar hpos).toCore
    (Algebra.lmul ℝ E s).IsPositive := by
  let _ := (rosatiInnerProductCore t hstar hpos).toNormedAddCommGroup
  let _ := InnerProductSpace.ofCore (rosatiInnerProductCore t hstar hpos).toCore
  refine ⟨(isSymmetric_lmul_iff t hcyclic hstar hpos s).mpr hs.1, fun x ↦ ?_⟩
  change 0 ≤ t (s * x * star x)
  rcases eq_or_ne x 0 with rfl | hx <;> [simp; exact (hs.2 x hx).le]

/-- Conversely, a unit whose left-multiplication operator is positive on the trace inner product
space is Rosati-positive. -/
theorem isRosatiPositive_of_isPositive_lmul_of_isUnit (t : E →ₗ[ℝ] ℝ)
    (hcyclic : ∀ x y : E, t (x * y) = t (y * x)) (hstar : ∀ x : E, t (star x) = t x)
    (hpos : ∀ x : E, x ≠ 0 → 0 < t (x * star x)) {s : E}
    (hsPos :
      letI := (rosatiInnerProductCore t hstar hpos).toNormedAddCommGroup
      letI := InnerProductSpace.ofCore (rosatiInnerProductCore t hstar hpos).toCore
      (Algebra.lmul ℝ E s).IsPositive)
    (hu : IsUnit s) :
    IsRosatiPositive t s := by
  let _ := (rosatiInnerProductCore t hstar hpos).toNormedAddCommGroup
  let _ := InnerProductSpace.ofCore (rosatiInnerProductCore t hstar hpos).toCore
  refine ⟨(isSymmetric_lmul_iff t hcyclic hstar hpos s).mp hsPos.isSymmetric, fun x hx ↦ ?_⟩
  refine lt_of_le_of_ne (hsPos.re_inner_nonneg_left x) fun hzero ↦ hx ?_
  set T := Algebra.lmul ℝ E s
  let B := (innerₗ E).compl₁₂ T LinearMap.id
  have hB : LinearMap.IsSymm B := ⟨fun a b ↦ by
    simp only [B, LinearMap.compl₁₂_apply, LinearMap.id_coe, id_eq, innerₗ_apply_apply,
      RingHom.id_apply]
    rw [hsPos.isSymmetric, real_inner_comm]⟩
  have hTxx : ⟪T x, T x⟫_ℝ = 0 := by
    have hsq := LinearMap.BilinForm.apply_sq_le_of_symm B hsPos.re_inner_nonneg_left hB x (T x)
    have hBxx : B x x = 0 := hzero.symm
    rw [hBxx, zero_mul] at hsq
    exact eq_zero_of_pow_eq_zero (le_antisymm hsq (sq_nonneg _))
  obtain ⟨u, rfl⟩ := hu
  simpa [T] using congrArg ((↑u⁻¹ : E) * ·) (inner_self_eq_zero.mp hTxx)

end InnerProduct

/-! ### Internal positive square roots -/

section SquareRoot

/-- Every functional calculus value `hT.cfc f` of a symmetric operator on a finite-dimensional
real inner product space equals `Polynomial.aeval T p` for a Lagrange interpolating polynomial. -/
private theorem exists_aeval_eq_cfc {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] {T : V →ₗ[ℝ] V} (hT : T.IsSymmetric) (f : ℝ → ℝ) :
    ∃ p : ℝ[X], Polynomial.aeval T p = hT.cfc f := by
  refine ⟨Lagrange.interpolate (Finset.univ.image (hT.eigenvalues rfl)) id f,
    (hT.eigenvectorBasis rfl).toBasis.ext fun i ↦ ?_⟩
  rw [OrthonormalBasis.coe_toBasis, hT.cfc_apply_eigenvectorBasis,
    Module.End.aeval_apply_of_mem_apply_eq_smul (hT.apply_eigenvectorBasis rfl i)]
  simp only [RCLike.ofReal_real_eq_id, id_eq]
  rw [show Polynomial.eval (hT.eigenvalues rfl i)
      (Lagrange.interpolate (Finset.univ.image (hT.eigenvalues rfl)) id f) =
      f (hT.eigenvalues rfl i) by
    simpa only [id_eq] using Lagrange.eval_interpolate_at_node (r := f) (v := id)
      (fun _ _ _ _ h ↦ h) (Finset.mem_image_of_mem _ (Finset.mem_univ i))]

/-- Every eigenvalue of left multiplication by a Rosati-positive element is strictly positive. -/
private theorem hasEigenvalue_lmul_pos {E : Type*} [Ring E] [Algebra ℝ E] [StarRing E]
    (t : E →ₗ[ℝ] ℝ) (hpos : ∀ x : E, x ≠ 0 → 0 < t (x * star x)) {s : E}
    (hs : IsRosatiPositive t s) {μ : ℝ} (hμ : (Algebra.lmul ℝ E s).HasEigenvalue μ) : 0 < μ := by
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have hv' : s * v = μ • v := by simpa using Module.End.mem_eigenspace_iff.mp hv.1
  have h1 := hs.2 v hv.2
  rw [hv', smul_mul_assoc, map_smul, smul_eq_mul] at h1
  exact pos_of_mul_pos_left h1 (hpos v hv.2).le

/-- Helper for `TauCeti.rosatiPositiveSquareRoot` assuming a star-invariant trace `t`. -/
private theorem rosatiPositiveSquareRoot_of_star_invariant {E : Type*} [Ring E] [Algebra ℝ E]
    [StarRing E] [Module.Finite ℝ E] (t : E →ₗ[ℝ] ℝ)
    (hcyclic : ∀ x y : E, t (x * y) = t (y * x))
    (hstar : ∀ x : E, t (star x) = t x)
    (hpos : ∀ x : E, x ≠ 0 → 0 < t (x * star x)) (s : E) (hs : IsRosatiPositive t s) :
    IsUnit s ∧ ∃ r : Eˣ, IsRosatiPositive t r ∧ (r : E) * r = s ∧
      (r : E) ∈ Algebra.adjoin ℝ ({s} : Set E) ∧
      ((r⁻¹ : Eˣ) : E) ∈ Algebra.adjoin ℝ ({s} : Set E) ∧
      (∀ x : E, Commute x s → Commute x r ∧ Commute x ((r⁻¹ : Eˣ) : E)) ∧
      ∀ r' : E, IsRosatiPositive t r' → r' * r' = s → r' = r := by
  let core := rosatiInnerProductCore t hstar hpos
  let _ : NormedAddCommGroup E := core.toNormedAddCommGroup
  let _ : InnerProductSpace ℝ E := InnerProductSpace.ofCore core.toCore
  have hT : (Algebra.lmul ℝ E s).IsPositive :=
    isPositive_lmul_of_isRosatiPositive t hcyclic hstar hpos hs
  have hsqrt_cfc : hT.sqrt = hT.isSymmetric.cfc Real.sqrt :=
    (hT.isSymmetric.eq_cfc_iff Real.sqrt).mpr fun _ _ hx ↦ hT.sqrt_apply_of_apply_eq_smul hx
  obtain ⟨p, hp⟩ := exists_aeval_eq_cfc hT.isSymmetric Real.sqrt
  obtain ⟨q, hq⟩ := exists_aeval_eq_cfc hT.isSymmetric (fun μ ↦ (Real.sqrt μ)⁻¹)
  set r : E := Polynomial.aeval s p; set rInv : E := Polynomial.aeval s q
  have hlmul_r : Algebra.lmul ℝ E r = hT.sqrt := by
    rw [hsqrt_cfc, ← hp]; exact (Polynomial.aeval_algHom_apply (Algebra.lmul ℝ E) s p).symm
  have hlmul_rInv : Algebra.lmul ℝ E rInv = hT.isSymmetric.cfc (fun μ ↦ (Real.sqrt μ)⁻¹) := by
    rw [← hq]; exact (Polynomial.aeval_algHom_apply (Algebra.lmul ℝ E) s q).symm
  have hcfc_mul {f g : ℝ → ℝ}
      (hfg : ∀ μ, (Algebra.lmul ℝ E s).HasEigenvalue μ → f μ * g μ = 1) :
      hT.isSymmetric.cfc f * hT.isSymmetric.cfc g = 1 := by
    rw [← hT.isSymmetric.cfc_mul, ← hT.isSymmetric.cfc_one]; exact hT.isSymmetric.cfc_congr hfg
  let u : Eˣ := ⟨r, rInv,
    Algebra.lmul_injective (R := ℝ) (by
      rw [map_mul, map_one, hlmul_r, hlmul_rInv, hsqrt_cfc]
      exact hcfc_mul fun μ hμ ↦
        mul_inv_cancel₀ (Real.sqrt_ne_zero'.mpr (hasEigenvalue_lmul_pos t hpos hs hμ))),
    Algebra.lmul_injective (R := ℝ) (by
      rw [map_mul, map_one, hlmul_r, hlmul_rInv, hsqrt_cfc]
      exact hcfc_mul fun μ hμ ↦
        inv_mul_cancel₀ (Real.sqrt_ne_zero'.mpr (hasEigenvalue_lmul_pos t hpos hs hμ)))⟩
  have hr_mem : r ∈ Algebra.adjoin ℝ ({s} : Set E) := Polynomial.aeval_mem_adjoin_singleton ℝ s
  have hrInv_mem : rInv ∈ Algebra.adjoin ℝ ({s} : Set E) :=
    Polynomial.aeval_mem_adjoin_singleton ℝ s
  refine ⟨hs.isUnit, u, isRosatiPositive_of_isPositive_lmul_of_isUnit t hcyclic hstar hpos
      (hlmul_r ▸ hT.sqrt_isPositive) ⟨u, rfl⟩,
    Algebra.lmul_injective (R := ℝ) (by rw [map_mul, hlmul_r, Module.End.mul_eq_comp, hT.sqrt_sq]),
    hr_mem, hrInv_mem, fun x hx ↦
      ⟨Algebra.commute_of_mem_adjoin_of_forall_mem_commute hr_mem (by simpa using hx),
       Algebra.commute_of_mem_adjoin_of_forall_mem_commute hrInv_mem (by simpa using hx)⟩,
    fun r' hr' hr'sq ↦ Algebra.lmul_injective (R := ℝ) <| by
      rw [hlmul_r]
      exact hT.sqrt_unique (isPositive_lmul_of_isRosatiPositive t hcyclic hstar hpos hr')
        (by rw [← Module.End.mul_eq_comp, ← map_mul, hr'sq])⟩

/-- **Internal positive square roots.** In a finite-dimensional real star algebra with a cyclic
linear functional `t : E →ₗ[ℝ] ℝ` strictly positive on `x * star x`, every element `s` with
`IsRosatiPositive t s` is a unit and admits a unique root `r` with `IsRosatiPositive t r` and
`r * r = s`.  Both `r` and `r⁻¹` lie in `ℝ[s]` and commute with every element commuting with `s`.

Neither `[StarModule ℝ E]` nor star-invariance `∀ x, t (star x) = t x` is needed: real-linearity
of `star` is automatic (`TauCeti.starModule_of_trace_mul_star_pos`), and symmetrizing `t` to
`x ↦ (t x + t (star x)) / 2` preserves `IsRosatiPositive` identically. -/
theorem rosatiPositiveSquareRoot {E : Type*} [Ring E] [Algebra ℝ E] [StarRing E]
    [Module.Finite ℝ E] (t : E →ₗ[ℝ] ℝ)
    (hcyclic : ∀ x y : E, t (x * y) = t (y * x))
    (hpos : ∀ x : E, x ≠ 0 → 0 < t (x * star x)) (s : E) (hs : IsRosatiPositive t s) :
    IsUnit s ∧ ∃ r : Eˣ, IsRosatiPositive t r ∧ (r : E) * r = s ∧
      (r : E) ∈ Algebra.adjoin ℝ ({s} : Set E) ∧
      ((r⁻¹ : Eˣ) : E) ∈ Algebra.adjoin ℝ ({s} : Set E) ∧
      (∀ x : E, Commute x s → Commute x r ∧ Commute x ((r⁻¹ : Eˣ) : E)) ∧
      ∀ r' : E, IsRosatiPositive t r' → r' * r' = s → r' = r := by
  have : StarModule ℝ E := starModule_of_trace_mul_star_pos t hpos
  let t' : E →ₗ[ℝ] ℝ := (t.comp (selfAdjoint.submodule ℝ E).subtype).comp (selfAdjointPart ℝ)
  have hiff (a : E) : IsRosatiPositive t' a ↔ IsRosatiPositive t a :=
    isRosatiPositive_iff_of_symmetrize (comp_selfAdjointPart_apply t) hcyclic
  obtain ⟨hsU, r, hrpos, hrsq, hrmem, hrImem, hcomm, huniq⟩ :=
    rosatiPositiveSquareRoot_of_star_invariant t'
      (comp_selfAdjointPart_cyclic hcyclic)
      (comp_selfAdjointPart_star t)
      (fun _ hx ↦ comp_selfAdjointPart_mul_star_pos hpos hx)
      s ((hiff s).mpr hs)
  exact ⟨hsU, r, (hiff r).mp hrpos, hrsq, hrmem, hrImem, hcomm,
    fun r' hr' hr'sq ↦ huniq r' ((hiff r').mpr hr') hr'sq⟩

end SquareRoot

end TauCeti

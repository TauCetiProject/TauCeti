/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Scheme.CodimensionOnePoint
public import TauCeti.AlgebraicGeometry.WeilDivisor.Basic
public import Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic

/-!
# Weil divisors on schemes

This file specializes the combinatorial type `WeilDivisor` to schemes. A prime divisor is
represented by its generic point, which is a point of codimension one, and a scheme-theoretic
Weil divisor is a finite formal integer sum of such points. This is the usual group `Div X` of
Hartshorne II.6 (the free abelian group on the prime divisors) for Noetherian `X`, and it agrees
with Stacks 0BE2 when `X` is quasi-compact. In general the Stacks Project allows locally finite,
possibly infinite, sums of prime divisors, and these finite sums form a subgroup of that group,
which can be proper.

Mathlib's `AlgebraicCycle X ℤ` allows locally finite support in every codimension, and its
Weil divisors `AlgebraicCycle.weilDivisors X ℤ` are the cycles supported in codimension one
(`AlgebraicCycle.IsWeilDivisor`), with locally finite support. The map
`SchemeWeilDivisor.toAlgebraicCycle` extends a Weil divisor by zero away from codimension one.
Its image is characterized by `finiteCodimensionOneCycles`, the subgroup of Weil divisors in
Mathlib's sense with finite support, and `SchemeWeilDivisor.equivFiniteCodimensionOneCycles`
identifies the two descriptions. On a quasi-compact scheme every cycle has finite support, so
there `finiteCodimensionOneCycles X` is all of `AlgebraicCycle.weilDivisors X ℤ`.

The coefficient, support, effectivity, and point-divisor API is inherited directly from
`WeilDivisor`; no scheme-specific copies of those declarations are introduced. The
codimension-one points themselves are supplied by
`TauCeti.AlgebraicGeometry.CodimensionOnePoint`.

This supplies the scheme-theoretic codimension-one specialization used to construct principal
divisors from `Scheme.ord`.
-/

public section

open Order AlgebraicGeometry

namespace TauCeti

namespace AlgebraicGeometry

universe u

/-- A Weil divisor on a scheme is a finite formal integer sum of its codimension-one points.
This is the standard group of divisors for a Noetherian scheme; for a scheme that is not
quasi-compact it is the finitely supported subgroup of the locally finite divisors of the Stacks
Project. -/
abbrev SchemeWeilDivisor (X : Scheme.{u}) : Type u :=
  WeilDivisor (CodimensionOnePoint X)

namespace SchemeWeilDivisor

variable {X : Scheme.{u}}

noncomputable section

/-- Regard a finitely supported function as an algebraic cycle. -/
private def algebraicCycleOfFinsupp : (X →₀ ℤ) →+ AlgebraicCycle X ℤ where
  toFun D :=
    { toFun := D
      supportWithinDomain' := Set.subset_univ _
      supportLocallyFiniteWithinDomain' := fun _ _ ↦
        ⟨Set.univ, Filter.univ_mem, by simp⟩ }
  map_zero' := by
    ext
    simp
  map_add' D E := by
    ext
    simp

@[simp]
private lemma algebraicCycleOfFinsupp_apply (D : X →₀ ℤ) (x : X) :
    algebraicCycleOfFinsupp D x = D x :=
  rfl

/-- Extend a scheme-theoretic Weil divisor by zero away from codimension one, obtaining
an algebraic cycle on the underlying scheme. -/
def toAlgebraicCycle : SchemeWeilDivisor X →+ AlgebraicCycle X ℤ :=
  algebraicCycleOfFinsupp.comp <|
    Finsupp.embDomain.addMonoidHom (Function.Embedding.subtype fun x : X ↦ coheight x = 1)

/-- Extension by zero preserves the coefficient at a codimension-one point. -/
@[simp]
lemma toAlgebraicCycle_apply (D : SchemeWeilDivisor X) (x : CodimensionOnePoint X) :
    toAlgebraicCycle D x = D x :=
  Finsupp.embDomain_apply_self _ D x

/-- Extension by zero vanishes at points whose codimension is not one. -/
@[simp]
lemma toAlgebraicCycle_apply_of_coheight_ne_one (D : SchemeWeilDivisor X) (x : X)
    (hx : coheight x ≠ 1) :
    toAlgebraicCycle D x = 0 := by
  rw [toAlgebraicCycle, AddMonoidHom.comp_apply, algebraicCycleOfFinsupp_apply]
  exact Finsupp.embDomain_of_notMem_range _ _ _ (by simpa)

/-- The support of a scheme-theoretic Weil divisor viewed as an algebraic cycle is the image of
its finite support under the inclusion of codimension-one points. -/
lemma support_toAlgebraicCycle (D : SchemeWeilDivisor X) : (toAlgebraicCycle D).support =
      Subtype.val '' (D.support : Set (CodimensionOnePoint X)) := by
  ext x
  constructor
  · intro hx
    by_cases hx₁ : coheight x = 1
    · refine ⟨⟨x, hx₁⟩, ?_, rfl⟩
      exact Finsupp.mem_support_iff.mpr <| by
        rwa [← toAlgebraicCycle_apply D ⟨x, hx₁⟩]
    · exact (hx (toAlgebraicCycle_apply_of_coheight_ne_one D x hx₁)).elim
  · rintro ⟨x, hx, rfl⟩
    simpa [Function.mem_support] using hx

/-- A scheme-theoretic Weil divisor has finite support when regarded as an algebraic cycle. -/
lemma finite_support_toAlgebraicCycle (D : SchemeWeilDivisor X) :
    (toAlgebraicCycle D).support.Finite := by
  rw [support_toAlgebraicCycle]
  exact D.support.finite_toSet.image Subtype.val

/-- The cycle associated to a scheme-theoretic Weil divisor is a Weil divisor in Mathlib's sense:
it is supported in codimension one. -/
lemma isWeilDivisor_toAlgebraicCycle (D : SchemeWeilDivisor X) :
    (toAlgebraicCycle D).IsWeilDivisor := by
  rw [AlgebraicCycle.isWeilDivisor_iff, support_toAlgebraicCycle]
  rintro _ ⟨x, _, rfl⟩
  exact x.property

/-- Extension by zero embeds scheme-theoretic Weil divisors into algebraic cycles. -/
lemma toAlgebraicCycle_injective :
    Function.Injective (toAlgebraicCycle : SchemeWeilDivisor X → AlgebraicCycle X ℤ) := by
  intro D E h
  apply Finsupp.ext
  intro x
  have hx := congrArg (fun C : AlgebraicCycle X ℤ ↦ C x) h
  simpa only [toAlgebraicCycle_apply] using hx

/-- Two scheme-theoretic Weil divisors have the same associated cycle exactly when they are
equal. -/
@[simp]
lemma toAlgebraicCycle_inj {D E : SchemeWeilDivisor X} :
    toAlgebraicCycle D = toAlgebraicCycle E ↔ D = E :=
  toAlgebraicCycle_injective.eq_iff

/-- Algebraic cycles with finite support contained in codimension one: the Weil divisors in
Mathlib's sense (`AlgebraicCycle.IsWeilDivisor`) with finite support. -/
def finiteCodimensionOneCycles (X : Scheme.{u}) : AddSubgroup (AlgebraicCycle X ℤ) where
  carrier := {C | C.support.Finite ∧ C.IsWeilDivisor}
  zero_mem' :=
    ⟨by simp [Function.locallyFinsuppWithin.support], AlgebraicCycle.isWeilDivisor_zero⟩
  add_mem' {C D} hC hD :=
    ⟨(hC.1.union hD.1).subset (Function.support_add (C : X → ℤ) D), hC.2.add hD.2⟩
  neg_mem' {C} hC :=
    ⟨by simpa only [Function.locallyFinsuppWithin.support_neg] using hC.1, hC.2.neg⟩

/-- Membership in `finiteCodimensionOneCycles` means finite support and support contained in
codimension one. -/
@[simp]
lemma mem_finiteCodimensionOneCycles_iff {C : AlgebraicCycle X ℤ} :
    C ∈ finiteCodimensionOneCycles X ↔ C.support.Finite ∧ C.IsWeilDivisor :=
  Iff.rfl

/-- Restrict a finite codimension-one cycle to its codimension-one points. -/
private def ofFiniteCodimensionOneCycle (C : finiteCodimensionOneCycles X) :
    SchemeWeilDivisor X :=
  Finsupp.ofSupportFinite (fun x ↦ (C : AlgebraicCycle X ℤ) x) <| by
    convert Set.Finite.preimage_embedding
      (Function.Embedding.subtype fun x : X ↦ coheight x = 1) C.property.1 using 1
    ext
    rfl

@[simp]
private lemma ofFiniteCodimensionOneCycle_apply
    (C : finiteCodimensionOneCycles X) (x : CodimensionOnePoint X) :
    ofFiniteCodimensionOneCycle C x = C.1 x :=
  congrFun Finsupp.ofSupportFinite_coe x

/-- Scheme-theoretic Weil divisors are additively equivalent to the finite algebraic cycles
supported entirely in codimension one. -/
def equivFiniteCodimensionOneCycles :
    SchemeWeilDivisor X ≃+ finiteCodimensionOneCycles X where
  toFun D :=
    ⟨toAlgebraicCycle D, finite_support_toAlgebraicCycle D, isWeilDivisor_toAlgebraicCycle D⟩
  invFun := ofFiniteCodimensionOneCycle
  left_inv D := by
    apply Finsupp.ext
    intro x
    calc
      ofFiniteCodimensionOneCycle
          ⟨toAlgebraicCycle D, finite_support_toAlgebraicCycle D,
            isWeilDivisor_toAlgebraicCycle D⟩ x =
          toAlgebraicCycle D x :=
        ofFiniteCodimensionOneCycle_apply _ x
      _ = D x := toAlgebraicCycle_apply D x
  right_inv C := by
    apply Subtype.ext
    apply Function.locallyFinsuppWithin.ext
    intro x
    by_cases hx : coheight x = 1
    · calc
        toAlgebraicCycle (ofFiniteCodimensionOneCycle C) x =
            ofFiniteCodimensionOneCycle C ⟨x, hx⟩ :=
          toAlgebraicCycle_apply _ ⟨x, hx⟩
        _ = C.1 x := ofFiniteCodimensionOneCycle_apply C ⟨x, hx⟩
    · rw [toAlgebraicCycle_apply_of_coheight_ne_one _ _ hx]
      exact (Function.notMem_support.mp fun h ↦ hx (C.property.2.coheight_eq_one h)).symm
  map_add' D E := by
    apply Subtype.ext
    exact (toAlgebraicCycle : SchemeWeilDivisor X →+ AlgebraicCycle X ℤ).map_add D E

/-- The forward direction of `equivFiniteCodimensionOneCycles` is extension by zero. -/
@[simp]
lemma coe_equivFiniteCodimensionOneCycles_apply (D : SchemeWeilDivisor X) :
    ((equivFiniteCodimensionOneCycles D : finiteCodimensionOneCycles X) :
      AlgebraicCycle X ℤ) =
      toAlgebraicCycle D :=
  (rfl)

/-- The inverse of `equivFiniteCodimensionOneCycles` recovers coefficients by restriction to
codimension-one points. -/
@[simp]
lemma equivFiniteCodimensionOneCycles_symm_apply_apply
    (C : finiteCodimensionOneCycles X) (x : CodimensionOnePoint X) :
    equivFiniteCodimensionOneCycles.symm C x = C.1 x :=
  ofFiniteCodimensionOneCycle_apply C x

end

end SchemeWeilDivisor

end AlgebraicGeometry

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Defs

/-!
# Lifting linear independence by expanding coefficients

Suppose the image of a scalar semiring `S` in an algebra `A` lies in the `R`-span of a family `γ`,
and let `β` be a family in an `A`-module `M`. If the products `γ m • β i` are linearly independent
over `R`, then `β` is linearly independent over `S`, provided `S` acts faithfully on `A`. This
reduces independence over `S` to independence over `R` by expanding the coefficients in the
spanning family. When `γ` spans `S` itself, `S` need not be commutative: this is the converse of
Mathlib's `linearIndependent_smul` for a spanning family of scalars.
-/

public section

namespace LinearIndependent

open Finsupp

/-- If every element of `S` is an `R`-linear combination of a family `γ` in `A`, and the
products `γ m • β i` are linearly independent over `R`, then `β` is linearly independent over `S`.
The scalar map from `S` to `A` must be injective. -/
theorem of_smul_of_algebraMap_mem_span {R S A M : Type*} [Semiring R] [CommSemiring S]
    [Semiring A] [Algebra S A] [FaithfulSMul S A] [AddCommMonoid M] [Module A M] [Module S M]
    [IsScalarTower S A M] [Module R A] [Module R M] [IsScalarTower R A M]
    {κ ι : Type*} {γ : κ → A} {β : ι → M}
    (h : LinearIndependent R fun p : κ × ι ↦ γ p.1 • β p.2)
    (hγ : ∀ x : S, algebraMap S A x ∈ Submodule.span R (Set.range γ)) :
    LinearIndependent S β := by
  rw [← linearIndependent_equiv' (.prodComm ..) (g := fun p : ι × κ ↦ γ p.2 • β p.1) rfl,
    LinearIndependent, linearCombination_smul] at h
  simp only [LinearMap.coe_comp, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe,
    ← Function.comp_assoc] at h
  -- `linearCombination A β` is injective on coefficient families with entries in `span R γ`
  have hinj : Set.InjOn (linearCombination A β)
      (Set.range (mapRange.linearMap (linearCombination R γ))) :=
    (h.of_comp_right (curryLinearEquiv R).surjective).injOn_range
  -- coefficient families from `S`, mapped into `A`, are such families
  have hrange (f : ι →₀ S) : f.mapRange (algebraMap S A) (map_zero _) ∈
      Set.range (mapRange.linearMap (linearCombination R γ)) := by
    simp only [Set.mem_range, mapRange.linearMap_apply]
    rw [← Set.mem_range, range_mapRange]
    exact fun i ↦ by simpa [← range_linearCombination] using hγ (f i)
  -- and mapping them into `A` does not change their combination of `β`
  have hlc (f : ι →₀ S) : linearCombination A β (f.mapRange (algebraMap S A) (map_zero _)) =
      linearCombination S β f := by
    simp [linearCombination_apply, sum_mapRange_index, algebraMap_smul]
  intro f g hfg
  refine mapRange_injective _ (map_zero _) (FaithfulSMul.algebraMap_injective S A)
    (hinj (hrange f) (hrange g) ?_)
  simpa [hlc] using hfg

/-- If a family `γ` spans the scalar semiring `S` over `R` and the products `γ m • β i` are
linearly independent over `R`, then `β` is linearly independent over `S`. Here `S` can be
noncommutative, as for left coefficients in a noncommutative ambient algebra. -/
theorem of_smul_of_span_eq_top {R S M : Type*} [Semiring R] [Semiring S] [AddCommMonoid M]
    [Module R S] [Module S M] [Module R M] [IsScalarTower R S M]
    {κ ι : Type*} {γ : κ → S} {β : ι → M}
    (h : LinearIndependent R fun p : κ × ι ↦ γ p.1 • β p.2)
    (hγ : Submodule.span R (Set.range γ) = ⊤) :
    LinearIndependent S β := by
  rw [← linearIndependent_equiv' (.prodComm ..) (g := fun p : ι × κ ↦ γ p.2 • β p.1) rfl,
    LinearIndependent, linearCombination_smul] at h
  simp only [LinearMap.coe_comp, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe,
    ← Function.comp_assoc] at h
  refine (h.of_comp_right (curryLinearEquiv R).surjective).of_comp_right ?_
  -- every coefficient family in `S` expands along the spanning family `γ`
  have hs : Function.Surjective (linearCombination R γ) := by
    rw [← LinearMap.range_eq_top, range_linearCombination, hγ]
  exact mapRange_surjective _ (map_zero _) hs

end LinearIndependent

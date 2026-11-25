/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PicardGroup
public import TauCeti.RingTheory.DedekindDomain.SteinitzClass
import TauCeti.RingTheory.FractionalIdeal.LinearEquiv

/-!
# Ideal classes and Steinitz classes as Picard classes

Mathlib's `ClassGroup.equivPic` identifies the ideal class group of a domain `A` with its Picard
group. This file computes it on representatives: an invertible fractional ideal goes to the
Picard class of the underlying invertible `A`-module (`ClassGroup.equivPic_mk`). Over a domain
every invertible module `L` is isomorphic to a non-zero-divisor ideal
(`Module.Invertible.exists_linearEquiv_nonZeroDivisors`). Over a Dedekind domain the Steinitz
class of `L` therefore corresponds to the Picard class of `L` (`ClassGroup.equivPic_steinitzClass`):
the Steinitz class of a rank-one projective is its Picard class, read in ideal-class coordinates.
-/

public section

open scoped nonZeroDivisors
open CommRing

universe u

/-- `ClassGroup.equivPic` sends the class of an invertible fractional ideal `I` to the Picard
class of `I` as an `A`-module. -/
theorem ClassGroup.equivPic_mk {A : Type u} [CommRing A] [IsDomain A]
    (I : (FractionalIdeal A⁰ (FractionRing A))ˣ) :
    ClassGroup.equivPic A (ClassGroup.mk (FractionRing A) I) =
      Pic.mk A (FractionalIdeal.unitsMulEquivSubmodule I : Submodule A (FractionRing A)) := by
  rw [← ClassGroup.Quot_mk_eq_mk]
  -- `ClassGroup.equivPic` is defined by sending the class of `I` to the Picard class of `I`.
  -- Mathlib has no `_mk` lemmas for its components, and rewriting with its `simps` lemma
  -- `ClassGroup.equivPic_apply` fails: the resulting term is not type-correct at reducible
  -- transparency, as Mathlib records at `ClassGroup.equivPic`. So we unfold definitionally.
  rfl

/-- If `FractionRing A` has trivial Picard group, for instance if `A` is a domain, every invertible
`A`-module is isomorphic to an ideal that is a non-zero-divisor in the monoid of ideals. -/
theorem Module.Invertible.exists_linearEquiv_nonZeroDivisors {A : Type u} [CommRing A]
    [Subsingleton (Pic (FractionRing A))] (M : Type*) [AddCommGroup M] [Module A M]
    [Module.Invertible A M] : ∃ I : (Ideal A)⁰, Nonempty (M ≃ₗ[A] (I : Ideal A)) := by
  obtain ⟨I, ⟨e⟩⟩ := Module.Invertible.exists_linearEquiv_ideal A M
  -- An ideal `J` with `J * I = 0` annihilates `I`, hence the faithful module `M`, so `J = 0`.
  refine ⟨⟨I, mem_nonZeroDivisors_iff_right.mpr fun J hJ ↦ ?_⟩, ⟨e⟩⟩
  refine (Submodule.eq_bot_iff J).mpr fun j hj ↦ eq_of_smul_eq_smul (α := M) fun m ↦ ?_
  refine e.injective (Subtype.ext ?_)
  simpa [hJ] using Ideal.mul_mem_mul hj (e m).property

/-- Over a Dedekind domain the Steinitz class of an invertible module `L` corresponds to the
Picard class of `L` under `ClassGroup.equivPic`. -/
theorem ClassGroup.equivPic_steinitzClass {A : Type u} [CommRing A] [IsDedekindDomain A]
    (L : Pic A) : ClassGroup.equivPic A (Module.steinitzClass A L) = L := by
  obtain ⟨I, ⟨e⟩⟩ := Module.Invertible.exists_linearEquiv_nonZeroDivisors (A := A) L
  rw [Module.steinitzClass_congr e, Module.steinitzClass_ideal,
    ← ClassGroup.mk_mk0 (FractionRing A), ClassGroup.equivPic_mk, Pic.mk_eq_iff]
  exact ⟨(FractionalIdeal.coeIdealEquiv (S := A⁰) (P := FractionRing A) (I : Ideal A)).trans e.symm⟩

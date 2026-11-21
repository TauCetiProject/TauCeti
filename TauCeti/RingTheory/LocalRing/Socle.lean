/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Injective
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.SimpleModule.Basic

import Mathlib.RingTheory.Nakayama
import TauCeti.Algebra.Module.Injective.SelfInjective

/-!
# The socle of a module over a local ring

Over a local ring `R` with maximal ideal `m`, the elements of a module `M` killed by `m` form the
submodule `Submodule.torsionBySet R M m`, the **socle** of `M`. It is an `R ⧸ m`-vector space, and
its simple `R`-submodules are its lines.

When `M` is artinian, the socle is essential: every nonzero submodule of `M` contains a nonzero
element of the socle. Indeed a nonzero submodule contains a minimal nonzero submodule `A`, which
is cyclic, so `m • A < A` by Nakayama's lemma and hence `m • A = 0`.

In a self-injective local ring, every nonzero principal ideal `R x` contains the socle. Indeed, if
`y` is in the socle, any `r` with `r x = 0` is not a unit, so `r ∈ m` and `r y = 0`; the
Ikeda–Nakayama annihilator criterion then puts `y` in `R x`. Hence a self-injective artinian local
ring has a simple socle. This is the `R`-module form of the statement that the socle is
one-dimensional over the residue field; it is the condition under which a finite local ring is its
own Matlis dual.

## Main results

* `TauCeti.IsLocalRing.inf_torsionBySet_maximalIdeal_ne_bot`: in an artinian module over a local
  ring, every nonzero submodule meets the socle.
* `TauCeti.IsLocalRing.torsionBySet_maximalIdeal_ne_bot`: a nonzero artinian module has a nonzero
  socle.
* `TauCeti.IsLocalRing.mem_span_singleton_of_mem_torsionBySet`: in a self-injective local ring,
  every nonzero principal ideal contains the socle.
* `TauCeti.IsLocalRing.isSimpleModule_torsionBySet_maximalIdeal_of_injective`: a self-injective
  artinian local ring has a simple socle.

## References

* T. Y. Lam, *Lectures on modules and rings*, Graduate Texts in Mathematics 189, Springer, 1999,
  §3D and Theorem 15.27.
-/

public section

namespace TauCeti.IsLocalRing

open _root_.IsLocalRing Submodule

variable {R : Type*} [CommRing R] [IsLocalRing R]

section Module

variable {M : Type*} [AddCommGroup M] [Module R M]

/-- **The socle is essential.** In an artinian module over a local ring, every nonzero submodule
contains a nonzero element killed by the maximal ideal. -/
theorem inf_torsionBySet_maximalIdeal_ne_bot [IsArtinian R M] {N : Submodule R M} (hN : N ≠ ⊥) :
    N ⊓ torsionBySet R M (maximalIdeal R) ≠ ⊥ := by
  obtain ⟨A, hA, hAN⟩ := (eq_bot_or_exists_atom_le N).resolve_left hN
  obtain ⟨a, haA, ha⟩ := exists_mem_ne_zero_of_ne_bot hA.1
  have hspan : span R {a} = A :=
    hA.le_iff.mp ((span_singleton_le_iff_mem a A).mpr haA) |>.resolve_left
      (span_singleton_eq_bot.not.mpr ha)
  -- the minimal submodule `A` is cyclic, so Nakayama's lemma gives `m • A < A`, hence `m • A = 0`
  have hsmul : maximalIdeal R • A = ⊥ := by
    refine (hA.le_iff.mp smul_le_right).resolve_right fun h ↦ hA.1 ?_
    exact eq_bot_of_le_smul_of_le_jacobson _ A (hspan ▸ fg_span_singleton a) h.ge
      (ringJacobson_eq_maximalIdeal (R := R)).ge
  refine (Submodule.ne_bot_iff _).mpr ⟨a, ⟨hAN haA, ?_⟩, ha⟩
  refine (mem_torsionBySet_iff _ _).mpr fun r ↦ ?_
  rw [← mem_bot R, ← hsmul]
  exact smul_mem_smul r.property haA

/-- A nonzero artinian module over a local ring has a nonzero socle. -/
theorem torsionBySet_maximalIdeal_ne_bot [IsArtinian R M] [Nontrivial M] :
    torsionBySet R M (maximalIdeal R) ≠ ⊥ := by
  simpa using inf_torsionBySet_maximalIdeal_ne_bot (N := (⊤ : Submodule R M)) top_ne_bot

end Module

/-- An element of a local ring which does not kill an element of the socle is a unit. -/
theorem isUnit_of_mul_ne_zero_of_mem_torsionBySet {x r : R}
    (hx : x ∈ torsionBySet R R (maximalIdeal R)) (hrx : r * x ≠ 0) : IsUnit r := by
  by_contra hr
  exact hrx ((mem_torsionBySet_iff _ _).mp hx ⟨r, (mem_maximalIdeal r).mpr hr⟩)

/-- In a self-injective local ring, every nonzero principal ideal contains the socle. -/
theorem mem_span_singleton_of_mem_torsionBySet [Module.Injective R R] {x y : R} (hx0 : x ≠ 0)
    (hy : y ∈ torsionBySet R R (maximalIdeal R)) : y ∈ Ideal.span {x} := by
  -- an `r` with `r * y ≠ 0` is a unit, so it does not kill `x ≠ 0`
  obtain ⟨c, hc⟩ := exists_eq_sum_mul_of_forall_mul_eq_zero (ι := Unit) (a := fun _ ↦ x) (x := y)
    fun r hr ↦ by_contra fun hry ↦
      hx0 ((isUnit_of_mul_ne_zero_of_mem_torsionBySet hy hry).mul_right_eq_zero.mp (hr ()))
  exact Ideal.mem_span_singleton.mpr ⟨c (), by simpa using hc⟩

/-- **A self-injective artinian local ring has a simple socle**: the ideal of elements killed by
the maximal ideal is a simple module, that is, a line over the residue field. -/
theorem isSimpleModule_torsionBySet_maximalIdeal_of_injective [IsArtinianRing R]
    [Module.Injective R R] : IsSimpleModule R (torsionBySet R R (maximalIdeal R)) := by
  rw [isSimpleModule_iff_isAtom]
  refine ⟨torsionBySet_maximalIdeal_ne_bot, fun J hJ ↦ ?_⟩
  by_contra hJ0
  obtain ⟨x, hxJ, hx0⟩ := exists_mem_ne_zero_of_ne_bot hJ0
  refine hJ.ne (le_antisymm hJ.le fun y hy ↦ ?_)
  obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp (mem_span_singleton_of_mem_torsionBySet hx0 hy)
  exact J.smul_mem r hxJ

end TauCeti.IsLocalRing

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

/-!
# The socle of a module over a local ring

Over a local ring `R` with maximal ideal `m`, the elements of a module `M` killed by `m` form the
submodule `Submodule.torsionBySet R M m`, the **socle** of `M`. It is an `R ⧸ m`-vector space, and
its simple `R`-submodules are its lines.

When `M` is artinian, the socle is essential: every nonzero submodule of `M` contains a nonzero
element of the socle. Indeed a nonzero submodule contains a minimal nonzero submodule `A`, which
is cyclic, so `m • A < A` by Nakayama's lemma and hence `m • A = 0`.

A self-injective artinian local ring has a simple socle. If `x` and `y` are nonzero elements of
the socle with `y ∉ R x`, then `R x` embeds in `R ⧸ R y`, and self-injectivity extends this
embedding to an endomorphism of `R`, a multiplication by some `r`, with `r x = x` and `r y = 0`.
The first equation forces `r ∉ m`, so `r` is a unit, which contradicts the second. This is the
`R`-module form of the statement that the socle is one-dimensional over the residue field; it is
the condition under which a finite local ring is its own Matlis dual.

## Main results

* `IsLocalRing.inf_torsionBySet_maximalIdeal_ne_bot`: in an artinian module over a local ring,
  every nonzero submodule meets the socle.
* `IsLocalRing.torsionBySet_maximalIdeal_ne_bot`: a nonzero artinian module has a nonzero socle.
* `IsLocalRing.isSimpleModule_torsionBySet_maximalIdeal_of_injective`: a self-injective artinian
  local ring has a simple socle.

## References

* T. Y. Lam, *Lectures on modules and rings*, Graduate Texts in Mathematics 189, Springer, 1999,
  §3D and Theorem 15.27.
-/

public section

namespace IsLocalRing

open Submodule

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

/-- An element of a local ring which does not kill a nonzero element of the socle is a unit. -/
private theorem isUnit_of_mul_ne_zero {x r : R} (hx : x ∈ torsionBySet R R (maximalIdeal R))
    (hrx : r * x ≠ 0) : IsUnit r := by
  by_contra hr
  exact hrx ((mem_torsionBySet_iff _ _).mp hx ⟨r, (mem_maximalIdeal r).mpr hr⟩)

/-- In a self-injective local ring, any two nonzero elements of the socle generate the same
ideal. -/
private theorem mem_span_singleton_of_mem_torsionBySet [Module.Injective R R] {x y : R}
    (hx : x ∈ torsionBySet R R (maximalIdeal R)) (hx0 : x ≠ 0)
    (hy : y ∈ torsionBySet R R (maximalIdeal R)) (hy0 : y ≠ 0) :
    y ∈ Ideal.span {x} := by
  by_contra hyx
  -- `R x` embeds in `R ⧸ R y`: a nonzero element `r x` of `R x` lying in `R y` would make `r`
  -- a unit, and then `x ∈ R y`; as `x = s y` with `s` a unit too, this would give `y ∈ R x`
  let ι : Ideal.span {x} →ₗ[R] R ⧸ Ideal.span {y} :=
    (Ideal.span {y}).mkQ ∘ₗ (Ideal.span {x}).subtype
  have hι : Function.Injective ι := by
    refine (injective_iff_map_eq_zero ι).mpr fun ⟨z, hz⟩ hz0 ↦ ?_
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hz
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.mp ((Ideal.Quotient.eq_zero_iff_mem).mp hz0)
    simp only [Submodule.subtype_apply] at hs
    by_contra hrx
    have hrx : r * x ≠ 0 := fun h ↦ hrx (Subtype.ext h)
    have hs0 : s * y ≠ 0 := hs ▸ hrx
    obtain ⟨u, hu⟩ := isUnit_of_mul_ne_zero hx hrx
    obtain ⟨v, hv⟩ := isUnit_of_mul_ne_zero hy hs0
    refine hyx (Ideal.mem_span_singleton'.mpr ⟨↑(v⁻¹ * u), ?_⟩)
    rw [Units.val_mul, mul_assoc, hu, ← hs, ← hv, ← mul_assoc, Units.inv_mul, one_mul]
  obtain ⟨g, hg⟩ := Module.Injective.extension_property R R _ _ ι hι (Ideal.span {x}).subtype
  -- the extension `g ∘ mkQ` is multiplication by `r = g 1`, with `r x = x` and `r y = 0`
  set r := g (Submodule.Quotient.mk (p := Ideal.span {y}) 1)
  have hg' (z : R) : g (Submodule.Quotient.mk z) = r * z := by
    rw [mul_comm, ← smul_eq_mul, ← map_smul, ← Submodule.Quotient.mk_smul, smul_eq_mul, mul_one]
  have hgx : r * x = x := by
    rw [← hg']
    simpa [ι] using LinearMap.congr_fun hg ⟨x, Ideal.mem_span_singleton_self x⟩
  have hgy : r * y = 0 := by
    rw [← hg', (Submodule.Quotient.mk_eq_zero _).mpr (Ideal.mem_span_singleton_self y), map_zero]
  obtain ⟨u, hu⟩ := isUnit_of_mul_ne_zero hx (hgx.symm ▸ hx0)
  exact hy0 (by rw [← hu] at hgy; exact (Units.mul_right_eq_zero u).mp hgy)

/-- **A self-injective artinian local ring has a simple socle**: the ideal of elements killed by
the maximal ideal is a simple module, that is, a line over the residue field. -/
theorem isSimpleModule_torsionBySet_maximalIdeal_of_injective [IsArtinianRing R]
    [Module.Injective R R] : IsSimpleModule R (torsionBySet R R (maximalIdeal R)) := by
  rw [isSimpleModule_iff_isAtom]
  refine ⟨torsionBySet_maximalIdeal_ne_bot, fun J hJ ↦ ?_⟩
  by_contra hJ0
  obtain ⟨x, hxJ, hx0⟩ := exists_mem_ne_zero_of_ne_bot hJ0
  refine hJ.ne (le_antisymm hJ.le fun y hy ↦ ?_)
  by_cases hy0 : y = 0
  · exact hy0 ▸ J.zero_mem
  · obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp
      (mem_span_singleton_of_mem_torsionBySet (hJ.le hxJ) hx0 hy hy0)
    exact J.smul_mem r hxJ

end IsLocalRing

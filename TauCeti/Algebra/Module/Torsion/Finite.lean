/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# Finiteness for modules killed by a scalar

If an `S`-module is killed by `f`, its scalar action factors through `S ⧸ (f)`. Thus a finite
`S`-module killed by `f` is finite over a coefficient semiring `A` whenever `S ⧸ (f)` is finite
over `A`. This transfers quotient-finiteness results to modules annihilated by distinguished
power series.

In addition, any finitely generated `S`-torsion module over a commutative semiring is uniformly
annihilated by a single element of `S` (`Module.IsTorsion'.exists_isTorsionBy_of_finite`),
obtained as the product of annihilators of a finite generating set.
-/

public section

namespace Module.IsTorsionBy

/-- A finite `S`-module killed by `f` is finite over `A` if `S ⧸ (f)` is finite over `A`. -/
theorem finite_of_finite_quotient {A S M : Type*} [CommSemiring A] [CommRing S] [Algebra A S]
    [AddCommGroup M] [Module S M] [Module A M] [IsScalarTower A S M] [Module.Finite S M]
    {f : S} (h : Module.IsTorsionBy S M f) [Module.Finite A (S ⧸ Ideal.span {f})] :
    Module.Finite A M := by
  have hM : Module.IsTorsionBySet S M (Ideal.span {f}) :=
    (Module.isTorsionBySet_span_singleton_iff f).mpr h
  let := hM.module
  have : IsScalarTower A (S ⧸ Ideal.span {f}) M := hM.isScalarTower
  have : Module.Finite (S ⧸ Ideal.span {f}) M := Module.Finite.of_restrictScalars_finite S _ M
  exact Module.Finite.trans (S ⧸ Ideal.span {f}) M

end Module.IsTorsionBy

namespace Module.IsTorsion'

/-- A finitely generated `S`-torsion module over a commutative semiring is uniformly annihilated by
a single element of `S`, namely the product of annihilators of a finite generating set. -/
theorem exists_isTorsionBy_of_finite {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
    {S : Submonoid R} [Module.Finite R M] (hM : Module.IsTorsion' M S) :
    ∃ s ∈ S, Module.IsTorsionBy R M s := by
  classical
  obtain ⟨G, hG⟩ := Module.Finite.fg_top (R := R) (M := M)
  choose s hs using fun g : G ↦ @hM g.val
  let r : R := ∏ g ∈ G.attach, (s g : R)
  refine ⟨r, S.prod_mem fun g _ ↦ (s g).property, ?_⟩
  rw [Module.isTorsionBy_iff_torsionBy_eq_top, eq_top_iff, ← hG, Submodule.span_le]
  intro x hx
  obtain ⟨c, hc⟩ :=
    Finset.dvd_prod_of_mem (fun g : G ↦ (s g : R)) (Finset.mem_attach G ⟨x, hx⟩)
  have hx0 : (s ⟨x, hx⟩ : R) • x = 0 := hs ⟨x, hx⟩
  have hrx : r • x = 0 := by
    dsimp only [r]
    rw [hc, mul_comm, mul_smul]
    simp [hx0]
  simpa [SetLike.mem_coe, Submodule.mem_torsionBy_iff] using hrx

end Module.IsTorsion'

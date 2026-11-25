/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients.Basic

/-!
# Finiteness for modules killed by a scalar

If an `S`-module is killed by `f`, its scalar action factors through `S ⧸ (f)`. Thus a finite
`S`-module killed by `f` is finite over a coefficient semiring `A` whenever `S ⧸ (f)` is finite
over `A`. This transfers quotient-finiteness results to modules annihilated by distinguished
power series.

Over a ring with finite quotients by nonzero ideals, such as the ring of integers of a number
field, a finitely generated torsion module is killed by a nonzero divisor, hence is a finitely
generated module over a finite ring, so it is a finite set (`Module.IsTorsion.finite`). This
generalizes Mathlib's `Module.finite_of_fg_torsion` over `ℤ`.
-/

public section

namespace Module.IsTorsionBy

/-- A finite `S`-module killed by `f` is finite over `S ⧸ (f)`, for the `S ⧸ (f)`-module structure
given by `Module.IsTorsionBySet.module`. -/
theorem finite_quotient {S M : Type*} [CommRing S] [AddCommGroup M] [Module S M]
    [Module.Finite S M] {f : S} (h : Module.IsTorsionBy S M f) :
    letI := ((Module.isTorsionBySet_span_singleton_iff f).mpr h).module
    Module.Finite (S ⧸ Ideal.span {f}) M :=
  letI := ((Module.isTorsionBySet_span_singleton_iff f).mpr h).module
  .of_restrictScalars_finite S _ M

/-- A finite `S`-module killed by `f` is finite over `A` if `S ⧸ (f)` is finite over `A`. -/
theorem finite_of_finite_quotient {A S M : Type*} [CommSemiring A] [CommRing S] [Algebra A S]
    [AddCommGroup M] [Module S M] [Module A M] [IsScalarTower A S M] [Module.Finite S M]
    {f : S} (h : Module.IsTorsionBy S M f) [Module.Finite A (S ⧸ Ideal.span {f})] :
    Module.Finite A M := by
  have hM := (Module.isTorsionBySet_span_singleton_iff f).mpr h
  let := hM.module
  have : IsScalarTower A (S ⧸ Ideal.span {f}) M := hM.isScalarTower
  have : Module.Finite (S ⧸ Ideal.span {f}) M := h.finite_quotient
  exact Module.Finite.trans (S ⧸ Ideal.span {f}) M

end Module.IsTorsionBy

namespace Module.IsTorsion

/-- **A finitely generated torsion module over a ring with finite quotients is finite.** A nonzero
divisor `d` annihilates the module, which is then a finitely generated module over the finite ring
`R ⧸ (d)`. -/
theorem finite {R M : Type*} [CommRing R] [Ring.HasFiniteQuotients R] [AddCommGroup M]
    [Module R M] [Module.Finite R M] (hM : Module.IsTorsion R M) : Finite M := by
  obtain _ | _ := subsingleton_or_nontrivial R
  · have := Module.subsingleton R M
    infer_instance
  obtain ⟨d, hd, hd0⟩ := Submodule.annihilator_top_inter_nonZeroDivisors hM
  have hdM : Module.IsTorsionBy R M d := fun m => Submodule.mem_annihilator.1 hd m Submodule.mem_top
  have : Finite (R ⧸ Ideal.span {d}) :=
    Ring.HasFiniteQuotients.finiteQuotient (by simpa using nonZeroDivisors.ne_zero hd0)
  let := ((Module.isTorsionBySet_span_singleton_iff d).mpr hdM).module
  have : Module.Finite (R ⧸ Ideal.span {d}) M := hdM.finite_quotient
  exact Module.finite_of_finite (R ⧸ Ideal.span {d})

end Module.IsTorsion

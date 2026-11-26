/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.BilinearForm.SymplecticBasis
public import TauCeti.NumberTheory.ClassFieldTheory.WeilGroup.Archimedean.IrreducibleDimension
public import TauCeti.RepresentationTheory.Irreducible

/-!
# Irreducible symplectic representations of `W_ℝ` are two-dimensional

A symplectic representation of the Weil group `W_ℝ` is a representation preserving a
nondegenerate alternating bilinear form. If it is irreducible, it is two-dimensional: an
irreducible representation of `W_ℝ` has dimension one or two
(`WeilGroupReal.finrank_le_two_of_isIrreducible`), and a space carrying a nondegenerate
alternating form has even dimension (`LinearMap.BilinForm.IsAlt.even_finrank`); on a line an
alternating form is zero. The invariance of the form is not needed for this.

## Main results

* `TauCeti.ClassFieldTheory.WeilGroupReal.finrank_eq_two_of_isIrreducible_of_isAlt`: an irreducible
  finite-dimensional representation of `W_ℝ` on a space carrying a nondegenerate alternating form
  is two-dimensional.

## References

* A. W. Knapp, *Local Langlands correspondence: the archimedean case*, in *Motives*,
  Proc. Sympos. Pure Math. 55, Part 2 (1994), §3.
-/

public section

open Module Representation

namespace TauCeti.ClassFieldTheory

namespace WeilGroupReal

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- **Irreducible symplectic representations of `W_ℝ` are two-dimensional.** An irreducible
finite-dimensional representation of `W_ℝ` on a space carrying a nondegenerate alternating
bilinear form has dimension two, since the dimension is one or two and must be even. In particular
this holds for an irreducible representation preserving such a form. -/
theorem finrank_eq_two_of_isIrreducible_of_isAlt (ρ : Representation ℂ WeilGroupReal V)
    (hρ : ρ.IsIrreducible) {B : LinearMap.BilinForm ℂ V} (hB : B.IsAlt)
    (hnd : B.Nondegenerate) : finrank ℂ V = 2 := by
  have hpos := hρ.finrank_pos
  have hle := finrank_le_two_of_isIrreducible ρ hρ
  obtain ⟨k, hk⟩ := hB.even_finrank hnd
  omega

end WeilGroupReal

end TauCeti.ClassFieldTheory

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DeligneTorus.MumfordTate.Basic
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Conjugation
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Conjugation

/-!
# The Mumford–Tate group under automorphisms and change of basis

Let `h : S → G_ℝ` be a homomorphism from the Deligne torus to the real extension of an affine
group `G` over `ℚ` with coordinate Hopf algebra `H`. Twisting `h` by an automorphism of `G`
defined over `ℚ` moves its Mumford–Tate group by that automorphism. For an inner automorphism,
conjugation by a rational point `g` of `G`, the Mumford–Tate group of the conjugate homomorphism
`g h g⁻¹` (that is, `s ↦ g h(s) g⁻¹`) is the conjugate subgroup `g MT(h) g⁻¹`. In coordinates,
twisting `h` means precomposing it with the real extension of a Hopf automorphism of `H`, and the
Mumford–Tate ideal moves by the inverse image under that automorphism.

For `G = GL_d`, twisting `h` by the coordinate automorphism of conjugation by an invertible
rational matrix `P` conjugates its Mumford–Tate group by the rational point `P`. This is the
coordinate input for showing that the Mumford–Tate group of a rational Hodge structure, computed
in a basis, is well defined up to conjugation.

## Main declarations

* `TauCeti.DeligneTorus.mumfordTateHopfIdeal_innerConjugationIso`: twisting `h` by conjugation by
  a rational point conjugates its Mumford–Tate group by that point.
* `TauCeti.DeligneTorus.mumfordTateHopfIdeal_conjCoordinateIso`: for `G = GL_d`, twisting `h`
  by conjugation by an invertible rational matrix `P` conjugates the Mumford–Tate group by `P`.

## References

* J. S. Milne, *Introduction to Shimura varieties*, §2, p. 31 (the aside after Definition 2.16).
* J. S. Milne, *Algebraic Groups* (2017), §§3.5 and 10.20.
-/

public section

open CategoryTheory _root_.CommHopfAlgCat TauCeti.CommHopfAlgCat

namespace TauCeti.DeligneTorus

variable {H : _root_.CommHopfAlgCat.{0} ℚ}

/-- **Conjugating `h` by a rational point conjugates its Mumford–Tate group.** Twisting `h` by
the coordinate automorphism of conjugation by a rational point `g` of `G` replaces its
Mumford–Tate ideal by the conjugate ideal, which cuts out the conjugate subgroup. -/
theorem mumfordTateHopfIdeal_innerConjugationIso
    (g : HopfAlgebra.points (R := ℚ) (H := H) (CommAlgCat.of ℚ ℚ))
    (h : baseChange (K := ℝ) H ⟶ _root_.CommHopfAlgCat.of ℝ S) :
    mumfordTateHopfIdeal (baseChangeMap (K := ℝ) (H.innerConjugationIso g).hom ≫ h) =
      (mumfordTateHopfIdeal h).conjugate g := by
  rw [← comapOfSurjective_mumfordTateHopfIdeal]
  ext x
  rw [HopfIdeal.mem_conjugate, HopfIdeal.mem_comapOfSurjective,
    ← innerConjugationIso_hom_toAlgHom, BialgHom.coe_toAlgHom]

/-- **Conjugating by a rational matrix conjugates the Mumford–Tate group.** For `G = GL_d`,
twisting `h : S → GL_{d,ℝ}` by the coordinate automorphism of conjugation by an invertible
rational matrix `P` replaces its Mumford–Tate ideal by its conjugate by the rational point `P`.
This is the coordinate input for the change-of-basis behaviour of Mumford–Tate groups. -/
theorem mumfordTateHopfIdeal_conjCoordinateIso {d : ℕ}
    (P : Matrix.GeneralLinearGroup (Fin d) ℚ)
    (h : baseChange (K := ℝ) (GeneralLinear.coordinateHopfAlgebra ℚ d) ⟶
      _root_.CommHopfAlgCat.of ℝ S) :
    mumfordTateHopfIdeal (baseChangeMap (K := ℝ) (GeneralLinear.conjCoordinateIso P).hom ≫ h) =
      (mumfordTateHopfIdeal h).conjugate
        ((GeneralLinear.pointsMulEquiv (R := ℚ) (A := ℚ) d).symm P) := by
  rw [GeneralLinear.conjCoordinateIso_eq_innerConjugationIso]
  exact mumfordTateHopfIdeal_innerConjugationIso _ h

end TauCeti.DeligneTorus

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DeligneTorus.MumfordTate
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Conjugation
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Conjugation

/-!
# The Mumford–Tate group under automorphisms and change of basis

Let `h : S → G_ℝ` be a homomorphism from the Deligne torus to the real extension of an affine
group `G` over `ℚ` with coordinate Hopf algebra `H`. Twisting `h` by an automorphism of `G`
defined over `ℚ` moves its Mumford–Tate group by that automorphism. For an inner automorphism,
conjugation by a rational point `g` of `G`, the Mumford–Tate group of the conjugate homomorphism
`g⁻¹ h g` is the conjugate subgroup. In coordinates, twisting `h` means precomposing it with the
real extension of a Hopf automorphism of `H`, and the Mumford–Tate ideal moves by the inverse
image under that automorphism.

For `G = GL_d`, conjugation by an invertible rational matrix `P` is a change of basis of the
underlying `ℚ`-vector space. So when the homomorphism `h_V` of a rational Hodge structure `V` is
written in a basis of `V`, changing the basis conjugates its Mumford–Tate group inside `GL_d` by
the change-of-basis matrix, and the Mumford–Tate groups computed in any two bases are isomorphic
affine groups over `ℚ`.

## Main declarations

* `TauCeti.DeligneTorus.mumfordTateQuotientIsoOfIso`: for an isomorphism `e : H ≅ L` of
  coordinate Hopf algebras, the coordinate isomorphism between the Mumford–Tate group of `h` and
  that of its twist by `e`.
* `TauCeti.DeligneTorus.mumfordTateHopfIdeal_innerConjugationIso`: twisting `h` by conjugation by
  a rational point conjugates its Mumford–Tate group by that point.
* `TauCeti.DeligneTorus.mumfordTateHopfIdeal_conjCoordinateIso`: for `G = GL_d`, the change of
  basis by an invertible rational matrix `P` conjugates the Mumford–Tate group by `P`.

## References

* J. S. Milne, *Introduction to Shimura varieties*, §2, p. 31 (the aside after Definition 2.16).
* J. S. Milne, *Algebraic Groups* (2017), §§3.5 and 10.20.
-/

public section

open CategoryTheory _root_.CommHopfAlgCat TauCeti.CommHopfAlgCat

namespace TauCeti.DeligneTorus

variable {H L : _root_.CommHopfAlgCat.{0} ℚ}

/-- **The Mumford–Tate groups of `h` and of its twist by an isomorphism are isomorphic.** For an
isomorphism `e : H ≅ L` of coordinate Hopf algebras, contravariantly an isomorphism `G' ≅ G` of
affine groups over `ℚ`, and `h : S → G'_ℝ`, the coordinate isomorphism between the Mumford–Tate
group of the composite `S → G'_ℝ → G_ℝ` and that of `h`, induced by `e`. -/
noncomputable def mumfordTateQuotientIsoOfIso (e : H ≅ L)
    (h : baseChange (K := ℝ) L ⟶ _root_.CommHopfAlgCat.of ℝ S) :
    quotient H (mumfordTateHopfIdeal (baseChangeMap (K := ℝ) e.hom ≫ h)) ≅
      quotient L (mumfordTateHopfIdeal h) :=
  quotientIsoOfComapEq e _ (comapOfSurjective_mumfordTateHopfIdeal e h)

/-- The isomorphism of Mumford–Tate groups induced by `e` commutes with their embeddings into the
ambient groups. -/
@[reassoc (attr := simp)]
theorem mkQuotient_comp_mumfordTateQuotientIsoOfIso_hom (e : H ≅ L)
    (h : baseChange (K := ℝ) L ⟶ _root_.CommHopfAlgCat.of ℝ S) :
    mkQuotient H (mumfordTateHopfIdeal (baseChangeMap (K := ℝ) e.hom ≫ h)) ≫
        (mumfordTateQuotientIsoOfIso e h).hom =
      e.hom ≫ mkQuotient L (mumfordTateHopfIdeal h) :=
  mkQuotient_comp_quotientIsoOfComapEq_hom _ _ _

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
    ← innerConjugationIso_hom_toAlgHom]
  rfl

/-- **Change of basis conjugates the Mumford–Tate group.** For `G = GL_d`, twisting
`h : S → GL_{d,ℝ}` by the coordinate automorphism of conjugation by an invertible rational
matrix `P`, as happens when the basis in which `h` is written changes by `P`, replaces its
Mumford–Tate ideal by its conjugate by the rational point `P`. -/
theorem mumfordTateHopfIdeal_conjCoordinateIso {d : ℕ}
    (P : Matrix.GeneralLinearGroup (Fin d) ℚ)
    (h : baseChange (K := ℝ) (GeneralLinear.coordinateHopfAlgebra ℚ d) ⟶
      _root_.CommHopfAlgCat.of ℝ S) :
    mumfordTateHopfIdeal (baseChangeMap (K := ℝ) (GeneralLinear.conjCoordinateIso P).hom ≫ h) =
      (mumfordTateHopfIdeal h).conjugate
        ((GeneralLinear.pointsMulEquiv (R := ℚ) (A := ℚ) d).symm P) := by
  have hP : ((GeneralLinear.conjCoordinateIso P).hom.hom :
      GeneralLinear.coordinateHopfAlgebra ℚ d →ₐ[ℚ] GeneralLinear.coordinateHopfAlgebra ℚ d) =
        HopfAlgebra.pointConjugationAlgHom
          ((GeneralLinear.pointsMulEquiv (R := ℚ) (A := ℚ) d).symm P) := by
    have h₁ := GeneralLinear.pointsMulEquiv_toConv_comp_conjCoordinateIso P
      (GeneralLinear.coordinateHopfAlgebra ℚ d) (WithConv.toConv (AlgHom.id ℚ _))
    rw [← GeneralLinear.pointsMulEquiv_toConv_comp_pointConjugationAlgHom] at h₁
    simpa using (GeneralLinear.pointsMulEquiv d).injective h₁
  rw [← comapOfSurjective_mumfordTateHopfIdeal]
  ext x
  rw [HopfIdeal.mem_conjugate, HopfIdeal.mem_comapOfSurjective, ← hP]
  rfl

end TauCeti.DeligneTorus

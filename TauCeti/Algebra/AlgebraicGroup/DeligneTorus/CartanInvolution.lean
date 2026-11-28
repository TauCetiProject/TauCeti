/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.CartanInvolution.Conjugation
public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.InnerConjugation
public import TauCeti.Algebra.AlgebraicGroup.DeligneTorus.Basic

/-!
# The Cartan condition for a Deligne torus homomorphism

`TauCeti.DeligneTorus.IsCartanInvolutionAtI.innerConjugationIso_iff` shows that the condition
that conjugation by `h(i)` be a Cartan involution depends only on the real conjugacy
class of the algebraic homomorphism `h`. It uses `CommHopfAlgCat.innerConjugationIso_mul`
and `TauCeti.isCartanInvolution_conj_iff`. Applied to the adjoint-group homomorphism,
this is the conjugacy invariance of the Shimura axiom SV2.

See J. S. Milne, *Introduction to Shimura varieties*, Definition 5.5.
-/

public section

open CategoryTheory

namespace TauCeti.DeligneTorus

variable {H : CommHopfAlgCat ℝ}

/-- The Cartan condition at `i` for a homomorphism from the Deligne torus, contravariantly
represented by `h`. For the homomorphism to the adjoint group this is SV2
(Milne, *Introduction to Shimura varieties*, Definition 5.5). The defining formula is
`IsCartanInvolutionAtI.iff_innerConjugationIso`. -/
def IsCartanInvolutionAtI (h : H ⟶ CommHopfAlgCat.of ℝ S) : Prop :=
  IsCartanInvolution (H.innerConjugationIso
    (h.mapPointsFunctor.app (CommAlgCat.of ℝ ℝ) imaginaryUnitPoint))

/-- The Cartan condition at `i` tests the inner automorphism by the image of the imaginary
unit under the Deligne torus homomorphism. This is not a simp lemma: simplification keeps the
condition folded and removes conjugation directly. -/
theorem IsCartanInvolutionAtI.iff_innerConjugationIso {h : H ⟶ CommHopfAlgCat.of ℝ S} :
    IsCartanInvolutionAtI h ↔
      IsCartanInvolution (H.innerConjugationIso
        (h.mapPointsFunctor.app (CommAlgCat.of ℝ ℝ) imaginaryUnitPoint)) :=
  (Iff.rfl)

/-- The Cartan condition at `i` is invariant under conjugating the Deligne torus homomorphism
by a real point of the target group. -/
@[simp]
theorem IsCartanInvolutionAtI.innerConjugationIso_iff
    {g : WithConv (H →ₐ[ℝ] ℝ)} {h : H ⟶ CommHopfAlgCat.of ℝ S} :
    IsCartanInvolutionAtI ((H.innerConjugationIso g).hom ≫ h) ↔ IsCartanInvolutionAtI h := by
  let x : HopfAlgebra.points (R := ℝ) (H := H) (CommAlgCat.of ℝ ℝ) :=
    h.mapPointsFunctor.app (CommAlgCat.of ℝ ℝ) imaginaryUnitPoint
  have hpoint :
      ((H.innerConjugationIso g).hom ≫ h).mapPointsFunctor.app (CommAlgCat.of ℝ ℝ)
        imaginaryUnitPoint =
        g * x * g⁻¹ := by
    have hx : (H.innerConjugationIso g).hom.mapPointsFunctor.app (CommAlgCat.of ℝ ℝ) x =
        g * x * g⁻¹ := by
      rw [CommHopfAlgCat.Hom.mapPointsFunctor_app_apply,
        CommHopfAlgCat.innerConjugationIso_hom_toAlgHom]
      exact HopfAlgebra.comp_pointConjugationAlgHom_self g x
    rw [CommHopfAlgCat.Hom.mapPointsFunctor_comp_app_apply]
    exact hx
  -- The pointwise conjugation induces conjugation of the coordinate automorphism in
  -- reverse order, since coordinate morphisms are contravariant.
  rw [IsCartanInvolutionAtI.iff_innerConjugationIso,
    IsCartanInvolutionAtI.iff_innerConjugationIso, hpoint]
  rw [CommHopfAlgCat.innerConjugationIso_mul, CommHopfAlgCat.innerConjugationIso_mul,
    CommHopfAlgCat.innerConjugationIso_inv_point, Iso.trans_assoc]
  exact isCartanInvolution_conj_iff (H.innerConjugationIso g).symm

end TauCeti.DeligneTorus

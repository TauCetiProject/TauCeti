/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.CartanInvolution
public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.InnerConjugation
public import TauCeti.Algebra.AlgebraicGroup.DeligneTorus.Basic

/-!
# The Cartan condition for a Deligne torus homomorphism

`TauCeti.DeligneTorus.IsCartanInvolutionAtI.innerConjugationIso_iff` shows that the condition
that conjugation by `h(i)` be a Cartan involution depends only on the real conjugacy
class of the algebraic homomorphism `h`. It follows from
`TauCeti.DeligneTorus.IsCartanInvolutionAtI.iso_hom_comp_iff`, which transports the condition across
isomorphic target groups using naturality of inner conjugation and
`TauCeti.isCartanInvolution_conj_iff`. Applied to the adjoint-group homomorphism,
this is the conjugacy invariance of the Shimura axiom SV2.

See J. S. Milne, *Introduction to Shimura varieties*, Definition 5.5.
-/

public section

open CategoryTheory

namespace TauCeti.DeligneTorus

variable {H K : CommHopfAlgCat ℝ}

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

/-- The Cartan condition at `i` is invariant under isomorphisms of the target group. -/
@[simp]
theorem IsCartanInvolutionAtI.iso_hom_comp_iff
    {e : K ≅ H} {h : H ⟶ CommHopfAlgCat.of ℝ S} :
    IsCartanInvolutionAtI (e.hom ≫ h) ↔ IsCartanInvolutionAtI h := by
  rw [IsCartanInvolutionAtI.iff_innerConjugationIso, IsCartanInvolutionAtI.iff_innerConjugationIso,
    CommHopfAlgCat.Hom.mapPointsFunctor_comp_app_apply]
  let x : HopfAlgebra.points (R := ℝ) (H := H) (CommAlgCat.of ℝ ℝ) :=
    h.mapPointsFunctor.app (CommAlgCat.of ℝ ℝ) imaginaryUnitPoint
  have hconj : K.innerConjugationIso (e.hom.mapPointsFunctor.app (CommAlgCat.of ℝ ℝ) x) =
      e ≪≫ H.innerConjugationIso x ≪≫ e.symm := by
    apply Iso.ext
    apply (cancel_mono e.hom).mp
    exact (e.hom.innerConjugationIso_hom_comp x).trans (by simp)
  rw [hconj]
  exact isCartanInvolution_conj_iff e.symm

/-- The Cartan condition at `i` is invariant under conjugating the Deligne torus homomorphism
by a real point of the target group. This specialization states SV2 invariance in the
real-conjugacy formulation of a Shimura datum. Simplification uses
`IsCartanInvolutionAtI.iso_hom_comp_iff`. -/
theorem IsCartanInvolutionAtI.innerConjugationIso_iff
    {g : WithConv (H →ₐ[ℝ] ℝ)} {h : H ⟶ CommHopfAlgCat.of ℝ S} :
    IsCartanInvolutionAtI ((H.innerConjugationIso g).hom ≫ h) ↔ IsCartanInvolutionAtI h :=
  IsCartanInvolutionAtI.iso_hom_comp_iff

end TauCeti.DeligneTorus

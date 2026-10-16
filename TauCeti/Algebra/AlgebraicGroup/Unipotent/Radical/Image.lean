/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.Quotient
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal.Image
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Image.Smooth
import TauCeti.RingTheory.Smooth.GeometricallyReduced
import TauCeti.Algebra.AlgebraicGroup.Connected.Finite

/-!
# Images of unipotent radicals under dominant homomorphisms

A schematically dominant homomorphism sends the unipotent radical into the target's
unipotent radical. Consequently, if the target radical is trivial and the kernel is finite,
the source radical is trivial: it is a smooth connected subgroup of a finite group.
The kernel itself may be nonreduced.

Coordinate arrows reverse the homomorphisms of represented groups, and defining Hopf ideals
reverse subgroup inclusions. The image comparison therefore takes the form of an ideal
containment in the target coordinate algebra.

The candidate-image argument extends the radical-image argument in
`TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.Reductive.Quotient`; its organization follows
the solvable-radical comparison in `TauCeti.Algebra.AlgebraicGroup.Solvable.Radical.Quotient`.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§6.45–6.46.
* A. Borel, *Linear Algebraic Groups*, §11.21.
-/

public section

open CategoryTheory

namespace TauCeti

universe u

namespace HopfIdeal.IsUnipotentRadicalCandidate

variable {k : Type u} [Field k]
variable {H D : FiniteTypeCommHopfAlgCat.{u, u} k} {I : HopfIdeal k H}

/-- The image of a connected normal smooth unipotent subgroup under a schematically dominant
homomorphism is again a connected normal smooth unipotent subgroup. -/
theorem comap_of_injective (hI : IsUnipotentRadicalCandidate H I)
    (f : D.obj ⟶ H.obj) (hf : Function.Injective f.hom) :
    IsUnipotentRadicalCandidate D (I.comap f.hom) := by
  let Q := FiniteTypeCommHopfAlgCat.quotient H I
  let g : D.obj ⟶ Q.obj := f ≫ CommHopfAlgCat.mkQuotient H.obj I
  have hker : HopfIdeal.ker g.hom = I.comap f.hom := by
    simp only [g, CommHopfAlgCat.hom_comp, HopfIdeal.ker_comp,
      CommHopfAlgCat.hom_mkQuotient, HopfIdeal.ker_mkBialgHom I]
  have hQ := (smoothUnipotentCommHopfAlgProperty_iff k Q).mp hI.smoothUnipotent
  let _ : Algebra.Smooth k Q := hQ.1
  let _ : IsReduced Q := isReduced_of_smooth k Q
  have hsmooth := smoothCommHopfAlgProperty.image g
    ((smoothCommHopfAlgProperty_iff _).mpr hQ.1)
  have hunipotent := geometricallyUnipotentPointsCommHopfAlgProperty.image_of_reduced g
    ((geometricallyUnipotentPointsCommHopfAlgProperty_iff k Q.obj).mpr hQ.2)
  have hconnected := geometricallyConnectedCommHopfAlgProperty.image g hI.geometricallyConnected
  rw [CommHopfAlgCat.image, hker] at hsmooth hunipotent hconnected
  refine .mk (hI.isNormal.comap_of_injective f.hom hf) hconnected ?_
  rw [smoothUnipotentCommHopfAlgProperty_iff]
  exact ⟨(smoothCommHopfAlgProperty_iff _).mp hsmooth,
    (geometricallyUnipotentPointsCommHopfAlgProperty_iff _ _).mp hunipotent⟩

end HopfIdeal.IsUnipotentRadicalCandidate

namespace FiniteTypeCommHopfAlgCat

variable {k : Type u} [Field k]

/-- A schematically dominant homomorphism sends the source unipotent radical into the target
unipotent radical. Defining ideals reverse subgroup inclusions. -/
theorem unipotentRadicalDefiningIdeal_le_comap
    (H D : FiniteTypeCommHopfAlgCat.{u, u} k)
    (f : D.obj ⟶ H.obj) (hf : Function.Injective f.hom) :
    unipotentRadicalDefiningIdeal D ≤ (unipotentRadicalDefiningIdeal H).comap f.hom :=
  unipotentRadicalDefiningIdeal_le D _
    ((isUnipotentRadicalCandidate_unipotentRadicalDefiningIdeal H).comap_of_injective f hf)

/-- A schematically dominant homomorphism with trivial target unipotent radical kills the
source unipotent radical: that radical is contained in the scheme-theoretic kernel. -/
theorem
kernelHopfIdeal_le_unipotentRadicalDefiningIdeal_of_eq_augmentation
    (H D : FiniteTypeCommHopfAlgCat.{u, u} k)
    (hD : unipotentRadicalDefiningIdeal D = HopfIdeal.augmentation k D)
    (f : D.obj ⟶ H.obj) (hf : Function.Injective f.hom) :
    CommHopfAlgCat.kernelHopfIdeal f ≤ unipotentRadicalDefiningIdeal H := by
  rw [CommHopfAlgCat.kernelHopfIdeal_def, HopfIdeal.map_le_iff, ← hD]
  intro x hx
  exact HopfIdeal.mem_comap.mp (unipotentRadicalDefiningIdeal_le_comap H D f hf hx)

/-- Triviality of the unipotent radical reflects along a schematically dominant homomorphism
with finite scheme-theoretic kernel. No smoothness or connectedness of the ambient groups,
nor reducedness of the kernel, is required. -/
theorem unipotentRadicalDefiningIdeal_eq_augmentation_of_finite_kernel
    (H D : FiniteTypeCommHopfAlgCat.{u, u} k)
    (hD : unipotentRadicalDefiningIdeal D = HopfIdeal.augmentation k D)
    (f : D.obj ⟶ H.obj) (hf : Function.Injective f.hom)
    [Module.Finite k (CommHopfAlgCat.quotient H.obj (CommHopfAlgCat.kernelHopfIdeal f))] :
    unipotentRadicalDefiningIdeal H = HopfIdeal.augmentation k H := by
  have hle :=
    kernelHopfIdeal_le_unipotentRadicalDefiningIdeal_of_eq_augmentation
      H D hD f hf
  let q := CommHopfAlgCat.quotientMapOfLe H.obj hle
  let _ : Module.Finite k (unipotentRadical H) := Module.Finite.of_surjective
    q.hom.toLinearMap (CommHopfAlgCat.quotientMapOfLe_surjective H.obj hle)
  have hU := (smoothUnipotentCommHopfAlgProperty_iff k (unipotentRadical H)).mp
    (smoothUnipotent_unipotentRadical H)
  let _ : Algebra.Smooth k (unipotentRadical H) := hU.1
  let _ : IsReduced (unipotentRadical H) := isReduced_of_smooth k _
  let _ : ConnectedSpace (PrimeSpectrum (unipotentRadical H)) :=
    geometricallyConnectedCommHopfAlgProperty.connectedSpace k _
      (geometricallyConnected_unipotentRadical H)
  have hbot := HopfIdeal.augmentation_eq_bot_of_moduleFinite
    (k := k) (H := unipotentRadical H)
  have h := congrArg (fun I : HopfIdeal k (unipotentRadical H) ↦
    I.comapOfSurjective (CommHopfAlgCat.mkQuotient H.obj (unipotentRadicalDefiningIdeal H)).hom
      (CommHopfAlgCat.mkQuotient_surjective _ _)) hbot
  simpa only [HopfIdeal.comapOfSurjective_augmentation, HopfIdeal.comapOfSurjective_bot,
    CommHopfAlgCat.hom_mkQuotient, HopfIdeal.kerOfSurjective_mkBialgHom] using h.symm

end FiniteTypeCommHopfAlgCat

end TauCeti

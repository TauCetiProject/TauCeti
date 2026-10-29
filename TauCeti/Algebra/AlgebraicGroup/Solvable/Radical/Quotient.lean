/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Solvable.Radical.Semisimple
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Kernel.Basic
import TauCeti.Algebra.AlgebraicGroup.Connected.Finite
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal.Image
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Image.Smooth
import TauCeti.Algebra.AlgebraicGroup.Solvable.Reduced
import TauCeti.RingTheory.Smooth.GeometricallyReduced

/-!
# Solvable radicals under quotient homomorphisms

A schematically dominant homomorphism of finite-type affine groups sends the solvable radical
into the solvable radical of its target. The scheme-theoretic image of a connected normal smooth
solvable subgroup is again such a subgroup: dominance preserves normality, and connectedness,
smoothness, and solvability descend to the image.

Consequently, a homomorphism to a group with trivial solvable radical kills the source radical.
A finite kernel forces the source radical to be trivial. If its kernel is itself connected,
smooth, and solvable, that kernel is the radical. In particular this identifies such kernels for
semisimple quotients. These statements use defining
Hopf ideals, whose order reverses inclusion of closed subgroups; coordinate morphisms also run
opposite to the homomorphisms of represented groups.

## Main declarations

* `TauCeti.HopfIdeal.IsSolvableRadicalCandidate.comap_of_injective`: the image of a candidate
  under a schematically dominant homomorphism is a candidate in the target.
* `TauCeti.FiniteTypeCommHopfAlgCat.solvableRadicalDefiningIdeal_le_comap`: the image of the
  source radical lies in the target radical.
* `TauCeti.FiniteTypeCommHopfAlgCat.solvableRadicalDefiningIdeal_eq_augmentation_of_finite_kernel`:
  a dominant homomorphism with finite kernel and trivial target radical has trivial source radical.
* `TauCeti.FiniteTypeCommHopfAlgCat.solvableRadicalDefiningIdeal_eq_kernelHopfIdeal_of_semisimple`:
  a connected smooth solvable kernel with semisimple quotient is the radical.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§6.45--6.46 and 21.10.
* A. Borel, *Linear Algebraic Groups*, §11.21.

The kernel criterion follows the existing unipotent-radical argument in
`TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.Reductive.Quotient`, using geometric
solvability in place of unipotence. The image comparison is stated separately so it also applies
when the target radical is nontrivial.
-/

public section

open CategoryTheory

namespace TauCeti

universe u

namespace HopfIdeal.IsSolvableRadicalCandidate

variable {k : Type u} [Field k]
variable {H D : FiniteTypeCommHopfAlgCat.{u, u} k} {I : HopfIdeal k H}

/-- The image of a connected normal smooth solvable subgroup under a schematically dominant
homomorphism is a connected normal smooth solvable subgroup of the target. Coordinate arrows
reverse: injectivity of `f : D ⟶ H` expresses dominance of `Spec H ⟶ Spec D`. -/
theorem comap_of_injective (hI : IsSolvableRadicalCandidate H I)
    (f : D.obj ⟶ H.obj) (hf : Function.Injective f.hom) :
    IsSolvableRadicalCandidate D (I.comap f.hom) := by
  let Q := FiniteTypeCommHopfAlgCat.quotient H I
  let g : D.obj ⟶ Q.obj := f ≫ CommHopfAlgCat.mkQuotient H.obj I
  have hker : HopfIdeal.ker g.hom = I.comap f.hom := by
    simp only [g, CommHopfAlgCat.hom_comp, HopfIdeal.ker_comp,
      CommHopfAlgCat.hom_mkQuotient, HopfIdeal.ker_mkBialgHom I]
  have hsmooth : smoothCommHopfAlgProperty k (CommHopfAlgCat.image g) :=
    smoothCommHopfAlgProperty.image g ((smoothCommHopfAlgProperty_iff _).mpr hI.smooth)
  have hsolvable : geometricallySolvablePointsCommHopfAlgProperty k
      (CommHopfAlgCat.image g) :=
    geometricallySolvablePointsCommHopfAlgProperty.of_injective_of_smooth
      (CommHopfAlgCat.imageι g) (CommHopfAlgCat.imageι_injective g)
      hI.smooth hI.geometricallySolvable
  have hconnected := geometricallyConnectedCommHopfAlgProperty.image g hI.geometricallyConnected
  rw [CommHopfAlgCat.image, hker] at hsmooth hsolvable hconnected
  exact .mk (hI.isNormal.comap_of_injective f.hom hf) hconnected
    ((smoothCommHopfAlgProperty_iff _).mp hsmooth) hsolvable

end HopfIdeal.IsSolvableRadicalCandidate

namespace FiniteTypeCommHopfAlgCat

variable {k : Type u} [Field k]

/-- A schematically dominant homomorphism sends the source solvable radical into the target
solvable radical. The inequality is reversed because these are defining ideals of subgroups. -/
theorem solvableRadicalDefiningIdeal_le_comap
    (H D : FiniteTypeCommHopfAlgCat.{u, u} k)
    (f : D.obj ⟶ H.obj) (hf : Function.Injective f.hom) :
    solvableRadicalDefiningIdeal D ≤ (solvableRadicalDefiningIdeal H).comap f.hom :=
  solvableRadicalDefiningIdeal_le D _
    ((isSolvableRadicalCandidate_solvableRadicalDefiningIdeal H).comap_of_injective f hf)

/-- A schematically dominant homomorphism to a group with trivial solvable radical kills the
source radical: the source radical is contained in its scheme-theoretic kernel. -/
theorem
kernelHopfIdeal_le_solvableRadicalDefiningIdeal_of_solvableRadicalDefiningIdeal_eq_augmentation
    (H D : FiniteTypeCommHopfAlgCat.{u, u} k)
    (hD : solvableRadicalDefiningIdeal D = HopfIdeal.augmentation k D)
    (f : D.obj ⟶ H.obj) (hf : Function.Injective f.hom) :
    CommHopfAlgCat.kernelHopfIdeal f ≤ solvableRadicalDefiningIdeal H := by
  rw [CommHopfAlgCat.kernelHopfIdeal_def, HopfIdeal.map_le_iff]
  rw [← hD]
  intro x hx
  exact HopfIdeal.mem_comap.mp (solvableRadicalDefiningIdeal_le_comap H D f hf hx)

/-- A schematically dominant homomorphism with finite scheme-theoretic kernel to a group
with trivial solvable radical has trivial source radical. Neither the ambient groups nor
the kernel need be smooth or connected. Coordinate arrows run from target to source. -/
theorem solvableRadicalDefiningIdeal_eq_augmentation_of_finite_kernel
    {Q G : FiniteTypeCommHopfAlgCat.{u, u} k}
    (f : Q.obj ⟶ G.obj) (hf : Function.Injective f.hom)
    [Module.Finite k (CommHopfAlgCat.quotient G.obj (CommHopfAlgCat.kernelHopfIdeal f))]
    (hQ : solvableRadicalDefiningIdeal Q = HopfIdeal.augmentation k Q) :
    solvableRadicalDefiningIdeal G = HopfIdeal.augmentation k G := by
  let I := solvableRadicalDefiningIdeal G
  have hI := isSolvableRadicalCandidate_solvableRadicalDefiningIdeal G
  have hle : CommHopfAlgCat.kernelHopfIdeal f ≤ I :=
    kernelHopfIdeal_le_solvableRadicalDefiningIdeal_of_solvableRadicalDefiningIdeal_eq_augmentation
      G Q hQ f hf
  -- The radical is a closed subgroup of the finite scheme-theoretic kernel.
  let p := CommHopfAlgCat.quotientMapOfLe G.obj hle
  let _ : Module.Finite k (CommHopfAlgCat.quotient G.obj I) :=
    Module.Finite.of_surjective p.hom.toLinearMap
      (CommHopfAlgCat.quotientMapOfLe_surjective G.obj hle)
  let _ : Algebra.Smooth k (CommHopfAlgCat.quotient G.obj I) := hI.smooth
  let _ : IsReduced (CommHopfAlgCat.quotient G.obj I) := isReduced_of_smooth k _
  let _ : ConnectedSpace (PrimeSpectrum (CommHopfAlgCat.quotient G.obj I)) :=
    geometricallyConnectedCommHopfAlgProperty.connectedSpace k _ hI.geometricallyConnected
  have hbot := HopfIdeal.augmentation_eq_bot_of_moduleFinite
    (k := k) (H := CommHopfAlgCat.quotient G.obj I)
  have hsurj : Function.Surjective (Bialgebra.Quotient.mkBialgHom (R := k) I.toIdeal) :=
    Ideal.Quotient.mk_surjective
  have h := HopfIdeal.comapOfSurjective_augmentation
    (Bialgebra.Quotient.mkBialgHom (R := k) I.toIdeal) hsurj
  rw [hbot] at h
  rw [HopfIdeal.comapOfSurjective_bot, HopfIdeal.kerOfSurjective_mkBialgHom] at h
  exact h

/-- A connected normal smooth solvable kernel of a schematically dominant homomorphism to a
group with trivial solvable radical is the solvable radical of the source. -/
theorem
solvableRadicalDefiningIdeal_eq_kernelHopfIdeal_of_solvableRadicalDefiningIdeal_eq_augmentation
    (H D : FiniteTypeCommHopfAlgCat.{u, u} k)
    (hD : solvableRadicalDefiningIdeal D = HopfIdeal.augmentation k D)
    (f : D.obj ⟶ H.obj) (hf : Function.Injective f.hom)
    (hker : HopfIdeal.IsSolvableRadicalCandidate H (CommHopfAlgCat.kernelHopfIdeal f)) :
    solvableRadicalDefiningIdeal H = CommHopfAlgCat.kernelHopfIdeal f :=
  le_antisymm (solvableRadicalDefiningIdeal_le H _ hker)
    (kernelHopfIdeal_le_solvableRadicalDefiningIdeal_of_solvableRadicalDefiningIdeal_eq_augmentation
      H D hD f hf)

/-- A connected normal smooth solvable kernel with semisimple quotient is the solvable radical.
No perfectness or characteristic hypothesis on the ground field is needed. -/
theorem solvableRadicalDefiningIdeal_eq_kernelHopfIdeal_of_semisimple
    (H D : FiniteTypeCommHopfAlgCat.{u, u} k) (hD : semisimpleCommHopfAlgProperty k D)
    (f : D.obj ⟶ H.obj) (hf : Function.Injective f.hom)
    (hker : HopfIdeal.IsSolvableRadicalCandidate H (CommHopfAlgCat.kernelHopfIdeal f)) :
    solvableRadicalDefiningIdeal H = CommHopfAlgCat.kernelHopfIdeal f :=
  solvableRadicalDefiningIdeal_eq_kernelHopfIdeal_of_solvableRadicalDefiningIdeal_eq_augmentation
    H D hD.solvableRadicalDefiningIdeal_eq_augmentation f hf hker

end FiniteTypeCommHopfAlgCat

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Solvable.Radical.Semisimple
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Kernel.Basic
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal.Image
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Image.Smooth
import TauCeti.Algebra.AlgebraicGroup.Solvable.Reduced

/-!
# Solvable radicals under quotient homomorphisms

A schematically dominant homomorphism of finite-type affine groups sends the solvable radical
into the solvable radical of its target. The scheme-theoretic image of a connected normal smooth
solvable subgroup is again such a subgroup: dominance preserves normality, and connectedness,
smoothness, and solvability descend to the image.

Consequently, a homomorphism to a group with trivial solvable radical kills the source radical.
If its kernel is itself connected, smooth, and solvable, that kernel is the radical. In
particular this identifies such kernels for semisimple quotients. These statements use defining
Hopf ideals, whose order reverses inclusion of closed subgroups; coordinate morphisms also run
opposite to the homomorphisms of represented groups.

## Main declarations

* `TauCeti.HopfIdeal.IsSolvableRadicalCandidate.comap_of_injective`: the image of a candidate
  under a schematically dominant homomorphism is a candidate in the target.
* `TauCeti.FiniteTypeCommHopfAlgCat.solvableRadicalDefiningIdeal_le_comap`: the image of the
  source radical lies in the target radical.
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
theorem kernelHopfIdeal_le_solvableRadicalDefiningIdeal_of_target_radical_eq_augmentation
    (H D : FiniteTypeCommHopfAlgCat.{u, u} k)
    (hD : solvableRadicalDefiningIdeal D = HopfIdeal.augmentation k D)
    (f : D.obj ⟶ H.obj) (hf : Function.Injective f.hom) :
    CommHopfAlgCat.kernelHopfIdeal f ≤ solvableRadicalDefiningIdeal H := by
  rw [CommHopfAlgCat.kernelHopfIdeal_def, HopfIdeal.map_le_iff]
  rw [← hD]
  intro x hx
  exact HopfIdeal.mem_comap.mp (solvableRadicalDefiningIdeal_le_comap H D f hf hx)

/-- A connected normal smooth solvable kernel of a schematically dominant homomorphism to a
group with trivial solvable radical is the solvable radical of the source. -/
theorem solvableRadicalDefiningIdeal_eq_kernelHopfIdeal_of_target_radical_eq_augmentation
    (H D : FiniteTypeCommHopfAlgCat.{u, u} k)
    (hD : solvableRadicalDefiningIdeal D = HopfIdeal.augmentation k D)
    (f : D.obj ⟶ H.obj) (hf : Function.Injective f.hom)
    (hker : HopfIdeal.IsSolvableRadicalCandidate H (CommHopfAlgCat.kernelHopfIdeal f)) :
    solvableRadicalDefiningIdeal H = CommHopfAlgCat.kernelHopfIdeal f :=
  le_antisymm (solvableRadicalDefiningIdeal_le H _ hker)
    (kernelHopfIdeal_le_solvableRadicalDefiningIdeal_of_target_radical_eq_augmentation
      H D hD f hf)

/-- A connected normal smooth solvable kernel with semisimple quotient is the solvable radical.
No perfectness or characteristic hypothesis on the ground field is needed. -/
theorem solvableRadicalDefiningIdeal_eq_kernelHopfIdeal_of_semisimple
    (H D : FiniteTypeCommHopfAlgCat.{u, u} k) (hD : semisimpleCommHopfAlgProperty k D)
    (f : D.obj ⟶ H.obj) (hf : Function.Injective f.hom)
    (hker : HopfIdeal.IsSolvableRadicalCandidate H (CommHopfAlgCat.kernelHopfIdeal f)) :
    solvableRadicalDefiningIdeal H = CommHopfAlgCat.kernelHopfIdeal f :=
  solvableRadicalDefiningIdeal_eq_kernelHopfIdeal_of_target_radical_eq_augmentation H D
    hD.solvableRadicalDefiningIdeal_eq_augmentation f hf hker

end FiniteTypeCommHopfAlgCat

end TauCeti

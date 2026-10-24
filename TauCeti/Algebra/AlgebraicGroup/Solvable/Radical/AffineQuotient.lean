/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Solvable.Radical.Construction
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Coinvariants.FiniteType

import TauCeti.Algebra.AlgebraicGroup.Connected.Extension
import TauCeti.Algebra.AlgebraicGroup.Solvable.Extension
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Kernel.Preimage
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Kernel.Smooth
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Coinvariants.Exactness

/-!
# The solvable radical of the affine quotient by the radical

The inverse image of a smooth connected normal solvable subgroup under a faithfully flat
homomorphism with smooth connected solvable kernel is again such a subgroup. Consequently,
a quotient homomorphism whose kernel is the solvable radical has a target with trivial
solvable radical. In particular this applies to the actual affine quotient constructed from
normal coinvariants.

These statements hold over every field. They concern the radical over the ground field;
identifying a quotient as semisimple additionally requires the corresponding geometric
statement after scalar extension. No commutation of radicals with scalar extension is assumed.

The preimage argument uses `CommHopfAlgCat.prop_quotient_map_of_kernel` to express the inverse
image as an extension of the given subgroup by the original kernel. Smoothness, connectedness and
solvability each follow from closure under such extensions.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapters 5 and 19.
* A. Borel, *Linear Algebraic Groups*, §11.21.
-/

public section

open CategoryTheory
open _root_.CommHopfAlgCat _root_.CommHopfAlgCat.Hom

namespace TauCeti

universe u

namespace HopfIdeal.IsSolvableRadicalCandidate

variable {k : Type u} [Field k]
variable {Q G : FiniteTypeCommHopfAlgCat.{u, u} k}

/-- The inverse image of a smooth geometrically connected normal solvable subgroup under a
faithfully flat homomorphism with smooth geometrically connected solvable kernel is again a
smooth geometrically connected normal solvable subgroup. Coordinate morphisms reverse arrows,
so inverse image of subgroups is extension of their defining Hopf ideals. -/
theorem map [Algebra.IsGeometricallyReduced k Q]
    {J : HopfIdeal k Q} (hJ : IsSolvableRadicalCandidate Q J)
    (p : Q.obj ⟶ G.obj) (hp : p.hom.toAlgHom.toRingHom.FaithfullyFlat)
    (hN : IsSolvableRadicalCandidate G (CommHopfAlgCat.kernelHopfIdeal p)) :
    IsSolvableRadicalCandidate G (J.map p.hom) := by
  refine .mk (hJ.isNormal.map p.hom) ?_ ?_ ?_
  · exact CommHopfAlgCat.prop_quotient_map_of_kernel (geometricallyConnectedCommHopfAlgProperty k)
      (fun r hr hA hker ↦ hA.of_kernel r hr hker) hJ.isNormal p hp hJ.geometricallyConnected
      hN.geometricallyConnected
  · refine (smoothCommHopfAlgProperty_iff _).mp <|
      CommHopfAlgCat.prop_quotient_map_of_kernel (smoothCommHopfAlgProperty k)
        (fun r hr hA hker ↦ ?_) hJ.isNormal p hp
        ((smoothCommHopfAlgProperty_iff _).mpr hJ.smooth)
        ((smoothCommHopfAlgProperty_iff _).mpr hN.smooth)
    let _ := (smoothCommHopfAlgProperty_iff _).mp hA
    exact (smoothCommHopfAlgProperty_iff _).mpr
      (algebraSmooth_of_algebraSmooth_quotient_kernelHopfIdeal r hr
        ((smoothCommHopfAlgProperty_iff _).mp hker))
  · exact CommHopfAlgCat.prop_quotient_map_of_kernel
      (geometricallySolvablePointsCommHopfAlgProperty k)
      (fun r _ hA hker ↦ geometricallySolvablePointsCommHopfAlgProperty_of_kernel k r hA hker)
      hJ.isNormal p hp hJ.geometricallySolvable hN.geometricallySolvable

end HopfIdeal.IsSolvableRadicalCandidate

namespace FiniteTypeCommHopfAlgCat

variable {k : Type u} [Field k]

/-- A faithfully flat quotient whose kernel is the solvable radical has target with trivial
solvable radical. Only the target is required to be geometrically reduced; the kernel is
smooth by the defining property of the radical. -/
theorem solvableRadicalDefiningIdeal_eq_augmentation_of_kernel_eq_solvableRadical
    {Q G : FiniteTypeCommHopfAlgCat.{u, u} k} [Algebra.IsGeometricallyReduced k Q]
    (p : Q.obj ⟶ G.obj) (hp : p.hom.toAlgHom.toRingHom.FaithfullyFlat)
    (hker : CommHopfAlgCat.kernelHopfIdeal p = solvableRadicalDefiningIdeal G) :
    solvableRadicalDefiningIdeal Q = HopfIdeal.augmentation k Q := by
  rw [solvableRadicalDefiningIdeal_eq_augmentation_iff]
  intro J hJ
  have hN : HopfIdeal.IsSolvableRadicalCandidate G (CommHopfAlgCat.kernelHopfIdeal p) :=
    hker ▸ isSolvableRadicalCandidate_solvableRadicalDefiningIdeal G
  apply CommHopfAlgCat.eq_augmentation_of_kernelHopfIdeal_le_map p hp
  rw [hker]
  exact solvableRadicalDefiningIdeal_le G _ (hJ.map p hp hN)

/-- The affine quotient of a geometrically reduced finite-type group by its solvable radical
has trivial solvable radical over the ground field, in every characteristic. -/
theorem solvableRadicalDefiningIdeal_coinvariants_eq_augmentation
    (G : FiniteTypeCommHopfAlgCat.{u, u} k) [Algebra.IsGeometricallyReduced k G] :
    let hR := isNormal_solvableRadicalDefiningIdeal G
    letI := hR.isHopfSubalgebra_coinvariants.hopfAlgebra
    let Q : FiniteTypeCommHopfAlgCat.{u, u} k :=
      ⟨CommHopfAlgCat.coinvariants hR,
        (finiteTypeCommHopfAlgProperty_iff _).mpr hR.finiteType_coinvariants⟩
    solvableRadicalDefiningIdeal Q = HopfIdeal.augmentation k Q := by
  let hR := isNormal_solvableRadicalDefiningIdeal G
  let := hR.isHopfSubalgebra_coinvariants.hopfAlgebra
  let Q : FiniteTypeCommHopfAlgCat.{u, u} k :=
    ⟨CommHopfAlgCat.coinvariants hR,
      (finiteTypeCommHopfAlgProperty_iff _).mpr hR.finiteType_coinvariants⟩
  let p : Q.obj ⟶ G.obj := CommHopfAlgCat.coinvariantsι hR
  let _ : Algebra.IsGeometricallyReduced k Q :=
    Algebra.IsGeometricallyReduced.of_injective p.hom.toAlgHom
      (CommHopfAlgCat.hopfSubalgebraι_injective hR.isHopfSubalgebra_coinvariants)
  exact solvableRadicalDefiningIdeal_eq_augmentation_of_kernel_eq_solvableRadical p
    (CommHopfAlgCat.faithfullyFlat_coinvariantsι hR)
    (CommHopfAlgCat.kernelHopfIdeal_coinvariantsι_eq hR)

end FiniteTypeCommHopfAlgCat

end TauCeti

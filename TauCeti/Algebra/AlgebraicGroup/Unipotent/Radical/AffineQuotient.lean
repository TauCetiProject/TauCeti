/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.Construction
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Coinvariants.FiniteType

import TauCeti.Algebra.AlgebraicGroup.Connected.Extension
import TauCeti.Algebra.AlgebraicGroup.Unipotent.Extension
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Coinvariants.Exactness
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Kernel.Preimage
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Kernel.Smooth

/-!
# The unipotent radical of the affine quotient by the unipotent radical

The inverse image of a smooth connected normal unipotent subgroup under a faithfully flat
homomorphism with smooth connected unipotent kernel is again such a subgroup: smoothness,
geometric connectedness and unipotence of geometric points are all closed under extensions.
Consequently, a quotient homomorphism whose kernel is the unipotent radical has a target with
trivial unipotent radical. In particular this applies to the actual affine quotient `G ⧸ R_u(G)`
constructed from normal coinvariants.

These statements hold over every field and concern the radical over the ground field, that is,
the `k`-unipotent radical. Over an imperfect field this radical need not become the geometric
unipotent radical after extension to an algebraic closure, so no reductivity of the quotient is
asserted here.

## Main declarations

* `TauCeti.HopfIdeal.IsUnipotentRadicalCandidate.map`: inverse images of connected normal smooth
  unipotent subgroups along a quotient homomorphism with such a kernel.
* `TauCeti.FiniteTypeCommHopfAlgCat.
    unipotentRadicalDefiningIdeal_eq_augmentation_of_kernel_eq_unipotentRadical`:
  a faithfully flat quotient whose kernel is the unipotent radical has trivial unipotent radical.
* `TauCeti.FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal_coinvariants_eq_augmentation`:
  the affine quotient by the unipotent radical has trivial unipotent radical.

## References

* B. Conrad, O. Gabber, G. Prasad, *Pseudo-reductive Groups*, 2nd ed. (2015), §1.1.
* J. S. Milne, *Algebraic Groups* (2017), §§6.45–6.46 and Chapter 19.
-/

public section

open CategoryTheory
open _root_.CommHopfAlgCat _root_.CommHopfAlgCat.Hom

namespace TauCeti

universe u

namespace HopfIdeal.IsUnipotentRadicalCandidate

variable {k : Type u} [Field k]
variable {Q G : FiniteTypeCommHopfAlgCat.{u, u} k}

/-- The inverse image of a connected normal smooth unipotent subgroup under a faithfully flat
homomorphism whose kernel is a connected normal smooth unipotent subgroup is again a connected
normal smooth unipotent subgroup. Coordinate morphisms reverse arrows, so inverse image of
subgroups is extension of their defining Hopf ideals. -/
theorem map [Algebra.IsGeometricallyReduced k Q]
    {J : HopfIdeal k Q} (hJ : IsUnipotentRadicalCandidate Q J)
    (p : Q.obj ⟶ G.obj) (hp : p.hom.toAlgHom.toRingHom.FaithfullyFlat)
    (hN : IsUnipotentRadicalCandidate G (CommHopfAlgCat.kernelHopfIdeal p)) :
    IsUnipotentRadicalCandidate G (J.map p.hom) := by
  obtain ⟨hJsmooth, hJunipotent⟩ :=
    (smoothUnipotentCommHopfAlgProperty_iff k _).mp hJ.smoothUnipotent
  obtain ⟨hNsmooth, hNunipotent⟩ :=
    (smoothUnipotentCommHopfAlgProperty_iff k _).mp hN.smoothUnipotent
  refine .mk (hJ.isNormal.map p.hom) ?_ ?_
  · exact CommHopfAlgCat.prop_quotient_map_of_kernel (geometricallyConnectedCommHopfAlgProperty k)
      (fun r hr hA hker ↦ hA.of_kernel r hr hker) hJ.isNormal p hp hJ.geometricallyConnected
      hN.geometricallyConnected
  rw [smoothUnipotentCommHopfAlgProperty_iff]
  refine ⟨(smoothCommHopfAlgProperty_iff _).mp ?_, ?_⟩
  · refine CommHopfAlgCat.prop_quotient_map_of_kernel (smoothCommHopfAlgProperty k)
      (fun r hr hA hker ↦ ?_) hJ.isNormal p hp
      ((smoothCommHopfAlgProperty_iff _).mpr hJsmooth)
      ((smoothCommHopfAlgProperty_iff _).mpr hNsmooth)
    let _ := (smoothCommHopfAlgProperty_iff _).mp hA
    exact (smoothCommHopfAlgProperty_iff _).mpr
      (algebraSmooth_of_algebraSmooth_quotient_kernelHopfIdeal r hr
        ((smoothCommHopfAlgProperty_iff _).mp hker))
  · rw [← geometricallyUnipotentPointsCommHopfAlgProperty_iff]
    exact CommHopfAlgCat.prop_quotient_map_of_kernel
      (geometricallyUnipotentPointsCommHopfAlgProperty k)
      (fun r _ hA hker ↦ geometricallyUnipotentPointsCommHopfAlgProperty_of_kernel k r hA hker)
      hJ.isNormal p hp
      ((geometricallyUnipotentPointsCommHopfAlgProperty_iff k _).mpr hJunipotent)
      ((geometricallyUnipotentPointsCommHopfAlgProperty_iff k _).mpr hNunipotent)

end HopfIdeal.IsUnipotentRadicalCandidate

namespace FiniteTypeCommHopfAlgCat

variable {k : Type u} [Field k]

/-- A faithfully flat quotient whose kernel is the unipotent radical has target with trivial
unipotent radical. Only the target is required to be geometrically reduced; the kernel is
smooth by the defining property of the radical. -/
theorem unipotentRadicalDefiningIdeal_eq_augmentation_of_kernel_eq_unipotentRadical
    {Q G : FiniteTypeCommHopfAlgCat.{u, u} k} [Algebra.IsGeometricallyReduced k Q]
    (p : Q.obj ⟶ G.obj) (hp : p.hom.toAlgHom.toRingHom.FaithfullyFlat)
    (hker : CommHopfAlgCat.kernelHopfIdeal p = unipotentRadicalDefiningIdeal G) :
    unipotentRadicalDefiningIdeal Q = HopfIdeal.augmentation k Q := by
  rw [unipotentRadicalDefiningIdeal_eq_augmentation_iff]
  intro J hJ
  have hN : HopfIdeal.IsUnipotentRadicalCandidate G (CommHopfAlgCat.kernelHopfIdeal p) :=
    hker ▸ isUnipotentRadicalCandidate_unipotentRadicalDefiningIdeal G
  apply CommHopfAlgCat.eq_augmentation_of_kernelHopfIdeal_le_map p hp
  rw [hker]
  exact unipotentRadicalDefiningIdeal_le G _ (hJ.map p hp hN)

/-- The affine quotient of a geometrically reduced finite-type group by its unipotent radical has
trivial unipotent radical over the ground field, in every characteristic. -/
theorem unipotentRadicalDefiningIdeal_coinvariants_eq_augmentation
    (G : FiniteTypeCommHopfAlgCat.{u, u} k) [Algebra.IsGeometricallyReduced k G] :
    let hR := isNormal_unipotentRadicalDefiningIdeal G
    letI := hR.isHopfSubalgebra_coinvariants.hopfAlgebra
    let Q : FiniteTypeCommHopfAlgCat.{u, u} k :=
      ⟨CommHopfAlgCat.coinvariants hR,
        (finiteTypeCommHopfAlgProperty_iff _).mpr hR.finiteType_coinvariants⟩
    unipotentRadicalDefiningIdeal Q = HopfIdeal.augmentation k Q := by
  let hR := isNormal_unipotentRadicalDefiningIdeal G
  let := hR.isHopfSubalgebra_coinvariants.hopfAlgebra
  let Q : FiniteTypeCommHopfAlgCat.{u, u} k :=
    ⟨CommHopfAlgCat.coinvariants hR,
      (finiteTypeCommHopfAlgProperty_iff _).mpr hR.finiteType_coinvariants⟩
  let p : Q.obj ⟶ G.obj := CommHopfAlgCat.coinvariantsι hR
  let _ : Algebra.IsGeometricallyReduced k Q :=
    Algebra.IsGeometricallyReduced.of_injective p.hom.toAlgHom
      (CommHopfAlgCat.hopfSubalgebraι_injective hR.isHopfSubalgebra_coinvariants)
  exact unipotentRadicalDefiningIdeal_eq_augmentation_of_kernel_eq_unipotentRadical p
    (CommHopfAlgCat.faithfullyFlat_coinvariantsι hR)
    (CommHopfAlgCat.kernelHopfIdeal_coinvariantsι_eq hR)

end FiniteTypeCommHopfAlgCat

end TauCeti

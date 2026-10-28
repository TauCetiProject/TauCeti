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
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Kernel.Composite
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

The preimage argument uses `CommHopfAlgCat.kernelCompositeMap` to express the inverse image
as an extension of the given subgroup by the original kernel. Smoothness and connectedness
follow from the kernel criteria; solvability follows from extension closure.

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
  -- Realize the subgroup and its inverse image as kernels of a composite.
  let f := CommHopfAlgCat.coinvariantsι hJ.isNormal
  have hf : CommHopfAlgCat.kernelHopfIdeal f = J :=
    CommHopfAlgCat.kernelHopfIdeal_coinvariantsι_eq hJ.isNormal
  let r := CommHopfAlgCat.kernelCompositeMap f p
  have hr := CommHopfAlgCat.faithfullyFlat_kernelCompositeMap f p hp
  let e := CommHopfAlgCat.kernelCompositeKernelIso f p
  have hkernelConnected : geometricallyConnectedCommHopfAlgProperty k
      (CommHopfAlgCat.quotient _ (CommHopfAlgCat.kernelHopfIdeal r)) :=
    (geometricallyConnectedCommHopfAlgProperty k).prop_of_iso e.symm hN.geometricallyConnected
  have hkernelSolvable : geometricallySolvablePointsCommHopfAlgProperty k
      (CommHopfAlgCat.quotient _ (CommHopfAlgCat.kernelHopfIdeal r)) :=
    (geometricallySolvablePointsCommHopfAlgProperty k).prop_of_iso e.symm hN.geometricallySolvable
  have hkernelSmooth : Algebra.Smooth k
      (CommHopfAlgCat.quotient _ (CommHopfAlgCat.kernelHopfIdeal r)) :=
    (smoothCommHopfAlgProperty_iff _).mp <|
      (smoothCommHopfAlgProperty k).prop_of_iso e.symm
        ((smoothCommHopfAlgProperty_iff _).mpr hN.smooth)
  -- Transport the three extension hypotheses through the exact-kernel identifications.
  have htargetConnected : geometricallyConnectedCommHopfAlgProperty k
      (CommHopfAlgCat.quotient Q.obj (CommHopfAlgCat.kernelHopfIdeal f)) := by
    rw [hf]
    exact hJ.geometricallyConnected
  have htargetSolvable : geometricallySolvablePointsCommHopfAlgProperty k
      (CommHopfAlgCat.quotient Q.obj (CommHopfAlgCat.kernelHopfIdeal f)) := by
    rw [hf]
    exact hJ.geometricallySolvable
  have htargetSmooth : Algebra.Smooth k
      (CommHopfAlgCat.quotient Q.obj (CommHopfAlgCat.kernelHopfIdeal f)) := by
    rw [hf]
    exact hJ.smooth
  -- Each closure theorem now applies to the same faithfully flat restriction.
  have hconnected := htargetConnected.of_kernel r hr hkernelConnected
  have hsolvable := geometricallySolvablePointsCommHopfAlgProperty_of_kernel k r
    htargetSolvable hkernelSolvable
  have hsmooth : Algebra.Smooth k
      (CommHopfAlgCat.quotient G.obj (CommHopfAlgCat.kernelHopfIdeal (f ≫ p))) := by
    let := r.hom.toAlgHom.toAlgebra
    let _ : IsScalarTower k
        (CommHopfAlgCat.quotient Q.obj (CommHopfAlgCat.kernelHopfIdeal f))
        (CommHopfAlgCat.quotient G.obj (CommHopfAlgCat.kernelHopfIdeal (f ≫ p))) :=
      IsScalarTower.of_algebraMap_eq fun a ↦ (r.hom.toAlgHom.commutes a).symm
    let _ := htargetSmooth
    let _ : Algebra.Smooth
        (CommHopfAlgCat.quotient Q.obj (CommHopfAlgCat.kernelHopfIdeal f))
        (CommHopfAlgCat.quotient G.obj (CommHopfAlgCat.kernelHopfIdeal (f ≫ p))) :=
      (_root_.CommHopfAlgCat.smooth_iff_algebraSmooth_quotient_kernelHopfIdeal r hr).mpr
        hkernelSmooth
    exact Algebra.Smooth.comp k
      (CommHopfAlgCat.quotient Q.obj (CommHopfAlgCat.kernelHopfIdeal f)) _
  have hpre : CommHopfAlgCat.kernelHopfIdeal (f ≫ p) = J.map p.hom := by
    rw [CommHopfAlgCat.kernelHopfIdeal_comp, hf]
  rw [hpre] at hconnected hsolvable hsmooth
  exact .mk (hJ.isNormal.map p.hom) hconnected hsmooth hsolvable

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
  have hle := solvableRadicalDefiningIdeal_le G _ (hJ.map p hp hN)
  rw [← hker, CommHopfAlgCat.kernelHopfIdeal_def] at hle
  let := p.hom.toAlgHom.toAlgebra
  let _ : Module.FaithfullyFlat Q G := hp
  apply le_antisymm (HopfIdeal.le_augmentation k Q J)
  intro x hx
  have hmap : p.hom x ∈ (J.map p.hom).toIdeal :=
    hle (HopfIdeal.mem_map_of_mem p.hom hx)
  rw [HopfIdeal.map_toIdeal] at hmap
  have hx' : x ∈ Ideal.comap (algebraMap Q G) (J.toIdeal.map (algebraMap Q G)) := by
    exact hmap
  rwa [Ideal.comap_map_eq_self_of_faithfullyFlat J.toIdeal] at hx'

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

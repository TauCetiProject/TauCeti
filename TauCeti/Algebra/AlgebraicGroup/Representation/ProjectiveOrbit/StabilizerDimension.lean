/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.Flat
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Basic
import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.Dimension
import TauCeti.Algebra.AlgebraicGroup.Tangent.KrullDimension
import TauCeti.AlgebraicGeometry.AugmentationPoint.ClosedPoints
import TauCeti.AlgebraicGeometry.Morphisms.Flat.Dimension
import TauCeti.Topology.KrullDimension.Basic

/-!
# The dimension of a projective orbit

Let `G` be a reduced affine group of finite type over an algebraically closed field `k`, acting
on a finite-dimensional representation `V`, and let `[m]` be a line in `V`. If `D` cuts out the
stabilizer of `[m]`, in the sense that a rational point of `G` lies in `D` exactly when it fixes
`[m]`, then the orbit `O` of `[m]` in the projective space `P(V)` satisfies

```text
  dim O + dim D = dim G,
```

where `dim D` is the dimension of the closed subgroup cut out by `D`, whose coordinate ring is
`H ⧸ D`.

Only the rational points of the stabilizer are prescribed, so `D` may be any closed subgroup with
the right rational points, reduced or not: the Krull dimension sees only the underlying space.

The orbit map `G → O` onto the projective orbit scheme is flat, so the dimension formula for flat
morphisms (`AlgebraicGeometry.Scheme.Hom.coheight_eq_coheight_add_coheight_preimage`) applies at
the identity. The three codimensions are identified as follows.

* The identity of `G` has codimension `dim G`, since translations make every closed point of `G`
  look alike.
* Its image in `O` has codimension `dim O`: rational translations act transitively on the closed
  points of `O`, and every point of `O` specializes to a closed point.
* The fibre of the orbit map through the identity is the closed subset cut out by `D`, since both
  are closed and have the same rational points, which are dense because `G` is Jacobson. The
  codimension of the identity in it is the height of the augmentation ideal of `H ⧸ D`, that is
  `dim D`.

This is the dimension count that relates the closed-orbit lemma, which concerns orbits of minimal
dimension, to stabilizers of maximal dimension, as in the conjugacy of Borel subgroups.

## Main declarations

* `TauCeti.Comodule.coheight_eq_topologicalKrullDim_of_mem_closedPoints`: every closed point of a
  projective orbit scheme has codimension equal to the dimension of the orbit.
* `TauCeti.Comodule.preimage_toProjectiveOrbit_augmentationPoint`: the fibre of the orbit map
  through the identity is the closed subset cut out by the stabilizer.
* `TauCeti.Comodule.topologicalKrullDim_range_projectiveOrbitMap_add_ringKrullDim_eq`: the
  dimension of the orbit plus that of the stabilizer is that of the group.

## References

* A. Borel, *Linear Algebraic Groups*, 2nd ed., GTM 126, §1.8.
* J. E. Humphreys, *Linear Algebraic Groups*, GTM 21, §8.3.
* J. S. Milne, *Algebraic Groups* (2017), §7.c, orbits and isotropy groups.
-/

public section

open CategoryTheory AlgebraicGeometry Order WithConv

namespace TauCeti.Comodule

universe u

variable {k H M : Type u} [Field k] [IsAlgClosed k] [CommRing H] [HopfAlgebra k H]
  [Algebra.FiniteType k H] [AddCommGroup M] [Module k M] [Comodule k H M] [Module.Finite k M]

/-- Every closed point of a projective orbit scheme has codimension equal to the dimension of the
orbit scheme: rational translations act transitively on the closed points, and every point
specializes to a closed point. -/
theorem coheight_eq_topologicalKrullDim_of_mem_closedPoints (m : M)
    (hm : Module.IsUnimodular k m) {y : projectiveOrbitScheme (H := H) m hm}
    (hy : y ∈ closedPoints _) :
    (coheight y : WithBot ℕ∞) = topologicalKrullDim (projectiveOrbitScheme (H := H) m hm) := by
  refine le_antisymm (TauCeti.coheight_le_topologicalKrullDim y) ?_
  rw [TauCeti.topologicalKrullDim_eq_iSup_coheight]
  refine iSup_le fun y' ↦ ?_
  obtain ⟨z, hz, hzc⟩ := (isClosed_closure (s := {y'})).exists_closed_singleton
    ⟨y', subset_closure (Set.mem_singleton y')⟩
  obtain ⟨g, rfl⟩ := exists_projectiveOrbitTranslation_eq_of_mem_closedPoints m hm hy hzc
  have hzy : (projectiveOrbitTranslation m hm g).hom y ≤ y' := specializes_iff_mem_closure.mpr hz
  exact_mod_cast (coheight_anti hzy).trans
    (coheight_eq_of_isOpenImmersion (projectiveOrbitTranslation m hm g).hom).le

/-- The fibre of the orbit map through the identity is the closed subset cut out by any closed
subgroup `D` whose rational points are those fixing the line `[m]`: both subsets are closed, and
they have the same rational points, which are dense in every closed subset. -/
theorem preimage_toProjectiveOrbit_augmentationPoint
    (m : M) (hm : Module.IsUnimodular k m) (D : HopfIdeal k H)
    (hstab : ∀ a : WithConv (H →ₐ[k] k),
      a ∈ CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k H) D
          (CommAlgCat.of k k) ↔
        projectiveOrbitMap (H := H) m hm (AlgHom.kernelPoint a.ofConv) =
          projectiveOrbitMap (H := H) m hm
            (AlgHom.kernelPoint (Bialgebra.counitAlgHom k H))) :
    toProjectiveOrbit (H := H) m hm ⁻¹'
        {toProjectiveOrbit (H := H) m hm (Bialgebra.augmentationPoint k H)} =
      {x : Spec (.of H) | D.toIdeal ≤ x.asIdeal} := by
  let f := toProjectiveOrbit (H := H) m hm
  have hc₁ : IsClosed (f ⁻¹' {f (Bialgebra.augmentationPoint k H)}) := by
    refine IsClosed.preimage f.continuous ?_
    rw [← mem_closedPoints_iff, ← range_toProjectiveOrbit_kernelPoint_eq_closedPoints m hm]
    exact ⟨toConv (Bialgebra.counitAlgHom k H), rfl⟩
  have hc₂ : IsClosed {x : Spec (.of H) | D.toIdeal ≤ x.asIdeal} :=
    PrimeSpectrum.isClosed_zeroLocus (D.toIdeal : Set H)
  have := isJacobsonRing_of_finiteType (A := k) (B := H)
  rw [← hc₁.closure_eq, ← hc₂.closure_eq,
    ← JacobsonSpace.closure_inter_closedPoints_eq_closure hc₁.isLocallyClosed,
    ← JacobsonSpace.closure_inter_closedPoints_eq_closure hc₂.isLocallyClosed]
  congr 1
  ext x
  simp only [Set.mem_inter_iff, and_congr_left_iff]
  intro hx
  rw [← range_kernelPoint_eq_closedPoints (k := k)] at hx
  obtain ⟨g, rfl⟩ := hx
  have hfg : f (AlgHom.kernelPoint g) = f (Bialgebra.augmentationPoint k H) ↔
      projectiveOrbitMap (H := H) m hm (AlgHom.kernelPoint g) =
        projectiveOrbitMap (H := H) m hm (Bialgebra.augmentationPoint k H) := by
    rw [← toProjectiveOrbit_projectiveOrbitι m hm, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
    exact (projectiveOrbitι m hm).isEmbedding.injective.eq_iff.symm
  rw [Set.mem_preimage, Set.mem_singleton_iff, hfg, ← hstab (toConv g),
    CommHopfAlgCat.mem_quotientPointsSubgroup_iff]
  simp [IsConcreteLE.le_iff]

variable [_root_.IsReduced H]

/-- **The dimension of a projective orbit.** For a reduced affine group of finite type over an
algebraically closed field, the orbit of a line `[m]` and a closed subgroup `D` whose rational
points are exactly those fixing `[m]` satisfy `dim O + dim D = dim G`, where `dim D` is the Krull
dimension of the coordinate ring `H ⧸ D` of that subgroup. -/
theorem topologicalKrullDim_range_projectiveOrbitMap_add_ringKrullDim_eq
    (m : M) (hm : Module.IsUnimodular k m) (D : HopfIdeal k H)
    (hstab : ∀ a : WithConv (H →ₐ[k] k),
      a ∈ CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k H) D
          (CommAlgCat.of k k) ↔
        projectiveOrbitMap (H := H) m hm (AlgHom.kernelPoint a.ofConv) =
          projectiveOrbitMap (H := H) m hm
            (AlgHom.kernelPoint (Bialgebra.counitAlgHom k H))) :
    topologicalKrullDim (Set.range (projectiveOrbitMap (H := H) m hm)) +
      ringKrullDim (H ⧸ D.toIdeal) = ringKrullDim H := by
  have := Algebra.FiniteType.isNoetherianRing k H
  let f := toProjectiveOrbit (H := H) m hm
  let x₀ := Bialgebra.augmentationPoint k H
  have hB := f.coheight_eq_coheight_add_coheight_preimage x₀
  -- The identity has codimension `dim G`.
  have h₁ : (coheight x₀ : WithBot ℕ∞) = ringKrullDim H := by
    rw [← idealHeight_eq_coheight, HopfAlgebra.ringKrullDim_eq_height_augmentation (k := k)]
    simp [x₀]
  -- Its image is a closed point, of codimension `dim O`.
  have h₂ : (coheight (f x₀) : WithBot ℕ∞) =
      topologicalKrullDim (Set.range (projectiveOrbitMap (H := H) m hm)) := by
    rw [← topologicalKrullDim_projectiveOrbitScheme]
    refine coheight_eq_topologicalKrullDim_of_mem_closedPoints m hm ?_
    rw [← range_toProjectiveOrbit_kernelPoint_eq_closedPoints m hm]
    exact ⟨toConv (Bialgebra.counitAlgHom k H), rfl⟩
  -- Its codimension in the fibre, the closed subgroup cut out by `D`, is `dim D`: the height of
  -- the augmentation ideal of `H ⧸ D`.
  have hfib := preimage_toProjectiveOrbit_augmentationPoint m hm D hstab
  have h₃ : (coheight (⟨x₀, rfl⟩ : f ⁻¹' {f x₀}) : WithBot ℕ∞) =
      ringKrullDim (H ⧸ D.toIdeal) := by
    have hx₀ : D.toIdeal ≤ x₀.asIdeal := hfib.subset rfl
    have hε : (Bialgebra.counitAlgHom k (H ⧸ D.toIdeal)).comp
        (Ideal.Quotient.mkₐ k D.toIdeal) = Bialgebra.counitAlgHom k H := by
      ext h
      simp
    have hx₀I : x₀.asIdeal = RingHom.ker (Bialgebra.counitAlgHom k H : H →+* k) :=
      AlgHom.kernelPoint_asIdeal _
    rw [← coheight_orderIso (Set.orderIsoOfEq _ _ hfib) ⟨x₀, rfl⟩,
      HopfAlgebra.ringKrullDim_eq_height_augmentation (k := k) (H := H ⧸ D.toIdeal)]
    refine congrArg _
      ((AlgebraicGeometry.coheight_zeroLocus_eq_height_map D.toIdeal x₀ hx₀).trans ?_)
    rw [hx₀I, ← hε, AlgHom.comp_toRingHom, ← RingHom.comap_ker]
    exact congrArg Ideal.height (Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective _)
  rw [← h₁, hB, WithBot.coe_add, h₂, h₃]

end TauCeti.Comodule

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.Orbit
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.Regular
public import TauCeti.Algebra.AlgebraicGroup.Representation.Orbit.ClosureOrder
import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.ClosedOrbit
import TauCeti.RingTheory.KrullDimension.FiniteType

/-!
# Centralizers along the boundary of an adjoint orbit

For a finite-type affine group over an algebraically closed field of characteristic zero,
a rational point in the boundary of an adjoint orbit has a strictly larger centralizer,
both as a Lie algebra and as an algebraic group. The orbits here are the full scheme-point
images in the projective completion of the Lie algebra; the boundary condition concerns
the point represented by `(y, 1)`, so it is a degeneration inside the Lie algebra.
The scheme-theoretic centralizer comparison also holds in arbitrary characteristic when
the group is reduced.

Consequently a regular element, in the minimal-centralizer sense, cannot lie in the boundary
of any adjoint orbit. If a regular element lies in an orbit closure, it already lies in that
orbit. These results apply to nilpotent orbits without assuming nilpotence, connectedness,
or semisimplicity of the acting group.

In the closure order on adjoint orbits (`TauCeti.Comodule.VectorOrbit` for the adjoint
representation), an orbit lying strictly below the orbit of `x` has dimension smaller than
`dim [𝔤, x]` (`TauCeti.finrank_range_ad_lt_of_mk_lt_mk`).

The proof uses the strict dimension drop for projective boundary orbits, the adjoint orbit
dimension formula, and rank-nullity. It compares dimensions, without asserting an inclusion
between the two centralizer subgroups.

## References

* D. H. Collingwood and W. M. McGovern, *Nilpotent Orbits in Semisimple Lie Algebras*,
  Van Nostrand Reinhold, 1993, Chapter 1 and §4.1.
* J. E. Humphreys, *Linear Algebraic Groups*, GTM 21, §8.3.
-/

public section

open AlgebraicGeometry

namespace TauCeti

universe u

variable {k H : Type u} [Field k] [IsAlgClosed k] [CommRing H]
  [HopfAlgebra k H] [Algebra.FiniteType k H]

attribute [local instance] Derivation.adjointComodule Comodule.prodTrivial

/-- The Lie centralizer strictly increases in dimension at a rational boundary point of
an adjoint orbit. The boundary is taken in the projective completion of the Lie algebra. -/
theorem finrank_ker_ad_lt_of_mem_adjointOrbit_boundary [CharZero k]
    {x y : Module.Dual k (Bialgebra.CotangentSpace k H)}
    (hy : Comodule.projectiveOrbitMap (H := H) (y, (1 : k)) (Module.isUnimodular_mk_one y)
        (AlgHom.kernelPoint (Bialgebra.counitAlgHom k H)) ∈
      closure (Set.range (Comodule.projectiveOrbitMap (H := H)
        (x, (1 : k)) (Module.isUnimodular_mk_one x))) \
        Set.range (Comodule.projectiveOrbitMap (H := H)
          (x, (1 : k)) (Module.isUnimodular_mk_one x))) :
    Module.finrank k (LinearMap.ker
        (LieAlgebra.ad k (Module.Dual k (Bialgebra.CotangentSpace k H)) x)) <
      Module.finrank k (LinearMap.ker
        (LieAlgebra.ad k (Module.Dual k (Bialgebra.CotangentSpace k H)) y)) := by
  have hrank := Comodule.topologicalKrullDim_range_projectiveOrbitMap_lt
    (Module.isUnimodular_mk_one x) (Module.isUnimodular_mk_one y) hy
  rw [topologicalKrullDim_range_projectiveOrbitMap_mk_one_eq_finrank_range_ad,
    topologicalKrullDim_range_projectiveOrbitMap_mk_one_eq_finrank_range_ad] at hrank
  norm_cast at hrank
  have hx := LinearMap.finrank_range_add_finrank_ker
    (LieAlgebra.ad k (Module.Dual k (Bialgebra.CotangentSpace k H)) x)
  have hy := LinearMap.finrank_range_add_finrank_ker
    (LieAlgebra.ad k (Module.Dual k (Bialgebra.CotangentSpace k H)) y)
  omega

/-- The scheme-theoretic centralizer strictly increases in dimension at a rational boundary
point of an adjoint orbit of a reduced group, in arbitrary characteristic. Dimensions are
Krull dimensions of the coordinate algebras. -/
theorem ringKrullDim_centralizer_lt_of_mem_adjointOrbit_boundary [IsReduced H]
    {x y : Module.Dual k (Bialgebra.CotangentSpace k H)}
    (hy : Comodule.projectiveOrbitMap (H := H) (y, (1 : k)) (Module.isUnimodular_mk_one y)
        (AlgHom.kernelPoint (Bialgebra.counitAlgHom k H)) ∈
      closure (Set.range (Comodule.projectiveOrbitMap (H := H)
        (x, (1 : k)) (Module.isUnimodular_mk_one x))) \
        Set.range (Comodule.projectiveOrbitMap (H := H)
          (x, (1 : k)) (Module.isUnimodular_mk_one x))) :
    ringKrullDim (H ⧸ (centralizerHopfIdeal H x).toIdeal) <
      ringKrullDim (H ⧸ (centralizerHopfIdeal H y).toIdeal) := by
  have horbit := Comodule.topologicalKrullDim_range_projectiveOrbitMap_lt
    (Module.isUnimodular_mk_one x) (Module.isUnimodular_mk_one y) hy
  have hx := topologicalKrullDim_range_projectiveOrbitMap_add_ringKrullDim_centralizerHopfIdeal x
  have hy := topologicalKrullDim_range_projectiveOrbitMap_add_ringKrullDim_centralizerHopfIdeal y
  have := Bialgebra.nontrivial (A := H ⧸ (centralizerHopfIdeal H x).toIdeal) k
  have := finiteRingKrullDim_of_finiteType k (H ⧸ (centralizerHopfIdeal H x).toIdeal)
  have htop := ringKrullDim_ne_top (R := H ⧸ (centralizerHopfIdeal H x).toIdeal)
  lift ringKrullDim (H ⧸ (centralizerHopfIdeal H x).toIdeal) to ℕ∞
    using ringKrullDim_ne_bot with d
  lift d to ℕ using by simpa using htop
  simp only [ENat.WithBot.coe_eq_natCast] at hx ⊢
  by_contra h
  apply horbit.not_ge
  apply (ENat.WithBot.add_le_add_natCast_right_iff (c := d)).mp
  rw [hx, ← hy]
  exact add_le_add le_rfl (not_lt.mp h)

/-- A minimal-centralizer regular element in the closure of an adjoint orbit already belongs
to that orbit. In particular no adjoint orbit has a regular element in its boundary. -/
theorem mem_adjointOrbit_of_mem_closure_of_isCentralizerRegular [CharZero k]
    {x y : Module.Dual k (Bialgebra.CotangentSpace k H)}
    (hy : LieAlgebra.IsCentralizerRegular k y)
    (hyClosure : Comodule.projectiveOrbitMap (H := H)
        (y, (1 : k)) (Module.isUnimodular_mk_one y)
        (AlgHom.kernelPoint (Bialgebra.counitAlgHom k H)) ∈
      closure (Set.range (Comodule.projectiveOrbitMap (H := H)
        (x, (1 : k)) (Module.isUnimodular_mk_one x)))) :
    Comodule.projectiveOrbitMap (H := H) (y, (1 : k)) (Module.isUnimodular_mk_one y)
        (AlgHom.kernelPoint (Bialgebra.counitAlgHom k H)) ∈
      Set.range (Comodule.projectiveOrbitMap (H := H)
        (x, (1 : k)) (Module.isUnimodular_mk_one x)) := by
  by_contra h
  have hlt := finrank_ker_ad_lt_of_mem_adjointOrbit_boundary ⟨hyClosure, h⟩
  exact (LieAlgebra.isCentralizerRegular_iff_forall_finrank_ker_le.mp hy x).not_gt hlt

/-- **Strictly smaller adjoint orbits have strictly smaller dimension.** In characteristic zero,
if the adjoint orbit of `y` lies strictly below the adjoint orbit of `x` in the closure order,
then `[𝔤, y]` has smaller dimension than `[𝔤, x]`. -/
theorem finrank_range_ad_lt_of_mk_lt_mk [CharZero k]
    {x y : Module.Dual k (Bialgebra.CotangentSpace k H)}
    (h : (Comodule.VectorOrbit.mk y :
        Comodule.VectorOrbit k H (Module.Dual k (Bialgebra.CotangentSpace k H))) <
      Comodule.VectorOrbit.mk x) :
    Module.finrank k (LinearMap.range
        (LieAlgebra.ad k (Module.Dual k (Bialgebra.CotangentSpace k H)) y)) <
      Module.finrank k (LinearMap.range
        (LieAlgebra.ad k (Module.Dual k (Bialgebra.CotangentSpace k H)) x)) := by
  have hlt := Comodule.VectorOrbit.strictMono_topologicalKrullDim_image h
  beta_reduce at hlt
  rw [Comodule.VectorOrbit.image_mk, Comodule.VectorOrbit.image_mk,
    topologicalKrullDim_range_projectiveOrbitMap_mk_one_eq_finrank_range_ad,
    topologicalKrullDim_range_projectiveOrbitMap_mk_one_eq_finrank_range_ad] at hlt
  exact_mod_cast hlt

end TauCeti

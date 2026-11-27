/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.Node.Ordinary
public import TauCeti.AlgebraicGeometry.Curves.StableReduction.Model.Prestable

/-!
# Prestable models from their special fibre

Let `R` be a discrete valuation ring with fraction field `K` and residue field `k`, and let `M` be
a proper model over `R` of a prestable curve `C ⟶ Spec K`, for instance a smooth proper
geometrically connected curve (`TauCeti.AlgebraicGeometry.PrestableFamily.of_smooth`). This file
shows that `M` is a prestable model exactly when its special fibre `X_k` is geometrically
connected and every point of `X_k` is a smooth point or an ordinary node, in the étale-local sense
of `TauCeti.AlgebraicGeometry.IsOrdinaryNodeOrSmoothAt`. Equivalently, the same holds after base
change to any field extension of `k`, for instance an algebraic closure, over which the nodes are
split. When `X_k` has pure relative dimension one, it is also equivalent to ask, at each singular
point of `X_k`, for a point above it that is an ordinary node after some finite separable
extension of `k`.

Geometric reducedness of the special fibre is not assumed separately, and the geometric
irreducible components need not be smooth: a component may cross itself at an ordinary
node.

## Main results

* `TauCeti.Model.prestableFamily_toBase_iff_forall_isOrdinaryNodeOrSmoothAt`: the prestable
  criterion on the special fibre.
* `TauCeti.Model.prestableFamily_toBase_iff_forall_baseChange_isOrdinaryNodeOrSmoothAt`: the
  prestable criterion after base change to a field extension of the residue field.
* `TauCeti.Model.prestableFamily_toBase_iff_forall_notMem_smoothLocus_exists_isSeparable`: the
  equivalent criterion with finite separable residue extensions at the singular points, for a
  special fibre of pure relative dimension one.

## References

* [The Stacks Project, Section 55.18, Semistable reduction](https://stacks.math.columbia.edu/tag/0CDL)
* [The Stacks Project, Section 53.19, Tag 0C46](https://stacks.math.columbia.edu/tag/0C46)
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TauCeti.AlgebraicGeometry

namespace TauCeti

universe u

namespace Model

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K]
variable {C : Scheme.{u}} {toK : C ⟶ Spec (.of K)}

/-- **The prestable criterion.** A proper model of a prestable curve over a discrete valuation
ring is a prestable model exactly when its special fibre is geometrically connected and each of
its points is a smooth point or an ordinary node. -/
theorem prestableFamily_toBase_iff_forall_isOrdinaryNodeOrSmoothAt (M : Model R K C toK)
    [M.IsProper] [PrestableFamily toK] :
    PrestableFamily M.toBase ↔ GeometricallyConnected (specialFiber R M.toBase).hom ∧
      ∀ x, IsOrdinaryNodeOrSmoothAt (specialFiber R M.toBase).hom x := by
  rw [M.prestableFamily_toBase_iff_atWorstNodal,
    atWorstNodalOfRelativeDimensionOne_iff_forall_isOrdinaryNodeOrSmoothAt]

/-- **The prestable criterion after a field extension.** A proper model of a prestable curve over
a discrete valuation ring is a prestable model exactly when its special fibre is geometrically
connected and, after base change to a field extension `L` of the residue field (for instance an
algebraic closure), each point is a smooth point or an ordinary node. -/
theorem prestableFamily_toBase_iff_forall_baseChange_isOrdinaryNodeOrSmoothAt
    (M : Model R K C toK) [M.IsProper] [PrestableFamily toK] (L : Type u) [Field L]
    [Algebra (IsLocalRing.ResidueField R) L] :
    PrestableFamily M.toBase ↔ GeometricallyConnected (specialFiber R M.toBase).hom ∧
      ∀ x, IsOrdinaryNodeOrSmoothAt
        (pullback.fst (Spec.algebraMap (IsLocalRing.ResidueField R) L)
          (specialFiber R M.toBase).hom) x := by
  rw [M.prestableFamily_toBase_iff_atWorstNodal,
    atWorstNodalOfRelativeDimensionOne_iff_forall_baseChange_isOrdinaryNodeOrSmoothAt L]

/-- **The prestable criterion with finite separable residue extensions at singular points.** Let
`M` be a proper model of a prestable curve over a discrete valuation ring whose special fibre has
pure relative dimension one. Then `M` is a prestable model exactly when its special fibre is
geometrically connected and each point outside the smooth locus of the special fibre has, after
some finite separable extension `L` of the residue field depending on the point, a point above it
that is a smooth point or an ordinary node. -/
theorem prestableFamily_toBase_iff_forall_notMem_smoothLocus_exists_isSeparable
    (M : Model R K C toK) [M.IsProper] [PrestableFamily toK]
    [PureRelativeDimension 1 (specialFiber R M.toBase).hom] :
    PrestableFamily M.toBase ↔ GeometricallyConnected (specialFiber R M.toBase).hom ∧
      ∀ x ∉ (specialFiber R M.toBase).hom.smoothLocus, ∃ (L : Type u) (_ : Field L)
        (_ : Algebra (IsLocalRing.ResidueField R) L)
        (_ : FiniteDimensional (IsLocalRing.ResidueField R) L)
        (_ : Algebra.IsSeparable (IsLocalRing.ResidueField R) L)
        (y : ↥(pullback (Spec.algebraMap (IsLocalRing.ResidueField R) L)
          (specialFiber R M.toBase).hom)),
        pullback.snd _ (specialFiber R M.toBase).hom y = x ∧
          IsOrdinaryNodeOrSmoothAt (pullback.fst _ (specialFiber R M.toBase).hom) y := by
  rw [M.prestableFamily_toBase_iff_atWorstNodal,
    atWorstNodalOfRelativeDimensionOne_iff_forall_notMem_smoothLocus_exists_isSeparable]

end Model

end TauCeti

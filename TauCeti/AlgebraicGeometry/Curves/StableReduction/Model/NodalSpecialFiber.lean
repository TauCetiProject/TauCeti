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
connected and, after base change to a separably closed extension of `k` such as an algebraic
closure, every point is a smooth point or an ordinary node, in the étale-local sense of
`TauCeti.AlgebraicGeometry.IsOrdinaryNodeOrSmoothAt`. Equivalently, a finite separable residue
extension, chosen at each singular point of `X_k`, makes some point above it an ordinary node.

Geometric reducedness of the special fibre is not assumed separately, and the geometric
irreducible components need not be smooth: a component may cross itself at an ordinary
node.

## Main results

* `TauCeti.Model.prestableFamily_toBase_iff_atWorstNodal`: a proper model of a prestable curve is
  prestable exactly when its special fibre is geometrically connected and at worst nodal.
* `TauCeti.Model.prestableFamily_toBase_of_specialFiber`: a proper model of a prestable curve
  whose special fibre is geometrically connected with only ordinary nodes after some field
  extension is a prestable model.
* `TauCeti.Model.prestableFamily_toBase_iff_of_isSepClosed`: the prestable criterion after
  base change to a separably closed extension of the residue field.
* `TauCeti.Model.prestableFamily_toBase_iff_forall_notMem_smoothLocus_exists_isSeparable`: the
  equivalent criterion with finite separable residue extensions at the singular points.

## References

* [The Stacks Project, Section 55.18, Semistable reduction](https://stacks.math.columbia.edu/tag/0CDL)
* [The Stacks Project, Section 53.19, Tag 0C46](https://stacks.math.columbia.edu/tag/0C46)
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TauCeti.AlgebraicGeometry

namespace TauCeti

universe u

/-- The special fibre of a morphism locally of finite presentation is locally of finite
presentation over the residue field. -/
instance locallyOfFinitePresentation_specialFiber_hom {R : Type u} [CommRing R] [IsLocalRing R]
    {X : Scheme.{u}} (toBase : X ⟶ Spec (.of R)) [LocallyOfFinitePresentation toBase] :
    LocallyOfFinitePresentation (specialFiber R toBase).hom := by
  rw [specialFiber_hom]
  infer_instance

namespace Model

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K]
variable {C : Scheme.{u}} {toK : C ⟶ Spec (.of K)}

/-- A proper model of a prestable curve over a discrete valuation ring is a prestable model
exactly when its special fibre is geometrically connected and at worst nodal of relative
dimension one. -/
theorem prestableFamily_toBase_iff_atWorstNodal (M : Model R K C toK) [M.IsProper]
    [PrestableFamily toK] :
    PrestableFamily M.toBase ↔ GeometricallyConnected (specialFiber R M.toBase).hom ∧
      AtWorstNodalOfRelativeDimensionOne (specialFiber R M.toBase).hom := by
  rw [M.prestableFamily_toBase_iff]
  refine ⟨fun ⟨_, _, h⟩ ↦ ⟨inferInstance, h.atWorstNodalOfRelativeDimensionOne⟩,
    fun ⟨_, h⟩ ↦ ⟨‹_›, ‹_›, ?_⟩⟩
  have : AlgebraicGeometry.IsProper (specialFiber R M.toBase).hom :=
    MorphismProperty.of_isPullback (P := @AlgebraicGeometry.IsProper)
      (isPullback_specialFiber R M.toBase) inferInstance
  exact { atWorstNodalOfRelativeDimensionOne := h }

/-- **The prestable criterion.** A proper model of a prestable curve over a discrete valuation
ring is a prestable model when its special fibre is geometrically connected and, after a field
extension `L` of the residue field (for instance an algebraic closure), each point of the base
changed special fibre is a smooth point or an ordinary node. -/
theorem prestableFamily_toBase_of_specialFiber (M : Model R K C toK) [M.IsProper]
    [PrestableFamily toK] [GeometricallyConnected (specialFiber R M.toBase).hom]
    (L : Type u) [Field L] [Algebra (IsLocalRing.ResidueField R) L]
    (h : ∀ x, IsOrdinaryNodeOrSmoothAt
      (pullback.fst (Spec.algebraMap (IsLocalRing.ResidueField R) L)
        (specialFiber R M.toBase).hom) x) :
    PrestableFamily M.toBase :=
  M.prestableFamily_toBase_iff_atWorstNodal.mpr ⟨‹_›,
    AtWorstNodalOfRelativeDimensionOne.of_baseChange_isOrdinaryNodeOrSmoothAt L _ h⟩

/-- **The prestable criterion over a separable closure.** A proper model of a prestable curve
over a discrete valuation ring is a prestable model exactly when its special fibre is
geometrically connected and, after base change to a separably closed extension `L` of the residue
field (for instance an algebraic closure), each point is a smooth point or an ordinary node. -/
theorem prestableFamily_toBase_iff_of_isSepClosed (M : Model R K C toK) [M.IsProper]
    [PrestableFamily toK] (L : Type u) [Field L] [Algebra (IsLocalRing.ResidueField R) L]
    [IsSepClosed L] :
    PrestableFamily M.toBase ↔ GeometricallyConnected (specialFiber R M.toBase).hom ∧
      ∀ x, IsOrdinaryNodeOrSmoothAt
        (pullback.fst (Spec.algebraMap (IsLocalRing.ResidueField R) L)
          (specialFiber R M.toBase).hom) x := by
  rw [M.prestableFamily_toBase_iff_atWorstNodal,
    atWorstNodalOfRelativeDimensionOne_iff_forall_isOrdinaryNodeOrSmoothAt_of_isSepClosed L]

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

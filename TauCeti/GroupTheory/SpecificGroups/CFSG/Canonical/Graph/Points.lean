/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.Canonical.AmbientGroup
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Canonical.Graph.Steinberg
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Frobenius
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.GraphAutomorphism

/-!
# Graph-twisted Steinberg maps on the canonical ambient group

`GraphTwistedIndex.canonicalSteinberg` is the pinned graph action after field Frobenius on
`ValidLieTypeIndex.CanonicalAmbientGroup`. It specializes `GraphTwistedIndex.scSteinberg`
through the equality of the simply connected Chevalley points with the full-weight Kostant
toral points. This identification leaves every underlying matrix unchanged; it is not a
comparison with a represented family model. The map factors as `γ_σ ∘ Frob_q`, for the pinned
graph automorphism `DynkinType.chevalleyGraphAut` of the simply connected Chevalley group and the
datum's `q`-power Frobenius, and these two factors commute.

The root-subgroup equations, on every root and on the positive and negative simple roots, use
the canonical root maps, and the character pullback uses `ValidLieTypeIndex.canonicalTorus` in
fundamental-weight coordinates. All of them are read off the factorization `γ_σ ∘ Frob_q`. The
native twist-order iterate is the datum's `q^r`-Frobenius, namely `ChevalleyDatum.frobenius` at
`fieldExponent * twistOrder`. Thus the independently constructed map is available on the same
carrier as the canonical pinning, without assuming point generation.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapters 10–11.
* R. W. Carter, *Finite Groups of Lie Type*, §§1.15–1.17.
-/

public section

namespace TauCeti.GraphTwistedIndex

open DynkinType _root_.TauCeti.UniversalEnvelopingAlgebra

noncomputable section

variable (d : GraphTwistedIndex)

private def pointEquiv :=
  MulEquiv.subgroupCongr
    (d.1.dynkinType.chevalleyGroup_eq_kostantToralPointsSubgroup d.1.dynkinType_valid d.1.Closure)

/-- The pinned graph–Frobenius map on the canonical ambient group. The change of point
interface is the identity on matrices, not a conjugation by a represented-model comparison. -/
def canonicalSteinberg : d.1.CanonicalAmbientGroup →* d.1.CanonicalAmbientGroup :=
  MonoidHom.subgroupCongr
    (d.1.dynkinType.chevalleyGroup_eq_kostantToralPointsSubgroup d.1.dynkinType_valid d.1.Closure)
    (d.1.dynkinType.chevalleyGroup_eq_kostantToralPointsSubgroup d.1.dynkinType_valid d.1.Closure)
    (d.scSteinberg d.1.Closure)

/-- The canonical map is the full-weight Steinberg map with the point subgroup rewritten. -/
theorem canonicalSteinberg_def :
    d.canonicalSteinberg = MonoidHom.subgroupCongr
      (d.1.dynkinType.chevalleyGroup_eq_kostantToralPointsSubgroup d.1.dynkinType_valid d.1.Closure)
      (d.1.dynkinType.chevalleyGroup_eq_kostantToralPointsSubgroup d.1.dynkinType_valid d.1.Closure)
      (d.scSteinberg d.1.Closure) := (rfl)

private theorem coe_pointEquiv (g : d.1.CanonicalAmbientGroup) :
    (d.pointEquiv g : Matrix.GeneralLinearGroup
      (Fin (d.1.dynkinType.scWeightBasisCard d.1.dynkinType_valid)) d.1.Closure) =
      (g : Matrix.GeneralLinearGroup
        (Fin (d.1.dynkinType.scWeightBasisCard d.1.dynkinType_valid)) d.1.Closure) :=
  MulEquiv.subgroupCongr_apply _ g

private theorem pointEquiv_canonicalSteinberg (g : d.1.CanonicalAmbientGroup) :
    d.pointEquiv (d.canonicalSteinberg g) = d.scSteinberg d.1.Closure (d.pointEquiv g) := by
  apply Subtype.ext
  simp only [coe_pointEquiv, canonicalSteinberg_def, MonoidHom.coe_subgroupCongr_apply]
  exact congrArg (fun y => (d.scSteinberg d.1.Closure y : Matrix.GeneralLinearGroup
    (Fin (d.1.dynkinType.scWeightBasisCard d.1.dynkinType_valid)) d.1.Closure))
    (Subtype.ext (d.coe_pointEquiv g)).symm

/-- On every canonical point, the Steinberg map is integral lattice conjugation after
entrywise Frobenius, without a point-generation hypothesis. -/
@[simp]
theorem coe_canonicalSteinberg (g : d.1.CanonicalAmbientGroup) :
    (d.canonicalSteinberg g : Matrix.GeneralLinearGroup
      (Fin (d.1.dynkinType.scWeightBasisCard d.1.dynkinType_valid)) d.1.Closure) =
      kostantNumberedSymmetryMatrix
          (d.1.dynkinType.scLattice d.1.dynkinType_valid).toAddSubgroup
          (d.1.dynkinType.scWeightBasis d.1.dynkinType_valid)
          (d.1.dynkinType.scModuleDiagramEquiv d.1.dynkinType_valid
            d.diagramPerm_mem_diagramSymmetry)
          (fun _ => d.1.dynkinType.scModuleDiagramEquiv_mem_scLattice_iff
            d.1.dynkinType_valid d.diagramPerm_mem_diagramSymmetry) d.1.Closure *
        Matrix.GeneralLinearGroup.map
          (iterateFrobenius d.1.Closure d.1.characteristic d.1.fieldExponent) g *
      (kostantNumberedSymmetryMatrix
          (d.1.dynkinType.scLattice d.1.dynkinType_valid).toAddSubgroup
          (d.1.dynkinType.scWeightBasis d.1.dynkinType_valid)
          (d.1.dynkinType.scModuleDiagramEquiv d.1.dynkinType_valid
            d.diagramPerm_mem_diagramSymmetry)
          (fun _ => d.1.dynkinType.scModuleDiagramEquiv_mem_scLattice_iff
            d.1.dynkinType_valid d.diagramPerm_mem_diagramSymmetry) d.1.Closure)⁻¹ := by
  have h := congrArg Subtype.val (d.pointEquiv_canonicalSteinberg g)
  simpa only [coe_pointEquiv, coe_scSteinberg] using h

/-- **The canonical Steinberg map is the graph automorphism after Frobenius**, pointwise:
`Fᶜ g = γ_σ (Frob_q g)`, for the pinned graph automorphism `γ_σ` of the simply connected
Chevalley group at the index's diagram permutation and the `q`-power Frobenius. -/
theorem canonicalSteinberg_apply (g : d.1.CanonicalAmbientGroup) :
    d.canonicalSteinberg g =
      d.1.dynkinType.chevalleyGraphAut d.1.dynkinType_valid d.diagramPerm_mem_diagramSymmetry
        d.1.Closure
        ((d.1.dynkinType.scChevalleyDatum d.1.dynkinType_valid).frobenius d.1.characteristic
          d.1.fieldExponent d.1.Closure g) := by
  apply Subtype.ext
  rw [coe_canonicalSteinberg]
  refine Eq.trans ?_ (coe_chevalleyGraphAut _ _ _ _).symm
  congr 2
  exact ((d.1.dynkinType.scChevalleyDatum d.1.dynkinType_valid).coe_frobenius d.1.characteristic
    d.1.fieldExponent d.1.Closure g).symm

/-- **The canonical Steinberg map is the graph automorphism after Frobenius**:
`Fᶜ = γ_σ ∘ Frob_q`. -/
theorem canonicalSteinberg_eq_chevalleyGraphAut_comp_frobenius :
    d.canonicalSteinberg =
      (d.1.dynkinType.chevalleyGraphAut d.1.dynkinType_valid d.diagramPerm_mem_diagramSymmetry
          d.1.Closure).toMonoidHom.comp
        ((d.1.dynkinType.scChevalleyDatum d.1.dynkinType_valid).frobenius d.1.characteristic
          d.1.fieldExponent d.1.Closure) :=
  MonoidHom.ext d.canonicalSteinberg_apply

/-- **The graph and Frobenius factors of the canonical Steinberg map commute**:
`Fᶜ = Frob_q ∘ γ_σ`. -/
theorem canonicalSteinberg_eq_frobenius_comp_chevalleyGraphAut :
    d.canonicalSteinberg =
      ((d.1.dynkinType.scChevalleyDatum d.1.dynkinType_valid).frobenius d.1.characteristic
          d.1.fieldExponent d.1.Closure).comp
        (d.1.dynkinType.chevalleyGraphAut d.1.dynkinType_valid d.diagramPerm_mem_diagramSymmetry
          d.1.Closure).toMonoidHom :=
  d.canonicalSteinberg_eq_chevalleyGraphAut_comp_frobenius.trans
    (chevalleyGraphAut_comp_frobenius _ _ _ _ _)

/-- **The canonical Steinberg map on every root subgroup**: it sends `x_α(u)` to
`x_{σ α}(ε u ^ q)`, where `σ α` is the image of `α` under the diagram permutation and `ε = ±1` is
the sign of the graph automorphism on the Chevalley root vector at `α`. -/
@[simp low]
theorem canonicalSteinberg_canonicalRootSubgroup (α : Fin d.1.dynkinType.numRoots)
    (u : d.1.Closure) :
    d.canonicalSteinberg (d.1.canonicalRootSubgroup α (Multiplicative.ofAdd u)) =
      d.1.canonicalRootSubgroup
        (d.1.dynkinType.diagramRootPerm d.1.dynkinType_valid d.diagramPerm_mem_diagramSymmetry α)
        (Multiplicative.ofAdd (((d.1.dynkinType.chevalleyDiagramSign d.1.dynkinType_valid
          d.diagramPerm_mem_diagramSymmetry α : ℤ) : d.1.Closure) * u ^ d.1.fieldOrder)) := by
  have h := congrArg (d.1.dynkinType.chevalleyGraphAut d.1.dynkinType_valid
    d.diagramPerm_mem_diagramSymmetry d.1.Closure)
    ((d.1.dynkinType.scChevalleyDatum d.1.dynkinType_valid).frobenius_rootSubgroupPoints
      d.1.characteristic d.1.fieldExponent d.1.Closure α u)
  rw [chevalleyGraphAut_rootSubgroupPoints, ← d.1.fieldOrder_eq_characteristic_pow] at h
  -- The canonical root maps are unfolded last: their codomain is the canonical ambient group, so
  -- the datum equation `h` applies to them only up to definitional unfolding.
  rw [canonicalSteinberg_apply, ValidLieTypeIndex.canonicalRootSubgroup_def,
    ValidLieTypeIndex.canonicalRootSubgroup_def]
  exact h

/-- On a positive simple root, the canonical Steinberg map applies the selected diagram
permutation and raises the additive parameter to the small-field order. -/
@[simp]
theorem canonicalSteinberg_canonicalRootSubgroup_simpleIndex (i : Fin d.1.rank)
    (u : Multiplicative d.1.Closure) :
    d.canonicalSteinberg
      (d.1.canonicalRootSubgroup (d.1.dynkinType.simpleIndex d.1.dynkinType_valid i)
        u) =
      d.1.canonicalRootSubgroup
        (d.1.dynkinType.simpleIndex d.1.dynkinType_valid (d.diagramPerm i))
        (Multiplicative.ofAdd (Multiplicative.toAdd u ^ d.1.fieldOrder)) := by
  have h := congrArg (d.1.dynkinType.chevalleyGraphAut d.1.dynkinType_valid
    d.diagramPerm_mem_diagramSymmetry d.1.Closure)
    ((d.1.dynkinType.scChevalleyDatum d.1.dynkinType_valid).frobenius_rootSubgroupPoints
      d.1.characteristic d.1.fieldExponent d.1.Closure
      (d.1.dynkinType.simpleIndex d.1.dynkinType_valid i) (Multiplicative.toAdd u))
  rw [chevalleyGraphAut_rootSubgroupPoints_simpleIndex,
    ← d.1.fieldOrder_eq_characteristic_pow] at h
  -- The canonical root maps are unfolded last: their codomain is the canonical ambient group, so
  -- the datum equation `h` applies to them only up to definitional unfolding.
  rw [canonicalSteinberg_apply, ValidLieTypeIndex.canonicalRootSubgroup_def,
    ValidLieTypeIndex.canonicalRootSubgroup_def]
  exact h

/-- On a negative simple root, the canonical Steinberg map applies `d.diagramPerm` and
raises the additive parameter to the small-field order `d.1.fieldOrder`. -/
@[simp]
theorem canonicalSteinberg_canonicalRootSubgroup_reflectionPerm_simpleIndex
    (i : Fin d.1.rank) (u : Multiplicative d.1.Closure) :
    d.canonicalSteinberg
      (d.1.canonicalRootSubgroup
        ((d.1.dynkinType.simplyConnectedRootDatum d.1.dynkinType_valid).reflectionPerm
          (d.1.dynkinType.simpleIndex d.1.dynkinType_valid i)
          (d.1.dynkinType.simpleIndex d.1.dynkinType_valid i)) u) =
      d.1.canonicalRootSubgroup
        ((d.1.dynkinType.simplyConnectedRootDatum d.1.dynkinType_valid).reflectionPerm
          (d.1.dynkinType.simpleIndex d.1.dynkinType_valid (d.diagramPerm i))
          (d.1.dynkinType.simpleIndex d.1.dynkinType_valid (d.diagramPerm i)))
        (Multiplicative.ofAdd (Multiplicative.toAdd u ^ d.1.fieldOrder)) := by
  have h := congrArg (d.1.dynkinType.chevalleyGraphAut d.1.dynkinType_valid
    d.diagramPerm_mem_diagramSymmetry d.1.Closure)
    ((d.1.dynkinType.scChevalleyDatum d.1.dynkinType_valid).frobenius_rootSubgroupPoints
      d.1.characteristic d.1.fieldExponent d.1.Closure
      ((d.1.dynkinType.simplyConnectedRootDatum d.1.dynkinType_valid).reflectionPerm
        (d.1.dynkinType.simpleIndex d.1.dynkinType_valid i)
        (d.1.dynkinType.simpleIndex d.1.dynkinType_valid i)) (Multiplicative.toAdd u))
  rw [chevalleyGraphAut_rootSubgroupPoints_reflectionPerm_simpleIndex,
    ← d.1.fieldOrder_eq_characteristic_pow] at h
  -- The canonical root maps are unfolded last: their codomain is the canonical ambient group, so
  -- the datum equation `h` applies to them only up to definitional unfolding.
  rw [canonicalSteinberg_apply, ValidLieTypeIndex.canonicalRootSubgroup_def,
    ValidLieTypeIndex.canonicalRootSubgroup_def]
  exact h

/-- The character pullback on the canonical torus is the native datum Steinberg weight map,
including the inverse diagram action. -/
theorem isCharacterMap_canonicalSteinberg :
    IsCharacterMap d.1.canonicalTorus d.canonicalSteinberg d.datumSteinberg.weightMap := by
  have h := (isCharacterMap_chevalleyGraphAut d.1.dynkinType_valid
    d.diagramPerm_mem_diagramSymmetry d.1.Closure).comp
      ((d.1.dynkinType.scChevalleyDatum d.1.dynkinType_valid).isCharacterMap_frobenius
        d.1.characteristic d.1.fieldExponent d.1.Closure)
  rw [smul_mul_assoc, one_mul] at h
  rw [d.canonicalSteinberg_eq_chevalleyGraphAut_comp_frobenius, datumSteinberg_weightMap,
    datumGraphAut_def, d.1.fieldOrder_eq_characteristic_pow, LinearMap.comp_smul,
    LinearMap.comp_id, ValidLieTypeIndex.canonicalTorus_def]
  exact h

/-- In fundamental-weight coordinates, the canonical map raises to `q` and relabels by the
inverse diagram permutation. -/
@[simp]
theorem canonicalSteinberg_canonicalTorus (s : Fin d.1.rank → d.1.Closureˣ) :
    d.canonicalSteinberg (d.1.canonicalTorus s) =
      d.1.canonicalTorus (fun j => s (d.diagramPerm⁻¹ j) ^ d.1.fieldOrder) := by
  have h := congrArg (d.1.dynkinType.chevalleyGraphAut d.1.dynkinType_valid
    d.diagramPerm_mem_diagramSymmetry d.1.Closure)
    ((d.1.dynkinType.scChevalleyDatum d.1.dynkinType_valid).frobenius_torusPoints
      d.1.characteristic d.1.fieldExponent d.1.Closure s)
  rw [chevalleyGraphAut_torusPoints, ← d.1.fieldOrder_eq_characteristic_pow] at h
  rw [canonicalSteinberg_apply, ValidLieTypeIndex.canonicalTorus_def]
  exact h

/-- The native twist-order iterate on canonical points is `q^r`-Frobenius. The field
Frobenius iteration index is the product of the field exponent and the twist order. -/
-- Select composition, rather than pointwise operations on bundled homomorphisms.
theorem canonicalSteinberg_pow_twistOrder :
    (show _root_.Monoid.End _ from d.canonicalSteinberg) ^ d.twistOrder =
      (d.1.dynkinType.scChevalleyDatum d.1.dynkinType_valid).frobenius
        d.1.characteristic (d.1.fieldExponent * d.twistOrder) d.1.Closure := by
  have h : Function.Semiconj d.pointEquiv d.canonicalSteinberg (d.scSteinberg d.1.Closure) :=
    d.pointEquiv_canonicalSteinberg
  apply MonoidHom.ext
  intro g
  apply Subtype.ext
  have hp := (congrArg d.pointEquiv
    (congrFun (_root_.Monoid.End.coe_pow _ d.canonicalSteinberg d.twistOrder) g)).trans
      ((h.iterate_right d.twistOrder g).trans
        (congrFun (_root_.Monoid.End.coe_pow _ (d.scSteinberg d.1.Closure) d.twistOrder)
          (d.pointEquiv g)).symm)
  have hF := congrArg (fun F : _root_.Monoid.End _ => F (d.pointEquiv g))
    (d.scSteinberg_pow_twistOrder d.1.Closure)
  refine (d.coe_pointEquiv _).symm.trans ((congrArg Subtype.val (hp.trans hF)).trans ?_)
  refine (coe_kostantToralFrobenius _ _ _ _ _ _ _ _ _ _ _ (d.pointEquiv g)).trans ?_
  exact (congrArg (Matrix.GeneralLinearGroup.map
    (iterateFrobenius d.1.Closure d.1.characteristic (d.1.fieldExponent * d.twistOrder)))
      (d.coe_pointEquiv g)).trans
    ((d.1.dynkinType.scChevalleyDatum d.1.dynkinType_valid).coe_frobenius
      d.1.characteristic (d.1.fieldExponent * d.twistOrder) d.1.Closure g).symm

end

end TauCeti.GraphTwistedIndex

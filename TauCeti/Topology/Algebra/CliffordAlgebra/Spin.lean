/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Real.Stabilizer
public import TauCeti.Topology.Algebra.CliffordAlgebra.Basic
public import TauCeti.Topology.Algebra.QuadraticForm.SpecialOrthogonal
public import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Topology on Clifford Spin groups

This file uses the canonical subtype topology on a Spin group inside a topological Clifford
algebra. The surrounding Clifford algebra has its module topology from
`TauCeti.Topology.Algebra.CliffordAlgebra.Basic`. A special orthogonal group in coordinates has the
independently induced topology from `TauCeti.Topology.Algebra.QuadraticForm.SpecialOrthogonal`.

For a quadratic form on a finite coordinate space, continuity of the Spin projection is proved
from the explicit Clifford conjugation formula for `spinVectorAction`. This supplies a bundled
continuous homomorphism over ℝ and ℂ. In particular, it gives the topological-group bridge for
the compact real double cover at signature `(n, 0)`. It makes no smoothness, compactness,
connectedness,
simple-connectivity, fibration, or universal-cover claim.

## Continuity argument

For `x : spinGroup Q` and a vector `v`, the public action equation gives

`ι Q (spinVectorAction Q x v) = x * ι Q v * star x`.

On the Spin group, `star x` is the inverse of `x`. The subtype coercion and Clifford star are
continuous, so the right-hand side is jointly continuous in `x` and `v`. The continuous vector-part
map `ιInv Q` is a left inverse to `ι Q`; applying it proves continuity of the Spin action.

A map into matrices is continuous exactly when each matrix entry is continuous. The `(i, j)` entry
of the standard matrix of the Spin action is the `i`th coordinate of the action on
`Pi.single j 1`. The fixed-vector result therefore proves continuity into the independently
topologized special orthogonal group.

## Main results

* `QuadraticMap.Isometry.continuous_spinGroupMap` proves continuity of the Spin-group map induced
  by an isometry of quadratic spaces.
* `QuadraticMap.Isometry.isEmbedding_spinGroupMap` restricts an embedding of the induced Clifford
  map to the corresponding Spin groups.
* `CliffordAlgebra.instIsTopologicalGroupSpinGroup` equips `spinGroup Q` with a topological
  group structure for its canonical subtype topology.
* `CliffordAlgebra.continuous_spinVectorAction` proves joint continuity of the Spin action.
* `CliffordAlgebra.continuous_spinVectorAction_apply` proves fixed-vector continuity of the Spin
  action.
* `QuadraticForm.isClosed_spinVectorStabilizer` proves that every vector stabilizer is closed.
* `CliffordAlgebra.continuous_spinToSpecialOrthogonal_pi` proves continuity of the Spin
  projection for every quadratic form on a finite coordinate space.
* `CliffordAlgebra.spinToSpecialOrthogonalHom` bundles the projection as a continuous
  monoid homomorphism.
* `CliffordAlgebra.continuous_realCliffordSpinDoubleCoverZero_rightHom` specializes this result to
  the projection field of the packaged compact real double cover.
* `CliffordAlgebra.continuous_realCliffordSpinInclusion` proves continuity of the lower-rank
  inclusion used in the compact stabilizer construction.
* `CliffordAlgebra.isEmbedding_realCliffordSpinInclusion` strengthens this inclusion to a
  topological embedding.
* `CliffordAlgebra.isEmbedding_realCliffordSpinStabilizerInclusion` proves that the lower-rank
  inclusion into the last-vector stabilizer is a topological embedding.
* `CliffordAlgebra.isClosed_realCliffordSpinLastStabilizer` proves that this stabilizer is closed.
* `CliffordAlgebra.continuous_realCliffordSpinStabilizerInclusion` proves continuity after
  restricting the inclusion's codomain to the last-vector stabilizer.

## References

H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I §2.
-/

public section


namespace QuadraticMap.Isometry

universe u v w


section

variable {R : Type u} [CommRing R]
  {V : Type v} {W : Type w}
  [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
  {Q : QuadraticForm R V} {P : QuadraticForm R W}
  [TopologicalSpace (CliffordAlgebra Q)] [TopologicalSpace (CliffordAlgebra P)]

/-- An embedding of the Clifford-algebra map induced by a quadratic isometry restricts to an
embedding of the corresponding Spin groups for their subtype topologies. -/
theorem isEmbedding_spinGroupMap (f : Q →qᵢ P)
    (hf : Topology.IsEmbedding (CliffordAlgebra.map f)) :
    Topology.IsEmbedding f.spinGroupMap := by
  have hmaps : Set.MapsTo (CliffordAlgebra.map f) (spinGroup Q) (spinGroup P) :=
    fun x hx => f.map_mem_spinGroup ⟨x, hx⟩
  convert hf.restrict hmaps using 1
  ext x
  exact coe_spinGroupMap_apply f x

end


variable {R : Type*} [CommRing R] [TopologicalSpace R]
  {V : Type u} {W : Type v}
  [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
  {Q : QuadraticForm R V} {P : QuadraticForm R W}

/-- The Spin-group map induced by an isometry of quadratic spaces is continuous for the
canonical subtype topologies. -/
@[fun_prop]
theorem continuous_spinGroupMap (f : Q →qᵢ P) : Continuous f.spinGroupMap := by
  apply continuous_induced_rng.mpr
  refine (f.continuous_cliffordAlgebraMap.comp
    continuous_subtype_val).congr ?_
  exact fun x ↦ (coe_spinGroupMap_apply f x).symm

end QuadraticMap.Isometry


namespace CliffordAlgebra

open TauCeti

noncomputable section

universe u v


variable {R : Type u} [CommRing R] [TopologicalSpace R]
  {V : Type v} [AddCommGroup V] [Module R V]

/-- A Spin group inside a continuously multiplicative Clifford algebra is a topological group for
its subtype topology. Multiplication is inherited from the Clifford algebra, while inversion is
Clifford star. -/
instance instIsTopologicalGroupSpinGroup (Q : QuadraticForm R V)
    [ContinuousMul (CliffordAlgebra Q)] :
    IsTopologicalGroup (spinGroup Q) where
  continuous_mul := continuous_mul
  continuous_inv := continuous_induced_rng.mpr continuous_subtype_val.star

/-- The Spin action is jointly continuous in the Spin element and the vector. -/
@[fun_prop]
theorem continuous_spinVectorAction [Invertible (2 : R)]
    [TopologicalSpace V] [IsModuleTopology R V] (Q : QuadraticForm R V)
    [ContinuousMul (CliffordAlgebra Q)] :
    Continuous (fun p : spinGroup Q × V => spinVectorAction Q p.1 p.2) := by
  let _ : IsTopologicalAddGroup V := IsModuleTopology.isTopologicalAddGroup R V
  have hval : Continuous (fun p : spinGroup Q × V => (p.1 : CliffordAlgebra Q)) :=
    continuous_subtype_val.comp continuous_fst
  have hι : Continuous (fun p : spinGroup Q × V => ι Q p.2) :=
    (IsModuleTopology.continuous_of_linearMap (ι Q)).comp continuous_snd
  have hstar : Continuous (fun p : spinGroup Q × V => star (p.1 : CliffordAlgebra Q)) :=
    (continuous_subtype_val.comp continuous_fst).star
  have hprod : Continuous (fun p : spinGroup Q × V =>
      (p.1 : CliffordAlgebra Q) * ι Q p.2 * star (p.1 : CliffordAlgebra Q)) :=
    (hval.mul hι).mul hstar
  have hvector := (IsModuleTopology.continuous_of_linearMap (ιInv Q)).comp hprod
  convert hvector using 1
  funext p
  rw [← ιInv_ι Q (spinVectorAction Q p.1 p.2), ι_spinVectorAction_apply]
  rfl

/-- For a fixed vector, its image under the Spin action depends continuously on the Spin
element. -/
@[fun_prop]
theorem continuous_spinVectorAction_apply [Invertible (2 : R)]
    [TopologicalSpace V] [IsModuleTopology R V] (Q : QuadraticForm R V)
    [ContinuousMul (CliffordAlgebra Q)] (v : V) :
    Continuous (fun x : spinGroup Q => spinVectorAction Q x v) := by
  have hpair : Continuous (fun x : spinGroup Q => (x, v)) := by fun_prop
  convert (continuous_spinVectorAction Q).comp hpair using 1
  rfl

/-- The subgroup of a Spin group fixing a vector is closed when the vector space is T1. -/
theorem _root_.QuadraticForm.isClosed_spinVectorStabilizer
    [Invertible (2 : R)] [TopologicalSpace V] [IsModuleTopology R V] [T1Space V]
    (Q : QuadraticForm R V) [ContinuousMul (CliffordAlgebra Q)] (v : V) :
    IsClosed {x : spinGroup Q | spinVectorAction Q x v = v} := by
  exact isClosed_singleton.preimage (CliffordAlgebra.continuous_spinVectorAction_apply Q v)

/-- The Spin action of a quadratic form on a finite coordinate space is continuous as a map to
the special orthogonal group with its standard coordinate topology. -/
@[fun_prop]
theorem continuous_spinToSpecialOrthogonal_pi [IsTopologicalRing R] [Invertible (2 : R)]
    {n : Type v} [Fintype n] [DecidableEq n] (Q : QuadraticForm R (n → R))
    [ContinuousMul (CliffordAlgebra Q)] :
    Continuous (spinToSpecialOrthogonal Q) := by
  apply (TauCeti.QuadraticMap.isEmbedding_specialOrthogonalToGeneralLinear
    Q).isInducing.continuous_iff.mpr
  have h : Continuous
      ((TauCeti.QuadraticMap.specialOrthogonalToGeneralLinear Q).comp
        (spinToSpecialOrthogonal Q)) := by
    apply Continuous.of_coeHom_comp
    apply continuous_matrix
    intro i j
    simpa only [MonoidHom.comp_apply, Units.coeHom_apply,
      TauCeti.QuadraticMap.specialOrthogonalToGeneralLinear_apply,
      coe_spinToSpecialOrthogonal_apply, Function.comp_def] using
      (continuous_apply i).comp
        (continuous_spinVectorAction_apply Q (Pi.single j 1))
  simpa only [MonoidHom.coe_comp] using h

/-- The Spin projection to the special orthogonal group as a continuous monoid homomorphism. -/
noncomputable def spinToSpecialOrthogonalHom [IsTopologicalRing R] [Invertible (2 : R)]
    {n : Type v} [Fintype n] [DecidableEq n] (Q : QuadraticForm R (n → R))
    [ContinuousMul (CliffordAlgebra Q)] :
    ContinuousMonoidHom (spinGroup Q) (TauCeti.QuadraticMap.specialOrthogonalGroup Q) where
  toMonoidHom := spinToSpecialOrthogonal Q
  continuous_toFun := continuous_spinToSpecialOrthogonal_pi Q

@[simp]
theorem spinToSpecialOrthogonalHom_apply [IsTopologicalRing R] [Invertible (2 : R)]
    {n : Type v} [Fintype n] [DecidableEq n] (Q : QuadraticForm R (n → R))
    [ContinuousMul (CliffordAlgebra Q)] (x : spinGroup Q) :
    spinToSpecialOrthogonalHom Q x = spinToSpecialOrthogonal Q x :=
  (rfl)

section Real

variable {V : Type v} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

/-- The projection field of the compact real Spin double cover is continuous. -/
@[fun_prop]
theorem continuous_realCliffordSpinDoubleCoverZero_rightHom (n : ℕ) [NeZero n] :
    Continuous (realCliffordSpinDoubleCoverZero n).rightHom := by
  rw [realCliffordSpinDoubleCoverZero_rightHom]
  exact continuous_spinToSpecialOrthogonal_pi (realCliffordForm n 0)

/-- The canonical inclusion `Spin(n) → Spin(n + 1)` is a topological embedding for every `n`. -/
theorem isEmbedding_realCliffordSpinInclusion (n : ℕ) :
    Topology.IsEmbedding (realCliffordSpinInclusion n) := by
  have hmap : Topology.IsEmbedding
      (CliffordAlgebra.map (realCliffordSpinInclusionIsometry n)) :=
    (LinearMap.isClosedEmbedding_of_injective
      ((CliffordAlgebra.map (realCliffordSpinInclusionIsometry n)).toLinearMap.ker_eq_bot.mpr
        (realCliffordSpinInclusionIsometry_map_injective n))).isEmbedding
  rw [realCliffordSpinInclusion_eq_spinGroupMap]
  exact (realCliffordSpinInclusionIsometry n).isEmbedding_spinGroupMap hmap

/-- The lower-rank inclusion `Spin(n) → Spin(n + 1)` is continuous for the canonical real
Clifford-algebra subtype topologies. -/
@[fun_prop]
theorem continuous_realCliffordSpinInclusion (n : ℕ) :
    Continuous (realCliffordSpinInclusion n) :=
  (isEmbedding_realCliffordSpinInclusion n).continuous

/-- The subgroup of `Spin(n + 1)` fixing the last coordinate vector is closed. -/
theorem isClosed_realCliffordSpinLastStabilizer (n : ℕ) :
    IsClosed (realCliffordSpinLastStabilizer n :
      Set (realCliffordSpinGroupZero (n + 1))) := by
  convert QuadraticForm.isClosed_spinVectorStabilizer (realCliffordForm (n + 1) 0)
    (Pi.single (Fin.last n) 1) using 1
  ext x
  exact mem_realCliffordSpinLastStabilizer_iff

/-- The canonical inclusion `Spin(n) → Spin(n + 1)`, restricted to the last-vector stabilizer, is
a topological embedding. -/
theorem isEmbedding_realCliffordSpinStabilizerInclusion (n : ℕ) :
    Topology.IsEmbedding (realCliffordSpinStabilizerInclusion n) := by
  convert (isEmbedding_realCliffordSpinInclusion n).codRestrict _
    (realCliffordSpinInclusion_mem_lastStabilizer n) using 1
  ext x
  exact congrArg Subtype.val (coe_realCliffordSpinStabilizerInclusion_apply n x)

/-- The canonical inclusion `Spin(n) → Spin(n + 1)` is continuous after restricting its codomain
to the last-vector stabilizer. -/
@[fun_prop]
theorem continuous_realCliffordSpinStabilizerInclusion (n : ℕ) :
    Continuous (realCliffordSpinStabilizerInclusion n) :=
  (isEmbedding_realCliffordSpinStabilizerInclusion n).continuous

end Real

end


end CliffordAlgebra

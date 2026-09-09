/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Real.Stabilizer
public import TauCeti.Topology.Algebra.CliffordAlgebra.Basic
public import TauCeti.Topology.Algebra.QuadraticForm.SpecialOrthogonal

/-!
# Topology on finite-dimensional real Spin groups

This file uses the canonical subtype topology on a finite-dimensional real Spin group. The
surrounding Clifford algebra has its real module topology from
`TauCeti.Topology.Algebra.CliffordAlgebra.Basic`. A real special orthogonal group in coordinates has
the independently induced topology from
`TauCeti.Topology.Algebra.QuadraticForm.SpecialOrthogonal`.

For a quadratic form on a finite real coordinate space, continuity of the Spin projection is proved
from the explicit Clifford conjugation formula for `spinVectorAction`. This supplies the
topological-group bridge for standard real Spin groups and, in particular, for the compact real
double cover at signature `(n, 0)`. It makes no compactness, connectedness, simple-connectivity,
fibration, or universal-cover claim.

## Continuity argument

For `x : spinGroup Q` and a fixed vector `v`, the public action equation gives

`ι Q (spinVectorAction Q x v) = x * ι Q v * star x`.

On the Spin group, `star x` is the inverse of `x`. The subtype coercion and Clifford star are
continuous, so the right-hand side is continuous in `x`. The continuous vector-part map `ιInv Q`
is a left inverse to `ι Q`; applying it proves continuity of
`x ↦ spinVectorAction Q x v`.

A map into matrices is continuous exactly when each matrix entry is continuous. The `(i, j)` entry
of the standard matrix of the Spin action is the `i`th coordinate of the action on
`Pi.single j 1`. The fixed-vector result therefore proves continuity into the independently
topologized special orthogonal group.

## Main results

* `QuadraticMap.Isometry.continuous_spinGroupMap` proves continuity of the Spin-group map induced
  by an isometry of real quadratic spaces.
* `CliffordAlgebra.instIsTopologicalGroupRealSpinGroup` equips `spinGroup Q` with a topological
  group structure for its canonical subtype topology.
* `CliffordAlgebra.continuous_spinVectorAction_apply` proves fixed-vector continuity of the Spin
  action.
* `CliffordAlgebra.continuous_spinToSpecialOrthogonal_pi` proves continuity of the Spin
  projection for every quadratic form on a finite real coordinate space.
* `CliffordAlgebra.continuous_realCliffordSpinDoubleCoverZero_rightHom` specializes this result to
  the projection field of the packaged compact real double cover.
* `CliffordAlgebra.continuous_realCliffordSpinInclusion` proves continuity of the lower-rank
  inclusion used in the compact stabilizer construction.

## References

This supplies the topological-group bridge in Layer 7 of
`TauCetiRoadmap/RepresentationTheory/SpinRepresentations/README.md`. See H. B. Lawson and
M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I §2.
-/

public section


namespace QuadraticMap.Isometry

universe u v


variable {V : Type u} {W : Type v}
  [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
  {Q : QuadraticForm ℝ V} {P : QuadraticForm ℝ W}

/-- The Spin-group map induced by an isometry of real quadratic spaces is continuous for the
canonical subtype topologies. -/
@[fun_prop]
theorem continuous_spinGroupMap (f : Q →qᵢ P) : Continuous f.spinGroupMap := by
  apply continuous_induced_rng.mpr
  refine ((CliffordAlgebra.continuous_map_realCliffordAlgebra f).comp
    continuous_subtype_val).congr ?_
  exact fun x ↦ (coe_spinGroupMap_apply f x).symm

end QuadraticMap.Isometry


namespace CliffordAlgebra

open TauCeti

noncomputable section

universe u


variable {V : Type u} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

/-- A finite-dimensional real Spin group is a topological group for its canonical subtype
topology. Multiplication is inherited from the Clifford algebra, while inversion is Clifford
star. -/
instance instIsTopologicalGroupRealSpinGroup (Q : QuadraticForm ℝ V) :
    IsTopologicalGroup (spinGroup Q) where
  continuous_mul := continuous_mul
  continuous_inv := continuous_induced_rng.mpr continuous_subtype_val.star

/-- For a fixed vector, its image under the real Spin action depends continuously on the Spin
element. -/
@[fun_prop]
theorem continuous_spinVectorAction_apply [TopologicalSpace V] [IsModuleTopology ℝ V]
    (Q : QuadraticForm ℝ V) (v : V) :
    Continuous (fun x : spinGroup Q => spinVectorAction Q x v) := by
  let _ : IsTopologicalAddGroup V := IsModuleTopology.isTopologicalAddGroup ℝ V
  have hval : Continuous (fun x : spinGroup Q => (x : CliffordAlgebra Q)) :=
    continuous_subtype_val
  have hstar : Continuous (fun x : spinGroup Q => star (x : CliffordAlgebra Q)) :=
    continuous_subtype_val.star
  have hprod : Continuous (fun x : spinGroup Q =>
      (x : CliffordAlgebra Q) * ι Q v * star (x : CliffordAlgebra Q)) :=
    (hval.mul continuous_const).mul hstar
  have hvector := (IsModuleTopology.continuous_of_linearMap (ιInv Q)).comp hprod
  convert hvector using 1
  funext x
  rw [← ιInv_ι Q (spinVectorAction Q x v), ι_spinVectorAction_apply]
  rfl

/-- The real Spin action of a quadratic form on a finite coordinate space is continuous as a map to
the special orthogonal group with its standard coordinate topology. -/
@[fun_prop]
theorem continuous_spinToSpecialOrthogonal_pi
    {n : Type u} [Fintype n] [DecidableEq n] (Q : QuadraticForm ℝ (n → ℝ)) :
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

/-- The projection field of the compact real Spin double cover is continuous. -/
@[fun_prop]
theorem continuous_realCliffordSpinDoubleCoverZero_rightHom (n : ℕ) [NeZero n] :
    Continuous (realCliffordSpinDoubleCoverZero n).rightHom := by
  rw [realCliffordSpinDoubleCoverZero_rightHom]
  exact continuous_spinToSpecialOrthogonal_pi (realCliffordForm n 0)

/-- The lower-rank inclusion `Spin(n) → Spin(n + 1)` is continuous for the canonical real
Clifford-algebra subtype topologies. -/
@[fun_prop]
theorem continuous_realCliffordSpinInclusion (n : ℕ) :
    Continuous (realCliffordSpinInclusion n) := by
  refine (QuadraticMap.Isometry.continuous_spinGroupMap
    ((realCliffordPositiveSplitIsometry n 0).symm.toIsometry.comp
      (QuadraticMap.Isometry.inl (realCliffordForm n 0)
        (QuadraticMap.sq (R := ℝ) (A := ℝ))))).congr ?_
  exact fun x ↦ by
    apply Subtype.ext
    rw [QuadraticMap.Isometry.coe_spinGroupMap_apply,
      coe_realCliffordSpinInclusion_apply]

end


end CliffordAlgebra

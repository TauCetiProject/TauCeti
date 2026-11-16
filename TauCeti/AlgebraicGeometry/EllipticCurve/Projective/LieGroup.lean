/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import TauCeti.AlgebraicGeometry.EllipticCurve.Projective.ComplexManifold
public import TauCeti.AlgebraicGeometry.EllipticCurve.Projective.TopologicalAddGroup

/-!
# Complex elliptic curves are complex Lie groups

Let `W` be an elliptic curve over `ℂ`. Its native projective points `W.Point` form a compact
Riemann surface (`WeierstrassCurve.Projective.Point.instIsManifold`) and a topological
group (`WeierstrassCurve.Projective.Point.instIsTopologicalAddGroup`). This file proves that the
group law is holomorphic, so that `W.Point` is a compact complex Lie group, directly
from the projective Weierstrass equation and without any lattice or analytic uniformization.

Near every point, the homogeneous coordinates normalized in a standard affine chart of `ℂℙ²` are
holomorphic nonsingular representatives of the points
(`Projectivization.contMDiffOn_insertNth_affineChart` and
`WeierstrassCurve.Projective.Point.exists_contMDiffAt_mk_eq`). Negation is linear on homogeneous
coordinates, and near every pair of points the sum is given on homogeneous coordinates by one of
the two polynomial addition laws `addXYZ` and `dblAddXYZ` of Bosma and Lenstra, whichever is
nonzero there. Composing these polynomials with the local holomorphic representatives gives local
holomorphic homogeneous coordinates for the negative and for the sum.

A change of variables acts on homogeneous coordinates by the invertible matrix `C.toMatrix`, so
the group isomorphism between the points of `C • W` and of `W` is a biholomorphism.

## Main results

* `WeierstrassCurve.Projective.Point.instLieAddGroup`: the points of a complex elliptic curve
  form a complex Lie group, analytic and so `C^r` for every `r`.
* `WeierstrassCurve.Projective.Point.diffeomorphVariableChange`: the change of variables `C` is a
  biholomorphism between the points of `C • W` and of `W`.

## References

* W. Bosma and H. W. Lenstra, Jr., *Complete systems of two addition laws for elliptic curves*,
  J. Number Theory 53 (1995), 229–240.
* J. H. Silverman, *The Arithmetic of Elliptic Curves*, 2nd ed., Graduate Texts in Mathematics
  106, Springer, 2009, §III.2 and §VI.1.
-/

public section

open Matrix Projectivization Topology
open scoped Manifold ContDiff

namespace WeierstrassCurve.Projective

section ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {W' : Projective 𝕜} {r : ℕ∞ω}

/-- The negation formula on homogeneous coordinates is `C^r`, for every `r`. -/
@[fun_prop]
protected theorem contDiff_neg : ContDiff 𝕜 r W'.neg := by
  refine contDiff_pi.mpr fun i ↦ ?_
  fin_cases i <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, neg_X, neg_Y, neg_Z, negY] <;> fun_prop

/-- The addition law `addXYZ` attached to the line `Z = 0` is `C^r` in both arguments, for
every `r`. -/
@[fun_prop]
theorem contDiff_addXYZ :
    ContDiff 𝕜 r fun PQ : (Fin 3 → 𝕜) × (Fin 3 → 𝕜) ↦ W'.addXYZ PQ.1 PQ.2 := by
  refine contDiff_pi.mpr fun i ↦ ?_
  fin_cases i <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, addXYZ_X, addXYZ_Y, addXYZ_Z, addX, addY,
      negAddY, addZ, negY, Matrix.cons_val] <;> fun_prop

/-- The Bosma–Lenstra addition law `dblAddXYZ` attached to the line `Y = 0` is `C^r` in both
arguments, for every `r`. -/
@[fun_prop]
theorem contDiff_dblAddXYZ :
    ContDiff 𝕜 r fun PQ : (Fin 3 → 𝕜) × (Fin 3 → 𝕜) ↦ W'.dblAddXYZ PQ.1 PQ.2 := by
  refine contDiff_pi.mpr fun i ↦ ?_
  fin_cases i <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, dblAddXYZ_X, dblAddXYZ_Y, dblAddXYZ_Z,
      dblAddX, dblAddY, dblAddZ] <;> fun_prop

end ContDiff

namespace Point

variable {W : Projective ℂ} [W.IsElliptic]

variable {r : ℕ∞ω}

/-- Negation of the points of a complex elliptic curve is holomorphic: on local holomorphic
representatives it is the linear map `W.neg`. -/
private theorem contMDiff_neg' : ContMDiff 𝓘(ℂ) 𝓘(ℂ) r fun P : W.Point ↦ -P := fun P₀ ↦ by
  obtain ⟨s, hs, h⟩ := exists_contMDiffAt_mk_eq P₀
  refine contMDiffAt_of_eventually_eq_mk
    (((Projective.contDiff_neg (W' := W)).contMDiff.contMDiffAt.comp P₀ hs).of_le le_top) ?_
  filter_upwards [h] with P ⟨hP, hPs⟩
  exact ⟨nonsingular_neg hP, (Point.ext (negMap_eq (s P)).symm).trans (congrArg _ hPs)⟩

/-- Addition of the points of a complex elliptic curve is holomorphic: near each pair of points it
is given on local holomorphic representatives by one of the two polynomial addition laws
`addXYZ` and `dblAddXYZ`. -/
private theorem contMDiff_add' :
    ContMDiff (𝓘(ℂ).prod 𝓘(ℂ)) 𝓘(ℂ) r fun PQ : W.Point × W.Point ↦ PQ.1 + PQ.2 := fun PQ₀ ↦ by
  obtain ⟨s, hs, h⟩ := exists_contMDiffAt_mk_eq PQ₀.1
  obtain ⟨t, ht, h'⟩ := exists_contMDiffAt_mk_eq PQ₀.2
  -- Holomorphic representatives of both summands near `PQ₀`.
  have hst : ContMDiffAt (𝓘(ℂ).prod 𝓘(ℂ)) 𝓘(ℂ, (Fin 3 → ℂ) × (Fin 3 → ℂ)) ω
      (fun PQ : W.Point × W.Point ↦ (s PQ.1, t PQ.2)) PQ₀ :=
    (hs.comp PQ₀ contMDiffAt_fst).prodMk_space (ht.comp PQ₀ contMDiffAt_snd)
  have hev : ∀ᶠ PQ : W.Point × W.Point in 𝓝 PQ₀,
      (∃ hP : W.Nonsingular (s PQ.1), Point.mk ((nonsingularLift_iff _).mpr hP) = PQ.1) ∧
        ∃ hQ : W.Nonsingular (t PQ.2), Point.mk ((nonsingularLift_iff _).mpr hQ) = PQ.2 :=
    (continuousAt_fst.eventually h).and (continuousAt_snd.eventually h')
  obtain ⟨⟨hP₀, -⟩, hQ₀, -⟩ := hev.self_of_nhds
  -- One of the two addition laws is nonzero at `PQ₀`, hence near `PQ₀`, and represents the sum.
  rcases addXYZ_ne_zero_or_dblAddXYZ_ne_zero hP₀ hQ₀ with hne | hne
  · have hc := (contDiff_addXYZ (W' := W)).contMDiff.contMDiffAt.comp PQ₀ hst
    refine contMDiffAt_of_eventually_eq_mk (hc.of_le le_top) ?_
    filter_upwards [hev, hc.continuousAt.eventually_ne hne] with PQ ⟨⟨hP, hPs⟩, hQ, hQt⟩ hPQ
    replace hPQ : W.addXYZ (s PQ.1) (t PQ.2) ≠ 0 := hPQ
    obtain ⟨hR, hR'⟩ := exists_mk_eq_mk_add_mk (R := W.addXYZ (s PQ.1) (t PQ.2)) hP hQ
      (add_of_addXYZ_ne_zero hPQ ▸ Setoid.refl _)
    exact ⟨hR, hR'.trans (by rw [hPs, hQt])⟩
  · have hc := (contDiff_dblAddXYZ (W' := W)).contMDiff.contMDiffAt.comp PQ₀ hst
    refine contMDiffAt_of_eventually_eq_mk (hc.of_le le_top) ?_
    filter_upwards [hev, hc.continuousAt.eventually_ne hne] with PQ ⟨⟨hP, hPs⟩, hQ, hQt⟩ hPQ
    obtain ⟨hR, hR'⟩ := exists_mk_eq_mk_add_mk hP hQ (dblAddXYZ_equiv_add hP hQ hPQ)
    exact ⟨hR, hR'.trans (by rw [hPs, hQt])⟩

/-- **The points of a complex elliptic curve form a complex Lie group.** The group law of the
compact Riemann surface `W.Point` is analytic, and so `C^r` for every `r`. -/
instance instLieAddGroup (r : ℕ∞ω) : LieAddGroup 𝓘(ℂ) r W.Point where
  contMDiff_add := contMDiff_add'
  contMDiff_neg := contMDiff_neg'

section VariableChange

variable (W : WeierstrassCurve ℂ) [W.IsElliptic] (C : VariableChange ℂ)

/-- The change of variables `C`, as a map from the points of `C • W` to those of `W`, is
holomorphic: on homogeneous coordinates it is the linear map `C.toMatrix`. -/
private theorem contMDiff_addEquivVariableChange :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) r (addEquivVariableChange W C) := fun P₀ ↦ by
  obtain ⟨s, hs, h⟩ := exists_contMDiffAt_mk_eq P₀
  refine contMDiffAt_of_eventually_eq_mk
    (((Matrix.mulVecLin C.toMatrix).toContinuousLinearMap.contDiff.contMDiff.contMDiffAt.comp
      P₀ hs).of_le le_top) ?_
  filter_upwards [h] with P ⟨hP, hPs⟩
  exact ⟨(nonsingular_variableChange W C _).mp hP,
    (addEquivVariableChange_mk C _).symm.trans (congrArg _ hPs)⟩

/-- The inverse of the change of variables `C`, as a map from the points of `W` to those of
`C • W`, is holomorphic: on homogeneous coordinates it is the linear map `C⁻¹.toMatrix`. -/
private theorem contMDiff_addEquivVariableChange_symm :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) r (addEquivVariableChange W C).symm := fun P₀ ↦ by
  obtain ⟨s, hs, h⟩ := exists_contMDiffAt_mk_eq P₀
  refine contMDiffAt_of_eventually_eq_mk
    (((Matrix.mulVecLin C⁻¹.toMatrix).toContinuousLinearMap.contDiff.contMDiff.contMDiffAt.comp
      P₀ hs).of_le le_top) ?_
  filter_upwards [h] with P ⟨hP, hPs⟩
  refine ⟨(nonsingular_variableChange W C _).mpr ?_,
    (addEquivVariableChange_symm_mk C _).symm.trans (congrArg _ hPs)⟩
  rwa [Function.comp_apply, LinearMap.coe_toContinuousLinearMap', mulVecLin_apply, mulVec_mulVec,
    VariableChange.toMatrix_mul_toMatrix_inv, one_mulVec]

/-- **A change of variables is a biholomorphism**: the group isomorphism
`Point.addEquivVariableChange` from the points of `C • W` to those of `W`, given on homogeneous
coordinates by the invertible matrix `C.toMatrix`, as a `C^r` diffeomorphism for every `r`. -/
noncomputable def diffeomorphVariableChange (r : ℕ∞ω) :
    (C • W).toProjective.Point ≃ₘ^r⟮𝓘(ℂ), 𝓘(ℂ)⟯ W.toProjective.Point where
  toEquiv := (addEquivVariableChange W C).toEquiv
  contMDiff_toFun := contMDiff_addEquivVariableChange W C
  contMDiff_invFun := contMDiff_addEquivVariableChange_symm W C

/-- The biholomorphism of a change of variables is the group isomorphism
`Point.addEquivVariableChange`. -/
@[simp]
theorem coe_diffeomorphVariableChange (r : ℕ∞ω) :
    ⇑(diffeomorphVariableChange W C r) = addEquivVariableChange W C :=
  (rfl)

/-- The inverse of the biholomorphism of a change of variables is the inverse of the group
isomorphism `Point.addEquivVariableChange`. -/
@[simp]
theorem coe_diffeomorphVariableChange_symm (r : ℕ∞ω) :
    ⇑(diffeomorphVariableChange W C r).symm = (addEquivVariableChange W C).symm :=
  (rfl)

end VariableChange

end Point

end WeierstrassCurve.Projective

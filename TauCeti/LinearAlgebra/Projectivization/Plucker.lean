/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Projectivization.Basic
public import TauCeti.LinearAlgebra.Basis.Basic
public import TauCeti.LinearAlgebra.ExteriorPower.Plucker

import TauCeti.Algebra.Module.Submodule.Map

/-!
# The Plücker point of a subspace

Let `K` be a field and `ι` a finite linearly ordered type. A subspace `U` of `K^ι` of dimension
`p` determines a point of the projective space over `K^(powersetCard ι p)`: the class of the
Plücker coordinates (the maximal minors) of any basis of `U`. A change of basis multiplies the
coordinates by its determinant, so the point does not depend on the basis. Conversely the point
determines the subspace: a vector `v` lies in the span of a linearly independent family `x`
exactly when the exterior product `v ∧ x 0 ∧ ⋯ ∧ x (p - 1)` vanishes, and that product is linear
in the exterior product of `x`. This is the Plücker embedding of the Grassmannian of
`p`-dimensional subspaces into projective space.

Heights of subspaces are heights of these points.

## Main definitions

* `Submodule.relativePluckerPoint U`: the Plücker point of a subspace `U` of `ι → K`, in the
  projective space over `powersetCard ι (finrank K U) → K`.

## Main results

* `TauCeti.mk_plucker_eq_mk_plucker_iff`: two linearly independent families of `p` vectors have
  proportional Plücker coordinates exactly when they span the same subspace.
* `Submodule.relativePluckerPoint_eq_mk`: the Plücker point of `U` is the class of the Plücker
  coordinates of any basis of `U`.
* `Submodule.finrank_relativePluckerPoint_injective`: a subspace is determined by its dimension
  and its Plücker point.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press
  (2006), §2.8.
-/

public section

open Set Set.powersetCard exteriorPower Module

namespace TauCeti

variable {ι K : Type*} [LinearOrder ι] [Finite ι] [Field K] {p : ℕ}

/-- Two linearly independent families of `p` vectors in `ι → K` have proportional Plücker
coordinates exactly when they span the same subspace. -/
theorem mk_plucker_eq_mk_plucker_iff {x y : Fin p → ι → K} (hx : LinearIndependent K x)
    (hy : LinearIndependent K y) :
    Projectivization.mk K (plucker x) ((plucker_ne_zero_iff _).2 hx) =
        Projectivization.mk K (plucker y) ((plucker_ne_zero_iff _).2 hy) ↔
      Submodule.span K (range x) = Submodule.span K (range y) := by
  rw [Projectivization.mk_eq_mk_iff]
  constructor
  · rintro ⟨a, ha⟩
    -- The exterior products are proportional, hence so are their products with any vector.
    have hι : ιMulti K p x = a • ιMulti K p y := by
      apply ((Pi.basisFun K ι).exteriorPower p).repr.injective
      ext s
      rw [← plucker_eq_repr_ιMulti, ← ha, Units.smul_def, Units.smul_def, map_smul,
        Finsupp.smul_apply, Pi.smul_apply, ← plucker_eq_repr_ιMulti]
    ext v
    rw [exteriorPower.mem_span_range_iff_ι_mul_ιMulti_eq_zero hx,
      exteriorPower.mem_span_range_iff_ι_mul_ιMulti_eq_zero hy, hι, Units.smul_def,
      Submodule.coe_smul, mul_smul_comm, smul_eq_zero_iff_right a.ne_zero]
  · intro h
    -- Write `x` in the basis `y` of the common span.
    have hxy (i : Fin p) : x i ∈ Submodule.span K (range y) := h ▸ Submodule.subset_span ⟨i, rfl⟩
    set A : Matrix (Fin p) (Fin p) K := .of fun i k ↦ (Basis.span hy).repr ⟨x i, hxy i⟩ k
    have hx' : x = fun i ↦ ∑ k, A i k • y k := by
      ext1 i
      have := congrArg Subtype.val ((Basis.span hy).sum_repr ⟨x i, hxy i⟩)
      simpa [A, Basis.coe_span_apply] using this.symm
    have hdet : plucker x = A.det • plucker y := by
      ext s
      conv_lhs => rw [hx']
      simp [plucker_sum_smul]
    have hA : A.det ≠ 0 := by
      rintro h0
      exact (plucker_ne_zero_iff _).2 hx (by simp [hdet, h0])
    exact ⟨Units.mk0 _ hA, by simp [hdet]⟩

end TauCeti

namespace Submodule

open TauCeti

variable {ι K : Type*} [LinearOrder ι] [Finite ι] [Field K] (U : Submodule K (ι → K))

/-- Bases of the same size of two subspaces have proportional Plücker coordinates exactly when
the subspaces are equal. -/
private theorem mk_plucker_basis_eq_iff {W : Submodule K (ι → K)} {n : ℕ} (b : Basis (Fin n) K U)
    (b' : Basis (Fin n) K W) :
    Projectivization.mk K (plucker fun i ↦ (b i : ι → K))
        ((plucker_ne_zero_iff _).2 b.linearIndependent_coe_basis) =
      Projectivization.mk K (plucker fun i ↦ (b' i : ι → K))
        ((plucker_ne_zero_iff _).2 b'.linearIndependent_coe_basis) ↔ U = W := by
  have span_coe_basis (X : Submodule K (ι → K)) (c : Basis (Fin n) K X) :
      span K (range fun i ↦ (c i : ι → K)) = X := by
    simpa only [LinearMap.id_apply, Submodule.map_id] using
      (Submodule.map_eq_span_basis X c LinearMap.id).symm
  rw [mk_plucker_eq_mk_plucker_iff b.linearIndependent_coe_basis
    b'.linearIndependent_coe_basis, span_coe_basis U b, span_coe_basis W b']

/-- The Plücker point of a subspace `U` of `ι → K`: the point of the projective space over
`powersetCard ι (finrank K U) → K` given by the Plücker coordinates of a basis of `U`. It does
not depend on the basis, by `relativePluckerPoint_eq_mk`. -/
noncomputable def relativePluckerPoint :
    Projectivization K (powersetCard ι (finrank K U) → K) :=
  .mk K (plucker fun i ↦ (finBasis K U i : ι → K))
    ((plucker_ne_zero_iff _).2 (finBasis K U).linearIndependent_coe_basis)

variable {U} in
/-- The Plücker point of `U` is the class of the Plücker coordinates of any basis of `U`. -/
theorem relativePluckerPoint_eq_mk (b : Basis (Fin (finrank K U)) K U) :
    relativePluckerPoint U = .mk K (plucker fun i ↦ (b i : ι → K))
      ((plucker_ne_zero_iff _).2 b.linearIndependent_coe_basis) :=
  (mk_plucker_basis_eq_iff U _ b).2 rfl

/-- A subspace is determined by its dimension together with its Plücker point: the Plücker point
is injective on the subspaces of each fixed dimension. -/
theorem finrank_relativePluckerPoint_injective :
    Function.Injective fun U : Submodule K (ι → K) ↦
      (⟨finrank K U, relativePluckerPoint U⟩ :
        Σ p : ℕ, Projectivization K (powersetCard ι p → K)) := by
  intro U W h
  obtain ⟨hp, h⟩ := Sigma.mk.inj_iff.mp h
  -- The Plücker point of `U` is heterogeneously equal to the class of the Plücker coordinates of
  -- any basis of `U` indexed by `Fin q` with `q = finrank K U`.
  have key (q : ℕ) (hq : finrank K U = q) (b : Basis (Fin q) K U) :
      HEq (relativePluckerPoint U) (Projectivization.mk K (plucker fun i ↦ (b i : ι → K))
        ((plucker_ne_zero_iff _).2 b.linearIndependent_coe_basis)) := by
    subst hq
    rw [relativePluckerPoint_eq_mk b]
  have := eq_of_heq ((key _ hp ((finBasis K U).reindex (finCongr hp))).symm.trans h)
  exact (mk_plucker_basis_eq_iff U _ _).1 this

end Submodule

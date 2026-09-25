/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Functoriality
public import TauCeti.LinearAlgebra.CliffordAlgebra.Pin.Action

/-!
# Functoriality of Lipschitz groups

A quadratic isometry induces a homomorphism of Lipschitz groups and its action on vectors is
natural with respect to that isometry.

## Main results

* `QuadraticMap.Isometry.lipschitzGroupMap` is the homomorphism induced on Lipschitz groups.
* `QuadraticMap.Isometry.lipschitzToOrthogonal_map` proves naturality of the Lipschitz action.
* `QuadraticMap.IsometryEquiv.orthogonalGroupCongr_lipschitzToOrthogonal` packages that result as
  an equality of orthogonal-group homomorphisms.
-/

public section

open QuadraticMap

namespace QuadraticMap.Isometry

universe u v w

variable {R : Type u} [CommRing R]
  {M₁ : Type v} [AddCommGroup M₁] [Module R M₁]
  {M₂ : Type w} [AddCommGroup M₂] [Module R M₂]
  {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}

/-- Mapping Clifford units along a quadratic isometry preserves the Lipschitz group. -/
theorem map_mem_lipschitzGroup (f : Q₁ →qᵢ Q₂) {x : (CliffordAlgebra Q₁)ˣ}
    (hx : x ∈ lipschitzGroup Q₁) :
    Units.map (CliffordAlgebra.map f).toMonoidHom x ∈ lipschitzGroup Q₂ := by
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
      apply Subgroup.subset_closure
      obtain ⟨m, hm⟩ := hx
      -- `lipschitzGroup` is the closure of the preimage of `Set.range (ι Q₂)`
      -- under the units coercion.  This `change` only exposes that defining
      -- representation before supplying the mapped Clifford generator.
      change ↑(Units.map (CliffordAlgebra.map f).toMonoidHom x) ∈
        Set.range (CliffordAlgebra.ι Q₂)
      refine ⟨f m, ?_⟩
      change CliffordAlgebra.ι Q₂ (f m) =
        CliffordAlgebra.map f (x : CliffordAlgebra Q₁)
      rw [← hm, CliffordAlgebra.map_apply_ι]
  | one => simp
  | mul x y _ _ hx hy => simpa using mul_mem hx hy
  | inv x _ hx => simpa using inv_mem hx

/-- The Clifford map of a quadratic isometry restricts to a homomorphism of Lipschitz groups. -/
def lipschitzGroupMap (f : Q₁ →qᵢ Q₂) : lipschitzGroup Q₁ →* lipschitzGroup Q₂ where
  toFun x :=
    ⟨Units.map (CliffordAlgebra.map f).toMonoidHom x.1, f.map_mem_lipschitzGroup x.2⟩
  map_one' := by simp
  map_mul' x y := by simp

/-- Coercing the induced Lipschitz-group map is the corresponding Clifford-algebra map. -/
@[simp]
theorem coe_lipschitzGroupMap_apply (f : Q₁ →qᵢ Q₂) (x : lipschitzGroup Q₁) :
    ((f.lipschitzGroupMap x : (CliffordAlgebra Q₂)ˣ) : CliffordAlgebra Q₂) =
      CliffordAlgebra.map f ((x : (CliffordAlgebra Q₁)ˣ) : CliffordAlgebra Q₁) := (rfl)

/-- Mapping the inverse of a Lipschitz unit agrees with taking the inverse after mapping. -/
@[simp]
theorem map_lipschitzGroup_inv_coe (f : Q₁ →qᵢ Q₂) (x : lipschitzGroup Q₁) :
    CliffordAlgebra.map f
        (((x : (CliffordAlgebra Q₁)ˣ)⁻¹ : (CliffordAlgebra Q₁)ˣ) : CliffordAlgebra Q₁) =
      (((f.lipschitzGroupMap x)⁻¹ : (CliffordAlgebra Q₂)ˣ) : CliffordAlgebra Q₂) := by
  calc
    _ = (((f.lipschitzGroupMap (x⁻¹) : lipschitzGroup Q₂) :
        (CliffordAlgebra Q₂)ˣ) : CliffordAlgebra Q₂) :=
      (f.coe_lipschitzGroupMap_apply (x⁻¹)).symm
    _ = _ := by simp

/-- The Lipschitz action commutes with the map induced by a quadratic isometry. -/
@[simp]
theorem lipschitzToOrthogonal_map [Invertible (2 : R)] (f : Q₁ →qᵢ Q₂)
    (x : lipschitzGroup Q₁) (m : M₁) :
    f (CliffordAlgebra.lipschitzVectorAction Q₁ x m) =
      CliffordAlgebra.lipschitzVectorAction Q₂ (f.lipschitzGroupMap x) (f m) := by
  apply CliffordAlgebra.ι_injective Q₂
  rw [← CliffordAlgebra.map_apply_ι (f := f)
      (CliffordAlgebra.lipschitzVectorAction Q₁ x m),
    CliffordAlgebra.ι_lipschitzVectorAction_apply,
    CliffordAlgebra.ι_lipschitzVectorAction_apply, map_mul, map_mul,
    CliffordAlgebra.map_involute]
  rw [← f.coe_lipschitzGroupMap_apply x, f.map_lipschitzGroup_inv_coe,
    CliffordAlgebra.map_apply_ι]

end QuadraticMap.Isometry

namespace QuadraticMap.IsometryEquiv

universe u v w

variable {R : Type u} [CommRing R]
  {M₁ : Type v} [AddCommGroup M₁] [Module R M₁]
  {M₂ : Type w} [AddCommGroup M₂] [Module R M₂]
  {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}

/-- The Lipschitz action is natural under a quadratic isometry equivalence. -/
@[simp]
theorem orthogonalGroupCongr_lipschitzToOrthogonal [Invertible (2 : R)]
    (e : Q₁.IsometryEquiv Q₂) (x : lipschitzGroup Q₁) :
    TauCeti.QuadraticMap.orthogonalGroupCongr e
        (CliffordAlgebra.lipschitzToOrthogonal Q₁ x) =
      CliffordAlgebra.lipschitzToOrthogonal Q₂ (e.toIsometry.lipschitzGroupMap x) := by
  ext m
  rw [TauCeti.QuadraticMap.coe_orthogonalGroupCongr_apply,
    CliffordAlgebra.coe_lipschitzToOrthogonal_apply,
    CliffordAlgebra.coe_lipschitzToOrthogonal_apply]
  -- The preceding application lemmas leave both sides as bundled linear
  -- equivalence applications.  This `change` unfolds those coercions to the
  -- underlying isometry action required by the reusable naturality theorem.
  change e.toIsometry (CliffordAlgebra.lipschitzVectorAction Q₁ x (e.symm m)) = _
  simpa only [QuadraticMap.IsometryEquiv.toIsometry_apply, e.apply_symm_apply] using
    e.toIsometry.lipschitzToOrthogonal_map x (e.symm m)

end QuadraticMap.IsometryEquiv

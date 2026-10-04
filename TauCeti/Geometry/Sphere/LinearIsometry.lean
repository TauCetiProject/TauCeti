/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Mathlib.Analysis.Normed.Group.BallSphere
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.MetricSpace.IsometricSMul

/-!
# Linear isometries of the unit sphere

A linear isometry equivalence preserves norms, so it restricts to an equivalence of unit spheres.
This file develops that restriction independently of the manifold structure on spheres.

## Main definitions

* `LinearIsometry.unitSphereMap`: the map of unit spheres obtained by restricting a linear
  isometry.
* `LinearIsometryEquiv.unitSphereEquiv`: the equivalence of unit spheres obtained by
  restricting a linear isometry equivalence.
* `LinearIsometryEquiv.unitSphereIsometryEquiv`: the isometry equivalence of unit spheres
  obtained by restricting a linear isometry equivalence.
* `LinearIsometryEquiv.instMulActionUnitSphere`: the action of the linear isometry group of `E`
  on the unit sphere of `E`, which is by isometries.

## Main results

* `LinearIsometry.isometry_unitSphereMap`, `LinearIsometry.isEmbedding_unitSphereMap`: the
  restriction of a linear isometry is an isometry, hence (for a normed source) a topological
  embedding.
* `LinearIsometryEquiv.isometry_unitSphereEquiv`: the restriction is an isometry.
* `TauCeti.LinearMap.eq_of_eqOn_unitSphere`: a real linear map is determined by its
  values on the unit sphere.

## Implementation notes

The declarations extending `LinearIsometry` and `LinearIsometryEquiv` live in the root-level
`LinearIsometry` and `LinearIsometryEquiv` namespaces, so receiver notation elaborates. The
separate linear-map lemma remains in `TauCeti.LinearMap`; it has no explicit `LinearMap` receiver
for dot notation.
-/

public section

open Metric Module

namespace LinearIsometry

section Seminormed

variable {R E F : Type*} [Semiring R]
variable [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
variable [Module R E] [Module R F]

/-- A linear isometry restricts to a map of the corresponding unit spheres. -/
def unitSphereMap (f : E →ₗᵢ[R] F) (x : sphere (0 : E) 1) : sphere (0 : F) 1 :=
  ⟨f x, f.map_zero ▸ f.isometry.mapsTo_sphere 0 1 x.2⟩

@[simp]
theorem coe_unitSphereMap_apply (f : E →ₗᵢ[R] F) (x : sphere (0 : E) 1) :
    (f.unitSphereMap x : F) = f x :=
  (rfl)

/-- The restriction of a linear isometry to the unit spheres is an isometry. -/
theorem isometry_unitSphereMap (f : E →ₗᵢ[R] F) : Isometry f.unitSphereMap :=
  Isometry.of_dist_eq fun x y => by simp [Subtype.dist_eq]

/-- The restriction of a linear isometry to the unit spheres is continuous. -/
theorem continuous_unitSphereMap (f : E →ₗᵢ[R] F) : Continuous f.unitSphereMap :=
  f.isometry_unitSphereMap.continuous

/-- The restriction of a linear isometry to the unit spheres commutes with the antipodal map. -/
@[simp]
theorem unitSphereMap_neg (f : E →ₗᵢ[R] F) (x : sphere (0 : E) 1) :
    f.unitSphereMap (-x) = -f.unitSphereMap x :=
  Subtype.ext <| by simp

end Seminormed

section Normed

variable {R E F : Type*} [Semiring R]
variable [NormedAddCommGroup E] [SeminormedAddCommGroup F]
variable [Module R E] [Module R F]

/-- The restriction of a linear isometry to the unit spheres is a topological embedding. -/
theorem isEmbedding_unitSphereMap (f : E →ₗᵢ[R] F) : Topology.IsEmbedding f.unitSphereMap :=
  f.isometry_unitSphereMap.isEmbedding

end Normed

end LinearIsometry

namespace LinearIsometryEquiv

section Seminormed

variable {R E F G : Type*} [Semiring R]
variable [SeminormedAddCommGroup E] [SeminormedAddCommGroup F] [SeminormedAddCommGroup G]
variable [Module R E] [Module R F] [Module R G]

/-- A linear isometry equivalence preserves the unit sphere: it maps unit vectors to unit vectors,
and nothing else to unit vectors. -/
theorem map_mem_unitSphere_iff (e : E ≃ₗᵢ[R] F) (x : E) :
    e x ∈ sphere (0 : F) 1 ↔ x ∈ sphere (0 : E) 1 := by
  simp

/-- A linear isometry equivalence restricts to an equivalence of the corresponding unit spheres. -/
def unitSphereEquiv (e : E ≃ₗᵢ[R] F) : sphere (0 : E) 1 ≃ sphere (0 : F) 1 :=
  e.toEquiv.subtypeEquiv fun x => (map_mem_unitSphere_iff e x).symm

@[simp]
theorem coe_unitSphereEquiv_apply (e : E ≃ₗᵢ[R] F) (x : sphere (0 : E) 1) :
    (unitSphereEquiv e x : F) = e x :=
  (rfl)

@[simp]
theorem unitSphereEquiv_symm (e : E ≃ₗᵢ[R] F) : (unitSphereEquiv e).symm = unitSphereEquiv e.symm :=
  (rfl)

@[simp]
theorem unitSphereEquiv_refl :
    unitSphereEquiv (_root_.LinearIsometryEquiv.refl R E) = Equiv.refl (sphere (0 : E) 1) :=
  (rfl)

@[simp]
theorem unitSphereEquiv_trans (e : E ≃ₗᵢ[R] F) (e' : F ≃ₗᵢ[R] G) :
    unitSphereEquiv (e.trans e') = (unitSphereEquiv e).trans (unitSphereEquiv e') :=
  (rfl)

/-- The restriction of a linear isometry equivalence to the unit sphere is an isometry for the
distance the sphere inherits from `E`: the action of `O(n + 1)` on `Sⁿ` is by isometries of the
round sphere. -/
theorem isometry_unitSphereEquiv (e : E ≃ₗᵢ[R] F) : Isometry (unitSphereEquiv e) :=
  Isometry.of_dist_eq fun x y => by simp [Subtype.dist_eq]

/-- A linear isometry equivalence restricts to an isometry equivalence of the corresponding unit
spheres. -/
def unitSphereIsometryEquiv (e : E ≃ₗᵢ[R] F) : sphere (0 : E) 1 ≃ᵢ sphere (0 : F) 1 :=
  ⟨unitSphereEquiv e, isometry_unitSphereEquiv e⟩

@[simp]
theorem coe_unitSphereIsometryEquiv_apply (e : E ≃ₗᵢ[R] F) (x : sphere (0 : E) 1) :
    (unitSphereIsometryEquiv e x : F) = e x :=
  coe_unitSphereEquiv_apply e x

@[simp]
theorem unitSphereIsometryEquiv_symm (e : E ≃ₗᵢ[R] F) :
    (unitSphereIsometryEquiv e).symm = unitSphereIsometryEquiv e.symm :=
  IsometryEquiv.ext fun _ => rfl

@[simp]
theorem unitSphereIsometryEquiv_refl :
    unitSphereIsometryEquiv (_root_.LinearIsometryEquiv.refl R E) =
      IsometryEquiv.refl (sphere (0 : E) 1) :=
  IsometryEquiv.ext fun _ => rfl

@[simp]
theorem unitSphereIsometryEquiv_trans (e : E ≃ₗᵢ[R] F) (e' : F ≃ₗᵢ[R] G) :
    unitSphereIsometryEquiv (e.trans e') =
      (unitSphereIsometryEquiv e).trans (unitSphereIsometryEquiv e') :=
  IsometryEquiv.ext fun _ => rfl

/-- A linear isometry equivalence of `E` acts on the unit sphere of `E` by restriction. -/
instance instSMulUnitSphere : SMul (E ≃ₗᵢ[R] E) (sphere (0 : E) 1) :=
  ⟨fun e => unitSphereEquiv e⟩

@[simp]
theorem coe_smul_unitSphere (e : E ≃ₗᵢ[R] E) (x : sphere (0 : E) 1) :
    ((e • x : sphere (0 : E) 1) : E) = e x :=
  coe_unitSphereEquiv_apply e x

/-- The group of linear isometry equivalences of `E` acts on the unit sphere of `E` by
restriction. -/
instance instMulActionUnitSphere : MulAction (E ≃ₗᵢ[R] E) (sphere (0 : E) 1) where
  one_smul x := Subtype.ext (by simp)
  mul_smul e e' x := Subtype.ext (by simp)

/-- The linear isometry group of `E` acts on the unit sphere by isometries. -/
instance : IsIsometricSMul (E ≃ₗᵢ[R] E) (sphere (0 : E) 1) :=
  ⟨fun e => Isometry.of_dist_eq fun x y => by simp [Subtype.dist_eq]⟩

end Seminormed

end LinearIsometryEquiv

namespace TauCeti

namespace LinearMap

section Normed

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [AddCommMonoid F] [Module ℝ F]

/-- A real linear map is determined by its values on the unit sphere, since every nonzero vector
is a positive multiple of a unit vector. -/
theorem eq_of_eqOn_unitSphere {f g : E →ₗ[ℝ] F} (h : Set.EqOn f g (sphere (0 : E) 1)) :
    f = g := by
  ext v
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  · have hnorm : ‖v‖ ≠ 0 := norm_ne_zero_iff.2 hv
    have hmem : ‖v‖⁻¹ • v ∈ sphere (0 : E) 1 := by
      simp [norm_smul, inv_mul_cancel₀ hnorm]
    have hsmul : ‖v‖⁻¹ • f v = ‖v‖⁻¹ • g v := by simpa using h hmem
    exact smul_right_injective F (inv_ne_zero hnorm) hsmul

end Normed

end LinearMap

end TauCeti

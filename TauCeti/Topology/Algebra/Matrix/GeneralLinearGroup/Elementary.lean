/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Group.Matrix
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Topology.Homotopy.Basic
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Elementary

import TauCeti.Topology.Homotopy.Homotopic.Group

/-!
# Continuity and nullhomotopy of elementary matrices with continuous entries

For a topological ring `𝕜` in which `0` and `1` are joined by a path (`Joined (0 : 𝕜) 1`) and a
ring homomorphism `f : A →+* C(X, 𝕜)`, entrywise evaluation along `f` defines a group
homomorphism `RingHom.mapGLContinuousMap f : GL n A →* C(X, GL n 𝕜)`, and over commutative
rings a group homomorphism `RingHom.mapSLContinuousMap f : SL n R →* C(X, SL n 𝕜)`.

Every elementary matrix `1 + a Eᵢⱼ` (`i ≠ j`) deforms continuously to the identity along a path
`γ : Path (0 : 𝕜) 1` via `t ↦ 1 + (γ t * f a x) Eᵢⱼ`. Because homotopies in a topological group
are closed under pointwise multiplication and inversion, every matrix in the elementary subgroup
`TauCeti.elementarySubgroup n A` maps to a nullhomotopic continuous map `X → GL n 𝕜` (and
`X → SL n 𝕜` in the commutative case). When the matrix evaluates to the identity at a basepoint
`x₀ : X`, basepoint correction in the topological group upgrades this to a homotopy relative to
`{x₀}`.

## Main definitions

* `RingHom.mapGLContinuousMap`: the group homomorphism `GL n A →* C(X, GL n 𝕜)` induced by a
  ring homomorphism `A →+* C(X, 𝕜)`.
* `RingHom.mapSLContinuousMap`: the corresponding homomorphism `SL n R →* C(X, SL n 𝕜)` over
  commutative rings.

## Main results

* `TauCeti.continuous_transvectionUnit`, `Matrix.SpecialLinearGroup.continuous_transvection`:
  transvections depend continuously on their off-diagonal entry.
* `RingHom.homotopic_one_mapGLContinuousMap_of_mem_elementarySubgroup`,
  `RingHom.homotopicRel_one_mapGLContinuousMap_of_mem_elementarySubgroup`: elementary matrices
  map to (pointed) nullhomotopic maps into `GL n 𝕜`.
* `RingHom.homotopic_one_mapSLContinuousMap_of_toGL_mem_elementarySubgroup`,
  `RingHom.homotopicRel_one_mapSLContinuousMap_of_toGL_mem_elementarySubgroup`: the same in
  `SL n 𝕜`.
-/

public section

open Matrix
open scoped unitInterval

namespace TauCeti

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n]

/-- A transvection `1 + c Eᵢⱼ` in `GL n 𝕜` varies continuously in its parameter `c`. -/
@[fun_prop]
theorem continuous_transvectionUnit [Ring 𝕜] [TopologicalSpace 𝕜]
    [ContinuousAdd 𝕜] [ContinuousNeg 𝕜] {i j : n} (hij : i ≠ j) :
    Continuous (transvectionUnit hij : 𝕜 → GL n 𝕜) := by
  rw [Units.continuous_iff]
  constructor
  · refine continuous_matrix fun p q ↦ ?_
    simp only [Function.comp_apply, coe_transvectionUnit_eq_one_add_single, Matrix.add_apply,
      Matrix.single_apply]
    by_cases h : i = p ∧ j = q
    · simp only [h, and_self, ↓reduceIte]
      exact continuous_const.add continuous_id
    · simp only [h, ↓reduceIte]
      exact continuous_const
  · refine continuous_matrix fun p q ↦ ?_
    have hinv :
        ∀ a : 𝕜, (↑(transvectionUnit hij a)⁻¹ : Matrix n n 𝕜) = 1 + single i j (-a) :=
      fun a ↦ by rw [transvectionUnit_inv, coe_transvectionUnit_eq_one_add_single]
    simp only [hinv, Matrix.add_apply, Matrix.single_apply]
    by_cases h : i = p ∧ j = q
    · simp only [h, and_self, ↓reduceIte]
      exact continuous_const.add continuous_neg
    · simp only [h, ↓reduceIte]
      exact continuous_const

end TauCeti

namespace Matrix.SpecialLinearGroup

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n]

/-- A transvection `1 + c Eᵢⱼ` in `SL n 𝕜` varies continuously in its parameter `c`. -/
@[fun_prop]
theorem continuous_transvection [CommRing 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜]
    {i j : n} (hij : i ≠ j) :
    Continuous (transvection hij : 𝕜 → SpecialLinearGroup n 𝕜) := by
  have hcont : Continuous fun a : 𝕜 ↦ (transvection hij a : Matrix n n 𝕜) := by
    refine continuous_matrix fun p q ↦ ?_
    have hentry :
        (fun a : 𝕜 ↦ (transvection hij a : Matrix n n 𝕜) p q) =
          fun a : 𝕜 ↦ (1 : Matrix n n 𝕜) p q + (if i = p ∧ j = q then a else 0) := by
      ext a
      simp [transvection_coe, Matrix.single_apply]
    rw [hentry]
    by_cases h : i = p ∧ j = q
    · simp only [h, and_self, ↓reduceIte]
      exact continuous_const.add continuous_id
    · simp only [h, ↓reduceIte]
      exact continuous_const
  exact hcont.subtype_mk fun a ↦ (transvection hij a).2

end Matrix.SpecialLinearGroup

namespace RingHom

open TauCeti

section GeneralLinear

variable {X A 𝕜 n : Type*} [TopologicalSpace X] [Ring A] [Ring 𝕜] [TopologicalSpace 𝕜]
  [IsTopologicalRing 𝕜] [Fintype n] [DecidableEq n]

/-- The group homomorphism `GL n A →* C(X, GL n 𝕜)` induced by a ring homomorphism
`f : A →+* C(X, 𝕜)`, applying `f · x` entrywise at each point `x : X`. -/
def mapGLContinuousMap (f : A →+* C(X, 𝕜)) : GL n A →* C(X, GL n 𝕜) where
  toFun g :=
    { toFun := fun x ↦
        Units.map
          ((((Pi.evalRingHom (fun _ : X ↦ 𝕜) x).comp ContinuousMap.coeFnRingHom).comp f).mapMatrix
            (m := n)).toMonoidHom g
      continuous_toFun := by
        rw [Units.continuous_iff]
        constructor
        · refine continuous_matrix fun i j ↦ ?_
          simpa using (f ((g : Matrix n n A) i j)).continuous
        · refine continuous_matrix fun i j ↦ ?_
          simpa using (f ((↑g⁻¹ : Matrix n n A) i j)).continuous }
  map_one' := by
    ext x i j
    simp
  map_mul' g₁ g₂ := by
    ext x i j
    simp [map_mul]

/-- The `(i, j)` entry of `f.mapGLContinuousMap g x` is `f (g i j) x`. -/
@[simp]
theorem coe_mapGLContinuousMap_apply (f : A →+* C(X, 𝕜)) (g : GL n A) (x : X) (i j : n) :
    ((f.mapGLContinuousMap g x : GL n 𝕜) : Matrix n n 𝕜) i j = f ((g : Matrix n n A) i j) x :=
  (rfl)

/-- Evaluating `f.mapGLContinuousMap` on a transvection evaluates its parameter along `f`. -/
@[simp]
theorem mapGLContinuousMap_transvectionUnit (f : A →+* C(X, 𝕜)) {i j : n} (hij : i ≠ j)
    (a : A) (x : X) :
    f.mapGLContinuousMap (transvectionUnit hij a) x = transvectionUnit hij (f a x) := by
  ext p q
  simp only [coe_mapGLContinuousMap_apply, coe_transvectionUnit_eq_one_add_single,
    Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, map_add, ContinuousMap.add_apply]
  split_ifs <;> simp

/-- **Elementary matrices map to nullhomotopic maps into `GL n 𝕜`.** When `0` and `1` are joined
by a path in `𝕜`, transporting the parameters of elementary generators along `h.somePath`
contracts the evaluated map of every element of `TauCeti.elementarySubgroup n A` to the constant
identity map. -/
theorem homotopic_one_mapGLContinuousMap_of_mem_elementarySubgroup
    (f : A →+* C(X, 𝕜)) (h : Joined (0 : 𝕜) 1) {g : GL n A}
    (hg : g ∈ elementarySubgroup n A) :
    ContinuousMap.Homotopic (1 : C(X, GL n 𝕜)) (f.mapGLContinuousMap g) := by
  let H : Subgroup (GL n A) :=
    { carrier := {u | ContinuousMap.Homotopic (1 : C(X, GL n 𝕜)) (f.mapGLContinuousMap u)}
      one_mem' := by
        rw [Set.mem_ofPred_eq, map_one]
      mul_mem' := fun {u v} hu hv ↦ by
        rw [Set.mem_ofPred_eq, map_mul, ← one_mul (1 : C(X, GL n 𝕜))]
        exact hu.mul hv
      inv_mem' := fun {u} hu ↦ by
        rw [Set.mem_ofPred_eq, map_inv, ← inv_one (G := C(X, GL n 𝕜))]
        exact hu.inv }
  have hle : elementarySubgroup n A ≤ H := by
    refine elementarySubgroup_le_iff.2 fun i j hij a ↦ ⟨?_⟩
    exact
      { toFun := fun p : I × X ↦ transvectionUnit hij (h.somePath p.1 * f a p.2)
        continuous_toFun :=
          (continuous_transvectionUnit hij).comp
            ((h.somePath.continuous.comp continuous_fst).mul
              ((f a).continuous.comp continuous_snd))
        map_zero_left := fun x ↦ by simp
        map_one_left := fun x ↦ by simp [mapGLContinuousMap_transvectionUnit] }
  exact hle hg

/-- **Based nullhomotopy of elementary matrices in `GL n 𝕜`.** If an elementary matrix evaluates
to the identity at `x₀ : X`, its evaluated map is homotopic to the constant identity map relative
to `{x₀}`. -/
theorem homotopicRel_one_mapGLContinuousMap_of_mem_elementarySubgroup
    (f : A →+* C(X, 𝕜)) (h : Joined (0 : 𝕜) 1) {g : GL n A}
    (hg : g ∈ elementarySubgroup n A) {x₀ : X} (hx₀ : f.mapGLContinuousMap g x₀ = 1) :
    ContinuousMap.HomotopicRel (1 : C(X, GL n 𝕜)) (f.mapGLContinuousMap g) {x₀} :=
  (f.homotopic_one_mapGLContinuousMap_of_mem_elementarySubgroup h hg).homotopicRel_singleton
    (by simp [hx₀])

end GeneralLinear

section SpecialLinear

variable {X R 𝕜 n : Type*} [TopologicalSpace X] [CommRing R] [CommRing 𝕜]
  [TopologicalSpace 𝕜] [IsTopologicalRing 𝕜] [Fintype n] [DecidableEq n]

/-- The group homomorphism `SL n R →* C(X, SL n 𝕜)` induced by a ring homomorphism
`f : R →+* C(X, 𝕜)`, applying `f · x` entrywise at each point `x : X`. -/
def mapSLContinuousMap (f : R →+* C(X, 𝕜)) :
    SpecialLinearGroup n R →* C(X, SpecialLinearGroup n 𝕜) where
  toFun g :=
    { toFun := fun x ↦
        SpecialLinearGroup.map ((ContinuousMap.evalAlgHom 𝕜 𝕜 x).toRingHom.comp f) g
      continuous_toFun := by
        have hcont : Continuous fun x : X ↦
            (SpecialLinearGroup.map ((ContinuousMap.evalAlgHom 𝕜 𝕜 x).toRingHom.comp f) g :
              Matrix n n 𝕜) :=
          continuous_matrix fun i j ↦ (f ((g : Matrix n n R) i j)).continuous
        exact hcont.subtype_mk fun x ↦
          (SpecialLinearGroup.map ((ContinuousMap.evalAlgHom 𝕜 𝕜 x).toRingHom.comp f) g).2 }
  map_one' := by
    ext x i j
    simp
  map_mul' g₁ g₂ := by
    ext x i j
    simp [map_mul]

/-- The `(i, j)` entry of `f.mapSLContinuousMap g x` is `f (g i j) x`. -/
@[simp]
theorem coe_mapSLContinuousMap_apply (f : R →+* C(X, 𝕜)) (g : SpecialLinearGroup n R)
    (x : X) (i j : n) :
    (f.mapSLContinuousMap g x : Matrix n n 𝕜) i j = f ((g : Matrix n n R) i j) x :=
  (rfl)

/-- Viewing `f.mapSLContinuousMap g x` in `GL n 𝕜` agrees with
`f.mapGLContinuousMap (toGL g) x`. -/
@[simp]
theorem toGL_mapSLContinuousMap_apply (f : R →+* C(X, 𝕜)) (g : SpecialLinearGroup n R)
    (x : X) :
    SpecialLinearGroup.toGL (f.mapSLContinuousMap g x) =
      f.mapGLContinuousMap (SpecialLinearGroup.toGL g) x := by
  ext i j
  simp

/-- Evaluating `f.mapSLContinuousMap` on a transvection evaluates its parameter along `f`. -/
@[simp]
theorem mapSLContinuousMap_transvection (f : R →+* C(X, 𝕜)) {i j : n} (hij : i ≠ j)
    (a : R) (x : X) :
    f.mapSLContinuousMap (SpecialLinearGroup.transvection hij a) x =
      SpecialLinearGroup.transvection hij (f a x) := by
  apply SpecialLinearGroup.toGL_injective
  rw [toGL_mapSLContinuousMap_apply, toGL_transvection_eq_transvectionUnit,
    toGL_transvection_eq_transvectionUnit, mapGLContinuousMap_transvectionUnit]

/-- **Elementary determinant-one matrices map to nullhomotopic maps into `SL n 𝕜`.** -/
theorem homotopic_one_mapSLContinuousMap_of_toGL_mem_elementarySubgroup
    (f : R →+* C(X, 𝕜)) (h : Joined (0 : 𝕜) 1)
    {g : SpecialLinearGroup n R}
    (hg : SpecialLinearGroup.toGL g ∈ elementarySubgroup n R) :
    ContinuousMap.Homotopic (1 : C(X, SpecialLinearGroup n 𝕜)) (f.mapSLContinuousMap g) := by
  let H : Subgroup (SpecialLinearGroup n R) :=
    { carrier := {u | ContinuousMap.Homotopic (1 : C(X, SpecialLinearGroup n 𝕜))
        (f.mapSLContinuousMap u)}
      one_mem' := by
        rw [Set.mem_ofPred_eq, map_one]
      mul_mem' := fun {u v} hu hv ↦ by
        rw [Set.mem_ofPred_eq, map_mul, ← one_mul (1 : C(X, SpecialLinearGroup n 𝕜))]
        exact hu.mul hv
      inv_mem' := fun {u} hu ↦ by
        rw [Set.mem_ofPred_eq, map_inv, ← inv_one (G := C(X, SpecialLinearGroup n 𝕜))]
        exact hu.inv }
  have hle : Subgroup.closure (Set.range (TransvectionStruct.toSpecialLinearGroup :
      TransvectionStruct n R → SpecialLinearGroup n R)) ≤ H := by
    refine (Subgroup.closure_le H).2 ?_
    rintro _ ⟨t, rfl⟩
    refine ⟨?_⟩
    exact
      { toFun := fun p : I × X ↦
          SpecialLinearGroup.transvection t.hij (h.somePath p.1 * f t.c p.2)
        continuous_toFun :=
          (SpecialLinearGroup.continuous_transvection t.hij).comp
            ((h.somePath.continuous.comp continuous_fst).mul
              ((f t.c).continuous.comp continuous_snd))
        map_zero_left := fun x ↦ by simp
        map_one_left := fun x ↦ by simp [TransvectionStruct.toSpecialLinearGroup] }
  rw [elementarySubgroup_eq_map_closure_range_toSpecialLinearGroup] at hg
  obtain ⟨u, hu, hug⟩ := hg
  have hgu : g = u := SpecialLinearGroup.toGL_injective hug.symm
  exact hgu ▸ hle hu

/-- **Based nullhomotopy of elementary determinant-one matrices in `SL n 𝕜`.** If a
determinant-one matrix is elementary and evaluates to the identity at `x₀ : X`, its evaluated map
is homotopic to the constant identity map in `SL n 𝕜` relative to `{x₀}`. -/
theorem homotopicRel_one_mapSLContinuousMap_of_toGL_mem_elementarySubgroup
    (f : R →+* C(X, 𝕜)) (h : Joined (0 : 𝕜) 1)
    {g : SpecialLinearGroup n R}
    (hg : SpecialLinearGroup.toGL g ∈ elementarySubgroup n R) {x₀ : X}
    (hx₀ : f.mapSLContinuousMap g x₀ = 1) :
    ContinuousMap.HomotopicRel
      (1 : C(X, SpecialLinearGroup n 𝕜)) (f.mapSLContinuousMap g) {x₀} :=
  (f.homotopic_one_mapSLContinuousMap_of_toGL_mem_elementarySubgroup h hg).homotopicRel_singleton
    (by simp [hx₀])

end SpecialLinear

end RingHom

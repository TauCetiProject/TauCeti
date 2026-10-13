/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Instances.AddCircle.Defs
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Path
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.Module.BigOperators

/-!
# Integer matrices acting on tori, and straight loops

A torus is a product `∀ i, AddCircle (p i)` of additive circles. An integer matrix
`A : Matrix κ ι ℤ` acts by the continuous additive map `Matrix.torusMap A p` from
`ι → AddCircle p` to `κ → AddCircle p`, sending `x` to `k ↦ ∑ i, A k i • x i`. For `p = 1` these
are Mathlib's tori `UnitAddTorus ι = ℝⁱ / ℤⁱ`, and this is the map induced by the linear map
`A : ℝⁱ → ℝᵏ`. It is functorial in the matrix.

For `n : ι → ℤ`, the straight loop `TauCeti.torusLoop p n` is the image in the torus of the
segment from `0` to `(n i • p i)ᵢ`: it winds `n i` times around the `i`-th circle. Integer
matrices act on these loops through `Matrix.mulVec` (`Matrix.torusMap_comp_torusLoop`). They are
the representatives used to compute the fundamental group and first homology of a torus
naturally in the matrix.
-/

public section

noncomputable section

open unitInterval

namespace Matrix

variable {ι κ μ : Type*} [Fintype ι] (A : Matrix κ ι ℤ) (p : ℝ)

/-- The continuous additive map of tori `(ι → AddCircle p) →ₜ+ (κ → AddCircle p)` induced by an
integer matrix `A`, sending `x` to `k ↦ ∑ i, A k i • x i`. -/
def torusMap : (ι → AddCircle p) →ₜ+ (κ → AddCircle p) where
  toFun x k := ∑ i, A k i • x i
  map_zero' := by ext k; simp
  map_add' x y := by ext k; simp [smul_add, Finset.sum_add_distrib]
  continuous_toFun := by fun_prop

@[simp]
theorem torusMap_apply (x : ι → AddCircle p) (k : κ) : A.torusMap p x k = ∑ i, A k i • x i :=
  (rfl)

/-- The identity matrix induces the identity of the torus. -/
@[simp]
theorem torusMap_one [DecidableEq ι] :
    (1 : Matrix ι ι ℤ).torusMap p = ContinuousAddMonoidHom.id _ := by
  ext x i
  simp [one_apply, ite_smul]

/-- The map of tori induced by a product of integer matrices is the composite of the maps they
induce. -/
theorem torusMap_mul [Fintype κ] (B : Matrix μ κ ℤ) :
    (B * A).torusMap p = (B.torusMap p).comp (A.torusMap p) := by
  ext x m
  simp only [torusMap_apply, ContinuousAddMonoidHom.comp_toFun, mul_apply, Finset.sum_smul,
    Finset.smul_sum, mul_smul]
  exact Finset.sum_comm

end Matrix

namespace TauCeti

variable {ι : Type*}

/-- The straight loop in the torus `∀ i, AddCircle (p i)` winding `n i` times around the `i`-th
circle: the image of the segment from `0` to `(n i • p i)ᵢ` in `ι → ℝ`. -/
def torusLoop (p : ι → ℝ) (n : ι → ℤ) : Path (0 : ∀ i, AddCircle (p i)) 0 where
  toFun t i := ((t * (n i • p i) : ℝ) : AddCircle (p i))
  continuous_toFun := by fun_prop
  source' := by ext i; simp
  target' := by ext i; simp [AddCircle.coe_period]

@[simp]
theorem torusLoop_apply (p : ι → ℝ) (n : ι → ℤ) (t : I) (i : ι) :
    torusLoop p n t i = ((t * (n i • p i) : ℝ) : AddCircle (p i)) :=
  (rfl)

end TauCeti

namespace Matrix

variable {ι κ : Type*} [Fintype ι] (A : Matrix κ ι ℤ) (p : ℝ)

/-- An integer matrix sends the straight loop of `n` to the straight loop of `A *ᵥ n`. -/
theorem torusMap_comp_torusLoop (n : ι → ℤ) :
    (A.torusMap p : C(ι → AddCircle p, κ → AddCircle p)).comp
        (TauCeti.torusLoop (fun _ ↦ p) n).toContinuousMap =
      (TauCeti.torusLoop (fun _ ↦ p) (A *ᵥ n)).toContinuousMap := by
  ext t k
  simp only [ContinuousMap.comp_apply, Path.coe_toContinuousMap, TauCeti.torusLoop_apply,
    mulVec, dotProduct]
  have h : (t * (∑ i, A k i * n i) • p : ℝ) = ∑ i, A k i • (t * (n i • p) : ℝ) := by
    simp only [Finset.sum_smul, Finset.mul_sum, mul_smul, mul_smul_comm]
  rw [h, ← QuotientAddGroup.mk'_apply, map_sum]
  simp

end Matrix

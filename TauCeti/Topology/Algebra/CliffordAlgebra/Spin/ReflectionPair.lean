/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.ReflectionPair
public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Basic
public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Real.UnitLevel
import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Basic

/-!
# Paths to normalized reflection-pair lifts

A path between two unit vectors maps to a path from the identity to their reflection-pair lift by
Clifford multiplication by the first vector. For the positive-definite real Clifford form, the
Euclidean unit sphere supplies such a path for every pair of unit vectors.

The dimension bound in the real specialization is sharp for this construction: the unit sphere is
path-connected precisely from dimension two onward. The resulting path is the input needed to
place reflection-pair lifts in the identity path component of the compact real Spin group.

## Main results

* `CliffordAlgebra.continuous_spinReflectionPair` shows that continuously varying unit vectors
  determine continuously varying reflection-pair lifts.
* `CliffordAlgebra.joined_one_spinReflectionPair_of_joined` maps a path in a unit quadric to a
  path from the identity to its reflection-pair lift.
* `CliffordAlgebra.joined_one_spinReflectionPair_realCliffordForm_zero` joins every normalized
  reflection-pair lift to the identity in the positive-definite real form of dimension at least two.
* `CliffordAlgebra.joined_of_coe_eq_prod_mul_ι_mul_prod` moves one factor of a Spin element written
  as a product of vectors along a path in its level set.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, Section 2.
-/

public section

namespace CliffordAlgebra

open Metric TauCeti

universe u v w

variable {R : Type u} [CommRing R] [TopologicalSpace R]
  {M : Type v} [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsModuleTopology R M]
  {Q : QuadraticForm R M} [ContinuousMul (CliffordAlgebra Q)]

/-- Two continuous families of unit vectors determine a continuous family of their normalized
reflection-pair lifts. -/
theorem continuous_spinReflectionPair {X : Type w} [TopologicalSpace X] (v w : X → M)
    (hv : ∀ x, Q (v x) = 1) (hw : ∀ x, Q (w x) = 1)
    (hvc : Continuous v) (hwc : Continuous w) :
    Continuous (fun x ↦ spinReflectionPair Q (v x) (w x) (hv x) (hw x)) := by
  apply continuous_induced_rng.mpr
  have hval : Continuous (fun x ↦ ι Q (v x) * ι Q (w x)) :=
    ((continuous_ι Q).comp hvc).mul ((continuous_ι Q).comp hwc)
  convert hval using 1
  funext x
  exact coe_spinReflectionPair Q (v x) (w x) (hv x) (hw x)

/-- Mapping a path between unit vectors by Clifford multiplication with the first vector joins the
identity to their normalized reflection-pair lift. -/
theorem joined_one_spinReflectionPair_of_joined (v w : M) (hv : Q v = 1) (hw : Q w = 1)
    (h : Joined (⟨v, hv⟩ : {u : M // Q u = 1}) ⟨w, hw⟩) :
    Joined (1 : spinGroup Q) (spinReflectionPair Q v w hv hw) := by
  let f : {u : M // Q u = 1} → spinGroup Q :=
    fun u => spinReflectionPair Q v u hv u.2
  have hf : Continuous f :=
    continuous_spinReflectionPair (fun _ ↦ v) Subtype.val (fun _ ↦ hv) (fun u ↦ u.2)
      continuous_const continuous_subtype_val
  simpa only [f, spinReflectionPair_self] using h.map hf

/-- **Moving one factor of a product of vectors.** Let a Spin element be a product
`P₁ * ι b * P₂` of vectors whose norms multiply to one, with `P₁` and `P₂` products of vectors.
Moving the factor `b` to `b'` along a path inside its level set `{v | Q v = Q b}` keeps the product
in the Spin group, and so joins the element to `P₁ * ι b' * P₂`. -/
theorem joined_of_coe_eq_prod_mul_ι_mul_prod {l₁ l₂ : List M} {b b' : M}
    (hl : Even (l₁.length + l₂.length + 1)) (hQ : (l₁.map Q).prod * Q b * (l₂.map Q).prod = 1)
    (h : JoinedIn {v | Q v = Q b} b b') {x y : spinGroup Q}
    (hx : (x : CliffordAlgebra Q) = (l₁.map (ι Q)).prod * ι Q b * (l₂.map (ι Q)).prod)
    (hy : (y : CliffordAlgebra Q) = (l₁.map (ι Q)).prod * ι Q b' * (l₂.map (ι Q)).prod) :
    Joined x y := by
  have hmem (v : {v : M // Q v = Q b}) :
      (l₁.map (ι Q)).prod * ι Q v * (l₂.map (ι Q)).prod ∈ spinGroup Q := by
    have h := prod_map_ι_mem_spinGroup (Q := Q) (l := l₁ ++ v.1 :: l₂)
      (by rwa [List.length_append, List.length_cons, ← Nat.add_assoc])
      (by rw [List.map_append, List.prod_append, List.map_cons, List.prod_cons, v.2, ← mul_assoc,
        hQ])
    rwa [List.map_append, List.prod_append, List.map_cons, List.prod_cons, ← mul_assoc] at h
  let f : {v : M // Q v = Q b} → spinGroup Q := fun v ↦ ⟨_, hmem v⟩
  have hf : Continuous f := continuous_induced_rng.mpr <|
    (continuous_const.mul ((continuous_ι Q).comp continuous_subtype_val)).mul continuous_const
  convert h.joined_subtype.map hf using 1
  exacts [Subtype.ext hx, Subtype.ext hy]

/-- In dimension at least two, every normalized reflection-pair lift for the positive-definite real
Clifford form is joined to the identity in the Spin group. -/
theorem joined_one_spinReflectionPair_realCliffordForm_zero {n : ℕ} (hn : 2 ≤ n)
    (v w : Fin n → ℝ) (hv : realCliffordForm n 0 v = 1)
    (hw : realCliffordForm n 0 w = 1) :
    Joined (1 : realCliffordSpinGroupZero n)
      (spinReflectionPair (realCliffordForm n 0) v w hv hw) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := by
    exact ⟨n - 2, by omega⟩
  let _ : PathConnectedSpace (realCliffordUnitLevel (k + 2)) :=
    pathConnectedSpace_realCliffordUnitLevel_add_two k
  have : Joined
      (⟨v, (mem_realCliffordUnitLevel (k + 2) v).mpr hv⟩ :
        realCliffordUnitLevel (k + 2))
      ⟨w, (mem_realCliffordUnitLevel (k + 2) w).mpr hw⟩ := PathConnectedSpace.joined _ _
  let f : realCliffordUnitLevel (k + 2) →
      {u : Fin (k + 2) → ℝ // realCliffordForm (k + 2) 0 u = 1} :=
    fun u => ⟨u.1, (mem_realCliffordUnitLevel (k + 2) _).mp u.2⟩
  have hf : Continuous f := by
    apply continuous_induced_rng.mpr
    exact continuous_subtype_val
  exact joined_one_spinReflectionPair_of_joined v w hv hw
    (by simpa only [f] using this.map hf)

end CliffordAlgebra

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Metric couplings of two extended pseudometric spaces

Two extended pseudometric spaces `X` and `Y` can be compared only after placing them in a common
space. The most economical common space is their disjoint union `X ⊕ Y`, equipped with an extended
pseudometric that restricts to the given distances on `X` and on `Y`. Such a pseudometric is
determined by its *cross distances* `f x y` between a point of `X` and a point of `Y`, and
`TauCeti.IsMetricCoupling f` says that these cross distances, together with the distances of `X` and
`Y`, satisfy the triangle inequality on `X ⊕ Y`
(`TauCeti.isMetricCoupling_iff_exists_pseudoEMetricSpace`). Sturm calls such a pseudometric on the
disjoint union a *coupling* of the two metrics, by analogy with couplings of two measures; here its
cross distances `f` are called a *metric coupling* of `X` and `Y`.

Metric couplings are the metric half of Sturm's transportation distance between metric-measure
spaces, `TauCeti.sturmEDist`, which minimises a transport cost over a metric coupling and a
coupling of the two measures. The measure-theoretic part of that theory uses three facts proved
here.

* Every pair of isometric embeddings into a common space induces a metric coupling
  (`TauCeti.IsMetricCoupling.of_isometry`); in particular the distance of `X` is a metric coupling
  of `X` with itself, and two spaces can always be glued at a point
  (`TauCeti.isMetricCoupling_edist_add_edist`).
* Metric couplings of `X` with `Y` and of `Y` with `Z` glue to a metric coupling of `X` with `Z`,
  whose cross distance is the length of the shortest path through `Y`
  (`TauCeti.IsMetricCoupling.comp`). This is the metric gluing behind the triangle inequality.
* The cross distances are `1`-Lipschitz in each variable, hence jointly continuous
  (`TauCeti.IsMetricCoupling.continuous`), so they are measurable whenever the open sets of
  `X × Y` are.

The cross distances take values in `[0, ∞]`. On ordinary pseudometric spaces this is no extra
generality where it matters: a metric coupling with one finite cross distance has only finite ones
(`TauCeti.IsMetricCoupling.ne_top`), so a metric coupling is either a finite pseudometric coupling
or identically `∞`.

## Main definitions

* `TauCeti.IsMetricCoupling f`: the cross distances `f : X → Y → ℝ≥0∞` extend the distances of `X`
  and `Y` to an extended pseudometric on `X ⊕ Y`.

## Main statements

* `TauCeti.isMetricCoupling_iff_exists_pseudoEMetricSpace`: the characterization by extended
  pseudometrics on the disjoint union.
* `TauCeti.IsMetricCoupling.swap`, `TauCeti.IsMetricCoupling.of_isometry`,
  `TauCeti.isMetricCoupling_edist` and `TauCeti.isMetricCoupling_edist_add_edist`: the basic
  constructions.
* `TauCeti.IsMetricCoupling.comp`: gluing two metric couplings along a common space.
* `TauCeti.IsMetricCoupling.continuous`: joint continuity of the cross distances.

## References

* K.-T. Sturm, *On the geometry of metric measure spaces. I*, Acta Math. 196 (2006), 65--131,
  §3.1, where a pseudometric on `X ⊔ Y` restricting to the two given metrics is called a coupling
  of them.
* D. Burago, Yu. Burago and S. Ivanov, *A Course in Metric Geometry*, GSM 33, AMS 2001, §7.3,
  where the same metrics on disjoint unions realize the Gromov–Hausdorff distance.
-/

public section

open scoped ENNReal

namespace TauCeti

variable {X Y Z : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace Y] [PseudoEMetricSpace Z]

/-- A **metric coupling** of `X` and `Y`: the cross distances `f x y` extend the distances of `X`
and `Y` to an extended pseudometric on the disjoint union `X ⊕ Y`
(`TauCeti.isMetricCoupling_iff_exists_pseudoEMetricSpace`). The four fields are the triangle
inequalities of the triangles with vertices in both spaces; the remaining ones hold in `X` and in
`Y`. -/
structure IsMetricCoupling (f : X → Y → ℝ≥0∞) : Prop where
  /-- Moving the point of `X` changes a cross distance by at most the distance moved. -/
  le_edist_add_left (x x' : X) (y : Y) : f x y ≤ edist x x' + f x' y
  /-- Moving the point of `Y` changes a cross distance by at most the distance moved. -/
  le_add_edist_right (x : X) (y y' : Y) : f x y ≤ f x y' + edist y' y
  /-- Two points of `X` are no farther apart than their cross distances to a point of `Y`. -/
  edist_left_le (x x' : X) (y : Y) : edist x x' ≤ f x y + f x' y
  /-- Two points of `Y` are no farther apart than their cross distances to a point of `X`. -/
  edist_right_le (x : X) (y y' : Y) : edist y y' ≤ f x y + f x y'

/-- **Metric couplings are pseudometrics on the disjoint union.** A function `f : X → Y → ℝ≥0∞`
is a metric coupling exactly when there is an extended pseudometric on `X ⊕ Y` restricting to the
distances of `X` and `Y` and with cross distances `f`. -/
theorem isMetricCoupling_iff_exists_pseudoEMetricSpace {f : X → Y → ℝ≥0∞} :
    IsMetricCoupling f ↔ ∃ d : PseudoEMetricSpace (X ⊕ Y),
      (∀ x x' : X, d.edist (.inl x) (.inl x') = edist x x') ∧
      (∀ y y' : Y, d.edist (.inr y) (.inr y') = edist y y') ∧
      ∀ x y, d.edist (.inl x) (.inr y) = f x y := by
  constructor
  · intro hf
    let e : X ⊕ Y → X ⊕ Y → ℝ≥0∞ :=
      Sum.elim (fun x ↦ Sum.elim (edist x) (f x)) fun y ↦ Sum.elim (fun x ↦ f x y) (edist y)
    refine ⟨{ edist := e, edist_self := ?_, edist_comm := ?_, edist_triangle := ?_ },
      fun _ _ ↦ rfl, fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩
    · rintro (x | y) <;> simp [e]
    · rintro (x | y) (x' | y') <;> simp [e, edist_comm]
    · rintro (x | y) (x' | y') (x'' | y'') <;> simp only [e, Sum.elim_inl, Sum.elim_inr]
      · exact edist_triangle x x' x''
      · exact hf.le_edist_add_left x x' y''
      · exact hf.edist_left_le x x'' y'
      · exact hf.le_add_edist_right x y'' y'
      · rw [add_comm, edist_comm]
        exact hf.le_edist_add_left x'' x' y
      · exact hf.edist_right_le x' y y''
      · rw [add_comm, edist_comm]
        exact hf.le_add_edist_right x'' y y'
      · exact edist_triangle y y' y''
  · rintro ⟨d, hX, hY, hXY⟩
    refine ⟨fun x x' y ↦ ?_, fun x y y' ↦ ?_, fun x x' y ↦ ?_, fun x y y' ↦ ?_⟩
    · rw [← hX, ← hXY, ← hXY]
      exact d.edist_triangle _ _ _
    · rw [← hY, ← hXY, ← hXY]
      exact d.edist_triangle _ _ _
    · rw [← hX, ← hXY, ← hXY, d.edist_comm (.inl x') (.inr y)]
      exact d.edist_triangle _ _ _
    · rw [← hY, ← hXY, ← hXY, d.edist_comm (.inl x) (.inr y)]
      exact d.edist_triangle _ _ _

/-- Two isometric embeddings into a common space induce the metric coupling of their cross
distances. -/
theorem IsMetricCoupling.of_isometry {T : X → Z} {S : Y → Z} (hT : Isometry T) (hS : Isometry S) :
    IsMetricCoupling fun x y ↦ edist (T x) (S y) where
  le_edist_add_left x x' y := hT x x' ▸ edist_triangle (T x) (T x') (S y)
  le_add_edist_right x y y' := hS y' y ▸ edist_triangle (T x) (S y') (S y)
  edist_left_le x x' y := hT x x' ▸ edist_comm (T x') (S y) ▸ edist_triangle (T x) (S y) (T x')
  edist_right_le x y y' := hS y y' ▸ edist_comm (T x) (S y) ▸ edist_triangle (S y) (T x) (S y')

/-- The distance of `X` is a metric coupling of `X` with itself. -/
theorem isMetricCoupling_edist : IsMetricCoupling fun x x' : X ↦ edist x x' :=
  IsMetricCoupling.of_isometry isometry_id isometry_id

/-- **Gluing at a point.** Identifying `x₀ ∈ X` with `y₀ ∈ Y` gives the metric coupling whose cross
distance is the length `edist x₀ x + edist y₀ y` of the path through the glued point. -/
theorem isMetricCoupling_edist_add_edist (x₀ : X) (y₀ : Y) :
    IsMetricCoupling fun x y ↦ edist x₀ x + edist y₀ y where
  le_edist_add_left x x' y := by
    rw [← add_assoc]
    gcongr
    rw [add_comm, edist_comm x x']
    exact edist_triangle x₀ x' x
  le_add_edist_right x y y' := by
    rw [add_assoc]
    gcongr
    exact edist_triangle y₀ y' y
  edist_left_le x x' y :=
    calc edist x x' ≤ edist x₀ x + edist x₀ x' := edist_comm x x₀ ▸ edist_triangle x x₀ x'
      _ ≤ edist x₀ x + edist y₀ y + (edist x₀ x' + edist y₀ y) := by
        gcongr <;> exact le_self_add
  edist_right_le x y y' :=
    calc edist y y' ≤ edist y₀ y + edist y₀ y' := edist_comm y y₀ ▸ edist_triangle y y₀ y'
      _ ≤ edist x₀ x + edist y₀ y + (edist x₀ x + edist y₀ y') := by
        gcongr <;> exact le_add_self

namespace IsMetricCoupling

variable {f : X → Y → ℝ≥0∞} {g : Y → Z → ℝ≥0∞}

/-- Exchanging the roles of the two spaces. -/
theorem swap (hf : IsMetricCoupling f) : IsMetricCoupling fun y x ↦ f x y where
  le_edist_add_left y y' x := by
    rw [edist_comm, add_comm]
    exact hf.le_add_edist_right x y y'
  le_add_edist_right y x x' := by
    rw [edist_comm, add_comm]
    exact hf.le_edist_add_left x x' y
  edist_left_le y y' x := hf.edist_right_le x y y'
  edist_right_le y x x' := hf.edist_left_le x x' y

/-- Moving both points changes a cross distance by at most the two distances moved. -/
theorem le_edist_add_add_edist (hf : IsMetricCoupling f) (x x' : X) (y y' : Y) :
    f x y ≤ edist x x' + f x' y' + edist y' y :=
  calc f x y ≤ edist x x' + f x' y := hf.le_edist_add_left x x' y
    _ ≤ edist x x' + (f x' y' + edist y' y) := by gcongr; exact hf.le_add_edist_right x' y y'
    _ = edist x x' + f x' y' + edist y' y := (add_assoc _ _ _).symm

/-- A metric coupling with one finite cross distance has finite cross distances throughout the
finite-distance components of the two points. In particular, on ordinary pseudometric spaces a
metric coupling is either finite everywhere or identically `∞`. -/
theorem ne_top (hf : IsMetricCoupling f) {x₀ x : X} {y₀ y : Y} (h : f x₀ y₀ ≠ ∞)
    (hx : edist x x₀ ≠ ∞) (hy : edist y₀ y ≠ ∞) : f x y ≠ ∞ :=
  ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨hx, h⟩, hy⟩)
    (hf.le_edist_add_add_edist x x₀ y y₀)

/-- The cross distances of a metric coupling are jointly continuous: by
`TauCeti.IsMetricCoupling.le_edist_add_add_edist` they are `2`-Lipschitz for the product distance,
which is the maximum of the two distances. -/
theorem continuous (hf : IsMetricCoupling f) : Continuous fun z : X × Y ↦ f z.1 z.2 := by
  refine continuous_of_le_add_edist 2 ENNReal.ofNat_ne_top fun z z' ↦ ?_
  have h₁ : edist z.1 z'.1 ≤ edist z z' := by
    rw [Prod.edist_eq]
    exact le_max_left _ _
  have h₂ : edist z'.2 z.2 ≤ edist z z' := by
    rw [edist_comm, Prod.edist_eq]
    exact le_max_right _ _
  calc f z.1 z.2 ≤ edist z.1 z'.1 + f z'.1 z'.2 + edist z'.2 z.2 :=
        hf.le_edist_add_add_edist _ _ _ _
    _ ≤ edist z z' + f z'.1 z'.2 + edist z z' := by gcongr
    _ = f z'.1 z'.2 + 2 * edist z z' := by ring

/-- **Gluing metric couplings.** Metric couplings of `X` with `Y` and of `Y` with `Z` glue along
`Y` to a metric coupling of `X` with `Z`, whose cross distance from `x` to `z` is the length of the
shortest path through a point of `Y`. -/
theorem comp (hf : IsMetricCoupling f) (hg : IsMetricCoupling g) :
    IsMetricCoupling fun x z ↦ ⨅ y, f x y + g y z where
  le_edist_add_left x x' z := by
    rw [ENNReal.add_iInf]
    refine iInf_mono fun y ↦ ?_
    rw [← add_assoc]
    gcongr
    exact hf.le_edist_add_left x x' y
  le_add_edist_right x z z' := by
    rw [ENNReal.iInf_add]
    refine iInf_mono fun y ↦ ?_
    rw [add_assoc]
    gcongr
    exact hg.le_add_edist_right y z z'
  edist_left_le x x' z := by
    rw [ENNReal.iInf_add]
    refine le_iInf fun y ↦ ?_
    rw [ENNReal.add_iInf]
    refine le_iInf fun y' ↦ ?_
    calc edist x x' ≤ f x y + f x' y := hf.edist_left_le x x' y
      _ ≤ f x y + (f x' y' + edist y' y) := by gcongr; exact hf.le_add_edist_right x' y y'
      _ ≤ f x y + (f x' y' + (g y' z + g y z)) := by gcongr; exact hg.edist_left_le y' y z
      _ = f x y + g y z + (f x' y' + g y' z) := by ring
  edist_right_le x z z' := by
    rw [ENNReal.iInf_add]
    refine le_iInf fun y ↦ ?_
    rw [ENNReal.add_iInf]
    refine le_iInf fun y' ↦ ?_
    calc edist z z' ≤ g y z + g y z' := hg.edist_right_le y z z'
      _ ≤ g y z + (edist y y' + g y' z') := by gcongr; exact hg.le_edist_add_left y y' z'
      _ ≤ g y z + ((f x y + f x y') + g y' z') := by gcongr; exact hf.edist_right_le x y y'
      _ = f x y + g y z + (f x y' + g y' z') := by ring

end IsMetricCoupling

end TauCeti

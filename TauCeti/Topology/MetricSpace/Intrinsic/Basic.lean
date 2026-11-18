/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.MetricSpace.Length
public import TauCeti.Topology.Path.Variation
public import Mathlib.Topology.EMetricSpace.Lipschitz

/-!
# The intrinsic distance

The intrinsic distance between two points of a pseudo-extended metric space `X` is the infimum of
the lengths of the continuous paths joining them,

`intrinsicEDist x y = ⨅ γ : Path x y, eVariationOn γ univ`,

with infimum `∞` when no path joins them. Applied to a subset `D` of a metric space, viewed as a
subtype, the paths are constrained to stay in `D` and are measured with the ambient distance: this
is the intrinsic distance `d_D` of `D`. Reversal and concatenation of paths give the metric laws,
and every path is at least as long as the distance between its endpoints, so the intrinsic distance
dominates the original one. It is an extended metric on an extended metric space,
`TauCeti.intrinsicEMetricSpace`, whose topology is finer than the original one.

The infimum may equivalently be taken over the curves `γ : ℝ → X` joining `x` to `y` on
`[0, 1]` in the sense of `TauCeti.IsCurveJoining`, so that a space is a length space exactly when
its distance is its intrinsic distance. After an affine change of parameter, every curve continuous
on a compact interval `[a, b]` bounds the intrinsic distance between its endpoints by its length.

## Main definitions and results

* `TauCeti.intrinsicEDist`: the infimum of the lengths of the paths joining two points.
* `Path.intrinsicEDist_le_eVariationOn`, `TauCeti.le_intrinsicEDist_iff` and
  `TauCeti.intrinsicEDist_lt_iff`: bounds through the lengths of the joining paths.
* `TauCeti.edist_le_intrinsicEDist`: the intrinsic distance dominates the original distance.
* `TauCeti.intrinsicEDist_comm` and `TauCeti.intrinsicEDist_triangle`: symmetry and the triangle
  inequality.
* `TauCeti.intrinsicEDist_eq_iInf_isCurveJoining` and
  `TauCeti.isLengthSpace_iff_edist_eq_intrinsicEDist`: comparison with the length-space
  condition.
* `TauCeti.intrinsicEDist_le_eVariationOn_Icc`: a curve continuous on `[a, b]` bounds the
  intrinsic distance between its endpoints by its length on `[a, b]`.
* `TauCeti.intrinsicEMetricSpace`: the intrinsic extended metric, and
  `TauCeti.continuous_id_intrinsicEMetricSpace`: its topology is finer than the original one.

## References

* D. Burago, Y. Burago, and S. Ivanov, *A Course in Metric Geometry*, AMS, 2001, Section 2.3
  (the induced intrinsic metric).
-/

public noncomputable section

open Set
open scoped ENNReal Topology unitInterval

namespace TauCeti

section PseudoEMetric

variable {X : Type*} [PseudoEMetricSpace X]

/-- The **intrinsic distance** between `x` and `y`: the infimum of the lengths of the continuous
paths from `x` to `y`, and `∞` if there is none. -/
def intrinsicEDist (x y : X) : ℝ≥0∞ :=
  ⨅ γ : Path x y, eVariationOn γ univ

/-- The definition of the intrinsic distance as an infimum over paths. -/
theorem intrinsicEDist_def (x y : X) :
    intrinsicEDist x y = ⨅ γ : Path x y, eVariationOn γ univ :=
  (rfl)

/-- A path bounds the intrinsic distance between its endpoints by its length. -/
theorem _root_.Path.intrinsicEDist_le_eVariationOn {x y : X} (γ : Path x y) :
    intrinsicEDist x y ≤ eVariationOn γ univ :=
  iInf_le _ γ

/-- The intrinsic distance is at least `r` exactly when every path between the two points has
length at least `r`. -/
theorem le_intrinsicEDist_iff {x y : X} {r : ℝ≥0∞} :
    r ≤ intrinsicEDist x y ↔ ∀ γ : Path x y, r ≤ eVariationOn γ univ :=
  le_iInf_iff

/-- The intrinsic distance is less than `r` exactly when some path between the two points has
length less than `r`. -/
theorem intrinsicEDist_lt_iff {x y : X} {r : ℝ≥0∞} :
    intrinsicEDist x y < r ↔ ∃ γ : Path x y, eVariationOn γ univ < r :=
  iInf_lt_iff

/-- The intrinsic distance dominates the original distance. -/
theorem edist_le_intrinsicEDist (x y : X) : edist x y ≤ intrinsicEDist x y :=
  le_iInf fun γ ↦ by
    simpa only [γ.source, γ.target] using
      eVariationOn.edist_le γ (mem_univ (0 : I)) (mem_univ (1 : I))

/-- The constant path gives zero intrinsic self-distance. -/
@[simp]
theorem intrinsicEDist_self (x : X) : intrinsicEDist x x = 0 :=
  nonpos_iff_eq_zero.1 <|
    (Path.refl x).intrinsicEDist_le_eVariationOn.trans_eq (Path.eVariationOn_refl x)

/-- Reversal of paths makes the intrinsic distance symmetric. -/
theorem intrinsicEDist_comm (x y : X) : intrinsicEDist x y = intrinsicEDist y x := by
  have hle (x y : X) : intrinsicEDist x y ≤ intrinsicEDist y x :=
    le_iInf fun γ ↦ γ.symm.intrinsicEDist_le_eVariationOn.trans_eq (Path.eVariationOn_symm γ)
  exact le_antisymm (hle x y) (hle y x)

/-- Concatenation of paths gives the triangle inequality for the intrinsic distance. -/
theorem intrinsicEDist_triangle (x y z : X) :
    intrinsicEDist x z ≤ intrinsicEDist x y + intrinsicEDist y z :=
  ENNReal.le_iInf_add_iInf fun γ δ ↦
    (γ.trans δ).intrinsicEDist_le_eVariationOn.trans_eq (Path.eVariationOn_trans γ δ)

/-- The intrinsic distance is the infimum of the lengths on `[0, 1]` of the curves `γ : ℝ → X`
joining `x` to `y` there. -/
theorem intrinsicEDist_eq_iInf_isCurveJoining (x y : X) :
    intrinsicEDist x y = ⨅ (γ : ℝ → X) (_ : IsCurveJoining γ x y), eVariationOn γ (Icc 0 1) := by
  refine le_antisymm (le_iInf₂ fun γ hγ ↦ ?_) (le_iInf fun γ ↦ ?_)
  · let p : Path x y :=
      { toFun := (Icc (0 : ℝ) 1).domRestrict γ
        continuous_toFun := hγ.continuousOn.domRestrict
        source' := hγ.source
        target' := hγ.target }
    refine p.intrinsicEDist_le_eVariationOn.trans_eq ?_
    rw [← p.eVariationOn_extend]
    exact eVariationOn.eq_of_eqOn fun t ht ↦ p.extend_apply ht
  · exact iInf₂_le_of_le γ.extend (isCurveJoining_extend γ) γ.eVariationOn_extend.le

/-- A curve continuous on `[a, b]` bounds the intrinsic distance between its endpoints by its length
on `[a, b]`. -/
theorem intrinsicEDist_le_eVariationOn_Icc {γ : ℝ → X} {a b : ℝ} (hab : a ≤ b)
    (hγ : ContinuousOn γ (Icc a b)) :
    intrinsicEDist (γ a) (γ b) ≤ eVariationOn γ (Icc a b) := by
  obtain ⟨δ, hδ, hvar⟩ := exists_isCurveJoining_of_continuousOn hab hγ rfl rfl
  rw [intrinsicEDist_eq_iInf_isCurveJoining, ← hvar]
  exact iInf₂_le δ hδ

/-- A space is a length space exactly when its distance is its intrinsic distance. -/
theorem isLengthSpace_iff_edist_eq_intrinsicEDist :
    IsLengthSpace X ↔ ∀ x y : X, edist x y = intrinsicEDist x y := by
  simp only [intrinsicEDist_eq_iInf_isCurveJoining]
  exact ⟨fun h ↦ h.edist_eq_iInf, fun h ↦ ⟨h⟩⟩

end PseudoEMetric

section EMetric

variable {X : Type*} [EMetricSpace X]

/-- The **intrinsic extended metric** on `X`, whose distance is `TauCeti.intrinsicEDist` and whose
uniformity is the one it defines. Its topology is finer than the original topology of `X`
(`TauCeti.continuous_id_intrinsicEMetricSpace`) and may be strictly finer. -/
@[instance_reducible]
def intrinsicEMetricSpace : EMetricSpace X where
  edist := intrinsicEDist
  edist_self := intrinsicEDist_self
  edist_comm := intrinsicEDist_comm
  edist_triangle := intrinsicEDist_triangle
  eq_of_edist_eq_zero h := edist_eq_zero.1 <| nonpos_iff_eq_zero.1 <|
    (edist_le_intrinsicEDist _ _).trans_eq h

/-- The distance of the intrinsic extended metric is the intrinsic distance. -/
@[simp]
theorem intrinsicEMetricSpace_edist (x y : X) :
    (intrinsicEMetricSpace (X := X)).edist x y = intrinsicEDist x y :=
  (rfl)

/-- The identity from `X` with its intrinsic extended metric to `X` with its original extended
metric is `1`-Lipschitz. -/
theorem lipschitzWith_one_id_intrinsicEMetricSpace :
    @LipschitzWith X X intrinsicEMetricSpace.toPseudoEMetricSpace _ 1 id := fun x y ↦ by
  simpa only [intrinsicEMetricSpace_edist, id, ENNReal.coe_one, one_mul] using
    edist_le_intrinsicEDist x y

/-- The topology of the intrinsic extended metric is finer than the original topology. -/
theorem continuous_id_intrinsicEMetricSpace :
    Continuous[intrinsicEMetricSpace.toUniformSpace.toTopologicalSpace, inferInstance]
      (id : X → X) :=
  @LipschitzWith.continuous X X intrinsicEMetricSpace.toPseudoEMetricSpace _ 1 id
    lipschitzWith_one_id_intrinsicEMetricSpace

end EMetric

end TauCeti

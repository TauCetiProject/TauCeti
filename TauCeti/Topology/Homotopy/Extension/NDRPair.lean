/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Algebra
public import TauCeti.Topology.ContinuousMap.ApplyProdMk
public import TauCeti.Topology.Homotopy.Extension.Basic

/-!
# NDR pairs

An *NDR pair* (neighbourhood deformation retract pair) `(X, A)` consists of a subset `A ⊆ X`
presented by explicit data: a control function `u : X → I` whose zero set is exactly `A`, and a
deformation `H : I × X → X` starting at the identity, fixing `A` pointwise, and carrying every
point with `u x < 1` into `A` at time `1`.

For an NDR pair, the bottom-and-sides subspace `J = {0} × X ∪ I × A` of the cylinder `I × X`
(`TauCeti.cylinderExtensionDomain A`) is again the zero set of an explicit control function,
`(t, x) ↦ t * u x`, and is a strong deformation retract of the cylinder by the explicit deformation
`(s, t, x) ↦ (t - s * min t (u x), H (s * min 1 (t / u x), x))`. At time `1` every point of the
cylinder lands in `J`, including the corner case `u x = t = 1`. Consequently `A` has the homotopy
extension property, and the pair `(I × X, J)` satisfies the hypotheses of the fixed-data relative
lifting theorem for Hurewicz fibrations
(`TauCeti.IsHurewiczFibration.zeroSetSDR_liftingInclusion`).

Continuity of the deformation along the zero set, where the formula divides by zero, rests on
the compactness argument `ContinuousMap.continuous_apply_prodMk_of_fixed`.

## Main declarations

* `TauCeti.NDRPair A`: NDR data for `A ⊆ X`.
* `TauCeti.NDRPair.cylinderControl`: the control function `(t, x) ↦ t * u x` of `J`.
* `TauCeti.NDRPair.cylinderDeformation`: the deformation of the cylinder onto `J`, with
  `TauCeti.NDRPair.cylinderDeformation_one_mem`.
* `TauCeti.NDRPair.cylinderRetraction`, `TauCeti.NDRPair.cylinderHomotopyRel`: the resulting
  strong deformation retraction of the cylinder onto `J`.
* `TauCeti.NDRPair.hasHomotopyExtensionProperty`: the subset of an NDR pair has the homotopy
  extension property.

## References

* N. E. Steenrod, *A convenient category of topological spaces*, Michigan Math. J. 14 (1967),
  133–152.
* J. P. May, *A Concise Course in Algebraic Topology*, Chapter 6.
* A. Strøm, *Note on cofibrations II*, Math. Scand. 22 (1968), 130–142.
-/

public section

open Set unitInterval

universe u

namespace TauCeti

variable {X : Type u} [TopologicalSpace X] {A : Set X}

/-- NDR data for a subset `A ⊆ X`: a control function `u : X → I` vanishing exactly on `A`, and
a deformation `H : I × X → X` of the identity which fixes `A` pointwise and carries every point
with `u x < 1` into `A` at time `1`. -/
structure NDRPair (A : Set X) where
  /-- The control function, vanishing exactly on `A`. -/
  control : C(X, I)
  control_eq_zero_iff (x : X) : control x = 0 ↔ x ∈ A
  /-- The deformation of `X`, starting at the identity and fixing `A`. -/
  deformation : C(I × X, X)
  deformation_zero (x : X) : deformation (0, x) = x
  deformation_of_mem (t : I) {x : X} (hx : x ∈ A) : deformation (t, x) = x
  deformation_one_mem {x : X} (hx : control x < 1) : deformation (1, x) ∈ A

attribute [simp] NDRPair.deformation_zero

namespace NDRPair

/-- The subset of an NDR pair is closed, being the zero set of its control function. -/
protected theorem isClosed (N : NDRPair A) : IsClosed A := by
  convert (isClosed_singleton (x := (0 : I))).preimage N.control.continuous
  ext x
  exact (N.control_eq_zero_iff x).symm

variable (N : NDRPair A)

/-- The control function `(t, x) ↦ t * u x` of the bottom-and-sides subspace
`{0} × X ∪ I × A` of the cylinder. -/
def cylinderControl : C(I × X, I) :=
  ⟨fun z ↦ z.1 * N.control z.2, by fun_prop⟩

@[simp]
theorem cylinderControl_apply (z : I × X) : N.cylinderControl z = z.1 * N.control z.2 := (rfl)

/-- The control function of the cylinder vanishes exactly on `{0} × X ∪ I × A`. -/
theorem cylinderControl_eq_zero_iff (z : I × X) :
    N.cylinderControl z = 0 ↔ z ∈ cylinderExtensionDomain A := by
  rw [cylinderControl_apply, mem_cylinderExtensionDomain_iff, ← N.control_eq_zero_iff]
  exact mul_eq_zero

/-- The time `min 1 (t / u x)` at which the cylinder deformation reads off `H`, scaled by `s`. -/
private noncomputable def cylinderTime (w : I × I × X) : I :=
  w.1 * projIcc 0 1 zero_le_one ((w.2.1 : ℝ) / N.control w.2.2)

private theorem continuousAt_cylinderTime {w : I × I × X} (hw : w.2.2 ∉ A) :
    ContinuousAt N.cylinderTime w :=
  continuous_fst.continuousAt.mul (continuousAt_projIcc_div_of_notMem N.control
    N.control_eq_zero_iff (by fun_prop) (by fun_prop) hw)

private theorem cylinderHeight_mem (w : I × I × X) :
    (w.2.1 : ℝ) - w.1 * min (w.2.1 : ℝ) (N.control w.2.2) ∈ I := by
  have h₁ : (w.1 : ℝ) * min (w.2.1 : ℝ) (N.control w.2.2) ≤ min (w.2.1 : ℝ) (N.control w.2.2) :=
    mul_le_of_le_one_left (le_min w.2.1.2.1 (N.control w.2.2).2.1) w.1.2.2
  have h₂ : 0 ≤ (w.1 : ℝ) * min (w.2.1 : ℝ) (N.control w.2.2) :=
    mul_nonneg w.1.2.1 (le_min w.2.1.2.1 (N.control w.2.2).2.1)
  constructor <;> linarith [min_le_left (w.2.1 : ℝ) (N.control w.2.2), w.2.1.2.2]

/-- The deformation of the cylinder `I × X` onto `{0} × X ∪ I × A`: at time `s` it sends
`(t, x)` to `(t - s * min t (u x), H (s * min 1 (t / u x), x))`. For `t > 0` the height is
`t * (1 - s * min 1 (u x / t))`. -/
noncomputable def cylinderDeformation : C(I × (I × X), I × X) where
  toFun w := (⟨_, N.cylinderHeight_mem w⟩, N.deformation (N.cylinderTime w, w.2.2))
  continuous_toFun :=
    (Continuous.subtype_mk (by fun_prop) _).prodMk
      (N.deformation.continuous_apply_prodMk_of_fixed (fun t _ hx ↦ N.deformation_of_mem t hx)
        (by fun_prop) fun _ hw ↦ N.continuousAt_cylinderTime hw)

@[simp]
theorem coe_cylinderDeformation_fst (s t : I) (x : X) :
    ((N.cylinderDeformation (s, t, x)).1 : ℝ) = t - s * min (t : ℝ) (N.control x) :=
  (rfl)

@[simp]
theorem cylinderDeformation_snd (s t : I) (x : X) :
    (N.cylinderDeformation (s, t, x)).2 =
      N.deformation (s * projIcc 0 1 zero_le_one ((t : ℝ) / N.control x), x) :=
  (rfl)

/-- At time `0` the cylinder deformation is the identity. -/
@[simp]
theorem cylinderDeformation_zero (z : I × X) : N.cylinderDeformation (0, z) = z := by
  obtain ⟨t, x⟩ := z
  refine Prod.ext (Subtype.ext ?_) ?_
  · simp
  · simp

/-- The cylinder deformation fixes `{0} × X ∪ I × A` pointwise. -/
theorem cylinderDeformation_of_mem (s : I) {z : I × X} (hz : z ∈ cylinderExtensionDomain A) :
    N.cylinderDeformation (s, z) = z := by
  obtain ⟨t, x⟩ := z
  rcases mem_cylinderExtensionDomain_iff.1 hz with ht | hx
  · obtain rfl : t = 0 := ht
    refine Prod.ext (Subtype.ext ?_) ?_
    · simp [min_eq_left (N.control x).2.1]
    · simp
  · have hu : (N.control x : ℝ) = 0 := by rw [(N.control_eq_zero_iff x).2 hx, Icc.coe_zero]
    refine Prod.ext (Subtype.ext ?_) ?_
    · simp [hu, min_eq_right t.2.1]
    · rw [cylinderDeformation_snd, N.deformation_of_mem _ hx]

/-- At time `1` the cylinder deformation lands in `{0} × X ∪ I × A`. Where `t ≤ u x` it reaches
the bottom of the cylinder; otherwise `u x < t ≤ 1`, so `H (1, x)` lies in `A`. This includes
the corner case `u x = t = 1`, which reaches the bottom. -/
theorem cylinderDeformation_one_mem (z : I × X) :
    N.cylinderDeformation (1, z) ∈ cylinderExtensionDomain A := by
  obtain ⟨t, x⟩ := z
  rw [mem_cylinderExtensionDomain_iff]
  rcases le_or_gt (t : ℝ) (N.control x) with htu | hut
  · left
    ext
    simp [min_eq_left htu]
  · right
    rw [cylinderDeformation_snd]
    by_cases hx : x ∈ A
    · rw [N.deformation_of_mem _ hx]
      exact hx
    · have hpos : 0 < (N.control x : ℝ) :=
        (N.control x).2.1.lt_of_ne ((coe_ne_zero_iff_notMem N.control_eq_zero_iff x).2 hx).symm
      have hproj : projIcc 0 1 zero_le_one ((t : ℝ) / N.control x) = 1 :=
        projIcc_eq_one.2 ((one_le_div hpos).2 hut.le)
      rw [hproj, one_mul]
      exact N.deformation_one_mem (Subtype.coe_lt_coe.1 (hut.trans_le t.2.2))

/-- The retraction of the cylinder `I × X` onto `{0} × X ∪ I × A`, the end of the cylinder
deformation. -/
noncomputable def cylinderRetraction : C(I × X, cylinderExtensionDomain A) :=
  ⟨fun z ↦ ⟨N.cylinderDeformation (1, z), N.cylinderDeformation_one_mem z⟩, by fun_prop⟩

@[simp]
theorem coe_cylinderRetraction_apply (z : I × X) :
    (N.cylinderRetraction z : I × X) = N.cylinderDeformation (1, z) := (rfl)

/-- The cylinder retraction fixes the points of `{0} × X ∪ I × A`. -/
@[simp]
theorem cylinderRetraction_apply_coe (z : cylinderExtensionDomain A) :
    N.cylinderRetraction z = z :=
  Subtype.ext (N.cylinderDeformation_of_mem 1 z.2)

/-- The cylinder deformation is a strong deformation retraction of `I × X` onto
`{0} × X ∪ I × A`: a homotopy relative to that subspace from the identity to the retraction. -/
noncomputable def cylinderHomotopyRel :
    (ContinuousMap.id (I × X)).HomotopyRel
      ((ContinuousMap.subtypeVal _).comp N.cylinderRetraction) (cylinderExtensionDomain A) where
  toContinuousMap := N.cylinderDeformation
  map_zero_left := N.cylinderDeformation_zero
  map_one_left _ := rfl
  prop' s z hz := by
    simp only [ContinuousMap.coe_mk, ContinuousMap.id_apply]
    exact N.cylinderDeformation_of_mem s hz

@[simp]
theorem cylinderHomotopyRel_apply (w : I × (I × X)) :
    N.cylinderHomotopyRel w = N.cylinderDeformation w := (rfl)

/-- The subset of an NDR pair has the homotopy extension property: the cylinder retracts onto
`{0} × X ∪ I × A`. -/
protected theorem hasHomotopyExtensionProperty (N : NDRPair A) :
    HasHomotopyExtensionProperty A :=
  hasHomotopyExtensionProperty_of_retraction (r := (ContinuousMap.subtypeVal _).comp
      N.cylinderRetraction) N.isClosed (fun z ↦ (N.cylinderRetraction z).2)
    fun z hz ↦ congrArg Subtype.val (N.cylinderRetraction_apply_coe ⟨z, hz⟩)

end NDRPair

end TauCeti

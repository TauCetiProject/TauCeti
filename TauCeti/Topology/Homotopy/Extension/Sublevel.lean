/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.Extension.NDRPair
public import TauCeti.Topology.Order.Sublevel

/-!
# Sublevels with a collar are closed cofibrations

Let `f : X → ℝ` be continuous and let `φ t` be a continuous motion of `X`, with `φ 0` the
identity, which lowers `f` at unit speed through the band `a ≤ f ≤ b`, where `a < b`: if
`f x ≤ b` and `f x - t ≥ a` with `t ≥ 0`, then `f (φ t x) = f x - t`. The band then serves as a
collar of the sublevel `{f ≤ a}`, and the sublevel is a closed cofibration.

Explicit NDR data for `{f ≤ a}` (`TauCeti.sublevelNDRPair`) push points of the band down along
`φ`. A point of value `v` moves for the time `max 0 (min (v - a) (b - v))`: the whole way down to
the level `a` from values `v ≤ (a + b) / 2`, and less and less above, so that no point of value
outside `(a, b)` moves. The control function `max 0 (min 1 (2 (f - a) / (b - a)))` vanishes
exactly on `{f ≤ a}` and is less than `1` exactly where `f < (a + b) / 2`. Hence `{f ≤ a}` has the
homotopy extension property in `X`
(`TauCeti.hasHomotopyExtensionProperty_sublevel_of_apply_eq_sub`).

The deformation never raises `f`, so it keeps every sublevel `{f ≤ c}` invariant, and the NDR
data restrict to every larger sublevel (`TauCeti.NDRPair.restrict`): the inclusion of `{f ≤ a}`
into `{f ≤ c}`, for `a ≤ c`, is a closed cofibration
(`TauCeti.hasHomotopyExtensionProperty_range_sublevelInclusion_of_apply_eq_sub`). This is the form
in which the sublevels of an exhaustion are the stages of a tower of closed cofibrations.

On a manifold the motion is the flow of a vector field `X` with `df(X) = -1` near a compact band
without critical points, so that sublevels at regular values with a compact band above them are
closed cofibrations.

## Main declarations

* `TauCeti.sublevelNDRPair`: NDR data for a sublevel with a collar.
* `TauCeti.hasHomotopyExtensionProperty_sublevel_of_apply_eq_sub`: the sublevel `{f ≤ a}` has the
  homotopy extension property in `X`.
* `TauCeti.hasHomotopyExtensionProperty_range_sublevelInclusion_of_apply_eq_sub`: the inclusion of
  `{f ≤ a}` into a larger sublevel is a closed cofibration.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Theorem 3.1, for the descending motion through a band without critical values.
* N. E. Steenrod, *A convenient category of topological spaces*, Michigan Math. J. 14 (1967),
  133–152, Section 6, for NDR pairs.
-/

public section

open Set unitInterval

namespace TauCeti

variable {X : Type*} [TopologicalSpace X] {f : X → ℝ} {a b : ℝ}

section CollarTime

variable {v : ℝ}

/-- The time `max 0 (min (v - a) (b - v))` for which the collar deformation moves a point of
value `v` vanishes at and below `a`. -/
private theorem collarTime_of_le_left (hv : v ≤ a) : max 0 (min (v - a) (b - v)) = 0 :=
  max_eq_left (min_le_of_left_le (by linarith))

/-- The collar time vanishes at and above `b`. -/
private theorem collarTime_of_right_le (hv : b ≤ v) : max 0 (min (v - a) (b - v)) = 0 :=
  max_eq_left (min_le_of_right_le (by linarith))

/-- Below the midpoint of the band, the collar time is the whole way down to the level `a`. -/
private theorem collarTime_of_le_midpoint (hav : a ≤ v) (hv : 2 * (v - a) ≤ b - a) :
    max 0 (min (v - a) (b - v)) = v - a := by
  rw [min_eq_left (by linarith), max_eq_right (by linarith)]

/-- A positive collar time is at most `v - a`, and `v ≤ b` there. -/
private theorem le_sub_of_collarTime_pos (h : 0 < max 0 (min (v - a) (b - v))) :
    max 0 (min (v - a) (b - v)) ≤ v - a ∧ v ≤ b := by
  rcases le_total b v with hv | hv
  · exact absurd (collarTime_of_right_le (a := a) hv) h.ne'
  rcases le_total v a with hva | hva
  · exact absurd (collarTime_of_le_left (b := b) hva) h.ne'
  exact ⟨max_le (by linarith) (min_le_left _ _), hv⟩

end CollarTime

variable (hf : Continuous f) (hab : a < b) (φ : ℝ → X → X) (hφ : Continuous (Function.uncurry φ))
  (hφ0 : ∀ x, φ 0 x = x)
  (hφf : ∀ x t, 0 ≤ t → a ≤ f x - t → f x ≤ b → f (φ t x) = f x - t)

include hf hab hφ hφ0 hφf

/-- **NDR data for a sublevel with a collar.** Let `φ t` be a continuous motion of `X`, with
`φ 0` the identity, which lowers the continuous function `f` at unit speed through the band
`a ≤ f ≤ b`, where `a < b`. Then `{f ≤ a}` has NDR data with control function
`max 0 (min 1 (2 (f - a) / (b - a)))` and deformation `(t, x) ↦ φ (t τ(f x)) x`, where
`τ(v) = max 0 (min (v - a) (b - v))`. -/
noncomputable def sublevelNDRPair : NDRPair {x | f x ≤ a} where
  control := ⟨fun x ↦ projIcc 0 1 zero_le_one (2 * (f x - a) / (b - a)), by fun_prop⟩
  control_eq_zero_iff x := by
    have hba := sub_pos.2 hab
    rw [ContinuousMap.coe_mk, ← Subtype.coe_inj, coe_projIcc, Icc.coe_zero, mem_ofPred_eq]
    constructor
    · intro h
      rcases min_le_iff.1 (h ▸ le_max_right 0 _ : min 1 (2 * (f x - a) / (b - a)) ≤ 0)
        with h1 | h1
      · linarith
      · have := (div_le_iff₀ hba).1 h1
        linarith
    · intro h
      exact max_eq_left (min_le_of_right_le (div_nonpos_of_nonpos_of_nonneg (by linarith) hba.le))
  deformation := ⟨fun p ↦ φ (p.1 * max 0 (min (f p.2 - a) (b - f p.2))) p.2,
    (hφ.comp (by fun_prop : Continuous fun p : I × X ↦
      ((p.1 : ℝ) * max 0 (min (f p.2 - a) (b - f p.2)), p.2))).congr fun _ ↦ rfl⟩
  deformation_zero x := by simp [hφ0]
  deformation_of_mem t x hx := by simp [collarTime_of_le_left (b := b) hx, hφ0]
  deformation_one_mem {x} hx := by
    have hba := sub_pos.2 hab
    rw [← Subtype.coe_lt_coe, ContinuousMap.coe_mk, Icc.coe_one, coe_projIcc, max_lt_iff,
      min_lt_iff, div_lt_one hba] at hx
    have hmid : 2 * (f x - a) < b - a := hx.2.resolve_left (lt_irrefl 1)
    rcases le_or_gt (f x) a with hxa | hxa
    · simp [hφ0, hxa]
    rw [ContinuousMap.coe_mk, Icc.coe_one, one_mul, mem_ofPred_eq,
      collarTime_of_le_midpoint hxa.le hmid.le, hφf x _ (by linarith) (by linarith) (by linarith)]
    linarith

/-- The control function of `TauCeti.sublevelNDRPair` is `max 0 (min 1 (2 (f - a) / (b - a)))`. -/
@[simp]
theorem coe_sublevelNDRPair_control (x : X) :
    ((sublevelNDRPair hf hab φ hφ hφ0 hφf).control x : ℝ) =
      max 0 (min 1 (2 * (f x - a) / (b - a))) :=
  coe_projIcc 0 1 zero_le_one _

/-- The deformation of `TauCeti.sublevelNDRPair` moves a point `x` along `φ` for the time
`t * max 0 (min (f x - a) (b - f x))`. -/
@[simp]
theorem sublevelNDRPair_deformation (t : I) (x : X) :
    (sublevelNDRPair hf hab φ hφ hφ0 hφf).deformation (t, x) =
      φ (t * max 0 (min (f x - a) (b - f x))) x :=
  (rfl)

/-- The deformation of `TauCeti.sublevelNDRPair` fixes every point with `b ≤ f x`. -/
theorem sublevelNDRPair_deformation_of_le (t : I) {x : X} (hx : b ≤ f x) :
    (sublevelNDRPair hf hab φ hφ hφ0 hφf).deformation (t, x) = x := by
  rw [sublevelNDRPair_deformation, collarTime_of_right_le hx, mul_zero, hφ0]

/-- The deformation of `TauCeti.sublevelNDRPair` never raises `f`. -/
theorem apply_sublevelNDRPair_deformation_le (t : I) (x : X) :
    f ((sublevelNDRPair hf hab φ hφ hφ0 hφf).deformation (t, x)) ≤ f x := by
  rw [sublevelNDRPair_deformation]
  rcases (le_max_left 0 (min (f x - a) (b - f x))).eq_or_lt with h | h
  · rw [← h, mul_zero, hφ0]
  obtain ⟨hle, hb⟩ := le_sub_of_collarTime_pos h
  have hs : (t : ℝ) * max 0 (min (f x - a) (b - f x)) ≤ max 0 (min (f x - a) (b - f x)) :=
    mul_le_of_le_one_left h.le t.2.2
  rw [hφf x _ (mul_nonneg t.2.1 h.le) (by linarith) hb]
  linarith [mul_nonneg t.2.1 h.le]

/-- **A sublevel with a collar is a closed cofibration.** If a continuous motion `φ` of `X`, with
`φ 0` the identity, lowers the continuous function `f` at unit speed through the band
`a ≤ f ≤ b`, where `a < b`, then `{f ≤ a}` has the homotopy extension property in `X`. -/
theorem hasHomotopyExtensionProperty_sublevel_of_apply_eq_sub :
    HasHomotopyExtensionProperty {x | f x ≤ a} :=
  (sublevelNDRPair hf hab φ hφ hφ0 hφf).hasHomotopyExtensionProperty

/-- **The inclusion of a sublevel with a collar into a larger sublevel is a closed cofibration.**
If a continuous motion `φ` of `X`, with `φ 0` the identity, lowers the continuous function `f` at
unit speed through the band `a ≤ f ≤ b`, where `a < b`, then for every `c ≥ a` the image of
`{f ≤ a}` in `{f ≤ c}` has the homotopy extension property. -/
theorem hasHomotopyExtensionProperty_range_sublevelInclusion_of_apply_eq_sub {c : ℝ}
    (hac : a ≤ c) : HasHomotopyExtensionProperty (range (sublevelInclusion f a c hac)) := by
  have hrange : range (sublevelInclusion f a c hac) =
      ((↑) ⁻¹' {x | f x ≤ a} : Set {x | f x ≤ c}) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      rw [mem_preimage, coe_sublevelInclusion_apply]
      exact x.2
    · exact fun hy ↦ ⟨⟨y, hy⟩, Subtype.ext (coe_sublevelInclusion_apply f hac _)⟩
  rw [hrange]
  exact ((sublevelNDRPair hf hab φ hφ hφ0 hφf).restrict fun t y hy ↦
    (apply_sublevelNDRPair_deformation_le hf hab φ hφ hφ0 hφf t y).trans
      hy).hasHomotopyExtensionProperty

end TauCeti

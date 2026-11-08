/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Deformation
public import TauCeti.Topology.Homotopy.Extension.Sublevel
import TauCeti.Geometry.Manifold.Morse.CriticalPoints

/-!
# Sublevels at regular values are closed cofibrations

Let `f` be a smooth real function on a boundaryless finite-dimensional manifold `M`, and write
`M_a = {f ≤ a}`. If the band `f⁻¹[a, b]` above `a`, with `a < b`, is compact and contains no
critical point of `f`, it is a collar of `M_a`: the flow of a vector field `X` with `df(X) = -1`
near the band (`TauCeti.exists_flow_apply_eq_sub`) pushes the lower half of the band down onto the
level `f⁻¹(a)`. This gives explicit NDR data for `M_a` (`TauCeti.sublevelNDRPair`), so `M_a` has
the homotopy extension property in `M` (`TauCeti.hasHomotopyExtensionProperty_sublevel`). The
deformation never raises `f`, so the same holds inside every larger sublevel `M_c`: the inclusion
`M_a → M_c` is a closed cofibration
(`TauCeti.hasHomotopyExtensionProperty_range_sublevelInclusion`).

A compact band above a regular value `a` begins with a compact collar without critical points
(`TauCeti.exists_mem_Ioc_isCompact_forall_mfderiv_ne_zero`), so both statements hold
at every regular value `a` with a compact band above it
(`TauCeti.hasHomotopyExtensionProperty_sublevel_of_isRegularValue` and
`TauCeti.hasHomotopyExtensionProperty_range_sublevelInclusion_of_isRegularValue`). For a proper
function every band is compact, so the sublevels at an increasing sequence of regular values, such
as those of `TauCeti.IsMorse.exists_regular_sublevel_exhaustion`, are linked by closed
cofibrations. Towers of closed cofibrations are what the comparison of the sublevel exhaustion of
a proper Morse function with a CW model, one cell attachment at a time, passes through.

## Main results

* `TauCeti.hasHomotopyExtensionProperty_sublevel`: a sublevel with a compact band above it free
  of critical points has the homotopy extension property in `M`.
* `TauCeti.hasHomotopyExtensionProperty_range_sublevelInclusion`: the inclusion of such a
  sublevel into a larger sublevel is a closed cofibration.
* `TauCeti.hasHomotopyExtensionProperty_sublevel_of_isRegularValue` and
  `TauCeti.hasHomotopyExtensionProperty_range_sublevelInclusion_of_isRegularValue`: the same at a
  regular value with a compact band above it.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Theorem 3.1.
* J. Milnor, *Lectures on the h-cobordism theorem*, Princeton University Press, 1965,
  Theorem 3.4, for the collar of a regular level.
-/

public section

open Set
open scoped ContDiff Manifold

namespace TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] [I.Boundaryless] [IsManifold I ∞ M] {f : M → ℝ} {a b c : ℝ}

/-- **A sublevel with a regular collar is a closed cofibration.** Let `f` be a smooth function
and `a < b` such that the band `f⁻¹[a, b]` is compact and contains no critical point of `f`. Then
the sublevel `{f ≤ a}` has the homotopy extension property in `M`. -/
theorem hasHomotopyExtensionProperty_sublevel (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hab : a < b)
    (hcompact : IsCompact (f ⁻¹' Icc a b))
    (hreg : ∀ x, a ≤ f x → f x ≤ b → mfderiv I 𝓘(ℝ) f x ≠ 0) :
    HasHomotopyExtensionProperty {x | f x ≤ a} := by
  obtain ⟨φ, -, -, -, hφ⟩ := exists_flow_apply_eq_sub hf hcompact hreg
  exact hasHomotopyExtensionProperty_sublevel_of_apply_eq_sub hf.continuous hab φ φ.cont'
    φ.map_zero_apply hφ

/-- **The inclusion of a sublevel with a regular collar into a larger sublevel is a closed
cofibration.** Let `f` be a smooth function and `a < b` such that the band `f⁻¹[a, b]` is compact
and contains no critical point of `f`. Then for every `c ≥ a` the image of `{f ≤ a}` in
`{f ≤ c}` has the homotopy extension property. -/
theorem hasHomotopyExtensionProperty_range_sublevelInclusion (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hab : a < b) (hcompact : IsCompact (f ⁻¹' Icc a b))
    (hreg : ∀ x, a ≤ f x → f x ≤ b → mfderiv I 𝓘(ℝ) f x ≠ 0) (hac : a ≤ c) :
    HasHomotopyExtensionProperty (range (sublevelInclusion f a c hac)) := by
  obtain ⟨φ, -, -, -, hφ⟩ := exists_flow_apply_eq_sub hf hcompact hreg
  exact hasHomotopyExtensionProperty_range_sublevelInclusion_of_apply_eq_sub hf.continuous hab φ
    φ.cont' φ.map_zero_apply hφ hac

/-- **A sublevel at a regular value is a closed cofibration.** If `a` is a regular value of a
smooth function `f` and the band `f⁻¹[a, b]`, where `a < b`, is compact, then the sublevel
`{f ≤ a}` has the homotopy extension property in `M`. -/
theorem hasHomotopyExtensionProperty_sublevel_of_isRegularValue (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hab : a < b) (hcompact : IsCompact (f ⁻¹' Icc a b)) (ha : IsRegularValue I 𝓘(ℝ) f a) :
    HasHomotopyExtensionProperty {x | f x ≤ a} := by
  obtain ⟨b', ⟨hab', -⟩, hcompact', hreg⟩ :=
    exists_mem_Ioc_isCompact_forall_mfderiv_ne_zero (hf.of_le (by simp)) hab hcompact ha
  exact hasHomotopyExtensionProperty_sublevel hf hab' hcompact' hreg

/-- **The inclusion of a sublevel at a regular value into a larger sublevel is a closed
cofibration.** If `a` is a regular value of a smooth function `f` and the band `f⁻¹[a, b]`, where
`a < b`, is compact, then for every `c ≥ a` the image of `{f ≤ a}` in `{f ≤ c}` has the homotopy
extension property. -/
theorem hasHomotopyExtensionProperty_range_sublevelInclusion_of_isRegularValue
    (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hab : a < b) (hcompact : IsCompact (f ⁻¹' Icc a b))
    (ha : IsRegularValue I 𝓘(ℝ) f a) (hac : a ≤ c) :
    HasHomotopyExtensionProperty (range (sublevelInclusion f a c hac)) := by
  obtain ⟨b', ⟨hab', -⟩, hcompact', hreg⟩ :=
    exists_mem_Ioc_isCompact_forall_mfderiv_ne_zero (hf.of_le (by simp)) hab hcompact ha
  exact hasHomotopyExtensionProperty_range_sublevelInclusion hf hab' hcompact' hreg hac

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Banach
public import TauCeti.LinearAlgebra.End.RangePow

/-!
# Invertibility on a stable range

A bounded endomorphism of a Banach space restricts to an invertible bounded operator on
a closed range of a power once both its kernel and range chains have stabilized. In terms of a
commuting idempotent `P` projecting onto the stable kernel along the stable range, the operator
`g (1 - P) + P` is invertible (`ContinuousLinearMap.isUnit_mul_one_sub_add_of_stable`).
-/

public section

namespace ContinuousLinearMap

variable {𝕜 X : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]

/-- If both power chains stabilize at `n` and the range of the `n`th power is closed,
the restriction to that range has a bounded inverse. No compactness hypothesis is needed. -/
theorem isUnit_restrict_range_pow_of_stable (A : X →L[𝕜] X) (n : ℕ)
    (hk : LinearMap.ker ((A : X →ₗ[𝕜] X) ^ (n + 1)) =
      LinearMap.ker ((A : X →ₗ[𝕜] X) ^ n))
    (hr : LinearMap.range ((A : X →ₗ[𝕜] X) ^ (n + 1)) =
      LinearMap.range ((A : X →ₗ[𝕜] X) ^ n))
    (hc : IsClosed (LinearMap.range ((A : X →ₗ[𝕜] X) ^ n) : Set X))
    (h : Set.MapsTo A (LinearMap.range ((A : X →ₗ[𝕜] X) ^ n))
      (LinearMap.range ((A : X →ₗ[𝕜] X) ^ n)) := A.toLinearMap.mapsTo_range_pow n) :
    IsUnit (A.restrict h : LinearMap.range ((A : X →ₗ[𝕜] X) ^ n) →L[𝕜]
      LinearMap.range ((A : X →ₗ[𝕜] X) ^ n)) := by
  have : CompleteSpace (LinearMap.range ((A : X →ₗ[𝕜] X) ^ n)) := hc.completeSpace_coe
  rw [isUnit_iff_bijective]
  exact LinearMap.bijective_restrict_range_pow_of_stable A.toLinearMap n hk hr h

/-- Let `P` be an idempotent commuting with `g` whose range is the kernel of `g ^ (p + 1)` and
whose kernel is the range of `g ^ (p + 1)`. Then `g` is invertible on the kernel of `P`: the
operator `g (1 - P) + P` is invertible. -/
theorem isUnit_mul_one_sub_add_of_stable {g P : X →L[𝕜] X} {p : ℕ} (hP : IsIdempotentElem P)
    (hgP : Commute g P) (hr : LinearMap.range (P : X →ₗ[𝕜] X) =
      LinearMap.ker ((g : X →ₗ[𝕜] X) ^ (p + 1)))
    (hk' : LinearMap.ker (P : X →ₗ[𝕜] X) = LinearMap.range ((g : X →ₗ[𝕜] X) ^ (p + 1))) :
    IsUnit (g * (1 - P) + P) := by
  have hPP (x : X) : P (P x) = P x := congr($(hP.eq) x)
  have hPg (x : X) : P (g x) = g (P x) := congr($(hgP.eq) x).symm
  have happly (x : X) : (g * (1 - P) + P) x = g (x - P x) + P x := by simp
  rw [isUnit_iff_bijective]
  refine ⟨(injective_iff_map_eq_zero _).mpr fun x hx ↦ ?_, fun y ↦ ?_⟩
  · rw [happly] at hx
    have hPx : P x = 0 := by simpa [hPg, hPP] using congr(P $hx)
    rw [hPx, sub_zero, add_zero] at hx
    have hmem : x ∈ LinearMap.ker ((g : X →ₗ[𝕜] X) ^ (p + 1)) := by
      rw [LinearMap.mem_ker, pow_succ, mul_apply_eq_comp]
      simp [hx]
    obtain ⟨z, rfl⟩ := hr ▸ hmem
    simpa [hPP] using hPx
  · have hy : y - P y ∈ LinearMap.range ((g : X →ₗ[𝕜] X) ^ (p + 1)) := by
      rw [← hk', LinearMap.mem_ker]
      simp [hPP]
    obtain ⟨z, hz⟩ := hy
    set u := ((g : X →ₗ[𝕜] X) ^ p) z
    have hgu : g u = y - P y := by
      rw [← hz, pow_succ', mul_apply_eq_comp, coe_coe]
    have hv : P (u - P u) = 0 := by rw [map_sub, hPP, sub_self]
    have hgv : g (u - P u) = y - P y := by
      rw [map_sub, ← hPg, hgu, map_sub, hPP, sub_self, sub_zero]
    have hPv : P (P y + (u - P u)) = P y := by rw [map_add, hPP, hv, add_zero]
    refine ⟨P y + (u - P u), ?_⟩
    simp only [happly, hPv, add_sub_cancel_left, hgv, sub_add_cancel]

end ContinuousLinearMap

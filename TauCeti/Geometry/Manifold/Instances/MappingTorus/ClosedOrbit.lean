/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.SmoothEmbedding
public import TauCeti.Geometry.Manifold.Instances.MappingTorus
import Mathlib.Order.Interval.Set.Nat
import TauCeti.Geometry.Manifold.Immersion.Differential

/-!
# Closed orbits of the suspension flow

Let `φ : M ≃ₘ^n⟮I, I⟯ M` be a diffeomorphism and `Y_φ = (ℝ × M) / ((t, x) ∼ (t + 1, φ⁻¹ x))` its
smooth mapping torus. If `x` is a periodic point of `φ` with period `d`, so `φ^[d] x = x`, then
`[t + d, x] = [t, φ^[d] x] = [t, x]`, so `t ↦ [t, x]` descends to a map

`γ : ℝ / dℤ → Y_φ`, `γ [t] = [t, x]`

(`TauCeti.SmoothMappingTorus.closedOrbit φ h`). It parametrizes the orbit of the suspension flow
through `[0, x]`: translating the parameter by `s` is the time-`s` map of the flow
(`TauCeti.SmoothMappingTorus.flow_closedOrbit`).

This file shows that `γ` is `C^n` for every positive period `d`, that its projection to the base
circle `ℝ / ℤ` has derivative one, and that it is injective exactly when `d` is the least period of
`x`. On a finite-dimensional boundaryless manifold `M`, `γ` is therefore an immersion of the
circle, and a smooth embedding exactly when `d` is the least period. Its image is the flow orbit
through `[0, x]`, so it depends neither on the period `d` (a larger period traverses the same
image several times) nor on which point of the `φ`-orbit of `x` is chosen as starting point.
The closed orbit meets each fibre `x ↦ [t, x]` of the mapping torus exactly in the points
`[t, φ^[j] x]` for `j` below the least period of `x`, so in as many points as that period.

So each periodic orbit of `φ` of least period `d` gives an embedded closed orbit of the suspension
flow, of period `d`, which meets each fibre in that periodic orbit. No compactness of `M` is
needed.

## Main definitions

* `TauCeti.SmoothMappingTorus.closedOrbit φ h`: for `h : Function.IsPeriodicPt φ d x`, the map
  `ℝ / dℤ → Y_φ`, `[t] ↦ [t, x]`.

## Main results

* `TauCeti.SmoothMappingTorus.range_closedOrbit`: the image of `γ` is the orbit of the suspension
  flow through `[0, x]`.
* `TauCeti.SmoothMappingTorus.closedOrbit_apply`,
  `TauCeti.SmoothMappingTorus.range_closedOrbit_apply`: starting at `φ x` instead of `x` translates
  the parameter by one and does not change the image.
* `TauCeti.SmoothMappingTorus.injective_closedOrbit_iff`: `γ` is injective exactly when `d` is the
  least period of `x`.
* `TauCeti.SmoothMappingTorus.mk_preimage_range_closedOrbit`,
  `TauCeti.SmoothMappingTorus.ncard_mk_preimage_range_closedOrbit`: the intersection of the image
  with the fibre at height `t` consists of the points `[t, φ^[j] x]`, `j` below the least period.
* `TauCeti.SmoothMappingTorus.mfderiv_proj_mfderiv_closedOrbit`: the projection of `γ` to the
  circle `ℝ / ℤ` has derivative one.
* `TauCeti.SmoothMappingTorus.isImmersion_closedOrbit`,
  `TauCeti.SmoothMappingTorus.isSmoothEmbedding_closedOrbit_iff`: `γ` is an immersion, and it is a
  smooth embedding exactly when `d` is the least period of `x`.

## References

* Michael Hutchings and Michael Sullivan, *The periodic Floer homology of a Dehn twist*, Algebraic
  & Geometric Topology 5 (2005), 301–354, Section 2 (closed orbits of the mapping torus and the
  periodic orbits of the monodromy).
-/

public noncomputable section

open Set Function Manifold
open scoped Manifold ContDiff

namespace TauCeti

namespace SmoothMappingTorus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : ℕ∞ω}
  (φ : M ≃ₘ^n⟮I, I⟯ M)

variable {φ} {d : ℕ} {x : M}

variable (φ) in
/-- The closed orbit `ℝ / dℤ → Y_φ`, `[t] ↦ [t, x]`, of the suspension flow through `[0, x]`,
for a periodic point `x` of `φ` with period `d`. It is a smooth embedding of the circle when `d`
is the least period of `x` (`TauCeti.SmoothMappingTorus.isSmoothEmbedding_closedOrbit_iff`); for a
larger period it traverses the same image several times. -/
def closedOrbit (h : IsPeriodicPt φ d x) : AddCircle (d : ℝ) → SmoothMappingTorus φ :=
  (periodic_mk h).lift

variable (h : IsPeriodicPt φ d x)

/-- The closed orbit sends the class of `t` to `[t, x]`. -/
@[simp]
theorem closedOrbit_coe (t : ℝ) : closedOrbit φ h t = mk φ t x :=
  (periodic_mk h).lift_coe t

/-- Translating the parameter of the closed orbit by `s` is the time-`s` map of the suspension
flow. -/
@[simp]
theorem flow_closedOrbit (s : ℝ) (θ : AddCircle (d : ℝ)) :
    flow φ s (closedOrbit φ h θ) = closedOrbit φ h (θ + s) := by
  induction θ using QuotientAddGroup.induction_on with
  | H t => rw [closedOrbit_coe, flow_mk, ← AddCircle.coe_add, closedOrbit_coe]

/-- The image of the closed orbit is the orbit of the suspension flow through `[0, x]`. -/
theorem range_closedOrbit : range (closedOrbit φ h) = (flow φ).orbit (mk φ 0 x) := by
  ext z
  rw [Flow.mem_orbit_iff]
  constructor
  · rintro ⟨θ, rfl⟩
    induction θ using QuotientAddGroup.induction_on with
    | H t => exact ⟨t, by simp⟩
  · rintro ⟨t, rfl⟩
    exact ⟨t, by simp⟩

/-- Starting the closed orbit at `φ x` instead of `x` translates its parameter by one. -/
theorem closedOrbit_apply (θ : AddCircle (d : ℝ)) :
    closedOrbit φ h.apply θ = closedOrbit φ h (θ + (1 : ℝ)) := by
  induction θ using QuotientAddGroup.induction_on with
  | H t => rw [closedOrbit_coe, ← AddCircle.coe_add, closedOrbit_coe, mk_add_one]

/-- The image of the closed orbit does not depend on the starting point in the `φ`-orbit of `x`. -/
theorem range_closedOrbit_apply : range (closedOrbit φ h.apply) = range (closedOrbit φ h) := by
  rw [show closedOrbit φ h.apply = closedOrbit φ h ∘ (· + ((1 : ℝ) : AddCircle (d : ℝ))) from
    funext (closedOrbit_apply h), (add_right_surjective _).range_comp]

/-- The closed orbit is injective exactly when its period `d` is the least period of `x`. -/
theorem injective_closedOrbit_iff : Injective (closedOrbit φ h) ↔ minimalPeriod φ x = d := by
  constructor
  · intro hinj
    -- `γ` takes the same value at `0` and at the least period `m`, so `d` divides `m`.
    have hm : ((minimalPeriod φ x : ℝ) : AddCircle (d : ℝ)) = ((0 : ℝ) : AddCircle (d : ℝ)) :=
      hinj (by
        rw [closedOrbit_coe, closedOrbit_coe, mk_eq_mk_iff_sub_mem_zmultiples, sub_zero]
        exact AddSubgroup.mem_zmultiples _)
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp
      ((QuotientAddGroup.eq_iff_sub_mem).mp hm)
    rw [sub_zero, zsmul_eq_mul] at hk
    have hdvd : (d : ℤ) ∣ minimalPeriod φ x := ⟨k, by rw [mul_comm]; exact_mod_cast hk.symm⟩
    exact Nat.dvd_antisymm h.minimalPeriod_dvd (Int.natCast_dvd_natCast.mp hdvd)
  · intro hd θ θ' hθ
    induction θ using QuotientAddGroup.induction_on with | H t => ?_
    induction θ' using QuotientAddGroup.induction_on with | H s => ?_
    rw [closedOrbit_coe, closedOrbit_coe, mk_eq_mk_iff_sub_mem_zmultiples, hd] at hθ
    exact (QuotientAddGroup.eq_iff_sub_mem).mpr hθ

include h in
/-- For a positive period `d`, the closed orbit meets the fibre `x ↦ [t, x]` exactly in the points
`[t, φ^[j] x]` with `j` below the least period of `x`. -/
theorem mk_preimage_range_closedOrbit (hd : 0 < d) (t : ℝ) :
    mk φ t ⁻¹' range (closedOrbit φ h) = (fun j ↦ φ^[j] x) '' Iio (minimalPeriod φ x) := by
  ext y
  have hx : x ∈ periodicPts φ := ⟨d, hd, h⟩
  have hrange : mk φ t y ∈ range (closedOrbit φ h) ↔ ∃ s : ℝ, mk φ s x = mk φ t y := by
    constructor
    · rintro ⟨θ, hθ⟩
      induction θ using QuotientAddGroup.induction_on with
      | H s => exact ⟨s, by rwa [closedOrbit_coe] at hθ⟩
    · rintro ⟨s, hs⟩
      exact ⟨s, by rwa [closedOrbit_coe]⟩
  rw [mem_preimage, hrange, exists_mk_eq_mk_iff, Diffeomorph.exists_zpow_apply_eq_iff hx]
  simp

include h in
/-- For a positive period `d`, the closed orbit meets each fibre of the mapping torus in exactly as
many points as the least period of `x`. -/
theorem ncard_mk_preimage_range_closedOrbit (hd : 0 < d) (t : ℝ) :
    (mk φ t ⁻¹' range (closedOrbit φ h)).ncard = minimalPeriod φ x := by
  rw [mk_preimage_range_closedOrbit h hd, iterate_injOn_Iio_minimalPeriod.ncard_image,
    Set.ncard_Iio_nat]

/-! ### Smoothness -/

section Manifold

variable [T2Space M] [LocallyCompactSpace M] [IsManifold I n M] [Fact (0 < (d : ℝ))]

/-- The closed orbit is `C^n`. -/
theorem contMDiff_closedOrbit : ContMDiff 𝓘(ℝ) (𝓘(ℝ).prod I) n (closedOrbit φ h) := by
  rw [← (AddCircle.isLocalDiffeomorph_coe (d : ℝ) n).contMDiff_comp_iff
    QuotientAddGroup.mk_surjective le_rfl]
  have hcomp : closedOrbit φ h ∘ ((↑) : ℝ → AddCircle (d : ℝ)) =
      uncurry (mk φ) ∘ fun t ↦ (t, x) :=
    funext fun t ↦ closedOrbit_coe h t
  rw [hcomp]
  exact (contMDiff_uncurry_mk φ).comp (contMDiff_id.prodMk contMDiff_const)

/-- The projection of the closed orbit to the circle `ℝ / ℤ` has derivative one: the derivative
of the projection `[t, x] ↦ [t]` undoes the derivative of the closed orbit. -/
theorem mfderiv_proj_comp_mfderiv_closedOrbit (hn : n ≠ 0) (θ : AddCircle (d : ℝ)) :
    (mfderiv (𝓘(ℝ).prod I) 𝓘(ℝ) (proj φ) (closedOrbit φ h θ)).comp
      (mfderiv 𝓘(ℝ) (𝓘(ℝ).prod I) (closedOrbit φ h) θ) = ContinuousLinearMap.id ℝ ℝ := by
  induction θ using QuotientAddGroup.induction_on with | H t => ?_
  -- The projection of `γ` lifts the identity of `ℝ`, so it has derivative one.
  have hlift : (proj φ ∘ closedOrbit φ h) ∘ ((↑) : ℝ → AddCircle (d : ℝ)) =
      ((↑) : ℝ → UnitAddCircle) ∘ id :=
    funext fun s ↦ by simp
  have hderiv := AddCircle.hasMFDerivAt_of_comp_coe_eq hlift (hasFDerivAt_id t)
  have hproj := ((contMDiff_proj φ).mdifferentiableAt hn :
    MDifferentiableAt (𝓘(ℝ).prod I) 𝓘(ℝ) (proj φ) (closedOrbit φ h t))
  have hγ := ((contMDiff_closedOrbit h).mdifferentiableAt hn :
    MDifferentiableAt 𝓘(ℝ) (𝓘(ℝ).prod I) (closedOrbit φ h) t)
  rw [← mfderiv_comp _ hproj hγ, hderiv.mfderiv]

/-- The derivative of the closed orbit is injective at every point. -/
theorem injective_mfderiv_closedOrbit (hn : n ≠ 0) (θ : AddCircle (d : ℝ)) :
    Injective (mfderiv 𝓘(ℝ) (𝓘(ℝ).prod I) (closedOrbit φ h) θ) := fun v w hvw ↦ by
  have hvw' := congrArg (mfderiv (𝓘(ℝ).prod I) 𝓘(ℝ) (proj φ) (closedOrbit φ h θ)) hvw
  rw [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.comp_apply,
    mfderiv_proj_comp_mfderiv_closedOrbit h hn θ] at hvw'
  exact hvw'

variable [I.Boundaryless] [FiniteDimensional ℝ E]

/-- The closed orbit is an immersion of the circle, for every positive period `d`. -/
theorem isImmersion_closedOrbit (hn : 1 ≤ n) :
    IsImmersion 𝓘(ℝ) (𝓘(ℝ).prod I) n (closedOrbit φ h) := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  rw [isImmersion_iff_forall_isImmersionAt]
  intro θ
  exact ((contMDiff_closedOrbit h).contMDiffOn.isImmersionAt_iff_injective_mfderiv isOpen_univ
    (mem_univ θ) hn).2 (injective_mfderiv_closedOrbit h hn0 θ)

/-- The closed orbit is a smooth embedding of the circle exactly when its period `d` is the least
period of `x`. -/
theorem isSmoothEmbedding_closedOrbit_iff (hn : 1 ≤ n) :
    IsSmoothEmbedding 𝓘(ℝ) (𝓘(ℝ).prod I) n (closedOrbit φ h) ↔ minimalPeriod φ x = d := by
  rw [← injective_closedOrbit_iff h]
  exact ⟨fun he ↦ he.isEmbedding.injective, fun hinj ↦ ⟨isImmersion_closedOrbit h hn,
    ((contMDiff_closedOrbit h).continuous.isClosedEmbedding hinj).isEmbedding⟩⟩

end Manifold

end SmoothMappingTorus

end TauCeti

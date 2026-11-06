/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.Mass.SmulLeft
public import TauCeti.Analysis.Distribution.Mass.Support
public import TauCeti.Analysis.Distribution.TestFunction.Pullback

/-!
# Normal and locally normal currents

Let `Ω` be an open set of a real normed space `E`. A `k`-current on `Ω` is a continuous linear map
`T` on the test `k`-forms `𝓓(Ω, E [⋀^Fin k]→L[ℝ] F)`, and for `k = j + 1` its boundary is the
`j`-current `∂T = T ∘ d`. The boundary of a `0`-current is zero. The current `T` is

* *locally normal* (`Distribution.IsLocallyNormal`) if `T` and `∂T` both have locally finite
  mass, that is, satisfy order-zero bounds on the tests supported in each compact subset of `Ω`;
* *normal* (`Distribution.IsNormal`) if `T` and `∂T` both have finite mass.

Neither notion includes a support condition: unlike Federer's normal currents, a normal current
here need not have compact support. A current whose support is a compact subset of `Ω` is normal
exactly when it is locally normal, and multiplying a locally normal current by a test function
gives a normal current with compact support. Locally normal currents form a real vector space
stable under the boundary, restriction to open subsets, multiplication by smooth functions and
pushforward along smooth maps proper from `Ω` to an open target set. Normal currents are stable
under the same operations given bounds on the multiplier and its derivative, or on the derivative
of the map; the mass bounds of `TauCeti.Analysis.Distribution.Mass.SmulLeft` and
`TauCeti.Analysis.Distribution.TestFunction.Pullback` control the result.

## Main declarations

* `Distribution.IsLocallyNormal`, `Distribution.IsNormal`: locally normal and normal currents.
* `Distribution.IsNormal.isLocallyNormal`: normal currents are locally normal.
* `Distribution.isNormal_iff_isLocallyNormal_of_isCompact_dsupport`: for a current with compact
  support in `Ω`, normality is local normality.
* `Distribution.IsLocallyNormal.comp_extDerivCLM`, `Distribution.IsNormal.comp_extDerivCLM`: the
  boundary of a (locally) normal current is (locally) normal.
* `Distribution.IsLocallyNormal.comp_monoCLM`, `Distribution.IsLocallyNormal.comp_smulLeftCLM`,
  `Distribution.IsLocallyNormal.comp_pullbackCLM`: restriction, smooth multiples and pushforward,
  with the corresponding statements for `Distribution.IsNormal`.
* `Distribution.IsLocallyNormal.isNormal_comp_smulLeftCLM`: a test function times a locally normal
  current is normal.
* `Distribution.isNormal_comp_evalCLM_comp_toBoundedContinuousFunctionCLM`: degree-zero point
  currents are normal.

## References

* H. Federer, *Geometric Measure Theory*, §4.1.7 (normal and locally normal currents).
* L. Simon, *Introduction to Geometric Measure Theory*, Chapter 6, §2.
-/

public section

noncomputable section

open Set TopologicalSpace TestFunction ContinuousLinearMap
open scoped ENNReal NNReal Distributions

namespace Distribution

variable {E F V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {Ω : Opens E} {k : ℕ}

section Defs

/-- A current `T` on the test `k`-forms on `Ω` is *locally normal* if both `T` and its boundary
`∂T = T ∘ d` have locally finite mass. The boundary of a `0`-current is zero, so in degree zero
this is local finiteness of the mass of `T`. No support condition is imposed. -/
def IsLocallyNormal : {k : ℕ} → (𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) →L[ℝ] V) → Prop
  | 0, T => HasLocallyFiniteMass T
  | _ + 1, T => HasLocallyFiniteMass T ∧ HasLocallyFiniteMass (T ∘L extDerivCLM)

/-- A current `T` on the test `k`-forms on `Ω` is *normal* if both `T` and its boundary
`∂T = T ∘ d` have finite mass. The boundary of a `0`-current is zero, so in degree zero this is
finiteness of the mass of `T`. No support condition is imposed. -/
def IsNormal : {k : ℕ} → (𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) →L[ℝ] V) → Prop
  | 0, T => mass T ≠ ⊤
  | _ + 1, T => mass T ≠ ⊤ ∧ mass (T ∘L extDerivCLM) ≠ ⊤

/-- In degree zero, local normality is local finiteness of the mass. -/
@[simp]
theorem isLocallyNormal_finZero_iff {T : 𝓓(Ω, E [⋀^Fin 0]→L[ℝ] F) →L[ℝ] V} :
    IsLocallyNormal T ↔ HasLocallyFiniteMass T :=
  Iff.rfl

/-- In degree `k + 1`, local normality is local finiteness of the masses of `T` and `∂T`. -/
theorem isLocallyNormal_succ_iff {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] V} :
    IsLocallyNormal T ↔ HasLocallyFiniteMass T ∧ HasLocallyFiniteMass (T ∘L extDerivCLM) :=
  Iff.rfl

/-- In degree zero, normality is finiteness of the mass. -/
@[simp]
theorem isNormal_finZero_iff {T : 𝓓(Ω, E [⋀^Fin 0]→L[ℝ] F) →L[ℝ] V} :
    IsNormal T ↔ mass T ≠ ⊤ :=
  Iff.rfl

/-- In degree `k + 1`, normality is finiteness of the masses of `T` and `∂T`. -/
theorem isNormal_succ_iff {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] V} :
    IsNormal T ↔ mass T ≠ ⊤ ∧ mass (T ∘L extDerivCLM) ≠ ⊤ :=
  Iff.rfl

variable {T : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) →L[ℝ] V}

/-- A locally normal current has locally finite mass. -/
theorem IsLocallyNormal.hasLocallyFiniteMass (hT : IsLocallyNormal T) : HasLocallyFiniteMass T := by
  cases k
  exacts [hT, hT.1]

/-- A normal current has finite mass. -/
theorem IsNormal.mass_ne_top (hT : IsNormal T) : mass T ≠ ⊤ := by
  cases k
  exacts [hT, hT.1]

/-- Normal currents are locally normal. -/
theorem IsNormal.isLocallyNormal (hT : IsNormal T) : IsLocallyNormal T := by
  cases k with
  | zero => exact hasLocallyFiniteMass_of_mass_ne_top T hT
  | succ k =>
    exact ⟨hasLocallyFiniteMass_of_mass_ne_top T hT.1, hasLocallyFiniteMass_of_mass_ne_top _ hT.2⟩

end Defs

section Module

variable {T S : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) →L[ℝ] V}

@[simp]
theorem isLocallyNormal_zero : IsLocallyNormal (0 : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) →L[ℝ] V) := by
  cases k
  · rw [isLocallyNormal_finZero_iff]
    simpa using hasLocallyFiniteMass_zero
  · rw [isLocallyNormal_succ_iff]
    exact ⟨by simpa using hasLocallyFiniteMass_zero, by simpa using hasLocallyFiniteMass_zero⟩

theorem IsLocallyNormal.add (hT : IsLocallyNormal T) (hS : IsLocallyNormal S) :
    IsLocallyNormal (T + S) := by
  cases k
  · rw [isLocallyNormal_finZero_iff]
    simpa using HasLocallyFiniteMass.add hT hS
  · rw [isLocallyNormal_succ_iff]
    exact ⟨by simpa using hT.1.add hS.1, by simpa using hT.2.add hS.2⟩

theorem IsLocallyNormal.smul (hT : IsLocallyNormal T) (a : ℝ) : IsLocallyNormal (a • T) := by
  cases k
  · rw [isLocallyNormal_finZero_iff]
    simpa using HasLocallyFiniteMass.smul hT a
  · rw [isLocallyNormal_succ_iff]
    exact ⟨by simpa using hT.1.smul a, by simpa using hT.2.smul a⟩

theorem IsLocallyNormal.neg (hT : IsLocallyNormal T) : IsLocallyNormal (-T) := by
  simpa using hT.smul (-1)

theorem IsLocallyNormal.sub (hT : IsLocallyNormal T) (hS : IsLocallyNormal S) :
    IsLocallyNormal (T - S) := by
  simpa [sub_eq_add_neg] using hT.add hS.neg

@[simp]
theorem isNormal_zero : IsNormal (0 : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) →L[ℝ] V) := by
  cases k
  · simp [isNormal_finZero_iff]
  · simp [isNormal_succ_iff]

theorem IsNormal.add (hT : IsNormal T) (hS : IsNormal S) : IsNormal (T + S) := by
  cases k
  · rw [isNormal_finZero_iff, FunLike.coe_add]
    exact ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hT, hS⟩) mass_add_le
  · rw [isNormal_succ_iff, add_comp, FunLike.coe_add, FunLike.coe_add]
    exact ⟨ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hT.1, hS.1⟩) mass_add_le,
      ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hT.2, hS.2⟩) mass_add_le⟩

theorem IsNormal.smul (hT : IsNormal T) (a : ℝ) : IsNormal (a • T) := by
  cases k
  · rw [isNormal_finZero_iff, FunLike.coe_smul, mass_smul]
    exact ENNReal.mul_ne_top enorm_ne_top hT
  · rw [isNormal_succ_iff, smul_comp, FunLike.coe_smul, FunLike.coe_smul, mass_smul, mass_smul]
    exact ⟨ENNReal.mul_ne_top enorm_ne_top hT.1, ENNReal.mul_ne_top enorm_ne_top hT.2⟩

theorem IsNormal.neg (hT : IsNormal T) : IsNormal (-T) := by
  simpa using hT.smul (-1)

theorem IsNormal.sub (hT : IsNormal T) (hS : IsNormal S) : IsNormal (T - S) := by
  simpa [sub_eq_add_neg] using hT.add hS.neg

end Module

section Boundary

variable {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] V}

/-- **The boundary of a locally normal current is locally normal**, since `∂ ∂ T = 0`. -/
theorem IsLocallyNormal.comp_extDerivCLM (hT : IsLocallyNormal T) :
    IsLocallyNormal (T ∘L extDerivCLM) := by
  cases k
  · exact hT.2
  · refine ⟨hT.2, ?_⟩
    rw [comp_assoc, extDerivCLM_comp_extDerivCLM, comp_zero]
    simpa using hasLocallyFiniteMass_zero

/-- **The boundary of a normal current is normal**, since `∂ ∂ T = 0`. -/
theorem IsNormal.comp_extDerivCLM (hT : IsNormal T) : IsNormal (T ∘L extDerivCLM) := by
  cases k
  · exact hT.2
  · refine ⟨hT.2, ?_⟩
    rw [comp_assoc, extDerivCLM_comp_extDerivCLM, comp_zero, FunLike.coe_zero, mass_zero]
    exact ENNReal.zero_ne_top

end Boundary

section CompactSupport

variable [FiniteDimensional ℝ E] {T : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) →L[ℝ] V}

/-- **Compactly supported locally normal currents are normal.** If the support of a locally normal
current is a compact subset of `Ω`, then the current and its boundary have finite mass. -/
theorem IsLocallyNormal.isNormal (hT : IsLocallyNormal T) (hc : IsCompact (dsupport T))
    (hΩ : dsupport T ⊆ Ω) : IsNormal T := by
  cases k with
  | zero => exact HasLocallyFiniteMass.mass_ne_top hT hc hΩ
  | succ k =>
    have hsub : dsupport (T ∘L extDerivCLM) ⊆ dsupport T := by
      rw [coe_comp]
      exact dsupport_comp_extDerivCLM_subset T
    exact ⟨hT.1.mass_ne_top hc hΩ,
      hT.2.mass_ne_top (hc.of_isClosed_subset isClosed_dsupport hsub) (hsub.trans hΩ)⟩

/-- For a current whose support is a compact subset of `Ω`, normality and local normality
agree. -/
theorem isNormal_iff_isLocallyNormal_of_isCompact_dsupport (hc : IsCompact (dsupport T))
    (hΩ : dsupport T ⊆ Ω) : IsNormal T ↔ IsLocallyNormal T :=
  ⟨IsNormal.isLocallyNormal, fun hT => hT.isNormal hc hΩ⟩

end CompactSupport

section Restriction

variable {Ω' : Opens E} {T : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) →L[ℝ] V}

/-- **Restriction.** The restriction of a locally normal current to an open subset `Ω' ⊆ Ω` is
locally normal. -/
theorem IsLocallyNormal.comp_monoCLM (hT : IsLocallyNormal T) (h : Ω' ≤ Ω) :
    IsLocallyNormal (T ∘L (monoCLM ℝ : 𝓓(Ω', E [⋀^Fin k]→L[ℝ] F) →L[ℝ] _)) := by
  cases k with
  | zero =>
    rw [isLocallyNormal_finZero_iff, coe_comp]
    exact HasLocallyFiniteMass.comp_monoCLM hT h
  | succ k =>
    rw [isLocallyNormal_succ_iff, comp_monoCLM_comp_extDerivCLM h, coe_comp, coe_comp]
    exact ⟨hT.1.comp_monoCLM h, hT.2.comp_monoCLM h⟩

/-- **Restriction.** The restriction of a normal current to an open subset `Ω' ⊆ Ω` is normal: its
mass and the mass of its boundary are local masses of `T` and `∂T` on `Ω'`. -/
theorem IsNormal.comp_monoCLM (hT : IsNormal T) (h : Ω' ≤ Ω) :
    IsNormal (T ∘L (monoCLM ℝ : 𝓓(Ω', E [⋀^Fin k]→L[ℝ] F) →L[ℝ] _)) := by
  cases k with
  | zero =>
    rw [isNormal_finZero_iff, coe_comp]
    exact ne_top_of_le_ne_top hT (mass_comp_monoCLM_le h)
  | succ k =>
    rw [isNormal_succ_iff, comp_monoCLM_comp_extDerivCLM h, coe_comp, coe_comp]
    exact ⟨ne_top_of_le_ne_top hT.1 (mass_comp_monoCLM_le h),
      ne_top_of_le_ne_top hT.2 (mass_comp_monoCLM_le h)⟩

end Restriction

section SmulLeft

variable {T : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) →L[ℝ] V} {f : E → ℝ}

/-- **Smooth multiples.** Multiplying a locally normal current by a smooth function gives a
locally normal current; the boundary obeys `∂(fT) = f ∂T - T ⌞ df`. -/
theorem IsLocallyNormal.comp_smulLeftCLM (hT : IsLocallyNormal T) (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    IsLocallyNormal (T ∘L smulLeftCLM hf) := by
  cases k with
  | zero =>
    rw [isLocallyNormal_finZero_iff, coe_comp]
    exact HasLocallyFiniteMass.comp_smulLeftCLM hT hf
  | succ k =>
    rw [isLocallyNormal_succ_iff, coe_comp]
    exact ⟨hT.1.comp_smulLeftCLM hf, hT.1.comp_smulLeftCLM_comp_extDerivCLM hf hT.2⟩

/-- **Smooth multiples.** Multiplying a normal current by a smooth function that is bounded on `Ω`
with bounded derivative on `Ω` gives a normal current. -/
theorem IsNormal.comp_smulLeftCLM (hT : IsNormal T) (hf : ContDiff ℝ (⊤ : ℕ∞) f) {C C' : ℝ≥0}
    (hfC : ∀ x ∈ Ω, ‖f x‖ ≤ C) (hdfC : ∀ x ∈ Ω, ‖fderiv ℝ f x‖ ≤ C') :
    IsNormal (T ∘L smulLeftCLM hf) := by
  have hfC' (x : E) (hx : x ∈ Ω) : ‖f x‖ₑ ≤ C := by
    rw [← ofReal_norm, ← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal (hfC x hx)
  have hM (S : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) →L[ℝ] V) (hS : mass S ≠ ⊤) :
      mass (S ∘L smulLeftCLM hf) ≠ ⊤ := by
    rw [coe_comp]
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top hS)
      (mass_comp_smulLeftCLM_le S hf hfC')
  cases k with
  | zero => exact hM T hT
  | succ k =>
    have hdfC' (x : E) (hx : x ∈ Ω) : ‖fderiv ℝ f x‖ₑ ≤ C' := by
      rw [← ofReal_norm, ← ENNReal.ofReal_coe_nnreal]
      exact ENNReal.ofReal_le_ofReal (hdfC x hx)
    refine ⟨hM T hT.1, ne_top_of_le_ne_top ?_
      (mass_comp_smulLeftCLM_comp_extDerivCLM_le T hf hfC' hdfC')⟩
    exact ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.coe_ne_top hT.2,
      ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) ENNReal.coe_ne_top) hT.1⟩

variable [FiniteDimensional ℝ E]

/-- **Cutoffs of locally normal currents are normal.** The product `χ T` of a locally normal
current with a test function `χ` on `Ω` is a normal current supported in `tsupport χ`. -/
theorem IsLocallyNormal.isNormal_comp_smulLeftCLM (hT : IsLocallyNormal T) (χ : 𝓓(Ω, ℝ)) :
    IsNormal (T ∘L smulLeftCLM χ.contDiff) := by
  have hsub : dsupport (T ∘L smulLeftCLM χ.contDiff) ⊆ tsupport χ := by
    rw [coe_comp]
    exact (dsupport_comp_smulLeftCLM_subset T χ.contDiff).trans inter_subset_left
  exact (hT.comp_smulLeftCLM χ.contDiff).isNormal
    (χ.hasCompactSupport.of_isClosed_subset isClosed_dsupport hsub)
    (hsub.trans χ.tsupport_subset)

end SmulLeft

section Pushforward

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] {Ω' : Opens E'} {Φ : E → E'}
  {hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ Ω}
  {hΦp : ∀ K : Set E', IsCompact K → K ⊆ Ω' → IsCompact ((Ω : Set E) ∩ Φ ⁻¹' K)}
  {T : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) →L[ℝ] V}

/-- **Pushforward.** The pushforward `Φ_# T = T ∘ Φ^*` of a locally normal current along a map
smooth on `Ω` and proper from `Ω` to `Ω'` is locally normal. -/
theorem IsLocallyNormal.comp_pullbackCLM (hT : IsLocallyNormal T) :
    IsLocallyNormal (T ∘L pullbackCLM Φ hΦ hΦp) := by
  cases k with
  | zero =>
    rw [isLocallyNormal_finZero_iff, coe_comp]
    exact HasLocallyFiniteMass.comp_pullbackCLM hT
  | succ k =>
    rw [isLocallyNormal_succ_iff, comp_pullbackCLM_comp_extDerivCLM, coe_comp, coe_comp]
    exact ⟨hT.1.comp_pullbackCLM, hT.2.comp_pullbackCLM⟩

/-- **Pushforward.** If `‖DΦ‖ ≤ L` on `Ω`, the pushforward `Φ_# T = T ∘ Φ^*` of a normal current
is normal. -/
theorem IsNormal.comp_pullbackCLM (hT : IsNormal T) {L : ℝ≥0}
    (hL : ∀ x ∈ Ω, ‖fderiv ℝ Φ x‖ ≤ L) : IsNormal (T ∘L pullbackCLM Φ hΦ hΦp) := by
  have hM {j : ℕ} (S : 𝓓(Ω, E [⋀^Fin j]→L[ℝ] F) →L[ℝ] V) (hS : mass S ≠ ⊤) :
      mass (S ∘L pullbackCLM Φ hΦ hΦp) ≠ ⊤ := by
    rw [coe_comp]
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top) hS)
      (mass_comp_pullbackCLM_le S hL)
  cases k with
  | zero => exact hM T hT
  | succ k =>
    rw [isNormal_succ_iff, comp_pullbackCLM_comp_extDerivCLM]
    exact ⟨hM T hT.1, hM _ hT.2⟩

end Pushforward

section Point

/-- **Point currents are normal.** For `x ∈ E` and a continuous linear map `ℓ` on `0`-forms, the
degree-zero point current `ω ↦ ℓ (ω x)` is normal: its mass is at most `‖ℓ‖`, with equality when
`x ∈ Ω` and `E` is finite-dimensional (`Distribution.mass_apply_apply`). -/
theorem isNormal_comp_evalCLM_comp_toBoundedContinuousFunctionCLM
    (ℓ : (E [⋀^Fin 0]→L[ℝ] F) →L[ℝ] V) (x : E) :
    IsNormal (ℓ ∘L BoundedContinuousFunction.evalCLM ℝ x ∘L
      (toBoundedContinuousFunctionCLM ℝ : 𝓓(Ω, E [⋀^Fin 0]→L[ℝ] F) →L[ℝ] _)) := by
  rw [isNormal_finZero_iff]
  refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := ‖ℓ‖)) (mass_le_iff.2 fun φ hφ => ?_)
  rw [← ofReal_norm]
  refine ENNReal.ofReal_le_ofReal ?_
  simpa using (ℓ.le_opNorm (φ x)).trans (mul_le_of_le_one_right (norm_nonneg ℓ) (hφ x))

end Point

end Distribution

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Normal currents form a real submodule of the continuous-linear dual of test forms. -/
def normalCurrentSubmodule (Ω : Opens E) (k : ℕ) :
    Submodule ℝ (𝓓(Ω, E [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ) where
  carrier := {T | Distribution.IsNormal T}
  zero_mem' := Distribution.isNormal_zero
  add_mem' := Distribution.IsNormal.add
  smul_mem' a _ h := h.smul a

@[simp] theorem mem_normalCurrentSubmodule {Ω : Opens E} {k : ℕ}
    {T : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ} :
    T ∈ normalCurrentSubmodule Ω k ↔ Distribution.IsNormal T := Iff.rfl

end TauCeti

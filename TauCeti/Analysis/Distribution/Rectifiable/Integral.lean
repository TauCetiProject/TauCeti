/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.Rectifiable.IntegerRectifiable
public import TauCeti.Analysis.Distribution.Mass.Normal

/-!
# Locally integral and integral currents

A `k`-current `T` on an open subset `Ω` of a finite-dimensional real inner product space is
*locally integral* (`Distribution.IsLocallyIntegral`) when `T` and its boundary `∂T = T ∘ d` are
both integer-rectifiable (`Distribution.IsIntegerRectifiable`). In degree zero the boundary is
zero, so this is integer-rectifiability of `T`. Integer-rectifiable currents have locally finite
mass, so the local mass bounds of Federer and Fleming are automatic, and locally integral currents
are locally normal (`Distribution.IsLocallyIntegral.isLocallyNormal`).

An *integral current* (`Distribution.IsIntegralCurrent`) is a locally integral current of finite
mass whose boundary has finite mass, that is a locally integral normal current; unlike Federer's
integral currents, it carries no support condition. A *compactly supported integral current*
(`Distribution.IsCompactlySupportedIntegralCurrent`) is an integral current whose support is a
compact subset of `Ω`; a compactly supported locally integral current
is automatically one (`Distribution.IsLocallyIntegral.isCompactlySupportedIntegralCurrent`). The
three classes are nested, are additive subgroups of the real `k`-currents (not real subspaces), and
are preserved by the boundary, since `∂∂T = 0`.

## Main declarations

* `Distribution.IsLocallyIntegral`, `Distribution.IsIntegralCurrent`,
  `Distribution.IsCompactlySupportedIntegralCurrent`: the three classes of currents.
* `Distribution.locallyIntegralCurrents`, `Distribution.integralCurrents`,
  `Distribution.compactlySupportedIntegralCurrents`: their additive subgroups.
* `Distribution.IsLocallyIntegral.comp_extDerivCLM`,
  `Distribution.IsIntegralCurrent.comp_extDerivCLM`,
  `Distribution.IsCompactlySupportedIntegralCurrent.comp_extDerivCLM`: boundary preservation.

## References

* H. Federer, *Geometric Measure Theory*, §4.1.24 (integral currents). Federer's `I_m(U)`, whose
  elements have compact support, corresponds to `Distribution.IsCompactlySupportedIntegralCurrent`
  and his `I_{m,loc}(U)` to `Distribution.IsLocallyIntegral`; `Distribution.IsIntegralCurrent`
  is the intermediate class of finite mass without the compact-support condition.
* H. Federer and W. H. Fleming, *Normal and integral currents*, Ann. of Math. **72** (1960),
  458–520.
* L. Simon, *Introduction to Geometric Measure Theory*, Chapter 6, §3.
-/

public section

noncomputable section

open Set TopologicalSpace TestFunction ContinuousLinearMap
open scoped Distributions

namespace Distribution

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {Ω : Opens V} {k : ℕ}

section Defs

/-- A `k`-current `T` on `Ω` is **locally integral** if `T` and its boundary `∂T = T ∘ d` are
both integer-rectifiable. The boundary of a `0`-current is zero, so in degree zero this is
integer-rectifiability of `T`. The local mass bounds are automatic
(`Distribution.IsIntegerRectifiable.hasLocallyFiniteMass`). -/
def IsLocallyIntegral : {k : ℕ} → (𝓓(Ω, V [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ) → Prop
  | 0, T => IsIntegerRectifiable T
  | _ + 1, T => IsIntegerRectifiable T ∧ IsIntegerRectifiable (T ∘L extDerivCLM)

/-- A `k`-current `T` on `Ω` is an **integral current** if it is locally integral and both `T` and
its boundary have finite mass. No support condition is imposed: Federer's integral currents
`I_m(U)` (*Geometric Measure Theory*, §4.1.24) are compactly supported and correspond to
`Distribution.IsCompactlySupportedIntegralCurrent`. -/
def IsIntegralCurrent (T : 𝓓(Ω, V [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ) : Prop :=
  IsLocallyIntegral T ∧ IsNormal T

/-- A `k`-current `T` on `Ω` is a **compactly supported integral current** if it is an integral
current whose support is a compact subset of `Ω`. -/
def IsCompactlySupportedIntegralCurrent (T : 𝓓(Ω, V [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ) : Prop :=
  IsIntegralCurrent T ∧ IsCompact (dsupport T) ∧ dsupport T ⊆ Ω

/-- In degree zero, local integrality is integer-rectifiability. -/
@[simp]
theorem isLocallyIntegral_finZero_iff {T : 𝓓(Ω, V [⋀^Fin 0]→L[ℝ] ℝ) →L[ℝ] ℝ} :
    IsLocallyIntegral T ↔ IsIntegerRectifiable T :=
  Iff.rfl

/-- In degree `k + 1`, local integrality is integer-rectifiability of `T` and `∂T`. -/
theorem isLocallyIntegral_succ_iff {T : 𝓓(Ω, V [⋀^Fin (k + 1)]→L[ℝ] ℝ) →L[ℝ] ℝ} :
    IsLocallyIntegral T ↔ IsIntegerRectifiable T ∧ IsIntegerRectifiable (T ∘L extDerivCLM) :=
  Iff.rfl

/-- Unfolding `Distribution.IsIntegralCurrent`. -/
theorem isIntegralCurrent_iff {T : 𝓓(Ω, V [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ} :
    IsIntegralCurrent T ↔ IsLocallyIntegral T ∧ IsNormal T :=
  Iff.rfl

/-- Unfolding `Distribution.IsCompactlySupportedIntegralCurrent`. -/
theorem isCompactlySupportedIntegralCurrent_iff {T : 𝓓(Ω, V [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ} :
    IsCompactlySupportedIntegralCurrent T ↔
      IsIntegralCurrent T ∧ IsCompact (dsupport T) ∧ dsupport T ⊆ Ω :=
  Iff.rfl

end Defs

section Inclusions

variable {T : 𝓓(Ω, V [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ}

/-- A locally integral current is integer-rectifiable. -/
theorem IsLocallyIntegral.isIntegerRectifiable (hT : IsLocallyIntegral T) :
    IsIntegerRectifiable T := by
  cases k
  exacts [hT, hT.1]

/-- **Locally integral currents are locally normal.** -/
theorem IsLocallyIntegral.isLocallyNormal (hT : IsLocallyIntegral T) : IsLocallyNormal T := by
  cases k with
  | zero => exact isLocallyNormal_finZero_iff.mpr (IsIntegerRectifiable.hasLocallyFiniteMass hT)
  | succ k =>
    exact isLocallyNormal_succ_iff.mpr ⟨hT.1.hasLocallyFiniteMass, hT.2.hasLocallyFiniteMass⟩

/-- **Integral currents are locally integral.** -/
theorem IsIntegralCurrent.isLocallyIntegral (hT : IsIntegralCurrent T) : IsLocallyIntegral T :=
  hT.1

/-- Integral currents are normal. -/
theorem IsIntegralCurrent.isNormal (hT : IsIntegralCurrent T) : IsNormal T :=
  hT.2

/-- **Compactly supported integral currents are integral currents.** -/
theorem IsCompactlySupportedIntegralCurrent.isIntegralCurrent
    (hT : IsCompactlySupportedIntegralCurrent T) : IsIntegralCurrent T :=
  hT.1

/-- Compactly supported integral currents are locally integral. -/
theorem IsCompactlySupportedIntegralCurrent.isLocallyIntegral
    (hT : IsCompactlySupportedIntegralCurrent T) : IsLocallyIntegral T :=
  hT.1.1

/-- Compactly supported integral currents are normal. -/
theorem IsCompactlySupportedIntegralCurrent.isNormal
    (hT : IsCompactlySupportedIntegralCurrent T) : IsNormal T :=
  hT.1.2

/-- The support of a compactly supported integral current is compact. -/
theorem IsCompactlySupportedIntegralCurrent.isCompact_dsupport
    (hT : IsCompactlySupportedIntegralCurrent T) : IsCompact (dsupport T) :=
  hT.2.1

/-- The support of a compactly supported integral current is contained in `Ω`. -/
theorem IsCompactlySupportedIntegralCurrent.dsupport_subset
    (hT : IsCompactlySupportedIntegralCurrent T) : dsupport T ⊆ Ω :=
  hT.2.2

/-- **A compactly supported locally integral current is a compactly supported integral current**:
its mass and the mass of its boundary are finite. -/
theorem IsLocallyIntegral.isCompactlySupportedIntegralCurrent (hT : IsLocallyIntegral T)
    (hc : IsCompact (dsupport T)) (hΩ : dsupport T ⊆ Ω) :
    IsCompactlySupportedIntegralCurrent T :=
  ⟨⟨hT, hT.isLocallyNormal.isNormal hc hΩ⟩, hc, hΩ⟩

/-- For a current whose support is a compact subset of `Ω`, being a compactly supported integral
current and being locally integral agree. -/
theorem isCompactlySupportedIntegralCurrent_iff_isLocallyIntegral_of_isCompact_dsupport
    (hc : IsCompact (dsupport T)) (hΩ : dsupport T ⊆ Ω) :
    IsCompactlySupportedIntegralCurrent T ↔ IsLocallyIntegral T :=
  ⟨IsCompactlySupportedIntegralCurrent.isLocallyIntegral,
    fun hT => hT.isCompactlySupportedIntegralCurrent hc hΩ⟩

end Inclusions

section Group

variable {T S : 𝓓(Ω, V [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ}

/-- The zero current is locally integral. -/
@[simp]
theorem isLocallyIntegral_zero : IsLocallyIntegral (0 : 𝓓(Ω, V [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ) := by
  cases k with
  | zero => exact isIntegerRectifiable_zero
  | succ k => exact ⟨isIntegerRectifiable_zero, by simpa using isIntegerRectifiable_zero⟩

/-- Locally integral currents are closed under addition. -/
theorem IsLocallyIntegral.add (hT : IsLocallyIntegral T) (hS : IsLocallyIntegral S) :
    IsLocallyIntegral (T + S) := by
  cases k with
  | zero => exact IsIntegerRectifiable.add hT hS
  | succ k => exact ⟨hT.1.add hS.1, by simpa [add_comp] using hT.2.add hS.2⟩

/-- Locally integral currents are closed under negation. -/
theorem IsLocallyIntegral.neg (hT : IsLocallyIntegral T) : IsLocallyIntegral (-T) := by
  cases k with
  | zero => exact IsIntegerRectifiable.neg hT
  | succ k => exact ⟨hT.1.neg, by simpa [neg_comp] using hT.2.neg⟩

/-- Locally integral currents are closed under subtraction. -/
theorem IsLocallyIntegral.sub (hT : IsLocallyIntegral T) (hS : IsLocallyIntegral S) :
    IsLocallyIntegral (T - S) := by
  simpa [sub_eq_add_neg] using hT.add hS.neg

/-- The zero current is an integral current. -/
@[simp]
theorem isIntegralCurrent_zero :
    IsIntegralCurrent (0 : 𝓓(Ω, V [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ⟨isLocallyIntegral_zero, isNormal_zero⟩

/-- Integral currents are closed under addition. -/
theorem IsIntegralCurrent.add (hT : IsIntegralCurrent T) (hS : IsIntegralCurrent S) :
    IsIntegralCurrent (T + S) :=
  ⟨hT.1.add hS.1, hT.2.add hS.2⟩

/-- Integral currents are closed under negation. -/
theorem IsIntegralCurrent.neg (hT : IsIntegralCurrent T) : IsIntegralCurrent (-T) :=
  ⟨hT.1.neg, hT.2.neg⟩

/-- Integral currents are closed under subtraction. -/
theorem IsIntegralCurrent.sub (hT : IsIntegralCurrent T) (hS : IsIntegralCurrent S) :
    IsIntegralCurrent (T - S) := by
  simpa [sub_eq_add_neg] using hT.add hS.neg

/-- The zero current is a compactly supported integral current. -/
@[simp]
theorem isCompactlySupportedIntegralCurrent_zero :
    IsCompactlySupportedIntegralCurrent (0 : 𝓓(Ω, V [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ⟨isIntegralCurrent_zero, by simp, by simp⟩

/-- Compactly supported integral currents are closed under addition. -/
theorem IsCompactlySupportedIntegralCurrent.add (hT : IsCompactlySupportedIntegralCurrent T)
    (hS : IsCompactlySupportedIntegralCurrent S) : IsCompactlySupportedIntegralCurrent (T + S) := by
  have hsub := dsupport_add_subset (T : 𝓓(Ω, V [⋀^Fin k]→L[ℝ] ℝ) → ℝ) S
  exact ⟨hT.isIntegralCurrent.add hS.isIntegralCurrent,
    (hT.isCompact_dsupport.union hS.isCompact_dsupport).of_isClosed_subset isClosed_dsupport hsub,
    hsub.trans (union_subset hT.dsupport_subset hS.dsupport_subset)⟩

/-- Compactly supported integral currents are closed under negation. -/
theorem IsCompactlySupportedIntegralCurrent.neg (hT : IsCompactlySupportedIntegralCurrent T) :
    IsCompactlySupportedIntegralCurrent (-T) := by
  have h : dsupport (⇑(-T)) = dsupport T := dsupport_neg _
  exact ⟨hT.isIntegralCurrent.neg, h ▸ hT.isCompact_dsupport, h ▸ hT.dsupport_subset⟩

/-- Compactly supported integral currents are closed under subtraction. -/
theorem IsCompactlySupportedIntegralCurrent.sub (hT : IsCompactlySupportedIntegralCurrent T)
    (hS : IsCompactlySupportedIntegralCurrent S) : IsCompactlySupportedIntegralCurrent (T - S) := by
  simpa [sub_eq_add_neg] using hT.add hS.neg

variable (Ω k)

/-- The **locally integral currents** of degree `k` on `Ω`, an additive subgroup of the real
`k`-currents. -/
def locallyIntegralCurrents : AddSubgroup (𝓓(Ω, V [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ) where
  carrier := {T | IsLocallyIntegral T}
  zero_mem' := isLocallyIntegral_zero
  add_mem' := IsLocallyIntegral.add
  neg_mem' := IsLocallyIntegral.neg

/-- The **integral currents** of degree `k` on `Ω`, an additive subgroup of the real
`k`-currents. -/
def integralCurrents : AddSubgroup (𝓓(Ω, V [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ) where
  carrier := {T | IsIntegralCurrent T}
  zero_mem' := isIntegralCurrent_zero
  add_mem' := IsIntegralCurrent.add
  neg_mem' := IsIntegralCurrent.neg

/-- The **compactly supported integral currents** of degree `k` on `Ω`, an additive subgroup of
the real `k`-currents. -/
def compactlySupportedIntegralCurrents : AddSubgroup (𝓓(Ω, V [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ) where
  carrier := {T | IsCompactlySupportedIntegralCurrent T}
  zero_mem' := isCompactlySupportedIntegralCurrent_zero
  add_mem' := IsCompactlySupportedIntegralCurrent.add
  neg_mem' := IsCompactlySupportedIntegralCurrent.neg

variable {Ω k}

@[simp]
theorem mem_locallyIntegralCurrents :
    T ∈ locallyIntegralCurrents Ω k ↔ IsLocallyIntegral T :=
  Iff.rfl

@[simp]
theorem mem_integralCurrents : T ∈ integralCurrents Ω k ↔ IsIntegralCurrent T :=
  Iff.rfl

@[simp]
theorem mem_compactlySupportedIntegralCurrents :
    T ∈ compactlySupportedIntegralCurrents Ω k ↔ IsCompactlySupportedIntegralCurrent T :=
  Iff.rfl

/-- Compactly supported integral currents are integral currents. -/
theorem compactlySupportedIntegralCurrents_le_integralCurrents :
    compactlySupportedIntegralCurrents Ω k ≤
      (integralCurrents Ω k : AddSubgroup (𝓓(Ω, V [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ)) :=
  fun _ hT ↦ IsCompactlySupportedIntegralCurrent.isIntegralCurrent hT

/-- Integral currents are locally integral. -/
theorem integralCurrents_le_locallyIntegralCurrents :
    integralCurrents Ω k ≤
      (locallyIntegralCurrents Ω k : AddSubgroup (𝓓(Ω, V [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ)) :=
  fun _ hT ↦ IsIntegralCurrent.isLocallyIntegral hT

/-- Locally integral currents are integer-rectifiable. -/
theorem locallyIntegralCurrents_le_integerRectifiableCurrents :
    locallyIntegralCurrents Ω k ≤ integerRectifiableCurrents Ω ⊤ k :=
  fun _ hT ↦ mem_integerRectifiableCurrents.mpr (IsLocallyIntegral.isIntegerRectifiable hT)

end Group

section Boundary

variable {T : 𝓓(Ω, V [⋀^Fin (k + 1)]→L[ℝ] ℝ) →L[ℝ] ℝ}

/-- **The boundary of a locally integral current is locally integral**, since `∂∂T = 0`. -/
theorem IsLocallyIntegral.comp_extDerivCLM (hT : IsLocallyIntegral T) :
    IsLocallyIntegral (T ∘L extDerivCLM) := by
  cases k
  · exact hT.2
  · refine ⟨hT.2, ?_⟩
    rw [comp_assoc, extDerivCLM_comp_extDerivCLM, comp_zero]
    exact isIntegerRectifiable_zero

/-- **The boundary of an integral current is an integral current.** -/
theorem IsIntegralCurrent.comp_extDerivCLM (hT : IsIntegralCurrent T) :
    IsIntegralCurrent (T ∘L extDerivCLM) :=
  ⟨hT.1.comp_extDerivCLM, hT.2.comp_extDerivCLM⟩

/-- **The boundary of a compactly supported integral current is a compactly supported integral
current**, its support being contained in that of the current. -/
theorem IsCompactlySupportedIntegralCurrent.comp_extDerivCLM
    (hT : IsCompactlySupportedIntegralCurrent T) :
    IsCompactlySupportedIntegralCurrent (T ∘L extDerivCLM) := by
  have hsub : dsupport (T ∘L extDerivCLM) ⊆ dsupport T := by
    rw [coe_comp]
    exact dsupport_comp_extDerivCLM_subset T
  exact ⟨hT.isIntegralCurrent.comp_extDerivCLM,
    hT.isCompact_dsupport.of_isClosed_subset isClosed_dsupport hsub, hsub.trans hT.dsupport_subset⟩

end Boundary

end Distribution

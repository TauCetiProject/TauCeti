/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import TauCeti.Analysis.Sobolev.BesselPotential.Inclusion

/-!
# Families of functions that are smooth in a Bessel-potential space

Let `f : X → E → G` be a family of functions on `E`, indexed by a real normed space `X` of
parameters. The family is *smooth in `H^{s,p}(E, G)` at `c₀`*
(`BesselPotentialSpace.IsSmoothFamilyAt`) when some family of elements of `H^{s,p}(E, G)`, `C^∞`
at `c₀`, has `Lᵖ` function almost everywhere `f c` for every `c` near `c₀`. Since an element of
`H^{s,p}`, `s ≥ 0`, is determined by its `Lᵖ` function, every family of elements representing `f`
near `c₀` is then `C^∞` at `c₀` (`BesselPotentialSpace.IsSmoothFamilyAt.contDiffAt`), and a family
that is smooth at every point is represented by one globally smooth family
(`BesselPotentialSpace.exists_contDiff_of_forall_isSmoothFamilyAt`).

This is the bookkeeping for proofs that a family of functions built pointwise from simpler ones,
such as the fields of plane vortices over a space of divisors, depends smoothly on its parameter
in a Sobolev space: sums, differences, products by smooth scalar functions of the parameter and
lowering of the order preserve the property.

## Main declarations

* `BesselPotentialSpace.IsSmoothFamilyAt`: the family `f c` is smooth in `H^{s,p}(E, G)` at `c₀`.
* `BesselPotentialSpace.IsSmoothFamilyAt.contDiffAt`: every family of elements of `H^{s,p}(E, G)`
  representing `f` near `c₀` is `C^∞` at `c₀`.
* `BesselPotentialSpace.exists_contDiff_of_forall_isSmoothFamilyAt`: a family that is smooth at
  every point is represented by a smooth family of elements of `H^{s,p}(E, G)`.
-/

public section

noncomputable section

open MeasureTheory Filter Topology
open scoped ContDiff ENNReal BesselPotentialSpace

namespace BesselPotentialSpace

variable {E G X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  {s t : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The family `f c` of functions on `E` is **smooth in `H^{s,p}(E, G)` at `c₀`**: some family of
elements of `H^{s,p}(E, G)`, `C^∞` at `c₀`, has `Lᵖ` function almost everywhere `f c` for every
`c` near `c₀`. -/
def IsSmoothFamilyAt (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hs : 0 ≤ s) (c₀ : X) (f : X → E → G) :
    Prop :=
  ∃ D : X → H^{s, p}(E, G), ContDiffAt ℝ ∞ D c₀ ∧
    ∀ᶠ c in 𝓝 c₀, ⇑(inclusionLp hs (D c)) =ᵐ[volume] f c

variable {hs : 0 ≤ s} {c₀ : X} {f g : X → E → G}

/-- Unfolds `IsSmoothFamilyAt` into a representing family that is `C^∞` at `c₀`. -/
theorem isSmoothFamilyAt_iff : IsSmoothFamilyAt s p hs c₀ f ↔ ∃ D : X → H^{s, p}(E, G),
    ContDiffAt ℝ ∞ D c₀ ∧ ∀ᶠ c in 𝓝 c₀, ⇑(inclusionLp hs (D c)) =ᵐ[volume] f c :=
  Iff.rfl

namespace IsSmoothFamilyAt

/-- A smooth family of elements of `H^{s,p}(E, G)` represents a family that is smooth at every
point. -/
theorem of_contDiff {D : X → H^{s, p}(E, G)} (hD : ContDiff ℝ ∞ D)
    (hDf : ∀ c, ⇑(inclusionLp hs (D c)) =ᵐ[volume] f c) : IsSmoothFamilyAt s p hs c₀ f :=
  ⟨D, hD.contDiffAt, .of_forall hDf⟩

/-- **Uniqueness of the representing family.** If `f` is smooth in `H^{s,p}(E, G)` at `c₀`, then
every family of elements of `H^{s,p}(E, G)` whose `Lᵖ` functions are `f c` near `c₀` is `C^∞` at
`c₀`. -/
theorem contDiffAt (hf : IsSmoothFamilyAt s p hs c₀ f) {D : X → H^{s, p}(E, G)}
    (hD : ∀ᶠ c in 𝓝 c₀, ⇑(inclusionLp hs (D c)) =ᵐ[volume] f c) : ContDiffAt ℝ ∞ D c₀ := by
  obtain ⟨D', hD', hD'f⟩ := hf
  refine hD'.congr_of_eventuallyEq ?_
  filter_upwards [hD, hD'f] with c h₁ h₂
  exact ext_of_ae_eq_inclusionLp hs (h₁.trans h₂.symm)

/-- Families that agree near `c₀` are smooth at `c₀` together. -/
theorem congr (hf : IsSmoothFamilyAt s p hs c₀ f) (h : ∀ᶠ c in 𝓝 c₀, f c = g c) :
    IsSmoothFamilyAt s p hs c₀ g := by
  obtain ⟨D, hD, hDf⟩ := hf
  refine ⟨D, hD, ?_⟩
  filter_upwards [hDf, h] with c h₁ h₂
  exact h₂ ▸ h₁

/-- Sums of families smooth at `c₀`. -/
theorem add (hf : IsSmoothFamilyAt s p hs c₀ f) (hg : IsSmoothFamilyAt s p hs c₀ g) :
    IsSmoothFamilyAt s p hs c₀ fun c x ↦ f c x + g c x := by
  obtain ⟨D, hD, hDf⟩ := hf
  obtain ⟨D', hD', hD'g⟩ := hg
  refine ⟨D + D', hD.add hD', ?_⟩
  filter_upwards [hDf, hD'g] with c h₁ h₂
  exact coeFn_inclusionLp_add_ae_eq hs h₁ h₂

/-- Differences of families smooth at `c₀`. -/
theorem sub (hf : IsSmoothFamilyAt s p hs c₀ f) (hg : IsSmoothFamilyAt s p hs c₀ g) :
    IsSmoothFamilyAt s p hs c₀ fun c x ↦ f c x - g c x := by
  obtain ⟨D, hD, hDf⟩ := hf
  obtain ⟨D', hD', hD'g⟩ := hg
  refine ⟨D - D', hD.sub hD', ?_⟩
  filter_upwards [hDf, hD'g] with c h₁ h₂
  exact coeFn_inclusionLp_sub_ae_eq hs h₁ h₂

/-- Products by a scalar function of the parameter that is `C^∞` at `c₀`. -/
theorem smul {γ : X → ℂ} (hγ : ContDiffAt ℝ ∞ γ c₀) (hf : IsSmoothFamilyAt s p hs c₀ f) :
    IsSmoothFamilyAt s p hs c₀ fun c x ↦ γ c • f c x := by
  obtain ⟨D, hD, hDf⟩ := hf
  refine ⟨fun c ↦ γ c • D c, hγ.smul hD, ?_⟩
  filter_upwards [hDf] with c h
  exact coeFn_inclusionLp_smul_ae_eq hs _ h

/-- Lowering the order. -/
theorem mono {ht : 0 ≤ t} (hf : IsSmoothFamilyAt t p ht c₀ f) (hst : s ≤ t) :
    IsSmoothFamilyAt s p hs c₀ f := by
  obtain ⟨D, hD, hDf⟩ := hf
  refine ⟨fun c ↦ inclusion hst (D c),
    ((inclusion hst).restrictScalars ℝ).contDiff.contDiffAt.comp c₀ hD, ?_⟩
  filter_upwards [hDf] with c h
  rwa [inclusionLp_inclusion]

end IsSmoothFamilyAt

/-- The zero family is smooth everywhere. -/
theorem isSmoothFamilyAt_zero : IsSmoothFamilyAt s p hs c₀ fun (_ : X) (_ : E) ↦ (0 : G) :=
  .of_contDiff (D := 0) contDiff_const fun _ ↦ by
    rw [Pi.zero_apply, map_zero]
    exact Lp.coeFn_zero G p volume

/-- Finite sums of families smooth at `c₀`. -/
theorem IsSmoothFamilyAt.sum {ι : Type*} (u : Finset ι) {f : ι → X → E → G}
    (hf : ∀ a ∈ u, IsSmoothFamilyAt s p hs c₀ (f a)) :
    IsSmoothFamilyAt s p hs c₀ fun c x ↦ ∑ a ∈ u, f a c x := by
  classical
  induction u using Finset.induction_on with
  | empty => simpa using isSmoothFamilyAt_zero
  | insert a u ha ih =>
    simp_rw [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a u)).add
      (ih fun b hb ↦ hf b (Finset.mem_insert_of_mem hb))

/-- **Smooth at every point.** A family that is smooth in `H^{s,p}(E, G)` at every point is
represented by one smooth family of elements of `H^{s,p}(E, G)`. -/
theorem exists_contDiff_of_forall_isSmoothFamilyAt {f : X → E → G}
    (h : ∀ c₀, IsSmoothFamilyAt s p hs c₀ f) :
    ∃ D : X → H^{s, p}(E, G), ContDiff ℝ ∞ D ∧ ∀ c, ⇑(inclusionLp hs (D c)) =ᵐ[volume] f c := by
  choose D hD hDf using h
  have hf (c : X) : ⇑(inclusionLp hs (D c c)) =ᵐ[volume] f c := (hDf c).self_of_nhds
  exact ⟨fun c ↦ D c c, contDiff_iff_contDiffAt.2 fun c₀ ↦
    IsSmoothFamilyAt.contDiffAt ⟨D c₀, hD c₀, hDf c₀⟩ (.of_forall hf), hf⟩

end BesselPotentialSpace

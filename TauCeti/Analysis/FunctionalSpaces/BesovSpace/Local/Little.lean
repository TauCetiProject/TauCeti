/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.LocalRegularity
public import TauCeti.Analysis.FunctionalSpaces.BesovSpace.ChangeOfVariables
public import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Little
public import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Local
import TauCeti.Analysis.Distribution.ChangeOfVariables.Tempered
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.Analysis.Distribution.TestFunction.Schwartz
import TauCeti.Analysis.Distribution.TestFunction.SmulLeft

/-!
# Local little Besov regularity of distributions

The little Besov space `b^s_{p,∞}` is the closure of the Schwartz functions in the Besov space
`B^s_{p,∞}` (`TemperedDistribution.MemLittleBesov`); for `p < ∞` it consists of the elements of
`B^s_{p,∞}` whose weighted Littlewood–Paley blocks `2^{js} ‖Δⱼ u‖_p` tend to zero. This file makes
membership in it a local notion, as `Distribution.IsLocallyMemBesovAt` does for `B^s_{p,q}`, so
that it can be read chart by chart on manifolds.

* **Pullback.** The pullback `Φ^*` along a bijection `Φ` of `E` with bounded derivatives preserves
  `b^s_{p,∞}` (`TemperedDistribution.MemLittleBesov.compCLM`): it is bounded on `B^s_{p,∞}` and
  sends Schwartz functions to Schwartz functions, hence preserves their closure.
* **Local regularity.** A complex distribution `T` on an open set `Ω ⊆ E` is **`b^s_{p,∞}` near
  `x`** (`Distribution.IsLocallyMemLittleBesovAt`) when `x` has a neighbourhood `U ⊆ Ω` such that
  `ψ T ∈ b^s_{p,∞}` for every test function `ψ` supported in `U`. It does not depend on the bump
  function, it can be tested with a single cutoff not vanishing at `x`
  (`Distribution.isLocallyMemLittleBesovAt_iff_exists_ne_zero_memLittleBesov_cutoffTempered`), and
  regularity near every point of the support of `χ` gives `χ T ∈ b^s_{p,∞}`
  (`Distribution.memLittleBesov_cutoffTempered_of_forall_isLocallyMemLittleBesovAt`).
* **Invariance.** Being `b^s_{p,∞}` near a point is an invariant notion of local regularity
  (`Distribution.isInvariantLocalRegularity_isLocallyMemLittleBesovAt`): it is preserved by smooth
  multiples, restriction and pullback along smooth changes of variables
  (`Distribution.isLocallyMemLittleBesovAt_compCLMOfOpenPartialHomeomorph_iff`).

Local `b^s_{p,∞}` regularity implies local `B^s_{p,∞}` regularity
(`Distribution.IsLocallyMemLittleBesovAt.isLocallyMemBesovAt`), and for `p < ∞` it follows from
local `B^s_{p,q}` regularity with `q < ∞`
(`Distribution.IsLocallyMemBesovAt.isLocallyMemLittleBesovAt_of_ne_top`).

## References

* H. Triebel, *Theory of Function Spaces*, Birkhäuser, 1983, §2.4.7 (localization of Besov
  spaces), §2.10.2 (diffeomorphisms preserve the Besov spaces) and §3.2.2 (Besov spaces on
  manifolds, defined chart by chart).
* H. Bahouri, J.-Y. Chemin and R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Springer, 2011, §2.7 (the closure of the Schwartz functions in `B^s_{p,∞}`).
-/

public section

noncomputable section

open MeasureTheory Filter Set TopologicalSpace TemperedDistribution
open scoped ENNReal Topology SchwartzMap Distributions ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

namespace TemperedDistribution

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  {φ : ContDiffBump (0 : E)} {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **Pullback of little Besov distributions.** If `u ∈ b^s_{p,∞}` and `Φ` is a bijection such
that `Φ` and `Φ⁻¹` have temperate growth, with bounded derivatives of `Φ` of orders `1` to
`⌊|s|⌋₊ + 1` and of `Φ⁻¹` of orders `1` to `⌊|s|⌋₊ + 2`, then `Φ^* u ∈ b^s_{p,∞}`. -/
theorem MemLittleBesov.compCLM {u : 𝓢'(E, F)} (hu : u.MemLittleBesov φ s p) {Φ : E ≃ E}
    (hΦ : (Φ : E → E).HasTemperateGrowth) (hΨ : (Φ.symm : E → E).HasTemperateGrowth)
    (hΦb : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 1 → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n Φ x‖ ≤ C)
    (hΨb : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 2 → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n Φ.symm x‖ ≤ C) :
    (compCLM F Φ hΦ hΨ u).MemLittleBesov φ s p := by
  have hv := hu.memBesov.toBesovSpace_mem_littleBesov_iff.2 hu
  -- The bounded pullback on `B^s_{p,∞}` sends the Schwartz function `f` to `f ∘ Φ`.
  have hw := TauCeti.BesovSpace.map_mem_littleBesov_of_toBesovSpaceCLM
    (TauCeti.BesovSpace.compCLM F φ s p ∞ Φ hΦ hΨ hΦb hΨb) (fun f ↦ ?_) hv
  · rwa [← TauCeti.BesovSpace.memLittleBesov_toDistr_iff, TauCeti.BesovSpace.toDistr_compCLM,
      MemBesov.toDistr_toBesovSpace] at hw
  rw [← TauCeti.BesovSpace.memLittleBesov_toDistr_iff, TauCeti.BesovSpace.toDistr_compCLM,
    SchwartzMap.toDistr_toBesovSpaceCLM]
  exact (compCLM_toTemperedDistributionCLM volume hΦ hΨ f).symm ▸
    SchwartzMap.memLittleBesov φ s p _

/-- **Pullback invariance of `MemLittleBesov`.** If `Φ` and `Φ⁻¹` have temperate growth and
bounded derivatives of orders `1` to `⌊|s|⌋₊ + 2`, a tempered distribution `u` lies in
`b^s_{p,∞}` if and only if its pullback `Φ^* u` does. -/
theorem memLittleBesov_compCLM_iff {u : 𝓢'(E, F)} {Φ : E ≃ E}
    (hΦ : (Φ : E → E).HasTemperateGrowth) (hΨ : (Φ.symm : E → E).HasTemperateGrowth)
    (hΦb : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 2 → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n Φ x‖ ≤ C)
    (hΨb : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 2 → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n Φ.symm x‖ ≤ C) :
    (compCLM F Φ hΦ hΨ u).MemLittleBesov φ s p ↔ u.MemLittleBesov φ s p := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.compCLM hΦ hΨ (fun n h₁ h₂ ↦ hΦb n h₁ (by omega)) hΨb⟩
  simpa only [compCLM_symm_compCLM hΦ hΨ hΦ] using
    h.compCLM hΨ hΦ (fun n h₁ h₂ ↦ hΨb n h₁ (by omega)) hΦb

/-- Multiplying a tempered distribution in `b^s_{p,∞}` by a test function keeps it in
`b^s_{p,∞}`. -/
theorem MemLittleBesov.smulLeftCLM_testFunction {Ω : Opens E} {u : 𝓢'(E, F)}
    (hu : u.MemLittleBesov φ s p) (ψ : 𝓓(Ω, ℂ)) :
    (TemperedDistribution.smulLeftCLM F (ψ : E → ℂ) u).MemLittleBesov φ s p := by
  simpa [TestFunction.coe_toSchwartzMapCLM] using
    hu.smulLeftCLM (g := TestFunction.toSchwartzMapCLM ℂ ψ) (SchwartzMap.hasTemperateGrowth _)
      fun k _ ↦ ⟨_, SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ _ k⟩

end TemperedDistribution

namespace Distribution

variable {Ω : Opens E} (φ : ContDiffBump (0 : E)) {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A complex distribution `T` on `Ω` is **`b^s_{p,∞}` near `x`**, for the little Besov space
built from the Littlewood–Paley partition of `φ`, if `x` has a neighbourhood `U ⊆ Ω` such that the
cut-off distribution `ψ T` lies in `b^s_{p,∞}` for every test function `ψ` supported in `U`. -/
def IsLocallyMemLittleBesovAt (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (T : 𝓓'(Ω, ℂ)) (x : E) : Prop :=
  ∃ U ∈ 𝓝 x, U ⊆ Ω ∧ ∀ ψ : 𝓓(Ω, ℂ), tsupport ψ ⊆ U → (T.cutoffTempered ψ).MemLittleBesov φ s p

variable {φ} {s : ℝ} {T : 𝓓'(Ω, ℂ)} {x : E}

/-- Unfolds `IsLocallyMemLittleBesovAt` into its neighbourhood and the regularity of the cut-off
distributions. -/
theorem isLocallyMemLittleBesovAt_iff : T.IsLocallyMemLittleBesovAt φ s p x ↔ ∃ U ∈ 𝓝 x,
    U ⊆ Ω ∧ ∀ ψ : 𝓓(Ω, ℂ), tsupport ψ ⊆ U → (T.cutoffTempered ψ).MemLittleBesov φ s p :=
  Iff.rfl

/-- A distribution can only be `b^s_{p,∞}` near points of its domain. -/
theorem IsLocallyMemLittleBesovAt.mem (h : T.IsLocallyMemLittleBesovAt φ s p x) : x ∈ Ω :=
  let ⟨_, hU, hUΩ, _⟩ := h
  hUΩ (mem_of_mem_nhds hU)

/-- **Monotonicity.** Being `b^s_{p,∞}` near a point implies being `b^{s'}_{p,∞}` there for
`s' ≤ s`. -/
theorem IsLocallyMemLittleBesovAt.mono (h : T.IsLocallyMemLittleBesovAt φ s p x) {s' : ℝ}
    (hs : s' ≤ s) : T.IsLocallyMemLittleBesovAt φ s' p x :=
  let ⟨U, hU, hUΩ, hT⟩ := h
  ⟨U, hU, hUΩ, fun ψ hψ ↦ (hT ψ hψ).mono hs⟩

/-- **Independence of the bump function.** A distribution `b^s_{p,∞}` near `x` for the
Littlewood–Paley partition of `φ` is `b^s_{p,∞}` near `x` for that of any other bump function. -/
theorem IsLocallyMemLittleBesovAt.of_bump (h : T.IsLocallyMemLittleBesovAt φ s p x)
    (φ' : ContDiffBump (0 : E)) : T.IsLocallyMemLittleBesovAt φ' s p x :=
  let ⟨U, hU, hUΩ, hT⟩ := h
  ⟨U, hU, hUΩ, fun ψ hψ ↦ (hT ψ hψ).of_bump φ'⟩

/-- A distribution `b^s_{p,∞}` near `x` is `B^s_{p,∞}` near `x`. -/
theorem IsLocallyMemLittleBesovAt.isLocallyMemBesovAt (h : T.IsLocallyMemLittleBesovAt φ s p x) :
    T.IsLocallyMemBesovAt φ s p ∞ x :=
  let ⟨U, hU, hUΩ, hT⟩ := h
  isLocallyMemBesovAt_iff.2 ⟨U, hU, hUΩ, fun ψ hψ ↦ (hT ψ hψ).memBesov⟩

/-- For `p < ∞`, a distribution `B^s_{p,q}` near `x` with `q < ∞` is `b^s_{p,∞}` near `x`. -/
theorem IsLocallyMemBesovAt.isLocallyMemLittleBesovAt_of_ne_top {q : ℝ≥0∞}
    (h : T.IsLocallyMemBesovAt φ s p q x) (hp : p ≠ (∞ : ℝ≥0∞)) (hq : q ≠ (∞ : ℝ≥0∞)) :
    T.IsLocallyMemLittleBesovAt φ s p x :=
  let ⟨U, hU, hUΩ, hT⟩ := isLocallyMemBesovAt_iff.1 h
  ⟨U, hU, hUΩ, fun ψ hψ ↦ (hT ψ hψ).memLittleBesov_of_ne_top hp hq⟩

variable (φ) in
/-- The set of points near which a distribution is `b^s_{p,∞}` is open. -/
theorem isOpen_setOf_isLocallyMemLittleBesovAt (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (T : 𝓓'(Ω, ℂ)) : IsOpen {x : E | T.IsLocallyMemLittleBesovAt φ s p x} := by
  refine isOpen_iff_mem_nhds.2 fun x ⟨U, hU, hUΩ, hT⟩ ↦ ?_
  filter_upwards [eventually_mem_nhds_iff.2 hU] with y hy using ⟨U, hy, hUΩ, hT⟩

/-- The zero distribution is `b^s_{p,∞}` near every point of its domain. -/
@[simp]
theorem isLocallyMemLittleBesovAt_zero_iff :
    (0 : 𝓓'(Ω, ℂ)).IsLocallyMemLittleBesovAt φ s p x ↔ x ∈ Ω := by
  refine ⟨IsLocallyMemLittleBesovAt.mem, fun hx ↦
    ⟨Ω, Ω.isOpen.mem_nhds hx, subset_rfl, fun ψ _ ↦ ?_⟩⟩
  rw [cutoffTempered_zero]
  exact MemLittleBesov.zero

/-- A scalar multiple of a distribution `b^s_{p,∞}` near `x` is `b^s_{p,∞}` near `x`. -/
theorem IsLocallyMemLittleBesovAt.smul (h : T.IsLocallyMemLittleBesovAt φ s p x) (c : ℂ) :
    (c • T).IsLocallyMemLittleBesovAt φ s p x :=
  let ⟨U, hU, hUΩ, hT⟩ := h
  ⟨U, hU, hUΩ, fun ψ hψ ↦ by simpa using (hT ψ hψ).smul c⟩

/-- The sum of two distributions `b^s_{p,∞}` near `x` is `b^s_{p,∞}` near `x`. -/
theorem IsLocallyMemLittleBesovAt.add {S : 𝓓'(Ω, ℂ)} (hS : S.IsLocallyMemLittleBesovAt φ s p x)
    (hT : T.IsLocallyMemLittleBesovAt φ s p x) : (S + T).IsLocallyMemLittleBesovAt φ s p x :=
  let ⟨U, hU, hUΩ, hSU⟩ := hS
  let ⟨V, hV, _, hTV⟩ := hT
  ⟨U ∩ V, inter_mem hU hV, inter_subset_left.trans hUΩ, fun ψ hψ ↦ by
    simpa using (hSU ψ (hψ.trans inter_subset_left)).add (hTV ψ (hψ.trans inter_subset_right))⟩

/-- At a point of an open subset `Ω' ≤ Ω`, the restriction `T|_{Ω'}` is `b^s_{p,∞}` near `x`
exactly when `T` is. -/
theorem isLocallyMemLittleBesovAt_restrictCLM_iff {Ω' : Opens E} (h : Ω' ≤ Ω) (hx : x ∈ Ω') :
    (restrictCLM T : 𝓓'(Ω', ℂ)).IsLocallyMemLittleBesovAt φ s p x ↔
      T.IsLocallyMemLittleBesovAt φ s p x := by
  constructor
  · rintro ⟨U, hU, hUΩ', hT⟩
    refine ⟨U, hU, hUΩ'.trans h, fun ψ hψ ↦ ?_⟩
    obtain ⟨ψ', rfl⟩ := TestFunction.exists_monoCLM_eq_of_tsupport_subset h (hψ.trans hUΩ')
    rw [← cutoffTempered_restrictCLM]
    exact hT ψ' (by rwa [TestFunction.coe_monoCLM_of_le le_rfl h] at hψ)
  · rintro ⟨U, hU, -, hT⟩
    refine ⟨U ∩ Ω', inter_mem hU (Ω'.isOpen.mem_nhds hx), inter_subset_right, fun ψ hψ ↦ ?_⟩
    rw [cutoffTempered_restrictCLM]
    exact hT _ (by rw [TestFunction.coe_monoCLM_of_le le_rfl h]; exact hψ.trans inter_subset_left)

/-- A smooth multiple `g T` of a distribution `b^s_{p,∞}` near `x` is `b^s_{p,∞}` near `x`. -/
theorem IsLocallyMemLittleBesovAt.smulLeftCLM (h : T.IsLocallyMemLittleBesovAt φ s p x)
    {g : E → ℝ} (hg : ContDiff ℝ ∞ g) :
    (Distribution.smulLeftCLM hg T).IsLocallyMemLittleBesovAt φ s p x :=
  let ⟨U, hU, hUΩ, hT⟩ := h
  ⟨U, hU, hUΩ, fun ψ hψ ↦ by
    rw [cutoffTempered_smulLeftCLM]
    exact hT _ ((TestFunction.tsupport_smulLeftCLM_subset hg ψ).trans
      (inter_subset_right.trans hψ))⟩

/-- **Testing with one cutoff.** A distribution is `b^s_{p,∞}` near `x` exactly when `χ T` lies in
`b^s_{p,∞}` for some test function `χ` equal to one near `x`. -/
theorem isLocallyMemLittleBesovAt_iff_exists_memLittleBesov_cutoffTempered :
    T.IsLocallyMemLittleBesovAt φ s p x ↔
      ∃ χ : 𝓓(Ω, ℂ), (∀ᶠ y in 𝓝 x, χ y = 1) ∧ (T.cutoffTempered χ).MemLittleBesov φ s p := by
  refine ⟨fun ⟨U, hU, hUΩ, hT⟩ ↦ ?_, fun ⟨χ, hχ, hT⟩ ↦ ?_⟩
  · obtain ⟨χ, hχ1, hχU⟩ := TestFunction.exists_complex_cutoff_tsupport_subset (n := ⊤)
      isCompact_singleton isOpen_interior
      (singleton_subset_iff.2 (mem_interior_iff_mem_nhds.2 hU)) (interior_subset.trans hUΩ)
    exact ⟨χ, by rwa [nhdsSet_singleton] at hχ1, hT χ (hχU.trans interior_subset)⟩
  · -- On the set where `χ = 1`, every cut-off distribution `ψ T` is the smooth multiple `ψ (χ T)`.
    have hxΩ : x ∈ Ω := χ.tsupport_subset (subset_tsupport _ (by simp [hχ.self_of_nhds]))
    refine ⟨{y | χ y = 1} ∩ Ω, inter_mem hχ (Ω.isOpen.mem_nhds hxΩ), inter_subset_right,
      fun ψ hψ ↦ ?_⟩
    rw [← smulLeftCLM_cutoffTempered T fun y hy ↦ (hψ hy).1]
    exact hT.smulLeftCLM_testFunction ψ

/-- **Testing with one nonvanishing cutoff.** A distribution is `b^s_{p,∞}` near `x` exactly when
`χ T` lies in `b^s_{p,∞}` for some test function `χ` with `χ x ≠ 0`. -/
theorem isLocallyMemLittleBesovAt_iff_exists_ne_zero_memLittleBesov_cutoffTempered :
    T.IsLocallyMemLittleBesovAt φ s p x ↔
      ∃ χ : 𝓓(Ω, ℂ), χ x ≠ 0 ∧ (T.cutoffTempered χ).MemLittleBesov φ s p := by
  refine ⟨fun h ↦ ?_, fun ⟨χ, hχx, hT⟩ ↦ ?_⟩
  · obtain ⟨χ, hχ, hT⟩ := isLocallyMemLittleBesovAt_iff_exists_memLittleBesov_cutoffTempered.1 h
    exact ⟨χ, by simp [hχ.self_of_nhds], hT⟩
  -- A cutoff `ρ` equal to one near `x` is a test-function multiple `h χ`, so `ρ T = h (χ T)`.
  obtain ⟨ρ, h, hρ1, hhχ⟩ := TestFunction.exists_eventually_eq_one_and_mul_eq hχx
  refine isLocallyMemLittleBesovAt_iff_exists_memLittleBesov_cutoffTempered.2 ⟨ρ, hρ1, ?_⟩
  rw [← smulLeftCLM_cutoffTempered_of_mul_eq T
    (h.hasCompactSupport.hasTemperateGrowth h.contDiff) hhχ]
  exact hT.smulLeftCLM_testFunction h

/-- A tempered distribution in `b^s_{p,∞}` is `b^s_{p,∞}` near every point, as a distribution on
`Ω`. -/
theorem _root_.TemperedDistribution.MemLittleBesov.isLocallyMemLittleBesovAt_toDistribution
    {u : 𝓢'(E, ℂ)} (hu : u.MemLittleBesov φ s p) (hx : x ∈ Ω) :
    (toDistribution Ω u).IsLocallyMemLittleBesovAt φ s p x := by
  refine ⟨Ω, Ω.isOpen.mem_nhds hx, subset_rfl, fun ψ _ ↦ ?_⟩
  rw [cutoffTempered_toDistribution]
  exact hu.smulLeftCLM_testFunction ψ

/-- **From local to global regularity.** If `T` is `b^s_{p,∞}` near every point of the support of
a test function `χ`, then `χ T ∈ b^s_{p,∞}`. -/
theorem memLittleBesov_cutoffTempered_of_forall_isLocallyMemLittleBesovAt {χ : 𝓓(Ω, ℂ)}
    (h : ∀ x ∈ tsupport χ, T.IsLocallyMemLittleBesovAt φ s p x) :
    (T.cutoffTempered χ).MemLittleBesov φ s p :=
  cutoffTempered_induction (fun u : 𝓢'(E, ℂ) ↦ u.MemLittleBesov φ s p) MemLittleBesov.zero
    (fun _ _ ↦ MemLittleBesov.add) fun x hx ↦ (h x hx).imp fun _ hU ↦ ⟨hU.1, hU.2.2⟩

/-! ### Changes of variables -/

section ChangeOfVariables

variable {e : OpenPartialHomeomorph E E} {U Ω' : Opens E}
  {he : ContDiffOn ℝ (⊤ : ℕ∞) e e.source} {he' : ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target}
  {hU : (U : Set E) ⊆ e.source} {hUΩ : MapsTo e U Ω'}

variable (φ p) in
/-- Being `b^s_{p,∞}` near a point is a notion of local regularity: it is open and linear. -/
theorem isLocalRegularity_isLocallyMemLittleBesovAt (s : ℝ) :
    IsLocalRegularity fun (Ω : Opens E) (T : 𝓓'(Ω, ℂ)) x ↦ T.IsLocallyMemLittleBesovAt φ s p x where
  isOpen_setOf _ T := isOpen_setOf_isLocallyMemLittleBesovAt φ s p T
  zero hx := isLocallyMemLittleBesovAt_zero_iff.2 hx
  add hS hT := hS.add hT
  smul c hT := hT.smul c

/-- **Pulling back preserves local little Besov regularity.** If `T` is `b^s_{p,∞}` near `e x`,
then its pullback `e^* T` along `e` is `b^s_{p,∞}` near `x`. -/
theorem IsLocallyMemLittleBesovAt.compCLMOfOpenPartialHomeomorph {T : 𝓓'(Ω', ℂ)} (hx : x ∈ U)
    (hT : T.IsLocallyMemLittleBesovAt φ s p (e x)) :
    (compCLMOfOpenPartialHomeomorph e he he' hU hUΩ T).IsLocallyMemLittleBesovAt φ s p x := by
  -- `ψ T ∈ b^s_{p,∞}` for every test function `ψ` supported in a neighbourhood `W` of `e x`.
  obtain ⟨W, hW, -, hWT⟩ := isLocallyMemLittleBesovAt_iff.1 hT
  obtain ⟨Φ, hΦ, hΨ, N, hNU, χ, hΦb, hΨb, hxN, hχW, hT⟩ :=
    exists_restrictCLM_compCLMOfOpenPartialHomeomorph_eq_toDistribution he he' hU hUΩ hx hW T
  rw [← isLocallyMemLittleBesovAt_restrictCLM_iff hNU hxN, hT]
  exact ((hWT χ hχW).compCLM hΦ hΨ (fun n hn _ ↦ hΦb n hn) (fun n hn _ ↦ hΨb n hn))
    |>.isLocallyMemLittleBesovAt_toDistribution hxN

variable (φ p) in
/-- Being `b^s_{p,∞}` near a point is an invariant notion of local regularity: it is open, linear,
preserved by smooth multiples and pullback along smooth changes of variables, and unchanged by
restriction to smaller open sets. -/
theorem isInvariantLocalRegularity_isLocallyMemLittleBesovAt (s : ℝ) :
    IsInvariantLocalRegularity
      fun (Ω : Opens E) (T : 𝓓'(Ω, ℂ)) x ↦ T.IsLocallyMemLittleBesovAt φ s p x where
  toIsLocalRegularity := isLocalRegularity_isLocallyMemLittleBesovAt φ p s
  smulLeftCLM hg hT := hT.smulLeftCLM hg
  restrictCLM_iff h _ _ hx := isLocallyMemLittleBesovAt_restrictCLM_iff h hx
  compCLMOfOpenPartialHomeomorph _ _ _ _ _ _ hx hT := hT.compCLMOfOpenPartialHomeomorph hx

/-- **Local little Besov regularity is invariant under changes of variables.** The pullback `e^* T`
of a distribution `T` along `e` is `b^s_{p,∞}` near a point `x ∈ U` exactly when `T` is
`b^s_{p,∞}` near `e x`. -/
theorem isLocallyMemLittleBesovAt_compCLMOfOpenPartialHomeomorph_iff {T : 𝓓'(Ω', ℂ)}
    (hx : x ∈ U) :
    (compCLMOfOpenPartialHomeomorph e he he' hU hUΩ T).IsLocallyMemLittleBesovAt φ s p x ↔
      T.IsLocallyMemLittleBesovAt φ s p (e x) :=
  (isInvariantLocalRegularity_isLocallyMemLittleBesovAt φ p s).compCLMOfOpenPartialHomeomorph_iff
    hx

end ChangeOfVariables

end Distribution

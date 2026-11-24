/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.TemperedDistribution.Cutoff
public import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Basic
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.Analysis.Distribution.TestFunction.Schwartz
import TauCeti.Analysis.Distribution.TestFunction.SmulLeft
import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Multiplication
import TauCeti.Analysis.Sobolev.BesselPotential.Besov
import TauCeti.Analysis.Sobolev.BesselPotential.Local

/-!
# Local Besov regularity of distributions

Let `T` be a complex distribution on an open subset `Ω` of a finite-dimensional real inner product
space `E`, and let `φ` be the bump function of a Littlewood–Paley partition. This file measures the
regularity of `T` near a point on the inhomogeneous Besov scale `B^s_{p,q}(E)`: `T` is `B^s_{p,q}`
near `x` (`Distribution.IsLocallyMemBesovAt φ s p q T x`) when, for some neighbourhood `U ⊆ Ω` of
`x`, every cut-off distribution `ψ T` with `ψ` a test function supported in `U` lies in
`B^s_{p,q}`. Here `ψ T` is the tempered distribution `Distribution.cutoffTempered T ψ`. For
`p = q = ∞` this is local membership in the Hölder–Zygmund space `𝒞^s = B^s_{∞,∞}`, the scale on
which local Schauder regularity is stated; at positive non-integer orders `k + α` the space `𝒞^s`
is the bounded Hölder space `C^{k,α}` (`TauCeti.BesovSpace.ckHolderSpaceEquiv`).

The notion does not depend on the bump function (`Distribution.IsLocallyMemBesovAt.of_bump`), and
it can be tested with a single cutoff equal to one near `x`
(`Distribution.isLocallyMemBesovAt_iff_exists_memBesov_cutoffTempered`), since smooth multipliers
preserve the Besov spaces (`TemperedDistribution.MemBesov.smulLeftCLM`). If `T` is `B^s_{p,q}` near
every point of the support of a test function `ψ`, then `ψ T ∈ B^s_{p,q}`
(`Distribution.memBesov_cutoffTempered_of_forall_isLocallyMemBesovAt`). The notion is local: it
is unchanged by restricting `T` to a smaller open set containing `x`
(`Distribution.isLocallyMemBesovAt_restrictCLM_iff`), and a tempered distribution in `B^s_{p,q}`
is `B^s_{p,q}` near every point
(`TemperedDistribution.MemBesov.isLocallyMemBesovAt_toDistribution`).

Every distribution has finite order on this scale: for `1 < p ≤ ∞` and `q ≠ 0`, every cut-off
distribution `ψ T` lies in some `B^s_{p,q}` (`Distribution.exists_memBesov_cutoffTempered`). This is
the starting point of elliptic regularity on the Besov scale, whose parametrix argument improves a
distribution already known to lie in some `B^r_{p,q}`. For `1 < p < ∞` it follows from the finite
order of `ψ T` on the Bessel-potential scale `H^{s,p}`
(`Distribution.exists_memSobolev_cutoffTempered_of_one_lt`) and `H^{s,p} ⊆ B^s_{p,∞}`; for
`p = ∞` from the finite `L²` Sobolev order of `ψ T` and the Bernstein embedding
`B^s_{2,∞} ⊆ B^{s - n/2}_{∞,∞}`. Hence, for `1 < p` and `1 ≤ q`, every distribution is
`B^s_{p,q}` near each point of `Ω` for some `s` (`Distribution.exists_isLocallyMemBesovAt`).

## References

* M. E. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, September 2008,
  Lecture I, (3.32)–(3.34) (the Zygmund spaces).
* H. Triebel, *Theory of Function Spaces*, Birkhäuser, 1983, §2.4.7 (localization of Besov
  spaces).
-/

public section

noncomputable section

open MeasureTheory Filter Set TopologicalSpace TemperedDistribution
open scoped ENNReal Topology SchwartzMap Distributions ContDiff

namespace Distribution

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {Ω : Opens E} (φ : ContDiffBump (0 : E)) {p q : ℝ≥0∞}
  [Fact (1 ≤ p)]

/-- A complex distribution `T` on `Ω` is **`B^s_{p,q}` near `x`**, for the Besov spaces built from
the Littlewood–Paley partition of `φ`, if `x` has a neighbourhood `U ⊆ Ω` such that the cut-off
distribution `ψ T` lies in `B^s_{p,q}` for every test function `ψ` supported in `U`. For
`p = q = ∞` this is membership of `T` in the local Hölder–Zygmund space `𝒞^s_loc` near `x`. -/
def IsLocallyMemBesovAt (s : ℝ) (p q : ℝ≥0∞) [Fact (1 ≤ p)] (T : 𝓓'(Ω, ℂ)) (x : E) : Prop :=
  ∃ U ∈ 𝓝 x, U ⊆ Ω ∧ ∀ ψ : 𝓓(Ω, ℂ), tsupport ψ ⊆ U → (T.cutoffTempered ψ).MemBesov φ s p q

variable {φ} {s : ℝ} {T : 𝓓'(Ω, ℂ)} {x : E}

/-- Unfolds `IsLocallyMemBesovAt` into its neighbourhood and the regularity of the cut-off
distributions. -/
theorem isLocallyMemBesovAt_iff : T.IsLocallyMemBesovAt φ s p q x ↔ ∃ U ∈ 𝓝 x, U ⊆ Ω ∧
    ∀ ψ : 𝓓(Ω, ℂ), tsupport ψ ⊆ U → (T.cutoffTempered ψ).MemBesov φ s p q :=
  Iff.rfl

/-- A distribution can only be `B^s_{p,q}` near points of its domain. -/
theorem IsLocallyMemBesovAt.mem (h : T.IsLocallyMemBesovAt φ s p q x) : x ∈ Ω :=
  let ⟨_, hU, hUΩ, _⟩ := h
  hUΩ (mem_of_mem_nhds hU)

/-- **Monotonicity.** Being `B^s_{p,q}` near a point implies being `B^{s'}_{p,q'}` there for
`s' ≤ s` and `q ≤ q'`. -/
theorem IsLocallyMemBesovAt.mono (h : T.IsLocallyMemBesovAt φ s p q x) {s' : ℝ} {q' : ℝ≥0∞}
    (hs : s' ≤ s) (hq : q ≤ q') : T.IsLocallyMemBesovAt φ s' p q' x :=
  let ⟨U, hU, hUΩ, hT⟩ := h
  ⟨U, hU, hUΩ, fun ψ hψ ↦ (hT ψ hψ).mono hs hq⟩

/-- **Independence of the bump function.** A distribution `B^s_{p,q}` near `x` for the
Littlewood–Paley partition of `φ` is `B^s_{p,q}` near `x` for that of any other bump function. -/
theorem IsLocallyMemBesovAt.of_bump (h : T.IsLocallyMemBesovAt φ s p q x)
    (φ' : ContDiffBump (0 : E)) : T.IsLocallyMemBesovAt φ' s p q x :=
  let ⟨U, hU, hUΩ, hT⟩ := h
  ⟨U, hU, hUΩ, fun ψ hψ ↦ (hT ψ hψ).of_bump φ'⟩

variable (φ) in
/-- The set of points near which a distribution is `B^s_{p,q}` is open. -/
theorem isOpen_setOf_isLocallyMemBesovAt (s : ℝ) (p q : ℝ≥0∞) [Fact (1 ≤ p)] (T : 𝓓'(Ω, ℂ)) :
    IsOpen {x : E | T.IsLocallyMemBesovAt φ s p q x} := by
  refine isOpen_iff_mem_nhds.2 fun x ⟨U, hU, hUΩ, hT⟩ ↦ ?_
  filter_upwards [eventually_mem_nhds_iff.2 hU] with y hy using ⟨U, hy, hUΩ, hT⟩

/-- The zero distribution is `B^s_{p,q}` near every point of its domain. -/
@[simp]
theorem isLocallyMemBesovAt_zero_iff :
    (0 : 𝓓'(Ω, ℂ)).IsLocallyMemBesovAt φ s p q x ↔ x ∈ Ω := by
  refine ⟨IsLocallyMemBesovAt.mem, fun hx ↦ ⟨Ω, Ω.isOpen.mem_nhds hx, subset_rfl, fun ψ _ ↦ ?_⟩⟩
  rw [cutoffTempered_zero]
  exact MemBesov.zero

/-- A scalar multiple of a distribution `B^s_{p,q}` near `x` is `B^s_{p,q}` near `x`. -/
theorem IsLocallyMemBesovAt.smul (h : T.IsLocallyMemBesovAt φ s p q x) (c : ℂ) :
    (c • T).IsLocallyMemBesovAt φ s p q x :=
  let ⟨U, hU, hUΩ, hT⟩ := h
  ⟨U, hU, hUΩ, fun ψ hψ ↦ by simpa using (hT ψ hψ).smul c⟩

/-- A nonzero scalar multiple of `T` is `B^s_{p,q}` near `x` exactly when `T` is. -/
theorem isLocallyMemBesovAt_smul_iff {c : ℂ} (hc : c ≠ 0) :
    (c • T).IsLocallyMemBesovAt φ s p q x ↔ T.IsLocallyMemBesovAt φ s p q x :=
  ⟨fun h ↦ by simpa [smul_smul, inv_mul_cancel₀ hc] using h.smul c⁻¹, fun h ↦ h.smul c⟩

/-- The negative of `T` is `B^s_{p,q}` near `x` exactly when `T` is. -/
@[simp]
theorem isLocallyMemBesovAt_neg_iff :
    (-T).IsLocallyMemBesovAt φ s p q x ↔ T.IsLocallyMemBesovAt φ s p q x := by
  rw [← neg_one_smul ℂ T, isLocallyMemBesovAt_smul_iff (neg_ne_zero.2 one_ne_zero)]

/-- The sum of two distributions `B^s_{p,q}` near `x` is `B^s_{p,q}` near `x`. -/
theorem IsLocallyMemBesovAt.add {S : 𝓓'(Ω, ℂ)} (hS : S.IsLocallyMemBesovAt φ s p q x)
    (hT : T.IsLocallyMemBesovAt φ s p q x) : (S + T).IsLocallyMemBesovAt φ s p q x :=
  let ⟨U, hU, hUΩ, hSU⟩ := hS
  let ⟨V, hV, _, hTV⟩ := hT
  ⟨U ∩ V, inter_mem hU hV, inter_subset_left.trans hUΩ, fun ψ hψ ↦ by
    simpa using (hSU ψ (hψ.trans inter_subset_left)).add (hTV ψ (hψ.trans inter_subset_right))⟩

/-- The difference of two distributions `B^s_{p,q}` near `x` is `B^s_{p,q}` near `x`. -/
theorem IsLocallyMemBesovAt.sub {S : 𝓓'(Ω, ℂ)} (hS : S.IsLocallyMemBesovAt φ s p q x)
    (hT : T.IsLocallyMemBesovAt φ s p q x) : (S - T).IsLocallyMemBesovAt φ s p q x := by
  rw [sub_eq_add_neg]
  exact hS.add (isLocallyMemBesovAt_neg_iff.2 hT)

/-- A finite sum of distributions `B^s_{p,q}` near a point `x` of `Ω` is `B^s_{p,q}` near `x`. -/
theorem IsLocallyMemBesovAt.sum {ι : Type*} {t : Finset ι} {T : ι → 𝓓'(Ω, ℂ)} (hx : x ∈ Ω)
    (h : ∀ i ∈ t, (T i).IsLocallyMemBesovAt φ s p q x) :
    (∑ i ∈ t, T i).IsLocallyMemBesovAt φ s p q x :=
  Finset.sum_induction _ (fun S : 𝓓'(Ω, ℂ) ↦ S.IsLocallyMemBesovAt φ s p q x) (fun _ _ ↦ .add)
    (isLocallyMemBesovAt_zero_iff.2 hx) h

/-- At a point of an open subset `Ω' ≤ Ω`, the restriction `T|_{Ω'}` is `B^s_{p,q}` near `x`
exactly when `T` is. -/
theorem isLocallyMemBesovAt_restrictCLM_iff {Ω' : Opens E} (h : Ω' ≤ Ω) (hx : x ∈ Ω') :
    (restrictCLM T : 𝓓'(Ω', ℂ)).IsLocallyMemBesovAt φ s p q x ↔
      T.IsLocallyMemBesovAt φ s p q x := by
  -- Extending a test function on `Ω'` by zero does not change it as a function on `E`.
  have hmono (ψ : 𝓓(Ω', ℂ)) : ⇑(TestFunction.monoCLM ℝ ψ : 𝓓(Ω, ℂ)) = ψ := by
    ext y
    simp [h]
  constructor
  · rintro ⟨U, hU, hUΩ', hT⟩
    refine ⟨U, hU, hUΩ'.trans h, fun ψ hψ ↦ ?_⟩
    obtain ⟨ψ', rfl⟩ := TestFunction.exists_monoCLM_eq_of_tsupport_subset h (hψ.trans hUΩ')
    rw [← cutoffTempered_restrictCLM h]
    exact hT ψ' (by rwa [hmono] at hψ)
  · rintro ⟨U, hU, -, hT⟩
    refine ⟨U ∩ Ω', inter_mem hU (Ω'.isOpen.mem_nhds hx), inter_subset_right, fun ψ hψ ↦ ?_⟩
    rw [cutoffTempered_restrictCLM h]
    exact hT _ (by rw [hmono]; exact hψ.trans inter_subset_left)

/-- A smooth multiple `g T` of a distribution `B^s_{p,q}` near `x` is `B^s_{p,q}` near `x`. -/
theorem IsLocallyMemBesovAt.smulLeftCLM (h : T.IsLocallyMemBesovAt φ s p q x) {g : E → ℝ}
    (hg : ContDiff ℝ ∞ g) : (Distribution.smulLeftCLM hg T).IsLocallyMemBesovAt φ s p q x :=
  let ⟨U, hU, hUΩ, hT⟩ := h
  ⟨U, hU, hUΩ, fun ψ hψ ↦ by
    rw [cutoffTempered_smulLeftCLM]
    exact hT _ ((TestFunction.tsupport_smulLeftCLM_subset hg ψ).trans
      (inter_subset_right.trans hψ))⟩

/-- **Testing with one cutoff.** A distribution is `B^s_{p,q}` near `x` exactly when `χ T` lies in
`B^s_{p,q}` for some test function `χ` equal to one near `x`. -/
theorem isLocallyMemBesovAt_iff_exists_memBesov_cutoffTempered [Fact (1 ≤ q)] :
    T.IsLocallyMemBesovAt φ s p q x ↔
      ∃ χ : 𝓓(Ω, ℂ), (∀ᶠ y in 𝓝 x, χ y = 1) ∧ (T.cutoffTempered χ).MemBesov φ s p q := by
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
    simpa [TestFunction.coe_toSchwartzMapCLM] using
      hT.smulLeftCLM (g := TestFunction.toSchwartzMapCLM ℂ ψ)
        (SchwartzMap.hasTemperateGrowth _)
        fun k _ ↦ ⟨_, SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ _ k⟩

/-- A tempered distribution in `B^s_{p,q}` is `B^s_{p,q}` near every point, as a distribution on
`Ω`. -/
theorem _root_.TemperedDistribution.MemBesov.isLocallyMemBesovAt_toDistribution [Fact (1 ≤ q)]
    {u : 𝓢'(E, ℂ)} (hu : u.MemBesov φ s p q) (hx : x ∈ Ω) :
    (toDistribution Ω u).IsLocallyMemBesovAt φ s p q x := by
  refine ⟨Ω, Ω.isOpen.mem_nhds hx, subset_rfl, fun ψ _ ↦ ?_⟩
  rw [cutoffTempered_toDistribution]
  simpa [TestFunction.coe_toSchwartzMapCLM] using
    hu.smulLeftCLM (g := TestFunction.toSchwartzMapCLM ℂ ψ) (SchwartzMap.hasTemperateGrowth _)
      fun k _ ↦ ⟨_, SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ _ k⟩

/-- **From local to global regularity.** If `T` is `B^s_{p,q}` near every point of the support of
a test function `χ`, then `χ T ∈ B^s_{p,q}`. -/
theorem memBesov_cutoffTempered_of_forall_isLocallyMemBesovAt {χ : 𝓓(Ω, ℂ)}
    (h : ∀ x ∈ tsupport χ, T.IsLocallyMemBesovAt φ s p q x) :
    (T.cutoffTempered χ).MemBesov φ s p q := by
  -- Each point of `tsupport χ` has a neighbourhood on which every cutoff gives a `B^s_{p,q}`
  -- product.
  choose U hU _ hUs using fun x : tsupport χ ↦ h x x.property
  -- Split `χ` into finitely many test functions supported in these neighbourhoods.
  obtain ⟨t, ψ, hψU, hψχ, -⟩ := χ.exists_sum_subordinate (fun x ↦ interior (U x))
    (fun _ ↦ isOpen_interior) fun x hx ↦
      mem_iUnion.2 ⟨⟨x, hx⟩, mem_interior_iff_mem_nhds.2 (hU ⟨x, hx⟩)⟩
  rw [← hψχ, cutoffTempered_sum_cutoff]
  exact Finset.sum_induction _ (fun u : 𝓢'(E, ℂ) ↦ u.MemBesov φ s p q)
    (fun _ _ ↦ MemBesov.add) MemBesov.zero fun i _ ↦ hUs i _ ((hψU i).trans interior_subset)

variable (φ) in
/-- **Finite order on the Besov scale.** Let `1 < p ≤ ∞` and `q ≠ 0`. Every cut-off distribution
`χ T` lies in the Besov space `B^s_{p,q}` for some real order `s`. -/
theorem exists_memBesov_cutoffTempered (hp : 1 < p) (hq : q ≠ 0) (T : 𝓓'(Ω, ℂ))
    (χ : 𝓓(Ω, ℂ)) : ∃ s : ℝ, (T.cutoffTempered χ).MemBesov φ s p q := by
  obtain ⟨s, hs⟩ : ∃ s : ℝ, (T.cutoffTempered χ).MemBesov φ s p ∞ := by
    rcases eq_or_ne p ∞ with rfl | hp_top
    · obtain ⟨r, hr⟩ := T.exists_memSobolev_cutoffTempered χ
      exact ⟨_, (hr.memBesov φ).mono_exponent le_top⟩
    · obtain ⟨r, hr⟩ := exists_memSobolev_cutoffTempered_of_one_lt hp hp_top T χ
      exact ⟨r, hr.memBesov φ⟩
  exact ⟨s - 1, hs.of_lt (by linarith) hq⟩

variable (φ) in
/-- **Finite local order on the Besov scale.** Let `1 < p ≤ ∞` and `1 ≤ q`. Every distribution
on `Ω` is `B^s_{p,q}` near each point of `Ω` for some real order `s`. -/
theorem exists_isLocallyMemBesovAt [Fact (1 ≤ q)] (hp : 1 < p) (T : 𝓓'(Ω, ℂ)) (hx : x ∈ Ω) :
    ∃ s : ℝ, T.IsLocallyMemBesovAt φ s p q x := by
  obtain ⟨χ, hχ1, -⟩ := TestFunction.exists_complex_cutoff_tsupport_subset (n := ⊤)
    isCompact_singleton Ω.isOpen (singleton_subset_iff.2 hx) subset_rfl
  have hq : q ≠ 0 := (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ q)).ne'
  obtain ⟨s, hs⟩ := exists_memBesov_cutoffTempered φ hp hq T χ
  exact ⟨s, isLocallyMemBesovAt_iff_exists_memBesov_cutoffTempered.2
    ⟨χ, by rwa [nhdsSet_singleton] at hχ1, hs⟩⟩

end Distribution

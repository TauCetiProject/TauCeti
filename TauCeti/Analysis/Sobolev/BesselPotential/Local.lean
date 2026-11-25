/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.LocalRegularity
public import TauCeti.Analysis.Distribution.WaveFrontSet.Sobolev.Tempered
import TauCeti.Analysis.Distribution.ChangeOfVariables.Tempered
import TauCeti.Analysis.Distribution.Sobolev
import TauCeti.Analysis.Distribution.TestFunction.Schwartz
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.Analysis.Distribution.TestFunction.SmulLeft
import TauCeti.Analysis.Sobolev.BesselPotential.Besov
import TauCeti.Analysis.Sobolev.BesselPotential.ChangeOfVariables
import TauCeti.Analysis.Sobolev.BesselPotential.Embedding
import TauCeti.Analysis.Sobolev.BesselPotential.MatrixMultiplier

/-!
# Local `H^{s,p}` regularity of distributions

Let `T` be a complex distribution on an open subset `Ω` of a finite-dimensional real inner product
space `E`. This file measures the regularity of `T` near a point on the `Lᵖ` scale of Mathlib's
Bessel-potential spaces `H^{s,p}(E)`: `T` is `H^{s,p}` near `x`
(`Distribution.IsLocallyMemSobolevAt s p T x`) when, for some neighbourhood `U ⊆ Ω` of `x`, every
cut-off distribution `φ T` with `φ` a test function supported in `U` lies in `H^{s,p}`. Here
`φ T` is the tempered distribution `Distribution.cutoffTempered T φ`. This is the local space
`H^{s,p}_loc` in which elliptic regularity on the `Lᵖ` scale is stated.

For `p = 2` the notion agrees with the Fourier description `Distribution.IsLocallySobolevAt` used
for the `H^s` wave front set (`Distribution.isLocallyMemSobolevAt_two_iff`).

Smooth multiples preserve the notion (`Distribution.IsLocallyMemSobolevAt.smulLeftCLM`), and for
`1 < p < ∞` each derivative costs one order (`Distribution.IsLocallyMemSobolevAt.lineDerivOp`,
`Distribution.IsLocallyMemSobolevAt.iteratedLineDerivOp`). Hence a differential operator of order
at most `k` maps `H^{s,p}_loc` to `H^{s - k,p}_loc`
(`Distribution.IsLocallyMemSobolevAt.sum_smul_smulLeftCLM_iteratedLineDerivOp`).

For `1 < p < ∞` the notion is invariant under smooth changes of variables: if `e` is a smooth open
partial homeomorphism of `E` with smooth inverse, the pullback `e^* T`
(`Distribution.compCLMOfOpenPartialHomeomorph`) is `H^{s,p}` near `x` exactly when `T` is
`H^{s,p}` near `e x` (`Distribution.isLocallyMemSobolevAt_compCLMOfOpenPartialHomeomorph_iff`).
Near `x`, `e^* T` is the tempered pullback `Φ^* (χ T)` along a bijection `Φ` of `E` whose
derivatives are bounded, for a cutoff `χ` supported near `e x`
(`Distribution.exists_restrictCLM_compCLMOfOpenPartialHomeomorph_eq_toDistribution`), and `Φ^*`
preserves `H^{s,p}` (`TemperedDistribution.MemSobolev.compCLM_of_norm_iteratedFDeriv_le_natCeil`).
Since chart transitions are such maps `e`, this is the invariance needed to define `H^{s,p}_loc` on
a manifold chart by chart. The restriction to an open subset `Ω' ≤ Ω` is `H^{s,p}` near a point of
`Ω'` exactly when `T` is (`Distribution.isLocallyMemSobolevAt_restrictCLM_iff`). Being `H^{s,p}`
near a point is thus an invariant notion of local regularity
(`Distribution.isInvariantLocalRegularity_isLocallyMemSobolevAt`), and the converse direction of
the change of variables comes from the general argument
(`Distribution.IsInvariantLocalRegularity.compCLMOfOpenPartialHomeomorph_iff`).

Every distribution has finite order on this scale: for `1 < p < ∞`, every
cut-off distribution `φ T` lies in some `H^{s,p}`
(`Distribution.exists_memSobolev_cutoffTempered_of_one_lt`), and for a compact `K ⊆ Ω` there is an
`s` with `T` being `H^{s,p}` near every point of `K`
(`Distribution.exists_forall_isLocallyMemSobolevAt`). This is the starting point of elliptic
regularity on the `Lᵖ` scale, whose parametrix argument improves a distribution already known to
lie in some `H^{r,p}`. It rests on a whole-space statement about Schwartz multiples of
distributions of finite `L²` order:

* `TemperedDistribution.MemSobolev.memSobolev_neg_two_mul_smulLeftCLM`: if `f ∈ H^s = H^{s,2}`
  and `n < 2 (s + 2k)`, where `n = dim E`, then `ψ f ∈ H^{-2k,p}` for every Schwartz function
  `ψ` and every `1 < p < ∞`.

## Finite order

Write `J^r` for the Bessel potential `TemperedDistribution.besselPotential` of order `r`. The
distribution `v = J^{-2k} f` lies in `H^{s + 2k}` with `2 (s + 2k) > n`, so by the Sobolev
embedding it is an `L²` function agreeing almost everywhere with a bounded continuous function
(`TemperedDistribution.MemSobolev.exists_zeroAtInftyContinuousMap_ae_eq`). Hence `ψ v` lies in
every `Lᵖ` for every Schwartz function `ψ`: Hölder's inequality pairs `ψ ∈ Lᵖ` with `v ∈ L^∞`.

Then `f = J^{2k} v = (J²)^k v`, with `J² = 1 - (2π)⁻² Δ`
(`TemperedDistribution.besselPotential_two_eq_sub_laplacian`). The Leibniz rule
`ψ ∂_w g = ∂_w (ψ g) - (∂_w ψ) g` shows that if every Schwartz multiple of `g` lies in `H^{r,p}`,
then every Schwartz multiple of `∂_w g` lies in `H^{r - 1,p}`, since `∂_w` maps `H^{r,p}` to
`H^{r - 1,p}` for `1 < p < ∞` (`TemperedDistribution.memSobolev_smulLeftCLM_lineDerivOp`). Each
factor `J²` therefore costs two orders
(`TemperedDistribution.memSobolev_smulLeftCLM_besselPotential_two`), and `k` of them give the order
`-2k`.

## References

* M. E. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, September 2008,
  Lecture II (the spaces `H^{s,p}` and elliptic regularity on them).
* M. E. Taylor, *Partial Differential Equations I*, 2nd ed., Springer, 2011, Chapter 4, §1
  (invariance of `H^s` under diffeomorphisms, and the local Sobolev spaces on manifolds).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Springer, 1985,
  Appendix B.1 (`H^s_loc` is invariant under diffeomorphisms).
-/

public section

noncomputable section

open MeasureTheory Filter Set TopologicalSpace TestFunction Module LineDeriv
open scoped ENNReal Topology SchwartzMap Distributions LineDeriv

namespace TemperedDistribution

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **Schwartz multiples of distributions of finite `L²` order lie in `H^{-2k,p}`.** Let
`1 < p < ∞`. If `f ∈ H^s = H^{s,2}` and `n < 2 (s + 2k)`, where `n = dim E`, then `ψ f ∈ H^{-2k,p}`
for every Schwartz function `ψ`. -/
theorem MemSobolev.memSobolev_neg_two_mul_smulLeftCLM (hp : 1 < p) (hp_top : p ≠ ∞) {s : ℝ}
    {k : ℕ} (hk : finrank ℝ E < 2 * (s + 2 * k)) {f : 𝓢'(E, F)} (hf : MemSobolev s 2 f)
    (ψ : 𝓢(E, ℂ)) : MemSobolev (-(2 * k)) p (smulLeftCLM F (ψ : E → ℂ) f) := by
  -- `v = J^{-2k} f` lies in `H^{s + 2k}` with `2 (s + 2k) > n`, so it is an `L²` function with a
  -- bounded continuous representative.
  set v := besselPotential E F (-(2 * k)) f
  have hv : MemSobolev (s + 2 * k) 2 v := by
    rw [memSobolev_besselPotential_iff, show -(2 * k : ℝ) + (s + 2 * k) = s by ring]
    exact hf
  have hs : (0 : ℝ) ≤ s + 2 * k := by
    have : (0 : ℝ) ≤ finrank ℝ E := Nat.cast_nonneg _
    linarith
  obtain ⟨u, hu⟩ := memSobolev_zero_iff.1 (hv.mono hs)
  obtain ⟨g, hg⟩ := MemSobolev.exists_zeroAtInftyContinuousMap_ae_eq hk (hu ▸ hv)
  have hgb : MemLp (g : E → F) ∞ volume := g.toBCF.memLp_top
  -- Each factor `J²` of `f = (J²)^k v` costs two orders.
  have key (j : ℕ) (ψ : 𝓢(E, ℂ)) :
      MemSobolev (-(2 * j)) p (smulLeftCLM F (ψ : E → ℂ) (besselPotential E F (2 * j) v)) := by
    induction j generalizing ψ with
    | zero =>
      simpa [besselPotential_zero, hu] using memSobolev_zero_smulLeftCLM_of_ae_eq hgb hg ψ
    | succ j ih =>
      have h := memSobolev_smulLeftCLM_besselPotential_two hp hp_top ih ψ
      rwa [besselPotential_besselPotential_apply,
        show 2 * (j : ℝ) + 2 = 2 * ((j + 1 : ℕ) : ℝ) by push_cast; ring,
        show -(2 * (j : ℝ)) - 2 = -(2 * ((j + 1 : ℕ) : ℝ)) by push_cast; ring] at h
  have hfv : besselPotential E F (2 * k) v = f := by
    rw [besselPotential_besselPotential_apply, neg_add_cancel, besselPotential_zero,
      ContinuousLinearMap.id_apply]
  simpa [hfv] using key k ψ

end TemperedDistribution

namespace Distribution

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {Ω : Opens E} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A complex distribution `T` on `Ω` is **`H^{s,p}` near `x`** if `x` has a neighbourhood
`U ⊆ Ω` such that the cut-off distribution `φ T` lies in the Bessel-potential space `H^{s,p}` for
every test function `φ` supported in `U`. This is membership of `T` in `H^{s,p}_loc` near `x`. -/
def IsLocallyMemSobolevAt (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (T : 𝓓'(Ω, ℂ)) (x : E) : Prop :=
  ∃ U ∈ 𝓝 x, U ⊆ Ω ∧
    ∀ φ : 𝓓(Ω, ℂ), tsupport φ ⊆ U → TemperedDistribution.MemSobolev s p (T.cutoffTempered φ)

variable {s : ℝ} {T : 𝓓'(Ω, ℂ)} {x : E}

/-- Unfolds `IsLocallyMemSobolevAt` into its neighbourhood and the regularity of the cut-off
distributions. -/
theorem isLocallyMemSobolevAt_iff : T.IsLocallyMemSobolevAt s p x ↔ ∃ U ∈ 𝓝 x, U ⊆ Ω ∧
    ∀ φ : 𝓓(Ω, ℂ), tsupport φ ⊆ U → TemperedDistribution.MemSobolev s p (T.cutoffTempered φ) :=
  Iff.rfl

/-- A distribution can only be `H^{s,p}` near points of its domain. -/
theorem IsLocallyMemSobolevAt.mem (h : T.IsLocallyMemSobolevAt s p x) : x ∈ Ω :=
  let ⟨_, hU, hUΩ, _⟩ := h
  hUΩ (mem_of_mem_nhds hU)

/-- Being `H^{s,p}` near a point is inherited by lower orders. -/
theorem IsLocallyMemSobolevAt.of_le (h : T.IsLocallyMemSobolevAt s p x) {s' : ℝ}
    (hs : s' ≤ s) : T.IsLocallyMemSobolevAt s' p x :=
  let ⟨U, hU, hUΩ, hT⟩ := h
  ⟨U, hU, hUΩ, fun φ hφ ↦ (hT φ hφ).of_le hs⟩

/-- The set of points near which a distribution is `H^{s,p}` is open. -/
theorem isOpen_setOf_isLocallyMemSobolevAt (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (T : 𝓓'(Ω, ℂ)) :
    IsOpen {x : E | T.IsLocallyMemSobolevAt s p x} := by
  refine isOpen_iff_mem_nhds.2 fun x ⟨U, hU, hUΩ, hT⟩ ↦ ?_
  filter_upwards [eventually_mem_nhds_iff.2 hU] with y hy using ⟨U, hy, hUΩ, hT⟩

/-- The zero distribution is `H^{s,p}` near every point of its domain. -/
@[simp]
theorem isLocallyMemSobolevAt_zero_iff :
    (0 : 𝓓'(Ω, ℂ)).IsLocallyMemSobolevAt s p x ↔ x ∈ Ω := by
  refine ⟨IsLocallyMemSobolevAt.mem, fun hx ↦ ⟨Ω, Ω.isOpen.mem_nhds hx, subset_rfl, fun φ _ ↦ ?_⟩⟩
  rw [cutoffTempered_zero]
  exact TemperedDistribution.memSobolev_fun_zero E ℂ s p

/-- A scalar multiple of a distribution `H^{s,p}` near `x` is `H^{s,p}` near `x`. -/
theorem IsLocallyMemSobolevAt.smul (h : T.IsLocallyMemSobolevAt s p x) (c : ℂ) :
    (c • T).IsLocallyMemSobolevAt s p x :=
  let ⟨U, hU, hUΩ, hT⟩ := h
  ⟨U, hU, hUΩ, fun φ hφ ↦ by simpa using (hT φ hφ).smul c⟩

/-- A nonzero scalar multiple of `T` is `H^{s,p}` near `x` exactly when `T` is. -/
theorem isLocallyMemSobolevAt_smul_iff {c : ℂ} (hc : c ≠ 0) :
    (c • T).IsLocallyMemSobolevAt s p x ↔ T.IsLocallyMemSobolevAt s p x :=
  ⟨fun h ↦ by simpa [smul_smul, inv_mul_cancel₀ hc] using h.smul c⁻¹, fun h ↦ h.smul c⟩

/-- The negative of `T` is `H^{s,p}` near `x` exactly when `T` is. -/
@[simp]
theorem isLocallyMemSobolevAt_neg_iff :
    (-T).IsLocallyMemSobolevAt s p x ↔ T.IsLocallyMemSobolevAt s p x := by
  rw [← neg_one_smul ℂ T, isLocallyMemSobolevAt_smul_iff (neg_ne_zero.2 one_ne_zero)]

/-- The sum of two distributions `H^{s,p}` near `x` is `H^{s,p}` near `x`. -/
theorem IsLocallyMemSobolevAt.add {S : 𝓓'(Ω, ℂ)} (hS : S.IsLocallyMemSobolevAt s p x)
    (hT : T.IsLocallyMemSobolevAt s p x) : (S + T).IsLocallyMemSobolevAt s p x :=
  let ⟨U, hU, hUΩ, hSU⟩ := hS
  let ⟨V, hV, _, hTV⟩ := hT
  ⟨U ∩ V, inter_mem hU hV, inter_subset_left.trans hUΩ, fun φ hφ ↦ by
    simpa using (hSU φ (hφ.trans inter_subset_left)).add (hTV φ (hφ.trans inter_subset_right))⟩

/-- The difference of two distributions `H^{s,p}` near `x` is `H^{s,p}` near `x`. -/
theorem IsLocallyMemSobolevAt.sub {S : 𝓓'(Ω, ℂ)} (hS : S.IsLocallyMemSobolevAt s p x)
    (hT : T.IsLocallyMemSobolevAt s p x) : (S - T).IsLocallyMemSobolevAt s p x := by
  rw [sub_eq_add_neg]
  exact hS.add (isLocallyMemSobolevAt_neg_iff.2 hT)

section Operations

open scoped ContDiff

/-- A smooth multiple `g T` of a distribution `H^{s,p}` near `x` is `H^{s,p}` near `x`. -/
theorem IsLocallyMemSobolevAt.smulLeftCLM (h : T.IsLocallyMemSobolevAt s p x) {g : E → ℝ}
    (hg : ContDiff ℝ ∞ g) : (Distribution.smulLeftCLM hg T).IsLocallyMemSobolevAt s p x :=
  let ⟨U, hU, hUΩ, hT⟩ := h
  ⟨U, hU, hUΩ, fun φ hφ ↦ by
    rw [cutoffTempered_smulLeftCLM]
    exact hT _ ((TestFunction.tsupport_smulLeftCLM_subset hg φ).trans
      (inter_subset_right.trans hφ))⟩

/-- For `1 < p < ∞`, a derivative `∂_v T` of a distribution `H^{s,p}` near `x` is `H^{s - 1,p}`
near `x`, by the Leibniz rule `φ ∂_v T = ∂_v (φ T) - (∂_v φ) T`. -/
theorem IsLocallyMemSobolevAt.lineDerivOp (hp : 1 < p) (hp_top : p ≠ (∞ : ℝ≥0∞))
    (h : T.IsLocallyMemSobolevAt s p x) (v : E) : (∂_{v} T).IsLocallyMemSobolevAt (s - 1) p x :=
  let ⟨U, hU, hUΩ, hT⟩ := h
  ⟨U, hU, hUΩ, fun φ hφ ↦ by
    rw [eq_sub_of_add_eq' (lineDerivOp_cutoffTempered T φ v).symm]
    exact ((hT φ hφ).lineDerivOp_of_one_lt hp hp_top).sub
      ((hT _ ((TestFunction.tsupport_lineDerivOp_subset φ v).trans hφ)).mono_of_one_lt hp
        hp_top (by linarith))⟩

/-- For `1 < p < ∞`, an iterated derivative `∂^m T` of order `n` of a distribution `H^{s,p}` near
`x` is `H^{s - n,p}` near `x`. -/
theorem IsLocallyMemSobolevAt.iteratedLineDerivOp (hp : 1 < p) (hp_top : p ≠ (∞ : ℝ≥0∞))
    (h : T.IsLocallyMemSobolevAt s p x) {n : ℕ} (m : Fin n → E) :
    (∂^{m} T).IsLocallyMemSobolevAt (s - n) p x := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    rw [iteratedLineDerivOp_succ_left, Nat.cast_succ, ← sub_sub]
    exact (ih _).lineDerivOp hp hp_top _

/-- **Differential operators map `H^{s,p}_loc` to `H^{s - k,p}_loc`.** Let `1 < p < ∞`. If `T` is
`H^{s,p}` near `x`, then `P T = ∑ i ∈ t, c i • g i ∂^(m i) T`, with smooth real coefficients and
orders `n i ≤ k`, is `H^{s - k,p}` near `x`. -/
theorem IsLocallyMemSobolevAt.sum_smul_smulLeftCLM_iteratedLineDerivOp (hp : 1 < p)
    (hp_top : p ≠ (∞ : ℝ≥0∞)) (h : T.IsLocallyMemSobolevAt s p x) {ι : Type*} (t : Finset ι)
    (c : ι → ℂ) {g : ι → E → ℝ} (hg : ∀ i, ContDiff ℝ ∞ (g i)) {n : ι → ℕ}
    (m : ∀ i, Fin (n i) → E) {k : ℕ} (hk : ∀ i ∈ t, n i ≤ k) :
    (∑ i ∈ t, c i • Distribution.smulLeftCLM (hg i) (∂^{m i} T)).IsLocallyMemSobolevAt (s - k) p
      x :=
  Finset.sum_induction _ (fun S : 𝓓'(Ω, ℂ) ↦ S.IsLocallyMemSobolevAt (s - k) p x)
    (fun _ _ ↦ IsLocallyMemSobolevAt.add) (isLocallyMemSobolevAt_zero_iff.2 h.mem)
    fun i hi ↦ (((h.iteratedLineDerivOp hp hp_top (m i)).of_le
      (by gcongr; exact hk i hi)).smulLeftCLM (hg i)).smul (c i)

end Operations

/-- For `p = 2`, being `H^{s,2}` near `x` is the Fourier description
`Distribution.IsLocallySobolevAt` of being `H^s` near `x`. -/
theorem isLocallyMemSobolevAt_two_iff :
    T.IsLocallyMemSobolevAt s 2 x ↔ T.IsLocallySobolevAt s x := by
  refine ⟨fun ⟨U, hU, hUΩ, hT⟩ ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨φ, hφU, hφx⟩ :=
      TestFunction.exists_tsupport_subset_apply_eq (n := ⊤) hU hUΩ (1 : ℂ)
    exact isLocallySobolevAt_iff_exists_memSobolev_cutoffTempered.2
      ⟨φ, by simp [hφx], hT φ hφU⟩
  · obtain ⟨U, hU, hT⟩ := h.exists_nhds_forall_memSobolev_cutoffTempered
    exact ⟨U ∩ Ω, inter_mem hU (Ω.isOpen.mem_nhds h.mem), inter_subset_right,
      fun φ hφ ↦ hT φ (hφ.trans inter_subset_left)⟩

/-- If `χ = 1` on the support of `φ` and `χ T ∈ H^r` with `n < 2 (r + 2k)`, then
`φ T = φ (χ T) ∈ H^{-2k,p}`. -/
private theorem memSobolev_cutoffTempered_of_memSobolev_two (hp : 1 < p) (hp_top : p ≠ ∞)
    (T : 𝓓'(Ω, ℂ)) {χ φ : 𝓓(Ω, ℂ)} (h : ∀ y ∈ tsupport φ, χ y = 1) {r : ℝ} {k : ℕ}
    (hk : (finrank ℝ E : ℝ) < 2 * (r + 2 * k))
    (hr : TemperedDistribution.MemSobolev r 2 (T.cutoffTempered χ)) :
    TemperedDistribution.MemSobolev (-(2 * k)) p (T.cutoffTempered φ) := by
  rw [← smulLeftCLM_cutoffTempered T h]
  simpa [TestFunction.coe_toSchwartzMapCLM] using
    hr.memSobolev_neg_two_mul_smulLeftCLM hp hp_top hk (TestFunction.toSchwartzMapCLM ℂ φ)

/-- A cutoff `χ` equal to `1` on an open `V ⊇ K`, for a compact `K ⊆ Ω`, with `χ T ∈ H^r` and an
index `k` with `n < 2 (r + 2k)`. -/
private theorem exists_cutoff_memSobolev_two (T : 𝓓'(Ω, ℂ)) {K : Set E} (hK : IsCompact K)
    (hKΩ : K ⊆ Ω) : ∃ (V : Set E) (χ : 𝓓(Ω, ℂ)) (r : ℝ) (k : ℕ), IsOpen V ∧ K ⊆ V ∧
      (∀ y ∈ V, χ y = 1) ∧ (finrank ℝ E : ℝ) < 2 * (r + 2 * k) ∧
      TemperedDistribution.MemSobolev r 2 (T.cutoffTempered χ) := by
  obtain ⟨χ, -, hχ1, -⟩ := TestFunction.exists_cutoff_tsupport_subset (n := ⊤) hK Ω.isOpen hKΩ
    subset_rfl
  obtain ⟨V, hVo, hKV, hV1⟩ := mem_nhdsSet_iff_exists.1 hχ1
  set χ' : 𝓓(Ω, ℂ) := postcompCLM (𝕜 := ℝ) Complex.ofRealCLM χ
  obtain ⟨r, hr⟩ := T.exists_memSobolev_cutoffTempered χ'
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (finrank ℝ E : ℝ) < 2 * (r + 2 * k) :=
    (exists_nat_gt ((finrank ℝ E - 2 * r) / 4)).imp fun k hk ↦ by linarith
  exact ⟨V, χ', r, k, hVo, hKV, fun y hy ↦ by simp [χ', show χ y = 1 from hV1 hy], hk, hr⟩

/-- **Finite order on the `Lᵖ` scale.** Let `1 < p < ∞`. Every cut-off distribution `φ T` lies in
the Bessel-potential space `H^{s,p}` for some real order `s`. -/
theorem exists_memSobolev_cutoffTempered_of_one_lt (hp : 1 < p) (hp_top : p ≠ ∞) (T : 𝓓'(Ω, ℂ))
    (φ : 𝓓(Ω, ℂ)) : ∃ s : ℝ, TemperedDistribution.MemSobolev s p (T.cutoffTempered φ) := by
  obtain ⟨V, χ, r, k, -, hV, hχ, hk, hr⟩ :=
    exists_cutoff_memSobolev_two T φ.hasCompactSupport.isCompact φ.tsupport_subset
  exact ⟨_, memSobolev_cutoffTempered_of_memSobolev_two hp hp_top T (fun y hy ↦ hχ y (hV hy))
    hk hr⟩

/-- **Finite local order on the `Lᵖ` scale.** Let `1 < p < ∞`. For every distribution `T` on `Ω`
and every compact `K ⊆ Ω` there is an order `s` such that `T` is `H^{s,p}` near every point
of `K`. -/
theorem exists_forall_isLocallyMemSobolevAt (hp : 1 < p) (hp_top : p ≠ ∞) (T : 𝓓'(Ω, ℂ))
    {K : Set E} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ s : ℝ, ∀ x ∈ K, T.IsLocallyMemSobolevAt s p x := by
  obtain ⟨V, χ, r, k, hVo, hKV, hχ, hk, hr⟩ := exists_cutoff_memSobolev_two T hK hKΩ
  exact ⟨-(2 * k), fun x hx ↦ ⟨V ∩ Ω, inter_mem (hVo.mem_nhds (hKV hx))
    (Ω.isOpen.mem_nhds (hKΩ hx)), inter_subset_right, fun φ hφ ↦
    memSobolev_cutoffTempered_of_memSobolev_two hp hp_top T (fun y hy ↦ hχ y (hφ hy).1) hk hr⟩⟩

/-! ### Restrictions, tempered distributions and changes of variables -/

section ChangeOfVariables

/-- At a point of an open subset `Ω' ≤ Ω`, the restriction `T|_{Ω'}` is `H^{s,p}` exactly where
`T` is. -/
theorem isLocallyMemSobolevAt_restrictCLM_iff {Ω' : Opens E} (h : Ω' ≤ Ω) (hx : x ∈ Ω') :
    (restrictCLM T : 𝓓'(Ω', ℂ)).IsLocallyMemSobolevAt s p x ↔ T.IsLocallyMemSobolevAt s p x := by
  constructor
  · -- A cutoff on `Ω` supported in `U ⊆ Ω'` is a cutoff on `Ω'`, extended by zero.
    rintro ⟨U, hU, hUΩ', hT⟩
    refine ⟨U, hU, hUΩ'.trans h, fun φ hφ ↦ ?_⟩
    let φ' : 𝓓(Ω', ℂ) := ⟨φ, φ.contDiff, φ.hasCompactSupport, hφ.trans hUΩ'⟩
    have hφ' : monoCLM ℝ φ' = φ := by
      ext y
      simp [φ', h]
    simpa [cutoffTempered_restrictCLM, hφ'] using hT φ' hφ
  · rintro ⟨U, hU, -, hT⟩
    refine ⟨U ∩ Ω', inter_mem hU (Ω'.isOpen.mem_nhds hx), inter_subset_right, fun φ hφ ↦ ?_⟩
    rw [cutoffTempered_restrictCLM]
    exact hT _ (by simpa [h] using hφ.trans inter_subset_left)

/-- For `1 < p < ∞`, a tempered distribution in `H^{s,p}`, restricted to `Ω`, is `H^{s,p}` near
every point of `Ω`: its cut-offs are its products with test functions. -/
theorem _root_.TemperedDistribution.MemSobolev.isLocallyMemSobolevAt_toDistribution (hp : 1 < p)
    (hp_top : p ≠ ∞) {u : 𝓢'(E, ℂ)} (hu : TemperedDistribution.MemSobolev s p u) (hx : x ∈ Ω) :
    (TemperedDistribution.toDistribution Ω u).IsLocallyMemSobolevAt s p x :=
  ⟨Ω, Ω.isOpen.mem_nhds hx, subset_rfl, fun φ _ ↦ by
    rw [cutoffTempered_toDistribution]
    exact hu.smulLeftCLM_of_norm_iteratedFDeriv_le_natCeil hp hp_top fun n _ ↦
      ⟨_, fun y ↦ by
        simpa [coe_toSchwartzMapCLM] using
          (toSchwartzMapCLM ℝ φ).norm_iteratedFDeriv_le_seminorm ℝ n y⟩⟩

variable {e : OpenPartialHomeomorph E E} {U : Opens E}
  {he : ContDiffOn ℝ (⊤ : ℕ∞) e e.source} {he' : ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target}
  {hU : (U : Set E) ⊆ e.source} {hUΩ : MapsTo e U Ω}

/-- **Pulling back preserves local `H^{s,p}` regularity.** Let `1 < p < ∞`. If `T` is `H^{s,p}`
near `e x`, then its pullback `e^* T` along `e` is `H^{s,p}` near `x`. -/
theorem IsLocallyMemSobolevAt.compCLMOfOpenPartialHomeomorph (hp : 1 < p) (hp_top : p ≠ ∞)
    (hx : x ∈ U) (hT : T.IsLocallyMemSobolevAt s p (e x)) :
    (compCLMOfOpenPartialHomeomorph e he he' hU hUΩ T).IsLocallyMemSobolevAt s p x := by
  -- `φ T ∈ H^{s,p}` for every test function `φ` supported in a neighbourhood `W` of `e x`.
  obtain ⟨W, hW, -, hWT⟩ := hT
  -- On a neighbourhood `N` of `x`, `e^* T` is a tempered pullback `Φ^* (χ T)` with `χ` in `W`.
  obtain ⟨Φ, hΦ, hΨ, N, hNU, χ, hΦb, hΨb, hxN, hχW, hT⟩ :=
    exists_restrictCLM_compCLMOfOpenPartialHomeomorph_eq_toDistribution he he' hU hUΩ hx hW T
  rw [← isLocallyMemSobolevAt_restrictCLM_iff hNU hxN, hT]
  exact ((hWT χ hχW).compCLM_of_norm_iteratedFDeriv_le_natCeil hp hp_top hΦ hΨ
    (fun n hn _ ↦ hΦb n hn) (fun n hn _ ↦ hΨb n hn)).isLocallyMemSobolevAt_toDistribution hp
    hp_top hxN

/-- Being `H^{s,p}` near a point is a notion of local regularity: it is open and linear. -/
theorem isLocalRegularity_isLocallyMemSobolevAt (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    IsLocalRegularity fun (Ω : Opens E) (T : 𝓓'(Ω, ℂ)) x ↦ T.IsLocallyMemSobolevAt s p x where
  isOpen_setOf _ T := isOpen_setOf_isLocallyMemSobolevAt s p T
  zero hx := isLocallyMemSobolevAt_zero_iff.2 hx
  add hS hT := hS.add hT
  smul c hT := hT.smul c

variable (s) in
/-- For `1 < p < ∞`, being `H^{s,p}` near a point is an invariant notion of local regularity: it is
open, linear, preserved by smooth multiples and pullback along smooth changes of variables, and
unchanged by restriction to smaller open sets. -/
theorem isInvariantLocalRegularity_isLocallyMemSobolevAt (hp : 1 < p) (hp_top : p ≠ ∞) :
    IsInvariantLocalRegularity
      fun (Ω : Opens E) (T : 𝓓'(Ω, ℂ)) x ↦ T.IsLocallyMemSobolevAt s p x where
  toIsLocalRegularity := isLocalRegularity_isLocallyMemSobolevAt s p
  smulLeftCLM hg hT := hT.smulLeftCLM hg
  restrictCLM_iff h _ _ hx := isLocallyMemSobolevAt_restrictCLM_iff h hx
  compCLMOfOpenPartialHomeomorph _ _ _ _ _ _ hx hT :=
    hT.compCLMOfOpenPartialHomeomorph hp hp_top hx

/-- **Local `H^{s,p}` regularity is invariant under changes of variables.** Let `1 < p < ∞`. The
pullback `e^* T` of a distribution `T` along `e` is `H^{s,p}` near a point `x ∈ U` exactly when
`T` is `H^{s,p}` near `e x`. -/
theorem isLocallyMemSobolevAt_compCLMOfOpenPartialHomeomorph_iff (hp : 1 < p) (hp_top : p ≠ ∞)
    (hx : x ∈ U) :
    (compCLMOfOpenPartialHomeomorph e he he' hU hUΩ T).IsLocallyMemSobolevAt s p x ↔
      T.IsLocallyMemSobolevAt s p (e x) :=
  (isInvariantLocalRegularity_isLocallyMemSobolevAt s hp hp_top).compCLMOfOpenPartialHomeomorph_iff
    hx

end ChangeOfVariables

end Distribution

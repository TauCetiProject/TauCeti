/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.AsymptoticSum
public import TauCeti.Analysis.Pseudodifferential.LocalSymbol.Classical
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff

/-!
# Asymptotic summation of symbols on an open set

Let `U ⊆ ℝⁿ` be open, let `m₀ ≥ m₁ ≥ ⋯` be real orders tending to `-∞` and let `aⱼ` be symbols of
order `mⱼ` on `U` (`TauCeti.LocalSymbol`). This file shows that they have an *asymptotic sum* on
`U`: a symbol `b` of order `m₀` on `U` such that for every `N` the remainder `b - ∑_{j < N} aⱼ` is
a symbol of order `m_N` on `U` (`TauCeti.LocalSymbol.IsAsymptoticSum`,
`TauCeti.LocalSymbol.exists_asymptoticSum`). It is unique modulo smoothing symbols on `U`
(`TauCeti.LocalSymbol.IsAsymptoticSum.isAsymptoticSum_iff_isSmoothing_sub`).

This is Borel's theorem for the symbols read in a chart of a manifold, whose estimates only hold on
the compact subsets of the chart domain `U`. Such a symbol need not extend to a symbol on `ℝⁿ`, so
the asymptotic summation of symbols on `ℝⁿ` (`TauCeti.Symbol.exists_asymptoticSum`) does not apply
to it directly. It does apply after localization. Choose smooth compactly supported functions `ζₖ`
on `U` which sum to `1` on `U` and are locally finite there, and cutoffs `χₖ` on `U` equal to `1`
on the support of `ζₖ` (`IsOpen.exists_contDiff_decomposition_cutoff`). The cut-off symbols
`χₖ aⱼ` extend to symbols on `ℝⁿ` (`TauCeti.LocalSymbol.extend`), with an asymptotic sum `Bₖ` on
`ℝⁿ`. Then `b = ∑ₖ ζₖ Bₖ` is an asymptotic sum on `U`: near every position of `U` only finitely
many `ζₖ` are nonzero, and there `b - ∑_{j < N} aⱼ = ∑ₖ ζₖ (Bₖ - ∑_{j < N} χₖ aⱼ)` is a finite sum
of symbols of order `m_N` (`TauCeti.LocalSymbol.ofEventuallyEq`).

Asymptotic sums commute with restriction to smaller open sets
(`TauCeti.LocalSymbol.IsAsymptoticSum.restrict`), with restriction of symbols on `ℝⁿ`
(`TauCeti.Symbol.IsAsymptoticSum.restrict`), and with the cut-off extension to `ℝⁿ`
(`TauCeti.LocalSymbol.IsAsymptoticSum.extend`).

Applied to the cut-off terms `χ(ξ) a_{m-j}(x, ξ)` of homogeneous symbols on `U`, asymptotic
summation constructs a classical symbol on `U` with any prescribed homogeneous terms
(`TauCeti.LocalClassicalSymbol.exists_term_eq`). So the homogeneous terms identify the classical
symbols of order `m` on `U` modulo the smoothing ones with all sequences of homogeneous symbols of
degrees `m - j` on `U` (`TauCeti.LocalClassicalSymbol.termsEquiv`), as on `ℝⁿ`
(`TauCeti.ClassicalSymbol.termsEquiv`). Asymptotic summation on `U` is what turns formal
expansions read in a chart, such as the inverse-symbol recursion of an elliptic classical symbol
on `U`, into actual symbols on `U`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Proposition 18.1.3.
* R. Melrose, *Pseudodifferential operators on Euclidean space*, MIT 18.199 (2008), Chapter 2,
  Proposition 2.3 and (2.55)–(2.57).
* M. E. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, September 2008,
  Lecture I, (1.17).
-/

public section

noncomputable section

open Set Filter
open scoped ContDiff Topology

namespace TauCeti

variable {n : ℕ} {U U' : TopologicalSpace.Opens (CoordinateSpace n)} {V W : Type*}
  [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]

namespace LocalSymbol

/-! ### Asymptotic sums -/

/-- A symbol `b` of order `m₀` on `U` is an *asymptotic sum* `b ∼ ∑ⱼ aⱼ` of symbols `aⱼ` of orders
`mⱼ` on `U` if for every `N` the remainder `b - ∑_{j < N} aⱼ` is a symbol of order `m_N` on `U`. -/
def IsAsymptoticSum {m : ℕ → ℝ} (b : LocalSymbol U V W (m 0)) (a : ∀ j, LocalSymbol U V W (m j)) :
    Prop :=
  ∀ N, ∃ r : LocalSymbol U V W (m N),
    b.coefficient - ∑ j ∈ Finset.range N, (a j).coefficient = r.coefficient

theorem isAsymptoticSum_iff {m : ℕ → ℝ} {b : LocalSymbol U V W (m 0)}
    {a : ∀ j, LocalSymbol U V W (m j)} :
    b.IsAsymptoticSum a ↔ ∀ N, ∃ r : LocalSymbol U V W (m N),
      b.coefficient - ∑ j ∈ Finset.range N, (a j).coefficient = r.coefficient :=
  Iff.rfl

/-- Asymptotic sums on `U` are unique modulo smoothing symbols: if `b` is an asymptotic sum of
symbols `aⱼ` on `U` whose orders tend to `-∞`, then `b'` is one exactly when `b' - b` is
smoothing. -/
theorem IsAsymptoticSum.isAsymptoticSum_iff_isSmoothing_sub {m : ℕ → ℝ}
    (hm' : Tendsto m atTop atBot) {a : ∀ j, LocalSymbol U V W (m j)}
    {b b' : LocalSymbol U V W (m 0)} (hb : b.IsAsymptoticSum a) :
    b'.IsAsymptoticSum a ↔ (b' - b).IsSmoothing := by
  refine ⟨fun hb' => isSmoothing_iff.2 fun m'' => ?_, fun h N => ?_⟩
  · obtain ⟨N, hN⟩ := (hm'.eventually (eventually_le_atBot m'')).exists
    obtain ⟨r, hr⟩ := hb N
    obtain ⟨r', hr'⟩ := hb' N
    refine ⟨inclusion hN (r' - r), ?_⟩
    rw [coefficient_inclusion, coefficient_sub, ← hr, ← hr', coefficient_sub]
    abel
  · obtain ⟨r, hr⟩ := hb N
    obtain ⟨s, hs⟩ := isSmoothing_iff.1 h (m N)
    refine ⟨s + r, ?_⟩
    rw [coefficient_add, hs, ← hr, coefficient_sub]
    abel

/-- Restricting an asymptotic sum on `U` and its terms to a smaller open set gives an asymptotic
sum there. -/
theorem IsAsymptoticSum.restrict {m : ℕ → ℝ} {b : LocalSymbol U V W (m 0)}
    {a : ∀ j, LocalSymbol U V W (m j)} (hb : b.IsAsymptoticSum a) (h : U' ≤ U) :
    (LocalSymbol.restrict h b).IsAsymptoticSum fun j => LocalSymbol.restrict h (a j) := fun N => by
  obtain ⟨r, hr⟩ := hb N
  refine ⟨LocalSymbol.restrict h r, funext fun ⟨x, ξ⟩ => ?_⟩
  by_cases hx : x ∈ U'
  · simpa [hx, Finset.sum_apply] using congrFun hr (x, ξ)
  · simp [hx, Finset.sum_apply]

/-- The cut-off extension to `ℝⁿ` of an asymptotic sum on `U` is an asymptotic sum of the cut-off
extensions of its terms. -/
theorem IsAsymptoticSum.extend {m : ℕ → ℝ} {b : LocalSymbol U V W (m 0)}
    {a : ∀ j, LocalSymbol U V W (m j)} (hb : b.IsAsymptoticSum a) {ψ : CoordinateSpace n → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hψU : tsupport ψ ⊆ U) :
    (LocalSymbol.extend ψ hψ hψU b).IsAsymptoticSum fun j => LocalSymbol.extend ψ hψ hψU (a j) :=
  Symbol.isAsymptoticSum_iff.2 fun N => by
    obtain ⟨r, hr⟩ := hb N
    refine ⟨LocalSymbol.extend ψ hψ hψU r, funext fun p => ?_⟩
    simp [← hr, Finset.sum_apply, smul_sub, Finset.smul_sum]

/-! ### Existence of asymptotic sums -/

/-- The glued sum `∑ₖ ζₖ(x) Bₖ(x, ξ)` of symbols `Bₖ` on `ℝⁿ` weighted by functions `ζₖ` of the
position. -/
private def gluedSum {m : ℝ} (ζ : ℕ → CoordinateSpace n → ℝ) (B : ℕ → Symbol n V W m)
    (p : CoordinateSpace n × CoordinateSpace n) : V →L[ℂ] W :=
  ∑ᶠ k, ζ k p.1 • (B k).coefficient p

/-- If the weights `ζₖ` sum to `1` near a position `x` of `U` and only the first `M` of them are
nonzero there, and each `ζₖ` is supported where the cutoff `χₖ` equals `1`, then near `x` the
glued sum of asymptotic sums `Bₖ` of the cut-off symbols `χₖ aⱼ` differs from `∑_{j < N} aⱼ` by a
symbol of order `m_N` on `ℝⁿ`. -/
private theorem exists_eventually_eq_gluedSum_sub {m : ℕ → ℝ} {a : ∀ j, LocalSymbol U V W (m j)}
    {ζ χ : ℕ → CoordinateSpace n → ℝ}
    (hζ : ∀ k, ContDiff ℝ ∞ (ζ k) ∧ HasCompactSupport (ζ k) ∧ tsupport (ζ k) ⊆ U)
    (hχ : ∀ k, ContDiff ℝ ∞ (χ k) ∧ HasCompactSupport (χ k) ∧ tsupport (χ k) ⊆ U)
    (hζχ : ∀ k y, ζ k y * χ k y = ζ k y) {B : ℕ → Symbol n V W (m 0)}
    (hB : ∀ k, (B k).IsAsymptoticSum fun j => extend (χ k) (hχ k).1 (hχ k).2.2 (a j))
    {x : CoordinateSpace n} {M : ℕ}
    (hM : ∀ᶠ y in 𝓝 x, (∀ k, M ≤ k → ζ k y = 0) ∧ ∑ k ∈ Finset.range M, ζ k y = 1) (N : ℕ) :
    ∃ s : Symbol n V W (m N), ∀ᶠ y in 𝓝 x, ∀ η, s.coefficient (y, η) =
      gluedSum ζ B (y, η) - ∑ j ∈ Finset.range N, (a j).coefficient (y, η) := by
  choose r hr using fun k => Symbol.isAsymptoticSum_iff.1 (hB k) N
  refine ⟨∑ k ∈ Finset.range M, extend (ζ k) (hζ k).1 (hζ k).2.2 ((r k).restrict U), ?_⟩
  filter_upwards [hM] with y ⟨hzero, hone⟩ η
  -- Only the first `M` weights contribute near `x`, and they sum to `1`.
  have hglued : gluedSum ζ B (y, η) =
      ∑ k ∈ Finset.range M, ζ k y • (B k).coefficient (y, η) :=
    finsum_eq_sum_of_support_subset _ fun k hk => Finset.mem_coe.2 <| Finset.mem_range.2 <|
      not_le.1 fun hMk => hk (by simp [hzero k hMk])
  have ha : ∑ j ∈ Finset.range N, (a j).coefficient (y, η) =
      ∑ k ∈ Finset.range M, ζ k y • ∑ j ∈ Finset.range N, χ k y • (a j).coefficient (y, η) := by
    simp_rw [Finset.smul_sum, smul_smul, hζχ, ← Finset.smul_sum, ← Finset.sum_smul, hone,
      one_smul]
  have hrk : ∀ k, (r k).coefficient (y, η) = (B k).coefficient (y, η) -
      ∑ j ∈ Finset.range N, χ k y • (a j).coefficient (y, η) := fun k => by
    simpa [Finset.sum_apply] using (congrFun (hr k) (y, η)).symm
  by_cases hy : y ∈ U
  · simp [hy, hglued, ha, hrk, smul_sub]
  · have hζy : ∀ k, ζ k y = 0 := fun k =>
      image_eq_zero_of_notMem_tsupport fun h => hy ((hζ k).2.2 h)
    simp [hζy, hglued, (a _).coefficient_of_notMem y hy η]

/-- **Asymptotic summation on an open set** (Borel). Let `m₀ ≥ m₁ ≥ ⋯` be real orders tending to
`-∞`, and let `aⱼ` be symbols of order `mⱼ` on the open set `U`. Then there is a symbol `b` of order
`m₀` on `U` such that for every `N` the remainder `b - ∑_{j < N} aⱼ` is a symbol of order `m_N` on
`U`. -/
theorem exists_asymptoticSum {m : ℕ → ℝ} (hm : Antitone m) (hm' : Tendsto m atTop atBot)
    (a : ∀ j, LocalSymbol U V W (m j)) : ∃ b : LocalSymbol U V W (m 0), b.IsAsymptoticSum a := by
  obtain ⟨ζ, χ, hζ, -, -, hχ, hχζ, hloc⟩ := U.isOpen.exists_contDiff_decomposition_cutoff
  have hζχ : ∀ k y, ζ k y * χ k y = ζ k y := fun k y => by
    by_cases hy : y ∈ tsupport (ζ k)
    · rw [hχζ k hy, Pi.one_apply, mul_one]
    · rw [image_eq_zero_of_notMem_tsupport hy, zero_mul]
  -- On the `k`-th piece, an asymptotic sum on `ℝⁿ` of the cut-off symbols `χₖ aⱼ`.
  choose B hB using fun k => Symbol.exists_asymptoticSum hm hm'
    fun j => extend (χ k) (hχ k).1 (hχ k).2.2 (a j)
  -- Near every position of `U` only finitely many weights `ζₖ` are nonzero, and they sum to `1`.
  have hfin : ∀ x ∈ U, ∃ M : ℕ, ∀ᶠ y in 𝓝 x,
      (∀ k, M ≤ k → ζ k y = 0) ∧ ∑ k ∈ Finset.range M, ζ k y = 1 := fun x hx => by
    obtain ⟨M, hM⟩ := hloc x hx
    refine ⟨M, hM.mono fun y hy => ⟨fun k hk => ?_, hy.2 M le_rfl⟩⟩
    rw [← hζχ k y, hy.1 k hk, mul_zero]
  have hrem : ∀ N, ∀ x ∈ U, ∃ s : Symbol n V W (m N), ∀ᶠ y in 𝓝 x, ∀ η,
      s.coefficient (y, η) =
        gluedSum ζ B (y, η) - ∑ j ∈ Finset.range N, (a j).coefficient (y, η) :=
    fun N x hx => (hfin x hx).elim fun _ hM =>
      exists_eventually_eq_gluedSum_sub hζ hχ hζχ hB hM N
  -- Outside `U` all weights vanish, and so does the glued sum.
  have hout : ∀ N, ∀ x ∉ U, ∀ ξ,
      (gluedSum ζ B - ∑ j ∈ Finset.range N, (a j).coefficient) (x, ξ) = 0 := fun N x hx ξ => by
    have hζx : ∀ k, ζ k x = 0 := fun k =>
      image_eq_zero_of_notMem_tsupport fun h => hx ((hζ k).2.2 h)
    simp [gluedSum, hζx, Finset.sum_apply, (a _).coefficient_of_notMem x hx ξ]
  let r : ∀ N, LocalSymbol U V W (m N) := fun N =>
    ofEventuallyEq (gluedSum ζ B - ∑ j ∈ Finset.range N, (a j).coefficient) (hout N)
      fun x hx => (hrem N x hx).imp fun _ hs => hs.mono fun y hy η => by
        rw [hy η, Pi.sub_apply, Finset.sum_apply]
  refine ⟨r 0, fun N => ⟨r N, ?_⟩⟩
  simp [r]

end LocalSymbol

/-- Restricting an asymptotic sum on `ℝⁿ` and its terms to an open set `U` gives an asymptotic sum
on `U`. -/
theorem Symbol.IsAsymptoticSum.restrict {m : ℕ → ℝ} {b : Symbol n V W (m 0)}
    {a : ∀ j, Symbol n V W (m j)} (hb : b.IsAsymptoticSum a) :
    (b.restrict U).IsAsymptoticSum fun j => (a j).restrict U := fun N => by
  obtain ⟨r, hr⟩ := Symbol.isAsymptoticSum_iff.1 hb N
  refine ⟨r.restrict U, funext fun ⟨x, ξ⟩ => ?_⟩
  by_cases hx : x ∈ U
  · simpa [hx, Finset.sum_apply] using congrFun hr (x, ξ)
  · simp [hx, Finset.sum_apply]

/-! ### Classical symbols with prescribed homogeneous terms -/

namespace LocalClassicalSymbol

variable {m : ℝ}

/-- **Borel summation of homogeneous terms on an open set.** Every sequence of homogeneous symbols
`a_{m-j}` of degrees `m - j` on `U` is the sequence of homogeneous terms of a classical symbol of
order `m` on `U`. -/
theorem exists_term_eq (a : ∀ j : ℕ, LocalHomogeneousSymbol U V W (m - j)) :
    ∃ b : LocalClassicalSymbol U V W m, b.term = a := by
  let χ : FrequencyCutoff (CoordinateSpace n) := default
  -- An asymptotic sum of the cut-off terms `χ(ξ) a_{m-j}(x, ξ)` is the required full symbol.
  have hm : Antitone fun j : ℕ => m - j := fun _ _ hij => sub_le_sub_left (Nat.cast_le.2 hij) m
  have hm' : Tendsto (fun j : ℕ => m - j) atTop atBot :=
    tendsto_atBot_add_const_left atTop m <| tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop
  obtain ⟨b, hb⟩ := LocalSymbol.exists_asymptoticSum hm hm' fun j =>
    LocalHomogeneousSymbol.cutoffSymbol χ (a j)
  refine ⟨⟨LocalSymbol.inclusion (by simp) b, a, χ, fun N => ?_⟩, rfl⟩
  obtain ⟨r, hr⟩ := hb N
  exact ⟨r, fun p => by simp [← hr, Finset.sum_apply]⟩

/-- Every sequence of homogeneous terms of degrees `m - j` on `U` is the expansion of a classical
symbol of order `m` on `U`. -/
theorem termsLinearMap_surjective : Function.Surjective (termsLinearMap U V W m) :=
  fun a => (exists_term_eq a).imp fun b hb => (termsLinearMap_apply b).trans hb

variable (U V W m) in
/-- Classical symbols of order `m` on `U` modulo smoothing symbols are the formal sums of
homogeneous terms of degrees `m - j` on `U`: the homogeneous terms identify the quotient by the
kernel of `TauCeti.LocalClassicalSymbol.termsLinearMap`, the smoothing classical symbols on `U`
(`TauCeti.LocalClassicalSymbol.mem_ker_termsLinearMap`), with all sequences of homogeneous terms. -/
def termsEquiv : (LocalClassicalSymbol U V W m ⧸ LinearMap.ker (termsLinearMap U V W m)) ≃ₗ[ℂ]
    ∀ j : ℕ, LocalHomogeneousSymbol U V W (m - j) :=
  (termsLinearMap U V W m).quotKerEquivOfSurjective termsLinearMap_surjective

@[simp]
theorem termsEquiv_mk (a : LocalClassicalSymbol U V W m) :
    termsEquiv U V W m (Submodule.Quotient.mk a) = a.term :=
  (LinearMap.quotKerEquivOfSurjective_apply_mk _ _ a).trans (termsLinearMap_apply a)

end LocalClassicalSymbol

end TauCeti

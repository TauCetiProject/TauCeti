/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Local
public import TauCeti.Analysis.Holder.Distribution
public import TauCeti.Analysis.Pseudodifferential.BesovSpace
public import TauCeti.Analysis.Pseudodifferential.ProperSupport.EllipticRegularity

/-!
# Elliptic regularity of properly supported pseudodifferential operators on Besov spaces

Let `a` be a scalar symbol of order `m` on `ℝⁿ` whose quantization has kernel supported within
distance `R` of the diagonal (`TauCeti.Symbol.HasNearDiagonalKernel a R`), so that `Op(a)` acts on
all distributions `T ∈ 𝓓'(ℝⁿ)` (`TauCeti.Symbol.quantizeDistribution`). This file proves **local
elliptic regularity** of `Op(a)` on the inhomogeneous Besov scale `B^s_{p,q}`, for every real `s`,
`1 < p ≤ ∞` and `1 ≤ q ≤ ∞`: if `a` has a formal left parametrix `b`, `1 ∼ ∑ₖ sharpTerm b a k`,
then

`Op(a) T ∈ B^s_{p,q}` near `x` ⟹ `T ∈ B^{s + m}_{p,q}` near `x`,

with no a priori regularity of `T` (`Distribution.IsLocallyMemBesovAt.of_quantizeDistribution`).
Every symbol elliptic above some radius
(`TauCeti.Symbol.IsEllipticAbove.isLocallyMemBesovAt_of_quantizeDistribution`) and every elliptic
classical symbol (`TauCeti.ClassicalSymbol.IsElliptic.isLocallyMemBesovAt_of_quantizeDistribution`)
qualifies.

Conversely, for all `1 ≤ p, q ≤ ∞`, properly supported operators of order `m` map
`B^{s + m}_{p,q}` locally to `B^s_{p,q}`
(`Distribution.memBesov_cutoffTempered_quantizeDistribution`).
For `p = q = ∞` these are the local mapping and regularity theorems on the Hölder–Zygmund scale
`𝒞^s = B^s_{∞,∞}`, which at positive non-integer orders `k + α` is the scale of the Hölder spaces
`C^{k,α}` (`TauCeti.BesovSpace.ckHolderSpaceEquiv`): an elliptic operator of order `m` gains back
`m` orders of Hölder–Zygmund regularity, as in the Schauder estimates. In Hölder form, for
`0 < α < 1` and natural numbers `k`, `l` with `k + m = l`,

`Op(a) T ∈ C^{k,α}` near `x` ⟹ `T ∈ C^{l,α}` near `x`

(`Distribution.IsLocallyCkHolderAt.of_quantizeDistribution`), which is the local Schauder theorem
for properly supported elliptic operators of integer order acting on distributions, through the
local identification `Distribution.isLocallyMemBesovAt_iff_isLocallyCkHolderAt`.

## The argument

The local regularity reduces to interior regularity on the Besov scale
(`TauCeti.Symbol.memBesov_smulLeftCLM_of_memBesov_quantizeTempered`) exactly as on the `H^s` scale
(`Distribution.IsLocallySobolevAt.of_quantizeDistribution`). For the nested cutoffs `φ`, `ψ` and
`χ` of `TauCeti.Symbol.HasNearDiagonalKernel.exists_cutoffs_of_mem_nhds`,
`Op(ψ a) (χ T) = ψ Op(a) T` (`TauCeti.Symbol.quantizeTempered_cutoffTempered`), and `χ T` lies in
some `B^r_{p,q}` (`Distribution.exists_memBesov_cutoffTempered`, which needs `1 < p`).

## References

* M. E. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, September 2008,
  Lecture I, (3.32)–(3.34) (pseudodifferential operators on the Zygmund spaces) and
  (4.6)–(4.11) (local elliptic regularity by the parametrix).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1.
-/

public section

noncomputable section

open Set TopologicalSpace TemperedDistribution
open scoped ContDiff Distributions ENNReal NNReal SchwartzMap Topology

namespace Distribution

open TauCeti TauCeti.Symbol

variable {n : ℕ} {m R : ℝ} {a : Symbol n ℂ ℂ m} {T : 𝓓'((⊤ : Opens (CoordinateSpace n)), ℂ)}
  {φ : ContDiffBump (0 : CoordinateSpace n)} {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- **Properly supported operators map `B^{s + m}_{p,q}` locally to `B^s_{p,q}`.** If `Op(a)` has
order `m` and kernel supported within distance `R` of the diagonal, and `T` is `B^{s + m}_{p,q}`
near every point of the closed `R`-neighbourhood of the support of a test function `ψ`, then
`ψ Op(a) T ∈ B^s_{p,q}`. -/
theorem memBesov_cutoffTempered_quantizeDistribution (ha : a.HasNearDiagonalKernel R)
    {ψ : 𝓓((⊤ : Opens (CoordinateSpace n)), ℂ)} {s : ℝ}
    (h : ∀ y ∈ Metric.cthickening R (tsupport ψ), T.IsLocallyMemBesovAt φ (s + m) p q y) :
    ((quantizeDistribution ha T).cutoffTempered ψ).MemBesov φ s p q := by
  obtain ⟨χ, hχ1, hχU⟩ := TestFunction.exists_complex_cutoff_tsupport_subset (n := ⊤) (Ω := ⊤)
    (ψ.hasCompactSupport.isCompact.cthickening (r := R))
    (isOpen_setOf_isLocallyMemBesovAt φ _ p q T) h (by simp)
  have hc := hasCompactSpatialSupport_smulLeft ψ.contDiff ψ.hasCompactSupport a
  have hca (x ξ : CoordinateSpace n) := coefficient_smulLeft ψ.contDiff a (x, ξ)
  rw [← quantizeTempered_cutoffTempered ha hc.isUniform hca
    (fun x hx ↦ hχ1.self_of_nhdsSet x hx) T]
  simpa using (memBesov_cutoffTempered_of_forall_isLocallyMemBesovAt
    fun y hy ↦ hχU hy).quantizeTempered hc.isUniform

/-- **Local elliptic regularity of properly supported operators on Besov spaces.** Let `Op(a)`
have order `m` and kernel supported within distance `R` of the diagonal, let `a` have a formal
left parametrix `b`, `1 ∼ ∑ₖ sharpTerm b a k`, and let `1 < p ≤ ∞`. If `Op(a) T` is `B^s_{p,q}`
near `x` for a distribution `T`, then `T` is `B^{s + m}_{p,q}` near `x`. -/
theorem IsLocallyMemBesovAt.of_quantizeDistribution (ha : a.HasNearDiagonalKernel R)
    {b : Symbol n ℂ ℂ (-m)}
    (hab : IsAsymptoticSum (m := fun k : ℕ ↦ -m + m - k)
      (inclusion (by simp) (const (.id ℂ ℂ))) (b.sharpTerm a))
    (hp : 1 < p) {x : CoordinateSpace n} {s : ℝ}
    (h : (quantizeDistribution ha T).IsLocallyMemBesovAt φ s p q x) :
    T.IsLocallyMemBesovAt φ (s + m) p q x := by
  obtain ⟨U, hU, -, hUs⟩ := isLocallyMemBesovAt_iff.1 h
  obtain ⟨φ₀, ψ, χ, φS, hφ₀x, hψU, hφS, hca, hT⟩ := ha.exists_cutoffs_of_mem_nhds hU
  obtain ⟨hcT, hφ₀T⟩ := hT T
  -- `χ T` lies in some `B^r_{p,q}`, and `Op(ψ a) (χ T) = ψ Op(a) T ∈ B^s_{p,q}`.
  obtain ⟨r, hr⟩ := exists_memBesov_cutoffTempered φ hp
    (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ q)).ne' T χ
  have hc := hasCompactSpatialSupport_smulLeft ψ.contDiff ψ.hasCompactSupport a
  have hreg := memBesov_smulLeftCLM_of_memBesov_quantizeTempered hab hφS hc hca hr
    (hcT ▸ hUs ψ hψU)
  exact isLocallyMemBesovAt_iff_exists_memBesov_cutoffTempered.2 ⟨φ₀, hφ₀x, hφ₀T ▸ hreg⟩

/-- **Local Schauder regularity of properly supported operators.** Let `Op(a)` have order `m` and
kernel supported within distance `R` of the diagonal, let `a` have a formal left parametrix `b`,
`1 ∼ ∑ₖ sharpTerm b a k`, and let `0 < α < 1` and `k + m = l` for natural numbers `k` and `l`. If
`Op(a) T` is a `C^{k,α}` function near `x` for a distribution `T`, then `T` is a `C^{l,α}` function
near `x`. -/
theorem IsLocallyCkHolderAt.of_quantizeDistribution (ha : a.HasNearDiagonalKernel R)
    {b : Symbol n ℂ ℂ (-m)}
    (hab : IsAsymptoticSum (m := fun k : ℕ ↦ -m + m - k)
      (inclusion (by simp) (const (.id ℂ ℂ))) (b.sharpTerm a))
    {k l : ℕ} {α : ℝ≥0} (hα0 : 0 < α) (hα1 : α < 1) (hkl : (k : ℝ) + m = l)
    {x : CoordinateSpace n} (h : (quantizeDistribution ha T).IsLocallyCkHolderAt k α x) :
    T.IsLocallyCkHolderAt l α x := by
  have hreg := (h.isLocallyMemBesovAt default).of_quantizeDistribution ha hab ENNReal.one_lt_top
  rw [add_right_comm, hkl] at hreg
  exact hreg.isLocallyCkHolderAt hα0 hα1

end Distribution

namespace TauCeti

variable {n : ℕ} {m R : ℝ} {T : 𝓓'((⊤ : Opens (CoordinateSpace n)), ℂ)} {x : CoordinateSpace n}
  {s : ℝ} {φ : ContDiffBump (0 : CoordinateSpace n)} {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- **Local Besov regularity for symbols elliptic above a radius.** If `a` is elliptic above some
radius, `Op(a)` has kernel supported within distance `R` of the diagonal and `1 < p ≤ ∞`, then
`Op(a) T ∈ B^s_{p,q}` near `x` implies `T ∈ B^{s + m}_{p,q}` near `x`. -/
theorem Symbol.IsEllipticAbove.isLocallyMemBesovAt_of_quantizeDistribution
    {a : Symbol n ℂ ℂ m} {R' : ℝ} (hell : a.IsEllipticAbove R') (ha : a.HasNearDiagonalKernel R)
    (hp : 1 < p) (h : (quantizeDistribution ha T).IsLocallyMemBesovAt φ s p q x) :
    T.IsLocallyMemBesovAt φ (s + m) p q x :=
  let ⟨_, hab, _⟩ := hell.exists_isAsymptoticSum_sharpTerm
  h.of_quantizeDistribution ha hab hp

/-- **Local Besov regularity for elliptic classical symbols.** If the classical symbol `a` is
elliptic, `Op(a)` has kernel supported within distance `R` of the diagonal and `1 < p ≤ ∞`, then
`Op(a) T ∈ B^s_{p,q}` near `x` implies `T ∈ B^{s + m}_{p,q}` near `x`. -/
theorem ClassicalSymbol.IsElliptic.isLocallyMemBesovAt_of_quantizeDistribution
    {a : ClassicalSymbol n ℂ ℂ m} (hell : a.IsElliptic) (ha : a.toSymbol.HasNearDiagonalKernel R)
    (hp : 1 < p) (h : (Symbol.quantizeDistribution ha T).IsLocallyMemBesovAt φ s p q x) :
    T.IsLocallyMemBesovAt φ (s + m) p q x :=
  let ⟨_, hab⟩ := hell.exists_isAsymptoticSum_sharpTerm_left
  h.of_quantizeDistribution ha hab hp

variable {k l : ℕ} {α : ℝ≥0}

/-- **Local Schauder regularity for symbols elliptic above a radius.** If `a` is elliptic above
some radius, `Op(a)` has kernel supported within distance `R` of the diagonal, `0 < α < 1` and
`k + m = l` for natural numbers `k` and `l`, then `Op(a) T ∈ C^{k,α}` near `x` implies
`T ∈ C^{l,α}` near `x`. -/
theorem Symbol.IsEllipticAbove.isLocallyCkHolderAt_of_quantizeDistribution
    {a : Symbol n ℂ ℂ m} {R' : ℝ} (hell : a.IsEllipticAbove R') (ha : a.HasNearDiagonalKernel R)
    (hα0 : 0 < α) (hα1 : α < 1) (hkl : (k : ℝ) + m = l)
    (h : (quantizeDistribution ha T).IsLocallyCkHolderAt k α x) : T.IsLocallyCkHolderAt l α x :=
  let ⟨_, hab, _⟩ := hell.exists_isAsymptoticSum_sharpTerm
  h.of_quantizeDistribution ha hab hα0 hα1 hkl

/-- **Local Schauder regularity for elliptic classical symbols.** If the classical symbol `a` is
elliptic, `Op(a)` has kernel supported within distance `R` of the diagonal, `0 < α < 1` and
`k + m = l` for natural numbers `k` and `l`, then `Op(a) T ∈ C^{k,α}` near `x` implies
`T ∈ C^{l,α}` near `x`. -/
theorem ClassicalSymbol.IsElliptic.isLocallyCkHolderAt_of_quantizeDistribution
    {a : ClassicalSymbol n ℂ ℂ m} (hell : a.IsElliptic) (ha : a.toSymbol.HasNearDiagonalKernel R)
    (hα0 : 0 < α) (hα1 : α < 1) (hkl : (k : ℝ) + m = l)
    (h : (Symbol.quantizeDistribution ha T).IsLocallyCkHolderAt k α x) :
    T.IsLocallyCkHolderAt l α x :=
  let ⟨_, hab⟩ := hell.exists_isAsymptoticSum_sharpTerm_left
  h.of_quantizeDistribution ha hab hα0 hα1 hkl

end TauCeti

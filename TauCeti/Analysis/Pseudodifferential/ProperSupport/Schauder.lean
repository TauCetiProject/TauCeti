/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.Holder
public import TauCeti.Analysis.Pseudodifferential.DistributionalRegularity
public import TauCeti.Analysis.Pseudodifferential.ProperSupport.Besov
public import TauCeti.Analysis.Pseudodifferential.ProperSupport.Differential

/-!
# Localized Schauder regularity of properly supported pseudodifferential operators

Let `a` be a scalar symbol of order `m` on `ℝⁿ` whose quantization has kernel supported within
distance `R` of the diagonal (`TauCeti.Symbol.HasNearDiagonalKernel a R`), so that `Op(a)` acts on
all distributions `T ∈ 𝓓'(ℝⁿ)` (`TauCeti.Symbol.quantizeDistribution`), and let `m` be an integer,
`m = l - k` for natural numbers `k` and `l`, so that `k + m ≥ 0`. This file proves the
**localized Schauder theorem** for such operators, in the classical Hölder spaces: for
`0 < α < 1`, if `a` has a formal left parametrix `b`, `1 ∼ ∑ₖ sharpTerm b a k`, then

`Op(a) T` is `C^{k,α}` near `x` ⟹ `T` is `C^{k+m,α}` near `x`,

for an arbitrary distribution `T`, with no a priori regularity
(`Distribution.IsLocallyCkHolderAt.of_quantizeDistribution`). Here a distribution is `C^{k,α}`
near `x` when it is a `C^k` function with `α`-Hölder `k`-th derivative on a neighbourhood of `x`
(`Distribution.IsLocallyCkHolderAt`). Every symbol elliptic above some radius
(`TauCeti.Symbol.IsEllipticAbove.isLocallyCkHolderAt_of_quantizeDistribution`) and every elliptic
classical symbol (`TauCeti.ClassicalSymbol.IsElliptic.isLocallyCkHolderAt_of_quantizeDistribution`)
qualifies, and so does every differential operator `P = ∑ i ∈ t, c i g i ∂^(m i)` of order `M`
with smooth coefficients that is elliptic at every point of `ℝⁿ`
(`Distribution.IsLocallyCkHolderAt.of_sum_smul_smulLeftCLM_iteratedLineDerivOp`): if `P T` is
`C^{k,α}` near `x`, then `T` is `C^{k+M,α}` near `x`.

Conversely, `Op(a)` maps `C^{k+m,α}` to `C^{k,α}` locally: if `T` is `C^{k+m,α}` near every point
of the closed `R`-neighbourhood of a neighbourhood of `x`, then `Op(a) T` is `C^{k,α}` near `x`
(`Distribution.IsLocallyCkHolderAt.quantizeDistribution`).

## The argument

For `0 < α < 1`, being `C^{k,α}` near `x` is local membership in the Hölder–Zygmund space
`𝒞^{k+α} = B^{k+α}_{∞,∞}` (`Distribution.isLocallyMemBesovAt_iff_isLocallyCkHolderAt`). On this
scale the parametrix gives local elliptic regularity
(`Distribution.IsLocallyMemBesovAt.of_quantizeDistribution`), and properly supported operators of
order `m` map `𝒞^{s+m}` locally to `𝒞^s`
(`Distribution.memBesov_cutoffTempered_quantizeDistribution`).
The integrality of `m` makes `k + α + m = l + α` again of the form `l + α` with `l : ℕ`.

## References

* M. E. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, September 2008,
  Lecture I, (3.32)–(3.34) (pseudodifferential operators on the Zygmund spaces) and
  (4.6)–(4.11) (local elliptic regularity by the parametrix).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1.
-/

public section

noncomputable section

open Set TopologicalSpace TemperedDistribution Metric
open scoped ContDiff Distributions ENNReal NNReal SchwartzMap Topology LineDeriv

namespace Distribution

open TauCeti TauCeti.Symbol

variable {n : ℕ} {m R : ℝ} {a : Symbol n ℂ ℂ m} {T : 𝓓'((⊤ : Opens (CoordinateSpace n)), ℂ)}
  {x : CoordinateSpace n} {k l : ℕ} {α : ℝ≥0}

/-- **Localized Schauder regularity of properly supported operators.** Let `Op(a)` have order `m`
and kernel supported within distance `R` of the diagonal, let `a` have a formal left parametrix
`b`, `1 ∼ ∑ₖ sharpTerm b a k`, and let `k + m = l` for natural numbers `k` and `l`. For
`0 < α < 1`, if `Op(a) T` is `C^{k,α}` near `x` for a distribution `T`, then `T` is `C^{l,α}` near
`x`. -/
theorem IsLocallyCkHolderAt.of_quantizeDistribution (ha : a.HasNearDiagonalKernel R)
    {b : Symbol n ℂ ℂ (-m)}
    (hab : IsAsymptoticSum (m := fun k : ℕ ↦ -m + m - k)
      (inclusion (by simp) (const (.id ℂ ℂ))) (b.sharpTerm a))
    (hm : k + m = l) (hα0 : 0 < α) (hα1 : α < 1)
    (h : (quantizeDistribution ha T).IsLocallyCkHolderAt k α x) :
    T.IsLocallyCkHolderAt l α x := by
  rw [← isLocallyMemBesovAt_iff_isLocallyCkHolderAt default hα0 hα1] at h ⊢
  have hs : (k : ℝ) + α + m = l + α := by rw [← hm]; ring
  simpa only [hs] using h.of_quantizeDistribution ha hab ENNReal.one_lt_top

/-- **Properly supported operators map `C^{k+m,α}` locally to `C^{k,α}`.** Let `Op(a)` have
order `m` and kernel supported within distance `R` of the diagonal, and let `k + m = l` for
natural numbers `k` and `l`. For `0 < α < 1`, if `T` is `C^{l,α}` near every point of the closed
`R`-neighbourhood of a neighbourhood `V` of `x`, then `Op(a) T` is `C^{k,α}` near `x`. -/
theorem IsLocallyCkHolderAt.quantizeDistribution (ha : a.HasNearDiagonalKernel R)
    (hm : k + m = l) (hα0 : 0 < α) (hα1 : α < 1) {V : Set (CoordinateSpace n)} (hV : V ∈ 𝓝 x)
    (h : ∀ y ∈ cthickening R V, T.IsLocallyCkHolderAt l α y) :
    (quantizeDistribution ha T).IsLocallyCkHolderAt k α x := by
  obtain ⟨ψ, hψ1, hψV⟩ := TestFunction.exists_complex_cutoff_tsupport_subset (n := ⊤)
    (Ω := ⊤) isCompact_singleton isOpen_interior
    (singleton_subset_iff.2 (mem_interior_iff_mem_nhds.2 hV)) (by simp)
  rw [← isLocallyMemBesovAt_iff_isLocallyCkHolderAt default hα0 hα1]
  refine isLocallyMemBesovAt_iff_exists_memBesov_cutoffTempered.2
    ⟨ψ, by rwa [nhdsSet_singleton] at hψ1, memBesov_cutoffTempered_quantizeDistribution ha
      fun y hy ↦ ?_⟩
  have hs : (k : ℝ) + α + m = l + α := by rw [← hm]; ring
  rw [hs, isLocallyMemBesovAt_iff_isLocallyCkHolderAt default hα0 hα1]
  exact h y (cthickening_subset_of_subset R (hψV.trans interior_subset) hy)

end Distribution

namespace TauCeti

open Distribution

variable {n : ℕ} {m R : ℝ} {T : 𝓓'((⊤ : Opens (CoordinateSpace n)), ℂ)} {x : CoordinateSpace n}
  {k l : ℕ} {α : ℝ≥0}

/-- **Localized Schauder regularity for symbols elliptic above a radius.** If `a` of order `m` is
elliptic above some radius, `Op(a)` has kernel supported within distance `R` of the diagonal,
`k + m = l` for natural numbers `k` and `l`, and `0 < α < 1`, then `Op(a) T` being `C^{k,α}` near
`x` implies that `T` is `C^{l,α}` near `x`. -/
theorem Symbol.IsEllipticAbove.isLocallyCkHolderAt_of_quantizeDistribution
    {a : Symbol n ℂ ℂ m} {R' : ℝ} (hell : a.IsEllipticAbove R') (ha : a.HasNearDiagonalKernel R)
    (hm : k + m = l) (hα0 : 0 < α) (hα1 : α < 1)
    (h : (quantizeDistribution ha T).IsLocallyCkHolderAt k α x) :
    T.IsLocallyCkHolderAt l α x :=
  let ⟨_, hab, _⟩ := hell.exists_isAsymptoticSum_sharpTerm
  h.of_quantizeDistribution ha hab hm hα0 hα1

/-- **Localized Schauder regularity for elliptic classical symbols.** If the classical symbol `a`
of order `m` is elliptic, `Op(a)` has kernel supported within distance `R` of the diagonal,
`k + m = l` for natural numbers `k` and `l`, and `0 < α < 1`, then `Op(a) T` being `C^{k,α}` near
`x` implies that `T` is `C^{l,α}` near `x`. -/
theorem ClassicalSymbol.IsElliptic.isLocallyCkHolderAt_of_quantizeDistribution
    {a : ClassicalSymbol n ℂ ℂ m} (hell : a.IsElliptic) (ha : a.toSymbol.HasNearDiagonalKernel R)
    (hm : k + m = l) (hα0 : 0 < α) (hα1 : α < 1)
    (h : (Symbol.quantizeDistribution ha T).IsLocallyCkHolderAt k α x) :
    T.IsLocallyCkHolderAt l α x :=
  let ⟨_, hab⟩ := hell.exists_isAsymptoticSum_sharpTerm_left
  h.of_quantizeDistribution ha hab hm hα0 hα1

end TauCeti

namespace Distribution

open TauCeti

variable {n : ℕ} {ι : Type*} {t : Finset ι} {d : ι → ℕ} {v : ∀ i, Fin (d i) → CoordinateSpace n}
  {c : ι → ℂ} {g : ι → CoordinateSpace n → ℝ} {T : 𝓓'((⊤ : Opens (CoordinateSpace n)), ℂ)}
  {x : CoordinateSpace n} {k : ℕ} {α : ℝ≥0}

/-- **Localized Schauder regularity for elliptic differential operators.** Let
`P = ∑ i ∈ t, c i g i ∂^(v i)` have smooth real coefficients `g i`, complex constants `c i` and
orders `d i ≤ M`, and let `P` be elliptic on `ℝⁿ`: at every point `y`, its principal symbol of
order `M` with the coefficients frozen at `y` vanishes at no `ξ ≠ 0`. For `0 < α < 1`, if `P T` is
`C^{k,α}` near `x`, then `T` is `C^{k+M,α}` near `x`. -/
theorem IsLocallyCkHolderAt.of_sum_smul_smulLeftCLM_iteratedLineDerivOp
    (hg : ∀ i, ContDiff ℝ ∞ (g i)) {M : ℕ} (hd : ∀ i ∈ t, d i ≤ M)
    (hσ : ∀ y ξ, ξ ≠ 0 → constCoeffPrincipalSymbol t (fun i ↦ c i * g i y) v M ξ ≠ 0)
    (hα0 : 0 < α) (hα1 : α < 1)
    (hPT : (∑ i ∈ t, c i • Distribution.smulLeftCLM (hg i) (∂^{v i} T)).IsLocallyCkHolderAt k α
      x) :
    T.IsLocallyCkHolderAt (k + M) α x := by
  have hb (i : ι) (_ : i ∈ t) :
      ContDiff ℝ ∞ fun y ↦ (c i * g i y) • ContinuousLinearMap.id ℂ ℂ :=
    (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (hg i))).smul contDiff_const
  have ha := ClassicalSymbol.hasNearDiagonalKernel_toSymbol_ofDifferentialSymbol M t v
    (fun i y ↦ (c i * g i y) • ContinuousLinearMap.id ℂ ℂ) hb hd one_pos
  rw [← ClassicalSymbol.quantizeDistribution_ofDifferentialSymbol hg ha] at hPT
  exact ((ClassicalSymbol.isElliptic_ofDifferentialSymbol_smul_id_iff M hb hd).2 hσ
    ).isLocallyCkHolderAt_of_quantizeDistribution ha (by push_cast; ring) hα0 hα1 hPT

end Distribution

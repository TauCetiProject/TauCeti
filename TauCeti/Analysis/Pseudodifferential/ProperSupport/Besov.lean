/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Local
public import TauCeti.Analysis.Pseudodifferential.BesovSpace
public import TauCeti.Analysis.Pseudodifferential.ProperSupport.EllipticRegularity

/-!
# Elliptic regularity of pseudodifferential operators on Besov spaces

Let `a` be a scalar symbol of order `m` on `ℝⁿ` with a formal left parametrix `b`,
`1 ∼ ∑ₖ sharpTerm b a k`; every symbol elliptic above some radius has one. This file proves
elliptic regularity of `Op(a)` on the inhomogeneous Besov scale `B^s_{p,q}`, for every real `s`
and all `1 ≤ p, q ≤ ∞`, in two forms.

* **Interior regularity on tempered distributions**
  (`TauCeti.Symbol.memBesov_smulLeftCLM_of_memBesov_quantizeTempered`): let `ψ` be a compactly
  supported Schwartz function and `c` a symbol with compact spatial support agreeing with `a` near
  the support of `ψ`. If `u ∈ B^r_{p,q}` and `Op(c) u ∈ B^s_{p,q}`, then `ψ u ∈ B^{s + m}_{p,q}`.
* **Local regularity of properly supported operators on distributions**
  (`Distribution.IsLocallyMemBesovAt.of_quantizeDistribution`): if `Op(a)` has kernel supported
  within distance `R` of the diagonal (`TauCeti.Symbol.HasNearDiagonalKernel a R`), so that it acts
  on all distributions `T ∈ 𝓓'(ℝⁿ)` (`TauCeti.Symbol.quantizeDistribution`), and `1 < p ≤ ∞`, then

  `Op(a) T ∈ B^s_{p,q}` near `x` ⟹ `T ∈ B^{s + m}_{p,q}` near `x`,

  with no a priori regularity of `T`. Every symbol elliptic above some radius
  (`TauCeti.Symbol.IsEllipticAbove.isLocallyMemBesovAt_of_quantizeDistribution`) and every
  elliptic classical symbol
  (`TauCeti.ClassicalSymbol.IsElliptic.isLocallyMemBesovAt_of_quantizeDistribution`) qualifies.

Conversely, properly supported operators of order `m` map `B^{s + m}_{p,q}` locally to
`B^s_{p,q}` (`Distribution.memBesov_cutoffTempered_quantizeDistribution`). For `p = q = ∞` these
are the local mapping and regularity theorems on the Hölder–Zygmund scale `𝒞^s = B^s_{∞,∞}`,
which at positive non-integer orders `k + α` is the scale of the Hölder spaces `C^{k,α}`
(`TauCeti.BesovSpace.ckHolderSpaceEquiv`): an elliptic operator of order `m` gains back `m` orders
of Hölder–Zygmund regularity, as in the Schauder estimates.

## The argument

The interior regularity follows the parametrix argument of
`TauCeti.Symbol.memSobolev_smulLeftCLM_of_memSobolev_quantizeSobolev` on the Bessel-potential
scale, carried out once on all tempered distributions. With `q(x, ξ) = ψ(x) b(x, ξ)`, the symbol
`q # c - ψ` is smoothing (`TauCeti.Symbol.isSmoothing_sharp_sub_ofSpatial`), so it has a
representative `R'` of every order. On tempered distributions `Op(q # c) = Op(q) ∘ Op(c)`
(`TauCeti.Symbol.quantizeTempered_sharp`) and `Op(ψ)` is the multiplication by `ψ`, so

`ψ u = Op(q) (Op(c) u) - Op(R') u`

for every tempered distribution `u`
(`TauCeti.Symbol.exists_smulLeftCLM_eq_quantizeTempered_sub_quantizeTempered`). Taking `R'` of
order `r - (s + m)`, both terms lie in `B^{s + m}_{p,q}` by the Besov mapping of symbols with
uniform estimates (`TemperedDistribution.MemBesov.quantizeTempered`).

The local regularity on distributions reduces to the interior regularity exactly as on the `H^s`
scale (`Distribution.IsLocallySobolevAt.of_quantizeDistribution`). For nested cutoffs `φ₀`, `ψ`
and `χ`, with `χ = 1` on the closed `R`-neighbourhood of the support of `ψ`,
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
open scoped ContDiff Distributions ENNReal SchwartzMap Topology

namespace TauCeti

namespace Symbol

variable {n : ℕ} {m : ℝ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  {a : Symbol n ℂ ℂ m} {b : Symbol n ℂ ℂ (-m)} {ψ : 𝓢(CoordinateSpace n, ℂ)} {c : Symbol n ℂ ℂ m}

/-- **The local parametrix identity on tempered distributions.** Let `b` be a formal left
parametrix of the scalar symbol `a` of order `m`, `1 ∼ ∑ₖ sharpTerm b a k`, let `ψ` be a compactly
supported Schwartz function, and `c` a symbol with compact spatial support which agrees with `a` at
all positions near the support of `ψ`. For every order `μ` there is a symbol `R` of order `μ` with
compact spatial support such that

`ψ u = Op(ψ b) (Op(c) u) - Op(R) u`

for every tempered distribution `u`. -/
theorem exists_smulLeftCLM_eq_quantizeTempered_sub_quantizeTempered
    (hab : IsAsymptoticSum (m := fun k : ℕ ↦ -m + m - k)
      (inclusion (by simp) (const (.id ℂ ℂ))) (b.sharpTerm a))
    (hψ : HasCompactSupport ψ) (hc : c.HasCompactSpatialSupport)
    (hca : ∀ᶠ x in 𝓝ˢ (tsupport ψ), ∀ ξ, c.coefficient (x, ξ) = a.coefficient (x, ξ)) (μ : ℝ) :
    ∃ (R : Symbol n ℂ ℂ μ) (hR : R.HasCompactSpatialSupport), ∀ u : 𝓢'(CoordinateSpace n, F),
      smulLeftCLM F (ψ : CoordinateSpace n → ℂ) u =
        quantizeTempered F (smulLeft (ψ.smooth ⊤) b)
            (hasCompactSpatialSupport_smulLeft _ hψ b).isUniform
            (quantizeTempered F c hc.isUniform u) -
          quantizeTempered F R hR.isUniform u := by
  have hψ' : ContDiff ℝ ∞ (ψ : CoordinateSpace n → ℂ) := ψ.smooth ⊤
  set ψs := ofSpatial (fun x ↦ ψ x • ContinuousLinearMap.id ℂ ℂ) (hψ'.smul contDiff_const)
  have hψs : ψs.HasCompactSpatialSupport :=
    (hasCompactSpatialSupport_ofSpatial_iff _).2 hψ.smul_right
  have hψs' := hψs.inclusion (neg_add_cancel m).ge
  have hq := hasCompactSpatialSupport_smulLeft hψ' hψ b
  have hqc := hq.sharp hc
  -- `q # c - ψ` is smoothing, so it has a representative `R` of order `μ`.
  obtain ⟨R, hR⟩ := isSmoothing_iff.1
    (isSmoothing_sharp_sub_ofSpatial hab hψ' (fun x ξ ↦ coefficient_smulLeft hψ' b (x, ξ)) hc
      hca) μ
  have hRc : R.HasCompactSpatialSupport := (hqc.sub hψs').of_coefficient_eq hR
  -- `Op(q) ∘ Op(c) = Op(q # c) = Op(R) + Op(ψ)`, and `Op(ψ)` is the multiplication by `ψ`.
  have hsum : quantizeTempered F (smulLeft hψ' b) hq.isUniform ∘L
      quantizeTempered F c hc.isUniform =
        quantizeTempered F R hRc.isUniform + smulLeftCLM F (ψ : CoordinateSpace n → ℂ) := by
    rw [← quantizeTempered_sharp hq.isUniform hc,
      quantizeTempered_congr _ ((hqc.sub hψs').add hψs').isUniform (sub_add_cancel _ _).symm,
      quantizeTempered_add (hqc.sub hψs').isUniform hψs'.isUniform,
      quantizeTempered_congr _ hRc.isUniform hR.symm,
      quantizeTempered_inclusion hψs.isUniform,
      quantizeTempered_ofSpatial_smul_id ψ hψs.isUniform]
  refine ⟨R, hRc, fun u ↦ ?_⟩
  rw [← ContinuousLinearMap.comp_apply, hsum, add_apply, add_sub_cancel_left]

variable {φ : ContDiffBump (0 : CoordinateSpace n)} {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- **Interior elliptic regularity on Besov spaces.** Let `b` be a formal left parametrix of the
scalar symbol `a` of order `m`, `1 ∼ ∑ₖ sharpTerm b a k`, let `ψ` be a compactly supported Schwartz
function, and `c` a symbol with compact spatial support which agrees with `a` at all positions near
the support of `ψ`. If the tempered distribution `u` lies in `B^r_{p,q}` and `Op(c) u` lies in
`B^s_{p,q}`, then `ψ u ∈ B^{s + m}_{p,q}`. -/
theorem memBesov_smulLeftCLM_of_memBesov_quantizeTempered [CompleteSpace F]
    (hab : IsAsymptoticSum (m := fun k : ℕ ↦ -m + m - k)
      (inclusion (by simp) (const (.id ℂ ℂ))) (b.sharpTerm a))
    (hψ : HasCompactSupport ψ) (hc : c.HasCompactSpatialSupport)
    (hca : ∀ᶠ x in 𝓝ˢ (tsupport ψ), ∀ ξ, c.coefficient (x, ξ) = a.coefficient (x, ξ))
    {r s : ℝ} {u : 𝓢'(CoordinateSpace n, F)} (hu : u.MemBesov φ r p q)
    (hcu : (quantizeTempered F c hc.isUniform u).MemBesov φ s p q) :
    (smulLeftCLM F (ψ : CoordinateSpace n → ℂ) u).MemBesov φ (s + m) p q := by
  obtain ⟨R, hR, hψu⟩ :=
    exists_smulLeftCLM_eq_quantizeTempered_sub_quantizeTempered (F := F) hab hψ hc hca (r - (s + m))
  -- `Op(ψ b)` has order `-m` and `Op(R)` has order `r - (s + m)`.
  have h₁ := hcu.quantizeTempered (hasCompactSpatialSupport_smulLeft (ψ.smooth ⊤) hψ b).isUniform
  have h₂ := hu.quantizeTempered hR.isUniform
  rw [sub_neg_eq_add] at h₁
  rw [sub_sub_cancel] at h₂
  exact hψu u ▸ h₁.sub h₂

end Symbol

end TauCeti

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
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.1 hU
  -- Nested cutoffs: `φ₀ = 1` near `x`, `ψ = 1` near the support of `φ₀`, and `χ = 1` on the
  -- closed `R`-neighbourhood of the support of `ψ`.
  obtain ⟨φ₀, hφ₀x, hφ₀s⟩ := TestFunction.exists_complex_cutoff_tsupport_subset (n := ⊤)
    (Ω := ⊤) isCompact_singleton (Metric.isOpen_ball : IsOpen (Metric.ball x (ε / 2)))
    (singleton_subset_iff.2 (Metric.mem_ball_self (half_pos hε))) (by simp)
  obtain ⟨ψ, hψ1, hψs⟩ := TestFunction.exists_complex_cutoff_tsupport_subset (n := ⊤) (Ω := ⊤)
    φ₀.hasCompactSupport.isCompact (Metric.isOpen_ball : IsOpen (Metric.ball x ε))
    (hφ₀s.trans (Metric.ball_subset_ball (by linarith))) (by simp)
  obtain ⟨χ, hχ1, -⟩ := TestFunction.exists_complex_cutoff_tsupport_subset (n := ⊤) (Ω := ⊤)
    (ψ.hasCompactSupport.isCompact.cthickening (r := R)) isOpen_univ (subset_univ _) (by simp)
  have hχψ (y : CoordinateSpace n) (hy : y ∈ Metric.cthickening R (tsupport ψ)) : χ y = 1 :=
    hχ1.self_of_nhdsSet y hy
  have hφ₀ψ : tsupport φ₀ ⊆ tsupport ψ := fun y hy ↦
    subset_tsupport _ (by simp [hψ1.self_of_nhdsSet y hy])
  -- `χ T` lies in some `B^r_{p,q}`, and `Op(ψ a) (χ T) = ψ Op(a) T ∈ B^s_{p,q}`.
  obtain ⟨r, hr⟩ := exists_memBesov_cutoffTempered φ hp
    (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ q)).ne' T χ
  set c := smulLeft ψ.contDiff a
  have hc : c.HasCompactSpatialSupport :=
    hasCompactSpatialSupport_smulLeft ψ.contDiff ψ.hasCompactSupport a
  have hca (x ξ : CoordinateSpace n) := coefficient_smulLeft ψ.contDiff a (x, ξ)
  have hcu : (quantizeTempered ℂ c hc.isUniform (T.cutoffTempered χ)).MemBesov φ s p q := by
    rw [quantizeTempered_cutoffTempered ha hc.isUniform hca hχψ T]
    exact hUs ψ (hψs.trans hεU)
  set φS : 𝓢(CoordinateSpace n, ℂ) := φ₀.hasCompactSupport.toSchwartzMap φ₀.contDiff
  have hφS : (φS : CoordinateSpace n → ℂ) = φ₀ :=
    funext (φ₀.hasCompactSupport.toSchwartzMap_toFun φ₀.contDiff)
  -- Near the support of `φ₀`, `ψ = 1`, so `c` agrees with `a` there.
  have hca' : ∀ᶠ y in 𝓝ˢ (tsupport φS), ∀ ξ, c.coefficient (y, ξ) = a.coefficient (y, ξ) := by
    rw [hφS]
    filter_upwards [hψ1] with y hy ξ
    rw [hca, hy, one_smul]
  have hreg := memBesov_smulLeftCLM_of_memBesov_quantizeTempered hab
    (hφS ▸ φ₀.hasCompactSupport) hc hca' hr hcu
  rw [hφS, smulLeftCLM_cutoffTempered T fun y hy ↦
    hχψ y (Metric.self_subset_cthickening _ (hφ₀ψ hy))] at hreg
  exact isLocallyMemBesovAt_iff_exists_memBesov_cutoffTempered.2
    ⟨φ₀, by rwa [nhdsSet_singleton] at hφ₀x, hreg⟩

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

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.WaveFrontSet.Sobolev.Smoothness
public import TauCeti.Analysis.Pseudodifferential.Composition.ProperSupport
public import TauCeti.Analysis.Pseudodifferential.ProperSupport.Distribution
public import TauCeti.Analysis.Pseudodifferential.TemperedDistribution
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.Analysis.Distribution.WaveFrontSet.Sobolev.Tempered

/-!
# Properly supported pseudodifferential operators on distributions: calculus and local regularity

Let `a` be a scalar symbol of order `m` on `ℝⁿ` whose quantization has kernel supported within
distance `R` of the diagonal (`TauCeti.Symbol.HasNearDiagonalKernel a R`). No estimate uniform in
the position is assumed. Such an operator acts on every distribution `T ∈ 𝓓'(ℝⁿ)` by
transposition (`TauCeti.Symbol.quantizeDistribution`). This file relates that action to the rest
of the calculus and proves that it loses at most `m` orders of local Sobolev regularity.

* **Composition.** `Op(a.properSharp ha b) = Op(a) ∘ Op(b)` on `𝓓'(ℝⁿ)` for properly supported
  `a` and `b` (`TauCeti.Symbol.quantizeDistribution_properSharp`), with no compact spatial
  support.
* **Agreement with the tempered extension.** If `a` agrees with a symbol `b` uniform in the
  position at the positions of an open set `U`, then on a tempered distribution `u` the
  distribution `Op(a) u` agrees on `U` with the tempered distribution
  `Op(b) u = u ∘ Op(b)ᵗ` of `TauCeti.Symbol.quantizeTempered`
  (`TauCeti.Symbol.isVanishingOn_quantizeDistribution_toDistribution_sub`). For `a` itself
  uniform the two extensions of `Op(a)` agree
  (`TauCeti.Symbol.quantizeDistribution_toDistribution`).
* **Local Sobolev regularity.** `Op(a)` maps a tempered distribution in `H^s` to a distribution
  that is `H^{s - m}` near every point
  (`TauCeti.Symbol.isLocallySobolevAt_quantizeDistribution_toDistribution`). More generally, if `T`
  is `H^s` near every point of the closed ball of radius `R` about `x`, then `Op(a) T` is
  `H^{s - m}` near `x`
  (`TauCeti.Symbol.isLocallySobolevAt_quantizeDistribution`). Hence the `H^{s - m}` singular support
  of `Op(a) T` lies in the closed `R`-neighbourhood of the `H^s` singular support of `T`, and the
  same holds for the singular supports
  (`TauCeti.Symbol.sobolevSingularSupport_quantizeDistribution_subset`,
  `TauCeti.Symbol.singularSupport_quantizeDistribution_subset_cthickening`). So `Op(a)` maps
  `H^s_loc(ℝⁿ)` to `H^{s - m}_loc(ℝⁿ)`
  (`TauCeti.Symbol.sobolevSingularSupport_quantizeDistribution_eq_empty`), and
  a smoothing symbol maps every distribution to one that is smooth near every point
  (`TauCeti.Symbol.IsSmoothing.singularSupport_quantizeDistribution_eq_empty`).

## Proof of the local regularity

Let `T` be `H^s` near every point of `closedBall x R`, for `R > 0`. Then `T` is `H^s` near every
point of a larger ball `closedBall x (R + δ)`, and a cutoff `χ` equal to `1` near that ball makes
the tempered distribution `S = χ T` an element of `H^s`
(`Distribution.memSobolev_cutoffTempered_of_forall_isLocallySobolevAt`). Split
`Op(a) T = Op(a) S + Op(a) (T - S)`.

* `T - S` vanishes on the ball of radius `R + δ` about `x`, so `Op(a) (T - S)` vanishes near `x`,
  since `Op(a)` enlarges supports by at most `R`
  (`TauCeti.Symbol.dsupport_quantizeDistribution_subset`).
* Near `x`, the symbol `a` agrees with the symbol `θ a` of compact spatial support, for a cutoff `θ`
  equal to `1` near `x`. By the agreement with the tempered extension, `Op(a) S` agrees near `x`
  with `Op(θ a) S`, which lies in `H^{s - m}` (`TauCeti.Symbol.memSobolev_quantizeTempered`).

## References

* M. E. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, §1 and
  (3.31) (Sobolev mapping after compact localization).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1 (properly
  supported operators on distributions and their composition).
-/

public section

noncomputable section

open Complex Distribution Filter MeasureTheory Metric Set TemperedDistribution TestFunction
  TopologicalSpace
open scoped ComplexConjugate ContDiff Distributions SchwartzMap

namespace TauCeti

namespace Symbol

variable {n : ℕ} {m m' R R' R'' : ℝ} {a : Symbol n ℂ ℂ m}

/-! ### Composition -/

section Composition

/-- **Properly supported operators compose on distributions.** For symbols `a` and `b` whose
quantizations have kernels supported near the diagonal, the composition symbol
`TauCeti.Symbol.properSharp` of `a` and `b` quantizes to `Op(a) ∘ Op(b)` on all distributions. No
compact spatial support is assumed. The near-diagonal kernel condition on `a` is passed to
`TauCeti.Symbol.properSharp` as finite propagation, and the kernel of the composition is supported
within the sum of the two distances (`TauCeti.Symbol.HasPropagationLE.properSharp`). -/
theorem quantizeDistribution_properSharp {b : Symbol n ℂ ℂ m'}
    (ha : a.HasNearDiagonalKernel R) (hb : b.HasNearDiagonalKernel R')
    (hc : HasNearDiagonalKernel
      (a.properSharp (hasPropagationLE_iff.2 (hasNearDiagonalKernel_iff.1 ha)) b) R'')
    (T : 𝓓'((⊤ : Opens (CoordinateSpace n)), ℂ)) :
    quantizeDistribution hc T = quantizeDistribution ha (quantizeDistribution hb T) :=
  quantizeDistribution_comp ha hb hc (fun u ↦ TestFunction.ext fun x ↦ by
    have he : ⇑(quantizeTestFunctionCLM hb u) =
        quantizeSchwartzValue b.coefficient (u.hasCompactSupport.toSchwartzMap u.contDiff) :=
      funext (quantizeTestFunctionCLM_apply hb u)
    have hu := he ▸ (quantizeTestFunctionCLM hb u).hasCompactSupport
    rw [quantizeTestFunctionCLM_apply, quantizeTestFunctionCLM_apply,
      quantizeSchwartzValue_properSharp_of_hasCompactSupport _ b hu x]
    congr 1
    exact SchwartzMap.ext fun y ↦ by simp [he]) T

end Composition

/-! ### Agreement with the tempered extension -/

section Tempered

/-- **Agreement with the tempered extension.** Let `a` agree, at the positions of a set `U`, with a
symbol `b` whose estimates are uniform in the position. Then on every tempered distribution `u`,
the distribution `Op(a) u` agrees on `U` with the tempered distribution `Op(b) u`
(`TauCeti.Symbol.quantizeTempered`). -/
theorem isVanishingOn_quantizeDistribution_toDistribution_sub (ha : a.HasNearDiagonalKernel R)
    {b : Symbol n ℂ ℂ m'} (hb : b.IsUniform) {U : Set (CoordinateSpace n)}
    (hab : ∀ x ∈ U, ∀ ξ, a.coefficient (x, ξ) = b.coefficient (x, ξ))
    (u : 𝓢'(CoordinateSpace n, ℂ)) :
    IsVanishingOn (quantizeDistribution ha (toDistribution ⊤ u) -
      toDistribution ⊤ (quantizeTempered ℂ b hb u)) U := by
  intro φ hφ
  set φc := postcompCLM (𝕜 := ℝ) ofRealCLM φ
  have hφc (x : CoordinateSpace n) : φc x = φ x := by simp [φc]
  -- On test functions supported in `U`, the transposes `Op(a)ᵗ` and `Op(b)ᵗ` agree.
  have ht : toSchwartzMapCLM ℝ (scalarTransposeTestFunctionCLM ha φc) =
      transposeUniformCLM b hb (toSchwartzMapCLM ℝ φc) := by
    refine SchwartzMap.ext fun x ↦ ?_
    rw [toSchwartzMapCLM_apply]
    refine congrFun (coe_scalarTransposeTestFunctionCLM_eq ha φc
      (transposeUniformCLM b hb _).continuous fun v ↦ ?_) x
    refine Eq.trans ?_ ((integral_mul_quantizeUniformCLM b hb (toSchwartzMapCLM ℝ v)
      (toSchwartzMapCLM ℝ φc)).trans (by simp only [toSchwartzMapCLM_apply]))
    refine integral_congr_ae (.of_forall fun x ↦ ?_)
    by_cases hx : x ∈ U
    · simp only [quantizeTestFunctionCLM_apply, quantizeUniformCLM_apply, toSchwartzMapCLM_apply]
      rw [quantizeSchwartzValue_congr_left (hab x hx)]
      exact congrArg (fun S ↦ φc x * quantizeSchwartzValue b.coefficient S x)
        (SchwartzMap.ext fun y ↦ by simp)
    · simp [hφc, image_eq_zero_of_notMem_tsupport fun h ↦ hx (hφ h)]
  rw [sub_apply, sub_eq_zero, quantizeDistribution_apply_eq_complexPairing,
    complexPairing_toDistribution, toDistribution_apply, quantizeTempered_apply_apply, ht]

/-- **The distribution and tempered extensions of `Op(a)` agree.** For a symbol `a` whose estimates
are uniform in the position and whose quantization has kernel supported near the diagonal, `Op(a)`
on the distribution of a tempered distribution `u` is the distribution of the tempered distribution
`Op(a) u`. -/
theorem quantizeDistribution_toDistribution (ha : a.HasNearDiagonalKernel R) (ha' : a.IsUniform)
    (u : 𝓢'(CoordinateSpace n, ℂ)) :
    quantizeDistribution ha (toDistribution ⊤ u) = toDistribution ⊤ (quantizeTempered ℂ a ha' u) :=
  sub_eq_zero.1 <| ContinuousLinearMap.ext fun φ ↦
    isVanishingOn_quantizeDistribution_toDistribution_sub ha ha' (U := univ)
      (fun _ _ _ ↦ rfl) u φ (subset_univ _)

end Tempered

/-! ### Local Sobolev regularity -/

section Sobolev

/-- If a distribution `D` vanishes on the ball of radius `r > R` about `x`, then `Op(a) D` vanishes
near `x`. -/
private theorem notMem_dsupport_quantizeDistribution (ha : a.HasNearDiagonalKernel R)
    {D : 𝓓'((⊤ : Opens (CoordinateSpace n)), ℂ)} {x : CoordinateSpace n} {r : ℝ} (hR : 0 < r)
    (hRr : R < r) (hD : IsVanishingOn D (ball x r)) :
    x ∉ dsupport (quantizeDistribution ha D) := fun hx ↦ by
  -- `supp (Op(a) D)` lies in the closed `R`-neighbourhood of `supp D ⊆ (ball x r)ᶜ`.
  have h := (dsupport_quantizeDistribution_subset ha D).trans (cthickening_subset_of_subset R
    (hD.disjoint_dsupport isOpen_ball).subset_compl_left) hx
  obtain ⟨y, hy, hxy⟩ := mem_thickening_iff.1 (cthickening_subset_thickening' hR hRr _ h)
  exact hy (mem_ball'.2 hxy)

/-- **Sobolev mapping on tempered distributions.** `Op(a)` maps the distribution of a tempered
distribution `S ∈ H^s` to a distribution that is `H^{s - m}` near every point. -/
theorem isLocallySobolevAt_quantizeDistribution_toDistribution (ha : a.HasNearDiagonalKernel R)
    {s : ℝ} {S : 𝓢'(CoordinateSpace n, ℂ)} (hS : S.MemSobolev s 2) (x : CoordinateSpace n) :
    (quantizeDistribution ha (toDistribution ⊤ S)).IsLocallySobolevAt (s - m) x := by
  -- Near `x`, the symbol `a` agrees with the symbol `θ a` of compact spatial support.
  obtain ⟨θ, V, hV, hxV, hθ1, -⟩ :=
    exists_eqOn_one_tsupport_subset (n := ⊤) (𝕜 := ℝ) univ_mem (Opens.mem_top x)
  set b := (cutoff ℂ θ.contDiff).comp a
  have hb : b.HasCompactSpatialSupport :=
    (hasCompactSpatialSupport_cutoff θ.contDiff θ.hasCompactSupport).comp_right a
  have hab (y : CoordinateSpace n) (hy : y ∈ V) (ξ : CoordinateSpace n) :
      a.coefficient (y, ξ) = b.coefficient (y, ξ) := by
    simp [b, coefficient_comp, hθ1 hy]
  -- So `Op(a) S` agrees near `x` with `Op(θ a) S ∈ H^{s - m}`.
  set D := quantizeDistribution ha (toDistribution ⊤ S) -
    toDistribution ⊤ (quantizeTempered ℂ b hb.isUniform S)
  have hxD : x ∉ dsupport D := fun hx ↦
    ((isVanishingOn_quantizeDistribution_toDistribution_sub ha hb.isUniform hab S).disjoint_dsupport
      hV).subset_compl_left hx hxV
  have hbS : (toDistribution ⊤ (quantizeTempered ℂ b hb.isUniform S)).IsLocallySobolevAt
      (s - m) x := by
    simpa using (memSobolev_quantizeTempered hb hS).isLocallySobolevAt_toDistribution
      (Opens.mem_top x)
  rw [← add_sub_cancel (toDistribution ⊤ (quantizeTempered ℂ b hb.isUniform S))
    (quantizeDistribution ha (toDistribution ⊤ S))]
  exact hbS.add (isLocallySobolevAt_of_notMem_dsupport (Opens.mem_top x) hxD _)

/-- **Local Sobolev regularity.** If `T` is `H^s` near every point of the closed ball of radius `R`
about `x`, then `Op(a) T` is `H^{s - m}` near `x`. -/
theorem isLocallySobolevAt_quantizeDistribution (ha : a.HasNearDiagonalKernel R)
    {T : 𝓓'((⊤ : Opens (CoordinateSpace n)), ℂ)} {s : ℝ} {x : CoordinateSpace n}
    (hT : ∀ y ∈ closedBall x R, T.IsLocallySobolevAt s y) :
    (quantizeDistribution ha T).IsLocallySobolevAt (s - m) x := by
  rcases le_or_gt R 0 with hR | hR
  · rw [ha.quantizeDistribution_eq_zero hR, zero_apply]
    exact isLocallySobolevAt_zero_iff.2 (Opens.mem_top x)
  -- `T` is `H^s` near every point of a larger closed ball `closedBall x (δ + R)`.
  have hG := isOpen_setOf_isLocallySobolevAt s T
  obtain ⟨δ, hδ, hδG⟩ := (isCompact_closedBall x R).exists_cthickening_subset_open hG hT
  rw [cthickening_closedBall hδ.le hR.le] at hδG
  -- The cut-off distribution `S = χ T` lies in `H^s`.
  obtain ⟨χ, hχ1, hχG⟩ := exists_complex_cutoff_tsupport_subset (n := ⊤)
    (isCompact_closedBall x (δ + R)) hG hδG fun y _ ↦ Opens.mem_top y
  set S := T.cutoffTempered χ
  have hS : S.MemSobolev s 2 :=
    memSobolev_cutoffTempered_of_forall_isLocallySobolevAt fun y hy ↦ hχG hy
  -- `T - S` vanishes on the ball of radius `δ + R`, so `Op(a) (T - S)` vanishes near `x`.
  have hD : IsVanishingOn (T - toDistribution ⊤ S) (ball x (δ + R)) := fun φ hφ ↦ by
    rw [sub_apply, sub_eq_zero, ← complexPairing_postcompCLM_ofRealCLM,
      ← complexPairing_postcompCLM_ofRealCLM, complexPairing_toDistribution,
      cutoffTempered_apply T χ fun y ↦ ?_]
    by_cases hy : y ∈ tsupport φ
    · simp [hχ1.self_of_nhdsSet y (ball_subset_closedBall (hφ hy))]
    · simp [image_eq_zero_of_notMem_tsupport hy]
  have hxD := notMem_dsupport_quantizeDistribution ha (by linarith) (by linarith) hD
  rw [← add_sub_cancel (toDistribution ⊤ S) T, map_add]
  exact (isLocallySobolevAt_quantizeDistribution_toDistribution ha hS x).add
    (isLocallySobolevAt_of_notMem_dsupport (Opens.mem_top x) hxD _)

/-- **The `H^s` singular support under a properly supported operator.** The `H^{s - m}` singular
support of `Op(a) T` lies in the closed `R`-neighbourhood of the `H^s` singular support of `T`. -/
theorem sobolevSingularSupport_quantizeDistribution_subset (ha : a.HasNearDiagonalKernel R)
    (s : ℝ) (T : 𝓓'((⊤ : Opens (CoordinateSpace n)), ℂ)) :
    (quantizeDistribution ha T).sobolevSingularSupport (s - m) ⊆
      cthickening R (T.sobolevSingularSupport s) := fun x hx ↦ by
  by_contra hxc
  refine absurd hx ((notMem_sobolevSingularSupport_iff (Opens.mem_top x)).2
    (isLocallySobolevAt_quantizeDistribution ha fun y hy ↦
      (notMem_sobolevSingularSupport_iff (Opens.mem_top y)).1 fun hys ↦ hxc
        (mem_cthickening_of_dist_le x y R _ hys (mem_closedBall'.1 hy))))

/-- **`Op(a)` maps `H^s_loc` to `H^{s - m}_loc`.** If `T` is `H^s` near every point, then `Op(a) T`
is `H^{s - m}` near every point. -/
theorem sobolevSingularSupport_quantizeDistribution_eq_empty (ha : a.HasNearDiagonalKernel R)
    {s : ℝ} {T : 𝓓'((⊤ : Opens (CoordinateSpace n)), ℂ)} (hT : T.sobolevSingularSupport s = ∅) :
    (quantizeDistribution ha T).sobolevSingularSupport (s - m) = ∅ :=
  subset_empty_iff.1 <| by
    simpa [hT] using sobolevSingularSupport_quantizeDistribution_subset ha s T

/-- **The singular support under a properly supported operator.** The singular support of
`Op(a) T` lies in the closed `R`-neighbourhood of the singular support of `T`. -/
theorem singularSupport_quantizeDistribution_subset_cthickening
    (ha : a.HasNearDiagonalKernel R)
    (T : 𝓓'((⊤ : Opens (CoordinateSpace n)), ℂ)) :
    (quantizeDistribution ha T).singularSupport ⊆ cthickening R T.singularSupport := fun x hx ↦ by
  by_contra hxc
  refine absurd hx ((notMem_singularSupport_iff_eventually_forall_isLocallySobolevAt
    (Opens.mem_top x)).2 ?_)
  filter_upwards [isClosed_cthickening.isOpen_compl.mem_nhds hxc] with y hy s
  -- Near every point of `closedBall y R`, `T` is smooth, so it is `H^{s + m}`.
  have h := isLocallySobolevAt_quantizeDistribution ha (s := s + m) fun z hz ↦
    (notMem_sobolevSingularSupport_iff (Opens.mem_top z)).1 fun hzs ↦ hy <|
      mem_cthickening_of_dist_le y z R _ (sobolevSingularSupport_subset_singularSupport _ T hzs)
        (mem_closedBall'.1 hz)
  simpa using h

/-- **Smoothing operators regularize distributions.** For a smoothing symbol `a` whose quantization
has kernel supported near the diagonal, `Op(a) T` is smooth near every point for every
distribution `T`: its singular support is empty. -/
theorem IsSmoothing.singularSupport_quantizeDistribution_eq_empty (ha : a.HasNearDiagonalKernel R)
    (ha' : a.IsSmoothing) (T : 𝓓'((⊤ : Opens (CoordinateSpace n)), ℂ)) :
    (quantizeDistribution ha T).singularSupport = ∅ := by
  refine eq_empty_iff_forall_notMem.2 fun x ↦
    (notMem_singularSupport_iff_eventually_forall_isLocallySobolevAt (Opens.mem_top x)).2 ?_
  -- `T` has a finite Sobolev order `t` near the closed ball of radius `R + 1` about `x`.
  obtain ⟨t, ht⟩ := T.exists_forall_isLocallySobolevAt (isCompact_closedBall x (R + 1))
    (subset_univ _)
  filter_upwards [ball_mem_nhds x one_pos] with y hy s
  -- Read `a` as a symbol of order `t - s`.
  obtain ⟨b, hb⟩ := isSmoothing_iff.1 ha' (t - s)
  have hb' : b.HasNearDiagonalKernel R := ha.of_coefficient_eq hb
  rw [quantizeDistribution_congr ha hb' hb.symm]
  have h := isLocallySobolevAt_quantizeDistribution hb' (s := t) (x := y) fun z hz ↦ ht z <|
    mem_closedBall.2 (by linarith [dist_triangle z y x, mem_ball.1 hy, mem_closedBall.1 hz])
  simpa using h

end Sobolev

end Symbol

end TauCeti

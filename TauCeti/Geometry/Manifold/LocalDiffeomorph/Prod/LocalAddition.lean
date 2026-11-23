/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Analysis.Calculus.FDeriv.Prod
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset

/-!
# Local additions on a normed space

A family of maps `A q : E → E`, `q ∈ E`, with `A q 0 = q` and with derivative the identity at
`0`, is a *local addition* near the points `q` where this holds: for small `v`, the point
`A q v` is a deformation of `q + v`. The point of a local addition in the sense of Kriegl and
Michor is that `(q, v) ↦ (q, A q v)` is a diffeomorphism from a neighbourhood of the zero section
onto a neighbourhood of the diagonal, so that maps `u` close to a map `u₀` are written uniquely
as `u = A u₀ ξ` with `ξ` small. Local additions adapted to a submanifold, for which `A q v`
stays on the submanifold exactly along tangent vectors, give the charts on spaces of maps with
boundary values on that submanifold.

This file proves the local-addition property by the inverse function theorem. Only the second
condition, on the derivative at `0`, is needed for `(q, v) ↦ (q, A q v)` to be a local
diffeomorphism. The normalization producing that condition is in
`TauCeti.Analysis.Calculus.FDeriv.NormalizeAtZero`.

* `TauCeti.isLocalDiffeomorphAt_prodMk_of_hasFDerivAt_id`: if the derivative of `A q₀` at `0` is
  the identity, then `(q, v) ↦ (q, A q v)` is a local diffeomorphism at `(q₀, 0)` when `A` is
  jointly `C^n`, `1 ≤ n`, since its derivative there is the invertible shear
  `(a, b) ↦ (a, b + L a)`, with `L` the derivative of `q ↦ A q 0` at `q₀`
  (`DifferentiableAt.hasFDerivAt_fst_prodMk_of_slices`).
* `IsCompact.exists_injOn_prodMk_isLocalDiffeomorphOn`: over a neighbourhood of a compact set of
  base points the local diffeomorphisms combine. There are an open `U` containing the compact set
  and `ε > 0` such that `(q, v) ↦ (q, A q v)` is injective and a local diffeomorphism on
  `U ×ˢ ball 0 ε`, so it is a diffeomorphism of `U ×ˢ ball 0 ε` onto an open subset of `E × E`.
  When moreover `A q 0 = q` on `U`, this open subset contains the diagonal over `U`.
* `TauCeti.exists_injOn_prodMk_isLocalDiffeomorphOn_of_eventually_eq_add`: the same on
  `univ ×ˢ ball 0 ε` for a local addition defined everywhere which is `q + v` outside a compact
  set of base points.
* `IsCompact.exists_localAddition_eventuallyEq`: on a finite-dimensional real space, a local
  addition defined near a compact set `K` extends to a local addition on the whole space,
  equal to the original one near `K` and to `q + v` far from `K`. It is the blend
  `q + v + χ q • (A q v - (q + v))` with a cutoff `χ` equal to `1` near `K`.

## References

* A. Kriegl and P. W. Michor, *The Convenient Setting of Global Analysis*, Mathematical Surveys
  and Monographs 53, American Mathematical Society, 1997, Section 42.4 (local additions).
-/

public section

open Set Filter Function Topology Metric
open scoped ContDiff Manifold

namespace TauCeti

section RCLike

variable {𝕂 : Type*} [RCLike 𝕂] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕂 E]
  [CompleteSpace E] {A : E → E → E} {q₀ : E} {n : WithTop ℕ∞}

/-- **Local additions are local diffeomorphisms.** If `A` is jointly `C^n` on an open set `s`
containing `(q₀, 0)`, with `1 ≤ n`, and `A q₀` has derivative the identity at `0`, then
`(q, v) ↦ (q, A q v)` is a `C^n` local diffeomorphism at `(q₀, 0)`. -/
theorem isLocalDiffeomorphAt_prodMk_of_hasFDerivAt_id {s : Set (E × E)}
    (hA : ContDiffOn 𝕂 n (uncurry A) s) (hs : IsOpen s) (hq₀ : (q₀, 0) ∈ s) (hn : 1 ≤ n)
    (hv : HasFDerivAt (A q₀) (ContinuousLinearMap.id 𝕂 E) 0) :
    IsLocalDiffeomorphAt 𝓘(𝕂, E × E) 𝓘(𝕂, E × E) n (fun p : E × E ↦ (p.1, A p.1 p.2))
      (q₀, 0) := by
  have hn0 : n ≠ 0 := by rintro rfl; exact absurd hn (by simp)
  have hd : DifferentiableAt 𝕂 (uncurry A) (q₀, 0) :=
    (hA.differentiableOn hn0).differentiableAt (hs.mem_nhds hq₀)
  -- The horizontal slice `q ↦ A q 0` is differentiable at `q₀`; its derivative is the shear part.
  have h0 : DifferentiableAt 𝕂 (fun q ↦ A q 0) q₀ :=
    hd.comp (g := uncurry A) (f := fun q ↦ (q, (0 : E))) q₀ (by fun_prop)
  exact isLocalDiffeomorphAt_of_fderiv_eq (e := (ContinuousLinearEquiv.refl 𝕂 E).skewProd
      (.refl 𝕂 E) (fderiv 𝕂 (fun q ↦ A q 0) q₀)) (contDiffOn_fst.prodMk hA) hs hq₀ hn
    (hd.hasFDerivAt_fst_prodMk_of_slices h0.hasFDerivAt hv).fderiv.symm

/-- **Local additions over a compact set.** Let `A` be jointly `C^n` on an open set `s`, with
`1 ≤ n`, and let `K` be a compact set with `(q, 0) ∈ s` and the derivative of `A q` at `0` the
identity for `q ∈ K`. Then there are an open set `U ⊇ K` and `ε > 0` such that
`(q, v) ↦ (q, A q v)` is injective and a `C^n` local diffeomorphism on `U ×ˢ ball 0 ε ⊆ s`. -/
theorem _root_.IsCompact.exists_injOn_prodMk_isLocalDiffeomorphOn {K : Set E} (hK : IsCompact K)
    {s : Set (E × E)} (hA : ContDiffOn 𝕂 n (uncurry A) s) (hs : IsOpen s) (hn : 1 ≤ n)
    (hKs : ∀ q ∈ K, (q, 0) ∈ s) (hv : ∀ q ∈ K, HasFDerivAt (A q) (ContinuousLinearMap.id 𝕂 E) 0) :
    ∃ U : Set E, IsOpen U ∧ K ⊆ U ∧ ∃ ε > 0, U ×ˢ ball (0 : E) ε ⊆ s ∧
      InjOn (fun p : E × E ↦ (p.1, A p.1 p.2)) (U ×ˢ ball 0 ε) ∧
      IsLocalDiffeomorphOn 𝓘(𝕂, E × E) 𝓘(𝕂, E × E) n (fun p : E × E ↦ (p.1, A p.1 p.2))
        (U ×ˢ ball 0 ε) := by
  -- `(q, v) ↦ (q, A q v)` is injective on `K ×ˢ {0}` and a local diffeomorphism at each of its
  -- points, hence injective and a local diffeomorphism on an open neighbourhood `O` of it.
  obtain ⟨O, hO, hKO, hinj, hloc⟩ := Set.InjOn.exists_isOpen_superset_isLocalDiffeomorphOn
    (f := fun p : E × E ↦ (p.1, A p.1 p.2))
    (fun p (hp : p ∈ K ×ˢ {0}) p' (hp' : p' ∈ K ×ˢ {0}) h ↦
      Prod.ext (congrArg Prod.fst h :) (hp.2.trans hp'.2.symm))
    (hK.prod isCompact_singleton) fun p hp ↦ by
    obtain ⟨q, v⟩ := p
    obtain ⟨hq, rfl⟩ := hp
    exact isLocalDiffeomorphAt_prodMk_of_hasFDerivAt_id hA hs (hKs q hq) hn (hv q hq)
  -- By the tube lemma, `O ∩ s` contains a product neighbourhood `U ×ˢ ball 0 ε` of `K ×ˢ {0}`.
  obtain ⟨U, W, hU, hW, hKU, h0W, hUW⟩ := generalized_tube_lemma hK isCompact_singleton
    (hO.inter hs) fun p hp ↦ ⟨hKO hp, by
      obtain ⟨q, v⟩ := p
      obtain ⟨hq, rfl⟩ := hp
      exact hKs q hq⟩
  obtain ⟨ε, hε, hεW⟩ := Metric.isOpen_iff.1 hW 0 (h0W rfl)
  have hUε : U ×ˢ ball 0 ε ⊆ O ∩ s := (prod_mono_right hεW).trans hUW
  exact ⟨U, hU, hKU, ε, hε, hUε.trans inter_subset_right,
    hinj.mono (hUε.trans inter_subset_left), fun p ↦ hloc ⟨p, (hUε p.property).1⟩⟩

/-- **Local additions that are the addition far away.** Let `A` be jointly `C^n` on
`univ ×ˢ ball 0 ε`, with `1 ≤ n` and `0 < ε`, with the derivative of `A q` at `0` the identity
for every `q`, and with `A q v = q + v` for `q` outside a compact set. Then for some
`0 < ε' ≤ ε` the map `(q, v) ↦ (q, A q v)` is injective and a `C^n` local diffeomorphism on
`univ ×ˢ ball 0 ε'`. -/
theorem exists_injOn_prodMk_isLocalDiffeomorphOn_of_eventually_eq_add {ε : ℝ}
    (hA : ContDiffOn 𝕂 n (uncurry A) (univ ×ˢ ball 0 ε)) (hε : 0 < ε) (hn : 1 ≤ n)
    (hv : ∀ q, HasFDerivAt (A q) (ContinuousLinearMap.id 𝕂 E) 0)
    (hadd : ∀ᶠ q in cocompact E, A q = (q + ·)) :
    ∃ ε' > 0, ε' ≤ ε ∧ InjOn (fun p : E × E ↦ (p.1, A p.1 p.2)) (univ ×ˢ ball 0 ε') ∧
      IsLocalDiffeomorphOn 𝓘(𝕂, E × E) 𝓘(𝕂, E × E) n (fun p : E × E ↦ (p.1, A p.1 p.2))
        (univ ×ˢ ball 0 ε') := by
  obtain ⟨L, hL, hLA'⟩ := mem_cocompact.1 hadd
  have hLA : ∀ q, q ∉ L → A q = (q + ·) := fun q hq ↦ hLA' hq
  -- Over a neighbourhood `U` of `L` the compact case applies.
  obtain ⟨U, -, hLU, ε', hε', -, hinj, hloc⟩ := hL.exists_injOn_prodMk_isLocalDiffeomorphOn hA
    (isOpen_univ.prod isOpen_ball) hn (fun q _ ↦ ⟨mem_univ q, mem_ball_self hε⟩)
    fun q _ ↦ hv q
  -- Off `L`, the map `(q, v) ↦ (q, A q v)` is the shear `(q, v) ↦ (q, v + q)`.
  set σ : (E × E) ≃L[𝕂] (E × E) := .skewProd (.refl 𝕂 E) (.refl 𝕂 E) (.id 𝕂 E)
  have hσ : ∀ p : E × E, p.1 ∉ L → (fun p : E × E ↦ (p.1, A p.1 p.2)) =ᶠ[𝓝 p] σ := fun p hp ↦ by
    filter_upwards [continuous_fst.continuousAt.preimage_mem_nhds
      (hL.isClosed.isOpen_compl.mem_nhds hp)] with p' hp'
    simp [σ, hLA _ hp', add_comm]
  refine ⟨min ε ε', lt_min hε hε', min_le_left _ _, ?_, fun p ↦ ?_⟩
  · rintro ⟨a, w⟩ ⟨-, hw⟩ ⟨a', w'⟩ ⟨-, hw'⟩ h
    obtain rfl : a = a' := congrArg Prod.fst h
    by_cases ha : a ∈ U
    · exact hinj ⟨ha, ball_subset_ball (min_le_right _ _) hw⟩
        ⟨ha, ball_subset_ball (min_le_right _ _) hw'⟩ h
    · have h2 := congrArg Prod.snd h
      simp only [hLA _ fun h ↦ ha (hLU h), add_right_inj] at h2
      rw [h2]
  · obtain ⟨⟨a, w⟩, -, hw⟩ := p
    by_cases ha : a ∈ U
    · exact hloc ⟨(a, w), ha, ball_subset_ball (min_le_right _ _) hw⟩
    · exact (isLocalDiffeomorphAt_of_fderiv_eq σ.contDiff.contDiffOn isOpen_univ (mem_univ _) hn
        σ.fderiv.symm).congr_of_eventuallyEq (hσ (a, w) fun h ↦ ha (hLU h))

end RCLike

section Real

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {A : E → E → E} {n : WithTop ℕ∞}

/-- **Extension of a local addition from a neighbourhood of a compact set.** Let `A` be jointly
`C^n` on an open set `s`, with `1 ≤ n ≤ ∞`, and let `K` be compact, such that near `K` the points
`(q, 0)` lie in `s`, `A q 0 = q`, and the derivative of `A q` at `0` is the identity. Then there
are a map `A'` and `ε > 0` such that `A'` is jointly `C^n` on `univ ×ˢ ball 0 ε`, `A' q 0 = q` and
`A' q` has derivative the identity at `0` for every `q`, `A' q = A q` for `q` near `K`,
`A' q v = q + v` for `q` outside a compact set, and `(q, v) ↦ (q, A' q v)` is injective and a
`C^n` local diffeomorphism on `univ ×ˢ ball 0 ε`. -/
theorem _root_.IsCompact.exists_localAddition_eventuallyEq {K : Set E} (hK : IsCompact K)
    {s : Set (E × E)} (hA : ContDiffOn ℝ n (uncurry A) s) (hs : IsOpen s) (hn : 1 ≤ n)
    (hn' : n ≤ ∞) (hKA : ∀ᶠ q in 𝓝ˢ K, (q, 0) ∈ s ∧ A q 0 = q ∧
      HasFDerivAt (A q) (ContinuousLinearMap.id ℝ E) 0) :
    ∃ A' : E → E → E, ∃ ε > 0, ContDiffOn ℝ n (uncurry A') (univ ×ˢ ball 0 ε) ∧
      (∀ q, A' q 0 = q) ∧ (∀ q, HasFDerivAt (A' q) (ContinuousLinearMap.id ℝ E) 0) ∧
      (∀ᶠ q in 𝓝ˢ K, A' q = A q) ∧ (∀ᶠ q in cocompact E, A' q = (q + ·)) ∧
      InjOn (fun p : E × E ↦ (p.1, A' p.1 p.2)) (univ ×ˢ ball 0 ε) ∧
      IsLocalDiffeomorphOn 𝓘(ℝ, E × E) 𝓘(ℝ, E × E) n (fun p : E × E ↦ (p.1, A' p.1 p.2))
        (univ ×ˢ ball 0 ε) := by
  -- An open neighbourhood `U` of `K` on which the hypotheses hold, and a cutoff `χ` equal to `1`
  -- near `K` whose support is compact and contained in `U`.
  obtain ⟨U, hU, hKU, hUA⟩ := mem_nhdsSet_iff_exists.1 hKA
  obtain ⟨χ, hχ, -, hχ1, hχc, hχU⟩ := hK.exists_contDiff_cutoff hU hKU
  have hχ0 : ∀ q, q ∉ tsupport χ → χ q = 0 := fun q hq ↦ image_eq_zero_of_notMem_tsupport hq
  -- `A` is `C^n` on a product neighbourhood of `tsupport χ × {0}`.
  obtain ⟨u, W, -, hW, hχu, h0W, huW⟩ := generalized_tube_lemma hχc.isCompact isCompact_singleton
    hs fun p hp ↦ by
      obtain ⟨q, v⟩ := p
      obtain ⟨hq, rfl⟩ := hp
      exact (hUA (hχU hq)).1
  obtain ⟨ε, hε, hεW⟩ := Metric.isOpen_iff.1 hW 0 (h0W rfl)
  set A' : E → E → E := fun q v ↦ q + v + χ q • (A q v - (q + v)) with hA'
  -- Away from `tsupport χ`, the map `A'` is the addition of `E`.
  have hA'0 : ∀ q, q ∉ tsupport χ → A' q = (q + ·) := fun q hq ↦ by
    ext v
    simp [hA', hχ0 q hq]
  have hA'zero : ∀ q, A' q 0 = q := fun q ↦ by
    by_cases hq : q ∈ tsupport χ
    · simp [hA', (hUA (hχU hq)).2.1]
    · simp [hA'0 q hq]
  have hA'v : ∀ q, HasFDerivAt (A' q) (ContinuousLinearMap.id ℝ E) 0 := fun q ↦ by
    by_cases hq : q ∈ tsupport χ
    · exact (((hasFDerivAt_id (0 : E)).const_add q).add (((hUA (hχU hq)).2.2.sub
        ((hasFDerivAt_id (0 : E)).const_add q)).const_smul (χ q))).congr_fderiv (by simp)
    · simpa [hA'0 q hq] using (hasFDerivAt_id (0 : E)).const_add q
  have hA'C : ContDiffOn ℝ n (uncurry A') (univ ×ˢ ball 0 ε) := by
    rintro ⟨q, v⟩ ⟨-, hv⟩
    refine ContDiffAt.contDiffWithinAt ?_
    by_cases hq : q ∈ u
    · exact (contDiffAt_fst.add contDiffAt_snd).add
        (((hχ.of_le hn').contDiffAt.comp _ contDiffAt_fst).smul
          ((hA.contDiffAt (hs.mem_nhds (huW ⟨hq, hεW hv⟩))).sub
            (contDiffAt_fst.add contDiffAt_snd)))
    · refine (contDiffAt_fst.add contDiffAt_snd).congr_of_eventuallyEq ?_
      filter_upwards [continuous_fst.continuousAt.preimage_mem_nhds
        ((isClosed_tsupport χ).isOpen_compl.mem_nhds fun h ↦ hq (hχu h))] with p hp
      simp [uncurry, hA'0 p.1 hp]
  have hadd : ∀ᶠ q in cocompact E, A' q = (q + ·) := by
    filter_upwards [hχc.isCompact.compl_mem_cocompact] with q hq using hA'0 q hq
  obtain ⟨ε', hε', hε'ε, hinj, hloc⟩ :=
    exists_injOn_prodMk_isLocalDiffeomorphOn_of_eventually_eq_add hA'C hε hn hA'v hadd
  refine ⟨A', ε', hε', hA'C.mono (prod_mono_right (ball_subset_ball hε'ε)), hA'zero, hA'v, ?_,
    hadd, hinj, hloc⟩
  filter_upwards [isOpen_interior.mem_nhdsSet.2 hχ1] with q hq
  have h1 : χ q = 1 := interior_subset hq
  ext v
  simp [hA', h1]

end Real

end TauCeti

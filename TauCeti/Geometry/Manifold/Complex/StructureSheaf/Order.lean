/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Coordinate
import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Domain
import Mathlib.Algebra.GroupWithZero.Divisibility
import Mathlib.Analysis.Analytic.Order
import Mathlib.Algebra.Category.Ring.FilteredColimits

/-!
# Finite vanishing order of holomorphic germs

The powers of the ideal of holomorphic germs vanishing at a point of a complex curve have
zero intersection. Consequently every nonzero germ lies in a unique last power of that
ideal. This supplies finite, intrinsic local multiplicities for divisor sheaves: the
multiplicity is measured without choosing a preferred coordinate.

The analytic input is finite vanishing order in a local chart. A germ divisible by the
`n`-th power of the centered coordinate has analytic order at least `n`; a nonzero analytic
germ cannot satisfy this for every `n`. No compactness or connectedness is required.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, §§1, 6 and 16.

The proof uses Mathlib's `natCast_le_analyticOrderAt` and the coordinate-division theorem
`OpenPartialHomeomorph.ker_eval_eq_span_holomorphicCoordinateGerm`.
-/

public noncomputable section

open CategoryTheory Filter IsManifold Opposite Set TopologicalSpace Topology
open scoped ContDiff Manifold
open TauCeti TauCeti.holomorphicStructureSheaf

namespace OpenPartialHomeomorph

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
  (e : OpenPartialHomeomorph X ℂ) (he : e ∈ maximalAtlas 𝓘(ℂ) 1 X) (x : X)

/-- A nonzero holomorphic germ is not divisible by arbitrarily high powers of a centered
chart coordinate. -/
theorem exists_not_dvd_holomorphicCoordinateGerm_pow (hx : x ∈ e.source)
    {f : (holomorphicStructureSheaf 𝓘(ℂ) X).presheaf.stalk x} (hf : f ≠ 0) :
    ∃ n : ℕ, ¬ holomorphicCoordinateGerm e he x hx ^ n ∣ f := by
  classical
  let S := (holomorphicStructureSheaf 𝓘(ℂ) X).presheaf
  obtain ⟨U, hxU, s, hs⟩ := S.exists_germ_eq f
  let F : X → ℂ := Function.extend Subtype.val s (fun _ => 0)
  let A : ℂ → ℂ := F ∘ e.symm
  have hF (y : U) : F y = s y := Subtype.val_injective.extend_apply _ _ y
  have hA : AnalyticAt ℂ A (e x) :=
    e.analyticAt_holomorphicSection_extend_comp_symm he x hx U hxU s
  -- Infinite analytic order would make the original germ zero on a smaller neighborhood.
  have hfinite : analyticOrderAt A (e x) ≠ ⊤ := by
    intro htop
    have hzero : ∀ᶠ y in 𝓝 x, F y = 0 := by
      filter_upwards [(e.continuousAt hx).eventually (analyticOrderAt_eq_top.mp htop),
        e.open_source.mem_nhds hx] with y hy hye
      simpa only [A, Function.comp_apply, e.left_inv hye] using hy
    obtain ⟨V, hV, hVopen, hxV⟩ := eventually_nhds_iff.mp hzero
    let W : Opens X := U ⊓ ⟨V, hVopen⟩
    have hxW : x ∈ W := ⟨hxU, hxV⟩
    have hres : S.map (homOfLE (inf_le_left : W ≤ U)).op s = 0 := by
      apply holomorphicStructureSheaf.ext
      intro y
      rw [map_apply, holomorphicStructureSheaf.zero_apply, ← hF]
      exact hV y y.2.2
    apply hf
    rw [← hs, ← S.germ_res_apply (homOfLE (inf_le_left : W ≤ U)) x hxW,
      hres, map_zero]
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hfinite
  refine ⟨n + 1, fun hdiv => ?_⟩
  -- A putative divisibility relation gives an analytic factorization in the same chart.
  obtain ⟨q, hq⟩ := hdiv
  obtain ⟨V, hVe, hxV, t, ht⟩ := S.exists_le_germ_eq q (V := ⟨e.source, e.open_source⟩) hx
  let c := holomorphicCoordinateSection e he (e x)
  let b : S.obj (op V) := S.map (homOfLE hVe).op c ^ (n + 1) * t
  have hb : S.germ V x hxV b = f := by
    simp only [b, map_mul, map_pow, S.germ_res_apply, ht]
    simpa only [holomorphicCoordinateGerm_def] using hq.symm
  obtain ⟨W, hxW, iU, iV, hW⟩ := S.germ_eq x hxU hxV s b (hs.trans hb.symm)
  let Q : ℂ → ℂ := (Function.extend Subtype.val t (fun _ => 0)) ∘ e.symm
  have hQ : AnalyticAt ℂ Q (e x) :=
    e.analyticAt_holomorphicSection_extend_comp_symm he x hx V hxV t
  have heq : A =ᶠ[𝓝 (e x)] fun z => (z - e x) ^ (n + 1) * Q z := by
    filter_upwards [(e.tendsto_symm hx).eventually (W.isOpen.mem_nhds hxW),
      e.open_target.mem_nhds (e.map_source hx)] with z hzW hz
    have hsz := congrArg (fun r => toFun 𝓘(ℂ) X (op W) r ⟨e.symm z, hzW⟩) hW
    dsimp only [S] at hsz
    simp only [map_apply] at hsz
    dsimp only [b, S] at hsz
    rw [mul_apply, pow_apply, map_apply,
      holomorphicCoordinateSection_apply e he (e x), e.right_inv hz] at hsz
    simpa only [A, Q, F, Function.comp_apply,
      Subtype.val_injective.extend_apply _ _ ⟨e.symm z, (leOfHom iU) hzW⟩,
      Subtype.val_injective.extend_apply _ _ ⟨e.symm z, (leOfHom iV) hzW⟩] using hsz
  have hbound : ((n + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt A (e x) :=
    (natCast_le_analyticOrderAt hA).mpr ⟨Q, hQ, heq⟩
  rw [← hn] at hbound
  exact (by exact_mod_cast hbound : n + 1 ≤ n) |>.not_gt (Nat.lt_succ_self n)

/-- The `n`-th power of a centered coordinate vanishes to exactly order `n`, measured by
powers of the evaluation kernel. In particular every finite multiplicity occurs. -/
@[simp]
theorem holomorphicCoordinateGerm_pow_mem_pow_ker_eval_iff (hx : x ∈ e.source) (n j : ℕ) :
    holomorphicCoordinateGerm e he x hx ^ n ∈ RingHom.ker (eval 𝓘(ℂ) X x) ^ j ↔ j ≤ n := by
  rw [ker_eval_eq_span_holomorphicCoordinateGerm e he x hx,
    Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  apply pow_dvd_pow_iff (holomorphicCoordinateGerm_ne_zero e he x hx)
  intro hunit
  have h := (hunit.map (eval 𝓘(ℂ) X x)).ne_zero
  exact h (eval_holomorphicCoordinateGerm e he x hx)

end OpenPartialHomeomorph

namespace TauCeti.holomorphicStructureSheaf

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]

/-- The vanishing ideal of holomorphic germs on a complex curve is separated: a germ in
every power of that ideal is zero. -/
theorem iInf_pow_ker_eval_eq_bot (x : X) :
    (⨅ n : ℕ, RingHom.ker (eval 𝓘(ℂ) X x) ^ n) = ⊥ := by
  apply le_antisymm _ bot_le
  intro f hf
  by_contra hne
  have hf0 : f ≠ 0 := by simpa only [Ideal.mem_bot] using hne
  obtain ⟨n, hn⟩ := (chartAt ℂ x).exists_not_dvd_holomorphicCoordinateGerm_pow
    (chart_mem_maximalAtlas x) x (mem_chart_source ℂ x) hf0
  have hmem := (Ideal.mem_iInf.mp hf) n
  rw [(chartAt ℂ x).ker_eval_eq_span_holomorphicCoordinateGerm
    (chart_mem_maximalAtlas x) x (mem_chart_source ℂ x), Ideal.span_singleton_pow,
    Ideal.mem_span_singleton] at hmem
  exact hn hmem

/-- A nonzero holomorphic germ has a unique finite vanishing multiplicity, characterized
intrinsically by consecutive powers of the evaluation kernel. -/
theorem existsUnique_mem_pow_ker_eval_notMem_succ (x : X)
    {f : (holomorphicStructureSheaf 𝓘(ℂ) X).presheaf.stalk x} (hf : f ≠ 0) :
    ∃! n : ℕ, f ∈ RingHom.ker (eval 𝓘(ℂ) X x) ^ n ∧
      f ∉ RingHom.ker (eval 𝓘(ℂ) X x) ^ (n + 1) := by
  classical
  let I := RingHom.ker (eval 𝓘(ℂ) X x)
  have hex : ∃ n : ℕ, f ∉ I ^ n := by
    by_contra h
    have hmem : f ∈ ⨅ n : ℕ, I ^ n := Ideal.mem_iInf.mpr (by simpa using h)
    rw [iInf_pow_ker_eval_eq_bot] at hmem
    exact hf hmem
  have hm : f ∉ I ^ Nat.find hex := Nat.find_spec hex
  have hm0 : Nat.find hex ≠ 0 := by intro h; simp [h] at hm
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hm0
  have hnmem : f ∈ I ^ n := by
    exact not_not.mp (Nat.find_min hex (by omega))
  rw [hn] at hm
  refine ⟨n, ⟨hnmem, hm⟩, ?_⟩
  intro j hj
  apply le_antisymm
  · by_contra h
    exact hm (Ideal.pow_le_pow_right (by omega : n + 1 ≤ j) hj.1)
  · by_contra h
    exact hj.2 (Ideal.pow_le_pow_right (by omega : j + 1 ≤ n) hnmem)

end TauCeti.holomorphicStructureSheaf

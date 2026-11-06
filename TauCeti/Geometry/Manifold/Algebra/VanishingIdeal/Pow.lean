/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Algebra.VanishingIdeal.Basic
public import TauCeti.RingTheory.Derivation.DifferentialOperator
import TauCeti.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Geometry.Manifold.ContMDiffMap.ExtChartAt

/-!
# Powers of the vanishing ideal of a point and finite jets

Let `x` be an interior point of a finite-dimensional Hausdorff smooth real manifold `M`, and let
`I_x` be the ideal of smooth real functions vanishing at `x`. This file identifies every power of
`I_x`: a smooth function lies in `I_x ^ n`, the ideal of finite sums of products of `n` functions
vanishing at `x`, exactly when all its derivatives of order less than `n` vanish at `x` in the
extended chart at `x`. Equivalently, two smooth functions agree modulo `I_x ^ (m + 1)` exactly when
they have the same derivatives of order at most `m` at `x`, that is, the same `m`-jet at `x`. So the
`m`-jets of functions at `x`, defined as these classes of functions, are the elements of the
quotient `C^∞(M) / I_x ^ (m + 1)`.

For `n = 2` this is `TauCeti.mem_smoothVanishingIdeal_sq_iff_of_isInteriorPoint`. The nontrivial
inclusion is the higher-order Hadamard lemma for the vanishing ideal,
`TauCeti.mem_smoothVanishingIdeal_pow_of_iteratedFDeriv_eq_zero`. The reverse inclusion is the
Leibniz rule (`TauCeti.iteratedFDeriv_mul_eq_zero_of_lt`).

Combined with `TauCeti.apply_mem_smul_top_of_mem_pow_smul_top`, this shows that a differential
operator of order at most `m` on `C^∞(M)`, in Grothendieck's algebraic sense
(`TauCeti.differentialOperators`), factors through `m`-jets: the value of `D f` at `x` depends only
on the derivatives of `f` of order at most `m` at `x`.

## Main results

* `TauCeti.mem_smoothVanishingIdeal_pow_iff_of_isInteriorPoint`: at an interior point,
  `f ∈ I_x ^ n` if and only if the derivatives of order less than `n` of `f` vanish at `x` in the
  extended chart at `x`.
* `TauCeti.mem_smoothVanishingIdeal_pow_iff`: the same at every point of a boundaryless manifold.
* `TauCeti.sub_mem_smoothVanishingIdeal_pow_iff_of_isInteriorPoint`: two functions agree modulo
  `I_x ^ n` if and only if they have the same derivatives of order less than `n` at `x`.
* `TauCeti.apply_eq_apply_of_iteratedFDeriv_eq`: a differential operator of order at most `m` on
  `C^∞(M)` gives the same value at `x` on two functions with the same `m`-jet at `x`.

## References

* I. Kolář, P. W. Michor, J. Slovák, *Natural operations in differential geometry*, Springer,
  1993, §§1.3–1.6 and §12.
* A. Grothendieck, *Éléments de géométrie algébrique IV*, Quatrième partie, §16.8.
-/

public section

open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable [T2Space M]

/-- The chart expression of a function in `I_x ^ n` has vanishing derivatives of every order less
than `n` at the image of an interior point `x`. -/
theorem iteratedFDeriv_comp_extChartAt_symm_eq_zero_of_mem_pow {x : M}
    (hx : I.IsInteriorPoint x) {n : ℕ} {f : C^∞⟮I, M; ℝ⟯} (hf : f ∈ smoothVanishingIdeal I x ^ n)
    {k : ℕ} (hk : k < n) :
    iteratedFDeriv ℝ k (f ∘ (extChartAt I x).symm) (extChartAt I x x) = 0 := by
  obtain ⟨F, hF⟩ := exists_contMDiffMap_eventuallyEq_extChartAt (I := I) x
  -- Work with global smooth representatives in the chart, where the Leibniz rule applies.
  suffices h : ∀ n, ∀ f ∈ smoothVanishingIdeal I x ^ n, ∀ g : C^∞⟮modelWithCornersSelf ℝ E, E; ℝ⟯,
      (f : M → ℝ) =ᶠ[𝓝 x] g ∘ F → ∀ k < n, iteratedFDeriv ℝ k g (F x) = 0 by
    obtain ⟨g, hg, hgk⟩ := exists_comp_eventuallyEq_iteratedFDeriv_eq hx hF f
    rw [hgk]
    exact h n f hf g hg k hk
  intro n
  induction n with
  | zero => intro _ _ _ _ k hk; omega
  | succ n ih =>
    intro f hf
    rw [pow_succ'] at hf
    refine Submodule.mul_induction_on hf (fun a ha b hb g hg k hk ↦ ?_)
      (fun a b iha ihb g hg k hk ↦ ?_)
    · obtain ⟨ga, hga, -⟩ := exists_comp_eventuallyEq_iteratedFDeriv_eq hx hF a
      obtain ⟨gb, hgb, -⟩ := exists_comp_eventuallyEq_iteratedFDeriv_eq hx hF b
      -- `g` and `ga * gb` agree near `F x`, since both recover `a * b` near `x`.
      have hgab : (g : E → ℝ) =ᶠ[𝓝 (F x)] fun y ↦ ga y * gb y :=
        eventuallyEq_of_comp_eventuallyEq hx hF hg (by
          filter_upwards [hga, hgb] with y hya hyb
          simp [hya, hyb])
      rw [(hgab.iteratedFDeriv ℝ k).eq_of_nhds]
      refine iteratedFDeriv_mul_eq_zero_of_lt (a := 1) (b := n)
        (ga.contMDiff.contDiff.of_le (by simp)) (gb.contMDiff.contDiff.of_le (by simp))
        (fun i hi ↦ ?_) (ih b hb gb hgb) (by omega)
      rw [Nat.lt_one_iff.mp hi, ← norm_eq_zero, norm_iteratedFDeriv_zero,
        show ga (F x) = a x from hga.eq_of_nhds.symm, mem_smoothVanishingIdeal_iff.mp ha,
        norm_zero]
    · obtain ⟨ga, hga, -⟩ := exists_comp_eventuallyEq_iteratedFDeriv_eq hx hF a
      obtain ⟨gb, hgb, -⟩ := exists_comp_eventuallyEq_iteratedFDeriv_eq hx hF b
      have hgab : (g : E → ℝ) =ᶠ[𝓝 (F x)] ga + gb :=
        eventuallyEq_of_comp_eventuallyEq hx hF hg (by
          filter_upwards [hga, hgb] with y hya hyb
          simp [hya, hyb])
      rw [(hgab.iteratedFDeriv ℝ k).eq_of_nhds, iteratedFDeriv_add_apply
        (ga.contMDiff.contDiff.contDiffAt.of_le (by simp))
        (gb.contMDiff.contDiff.contDiffAt.of_le (by simp)),
        iha ga hga k hk, ihb gb hgb k hk, add_zero]

/-- **Powers of the vanishing ideal.** At an interior point `x` of a finite-dimensional Hausdorff
real manifold, a smooth function is a finite sum of products of `n` smooth functions vanishing at
`x` if and only if all derivatives of order less than `n` of its expression in the extended chart
at `x` vanish at the image of `x`. -/
theorem mem_smoothVanishingIdeal_pow_iff_of_isInteriorPoint {x : M} (hx : I.IsInteriorPoint x)
    (n : ℕ) (f : C^∞⟮I, M; ℝ⟯) :
    f ∈ smoothVanishingIdeal I x ^ n ↔
      ∀ k < n, iteratedFDeriv ℝ k (f ∘ (extChartAt I x).symm) (extChartAt I x x) = 0 :=
  ⟨fun hf _ hk ↦ iteratedFDeriv_comp_extChartAt_symm_eq_zero_of_mem_pow hx hf hk,
    mem_smoothVanishingIdeal_pow_of_iteratedFDeriv_eq_zero hx⟩

/-- **Powers of the vanishing ideal.** On a finite-dimensional Hausdorff boundaryless real
manifold, a smooth function is a finite sum of products of `n` smooth functions vanishing at `x`
if and only if all derivatives of order less than `n` of its expression in the extended chart at
`x` vanish at the image of `x`. -/
theorem mem_smoothVanishingIdeal_pow_iff [BoundarylessManifold I M] (x : M) (n : ℕ)
    (f : C^∞⟮I, M; ℝ⟯) :
    f ∈ smoothVanishingIdeal I x ^ n ↔
      ∀ k < n, iteratedFDeriv ℝ k (f ∘ (extChartAt I x).symm) (extChartAt I x x) = 0 :=
  mem_smoothVanishingIdeal_pow_iff_of_isInteriorPoint BoundarylessManifold.isInteriorPoint n f

/-- **Jets are classes modulo powers of the vanishing ideal.** At an interior point `x`, two smooth
functions agree modulo `I_x ^ n` if and only if their chart expressions have the same derivatives of
every order less than `n` at the image of `x`. -/
theorem sub_mem_smoothVanishingIdeal_pow_iff_of_isInteriorPoint {x : M}
    (hx : I.IsInteriorPoint x) (n : ℕ) (f g : C^∞⟮I, M; ℝ⟯) :
    f - g ∈ smoothVanishingIdeal I x ^ n ↔
      ∀ k < n, iteratedFDeriv ℝ k (f ∘ (extChartAt I x).symm) (extChartAt I x x) =
        iteratedFDeriv ℝ k (g ∘ (extChartAt I x).symm) (extChartAt I x x) := by
  obtain ⟨F, hF⟩ := exists_contMDiffMap_eventuallyEq_extChartAt (I := I) x
  obtain ⟨gf, hgf, hgfk⟩ := exists_comp_eventuallyEq_iteratedFDeriv_eq hx hF f
  obtain ⟨gg, hgg, hggk⟩ := exists_comp_eventuallyEq_iteratedFDeriv_eq hx hF g
  -- The chart expression of `f - g` is represented by `gf - gg`.
  have hsub (k : ℕ) : iteratedFDeriv ℝ k ((f - g : C^∞⟮I, M; ℝ⟯) ∘ (extChartAt I x).symm)
      (extChartAt I x x) = iteratedFDeriv ℝ k gf (F x) - iteratedFDeriv ℝ k gg (F x) := by
    rw [← iteratedFDeriv_sub_apply (gf.contMDiff.contDiff.contDiffAt.of_le (by simp))
      (gg.contMDiff.contDiff.contDiffAt.of_le (by simp)), hF.eq_of_nhds]
    refine ((comp_extChartAt_symm_eventuallyEq hx hF ?_).iteratedFDeriv ℝ k).eq_of_nhds
    exact hgf.sub hgg
  simp_rw [mem_smoothVanishingIdeal_pow_iff_of_isInteriorPoint hx, hsub, hgfk, hggk, sub_eq_zero]

/-- **Differential operators factor through jets.** At an interior point `x`, a differential
operator of order at most `m` on the smooth functions, in Grothendieck's algebraic sense, takes the
same value at `x` on two functions whose chart expressions have the same derivatives of order at
most `m` at the image of `x`. -/
theorem apply_eq_apply_of_iteratedFDeriv_eq {x : M} (hx : I.IsInteriorPoint x) {m : ℕ}
    {D : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯}
    (hD : D ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ m)
    {f g : C^∞⟮I, M; ℝ⟯}
    (hfg : ∀ k ≤ m, iteratedFDeriv ℝ k (f ∘ (extChartAt I x).symm) (extChartAt I x x) =
      iteratedFDeriv ℝ k (g ∘ (extChartAt I x).symm) (extChartAt I x x)) :
    D f x = D g x := by
  have h := apply_mem_smul_top_of_mem_pow_smul_top hD (smoothVanishingIdeal I x)
    (x := f - g) (by
      rw [Ideal.smul_eq_mul, Ideal.mul_top]
      exact (sub_mem_smoothVanishingIdeal_pow_iff_of_isInteriorPoint hx (m + 1) f g).mpr
        fun k hk ↦ hfg k (Nat.lt_succ_iff.mp hk))
  rw [Ideal.smul_eq_mul, Ideal.mul_top, mem_smoothVanishingIdeal_iff, map_sub,
    ContMDiffMap.coe_sub, Pi.sub_apply, sub_eq_zero] at h
  exact h

end TauCeti

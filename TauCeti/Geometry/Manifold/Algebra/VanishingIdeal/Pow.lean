/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Algebra.VanishingIdeal.Basic
public import TauCeti.RingTheory.Derivation.DifferentialOperator
import TauCeti.Analysis.Calculus.IteratedFDeriv.Mul
import TauCeti.Geometry.Manifold.ContMDiffMap.ExtChartAt

/-!
# Powers of the vanishing ideal of a point and jets of smooth functions

Let `I_x` be the ideal of smooth real functions on a manifold `M` vanishing at an interior point
`x`, and write `φ = extChartAt I x` for the extended chart at `x`. For every `m`, the power
`I_x ^ (m + 1)`, the ideal of finite sums of products of `m + 1` functions vanishing at `x`,
consists exactly of the smooth functions `f` whose chart expression `f ∘ φ⁻¹` has vanishing
derivatives of every order at most `m` at `φ x`. Consequently the quotient `C^∞(M) / I_x ^ (m + 1)`
is the space of `m`-jets of smooth functions at `x`: two functions have the same class exactly
when their chart expressions have the same Taylor coefficients of order at most `m`.

Combined with the algebraic fact that a differential operator of order at most `m`, in
Grothendieck's sense of iterated commutators with multiplication operators, maps
`I_x ^ (m + 1)` into `I_x`, this shows that such an operator on `C^∞(M)` is local of order `m`:
the value `(D f)(x)` depends only on the `m`-jet of `f` at `x`. No continuity of `D` is assumed.

The inclusion of `I_x ^ (m + 1)` in the functions with vanishing `m`-jet holds because orders of
vanishing add under multiplication. The converse is Hadamard's lemma of order `m`,
`TauCeti.mem_smoothVanishingIdeal_pow_succ_of_iteratedFDeriv_eq_zero`, proved in
`TauCeti.Geometry.Manifold.Algebra.VanishingIdeal.Basic`. The case `m = 1` is
`TauCeti.mem_smoothVanishingIdeal_sq_iff_of_isInteriorPoint`.

## Main results

* `TauCeti.mem_smoothVanishingIdeal_pow_succ_iff_of_isInteriorPoint`: at an interior point of a
  finite-dimensional Hausdorff manifold, `f ∈ I_x ^ (m + 1)` if and only if the derivatives of
  order at most `m` of `f ∘ φ⁻¹` vanish at `φ x`.
* `TauCeti.mem_smoothVanishingIdeal_pow_succ_iff`: the same at every point of a boundaryless
  manifold.
* `TauCeti.quotient_mk_smoothVanishingIdeal_pow_succ_eq_iff`: two smooth functions have the same
  class modulo `I_x ^ (m + 1)` if and only if their chart expressions have the same derivatives of
  order at most `m` at `φ x`.
* `TauCeti.differentialOperators_apply_eq_of_iteratedFDeriv_eq`: a differential operator of order
  at most `m` on `C^∞(M)` takes the same value at `x` on two functions with the same `m`-jet at
  `x`.

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
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

/-- A function in `I_x ^ (m + 1)` has a chart expression whose derivatives of order at most `m`
vanish at the image of `x`. -/
theorem iteratedFDeriv_comp_extChartAt_symm_eq_zero_of_mem_smoothVanishingIdeal_pow {x : M}
    (hx : I.IsInteriorPoint x) {m : ℕ} {f : C^∞⟮I, M; ℝ⟯}
    (hf : f ∈ smoothVanishingIdeal I x ^ (m + 1)) {k : ℕ} (hk : k ≤ m) :
    iteratedFDeriv ℝ k ((f : M → ℝ) ∘ (extChartAt I x).symm) (extChartAt I x x) = 0 := by
  induction m generalizing f k with
  | zero =>
    obtain rfl : k = 0 := by omega
    rw [zero_add, pow_one, mem_smoothVanishingIdeal_iff] at hf
    rw [← norm_eq_zero, norm_iteratedFDeriv_zero, Function.comp_apply, extChartAt_to_inv, hf,
      norm_zero]
  | succ m ih =>
    rw [pow_succ] at hf
    refine Submodule.mul_induction_on
      (C := fun r : C^∞⟮I, M; ℝ⟯ ↦ ∀ k ≤ m + 1,
        iteratedFDeriv ℝ k ((r : M → ℝ) ∘ (extChartAt I x).symm) (extChartAt I x x) = 0)
      hf (fun u hu v hv k hk ↦ ?_) (fun u v hu hv k hk ↦ ?_) k hk
    · -- Orders of vanishing add: `u` vanishes to order `m + 1` and `v` to order `1`.
      obtain ⟨gu, hgu, hu'⟩ := exists_contDiff_comp_extChartAt_symm_eventuallyEq hx u
      obtain ⟨gv, hgv, hv'⟩ := exists_contDiff_comp_extChartAt_symm_eventuallyEq hx v
      have huv : ((u * v : C^∞⟮I, M; ℝ⟯) : M → ℝ) ∘ (extChartAt I x).symm =ᶠ[𝓝 _]
          fun y ↦ gu y * gv y := hu'.mul hv'
      rw [(huv.iteratedFDeriv ℝ k).eq_of_nhds]
      refine iteratedFDeriv_mul_eq_zero_of_lt_add (a := m + 1) (b := 1) (hgu.of_le (by simp))
        (hgv.of_le (by simp)) (fun i hi ↦ ?_) (fun i hi ↦ ?_) (by omega)
      · rw [← (hu'.iteratedFDeriv ℝ i).eq_of_nhds]
        exact ih hu (by omega)
      · obtain rfl : i = 0 := by omega
        rw [← (hv'.iteratedFDeriv ℝ 0).eq_of_nhds, ← norm_eq_zero, norm_iteratedFDeriv_zero,
          Function.comp_apply, extChartAt_to_inv, mem_smoothVanishingIdeal_iff.1 hv, norm_zero]
    · obtain ⟨gu, hgu, hu'⟩ := exists_contDiff_comp_extChartAt_symm_eventuallyEq hx u
      obtain ⟨gv, hgv, hv'⟩ := exists_contDiff_comp_extChartAt_symm_eventuallyEq hx v
      have huv : ((u + v : C^∞⟮I, M; ℝ⟯) : M → ℝ) ∘ (extChartAt I x).symm =ᶠ[𝓝 _] gu + gv :=
        hu'.add hv'
      rw [(huv.iteratedFDeriv ℝ k).eq_of_nhds,
        iteratedFDeriv_add_apply (hgu.contDiffAt.of_le (by simp))
          (hgv.contDiffAt.of_le (by simp)),
        ← (hu'.iteratedFDeriv ℝ k).eq_of_nhds, ← (hv'.iteratedFDeriv ℝ k).eq_of_nhds,
        hu k hk, hv k hk, add_zero]

/-- **The powers of the vanishing ideal.** At an interior point `x` of a finite-dimensional
Hausdorff real manifold, a smooth function is a finite sum of products of `m + 1` smooth functions
vanishing at `x` if and only if its chart expression has vanishing derivatives of every order at
most `m` at the image of `x`. -/
theorem mem_smoothVanishingIdeal_pow_succ_iff_of_isInteriorPoint {x : M}
    (hx : I.IsInteriorPoint x) (m : ℕ) (f : C^∞⟮I, M; ℝ⟯) :
    f ∈ smoothVanishingIdeal I x ^ (m + 1) ↔ ∀ k ≤ m,
      iteratedFDeriv ℝ k ((f : M → ℝ) ∘ (extChartAt I x).symm) (extChartAt I x x) = 0 :=
  ⟨fun hf _ hk ↦
    iteratedFDeriv_comp_extChartAt_symm_eq_zero_of_mem_smoothVanishingIdeal_pow hx hf hk,
    mem_smoothVanishingIdeal_pow_succ_of_iteratedFDeriv_eq_zero hx⟩

/-- **The powers of the vanishing ideal.** On a finite-dimensional Hausdorff boundaryless real
manifold, a smooth function is a finite sum of products of `m + 1` smooth functions vanishing at
`x` if and only if its chart expression has vanishing derivatives of every order at most `m` at
the image of `x`. -/
theorem mem_smoothVanishingIdeal_pow_succ_iff [BoundarylessManifold I M] (x : M) (m : ℕ)
    (f : C^∞⟮I, M; ℝ⟯) :
    f ∈ smoothVanishingIdeal I x ^ (m + 1) ↔ ∀ k ≤ m,
      iteratedFDeriv ℝ k ((f : M → ℝ) ∘ (extChartAt I x).symm) (extChartAt I x x) = 0 :=
  mem_smoothVanishingIdeal_pow_succ_iff_of_isInteriorPoint BoundarylessManifold.isInteriorPoint m f

/-- **Jets as quotients.** At an interior point `x`, two smooth functions have the same class in
`C^∞(M) / I_x ^ (m + 1)`, the space of `m`-jets at `x`, if and only if their chart expressions have
the same derivatives of every order at most `m` at the image of `x`. -/
theorem quotient_mk_smoothVanishingIdeal_pow_succ_eq_iff {x : M} (hx : I.IsInteriorPoint x)
    (m : ℕ) (f g : C^∞⟮I, M; ℝ⟯) :
    Ideal.Quotient.mk (smoothVanishingIdeal I x ^ (m + 1)) f =
        Ideal.Quotient.mk (smoothVanishingIdeal I x ^ (m + 1)) g ↔
      ∀ k ≤ m, iteratedFDeriv ℝ k ((f : M → ℝ) ∘ (extChartAt I x).symm) (extChartAt I x x) =
        iteratedFDeriv ℝ k ((g : M → ℝ) ∘ (extChartAt I x).symm) (extChartAt I x x) := by
  obtain ⟨u, hu, hfu⟩ := exists_contDiff_comp_extChartAt_symm_eventuallyEq hx f
  obtain ⟨v, hv, hgv⟩ := exists_contDiff_comp_extChartAt_symm_eventuallyEq hx g
  have hsub : ((f - g : C^∞⟮I, M; ℝ⟯) : M → ℝ) ∘ (extChartAt I x).symm =ᶠ[𝓝 _] u - v :=
    hfu.sub hgv
  rw [Ideal.Quotient.eq, mem_smoothVanishingIdeal_pow_succ_iff_of_isInteriorPoint hx]
  refine forall₂_congr fun k _ ↦ ?_
  rw [(hsub.iteratedFDeriv ℝ k).eq_of_nhds, (hfu.iteratedFDeriv ℝ k).eq_of_nhds,
    (hgv.iteratedFDeriv ℝ k).eq_of_nhds,
    iteratedFDeriv_sub_apply (hu.contDiffAt.of_le (by simp)) (hv.contDiffAt.of_le (by simp)),
    sub_eq_zero]

/-- **Differential operators factor through jets.** At an interior point `x`, a differential
operator of order at most `m` on `C^∞(M)`, in the sense of iterated commutators with
multiplication operators, takes the same value at `x` on two smooth functions whose chart
expressions have the same derivatives of every order at most `m` at the image of `x`. -/
theorem differentialOperators_apply_eq_of_iteratedFDeriv_eq {m : ℕ}
    {D : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯}
    (hD : D ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ m) {x : M}
    (hx : I.IsInteriorPoint x) {f g : C^∞⟮I, M; ℝ⟯}
    (hfg : ∀ k ≤ m,
      iteratedFDeriv ℝ k ((f : M → ℝ) ∘ (extChartAt I x).symm) (extChartAt I x x) =
        iteratedFDeriv ℝ k ((g : M → ℝ) ∘ (extChartAt I x).symm) (extChartAt I x x)) :
    D f x = D g x := by
  have hmem : f - g ∈ smoothVanishingIdeal I x ^ (m + 1) := by
    rw [← Ideal.Quotient.eq]
    exact (quotient_mk_smoothVanishingIdeal_pow_succ_eq_iff hx m f g).mpr hfg
  have h := apply_mem_smul_top_of_mem_pow_smul_top hD (smoothVanishingIdeal I x)
    (x := f - g) (by simpa using hmem)
  rw [smul_eq_mul, Ideal.mul_top, map_sub, mem_smoothVanishingIdeal_iff, ContMDiffMap.coe_sub,
    Pi.sub_apply, sub_eq_zero] at h
  exact h

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Algebra.VanishingIdeal.Basic
public import TauCeti.RingTheory.Derivation.DifferentialOperator
import Mathlib.Geometry.Manifold.BumpFunction
import TauCeti.Analysis.Calculus.IteratedFDeriv.Mul
import TauCeti.Geometry.Manifold.ContMDiffMap.ExtChartAt
import TauCeti.Geometry.Manifold.ContMDiffMap.Hadamard

/-!
# Powers of the vanishing ideal of a point and jets

Let `I_x` be the ideal of smooth real functions on a manifold `M` vanishing at `x`. At an interior
point `x` of a finite-dimensional Hausdorff manifold, the power `I_x ^ n`, whose elements are the
finite sums of products of `n` functions vanishing at `x`, consists exactly of the functions whose
iterated derivatives of every order `k < n` vanish at `x` in the extended chart at `x`. In other
words, `I_x ^ (m + 1)` is the ideal of functions with vanishing `m`-jet at `x`, so two functions
have the same `m`-jet at `x` exactly when their difference lies in `I_x ^ (m + 1)`. For `n = 2`
this is `TauCeti.mem_smoothVanishingIdeal_sq_iff_of_isInteriorPoint`.

Combined with the algebraic locality of differential operators
(`TauCeti.apply_mem_smul_top_of_mem_pow_smul_top`), this shows that the value at `x` of a
differential operator of order at most `m` on smooth functions, defined by iterated commutators
with multiplication by functions, depends only on the `m`-jet at `x` of its argument.

## Main results

* `TauCeti.mem_smoothVanishingIdeal_pow_iff_of_isInteriorPoint`: at an interior point `x`,
  `f ∈ I_x ^ n` if and only if the iterated derivatives of order `k < n` of `f` in the chart at
  `x` vanish at `x`.
* `TauCeti.mem_smoothVanishingIdeal_pow_iff`: the same at every point of a boundaryless manifold.
* `TauCeti.mem_smoothVanishingIdeal_pow_of_eventuallyEq_zero`: a function vanishing near `x`
  lies in every power of `I_x`.
* `TauCeti.apply_eq_of_mem_differentialOperators_of_iteratedFDeriv_eq`: a differential operator of
  order at most `m` on smooth functions takes the same value at `x` on two functions with the same
  `m`-jet at `x`.

## Implementation notes

Near an interior point every smooth function agrees with a smooth function on the model space
composed with a globally smooth localized chart. The higher-order Hadamard lemma
(`ContMDiffMap.exists_hadamard_coords_of_iteratedFDeriv_eq_zero`) writes a function on the model
space with vanishing jet as a combination of products of relative coordinate functions, and
pulling back along the localized chart gives an element of `I_x ^ n` up to a function vanishing
near `x`. Conversely, orders of vanishing add under multiplication
(`TauCeti.iteratedFDeriv_mul_eq_zero_of_lt_add`).

## References

* I. Kolář, P. W. Michor, J. Slovák, *Natural operations in differential geometry*, Springer,
  1993, §§1.3–1.6 and §12.
-/

public section

open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

variable [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M]

/-- A smooth function vanishing on a neighbourhood of `x` lies in every power of the vanishing
ideal at `x`. -/
theorem mem_smoothVanishingIdeal_pow_of_eventuallyEq_zero {x : M} {f : C^∞⟮I, M; ℝ⟯}
    (hf : (f : M → ℝ) =ᶠ[𝓝 x] 0) (n : ℕ) : f ∈ smoothVanishingIdeal I x ^ n := by
  obtain ⟨b, -, hb⟩ := (SmoothBumpFunction.nhds_basis_support (I := I) hf).mem_iff.mp hf
  let χ : C^∞⟮I, M; ℝ⟯ := ⟨b, b.contMDiff⟩
  have hχ : ⇑χ = b := ContMDiffMap.coeFn_mk _ _
  -- `f = (1 - χ) * f` with `1 - χ ∈ I_x`, so `f` lies in `I_x * I_x ^ n` whenever it lies in
  -- `I_x ^ n`.
  have hfac : f = (1 - χ) * f := by
    ext y
    by_cases hy : b y = 0
    · simp [hχ, hy]
    · simp [show f y = 0 from hb hy]
  have h1 : 1 - χ ∈ smoothVanishingIdeal I x := by simp [hχ]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [hfac, pow_succ']
    exact Ideal.mul_mem_mul h1 ih

/-- At an interior point `x`, a function in the `n`-th power of the vanishing ideal at `x` has
vanishing iterated derivatives of every order `k < n` at `x` in the chart at `x`. -/
theorem iteratedFDeriv_comp_extChartAt_symm_eq_zero_of_mem_smoothVanishingIdeal_pow {x : M}
    (hx : I.IsInteriorPoint x) {n : ℕ} {f : C^∞⟮I, M; ℝ⟯}
    (hf : f ∈ smoothVanishingIdeal I x ^ n) {k : ℕ} (hk : k < n) :
    iteratedFDeriv ℝ k (f ∘ (extChartAt I x).symm) (extChartAt I x x) = 0 := by
  induction n generalizing f k with
  | zero => omega
  | succ n ih =>
    rw [pow_succ] at hf
    induction hf using Submodule.mul_induction_on' with
    | mem_mul_mem g hg h hh =>
      -- Replace both chart expressions by smooth functions on the model space and use that
      -- orders of vanishing add.
      obtain ⟨G, hG⟩ := exists_contMDiffMap_comp_extChartAt_symm_eventuallyEq hx g
      obtain ⟨K, hK⟩ := exists_contMDiffMap_comp_extChartAt_symm_eventuallyEq hx h
      have hGK : ((g * h : C^∞⟮I, M; ℝ⟯) ∘ (extChartAt I x).symm) =ᶠ[𝓝 (extChartAt I x x)]
          fun y ↦ G y * K y := by
        filter_upwards [hG, hK] with z hz hz'
        simp only [Function.comp_apply] at hz hz' ⊢
        rw [ContMDiffMap.coe_mul, Pi.mul_apply, hz, hz']
      rw [(hGK.iteratedFDeriv ℝ k).eq_of_nhds]
      refine iteratedFDeriv_mul_eq_zero_of_lt_add G.contMDiff.contDiff K.contMDiff.contDiff
        (m := n) (n := 1) (fun i hi ↦ ?_) (fun i hi ↦ ?_) hk (by exact_mod_cast le_top)
      · rw [← (hG.iteratedFDeriv ℝ i).eq_of_nhds]
        exact ih hg hi
      · obtain rfl : i = 0 := by omega
        ext v
        rw [← (hK.iteratedFDeriv ℝ 0).eq_of_nhds, iteratedFDeriv_zero_apply]
        simpa using hh
    | add g _ h _ hg hh =>
      have hsum : ((g + h : C^∞⟮I, M; ℝ⟯) ∘ (extChartAt I x).symm) =
          (g ∘ (extChartAt I x).symm) + (h ∘ (extChartAt I x).symm) := by
        ext; simp
      rw [hsum, iteratedFDeriv_add_apply
        ((contDiffAt_comp_extChartAt_symm hx g).of_le (by exact_mod_cast le_top))
        ((contDiffAt_comp_extChartAt_symm hx h).of_le (by exact_mod_cast le_top)), hg, hh,
        add_zero]

/-- **The higher-order Hadamard lemma for the vanishing ideal.** At an interior point `x`, a
smooth function whose iterated derivatives of every order `k < n` vanish at `x` in the chart at
`x` lies in the `n`-th power of the vanishing ideal at `x`. -/
theorem mem_smoothVanishingIdeal_pow_of_iteratedFDeriv_eq_zero {x : M}
    (hx : I.IsInteriorPoint x) {n : ℕ} {f : C^∞⟮I, M; ℝ⟯}
    (hf : ∀ k < n, iteratedFDeriv ℝ k (f ∘ (extChartAt I x).symm) (extChartAt I x x) = 0) :
    f ∈ smoothVanishingIdeal I x ^ n := by
  -- Near `x`, write `f` as a smooth function `g` of a globally smooth localized chart `F`.
  obtain ⟨F, hF⟩ := exists_contMDiffMap_eventuallyEq_extChartAt (I := I) x
  obtain ⟨g, hg⟩ := exists_contMDiffMap_comp_eventuallyEq hx F hF f
  have hFx : F x = extChartAt I x x := hF.eq_of_nhds
  have hfg := comp_extChartAt_symm_eventuallyEq_of_eventuallyEq hx hF hg
  -- The higher-order Hadamard lemma factors `g` through products of `n` relative coordinates;
  -- pulling back by `F` gives an element of `I_x ^ n`.
  let b := Module.finBasis ℝ E
  obtain ⟨a, -, ha⟩ := ContMDiffMap.exists_hadamard_coords_of_iteratedFDeriv_eq_zero g (F x) b
    (n := n) fun k hk ↦ by rw [hFx, ← (hfg.iteratedFDeriv ℝ k).eq_of_nhds, hf k hk]
  let c (i : Fin (Module.finrank ℝ E)) : C^∞⟮I, M; ℝ⟯ :=
    ⟨fun y ↦ b.coord i (F y) - b.coord i (F x),
      ((b.coord i).toContinuousLinearMap.contDiff.contMDiff.comp F.contMDiff).sub contMDiff_const⟩
  have hc (i) (y : M) : c i y = b.coord i (F y) - b.coord i (F x) := rfl
  let p : C^∞⟮I, M; ℝ⟯ := ∑ σ, (a σ).comp F * ∏ j, c (σ j)
  have hp : p ∈ smoothVanishingIdeal I x ^ n := by
    refine Ideal.sum_mem _ fun σ _ ↦ Ideal.mul_mem_left _ _ ?_
    simpa using Ideal.prod_mem_prod (s := Finset.univ)
      (I := fun _ : Fin n ↦ smoothVanishingIdeal I x) (x := fun j ↦ c (σ j)) fun j _ ↦ by simp [hc]
  -- The remainder `f - p` vanishes near `x`.
  have hfp : f - p ∈ smoothVanishingIdeal I x ^ n := by
    refine mem_smoothVanishingIdeal_pow_of_eventuallyEq_zero ?_ n
    filter_upwards [hg] with y hy
    -- Evaluate `p` at `y` through the evaluation ring homomorphism, which is evaluation.
    have hev (q : C^∞⟮I, M; ℝ⟯) : ContMDiffMap.evalRingHom y q = q y := rfl
    have hpy : p y = ∑ σ, a σ (F y) * ∏ j, (b.coord (σ j) (F y) - b.coord (σ j) (F x)) := by
      rw [← hev p]
      simp only [p, map_sum, map_mul, map_prod]
      simp only [hev, ContMDiffMap.comp_apply, hc]
    rw [Pi.zero_apply, ContMDiffMap.coe_sub, Pi.sub_apply, hpy, ← ha (F y), hy,
      Function.comp_apply, sub_self]
  simpa using add_mem hfp hp

/-- At an interior point `x` of a finite-dimensional Hausdorff real manifold, a smooth function is
a finite sum of products of `n` smooth functions vanishing at `x` if and only if its iterated
derivatives of every order `k < n` vanish at `x` in the chart at `x`. -/
theorem mem_smoothVanishingIdeal_pow_iff_of_isInteriorPoint {x : M} (hx : I.IsInteriorPoint x)
    (n : ℕ) (f : C^∞⟮I, M; ℝ⟯) :
    f ∈ smoothVanishingIdeal I x ^ n ↔
      ∀ k < n, iteratedFDeriv ℝ k (f ∘ (extChartAt I x).symm) (extChartAt I x x) = 0 :=
  ⟨fun hf _ hk ↦
    iteratedFDeriv_comp_extChartAt_symm_eq_zero_of_mem_smoothVanishingIdeal_pow hx hf hk,
    mem_smoothVanishingIdeal_pow_of_iteratedFDeriv_eq_zero hx⟩

/-- On a finite-dimensional Hausdorff boundaryless real manifold, a smooth function is a finite sum
of products of `n` smooth functions vanishing at `x` if and only if its iterated derivatives of
every order `k < n` vanish at `x` in the chart at `x`. -/
theorem mem_smoothVanishingIdeal_pow_iff [BoundarylessManifold I M] (x : M) (n : ℕ)
    (f : C^∞⟮I, M; ℝ⟯) :
    f ∈ smoothVanishingIdeal I x ^ n ↔
      ∀ k < n, iteratedFDeriv ℝ k (f ∘ (extChartAt I x).symm) (extChartAt I x x) = 0 :=
  mem_smoothVanishingIdeal_pow_iff_of_isInteriorPoint BoundarylessManifold.isInteriorPoint n f

/-- **Differential operators factor through jets.** At an interior point `x`, a differential
operator of order at most `m` on smooth functions, in the sense of iterated commutators with
multiplication by functions, takes the same value at `x` on two functions whose iterated
derivatives of every order `k ≤ m` agree at `x` in the chart at `x`. -/
theorem apply_eq_of_mem_differentialOperators_of_iteratedFDeriv_eq
    {D : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯} {m : ℕ}
    (hD : D ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ m) {x : M}
    (hx : I.IsInteriorPoint x) {u v : C^∞⟮I, M; ℝ⟯}
    (huv : ∀ k ≤ m, iteratedFDeriv ℝ k (u ∘ (extChartAt I x).symm) (extChartAt I x x) =
      iteratedFDeriv ℝ k (v ∘ (extChartAt I x).symm) (extChartAt I x x)) :
    D u x = D v x := by
  have hsub : u - v ∈ smoothVanishingIdeal I x ^ (m + 1) := by
    refine mem_smoothVanishingIdeal_pow_of_iteratedFDeriv_eq_zero hx fun k hk ↦ ?_
    have hcomp : ((u - v : C^∞⟮I, M; ℝ⟯) ∘ (extChartAt I x).symm) =
        (u ∘ (extChartAt I x).symm) - (v ∘ (extChartAt I x).symm) := by
      ext; simp
    rw [hcomp, iteratedFDeriv_sub_apply
      ((contDiffAt_comp_extChartAt_symm hx u).of_le (by exact_mod_cast le_top))
      ((contDiffAt_comp_extChartAt_symm hx v).of_le (by exact_mod_cast le_top)),
      huv k (Nat.lt_succ_iff.mp hk), sub_self]
  -- For the module of functions over itself, `I • ⊤ = I`.
  have h := apply_mem_smul_top_of_mem_pow_smul_top hD (smoothVanishingIdeal I x)
    (x := u - v) (by rwa [Ideal.smul_eq_mul, Ideal.mul_top])
  rwa [Ideal.smul_eq_mul, Ideal.mul_top, map_sub, mem_smoothVanishingIdeal_iff,
    ContMDiffMap.coe_sub, Pi.sub_apply, sub_eq_zero] at h

end TauCeti

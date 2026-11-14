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
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic

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
vanishing add under multiplication. It only uses that chart expressions of smooth functions are
smooth at the image of an interior point, so it needs neither finite dimensionality, the Hausdorff
property nor a smooth manifold structure on `M`. On a smooth manifold the same argument applies
in the chart at `x` at every point `y` of its source whose image lies in the interior of the chart
target, which lets one chart serve all nearby points. The converse is Hadamard's lemma of order `m`,
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
* `TauCeti.differentialOperators_apply_eq_of_eventuallyEq`,
  `TauCeti.tsupport_apply_subset_of_mem_differentialOperators`: differential operators are local,
  so they do not enlarge supports.
* `TauCeti.differentialOperators_eq_of_forall_hasCompactSupport_apply_eq`: a differential operator
  is determined by its values on compactly supported functions.

## References

* I. Kolář, P. W. Michor, J. Slovák, *Natural operations in differential geometry*, Springer,
  1993, §§1.3–1.6 and §12.
* A. Grothendieck, *Éléments de géométrie algébrique IV*, Quatrième partie, §16.8.
-/

public section

open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- The jet inclusion at the image of `y` in the extended chart at `x`, given that chart
expressions of smooth functions are smooth there. -/
private theorem iteratedFDeriv_comp_extChartAt_symm_eq_zero_of_contDiffAt {x y : M}
    (hy : y ∈ (extChartAt I x).source)
    (hs : ∀ g : C^∞⟮I, M; ℝ⟯,
      ContDiffAt ℝ ∞ ((g : M → ℝ) ∘ (extChartAt I x).symm) (extChartAt I x y))
    {m : ℕ} {f : C^∞⟮I, M; ℝ⟯} (hf : f ∈ smoothVanishingIdeal I y ^ (m + 1)) {k : ℕ}
    (hk : k ≤ m) :
    iteratedFDeriv ℝ k ((f : M → ℝ) ∘ (extChartAt I x).symm) (extChartAt I x y) = 0 := by
  induction m generalizing f k with
  | zero =>
    obtain rfl : k = 0 := by omega
    rw [zero_add, pow_one, mem_smoothVanishingIdeal_iff] at hf
    rw [← norm_eq_zero, norm_iteratedFDeriv_zero, Function.comp_apply,
      (extChartAt I x).left_inv hy, hf, norm_zero]
  | succ m ih =>
    rw [pow_succ] at hf
    refine Submodule.mul_induction_on
      (C := fun r : C^∞⟮I, M; ℝ⟯ ↦ ∀ k ≤ m + 1,
        iteratedFDeriv ℝ k ((r : M → ℝ) ∘ (extChartAt I x).symm) (extChartAt I x y) = 0)
      hf (fun u hu v hv k hk ↦ ?_) (fun u v hu hv k hk ↦ ?_) k hk
    · -- Orders of vanishing add: `u` vanishes to order `m + 1` and `v` to order `1`.
      rw [ContMDiffMap.coe_mul, Pi.mul_comp]
      refine iteratedFDeriv_mul_eq_zero_of_lt_add (hs u) (hs v) (m := m + 1) (n := 1)
        (fun i hi ↦ ih hu (by omega)) (fun i hi ↦ ?_) (by omega) (by exact_mod_cast le_top)
      obtain rfl : i = 0 := by omega
      rw [← norm_eq_zero, norm_iteratedFDeriv_zero, Function.comp_apply,
        (extChartAt I x).left_inv hy, mem_smoothVanishingIdeal_iff.1 hv, norm_zero]
    · rw [ContMDiffMap.coe_add, Pi.add_comp,
        iteratedFDeriv_add_apply ((hs u).of_le (by simp)) ((hs v).of_le (by simp)), hu k hk,
        hv k hk, add_zero]

/-- A function in `I_x ^ (m + 1)` has a chart expression whose derivatives of order at most `m`
vanish at the image of `x`. -/
theorem iteratedFDeriv_comp_extChartAt_symm_eq_zero_of_mem_smoothVanishingIdeal_pow {x : M}
    (hx : I.IsInteriorPoint x) {m : ℕ} {f : C^∞⟮I, M; ℝ⟯}
    (hf : f ∈ smoothVanishingIdeal I x ^ (m + 1)) {k : ℕ} (hk : k ≤ m) :
    iteratedFDeriv ℝ k ((f : M → ℝ) ∘ (extChartAt I x).symm) (extChartAt I x x) = 0 :=
  iteratedFDeriv_comp_extChartAt_symm_eq_zero_of_contDiffAt (mem_extChartAt_source x)
    (fun g ↦ g.contMDiff.contMDiffAt.contDiffAt_comp_extChartAt_symm_of_isInteriorPoint hx) hf hk

/-- On a smooth manifold, a function in `I_y ^ (m + 1)` has a chart expression whose derivatives
of order at most `m` vanish at the image of `y`, in the extended chart at any point `x` whose
source contains `y` and whose target contains the image of `y` in its interior. -/
theorem iteratedFDeriv_comp_extChartAt_symm_eq_zero_of_mem_smoothVanishingIdeal_pow_of_mem_source
    [IsManifold I ∞ M] {x y : M} (hy : y ∈ (extChartAt I x).source)
    (hy' : extChartAt I x y ∈ interior (extChartAt I x).target) {m : ℕ} {f : C^∞⟮I, M; ℝ⟯}
    (hf : f ∈ smoothVanishingIdeal I y ^ (m + 1)) {k : ℕ} (hk : k ≤ m) :
    iteratedFDeriv ℝ k ((f : M → ℝ) ∘ (extChartAt I x).symm) (extChartAt I x y) = 0 :=
  iteratedFDeriv_comp_extChartAt_symm_eq_zero_of_contDiffAt hy
    (fun g ↦ contMDiffAt_iff_contDiffAt.mp
      ((g.contMDiff.contMDiffAt.comp_contMDiffWithinAt _
        (contMDiffWithinAt_extChartAt_symm_target x (interior_subset hy'))).contMDiffAt
          (mem_interior_iff_mem_nhds.mp hy'))) hf hk

variable [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M]

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
  have hx' := (ModelWithCorners.isInteriorPoint_iff (I := I)).mp hx
  obtain ⟨u, hu, hfu⟩ := exists_contDiff_comp_extChartAt_symm_eventuallyEq hx' f
  obtain ⟨v, hv, hgv⟩ := exists_contDiff_comp_extChartAt_symm_eventuallyEq hx' g
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

/-- **Differential operators are local.** A differential operator on `C^∞(M)` takes the same value
at `x` on two smooth functions that agree near `x`. This holds at boundary points as well. -/
theorem differentialOperators_apply_eq_of_eventuallyEq {m : ℕ}
    {D : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯}
    (hD : D ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ m) {x : M}
    {f g : C^∞⟮I, M; ℝ⟯} (hfg : (f : M → ℝ) =ᶠ[𝓝 x] g) :
    D f x = D g x := by
  -- Take a bump function `χ` at `x` supported where `f = g`. Then `1 - χ` vanishes at `x` and
  -- `(1 - χ) * (f - g) = f - g`, so `f - g = (1 - χ) ^ (m + 1) * (f - g)` lies in `I_x ^ (m + 1)`.
  obtain ⟨χ, -, hχ⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := I) x).mem_iff.mp hfg
  let φ : C^∞⟮I, M; ℝ⟯ := ⟨χ, χ.contMDiff⟩
  have hφ : 1 - φ ∈ smoothVanishingIdeal I x := by
    rw [mem_smoothVanishingIdeal_iff, ContMDiffMap.coe_sub, ContMDiffMap.coe_one,
      ContMDiffMap.coeFn_mk, Pi.sub_apply, Pi.one_apply, χ.eq_one, sub_self]
  have hφfg : (1 - φ) * (f - g) = f - g := by
    ext y
    rw [ContMDiffMap.coe_mul, ContMDiffMap.coe_sub, ContMDiffMap.coe_one, ContMDiffMap.coeFn_mk,
      ContMDiffMap.coe_sub, Pi.mul_apply, Pi.sub_apply, Pi.sub_apply, Pi.one_apply]
    by_cases hy : χ y = 0
    · rw [hy, sub_zero, one_mul]
    · rw [show f y = g y from hχ (subset_tsupport _ hy), sub_self, mul_zero]
  have hpow : ∀ n : ℕ, (1 - φ) ^ n * (f - g) = f - g := fun n ↦ by
    induction n with
    | zero => rw [pow_zero, one_mul]
    | succ n ih => rw [pow_succ, mul_assoc, hφfg, ih]
  have hmem : f - g ∈ smoothVanishingIdeal I x ^ (m + 1) :=
    hpow (m + 1) ▸ Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hφ _)
  have h := apply_mem_smul_top_of_mem_pow_smul_top hD (smoothVanishingIdeal I x)
    (x := f - g) (by simpa using hmem)
  rw [smul_eq_mul, Ideal.mul_top, map_sub, mem_smoothVanishingIdeal_iff, ContMDiffMap.coe_sub,
    Pi.sub_apply, sub_eq_zero] at h
  exact h

/-- A differential operator on `C^∞(M)` does not enlarge supports: `tsupport (D f) ⊆ tsupport f`.
-/
theorem tsupport_apply_subset_of_mem_differentialOperators {m : ℕ}
    {D : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯}
    (hD : D ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ m)
    (f : C^∞⟮I, M; ℝ⟯) : tsupport (D f) ⊆ tsupport f := by
  refine closure_minimal (fun x hx ↦ ?_) (isClosed_tsupport _)
  by_contra hxf
  refine hx ?_
  have hf0 : (f : M → ℝ) =ᶠ[𝓝 x] (0 : C^∞⟮I, M; ℝ⟯) := by
    rw [ContMDiffMap.coe_zero]
    exact notMem_tsupport_iff_eventuallyEq.mp hxf
  rw [differentialOperators_apply_eq_of_eventuallyEq hD hf0, map_zero, ContMDiffMap.coe_zero,
    Pi.zero_apply]

/-- A differential operator on `C^∞(M)` maps compactly supported functions to compactly
supported functions. -/
theorem hasCompactSupport_apply_of_mem_differentialOperators {m : ℕ}
    {D : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯}
    (hD : D ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ m)
    {f : C^∞⟮I, M; ℝ⟯} (hf : HasCompactSupport f) : HasCompactSupport (D f) :=
  hf.mono' ((subset_tsupport _).trans (tsupport_apply_subset_of_mem_differentialOperators hD f))

/-- A differential operator on `C^∞(M)` is determined by its values on compactly supported
functions: two differential operators agreeing there are equal, since they are local. -/
theorem differentialOperators_eq_of_forall_hasCompactSupport_apply_eq {m₁ m₂ : ℕ}
    {D₁ D₂ : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯}
    (hD₁ : D₁ ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ m₁)
    (hD₂ : D₂ ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ m₂)
    (h : ∀ f : C^∞⟮I, M; ℝ⟯, HasCompactSupport f → D₁ f = D₂ f) : D₁ = D₂ := by
  refine LinearMap.ext fun g ↦ ContMDiffMap.ext fun x ↦ ?_
  -- Cut `g` off by a bump function equal to one near `x`.
  let χ : SmoothBumpFunction I x := Classical.choice inferInstance
  let φ : C^∞⟮I, M; ℝ⟯ := ⟨χ, χ.contMDiff⟩
  have hφg : ((φ * g : C^∞⟮I, M; ℝ⟯) : M → ℝ) =ᶠ[𝓝 x] g := by
    filter_upwards [χ.eventuallyEq_one] with y hy
    rw [ContMDiffMap.coe_mul, Pi.mul_apply, ContMDiffMap.coeFn_mk, hy, Pi.one_apply, one_mul]
  have hφgc : HasCompactSupport (φ * g : C^∞⟮I, M; ℝ⟯) := by
    rw [ContMDiffMap.coe_mul, ContMDiffMap.coeFn_mk]
    exact χ.hasCompactSupport.mul_right
  rw [← differentialOperators_apply_eq_of_eventuallyEq hD₁ hφg,
    ← differentialOperators_apply_eq_of_eventuallyEq hD₂ hφg, h _ hφgc]

end TauCeti

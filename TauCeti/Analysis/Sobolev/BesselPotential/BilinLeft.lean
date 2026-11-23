/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Multiplication
public import TauCeti.Analysis.Sobolev.BesselPotential.Besov
public import TauCeti.Analysis.Sobolev.BesselPotential.Extension
public import TauCeti.Analysis.Sobolev.BesselPotential.Postcomp
import TauCeti.Analysis.Calculus.IteratedFDeriv.Basic
import TauCeti.Analysis.Distribution.SchwartzSpace.Basic
import TauCeti.Analysis.Distribution.TemperateGrowth
import TauCeti.Analysis.Distribution.TemperedDistribution.SmulLeft
import TauCeti.Analysis.Sobolev.BesselPotential.Distribution

/-!
# Multiplication by functions with bounded derivatives on `H^s(ℝⁿ)`

Let `g : E → G` be a function of temperate growth with values in a finite-dimensional complex
normed space whose derivatives of order at most `N` are bounded, for a natural number `N > |s|`,
and let `B : F →L[ℂ] G →L[ℂ] K` be a continuous bilinear map, where `F` is a complex Banach
space and `K` is a complex Hilbert space. Mathlib's `SchwartzMap.bilinLeftCLM B hg` is the
operator `u ↦ (x ↦ B (u x) (g x))` on Schwartz functions.
This file shows that it extends to a bounded operator `H^s(E, F) → H^s(E, K)` on the
Bessel-potential spaces `H^s = H^{s,2}`, for every real `s`, including negative orders, with
operator norm at most `C ‖B‖ M` when the derivatives of `g` of order at most `N` are bounded by
`M`. Here `C` depends only on the spaces, on `s` and on `N`, and not on `B`, `g` or `M`.

The main instance is multiplication by a smooth matrix-valued function: for
`A : E → (F →L[ℂ] G')` with bounded derivatives, the map `u ↦ (x ↦ A x (u x))` is
`SchwartzMap.bilinLeftCLM (ContinuousLinearMap.apply ℂ G') hA`. This is covered when `F` is
complete, `G'` is a complex Hilbert space and `F →L[ℂ] G'` is finite-dimensional, for example
when `F` and `G'` are both finite-dimensional. Such multiplications are the changes of frame of
Sobolev spaces of sections of vector bundles, and the bounded Jacobian factors of changes of
coordinates. Scalar multiplication `u ↦ g u` by `g : E → ℂ` is the case
`B = (ContinuousLinearMap.lsmul ℂ ℂ).flip`, which is how Mathlib defines
`SchwartzMap.smulLeftCLM`. The multiplier need not decay, unlike the Schwartz multipliers of
`BesselPotentialSpace.smulLeftCLM`, and the order `s` is any real number, unlike the
integer-order statements `TemperedDistribution.MemSobolev.smulLeftCLM_of_norm_iteratedFDeriv_le`
and `TemperedDistribution.mul_mem_realSobolevFunctions_of_bounded_derivatives`. The existence of
the bounded extensions for scalar multipliers and for `A : E → (F →L[ℂ] G')` with `F` and `G'`
finite-dimensional Hilbert spaces is `SchwartzMap.hasSobolevExtension_smulLeftCLM` and
`SchwartzMap.hasSobolevExtension_bilinLeftCLM_apply`, proved by duality and interpolation. This
file adds a named operator for every bilinear `B` and Banach space `F`, with an operator norm
bound `C ‖B‖ M` that is uniform in `g`.

The scalar case comes from the Besov spaces. At `p = q = 2` the Besov space `B^s_{2,2}` and the
Bessel-potential space `H^{s,2}` contain the same tempered distributions with equivalent norms
(`TauCeti.BesovSpace.besselPotentialSpaceEquiv`), and multiplication by `g` is bounded on every
Besov space, with a bound uniform in `p` and `q`
(`TauCeti.BesovSpace.exists_toDistr_eq_smulLeftCLM_and_norm_le`). Writing
`g = ∑ₖ gₖ bₖ` in a basis `bₖ` of `G` gives
`B (u x) (g x) = ∑ₖ gₖ x • B (u x) bₖ` (`SchwartzMap.bilinLeftCLM_eq_sum_smulLeftCLM`), a finite
sum of scalar multiplications applied after the pointwise maps `B.flip bₖ`, which act on `H^s`
with norm at most `‖B‖ ‖bₖ‖` (`BesselPotentialSpace.norm_postcomp_le`).

## Main declarations

* `BesselPotentialSpace.exists_toDistr_eq_smulLeftCLM_and_norm_le`: multiplication by a scalar
  function `g` with derivatives of order at most `N > |s|` bounded by `M` maps `H^s(E, H)` into
  itself, with norm at most `C M`, for a complex Hilbert space `H`.
* `BesselPotentialSpace.bilinLeftCLM`: for a complex Banach space `F` and a complex Hilbert space
  `K`, the bounded operator `H^s(E, F) → H^s(E, K)` extending `SchwartzMap.bilinLeftCLM B hg`,
  characterised on Schwartz functions by
  `BesselPotentialSpace.bilinLeftCLM_toBesselPotentialSpaceCLM`. For scalar multiplication it is
  `TemperedDistribution.smulLeftCLM` on every element of `H^s`
  (`BesselPotentialSpace.toDistr_bilinLeftCLM_lsmul_flip`).
* `BesselPotentialSpace.exists_norm_bilinLeftCLM_le`: its operator norm is at most `C ‖B‖ M`.
* `SchwartzMap.hasSobolevExtension_bilinLeftCLM`: `SchwartzMap.bilinLeftCLM B hg` extends to a
  bounded operator `H^s → H^s`.

## References

* H. Triebel, *Theory of Function Spaces*, Birkhäuser, 1983, §2.8.2 (smooth functions as
  pointwise multipliers of Besov spaces).
* J. Bergh and J. Löfström, *Interpolation Spaces: An Introduction*, Springer, 1976,
  Theorem 6.2.4 (`B^s_{2,2} = H^s`).
-/

public section

noncomputable section

open MeasureTheory TemperedDistribution TauCeti
open scoped ENNReal SchwartzMap BesselPotentialSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

namespace BesselPotentialSpace

/-! ### Scalar multipliers -/

section Scalar

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Multiplication by a function with bounded derivatives is bounded on `H^s`.** Let `N` be a
natural number with `|s| < N`. There is `C` with the following property. Let `g` be a scalar
function of temperate growth whose derivatives of order at most `N` are bounded by `M`. Then for
every `u ∈ H^s(E, H)` the product `g u` lies in `H^s(E, H)`, with `‖g u‖ ≤ C M ‖u‖`. -/
theorem exists_toDistr_eq_smulLeftCLM_and_norm_le {s : ℝ} {N : ℕ} (hN : |s| < N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {g : E → ℂ} {M : ℝ}, g.HasTemperateGrowth →
      (∀ n ≤ N, ∀ x, ‖iteratedFDeriv ℝ n g x‖ ≤ M) → ∀ u : H^{s}(E, H),
      ∃ v : H^{s}(E, H), v.toDistr = smulLeftCLM H g u.toDistr ∧ ‖v‖ ≤ C * M * ‖u‖ := by
  -- Transport the Besov multiplier theorem along `B^s_{2,2} ≃ H^s`.
  let e := BesovSpace.besselPotentialSpaceEquiv H (default : ContDiffBump (0 : E)) s
  obtain ⟨C, hC, hmul⟩ :=
    BesovSpace.exists_toDistr_eq_smulLeftCLM_and_norm_le (F := H) (default : ContDiffBump (0 : E))
      hN
  refine ⟨‖e.toContinuousLinearMap‖ * C * ‖e.symm.toContinuousLinearMap‖,
    mul_nonneg (mul_nonneg (norm_nonneg _) hC) (norm_nonneg _), fun {g M} hg hgM u ↦ ?_⟩
  obtain ⟨w, hw, hwn⟩ := hmul hg hgM (p := 2) (q := 2) (e.symm u)
  have hM := (nonneg_and_norm_le_of_norm_iteratedFDeriv_le hgM).1
  refine ⟨e w, ?_, ?_⟩
  · rw [BesovSpace.toDistr_besselPotentialSpaceEquiv, hw,
      BesovSpace.toDistr_besselPotentialSpaceEquiv_symm]
  · calc ‖e w‖ ≤ ‖e.toContinuousLinearMap‖ * (C * M * ‖e.symm u‖) :=
          (e.toContinuousLinearMap.le_opNorm w).trans (by gcongr)
      _ ≤ ‖e.toContinuousLinearMap‖ * (C * M * (‖e.symm.toContinuousLinearMap‖ * ‖u‖)) := by
          gcongr
          exact e.symm.toContinuousLinearMap.le_opNorm u
      _ = _ := by ring

end Scalar

/-! ### Bilinear multipliers -/

section Bilinear

variable {F G K : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [FiniteDimensional ℂ G]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

omit [FiniteDimensional ℂ G] in
/-- On a Schwartz function `u`, the product `x ↦ B (u x) (g x)` is the sum of any elements `vₖ` of
`H^s` representing the products `gₖ • (B.flip bₖ) u` by the coordinates `gₖ` of `g` in the basis
`b`. -/
private theorem toBesselPotentialSpaceCLM_bilinLeftCLM_eq_sum {s : ℝ} {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℂ G) (B : F →L[ℂ] G →L[ℂ] K) {g : E → G} (hg : g.HasTemperateGrowth)
    (u : 𝓢(E, F)) (v : ι → H^{s}(E, K))
    (hv : ∀ k, (v k).toDistr = smulLeftCLM K (fun x ↦ b.repr (g x) k)
      (postcomp E s 2 (B.flip (b k)) (SchwartzMap.toBesselPotentialSpaceCLM s 2 u)).toDistr) :
    SchwartzMap.toBesselPotentialSpaceCLM s 2 (SchwartzMap.bilinLeftCLM B hg u) = ∑ k, v k := by
  refine ext ?_
  rw [toDistr_sum, SchwartzMap.toDistr_toBesselPotentialSpaceCLM,
    SchwartzMap.bilinLeftCLM_eq_sum_smulLeftCLM b B hg, map_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [hv, ← SchwartzMap.toBesselPotentialSpaceCLM_postcompCLM,
    SchwartzMap.toDistr_toBesselPotentialSpaceCLM, smulLeftCLM_toTemperedDistributionCLM_eq]

/-- The estimate behind `BesselPotentialSpace.bilinLeftCLM`, on Schwartz functions. -/
private theorem exists_norm_toBesselPotentialSpaceCLM_bilinLeftCLM_le (s : ℝ) {N : ℕ}
    (hN : |s| < N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (B : F →L[ℂ] G →L[ℂ] K) {g : E → G} (hg : g.HasTemperateGrowth) {M : ℝ},
      (∀ n ≤ N, ∀ x, ‖iteratedFDeriv ℝ n g x‖ ≤ M) → ∀ u : 𝓢(E, F),
      ‖SchwartzMap.toBesselPotentialSpaceCLM s 2 (SchwartzMap.bilinLeftCLM B hg u)‖ ≤
        C * ‖B‖ * M * ‖SchwartzMap.toBesselPotentialSpaceCLM s 2 u‖ := by
  let b := Module.finBasis ℂ G
  -- The coordinate functionals `c k` of the basis `b`.
  let c (k : Fin (Module.finrank ℂ G)) : G →L[ℂ] ℂ := LinearMap.toContinuousLinearMap (b.coord k)
  obtain ⟨C₀, hC₀, hmul⟩ := exists_toDistr_eq_smulLeftCLM_and_norm_le (E := E) (H := K) hN
  refine ⟨C₀ * ∑ k, ‖c k‖ * ‖b k‖, mul_nonneg hC₀ (Finset.sum_nonneg fun _ _ ↦ by positivity),
    fun B g hg M hgM u ↦ ?_⟩
  have hM := (nonneg_and_norm_le_of_norm_iteratedFDeriv_le hgM).1
  -- The coordinates `gₖ = c k ∘ g` of `g` have bounded derivatives.
  have hgkM (k : Fin (Module.finrank ℂ G)) :
      ∀ n ≤ N, ∀ x, ‖iteratedFDeriv ℝ n (fun x ↦ b.repr (g x) k) x‖ ≤ ‖c k‖ * M :=
    fun n hn x ↦ by
      have h := ((c k).restrictScalars ℝ).norm_iteratedFDeriv_comp_left (x := x) (n := n)
        (hg.1.contDiffAt) (mod_cast le_top)
      simp only [ContinuousLinearMap.norm_restrictScalars, Function.comp_def,
        ContinuousLinearMap.coe_restrictScalars', c, LinearMap.coe_toContinuousLinearMap',
        Module.Basis.coord_apply] at h
      exact h.trans (by gcongr; exact hgM n hn x)
  set U := SchwartzMap.toBesselPotentialSpaceCLM s 2 u
  choose v hv hvn using fun k ↦ hmul (hg.repr b k) (hgkM k) (postcomp E s 2 (B.flip (b k)) U)
  -- Since `‖B.flip bₖ‖ ≤ ‖B‖ ‖bₖ‖`, the `k`-th term has norm at most `C₀ ‖c k‖ M ‖B‖ ‖bₖ‖ ‖U‖`.
  have hterm (k : Fin (Module.finrank ℂ G)) :
      ‖v k‖ ≤ C₀ * (‖c k‖ * ‖b k‖) * ‖B‖ * M * ‖U‖ := by
    have hpost : ‖postcomp E s 2 (B.flip (b k)) U‖ ≤ ‖B‖ * ‖b k‖ * ‖U‖ :=
      (postcomp E s 2 (B.flip (b k))).le_of_opNorm_le ((norm_postcomp_le _).trans
        ((B.flip.le_opNorm (b k)).trans_eq (by rw [ContinuousLinearMap.opNorm_flip]))) U
    calc ‖v k‖ ≤ C₀ * (‖c k‖ * M) * ‖postcomp E s 2 (B.flip (b k)) U‖ := hvn k
      _ ≤ C₀ * (‖c k‖ * M) * (‖B‖ * ‖b k‖ * ‖U‖) := by gcongr
      _ = _ := by ring
  rw [toBesselPotentialSpaceCLM_bilinLeftCLM_eq_sum b B hg u v hv, Finset.mul_sum,
    Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ ↦ hterm k)

variable (s : ℝ)

/-- **Multiplication by a bilinear map against a function with bounded derivatives** as a bounded
operator `H^s(E, F) → H^s(E, K)`: the extension of `SchwartzMap.bilinLeftCLM B hg`, the operator
`u ↦ (x ↦ B (u x) (g x))` on Schwartz functions. When the derivatives of `g` of order at most
`⌊|s|⌋₊ + 1` are bounded, it agrees with that operator on Schwartz functions
(`BesselPotentialSpace.bilinLeftCLM_toBesselPotentialSpaceCLM`), which determines it
(`BesselPotentialSpace.continuousLinearMap_ext`), and its norm is controlled by those bounds
(`BesselPotentialSpace.exists_norm_bilinLeftCLM_le`). For `g` without such bounds the value is the
junk value of `LinearMap.extendOfNorm`. -/
def bilinLeftCLM (B : F →L[ℂ] G →L[ℂ] K) {g : E → G} (hg : g.HasTemperateGrowth) :
    H^{s}(E, F) →L[ℂ] H^{s}(E, K) :=
  ((SchwartzMap.toBesselPotentialSpaceCLM s 2).comp
      (SchwartzMap.bilinLeftCLM B hg)).toLinearMap.extendOfNorm
    (SchwartzMap.toBesselPotentialSpaceCLM (E := E) (F := F) s 2).toLinearMap

/-- On a Schwartz function `u`, the operator `BesselPotentialSpace.bilinLeftCLM s B hg` is the
Schwartz function `x ↦ B (u x) (g x)`, as soon as the derivatives of `g` of order at most
`⌊|s|⌋₊ + 1` are bounded. -/
theorem bilinLeftCLM_toBesselPotentialSpaceCLM (B : F →L[ℂ] G →L[ℂ] K) {g : E → G}
    (hg : g.HasTemperateGrowth)
    (hbd : ∀ n ≤ ⌊|s|⌋₊ + 1, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n g x‖ ≤ C) (u : 𝓢(E, F)) :
    bilinLeftCLM s B hg (SchwartzMap.toBesselPotentialSpaceCLM s 2 u) =
      SchwartzMap.toBesselPotentialSpaceCLM s 2 (SchwartzMap.bilinLeftCLM B hg u) := by
  obtain ⟨M, hM⟩ := exists_forall_norm_iteratedFDeriv_le_of_forall_exists hbd
  obtain ⟨C, -, hC⟩ := exists_norm_toBesselPotentialSpaceCLM_bilinLeftCLM_le (E := E) (F := F)
    (G := G) (K := K) s (N := ⌊|s|⌋₊ + 1) (by push_cast; exact Nat.lt_floor_add_one _)
  exact LinearMap.extendOfNorm_eq
    (SchwartzMap.denseRange_toBesselPotentialSpaceCLM (p := 2) s ENNReal.ofNat_ne_top)
    ⟨C * ‖B‖ * M, hC B hg hM⟩ u

/-- **Scalar multiplication on `H^s` as an operation on distributions.** For
`B = (ContinuousLinearMap.lsmul ℂ ℂ).flip`, the operator `BesselPotentialSpace.bilinLeftCLM`
is multiplication by `g` on the underlying tempered distributions, Mathlib's
`TemperedDistribution.smulLeftCLM`, as soon as the derivatives of `g` of order at most
`⌊|s|⌋₊ + 1` are bounded. -/
@[simp]
theorem toDistr_bilinLeftCLM_lsmul_flip {g : E → ℂ} (hg : g.HasTemperateGrowth)
    (hbd : ∀ n ≤ ⌊|s|⌋₊ + 1, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n g x‖ ≤ C) (u : H^{s}(E, K)) :
    (bilinLeftCLM s (ContinuousLinearMap.lsmul ℂ ℂ).flip hg u).toDistr =
      smulLeftCLM K g u.toDistr := by
  -- Compare with the Besov multiplier transported along `B^s_{2,2} ≃ H^s`, which has this
  -- property by construction, on the dense subspace of Schwartz functions.
  let e := BesovSpace.besselPotentialSpaceEquiv K (default : ContDiffBump (0 : E)) s
  have h : bilinLeftCLM s (ContinuousLinearMap.lsmul ℂ ℂ).flip hg =
      e.toContinuousLinearMap ∘L BesovSpace.smulLeftCLM K _ s 2 2 g hg hbd ∘L
        e.symm.toContinuousLinearMap := by
    refine continuousLinearMap_ext ENNReal.ofNat_ne_top fun v ↦ ext ?_
    simp [bilinLeftCLM_toBesselPotentialSpaceCLM s _ hg hbd, e,
      smulLeftCLM_toTemperedDistributionCLM_eq, SchwartzMap.smulLeftCLM, hg]
  simp [h, e]

variable {s} in
/-- **The norm of a bilinear multiplier of `H^s`.** Let `N` be a natural number with `|s| < N`.
There is `C`, depending only on the spaces, on `s` and on `N`, with the following property. If
the derivatives of order at most `N` of `g` are bounded by `M`, then
`BesselPotentialSpace.bilinLeftCLM s B hg` has operator norm at most `C ‖B‖ M`. -/
theorem exists_norm_bilinLeftCLM_le {N : ℕ} (hN : |s| < N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (B : F →L[ℂ] G →L[ℂ] K) {g : E → G} (hg : g.HasTemperateGrowth) {M : ℝ},
      (∀ n ≤ N, ∀ x, ‖iteratedFDeriv ℝ n g x‖ ≤ M) → ‖bilinLeftCLM s B hg‖ ≤ C * ‖B‖ * M := by
  obtain ⟨C, hC, h⟩ := exists_norm_toBesselPotentialSpaceCLM_bilinLeftCLM_le (E := E) (F := F)
    (G := G) (K := K) s hN
  refine ⟨C, hC, fun B g hg M hgM ↦ ?_⟩
  have hM := (nonneg_and_norm_le_of_norm_iteratedFDeriv_le hgM).1
  exact LinearMap.opNorm_extendOfNorm_le
    (SchwartzMap.denseRange_toBesselPotentialSpaceCLM (p := 2) s ENNReal.ofNat_ne_top)
    (mul_nonneg (mul_nonneg hC (norm_nonneg B)) hM) (h B hg hgM)

end Bilinear

end BesselPotentialSpace

namespace SchwartzMap

variable {F G K : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [FiniteDimensional ℂ G]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The operator `u ↦ (x ↦ B (u x) (g x))` on Schwartz functions extends to a bounded operator
`H^s → H^s` for every real `s`, as soon as the derivatives of `g` of order at most `⌊|s|⌋₊ + 1`
are bounded. -/
theorem hasSobolevExtension_bilinLeftCLM (s : ℝ) (B : F →L[ℂ] G →L[ℂ] K) {g : E → G}
    (hg : g.HasTemperateGrowth)
    (hbd : ∀ n ≤ ⌊|s|⌋₊ + 1, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n g x‖ ≤ C) :
    HasSobolevExtension (bilinLeftCLM B hg) s s :=
  hasSobolevExtension_iff.2 ⟨BesselPotentialSpace.bilinLeftCLM s B hg,
    ContinuousLinearMap.ext fun u ↦ by
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
        BesselPotentialSpace.bilinLeftCLM_toBesselPotentialSpaceCLM s B hg hbd u]⟩

end SchwartzMap

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.TemperedDistribution.ApplyLeft
public import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Multiplication
import TauCeti.Analysis.Calculus.IteratedFDeriv.Basic
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp

/-!
# Operator fields acting on Besov spaces

Let `F` and `G` be finite-dimensional complex normed spaces, let `s ∈ ℝ` and let
`A : E → (F →L[ℂ] G)` be an operator field of temperate growth whose derivatives of order at most
`N` are bounded, for a natural number `N > |s|`. This file proves that `u ↦ A u`
(`TemperedDistribution.applyLeftCLM`) maps the Besov space `B^s_{p,q}(E; F)` boundedly to
`B^s_{p,q}(E; G)` for all `1 ≤ p, q ≤ ∞`, with operator norm at most `C M`, where `M` bounds the
derivatives of `A` of order at most `N` and `C` depends only on the bump function `φ`, on `s`,
on `N` and on the normed spaces `F` and `G`, not on `p` or `q`
(`TauCeti.BesovSpace.exists_toDistr_eq_applyLeftCLM_and_norm_le`). This includes the
Hölder–Zygmund scale `𝒞^s = B^s_{∞,∞}` and negative orders.

These are the changes of frame of a trivialized vector bundle: in local trivializations, a section
of a bundle with fibre `F` is an `F`-valued function, and a change of trivialization multiplies it
by a smooth field of invertible matrices. When `A` has a pointwise inverse `B` whose derivatives
are also bounded, `A` induces an isomorphism `B^s_{p,q}(E; F) ≃ B^s_{p,q}(E; G)`
(`TauCeti.BesovSpace.applyLeftEquiv`), so the Besov regularity of a section read in a
trivialization does not depend on the trivialization.

The proof reduces to scalar multipliers. Writing `A x = ∑ₖ aₖ x • Lₖ` in a basis `(Lₖ)` of
`F →L[ℂ] G`, the operator `A` is `∑ₖ Lₖ ∘ aₖ`
(`TemperedDistribution.applyLeftCLM_eq_sum_basis`). Each coordinate `aₖ` is a smooth scalar
multiplier of Besov spaces (`TauCeti.BesovSpace.exists_toDistr_eq_smulLeftCLM_and_norm_le`), and
a constant operator `L` commutes with the Littlewood–Paley blocks and maps `Lᵖ(E; F)` to
`Lᵖ(E; G)` with norm at most `‖L‖`, so it maps `B^s_{p,q}(E; F)` to `B^s_{p,q}(E; G)` with norm at
most `‖L‖` (`TauCeti.BesovSpace.postcomp`).

## Main declarations

* `TauCeti.BesovSpace.postcomp`: a continuous linear map `L : F →L[ℂ] G` applied to the values,
  as an operator `B^s_{p,q}(E; F) → B^s_{p,q}(E; G)` of norm at most `‖L‖`.
* `TauCeti.BesovSpace.exists_toDistr_eq_applyLeftCLM_and_norm_le`: an operator field with bounded
  derivatives acts boundedly on Besov spaces, with a bound independent of `p` and `q`.
* `TauCeti.BesovSpace.applyLeftCLM`: this action as a bounded operator, and
  `TauCeti.BesovSpace.exists_norm_applyLeftCLM_le` its norm bound.
* `TauCeti.BesovSpace.applyLeftEquiv`: an invertible operator field whose inverse also has bounded
  derivatives induces an isomorphism of Besov spaces.

## References

* H. Triebel, *Theory of Function Spaces*, Birkhäuser, 1983, §2.8.2 (smooth functions as
  pointwise multipliers of Besov spaces).
-/

public section

noncomputable section

open MeasureTheory TemperedDistribution
open scoped ENNReal SchwartzMap

variable {E F G H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G] [NormedAddCommGroup H]
  [NormedSpace ℂ H] [CompleteSpace H]

namespace TauCeti.BesovSpace

variable {φ : ContDiffBump (0 : E)} {s : ℝ} {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-! ### Constant operators -/

/-- A continuous linear map `L : F →L[ℂ] G` applied to the values maps `B^s_{p,q}(E; F)` to
`B^s_{p,q}(E; G)` with norm at most `‖L‖`. -/
theorem exists_toDistr_eq_postcomp_and_norm_le (L : F →L[ℂ] G) (u : BesovSpace F φ s p q) :
    ∃ v : BesovSpace G φ s p q,
      v.toDistr = PointwiseConvergenceCLM.postcomp _ L u.toDistr ∧ ‖v‖ ≤ ‖L‖ * ‖u‖ := by
  refine exists_toDistr_eq_and_norm_le_of_block (norm_nonneg L) u
    (fun j ↦ L.compLp (u.block j)) (fun j ↦ ?_) fun j ↦ ?_
  · ext ψ
    rw [← postcomp_littlewoodPaleyBlock, ← coe_block, PointwiseConvergenceCLM.postcomp_apply,
      Lp.toTemperedDistribution_compLp_apply]
    -- `L ∘ T` evaluates to `L (T ψ)`; `ContinuousLinearMap.comp_apply` does not fire because
    -- `T` is coerced through the type synonym `𝓢'(E, F)` of pointwise convergence.
    rfl
  · calc 2 ^ (s * j) * ‖L.compLp (u.block j)‖ ≤ 2 ^ (s * j) * (‖L‖ * ‖u.block j‖) := by
          gcongr
          exact L.norm_compLp_le _
      _ = ‖L‖ * (2 ^ (s * j) * ‖u.block j‖) := by ring

end TauCeti.BesovSpace

namespace TemperedDistribution

variable {φ : ContDiffBump (0 : E)} {s : ℝ} {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- If `u ∈ B^s_{p,q}(E; F)`, then `L u ∈ B^s_{p,q}(E; G)` for every continuous linear map
`L : F →L[ℂ] G` applied to the values. -/
theorem MemBesov.postcomp {u : 𝓢'(E, F)} (hu : u.MemBesov φ s p q) (L : F →L[ℂ] G) :
    MemBesov φ s p q (PointwiseConvergenceCLM.postcomp _ L u : 𝓢'(E, G)) := by
  obtain ⟨v, hv, -⟩ := TauCeti.BesovSpace.exists_toDistr_eq_postcomp_and_norm_le L hu.toBesovSpace
  rw [← hu.toDistr_toBesovSpace, ← hv]
  exact v.memBesov_toDistr

end TemperedDistribution

namespace TauCeti.BesovSpace

variable {φ : ContDiffBump (0 : E)} {s : ℝ} {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

variable (φ s p q) in
/-- A continuous linear map `L : F →L[ℂ] G` applied to the values, as a bounded operator
`B^s_{p,q}(E; F) → B^s_{p,q}(E; G)` of norm at most `‖L‖`
(`TauCeti.BesovSpace.norm_postcomp_le`). -/
def postcomp (L : F →L[ℂ] G) : BesovSpace F φ s p q →L[ℂ] BesovSpace G φ s p q :=
  LinearMap.mkContinuous
    { toFun u := (u.memBesov_toDistr.postcomp L).toBesovSpace
      map_add' u v := ext (by
        simp only [toDistr_add, MemBesov.toDistr_toBesovSpace]
        exact map_add _ _ _)
      map_smul' c u := ext (by
        simp only [toDistr_smul, MemBesov.toDistr_toBesovSpace, RingHom.id_apply]
        exact map_smul _ _ _) }
    ‖L‖ fun u ↦ by
      obtain ⟨v, hv, hvn⟩ := exists_toDistr_eq_postcomp_and_norm_le L u
      convert hvn using 2
      ext1
      simp only [LinearMap.coe_mk, AddHom.coe_mk, MemBesov.toDistr_toBesovSpace, hv]

@[simp]
theorem toDistr_postcomp (L : F →L[ℂ] G) (u : BesovSpace F φ s p q) :
    (postcomp φ s p q L u).toDistr = PointwiseConvergenceCLM.postcomp _ L u.toDistr :=
  MemBesov.toDistr_toBesovSpace _

theorem norm_postcomp_le (L : F →L[ℂ] G) : ‖postcomp (E := E) φ s p q L‖ ≤ ‖L‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg L) _

/-! ### Operator fields -/

section ApplyLeft

variable [FiniteDimensional ℂ F] [FiniteDimensional ℂ G] [FiniteDimensional ℂ H]

/-- **Operator fields with bounded derivatives act boundedly on Besov spaces.** Let `N` be a
natural number with `|s| < N`. There is `C`, depending only on `φ`, `s`, `N` and the normed spaces
`F` and `G`, with the following property. Let `A : E → (F →L[ℂ] G)` be an operator field of
temperate growth whose derivatives of order at most `N` are bounded by `M`. Then for all
`1 ≤ p, q ≤ ∞` and every `u ∈ B^s_{p,q}(E; F)`, the distribution `A u` lies in
`B^s_{p,q}(E; G)` and `‖A u‖ ≤ C M ‖u‖`. -/
theorem exists_toDistr_eq_applyLeftCLM_and_norm_le (φ : ContDiffBump (0 : E)) {s : ℝ} {N : ℕ}
    (hN : |s| < N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {A : E → F →L[ℂ] G} {M : ℝ}, A.HasTemperateGrowth →
      (∀ n ≤ N, ∀ x, ‖iteratedFDeriv ℝ n A x‖ ≤ M) →
      ∀ {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] (u : BesovSpace F φ s p q),
      ∃ v : BesovSpace G φ s p q, v.toDistr = applyLeftCLM A u.toDistr ∧ ‖v‖ ≤ C * M * ‖u‖ := by
  set b := Module.finBasis ℂ (F →L[ℂ] G)
  -- The coordinate functionals of the basis `b`, as continuous linear maps.
  set c : Fin (Module.finrank ℂ (F →L[ℂ] G)) → (F →L[ℂ] G) →L[ℂ] ℂ :=
    fun k ↦ (b.coord k).toContinuousLinearMap
  obtain ⟨C₀, hC₀, hmul⟩ := exists_toDistr_eq_smulLeftCLM_and_norm_le (F := F) φ hN
  refine ⟨C₀ * ∑ k, ‖b k‖ * ‖c k‖, by positivity, fun {A M} hA hAM {p q} _ _ u ↦ ?_⟩
  -- The `k`-th coordinate `x ↦ c k (A x)` of `A` has derivatives bounded by `‖c k‖ M`.
  have hcA (k) : (fun x ↦ c k (A x)).HasTemperateGrowth :=
    ((c k).restrictScalars ℝ).hasTemperateGrowth.comp hA
  have hcAM (k) : ∀ n ≤ N, ∀ x, ‖iteratedFDeriv ℝ n (fun x ↦ c k (A x)) x‖ ≤ ‖c k‖ * M :=
    fun n hn x ↦ calc
      _ ≤ ‖(c k).restrictScalars ℝ‖ * ‖iteratedFDeriv ℝ n A x‖ :=
        ((c k).restrictScalars ℝ).norm_iteratedFDeriv_comp_left hA.1.contDiffAt
          (mod_cast le_top)
      _ ≤ ‖c k‖ * M := by
        rw [ContinuousLinearMap.norm_restrictScalars]
        gcongr
        exact hAM n hn x
  choose v hv hvn using fun k ↦ hmul (hcA k) (hcAM k) u
  refine ⟨∑ k, postcomp φ s p q (b k) (v k), ?_, ?_⟩
  · simp [applyLeftCLM_eq_sum_basis b hA, hv, c, sum_apply]
  · calc ‖∑ k, postcomp φ s p q (b k) (v k)‖ ≤ ∑ k, ‖b k‖ * (C₀ * (‖c k‖ * M) * ‖u‖) := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ ↦ ?_)
          exact ((postcomp φ s p q (b k)).le_of_opNorm_le (norm_postcomp_le _) _).trans
            (by gcongr; exact hvn k)
      _ = C₀ * (∑ k, ‖b k‖ * ‖c k‖) * M * ‖u‖ := by
          rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
          exact Finset.sum_congr rfl fun k _ ↦ by ring

end ApplyLeft

end TauCeti.BesovSpace

namespace TemperedDistribution

variable [FiniteDimensional ℂ F] [FiniteDimensional ℂ G]
  {φ : ContDiffBump (0 : E)} {s : ℝ} {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- **Smooth operator fields preserve Besov spaces.** If `u ∈ B^s_{p,q}(E; F)` and
`A : E → (F →L[ℂ] G)` is an operator field of temperate growth whose derivatives of order at most
`⌊|s|⌋₊ + 1`, the least natural number exceeding `|s|`, are bounded, then
`A u ∈ B^s_{p,q}(E; G)`. -/
theorem MemBesov.applyLeftCLM {u : 𝓢'(E, F)} (hu : u.MemBesov φ s p q) {A : E → F →L[ℂ] G}
    (hA : A.HasTemperateGrowth)
    (hbd : ∀ n ≤ ⌊|s|⌋₊ + 1, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n A x‖ ≤ C) :
    (applyLeftCLM A u).MemBesov φ s p q := by
  obtain ⟨C, -, hC⟩ := TauCeti.BesovSpace.exists_toDistr_eq_applyLeftCLM_and_norm_le
    (F := F) (G := G) φ (N := ⌊|s|⌋₊ + 1) (by push_cast; exact Nat.lt_floor_add_one _)
  obtain ⟨M, hM⟩ := TauCeti.exists_forall_norm_iteratedFDeriv_le_of_forall_exists hbd
  obtain ⟨v, hv, -⟩ := hC hA hM hu.toBesovSpace
  rw [← hu.toDistr_toBesovSpace, ← hv]
  exact v.memBesov_toDistr

end TemperedDistribution

namespace TauCeti.BesovSpace

variable [FiniteDimensional ℂ F] [FiniteDimensional ℂ G] [FiniteDimensional ℂ H]
  {φ : ContDiffBump (0 : E)} {s : ℝ} {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

variable (φ s p q) in
/-- **A smooth operator field** `A : E → (F →L[ℂ] G)` of temperate growth whose derivatives of
order at most `⌊|s|⌋₊ + 1` are bounded, acting as a bounded operator
`B^s_{p,q}(E; F) → B^s_{p,q}(E; G)`. Its norm is bounded by a constant depending only on `φ`,
`s`, `N`, `F` and `G` times a bound for the derivatives of `A` of order at most `N`, for any
natural number `N > |s|` (`TauCeti.BesovSpace.exists_norm_applyLeftCLM_le`). -/
def applyLeftCLM (A : E → F →L[ℂ] G) (hA : A.HasTemperateGrowth)
    (hbd : ∀ n ≤ ⌊|s|⌋₊ + 1, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n A x‖ ≤ C) :
    BesovSpace F φ s p q →L[ℂ] BesovSpace G φ s p q :=
  LinearMap.mkContinuousOfExistsBound
    { toFun u := (u.memBesov_toDistr.applyLeftCLM hA hbd).toBesovSpace
      map_add' u v := ext (by
        simp only [toDistr_add, MemBesov.toDistr_toBesovSpace]
        exact map_add _ _ _)
      map_smul' c u := ext (by
        simp only [toDistr_smul, MemBesov.toDistr_toBesovSpace, RingHom.id_apply]
        exact map_smul _ _ _) } <| by
    obtain ⟨C, -, hC⟩ := exists_toDistr_eq_applyLeftCLM_and_norm_le (F := F) (G := G) φ
      (N := ⌊|s|⌋₊ + 1) (by push_cast; exact Nat.lt_floor_add_one _)
    obtain ⟨M, hM⟩ := exists_forall_norm_iteratedFDeriv_le_of_forall_exists hbd
    refine ⟨C * M, fun u ↦ ?_⟩
    obtain ⟨v, hv, hvn⟩ := hC hA hM (p := p) (q := q) u
    convert hvn using 2
    ext1
    simp only [LinearMap.coe_mk, AddHom.coe_mk, MemBesov.toDistr_toBesovSpace, hv]

@[simp]
theorem toDistr_applyLeftCLM {A : E → F →L[ℂ] G} (hA : A.HasTemperateGrowth)
    (hbd : ∀ n ≤ ⌊|s|⌋₊ + 1, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n A x‖ ≤ C) (u : BesovSpace F φ s p q) :
    (applyLeftCLM φ s p q A hA hbd u).toDistr = TemperedDistribution.applyLeftCLM A u.toDistr :=
  MemBesov.toDistr_toBesovSpace _

/-- **The norm of a smooth operator field on Besov spaces.** Let `N` be a natural number with
`|s| < N`. There is `C`, depending only on `φ`, `s`, `N`, `F` and `G`, with the following
property. If the derivatives of order at most `N` of `A` are bounded by `M`, then `A` has operator
norm at most `C M` on `B^s_{p,q}` for all `1 ≤ p, q ≤ ∞`. -/
theorem exists_norm_applyLeftCLM_le (φ : ContDiffBump (0 : E)) {N : ℕ} (hN : |s| < N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] {A : E → F →L[ℂ] G}
      (hA : A.HasTemperateGrowth) (hbd : ∀ n ≤ ⌊|s|⌋₊ + 1, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n A x‖ ≤ C)
      {M : ℝ}, (∀ n ≤ N, ∀ x, ‖iteratedFDeriv ℝ n A x‖ ≤ M) →
      ‖applyLeftCLM φ s p q A hA hbd‖ ≤ C * M := by
  obtain ⟨C, hC, happ⟩ := exists_toDistr_eq_applyLeftCLM_and_norm_le (F := F) (G := G) φ hN
  refine ⟨C, hC, fun {p q} _ _ A hA hbd M hAM ↦ ?_⟩
  have hM := (nonneg_and_norm_le_of_norm_iteratedFDeriv_le hAM).1
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun u ↦ ?_
  obtain ⟨v, hv, hvn⟩ := happ hA hAM (p := p) (q := q) u
  have : applyLeftCLM φ s p q A hA hbd u = v := ext (by simp [hv])
  rwa [this]

/-- The action of a composition of smooth operator fields on Besov spaces is the composition of
their actions. -/
theorem applyLeftCLM_applyLeftCLM {A : E → G →L[ℂ] H} {B : E → F →L[ℂ] G}
    (hA : A.HasTemperateGrowth) (hB : B.HasTemperateGrowth)
    (hbdA : ∀ n ≤ ⌊|s|⌋₊ + 1, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n A x‖ ≤ C)
    (hbdB : ∀ n ≤ ⌊|s|⌋₊ + 1, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n B x‖ ≤ C)
    (hAB : (fun x ↦ A x ∘L B x).HasTemperateGrowth)
    (hbdAB : ∀ n ≤ ⌊|s|⌋₊ + 1, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n (fun x ↦ A x ∘L B x) x‖ ≤ C)
    (u : BesovSpace F φ s p q) :
    applyLeftCLM φ s p q A hA hbdA (applyLeftCLM φ s p q B hB hbdB u) =
      applyLeftCLM φ s p q (fun x ↦ A x ∘L B x) hAB hbdAB u :=
  ext (by simp [TemperedDistribution.applyLeftCLM_applyLeftCLM hA hB])

variable (φ s p q) in
/-- **Changes of frame.** An operator field `A : E → (F →L[ℂ] G)` with a pointwise two-sided
inverse `B`, both of temperate growth with derivatives of order at most `⌊|s|⌋₊ + 1` bounded,
induces an isomorphism `B^s_{p,q}(E; F) ≃ B^s_{p,q}(E; G)`. -/
def applyLeftEquiv {A : E → F →L[ℂ] G} {B : E → G →L[ℂ] F} (hA : A.HasTemperateGrowth)
    (hB : B.HasTemperateGrowth)
    (hbdA : ∀ n ≤ ⌊|s|⌋₊ + 1, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n A x‖ ≤ C)
    (hbdB : ∀ n ≤ ⌊|s|⌋₊ + 1, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n B x‖ ≤ C)
    (hBA : ∀ x, B x ∘L A x = ContinuousLinearMap.id ℂ F)
    (hAB : ∀ x, A x ∘L B x = ContinuousLinearMap.id ℂ G) :
    BesovSpace F φ s p q ≃L[ℂ] BesovSpace G φ s p q :=
  ContinuousLinearEquiv.equivOfInverse (applyLeftCLM φ s p q A hA hbdA)
    (applyLeftCLM φ s p q B hB hbdB)
    (fun u ↦ ext (by
      rw [toDistr_applyLeftCLM, toDistr_applyLeftCLM,
        TemperedDistribution.applyLeftCLM_applyLeftCLM hB hA, funext hBA,
        TemperedDistribution.applyLeftCLM_id, ContinuousLinearMap.id_apply]))
    (fun u ↦ ext (by
      rw [toDistr_applyLeftCLM, toDistr_applyLeftCLM,
        TemperedDistribution.applyLeftCLM_applyLeftCLM hA hB, funext hAB,
        TemperedDistribution.applyLeftCLM_id, ContinuousLinearMap.id_apply]))

@[simp]
theorem toDistr_applyLeftEquiv {A : E → F →L[ℂ] G} {B : E → G →L[ℂ] F}
    (hA : A.HasTemperateGrowth) (hB : B.HasTemperateGrowth)
    (hbdA : ∀ n ≤ ⌊|s|⌋₊ + 1, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n A x‖ ≤ C)
    (hbdB : ∀ n ≤ ⌊|s|⌋₊ + 1, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n B x‖ ≤ C)
    (hBA : ∀ x, B x ∘L A x = ContinuousLinearMap.id ℂ F)
    (hAB : ∀ x, A x ∘L B x = ContinuousLinearMap.id ℂ G) (u : BesovSpace F φ s p q) :
    (applyLeftEquiv φ s p q hA hB hbdA hbdB hBA hAB u).toDistr =
      TemperedDistribution.applyLeftCLM A u.toDistr :=
  toDistr_applyLeftCLM hA hbdA u

@[simp]
theorem toDistr_applyLeftEquiv_symm {A : E → F →L[ℂ] G} {B : E → G →L[ℂ] F}
    (hA : A.HasTemperateGrowth) (hB : B.HasTemperateGrowth)
    (hbdA : ∀ n ≤ ⌊|s|⌋₊ + 1, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n A x‖ ≤ C)
    (hbdB : ∀ n ≤ ⌊|s|⌋₊ + 1, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n B x‖ ≤ C)
    (hBA : ∀ x, B x ∘L A x = ContinuousLinearMap.id ℂ F)
    (hAB : ∀ x, A x ∘L B x = ContinuousLinearMap.id ℂ G) (u : BesovSpace G φ s p q) :
    ((applyLeftEquiv φ s p q hA hB hbdA hbdB hBA hAB).symm u).toDistr =
      TemperedDistribution.applyLeftCLM B u.toDistr :=
  toDistr_applyLeftCLM hB hbdB u

end TauCeti.BesovSpace

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.TemperedDistribution.MulLeft
public import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Multiplication
public import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Postcomp
import TauCeti.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.Calculus.IteratedFDeriv.Basic
import TauCeti.Analysis.Distribution.TemperateGrowth
import TauCeti.Analysis.Distribution.TemperedDistribution.SmulLeft
import TauCeti.Topology.Algebra.Module.Spaces.PointwiseConvergenceCLM

/-!
# Multiplication by matrix-valued functions on Besov spaces

Let `F` and `G` be finite-dimensional complex normed spaces, `s ∈ ℝ`, and let
`A : E → (F →L[ℂ] G)` be a smooth matrix-valued function of temperate growth whose derivatives of
order at most `N` are bounded, for a natural number `N > |s|`. Multiplication by `A` maps the
inhomogeneous Besov space `B^s_{p,q}(E; F)` boundedly to `B^s_{p,q}(E; G)` for all
`1 ≤ p, q ≤ ∞` (`TauCeti.BesovSpace.mulLeftCLM`), with operator norm at most `C M`, where `M`
bounds the derivatives of `A` of order at most `N` and `C` depends only on the bump function `φ`,
on `s`, on `N` and on `F` and `G`, not on `p` or `q`
(`TauCeti.BesovSpace.exists_norm_mulLeftCLM_le`). If `A x` is invertible for every `x` and its
inverse has the same properties, multiplication by `A` is an isomorphism
`B^s_{p,q}(E; F) ≃ B^s_{p,q}(E; G)` (`TauCeti.BesovSpace.mulLeftEquiv`). These are the changes of
frame under which Besov norms of sections of vector bundles are compared in local
trivializations, including the Hölder–Zygmund scale `B^s_{∞,∞}`.

The proof reduces to the scalar case `TauCeti.BesovSpace.smulLeftCLM`. In a basis `(L k)` of the
finite-dimensional space `F →L[ℂ] G`, `A x = ∑ k, c k x • L k`, the coordinates `c k` are scalar
functions with derivatives bounded by a constant multiple of those of `A`, and
`A u = ∑ k, L k (c k u)` (`TemperedDistribution.mulLeftCLM_eq_sum`). A constant operator `L` maps
`B^s_{p,q}(E; F)` to `B^s_{p,q}(E; G)` with norm at most `‖L‖` (`TauCeti.BesovSpace.postcomp`).

## Main declarations

* `TemperedDistribution.MemBesov.mulLeftCLM`: `B^s_{p,q}` is stable under multiplication by
  matrix-valued functions of temperate growth with bounded derivatives of order at most
  `⌊|s|⌋₊ + 1`.
* `TauCeti.BesovSpace.mulLeftCLM`: the multiplication as a bounded operator, with its tempered
  distribution `TauCeti.BesovSpace.toDistr_mulLeftCLM` and its norm bound
  `TauCeti.BesovSpace.exists_norm_mulLeftCLM_le`.
* `TauCeti.BesovSpace.mulLeftCLM_compL_mulLeftCLM`, `TauCeti.BesovSpace.mulLeftCLM_const`: the
  multiplications compose as the functions do, and constant functions act by `postcomp`.
* `TauCeti.BesovSpace.mulLeftCLM_smul_id`, `TauCeti.BesovSpace.mulLeftCLM_add`: multiplication by
  `x ↦ g x • id` is the scalar multiplication `TauCeti.BesovSpace.smulLeftCLM`, and the
  multiplication is additive in the function.
* `TauCeti.BesovSpace.mulLeftEquiv`: multiplication by a pointwise invertible function.

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
  [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]

namespace TauCeti.BesovSpace

variable {φ : ContDiffBump (0 : E)} {s : ℝ} {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-! ### Matrix-valued functions -/

section Matrix

variable [FiniteDimensional ℂ F] [FiniteDimensional ℂ G]

variable (φ s p q) in
/-- **Multiplication by a matrix-valued function on Besov spaces.** For a function
`A : E → (F →L[ℂ] G)` of temperate growth whose derivatives of order at most `⌊|s|⌋₊ + 1` are
bounded, the multiplication `u ↦ A u` (`TemperedDistribution.mulLeftCLM`) as a bounded operator
`B^s_{p,q}(E; F) → B^s_{p,q}(E; G)`. Its norm is bounded by a constant depending only on `φ`, `s`,
`N`, `F` and `G` times a bound for the derivatives of `A` of order at most `N`, for any natural
number `N > |s|` (`TauCeti.BesovSpace.exists_norm_mulLeftCLM_le`). -/
def mulLeftCLM (A : E → F →L[ℂ] G) (hA : A.HasTemperateGrowth)
    (hbd : ∀ n ≤ ⌊|s|⌋₊ + 1, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n A x‖ ≤ C) :
    BesovSpace F φ s p q →L[ℂ] BesovSpace G φ s p q :=
  ∑ k, postcomp φ s p q (Module.finBasis ℂ (F →L[ℂ] G) k) ∘L
    smulLeftCLM F φ s p q
      (LinearMap.toContinuousLinearMap ((Module.finBasis ℂ (F →L[ℂ] G)).coord k) ∘ A)
      (hA.continuousLinearMap_comp _)
      (by
        obtain ⟨M, hM⟩ := exists_forall_norm_iteratedFDeriv_le_of_forall_exists hbd
        exact fun n hn ↦ ⟨_, ContinuousLinearMap.norm_iteratedFDeriv_comp_left_le_of_forall_le _
          (hA.1.of_le (mod_cast le_top)) hM n hn⟩)

/-- The tempered distribution of the Besov multiplication `mulLeftCLM φ s p q A hA hbd u` is the
product `TemperedDistribution.mulLeftCLM A u.toDistr` of the tempered distribution of `u`. -/
@[simp]
theorem toDistr_mulLeftCLM {A : E → F →L[ℂ] G} (hA : A.HasTemperateGrowth)
    (hbd : ∀ n ≤ ⌊|s|⌋₊ + 1, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n A x‖ ≤ C)
    (u : BesovSpace F φ s p q) :
    (mulLeftCLM φ s p q A hA hbd u).toDistr = TemperedDistribution.mulLeftCLM A u.toDistr := by
  ext ψ
  rw [TemperedDistribution.mulLeftCLM_apply_apply, ← toDistrCLM_apply, mulLeftCLM, sum_apply,
    map_sum, sum_apply]
  simp only [ContinuousLinearMap.comp_apply, toDistrCLM_apply, toDistr_postcomp,
    toDistr_smulLeftCLM, PointwiseConvergenceCLM.postcomp_apply_apply,
    TemperedDistribution.smulLeftCLM_apply_apply]

end Matrix

end TauCeti.BesovSpace

namespace TemperedDistribution

open TauCeti

variable [FiniteDimensional ℂ F] [FiniteDimensional ℂ G]
  {φ : ContDiffBump (0 : E)} {s : ℝ} {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- **Matrix-valued multipliers of Besov spaces.** If `u ∈ B^s_{p,q}(E; F)` and
`A : E → (F →L[ℂ] G)` is a function of temperate growth whose derivatives of order at most
`⌊|s|⌋₊ + 1`, the least natural number exceeding `|s|`, are bounded, then
`A u ∈ B^s_{p,q}(E; G)`. -/
theorem MemBesov.mulLeftCLM {u : 𝓢'(E, F)} (hu : u.MemBesov φ s p q) {A : E → F →L[ℂ] G}
    (hA : A.HasTemperateGrowth)
    (hbd : ∀ n ≤ ⌊|s|⌋₊ + 1, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n A x‖ ≤ C) :
    MemBesov φ s p q (TemperedDistribution.mulLeftCLM A u) := by
  rw [← hu.toDistr_toBesovSpace, ← BesovSpace.toDistr_mulLeftCLM hA hbd]
  exact BesovSpace.memBesov_toDistr _

end TemperedDistribution

namespace TauCeti.BesovSpace

variable [FiniteDimensional ℂ F] [FiniteDimensional ℂ G]
  {φ : ContDiffBump (0 : E)} {s : ℝ} {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

variable (F G) in
/-- **The norm of a matrix-valued multiplier of Besov spaces.** Let `N` be a natural number with
`|s| < N`. There is `C`, depending only on `φ`, `s`, `N`, `F` and `G`, with the following
property. If the derivatives of order at most `N` of `A : E → (F →L[ℂ] G)` are bounded by `M`,
then multiplication by `A` has operator norm at most `C M` from `B^s_{p,q}(E; F)` to
`B^s_{p,q}(E; G)` for all `1 ≤ p, q ≤ ∞`. -/
theorem exists_norm_mulLeftCLM_le (φ : ContDiffBump (0 : E)) {N : ℕ} (hN : |s| < N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] {A : E → F →L[ℂ] G}
      (hA : A.HasTemperateGrowth)
      (hbd : ∀ n ≤ ⌊|s|⌋₊ + 1, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n A x‖ ≤ C) {M : ℝ},
      (∀ n ≤ N, ∀ x, ‖iteratedFDeriv ℝ n A x‖ ≤ M) →
      ‖mulLeftCLM φ s p q A hA hbd‖ ≤ C * M := by
  obtain ⟨C, hC, hmul⟩ := exists_norm_smulLeftCLM_le (F := F) (s := s) φ hN
  set b := Module.finBasis ℂ (F →L[ℂ] G)
  refine ⟨C * ∑ k, ‖b k‖ * ‖LinearMap.toContinuousLinearMap (b.coord k)‖, by positivity,
    fun {p q} _ _ A hA hbd M hAM ↦ ?_⟩
  -- Each term `L k (c k u)` has norm at most `‖L k‖ C ‖c k‖_{C^N}`, and the derivatives of the
  -- coordinate `c k` are bounded by `‖c k‖ M`.
  rw [mulLeftCLM]
  calc _ ≤ ∑ k, ‖b k‖ * (C * (‖LinearMap.toContinuousLinearMap (b.coord k)‖ * M)) := by
        refine (norm_sum_le _ _).trans ?_
        refine Finset.sum_le_sum fun k _ ↦ (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
        exact mul_le_mul (norm_postcomp_le _) (hmul _ _
          (ContinuousLinearMap.norm_iteratedFDeriv_comp_left_le_of_forall_le
            (LinearMap.toContinuousLinearMap (b.coord k)) (hA.1.of_le (mod_cast le_top)) hAM))
          (norm_nonneg _) (norm_nonneg _)
    _ = C * (∑ k, ‖b k‖ * ‖LinearMap.toContinuousLinearMap (b.coord k)‖) * M := by
        rw [Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun k _ ↦ by ring

/-- **Constant functions.** Multiplication by a constant `L` is `TauCeti.BesovSpace.postcomp`. -/
@[simp]
theorem mulLeftCLM_const (L : F →L[ℂ] G)
    (hbd : ∀ n ≤ ⌊|s|⌋₊ + 1, ∃ C, ∀ x : E, ‖iteratedFDeriv ℝ n (fun _ : E ↦ L) x‖ ≤ C) :
    mulLeftCLM φ s p q (fun _ : E ↦ L) (.const L) hbd = postcomp φ s p q L := by
  ext1 u
  ext1
  rw [toDistr_mulLeftCLM, TemperedDistribution.mulLeftCLM_const, toDistr_postcomp]

omit [FiniteDimensional ℂ G] in
/-- **Scalar functions.** Multiplication by `x ↦ g x • id` is the multiplication
`TauCeti.BesovSpace.smulLeftCLM` by the scalar function `g`. -/
theorem mulLeftCLM_smul_id {g : E → ℂ} (hg : g.HasTemperateGrowth)
    (hbdg : ∀ n ≤ ⌊|s|⌋₊ + 1, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n g x‖ ≤ C)
    (hA : (fun x ↦ g x • ContinuousLinearMap.id ℂ F).HasTemperateGrowth)
    (hbd : ∀ n ≤ ⌊|s|⌋₊ + 1, ∃ C, ∀ x,
      ‖iteratedFDeriv ℝ n (fun x ↦ g x • ContinuousLinearMap.id ℂ F) x‖ ≤ C) :
    mulLeftCLM φ s p q (fun x ↦ g x • ContinuousLinearMap.id ℂ F) hA hbd =
      smulLeftCLM F φ s p q g hg hbdg := by
  ext1 u
  ext1
  rw [toDistr_mulLeftCLM, TemperedDistribution.mulLeftCLM_smul_id hg, toDistr_smulLeftCLM]

/-- **Additivity.** Multiplication by `A + B` is the sum of the multiplications by `A` and by
`B`. -/
theorem mulLeftCLM_add {A B : E → F →L[ℂ] G} (hA : A.HasTemperateGrowth)
    (hbdA : ∀ n ≤ ⌊|s|⌋₊ + 1, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n A x‖ ≤ C)
    (hB : B.HasTemperateGrowth)
    (hbdB : ∀ n ≤ ⌊|s|⌋₊ + 1, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n B x‖ ≤ C)
    (hAB : (A + B).HasTemperateGrowth)
    (hbdAB : ∀ n ≤ ⌊|s|⌋₊ + 1, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n (A + B) x‖ ≤ C) :
    mulLeftCLM φ s p q (A + B) hAB hbdAB =
      mulLeftCLM φ s p q A hA hbdA + mulLeftCLM φ s p q B hB hbdB := by
  ext1 u
  ext1
  rw [toDistr_mulLeftCLM, TemperedDistribution.mulLeftCLM_add hA hB, add_apply, add_apply,
    toDistr_add, toDistr_mulLeftCLM, toDistr_mulLeftCLM]

/-- **Composition.** For `A : E → (F →L[ℂ] G)` and `B : E → (G →L[ℂ] H)`, multiplying by `A` and
then by `B` is multiplying by the pointwise composition `x ↦ B x ∘ A x`. -/
theorem mulLeftCLM_compL_mulLeftCLM [FiniteDimensional ℂ H] {A : E → F →L[ℂ] G}
    {B : E → G →L[ℂ] H} (hA : A.HasTemperateGrowth)
    (hbdA : ∀ n ≤ ⌊|s|⌋₊ + 1, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n A x‖ ≤ C)
    (hB : B.HasTemperateGrowth)
    (hbdB : ∀ n ≤ ⌊|s|⌋₊ + 1, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n B x‖ ≤ C)
    (hBA : (fun x ↦ (B x).comp (A x)).HasTemperateGrowth)
    (hbdBA : ∀ n ≤ ⌊|s|⌋₊ + 1, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n (fun x ↦ (B x).comp (A x)) x‖ ≤ C) :
    mulLeftCLM φ s p q B hB hbdB ∘L mulLeftCLM φ s p q A hA hbdA =
      mulLeftCLM φ s p q (fun x ↦ (B x).comp (A x)) hBA hbdBA := by
  ext1 u
  ext1
  rw [ContinuousLinearMap.comp_apply, toDistr_mulLeftCLM, toDistr_mulLeftCLM, toDistr_mulLeftCLM,
    ← ContinuousLinearMap.comp_apply (TemperedDistribution.mulLeftCLM B),
    TemperedDistribution.mulLeftCLM_compL_mulLeftCLM hA hB]

omit [FiniteDimensional ℂ G] in
/-- Multiplication by the identity is the identity. -/
private theorem mulLeftCLM_eq_id {C : E → F →L[ℂ] F} (hC : ∀ x, C x = .id ℂ F)
    (hC' : C.HasTemperateGrowth)
    (hbd : ∀ n ≤ ⌊|s|⌋₊ + 1, ∃ M, ∀ x, ‖iteratedFDeriv ℝ n C x‖ ≤ M) :
    mulLeftCLM φ s p q C hC' hbd = .id ℂ _ := by
  obtain rfl : C = fun _ ↦ .id ℂ F := funext hC
  rw [mulLeftCLM_const, postcomp_id]

/-- Multiplying by `A` and then by a pointwise left inverse `B` of `A` is the identity. -/
private theorem mulLeftCLM_compL_mulLeftCLM_eq_id {A : E → F →L[ℂ] G} {B : E → G →L[ℂ] F}
    (hA : A.HasTemperateGrowth) (hbdA : ∀ n ≤ ⌊|s|⌋₊ + 1, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n A x‖ ≤ C)
    (hB : B.HasTemperateGrowth) (hbdB : ∀ n ≤ ⌊|s|⌋₊ + 1, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n B x‖ ≤ C)
    (h : ∀ x, (B x).comp (A x) = .id ℂ F) :
    mulLeftCLM φ s p q B hB hbdB ∘L mulLeftCLM φ s p q A hA hbdA = .id ℂ _ := by
  have hBA : (fun x ↦ (B x).comp (A x)) = fun _ ↦ .id ℂ F := funext h
  rw [mulLeftCLM_compL_mulLeftCLM hA hbdA hB hbdB (by rw [hBA]; exact .const _)
      (by rw [hBA]; exact fun n _ ↦ ⟨_, norm_iteratedFDeriv_const_le n _⟩)]
  exact mulLeftCLM_eq_id h _ _

variable (φ s p q) in
/-- **Invertible matrix-valued functions.** If `A : E → (F →L[ℂ] G)` and
`A' : E → (G →L[ℂ] F)` are pointwise inverse to each other, both of temperate growth with bounded
derivatives of order at most `⌊|s|⌋₊ + 1`, then multiplication by `A` is an isomorphism
`B^s_{p,q}(E; F) ≃ B^s_{p,q}(E; G)` with inverse the multiplication by `A'`. -/
def mulLeftEquiv {A : E → F →L[ℂ] G} {A' : E → G →L[ℂ] F} (hA : A.HasTemperateGrowth)
    (hbdA : ∀ n ≤ ⌊|s|⌋₊ + 1, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n A x‖ ≤ C)
    (hA' : A'.HasTemperateGrowth)
    (hbdA' : ∀ n ≤ ⌊|s|⌋₊ + 1, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n A' x‖ ≤ C)
    (hleft : ∀ x, (A' x).comp (A x) = .id ℂ F) (hright : ∀ x, (A x).comp (A' x) = .id ℂ G) :
    BesovSpace F φ s p q ≃L[ℂ] BesovSpace G φ s p q :=
  ContinuousLinearEquiv.ofContinuousLinearMap (mulLeftCLM φ s p q A hA hbdA)
    (mulLeftCLM φ s p q A' hA' hbdA')
    (mulLeftCLM_compL_mulLeftCLM_eq_id hA' hbdA' hA hbdA hright)
    (mulLeftCLM_compL_mulLeftCLM_eq_id hA hbdA hA' hbdA' hleft)

@[simp]
theorem mulLeftEquiv_apply {A : E → F →L[ℂ] G} {A' : E → G →L[ℂ] F} (hA : A.HasTemperateGrowth)
    (hbdA : ∀ n ≤ ⌊|s|⌋₊ + 1, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n A x‖ ≤ C)
    (hA' : A'.HasTemperateGrowth)
    (hbdA' : ∀ n ≤ ⌊|s|⌋₊ + 1, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n A' x‖ ≤ C)
    (hleft : ∀ x, (A' x).comp (A x) = .id ℂ F) (hright : ∀ x, (A x).comp (A' x) = .id ℂ G)
    (u : BesovSpace F φ s p q) :
    mulLeftEquiv φ s p q hA hbdA hA' hbdA' hleft hright u = mulLeftCLM φ s p q A hA hbdA u :=
  (rfl)

@[simp]
theorem mulLeftEquiv_symm_apply {A : E → F →L[ℂ] G} {A' : E → G →L[ℂ] F}
    (hA : A.HasTemperateGrowth)
    (hbdA : ∀ n ≤ ⌊|s|⌋₊ + 1, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n A x‖ ≤ C)
    (hA' : A'.HasTemperateGrowth)
    (hbdA' : ∀ n ≤ ⌊|s|⌋₊ + 1, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n A' x‖ ≤ C)
    (hleft : ∀ x, (A' x).comp (A x) = .id ℂ F) (hright : ∀ x, (A x).comp (A' x) = .id ℂ G)
    (u : BesovSpace G φ s p q) :
    (mulLeftEquiv φ s p q hA hbdA hA' hbdA' hleft hright).symm u =
      mulLeftCLM φ s p q A' hA' hbdA' u :=
  (rfl)

@[simp]
theorem coe_mulLeftEquiv {A : E → F →L[ℂ] G} {A' : E → G →L[ℂ] F} (hA : A.HasTemperateGrowth)
    (hbdA : ∀ n ≤ ⌊|s|⌋₊ + 1, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n A x‖ ≤ C)
    (hA' : A'.HasTemperateGrowth)
    (hbdA' : ∀ n ≤ ⌊|s|⌋₊ + 1, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n A' x‖ ≤ C)
    (hleft : ∀ x, (A' x).comp (A x) = .id ℂ F) (hright : ∀ x, (A x).comp (A' x) = .id ℂ G) :
    (mulLeftEquiv φ s p q hA hbdA hA' hbdA' hleft hright : _ →L[ℂ] _) =
      mulLeftCLM φ s p q A hA hbdA :=
  (rfl)

@[simp]
theorem coe_mulLeftEquiv_symm {A : E → F →L[ℂ] G} {A' : E → G →L[ℂ] F}
    (hA : A.HasTemperateGrowth)
    (hbdA : ∀ n ≤ ⌊|s|⌋₊ + 1, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n A x‖ ≤ C)
    (hA' : A'.HasTemperateGrowth)
    (hbdA' : ∀ n ≤ ⌊|s|⌋₊ + 1, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n A' x‖ ≤ C)
    (hleft : ∀ x, (A' x).comp (A x) = .id ℂ F) (hright : ∀ x, (A x).comp (A' x) = .id ℂ G) :
    ((mulLeftEquiv φ s p q hA hbdA hA' hbdA' hleft hright).symm : _ →L[ℂ] _) =
      mulLeftCLM φ s p q A' hA' hbdA' :=
  (rfl)

end TauCeti.BesovSpace

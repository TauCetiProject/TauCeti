/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.lpSpace
public import TauCeti.Analysis.Normed.Module.Bases.Basic
public import TauCeti.Analysis.Normed.Module.BoundedCoefficients
import TauCeti.Analysis.Normed.Operator.Dense

/-!
# Rearrangements and coordinate multipliers of unconditional bases

An unconditional basis stays a basis under every rearrangement of its index type:
`UnconditionalSchauderBasis.reindex` transports it along an equivalence, keeping its finite
projections and its basis constant `nnNormProjBound`. For an unconditional basis indexed by `ℕ`
and a permutation `π` of `ℕ`, `(b.reindex π).toSchauderBasis` is the rearranged classical
Schauder basis.

Over real or complex scalars, a uniform bound on the projections of a basis onto all finite sets
controls all bounded coordinate multipliers. If every such projection has norm at most `C`, the
multiplier `x ↦ ∑ i ∈ A, a i • b.coord i x • b i` has norm at most `2 * t * C` for real
coefficients and `4 * t * C` for scalar coefficients of norm at most `t`. In particular a uniform
bound on finite coordinate projections is equivalent to one on signed coordinate multipliers
(`GeneralSchauderBasis.exists_forall_norm_proj_le_iff`). For an `ℕ`-indexed generalized Schauder
basis, a uniform bound `C` on signed multipliers along initial segments `Finset.range N` transfers
without loss of constant to bounded real multipliers and finite coordinate projections over
arbitrary finite sets, and with a factor of `2` to bounded scalar multipliers
(`GeneralSchauderBasis.norm_proj_le_of_forall_range_abs_eq_one`). Whenever the finite projections
of a basis with a nontrivial summation filter are uniformly bounded, its coordinate series
converges unconditionally (`GeneralSchauderBasis.hasSum_of_norm_proj_le`), even without
completeness of the ambient space.

In a Banach space every bounded scalar family `a ∈ ℓ^∞(β, 𝕜)` then defines the multiplier
`x ↦ ∑' i, a i • b.coord i x • b i`, whose series converges unconditionally
(`UnconditionalSchauderBasis.hasSum_multiplier`). This is the continuous bilinear map
`UnconditionalSchauderBasis.multiplier`, of norm at most `4 * b.nnNormProjBound` (and at most `C`
over `ℝ` or `2 * C` over `𝕜` from initial-segment sign bounds `C`); it acts on each basis vector
by its coefficient and is multiplicative, sending `1` to the identity.

## References

* F. Albiac and N. J. Kalton, *Topics in Banach Space Theory*, Section 3.1.
* J. Lindenstrauss and L. Tzafriri, *Classical Banach Spaces I*, Section 1.c.
-/

public section

noncomputable section

open Filter Set Topology
open scoped ENNReal lp

namespace UnconditionalSchauderBasis

section Reindex

variable {β γ 𝕜 X : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  (b : UnconditionalSchauderBasis β 𝕜 X)

/-- The rearrangement of an unconditional basis along an equivalence of index types. -/
protected def reindex (e : β ≃ γ) : UnconditionalSchauderBasis γ 𝕜 X where
  basis := b ∘ e.symm
  coord := b.coord ∘ e.symm
  ortho i j := by
    classical
    simp only [Function.comp_apply, b.ortho, Pi.single_apply]
    exact if_congr e.symm.injective.eq_iff rfl rfl
  expansion x := (e.symm.hasSum_iff (f := fun i ↦ b.coord i x • b i)).2 (b.expansion x)

/-- The basis vectors of a rearranged basis are the rearranged basis vectors. -/
@[simp]
theorem coe_reindex (e : β ≃ γ) : ⇑(b.reindex e) = b ∘ e.symm :=
  (rfl)

/-- The coordinate functionals of a rearranged basis are the rearranged coordinate functionals. -/
@[simp]
theorem coord_reindex (e : β ≃ γ) : (b.reindex e).coord = b.coord ∘ e.symm :=
  (rfl)

/-- The projection of a rearranged basis onto `A` is the projection onto the image of `A`. -/
@[simp]
theorem proj_reindex (e : β ≃ γ) (A : Finset γ) :
    (b.reindex e).proj A = b.proj (A.map e.symm.toEmbedding) := by
  ext x
  simp

/-- Rearranging an unconditional basis preserves its basis constant. -/
@[simp]
theorem nnnormProjBound_reindex (e : β ≃ γ) :
    (b.reindex e).nnNormProjBound = b.nnNormProjBound := by
  simp only [nnNormProjBound, proj_reindex, ← Equiv.finsetCongr_apply]
  exact e.symm.finsetCongr.iSup_comp (g := fun A ↦ ‖b.proj A‖₊)

end Reindex

end UnconditionalSchauderBasis

namespace GeneralSchauderBasis

section NormProjLe

variable {β 𝕜 X : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  {L : SummationFilter β} (b : GeneralSchauderBasis β 𝕜 X L)

/-- If the finite coordinate projections of a generalized Schauder basis with a nontrivial
summation filter are uniformly bounded, then the basis expansion of every vector converges
unconditionally. -/
theorem hasSum_of_norm_proj_le [L.NeBot] {C : ℝ} (hC : ∀ A : Finset β, ‖b.proj A‖ ≤ C) (x : X) :
    HasSum (fun i ↦ b.coord i x • b i) x := by
  classical
  -- Each finite combination of basis vectors is fixed by `b.proj A` once `A` contains its support,
  -- and uniform boundedness of `b.proj` propagates convergence from the dense span to `X`.
  rw [HasSum, SummationFilter.unconditional_filter]
  simp_rw [← b.proj_apply]
  refine ContinuousLinearMap.tendsto_apply_of_dense b.dense_span (.of_forall hC)
    (g := .id 𝕜 X) (fun y hy ↦ ?_) x
  obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hy
  refine tendsto_atTop_of_eventually_const (i₀ := c.support) fun A hA ↦ ?_
  rw [ContinuousLinearMap.id_apply, Finsupp.sum, map_sum]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [map_smul, b.proj_apply_basis_mem, ite_eq_left (hA hi)]

end NormProjLe

section BoundedMultipliers

variable {β 𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  {L : SummationFilter β} (b : GeneralSchauderBasis β 𝕜 X L)

/-- If every finite coordinate projection has norm at most `C`, then the coordinate multiplier
with real coefficients of absolute value at most `t` has norm at most `2 * t * C`. -/
theorem norm_sum_ofReal_smul_coord_smul_le {C : ℝ} (hC : ∀ A : Finset β, ‖b.proj A‖ ≤ C)
    (A : Finset β) {a : β → ℝ} {t : ℝ} (ht : 0 ≤ t) (ha : ∀ i ∈ A, |a i| ≤ t) (x : X) :
    ‖∑ i ∈ A, (a i : 𝕜) • b.coord i x • b i‖ ≤ 2 * t * C * ‖x‖ := by
  rw [mul_assoc _ C]
  refine TauCeti.norm_sum_ofReal_smul_le_two_mul (fun u _ ↦ ?_) ht ha
  simpa using (b.proj u).le_of_opNorm_le (hC u) x

/-- If every finite coordinate projection has norm at most `C`, then the coordinate multiplier
with scalar coefficients of norm at most `t` has norm at most `4 * t * C`. -/
theorem norm_sum_smul_coord_smul_le {C : ℝ} (hC : ∀ A : Finset β, ‖b.proj A‖ ≤ C)
    (A : Finset β) {a : β → 𝕜} {t : ℝ} (ht : 0 ≤ t) (ha : ∀ i ∈ A, ‖a i‖ ≤ t) (x : X) :
    ‖∑ i ∈ A, a i • b.coord i x • b i‖ ≤ 4 * t * C * ‖x‖ := by
  rw [mul_assoc _ C]
  refine TauCeti.norm_sum_smul_le_four_mul (fun u _ ↦ ?_) ht ha
  simpa using (b.proj u).le_of_opNorm_le (hC u) x

/-- The finite coordinate projections of a generalized Schauder basis are uniformly bounded if
and only if its signed coordinate multipliers `x ↦ ∑ i ∈ A, ε i • b.coord i x • b i`, with
`ε i = ±1`, are uniformly bounded. -/
theorem exists_forall_norm_proj_le_iff :
    (∃ C, ∀ A : Finset β, ‖b.proj A‖ ≤ C) ↔
      ∃ C, ∀ (A : Finset β) (ε : β → ℝ), (∀ i, ε i = 1 ∨ ε i = -1) →
        ∀ x, ‖∑ i ∈ A, (ε i : 𝕜) • b.coord i x • b i‖ ≤ C * ‖x‖ := by
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨2 * 1 * C, fun A ε hε x ↦
      b.norm_sum_ofReal_smul_coord_smul_le hC A zero_le_one (fun i _ ↦ ?_) x⟩
    rcases hε i with h | h <;> simp [h]
  · rintro ⟨C, hC⟩
    -- The constant sign `1` gives the projections themselves.
    refine ⟨max C 0, fun A ↦ (b.proj A).opNorm_le_bound (le_max_right _ _) fun x ↦ ?_⟩
    have h := hC A 1 (fun _ ↦ Or.inl rfl) x
    simp only [Pi.one_apply, RCLike.ofReal_one, one_smul] at h
    rw [proj_apply]
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg x))

end BoundedMultipliers

section InitialSegments

variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  {L : SummationFilter ℕ} (b : GeneralSchauderBasis ℕ 𝕜 X L)

/-- If every `±1`-signed coordinate multiplier along an initial segment `Finset.range N` has norm
at most `S` at `x`, then every real coordinate multiplier over an arbitrary finite set `A` with
coefficients of absolute value at most `t` has norm at most `t * S` at `x`. -/
theorem norm_sum_ofReal_smul_coord_smul_le_of_forall_range {S : ℝ} {x : X}
    (hS : ∀ (N : ℕ) (ε : ℕ → ℝ), (∀ n, |ε n| = 1) →
      ‖∑ n ∈ Finset.range N, (ε n : 𝕜) • b.coord n x • b n‖ ≤ S)
    (A : Finset ℕ) {a : ℕ → ℝ} {t : ℝ} (ht : 0 ≤ t) (ha : ∀ n ∈ A, |a n| ≤ t) :
    ‖∑ n ∈ A, (a n : 𝕜) • b.coord n x • b n‖ ≤ t * S := by
  classical
  -- Embed `A` in `Finset.range (A.sup id).succ` and extend `a` by `0` outside `A`.
  let N := (A.sup id).succ
  let a' : ℕ → ℝ := fun n ↦ if n ∈ A then a n else 0
  have heq : ∑ n ∈ A, (a n : 𝕜) • b.coord n x • b n =
      ∑ n ∈ Finset.range N, (a' n : 𝕜) • b.coord n x • b n := by
    rw [← Finset.sum_subset (Finset.subset_range_sup_succ A)]
    · exact Finset.sum_congr rfl fun n hn ↦ by simp [a', hn]
    · intro n _ hn
      simp [a', hn]
  rw [heq]
  refine TauCeti.norm_sum_ofReal_smul_le_of_forall_abs_eq_one (hS N) ht fun n _ ↦ ?_
  dsimp only [a']
  split_ifs with hn
  · exact ha n hn
  · simpa using ht

/-- If every `±1`-signed coordinate multiplier along an initial segment `Finset.range N` has norm
at most `S` at `x`, then every scalar coordinate multiplier over an arbitrary finite set `A` with
coefficients of norm at most `t` has norm at most `2 * t * S` at `x`. -/
theorem norm_sum_smul_coord_smul_le_of_forall_range {S : ℝ} {x : X}
    (hS : ∀ (N : ℕ) (ε : ℕ → ℝ), (∀ n, |ε n| = 1) →
      ‖∑ n ∈ Finset.range N, (ε n : 𝕜) • b.coord n x • b n‖ ≤ S)
    (A : Finset ℕ) {a : ℕ → 𝕜} {t : ℝ} (ht : 0 ≤ t) (ha : ∀ n ∈ A, ‖a n‖ ≤ t) :
    ‖∑ n ∈ A, a n • b.coord n x • b n‖ ≤ 2 * t * S :=
  TauCeti.norm_sum_smul_le_two_mul_of_forall_abs_eq_one
    (fun ε hε ↦ by
      simpa using b.norm_sum_ofReal_smul_coord_smul_le_of_forall_range hS A zero_le_one
        fun n _ ↦ (hε n).le)
    ht ha

/-- If every `±1`-signed coordinate multiplier along an initial segment `Finset.range N` has
operator norm at most `C`, then every finite coordinate projection `b.proj A` also has operator
norm at most `C`. -/
theorem norm_proj_le_of_forall_range_abs_eq_one {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ (N : ℕ) (ε : ℕ → ℝ), (∀ n, |ε n| = 1) →
      ∀ x, ‖∑ n ∈ Finset.range N, (ε n : 𝕜) • b.coord n x • b n‖ ≤ C * ‖x‖)
    (A : Finset ℕ) :
    ‖b.proj A‖ ≤ C := by
  refine (b.proj A).opNorm_le_bound hC0 fun x ↦ ?_
  have h := b.norm_sum_ofReal_smul_coord_smul_le_of_forall_range
    (fun N ε hε ↦ hC N ε hε x) A (a := 1) zero_le_one (fun _ _ ↦ by simp)
  simpa [proj_apply] using h

end InitialSegments

end GeneralSchauderBasis

namespace UnconditionalSchauderBasis

section Multiplier

variable {β 𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [CompleteSpace X] (b : UnconditionalSchauderBasis β 𝕜 X)

/-- In a Banach space, the expansion of a vector along an unconditional basis stays
unconditionally summable after multiplying its terms by a bounded scalar family. -/
theorem summable_smul_coord_smul (a : ℓ^∞(β, 𝕜)) (x : X) :
    Summable fun i ↦ a i • b.coord i x • b i := by
  refine summable_iff_vanishing_norm.2 fun ε hε ↦ ?_
  -- The tails of the expansion of `x` are uniformly small, and so are the multiplied tails.
  have hδ : 0 < ε / (4 * (‖a‖ + 1)) := by positivity
  obtain ⟨A₀, hA₀⟩ := summable_iff_vanishing_norm.1 (b.expansion x).summable _ hδ
  refine ⟨A₀, fun B hB ↦ ?_⟩
  calc
    ‖∑ i ∈ B, a i • b.coord i x • b i‖ ≤ 4 * ‖a‖ * (ε / (4 * (‖a‖ + 1))) :=
      TauCeti.norm_sum_smul_le_four_mul (fun u hu ↦ (hA₀ u (hB.mono_left hu)).le)
        (norm_nonneg a) fun i _ ↦ lp.norm_apply_le_norm ENNReal.top_ne_zero a i
    _ = ε * (‖a‖ / (‖a‖ + 1)) := by field_simp
    _ < ε * 1 := by
      gcongr
      exact (div_lt_one (by positivity)).2 (lt_add_one _)
    _ = ε := mul_one ε

/-- The coordinate multiplier series of a bounded scalar family is bounded by `4` times the
basis constant, the norm of the family and the norm of the vector. -/
private theorem norm_tsum_smul_coord_smul_le (a : ℓ^∞(β, 𝕜)) (x : X) :
    ‖∑' i, a i • b.coord i x • b i‖ ≤ 4 * b.nnNormProjBound * ‖a‖ * ‖x‖ := by
  refine le_of_tendsto' (b.summable_smul_coord_smul a x).hasSum.norm fun A ↦ ?_
  calc
    ‖∑ i ∈ A, a i • b.coord i x • b i‖ ≤ 4 * ‖a‖ * b.nnNormProjBound * ‖x‖ :=
      b.norm_sum_smul_coord_smul_le b.norm_proj_le_nnNormProjBound A (norm_nonneg a)
        (fun i _ ↦ lp.norm_apply_le_norm ENNReal.top_ne_zero a i) x
    _ = 4 * b.nnNormProjBound * ‖a‖ * ‖x‖ := by ring

/-- The coordinate multiplier of an unconditional basis of a Banach space: a bounded scalar family
`a` acts by `x ↦ ∑' i, a i • b.coord i x • b i`. -/
def multiplier : ℓ^∞(β, 𝕜) →L[𝕜] X →L[𝕜] X :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ 𝕜 (fun a x ↦ ∑' i, a i • b.coord i x • b i)
      (fun a a' x ↦ by
        simp only [lp.coeFn_add, Pi.add_apply, add_smul]
        exact (b.summable_smul_coord_smul a x).tsum_add (b.summable_smul_coord_smul a' x))
      (fun c a x ↦ by
        simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, mul_smul]
        exact (b.summable_smul_coord_smul a x).tsum_const_smul c)
      (fun a x y ↦ by
        simp only [map_add, add_smul, smul_add]
        exact (b.summable_smul_coord_smul a x).tsum_add (b.summable_smul_coord_smul a y))
      (fun c a x ↦ by
        simp only [map_smul, smul_eq_mul, mul_smul, smul_comm (a _) c]
        exact (b.summable_smul_coord_smul a x).tsum_const_smul c))
    (4 * b.nnNormProjBound) b.norm_tsum_smul_coord_smul_le

/-- The coordinate multiplier series converges unconditionally to the multiplier. -/
theorem hasSum_multiplier (a : ℓ^∞(β, 𝕜)) (x : X) :
    HasSum (fun i ↦ a i • b.coord i x • b i) (b.multiplier a x) :=
  (b.summable_smul_coord_smul a x).hasSum

/-- The coordinate multiplier is the sum of the multiplied expansion. -/
theorem multiplier_apply (a : ℓ^∞(β, 𝕜)) (x : X) :
    b.multiplier a x = ∑' i, a i • b.coord i x • b i :=
  (rfl)

/-- If every finite partial sum of the multiplied expansion has operator norm at most `M`, with
`0 ≤ M`, then `b.multiplier a` has operator norm at most `M`. -/
theorem norm_multiplier_le_of_forall_sum_le (a : ℓ^∞(β, 𝕜)) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ (A : Finset β) (x : X), ‖∑ i ∈ A, a i • b.coord i x • b i‖ ≤ M * ‖x‖) :
    ‖b.multiplier a‖ ≤ M :=
  (b.multiplier a).opNorm_le_bound hM0 fun x ↦
    le_of_tendsto' (b.hasSum_multiplier a x).norm fun A ↦ hM A x

/-- The coordinate multiplier has norm at most `4` times the basis constant and the norm of the
coefficient family. -/
theorem norm_multiplier_le (a : ℓ^∞(β, 𝕜)) :
    ‖b.multiplier a‖ ≤ 4 * b.nnNormProjBound * ‖a‖ :=
  (b.multiplier a).opNorm_le_bound (by positivity) (b.norm_tsum_smul_coord_smul_le a)

/-- The coordinate multiplier map has norm at most `4` times the basis constant. -/
theorem norm_multiplier_le' : ‖b.multiplier‖ ≤ 4 * b.nnNormProjBound :=
  b.multiplier.opNorm_le_bound (by positivity) b.norm_multiplier_le

/-- Coordinates of a multiplied vector are multiplied by the coefficients. -/
@[simp]
theorem coord_multiplier (a : ℓ^∞(β, 𝕜)) (i : β) (x : X) :
    b.coord i (b.multiplier a x) = a i * b.coord i x := by
  classical
  rw [multiplier_apply, (b.coord i).map_tsum (b.summable_smul_coord_smul a x),
    tsum_eq_single i fun j hj ↦ by simp [b.ortho, Ne.symm hj]]
  simp [b.ortho]

/-- The coordinate multiplier acts on a basis vector by its coefficient. -/
@[simp]
theorem multiplier_apply_basis (a : ℓ^∞(β, 𝕜)) (i : β) : b.multiplier a (b i) = a i • b i := by
  classical
  rw [multiplier_apply, tsum_eq_single i fun j hj ↦ by simp [b.ortho, hj]]
  simp [b.ortho]

/-- A bounded operator is the coordinate multiplier of `a` exactly when it acts on each basis
vector by the corresponding coefficient. -/
theorem multiplier_eq_iff {a : ℓ^∞(β, 𝕜)} {T : X →L[𝕜] X} :
    b.multiplier a = T ↔ ∀ i, T (b i) = a i • b i := by
  refine ⟨fun h i ↦ h ▸ b.multiplier_apply_basis a i, fun h ↦ ?_⟩
  refine ContinuousLinearMap.ext_on b.dense_span ?_
  rintro _ ⟨i, rfl⟩
  rw [multiplier_apply_basis, h]

/-- The constant coefficient family `1` multiplies by the identity. -/
@[simp]
theorem multiplier_one : b.multiplier 1 = ContinuousLinearMap.id 𝕜 X :=
  b.multiplier_eq_iff.2 fun i ↦ by simp [lp.infty_coeFn_one]

/-- Coordinate multipliers compose by multiplying their coefficient families. -/
theorem multiplier_mul (a c : ℓ^∞(β, 𝕜)) :
    b.multiplier (a * c) = (b.multiplier a).comp (b.multiplier c) :=
  b.multiplier_eq_iff.2 fun i ↦ by simp [lp.infty_coeFn_mul, smul_smul, mul_comm]

end Multiplier

section NatMultiplier

/-- Over `ℝ`, if every `±1`-signed coordinate multiplier along an initial segment `Finset.range N`
has operator norm at most `C` (`0 ≤ C`), then `b.multiplier a` has operator norm at most
`C * ‖a‖`. -/
theorem norm_multiplier_le_of_forall_range_abs_eq_one
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (b : UnconditionalSchauderBasis ℕ ℝ X) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ (N : ℕ) (ε : ℕ → ℝ), (∀ n, |ε n| = 1) →
      ∀ x, ‖∑ n ∈ Finset.range N, ε n • b.coord n x • b n‖ ≤ C * ‖x‖)
    (a : ℓ^∞(ℕ, ℝ)) :
    ‖b.multiplier a‖ ≤ C * ‖a‖ :=
  b.norm_multiplier_le_of_forall_sum_le a (mul_nonneg hC0 (norm_nonneg a)) fun A x ↦ by
    have h := b.norm_sum_ofReal_smul_coord_smul_le_of_forall_range
      (fun N ε hε ↦ by simpa using hC N ε hε x) A (norm_nonneg a)
      fun n _ ↦ by simpa using lp.norm_apply_le_norm ENNReal.top_ne_zero a n
    simpa only [RCLike.ofReal_real_eq_id, id_eq] using h.trans_eq (by ring)

/-- If every `±1`-signed coordinate multiplier along an initial segment `Finset.range N` has
operator norm at most `C` (`0 ≤ C`), then `b.multiplier a` has operator norm at most
`2 * C * ‖a‖`. -/
theorem norm_multiplier_le_two_mul_of_forall_range_abs_eq_one
    {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
    (b : UnconditionalSchauderBasis ℕ 𝕜 X) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ (N : ℕ) (ε : ℕ → ℝ), (∀ n, |ε n| = 1) →
      ∀ x, ‖∑ n ∈ Finset.range N, (ε n : 𝕜) • b.coord n x • b n‖ ≤ C * ‖x‖)
    (a : ℓ^∞(ℕ, 𝕜)) :
    ‖b.multiplier a‖ ≤ 2 * C * ‖a‖ :=
  b.norm_multiplier_le_of_forall_sum_le a (by positivity) fun A x ↦
    (b.norm_sum_smul_coord_smul_le_of_forall_range (fun N ε hε ↦ hC N ε hε x) A (norm_nonneg a)
      fun n _ ↦ lp.norm_apply_le_norm ENNReal.top_ne_zero a n).trans_eq (by ring)

end NatMultiplier

end UnconditionalSchauderBasis

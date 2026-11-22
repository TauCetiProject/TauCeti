/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.LinearAlgebra.Basis.VectorSpace
import TauCeti.Analysis.Normed.Operator.Dense

/-!
# Coordinates on `lp`

The characteristic equation and single-coordinate retraction identities for Mathlib's bundled
coordinate evaluation (`lp.evalCLM_apply`, `lp.evalCLM_comp_singleContinuousLinearMap`,
`lp.leftInverse_evalCLM_singleContinuousLinearMap`, `lp.evalCLM_surjective`) let users compute
with `lp.evalCLM` without unfolding its construction as a bounded linear map, and the ℓ¹ norm is
the sum of the norms of the coordinates (`lp.hasSum_norm_one`, and `lp.hasSum_enorm_one` for
extended norms); for `1 ≤ p` it bounds the `ℓ^p` norm (`lp.norm_le_tsum_norm`). Sequences whose
coordinates have the same norms have the same `ℓᵖ` norm (`lp.norm_eq_of_forall_norm_eq`); in
particular the sequence `i ↦ ‖f i‖` of coordinate norms of `f ∈ ℓᵖ` (`lp.normSeq`) has `ℓᵖ` norm
`‖f‖` (`lp.norm_normSeq`). For Hölder conjugate exponents `p` and `q`, including `1` and `∞`,
every finite sum of `‖f i‖ ‖g i‖` is at most `‖f‖ ‖g‖` (`lp.sum_norm_mul_norm_le`). For `0 < p ≤ q`
the `ℓ^q` norm of a sequence is at most its `ℓᵖ` norm (`lp.norm_le_norm_of_exponent_le`), the norm
form of Mathlib's inclusion `Memℓp.of_exponent_ge`. A sequence indexed by `ℕ` whose terms are
bounded by a geometric sequence `C rⁱ` with `0 ≤ r < 1` lies in every `ℓᵖ` with `p ≠ 0`
(`Memℓp.of_norm_le_geometric`), and for `1 ≤ p` its `ℓᵖ` norm is at most `C (1 - r)⁻¹`
(`lp.norm_le_of_norm_le_geometric`). Rescaling an infinite linearly independent sequence, an
infinite-dimensional normed space therefore contains, for each `p ≠ 0`, a linearly independent
sequence in `ℓᵖ` (`lp.exists_linearIndependent`). Membership in `ℓᵖ` is unchanged by a unit scalar
factor (`IsUnit.memℓp_smul_iff`), and conversely, for `p ≠ 0` the geometric sequence `rⁱ`, or a
nonzero multiple `C rⁱ` of it, lies in `ℓᵖ` exactly when `‖r‖ < 1`, or `‖r‖ = 1` and `p = ∞`
(`TauCeti.memℓp_pow_iff`, `TauCeti.memℓp_const_mul_pow_iff`). The scalar coordinate vectors are
linearly independent, and vectors in the span of single-coordinate vectors vanish outside the
corresponding indices. These algebraic facts hold over normed rings at every exponent; over a ring
with the strong rank condition, for instance a field, `lp` over an infinite index type is therefore
not a finite module (`lp.not_finite`). Finite sums of single-coordinate vectors over a finset `s`
along a map `g` evaluate to the corresponding entry at `g j` (`j ∈ s`) when `g` is injective on `s`
(`lp.sum_single_apply_of_injOn_of_mem`) and vanish at coordinates not equal to any `g i` (`i ∈ s`)
(`lp.sum_single_apply_eq_zero_of_forall_ne`). Subtracting a finite sum of coordinate vectors
zeroes out those coordinates (`lp.sub_sum_single_apply`) and does not increase the `ℓᵖ` norm, for
any `p` (`lp.norm_sub_sum_single_le`). In `ℓ²`, the squared norm of a finite sum of
single-coordinate vectors is the sum of the squared norms of its coordinates
(`lp.norm_sum_single_sq`, and `lp.enorm_sum_single` for the extended norm). It follows that the
operators `v ↦ (aᵢ v)ᵢ` from `F` to `ℓ²(F)` and `(wᵢ) ↦ ∑ᵢ aᵢ wᵢ` from `ℓ²(F)` to `F`, for finitely
many scalars `aᵢ`, have norm at most `‖(aᵢ)‖_{ℓ²}` (`lp.norm_sum_single_comp_lsmul_le`,
`lp.norm_sum_lsmul_comp_evalCLM_le`).

A uniformly bounded family of operators with a common domain assembles into an `ℓ∞`-valued
operator (`ContinuousLinearMap.piLpInfty`), with the same norm bound.

For `p ≠ ∞`, every sequence in `ℓᵖ` has countable support (`Memℓp.countable_dsupport`,
`lp.countable_dsupport`). For `1 ≤ p`, separability of `lp E p` forces the subtype of indices with
nontrivial fibres `{i : ι // Nontrivial (E i)}` to be countable because the open balls of radius
`‖v i‖ / 2` around `lp.single p i (v i)` (`v i ≠ 0`) are pairwise disjoint
(`lp.countable_nontrivial_of_separableSpace`, specializing to `lp.countable_of_separableSpace` when
all fibres are nontrivial). For `1 ≤ p < ∞`, `lp E p` is separable if and only if every fibre `E i`
is separable and `{i : ι // Nontrivial (E i)}` is countable (`lp.separableSpace_iff`),
specializing to `lp.separableSpace` and `lp.separableSpace_iff_countable`.

For `p ≠ ∞` the coordinate vectors span a dense subspace, so a uniformly bounded family of
operators on `lp E p` that converges on every `single i x` converges at every vector
(`lp.tendsto_apply_of_tendsto_apply_single`). In the scalar case such an operator `T` is given by
its coordinate series `T x = ∑ i, xᵢ • T eᵢ` (`ContinuousLinearMap.hasSum_smul_lp_single`), so for
`q ≠ ∞` an operator out of `ℓ^q` into a Hausdorff space is determined by its values on the unit
coordinate vectors (`ContinuousLinearMap.ext_lp_of_ne_top`). On ℓ¹, a uniform bound `C` on the
norms `‖T eᵢ‖` bounds `‖T‖` (`ContinuousLinearMap.opNorm_lpOne_le`), so the norm of `T` is the
supremum of the norms `‖T eᵢ‖` (`ContinuousLinearMap.norm_eq_ciSup_norm_lp_single`,
`ContinuousLinearMap.nnnorm_eq_ciSup_nnnorm_lp_single`).
-/

public section

open scoped ENNReal NNReal lp Topology
open Filter

namespace ContinuousLinearMap

variable {ι 𝕜 X : Type*} {E : ι → Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup X] [NormedSpace 𝕜 X]
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]

/-- A uniformly bounded family of operators, assembled into an operator with values in `ℓ∞`. -/
noncomputable def piLpInfty (f : ∀ i, X →L[𝕜] E i) (C : ℝ≥0) (hf : ∀ i, ‖f i‖₊ ≤ C) :
    X →L[𝕜] lp E ∞ :=
  LinearMap.mkContinuous
    { toFun x := ⟨fun i ↦ f i x, memℓp_infty ⟨C * ‖x‖, by
        rintro _ ⟨i, rfl⟩
        exact (f i).le_of_opNorm_le (mod_cast hf i) x⟩⟩
      map_add' x y := lp.ext <| funext fun i ↦ (f i).map_add x y
      map_smul' c x := lp.ext <| funext fun i ↦ (f i).map_smul c x }
    C fun x ↦ lp.norm_le_of_forall_le (by positivity) fun i ↦
      (f i).le_of_opNorm_le (mod_cast hf i) x

/-- Each coordinate of the assembled operator is the corresponding member of the family. -/
@[simp]
theorem piLpInfty_apply (f : ∀ i, X →L[𝕜] E i) (C : ℝ≥0) (hf : ∀ i, ‖f i‖₊ ≤ C)
    (x : X) (i : ι) : piLpInfty f C hf x i = f i x := (rfl)

/-- The norm of the assembled operator is at most the uniform bound. -/
theorem nnnorm_piLpInfty_le (f : ∀ i, X →L[𝕜] E i) (C : ℝ≥0) (hf : ∀ i, ‖f i‖₊ ≤ C) :
    ‖piLpInfty f C hf‖₊ ≤ C := by
  refine opNNNorm_le_bound _ _ fun x ↦ ?_
  exact_mod_cast lp.norm_le_of_forall_le (by positivity : 0 ≤ (C : ℝ) * ‖x‖)
    fun i ↦ (f i).le_of_opNorm_le (mod_cast hf i) x

end ContinuousLinearMap

/-- For `p ≠ ∞`, a sequence in `ℓᵖ` vanishes outside a countable set of indices. -/
theorem Memℓp.countable_dsupport {ι : Type*} {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
    {p : ℝ≥0∞} {f : ∀ i, E i} (hf : Memℓp f p) (hp : p ≠ ∞) : {i | f i ≠ 0}.Countable := by
  rcases eq_or_ne p 0 with rfl | hp0
  · exact hf.finite_dsupport.countable
  · have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
    refine (hf.summable hpr).countable_support.mono fun i hi ↦ ?_
    exact (Real.rpow_pos_of_pos (norm_pos_iff.2 hi) p.toReal).ne'

namespace lp

variable {ι 𝕜 : Type*} {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
  [NormedRing 𝕜] [∀ i, Module 𝕜 (E i)] [∀ i, IsBoundedSMul 𝕜 (E i)]
  {p : ℝ≥0∞}

/-- The bundled coordinate evaluation returns the corresponding coordinate. -/
@[simp]
theorem evalCLM_apply [Fact (1 ≤ p)] (i : ι) (x : lp E p) : evalCLM 𝕜 E p i x = x i := (rfl)

/-- The ℓ¹ norm is the sum of the norms of the coordinates. -/
theorem hasSum_norm_one (y : lp E 1) : HasSum (fun i ↦ ‖y i‖) ‖y‖ := by
  simpa using lp.hasSum_norm (p := 1) (by simp) y

/-- **The `ℓᵖ` norms decrease in the exponent.** For `0 < p ≤ q`, a sequence `f ∈ ℓᵖ` lies in
`ℓ^q` (`Memℓp.of_exponent_ge`), and its `ℓ^q` norm is at most its `ℓᵖ` norm. -/
theorem norm_le_norm_of_exponent_le {q : ℝ≥0∞} (hp : p ≠ 0) (hpq : p ≤ q) {f : lp E p}
    {g : lp E q} (hfg : ∀ i, g i = f i) : ‖g‖ ≤ ‖f‖ := by
  rcases eq_or_ne q ∞ with rfl | hq
  · exact norm_le_of_forall_le (norm_nonneg' f) fun i ↦ (hfg i).symm ▸ norm_apply_le_norm hp f i
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp (ne_top_of_le_ne_top hq hpq)
  have hpq' : p.toReal ≤ q.toReal := ENNReal.toReal_mono hq hpq
  have hqr : 0 < q.toReal := hpr.trans_le hpq'
  -- Split `t ^ q = t ^ (q - p) * t ^ p` and bound the first factor by `‖f‖ ^ (q - p)`.
  have hsplit (t : ℝ) (ht : 0 ≤ t) : t ^ q.toReal = t ^ (q.toReal - p.toReal) * t ^ p.toReal := by
    rw [← Real.rpow_add' ht (by simpa using hqr.ne'), sub_add_cancel]
  refine norm_le_of_forall_sum_le hqr (norm_nonneg' f) fun s ↦ ?_
  calc ∑ i ∈ s, ‖g i‖ ^ q.toReal
      ≤ ∑ i ∈ s, ‖f‖ ^ (q.toReal - p.toReal) * ‖f i‖ ^ p.toReal := by
        gcongr with i
        rw [hfg i, hsplit _ (norm_nonneg _)]
        gcongr
        exact norm_apply_le_norm hp f i
    _ = ‖f‖ ^ (q.toReal - p.toReal) * ∑ i ∈ s, ‖f i‖ ^ p.toReal := (Finset.mul_sum ..).symm
    _ ≤ ‖f‖ ^ (q.toReal - p.toReal) * ‖f‖ ^ p.toReal :=
        mul_le_mul_of_nonneg_left (sum_rpow_le_norm_rpow hpr f s)
          (Real.rpow_nonneg (norm_nonneg' f) _)
    _ = ‖f‖ ^ q.toReal := (hsplit _ (norm_nonneg' f)).symm

/-- For `1 ≤ p`, the `ℓ^p` norm of a sequence is at most its `ℓ¹` norm. -/
theorem norm_le_tsum_norm [Fact (1 ≤ p)] (f : lp E p)
    (hf : Summable fun i ↦ ‖f i‖) : ‖f‖ ≤ ∑' i, ‖f i‖ := by
  -- The same sequence, viewed in `ℓ¹`, where its norm is the sum of the norms of its coordinates.
  let g : lp E 1 := ⟨f, memℓp_gen (by simpa using hf)⟩
  calc ‖f‖ ≤ ‖g‖ := norm_le_norm_of_exponent_le one_ne_zero Fact.out fun _ ↦ rfl
    _ = ∑' i, ‖f i‖ := (hasSum_norm_one g).tsum_eq.symm

/-- The extended ℓ¹ norm is the sum of the extended norms of the coordinates. -/
theorem hasSum_enorm_one (y : lp E 1) : HasSum (fun i ↦ ‖y i‖ₑ) ‖y‖ₑ := by
  simp only [eNorm_eq_nnNorm]
  exact ENNReal.hasSum_coe.2 (NNReal.hasSum_coe.1 (hasSum_norm_one y))

/-- Two sequences whose coordinates have the same norms have the same `ℓᵖ` norm. For instance,
the sequence of norms `i ↦ ‖f i‖` of `f ∈ ℓᵖ` has `ℓᵖ` norm `‖f‖`. -/
theorem norm_eq_of_forall_norm_eq {F : ι → Type*} [∀ i, NormedAddCommGroup (F i)] {f : lp E p}
    {g : lp F p} (h : ∀ i, ‖f i‖ = ‖g i‖) : ‖f‖ = ‖g‖ := by
  rcases eq_or_ne p 0 with rfl | hp
  · have hs : {i | f i ≠ 0} = {i | g i ≠ 0} := by
      ext i
      rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, ← norm_ne_zero_iff, h i, norm_ne_zero_iff]
    simp only [norm_eq_card_dsupport, hs]
  · exact (norm_mono hp fun i ↦ (h i).le).antisymm (norm_mono hp fun i ↦ (h i).ge)

/-- The sequence `i ↦ ‖f i‖` of the norms of the coordinates of `f ∈ ℓᵖ`, as an element of the
scalar `ℓᵖ`. It has the same norm as `f` (`lp.norm_normSeq`). -/
def normSeq (f : lp E p) : lp (fun _ : ι ↦ ℝ) p :=
  ⟨fun i ↦ ‖f i‖, (lp.memℓp f).norm⟩

@[simp]
theorem normSeq_apply (f : lp E p) (i : ι) : normSeq f i = ‖f i‖ := (rfl)

@[simp]
theorem norm_normSeq (f : lp E p) : ‖normSeq f‖ = ‖f‖ :=
  norm_eq_of_forall_norm_eq fun i ↦ by simp

/-- The coordinates of the Hölder pairing `lp.holderL r B hBK e f` are `B i (e i) (f i)`. -/
@[simp]
theorem holderL_apply_apply_coe {𝕜 : Type*} [RCLike 𝕜] {F G : ι → Type*}
    [∀ i, NormedSpace 𝕜 (E i)] [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace 𝕜 (F i)]
    [∀ i, NormedAddCommGroup (G i)] [∀ i, NormedSpace 𝕜 (G i)] {q : ℝ≥0∞} (r : ℝ≥0∞)
    [p.HolderTriple q r] [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ r)]
    (B : (i : ι) → E i →L[𝕜] F i →L[𝕜] G i) {K : ℝ≥0} (hBK : ∀ i, ‖B i‖ ≤ K) (e : lp E p)
    (f : lp F q) (i : ι) : holderL r B hBK e f i = B i (e i) (f i) := by
  rw [holderL, LinearMap.mkContinuous₂_apply, holderₗ_apply_apply_coe]

/-- **Hölder's inequality in `ℓᵖ`, for finite sums.** For Hölder conjugate exponents `p` and `q`,
every finite sum of `‖f i‖ ‖g i‖` is at most `‖f‖ ‖g‖`. Unlike `lp.tsum_mul_le_mul_norm`, this
allows the exponents `1` and `∞`. -/
theorem sum_norm_mul_norm_le {F : ι → Type*} [∀ i, NormedAddCommGroup (F i)] {q : ℝ≥0∞}
    [p.HolderConjugate q] (f : lp E p) (g : lp F q) (s : Finset ι) :
    ∑ i ∈ s, ‖f i‖ * ‖g i‖ ≤ ‖f‖ * ‖g‖ := by
  have : Fact (1 ≤ p) := ⟨ENNReal.HolderConjugate.one_le p q⟩
  have : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
  -- Pair the sequences of norms by multiplication, a bilinear map of norm at most `1`.
  have hB : ∀ _ : ι, ‖ContinuousLinearMap.mul ℝ ℝ‖ ≤ (1 : ℝ≥0) := fun _ ↦ by simp
  set P := holderL (p := p) (q := q) 1 (fun _ : ι ↦ ContinuousLinearMap.mul ℝ ℝ) hB
  have h1 := sum_rpow_le_norm_rpow (p := 1) (by simp) (P (normSeq f) (normSeq g)) s
  simp only [ENNReal.toReal_one, Real.rpow_one] at h1
  calc ∑ i ∈ s, ‖f i‖ * ‖g i‖ ≤ ∑ i ∈ s, ‖P (normSeq f) (normSeq g) i‖ :=
        Finset.sum_le_sum fun i _ ↦ by simp [P]
    _ ≤ ‖P‖ * ‖normSeq f‖ * ‖normSeq g‖ := h1.trans (P.le_opNorm₂ _ _)
    _ ≤ 1 * ‖f‖ * ‖g‖ := by
        rw [norm_normSeq, norm_normSeq]
        gcongr
        exact norm_holderL_le 1 _ hB
    _ = ‖f‖ * ‖g‖ := by rw [one_mul]

section Single

variable [DecidableEq ι]

/-- The scalar coordinate vectors in `lp` are linearly independent. -/
theorem linearIndependent_single_one :
    LinearIndependent 𝕜 (fun i : ι ↦ lp.single p i (1 : 𝕜)) := by
  apply LinearIndependent.of_comp (lpSubmodule 𝕜 (fun _ : ι ↦ 𝕜) p).subtype
  have hcoe : (lpSubmodule 𝕜 (fun _ : ι ↦ 𝕜) p).subtype ∘
      (fun i : ι ↦ lp.single p i (1 : 𝕜)) = fun i ↦ Pi.single i (1 : 𝕜) := by
    funext i
    exact lp.coeFn_single p i 1
  rw [hcoe]
  exact Pi.linearIndependent_single_one ι 𝕜

/-- A vector in the span of a family of single-coordinate vectors vanishes outside their indices. -/
theorem apply_eq_zero_of_mem_span_single {κ : Type*} (f : κ → ι) {v : ∀ j, E (f j)}
    {x : lp E p} (hx : x ∈ Submodule.span 𝕜 (Set.range fun j ↦ lp.single p (f j) (v j)))
    {i : ι} (hi : i ∉ Set.range f) : x i = 0 := by
  have hle : Submodule.span 𝕜 (Set.range fun j ↦ lp.single p (f j) (v j)) ≤
      LinearMap.ker (evalₗ (𝕜 := 𝕜) E p i) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨j, rfl⟩
    apply LinearMap.mem_ker.mpr
    rw [evalₗ_apply]
    exact lp.single_apply_ne p (f j) (v j) (fun hij ↦ hi ⟨j, hij.symm⟩)
  simpa only [evalₗ_apply] using LinearMap.mem_ker.mp (hle hx)

/-- Evaluating a finite sum of single-coordinate vectors `∑ i ∈ s, lp.single p (g i) (v i)` at
`g j` for `j ∈ s` recovers `v j`, provided `g` is injective on `s`. -/
theorem sum_single_apply_of_injOn_of_mem {κ : Type*} {s : Finset κ} {g : κ → ι}
    {v : ∀ i, E (g i)} {j : κ} (hg : Set.InjOn g s) (hj : j ∈ s) :
    (∑ i ∈ s, lp.single p (g i) (v i)) (g j) = v j := by
  rw [lp.coeFn_sum, Finset.sum_apply, Finset.sum_eq_single j
    (fun i hi hne ↦ lp.single_apply_ne p (g i) (v i) fun h ↦ hne (hg hi hj h.symm))
    (fun h ↦ absurd hj h), lp.single_apply_self]

/-- Evaluating a finite sum of single-coordinate vectors `∑ i ∈ s, lp.single p (g i) (v i)` at a
coordinate `k` not equal to `g i` for any `i ∈ s` returns `0`. -/
theorem sum_single_apply_eq_zero_of_forall_ne {κ : Type*} {s : Finset κ} {g : κ → ι}
    {v : ∀ i, E (g i)} {k : ι} (hk : ∀ i ∈ s, k ≠ g i) :
    (∑ i ∈ s, lp.single p (g i) (v i)) k = 0 := by
  rw [lp.coeFn_sum, Finset.sum_apply]
  exact Finset.sum_eq_zero fun i hi ↦ lp.single_apply_ne p (g i) (v i) (hk i hi)

omit [DecidableEq ι] in
/-- For an infinite index type, the scalar sequence space `lp` is not a finite module. -/
theorem not_finite [Infinite ι] [StrongRankCondition 𝕜] :
    ¬ Module.Finite 𝕜 (lp (fun _ : ι ↦ 𝕜) p) := fun _ ↦ by
  classical
  exact Module.Finite.not_linearIndependent_of_infinite _
    (linearIndependent_single_one (ι := ι) (𝕜 := 𝕜) (p := p))

end Single

/-- Evaluating a single-coordinate vector at its own coordinate is the identity continuous linear
map. -/
@[simp]
theorem evalCLM_comp_singleContinuousLinearMap [Fact (1 ≤ p)] [DecidableEq ι] (i : ι) :
    (evalCLM 𝕜 E p i).comp (singleContinuousLinearMap 𝕜 E p i) = .id 𝕜 (E i) := by
  ext x
  simp

/-- Bundled coordinate evaluation at `i` is a left inverse to the single-coordinate inclusion at
`i`. -/
theorem leftInverse_evalCLM_singleContinuousLinearMap [Fact (1 ≤ p)] [DecidableEq ι] (i : ι) :
    Function.LeftInverse (evalCLM 𝕜 E p i) (singleContinuousLinearMap 𝕜 E p i) :=
  fun x ↦ by simp

/-- Bundled coordinate evaluation on `lp E p` is surjective at every coordinate. -/
theorem evalCLM_surjective [Fact (1 ≤ p)] (i : ι) :
    Function.Surjective (evalCLM 𝕜 E p i) := by
  classical
  exact fun x ↦ ⟨lp.single p i x, by simp⟩

/-- The square of the `ℓ²` norm of a finite sum of single-coordinate vectors is the sum of the
squared norms of the coordinates. -/
theorem norm_sum_single_sq [DecidableEq ι] (f : ∀ i, E i) (s : Finset ι) :
    ‖∑ i ∈ s, lp.single 2 i (f i)‖ ^ 2 = ∑ i ∈ s, ‖f i‖ ^ 2 := by
  simpa [Real.rpow_two] using lp.norm_sum_single (E := E) (p := 2) (by norm_num) f s

/-- The extended `ℓ²` norm of a finite sum of single-coordinate vectors is the square root of the
sum of the squared extended norms of the coordinates. -/
theorem enorm_sum_single [DecidableEq ι] (f : ∀ i, E i) (s : Finset ι) :
    ‖∑ i ∈ s, lp.single 2 i (f i)‖ₑ = (∑ i ∈ s, ‖f i‖ₑ ^ 2) ^ (2⁻¹ : ℝ) := by
  have h : ‖∑ i ∈ s, lp.single 2 i (f i)‖ = (∑ i ∈ s, ‖f i‖ ^ 2) ^ (2⁻¹ : ℝ) := by
    rw [← norm_sum_single_sq, ← one_div, ← Real.sqrt_eq_rpow, Real.sqrt_sq (norm_nonneg _)]
  rw [← ofReal_norm, h, ← ENNReal.ofReal_rpow_of_nonneg
      (Finset.sum_nonneg fun _ _ ↦ by positivity) (by norm_num),
    ENNReal.ofReal_sum_of_nonneg fun _ _ ↦ by positivity]
  simp_rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

/-- Evaluating `v - ∑ i ∈ s, lp.single p i (v i)` at coordinate `j` gives `0` on `s` and `v j`
outside `s`. -/
theorem sub_sum_single_apply [DecidableEq ι] (v : lp E p) (s : Finset ι) (j : ι) :
    (v - ∑ i ∈ s, lp.single p i (v i)) j = if j ∈ s then 0 else v j := by
  simp only [lp.coeFn_sub, lp.coeFn_sum, lp.coeFn_single, Pi.sub_apply, Finset.sum_apply,
    Finset.sum_pi_single]
  split_ifs <;> simp

/-- Subtracting the partial sum of coordinate vectors over a finite set `s` does not increase the
`ℓᵖ` norm, for every exponent `p` (including `p = 0`, where the norm counts the nonzero coordinates,
and `p = ∞`). -/
theorem norm_sub_sum_single_le [DecidableEq ι] (v : lp E p) (s : Finset ι) :
    ‖v - ∑ i ∈ s, lp.single p i (v i)‖ ≤ ‖v‖ := by
  rcases eq_or_ne p 0 with rfl | hp
  · -- For `p = 0` the norm counts the nonzero coordinates, and no new ones appear.
    rw [norm_eq_card_dsupport, norm_eq_card_dsupport, Nat.cast_le]
    refine Finset.card_le_card (Set.Finite.toFinset_subset_toFinset.2 fun j hj ↦ ?_)
    rw [Set.mem_ofPred_eq, sub_sum_single_apply] at hj
    split_ifs at hj
    exacts [(hj rfl).elim, hj]
  · refine lp.norm_mono hp fun j ↦ ?_
    rw [sub_sum_single_apply]
    split_ifs <;> simp

section Operator

open ContinuousLinearMap

variable {𝕜 R F : Type*} [NontriviallyNormedField 𝕜] [NormedRing R] [NormedAlgebra 𝕜 R]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [Module R F] [IsBoundedSMul R F]
  [IsScalarTower 𝕜 R F] [DecidableEq ι]

/-- The operator `v ↦ (aᵢ v)ᵢ` from `F` to `ℓ²(F)` has norm at most `‖(aᵢ)‖_{ℓ²}`. -/
theorem norm_sum_single_comp_lsmul_le (s : Finset ι) (a : ι → R) :
    ‖∑ i ∈ s, (lp.singleContinuousLinearMap 𝕜 (fun _ : ι ↦ F) 2 i).comp (lsmul 𝕜 R (a i))‖ ≤
      ‖∑ i ∈ s, lp.single 2 i (a i)‖ := by
  refine opNorm_le_bound _ (norm_nonneg _) fun v ↦ ?_
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
  simp only [sum_apply, coe_comp, Function.comp_apply, lsmul_apply,
    lp.singleContinuousLinearMap_apply]
  rw [lp.norm_sum_single_sq, mul_pow, lp.norm_sum_single_sq, Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  rw [← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_smul_le _ _) 2

/-- The operator `(wᵢ) ↦ ∑ᵢ aᵢ wᵢ` from `ℓ²(F)` to `F` has norm at most `‖(aᵢ)‖_{ℓ²}`. -/
theorem norm_sum_lsmul_comp_evalCLM_le (s : Finset ι) (a : ι → R) :
    ‖∑ i ∈ s, (lsmul 𝕜 R (a i)).comp (lp.evalCLM 𝕜 (fun _ : ι ↦ F) 2 i)‖ ≤
      ‖∑ i ∈ s, lp.single 2 i (a i)‖ := by
  refine opNorm_le_bound _ (norm_nonneg _) fun w ↦ ?_
  have ha : √(∑ i ∈ s, ‖a i‖ ^ 2) = ‖∑ i ∈ s, lp.single 2 i (a i)‖ := by
    rw [← lp.norm_sum_single_sq, Real.sqrt_sq (norm_nonneg _)]
  have hw : √(∑ i ∈ s, ‖w i‖ ^ 2) ≤ ‖w‖ := by
    refine Real.sqrt_le_iff.2 ⟨norm_nonneg _, ?_⟩
    simpa [Real.rpow_two] using lp.sum_rpow_le_norm_rpow (p := 2) (by norm_num) w s
  simp only [sum_apply, coe_comp, Function.comp_apply, lsmul_apply, evalCLM_apply]
  calc ‖∑ i ∈ s, a i • w i‖
      ≤ ∑ i ∈ s, ‖a i‖ * ‖w i‖ := (norm_sum_le _ _).trans (Finset.sum_le_sum fun _ _ ↦
        norm_smul_le _ _)
    _ ≤ √(∑ i ∈ s, ‖a i‖ ^ 2) * √(∑ i ∈ s, ‖w i‖ ^ 2) := Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ ≤ ‖∑ i ∈ s, lp.single 2 i (a i)‖ * ‖w‖ := by rw [ha]; gcongr

end Operator

section Density

variable {ι 𝕜 : Type*} {E : ι → Type*} [NontriviallyNormedField 𝕜]
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **Bounded convergence on coordinate vectors.** For `p ≠ ∞`, a uniformly bounded family of
operators on `lp E p` that converges at every coordinate vector `single i x` converges at every
vector. -/
theorem tendsto_apply_of_tendsto_apply_single [DecidableEq ι] {Z : Type*}
    [SeminormedAddCommGroup Z] [NormedSpace 𝕜 Z] (hp : p ≠ ∞) {α : Type*} {l : Filter α}
    {f : α → lp E p →L[𝕜] Z} {g : lp E p →L[𝕜] Z} {C : ℝ} (hC : ∀ᶠ a in l, ‖f a‖ ≤ C)
    (h : ∀ i (x : E i), Tendsto (fun a ↦ f a (lp.single p i x)) l (𝓝 (g (lp.single p i x))))
    (x : lp E p) : Tendsto (fun a ↦ f a x) l (𝓝 (g x)) := by
  let D : Submodule 𝕜 (lp E p) :=
    { carrier := {y | Tendsto (fun a ↦ f a y) l (𝓝 (g y))}
      add_mem' := fun hy hz ↦ by simpa only [Set.mem_ofPred_eq, map_add] using hy.add hz
      zero_mem' := by simpa only [Set.mem_ofPred_eq, map_zero] using tendsto_const_nhds
      smul_mem' := fun c y hy ↦ by simpa only [Set.mem_ofPred_eq, map_smul] using hy.const_smul c }
  have hD : Dense (D : Set (lp E p)) := fun y ↦
    mem_closure_of_tendsto (lp.hasSum_single hp y)
      (Eventually.of_forall fun s ↦ D.sum_mem fun i _ ↦ h i (y i))
  exact ContinuousLinearMap.tendsto_apply_of_dense hD hC (fun y hy ↦ hy) x

end Density

/-- For `p ≠ ∞`, every vector of `lp E p` vanishes outside a countable set of indices. -/
theorem countable_dsupport (hp : p ≠ ∞) (f : lp E p) : {i | f i ≠ 0}.Countable :=
  (lp.memℓp f).countable_dsupport hp

variable (E p) in
/-- If `lp E p` (`1 ≤ p`) is separable, then the subtype of indices with nontrivial fibres is
countable. -/
theorem countable_nontrivial_of_separableSpace [Fact (1 ≤ p)]
    [TopologicalSpace.SeparableSpace (lp E p)] :
    Countable {i : ι // Nontrivial (E i)} := by
  classical
  let v : ∀ i : {i : ι // Nontrivial (E i)}, E i.val :=
    fun i ↦ (@exists_ne (E i.val) i.property 0).choose
  have hv (i : {i : ι // Nontrivial (E i)}) : v i ≠ 0 :=
    (@exists_ne (E i.val) i.property 0).choose_spec
  have hd : Pairwise (Function.onFun Disjoint
      fun i : {i : ι // Nontrivial (E i)} ↦
        Metric.ball (lp.single p i.val (v i)) (‖v i‖ / 2)) := by
    intro i j hij
    refine Metric.ball_disjoint_ball ?_
    have hij' : i.val ≠ j.val := Subtype.coe_ne_coe.2 hij
    have hi := (lp.lipschitzWith_one_eval p i.val).dist_le_mul
      (lp.single p i.val (v i)) (lp.single p j.val (v j))
    have hj := (lp.lipschitzWith_one_eval p j.val).dist_le_mul
      (lp.single p i.val (v i)) (lp.single p j.val (v j))
    simp only [NNReal.coe_one, one_mul, lp.single_apply, Pi.single_eq_same,
      Pi.single_eq_of_ne hij', Pi.single_eq_of_ne' hij', dist_zero_right, dist_zero_left] at hi hj
    linarith
  exact hd.countable_of_isOpen_disjoint (fun _ ↦ Metric.isOpen_ball)
    (fun i ↦ ⟨_, Metric.mem_ball_self (half_pos (norm_pos_iff.2 (hv i)))⟩)

variable (E p) in
/-- If `lp E p` (`1 ≤ p`) is separable and every fibre `E i` is nontrivial, then the index type `ι`
is countable. -/
theorem countable_of_separableSpace [∀ i, Nontrivial (E i)] [Fact (1 ≤ p)]
    [TopologicalSpace.SeparableSpace (lp E p)] : Countable ι :=
  have := countable_nontrivial_of_separableSpace E p
  Countable.of_equiv _ (Equiv.subtypeUnivEquiv ‹∀ i, Nontrivial (E i)›)

/-- For `1 ≤ p < ∞`, `lp E p` is separable when only countably many fibres are nontrivial and
every fibre `E i` is separable. -/
theorem separableSpace_of_countable_nontrivial [Fact (1 ≤ p)] (hp : p ≠ ∞)
    [Countable {i : ι // Nontrivial (E i)}] [∀ i, TopologicalSpace.SeparableSpace (E i)] :
    TopologicalSpace.SeparableSpace (lp E p) := by
  classical
  set S : Set (lp E p) := ⋃ i : {i : ι // Nontrivial (E i)}, Set.range (lp.single p i.val)
  have hS : TopologicalSpace.IsSeparable S :=
    .iUnion fun i ↦ TopologicalSpace.isSeparable_range (lp.isometry_single i.val).continuous
  rw [← TopologicalSpace.isSeparable_univ_iff]
  -- Every element is the limit of the finite sums of its coordinate vectors, which lie in the
  -- additive span of `S`.
  refine (hS.span (R := ℕ)).closure.mono fun f _ ↦
    mem_closure_of_tendsto (lp.hasSum_single hp f) (Filter.Eventually.of_forall fun s ↦ ?_)
  refine Submodule.sum_mem _ fun i _ ↦ ?_
  by_cases hi : Nontrivial (E i)
  · exact Submodule.subset_span (Set.mem_iUnion.2 ⟨⟨i, hi⟩, f i, rfl⟩)
  · rw [not_nontrivial_iff_subsingleton] at hi
    simp [Subsingleton.elim (f i) 0]

/-- For `1 ≤ p < ∞`, `lp E p` is separable if and only if the subtype of indices with nontrivial
fibres is countable and every fibre `E i` is separable. -/
theorem separableSpace_iff [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    TopologicalSpace.SeparableSpace (lp E p) ↔
      Countable {i : ι // Nontrivial (E i)} ∧ ∀ i, TopologicalSpace.SeparableSpace (E i) := by
  classical
  refine ⟨fun _ ↦ ⟨countable_nontrivial_of_separableSpace E p, fun i ↦ ?_⟩,
    fun ⟨_, _⟩ ↦ separableSpace_of_countable_nontrivial hp⟩
  have : SecondCountableTopology (lp E p) := UniformSpace.secondCountable_of_separable (lp E p)
  exact (lp.isometry_single (E := E) (p := p) i).isEmbedding.separableSpace

/-- For a finite exponent and a countable index type, `lp E p` is separable when every `E i` is.
-/
theorem separableSpace [Countable ι] [∀ i, TopologicalSpace.SeparableSpace (E i)]
    [Fact (1 ≤ p)] (hp : p ≠ ⊤) : TopologicalSpace.SeparableSpace (lp E p) :=
  (separableSpace_iff hp).2 ⟨inferInstance, inferInstance⟩

/-- For `1 ≤ p < ∞` and nontrivial separable fibres `E i`, `lp E p` is separable if and only if the
index type `ι` is countable. -/
theorem separableSpace_iff_countable [∀ i, Nontrivial (E i)]
    [∀ i, TopologicalSpace.SeparableSpace (E i)] [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    TopologicalSpace.SeparableSpace (lp E p) ↔ Countable ι :=
  (separableSpace_iff hp).trans
    ⟨fun ⟨h, _⟩ ↦ Countable.of_equiv _ (Equiv.subtypeUnivEquiv ‹∀ i, Nontrivial (E i)›),
     fun _ ↦ ⟨inferInstance, inferInstance⟩⟩

end lp

section Smul

variable {ι 𝕜 : Type*} {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] {p : ℝ≥0∞} [NormedRing 𝕜]
  [∀ i, Module 𝕜 (E i)] [∀ i, IsBoundedSMul 𝕜 (E i)]

/-- Multiplying a sequence by a unit does not change whether it lies in `ℓᵖ`. -/
theorem IsUnit.memℓp_smul_iff {c : 𝕜} (hc : IsUnit c) {f : ∀ i, E i} :
    Memℓp (c • f) p ↔ Memℓp f p := by
  obtain ⟨u, rfl⟩ := hc
  refine ⟨fun hf ↦ ?_, fun hf ↦ hf.const_smul _⟩
  simpa [smul_smul] using hf.const_smul (↑u⁻¹ : 𝕜)

end Smul

section Geometric

variable {E : ℕ → Type*} [∀ i, NormedAddCommGroup (E i)] {p : ℝ≥0∞} {C r : ℝ}

/-- A sequence whose terms are bounded by a geometric sequence `C rⁱ` with `0 ≤ r < 1` lies in
every `ℓᵖ` with `p ≠ 0`. -/
theorem Memℓp.of_norm_le_geometric {f : ∀ i, E i} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hf : ∀ i, ‖f i‖ ≤ C * r ^ i) (hp : p ≠ 0) : Memℓp f p := by
  have hC : 0 ≤ C := (norm_nonneg _).trans ((hf 0).trans_eq (by simp))
  have hgeom (t : ℝ≥0∞) (ht : 0 < t.toReal) : Memℓp f t := by
    refine memℓp_gen <| Summable.of_nonneg_of_le (fun i ↦ by positivity) (fun i ↦ ?_)
      ((summable_geometric_of_lt_one (by positivity)
        (Real.rpow_lt_one hr0 hr1 ht)).mul_left (C ^ t.toReal))
    calc ‖f i‖ ^ t.toReal ≤ (C * r ^ i) ^ t.toReal :=
          Real.rpow_le_rpow (norm_nonneg _) (hf i) ht.le
      _ = C ^ t.toReal * (r ^ t.toReal) ^ i := by
          rw [Real.mul_rpow hC (by positivity), Real.rpow_pow_comm hr0]
  rcases eq_or_ne p ∞ with rfl | hptop
  · exact (hgeom 1 (by simp)).of_exponent_ge le_top
  · exact hgeom p (ENNReal.toReal_pos hp hptop)

/-- For `1 ≤ p`, a sequence in `ℓᵖ` whose terms are bounded by a geometric sequence `C rⁱ` with
`0 ≤ r < 1` has `ℓᵖ` norm at most `C (1 - r)⁻¹`. -/
theorem lp.norm_le_of_norm_le_geometric [Fact (1 ≤ p)] {f : lp E p} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hf : ∀ i, ‖f i‖ ≤ C * r ^ i) : ‖f‖ ≤ C * (1 - r)⁻¹ := by
  have hgeom := (summable_geometric_of_lt_one hr0 hr1).mul_left C
  calc ‖f‖ ≤ ∑' i, ‖f i‖ :=
        lp.norm_le_tsum_norm f (hgeom.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hf)
    _ ≤ ∑' i, C * r ^ i :=
        (hgeom.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hf).tsum_le_tsum hf hgeom
    _ = C * (1 - r)⁻¹ := by rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]

/-- An infinite-dimensional normed space contains a linearly independent sequence lying in `ℓᵖ`,
for every `p ≠ 0`. -/
theorem lp.exists_linearIndependent {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {p : ℝ≥0∞} (hp : p ≠ 0)
    (hE : ¬ FiniteDimensional 𝕜 E) : ∃ ξ : ℓ^p(ℕ, E), LinearIndependent 𝕜 fun n ↦ ξ n := by
  -- An infinite linearly independent sequence `v`, taken from a basis of `E`.
  let b := Module.Basis.ofVectorSpace 𝕜 E
  have : Infinite (Module.Basis.ofVectorSpaceIndex 𝕜 E) :=
    not_finite_iff_infinite.1 fun _ ↦ hE (.of_basis b)
  obtain ⟨v, hv⟩ : ∃ v : ℕ → E, LinearIndependent 𝕜 v :=
    ⟨_, b.linearIndependent.comp _ (Infinite.natEmbedding _).injective⟩
  -- Rescaled to norms below `2⁻ⁿ`, it lies in `ℓᵖ`.
  choose c hc0 hc using fun n ↦ NormedField.exists_norm_lt 𝕜
    (div_pos (pow_pos (by norm_num : (0 : ℝ) < 2⁻¹) n) (norm_pos_iff.2 (hv.ne_zero n)))
  have hmem : Memℓp (fun n ↦ c n • v n) p :=
    Memℓp.of_norm_le_geometric (C := 1) (r := 2⁻¹) (by norm_num) (by norm_num) (fun n ↦ by
      rw [norm_smul, one_mul]
      exact (le_div_iff₀ (norm_pos_iff.2 (hv.ne_zero n))).1 (hc n).le) hp
  exact ⟨⟨_, hmem⟩, hv.units_smul fun n ↦ Units.mk0 (c n) (norm_pos_iff.1 (hc0 n))⟩

namespace TauCeti

/-- **Geometric sequences in `ℓᵖ`.** For `p ≠ 0`, the geometric sequence `rⁱ` lies in `ℓᵖ`
exactly when `‖r‖ < 1`, or when `‖r‖ = 1` and `p = ∞`. -/
theorem memℓp_pow_iff {R : Type*} [NormedRing R] [NormOneClass R] [NormMulClass R] {r : R}
    (hp : p ≠ 0) : Memℓp (fun i : ℕ ↦ r ^ i) p ↔ ‖r‖ < 1 ∨ ‖r‖ = 1 ∧ p = ∞ := by
  refine ⟨fun hf ↦ ?_, ?_⟩
  · by_contra h
    push Not at h
    -- The terms do not decrease: `1 ≤ ‖rⁱ‖`.
    have hle (i : ℕ) : 1 ≤ ‖r ^ i‖ := (norm_pow r i).symm ▸ one_le_pow₀ h.1
    rcases eq_or_ne p ∞ with rfl | hptop
    · -- For `p = ∞`, `‖r‖ > 1` and the terms are unbounded.
      have hr : 1 < ‖r‖ := h.1.lt_of_ne fun h' ↦ h.2 h'.symm rfl
      obtain ⟨M, hM⟩ := hf.bddAbove
      have ht : Tendsto (fun i : ℕ ↦ ‖r ^ i‖) atTop atTop := by
        simp_rw [norm_pow]
        exact tendsto_pow_atTop_atTop_of_one_lt hr
      obtain ⟨i, hi⟩ := (ht.eventually_gt_atTop M).exists
      exact hi.not_ge (hM ⟨i, rfl⟩)
    · -- For `p < ∞`, the terms of a sequence in `ℓᵖ` tend to zero.
      have hpr : 0 < p.toReal := ENNReal.toReal_pos hp hptop
      obtain ⟨i, hi⟩ := ((hf.summable hpr).tendsto_atTop_zero.eventually
        (gt_mem_nhds zero_lt_one)).exists
      exact hi.not_ge (Real.one_le_rpow (hle i) hpr.le)
  · rintro (hr | ⟨hr, rfl⟩)
    · exact Memℓp.of_norm_le_geometric (C := 1) (norm_nonneg r) hr
        (fun i ↦ by rw [norm_pow, one_mul]) hp
    · exact memℓp_infty ⟨1, by rintro _ ⟨i, rfl⟩; simp [norm_pow, hr]⟩

/-- **Nonzero multiples of geometric sequences in `ℓᵖ`.** For `C ≠ 0` and `p ≠ 0`, the sequence
`C rⁱ` lies in `ℓᵖ` exactly when `‖r‖ < 1`, or when `‖r‖ = 1` and `p = ∞`. -/
theorem memℓp_const_mul_pow_iff {𝕜 : Type*} [NormedDivisionRing 𝕜] {C r : 𝕜} (hC : C ≠ 0)
    (hp : p ≠ 0) : Memℓp (fun i : ℕ ↦ C * r ^ i) p ↔ ‖r‖ < 1 ∨ ‖r‖ = 1 ∧ p = ∞ :=
  (hC.isUnit.memℓp_smul_iff (f := fun i : ℕ ↦ r ^ i)).trans (memℓp_pow_iff hp)

end TauCeti

end Geometric

namespace ContinuousLinearMap

section Coordinates

variable {𝕜 ι E : Type*} [DecidableEq ι] {q : ℝ≥0∞} [Fact (1 ≤ q)]

section NormedRing

variable [NormedRing 𝕜] [AddCommMonoid E] [Module 𝕜 E] [TopologicalSpace E]

/-- A continuous linear map on `ℓ^q` scales its value on a unit coordinate vector:
`T (z • eᵢ) = z • T eᵢ`. -/
theorem apply_lp_single (T : lp (fun _ : ι ↦ 𝕜) q →L[𝕜] E) (i : ι) (z : 𝕜) :
    T (lp.single q i z) = z • T (lp.single q i 1) := by
  rw [← T.map_smul, ← lp.single_smul, smul_eq_mul, mul_one]

/-- For `q < ∞`, every continuous linear map `T` on `ℓ^q` is given by its coordinate series:
`T x = ∑ i, xᵢ • T eᵢ`. -/
theorem hasSum_smul_lp_single (hq : q ≠ ∞) (T : lp (fun _ : ι ↦ 𝕜) q →L[𝕜] E)
    (x : lp (fun _ : ι ↦ 𝕜) q) :
    HasSum (fun i ↦ x i • T (lp.single q i 1)) (T x) := by
  convert (lp.hasSum_single hq x).map T T.continuous using 1
  ext i
  exact (T.apply_lp_single i (x i)).symm

/-- For `q < ∞`, two continuous linear maps on `ℓ^q` with values in a Hausdorff space are equal as
soon as they agree on every unit coordinate vector `eᵢ`. -/
theorem ext_lp_of_ne_top [T2Space E] (hq : q ≠ ∞) {T₁ T₂ : lp (fun _ : ι ↦ 𝕜) q →L[𝕜] E}
    (h : ∀ i, T₁ (lp.single q i 1) = T₂ (lp.single q i 1)) : T₁ = T₂ := by
  ext x
  refine (T₁.hasSum_smul_lp_single hq x).unique ?_
  simpa only [h] using T₂.hasSum_smul_lp_single hq x

end NormedRing

variable [NontriviallyNormedField 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The value of a continuous linear map on `ℓ^q` at a unit coordinate vector has norm at most
the norm of the map. -/
theorem norm_apply_lp_single_le (T : lp (fun _ : ι ↦ 𝕜) q →L[𝕜] E) (i : ι) :
    ‖T (lp.single q i 1)‖ ≤ ‖T‖ := by
  simpa [lp.norm_single (zero_lt_one.trans_le Fact.out)] using
    T.le_opNorm (lp.single q i (1 : 𝕜))

/-- The norms of the values of a continuous linear map on `ℓ^q` at the unit coordinate vectors
are bounded above (by the norm of the map). -/
theorem bddAbove_range_norm_apply_lp_single (T : lp (fun _ : ι ↦ 𝕜) q →L[𝕜] E) :
    BddAbove (Set.range fun i ↦ ‖T (lp.single q i 1)‖) :=
  ⟨‖T‖, Set.forall_mem_range.2 T.norm_apply_lp_single_le⟩

/-- A continuous linear map on ℓ¹ whose values on the unit coordinate vectors have norm at most
`C ≥ 0` has norm at most `C`. -/
theorem opNorm_lpOne_le (T : lp (fun _ : ι ↦ 𝕜) 1 →L[𝕜] E) {C : ℝ} (hC : 0 ≤ C)
    (hT : ∀ i, ‖T (lp.single 1 i 1)‖ ≤ C) : ‖T‖ ≤ C := by
  refine T.opNorm_le_bound hC fun x ↦ ?_
  -- Bound each term of `T x = ∑ i, xᵢ • T eᵢ` by `‖xᵢ‖ * C`; these sum to `‖x‖ * C`.
  rw [mul_comm]
  exact (T.hasSum_smul_lp_single ENNReal.one_ne_top x).norm_le_of_bounded
    ((lp.hasSum_norm_one x).mul_right _) fun i ↦
      (norm_smul_le _ _).trans (mul_le_mul_of_nonneg_left (hT i) (norm_nonneg _))

/-- The norm of a continuous linear map on ℓ¹ is the supremum of the norms of its values on the
unit coordinate vectors. For an empty index type both sides are `0`. -/
theorem norm_eq_ciSup_norm_lp_single (T : lp (fun _ : ι ↦ 𝕜) 1 →L[𝕜] E) :
    ‖T‖ = ⨆ i, ‖T (lp.single 1 i 1)‖ :=
  le_antisymm
    (T.opNorm_lpOne_le (Real.iSup_nonneg fun _ ↦ norm_nonneg _)
      fun i ↦ le_ciSup T.bddAbove_range_norm_apply_lp_single i)
    (Real.iSup_le T.norm_apply_lp_single_le (norm_nonneg T))

/-- The nonnegative norm of a continuous linear map on ℓ¹ is the supremum of the nonnegative norms
of its values on the unit coordinate vectors. -/
theorem nnnorm_eq_ciSup_nnnorm_lp_single (T : lp (fun _ : ι ↦ 𝕜) 1 →L[𝕜] E) :
    ‖T‖₊ = ⨆ i, ‖T (lp.single 1 i 1)‖₊ :=
  NNReal.eq <| by simpa only [coe_nnNorm, NNReal.coe_iSup] using T.norm_eq_ciSup_norm_lp_single

end Coordinates

end ContinuousLinearMap

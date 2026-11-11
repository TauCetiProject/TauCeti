/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.lpHolder
public import TauCeti.Analysis.Normed.Lp.Basic

/-!
# Direct sums of uniformly bounded operator families on `lp`

A family of bounded operators `T i : E i →L[𝕜] F i` with `‖T i‖ ≤ K` for every `i` acts
coordinatewise on `lp E p`, giving the direct sum `⊕ T i : lp E p →L[𝕜] lp F p`. Mathlib constructs
this operator as `lp.mapCLM p T hK hTK`, together with the bound `‖⊕ T i‖ ≤ K`. This file supplies
its characterizing API, at every exponent `1 ≤ p ≤ ∞` and over every nontrivially normed field:

* the direct sum is characterized by its coordinates: an operator `A` equals `⊕ T i` exactly when
  `evalCLM i ∘ A = T i ∘ evalCLM i` for every `i` (`lp.eq_mapCLM_iff`), and it sends the
  coordinate vector `single i x` to `single i (T i x)`;
* it depends only on the family, not on the chosen bound, and determines the family;
* it is additive, homogeneous and multiplicative in the family: identities give the identity, and
  composing coordinatewise composes the direct sums;
* its operator norm is exactly the supremum `⨆ i, ‖T i‖` (`lp.norm_mapCLM`).

Taking the same operator `T : X →L[𝕜] Y` in every coordinate gives its ampliation
`lp.ampliation ι p T = ⊕_{i : ι} T : ℓ^p(ι, X) →L[𝕜] ℓ^p(ι, Y)`, bundled as a bounded linear map
of `T`. It has the same norm as `T` for nonempty `ι`, so it is injective, and it is compatible
with composition. On `ℓ²(ℕ, H)` it is the device that defines the ultrastrong and ultraweak
operator topologies from the strong and weak ones.

On Hilbert spaces and `p = 2` the direct sum is moreover compatible with adjoints, so these laws
let representations of an algebra on the summands be assembled into one on the direct sum; the
adjoint law is in `TauCeti.Analysis.InnerProductSpace.HilbertSum`.

## Main results

* `lp.eq_mapCLM_iff`: the coordinatewise characterization of the direct sum.
* `lp.mapCLM_single`: the direct sum on coordinate vectors.
* `lp.mapCLM_inj`: the direct sum determines the family.
* `lp.mapCLM_add`, `lp.mapCLM_smul`, `lp.mapCLM_id`, `lp.mapCLM_comp`: the algebraic laws.
* `lp.norm_mapCLM`: `‖⊕ T i‖ = ⨆ i, ‖T i‖`.
* `lp.ampliation`, `lp.norm_ampliation`, `lp.ampliation_comp`: the ampliation of one operator.

## References

* J. B. Conway, *A Course in Functional Analysis*, 2nd ed., Springer GTM 96, 1990, §II.1.
-/

public section

open scoped ENNReal lp

namespace lp

variable {ι 𝕜 : Type*} {E F G : ι → Type*} [NontriviallyNormedField 𝕜]
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
  [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace 𝕜 (F i)]
  [∀ i, NormedAddCommGroup (G i)] [∀ i, NormedSpace 𝕜 (G i)]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **Coordinatewise characterization.** An operator equals the direct sum `⊕ T i` exactly when
its `i`-th coordinate is `T i` applied to the `i`-th coordinate, for every `i`. -/
theorem eq_mapCLM_iff (A : lp E p →L[𝕜] lp F p) (T : ∀ i, E i →L[𝕜] F i) {K : ℝ}
    (hK : 0 ≤ K) (hTK : ∀ i, ‖T i‖ ≤ K) :
    A = mapCLM p T hK hTK ↔ ∀ i, evalCLM 𝕜 F p i ∘L A = T i ∘L evalCLM 𝕜 E p i := by
  refine ⟨fun h i ↦ ?_, fun h ↦ ?_⟩
  · subst h
    ext x
    simp
  · ext x i
    simpa using congr($(h i) x)

/-- Coordinate evaluation intertwines the direct sum with its `i`-th summand. -/
@[simp]
theorem evalCLM_comp_mapCLM (T : ∀ i, E i →L[𝕜] F i) {K : ℝ} (hK : 0 ≤ K)
    (hTK : ∀ i, ‖T i‖ ≤ K) (i : ι) :
    evalCLM 𝕜 F p i ∘L mapCLM p T hK hTK = T i ∘L evalCLM 𝕜 E p i :=
  (eq_mapCLM_iff _ T hK hTK).1 rfl i

/-- The direct sum `⊕ T i` maps the `i`-th coordinate vector `single i x` to `single i (T i x)`. -/
@[simp]
theorem mapCLM_single [DecidableEq ι] (T : ∀ i, E i →L[𝕜] F i) {K : ℝ} (hK : 0 ≤ K)
    (hTK : ∀ i, ‖T i‖ ≤ K) (i : ι) (x : E i) :
    mapCLM p T hK hTK (lp.single p i x) = lp.single p i (T i x) := by
  ext j
  rcases eq_or_ne j i with rfl | h
  · simp
  · simp [Pi.single_eq_of_ne h]

/-- The direct sum does not depend on the chosen uniform bound. -/
theorem mapCLM_congr {T S : ∀ i, E i →L[𝕜] F i} (h : T = S) {K L : ℝ} (hK : 0 ≤ K)
    (hTK : ∀ i, ‖T i‖ ≤ K) (hL : 0 ≤ L) (hSL : ∀ i, ‖S i‖ ≤ L) :
    mapCLM p T hK hTK = mapCLM p S hL hSL := by
  subst h
  ext x i
  simp

/-- The direct sum determines the family of summands. -/
theorem mapCLM_inj {T S : ∀ i, E i →L[𝕜] F i} {K L : ℝ} (hK : 0 ≤ K)
    (hTK : ∀ i, ‖T i‖ ≤ K) (hL : 0 ≤ L) (hSL : ∀ i, ‖S i‖ ≤ L) :
    mapCLM p T hK hTK = mapCLM p S hL hSL ↔ T = S := by
  classical
  refine ⟨fun h ↦ funext fun i ↦ ?_, fun h ↦ mapCLM_congr h hK hTK hL hSL⟩
  ext x
  simpa using congr($h (lp.single p i x) i)

/-- The direct sum of zero operators is zero. -/
@[simp]
theorem mapCLM_zero {K : ℝ} (hK : 0 ≤ K) (h0K : ∀ i, ‖(0 : E i →L[𝕜] F i)‖ ≤ K) :
    mapCLM p (fun i ↦ (0 : E i →L[𝕜] F i)) hK h0K = 0 := by
  ext x i
  simp

/-- The direct sum is additive in the family of summands. -/
theorem mapCLM_add (T S : ∀ i, E i →L[𝕜] F i) {K L M : ℝ} (hK : 0 ≤ K)
    (hTK : ∀ i, ‖T i‖ ≤ K) (hL : 0 ≤ L) (hSL : ∀ i, ‖S i‖ ≤ L) (hM : 0 ≤ M)
    (hTSM : ∀ i, ‖T i + S i‖ ≤ M) :
    mapCLM p (fun i ↦ T i + S i) hM hTSM = mapCLM p T hK hTK + mapCLM p S hL hSL := by
  ext x i
  simp

/-- The direct sum commutes with negation of the family of summands. -/
theorem mapCLM_neg (T : ∀ i, E i →L[𝕜] F i) {K L : ℝ} (hK : 0 ≤ K)
    (hTK : ∀ i, ‖T i‖ ≤ K) (hL : 0 ≤ L) (hTL : ∀ i, ‖-T i‖ ≤ L) :
    mapCLM p (fun i ↦ -T i) hL hTL = -mapCLM p T hK hTK := by
  ext x i
  simp

/-- The direct sum is subtractive in the family of summands. -/
theorem mapCLM_sub (T S : ∀ i, E i →L[𝕜] F i) {K L M : ℝ} (hK : 0 ≤ K)
    (hTK : ∀ i, ‖T i‖ ≤ K) (hL : 0 ≤ L) (hSL : ∀ i, ‖S i‖ ≤ L) (hM : 0 ≤ M)
    (hTSM : ∀ i, ‖T i - S i‖ ≤ M) :
    mapCLM p (fun i ↦ T i - S i) hM hTSM = mapCLM p T hK hTK - mapCLM p S hL hSL := by
  ext x i
  simp

/-- The direct sum is homogeneous in the family of summands. -/
theorem mapCLM_smul (c : 𝕜) (T : ∀ i, E i →L[𝕜] F i) {K L : ℝ} (hK : 0 ≤ K)
    (hTK : ∀ i, ‖T i‖ ≤ K) (hL : 0 ≤ L) (hTL : ∀ i, ‖c • T i‖ ≤ L) :
    mapCLM p (fun i ↦ c • T i) hL hTL = c • mapCLM p T hK hTK := by
  ext x i
  simp

/-- The direct sum of identity operators is the identity. -/
@[simp]
theorem mapCLM_id {K : ℝ} (hK : 0 ≤ K) (hidK : ∀ i, ‖ContinuousLinearMap.id 𝕜 (E i)‖ ≤ K) :
    mapCLM p (fun i ↦ ContinuousLinearMap.id 𝕜 (E i)) hK hidK = ContinuousLinearMap.id 𝕜 _ := by
  ext x i
  simp

/-- Composing the summands composes the direct sums. -/
theorem mapCLM_comp (T : ∀ i, F i →L[𝕜] G i) (S : ∀ i, E i →L[𝕜] F i) {K L M : ℝ}
    (hK : 0 ≤ K) (hTK : ∀ i, ‖T i‖ ≤ K) (hL : 0 ≤ L) (hSL : ∀ i, ‖S i‖ ≤ L) (hM : 0 ≤ M)
    (hTSM : ∀ i, ‖T i ∘L S i‖ ≤ M) :
    mapCLM p (fun i ↦ T i ∘L S i) hM hTSM = mapCLM p T hK hTK ∘L mapCLM p S hL hSL := by
  ext x i
  simp

/-- Each summand is bounded by the direct sum: `‖T i‖ ≤ ‖⊕ T j‖`. -/
theorem norm_le_norm_mapCLM (T : ∀ i, E i →L[𝕜] F i) {K : ℝ} (hK : 0 ≤ K)
    (hTK : ∀ i, ‖T i‖ ≤ K) (i : ι) :
    ‖T i‖ ≤ ‖mapCLM p T hK hTK‖ := by
  classical
  have hp : 0 < p := zero_lt_one.trans_le Fact.out
  refine (T i).opNorm_le_bound (norm_nonneg _) fun x ↦ ?_
  simpa [lp.norm_single hp] using (mapCLM p T hK hTK).le_opNorm (lp.single p i x)

/-- **Norm of a direct sum.** The operator norm of `⊕ T i` is the supremum of the operator norms
of its summands, `0` for an empty family. -/
theorem norm_mapCLM (T : ∀ i, E i →L[𝕜] F i) {K : ℝ} (hK : 0 ≤ K) (hTK : ∀ i, ‖T i‖ ≤ K) :
    ‖mapCLM p T hK hTK‖ = ⨆ i, ‖T i‖ := by
  have hbdd : BddAbove (Set.range fun i ↦ ‖T i‖) := ⟨K, by simpa [upperBounds] using hTK⟩
  refine le_antisymm ?_ (Real.iSup_le (norm_le_norm_mapCLM T hK hTK) (norm_nonneg _))
  rw [mapCLM_congr rfl hK hTK (Real.iSup_nonneg fun i ↦ norm_nonneg (T i))
    fun i ↦ le_ciSup hbdd i]
  exact norm_mapCLM_le _ _ _ _

section Ampliation

variable (ι p) {X Y Z : Type*}
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
  [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]

/-- The **ampliation** `T ↦ ⊕_{i : ι} T` of an operator to `ℓ^p(ι, X) →L[𝕜] ℓ^p(ι, Y)`, acting by
`T` in every coordinate, as a bounded linear map of `T`. -/
noncomputable def ampliation : (X →L[𝕜] Y) →L[𝕜] (ℓ^p(ι, X) →L[𝕜] ℓ^p(ι, Y)) :=
  LinearMap.mkContinuous
    { toFun T := mapCLM p (fun _ ↦ T) (norm_nonneg T) fun _ ↦ le_rfl
      map_add' T S := by ext x i; simp
      map_smul' c T := by ext x i; simp }
    1 fun T ↦ by simpa using norm_mapCLM_le p (fun _ : ι ↦ T) (norm_nonneg T) fun _ ↦ le_rfl

variable {ι p}

theorem ampliation_eq_mapCLM (T : X →L[𝕜] Y) :
    ampliation ι p T = mapCLM p (fun _ ↦ T) (norm_nonneg T) fun _ ↦ le_rfl :=
  (rfl)

@[simp]
theorem ampliation_apply_apply (T : X →L[𝕜] Y) (x : ℓ^p(ι, X)) (i : ι) :
    ampliation ι p T x i = T (x i) := by
  simp [ampliation_eq_mapCLM]

/-- The ampliation maps the coordinate vector `single i x` to `single i (T x)`. -/
@[simp]
theorem ampliation_single [DecidableEq ι] (T : X →L[𝕜] Y) (i : ι) (x : X) :
    ampliation ι p T (lp.single p i x) = lp.single p i (T x) := by
  simp [ampliation_eq_mapCLM]

theorem norm_ampliation_le (T : X →L[𝕜] Y) : ‖ampliation ι p T‖ ≤ ‖T‖ :=
  norm_mapCLM_le p _ (norm_nonneg T) fun _ ↦ le_rfl

/-- Over a nonempty index type the ampliation preserves the operator norm. -/
@[simp]
theorem norm_ampliation [Nonempty ι] (T : X →L[𝕜] Y) : ‖ampliation ι p T‖ = ‖T‖ := by
  rw [ampliation_eq_mapCLM, norm_mapCLM, ciSup_const]

theorem ampliation_injective [Nonempty ι] :
    Function.Injective (ampliation ι p : (X →L[𝕜] Y) → ℓ^p(ι, X) →L[𝕜] ℓ^p(ι, Y)) := by
  classical
  intro T S h
  obtain ⟨i⟩ := ‹Nonempty ι›
  ext x
  simpa using congr($h (lp.single p i x) i)

@[simp]
theorem ampliation_id :
    ampliation ι p (ContinuousLinearMap.id 𝕜 X) = ContinuousLinearMap.id 𝕜 ℓ^p(ι, X) := by
  ext x i
  simp

@[simp]
theorem ampliation_comp (T : Y →L[𝕜] Z) (S : X →L[𝕜] Y) :
    ampliation ι p (T ∘L S) = ampliation ι p T ∘L ampliation ι p S := by
  ext x i
  simp

@[simp]
theorem ampliation_one : ampliation ι p (1 : X →L[𝕜] X) = 1 :=
  ampliation_id

@[simp]
theorem ampliation_mul (T S : X →L[𝕜] X) :
    ampliation ι p (T * S) = ampliation ι p T * ampliation ι p S :=
  ampliation_comp T S

end Ampliation

end lp

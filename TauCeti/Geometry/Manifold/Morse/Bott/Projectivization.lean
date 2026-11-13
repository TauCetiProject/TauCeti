/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Bott.Family
public import TauCeti.Geometry.Manifold.Morse.Projectivization
public import TauCeti.Geometry.Manifold.Projectivization.Map
import TauCeti.Geometry.Manifold.IsManifold.Basic

/-!
# Moment functions on projective space are Morse–Bott

On the projective space `ℙ 𝕜 (Fin (n + 1) → 𝕜)` over `𝕜 = ℝ` or `ℂ`, the moment function with
weights `w : Fin (n + 1) → ℝ` (`TauCeti.projectiveMomentFunction`) sends the line through `v` to
`(∑ i, w i * ‖v i‖ ^ 2) / ∑ i, ‖v i‖ ^ 2`. It is a Morse function exactly when the weights are
pairwise distinct (`TauCeti.isMorse_projectiveMomentFunction_iff`). This file shows that for
arbitrary weights it is a Morse–Bott function, for the underlying real smooth structure.

Its critical points with value `c` are the lines in the weight space
`V_c = {v | v i = 0 whenever w i ≠ c}`
(`TauCeti.mk_mem_criticalPoints_projectiveMomentFunction_and_eq_iff`). If `c` is the weight of
`m + 1` coordinates, an injective linear map `𝕜ᵐ⁺¹ → V_c` is onto `V_c`, so the linear embedding
`ℙᵐ → ℙⁿ` it induces (`Projectivization.isSmoothEmbedding_map`) is onto these critical points
(`TauCeti.range_map_eq_criticalPoints_inter_preimage_projectiveMomentFunction`). This embedding is
a nondegenerate critical submanifold
(`TauCeti.isNondegenerateCriticalSubmanifold_projectiveMomentFunction`): its tangent space lies in
the kernel of the critical Hessian, and that kernel has the real dimension of `ℙᵐ`
(`TauCeti.finrank_ker_criticalHessian_projectiveMomentFunction`), so the two agree. Taking one
projective subspace for each value of the weights gives a Morse–Bott family
(`TauCeti.exists_isMorseBottFamily_projectiveMomentFunction`). The Morse index along the critical
set of value `c` is the real dimension of `𝕜` times the number of weights below `c`
(`TauCeti.manifoldMorseIndex_projectiveMomentFunction_of_mem_criticalPoints`).

For example, on `ℝℙ²` with the weights `1, 1, 0` the critical set is the point `[e₂]`, a minimum,
and the projective line `{v₂ = 0}`, a circle of maxima of index `1`.

## Main results

* `TauCeti.range_map_eq_criticalPoints_inter_preimage_projectiveMomentFunction`: the projective
  subspace of the weight space of `c` is the set of critical points of value `c`.
* `TauCeti.isNondegenerateCriticalSubmanifold_projectiveMomentFunction`: the projective subspace
  of a weight space is a Morse–Bott critical submanifold.
* `TauCeti.exists_isMorseBottFamily_projectiveMomentFunction`: **the moment function is
  Morse–Bott**, with one projective subspace for each value of the weights.

## References

* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
* T. Frankel, *Fixed points and torsion on Kähler manifolds*, Annals of Mathematics 70 (1959),
  1–8, for moment functions of circle actions.
-/

public section

open Function Module Set
open scoped ContDiff Manifold LinearAlgebra.Projectivization

noncomputable section

namespace TauCeti

open Projectivization

variable {𝕜 : Type*} [RCLike 𝕜] {n m : ℕ} {w : Fin (n + 1) → ℝ} {c : ℝ}

/-- **The projective subspace of a weight space is a critical set.** Let `L` be an injective linear
map from `𝕜ᵐ⁺¹` into the weight space of `c`, the vectors whose coordinates of weight `w i ≠ c`
vanish, and suppose that exactly `m + 1` coordinates have weight `c`. Then the induced map
`ℙᵐ → ℙⁿ` is onto the critical points of the moment function of value `c`. -/
theorem range_map_eq_criticalPoints_inter_preimage_projectiveMomentFunction
    (L : (Fin (m + 1) → 𝕜) →ₗ[𝕜] Fin (n + 1) → 𝕜) (hL : Injective L)
    (hLw : ∀ u i, w i ≠ c → L u i = 0) (hm : {i | w i = c}.ncard = m + 1) :
    range (map L hL) = criticalPoints 𝓘(ℝ, Fin n → 𝕜) (projectiveMomentFunction 𝕜 w) ∩
      projectiveMomentFunction 𝕜 w ⁻¹' {c} := by
  -- The weight space `V` of `c` has dimension `m + 1`, so `L` is onto it.
  set V := LinearMap.ker (LinearMap.funLeft 𝕜 𝕜 (Subtype.val : {i // w i ≠ c} → Fin (n + 1)))
  have hV : finrank 𝕜 V ≤ m + 1 := by
    let ρ := LinearMap.funLeft 𝕜 𝕜 (Subtype.val : {i // w i = c} → Fin (n + 1)) ∘ₗ V.subtype
    have hρ : Injective ρ := fun v v' h ↦ Subtype.ext (funext fun i ↦ by
      by_cases hi : w i = c
      · exact congrFun h ⟨i, hi⟩
      · exact (congrFun (LinearMap.mem_ker.1 v.2) ⟨i, hi⟩).trans
          (congrFun (LinearMap.mem_ker.1 v'.2) ⟨i, hi⟩).symm)
    refine (LinearMap.finrank_le_finrank_of_injective hρ).trans_eq ?_
    rw [Module.finrank_fintype_fun_eq_card, ← Nat.card_eq_fintype_card, ← hm]
    exact Nat.card_coe_set_eq {i | w i = c}
  have hrange : LinearMap.range L = V := by
    refine Submodule.eq_of_le_of_finrank_le ?_ ?_
    · rintro _ ⟨u, rfl⟩
      exact funext fun i ↦ hLw u i i.2
    · rw [LinearMap.finrank_range_of_inj hL, Module.finrank_fin_fun]
      exact hV
  ext x
  induction x using ind with | h v hv =>
  rw [mem_inter_iff, mem_preimage, mem_singleton_iff,
    mk_mem_criticalPoints_projectiveMomentFunction_and_eq_iff]
  constructor
  · rintro ⟨s, hs⟩
    induction s using ind with | h u hu =>
    rw [map_mk, mk_eq_mk_iff] at hs
    obtain ⟨a, ha⟩ := hs
    intro i hi
    have hai := congrFun ha i
    rw [Pi.smul_apply, hLw u i hi, Units.smul_def, smul_eq_mul, mul_eq_zero] at hai
    exact hai.resolve_left a.ne_zero
  · intro h
    obtain ⟨u, rfl⟩ : v ∈ LinearMap.range L := hrange ▸ funext fun i ↦ h i i.2
    exact ⟨mk 𝕜 u fun hu ↦ hv (by rw [hu, map_zero]), map_mk _ _ _ _⟩

/-- **Projective subspaces of weight spaces are Morse–Bott critical submanifolds.** Let `L` be an
injective linear map from `𝕜ᵐ⁺¹` into the weight space of `c`, the vectors whose coordinates of
weight `w i ≠ c` vanish, and suppose that exactly `m + 1` coordinates have weight `c`. Then the
induced embedding `ℙᵐ → ℙⁿ` is a nondegenerate critical submanifold of the moment function. -/
theorem isNondegenerateCriticalSubmanifold_projectiveMomentFunction
    (L : (Fin (m + 1) → 𝕜) →ₗ[𝕜] Fin (n + 1) → 𝕜) (hL : Injective L)
    (hLw : ∀ u i, w i ≠ c → L u i = 0) (hm : {i | w i = c}.ncard = m + 1) {r : ℕ∞ω}
    (hr : 1 ≤ r) :
    (SmoothEmbedding.ofIsSmoothEmbedding (map L hL)
      (isSmoothEmbedding_map (𝕜' := ℝ) L hL hr)).IsNondegenerateCriticalSubmanifold
      (projectiveMomentFunction 𝕜 w) := by
  set i := SmoothEmbedding.ofIsSmoothEmbedding (map L hL) (isSmoothEmbedding_map (𝕜' := ℝ) L hL hr)
  have hr0 : r ≠ 0 := by
    rintro rfl
    simp at hr
  have hcrit (s : ℙ 𝕜 (Fin (m + 1) → 𝕜)) :
      i s ∈ criticalPoints 𝓘(ℝ, Fin n → 𝕜) (projectiveMomentFunction 𝕜 w) ∧
        projectiveMomentFunction 𝕜 w (i s) = c := by
    have hs : map L hL s ∈ range (map L hL) := mem_range_self s
    rw [range_map_eq_criticalPoints_inter_preimage_projectiveMomentFunction L hL hLw hm] at hs
    rwa [show i s = map L hL s from SmoothEmbedding.ofIsSmoothEmbedding_apply _ _ s]
  have hcs : i.IsCriticalSubmanifold (projectiveMomentFunction 𝕜 w) :=
    ⟨fun _ ↦ (contMDiff_projectiveMomentFunction w).contMDiffAt, fun s ↦ (hcrit s).1⟩
  refine ⟨hcs, fun s ↦ ?_⟩
  -- The tangent space lies in the kernel and has at least its dimension, so the two agree.
  refine (Submodule.eq_of_le_of_finrank_le (hcs.tangentRange_le_ker_criticalHessian hr0 s)
    ?_).ge
  rw [SmoothEmbedding.tangentRange,
    LinearMap.finrank_range_of_inj ((i.isImmersion.isImmersionAt s).mfderiv_injective hr0),
    finrank_ker_criticalHessian_projectiveMomentFunction (hcrit s).1, (hcrit s).2, hm,
    Nat.add_sub_cancel, finrank_tangentSpace, Module.finrank_pi_fintype, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_comm]

/-! ### The projective subspaces of the weight spaces -/

/-- The number `m` such that exactly `m + 1` coordinates carry the weight `c`, for a value `c` of
the weights. -/
private def weightDim (w : Fin (n + 1) → ℝ) (c : ℝ) : ℕ :=
  {i | w i = c}.ncard - 1

private theorem ncard_eq_weightDim_add_one (hc : c ∈ range w) :
    {i | w i = c}.ncard = weightDim w c + 1 := by
  obtain ⟨k, rfl⟩ := hc
  exact (Nat.sub_add_cancel ((ncard_pos (toFinite _)).2 ⟨k, rfl⟩)).symm

/-- An enumeration of the coordinates of weight `c`. -/
private def weightEquiv (hc : c ∈ range w) : Fin (weightDim w c + 1) ≃ {i // w i = c} :=
  (Fintype.equivFinOfCardEq (by
    rw [← Nat.card_eq_fintype_card]
    exact ncard_eq_weightDim_add_one hc)).symm

/-- The linear isomorphism of `𝕜ᵐ⁺¹` onto the weight space of `c` given by the enumeration of the
coordinates of weight `c`, extending by zero. -/
private def weightIncl (𝕜 : Type*) [RCLike 𝕜] (hc : c ∈ range w) :
    (Fin (weightDim w c + 1) → 𝕜) →ₗ[𝕜] Fin (n + 1) → 𝕜 :=
  ExtendByZero.linearMap 𝕜 𝕜 (Subtype.val ∘ weightEquiv hc)

private theorem injective_weightIncl (hc : c ∈ range w) : Injective (weightIncl 𝕜 hc) :=
  extend_injective (Subtype.val_injective.comp (weightEquiv hc).injective) 0

private theorem weightIncl_apply_of_ne (hc : c ∈ range w) (u : Fin (weightDim w c + 1) → 𝕜)
    {i : Fin (n + 1)} (hi : w i ≠ c) : weightIncl 𝕜 hc u i = 0 :=
  extend_apply' _ _ _ fun ⟨a, ha⟩ ↦ hi (ha ▸ (weightEquiv hc a).2)

/-- The projective subspace of the weight space of `c`, as a smooth embedding of `ℙᵐ`. -/
private def weightEmbedding (𝕜 : Type*) [RCLike 𝕜] (hc : c ∈ range w) {r : ℕ∞ω} (hr : 1 ≤ r) :
    SmoothEmbedding 𝓘(ℝ, Fin (weightDim w c) → 𝕜) 𝓘(ℝ, Fin n → 𝕜) r
      (ℙ 𝕜 (Fin (weightDim w c + 1) → 𝕜)) (ℙ 𝕜 (Fin (n + 1) → 𝕜)) :=
  .ofIsSmoothEmbedding _ (isSmoothEmbedding_map (𝕜' := ℝ) _ (injective_weightIncl hc) hr)

private theorem isNondegenerateCriticalSubmanifold_weightEmbedding (hc : c ∈ range w) {r : ℕ∞ω}
    (hr : 1 ≤ r) :
    (weightEmbedding 𝕜 hc hr).IsNondegenerateCriticalSubmanifold
      (projectiveMomentFunction 𝕜 w) :=
  isNondegenerateCriticalSubmanifold_projectiveMomentFunction _ _ (fun u _ ↦
    weightIncl_apply_of_ne hc u) (ncard_eq_weightDim_add_one hc) hr

/-- The image of the projective subspace of the weight space of `c` is the set of critical points
of value `c`. -/
private theorem range_weightEmbedding (hc : c ∈ range w) {r : ℕ∞ω} (hr : 1 ≤ r) :
    range (weightEmbedding 𝕜 hc hr) =
      criticalPoints 𝓘(ℝ, Fin n → 𝕜) (projectiveMomentFunction 𝕜 w) ∩
        projectiveMomentFunction 𝕜 w ⁻¹' {c} := by
  rw [weightEmbedding, SmoothEmbedding.coe_ofIsSmoothEmbedding]
  exact range_map_eq_criticalPoints_inter_preimage_projectiveMomentFunction _ _
    (fun u _ ↦ weightIncl_apply_of_ne hc u) (ncard_eq_weightDim_add_one hc)

/-- **The moment function is Morse–Bott.** For arbitrary weights `w`, the moment function on
`ℙ 𝕜 (Fin (n + 1) → 𝕜)` is a Morse–Bott function for the underlying real smooth structure. Its
critical components are indexed by the values `c` of the weights: if `m c + 1` coordinates carry
the weight `c`, the component of value `c` is a projective space `ℙ 𝕜 (Fin (m c + 1) → 𝕜)`,
embedded onto the critical points of value `c` by the map induced by an injective linear map
`L c` into the weight space of `c`. -/
theorem exists_isMorseBottFamily_projectiveMomentFunction (𝕜 : Type*) [RCLike 𝕜]
    (w : Fin (n + 1) → ℝ) {r : ℕ∞ω} (hr : 1 ≤ r) :
    ∃ (m : range w → ℕ) (L : ∀ c : range w, (Fin (m c + 1) → 𝕜) →ₗ[𝕜] Fin (n + 1) → 𝕜)
      (hL : ∀ c, Injective (L c)) (i : ∀ c : range w, SmoothEmbedding 𝓘(ℝ, Fin (m c) → 𝕜)
        𝓘(ℝ, Fin n → 𝕜) r (ℙ 𝕜 (Fin (m c + 1) → 𝕜)) (ℙ 𝕜 (Fin (n + 1) → 𝕜))),
      (∀ c : range w, {i | w i = c}.ncard = m c + 1) ∧
      (∀ (c : range w) u j, w j ≠ c → L c u j = 0) ∧
      (∀ c, ⇑(i c) = map (L c) (hL c)) ∧
      (∀ c : range w, range (i c) =
        criticalPoints 𝓘(ℝ, Fin n → 𝕜) (projectiveMomentFunction 𝕜 w) ∩
          projectiveMomentFunction 𝕜 w ⁻¹' {(c : ℝ)}) ∧
      IsMorseBottFamily i (projectiveMomentFunction 𝕜 w) := by
  refine ⟨fun c ↦ weightDim w c, fun c ↦ weightIncl 𝕜 c.2, fun c ↦ injective_weightIncl c.2,
    fun c ↦ weightEmbedding 𝕜 c.2 hr, fun c ↦ ncard_eq_weightDim_add_one c.2,
    fun c u _ ↦ weightIncl_apply_of_ne c.2 u, fun _ ↦ SmoothEmbedding.coe_ofIsSmoothEmbedding _ _,
    fun c ↦ range_weightEmbedding c.2 hr,
    ?_⟩
  -- Build the family for `C²` embeddings; it has the same underlying maps.
  have h2 : (1 : ℕ∞ω) ≤ 2 := by norm_num
  have hfam := IsMorseBottFamily.of_pairwise_disjoint le_rfl (contMDiff_projectiveMomentFunction w)
    (fun c : range w ↦ isNondegenerateCriticalSubmanifold_weightEmbedding (𝕜 := 𝕜) c.2 h2) ?_ ?_
  · -- Apart from nondegeneracy, the conditions only involve the underlying maps, which do not
    -- depend on the order of smoothness.
    have hcoe (c : range w) : ⇑(weightEmbedding 𝕜 c.2 hr) = weightEmbedding 𝕜 c.2 h2 := by
      simp only [weightEmbedding, SmoothEmbedding.coe_ofIsSmoothEmbedding]
    refine ⟨hfam.contMDiff, fun c ↦ isNondegenerateCriticalSubmanifold_weightEmbedding c.2 hr,
      hfam.nonempty, hfam.boundarylessManifold, fun c s ↦ ?_, ?_, ?_, ?_⟩
    · rw [hcoe]
      exact hfam.range_eq_connectedComponentIn c s
    · simpa only [hcoe] using hfam.range_injective
    · simpa only [hcoe] using hfam.criticalPoints_subset_iUnion_range
    · simpa only [hcoe] using hfam.locallyFinite_range
  · intro c c' hcc'
    rw [Function.onFun, range_weightEmbedding, range_weightEmbedding]
    exact Disjoint.inter_left' _ (Disjoint.inter_right' _
      (Disjoint.preimage _ (disjoint_singleton.2 fun h ↦ hcc' (Subtype.ext h))))
  · intro x hx
    refine mem_iUnion.2 ⟨⟨_, projectiveMomentFunction_mem_range_of_mem_criticalPoints hx⟩, ?_⟩
    rw [range_weightEmbedding]
    exact ⟨hx, rfl⟩

end TauCeti

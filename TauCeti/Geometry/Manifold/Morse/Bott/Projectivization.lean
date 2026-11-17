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
(`TauCeti.isMorseBottFamily_projectiveMomentFunction`,
`TauCeti.exists_isMorseBottFamily_projectiveMomentFunction`). The Morse index along the critical
set of value `c` is the real dimension of `𝕜` times the number of weights below `c`
(`TauCeti.manifoldMorseIndex_projectiveMomentFunction_of_mem_criticalPoints`).

For example, on `ℝℙ²` with the weights `1, 1, 0` the critical set is the point `[e₂]`, a minimum,
and the projective line `{v₂ = 0}`, a circle of maxima of index `1`.

## Main results

* `TauCeti.isNondegenerateCriticalSubmanifold_projectiveMomentFunction`: the projective subspace
  of a weight space is a Morse–Bott critical submanifold.
* `TauCeti.isMorseBottFamily_projectiveMomentFunction`: the projective subspaces of the weight
  spaces, given by explicit injective linear maps, form a Morse–Bott family.
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
    with hi
  have hr0 : r ≠ 0 := by
    rintro rfl
    simp at hr
  have hcrit (s : ℙ 𝕜 (Fin (m + 1) → 𝕜)) :
      i s ∈ criticalPoints 𝓘(ℝ, Fin n → 𝕜) (projectiveMomentFunction 𝕜 w) ∧
        projectiveMomentFunction 𝕜 w (i s) = c := by
    have hs : map L hL s ∈ range (map L hL) := mem_range_self s
    rw [range_map_eq_criticalPoints_inter_preimage_projectiveMomentFunction L hL hLw hm] at hs
    rwa [hi, SmoothEmbedding.ofIsSmoothEmbedding_apply]
  have hcs : i.IsCriticalSubmanifold (projectiveMomentFunction 𝕜 w) :=
    ⟨fun _ ↦ (contMDiff_projectiveMomentFunction w).contMDiffAt, fun s ↦ (hcrit s).1⟩
  refine ⟨hcs, fun s ↦ ?_⟩
  -- The tangent space lies in the kernel and has at least its dimension, so the two agree.
  refine (Submodule.eq_of_le_of_finrank_le (hcs.tangentRange_le_ker_criticalHessian hr0 s)
    ?_).ge
  rw [SmoothEmbedding.tangentRange,
    LinearMap.finrank_range_of_inj ((i.isImmersion.isImmersionAt s).mfderiv_injective hr0),
    finrank_ker_criticalHessian_projectiveMomentFunction (hcrit s).1, (hcrit s).2, hm,
    finrank_tangentSpace]
  simp [Module.finrank_pi_fintype, mul_comm]

/-- **The moment function is Morse–Bott, for an explicit family.** Let `c : ι → ℝ` list the
values of the weights without repetition. For each `a`, let `m a + 1` be the number of coordinates
of weight `c a` and `L a` an injective linear map from `𝕜ᵐ⁺¹` into the weight space of `c a`. Then
smooth embeddings `i a` whose underlying maps are the induced maps `ℙᵐ → ℙⁿ` form a Morse–Bott
family for the moment function. -/
theorem isMorseBottFamily_projectiveMomentFunction {ι : Type*} {c : ι → ℝ} (hc : Injective c)
    (hwc : range w ⊆ range c) {m : ι → ℕ}
    (L : ∀ a, (Fin (m a + 1) → 𝕜) →ₗ[𝕜] Fin (n + 1) → 𝕜) (hL : ∀ a, Injective (L a))
    (hLw : ∀ a u j, w j ≠ c a → L a u j = 0) (hm : ∀ a, {j | w j = c a}.ncard = m a + 1)
    {r : ℕ∞ω} {i : ∀ a, SmoothEmbedding 𝓘(ℝ, Fin (m a) → 𝕜) 𝓘(ℝ, Fin n → 𝕜) r
      (ℙ 𝕜 (Fin (m a + 1) → 𝕜)) (ℙ 𝕜 (Fin (n + 1) → 𝕜))}
    (hi : ∀ a, ⇑(i a) = map (L a) (hL a)) :
    IsMorseBottFamily i (projectiveMomentFunction 𝕜 w) := by
  have hrange (a : ι) : range (map (L a) (hL a)) =
      criticalPoints 𝓘(ℝ, Fin n → 𝕜) (projectiveMomentFunction 𝕜 w) ∩
        projectiveMomentFunction 𝕜 w ⁻¹' {c a} :=
    range_map_eq_criticalPoints_inter_preimage_projectiveMomentFunction _ _ (hLw a) (hm a)
  -- Build the family for `C²` embeddings with the same underlying maps.
  have h2 : (1 : ℕ∞ω) ≤ 2 := by norm_num
  refine IsMorseBottFamily.congr (i := fun a ↦ SmoothEmbedding.ofIsSmoothEmbedding _
    (isSmoothEmbedding_map (𝕜' := ℝ) _ (hL a) h2)) ?_ fun a ↦ by
      rw [hi, SmoothEmbedding.coe_ofIsSmoothEmbedding]
  refine IsMorseBottFamily.of_pairwise_disjoint le_rfl (contMDiff_projectiveMomentFunction w)
    (fun a ↦ isNondegenerateCriticalSubmanifold_projectiveMomentFunction _ _ (hLw a) (hm a) h2)
    (fun a b hab ↦ ?_) fun x hx ↦ ?_
  · rw [onFun, SmoothEmbedding.coe_ofIsSmoothEmbedding, SmoothEmbedding.coe_ofIsSmoothEmbedding,
      hrange, hrange]
    exact Disjoint.inter_left' _ (Disjoint.inter_right' _
      (Disjoint.preimage _ (disjoint_singleton.2 (hc.ne hab))))
  · -- A critical value is a weight, hence one of the values `c a`.
    obtain ⟨a, ha⟩ := hwc (projectiveMomentFunction_mem_range_of_mem_criticalPoints hx)
    refine mem_iUnion.2 ⟨a, ?_⟩
    rw [SmoothEmbedding.coe_ofIsSmoothEmbedding, hrange]
    exact ⟨hx, ha.symm⟩

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
    rw [← Nat.card_eq_fintype_card, ← ncard_ofPred]
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
    isMorseBottFamily_projectiveMomentFunction Subtype.val_injective (fun x hx ↦ ⟨⟨x, hx⟩, rfl⟩)
      _ _ (fun c u _ ↦ weightIncl_apply_of_ne c.2 u) (fun c ↦ ncard_eq_weightDim_add_one c.2)
      fun _ ↦ SmoothEmbedding.coe_ofIsSmoothEmbedding _ _⟩

end TauCeti

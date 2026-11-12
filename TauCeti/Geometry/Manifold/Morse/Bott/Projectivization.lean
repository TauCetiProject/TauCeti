/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Bott.Family
public import TauCeti.Geometry.Manifold.Morse.Projectivization
public import TauCeti.Geometry.Manifold.Projectivization.Map
import TauCeti.Geometry.Manifold.Morse.Bott.Index

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
`m + 1` coordinates, these lines form the image of a linear embedding `ℙᵐ → ℙⁿ` induced by an
injective linear map onto `V_c` (`Projectivization.isSmoothEmbedding_map`), and this embedding is
a nondegenerate critical submanifold
(`TauCeti.isNondegenerateCriticalSubmanifold_projectiveMomentFunction`). Indeed, in the affine
chart at a coordinate `k` of weight `c`, the moment function is the chart model
`(c + ∑ j, ν j * ‖z j‖ ^ 2) / (1 + ∑ j, ‖z j‖ ^ 2)`, `ν = w ∘ k.succAbove`, whose Hessian at a
critical point `z` is a positive multiple of `(v, v') ↦ ∑ j, (ν j - c) * ⟪v j, v' j⟫`
(`TauCeti.ProjectiveMomentChart.one_add_sum_mul_fderiv_fderiv_model_apply`). Its kernel consists of
the vectors supported on the `m` coordinates `j` with `ν j = c`, so it has the real dimension of
`ℙᵐ`, and it contains the tangent space of the embedded `ℙᵐ`; so the two agree.

The Morse index along the critical set of value `c` is the real dimension of `𝕜` times the number
of weights below `c` (`TauCeti.manifoldMorseIndex_projectiveMomentFunction_of_mem_criticalPoints`),
since it is locally constant along a Morse–Bott critical submanifold and the coordinate points
`[eₖ]` have this index. Taking one projective subspace for each value of the weights gives a
Morse–Bott family (`TauCeti.exists_isMorseBottFamily_projectiveMomentFunction`).

For example, on `ℝℙ²` with the weights `1, 1, 0` the critical set is the point `[e₂]`, a minimum,
and the projective line `{v₂ = 0}`, a circle of maxima of index `1`.

## Main results

* `TauCeti.mk_mem_criticalPoints_projectiveMomentFunction_and_eq_iff`: the critical points of
  value `c` are the lines in the weight space of `c`.
* `TauCeti.isNondegenerateCriticalSubmanifold_projectiveMomentFunction`: the projective subspace
  of a weight space is a Morse–Bott critical submanifold.
* `TauCeti.manifoldMorseIndex_projectiveMomentFunction_of_mem_criticalPoints`: the Morse index at a
  critical point of value `c` is `dim_ℝ 𝕜 * #{i | w i < c}`.
* `TauCeti.exists_isMorseBottFamily_projectiveMomentFunction`: **the moment function is
  Morse–Bott**, with one projective subspace for each value of the weights.

## References

* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
* T. Frankel, *Fixed points and torsion on Kähler manifolds*, Annals of Mathematics 70 (1959),
  1–8, for moment functions of circle actions.
-/

public section

open Function Module Set
open scoped ContDiff Manifold LinearAlgebra.Projectivization RealInnerProductSpace

noncomputable section

namespace TauCeti

open Projectivization ProjectiveMomentChart

variable {𝕜 : Type*} [RCLike 𝕜] {n m : ℕ} {w : Fin (n + 1) → ℝ} {c : ℝ}

/-- **The critical points of a given value.** The line through `v` is a critical point of the
moment function with value `c` exactly when `v` lies in the weight space of `c`: its coordinates
`v i` of weight `w i ≠ c` vanish. -/
theorem mk_mem_criticalPoints_projectiveMomentFunction_and_eq_iff {v : Fin (n + 1) → 𝕜}
    (hv : v ≠ 0) :
    mk 𝕜 v hv ∈ criticalPoints 𝓘(ℝ, Fin n → 𝕜) (projectiveMomentFunction 𝕜 w) ∧
        projectiveMomentFunction 𝕜 w (mk 𝕜 v hv) = c ↔
      ∀ i, w i ≠ c → v i = 0 := by
  rw [mk_mem_criticalPoints_projectiveMomentFunction_iff hv]
  refine ⟨fun ⟨h, hc⟩ i hi ↦ (h i).resolve_right (hc ▸ hi), fun h ↦ ?_⟩
  -- Every nonzero coordinate carries the weight `c`, so the value at `[v]` is `c`.
  have hval : projectiveMomentFunction 𝕜 w (mk 𝕜 v hv) = c := by
    obtain ⟨k, hk⟩ := Function.ne_iff.1 hv
    have hpos : 0 < ∑ i, ‖v i‖ ^ 2 :=
      (pow_pos (norm_pos_iff.2 hk) 2).trans_le
        (Finset.single_le_sum (f := fun i ↦ ‖v i‖ ^ 2) (fun i _ ↦ by positivity)
          (Finset.mem_univ k))
    rw [projectiveMomentFunction_mk, div_eq_iff hpos.ne', Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    by_cases hi : w i = c
    · rw [hi]
    · simp [h i hi]
  refine ⟨fun i ↦ ?_, hval⟩
  rw [hval]
  by_cases hi : w i = c
  · exact Or.inr hi
  · exact Or.inl (h i hi)

/-- At a critical point of value `c`, the kernel of the critical Hessian of the moment function
has real dimension at most `dim_ℝ 𝕜` times the number of coordinates of weight `c`, less one. It is
computed in the affine chart at a nonzero coordinate. -/
private theorem finrank_ker_criticalHessian_projectiveMomentFunction_le
    {x : ℙ 𝕜 (Fin (n + 1) → 𝕜)}
    (hx : x ∈ criticalPoints 𝓘(ℝ, Fin n → 𝕜) (projectiveMomentFunction 𝕜 w)) :
    finrank ℝ (criticalHessian 𝓘(ℝ, Fin n → 𝕜) (projectiveMomentFunction 𝕜 w) x).ker ≤
      ({i | w i = projectiveMomentFunction 𝕜 w x}.ncard - 1) * finrank ℝ 𝕜 := by
  set f := projectiveMomentFunction 𝕜 w
  obtain ⟨v, hv, rfl⟩ : ∃ v hv, mk 𝕜 v hv = x := ⟨x.rep, x.rep_ne_zero, x.mk_rep⟩
  obtain ⟨k, hk⟩ := Function.ne_iff.1 hv
  have hwk : w k = f (mk 𝕜 v hv) :=
    ((mk_mem_criticalPoints_projectiveMomentFunction_iff hv).1 hx k).resolve_left hk
  -- Work in the affine chart `e` at `k`, where `f` is the chart model.
  set e := affineOpenPartialHomeomorph (K := 𝕜) k
  have he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, Fin n → 𝕜) 2 (ℙ 𝕜 (Fin (n + 1) → 𝕜)) :=
    affineOpenPartialHomeomorph_mem_maximalAtlas k
  have hxe : mk 𝕜 v hv ∈ e.source := by
    simpa [e] using (mk_mem_affineOpen_iff k v hv).2 hk
  set ν := w ∘ k.succAbove
  set z := e.extend 𝓘(ℝ, Fin n → 𝕜) (mk 𝕜 v hv)
  have hcomp : f ∘ (e.extend 𝓘(ℝ, Fin n → 𝕜)).symm = model 𝕜 (w k) ν :=
    projectiveMomentFunction_comp_extend_symm w k
  have hz : ∀ j, z j = 0 ∨ ν j = w k := by
    rw [← fderiv_model_eq_zero_iff_forall, ← hcomp,
      ← mvfderiv_eq_zero_iff_fderiv_comp_extend_symm_eq_zero
        (affineOpenPartialHomeomorph_mem_maximalAtlas k) hxe]
    exact mem_criticalPoints.1 hx
  -- The chart derivative `D` carries the critical Hessian to the Hessian of the model at `z`.
  obtain ⟨D, hD⟩ :
      (mvfderiv 𝓘(ℝ, Fin n → 𝕜) (e.extend 𝓘(ℝ, Fin n → 𝕜)) (mk 𝕜 v hv)).IsInvertible := by
    -- `mvfderiv` is `mfderiv` followed by the identification of the tangent space of the model
    -- with the model; both factors are invertible.
    unfold mvfderiv
    exact ContinuousLinearMap.IsInvertible.comp ⟨NormedSpace.fromTangentSpace _, rfl⟩
      (isInvertible_mfderiv_extend (IsManifold.maximalAtlas_subset_of_le (by norm_num) he) hxe)
  have hH (u t : TangentSpace 𝓘(ℝ, Fin n → 𝕜) (mk 𝕜 v hv)) :
      criticalHessian 𝓘(ℝ, Fin n → 𝕜) f (mk 𝕜 v hv) u t =
        fderiv ℝ (fderiv ℝ (model 𝕜 (w k) ν)) z (D u) (D t) := by
    rw [criticalHessian_apply_eq_of_mem_maximalAtlas he hxe
      ((contMDiff_projectiveMomentFunction w).contMDiffAt) (mem_criticalPoints.1 hx), hcomp, ← hD]
    rfl
  -- A vector of the kernel is determined by its coordinates of weight `w k` read through `D`.
  set s : Set (Fin n) := {j | ν j = w k}
  let φ : (criticalHessian 𝓘(ℝ, Fin n → 𝕜) f (mk 𝕜 v hv)).ker →ₗ[ℝ] (s → 𝕜) :=
    (LinearMap.pi fun j : s ↦ LinearMap.proj (R := ℝ) (φ := fun _ : Fin n ↦ 𝕜) (j : Fin n)) ∘ₗ
      D.toLinearEquiv.toLinearMap ∘ₗ Submodule.subtype _
  have hφ : Injective φ := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    rintro ⟨u, hu⟩ hφu
    have hHu : fderiv ℝ (fderiv ℝ (model 𝕜 (w k) ν)) z (D u) = 0 := by
      refine ContinuousLinearMap.ext fun t ↦ ?_
      obtain ⟨t, rfl⟩ := D.surjective t
      have hu' : criticalHessian 𝓘(ℝ, Fin n → 𝕜) f (mk 𝕜 v hv) u = 0 := hu
      rw [← hH, hu', zero_apply, zero_apply]
    have hDu : D u = 0 := funext fun j ↦ by
      by_cases hj : ν j = w k
      · exact congrFun (LinearMap.mem_ker.1 hφu) ⟨j, hj⟩
      · exact (fderiv_fderiv_model_apply_eq_zero_iff hz (D u)).1 hHu j hj
    exact Subtype.ext (D.map_eq_zero_iff.1 hDu)
  -- The coordinates of weight `w k` other than `k` are the coordinates `j` with `ν j = w k`.
  have himage : k.succAbove '' s = {i | w i = f (mk 𝕜 v hv)} \ {k} := by
    ext i
    simp only [s, ν, mem_image, mem_ofPred_eq, comp_apply, mem_sdiff, mem_singleton_iff]
    refine ⟨fun ⟨j, hj, hji⟩ ↦ hji ▸ ⟨hj.trans hwk, Fin.succAbove_ne k j⟩, fun ⟨hi, hik⟩ ↦ ?_⟩
    obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hik
    exact ⟨j, hi.trans hwk.symm, rfl⟩
  have hcard : Fintype.card s = {i | w i = f (mk 𝕜 v hv)}.ncard - 1 := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq,
      ← Fin.succAbove_right_injective.injOn.ncard_image, himage,
      ncard_sdiff_singleton_of_mem (show k ∈ {i | w i = f (mk 𝕜 v hv)} from hwk)]
  calc finrank ℝ (criticalHessian 𝓘(ℝ, Fin n → 𝕜) f (mk 𝕜 v hv)).ker
      ≤ finrank ℝ (s → 𝕜) := LinearMap.finrank_le_finrank_of_injective hφ
    _ = ({i | w i = f (mk 𝕜 v hv)}.ncard - 1) * finrank ℝ 𝕜 := by
      rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, hcard, smul_eq_mul]

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
    induction s using ind with | h u hu =>
    rw [SmoothEmbedding.ofIsSmoothEmbedding_apply, map_mk]
    exact (mk_mem_criticalPoints_projectiveMomentFunction_and_eq_iff _).2 (hLw u)
  have hcs : i.IsCriticalSubmanifold (projectiveMomentFunction 𝕜 w) :=
    ⟨fun _ ↦ (contMDiff_projectiveMomentFunction w).contMDiffAt, fun s ↦ (hcrit s).1⟩
  refine ⟨hcs, fun s ↦ ?_⟩
  -- The tangent space lies in the kernel and has at least its dimension, so the two agree.
  refine (Submodule.eq_of_le_of_finrank_le (hcs.tangentRange_le_ker_criticalHessian hr0 s)
    ?_).ge
  rw [SmoothEmbedding.tangentRange,
    LinearMap.finrank_range_of_inj ((i.isImmersion.isImmersionAt s).mfderiv_injective hr0)]
  refine (finrank_ker_criticalHessian_projectiveMomentFunction_le (hcrit s).1).trans_eq ?_
  rw [(hcrit s).2, hm, Nat.add_sub_cancel]
  -- The tangent spaces of `ℙᵐ` are the model space `Fin m → 𝕜`.
  change m * finrank ℝ 𝕜 = finrank ℝ (Fin m → 𝕜)
  rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul]

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
coordinates of weight `c`. -/
private def weightIncl (𝕜 : Type*) [RCLike 𝕜] (hc : c ∈ range w) :
    (Fin (weightDim w c + 1) → 𝕜) →ₗ[𝕜] Fin (n + 1) → 𝕜 :=
  LinearMap.pi fun i ↦ if h : w i = c then LinearMap.proj ((weightEquiv hc).symm ⟨i, h⟩) else 0

private theorem weightIncl_apply (hc : c ∈ range w) (u : Fin (weightDim w c + 1) → 𝕜)
    (i : Fin (n + 1)) :
    weightIncl 𝕜 hc u i = if h : w i = c then u ((weightEquiv hc).symm ⟨i, h⟩) else 0 := by
  by_cases h : w i = c <;> simp [weightIncl, h]

private theorem weightIncl_apply_weightEquiv (hc : c ∈ range w) (u : Fin (weightDim w c + 1) → 𝕜)
    (a : Fin (weightDim w c + 1)) : weightIncl 𝕜 hc u (weightEquiv hc a) = u a := by
  simp [weightIncl_apply, (weightEquiv hc a).2]

private theorem injective_weightIncl (hc : c ∈ range w) : Injective (weightIncl 𝕜 hc) :=
  fun u u' h ↦ funext fun a ↦ by
    rw [← weightIncl_apply_weightEquiv hc u, ← weightIncl_apply_weightEquiv hc u', h]

private theorem weightIncl_apply_of_ne (hc : c ∈ range w) (u : Fin (weightDim w c + 1) → 𝕜)
    {i : Fin (n + 1)} (hi : w i ≠ c) : weightIncl 𝕜 hc u i = 0 := by
  simp [weightIncl_apply, hi]

/-- Every vector of the weight space of `c` is in the image of `weightIncl`. -/
private theorem weightIncl_comp_weightEquiv (hc : c ∈ range w) {v : Fin (n + 1) → 𝕜}
    (hv : ∀ i, w i ≠ c → v i = 0) : weightIncl 𝕜 hc (fun a ↦ v (weightEquiv hc a)) = v := by
  funext i
  rw [weightIncl_apply]
  split_ifs with h
  · simp
  · exact (hv i h).symm

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
  ext x
  induction x using ind with | h v hv =>
  simp only [mem_inter_iff, mem_preimage, mem_singleton_iff,
    mk_mem_criticalPoints_projectiveMomentFunction_and_eq_iff, weightEmbedding,
    SmoothEmbedding.coe_ofIsSmoothEmbedding, mem_range]
  constructor
  · rintro ⟨s, hs⟩
    induction s using ind with | h u hu =>
    rw [map_mk, mk_eq_mk_iff] at hs
    obtain ⟨a, ha⟩ := hs
    intro i hi
    have hai := congrFun ha i
    rw [Pi.smul_apply, weightIncl_apply_of_ne hc u hi, Units.smul_def, smul_eq_mul,
      mul_eq_zero] at hai
    exact hai.resolve_left a.ne_zero
  · intro h
    have hu : (fun a ↦ v (weightEquiv hc a)) ≠ 0 := fun hu ↦ hv <| by
      rw [← weightIncl_comp_weightEquiv hc h, hu, map_zero]
    exact ⟨mk 𝕜 _ hu, by simp [map_mk, weightIncl_comp_weightEquiv hc h]⟩

/-- **The Morse index of the moment function at an arbitrary critical point.** At a critical point
of value `c`, the Morse index of the moment function is the real dimension of `𝕜` times the number
of weights below `c`. Over `ℂ` this is twice that number. -/
theorem manifoldMorseIndex_projectiveMomentFunction_of_mem_criticalPoints
    {x : ℙ 𝕜 (Fin (n + 1) → 𝕜)}
    (hx : x ∈ criticalPoints 𝓘(ℝ, Fin n → 𝕜) (projectiveMomentFunction 𝕜 w)) :
    manifoldMorseIndex 𝓘(ℝ, Fin n → 𝕜) (projectiveMomentFunction 𝕜 w) x =
      finrank ℝ 𝕜 * {i | w i < projectiveMomentFunction 𝕜 w x}.ncard := by
  set c := projectiveMomentFunction 𝕜 w x
  -- The critical value `c` is the weight of a nonzero coordinate.
  obtain ⟨v, hv, rfl⟩ : ∃ v hv, mk 𝕜 v hv = x := ⟨x.rep, x.rep_ne_zero, x.mk_rep⟩
  obtain ⟨k, hk⟩ := Function.ne_iff.1 hv
  have hwk : w k = c :=
    ((mk_mem_criticalPoints_projectiveMomentFunction_iff hv).1 hx k).resolve_left hk
  have hc : c ∈ range w := ⟨k, hwk⟩
  -- The index is constant along the projective subspace of the weight space of `c`, which
  -- passes through `x` and through the coordinate point `[eₖ]`.
  have hr : (1 : ℕ∞ω) ≤ 2 := by norm_num
  set i := weightEmbedding 𝕜 hc hr
  have hconst := (isNondegenerateCriticalSubmanifold_weightEmbedding (𝕜 := 𝕜) hc
    hr).isLocallyConstant_manifoldMorseIndex two_ne_zero
  have hrange := range_weightEmbedding (𝕜 := 𝕜) hc hr
  obtain ⟨s, hs⟩ : mk 𝕜 v hv ∈ range i := by
    rw [hrange]
    exact ⟨hx, rfl⟩
  obtain ⟨s₀, hs₀⟩ : mk 𝕜 (Pi.single k 1) (by simp) ∈ range i := by
    rw [hrange, mem_inter_iff, mem_preimage, mem_singleton_iff,
      mk_mem_criticalPoints_projectiveMomentFunction_and_eq_iff]
    intro j hj
    exact Pi.single_eq_of_ne (fun h ↦ hj (by rw [h, hwk])) 1
  rw [← hs, hconst.apply_eq_of_preconnectedSpace s s₀, hs₀,
    manifoldMorseIndex_projectiveMomentFunction, hwk]

/-- **The moment function is Morse–Bott.** For arbitrary weights `w`, the moment function on
`ℙ 𝕜 (Fin (n + 1) → 𝕜)` is a Morse–Bott function for the underlying real smooth structure. Its
critical components are indexed by the values `c` of the weights: if `m c + 1` coordinates carry
the weight `c`, the component of value `c` is a projective space `ℙ 𝕜 (Fin (m c + 1) → 𝕜)`,
embedded onto the critical points of value `c`. -/
theorem exists_isMorseBottFamily_projectiveMomentFunction (𝕜 : Type*) [RCLike 𝕜]
    (w : Fin (n + 1) → ℝ) {r : ℕ∞ω} (hr : 2 ≤ r) :
    ∃ (m : range w → ℕ) (i : ∀ c : range w, SmoothEmbedding 𝓘(ℝ, Fin (m c) → 𝕜)
        𝓘(ℝ, Fin n → 𝕜) r (ℙ 𝕜 (Fin (m c + 1) → 𝕜)) (ℙ 𝕜 (Fin (n + 1) → 𝕜))),
      (∀ c : range w, {i | w i = c}.ncard = m c + 1) ∧
      (∀ c : range w, range (i c) =
        criticalPoints 𝓘(ℝ, Fin n → 𝕜) (projectiveMomentFunction 𝕜 w) ∩
          projectiveMomentFunction 𝕜 w ⁻¹' {(c : ℝ)}) ∧
      IsMorseBottFamily i (projectiveMomentFunction 𝕜 w) := by
  have hr1 : 1 ≤ r := le_trans (by norm_num) hr
  refine ⟨fun c ↦ weightDim w c, fun c ↦ weightEmbedding 𝕜 c.2 hr1,
    fun c ↦ ncard_eq_weightDim_add_one c.2, fun c ↦ range_weightEmbedding c.2 hr1,
    IsMorseBottFamily.of_pairwise_disjoint hr (contMDiff_projectiveMomentFunction w)
      (fun c ↦ isNondegenerateCriticalSubmanifold_weightEmbedding c.2 hr1) ?_ ?_⟩
  · intro c c' hcc'
    rw [Function.onFun, range_weightEmbedding, range_weightEmbedding]
    exact Disjoint.inter_left' _ (Disjoint.inter_right' _
      (Disjoint.preimage _ (disjoint_singleton.2 fun h ↦ hcc' (Subtype.ext h))))
  · intro x hx
    -- The value at a critical point is the weight of one of its nonzero coordinates.
    obtain ⟨v, hv, rfl⟩ : ∃ v hv, mk 𝕜 v hv = x := ⟨x.rep, x.rep_ne_zero, x.mk_rep⟩
    obtain ⟨k, hk⟩ := Function.ne_iff.1 hv
    have hwk := ((mk_mem_criticalPoints_projectiveMomentFunction_iff hv).1 hx k).resolve_left hk
    refine mem_iUnion.2 ⟨⟨_, k, hwk⟩, ?_⟩
    rw [range_weightEmbedding]
    exact ⟨hx, rfl⟩

end TauCeti

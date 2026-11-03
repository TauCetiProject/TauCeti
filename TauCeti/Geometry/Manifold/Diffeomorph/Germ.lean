/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import TauCeti.Analysis.Normed.Operator.PositiveDeterminant
public import TauCeti.Geometry.Manifold.Diffeomorph.Perturbation

/-!
# Germs of diffeomorphisms with small compact support

Let `E` be a finite-dimensional real normed space and let `g : E → E` be a `C^n` map near a point
`c`, `1 ≤ n`, which fixes `c` and whose derivative at `c` has positive determinant. Then for every
neighbourhood `U` of `c` there is a `C^n` diffeomorphism of `E` which is the identity outside a
compact subset of `U` and agrees with `g` near `c`
(`TauCeti.exists_diffeomorph_eventuallyEq_of_det_fderiv_pos`). So an orientation-preserving local
diffeomorphism germ at a fixed point is the germ of a compactly supported diffeomorphism.

Read in a chart, this is what compares two orientation-compatible ball embeddings with the same
centre in a manifold: the transition between them is such a germ, and the compactly supported
diffeomorphism realizing it, extended by the identity outside the chart, carries one embedding to
the other near the centre. This is the Euclidean core of the ambient disc theorem of Palais, which
shows that a connected sum does not depend on the balls along which it is formed.

The construction does not integrate vector fields. It has two ingredients.

* **Perturbations of the identity.** If `u : E → E` is `C^n` and `K`-Lipschitz with `K < 1`, then
  `x ↦ x + u x` is a `C^n` diffeomorphism of `E`, for `E` a Banach space over any nontrivially
  normed field (`ContDiff.exists_diffeomorph_apply_eq_add_of_lipschitzWith`, in
  `TauCeti.Geometry.Manifold.Diffeomorph.Perturbation`): it is a
  homeomorphism because it approximates the identity (`ApproximatesLinearOn.toHomeomorph`), and
  its derivative `1 + Du` is invertible everywhere, so its inverse is `C^n`
  (`Homeomorph.contDiff_symm`).
* **Cutting off.** If the derivative of `h` stays close to the identity on the closed ball of
  radius `2 r` about a fixed point `c`, then `u = ρ • (h - id)`, for a bump function `ρ` equal to
  `1` on the ball of radius `r` and supported in that of radius `2 r`, has small derivative: the
  term `Dρ ⊗ (h - id)` is of size `r⁻¹ · r`, by the mean value inequality. So `id + u` is a
  diffeomorphism which is `h` near `c` and the identity off the ball of radius `2 r`.

Cutting off applies directly to a germ tangent to the identity, and to an affine map
`x ↦ c + L (x - c)` with `L` close to the identity. Germs realized in this way can be composed and
inverted. Along a path `t ↦ γ t` of linear maps of positive determinant from the identity to any
given one (`ContinuousLinearMap.exists_contDiff_det_pos`), the parameters `t` for which the
affine map with linear part `γ t` is realized therefore form an open and closed subset of `ℝ`, so
all of it. Composing the derivative `A` of `g` at `c` with
the germ `A⁻¹ ∘ g`, tangent to the identity, gives `g`.

## Main results

* `TauCeti.exists_diffeomorph_eventuallyEq_of_det_fderiv_pos`: an orientation-preserving `C^n`
  germ at a fixed point is the germ of a `C^n` diffeomorphism supported in a compact subset of any
  prescribed neighbourhood.

## References

* R. Palais, *Extending diffeomorphisms*, Proc. Amer. Math. Soc. 11 (1960), 274–277.
* M. Hirsch, *Differential Topology*, Springer GTM 33 (1976), Chapter 8, §3 (the disc theorem).
-/

public section

noncomputable section

open Set Filter Metric Topology
open scoped Manifold ContDiff NNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The affine map `x ↦ c + L (x - c)` fixing `c` with linear part `L`. -/
private def affineAt (c : E) (L : E →L[ℝ] E) (x : E) : E :=
  c + L (x - c)

private theorem affineAt_self (c : E) (L : E →L[ℝ] E) : affineAt c L c = c := by
  simp [affineAt]

private theorem affineAt_id (c : E) : affineAt c (ContinuousLinearMap.id ℝ E) = id := by
  ext x
  simp [affineAt]

private theorem affineAt_comp (c : E) (L M : E →L[ℝ] E) :
    affineAt c L ∘ affineAt c M = affineAt c (L.comp M) := by
  ext x
  simp [affineAt]

private theorem contDiff_affineAt (c : E) (L : E →L[ℝ] E) {n : WithTop ℕ∞} :
    ContDiff ℝ n (affineAt c L) :=
  contDiff_const.add (L.contDiff.comp (contDiff_id.sub contDiff_const))

private theorem hasFDerivAt_affineAt (c : E) (L : E →L[ℝ] E) (x : E) :
    HasFDerivAt (affineAt c L) L x :=
  ((L.hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const c)).const_add c).congr_fderiv
    (L.comp_id)

/-- The germ of `g` at `c` is the germ of a `C^n` diffeomorphism of `E` which is the identity
outside a compact subset of any prescribed neighbourhood of `c`. -/
private def Realizes (n : ℕ∞) (c : E) (g : E → E) : Prop :=
  ∀ U ∈ 𝓝 c, ∃ (φ : E ≃ₘ^n⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ E) (K : Set E), IsCompact K ∧ K ⊆ U ∧
    EqOn φ id Kᶜ ∧ ⇑φ =ᶠ[𝓝 c] g

private theorem realizes_id {n : ℕ∞} {c : E} : Realizes n c id :=
  fun _ _ ↦ ⟨Diffeomorph.refl _ _ _, ∅, isCompact_empty, empty_subset _, fun _ _ ↦ rfl,
    EventuallyEq.rfl⟩

private theorem Realizes.comp {n : ℕ∞} {c : E} {g₁ g₂ : E → E} (h₁ : Realizes n c g₁)
    (h₂ : Realizes n c g₂) (hg₂ : g₂ c = c) : Realizes n c (g₁ ∘ g₂) := by
  intro U hU
  obtain ⟨φ₁, K₁, hK₁, hK₁U, hφ₁K, hφ₁⟩ := h₁ U hU
  obtain ⟨φ₂, K₂, hK₂, hK₂U, hφ₂K, hφ₂⟩ := h₂ U hU
  have ht : Tendsto φ₂ (𝓝 c) (𝓝 c) := by
    simpa [hφ₂.eq_of_nhds.trans hg₂] using φ₂.continuous.tendsto c
  refine ⟨φ₂.trans φ₁, K₁ ∪ K₂, hK₁.union hK₂, union_subset hK₁U hK₂U, fun x hx ↦ ?_, ?_⟩
  · rw [compl_union] at hx
    simp [hφ₂K hx.2, hφ₁K hx.1]
  · rw [Diffeomorph.coe_trans]
    exact (hφ₁.comp_tendsto ht).trans (hφ₂.fun_comp g₁)

private theorem Realizes.of_leftInverse {n : ℕ∞} {c : E} {g g' : E → E} (h : Realizes n c g)
    (hgc : g c = c) (hg' : Function.LeftInverse g' g) : Realizes n c g' := by
  intro U hU
  obtain ⟨φ, K, hK, hKU, hφK, hφ⟩ := h U hU
  have hc : φ.symm c = c :=
    (Equiv.symm_apply_eq φ.toEquiv).2 (by rw [Diffeomorph.coe_toEquiv, hφ.eq_of_nhds, hgc])
  have ht : Tendsto φ.symm (𝓝 c) (𝓝 c) := by
    simpa [hc] using φ.symm.continuous.tendsto c
  refine ⟨φ.symm, K, hK, hKU, fun x hx ↦ ?_, ?_⟩
  · have hx' : φ x = x := hφK hx
    exact (Equiv.symm_apply_eq φ.toEquiv).2 (by rw [Diffeomorph.coe_toEquiv, id_eq, hx'])
  · filter_upwards [ht.eventually hφ] with y hy
    rw [Diffeomorph.apply_symm_apply] at hy
    nth_rw 2 [hy]
    exact (hg' _).symm

variable [FiniteDimensional ℝ E]

/-- **Cutting off.** There is `δ > 0`, depending only on `E`, such that a `C^n` map `h` fixing `c`
whose derivative is within `δ` of the identity on the closed ball of radius `2 r` about `c` agrees
on the closed ball of radius `r` with a `C^n` diffeomorphism which is the identity off the closed
ball of radius `2 r`. The diffeomorphism is `id + ρ • (h - id)` for a bump function `ρ`. -/
private theorem exists_pos_forall_exists_diffeomorph_eqOn :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (n : ℕ∞), 1 ≤ n → ∀ (c : E) (h : E → E) (r : ℝ), 0 < r → h c = c →
      (∀ x ∈ closedBall c (2 * r), ContDiffAt ℝ n h x) →
      (∀ x ∈ closedBall c (2 * r), ‖fderiv ℝ h x - ContinuousLinearMap.id ℝ E‖ ≤ δ) →
      ∃ φ : E ≃ₘ^n⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ E, EqOn φ h (closedBall c r) ∧
        EqOn φ id (closedBall c (2 * r))ᶜ := by
  let β : ContDiffBump (0 : E) := ⟨1, 2, one_pos, one_lt_two⟩
  have hβ : Continuous (fderiv ℝ β) := (β.contDiff (n := 1)).continuous_fderiv one_ne_zero
  obtain ⟨C, hC⟩ := hβ.bounded_above_of_compact_support (β.hasCompactSupport.fderiv (𝕜 := ℝ))
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  refine ⟨(2 * (1 + 2 * C))⁻¹, by positivity, ?_⟩
  intro n hn c h r hr hhc hcd hδ
  have hn' : (n : WithTop ℕ∞) ≠ 0 := by exact_mod_cast (zero_lt_one.trans_le hn).ne'
  set δ : ℝ := (2 * (1 + 2 * C))⁻¹ with hδdef
  have hδ0 : 0 ≤ δ := by positivity
  -- The cutoff `ρ x = β (r⁻¹ • (x - c))`, equal to `1` on `closedBall c r` and to `0` off
  -- `ball c (2 * r)`, with derivative of norm at most `C * r⁻¹`.
  let ρ : E → ℝ := fun x ↦ β (r⁻¹ • (x - c))
  let ρ' : E → E →L[ℝ] ℝ := fun x ↦
    (fderiv ℝ β (r⁻¹ • (x - c))).comp (r⁻¹ • ContinuousLinearMap.id ℝ E)
  have hnorm (x : E) : ‖r⁻¹ • (x - c)‖ = r⁻¹ * dist x c := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hr.le), dist_eq_norm]
  have hρ1 (x : E) (hx : x ∈ closedBall c r) : ρ x = 1 := by
    refine β.one_of_mem_closedBall ?_
    rw [mem_closedBall, dist_zero_right, hnorm]
    exact (inv_mul_le_one₀ hr).2 (mem_closedBall.1 hx)
  have hρ0 (x : E) (hx : 2 * r < dist x c) : ρ x = 0 := by
    refine Function.notMem_support.1 fun hx' ↦ ?_
    have hmem : r⁻¹ • (x - c) ∈ Function.support β := hx'
    rw [β.support_eq, mem_ball, dist_zero_right, hnorm] at hmem
    have h2 : r⁻¹ * dist x c < 2 := hmem
    rw [inv_mul_lt_iff₀ hr] at h2
    linarith
  have hρd (x : E) : HasFDerivAt ρ (ρ' x) x :=
    ((β.contDiff (n := 1)).differentiable one_ne_zero _).hasFDerivAt.comp x
      (((hasFDerivAt_id x).sub_const c).const_smul r⁻¹)
  have hρ'le (x : E) : ‖ρ' x‖ ≤ C * r⁻¹ := by
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul (hC _) ?_ (norm_nonneg _) hC0)
    refine (norm_smul_le r⁻¹ (ContinuousLinearMap.id ℝ E)).trans ?_
    rw [Real.norm_of_nonneg (inv_nonneg.2 hr.le)]
    exact mul_le_of_le_one_right (inv_nonneg.2 hr.le) ContinuousLinearMap.norm_id_le
  -- The perturbation `u = ρ • (h - id)`.
  let u : E → E := fun x ↦ ρ x • (h x - x)
  have hu0 (x : E) (hx : x ∉ closedBall c (2 * r)) : u =ᶠ[𝓝 x] fun _ ↦ 0 := by
    have hx' : 2 * r < dist x c := not_le.1 hx
    filter_upwards [(isOpen_lt continuous_const (continuous_id.dist continuous_const)).mem_nhds
      hx'] with y hy
    simp [u, hρ0 y hy]
  have hucd : ContDiff ℝ n u := by
    refine contDiff_iff_contDiffAt.2 fun x ↦ ?_
    by_cases hx : x ∈ closedBall c (2 * r)
    · exact (β.contDiff.comp (contDiff_const.smul (contDiff_id.sub contDiff_const))).contDiffAt.smul
        ((hcd x hx).sub contDiffAt_id)
    · exact contDiffAt_const.congr_of_eventuallyEq (hu0 x hx)
  have hhd (x : E) (hx : x ∈ closedBall c (2 * r)) :
      HasFDerivAt (fun y ↦ h y - y) (fderiv ℝ h x - ContinuousLinearMap.id ℝ E) x :=
    ((hcd x hx).differentiableAt hn').hasFDerivAt.sub (hasFDerivAt_id x)
  -- By the mean value inequality, `h - id` moves points of the ball by at most `δ ‖x - c‖`.
  have hmv (x : E) (hx : x ∈ closedBall c (2 * r)) : ‖h x - x‖ ≤ δ * (2 * r) := by
    have := Convex.norm_image_sub_le_of_norm_fderiv_le (fun y hy ↦ (hhd y hy).differentiableAt)
      (fun y hy ↦ (hhd y hy).fderiv ▸ hδ y hy) (convex_closedBall c (2 * r))
      (mem_closedBall_self (by positivity)) hx
    rw [hhc, sub_self, sub_zero] at this
    exact this.trans (mul_le_mul_of_nonneg_left (mem_closedBall_iff_norm.1 hx) hδ0)
  have hud (x : E) : ‖fderiv ℝ u x‖ ≤ 2⁻¹ := by
    by_cases hx : x ∈ closedBall c (2 * r)
    · have hD : HasFDerivAt u (ρ x • (fderiv ℝ h x - ContinuousLinearMap.id ℝ E) +
          (ρ' x).smulRight (h x - x)) x := (hρd x).smul (hhd x hx)
      have hρx : ‖ρ x‖ ≤ 1 := by
        rw [Real.norm_of_nonneg β.nonneg]
        exact β.le_one
      rw [hD.fderiv]
      calc _ ≤ ‖ρ x • (fderiv ℝ h x - ContinuousLinearMap.id ℝ E)‖ +
            ‖(ρ' x).smulRight (h x - x)‖ := norm_add_le _ _
        _ ≤ 1 * δ + C * r⁻¹ * (δ * (2 * r)) := by
          gcongr
          · exact (norm_smul_le _ _).trans (mul_le_mul hρx (hδ x hx) (norm_nonneg _) zero_le_one)
          · rw [ContinuousLinearMap.norm_smulRight_apply]
            exact mul_le_mul (hρ'le x) (hmv x hx) (norm_nonneg _) (by positivity)
        _ = 2⁻¹ := by
          rw [hδdef]
          field_simp
    · rw [(hu0 x hx).fderiv_eq]
      simp
  have hlip : LipschitzWith 2⁻¹ u :=
    lipschitzWith_of_nnnorm_fderiv_le (hucd.differentiable hn') fun x ↦ by
      rw [← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_inv, NNReal.coe_ofNat]
      exact hud x
  obtain ⟨φ, hφ⟩ := hucd.exists_diffeomorph_apply_eq_add_of_lipschitzWith (by exact_mod_cast hn)
    hlip (by norm_num)
  refine ⟨φ, fun x hx ↦ ?_, fun x hx ↦ ?_⟩
  · simp [hφ, u, hρ1 x hx]
  · simp [hφ, u, hρ0 x (not_le.1 hx)]

/-- A germ at a fixed point whose derivative stays within the cutoff constant of the identity
near that point is realized by compactly supported diffeomorphisms. -/
private theorem exists_pos_forall_realizes :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (n : ℕ∞), 1 ≤ n → ∀ (c : E) (h : E → E), h c = c →
      (∀ᶠ x in 𝓝 c, ContDiffAt ℝ n h x ∧
        ‖fderiv ℝ h x - ContinuousLinearMap.id ℝ E‖ ≤ δ) → Realizes n c h := by
  obtain ⟨δ, hδ, H⟩ := exists_pos_forall_exists_diffeomorph_eqOn (E := E)
  refine ⟨δ, hδ, fun n hn c h hhc hev U hU ↦ ?_⟩
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.1 (inter_mem hU hev)
  have hsub : closedBall c (2 * (ε / 4)) ⊆ ball c ε :=
    closedBall_subset_ball (by linarith)
  obtain ⟨φ, hφh, hφid⟩ := H n hn c h (ε / 4) (by positivity) hhc
    (fun x hx ↦ (hεU (hsub hx)).2.1) (fun x hx ↦ (hεU (hsub hx)).2.2)
  exact ⟨φ, closedBall c (2 * (ε / 4)), isCompact_closedBall _ _,
    hsub.trans (hεU.trans inter_subset_left), hφid,
    eventually_of_mem (closedBall_mem_nhds c (by positivity)) hφh⟩

/-- A germ tangent to the identity at a fixed point is realized. -/
private theorem realizes_of_fderiv_eq_id {n : ℕ∞} (hn : 1 ≤ n) {c : E} {h : E → E}
    (hcd : ∀ᶠ x in 𝓝 c, ContDiffAt ℝ n h x) (hhc : h c = c)
    (hD : fderiv ℝ h c = ContinuousLinearMap.id ℝ E) : Realizes n c h := by
  obtain ⟨δ, hδ, H⟩ := exists_pos_forall_realizes (E := E)
  refine H n hn c h hhc (hcd.and ?_)
  have hcont : ContinuousAt (fderiv ℝ h) c :=
    (hcd.self_of_nhds.fderiv_right (m := 0) (by simpa using hn)).continuousAt
  filter_upwards [hcont.eventually (closedBall_mem_nhds _ hδ)] with x hx
  simpa [dist_eq_norm, hD] using hx

/-- Affine maps whose linear part is close to the identity are realized. -/
private theorem eventually_realizes_affineAt {n : ℕ∞} (hn : 1 ≤ n) (c : E) :
    ∀ᶠ L in 𝓝 (ContinuousLinearMap.id ℝ E), Realizes n c (affineAt c L) := by
  obtain ⟨δ, hδ, H⟩ := exists_pos_forall_realizes (E := E)
  filter_upwards [closedBall_mem_nhds _ hδ] with L hL
  refine H n hn c _ (affineAt_self c L) (Eventually.of_forall fun x ↦ ⟨?_, ?_⟩)
  · exact (contDiff_affineAt c L).contDiffAt
  · rwa [(hasFDerivAt_affineAt c L x).fderiv, ← dist_eq_norm, ← mem_closedBall]

/-- Affine maps whose linear part has positive determinant are realized: along a path of such
linear maps from the identity, realizability is locally constant. -/
private theorem realizes_affineAt {n : ℕ∞} (hn : 1 ≤ n) (c : E) {L : E →L[ℝ] E}
    (hL : 0 < L.det) : Realizes n c (affineAt c L) := by
  obtain ⟨γ, hγ, hγ0, hγ1, hγdet⟩ := L.exists_contDiff_det_pos hL
  let e (t : ℝ) : E ≃L[ℝ] E := (γ t).toContinuousLinearEquivOfDetNeZero (hγdet t).ne'
  have he (t : ℝ) : (e t : E →L[ℝ] E) = γ t :=
    ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero _ _
  have key (t : ℝ) : ∀ᶠ s in 𝓝 t,
      (Realizes n c (affineAt c (γ s)) ↔ Realizes n c (affineAt c (γ t))) := by
    -- `B = γ s ∘ (γ t)⁻¹` tends to the identity as `s → t`.
    have hB : Tendsto (fun s ↦ (γ s).comp ((e t).symm : E →L[ℝ] E)) (𝓝 t)
        (𝓝 (ContinuousLinearMap.id ℝ E)) := by
      have := ((hγ.continuous.clm_comp continuous_const).tendsto t :
        Tendsto (fun s ↦ (γ s).comp ((e t).symm : E →L[ℝ] E)) (𝓝 t) _)
      rwa [← he t, ContinuousLinearEquiv.coe_comp_coe_symm] at this
    filter_upwards [hB.eventually (eventually_realizes_affineAt hn c)] with s hs
    constructor
    · -- `γ t = (γ t ∘ (γ s)⁻¹) ∘ γ s`, and `γ t ∘ (γ s)⁻¹` is a left inverse of `B`.
      intro hs'
      have hinv : Function.LeftInverse (affineAt c ((γ t).comp ((e s).symm : E →L[ℝ] E)))
          (affineAt c ((γ s).comp ((e t).symm : E →L[ℝ] E))) := fun x ↦ by
        rw [← Function.comp_apply (f := affineAt c _), affineAt_comp, ← he s, ← he t]
        simp [affineAt]
      convert (hs.of_leftInverse (affineAt_self _ _) hinv).comp hs' (affineAt_self _ _) using 1
      rw [affineAt_comp, ← he s, ← he t]
      congr 1
      ext x
      simp
    · intro ht'
      convert hs.comp ht' (affineAt_self _ _) using 1
      rw [affineAt_comp, ← he t]
      congr 1
      ext x
      simp
  have hS : IsClopen {t | Realizes n c (affineAt c (γ t))} := by
    refine ⟨isOpen_compl_iff.1 (isOpen_iff_mem_nhds.2 fun t ht ↦ ?_),
      isOpen_iff_mem_nhds.2 fun t ht ↦ ?_⟩
    · exact (key t).mono fun s hs hs' ↦ ht (hs.1 hs')
    · exact (key t).mono fun s hs ↦ hs.2 ht
  have h0 : (0 : ℝ) ∈ {t | Realizes n c (affineAt c (γ t))} := by
    simpa [hγ0, affineAt_id] using (realizes_id (n := n) (c := c))
  have h1 : (1 : ℝ) ∈ {t | Realizes n c (affineAt c (γ t))} := by
    rw [hS.eq_univ ⟨0, h0⟩]
    exact mem_univ _
  simpa [hγ1] using h1

/-- **Orientation-preserving germs are germs of compactly supported diffeomorphisms.** Let `E` be
a finite-dimensional real normed space and `1 ≤ n`. If `g : E → E` is `C^n` near `c`, fixes `c`,
and has a derivative of positive determinant at `c`, then for every neighbourhood `U` of `c` there
is a `C^n` diffeomorphism `φ` of `E` which is the identity outside a compact subset `K` of `U` and
agrees with `g` near `c`. -/
theorem exists_diffeomorph_eventuallyEq_of_det_fderiv_pos {n : ℕ∞} (hn : 1 ≤ n) {c : E}
    {g : E → E} (hg : ∀ᶠ x in 𝓝 c, ContDiffAt ℝ n g x) (hgc : g c = c)
    (hdet : 0 < (fderiv ℝ g c).det) {U : Set E} (hU : U ∈ 𝓝 c) :
    ∃ (φ : E ≃ₘ^n⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ E) (K : Set E), IsCompact K ∧ K ⊆ U ∧
      EqOn φ id Kᶜ ∧ ⇑φ =ᶠ[𝓝 c] g := by
  have hn' : (n : WithTop ℕ∞) ≠ 0 := by exact_mod_cast (zero_lt_one.trans_le hn).ne'
  -- Write `g = A ∘ (A⁻¹ ∘ g)` with `A` the derivative of `g` at `c`, both read about `c`.
  let eA : E ≃L[ℝ] E := (fderiv ℝ g c).toContinuousLinearEquivOfDetNeZero hdet.ne'
  have heA : (eA : E →L[ℝ] E) = fderiv ℝ g c :=
    ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero _ _
  let h : E → E := affineAt c (eA.symm : E →L[ℝ] E) ∘ g
  have hhc : h c = c := by
    simp only [h, Function.comp_apply, hgc, affineAt_self]
  have hD : fderiv ℝ h c = ContinuousLinearMap.id ℝ E := by
    have := (hasFDerivAt_affineAt c (eA.symm : E →L[ℝ] E) (g c)).comp c
      (hg.self_of_nhds.differentiableAt hn').hasFDerivAt
    rw [this.fderiv, ← heA, ContinuousLinearEquiv.coe_symm_comp_coe]
  have hh : Realizes n c h := realizes_of_fderiv_eq_id hn
    (hg.mono fun x hx ↦ (contDiff_affineAt c _).contDiffAt.comp x hx) hhc hD
  have hg_eq : affineAt c (fderiv ℝ g c) ∘ h = g := by
    ext x
    simp only [h, affineAt, Function.comp_apply, add_sub_cancel_left, ← heA,
      ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply, add_sub_cancel]
  exact hg_eq ▸ (realizes_affineAt hn c hdet).comp hh hhc U hU

end TauCeti

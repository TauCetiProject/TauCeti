/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homeomorph.ClosedBall
public import TauCeti.Topology.Homotopy.Isotopy.Restrict

/-!
# Alexander's trick

A homeomorphism `f` of a real normed space with uniformly bounded displacement is joined to
the identity by the ambient isotopy `x ↦ t • f (t⁻¹ • x)` for `t > 0`, starting at the identity
at `t = 0`. The displacement at time `t` is at most `t` times the original bound, giving joint
continuity at time zero. The inverse is the same construction applied to `f.symm`.

In particular a homeomorphism of the closed unit ball fixing its boundary is isotopic to the
identity relative to the boundary. Its identity extension has an isotopy supported in the ball
of radius `t` at time `t`. This is the disc step in the Alexander method for classifying
homeomorphisms of surfaces after fixing a system of cutting curves.

## References

* B. Farb, D. Margalit, *A Primer on Mapping Class Groups*, Section 2.2.1, Lemma 2.1
  (the Alexander lemma); Section 2.3 (the Alexander method).
-/

public section

noncomputable section

open Metric Set Filter Topology unitInterval

namespace Homeomorph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private def shrinkMap (f : E ≃ₜ E) (p : I × E) : E :=
  if p.1 = 0 then p.2 else (p.1 : ℝ) • f ((p.1 : ℝ)⁻¹ • p.2)

private theorem shrinkMap_inverse (f : E ≃ₜ E) (t : I) (x : E) :
    shrinkMap f.symm (t, shrinkMap f (t, x)) = x := by
  by_cases ht : t = 0
  · simp [shrinkMap, ht]
  · have ht' : (t : ℝ) ≠ 0 := fun h => ht (Subtype.ext h)
    simp [shrinkMap, ht, ht']

private theorem norm_shrinkMap_sub_le (f : E ≃ₜ E) {C : ℝ}
    (hC : ∀ x, ‖f x - x‖ ≤ C) (p : I × E) :
    ‖shrinkMap f p - p.2‖ ≤ (p.1 : ℝ) * C := by
  by_cases ht : p.1 = 0
  · simp [shrinkMap, ht]
  · have ht' : (p.1 : ℝ) ≠ 0 := fun h => ht (Subtype.ext h)
    have heq : (p.1 : ℝ) • f ((p.1 : ℝ)⁻¹ • p.2) - p.2 =
        (p.1 : ℝ) • (f ((p.1 : ℝ)⁻¹ • p.2) - (p.1 : ℝ)⁻¹ • p.2) := by
      rw [smul_sub, smul_inv_smul₀ ht']
    rw [shrinkMap, ite_eq_right ht, heq, norm_smul_of_nonneg p.1.2.1]
    exact mul_le_mul_of_nonneg_left (hC _) p.1.2.1

private theorem continuous_shrinkMap (f : E ≃ₜ E) {C : ℝ}
    (hC : ∀ x, ‖f x - x‖ ≤ C) : Continuous (shrinkMap f) := by
  refine continuous_iff_continuousAt.mpr fun p => ?_
  have ht : ContinuousAt (fun q : I × E => (q.1 : ℝ)) p := by fun_prop
  by_cases hp : p.1 = 0
  · have hlim : Tendsto (fun q : I × E => shrinkMap f q - q.2) (𝓝 p) (𝓝 0) :=
      squeeze_zero_norm (norm_shrinkMap_sub_le f hC) (by
        simpa [hp] using ht.tendsto.mul_const C)
    have hv : shrinkMap f p = p.2 := by simp [shrinkMap, hp]
    rw [ContinuousAt, hv]
    simpa only [sub_add_cancel, zero_add] using hlim.add (continuous_snd.tendsto p)
  · have hp' : (p.1 : ℝ) ≠ 0 := fun h => hp (Subtype.ext h)
    have hformula : ContinuousAt (fun q : I × E =>
        (q.1 : ℝ) • f ((q.1 : ℝ)⁻¹ • q.2)) p :=
      ht.smul (f.continuous.continuousAt.comp ((ht.inv₀ hp').smul continuousAt_snd))
    apply hformula.congr
    filter_upwards [(isOpen_ne.preimage continuous_fst).mem_nhds hp] with q hq
    have hq' : q.1 ≠ 0 := hq
    simp [shrinkMap, hq']

/-- **Alexander's trick for bounded displacement.** Conjugating a homeomorphism by dilations
joins it to the identity, provided its displacement is uniformly bounded. -/
def alexanderIsotopy (f : E ≃ₜ E) (C : ℝ) (hC : ∀ x, ‖f x - x‖ ≤ C) :
    TauCeti.AmbientIsotopy E where
  toFun := shrinkMap f
  continuous_toFun := continuous_shrinkMap f hC
  map_zero_left' x := by simp [shrinkMap]
  isHomeomorph_total' := by
    have hCs : ∀ x, ‖f.symm x - x‖ ≤ C := fun x => by
      simpa only [apply_symm_apply, norm_sub_rev] using hC (f.symm x)
    let H : I × E ≃ₜ I × E :=
      { toFun := fun p => (p.1, shrinkMap f p)
        invFun := fun p => (p.1, shrinkMap f.symm p)
        left_inv := fun p => Prod.ext rfl (shrinkMap_inverse f p.1 p.2)
        right_inv := fun p => Prod.ext rfl (shrinkMap_inverse f.symm p.1 p.2)
        continuous_toFun := continuous_fst.prodMk (continuous_shrinkMap f hC)
        continuous_invFun := continuous_fst.prodMk (continuous_shrinkMap f.symm hCs) }
    exact H.isHomeomorph

/-- At positive times Alexander's isotopy is conjugation by scalar multiplication. -/
theorem alexanderIsotopy_apply_of_ne_zero (f : E ≃ₜ E) (C : ℝ)
    (hC : ∀ x, ‖f x - x‖ ≤ C) {t : I} (ht : t ≠ 0) (x : E) :
    (f.alexanderIsotopy C hC).toContinuousMap (t, x) =
      (t : ℝ) • f ((t : ℝ)⁻¹ • x) := by
  simp [alexanderIsotopy, shrinkMap, ht]

/-- The endpoint of Alexander's isotopy is the original homeomorphism. -/
@[simp 1100]
theorem alexanderIsotopy_final (f : E ≃ₜ E) (C : ℝ)
    (hC : ∀ x, ‖f x - x‖ ≤ C) (x : E) :
    (f.alexanderIsotopy C hC).final x = f x := by
  simp [TauCeti.AmbientIsotopy.final_apply, alexanderIsotopy, shrinkMap]

/-- If `f` fixes the complement of the open unit ball, its Alexander isotopy at time `t`
fixes the complement of the open ball of radius `t`. -/
theorem alexanderIsotopy_apply_of_le_norm (f : E ≃ₜ E) (C : ℝ)
    (hC : ∀ x, ‖f x - x‖ ≤ C) (hf : ∀ x, 1 ≤ ‖x‖ → f x = x)
    (t : I) {x : E} (hx : (t : ℝ) ≤ ‖x‖) :
    (f.alexanderIsotopy C hC).toContinuousMap (t, x) = x := by
  by_cases ht : t = 0
  · subst ht
    exact TauCeti.AmbientIsotopy.map_zero_left _ x
  have ht' : (t : ℝ) ≠ 0 := fun h => ht (Subtype.ext h)
  rw [alexanderIsotopy_apply_of_ne_zero f C hC ht, hf, smul_inv_smul₀ ht']
  rw [norm_smul, norm_inv, Real.norm_of_nonneg t.2.1, inv_mul_eq_div,
    le_div_iff₀ (lt_of_le_of_ne t.2.1 (Ne.symm ht')), one_mul]
  exact hx

/-- **Alexander's lemma.** A homeomorphism of the closed unit ball fixing the unit sphere is
joined to the identity through homeomorphisms of the ball fixing the sphere. -/
def alexanderIsotopyClosedBall (f : closedBall (0 : E) 1 ≃ₜ closedBall (0 : E) 1)
    (hf : ∀ x : closedBall (0 : E) 1, ‖(x : E)‖ = 1 → f x = x) :
    TauCeti.AmbientIsotopy (closedBall (0 : E) 1) :=
  let Φ := (f.extendClosedBall hf).alexanderIsotopy 2 (f.norm_extendClosedBall_sub_le hf)
  Φ.restrict _ (by
    intro t x
    have hfix {y : E} (hy : 1 ≤ ‖y‖) : Φ.toContinuousMap (t, y) = y :=
      alexanderIsotopy_apply_of_le_norm _ _ _
        (fun z hz => f.extendClosedBall_of_one_le hf hz) t (t.2.2.trans hy)
    by_cases hx : x ∈ closedBall (0 : E) 1
    · refine iff_of_true ?_ hx
      by_contra hy
      have hynorm : 1 ≤ ‖Φ.toContinuousMap (t, x)‖ := by
        exact le_of_lt (not_le.mp (fun h => hy (mem_closedBall_zero_iff.mpr h)))
      have heq := (Φ.isHomeomorph_apply t).injective (hfix hynorm)
      exact hy (heq.symm ▸ hx)
    · rw [hfix (le_of_lt (not_le.mp (fun h => hx (mem_closedBall_zero_iff.mpr h))))])

/-- The pointwise formula for the ball isotopy, read in the ambient space. -/
@[simp]
theorem coe_alexanderIsotopyClosedBall_apply
    (f : closedBall (0 : E) 1 ≃ₜ closedBall (0 : E) 1)
    (hf : ∀ x : closedBall (0 : E) 1, ‖(x : E)‖ = 1 → f x = x)
    (t : I) (x : closedBall (0 : E) 1) :
    ((f.alexanderIsotopyClosedBall hf).toContinuousMap (t, x) : E) =
      ((f.extendClosedBall hf).alexanderIsotopy 2
        (f.norm_extendClosedBall_sub_le hf)).toContinuousMap (t, x) := by
  unfold alexanderIsotopyClosedBall
  rw [TauCeti.AmbientIsotopy.coe_restrict_apply]

/-- Alexander's ball isotopy ends at the given homeomorphism. -/
@[simp 1100]
theorem alexanderIsotopyClosedBall_final
    (f : closedBall (0 : E) 1 ≃ₜ closedBall (0 : E) 1)
    (hf : ∀ x : closedBall (0 : E) 1, ‖(x : E)‖ = 1 → f x = x)
    (x : closedBall (0 : E) 1) : (f.alexanderIsotopyClosedBall hf).final x = f x := by
  apply Subtype.ext
  rw [TauCeti.AmbientIsotopy.final_apply, coe_alexanderIsotopyClosedBall_apply,
    ← TauCeti.AmbientIsotopy.final_apply, alexanderIsotopy_final, extendClosedBall_coe]

/-- Alexander's ball isotopy at time `t` fixes every point of norm at least `t`. In particular
it fixes the unit sphere throughout. -/
theorem alexanderIsotopyClosedBall_apply_of_le_norm
    (f : closedBall (0 : E) 1 ≃ₜ closedBall (0 : E) 1)
    (hf : ∀ x : closedBall (0 : E) 1, ‖(x : E)‖ = 1 → f x = x)
    (t : I) (x : closedBall (0 : E) 1) (hx : (t : ℝ) ≤ ‖(x : E)‖) :
    (f.alexanderIsotopyClosedBall hf).toContinuousMap (t, x) = x := by
  apply Subtype.ext
  rw [coe_alexanderIsotopyClosedBall_apply]
  exact alexanderIsotopy_apply_of_le_norm _ _ _
    (fun z hz => f.extendClosedBall_of_one_le hf hz) t hx

/-- Inside the shrinking ball, Alexander's isotopy is the given homeomorphism rescaled. -/
theorem coe_alexanderIsotopyClosedBall_smul
    (f : closedBall (0 : E) 1 ≃ₜ closedBall (0 : E) 1)
    (hf : ∀ x : closedBall (0 : E) 1, ‖(x : E)‖ = 1 → f x = x)
    (t : I) (x : closedBall (0 : E) 1) :
    ((f.alexanderIsotopyClosedBall hf).toContinuousMap
      (t, ⟨(t : ℝ) • (x : E), by
        rw [mem_closedBall_zero_iff, norm_smul_of_nonneg t.2.1]
        exact (mul_le_mul_of_nonneg_left
          (mem_closedBall_zero_iff.mp x.2) t.2.1).trans (by simpa using t.2.2)⟩) : E) =
      (t : ℝ) • (f x : E) := by
  rw [coe_alexanderIsotopyClosedBall_apply]
  by_cases ht : t = 0
  · subst ht
    simp
  · have ht' : (t : ℝ) ≠ 0 := fun h => ht (Subtype.ext h)
    rw [alexanderIsotopy_apply_of_ne_zero _ _ _ ht, inv_smul_smul₀ ht',
      extendClosedBall_coe]

/-- The unit sphere is fixed throughout Alexander's ball isotopy. -/
@[simp]
theorem alexanderIsotopyClosedBall_apply_of_norm_eq_one
    (f : closedBall (0 : E) 1 ≃ₜ closedBall (0 : E) 1)
    (hf : ∀ x : closedBall (0 : E) 1, ‖(x : E)‖ = 1 → f x = x)
    (t : I) (x : closedBall (0 : E) 1) (hx : ‖(x : E)‖ = 1) :
    (f.alexanderIsotopyClosedBall hf).toContinuousMap (t, x) = x :=
  f.alexanderIsotopyClosedBall_apply_of_le_norm hf t x (t.2.2.trans_eq hx.symm)

end Homeomorph

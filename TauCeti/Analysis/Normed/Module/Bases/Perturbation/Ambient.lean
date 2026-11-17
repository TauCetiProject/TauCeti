/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.Bases.Map
public import TauCeti.Analysis.Normed.Module.Bases.Basic
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Topology.Algebra.InfiniteSum.ContinuousEval

/-!
# Small perturbations in an ambient Banach space

Let `b` be a Schauder basis of a Banach space `E`, embedded isometrically into an ambient
Banach space `F` by `j`.
If the weighted error `θ = ∑' i, ‖b.coord i‖ * ‖c i - j (b i)‖` is summable and less
than one, the map sending `b i` to `c i` is an isomorphism from `E` onto the closed
span of `c`. Its norm is at most `1 + θ`, and its inverse has norm at most `(1 - θ)⁻¹`.
In particular, `c` is a basis of its closed span, even when its vectors do not lie
in the range of `j`.

The perturbing map is the inclusion plus a norm-convergent series of rank-one maps.
Only this error series is summed unconditionally: the transported basis retains its
original summation filter. Taking `E` to be the closed span of a basic sequence and
`j` its inclusion gives the ambient basic-sequence perturbation theorem.

## References

* F. Albiac and N. J. Kalton, *Topics in Banach Space Theory*, Chapter 1,
  the principle of small perturbations.
-/

public section

noncomputable section

open Filter Set Topology

namespace GeneralSchauderBasis

variable {β 𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {L : SummationFilter β} (b : GeneralSchauderBasis β 𝕜 E L)
  (j : E →ₗᵢ[𝕜] F) (c : β → F)

/-- The inclusion plus the series of rank-one errors sending `b i` to `c i`.
The evaluation laws require summability of the weighted errors. -/
def ambientPerturbationMap : E →L[𝕜] F :=
  j.toContinuousLinearMap + ∑' i, (b.coord i).smulRight (c i - j (b i))

section CompleteTarget

variable [CompleteSpace F]

/-- The perturbing map is the inclusion plus its absolutely convergent error series. -/
theorem ambientPerturbationMap_apply
    (hs : Summable (fun i ↦ ‖b.coord i‖ * ‖c i - j (b i)‖)) (x : E) :
    b.ambientPerturbationMap j c x =
      j x + ∑' i, b.coord i x • (c i - j (b i)) := by
  simp only [ambientPerturbationMap, add_apply,
    LinearIsometry.coe_toContinuousLinearMap,
    tsum_apply (b.summable_coord_smulRight (fun i ↦ c i - j (b i)) hs),
    ContinuousLinearMap.smulRight_apply]

/-- The perturbing map sends the original basis vectors to their prescribed perturbations. -/
@[simp]
theorem ambientPerturbationMap_apply_basis
    (hs : Summable (fun i ↦ ‖b.coord i‖ * ‖c i - j (b i)‖)) (i : β) :
    b.ambientPerturbationMap j c (b i) = c i := by
  simp only [ambientPerturbationMap, add_apply, LinearIsometry.coe_toContinuousLinearMap,
    b.tsum_coord_smulRight_apply_basis (fun k ↦ c k - j (b k)) hs i, add_sub_cancel]

end CompleteTarget

/-- The operator error is bounded by the sum of weighted vector errors. -/
theorem norm_ambientPerturbationMap_sub_le
    (hs : Summable (fun i ↦ ‖b.coord i‖ * ‖c i - j (b i)‖)) :
    ‖b.ambientPerturbationMap j c - j.toContinuousLinearMap‖ ≤
      ∑' i, ‖b.coord i‖ * ‖c i - j (b i)‖ := by
  simp only [ambientPerturbationMap, add_sub_cancel_left]
  exact b.norm_tsum_coord_smulRight_le (fun i ↦ c i - j (b i)) hs

/-- The perturbing operator has norm at most one plus the weighted error. -/
theorem norm_ambientPerturbationMap_le
    (hs : Summable (fun i ↦ ‖b.coord i‖ * ‖c i - j (b i)‖)) :
    ‖b.ambientPerturbationMap j c‖ ≤ 1 + ∑' i, ‖b.coord i‖ * ‖c i - j (b i)‖ := by
  calc
    ‖b.ambientPerturbationMap j c‖ ≤
        ‖j.toContinuousLinearMap‖ + ‖b.ambientPerturbationMap j c - j.toContinuousLinearMap‖ :=
      (norm_le_norm_sub_add (b.ambientPerturbationMap j c) j.toContinuousLinearMap).trans_eq
        (add_comm _ _)
    _ ≤ _ := add_le_add j.norm_toContinuousLinearMap_le
      (b.norm_ambientPerturbationMap_sub_le j c hs)

/-- The perturbing operator is bounded below by one minus the weighted error. -/
theorem mul_norm_le_norm_ambientPerturbationMap
    (hs : Summable (fun i ↦ ‖b.coord i‖ * ‖c i - j (b i)‖)) (x : E) :
    (1 - ∑' i, ‖b.coord i‖ * ‖c i - j (b i)‖) * ‖x‖ ≤
      ‖b.ambientPerturbationMap j c x‖ := by
  have herr := (b.ambientPerturbationMap j c - j.toContinuousLinearMap).le_of_opNorm_le
    (b.norm_ambientPerturbationMap_sub_le j c hs) x
  have htri := norm_le_norm_sub_add (j x) (b.ambientPerturbationMap j c x)
  simp only [sub_apply, LinearIsometry.coe_toContinuousLinearMap] at herr
  rw [norm_sub_rev] at herr
  rw [j.norm_map] at htri
  linarith

private theorem antilipschitz_ambientPerturbationMap
    (hs : Summable (fun i ↦ ‖b.coord i‖ * ‖c i - j (b i)‖))
    (hθ : (∑' i, ‖b.coord i‖ * ‖c i - j (b i)‖) < 1) :
    AntilipschitzWith ⟨(1 - ∑' i, ‖b.coord i‖ * ‖c i - j (b i)‖)⁻¹,
      inv_nonneg.2 (sub_pos.2 hθ).le⟩ (b.ambientPerturbationMap j c) := by
  apply ContinuousLinearMap.antilipschitz_of_bound
  intro x
  exact (le_inv_mul_iff₀ (sub_pos.2 hθ)).2
    (b.mul_norm_le_norm_ambientPerturbationMap j c hs x)

variable [CompleteSpace E] [CompleteSpace F] [L.NeBot]

/-- A small ambient perturbation has range exactly the closed span of its new vectors. -/
theorem range_ambientPerturbationMap
    (hs : Summable (fun i ↦ ‖b.coord i‖ * ‖c i - j (b i)‖))
    (hθ : (∑' i, ‖b.coord i‖ * ‖c i - j (b i)‖) < 1) :
    (b.ambientPerturbationMap j c).range =
      (Submodule.span 𝕜 (range c)).topologicalClosure := by
  let T := b.ambientPerturbationMap j c
  have hclosed : IsClosed (T.range : Set F) :=
    (b.antilipschitz_ambientPerturbationMap j c hs hθ).isClosed_range T.uniformContinuous
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    apply closure_mono ?_
      (image_closure_subset_closure_image (s := (Submodule.span 𝕜 (range b) : Set E))
        T.continuous ⟨x, b.dense_span x, rfl⟩)
    apply (Submodule.image_span_subset T.toLinearMap (range b) (Submodule.span 𝕜 (range c))).2
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span ⟨i, (b.ambientPerturbationMap_apply_basis j c hs i).symm⟩
  · apply Submodule.topologicalClosure_minimal _ _ hclosed
    apply Submodule.span_le.2
    rintro _ ⟨i, rfl⟩
    exact ⟨b i, b.ambientPerturbationMap_apply_basis j c hs i⟩

/-- **Ambient small perturbation theorem.** A small summable perturbation of an isometrically
embedded basis gives an isomorphism onto its new closed span, with quantitative norm bounds. -/
def ambientSmallPerturbationEquiv
    (hs : Summable (fun i ↦ ‖b.coord i‖ * ‖c i - j (b i)‖))
    (hθ : (∑' i, ‖b.coord i‖ * ‖c i - j (b i)‖) < 1) :
    E ≃L[𝕜] (Submodule.span 𝕜 (range c)).topologicalClosure :=
  ((b.ambientPerturbationMap j c).equivRange
    (b.antilipschitz_ambientPerturbationMap j c hs hθ).injective
    ((b.antilipschitz_ambientPerturbationMap j c hs hθ).isClosed_range
      (b.ambientPerturbationMap j c).uniformContinuous)).trans
    (LinearIsometryEquiv.ofEq _ _
      (b.range_ambientPerturbationMap j c hs hθ)).toContinuousLinearEquiv

/-- The closed-span equivalence is the perturbing operator with codomain restricted. -/
@[simp]
theorem coe_ambientSmallPerturbationEquiv_apply
    (hs : Summable (fun i ↦ ‖b.coord i‖ * ‖c i - j (b i)‖))
    (hθ : (∑' i, ‖b.coord i‖ * ‖c i - j (b i)‖) < 1) (x : E) :
    (b.ambientSmallPerturbationEquiv j c hs hθ x : F) = b.ambientPerturbationMap j c x := by
  simp only [ambientSmallPerturbationEquiv, ContinuousLinearEquiv.trans_apply,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    ContinuousLinearMap.coe_equivRange]
  rw [LinearIsometryEquiv.coe_ofEq_apply]
  exact ContinuousLinearMap.coe_codRestrict_apply _ _ _ _

/-- The ambient equivalence has norm at most one plus the weighted error. -/
theorem norm_ambientSmallPerturbationEquiv_le
    (hs : Summable (fun i ↦ ‖b.coord i‖ * ‖c i - j (b i)‖))
    (hθ : (∑' i, ‖b.coord i‖ * ‖c i - j (b i)‖) < 1) :
    ‖(b.ambientSmallPerturbationEquiv j c hs hθ).toContinuousLinearMap‖ ≤
      1 + ∑' i, ‖b.coord i‖ * ‖c i - j (b i)‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  simpa only [ContinuousLinearEquiv.coe_coe, ← Submodule.norm_coe,
    coe_ambientSmallPerturbationEquiv_apply] using
    (b.ambientPerturbationMap j c).le_of_opNorm_le (b.norm_ambientPerturbationMap_le j c hs) x

/-- The inverse ambient equivalence has the geometric-series bound. -/
theorem norm_ambientSmallPerturbationEquiv_symm_le
    (hs : Summable (fun i ↦ ‖b.coord i‖ * ‖c i - j (b i)‖))
    (hθ : (∑' i, ‖b.coord i‖ * ‖c i - j (b i)‖) < 1) :
    ‖(b.ambientSmallPerturbationEquiv j c hs hθ).symm.toContinuousLinearMap‖ ≤
      (1 - ∑' i, ‖b.coord i‖ * ‖c i - j (b i)‖)⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.2 (sub_pos.2 hθ).le)
  intro y
  have h := b.mul_norm_le_norm_ambientPerturbationMap j c hs
    ((b.ambientSmallPerturbationEquiv j c hs hθ).symm y)
  rw [← coe_ambientSmallPerturbationEquiv_apply b j c hs hθ,
    ContinuousLinearEquiv.apply_symm_apply, Submodule.norm_coe] at h
  exact (le_inv_mul_iff₀ (sub_pos.2 hθ)).2 h

/-- A small ambient perturbation is a basis of its closed span, with the original
summation filter. -/
def ambientPerturb
    (hs : Summable (fun i ↦ ‖b.coord i‖ * ‖c i - j (b i)‖))
    (hθ : (∑' i, ‖b.coord i‖ * ‖c i - j (b i)‖) < 1) :
    GeneralSchauderBasis β 𝕜 (Submodule.span 𝕜 (range c)).topologicalClosure L :=
  b.map (b.ambientSmallPerturbationEquiv j c hs hθ)

/-- The vectors of the perturbed closed-span basis are precisely the prescribed vectors. -/
@[simp]
theorem coe_ambientPerturb_apply
    (hs : Summable (fun i ↦ ‖b.coord i‖ * ‖c i - j (b i)‖))
    (hθ : (∑' i, ‖b.coord i‖ * ‖c i - j (b i)‖) < 1) (i : β) :
    (b.ambientPerturb j c hs hθ i : F) = c i := by
  simp only [ambientPerturb, map_apply, coe_ambientSmallPerturbationEquiv_apply,
    ambientPerturbationMap_apply_basis b j c hs]

/-- Coordinates of the ambient perturbation are the old coordinates transported by the inverse. -/
@[simp]
theorem ambientPerturb_coord_apply
    (hs : Summable (fun i ↦ ‖b.coord i‖ * ‖c i - j (b i)‖))
    (hθ : (∑' i, ‖b.coord i‖ * ‖c i - j (b i)‖) < 1) (i : β)
    (y : (Submodule.span 𝕜 (range c)).topologicalClosure) :
    (b.ambientPerturb j c hs hθ).coord i y =
      b.coord i ((b.ambientSmallPerturbationEquiv j c hs hθ).symm y) := by
  simp only [ambientPerturb, map_coord_apply]

end GeneralSchauderBasis

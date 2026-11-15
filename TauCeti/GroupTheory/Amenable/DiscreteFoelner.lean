/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Lp.BoundedContinuous
public import TauCeti.GroupTheory.Amenable.Average
public import TauCeti.GroupTheory.Amenable.Reiter
import Mathlib.Analysis.LocallyConvex.Separation
import TauCeti.Topology.Algebra.Group.UCB.Discrete

/-!
# Amenable discrete groups, Reiter's `ℓ¹` condition, and Følner sets

Let a group `G` act on `X` and let `K ⊆ G` be finite. The continuous linear operator
`TauCeti.leftTranslationSubPiLp X K` sends `p ∈ ℓ¹(X)` to the family `(L_g p - p)_{g ∈ K}` in the
sum-normed product `PiLp 1 (fun _ : K ↦ lp (fun _ : X ↦ ℝ) 1)`, whose norm is literally
`∑ g ∈ K, ‖L_g p - p‖`. On Mathlib's finitely supported probability distributions
`w : Convexity.StdSimplex ℝ X`, the vectors `leftTranslationSubPiLp X K (w.toLp 1)` form a convex
set equal to the convex hull of the point-mass differences `(δ_{g • x} - δ_x)_{g ∈ K}`, and `0`
lies in its norm closure if and only if for every `δ > 0` there is `w : StdSimplex ℝ X` with
`∑ g ∈ K, ‖L_g (w.toLp 1) - w.toLp 1‖ < δ`.

When `X` carries the discrete topology, `BoundedContinuousFunction.piLpOneDualEquiv` identifies
continuous linear functionals `Λ` on `PiLp 1 (fun _ : K ↦ lp (fun _ : X ↦ ℝ) 1)` with families of
bounded functions `f_g = (piLpOneDualEquiv ℝ K X).symm Λ g : X →ᵇ ℝ`, where
`f_g y = Λ (PiLp.single 1 g (lp.single 1 y 1))` and `‖f_g‖ ≤ ‖Λ‖`. If `0` is outside the norm
closure of `{leftTranslationSubPiLp X K (w.toLp 1) : w ∈ StdSimplex ℝ X}`, Hahn–Banach separation
yields `Λ` and `u > 0` such that

```text
u < ∑_{g ∈ K} (f_g (g • x) - f_g x)     for every x ∈ X.
```

Specializing to the left multiplication action of a discrete group `G` on itself, a left-invariant
mean on `TauCeti.UCB G` assigns mean `0` to `x ↦ ∑_{g ∈ K} (f_g (g * x) - f_g x)`, ruling out any
such strict separator and establishing **Reiter's condition** in both `ℓ¹` probability form and
coordinatewise series form. Superlevel-set averaging
(`TauCeti.hasFoelnerSets_of_forall_exists_sum_tsum_abs_sub_lt`) then produces **Følner sets**,
completing the equivalence between amenability, Reiter's condition, and Følner sets on discrete
groups.

## Main definitions

* `TauCeti.leftTranslationSubPiLp X K`: the continuous linear operator
  `p ↦ (L_g p - p)_{g ∈ K}` from `ℓ¹(X)` to `PiLp 1 (fun _ : K ↦ lp (fun _ : X ↦ ℝ) 1)`.

## Main results

* `TauCeti.norm_leftTranslationSubPiLp`:
  `‖leftTranslationSubPiLp X K p‖ = ∑ g ∈ K, ‖L_g p - p‖`.
* `TauCeti.zero_mem_closure_range_leftTranslationSubPiLp_stdSimplex_iff`: `0` lies in the norm
  closure of the probability translation differences if and only if every `δ > 0` admits
  `w : StdSimplex ℝ X` with `∑ g ∈ K, ‖L_g (w.toLp 1) - w.toLp 1‖ < δ`.
* `TauCeti.exists_pos_lt_sum_piLpOneDualEquiv_symm_of_zero_notMem_closure`: if `0` is outside that
  closure on discrete `X`, a functional `Λ` and `u > 0` give a uniform positive lower bound for
  `x ↦ ∑ g : K, (f_g (g • x) - f_g x)` where `f = (piLpOneDualEquiv ℝ K X).symm Λ`.
* `TauCeti.Amenable.exists_stdSimplex_sum_norm_leftTranslation_sub_lt` and
  `TauCeti.amenable_iff_exists_stdSimplex_sum_norm_leftTranslation_sub_lt`: Reiter's `ℓ¹`
  probability characterization of amenable discrete groups.
* `TauCeti.Amenable.exists_sum_tsum_abs_sub_lt` and
  `TauCeti.amenable_iff_exists_sum_tsum_abs_sub_lt`: Reiter's coordinatewise characterization.
* `TauCeti.Amenable.hasFoelnerSets`, `TauCeti.amenable_iff_hasFoelnerSets`, and
  `TauCeti.amenable_iff_exists_finset`: the Følner-set characterizations of amenable discrete
  groups.

## References

* B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property (T)*, Theorem G.3.1 and
  Theorem G.5.1.
* A. Garrido, *An introduction to amenable groups*, Theorem 3.6.
-/

public section

noncomputable section

open Convexity Finset Function
open scoped ENNReal BoundedContinuousFunction Pointwise symmDiff

namespace TauCeti

section MulAction

variable {G : Type*} [Group G] (X : Type*) [MulAction G X]

/-- The continuous linear operator `p ↦ (L_g p - p)_{g ∈ K}` from `ℓ¹(X)` into the sum-normed
finite product `PiLp 1 (fun _ : K ↦ lp (fun _ : X ↦ ℝ) 1)`. -/
def leftTranslationSubPiLp (K : Finset G) :
    lp (fun _ : X ↦ ℝ) 1 →L[ℝ] PiLp 1 (fun _ : K ↦ lp (fun _ : X ↦ ℝ) 1) :=
  (PiLp.continuousLinearEquiv 1 ℝ
    (fun _ : K ↦ lp (fun _ : X ↦ ℝ) 1)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun g : K ↦
      (lp.leftTranslation X 1 ℝ ℝ (g : G)).toLinearIsometry.toContinuousLinearMap -
        ContinuousLinearMap.id ℝ _)

variable {X}

/-- Evaluating `leftTranslationSubPiLp X K p` at `g : K` gives `L_g p - p`. -/
@[simp]
theorem leftTranslationSubPiLp_apply (K : Finset G) (p : lp (fun _ : X ↦ ℝ) 1) (g : K) :
    leftTranslationSubPiLp X K p g = lp.leftTranslation X 1 ℝ ℝ (g : G) p - p :=
  (rfl)

/-- The norm of `leftTranslationSubPiLp X K p` in the sum-normed product is
`∑ g ∈ K, ‖L_g p - p‖`. -/
theorem norm_leftTranslationSubPiLp (K : Finset G) (p : lp (fun _ : X ↦ ℝ) 1) :
    ‖leftTranslationSubPiLp X K p‖ = ∑ g ∈ K, ‖lp.leftTranslation X 1 ℝ ℝ g p - p‖ := by
  rw [PiLp.norm_eq_of_L1]
  simpa only [leftTranslationSubPiLp_apply] using
    (Finset.sum_coe_sort K fun g ↦ ‖lp.leftTranslation X 1 ℝ ℝ g p - p‖)

/-- The norm of `leftTranslationSubPiLp X K p` expands as
`∑ g ∈ K, ∑' x, |p (g⁻¹ • x) - p x|`. -/
theorem norm_leftTranslationSubPiLp_eq_sum_tsum (K : Finset G) (p : lp (fun _ : X ↦ ℝ) 1) :
    ‖leftTranslationSubPiLp X K p‖ = ∑ g ∈ K, ∑' x, |p (g⁻¹ • x) - p x| := by
  rw [norm_leftTranslationSubPiLp]
  refine Finset.sum_congr rfl fun g _ ↦ ?_
  simpa only [Real.norm_eq_abs] using lp.norm_leftTranslation_sub_eq_tsum g p

/-- The translation-difference vectors `leftTranslationSubPiLp X K (w.toLp 1)` for
`w : StdSimplex ℝ X` form a convex set in `PiLp 1 (fun _ : K ↦ lp (fun _ : X ↦ ℝ) 1)`. -/
theorem convex_range_leftTranslationSubPiLp_stdSimplex (K : Finset G) :
    Convex ℝ (Set.range fun w : StdSimplex ℝ X ↦ leftTranslationSubPiLp X K (w.toLp 1)) := by
  have h : (Set.range fun w : StdSimplex ℝ X ↦ leftTranslationSubPiLp X K (w.toLp 1)) =
      leftTranslationSubPiLp X K '' Set.range (StdSimplex.toLp 1) :=
    Set.range_comp (leftTranslationSubPiLp X K) (StdSimplex.toLp 1)
  rw [h]
  exact (StdSimplex.convex_range_toLp 1).linear_image (leftTranslationSubPiLp X K).toLinearMap

/-- The set of translation-difference vectors of finitely supported probabilities equals the convex
hull of the point-mass differences `(δ_{g • x} - δ_x)_{g ∈ K}`. -/
theorem range_leftTranslationSubPiLp_stdSimplex_eq_convexHull [DecidableEq X] (K : Finset G) :
    Set.range (fun w : StdSimplex ℝ X ↦ leftTranslationSubPiLp X K (w.toLp 1)) =
      convexHull ℝ (Set.range fun x : X ↦ leftTranslationSubPiLp X K (lp.single 1 x 1)) := by
  have h₁ : (Set.range fun w : StdSimplex ℝ X ↦ leftTranslationSubPiLp X K (w.toLp 1)) =
      leftTranslationSubPiLp X K '' Set.range (StdSimplex.toLp 1) :=
    Set.range_comp (leftTranslationSubPiLp X K) (StdSimplex.toLp 1)
  have h₂ : (Set.range fun x : X ↦ leftTranslationSubPiLp X K (lp.single 1 x 1)) =
      leftTranslationSubPiLp X K '' Set.range fun x : X ↦ lp.single 1 x (1 : ℝ) :=
    Set.range_comp (leftTranslationSubPiLp X K) fun x : X ↦ lp.single 1 x (1 : ℝ)
  rw [h₁, h₂, StdSimplex.range_toLp_eq_convexHull_single 1]
  exact (leftTranslationSubPiLp X K).toLinearMap.image_convexHull _

/-- Zero lies in the norm closure of `{leftTranslationSubPiLp X K (w.toLp 1) : w ∈ StdSimplex ℝ X}`
if and only if every `δ > 0` admits `w : StdSimplex ℝ X` with
`∑ g ∈ K, ‖L_g (w.toLp 1) - w.toLp 1‖ < δ`. -/
theorem zero_mem_closure_range_leftTranslationSubPiLp_stdSimplex_iff (K : Finset G) :
    0 ∈ closure (Set.range fun w : StdSimplex ℝ X ↦ leftTranslationSubPiLp X K (w.toLp 1)) ↔
      ∀ δ : ℝ, 0 < δ → ∃ w : StdSimplex ℝ X,
        ∑ g ∈ K, ‖lp.leftTranslation X 1 ℝ ℝ g (w.toLp 1) - w.toLp 1‖ < δ := by
  rw [Metric.mem_closure_iff]
  refine ⟨fun h δ hδ ↦ ?_, fun h δ hδ ↦ ?_⟩
  · obtain ⟨_, ⟨w, rfl⟩, hw⟩ := h δ hδ
    rw [dist_zero_left, norm_leftTranslationSubPiLp] at hw
    exact ⟨w, hw⟩
  · obtain ⟨w, hw⟩ := h δ hδ
    refine ⟨leftTranslationSubPiLp X K (w.toLp 1), ⟨w, rfl⟩, ?_⟩
    rwa [dist_zero_left, norm_leftTranslationSubPiLp]

/-- Existence of `w : StdSimplex ℝ X` with `∑ g ∈ K, ‖L_g (w.toLp 1) - w.toLp 1‖ < δ` is
equivalent to existence of a nonnegative finitely supported function `p : X → ℝ` with
`∑' x, p x = 1` and `∑ g ∈ K, ∑' x, |p (g⁻¹ • x) - p x| < δ`. -/
theorem exists_stdSimplex_sum_norm_leftTranslation_sub_lt_iff (K : Finset G) (δ : ℝ) :
    (∃ w : StdSimplex ℝ X,
      ∑ g ∈ K, ‖lp.leftTranslation X 1 ℝ ℝ g (w.toLp 1) - w.toLp 1‖ < δ) ↔
    ∃ p : X → ℝ, 0 ≤ p ∧ p.HasFiniteSupport ∧ ∑' x, p x = 1 ∧
      ∑ g ∈ K, ∑' x, |p (g⁻¹ • x) - p x| < δ := by
  refine ⟨?_, ?_⟩
  · rintro ⟨w, hw⟩
    refine ⟨⇑(w.toLp 1), w.toLp_nonneg 1, w.hasFiniteSupport_toLp 1, w.tsum_toLp 1, ?_⟩
    rwa [← norm_leftTranslationSubPiLp, norm_leftTranslationSubPiLp_eq_sum_tsum] at hw
  · rintro ⟨p, hp0, hpfin, hpsum, hp⟩
    obtain ⟨w, hw⟩ := (StdSimplex.mem_range_toLp_iff (p := 1)
      (f := ⟨p, hpfin.memℓp 1⟩)).mpr ⟨hp0, hpfin, hpsum⟩
    refine ⟨w, ?_⟩
    rwa [← norm_leftTranslationSubPiLp, hw, norm_leftTranslationSubPiLp_eq_sum_tsum]

section DiscreteSeparation

variable [TopologicalSpace X] [DiscreteTopology X]

/-- On a discrete space `X`, evaluating a continuous linear functional `Λ` on
`leftTranslationSubPiLp X K p` pairs `p` against the differences `f_g (g • ·) - f_g`, where
`f = (BoundedContinuousFunction.piLpOneDualEquiv ℝ K X).symm Λ`. -/
theorem apply_leftTranslationSubPiLp (K : Finset G)
    (Λ : StrongDual ℝ (PiLp 1 fun _ : K ↦ lp (fun _ : X ↦ ℝ) 1)) (p : lp (fun _ : X ↦ ℝ) 1) :
    Λ (leftTranslationSubPiLp X K p) =
      ∑ g : K, BoundedContinuousFunction.toLpOneDual ℝ X
        (((BoundedContinuousFunction.piLpOneDualEquiv ℝ K X).symm Λ g).compContinuous
          ⟨((g : G) • ·), continuous_of_discreteTopology⟩ -
          (BoundedContinuousFunction.piLpOneDualEquiv ℝ K X).symm Λ g) p := by
  have : ContinuousConstSMul G X := ⟨fun _ ↦ continuous_of_discreteTopology⟩
  conv_lhs => rw [← (BoundedContinuousFunction.piLpOneDualEquiv ℝ K X).apply_symm_apply Λ]
  rw [BoundedContinuousFunction.piLpOneDualEquiv_apply]
  refine Finset.sum_congr rfl fun g _ ↦ ?_
  rw [leftTranslationSubPiLp_apply, BoundedContinuousFunction.toLpOneDual_leftTranslation_sub]

/-- On a discrete space `X`, evaluating `Λ` at a point-mass translation difference
`leftTranslationSubPiLp X K (lp.single 1 x 1)` gives `∑ g : K, (f_g (g • x) - f_g x)`, where
`f = (BoundedContinuousFunction.piLpOneDualEquiv ℝ K X).symm Λ`. -/
theorem apply_leftTranslationSubPiLp_single [DecidableEq X] (K : Finset G)
    (Λ : StrongDual ℝ (PiLp 1 fun _ : K ↦ lp (fun _ : X ↦ ℝ) 1)) (x : X) :
    Λ (leftTranslationSubPiLp X K (lp.single 1 x 1)) =
      ∑ g : K, ((BoundedContinuousFunction.piLpOneDualEquiv ℝ K X).symm Λ g ((g : G) • x) -
        (BoundedContinuousFunction.piLpOneDualEquiv ℝ K X).symm Λ g x) := by
  rw [apply_leftTranslationSubPiLp]
  refine Finset.sum_congr rfl fun g _ ↦ ?_
  rw [BoundedContinuousFunction.toLpOneDual_apply_single]
  simp

variable (X) in
/-- **Hahn–Banach separation for translation differences of probabilities.** On a discrete `G`-set
`X`, if `0` does not lie in the norm closure of
`{leftTranslationSubPiLp X K (w.toLp 1) : w ∈ StdSimplex ℝ X}`, then there exist a continuous
linear functional `Λ` on `PiLp 1 (fun _ : K ↦ lp (fun _ : X ↦ ℝ) 1)` and `u > 0` such that the
bounded functions `f_g = (piLpOneDualEquiv ℝ K X).symm Λ g` satisfy
`u < ∑ g : K, (f_g (g • x) - f_g x)` for every `x : X`. -/
theorem exists_pos_lt_sum_piLpOneDualEquiv_symm_of_zero_notMem_closure (K : Finset G)
    (h : 0 ∉ closure (Set.range fun w : StdSimplex ℝ X ↦
      leftTranslationSubPiLp X K (w.toLp 1))) :
    ∃ (Λ : StrongDual ℝ (PiLp 1 fun _ : K ↦ lp (fun _ : X ↦ ℝ) 1)) (u : ℝ),
      0 < u ∧ ∀ x : X, u < ∑ g : K,
        ((BoundedContinuousFunction.piLpOneDualEquiv ℝ K X).symm Λ g ((g : G) • x) -
          (BoundedContinuousFunction.piLpOneDualEquiv ℝ K X).symm Λ g x) := by
  classical
  obtain ⟨Λ, u, hu0, hΛ⟩ := geometric_hahn_banach_point_closed
    (convex_range_leftTranslationSubPiLp_stdSimplex K).closure isClosed_closure h
  rw [map_zero] at hu0
  refine ⟨Λ, u, hu0, fun x ↦ ?_⟩
  rw [← apply_leftTranslationSubPiLp_single]
  exact hΛ _ (subset_closure ⟨StdSimplex.single x, by simp⟩)

end DiscreteSeparation

end MulAction

section DiscreteGroup

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- For an amenable discrete group `G` and finite `K ⊆ G`, `0` lies in the norm closure of
`{leftTranslationSubPiLp G K (w.toLp 1) : w ∈ StdSimplex ℝ G}` in the sum-normed product
`PiLp 1 (fun _ : K ↦ lp (fun _ : G ↦ ℝ) 1)`. -/
theorem Amenable.zero_mem_closure_range_leftTranslationSubPiLp_stdSimplex [DiscreteTopology G]
    [Amenable G] (K : Finset G) :
    0 ∈ closure (Set.range fun w : StdSimplex ℝ G ↦ leftTranslationSubPiLp G K (w.toLp 1)) := by
  by_contra h
  obtain ⟨Λ, u, hu0, hu⟩ := exists_pos_lt_sum_piLpOneDualEquiv_symm_of_zero_notMem_closure G K h
  let F (g : K) : UCB G :=
    (UCB.discreteAlgEquiv G).symm ((BoundedContinuousFunction.piLpOneDualEquiv ℝ K G).symm Λ g)
  obtain ⟨m, hm⟩ := Amenable.exists_isLeftInvariant (G := G)
  have h0 : m (∑ g : K, (UCB.leftTranslation (g : G)⁻¹ (F g) - F g)) = 0 := by
    simp only [map_sum, map_sub, hm.apply_leftTranslation, sub_self, sum_const_zero]
  -- `map_inv` would rewrite `UCB.leftTranslation g⁻¹` to `(UCB.leftTranslation g).symm`.
  have hum : u ≤ m (∑ g : K, (UCB.leftTranslation (g : G)⁻¹ (F g) - F g)) :=
    m.le_apply_of_forall_le fun x ↦ by
      simpa [F, -map_inv] using (hu x).le
  linarith

/-- **Reiter's condition (`ℓ¹` probability form).** In an amenable discrete group, for every finite
`K ⊆ G` and `δ > 0` there is a finitely supported probability distribution `w : StdSimplex ℝ G`
with `∑ g ∈ K, ‖L_g (w.toLp 1) - w.toLp 1‖ < δ`. -/
theorem Amenable.exists_stdSimplex_sum_norm_leftTranslation_sub_lt [DiscreteTopology G]
    [Amenable G] (K : Finset G) {δ : ℝ} (hδ : 0 < δ) :
    ∃ w : StdSimplex ℝ G,
      ∑ g ∈ K, ‖lp.leftTranslation G 1 ℝ ℝ g (w.toLp 1) - w.toLp 1‖ < δ :=
  (zero_mem_closure_range_leftTranslationSubPiLp_stdSimplex_iff K).mp
    (Amenable.zero_mem_closure_range_leftTranslationSubPiLp_stdSimplex K) δ hδ

/-- **Reiter's condition.** In an amenable discrete group, for every finite `K` and `ε > 0` there
is a finitely supported probability density `p` with `∑_{g ∈ K} ∑_x |p (g⁻¹ x) - p x| < ε`. -/
theorem Amenable.exists_sum_tsum_abs_sub_lt [DiscreteTopology G] [Amenable G] (K : Finset G)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ p : G → ℝ, 0 ≤ p ∧ p.HasFiniteSupport ∧ ∑' x, p x = 1 ∧
      ∑ g ∈ K, ∑' x, |p (g⁻¹ * x) - p x| < ε := by
  simpa only [smul_eq_mul] using
    (exists_stdSimplex_sum_norm_leftTranslation_sub_lt_iff K ε).mp
      (Amenable.exists_stdSimplex_sum_norm_leftTranslation_sub_lt K hε)

/-- A discrete group is amenable exactly when it satisfies **Reiter's condition**: for every
finite `K` and `ε > 0` there is a finitely supported probability density `p` with
`∑_{g ∈ K} ∑_x |p (g⁻¹ x) - p x| < ε`. -/
theorem amenable_iff_exists_sum_tsum_abs_sub_lt [DiscreteTopology G] :
    Amenable G ↔ ∀ K : Finset G, ∀ ε : ℝ, 0 < ε →
      ∃ p : G → ℝ, 0 ≤ p ∧ p.HasFiniteSupport ∧ ∑' x, p x = 1 ∧
        ∑ g ∈ K, ∑' x, |p (g⁻¹ * x) - p x| < ε :=
  ⟨fun _ K _ hε ↦ Amenable.exists_sum_tsum_abs_sub_lt K hε,
    fun h ↦ .of_hasFoelnerSets (hasFoelnerSets_of_forall_exists_sum_tsum_abs_sub_lt h)⟩

/-- A discrete group is amenable if and only if for every finite `K ⊆ G` and `δ > 0` there is a
finitely supported probability distribution `w : StdSimplex ℝ G` with
`∑ g ∈ K, ‖L_g (w.toLp 1) - w.toLp 1‖ < δ`. -/
theorem amenable_iff_exists_stdSimplex_sum_norm_leftTranslation_sub_lt [DiscreteTopology G] :
    Amenable G ↔ ∀ K : Finset G, ∀ δ : ℝ, 0 < δ →
      ∃ w : StdSimplex ℝ G,
        ∑ g ∈ K, ‖lp.leftTranslation G 1 ℝ ℝ g (w.toLp 1) - w.toLp 1‖ < δ := by
  simp only [amenable_iff_exists_sum_tsum_abs_sub_lt,
    exists_stdSimplex_sum_norm_leftTranslation_sub_lt_iff, smul_eq_mul]

/-- A discrete group is amenable if and only if for every finite `K ⊆ G`, zero lies in the norm
closure of `{leftTranslationSubPiLp G K (w.toLp 1) : w ∈ StdSimplex ℝ G}` in the sum-normed product
`PiLp 1 (fun _ : K ↦ lp (fun _ : G ↦ ℝ) 1)`. -/
theorem amenable_iff_zero_mem_closure_range_leftTranslationSubPiLp_stdSimplex
    [DiscreteTopology G] :
    Amenable G ↔ ∀ K : Finset G,
      0 ∈ closure (Set.range fun w : StdSimplex ℝ G ↦
        leftTranslationSubPiLp G K (w.toLp 1)) := by
  simp only [zero_mem_closure_range_leftTranslationSubPiLp_stdSimplex_iff,
    amenable_iff_exists_stdSimplex_sum_norm_leftTranslation_sub_lt]

/-- An amenable discrete group has Følner sets. -/
theorem Amenable.hasFoelnerSets [DiscreteTopology G] [Amenable G] : HasFoelnerSets G :=
  hasFoelnerSets_of_forall_exists_sum_tsum_abs_sub_lt fun K _ hε ↦
    Amenable.exists_sum_tsum_abs_sub_lt K hε

/-- A discrete group is amenable exactly when it has Følner sets. -/
theorem amenable_iff_hasFoelnerSets [DiscreteTopology G] : Amenable G ↔ HasFoelnerSets G :=
  ⟨fun _ ↦ Amenable.hasFoelnerSets, .of_hasFoelnerSets⟩

/-- A discrete group is amenable exactly when for every finite `K ⊆ G` and every `ε > 0` there is
a finite nonempty `F ⊆ G` with `|gF △ F| < ε · |F|` for all `g ∈ K`. -/
theorem amenable_iff_exists_finset [DiscreteTopology G] [DecidableEq G] :
    Amenable G ↔ ∀ K : Finset G, ∀ ε : ℝ, 0 < ε →
      ∃ F : Finset G, F.Nonempty ∧ ∀ g ∈ K, (#((g • F) ∆ F) : ℝ) < ε * #F := by
  rw [amenable_iff_hasFoelnerSets, hasFoelnerSets_iff]

end DiscreteGroup

end TauCeti

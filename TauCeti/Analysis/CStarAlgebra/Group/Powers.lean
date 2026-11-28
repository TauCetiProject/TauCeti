/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.FreeGroup.Reduce
public import Mathlib.RingTheory.SimpleRing.Defs
public import TauCeti.Analysis.CStarAlgebra.Group.Basic
public import TauCeti.Analysis.CStarAlgebra.Unitary.Average
public import TauCeti.Analysis.InnerProductSpace.Projection.Averaging
public import TauCeti.Analysis.Normed.Lp.Diagonal.Indicator
public import TauCeti.Analysis.Normed.Lp.LeftTranslation
public import TauCeti.GroupTheory.PowersProperty
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.RingTheory.SimpleRing.Congr
import TauCeti.Analysis.CStarAlgebra.Basic
import TauCeti.Analysis.CStarAlgebra.Ideal
import TauCeti.Analysis.Normed.Operator.LinearIsometry
import TauCeti.GroupTheory.FreeGroup.PowersPartition
import TauCeti.Topology.Algebra.Ring.TwoSidedIdeal

/-!
# Powers averaging, simplicity, and uniqueness of the trace

For a group `Γ` with measurable multiplication and measurable singletons on its counting-measure
space (in particular any discrete group `[DiscreteMeasurableSpace Γ]`), we prove Powers's
averaging estimate in `TauCeti.reducedGroupCStarAlgebra Γ` and deduce simplicity and uniqueness
of the canonical tracial state whenever `TauCeti.HasPowersProperty Γ` holds:

* **Zero-compression averaging**: transferring along `(MeasureTheory.L2.countHilbertBasis ℂ Γ).repr`
  to `ℓ²(Γ, ℂ)` identifies left regular unitaries with `lp.leftTranslation 2 ℂ`. On the
  complementary projections `1 - P j` onto `ℓ²((γ j • ·) '' D)ᶜ`, any finite linear combination
  supported on `F ⊆ Γ \ {1}` has vanishing compression after conjugation by `λ (γ j)`, yielding
  the norm bound `2 * ‖x‖ / √N` (`TauCeti.norm_unitaryConjAverage_sum_le_of_disjoint`).
* **Simplicity and unique trace**: approximating elements of `reducedGroupCStarAlgebra Γ` by the
  dense image of `MonoidAlgebra ℂ Γ` shows that `τ(x) • 1` lies in the norm closure of the convex
  hull of unitary conjugates of `x`
  (`TauCeti.reducedGroupCStarAlgebraTrace_smul_one_mem_closure_convexHull`).
  Consequently, whenever `HasPowersProperty Γ` holds, `reducedGroupCStarAlgebra Γ` is a simple
  ring (`TauCeti.isSimpleRing_reducedGroupCStarAlgebra_of_hasPowersProperty`) and
  `reducedGroupCStarAlgebraTrace Γ` is the unique continuous unital tracial linear functional
  (`TauCeti.eq_reducedGroupCStarAlgebraTrace_of_hasPowersProperty`,
  `TauCeti.eq_reducedGroupCStarAlgebraTracePositive_of_hasPowersProperty`, and
  `TauCeti.tracialStates_reducedGroupCStarAlgebra_eq_singleton`).
* **Free groups**: transferring along `TauCeti.reducedGroupCStarAlgebraEquivOfApply` and
  specializing via `FreeGroup.hasPowersProperty_of_ne` gives
  `TauCeti.reducedFreeGroup_isSimpleRing` and `TauCeti.reducedFreeGroup_trace_unique`.

## References

* R. T. Powers, *Simplicity of the C*-algebra associated with the free group on two generators*,
  Duke Math. J. 42 (1975), 151–156.
* P. de la Harpe, *On simplicity of reduced C*-algebras of groups*, Bull. Lond. Math. Soc. 39
  (2007), 1–26, Definition 9, Theorem 14, and p. 19.
-/

public section

noncomputable section

open MeasureTheory
open scoped InnerProductSpace ComplexOrder ENNReal lp

namespace TauCeti

section Averaging

variable {Γ : Type*} [Group Γ]

/-- **Zero compression on the complement of `γ • D`.** When `C ⊔ D = univ` is a partition of `Γ`
with `Disjoint ((f * ·) '' C) C`, conjugating left translation by `f` with left translation by
`g` has vanishing compression onto the complement of `(g * ·) '' D`. -/
theorem compression_sub_indicatorCLM_leftTranslation_eq_zero {𝕜 : Type*} [RCLike 𝕜]
    {C D : Set Γ} (hCDU : C ∪ D = Set.univ) {f : Γ}
    (hfC : Disjoint ((fun x : Γ ↦ f * x) '' C) C) (g : Γ) :
    (1 - lp.indicatorCLM 2 𝕜 ((fun x : Γ ↦ g * x) '' D)) *
        ((lp.leftTranslation 2 𝕜 (X := Γ) (E := 𝕜) g :
            lp (fun _ : Γ ↦ 𝕜) 2 →L[𝕜] lp (fun _ : Γ ↦ 𝕜) 2) *
          (lp.leftTranslation 2 𝕜 (X := Γ) (E := 𝕜) f :
            lp (fun _ : Γ ↦ 𝕜) 2 →L[𝕜] lp (fun _ : Γ ↦ 𝕜) 2) *
          star (lp.leftTranslation 2 𝕜 (X := Γ) (E := 𝕜) g :
            lp (fun _ : Γ ↦ 𝕜) 2 →L[𝕜] lp (fun _ : Γ ↦ 𝕜) 2)) *
        (1 - lp.indicatorCLM 2 𝕜 ((fun x : Γ ↦ g * x) '' D)) = 0 := by
  set S : Set Γ := (fun x : Γ ↦ g * x) '' D
  rw [← lp.indicatorCLM_compl, lp.star_coe_leftTranslation, ← lp.coe_leftTranslation_mul,
    ← lp.coe_leftTranslation_mul]
  ext ξ t
  simp only [mul_apply_eq_comp, zero_apply, lp.coeFn_zero, Pi.zero_apply, lp.indicatorCLM_apply]
  by_cases ht : t ∈ Sᶜ
  · rw [Set.indicator_of_mem ht, LinearIsometryEquiv.coe_coe'', lp.leftTranslation_apply,
      smul_eq_mul]
    have hgtD : g⁻¹ * t ∉ D := fun hmem ↦ ht ⟨g⁻¹ * t, hmem, mul_inv_cancel_left g t⟩
    have hgtC : g⁻¹ * t ∈ C := (hCDU.symm ▸ Set.mem_univ _).resolve_right hgtD
    have hfc : f⁻¹ * (g⁻¹ * t) ∉ C := fun hmem ↦
      Set.disjoint_left.1 hfC ⟨f⁻¹ * (g⁻¹ * t), hmem, mul_inv_cancel_left f _⟩ hgtC
    have hfD : f⁻¹ * (g⁻¹ * t) ∈ D := (hCDU.symm ▸ Set.mem_univ _).resolve_left hfc
    have harg : (g * f * g⁻¹)⁻¹ * t ∈ S := by
      refine ⟨f⁻¹ * (g⁻¹ * t), hfD, ?_⟩
      group
    rw [lp.indicatorCLM_apply]
    exact Set.indicator_of_notMem (Set.notMem_compl_iff.2 harg) _
  · exact Set.indicator_of_notMem ht _

variable [MeasurableSpace Γ] [MeasurableMul Γ]

private theorem exists_monoidAlgebra_norm_sub_lt (x : reducedGroupCStarAlgebra Γ) {δ : ℝ}
    (hδ : 0 < δ) :
    ∃ f : MonoidAlgebra ℂ Γ, ‖x - groupAlgebraToReducedGroupCStarAlgebra Γ f‖ < δ := by
  obtain ⟨f, hdist⟩ :=
    Metric.mem_closure_range_iff.1 (denseRange_groupAlgebraToReducedGroupCStarAlgebra Γ x) δ hδ
  refine ⟨f, ?_⟩
  rwa [dist_eq_norm] at hdist

variable [MeasurableSingletonClass Γ]

/-- **Powers's operator-norm averaging bound.** For a finite sum
`x = ∑ f ∈ F, c f • leftRegularUnitary Γ f` with `F` disjoint from `{1}`, a Powers partition
`(C, D, γ)` yields `‖unitaryConjAverage (fun j ↦ leftRegularUnitary Γ (γ j)) x‖ ≤ 2 * ‖x‖ / √N`.
-/
theorem norm_unitaryConjAverage_sum_le_of_disjoint
    {F : Finset Γ} {C D : Set Γ} {N : ℕ} {γ : Fin N → Γ}
    (hCDU : C ∪ D = Set.univ)
    (hfC : ∀ f ∈ F, Disjoint ((fun x : Γ ↦ f * x) '' C) C)
    (hγD : Pairwise fun i j : Fin N ↦
      Disjoint ((fun x : Γ ↦ γ i * x) '' D) ((fun x : Γ ↦ γ j * x) '' D))
    (c : Γ → ℂ) :
    ‖unitaryConjAverage (fun j ↦ leftRegularUnitary Γ (γ j))
        (∑ f ∈ F, c f • (leftRegularUnitary Γ f : reducedGroupCStarAlgebra Γ))‖ ≤
      2 * ‖∑ f ∈ F, c f • (leftRegularUnitary Γ f : reducedGroupCStarAlgebra Γ)‖ /
        Real.sqrt N := by
  let xlp : lp (fun _ : Γ ↦ ℂ) 2 →L[ℂ] lp (fun _ : Γ ↦ ℂ) 2 :=
    ∑ f ∈ F, c f • (lp.leftTranslation 2 ℂ (X := Γ) (E := ℂ) f :
      lp (fun _ : Γ ↦ ℂ) 2 →L[ℂ] lp (fun _ : Γ ↦ ℂ) 2)
  let P : Fin N → (lp (fun _ : Γ ↦ ℂ) 2 →L[ℂ] lp (fun _ : Γ ↦ ℂ) 2) :=
    fun j ↦ lp.indicatorCLM 2 ℂ ((fun y : Γ ↦ γ j * y) '' D)
  let U : Fin N → unitary (lp (fun _ : Γ ↦ ℂ) 2 →L[ℂ] lp (fun _ : Γ ↦ ℂ) 2) :=
    fun j ↦ lp.leftTranslationUnitary (γ j)
  have hzero : ∀ j ∈ (Finset.univ : Finset (Fin N)),
      (1 - P j) * ((U j : lp (fun _ : Γ ↦ ℂ) 2 →L[ℂ] lp (fun _ : Γ ↦ ℂ) 2) * xlp *
        star (U j : lp (fun _ : Γ ↦ ℂ) 2 →L[ℂ] lp (fun _ : Γ ↦ ℂ) 2)) * (1 - P j) = 0 := by
    intro j _
    simp only [xlp, U, lp.coe_leftTranslationUnitary, Finset.mul_sum, Finset.sum_mul,
      mul_smul_comm, smul_mul_assoc]
    exact Finset.sum_eq_zero fun f hf ↦ by
      rw [compression_sub_indicatorCLM_leftTranslation_eq_zero (𝕜 := ℂ) hCDU (hfC f hf) (γ j)]
      ext; simp
  have hbound :=
    ContinuousLinearMap.norm_average_unitary_conj_le_two_mul_div_sqrt_card_of_compression_eq_zero
      xlp U P Finset.univ
      (fun j _ ↦ lp.isStarProjection_indicatorCLM ℂ _)
      (fun i _ j _ hij ↦ lp.indicatorCLM_mul_of_disjoint (hγD hij))
      hzero
  have hnorm_conj (M : Lp ℂ 2 (Measure.count : Measure Γ) →L[ℂ]
      Lp ℂ 2 (Measure.count : Measure Γ)) :
      ‖(L2.countHilbertBasis ℂ Γ).repr.conjStarAlgEquiv M‖ = ‖M‖ :=
    (L2.countHilbertBasis ℂ Γ).repr.norm_conjContinuousAlgEquiv_apply M
  have hlhs :
      ‖unitaryConjAverage (fun j ↦ leftRegularUnitary Γ (γ j))
          (∑ f ∈ F, c f • (leftRegularUnitary Γ f : reducedGroupCStarAlgebra Γ))‖ =
        ‖((Finset.univ : Finset (Fin N)).card : ℂ)⁻¹ •
            ∑ j : Fin N, (U j : _ →L[ℂ] _) * xlp * star (U j : _ →L[ℂ] _)‖ := by
    rw [AddSubgroupClass.coe_norm, ← hnorm_conj, unitaryConjAverage_apply]
    congr 1
    simp only [SetLike.val_smul, AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul,
      StarMemClass.coe_star, map_smul, map_sum, map_mul, map_star, coe_leftRegularUnitary,
      Measure.countHilbertBasis_conjStarAlgEquiv_leftRegular, xlp, U, lp.coe_leftTranslationUnitary,
      Finset.card_univ, Fintype.card_fin]
  have hrhs : ‖∑ f ∈ F, c f • (leftRegularUnitary Γ f : reducedGroupCStarAlgebra Γ)‖ = ‖xlp‖ := by
    rw [AddSubgroupClass.coe_norm, ← hnorm_conj,
      countHilbertBasis_conjStarAlgEquiv_sum_leftRegularUnitary]
  rw [hlhs, hrhs]
  simpa only [Finset.card_univ, Fintype.card_fin] using hbound

private theorem monoidAlgebra_sub_reducedGroupCStarAlgebraTrace_eq [DecidableEq Γ] {F : Finset Γ}
    (hF : ∀ f ∈ F, f ≠ 1) (f : MonoidAlgebra ℂ Γ) (hfF : f.coeff.support.erase 1 ⊆ F) :
    groupAlgebraToReducedGroupCStarAlgebra Γ f -
        reducedGroupCStarAlgebraTrace Γ (groupAlgebraToReducedGroupCStarAlgebra Γ f) • 1 =
      ∑ g ∈ F, f.coeff g • (leftRegularUnitary Γ g : reducedGroupCStarAlgebra Γ) := by
  have hsum_F :
      ∑ g ∈ F, f.coeff g • (leftRegularUnitary Γ g : reducedGroupCStarAlgebra Γ) =
        ∑ g ∈ f.coeff.support.erase 1,
          f.coeff g • (leftRegularUnitary Γ g : reducedGroupCStarAlgebra Γ) := by
    refine (Finset.sum_subset hfF fun g hgF hgnot ↦ ?_).symm
    have hnot : g ∉ f.coeff.support := fun hmem ↦ hgnot (Finset.mem_erase.2 ⟨hF g hgF, hmem⟩)
    simp [Finsupp.notMem_support_iff.1 hnot]
  rw [reducedGroupCStarAlgebraTrace_groupAlgebraToReducedGroupCStarAlgebra,
    groupAlgebraToReducedGroupCStarAlgebra_eq_sum, hsum_F]
  by_cases h1 : (1 : Γ) ∈ f.coeff.support
  · rw [← Finset.add_sum_erase f.coeff.support
      (fun g ↦ f.coeff g • (leftRegularUnitary Γ g : reducedGroupCStarAlgebra Γ)) h1,
      map_one (leftRegularUnitary Γ), OneMemClass.coe_one, add_sub_cancel_left]
  · rw [Finsupp.notMem_support_iff.1 h1, zero_smul ℂ (1 : reducedGroupCStarAlgebra Γ), sub_zero,
      Finset.erase_eq_of_notMem h1]

private theorem norm_unitaryConjAverage_sub_reducedGroupCStarAlgebraTrace_smul_one_lt_of_approx
    {N : ℕ} (hN : 0 < N) (γ : Fin N → Γ) {x y : reducedGroupCStarAlgebra Γ} {ε : ℝ}
    (hxy : ‖x - y‖ < ε / 3)
    (hMy : ‖unitaryConjAverage (fun j ↦ leftRegularUnitary Γ (γ j))
        (y - reducedGroupCStarAlgebraTrace Γ y • 1)‖ < ε / 3) :
    ‖unitaryConjAverage (fun j ↦ leftRegularUnitary Γ (γ j)) x -
        reducedGroupCStarAlgebraTrace Γ x • 1‖ < ε := by
  let u : Fin N → unitary (reducedGroupCStarAlgebra Γ) := fun j ↦ leftRegularUnitary Γ (γ j)
  have hdecomp : unitaryConjAverage u x - reducedGroupCStarAlgebraTrace Γ x • 1 =
      unitaryConjAverage u (x - y) +
        unitaryConjAverage u (y - reducedGroupCStarAlgebraTrace Γ y • 1) +
        (reducedGroupCStarAlgebraTrace Γ y - reducedGroupCStarAlgebraTrace Γ x) • 1 := by
    rw [map_sub, map_sub, map_smul, unitaryConjAverage_one hN u, sub_smul]
    abel
  have hnorm1 : ‖unitaryConjAverage u (x - y)‖ < ε / 3 :=
    (norm_unitaryConjAverage_apply_le hN u (x - y)).trans_lt hxy
  have hnorm3 : ‖(reducedGroupCStarAlgebraTrace Γ y - reducedGroupCStarAlgebraTrace Γ x) •
      (1 : reducedGroupCStarAlgebra Γ)‖ < ε / 3 := by
    refine (norm_smul_le _ _).trans_lt ?_
    refine (mul_le_of_le_one_right (norm_nonneg _) CStarRing.norm_one_le).trans_lt ?_
    rw [← map_sub]
    exact (norm_reducedGroupCStarAlgebraTrace_apply_le _).trans_lt (by rwa [norm_sub_rev])
  rw [hdecomp]
  exact norm_add₃_le.trans_lt (by linarith)

private theorem norm_unitaryConjAverage_monoidAlgebra_sub_reducedGroupCStarAlgebraTrace_smul_one_le
    [DecidableEq Γ]
    {F : Finset Γ} (hF : ∀ f ∈ F, f ≠ 1) {C D : Set Γ} {N : ℕ} {γ : Fin N → Γ}
    (hCDU : C ∪ D = Set.univ) (hfC : ∀ f ∈ F, Disjoint ((fun x : Γ ↦ f * x) '' C) C)
    (hγD : Pairwise fun i j : Fin N ↦
      Disjoint ((fun x : Γ ↦ γ i * x) '' D) ((fun x : Γ ↦ γ j * x) '' D))
    (f : MonoidAlgebra ℂ Γ) (hfF : f.coeff.support.erase 1 ⊆ F) :
    let y := groupAlgebraToReducedGroupCStarAlgebra Γ f
    ‖unitaryConjAverage (fun j ↦ leftRegularUnitary Γ (γ j))
        (y - reducedGroupCStarAlgebraTrace Γ y • 1)‖ ≤
      2 * ‖y - reducedGroupCStarAlgebraTrace Γ y • 1‖ / Real.sqrt N := by
  intro y
  rw [monoidAlgebra_sub_reducedGroupCStarAlgebraTrace_eq hF f hfF]
  exact norm_unitaryConjAverage_sum_le_of_disjoint hCDU hfC hγD (fun g ↦ f.coeff g)

/-- **Simultaneous Powers averaging in `reducedGroupCStarAlgebra Γ`.** Given a finite family `x`
and `ε > 0`, when `Γ` has the Powers property there exist `N > 0` and `γ : Fin N → Γ` whose
conjugate average brings every `x i` (`i ∈ s`) within `ε` of
`reducedGroupCStarAlgebraTrace Γ (x i) • 1`. -/
theorem exists_forall_norm_unitaryConjAverage_sub_reducedGroupCStarAlgebraTrace_smul_one_lt
    (hΓ : HasPowersProperty Γ)
    {ι : Type*} (s : Finset ι) (x : ι → reducedGroupCStarAlgebra Γ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (N : ℕ) (γ : Fin N → Γ), 0 < N ∧ ∀ i ∈ s,
      ‖unitaryConjAverage (fun j ↦ leftRegularUnitary Γ (γ j)) (x i) -
          reducedGroupCStarAlgebraTrace Γ (x i) • 1‖ < ε := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | hs
  · exact ⟨1, fun _ ↦ 1, zero_lt_one, fun _ hi ↦ absurd hi (Finset.notMem_empty _)⟩
  have happrox (i : ι) :
      ∃ f : MonoidAlgebra ℂ Γ, ‖x i - groupAlgebraToReducedGroupCStarAlgebra Γ f‖ < ε / 3 :=
    exists_monoidAlgebra_norm_sub_lt (x i) (by positivity)
  choose f hf using happrox
  let y : ι → reducedGroupCStarAlgebra Γ := fun i ↦ groupAlgebraToReducedGroupCStarAlgebra Γ (f i)
  let F : Finset Γ := s.biUnion fun i ↦ (f i).coeff.support.erase 1
  have hF : ∀ g ∈ F, g ≠ 1 := fun g hg ↦
    let ⟨_, _, hgi⟩ := Finset.mem_biUnion.1 hg
    Finset.ne_of_mem_erase hgi
  let R : ℝ := s.sup' hs fun i ↦ ‖y i - reducedGroupCStarAlgebraTrace Γ (y i) • 1‖
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt ((6 * R / ε) ^ 2)
  let N : ℕ := max 1 N₀
  have hN_pos : 0 < N := lt_of_lt_of_le zero_lt_one (le_max_left 1 N₀)
  have hN_sqrt : 6 * R / ε < Real.sqrt N :=
    Real.lt_sqrt_of_sq_lt (hN₀.trans_le (Nat.cast_le.2 (le_max_right 1 N₀)))
  obtain ⟨C, D, γ, -, hCDU, hfC, hγD⟩ := hasPowersProperty_def.1 hΓ F hF N
  refine ⟨N, γ, hN_pos, fun i hi ↦ ?_⟩
  have hR : ‖y i - reducedGroupCStarAlgebraTrace Γ (y i) • 1‖ ≤ R :=
    Finset.le_sup' (fun k ↦ ‖y k - reducedGroupCStarAlgebraTrace Γ (y k) • 1‖) hi
  have hM_bound :
      ‖unitaryConjAverage (fun j ↦ leftRegularUnitary Γ (γ j))
          (y i - reducedGroupCStarAlgebraTrace Γ (y i) • 1)‖ < ε / 3 := by
    calc _ ≤ 2 * ‖y i - reducedGroupCStarAlgebraTrace Γ (y i) • 1‖ / Real.sqrt N :=
          norm_unitaryConjAverage_monoidAlgebra_sub_reducedGroupCStarAlgebraTrace_smul_one_le
            hF hCDU (fun g hg ↦ hfC g hg) hγD
            (f i) (Finset.subset_biUnion_of_mem (u := fun i ↦ (f i).coeff.support.erase 1) hi)
      _ ≤ 2 * R / Real.sqrt N := by gcongr
      _ < ε / 3 := by
        rw [div_lt_iff₀ (Real.sqrt_pos.2 (Nat.cast_pos.2 hN_pos))]
        have hmul : 6 * R < ε * Real.sqrt N := (div_lt_iff₀' hε).1 hN_sqrt
        linarith
  exact norm_unitaryConjAverage_sub_reducedGroupCStarAlgebraTrace_smul_one_lt_of_approx
    hN_pos γ (hf i) hM_bound

/-- **Powers averaging in `reducedGroupCStarAlgebra Γ`.** Every element `x` can be averaged by
finitely many left-regular unitary conjugates arbitrarily close to
`reducedGroupCStarAlgebraTrace Γ x • 1`. -/
theorem exists_norm_unitaryConjAverage_sub_reducedGroupCStarAlgebraTrace_smul_one_lt
    (hΓ : HasPowersProperty Γ) (x : reducedGroupCStarAlgebra Γ) {ε : ℝ} (hε : 0 < ε) :
    ∃ (N : ℕ) (γ : Fin N → Γ), 0 < N ∧
      ‖unitaryConjAverage (fun j ↦ leftRegularUnitary Γ (γ j)) x -
          reducedGroupCStarAlgebraTrace Γ x • 1‖ < ε := by
  obtain ⟨N, γ, hN, h⟩ :=
    exists_forall_norm_unitaryConjAverage_sub_reducedGroupCStarAlgebraTrace_smul_one_lt
      hΓ ({()} : Finset Unit) (fun _ ↦ x) hε
  exact ⟨N, γ, hN, h () (Finset.mem_singleton_self ())⟩

/-- **Dixmier property.** When `Γ` has the Powers property,
`reducedGroupCStarAlgebraTrace Γ x • 1` lies in the norm closure of the real convex hull of unitary
conjugates of `x`. -/
theorem reducedGroupCStarAlgebraTrace_smul_one_mem_closure_convexHull
    (hΓ : HasPowersProperty Γ) (x : reducedGroupCStarAlgebra Γ) :
    reducedGroupCStarAlgebraTrace Γ x • (1 : reducedGroupCStarAlgebra Γ) ∈
      closure (convexHull ℝ (Set.range fun g : Γ ↦
        (leftRegularUnitary Γ g : reducedGroupCStarAlgebra Γ) * x *
          star (leftRegularUnitary Γ g : reducedGroupCStarAlgebra Γ))) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨N, γ, hN, hnorm⟩ :=
    exists_norm_unitaryConjAverage_sub_reducedGroupCStarAlgebraTrace_smul_one_lt hΓ x hε
  have : Nonempty (Fin N) := Fin.pos_iff_nonempty.1 hN
  let z : reducedGroupCStarAlgebra Γ :=
    Finset.univ.centerMass (fun _ : Fin N ↦ (1 : ℝ)) fun j ↦
      (leftRegularUnitary Γ (γ j) : reducedGroupCStarAlgebra Γ) * x *
        star (leftRegularUnitary Γ (γ j) : reducedGroupCStarAlgebra Γ)
  have hz_eq : z = unitaryConjAverage (fun j ↦ leftRegularUnitary Γ (γ j)) x := by
    simp [z, Finset.centerMass, unitaryConjAverage_apply_real_smul]
  have hz_mem : z ∈ convexHull ℝ (Set.range fun g : Γ ↦
      (leftRegularUnitary Γ g : reducedGroupCStarAlgebra Γ) * x *
        star (leftRegularUnitary Γ g : reducedGroupCStarAlgebra Γ)) :=
    Finset.univ.centerMass_mem_convexHull (fun _ _ ↦ zero_le_one) (by
      simpa [Finset.card_univ] using (Nat.cast_pos (α := ℝ)).2 hN)
      fun j _ ↦ ⟨γ j, rfl⟩
  refine ⟨z, hz_mem, ?_⟩
  rw [dist_comm, dist_eq_norm, hz_eq]
  exact hnorm

end Averaging

section SimplicityAndUniqueTrace

/-- **Simplicity of reduced group C⋆-algebras with the Powers property.** Every two-sided ideal,
closed or not, of `reducedGroupCStarAlgebra Γ` is `⊥` or `⊤`. -/
theorem isSimpleRing_reducedGroupCStarAlgebra_of_hasPowersProperty {Γ : Type*} [Group Γ]
    [MeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSingletonClass Γ]
    (hΓ : HasPowersProperty Γ) :
    IsSimpleRing (reducedGroupCStarAlgebra Γ) := by
  have : Nontrivial (TwoSidedIdeal (reducedGroupCStarAlgebra Γ)) := ⟨⟨⊥, ⊤, bot_ne_top⟩⟩
  refine ⟨⟨TwoSidedIdeal.eq_bot_or_eq_top_of_forall_isClosed Units.isOpen fun I hI ↦ ?_⟩⟩
  rw [or_iff_not_imp_left]
  intro hI0
  obtain ⟨a, haI, ha0⟩ := IsConcreteLE.exists_of_lt (bot_lt_iff_ne_bot.2 hI0)
  let b : reducedGroupCStarAlgebra Γ := star a * a
  have hbI : b ∈ I := I.mul_mem_left (star a) a haI
  have hb_tr : reducedGroupCStarAlgebraTrace Γ b ≠ 0 := by
    simpa [b] using mt (reducedGroupCStarAlgebraTrace_star_mul_self_eq_zero_iff a).1 ha0
  let c : reducedGroupCStarAlgebra Γ := (reducedGroupCStarAlgebraTrace Γ b)⁻¹ • b
  have hcI : c ∈ I := I.smul_mem_of_isClosed (reducedGroupCStarAlgebraTrace Γ b)⁻¹ hbI
  have hc_tr : reducedGroupCStarAlgebraTrace Γ c = 1 := by
    dsimp only [c]
    rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hb_tr]
  obtain ⟨N, γ, _, havg⟩ :=
    exists_norm_unitaryConjAverage_sub_reducedGroupCStarAlgebraTrace_smul_one_lt hΓ c zero_lt_one
  let avg := unitaryConjAverage (fun j ↦ leftRegularUnitary Γ (γ j)) c
  have havgI : avg ∈ I := by
    dsimp only [avg]
    rw [unitaryConjAverage_apply]
    refine I.smul_mem_of_isClosed (N : ℂ)⁻¹ (sum_mem fun j _ ↦ ?_)
    exact I.mul_mem_right _ _ (I.mul_mem_left _ c hcI)
  have hunit : IsUnit avg := by
    have hlt : ‖(1 : reducedGroupCStarAlgebra Γ) - avg‖ < 1 := by
      rw [norm_sub_rev]
      simpa [avg, hc_tr] using havg
    simpa [sub_sub_cancel] using isUnit_one_sub_of_norm_lt_one hlt
  obtain ⟨u, hu⟩ := hunit
  have h1I : (1 : reducedGroupCStarAlgebra Γ) ∈ I := by
    rw [← u.mul_inv, hu]
    exact I.mul_mem_right avg (↑u⁻¹) havgI
  exact I.eq_top h1I

/-- **Uniqueness of the trace under the Powers property.** Every continuous unital tracial linear
functional on `reducedGroupCStarAlgebra Γ` agrees with `reducedGroupCStarAlgebraTrace Γ`. -/
theorem eq_reducedGroupCStarAlgebraTrace_of_hasPowersProperty {Γ : Type*} [Group Γ]
    [MeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSingletonClass Γ]
    (hΓ : HasPowersProperty Γ) (φ : reducedGroupCStarAlgebra Γ →L[ℂ] ℂ)
    (hone : φ 1 = 1) (htrace : ∀ x y, φ (x * y) = φ (y * x))
    (x : reducedGroupCStarAlgebra Γ) :
    φ x = reducedGroupCStarAlgebraTrace Γ x := by
  rw [← sub_eq_zero, ← norm_eq_zero]
  refine le_antisymm ?_ (norm_nonneg _)
  refine le_of_forall_pos_le_add fun δ hδ ↦ ?_
  rw [zero_add]
  have hε : 0 < δ / (‖φ‖ + 1) := div_pos hδ (add_pos_of_nonneg_of_pos (norm_nonneg φ) zero_lt_one)
  obtain ⟨N, γ, hN, havg⟩ :=
    exists_norm_unitaryConjAverage_sub_reducedGroupCStarAlgebraTrace_smul_one_lt hΓ x hε
  let avg := unitaryConjAverage (fun j ↦ leftRegularUnitary Γ (γ j)) x
  have hφ_avg : φ avg = φ x :=
    map_unitaryConjAverage_eq hN _ (φ : reducedGroupCStarAlgebra Γ →ₗ[ℂ] ℂ) htrace x
  have hφ_tr : φ (reducedGroupCStarAlgebraTrace Γ x • 1) = reducedGroupCStarAlgebraTrace Γ x := by
    rw [map_smul, hone, smul_eq_mul, mul_one]
  calc ‖φ x - reducedGroupCStarAlgebraTrace Γ x‖
      = ‖φ (avg - reducedGroupCStarAlgebraTrace Γ x • 1)‖ := by rw [map_sub, hφ_avg, hφ_tr]
    _ ≤ ‖φ‖ * ‖avg - reducedGroupCStarAlgebraTrace Γ x • 1‖ := φ.le_opNorm _
    _ ≤ ‖φ‖ * (δ / (‖φ‖ + 1)) := mul_le_mul_of_nonneg_left havg.le (norm_nonneg φ)
    _ ≤ δ := by
        rw [mul_div_assoc', div_le_iff₀ (by positivity)]
        nlinarith [norm_nonneg φ]

/-- **Uniqueness of the tracial state under the Powers property.** Every tracial state
`τ : reducedGroupCStarAlgebra Γ →P[ℂ] ℂ` agrees with `reducedGroupCStarAlgebraTracePositive Γ`. -/
theorem eq_reducedGroupCStarAlgebraTracePositive_of_hasPowersProperty {Γ : Type*} [Group Γ]
    [MeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSingletonClass Γ]
    (hΓ : HasPowersProperty Γ) {τ : reducedGroupCStarAlgebra Γ →P[ℂ] ℂ}
    (hτ : τ.IsTracialState) (x : reducedGroupCStarAlgebra Γ) :
    τ x = reducedGroupCStarAlgebraTracePositive Γ x :=
  (eq_reducedGroupCStarAlgebraTrace_of_hasPowersProperty hΓ
    (τ : reducedGroupCStarAlgebra Γ →L[ℂ] ℂ) hτ.map_one hτ.map_mul_comm x).trans
    (reducedGroupCStarAlgebraTracePositive_apply x).symm

/-- **Singleton tracial state space under the Powers property.** When `Γ` has the Powers
property, `tracialStates (reducedGroupCStarAlgebra Γ)` consists solely of the canonical trace. -/
theorem tracialStates_reducedGroupCStarAlgebra_eq_singleton {Γ : Type*} [Group Γ]
    [MeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSingletonClass Γ]
    (hΓ : HasPowersProperty Γ) :
    tracialStates (reducedGroupCStarAlgebra Γ) =
      {StrongDual.toWeakDual (reducedGroupCStarAlgebraTrace Γ)} := by
  ext φ
  rw [Set.mem_singleton_iff]
  refine ⟨fun hφ ↦ ?_, fun hφ ↦ ?_⟩
  · rw [mem_tracialStates_iff] at hφ
    refine DFunLike.ext φ _ fun x ↦ ?_
    simpa [StrongDual.toWeakDual_apply] using
      eq_reducedGroupCStarAlgebraTrace_of_hasPowersProperty hΓ
        (WeakDual.toStrongDual φ) (map_one_of_mem_stateSpace hφ.1) hφ.2 x
  · subst hφ
    rw [← toContinuousLinearMap_reducedGroupCStarAlgebraTracePositive,
      toWeakDual_mem_tracialStates_iff]
    exact isTracialState_reducedGroupCStarAlgebraTracePositive

/-- Powers's theorem: the reduced C⋆-algebra of a free group on a basis with two distinct elements
is simple as a ring (every two-sided ideal, closed or not, is `⊥` or `⊤`). -/
theorem reducedFreeGroup_isSimpleRing {ι : Type*} (a b : ι) (hab : a ≠ b)
    (lam : FreeGroup ι →
      (lp (fun _ : FreeGroup ι ↦ ℂ) 2 →L[ℂ] lp (fun _ : FreeGroup ι ↦ ℂ) 2))
    (hlam : ∀ g ξ h, lam g ξ h = ξ (g⁻¹ * h)) :
    IsSimpleRing (generatedCStarAlgebra ℂ lam) := by
  let _ : MeasurableSpace (FreeGroup ι) := ⊤
  have _ : MeasurableMul (FreeGroup ι) := DiscreteMeasurableSpace.toMeasurableMul
  exact IsSimpleRing.of_ringEquiv
    (reducedGroupCStarAlgebraEquivOfApply hlam).toRingEquiv
    (isSimpleRing_reducedGroupCStarAlgebra_of_hasPowersProperty
      (FreeGroup.hasPowersProperty_of_ne hab))

/-- Uniqueness of the trace: every continuous unital tracial linear functional on the reduced
C⋆-algebra of a free group on a basis with two distinct elements equals the canonical trace
`τ(x) = ⟪δ₁, x δ₁⟫_ℂ`. -/
theorem reducedFreeGroup_trace_unique {ι : Type*} [DecidableEq ι] (a b : ι) (hab : a ≠ b)
    (lam : FreeGroup ι →
      (lp (fun _ : FreeGroup ι ↦ ℂ) 2 →L[ℂ] lp (fun _ : FreeGroup ι ↦ ℂ) 2))
    (hlam : ∀ g ξ h, lam g ξ h = ξ (g⁻¹ * h))
    (φ : generatedCStarAlgebra ℂ lam →L[ℂ] ℂ)
    (hone : φ 1 = 1) (htrace : ∀ x y, φ (x * y) = φ (y * x))
    (x : generatedCStarAlgebra ℂ lam) :
    φ x = inner ℂ (lp.single 2 (1 : FreeGroup ι) (1 : ℂ))
      ((x : lp (fun _ : FreeGroup ι ↦ ℂ) 2 →L[ℂ] lp (fun _ : FreeGroup ι ↦ ℂ) 2)
        (lp.single 2 (1 : FreeGroup ι) (1 : ℂ))) := by
  let _ : MeasurableSpace (FreeGroup ι) := ⊤
  have _ : MeasurableMul (FreeGroup ι) := DiscreteMeasurableSpace.toMeasurableMul
  let e := reducedGroupCStarAlgebraEquivOfApply hlam
  let eCLM : reducedGroupCStarAlgebra (FreeGroup ι) →L[ℂ] generatedCStarAlgebra ℂ lam :=
    ⟨e.toAlgEquiv.toLinearMap, continuous_reducedGroupCStarAlgebraEquivOfApply hlam⟩
  have heCLM (u : reducedGroupCStarAlgebra (FreeGroup ι)) : eCLM u = e u := rfl
  let ψ : reducedGroupCStarAlgebra (FreeGroup ι) →L[ℂ] ℂ := φ.comp eCLM
  have hψ : ψ (e.symm x) =
      reducedGroupCStarAlgebraTrace (FreeGroup ι) (e.symm x) :=
    eq_reducedGroupCStarAlgebraTrace_of_hasPowersProperty
      (FreeGroup.hasPowersProperty_of_ne hab) ψ
      (by simp [ψ, heCLM, hone]) (fun u v ↦ by simp [ψ, heCLM, htrace]) (e.symm x)
  have hφx : φ x = ψ (e.symm x) := by simp [ψ, heCLM]
  exact hφx.trans (hψ.trans (reducedGroupCStarAlgebraTrace_symm_equivOfApply hlam x))

end SimplicityAndUniqueTrace

end TauCeti

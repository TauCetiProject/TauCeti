/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.RingTheory.SimpleRing.Defs
public import TauCeti.Analysis.CStarAlgebra.Group.Basic
public import TauCeti.Analysis.InnerProductSpace.Projection.Averaging
public import TauCeti.Analysis.Normed.Lp.Diagonal.Indicator
public import TauCeti.Analysis.Normed.Lp.LeftTranslation
public import TauCeti.GroupTheory.PowersProperty
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Normed.Ring.Units
import TauCeti.Analysis.CStarAlgebra.Basic
import TauCeti.Analysis.CStarAlgebra.Ideal
import TauCeti.Analysis.CStarAlgebra.UnitaryAverage
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
  the norm bound `2 * ‖x‖ / √N` (`TauCeti.norm_average_unitary_conj_le_of_powersPartition`).
* **Simplicity and unique trace**: approximating elements of `reducedGroupCStarAlgebra Γ` by the
  dense image of `MonoidAlgebra ℂ Γ` shows that `τ(x) • 1` lies in the norm closure of the convex
  hull of unitary conjugates of `x` (`TauCeti.canonicalTrace_smul_one_mem_closure_convexHull`).
  Consequently, whenever `HasPowersProperty Γ` holds, `reducedGroupCStarAlgebra Γ` is a simple
  ring (`TauCeti.isSimpleRing_of_hasPowersProperty`) and `canonicalTrace Γ` is the unique
  continuous unital tracial linear functional (`TauCeti.eq_canonicalTrace_of_hasPowersProperty`).
* **Free groups**: specializing via `FreeGroup.hasPowersProperty_of_ne` gives
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

private noncomputable def leftTranslationCLM (g : Γ) :
    lp (fun _ : Γ ↦ ℂ) 2 →L[ℂ] lp (fun _ : Γ ↦ ℂ) 2 :=
  (lp.leftTranslation 2 ℂ (X := Γ) (E := ℂ) g).toLinearIsometry.toContinuousLinearMap

private theorem leftTranslationCLM_apply (g : Γ) (ξ : lp (fun _ : Γ ↦ ℂ) 2) (t : Γ) :
    leftTranslationCLM g ξ t = ξ (g⁻¹ * t) := by
  simp [leftTranslationCLM]

private theorem leftTranslationCLM_mul (g h : Γ) :
    leftTranslationCLM (g * h) = leftTranslationCLM g * leftTranslationCLM h := by
  ext ξ t
  simp [leftTranslationCLM_apply, mul_assoc]

private theorem star_leftTranslationCLM (g : Γ) :
    star (leftTranslationCLM g) = leftTranslationCLM g⁻¹ := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  symm
  refine (ContinuousLinearMap.eq_adjoint_iff _ _).2 fun ξ η ↦ ?_
  simp only [lp.inner_eq_tsum, leftTranslationCLM_apply, inv_inv]
  rw [← (Equiv.mulLeft g⁻¹).tsum_eq (fun h ↦ ⟪ξ (g * h), η h⟫_ℂ)]
  simp [mul_inv_cancel_left]

private theorem leftTranslationCLM_mem_unitary (g : Γ) :
    leftTranslationCLM g ∈ unitary (lp (fun _ : Γ ↦ ℂ) 2 →L[ℂ] lp (fun _ : Γ ↦ ℂ) 2) := by
  refine Unitary.mem_iff.2 ⟨?_, ?_⟩
  · rw [star_leftTranslationCLM, ← leftTranslationCLM_mul, inv_mul_cancel]
    ext ξ t; simp [leftTranslationCLM_apply]
  · rw [star_leftTranslationCLM, ← leftTranslationCLM_mul, mul_inv_cancel]
    ext ξ t; simp [leftTranslationCLM_apply]

/-- **Zero compression on the complement of `γ • D`.** When `C ⊔ D = univ` is a partition of `Γ`
with `Disjoint ((f * ·) '' C) C`, conjugating left translation by `f` with left translation by
`g` has vanishing compression onto the complement of `(g * ·) '' D`. -/
theorem compression_sub_indicatorCLM_leftTranslation_eq_zero {C D : Set Γ}
    (hCDU : C ∪ D = Set.univ) {f : Γ} (hfC : Disjoint ((fun x : Γ ↦ f * x) '' C) C) (g : Γ) :
    (1 - lp.indicatorCLM 2 ℂ ((fun x : Γ ↦ g * x) '' D)) *
        ((lp.leftTranslation 2 ℂ (X := Γ) (E := ℂ) g).toLinearIsometry.toContinuousLinearMap *
          (lp.leftTranslation 2 ℂ (X := Γ) (E := ℂ) f).toLinearIsometry.toContinuousLinearMap *
          star (lp.leftTranslation 2 ℂ (X := Γ) (E := ℂ)
            g).toLinearIsometry.toContinuousLinearMap) *
        (1 - lp.indicatorCLM 2 ℂ ((fun x : Γ ↦ g * x) '' D)) = 0 := by
  change (1 - lp.indicatorCLM 2 ℂ ((fun x : Γ ↦ g * x) '' D)) *
      (leftTranslationCLM g * leftTranslationCLM f * star (leftTranslationCLM g)) *
      (1 - lp.indicatorCLM 2 ℂ ((fun x : Γ ↦ g * x) '' D)) = 0
  set S : Set Γ := (fun x : Γ ↦ g * x) '' D
  rw [← lp.indicatorCLM_compl, star_leftTranslationCLM, ← leftTranslationCLM_mul,
    ← leftTranslationCLM_mul]
  ext ξ t
  simp only [mul_apply_eq_comp, zero_apply, lp.coeFn_zero, Pi.zero_apply, lp.indicatorCLM_apply]
  by_cases ht : t ∈ Sᶜ
  · rw [Set.indicator_of_mem ht, leftTranslationCLM_apply]
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

omit [Group Γ] in
private theorem opNorm_countHilbertBasis_conjStarAlgEquiv
    [MeasurableSpace Γ] [MeasurableSingletonClass Γ]
    (T : Lp ℂ 2 (Measure.count : Measure Γ) →L[ℂ] Lp ℂ 2 (Measure.count : Measure Γ)) :
    ‖(L2.countHilbertBasis ℂ Γ).repr.conjStarAlgEquiv T‖ = ‖T‖ := by
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply,
    ContinuousLinearMap.opNorm_linearIsometryEquiv_comp,
    ContinuousLinearMap.opNorm_comp_linearIsometryEquiv]

variable [MeasurableSpace Γ] [MeasurableMul Γ]

private theorem exists_monoidAlgebra_norm_sub_lt (x : reducedGroupCStarAlgebra Γ) {δ : ℝ}
    (hδ : 0 < δ) :
    ∃ f : MonoidAlgebra ℂ Γ, ‖x - groupAlgebraToReducedGroupCStarAlgebra Γ f‖ < δ := by
  obtain ⟨f, hdist⟩ :=
    Metric.mem_closure_range_iff.1 (denseRange_groupAlgebraToReducedGroupCStarAlgebra Γ x) δ hδ
  refine ⟨f, ?_⟩
  rwa [dist_eq_norm] at hdist

variable [MeasurableSingletonClass Γ]

private theorem countHilbertBasis_conjStarAlgEquiv_leftRegular (g : Γ) :
    (L2.countHilbertBasis ℂ Γ).repr.conjStarAlgEquiv
        ((Measure.count : Measure Γ).leftRegular ℂ ℂ 2 g) =
      leftTranslationCLM g := by
  ext ξ t
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply, leftTranslationCLM_apply]
  change (L2.countHilbertBasis ℂ Γ).repr
      ((Measure.count : Measure Γ).leftRegular ℂ ℂ 2 g
        ((L2.countHilbertBasis ℂ Γ).repr.symm ξ)) t = ξ (g⁻¹ * t)
  rw [L2.countHilbertBasis_repr_apply]
  have h1 := Measure.ae_count_iff.1
    (Measure.coeFn_leftRegular (𝕜 := ℂ) (Measure.count : Measure Γ) 2 g
      ((L2.countHilbertBasis ℂ Γ).repr.symm ξ)) t
  have h2 := L2.countHilbertBasis_repr_apply ((L2.countHilbertBasis ℂ Γ).repr.symm ξ) (g⁻¹ * t)
  have h3 := congrArg (fun u : lp (fun _ : Γ ↦ ℂ) 2 ↦ u (g⁻¹ * t))
    ((L2.countHilbertBasis ℂ Γ).repr.apply_symm_apply ξ)
  exact h1.trans (h2.symm.trans h3)

/-- **Powers's operator-norm averaging bound.** For a finite sum
`x = ∑ f ∈ F, c f • leftRegularUnitary Γ f` with `F` disjoint from `{1}`, a Powers partition
`(C, D, γ)` yields `‖(N : ℂ)⁻¹ • ∑ j, λ(γ j) * x * star (λ(γ j))‖ ≤ 2 * ‖x‖ / √N`. -/
theorem norm_average_unitary_conj_le_of_powersPartition
    {F : Finset Γ} {C D : Set Γ} {N : ℕ} {γ : Fin N → Γ}
    (hCDU : C ∪ D = Set.univ)
    (hfC : ∀ f ∈ F, Disjoint ((fun x : Γ ↦ f * x) '' C) C)
    (hγD : Pairwise fun i j : Fin N ↦
      Disjoint ((fun x : Γ ↦ γ i * x) '' D) ((fun x : Γ ↦ γ j * x) '' D))
    (c : Γ → ℂ) :
    ‖(N : ℂ)⁻¹ • ∑ j : Fin N,
        (leftRegularUnitary Γ (γ j) : reducedGroupCStarAlgebra Γ) *
          (∑ f ∈ F, c f • (leftRegularUnitary Γ f : reducedGroupCStarAlgebra Γ)) *
          star (leftRegularUnitary Γ (γ j) : reducedGroupCStarAlgebra Γ)‖ ≤
      2 * ‖∑ f ∈ F, c f • (leftRegularUnitary Γ f : reducedGroupCStarAlgebra Γ)‖ /
        Real.sqrt N := by
  let xlp : lp (fun _ : Γ ↦ ℂ) 2 →L[ℂ] lp (fun _ : Γ ↦ ℂ) 2 :=
    ∑ f ∈ F, c f • leftTranslationCLM f
  let P : Fin N → (lp (fun _ : Γ ↦ ℂ) 2 →L[ℂ] lp (fun _ : Γ ↦ ℂ) 2) :=
    fun j ↦ lp.indicatorCLM 2 ℂ ((fun y : Γ ↦ γ j * y) '' D)
  let U : Fin N → unitary (lp (fun _ : Γ ↦ ℂ) 2 →L[ℂ] lp (fun _ : Γ ↦ ℂ) 2) :=
    fun j ↦ ⟨leftTranslationCLM (γ j), leftTranslationCLM_mem_unitary (γ j)⟩
  have hzero : ∀ j ∈ (Finset.univ : Finset (Fin N)),
      (1 - P j) * ((U j : lp (fun _ : Γ ↦ ℂ) 2 →L[ℂ] lp (fun _ : Γ ↦ ℂ) 2) * xlp *
        star (U j : lp (fun _ : Γ ↦ ℂ) 2 →L[ℂ] lp (fun _ : Γ ↦ ℂ) 2)) * (1 - P j) = 0 := by
    intro j _
    simp only [xlp, U, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc]
    exact Finset.sum_eq_zero fun f hf ↦ by
      rw [show (1 - P j) * (leftTranslationCLM (γ j) * leftTranslationCLM f *
            star (leftTranslationCLM (γ j))) * (1 - P j) = 0 from
          compression_sub_indicatorCLM_leftTranslation_eq_zero hCDU (hfC f hf) (γ j)]
      ext; simp
  have hbound :=
    ContinuousLinearMap.norm_average_unitary_conj_le_two_mul_div_sqrt_card_of_compression_eq_zero
      xlp U P Finset.univ
      (fun j _ ↦ lp.isStarProjection_indicatorCLM ℂ _)
      (fun i _ j _ hij ↦ lp.indicatorCLM_mul_of_disjoint (hγD hij))
      hzero
  have hlhs : ‖(N : ℂ)⁻¹ • ∑ j : Fin N,
        (leftRegularUnitary Γ (γ j) : reducedGroupCStarAlgebra Γ) *
          (∑ f ∈ F, c f • (leftRegularUnitary Γ f : reducedGroupCStarAlgebra Γ)) *
          star (leftRegularUnitary Γ (γ j) : reducedGroupCStarAlgebra Γ)‖ =
      ‖((Finset.univ : Finset (Fin N)).card : ℂ)⁻¹ •
          ∑ j : Fin N, (U j : _ →L[ℂ] _) * xlp * star (U j : _ →L[ℂ] _)‖ := by
    rw [AddSubgroupClass.coe_norm, ← opNorm_countHilbertBasis_conjStarAlgEquiv]
    congr 1
    simp [-star_coe_leftRegularUnitary, U, xlp, countHilbertBasis_conjStarAlgEquiv_leftRegular,
      star_leftTranslationCLM]
  have hrhs : ‖∑ f ∈ F, c f • (leftRegularUnitary Γ f : reducedGroupCStarAlgebra Γ)‖ = ‖xlp‖ := by
    rw [AddSubgroupClass.coe_norm, ← opNorm_countHilbertBasis_conjStarAlgEquiv]
    congr 1
    simp [xlp, countHilbertBasis_conjStarAlgEquiv_leftRegular]
  rw [hlhs, hrhs]
  simpa only [Finset.card_univ, Fintype.card_fin] using hbound

private theorem monoidAlgebra_sub_canonicalTrace_eq [DecidableEq Γ] {F : Finset Γ}
    (hF : ∀ f ∈ F, f ≠ 1) (f : MonoidAlgebra ℂ Γ) (hfF : f.coeff.support.erase 1 ⊆ F) :
    groupAlgebraToReducedGroupCStarAlgebra Γ f -
        canonicalTrace Γ (groupAlgebraToReducedGroupCStarAlgebra Γ f) • 1 =
      ∑ g ∈ F, f.coeff g • (leftRegularUnitary Γ g : reducedGroupCStarAlgebra Γ) := by
  have hy : groupAlgebraToReducedGroupCStarAlgebra Γ f =
      ∑ g ∈ f.coeff.support,
        f.coeff g • (leftRegularUnitary Γ g : reducedGroupCStarAlgebra Γ) := by
    conv_lhs => rw [← MonoidAlgebra.sum_coeff_single f]
    rw [Finsupp.sum, map_sum]
    simp
  have hsum_F :
      ∑ g ∈ F, f.coeff g • (leftRegularUnitary Γ g : reducedGroupCStarAlgebra Γ) =
        ∑ g ∈ f.coeff.support.erase 1,
          f.coeff g • (leftRegularUnitary Γ g : reducedGroupCStarAlgebra Γ) := by
    refine (Finset.sum_subset hfF fun g hgF hgnot ↦ ?_).symm
    have hnot : g ∉ f.coeff.support := fun hmem ↦ hgnot (Finset.mem_erase.2 ⟨hF g hgF, hmem⟩)
    simp [Finsupp.notMem_support_iff.1 hnot]
  rw [canonicalTrace_groupAlgebraToReducedGroupCStarAlgebra, hy, hsum_F]
  by_cases h1 : (1 : Γ) ∈ f.coeff.support
  · rw [← Finset.add_sum_erase f.coeff.support
      (fun g ↦ f.coeff g • (leftRegularUnitary Γ g : reducedGroupCStarAlgebra Γ)) h1,
      map_one (leftRegularUnitary Γ), OneMemClass.coe_one, add_sub_cancel_left]
  · rw [Finsupp.notMem_support_iff.1 h1, zero_smul ℂ (1 : reducedGroupCStarAlgebra Γ), sub_zero,
      Finset.erase_eq_of_notMem h1]

private theorem norm_average_sub_canonicalTrace_lt_of_approx {N : ℕ} (hN : 0 < N)
    (γ : Fin N → Γ) {x y : reducedGroupCStarAlgebra Γ} {ε : ℝ}
    (hxy : ‖x - y‖ < ε / 3)
    (hMy : ‖unitaryConjAverage (fun j ↦ leftRegularUnitary Γ (γ j))
        (y - canonicalTrace Γ y • 1)‖ < ε / 3) :
    ‖unitaryConjAverage (fun j ↦ leftRegularUnitary Γ (γ j)) x -
        canonicalTrace Γ x • 1‖ < ε := by
  let u : Fin N → unitary (reducedGroupCStarAlgebra Γ) := fun j ↦ leftRegularUnitary Γ (γ j)
  have hdecomp : unitaryConjAverage u x - canonicalTrace Γ x • 1 =
      unitaryConjAverage u (x - y) + unitaryConjAverage u (y - canonicalTrace Γ y • 1) +
        (canonicalTrace Γ y - canonicalTrace Γ x) • 1 := by
    rw [map_sub, map_sub, map_smul, unitaryConjAverage_one hN u, sub_smul]
    abel
  have hnorm1 : ‖unitaryConjAverage u (x - y)‖ < ε / 3 :=
    (norm_unitaryConjAverage_apply_le hN u (x - y)).trans_lt hxy
  have hnorm3 : ‖(canonicalTrace Γ y - canonicalTrace Γ x) •
      (1 : reducedGroupCStarAlgebra Γ)‖ < ε / 3 := by
    calc ‖(canonicalTrace Γ y - canonicalTrace Γ x) • (1 : reducedGroupCStarAlgebra Γ)‖
        = ‖canonicalTrace Γ (y - x)‖ * ‖(1 : reducedGroupCStarAlgebra Γ)‖ := by
          rw [norm_smul, map_sub]
      _ ≤ ‖canonicalTrace Γ (y - x)‖ * 1 :=
          mul_le_mul_of_nonneg_left CStarRing.norm_one_le (norm_nonneg _)
      _ = ‖canonicalTrace Γ (y - x)‖ := mul_one _
      _ ≤ ‖y - x‖ := norm_canonicalTrace_apply_le _
      _ = ‖x - y‖ := norm_sub_rev _ _
      _ < ε / 3 := hxy
  rw [hdecomp]
  calc ‖unitaryConjAverage u (x - y) + unitaryConjAverage u (y - canonicalTrace Γ y • 1) +
        (canonicalTrace Γ y - canonicalTrace Γ x) • 1‖
      ≤ ‖unitaryConjAverage u (x - y) + unitaryConjAverage u (y - canonicalTrace Γ y • 1)‖ +
          ‖(canonicalTrace Γ y - canonicalTrace Γ x) • (1 : reducedGroupCStarAlgebra Γ)‖ :=
        norm_add_le _ _
    _ ≤ (‖unitaryConjAverage u (x - y)‖ +
            ‖unitaryConjAverage u (y - canonicalTrace Γ y • 1)‖) +
          ‖(canonicalTrace Γ y - canonicalTrace Γ x) • (1 : reducedGroupCStarAlgebra Γ)‖ :=
        add_le_add (norm_add_le _ _) le_rfl
    _ < ε / 3 + ε / 3 + ε / 3 := by linarith
    _ = ε := by ring

private theorem norm_average_monoidAlgebra_sub_canonicalTrace_le [DecidableEq Γ]
    {F : Finset Γ} (hF : ∀ f ∈ F, f ≠ 1) {C D : Set Γ} {N : ℕ} {γ : Fin N → Γ}
    (hCDU : C ∪ D = Set.univ) (hfC : ∀ f ∈ F, Disjoint ((fun x : Γ ↦ f * x) '' C) C)
    (hγD : Pairwise fun i j : Fin N ↦
      Disjoint ((fun x : Γ ↦ γ i * x) '' D) ((fun x : Γ ↦ γ j * x) '' D))
    (f : MonoidAlgebra ℂ Γ) (hfF : f.coeff.support.erase 1 ⊆ F) :
    let y := groupAlgebraToReducedGroupCStarAlgebra Γ f
    ‖unitaryConjAverage (fun j ↦ leftRegularUnitary Γ (γ j))
        (y - canonicalTrace Γ y • 1)‖ ≤
      2 * ‖y - canonicalTrace Γ y • 1‖ / Real.sqrt N := by
  intro y
  rw [monoidAlgebra_sub_canonicalTrace_eq hF f hfF, unitaryConjAverage_apply]
  exact norm_average_unitary_conj_le_of_powersPartition hCDU hfC hγD (fun g ↦ f.coeff g)

/-- **Simultaneous Powers averaging in `reducedGroupCStarAlgebra Γ`.** Given a finite family `x`
and `ε > 0`, when `Γ` has the Powers property there exist `N > 0` and `γ : Fin N → Γ` whose
conjugate average brings every `x i` (`i ∈ s`) within `ε` of `canonicalTrace Γ (x i) • 1`. -/
theorem exists_forall_norm_average_unitary_conj_sub_canonicalTrace_lt
    (hΓ : HasPowersProperty Γ)
    {ι : Type*} (s : Finset ι) (x : ι → reducedGroupCStarAlgebra Γ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (N : ℕ) (γ : Fin N → Γ), 0 < N ∧ ∀ i ∈ s,
      ‖(N : ℂ)⁻¹ • ∑ j : Fin N,
          (leftRegularUnitary Γ (γ j) : reducedGroupCStarAlgebra Γ) * x i *
            star (leftRegularUnitary Γ (γ j) : reducedGroupCStarAlgebra Γ) -
          canonicalTrace Γ (x i) • 1‖ < ε := by
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
  let R : ℝ := s.sup' hs fun i ↦ ‖y i - canonicalTrace Γ (y i) • 1‖
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt ((6 * R / ε) ^ 2)
  let N : ℕ := max 1 N₀
  have hN_pos : 0 < N := lt_of_lt_of_le zero_lt_one (le_max_left 1 N₀)
  have hN_sqrt : 6 * R / ε < Real.sqrt N :=
    Real.lt_sqrt_of_sq_lt (hN₀.trans_le (Nat.cast_le.2 (le_max_right 1 N₀)))
  obtain ⟨C, D, γ, -, hCDU, hfC, hγD⟩ := hasPowersProperty_def.1 hΓ F hF N
  refine ⟨N, γ, hN_pos, fun i hi ↦ ?_⟩
  have hR : ‖y i - canonicalTrace Γ (y i) • 1‖ ≤ R :=
    Finset.le_sup' (fun k ↦ ‖y k - canonicalTrace Γ (y k) • 1‖) hi
  have hM_bound :
      ‖unitaryConjAverage (fun j ↦ leftRegularUnitary Γ (γ j))
          (y i - canonicalTrace Γ (y i) • 1)‖ < ε / 3 := by
    calc _ ≤ 2 * ‖y i - canonicalTrace Γ (y i) • 1‖ / Real.sqrt N :=
          norm_average_monoidAlgebra_sub_canonicalTrace_le hF hCDU (fun g hg ↦ hfC g hg) hγD
            (f i) (Finset.subset_biUnion_of_mem (u := fun i ↦ (f i).coeff.support.erase 1) hi)
      _ ≤ 2 * R / Real.sqrt N := by gcongr
      _ < ε / 3 := by
        rw [div_lt_iff₀ (Real.sqrt_pos.2 (Nat.cast_pos.2 hN_pos))]
        have hmul : 6 * R < ε * Real.sqrt N := (div_lt_iff₀' hε).1 hN_sqrt
        linarith
  rw [← unitaryConjAverage_apply]
  exact norm_average_sub_canonicalTrace_lt_of_approx hN_pos γ (hf i) hM_bound

/-- **Powers averaging in `reducedGroupCStarAlgebra Γ`.** Every element `x` can be averaged by
finitely many left-regular unitary conjugates arbitrarily close to `canonicalTrace Γ x • 1`. -/
theorem exists_norm_average_unitary_conj_sub_canonicalTrace_lt
    (hΓ : HasPowersProperty Γ) (x : reducedGroupCStarAlgebra Γ) {ε : ℝ} (hε : 0 < ε) :
    ∃ (N : ℕ) (γ : Fin N → Γ), 0 < N ∧
      ‖(N : ℂ)⁻¹ • ∑ j : Fin N,
          (leftRegularUnitary Γ (γ j) : reducedGroupCStarAlgebra Γ) * x *
            star (leftRegularUnitary Γ (γ j) : reducedGroupCStarAlgebra Γ) -
          canonicalTrace Γ x • 1‖ < ε := by
  obtain ⟨N, γ, hN, h⟩ :=
    exists_forall_norm_average_unitary_conj_sub_canonicalTrace_lt hΓ ({()} : Finset Unit)
      (fun _ ↦ x) hε
  exact ⟨N, γ, hN, h () (Finset.mem_singleton_self ())⟩

/-- **Dixmier property.** When `Γ` has the Powers property, `canonicalTrace Γ x • 1` lies in the
norm closure of the real convex hull of unitary conjugates of `x`. -/
theorem canonicalTrace_smul_one_mem_closure_convexHull
    (hΓ : HasPowersProperty Γ) (x : reducedGroupCStarAlgebra Γ) :
    canonicalTrace Γ x • (1 : reducedGroupCStarAlgebra Γ) ∈
      closure (convexHull ℝ (Set.range fun g : Γ ↦
        (leftRegularUnitary Γ g : reducedGroupCStarAlgebra Γ) * x *
          star (leftRegularUnitary Γ g : reducedGroupCStarAlgebra Γ))) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨N, γ, hN, hnorm⟩ :=
    exists_norm_average_unitary_conj_sub_canonicalTrace_lt hΓ x hε
  have : Nonempty (Fin N) := Fin.pos_iff_nonempty.1 hN
  let z : reducedGroupCStarAlgebra Γ :=
    Finset.univ.centerMass (fun _ : Fin N ↦ (1 : ℝ)) fun j ↦
      (leftRegularUnitary Γ (γ j) : reducedGroupCStarAlgebra Γ) * x *
        star (leftRegularUnitary Γ (γ j) : reducedGroupCStarAlgebra Γ)
  have hz_eq : z = unitaryConjAverage (fun j ↦ leftRegularUnitary Γ (γ j)) x := by
    simp only [z, Finset.centerMass, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one, one_smul, unitaryConjAverage_apply]
    rw [← algebraMap_smul ℂ (N : ℝ)⁻¹]
    simp
  have hz_mem : z ∈ convexHull ℝ (Set.range fun g : Γ ↦
      (leftRegularUnitary Γ g : reducedGroupCStarAlgebra Γ) * x *
        star (leftRegularUnitary Γ g : reducedGroupCStarAlgebra Γ)) :=
    Finset.univ.centerMass_mem_convexHull (fun _ _ ↦ zero_le_one) (by
      simpa [Finset.card_univ] using (Nat.cast_pos (α := ℝ)).2 hN)
      fun j _ ↦ ⟨γ j, rfl⟩
  refine ⟨z, hz_mem, ?_⟩
  rw [dist_comm, dist_eq_norm, hz_eq, unitaryConjAverage_apply]
  exact hnorm

end Averaging

section SimplicityAndUniqueTrace

/-- **Simplicity of reduced group C⋆-algebras with the Powers property.** Every two-sided ideal,
closed or not, of `reducedGroupCStarAlgebra Γ` is `⊥` or `⊤`. -/
theorem isSimpleRing_of_hasPowersProperty {Γ : Type*} [Group Γ]
    [MeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSingletonClass Γ]
    (hΓ : HasPowersProperty Γ) :
    IsSimpleRing (reducedGroupCStarAlgebra Γ) := by
  have : Nontrivial (Lp ℂ 2 (Measure.count : Measure Γ)) :=
    ⟨⟨L2.countHilbertBasis ℂ Γ 1, 0, fun h ↦ by
      have h' := congrArg norm h
      simp at h'⟩⟩
  have : Nontrivial (TwoSidedIdeal (reducedGroupCStarAlgebra Γ)) := ⟨⟨⊥, ⊤, bot_ne_top⟩⟩
  refine ⟨⟨TwoSidedIdeal.eq_bot_or_eq_top_of_forall_isClosed Units.isOpen fun I hI ↦ ?_⟩⟩
  rw [or_iff_not_imp_left]
  intro hI0
  obtain ⟨a, haI, ha0⟩ : ∃ a ∈ I, a ≠ 0 := by
    by_contra! hall
    apply hI0
    ext x
    exact ⟨fun hx ↦ (TwoSidedIdeal.mem_bot _).2 (hall x hx), fun hx ↦ by
      rw [(TwoSidedIdeal.mem_bot _).1 hx]
      exact I.zero_mem⟩
  let b : reducedGroupCStarAlgebra Γ := star a * a
  have hbI : b ∈ I := I.mul_mem_left (star a) a haI
  have hb_tr : canonicalTrace Γ b ≠ 0 := by
    simpa [b] using mt (canonicalTrace_star_mul_self_eq_zero_iff a).1 ha0
  let c : reducedGroupCStarAlgebra Γ := (canonicalTrace Γ b)⁻¹ • b
  have hcI : c ∈ I := I.smul_mem_of_isClosed (canonicalTrace Γ b)⁻¹ hbI
  have hc_tr : canonicalTrace Γ c = 1 := by
    dsimp only [c]
    rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hb_tr]
  obtain ⟨N, γ, _, havg⟩ :=
    exists_norm_average_unitary_conj_sub_canonicalTrace_lt hΓ c zero_lt_one
  let avg := unitaryConjAverage (fun j ↦ leftRegularUnitary Γ (γ j)) c
  have havgI : avg ∈ I := by
    dsimp only [avg]
    rw [unitaryConjAverage_apply]
    refine I.smul_mem_of_isClosed (N : ℂ)⁻¹ (sum_mem fun j _ ↦ ?_)
    exact I.mul_mem_right _ _ (I.mul_mem_left _ c hcI)
  have hunit : IsUnit avg := by
    have hlt : ‖(1 : reducedGroupCStarAlgebra Γ) - avg‖ < 1 := by
      rw [norm_sub_rev]
      simpa [avg, unitaryConjAverage_apply, hc_tr] using havg
    simpa [sub_sub_cancel] using isUnit_one_sub_of_norm_lt_one hlt
  obtain ⟨u, hu⟩ := hunit
  have h1I : (1 : reducedGroupCStarAlgebra Γ) ∈ I := by
    rw [← u.mul_inv, hu]
    exact I.mul_mem_right avg (↑u⁻¹) havgI
  exact I.eq_top h1I

/-- **Uniqueness of the trace under the Powers property.** Every continuous unital tracial linear
functional on `reducedGroupCStarAlgebra Γ` agrees with `canonicalTrace Γ`. -/
theorem eq_canonicalTrace_of_hasPowersProperty {Γ : Type*} [Group Γ]
    [MeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSingletonClass Γ]
    (hΓ : HasPowersProperty Γ) (φ : reducedGroupCStarAlgebra Γ →L[ℂ] ℂ)
    (hone : φ 1 = 1) (htrace : ∀ x y, φ (x * y) = φ (y * x))
    (x : reducedGroupCStarAlgebra Γ) :
    φ x = canonicalTrace Γ x := by
  rw [← sub_eq_zero, ← norm_eq_zero]
  refine le_antisymm ?_ (norm_nonneg _)
  refine le_of_forall_pos_le_add fun δ hδ ↦ ?_
  rw [zero_add]
  have hε : 0 < δ / (‖φ‖ + 1) := div_pos hδ (add_pos_of_nonneg_of_pos (norm_nonneg φ) zero_lt_one)
  obtain ⟨N, γ, hN, havg⟩ :=
    exists_norm_average_unitary_conj_sub_canonicalTrace_lt hΓ x hε
  rw [← unitaryConjAverage_apply] at havg
  let avg := unitaryConjAverage (fun j ↦ leftRegularUnitary Γ (γ j)) x
  have hφ_avg : φ avg = φ x :=
    map_unitaryConjAverage_eq hN _ (φ : reducedGroupCStarAlgebra Γ →ₗ[ℂ] ℂ) htrace x
  have hφ_tr : φ (canonicalTrace Γ x • 1) = canonicalTrace Γ x := by
    rw [map_smul, hone, smul_eq_mul, mul_one]
  calc ‖φ x - canonicalTrace Γ x‖
      = ‖φ (avg - canonicalTrace Γ x • 1)‖ := by rw [map_sub, hφ_avg, hφ_tr]
    _ ≤ ‖φ‖ * ‖avg - canonicalTrace Γ x • 1‖ := φ.le_opNorm _
    _ ≤ ‖φ‖ * (δ / (‖φ‖ + 1)) := mul_le_mul_of_nonneg_left havg.le (norm_nonneg φ)
    _ ≤ δ := by
        rw [mul_div_assoc', div_le_iff₀ (by positivity)]
        nlinarith [norm_nonneg φ]

/-- Powers's theorem: the reduced C⋆-algebra of a free group on a basis with two distinct elements
is simple as a ring (every two-sided ideal, closed or not, is `⊥` or `⊤`). -/
theorem reducedFreeGroup_isSimpleRing {ι : Type*}
    [MeasurableSpace (FreeGroup ι)] [MeasurableMul (FreeGroup ι)]
    [MeasurableSingletonClass (FreeGroup ι)]
    (a b : ι) (hab : a ≠ b) :
    IsSimpleRing (reducedGroupCStarAlgebra (FreeGroup ι)) :=
  isSimpleRing_of_hasPowersProperty (FreeGroup.hasPowersProperty_of_ne hab)

/-- Uniqueness of the trace: every continuous unital tracial linear functional (in particular every
tracial state) on the reduced C⋆-algebra of a free group on a basis with two distinct elements
equals the canonical trace `τ(x) = ⟪δ₁, x δ₁⟫_ℂ`. -/
theorem reducedFreeGroup_trace_unique {ι : Type*}
    [MeasurableSpace (FreeGroup ι)] [MeasurableMul (FreeGroup ι)]
    [MeasurableSingletonClass (FreeGroup ι)]
    (a b : ι) (hab : a ≠ b)
    (φ : reducedGroupCStarAlgebra (FreeGroup ι) →L[ℂ] ℂ) (hone : φ 1 = 1)
    (htrace : ∀ x y, φ (x * y) = φ (y * x)) (x : reducedGroupCStarAlgebra (FreeGroup ι)) :
    φ x = ⟪L2.countHilbertBasis ℂ (FreeGroup ι) 1,
      (x : Lp ℂ 2 (Measure.count : Measure (FreeGroup ι)) →L[ℂ]
        Lp ℂ 2 (Measure.count : Measure (FreeGroup ι)))
        (L2.countHilbertBasis ℂ (FreeGroup ι) 1)⟫_ℂ :=
  (eq_canonicalTrace_of_hasPowersProperty (FreeGroup.hasPowersProperty_of_ne hab) φ
    hone htrace x).trans (canonicalTrace_apply x)

end SimplicityAndUniqueTrace

end TauCeti

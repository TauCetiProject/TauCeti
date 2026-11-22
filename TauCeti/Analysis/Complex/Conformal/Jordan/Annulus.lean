/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.UnitInterval
public import TauCeti.Topology.FilledHull
public import TauCeti.Topology.JordanCurve.Basic
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Analysis.Complex.Circle
import TauCeti.Analysis.Complex.Conformal.Jordan.Quadrilateral
import TauCeti.Analysis.Complex.Conformal.Jordan.Schoenflies
import TauCeti.Analysis.Complex.Conformal.PrimeEnd.Crosscut.Decomposition
import TauCeti.Analysis.Complex.PlaneSeparation.Inside
import TauCeti.Analysis.Normed.Module.FilledHull
import TauCeti.Data.Set.InjOnUnion
import TauCeti.Topology.ContinuousMap.Glue.ClosedEmbeddings
import TauCeti.Topology.Frontier
import TauCeti.Topology.Homeomorph.SetCongr
import TauCeti.Topology.MetricSpace.ProperSpace
import TauCeti.Topology.Path.Arc

/-!
# The planar annulus theorem

**Two nested Jordan curves in the plane cobound a closed annulus**: if `C₁` and `C₂` are Jordan
curves in `ℂ` with `C₂` contained in the inside `filledHull C₁ \ C₁` of `C₁`, then the closed
annular region `filledHull C₁ \ (filledHull C₂ \ C₂)` between them is homeomorphic to
`sphere (0 : ℂ) 1 × I`, carrying the end `sphere (0 : ℂ) 1 × {0}` onto `C₁` and the end
`sphere (0 : ℂ) 1 × {1}` onto `C₂`
(`TauCeti.IsJordanCurve.exists_homeomorph_sphere_prod_unitInterval`). Moreover, the parametrization
on the outer boundary `C₁` may be prescribed arbitrarily
(`TauCeti.exists_homeomorph_sphere_prod_unitInterval_of_homeomorph`).

## The argument

1. **Normalization.** Since `C₂ ⊆ filledHull C₁ \ C₁`, its entire filled hull also lies inside
   `filledHull C₁ \ C₁` (`TauCeti.IsJordanCurve.filledHull_subset_filledHull_sdiff`). Choosing a
   point `p₀ ∈ filledHull C₂ \ C₂` and applying the prescribed-boundary Schoenflies theorem
   (`TauCeti.exists_homeomorph_sphere_eq_of_mem`) to `C₁` at `p₀` reduces to the case
   `C₁ = sphere 0 1`, `C₂ ⊆ ball 0 1`, and `0 ∈ filledHull C₂ \ C₂`.

2. **Two radial crosscuts and two disc decompositions.** Along the positive and negative real rays
   from `0` to `±1`, compactness of `C₂` yields last-hit points `p₁ = t₁` and `p₂ = -t₂` with
   `t₁, t₂ ∈ (0, 1)`. The radial segments `J₁` from `1` to `p₁` and `J₂` from `p₂` to `-1` are
   disjoint and meet `C₂` only at `p₁` and `p₂`. Splitting `C₂` at `p₁, p₂` into arcs `γ₁, γ₂`
   produces a crosscut `κ₁ = (J₁.trans γ₁).trans J₂` of `ball 0 1`, which splits `closedBall 0 1`
   into two closed Jordan domains `D⁺, D⁻`
   (`Path.IsCrosscut.filledHull_union_filledHull_eq_closedBall`). The open arc of `γ₂` is connected
   and avoids `κ₁`, so it lies in the inside of one half, say `D⁻`, where it forms a second
   crosscut splitting `D⁻` into `filledHull C₂` and a remaining four-sided closed Jordan domain
   `D⁻'`. Together `D⁺` and `D⁻'` cover `closedBall 0 1 \ (filledHull C₂ \ C₂)` and meet precisely
   along `range J₁ ∪ range J₂`.

3. **Gluing.** The four-sided Jordan domain theorem
   (`TauCeti.exists_homeomorph_unitInterval_prod_filledHull`) identifies `D⁺` and `D⁻'` with
   `I × I` via maps agreeing identically along the common vertical edges `J₁` and `J₂.symm`.
   Parametrizing the upper and lower semicircles by `u ↦ (1 - u.re) / 2` glues the two
   squares into the desired homeomorphism
   `sphere (0 : ℂ) 1 × I ≃ₜ ↥(closedBall 0 1 \ (filledHull C₂ \ C₂))`.

## Main results

* `TauCeti.exists_homeomorph_sphere_prod_unitInterval_of_homeomorph`: **the planar annulus
  theorem** with prescribed outer boundary parametrization.
* `TauCeti.IsJordanCurve.exists_homeomorph_sphere_prod_unitInterval`: **the planar annulus
  theorem**.

## References

* A. Schoenflies, *Beiträge zur Theorie der Punktmengen. III*, Math. Ann. 62 (1906), 286–328.
* E. E. Moise, *Geometric Topology in Dimensions 2 and 3*, Springer GTM 47 (1977), Chapter 10.
-/

public section

noncomputable section

open Function Metric Set Topology unitInterval

namespace TauCeti

/-! ### Normalized planar annulus theorem -/

section Normalized

/-- Set-level decomposition behind `split_second_half`: cutting `Db` along `γ₂` inside
`U = Da ∪ Db` isolates `F` from `Db'`, leaving `Da` and `Db'` covering `U \ (F \ C)` with
intersection `J₁ ∪ J₂`. -/
private theorem sdiff_filledHull_decomposition {α : Type*}
    {Da Db Db' F U C γ₁ γ₂ J₁ J₂ κ : Set α} {p₁ p₂ : α}
    (hD_union : Da ∪ Db = U) (hD_inter : Da ∩ Db = κ)
    (hDb_union : F ∪ Db' = Db) (hDb_inter : F ∩ Db' = γ₂)
    (hF_inside : F \ C ⊆ Db \ κ)
    (hκ_eq : κ = J₁ ∪ γ₁ ∪ J₂) (hγu : γ₁ ∪ γ₂ = C) (hγi : γ₁ ∩ γ₂ = {p₁, p₂})
    (hp₁J₁ : p₁ ∈ J₁) (hp₂J₂ : p₂ ∈ J₂)
    (hγ₁F : γ₁ ⊆ F) (hJ₁Db' : J₁ ⊆ Db') (hJ₂Db' : J₂ ⊆ Db') :
    Da ∪ Db' = U \ (F \ C) ∧ Da ∩ Db' = J₁ ∪ J₂ := by
  have hDb'_sub : Db' ⊆ Db := hDb_union ▸ subset_union_right
  have hκDa : κ ⊆ Da := hD_inter ▸ inter_subset_left
  have hγ₂C : γ₂ ⊆ C := hγu ▸ subset_union_right
  have hγ₂Db' : γ₂ ⊆ Db' := hDb_inter ▸ inter_subset_right
  have hγ₁Da : γ₁ ⊆ Da := (subset_union_right.trans subset_union_left).trans (hκ_eq ▸ hκDa)
  have hJ₁Da : J₁ ⊆ Da := (subset_union_left.trans subset_union_left).trans (hκ_eq ▸ hκDa)
  have hJ₂Da : J₂ ⊆ Da := subset_union_right.trans (hκ_eq ▸ hκDa)
  refine ⟨Subset.antisymm ?_ ?_, Subset.antisymm ?_ ?_⟩
  · refine union_subset ?_ ?_
    · intro z hz
      refine ⟨hD_union ▸ Or.inl hz, fun hzC => ?_⟩
      have hzW := hF_inside hzC
      exact hzW.2 (hD_inter ▸ ⟨hz, hzW.1⟩)
    · intro z hz
      refine ⟨hD_union ▸ Or.inr (hDb'_sub hz), fun hzC => ?_⟩
      exact hzC.2 (hγ₂C (hDb_inter ▸ ⟨hzC.1, hz⟩))
  · intro z ⟨hzU, hznot⟩
    rcases hD_union.symm.subset hzU with hzA | hzB
    · exact Or.inl hzA
    · rcases hDb_union.symm.subset hzB with hzF | hzB'
      · have hzCmem : z ∈ C := by_contra fun h => hznot ⟨hzF, h⟩
        rcases hγu.symm.subset hzCmem with hz1 | hz2
        · exact Or.inl (hγ₁Da hz1)
        · exact Or.inr (hγ₂Db' hz2)
      · exact Or.inr hzB'
  · intro z ⟨hzA, hzB'⟩
    have hzκ : z ∈ J₁ ∪ γ₁ ∪ J₂ := hκ_eq ▸ hD_inter ▸ ⟨hzA, hDb'_sub hzB'⟩
    rcases hzκ with (hzJ₁ | hzγ₁) | hzJ₂
    · exact Or.inl hzJ₁
    · have hzγ₂ : z ∈ γ₂ := hDb_inter ▸ ⟨hγ₁F hzγ₁, hzB'⟩
      rcases (hγi ▸ ⟨hzγ₁, hzγ₂⟩ : z ∈ ({p₁, p₂} : Set α)) with rfl | rfl
      · exact Or.inl hp₁J₁
      · exact Or.inr hp₂J₂
    · exact Or.inr hzJ₂
  · rintro z (hz | hz)
    · exact ⟨hJ₁Da hz, hJ₁Db' hz⟩
    · exact ⟨hJ₂Da hz, hJ₂Db' hz⟩

/-- Concatenating three injective paths whose adjacent pairs meet only at their shared endpoints
and whose outer ranges are disjoint yields an injective path. -/
private theorem injective_trans_trans {X : Type*} [TopologicalSpace X] {a b c d : X}
    {α : Path a b} {β : Path b c} {γ : Path c d}
    (hα : Injective α) (hβ : Injective β) (hγ : Injective γ)
    (hαβ : range α ∩ range β = {b}) (hβγ : range β ∩ range γ = {c})
    (hαγ : Disjoint (range α) (range γ)) :
    Injective ((α.trans β).trans γ) := by
  refine Path.injective_trans (Path.injective_trans hα hβ hαβ) hγ ?_
  rwa [Path.trans_range, union_inter_distrib_right, hαγ.inter_eq, empty_union]

/-- On either real ray `{s * r | r ≥ 0}` (`s = ±1`), a Jordan curve `C ⊆ ball 0 1` enclosing `0`
has a last intersection point at some radius `t ∈ (0, 1)`, giving an injective radial segment from
`s` to that point lying in `closedBall 0 1` and meeting `sphere 0 1` and `C` only at its
endpoints. -/
private theorem exists_signed_radial_segment {C : Set ℂ} (hC : IsJordanCurve C)
    (hCb : C ⊆ ball 0 1) (h0 : (0 : ℂ) ∈ filledHull C \ C) {s : ℝ} (hs : s = 1 ∨ s = -1) :
    ∃ (t : ℝ) (p : ℂ) (J : Path (s : ℂ) p),
      0 < t ∧ t < 1 ∧ p = ((s * t : ℝ) : ℂ) ∧ p ∈ C ∧ Injective J ∧
      range J ⊆ closedBall 0 1 ∧ range J ∩ sphere 0 1 = {(s : ℂ)} ∧
      range J ∩ C = {p} ∧ ∀ z ∈ range J, t ≤ s * z.re := by
  have hsabs : |s| = 1 := by rcases hs with rfl | rfl <;> norm_num
  have hssq : s * s = 1 := by rcases hs with rfl | rfl <;> norm_num
  let f : ℝ → ℂ := fun r => ((s * r : ℝ) : ℂ)
  have hfc : Continuous f := by fun_prop
  have hnorm {r : ℝ} (hr : 0 ≤ r) : ‖f r‖ = r := by
    simp only [f, Complex.norm_real, Real.norm_eq_abs, abs_mul, hsabs, one_mul, abs_of_nonneg hr]
  set S : Set ℝ := {r : ℝ | 0 ≤ r ∧ f r ∈ C}
  have hSlt {r : ℝ} (hr : r ∈ S) : r < 1 := by
    have hlt : ‖f r‖ < 1 := mem_ball_zero_iff.mp (hCb hr.2)
    linarith [hnorm hr.1]
  have hSsub : S ⊆ Icc 0 1 := fun _ hr => ⟨hr.1, (hSlt hr).le⟩
  have hSclosed : IsClosed S := isClosed_Ici.inter (hC.isClosed.preimage hfc)
  have hScomp : IsCompact S := isCompact_Icc.of_isClosed_subset hSclosed hSsub
  have hSne : S.Nonempty := by
    have h1not : f 1 ∉ filledHull C := by
      intro hmem
      have hlt : ‖f 1‖ < 1 := mem_ball_zero_iff.mp (hC.isCompact.filledHull_subset_ball hCb hmem)
      simp [f, hsabs] at hlt
    have hconn : IsPreconnected (f '' Icc 0 1) :=
      isPreconnected_Icc.image f hfc.continuousOn
    obtain ⟨z, ⟨r, hr, rfl⟩, hfr⟩ := hconn.inter_frontier_nonempty
      ⟨f 0, mem_image_of_mem f ⟨le_rfl, zero_le_one⟩, by simpa [f] using h0.1⟩
      ⟨f 1, mem_image_of_mem f ⟨zero_le_one, le_rfl⟩, h1not⟩
    rw [hC.frontier_filledHull] at hfr
    exact ⟨r, hr.1, hfr⟩
  obtain ⟨t, htS, htmax⟩ := hScomp.exists_isMaxOn hSne continuous_id.continuousOn
  have htpos : 0 < t := lt_of_le_of_ne htS.1 fun h0t => by
    subst h0t
    exact h0.2 (by simpa [f] using htS.2)
  have htlt : t < 1 := hSlt htS
  have hpC : f t ∈ C := htS.2
  have htmax' : ∀ r : ℝ, t < r → f r ∉ C := fun r hr hmem => by
    have hle : r ≤ t := htmax ⟨htpos.le.trans hr.le, hmem⟩
    linarith
  set p : ℂ := f t
  have hp_ne : (s : ℂ) ≠ p := fun h => by
    have hre := congrArg (fun z : ℂ => s * z.re) h
    simp only [p, f, Complex.ofReal_re, ← mul_assoc, hssq, one_mul] at hre
    linarith
  set J : Path (s : ℂ) p := Path.segment (s : ℂ) p
  have hJ_eval (r : I) : J r = ((s * ((1 - (r : ℝ)) + (r : ℝ) * t) : ℝ) : ℂ) := by
    simp [J, Path.segment, AffineMap.lineMap_apply, p, f]
    ring
  have hJ_cb : range J ⊆ closedBall 0 1 := by
    rw [Path.range_segment]
    refine (convex_closedBall (0 : ℂ) 1).segment_subset ?_ (ball_subset_closedBall (hCb hpC))
    simp [Complex.norm_real, Real.norm_eq_abs, hsabs]
  have hJ_re {z : ℂ} (hz : z ∈ range J) : t ≤ s * z.re := by
    rcases hz with ⟨r, rfl⟩
    rw [hJ_eval, Complex.ofReal_re, ← mul_assoc, hssq, one_mul]
    nlinarith [r.property.1, r.property.2]
  have hJ_S : range J ∩ sphere 0 1 = {(s : ℂ)} := by
    refine Subset.antisymm ?_
      (singleton_subset_iff.mpr ⟨J.source_mem_range, by simp [hsabs]⟩)
    rintro z ⟨hzJ, hzS⟩
    rw [Path.range_segment] at hzJ
    by_cases hzs : z = (s : ℂ)
    · exact mem_singleton_iff.mpr hzs
    have hzp : z ≠ p := fun h =>
      sphere_disjoint_ball.notMem_of_mem_left hzS (h ▸ hCb hpC)
    have hz_open := mem_openSegment_of_ne_left_right (Ne.symm hzs) (Ne.symm hzp) hzJ
    have hball : z ∈ ball (0 : ℂ) 1 :=
      openSegment_subset_ball_of_ne (by simp [hsabs]) (ball_subset_closedBall (hCb hpC)) hp_ne
        hz_open
    exact (sphere_disjoint_ball.notMem_of_mem_left hzS hball).elim
  have hJ_C : range J ∩ C = {p} := by
    refine Subset.antisymm ?_ (singleton_subset_iff.mpr ⟨J.target_mem_range, hpC⟩)
    rintro z ⟨⟨r, rfl⟩, hzC⟩
    rw [mem_singleton_iff]
    by_cases hr1 : (r : ℝ) = 1
    · have : r = 1 := Subtype.ext hr1
      subst this; exact J.target
    · have hlt : (r : ℝ) < 1 := lt_of_le_of_ne r.property.2 hr1
      have hgt : t < (1 - (r : ℝ)) + (r : ℝ) * t := by nlinarith
      exact (htmax' _ hgt (by dsimp only [f]; rw [← hJ_eval r]; exact hzC)).elim
  exact ⟨t, p, J, htpos, htlt, rfl, hpC, Path.segment_injective_of_ne hp_ne, hJ_cb, hJ_S, hJ_C,
    fun _ => hJ_re⟩

/-- Second crosscut decomposition: given the first crosscut `κ₁ = (J₁.trans γ₁).trans J₂` splitting
`closedBall 0 1` into `Dₐ` (bounded by `κ₁` and `σₐ`) and `D_b` (bounded by `κ₁` and `σ_b`), if the
open arc `γ₂ '' Ioo 0 1` lies inside the open domain `W_b = D_b \ (range κ₁ ∪ range σ_b)`, then
cutting `W_b` along `γ₂` isolates `filledHull C` from the complementary four-sided domain `D_b'`, so
that `Dₐ` and `D_b'` cover `closedBall 0 1 \ (filledHull C \ C)` and meet precisely along
`range J₁ ∪ range J₂`. -/
private theorem split_second_half {C : Set ℂ} {p₁ p₂ : ℂ}
    {J₁ : Path (1 : ℂ) p₁} {J₂ : Path p₂ (-1 : ℂ)}
    {γ₁ γ₂ : Path p₁ p₂} {σₐ σ_b : Path (1 : ℂ) (-1 : ℂ)}
    (hJ₁ : Injective J₁) (hJ₂ : Injective J₂)
    (hγ₁ : Injective γ₁) (hγ₂ : Injective γ₂)
    (hσₐ : Injective σₐ) (hσ_b : Injective σ_b)
    (hJ₁J₂ : Disjoint (range J₁) (range J₂))
    (hJ₁C : range J₁ ∩ C = {p₁}) (hJ₂C : range J₂ ∩ C = {p₂})
    (hJ₁S : range J₁ ∩ sphere 0 1 = {1}) (hJ₂S : range J₂ ∩ sphere 0 1 = {-1})
    (hCb : C ⊆ ball 0 1)
    (hγu : range γ₁ ∪ range γ₂ = C) (hγi : range γ₁ ∩ range γ₂ = {p₁, p₂})
    (hσₐS : range σₐ ⊆ sphere 0 1) (hσ_bS : range σ_b ⊆ sphere 0 1)
    (hσi : range σₐ ∩ range σ_b = {1, -1})
    (hκcut : ((J₁.trans γ₁).trans J₂).IsCrosscut (ball 0 1))
    (hγ₂in : γ₂ '' Ioo 0 1 ⊆
      filledHull (range ((J₁.trans γ₁).trans J₂) ∪ range σ_b) \
        (range ((J₁.trans γ₁).trans J₂) ∪ range σ_b)) :
    let Aₐ := filledHull (range σₐ ∪ range γ₁ ∪ range J₁ ∪ range J₂.symm)
    let A_b := filledHull (range σ_b ∪ range γ₂ ∪ range J₁ ∪ range J₂.symm)
    Aₐ ∪ A_b = closedBall 0 1 \ (filledHull C \ C) ∧
      Aₐ ∩ A_b = range J₁ ∪ range J₂ := by
  set κ₁ : Path (1 : ℂ) (-1 : ℂ) := (J₁.trans γ₁).trans J₂
  have hκ₁_range : range κ₁ = range J₁ ∪ range γ₁ ∪ range J₂ := by
    simp [κ₁, Path.trans_range]
  have hγ₁C : range γ₁ ⊆ C := hγu ▸ subset_union_left
  have hγ₂C : range γ₂ ⊆ C := hγu ▸ subset_union_right
  -- First decomposition: `closedBall 0 1 = Dₐ ∪ D_b` with `Dₐ ∩ D_b = range κ₁`.
  set Jₐ : Set ℂ := range κ₁ ∪ range σₐ
  set J_b : Set ℂ := range κ₁ ∪ range σ_b
  have hJ_b_curve : IsJordanCurve J_b :=
    hκcut.isJordanCurve_range_union_range_of_subset_sphere hσ_b hσ_bS
  have hD_union : filledHull Jₐ ∪ filledHull J_b = closedBall 0 1 :=
    hκcut.filledHull_union_filledHull_eq_closedBall hσₐ hσ_b hσₐS hσ_bS hσi
  have hD_inter : filledHull Jₐ ∩ filledHull J_b = range κ₁ :=
    hκcut.filledHull_inter_filledHull_eq_range_of_subset_sphere hσₐ hσ_b hσₐS hσ_bS hσi
  -- `γ₂` is a crosscut of the open Jordan domain `W_b = filledHull J_b \ J_b`.
  set W_b : Set ℂ := filledHull J_b \ J_b
  have hW_open : IsOpen W_b := hJ_b_curve.isClosed.isOpen_filledHull_sdiff
  have hW_bdd : Bornology.IsBounded W_b :=
    (isBounded_filledHull.mpr hJ_b_curve.isCompact.isBounded).subset sdiff_subset
  have hW_fr : frontier W_b = J_b := hJ_b_curve.frontier_filledHull_sdiff
  have hW_cl : closure W_b = filledHull J_b := hJ_b_curve.closure_filledHull_sdiff
  have hW_frJ : IsJordanCurve (frontier W_b) := hW_fr.symm ▸ hJ_b_curve
  have hp₁Jb : p₁ ∈ J_b := Or.inl (hκ₁_range ▸ Or.inl (Or.inr γ₁.source_mem_range))
  have hp₂Jb : p₂ ∈ J_b := Or.inl (hκ₁_range ▸ Or.inl (Or.inr γ₁.target_mem_range))
  have hγ₂_cut : γ₂.IsCrosscut W_b := Path.isCrosscut_def.mpr
    ⟨hγ₂, hW_fr.symm ▸ hp₁Jb, hW_fr.symm ▸ hp₂Jb, fun t ht => hγ₂in (mem_image_of_mem γ₂ ht)⟩
  -- Build the complementary boundary path `β₂ = (J₁.symm.trans σ_b).trans J₂.symm` of `W_b`.
  have hJ₁_σb : range J₁.symm ∩ range σ_b = {1} := by
    rw [Path.symm_range]
    refine Subset.antisymm ((inter_subset_inter_right _ hσ_bS).trans hJ₁S.subset) ?_
    rintro z rfl
    exact ⟨J₁.source_mem_range, σ_b.source_mem_range⟩
  have hσb_J₂ : range σ_b ∩ range J₂.symm = {-1} := by
    rw [Path.symm_range]
    refine Subset.antisymm ?_ ?_
    · rw [inter_comm]
      exact (inter_subset_inter_right _ hσ_bS).trans hJ₂S.subset
    · rintro z rfl
      exact ⟨σ_b.target_mem_range, J₂.target_mem_range⟩
  set β₂ : Path p₁ p₂ := (J₁.symm.trans σ_b).trans J₂.symm
  have hβ₂_inj : Injective β₂ :=
    injective_trans_trans (Path.injective_symm_iff.mpr hJ₁) hσ_b
      (Path.injective_symm_iff.mpr hJ₂) hJ₁_σb hσb_J₂
      (by rw [Path.symm_range, Path.symm_range]; exact hJ₁J₂)
  have hβ₂_range : range β₂ = range J₁ ∪ range σ_b ∪ range J₂ := by
    simp [β₂, Path.trans_range]
  have hγ₁_fr : range γ₁ ⊆ frontier W_b := by
    rintro z hz
    rw [hW_fr]
    exact Or.inl (hκ₁_range ▸ Or.inl (Or.inr hz))
  have hβ₂_fr : range β₂ ⊆ frontier W_b := by
    rw [hW_fr, hβ₂_range]
    rintro z ((hz | hz) | hz)
    · exact Or.inl (hκ₁_range ▸ Or.inl (Or.inl hz))
    · exact Or.inr hz
    · exact Or.inl (hκ₁_range ▸ Or.inr hz)
  have hγ₁_β₂ : range γ₁ ∩ range β₂ = {p₁, p₂} := by
    rw [hβ₂_range]
    refine Subset.antisymm ?_ ?_
    · rintro z ⟨hz₁, ((hz | hz) | hz)⟩
      · exact Or.inl (mem_singleton_iff.mp (hJ₁C ▸ ⟨hz, hγ₁C hz₁⟩))
      · exact (sphere_disjoint_ball.notMem_of_mem_left (hσ_bS hz)
          (hCb (hγ₁C hz₁))).elim
      · exact Or.inr (mem_singleton_iff.mp (hJ₂C ▸ ⟨hz, hγ₁C hz₁⟩))
    · rintro z (rfl | rfl)
      · exact ⟨γ₁.source_mem_range, Or.inl (Or.inl J₁.target_mem_range)⟩
      · exact ⟨γ₁.target_mem_range, Or.inr J₂.source_mem_range⟩
  -- Apply the second crosscut decomposition to `W_b` along `γ₂`.
  have hC_eq : range γ₂ ∪ range γ₁ = C := by rw [union_comm, hγu]
  have hD_b_union : filledHull C ∪ filledHull (range γ₂ ∪ range β₂) = filledHull J_b := by
    rw [← hC_eq, ← hW_cl]
    exact hγ₂_cut.filledHull_union_filledHull_eq_closure hW_open hW_bdd hW_frJ hγ₁ hβ₂_inj
      hγ₁_fr hβ₂_fr hγ₁_β₂
  have hD_b_inter : filledHull C ∩ filledHull (range γ₂ ∪ range β₂) = range γ₂ := by
    rw [← hC_eq]
    exact hγ₂_cut.filledHull_inter_filledHull_eq_range hW_open hW_bdd hW_frJ hγ₁ hβ₂_inj
      hγ₁_fr hβ₂_fr hγ₁_β₂
  have hC_inside : filledHull C \ C ⊆ filledHull J_b \ range κ₁ := by
    rw [← hC_eq]
    exact ((hγ₂_cut.filledHull_sdiff_subset hW_open hW_bdd hW_frJ hγ₁_fr).trans sdiff_subset).trans
      (sdiff_subset_sdiff_right subset_union_left)
  -- Rewrite the boundary unions to match `Aₐ` and `A_b`.
  have hJₐ_eq : Jₐ = range σₐ ∪ range γ₁ ∪ range J₁ ∪ range J₂.symm := by
    simp only [Jₐ, hκ₁_range, Path.symm_range]
    ext z; simp only [mem_union]; tauto
  have hJ_b'_eq : range γ₂ ∪ range β₂ = range σ_b ∪ range γ₂ ∪ range J₁ ∪ range J₂.symm := by
    simp only [hβ₂_range, Path.symm_range]
    ext z; simp only [mem_union]; tauto
  dsimp only
  rw [← hJₐ_eq, ← hJ_b'_eq]
  exact sdiff_filledHull_decomposition hD_union hD_inter hD_b_union hD_b_inter hC_inside
    hκ₁_range hγu hγi J₁.target_mem_range J₂.source_mem_range
    (fun z hz => subset_filledHull (hγ₁C hz))
    (fun z hz => subset_filledHull (Or.inr (hβ₂_range ▸ Or.inl (Or.inl hz))))
    (fun z hz => subset_filledHull (Or.inr (hβ₂_range ▸ Or.inr hz)))

/-- Gluing two four-sided parametrizations `Φp, Φm : I × I ≃ₜ Ap, Am` that agree on the common
vertical edges `J₁` and `J₂.symm` and map the top edges to the upper and lower semicircles yields a
homeomorphism `sphere (0 : ℂ) 1 × I ≃ₜ ↥(Ap ∪ Am)`. -/
private theorem glue_upper_lower_squares {C : Set ℂ} {p₁ p₂ : ℂ}
    {J₁ : Path (1 : ℂ) p₁} {J₂ : Path p₂ (-1 : ℂ)} {αp αm : Path p₁ p₂}
    {Ap Am : Set ℂ}
    (hαu : range αp ∪ range αm = C)
    (hA_union : Ap ∪ Am = closedBall 0 1 \ (filledHull C \ C))
    (hA_inter : Ap ∩ Am = range J₁ ∪ range J₂)
    (Φp : I × I ≃ₜ Ap) (Φm : I × I ≃ₜ Am)
    (hΦp_top : ∀ s : I, (Φp (s, 0) : ℂ) = upperSemicirclePath s)
    (hΦp_bot : ∀ s : I, (Φp (s, 1) : ℂ) = αp s)
    (hΦp_left : ∀ t : I, (Φp (0, t) : ℂ) = J₁ t)
    (hΦp_right : ∀ t : I, (Φp (1, t) : ℂ) = J₂.symm t)
    (hΦm_top : ∀ s : I, (Φm (s, 0) : ℂ) = lowerSemicirclePath s)
    (hΦm_bot : ∀ s : I, (Φm (s, 1) : ℂ) = αm s)
    (hΦm_left : ∀ t : I, (Φm (0, t) : ℂ) = J₁ t)
    (hΦm_right : ∀ t : I, (Φm (1, t) : ℂ) = J₂.symm t) :
    ∃ Φ : sphere (0 : ℂ) 1 × I ≃ₜ ↥(closedBall (0 : ℂ) 1 \ (filledHull C \ C)),
      (∀ u : sphere (0 : ℂ) 1, (Φ (u, 0) : ℂ) = u) ∧
      (fun p => (Φ p : ℂ)) '' (univ ×ˢ {1}) = C := by
  have hαpC : range αp ⊆ C := hαu ▸ subset_union_left
  have hαmC : range αm ⊆ C := hαu ▸ subset_union_right
  have hH_agree {u : sphere (0 : ℂ) 1} (hu : (u : ℂ).im = 0) (t : I) :
      (Φp (circleParam u, t) : ℂ) = (Φm (circleParam u, t) : ℂ) := by
    rcases (Circle.im_coe_eq_zero_iff (Circle.homeomorphSphere.symm u)).mp (by simpa using hu) with
      h1 | h1
    · have hu1 : (u : ℂ) = 1 := by simpa using congrArg ((↑) : Circle → ℂ) h1
      rw [circleParam_eq_zero_of_coe_eq_one hu1, hΦp_left, hΦm_left]
    · have hu1 : (u : ℂ) = -1 := by simpa using congrArg ((↑) : Circle → ℂ) h1
      rw [circleParam_eq_one_of_coe_eq_neg_one hu1, hΦp_right, hΦm_right]
  let S_up : Set (sphere (0 : ℂ) 1 × I) := {p | 0 ≤ (p.1 : ℂ).im}
  let S_dn : Set (sphere (0 : ℂ) 1 × I) := {p | (p.1 : ℂ).im ≤ 0}
  have hS_up_closed : IsClosed S_up :=
    isClosed_le continuous_const
      (Complex.continuous_im.comp (continuous_subtypeVal.comp continuous_fst))
  have hS_dn_closed : IsClosed S_dn :=
    isClosed_le
      (Complex.continuous_im.comp (continuous_subtypeVal.comp continuous_fst)) continuous_const
  have hcov : range ((↑) : S_up → sphere (0 : ℂ) 1 × I) ∪
      range ((↑) : S_dn → sphere (0 : ℂ) 1 × I) = univ := by
    rw [Subtype.range_coe, Subtype.range_coe]
    ext p
    simpa [S_up, S_dn] using le_total 0 (p.1 : ℂ).im
  let H : C(sphere (0 : ℂ) 1 × I, ℂ) := ContinuousMap.glueClosedEmbeddings
    ⟨fun p => (Φp (circleParam p.val.1, p.val.2) : ℂ),
      continuous_subtypeVal.comp (Φp.continuous.comp
        ((continuous_circleParam.comp (continuous_fst.comp continuous_subtypeVal)).prodMk
          (continuous_snd.comp continuous_subtypeVal)))⟩
    ⟨fun p => (Φm (circleParam p.val.1, p.val.2) : ℂ),
      continuous_subtypeVal.comp (Φm.continuous.comp
        ((continuous_circleParam.comp (continuous_fst.comp continuous_subtypeVal)).prodMk
          (continuous_snd.comp continuous_subtypeVal)))⟩
    hS_up_closed.isClosedEmbedding_subtypeVal hS_dn_closed.isClosedEmbedding_subtypeVal hcov
    (fun ⟨⟨u, t⟩, hu⟩ ⟨⟨u', t'⟩, hu'⟩ h => by
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      exact hH_agree (le_antisymm hu' hu) t)
  have hH_upper {u : sphere (0 : ℂ) 1} (hu : 0 ≤ (u : ℂ).im) (t : I) :
      H (u, t) = (Φp (circleParam u, t) : ℂ) :=
    ContinuousMap.glueClosedEmbeddings_apply_left _ _ _ _ _ _ (⟨(u, t), hu⟩ : S_up)
  have hH_lower {u : sphere (0 : ℂ) 1} (hu : (u : ℂ).im ≤ 0) (t : I) :
      H (u, t) = (Φm (circleParam u, t) : ℂ) :=
    ContinuousMap.glueClosedEmbeddings_apply_right _ _ _ _ _ _ (⟨(u, t), hu⟩ : S_dn)
  have him_zero_of_seam {u : sphere (0 : ℂ) 1} {t : I} (hu : (u : ℂ).im ≤ 0)
      (hmem : (Φm (circleParam u, t) : ℂ) ∈ range J₁ ∪ range J₂) : (u : ℂ).im = 0 := by
    have hparam : circleParam u = 0 ∨ circleParam u = 1 := by
      rcases hmem with ⟨s, hs⟩ | ⟨s, hs⟩
      · exact Or.inl <| congrArg Prod.fst <| Φm.injective <| Subtype.ext <|
          hs.symm.trans (hΦm_left s).symm
      · have heq : (Φm (circleParam u, t) : ℂ) = Φm (1, σ s) := by
          rw [← hs, hΦm_right (σ s), Path.symm_apply, Function.comp_apply, unitInterval.symm_symm]
        exact Or.inr <| congrArg Prod.fst <| Φm.injective <| Subtype.ext heq
    have hu_pm : (u : ℂ) = 1 ∨ (u : ℂ) = -1 := by
      rcases hparam with h0 | h1
      · exact Or.inl <| by rw [← lowerSemicirclePath_circleParam hu, h0, lowerSemicirclePath.source]
      · exact Or.inr <| by rw [← lowerSemicirclePath_circleParam hu, h1, lowerSemicirclePath.target]
    rcases hu_pm with h1 | h1 <;> simp [h1]
  have hH_inj : Injective H := by
    rw [← injOn_univ]
    let S : Bool → Set (sphere (0 : ℂ) 1 × I)
      | false => S_up
      | true => S_dn
    refine injOn_of_subset_iUnion (S := S) ?_ ?_ ?_
    · intro p _
      rcases le_total 0 (p.1 : ℂ).im with hp | hp
      · exact mem_iUnion.2 ⟨false, hp⟩
      · exact mem_iUnion.2 ⟨true, hp⟩
    · intro b
      cases b
      · rintro ⟨u₁, t₁⟩ h1 ⟨u₂, t₂⟩ h2 heq
        rw [hH_upper h1, hH_upper h2] at heq
        obtain ⟨hu_ang, ht⟩ := Prod.mk.inj (Φp.injective (Subtype.ext heq))
        exact Prod.ext (Subtype.ext <| by
          rw [← upperSemicirclePath_circleParam h1, ← upperSemicirclePath_circleParam h2, hu_ang])
          ht
      · rintro ⟨u₁, t₁⟩ h1 ⟨u₂, t₂⟩ h2 heq
        rw [hH_lower h1, hH_lower h2] at heq
        obtain ⟨hu_ang, ht⟩ := Prod.mk.inj (Φm.injective (Subtype.ext heq))
        exact Prod.ext (Subtype.ext <| by
          rw [← lowerSemicirclePath_circleParam h1, ← lowerSemicirclePath_circleParam h2, hu_ang])
          ht
    · intro i j hij ⟨u₁, t₁⟩ ⟨u₂, t₂⟩ h1 h2 heq
      cases i <;> cases j
      · exact absurd hij (by decide)
      · rw [hH_upper h1, hH_lower h2] at heq
        have hmem : (Φm (circleParam u₂, t₂) : ℂ) ∈ range J₁ ∪ range J₂ :=
          hA_inter ▸ ⟨heq ▸ (Φp (circleParam u₁, t₁)).property, (Φm (circleParam u₂, t₂)).property⟩
        exact Or.inr (him_zero_of_seam h2 hmem).ge
      · exact absurd hij (by decide)
      · exact absurd hij (by decide)
  have hH_range : range H = closedBall (0 : ℂ) 1 \ (filledHull C \ C) := by
    rw [← hA_union]
    refine Subset.antisymm ?_ ?_
    · rintro _ ⟨⟨u, t⟩, rfl⟩
      by_cases hu : 0 ≤ (u : ℂ).im
      · rw [hH_upper hu]; exact Or.inl (Φp _).property
      · rw [hH_lower (not_le.mp hu).le]; exact Or.inr (Φm _).property
    · rintro z (hz | hz)
      · obtain ⟨⟨s, t⟩, hst⟩ := Φp.surjective ⟨z, hz⟩
        refine ⟨(⟨upperSemicirclePath s, upperSemicirclePath_mem_sphere s⟩, t), ?_⟩
        rw [hH_upper (u := ⟨upperSemicirclePath s, _⟩) (upperSemicirclePath_im_nonneg s),
          circleParam_upperSemicirclePath]
        exact congrArg Subtype.val hst
      · obtain ⟨⟨s, t⟩, hst⟩ := Φm.surjective ⟨z, hz⟩
        refine ⟨(⟨lowerSemicirclePath s, lowerSemicirclePath_mem_sphere s⟩, t), ?_⟩
        rw [hH_lower (u := ⟨lowerSemicirclePath s, _⟩) (lowerSemicirclePath_im_nonpos s),
          circleParam_lowerSemicirclePath]
        exact congrArg Subtype.val hst
  have hH_emb : IsEmbedding H := (H.continuous.isClosedEmbedding hH_inj).isEmbedding
  let Φ : sphere (0 : ℂ) 1 × I ≃ₜ ↥(closedBall (0 : ℂ) 1 \ (filledHull C \ C)) :=
    hH_emb.toHomeomorph.trans (Homeomorph.setCongr hH_range)
  have hΦ_coe (p : sphere (0 : ℂ) 1 × I) : (Φ p : ℂ) = H p := by
    simp [Φ, Homeomorph.trans_apply, Homeomorph.setCongr_apply]
  refine ⟨Φ, ?_, ?_⟩
  · intro u
    rw [hΦ_coe]
    rcases le_total 0 (u : ℂ).im with hu | hu
    · rw [hH_upper hu, hΦp_top, upperSemicirclePath_circleParam hu]
    · rw [hH_lower hu, hΦm_top, lowerSemicirclePath_circleParam hu]
  · rw [Set.prod_singleton, ← Set.image_comp, Set.image_univ]
    refine Subset.antisymm ?_ ?_
    · rintro _ ⟨u, rfl⟩
      dsimp only [Function.comp_apply]
      rw [hΦ_coe]
      rcases le_total 0 (u : ℂ).im with hu | hu
      · rw [hH_upper hu, hΦp_bot]; exact hαpC (mem_range_self _)
      · rw [hH_lower hu, hΦm_bot]; exact hαmC (mem_range_self _)
    · intro z hz
      rcases hαu.symm.subset hz with ⟨s, rfl⟩ | ⟨s, rfl⟩
      · refine ⟨⟨upperSemicirclePath s, upperSemicirclePath_mem_sphere s⟩, ?_⟩
        dsimp only [Function.comp_apply]
        rw [hΦ_coe, hH_upper (u := ⟨upperSemicirclePath s, _⟩) (upperSemicirclePath_im_nonneg s),
          circleParam_upperSemicirclePath, hΦp_bot]
      · refine ⟨⟨lowerSemicirclePath s, lowerSemicirclePath_mem_sphere s⟩, ?_⟩
        dsimp only [Function.comp_apply]
        rw [hΦ_coe, hH_lower (u := ⟨lowerSemicirclePath s, _⟩) (lowerSemicirclePath_im_nonpos s),
          circleParam_lowerSemicirclePath, hΦm_bot]

/-- **Normalized planar annulus theorem.** If `C ⊆ ball (0 : ℂ) 1` is a Jordan curve with
`0 ∈ filledHull C \ C`, then `closedBall (0 : ℂ) 1 \ (filledHull C \ C)` is homeomorphic to
`sphere (0 : ℂ) 1 × I` by a homeomorphism fixing the outer boundary `sphere (0 : ℂ) 1` pointwise at
`t = 0` and carrying `sphere (0 : ℂ) 1 × {1}` onto `C`. -/
private theorem exists_homeomorph_sphere_prod_unitInterval_normalized {C : Set ℂ}
    (hC : IsJordanCurve C) (hCb : C ⊆ ball 0 1) (h0 : (0 : ℂ) ∈ filledHull C \ C) :
    ∃ Φ : sphere (0 : ℂ) 1 × I ≃ₜ ↥(closedBall (0 : ℂ) 1 \ (filledHull C \ C)),
      (∀ u : sphere (0 : ℂ) 1, (Φ (u, 0) : ℂ) = u) ∧
      (fun p => (Φ p : ℂ)) '' (univ ×ˢ {1}) = C := by
  -- Step 1: Two disjoint radial segments `J₁` and `J₂` joining `±1` to `C`.
  obtain ⟨t₁, p₁, J₁₀, ht₁pos, _, hp₁_eq, hp₁C, hJ₁₀_inj, hJ₁₀_cb, hJ₁₀S, hJ₁₀C, hJ₁₀_re⟩ :=
    exists_signed_radial_segment hC hCb h0 (Or.inl rfl)
  obtain ⟨t₂, p₂, J₂₀, ht₂pos, _, hp₂_eq, hp₂C, hJ₂₀_inj, hJ₂₀_cb, hJ₂₀S, hJ₂₀C, hJ₂₀_re⟩ :=
    exists_signed_radial_segment hC hCb h0 (Or.inr rfl)
  have h1c : ((1 : ℝ) : ℂ) = 1 := Complex.ofReal_one
  have hm1c : ((-1 : ℝ) : ℂ) = -1 := by simp
  let J₁ : Path (1 : ℂ) p₁ := J₁₀.cast h1c.symm rfl
  let J₂₀' : Path (-1 : ℂ) p₂ := J₂₀.cast hm1c.symm rfl
  let J₂ : Path p₂ (-1 : ℂ) := J₂₀'.symm
  have hJ₁_coe : (J₁ : I → ℂ) = J₁₀ := Path.cast_coe J₁₀ h1c.symm rfl
  have hJ₂₀'_coe : (J₂₀' : I → ℂ) = J₂₀ := Path.cast_coe J₂₀ hm1c.symm rfl
  have hJ₁_range : range J₁ = range J₁₀ := by rw [hJ₁_coe]
  have hJ₂_range : range J₂ = range J₂₀ := by rw [Path.symm_range, hJ₂₀'_coe]
  have hJ₁_inj : Injective J₁ := by rw [hJ₁_coe]; exact hJ₁₀_inj
  have hJ₁_cb : range J₁ ⊆ closedBall 0 1 := hJ₁_range ▸ hJ₁₀_cb
  have hJ₁S : range J₁ ∩ sphere 0 1 = {1} := by rw [hJ₁_range, hJ₁₀S, h1c]
  have hJ₁C : range J₁ ∩ C = {p₁} := hJ₁_range ▸ hJ₁₀C
  have hJ₂_inj : Injective J₂ := by rw [Path.injective_symm_iff, hJ₂₀'_coe]; exact hJ₂₀_inj
  have hJ₂_cb : range J₂ ⊆ closedBall 0 1 := hJ₂_range ▸ hJ₂₀_cb
  have hJ₂S : range J₂ ∩ sphere 0 1 = {-1} := by rw [hJ₂_range, hJ₂₀S, hm1c]
  have hJ₂C : range J₂ ∩ C = {p₂} := hJ₂_range ▸ hJ₂₀C
  have hp₁₂ : p₁ ≠ p₂ := fun h => by
    have hre := congrArg Complex.re h
    simp only [hp₁_eq, hp₂_eq, Complex.ofReal_re, one_mul, neg_one_mul] at hre
    linarith
  have hJ₁J₂ : Disjoint (range J₁) (range J₂) := Set.disjoint_left.mpr fun z hz₁ hz₂ => by
    have h1 := hJ₁₀_re z (hJ₁_range ▸ hz₁)
    have h2 := hJ₂₀_re z (hJ₂_range ▸ hz₂)
    linarith
  -- Step 2: Split `C` at `p₁, p₂` into `γ₁, γ₂` and form the crosscut `κ₁ = J₁ · γ₁ · J₂`.
  obtain ⟨γ₁, γ₂, hγ₁_inj, hγ₂_inj, hγu, hγi⟩ :=
    hC.exists_injective_path_range_union_eq_and_inter_eq_pair hp₁C hp₂C hp₁₂
  have hγ₁C : range γ₁ ⊆ C := hγu ▸ subset_union_left
  have hγ₂C : range γ₂ ⊆ C := hγu ▸ subset_union_right
  have hJ₁γ₁ : range J₁ ∩ range γ₁ = {p₁} := by
    refine Subset.antisymm ((inter_subset_inter_right _ hγ₁C).trans hJ₁C.subset) ?_
    exact singleton_subset_iff.mpr ⟨J₁.target_mem_range, γ₁.source_mem_range⟩
  have hγ₁J₂ : range γ₁ ∩ range J₂ = {p₂} := by
    refine Subset.antisymm ?_
      (singleton_subset_iff.mpr ⟨γ₁.target_mem_range, J₂.source_mem_range⟩)
    rw [inter_comm]
    exact (inter_subset_inter_right _ hγ₁C).trans hJ₂C.subset
  set κ₁ : Path (1 : ℂ) (-1 : ℂ) := (J₁.trans γ₁).trans J₂
  have hκ₁_inj : Injective κ₁ :=
    injective_trans_trans hJ₁_inj hγ₁_inj hJ₂_inj hJ₁γ₁ hγ₁J₂ hJ₁J₂
  have hκ₁_range : range κ₁ = range J₁ ∪ range γ₁ ∪ range J₂ := by simp [κ₁, Path.trans_range]
  have hκ₁_cb : range κ₁ ⊆ closedBall 0 1 := by
    rw [hκ₁_range]
    exact union_subset (union_subset hJ₁_cb (hγ₁C.trans (hCb.trans ball_subset_closedBall))) hJ₂_cb
  have hκ₁_S : range κ₁ ∩ sphere 0 1 = {1, -1} := by
    rw [hκ₁_range]
    refine Subset.antisymm ?_ ?_
    · rintro z ⟨((hz | hz) | hz), hzS⟩
      · exact Or.inl (mem_singleton_iff.mp (hJ₁S ▸ ⟨hz, hzS⟩))
      · exact (sphere_disjoint_ball.notMem_of_mem_left hzS (hCb (hγ₁C hz))).elim
      · exact Or.inr (mem_singleton_iff.mp (hJ₂S ▸ ⟨hz, hzS⟩))
    · rintro z (rfl | rfl)
      · exact ⟨Or.inl (Or.inl J₁.source_mem_range), by simp⟩
      · exact ⟨Or.inr J₂.target_mem_range, by simp⟩
  have hfr_ball : frontier (ball (0 : ℂ) 1) = sphere (0 : ℂ) 1 := frontier_ball 0 one_ne_zero
  have hκ₁_cut : κ₁.IsCrosscut (ball 0 1) := Path.isCrosscut_def.mpr
    ⟨hκ₁_inj, by rw [hfr_ball]; simp, by rw [hfr_ball]; simp, fun t ht => by
      obtain ⟨hmem, hnot⟩ := (Path.image_Ioo_eq_range_sdiff_endpoints hκ₁_inj).subset
        (mem_image_of_mem κ₁ ht)
      have hnotS : κ₁ t ∉ sphere (0 : ℂ) 1 := fun hS => hnot (hκ₁_S ▸ ⟨hmem, hS⟩)
      rw [mem_ball_zero_iff]
      exact lt_of_le_of_ne (mem_closedBall_zero_iff.mp (hκ₁_cb hmem))
        (by simpa [mem_sphere_zero_iff_norm] using hnotS)⟩
  -- Step 3: Locate `γ₂ '' Ioo 0 1` on one side of `κ₁`, and split that side along `γ₂`.
  have hσpS : range upperSemicirclePath ⊆ sphere 0 1 :=
    range_subset_iff.mpr upperSemicirclePath_mem_sphere
  have hσmS : range lowerSemicirclePath ⊆ sphere 0 1 :=
    range_subset_iff.mpr lowerSemicirclePath_mem_sphere
  obtain ⟨hWdisj, hWunion⟩ := hκ₁_cut.disjoint_and_union_filledHull_sdiff isOpen_ball isBounded_ball
    (hfr_ball.symm ▸ isJordanCurve_sphere 0 one_pos) upperSemicirclePath_injective
    lowerSemicirclePath_injective (hfr_ball.symm ▸ hσpS) (hfr_ball.symm ▸ hσmS)
    range_upperSemicirclePath_inter_lowerSemicirclePath
  have hJp_curve : IsJordanCurve (range κ₁ ∪ range upperSemicirclePath) :=
    hκ₁_cut.isJordanCurve_range_union_range_of_subset_sphere upperSemicirclePath_injective hσpS
  have hJm_curve : IsJordanCurve (range κ₁ ∪ range lowerSemicirclePath) :=
    hκ₁_cut.isJordanCurve_range_union_range_of_subset_sphere lowerSemicirclePath_injective hσmS
  have hγ₂_open_sub : γ₂ '' Ioo 0 1 ⊆ ball 0 1 \ range κ₁ := by
    intro z hz
    obtain ⟨hzγ₂, hnot⟩ := (Path.image_Ioo_eq_range_sdiff_endpoints hγ₂_inj).subset hz
    refine ⟨hCb (hγ₂C hzγ₂), fun hmem => hnot ?_⟩
    rw [hκ₁_range] at hmem
    rcases hmem with (h | h) | h
    · exact Or.inl (mem_singleton_iff.mp (hJ₁C ▸ ⟨h, hγ₂C hzγ₂⟩))
    · exact hγi ▸ ⟨h, hzγ₂⟩
    · exact Or.inr (mem_singleton_iff.mp (hJ₂C ▸ ⟨h, hγ₂C hzγ₂⟩))
  have hγ₂_conn : IsPreconnected (γ₂ '' Ioo (0 : I) 1) :=
    (isPreconnected_Ioo (a := (0 : I)) (b := 1)).image γ₂ γ₂.continuous.continuousOn
  have hγ₂_side :
      γ₂ '' Ioo 0 1 ⊆
          filledHull (range κ₁ ∪ range lowerSemicirclePath) \
            (range κ₁ ∪ range lowerSemicirclePath) ∨
        γ₂ '' Ioo 0 1 ⊆
          filledHull (range κ₁ ∪ range upperSemicirclePath) \
            (range κ₁ ∪ range upperSemicirclePath) := by
    have hcov : γ₂ '' Ioo 0 1 ⊆
        (filledHull (range κ₁ ∪ range upperSemicirclePath) \
          (range κ₁ ∪ range upperSemicirclePath)) ∪
          (filledHull (range κ₁ ∪ range lowerSemicirclePath) \
            (range κ₁ ∪ range lowerSemicirclePath)) :=
      hWunion ▸ hγ₂_open_sub
    exact (hγ₂_conn.subset_or_subset
      hJp_curve.isClosed.isOpen_filledHull_sdiff hJm_curve.isClosed.isOpen_filledHull_sdiff
      hWdisj hcov).symm
  have hsplit : ∃ αp αm : Path p₁ p₂, Injective αp ∧ Injective αm ∧
      range αp ∪ range αm = C ∧
      filledHull (range upperSemicirclePath ∪ range αp ∪ range J₁ ∪ range J₂.symm) ∪
        filledHull (range lowerSemicirclePath ∪ range αm ∪ range J₁ ∪ range J₂.symm) =
        closedBall 0 1 \ (filledHull C \ C) ∧
      filledHull (range upperSemicirclePath ∪ range αp ∪ range J₁ ∪ range J₂.symm) ∩
        filledHull (range lowerSemicirclePath ∪ range αm ∪ range J₁ ∪ range J₂.symm) =
        range J₁ ∪ range J₂ := by
    rcases hγ₂_side with hside | hside
    · obtain ⟨hu, hi⟩ := split_second_half hJ₁_inj hJ₂_inj hγ₁_inj hγ₂_inj
        upperSemicirclePath_injective lowerSemicirclePath_injective hJ₁J₂ hJ₁C hJ₂C hJ₁S hJ₂S hCb
        hγu hγi hσpS hσmS range_upperSemicirclePath_inter_lowerSemicirclePath hκ₁_cut hside
      exact ⟨γ₁, γ₂, hγ₁_inj, hγ₂_inj, hγu, hu, hi⟩
    · obtain ⟨hu, hi⟩ := split_second_half hJ₁_inj hJ₂_inj hγ₁_inj hγ₂_inj
        lowerSemicirclePath_injective upperSemicirclePath_injective hJ₁J₂ hJ₁C hJ₂C hJ₁S hJ₂S hCb
        hγu hγi hσmS hσpS (by rw [inter_comm, range_upperSemicirclePath_inter_lowerSemicirclePath])
        hκ₁_cut hside
      exact ⟨γ₂, γ₁, hγ₂_inj, hγ₁_inj, by rw [union_comm, hγu],
        by rw [union_comm, hu], by rw [inter_comm, hi]⟩
  obtain ⟨αp, αm, hαp_inj, hαm_inj, hαu, hA_union, hA_inter⟩ := hsplit
  have hαpC : range αp ⊆ C := hαu ▸ subset_union_left
  have hαmC : range αm ⊆ C := hαu ▸ subset_union_right
  -- Step 4: Parametrize both four-sided domains by `I × I` and glue them along `J₁` and `J₂.symm`.
  have hmkSquare {arc : Path (1 : ℂ) (-1 : ℂ)} {α : Path p₁ p₂}
      (harc : Injective arc) (hα : Injective α)
      (harcS : range arc ⊆ sphere 0 1) (hαC : range α ⊆ C) :
      ∃ Φ : I × I ≃ₜ filledHull (range arc ∪ range α ∪ range J₁ ∪ range J₂.symm),
        (∀ s : I, (Φ (s, 0) : ℂ) = arc s) ∧
        (∀ s : I, (Φ (s, 1) : ℂ) = α s) ∧
        (∀ t : I, (Φ (0, t) : ℂ) = J₁ t) ∧
        (∀ t : I, (Φ (1, t) : ℂ) = J₂.symm t) := by
    refine (exists_homeomorph_unitInterval_prod_filledHull harc hα hJ₁_inj
      (Path.injective_symm_iff.mpr hJ₂_inj)
      (sphere_disjoint_ball.mono harcS (hαC.trans hCb))
      (by rwa [Path.symm_range]) ?_ ?_ ?_ ?_).2
    · refine Subset.antisymm ?_
        (singleton_subset_iff.mpr ⟨arc.source_mem_range, J₁.source_mem_range⟩)
      rw [inter_comm]
      exact (inter_subset_inter_right _ harcS).trans hJ₁S.subset
    · rw [Path.symm_range]
      refine Subset.antisymm ?_
        (singleton_subset_iff.mpr ⟨arc.target_mem_range, J₂.target_mem_range⟩)
      rw [inter_comm]
      exact (inter_subset_inter_right _ harcS).trans hJ₂S.subset
    · refine Subset.antisymm ?_ (singleton_subset_iff.mpr ⟨α.source_mem_range, J₁.target_mem_range⟩)
      rw [inter_comm]
      exact (inter_subset_inter_right _ hαC).trans hJ₁C.subset
    · rw [Path.symm_range]
      refine Subset.antisymm ?_ (singleton_subset_iff.mpr ⟨α.target_mem_range, J₂.source_mem_range⟩)
      rw [inter_comm]
      exact (inter_subset_inter_right _ hαC).trans hJ₂C.subset
  obtain ⟨Φp, hΦp_top, hΦp_bot, hΦp_left, hΦp_right⟩ :=
    hmkSquare upperSemicirclePath_injective hαp_inj hσpS hαpC
  obtain ⟨Φm, hΦm_top, hΦm_bot, hΦm_left, hΦm_right⟩ :=
    hmkSquare lowerSemicirclePath_injective hαm_inj hσmS hαmC
  exact glue_upper_lower_squares hαu hA_union hA_inter Φp Φm hΦp_top hΦp_bot hΦp_left hΦp_right
    hΦm_top hΦm_bot hΦm_left hΦm_right

end Normalized

/-! ### The planar annulus theorem -/

/-- **The planar annulus theorem with prescribed outer boundary parametrization.** Let `C₁` and `C₂`
be subsets of `ℂ` with `C₂` a Jordan curve contained in `filledHull C₁ \ C₁`, and let
`φ : sphere (0 : ℂ) 1 ≃ₜ C₁` be any homeomorphism onto `C₁`. Then the closed region
`filledHull C₁ \ (filledHull C₂ \ C₂)` between `C₁` and `C₂` is homeomorphic to
`sphere (0 : ℂ) 1 × I` by a homeomorphism restricting to `φ` on `sphere (0 : ℂ) 1 × {0}` and
carrying `sphere (0 : ℂ) 1 × {1}` onto `C₂`. -/
theorem exists_homeomorph_sphere_prod_unitInterval_of_homeomorph {C₁ C₂ : Set ℂ}
    (hC₂ : IsJordanCurve C₂) (hsub : C₂ ⊆ filledHull C₁ \ C₁)
    (φ : sphere (0 : ℂ) 1 ≃ₜ C₁) :
    ∃ Φ : sphere (0 : ℂ) 1 × I ≃ₜ ↥(filledHull C₁ \ (filledHull C₂ \ C₂)),
      (∀ u : sphere (0 : ℂ) 1, (Φ (u, 0) : ℂ) = φ u) ∧
      (fun p => (Φ p : ℂ)) '' (univ ×ˢ {1}) = C₂ := by
  have hC₁ : IsJordanCurve C₁ :=
    isJordanCurve_iff.mpr ⟨φ.symm.trans (sphereCircleHomeomorph 0 one_pos)⟩
  obtain ⟨p₀, hp₀⟩ := hC₂.nonempty_filledHull_sdiff
  have hp₀₁ : p₀ ∈ filledHull C₁ \ C₁ :=
    hC₁.filledHull_subset_filledHull_sdiff hsub hp₀.1
  obtain ⟨e, he0, heφ, -, heB, heCB⟩ := exists_homeomorph_sphere_eq_of_mem hp₀₁ φ
  set C : Set ℂ := e.symm '' C₂
  have hC : IsJordanCurve C := hC₂.image_homeomorph e.symm
  have hCb : C ⊆ ball 0 1 := by
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨w, hw, hwe⟩ := heB.symm.subset (hsub hz)
    rwa [← hwe, e.symm_apply_apply]
  have hfhC : filledHull C = e.symm '' filledHull C₂ :=
    (e.symm.image_filledHull (fun _ => e.symm.isBounded_image_iff) C₂).symm
  have h0C : (0 : ℂ) ∈ filledHull C \ C := by
    have he0' : e.symm p₀ = 0 := by rw [← he0, e.symm_apply_apply]
    refine ⟨?_, ?_⟩
    · rw [hfhC, ← he0']; exact mem_image_of_mem e.symm hp₀.1
    · rw [← he0', e.symm.injective.mem_set_image]; exact hp₀.2
  obtain ⟨Φ₀, hΦ₀0, hΦ₀1⟩ := exists_homeomorph_sphere_prod_unitInterval_normalized hC hCb h0C
  have himg : e '' (closedBall 0 1 \ (filledHull C \ C)) =
      filledHull C₁ \ (filledHull C₂ \ C₂) := by
    rw [Set.image_sdiff e.injective, Set.image_sdiff e.injective, heCB, hfhC]
    simp [C, image_image]
  let Ψ : ↥(closedBall (0 : ℂ) 1 \ (filledHull C \ C)) ≃ₜ
      ↥(filledHull C₁ \ (filledHull C₂ \ C₂)) :=
    (e.image _).trans (Homeomorph.setCongr himg)
  have hΨ_coe (x) : (Ψ x : ℂ) = e x := by
    simp [Ψ, Homeomorph.trans_apply, Homeomorph.setCongr_apply]
  refine ⟨Φ₀.trans Ψ, ?_, ?_⟩
  · intro u
    rw [Homeomorph.trans_apply, hΨ_coe, hΦ₀0 u, heφ u]
  · have hcoe : (fun p : sphere (0 : ℂ) 1 × I => ((Φ₀.trans Ψ) p : ℂ)) =
        e ∘ (fun p => (Φ₀ p : ℂ)) :=
      funext fun p => by simp [Homeomorph.trans_apply, hΨ_coe]
    rw [hcoe, image_comp, hΦ₀1]
    simp [C, image_image]

/-- **The planar annulus theorem.** If `C₁` and `C₂` are Jordan curves in `ℂ` with
`C₂ ⊆ filledHull C₁ \ C₁`, then the closed region `filledHull C₁ \ (filledHull C₂ \ C₂)` between
them is homeomorphic to `sphere (0 : ℂ) 1 × I`, carrying `sphere (0 : ℂ) 1 × {0}` onto `C₁` and
`sphere (0 : ℂ) 1 × {1}` onto `C₂`. -/
theorem IsJordanCurve.exists_homeomorph_sphere_prod_unitInterval {C₁ C₂ : Set ℂ}
    (hC₁ : IsJordanCurve C₁) (hC₂ : IsJordanCurve C₂) (hsub : C₂ ⊆ filledHull C₁ \ C₁) :
    ∃ Φ : sphere (0 : ℂ) 1 × I ≃ₜ ↥(filledHull C₁ \ (filledHull C₂ \ C₂)),
      (fun p => (Φ p : ℂ)) '' (univ ×ˢ {0}) = C₁ ∧
      (fun p => (Φ p : ℂ)) '' (univ ×ˢ {1}) = C₂ := by
  obtain ⟨e₁⟩ := isJordanCurve_iff.mp hC₁
  let φ : sphere (0 : ℂ) 1 ≃ₜ C₁ := (sphereCircleHomeomorph 0 one_pos).trans e₁.symm
  obtain ⟨Φ, hΦ0, hΦ1⟩ :=
    exists_homeomorph_sphere_prod_unitInterval_of_homeomorph hC₂ hsub φ
  refine ⟨Φ, ?_, hΦ1⟩
  rw [Set.prod_singleton, ← Set.image_comp, Set.image_univ]
  have h : (fun p => (Φ p : ℂ)) ∘ (fun u : sphere (0 : ℂ) 1 => (u, (0 : I))) = Subtype.val ∘ φ :=
    funext hΦ0
  rw [h, φ.surjective.range_comp, Subtype.range_coe]

end TauCeti

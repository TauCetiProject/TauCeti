/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.Bases.TOrthogonal
public import TauCeti.Topology.MetricSpace.SphericallyComplete

/-!
# Best approximation and orthogonal bases

Over a spherically complete nonarchimedean field, a finite orthogonal span admits best
approximations. Nested balls in the scalar coordinates give an approximation attaining the
infimum, even when the residue field is infinite and bounded balls need not be compact.
This is the exact, rather than approximate, Gram–Schmidt step. A maximal finite orthogonal
family therefore gives an orthogonal basis in every finite-dimensional space. Complete fields
with discrete value group satisfy the spherical completeness hypothesis; no condition on the
values of the module norm is needed.

## References

* P. Schneider, *Nonarchimedean Functional Analysis*, Springer, 2002, §§3–4.
* C. Perez-Garcia and W. H. Schikhof, *Locally Convex Spaces over Non-Archimedean Valued
  Fields*, Cambridge University Press, 2010, Chapter 2.
-/

public section

open Set Submodule Filter Metric Topology

namespace TauCeti

variable {K E I : Type*} [NormedField K] [IsUltrametricDist K]
  [SphericallyCompleteSpace K] [NormedAddCommGroup E] [NormedSpace K E]
  [IsUltrametricDist E] [Finite I]

/-- A finite orthogonal family of nonzero vectors over a spherically complete field has a
span admitting a best approximation to every vector of the ambient space. -/
theorem IsTOrthogonalFamily.exists_forall_norm_sub_le {e : I → E}
    (he : IsTOrthogonalFamily K 1 e) (hne : ∀ i, e i ≠ 0) (x : E) :
    ∃ y ∈ span K (range e), ∀ z ∈ span K (range e), ‖x - y‖ ≤ ‖x - z‖ := by
  classical
  let := Fintype.ofFinite I
  let F := span K (range e)
  let D : Set ℝ := range (fun y : F ↦ ‖x - y‖)
  have hD : D.Nonempty := ⟨‖x - (0 : F)‖, 0, rfl⟩
  have hDb : BddBelow D := ⟨0, by rintro _ ⟨y, rfl⟩; exact norm_nonneg _⟩
  obtain ⟨r, hr, hlim, hmem⟩ := exists_seq_tendsto_sInf hD hDb
  choose y hy using fun n ↦ hmem n
  have hyF (n : ℕ) : (y n : E) ∈ span K (range e) := (y n).2
  choose a ha using fun n ↦ (mem_span_range_iff_exists_fun K).1 (hyF n)
  have hr0 (n : ℕ) : 0 ≤ r n := hy n ▸ norm_nonneg _
  -- Orthogonality turns nested error bounds into nested balls in each scalar coordinate.
  have hcoeff (i : I) (m n : ℕ) (hmn : m ≤ n) :
      ‖a n i - a m i‖ * ‖e i‖ ≤ r m := by
    have h := he.mul_norm_smul_le (Finset.mem_univ i) (fun j ↦ a n j - a m j)
    have hsum : ∑ j, (a n j - a m j) • e j = (y n : E) - y m := by
      simp only [sub_smul, Finset.sum_sub_distrib, ha]
    have hdist : ‖(y n : E) - y m‖ ≤ max (r n) (r m) := by
      simpa only [dist_eq_norm, norm_sub_rev (y n : E) x, hy n, hy m] using
        IsUltrametricDist.dist_triangle_max (y n : E) x (y m)
    simp only [NNReal.coe_one, one_mul, norm_smul, hsum] at h
    exact h.trans (hdist.trans (max_le (hr hmn) le_rfl))
  have hex (i : I) : (⋂ n, closedBall (a n i) (r n / ‖e i‖)).Nonempty := by
    refine SphericallyCompleteSpace.nonempty_iInter_closedBall
      (fun n ↦ div_nonneg (hr0 n) (norm_nonneg _)) (antitone_nat_of_succ_le fun n ↦ ?_)
    have hcenter : a (n + 1) i ∈ closedBall (a n i) (r n / ‖e i‖) := by
      rw [mem_closedBall, dist_eq_norm, le_div_iff₀ (norm_pos_iff.2 (hne i))]
      exact hcoeff i n (n + 1) (Nat.le_succ n)
    rw [IsUltrametricDist.closedBall_eq_of_mem hcenter]
    exact closedBall_subset_closedBall (div_le_div_of_nonneg_right (hr n.le_succ) (norm_nonneg _))
  choose c hc using hex
  -- The coordinatewise intersection gives one finite combination within every error bound.
  let z : E := ∑ i, c i • e i
  have hzF : z ∈ F := sum_mem fun i _ ↦ smul_mem _ _ (subset_span (mem_range_self i))
  have hz (n : ℕ) : ‖z - (y n : E)‖ ≤ r n := by
    have hid : z - (y n : E) = ∑ i, (c i - a n i) • e i := by
      simp only [sub_smul, Finset.sum_sub_distrib, ha, z]
    rw [hid]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (hr0 n) fun i _ ↦ ?_
    rw [norm_smul]
    exact (le_div_iff₀ (norm_pos_iff.2 (hne i))).1
      (by simpa [dist_eq_norm] using Set.mem_iInter.1 (hc i) n)
  have hxz (n : ℕ) : ‖x - z‖ ≤ r n := by
    have hbound : ‖x - z‖ ≤ max ‖x - (y n : E)‖ ‖z - y n‖ := by
      simpa only [dist_eq_norm, norm_sub_rev (y n : E) z] using
        IsUltrametricDist.dist_triangle_max x (y n : E) z
    exact hbound.trans (max_le (hy n).le (hz n))
  refine ⟨z, hzF, fun w hw ↦ ?_⟩
  exact (ge_of_tendsto hlim (Eventually.of_forall hxz)).trans
    (csInf_le hDb ⟨⟨w, hw⟩, rfl⟩)

/-- A finite-dimensional ultrametric space over a spherically complete field has an
orthogonal basis. The norm need not take values in the scalar value group. -/
theorem exists_basis_isTOrthogonalFamily_one_of_sphericallyComplete [FiniteDimensional K E] :
    ∃ b : Module.Basis (Fin (Module.finrank K E)) K E, IsTOrthogonalFamily K 1 b := by
  classical
  let P : ℕ → Prop := fun n ↦ ∃ e : Fin n → E,
    IsTOrthogonalFamily K 1 e ∧ ∀ i, e i ≠ 0
  have hbound (n : ℕ) (e : Fin n → E) (he : IsTOrthogonalFamily K 1 e)
      (hne : ∀ i, e i ≠ 0) : n ≤ Module.finrank K E := by
    simpa using (he.linearIndependent zero_lt_one hne).fintype_card_le_finrank
  have hzero : P 0 := ⟨Fin.elim0, (by
    rw [isTOrthogonalFamily_def]
    intro s a
    simp), fun i ↦ Fin.elim0 i⟩
  -- A family of largest possible cardinality must span: otherwise a best approximation
  -- lets us adjoin a nonzero vector orthogonal to its span.
  obtain ⟨e, he, hne⟩ := Nat.findGreatest_spec (Nat.zero_le (Module.finrank K E)) hzero
  let n := Nat.findGreatest P (Module.finrank K E)
  have hmax (m : ℕ) (f : Fin m → E) (hf : IsTOrthogonalFamily K 1 f)
      (hf0 : ∀ i, f i ≠ 0) : m ≤ n :=
    Nat.le_findGreatest (hbound m f hf hf0) ⟨f, hf, hf0⟩
  have hspan : span K (range e) = ⊤ := by
    by_contra htop
    obtain ⟨x, hx⟩ := IsConcreteLE.exists_of_lt (lt_top_iff_ne_top.2 htop)
    obtain ⟨y, hy, hbest⟩ := he.exists_forall_norm_sub_le hne x
    have hw0 : x - y ≠ 0 := sub_ne_zero.2 fun h ↦ hx.2 (h ▸ hy)
    have hw : ∀ z ∈ span K (range e), ‖x - y‖ ≤ ‖(x - y) - z‖ := by
      intro z hz
      simpa only [sub_sub] using hbest (y + z) (add_mem hy hz)
    have hcons := he.finCons hw
    have hcons0 : ∀ i, Fin.cons (α := fun _ ↦ E) (x - y) e i ≠ 0 :=
      Fin.cases (by simpa using hw0) (fun i ↦ by simpa using hne i)
    have := hmax (n + 1) _ hcons hcons0
    omega
  let b : Module.Basis (Fin n) K E := .mk (he.linearIndependent zero_lt_one hne) hspan.ge
  have hn : n = Module.finrank K E := by simpa using (Module.finrank_eq_card_basis b).symm
  refine ⟨b.reindex (finCongr hn), ?_⟩
  simpa only [Module.Basis.coe_reindex, b, Module.Basis.coe_mk] using
    he.comp (finCongr hn).symm.injective

/-- Finite-dimensional subspaces of ultrametric spaces over spherically complete fields
admit best approximations, without a compactness assumption. -/
theorem _root_.Submodule.exists_infDist_eq_dist_of_sphericallyComplete
    (F : Submodule K E) [FiniteDimensional K F] (x : E) :
    ∃ y ∈ F, infDist x (F : Set E) = dist x y := by
  obtain ⟨b, hb⟩ := exists_basis_isTOrthogonalFamily_one_of_sphericallyComplete (K := K) (E := F)
  have he := hb.map F.subtypeₗᵢ
  have hspan : span K (range (F.subtypeₗᵢ ∘ b)) = F := by
    have h := congrArg (Submodule.map F.subtype) b.span_eq
    simpa only [Submodule.map_span, ← range_comp, Submodule.map_top,
      Submodule.range_subtype, Submodule.coe_subtypeₗᵢ] using h
  obtain ⟨y, hy, hbest⟩ := he.exists_forall_norm_sub_le
    (fun i h ↦ b.ne_zero i (Subtype.ext h)) x
  rw [hspan] at hy hbest
  exact ⟨y, hy, le_antisymm (infDist_le_dist_of_mem hy)
    ((le_infDist ⟨0, F.zero_mem⟩).2 fun z hz ↦ by
      simpa only [dist_eq_norm] using hbest z hz)⟩

omit [SphericallyCompleteSpace K] in
/-- Every finite-dimensional ultrametric space over a complete discretely normed field has
an orthogonal basis. Neither local compactness nor a discrete module norm is required. -/
theorem exists_basis_isTOrthogonalFamily_one_of_norm_eq_zpow [CompleteSpace K]
    [FiniteDimensional K E] {b : ℝ} (hb : 1 < b)
    (hdiscrete : ∀ a : K, a ≠ 0 → ∃ k : ℤ, ‖a‖ = b ^ k) :
    ∃ e : Module.Basis (Fin (Module.finrank K E)) K E, IsTOrthogonalFamily K 1 e := by
  have : SphericallyCompleteSpace K := sphericallyCompleteSpace_of_dist_eq_zpow hb
    fun x y hxy ↦ by
      simpa only [dist_eq_norm] using
        hdiscrete (x - y) (by simpa only [dist_eq_norm, ne_eq, norm_eq_zero] using hxy)
  exact exists_basis_isTOrthogonalFamily_one_of_sphericallyComplete

end TauCeti

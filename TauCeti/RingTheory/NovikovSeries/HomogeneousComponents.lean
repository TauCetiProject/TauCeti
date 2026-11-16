/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.NovikovSeries.Grading
public import TauCeti.RingTheory.NovikovSeries.Topology
public import Mathlib.Algebra.Group.Torsion
public import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Homogeneous components of Novikov series

Let `f : H → ι` be a degree function on the exponents of Novikov series. The homogeneous pieces
`TauCeti.NovikovSeries.gradeBy R N f i` are independent, but the Novikov ring is in general not
their direct sum: a series whose support meets infinitely many degrees is not a finite sum of
homogeneous series. This file shows that the completion is nevertheless recovered from the
homogeneous pieces through the period topology of `TauCeti.RingTheory.NovikovSeries.Topology`.

* The **homogeneous component** of degree `i` of a series keeps its coefficients at the exponents
  of degree `i` (`TauCeti.NovikovSeries.gradeProj`). It is a continuous projection onto the
  homogeneous piece of degree `i` (`TauCeti.NovikovSeries.continuous_gradeProj`), and every
  homogeneous piece is closed (`TauCeti.NovikovSeries.isClosed_gradeBy`).
* Every series is the sum, convergent in the period topology, of its homogeneous components
  (`TauCeti.NovikovSeries.hasSum_gradeProj`), and this is its only decomposition into a convergent
  sum of homogeneous series (`TauCeti.NovikovSeries.hasSum_iff_eq_gradeProj`). Hence the sum of
  the homogeneous pieces is dense (`TauCeti.NovikovSeries.dense_iSup_gradeBy`).
* A series is a finite sum of homogeneous series exactly when its support meets finitely many
  degrees (`TauCeti.NovikovSeries.mem_iSup_gradeBy_iff_finite`). So the sum of the homogeneous
  pieces is closed exactly when it is everything, and the Novikov ring is the internal direct sum
  of its homogeneous pieces exactly when every series meets finitely many degrees
  (`TauCeti.NovikovSeries.isClosed_iSup_gradeBy_iff`,
  `TauCeti.NovikovSeries.isInternal_gradeBy_iff`).
* For an additive degree `δ : H →+ ι` with values in a torsion-free group and a nontrivial ring of
  coefficients, this happens exactly when the period `N` or the degree `δ` vanishes
  (`TauCeti.NovikovSeries.isInternal_gradeBy_iff_eq_zero_or_eq_zero`). Otherwise some class `C`
  has positive period and nonzero degree, and the geometric series `∑ₙ e^(n C)` meets the
  infinitely many degrees `n δ(C)`.

For the Floer Novikov ring, graded by twice the first Chern number, the last statement says that,
for nontrivial coefficients, the integer direct sum of the homogeneous pieces is the whole ring
only when the first Chern number or the symplectic area vanishes on spherical classes; in general
the ring is the completion of that direct sum, with each series the convergent sum of its
homogeneous components.

## References

* H. Hofer and D. A. Salamon, *Floer homology and Novikov rings*, in *The Floer memorial
  volume*, Progr. Math. 133 (1995), 483–524.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 11.1, on the
  Novikov ring and its grading.
-/

public section

noncomputable section

open Filter Function Set Topology

namespace TauCeti

namespace NovikovSeries

variable {R H ι : Type*}

section Semiring

variable [Semiring R] [AddZeroClass H] {N : H →+ ℝ}

section Proj

variable [DecidableEq ι]

variable (R N) in
/-- The homogeneous component of degree `i` of a Novikov series for the degree function `f`: the
coefficients at exponents of degree `i`, with all other coefficients set to zero. -/
def gradeProj (f : H → ι) (i : ι) : NovikovSeries R H N →ₗ[R] NovikovSeries R H N where
  toFun a := ⟨fun h => if f h = i then a.coeff h else 0, fun C => (a.finite_lt C).subset
    fun h hh => ⟨fun ha => hh.1 (by simp [ha]), hh.2⟩⟩
  map_add' a b := by
    ext h
    by_cases hh : f h = i <;> simp [hh, coeff_add]
  map_smul' r a := by
    ext h
    by_cases hh : f h = i <;> simp [hh, coeff_smul]

/-- The coefficients of the homogeneous component of degree `i`. -/
@[simp]
theorem coeff_gradeProj (f : H → ι) (i : ι) (a : NovikovSeries R H N) (h : H) :
    (gradeProj R N f i a).coeff h = if f h = i then a.coeff h else 0 :=
  (rfl)

/-- The homogeneous component of degree `i` is homogeneous of degree `i`. -/
theorem gradeProj_mem_gradeBy (f : H → ι) (i : ι) (a : NovikovSeries R H N) :
    gradeProj R N f i a ∈ gradeBy R N f i := mem_gradeBy_iff.2 fun h hh => by
  rw [mem_support, coeff_gradeProj] at hh
  by_contra hne
  exact hh (ite_eq_right hne)

/-- A series of degree `i` is its own homogeneous component of degree `i`. -/
theorem gradeProj_eq_self_of_mem_gradeBy {f : H → ι} {i : ι} {a : NovikovSeries R H N}
    (ha : a ∈ gradeBy R N f i) : gradeProj R N f i a = a := by
  ext h
  rw [coeff_gradeProj]
  split_ifs with hh
  · rfl
  · by_contra hne
    exact hh (mem_gradeBy_iff.1 ha (mem_support.2 (Ne.symm hne)))

/-- A series of degree `j` has no homogeneous component of a different degree `i`. -/
theorem gradeProj_eq_zero_of_mem_gradeBy {f : H → ι} {i j : ι} (hij : j ≠ i)
    {a : NovikovSeries R H N} (ha : a ∈ gradeBy R N f j) : gradeProj R N f i a = 0 := by
  ext h
  rw [coeff_gradeProj, coeff_zero]
  split_ifs with hh
  · by_contra hne
    exact hij ((mem_gradeBy_iff.1 ha (mem_support.2 hne) : f h = j).symm.trans hh)
  · rfl

/-- The sum of the homogeneous components of the degrees in a finite set `s` keeps the
coefficients at the exponents whose degree lies in `s`. -/
theorem coeff_sum_gradeProj (f : H → ι) (s : Finset ι) (a : NovikovSeries R H N) (h : H) :
    (∑ i ∈ s, gradeProj R N f i a).coeff h = if f h ∈ s then a.coeff h else 0 := by
  simp [coeff_sum, Finset.sum_ite_eq]

/-- If the degrees of the support of `a` lie in the finite set `s`, then `a` is the sum of its
homogeneous components of the degrees in `s`. -/
theorem sum_gradeProj_eq_self {f : H → ι} {s : Finset ι} {a : NovikovSeries R H N}
    (hs : f '' a.support ⊆ s) : ∑ i ∈ s, gradeProj R N f i a = a := by
  ext h
  rw [coeff_sum_gradeProj]
  split_ifs with hh
  · rfl
  · by_contra hne
    exact hh (hs ⟨h, mem_support.2 (Ne.symm hne), rfl⟩)

end Proj

/-- A series is a finite sum of homogeneous series exactly when its support meets only finitely
many degrees. -/
theorem mem_iSup_gradeBy_iff_finite {f : H → ι} {a : NovikovSeries R H N} :
    a ∈ ⨆ i, gradeBy R N f i ↔ (f '' a.support).Finite := by
  classical
  refine ⟨fun ha => ?_, fun ha => ?_⟩
  · exact Submodule.iSup_induction (motive := fun b => (f '' b.support).Finite) _ ha
      (fun i b hb => (finite_singleton i).subset (image_subset_iff.2 (mem_gradeBy_iff.1 hb)))
      (by simp)
      fun b c hb hc => (hb.union hc).subset
        ((image_mono (support_add_subset b c)).trans (image_union f _ _).subset)
  · rw [← sum_gradeProj_eq_self (f := f) (s := ha.toFinset) (a := a) (by simp)]
    exact Submodule.sum_mem _ fun i _ => Submodule.mem_iSup_of_mem i (gradeProj_mem_gradeBy f i a)

end Semiring

section Ring

variable [Ring R] [AddZeroClass H] {N : H →+ ℝ}

/-- Every homogeneous piece is closed in the period topology: it is cut out by the vanishing of
the coefficients at the exponents of other degrees, each of which is locally constant. -/
theorem isClosed_gradeBy (f : H → ι) (i : ι) :
    IsClosed (gradeBy R N f i : Set (NovikovSeries R H N)) := by
  have heq : (gradeBy R N f i : Set (NovikovSeries R H N)) =
      ⋂ h ∈ (f ⁻¹' {i})ᶜ, {a | a.coeff h = 0} := by
    ext a
    simp only [SetLike.mem_coe, mem_gradeBy_iff, mem_iInter, mem_ofPred_eq]
    exact ⟨fun ha h hh => by_contra fun hne => hh (ha (mem_support.2 hne)),
      fun ha h hh => by_contra fun hne => mem_support.1 hh (ha h hne)⟩
  rw [heq]
  exact isClosed_biInter fun h _ => (isLocallyConstant_coeff h).isClosed_fiber 0
section Proj

variable [DecidableEq ι]

/-- Taking a homogeneous component preserves every subgroup `U_C` of the period filtration. -/
theorem gradeProj_mem_periodFiltration (f : H → ι) (i : ι) {C : ℝ} {a : NovikovSeries R H N}
    (ha : a ∈ periodFiltration R N C) : gradeProj R N f i a ∈ periodFiltration R N C :=
  mem_periodFiltration.2 fun h hh => by
    rw [coeff_gradeProj, mem_periodFiltration.1 ha h hh, ite_self]

/-- Taking a homogeneous component is continuous in the period topology. -/
theorem continuous_gradeProj (f : H → ι) (i : ι) :
    Continuous (gradeProj R N f i) :=
  continuous_of_continuousAt_zero (gradeProj R N f i) <| by
    rw [ContinuousAt, map_zero]
    exact (hasBasis_nhds_zero.tendsto_iff hasBasis_nhds_zero).2 fun C _ =>
      ⟨C, trivial, fun _ ha => gradeProj_mem_periodFiltration f i ha⟩

/-- **Every Novikov series is the sum of its homogeneous components**, convergent in the period
topology: below any period cutoff only finitely many degrees occur in the support. -/
theorem hasSum_gradeProj (f : H → ι) (a : NovikovSeries R H N) :
    HasSum (fun i => gradeProj R N f i a) a := by
  rw [HasSum, SummationFilter.unconditional_filter, tendsto_nhds_iff]
  intro C
  filter_upwards [eventually_ge_atTop ((a.finite_lt C).toFinset.image f)] with s hs h hh
  rw [coeff_sum_gradeProj]
  split_ifs with hhs
  · rfl
  · by_contra hne
    exact hhs (hs (Finset.mem_image_of_mem f ((a.finite_lt C).mem_toFinset.2 ⟨Ne.symm hne, hh⟩)))

/-- **Uniqueness of the homogeneous decomposition.** A family of series of the respective degrees
sums to `a` exactly when it is the family of homogeneous components of `a`. -/
theorem hasSum_iff_eq_gradeProj {f : H → ι} {b : ι → NovikovSeries R H N}
    (hb : ∀ i, b i ∈ gradeBy R N f i) {a : NovikovSeries R H N} :
    HasSum b a ↔ ∀ i, b i = gradeProj R N f i a := by
  refine ⟨fun h i => ?_, fun h => funext h ▸ hasSum_gradeProj f a⟩
  -- The `i`-th component of the sum is the sum of the `i`-th components, which is `b i`.
  have hi : HasSum (fun j => gradeProj R N f i (b j)) (b i) := by
    convert hasSum_ite_eq i (b i) using 2 with j
    by_cases hj : j = i
    · rw [ite_eq_left hj, hj, gradeProj_eq_self_of_mem_gradeBy (hb i)]
    · rw [ite_eq_right hj, gradeProj_eq_zero_of_mem_gradeBy hj (hb j)]
  exact hi.unique (h.map (gradeProj R N f i) (continuous_gradeProj f i))

end Proj

/-- The finite sums of homogeneous series are dense in the period topology. -/
theorem dense_iSup_gradeBy (f : H → ι) :
    Dense ((⨆ i, gradeBy R N f i : Submodule R (NovikovSeries R H N)) :
      Set (NovikovSeries R H N)) := fun a => by
  classical
  have ha := hasSum_gradeProj f a
  rw [HasSum, SummationFilter.unconditional_filter] at ha
  exact mem_closure_of_tendsto ha (Eventually.of_forall fun s =>
    Submodule.sum_mem _ fun i _ => Submodule.mem_iSup_of_mem i (gradeProj_mem_gradeBy f i a))

/-- The homogeneous series span all Novikov series exactly when every series meets only finitely
many degrees. -/
theorem iSup_gradeBy_eq_top_iff {f : H → ι} :
    ⨆ i, gradeBy R N f i = ⊤ ↔ ∀ a : NovikovSeries R H N, (f '' a.support).Finite := by
  simp only [Submodule.eq_top_iff', mem_iSup_gradeBy_iff_finite]

/-- The sum of the homogeneous pieces is closed in the period topology exactly when it is
everything, that is, when every series meets only finitely many degrees. -/
theorem isClosed_iSup_gradeBy_iff {f : H → ι} :
    IsClosed ((⨆ i, gradeBy R N f i : Submodule R (NovikovSeries R H N)) :
      Set (NovikovSeries R H N)) ↔ ∀ a : NovikovSeries R H N, (f '' a.support).Finite := by
  rw [← iSup_gradeBy_eq_top_iff]
  refine ⟨fun h => ?_, fun h => by simp [h]⟩
  rw [← Submodule.coe_eq_univ, ← h.closure_eq, (dense_iSup_gradeBy f).closure_eq]

/-- The Novikov series form the internal direct sum of their homogeneous pieces exactly when
every series meets only finitely many degrees. -/
theorem isInternal_gradeBy_iff [DecidableEq ι] {f : H → ι} :
    DirectSum.IsInternal (gradeBy R N f) ↔ ∀ a : NovikovSeries R H N, (f '' a.support).Finite := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top, iSup_gradeBy_eq_top_iff]
  exact and_iff_right (iSupIndep_gradeBy f)

end Ring

section Additive

variable [Semiring R] [Nontrivial R] [AddGroup H] {N : H →+ ℝ} [AddGroup ι] (δ : H →+ ι)

/-- For an additive degree with values in a torsion-free group, every Novikov series meets only
finitely many degrees exactly when the period or the degree vanishes. -/
theorem forall_finite_image_support_iff [IsAddTorsionFree ι] :
    (∀ a : NovikovSeries R H N, (δ '' a.support).Finite) ↔ N = 0 ∨ δ = 0 := by
  refine ⟨fun h => ?_, fun h a => ?_⟩
  · by_contra hNδ
    push Not at hNδ
    -- Some exponent has nonzero period and nonzero degree: if `δ A ≠ 0` and `N B ≠ 0`, take `A`
    -- unless `N A = 0`, then `B` unless `δ B = 0`, and otherwise `A + B`.
    have hC : ∃ C, N C ≠ 0 ∧ δ C ≠ 0 := by
      obtain ⟨A, hA⟩ := DFunLike.ne_iff.1 hNδ.2
      obtain ⟨B, hB⟩ := DFunLike.ne_iff.1 hNδ.1
      rw [AddMonoidHom.zero_apply] at hA hB
      by_cases hNA : N A = 0
      · by_cases hδB : δ B = 0
        · exact ⟨A + B, by simpa [hNA] using hB, by simpa [hδB] using hA⟩
        · exact ⟨B, hB, hδB⟩
      · exact ⟨A, hNA, hA⟩
    -- Replacing it by its negative if necessary, its period is positive. The geometric series
    -- `∑ₙ e^(n C)` then meets the infinitely many degrees `n δ(C)`.
    obtain ⟨C, hNC, hδC⟩ : ∃ C, 0 < N C ∧ δ C ≠ 0 := by
      obtain ⟨C, hNC, hδC⟩ := hC
      rcases hNC.lt_or_gt with hlt | hlt
      · exact ⟨-C, by simpa using hlt, by simpa using hδC⟩
      · exact ⟨C, hlt, hδC⟩
    refine infinite_range_of_injective (IsAddTorsionFree.nsmul_left_injective hδC) ?_
    have himage : δ '' (geometric N hNC (1 : R)).support = range fun n : ℕ => n • δ C := by
      rw [support_geometric hNC one_ne_zero, ← range_comp]
      exact congrArg range (funext fun n => map_nsmul δ n C)
    exact himage ▸ h _
  · rcases h with rfl | rfl
    · exact (finite_support_of_bddAbove_image ⟨0, by simp [upperBounds]⟩).image _
    · exact (finite_singleton 0).subset (by simp)

end Additive

/-- **Criterion for an internally graded Novikov ring.** For an additive degree with values in a
torsion-free group and nontrivial coefficients, the Novikov series form the internal direct sum of
their homogeneous pieces exactly when the period or the degree vanishes. -/
theorem isInternal_gradeBy_iff_eq_zero_or_eq_zero [Ring R] [Nontrivial R] [AddGroup H]
    {N : H →+ ℝ} [AddGroup ι] [IsAddTorsionFree ι] [DecidableEq ι] (δ : H →+ ι) :
    DirectSum.IsInternal (gradeBy R N δ) ↔ N = 0 ∨ δ = 0 := by
  rw [isInternal_gradeBy_iff, forall_finite_image_support_iff]

end NovikovSeries

end TauCeti

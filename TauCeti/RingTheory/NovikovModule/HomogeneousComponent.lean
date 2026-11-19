/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.NovikovModule.Grading
public import TauCeti.RingTheory.NovikovModule.Topology

/-!
# Homogeneous components of completed combinations

For a degree function `d : S → D` on the generators, the homogeneous pieces
`TauCeti.NovikovModule.gradeBy R F d k` of the completed combinations are not a direct-sum
decomposition of the whole completion: a combination with nonzero coefficients at generators of
infinitely many degrees is not a finite sum of homogeneous ones. This file shows that the
completion is instead the completion of the direct sum of its pieces, for every coefficient ring,
every potential `F : S → ℝ` and every degree function.

The homogeneous component `TauCeti.NovikovModule.homogeneousComponent R F d k a` keeps the
coefficients of `a` at generators of degree `k`. It is a linear projection onto the piece of
degree `k`, vanishing on the pieces of every other degree, so the pieces are independent. It does
not raise potentials, so it is continuous for the potential-cutoff topology and the pieces are
closed. Every completed combination is the unconditionally convergent sum of its homogeneous
components, and a convergent sum of homogeneous combinations, one of each degree, has those
combinations as its components. By
`TauCeti.NovikovModule.summable_iff_finite_setOf_notMem_potentialFiltration`, such a family is
summable exactly when only finitely many of its members have a nonzero coefficient above each
potential cutoff.

The span of the pieces consists of the combinations whose nonzero coefficients occur in finitely
many degrees. It contains the finite combinations and is therefore dense, so it is closed exactly
when it is the whole module. Closedness of each piece does not give closedness of their sum: on
`S = ℕ` with potential `n ↦ -n` and degree `n ↦ n`, the pieces are the lines through the
generators, and the combination with every coefficient `1` is a limit of finite combinations
outside their span.

For graded Novikov modules of capped generators, with degree given by a Conley–Zehnder or
Chern grading, these are the statements that a completed state module, or a completed Floer
chain module, is the filtered completion of its homogeneous part, and that the homogeneous parts
of a limit can be read off coefficientwise.

The component is the analogue for completed combinations of Mathlib's
`MvPowerSeries.homogeneousComponent`, and the closedness argument follows the coefficientwise
description of the potential-cutoff topology in `TauCeti.RingTheory.NovikovModule.Topology`.

## Main definitions

* `TauCeti.NovikovModule.homogeneousComponent R F d k`: the component of degree `k`.

## Main results

* `TauCeti.NovikovModule.iSupIndep_gradeBy`: the homogeneous pieces are independent.
* `TauCeti.NovikovModule.mem_iSup_gradeBy_iff`: the pieces span exactly the combinations with
  nonzero coefficients in finitely many degrees.
* `TauCeti.NovikovModule.isClosed_gradeBy`: each homogeneous piece is closed.
* `TauCeti.NovikovModule.hasSum_homogeneousComponent`: a completed combination is the sum of its
  homogeneous components.
* `TauCeti.NovikovModule.hasSum_iff_forall_homogeneousComponent_eq`: a family of homogeneous
  combinations sums to `a` exactly when it is the family of homogeneous components of `a`.
* `TauCeti.NovikovModule.dense_iSup_gradeBy`, `TauCeti.NovikovModule.isClosed_iSup_gradeBy_iff`:
  the span of the pieces is dense, and closed exactly when it is everything.

## References

* H. Hofer and D. A. Salamon, *Floer homology and Novikov rings*, in *The Floer memorial
  volume*, Progr. Math. 133 (1995), 483–524.
-/

public section

noncomputable section

open Filter Function Set Topology

namespace TauCeti.NovikovModule

variable {R S D : Type*}

section Semiring

variable [Semiring R] {F : S → ℝ} {d : S → D} {k : D} {a : NovikovModule R F}

variable (R F) in
/-- The homogeneous component of degree `k` of a completed combination: it keeps the coefficients
at the generators of degree `k` and replaces every other coefficient by `0`. -/
def homogeneousComponent (d : S → D) (k : D) : NovikovModule R F →ₗ[R] NovikovModule R F where
  toFun a := ⟨(d ⁻¹' {k}).indicator a.val, mem_iff.2 fun C =>
    (finite_gt a C).subset fun _ hs => ⟨(indicator_apply_ne_zero.1 hs.1).2, hs.2⟩⟩
  map_add' _ _ := Subtype.ext (indicator_add' _ _ _)
  map_smul' c _ := Subtype.ext (indicator_const_smul _ c _)

/-- At a generator of degree `k` the component of degree `k` keeps the coefficient. -/
theorem homogeneousComponent_apply_val_of_eq {s : S} (hs : d s = k) :
    (homogeneousComponent R F d k a).val s = a.val s :=
  indicator_of_mem hs _

/-- At a generator of another degree the component of degree `k` vanishes. -/
theorem homogeneousComponent_apply_val_of_ne {s : S} (hs : d s ≠ k) :
    (homogeneousComponent R F d k a).val s = 0 :=
  indicator_of_notMem hs _

/-- The coefficients of a homogeneous component. -/
@[simp]
theorem homogeneousComponent_apply_val [DecidableEq D] (d : S → D) (k : D)
    (a : NovikovModule R F) (s : S) :
    (homogeneousComponent R F d k a).val s = if d s = k then a.val s else 0 := by
  split_ifs with hs
  · exact homogeneousComponent_apply_val_of_eq hs
  · exact homogeneousComponent_apply_val_of_ne hs

/-- A homogeneous component of degree `k` is homogeneous of degree `k`. -/
theorem homogeneousComponent_mem_gradeBy (d : S → D) (k : D) (a : NovikovModule R F) :
    homogeneousComponent R F d k a ∈ gradeBy R F d k :=
  mem_gradeBy_iff.2 fun _ hs => by_contra fun h => hs (homogeneousComponent_apply_val_of_ne h)

/-- A homogeneous combination of degree `k` is its own component of degree `k`. -/
theorem homogeneousComponent_of_mem_gradeBy (ha : a ∈ gradeBy R F d k) :
    homogeneousComponent R F d k a = a := by
  refine Subtype.ext (funext fun s => ?_)
  by_cases hs : d s = k
  · exact homogeneousComponent_apply_val_of_eq hs
  · rw [homogeneousComponent_apply_val_of_ne hs, val_eq_zero_of_mem_gradeBy ha hs]

/-- A homogeneous combination has no component in any other degree. -/
theorem homogeneousComponent_eq_zero_of_mem_gradeBy {j : D} (ha : a ∈ gradeBy R F d j)
    (hjk : j ≠ k) : homogeneousComponent R F d k a = 0 := by
  refine Subtype.ext (funext fun s => ?_)
  by_cases hs : d s = k
  · simp [homogeneousComponent_apply_val_of_eq hs, val_eq_zero_of_mem_gradeBy ha (hs ▸ hjk.symm)]
  · exact homogeneousComponent_apply_val_of_ne hs

/-- A combination is homogeneous of degree `k` exactly when it equals its component of
degree `k`. -/
theorem mem_gradeBy_iff_homogeneousComponent_eq :
    a ∈ gradeBy R F d k ↔ homogeneousComponent R F d k a = a :=
  ⟨homogeneousComponent_of_mem_gradeBy, fun h => h ▸ homogeneousComponent_mem_gradeBy d k a⟩

/-- The component of degree `k` is a projection onto the homogeneous piece of degree `k`. -/
@[simp]
theorem range_homogeneousComponent (d : S → D) (k : D) :
    LinearMap.range (homogeneousComponent R F d k) = gradeBy R F d k :=
  le_antisymm (LinearMap.range_le_iff_comap.2 (eq_top_iff.2 fun a _ =>
      homogeneousComponent_mem_gradeBy d k a))
    fun _ ha => ⟨_, homogeneousComponent_of_mem_gradeBy ha⟩

/-- Taking the component of degree `k` twice is the same as taking it once. -/
@[simp]
theorem homogeneousComponent_homogeneousComponent (d : S → D) (k : D) (a : NovikovModule R F) :
    homogeneousComponent R F d k (homogeneousComponent R F d k a) =
      homogeneousComponent R F d k a :=
  homogeneousComponent_of_mem_gradeBy (homogeneousComponent_mem_gradeBy d k a)

/-- The homogeneous pieces of the completed combinations are independent, for every degree
function. -/
theorem iSupIndep_gradeBy (d : S → D) : iSupIndep (gradeBy R F d) := by
  intro k
  -- The pieces of the other degrees are killed by the component of degree `k`.
  have hle : ⨆ (j) (_ : j ≠ k), gradeBy R F d j ≤ LinearMap.ker (homogeneousComponent R F d k) :=
    iSup₂_le fun _ hj _ ha => homogeneousComponent_eq_zero_of_mem_gradeBy ha hj
  refine (Submodule.disjoint_def.2 fun a ha ha' => ?_).mono_right hle
  rw [← homogeneousComponent_of_mem_gradeBy ha]
  exact ha'

/-- The coefficients of a finite sum of homogeneous components. -/
theorem sum_homogeneousComponent_apply_val [DecidableEq D] (d : S → D) (T : Finset D)
    (a : NovikovModule R F) (s : S) :
    (∑ k ∈ T, homogeneousComponent R F d k a).val s = if d s ∈ T then a.val s else 0 := by
  simp [Finset.sum_apply, Finset.sum_ite_eq]

/-- A combination is the sum of its components over any finite set of degrees containing the
degrees of all of its nonzero coefficients. -/
theorem sum_homogeneousComponent {T : Finset D} (hT : ∀ s, a.val s ≠ 0 → d s ∈ T) :
    ∑ k ∈ T, homogeneousComponent R F d k a = a := by
  classical
  refine Subtype.ext (funext fun s => ?_)
  rw [sum_homogeneousComponent_apply_val]
  split_ifs with hs
  · rfl
  · exact (not_not.1 (mt (hT s) hs)).symm

/-- The homogeneous pieces span exactly the combinations whose nonzero coefficients occur at
generators of finitely many degrees. -/
theorem mem_iSup_gradeBy_iff :
    a ∈ ⨆ k, gradeBy R F d k ↔ (d '' Function.support a.val).Finite := by
  refine ⟨fun ha => ?_, fun ha => ?_⟩
  · refine Submodule.iSup_induction (motive := fun b => (d '' Function.support b.val).Finite) _ ha
      (fun k b hb => (finite_singleton k).subset ?_) (by simp) fun b c hb hc => ?_
    · rintro _ ⟨s, hs, rfl⟩
      exact mem_gradeBy_iff.1 hb s hs
    · exact (hb.union hc).subset ((image_mono (support_add _ _)).trans (image_union _ _ _).le)
  · rw [← sum_homogeneousComponent (T := ha.toFinset) fun s hs => ha.mem_toFinset.2 ⟨s, hs, rfl⟩]
    exact Submodule.sum_mem _ fun k _ =>
      Submodule.mem_iSup_of_mem k (homogeneousComponent_mem_gradeBy d k a)

end Semiring

section Ring

variable [Ring R] {F : S → ℝ} {d : S → D} {a : NovikovModule R F}

/-- The component of degree `k` does not raise potentials: it maps `U_C` into `U_C`. -/
theorem homogeneousComponent_mem_potentialFiltration {C : ℝ} (k : D)
    (ha : a ∈ potentialFiltration R F C) :
    homogeneousComponent R F d k a ∈ potentialFiltration R F C := by
  classical
  exact mem_potentialFiltration.2 fun s hs => by
    simp [mem_potentialFiltration.1 ha s hs]

/-- The homogeneous components are continuous for the potential-cutoff topology. -/
theorem continuous_homogeneousComponent (d : S → D) (k : D) :
    Continuous (homogeneousComponent R F d k) :=
  continuous_of_forall_mem_potentialFiltration _ fun C =>
    ⟨C, fun _ ha => homogeneousComponent_mem_potentialFiltration k ha⟩

/-- Each homogeneous piece is closed in the potential-cutoff topology. -/
theorem isClosed_gradeBy (d : S → D) (k : D) :
    IsClosed (gradeBy R F d k : Set (NovikovModule R F)) := by
  have h : (gradeBy R F d k : Set (NovikovModule R F)) =
      {a | homogeneousComponent R F d k a = a} :=
    Set.ext fun _ => mem_gradeBy_iff_homogeneousComponent_eq
  rw [h]
  exact isClosed_eq (continuous_homogeneousComponent d k) continuous_id

/-- Every completed combination is the sum, unconditionally convergent in the potential-cutoff
topology, of its homogeneous components. -/
theorem hasSum_homogeneousComponent (d : S → D) (a : NovikovModule R F) :
    HasSum (fun k => homogeneousComponent R F d k a) a := by
  classical
  rw [HasSum, SummationFilter.unconditional_filter, tendsto_nhds_iff]
  intro C
  -- Above `C` the coefficients of `a` occur in the finitely many degrees of this set.
  have hfin := (finite_gt a C).image d
  filter_upwards [eventually_ge_atTop hfin.toFinset] with T hT s hs
  rw [sum_homogeneousComponent_apply_val]
  split_ifs with hdT
  · rfl
  · by_contra h
    exact hdT (hT (hfin.mem_toFinset.2 ⟨s, ⟨Ne.symm h, hs⟩, rfl⟩))

/-- If homogeneous combinations `b k` of degree `k` sum to `a`, then `b k` is the component of
`a` of degree `k`. -/
theorem homogeneousComponent_eq_of_hasSum {b : D → NovikovModule R F}
    (hb : ∀ k, b k ∈ gradeBy R F d k) (h : HasSum b a) (k : D) :
    homogeneousComponent R F d k a = b k := by
  classical
  have hk : (homogeneousComponent R F d k ∘ b) = fun j => if j = k then b k else 0 := by
    funext j
    split_ifs with hj
    · exact hj ▸ homogeneousComponent_of_mem_gradeBy (hb j)
    · exact homogeneousComponent_eq_zero_of_mem_gradeBy (hb j) hj
  have h' := h.map (homogeneousComponent R F d k) (continuous_homogeneousComponent d k)
  rw [hk] at h'
  exact h'.unique (hasSum_ite_eq k (b k))

/-- A family of combinations `b k`, homogeneous of degree `k`, sums to `a` exactly when each
`b k` is the component of `a` of degree `k`. -/
theorem hasSum_iff_forall_homogeneousComponent_eq {b : D → NovikovModule R F}
    (hb : ∀ k, b k ∈ gradeBy R F d k) :
    HasSum b a ↔ ∀ k, homogeneousComponent R F d k a = b k :=
  ⟨fun h => homogeneousComponent_eq_of_hasSum hb h, fun h =>
    (funext h : (fun k => homogeneousComponent R F d k a) = b) ▸ hasSum_homogeneousComponent d a⟩

/-- The span of the homogeneous pieces is dense: it contains the finite combinations. -/
theorem dense_iSup_gradeBy (d : S → D) :
    Dense ((⨆ k, gradeBy R F d k : Submodule R (NovikovModule R F)) : Set (NovikovModule R F)) :=
  denseRange_ofFinsupp.mono <| by
    rintro _ ⟨x, rfl⟩
    rw [SetLike.mem_coe, mem_iSup_gradeBy_iff,
      show (ofFinsupp F x).val = x from funext (ofFinsupp_apply_val x)]
    exact x.hasFiniteSupport.image d

/-- The span of the homogeneous pieces is closed exactly when it is the whole module, that is,
when every completed combination has nonzero coefficients in only finitely many degrees. -/
theorem isClosed_iSup_gradeBy_iff :
    IsClosed ((⨆ k, gradeBy R F d k : Submodule R (NovikovModule R F)) : Set (NovikovModule R F)) ↔
      ⨆ k, gradeBy R F d k = ⊤ := by
  refine ⟨fun h => ?_, fun h => h ▸ isClosed_univ⟩
  rw [← SetLike.coe_set_eq, Submodule.top_coe, ← h.closure_eq]
  exact (dense_iSup_gradeBy d).closure_eq

end Ring

end TauCeti.NovikovModule

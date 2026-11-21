/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.NovikovModule.Grading
public import TauCeti.RingTheory.NovikovModule.Topology

/-!
# Homogeneous decomposition of completed combinations

For any degree function on the generators, a completed combination has homogeneous components,
obtained by retaining its coefficients in one degree. The finite sums of these components
converge in the potential-cutoff topology: above each cutoff only finitely many generators,
and hence only finitely many degrees, occur.

Each homogeneous piece is closed, but their algebraic sum need not be closed. That sum is dense
and consists exactly of the combinations supported in finitely many degrees. Thus the completion
is the closure of the algebraic sum, not in general an internal direct sum. These results require
neither an additive structure on the degrees nor torsor coordinates for the generators.

The homogeneous pieces are `TauCeti.NovikovModule.gradeBy`, and convergence uses the
potential-cutoff topology of `TauCeti.RingTheory.NovikovModule.Topology`.
-/

public section

noncomputable section

open Filter Function Set Topology

namespace TauCeti.NovikovModule

variable {R S D : Type*}

section Semiring

variable [Semiring R] {F : S → ℝ}

open Classical in
/-- Projection onto the coefficients of degree `k`. -/
def homogeneousComponent (d : S → D) (k : D) :
    NovikovModule R F →ₗ[R] NovikovModule R F where
  toFun a := ⟨fun s => if d s = k then a.val s else 0, mem_iff.mpr fun C =>
    (finite_gt a C).subset fun s hs => by
      by_cases h : d s = k <;> simp_all⟩
  map_add' a b := by
    ext s
    by_cases h : d s = k <;> simp [h]
  map_smul' r a := by
    ext s
    by_cases h : d s = k <;> simp [h]

open Classical in
/-- The coefficient formula for a homogeneous component. -/
@[simp]
theorem homogeneousComponent_apply_val (d : S → D) (k : D)
    (a : NovikovModule R F) (s : S) :
    (homogeneousComponent d k a).val s = if d s = k then a.val s else 0 :=
  (rfl)

/-- A homogeneous component belongs to its homogeneous piece. -/
theorem homogeneousComponent_mem_gradeBy (d : S → D) (k : D) (a : NovikovModule R F) :
    homogeneousComponent d k a ∈ gradeBy R F d k := by
  rw [mem_gradeBy_iff]
  intro s hs
  by_contra h
  exact hs (by simp [h])

open Classical in
/-- Projection fixes the piece of its own degree and kills every other homogeneous piece. -/
theorem homogeneousComponent_of_mem_gradeBy {d : S → D} {j : D}
    {a : NovikovModule R F} (ha : a ∈ gradeBy R F d j) (k : D) :
    homogeneousComponent d k a = if j = k then a else 0 := by
  split_ifs with hjk
  · subst k
    ext s
    by_cases hs : a.val s = 0
    · simp [hs]
    · simp [mem_gradeBy_iff.mp ha s hs]
  · ext s
    by_cases hs : a.val s = 0
    · simp [hs]
    · simp [mem_gradeBy_iff.mp ha s hs, hjk]

/-- Being homogeneous of degree `k` is equivalent to being fixed by its projection. -/
theorem mem_gradeBy_iff_homogeneousComponent_eq_self {d : S → D} {k : D}
    {a : NovikovModule R F} :
    a ∈ gradeBy R F d k ↔ homogeneousComponent d k a = a := by
  constructor
  · intro ha
    simpa using homogeneousComponent_of_mem_gradeBy ha k
  · intro ha
    rw [← ha]
    exact homogeneousComponent_mem_gradeBy d k a

open Classical in
/-- The projections onto degrees are mutually orthogonal idempotents. -/
@[simp]
theorem homogeneousComponent_homogeneousComponent (d : S → D) (j k : D)
    (a : NovikovModule R F) :
    homogeneousComponent d j (homogeneousComponent d k a) =
      if k = j then homogeneousComponent d k a else 0 :=
  homogeneousComponent_of_mem_gradeBy (homogeneousComponent_mem_gradeBy d k a) j

open Classical in
/-- A finite sum of components keeps exactly the coefficients whose degrees are in the sum. -/
@[simp]
theorem sum_homogeneousComponent_apply_val (d : S → D) (t : Finset D)
    (a : NovikovModule R F) (s : S) :
    (∑ k ∈ t, homogeneousComponent d k a).val s =
      if d s ∈ t then a.val s else 0 := by
  classical
  simp [homogeneousComponent_apply_val, Finset.sum_apply]

/-- The algebraic sum consists exactly of combinations supported in finitely many degrees. -/
theorem mem_iSup_gradeBy_iff {d : S → D} {a : NovikovModule R F} :
    a ∈ ⨆ k, gradeBy R F d k ↔ (d '' support a.val).Finite := by
  classical
  constructor
  · intro ha
    refine Submodule.iSup_induction _
      (motive := fun b => (d '' support b.val).Finite) ha (fun k b hb => ?_) (by simp) ?_
    · exact (finite_singleton k).subset (by rintro _ ⟨s, hs, rfl⟩; exact mem_gradeBy_iff.mp hb s hs)
    · intro b c hb hc
      exact (hb.union hc).subset (by
        rintro _ ⟨s, hs, rfl⟩
        by_cases h : b.val s = 0
        · exact Or.inr ⟨s, by simpa [h] using hs, rfl⟩
        · exact Or.inl ⟨s, h, rfl⟩)
  · intro ha
    have heq : (∑ k ∈ ha.toFinset, homogeneousComponent d k a) = a := by
      ext s
      by_cases hs : a.val s = 0
      · simp [hs]
      · simp [ha.mem_toFinset.mpr (mem_image_of_mem d hs)]
    rw [← heq]
    exact Submodule.sum_mem _ fun k _ =>
      Submodule.mem_iSup_of_mem k (homogeneousComponent_mem_gradeBy d k a)

/-- Finite combinations belong to the algebraic sum of the homogeneous pieces. -/
theorem ofFinsupp_mem_iSup_gradeBy (d : S → D) (x : S →₀ R) :
    ofFinsupp F x ∈ ⨆ k, gradeBy R F d k := by
  apply mem_iSup_gradeBy_iff.mpr
  have heq : (ofFinsupp F x).val = x := funext (ofFinsupp_apply_val x)
  rw [heq]
  exact x.hasFiniteSupport.image d

end Semiring

section Ring

variable [Ring R] {F : S → ℝ}

/-- A homogeneous piece is closed for the potential-cutoff topology. -/
theorem isClosed_gradeBy (d : S → D) (k : D) :
    IsClosed (gradeBy R F d k : Set (NovikovModule R F)) := by
  have heq : (gradeBy R F d k : Set (NovikovModule R F)) =
      ⋂ (s : S) (_ : d s ≠ k), {a | a.val s = 0} := by
    ext a
    simp only [Set.mem_iInter, Set.mem_ofPred, SetLike.mem_coe]
    constructor
    · exact fun ha s hs => val_eq_zero_of_mem_gradeBy ha hs
    · intro ha
      rw [mem_gradeBy_iff]
      intro s hs
      by_contra h
      exact hs (ha s h)
  rw [heq]
  exact isClosed_iInter fun s => isClosed_iInter fun _ =>
    (isLocallyConstant_apply_val s).isClosed_fiber 0

/-- Homogeneous projection preserves every potential cutoff. -/
theorem homogeneousComponent_mem_potentialFiltration (d : S → D) (k : D)
    {C : ℝ} {a : NovikovModule R F} (ha : a ∈ potentialFiltration R F C) :
    homogeneousComponent d k a ∈ potentialFiltration R F C := by
  rw [mem_potentialFiltration]
  intro s hs
  simp [mem_potentialFiltration.mp ha s hs]

/-- Each homogeneous projection is continuous for the potential-cutoff topology. -/
@[continuity]
theorem continuous_homogeneousComponent (d : S → D) (k : D) :
    Continuous (homogeneousComponent (R := R) (F := F) d k) :=
  continuous_of_forall_mem_potentialFiltration _ fun C =>
    ⟨C, fun _ ha => homogeneousComponent_mem_potentialFiltration d k ha⟩

/-- Every completed combination is the convergent sum of its homogeneous components. -/
theorem hasSum_homogeneousComponent (d : S → D) (a : NovikovModule R F) :
    HasSum (fun k => homogeneousComponent d k a) a := by
  classical
  apply tendsto_nhds_iff.mpr
  intro C
  let t := ((finite_gt a C).image d).toFinset
  filter_upwards [eventually_ge_atTop t] with u hu s hs
  by_cases h : a.val s = 0
  · simp [h]
  · have hmem : d s ∈ t := by
      exact ((finite_gt a C).image d).mem_toFinset.mpr ⟨s, ⟨h, hs⟩, rfl⟩
    simp [hu hmem]

/-- The algebraic sum of homogeneous pieces is dense in the potential-cutoff topology. -/
theorem dense_iSup_gradeBy (d : S → D) :
    Dense (SetLike.coe (⨆ k, gradeBy R F d k)) :=
  denseRange_ofFinsupp.mono (by
    rintro _ ⟨x, rfl⟩
    exact ofFinsupp_mem_iSup_gradeBy d x)

/-- The algebraic sum is closed exactly when every combination has finitely many nonzero
homogeneous degrees. Individual closed pieces do not imply that their sum is closed. -/
theorem isClosed_iSup_gradeBy_iff (d : S → D) :
    IsClosed (SetLike.coe (⨆ k, gradeBy R F d k)) ↔
      ∀ a : NovikovModule R F, (d '' support a.val).Finite := by
  constructor
  · intro h a
    have htop := h.dense_iff.mp (dense_iSup_gradeBy (R := R) (F := F) d)
    apply mem_iSup_gradeBy_iff.mp
    exact Set.eq_univ_iff_forall.mp htop a
  · intro h
    have htop : (⨆ k, gradeBy R F d k : Submodule R (NovikovModule R F)) = ⊤ :=
      Submodule.eq_top_iff'.mpr fun a => mem_iSup_gradeBy_iff.mpr (h a)
    simp [htop]

end Ring

end TauCeti.NovikovModule

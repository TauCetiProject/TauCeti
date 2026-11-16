/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.NovikovSeries.TopologicalRing
public import Mathlib.Algebra.MonoidAlgebra.Grading
public import Mathlib.Topology.Algebra.Algebra

/-!
# Homogeneous Novikov series

Let `f : H → ι` be a degree function on the exponents of Novikov series. A Novikov series is
*homogeneous of degree `i`* when its support lies in the fibre `f ⁻¹' {i}`. These series form the
submodule `TauCeti.NovikovSeries.gradeBy R N f i`, the Novikov analogue of Mathlib's
`AddMonoidAlgebra.gradeBy`. For an additive degree function the pieces multiply as a graded
monoid, and they are independent. Each homogeneous piece is closed in the period topology, and the
sum of the homogeneous pieces is dense.

Intersecting with the nonnegative subring `TauCeti.NovikovSeries.nonnegSubring` gives the closed
homogeneous submodules `TauCeti.NovikovSeries.nonnegGradeBy S R N f i`. For an additive degree
homomorphism `f : H →+ ι` these pieces form a graded monoid, hence a `DirectSum.GAlgebra`, and
`DirectSum.coeAlgHom` embeds `⨁ i, nonnegGradeBy S R N f i` as a dense graded subalgebra of
`nonnegSubring R N` whose topological closure is the whole nonnegative subring.

Unlike the group ring, neither the Novikov ring nor its nonnegative subring is in general the
algebraic direct sum of its homogeneous pieces: every finite sum of homogeneous series has support
meeting only finitely many fibres of `f`, whereas a completed series may have support meeting
infinitely many fibres with periods tending to `+∞`. The homogeneous pieces of `NovikovSeries`
span exactly the finitely supported series as soon as the period `N` is bounded above on every
fibre of `f`, for instance when `f` is injective. In that case the graded ring spanned by
homogeneous series is the group ring `R[H]`, and the Novikov ring is its period completion. This
is the situation of the coefficient ring of capped Hamiltonian Floer theory on a spherically
monotone symplectic manifold, graded by twice the first Chern number.

## Main definitions

* `TauCeti.NovikovSeries.supported R N s`: the Novikov series supported in the set `s`.
* `TauCeti.NovikovSeries.gradeBy R N f i`: the Novikov series of degree `i` for the degree
  function `f`.
* `TauCeti.NovikovSeries.nonnegSupported S R N s` and
  `TauCeti.NovikovSeries.nonnegGradeBy S R N f i`: the corresponding `S`-submodules of the
  nonnegative subring `nonnegSubring R N`.

## Main results

* `TauCeti.NovikovSeries.gradeBy.gradedMonoid` and
  `TauCeti.NovikovSeries.nonnegGradeBy.gradedMonoid`: for an additive degree function, the
  homogeneous pieces of `NovikovSeries` and of `nonnegSubring` form graded monoids.
* `TauCeti.NovikovSeries.iSupIndep_gradeBy` and
  `TauCeti.NovikovSeries.iSupIndep_nonnegGradeBy`: the homogeneous pieces are independent.
* `TauCeti.NovikovSeries.isClosed_gradeBy` and
  `TauCeti.NovikovSeries.isClosed_nonnegGradeBy`: each homogeneous piece is closed in the period
  topology.
* `TauCeti.NovikovSeries.coeAlgHom_nonnegGradeBy_injective`,
  `TauCeti.NovikovSeries.denseRange_coeAlgHom_nonnegGradeBy`, and
  `TauCeti.NovikovSeries.topologicalClosure_range_coeAlgHom_nonnegGradeBy`: the direct sum of the
  nonnegative homogeneous pieces embeds injectively and densely into `nonnegSubring R N`.
* `TauCeti.NovikovSeries.finite_image_support_of_mem_iSup_gradeBy` and
  `TauCeti.NovikovSeries.finite_image_support_of_mem_iSup_nonnegGradeBy`: a finite sum of
  homogeneous series meets only finitely many degrees.
* `TauCeti.NovikovSeries.ofAddMonoidAlgebra_mem_gradeBy_iff`: the inclusion of the group ring
  preserves and reflects the degree.
* `TauCeti.NovikovSeries.finite_support_of_mem_gradeBy`: a homogeneous series is finitely
  supported when the period is bounded above on its fibre.
* `TauCeti.NovikovSeries.mem_iSup_gradeBy_iff`: if the period is bounded above on every fibre,
  the homogeneous pieces span exactly the finitely supported series.
* `TauCeti.NovikovSeries.eq_single_of_mem_gradeBy`: for an injective degree function, every
  homogeneous series is a monomial.

## References

* H. Hofer and D. A. Salamon, *Floer homology and Novikov rings*, in *The Floer memorial
  volume*, Progr. Math. 133 (1995), 483–524.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, the construction of
  the Novikov ring in the chapter on quantum cohomology.
* K. Fukaya, Y.-G. Oh, H. Ohta, and K. Ono, *Lagrangian Intersection Floer Theory: Anomaly and
  Obstruction*, AMS/IP Studies in Advanced Mathematics 46, 2009, Chapter 2.
-/

public section

noncomputable section

open Function Set

namespace TauCeti

namespace NovikovSeries

variable {S R H ι : Type*}

section Semiring

variable [Semiring R]

section AddZeroClass

variable [AddZeroClass H] {N : H →+ ℝ}

variable (R N) in
/-- The Novikov series supported in the set `s`, the Novikov analogue of `Finsupp.supported`. -/
def supported (s : Set H) : Submodule R (NovikovSeries R H N) where
  carrier := {a | a.support ⊆ s}
  zero_mem' := by simp
  add_mem' ha hb := (support_add_subset _ _).trans (union_subset ha hb)
  smul_mem' r _ ha := (support_smul_subset r _).trans ha

/-- A series lies in `supported R N s` exactly when its support lies in `s`. -/
theorem mem_supported {s : Set H} {a : NovikovSeries R H N} :
    a ∈ supported R N s ↔ a.support ⊆ s :=
  Iff.rfl

variable (R N) in
/-- The Novikov series of degree `i` for the degree function `f`: those whose support lies in
the fibre `f ⁻¹' {i}`. -/
def gradeBy (f : H → ι) (i : ι) : Submodule R (NovikovSeries R H N) :=
  supported R N (f ⁻¹' {i})

/-- A series has degree `i` exactly when its support lies in the fibre over `i`. -/
theorem mem_gradeBy_iff {f : H → ι} {i : ι} {a : NovikovSeries R H N} :
    a ∈ gradeBy R N f i ↔ a.support ⊆ f ⁻¹' {i} :=
  Iff.rfl

/-- The monomial `r e^h` has degree `f h`. -/
theorem single_mem_gradeBy (f : H → ι) (h : H) (r : R) :
    (single h r : NovikovSeries R H N) ∈ gradeBy R N f (f h) := fun _ hg => by
  rw [mem_singleton_iff.1 (support_single_subset h r hg), mem_preimage, mem_singleton_iff]

/-- There are no nonzero series of a degree that no exponent has. -/
theorem gradeBy_eq_bot {f : H → ι} {i : ι} (hi : i ∉ range f) : gradeBy R N f i = ⊥ := by
  refine (Submodule.eq_bot_iff _).2 fun a ha => support_eq_empty.1 ?_
  exact eq_empty_of_forall_notMem fun h hh => hi ⟨h, ha hh⟩

/-- If every exponent has degree `i`, every series is homogeneous of degree `i`. -/
theorem gradeBy_eq_top {f : H → ι} {i : ι} (hf : ∀ h, f h = i) : gradeBy R N f i = ⊤ :=
  Submodule.eq_top_iff'.2 fun _ h _ => hf h

/-- Homogeneous series of different degrees span independent submodules. -/
theorem iSupIndep_gradeBy (f : H → ι) : iSupIndep (gradeBy R N f) := by
  intro i
  -- Every homogeneous piece of degree `j ≠ i` consists of series avoiding the fibre over `i`.
  have hle : ⨆ (j) (_ : j ≠ i), gradeBy R N f j ≤ supported R N (f ⁻¹' {i})ᶜ :=
    iSup₂_le fun j hj a ha h hh => by
      rw [mem_compl_iff, mem_preimage, mem_singleton_iff, (ha hh : f h = j)]
      exact hj
  refine (Submodule.disjoint_def.2 fun a ha ha' => support_eq_empty.1 ?_).mono_right hle
  exact eq_empty_of_forall_notMem fun h hh => ha' hh (ha hh)

/-- Every finite sum of homogeneous Novikov series has support meeting only finitely many
degrees. -/
theorem finite_image_support_of_mem_iSup_gradeBy {f : H → ι} {a : NovikovSeries R H N}
    (ha : a ∈ ⨆ i, gradeBy R N f i) : (f '' a.support).Finite :=
  Submodule.iSup_induction (motive := fun b => (f '' b.support).Finite) _ ha
    (fun i _ hb => (finite_singleton i).subset
      ((image_mono hb).trans (image_preimage_subset f {i})))
    (by simp)
    fun b c hb hc => (hb.union hc).subset
      ((image_mono (support_add_subset b c)).trans (image_union f _ _).le)

/-- A homogeneous series is finitely supported if the period is bounded above on its fibre. -/
theorem finite_support_of_mem_gradeBy {f : H → ι} {i : ι} (hf : BddAbove (N '' (f ⁻¹' {i})))
    {a : NovikovSeries R H N} (ha : a ∈ gradeBy R N f i) : a.support.Finite :=
  finite_support_of_bddAbove_image (hf.mono (image_mono ha))

/-- A finitely supported series is a finite sum of homogeneous series. -/
theorem ofFinsupp_mem_iSup_gradeBy (f : H → ι) (x : H →₀ R) :
    ofFinsupp x ∈ ⨆ i, gradeBy R N f i := by
  induction x using Finsupp.induction with
  | zero => simp
  | single_add h r x _ _ hx =>
    rw [map_add, ofFinsupp_single]
    exact add_mem (Submodule.mem_iSup_of_mem (f h) (single_mem_gradeBy f h r)) hx

/-- If the period is bounded above on every fibre of the degree function, the homogeneous series
span exactly the finitely supported series. -/
theorem mem_iSup_gradeBy_iff {f : H → ι} (hf : ∀ i, BddAbove (N '' (f ⁻¹' {i})))
    {a : NovikovSeries R H N} : a ∈ ⨆ i, gradeBy R N f i ↔ a.support.Finite := by
  refine ⟨fun ha => ?_, fun ha => ?_⟩
  · exact Submodule.iSup_induction (motive := fun b => b.support.Finite) _ ha
      (fun i _ hb => finite_support_of_mem_gradeBy (hf i) hb) (by simp)
      fun _ _ hb hc => (hb.union hc).subset (support_add_subset _ _)
  · obtain ⟨x, rfl⟩ := mem_range_ofFinsupp_iff.2 ha
    exact ofFinsupp_mem_iSup_gradeBy f x

/-- For an injective degree function, a series of the degree of `h` is the monomial at `h`
with its own coefficient. -/
theorem eq_single_of_mem_gradeBy {f : H → ι} (hf : Injective f) {h : H}
    {a : NovikovSeries R H N} (ha : a ∈ gradeBy R N f (f h)) : a = single h (a.coeff h) := by
  ext g
  by_cases hg : g = h
  · rw [hg, coeff_single_same]
  · rw [coeff_single_of_ne hg]
    by_contra hag
    exact hg (hf (ha (mem_support.2 hag)))

end AddZeroClass

/-- For an additive degree function, the homogeneous Novikov series form a graded monoid. -/
instance gradeBy.gradedMonoid [AddMonoid H] {N : H →+ ℝ} [AddMonoid ι] (f : H →+ ι) :
    SetLike.GradedMonoid (gradeBy R N f) where
  one_mem h hh := by
    rw [← single_zero_one] at hh
    rw [mem_preimage, mem_singleton_iff, mem_singleton_iff.1 (support_single_subset 0 1 hh),
      map_zero]
  mul_mem i j a b ha hb h hh := by
    obtain ⟨u, hu, v, hv, rfl⟩ := support_mul_subset a b hh
    rw [mem_preimage, mem_singleton_iff, map_add, (ha hu : f u = i), (hb hv : f v = j)]

end Semiring

/-- The inclusion of the group ring into the Novikov series preserves and reflects the degree. -/
theorem ofAddMonoidAlgebra_mem_gradeBy_iff [CommSemiring R] [AddMonoid H] {N : H →+ ℝ}
    {f : H → ι} {i : ι} {x : AddMonoidAlgebra R H} :
    (ofAddMonoidAlgebra x : NovikovSeries R H N) ∈ gradeBy R N f i ↔
      x ∈ AddMonoidAlgebra.gradeBy R f i := by
  simp only [mem_gradeBy_iff, AddMonoidAlgebra.mem_gradeBy_iff, subset_def, mem_support,
    coeff_ofAddMonoidAlgebra, Finset.mem_coe, Finsupp.mem_support_iff]

section Topology

variable [AddZeroClass H] {N : H →+ ℝ} [Ring R]

/-- The Novikov series supported in a given set of exponents form a closed subset for the period
topology. -/
theorem isClosed_supported (s : Set H) :
    IsClosed (supported R N s : Set (NovikovSeries R H N)) := by
  have hset : (supported R N s : Set (NovikovSeries R H N)) =
      ⋂ h ∈ sᶜ, {a | a.coeff h = 0} := by
    ext a
    simp [mem_supported, subset_def, mem_support, not_imp_comm]
  rw [hset]
  exact isClosed_biInter fun h _ => (isLocallyConstant_coeff h).isClosed_fiber 0

/-- Every homogeneous piece of `NovikovSeries` is closed in the period topology. -/
theorem isClosed_gradeBy (f : H → ι) (i : ι) :
    IsClosed (gradeBy R N f i : Set (NovikovSeries R H N)) :=
  isClosed_supported (f ⁻¹' {i})

/-- The algebraic sum of the homogeneous pieces is dense in `NovikovSeries`. -/
theorem dense_iSup_gradeBy (f : H → ι) :
    Dense ((⨆ i, gradeBy R N f i : Submodule R (NovikovSeries R H N)) :
      Set (NovikovSeries R H N)) :=
  denseRange_ofFinsupp.mono (range_subset_iff.2 (ofFinsupp_mem_iSup_gradeBy f))

end Topology

section NonnegSubring

variable [CommSemiring S] [Ring R] [Algebra S R] [AddMonoid H] {N : H →+ ℝ}

variable (S R N) in
/-- The `S`-submodule of the nonnegative Novikov subring consisting of series supported in `s`. -/
def nonnegSupported (s : Set H) : Submodule S (nonnegSubring R N) where
  carrier := {a | (a : NovikovSeries R H N).support ⊆ s}
  zero_mem' := by simp
  add_mem' ha hb := (support_add_subset _ _).trans (union_subset ha hb)
  smul_mem' c a ha := (support_smul_subset c (a : NovikovSeries R H N)).trans ha

@[simp]
theorem mem_nonnegSupported {s : Set H} {a : nonnegSubring R N} :
    a ∈ nonnegSupported S R N s ↔ (a : NovikovSeries R H N).support ⊆ s :=
  Iff.rfl

theorem coe_mem_supported_iff {s : Set H} {a : nonnegSubring R N} :
    (a : NovikovSeries R H N) ∈ supported R N s ↔ a ∈ nonnegSupported S R N s :=
  Iff.rfl

/-- The series of the nonnegative subring supported in `s` form a closed subset. -/
theorem isClosed_nonnegSupported (s : Set H) :
    IsClosed (nonnegSupported S R N s : Set (nonnegSubring R N)) :=
  (isClosed_supported (R := R) (N := N) s).preimage continuous_subtype_val

variable (S R N) in
/-- The `S`-submodule of homogeneous series of degree `i` in the nonnegative Novikov subring. -/
def nonnegGradeBy (f : H → ι) (i : ι) : Submodule S (nonnegSubring R N) :=
  nonnegSupported S R N (f ⁻¹' {i})

@[simp]
theorem mem_nonnegGradeBy_iff {f : H → ι} {i : ι} {a : nonnegSubring R N} :
    a ∈ nonnegGradeBy S R N f i ↔ (a : NovikovSeries R H N).support ⊆ f ⁻¹' {i} :=
  Iff.rfl

theorem coe_mem_gradeBy_iff {f : H → ι} {i : ι} {a : nonnegSubring R N} :
    (a : NovikovSeries R H N) ∈ gradeBy R N f i ↔ a ∈ nonnegGradeBy S R N f i :=
  Iff.rfl

/-- A nonnegative-period monomial `r e^h` lies in the homogeneous piece of degree `f h` of the
nonnegative subring. -/
theorem single_mem_nonnegGradeBy (f : H → ι) {h : H} (hh : 0 ≤ N h) (r : R) :
    ⟨single h r, single_mem_nonnegSubring hh r⟩ ∈ nonnegGradeBy S R N f (f h) :=
  single_mem_gradeBy f h r

/-- A degree outside the range of `f` has trivial nonnegative homogeneous piece. -/
theorem nonnegGradeBy_eq_bot {f : H → ι} {i : ι} (hi : i ∉ range f) :
    nonnegGradeBy S R N f i = ⊥ := by
  refine (Submodule.eq_bot_iff _).2 fun a ha => Subtype.ext ?_
  exact (Submodule.eq_bot_iff _).1 (gradeBy_eq_bot hi) a.1 ha

/-- Every nonnegative homogeneous piece is closed in the subspace topology on
`nonnegSubring R N`. -/
theorem isClosed_nonnegGradeBy (f : H → ι) (i : ι) :
    IsClosed (nonnegGradeBy S R N f i : Set (nonnegSubring R N)) :=
  isClosed_nonnegSupported (f ⁻¹' {i})

/-- Homogeneous pieces of the nonnegative subring of distinct degrees are independent. -/
theorem iSupIndep_nonnegGradeBy (f : H → ι) : iSupIndep (nonnegGradeBy S R N f) := by
  intro i
  have hle : ⨆ (j) (_ : j ≠ i), nonnegGradeBy S R N f j ≤ nonnegSupported S R N (f ⁻¹' {i})ᶜ :=
    iSup₂_le fun j hj a ha h hh => by
      rw [mem_compl_iff, mem_preimage, mem_singleton_iff, (ha hh : f h = j)]
      exact hj
  refine (Submodule.disjoint_def.2 fun a ha ha' => Subtype.ext <| support_eq_empty.1 ?_).mono_right
    hle
  exact eq_empty_of_forall_notMem fun h hh => ha' hh (ha hh)

/-- Every finite sum of homogeneous series in `nonnegSubring R N` meets only finitely many
degrees. -/
theorem finite_image_support_of_mem_iSup_nonnegGradeBy {f : H → ι} {a : nonnegSubring R N}
    (ha : a ∈ ⨆ i, nonnegGradeBy S R N f i) :
    (f '' (a : NovikovSeries R H N).support).Finite :=
  Submodule.iSup_induction (motive := fun b => (f '' (b : NovikovSeries R H N).support).Finite)
    (nonnegGradeBy S R N f) ha
    (fun i _ hb => (finite_singleton i).subset
      ((image_mono (mem_nonnegGradeBy_iff.1 hb)).trans (image_preimage_subset f {i})))
    (by simp)
    fun b c hb hc => (hb.union hc).subset
      ((image_mono (support_add_subset (b : NovikovSeries R H N) (c : NovikovSeries R H N))).trans
        (image_union f _ _).le)

/-- For an additive degree homomorphism, the homogeneous pieces of the nonnegative subring form a
graded monoid, equipping `⨁ i, nonnegGradeBy S R N f i` with a `DirectSum.GAlgebra S` structure. -/
instance nonnegGradeBy.gradedMonoid [AddMonoid ι] (f : H →+ ι) :
    SetLike.GradedMonoid (nonnegGradeBy S R N f) where
  one_mem := SetLike.GradedOne.one_mem (A := gradeBy R N f)
  mul_mem i j _ _ ha hb := SetLike.GradedMul.mul_mem (A := gradeBy R N f) (i := i) (j := j) ha hb

/-- A finitely supported series supported in nonnegative periods lies in the nonnegative subring
and is a finite sum of nonnegative homogeneous series. -/
theorem ofFinsupp_mem_iSup_nonnegGradeBy (f : H → ι) {x : H →₀ R}
    (hx : ∀ h ∈ x.support, 0 ≤ N h) (hx0 : ofFinsupp x ∈ nonnegSubring R N) :
    (⟨ofFinsupp x, hx0⟩ : nonnegSubring R N) ∈ ⨆ i, nonnegGradeBy S R N f i := by
  classical
  induction x using Finsupp.induction with
  | zero =>
    convert zero_mem (⨆ i, nonnegGradeBy S R N f i)
    ext1
    simp
  | single_add h r y hhy hr ih =>
    have hh0 : 0 ≤ N h := hx h (Finsupp.mem_support_iff.2 <| by
      rw [Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.notMem_support_iff.1 hhy, add_zero]
      exact hr)
    have hy_supp : ∀ g ∈ y.support, 0 ≤ N g := fun g hg =>
      hx g (by
        have hgh : g ≠ h := fun e => hhy (e ▸ hg)
        rw [Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.single_eq_of_ne hgh, zero_add]
        exact Finsupp.mem_support_iff.1 hg)
    have hy0 : ofFinsupp (N := N) y ∈ nonnegSubring R N :=
      mem_nonnegSubring.2 fun g hg => by
        rw [coeff_ofFinsupp]
        by_contra hne
        exact not_lt_of_ge (hy_supp g (Finsupp.mem_support_iff.2 hne)) hg
    have heq : (⟨ofFinsupp (Finsupp.single h r + y), hx0⟩ : nonnegSubring R N) =
        ⟨single h r, single_mem_nonnegSubring hh0 r⟩ + ⟨ofFinsupp y, hy0⟩ := by
      ext1
      simp
    rw [heq]
    exact add_mem (Submodule.mem_iSup_of_mem (f h) (single_mem_nonnegGradeBy f hh0 r))
      (ih hy_supp hy0)

/-- Every truncation of a series in the nonnegative subring lies in the nonnegative subring. -/
theorem ofFinsupp_trunc_mem_nonnegSubring (C : ℝ) (a : nonnegSubring R N) :
    ofFinsupp (trunc C (a : NovikovSeries R H N)) ∈ nonnegSubring R N :=
  mem_nonnegSubring.2 <| mem_periodFiltration.1 <|
    ofFinsupp_trunc_mem_periodFiltration C (mem_periodFiltration.2 (mem_nonnegSubring.1 a.2))

/-- Every truncation of a series in the nonnegative subring is a finite sum of nonnegative
homogeneous series. -/
theorem ofFinsupp_trunc_mem_iSup_nonnegGradeBy (f : H → ι) (C : ℝ) (a : nonnegSubring R N) :
    (⟨ofFinsupp (trunc C (a : NovikovSeries R H N)),
      ofFinsupp_trunc_mem_nonnegSubring C a⟩ : nonnegSubring R N) ∈
      ⨆ i, nonnegGradeBy S R N f i := by
  refine ofFinsupp_mem_iSup_nonnegGradeBy f (fun h hh => ?_) _
  have hne : (a : NovikovSeries R H N).coeff h ≠ 0 := by
    intro hz
    exact Finsupp.mem_support_iff.1 hh (by simp [hz])
  exact not_lt.1 fun hlt => hne (mem_nonnegSubring.1 a.2 h hlt)

/-- The algebraic sum of the nonnegative homogeneous pieces is dense in `nonnegSubring R N`. -/
theorem dense_iSup_nonnegGradeBy (f : H → ι) :
    Dense ((⨆ i, nonnegGradeBy S R N f i : Submodule S (nonnegSubring R N)) :
      Set (nonnegSubring R N)) := by
  intro a
  refine mem_closure_of_tendsto (f := fun C : ℝ =>
    (⟨ofFinsupp (trunc C (a : NovikovSeries R H N)),
      ofFinsupp_trunc_mem_nonnegSubring C a⟩ : nonnegSubring R N)) (b := Filter.atTop) ?_
    (Filter.Eventually.of_forall fun C =>
      ofFinsupp_trunc_mem_iSup_nonnegGradeBy (S := S) f C a)
  rw [Topology.IsInducing.subtypeVal.tendsto_nhds_iff]
  exact tendsto_ofFinsupp_trunc (a : NovikovSeries R H N)

/-- The canonical graded algebra homomorphism
`⨁ i, nonnegGradeBy S R N f i →ₐ[S] nonnegSubring R N` is injective. -/
theorem coeAlgHom_nonnegGradeBy_injective [DecidableEq ι] [AddMonoid ι] (f : H →+ ι) :
    Injective (DirectSum.coeAlgHom (nonnegGradeBy S R N f)) := by
  intro x y hxy
  let e : (DirectSum ι fun i => nonnegGradeBy S R N f i) →+
      DirectSum ι fun i => nonnegGradeBy ℤ R N f i :=
    DirectSum.toAddMonoid fun i =>
      (DirectSum.of (fun j => nonnegGradeBy ℤ R N f j) i).comp
        { toFun := fun a => ⟨a.1, a.2⟩
          map_zero' := rfl
          map_add' := fun _ _ => rfl }
  have he_coe : ∀ z,
      DirectSum.coeLinearMap (nonnegGradeBy ℤ R N f) (e z) =
        DirectSum.coeAlgHom (nonnegGradeBy S R N f) z := fun z =>
    DirectSum.induction_on z (by simp)
      (fun i a => by simp [e])
      (fun u v hu hv => by simp [map_add, hu, hv])
  have he_inj : Injective e := by
    intro u v huv
    ext i : 1
    apply Subtype.ext
    have hi := congr_arg
      (fun z : DirectSum ι fun j => nonnegGradeBy ℤ R N f j => (z i : nonnegSubring R N)) huv
    have hval : ∀ z : DirectSum ι fun j => nonnegGradeBy S R N f j,
        ((e z i : nonnegGradeBy ℤ R N f i) : nonnegSubring R N) = z i := fun z =>
      DirectSum.induction_on z (by simp)
        (fun j a => by
          simp only [e, DirectSum.toAddMonoid_of, AddMonoidHom.comp_apply, AddMonoidHom.coe_mk,
            ZeroHom.coe_mk]
          by_cases hij : j = i
          · subst hij; simp
          · simp [DirectSum.of_eq_of_ne j i _ (Ne.symm hij)])
        (fun p q hp hq => by simp [map_add, hp, hq])
    simpa [hval] using hi
  have hcoe_inj : Injective (DirectSum.coeLinearMap (nonnegGradeBy ℤ R N f)) :=
    (iSupIndep_nonnegGradeBy (S := ℤ) (R := R) (N := N) f).dfinsupp_lsum_injective
  exact he_inj <| hcoe_inj <| by rw [he_coe, he_coe, hxy]

/-- The canonical graded algebra homomorphism from the direct sum of the nonnegative homogeneous
pieces into `nonnegSubring R N` has dense range. -/
theorem denseRange_coeAlgHom_nonnegGradeBy [DecidableEq ι] [AddMonoid ι] (f : H →+ ι) :
    DenseRange (DirectSum.coeAlgHom (nonnegGradeBy S R N f)) := by
  simp only [DenseRange, ← AlgHom.coe_range, ← Subalgebra.coe_toSubmodule,
    ← Submodule.iSup_eq_toSubmodule_range]
  exact dense_iSup_nonnegGradeBy (S := S) f

/-- The topological closure in `nonnegSubring R N` of the graded subalgebra spanned by the
homogeneous pieces is the whole nonnegative subring. -/
@[simp]
theorem topologicalClosure_range_coeAlgHom_nonnegGradeBy [DecidableEq ι] [AddMonoid ι]
    (f : H →+ ι) :
    (DirectSum.coeAlgHom (nonnegGradeBy S R N f)).range.topologicalClosure = ⊤ :=
  SetLike.ext' <| by
    simpa [Subalgebra.topologicalClosure_coe] using
      (denseRange_coeAlgHom_nonnegGradeBy (S := S) (R := R) (N := N) f).closure_eq

end NonnegSubring

end NovikovSeries

end TauCeti

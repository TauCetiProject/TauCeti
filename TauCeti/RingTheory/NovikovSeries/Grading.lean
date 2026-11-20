/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.NovikovSeries.Multiplication
public import Mathlib.Algebra.MonoidAlgebra.Grading

/-!
# Homogeneous Novikov series

Let `f : H → ι` be a degree function on the exponents of Novikov series. A Novikov series is
*homogeneous of degree `i`* when its support lies in the fibre `f ⁻¹' {i}`. These series form the
submodule `TauCeti.NovikovSeries.gradeBy R N f i`, the Novikov analogue of Mathlib's
`AddMonoidAlgebra.gradeBy`. For an additive degree function the pieces multiply as a graded
monoid, and they are independent.

Unlike the group ring, the Novikov ring is in general *not* the direct sum of its homogeneous
pieces: a series whose support meets infinitely many fibres is not a finite sum of homogeneous
series. The homogeneous pieces span exactly the series whose support meets finitely many fibres,
so the Novikov series are their internal direct sum exactly when every support does. Over a
nontrivial ring and for an additive degree `δ`, this happens exactly when the period vanishes or
`δ` takes finitely many values. For a degree with values in a torsion-free group, such as twice the
first Chern class on the second homology of a symplectic manifold with its area period, it happens
exactly when the period or the degree vanishes. The homogeneous pieces span exactly the finitely
supported series as soon as the period `N` is bounded above on every fibre of `f`, for instance
when `f` is injective. In that case the
graded ring spanned by homogeneous series is the group ring `R[H]`, and the Novikov ring is its
period completion. This is the situation of the coefficient ring of capped Hamiltonian Floer
theory on a spherically monotone symplectic manifold, graded by twice the first Chern number.

## Main definitions

* `TauCeti.NovikovSeries.supported R N s`: the Novikov series supported in the set `s`.
* `TauCeti.NovikovSeries.supportedSubalgebra S R N s`: the subalgebra of series supported in an
  additive submonoid or subgroup `s`.
* `TauCeti.NovikovSeries.gradeBy R N f i`: the Novikov series of degree `i` for the degree
  function `f`.
* `TauCeti.NovikovSeries.homogeneousComponent R N f i`: the homogeneous component of degree `i`,
  the restriction of the coefficients to the fibre over `i`.

## Main results

* `TauCeti.NovikovSeries.gradeBy.gradedMonoid`: for an additive degree function, the homogeneous
  pieces form a graded monoid.
* `TauCeti.NovikovSeries.iSupIndep_gradeBy`: the homogeneous pieces are independent.
* `TauCeti.NovikovSeries.ofAddMonoidAlgebra_mem_gradeBy_iff`: the inclusion of the group ring
  preserves and reflects the degree.
* `TauCeti.NovikovSeries.finite_support_of_mem_gradeBy`: a homogeneous series is finitely
  supported when the period is bounded above on its fibre.
* `TauCeti.NovikovSeries.mem_iSup_gradeBy_iff`: if the period is bounded above on every fibre,
  the homogeneous pieces span exactly the finitely supported series.
* `TauCeti.NovikovSeries.eq_single_of_mem_gradeBy`: for an injective degree function, every
  homogeneous series is a monomial.
* `TauCeti.NovikovSeries.mem_iSup_gradeBy_iff_finite_image`: the homogeneous pieces span exactly
  the series whose support meets finitely many degrees.
* `TauCeti.NovikovSeries.isInternal_gradeBy_iff`: the Novikov series are the internal direct sum
  of their homogeneous pieces exactly when every support meets finitely many degrees.
* `TauCeti.NovikovSeries.isInternal_gradeBy_iff_eq_zero_or_finite_range`: for an additive degree
  `δ` over a nontrivial ring, this holds exactly when the period vanishes or `δ` has finite range.
* `TauCeti.NovikovSeries.isInternal_gradeBy_iff_eq_zero_or_eq_zero`: for an additive degree with
  values in a torsion-free cancellative monoid, this holds exactly when the period or the degree
  vanishes.

## References

* H. Hofer and D. A. Salamon, *Floer homology and Novikov rings*, in *The Floer memorial
  volume*, Progr. Math. 133 (1995), 483–524.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, the construction of
  the Novikov ring in the chapter on quantum cohomology.
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

end AddZeroClass

section AddMonoid

variable [CommSemiring S] [Algebra S R] [AddMonoid H] {N : H →+ ℝ}
    {M : Type*} [SetLike M H] [AddSubmonoidClass M H]

variable (S R N) in
/-- The subalgebra of Novikov series supported in the additive submonoid or subgroup `s`. -/
def supportedSubalgebra (s : M) : Subalgebra S (NovikovSeries R H N) where
  carrier := {a | a.support ⊆ s}
  add_mem' ha hb := (support_add_subset _ _).trans (Set.union_subset ha hb)
  mul_mem' ha hb h hh := by
    obtain ⟨a, ha', b, hb', rfl⟩ := support_mul_subset _ _ hh
    exact add_mem (ha ha') (hb hb')
  algebraMap_mem' r h hh := by
    rw [algebraMap_apply] at hh
    exact (Set.mem_singleton_iff.1 (support_single_subset 0 (algebraMap S R r) hh)) ▸
      zero_mem s

variable (S R N) in
/-- The carrier of `supportedSubalgebra S R N s` consists of series supported in `s`. -/
@[simp]
theorem coe_supportedSubalgebra (s : M) :
    (supportedSubalgebra S R N s : Set (NovikovSeries R H N)) = {a | a.support ⊆ (s : Set H)} := by
  rfl

variable (S R N) in
/-- A series lies in `supportedSubalgebra S R N s` exactly when its support lies in `s`. -/
@[simp]
theorem mem_supportedSubalgebra {s : M} {a : NovikovSeries R H N} :
    a ∈ supportedSubalgebra S R N s ↔ a.support ⊆ s :=
  Iff.rfl

end AddMonoid

section AddZeroClass

variable [AddZeroClass H] {N : H →+ ℝ}

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

section Component

variable (R N) in
/-- The homogeneous component of degree `i` of a Novikov series for the degree function `f`: the
series with the coefficients of `a` on the fibre `f ⁻¹' {i}` and zero elsewhere. -/
def homogeneousComponent (f : H → ι) (i : ι) :
    NovikovSeries R H N →ₗ[R] NovikovSeries R H N where
  toFun a :=
    { coeff := (f ⁻¹' {i}).indicator a.coeff
      finite_lt C :=
        (a.finite_lt C).subset fun _ hh => ⟨(indicator_apply_ne_zero.1 hh.1).2, hh.2⟩ }
  map_add' a b := ext fun h => by
    by_cases hh : f h = i <;> simp [coeff_add, hh]
  map_smul' r a := ext fun h => by
    by_cases hh : f h = i <;> simp [coeff_smul, hh]

/-- The coefficient of the homogeneous component of degree `i` at `h` is that of the series when
`h` has degree `i`, and zero otherwise. -/
@[simp]
theorem coeff_homogeneousComponent [DecidableEq ι] (f : H → ι) (i : ι)
    (a : NovikovSeries R H N) (h : H) :
    (homogeneousComponent R N f i a).coeff h = if f h = i then a.coeff h else 0 := by
  by_cases hh : f h = i
  · simp only [hh, ↓reduceIte]
    exact indicator_of_mem (s := f ⁻¹' {i}) hh a.coeff
  · simp only [hh, ↓reduceIte]
    exact indicator_of_notMem (s := f ⁻¹' {i}) hh a.coeff

/-- The support of a homogeneous component is the part of the support in the fibre. -/
theorem support_homogeneousComponent (f : H → ι) (i : ι) (a : NovikovSeries R H N) :
    (homogeneousComponent R N f i a).support = a.support ∩ f ⁻¹' {i} := by
  classical
  ext h
  simp [mem_support, and_comm]

/-- The homogeneous component of degree `i` is homogeneous of degree `i`. -/
theorem homogeneousComponent_mem_gradeBy (f : H → ι) (i : ι) (a : NovikovSeries R H N) :
    homogeneousComponent R N f i a ∈ gradeBy R N f i := by
  rw [mem_gradeBy_iff, support_homogeneousComponent]
  exact inter_subset_right

/-- A homogeneous series of degree `i` is its own component of degree `i`, and its other
components vanish. -/
theorem homogeneousComponent_of_mem_gradeBy [DecidableEq ι] {f : H → ι} {i : ι}
    {a : NovikovSeries R H N} (ha : a ∈ gradeBy R N f i) (j : ι) :
    homogeneousComponent R N f j a = if i = j then a else 0 := by
  ext h
  by_cases hh : a.coeff h = 0
  · split_ifs <;> simp [hh]
  · have hfh : f h = i := ha (mem_support.2 hh)
    split_ifs with hij <;> simp [hfh, hij]

/-- The homogeneous component of degree `i` of a monomial is the monomial when its exponent has
degree `i`, and zero otherwise. -/
@[simp]
theorem homogeneousComponent_single [DecidableEq ι] (f : H → ι) (i : ι) (h : H) (r : R) :
    homogeneousComponent R N f i (single h r) = if f h = i then single h r else 0 :=
  homogeneousComponent_of_mem_gradeBy (single_mem_gradeBy f h r) i

/-- A series is the sum of its homogeneous components over any finite set of degrees containing
every degree of its support. -/
theorem sum_homogeneousComponent {f : H → ι} {a : NovikovSeries R H N} (T : Finset ι)
    (hT : f '' a.support ⊆ T) : ∑ i ∈ T, homogeneousComponent R N f i a = a := by
  classical
  ext h
  rw [coeff_sum]
  simp only [coeff_homogeneousComponent]
  rw [Finset.sum_ite_eq]
  by_cases hh : a.coeff h = 0
  · simp [hh]
  · simp [Finset.mem_coe.1 (hT (mem_image_of_mem f (mem_support.2 hh)))]

/-- The homogeneous component of degree `i` of a sum of homogeneous series, one of each degree, is
the summand of degree `i`. -/
@[simp]
theorem homogeneousComponent_coeAddMonoidHom [DecidableEq ι] {f : H → ι}
    (x : DirectSum ι fun i => gradeBy R N f i) (i : ι) :
    homogeneousComponent R N f i (DirectSum.coeAddMonoidHom (gradeBy R N f) x) = x i := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of j y =>
    rw [DirectSum.coeAddMonoidHom_of, homogeneousComponent_of_mem_gradeBy y.2,
      DirectSum.of_apply]
    split_ifs with hji
    · subst hji
      rfl
    · rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy, DirectSum.add_apply, Submodule.coe_add]

/-- The homogeneous series span exactly the series whose support meets only finitely many
degrees. -/
theorem mem_iSup_gradeBy_iff_finite_image {f : H → ι} {a : NovikovSeries R H N} :
    a ∈ ⨆ i, gradeBy R N f i ↔ (f '' a.support).Finite := by
  refine ⟨fun ha => ?_, fun ha => ?_⟩
  · refine Submodule.iSup_induction (motive := fun b => (f '' b.support).Finite) _ ha
      (fun i b hb => (finite_singleton i).subset ?_) (by simp)
      fun b c hb hc => (hb.union hc).subset ?_
    · exact image_subset_iff.2 hb
    · rw [← image_union]
      exact image_mono (support_add_subset b c)
  · rw [← sum_homogeneousComponent (f := f) (a := a) ha.toFinset (by simp)]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.mem_iSup_of_mem i (homogeneousComponent_mem_gradeBy f i a)

/-- The Novikov series are the internal direct sum of their homogeneous pieces exactly when the
support of every series meets only finitely many degrees. -/
theorem isInternal_gradeBy_iff [DecidableEq ι] {f : H → ι} :
    DirectSum.IsInternal (gradeBy R N f) ↔
      ∀ a : NovikovSeries R H N, (f '' a.support).Finite := by
  refine ⟨fun h a => mem_iSup_gradeBy_iff_finite_image.1 ?_, fun h => ⟨fun x y hxy => ?_,
    fun a => ?_⟩⟩
  · rw [h.submodule_iSup_eq_top]
    exact Submodule.mem_top
  · refine DFinsupp.ext fun i => Subtype.ext ?_
    rw [← homogeneousComponent_coeAddMonoidHom x, hxy, homogeneousComponent_coeAddMonoidHom]
  · refine ⟨∑ i ∈ (h a).toFinset, DirectSum.of (fun i => gradeBy R N f i) i
      ⟨_, homogeneousComponent_mem_gradeBy f i a⟩, ?_⟩
    simp only [map_sum, DirectSum.coeAddMonoidHom_of]
    exact sum_homogeneousComponent _ (by simp)

end Component

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

section Internal

variable [AddGroup H] {N : H →+ ℝ}

/-- Over a nontrivial ring, if the period is nonzero and the additive degree `δ` takes infinitely
many values, some Novikov series has nonzero coefficients in infinitely many degrees. -/
theorem exists_infinite_image_support [Nontrivial R] [AddMonoid ι] (hN : N ≠ 0) {δ : H →+ ι}
    (hδ : (range δ).Infinite) : ∃ a : NovikovSeries R H N, (δ '' a.support).Infinite := by
  -- Choose exponents `u n` whose degrees are pairwise distinct and whose periods grow by at least
  -- one at each step.
  obtain ⟨u, hu⟩ := seq_of_forall_finite_exists
    (P := fun c t => δ c ∉ δ '' t ∧ ∀ x ∈ t, N x + 1 ≤ N c) fun t ht => by
      obtain ⟨K, hK⟩ := (ht.image fun x => N x + 1).bddAbove
      obtain ⟨_, ⟨c, hc, rfl⟩, hct⟩ :=
        ((AddMonoidHom.infinite_image_setOf_le hN hδ K).sdiff (ht.image δ)).nonempty
      exact ⟨c, hct, fun x hx => (hK (mem_image_of_mem _ hx)).trans hc⟩
  have hinj : Injective (δ ∘ u) := by
    intro m n hmn
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · exact (hu n).1 ⟨u m, mem_image_of_mem u hlt, hmn⟩
    · exact (hu m).1 ⟨u n, mem_image_of_mem u hlt, hmn.symm⟩
  have hgrow : ∀ n : ℕ, N (u 0) + n ≤ N (u n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have := (hu (n + 1)).2 (u n) (mem_image_of_mem u (Nat.lt_succ_self n))
      push_cast
      linarith
  -- The series with coefficient `1` at every `u n` meets every degree `δ (u n)`.
  let a : NovikovSeries R H N :=
    { coeff := (range u).indicator 1
      finite_lt C := by
        refine ((Finset.range ⌈C - N (u 0)⌉₊).finite_toSet.image u).subset ?_
        rintro h ⟨hh, hhC⟩
        obtain ⟨n, rfl⟩ := mem_of_indicator_ne_zero hh
        refine ⟨n, Finset.mem_coe.2 (Finset.mem_range.2 (Nat.lt_ceil.2 ?_)), rfl⟩
        linarith [hgrow n] }
  refine ⟨a, ?_⟩
  have hsupp : a.support = range u := by
    ext h
    simp [a, mem_support]
  rw [hsupp, ← range_comp]
  exact infinite_range_of_injective hinj

/-- Over a nontrivial ring, the Novikov series are the internal direct sum of their homogeneous
pieces for an additive degree `δ` exactly when the period vanishes, so that every series is
finitely supported, or `δ` takes only finitely many values. -/
theorem isInternal_gradeBy_iff_eq_zero_or_finite_range [Nontrivial R] [AddMonoid ι]
    [DecidableEq ι] (δ : H →+ ι) :
    DirectSum.IsInternal (gradeBy R N δ) ↔ N = 0 ∨ (range δ).Finite := by
  rw [isInternal_gradeBy_iff]
  refine ⟨fun h => ?_, fun h a => ?_⟩
  · by_contra! hc
    obtain ⟨a, ha⟩ := exists_infinite_image_support (R := R) hc.1 hc.2
    exact ha (h a)
  · rcases h with hN | hδ
    · obtain ⟨x, rfl⟩ := (ofFinsupp_surjective_iff (R := R)).2 hN a
      rw [support_ofFinsupp]
      exact x.support.finite_toSet.image _
    · exact hδ.subset (image_subset_range _ _)

/-- Over a nontrivial ring, for an additive degree `δ` with values in a torsion-free cancellative
monoid, such as twice the first Chern class on the second homology, the Novikov series are the
internal direct sum of their homogeneous pieces exactly when the period or the degree vanishes. -/
theorem isInternal_gradeBy_iff_eq_zero_or_eq_zero [Nontrivial R] [AddCancelMonoid ι]
    [IsAddTorsionFree ι] [DecidableEq ι] (δ : H →+ ι) :
    DirectSum.IsInternal (gradeBy R N δ) ↔ N = 0 ∨ δ = 0 := by
  rw [isInternal_gradeBy_iff_eq_zero_or_finite_range]
  refine or_congr_right ⟨fun hδ => ?_, fun hδ => ?_⟩
  · ext h
    by_contra hh
    refine infinite_range_of_injective (IsAddTorsionFree.nsmul_left_injective hh)
      (hδ.subset ?_)
    rintro _ ⟨n, rfl⟩
    exact ⟨n • h, map_nsmul δ n h⟩
  · subst hδ
    exact (finite_singleton 0).subset (range_subset_singleton.2 rfl)

end Internal

end Semiring

/-- The inclusion of the group ring into the Novikov series preserves and reflects the degree. -/
theorem ofAddMonoidAlgebra_mem_gradeBy_iff [CommSemiring R] [AddMonoid H] {N : H →+ ℝ}
    {f : H → ι} {i : ι} {x : AddMonoidAlgebra R H} :
    (ofAddMonoidAlgebra x : NovikovSeries R H N) ∈ gradeBy R N f i ↔
      x ∈ AddMonoidAlgebra.gradeBy R f i := by
  simp only [mem_gradeBy_iff, AddMonoidAlgebra.mem_gradeBy_iff, subset_def, mem_support,
    coeff_ofAddMonoidAlgebra, Finset.mem_coe, Finsupp.mem_support_iff]

end NovikovSeries

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.NovikovSeries.Multiplication
public import Mathlib.Algebra.MonoidAlgebra.Grading
public import Mathlib.Algebra.Group.Torsion

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
`δ` takes finitely many values. For a degree with values in a torsion-free cancellative monoid,
such as twice the first Chern class on the second homology of a symplectic manifold with its area
period, it happens exactly when the period or the degree vanishes. The homogeneous pieces span
exactly the finitely supported series as soon as the period `N` is bounded above on every fibre of
`f`, for instance when `f` is injective. In that case the
graded ring spanned by homogeneous series is the group ring `R[H]`, and the Novikov ring is its
period completion. This is the situation of the coefficient ring of capped Hamiltonian Floer
theory on a spherically monotone symplectic manifold, graded by twice the first Chern number.

## Main definitions

* `TauCeti.NovikovSeries.supported R N s`: the Novikov series supported in the set `s`.
* `TauCeti.NovikovSeries.supportedSubalgebra S R N s`: the subalgebra of series supported in an
  additive submonoid or subgroup `s`.
* `TauCeti.NovikovSeries.gradeBy R N f i`: the Novikov series of degree `i` for the degree
  function `f`.
* `TauCeti.NovikovSeries.gradeProj R N f i`: the homogeneous component of degree `i` of a
  series.
* `TauCeti.NovikovSeries.gradeByCoeff N 𝒱 δ D`: for coefficients in a module `V` graded by `𝒱`
  and a degree `δ` on the exponents, the series of degree `D`, those whose coefficient at `A` has
  degree `D - δ A`. For `R` itself concentrated in degree `0` these are the pieces `gradeBy`
  (`TauCeti.NovikovSeries.gradeByCoeff_ite_eq_gradeBy`).

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
* `TauCeti.NovikovSeries.mem_iSup_gradeBy_iff_finite`: a series is a finite sum of homogeneous
  series exactly when its support meets finitely many degrees.
* `TauCeti.NovikovSeries.isInternal_gradeBy_iff`: the Novikov ring is the internal direct sum of
  its homogeneous pieces exactly when every series meets finitely many degrees.
* `TauCeti.NovikovSeries.isInternal_gradeBy_iff_eq_zero_or_finite_range`: for an additive degree
  `δ` over a nontrivial ring, this happens exactly when the period vanishes or `δ` has finite range.
* `TauCeti.NovikovSeries.isInternal_gradeBy_iff_eq_zero_or_eq_zero`: for an additive degree with
  values in a torsion-free cancellative monoid and nontrivial coefficients, this happens exactly
  when the period or the degree vanishes, since a nonzero degree `δ` takes the infinitely many
  values `n δ(C)` for a class `C` with `δ(C) ≠ 0`.

## References

* H. Hofer and D. A. Salamon, *Floer homology and Novikov rings*, in *The Floer memorial
  volume*, Progr. Math. 133 (1995), 483–524.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, the construction of
  the Novikov ring in the chapter on quantum cohomology.
-/

public section

noncomputable section

open Function Set
open scoped DirectSum

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

/-- The homogeneous component of degree `i` of a sum of homogeneous series, one of each degree, is
the summand of degree `i`. -/
theorem gradeProj_coeAddMonoidHom (f : H → ι) (x : ⨁ i, gradeBy R N f i) (i : ι) :
    gradeProj R N f i (DirectSum.coeAddMonoidHom (gradeBy R N f) x) = x i := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of j y =>
    rw [DirectSum.coeAddMonoidHom_of]
    by_cases hji : j = i
    · subst hji
      rw [DirectSum.of_eq_same, gradeProj_eq_self_of_mem_gradeBy y.property]
    · rw [DirectSum.of_eq_of_ne _ _ _ (Ne.symm hji),
        gradeProj_eq_zero_of_mem_gradeBy hji y.property, ZeroMemClass.coe_zero]
  | add x y hx hy => simp only [map_add, hx, hy, DirectSum.add_apply, AddMemClass.coe_add]

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

/-- The homogeneous series span all Novikov series exactly when every series meets only finitely
many degrees. -/
theorem iSup_gradeBy_eq_top_iff {f : H → ι} :
    ⨆ i, gradeBy R N f i = ⊤ ↔ ∀ a : NovikovSeries R H N, (f '' a.support).Finite := by
  simp only [Submodule.eq_top_iff', mem_iSup_gradeBy_iff_finite]

/-- The Novikov series form the internal direct sum of their homogeneous pieces exactly when
every series meets only finitely many degrees. -/
theorem isInternal_gradeBy_iff [DecidableEq ι] {f : H → ι} :
    DirectSum.IsInternal (gradeBy R N f) ↔ ∀ a : NovikovSeries R H N, (f '' a.support).Finite := by
  refine ⟨fun h => iSup_gradeBy_eq_top_iff.1 h.submodule_iSup_eq_top,
    fun h => ⟨fun x y hxy => DirectSum.ext fun i => Subtype.ext ?_, fun a => ?_⟩⟩
  · -- The summands are recovered as homogeneous components.
    rw [← gradeProj_coeAddMonoidHom, ← gradeProj_coeAddMonoidHom, hxy]
  · -- `a` is the sum of its finitely many homogeneous components.
    refine ⟨∑ i ∈ (h a).toFinset, DirectSum.of (fun i => gradeBy R N f i) i
      ⟨gradeProj R N f i a, gradeProj_mem_gradeBy f i a⟩, ?_⟩
    rw [map_sum]
    simp only [DirectSum.coeAddMonoidHom_of]
    exact sum_gradeProj_eq_self (by simp)

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

/-- Over a nontrivial ring, every Novikov series meets only finitely many degrees of an additive
degree `δ` exactly when the period vanishes, so that every series is finitely supported, or `δ`
takes only finitely many values. -/
theorem forall_finite_image_support_iff_eq_zero_or_finite_range [Nontrivial R] [AddMonoid ι]
    (δ : H →+ ι) :
    (∀ a : NovikovSeries R H N, (δ '' a.support).Finite) ↔ N = 0 ∨ (range δ).Finite := by
  refine ⟨fun h => ?_, fun h a => ?_⟩
  · by_contra! hc
    obtain ⟨a, ha⟩ := exists_infinite_image_support (R := R) hc.1 hc.2
    exact ha (h a)
  · rcases h with hN | hδ
    · obtain ⟨x, rfl⟩ := (ofFinsupp_surjective_iff (R := R)).2 hN a
      rw [support_ofFinsupp]
      exact x.support.finite_toSet.image _
    · exact hδ.subset (image_subset_range _ _)

/-- Over a nontrivial ring, the Novikov series are the internal direct sum of their homogeneous
pieces for an additive degree `δ` exactly when the period vanishes, so that every series is
finitely supported, or `δ` takes only finitely many values. -/
theorem isInternal_gradeBy_iff_eq_zero_or_finite_range [Nontrivial R] [AddMonoid ι]
    [DecidableEq ι] (δ : H →+ ι) :
    DirectSum.IsInternal (gradeBy R N δ) ↔ N = 0 ∨ (range δ).Finite := by
  rw [isInternal_gradeBy_iff, forall_finite_image_support_iff_eq_zero_or_finite_range]

end Internal

section Additive

variable [Nontrivial R] [AddGroup H] {N : H →+ ℝ} [AddCancelMonoid ι] (δ : H →+ ι)

/-- For an additive degree with values in a torsion-free cancellative monoid, every Novikov series
meets only finitely many degrees exactly when the period or the degree vanishes. -/
theorem forall_finite_image_support_iff [IsAddTorsionFree ι] :
    (∀ a : NovikovSeries R H N, (δ '' a.support).Finite) ↔ N = 0 ∨ δ = 0 := by
  rw [forall_finite_image_support_iff_eq_zero_or_finite_range]
  refine or_congr_right ⟨fun hδ => AddMonoidHom.ext fun C => ?_, fun hδ => ?_⟩
  · -- A class `C` of nonzero degree has the infinitely many distinct multiples `n δ(C)` as degrees.
    by_contra hC
    rw [AddMonoidHom.zero_apply] at hC
    refine (infinite_range_of_injective (IsAddTorsionFree.nsmul_left_injective hC)).mono ?_ hδ
    rintro _ ⟨n, rfl⟩
    exact ⟨n • C, map_nsmul δ n C⟩
  · subst hδ
    exact (finite_singleton 0).subset (by simp [subset_def])

/-- **Criterion for an internally graded Novikov ring.** For an additive degree with values in a
torsion-free cancellative monoid and nontrivial coefficients, the Novikov series form the internal
direct sum of their homogeneous pieces exactly when the period or the degree vanishes. -/
theorem isInternal_gradeBy_iff_eq_zero_or_eq_zero [IsAddTorsionFree ι] [DecidableEq ι] :
    DirectSum.IsInternal (gradeBy R N δ) ↔ N = 0 ∨ δ = 0 := by
  rw [isInternal_gradeBy_iff, forall_finite_image_support_iff]

end Additive

end Semiring

/-- The inclusion of the group ring into the Novikov series preserves and reflects the degree. -/
theorem ofAddMonoidAlgebra_mem_gradeBy_iff [CommSemiring R] [AddMonoid H] {N : H →+ ℝ}
    {f : H → ι} {i : ι} {x : AddMonoidAlgebra R H} :
    (ofAddMonoidAlgebra x : NovikovSeries R H N) ∈ gradeBy R N f i ↔
      x ∈ AddMonoidAlgebra.gradeBy R f i := by
  simp only [mem_gradeBy_iff, AddMonoidAlgebra.mem_gradeBy_iff, subset_def, mem_support,
    coeff_ofAddMonoidAlgebra, Finset.mem_coe, Finsupp.mem_support_iff]

section GradeByCoeff

variable {Γ : Type*} [AddGroup Γ] [AddZeroClass H] {N : H →+ ℝ} [Semiring R] {V : Type*}
  [AddCommMonoid V] [Module R V]

variable (N) in
/-- The Novikov series of degree `D` with coefficients in a graded module: for a grading `𝒱` of
`V` and a degree `δ A` of the exponents, those `v` with `v_A ∈ 𝒱 (D - δ A)` for every `A`. For
`V = R` concentrated in degree `0` these are the series supported on `δ⁻¹ {D}`
(`TauCeti.NovikovSeries.gradeByCoeff_ite_eq_gradeBy`). -/
def gradeByCoeff (𝒱 : Γ → Submodule R V) (δ : H → Γ) (D : Γ) :
    Submodule R (NovikovSeries V H N) where
  carrier := {v | ∀ A, v.coeff A ∈ 𝒱 (D - δ A)}
  zero_mem' A := by simp
  add_mem' hv hw A := by simpa using add_mem (hv A) (hw A)
  smul_mem' c v hv A := by simpa using Submodule.smul_mem _ c (hv A)

/-- A series has degree `D` exactly when each coefficient `v_A` has degree `D - δ A`. -/
@[simp]
theorem mem_gradeByCoeff {𝒱 : Γ → Submodule R V} {δ : H → Γ} {D : Γ}
    {v : NovikovSeries V H N} : v ∈ gradeByCoeff N 𝒱 δ D ↔ ∀ A, v.coeff A ∈ 𝒱 (D - δ A) :=
  Iff.rfl

/-- For `R` itself concentrated in degree `0`, the series of degree `D` are those supported on
the exponents of degree `D`, the pieces `TauCeti.NovikovSeries.gradeBy` of the Novikov ring. -/
theorem gradeByCoeff_ite_eq_gradeBy [DecidableEq Γ] (δ : H → Γ) (D : Γ) :
    gradeByCoeff N (fun k => if k = 0 then ⊤ else ⊥ : Γ → Submodule R R) δ D =
      gradeBy R N δ D := by
  ext v
  simp only [mem_gradeByCoeff, mem_gradeBy_iff, Set.subset_def, mem_support, Set.mem_preimage,
    Set.mem_singleton_iff, sub_eq_zero]
  refine forall_congr' fun A => ?_
  by_cases hA : D = δ A
  · simp [hA]
  · simp [hA, Ne.symm hA]

end GradeByCoeff

end NovikovSeries

end TauCeti

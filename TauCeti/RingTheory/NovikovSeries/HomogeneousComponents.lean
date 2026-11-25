/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.NovikovSeries.Grading
public import TauCeti.RingTheory.NovikovSeries.TopologicalRing
public import Mathlib.Topology.Algebra.Algebra

/-!
# Homogeneous components of Novikov series

Let `f : H → ι` be a degree function on the exponents of Novikov series. The homogeneous pieces
`TauCeti.NovikovSeries.gradeBy R N f i` are independent, but the Novikov ring is in general not
their direct sum: a series whose support meets infinitely many degrees is not a finite sum of
homogeneous series. This file shows that the completion is nevertheless recovered from the
homogeneous pieces through the period topology of `TauCeti.RingTheory.NovikovSeries.Topology`, both
on the full ring `NovikovSeries R H N` and on its nonnegative subring
`TauCeti.NovikovSeries.nonnegSubring R N`.

* Taking the **homogeneous component** of degree `i` (`TauCeti.NovikovSeries.gradeProj`, and
  `TauCeti.NovikovSeries.nonnegGradeProj` on `nonnegSubring`) is continuous
  (`TauCeti.NovikovSeries.continuous_gradeProj`,
  `TauCeti.NovikovSeries.continuous_nonnegGradeProj`), and every homogeneous piece is closed
  (`TauCeti.NovikovSeries.isClosed_gradeBy`, `TauCeti.NovikovSeries.isClosed_nonnegGradeBy`).
* Every series is the sum, convergent in the period topology, of its homogeneous components
  (`TauCeti.NovikovSeries.hasSum_gradeProj`, `TauCeti.NovikovSeries.hasSum_nonnegGradeProj`), and
  this is its only decomposition into a convergent sum of homogeneous series
  (`TauCeti.NovikovSeries.hasSum_iff_eq_gradeProj`). Hence the sum of the homogeneous pieces is
  dense (`TauCeti.NovikovSeries.dense_iSup_gradeBy`,
  `TauCeti.NovikovSeries.dense_iSup_nonnegGradeBy`).
* For an additive degree `f : H →+ ι`, the nonnegative homogeneous pieces
  `TauCeti.NovikovSeries.nonnegGradeBy S R N f i` form a graded monoid, and `DirectSum.coeAlgHom`
  embeds `⨁ i, nonnegGradeBy S R N f i` injectively and densely into `nonnegSubring R N`
  (`TauCeti.NovikovSeries.coeAlgHom_nonnegGradeBy_injective`,
  `TauCeti.NovikovSeries.denseRange_coeAlgHom_nonnegGradeBy`), with topological closure `⊤`
  (`TauCeti.NovikovSeries.topologicalClosure_range_coeAlgHom_nonnegGradeBy`).
* A series is a finite sum of homogeneous series exactly when its support meets finitely many
  degrees (`TauCeti.NovikovSeries.mem_iSup_gradeBy_iff_finite`,
  `TauCeti.NovikovSeries.mem_iSup_nonnegGradeBy_iff_finite`). So the sum of the homogeneous
  pieces is closed exactly when it is everything, that is, exactly when the Novikov ring is the
  internal direct sum of its homogeneous pieces
  (`TauCeti.NovikovSeries.isClosed_iSup_gradeBy_iff`,
  `TauCeti.NovikovSeries.isInternal_gradeBy_iff`). For an additive degree with values in a
  torsion-free group and nontrivial coefficients, this happens exactly when the period or the
  degree vanishes (`TauCeti.NovikovSeries.isInternal_gradeBy_iff_eq_zero_or_eq_zero`).

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
* K. Fukaya, Y.-G. Oh, H. Ohta and K. Ono, *Lagrangian intersection Floer theory: anomaly and
  obstruction, Part I*, AMS/IP Studies in Advanced Mathematics 46.1, 2009, Chapter 2.
-/

public section

noncomputable section

open Filter Function Set Topology

namespace TauCeti

namespace NovikovSeries

variable {S R H ι : Type*}

section AddZeroClass

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

/-- The sum of the homogeneous pieces is closed in the period topology exactly when it is
everything, that is, when every series meets only finitely many degrees. -/
theorem isClosed_iSup_gradeBy_iff {f : H → ι} :
    IsClosed ((⨆ i, gradeBy R N f i : Submodule R (NovikovSeries R H N)) :
      Set (NovikovSeries R H N)) ↔ ∀ a : NovikovSeries R H N, (f '' a.support).Finite := by
  rw [← iSup_gradeBy_eq_top_iff]
  refine ⟨fun h => ?_, fun h => by simp [h]⟩
  rw [← Submodule.coe_eq_univ, ← h.closure_eq, (dense_iSup_gradeBy f).closure_eq]

end AddZeroClass

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
  mem_supported.trans mem_nonnegSupported.symm

/-- The series of the nonnegative subring supported in `s` form a closed subset. -/
theorem isClosed_nonnegSupported (s : Set H) :
    IsClosed (nonnegSupported S R N s : Set (nonnegSubring R N)) :=
  (isClosed_setOf_support_subset s).preimage continuous_subtypeVal

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
  mem_gradeBy_iff.trans mem_nonnegGradeBy_iff.symm

/-- A nonnegative-period monomial `r e^h` lies in the homogeneous piece of degree `f h` of the
nonnegative subring. -/
theorem single_mem_nonnegGradeBy (f : H → ι) {h : H} (hh : 0 ≤ N h) (r : R) :
    ⟨single h r, single_mem_nonnegSubring hh r⟩ ∈ nonnegGradeBy S R N f (f h) :=
  (coe_mem_gradeBy_iff (S := S)).1 (single_mem_gradeBy f h r)

/-- A degree outside the range of `f` has trivial nonnegative homogeneous piece. -/
theorem nonnegGradeBy_eq_bot {f : H → ι} {i : ι} (hi : i ∉ range f) :
    nonnegGradeBy S R N f i = ⊥ :=
  (Submodule.eq_bot_iff _).2 fun a ha =>
    Subtype.ext <| (Submodule.eq_bot_iff _).1 (gradeBy_eq_bot hi) a.val (coe_mem_gradeBy_iff.2 ha)

/-- Every nonnegative homogeneous piece is closed in the subspace topology on
`nonnegSubring R N`. -/
theorem isClosed_nonnegGradeBy (f : H → ι) (i : ι) :
    IsClosed (nonnegGradeBy S R N f i : Set (nonnegSubring R N)) :=
  isClosed_nonnegSupported (f ⁻¹' {i})

/-- Homogeneous pieces of the nonnegative subring of distinct degrees are independent. -/
theorem iSupIndep_nonnegGradeBy (f : H → ι) : iSupIndep (nonnegGradeBy S R N f) := fun i => by
  have hle : ⨆ (j) (_ : j ≠ i), nonnegGradeBy S R N f j ≤ nonnegSupported S R N (f ⁻¹' {i})ᶜ :=
    iSup₂_le fun j hj _ ha _ hh hhi => hj ((mem_nonnegGradeBy_iff.1 ha hh).symm.trans hhi)
  exact Disjoint.mono_right hle <| Submodule.disjoint_def.2 fun _ ha ha' =>
    Subtype.ext <| support_eq_empty.1 <| eq_empty_of_forall_notMem fun _ hh =>
      mem_nonnegSupported.1 ha' hh (mem_nonnegGradeBy_iff.1 ha hh)

/-- For an additive degree homomorphism, the homogeneous pieces of the nonnegative subring form a
graded monoid, equipping `⨁ i, nonnegGradeBy S R N f i` with a `DirectSum.GAlgebra S` structure. -/
instance nonnegGradeBy.gradedMonoid [AddMonoid ι] (f : H →+ ι) :
    SetLike.GradedMonoid (nonnegGradeBy S R N f) where
  one_mem := (coe_mem_gradeBy_iff (S := S)).1 (SetLike.GradedOne.one_mem (A := gradeBy R N f))
  mul_mem _ _ _ _ ha hb := (coe_mem_gradeBy_iff (S := S)).1
    (SetLike.GradedMul.mul_mem (coe_mem_gradeBy_iff.2 ha) (coe_mem_gradeBy_iff.2 hb))

section NonnegProj

variable [DecidableEq ι]

variable (S R N) in
/-- The `S`-linear projection taking a series in `nonnegSubring R N` to its homogeneous component
of degree `i`. -/
def nonnegGradeProj (f : H → ι) (i : ι) : nonnegSubring R N →ₗ[S] nonnegSubring R N where
  toFun a := ⟨gradeProj R N f i a, mem_nonnegSubring.2 <| mem_periodFiltration.1 <|
    gradeProj_mem_periodFiltration f i (mem_periodFiltration.2 (mem_nonnegSubring.1 a.property))⟩
  map_add' a b := Subtype.ext (map_add (gradeProj R N f i) a.val b.val)
  map_smul' s a := Subtype.ext <| by
    ext h
    simp [coeff_gradeProj, coeff_smul, smul_ite]

@[simp]
theorem coe_nonnegGradeProj (f : H → ι) (i : ι) (a : nonnegSubring R N) :
    (nonnegGradeProj S R N f i a : NovikovSeries R H N) = gradeProj R N f i a :=
  (rfl)

theorem nonnegGradeProj_mem_nonnegGradeBy (f : H → ι) (i : ι) (a : nonnegSubring R N) :
    nonnegGradeProj S R N f i a ∈ nonnegGradeBy S R N f i := by
  rw [← coe_mem_gradeBy_iff (S := S), coe_nonnegGradeProj]
  exact gradeProj_mem_gradeBy f i (a : NovikovSeries R H N)

/-- A nonnegative series of degree `i` is its own homogeneous component of degree `i`. -/
@[simp]
theorem nonnegGradeProj_eq_self_of_mem_nonnegGradeBy {f : H → ι} {i : ι} {a : nonnegSubring R N}
    (ha : a ∈ nonnegGradeBy S R N f i) : nonnegGradeProj S R N f i a = a :=
  Subtype.ext <| gradeProj_eq_self_of_mem_gradeBy (coe_mem_gradeBy_iff.2 ha)

/-- A nonnegative series of degree `j` has zero homogeneous component in any distinct degree `i`. -/
theorem nonnegGradeProj_eq_zero_of_mem_nonnegGradeBy {f : H → ι} {i j : ι} (hij : j ≠ i)
    {a : nonnegSubring R N} (ha : a ∈ nonnegGradeBy S R N f j) :
    nonnegGradeProj S R N f i a = 0 :=
  Subtype.ext <| gradeProj_eq_zero_of_mem_gradeBy hij (coe_mem_gradeBy_iff.2 ha)

@[fun_prop]
theorem continuous_nonnegGradeProj (f : H → ι) (i : ι) :
    Continuous (nonnegGradeProj S R N f i) :=
  continuous_induced_rng.2 ((continuous_gradeProj (R := R) (N := N) f i).comp continuous_subtypeVal)

/-- **Every nonnegative Novikov series is the sum of its homogeneous components**, convergent in the
subspace period topology on `nonnegSubring R N`. -/
theorem hasSum_nonnegGradeProj (f : H → ι) (a : nonnegSubring R N) :
    HasSum (fun i => nonnegGradeProj S R N f i a) a := by
  have hind : IsInducing ((nonnegSubring R N).subtype : nonnegSubring R N →+ NovikovSeries R H N) :=
    IsInducing.subtypeVal
  exact (hind.hasSum_iff (f := fun i => nonnegGradeProj S R N f i a) (a := a)).1
    (by simpa [Function.comp_def] using hasSum_gradeProj f (a : NovikovSeries R H N))

/-- Applying `nonnegGradeProj` to `DirectSum.coeAlgHom` recovers the `i`-th graded summand. -/
@[simp]
theorem nonnegGradeProj_coeAlgHom [AddMonoid ι] (f : H →+ ι)
    (x : DirectSum ι fun i => nonnegGradeBy S R N f i) (i : ι) :
    nonnegGradeProj S R N f i (DirectSum.coeAlgHom (nonnegGradeBy S R N f) x) = x i := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of j y =>
    rw [DirectSum.coeAlgHom_of]
    by_cases hji : j = i
    · subst hji
      rw [DirectSum.of_eq_same, nonnegGradeProj_eq_self_of_mem_nonnegGradeBy y.property]
    · rw [DirectSum.of_eq_of_ne _ _ _ (Ne.symm hji),
        nonnegGradeProj_eq_zero_of_mem_nonnegGradeBy hji y.property, ZeroMemClass.coe_zero]
  | add x y hx hy => simp only [map_add, hx, hy, DirectSum.add_apply, AddMemClass.coe_add]

end NonnegProj

/-- A series in `nonnegSubring R N` is a finite sum of homogeneous series in `nonnegSubring R N`
if and only if its support meets only finitely many degrees. -/
theorem mem_iSup_nonnegGradeBy_iff_finite {f : H → ι} {a : nonnegSubring R N} :
    a ∈ ⨆ i, nonnegGradeBy S R N f i ↔ (f '' (a : NovikovSeries R H N).support).Finite := by
  classical
  refine ⟨fun ha => mem_iSup_gradeBy_iff_finite.1 <|
    Submodule.iSup_induction (motive := fun b => (b : NovikovSeries R H N) ∈ ⨆ i, gradeBy R N f i)
      (nonnegGradeBy S R N f) ha
      (fun i _ hb => Submodule.mem_iSup_of_mem i (coe_mem_gradeBy_iff.2 hb)) (by simp)
      fun _ _ hb hc => by simpa using add_mem hb hc, fun ha => ?_⟩
  have hsum : ∑ i ∈ ha.toFinset, nonnegGradeProj S R N f i a = a :=
    Subtype.ext <| by
      rw [← Subring.subtype_apply, map_sum]
      simpa only [Subring.subtype_apply, coe_nonnegGradeProj] using
        sum_gradeProj_eq_self (f := f) (s := ha.toFinset) (a := (a : NovikovSeries R H N)) (by simp)
  exact hsum ▸ Submodule.sum_mem _ fun i _ =>
    Submodule.mem_iSup_of_mem i (nonnegGradeProj_mem_nonnegGradeBy f i a)

/-- The algebraic sum of the nonnegative homogeneous pieces is dense in `nonnegSubring R N`. -/
theorem dense_iSup_nonnegGradeBy (f : H → ι) :
    Dense ((⨆ i, nonnegGradeBy S R N f i : Submodule S (nonnegSubring R N)) :
      Set (nonnegSubring R N)) := fun a => by
  classical
  have ha := hasSum_nonnegGradeProj (S := S) f a
  rw [HasSum, SummationFilter.unconditional_filter] at ha
  exact mem_closure_of_tendsto ha (Eventually.of_forall fun s =>
    Submodule.sum_mem _ fun i _ =>
      Submodule.mem_iSup_of_mem i (nonnegGradeProj_mem_nonnegGradeBy f i a))

/-- The canonical graded algebra homomorphism
`⨁ i, nonnegGradeBy S R N f i →ₐ[S] nonnegSubring R N` is injective. -/
theorem coeAlgHom_nonnegGradeBy_injective [DecidableEq ι] [AddMonoid ι] (f : H →+ ι) :
    Injective (DirectSum.coeAlgHom (nonnegGradeBy S R N f)) := fun x y hxy =>
  DirectSum.ext fun i => Subtype.ext <| by
    have h := congrArg (nonnegGradeProj S R N f i) hxy
    rwa [nonnegGradeProj_coeAlgHom, nonnegGradeProj_coeAlgHom] at h

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
    (f : H →+ ι) : (DirectSum.coeAlgHom (nonnegGradeBy S R N f)).range.topologicalClosure = ⊤ :=
  SetLike.ext' <| by
    simpa [Subalgebra.topologicalClosure_coe] using
      (denseRange_coeAlgHom_nonnegGradeBy (S := S) (R := R) (N := N) f).closure_eq

end NonnegSubring

end NovikovSeries

end TauCeti

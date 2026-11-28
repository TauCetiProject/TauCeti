/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Data.Set.Countable
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.RingTheory.Ideal.Defs
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Module.Torsion.Field
import Mathlib.Data.Fintype.BigOperators

/-!
# Finite spans and singleton spans

A generator with a unit coefficient in a linear combination can be replaced by that combination
without changing the span. Over a division semiring, a nonzero vector in a singleton span can be
used to recover the generator's membership in any submodule. A vector outside a line is not
cancelled by adding any multiple of the generator. Acting on a line gives the line
through the image of its generator, so a group element stabilizes the line through a vector
exactly when it sends that vector to a multiple of itself. A submodule over a
subring that is a direct sum `⊕ i, J i • y i` with nonzero ideal coefficients spans the same
subspace over the division ring as the family `y`. A unitriangular change of a family indexed by a
well-founded order, where each `z j` is `x j` plus a combination of the earlier `x l`, preserves
the spans of initial segments and of the whole family. A ring homomorphism carries a span over
`A` into a span over `B` as soon as it carries the generators into the target span and the
scalars in `A` to scalars in `B`. Over a scalar extension, the image span of a semilinear map is
spanned by its values on any spanning family of the domain, and a family vanishing off the range
of a map `e` spans the same submodule as its restriction along `e`. A property closed under
`u + a • v` extends from a submodule `S` and a vector `x` to `S ⊔ (R ∙ x)`. The span of any
countable set admits a spanning sequence indexed by `ℕ`
(`Set.Countable.exists_span_range_eq_top`). When a generating set is closed under scalar
multiplication, the additive subgroup underlying its span equals the additive subgroup it
generates (`Submodule.span_eq_addSubgroupClosure_of_smul_mem`). If `r ↦ r • x` is injective, then
`r ↦ r • x` identifies `R` with the line `R ∙ x`
(`LinearEquiv.toSpanSingletonOfInjective`); for instance a non-zero-divisor `x` of a commutative
ring identifies the ring with the principal ideal it generates.
-/

public section

namespace TauCeti.Submodule

variable {A : Type*} [Ring A] {M : Type*} [AddCommGroup M] [Module A M]

/-- If one coefficient of `x` in a finite span is a unit, then `x` can replace that generator. -/
theorem span_insert_erase_eq_span_of_isUnit [DecidableEq M] {s : Finset M} {i x : M}
    {f : M → A} (hi : i ∈ s) (hf : ∑ a ∈ s, f a • a = x) (hfi : IsUnit (f i)) :
    _root_.Submodule.span A ((insert x (s.erase i)) : Set M) =
      _root_.Submodule.span A (s : Set M) := by
  have hx : x ∈ _root_.Submodule.span A (s : Set M) :=
    hf ▸ sum_mem fun a ha ↦ Submodule.smul_mem _ _ (Submodule.subset_span ha)
  have hi' : i ∈ _root_.Submodule.span A (insert x (s.erase i : Set M)) := by
    refine (Submodule.smul_mem_iff_of_isUnit _ hfi).mp (Submodule.mem_span_insert.mpr
      ⟨1, -∑ a ∈ s.erase i, f a • a,
        neg_mem (sum_mem fun a ha ↦ Submodule.smul_mem _ _ (Submodule.subset_span ha)), ?_⟩)
    rw [one_smul, ← hf, ← Finset.add_sum_erase _ _ hi, add_neg_cancel_right]
  calc _ = _root_.Submodule.span A (insert i (insert x (s.erase i : Set M))) :=
        (Submodule.span_insert_eq_span hi').symm
    _ = _root_.Submodule.span A (insert x (s : Set M)) := by
      rw [Set.insert_comm, ← Finset.coe_insert, Finset.insert_erase hi]
    _ = _ := Submodule.span_insert_eq_span hx

end TauCeti.Submodule

namespace Submodule

/-- A property `P` closed under `u + a • v` holds on `S ⊔ (R ∙ x)` when it holds on `S` and at
`x`. -/
theorem forall_mem_sup_span_singleton {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    {S : Submodule R M} {x : M} {P : M → Prop} (hS : ∀ s ∈ S, P s) (hx : P x)
    (hlin : ∀ u v (a : R), P u → P v → P (u + a • v)) : ∀ s ∈ S ⊔ (R ∙ x), P s := by
  intro _ hw
  obtain ⟨s, hs, _, ht, rfl⟩ := Submodule.mem_sup.mp hw
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp ht
  exact hlin s x a (hS s hs) hx

/-- A vector outside the line `R ∙ v` is not cancelled by adding any multiple of `v`. -/
theorem add_smul_ne_zero_of_notMem_span_singleton {R M : Type*} [Ring R] [AddCommGroup M]
    [Module R M] {v y : M} (hy : y ∉ R ∙ v) (r : R) : y + r • v ≠ 0 := fun h ↦
  hy <| (Submodule.add_mem_iff_left _ (smul_mem _ r (mem_span_singleton_self v))).mp
    (h ▸ zero_mem _)

variable {K V : Type*} [DivisionSemiring K] [AddCommMonoid V] [Module K V]

/-- If a nonzero member of a submodule lies in the span of `y`, then `y` also belongs to
the submodule. -/
theorem mem_of_mem_span_singleton_of_ne_zero (P : Submodule K V) {x y : V}
    (hx : x ∈ P) (hx0 : x ≠ 0) (hxy : x ∈ K ∙ y) : y ∈ P := by
  obtain ⟨c, rfl⟩ := mem_span_singleton.mp hxy
  exact (P.smul_mem_iff (left_ne_zero_of_smul hx0)).mp hx

section Action

open Pointwise

variable {R M G : Type*} [Semiring R] [AddCommMonoid M] [Module R M] [Monoid G]
  [DistribMulAction G M] [SMulCommClass G R M]

/-- Acting on the line through `v` gives the line through the image of `v`. -/
theorem smul_span_singleton (g : G) (v : M) : g • (R ∙ v) = R ∙ (g • v) := by
  rw [smul_span, Set.smul_set_singleton]

end Action

section GroupAction

open Pointwise

variable {D W G : Type*} [DivisionRing D] [AddCommGroup W] [Module D W] [Group G]
  [DistribMulAction G W] [SMulCommClass G D W]

/-- A group element stabilizes the line through `v` exactly when `g • v` is a multiple of `v`. -/
theorem smul_span_singleton_eq_iff {g : G} {v : W} :
    g • (D ∙ v) = D ∙ v ↔ ∃ c : D, g • v = c • v := by
  rw [smul_span_singleton]
  refine ⟨fun h ↦ (mem_span_singleton.mp (h ▸ mem_span_singleton_self (g • v))).imp
    fun _ ↦ Eq.symm, fun ⟨c, hc⟩ ↦ ?_⟩
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  -- `c ≠ 0` because `g • v ≠ 0`, so `c • v` spans the same line as `v`.
  have hc0 : c ≠ 0 := left_ne_zero_of_smul (hc ▸ (smul_ne_zero_iff_ne g).mpr hv)
  rw [hc, span_singleton_smul_eq (IsUnit.mk0 c hc0)]

end GroupAction

section IdealCoefficients

variable {R K V : Type*} [CommSemiring R] [DivisionRing K] [Algebra R K] [AddCommMonoid V]
  [Module K V] [Module R V] [IsScalarTower R K V]

/-- If `Λ = ⊕ i, J i • y i` with every `J i` nonzero, then `y` spans the same `K`-subspace as
`Λ`. -/
theorem span_range_eq_span_of_forall_mem_iff [FaithfulSMul R K] {ι : Type*} [Fintype ι]
    {Λ : Submodule R V} {y : ι → V} {J : ι → Ideal R} (hJ : ∀ i, J i ≠ ⊥)
    (hmem : ∀ x, x ∈ Λ ↔ ∃ c : ι → R, (∀ i, c i ∈ J i) ∧ ∑ i, c i • y i = x) :
    span K (Set.range y) = span K (Λ : Set V) := by
  classical
  refine le_antisymm (span_le.2 <| Set.range_subset_iff.2 fun i ↦ ?_) (span_le.2 fun x hx ↦ ?_)
  · obtain ⟨b, hb, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (hJ i)
    -- The coefficient family `Pi.single i b` exhibits `b • y i` as an element of `Λ`.
    have hbΛ : b • y i ∈ Λ := (hmem _).2 ⟨Pi.single i b, fun k ↦ by
      obtain rfl | hk := eq_or_ne k i
      · simpa using hb
      · simp [hk], by simp [Pi.single_apply, ite_smul]⟩
    have hb' : algebraMap R K b ≠ 0 :=
      (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective R K)).2 hb0
    rw [← inv_smul_smul₀ hb' (y i), algebraMap_smul]
    exact smul_mem _ _ (subset_span hbΛ)
  · obtain ⟨c, -, rfl⟩ := (hmem x).1 hx
    exact sum_mem fun i _ ↦ by
      rw [← algebraMap_smul K]
      exact smul_mem _ _ (subset_span ⟨i, rfl⟩)

end IdealCoefficients

section Unitriangular

variable {R M ι : Type*} [Ring R] [AddCommGroup M] [Module R M] [Preorder ι] [WellFoundedLT ι]

/-- Initial segments of `x` and `z` span the same submodule when every `z j` is `x j` plus a
combination of the earlier `x l`. -/
theorem span_image_Iio_eq_span_image_Iio {x z : ι → M}
    (h : ∀ j, z j - x j ∈ span R (x '' Set.Iio j)) (j : ι) :
    span R (z '' Set.Iio j) = span R (x '' Set.Iio j) := by
  refine le_antisymm (span_le.2 ?_) ?_
  · rintro _ ⟨l, hl, rfl⟩
    have hmem := add_mem (span_mono (Set.image_mono (Set.Iio_subset_Iio hl.le)) (h l))
      (subset_span (R := R) ⟨l, hl, rfl⟩)
    rwa [sub_add_cancel] at hmem
  induction j using WellFoundedLT.induction with
  | _ j ih =>
    rw [span_le]
    rintro _ ⟨l, hl, rfl⟩
    have hmem := sub_mem (subset_span (R := R) (Set.mem_image_of_mem z hl)) <|
      span_mono (Set.image_mono (Set.Iio_subset_Iio hl.le)) (ih l hl (h l))
    rwa [sub_sub_cancel] at hmem

/-- Two families span the same submodule when every `z j` is `x j` plus a combination of the
earlier `x l`. -/
theorem span_range_eq_span_range_of_sub_mem_span {x z : ι → M}
    (h : ∀ j, z j - x j ∈ span R (x '' Set.Iio j)) :
    span R (Set.range z) = span R (Set.range x) := by
  refine le_antisymm (span_le.2 ?_) (span_le.2 ?_)
  · rintro _ ⟨j, rfl⟩
    have hmem := add_mem (span_mono (Set.image_subset_range x _) (h j))
      (subset_span (R := R) (Set.mem_range_self j))
    rwa [sub_add_cancel] at hmem
  · rintro _ ⟨j, rfl⟩
    have hj : z j - x j ∈ span R (z '' Set.Iio j) := span_image_Iio_eq_span_image_Iio h j ▸ h j
    have hmem := sub_mem (subset_span (R := R) (Set.mem_range_self (f := z) j))
      (span_mono (Set.image_subset_range z _) hj)
    rwa [sub_sub_cancel] at hmem

end Unitriangular

section RingHom

/-- A ring homomorphism `f : R → S` carries `span_A T` into `span_B T'` as soon as it carries
every generator in `T` into `span_B T'` and the image of every scalar in `A` is a scalar in `B`.
Unlike `Submodule.apply_mem_span_image_of_mem_span`, no ring map `A → B` is required. -/
theorem map_mem_span_of_forall_exists {A B R S : Type*} [CommSemiring A] [CommSemiring B]
    [Semiring R] [Semiring S] [Algebra A R] [Algebra B S] (f : R →+* S) (T : Set R) (T' : Set S)
    (hA : ∀ r : A, ∃ b : B, f (algebraMap A R r) = algebraMap B S b)
    (hT : ∀ t ∈ T, f t ∈ Submodule.span B T') {z : R} (hz : z ∈ Submodule.span A T) :
    f z ∈ Submodule.span B T' := by
  induction hz using Submodule.span_induction with
  | mem x hx => exact hT x hx
  | zero => simp
  | add x y _ _ hx hy => simpa using add_mem hx hy
  | smul r x _ hx =>
    obtain ⟨b, hb⟩ := hA r
    rw [Algebra.smul_def, map_mul, hb, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ hx

end RingHom

section SpanningFamily

/-- Over a scalar extension, the image of a semilinear map is spanned by its values on any
spanning family. The ring homomorphism defining semilinearity need not be surjective. -/
theorem span_range_eq_span_range_comp_of_span_eq_top
    {R R' S M N ι : Type*} [Semiring R] [Semiring R'] [Semiring S] [SMul R' S]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R' N]
    [Module S N] [IsScalarTower R' S N] {σ : R →+* R'} {v : ι → M}
    (hv : span R (Set.range v) = ⊤) (f : M →ₛₗ[σ] N) :
    span S (Set.range f) = span S (Set.range (f ∘ v)) := by
  refine le_antisymm (span_le.mpr ?_) (span_mono (Set.range_comp_subset_range _ _))
  rintro _ ⟨x, rfl⟩
  exact (image_span_subset f _ ((span S (Set.range (f ∘ v))).restrictScalars R')).mpr
    (Set.forall_mem_range.mpr fun i ↦ subset_span ⟨i, rfl⟩) ⟨x, hv ▸ mem_top, rfl⟩

/-- A family that vanishes off the range of `e` spans the same submodule as its restriction
along `e`. -/
theorem span_range_eq_span_range_comp_of_eq_zero {R M ι κ : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M] (e : κ → ι) {w : ι → M} (h : ∀ i ∉ Set.range e, w i = 0) :
    span R (Set.range w) = span R (Set.range (w ∘ e)) := by
  refine le_antisymm (span_le.mpr ?_) (span_mono (Set.range_comp_subset_range _ _))
  rintro _ ⟨i, rfl⟩
  by_cases hi : i ∈ Set.range e
  · obtain ⟨j, rfl⟩ := hi
    exact subset_span ⟨j, rfl⟩
  · rw [h i hi]
    exact zero_mem _

end SpanningFamily

section AddSubgroup

/-- If `s` is closed under scalar multiplication by `R`, then the additive subgroup underlying its
`R`-linear span `Submodule.span R s` coincides with the additive subgroup generated by `s`. -/
theorem span_eq_addSubgroupClosure_of_smul_mem {R M : Type*} [Ring R] [AddCommGroup M]
    [Module R M] {s : Set M} (hs : ∀ r : R, ∀ x ∈ s, r • x ∈ s) :
    (span R s).toAddSubgroup = AddSubgroup.closure s := by
  refine le_antisymm ?_ ((span R s).toAddSubgroup.closure_le.mpr subset_span)
  let p : Submodule R M :=
    { toAddSubmonoid := (AddSubgroup.closure s).toAddSubmonoid
      smul_mem' := fun r x hx => by
        rw [AddSubmonoid.mem_carrier, AddSubgroup.mem_toAddSubmonoid] at hx ⊢
        induction hx using AddSubgroup.closure_induction with
        | mem y hy => exact AddSubgroup.subset_closure (hs r y hy)
        | zero => simp
        | add y z _ _ hy hz => simpa [smul_add] using AddSubgroup.add_mem _ hy hz
        | neg y _ hy => simpa [smul_neg] using AddSubgroup.neg_mem _ hy }
  exact (span_le (p := p)).mpr AddSubgroup.subset_closure

end AddSubgroup

end Submodule

section Countable

/-- The `R`-span of a countable set `s` admits a spanning sequence `v : ℕ → Submodule.span R s`
with `Submodule.span R (Set.range v) = ⊤`. -/
theorem Set.Countable.exists_span_range_eq_top (R : Type*) {M : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M] {s : Set M} (hs : s.Countable) :
    ∃ v : ℕ → Submodule.span R s, Submodule.span R (Set.range v) = ⊤ := by
  obtain ⟨f, hf⟩ := (hs.insert 0).exists_eq_range (Set.insert_nonempty 0 s)
  have hfs (n : ℕ) : f n ∈ Submodule.span R s :=
    Set.insert_subset (Submodule.zero_mem _) Submodule.subset_span (hf ▸ Set.mem_range_self n)
  exact ⟨fun n ↦ ⟨f n, hfs n⟩, (Submodule.span_range_subtype_eq_top_iff _ hfs).2 <| by
    rw [← hf, Submodule.span_insert_zero]⟩

end Countable

namespace LinearEquiv

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] (x : M)
  (hx : Function.Injective fun r : R ↦ r • x)

/-- If `r ↦ r • x` is injective, the natural isomorphism `R ≃ₗ[R] R ∙ x`, `r ↦ r • x`. This
extends Mathlib's `LinearEquiv.toSpanNonzeroSingleton` from torsion-free modules over domains; for
instance it applies to a non-zero-divisor `x` of a commutative ring `R`, identifying `R` with the
principal ideal `x R`. -/
noncomputable def toSpanSingletonOfInjective : R ≃ₗ[R] R ∙ x :=
  (LinearEquiv.ofInjective (LinearMap.toSpanSingleton R M x) hx).trans
    (LinearEquiv.ofEq _ _ (LinearMap.range_toSpanSingleton x))

@[simp]
theorem coe_toSpanSingletonOfInjective_apply (r : R) :
    (toSpanSingletonOfInjective x hx r : M) = r • x :=
  (rfl)

@[simp]
theorem toSpanSingletonOfInjective_symm_apply_smul (y : R ∙ x) :
    (toSpanSingletonOfInjective x hx).symm y • x = y :=
  congrArg Subtype.val ((toSpanSingletonOfInjective x hx).apply_symm_apply y)

@[simp]
theorem toSpanSingletonOfInjective_symm_mk_smul (r : R) :
    (toSpanSingletonOfInjective x hx).symm
      ⟨r • x, Submodule.smul_mem _ r (Submodule.mem_span_singleton_self x)⟩ = r :=
  (toSpanSingletonOfInjective x hx).symm_apply_apply r

end LinearEquiv

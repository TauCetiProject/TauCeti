/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.Algebra.GradedMulAction
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Pi
import TauCeti.LinearAlgebra.Submodule.Independent

/-!
# Internal direct sums from explicit equivalences

This file provides reusable infrastructure for direct sums of submodules.  The generic
`DirectSum.piInclusion`, `DirectSum.piSubmodule`, and `DirectSum.piSubmoduleEquiv` declarations
describe their componentwise inclusion and range, while `DirectSum.isInternal_of_lof` gives a
criterion for proving that a family of submodules is an internal direct sum by identifying its
summands with the components of a linear equivalence.

A second group of declarations concerns maps between decompositions.
`DirectSum.decompose_map_eq_sum` computes a target component by summing source components
over its degree fiber, with no injectivity or finite-fiber assumption on the degree map;
applied to the identity map, `DirectSum.Decomposition.eq_zero_of_mem_of_forall_ne` shows that any
summand of a second decomposition whose degree lies outside the image of the degree map is zero.
This formula is adapted from `Mei/Algebra/DirectSum/Map.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei),
commit `bac6f02d25746bc1c2ec808601d4e9284911c475` (Apache 2.0),
by the Mei contributors (Authors: Codex).
`DirectSum.map_decompose_shift` says that an additive map carrying each summand of one
decomposition into a summand of another, along an injective reindexing of the degrees, commutes
with the homogeneous projections; applied to the identity map,
`DirectSum.Decomposition.mem_iff_of_mem_shift`, `DirectSum.Decomposition.eq_of_subset_shift`, and
`DirectSum.Decomposition.eq_of_subset` show that one-sided inclusion between internal
decompositions along an injective reindexing (or on the same index type) implies componentwise
equality. Meanwhile, `DirectSum.isInternal_comap` and
`DirectSum.Decomposition.restrict` transport a decomposition backwards along an injective linear
map whose range contains the homogeneous projections of its elements, with
`DirectSum.map_decompose_restrict` computing the projections of the restricted decomposition.

A third group is about maps compatible with a decomposition. Two linear maps out of a finite
product `P → M` agree as soon as they agree on the homogeneous single-coordinate functions
`Pi.single x α`, `LinearMap.pi_ext_of_decomposition`, and two additive maps out of `α →₀ M`
agree as soon as they agree on the homogeneous singles `Finsupp.single x c`,
`Finsupp.addHom_ext_of_decomposition`.

`DirectSum.IsInternal.iSup_fiber` collects an internal decomposition along the fibers of any map,
`DirectSum.IsInternal.comp_equiv` reindexes one along an equivalence of the index types, and
`DirectSum.IsInternal.nat_cons_bot` prepends the zero submodule to a natural-number-indexed
internal decomposition.

`DirectSum.IsInternal.iSup_inf_eq_of_component_mem` restricts an internal decomposition to any
submodule that contains the canonical components of each of its elements,
`DirectSum.mem_of_forall_ne_eq_bot` shows that when all pieces outside one degree vanish, every
element lies in that piece, and over a ring `DirectSum.isInternal_submodule_comap_subtype` turns a
supremum-independent family with supremum `S` into an internal direct sum of `S` via
`(A i).comap S.subtype`. Over any additive commutative monoid, if two sums over the same `Finset`
take their `i`-th terms from the `i`-th summand of an internal direct sum and are equal, then their
terms are equal at every index of that `Finset` (`DirectSum.IsInternal.eq_of_finsetSum_eq`).

`DirectSum.support_decompose_nonempty_iff` and `DirectSum.mem_support_decompose_iff` characterize
nonemptiness and membership in `(DirectSum.decompose ℳ x).support` in terms of nonvanishing of `x`
and its homogeneous components `(DirectSum.decompose ℳ x i : M)`.
`DirectSum.coe_decompose_smul_add_of_right_mem` computes the components of a scalar
action on a homogeneous element when the scalar and module decompositions are compatible.
When the ambient carrier is an additive commutative group, `DirectSum.coe_decompose_neg` shows that
homogeneous projections commute with negation even when the summand type carries only
`AddSubmonoidClass` (such as submodules over a semiring), giving closure of each summand under
negation, subtraction, and integer scaling (`DirectSum.Decomposition.neg_mem`,
`DirectSum.Decomposition.sub_mem`, `DirectSum.Decomposition.zsmul_mem`).

Finally, the external direct sum `⨁ i, M i` of a family of `R`-modules is the internal direct sum
of its summands `DirectSum.summand R M i`, the ranges of the inclusions `DirectSum.lof R ι M i`
(`DirectSum.isInternal_summand`). The resulting decomposition `DirectSum.instDecompositionSummand`
has `i`-th component `DirectSum.of M i (x i)` (`DirectSum.coe_decompose_summand`).

Over any semiring, the spans of the basis vectors in the fibers of a map on the index set of a basis
form an internal direct sum (`Module.Basis.isInternal_span_image_fiber`), and the basis vectors in
one fiber form a basis of their span (`Module.Basis.spanImageFiber`).
-/

public section

open scoped DirectSum

namespace TauCeti

/-- The canonical inclusion of a direct sum of submodules into the direct sum of their ambient
modules. -/
def DirectSum.piInclusion {R ι : Type*} {M : ι → Type*} [Semiring R]
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] (N : ∀ i, Submodule R (M i)) :
    (⨁ i, N i) →ₗ[R] ⨁ i, M i :=
  DirectSum.lmap fun i ↦ (N i).subtype

/-- The submodule of the direct sum consisting of elements whose components lie in the given
submodules. -/
def DirectSum.piSubmodule {R ι : Type*} {M : ι → Type*} [Semiring R]
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] (N : ∀ i, Submodule R (M i)) :
    Submodule R (⨁ i, M i) :=
  LinearMap.range (DirectSum.piInclusion N)

/-- The componentwise formula for the inclusion of a direct sum of submodules. -/
@[simp]
theorem DirectSum.piInclusion_apply {R ι : Type*} {M : ι → Type*} [Semiring R]
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] (N : ∀ i, Submodule R (M i))
    (x : ⨁ i, N i) (i : ι) :
    DirectSum.piInclusion N x i = (x i : M i) := by
  rw [DirectSum.piInclusion, DirectSum.lmap_apply, Submodule.coe_subtype]

/-- The inclusion of a generator of a direct sum of submodules. -/
@[simp]
theorem DirectSum.piInclusion_lof {R ι : Type*} {M : ι → Type*} [Semiring R]
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] (N : ∀ i, Submodule R (M i)) (i : ι)
    (x : N i)
    [DecidableEq ι] :
    DirectSum.piInclusion N
        (DirectSum.lof R ι (fun i ↦ N i) i x) = DirectSum.lof R ι (fun i ↦ M i) i x := by
  rw [DirectSum.piInclusion, DirectSum.lmap_lof, Submodule.coe_subtype]

private theorem DirectSum.piInclusion_injective {R ι : Type*} {M : ι → Type*} [Semiring R]
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] (N : ∀ i, Submodule R (M i)) :
    Function.Injective (DirectSum.piInclusion N) := by
  rw [DirectSum.piInclusion]
  refine (DirectSum.lmap_injective fun i ↦ (N i).subtype).mpr fun i ↦ ?_
  exact (N i).injective_subtype

/-- The linear equivalence from the direct sum of submodules to `piSubmodule N`. -/
noncomputable def DirectSum.piSubmoduleEquiv {R ι : Type*} {M : ι → Type*} [Semiring R]
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] (N : ∀ i, Submodule R (M i)) :
    (⨁ i, N i) ≃ₗ[R] DirectSum.piSubmodule N :=
  LinearEquiv.ofInjective (DirectSum.piInclusion N)
    (DirectSum.piInclusion_injective N)

/-- The underlying map of `piSubmoduleEquiv` is the canonical inclusion. -/
@[simp]
theorem DirectSum.piSubmoduleEquiv_apply {R ι : Type*} {M : ι → Type*} [Semiring R]
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] (N : ∀ i, Submodule R (M i))
    (x : ⨁ i, N i) :
    ((DirectSum.piSubmoduleEquiv N x : DirectSum.piSubmodule N) :
      ⨁ i, M i) = DirectSum.piInclusion N x := by
  rw [DirectSum.piSubmoduleEquiv]
  exact LinearEquiv.ofInjective_apply _ x

/-- The inverse of `piSubmoduleEquiv` has the expected componentwise values. -/
@[simp]
theorem DirectSum.piSubmoduleEquiv_symm_apply {R ι : Type*} {M : ι → Type*} [Semiring R]
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] (N : ∀ i, Submodule R (M i))
    (y : DirectSum.piSubmodule N) (i : ι) :
    ((DirectSum.piSubmoduleEquiv N).symm y i : M i) = (y : ⨁ i, M i) i := by
  have h := DirectSum.piSubmoduleEquiv_apply N
    ((DirectSum.piSubmoduleEquiv N).symm y)
  rw [LinearEquiv.apply_symm_apply] at h
  have hi := congrArg (fun z : ⨁ i, M i ↦ z i) h
  simpa only [DirectSum.piInclusion_apply] using hi.symm

/-- Membership in the direct sum of a family of submodules is componentwise. -/
@[simp]
theorem DirectSum.mem_piSubmodule_iff {R ι : Type*} {M : ι → Type*} [Semiring R]
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] (N : ∀ i, Submodule R (M i))
    (x : ⨁ i, M i) :
    x ∈ DirectSum.piSubmodule N ↔ ∀ i, x i ∈ N i := by
  rw [DirectSum.piSubmodule, DirectSum.piInclusion, DirectSum.range_lmap]
  simp [Submodule.mem_comap, DirectSum.coeFnLinearMap_apply, Submodule.mem_pi]

/-- An included summand belongs to the direct sum of a family of submodules. -/
theorem DirectSum.lof_mem_piSubmodule {R ι : Type*} {M : ι → Type*} [Semiring R]
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] (N : ∀ i, Submodule R (M i)) (i : ι)
    (x : N i)
    [DecidableEq ι] :
    DirectSum.lof R ι M i x ∈ DirectSum.piSubmodule N := by
  refine ⟨DirectSum.lof R ι (fun i ↦ N i) i x, ?_⟩
  exact DirectSum.piInclusion_lof N i x

/-- Restrict an internal direct sum decomposition along an injective linear map `f` which detects
membership in the summands and whose range contains every homogeneous projection of each of its
elements: the summands `𝓝` pulled back from `ℳ` are again an internal direct sum. -/
theorem DirectSum.isInternal_comap {R ι M N : Type*} [Semiring R]
    [DecidableEq ι] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    (ℳ : ι → Submodule R M) [DirectSum.Decomposition ℳ] (𝓝 : ι → Submodule R N)
    (f : N →ₗ[R] M) (hf : Function.Injective f)
    (hmem : ∀ i x, x ∈ 𝓝 i ↔ f x ∈ ℳ i)
    (hproj : ∀ i x, (DirectSum.decompose ℳ (f x) i : M) ∈ LinearMap.range f) :
    DirectSum.IsInternal 𝓝 := by
  classical
  let φ : ∀ i, 𝓝 i →ₗ[R] ℳ i := fun i ↦
    (f.comp (𝓝 i).subtype).codRestrict (ℳ i) fun x ↦ (hmem i x).mp x.property
  have hφ : ∀ (i : ι) (x : 𝓝 i), (φ i x : M) = f x := fun _ _ ↦ rfl
  have hΦinj : Function.Injective (DirectSum.lmap φ) :=
    (DirectSum.lmap_injective φ).mpr fun i x y hxy ↦
      Subtype.ext (hf (by rw [← hφ i x, ← hφ i y, hxy]))
  have hcoe : ∀ y : ⨁ i, 𝓝 i, f (DirectSum.coeAddMonoidHom 𝓝 y) =
      DirectSum.coeAddMonoidHom ℳ (DirectSum.lmap φ y) := by
    intro y
    induction y using DirectSum.induction_on with
    | zero => simp
    | of i x =>
      simp only [DirectSum.lmap_of, DirectSum.coeAddMonoidHom_of]
      exact hφ i x
    | add y z hy hz => simp [hy, hz]
  have hsurj : ∀ x : N, ∃ y : ⨁ i, 𝓝 i,
      DirectSum.lmap φ y = DirectSum.decompose ℳ (f x) := by
    intro x
    have hmemrange : DirectSum.decompose ℳ (f x) ∈ LinearMap.range (DirectSum.lmap φ) := by
      rw [← DirectSum.sum_support_of (DirectSum.decompose ℳ (f x))]
      refine Submodule.sum_mem _ fun i _ ↦ ?_
      obtain ⟨n, hn⟩ := hproj i x
      have hn' : n ∈ 𝓝 i := (hmem i n).mpr (by rw [hn]; exact SetLike.coe_mem _)
      refine ⟨DirectSum.of (fun i ↦ 𝓝 i) i ⟨n, hn'⟩, ?_⟩
      rw [DirectSum.lmap_of]
      exact congrArg _ (Subtype.ext hn)
    exact hmemrange
  refine ⟨fun y z hyz ↦ hΦinj ((DirectSum.Decomposition.isInternal ℳ).injective ?_), fun x ↦ ?_⟩
  · rw [← hcoe, ← hcoe, hyz]
  · obtain ⟨y, hy⟩ := hsurj x
    refine ⟨y, hf ?_⟩
    rw [hcoe, hy]
    simpa using DirectSum.Decomposition.left_inv (ℳ := ℳ) (f x)

/-- Restrict an internal decomposition along an injective linear map whose range contains every
homogeneous projection of each of its elements. -/
@[instance_reducible]
noncomputable def DirectSum.Decomposition.restrict {R ι M N : Type*} [Semiring R]
    [DecidableEq ι] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    (ℳ : ι → Submodule R M) [DirectSum.Decomposition ℳ] (𝓝 : ι → Submodule R N)
    (f : N →ₗ[R] M) (hf : Function.Injective f) (hmem : ∀ i x, x ∈ 𝓝 i ↔ f x ∈ ℳ i)
    (hproj : ∀ i x, (DirectSum.decompose ℳ (f x) i : M) ∈ LinearMap.range f) :
    DirectSum.Decomposition 𝓝 :=
  (DirectSum.isInternal_comap ℳ 𝓝 f hf hmem hproj).chooseDecomposition

end TauCeti

namespace DirectSum

open Classical in
/-- Under a homogeneous additive map, a target component is the finite sum of the images
of the source components whose degrees map to that target degree. -/
theorem decompose_map_eq_sum {ι κ M N S T : Type*}
    [DecidableEq ι] [DecidableEq κ] [AddCommMonoid M] [AddCommMonoid N]
    [SetLike S M] [AddSubmonoidClass S M] [SetLike T N] [AddSubmonoidClass T N]
    (ℳ : ι → S) [Decomposition ℳ] (𝓝 : κ → T) [Decomposition 𝓝]
    (f : M →+ N) (σ : ι → κ)
    (hf : ∀ i x, x ∈ ℳ i → f x ∈ 𝓝 (σ i)) (x : M) (j : κ) :
    (decompose 𝓝 (f x) j : N) =
      ∑ i ∈ (decompose ℳ x).support with σ i = j, f (decompose ℳ x i : M) := by
  have hproj (i : ι) :
      (decompose 𝓝 (f (decompose ℳ x i : M)) j : N) =
        if σ i = j then f (decompose ℳ x i : M) else 0 := by
    split_ifs with h
    · exact decompose_of_mem_same 𝓝 (h ▸ hf i _ (decompose ℳ x i).property)
    · exact decompose_of_mem_ne 𝓝 (hf i _ (decompose ℳ x i).property) h
  calc
    (decompose 𝓝 (f x) j : N) =
        (decompose 𝓝 (f (∑ i ∈ (decompose ℳ x).support,
          (decompose ℳ x i : M))) j : N) := by rw [sum_support_decompose]
    _ = ∑ i ∈ (decompose ℳ x).support,
        (decompose 𝓝 (f (decompose ℳ x i : M)) j : N) := by
      simp only [map_sum, decompose_sum, sum_apply]
      exact map_sum (AddSubmonoidClass.subtype (𝓝 j)) _ _
    _ = _ := by simp_rw [hproj]; rw [Finset.sum_filter]

open Classical in
/-- If an internal decomposition `ℳ` maps into an internal decomposition `𝓝` of the same
additive commutative monoid along a degree map `σ : ι → κ`, any element of a summand `𝓝 j`
whose degree `j` lies outside the image of `σ` is zero. -/
theorem Decomposition.eq_zero_of_mem_of_forall_ne {ι κ M S T : Type*}
    [DecidableEq ι] [DecidableEq κ] [AddCommMonoid M]
    [SetLike S M] [AddSubmonoidClass S M] [SetLike T M] [AddSubmonoidClass T M]
    (ℳ : ι → S) [Decomposition ℳ] (𝓝 : κ → T) [Decomposition 𝓝]
    {σ : ι → κ} (h : ∀ i ⦃x : M⦄, x ∈ ℳ i → x ∈ 𝓝 (σ i))
    {j : κ} (hj : ∀ i, σ i ≠ j) {x : M} (hx : x ∈ 𝓝 j) : x = 0 := by
  rw [← decompose_of_mem_same 𝓝 hx]
  have hsum := decompose_map_eq_sum ℳ 𝓝 (AddMonoidHom.id M) σ (fun i _ hy ↦ h i hy) x j
  simp only [AddMonoidHom.id_apply] at hsum
  exact hsum.trans (Finset.sum_eq_zero fun i hi ↦ (hj i (Finset.mem_filter.mp hi).2).elim)

/-- An additive map which carries the degree-`i` summand of one internal decomposition into the
degree-`σ i` summand of another, along an injective reindexing `σ` of the degrees, commutes with
the homogeneous projections. The summands may be any additive subobjects, including submodules
over unrelated scalar semirings. -/
theorem map_decompose_shift {ι κ M N S T : Type*}
    [DecidableEq ι] [DecidableEq κ] [AddCommMonoid M] [AddCommMonoid N]
    [SetLike S M] [AddSubmonoidClass S M] [SetLike T N] [AddSubmonoidClass T N]
    (ℳ : ι → S) [Decomposition ℳ] (𝓝 : κ → T)
    [Decomposition 𝓝] (f : M →+ N) (σ : ι → κ) (hσ : Function.Injective σ)
    (hf : ∀ (i : ι) (x : M), x ∈ ℳ i → f x ∈ 𝓝 (σ i)) (i : ι) (x : M) :
    f (decompose ℳ x i : M) = (decompose 𝓝 (f x) (σ i) : N) := by
  induction x using Decomposition.inductionOn ℳ with
  | zero => simp
  | @homogeneous j x =>
    have hxM : (x : M) ∈ ℳ j := x.property
    have hxN : f (x : M) ∈ 𝓝 (σ j) := hf j x hxM
    by_cases hij : i = j
    · subst hij
      rw [decompose_of_mem_same ℳ hxM, decompose_of_mem_same 𝓝 hxN]
    · rw [decompose_of_mem_ne ℳ hxM (Ne.symm hij), map_zero,
        decompose_of_mem_ne 𝓝 hxN fun hc ↦ Ne.symm hij (hσ hc)]
  | add x y hx hy => simp [hx, hy]

/-- If an internal decomposition `ℳ` maps into an internal decomposition `𝓝` of the same
additive commutative monoid along an injective reindexing `σ` of the degrees, then each summand
`ℳ i` has the same elements as `𝓝 (σ i)`. -/
theorem Decomposition.mem_iff_of_mem_shift {ι κ M S T : Type*}
    [DecidableEq ι] [DecidableEq κ] [AddCommMonoid M]
    [SetLike S M] [AddSubmonoidClass S M] [SetLike T M] [AddSubmonoidClass T M]
    (ℳ : ι → S) [Decomposition ℳ] (𝓝 : κ → T) [Decomposition 𝓝]
    {σ : ι → κ} (hσ : Function.Injective σ)
    (h : ∀ i ⦃x : M⦄, x ∈ ℳ i → x ∈ 𝓝 (σ i)) (i : ι) {x : M} :
    x ∈ ℳ i ↔ x ∈ 𝓝 (σ i) := by
  refine ⟨fun hx ↦ h i hx, fun hx ↦ ?_⟩
  have hproj := map_decompose_shift ℳ 𝓝 (AddMonoidHom.id M) σ hσ (fun j _ hy ↦ h j hy) i x
  simp only [AddMonoidHom.id_apply, decompose_of_mem_same 𝓝 hx] at hproj
  exact hproj ▸ (decompose ℳ x i).property

/-- If each summand of an internal decomposition `ℳ` is contained in the `σ`-shifted summand of
an internal decomposition `𝓝` along an injective reindexing `σ`, then `ℳ i = 𝓝 (σ i)`. -/
theorem Decomposition.eq_of_subset_shift {ι κ M S : Type*}
    [DecidableEq ι] [DecidableEq κ] [AddCommMonoid M]
    [SetLike S M] [AddSubmonoidClass S M]
    (ℳ : ι → S) [Decomposition ℳ] (𝓝 : κ → S) [Decomposition 𝓝]
    {σ : ι → κ} (hσ : Function.Injective σ)
    (h : ∀ i ⦃x : M⦄, x ∈ ℳ i → x ∈ 𝓝 (σ i)) (i : ι) :
    ℳ i = 𝓝 (σ i) :=
  SetLike.ext fun _ ↦ Decomposition.mem_iff_of_mem_shift ℳ 𝓝 hσ h i

/-- Two internal decompositions of an additive commutative monoid indexed by the same type are
equal as soon as each summand of the first is contained in the corresponding summand of the
second. -/
theorem Decomposition.eq_of_subset {ι M S : Type*} [DecidableEq ι] [AddCommMonoid M]
    [SetLike S M] [AddSubmonoidClass S M] (ℳ 𝓝 : ι → S) [Decomposition ℳ] [Decomposition 𝓝]
    (h : ∀ i ⦃x : M⦄, x ∈ ℳ i → x ∈ 𝓝 i) : ℳ = 𝓝 :=
  funext (Decomposition.eq_of_subset_shift ℳ 𝓝 Function.injective_id h)

end DirectSum

namespace TauCeti

/-- Homogeneous projection in a restricted decomposition agrees with projection in the ambient
module. -/
@[simp]
theorem DirectSum.map_decompose_restrict {R ι M N : Type*} [Semiring R]
    [DecidableEq ι] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    (ℳ : ι → Submodule R M) [DirectSum.Decomposition ℳ] (𝓝 : ι → Submodule R N)
    [DirectSum.Decomposition 𝓝] (f : N →ₗ[R] M) (hmem : ∀ i x, x ∈ 𝓝 i ↔ f x ∈ ℳ i)
    (i : ι) (x : N) :
    f (DirectSum.decompose 𝓝 x i : N) =
      (DirectSum.decompose ℳ (f x) i : M) :=
  DirectSum.map_decompose_shift 𝓝 ℳ f.toAddMonoidHom id Function.injective_id
    (fun i x hx ↦ (hmem i x).mp hx) i x

-- The inverse congruence is definitionally the direct sum of the componentwise inverses; this
-- helper exposes that computation through the `DirectSum.lmap` API.
private theorem DirectSum.congrLinearEquiv_symm_apply {R ι : Type*} {N P : ι → Type*}
    [Semiring R] [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)]
    [∀ i, AddCommMonoid (P i)] [∀ i, Module R (P i)]
    (e : ∀ i, N i ≃ₗ[R] P i) (x : ⨁ i, P i) :
    (DirectSum.congrLinearEquiv e).symm x =
      DirectSum.lmap (fun i ↦ (e i).symm.toLinearMap) x := by
  rfl

-- Mathlib defines `DirectSum.IsInternal A` as bijectivity of the canonical map
-- `DirectSum.coeAddMonoidHom A`; for a family of submodules that canonical map is
-- `DirectSum.coeLinearMap A` (the same function packaged as a `LinearMap`).  Mathlib states no
-- iff lemma for this module-level form, so the equivalence below is a definitional unfolding,
-- the same one Mathlib's own API relies on (e.g. `IsInternal.ofBijective_coeLinearMap_same`).
-- The helper is private and single-purpose, so a Mathlib refactor of either definition will
-- surface exactly here.
private theorem DirectSum.isInternal_iff_bijective_coeLinearMap {R ι M : Type*}
    [Semiring R] [DecidableEq ι] [AddCommMonoid M] [Module R M]
    {A : ι → Submodule R M} :
    DirectSum.IsInternal A ↔ Function.Bijective (DirectSum.coeLinearMap A) :=
  Iff.rfl

/-- The canonical inclusions of a family of submodules form an internal direct sum when they are
identified with the summands of an equivalence. -/
theorem DirectSum.isInternal_of_lof {R ι M : Type*} [Semiring R] [DecidableEq ι]
    [AddCommMonoid M] [Module R M] {A : ι → Submodule R M} {N : ι → Type*}
    [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)] (e : ∀ i, N i ≃ₗ[R] A i)
    (E : (⨁ i, N i) ≃ₗ[R] M)
    (hE : ∀ i (x : N i), E (DirectSum.lof R ι (fun i ↦ N i) i x) = (e i x : M)) :
    DirectSum.IsInternal A := by
  let F : (⨁ i, A i) ≃ₗ[R] M :=
    (DirectSum.congrLinearEquiv e).symm.trans E
  have hF : ∀ i (x : A i), F (DirectSum.lof R ι (fun i ↦ A i) i x) = (x : M) := by
    intro i x
    simp only [F, LinearEquiv.trans_apply]
    rw [DirectSum.congrLinearEquiv_symm_apply, DirectSum.lmap_lof]
    simpa using hE i ((e i).symm x)
  have hcoe : DirectSum.coeLinearMap A = F.toLinearMap := by
    apply DirectSum.linearMap_ext R
    intro i
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, DirectSum.coeLinearMap_lof]
    exact (hF i x).symm
  rw [DirectSum.isInternal_iff_bijective_coeLinearMap, hcoe]
  exact F.bijective

/-- When all pieces of a direct-sum decomposition of submodules outside degree `i` vanish, every
element lies in the degree-`i` piece. -/
theorem DirectSum.mem_of_forall_ne_eq_bot {R M ι : Type*} [Semiring R] [AddCommMonoid M]
    [Module R M] [DecidableEq ι] {ℳ : ι → Submodule R M} [_root_.DirectSum.Decomposition ℳ]
    {i : ι} (h : ∀ j, j ≠ i → ℳ j = ⊥) (x : M) : x ∈ ℳ i := by
  have htop : ⊤ ≤ ℳ i := by
    rw [← (_root_.DirectSum.Decomposition.isInternal ℳ).submodule_iSup_eq_top]
    refine iSup_le fun j ↦ ?_
    by_cases hj : j = i
    · exact hj ▸ le_rfl
    · rw [h j hj]
      exact bot_le
  exact htop Submodule.mem_top

end TauCeti

namespace LinearMap

/-- Two linear maps out of `P → M` agree if they agree on the homogeneous single-coordinate
functions `Pi.single x α`, with `α` in a piece `ℳ q` of a decomposition of `M`. -/
theorem pi_ext_of_decomposition {R ι M N P : Type*} [Semiring R] [AddCommMonoid M]
    [Module R M] [AddCommMonoid N] [Module R N] [Finite P] [DecidableEq P] [DecidableEq ι]
    (ℳ : ι → Submodule R M) [DirectSum.Decomposition ℳ] {φ ψ : (P → M) →ₗ[R] N}
    (h : ∀ (x : P) {q : ι} {α : M}, α ∈ ℳ q → φ (Pi.single x α) = ψ (Pi.single x α)) :
    φ = ψ := by
  refine pi_ext' fun x ↦ ?_
  refine DirectSum.decompose_lhom_ext ℳ fun i ↦ ?_
  refine ext fun α ↦ ?_
  simpa using h x α.property

end LinearMap

namespace Finsupp

/-- Two additive maps out of `α →₀ M` agree if they agree on `Finsupp.single x c` for every `x`
and every `c` in a piece `ℳ i` of a decomposition of `M`. -/
theorem addHom_ext_of_decomposition {ι α M N σ : Type*} [DecidableEq ι] [AddCommMonoid M]
    [SetLike σ M] [AddSubmonoidClass σ M] (ℳ : ι → σ) [DirectSum.Decomposition ℳ]
    [AddZeroClass N] {φ ψ : (α →₀ M) →+ N}
    (h : ∀ x i (c : M), c ∈ ℳ i → φ (single x c) = ψ (single x c)) : φ = ψ :=
  addHom_ext fun x c ↦ by
    induction c using DirectSum.Decomposition.inductionOn ℳ with
    | zero => simp
    | @homogeneous i c => exact h x i c c.property
    | add c c' hc hc' => rw [single_add, map_add, map_add, hc, hc']

end Finsupp

namespace DirectSum.IsInternal

/-- The recomposition map of the fiberwise collection of an internal decomposition is injective. -/
private theorem injective_coeLinearMap_iSup_fiber {R M ι κ : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M] [DecidableEq ι] [DecidableEq κ] {P : ι → Submodule R M}
    (hP : IsInternal P) (degree : ι → κ) :
    Function.Injective (coeLinearMap fun j ↦ ⨆ i, ⨆ _ : degree i = j, P i) := by
  -- Projection onto each fiber recovers that component of the recomposed direct sum.
  let Q : κ → Submodule R M := fun j ↦ ⨆ i, ⨆ _ : degree i = j, P i
  let _ : Decomposition P := hP.chooseDecomposition
  let projection (j : κ) : M →ₗ[R] M :=
    (toModule R ι M fun i ↦
      if degree i = j then (P i).subtype else 0) ∘ₗ
        (decomposeLinearEquiv P).toLinearMap
  have projection_piece (j : κ) (i : ι) (x : P i) :
      projection j x = if degree i = j then (x : M) else 0 := by
    simp only [projection, LinearMap.comp_apply, LinearEquiv.coe_coe,
      decomposeLinearEquiv_apply_coe, toModule_lof]
    split <;> simp
  have projection_mem (j k : κ) {x : M} (hx : x ∈ Q k) :
      projection j x = if k = j then x else 0 := by
    dsimp only [Q] at hx
    rw [iSup_subtype'] at hx
    refine Submodule.iSup_induction (fun i : {i // degree i = k} ↦ P i)
      (motive := fun y ↦ projection j y = if k = j then y else 0) hx
      (fun i x hx ↦ ?_) (by simp) (fun x y ihx ihy ↦ ?_)
    · simpa only [i.property] using projection_piece j i ⟨x, hx⟩
    · simp only [map_add, ihx, ihy, ite_add_zero]
  have projection_coe (j : κ) (z : ⨁ k, ↥(Q k)) :
      projection j (coeLinearMap Q z) = z j := by
    induction z using DirectSum.induction_on with
    | zero => simp
    | of k x =>
        rw [coeLinearMap_of, projection_mem j k x.property]
        simp only [coe_of_apply]
        split <;> simp
    | add x y ihx ihy =>
        rw [map_add (coeLinearMap Q), map_add (projection j), ihx, ihy]
        rw [add_apply, Submodule.coe_add]
  intro x y hxy
  apply ext fun j ↦ Subtype.ext ?_
  exact (projection_coe j x).symm.trans ((congrArg (projection j) hxy).trans
    (projection_coe j y))

/-- Collecting an internal decomposition along the fibers of any map again gives an internal
decomposition. Each new summand is the sum of the original summands over the corresponding fiber. -/
theorem iSup_fiber {R M ι κ : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    [DecidableEq ι] [DecidableEq κ] {P : ι → Submodule R M}
    (hP : IsInternal P) (degree : ι → κ) :
    IsInternal fun j ↦ ⨆ i, ⨆ _ : degree i = j, P i := by
  -- For submodules, the additive recomposition map in `IsInternal` is the underlying function
  -- of the canonical linear recomposition map.
  change Function.Bijective (coeLinearMap fun j ↦ ⨆ i, ⨆ _ : degree i = j, P i)
  refine ⟨injective_coeLinearMap_iSup_fiber hP degree, ?_⟩
  rw [← LinearMap.range_eq_top, range_coeLinearMap, iSup_comm]
  simpa only [iSup_iSup_eq_right] using hP.submodule_iSup_eq_top

/-- An internal direct sum of submodules can be reindexed along an equivalence of the index
types. -/
theorem comp_equiv {R M κ κ' : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    [DecidableEq κ] [DecidableEq κ'] {A : κ' → Submodule R M} (hA : IsInternal A)
    (e : κ ≃ κ') : IsInternal (A ∘ e) := by
  convert hA.iSup_fiber e.symm with k
  simp [Equiv.symm_apply_eq]

/-- Transporting an internal direct sum of submodules along a linear equivalence gives an internal
direct sum. -/
theorem map_linearEquiv {R M N ι : Type*} [Semiring R] [AddCommMonoid M]
    [AddCommMonoid N] [Module R M] [Module R N] [DecidableEq ι] {A : ι → Submodule R M}
    (h : IsInternal A) (e : M ≃ₗ[R] N) :
    IsInternal fun i => (A i).map e.toLinearMap := by
  -- For submodules, the additive recomposition map in `IsInternal` is the underlying function
  -- of the canonical linear recomposition map.
  have hA : Function.Bijective (coeLinearMap A) := h
  refine TauCeti.DirectSum.isInternal_of_lof
    (e := fun i => (A i).equivMapOfInjective e.toLinearMap e.injective)
    (E := (LinearEquiv.ofBijective (coeLinearMap A) hA).trans e) fun i x => ?_
  simp [coeLinearMap_lof]

/-- Prepending the zero submodule to a natural-number-indexed internal decomposition
again gives an internal decomposition. -/
theorem nat_cons_bot {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    {N : ℕ → Submodule R M} (h : IsInternal N) :
    IsInternal (fun | 0 => ⊥ | i + 1 => N i) := by
  have hfamily : (fun j ↦ ⨆ i, ⨆ _ : Nat.succ i = j, N i) =
      (fun | 0 => ⊥ | i + 1 => N i) := by
    funext j
    cases j <;> simp
  rw [← hfamily]
  exact h.iSup_fiber Nat.succ

/-- **Restricting an internal decomposition to a component-stable subspace.** If a subspace
contains every canonical component of each of its elements, then it is the internal sum of its
intersections with the original summands. -/
theorem iSup_inf_eq_of_component_mem
    {S V κ : Type*} [Semiring S] [AddCommMonoid V] [Module S V] [DecidableEq κ]
    {A : κ → Submodule S V} (h : IsInternal A) (p : Submodule S V)
    (hp : ∀ (m : V), m ∈ p → ∀ i,
      (((LinearEquiv.ofBijective (coeLinearMap A) h).symm m i : A i) : V) ∈ p) :
    ⨆ i, p ⊓ A i = p := by
  classical
  refine le_antisymm (iSup_le fun _ ↦ inf_le_left) fun m hm ↦ ?_
  let e := LinearEquiv.ofBijective (coeLinearMap A) h
  have hsum : m = ∑ i ∈ (e.symm m).support, ((e.symm m i : A i) : V) := by
    conv_lhs => rw [← e.apply_symm_apply m, ← sum_support_of (e.symm m)]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ ↦ coeLinearMap_of A i (e.symm m i)
  rw [hsum]
  exact Submodule.sum_mem _ fun i _ ↦
    Submodule.mem_iSup_of_mem i ⟨hp m hm i, (e.symm m i).property⟩

/-- **Finite sums in an internal direct sum are compared termwise.** If two sums over the same
`Finset` `s`, each taking its `i`-th term from the `i`-th summand, are equal, then their terms are
equal at every index in `s`. -/
theorem eq_of_finsetSum_eq {ι M σ : Type*} [DecidableEq ι] [AddCommMonoid M] [SetLike σ M]
    [AddSubmonoidClass σ M] {A : ι → σ} (h : IsInternal A) {s : Finset ι} {v w : ι → M}
    (hv : ∀ i ∈ s, v i ∈ A i) (hw : ∀ i ∈ s, w i ∈ A i)
    (hvw : ∑ i ∈ s, v i = ∑ i ∈ s, w i) {i : ι} (hi : i ∈ s) : v i = w i := by
  let _ : Decomposition A := h.chooseDecomposition
  -- the `i`-th component of such a sum is its `i`-th term
  have component {u : ι → M} (hu : ∀ j ∈ s, u j ∈ A j) :
      (decompose A (∑ j ∈ s, u j) i : M) = u i := by
    rw [decompose_sum, DirectSum.sum_apply, AddSubmonoidClass.coe_finsetSum,
      Finset.sum_eq_single_of_mem i hi fun j hj hji ↦ decompose_of_mem_ne A (hu j hj) hji,
      decompose_of_mem_same A (hu i hi)]
  rw [← component hv, hvw, component hw]

end DirectSum.IsInternal

namespace DirectSum

variable {ι A M σA σM : Type*} [DecidableEq ι] [Add ι] [IsRightCancelAdd ι]
  [Semiring A] [AddCommMonoid M] [Module A M]
  [SetLike σA A] [AddSubmonoidClass σA A] (𝒜 : ι → σA) [Decomposition 𝒜]
  [SetLike σM M] [AddSubmonoidClass σM M] (ℳ : ι → σM) [Decomposition ℳ]
  [SetLike.GradedSMul 𝒜 ℳ]

/-- For compatible decompositions of a semiring and its module, the degree-`i + j` component of
`a • x`, for `x` homogeneous of degree `j`, is the degree-`i` component of `a` acting on `x`.
Only right cancellation of addition on the degrees is needed. This is the module analogue of
Mathlib's `DirectSum.coe_decompose_mul_add_of_right_mem`. -/
theorem coe_decompose_smul_add_of_right_mem {a : A} {x : M} {i j : ι} (hx : x ∈ ℳ j) :
    (decompose ℳ (a • x) (i + j) : M) = (decompose 𝒜 a i : A) • x := by
  induction a using Decomposition.inductionOn 𝒜 with
  | zero => simp
  | @homogeneous k a =>
    have hmem : (a : A) • x ∈ ℳ (k + j) := SetLike.GradedSMul.smul_mem a.property hx
    by_cases hki : k = i
    · subst k
      rw [decompose_of_mem_same ℳ hmem, decompose_of_mem_same 𝒜 a.property]
    · rw [decompose_of_mem_ne ℳ hmem (fun h ↦ hki (add_right_cancel h)),
        decompose_of_mem_ne 𝒜 a.property hki, zero_smul]
  | add a b ha hb => simp [add_smul, ha, hb]

end DirectSum

namespace DirectSum

section Support

variable {ι M σ : Type*} [DecidableEq ι] [AddCommMonoid M] [SetLike σ M] [AddSubmonoidClass σ M]
  (ℳ : ι → σ) [Decomposition ℳ] [∀ (i : ι) (x : ℳ i), Decidable (x ≠ 0)]

/-- The homogeneous support of `x` in an internal direct sum is nonempty if and only if `x ≠ 0`. -/
theorem support_decompose_nonempty_iff {x : M} :
    (decompose ℳ x).support.Nonempty ↔ x ≠ 0 := by
  rw [← Finset.ne_empty_iff_nonempty, not_iff_not, DFinsupp.support_eq_empty]
  exact (decomposeAddEquiv ℳ).map_eq_zero_iff

/-- A degree `i` lies in the homogeneous support of `x` if and only if the `i`-th homogeneous
component `(decompose ℳ x i : M)` is nonzero. -/
theorem mem_support_decompose_iff {x : M} {i : ι} :
    i ∈ (decompose ℳ x).support ↔ (decompose ℳ x i : M) ≠ 0 := by
  rw [DFinsupp.mem_support_iff, Ne, ← Subtype.coe_inj, ZeroMemClass.coe_zero]

end Support

section AddCommGroup

variable {ι M σ : Type*} [DecidableEq ι] [AddCommGroup M] [SetLike σ M] [AddSubmonoidClass σ M]

/-- In an additive commutative group decomposed into additive submonoids (for instance submodules
over a semiring), homogeneous projections commute with negation. -/
theorem coe_decompose_neg (ℳ : ι → σ) [Decomposition ℳ] (x : M) (i : ι) :
    (decompose ℳ (-x) i : M) = -(decompose ℳ x i : M) :=
  eq_neg_of_add_eq_zero_left <| by
    rw [← AddMemClass.coe_add, ← DirectSum.add_apply, ← decompose_add, neg_add_cancel,
      decompose_zero, DirectSum.zero_apply, ZeroMemClass.coe_zero]

/-- Each summand of a `DirectSum.Decomposition` of an additive commutative group is closed under
negation, even when the summand type carries only `AddSubmonoidClass` (such as `Submodule R M`
over a semiring `R`). -/
theorem Decomposition.neg_mem {ℳ : ι → σ} [Decomposition ℳ] {i : ι} {x : M} (hx : x ∈ ℳ i) :
    -x ∈ ℳ i := by
  rw [← decompose_of_mem_same ℳ hx, ← coe_decompose_neg]
  exact (decompose ℳ (-x) i).property

/-- Each summand of a `DirectSum.Decomposition` of an additive commutative group is closed under
subtraction. -/
theorem Decomposition.sub_mem {ℳ : ι → σ} [Decomposition ℳ] {i : ι} {x y : M}
    (hx : x ∈ ℳ i) (hy : y ∈ ℳ i) : x - y ∈ ℳ i := by
  rw [sub_eq_add_neg]
  exact add_mem hx (Decomposition.neg_mem hy)

/-- Each summand of a `DirectSum.Decomposition` of an additive commutative group is closed under
integer scalar multiplication. -/
theorem Decomposition.zsmul_mem {ℳ : ι → σ} [Decomposition ℳ] {i : ι} {x : M}
    (hx : x ∈ ℳ i) (n : ℤ) : n • x ∈ ℳ i := by
  cases n with
  | ofNat k => simpa only [Int.ofNat_eq_natCast, natCast_zsmul] using nsmul_mem hx k
  | negSucc k => simpa only [negSucc_zsmul] using Decomposition.neg_mem (nsmul_mem hx (k + 1))

end AddCommGroup

section Module

variable {ι : Type*} (R : Type*) (M : ι → Type*) [DecidableEq ι] [Semiring R]
  [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

/-- The `i`-th summand of the external direct sum `⨁ i, M i`: the image of `M i` under the
inclusion `DirectSum.lof R ι M i`. -/
def summand (i : ι) : Submodule R (⨁ i, M i) :=
  LinearMap.range (lof R ι M i)

/-- The `i`-th summand is the range of the inclusion `DirectSum.lof R ι M i`. -/
theorem summand_def (i : ι) : summand R M i = LinearMap.range (lof R ι M i) :=
  (rfl)

variable {R M}

/-- An element of `⨁ i, M i` lies in the `i`-th summand exactly when it is `DirectSum.of M i m`
for some `m : M i`. -/
theorem mem_summand {i : ι} {x : ⨁ i, M i} :
    x ∈ summand R M i ↔ ∃ m : M i, of M i m = x := by
  simp [summand, lof_eq_of]

/-- The element `DirectSum.lof R ι M i m` lies in the `i`-th summand. -/
theorem lof_mem_summand (i : ι) (m : M i) : lof R ι M i m ∈ summand R M i :=
  LinearMap.mem_range_self _ m

/-- The element `DirectSum.of M i m` lies in the `i`-th summand. -/
theorem of_mem_summand (i : ι) (m : M i) : of M i m ∈ summand R M i :=
  mem_summand.mpr ⟨m, rfl⟩

/-- The summands of the external direct sum form an internal direct sum: they are the ranges of
the inclusions `DirectSum.lof R ι M i`. -/
theorem isInternal_summand : IsInternal (summand R M) :=
  TauCeti.DirectSum.isInternal_of_lof
    (e := fun i ↦ LinearEquiv.ofInjective (lof R ι M i) (of_injective i))
    (E := LinearEquiv.refl R _) fun _ _ ↦ rfl

/-- The external direct sum decomposes as the direct sum of its summands. -/
noncomputable instance instDecompositionSummand : Decomposition (summand R M) :=
  isInternal_summand.chooseDecomposition

/-- The `i`-th component of an element `x` of `⨁ i, M i` for the summand decomposition is the
summand `x i`. -/
@[simp]
theorem coe_decompose_summand (x : ⨁ i, M i) (i : ι) :
    (decompose (summand R M) x i : ⨁ i, M i) = of M i (x i) := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of j m =>
    rw [decompose_of_mem (summand R M) (of_mem_summand j m)]
    by_cases h : j = i
    · subst h
      simp
    · simp [of_eq_of_ne _ _ _ (Ne.symm h)]
  | add x y hx hy => simp [hx, hy]

end Module

end DirectSum

/-- **A basis split along the fibers of a map gives an internal direct sum**: if `b` is a basis of
`M` and `w : ι → κ` is any map of the index type, then the spans of the basis vectors in the fibers
of `w` form an internal direct sum decomposition of `M`. -/
theorem Module.Basis.isInternal_span_image_fiber {R ι κ M : Type*} [Semiring R] [AddCommMonoid M]
    [Module R M] [DecidableEq κ] (b : Module.Basis ι R M) (w : ι → κ) :
    DirectSum.IsInternal fun c : κ => Submodule.span R (b '' {i | w i = c}) := by
  let A : κ → Submodule R M := fun c => Submodule.span R (b '' {i | w i = c})
  have hsupp : ∀ c (a : M), a ∈ A c → ∀ i, w i ≠ c → b.repr a i = 0 := fun c a ha i hi => by
    by_contra h
    exact hi ((Module.Basis.mem_span_image b).1 ha (Finsupp.mem_support_iff.2 h))
  have key : ∀ (x : ⨁ c, A c) (c : κ) (i : ι), w i = c →
      b.repr (DirectSum.coeLinearMap A x) i = b.repr (x c : M) i := by
    intro x c i hi
    induction x using DirectSum.induction_on with
    | zero => simp
    | of c' a =>
      rw [DirectSum.coeLinearMap_of]
      by_cases h : c' = c
      · subst h; simp
      · rw [DirectSum.of_eq_of_ne _ _ _ (Ne.symm h), hsupp c' a a.property i fun e => h
          (e.symm.trans hi)]
        simp
    | add x y hx hy => simp [hx, hy]
  -- For submodules, the additive recomposition map in `IsInternal` is the underlying function
  -- of the canonical linear recomposition map.
  change Function.Bijective (DirectSum.coeLinearMap A)
  refine ⟨fun x y hxy => ?_, ?_⟩
  · refine DirectSum.ext fun c => Subtype.ext (b.repr.injective (Finsupp.ext fun i => ?_))
    by_cases hi : w i = c
    · rw [← key x c i hi, ← key y c i hi, hxy]
    · rw [hsupp c _ (x c).property i hi, hsupp c _ (y c).property i hi]
  · rw [← LinearMap.range_eq_top, eq_top_iff, ← b.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨DirectSum.of (fun c => A c) (w i) ⟨b i, Submodule.subset_span ⟨i, rfl, rfl⟩⟩, by simp⟩

/-- The basis vectors of `b` in the fiber of `w : ι → κ` over `c`, as a basis of their span. -/
noncomputable def Module.Basis.spanImageFiber {R ι κ M : Type*} [Semiring R] [AddCommMonoid M]
    [Module R M] (b : Module.Basis ι R M) (w : ι → κ) (c : κ) :
    Module.Basis {i // w i = c} R (Submodule.span R (b '' {i | w i = c})) :=
  (Module.Basis.span (b.linearIndependent.comp _ Subtype.val_injective)).map
    (LinearEquiv.ofEq _ _ (by rw [Set.range_comp, Subtype.range_coe_subtype]))

/-- The vectors of `Module.Basis.spanImageFiber` are the basis vectors of `b`. -/
@[simp]
theorem Module.Basis.spanImageFiber_apply {R ι κ M : Type*} [Semiring R] [AddCommMonoid M]
    [Module R M] (b : Module.Basis ι R M) (w : ι → κ) (c : κ) (i : {i // w i = c}) :
    (b.spanImageFiber w c i : M) = b i := by
  simp [Module.Basis.spanImageFiber, Module.Basis.span_apply]

/-- If a supremum-independent family of submodules `A` over a ring has supremum `S`, then its
traces `(A i).comap S.subtype` on `S` form an internal direct sum of `S` (the ring hypothesis is
required by `DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top`). -/
theorem DirectSum.isInternal_submodule_comap_subtype {R ι M : Type*} [Ring R] [AddCommGroup M]
    [Module R M] [DecidableEq ι] {A : ι → Submodule R M} {S : Submodule R M}
    (hind : iSupIndep A) (hsup : ⨆ i, A i = S) :
    DirectSum.IsInternal fun i ↦ (A i).comap S.subtype := by
  refine DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind.comap_subtype ?_
  have hS : S = ⨆ i ∈ (Set.univ : Set ι), A i := by simp [← hsup]
  subst hS
  simpa using Submodule.biSup_comap_subtype_eq_top Set.univ A

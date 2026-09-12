/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.RingTheory.Finiteness.Basic
import TauCeti.Order.CompactlyGenerated

/-!
# Internal direct sums from explicit equivalences

This file provides reusable infrastructure for direct sums of submodules.  The generic
`DirectSum.piInclusion`, `DirectSum.piSubmodule`, and `DirectSum.piSubmoduleEquiv` declarations
describe their componentwise inclusion and range, while `DirectSum.isInternal_of_lof` gives a
criterion for proving that a family of submodules is an internal direct sum by identifying its
summands with the components of a linear equivalence.

A second group of declarations restricts a decomposition along a linear map.
`DirectSum.map_decompose_shift` says that a map carrying each summand of one decomposition into a
summand of another, along an injective reindexing of the degrees, commutes with the homogeneous
projections, while `DirectSum.isInternal_comap` and
`DirectSum.Decomposition.restrict` transport a decomposition backwards along an injective linear
map whose range contains the homogeneous projections of its elements, with
`DirectSum.map_decompose_restrict` computing the projections of the restricted decomposition.

The file also specializes the compactness bound
`TauCeti.finite_ne_bot_of_iSupIndep_of_isCompactElement` to submodules,
`TauCeti.Submodule.finite_ne_bot_of_iSupIndep_of_fg`.
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
  LinearMap.range (TauCeti.DirectSum.piInclusion N)

/-- The componentwise formula for the inclusion of a direct sum of submodules. -/
@[simp]
theorem DirectSum.piInclusion_apply {R ι : Type*} {M : ι → Type*} [Semiring R]
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] (N : ∀ i, Submodule R (M i))
    (x : ⨁ i, N i) (i : ι) :
    TauCeti.DirectSum.piInclusion N x i = (x i : M i) := by
  rw [TauCeti.DirectSum.piInclusion, DirectSum.lmap_apply, Submodule.coe_subtype]

/-- The inclusion of a generator of a direct sum of submodules. -/
@[simp]
theorem DirectSum.piInclusion_lof {R ι : Type*} {M : ι → Type*} [Semiring R]
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] (N : ∀ i, Submodule R (M i)) (i : ι)
    (x : N i)
    [DecidableEq ι] :
    TauCeti.DirectSum.piInclusion N
        (DirectSum.lof R ι (fun i ↦ N i) i x) = DirectSum.lof R ι (fun i ↦ M i) i x := by
  rw [TauCeti.DirectSum.piInclusion, DirectSum.lmap_lof, Submodule.coe_subtype]

private theorem DirectSum.piInclusion_injective {R ι : Type*} {M : ι → Type*} [Semiring R]
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] (N : ∀ i, Submodule R (M i)) :
    Function.Injective (TauCeti.DirectSum.piInclusion N) := by
  rw [TauCeti.DirectSum.piInclusion]
  refine (DirectSum.lmap_injective fun i ↦ (N i).subtype).mpr fun i ↦ ?_
  exact (N i).injective_subtype

/-- The linear equivalence from the direct sum of submodules to `piSubmodule N`. -/
noncomputable def DirectSum.piSubmoduleEquiv {R ι : Type*} {M : ι → Type*} [Semiring R]
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] (N : ∀ i, Submodule R (M i)) :
    (⨁ i, N i) ≃ₗ[R] TauCeti.DirectSum.piSubmodule N :=
  LinearEquiv.ofInjective (TauCeti.DirectSum.piInclusion N)
    (TauCeti.DirectSum.piInclusion_injective N)

/-- The underlying map of `piSubmoduleEquiv` is the canonical inclusion. -/
@[simp]
theorem DirectSum.piSubmoduleEquiv_apply {R ι : Type*} {M : ι → Type*} [Semiring R]
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] (N : ∀ i, Submodule R (M i))
    (x : ⨁ i, N i) :
    ((TauCeti.DirectSum.piSubmoduleEquiv N x : TauCeti.DirectSum.piSubmodule N) :
      ⨁ i, M i) = TauCeti.DirectSum.piInclusion N x := by
  rw [TauCeti.DirectSum.piSubmoduleEquiv]
  exact LinearEquiv.ofInjective_apply _ x

/-- The inverse of `piSubmoduleEquiv` has the expected componentwise values. -/
@[simp]
theorem DirectSum.piSubmoduleEquiv_symm_apply {R ι : Type*} {M : ι → Type*} [Semiring R]
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] (N : ∀ i, Submodule R (M i))
    (y : TauCeti.DirectSum.piSubmodule N) (i : ι) :
    ((TauCeti.DirectSum.piSubmoduleEquiv N).symm y i : M i) = (y : ⨁ i, M i) i := by
  have h := TauCeti.DirectSum.piSubmoduleEquiv_apply N
    ((TauCeti.DirectSum.piSubmoduleEquiv N).symm y)
  rw [LinearEquiv.apply_symm_apply] at h
  have hi := congrArg (fun z : ⨁ i, M i ↦ z i) h
  simpa only [TauCeti.DirectSum.piInclusion_apply] using hi.symm

/-- Membership in the direct sum of a family of submodules is componentwise. -/
@[simp]
theorem DirectSum.mem_piSubmodule_iff {R ι : Type*} {M : ι → Type*} [Semiring R]
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] (N : ∀ i, Submodule R (M i))
    (x : ⨁ i, M i) :
    x ∈ TauCeti.DirectSum.piSubmodule N ↔ ∀ i, x i ∈ N i := by
  rw [TauCeti.DirectSum.piSubmodule, TauCeti.DirectSum.piInclusion, DirectSum.range_lmap]
  simp [Submodule.mem_comap, DirectSum.coeFnLinearMap_apply, Submodule.mem_pi]

/-- An included summand belongs to the direct sum of a family of submodules. -/
theorem DirectSum.lof_mem_piSubmodule {R ι : Type*} {M : ι → Type*} [Semiring R]
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] (N : ∀ i, Submodule R (M i)) (i : ι)
    (x : N i)
    [DecidableEq ι] :
    DirectSum.lof R ι M i x ∈ TauCeti.DirectSum.piSubmodule N := by
  refine ⟨DirectSum.lof R ι (fun i ↦ N i) i x, ?_⟩
  exact TauCeti.DirectSum.piInclusion_lof N i x

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
    (f.comp (𝓝 i).subtype).codRestrict (ℳ i) fun x ↦ (hmem i x).mp x.2
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

/-- A linear map which carries the degree-`i` summand of one internal decomposition into the
degree-`σ i` summand of another, along an injective reindexing `σ` of the degrees, commutes with
the homogeneous projections. -/
theorem DirectSum.map_decompose_shift {R ι κ M N : Type*} [Semiring R]
    [DecidableEq ι] [DecidableEq κ] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    (ℳ : ι → Submodule R M) [DirectSum.Decomposition ℳ] (𝓝 : κ → Submodule R N)
    [DirectSum.Decomposition 𝓝] (f : M →ₗ[R] N) (σ : ι → κ) (hσ : Function.Injective σ)
    (hf : ∀ (i : ι) (x : M), x ∈ ℳ i → f x ∈ 𝓝 (σ i)) (i : ι) (x : M) :
    f (DirectSum.decompose ℳ x i : M) = (DirectSum.decompose 𝓝 (f x) (σ i) : N) := by
  induction x using DirectSum.Decomposition.inductionOn ℳ with
  | zero => simp
  | @homogeneous j x =>
    have hxM : (x : M) ∈ ℳ j := x.2
    have hxN : f (x : M) ∈ 𝓝 (σ j) := hf j x hxM
    by_cases hij : i = j
    · subst hij
      rw [DirectSum.decompose_of_mem_same ℳ hxM, DirectSum.decompose_of_mem_same 𝓝 hxN]
    · rw [DirectSum.decompose_of_mem_ne ℳ hxM (Ne.symm hij), map_zero,
        DirectSum.decompose_of_mem_ne 𝓝 hxN fun hc ↦ Ne.symm hij (hσ hc)]
  | add x y hx hy => simp [hx, hy]

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
  DirectSum.map_decompose_shift 𝓝 ℳ f id Function.injective_id
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

-- The decomposition is spelled as `iSupIndep A` together with a finiteness hypothesis on
-- `⨆ i, A i` rather than as `DirectSum.IsInternal`, which carries a `DecidableEq` hypothesis on
-- the index type that the proof does not need.  Over a semiring an internal decomposition supplies
-- the two hypotheses through `DirectSum.IsInternal.submodule_iSupIndep` and
-- `DirectSum.IsInternal.submodule_iSup_eq_top`; the converse implication, and with it
-- `DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top`, needs `[Ring R]` and
-- `[AddCommGroup M]`.
private theorem Submodule.finite_ne_bot_of_iSupIndep_of_fg_aux
    {R ι M : Type*} [Semiring R] [AddCommMonoid M]
    [Module R M] {A : ι → Submodule R M} (hAi : iSupIndep A) (hAf : (⨆ i, A i).FG) :
    {i | A i ≠ ⊥}.Finite :=
  finite_ne_bot_of_iSupIndep_of_isCompactElement hAi ((Submodule.fg_iff_compact _).mp hAf)

/-- An independent family of submodules spanning a finitely generated submodule has only finitely
many nonzero members. -/
theorem Submodule.finite_ne_bot_of_iSupIndep_of_fg {R ι M : Type*} [Semiring R] [AddCommMonoid M]
    [Module R M] {A : ι → Submodule R M} (hAi : iSupIndep A) (hAf : (⨆ i, A i).FG) :
    {i | A i ≠ ⊥}.Finite :=
  Submodule.finite_ne_bot_of_iSupIndep_of_fg_aux hAi hAf

end TauCeti

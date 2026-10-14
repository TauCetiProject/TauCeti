/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.Algebra.GradedMulAction
public import Mathlib.RingTheory.Finiteness.Basic
import TauCeti.Order.CompactlyGenerated

/-!
# Internal direct sums from explicit equivalences

This file provides reusable infrastructure for direct sums of submodules.  The generic
`DirectSum.piInclusion`, `DirectSum.piSubmodule`, and `DirectSum.piSubmoduleEquiv` declarations
describe their componentwise inclusion and range, while `DirectSum.isInternal_of_lof` gives a
criterion for proving that a family of submodules is an internal direct sum by identifying its
summands with the components of a linear equivalence.

A second group of declarations concerns maps between decompositions.
`DirectSum.map_decompose_shift` says that an additive map carrying each summand of one
decomposition into a summand of another, along an injective reindexing of the degrees, commutes
with the homogeneous projections, while `DirectSum.isInternal_comap` and
`DirectSum.Decomposition.restrict` transport a decomposition backwards along an injective linear
map whose range contains the homogeneous projections of its elements, with
`DirectSum.map_decompose_restrict` computing the projections of the restricted decomposition.

A third group is about maps compatible with a decomposition: if a linear map carries each
summand of a spanning family into the corresponding member of an independent family, then its
kernel is spanned by its homogeneous parts, `LinearMap.ker_eq_iSup_inf_of_map_le`. Conversely,
`iSupIndep.map_of_ker_inf_iSup_le` shows that a linear map preserves independence when the
part of its kernel in the span is spanned by its intersections with the summands.

The file also specializes the compactness bound
`TauCeti.finite_ne_bot_of_iSupIndep_of_isCompactElement` to submodules,
`TauCeti.Submodule.finite_ne_bot_of_iSupIndep_of_fg`.

`DirectSum.IsInternal.iSup_fiber` collects an internal decomposition along the fibers of any map.

`DirectSum.IsInternal.iSup_inf_eq_of_component_mem` restricts an internal decomposition to any
submodule that contains the canonical components of each of its elements.

Finally, `DirectSum.coe_decompose_smul_add_of_right_mem` computes the components of a scalar
action on a homogeneous element when the scalar and module decompositions are compatible.
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

end TauCeti

namespace DirectSum

/-- An additive map which carries the degree-`i` summand of one internal decomposition into the
degree-`σ i` summand of another, along an injective reindexing `σ` of the degrees, commutes with
the homogeneous projections. The summands may be any additive subobjects, including submodules
over unrelated scalar semirings. -/
theorem map_decompose_shift {ι κ M N S T : Type*}
    [DecidableEq ι] [DecidableEq κ] [AddCommMonoid M] [AddCommMonoid N]
    [SetLike S M] [AddSubmonoidClass S M] [SetLike T N] [AddSubmonoidClass T N]
    (ℳ : ι → S) [DirectSum.Decomposition ℳ] (𝓝 : κ → T)
    [DirectSum.Decomposition 𝓝] (f : M →+ N) (σ : ι → κ) (hσ : Function.Injective σ)
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

/-- **The kernel of a map compatible with a decomposition is spanned by its homogeneous parts.**
If the submodules `A i` span the source, the submodules `A' i` are independent, and `g` carries
`A i` into `A' i`, then the kernel of `g` is the supremum of its intersections with the `A i`.

The hypothesis on the source is only that its family spans; independence there is not used, and
an internal direct sum supplies it through `DirectSum.IsInternal.submodule_iSup_eq_top`. -/
theorem _root_.LinearMap.ker_eq_iSup_inf_of_map_le {R ι M N : Type*} [Ring R] [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] (g : M →ₗ[R] N) {A : ι → Submodule R M}
    {A' : ι → Submodule R N} (hA : ⨆ i, A i = ⊤) (hA' : iSupIndep A')
    (hg : ∀ i, (A i).map g ≤ A' i) :
    LinearMap.ker g = ⨆ i, LinearMap.ker g ⊓ A i := by
  classical
  refine le_antisymm (fun x hx ↦ ?_) (iSup_le fun _ ↦ inf_le_left)
  obtain ⟨c, hc, rfl⟩ :=
    (Submodule.mem_iSup_iff_exists_finsupp A x).1 (hA ▸ Submodule.mem_top)
  have hsum : ∑ i ∈ c.support, g (c i) = 0 := by
    rw [← map_sum]
    simpa [Finsupp.sum] using hx
  have hzero := (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero A').1 hA' c.support
    (fun i ↦ g (c i)) (fun i _ ↦ hg i ⟨c i, hc i, rfl⟩) hsum
  simp only [Finsupp.sum]
  exact Submodule.sum_mem _ fun i hi ↦
    Submodule.mem_iSup_of_mem i ⟨LinearMap.mem_ker.2 (hzero i hi), hc i⟩

end TauCeti

/-- A linear map preserves independence of a family of submodules if the part of its kernel
in their span is spanned by its intersections with the family. In particular, a quotient by a
homogeneous submodule preserves independence. -/
theorem iSupIndep.map_of_ker_inf_iSup_le {R ι M N : Type*} [Ring R] [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] {A : ι → Submodule R M}
    (hA : iSupIndep A) (f : M →ₗ[R] N)
    (hker : LinearMap.ker f ⊓ (⨆ i, A i) ≤ ⨆ i, LinearMap.ker f ⊓ A i) :
    iSupIndep fun i ↦ (A i).map f := by
  rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
  classical
  intro s v hv hv0 j hj
  have hall : ∀ i : ι, ∃ y, y ∈ A i ∧ (i ∈ s → f y = v i) ∧ (i ∉ s → y = 0) := by
    intro i
    by_cases hi : i ∈ s
    · obtain ⟨y, hy, hf⟩ := Submodule.mem_map.1 (hv i hi)
      exact ⟨y, hy, fun _ ↦ hf, fun h ↦ absurd hi h⟩
    · exact ⟨0, Submodule.zero_mem _, fun h ↦ absurd h hi, fun _ ↦ rfl⟩
  choose a haA haf ha0 using hall
  have hasum : ∑ i ∈ s, a i ∈ LinearMap.ker f := by
    rw [LinearMap.mem_ker, map_sum]
    exact (Finset.sum_congr rfl fun i hi ↦ haf i hi).trans hv0
  have hasumA : ∑ i ∈ s, a i ∈ ⨆ i, A i :=
    Submodule.sum_mem _ fun i _ ↦ Submodule.mem_iSup_of_mem i (haA i)
  obtain ⟨c, hc, hca⟩ :=
    (Submodule.mem_iSup_iff_exists_finsupp _ _).1 (hker ⟨hasum, hasumA⟩)
  have haj : a j = c j := by
    refine (iSupIndep_iff_finsetSum_eq_imp_eq A).1 hA (s ∪ c.support) a c
      (fun i _ ↦ ⟨haA i, (hc i).2⟩) ?_ j (Finset.mem_union_left _ hj)
    calc
        ∑ i ∈ s ∪ c.support, a i = ∑ i ∈ s, a i := by
          symm
          apply Finset.sum_subset (Finset.subset_union_left)
          intro i _ hi
          exact ha0 i hi
        _ = ∑ i ∈ c.support, c i := hca.symm
        _ = ∑ i ∈ s ∪ c.support, c i := by
          apply Finset.sum_subset (Finset.subset_union_right)
          simp
  rw [← haf j hj, haj]
  exact (hc j).1

namespace DirectSum.IsInternal

/-- Collecting an internal decomposition along the fibers of any map again gives an internal
decomposition. Each new summand is the sum of the original summands over the corresponding fiber. -/
theorem iSup_fiber {R M ι κ : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    [DecidableEq ι] [DecidableEq κ] {P : ι → Submodule R M}
    (hP : DirectSum.IsInternal P) (degree : ι → κ) :
    DirectSum.IsInternal fun j ↦ ⨆ i, ⨆ _ : degree i = j, P i := by
  -- For submodules, the additive recomposition map in `IsInternal` is the underlying function
  -- of the canonical linear recomposition map.
  change Function.Bijective (DirectSum.coeLinearMap fun j ↦ ⨆ i, ⨆ _ : degree i = j, P i)
  refine ⟨?_, ?_⟩
  · -- Projection onto each fiber recovers that component of the recomposed direct sum.
    let Q : κ → Submodule R M := fun j ↦ ⨆ i, ⨆ _ : degree i = j, P i
    let _ : DirectSum.Decomposition P := hP.chooseDecomposition
    let projection (j : κ) : M →ₗ[R] M :=
      (DirectSum.toModule R ι M fun i ↦
        if degree i = j then (P i).subtype else 0) ∘ₗ
          (DirectSum.decomposeLinearEquiv P).toLinearMap
    have projection_piece (j : κ) (i : ι) (x : P i) :
        projection j x = if degree i = j then (x : M) else 0 := by
      simp only [projection, LinearMap.comp_apply, LinearEquiv.coe_coe,
        DirectSum.decomposeLinearEquiv_apply_coe, DirectSum.toModule_lof]
      split <;> rfl
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
        projection j (DirectSum.coeLinearMap Q z) = z j := by
      induction z using DirectSum.induction_on with
      | zero => simp
      | of k x =>
          rw [DirectSum.coeLinearMap_of, projection_mem j k x.property]
          simp only [DirectSum.coe_of_apply]
          split <;> rfl
      | add x y ihx ihy =>
          rw [map_add (DirectSum.coeLinearMap Q), map_add (projection j), ihx, ihy]
          rfl
    intro x y hxy
    apply DirectSum.ext fun j ↦ Subtype.ext ?_
    exact (projection_coe j x).symm.trans ((congrArg (projection j) hxy).trans
      (projection_coe j y))
  · rw [← LinearMap.range_eq_top, DirectSum.range_coeLinearMap, iSup_comm]
    simpa only [iSup_iSup_eq_right] using hP.submodule_iSup_eq_top

/-- **Restricting an internal decomposition to a component-stable subspace.** If a subspace
contains every canonical component of each of its elements, then it is the internal sum of its
intersections with the original summands. -/
theorem iSup_inf_eq_of_component_mem
    {S V κ : Type*} [Semiring S] [AddCommMonoid V] [Module S V] [DecidableEq κ]
    {A : κ → Submodule S V} (h : DirectSum.IsInternal A) (p : Submodule S V)
    (hp : ∀ (m : V), m ∈ p → ∀ i,
      (((LinearEquiv.ofBijective (DirectSum.coeLinearMap A) h).symm m i : A i) : V) ∈ p) :
    ⨆ i, p ⊓ A i = p := by
  classical
  refine le_antisymm (iSup_le fun _ ↦ inf_le_left) fun m hm ↦ ?_
  let e := LinearEquiv.ofBijective (DirectSum.coeLinearMap A) h
  have hsum : m = ∑ i ∈ (e.symm m).support, ((e.symm m i : A i) : V) := by
    conv_lhs => rw [← e.apply_symm_apply m, ← DirectSum.sum_support_of (e.symm m)]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ ↦ DirectSum.coeLinearMap_of A i (e.symm m i)
  rw [hsum]
  exact Submodule.sum_mem _ fun i _ ↦
    Submodule.mem_iSup_of_mem i ⟨hp m hm i, (e.symm m i).2⟩

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
    have hmem : (a : A) • x ∈ ℳ (k + j) := SetLike.GradedSMul.smul_mem a.2 hx
    by_cases hki : k = i
    · subst k
      rw [decompose_of_mem_same ℳ hmem, decompose_of_mem_same 𝒜 a.2]
    · rw [decompose_of_mem_ne ℳ hmem (fun h ↦ hki (add_right_cancel h)),
        decompose_of_mem_ne 𝒜 a.2 hki, zero_smul]
  | add a b ha hb => simp [add_smul, ha, hb]

end DirectSum

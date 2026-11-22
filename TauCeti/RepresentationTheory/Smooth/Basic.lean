/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Group.Quotient
public import TauCeti.RepresentationTheory.Stabilizer
public import TauCeti.RepresentationTheory.Subrepresentation
public import TauCeti.Topology.Algebra.Group.OpenSubgroup.Compact
import TauCeti.RepresentationTheory.Quotient
import TauCeti.Topology.Algebra.Group.Subgroup

/-!
# Smooth representations and smooth vectors

Let `G` be a topological group and `ρ` a representation of `G` on a module `V` over a semiring `A`,
with no topology on `V`. The representation is *smooth* when every vector has an open stabilizer.
For a locally profinite group, such as the rational points of a reductive group over a
nonarchimedean local field, this says that every vector is fixed by a compact open subgroup, and
these are the representations studied in the representation theory of `p`-adic groups.

Over any semiring `A`, every representation has a largest smooth subrepresentation, its
subrepresentation of *smooth vectors* `V^∞`, made of the vectors with open stabilizer; when `G` is
weakly locally compact and nonarchimedean (in particular, for locally profinite groups), a vector
lies in `V^∞` exactly when its stabilizer contains a compact open subgroup `U` of `G`. When `A` is
a commutative ring and `V` is an additive commutative group (matching `Representation.invariants`),
`V^∞` is correspondingly the union and supremum of the invariants `V^U` over the open subgroups
`U` of `G`, and over the compact open subgroups `U` in the weakly locally compact nonarchimedean
case.

## Main definitions

* `Representation.IsSmooth ρ`: every vector of `V` has an open stabilizer.
* `Representation.smoothVectors ρ`: the subrepresentation of vectors with open stabilizer.
* `Representation.IntertwiningMap.liftSmoothVectors`: unique lift of an intertwining map from a
  smooth representation into `smoothVectors`.
* `Representation.IntertwiningMap.restrictSmoothVectors`: restriction of an intertwining map to
  `smoothVectors`.

## Main results

* `Representation.isSmooth_iff_exists_isCompact_openSubgroup`: for a locally profinite group, a
  representation is smooth when every vector is fixed by a compact open subgroup.
* `Representation.coe_smoothVectors_eq_iUnion`,
  `Representation.toSubmodule_smoothVectors_eq_biSup_invariants_isCompact`: over a commutative ring
  `A` and an additive commutative group `V`, for a locally profinite group, `V^∞` is the union and
  supremum of the invariants of the compact open subgroups.
* `Representation.le_smoothVectors_iff`: `V^∞` is the largest smooth subrepresentation.
* `Representation.smoothVectors_eq_top_iff`: `V^∞ = V` exactly when the representation is smooth.
* `Representation.IsSmooth.of_injective`, `Representation.IsSmooth.of_surjective`: smoothness
  passes to subrepresentations and quotients, and equivalent representations are smooth together
  (`Representation.Equiv.isSmooth_iff`).
* `Representation.IsSmooth.comp`: smoothness passes to the restriction along a continuous
  homomorphism, in particular to subgroups.
* `Representation.isSmooth_ofMulAction_iff`: over a nontrivial semiring, the permutation
  representation on `A[X]` is smooth exactly when every point of `X` has an open stabilizer, as
  for `X = G ⧸ U` with `U` open (`Representation.isSmooth_ofMulAction_quotient`).
* `Representation.smoothVectors_leftRegular_eq_bot`: for a Hausdorff (indeed `T₁`) group that is
  not discrete, the left regular representation on `A[G]` has no nonzero smooth vector.
* `Representation.not_isSmooth_pi_ofMulAction_quotient`: over a nontrivial semiring, an infinite
  product of coset permutation modules `∏ i, A[G ⧸ H i]` fails to be smooth when `⨅ i, H i` is
  not open.

## References

* J. Bernstein, *Representations of p-adic groups*, Harvard lectures 1992, written by
  K. Rumelhart, Chapter I, §1.1, Definition 2 and Proposition 1, p. 7.
* JX-Mo, [mathlib4#41525](https://github.com/leanprover-community/mathlib4/pull/41525) (file
  `Mathlib/RepresentationTheory/Smooth/Basic.lean`), and the Lean Zulip discussion
  [class and def (p-adic reps)](https://leanprover-community.github.io/archive/stream/116395-maths/topic/class.20and.20def.20%28p-adic.20reps%29.html),
  whose design this file follows: `IsSmooth` as a `Prop`-valued class asserting open stabilizers,
  and `smoothVectors` as a `Subrepresentation`.
-/

public section

open Set
open scoped MonoidAlgebra

namespace Representation

variable {A G V W : Type*} [Semiring A] [Group G]
  [AddCommMonoid V] [Module A V] [AddCommMonoid W] [Module A W]
  {ρ : Representation A G V} {σ : Representation A G W}

variable [TopologicalSpace G]

/-! ### Smooth representations -/

section IsSmooth

variable (ρ) in
/-- A representation of a topological group `G` is *smooth* when the stabilizer of every vector
is open in `G`. -/
@[mk_iff]
class IsSmooth : Prop where
  isOpen_stabilizer (v : V) : IsOpen (ρ.stabilizer v : Set G)

/-- A representation with an injective intertwining map to a smooth representation is smooth;
in particular smoothness passes to subrepresentations. -/
theorem IsSmooth.of_injective [IsSmooth σ] (f : ρ.IntertwiningMap σ)
    (hf : Function.Injective f) : IsSmooth ρ :=
  ⟨fun v ↦ f.stabilizer_apply_of_injective hf v ▸ IsSmooth.isOpen_stabilizer (f v)⟩

/-- A representation receiving a surjective intertwining map from a smooth representation is
smooth; in particular smoothness passes to quotients. -/
theorem IsSmooth.of_surjective [SeparatelyContinuousMul G] [IsSmooth ρ]
    (f : ρ.IntertwiningMap σ) (hf : Function.Surjective f) : IsSmooth σ := by
  refine ⟨fun w ↦ ?_⟩
  obtain ⟨v, rfl⟩ := hf w
  exact Subgroup.isOpen_mono (f.stabilizer_le v) (IsSmooth.isOpen_stabilizer v)

/-- Equivalent representations are smooth together, since an equivalence preserves stabilizers. -/
theorem Equiv.isSmooth_iff (e : Equiv ρ σ) : IsSmooth ρ ↔ IsSmooth σ := by
  refine ⟨fun _ ↦ ⟨fun w ↦ ?_⟩, fun _ ↦ ⟨fun v ↦ ?_⟩⟩
  · rw [← e.apply_symm_apply w, e.stabilizer_apply]
    exact IsSmooth.isOpen_stabilizer _
  · rw [← e.stabilizer_apply]
    exact IsSmooth.isOpen_stabilizer _

/-- A subrepresentation of a smooth representation is smooth. -/
instance [IsSmooth ρ] (ρ' : Subrepresentation ρ) : IsSmooth ρ'.toRepresentation :=
  ⟨fun v ↦ ρ'.stabilizer_toRepresentation v ▸ IsSmooth.isOpen_stabilizer (v : V)⟩

/-- The restriction of a smooth representation to an invariant submodule is smooth. -/
instance [IsSmooth ρ] (W : Submodule A V) (le_comap : ∀ g, W ≤ W.comap (ρ g)) :
    IsSmooth (ρ.subrepresentation W le_comap) :=
  IsSmooth.of_injective (σ := ρ) ⟨W.subtype, fun _ ↦ rfl⟩ W.injective_subtype

/-- The restriction of a smooth representation along a continuous homomorphism is smooth. -/
theorem IsSmooth.comp [IsSmooth ρ] {H : Type*} [Group H] [TopologicalSpace H] {φ : H →* G}
    (hφ : Continuous φ) : IsSmooth (ρ.comp φ) :=
  ⟨fun v ↦ (IsSmooth.isOpen_stabilizer (ρ := ρ) v).preimage hφ⟩

/-- The restriction of a smooth representation to a subgroup is smooth. -/
instance [IsSmooth ρ] (H : Subgroup G) : IsSmooth (ρ.comp H.subtype) :=
  IsSmooth.comp continuous_subtypeVal

/-- Descending a smooth representation to `G ⧸ S` along a normal subgroup `S` acting trivially
yields a smooth representation of `G ⧸ S` in the quotient topology. -/
instance instIsSmoothOfQuotient [IsSmooth ρ] (S : Subgroup G) [S.Normal]
    [IsTrivial (ρ.comp S.subtype)] : IsSmooth (ρ.ofQuotient S) where
  isOpen_stabilizer v := by
    rw [← (QuotientGroup.isQuotientMap_mk S).isOpen_preimage]
    change IsOpen
      ((((ρ.ofQuotient S).stabilizer v).comap (QuotientGroup.mk' S) : Subgroup G) : Set G)
    rw [comap_mk'_stabilizer_ofQuotient]
    exact IsSmooth.isOpen_stabilizer v

/-- The binary product of two smooth representations is smooth. -/
instance instIsSmoothProd [IsSmooth ρ] [IsSmooth σ] : IsSmooth (ρ.prod σ) where
  isOpen_stabilizer x := by
    rw [stabilizer_prod]
    exact (IsSmooth.isOpen_stabilizer x.fst).inter (IsSmooth.isOpen_stabilizer x.snd)

/-- A finite product `Representation.pi ρ` of smooth representations is smooth. -/
instance instIsSmoothPi {ι : Type*} [Finite ι] {M : ι → Type*}
    [∀ i, AddCommMonoid (M i)] [∀ i, Module A (M i)] (ρ : ∀ i, Representation A G (M i))
    [∀ i, IsSmooth (ρ i)] : IsSmooth (Representation.pi ρ) where
  isOpen_stabilizer x := by
    rw [stabilizer_pi, Subgroup.coe_iInf]
    exact isOpen_iInter_of_finite fun i ↦ IsSmooth.isOpen_stabilizer (x i)

/-- Every representation of a discrete group is smooth. -/
instance [DiscreteTopology G] : IsSmooth ρ :=
  ⟨fun _ ↦ isOpen_discrete _⟩

/-- A trivial representation is smooth: every stabilizer is the whole group. -/
instance [ρ.IsTrivial] : IsSmooth ρ :=
  ⟨fun v ↦ by
    convert isOpen_univ
    exact Set.eq_univ_of_forall fun g ↦ by simp [IsTrivial.out (ρ := ρ) g]⟩

/-- A representation on a space with at most one vector is smooth. -/
instance [Subsingleton V] : IsSmooth ρ :=
  ⟨fun v ↦ by
    convert isOpen_univ
    exact Set.eq_univ_of_forall fun g ↦ Subsingleton.elim (ρ g v) v⟩

end IsSmooth

/-! ### The subrepresentation of smooth vectors -/

section SmoothVectors

variable [SeparatelyContinuousMul G]

/-- A vector has open stabilizer exactly when each of its translates does: the stabilizer of
`ρ g v` is the conjugate `g (ρ.stabilizer v) g⁻¹`. -/
@[simp]
theorem isOpen_stabilizer_apply_iff (g : G) {v : V} :
    IsOpen (ρ.stabilizer (ρ g v) : Set G) ↔ IsOpen (ρ.stabilizer v : Set G) := by
  rw [stabilizer_conj, Subgroup.isOpen_map_conj_iff]

variable (ρ) in
/-- The *smooth vectors* `V^∞` of a representation of a topological group: the vectors whose
stabilizer is open. It is the largest smooth subrepresentation (`le_smoothVectors_iff`). -/
def smoothVectors : Subrepresentation ρ where
  toSubmodule :=
    { carrier := {v | IsOpen (ρ.stabilizer v : Set G)}
      add_mem' := fun {v w} hv hw ↦
        Subgroup.isOpen_mono (ρ.le_stabilizer_add v w) (hv.inter hw)
      zero_mem' := by simp [stabilizer_zero]
      smul_mem' := fun c v hv ↦ Subgroup.isOpen_mono (ρ.le_stabilizer_smul c v) hv }
  apply_mem_toSubmodule g _ hv := (isOpen_stabilizer_apply_iff g).2 hv

@[simp]
theorem mem_smoothVectors_iff {v : V} :
    v ∈ ρ.smoothVectors ↔ IsOpen (ρ.stabilizer v : Set G) :=
  Iff.rfl

/-- The carrier set of `ρ.smoothVectors` consists of the vectors with open stabilizer in `G`. -/
theorem coe_smoothVectors (ρ : Representation A G V) :
    (ρ.smoothVectors : Set V) = {v : V | IsOpen (ρ.stabilizer v : Set G)} :=
  Set.ext fun _ ↦ mem_smoothVectors_iff

/-- A vector lies in `V^∞` exactly when it is fixed by an open subgroup. -/
theorem mem_smoothVectors_iff_exists_openSubgroup {v : V} :
    v ∈ ρ.smoothVectors ↔ ∃ U : OpenSubgroup G, (U : Subgroup G) ≤ ρ.stabilizer v :=
  ⟨fun hv ↦ ⟨⟨ρ.stabilizer v, hv⟩, le_rfl⟩, fun ⟨_, hU⟩ ↦ Subgroup.isOpen_of_openSubgroup _ hU⟩

/-- For a locally profinite group, a vector lies in `V^∞` exactly when it is fixed by a compact
open subgroup. -/
theorem mem_smoothVectors_iff_exists_isCompact_openSubgroup [NonarchimedeanGroup G]
    [WeaklyLocallyCompactSpace G] {v : V} :
    v ∈ ρ.smoothVectors ↔
      ∃ U : OpenSubgroup G, IsCompact (U : Set G) ∧ (U : Subgroup G) ≤ ρ.stabilizer v :=
  (ρ.stabilizer v).isOpen_iff_exists_isCompact_openSubgroup_le

/-- Over a commutative semiring `R`, `ρ.smoothVectors` coincides with the `R[G]`-submodule of
`ρ.asModule` generated by the vectors with open stabilizer. -/
theorem smoothVectors_eq_ofSubmodule'_span {R : Type*} [CommSemiring R] [Module R V]
    (ρ : Representation R G V) :
    ρ.smoothVectors = Subrepresentation.ofSubmodule'
      (Submodule.span R[G]
        {v : ρ.asModule | IsOpen ((ρ.stabilizer (ρ.asModuleEquiv v) : Subgroup G) : Set G)}) := by
  have hset :
      {w : ρ.asModule | IsOpen ((ρ.stabilizer (ρ.asModuleEquiv w) : Subgroup G) : Set G)} =
        (ρ.smoothVectors.asSubmodule : Set ρ.asModule) := by
    ext w
    rw [Set.mem_ofPred_eq, SetLike.mem_coe]
    exact (mem_smoothVectors_iff (ρ := ρ) (v := ρ.asModuleEquiv w)).symm.trans
      (Subrepresentation.mem_asSubmodule_iff (σ := ρ.smoothVectors) (v := ρ.asModuleEquiv w)).symm
  rw [hset, Submodule.span_eq, ← Subrepresentation.subrepresentationSubmoduleOrderIso_apply,
    ← Subrepresentation.subrepresentationSubmoduleOrderIso_symm_apply]
  exact ((Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ)).symm_apply_apply
    ρ.smoothVectors).symm

/-- Translates of smooth vectors are smooth. -/
theorem apply_mem_smoothVectors {v : V} (hv : v ∈ ρ.smoothVectors) (g : G) :
    ρ g v ∈ ρ.smoothVectors :=
  ρ.smoothVectors.apply_mem_toSubmodule g hv

/-- Intertwining maps send smooth vectors to smooth vectors. -/
theorem IntertwiningMap.apply_mem_smoothVectors (f : ρ.IntertwiningMap σ) {v : V}
    (hv : v ∈ ρ.smoothVectors) : f v ∈ σ.smoothVectors :=
  Subgroup.isOpen_mono (f.stabilizer_le v) hv

/-- A representation is smooth exactly when every vector is smooth. -/
theorem isSmooth_iff_forall_mem_smoothVectors : IsSmooth ρ ↔ ∀ v, v ∈ ρ.smoothVectors :=
  isSmooth_iff ρ

/-- Every vector of a smooth representation is smooth. -/
theorem IsSmooth.mem_smoothVectors [IsSmooth ρ] (v : V) : v ∈ ρ.smoothVectors :=
  IsSmooth.isOpen_stabilizer v

/-- `V^∞` is smooth. -/
instance : IsSmooth ρ.smoothVectors.toRepresentation :=
  ⟨fun v ↦ ρ.smoothVectors.stabilizer_toRepresentation v ▸ v.property⟩

/-- An intertwining map from a smooth representation `ρ` into `σ` factors through
`σ.smoothVectors`. -/
def IntertwiningMap.liftSmoothVectors [IsSmooth ρ] (f : ρ.IntertwiningMap σ) :
    ρ.IntertwiningMap σ.smoothVectors.toRepresentation :=
  f.codRestrict σ.smoothVectors fun v ↦
    Subrepresentation.mem_toSubmodule.mpr
      (f.apply_mem_smoothVectors (IsSmooth.mem_smoothVectors v))

/-- Coercing `f.liftSmoothVectors v` to the ambient module evaluates `f` on `v`. -/
@[simp]
theorem IntertwiningMap.coe_liftSmoothVectors_apply [IsSmooth ρ] (f : ρ.IntertwiningMap σ)
    (v : V) :
    ((f.liftSmoothVectors v : σ.smoothVectors.toSubmodule) : W) = f v := by
  simp [liftSmoothVectors]

/-- Composing `f.liftSmoothVectors` with the inclusion of `σ.smoothVectors` recovers `f`. -/
@[simp]
theorem IntertwiningMap.subtype_comp_liftSmoothVectors [IsSmooth ρ] (f : ρ.IntertwiningMap σ) :
    σ.smoothVectors.subtype.comp f.liftSmoothVectors = f :=
  IntertwiningMap.ext <| LinearMap.ext fun _ ↦ by simp

/-- `f.liftSmoothVectors` is the unique intertwining map into `σ.smoothVectors` whose composition
with `σ.smoothVectors.subtype` is `f`. -/
theorem IntertwiningMap.liftSmoothVectors_unique [IsSmooth ρ] (f : ρ.IntertwiningMap σ)
    (g : ρ.IntertwiningMap σ.smoothVectors.toRepresentation)
    (hg : σ.smoothVectors.subtype.comp g = f) :
    g = f.liftSmoothVectors :=
  IntertwiningMap.ext <| LinearMap.ext fun v ↦ Subtype.ext <| by
    simpa using congrArg (fun h ↦ h v) hg

/-- **Functoriality of smooth vectors:** an intertwining map `f : ρ → σ` restricts to an
intertwining map `ρ.smoothVectors → σ.smoothVectors`. -/
def IntertwiningMap.restrictSmoothVectors (f : ρ.IntertwiningMap σ) :
    ρ.smoothVectors.toRepresentation.IntertwiningMap σ.smoothVectors.toRepresentation :=
  (f.comp ρ.smoothVectors.subtype).liftSmoothVectors

/-- Coercing `f.restrictSmoothVectors v` to the ambient module evaluates `f` on `v`. -/
@[simp]
theorem IntertwiningMap.coe_restrictSmoothVectors_apply (f : ρ.IntertwiningMap σ)
    (v : ρ.smoothVectors.toSubmodule) :
    ((f.restrictSmoothVectors v : σ.smoothVectors.toSubmodule) : W) = f v := by
  simp [restrictSmoothVectors]

/-- Composing `f.restrictSmoothVectors` with the inclusion of `σ.smoothVectors` equals the
restriction of `f` to `ρ.smoothVectors`. -/
@[simp]
theorem IntertwiningMap.subtype_comp_restrictSmoothVectors (f : ρ.IntertwiningMap σ) :
    σ.smoothVectors.subtype.comp f.restrictSmoothVectors = f.comp ρ.smoothVectors.subtype :=
  (f.comp ρ.smoothVectors.subtype).subtype_comp_liftSmoothVectors

/-- Restricting the identity intertwining map to `smoothVectors` yields the identity. -/
@[simp]
theorem IntertwiningMap.restrictSmoothVectors_id (ρ : Representation A G V) :
    (IntertwiningMap.id ρ).restrictSmoothVectors = IntertwiningMap.id _ :=
  IntertwiningMap.ext <| LinearMap.ext fun _ ↦ Subtype.ext <| by simp

/-- Restriction to `smoothVectors` commutes with composition of intertwining maps. -/
@[simp]
theorem IntertwiningMap.restrictSmoothVectors_comp {U : Type*} [AddCommMonoid U] [Module A U]
    {τ : Representation A G U} (g : σ.IntertwiningMap τ) (f : ρ.IntertwiningMap σ) :
    (g.comp f).restrictSmoothVectors = g.restrictSmoothVectors.comp f.restrictSmoothVectors :=
  IntertwiningMap.ext <| LinearMap.ext fun _ ↦ Subtype.ext <| by simp

/-- A representation is smooth exactly when every vector is fixed by an open subgroup. -/
theorem isSmooth_iff_exists_openSubgroup :
    IsSmooth ρ ↔ ∀ v, ∃ U : OpenSubgroup G, (U : Subgroup G) ≤ ρ.stabilizer v := by
  simp only [isSmooth_iff_forall_mem_smoothVectors, mem_smoothVectors_iff_exists_openSubgroup]

/-- For a locally profinite group, a representation is smooth exactly when every vector is fixed
by a compact open subgroup. -/
theorem isSmooth_iff_exists_isCompact_openSubgroup [NonarchimedeanGroup G]
    [WeaklyLocallyCompactSpace G] :
    IsSmooth ρ ↔
      ∀ v, ∃ U : OpenSubgroup G, IsCompact (U : Set G) ∧ (U : Subgroup G) ≤ ρ.stabilizer v := by
  simp only [isSmooth_iff_forall_mem_smoothVectors,
    mem_smoothVectors_iff_exists_isCompact_openSubgroup]

/-- `V^∞` is the largest smooth subrepresentation: a subrepresentation lies in it exactly when it
is smooth. -/
theorem le_smoothVectors_iff {ρ' : Subrepresentation ρ} :
    ρ' ≤ ρ.smoothVectors ↔ IsSmooth ρ'.toRepresentation := by
  rw [isSmooth_iff]
  refine ⟨fun h v ↦ ?_, fun h v hv ↦ ?_⟩
  · rw [Subrepresentation.stabilizer_toRepresentation]
    exact h v.property
  · simpa using h ⟨v, hv⟩

/-- `V^∞ = V` exactly when the representation is smooth. -/
theorem smoothVectors_eq_top_iff : ρ.smoothVectors = ⊤ ↔ IsSmooth ρ := by
  rw [eq_top_iff, isSmooth_iff_forall_mem_smoothVectors]
  exact ⟨fun h v ↦ h Subrepresentation.mem_top, fun h v _ ↦ h v⟩

/-- A smooth representation is its own subrepresentation of smooth vectors. -/
@[simp]
theorem smoothVectors_eq_top [IsSmooth ρ] : ρ.smoothVectors = ⊤ :=
  smoothVectors_eq_top_iff.2 inferInstance

end SmoothVectors

/-! ### Invariants of open and compact open subgroups

Because `Representation.invariants` requires a commutative ring acting on an additive commutative
group, the invariant characterizations in this section assume `[CommRing A]` and
`[AddCommGroup V]`. -/

section Invariants

variable {A G V : Type*} [CommRing A] [Group G] [AddCommGroup V] [Module A V]
  {ρ : Representation A G V}

section TopologicalGroup

variable [TopologicalSpace G] [SeparatelyContinuousMul G]

/-- Over a commutative ring, `v ∈ ρ.smoothVectors` if and only if `v ∈ V^U` for some open subgroup
`U` of `G`. -/
theorem mem_smoothVectors_iff_exists_openSubgroup_mem_invariants {v : V} :
    v ∈ ρ.smoothVectors ↔ ∃ U : OpenSubgroup G, v ∈ invariants (ρ.comp U.toSubgroup.subtype) := by
  simp_rw [mem_smoothVectors_iff_exists_openSubgroup, mem_invariants_comp_subtype_iff]

/-- Over a commutative ring, `ρ` is smooth if and only if every vector lies in `V^U` for some open
subgroup `U` of `G`. -/
theorem isSmooth_iff_forall_exists_openSubgroup_mem_invariants (ρ : Representation A G V) :
    IsSmooth ρ ↔ ∀ v : V, ∃ U : OpenSubgroup G, v ∈ invariants (ρ.comp U.toSubgroup.subtype) := by
  simp_rw [isSmooth_iff_exists_openSubgroup, mem_invariants_comp_subtype_iff]

/-- As a set, `ρ.smoothVectors` is the union of the `U`-invariants `V^U` over all open subgroups
`U` of `G`. -/
theorem coe_smoothVectors_eq_iUnion_invariants (ρ : Representation A G V) :
    (ρ.smoothVectors : Set V) =
      ⋃ U : OpenSubgroup G, (invariants (ρ.comp U.toSubgroup.subtype) : Set V) := by
  ext v
  simp only [SetLike.mem_coe, mem_smoothVectors_iff_exists_openSubgroup_mem_invariants,
    Set.mem_iUnion]

/-- The underlying `A`-submodule of `ρ.smoothVectors` is the supremum of `V^U` over all open
subgroups `U` of `G`. -/
theorem toSubmodule_smoothVectors_eq_iSup_invariants (ρ : Representation A G V) :
    ρ.smoothVectors.toSubmodule =
      ⨆ U : OpenSubgroup G, invariants (ρ.comp U.toSubgroup.subtype) := by
  refine le_antisymm (fun v hv ↦ ?_) (iSup_le fun U v hv ↦ ?_)
  · obtain ⟨U, hU⟩ := mem_smoothVectors_iff_exists_openSubgroup_mem_invariants.mp hv
    exact Submodule.mem_iSup_of_mem U hU
  · exact mem_smoothVectors_iff_exists_openSubgroup_mem_invariants.mpr ⟨U, hv⟩

end TopologicalGroup

section LocallyProfinite

variable [TopologicalSpace G] [NonarchimedeanGroup G] [WeaklyLocallyCompactSpace G]

/-- In a weakly locally compact nonarchimedean group, `v ∈ ρ.smoothVectors` if and only if
`v ∈ V^U` for some compact open subgroup `U` of `G`. -/
theorem mem_smoothVectors_iff_exists_isCompact_openSubgroup_mem_invariants {v : V} :
    v ∈ ρ.smoothVectors ↔
      ∃ U : OpenSubgroup G, IsCompact (U : Set G) ∧
        v ∈ invariants (ρ.comp U.toSubgroup.subtype) := by
  simp_rw [mem_smoothVectors_iff_exists_isCompact_openSubgroup, mem_invariants_comp_subtype_iff]

/-- For a locally profinite group, `V^∞ = ⋃ V^U`, the union of the invariants of the compact open
subgroups `U`. -/
theorem coe_smoothVectors_eq_iUnion :
    (ρ.smoothVectors : Set V) =
      ⋃ (U : OpenSubgroup G) (_ : IsCompact (U : Set G)),
        (invariants (ρ.comp (U : Subgroup G).subtype) : Set V) := by
  ext v
  simp only [SetLike.mem_coe, mem_smoothVectors_iff_exists_isCompact_openSubgroup, mem_iUnion,
    mem_invariants_comp_subtype_iff, exists_prop]

/-- For a locally profinite group, the underlying `A`-submodule of `ρ.smoothVectors` is the
supremum of `V^U` over all compact open subgroups `U` of `G`. -/
theorem toSubmodule_smoothVectors_eq_biSup_invariants_isCompact (ρ : Representation A G V) :
    ρ.smoothVectors.toSubmodule =
      ⨆ (U : OpenSubgroup G) (_ : IsCompact (U : Set G)),
        invariants (ρ.comp U.toSubgroup.subtype) := by
  refine le_antisymm (fun v hv ↦ ?_) (iSup₂_le fun U hU v hv ↦ ?_)
  · obtain ⟨U, hUcpt, hU⟩ :=
      mem_smoothVectors_iff_exists_isCompact_openSubgroup_mem_invariants.mp hv
    exact Submodule.mem_iSup_of_mem U (Submodule.mem_iSup_of_mem hUcpt hU)
  · exact mem_smoothVectors_iff_exists_isCompact_openSubgroup_mem_invariants.mpr ⟨U, hU, hv⟩

/-- In a weakly locally compact nonarchimedean group, `ρ` is smooth if and only if every vector
lies in `V^U` for some compact open subgroup `U` of `G`. -/
theorem isSmooth_iff_forall_exists_isCompact_openSubgroup_mem_invariants
    (ρ : Representation A G V) :
    IsSmooth ρ ↔ ∀ v : V, ∃ U : OpenSubgroup G, IsCompact (U : Set G) ∧
      v ∈ invariants (ρ.comp U.toSubgroup.subtype) := by
  simp_rw [isSmooth_iff_exists_isCompact_openSubgroup, mem_invariants_comp_subtype_iff]

/-- For a locally profinite group, a representation is smooth exactly when `V = ⋃ V^U`, the
union of the invariants of the compact open subgroups `U`. -/
theorem isSmooth_iff_iUnion_eq_univ :
    IsSmooth ρ ↔
      ⋃ (U : OpenSubgroup G) (_ : IsCompact (U : Set G)),
        (invariants (ρ.comp (U : Subgroup G).subtype) : Set V) = univ := by
  simp only [← coe_smoothVectors_eq_iUnion, isSmooth_iff_forall_mem_smoothVectors,
    eq_univ_iff_forall, SetLike.mem_coe]

/-- For a locally profinite group, `⨆_U V^U = ⊤` over compact open subgroups `U` if and only if
`ρ` is smooth. -/
theorem biSup_invariants_isCompact_eq_top_iff_isSmooth (ρ : Representation A G V) :
    (⨆ (U : OpenSubgroup G) (_ : IsCompact (U : Set G)),
      invariants (ρ.comp U.toSubgroup.subtype)) = ⊤ ↔ IsSmooth ρ := by
  rw [← toSubmodule_smoothVectors_eq_biSup_invariants_isCompact, ← smoothVectors_eq_top_iff,
    ← Subrepresentation.toSubmodule_injective.eq_iff, Subrepresentation.toSubmodule_top]

end LocallyProfinite

end Invariants

/-! ### Quotients -/

section Quotient

variable {A G V : Type*} [Ring A] [Group G] [TopologicalSpace G] [SeparatelyContinuousMul G]
  [AddCommGroup V] [Module A V] {ρ : Representation A G V}

/-- A quotient of a smooth representation by an invariant submodule is smooth. -/
instance [IsSmooth ρ] (W : Submodule A V) (le_comap : ∀ g, W ≤ W.comap (ρ g)) :
    IsSmooth (ρ.quotient W le_comap) :=
  IsSmooth.of_surjective (σ := ρ.quotient W le_comap)
    ⟨W.mkQ, fun _ ↦ rfl⟩ W.mkQ_surjective

/-- The quotient of a smooth representation by a subrepresentation is smooth. -/
instance [IsSmooth ρ] (ρ' : Subrepresentation ρ) : IsSmooth ρ'.quotient :=
  inferInstanceAs (IsSmooth (ρ.quotient _ _))

end Quotient

/-! ### Permutation, regular, and infinite-product representations -/

section OfMulAction

variable {X : Type*} [MulAction G X]

/-- The permutation representation on `A[X]` is smooth when every point of `X` has an open
stabilizer. -/
theorem isSmooth_ofMulAction [SeparatelyContinuousMul G]
    (h : ∀ x : X, IsOpen (MulAction.stabilizer G x : Set G)) : IsSmooth (ofMulAction A G X) := by
  rw [isSmooth_iff_forall_mem_smoothVectors]
  intro f
  induction f using MonoidAlgebra.induction_linear with
  | zero => exact (ofMulAction A G X).smoothVectors.toSubmodule.zero_mem
  | add u w hu hw => exact (ofMulAction A G X).smoothVectors.toSubmodule.add_mem hu hw
  | single x r => exact Subgroup.isOpen_mono (le_stabilizer_ofMulAction_single x r) (h x)

/-- Over a nontrivial semiring, the permutation representation on `A[X]` is smooth exactly when
every point of `X` has an open stabilizer. -/
theorem isSmooth_ofMulAction_iff [SeparatelyContinuousMul G] [Nontrivial A] :
    IsSmooth (ofMulAction A G X) ↔ ∀ x : X, IsOpen (MulAction.stabilizer G x : Set G) :=
  ⟨fun _ x ↦ stabilizer_ofMulAction_single (A := A) (G := G) x one_ne_zero ▸
    IsSmooth.isOpen_stabilizer _, isSmooth_ofMulAction⟩

/-- The permutation representation on a discrete set with a continuous action is smooth; for
instance `A[G ⧸ U]` for an open subgroup `U`. -/
instance [SeparatelyContinuousMul G] [TopologicalSpace X] [DiscreteTopology X]
    [ContinuousSMul G X] : IsSmooth (ofMulAction A G X) :=
  isSmooth_ofMulAction (stabilizer_isOpen G)

/-- The permutation representation `A[G ⧸ U]` on the cosets of an open subgroup is smooth: the
stabilizer of the coset `g U` is the open subgroup `g U g⁻¹`. Unlike the instance for discrete
`G`-sets with a continuous action, this needs only separately continuous multiplication. -/
instance isSmooth_ofMulAction_quotient [SeparatelyContinuousMul G] (U : OpenSubgroup G) :
    IsSmooth (ofMulAction A G (G ⧸ (U : Subgroup G))) :=
  isSmooth_ofMulAction fun x ↦ by
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    have hg : ((g : G ⧸ (U : Subgroup G))) = g • ((1 : G) : G ⧸ (U : Subgroup G)) := by simp
    rw [hg, MulAction.stabilizer_smul_eq_stabilizer_map_conj, MulAction.stabilizer_quotient,
      MulEquiv.toMonoidHom_eq_coe, Subgroup.isOpen_map_conj_iff]
    exact U.isOpen

/-- Over a nontrivial semiring, the left regular representation on `A[G]` is smooth exactly when
`G` is discrete. -/
theorem isSmooth_leftRegular_iff [SeparatelyContinuousMul G] [Nontrivial A] :
    IsSmooth (leftRegular A G) ↔ DiscreteTopology G := by
  simp [isSmooth_ofMulAction_iff, discreteTopology_iff_isOpen_singleton_one]

/-- For a `T₁` group that is not discrete, the left regular representation on `A[G]` has no
nonzero smooth vector. -/
theorem smoothVectors_leftRegular_eq_bot [SeparatelyContinuousMul G] [T1Space G]
    (hG : ¬ DiscreteTopology G) : (leftRegular A G).smoothVectors = ⊥ := by
  -- A nonzero `f` with open stabilizer `H` would make `H` finite, and a finite open subgroup of a
  -- `T₁` group makes `{1}` open.
  refine eq_bot_iff.2 fun f hf ↦ ?_
  rw [Subrepresentation.mem_bot]
  by_contra hf0
  set H := (leftRegular A G).stabilizer f
  have hfin : (H : Set G).Finite := finite_stabilizer_leftRegular hf0
  exact hG (discreteTopology_of_isOpen_singleton_one
    (isOpen_singleton_of_finite_mem_nhds 1 ((mem_smoothVectors_iff.1 hf).mem_nhds H.one_mem) hfin))

omit [TopologicalSpace G] in
private theorem stabilizer_pi_ofMulAction_quotient_basepoint [Nontrivial A] {ι : Type*}
    (H : ι → Subgroup G) :
    (Representation.pi fun i ↦ ofMulAction A G (G ⧸ H i)).stabilizer
        (fun i ↦ MonoidAlgebra.single ((1 : G) : G ⧸ H i) (1 : A)) =
      ⨅ i, H i := by
  simp only [stabilizer_pi, stabilizer_ofMulAction_single _ one_ne_zero,
    MulAction.stabilizer_quotient]

/-- In a product `∏ i, A[G ⧸ H i]` of coset permutation representations over a nontrivial
semiring `A`, if `⨅ i, H i` is not open in `G`, then the family of basepoints
`fun i ↦ single ↑1 1` is not a smooth vector. -/
theorem notMem_smoothVectors_pi_ofMulAction_quotient [Nontrivial A] [SeparatelyContinuousMul G]
    {ι : Type*} {H : ι → Subgroup G}
    (hH : ¬ IsOpen (((⨅ i, H i : Subgroup G) : Set G))) :
    (fun i ↦ MonoidAlgebra.single ((1 : G) : G ⧸ H i) 1) ∉
      (Representation.pi fun i ↦ ofMulAction A G (G ⧸ H i)).smoothVectors := by
  simpa [mem_smoothVectors_iff, stabilizer_pi_ofMulAction_quotient_basepoint] using hH

/-- In a product `∏ i, A[G ⧸ H i]` of coset permutation representations over a nontrivial
semiring `A`, if `⨅ i, H i` is not open in `G`, then the product representation is not smooth. -/
theorem not_isSmooth_pi_ofMulAction_quotient [Nontrivial A] {ι : Type*} {H : ι → Subgroup G}
    (hH : ¬ IsOpen (((⨅ i, H i : Subgroup G) : Set G))) :
    ¬ IsSmooth (Representation.pi fun i ↦ ofMulAction A G (G ⧸ H i)) := fun h ↦
  hH (stabilizer_pi_ofMulAction_quotient_basepoint (A := A) H ▸ h.isOpen_stabilizer _)

end OfMulAction

end Representation

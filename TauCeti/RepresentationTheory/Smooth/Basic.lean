/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Stabilizer
public import TauCeti.RepresentationTheory.Subrepresentation
public import TauCeti.Topology.Algebra.Group.OpenSubgroup.Compact
import TauCeti.Topology.Algebra.Group.Subgroup

/-!
# Smooth representations and smooth vectors

Let `G` be a topological group and `ρ` a representation of `G` on a module `V` over a semiring `A`,
with no topology on `V`. The representation is *smooth* when every vector has an open stabilizer.
For a locally profinite group, such as the rational points of a reductive group over a
nonarchimedean local field, this says that every vector is fixed by a compact open subgroup, and
these are the representations studied in the representation theory of `p`-adic groups.

Every representation has a largest smooth subrepresentation, its subrepresentation of *smooth
vectors* `V^∞`, made of the vectors with open stabilizer. When `G` is weakly locally compact and
nonarchimedean (locally profinite), `V^∞` is the union of the invariants `V^U` over the compact
open subgroups `U` of `G`.

## Main definitions

* `Representation.IsSmooth ρ`: every vector of `V` has an open stabilizer.
* `Representation.smoothVectors ρ`: the subrepresentation of vectors with open stabilizer.

## Main results

* `Representation.isSmooth_iff_exists_isCompact_openSubgroup`: for a locally profinite group, a
  representation is smooth when every vector is fixed by a compact open subgroup.
* `Representation.coe_smoothVectors_eq_iUnion`: for a locally profinite group, `V^∞` is the
  union of the invariants of the compact open subgroups.
* `Representation.iSup_invariants_eq_smoothVectors`,
  `Representation.isSmooth_iff_iSup_invariants_eq_top`: for any basis of neighbourhoods of `1`
  made of subgroups, `V^∞` is the supremum of their invariants.
* `Representation.le_smoothVectors_iff`: `V^∞` is the largest smooth subrepresentation.
* `Representation.smoothVectors_eq_top_iff`: `V^∞ = V` exactly when the representation is smooth.
* `Representation.IsSmooth.of_injective`, `Representation.IsSmooth.of_surjective`: smoothness
  passes to subrepresentations and quotients, and equivalent representations are smooth together
  (`Representation.Equiv.isSmooth_iff`).
* `Representation.IsSmooth.comp`: smoothness passes to the restriction along a continuous
  homomorphism, in particular to subgroups.
* `Representation.isSmooth_ofMulAction_iff`: the permutation representation on `A[X]` is smooth
  exactly when every point of `X` has an open stabilizer, as for `X = G ⧸ U` with `U` open
  (`Representation.isSmooth_ofMulAction_quotient`).
* `Representation.smoothVectors_leftRegular_eq_bot`: for a Hausdorff (indeed `T₁`) group that is
  not discrete, the left regular representation on `A[G]` has no nonzero smooth vector.

## References

* J. Bernstein, *Representations of p-adic groups*, Harvard lectures 1992, written by
  K. Rumelhart, Chapter I, §1.1, Definition 2 and Proposition 1, p. 7.
* JX-Mo, [mathlib4#41525](https://github.com/leanprover-community/mathlib4/pull/41525) (file
  `Mathlib/RepresentationTheory/Smooth/Basic.lean`), whose design this file follows:
  `IsSmooth` as a Prop-valued class asserting open stabilizers, and `smoothVectors` as a
  `Subrepresentation`.
-/

public section

open Set Topology
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

/-- `V^∞` is smooth. -/
instance : IsSmooth ρ.smoothVectors.toRepresentation :=
  ⟨fun v ↦ ρ.smoothVectors.stabilizer_toRepresentation v ▸ v.property⟩

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

/-! ### Invariants of a basis of open subgroups -/

section Basis

variable {A G V : Type*} [CommRing A] [Group G] [AddCommGroup V] [Module A V]
  {ρ : Representation A G V} [TopologicalSpace G] [SeparatelyContinuousMul G]

/-- For any family of subgroups forming a basis of neighbourhoods of `1`, the smooth vectors are
the supremum of the invariants of the members of the family. -/
theorem iSup_invariants_eq_smoothVectors {ι : Type*} {p : ι → Prop} {U : ι → Subgroup G}
    (hU : (𝓝 (1 : G)).HasBasis p fun i ↦ (U i : Set G)) :
    ⨆ (i) (_ : p i), invariants (ρ.comp (U i).subtype) = ρ.smoothVectors.toSubmodule := by
  refine le_antisymm (iSup₂_le fun i hi v hv ↦ ?_) fun v hv ↦ ?_
  · have hUi : IsOpen (U i : Set G) := (U i).isOpen_of_mem_nhds (hU.mem_of_mem hi)
    exact (mem_smoothVectors_iff_exists_openSubgroup (ρ := ρ)).2
      ⟨⟨U i, hUi⟩, mem_invariants_comp_subtype_iff.1 hv⟩
  · obtain ⟨i, hi, hsub⟩ := hU.mem_iff.1
      ((mem_smoothVectors_iff (ρ := ρ)).1 hv |>.mem_nhds (ρ.stabilizer v).one_mem)
    exact Submodule.mem_iSup_of_mem i <| Submodule.mem_iSup_of_mem hi <|
      mem_invariants_comp_subtype_iff.2 hsub

/-- For any family of subgroups forming a basis of neighbourhoods of `1`, a representation is
smooth exactly when the invariants of the members of the family span `V`. -/
theorem isSmooth_iff_iSup_invariants_eq_top {ι : Type*} {p : ι → Prop} {U : ι → Subgroup G}
    (hU : (𝓝 (1 : G)).HasBasis p fun i ↦ (U i : Set G)) :
    IsSmooth ρ ↔ ⨆ (i) (_ : p i), invariants (ρ.comp (U i).subtype) = ⊤ := by
  rw [iSup_invariants_eq_smoothVectors hU, isSmooth_iff_forall_mem_smoothVectors,
    Submodule.eq_top_iff']
  rfl

end Basis

/-! ### Invariants of compact open subgroups -/

section Invariants

variable {A G V : Type*} [CommRing A] [Group G] [AddCommGroup V] [Module A V]
  {ρ : Representation A G V}

variable [TopologicalSpace G] [NonarchimedeanGroup G] [WeaklyLocallyCompactSpace G]

/-- For a locally profinite group, `V^∞ = ⋃ V^U`, the union of the invariants of the compact open
subgroups `U`. -/
theorem coe_smoothVectors_eq_iUnion :
    (ρ.smoothVectors : Set V) =
      ⋃ (U : OpenSubgroup G) (_ : IsCompact (U : Set G)),
        (invariants (ρ.comp (U : Subgroup G).subtype) : Set V) := by
  ext v
  simp only [SetLike.mem_coe, mem_smoothVectors_iff_exists_isCompact_openSubgroup, mem_iUnion,
    mem_invariants_comp_subtype_iff, exists_prop]

/-- For a locally profinite group, a representation is smooth exactly when `V = ⋃ V^U`, the
union of the invariants of the compact open subgroups `U`. -/
theorem isSmooth_iff_iUnion_eq_univ :
    IsSmooth ρ ↔
      ⋃ (U : OpenSubgroup G) (_ : IsCompact (U : Set G)),
        (invariants (ρ.comp (U : Subgroup G).subtype) : Set V) = univ := by
  simp only [← coe_smoothVectors_eq_iUnion, isSmooth_iff_forall_mem_smoothVectors,
    eq_univ_iff_forall, SetLike.mem_coe]

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

/-! ### Permutation representations -/

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
  | add f₁ f₂ h₁ h₂ => exact (ofMulAction A G X).smoothVectors.toSubmodule.add_mem h₁ h₂
  | single x r =>
    refine Subgroup.isOpen_mono (fun g hg ↦ ?_) (h x)
    rw [mem_stabilizer, ofMulAction_single, MulAction.mem_stabilizer_iff.1 hg]

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
  -- A nonzero `f` with open stabilizer `H` would make `H` finite, since `H` permutes the finite
  -- support of `f`, and a finite open subgroup of a `T₁` group makes `{1}` open.
  refine eq_bot_iff.2 fun f hf ↦ ?_
  rw [Subrepresentation.mem_bot]
  by_contra hf0
  obtain ⟨x, hx⟩ := Finsupp.support_nonempty_iff.2 (mt MonoidAlgebra.coeff_eq_zero.1 hf0)
  set H := (leftRegular A G).stabilizer f
  -- Every `g ∈ H` sends `x` into the support of `f`, so `H` lies in a finite set.
  have hfin : (H : Set G).Finite := by
    refine ((f.coeff.support.finite_toSet.image fun y ↦ y * x⁻¹)).subset fun g hg ↦ ?_
    refine ⟨g * x, ?_, by simp⟩
    rw [← mem_stabilizer.1 hg]
    simpa [coeff_ofMulAction] using hx
  exact hG (discreteTopology_of_isOpen_singleton_one
    (isOpen_singleton_of_finite_mem_nhds 1 ((mem_smoothVectors_iff.1 hf).mem_nhds H.one_mem) hfin))

end OfMulAction

end Representation

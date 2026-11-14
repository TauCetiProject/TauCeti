/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.OpenSubgroup
public import TauCeti.RepresentationTheory.Intertwining
public import TauCeti.RepresentationTheory.Subrepresentation

/-!
# Smooth representations and smooth vectors

Let `G` be a topological group, `A` a semiring and `ρ : Representation A G V` a representation of
`G` on an `A`-module `V`, with no topology on `V`. The representation is *smooth* when the
stabilizer of every vector is open in `G`. For a locally profinite group `G` (for instance the
points of a reductive group over a nonarchimedean local field) these are the smooth
representations of Bernstein–Zelevinsky, the local components of automorphic representations; over
an arbitrary coefficient ring they are the objects of the smooth category, built as a full
subcategory of `Rep A G`.

The smooth vectors `V^∞` of an arbitrary representation are the vectors with open stabilizer. In a
topological group, or more generally whenever multiplication is separately continuous, they form a
subrepresentation: the stabilizer of a sum contains the intersection of the stabilizers, and the
stabilizer of a translate `ρ g v` is a conjugate of that of `v`. Without such a compatibility
between the topology and the group law they need not be closed under translation. It is
the largest smooth subrepresentation, which is what makes `V ↦ V^∞` right adjoint to the inclusion
of smooth representations into all representations.

The definitions follow the design of the smooth representations of mathlib4 pull request
#41525 (`Mathlib/RepresentationTheory/Smooth/Basic.lean`): smoothness is a proposition-valued
class asserting open stabilizers, and the smooth vectors form a `Subrepresentation`.

## Main definitions

* `Representation.IsSmooth`: every vector has an open stabilizer.
* `Representation.smoothVectors`: the subrepresentation of vectors with open stabilizer.

## Main results

* `Representation.isSmooth_iff_forall_exists_openSubgroup`: a representation is smooth exactly
  when every vector is fixed by some open subgroup.
* `Representation.IsSmooth.of_injective`, `Representation.IsSmooth.of_surjective`: smoothness
  passes to the source of an injective and to the target of a surjective intertwining map; in
  particular subrepresentations and quotients of smooth representations are smooth.
* `Representation.isSmooth_ofMulAction_iff`: a permutation representation `A[X]` over a nonzero
  ring is smooth exactly when the point stabilizers of `X` are open; in particular `A[G ⧸ U]` is
  smooth for an open subgroup `U`.
* `Representation.smoothVectors_eq_top_iff`: a representation is smooth exactly when all of its
  vectors are smooth.
* `Representation.le_smoothVectors_iff`: the smooth vectors form the largest smooth
  subrepresentation.

## References

* J. Bernstein, *Representations of p-adic groups*, lectures at Harvard University, 1992,
  written by K. E. Rumelhart; Chapter I, §1.1, Definition 2 and Proposition 1.
-/

public section

open Function

namespace Representation

section IsSmooth

variable {A G V W : Type*} [Semiring A] [Group G] [TopologicalSpace G]
  [AddCommMonoid V] [Module A V] [AddCommMonoid W] [Module A W]

/-- A representation `ρ` of a topological group `G` is **smooth** when the stabilizer
`{g | ρ g v = v}` of every vector `v` is open in `G`. No topology on the representation space is
involved. -/
@[mk_iff]
class IsSmooth (ρ : Representation A G V) : Prop where
  /-- The stabilizer of every vector is open. -/
  isOpen_stabilizer (v : V) : IsOpen (ρ.stabilizer v : Set G)

/-- A vector has open stabilizer exactly when it is fixed by some open subgroup. -/
theorem isOpen_stabilizer_iff_exists_openSubgroup [SeparatelyContinuousMul G]
    {ρ : Representation A G V} {v : V} :
    IsOpen (ρ.stabilizer v : Set G) ↔ ∃ U : OpenSubgroup G, ∀ g ∈ U, ρ g v = v :=
  ⟨fun h ↦ ⟨⟨ρ.stabilizer v, h⟩, fun _ hg ↦ hg⟩,
    fun ⟨U, hU⟩ ↦ Subgroup.isOpen_of_openSubgroup _ (U := U) fun g hg ↦ hU g hg⟩

/-- **Smoothness through open subgroups.** A representation is smooth exactly when every vector
is fixed by some open subgroup. -/
theorem isSmooth_iff_forall_exists_openSubgroup [SeparatelyContinuousMul G]
    {ρ : Representation A G V} :
    IsSmooth ρ ↔ ∀ v, ∃ U : OpenSubgroup G, ∀ g ∈ U, ρ g v = v := by
  simp only [isSmooth_iff, isOpen_stabilizer_iff_exists_openSubgroup]

/-- In a smooth representation every vector is fixed by some open subgroup. -/
theorem IsSmooth.exists_openSubgroup (ρ : Representation A G V) [IsSmooth ρ] (v : V) :
    ∃ U : OpenSubgroup G, ∀ g ∈ U, ρ g v = v :=
  ⟨⟨ρ.stabilizer v, IsSmooth.isOpen_stabilizer v⟩, fun _ hg ↦ hg⟩

/-- The trivial representation is smooth: every stabilizer is the whole group. -/
instance isSmooth_trivial : IsSmooth (trivial A G V) :=
  ⟨fun v ↦ by
    convert isOpen_univ
    ext g
    simp [trivial_apply]⟩

/-- Every representation of a discrete group is smooth. -/
instance isSmooth_of_discreteTopology [DiscreteTopology G] (ρ : Representation A G V) :
    IsSmooth ρ :=
  ⟨fun _ ↦ isOpen_discrete _⟩

/-- **Restriction preserves smoothness.** The restriction of a smooth representation along a
continuous homomorphism, for instance to a subgroup, is smooth: its stabilizers are the preimages
of those of `ρ`. -/
theorem IsSmooth.comp {H : Type*} [Group H] [TopologicalSpace H] (ρ : Representation A G V)
    [IsSmooth ρ] {f : H →* G} (hf : Continuous f) : IsSmooth (ρ.comp f) :=
  ⟨fun v ↦ (IsSmooth.isOpen_stabilizer (ρ := ρ) v).preimage hf⟩

/-- **Subobjects of smooth representations are smooth.** Smoothness passes to the source of an
injective intertwining map, which has the same stabilizers. -/
theorem IsSmooth.of_injective {ρ : Representation A G V} {σ : Representation A G W} [IsSmooth σ]
    (f : IntertwiningMap ρ σ) (hf : Injective f) : IsSmooth ρ :=
  ⟨fun v ↦ f.stabilizer_apply_of_injective hf v ▸ IsSmooth.isOpen_stabilizer (f v)⟩

/-- **Quotients of smooth representations are smooth.** Smoothness passes to the target of a
surjective intertwining map, since the stabilizer of `f v` contains that of `v`. -/
theorem IsSmooth.of_surjective [SeparatelyContinuousMul G] {ρ : Representation A G V}
    {σ : Representation A G W} [IsSmooth ρ] (f : IntertwiningMap ρ σ) (hf : Surjective f) :
    IsSmooth σ :=
  ⟨fun w ↦ by
    obtain ⟨v, rfl⟩ := hf w
    exact Subgroup.isOpen_mono (f.stabilizer_le v) (IsSmooth.isOpen_stabilizer v)⟩

/-- A subrepresentation of a smooth representation is smooth. -/
instance _root_.Subrepresentation.isSmooth_toRepresentation {ρ : Representation A G V} [IsSmooth ρ]
    (σ : Subrepresentation ρ) : IsSmooth σ.toRepresentation :=
  IsSmooth.of_injective σ.subtype σ.subtype_injective

/-- The quotient of a smooth representation by an invariant submodule is smooth. -/
instance isSmooth_quotient [SeparatelyContinuousMul G] {A V : Type*} [Ring A] [AddCommGroup V]
    [Module A V] (ρ : Representation A G V) [IsSmooth ρ] (W : Submodule A V)
    (le_comap : ∀ g, W ≤ W.comap (ρ g)) : IsSmooth (ρ.quotient W le_comap) :=
  ⟨fun x ↦ by
    obtain ⟨v, rfl⟩ := W.mkQ_surjective x
    exact Subgroup.isOpen_mono (fun g hg ↦ by simp_all) (IsSmooth.isOpen_stabilizer (ρ := ρ) v)⟩

/-- The quotient of a smooth representation by a subrepresentation is smooth. -/
instance _root_.Subrepresentation.isSmooth_quotient [SeparatelyContinuousMul G] {A V : Type*}
    [Ring A] [AddCommGroup V] [Module A V] {ρ : Representation A G V} [IsSmooth ρ]
    (σ : Subrepresentation ρ) : IsSmooth σ.quotient :=
  Representation.isSmooth_quotient ρ _ _

/-- A permutation representation `A[X]` is smooth when every point of `X` has an open stabilizer:
a finitely supported function is fixed by the open subgroup fixing each point of its support. -/
theorem isSmooth_ofMulAction [SeparatelyContinuousMul G] {X : Type*} [MulAction G X]
    (h : ∀ x : X, IsOpen (MulAction.stabilizer G x : Set G)) : IsSmooth (ofMulAction A G X) := by
  refine ⟨fun f ↦ ?_⟩
  set S : Set G := ⋂ x ∈ f.coeff.support, (MulAction.stabilizer G x : Set G)
  have hS : IsOpen S := isOpen_biInter_finset fun x _ ↦ h x
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset
    (hS.mem_nhds (by simp [S])) fun g hg ↦ ?_)
  have hfix : ∀ x ∈ f.coeff.support, g • x = x := fun x hx ↦ by
    simpa using Set.mem_iInter₂.mp hg x hx
  rw [SetLike.mem_coe, mem_stabilizer]
  ext y
  rw [coeff_ofMulAction]
  by_cases hy : y ∈ f.coeff.support
  · rw [← hfix y hy, inv_smul_smul, hfix y hy]
  · have hgy : g⁻¹ • y ∉ f.coeff.support := fun hgy ↦ hy <| by
      have hy' : y = g⁻¹ • y := by simpa using hfix _ hgy
      rwa [hy']
    rw [Finsupp.notMem_support_iff.mp hy, Finsupp.notMem_support_iff.mp hgy]

/-- **Smooth permutation representations.** Over a nonzero ring, the permutation representation
`A[X]` is smooth exactly when every point of `X` has an open stabilizer: the stabilizer of the
basis vector at `x` is the stabilizer of `x`. -/
theorem isSmooth_ofMulAction_iff [SeparatelyContinuousMul G] [Nontrivial A] {X : Type*}
    [MulAction G X] :
    IsSmooth (ofMulAction A G X) ↔ ∀ x : X, IsOpen (MulAction.stabilizer G x : Set G) := by
  refine ⟨fun h x ↦ ?_, isSmooth_ofMulAction⟩
  convert h.isOpen_stabilizer (MonoidAlgebra.single x (1 : A)) using 2
  ext g
  simp [ofMulAction_single, MonoidAlgebra.single_left_inj]

/-- The permutation representation `A[G ⧸ U]` on the cosets of an open subgroup is smooth: the
stabilizer of the coset `g U` is the open subgroup `g U g⁻¹`. -/
instance isSmooth_ofMulAction_quotient [SeparatelyContinuousMul G] (U : OpenSubgroup G) :
    IsSmooth (ofMulAction A G (G ⧸ (U : Subgroup G))) :=
  isSmooth_ofMulAction fun x ↦ by
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    have hg : ((g : G ⧸ (U : Subgroup G))) = g • ((1 : G) : G ⧸ (U : Subgroup G)) := by simp
    rw [hg, MulAction.stabilizer_smul_eq_stabilizer_map_conj, MulAction.stabilizer_quotient,
      Subgroup.coe_map]
    exact (Homeomorph.mulLeft g |>.trans (Homeomorph.mulRight g⁻¹)).isOpenMap _ U.isOpen

end IsSmooth

section SmoothVectors

variable {A G V : Type*} [Semiring A] [Group G] [TopologicalSpace G] [SeparatelyContinuousMul G]
  [AddCommMonoid V] [Module A V] {ρ : Representation A G V}

/-- A vector has open stabilizer exactly when each of its translates does: the stabilizer of
`ρ g v` is the conjugate `g (ρ.stabilizer v) g⁻¹`. -/
theorem isOpen_stabilizer_apply_iff (g : G) {v : V} :
    IsOpen (ρ.stabilizer (ρ g v) : Set G) ↔ IsOpen (ρ.stabilizer v : Set G) := by
  have key : ∀ (g : G) (v : V), IsOpen (ρ.stabilizer v : Set G) →
      IsOpen (ρ.stabilizer (ρ g v) : Set G) := fun g v hv ↦ by
    rw [stabilizer_conj, Subgroup.coe_map]
    exact (Homeomorph.mulLeft g |>.trans (Homeomorph.mulRight g⁻¹)).isOpenMap _ hv
  exact ⟨fun h ↦ by simpa using key g⁻¹ _ h, key g v⟩

variable (ρ) in
/-- The **smooth vectors** `V^∞` of a representation of a group with separately continuous
multiplication (for instance a topological group): the vectors whose stabilizer is open. They
form a subrepresentation, the largest smooth one (`Representation.le_smoothVectors_iff`). -/
def smoothVectors : Subrepresentation ρ where
  toSubmodule :=
    { carrier := {v | IsOpen (ρ.stabilizer v : Set G)}
      add_mem' {v w} hv hw := Subgroup.isOpen_mono (le_stabilizer_add ρ v w) <| by
        rw [Subgroup.coe_inf]
        exact hv.inter hw
      zero_mem' := by simp [stabilizer_zero]
      smul_mem' c v hv := Subgroup.isOpen_mono (le_stabilizer_smul ρ c v) hv }
  apply_mem_toSubmodule g _ hv := (isOpen_stabilizer_apply_iff g).mpr hv

@[simp]
theorem mem_smoothVectors {v : V} : v ∈ ρ.smoothVectors ↔ IsOpen (ρ.stabilizer v : Set G) :=
  Iff.rfl

/-- **The smooth vectors are the largest smooth subrepresentation.** A subrepresentation is
contained in `V^∞` exactly when the representation it carries is smooth. -/
theorem le_smoothVectors_iff {σ : Subrepresentation ρ} :
    σ ≤ ρ.smoothVectors ↔ IsSmooth σ.toRepresentation := by
  simp only [IsConcreteLE.le_iff, mem_smoothVectors, isSmooth_iff, Subtype.forall,
    ← σ.subtype.stabilizer_apply_of_injective σ.subtype_injective, Subrepresentation.coe_subtype,
    Subrepresentation.mem_toSubmodule]

/-- The representation on the smooth vectors is smooth. -/
instance isSmooth_smoothVectors : IsSmooth ρ.smoothVectors.toRepresentation :=
  le_smoothVectors_iff.mp le_rfl

/-- A representation is smooth exactly when all of its vectors are smooth. -/
theorem smoothVectors_eq_top_iff : ρ.smoothVectors = ⊤ ↔ IsSmooth ρ := by
  rw [eq_top_iff, isSmooth_iff]
  exact ⟨fun h v ↦ h (Set.mem_univ v), fun h v _ ↦ h v⟩

@[simp]
theorem smoothVectors_eq_top [IsSmooth ρ] : ρ.smoothVectors = ⊤ :=
  smoothVectors_eq_top_iff.mpr ‹_›

/-- Intertwining maps send smooth vectors to smooth vectors: the stabilizer of `f v` contains the
stabilizer of `v`. -/
theorem IntertwiningMap.apply_mem_smoothVectors {W : Type*} [AddCommMonoid W] [Module A W]
    {σ : Representation A G W} (f : IntertwiningMap ρ σ) {v : V} (hv : v ∈ ρ.smoothVectors) :
    f v ∈ σ.smoothVectors :=
  Subgroup.isOpen_mono (f.stabilizer_le v) hv

end SmoothVectors

end Representation

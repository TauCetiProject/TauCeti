/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.OpenSubgroup
public import TauCeti.RepresentationTheory.Intertwining
public import TauCeti.RepresentationTheory.Subrepresentation
import TauCeti.Topology.Algebra.Group.Subgroup

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
  particular subrepresentations and quotients of smooth representations are smooth, and
  equivalent representations are smooth together (`Representation.Equiv.isSmooth_iff`).
* `Representation.isSmooth_ofMulAction_iff`: a permutation representation `A[X]` over a nonzero
  ring is smooth exactly when the point stabilizers of `X` are open; in particular `A[G ⧸ U]` is
  smooth for an open subgroup `U`.
* `Representation.smoothVectors_eq_top_iff`: a representation is smooth exactly when all of its
  vectors are smooth.
* `Representation.le_smoothVectors_iff`: the smooth vectors form the largest smooth
  subrepresentation.
* `Representation.smoothVectors_leftRegular_eq_bot`: in a `T₁` group in which `{1}` is not open,
  the left regular representation has no nonzero smooth vector.

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
  /-- The stabilizer of every vector is open. Use `Representation.isOpen_stabilizer` instead. -/
  out (v : V) : IsOpen (ρ.stabilizer v : Set G)

/-- In a smooth representation the stabilizer of every vector is open. -/
theorem isOpen_stabilizer (ρ : Representation A G V) [IsSmooth ρ] (v : V) :
    IsOpen (ρ.stabilizer v : Set G) :=
  IsSmooth.out v

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
  ⟨⟨ρ.stabilizer v, ρ.isOpen_stabilizer v⟩, fun _ hg ↦ hg⟩

/-- A trivial representation, for instance `Representation.trivial`, is smooth: every stabilizer
is the whole group. -/
instance isSmooth_of_isTrivial (ρ : Representation A G V) [ρ.IsTrivial] : IsSmooth ρ :=
  ⟨fun v ↦ by
    convert isOpen_univ
    ext g
    simp [isTrivial_apply]⟩

/-- A representation on a space with at most one vector is smooth. -/
instance isSmooth_of_subsingleton [Subsingleton V] (ρ : Representation A G V) : IsSmooth ρ :=
  ⟨fun v ↦ by
    convert isOpen_univ
    ext g
    simp [Subsingleton.elim (ρ g v) v]⟩

/-- Every representation of a discrete group is smooth. -/
instance isSmooth_of_discreteTopology [DiscreteTopology G] (ρ : Representation A G V) :
    IsSmooth ρ :=
  ⟨fun _ ↦ isOpen_discrete _⟩

/-- **Restriction preserves smoothness.** The restriction of a smooth representation along a
continuous homomorphism, for instance to a subgroup, is smooth: its stabilizers are the preimages
of those of `ρ` (`Representation.stabilizer_comp`). -/
theorem IsSmooth.comp {H : Type*} [Group H] [TopologicalSpace H] (ρ : Representation A G V)
    [IsSmooth ρ] {f : H →* G} (hf : Continuous f) : IsSmooth (ρ.comp f) :=
  ⟨fun v ↦ by
    rw [stabilizer_comp, Subgroup.coe_comap]
    exact (ρ.isOpen_stabilizer v).preimage hf⟩

/-- **Subobjects of smooth representations are smooth.** Smoothness passes to the source of an
injective intertwining map, which has the same stabilizers. -/
theorem IsSmooth.of_injective {ρ : Representation A G V} {σ : Representation A G W} [IsSmooth σ]
    (f : IntertwiningMap ρ σ) (hf : Injective f) : IsSmooth ρ :=
  ⟨fun v ↦ f.stabilizer_apply_of_injective hf v ▸ σ.isOpen_stabilizer (f v)⟩

/-- **Quotients of smooth representations are smooth.** Smoothness passes to the target of a
surjective intertwining map, since the stabilizer of `f v` contains that of `v`. -/
theorem IsSmooth.of_surjective [SeparatelyContinuousMul G] {ρ : Representation A G V}
    {σ : Representation A G W} [IsSmooth ρ] (f : IntertwiningMap ρ σ) (hf : Surjective f) :
    IsSmooth σ :=
  ⟨fun w ↦ by
    obtain ⟨v, rfl⟩ := hf w
    exact Subgroup.isOpen_mono (f.stabilizer_le v) (ρ.isOpen_stabilizer v)⟩

/-- Equivalent representations are smooth together, since an equivalence preserves stabilizers. -/
theorem Equiv.isSmooth_iff {ρ : Representation A G V} {σ : Representation A G W}
    (e : Equiv ρ σ) : IsSmooth ρ ↔ IsSmooth σ := by
  refine ⟨fun _ ↦ ⟨fun w ↦ ?_⟩, fun _ ↦ ⟨fun v ↦ ?_⟩⟩
  · rw [← e.apply_symm_apply w, e.stabilizer_apply]
    exact ρ.isOpen_stabilizer _
  · rw [← e.stabilizer_apply]
    exact σ.isOpen_stabilizer _

/-- A subrepresentation of a smooth representation is smooth. -/
instance _root_.Subrepresentation.isSmooth_toRepresentation {ρ : Representation A G V} [IsSmooth ρ]
    (σ : Subrepresentation ρ) : IsSmooth σ.toRepresentation :=
  IsSmooth.of_injective σ.subtype σ.subtype_injective

/-- The restriction of a smooth representation to an invariant submodule is smooth. -/
instance isSmooth_subrepresentation (ρ : Representation A G V) [IsSmooth ρ] (W : Submodule A V)
    (le_comap : ∀ g, W ≤ W.comap (ρ g)) : IsSmooth (ρ.subrepresentation W le_comap) :=
  ⟨fun w ↦ by
    convert ρ.isOpen_stabilizer (w : V) using 2
    ext g
    simp [Subtype.ext_iff]⟩

/-- The quotient of a smooth representation by an invariant submodule is smooth. -/
instance isSmooth_quotient [SeparatelyContinuousMul G] {A V : Type*} [Ring A] [AddCommGroup V]
    [Module A V] (ρ : Representation A G V) [IsSmooth ρ] (W : Submodule A V)
    (le_comap : ∀ g, W ≤ W.comap (ρ g)) : IsSmooth (ρ.quotient W le_comap) :=
  ⟨fun x ↦ by
    obtain ⟨v, rfl⟩ := W.mkQ_surjective x
    exact Subgroup.isOpen_mono (fun g hg ↦ by simp_all) (ρ.isOpen_stabilizer v)⟩

/-- The quotient of a smooth representation by a subrepresentation is smooth. -/
instance _root_.Subrepresentation.isSmooth_quotient [SeparatelyContinuousMul G] {A V : Type*}
    [Ring A] [AddCommGroup V] [Module A V] {ρ : Representation A G V} [IsSmooth ρ]
    (σ : Subrepresentation ρ) : IsSmooth σ.quotient :=
  Representation.isSmooth_quotient ρ _ _

end IsSmooth

section SmoothVectors

variable {A G V : Type*} [Semiring A] [Group G] [TopologicalSpace G] [SeparatelyContinuousMul G]
  [AddCommMonoid V] [Module A V] {ρ : Representation A G V}

/-- A vector has open stabilizer exactly when each of its translates does: the stabilizer of
`ρ g v` is the conjugate `g (ρ.stabilizer v) g⁻¹`. -/
@[simp, grind =]
theorem isOpen_stabilizer_apply_iff (g : G) {v : V} :
    IsOpen (ρ.stabilizer (ρ g v) : Set G) ↔ IsOpen (ρ.stabilizer v : Set G) := by
  rw [stabilizer_conj, Subgroup.isOpen_map_conj_iff]

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

@[simp, grind =]
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
  simp [eq_top_iff, IsConcreteLE.le_iff, isSmooth_iff]

@[simp, grind =]
theorem smoothVectors_eq_top [IsSmooth ρ] : ρ.smoothVectors = ⊤ :=
  smoothVectors_eq_top_iff.mpr ‹_›

/-- Intertwining maps send smooth vectors to smooth vectors: the stabilizer of `f v` contains the
stabilizer of `v`. -/
theorem IntertwiningMap.apply_mem_smoothVectors {W : Type*} [AddCommMonoid W] [Module A W]
    {σ : Representation A G W} (f : IntertwiningMap ρ σ) {v : V} (hv : v ∈ ρ.smoothVectors) :
    f v ∈ σ.smoothVectors :=
  Subgroup.isOpen_mono (f.stabilizer_le v) hv

end SmoothVectors

section OfMulAction

variable {A G : Type*} [Semiring A] [Group G] [TopologicalSpace G] [SeparatelyContinuousMul G]

/-- A permutation representation `A[X]` is smooth when every point of `X` has an open stabilizer:
the stabilizer of the basis vector at `x` contains the stabilizer of `x`, and the smooth vectors
are closed under sums. -/
theorem isSmooth_ofMulAction {X : Type*} [MulAction G X]
    (h : ∀ x : X, IsOpen (MulAction.stabilizer G x : Set G)) : IsSmooth (ofMulAction A G X) := by
  refine smoothVectors_eq_top_iff.mp <| eq_top_iff.mpr fun f hf ↦ ?_
  clear hf
  rw [← Subrepresentation.mem_toSubmodule]
  induction f using MonoidAlgebra.induction_linear with
  | zero => exact zero_mem _
  | add f₁ f₂ h₁ h₂ => exact add_mem h₁ h₂
  | single x a =>
    refine Subgroup.isOpen_mono (fun g hg ↦ ?_) (h x)
    rw [MulAction.mem_stabilizer_iff] at hg
    rw [mem_stabilizer, ofMulAction_single, hg]

/-- **Smooth permutation representations.** Over a nonzero ring, the permutation representation
`A[X]` is smooth exactly when every point of `X` has an open stabilizer: the stabilizer of the
basis vector at `x` is the stabilizer of `x`. -/
theorem isSmooth_ofMulAction_iff [Nontrivial A] {X : Type*} [MulAction G X] :
    IsSmooth (ofMulAction A G X) ↔ ∀ x : X, IsOpen (MulAction.stabilizer G x : Set G) := by
  refine ⟨fun h x ↦ ?_, isSmooth_ofMulAction⟩
  convert (ofMulAction A G X).isOpen_stabilizer (MonoidAlgebra.single x (1 : A)) using 2
  ext g
  simp [ofMulAction_single, MonoidAlgebra.single_left_inj]

/-- The permutation representation `A[G ⧸ U]` on the cosets of an open subgroup is smooth: the
stabilizer of the coset `g U` is the open subgroup `g U g⁻¹`. -/
instance isSmooth_ofMulAction_quotient (U : OpenSubgroup G) :
    IsSmooth (ofMulAction A G (G ⧸ (U : Subgroup G))) :=
  isSmooth_ofMulAction fun x ↦ by
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    have hg : ((g : G ⧸ (U : Subgroup G))) = g • ((1 : G) : G ⧸ (U : Subgroup G)) := by simp
    rw [hg, MulAction.stabilizer_smul_eq_stabilizer_map_conj, MulAction.stabilizer_quotient,
      MulEquiv.toMonoidHom_eq_coe, Subgroup.isOpen_map_conj_iff]
    exact U.isOpen

/-- In a `T₁` group in which `{1}` is not open, the left regular representation has no
nonzero smooth vector: the open stabilizer of a vector `f` would act freely on the finite support
of `f`, so it would be a finite open subgroup, and `{1}` would be open. -/
theorem smoothVectors_leftRegular_eq_bot [T1Space G] (hG : ¬IsOpen ({1} : Set G)) :
    (leftRegular A G).smoothVectors = ⊥ := by
  refine eq_bot_iff.mpr fun f hf ↦ ?_
  rw [Subrepresentation.mem_bot]
  by_contra hf0
  obtain ⟨x, hx⟩ : f.coeff.support.Nonempty := by
    rwa [Finsupp.support_nonempty_iff, Ne, MonoidAlgebra.coeff_eq_zero]
  set H : Set G := ((leftRegular A G).stabilizer f : Set G)
  have hH : IsOpen H := mem_smoothVectors.mp hf
  -- Each `h ∈ H` fixes `f`, so it moves the point `x` of the support to `h * x` in the support.
  have hfin : H.Finite := by
    refine Set.Finite.of_finite_image (f := (· * x)) ?_ (mul_left_injective x).injOn
    refine f.coeff.support.finite_toSet.subset ?_
    rintro _ ⟨h, hh, rfl⟩
    have hfix : leftRegular A G h f = f := hh
    rw [Finset.mem_coe, Finsupp.mem_support_iff, ← hfix, coeff_ofMulAction, smul_eq_mul,
      inv_mul_cancel_left]
    exact Finsupp.mem_support_iff.mp hx
  exact hG (isOpen_singleton_of_finite_mem_nhds 1 (hH.mem_nhds (one_mem _)) hfin)

end OfMulAction

end Representation

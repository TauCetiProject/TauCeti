/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.LinearTopology
public import Mathlib.Topology.Algebra.Nonarchimedean.Basic
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Topology.Algebra.TopologicallyNilpotent

/-!
# Bounded subsets of topological rings and modules

A subset `S` of a topological monoid with zero is *bounded* when every neighbourhood `U` of zero
absorbs `S`: there is a neighbourhood `V` of zero with `V * S ⊆ U`. This is the notion of
boundedness underlying Huber's theory of adic spaces (Wedhorn, *Adic Spaces*, Definition 5.27),
where it is the condition cutting out the rings of definition of a Huber ring.

The same condition makes sense for a subset `S` of a topological `R`-module `M`: every
neighbourhood `U` of zero in `M` contains `V • S` for some neighbourhood `V` of zero in `R`.
Boundedness in a ring is the case of the ring acting on itself (`isModuleBounded_self_iff`), and
the elementary calculus is proved once, for modules. In a topological `R`-algebra, a bounded subset
is bounded for the `R`-module structure as soon as the structure map is continuous at zero
(`IsBounded.isModuleBounded`).

Unlike ring boundedness, module boundedness is preserved by every linear map continuous at zero
(`IsModuleBounded.image`), because the neighbourhood of zero in the scalars does not have to be
transported along the map.

## Provenance

`IsBounded` and the elementary calculus — `IsBounded.subset`, `isBounded_empty`,
`isBounded_singleton_zero`, `isBounded_pair_zero_one`, `IsBounded.union`, `IsBounded.mul`,
`isBounded_singleton` and `isBounded_finite` — follow William Coram's mathlib4#40013, as do
several of their proofs; the proofs of the module versions adapt them. Everything else here is
new: the finite unions `isBounded_iUnion`, the nonarchimedean `IsBounded.addSubgroupClosure`,
`IsBounded.add` and `isBounded_sup`, the image, transport and product lemmas, and the module
notion `IsModuleBounded` with its calculus. The selection and ordering of the ring results follows
AINTLIB's `Bounded.lean`; its proofs were not used.

## Main definitions

* `TauCeti.Huber.IsBounded`: `S` is bounded, i.e. every neighbourhood of zero absorbs `S`.
* `TauCeti.Huber.IsModuleBounded`: `S` is a bounded subset of a topological module.

## Main results

* `TauCeti.Huber.isBounded_iff`: unfolding lemma for `IsBounded`.
* `TauCeti.Huber.isBounded_finsetProd`: a finite pointwise product of bounded sets is bounded.
* `TauCeti.Huber.isBounded_finite`: finite sets are bounded.
* `TauCeti.Huber.isBounded_of_isLinearTopology`: in a linearly topologized commutative ring, such
  as an adic ring, every subset is bounded.
* `TauCeti.Huber.IsBounded.union`, `TauCeti.Huber.IsBounded.mul`: unions and pointwise products
  of bounded sets are bounded.
* `TauCeti.Huber.IsBounded.add`, `TauCeti.Huber.IsBounded.addSubgroupClosure`: over a ring with a
  nonarchimedean additive group, sums and the generated additive subgroup of bounded sets stay
  bounded.
* `TauCeti.Huber.isBounded_sup`: the join of two bounded subrings of a commutative ring is
  bounded — the boundedness input for joins of rings of definition.
* `TauCeti.Huber.IsBounded.image`: a morphism continuous at zero which is open at zero preserves
  boundedness, and `TauCeti.Huber.isBounded_image_ringEquiv_iff` transports boundedness along a
  topological ring isomorphism.
* `TauCeti.Huber.isBounded_prod_iff`: a subset of a product of two topological rings, or more
  generally monoids with zero, is bounded exactly when both of its projections are.
* `TauCeti.Huber.IsModuleBounded.image`: linear maps continuous at zero, in particular continuous
  linear maps, send bounded subsets of modules to bounded subsets.
* `TauCeti.Huber.isModuleBounded_prod_iff`: a subset of a product of two modules is bounded
  exactly when both of its projections are.
* `TauCeti.Huber.IsModuleBounded.smul`: a bounded set of scalars times a bounded subset of a
  module is bounded.

## Implementation notes

This is not Mathlib's `Bornology.IsVonNBounded`. That predicate asks that every neighbourhood of
zero *absorb* `S` after dilation by a norm-large scalar, so it needs a `SeminormedRing` of scalars
to have a bornology to be cofinal in; a Huber ring such as `ℤ_[p]⟦T⟧` with its `(p, T)`-adic
topology carries no such norm. The two notions agree over a nontrivially normed field acting on
itself, but neither the statement shape (`∃ V ∈ 𝓝 0, V * S ⊆ U` against
`∀ᶠ a in cobounded, S ⊆ a • U`) nor the hypotheses transfer. The same holds for
`IsModuleBounded` against `Bornology.IsVonNBounded` over a normed ring of scalars.

Boundedness is *not* preserved by an arbitrary continuous homomorphism: giving `ℚ_[p]` the
discrete topology makes every subset bounded, while the identity to the `p`-adic topology is
continuous and `ℚ_[p]` is not bounded in itself. `IsBounded.image` therefore carries the extra
hypothesis that the morphism maps neighbourhoods of zero to neighbourhoods of zero.

## References

* [Wedhorn, *Adic Spaces*][wedhorn_adic], Definition 5.27 and Remark 5.28.
* William Coram, *feat: define bounded sets and power bounded elements*,
  [mathlib4#40013](https://github.com/leanprover-community/mathlib4/pull/40013).
* [AINTLIB](https://github.com/CBirkbeck/AINTLIB), branch `dev/adic-spaces`,
  `projects/AdicSpaces/Adic spaces/Bounded.lean`.

-/

public section

open Filter Pointwise Topology

namespace TauCeti.Huber

section Module

variable {R M N : Type*} [TopologicalSpace R] [TopologicalSpace M] [TopologicalSpace N]

section SMul

variable [Zero R] [Zero M] [SMul R M]

variable (R) in
/-- A subset `S` of a topological `R`-module `M` is *bounded* if for every neighbourhood `U` of `0`
in `M` there is a neighbourhood `V` of `0` in `R` with `V • S ⊆ U`.

Only the scalar action is used, so this applies to any topological space with zero carrying an
action of a topological space with zero. -/
def IsModuleBounded (S : Set M) : Prop := ∀ U ∈ 𝓝 (0 : M), ∃ V ∈ 𝓝 (0 : R), V • S ⊆ U

/-- Unfolding lemma for `TauCeti.Huber.IsModuleBounded`. -/
theorem isModuleBounded_iff {S : Set M} :
    IsModuleBounded R S ↔ ∀ U ∈ 𝓝 (0 : M), ∃ V ∈ 𝓝 (0 : R), V • S ⊆ U := (Iff.rfl)

/-- Subsets of bounded sets are bounded. -/
theorem IsModuleBounded.subset {S T : Set M} (hS : IsModuleBounded R S) (hTS : T ⊆ S) :
    IsModuleBounded R T :=
  fun U hU ↦
    let ⟨V, hV, hVS⟩ := hS U hU
    ⟨V, hV, (Set.smul_subset_smul_left hTS).trans hVS⟩

variable (R) in
/-- The empty set is bounded. -/
@[simp]
theorem isModuleBounded_empty : IsModuleBounded R (∅ : Set M) :=
  fun _ _ ↦ ⟨Set.univ, univ_mem, by simp⟩

/-- A finite union of bounded sets is bounded. -/
theorem isModuleBounded_iUnion {ι : Sort*} [Finite ι] {S : ι → Set M}
    (hS : ∀ i, IsModuleBounded R (S i)) : IsModuleBounded R (⋃ i, S i) := by
  intro U hU
  choose V hV hVS using fun i ↦ hS i U hU
  refine ⟨⋂ i, V i, Filter.iInter_mem.mpr hV, ?_⟩
  rw [Set.smul_iUnion]
  exact Set.iUnion_subset fun i ↦
    (Set.smul_subset_smul_right (Set.iInter_subset _ i)).trans (hVS i)

/-- A finite indexed union is bounded exactly when every piece is. -/
@[simp]
theorem isModuleBounded_iUnion_iff {ι : Sort*} [Finite ι] {S : ι → Set M} :
    IsModuleBounded R (⋃ i, S i) ↔ ∀ i, IsModuleBounded R (S i) :=
  ⟨fun h i ↦ h.subset (Set.subset_iUnion _ i), isModuleBounded_iUnion⟩

/-- The union of two bounded sets is bounded. -/
theorem IsModuleBounded.union {S T : Set M} (hS : IsModuleBounded R S)
    (hT : IsModuleBounded R T) : IsModuleBounded R (S ∪ T) := by
  rw [Set.union_eq_iUnion]
  exact isModuleBounded_iUnion (by rintro (_ | _) <;> assumption)

/-- A union is bounded exactly when both parts are. -/
@[simp]
theorem isModuleBounded_union {S T : Set M} :
    IsModuleBounded R (S ∪ T) ↔ IsModuleBounded R S ∧ IsModuleBounded R T :=
  ⟨fun h ↦ ⟨h.subset Set.subset_union_left, h.subset Set.subset_union_right⟩,
    fun h ↦ h.1.union h.2⟩

/-- **Images of bounded sets under linear maps continuous at zero are bounded.** This covers
continuous linear maps. Unlike `TauCeti.Huber.IsBounded.image` for ring homomorphisms, no
openness is needed: the neighbourhood of zero in the scalars is not transported. -/
theorem IsModuleBounded.image [Zero N] [SMul R N] {F : Type*} [FunLike F M N]
    [ZeroHomClass F M N] [MulActionHomClass F R M N] {f : F} (hf : ContinuousAt f 0)
    {S : Set M} (hS : IsModuleBounded R S) : IsModuleBounded R (f '' S) := by
  intro U hU
  obtain ⟨V, hV, hVS⟩ := hS (f ⁻¹' U) (hf.preimage_mem_nhds (by rwa [map_zero]))
  refine ⟨V, hV, ?_⟩
  rintro _ ⟨v, hv, _, ⟨s, hs, rfl⟩, rfl⟩
  simpa [map_smul] using hVS (Set.smul_mem_smul hv hs)

/-- A subset of a product of two modules is bounded exactly when both of its projections are. -/
theorem isModuleBounded_prod_iff [Zero N] [SMul R N] {S : Set (M × N)} :
    IsModuleBounded R S ↔
      IsModuleBounded R (Prod.fst '' S) ∧ IsModuleBounded R (Prod.snd '' S) := by
  refine ⟨fun hS ↦ ⟨fun U hU ↦ ?_, fun U hU ↦ ?_⟩, fun ⟨h₁, h₂⟩ U hU ↦ ?_⟩
  · obtain ⟨V, hV, hVS⟩ := hS (U ×ˢ Set.univ) (prod_mem_nhds hU univ_mem)
    refine ⟨V, hV, ?_⟩
    rintro _ ⟨v, hv, _, ⟨s, hs, rfl⟩, rfl⟩
    exact (hVS (Set.smul_mem_smul hv hs)).1
  · obtain ⟨V, hV, hVS⟩ := hS (Set.univ ×ˢ U) (prod_mem_nhds univ_mem hU)
    refine ⟨V, hV, ?_⟩
    rintro _ ⟨v, hv, _, ⟨s, hs, rfl⟩, rfl⟩
    exact (hVS (Set.smul_mem_smul hv hs)).2
  · obtain ⟨U₁, hU₁, U₂, hU₂, hU⟩ := mem_nhds_prod_iff.mp hU
    obtain ⟨V₁, hV₁, hVS₁⟩ := h₁ U₁ hU₁
    obtain ⟨V₂, hV₂, hVS₂⟩ := h₂ U₂ hU₂
    refine ⟨V₁ ∩ V₂, inter_mem hV₁ hV₂, ?_⟩
    rintro _ ⟨v, hv, s, hs, rfl⟩
    exact hU ⟨hVS₁ (Set.smul_mem_smul hv.1 ⟨s, hs, rfl⟩),
      hVS₂ (Set.smul_mem_smul hv.2 ⟨s, hs, rfl⟩)⟩

/-- The product of two bounded sets is bounded. -/
theorem IsModuleBounded.prod [Zero N] [SMul R N] {S : Set M} {T : Set N}
    (hS : IsModuleBounded R S) (hT : IsModuleBounded R T) : IsModuleBounded R (S ×ˢ T) :=
  isModuleBounded_prod_iff.mpr ⟨hS.subset (Set.fst_image_prod_subset S T),
    hT.subset (Set.snd_image_prod_subset S T)⟩

end SMul

section SMulZeroClass

variable [Zero R] [Zero M] [SMulZeroClass R M]

variable (R) in
/-- The singleton `{0}` is bounded. -/
@[simp]
theorem isModuleBounded_singleton_zero : IsModuleBounded R ({0} : Set M) :=
  fun U hU ↦ ⟨Set.univ, univ_mem, fun _ hx ↦ by simp_all [mem_of_mem_nhds hU]⟩

end SMulZeroClass

section ContinuousSMul

variable [Zero R] [Zero M] [SMulWithZero R M] [ContinuousSMul R M]

variable (R) in
/-- Every singleton is bounded. -/
@[simp]
theorem isModuleBounded_singleton (m : M) : IsModuleBounded R ({m} : Set M) :=
  fun U hU ↦ ⟨(· • m) ⁻¹' U, (continuous_id.smul continuous_const).continuousAt.preimage_mem_nhds
    (by simp [hU]), by simp⟩

variable (R) in
/-- Every finite subset is bounded. -/
theorem isModuleBounded_finite {S : Set M} (hS : S.Finite) : IsModuleBounded R S := by
  refine Set.Finite.induction_on S hS (isModuleBounded_empty R) fun {m s} _ _ ih ↦ ?_
  exact Set.insert_eq m s ▸ (isModuleBounded_singleton R m).union ih

end ContinuousSMul

section Nonarchimedean

variable [Zero R] [AddGroup M] [NonarchimedeanAddGroup M] [DistribSMul R M]

/-- The additive subgroup generated by a bounded subset of a module with a nonarchimedean
additive group is bounded. -/
theorem IsModuleBounded.addSubgroupClosure {S : Set M} (hS : IsModuleBounded R S) :
    IsModuleBounded R (AddSubgroup.closure S : Set M) := by
  intro U hU
  obtain ⟨G, hGU⟩ := NonarchimedeanAddGroup.is_nonarchimedean U hU
  obtain ⟨V, hV, hVS⟩ := hS _ (G.isOpen.mem_nhds G.zero_mem)
  refine ⟨V, hV, ?_⟩
  rintro _ ⟨v, hv, x, hx, rfl⟩
  refine hGU (?_ : v • x ∈ (G : Set M))
  induction hx using AddSubgroup.closure_induction with
  | mem s hs => exact hVS (Set.smul_mem_smul hv hs)
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact G.toAddSubgroup.add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact G.toAddSubgroup.neg_mem hx

/-- The pointwise sum of two bounded subsets of a module with a nonarchimedean additive group is
bounded. -/
theorem IsModuleBounded.add {S T : Set M} (hS : IsModuleBounded R S)
    (hT : IsModuleBounded R T) : IsModuleBounded R (S + T) := by
  refine (hS.union hT).addSubgroupClosure.subset ?_
  rintro _ ⟨s, hs, t, ht, rfl⟩
  exact AddSubgroup.add_mem _ (AddSubgroup.subset_closure (.inl hs))
    (AddSubgroup.subset_closure (.inr ht))

end Nonarchimedean

end Module

section MonoidWithZero

variable {M : Type*} [MonoidWithZero M] [TopologicalSpace M]

/-- A subset `S` of a topological monoid with zero is *bounded* if for every neighbourhood `U`
of `0` there is a neighbourhood `V` of `0` with `V * S ⊆ U`. -/
def IsBounded (S : Set M) : Prop := ∀ U ∈ 𝓝 (0 : M), ∃ V ∈ 𝓝 (0 : M), V * S ⊆ U

/-- Unfolding lemma for `TauCeti.Huber.IsBounded`. -/
theorem isBounded_iff {S : Set M} :
    IsBounded S ↔ ∀ U ∈ 𝓝 (0 : M), ∃ V ∈ 𝓝 (0 : M), V * S ⊆ U := (Iff.rfl)

/-- Boundedness in a topological monoid with zero is boundedness for its action on itself. -/
@[simp]
theorem isModuleBounded_self_iff {S : Set M} : IsModuleBounded M S ↔ IsBounded S := by
  simp only [isModuleBounded_iff, isBounded_iff, smul_eq_mul]

/-- A bounded set of scalars times a bounded subset of a module is bounded. -/
theorem IsModuleBounded.smul {N : Type*} [TopologicalSpace N] [Zero N] [SMul M N]
    [IsScalarTower M M N] {S : Set M} {T : Set N} (hS : IsBounded S) (hT : IsModuleBounded M T) :
    IsModuleBounded M (S • T) := by
  intro U hU
  obtain ⟨W, hW, hWT⟩ := hT U hU
  obtain ⟨V, hV, hVS⟩ := hS W hW
  refine ⟨V, hV, ?_⟩
  rw [← smul_assoc, smul_eq_mul]
  exact (Set.smul_subset_smul_right hVS).trans hWT

/-- Some power of a topologically nilpotent element multiplies a bounded set into any
neighbourhood of zero. -/
theorem IsBounded.exists_pow_mul_subset {S U : Set M} {a : M} (hS : IsBounded S)
    (ha : IsTopologicallyNilpotent a) (hU : U ∈ 𝓝 (0 : M)) :
    ∃ n : ℕ, {a ^ n} * S ⊆ U := by
  obtain ⟨V, hV, hVS⟩ := hS U hU
  obtain ⟨n, hn⟩ := ha.exists_pow_mem_of_mem_nhds hV
  exact ⟨n, (Set.mul_subset_mul_right (Set.singleton_subset_iff.mpr hn)).trans hVS⟩

/-- Subsets of bounded sets are bounded. -/
theorem IsBounded.subset {S T : Set M} (hS : IsBounded S) (hTS : T ⊆ S) : IsBounded T :=
  isModuleBounded_self_iff.mp <| (isModuleBounded_self_iff.mpr hS).subset hTS

/-- The empty set is bounded. -/
@[simp]
theorem isBounded_empty : IsBounded (∅ : Set M) :=
  isModuleBounded_self_iff.mp (isModuleBounded_empty M)

/-- The singleton `{0}` is bounded. -/
@[simp]
theorem isBounded_singleton_zero : IsBounded ({0} : Set M) :=
  isModuleBounded_self_iff.mp (isModuleBounded_singleton_zero M)

/-- The pair `{0, 1}` is bounded. -/
@[simp]
theorem isBounded_pair_zero_one : IsBounded ({0, 1} : Set M) :=
  fun U hU ↦ ⟨U, hU, fun _ hx ↦ by
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hx
    rcases Set.mem_insert_iff.mp hb with rfl | hb
    · rw [mul_zero]; exact mem_of_mem_nhds hU
    · rwa [Set.mem_singleton_iff.mp hb, mul_one]⟩

/-- A finite union of bounded sets is bounded. -/
theorem isBounded_iUnion {ι : Sort*} [Finite ι] {S : ι → Set M} (hS : ∀ i, IsBounded (S i)) :
    IsBounded (⋃ i, S i) :=
  isModuleBounded_self_iff.mp <| isModuleBounded_iUnion fun i ↦ isModuleBounded_self_iff.mpr (hS i)

/-- A finite indexed union is bounded exactly when every piece is. -/
@[simp]
theorem isBounded_iUnion_iff {ι : Sort*} [Finite ι] {S : ι → Set M} :
    IsBounded (⋃ i, S i) ↔ ∀ i, IsBounded (S i) :=
  ⟨fun h i ↦ h.subset (Set.subset_iUnion _ i), isBounded_iUnion⟩

/-- The union of two bounded sets is bounded. -/
theorem IsBounded.union {S T : Set M} (hS : IsBounded S) (hT : IsBounded T) :
    IsBounded (S ∪ T) := by
  rw [Set.union_eq_iUnion]
  exact isBounded_iUnion (by rintro (_ | _) <;> assumption)

/-- A union is bounded exactly when both parts are. -/
@[simp]
theorem isBounded_union {S T : Set M} : IsBounded (S ∪ T) ↔ IsBounded S ∧ IsBounded T :=
  ⟨fun h ↦ ⟨h.subset Set.subset_union_left, h.subset Set.subset_union_right⟩,
    fun h ↦ h.1.union h.2⟩

/-- The pointwise product of two bounded sets is bounded. -/
theorem IsBounded.mul {S T : Set M} (hS : IsBounded S) (hT : IsBounded T) : IsBounded (S * T) := by
  rw [← smul_eq_mul, ← isModuleBounded_self_iff]
  exact (isModuleBounded_self_iff.mpr hT).smul hS

/-- Every subset of a discrete monoid with zero is bounded. -/
theorem isBounded_of_discreteTopology [DiscreteTopology M] (S : Set M) : IsBounded S :=
  fun U hU ↦ ⟨{0}, by simp, by
    rintro _ ⟨_, rfl, s, -, rfl⟩
    simpa using mem_of_mem_nhds hU⟩

section SeparatelyContinuousMul

variable [SeparatelyContinuousMul M]

/-- Every singleton is bounded. -/
@[simp]
theorem isBounded_singleton (a : M) : IsBounded ({a} : Set M) :=
  fun U hU ↦ ⟨(· * a) ⁻¹' U, (continuous_mul_const a).continuousAt.preimage_mem_nhds
    (by simp [hU]), by simp⟩

/-- Every finite subset is bounded. -/
theorem isBounded_finite {S : Set M} (hS : S.Finite) : IsBounded S := by
  refine Set.Finite.induction_on S hS isBounded_empty fun {a s} _ _ ih ↦ ?_
  exact Set.insert_eq a s ▸ (isBounded_singleton a).union ih

end SeparatelyContinuousMul

end MonoidWithZero

section CommMonoidWithZero

variable {M : Type*} [CommMonoidWithZero M] [TopologicalSpace M]

/-- **A finite pointwise product of bounded sets is bounded.** Commutativity is
what makes the `Finset` product of sets available in the first place, and no continuity is
required. -/
theorem isBounded_finsetProd {ι : Type*} (s : Finset ι) {S : ι → Set M}
    (hS : ∀ i ∈ s, IsBounded (S i)) : IsBounded (∏ i ∈ s, S i) :=
  s.prod_induction S IsBounded (fun _ _ ↦ IsBounded.mul)
    (isBounded_pair_zero_one.subset (by simp)) hS

end CommMonoidWithZero

section LinearTopology

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsLinearTopology A A]

/-- Every subset of a linearly topologized commutative ring is bounded: a neighbourhood of zero
contains an open ideal, which absorbs every subset. This covers the adic rings, such as `ℤ_[p]`
or `W(𝒪_F)` with its `(p, [ϖ])`-adic topology, and in particular the discrete rings. -/
theorem isBounded_of_isLinearTopology (S : Set A) : IsBounded S := fun U hU ↦ by
  obtain ⟨I, hI, hIU⟩ := (IsLinearTopology.hasBasis_ideal (R := A)).mem_iff.mp hU
  exact ⟨I, hI, by
    rintro _ ⟨i, hi, s, -, rfl⟩
    exact hIU (I.mul_mem_right s hi)⟩

end LinearTopology

section Nonarchimedean

variable {A : Type*} [Ring A] [TopologicalSpace A] [NonarchimedeanAddGroup A]

/-- The additive subgroup generated by a bounded set is bounded in a nonarchimedean ring
(the key step of Wedhorn, Proposition 5.30). -/
theorem IsBounded.addSubgroupClosure {S : Set A} (hS : IsBounded S) :
    IsBounded (AddSubgroup.closure S : Set A) :=
  isModuleBounded_self_iff.mp (isModuleBounded_self_iff.mpr hS).addSubgroupClosure

/-- The pointwise sum of two bounded sets is bounded in a nonarchimedean ring. -/
theorem IsBounded.add {S T : Set A} (hS : IsBounded S) (hT : IsBounded T) : IsBounded (S + T) :=
  isModuleBounded_self_iff.mp
    ((isModuleBounded_self_iff.mpr hS).add (isModuleBounded_self_iff.mpr hT))

/-- The join of two bounded subrings of a commutative ring is bounded. -/
theorem isBounded_sup {A : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanAddGroup A]
    (B₀ B₁ : Subring A) (hB₀ : IsBounded (B₀ : Set A)) (hB₁ : IsBounded (B₁ : Set A)) :
    IsBounded ((B₀ ⊔ B₁ : Subring A) : Set A) := by
  refine (hB₀.mul hB₁).addSubgroupClosure.subset fun x hx ↦ ?_
  have hmem : x ∈ Subring.closure ((B₀ : Set A) ∪ (B₁ : Set A)) := by
    simpa [Subring.closure_union] using hx
  have hcl : ∀ B : Subring A, Submonoid.closure (B : Set A) = B.toSubmonoid := fun B ↦ by
    rw [← Subring.coe_toSubmonoid]; exact Submonoid.closure_eq _
  rw [Subring.mem_closure_iff, Submonoid.closure_union, hcl, hcl] at hmem
  simpa [Submonoid.coe_sup] using hmem

end Nonarchimedean

section Image

variable {M N : Type*} [MonoidWithZero M] [MonoidWithZero N]
  [TopologicalSpace M] [TopologicalSpace N]

/-- A morphism continuous at zero which carries neighbourhoods of zero to neighbourhoods of zero
sends bounded sets to bounded sets.

Boundedness is a condition at zero only, so continuity away from zero is irrelevant; but
continuity at zero alone is not enough, since refining the topology on the source only creates
bounded sets. -/
theorem IsBounded.image {F : Type*} [FunLike F M N] [ZeroHomClass F M N] [MulHomClass F M N]
    {f : F}
    (hf : ContinuousAt f 0) (hf₀ : ∀ V ∈ 𝓝 (0 : M), f '' V ∈ 𝓝 (0 : N)) {S : Set M}
    (hS : IsBounded S) : IsBounded (f '' S) := by
  intro U hU
  obtain ⟨V, hV, hVS⟩ := hS (f ⁻¹' U) (hf.preimage_mem_nhds (by rwa [map_zero]))
  exact ⟨f '' V, hf₀ V hV, by
    rw [← Set.image_mul]
    exact (Set.image_mono hVS).trans (Set.image_preimage_subset f U)⟩

/-- An open morphism continuous at zero sends bounded sets to bounded sets. -/
theorem IsBounded.image_of_isOpenMap {F : Type*} [FunLike F M N] [ZeroHomClass F M N]
    [MulHomClass F M N] {f : F} (hf : ContinuousAt f 0) (hf₀ : IsOpenMap f) {S : Set M}
    (hS : IsBounded S) : IsBounded (f '' S) :=
  hS.image hf fun _ hV ↦ map_zero f ▸ hf₀.image_mem_nhds hV

end Image

section Prod

variable {M N : Type*} [MonoidWithZero M] [MonoidWithZero N]
  [TopologicalSpace M] [TopologicalSpace N]

/-- A subset of a product of two topological monoids with zero is bounded exactly when both of its
projections are. -/
theorem isBounded_prod_iff {S : Set (M × N)} :
    IsBounded S ↔ IsBounded (Prod.fst '' S) ∧ IsBounded (Prod.snd '' S) := by
  refine ⟨fun hS ↦ ⟨fun U hU ↦ ?_, fun U hU ↦ ?_⟩, fun ⟨h₁, h₂⟩ U hU ↦ ?_⟩
  · obtain ⟨V, hV, hVS⟩ := hS (U ×ˢ Set.univ) (prod_mem_nhds hU univ_mem)
    refine ⟨Prod.fst '' V, isOpenMap_fst.image_mem_nhds hV, ?_⟩
    rintro _ ⟨_, ⟨v, hv, rfl⟩, _, ⟨s, hs, rfl⟩, rfl⟩
    exact (hVS (Set.mul_mem_mul hv hs)).1
  · obtain ⟨V, hV, hVS⟩ := hS (Set.univ ×ˢ U) (prod_mem_nhds univ_mem hU)
    refine ⟨Prod.snd '' V, isOpenMap_snd.image_mem_nhds hV, ?_⟩
    rintro _ ⟨_, ⟨v, hv, rfl⟩, _, ⟨s, hs, rfl⟩, rfl⟩
    exact (hVS (Set.mul_mem_mul hv hs)).2
  · obtain ⟨U₁, hU₁, U₂, hU₂, hU⟩ := mem_nhds_prod_iff.mp hU
    obtain ⟨V₁, hV₁, hVS₁⟩ := h₁ U₁ hU₁
    obtain ⟨V₂, hV₂, hVS₂⟩ := h₂ U₂ hU₂
    refine ⟨V₁ ×ˢ V₂, prod_mem_nhds hV₁ hV₂, ?_⟩
    rintro _ ⟨v, hv, s, hs, rfl⟩
    exact hU ⟨hVS₁ (Set.mul_mem_mul hv.1 ⟨s, hs, rfl⟩),
      hVS₂ (Set.mul_mem_mul hv.2 ⟨s, hs, rfl⟩)⟩

/-- The product of two bounded sets is bounded in the product monoid. -/
theorem IsBounded.prod {S : Set M} {T : Set N} (hS : IsBounded S) (hT : IsBounded T) :
    IsBounded (S ×ˢ T) :=
  isBounded_prod_iff.mpr ⟨hS.subset (Set.fst_image_prod_subset S T),
    hT.subset (Set.snd_image_prod_subset S T)⟩

end Prod

section Algebra

variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
  [TopologicalSpace R] [TopologicalSpace A]

/-- In a topological `R`-algebra whose structure map is continuous at zero, a bounded subset is
bounded for the `R`-module structure. -/
theorem IsBounded.isModuleBounded (h : ContinuousAt (algebraMap R A) 0) {S : Set A}
    (hS : IsBounded S) : IsModuleBounded R S := by
  intro U hU
  obtain ⟨V, hV, hVS⟩ := hS U hU
  refine ⟨algebraMap R A ⁻¹' V, h.preimage_mem_nhds (by rwa [map_zero]),
    Set.smul_subset_iff.mpr fun r hr s hs ↦ ?_⟩
  rw [Algebra.smul_def]
  exact hVS (Set.mul_mem_mul hr hs)

end Algebra

section Transport

variable {A B : Type*} [Semiring A] [Semiring B] [TopologicalSpace A] [TopologicalSpace B]

/-- A topological ring isomorphism sends bounded sets to bounded sets. -/
theorem IsBounded.image_ringEquiv (e : A ≃+* B) (he : Continuous e) (he' : Continuous e.symm)
    {S : Set A} (hS : IsBounded S) : IsBounded (e '' S) :=
  hS.image_of_isOpenMap he.continuousAt (e.toEquiv.continuous_symm_iff.mp he')

/-- Boundedness transports along a topological ring isomorphism. -/
theorem isBounded_image_ringEquiv_iff (e : A ≃+* B) (he : Continuous e) (he' : Continuous e.symm)
    {S : Set A} : IsBounded (e '' S) ↔ IsBounded S :=
  ⟨fun h ↦ by simpa [Set.image_image] using h.image_ringEquiv e.symm he' (by simpa using he),
    fun h ↦ h.image_ringEquiv e he he'⟩

end Transport

end TauCeti.Huber

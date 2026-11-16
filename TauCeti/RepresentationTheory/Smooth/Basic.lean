/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.RepresentationTheory.Stabilizer
public import Mathlib.Topology.Algebra.OpenSubgroup
public import TauCeti.RepresentationTheory.Pi
public import TauCeti.RepresentationTheory.Subrepresentation
public import TauCeti.Topology.Algebra.Nonarchimedean.VanDantzig
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.LinearAlgebra.Span.Defs
import TauCeti.RepresentationTheory.Intertwining

/-!
# Smooth representations and smooth vectors

A linear representation `ρ : Representation k G V` of a topological group `G` on an untopologized
`k`-module `V` is *smooth* if every vector `v : V` has open stabilizer `ρ.stabilizer v` in `G`.
For any group with separately continuous multiplication this is equivalent to requiring every
vector to be fixed by some open subgroup of `G`, and by van Dantzig's theorem, for a locally
profinite (more generally, weakly locally compact zero-dimensional) topological group, to requiring
every vector to be fixed by some compact open subgroup — equivalently, `V = ⋃_K V^K` over compact
open subgroups `K`.

Inside an arbitrary representation `ρ` of a group with separately continuous multiplication, the
vectors with open stabilizer form a subrepresentation `ρ.smoothVectors` (the smooth part `V^∞`),
which is the largest smooth subrepresentation of `ρ`. Intertwining maps preserve smooth vectors
and induce maps on smooth parts, yielding the coreflection universal property: every intertwining
map from a smooth representation into `ρ` factors uniquely through `ρ.smoothVectors.subtype`.

We also record closure properties of smoothness (subrepresentations, quotients, injective and
surjective intertwiners, equivalences, restrictions along continuous homomorphisms, binary and
finite products, direct sums, tensor products), characterizations for permutation representations
and the left regular representation, and the non-smoothness of infinite products of coset
representations whose stabilizer intersection is not open.

## Main definitions

* `Representation.IsSmooth`: the proposition-valued typeclass asserting that every vector of `ρ`
  has open stabilizer in `G`.
* `Representation.stabilizerOpenSubgroup`: the stabilizer of a vector in a smooth representation,
  bundled as an `OpenSubgroup G`.
* `Representation.smoothVectors`: the subrepresentation of vectors with open stabilizer.
* `Representation.IntertwiningMap.liftSmoothVectors`: the unique factorization of an intertwining
  map from a smooth representation through `σ.smoothVectors`.
* `Representation.IntertwiningMap.restrictSmoothVectors`: the induced intertwining map between
  the smooth-vector subrepresentations.

## Main results

* `Representation.isSmooth_iff_exists_openSubgroup`: `ρ` is smooth iff every vector is fixed by an
  open subgroup.
* `Representation.isSmooth_iff_exists_isCompact_openSubgroup`: for a weakly locally compact
  zero-dimensional topological group, `ρ` is smooth iff every vector is fixed by a compact open
  subgroup.
* `Representation.isSmooth_iff_iSup_invariants_eq_top` and
  `Representation.isSmooth_iff_iSup_isCompact_invariants_eq_top`: smoothness as exhaustion by
  open-subgroup (resp. compact-open-subgroup) invariants.
* `Representation.IsSmooth.of_injective`, `Representation.IsSmooth.of_surjective`,
  `Representation.Equiv.isSmooth_iff`, `Representation.IsSmooth.subrepresentation`,
  `Subrepresentation.instIsSmooth`, `Representation.IsSmooth.quotient`,
  `Subrepresentation.instIsSmoothQuotient`, `Representation.IsSmooth.comp`,
  `Representation.IsSmooth.prod`, `Representation.IsSmooth.pi`,
  `Representation.IsSmooth.directSum`, `Representation.IsSmooth.tprod`: stability of smoothness
  under standard representation-theoretic constructions.
* `Representation.isTrivial_of_isSmooth_of_preconnectedSpace`: every smooth representation of a
  preconnected group with separately continuous multiplication is trivial.
* `Representation.isSmooth_ofMulAction_iff`, `Representation.isSmooth_ofMulAction_quotient_iff`,
  `Representation.isSmooth_leftRegular_iff`, `Representation.not_isSmooth_pi_ofMulAction_quotient`:
  smoothness criteria for permutation, coset, regular, and infinite-product representations.
* `Representation.mem_smoothVectors_iff`,
  `Representation.mem_smoothVectors_iff_exists_openSubgroup`,
  `Representation.mem_smoothVectors_iff_exists_isCompact_openSubgroup`,
  `Representation.smoothVectors_toSubmodule_eq_iSup`,
  `Representation.smoothVectors_toSubmodule_eq_iSup_isCompact`,
  `Representation.isSmooth_smoothVectors`, `Representation.smoothVectors_eq_top_iff`,
  `Representation.le_smoothVectors_iff`, `Representation.IntertwiningMap.eq_liftSmoothVectors_iff`,
  `Representation.smoothVectors_leftRegular_eq_bot`: characterizations, universal property, and
  computation of `smoothVectors`.

## References

* J. Bernstein, *Representations of `p`-adic groups*, lecture notes by K. E. Rumelhart, 1992,
  Ch. I, §1.1, Definition 2 and Proposition 1, p. 7.
* The typeclass-and-subrepresentation design follows Mathlib PR #41525
  (`Mathlib/RepresentationTheory/Smooth/Basic.lean`).
-/

public section

open Filter Topology

namespace Representation

section StabilizerLemmas

variable {k G V W : Type*} [Semiring k] [Group G]
  [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W]

/-- An injective intertwining map preserves vector stabilizers exactly. -/
theorem IntertwiningMap.stabilizer_eq_of_injective {ρ : Representation k G V}
    {σ : Representation k G W} (f : ρ.IntertwiningMap σ) (hf : Function.Injective f) (v : V) :
    ρ.stabilizer v = σ.stabilizer (f v) := by
  ext g
  simp only [mem_stabilizer, ← hf.eq_iff, IntertwiningMap.isIntertwining]

/-- The stabilizer of a vector in a restricted representation `ρ.comp f` is the preimage of its
stabilizer in `ρ`. -/
@[simp]
theorem stabilizer_comp {H : Type*} [Group H] (ρ : Representation k G V) (f : H →* G) (v : V) :
    stabilizer (ρ.comp f) v = (ρ.stabilizer v).comap f := by
  ext h
  simp [mem_stabilizer]

/-- The stabilizer of a pair in a binary product of representations is the intersection of the
stabilizers of its components. -/
@[simp]
theorem stabilizer_prod (ρ : Representation k G V) (σ : Representation k G W) (x : V × W) :
    (ρ.prod σ).stabilizer x = ρ.stabilizer x.1 ⊓ σ.stabilizer x.2 := by
  ext g
  simp [mem_stabilizer, Prod.ext_iff]

/-- The stabilizer of a family in a product of representations is the infimum of the stabilizers of
its components. -/
@[simp]
theorem stabilizer_pi {ι : Type*} {U : ι → Type*} [∀ i, AddCommMonoid (U i)]
    [∀ i, Module k (U i)] (ρ : ∀ i, Representation k G (U i)) (x : ∀ i, U i) :
    (Representation.pi ρ).stabilizer x = ⨅ i, (ρ i).stabilizer (x i) := by
  ext g
  simp [mem_stabilizer, funext_iff, Subgroup.mem_iInf]

/-- The stabilizer of a nonzero basis vector `single x c` in the permutation representation
`ofMulAction k G X` is the point stabilizer `MulAction.stabilizer G x`. -/
theorem stabilizer_ofMulAction_single {X : Type*} [MulAction G X] (x : X) {c : k} (hc : c ≠ 0) :
    (ofMulAction k G X).stabilizer (MonoidAlgebra.single x c) = MulAction.stabilizer G x := by
  ext g
  simp only [mem_stabilizer, ofMulAction_single, MulAction.mem_stabilizer_iff]
  constructor
  · intro h
    have hcoeff := congrArg (fun a : MonoidAlgebra k X ↦ a.coeff (g • x)) h
    simp only [MonoidAlgebra.coeff_single] at hcoeff
    by_contra hne
    rw [Finsupp.single_eq_same, Finsupp.single_eq_of_ne hne] at hcoeff
    exact hc hcoeff
  · intro h
    rw [h]

end StabilizerLemmas

section IsSmooth

variable {k G V W : Type*} [Semiring k] [Group G] [TopologicalSpace G]
  [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W]

/-- A representation `ρ` of a topological group `G` on an untopologized `k`-module `V` is *smooth*
if every vector has open stabilizer in `G`. -/
class IsSmooth (ρ : Representation k G V) : Prop where
  isOpen_stabilizer : ∀ v : V, IsOpen (ρ.stabilizer v : Set G)

/-- A representation is smooth iff every vector has open stabilizer. -/
theorem isSmooth_iff (ρ : Representation k G V) :
    ρ.IsSmooth ↔ ∀ v : V, IsOpen (ρ.stabilizer v : Set G) :=
  ⟨fun h ↦ h.isOpen_stabilizer, fun h ↦ ⟨h⟩⟩

/-- The stabilizer of a vector in a smooth representation, bundled as an `OpenSubgroup G`. -/
def stabilizerOpenSubgroup (ρ : Representation k G V) [ρ.IsSmooth] (v : V) : OpenSubgroup G :=
  ⟨ρ.stabilizer v, IsSmooth.isOpen_stabilizer v⟩

@[simp]
theorem toSubgroup_stabilizerOpenSubgroup (ρ : Representation k G V) [ρ.IsSmooth] (v : V) :
    (ρ.stabilizerOpenSubgroup v).toSubgroup = ρ.stabilizer v := (rfl)

@[simp]
theorem mem_stabilizerOpenSubgroup (ρ : Representation k G V) [ρ.IsSmooth] (v : V) {g : G} :
    g ∈ ρ.stabilizerOpenSubgroup v ↔ ρ g v = v := Iff.rfl

/-- In a group with separately continuous multiplication, a representation is smooth iff every
vector is fixed by some open subgroup. -/
theorem isSmooth_iff_exists_openSubgroup [SeparatelyContinuousMul G] (ρ : Representation k G V) :
    ρ.IsSmooth ↔ ∀ v : V, ∃ U : OpenSubgroup G, ∀ g ∈ U, ρ g v = v := by
  constructor
  · intro _ v
    exact ⟨ρ.stabilizerOpenSubgroup v, fun _ hg ↦ hg⟩
  · intro h
    refine ⟨fun v ↦ ?_⟩
    obtain ⟨U, hU⟩ := h v
    exact Subgroup.isOpen_of_openSubgroup (ρ.stabilizer v) hU

/-- In a weakly locally compact zero-dimensional topological group (in particular, any locally
profinite group), a representation is smooth iff every vector is fixed by some compact open
subgroup. -/
theorem isSmooth_iff_exists_isCompact_openSubgroup [IsTopologicalGroup G]
    [WeaklyLocallyCompactSpace G] [ZeroDimensionalSpace G] (ρ : Representation k G V) :
    ρ.IsSmooth ↔ ∀ v : V, ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ ∀ g ∈ K, ρ g v = v := by
  constructor
  · intro h v
    have hnhds : (ρ.stabilizer v : Set G) ∈ 𝓝 (1 : G) :=
      (h.isOpen_stabilizer v).mem_nhds (one_mem _)
    obtain ⟨K, hKc, hKsub⟩ := IsTopologicalGroup.exists_compact_openSubgroup_subset hnhds
    exact ⟨K, hKc, fun g hg ↦ hKsub hg⟩
  · intro h
    rw [isSmooth_iff_exists_openSubgroup]
    exact fun v ↦ let ⟨K, _, hK⟩ := h v; ⟨K, hK⟩

/-- Every representation of a discrete group is smooth. -/
instance isSmooth_of_discreteTopology [DiscreteTopology G] (ρ : Representation k G V) :
    ρ.IsSmooth :=
  ⟨fun _ ↦ isOpen_discrete _⟩

/-- Every trivial representation is smooth. -/
instance isSmooth_of_isTrivial (ρ : Representation k G V) [ρ.IsTrivial] : ρ.IsSmooth :=
  ⟨fun v ↦ by
    have htop : (ρ.stabilizer v : Set G) = Set.univ :=
      Set.eq_univ_iff_forall.mpr fun g ↦ ρ.isTrivial_apply g v
    rw [htop]
    exact isOpen_univ⟩

/-- Every representation on a subsingleton module is smooth. -/
instance isSmooth_of_subsingleton [Subsingleton V] (ρ : Representation k G V) : ρ.IsSmooth :=
  ⟨fun v ↦ by
    have htop : (ρ.stabilizer v : Set G) = Set.univ :=
      Set.eq_univ_iff_forall.mpr fun _ ↦ Subsingleton.elim _ _
    rw [htop]
    exact isOpen_univ⟩

/-- Every smooth representation of a preconnected group with separately continuous multiplication
is trivial. -/
theorem isTrivial_of_isSmooth_of_preconnectedSpace [SeparatelyContinuousMul G]
    [PreconnectedSpace G] (ρ : Representation k G V) [ρ.IsSmooth] : ρ.IsTrivial :=
  ⟨fun g ↦ LinearMap.ext fun v ↦ by
    have htop : ρ.stabilizerOpenSubgroup v = ⊤ :=
      OpenSubgroup.eq_top_of_preconnectedSpace (ρ.stabilizerOpenSubgroup v)
    have hmem : g ∈ ρ.stabilizerOpenSubgroup v := htop.symm ▸ OpenSubgroup.mem_top g
    exact (mem_stabilizerOpenSubgroup ρ v).mp hmem⟩

/-- If `f : ρ → σ` is an injective intertwining map and `σ` is smooth, then `ρ` is smooth. -/
theorem IsSmooth.of_injective {ρ : Representation k G V} {σ : Representation k G W} [σ.IsSmooth]
    (f : ρ.IntertwiningMap σ) (hf : Function.Injective f) : ρ.IsSmooth :=
  ⟨fun v ↦ f.stabilizer_eq_of_injective hf v ▸ IsSmooth.isOpen_stabilizer (f v)⟩

/-- If `f : ρ → σ` is a surjective intertwining map and `ρ` is smooth, then `σ` is smooth. -/
theorem IsSmooth.of_surjective [SeparatelyContinuousMul G] {ρ : Representation k G V}
    {σ : Representation k G W} [ρ.IsSmooth] (f : ρ.IntertwiningMap σ)
    (hf : Function.Surjective f) : σ.IsSmooth :=
  ⟨fun w ↦ by
    obtain ⟨v, rfl⟩ := hf w
    exact Subgroup.isOpen_mono (f.stabilizer_le v) (IsSmooth.isOpen_stabilizer v)⟩

/-- Equivalent representations are simultaneously smooth. -/
theorem Equiv.isSmooth_iff {ρ : Representation k G V} {σ : Representation k G W}
    (e : ρ.Equiv σ) : ρ.IsSmooth ↔ σ.IsSmooth :=
  ⟨fun _ ↦ IsSmooth.of_injective e.symm.toIntertwiningMap e.symm.injective,
    fun _ ↦ IsSmooth.of_injective e.toIntertwiningMap e.injective⟩

/-- The restriction of a smooth representation to an invariant submodule is smooth. -/
theorem IsSmooth.subrepresentation (ρ : Representation k G V) [ρ.IsSmooth] (U : Submodule k V)
    (hU : ∀ g, U ≤ U.comap (ρ g)) : (ρ.subrepresentation U hU).IsSmooth :=
  ⟨fun v ↦ by
    have hstab : (ρ.subrepresentation U hU).stabilizer v = ρ.stabilizer v.1 := by
      ext g
      simp [mem_stabilizer, Subtype.ext_iff]
    rw [hstab]
    exact IsSmooth.isOpen_stabilizer v.1⟩

/-- Every subrepresentation of a smooth representation is smooth. -/
instance _root_.Subrepresentation.instIsSmooth {ρ : Representation k G V} [ρ.IsSmooth]
    (S : Subrepresentation ρ) : S.toRepresentation.IsSmooth :=
  IsSmooth.of_injective S.subtype S.subtype_injective

/-- Restriction of a smooth representation along a continuous group homomorphism is smooth. -/
theorem IsSmooth.comp {H : Type*} [Group H] [TopologicalSpace H] {ρ : Representation k G V}
    [ρ.IsSmooth] {f : H →* G} (hf : Continuous f) : IsSmooth (ρ.comp f) :=
  ⟨fun v ↦ by
    rw [stabilizer_comp, Subgroup.coe_comap]
    exact (IsSmooth.isOpen_stabilizer v).preimage hf⟩

/-- The binary product of two smooth representations is smooth. -/
instance IsSmooth.prod (ρ : Representation k G V) (σ : Representation k G W)
    [ρ.IsSmooth] [σ.IsSmooth] : (ρ.prod σ).IsSmooth :=
  ⟨fun x ↦ by
    rw [stabilizer_prod, Subgroup.coe_inf]
    exact (IsSmooth.isOpen_stabilizer x.1).inter (IsSmooth.isOpen_stabilizer x.2)⟩

/-- A finite product of smooth representations is smooth. -/
instance IsSmooth.pi {ι : Type*} [Finite ι] {U : ι → Type*} [∀ i, AddCommMonoid (U i)]
    [∀ i, Module k (U i)] (ρ : ∀ i, Representation k G (U i)) [∀ i, (ρ i).IsSmooth] :
    (Representation.pi ρ).IsSmooth :=
  ⟨fun x ↦ by
    rw [stabilizer_pi, Subgroup.coe_iInf]
    exact isOpen_iInter_of_finite fun i ↦ IsSmooth.isOpen_stabilizer (x i)⟩

/-- An arbitrary direct sum of smooth representations is smooth. -/
instance IsSmooth.directSum {ι : Type*} {U : ι → Type*} [∀ i, AddCommMonoid (U i)]
    [∀ i, Module k (U i)] (ρ : ∀ i, Representation k G (U i)) [∀ i, (ρ i).IsSmooth] :
    (Representation.directSum ρ).IsSmooth :=
  ⟨fun x ↦ by
    classical
    have hstab : ((Representation.directSum ρ).stabilizer x : Set G) =
        ⋂ i ∈ x.support, ((ρ i).stabilizer (x i) : Set G) := by
      ext g
      simp only [SetLike.mem_coe, mem_stabilizer, Set.mem_iInter, DFinsupp.mem_support_toFun,
        directSum_apply, DirectSum.ext_iff, DirectSum.lmap_apply]
      refine ⟨fun h i _ ↦ h i, fun h i ↦ ?_⟩
      by_cases hi : x i = 0
      · simp [hi]
      · exact h i hi
    rw [hstab]
    exact isOpen_biInter_finset fun i _ ↦ IsSmooth.isOpen_stabilizer (x i)⟩

end IsSmooth

section QuotientAndTensor

variable {G : Type*} [Group G] [TopologicalSpace G] [SeparatelyContinuousMul G]

/-- The quotient of a smooth representation by an invariant submodule is smooth. -/
theorem IsSmooth.quotient {k V : Type*} [Ring k] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) [ρ.IsSmooth] (U : Submodule k V) (hU : ∀ g, U ≤ U.comap (ρ g)) :
    (ρ.quotient U hU).IsSmooth := by
  let q : ρ.IntertwiningMap (ρ.quotient U hU) :=
    U.mkQ.intertwiningMap_of_isIntertwiningMap ρ (ρ.quotient U hU) fun _ _ ↦ rfl
  exact IsSmooth.of_surjective q (Submodule.mkQ_surjective U)

/-- The quotient of a smooth representation by a subrepresentation is smooth. -/
instance _root_.Subrepresentation.instIsSmoothQuotient {k V : Type*} [Ring k] [AddCommGroup V]
    [Module k V] {ρ : Representation k G V} [ρ.IsSmooth] (S : Subrepresentation ρ) :
    S.quotient.IsSmooth :=
  IsSmooth.quotient ρ S.toSubmodule fun g _ hv ↦ S.apply_mem_toSubmodule g hv

/-- The tensor product of two smooth representations over a commutative semiring is smooth. -/
instance IsSmooth.tprod {k V W : Type*} [CommSemiring k] [AddCommMonoid V] [Module k V]
    [AddCommMonoid W] [Module k W] (ρ : Representation k G V) (σ : Representation k G W)
    [ρ.IsSmooth] [σ.IsSmooth] : (ρ.tprod σ).IsSmooth :=
  ⟨fun z ↦ by
    induction z using TensorProduct.inductionOn with
    | tmul v w =>
      have hle : ρ.stabilizer v ⊓ σ.stabilizer w ≤ (ρ.tprod σ).stabilizer (v ⊗ₜ[k] w) := by
        intro g hg
        simp only [mem_stabilizer, tprod_apply, TensorProduct.map_tmul]
        rw [hg.1, hg.2]
      exact Subgroup.isOpen_mono hle
        ((IsSmooth.isOpen_stabilizer v).inter (IsSmooth.isOpen_stabilizer w))
    | add x y hx hy =>
      exact Subgroup.isOpen_mono (le_stabilizer_add (ρ.tprod σ) x y) (hx.inter hy)⟩

end QuotientAndTensor

section PermutationAndRegular

variable {k G : Type*} [Semiring k] [Group G] [TopologicalSpace G]

/-- If every point of a `G`-set `X` has open stabilizer in `G`, then the permutation representation
`ofMulAction k G X` is smooth. -/
theorem isSmooth_ofMulAction_of_isOpen_stabilizer [SeparatelyContinuousMul G]
    {X : Type*} [MulAction G X] (hX : ∀ x : X, IsOpen (MulAction.stabilizer G x : Set G)) :
    (ofMulAction k G X).IsSmooth :=
  ⟨fun a ↦ by
    induction a using MonoidAlgebra.induction_linear with
    | zero =>
      rw [stabilizer_zero, Subgroup.coe_top]
      exact isOpen_univ
    | add x y hx hy =>
      exact Subgroup.isOpen_mono (le_stabilizer_add (ofMulAction k G X) x y) (hx.inter hy)
    | single x c =>
      by_cases hc : c = 0
      · subst hc
        simp only [MonoidAlgebra.single_zero, stabilizer_zero, Subgroup.coe_top]
        exact isOpen_univ
      · rw [stabilizer_ofMulAction_single x hc]
        exact hX x⟩

/-- Over a nontrivial coefficient semiring, the permutation representation `ofMulAction k G X` is
smooth iff every point of `X` has open stabilizer in `G`. -/
theorem isSmooth_ofMulAction_iff [SeparatelyContinuousMul G] [Nontrivial k]
    {X : Type*} [MulAction G X] :
    (ofMulAction k G X).IsSmooth ↔ ∀ x : X, IsOpen (MulAction.stabilizer G x : Set G) := by
  refine ⟨fun h x ↦ ?_, isSmooth_ofMulAction_of_isOpen_stabilizer⟩
  rw [← stabilizer_ofMulAction_single (k := k) x one_ne_zero]
  exact h.isOpen_stabilizer _

/-- The coset permutation representation `ofMulAction k G (G ⧸ H)` is smooth whenever `H` is an
open subgroup of `G`. -/
theorem isSmooth_ofMulAction_quotient [SeparatelyContinuousMul G] {H : Subgroup G}
    (hH : IsOpen (H : Set G)) : (ofMulAction k G (G ⧸ H)).IsSmooth := by
  refine isSmooth_ofMulAction_of_isOpen_stabilizer fun q ↦ ?_
  induction q using QuotientGroup.induction_on with
  | H g =>
    have hpre : (MulAction.stabilizer G (g : G ⧸ H) : Set G) =
        (fun x ↦ g⁻¹ * x * g) ⁻¹' (H : Set G) := by
      ext x
      simp only [SetLike.mem_coe, MulAction.mem_stabilizer_iff, Set.mem_preimage]
      have hsmul : x • (g : G ⧸ H) = ((x * g : G) : G ⧸ H) := rfl
      rw [hsmul, QuotientGroup.eq, mul_inv_rev, mul_assoc]
      exact ⟨fun h ↦ by simpa [mul_assoc] using H.inv_mem h,
        fun h ↦ by simpa [mul_assoc] using H.inv_mem h⟩
    rw [hpre]
    exact hH.preimage ((Homeomorph.mulRight g).continuous.comp (Homeomorph.mulLeft g⁻¹).continuous)

/-- The coset permutation representation of an open subgroup `U` is smooth. -/
instance instIsSmoothOfMulActionQuotientOpenSubgroup [SeparatelyContinuousMul G]
    (U : OpenSubgroup G) : (ofMulAction k G (G ⧸ U.toSubgroup)).IsSmooth :=
  isSmooth_ofMulAction_quotient U.isOpen

/-- Over a nontrivial coefficient semiring, the coset permutation representation on `k[G ⧸ H]` is
smooth iff `H` is open in `G`. -/
theorem isSmooth_ofMulAction_quotient_iff [SeparatelyContinuousMul G] [Nontrivial k]
    (H : Subgroup G) : (ofMulAction k G (G ⧸ H)).IsSmooth ↔ IsOpen (H : Set G) := by
  refine ⟨fun h ↦ ?_, isSmooth_ofMulAction_quotient⟩
  have h1 := (isSmooth_ofMulAction_iff (k := k)).mp h ((1 : G) : G ⧸ H)
  rwa [MulAction.stabilizer_quotient] at h1

/-- Over a nontrivial coefficient semiring, the left regular representation on `k[G]` is smooth
iff `G` carries the discrete topology. -/
theorem isSmooth_leftRegular_iff [SeparatelyContinuousMul G] [Nontrivial k] :
    (leftRegular k G).IsSmooth ↔ DiscreteTopology G := by
  rw [leftRegular, isSmooth_ofMulAction_iff, discreteTopology_iff_isOpen_singleton_one]
  constructor
  · intro h
    simpa [Set.eq_singleton_iff_unique_mem] using h 1
  · intro h x
    have hx : (MulAction.stabilizer G x : Set G) = {1} := by
      ext g
      simp
    rw [hx]
    exact h

/-- A product of coset permutation representations `∏ i, k[G ⧸ H i]` is not smooth whenever the
intersection `⨅ i, H i` is not open (in particular, an infinite product of smooth representations
need not be smooth). -/
theorem not_isSmooth_pi_ofMulAction_quotient [Nontrivial k] {ι : Type*}
    (H : ι → Subgroup G) (hH : ¬ IsOpen ((⨅ i, H i : Subgroup G) : Set G)) :
    ¬ (Representation.pi fun i ↦ ofMulAction k G (G ⧸ H i)).IsSmooth := by
  intro h
  apply hH
  have hstab : (Representation.pi fun i ↦ ofMulAction k G (G ⧸ H i)).stabilizer
      (fun i ↦ MonoidAlgebra.single ((1 : G) : G ⧸ H i) (1 : k)) = ⨅ i, H i := by
    rw [stabilizer_pi]
    congr 1
    ext i
    rw [stabilizer_ofMulAction_single _ one_ne_zero, MulAction.stabilizer_quotient]
  rw [← hstab]
  exact h.isOpen_stabilizer _

end PermutationAndRegular

section SmoothVectors

variable {k G V W U : Type*} [Semiring k] [Group G] [TopologicalSpace G]
  [SeparatelyContinuousMul G] [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W]
  [AddCommMonoid U] [Module k U]

/-- The subrepresentation of smooth vectors of `ρ`: all vectors whose stabilizer in `G` is open. -/
def smoothVectors (ρ : Representation k G V) : Subrepresentation ρ where
  toSubmodule :=
    { carrier := {v : V | IsOpen (ρ.stabilizer v : Set G)}
      zero_mem' := by
        simp only [Set.mem_ofPred_eq, stabilizer_zero, Subgroup.coe_top]
        exact isOpen_univ
      add_mem' := fun {x y} hx hy ↦
        Subgroup.isOpen_mono (le_stabilizer_add ρ x y) (hx.inter hy)
      smul_mem' := fun c {x} hx ↦
        Subgroup.isOpen_mono (le_stabilizer_smul ρ c x) hx }
  apply_mem_toSubmodule g v hv := by
    have hpre : (ρ.stabilizer (ρ g v) : Set G) =
        (fun x ↦ g⁻¹ * x * g) ⁻¹' (ρ.stabilizer v : Set G) := by
      ext x
      simp only [SetLike.mem_coe, mem_stabilizer, Set.mem_preimage, map_mul, mul_apply_eq_comp,
        inv_apply_eq_iff]
    have hopen : IsOpen (ρ.stabilizer (ρ g v) : Set G) := by
      rw [hpre]
      exact hv.preimage
        ((Homeomorph.mulRight g).continuous.comp (Homeomorph.mulLeft g⁻¹).continuous)
    exact hopen

/-- A vector belongs to `ρ.smoothVectors` iff its stabilizer in `G` is open. -/
@[simp]
theorem mem_smoothVectors_iff {ρ : Representation k G V} {v : V} :
    v ∈ ρ.smoothVectors ↔ IsOpen (ρ.stabilizer v : Set G) := Iff.rfl

/-- A vector belongs to `ρ.smoothVectors` iff it is fixed by some open subgroup of `G`. -/
theorem mem_smoothVectors_iff_exists_openSubgroup {ρ : Representation k G V} {v : V} :
    v ∈ ρ.smoothVectors ↔ ∃ K : OpenSubgroup G, ∀ g ∈ K, ρ g v = v :=
  ⟨fun hv ↦ ⟨⟨ρ.stabilizer v, hv⟩, fun _ hg ↦ hg⟩,
    fun ⟨_, hK⟩ ↦ Subgroup.isOpen_of_openSubgroup (ρ.stabilizer v) hK⟩

/-- The restriction of `ρ` to its subrepresentation of smooth vectors is smooth. -/
instance isSmooth_smoothVectors (ρ : Representation k G V) :
    ρ.smoothVectors.toRepresentation.IsSmooth :=
  ⟨fun v ↦ by
    have hstab : ρ.smoothVectors.toRepresentation.stabilizer v = ρ.stabilizer v.1 := by
      ext g
      exact Subrepresentation.toRepresentation_apply_coe
    rw [hstab]
    exact v.2⟩

/-- A representation is smooth iff every vector is smooth, i.e., `ρ.smoothVectors = ⊤`. -/
theorem smoothVectors_eq_top_iff (ρ : Representation k G V) :
    ρ.smoothVectors = ⊤ ↔ ρ.IsSmooth :=
  ⟨fun h ↦ ⟨fun v ↦ by rw [← mem_smoothVectors_iff, h]; exact Submodule.mem_top⟩,
    fun h ↦ eq_top_iff.mpr fun v _ ↦ h.isOpen_stabilizer v⟩

/-- For a smooth representation, the subrepresentation of smooth vectors is `⊤`. -/
@[simp]
theorem smoothVectors_eq_top (ρ : Representation k G V) [ρ.IsSmooth] :
    ρ.smoothVectors = ⊤ :=
  (smoothVectors_eq_top_iff ρ).mpr ‹_›

/-- `ρ.smoothVectors` is the largest smooth subrepresentation of `ρ`: a subrepresentation `S` lies
inside `ρ.smoothVectors` iff `S.toRepresentation` is smooth. -/
theorem le_smoothVectors_iff {ρ : Representation k G V} {S : Subrepresentation ρ} :
    S ≤ ρ.smoothVectors ↔ S.toRepresentation.IsSmooth := by
  constructor
  · intro hS
    refine ⟨fun v ↦ ?_⟩
    have hstab : S.toRepresentation.stabilizer v = ρ.stabilizer v.1 := by
      ext g
      exact Subrepresentation.toRepresentation_apply_coe (ρ' := S)
    rw [hstab]
    exact mem_smoothVectors_iff.mp (hS v.2)
  · intro hS v hv
    rw [mem_smoothVectors_iff]
    have hstab : ρ.stabilizer v = S.toRepresentation.stabilizer ⟨v, hv⟩ := by
      ext g
      exact (Subrepresentation.toRepresentation_apply_coe (ρ' := S) (v := ⟨v, hv⟩)
        (w := ⟨v, hv⟩)).symm
    rw [hstab]
    exact hS.isOpen_stabilizer ⟨v, hv⟩

/-- Intertwining maps carry smooth vectors to smooth vectors. -/
theorem IntertwiningMap.map_mem_smoothVectors {ρ : Representation k G V}
    {σ : Representation k G W} (f : ρ.IntertwiningMap σ) {v : V} (hv : v ∈ ρ.smoothVectors) :
    f v ∈ σ.smoothVectors :=
  Subgroup.isOpen_mono (f.stabilizer_le v) hv

/-- An injective intertwining map detects smooth vectors. -/
theorem IntertwiningMap.map_mem_smoothVectors_iff_of_injective {ρ : Representation k G V}
    {σ : Representation k G W} (f : ρ.IntertwiningMap σ) (hf : Function.Injective f) {v : V} :
    f v ∈ σ.smoothVectors ↔ v ∈ ρ.smoothVectors := by
  rw [mem_smoothVectors_iff, mem_smoothVectors_iff, f.stabilizer_eq_of_injective hf v]

/-- Any intertwining map from a smooth representation `ρ` into `σ` factors through the
subrepresentation of smooth vectors `σ.smoothVectors`. -/
def IntertwiningMap.liftSmoothVectors {ρ : Representation k G V} {σ : Representation k G W}
    [ρ.IsSmooth] (f : ρ.IntertwiningMap σ) :
    ρ.IntertwiningMap σ.smoothVectors.toRepresentation :=
  f.codRestrict σ.smoothVectors fun v ↦
    Subrepresentation.mem_toSubmodule.mpr (f.map_mem_smoothVectors (IsSmooth.isOpen_stabilizer v))

@[simp]
theorem IntertwiningMap.coe_liftSmoothVectors_apply {ρ : Representation k G V}
    {σ : Representation k G W} [ρ.IsSmooth] (f : ρ.IntertwiningMap σ) (v : V) :
    (f.liftSmoothVectors v : W) = f v :=
  f.codRestrict_apply_coe σ.smoothVectors _ v

@[simp]
theorem IntertwiningMap.subtype_comp_liftSmoothVectors {ρ : Representation k G V}
    {σ : Representation k G W} [ρ.IsSmooth] (f : ρ.IntertwiningMap σ) :
    σ.smoothVectors.subtype.comp f.liftSmoothVectors = f := by
  ext v
  simp

/-- **Universal property of `smoothVectors`**: an intertwining map `ρ → σ.smoothVectors` from a
smooth representation `ρ` equals `f.liftSmoothVectors` iff composing with the inclusion recovers
`f`. -/
theorem IntertwiningMap.eq_liftSmoothVectors_iff {ρ : Representation k G V}
    {σ : Representation k G W} [ρ.IsSmooth] {f : ρ.IntertwiningMap σ}
    {g : ρ.IntertwiningMap σ.smoothVectors.toRepresentation} :
    g = f.liftSmoothVectors ↔ σ.smoothVectors.subtype.comp g = f := by
  refine ⟨fun h ↦ h ▸ subtype_comp_liftSmoothVectors f, fun h ↦ ?_⟩
  ext v
  have h' := congrArg (fun φ : ρ.IntertwiningMap σ ↦ φ v) h
  simpa using h'

/-- An intertwining map `f : ρ → σ` restricts to an intertwining map between the smooth-vector
subrepresentations. -/
def IntertwiningMap.restrictSmoothVectors {ρ : Representation k G V} {σ : Representation k G W}
    (f : ρ.IntertwiningMap σ) :
    ρ.smoothVectors.toRepresentation.IntertwiningMap σ.smoothVectors.toRepresentation :=
  (f.comp ρ.smoothVectors.subtype).liftSmoothVectors

@[simp]
theorem IntertwiningMap.coe_restrictSmoothVectors_apply {ρ : Representation k G V}
    {σ : Representation k G W} (f : ρ.IntertwiningMap σ) (v : ρ.smoothVectors.toSubmodule) :
    (f.restrictSmoothVectors v : W) = f v := by
  simp [restrictSmoothVectors]

@[simp]
theorem IntertwiningMap.restrictSmoothVectors_id (ρ : Representation k G V) :
    (IntertwiningMap.id ρ).restrictSmoothVectors =
      IntertwiningMap.id ρ.smoothVectors.toRepresentation := by
  ext v
  simp

@[simp]
theorem IntertwiningMap.restrictSmoothVectors_comp {ρ : Representation k G V}
    {σ : Representation k G W} {τ : Representation k G U}
    (g : σ.IntertwiningMap τ) (f : ρ.IntertwiningMap σ) :
    (g.comp f).restrictSmoothVectors = g.restrictSmoothVectors.comp f.restrictSmoothVectors := by
  ext v
  simp

@[simp]
theorem IntertwiningMap.subtype_comp_restrictSmoothVectors {ρ : Representation k G V}
    {σ : Representation k G W} (f : ρ.IntertwiningMap σ) :
    σ.smoothVectors.subtype.comp f.restrictSmoothVectors = f.comp ρ.smoothVectors.subtype := by
  ext v
  simp

/-- A pair `(v, w)` is a smooth vector of `ρ.prod σ` iff both `v` and `w` are smooth vectors. -/
theorem mem_smoothVectors_prod_iff {ρ : Representation k G V} {σ : Representation k G W}
    {x : V × W} :
    x ∈ (ρ.prod σ).smoothVectors ↔ x.1 ∈ ρ.smoothVectors ∧ x.2 ∈ σ.smoothVectors := by
  simp only [mem_smoothVectors_iff, stabilizer_prod, Subgroup.coe_inf]
  refine ⟨fun h ↦ ⟨Subgroup.isOpen_mono inf_le_left h, Subgroup.isOpen_mono inf_le_right h⟩,
    fun h ↦ h.1.inter h.2⟩

/-- A smooth vector of `ρ` remains smooth after restriction along a continuous group
homomorphism. -/
theorem smoothVectors_toSubmodule_le_comp {H : Type*} [Group H] [TopologicalSpace H]
    [SeparatelyContinuousMul H] (ρ : Representation k G V) {f : H →* G} (hf : Continuous f) :
    ρ.smoothVectors.toSubmodule ≤ (smoothVectors (ρ.comp f)).toSubmodule := by
  intro v hv
  rw [Subrepresentation.mem_toSubmodule, mem_smoothVectors_iff, stabilizer_comp, Subgroup.coe_comap]
  exact hv.preimage hf

/-- For a non-discrete `T1` topological group with separately continuous multiplication, the left
regular representation on `k[G]` has no nonzero smooth vectors. -/
theorem smoothVectors_leftRegular_eq_bot [T1Space G] (hG : ¬ DiscreteTopology G) :
    (leftRegular k G).smoothVectors = ⊥ := by
  apply Subrepresentation.toSubmodule_injective
  rw [Subrepresentation.toSubmodule_bot, Submodule.eq_bot_iff]
  intro x hx
  by_contra hx0
  obtain ⟨g₀, hg₀⟩ : x.coeff.support.Nonempty := by
    rw [Finsupp.support_nonempty_iff]
    simpa [MonoidAlgebra.coeff_eq_zero] using hx0
  have hU_open : IsOpen ((leftRegular k G).stabilizer x : Set G) := hx
  have hU_fin : ((leftRegular k G).stabilizer x : Set G).Finite := by
    refine Set.Finite.of_finite_image (f := fun g : G ↦ g * g₀) ?_ (mul_left_injective g₀).injOn
    refine x.coeff.support.finite_toSet.subset ?_
    rintro _ ⟨u, hu, rfl⟩
    rw [SetLike.mem_coe, mem_stabilizer] at hu
    have hcoeff : (leftRegular k G u x).coeff (u * g₀) = x.coeff g₀ := by
      simp [leftRegular, ofMulAction_def,
        Finsupp.mapDomain_apply_of_injective (mul_right_injective u)]
    rw [hu] at hcoeff
    rw [Finset.mem_coe, Finsupp.mem_support_iff, hcoeff]
    exact Finsupp.mem_support_iff.mp hg₀
  have h1_open : IsOpen ({1} : Set G) := by
    have hclosed : IsClosed (((leftRegular k G).stabilizer x : Set G) \ ({1} : Set G)) :=
      (hU_fin.sdiff).isClosed
    have heq : ({1} : Set G) =
        ((leftRegular k G).stabilizer x : Set G) ∩
          (((leftRegular k G).stabilizer x : Set G) \ ({1} : Set G))ᶜ := by
      ext g
      simp only [Set.mem_singleton_iff, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_sdiff,
        not_and, not_not]
      exact ⟨fun hg ↦ by subst hg; exact ⟨one_mem _, fun _ ↦ rfl⟩, fun ⟨hgU, h⟩ ↦ h hgU⟩
    rw [heq]
    exact hU_open.inter hclosed.isOpen_compl
  exact hG (discreteTopology_of_isOpen_singleton_one h1_open)

end SmoothVectors

section LocallyProfiniteSmoothVectors

variable {k G V : Type*} [Semiring k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [WeaklyLocallyCompactSpace G] [ZeroDimensionalSpace G] [AddCommMonoid V] [Module k V]

/-- In a weakly locally compact zero-dimensional topological group (in particular, any locally
profinite group), a vector belongs to `ρ.smoothVectors` iff it is fixed by some compact open
subgroup of `G`. -/
theorem mem_smoothVectors_iff_exists_isCompact_openSubgroup {ρ : Representation k G V} {v : V} :
    v ∈ ρ.smoothVectors ↔ ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ ∀ g ∈ K, ρ g v = v := by
  constructor
  · intro hv
    obtain ⟨K, hKc, hKsub⟩ :=
      IsTopologicalGroup.exists_compact_openSubgroup_subset (hv.mem_nhds (one_mem _))
    exact ⟨K, hKc, fun g hg ↦ hKsub hg⟩
  · rintro ⟨K, _, hK⟩
    exact mem_smoothVectors_iff_exists_openSubgroup.mpr ⟨K, hK⟩

end LocallyProfiniteSmoothVectors

section InvariantsSup

variable {k G V : Type*} [CommRing k] [Group G] [TopologicalSpace G]
  [AddCommGroup V] [Module k V]

/-- Restricting to a smaller subgroup yields a larger submodule of invariants. -/
private theorem invariants_comp_subtype_antitone (ρ : Representation k G V) :
    Antitone (fun U : OpenSubgroup G ↦ invariants (ρ.comp U.toSubgroup.subtype)) :=
  fun _ _ hle _ hv g ↦ hv ⟨g.1, hle g.2⟩

/-- The underlying submodule of `ρ.smoothVectors` is the directed supremum of the open-subgroup
invariant submodules `invariants (ρ.comp U.toSubgroup.subtype)`. -/
theorem smoothVectors_toSubmodule_eq_iSup [SeparatelyContinuousMul G]
    (ρ : Representation k G V) :
    ρ.smoothVectors.toSubmodule =
      ⨆ U : OpenSubgroup G, invariants (ρ.comp U.toSubgroup.subtype) := by
  have hdir : Directed (· ≤ ·)
      (fun U : OpenSubgroup G ↦ invariants (ρ.comp U.toSubgroup.subtype)) :=
    fun U₁ U₂ ↦ ⟨U₁ ⊓ U₂, invariants_comp_subtype_antitone ρ inf_le_left,
      invariants_comp_subtype_antitone ρ inf_le_right⟩
  ext v
  rw [Subrepresentation.mem_toSubmodule, mem_smoothVectors_iff_exists_openSubgroup,
    Submodule.mem_iSup_of_directed _ hdir]
  simp [mem_invariants]

/-- In a weakly locally compact zero-dimensional topological group (in particular, any locally
profinite group), the underlying submodule of `ρ.smoothVectors` is the directed supremum of the
compact-open-subgroup invariant submodules. -/
theorem smoothVectors_toSubmodule_eq_iSup_isCompact [IsTopologicalGroup G]
    [WeaklyLocallyCompactSpace G] [ZeroDimensionalSpace G] (ρ : Representation k G V) :
    ρ.smoothVectors.toSubmodule =
      ⨆ (K : OpenSubgroup G) (_ : IsCompact (K : Set G)),
        invariants (ρ.comp K.toSubgroup.subtype) := by
  obtain ⟨K₀, hK₀, _⟩ := IsTopologicalGroup.exists_compact_openSubgroup_subset (G := G) univ_mem
  have : Nonempty {K : OpenSubgroup G // IsCompact (K : Set G)} := ⟨⟨K₀, hK₀⟩⟩
  have hdir : Directed (· ≤ ·) (fun K : {K : OpenSubgroup G // IsCompact (K : Set G)} ↦
      invariants (ρ.comp K.1.toSubgroup.subtype)) :=
    fun K₁ K₂ ↦
      let ⟨K, hK₁, hK₂⟩ := OpenSubgroup.directed_isCompact K₁ K₂
      ⟨K, invariants_comp_subtype_antitone ρ hK₁, invariants_comp_subtype_antitone ρ hK₂⟩
  ext v
  rw [Subrepresentation.mem_toSubmodule, mem_smoothVectors_iff_exists_isCompact_openSubgroup,
    iSup_subtype', Submodule.mem_iSup_of_directed _ hdir]
  simp [mem_invariants]

/-- A representation is smooth iff `V` is the supremum of its open-subgroup invariant submodules. -/
theorem isSmooth_iff_iSup_invariants_eq_top [SeparatelyContinuousMul G]
    (ρ : Representation k G V) :
    ρ.IsSmooth ↔ (⨆ U : OpenSubgroup G, invariants (ρ.comp U.toSubgroup.subtype)) = ⊤ := by
  rw [← smoothVectors_toSubmodule_eq_iSup, ← Subrepresentation.toSubmodule_top (ρ := ρ),
    Subrepresentation.toSubmodule_injective.eq_iff, smoothVectors_eq_top_iff]

/-- In a weakly locally compact zero-dimensional topological group (in particular, any locally
profinite group), a representation is smooth iff `V` is the supremum of its compact-open-subgroup
invariant submodules. -/
theorem isSmooth_iff_iSup_isCompact_invariants_eq_top [IsTopologicalGroup G]
    [WeaklyLocallyCompactSpace G] [ZeroDimensionalSpace G] (ρ : Representation k G V) :
    ρ.IsSmooth ↔
      (⨆ (K : OpenSubgroup G) (_ : IsCompact (K : Set G)),
        invariants (ρ.comp K.toSubgroup.subtype)) = ⊤ := by
  rw [← smoothVectors_toSubmodule_eq_iSup_isCompact, ← Subrepresentation.toSubmodule_top (ρ := ρ),
    Subrepresentation.toSubmodule_injective.eq_iff, smoothVectors_eq_top_iff]

end InvariantsSup

end Representation

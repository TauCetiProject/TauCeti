/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.RepresentationTheory.Stabilizer
public import Mathlib.RepresentationTheory.Subrepresentation
public import TauCeti.RepresentationTheory.Pi.Basic
import Mathlib.Algebra.Module.Submodule.Union
import Mathlib.LinearAlgebra.FixedSubmodule
import TauCeti.RepresentationTheory.Quotient

/-!
# Stabilizers of vectors and subsets in a representation

Mathlib's `Mathlib.RepresentationTheory.Stabilizer` introduces `Representation.stabilizer ρ v` and
records how it behaves under zero, scalar multiplication, addition, finite sums, intertwining maps,
and conjugation by group elements. This file supplies structural identities needed to compute vector
and subset stabilizers across standard constructions on representations:

* subrepresentations (`Subrepresentation.stabilizer_toRepresentation`), injective intertwining maps
  (`Representation.IntertwiningMap.stabilizer_apply_of_injective`), and equivalences
  (`Representation.Equiv.stabilizer_apply`);
* restriction along a group homomorphism (`Representation.stabilizer_comp` and
  `Representation.map_stabilizer_comp_of_surjective`), trivial and subsingleton representations,
  binary and arbitrary products (`Representation.stabilizer_prod`, `Representation.stabilizer_pi`),
  and quotients (`Subrepresentation.le_stabilizer_quotient_mk`);
* permutation and left regular representations (`Representation.stabilizer_ofMulAction_single`,
  `Representation.stabilizer_leftRegular_single`, `Representation.finite_stabilizer_leftRegular`),
  trivial subgroup restrictions (`Representation.isTrivial_comp_subtype_iff` and
  `Representation.le_stabilizer_of_isTrivial_comp_subtype`), and coset permutation modules
  `A[G ⧸ N]`;
* the Galois-style correspondence `v ∈ invariants (ρ.comp H.subtype) ↔ H ≤ ρ.stabilizer v`
  linking stabilizers to subgroup invariants (`Representation.mem_invariants_comp_subtype_iff`).

For a vector `v : V`, the **orbit map** `G ⧸ stabilizer ρ v → V`, `[g] ↦ ρ g v`
(`Representation.orbitMap`), is well defined because `ρ g v` depends only on the coset
`g (stabilizer ρ v)`. It is equivariant for the action of `G` on the cosets by left multiplication
(`Representation.orbitMap_smul`), injective (`Representation.orbitMap_injective`), and its range is
the orbit `{ρ g v | g ∈ G}` of `v` (`Representation.range_orbitMap`). The coadjoint orbit
`G ⧸ G_ν` of a Lie group, with the orbit map of the coadjoint representation, is the main instance.

Let a group `G` act linearly on an `R`-module `M` through `ρ`. Every element fixing a set `s`
pointwise fixes `Submodule.span R s` (`Representation.biInf_stabilizer_span`), and pulling `ρ` back
along a group homomorphism pulls back point stabilizers (`Representation.stabilizer_comp`) and
pushes them forward when surjective (`Representation.map_stabilizer_comp_of_surjective`).

When `G` is finite and acts on a vector space `V` over an infinite field `K` (without dimension or
characteristic restrictions), the pointwise stabilizer `⨅ w ∈ U, ρ.stabilizer w` of any subspace `U`
equals `ρ.stabilizer v` for a single general-position vector `v ∈ U`, via subspace avoidance
(`Submodule.exists_forall_notMem_of_forall_ne_top`).

## Main results

* `Subrepresentation.stabilizer_toRepresentation`
* `Representation.IntertwiningMap.stabilizer_apply_of_injective`
* `Representation.Equiv.stabilizer_apply`
* `Representation.stabilizer_prod` and `Representation.stabilizer_pi`
* `Subrepresentation.le_stabilizer_quotient_mk`
* `Representation.stabilizer_ofMulAction_single` and `Representation.stabilizer_leftRegular_single`
* `Representation.finite_stabilizer_leftRegular`
* `Representation.isTrivial_comp_subtype_iff` and
  `Representation.le_stabilizer_of_isTrivial_comp_subtype`
* `Representation.mem_invariants_comp_subtype_iff`
* `Representation.orbitMap_smul`, `Representation.orbitMap_injective`,
  `Representation.range_orbitMap`
* `Representation.biInf_stabilizer_span`: pointwise stabilizer of `Submodule.span R s`.
* `Representation.stabilizer_comp`, `Representation.map_stabilizer_comp_of_surjective`,
  `Representation.comap_mk'_stabilizer_ofQuotient`, and `Representation.map_mk'_stabilizer`:
  pullback and pushforward of point stabilizers under group homomorphisms and quotients.
* `Representation.exists_mem_stabilizer_eq_biInf` and
  `Representation.exists_mem_span_stabilizer_eq_biInf`: general-position stabilizer witnesses in `U`
  and `Submodule.span K s` over an infinite field.

## References

* R. Kane, *Reflection Groups and Invariant Theory*, CMS Books in Mathematics, Springer (2001),
  § 22.1.
-/

public section

open scoped MonoidAlgebra

namespace Subrepresentation

/-- The stabilizer of a vector of a subrepresentation is its stabilizer in the ambient
representation. -/
@[simp]
theorem stabilizer_toRepresentation {A G V : Type*} [Semiring A] [Group G]
    [AddCommMonoid V] [Module A V] {ρ : Representation A G V} (ρ' : Subrepresentation ρ)
    (v : ρ'.toSubmodule) : ρ'.toRepresentation.stabilizer v = ρ.stabilizer v := by
  ext g
  rw [Representation.mem_stabilizer, Representation.mem_stabilizer,
    Subrepresentation.toRepresentation_apply_coe]

/-- Taking the quotient by a subrepresentation can only enlarge the stabilizer of a vector. -/
theorem le_stabilizer_quotient_mk {A G V : Type*} [Ring A] [Group G]
    [AddCommGroup V] [Module A V] {ρ : Representation A G V} (S : Subrepresentation ρ) (v : V) :
    ρ.stabilizer v ≤ S.quotient.stabilizer (Submodule.Quotient.mk v) := by
  intro g hg
  rw [Representation.mem_stabilizer] at hg ⊢
  change S.quotient g ⟦v⟧ = ⟦v⟧
  rw [Subrepresentation.quotient_apply_mk, hg]

end Subrepresentation

namespace Representation

section Semiring

variable {A G V W : Type*} [Semiring A] [Group G]
  [AddCommMonoid V] [Module A V] [AddCommMonoid W] [Module A W]
  {ρ : Representation A G V} {σ : Representation A G W}

/-- The carrier of `ρ.stabilizer v` is `{g : G | ρ g v = v}`. -/
theorem coe_stabilizer (ρ : Representation A G V) (v : V) :
    ((ρ.stabilizer v : Subgroup G) : Set G) = {g : G | ρ g v = v} :=
  (rfl)

/-- The stabilizers of an injective intertwining map agree with those of its source. -/
theorem IntertwiningMap.stabilizer_apply_of_injective (f : ρ.IntertwiningMap σ)
    (hf : Function.Injective f) (v : V) : σ.stabilizer (f v) = ρ.stabilizer v := by
  ext g
  rw [mem_stabilizer, mem_stabilizer, ← f.isIntertwining, hf.eq_iff]

/-- An equivalence of representations preserves the stabilizer of every vector. -/
@[simp]
theorem Equiv.stabilizer_apply (e : Equiv ρ σ) (v : V) : σ.stabilizer (e v) = ρ.stabilizer v :=
  e.toIntertwiningMap.stabilizer_apply_of_injective (EquivLike.injective e) v

/-- Every vector in a trivial representation has stabilizer `⊤`. -/
theorem stabilizer_eq_top (ρ : Representation A G V) [ρ.IsTrivial] (v : V) :
    ρ.stabilizer v = ⊤ := by
  ext g
  simp [isTrivial_apply]

/-- Every vector in `Representation.trivial` has stabilizer `⊤`. -/
@[simp]
theorem stabilizer_trivial (v : V) : (trivial A G V).stabilizer v = ⊤ :=
  stabilizer_eq_top (trivial A G V) v

/-- Every vector in a representation on a subsingleton module has stabilizer `⊤`. -/
theorem stabilizer_eq_top_of_subsingleton (ρ : Representation A G V) [Subsingleton V] (v : V) :
    ρ.stabilizer v = ⊤ := by
  ext g
  simp [Subsingleton.elim (ρ g v) v]

/-- The stabilizer of a pair in a binary product representation is the intersection of the
component stabilizers. -/
@[simp]
theorem stabilizer_prod (ρ : Representation A G V) (σ : Representation A G W) (x : V × W) :
    (ρ.prod σ).stabilizer x = ρ.stabilizer x.fst ⊓ σ.stabilizer x.snd := by
  ext g
  simp [Prod.ext_iff]

/-- The stabilizer of a family in a product representation `Representation.pi ρ` is the infimum of
the component stabilizers. -/
@[simp]
theorem stabilizer_pi {ι : Type*} {M : ι → Type*} [∀ i, AddCommMonoid (M i)] [∀ i, Module A (M i)]
    (ρ : ∀ i, Representation A G (M i)) (x : ∀ i, M i) :
    (Representation.pi ρ).stabilizer x = ⨅ i, (ρ i).stabilizer (x i) := by
  ext g
  simp [Subgroup.mem_iInf, funext_iff]

section MulAction

variable {X : Type*} [MulAction G X]

/-- In a permutation representation `A[X]`, the point stabilizer of `x` fixes every scalar
multiple `single x a` of the basis vector at `x`. -/
theorem le_stabilizer_ofMulAction_single (x : X) (a : A) :
    MulAction.stabilizer G x ≤ (ofMulAction A G X).stabilizer (MonoidAlgebra.single x a) := by
  intro g hg
  rw [mem_stabilizer]
  simp [MulAction.mem_stabilizer_iff.mp hg]

/-- The stabilizer of a basis vector of a permutation representation is the stabilizer of the
point, for nonzero coefficient. -/
theorem stabilizer_ofMulAction_single (x : X) {r : A} (hr : r ≠ 0) :
    (ofMulAction A G X).stabilizer (MonoidAlgebra.single x r) = MulAction.stabilizer G x := by
  ext g
  rw [mem_stabilizer, ofMulAction_single, MonoidAlgebra.single_left_inj hr,
    MulAction.mem_stabilizer_iff]

end MulAction

/-- In the left regular representation `A[G]`, any nonzero monomial `single g a` has trivial
stabilizer. -/
theorem stabilizer_leftRegular_single (g : G) {a : A} (ha : a ≠ 0) :
    (leftRegular A G).stabilizer (MonoidAlgebra.single g a) = ⊥ := by
  rw [leftRegular, stabilizer_ofMulAction_single _ ha]
  simp

/-- **Every nonzero vector in the left regular representation has finite stabilizer.** -/
theorem finite_stabilizer_leftRegular {x : A[G]} (hx : x ≠ 0) :
    ((leftRegular A G).stabilizer x : Set G).Finite := by
  obtain ⟨g₀, hg₀⟩ := Finsupp.support_nonempty_iff.mpr (MonoidAlgebra.coeff_eq_zero.not.mpr hx)
  refine (x.coeff.support.finite_toSet.preimage (mul_left_injective g₀).injOn).subset fun h hh ↦ ?_
  rw [SetLike.mem_coe, mem_stabilizer] at hh
  have hcoeff := congrArg (fun y : A[G] ↦ y.coeff (h * g₀)) hh
  rw [coeff_ofMulAction, smul_eq_mul, inv_mul_cancel_left] at hcoeff
  exact Finset.mem_coe.mpr (Finsupp.mem_support_iff.mpr (hcoeff ▸ Finsupp.mem_support_iff.mp hg₀))

/-- The restriction of `ρ` to a subgroup `H` is trivial if and only if `H` fixes every vector of
`V`. -/
theorem isTrivial_comp_subtype_iff (ρ : Representation A G V) (H : Subgroup G) :
    IsTrivial (ρ.comp H.subtype) ↔ ∀ v : V, H ≤ ρ.stabilizer v :=
  ⟨fun h v g hg ↦ LinearMap.congr_fun (h.out ⟨g, hg⟩) v,
    fun h ↦ ⟨fun ⟨_, hg⟩ ↦ LinearMap.ext fun v ↦ h v hg⟩⟩

/-- If the restriction of `ρ` to a subgroup `H` is trivial, then `H` is contained in the
stabilizer of every vector. -/
theorem le_stabilizer_of_isTrivial_comp_subtype (ρ : Representation A G V) (H : Subgroup G)
    [IsTrivial (ρ.comp H.subtype)] (v : V) :
    H ≤ ρ.stabilizer v :=
  (ρ.isTrivial_comp_subtype_iff H).mp ‹_› v

/-- Every normal subgroup `N` of `G` is contained in the stabilizer of every vector of the coset
permutation representation `A[G ⧸ N]`. -/
theorem le_stabilizer_ofMulAction_quotient (N : Subgroup G) [N.Normal] (v : A[G ⧸ N]) :
    N ≤ (ofMulAction A G (G ⧸ N)).stabilizer v :=
  le_stabilizer_of_isTrivial_comp_subtype (ofMulAction A G (G ⧸ N)) N v

end Semiring

section CommRing

variable {A G V : Type*} [CommRing A] [Group G] [AddCommGroup V] [Module A V]
  {ρ : Representation A G V}

/-- A vector is invariant under the restriction of `ρ` to a subgroup `H` exactly when `H` lies in
its stabilizer. -/
theorem mem_invariants_comp_subtype_iff {H : Subgroup G} {v : V} :
    v ∈ invariants (ρ.comp H.subtype) ↔ H ≤ ρ.stabilizer v := by
  simp [mem_invariants, IsConcreteLE.le_iff]

end CommRing

section OrbitMap

variable {k G V : Type*} [Semiring k] [Group G] [AddCommMonoid V] [Module k V]
  (ρ : Representation k G V) (v : V)

/-- The **orbit map** `[g] ↦ ρ g v` from the cosets of the stabilizer of `v` to `V`. It is a
bijection onto the orbit of `v` (`Representation.orbitMap_injective`,
`Representation.range_orbitMap`). -/
def orbitMap : G ⧸ ρ.stabilizer v → V :=
  Quotient.lift (s := QuotientGroup.leftRel _) (fun g : G ↦ ρ g v) fun g h hgh ↦ by
    have hk : ρ (g⁻¹ * h) v = v := mem_stabilizer.1 (QuotientGroup.leftRel_apply.1 hgh)
    rw [← mul_inv_cancel_left g h, map_mul, mul_apply_eq_comp, hk]

/-- The orbit map sends the coset of `g` to `ρ g v`. -/
@[simp]
theorem orbitMap_mk (g : G) : ρ.orbitMap v (g : G ⧸ ρ.stabilizer v) = ρ g v :=
  (rfl)

/-- The orbit map is equivariant for the action of `G` on the cosets of the stabilizer by left
multiplication. -/
@[simp]
theorem orbitMap_smul (h : G) (x : G ⧸ ρ.stabilizer v) :
    ρ.orbitMap v (h • x) = ρ h (ρ.orbitMap v x) := by
  induction x using QuotientGroup.induction_on with
  | H g => rw [MulAction.Quotient.smul_coe, smul_eq_mul, orbitMap_mk, orbitMap_mk, map_mul,
    mul_apply_eq_comp]

/-- The orbit map is injective: `ρ g v = ρ h v` exactly when `g⁻¹ h` stabilizes `v`. -/
theorem orbitMap_injective : Function.Injective (ρ.orbitMap v) := by
  intro x y hxy
  induction x using QuotientGroup.induction_on with | H g =>
  induction y using QuotientGroup.induction_on with | H h =>
  refine QuotientGroup.eq.2 (mem_stabilizer.2 ?_)
  rw [orbitMap_mk, orbitMap_mk] at hxy
  rw [map_mul, mul_apply_eq_comp, ← hxy, ← mul_apply_eq_comp, ← map_mul, inv_mul_cancel,
    map_one, one_apply_eq_self]

/-- The range of the orbit map is the orbit `{ρ g v | g ∈ G}` of `v`. -/
theorem range_orbitMap : Set.range (ρ.orbitMap v) = Set.range fun g : G ↦ ρ g v :=
  (QuotientGroup.mk_surjective.range_comp (ρ.orbitMap v)).symm

end OrbitMap

section Semiring

variable {R G M : Type*} [Semiring R] [Group G] [AddCommMonoid M] [Module R M]
  (ρ : Representation R G M)

/-- The pointwise stabilizer of the `R`-linear span of `s` equals the pointwise stabilizer of
`s`. -/
@[simp] theorem biInf_stabilizer_span (s : Set M) :
    (⨅ v ∈ Submodule.span R s, ρ.stabilizer v) = ⨅ v ∈ s, ρ.stabilizer v := by
  refine le_antisymm (le_iInf₂ fun v hv ↦ iInf₂_le v (Submodule.subset_span hv)) (le_iInf₂ ?_)
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx => exact iInf₂_le x hx
  | zero => simp [stabilizer_zero]
  | add x y _ _ ihx ihy => exact (le_inf ihx ihy).trans (ρ.le_stabilizer_add x y)
  | smul r x _ ihx => exact ihx.trans (ρ.le_stabilizer_smul r x)

/-- Pulling a representation back along a group homomorphism `f` pulls back point stabilizers by
`Subgroup.comap f`. -/
@[simp] theorem stabilizer_comp {H : Type*} [Group H] (f : H →* G) (v : M) :
    stabilizer (ρ.comp f) v = (ρ.stabilizer v).comap f := rfl

/-- Pushing forward the stabilizer of `v` in `ρ.comp f` along a surjective group homomorphism `f`
recovers `ρ.stabilizer v`. -/
theorem map_stabilizer_comp_of_surjective {H : Type*} [Group H] {f : H →* G}
    (hf : Function.Surjective f) (v : M) :
    (stabilizer (ρ.comp f) v).map f = ρ.stabilizer v := by
  rw [ρ.stabilizer_comp f v, Subgroup.map_comap_eq_self_of_surjective hf]

/-- Pulling back the stabilizer of `v` in a quotient by a trivially acting normal subgroup recovers
`ρ.stabilizer v`. -/
@[simp] theorem comap_mk'_stabilizer_ofQuotient (S : Subgroup G) [S.Normal]
    [IsTrivial (ρ.comp S.subtype)] (v : M) :
    ((ρ.ofQuotient S).stabilizer v).comap (QuotientGroup.mk' S) = ρ.stabilizer v := by
  rw [← (ρ.ofQuotient S).stabilizer_comp (QuotientGroup.mk' S) v, ρ.ofQuotient_comp_mk' S]

/-- Pushing `ρ.stabilizer v` forward along the quotient by a trivially acting normal subgroup gives
the stabilizer of `v` in the quotient representation. -/
@[simp] theorem map_mk'_stabilizer (S : Subgroup G) [S.Normal]
    [IsTrivial (ρ.comp S.subtype)] (v : M) :
    (ρ.stabilizer v).map (QuotientGroup.mk' S) = (ρ.ofQuotient S).stabilizer v := by
  simpa only [ρ.ofQuotient_comp_mk' S] using
    (ρ.ofQuotient S).map_stabilizer_comp_of_surjective (QuotientGroup.mk'_surjective S) v

end Semiring

section InfiniteField

variable {K G V : Type*} [Field K] [Infinite K] [Group G] [Finite G]
  [AddCommGroup V] [Module K V] (ρ : Representation K G V)

/-- **General-position witness for a subspace stabilizer.** When a finite group `G` acts linearly on
a vector space `V` over an infinite field `K`, every subspace `U` contains a vector `v ∈ U` whose
stabilizer equals the pointwise stabilizer `⨅ w ∈ U, ρ.stabilizer w` of `U`. -/
theorem exists_mem_stabilizer_eq_biInf (U : Submodule K V) :
    ∃ v ∈ U, ρ.stabilizer v = ⨅ w ∈ U, ρ.stabilizer w := by
  classical
  set H : Subgroup G := ⨅ w ∈ U, ρ.stabilizer w
  let p : {g : G // g ∉ H} → Submodule K U := fun g ↦ (ρ g.val).fixedSubmodule.comap U.subtype
  have hp (g : {g : G // g ∉ H}) : p g ≠ ⊤ := fun htop ↦ g.property <|
    Subgroup.mem_iInf.mpr fun w ↦ Subgroup.mem_iInf.mpr fun hw ↦ by
      simpa [p] using (htop ▸ Submodule.mem_top : (⟨w, hw⟩ : U) ∈ p g)
  obtain ⟨u, hu⟩ := Submodule.exists_forall_notMem_of_forall_ne_top p hp
  refine ⟨u.val, u.property, le_antisymm (fun g hg ↦ ?_) (iInf₂_le u.val u.property)⟩
  by_contra hgH
  exact hu ⟨g, hgH⟩ (by simpa [p] using hg)

/-- **General-position witness for a set stabilizer.** Over an infinite field, the pointwise
stabilizer of any subset `s` of a representation of a finite group equals the stabilizer of a
single vector in `Submodule.span K s`. -/
theorem exists_mem_span_stabilizer_eq_biInf (s : Set V) :
    ∃ v ∈ Submodule.span K s, ρ.stabilizer v = ⨅ w ∈ s, ρ.stabilizer w := by
  obtain ⟨v, hv, hstab⟩ := ρ.exists_mem_stabilizer_eq_biInf (Submodule.span K s)
  exact ⟨v, hv, hstab.trans (ρ.biInf_stabilizer_span s)⟩

end InfiniteField

end Representation

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.RepresentationTheory.Stabilizer
public import Mathlib.RepresentationTheory.Subrepresentation
public import TauCeti.RepresentationTheory.Pi.Basic
import TauCeti.RepresentationTheory.Quotient

/-!
# Vector stabilizers in representations

Mathlib's `Mathlib.RepresentationTheory.Stabilizer` introduces `Representation.stabilizer ρ v` and
records how it behaves under zero, scalar multiplication, addition, finite sums, intertwining maps,
and conjugation by group elements. This file supplies the remaining structural identities needed to
compute vector stabilizers across standard constructions on representations:

* subrepresentations (`Subrepresentation.stabilizer_toRepresentation`), injective intertwining maps
  (`Representation.IntertwiningMap.stabilizer_apply_of_injective`), and equivalences
  (`Representation.Equiv.stabilizer_apply`);
* restriction along a group homomorphism (`Representation.stabilizer_comp`), trivial and
  subsingleton representations, binary and arbitrary products (`Representation.stabilizer_prod`,
  `Representation.stabilizer_pi`), and quotients (`Representation.le_stabilizer_quotient_mk`,
  `Subrepresentation.le_stabilizer_quotient_mk`);
* permutation and left regular representations (`Representation.stabilizer_ofMulAction_single`,
  `Representation.stabilizer_leftRegular_single`, `Representation.finite_stabilizer_leftRegular`),
  trivial subgroup restrictions (`Representation.isTrivial_comp_subtype_iff` and
  `Representation.le_stabilizer_of_isTrivial_comp_subtype`), and coset permutation modules
  `A[G ⧸ N]`;
* the Galois-style correspondence `v ∈ invariants (ρ.comp H.subtype) ↔ H ≤ ρ.stabilizer v`
  linking stabilizers to subgroup invariants (`Representation.mem_invariants_comp_subtype_iff`).

## Main results

* `Subrepresentation.stabilizer_toRepresentation`
* `Representation.IntertwiningMap.stabilizer_apply_of_injective`
* `Representation.Equiv.stabilizer_apply`
* `Representation.stabilizer_comp`
* `Representation.stabilizer_prod` and `Representation.stabilizer_pi`
* `Representation.le_stabilizer_quotient_mk` and `Subrepresentation.le_stabilizer_quotient_mk`
* `Representation.stabilizer_ofMulAction_single` and `Representation.stabilizer_leftRegular_single`
* `Representation.finite_stabilizer_leftRegular`
* `Representation.isTrivial_comp_subtype_iff` and
  `Representation.le_stabilizer_of_isTrivial_comp_subtype`
* `Representation.mem_invariants_comp_subtype_iff`
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
  rw [Subrepresentation.quotient, Representation.quotient_apply, Submodule.mapQ_apply, hg]

end Subrepresentation

namespace Representation

section Semiring

variable {A G H V W : Type*} [Semiring A] [Group G] [Group H]
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

/-- An equivalence of representations preserves vector stabilizers. -/
@[simp]
theorem Equiv.stabilizer_apply (e : ρ.Equiv σ) (v : V) :
    σ.stabilizer (e v) = ρ.stabilizer v :=
  e.toIntertwiningMap.stabilizer_apply_of_injective e.injective v

/-- Restricting a representation along a group homomorphism pulls back vector stabilizers. -/
@[simp]
theorem stabilizer_comp (ρ : Representation A G V) (f : H →* G) (v : V) :
    stabilizer (ρ.comp f) v = (ρ.stabilizer v).comap f :=
  (rfl)

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

section Ring

variable {A G V : Type*} [Ring A] [Group G] [AddCommGroup V] [Module A V]

/-- Passing to a quotient representation can only enlarge the stabilizer of a vector. -/
theorem le_stabilizer_quotient_mk (ρ : Representation A G V) (W : Submodule A V)
    (hW : ∀ g, ∀ w ∈ W, ρ g w ∈ W) (v : V) :
    ρ.stabilizer v ≤ (ρ.quotient W hW).stabilizer (Submodule.Quotient.mk v) :=
  Subrepresentation.le_stabilizer_quotient_mk ⟨W, hW⟩ v

end Ring

section CommRing

variable {A G V : Type*} [CommRing A] [Group G] [AddCommGroup V] [Module A V]
  {ρ : Representation A G V}

/-- A vector is invariant under the restriction of `ρ` to a subgroup `H` exactly when `H` lies in
its stabilizer. -/
theorem mem_invariants_comp_subtype_iff {H : Subgroup G} {v : V} :
    v ∈ invariants (ρ.comp H.subtype) ↔ H ≤ ρ.stabilizer v := by
  simp [mem_invariants, IsConcreteLE.le_iff]

end CommRing

end Representation

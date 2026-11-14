/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Stabilizer
public import TauCeti.RepresentationTheory.Pi
import TauCeti.GroupTheory.QuotientGroup.Basic

/-!
# Vector stabilizers in representations

Mathlib's `Mathlib.RepresentationTheory.Stabilizer` introduces `Representation.stabilizer ρ v` and
records how it behaves under zero, scalar multiplication, addition, finite sums, intertwining maps,
and conjugation by group elements. This file supplies the remaining structural identities needed to
compute vector stabilizers across standard constructions on representations:

* subrepresentations (`Subrepresentation.stabilizer_toRepresentation`), injective intertwining maps
  (`Representation.IntertwiningMap.stabilizer_eq_of_injective`), and equivalences
  (`Representation.Equiv.stabilizer_apply`);
* restriction along a group homomorphism (`Representation.stabilizer_comp`), trivial and
  subsingleton representations, binary and arbitrary products (`Representation.stabilizer_prod`,
  `Representation.stabilizer_pi`), and quotients (`Representation.le_stabilizer_quotient_mk`,
  `Subrepresentation.le_stabilizer_quotient_mk`);
* permutation and left regular representations (`Representation.stabilizer_ofMulAction_single`,
  `Representation.stabilizer_leftRegular_single`, `Representation.finite_stabilizer_leftRegular`,
  and coset permutation modules `A[G ⧸ N]`);
* the Galois-style correspondence `H ≤ ρ.stabilizer v ↔ v ∈ invariants (ρ.comp H.subtype)`
  linking stabilizers to subgroup invariants
  (`Representation.le_stabilizer_iff_mem_invariants_comp_subtype`).

## Main results

* `Subrepresentation.stabilizer_toRepresentation`
* `Representation.IntertwiningMap.stabilizer_eq_of_injective`
* `Representation.Equiv.stabilizer_apply`
* `Representation.stabilizer_comp`
* `Representation.stabilizer_prod` and `Representation.stabilizer_pi`
* `Representation.le_stabilizer_quotient_mk` and `Subrepresentation.le_stabilizer_quotient_mk`
* `Representation.stabilizer_ofMulAction_single` and `Representation.stabilizer_leftRegular_single`
* `Representation.finite_stabilizer_leftRegular`
* `Representation.le_stabilizer_iff_mem_invariants_comp_subtype`
-/

public section

open scoped MonoidAlgebra

namespace Subrepresentation

/-- Restricting a representation to a subrepresentation leaves the stabilizer of each vector
unchanged. -/
@[simp]
theorem stabilizer_toRepresentation {A G V : Type*} [Semiring A] [Group G]
    [AddCommMonoid V] [Module A V] {ρ : Representation A G V} (S : Subrepresentation ρ)
    (v : S.toSubmodule) :
    S.toRepresentation.stabilizer v = ρ.stabilizer (v : V) := by
  ext g
  simp [Subrepresentation.toRepresentation_apply_coe]

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

/-- The carrier of `ρ.stabilizer v` is `{g : G | ρ g v = v}`. -/
theorem coe_stabilizer (ρ : Representation A G V) (v : V) :
    ((ρ.stabilizer v : Subgroup G) : Set G) = {g : G | ρ g v = v} :=
  (rfl)

/-- An injective intertwining map preserves the stabilizer of every vector. -/
theorem IntertwiningMap.stabilizer_eq_of_injective {ρ : Representation A G V}
    {σ : Representation A G W} (f : ρ.IntertwiningMap σ) (hf : Function.Injective f) (v : V) :
    σ.stabilizer (f v) = ρ.stabilizer v := by
  refine le_antisymm (fun g hg ↦ ?_) (f.stabilizer_le v)
  rw [mem_stabilizer] at hg ⊢
  exact hf ((IntertwiningMap.isIntertwining _ _ f g v).trans hg)

/-- An equivalence of representations preserves vector stabilizers. -/
@[simp]
theorem Equiv.stabilizer_apply {ρ : Representation A G V} {σ : Representation A G W}
    (e : ρ.Equiv σ) (v : V) :
    σ.stabilizer (e v) = ρ.stabilizer v :=
  e.toIntertwiningMap.stabilizer_eq_of_injective e.injective v

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
    (ρ.prod σ).stabilizer x = ρ.stabilizer x.1 ⊓ σ.stabilizer x.2 := by
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

/-- In a permutation representation `A[X]`, the stabilizer of a nonzero monomial `single x a` is
the point stabilizer of `x` in `G`. -/
@[simp]
theorem stabilizer_ofMulAction_single (x : X) {a : A} (ha : a ≠ 0) :
    (ofMulAction A G X).stabilizer (MonoidAlgebra.single x a) = MulAction.stabilizer G x := by
  classical
  refine le_antisymm (fun g hg ↦ ?_) (le_stabilizer_ofMulAction_single x a)
  rw [mem_stabilizer] at hg
  have hcoeff := congrArg (fun f : A[X] ↦ f.coeff (g • x)) hg
  simp only [ofMulAction_single, MonoidAlgebra.coeff_single, Finsupp.single_eq_same] at hcoeff
  by_contra hgx
  rw [MulAction.mem_stabilizer_iff] at hgx
  exact ha (by simpa [Ne.symm hgx] using hcoeff)

end MulAction

/-- In the left regular representation `A[G]`, any nonzero monomial `single g a` has trivial
stabilizer. -/
theorem stabilizer_leftRegular_single (g : G) {a : A} (ha : a ≠ 0) :
    (leftRegular A G).stabilizer (MonoidAlgebra.single g a) = ⊥ := by
  simp [ha]

/-- **Every nonzero vector in the left regular representation has finite stabilizer.** If `g`
fixes `x ≠ 0` in `A[G]`, then `g` translates any element `g₀` in the support of `x` to another
element of the finite support of `x`. -/
theorem finite_stabilizer_leftRegular {x : A[G]} (hx : x ≠ 0) :
    ((leftRegular A G).stabilizer x : Set G).Finite := by
  obtain ⟨g₀, hg₀⟩ := Finsupp.support_nonempty_iff.mpr (MonoidAlgebra.coeff_eq_zero.not.mpr hx)
  refine (x.coeff.support.finite_toSet.preimage (mul_left_injective g₀).injOn).subset fun h hh ↦ ?_
  rw [SetLike.mem_coe, mem_stabilizer] at hh
  have hcoeff := congrArg (fun y : A[G] ↦ y.coeff (h * g₀)) hh
  rw [coeff_ofMulAction, smul_eq_mul, inv_mul_cancel_left] at hcoeff
  exact Finset.mem_coe.mpr (Finsupp.mem_support_iff.mpr (hcoeff ▸ Finsupp.mem_support_iff.mp hg₀))

/-- For a normal subgroup `N` of `G`, the restriction of the coset permutation representation
`A[G ⧸ N]` to `N` is trivial. -/
instance instIsTrivialOfMulActionQuotientCompSubtype (N : Subgroup G) [N.Normal] :
    IsTrivial ((ofMulAction A G (G ⧸ N)).comp N.subtype) where
  out n := by
    ext x
    simp [Subgroup.smul_def, TauCeti.smul_quotient_eq_self_of_mem n.2]

/-- Every normal subgroup `N` of `G` is contained in the stabilizer of every vector of the coset
permutation representation `A[G ⧸ N]`. -/
theorem le_stabilizer_ofMulAction_quotient (N : Subgroup G) [N.Normal] (v : A[G ⧸ N]) :
    N ≤ (ofMulAction A G (G ⧸ N)).stabilizer v := fun g hg ↦
  LinearMap.congr_fun (isTrivial_def ((ofMulAction A G (G ⧸ N)).comp N.subtype) ⟨g, hg⟩) v

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

/-- A subgroup `H ≤ G` fixes a vector `v` (that is, `H ≤ ρ.stabilizer v`) if and only if `v` lies
in the `H`-invariants `invariants (ρ.comp H.subtype)`. -/
@[simp]
theorem le_stabilizer_iff_mem_invariants_comp_subtype (ρ : Representation A G V)
    (H : Subgroup G) (v : V) :
    H ≤ ρ.stabilizer v ↔ v ∈ invariants (ρ.comp H.subtype) := by
  simp [IsConcreteLE.le_iff]

end CommRing

end Representation

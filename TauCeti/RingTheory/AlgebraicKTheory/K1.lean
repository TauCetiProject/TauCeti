/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Abelianization.Defs
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Stable

/-!
# Algebraic `K₁` of a ring

For a possibly noncommutative ring `A`, **algebraic `K₁`** is the quotient
`K₁(A) = GL_∞(A) / E_∞(A)` of the stable general linear group by the stable elementary subgroup.
Since `E_∞(A)` is the commutator subgroup of `GL_∞(A)`
(`TauCeti.stableElementarySubgroup_eq_commutator`), `K₁(A)` is an abelian group, the
abelianization of `GL_∞(A)`.

Every class is represented by an invertible matrix of some finite size, and such a matrix
represents the trivial class exactly when it becomes elementary after stabilization. A family of
homomorphisms from the groups `GL (Fin n) A` to an abelian group which is compatible with
stabilization factors through `K₁(A)`; this is how invariants of invertible matrices, such as
Connes' odd pairing with cyclic cohomology, descend to `K₁`.

## Main definitions

* `TauCeti.AlgebraicK₁`: the abelian group `K₁(A) = GL_∞(A) / E_∞(A)`.
* `TauCeti.AlgebraicK₁.of`: the class map `GL (Fin n) A →* K₁(A)`.
* `TauCeti.AlgebraicK₁.lift`: the homomorphism out of `K₁(A)` induced by a compatible family of
  homomorphisms from the `GL (Fin n) A` to an abelian group.
* `TauCeti.AlgebraicK₁.equivAbelianization`: `K₁(A)` is the abelianization of `GL_∞(A)`.

## Main results

* `TauCeti.AlgebraicK₁.exists_of`: every class is represented by an invertible matrix.
* `TauCeti.AlgebraicK₁.of_eq_one_iff`: an invertible matrix has trivial class exactly when some
  stabilization of it is elementary.

## References

* J. Milnor, *Introduction to Algebraic K-Theory*, Annals of Mathematics Studies 72 (1971), §3.
* J. Rosenberg, *Algebraic K-Theory and Its Applications*, GTM 147 (1994), §2.1,
  Definition 2.1.5.
-/

public section

open scoped commutatorElement

namespace TauCeti

variable (A : Type*) [Ring A] {m n : ℕ}

/-- **Algebraic `K₁`** of a ring `A`: the quotient `GL_∞(A) / E_∞(A)` of the stable general linear
group by the stable elementary subgroup. -/
def AlgebraicK₁ : Type _ :=
  StableGL A ⧸ stableElementarySubgroup A

noncomputable instance : Group (AlgebraicK₁ A) :=
  inferInstanceAs (Group (StableGL A ⧸ stableElementarySubgroup A))

/-- `K₁(A)` is abelian, because `E_∞(A)` contains every commutator of `GL_∞(A)`. -/
noncomputable instance : CommGroup (AlgebraicK₁ A) where
  mul_comm x y := by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective (s := stableElementarySubgroup A) x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective (s := stableElementarySubgroup A) y
    refine QuotientGroup.eq.2 ?_
    -- `(x * y)⁻¹ * (y * x)` is the commutator `⁅y⁻¹, x⁻¹⁆`
    rw [stableElementarySubgroup_eq_commutator, show (x * y)⁻¹ * (y * x) = ⁅y⁻¹, x⁻¹⁆ by
      simp [commutatorElement_def, mul_assoc]]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

namespace AlgebraicK₁

/-- `K₁(A)` is the abelianization of `GL_∞(A)`. -/
noncomputable def equivAbelianization : AlgebraicK₁ A ≃* Abelianization (StableGL A) :=
  QuotientGroup.quotientMulEquivOfEq (stableElementarySubgroup_eq_commutator A)

/-- The class map `GL (Fin n) A →* K₁(A)`, sending an invertible matrix to its class. -/
noncomputable def of (n : ℕ) : GL (Fin n) A →* AlgebraicK₁ A :=
  (QuotientGroup.mk' (stableElementarySubgroup A)).comp (StableGL.of A n)

variable {A}

/-- The class of an invertible matrix is the class of its image in `GL_∞(A)`. -/
private theorem of_apply (u : GL (Fin n) A) :
    of A n u = (QuotientGroup.mk (s := stableElementarySubgroup A) (StableGL.of A n u) :
      StableGL A ⧸ stableElementarySubgroup A) :=
  (rfl)

/-- The equivalence with the abelianization sends the class of an invertible matrix to the class
of its image in `GL_∞(A)`. -/
@[simp]
theorem equivAbelianization_of (u : GL (Fin n) A) :
    equivAbelianization A (of A n u) = Abelianization.of (StableGL.of A n u) :=
  (rfl)

/-- The class of an invertible matrix does not change under stabilization. -/
@[simp]
theorem of_stabilizeGL (h : m ≤ n) (u : GL (Fin m) A) : of A n (stabilizeGL A h u) = of A m u := by
  rw [of_apply, of_apply, StableGL.of_stabilizeGL]

/-- Every class in `K₁(A)` is represented by an invertible matrix of some finite size. -/
theorem exists_of (x : AlgebraicK₁ A) : ∃ n u, of A n u = x := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective (s := stableElementarySubgroup A) x
  obtain ⟨n, u, rfl⟩ := StableGL.exists_of x
  exact ⟨n, u, rfl⟩

/-- **The kernel of the class map.** An invertible matrix has trivial class in `K₁(A)` exactly
when some stabilization of it is elementary. -/
theorem of_eq_one_iff {u : GL (Fin n) A} :
    of A n u = 1 ↔ ∃ k, ∃ h : n ≤ k, stabilizeGL A h u ∈ elementarySubgroup (Fin k) A := by
  have h1 : of A n u = 1 ↔ StableGL.of A n u ∈ stableElementarySubgroup A :=
    QuotientGroup.eq_one_iff (StableGL.of A n u)
  rw [h1, mem_stableElementarySubgroup_iff]
  constructor
  · rintro ⟨k, e, he, hek⟩
    -- stabilize `e` and `u` to a common size, where they agree
    refine ⟨max k n, le_max_right k n, ?_⟩
    rw [← StableGL.of_injective _ ((StableGL.of_stabilizeGL (le_max_left k n) e).trans
      (hek.trans (StableGL.of_stabilizeGL (le_max_right k n) u).symm))]
    exact stabilizeGL_mem_elementarySubgroup _ he
  · rintro ⟨k, h, hk⟩
    exact ⟨k, _, hk, StableGL.of_stabilizeGL h u⟩

/-- Two homomorphisms out of `K₁(A)` agreeing on the classes of invertible matrices are equal. -/
theorem hom_ext {G : Type*} [Group G] {f g : AlgebraicK₁ A →* G}
    (h : ∀ n, f.comp (of A n) = g.comp (of A n)) : f = g := by
  ext x
  obtain ⟨n, u, rfl⟩ := exists_of x
  exact DFunLike.congr_fun (h n) u

variable {C : Type*} [CommGroup C] (φ : ∀ n, GL (Fin n) A →* C)
  (hφ : ∀ m n (h : m ≤ n) u, φ n (stabilizeGL A h u) = φ m u)

/-- **The universal property of `K₁(A)`.** Homomorphisms from the groups `GL (Fin n) A` to an
abelian group which are compatible with stabilization induce a homomorphism out of `K₁(A)`: they
vanish on `E_∞(A)` because it is the commutator subgroup. -/
noncomputable def lift : AlgebraicK₁ A →* C :=
  QuotientGroup.lift (stableElementarySubgroup A) (StableGL.lift φ hφ) <| by
    rw [stableElementarySubgroup_eq_commutator]
    exact Abelianization.commutator_le_ker _

/-- The homomorphism induced on `K₁(A)` sends the class of an invertible matrix to its value. -/
@[simp]
theorem lift_of (u : GL (Fin n) A) : lift φ hφ (of A n u) = φ n u :=
  (QuotientGroup.lift_mk _ _ _).trans (StableGL.lift_of φ hφ n u)

/-- The homomorphism induced on `K₁(A)` restricts to the given ones. -/
@[simp]
theorem lift_comp_of (n : ℕ) : (lift φ hφ).comp (of A n) = φ n :=
  MonoidHom.ext (lift_of φ hφ)

end AlgebraicK₁

end TauCeti

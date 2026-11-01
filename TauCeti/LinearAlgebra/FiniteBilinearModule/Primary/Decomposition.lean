/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.Primary.Decomposition
public import TauCeti.LinearAlgebra.FiniteBilinearModule.Primary.Component

/-!
# Primary decomposition of finite bilinear and quadratic modules

This file upgrades the primary decomposition of the underlying finite abelian group to the
form-theoretic decompositions used for discriminant forms. For a finite bilinear module, its
primary components form an orthogonal product whose pairing is the sum of the restricted
pairings. For a finite quadratic module, the analogous quadratic map is the sum of the restricted
quadratic maps.

The canonical additive equivalence is an isometry in both settings. This follows from the
orthogonality and finite-sum identities proved in
`TauCeti.LinearAlgebra.FiniteBilinearModule.Primary.Component`.

## Main results

* `TauCeti.FiniteBilinearModule.primaryDecomposition`: the canonical primary decomposition as a
  bilinear isometry.
* `TauCeti.FiniteQuadraticModule.primaryDecomposition`: the canonical primary decomposition as a
  quadratic isometry.
* `TauCeti.FiniteBilinearModule.isNondegenerate_primaryComponents` and
  `TauCeti.FiniteQuadraticModule.isNondegenerate_primaryComponents`: nondegeneracy is equivalent
  to nondegeneracy of the orthogonal product.
* `TauCeti.FiniteBilinearModule.nonempty_isometry_of_forall_primaryComponent` and
  `TauCeti.FiniteQuadraticModule.nonempty_isometry_of_forall_primaryComponent`: two modules of the
  same order are isometric when their primary components are isometric at every prime.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, §1.1.
* W. Ebeling, *Lattices and Codes*, Chapter 1.
-/

public section

open AddCommGroup

namespace TauCeti

namespace FiniteBilinearModule

variable (A : FiniteBilinearModule)

/-- The orthogonal product of the prime-primary restrictions of a finite bilinear module. -/
@[expose] noncomputable def primaryComponents : FiniteBilinearModule where
  carrier := ∀ p : (Nat.card A).primeFactors,
    AddCommGroup.primaryComponent A p.1
  pairing :=
    { toFun := fun x ↦
        { toFun := fun y ↦ ∑ p, A.pairing (x p) (y p)
          map_zero' := by simp
          map_add' := fun y z ↦ by
            simp only [Pi.add_apply, AddSubgroup.coe_add, pairing_add_right,
              Finset.sum_add_distrib] }
      map_zero' := by
        ext y
        -- Expose the pointwise formula while constructing the bundled pairing itself.
        change ∑ p, A.pairing 0 (y p) = 0
        apply Finset.sum_eq_zero
        intro p _
        exact A.pairing_zero_left (y p)
      map_add' := fun x y ↦ by
        ext z
        -- Expose the pointwise formula while constructing the bundled pairing itself.
        change ∑ p, A.pairing (x p + y p) (z p) =
          (∑ p, A.pairing (x p) (z p)) + ∑ p, A.pairing (y p) (z p)
        simp only [pairing_add_left, Finset.sum_add_distrib] }
  pairing_comm x y := by
    -- Expose the pointwise formula while proving the final structure field.
    change (∑ p, A.pairing (x p) (y p)) = ∑ p, A.pairing (y p) (x p)
    apply Finset.sum_congr rfl
    intro p _
    exact A.pairing_comm (x p) (y p)

/-- The pairing on the orthogonal product is the sum of the component pairings. -/
@[simp]
theorem primaryComponents_pairing (x y : A.primaryComponents) :
    A.primaryComponents.pairing x y = ∑ p, A.pairing (x p) (y p) := by
  rfl

/-- The canonical primary decomposition is a bilinear isometry. -/
noncomputable def primaryDecomposition : Isometry A.primaryComponents A where
  toAddEquiv := AddCommGroup.primaryDecomposition A
  map_pairing' x y := by
    -- Unfolding the carrier variables and goal together aligns the bundled carrier's synthesized
    -- additive instance with the dependent-product instance used by the group decomposition.
    unfold primaryComponents at x y ⊢
    rw [AddCommGroup.primaryDecomposition_apply, AddCommGroup.primaryDecomposition_apply]
    change A.pairing (∑ p, (x p : A)) (∑ p, (y p : A)) =
      ∑ p, A.pairing (x p) (y p)
    exact A.pairing_sum_eq_sum_pairing_of_mem_primaryComponent
      Finset.univ Subtype.val (fun p ↦ x p) (fun p ↦ y p)
      (fun p _ ↦ Nat.prime_of_mem_primeFactors p.2)
      (fun p _ q _ hpq ↦ by simpa using hpq)
      (fun p _ ↦ (x p).2) (fun p _ ↦ (y p).2)

/-- The bilinear primary-decomposition isometry maps a tuple to its component sum. -/
@[simp]
theorem primaryDecomposition_apply (x : A.primaryComponents) :
    A.primaryDecomposition x = ∑ p, (x p : A) :=
  AddCommGroup.primaryDecomposition_apply A x

/-- The orthogonal product of primary components is nondegenerate exactly when the original
finite bilinear module is nondegenerate. -/
@[simp]
theorem isNondegenerate_primaryComponents :
    A.primaryComponents.IsNondegenerate ↔ A.IsNondegenerate :=
  A.primaryDecomposition.isNondegenerate_iff

/-- Equal orders give the same index set of prime factors. -/
private def primeFactorsEquiv {A B : FiniteBilinearModule} (hcard : Nat.card A = Nat.card B) :
    (Nat.card A).primeFactors ≃ (Nat.card B).primeFactors :=
  Equiv.subtypeEquivRight fun p ↦ by rw [hcard]

/-- Additive equivalences of the primary components of two finite abelian groups of the same order
assemble to an additive equivalence of the products of their primary components: reindex along
`primeFactorsEquiv`, then apply the given equivalence componentwise. -/
private noncomputable def primaryComponentsAddEquiv {A B : FiniteBilinearModule}
    (hcard : Nat.card A = Nat.card B)
    (f : ∀ p : ℕ, p.Prime → primaryComponent A p ≃+ primaryComponent B p) :
    A.primaryComponents ≃+ B.primaryComponents :=
  (LinearEquiv.piCongrLeft' ℤ (fun p : (Nat.card A).primeFactors ↦ primaryComponent A p.1)
    (primeFactorsEquiv hcard)).toAddEquiv.trans
    (AddEquiv.piCongrRight fun q ↦ f q.1 (Nat.prime_of_mem_primeFactors q.2))

/-- `primaryComponentsAddEquiv` applies the given equivalence to the reindexed component. This is
`LinearEquiv.piCongrLeft'_apply` followed by `AddEquiv.piCongrRight_apply`, stated for the bundled
carrier `primaryComponents` so that it rewrites in the isometry proofs below. -/
private theorem primaryComponentsAddEquiv_apply {A B : FiniteBilinearModule}
    (hcard : Nat.card A = Nat.card B)
    (f : ∀ p : ℕ, p.Prime → primaryComponent A p ≃+ primaryComponent B p)
    (x : A.primaryComponents) (q : (Nat.card B).primeFactors) :
    primaryComponentsAddEquiv hcard f x q =
      f q.1 (Nat.prime_of_mem_primeFactors q.2) (x ((primeFactorsEquiv hcard).symm q)) :=
  rfl

/-- **Primary components decide isometry.** Two finite bilinear modules of the same order are
isometric as soon as, at every prime `p`, their `p`-primary components are isometric. -/
theorem nonempty_isometry_of_forall_primaryComponent {A B : FiniteBilinearModule}
    (hcard : Nat.card A = Nat.card B)
    (h : ∀ p : ℕ, p.Prime →
      Nonempty (Isometry (A.restrict (primaryComponent A p)) (B.restrict (primaryComponent B p)))) :
    Nonempty (Isometry A B) := by
  let f p hp := (h p hp).some
  let g := primaryComponentsAddEquiv hcard fun p hp ↦ (f p hp).toAddEquiv
  refine ⟨A.primaryDecomposition.symm.trans (Isometry.trans ⟨g, fun x y ↦ ?_⟩
    B.primaryDecomposition)⟩
  rw [primaryComponents_pairing, primaryComponents_pairing]
  exact Fintype.sum_equiv (primeFactorsEquiv hcard).symm _ _ fun q ↦ by
    rw [primaryComponentsAddEquiv_apply, primaryComponentsAddEquiv_apply]
    exact (f q.1 (Nat.prime_of_mem_primeFactors q.2)).map_pairing _ _

end FiniteBilinearModule

namespace FiniteQuadraticModule

variable (A : FiniteQuadraticModule)

/-- The orthogonal product of the prime-primary restrictions of a finite quadratic module. -/
@[expose] noncomputable def primaryComponents : FiniteQuadraticModule where
  toFiniteBilinearModule := A.toFiniteBilinearModule.primaryComponents
  quadratic := ∑ p : (Nat.card A).primeFactors,
    (A.restrict (AddCommGroup.primaryComponent A p.1)).quadratic.comp (LinearMap.proj p)
  polar_eq_pairing' x y := by
    simp only [QuadraticMap.polar, sum_apply]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p _
    exact A.polar_eq_pairing (x p) (y p)

/-- The quadratic map on the orthogonal product is the sum of the component quadratic maps. -/
@[simp]
theorem primaryComponents_quadratic (x : A.primaryComponents) :
    A.primaryComponents.quadratic x = ∑ p, A.quadratic (x p) := by
  -- Unfold the carrier together with the structure so the dependent-product module instances
  -- used by `QuadraticMap.sum_apply` agree definitionally.
  unfold FiniteQuadraticModule.primaryComponents at x ⊢
  unfold FiniteBilinearModule.primaryComponents at x ⊢
  rw [sum_apply]
  apply Finset.sum_congr rfl
  intro p _
  rfl

/-- The canonical primary decomposition is a quadratic isometry. -/
noncomputable def primaryDecomposition : Isometry A.primaryComponents A where
  toLinearEquiv := (AddCommGroup.primaryDecomposition A).toIntLinearEquiv
  map_app' x := by
    -- Unfolding the carrier variable and goal together aligns the bundled carrier's synthesized
    -- module instance with the dependent-product instance used by the group decomposition.
    unfold FiniteQuadraticModule.primaryComponents at x ⊢
    unfold FiniteBilinearModule.primaryComponents at x ⊢
    rw [sum_apply]
    change A.quadratic (AddCommGroup.primaryDecomposition A x) =
      ∑ p, A.quadratic (x p)
    rw [AddCommGroup.primaryDecomposition_apply]
    exact A.quadratic_sum_of_mem_primaryComponent Finset.univ Subtype.val (fun p ↦ x p)
      (fun p _ ↦ Nat.prime_of_mem_primeFactors p.2)
      (fun p _ q _ hpq ↦ by simpa using hpq)
      (fun p _ ↦ (x p).2)

/-- The quadratic primary-decomposition isometry maps a tuple to its component sum. -/
@[simp]
theorem primaryDecomposition_apply (x : A.primaryComponents) :
    A.primaryDecomposition x = ∑ p, (x p : A) :=
  AddCommGroup.primaryDecomposition_apply A x

/-- The orthogonal product of primary components is nondegenerate exactly when the original
finite quadratic module is nondegenerate. -/
@[simp]
theorem isNondegenerate_primaryComponents :
    A.primaryComponents.IsNondegenerate ↔ A.IsNondegenerate :=
  A.primaryDecomposition.isNondegenerate_iff

/-- **Primary components decide isometry.** Two finite quadratic modules of the same order are
isometric as soon as, at every prime `p`, their `p`-primary components are isometric. -/
theorem nonempty_isometry_of_forall_primaryComponent {A B : FiniteQuadraticModule}
    (hcard : Nat.card A = Nat.card B)
    (h : ∀ p : ℕ, p.Prime →
      Nonempty (Isometry (A.restrict (primaryComponent A p)) (B.restrict (primaryComponent B p)))) :
    Nonempty (Isometry A B) := by
  let f p hp := (h p hp).some
  let g := FiniteBilinearModule.primaryComponentsAddEquiv hcard fun p hp ↦
    (f p hp).toLinearEquiv.toAddEquiv
  refine ⟨A.primaryDecomposition.symm.trans
    ((⟨g.toIntLinearEquiv, fun x ↦ ?_⟩ : Isometry _ _).trans B.primaryDecomposition)⟩
  rw [primaryComponents_quadratic, primaryComponents_quadratic]
  -- The coercion of `g.toIntLinearEquiv` is `g` (`AddEquiv.coe_toIntLinearEquiv` is `rfl`).
  exact Fintype.sum_equiv (FiniteBilinearModule.primeFactorsEquiv hcard).symm _ _ fun q ↦
    (congrArg (fun y : primaryComponent B.carrier q.1 ↦ B.quadratic y)
      (FiniteBilinearModule.primaryComponentsAddEquiv_apply hcard _ x q)).trans
      ((f q.1 (Nat.prime_of_mem_primeFactors q.2)).map_app _)

end FiniteQuadraticModule

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.BigOperators.Ring.Int
public import TauCeti.LinearAlgebra.WeightedCycle.Family.Basic
public import TauCeti.LinearAlgebra.Pi

/-!
# Integral signs and fixed vectors of a basis-cycle family

The monodromy signs partition the cycles over the integers. Positive cycles
contribute one scalar coordinate; negative cycles contribute the full
`2`-torsion submodule. This partition is unchanged in characteristic two,
where the two integer signs have the same image in the coefficient ring.
-/

public section

open TauCeti.WeightedCycle

namespace Module.Basis

variable {A V ι J : Type*} {n : J → ℕ}

private def negativeIndexEquiv (ε : ∀ j, Fin (n j + 1) → ℤ)
    (hε : ∀ j i, ε j i = 1 ∨ ε j i = -1) :
    {j // (∏ i, ε j i) ≠ 1} ≃ {j // (∏ i, ε j i) = -1} :=
  Equiv.subtypeEquivRight fun j ↦
    Int.prod_ne_one_iff_eq_neg_one (fun i _ ↦ hε j i)

variable [CommRing A] [AddCommGroup V] [Module A V]

private noncomputable def fixedSignedTuplesEquiv (ε : ∀ j, Fin (n j + 1) → ℤ)
    (hε : ∀ j i, ε j i = 1 ∨ ε j i = -1) :
    (∀ j, (TauCeti.WeightedCycle.linearMap (fun i ↦ (ε j i : A)) (M := A)).fixedSubmodule) ≃ₗ[A]
      ({j // (∏ i, ε j i) = 1} → A) ×
        ({j // (∏ i, ε j i) = -1} → Submodule.torsionBy A A 2) := by
  classical
  let pos : (∀ j : {j // (∏ i, ε j i) = 1},
      (TauCeti.WeightedCycle.linearMap (fun i ↦ (ε j.val i : A)) (M := A)).fixedSubmodule) ≃ₗ[A]
      ({j // (∏ i, ε j i) = 1} → A) :=
    LinearEquiv.piCongrRight fun j ↦ fixedEquivOfProdEqOne
      (fun i ↦ (ε j.val i : A)) (by
        simpa using congrArg (Int.castRingHom A) j.property)
  let neg : (∀ j : {j // (∏ i, ε j i) ≠ 1},
      (TauCeti.WeightedCycle.linearMap (fun i ↦ (ε j.val i : A)) (M := A)).fixedSubmodule) ≃ₗ[A]
      ({j // (∏ i, ε j i) ≠ 1} → Submodule.torsionBy A A 2) :=
    LinearEquiv.piCongrRight fun j ↦ fixedEquivOfProdEqNegOne
      (fun i ↦ (ε j.val i : A)) (by
        have hj : (∏ i, ε j.val i) = -1 := ((negativeIndexEquiv ε hε) j).property
        simpa using congrArg (Int.castRingHom A) hj)
  exact ((LinearEquiv.piEquivPiSubtypeProd A (fun j ↦ (∏ i, ε j i) = 1)
    (fun j ↦ (TauCeti.WeightedCycle.linearMap (fun i ↦ (ε j i : A)) (M := A)).fixedSubmodule)).trans
      (pos.prodCongr neg)).trans
        ((LinearEquiv.refl A _).prodCongr
          (LinearEquiv.piCongrLeft' A (fun _ ↦ Submodule.torsionBy A A 2)
            (negativeIndexEquiv ε hε)))

/-- The integral monodromy partition identifies the actual fixed module with positive
scalar coordinates and negative `2`-torsion coordinates over every commutative ring. -/
noncomputable def fixedEquivSignedFamily [Finite J] (b : Module.Basis ι A V)
    (e : (Σ j, Fin (n j + 1)) ≃ ι) (ε : ∀ j, Fin (n j + 1) → ℤ)
    (hε : ∀ j i, ε j i = 1 ∨ ε j i = -1) (f : V →ₗ[A] V)
    (h : ∀ j i, f (b (e ⟨j, i⟩)) = (ε j i : A) • b (e ⟨j, finRotate (n j + 1) i⟩)) :
    f.fixedSubmodule ≃ₗ[A] ({j // (∏ i, ε j i) = 1} → A) ×
      ({j // (∏ i, ε j i) = -1} → Submodule.torsionBy A A 2) :=
  (fixedFamilyEquiv b e (fun j i ↦ (ε j i : A)) f h).trans
    (fixedSignedTuplesEquiv ε hε)

/-- A positive cycle contributes its initial coefficient in the original basis. -/
@[simp]
theorem fixedEquivSignedFamily_apply_pos [Finite J] (b : Module.Basis ι A V)
    (e : (Σ j, Fin (n j + 1)) ≃ ι) (ε : ∀ j, Fin (n j + 1) → ℤ)
    (hε : ∀ j i, ε j i = 1 ∨ ε j i = -1) (f : V →ₗ[A] V)
    (h : ∀ j i, f (b (e ⟨j, i⟩)) = (ε j i : A) • b (e ⟨j, finRotate (n j + 1) i⟩))
    (v : f.fixedSubmodule) (j : {j // (∏ i, ε j i) = 1}) :
    (fixedEquivSignedFamily b e ε hε f h v).1 j = b.repr v.val (e ⟨j.val, 0⟩) := by
  simp [fixedEquivSignedFamily, fixedSignedTuplesEquiv]

/-- A negative cycle contributes its initial coefficient, including any nonzero `2`-torsion. -/
@[simp]
theorem fixedEquivSignedFamily_apply_neg [Finite J] (b : Module.Basis ι A V)
    (e : (Σ j, Fin (n j + 1)) ≃ ι) (ε : ∀ j, Fin (n j + 1) → ℤ)
    (hε : ∀ j i, ε j i = 1 ∨ ε j i = -1) (f : V →ₗ[A] V)
    (h : ∀ j i, f (b (e ⟨j, i⟩)) = (ε j i : A) • b (e ⟨j, finRotate (n j + 1) i⟩))
    (v : f.fixedSubmodule) (j : {j // (∏ i, ε j i) = -1}) :
    ((fixedEquivSignedFamily b e ε hε f h v).2 j : A) =
      b.repr v.val (e ⟨j.val, 0⟩) := by
  simp [fixedEquivSignedFamily, fixedSignedTuplesEquiv, negativeIndexEquiv,
    Equiv.subtypeEquivRight_symm_apply]

/-- Inverting the signed classification gives the prefix coefficients on a positive cycle. -/
@[simp]
theorem fixedEquivSignedFamily_symm_repr_pos [Finite J] (b : Module.Basis ι A V)
    (e : (Σ j, Fin (n j + 1)) ≃ ι) (ε : ∀ j, Fin (n j + 1) → ℤ)
    (hε : ∀ j i, ε j i = 1 ∨ ε j i = -1) (f : V →ₗ[A] V)
    (h : ∀ j i, f (b (e ⟨j, i⟩)) = (ε j i : A) • b (e ⟨j, finRotate (n j + 1) i⟩))
    (t : ({j // (∏ i, ε j i) = 1} → A) ×
      ({j // (∏ i, ε j i) = -1} → Submodule.torsionBy A A 2))
    (j : {j // (∏ i, ε j i) = 1}) (i : Fin (n j.val + 1)) :
    b.repr ((fixedEquivSignedFamily b e ε hε f h).symm t).val (e ⟨j.val, i⟩) =
      Fin.partialProd (Fin.init (fun k ↦ (ε j.val k : A))) i * t.1 j := by
  simp [fixedEquivSignedFamily, fixedSignedTuplesEquiv, j.property]

/-- Negative cycles retain the full `2`-torsion coordinate in the inverse basis coefficients. -/
@[simp]
theorem fixedEquivSignedFamily_symm_repr_neg [Finite J] (b : Module.Basis ι A V)
    (e : (Σ j, Fin (n j + 1)) ≃ ι) (ε : ∀ j, Fin (n j + 1) → ℤ)
    (hε : ∀ j i, ε j i = 1 ∨ ε j i = -1) (f : V →ₗ[A] V)
    (h : ∀ j i, f (b (e ⟨j, i⟩)) = (ε j i : A) • b (e ⟨j, finRotate (n j + 1) i⟩))
    (t : ({j // (∏ i, ε j i) = 1} → A) ×
      ({j // (∏ i, ε j i) = -1} → Submodule.torsionBy A A 2))
    (j : {j // (∏ i, ε j i) = -1}) (i : Fin (n j.val + 1)) :
    b.repr ((fixedEquivSignedFamily b e ε hε f h).symm t).val (e ⟨j.val, i⟩) =
      Fin.partialProd (Fin.init (fun k ↦ (ε j.val k : A))) i * (t.2 j).val := by
  have hj : (∏ k, ε j.val k) ≠ 1 := by
    rw [j.property]
    norm_num
  simp [fixedEquivSignedFamily, fixedSignedTuplesEquiv, negativeIndexEquiv, hj,
    Equiv.subtypeEquivRight_apply]

/-- The inverse signed classification is the sum of the positive and negative cycle
expansions in the original basis, including the negative `2`-torsion terms. -/
theorem fixedEquivSignedFamily_symm_apply [Fintype J] (b : Module.Basis ι A V)
    (e : (Σ j, Fin (n j + 1)) ≃ ι) (ε : ∀ j, Fin (n j + 1) → ℤ)
    (hε : ∀ j i, ε j i = 1 ∨ ε j i = -1) (f : V →ₗ[A] V)
    (h : ∀ j i, f (b (e ⟨j, i⟩)) = (ε j i : A) • b (e ⟨j, finRotate (n j + 1) i⟩))
    (t : ({j // (∏ i, ε j i) = 1} → A) ×
      ({j // (∏ i, ε j i) = -1} → Submodule.torsionBy A A 2)) :
    ((fixedEquivSignedFamily b e ε hε f h).symm t).val =
      (∑ j : {j // (∏ i, ε j i) = 1}, ∑ i,
        (Fin.partialProd (Fin.init (fun k ↦ (ε j.val k : A))) i * t.1 j) •
          b (e ⟨j.val, i⟩)) +
      ∑ j : {j // (∏ i, ε j i) = -1}, ∑ i,
        (Fin.partialProd (Fin.init (fun k ↦ (ε j.val k : A))) i * (t.2 j).val) •
          b (e ⟨j.val, i⟩) := by
  classical
  let v := (fixedEquivSignedFamily b e ε hε f h).symm t
  have hv : v.val = ∑ j, ∑ i, b.repr v.val (e ⟨j, i⟩) • b (e ⟨j, i⟩) := by
    simpa only [LinearEquiv.symm_apply_apply, fixedFamilyEquiv_apply] using
      fixedFamilyEquiv_symm_apply b e (fun j i ↦ (ε j i : A)) f h
        (fixedFamilyEquiv b e (fun j i ↦ (ε j i : A)) f h v)
  rw [hv, ← Fintype.sum_subtype_add_sum_subtype (fun j ↦ (∏ i, ε j i) = 1)]
  congr 1
  · apply Finset.sum_congr rfl
    intro j _
    simp only [v, fixedEquivSignedFamily_symm_repr_pos]
  · rw [← (negativeIndexEquiv ε hε).sum_comp]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    exact congrArg (fun c : A ↦ c • b (e ⟨j.val, i⟩))
      (fixedEquivSignedFamily_symm_repr_neg b e ε hε f h t
        ((negativeIndexEquiv ε hε) j) i)

end Module.Basis

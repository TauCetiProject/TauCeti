/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.BigOperators.Ring.Int
public import TauCeti.Algebra.Module.Torsion.Int
public import TauCeti.LinearAlgebra.WeightedCycle.Family.Basic
public import TauCeti.LinearAlgebra.Pi

/-!
# Integral signs and fixed vectors of a basis-cycle family

The monodromy signs partition the cycles over the integers. Positive cycles
contribute one scalar coordinate; negative cycles contribute the full
`2`-torsion submodule. This partition is unchanged in characteristic two,
where the two integer signs have the same image in the coefficient ring.
Over the integers, negative coordinates vanish, and the positive cycles give
an explicit basis of the fixed submodule.
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

section Integral

variable [Finite J]
variable (b : Module.Basis ι ℤ V) (e : (Σ j, Fin (n j + 1)) ≃ ι)
  (ε : ∀ j, Fin (n j + 1) → ℤ) (hε : ∀ j i, ε j i = 1 ∨ ε j i = -1)
  (f : V →ₗ[ℤ] V)
  (h : ∀ j i, f (b (e ⟨j, i⟩)) = ε j i • b (e ⟨j, finRotate (n j + 1) i⟩))

/-- Integral fixed vectors are determined by the initial coefficients on positive cycles. -/
noncomputable def fixedEquivPositiveSignedFamily :
    f.fixedSubmodule ≃ₗ[ℤ] ({j // (∏ i, ε j i) = 1} → ℤ) := by
  letI : Subsingleton (Submodule.torsionBy ℤ ℤ 2) := TauCeti.subsingleton_torsionBy_int 2 ℤ
  letI := uniqueOfSubsingleton (0 : Submodule.torsionBy ℤ ℤ 2)
  exact (b.fixedEquivSignedFamily e ε hε f h).trans LinearEquiv.prodUnique

/-- Positive integral fixed coordinates read the original initial basis coefficients. -/
@[simp]
theorem fixedEquivPositiveSignedFamily_apply (v : f.fixedSubmodule)
    (j : {j // (∏ i, ε j i) = 1}) :
    b.fixedEquivPositiveSignedFamily e ε hε f h v j = b.repr v.val (e ⟨j.val, 0⟩) := by
  exact b.fixedEquivSignedFamily_apply_pos e ε hε f h v j

/-- The inverse positive-coordinate map has zero negative coordinates. -/
theorem fixedEquivPositiveSignedFamily_symm (t : {j // (∏ i, ε j i) = 1} → ℤ) :
    (b.fixedEquivPositiveSignedFamily e ε hε f h).symm t =
      (b.fixedEquivSignedFamily e ε hε f h).symm (t, 0) := by
  rfl

/-- An integral positive-cycle basis of the actual fixed submodule. -/
noncomputable def fixedBasisSignedFamily :
    Module.Basis {j // (∏ i, ε j i) = 1} ℤ f.fixedSubmodule :=
  Module.Basis.ofEquivFun (b.fixedEquivPositiveSignedFamily e ε hε f h)

/-- Coordinates in the integral fixed basis are the original initial coefficients. -/
@[simp]
theorem fixedBasisSignedFamily_repr (v : f.fixedSubmodule)
    (j : {j // (∏ i, ε j i) = 1}) :
    (b.fixedBasisSignedFamily e ε hε f h).repr v j = b.repr v.val (e ⟨j.val, 0⟩) := by
  simp [fixedBasisSignedFamily]

/-- The positive coordinate equivalence is the coordinate map of the integral fixed basis. -/
@[simp]
theorem fixedBasisSignedFamily_equivFun :
    (b.fixedBasisSignedFamily e ε hε f h).equivFun =
      b.fixedEquivPositiveSignedFamily e ε hε f h := by
  simp [fixedBasisSignedFamily]

include hε h in
/-- A negative-cycle initial coefficient of an integral fixed vector is zero. -/
theorem fixedSignedFamily_repr_neg (v : f.fixedSubmodule)
    (j : {j // (∏ i, ε j i) = -1}) :
    b.repr v.val (e ⟨j.val, 0⟩) = 0 := by
  let : Subsingleton (Submodule.torsionBy ℤ ℤ 2) := TauCeti.subsingleton_torsionBy_int 2 ℤ
  rw [← b.fixedEquivSignedFamily_apply_neg e ε hε f h v j]
  exact congrArg Subtype.val (Subsingleton.elim _ 0)

/-- The integral fixed basis vector has the prescribed prefix coefficients on positive cycles. -/
@[simp]
theorem fixedBasisSignedFamily_repr_pos [DecidableEq {j // (∏ i, ε j i) = 1}]
    (j k : {j // (∏ i, ε j i) = 1}) (i : Fin (n k.val + 1)) :
    b.repr (b.fixedBasisSignedFamily e ε hε f h j).val (e ⟨k.val, i⟩) =
      Fin.partialProd (Fin.init (ε k.val)) i * (if j = k then 1 else 0) := by
  simp only [fixedBasisSignedFamily, Module.Basis.coe_ofEquivFun,
    fixedEquivPositiveSignedFamily_symm]
  by_cases hj : j = k <;> simp [hj]

/-- Every coefficient on a negative cycle of an integral fixed basis vector vanishes. -/
@[simp]
theorem fixedBasisSignedFamily_repr_neg
    (j : {j // (∏ i, ε j i) = 1}) (k : {j // (∏ i, ε j i) = -1})
    (i : Fin (n k.val + 1)) :
    b.repr (b.fixedBasisSignedFamily e ε hε f h j).val (e ⟨k.val, i⟩) = 0 := by
  classical
  simp only [fixedBasisSignedFamily, Module.Basis.coe_ofEquivFun,
    fixedEquivPositiveSignedFamily_symm]
  simp

/-- Each integral fixed basis vector is the signed prefix sum along its positive cycle. -/
theorem fixedBasisSignedFamily_apply (j : {j // (∏ i, ε j i) = 1}) :
    (b.fixedBasisSignedFamily e ε hε f h j).val =
      ∑ i, Fin.partialProd (Fin.init (ε j.val)) i • b (e ⟨j.val, i⟩) := by
  classical
  let := Fintype.ofFinite J
  simp [fixedBasisSignedFamily, Module.Basis.coe_ofEquivFun,
    fixedEquivPositiveSignedFamily_symm, fixedEquivSignedFamily_symm_apply, Pi.single_apply]

end Integral

end Module.Basis

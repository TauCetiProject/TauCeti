/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.WeightedCycle.Basic
public import TauCeti.LinearAlgebra.FixedSubmodule
public import Mathlib.LinearAlgebra.Basis.Defs

/-!
# Fixed vectors of a family of weighted basis cycles

A supplied partition of a whole basis into nonempty weighted cycles identifies
fixed vectors with a product of single-cycle fixed modules. Over a commutative
ring, the initial coefficients lie in the torsion submodules for monodromy minus
one. The inverse is the actual basis expansion with prefix-product coefficients.
The family may be empty, and weights need not be invertible.
-/

public section

open TauCeti.WeightedCycle

namespace Module.Basis

variable {A V ι J : Type*} {n : J → ℕ}

section CommSemiring

variable [CommSemiring A] [AddCommMonoid V] [Module A V]

/-- Curried basis coordinates intertwine the given family action with its componentwise
weighted shifts. The enumeration exhausts the whole basis. -/
theorem equivFun_comp_eq_piMap_comp [Finite J] (b : Module.Basis ι A V)
    (e : (Σ j, Fin (n j + 1)) ≃ ι) (a : ∀ j, Fin (n j + 1) → A) (f : V →ₗ[A] V)
    (h : ∀ j i, f (b (e ⟨j, i⟩)) = a j i • b (e ⟨j, finRotate (n j + 1) i⟩)) :
    ((b.reindex e.symm).equivFun.trans
      (LinearEquiv.piCurry A fun j (_ : Fin (n j + 1)) ↦ A)).toLinearMap ∘ₗ f =
      (LinearMap.piMap fun j ↦ linearMap (a j)) ∘ₗ
        ((b.reindex e.symm).equivFun.trans
          (LinearEquiv.piCurry A fun j (_ : Fin (n j + 1)) ↦ A)).toLinearMap := by
  classical
  apply (b.reindex e.symm).ext
  rintro ⟨j, i⟩
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.trans_apply]
  have hi : f ((b.reindex e.symm) ⟨j, i⟩) = a j i •
      (b.reindex e.symm) ⟨j, finRotate (n j + 1) i⟩ := by
    simpa using h j i
  rw [hi, map_smul, map_smul]
  funext k l
  obtain ⟨r, rfl⟩ := (finRotate (n k + 1)).surjective l
  simp only [LinearEquiv.piCurry_apply, Sigma.curry, Pi.smul_apply, smul_eq_mul,
    LinearMap.coe_piMap, Pi.map]
  rw [linearMap_apply_rotate]
  simp only [Sigma.curry]
  by_cases hj : j = k
  · subst k
    simp only [equivFun_self, smul_eq_mul]
    by_cases hir : i = r <;> simp [hir]
  · simp [hj]

/-- Fixed vectors in the original module give one native fixed tuple per cycle. -/
noncomputable def fixedFamilyEquiv [Finite J] (b : Module.Basis ι A V)
    (e : (Σ j, Fin (n j + 1)) ≃ ι) (a : ∀ j, Fin (n j + 1) → A) (f : V →ₗ[A] V)
    (h : ∀ j i, f (b (e ⟨j, i⟩)) = a j i • b (e ⟨j, finRotate (n j + 1) i⟩)) :
    f.fixedSubmodule ≃ₗ[A] ∀ j, (linearMap (a j) (M := A)).fixedSubmodule :=
  (((b.reindex e.symm).equivFun.trans
    (LinearEquiv.piCurry A fun j (_ : Fin (n j + 1)) ↦ A)).fixedSubmoduleCongr
      (equivFun_comp_eq_piMap_comp b e a f h)).trans
    (LinearMap.fixedSubmodulePiEquiv fun j ↦ linearMap (a j))

/-- Each fixed tuple records the corresponding coefficients in the original basis. -/
@[simp]
theorem fixedFamilyEquiv_apply [Finite J] (b : Module.Basis ι A V)
    (e : (Σ j, Fin (n j + 1)) ≃ ι) (a : ∀ j, Fin (n j + 1) → A) (f : V →ₗ[A] V)
    (h : ∀ j i, f (b (e ⟨j, i⟩)) = a j i • b (e ⟨j, finRotate (n j + 1) i⟩))
    (v : f.fixedSubmodule) (j : J) (i : Fin (n j + 1)) :
    (fixedFamilyEquiv b e a f h v j).val i = b.repr v.val (e ⟨j, i⟩) := by
  simp [fixedFamilyEquiv, Sigma.curry]

/-- The inverse family equivalence has the supplied tuple as its basis coefficients. -/
@[simp]
theorem fixedFamilyEquiv_symm_repr [Finite J] (b : Module.Basis ι A V)
    (e : (Σ j, Fin (n j + 1)) ≃ ι) (a : ∀ j, Fin (n j + 1) → A) (f : V →ₗ[A] V)
    (h : ∀ j i, f (b (e ⟨j, i⟩)) = a j i • b (e ⟨j, finRotate (n j + 1) i⟩))
    (w : ∀ j, (linearMap (a j) (M := A)).fixedSubmodule) (j : J) (i : Fin (n j + 1)) :
    b.repr ((fixedFamilyEquiv b e a f h).symm w).val (e ⟨j, i⟩) = (w j).val i := by
  simpa only [LinearEquiv.apply_symm_apply] using
    (fixedFamilyEquiv_apply b e a f h ((fixedFamilyEquiv b e a f h).symm w) j i).symm

/-- The inverse assembles the componentwise fixed tuples into the original basis. -/
theorem fixedFamilyEquiv_symm_apply [Fintype J] (b : Module.Basis ι A V)
    (e : (Σ j, Fin (n j + 1)) ≃ ι) (a : ∀ j, Fin (n j + 1) → A) (f : V →ₗ[A] V)
    (h : ∀ j i, f (b (e ⟨j, i⟩)) = a j i • b (e ⟨j, finRotate (n j + 1) i⟩))
    (w : ∀ j, (linearMap (a j) (M := A)).fixedSubmodule) :
    ((fixedFamilyEquiv b e a f h).symm w).val =
      ∑ j, ∑ i, (w j).val i • b (e ⟨j, i⟩) := by
  simp [fixedFamilyEquiv, Module.Basis.equivFun_symm_apply, Fintype.sum_sigma, Sigma.uncurry]

/-- All coefficients in a fixed vector are prefix products times their cycle's initial
coefficient. -/
theorem repr_eq_family_partialProd_mul [Finite J] (b : Module.Basis ι A V)
    (e : (Σ j, Fin (n j + 1)) ≃ ι) (a : ∀ j, Fin (n j + 1) → A) (f : V →ₗ[A] V)
    (h : ∀ j i, f (b (e ⟨j, i⟩)) = a j i • b (e ⟨j, finRotate (n j + 1) i⟩))
    (v : f.fixedSubmodule) (j : J) (i : Fin (n j + 1)) :
    b.repr v.val (e ⟨j, i⟩) =
      Fin.partialProd (Fin.init (a j)) i * b.repr v.val (e ⟨j, 0⟩) := by
  simpa only [fixedFamilyEquiv_apply, smul_eq_mul] using
    coeff_eq_partialProd_smul (a j) (fixedFamilyEquiv b e a f h v j) i

end CommSemiring

section CommRing

variable [CommRing A] [AddCommGroup V] [Module A V]

/-- The initial coefficient in each cycle classifies fixed vectors of the actual endomorphism
by torsion for that cycle's monodromy minus one. -/
noncomputable def fixedEquivPiTorsionOfBasis [Finite J] (b : Module.Basis ι A V)
    (e : (Σ j, Fin (n j + 1)) ≃ ι) (a : ∀ j, Fin (n j + 1) → A) (f : V →ₗ[A] V)
    (h : ∀ j i, f (b (e ⟨j, i⟩)) = a j i • b (e ⟨j, finRotate (n j + 1) i⟩)) :
    f.fixedSubmodule ≃ₗ[A] ∀ j, Submodule.torsionBy A A ((∏ i, a j i) - 1) :=
  (fixedFamilyEquiv b e a f h).trans
    (LinearEquiv.piCongrRight fun j ↦ fixedEquivTorsion (a j))

/-- The product equivalence reads the initial basis coefficient of each cycle. -/
@[simp]
theorem fixedEquivPiTorsionOfBasis_apply [Finite J] (b : Module.Basis ι A V)
    (e : (Σ j, Fin (n j + 1)) ≃ ι) (a : ∀ j, Fin (n j + 1) → A) (f : V →ₗ[A] V)
    (h : ∀ j i, f (b (e ⟨j, i⟩)) = a j i • b (e ⟨j, finRotate (n j + 1) i⟩))
    (v : f.fixedSubmodule) (j : J) :
    (fixedEquivPiTorsionOfBasis b e a f h v j : A) = b.repr v.val (e ⟨j, 0⟩) := by
  simp [fixedEquivPiTorsionOfBasis]

/-- The inverse torsion equivalence has prefix products times its parameters as coefficients. -/
@[simp]
theorem fixedEquivPiTorsionOfBasis_symm_repr [Finite J] (b : Module.Basis ι A V)
    (e : (Σ j, Fin (n j + 1)) ≃ ι) (a : ∀ j, Fin (n j + 1) → A) (f : V →ₗ[A] V)
    (h : ∀ j i, f (b (e ⟨j, i⟩)) = a j i • b (e ⟨j, finRotate (n j + 1) i⟩))
    (t : ∀ j, Submodule.torsionBy A A ((∏ i, a j i) - 1)) (j : J) (i : Fin (n j + 1)) :
    b.repr ((fixedEquivPiTorsionOfBasis b e a f h).symm t).val (e ⟨j, i⟩) =
      Fin.partialProd (Fin.init (a j)) i * (t j).val := by
  simp [fixedEquivPiTorsionOfBasis]

/-- The inverse is the double basis sum with the native prefix-product coefficients. -/
theorem fixedEquivPiTorsionOfBasis_symm_apply [Fintype J] (b : Module.Basis ι A V)
    (e : (Σ j, Fin (n j + 1)) ≃ ι) (a : ∀ j, Fin (n j + 1) → A) (f : V →ₗ[A] V)
    (h : ∀ j i, f (b (e ⟨j, i⟩)) = a j i • b (e ⟨j, finRotate (n j + 1) i⟩))
    (t : ∀ j, Submodule.torsionBy A A ((∏ i, a j i) - 1)) :
    ((fixedEquivPiTorsionOfBasis b e a f h).symm t).val =
      ∑ j, ∑ i, (Fin.partialProd (Fin.init (a j)) i * (t j).val) • b (e ⟨j, i⟩) := by
  simp [fixedEquivPiTorsionOfBasis, fixedFamilyEquiv_symm_apply]

end CommRing

end Module.Basis

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

/-- The coordinate of the image of a vector at a rotated index is the weight times the coordinate
of the vector at the original index. -/
theorem repr_apply_rotate (b : Module.Basis ι A V)
    (e : (Σ j, Fin (n j + 1)) ≃ ι) (a : ∀ j, Fin (n j + 1) → A) (f : V →ₗ[A] V)
    (h : ∀ j i, f (b (e ⟨j, i⟩)) = a j i • b (e ⟨j, finRotate (n j + 1) i⟩))
    (x : V) (j : J) (i : Fin (n j + 1)) :
    b.repr (f x) (e ⟨j, finRotate (n j + 1) i⟩) = a j i * b.repr x (e ⟨j, i⟩) := by
  classical
  have key : (b.coord (e ⟨j, finRotate (n j + 1) i⟩)) ∘ₗ f = a j i • b.coord (e ⟨j, i⟩) := by
    apply b.ext
    rintro k
    obtain ⟨⟨j', i'⟩, rfl⟩ := e.surjective k
    simp only [LinearMap.comp_apply, h, map_smul, Module.Basis.coord_apply,
      Module.Basis.repr_self, Finsupp.single_apply, e.injective.eq_iff, LinearMap.smul_apply,
      smul_eq_mul, Sigma.mk.injEq]
    by_cases hj : j = j'
    · subst hj
      by_cases hi : i = i'
      · simp [hi]
      · simp [Ne.symm hi]
    · simp [Ne.symm hj]
  simpa using LinearMap.congr_fun key x

/-- Curried basis coordinates intertwine the given family action with its componentwise
weighted shifts. The enumeration exhausts the whole basis. -/
theorem equivFun_comp_eq_piMap_comp [Finite J] (b : Module.Basis ι A V)
    (e : (Σ j, Fin (n j + 1)) ≃ ι) (a : ∀ j, Fin (n j + 1) → A) (f : V →ₗ[A] V)
    (h : ∀ j i, f (b (e ⟨j, i⟩)) = a j i • b (e ⟨j, finRotate (n j + 1) i⟩)) :
    ((b.reindex e.symm).equivFun.trans
      (LinearEquiv.piCurry A fun j (_ : Fin (n j + 1)) ↦ A)).toLinearMap ∘ₗ f =
      (LinearMap.piMap fun j ↦ TauCeti.WeightedCycle.linearMap (a j)) ∘ₗ
        ((b.reindex e.symm).equivFun.trans
          (LinearEquiv.piCurry A fun j (_ : Fin (n j + 1)) ↦ A)).toLinearMap := by
  ext x k l
  obtain ⟨r, rfl⟩ := (finRotate (n k + 1)).surjective l
  simpa [Sigma.curry, linearMap_apply_rotate] using repr_apply_rotate b e a f h x k r

/-- Fixed vectors in the original module give one native fixed tuple per cycle. -/
noncomputable def fixedFamilyEquiv [Finite J] (b : Module.Basis ι A V)
    (e : (Σ j, Fin (n j + 1)) ≃ ι) (a : ∀ j, Fin (n j + 1) → A) (f : V →ₗ[A] V)
    (h : ∀ j i, f (b (e ⟨j, i⟩)) = a j i • b (e ⟨j, finRotate (n j + 1) i⟩)) :
    f.fixedSubmodule ≃ₗ[A] ∀ j, (TauCeti.WeightedCycle.linearMap (a j) (M := A)).fixedSubmodule :=
  (((b.reindex e.symm).equivFun.trans
    (LinearEquiv.piCurry A fun j (_ : Fin (n j + 1)) ↦ A)).fixedSubmoduleCongr
      (equivFun_comp_eq_piMap_comp b e a f h)).trans
    (LinearMap.fixedSubmodulePiEquiv fun j ↦ TauCeti.WeightedCycle.linearMap (a j))

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
    (w : ∀ j, (TauCeti.WeightedCycle.linearMap (a j) (M := A)).fixedSubmodule)
    (j : J) (i : Fin (n j + 1)) :
    b.repr ((fixedFamilyEquiv b e a f h).symm w).val (e ⟨j, i⟩) = (w j).val i := by
  simpa only [LinearEquiv.apply_symm_apply] using
    (fixedFamilyEquiv_apply b e a f h ((fixedFamilyEquiv b e a f h).symm w) j i).symm

/-- The inverse assembles the componentwise fixed tuples into the original basis. -/
theorem fixedFamilyEquiv_symm_apply [Fintype J] (b : Module.Basis ι A V)
    (e : (Σ j, Fin (n j + 1)) ≃ ι) (a : ∀ j, Fin (n j + 1) → A) (f : V →ₗ[A] V)
    (h : ∀ j i, f (b (e ⟨j, i⟩)) = a j i • b (e ⟨j, finRotate (n j + 1) i⟩))
    (w : ∀ j, (TauCeti.WeightedCycle.linearMap (a j) (M := A)).fixedSubmodule) :
    ((fixedFamilyEquiv b e a f h).symm w).val =
      ∑ j, ∑ i, (w j).val i • b (e ⟨j, i⟩) := by
  simp [fixedFamilyEquiv, Module.Basis.equivFun_symm_apply, Fintype.sum_sigma, Sigma.uncurry]

/-- The coefficients of a fixed vector along one cycle form a fixed tuple of that cycle's
weighted shift. -/
theorem repr_mem_fixedSubmodule (b : Module.Basis ι A V)
    (e : (Σ j, Fin (n j + 1)) ≃ ι) (a : ∀ j, Fin (n j + 1) → A) (f : V →ₗ[A] V)
    (h : ∀ j i, f (b (e ⟨j, i⟩)) = a j i • b (e ⟨j, finRotate (n j + 1) i⟩))
    (v : f.fixedSubmodule) (j : J) :
    (fun i ↦ b.repr v.val (e ⟨j, i⟩)) ∈
      (TauCeti.WeightedCycle.linearMap (a j) (M := A)).fixedSubmodule := by
  rw [mem_fixedSubmodule_iff]
  intro i
  have hv : f v.val = v.val := (LinearMap.mem_fixedSubmodule_iff).mp v.property
  simpa [hv] using repr_apply_rotate b e a f h v.val j i

/-- All coefficients in a fixed vector are prefix products times their cycle's initial
coefficient. -/
theorem repr_eq_family_partialProd_mul (b : Module.Basis ι A V)
    (e : (Σ j, Fin (n j + 1)) ≃ ι) (a : ∀ j, Fin (n j + 1) → A) (f : V →ₗ[A] V)
    (h : ∀ j i, f (b (e ⟨j, i⟩)) = a j i • b (e ⟨j, finRotate (n j + 1) i⟩))
    (v : f.fixedSubmodule) (j : J) (i : Fin (n j + 1)) :
    b.repr v.val (e ⟨j, i⟩) =
      Fin.partialProd (Fin.init (a j)) i * b.repr v.val (e ⟨j, 0⟩) :=
  coeff_eq_partialProd_smul (a j) ⟨_, repr_mem_fixedSubmodule b e a f h v j⟩ i

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

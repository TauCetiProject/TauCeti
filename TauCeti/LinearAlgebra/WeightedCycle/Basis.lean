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
# Fixed vectors of a weighted cycle on a basis

An enumeration of a basis and the actual weighted-cycle action equations for a
linear endomorphism identify its fixed submodule with the fixed coefficient tuples
over a commutative semiring. Over a commutative ring these are the annihilator of
monodromy minus one. The inverse is the basis expansion with prefix-product coefficients.
This consumes a supplied basis and action; it does not construct a root-orbit basis.
The enumeration exhausts the basis, so the module consists of one cycle.

-/

public section

open TauCeti.WeightedCycle

namespace Module.Basis

variable {A V ι : Type*} {n : ℕ}

section CommSemiring

variable [CommSemiring A] [AddCommMonoid V] [Module A V]

/-- Basis coordinates intertwine the given weighted-cycle action with `linearMap`. -/
theorem equivFun_comp_eq_linearMap_comp (b : Module.Basis ι A V) (e : Fin (n + 1) ≃ ι)
    (a : Fin (n + 1) → A) (f : V →ₗ[A] V)
    (h : ∀ i, f (b (e i)) = a i • b (e (finRotate (n + 1) i))) :
    (b.reindex e.symm).equivFun.toLinearMap ∘ₗ f =
      linearMap a ∘ₗ (b.reindex e.symm).equivFun.toLinearMap := by
  apply (b.reindex e.symm).ext
  intro i
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  have hi : f ((b.reindex e.symm) i) = a i •
      (b.reindex e.symm) (finRotate (n + 1) i) := by
    simpa using h i
  rw [hi, map_smul]
  funext j
  obtain ⟨k, rfl⟩ := (finRotate (n + 1)).surjective j
  rw [linearMap_apply_rotate]
  simp only [Pi.smul_apply, Module.Basis.equivFun_self, Equiv.apply_eq_iff_eq]
  by_cases hik : i = k <;> simp [hik]

/-- Basis coordinates restrict to an equivalence of the actual fixed submodules. -/
noncomputable def fixedBasisEquiv (b : Module.Basis ι A V)
    (e : Fin (n + 1) ≃ ι) (a : Fin (n + 1) → A) (f : V →ₗ[A] V)
    (h : ∀ i, f (b (e i)) = a i • b (e (finRotate (n + 1) i))) :
    f.fixedSubmodule ≃ₗ[A] (linearMap a (M := A)).fixedSubmodule :=
  (b.reindex e.symm).equivFun.fixedSubmoduleCongr
    (equivFun_comp_eq_linearMap_comp b e a f h)

/-- The fixed-submodule equivalence reads coordinates in the original basis. -/
@[simp]
theorem fixedBasisEquiv_apply (b : Module.Basis ι A V)
    (e : Fin (n + 1) ≃ ι) (a : Fin (n + 1) → A) (f : V →ₗ[A] V)
    (h : ∀ i, f (b (e i)) = a i • b (e (finRotate (n + 1) i)))
    (v : f.fixedSubmodule) :
    (fixedBasisEquiv b e a f h v : Fin (n + 1) → A) =
      fun i ↦ b.repr v.val (e i) := by
  ext i
  simp [fixedBasisEquiv]

/-- The inverse fixed-submodule equivalence is the original basis expansion. -/
@[simp]
theorem fixedBasisEquiv_symm_apply (b : Module.Basis ι A V)
    (e : Fin (n + 1) ≃ ι) (a : Fin (n + 1) → A) (f : V →ₗ[A] V)
    (h : ∀ i, f (b (e i)) = a i • b (e (finRotate (n + 1) i)))
    (w : (linearMap a (M := A)).fixedSubmodule) :
    ((fixedBasisEquiv b e a f h).symm w : V) = ∑ i, w.val i • b (e i) := by
  simp [fixedBasisEquiv, Module.Basis.equivFun_symm_apply]

/-- Every coefficient of a fixed vector is the corresponding prefix product times
its initial coefficient, in the original basis indexing. -/
theorem repr_eq_partialProd_mul (b : Module.Basis ι A V)
    (e : Fin (n + 1) ≃ ι) (a : Fin (n + 1) → A) (f : V →ₗ[A] V)
    (h : ∀ i, f (b (e i)) = a i • b (e (finRotate (n + 1) i)))
    (v : f.fixedSubmodule) (i : Fin (n + 1)) :
    b.repr v.val (e i) = Fin.partialProd (Fin.init a) i * b.repr v.val (e 0) := by
  have hc := coeff_eq_partialProd_smul a (fixedBasisEquiv b e a f h v) i
  simpa only [fixedBasisEquiv_apply, smul_eq_mul] using hc

end CommSemiring

section CommRing

variable [CommRing A] [AddCommGroup V] [Module A V]

/-- The initial basis coefficient classifies fixed vectors of the given endomorphism.
For a negative signed cycle the codomain retains every coefficient killed by two. -/
noncomputable def fixedEquivTorsionOfBasis (b : Module.Basis ι A V)
    (e : Fin (n + 1) ≃ ι) (a : Fin (n + 1) → A) (f : V →ₗ[A] V)
    (h : ∀ i, f (b (e i)) = a i • b (e (finRotate (n + 1) i))) :
    f.fixedSubmodule ≃ₗ[A] Submodule.torsionBy A A ((∏ i, a i) - 1) :=
  (fixedBasisEquiv b e a f h).trans (fixedEquivTorsion a)

/-- The equivalence reads the coefficient of the enumerated initial basis vector. -/
@[simp]
theorem fixedEquivTorsionOfBasis_apply (b : Module.Basis ι A V)
    (e : Fin (n + 1) ≃ ι) (a : Fin (n + 1) → A) (f : V →ₗ[A] V)
    (h : ∀ i, f (b (e i)) = a i • b (e (finRotate (n + 1) i)))
    (v : f.fixedSubmodule) :
    (fixedEquivTorsionOfBasis b e a f h v : A) = b.repr v.val (e 0) := by
  simp [fixedEquivTorsionOfBasis]

/-- The inverse is the literal basis expansion with prefix-product coefficients. -/
@[simp]
theorem fixedEquivTorsionOfBasis_symm_apply (b : Module.Basis ι A V)
    (e : Fin (n + 1) ≃ ι) (a : Fin (n + 1) → A) (f : V →ₗ[A] V)
    (h : ∀ i, f (b (e i)) = a i • b (e (finRotate (n + 1) i)))
    (t : Submodule.torsionBy A A ((∏ i, a i) - 1)) :
    ((fixedEquivTorsionOfBasis b e a f h).symm t).val =
      ∑ i, (Fin.partialProd (Fin.init a) i * t.val) • b (e i) := by
  simp [fixedEquivTorsionOfBasis]

end CommRing

end Module.Basis

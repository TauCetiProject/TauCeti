/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.Topology.Algebra.OpenSubgroup
public import TauCeti.RepresentationTheory.GaloisLattice.Basic
public import TauCeti.RepresentationTheory.GaloisLattice.FiniteQuotient

/-!
# Duals of integral Galois lattices

The contragredient representation on the integral dual of a Galois lattice is again a Galois
lattice. Continuity is proved using the open kernel of the representation on a finitely generated
module: it is an open subgroup, and it fixes every linear functional under the contragredient
action. The integral dual of a finitely generated module is finite free, so no freeness of `V` is
assumed.

## Main declaration

* `TauCeti.galoisLatticeProperty_dual`: the integral dual of a Galois lattice,
  with its contragredient action, is a Galois lattice.
* `TauCeti.galoisLatticeProperty_contragredient`: transport the contragredient action across a
  linear equivalence with an integral dual.

## References

See J. S. Milne, *Algebraic Groups* (2017), Definitions 12.14 and 12.17.
-/

public section

open CategoryTheory

namespace TauCeti

universe u

variable {k V : Type u} [Field k] [AddCommGroup V]
variable [Module.Finite ℤ V]

/-- A representation identified equivariantly with the contragredient of a Galois lattice is
itself a Galois lattice. This form lets a construction retain its intrinsic carrier rather than
replacing it by an integral dual. -/
theorem galoisLatticeProperty_contragredient
    {W : Type u} [AddCommGroup W] [Module ℤ W]
    (ρ : Representation ℤ (Field.absoluteGaloisGroup k) V)
    (τ : Representation ℤ (Field.absoluteGaloisGroup k) W)
    (e : W ≃ₗ[ℤ] Module.Dual ℤ V)
    (he : ∀ (σ : Field.absoluteGaloisGroup k) (w : W) (x : V),
      e (τ σ w) x = e w (ρ σ⁻¹ x))
    (hopen : ∀ x : V, IsOpen {σ | ρ σ x = x}) :
    galoisLatticeProperty k (Rep.of τ) := by
  have : Module.Free ℤ (Module.Dual ℤ V) := inferInstance
  let _ : Module.Free ℤ W := Module.Free.of_equiv e.symm
  let _ : Module.Finite ℤ W := Module.Finite.equiv e.symm
  -- `MulAction.stabilizer` needs an action on the carrier, while the hypotheses deliberately
  -- retain the bundled representation form. This local action exposes exactly that map.
  let _ : MulAction (Field.absoluteGaloisGroup k) W := {
    smul σ w := τ σ w
    one_smul w := by
      change τ 1 w = w
      rw [map_one, one_apply_eq_self]
    mul_smul σ τ' w := by
      change τ (σ * τ') w = τ σ (τ τ' w)
      rw [map_mul, mul_apply_eq_comp]
  }
  rw [galoisLatticeProperty_iff]
  refine ⟨⟨inferInstance, inferInstance⟩, ?_⟩
  intro w
  -- Rewrite the continuity goal as openness of a subgroup so the open kernel of `ρ` can be
  -- enlarged with `Subgroup.isOpen_mono`.
  change IsOpen (↑(MulAction.stabilizer (Field.absoluteGaloisGroup k) w) :
    Set (Field.absoluteGaloisGroup k))
  apply Subgroup.isOpen_mono (H₁ := ρ.ker)
  · intro σ hσ
    rw [MulAction.mem_stabilizer_iff]
    apply e.injective
    apply LinearMap.ext
    intro x
    -- Expose the local action above before applying the stated equivariance formula for `e`.
    change e (τ σ w) x = e w x
    rw [he, (MonoidHom.mem_ker.mp (ρ.ker.inv_mem hσ) : ρ σ⁻¹ = 1)]
    rfl
  · exact Representation.isOpen_ker_of_finite ρ hopen

/-- The contragredient representation on the integral dual of a Galois lattice is again a
Galois lattice. -/
theorem galoisLatticeProperty_dual
    (ρ : Representation ℤ (Field.absoluteGaloisGroup k) V)
    (hopen : ∀ x : V, IsOpen {σ | ρ σ x = x}) :
    galoisLatticeProperty k (Rep.of ρ.dual) := by
  apply galoisLatticeProperty_contragredient ρ ρ.dual (LinearEquiv.refl ℤ _)
  · intro σ f x
    rfl
  · exact hopen

end TauCeti

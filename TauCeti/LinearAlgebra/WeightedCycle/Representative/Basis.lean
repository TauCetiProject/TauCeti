/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.WeightedCycle.Basis
public import TauCeti.LinearAlgebra.WeightedCycle.Representative.Basic

/-!
# Changing the representative in a basis cycle

Changing the first vertex in the enumeration of a basis gives the rotated
weighted-cycle equations for the same endomorphism. The actual fixed-vector
coordinate maps commute with this rotation, in both directions, and their
monodromy parameters change by the prefix product.
-/

public section

open TauCeti.WeightedCycle

namespace Module.Basis

variable {A V ι : Type*} {n : ℕ}

section CommSemiring

variable [CommSemiring A] [AddCommMonoid V] [Module A V]

/-- The fixed-coordinate equivalence commutes with changing the initial basis vertex. -/
theorem fixedBasisEquiv_addRight_trans (b : Module.Basis ι A V)
    (e : Fin (n + 1) ≃ ι) (a : Fin (n + 1) → A) (f : V →ₗ[A] V)
    (h : ∀ i, f (b (e i)) = a i • b (e (finRotate (n + 1) i))) (k : Fin (n + 1))
    (v : f.fixedSubmodule) :
    fixedBasisEquiv b ((Equiv.addRight k).trans e) (fun i ↦ a (i + k)) f
        (apply_eq_smul_addRight_trans b e a f h k) v =
      fixedRotateEquiv a k (fixedBasisEquiv b e a f h v) := by
  apply Subtype.ext
  funext i
  simp only [fixedBasisEquiv_apply, fixedRotateEquiv_apply,
    Equiv.trans_apply, Equiv.coe_addRight]

/-- Both enumerations reconstruct the same fixed vector from rotated coordinates. -/
theorem fixedBasisEquiv_symm_addRight_trans (b : Module.Basis ι A V)
    (e : Fin (n + 1) ≃ ι) (a : Fin (n + 1) → A) (f : V →ₗ[A] V)
    (h : ∀ i, f (b (e i)) = a i • b (e (finRotate (n + 1) i))) (k : Fin (n + 1))
    (w : (TauCeti.WeightedCycle.linearMap a (M := A)).fixedSubmodule) :
    (fixedBasisEquiv b ((Equiv.addRight k).trans e) (fun i ↦ a (i + k)) f
        (apply_eq_smul_addRight_trans b e a f h k)).symm (fixedRotateEquiv a k w) =
      (fixedBasisEquiv b e a f h).symm w := by
  apply (fixedBasisEquiv b ((Equiv.addRight k).trans e) (fun i ↦ a (i + k)) f
    (apply_eq_smul_addRight_trans b e a f h k)).injective
  rw [LinearEquiv.apply_symm_apply, fixedBasisEquiv_addRight_trans b e a f h k,
    LinearEquiv.apply_symm_apply]

end CommSemiring

section CommRing

variable [CommRing A] [AddCommGroup V] [Module A V]

/-- The torsion-coordinate equivalence of the rotated enumeration is the original one
followed by the change of torsion parameter. -/
theorem fixedEquivTorsionOfBasis_addRight_trans (b : Module.Basis ι A V)
    (e : Fin (n + 1) ≃ ι) (a : Fin (n + 1) → A) (f : V →ₗ[A] V)
    (h : ∀ i, f (b (e i)) = a i • b (e (finRotate (n + 1) i))) (k : Fin (n + 1)) :
    fixedEquivTorsionOfBasis b ((Equiv.addRight k).trans e) (fun i ↦ a (i + k)) f
        (apply_eq_smul_addRight_trans b e a f h k) =
      (fixedEquivTorsionOfBasis b e a f h).trans (torsionRotateEquiv a k) := by
  refine LinearEquiv.ext fun v ↦ Subtype.ext ?_
  rw [LinearEquiv.trans_apply, fixedEquivTorsionOfBasis_apply, torsionRotateEquiv_apply,
    fixedEquivTorsionOfBasis_apply]
  simpa only [Equiv.trans_apply, Equiv.coe_addRight, zero_add, smul_eq_mul] using
    repr_eq_partialProd_mul b e a f h v k

/-- Both enumerations reconstruct the same fixed vector from the rotated torsion parameter. -/
theorem fixedEquivTorsionOfBasis_symm_addRight_trans (b : Module.Basis ι A V)
    (e : Fin (n + 1) ≃ ι) (a : Fin (n + 1) → A) (f : V →ₗ[A] V)
    (h : ∀ i, f (b (e i)) = a i • b (e (finRotate (n + 1) i))) (k : Fin (n + 1))
    (t : Submodule.torsionBy A A ((∏ i, a i) - 1)) :
    (fixedEquivTorsionOfBasis b ((Equiv.addRight k).trans e) (fun i ↦ a (i + k)) f
        (apply_eq_smul_addRight_trans b e a f h k)).symm (torsionRotateEquiv a k t) =
      (fixedEquivTorsionOfBasis b e a f h).symm t := by
  rw [fixedEquivTorsionOfBasis_addRight_trans, LinearEquiv.trans_symm,
    LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]

end CommRing

end Module.Basis

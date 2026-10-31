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
weighted-cycle action for the same endomorphism. The actual fixed-vector
coordinate maps commute with this rotation. Their monodromy parameters and
inverse basis expansions change by the prefix product.
-/

public section

open TauCeti.WeightedCycle

namespace Module.Basis

variable {A V ι : Type*} {n : ℕ}

section CommSemiring

variable [CommSemiring A] [AddCommMonoid V] [Module A V]

/-- A cyclic change of enumeration gives the rotated weights for the same endomorphism. -/
theorem weightedCycle_reindex_addRight (b : Module.Basis ι A V)
    (e : Fin (n + 1) ≃ ι) (a : Fin (n + 1) → A) (f : V →ₗ[A] V)
    (h : ∀ i, f (b (e i)) = a i • b (e (finRotate (n + 1) i))) (k : Fin (n + 1)) :
    ∀ i, f (b (((Equiv.addRight k).trans e) i)) =
      a (i + k) • b (((Equiv.addRight k).trans e) (finRotate (n + 1) i)) := by
  intro i
  simpa only [Equiv.trans_apply, Equiv.coe_addRight, finRotate_apply,
    add_right_comm i k 1] using h (i + k)

/-- The fixed-coordinate equivalence commutes with changing the initial basis vertex. -/
theorem fixedBasisEquiv_reindex_addRight (b : Module.Basis ι A V)
    (e : Fin (n + 1) ≃ ι) (a : Fin (n + 1) → A) (f : V →ₗ[A] V)
    (h : ∀ i, f (b (e i)) = a i • b (e (finRotate (n + 1) i))) (k : Fin (n + 1))
    (v : f.fixedSubmodule) :
    fixedBasisEquiv b ((Equiv.addRight k).trans e) (fun i ↦ a (i + k)) f
        (weightedCycle_reindex_addRight b e a f h k) v =
      fixedRotateEquiv a k (fixedBasisEquiv b e a f h v) := by
  apply Subtype.ext
  funext i
  simp only [fixedBasisEquiv_apply, fixedRotateEquiv_apply,
    Equiv.trans_apply, Equiv.coe_addRight]

/-- Both enumerations reconstruct the same fixed vector from rotated coordinates. -/
theorem fixedBasisEquiv_symm_reindex_addRight (b : Module.Basis ι A V)
    (e : Fin (n + 1) ≃ ι) (a : Fin (n + 1) → A) (f : V →ₗ[A] V)
    (h : ∀ i, f (b (e i)) = a i • b (e (finRotate (n + 1) i))) (k : Fin (n + 1))
    (w : (linearMap a (M := A)).fixedSubmodule) :
    (fixedBasisEquiv b ((Equiv.addRight k).trans e) (fun i ↦ a (i + k)) f
        (weightedCycle_reindex_addRight b e a f h k)).symm (fixedRotateEquiv a k w) =
      (fixedBasisEquiv b e a f h).symm w := by
  apply (fixedBasisEquiv b ((Equiv.addRight k).trans e) (fun i ↦ a (i + k)) f
    (weightedCycle_reindex_addRight b e a f h k)).injective
  rw [LinearEquiv.apply_symm_apply, fixedBasisEquiv_reindex_addRight b e a f h k,
    LinearEquiv.apply_symm_apply]

end CommSemiring

section CommRing

variable [CommRing A] [AddCommGroup V] [Module A V]

/-- The scalar torsion coordinate changes by the induced torsion automorphism. -/
theorem fixedEquivTorsionOfBasis_reindex_addRight (b : Module.Basis ι A V)
    (e : Fin (n + 1) ≃ ι) (a : Fin (n + 1) → A) (f : V →ₗ[A] V)
    (h : ∀ i, f (b (e i)) = a i • b (e (finRotate (n + 1) i))) (k : Fin (n + 1))
    (v : f.fixedSubmodule) :
    (fixedEquivTorsionOfBasis b ((Equiv.addRight k).trans e) (fun i ↦ a (i + k)) f
        (weightedCycle_reindex_addRight b e a f h k) v : A) =
      (torsionRotateEquiv a k (fixedEquivTorsionOfBasis b e a f h v) : A) := by
  rw [fixedEquivTorsionOfBasis_apply, torsionRotateEquiv_apply,
    fixedEquivTorsionOfBasis_apply]
  simpa only [Equiv.trans_apply, Equiv.coe_addRight, zero_add, smul_eq_mul] using
    repr_eq_partialProd_mul b e a f h v k

/-- The two prefix-product basis expansions agree after changing the initial parameter. -/
theorem sum_partialProd_reindex_addRight (b : Module.Basis ι A V)
    (e : Fin (n + 1) ≃ ι) (a : Fin (n + 1) → A) (k : Fin (n + 1))
    (t : Submodule.torsionBy A A ((∏ i, a i) - 1)) :
    (∑ i, (Fin.partialProd (Fin.init (fun j ↦ a (j + k))) i *
        (Fin.partialProd (Fin.init a) k * t.val)) • b (e (i + k))) =
      ∑ i, (Fin.partialProd (Fin.init a) i * t.val) • b (e i) := by
  calc
    _ = ∑ i, (Fin.partialProd (Fin.init a) (i + k) * t.val) • b (e (i + k)) := by
      apply Finset.sum_congr rfl
      intro i _
      have h := partialProd_rotate_smul a k i t
      simp only [smul_eq_mul, add_comm k i] at h
      rw [h]
    _ = _ := Equiv.sum_comp (Equiv.addRight k)
      (fun i ↦ (Fin.partialProd (Fin.init a) i * t.val) • b (e i))

end CommRing

end Module.Basis

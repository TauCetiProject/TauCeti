/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.RepresentationTheory.Homological.TateCohomology.Cup.Product

/-!
# Associativity edges of the Tate cup product

The tensor associator identifies the two ways to cup three Tate classes when either the middle
or the last class has degree zero. These identities hold in every integer degree for the other
two classes. They are the two base edges from which associativity in all tridegrees is obtained by
dimension shifting.

See Artin and Tate, *Class Field Theory*, Preliminaries §2, and Brown,
*Cohomology of Groups*, Chapter VI, §5.
-/

public noncomputable section

universe u

open CategoryTheory MonoidalCategory Rep
open scoped TensorProduct

namespace TauCeti.TateCohomology

variable {k G : Type u} [CommRing k] [Group G] [Fintype G]

/-- Associativity of the Tate cup product when the last class has degree zero. -/
theorem cup_assoc_zero_right (M N P : Rep k G) {p q r : ℤ} (h : p + q = r)
    (x : tateCohomology M p) (y : tateCohomology N q)
    (z : tateCohomology P 0) :
    (tateCohomologyFunctor r).map (α_ M N P).hom
      (cup (M ⊗ N) P r 0 r (by omega)
        (cup M N p q r h x y) z) =
      cup M (N ⊗ P) p q r h x
        (cup N P q 0 q (by omega) y z) := by
  induction z using H0_induction_on with
  | h z =>
    rw [cup_zero_right, cup_zero_right, cupH0_H0π, cupH0_H0π, cup_map_right,
      ← ModuleCat.comp_apply, ← Functor.map_comp,
      Rep.tensorInvariant_comp_associator]

/-- Associativity of the Tate cup product when the middle class has degree zero. -/
theorem cup_assoc_zero_middle (M N P : Rep k G) {p q r : ℤ} (h : p + q = r)
    (x : tateCohomology M p) (y : tateCohomology N 0)
    (z : tateCohomology P q) :
    (tateCohomologyFunctor r).map (α_ M N P).hom
      (cup (M ⊗ N) P p q r h
        (cup M N p 0 p (by omega) x y) z) =
      cup M (N ⊗ P) p q r h x
        (cup N P 0 q q (by omega) y z) := by
  induction y using H0_induction_on with
  | h y =>
    rw [cup_zero_right, cup_zero_left, cupH0_H0π, cup0H_H0π,
      cup_map_left, cup_map_right, ← ModuleCat.comp_apply, ← Functor.map_comp,
      Rep.whiskerRight_tensorInvariant_comp_associator]

/-- Cup product with two degree-zero Tate classes is associative, after applying the tensor
associator to the coefficient representation. -/
@[simp]
theorem cupH0_assoc_zero (M N P : Rep k G) (p : ℤ)
    (x : tateCohomology M p) (y : tateCohomology N 0)
    (z : tateCohomology P 0) :
    (tateCohomologyFunctor p).map (α_ M N P).hom
      (cupH0 (M ⊗ N) P p (cupH0 M N p x y) z) =
      cupH0 M (N ⊗ P) p x (cupH0 N P 0 y z) := by
  have h := cup_assoc_zero_right M N P (p := p) (q := 0) (r := p) (by omega) x y z
  rw [LinearMap.congr_fun₂ (cup_zero_right M N p (by omega)) x y] at h
  rw [LinearMap.congr_fun₂ (cup_zero_right (M ⊗ N) P p (by omega))
    (cupH0 M N p x y) z] at h
  rw [LinearMap.congr_fun₂ (cup_zero_right N P 0 (by omega)) y z] at h
  rw [LinearMap.congr_fun₂ (cup_zero_right M (N ⊗ P) p (by omega)) x
    (cupH0 N P 0 y z)] at h
  exact h

/-- Associativity of the Tate cup product in tridegrees `(p, 0, 0)`. -/
theorem cup_assoc_zero_zero (M N P : Rep k G) (p : ℤ)
    (x : tateCohomology M p) (y : tateCohomology N 0)
    (z : tateCohomology P 0) :
    (tateCohomologyFunctor p).map (α_ M N P).hom
      (cup (M ⊗ N) P p 0 p (by omega)
        (cup M N p 0 p (by omega) x y) z) =
      cup M (N ⊗ P) p 0 p (by omega) x
        (cup N P 0 0 0 (by omega) y z) := by
  simpa only [cup_zero_right] using cupH0_assoc_zero M N P p x y z

end TauCeti.TateCohomology

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.KZero.Defs
public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.KZero.Map
public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.SplitK0.Basic

import TauCeti.Algebra.Ring.Opposite

/-!
# Algebraic `K₀` of a ring and ring isomorphisms

Built on `TauCeti.KZero R`, `TauCeti.KZero.regular` (from
`TauCeti.Algebra.Category.ModuleCat.FiniteProjective.KZero.Defs`), and `TauCeti.KZero.map` (from
`TauCeti.Algebra.Category.ModuleCat.FiniteProjective.KZero.Map`), this file provides:

* the standard normal form `[P] - n • [R]` (`TauCeti.KZero.exists_eq_of_sub_nsmul_regular`),
* `[R] ↦ [S]` (`TauCeti.KZero.map_regular`),
* ring-equivalence functoriality (`RingEquiv.kZeroEquiv`).

## References

* C. A. Weibel, *The K-book*, Chapter II, §2, Lemma 2.1, Examples 2.1.1–2.1.2, §2.8.
-/

public section

open CategoryTheory MulOpposite

universe u

namespace TauCeti.KZero

variable {R S T : Type u} [Ring R] [Ring S] [Ring T]

/-- Every class in `KZero R` has the form `[P] - n • [R]`. -/
theorem exists_eq_of_sub_nsmul_regular (x : KZero R) :
    ∃ (P : FiniteProjectiveRight R) (n : ℕ),
      x = SplitK0.of.{u} P - n • regular R :=
  regular_def R ▸ SplitK0.exists_eq_of_sub_nsmul_finiteProjectiveModulesRegular x

@[simp] theorem map_regular (f : R →+* S) : map f (regular R) = regular S := by
  simp [regular_def]

end TauCeti.KZero

namespace RingEquiv

open TauCeti

variable {R S T : Type u} [Ring R] [Ring S] [Ring T]

/-- A ring isomorphism `e : R ≃+* S` induces an isomorphism `KZero R ≃+ KZero S`. -/
noncomputable def kZeroEquiv (e : R ≃+* S) : KZero R ≃+ KZero S :=
  (ModuleCat.restrictScalarsEquivalenceOfRingEquiv
    (RingEquiv.op e)).symm.finiteProjectiveModulesSplitK0Equiv

@[simp] theorem kZeroEquiv_apply (e : R ≃+* S) (x : KZero R) :
    e.kZeroEquiv x = KZero.map e.toRingHom x := by
  induction x using SplitK0.induction_on with
  | zero => simp
  | of P =>
    have heq : (RingEquiv.op e).toRingHom = RingHom.op e.toRingHom := RingHom.ext fun _ ↦ rfl
    have h := DFunLike.congr_fun
      (RingEquiv.splitK0Map_finiteProjectiveModulesExtendScalars_eq_restrictScalars
        (RingEquiv.op e)) (SplitK0.of.{u} P)
    rw [heq] at h
    simp only [Equivalence.finiteProjectiveModulesSplitK0Equiv_toAddMonoidHom,
      SplitK0.map_of] at h
    simpa only [kZeroEquiv, Equivalence.finiteProjectiveModulesSplitK0Equiv_of,
      KZero.map_of] using h.symm
  | neg _ hx => simp [hx]
  | add _ _ hx hy => simp [hx, hy]

@[simp] theorem kZeroEquiv_symm (e : R ≃+* S) :
    e.kZeroEquiv.symm = e.symm.kZeroEquiv := by
  ext x
  apply e.kZeroEquiv.injective
  simp [kZeroEquiv_apply, KZero.map_map]

theorem kZeroEquiv_trans (e : R ≃+* S) (e' : S ≃+* T) :
    (e.trans e').kZeroEquiv = e.kZeroEquiv.trans e'.kZeroEquiv := by
  ext; simp [RingEquiv.toRingHom_trans]

@[simp] theorem kZeroEquiv_refl (R : Type u) [Ring R] :
    (RingEquiv.refl R).kZeroEquiv = AddEquiv.refl (KZero R) := by ext; simp

end RingEquiv

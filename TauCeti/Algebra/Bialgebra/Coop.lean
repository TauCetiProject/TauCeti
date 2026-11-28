/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Bialgebra.Basic
public import TauCeti.Algebra.Coalgebra.Coop

/-!
# Co-opposite bialgebras

For an `R`-bialgebra `A`, the co-opposite `TauCeti.Coop A` (equipped with the coalgebra
structure from `TauCeti.Algebra.Coalgebra.Coop`) is again an `R`-bialgebra
(`TauCeti.Coop.instBialgebra`).
-/

@[expose] public section

open scoped TensorProduct

namespace TauCeti.Coop

universe u v

variable {R : Type u} {A : Type v} [CommSemiring R] [Semiring A] [Bialgebra R A]

noncomputable instance instBialgebra : Bialgebra R (Coop A) :=
  Bialgebra.mk' R (Coop A)
    (by rw [counit_apply, val_one, Bialgebra.counit_one])
    (fun {a b} ↦ by rw [counit_apply, val_mul, counit_apply, counit_apply, Bialgebra.counit_mul])
    (by
      rw [← mk_one, comul_mk, Bialgebra.comul_one, Algebra.TensorProduct.one_def]
      simp [Algebra.TensorProduct.one_def])
    (fun {a b} ↦ by
      induction a with | mk a =>
      induction b with | mk b =>
      let f : A ⊗[R] A →ₐ[R] Coop A ⊗[R] Coop A :=
        (Algebra.TensorProduct.map (algEquiv R A).symm.toAlgHom
          (algEquiv R A).symm.toAlgHom).comp (Algebra.TensorProduct.comm R A A).toAlgHom
      have hf (z : A ⊗[R] A) :
          TensorProduct.map (linearEquiv R A).symm.toLinearMap
              (linearEquiv R A).symm.toLinearMap (TensorProduct.comm R A A z) = f z := by
        induction z using TensorProduct.inductionOn with
        | add u v hu hv => simp only [map_add, hu, hv]
        | tmul x y => simp [f]
      simp only [← mk_mul, comul_mk, Bialgebra.comul_mul, hf]
      exact map_mul f (Coalgebra.comul (R := R) a) (Coalgebra.comul (R := R) b))

end TauCeti.Coop

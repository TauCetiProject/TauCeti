/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.WeilRestriction.Basic
public import Mathlib.RingTheory.Smooth.Basic

import TauCeti.Algebra.TensorProduct.Ideal

/-!
# Smoothness of Weil restrictions

Weil restriction along a finite projective algebra sends a finitely presented, formally smooth
algebra to a formally smooth algebra. Since the Weil restriction is finitely presented, it
also preserves smoothness. These instances allow smooth affine schemes, and in particular
smooth affine groups, to be restricted to the smaller base ring.

The infinitesimal lifting property passes through `WeilRestriction.homEquiv`: tensoring a
surjection with square-zero kernel gives another surjection with square-zero kernel.
`Ideal.ker_tensorProduct_map_id_quotient` supplies the kernel calculation from Mathlib's
tensor-product right exactness; no flatness assumption is needed for that calculation.

## References

* F. Bruhat, J. Tits, *Groupes réductifs sur un corps local II*, §1.5.9, p. 28.
-/

public section

open Algebra

namespace TauCeti.Algebra.WeilRestriction

variable (A B C : Type*) [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra B C] [Module.Finite A B] [Module.Projective A B]
  [FinitePresentation B C]

/-- Weil restriction of a formally smooth finitely presented algebra along a finite
projective algebra is formally smooth. -/
instance instFormallySmooth [FormallySmooth B C] :
    FormallySmooth A (WeilRestriction A B C) := by
  refine FormallySmooth.of_comp_surjective fun T _ _ I hI f ↦ ?_
  let q := Algebra.TensorProduct.lTensor (S := B) B (Ideal.Quotient.mkₐ A I)
  have hq : Function.Surjective q :=
    LinearMap.lTensor_surjective B Ideal.Quotient.mk_surjective
  have hqker : RingHom.ker q = Ideal.rightTensorIdeal A B I :=
    Ideal.ker_tensorProduct_map_id_quotient (R := A) (A := B) I
  have hker : RingHom.ker q ^ 2 = ⊥ := by
    rw [hqker, Ideal.rightTensorIdeal_def, ← Ideal.map_pow, hI, Ideal.map_bot]
  let g := FormallySmooth.liftOfSurjective (homEquiv A B C (T ⧸ I) f) q hq ⟨2, hker⟩
  refine ⟨(homEquiv A B C T).symm g, ?_⟩
  apply (homEquiv A B C (T ⧸ I)).injective
  rw [homEquiv_comp, Equiv.apply_symm_apply]
  exact FormallySmooth.comp_liftOfSurjective (homEquiv A B C (T ⧸ I) f) q hq ⟨2, hker⟩

/-- Weil restriction along a finite projective algebra preserves smoothness. -/
instance instSmooth [Smooth B C] : Smooth A (WeilRestriction A B C) where

end TauCeti.Algebra.WeilRestriction

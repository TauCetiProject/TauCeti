/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.RingHom.Flat

/-!
# Descent of flatness and faithful flatness

Faithful flatness of a module descends along a faithfully flat extension of the base,
complementing Mathlib's descent of flatness (`Module.Flat.of_flat_tensorProduct`). Thus both
can be established after extending scalars to a faithfully flat algebra. The
ring-homomorphism formulations supply the descent properties used to descend flat morphisms of
schemes along fpqc covers, and finite faithfully flat morphisms such as isogenies of affine
group schemes. For an algebra homomorphism, `RingHom.FaithfullyFlat.of_lTensor` descends faithful
flatness along a faithfully flat extension of the common scalar ring, with no restriction on the
universes of the rings involved.
-/

public section

open TensorProduct

/-- Faithful flatness of a module descends along faithfully flat scalar extension. -/
theorem Module.FaithfullyFlat.of_faithfullyFlat_tensorProduct
    (R M S : Type*) [CommRing R] [AddCommGroup M] [Module R M] [CommRing S] [Algebra R S]
    [Module.FaithfullyFlat R S] [Module.FaithfullyFlat S (S ⊗[R] M)] :
    Module.FaithfullyFlat R M := by
  refine (iff_flat_and_rTensor_reflects_triviality R M).2
    ⟨Module.Flat.of_flat_tensorProduct R M S, fun N _ _ _ ↦ ?_⟩
  simpa using (AlgebraTensorModule.distribBaseChange R S N M).symm.subsingleton

/-- Faithfully flat ring maps descend along faithfully flat base change. -/
theorem RingHom.FaithfullyFlat.codescendsAlong_faithfullyFlat :
    RingHom.CodescendsAlong RingHom.FaithfullyFlat RingHom.FaithfullyFlat := by
  refine .mk _ RingHom.FaithfullyFlat.respectsIso fun R S T _ _ _ _ _ h h' ↦ ?_
  rw [RingHom.faithfullyFlat_algebraMap_iff] at h h' ⊢
  exact Module.FaithfullyFlat.of_faithfullyFlat_tensorProduct R T S

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- Faithful flatness of an algebra homomorphism descends along a faithfully flat extension of
the common scalar ring: the converse of `RingHom.FaithfullyFlat.lTensor`. The rings may lie in
different universes, unlike in `RingHom.FaithfullyFlat.codescendsAlong_faithfullyFlat`. -/
theorem RingHom.FaithfullyFlat.of_lTensor {R S : Type*} (A : Type*) {B D : Type*} [CommRing R]
    [CommSemiring S] [Algebra R S] [CommRing A] [Algebra R A] [Algebra S A] [IsScalarTower R S A]
    [CommRing B] [Algebra R B] [CommRing D] [Algebra R D] [Module.FaithfullyFlat R A]
    {f : B →ₐ[R] D} (hf : (Algebra.TensorProduct.lTensor (S := S) A f).FaithfullyFlat) :
    f.FaithfullyFlat := by
  algebraize [f.toRingHom, (Algebra.TensorProduct.lTensor (S := S) A f).toRingHom]
  -- `A ⊗[R] D` is the base change of `D` along `B → A ⊗[R] B`, as in `RingHom.Flat.lTensor`.
  let e : A ⊗[R] D ≃ₐ[A ⊗[R] B] (A ⊗[R] B) ⊗[B] D :=
    { __ := (Algebra.IsPushout.cancelBaseChangeAlg _ _ _ _ _).symm,
      commutes' x := congr($(Algebra.IsPushout.cancelBaseChange_symm_comp_lTensor R B D A) x) }
  have : Module.FaithfullyFlat (A ⊗[R] B) ((A ⊗[R] B) ⊗[B] D) :=
    .of_linearEquiv _ _ e.symm.toLinearEquiv
  have : Module.FaithfullyFlat B (A ⊗[R] B) :=
    .of_linearEquiv B _ (Algebra.TensorProduct.commRight R B A).symm.toLinearEquiv
  exact Module.FaithfullyFlat.of_faithfullyFlat_tensorProduct B D (A ⊗[R] B)

/-- Flat ring maps descend along faithfully flat base change. -/
theorem RingHom.Flat.codescendsAlong_faithfullyFlat :
    RingHom.CodescendsAlong RingHom.Flat RingHom.FaithfullyFlat := by
  refine .mk _ RingHom.Flat.respectsIso fun R S T _ _ _ _ _ h h' ↦ ?_
  rw [RingHom.faithfullyFlat_algebraMap_iff] at h
  rw [RingHom.flat_algebraMap_iff] at h' ⊢
  exact Module.Flat.of_flat_tensorProduct R T S

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
group schemes.
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

/-- Flat ring maps descend along faithfully flat base change. -/
theorem RingHom.Flat.codescendsAlong_faithfullyFlat :
    RingHom.CodescendsAlong RingHom.Flat RingHom.FaithfullyFlat := by
  refine .mk _ RingHom.Flat.respectsIso fun R S T _ _ _ _ _ h h' ↦ ?_
  rw [RingHom.faithfullyFlat_algebraMap_iff] at h
  rw [RingHom.flat_algebraMap_iff] at h' ⊢
  exact Module.Flat.of_flat_tensorProduct R T S

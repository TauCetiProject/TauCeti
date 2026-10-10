/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Kernel.Exact
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Kernel.BaseChange
import TauCeti.RingTheory.Flat.Descent
import TauCeti.RingTheory.TensorProduct.Descent

/-!
# Base change and descent of short exact sequences of affine groups

A short exact sequence of affine group schemes remains short exact after every extension
of the base ring. Conversely, a sequence is short exact if it becomes so after a faithfully
flat extension. In particular, exactness over a field can be checked over an algebraic closure.

The coordinate formulation retains the full scheme-theoretic kernel, including infinitesimal
structure. It requires neither smoothness nor finite type. Preservation uses faithful flatness
of the quotient projection and right exactness of scalar extension for the closed immersion.
Reflection uses faithfully flat descent and injectivity of scalar extension on Hopf ideals.

The preservation theorem allows separate universes. The descent theorem uses a common universe
for all rings, as required by `RingHom.CodescendsAlong.of_tensorProduct_map`.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti.CommHopfAlgCat

universe u v w

section BaseChange

variable {R : Type u} {S : Type w} [CommRing R] [CommRing S] [Algebra R S]
variable {Q G N : _root_.CommHopfAlgCat.{v} R}

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
private theorem faithfullyFlat_lTensor {A B : Type v} [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (f : A →ₐ[R] B)
    (hf : f.toRingHom.FaithfullyFlat) :
    (Algebra.TensorProduct.lTensor (S := S) S f).toRingHom.FaithfullyFlat := by
  algebraize [f.toRingHom, (Algebra.TensorProduct.lTensor (S := S) S f).toRingHom]
  -- This is the same pushout comparison used by `RingHom.Flat.lTensor`.
  let e : S ⊗[R] B ≃ₐ[S ⊗[R] A] (S ⊗[R] A) ⊗[A] B :=
    { __ := (Algebra.IsPushout.cancelBaseChangeAlg _ _ _ _ _).symm,
      commutes' x := congr($(Algebra.IsPushout.cancelBaseChange_symm_comp_lTensor R A B S) x) }
  exact Module.FaithfullyFlat.of_linearEquiv _ _ e.toLinearEquiv

private theorem ker_baseChangeMap {i : G ⟶ N} (hi : Function.Surjective i.hom) :
    RingHom.ker (baseChangeMap (K := S) i).hom.toAlgHom.toRingHom =
      (baseChangeHopfIdeal (K := S) (HopfIdeal.kerOfSurjective i.hom hi)).toIdeal := by
  rw [baseChangeHopfIdeal_toIdeal, HopfIdeal.kerOfSurjective_toIdeal, hom_baseChangeMap]
  exact Algebra.TensorProduct.lTensor_ker i.hom.toAlgHom hi

/-- Every extension of the base ring preserves short exact sequences of affine group schemes. -/
theorem IsShortExact.baseChange {p : Q ⟶ G} {i : G ⟶ N} (h : IsShortExact p i) :
    IsShortExact (baseChangeMap (K := S) p) (baseChangeMap (K := S) i) := by
  refine ⟨?_, baseChangeMap_surjective i h.surjective, ?_⟩
  · rw [hom_baseChangeMap]
    exact faithfullyFlat_lTensor p.hom.toAlgHom h.faithfullyFlat
  · rw [ker_baseChangeMap h.surjective, h.kerOfSurjective_eq_kernelHopfIdeal,
      baseChangeHopfIdeal_kernelHopfIdeal]

end BaseChange

section Descent

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable [Module.FaithfullyFlat R S] {Q G N : _root_.CommHopfAlgCat.{u} R}

/-- Faithfully flat scalar extension preserves and reflects short exact sequences of affine
group schemes. Over a field this applies to every field extension, including algebraic closure. -/
@[simp]
theorem isShortExact_baseChangeMap_iff (p : Q ⟶ G) (i : G ⟶ N) :
    IsShortExact (baseChangeMap (K := S) p) (baseChangeMap (K := S) i) ↔
      IsShortExact p i := by
  constructor
  · intro h
    have hi : Function.Surjective i.hom :=
      (Module.FaithfullyFlat.lTensor_surjective_iff_surjective R S i.hom.toLinearMap).mp
        h.surjective
    refine ⟨?_, hi, ?_⟩
    · have hmap : (baseChangeMap (K := S) p).hom.toAlgHom.toRingHom =
          (Algebra.TensorProduct.map (AlgHom.id R S) p.hom.toAlgHom).toRingHom := by
        exact congrArg (fun g ↦ g.toAlgHom.toRingHom) (hom_baseChangeMap (K := S) p)
      exact RingHom.FaithfullyFlat.codescendsAlong_faithfullyFlat.of_tensorProduct_map
        p.hom.toAlgHom (hmap ▸ h.faithfullyFlat)
    · have hker := h.ker_eq
      rw [ker_baseChangeMap hi, ← baseChangeHopfIdeal_kernelHopfIdeal] at hker
      have heq : HopfIdeal.kerOfSurjective i.hom hi = kernelHopfIdeal p := by
        apply baseChangeHopfIdeal_injective (K := S)
        ext x
        rw [← HopfIdeal.mem_toIdeal, ← HopfIdeal.mem_toIdeal, hker]
      ext x
      rw [← heq, HopfIdeal.mem_toIdeal, HopfIdeal.mem_kerOfSurjective, RingHom.mem_ker,
        AlgHom.toRingHom_eq_coe, RingHom.coe_coe, BialgHom.coe_toAlgHom]
  · exact IsShortExact.baseChange

end Descent

end TauCeti.CommHopfAlgCat

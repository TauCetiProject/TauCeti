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
# Faithfully flat descent of short exact sequences of affine groups

A sequence of affine group schemes is short exact if and only if it becomes short exact
under a faithfully flat extension of the base ring. Over a field this permits exactness
checks after any field extension, including an algebraic closure.

The coordinate proof descends faithful flatness, surjectivity, and equality of the kernel
Hopf ideals. It retains the full scheme-theoretic kernel, including infinitesimal structure,
and requires neither smoothness nor finite type. Preservation under arbitrary base change
is already supplied by `IsShortExact.baseChange`.

The extending algebra and the coordinate Hopf algebras share a universe, as required by
`RingHom.CodescendsAlong.of_tensorProduct_map`. The base ring may lie in a separate universe.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti.CommHopfAlgCat

universe u v

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable {Q G N : _root_.CommHopfAlgCat.{v} R}

private theorem ker_baseChangeMap {i : G ⟶ N} (hi : Function.Surjective i.hom) :
    RingHom.ker (baseChangeMap (K := S) i).hom.toAlgHom.toRingHom =
      (baseChangeHopfIdeal (K := S) (HopfIdeal.kerOfSurjective i.hom hi)).toIdeal := by
  rw [baseChangeHopfIdeal_toIdeal, HopfIdeal.kerOfSurjective_toIdeal, hom_baseChangeMap]
  exact Algebra.TensorProduct.lTensor_ker i.hom.toAlgHom hi

variable [Module.FaithfullyFlat R S]

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
        -- The exported bialgebra equation induces the scalar-extension equation on ring maps.
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
  · exact fun h ↦ h.baseChange S

end TauCeti.CommHopfAlgCat

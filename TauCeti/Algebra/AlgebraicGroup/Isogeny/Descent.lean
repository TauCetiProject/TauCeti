/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Isogeny.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Kernel.ScalarExtension
import TauCeti.Algebra.AlgebraicGroup.Center.BaseChange
import TauCeti.RingTheory.Flat.Descent
import TauCeti.RingTheory.TensorProduct.Descent
import Mathlib.RingTheory.Finiteness.Descent

/-!
# Descent of isogenies

A coordinate morphism is an isogeny if and only if it becomes one after faithfully flat
extension of the base ring. Over fields, the same holds for central isogenies. Consequently,
central isogenies can be detected after passage to an algebraic closure, where character
lattices can be used for groups of multiplicative type.

Finiteness and faithful flatness descend as properties of ring homomorphisms. Centrality
descends because formation of the center and of the kernel Hopf ideal commutes with field
extension, and faithfully flat extension reflects containment of ideals.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§2 and 12.
-/

public section

open CategoryTheory

namespace TauCeti.CommHopfAlgCat

universe u

section Ring

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable [Module.FaithfullyFlat R S] {H K : _root_.CommHopfAlgCat.{u} R}

/-- Faithfully flat scalar extension preserves and reflects isogenies. -/
@[simp]
theorem isIsogeny_baseChangeMap_iff (f : H ⟶ K) :
    IsIsogeny (baseChangeMap (K := S) f) ↔ IsIsogeny f := by
  constructor
  · intro hf
    have hmap : (baseChangeMap (K := S) f).hom.toAlgHom.toRingHom =
        (Algebra.TensorProduct.map (AlgHom.id R S) f.hom.toAlgHom).toRingHom := by
      apply RingHom.ext
      intro z
      induction z using TensorProduct.inductionOn with
      | tmul s x => exact baseChangeMap_apply_tmul f s x
      | add x y hx hy => simp only [map_add, hx, hy]
    apply (isIsogeny_iff f).mpr
    exact ⟨RingHom.Finite.codescendsAlong_faithfullyFlat.of_tensorProduct_map
        f.hom.toAlgHom (by rw [← hmap]; exact hf.finite),
      RingHom.FaithfullyFlat.codescendsAlong_faithfullyFlat.of_tensorProduct_map
        f.hom.toAlgHom (hmap ▸ hf.faithfullyFlat)⟩
  · exact IsIsogeny.baseChange

end Ring

section Field

variable {k L : Type u} [Field k] [Field L] [Algebra k L]
variable {H K : _root_.CommHopfAlgCat.{u} k}

/-- Field extension preserves and reflects central isogenies, including those with
non-reduced kernels. -/
@[simp]
theorem isCentralIsogeny_baseChangeMap_iff (f : H ⟶ K) :
    IsCentralIsogeny (baseChangeMap (K := L) f) ↔ IsCentralIsogeny f := by
  constructor
  · intro hf
    have hi := (isIsogeny_baseChangeMap_iff f).mp hf.isIsogeny
    apply (isCentralIsogeny_iff f).mpr
    refine ⟨hi.finite, hi.faithfullyFlat, ?_⟩
    have hcentral := hf.isCentral_kernelHopfIdeal
    rw [← centerDefiningIdeal_le_iff, ← baseChangeHopfIdeal_centerDefiningIdeal,
      ← baseChangeHopfIdeal_kernelHopfIdeal,
      baseChangeHopfIdeal_le_iff_of_faithfullyFlat, centerDefiningIdeal_le_iff] at hcentral
    exact hcentral
  · exact IsCentralIsogeny.baseChange

end Field

end TauCeti.CommHopfAlgCat

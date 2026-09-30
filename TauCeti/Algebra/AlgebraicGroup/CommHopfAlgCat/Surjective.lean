/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.DominantPoints
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-!
# Surjectivity of affine group morphisms

An injective map of finite-type commutative Hopf algebras over a field induces a
surjection on prime spectra. Consequently, for such a map, faithful flatness is equivalent
to flatness. Neither smoothness nor reducedness is required, and the ground field need not
be algebraically closed.

The spectral surjectivity theorem lifts a prime to the algebraic closure of its residue
field and uses surjectivity on geometric points. This separates the surjectivity input to
faithful flatness of quotient morphisms from the remaining flatness argument.

## References

* J. S. Milne, *Algebraic Groups* (2017), §5, homomorphism theorems.
-/

public section

open CategoryTheory WithConv

namespace TauCeti.CommHopfAlgCat

universe u v

variable {k : Type u} [Field k] {H K : _root_.CommHopfAlgCat.{v} k}
  [Algebra.FiniteType k H] [Algebra.FiniteType k K]

/-- An injective homomorphism of finite-type commutative Hopf algebras over any field
induces a surjection on prime spectra. -/
theorem comap_surjective_of_injective (f : H ⟶ K) (hf : Function.Injective f.hom) :
    Function.Surjective (PrimeSpectrum.comap f.hom.toAlgHom.toRingHom) := by
  intro p
  let L := AlgebraicClosure p.asIdeal.ResidueField
  let a : H →ₐ[k] L := (IsScalarTower.toAlgHom k p.asIdeal.ResidueField L).comp
    (IsScalarTower.toAlgHom k H p.asIdeal.ResidueField)
  obtain ⟨q, hq⟩ := mapPointsFunctor_app_surjective_of_injective L f hf (toConv a)
  have hcomp : q.ofConv.comp f.hom.toAlgHom = a :=
    congrArg ofConv ((mapPointsFunctor_app_apply f (CommAlgCat.of k L) q).symm.trans hq)
  refine ⟨⟨RingHom.ker q.ofConv.toRingHom, RingHom.ker_isPrime _⟩, ?_⟩
  apply PrimeSpectrum.ext
  rw [PrimeSpectrum.comap_asIdeal, RingHom.comap_ker]
  have hker := congrArg (fun g : H →ₐ[k] L ↦ RingHom.ker g.toRingHom) hcomp
  refine hker.trans ?_
  ext x
  simp only [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, a,
    AlgHom.comp_apply, IsScalarTower.toAlgHom_apply]
  rw [map_eq_zero_iff _ (algebraMap p.asIdeal.ResidueField L).injective,
    Ideal.algebraMap_residueField_eq_zero]

/-- For an injective coordinate morphism between finite-type affine groups over a field,
faithful flatness is equivalent to flatness. -/
theorem faithfullyFlat_iff_flat_of_injective (f : H ⟶ K) (hf : Function.Injective f.hom) :
    f.hom.toAlgHom.toRingHom.FaithfullyFlat ↔ f.hom.toAlgHom.toRingHom.Flat := by
  rw [RingHom.FaithfullyFlat.iff_flat_and_comap_surjective,
    and_iff_left (comap_surjective_of_injective f hf)]

end TauCeti.CommHopfAlgCat

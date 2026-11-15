/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.LinearAlgebra.TensorProduct.FiniteExtension
public import TauCeti.RingTheory.Ideal.MinimalPrime.Finite
public import TauCeti.RingTheory.Ideal.MinimalPrime.TensorProduct

/-!
# Descent of minimal primes to a finite field extension

For an algebraic field extension `L / K`, finitely many minimal primes of `L ⊗[K] A` can
already be distinguished over a finite intermediate field. Contraction then gives a bijection
on minimal primes. This also holds over every larger intermediate field, so the field of
definition may be enlarged to accommodate other finite splitting problems.

The finiteness hypothesis on the minimal primes holds whenever `L ⊗[K] A` is Noetherian.

## References

* The Stacks Project, Section 33.8, *Geometrically irreducible schemes*.
-/

public section

open scoped TensorProduct

namespace Ideal

/-- Finitely many minimal primes after an algebraic scalar extension are all distinguished
over a single finite intermediate field. Every larger intermediate field also gives a
bijection on minimal primes by contraction. -/
theorem exists_finiteDimensional_bijOn_comap_minimalPrimes
    {K L A : Type*} [Field K] [Field L] [CommRing A] [Algebra K L]
    [Algebra.IsAlgebraic K L] [Algebra K A]
    (hfin : (minimalPrimes (L ⊗[K] A)).Finite) :
    ∃ E : IntermediateField K L, FiniteDimensional K E ∧
      ∀ F : IntermediateField K L, E ≤ F →
        Set.BijOn (Ideal.comap (Algebra.TensorProduct.map F.val (AlgHom.id K A)))
          (minimalPrimes (L ⊗[K] A)) (minimalPrimes (F ⊗[K] A)) := by
  classical
  -- One tensor per component isolates its generic point from all the other generic points.
  choose g hg hsep using fun P : minimalPrimes (L ⊗[K] A) ↦
    Ideal.exists_notMem_forall_le_of_mem_minimalPrimes ⊥ hfin P.property
  have : Finite (minimalPrimes (L ⊗[K] A)) := hfin.to_subtype
  obtain ⟨E, hE, hdef⟩ :=
    Set.exists_finiteDimensional_intermediateField_subset_range_rTensor
      (Set.range g) (Set.finite_range g)
  refine ⟨E, hE, fun F hEF ↦ ?_⟩
  let f := Algebra.TensorProduct.map F.val (AlgHom.id K A)
  have hf : Function.Injective f :=
    Module.Flat.rTensor_preserves_injective_linearMap F.val.toLinearMap Subtype.val_injective
  have hlift (P : minimalPrimes (L ⊗[K] A)) : g P ∈ Set.range f := by
    obtain ⟨x, hx⟩ := hdef ⟨P, rfl⟩
    refine ⟨Algebra.TensorProduct.map (IntermediateField.inclusion hEF) (AlgHom.id K A) x, ?_⟩
    -- The maps here are the tensor extensions of the two compatible field inclusions.
    have hcomp : f.comp
        (Algebra.TensorProduct.map (IntermediateField.inclusion hEF) (AlgHom.id K A)) =
        Algebra.TensorProduct.map E.val (AlgHom.id K A) := by
      ext <;> simp [f]
    exact DFunLike.congr_fun hcomp x |>.trans hx
  refine ⟨fun Q hQ ↦ Q.comap_tensorProduct_map_mem_minimalPrimes hQ, ?_, ?_⟩
  · intro P hP Q hQ heq
    obtain ⟨x, hx⟩ := hlift ⟨P, hP⟩
    have hxP : x ∉ P.comap f := by simpa [Ideal.mem_comap, hx] using hg ⟨P, hP⟩
    have hxQ : g ⟨P, hP⟩ ∉ Q := by
      have hxQ' : x ∉ Q.comap f := by
        rw [← heq]
        exact hxP
      simpa [Ideal.mem_comap, hx] using hxQ'
    have hPQ := hsep ⟨P, hP⟩ Q hQ.isPrime bot_le hxQ
    exact le_antisymm hPQ (hQ.2 hP.1 hPQ)
  · intro P hP
    exact Ideal.exists_minimalPrimes_comap_eq f.toRingHom P
      (by rwa [Ideal.comap_bot_of_injective f.toRingHom hf])

/-- A finite family of algebras has a common finite field over which all its minimal primes
are distinguished. The bijections persist after enlarging that intermediate field. -/
theorem exists_finiteDimensional_forall_bijOn_comap_minimalPrimes
    {K L : Type*} [Field K] [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
    {ι : Type*} [Finite ι] (A : ι → Type*) [∀ i, CommRing (A i)] [∀ i, Algebra K (A i)]
    (hfin : ∀ i, (minimalPrimes (L ⊗[K] A i)).Finite) :
    ∃ E : IntermediateField K L, FiniteDimensional K E ∧
      ∀ F : IntermediateField K L, E ≤ F → ∀ i,
        Set.BijOn (Ideal.comap (Algebra.TensorProduct.map F.val (AlgHom.id K (A i))))
          (minimalPrimes (L ⊗[K] A i)) (minimalPrimes (F ⊗[K] A i)) := by
  choose E hE hbij using fun i ↦ exists_finiteDimensional_bijOn_comap_minimalPrimes (hfin i)
  have : ∀ i, FiniteDimensional K (E i) := hE
  refine ⟨(⨆ i, E i), inferInstance, ?_⟩
  intro F hF i
  exact hbij i F ((le_iSup E i).trans hF)

end Ideal

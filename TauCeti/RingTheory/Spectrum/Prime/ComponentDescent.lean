/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.RingTheory.Ideal.MinimalPrime.Descent
public import TauCeti.RingTheory.Spectrum.Prime.Topology
public import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.FiniteStability

/-!
# Finite fields of definition for affine irreducible components

For a finite family of finitely generated `K`-algebras and an algebraic extension `L / K`,
there is a finite intermediate field over which all the irreducible components of their
spectra over `L` are distinguished. The component over the smaller field is the closure of
the image of the component over `L`. This labelling remains bijective over every larger
intermediate field.

Taking `L` to be a separable closure gives a common finite separable extension distinguishing
the geometric components on every affine chart. These results concern affine spectra only.

## References

* The Stacks Project, Section 33.8, *Geometrically irreducible schemes*.
-/

public section

open scoped TensorProduct

namespace PrimeSpectrum

/-- For finitely many affine schemes of finite type, their components over an algebraic
extension are all distinguished over one finite intermediate field. This continues to hold
after enlarging that field, for example to split other finite data at the same time. -/
theorem exists_finiteDimensional_forall_bijOn_closure_image_comap_irreducibleComponents
    {K L : Type*} [Field K] [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
    {ι : Type*} [Finite ι] (A : ι → Type*) [∀ i, CommRing (A i)] [∀ i, Algebra K (A i)]
    [∀ i, Algebra.FiniteType K (A i)] :
    ∃ E : IntermediateField K L, FiniteDimensional K E ∧
      ∀ F : IntermediateField K L, E ≤ F → ∀ i,
        Set.BijOn (fun Z ↦ closure
          (comap (Algebra.TensorProduct.map F.val (AlgHom.id K (A i))).toRingHom '' Z))
          (irreducibleComponents (PrimeSpectrum (L ⊗[K] A i)))
          (irreducibleComponents (PrimeSpectrum (F ⊗[K] A i))) := by
  have : ∀ i, IsNoetherianRing (L ⊗[K] A i) := fun _ ↦
    Algebra.FiniteType.isNoetherianRing L _
  obtain ⟨E, hE, hbij⟩ := Ideal.exists_finiteDimensional_forall_bijOn_comap_minimalPrimes A
    (fun i ↦ minimalPrimes.finite_of_isNoetherianRing (L ⊗[K] A i))
  exact ⟨E, hE, fun F hF i ↦
    RingHom.bijOn_closure_image_comap_irreducibleComponents _ (hbij F hF i)⟩

end PrimeSpectrum

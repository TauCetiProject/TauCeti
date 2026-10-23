/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.RingTheory.NormTrace.Pi
public import Mathlib.RingTheory.Etale.Field

/-!
# Norms from finite reduced algebras with a rational point

A finite reduced algebra over a field with a rational point has a surjective norm on units.
Its field-product decomposition has a factor equal to the base field; a unit supported in
that factor, with value one in the other factors, realizes any prescribed norm.

In particular, a finite separable field extension embedded in a field `F` has a scalar
extension to `F` whose norm on units is surjective. This supplies local norms when a radical
extension splits at a place, in the Kummer proof of the fundamental inequalities.

The decomposition and norm calculation use Mathlib's `IsArtinianRing.equivPi` and
`TauCeti.Algebra.mem_range_normUnits_iff_of_algEquiv`.

## References

* J. S. Milne, *Class Field Theory*, v4.03, Chapter VII, Proposition 6.10.
-/

public noncomputable section

open scoped TensorProduct

namespace AlgHom

variable {K A : Type*} [Field K] [CommRing A] [Algebra K A]

/-- The norm on units of a finite reduced algebra with a rational point is surjective.
Reducedness is essential: the norm of a dual number is the square of its constant term. -/
theorem normUnits_surjective [Module.Finite K A] [IsReduced A] (f : A →ₐ[K] K) :
    Function.Surjective (TauCeti.Algebra.normUnits K (S := A)) := by
  classical
  have : IsArtinianRing A := .of_finite K A
  have hf : Function.Surjective f := fun x ↦ ⟨algebraMap K A x, f.commutes x⟩
  let m : MaximalSpectrum A := ⟨RingHom.ker f, RingHom.ker_isMaximal_of_surjective f hf⟩
  let e := (IsArtinianRing.equivPi A).restrictScalars K
  let q : (A ⧸ m.asIdeal) ≃ₐ[K] K := Ideal.quotientKerAlgEquivOfSurjective hf
  intro a
  rw [← MonoidHom.mem_range, TauCeti.Algebra.mem_range_normUnits_iff_of_algEquiv e]
  refine ⟨Pi.mulSingle m (Units.map q.symm.toMonoidHom a), ?_⟩
  rw [finprod_eq_single _ m fun i hi ↦ by simp [Pi.mulSingle_eq_of_ne hi]]
  apply Units.ext
  rw [TauCeti.Algebra.coe_normUnits, ← Algebra.norm_eq_of_algEquiv q, Algebra.norm_self]
  simp

/-- If a finite separable field extension admits an embedding into `F`, its scalar extension
has a surjective norm on units over `F`. -/
theorem normUnits_tensorProduct_surjective
    {L F : Type*} [Field L] [Field F] [Algebra K L] [Algebra K F]
    [Module.Finite K L] [Algebra.IsSeparable K L] (f : L →ₐ[K] F) :
    Function.Surjective (TauCeti.Algebra.normUnits F (S := F ⊗[K] L)) := by
  have := Algebra.FormallyEtale.of_isSeparable K L
  have : Algebra.FormallyEtale F (F ⊗[K] L) := inferInstance
  have := Algebra.FormallyUnramified.isReduced_of_field F (F ⊗[K] L)
  exact (Algebra.TensorProduct.lift (Algebra.ofId F F) f
    (fun x y ↦ Commute.all x (f y))).normUnits_surjective

end AlgHom

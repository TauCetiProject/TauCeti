/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Injective
public import TauCeti.RingTheory.LocalRing.Quotient
import TauCeti.Algebra.Module.Injective.Bidual

/-!
# Noetherian self-injective commutative rings are artinian

Over a self-injective commutative ring, a finitely generated ideal is its double
annihilator. Consequently, when the ring is noetherian, annihilation reverses and reflects
the order on all ideals. The ascending chain condition therefore gives the descending
chain condition.

For a local ring with finite residue field, `TauCeti.IsLocalRing.finite_of_isArtinianRing`
then proves that the ring is finite.
Thus finite coefficient duality applies to noetherian self-injective local rings without
an additional finiteness assumption on the ring.

The double-annihilator argument uses the reflexivity of finitely presented modules from
`TauCeti.Algebra.Module.Injective.Bidual`, applied to the quotient by the ideal.

## References

* T. Y. Lam, *Lectures on Modules and Rings*, Graduate Texts in Mathematics 189,
  Springer (1999), §15, especially Theorem 15.1, for the quasi-Frobenius theorem and
  its double-annihilator argument.
-/

public section

/-- A finitely generated ideal in a self-injective commutative ring is its double
annihilator. -/
@[simp]
theorem Ideal.annihilator_annihilator_of_fg {R : Type*} [CommRing R] [Module.Injective R R]
    (I : Ideal R) (hI : I.FG) : I.annihilator.annihilator = I := by
  have : Module.FinitePresentation R (R ⧸ I) :=
    Module.finitePresentation_of_surjective I.mkQ I.mkQ_surjective
      (by rwa [Submodule.ker_mkQ])
  apply le_antisymm
  · intro x hx
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply (Module.bijective_dual_eval R (R ⧸ I)).injective
    ext f
    have hfx (r : R) : f (Ideal.Quotient.mk I r) = r * f (Ideal.Quotient.mk I 1) := by
      simpa using (f.comp I.mkQ).map_smul r 1
    have hf : f (Ideal.Quotient.mk I 1) ∈ I.annihilator :=
      Submodule.mem_annihilator.mpr fun r hr ↦ by
        rw [smul_eq_mul, mul_comm, ← hfx]
        simp [Ideal.Quotient.eq_zero_iff_mem.mpr hr]
    have hx' := Submodule.mem_annihilator.mp hx _ hf
    simpa only [smul_eq_mul, ← hfx, map_zero, Module.Dual.eval_apply,
      LinearMap.zero_apply] using hx'
  · exact Submodule.le_annihilator_iff.mpr (Submodule.mul_annihilator I)

namespace TauCeti

/-- A noetherian self-injective commutative ring is artinian. -/
theorem isArtinianRing_of_injective (R : Type*) [CommRing R] [IsNoetherianRing R]
    [Module.Injective R R] : IsArtinianRing R := by
  have hanti : Antitone (fun I : Ideal R ↦ I.annihilator) :=
    fun _ _ h ↦ Submodule.annihilator_mono h
  have hinj : Function.Injective (fun I : Ideal R ↦ I.annihilator) :=
    Function.LeftInverse.injective fun I ↦
      I.annihilator_annihilator_of_fg (IsNoetherian.noetherian _)
  exact (hanti.strictAnti_of_injective hinj).wellFoundedLT

end TauCeti

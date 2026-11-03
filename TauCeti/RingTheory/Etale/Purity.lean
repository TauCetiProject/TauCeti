/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Etale.Discriminant
public import TauCeti.RingTheory.Ideal.Height
public import TauCeti.RingTheory.Unramified.Fiber
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Smooth.Fiber

/-!
# Purity for finite flat algebras

For a finite free algebra over a Noetherian ring, étaleness is detected on the fibres over primes
of height at most one: a nonunit discriminant belongs to such a prime by Krull's principal ideal
theorem. Consequently, over a Noetherian local ring of dimension at least two, a finite flat
algebra which is unramified away from the closed point is étale everywhere.

The last statement supplies the discriminant step in local purity arguments after flatness has
been established. It requires neither regularity nor normality of the base or the algebra.
Flatness is essential; this statement does not assert that arbitrary finite covers of a
punctured spectrum extend.

## Main results

* `TauCeti.Algebra.etale_iff_etale_fiber_of_height_le_one`: the fibre criterion for a finite
  free algebra over a Noetherian ring.
* `TauCeti.Algebra.etale_of_isUnramifiedAt_of_two_le_ringKrullDim`: a finite flat algebra over a
  Noetherian local ring of dimension at least two is étale if it is unramified at all primes not
  lying over the closed point.

## References

* [The Stacks Project, Lemma 58.21.3](https://stacks.math.columbia.edu/tag/0BMA),
  the discriminant argument after establishing flatness in dimension two.
* [The Stacks Project, Lemma 49.3.1](https://stacks.math.columbia.edu/tag/0BJF),
  the discriminant criterion for étaleness.
-/

public section

open scoped TensorProduct

namespace TauCeti.Algebra

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

/-- A finite free algebra over a Noetherian ring is étale if and only if its fibres over all
primes of height at most one are étale. Minimal primes must be included; no generic étaleness
assumption is imposed. -/
theorem etale_iff_etale_fiber_of_height_le_one [IsNoetherianRing A]
    [Module.Finite A B] [Module.Free A B] :
    Algebra.Etale A B ↔ ∀ (p : Ideal A) [p.IsPrime], p.height ≤ 1 →
      Algebra.Etale p.ResidueField (p.Fiber B) := by
  classical
  refine ⟨fun _ _ _ _ ↦ inferInstance, fun h ↦ ?_⟩
  let b := Module.Free.chooseBasis A B
  apply (etale_iff_isUnit_discr A B b).mpr
  apply (isUnit_iff_forall_notMem_of_height_le_one _).mpr
  intro p _ hp hmem
  exact (algebraMap_discr_ne_zero_iff_etale_baseChange b p.ResidueField).mpr (h p hp)
    (Ideal.algebraMap_residueField_eq_zero.mpr hmem)

/-- A finite flat algebra over a Noetherian local ring of dimension at least two is étale
everywhere if it is unramified at each prime not lying over the closed point. This is the finite
flat case of local purity, with no regularity or normality assumptions. -/
theorem etale_of_isUnramifiedAt_of_two_le_ringKrullDim
    [IsNoetherianRing A] [IsLocalRing A] [Module.Finite A B] [Module.Flat A B]
    (hdim : 2 ≤ ringKrullDim A)
    (h : ∀ (q : Ideal B) [q.IsPrime], q.under A ≠ IsLocalRing.maximalIdeal A →
      Algebra.IsUnramifiedAt A q) : Algebra.Etale A B := by
  have : Module.Free A B := Module.free_of_flat_of_isLocalRing
  apply etale_iff_etale_fiber_of_height_le_one.mpr
  intro p _ hp
  have hp_ne : p ≠ IsLocalRing.maximalIdeal A := by
    intro heq
    have hheight : (p.height : WithBot ℕ∞) ≤ 1 := by exact_mod_cast hp
    rw [heq, IsLocalRing.maximalIdeal_height_eq_ringKrullDim] at hheight
    have : (2 : WithBot ℕ∞) ≤ 1 := hdim.trans hheight
    norm_num at this
  have hunram : Algebra.IsUnramifiedIn B p :=
    fun q _ _ ↦ h q (by rwa [← q.over_def p])
  have : Algebra.FormallyUnramified p.ResidueField (p.Fiber B) :=
    Algebra.IsUnramifiedIn.formallyUnramified_fiber hunram
  have : Module.FinitePresentation p.ResidueField (p.Fiber B) :=
    Module.finitePresentation_of_projective _ _
  exact Algebra.Etale.of_formallyUnramified_of_flat

end TauCeti.Algebra

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import TauCeti.AlgebraicGeometry.Blowup.Submodule.Basic
public import TauCeti.AlgebraicGeometry.Cohomology.Module.Base
public import TauCeti.RingTheory.Huber.Basic
import TauCeti.AlgebraicGeometry.Blowup.Submodule.OpenSubring
import TauCeti.AlgebraicGeometry.Blowup.Submodule.Projective
import TauCeti.AlgebraicGeometry.Cohomology.ProjectiveSpace.Finite
import TauCeti.AlgebraicGeometry.Cohomology.Torsion
import TauCeti.AlgebraicGeometry.Restrict

/-!
# Cohomology of a submodule blowup over a ring of definition

`TauCeti.Huber.PairOfDefinition.exists_pow_le_annihilator_cohomology_submoduleBlowup` shows that
a power of the ideal of definition kills higher coherent cohomology on the submodule blowup.
The blowup is projective by `submoduleBlowup.isProjectiveOver` and is an isomorphism over the
non-open primes by `submoduleBlowup.isIso_toSpec_restrict_nonOpenPrimes`.

## References

* R. Huber, *A generalization of formal schemes and rigid analytic varieties*, Math. Z. 217
  (1994), §2, p. 528, proof of (1.3.1)(i).
-/

public section

open AlgebraicGeometry CategoryTheory Scheme.Modules
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme.Modules

namespace TauCeti.Huber.PairOfDefinition

universe u

/-- For a noetherian ring of definition, a power of its ideal of definition annihilates
positive-degree cohomology of any finite type quasi-coherent sheaf on the blowup of the
submodule spanned by a finite set `F` generating the unit ideal in the ambient Huber ring
(Huber, proof of (1.3.1)(i)). -/
theorem exists_pow_le_annihilator_cohomology_submoduleBlowup {A : Type u} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] (P : PairOfDefinition A)
    [IsNoetherianRing P.ringOfDefinition] {F : Set A} (hfin : F.Finite)
    (hF : Ideal.span F = ⊤) (M : (submoduleBlowup P.ringOfDefinition F).Modules)
    [M.IsQuasicoherent] [M.IsFiniteType] (n : ℕ) :
    ∃ k : ℕ, P.idealOfDefinition ^ k ≤
      Module.annihilator P.ringOfDefinition (Cohomology M (n + 1)) := by
  let C := P.ringOfDefinition
  have := submoduleBlowup.isNoetherian C hfin
  have := submoduleBlowup.isProjectiveOver C F hfin
  let _ : IsHuberRing A := ⟨⟨P⟩⟩
  have hiso := submoduleBlowup.isIso_toSpec_restrict_nonOpenPrimes C P.isOpen_ringOfDefinition hF
  apply M.exists_pow_le_annihilator_cohomology (n + 1) P.fg_idealOfDefinition
  intro r hr
  rw [submoduleBlowup.over_eq_toSpec]
  have hle : (PrimeSpectrum.basicOpen r : (Spec (.of C)).Opens) ≤ C.nonOpenPrimes := by
    rw [Subring.nonOpenPrimes_eq_iSup_basicOpen]
    exact le_iSup (fun s : {s : C // IsTopologicallyNilpotent (s : A)} ↦
      PrimeSpectrum.basicOpen s.val) ⟨r, P.isTopologicallyNilpotent_of_mem_idealOfDefinition hr⟩
  have hrestrict : IsIso (submoduleBlowup.toSpec C F ∣_ PrimeSpectrum.basicOpen r) :=
    (MorphismProperty.isomorphisms.iff _).mp (IsZariskiLocalAtTarget.restrict_of_le _
      ((MorphismProperty.isomorphisms.iff _).mpr hiso) hle)
  have haffine : IsAffineOpen (X := Spec (.of C)) (PrimeSpectrum.basicOpen r) :=
    IsAffineOpen.Spec_basicOpen (R := .of C) r
  exact subsingleton_cohomologyOn_succ_of_isAffineOpen M (.of_isIso
    ((submoduleBlowup.toSpec C F ∣_ PrimeSpectrum.basicOpen r) ≫ haffine.isoSpec.hom)) n

end TauCeti.Huber.PairOfDefinition

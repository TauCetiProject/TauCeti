/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import TauCeti.CategoryTheory.Abelian.Injective.Resolution.Minimal
import Mathlib.Algebra.Category.ModuleCat.Algebra
import Mathlib.RingTheory.Finiteness.Small
import TauCeti.Algebra.Module.Injective.Envelope.ModuleCat
import TauCeti.RingTheory.MatlisDuality.ArtinAlgebra

/-!
# Minimal injective resolutions over Artin algebras

A finitely generated module over an Artin algebra admits a minimal injective resolution by
finitely generated modules. The first term is the injective envelope of the given module and
subsequent terms are injective envelopes of the successive cosyzygies. Finite generation is
preserved because the injective envelope of a finitely generated module is finite and quotients
of finitely generated modules are finite.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*,
  Cambridge Studies in Advanced Mathematics 36, Cambridge University Press (1995), §§II.3–4.
-/

public section

open CategoryTheory Limits TauCeti
open scoped ModuleCat.Algebra

namespace ModuleCat

universe u v w

/-- Every finitely generated left module over a finite algebra over a commutative Artinian ring
has a minimal injective resolution with finitely generated terms in every degree. -/
theorem exists_isMinimal_injectiveResolution_of_finite {A : Type v} [Ring A]
    (M : ModuleCat.{w} A) (R : Type u) [CommRing R] [IsArtinianRing R] [Algebra R A]
    [Module.Finite R A] [Small.{w} A] [Module.Finite A M] :
    ∃ I : InjectiveResolution M, I.IsMinimal ∧ ∀ n, Module.Finite A (I.cocomplex.X n) := by
  refine TauCeti.exists_isMinimal_injectiveResolution_of_closedUnder_envelopes
    (Q := fun N : ModuleCat.{w} A ↦ Module.Finite A N) (Y := M) ?_ inferInstance
  intro N hN
  obtain ⟨J, _, _, hJ, i, hi⟩ := exists_isInjectiveEnvelope_finite R (A := A) N
  -- The envelope is finite over A, so it can be placed in the same universe as N.
  have : Small.{w} J := Module.Finite.small A J
  let e := Shrink.linearEquiv.{w} A J
  let ι : N ⟶ ModuleCat.of A (Shrink.{w} J) := ModuleCat.ofHom (e.symm.toLinearMap ∘ₗ i)
  have hess : IsEssentialMono ι := by
    refine (ModuleCat.isEssentialMono_iff ι).2 ⟨e.symm.injective.comp hi.injective, ?_⟩
    simpa only [ι, ModuleCat.hom_ofHom, LinearMap.range_comp] using
      (isEssential_map_equiv_iff e.symm).2 hi.isEssential_range
  have : Module.Injective A (Shrink.{w} J) :=
    Module.Baer.injective ((Module.Baer.of_injective hi.moduleInjective).of_equiv e.symm)
  refine ⟨_, ι, Module.injective_object_of_injective_module A _, hess, inferInstance, ?_⟩
  exact Module.Finite.of_surjective (cokernel.π ι).hom
    ((ModuleCat.epi_iff_surjective _).1 inferInstance)

end ModuleCat

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.AffineGlobalSections
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-!
# Global sections of quasicoherent sheaves on an affine scheme

An epimorphism of quasicoherent sheaves on `Spec R` is surjective on global sections. This is
the exactness step behind affine acyclicity: the quasicoherent sheaves on `Spec R` are equivalent
to `R`-modules by Mathlib's `AlgebraicGeometry.tildeEquiv`, and an epimorphism of modules is
surjective.

The epimorphism is taken in the category of all sheaves of modules, so the result applies to
the short exact sequences used in sheaf cohomology. The quasicoherence assumptions concern only
the source and target.

Consequently the global-section functor preserves short exact sequences of quasicoherent
sheaves on `Spec R`, even when exactness is stated in the category of all sheaves of modules.

This is the affine exactness statement used in the proof of Serre's affine acyclicity theorem;
see Hartshorne, *Algebraic Geometry*, Chapter III, Theorem 3.5.
-/

public section

open AlgebraicGeometry CategoryTheory

namespace TauCeti

namespace AlgebraicGeometry

universe u

variable {R : CommRingCat.{u}}

/-- Taking global sections preserves a short exact sequence whose middle and right terms are
quasicoherent sheaves on `Spec R`. The exactness hypothesis is in the ambient category of sheaves
of modules. -/
theorem shortExact_map_moduleSpecΓFunctor_of_isQuasicoherent
    {S : ShortComplex (Spec R).Modules} (hS : S.ShortExact)
    [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent] :
    (S.map (moduleSpecΓFunctor (R := R))).ShortExact := by
  have : (moduleSpecΓFunctor (R := R)).Additive :=
    (moduleSpecΓFunctor (R := R)).additive_of_preserves_binary_products
  have h := (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono
    (moduleSpecΓFunctor (R := R))).mp inferInstance S hS
  have : Epi S.g := hS.epi_g
  have hΓ : Epi ((moduleSpecΓFunctor (R := R)).map S.g) :=
    (ModuleCat.epi_iff_surjective _).mpr
      (surjective_globalSections_of_epi_of_isQuasicoherent S.g)
  exact { exact := h.1, mono_f := h.2, epi_g := hΓ }

end AlgebraicGeometry

end TauCeti

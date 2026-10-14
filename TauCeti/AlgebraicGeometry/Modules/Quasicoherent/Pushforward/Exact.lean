/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.AffineGlobalSections
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import TauCeti.AlgebraicGeometry.Modules.Sheaf

/-!
# Exactness of affine pushforward

Pushforward along an affine scheme morphism preserves epimorphisms between quasicoherent
module sheaves and short exact sequences with quasicoherent middle and right terms. Exactness
is stated in the ambient categories of module sheaves. No Noetherian, flatness or finiteness
hypothesis is imposed.

On every affine open of the target, pushforward sections are sections over an affine open of
the source. Affine exactness of global sections therefore gives surjectivity there. This is
the direct-image exactness used when computing relative cohomology from affine covers.

## References

* R. Hartshorne, *Algebraic Geometry*, III, Proposition 8.1 and Theorem 3.5.
* The Stacks Project, Tag 01XC (higher direct images under affine morphisms).
-/

public section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

open Scheme.Modules

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f]

/-- Affine pushforward preserves epimorphisms between quasicoherent module sheaves, with
epimorphisms taken in the ambient module-sheaf categories. -/
theorem epi_pushforward_map_of_isAffineHom {M N : X.Modules} (φ : M ⟶ N)
    [Epi φ] [M.IsQuasicoherent] [N.IsQuasicoherent] : Epi ((pushforward f).map φ) := by
  apply Scheme.Modules.Hom.epi_of_surjective_on_affineOpens
  intro U hU
  -- Pushforward on sections is restriction of scalars of the component over the preimage.
  rw [Scheme.Modules.pushforward_map_app]
  exact φ.app_surjective_of_epi_of_isAffineOpen (f ⁻¹ᵁ U) (hU.preimage f)

/-- Affine pushforward preserves a short exact sequence of module sheaves whose middle and
right terms are quasicoherent. The first term needs no quasicoherence assumption. -/
theorem shortExact_pushforward_of_isAffineHom {S : ShortComplex X.Modules}
    (hS : S.ShortExact) [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent] :
    (S.map (pushforward f)).ShortExact := by
  have : (pushforward f).Additive := (pushforward f).additive_of_preserves_binary_products
  have h := (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono
    (pushforward f)).mp inferInstance S hS
  have : Epi S.g := hS.epi_g
  exact { exact := h.1, mono_f := h.2, epi_g := f.epi_pushforward_map_of_isAffineHom S.g }

end AlgebraicGeometry.Scheme.Hom

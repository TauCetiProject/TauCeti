/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Grp
public import TauCeti.AlgebraicGeometry.FiniteEtale.Limits

/-!
# Finite étale group schemes

Group objects in `FiniteEtaleScheme S` are the finite étale group schemes over `S`: the inclusion
into `Over S` preserves finite products, so it is a braided monoidal functor for the cartesian
monoidal structures and carries group objects to group schemes over `S`, fully faithfully. A group
scheme over `S` comes from `FiniteEtaleScheme S` exactly when its underlying scheme is finite
étale over `S` (`TauCeti.FiniteEtaleScheme.essImage_mapGrp_ι_iff`).

## Main results

* `TauCeti.FiniteEtaleScheme.essImage_mapGrp_ι_iff`: the group schemes over `S` coming from group
  objects of `FiniteEtaleScheme S` are those whose underlying scheme is finite étale over `S`.
-/

public section

open CategoryTheory AlgebraicGeometry

universe u

namespace TauCeti

namespace FiniteEtaleScheme

variable (S : Scheme.{u})

/-- The inclusion of finite étale schemes over `S` into `Over S` is monoidal for the cartesian
monoidal structures, as it preserves finite products. -/
noncomputable instance : (finiteEtaleSchemeProperty S).ι.Monoidal :=
  .ofChosenFiniteProducts _

/-- The inclusion of finite étale schemes over `S` into `Over S` is braided. -/
noncomputable instance : (finiteEtaleSchemeProperty S).ι.Braided :=
  .ofChosenFiniteProducts _

variable {S}

/-- **Finite étale group schemes.** A group scheme over `S` is, up to isomorphism, a group object
of finite étale schemes over `S` if and only if its underlying scheme is finite and étale over
`S`. -/
theorem essImage_mapGrp_ι_iff {G : Grp (Over S)} :
    (finiteEtaleSchemeProperty S).ι.mapGrp.essImage G ↔ IsFinite G.X.hom ∧ Etale G.X.hom := by
  rw [Functor.essImage_mapGrp, ← finiteEtaleSchemeProperty_iff]
  exact ⟨fun ⟨X, ⟨e⟩⟩ ↦ (finiteEtaleSchemeProperty S).prop_of_iso e X.property,
    fun h ↦ ⟨⟨G.X, h⟩, ⟨Iso.refl _⟩⟩⟩

end FiniteEtaleScheme

end TauCeti

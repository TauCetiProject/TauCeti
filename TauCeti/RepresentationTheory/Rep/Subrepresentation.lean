/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Rep.Basic
public import TauCeti.RepresentationTheory.Subrepresentation

/-!
# The inclusion of a subrepresentation as a morphism of `Rep k G`

The inclusion `Subrepresentation.subtype W` of a subrepresentation `W` of `ρ` is an intertwining
map, so `Rep.ofHom W.subtype` is a morphism of `Rep k G` into `Rep.of ρ`. This file records how
the categorical properties of that morphism read off `W`: it is always a monomorphism, it is zero
exactly when `W = ⊥`, and it is an isomorphism exactly when `W = ⊤`. These are the facts through
which simplicity of an object of `Rep k G` or `FDRep k G` is compared with irreducibility of the
representation it carries.

## Main results

* `Rep.mono_ofHom_subtype`: the inclusion of a subrepresentation is a monomorphism.
* `Rep.ofHom_subtype_eq_zero_iff`: the inclusion is zero exactly when the subrepresentation is
  `⊥`.
* `Rep.isIso_ofHom_subtype_iff`: the inclusion is an isomorphism exactly when the
  subrepresentation is `⊤`.
-/

public section

open CategoryTheory

universe u v w

namespace Rep

variable {k : Type u} {G : Type v} [Ring k] [Monoid G] {V : Type w} [AddCommGroup V] [Module k V]
  {ρ : Representation k G V} (W : Subrepresentation ρ)

/-- The inclusion of a subrepresentation is a monomorphism of `Rep k G`. -/
instance mono_ofHom_subtype : Mono (Rep.ofHom W.subtype) :=
  (Rep.mono_iff_injective _).mpr W.subtype_injective

/-- The inclusion of a subrepresentation is the zero morphism of `Rep k G` exactly when the
subrepresentation is `⊥`. -/
@[simp]
theorem ofHom_subtype_eq_zero_iff : Rep.ofHom W.subtype = 0 ↔ W = ⊥ := by
  rw [Rep.hom_ext_iff, Rep.hom_ofHom, Rep.zero_hom, W.subtype_eq_zero_iff]

/-- The inclusion of a subrepresentation is an isomorphism of `Rep k G` exactly when the
subrepresentation is `⊤`. -/
theorem isIso_ofHom_subtype_iff : IsIso (Rep.ofHom W.subtype) ↔ W = ⊤ := by
  rw [isIso_iff_mono_and_epi, Rep.epi_iff_surjective, Rep.hom_ofHom, W.subtype_surjective_iff]
  exact and_iff_right inferInstance

end Rep

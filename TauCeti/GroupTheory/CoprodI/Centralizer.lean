/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.GroupTheory.CoprodI
import TauCeti.GroupTheory.PushoutI.Centralizer
import TauCeti.GroupTheory.PushoutI.TrivialBase
import TauCeti.GroupTheory.Subgroup.Centralizer

/-!
# Centralizers of elements of a factor of a free product

In a free product of groups, the centralizer of a nontrivial element `g` of one factor is the
centralizer of `g` in that factor: an element commuting with `g` lies in the factor of `g`. The
free product is the amalgamated product of its factors over the trivial group
(`Monoid.PushoutI.equivCoprodI`), and a nontrivial `g` is not conjugate into the trivial
amalgamated subgroup, so this is a case of the description of the centralizers of factor elements
of an amalgamated product (`Monoid.PushoutI.centralizer_of_eq_map`).

## Main results

* `Monoid.CoprodI.centralizer_of_eq_map`: the centralizer of a nontrivial element `g` of a factor
  of `CoprodI G` is the image of the centralizer of `g` in that factor.

## References

* R. C. Lyndon, P. E. Schupp, *Combinatorial group theory*, Springer (1977), Chapter IV, §1
  (the normal form theorem for free products).
-/

public section

open Subgroup

namespace Monoid.CoprodI

variable {ι : Type*} {G : ι → Type*} [∀ i, Group (G i)]

/-- **Centralizers of factor elements in a free product.** In a free product of groups, the
centralizer of a nontrivial element `g` of a factor is the centralizer of `g` in that factor. -/
theorem centralizer_of_eq_map {i : ι} {g : G i} (hg : g ≠ 1) :
    centralizer {(of g : CoprodI G)} = (centralizer {g}).map of := by
  -- `CoprodI G` is the amalgamated product `PushoutI φ` of the factors over the trivial group.
  let φ : ∀ i, Unit →* G i := fun _ => 1
  -- A conjugate of `g ≠ 1` is not in the trivial amalgamated subgroup.
  have hg' (k : G i) : k * g * k⁻¹ ∉ (φ i).range := fun ⟨_, hk⟩ => hg (conj_eq_one_iff.1 hk.symm)
  simpa using MulEquiv.centralizer_image_eq_map (PushoutI.equivCoprodI φ) (.id _)
    (fun _ => PushoutI.equivCoprodI_of _ _) (s := {g}) (by
      rw [Set.image_singleton]
      exact PushoutI.centralizer_of_eq_map (fun _ => Function.injective_of_subsingleton _) hg')

end Monoid.CoprodI

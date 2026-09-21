/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.GaloisGroups.Label
public import TauCeti.FieldTheory.GaloisGroups.Resolvent.Root

/-!
# Resolvents and transitive-group labels

The resolvent criterion of `TauCeti.ResolventSpec.exists_isRoot_specialize_iff_exists_le_map_conj`
compares the roots of a specialized resolvent in the base field with the Galois image of `f` read
through a numbering of its roots. That image is only defined up to a numbering, while the
transitive-group label `TauCeti.HasGaloisLabel` of `f` is not, so the criterion is restated here
against the label: a resolvent of `f` has a root in the base field exactly when the reference
subgroup of the label of `f` lies in a conjugate of the subgroup of the specification.

One direction assumes nothing about the resolvent; the converse needs the specialized resolvent
to be separable, since two orbit values that collide at the roots of `f` produce a root of the
resolvent that constrains the Galois image no further.

This is what turns a resolvent into a test on labels: for a fixed degree, the labels whose
reference subgroup is conjugate into the subgroup of the specification can be listed once and for
all as a statement of permutation group theory, and the resolvent then decides membership in that
list.

## Main results

* `TauCeti.HasGaloisLabel.exists_isRoot_specialize_of_exists_le_map_conj`: a label whose reference
  subgroup lies in a conjugate of the subgroup of the specification gives the resolvent a root in
  the base field.
* `TauCeti.HasGaloisLabel.exists_isRoot_specialize_iff`: conversely for a separable specialized
  resolvent, so that the resolvent decides the containment.

## References

* [H. Cohen, *A Course in Computational Algebraic Number Theory*][cohen1993], §6.3.
-/

public section

open Polynomial Equiv Equiv.Perm

namespace TauCeti

variable {F : Type*} [Field F] {f : F[X]} {n : ℕ} {j : TransitiveGroupIndex n}

/- The Galois action on the roots in the splitting field, which `Polynomial.Gal.galActionHom`
asks for; it stays local, as in `TauCeti.HasGaloisLabel`, because as a global instance it would
compete with Mathlib's intrinsic action. -/
local instance factSplitsSplittingFieldResolvent (f : F[X]) :
    Fact ((f.map (algebraMap F f.SplittingField)).Splits) :=
  ⟨SplittingField.splits f⟩

/-- **A label confined to the subgroup of a specification gives the resolvent a root.** If the
reference subgroup of the label of a monic `f` lies in a conjugate of the subgroup of a resolvent
specification, then the resolvent of `f` has a root in the base field. Nothing is assumed about
the resolvent. -/
theorem HasGaloisLabel.exists_isRoot_specialize_of_exists_le_map_conj (h : HasGaloisLabel f j)
    (hf : f.Monic) (spec : ResolventSpec n)
    (hle : ∃ τ : Perm (Fin n), referenceSubgroup n j ≤ spec.H.map (MulAut.conj τ).toMonoidHom) :
    ∃ a : F, (spec.specialize F f).IsRoot a := by
  have : IsGalois F f.SplittingField := IsGalois.of_separable_splitting_field h.separable
  obtain ⟨e⟩ := nonempty_rootSet_splittingField_equiv_fin f h.separable
  obtain ⟨τ, hτ⟩ :=
    (h.transitiveGroupLabel (e.trans (finCongr h.natDegree_eq))).exists_le_map_conj_iff.2 hle
  exact spec.exists_isRoot_specialize_of_le_map_conj hf h.separable h.natDegree_eq _ τ hτ

/-- **The resolvent criterion, read on the label.** Let `f` be monic with a transitive-group
label, and let the resolvent of `f` for a specification be separable. The resolvent then has a
root in the base field exactly when the reference subgroup of the label of `f` lies in a
conjugate of the subgroup of the specification.

Separability of the resolvent is what the forward implication needs; the reverse implication is
`TauCeti.HasGaloisLabel.exists_isRoot_specialize_of_exists_le_map_conj`, which assumes nothing
about the resolvent. -/
theorem HasGaloisLabel.exists_isRoot_specialize_iff (h : HasGaloisLabel f j) (hf : f.Monic)
    (spec : ResolventSpec n) (hres : (spec.specialize F f).Separable) :
    (∃ a : F, (spec.specialize F f).IsRoot a) ↔
      ∃ τ : Perm (Fin n), referenceSubgroup n j ≤ spec.H.map (MulAut.conj τ).toMonoidHom := by
  have : IsGalois F f.SplittingField := IsGalois.of_separable_splitting_field h.separable
  obtain ⟨e⟩ := nonempty_rootSet_splittingField_equiv_fin f h.separable
  rw [spec.exists_isRoot_specialize_iff_exists_le_map_conj hf h.separable h.natDegree_eq
    (e.trans (finCongr h.natDegree_eq)) hres]
  exact (h.transitiveGroupLabel _).exists_le_map_conj_iff

end TauCeti

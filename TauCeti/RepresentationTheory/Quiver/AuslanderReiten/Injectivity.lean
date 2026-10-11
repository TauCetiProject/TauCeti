/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.AuslanderReiten.Translation

/-!
# Injectivity of Auslander–Reiten translation

The partial translation on the quiver of irreducible morphisms is injective wherever it is
defined: two classes sent to the same class are equal. Restricting its domain to non-projective
classes therefore gives an injection into the non-injective classes. This is the injectivity
part of the correspondence between these two sets of indecomposables; surjectivity requires
the inverse translate `Tr D`.

The result holds over any field for quivers with finitely many paths, without a
representation-finiteness hypothesis. It uses the isomorphism-class detection theorem for
the module-level translate through the equivalence with path-algebra modules.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*,
  Cambridge University Press (1995), Sections IV.1 and VII.1.
-/

public section

namespace TauCeti.irreducibleMorphismQuiver

open CategoryTheory

universe u v w t

variable {k : Type u} {Q : Type v} [Field k] [Quiver.{w} Q]
  [Finite (Quiver.TotalPath Q)]

local instance : Finite Q :=
  Finite.of_injective (fun q : Q ↦ (⟨q, q, Quiver.Path.nil⟩ : Quiver.TotalPath Q))
    (fun _ _ h ↦ congrArg Sigma.fst h)

/-- Two indecomposable classes with the same defined translate are equal. -/
theorem eq_of_translate_eq_some
    {a b c : irreducibleMorphismQuiver.{u, v, w, max u v w t} k Q}
    (ha : translate.{u, v, w, t} a = some c)
    (hb : translate.{u, v, w, t} b = some c) : a = b := by
  have ha' := (translate_of_eq_some_of_iff.{u, v, w, t}
    a.representative_property.1 a.representative_property.2
    c.representative_property.1 c.representative_property.2).mp
      (by simpa only [of_representative] using ha)
  have hb' := (translate_of_eq_some_of_iff.{u, v, w, t}
    b.representative_property.1 b.representative_property.2
    c.representative_property.1 c.representative_property.2).mp
      (by simpa only [of_representative] using hb)
  obtain ⟨ea⟩ := ha'.2
  obtain ⟨eb⟩ := hb'.2
  have h := (nonempty_iso_arTranslate_iff.{u, v, w, t} k Q
    a.representative_property.1 b.representative_property.1
    a.representative_property.2 b.representative_property.2 ha'.1).mp ⟨ea ≪≫ eb.symm⟩
  simpa only [of_representative] using (of_eq_of_iff
    a.representative_property.1 a.representative_property.2
    b.representative_property.1 b.representative_property.2).mpr h

/-- Auslander–Reiten translation is injective on the non-projective vertices. -/
theorem translate_injective :
    Function.Injective (fun a :
      {a : irreducibleMorphismQuiver.{u, v, w, max u v w t} k Q //
        ¬ Projective a.representative} ↦ translate.{u, v, w, t} a.val) := by
  intro a b hab
  apply Subtype.ext
  cases ha : translate.{u, v, w, t} a.val with
  | none => exact False.elim (a.property ((translate_eq_none_iff a.val).mp ha))
  | some c => exact eq_of_translate_eq_some.{u, v, w, t} ha (hab.symm.trans ha)

end TauCeti.irreducibleMorphismQuiver

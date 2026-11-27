/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AbelianVariety.Isogeny
public import TauCeti.AlgebraicGeometry.GroupScheme.FaithfullyFlat
public import TauCeti.AlgebraicGeometry.GroupScheme.Isogeny.Basic
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.GeometricallyReduced

/-!
# Surjective homomorphisms of abelian varieties are faithfully flat

Every surjective homomorphism `f : A ⟶ B` of abelian varieties over a field `K` is faithfully
flat, with no hypothesis on the dimensions of `A` and `B`
(`TauCeti.AlgebraicGeometry.AbelianVariety.Hom.flat_of_surjective`). This is the case of group
schemes of finite type with geometrically reduced target,
`TauCeti.GroupScheme.flat_of_surjective`: an abelian variety is proper, hence of finite type and
quasi-compact, and smooth, hence geometrically reduced.

In particular an isogeny of abelian varieties, defined as a finite surjective homomorphism, is
flat (`TauCeti.AlgebraicGeometry.AbelianVariety.IsIsogeny.flat`). So over a field the definition
of `TauCeti.AlgebraicGeometry.AbelianVariety.IsIsogeny`, finite and surjective, agrees with the
definition `TauCeti.GroupScheme.IsIsogeny` of isogenies of group schemes over an arbitrary base,
finite, flat and surjective (`TauCeti.AlgebraicGeometry.AbelianVariety.isIsogeny_iff_isIsogeny`).

## Main results

In the namespace `TauCeti.AlgebraicGeometry.AbelianVariety`:

* `Hom.flat_of_surjective`: a surjective homomorphism of abelian varieties is flat.
* `Hom.faithfullyFlat_of_surjective`: it is flat and surjective.
* `IsIsogeny.flat`: an isogeny of abelian varieties is flat.
* `isIsogeny_iff_isIsogeny`: a homomorphism of abelian varieties is an isogeny exactly when the
  underlying homomorphism of group schemes over `Spec K` is a group-scheme isogeny.

## References

* G. Faltings and C.-L. Chai, *Degeneration of Abelian Varieties*, Ergebnisse der Mathematik (3)
  22, Springer, 1990, Chapter I, §1, p. 5, for isogenies of abelian schemes.
* The Stacks Project, Proposition 29.28.1 (Tag 052A), generic flatness.
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry.AbelianVariety

universe u

variable {K : Type u} [Field K] {A B : AbelianVariety K}

/-- The underlying scheme of an abelian variety is quasi-compact: it is proper over `Spec K`. -/
instance compactSpace_toScheme (A : AbelianVariety K) : CompactSpace A.toScheme :=
  QuasiCompact.compactSpace_of_compactSpace A.toOver.hom

/-- **Surjective homomorphisms of abelian varieties are flat.** -/
theorem Hom.flat_of_surjective (f : A ⟶ B) [Surjective (Hom.toSchemeHom f)] :
    Flat (Hom.toSchemeHom f) :=
  GroupScheme.flat_of_surjective (Hom.toOverHom f)

/-- **Surjective homomorphisms of abelian varieties are faithfully flat**: such a homomorphism is
flat and surjective. -/
theorem Hom.faithfullyFlat_of_surjective (f : A ⟶ B) [Surjective (Hom.toSchemeHom f)] :
    Flat (Hom.toSchemeHom f) ∧ Surjective (Hom.toSchemeHom f) :=
  ⟨Hom.flat_of_surjective f, ‹_›⟩

/-- An isogeny of abelian varieties is flat: it is a surjective homomorphism. -/
theorem IsIsogeny.flat {f : A ⟶ B} (hf : IsIsogeny f) : Flat (Hom.toSchemeHom f) :=
  have := hf.surjective
  Hom.flat_of_surjective f

/-- **Isogenies of abelian varieties are group-scheme isogenies.** A homomorphism of abelian
varieties is an isogeny, finite and surjective, exactly when the underlying homomorphism of group
schemes over `Spec K` is finite, flat and surjective. -/
theorem isIsogeny_iff_isIsogeny (f : A ⟶ B) :
    IsIsogeny f ↔ GroupScheme.IsIsogeny ((CommGrp.forget₂Grp _).map f.hom) := by
  rw [GroupScheme.isIsogeny_iff, isIsogeny_iff]
  change _ ↔ IsFinite (Hom.toSchemeHom f) ∧ Flat (Hom.toSchemeHom f) ∧
    Surjective (Hom.toSchemeHom f)
  exact ⟨fun ⟨h₁, h₂⟩ ↦ ⟨h₁, IsIsogeny.flat ((isIsogeny_iff f).mpr ⟨h₁, h₂⟩), h₂⟩,
    fun ⟨h₁, _, h₃⟩ ↦ ⟨h₁, h₃⟩⟩

end TauCeti.AlgebraicGeometry.AbelianVariety

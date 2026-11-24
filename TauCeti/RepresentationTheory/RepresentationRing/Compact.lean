/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Compact.Semisimple
public import TauCeti.RepresentationTheory.RepresentationRing.Continuous
public import TauCeti.RepresentationTheory.Semisimple

/-!
# The representation ring of a compact group is detected by characters

Let `G` be a compact group and `𝕜` be `ℝ` or `ℂ`. Every continuous finite-dimensional
representation of `G` over `𝕜` is semisimple
(`Representation.isSemisimpleRepresentation_of_continuous`), and semisimple representations in
characteristic zero are determined by their characters
(`Representation.nonempty_equiv_of_character_eq_of_isSemisimpleRepresentation`). So two virtual
representations in the representation ring `TauCeti.contRepRing 𝕜 G` with the same character are
equal: the character map `R(G) → (G → 𝕜)` is injective. This is how an identity in `R(G)`, such as
the equality of two equivariant indices, is reduced to an identity between traces.

For a finite group this is `TauCeti.repRingCharacter_injective`. For a compact group no
orthogonality relation or completeness theorem for characters is used; complete reducibility does
the work.

## Main results

* `TauCeti.repRingCharacter_contRepRingToRepRing_injective`: for a compact group over `ℝ` or `ℂ`,
  the character of a virtual continuous representation determines it.

## References

* G. Segal, *Equivariant K-theory*, Publ. Math. IHÉS 34 (1968), §2, for the representation ring
  of a compact group and its embedding into class functions by characters.
-/

public section

open CategoryTheory

namespace TauCeti

variable {𝕜 G : Type*} [RCLike 𝕜] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G]

/-- **Characters detect the representation ring of a compact group.** Over `ℝ` or `ℂ`, two virtual
continuous finite-dimensional representations of a compact group with the same character are
equal in the representation ring `TauCeti.contRepRing 𝕜 G`. -/
theorem repRingCharacter_contRepRingToRepRing_injective :
    Function.Injective fun x : contRepRing 𝕜 G ↦
      repRingCharacter 𝕜 G (contRepRingToRepRing 𝕜 G x) := by
  let f : contRepRing 𝕜 G →+ (G → 𝕜) :=
    (repRingCharacter 𝕜 G).toAddMonoidHom.comp (contRepRingToRepRing 𝕜 G).toAddMonoidHom
  refine (injective_iff_map_eq_zero f).mpr fun x hx ↦ ?_
  obtain ⟨X, Y, rfl⟩ := SplitK0.exists_eq_sub x
  have hchar : Representation.character X.obj.ρ = Representation.character Y.obj.ρ := by
    have h : X.obj.character = Y.obj.character := by simpa [f, sub_eq_zero] using hx
    ext g
    simpa using congrFun h g
  -- Both representations are semisimple, by Haar averaging, so equal characters make them
  -- isomorphic.
  have := Representation.isSemisimpleRepresentation_of_continuous _
    (FDRep.isContinuous_iff.mp X.property)
  have := Representation.isSemisimpleRepresentation_of_continuous _
    (FDRep.isContinuous_iff.mp Y.property)
  obtain ⟨e⟩ :=
    Representation.nonempty_equiv_of_character_eq_of_isSemisimpleRepresentation _ _ hchar
  obtain ⟨i⟩ := nonempty_fdRepIso_iff.mpr ⟨e⟩
  rw [sub_eq_zero]
  exact SplitK0.of_congr (ObjectProperty.isoMk _ i)

end TauCeti

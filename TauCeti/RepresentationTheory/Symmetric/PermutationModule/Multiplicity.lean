/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Young.Kostka
public import TauCeti.RepresentationTheory.Symmetric.Specht.Dominance
-- Non-public: neither appears in the type of an exported declaration.  The character of the Young
-- permutation module of the all-ones partition and the dimension of the Specht module are used
-- only inside the proof of `TauCeti.spechtMultiplicity_ones`.
import TauCeti.RepresentationTheory.Symmetric.PermutationModule.Extremes
import TauCeti.RepresentationTheory.Symmetric.Specht.StandardBasis

/-!
# Specht multiplicities in Young permutation modules

For a Young diagram `lam` and a partition `μ` of its number of cells, the multiplicity of the
Specht representation `S^lam` in the Young permutation module `M^μ` is the dimension of the
intertwiner space

`Hom_{Sₙ}(S^lam, M^μ)`.

This file defines that number as `TauCeti.spechtMultiplicity lam μ` and proves the unitriangular
part of Young's rule:

* it vanishes unless the shape of `lam` dominates `μ`;
* it is one when `μ` is the shape of `lam`.

These results describe the diagonal and the zero region of the Kostka multiplicity matrix.  In
particular, they supply the unitriangular part of the multiplicity statement in Young's rule.

It then proves Young's rule itself at one further partition, the all-ones `μ = (1ⁿ)`, where `M^μ`
is the regular representation `ℚ[Sₙ]`.  There the multiplicity is the dimension `f^lam` of
`S^lam`: the character of `M^{(1ⁿ)}` is `n !` at the identity and `0` elsewhere
(`TauCeti.char_permutationModule_ones`), so the character pairing that computes an intertwiner
dimension has a single surviving term.  Matching it against the combinatorial side,
`TauCeti.kostkaNumber_ones`, gives the Kostka number `K_{lam (1ⁿ)}`, so the last column of the two
matrices agrees as well.  The general identification of the two matrices — Young's rule proper —
is not proved here; it needs the semistandard-tableau filtration of `M^μ`.

## Main definitions

* `TauCeti.spechtMultiplicity`: the multiplicity of `S^lam` in `M^μ`.
* `TauCeti.spechtSelfMultiplicityEquiv`: the canonical equivalence
  `ℚ ≃ₗ[ℚ] Hom_{Sₙ}(S^lam, M^lam)` given by scalar multiples of the inclusion.

## Main results

* `TauCeti.spechtMultiplicity_eq_zero_of_not_dominates`: the multiplicity vanishes outside the
  dominance cone.
* `TauCeti.dominates_of_spechtMultiplicity_ne_zero`: a nonzero multiplicity forces dominance.
* `TauCeti.spechtMultiplicity_self`: the diagonal multiplicity is one.
* `TauCeti.spechtMultiplicity_ones`: the multiplicity of `S^lam` in the regular representation
  `M^{(1ⁿ)}` is `f^lam`, and `TauCeti.spechtMultiplicity_ones_eq_kostkaNumber` reads that as
  Young's rule at the all-ones partition.

## References

* [G. D. James, *The Representation Theory of the Symmetric Groups*][james1978], Chapters 4 and 13.
* B. E. Sagan, *The Symmetric Group*, 2nd ed. (2001), Section 2.11.
-/

public section

namespace TauCeti

open YoungTableau

variable {lam : YoungDiagram}

/-- **The multiplicity of `S^lam` in the Young permutation module `M^μ`**: the dimension of
the space of equivariant linear maps from the Specht representation of `lam` to `M^μ`.

Over `ℚ`, the group algebra of the symmetric group is semisimple and the rational Specht modules
are absolutely irreducible, so this intertwiner dimension is the number of copies of `S^lam` in
`M^μ`.  Young's rule identifies it with the Kostka number of the same two shapes. -/
noncomputable def spechtMultiplicity (lam : YoungDiagram) (μ : lam.card.Partition) : ℕ :=
  Module.finrank ℚ
    (Representation.IntertwiningMap (spechtSubrepresentation lam).toRepresentation
      (permutationModule μ).ρ)

/-- The Specht multiplicity is the dimension of the corresponding intertwiner space. -/
theorem spechtMultiplicity_def (lam : YoungDiagram) (μ : lam.card.Partition) :
    spechtMultiplicity lam μ = Module.finrank ℚ
      (Representation.IntertwiningMap (spechtSubrepresentation lam).toRepresentation
        (permutationModule μ).ρ) := (rfl)

/-- **The Specht multiplicity vanishes outside the dominance cone.**  This is the zero region of
the unitriangular multiplicity matrix in Young's rule. -/
@[simp]
theorem spechtMultiplicity_eq_zero_of_not_dominates (μ : lam.card.Partition)
    (h : ¬Dominates (shapePartition lam) μ) : spechtMultiplicity lam μ = 0 := by
  have : Subsingleton
      (Representation.IntertwiningMap (spechtSubrepresentation lam).toRepresentation
        (permutationModule μ).ρ) :=
    ⟨fun f g => sub_eq_zero.mp
      (intertwiningMap_eq_zero_of_not_dominates μ h (f - g))⟩
  exact Module.finrank_zero_of_subsingleton

/-- **A nonzero Specht multiplicity forces dominance.** -/
theorem dominates_of_spechtMultiplicity_ne_zero (μ : lam.card.Partition)
    (h : spechtMultiplicity lam μ ≠ 0) : Dominates (shapePartition lam) μ := by
  by_contra hdom
  exact h (spechtMultiplicity_eq_zero_of_not_dominates μ hdom)

/-! ### The diagonal intertwiner space -/

/-- Every intertwiner `S^lam → M^lam` is a scalar multiple of the canonical inclusion.  This
characterizes the diagonal intertwiner space and yields the diagonal case of Young's rule. -/
private theorem exists_intertwiningMap_eq_smul_subtype
    (f : Representation.IntertwiningMap (spechtSubrepresentation lam).toRepresentation
      (permutationModule (shapePartition lam)).ρ) :
    ∃ κ : ℚ, f = κ • (spechtSubrepresentation lam).subtype := by
  obtain ⟨t⟩ := YoungTableau.nonempty lam
  obtain ⟨v, hv, hbv⟩ :=
    exists_mem_asAlgebraHom_columnAntisymmetrizer_eq_polytabloid t
  let v' : (spechtSubrepresentation lam).toSubmodule := ⟨v, hv⟩
  let et : (spechtSubrepresentation lam).toSubmodule :=
    ⟨polytabloid t, polytabloid_mem_spechtSubrepresentation t⟩
  have hmap : f
      ((spechtSubrepresentation lam).toRepresentation.asAlgebraHom
        (columnAntisymmetrizer t) v') =
      (permutationModule (shapePartition lam)).ρ.asAlgebraHom
        (columnAntisymmetrizer t) (f v') :=
    (Representation.IntertwiningMap.equivLinearMapAsModule _ _ f).map_smul'
      (columnAntisymmetrizer t) v'
  have hbet :
      (spechtSubrepresentation lam).toRepresentation.asAlgebraHom
          (columnAntisymmetrizer t) v' = et := by
    apply Subtype.ext
    simpa only [v', et, Subrepresentation.coe_toRepresentation_asAlgebraHom_apply] using hbv
  obtain ⟨κ, hκ⟩ := exists_eq_smul_polytabloid t (f v')
  refine ⟨κ, ?_⟩
  have het : f et = κ • (et : (permutationModule (shapePartition lam)).V) := by
    rw [← hbet, hmap, hκ]
    simpa only [et] using congrArg
      (fun x : (spechtSubrepresentation lam).toSubmodule =>
        κ • (x : (permutationModule (shapePartition lam)).V)) hbet.symm
  have hspan : Submodule.span ℚ
      (Set.range fun σ : Equiv.Perm (Fin lam.card) =>
        (spechtSubrepresentation lam).toRepresentation σ et) = ⊤ := by
    apply Submodule.map_injective_of_injective
      (spechtSubrepresentation lam).toSubmodule.injective_subtype
    rw [Submodule.map_top, Submodule.range_subtype, Submodule.map_span]
    have himage : (spechtSubrepresentation lam).toSubmodule.subtype ''
        Set.range (fun σ : Equiv.Perm (Fin lam.card) =>
          (spechtSubrepresentation lam).toRepresentation σ et) =
        Set.range (fun σ : Equiv.Perm (Fin lam.card) =>
          (permutationModule (shapePartition lam)).ρ σ (polytabloid t)) := by
      ext x
      constructor
      · rintro ⟨y, ⟨σ, rfl⟩, rfl⟩
        exact ⟨σ, rfl⟩
      · rintro ⟨σ, rfl⟩
        exact ⟨_, ⟨σ, rfl⟩, rfl⟩
    rw [himage]
    exact (spechtSubrepresentation_eq_span_orbit t).symm
  apply Representation.IntertwiningMap.ext
  refine (Submodule.linearMap_eq_iff_of_span_eq_top _ _ hspan).2 ?_
  rintro ⟨_, ⟨σ, rfl⟩⟩
  have hf := Representation.IntertwiningMap.isIntertwining
    (spechtSubrepresentation lam).toRepresentation
    (permutationModule (shapePartition lam)).ρ f σ et
  rw [het] at hf
  simpa only [Representation.IntertwiningMap.toLinearMap_apply,
    Representation.IntertwiningMap.smul_apply, Subrepresentation.coe_subtype,
    Subrepresentation.toRepresentation_apply, LinearMap.restrict_apply, map_smul] using hf

/-- Scalar multiplication of the inclusion `S^lam ↪ M^lam`, as a linear map into the diagonal
intertwiner space. -/
private noncomputable def scalarToSpechtIntertwiningMap (lam : YoungDiagram) :
    ℚ →ₗ[ℚ] Representation.IntertwiningMap (spechtSubrepresentation lam).toRepresentation
      (permutationModule (shapePartition lam)).ρ where
  toFun κ := κ • (spechtSubrepresentation lam).subtype
  map_add' κ ν := by rw [add_smul]
  map_smul' κ ν := by rw [smul_eq_mul, mul_smul, RingHom.id_apply]

private theorem scalarToSpechtIntertwiningMap_injective (lam : YoungDiagram) :
    Function.Injective (scalarToSpechtIntertwiningMap lam) := by
  intro κ ν hκν
  obtain ⟨t⟩ := YoungTableau.nonempty lam
  let et : (spechtSubrepresentation lam).toSubmodule :=
    ⟨polytabloid t, polytabloid_mem_spechtSubrepresentation t⟩
  have happ : κ • (polytabloid t : (permutationModule (shapePartition lam)).V) =
      ν • (polytabloid t : (permutationModule (shapePartition lam)).V) := by
    simpa only [scalarToSpechtIntertwiningMap,
      LinearMap.coe_mk, AddHom.coe_mk, Representation.IntertwiningMap.smul_apply,
      Subrepresentation.coe_subtype, et] using
      DFunLike.congr_fun hκν et
  have hpoly : (polytabloid t : (permutationModule (shapePartition lam)).V) ≠ 0 :=
    polytabloid_ne_zero t
  have hsub : (κ - ν) • (polytabloid t : (permutationModule (shapePartition lam)).V) = 0 := by
    rw [sub_smul]
    exact sub_eq_zero.mpr happ
  exact sub_eq_zero.mp ((smul_eq_zero.mp hsub).resolve_right hpoly)

/-- **The diagonal intertwiner space is one-dimensional.**  The equivalence sends a scalar `κ`
to `κ` times the canonical inclusion `S^lam ↪ M^lam`. -/
noncomputable def spechtSelfMultiplicityEquiv (lam : YoungDiagram) :
    ℚ ≃ₗ[ℚ] Representation.IntertwiningMap (spechtSubrepresentation lam).toRepresentation
      (permutationModule (shapePartition lam)).ρ :=
  LinearEquiv.ofBijective (scalarToSpechtIntertwiningMap lam)
    ⟨scalarToSpechtIntertwiningMap_injective lam,
      fun f => by
        obtain ⟨κ, hκ⟩ := exists_intertwiningMap_eq_smul_subtype f
        exact ⟨κ, hκ.symm⟩⟩

/-- The diagonal equivalence sends `κ` to `κ` times the inclusion. -/
@[simp]
theorem spechtSelfMultiplicityEquiv_apply (lam : YoungDiagram) (κ : ℚ) :
    spechtSelfMultiplicityEquiv lam κ = κ • (spechtSubrepresentation lam).subtype := (rfl)

/-- **The diagonal Specht multiplicity is one.**  There is exactly one copy of `S^lam` in
`M^lam`: every equivariant map `S^lam → M^lam` is a scalar multiple of the inclusion. -/
@[simp]
theorem spechtMultiplicity_self (lam : YoungDiagram) :
    spechtMultiplicity lam (shapePartition lam) = 1 := by
  rw [spechtMultiplicity, ← (spechtSelfMultiplicityEquiv lam).finrank_eq]
  exact Module.finrank_self ℚ

/-! ### Young's rule at the all-ones partition -/

/-- **The multiplicity of `S^lam` in the regular representation is `f^lam`.**  The Young
permutation module of the all-ones partition is `ℚ[Sₙ]`, whose character is `n !` at the identity
and `0` elsewhere, so the character pairing that computes the intertwiner dimension collapses to
the single term `(n !)⁻¹ · n ! · dim S^lam`. -/
theorem spechtMultiplicity_ones (lam : YoungDiagram) :
    spechtMultiplicity lam (Nat.Partition.ones lam.card) = standardCount lam := by
  let _ : Invertible (Nat.card (Equiv.Perm (Fin lam.card)) : ℚ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have hcard : (Nat.card (Equiv.Perm (Fin lam.card)) : ℚ) = (lam.card.factorial : ℚ) := by
    rw [Nat.card_perm, Nat.card_fin]
  have hoff : ∀ g ∈ Finset.univ, g ≠ (1 : Equiv.Perm (Fin lam.card)) →
      (permutationModule (Nat.Partition.ones lam.card)).ρ.character g *
        (spechtSubrepresentation lam).toRepresentation.character g⁻¹ = 0 := by
    intro g _ hg
    rw [char_permutationModule_ones, ite_eq_right hg, zero_mul]
  have hsum : ∑ g : Equiv.Perm (Fin lam.card),
      (permutationModule (Nat.Partition.ones lam.card)).ρ.character g *
        (spechtSubrepresentation lam).toRepresentation.character g⁻¹ =
      (lam.card.factorial : ℚ) * (standardCount lam : ℚ) := by
    rw [Finset.sum_eq_single_of_mem (1 : Equiv.Perm (Fin lam.card)) (Finset.mem_univ _) hoff,
      char_permutationModule_ones, ite_eq_left rfl, inv_one, Representation.char_one]
    rw [finrank_spechtSubrepresentation]
  refine Nat.cast_injective (R := ℚ) ?_
  rw [spechtMultiplicity_def,
    ← Representation.card_inv_mul_sum_char_mul_char_eq_finrank
      (spechtSubrepresentation lam).toRepresentation
      (permutationModule (Nat.Partition.ones lam.card)).ρ,
    hsum, hcard, inv_mul_cancel_left₀ (Nat.cast_ne_zero.mpr lam.card.factorial_ne_zero)]

/-- **Young's rule at the all-ones partition**: the multiplicity of `S^lam` in the Young
permutation module `M^{(1ⁿ)}` is the Kostka number `K_{lam (1ⁿ)}`.

This is the last column of the multiplicity matrix, the one the regular representation
`M^{(1ⁿ)} = ℚ[Sₙ]` reads: both sides are `f^lam`, the dimension of `S^lam` on the representation
side (`TauCeti.spechtMultiplicity_ones`) and the number of standard Young tableaux of shape `lam`
on the combinatorial side (`TauCeti.kostkaNumber_ones`).  Together with the diagonal
`TauCeti.spechtMultiplicity_self` and `TauCeti.kostkaNumber_self`, and the common vanishing off the
dominance cone, it is one more agreement of the two matrices; the general statement is still
open. -/
theorem spechtMultiplicity_ones_eq_kostkaNumber (lam : YoungDiagram) :
    spechtMultiplicity lam (Nat.Partition.ones lam.card) =
      kostkaNumber (shapePartition lam) (Nat.Partition.ones lam.card) := by
  rw [spechtMultiplicity_ones, kostkaNumber_ones, diagramOf_shapePartition]

end TauCeti

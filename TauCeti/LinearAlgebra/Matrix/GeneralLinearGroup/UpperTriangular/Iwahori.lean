/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `IsLocalRing.residue` and `IsLocalRing.ker_residue`.
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
-- `TauCeti.GL2Borel.index_eq` computes the index of the Borel subgroup of `GL₂(𝔽_q)`.
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Borel
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UpperTriangular.Congruence

/-!
# Iwahori subgroups of `GL_m` over a local ring

For a commutative local ring `R` with maximal ideal `𝔪` and residue field `k`, the **Iwahori
subgroup** `Iw ⊆ GL_m(R)` consists of the invertible matrices that are upper triangular modulo `𝔪`,
and the **pro-`p` Iwahori subgroup** `Iw₁ ⊆ Iw` of those that are upper unitriangular modulo `𝔪`.
When `R` is the valuation ring of a nonarchimedean local field, these are the Iwahori and pro-`p`
Iwahori subgroups of `GL_m(R)`, the local factors of the Iwahori-type levels of automorphic forms
and of locally symmetric spaces.

They are the upper-triangular and upper-unitriangular congruence subgroups modulo `𝔪`, so they
inherit the API of `TauCeti.upperTriangularCongruenceSubgroup`. Since `𝔪` is the Jacobson radical,
reduction to `GL_m(k)` is surjective, and this file computes in terms of the residue field:

* `Iw` and `Iw₁` are the preimages of the upper-triangular and upper-unitriangular subgroups of
  `GL_m(k)` under the residue map;
* `[GL_m(R) : Iw]` is the index of the upper-triangular subgroup of `GL_m(k)`, the number of
  complete flags in `k^m`; for `m = 2` and `#k = q` it is `q + 1`;
* the diagonal modulo `𝔪` identifies `Iw ⧸ Iw₁` with `m → kˣ`, so `[Iw : Iw₁] = (q - 1) ^ #m`.

## Main declarations

* `TauCeti.iwahori`, `TauCeti.iwahoriOne`: the subgroups `Iw` and `Iw₁` of `GL_m(R)`.
* `TauCeti.comap_generalLinearGroupMap_residue_upperTriangularGroup`: `Iw` is the preimage of
  the upper-triangular subgroup of `GL_m(k)`.
* `TauCeti.index_iwahori`: `[GL_m(R) : Iw]` is the index of the upper-triangular subgroup of
  `GL_m(k)`.
* `TauCeti.index_iwahori_fin_two`: `[GL₂(R) : Iw] = q + 1`.
* `TauCeti.iwahoriQuotientEquiv`: `Iw ⧸ Iw₁ ≃* (m → kˣ)`.
* `TauCeti.relIndex_iwahoriOne_iwahori`: `[Iw : Iw₁] = (q - 1) ^ #m`.

## Implementation notes

Mathlib defines `IsLocalRing.ResidueField R` as `R ⧸ maximalIdeal R`, with `IsLocalRing.residue R`
the quotient map (`IsLocalRing.residue_def`). The results for the general congruence subgroups
modulo `maximalIdeal R` are stated over `R ⧸ maximalIdeal R`; this file restates them over
`ResidueField R` through this definitional identification, where the residue field structure
(`Field`, `Finite`) lives.

## References

* F. Calegari and D. Geraghty, *Modularity lifting beyond the Taylor–Wiles method*, Invent. Math.
  211 (2018), §5.2.1.
* N. Iwahori and H. Matsumoto, *On some Bruhat decomposition and the structure of the Hecke rings
  of p-adic Chevalley groups*, Publ. Math. IHÉS 25 (1965).
-/

public section

namespace TauCeti

open Matrix IsLocalRing UpperTriangularCongruenceSubgroup

variable (m : Type*) [Fintype m] [LinearOrder m] (R : Type*) [CommRing R] [IsLocalRing R]

/-- The **Iwahori subgroup** of `GL_m(R)` for a local ring `R`: the invertible matrices that are
upper triangular modulo the maximal ideal. -/
abbrev iwahori : Subgroup (GL m R) :=
  upperTriangularCongruenceSubgroup m (maximalIdeal R)

/-- The **pro-`p` Iwahori subgroup** of `GL_m(R)` for a local ring `R`: the invertible matrices
that are upper unitriangular modulo the maximal ideal. -/
abbrev iwahoriOne : Subgroup (GL m R) :=
  upperUnitriangularCongruenceSubgroup m (maximalIdeal R)

variable {m R}

/-- The pro-`p` Iwahori subgroup lies in the Iwahori subgroup. -/
theorem iwahoriOne_le_iwahori : iwahoriOne m R ≤ iwahori m R :=
  upperUnitriangularCongruenceSubgroup_le_upperTriangularCongruenceSubgroup

/-- The Iwahori subgroup is the preimage of the upper-triangular subgroup of `GL_m` of the residue
field. -/
theorem comap_generalLinearGroupMap_residue_upperTriangularGroup :
    (upperTriangularGroup m (ResidueField R)).comap (GeneralLinearGroup.map (residue R)) =
      iwahori m R := by
  rw [comap_generalLinearGroupMap_upperTriangularGroup, ker_residue]

/-- The pro-`p` Iwahori subgroup is the preimage of the upper-unitriangular subgroup of `GL_m` of
the residue field. -/
theorem comap_generalLinearGroupMap_residue_upperUnitriangularGroup :
    (upperUnitriangularGroup m (ResidueField R)).comap (GeneralLinearGroup.map (residue R)) =
      iwahoriOne m R := by
  rw [comap_generalLinearGroupMap_upperUnitriangularGroup, ker_residue]

/-- The index of the Iwahori subgroup in `GL_m(R)` is the index of the upper-triangular subgroup
in `GL_m` of the residue field. -/
theorem index_iwahori :
    (iwahori m R).index = (upperTriangularGroup m (ResidueField R)).index :=
  -- `ResidueField R` is `R ⧸ maximalIdeal R` by definition.
  index_upperTriangularCongruenceSubgroup (ringJacobson_eq_maximalIdeal R).ge

/-- The index of the pro-`p` Iwahori subgroup in `GL_m(R)` is the index of the
upper-unitriangular subgroup in `GL_m` of the residue field. -/
theorem index_iwahoriOne :
    (iwahoriOne m R).index = (upperUnitriangularGroup m (ResidueField R)).index :=
  -- `ResidueField R` is `R ⧸ maximalIdeal R` by definition.
  index_upperUnitriangularCongruenceSubgroup (ringJacobson_eq_maximalIdeal R).ge

/-- For a finite residue field with `q` elements, the Iwahori subgroup of `GL₂(R)` has index
`q + 1`, the number of points of the projective line over the residue field. -/
theorem index_iwahori_fin_two [Finite (ResidueField R)] :
    (iwahori (Fin 2) R).index = Nat.card (ResidueField R) + 1 := by
  have := Fintype.ofFinite (ResidueField R)
  rw [index_iwahori, GL2Borel.index_eq, Nat.card_eq_fintype_card]

variable (m R) in
/-- The diagonal modulo the maximal ideal identifies the quotient of the Iwahori subgroup by the
pro-`p` Iwahori subgroup with `m → kˣ`, for the residue field `k`. -/
noncomputable def iwahoriQuotientEquiv :
    iwahori m R ⧸ (iwahoriOne m R).subgroupOf (iwahori m R) ≃* (m → (ResidueField R)ˣ) :=
  -- `ResidueField R` is `R ⧸ maximalIdeal R` by definition.
  quotientEquiv (ringJacobson_eq_maximalIdeal R).ge

/-- The identification of the Iwahori quotient sends a class to the diagonal entries of a
representative, reduced to the residue field. -/
@[simp]
theorem iwahoriQuotientEquiv_mk_apply_val (g : iwahori m R) (i : m) :
    ((iwahoriQuotientEquiv m R
        (g : iwahori m R ⧸ (iwahoriOne m R).subgroupOf (iwahori m R)) i : (ResidueField R)ˣ) :
      ResidueField R) = residue R (((g : GL m R) : Matrix m m R) i i) := by
  -- `iwahoriQuotientEquiv` is `quotientEquiv` with its codomain restated over `ResidueField R`,
  -- which is `R ⧸ maximalIdeal R` by definition; `change` states the goal over the quotient.
  change ((quotientEquiv _ (g : iwahori m R ⧸ _) i : (R ⧸ maximalIdeal R)ˣ) : R ⧸ maximalIdeal R) =
    residue R _
  rw [quotientEquiv_mk, diag_apply_val, residue_def]

/-- The index of the pro-`p` Iwahori subgroup in the Iwahori subgroup is `(q - 1) ^ #m`, where `q`
is the cardinality of the residue field. -/
theorem relIndex_iwahoriOne_iwahori :
    (iwahoriOne m R).relIndex (iwahori m R) = (Nat.card (ResidueField R) - 1) ^ Fintype.card m := by
  rw [← Nat.card_units]
  -- `(ResidueField R)ˣ` is `(R ⧸ maximalIdeal R)ˣ`, as `ResidueField R` is `R ⧸ maximalIdeal R`
  -- by definition.
  exact relIndex_upperUnitriangularCongruenceSubgroup_upperTriangularCongruenceSubgroup
    (ringJacobson_eq_maximalIdeal R).ge

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.UnitFiltration.Basic
public import TauCeti.RingTheory.DiscreteValuationRing.UnitFiltration

/-!
# Uniformizer coordinates on unit-filtration graded pieces

Fixing a uniformizer `π` identifies the `m`th positive graded piece of the unit filtration
with the additive residue field: the class of `u` has coordinate `(u - 1) / π ^ m` modulo the
maximal ideal. This file transports the general discrete-valuation-ring construction
`TauCeti.IsDiscreteValuationRing.unitFiltrationGradedSuccEquivResidueField` to the ambient-field
unit filtration `TauCeti.unitFiltration` via `TauCeti.unitFiltrationGradedEquivInteger`.

If `π' = π * a` for a unit `a` of the integer ring, then the coordinate relative to `π` is
`a ^ m` times the coordinate relative to `π'`. Thus the identification is independent of the
uniformizer up to the additive automorphism of the residue field induced by multiplication by
the residue of `a ^ m`.

## Main results

* `TauCeti.unitFiltrationGradedSuccEquivResidueFieldOfUniformizer`: the residue coordinate
  determined by a uniformizer.
* `TauCeti.unitFiltrationGradedSuccEquivResidueFieldOfUniformizer_ofMul_mk_eq_residue`: its value
  on a representative whose difference from one is given explicitly.
* `TauCeti.unitFiltrationGradedSuccEquivResidueFieldOfUniformizer_change`: changing the
  uniformizer scales the coordinate by the corresponding residue-field unit.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §2.
* J. Neukirch, *Algebraic Number Theory*, Chapter II, §5.
-/

public section
noncomputable section

open ValuativeRel IsNonarchimedeanLocalField

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The positive-depth unit-filtration coordinate associated to a uniformizer. The class of
`u ∈ U(K,n+1)` is sent to the residue of `(u - 1) / π^(n+1)`. -/
noncomputable def unitFiltrationGradedSuccEquivResidueFieldOfUniformizer (n : ℕ)
    (π : 𝒪[K]) (hπ : Irreducible π) : Additive (UnitFiltrationGraded K (n + 1)) ≃+ 𝓀[K] :=
  (unitFiltrationGradedEquivInteger (K := K) (n + 1)).toAdditive.trans <|
    TauCeti.IsDiscreteValuationRing.unitFiltrationGradedSuccEquivResidueField n π hπ

/-- The uniformizer coordinate of the class of `u` is characterized by multiplying it by
`π^(n+1)`: the result is the class of `u - 1` in the maximal-ideal graded piece. -/
@[simp]
theorem unitFiltrationGradedSuccEquivResidueFieldOfUniformizer_ofMul_mk (n : ℕ)
    (π : 𝒪[K]) (hπ : Irreducible π) (x : unitFiltration K (n + 1)) :
    residueFieldEquivMaximalIdealGradedOfUniformizer π hπ (n + 1)
        (unitFiltrationGradedSuccEquivResidueFieldOfUniformizer (K := K) n π hπ
          (Additive.ofMul (QuotientGroup.mk x))) =
      Submodule.Quotient.mk
        ⟨((unitFiltrationEquivInteger (n + 1) x : 𝒪[K]ˣ) : 𝒪[K]) - 1,
          TauCeti.IsLocalRing.mem_unitFiltration_iff.mp
            (unitFiltrationEquivInteger (n + 1) x).property⟩ := by
  simp [unitFiltrationGradedSuccEquivResidueFieldOfUniformizer]

/-- If `u - 1 = y * π^(n+1)`, then the uniformizer coordinate of the class of `u` is the
residue of `y`. This is the representative form of the positive-depth graded equivalence used in
ramification computations. -/
theorem unitFiltrationGradedSuccEquivResidueFieldOfUniformizer_ofMul_mk_eq_residue
    (n : ℕ) (π : 𝒪[K]) (hπ : Irreducible π) (x : unitFiltration K (n + 1)) (y : 𝒪[K])
    (hxy : (unitFiltrationToIntegerUnits (n + 1) x : 𝒪[K]) - 1 = y * π ^ (n + 1)) :
    unitFiltrationGradedSuccEquivResidueFieldOfUniformizer (K := K) n π hπ
        (Additive.ofMul (QuotientGroup.mk x)) =
      IsLocalRing.residue 𝒪[K] y := by
  simpa [unitFiltrationGradedSuccEquivResidueFieldOfUniformizer] using
    TauCeti.IsDiscreteValuationRing.unitFiltrationGradedSuccEquivResidueField_eq_residue
      n π hπ (unitFiltrationEquivInteger (n + 1) x) y (by simpa using hxy)

/-- Coordinates attached to `π` and `π'` differ by multiplication by the residue of the
`(n+1)`st power of the unit carrying `π` to `π'`. -/
theorem unitFiltrationGradedSuccEquivResidueFieldOfUniformizer_change (n : ℕ)
    (π π' : 𝒪[K]) (hπ : Irreducible π) (hπ' : Irreducible π')
    (x : Additive (UnitFiltrationGraded K (n + 1))) :
    unitFiltrationGradedSuccEquivResidueFieldOfUniformizer (K := K) n π hπ x =
      IsLocalRing.residue 𝒪[K] (uniformizerChangeUnit π π' hπ hπ' : 𝒪[K]) ^ (n + 1) *
        unitFiltrationGradedSuccEquivResidueFieldOfUniformizer (K := K) n π' hπ' x :=
  TauCeti.IsDiscreteValuationRing.unitFiltrationGradedSuccEquivResidueField_change
    n π π' hπ hπ' _

end TauCeti

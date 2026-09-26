/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.UnitFiltration.Graded
public import TauCeti.RingTheory.DiscreteValuationRing.Uniformizer

/-!
# Uniformizer coordinates on unit-filtration graded pieces

Fixing a uniformizer `π` identifies the `m`th positive graded piece of the unit filtration
with the additive residue field: the class of `u` has coordinate `(u - 1) / π ^ m` modulo the
maximal ideal.  This file constructs that coordinate by composing the unit-filtration graded
equivalence with the discrete-valuation-ring identification
`TauCeti.residueFieldEquivMaximalIdealGradedOfUniformizer`, and computes how it changes when
the uniformizer is replaced.

If `π' = π * a` for a unit `a` of the integer ring, then the coordinate relative to `π` is
`a ^ m` times the coordinate relative to `π'`.  Thus the identification is independent of the
uniformizer up to the additive automorphism of the residue field induced by multiplication by
the residue of `a ^ m`.

## Main results

* `TauCeti.unitFiltrationGradedSuccEquivResidueFieldOfUniformizer`: the residue coordinate
  determined by a uniformizer.
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

/-- The positive-depth unit-filtration coordinate associated to a uniformizer.  The class of
`u ∈ U(K,n+1)` is sent to the residue of `(u - 1) / π^(n+1)`. -/
noncomputable def unitFiltrationGradedSuccEquivResidueFieldOfUniformizer (n : ℕ)
    (π : 𝒪[K]) (hπ : Irreducible π) : Additive (UnitFiltrationGraded K (n + 1)) ≃+ 𝓀[K] :=
  (unitFiltrationGradedSuccEquivMaximalIdealGraded (K := K) n).toAdditive.trans <|
    (AddEquiv.additiveMultiplicative (MaximalIdealGraded K (n + 1))).trans <|
      (residueFieldEquivMaximalIdealGradedOfUniformizer π hπ (n + 1)).symm.toAddEquiv

/-- The uniformizer coordinate of the class of `u` is characterized by multiplying it by
`π^(n+1)`: the result is the class of `u - 1` in the maximal-ideal graded piece. -/
@[simp]
theorem unitFiltrationGradedSuccEquivResidueFieldOfUniformizer_ofMul_mk (n : ℕ)
    (π : 𝒪[K]) (hπ : Irreducible π) (x : unitFiltration K (n + 1)) :
    residueFieldEquivMaximalIdealGradedOfUniformizer π hπ (n + 1)
        (unitFiltrationGradedSuccEquivResidueFieldOfUniformizer (K := K) n π hπ
          (Additive.ofMul (QuotientGroup.mk x))) =
      Submodule.Quotient.mk (unitFiltrationDifference n x) := by
  rw [unitFiltrationGradedSuccEquivResidueFieldOfUniformizer]
  simp only [AddEquiv.trans_apply, MulEquiv.toAdditive_apply_apply, toMul_ofMul,
    unitFiltrationGradedSuccEquivMaximalIdealGraded_mk]
  exact LinearEquiv.apply_symm_apply _ _

/-- Coordinates attached to `π` and `π'` differ by multiplication by the residue of the
`(n+1)`st power of the unit carrying `π` to `π'`. -/
theorem unitFiltrationGradedSuccEquivResidueFieldOfUniformizer_change (n : ℕ)
    (π π' : 𝒪[K]) (hπ : Irreducible π) (hπ' : Irreducible π')
    (x : Additive (UnitFiltrationGraded K (n + 1))) :
    unitFiltrationGradedSuccEquivResidueFieldOfUniformizer (K := K) n π hπ x =
      uniformizerChangeResidueAddEquiv π π' hπ hπ' (n + 1)
        (unitFiltrationGradedSuccEquivResidueFieldOfUniformizer (K := K) n π' hπ' x) := by
  exact residueFieldEquivMaximalIdealGradedOfUniformizer_symm_change π π' hπ hπ'
    (n + 1) _

end TauCeti

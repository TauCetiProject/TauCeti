/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.LocalField
public import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.Unramified
public import TauCeti.NumberTheory.LocalField.Unramified.Existence
import TauCeti.AlgebraicGeometry.EllipticCurve.LocalPolynomial
import TauCeti.NumberTheory.LocalField.Unramified.Reduction
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.GroupTheory.Perm.Cycle.Type
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FinitePoint

/-!
# Unramified torsion at multiplicative reduction

A curve with multiplicative reduction acquires nonsingular torsion of every prime order different
from the residue characteristic over a finite unramified extension. Reduction lifts this torsion
from the multiplicative group of a split node. This supplies points on which Frobenius detects
whether multiplicative reduction is split.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.2.5 and VII.2–3.
-/

public section

open ValuativeRel IsLocalRing Polynomial

namespace WeierstrassCurve.Affine.Point

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] {W : WeierstrassCurve K} [W.IsElliptic]

variable [DecidableEq K] in
/-- At split multiplicative reduction, every prime dividing the order of the multiplicative
residue group occurs as the order of a point with nonsingular reduction. -/
theorem exists_addOrderOf_eq_of_hasSplitMultiplicativeReduction
    (h : W.HasSplitMultiplicativeReduction 𝒪[K]) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hdvd : ℓ ∣ Nat.card 𝓀[K] - 1) :
    ∃ P : W.toAffine.Point, P ∈ W.toAffine.nonsingularReduction (valuation K) ∧
      addOrderOf P = ℓ := by
  classical
  have := h.toIsMinimal
  let _ := Fintype.ofFinite 𝓀[K]
  have := Fact.mk hℓ
  let V := W.reduction 𝒪[K]
  have hΔ : V.Δ = 0 := (reduction_Δ_eq_zero_iff 𝒪[K]).mpr (h.not_hasGoodReduction 𝒪[K])
  obtain ⟨x, y, hxy⟩ := Affine.exists_isSingular_of_Δ_eq_zero V.toAffine hΔ
  have hcard : Nat.card V.toAffine.Point = Nat.card 𝓀[K] - 1 := by
    have htr := h.frobeniusTrace_reduction_eq_one 𝒪[K]
    rw [frobeniusTrace_def, pointCount_eq_card_point_add_one_of_isSingular _ hxy] at htr
    omega
  obtain ⟨Q, hQ⟩ := exists_prime_addOrderOf_dvd_card' ℓ (hcard ▸ hdvd)
  have hn : (ℓ : 𝓀[K]) ≠ 0 := by
    intro hn
    obtain ⟨m, hm⟩ := hdvd
    have he : ((Nat.card 𝓀[K] - 1 : ℕ) : 𝓀[K]) = -1 := by
      rw [Nat.cast_sub Nat.card_pos, Nat.card_eq_fintype_card, Nat.cast_card_eq_zero]
      simp
    rw [hm, Nat.cast_mul, hn, zero_mul] at he
    exact neg_ne_zero.mpr one_ne_zero he.symm
  obtain ⟨P, ⟨hP, hred⟩, -⟩ :=
    W.toAffine.existsUnique_nonsingularReduction_torsion_lift_of_localField hn Q
      (hQ ▸ addOrderOf_nsmul_eq_zero Q)
  refine ⟨P, P.2, ?_⟩
  have hPn : ℓ • (P : W.toAffine.Point) = 0 := congrArg Subtype.val hP
  apply Nat.dvd_antisymm (addOrderOf_dvd_of_nsmul_eq_zero hPn)
  rw [← hQ, ← hred]
  exact (addOrderOf_map_dvd (W.toAffine.nonsingularReductionHom (valuation K)) P).trans
    (by simp)

open Classical in
/-- A curve with multiplicative reduction has a point of every prime order different from the
residue characteristic, with nonsingular reduction, over some finite unramified extension.
The extension is taken inside any specified separably closed extension of the local field. -/
theorem exists_addOrderOf_eq_unramifiedExtension
    (h : W.HasMultiplicativeReduction 𝒪[K]) {ℓ : ℕ} (hℓ : ℓ.Prime) (hn : (ℓ : 𝓀[K]) ≠ 0)
    (Ω : Type*) [Field Ω] [Algebra K Ω] [IsSepClosed Ω] :
    ∃ f : ℕ+,
      let L := TauCeti.unramifiedExtension K Ω f
      letI := TauCeti.finiteIntermediateFieldValuativeRel K Ω L
      letI := TauCeti.finiteIntermediateFieldTopology K Ω L
      letI := TauCeti.finiteIntermediateField_isNonarchimedeanLocalField K Ω L
      letI := TauCeti.finiteIntermediateField_valuativeExtension K Ω L
      ∃ P : (W⁄L).toAffine.Point,
        P ∈ (W⁄L).toAffine.nonsingularReduction (valuation L) ∧ addOrderOf P = ℓ := by
  classical
  have := h.toIsMinimal
  let V := W.reduction 𝒪[K]
  -- Split the node and adjoin the desired roots of unity in a finite residue extension.
  have hp₀ : V.nodePolynomial ≠ 0 := by
    intro he
    have hc := congrArg (fun p : 𝓀[K][X] ↦ p.coeff 2) he
    exact h.reduction_c₄_ne_zero 𝒪[K] (by simpa [nodePolynomial_def] using hc)
  let p := V.nodePolynomial * cyclotomic ℓ 𝓀[K]
  let k := p.SplittingField
  let _ : Algebra 𝓀[K] k := SplittingField.instAlgebra_1 p
  have : NeZero (ℓ : k) := ⟨by
    rw [← map_natCast (algebraMap 𝓀[K] k)]
    simpa only [_root_.map_zero] using (algebraMap 𝓀[K] k).injective.ne hn⟩
  have hp : p ≠ 0 := mul_ne_zero hp₀ (cyclotomic_ne_zero ℓ 𝓀[K])
  have hpmap : p.map (algebraMap 𝓀[K] k) ≠ 0 := Polynomial.map_ne_zero hp
  have hsplit : (V.nodePolynomial.map (algebraMap 𝓀[K] k)).Splits :=
    (SplittingField.splits p).of_dvd hpmap (Polynomial.map_dvd _ (dvd_mul_right _ _))
  have hcyc : (cyclotomic ℓ k).Splits := by
    rw [← map_cyclotomic ℓ (algebraMap 𝓀[K] k)]
    exact (SplittingField.splits p).of_dvd hpmap
      (Polynomial.map_dvd _ (dvd_mul_left _ _))
  obtain ⟨ζ, hζ⟩ := hcyc.exists_eval_eq_zero (degree_cyclotomic_pos ℓ k hℓ.pos).ne'
  have hζ : IsPrimitiveRoot ζ ℓ := isRoot_cyclotomic_iff.mp hζ
  have hdvd : ℓ ∣ Nat.card k - 1 := by
    have hzunit := hζ.isUnit hℓ.ne_zero
    have hzorder : orderOf hzunit.unit = ℓ := by
      rw [← orderOf_units, hzunit.unit_spec]
      exact hζ.eq_orderOf.symm
    have hzdiv := orderOf_dvd_natCard hzunit.unit
    rw [hzorder, Nat.card_units] at hzdiv
    exact hzdiv
  -- Realize this finite residue extension as the residue field of an unramified extension.
  let f : ℕ+ := ⟨Module.finrank 𝓀[K] k, Module.finrank_pos⟩
  let L := TauCeti.unramifiedExtension K Ω f
  let _ := TauCeti.finiteIntermediateFieldValuativeRel K Ω L
  let _ := TauCeti.finiteIntermediateFieldTopology K Ω L
  have _ := TauCeti.finiteIntermediateField_isNonarchimedeanLocalField K Ω L
  have _ := TauCeti.finiteIntermediateField_valuativeExtension K Ω L
  have _ : TauCeti.IsUnramified K L := TauCeti.isUnramified_unramifiedExtension
  obtain ⟨e⟩ : Nonempty (𝓀[L] ≃ₐ[𝓀[K]] k) :=
    TauCeti.nonempty_residueFieldAlgEquiv_unramifiedExtension K Ω k
  have hred : (W⁄L).reduction 𝒪[L] = V.baseChange 𝓀[L] :=
    W.reduction_baseChange 𝒪[K] 𝒪[L] TauCeti.algebraMap_comp_algebraMap_integerRing
  have hmult : (W⁄L).HasMultiplicativeReduction 𝒪[L] :=
    (W.hasMultiplicativeReduction_baseChange_iff 𝒪[K] 𝒪[L]
      TauCeti.algebraMap_comp_algebraMap_integerRing).mpr h
  have hs : (W⁄L).HasSplitMultiplicativeReduction 𝒪[L] := by
    apply (hmult.splits_nodePolynomial_reduction_iff 𝒪[L]).mp
    rw [hred, WeierstrassCurve.baseChange, map_nodePolynomial]
    have he : e.symm.toRingHom.comp (algebraMap 𝓀[K] k) = algebraMap 𝓀[K] 𝓀[L] := by
      ext x
      exact e.symm.commutes x
    rw [← he, ← Polynomial.map_map]
    exact hsplit.map e.symm.toRingHom
  refine ⟨f, ?_⟩
  apply exists_addOrderOf_eq_of_hasSplitMultiplicativeReduction hs hℓ
  rwa [Nat.card_congr e.toEquiv]

end WeierstrassCurve.Affine.Point

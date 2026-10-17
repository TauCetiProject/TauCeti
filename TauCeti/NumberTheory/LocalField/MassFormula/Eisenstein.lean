/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.MassFormula.Basic
public import TauCeti.NumberTheory.LocalField.Eisenstein.TotallyRamified
import TauCeti.NumberTheory.LocalField.Monogenic
import TauCeti.FieldTheory.IntermediateField.Adjoin.EqTop
import TauCeti.FieldTheory.IntermediateField.Adjoin.Defs
import Mathlib.RingTheory.Valuation.ValuationRing
import TauCeti.RingTheory.Polynomial.Eisenstein.Minpoly

/-!
# Eisenstein generators of the counted extensions

The totally ramified degree-`n` subextensions of a separable closure are precisely the fields
obtained by adjoining a root of a monic Eisenstein polynomial of degree `n`. The root is taken
in the separable closure, so inseparable Eisenstein polynomials contribute no extensions.

These characterizations connect coefficient-space root counts with the family
`totallyRamifiedOfDegree`. They also show that the family is preserved under embeddings into
the separable closure, as needed when regrouping extensions by isomorphism class.

The proofs transport the local-field Eisenstein-generator theorems through the canonical
finite-intermediate-field structures; no valuation or topology on the separable closure is needed.

## References

* J.-P. Serre, *Local Fields*, Chapter I, §6, Proposition 17.
* J.-P. Serre, *Une « formule de masse » pour les extensions totalement ramifiées de degré donné
  d'un corps local*, C. R. Acad. Sci. Paris Sér. A **286** (1978), 1031–1036, §2.
-/

public section
noncomputable section

open ValuativeRel Polynomial
open scoped IntermediateField

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- Every counted extension has a monic Eisenstein generator of the prescribed degree,
viewed as an element of the ambient separable closure. -/
theorem exists_eisenstein_generator_of_mem_totallyRamifiedOfDegree {n : ℕ}
    {L : IntermediateField K (SeparableClosure K)} (hL : L ∈ totallyRamifiedOfDegree K n) :
    ∃ (f : 𝒪[K][X]) (x : SeparableClosure K), f.Monic ∧ f.IsEisensteinAt 𝓂[K] ∧
      f.natDegree = n ∧ aeval x (f.map (algebraMap 𝒪[K] K)) = 0 ∧ K⟮x⟯ = L := by
  rw [mem_totallyRamifiedOfDegree_iff] at hL
  have := hL.2.finite
  let _ := finiteIntermediateFieldValuativeRel K (SeparableClosure K) L
  let _ := finiteIntermediateFieldTopology K (SeparableClosure K) L
  have := finiteIntermediateField_isNonarchimedeanLocalField K (SeparableClosure K) L
  have := finiteIntermediateField_valuativeExtension K (SeparableClosure K) L
  -- Fix the integer-ring algebra explicitly to avoid searching through the ambient closure.
  let : Algebra 𝒪[L] L := Algebra.ofSubsemiring (R := L) (A := L) 𝒪[L]
  have : IsScalarTower 𝒪[K] 𝒪[L] L := .of_algebraMap_eq' rfl
  have htr := (IntermediateField.isTotallyRamified_iff L).1 hL.2
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[L]
  have hint : IsIntegral 𝒪[K] π := IsIntegral.of_finite 𝒪[K] π
  have hgen : K⟮(π : L)⟯ = ⊤ := by
    simpa only [Algebra.algebraMap_ofSubsemiring_apply] using
      IntermediateField.adjoin_eq_top_of_algebra_adjoin_eq_top
        (R := 𝒪[K]) (S := 𝒪[L]) (K := K) (L := L)
        (htr.adjoin_eq_top_of_irreducible hπ)
  refine ⟨minpoly 𝒪[K] π, L.val π.val, minpoly.monic hint,
    htr.isEisensteinAt_minpoly hπ, ?_, ?_, ?_⟩
  · simpa only [htr.integralPowerBasis_gen, htr.integralPowerBasis_dim,
      (isTotallyRamified_iff_ramificationIndex_eq_finrank K L).1 htr, hL.1] using
        (htr.integralPowerBasis hπ).natDegree_minpoly
  · have hroot : aeval π.val (minpoly 𝒪[K] π) = 0 := by
      calc
        _ = (IsScalarTower.toAlgHom 𝒪[K] 𝒪[L] L) (aeval π (minpoly 𝒪[K] π)) :=
          aeval_algHom_apply (R := 𝒪[K]) (A := 𝒪[L]) (B := L)
            (IsScalarTower.toAlgHom 𝒪[K] 𝒪[L] L) π _
        _ = 0 := by rw [minpoly.aeval, map_zero]
    have hrootK : aeval π.val ((minpoly 𝒪[K] π).map (algebraMap 𝒪[K] K)) = 0 := by
      rw [← aeval_eq_aeval_map (IsScalarTower.algebraMap_eq 𝒪[K] K L).symm]
      exact hroot
    exact (aeval_algHom_apply L.val π.val _).trans (by rw [hrootK, map_zero])
  · simpa only [IntermediateField.adjoin_map, Set.image_singleton,
      ← AlgHom.fieldRange_eq_map, IntermediateField.fieldRange_val] using
      congrArg (fun E : IntermediateField K L ↦ E.map L.val) hgen

/-- A root in the separable closure of an Eisenstein polynomial generates a counted
extension, whose degree is the degree of the polynomial. Monicity is not required. -/
theorem adjoin_mem_totallyRamifiedOfDegree_of_eisenstein {n : ℕ} (hn : 0 < n)
    {f : 𝒪[K][X]} (hf : f.IsEisensteinAt 𝓂[K])
    (hdeg : f.natDegree = n) {x : SeparableClosure K}
    (hx : aeval x (f.map (algebraMap 𝒪[K] K)) = 0) :
    K⟮x⟯ ∈ totallyRamifiedOfDegree K n := by
  let L := K⟮x⟯
  have : Module.Finite K L := IntermediateField.adjoin.finiteDimensional
    (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  let _ := finiteIntermediateFieldValuativeRel K (SeparableClosure K) L
  let _ := finiteIntermediateFieldTopology K (SeparableClosure K) L
  have := finiteIntermediateField_isNonarchimedeanLocalField K (SeparableClosure K) L
  have := finiteIntermediateField_valuativeExtension K (SeparableClosure K) L
  -- Fix the integer-ring algebra explicitly to avoid searching through the ambient closure.
  let : Algebra 𝒪[L] L := Algebra.ofSubsemiring (R := L) (A := L) 𝒪[L]
  have : IsScalarTower 𝒪[K] 𝒪[L] L := .of_algebraMap_eq' rfl
  let y : L := IntermediateField.AdjoinSimple.gen K x
  have hy : aeval y f = 0 := by
    rw [aeval_eq_aeval_map (IsScalarTower.algebraMap_eq 𝒪[K] K L).symm]
    exact L.val.injective (((aeval_algHom_apply L.val y _).symm.trans hx).trans
      (map_zero _).symm)
  have : Module.IsTorsionFree 𝒪[K] L := Module.IsTorsionFree.trans K
  have hassoc : Associated (minpoly 𝒪[K] y) f :=
    associated_minpoly_of_eisenstein_isRoot y f hf (by
      simpa only [IsRoot, eval_map, ← aeval_def] using hy)
  have hf0 : f ≠ 0 := by
    intro h
    simp [h] at hdeg
    omega
  have hint : IsIntegral 𝒪[K] y := minpoly.ne_zero_iff.mp (hassoc.ne_zero_iff.mpr hf0)
  let π : 𝒪[L] := ⟨y, (Valuation.Integers.isIntegral_iff_valuation_le_one
    (Valuation.integer.integers (valuation K)) _).1 hint⟩
  have hroot : (f.map (algebraMap 𝒪[K] 𝒪[L])).IsRoot π := by
    have hinj : Function.Injective (IsScalarTower.toAlgHom 𝒪[K] 𝒪[L] L) :=
      IsFractionRing.injective 𝒪[L] L
    rw [IsRoot, eval_map, ← aeval_def]
    exact hinj (((aeval_algHom_apply (R := 𝒪[K]) (A := 𝒪[L]) (B := L)
      (IsScalarTower.toAlgHom 𝒪[K] 𝒪[L] L) π f).symm.trans
      hy).trans (map_zero _).symm)
  have hgen : K⟮π.val⟯ = ⊤ :=
    IntermediateField.AdjoinSimple.adjoin_gen_eq_top x
  have htr := isTotallyRamified_of_eisenstein_adjoin_eq_top hf hroot hgen
  rw [mem_totallyRamifiedOfDegree_iff]
  refine ⟨?_, (IntermediateField.isTotallyRamified_iff L).2 htr⟩
  rw [← (isTotallyRamified_iff_ramificationIndex_eq_finrank K L).1 htr]
  exact (ramificationIndex_eq_natDegree_of_eisenstein_adjoin_eq_top f hf π hroot hgen).trans hdeg

/-- Membership in the counted family is equivalent to being generated by a root of a monic
Eisenstein polynomial of the prescribed degree. -/
theorem mem_totallyRamifiedOfDegree_iff_exists_eisenstein_generator {n : ℕ} (hn : 0 < n)
    {L : IntermediateField K (SeparableClosure K)} :
    L ∈ totallyRamifiedOfDegree K n ↔
      ∃ (f : 𝒪[K][X]) (x : SeparableClosure K), f.Monic ∧ f.IsEisensteinAt 𝓂[K] ∧
        f.natDegree = n ∧ aeval x (f.map (algebraMap 𝒪[K] K)) = 0 ∧ K⟮x⟯ = L := by
  refine ⟨exists_eisenstein_generator_of_mem_totallyRamifiedOfDegree, ?_⟩
  rintro ⟨f, x, hmonic, hf, hdeg, hx, rfl⟩
  exact adjoin_mem_totallyRamifiedOfDegree_of_eisenstein hn hf hdeg hx

/-- The image of any embedding of a counted extension into the separable closure is again
a counted extension of the same degree. -/
theorem _root_.AlgHom.fieldRange_mem_totallyRamifiedOfDegree {n : ℕ}
    {L : IntermediateField K (SeparableClosure K)} (φ : L →ₐ[K] SeparableClosure K) (hn : 0 < n)
    (hL : L ∈ totallyRamifiedOfDegree K n) :
    φ.fieldRange ∈ totallyRamifiedOfDegree K n := by
  obtain ⟨f, x, hmonic, hf, hdeg, hx, hgen⟩ :=
    exists_eisenstein_generator_of_mem_totallyRamifiedOfDegree hL
  let y : L := ⟨x, hgen ▸ IntermediateField.mem_adjoin_simple_self K x⟩
  have hy : aeval y (f.map (algebraMap 𝒪[K] K)) = 0 := by
    exact L.val.injective (((aeval_algHom_apply L.val y _).symm.trans hx).trans
      (map_zero _).symm)
  have hygen : K⟮y⟯ = ⊤ := by
    apply IntermediateField.map_injective L.val
    simpa only [IntermediateField.adjoin_map, Set.image_singleton,
      ← AlgHom.fieldRange_eq_map, IntermediateField.fieldRange_val,
      IntermediateField.coe_val, y] using hgen
  have hφ : aeval (φ y) (f.map (algebraMap 𝒪[K] K)) = 0 := by
    rw [aeval_algHom_apply φ, hy, map_zero]
  have himage : K⟮φ y⟯ = φ.fieldRange := by
    simpa only [IntermediateField.adjoin_map, Set.image_singleton,
      ← AlgHom.fieldRange_eq_map] using
      congrArg (fun E : IntermediateField K L ↦ E.map φ) hygen
  rw [← himage]
  exact adjoin_mem_totallyRamifiedOfDegree_of_eisenstein hn hf hdeg hφ

end TauCeti

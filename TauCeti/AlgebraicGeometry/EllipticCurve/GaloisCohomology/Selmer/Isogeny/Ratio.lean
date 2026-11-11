/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Index.Isogeny
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.Real
import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.AlmostEverywhere
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.BaseChange.Degree
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients.Basic
import TauCeti.GroupTheory.Index.Comp
import Mathlib.Algebra.BigOperators.Finprod

/-!
# The global product of local Kummer ratios over the rationals

For an isogeny `φ : E₁ → E₂` over `ℚ`, the local Kummer ratio at a place `v` is
`[E₂(ℚ_v) : φ E₁(ℚ_v)] / #E₁(ℚ_v)[φ]`. Both counts are finite and positive.
The finite-place factors are one almost everywhere, so their product, including the real
factor, is a positive rational number, `TauCeti.Isogeny.globalKummerRatio`.
This is the local product that enters the global Selmer ratio formula. No equality with
orders of global Selmer groups is asserted here.

The product is multiplicative under composition. This follows from the kernel–cokernel
index identity at each place; in particular it does not require choices of minimal equations,
differentials, or embeddings of separable closures. A finite set containing the nontrivial
factors computes the product exactly.

## References

* J. W. S. Cassels, *Arithmetic on curves of genus 1. VIII. On conjectures of Birch and
  Swinnerton-Dyer*, J. Reine Angew. Math. 217 (1965), 180–199.
* E. F. Schaefer, *Class groups and Selmer groups*, J. Number Theory 56 (1996), §3.
-/

public noncomputable section

open IsDedekindDomain WeierstrassCurve

namespace TauCeti.Isogeny

attribute [local instance] Classical.propDecidable

/-- Use the completion's scalar action, rather than the other rational-algebra instance. -/
local instance (v : HeightOneSpectrum ℤ) : Algebra ℚ (v.adicCompletion ℚ) :=
  HeightOneSpectrum.instAlgebraAdicCompletion ℤ ℚ v

local instance (v : HeightOneSpectrum ℤ) : Finite (ℤ ⧸ v.asIdeal) :=
  Ring.HasFiniteQuotients.finiteQuotient v.ne_bot

variable {W₁ W₂ W₃ : WeierstrassCurve ℚ} [W₁.IsElliptic] [W₂.IsElliptic] [W₃.IsElliptic]

/-- The local Kummer ratio at a finite prime of `ℤ`: the order of the local Kummer image
divided by the order of the local rational kernel. -/
def finiteKummerRatio (φ : Isogeny W₁.toAffine W₂.toAffine) (v : HeightOneSpectrum ℤ) : ℚ :=
  let f := Hom.ofIsogeny (φ.map (algebraMap ℚ (v.adicCompletion ℚ)))
  (f.pointMapHom.range.index : ℚ) / Nat.card f.pointMapHom.ker

/-- The finite local ratio in terms of the point homomorphism. -/
theorem finiteKummerRatio_def (φ : Isogeny W₁.toAffine W₂.toAffine)
    (v : HeightOneSpectrum ℤ) :
    φ.finiteKummerRatio v =
      ((Hom.ofIsogeny (φ.map (algebraMap ℚ (v.adicCompletion ℚ)))).pointMapHom.range.index : ℚ) /
        Nat.card (Hom.ofIsogeny (φ.map (algebraMap ℚ (v.adicCompletion ℚ)))).pointMapHom.ker :=
  (rfl)

/-- Each finite local factor is positive: neither count is a junk cardinality. -/
theorem finiteKummerRatio_pos (φ : Isogeny W₁.toAffine W₂.toAffine)
    (v : HeightOneSpectrum ℤ) : 0 < φ.finiteKummerRatio v := by
  let f := Hom.ofIsogeny (φ.map (algebraMap ℚ (v.adicCompletion ℚ)))
  have hf := Hom.ofIsogeny_ne_zero (φ.map (algebraMap ℚ (v.adicCompletion ℚ)))
  have := f.finite_ker_pointMapHom hf
  have := Hom.finiteIndex_range_pointMapHom_of_degree_ne_zero
    (A := ℤ) (F := ℚ) v (f := f) (by
      rw [Hom.degree_ofIsogeny]
      exact_mod_cast (φ.map (algebraMap ℚ (v.adicCompletion ℚ))).degree_pos.ne')
  rw [finiteKummerRatio_def]
  exact div_pos (Nat.cast_pos.mpr f.pointMapHom.range.index_pos)
    (Nat.cast_pos.mpr Nat.card_pos)

/-- Only finitely many finite primes have nontrivial local Kummer factor. -/
theorem hasFiniteMulSupport_finiteKummerRatio (φ : Isogeny W₁.toAffine W₂.toAffine) :
    φ.finiteKummerRatio.HasFiniteMulSupport := by
  classical
  obtain ⟨T, -, hT, hdeg⟩ := exists_finset_isElliptic_integralModel_adicCompletion ℤ W₁
    (Nat.cast_ne_zero.mpr φ.degree_pos.ne') ∅
  apply Filter.eventually_cofinite.mp
  filter_upwards [T.eventually_cofinite_notMem,
    eventually_isElliptic_integralModel_adicCompletion ℤ W₂] with v hv ⟨hI₂, hE₂⟩
  obtain ⟨hI₁, hE₁⟩ := hT v hv
  simp only [WeierstrassCurve.baseChange] at hI₁ hI₂ hE₁ hE₂
  have heq := Hom.index_range_eq_card_ker_of_isElliptic_integralModel
    (f := Hom.ofIsogeny (φ.map (algebraMap ℚ (v.adicCompletion ℚ)))) (by
      rw [Hom.degree_ofIsogeny, degree_map]
      exact hdeg v hv)
  have := (Hom.ofIsogeny (φ.map (algebraMap ℚ (v.adicCompletion ℚ)))).finite_ker_pointMapHom
    (Hom.ofIsogeny_ne_zero _)
  rw [finiteKummerRatio_def, heq, div_self (Nat.cast_ne_zero.mpr Nat.card_pos.ne')]

/-- The global Kummer ratio, with the real factor and every finite-place factor. -/
def globalKummerRatio (φ : Isogeny W₁.toAffine W₂.toAffine) : ℚ :=
  let f := Hom.ofIsogeny (φ.map (algebraMap ℚ ℝ))
  ((f.pointMapHom.range.index : ℚ) / Nat.card f.pointMapHom.ker) *
    ∏ᶠ v : HeightOneSpectrum ℤ, φ.finiteKummerRatio v

/-- The defining product, including the real place. -/
theorem globalKummerRatio_def (φ : Isogeny W₁.toAffine W₂.toAffine) :
    φ.globalKummerRatio =
      ((Hom.ofIsogeny (φ.map (algebraMap ℚ ℝ))).pointMapHom.range.index : ℚ) /
        Nat.card (Hom.ofIsogeny (φ.map (algebraMap ℚ ℝ))).pointMapHom.ker *
      ∏ᶠ v : HeightOneSpectrum ℤ, φ.finiteKummerRatio v :=
  (rfl)

/-- A finite exceptional set computes the product, independently of the extra primes included. -/
theorem globalKummerRatio_eq_mul_prod (φ : Isogeny W₁.toAffine W₂.toAffine)
    (S : Finset (HeightOneSpectrum ℤ)) (hS : ∀ v ∉ S, φ.finiteKummerRatio v = 1) :
    φ.globalKummerRatio =
      ((Hom.ofIsogeny (φ.map (algebraMap ℚ ℝ))).pointMapHom.range.index : ℚ) /
        Nat.card (Hom.ofIsogeny (φ.map (algebraMap ℚ ℝ))).pointMapHom.ker *
      ∏ v ∈ S, φ.finiteKummerRatio v := by
  rw [globalKummerRatio_def, finprod_eq_prod_of_mulSupport_subset]
  exact fun v hv => by_contra fun h => hv (hS v h)

/-- The global Kummer ratio is positive. -/
theorem globalKummerRatio_pos (φ : Isogeny W₁.toAffine W₂.toAffine) :
    0 < φ.globalKummerRatio := by
  let f := Hom.ofIsogeny (φ.map (algebraMap ℚ ℝ))
  have hf := Hom.ofIsogeny_ne_zero (φ.map (algebraMap ℚ ℝ))
  have := f.finite_ker_pointMapHom hf
  have := f.finiteIndex_range_pointMapHom_real hf
  rw [globalKummerRatio_def]
  exact mul_pos
    (div_pos (Nat.cast_pos.mpr f.pointMapHom.range.index_pos) (Nat.cast_pos.mpr Nat.card_pos))
    (by
      rw [finprod_eq_prod _ φ.hasFiniteMulSupport_finiteKummerRatio]
      exact Finset.prod_pos fun v _ => φ.finiteKummerRatio_pos v)

/-- Local Kummer ratios multiply under composition of isogenies. -/
@[simp]
theorem finiteKummerRatio_comp (ψ : Isogeny W₂.toAffine W₃.toAffine)
    (φ : Isogeny W₁.toAffine W₂.toAffine) (v : HeightOneSpectrum ℤ) :
    (ψ.comp φ).finiteKummerRatio v = ψ.finiteKummerRatio v * φ.finiteKummerRatio v := by
  classical
  let f := Hom.ofIsogeny (φ.map (algebraMap ℚ (v.adicCompletion ℚ)))
  let g := Hom.ofIsogeny (ψ.map (algebraMap ℚ (v.adicCompletion ℚ)))
  have := f.finite_ker_pointMapHom (Hom.ofIsogeny_ne_zero _)
  have := g.finite_ker_pointMapHom (Hom.ofIsogeny_ne_zero _)
  have hc : (Hom.ofIsogeny ((ψ.comp φ).map (algebraMap ℚ (v.adicCompletion ℚ)))).pointMapHom =
      g.pointMapHom.comp f.pointMapHom := by
    rw [comp_map, ← Hom.ofIsogeny_comp_ofIsogeny]
    ext P
    simpa only [Hom.pointMapHom_apply, AddMonoidHom.comp_apply] using Hom.comp_pointMap g f P
  simp only [finiteKummerRatio_def, hc]
  exact f.pointMapHom.index_range_div_card_ker_comp g.pointMapHom

/-- The global product of local Kummer ratios is multiplicative under composition. -/
@[simp]
theorem globalKummerRatio_comp (ψ : Isogeny W₂.toAffine W₃.toAffine)
    (φ : Isogeny W₁.toAffine W₂.toAffine) :
    (ψ.comp φ).globalKummerRatio = ψ.globalKummerRatio * φ.globalKummerRatio := by
  classical
  let f := Hom.ofIsogeny (φ.map (algebraMap ℚ ℝ))
  let g := Hom.ofIsogeny (ψ.map (algebraMap ℚ ℝ))
  have := f.finite_ker_pointMapHom (Hom.ofIsogeny_ne_zero _)
  have := g.finite_ker_pointMapHom (Hom.ofIsogeny_ne_zero _)
  have hc : (Hom.ofIsogeny ((ψ.comp φ).map (algebraMap ℚ ℝ))).pointMapHom =
      g.pointMapHom.comp f.pointMapHom := by
    rw [comp_map, ← Hom.ofIsogeny_comp_ofIsogeny]
    ext P
    simpa only [Hom.pointMapHom_apply, AddMonoidHom.comp_apply] using Hom.comp_pointMap g f P
  simp only [globalKummerRatio_def, hc, finiteKummerRatio_comp]
  rw [f.pointMapHom.index_range_div_card_ker_comp,
    finprod_mul_distrib ψ.hasFiniteMulSupport_finiteKummerRatio
      φ.hasFiniteMulSupport_finiteKummerRatio]
  ring

/-- The identity isogeny has local Kummer ratio one. -/
@[simp]
theorem finiteKummerRatio_id (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (v : HeightOneSpectrum ℤ) : (Isogeny.id W.toAffine).finiteKummerRatio v = 1 := by
  apply mul_left_cancel₀ (ne_of_gt ((Isogeny.id W.toAffine).finiteKummerRatio_pos v))
  simpa only [id_comp, mul_one] using
    (finiteKummerRatio_comp (Isogeny.id W.toAffine) (Isogeny.id W.toAffine) v).symm

/-- The identity isogeny has global Kummer ratio one. -/
@[simp]
theorem globalKummerRatio_id (W : WeierstrassCurve ℚ) [W.IsElliptic] :
    (Isogeny.id W.toAffine).globalKummerRatio = 1 := by
  apply mul_left_cancel₀ (ne_of_gt (Isogeny.id W.toAffine).globalKummerRatio_pos)
  simpa only [id_comp, mul_one] using
    (globalKummerRatio_comp (Isogeny.id W.toAffine) (Isogeny.id W.toAffine)).symm

end TauCeti.Isogeny

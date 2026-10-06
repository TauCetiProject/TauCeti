/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Operators
public import TauCeti.NumberTheory.ModularForms.ModularSymbols.Hecke.Basic
public import TauCeti.NumberTheory.ModularForms.ModularSymbols.Period.Map

/-!
# Hecke equivariance of the period map

Let `Γ ≤ SL(2, ℤ)` be a subgroup of finite index and `D = Γ' δ Γ' = ⊔ᵥ Γ' aᵥ` a double coset,
with `Γ' = Γ.map (mapGL ℚ)` and `δ` an integral matrix of positive determinant. The same double
coset acts on cusp forms of weight `k = w + 2` on `Γ`, by `f ↦ ∑ᵥ f ∣[k] aᵥ`
(`HeckeRing.GL2.heckeSlashCuspFormEnd`), and on the modular symbols `𝕄_w(Γ; R)`, by
`{α, β} ⊗ P ↦ ∑ᵥ {aᵥα, aᵥβ} ⊗ (P ∣ adj aᵥ)` (`TauCeti.ModularSymbols.heckeSymbol`). This file
proves that the period map `TauCeti.ModularSymbols.periodMap` intertwines the two actions:

`periodMap (T_D f) = periodMap f ∘ T_D`.

Since the period map sends a cusp form to a functional on the symbols, the symbol-side operator
appears by precomposition, as a transpose. The proof is the substitution `z ↦ aᵥ z` in each
summand (`TauCeti.ModularSymbols.cuspIntegral_periodIntegrand_slash`):
`∫_β^α (f ∣[k] aᵥ)(z) P(z, 1) dz = ∫_{aᵥβ}^{aᵥα} f(z) (P ∣ adj aᵥ)(z, 1) dz`, where the
determinant factors of the slash action and of the adjugate cancel. Both sides are computed with
the same representatives `aᵥ = DoubleCoset.rightCosetRep D v`, so no comparison of coset
decompositions is needed.

Specialized to `Γ = Γ₁(N)` and the double coset of `diag(1, n)`, this is the equivariance
`periodMap (T_n f) = periodMap f ∘ T_n` of the period map for the Hecke operators `T_n`. This is
the input, alongside the injectivity of the period map, through which integrality of the Hecke
operators on modular symbols is transferred to the Hecke operators on cusp forms.

## Main results

* `TauCeti.ModularSymbols.periodMap_heckeSlashCuspFormEnd`: the period map intertwines the
  operator of a double coset on cusp forms with the transpose of its operator on modular symbols.
* `TauCeti.ModularSymbols.periodMap_heckeTCuspNat`: the same for the Hecke operators `T_n` at
  level `Γ₁(N)`.

## Provenance

The statement corresponds to `periodMap'_heckeEnd` in the AINTLIB `LeanModularForms` project
(`HeckeRIngs/GL2/ModularSymbols/PeriodHecke.lean`, Apache-2.0); no code is transcribed.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §8.2.
* W. Stein, *Modular Forms: A Computational Approach*, Graduate Studies in Mathematics **79**,
  American Mathematical Society, 2007, §8.5.
-/

public section

open DoubleCoset HeckeRing.GL2 HeckeRing.GLn Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups ModularForm

namespace TauCeti.ModularSymbols

variable {R : Type*} [CommRing R] [Algebra R ℂ] {k : ℤ} {w : ℕ}

/-- **Hecke equivariance of the period map.** For a double coset `D = Γ' δ Γ'` with `δ` an
integral matrix of positive determinant, the period map intertwines the operator of `D` on cusp
forms of weight `w + 2` on `Γ` with the transpose of its operator on `𝕄_w(Γ; R)`:
`⟪T_D f, x⟫ = ⟪f, T_D x⟫`. -/
theorem periodMap_heckeSlashCuspFormEnd {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex]
    {Δ : Submonoid (GL (Fin 2) ℚ)} (D : HeckeCoset Δ (Γ.map (mapGL ℚ)) (Γ.map (mapGL ℚ)))
    [Finite (DecompQuotient (Γ.map (mapGL ℚ)) (Γ.map (mapGL ℚ)) (D.out : GL (Fin 2) ℚ)⁻¹)]
    (hDpos : (D.out : GL (Fin 2) ℚ) ∈ Matrix.GLPos (Fin 2) ℚ)
    (hDint : (D.out : GL (Fin 2) ℚ) ∈ intEntries 2) (hk : k = w + 2)
    (f : CuspForm (Γ.map (mapGL ℝ)) k) :
    periodMap R Γ hk (heckeSlashCuspFormEnd k D hDpos f) =
      periodMap R Γ hk f ∘ₗ heckeSymbol Γ Γ D hDint := by
  refine Representation.Coinvariants.hom_ext (hom_ext_unimodular fun γ P ↦ ?_)
  have hγ : 0 < ((mapGL ℚ γ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply, det_mapGL, Units.val_one]
    exact one_pos
  have hpos := det_rightCosetRep_pos D (ModularForm.map_mapGL_le_glpos Γ) hDpos
  have hA (v) := (map_intMatrix 2 ⟨rightCosetRep D v,
    rightCosetRep_mem D hDint (map_mapGL_le_intEntries 2 Γ) v⟩).symm
  -- both sides are read on the symbol `{γ∞, γ0} ⊗ P`: on the left as a period of the slash sum
  -- `∑ᵥ f ∣[k] aᵥ`, on the right as the sum of the periods of `f` on `{aᵥγ∞, aᵥγ0} ⊗ (P ∣ adj aᵥ)`
  simp only [LinearMap.comp_apply, ← symbol_apply, periodMap_symbol, heckeSymbol_symbol, map_sum,
    coe_heckeSlashCuspFormEnd, heckeSlashSum_def, periodIntegrand_sum_left]
  -- each summand is the substitution `z ↦ aᵥ z`; the summands are integrable along the geodesic
  -- because they are themselves periods of `f`, along the geodesic moved by `aᵥ`
  rw [cuspIntegral_sum _ hγ fun v _ ↦ ?_]
  · exact Finset.sum_congr rfl fun v _ ↦
      cuspIntegral_periodIntegrand_slash hk f P (hA v) (hpos v) _ _
  · rw [← periodIntegrand_adjugate_slash hk f P (hA v) (hpos v), ← SlashAction.slash_mul]
    refine integrableOn_resToImagAxis_periodIntegrand_slash f hk _ ?_
    rw [Units.val_mul, Matrix.det_mul]
    exact mul_pos (hpos v) hγ

/-- **Hecke equivariance of the period map for `T_n`.** At level `Γ₁(N)`, the period map
intertwines the Hecke operator `T_n` on cusp forms of weight `w + 2` with the transpose of the
Hecke operator `T_n` on `𝕄_w(Γ₁(N); R)`: `⟪T_n f, x⟫ = ⟪f, T_n x⟫`. -/
theorem periodMap_heckeTCuspNat (N : ℕ) [NeZero N] (n : ℕ) [NeZero n] (hk : k = w + 2)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    periodMap R (Gamma1 N) hk (heckeTCuspNat k n f) =
      periodMap R (Gamma1 N) hk f ∘ₗ heckeTSymbol R w N n := by
  have h : heckeTCuspNat k n f =
      heckeSlashCuspFormEnd k (diagCosetGamma1 N n) (out_mem_glpos_of_delta0 N _) f :=
    DFunLike.coe_injective (by rw [coe_heckeTCuspNat, coe_heckeSlashCuspFormEnd])
  rw [h, heckeTSymbol_def, periodMap_heckeSlashCuspFormEnd]

end TauCeti.ModularSymbols

end

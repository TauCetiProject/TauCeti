/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.HeckeRing.GL2.Gamma1.DiamondCosets
public import TauCeti.NumberTheory.ModularForms.ModularSymbols.Hecke.Composition

/-!
# Diamond operators on modular symbols

For `d : (ZMod N)ˣ`, choose a lift `g ∈ Γ₀(N)` and let `⟨d⟩` act on `𝕄_w(Γ₁(N); R)` through
the one-term double coset `Γ₁(N) g Γ₁(N)`. The double coset depends only on `d`, so the
resulting operator is independent of the lift. Since `Γ₁(N)` is normal in
`Γ₀(N)`, these operators multiply exactly as their labels do and hence define a monoid action

`(ZMod N)ˣ →* End_R(𝕄_w(Γ₁(N); R))`.

This supplies the diamond generators on the integral symbol module. Together with the operators
`heckeTSymbol`, they are the symbol-side generators used by the period pairing and by the
integral Hecke algebra.

## Main definitions

* `TauCeti.ModularSymbols.diamondSymbol`: the diamond operator on modular symbols.
* `TauCeti.ModularSymbols.diamondSymbolHom`: the monoid homomorphism formed by the diamond
  operators.

## Main results

* `TauCeti.ModularSymbols.diamondSymbol_eq_heckeSymbol`: compute the operator using any lift in
  `Γ₀(N)` with the prescribed label.
* `TauCeti.ModularSymbols.diamondSymbol_mk`: on a class, the diamond is the class of the
  translate by any lift.
* `TauCeti.ModularSymbols.diamondSymbol_mul`: `⟨d₁d₂⟩ = ⟨d₁⟩ ∘ ⟨d₂⟩`.
* `TauCeti.ModularSymbols.commute_diamondSymbol`: any two diamond operators commute.

## References

* W. Stein, *Modular Forms: A Computational Approach*, Graduate Studies in Mathematics **79**,
  American Mathematical Society, 2007, §8.3.
-/

public section

open DoubleCoset HeckeRing.GL2 HeckeRing.GLn Matrix Matrix.SpecialLinearGroup
  CongruenceSubgroup MvPolynomial Representation TensorProduct
open scoped MatrixGroups

namespace TauCeti.ModularSymbols

variable {R : Type*} [CommRing R] {w N : ℕ} [NeZero N]

/-- **A diamond double coset acts by its single representative.** On the class of `x`, the
operator attached to `Γ₁(N) g Γ₁(N)` is the class of `g • x`. The normality of `Γ₁(N)` in
`Γ₀(N)` collapses the double coset to one right coset. -/
theorem heckeSymbol_diamondCosetGamma1_mk (g : ↥(Gamma0 N))
    (x : degreeZero R ⊗[R] homogeneousSubmodule (Fin 2) R w) :
    heckeSymbol (Gamma1 N) (Gamma1 N) (diamondCosetGamma1 N g)
        (Delta0_le_intEntries N (diamondCosetGamma1 N g).out.2) (Coinvariants.mk _ x) =
      Coinvariants.mk _
        (symbolIntRep R w ⟨mapGL ℚ (g : SL(2, ℤ)), mapGL_mem_intEntries 2 g⟩ x) := by
  rw [heckeSymbol_mk_eq_sum_of_rightCosets (Gamma1 N) (Gamma1 N)
    (diamondCosetGamma1 N g) _ (fun _ : Unit ↦ mapGL ℚ (g : SL(2, ℤ)))
    (fun _ ↦ mapGL_mem_intEntries 2 g)
    (doubleCoset_out_diamondCosetGamma1_eq_iUnion_rightCosets g)
    (Function.injective_of_subsingleton _), Fintype.sum_unique]

/-- **The diamond operator on modular symbols.** A unit `d : (ZMod N)ˣ` acts through the double
coset of any lift `g ∈ Γ₀(N)` whose lower-right entry is `d`. Independence of the lift is
`diamondSymbol_eq_heckeSymbol`. -/
noncomputable def diamondSymbol (R : Type*) [CommRing R] (w N : ℕ) [NeZero N]
    (d : (ZMod N)ˣ) : Module.End R (ModularSymbols R (Gamma1 N) w) :=
  let g := (Gamma0Map_toHomUnits_surjective d).choose
  heckeSymbol (Gamma1 N) (Gamma1 N) (diamondCosetGamma1 N g)
    (Delta0_le_intEntries N (diamondCosetGamma1 N g).out.2)

/-- Compute `diamondSymbol` using any lift in `Γ₀(N)` with the prescribed lower-right entry. -/
theorem diamondSymbol_eq_heckeSymbol {d : (ZMod N)ˣ} (g : ↥(Gamma0 N))
    (hg : (Gamma0Map N).toHomUnits g = d) :
    diamondSymbol R w N d =
      heckeSymbol (Gamma1 N) (Gamma1 N) (diamondCosetGamma1 N g)
        (Delta0_le_intEntries N (diamondCosetGamma1 N g).out.2) := by
  let g' := (Gamma0Map_toHomUnits_surjective d).choose
  have hD : diamondCosetGamma1 N g' = diamondCosetGamma1 N g :=
    diamondCosetGamma1_eq_iff.mpr
      ((Gamma0Map_toHomUnits_surjective d).choose_spec.trans hg.symm)
  exact congrArg
    (fun D ↦ heckeSymbol (Gamma1 N) (Gamma1 N) D
      (Delta0_le_intEntries N D.out.2)) hD

/-- On a class, `diamondSymbol` is translation by any lift of the diamond label. -/
theorem diamondSymbol_mk {d : (ZMod N)ˣ} (g : ↥(Gamma0 N))
    (hg : (Gamma0Map N).toHomUnits g = d)
    (x : degreeZero R ⊗[R] homogeneousSubmodule (Fin 2) R w) :
    diamondSymbol R w N d (Coinvariants.mk _ x) =
      Coinvariants.mk _
        (symbolIntRep R w ⟨mapGL ℚ (g : SL(2, ℤ)), mapGL_mem_intEntries 2 g⟩ x) := by
  rw [diamondSymbol_eq_heckeSymbol g hg, heckeSymbol_diamondCosetGamma1_mk]

/-- The action of a diamond operator on a modular symbol, computed using any lift of its label. -/
theorem diamondSymbol_symbol {d : (ZMod N)ˣ} (g : ↥(Gamma0 N))
    (hg : (Gamma0Map N).toHomUnits g = d) (α β : OnePoint ℚ)
    (P : homogeneousSubmodule (Fin 2) R w) :
    diamondSymbol R w N d (symbol (Gamma1 N) α β P) =
      symbol (Gamma1 N) (mapGL ℚ (g : SL(2, ℤ)) • α) (mapGL ℚ (g : SL(2, ℤ)) • β)
        (binaryFormRep R w
          (MulOpposite.op (adjugate
            (intMatrix 2
              ⟨mapGL ℚ (g : SL(2, ℤ)), mapGL_mem_intEntries 2 g⟩))) P) := by
  rw [symbol_apply, diamondSymbol_mk g hg, mk_symbolIntRep_tmul]

/-- The diamond operator with label `1` is the identity. -/
@[simp]
theorem diamondSymbol_one : diamondSymbol R w N 1 = 1 := by
  rw [diamondSymbol_eq_heckeSymbol 1 (map_one _), diamondCosetGamma1_one, heckeSymbol_one]
  rfl

/-- **Diamond operators multiply according to their labels**:
`⟨d₁d₂⟩ = ⟨d₁⟩ ∘ ⟨d₂⟩` on modular symbols. -/
@[simp]
theorem diamondSymbol_mul (d₁ d₂ : (ZMod N)ˣ) :
    diamondSymbol R w N (d₁ * d₂) = diamondSymbol R w N d₁ * diamondSymbol R w N d₂ := by
  obtain ⟨g₁, hg₁⟩ := Gamma0Map_toHomUnits_surjective d₁
  obtain ⟨g₂, hg₂⟩ := Gamma0Map_toHomUnits_surjective d₂
  rw [diamondSymbol_eq_heckeSymbol (g₁ * g₂) (by rw [map_mul, hg₁, hg₂]),
    diamondSymbol_eq_heckeSymbol g₁ hg₁, diamondSymbol_eq_heckeSymbol g₂ hg₂,
    Module.End.mul_eq_comp]
  refine (heckeSymbol_comp_heckeSymbol_eq_heckeSymbol (Gamma1 N) (Gamma1 N) (Gamma1 N) _ _ _ _
    (fun _ : Unit ↦ mapGL ℚ (g₁ : SL(2, ℤ))) (fun _ : Unit ↦ mapGL ℚ (g₂ : SL(2, ℤ)))
    (doubleCoset_out_diamondCosetGamma1_eq_iUnion_rightCosets g₁)
    (Function.injective_of_subsingleton _)
    (doubleCoset_out_diamondCosetGamma1_eq_iUnion_rightCosets g₂)
    (Function.injective_of_subsingleton _) (diamondCosetGamma1 N (g₁ * g₂)) ?_
    (Function.injective_of_subsingleton _)).symm
  rw [doubleCoset_mul_doubleCoset_eq_iUnion_rightCosets _ _
      (doubleCoset_out_diamondCosetGamma1_eq_iUnion_rightCosets g₁)
      (doubleCoset_out_diamondCosetGamma1_eq_iUnion_rightCosets g₂),
    doubleCoset_out_diamondCosetGamma1_eq_iUnion_rightCosets, Set.iUnion_const, Set.iUnion_const,
    Subgroup.coe_mul, map_mul]

/-- Any two diamond operators on modular symbols commute. -/
theorem commute_diamondSymbol (d₁ d₂ : (ZMod N)ˣ) :
    Commute (diamondSymbol R w N d₁) (diamondSymbol R w N d₂) := by
  rw [commute_iff_eq, ← diamondSymbol_mul, ← diamondSymbol_mul]
  exact congrArg (diamondSymbol R w N) (mul_comm d₁ d₂)

/-- The diamond operators on modular symbols, as a monoid homomorphism from `(ZMod N)ˣ`. -/
noncomputable def diamondSymbolHom (R : Type*) [CommRing R] (w N : ℕ) [NeZero N] :
    (ZMod N)ˣ →* Module.End R (ModularSymbols R (Gamma1 N) w) where
  toFun := diamondSymbol R w N
  map_one' := diamondSymbol_one
  map_mul' := diamondSymbol_mul

@[simp] lemma diamondSymbolHom_apply (d : (ZMod N)ˣ) :
    diamondSymbolHom R w N d = diamondSymbol R w N d :=
  (rfl)

end TauCeti.ModularSymbols

end

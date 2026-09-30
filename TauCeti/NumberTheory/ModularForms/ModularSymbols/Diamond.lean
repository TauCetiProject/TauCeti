/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.ModularSymbols.Hecke
public import TauCeti.NumberTheory.HeckeRing.GL2.Gamma1.DiamondCosets

/-!
# Diamond operators on modular symbols

The diamond operator on the `Γ₁(N)`-coinvariants is the Hecke action of the diamond double
coset. Since `Γ₀(N)` normalizes `Γ₁(N)`, this double coset has one right coset. Thus on a class
`[x]`, the operator associated to `d` is `[g · x]` for any `g ∈ Γ₀(N)` mapping to `d`.

This is the integral counterpart of the diamond operators on modular and cusp forms; the
period pairing uses the induced action by precomposition.

The construction follows the quotient description of diamond operators in
Diamond–Shurman, *A First Course in Modular Forms*, §5.1, and the coinvariant description
of modular symbols in Stein, *Modular Forms: A Computational Approach*, §8.2.
Its representative formula adapts the chosen-representative construction of Chris Birkbeck in
`TauCeti/NumberTheory/ModularForms/DiamondOperators.lean` to modular-symbol coinvariants.
-/

public section

open Matrix.SpecialLinearGroup CongruenceSubgroup Representation TensorProduct MvPolynomial
  OnePoint DoubleCoset HeckeRing.GL2 HeckeRing.GLn MulOpposite
open scoped MatrixGroups Pointwise

namespace TauCeti.ModularSymbols

variable {R : Type*} [CommRing R] {w N : ℕ} [NeZero N]

/-- The diamond operator `⟨d⟩` on modular symbols at level `Γ₁(N)`, given by the Hecke action
of its diamond double coset. -/
noncomputable def diamondOp (d : (ZMod N)ˣ) :
    Module.End R (ModularSymbols R (Gamma1 N) w) :=
  let g := (Gamma0Map_toHomUnits_surjective d).choose
  heckeSymbol (Gamma1 N) (Gamma1 N) (diamondCosetGamma1 N g)
    (Delta0_le_intEntries N (diamondCosetGamma1 N g).out.2)

/-- The diamond operator is the Hecke operator of the double coset of any representative. -/
theorem diamondOp_eq_heckeSymbol (d : (ZMod N)ˣ) (g : ↥(Gamma0 N))
    (hg : (Gamma0Map N).toHomUnits g = d) :
    diamondOp (R := R) (w := w) d =
      heckeSymbol (Gamma1 N) (Gamma1 N) (diamondCosetGamma1 N g)
        (Delta0_le_intEntries N (diamondCosetGamma1 N g).out.2) := by
  dsimp only [diamondOp]
  have hcoset : diamondCosetGamma1 N (Gamma0Map_toHomUnits_surjective d).choose =
      diamondCosetGamma1 N g := diamondCosetGamma1_eq_iff.mpr
        ((Gamma0Map_toHomUnits_surjective d).choose_spec.trans hg.symm)
  simp only [hcoset]

/-- The diamond operator on a coinvariant class. -/
theorem diamondOp_mk (d : (ZMod N)ˣ) (g : ↥(Gamma0 N))
    (hg : (Gamma0Map N).toHomUnits g = d)
    (x : degreeZero R ⊗[R] homogeneousSubmodule (Fin 2) R w) :
    diamondOp d (Coinvariants.mk _ x) =
      Coinvariants.mk _ (symbolRep R w (g : SL(2, ℤ)) x) := by
  rw [diamondOp_eq_heckeSymbol d g hg]
  rw [heckeSymbol_mk_eq_sum_of_rightCosets (a := fun _ : Unit ↦
    mapGL ℚ (g : SL(2, ℤ))) (ha := fun _ ↦ mapGL_mem_intEntries 2 _)
    (hcover := doubleCoset_out_diamondCosetGamma1_eq_iUnion_rightCosets g)
    (hinj := Function.injective_of_subsingleton _)]
  rw [Fintype.sum_unique, symbolIntRep_mapGL]

/-- On symbols, `⟨d⟩` translates both endpoints by a representative of `d` and acts on
the binary form by its inverse. -/
theorem diamondOp_symbol (d : (ZMod N)ˣ) (g : ↥(Gamma0 N))
    (hg : (Gamma0Map N).toHomUnits g = d) (α β : OnePoint ℚ)
    (P : homogeneousSubmodule (Fin 2) R w) :
    diamondOp d (symbol (Gamma1 N) α β P) =
      symbol (Gamma1 N) (mapGL ℚ (g : SL(2, ℤ)) • α)
        (mapGL ℚ (g : SL(2, ℤ)) • β)
        (binaryFormSLRep R w (g : SL(2, ℤ)) P) := by
  rw [symbol_apply, diamondOp_mk d g hg]
  rw [symbolRep_tmul, symbol_apply]
  congr 1
  congr 1
  ext1
  simp

/-- The identity diamond acts as the identity. -/
@[simp]
theorem diamondOp_one : diamondOp (R := R) (w := w) (N := N) 1 = 1 := by
  rw [diamondOp_eq_heckeSymbol 1 1 (map_one _)]
  simp only [diamondCosetGamma1_one]
  exact heckeSymbol_one (Gamma1 N) _

/-- Diamond operators multiply according to their indices. -/
@[simp]
theorem diamondOp_mul (d e : (ZMod N)ˣ) :
    diamondOp (R := R) (w := w) (d * e) =
      diamondOp d * diamondOp e := by
  obtain ⟨g, hg⟩ := Gamma0Map_toHomUnits_surjective (N := N) d
  obtain ⟨h, hh⟩ := Gamma0Map_toHomUnits_surjective (N := N) e
  apply Coinvariants.hom_ext
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply]
  rw [diamondOp_mk (d * e) (g * h) (by simp [map_mul, hg, hh]),
    Module.End.mul_apply, diamondOp_mk e h hh, diamondOp_mk d g hg]
  simp [map_mul, Module.End.mul_apply]

/-- The diamond action as a monoid homomorphism into the endomorphism ring of modular symbols. -/
noncomputable def diamondOpHom :
    (ZMod N)ˣ →* Module.End R (ModularSymbols R (Gamma1 N) w) where
  toFun := diamondOp
  map_one' := diamondOp_one
  map_mul' := diamondOp_mul

@[simp]
theorem diamondOpHom_apply (d : (ZMod N)ˣ) :
    diamondOpHom (R := R) (w := w) d = diamondOp d := (rfl)

end TauCeti.ModularSymbols

end

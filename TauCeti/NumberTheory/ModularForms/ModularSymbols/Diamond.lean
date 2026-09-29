/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.ModularSymbols.Basic
public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Basic

/-!
# Diamond operators on modular symbols

The subgroup `Γ₀(N)` normalizes `Γ₁(N)` and acts on the `Γ₁(N)`-coinvariants defining modular
symbols.
The action factors through the lower-right-entry homomorphism
`Γ₀(N) → (ZMod N)ˣ`, giving a diamond action on modular symbols. On a class `[x]`, the
operator associated to `d` is `[g · x]` for any `g ∈ Γ₀(N)` mapping to `d`.

This is the integral counterpart of the diamond operators on modular and cusp forms; the
period pairing uses the induced action by precomposition.

The construction follows the quotient description of diamond operators in
Diamond–Shurman, *A First Course in Modular Forms*, §5.1, and the coinvariant description
of modular symbols in Stein, *Modular Forms: A Computational Approach*, §8.2.
It adapts the chosen-representative construction of Chris Birkbeck in
`TauCeti/NumberTheory/ModularForms/DiamondOperators.lean` to modular-symbol coinvariants.
-/

public section

open Matrix.SpecialLinearGroup CongruenceSubgroup Representation TensorProduct MvPolynomial
  OnePoint
open scoped MatrixGroups

namespace TauCeti.ModularSymbols

variable {R : Type*} [CommRing R] {w N : ℕ}

/-- The action of `g ∈ Γ₀(N)` on modular symbols at level `Γ₁(N)`, induced by the
`SL₂(ℤ)`-action before passing to coinvariants. -/
private noncomputable def gamma0Symbol (g : ↥(Gamma0 N)) :
    Module.End R (ModularSymbols R (Gamma1 N) w) :=
  Coinvariants.lift _
    (Coinvariants.mk _ ∘ₗ symbolRep R w (g : SL(2, ℤ))) fun h ↦ by
      apply LinearMap.ext
      intro x
      have hc : (g : SL(2, ℤ)) * (h : SL(2, ℤ)) * (g : SL(2, ℤ))⁻¹ ∈ Gamma1 N :=
        Gamma0_normalizes_Gamma1 g h h.property
      have heq : (g : SL(2, ℤ)) * (h : SL(2, ℤ)) =
          ((g : SL(2, ℤ)) * h * (g : SL(2, ℤ))⁻¹) * g := by group
      simp only [LinearMap.comp_apply, MonoidHom.coe_comp, Function.comp_apply,
        Subgroup.coe_subtype]
      calc
        Coinvariants.mk _ (symbolRep R w g (symbolRep R w h x)) =
            Coinvariants.mk _ (symbolRep R w (g * h) x) := by
              rw [map_mul, Module.End.mul_apply]
        _ = Coinvariants.mk _ (symbolRep R w ((g * h * g⁻¹) * g) x) := by
              simp only [Subgroup.coe_inv]
              rw [← heq]
        _ = Coinvariants.mk _ (symbolRep R w (g * h * g⁻¹) (symbolRep R w g x)) := by
              rw [map_mul, Module.End.mul_apply]
        _ = Coinvariants.mk _ (symbolRep R w g x) :=
          Coinvariants.mk_self_apply _ (⟨_, hc⟩ : Gamma1 N) _

/-- On a coinvariant class, `gamma0Symbol` applies the representative to the class. -/
@[simp]
private theorem gamma0Symbol_mk (g : ↥(Gamma0 N))
    (x : degreeZero R ⊗[R] homogeneousSubmodule (Fin 2) R w) :
    gamma0Symbol g (Coinvariants.mk _ x) =
      Coinvariants.mk _ (symbolRep R w (g : SL(2, ℤ)) x) :=
  Coinvariants.lift_mk _ _ _ x

/-- A representative in `Γ₀(N)` sends a modular symbol to the symbol with translated
endpoints and the inverse matrix action on its binary form. -/
private theorem gamma0Symbol_symbol (g : ↥(Gamma0 N)) (α β : OnePoint ℚ)
    (P : homogeneousSubmodule (Fin 2) R w) :
    gamma0Symbol g (symbol (Gamma1 N) α β P) =
      symbol (Gamma1 N) (mapGL ℚ (g : SL(2, ℤ)) • α)
        (mapGL ℚ (g : SL(2, ℤ)) • β)
        (binaryFormSLRep R w (g : SL(2, ℤ)) P) := by
  rw [symbol_apply, gamma0Symbol_mk, symbolRep_tmul, symbol_apply]
  congr 1
  congr 1
  ext1
  simp

/-- The action of the identity of `Γ₀(N)` is the identity on modular symbols. -/
@[simp]
private theorem gamma0Symbol_one :
    gamma0Symbol (R := R) (w := w) (N := N) 1 = 1 := by
  apply Coinvariants.hom_ext
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply]
  rw [gamma0Symbol_mk]
  simp

/-- The `Γ₀(N)`-action on modular symbols respects multiplication. -/
private theorem gamma0Symbol_mul (g h : ↥(Gamma0 N)) :
    gamma0Symbol (R := R) (w := w) (g * h) =
      gamma0Symbol g * gamma0Symbol h := by
  apply Coinvariants.hom_ext
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply]
  rw [gamma0Symbol_mk, Module.End.mul_apply, gamma0Symbol_mk, gamma0Symbol_mk]
  simp [map_mul, Module.End.mul_apply]

/-- Elements of `Γ₁(N)` act trivially on its modular symbols. -/
private theorem gamma0Symbol_eq_one (g : ↥(Gamma0 N)) (hg : (g : SL(2, ℤ)) ∈ Gamma1 N) :
    gamma0Symbol (R := R) (w := w) g = 1 := by
  apply Coinvariants.hom_ext
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply]
  rw [gamma0Symbol_mk]
  simpa using Coinvariants.mk_self_apply
    ((symbolRep R w).comp (Gamma1 N).subtype) (⟨g, hg⟩ : Gamma1 N) x

/-- Representatives with the same lower-right entry induce the same action. -/
private theorem gamma0Symbol_eq_of_Gamma0Map_eq (g h : ↥(Gamma0 N))
    (heq : (Gamma0Map N).toHomUnits g = (Gamma0Map N).toHomUnits h) :
    gamma0Symbol (R := R) (w := w) g = gamma0Symbol h := by
  have hmem : ((g : SL(2, ℤ)) * (h : SL(2, ℤ))⁻¹) ∈ Gamma1 N :=
    mul_inv_mem_Gamma1_of_Gamma0Map_eq g h (congrArg Units.val heq)
  have hgh : gamma0Symbol (R := R) (w := w) (g * h⁻¹) = 1 :=
    gamma0Symbol_eq_one (g * h⁻¹) (by simpa using hmem)
  have hmul := gamma0Symbol_mul (R := R) (w := w) (g * h⁻¹) h
  simpa [hgh] using hmul

/-- The diamond operator `⟨d⟩` on modular symbols at level `Γ₁(N)`. -/
noncomputable def diamondOp (d : (ZMod N)ˣ) :
    Module.End R (ModularSymbols R (Gamma1 N) w) :=
  gamma0Symbol (Gamma0Map_toHomUnits_surjective d).choose

/-- Any representative of `d` computes the diamond operator. -/
private theorem diamondOp_eq_gamma0Symbol (d : (ZMod N)ˣ) (g : ↥(Gamma0 N))
    (hg : (Gamma0Map N).toHomUnits g = d) :
    diamondOp (R := R) (w := w) d = gamma0Symbol g := by
  apply gamma0Symbol_eq_of_Gamma0Map_eq
  exact (Gamma0Map_toHomUnits_surjective d).choose_spec.trans hg.symm

/-- The diamond operator on a coinvariant class. -/
theorem diamondOp_mk (d : (ZMod N)ˣ) (g : ↥(Gamma0 N))
    (hg : (Gamma0Map N).toHomUnits g = d)
    (x : degreeZero R ⊗[R] homogeneousSubmodule (Fin 2) R w) :
    diamondOp d (Coinvariants.mk _ x) =
      Coinvariants.mk _ (symbolRep R w (g : SL(2, ℤ)) x) := by
  rw [diamondOp_eq_gamma0Symbol d g hg, gamma0Symbol_mk]

/-- On symbols, `⟨d⟩` translates both endpoints by a representative of `d` and acts on
the binary form by its inverse. -/
theorem diamondOp_symbol (d : (ZMod N)ˣ) (g : ↥(Gamma0 N))
    (hg : (Gamma0Map N).toHomUnits g = d) (α β : OnePoint ℚ)
    (P : homogeneousSubmodule (Fin 2) R w) :
    diamondOp d (symbol (Gamma1 N) α β P) =
      symbol (Gamma1 N) (mapGL ℚ (g : SL(2, ℤ)) • α)
        (mapGL ℚ (g : SL(2, ℤ)) • β)
        (binaryFormSLRep R w (g : SL(2, ℤ)) P) := by
  rw [diamondOp_eq_gamma0Symbol d g hg, gamma0Symbol_symbol]

/-- The identity diamond acts as the identity. -/
@[simp]
theorem diamondOp_one : diamondOp (R := R) (w := w) (N := N) 1 = 1 := by
  rw [diamondOp_eq_gamma0Symbol 1 1 (map_one _)]
  exact gamma0Symbol_one

/-- Diamond operators multiply according to their indices. -/
theorem diamondOp_mul (d e : (ZMod N)ˣ) :
    diamondOp (R := R) (w := w) (d * e) =
      diamondOp d * diamondOp e := by
  obtain ⟨g, hg⟩ := Gamma0Map_toHomUnits_surjective (N := N) d
  obtain ⟨h, hh⟩ := Gamma0Map_toHomUnits_surjective (N := N) e
  rw [diamondOp_eq_gamma0Symbol (d * e) (g * h) (by simp [map_mul, hg, hh]),
    diamondOp_eq_gamma0Symbol d g hg, diamondOp_eq_gamma0Symbol e h hh]
  exact gamma0Symbol_mul g h

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

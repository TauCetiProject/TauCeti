/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.ModularSymbols.Basic

/-!
# Modular symbols with values in a representation

Let `Δ₀ = Div⁰(ℙ¹(ℚ))` be the integral degree-zero divisors on the cusps
(`TauCeti.ModularSymbols.degreeZero ℤ`), on which `GL(2, ℚ)` acts by Möbius transformations. For a
subgroup `Γ ≤ SL(2, ℤ)` and a representation `ρ` of `Γ` on an `R`-module `V`, the
**`V`-valued modular symbols** for `Γ` are the `Γ`-equivariant additive maps
`Symb_Γ(V) = Hom_{ℤ[Γ]}(Δ₀, V)`, that is, the additive maps `φ : Δ₀ → V` with
`φ(γ D) = ρ(γ) (φ D)` for all `γ ∈ Γ` and `D ∈ Δ₀`. When `ρ(γ) v = v ∣ γ⁻¹` comes from a right
action, this is the condition `φ(γ D) = φ(D) ∣ γ⁻¹` of Pollack–Stevens. They form an
`R`-submodule of the additive maps `Δ₀ →+ V`. The divisors stay integral while the coefficients
are over `R`, so this is not an instance of Mathlib's `Representation.IntertwiningMap` or of the
invariants of `Representation.linHom`, which take both sides over one ring.

This is the cohomological counterpart of the homological module of modular symbols
`TauCeti.ModularSymbols` (a module of coinvariants of `Δ₀ ⊗ V`): its symbols are functions on
paths between cusps, which is the form in which the period symbol of a cusp form, the boundary
map to group cohomology, and the overconvergent symbols of `p`-adic interpolation are written.

The divisor `{b} - {a}` with `+1` at `b` and `-1` at `a` is the oriented path from `a` to `b`
(`TauCeti.ModularSymbol.divisor a b`). The unimodular divisors `{g 0} - {g ∞}`, `g ∈ SL(2, ℤ)`,
span `Δ₀` by Manin's lemma, so an additive map on `Δ₀` is determined by its values on them, and a
modular symbol by its values on the unimodular divisors of a set of representatives of the right
cosets `Γ \ SL(2, ℤ)`. They satisfy the two-term and three-term Manin relations, from which
the module of modular symbols of the full modular group with trivial coefficients is zero.

## Main definitions

* `TauCeti.ModularSymbol.divisor a b`: the oriented divisor `{b} - {a}` of the path from `a` to
  `b`.
* `TauCeti.ModularSymbol.unimodularDivisor g`: the unimodular divisor `{g 0} - {g ∞}`.
* `TauCeti.ModularSymbol.symb ρ`: the `R`-module `Symb_Γ(V)` of `V`-valued modular symbols.

## Main results

* `TauCeti.ModularSymbol.divisor_add_divisor`, `TauCeti.ModularSymbol.degreeZeroGLRep_divisor`:
  paths compose additively and are moved by `GL(2, ℚ)`.
* `TauCeti.ModularSymbol.unimodularDivisor_mul_S`,
  `TauCeti.ModularSymbol.unimodularDivisor_add_mul_T_mul_S_add_mul_T_mul_S_sq`: the two-term and
  three-term Manin relations among unimodular divisors.
* `TauCeti.ModularSymbol.span_unimodularDivisor_eq_top`: the unimodular divisors span `Δ₀`.
* `TauCeti.ModularSymbol.addMonoidHom_ext`: an additive map on `Δ₀` is determined by its values on
  the unimodular divisors.
* `TauCeti.ModularSymbol.eq_of_forall_unimodularDivisor_eq`: a modular symbol is determined by its
  values on the unimodular divisors of representatives of `Γ \ SL(2, ℤ)`.
* `TauCeti.ModularSymbol.symb_le_symb_comp_inclusion`: for `Γ' ≤ Γ`, every `Γ`-symbol is a
  `Γ'`-symbol.
* `TauCeti.ModularSymbol.symb_trivial_eq_bot`: `Symb_{SL(2, ℤ)}(V) = 0` for the trivial action.

## References

* R. Pollack and G. Stevens, *Overconvergent modular symbols and `p`-adic `L`-functions*,
  Ann. Sci. Éc. Norm. Supér. (4) **44** (2011), 1–42, §§2.1–2.2.
* Y. I. Manin, *Parabolic points and zeta functions of modular curves*, Izv. Akad. Nauk SSSR
  Ser. Mat. **36** (1972), 19–66, §1.
-/

public section

open MonoidAlgebra Matrix.SpecialLinearGroup ModularGroup OnePoint
open scoped MatrixGroups

namespace TauCeti.ModularSymbol

open ModularSymbols

/-! ### Oriented cusp divisors -/

section Divisor

variable (R : Type*) [Ring R]

/-- The oriented divisor `{b} - {a}` of the path from the cusp `a` to the cusp `b`: the
degree-zero divisor with coefficient `1` at `b` and `-1` at `a`. -/
noncomputable def divisor (a b : OnePoint ℚ) : degreeZero R :=
  ⟨single b 1 - single a 1, single_sub_single_mem_degreeZero b a⟩

variable {R}

@[simp]
theorem coe_divisor (a b : OnePoint ℚ) :
    (divisor R a b : R[OnePoint ℚ]) = single b 1 - single a 1 :=
  (rfl)

/-- The constant path is the zero divisor. -/
@[simp]
theorem divisor_self (a : OnePoint ℚ) : divisor R a a = 0 := by
  ext1
  simp

/-- Reversing a path negates its divisor. -/
@[simp]
theorem neg_divisor (a b : OnePoint ℚ) : -divisor R a b = divisor R b a := by
  ext1
  simp

/-- Composing the path from `a` to `b` with the path from `b` to `c` gives the path from `a` to
`c`. -/
theorem divisor_add_divisor (a b c : OnePoint ℚ) :
    divisor R a b + divisor R b c = divisor R a c := by
  ext1
  simp only [Submodule.coe_add, coe_divisor]
  abel

/-- `GL(2, ℚ)` moves the path from `a` to `b` to the path from `g a` to `g b`. -/
@[simp]
theorem degreeZeroGLRep_divisor (g : GL (Fin 2) ℚ) (a b : OnePoint ℚ) :
    degreeZeroGLRep R g (divisor R a b) = divisor R (g • a) (g • b) := by
  ext1
  simp

variable (R) in
/-- The unimodular divisor `{g 0} - {g ∞}` of `g ∈ SL(2, ℤ)`: the divisor of the path from
`g ∞` to `g 0`, the translate by `g` of the path from `∞` to `0`. -/
noncomputable def unimodularDivisor (g : SL(2, ℤ)) : degreeZero R :=
  divisor R (mapGL ℚ g • ∞) (mapGL ℚ g • ((0 : ℚ) : OnePoint ℚ))

/-- The unimodular divisor of `g` is the divisor of the path from `g ∞` to `g 0`. -/
theorem unimodularDivisor_def (g : SL(2, ℤ)) :
    unimodularDivisor R g =
      divisor R (mapGL ℚ g • ∞) (mapGL ℚ g • ((0 : ℚ) : OnePoint ℚ)) :=
  (rfl)

/-- `SL(2, ℤ)` permutes the unimodular divisors by left multiplication. -/
@[simp]
theorem degreeZeroGLRep_mapGL_unimodularDivisor (h g : SL(2, ℤ)) :
    degreeZeroGLRep R (mapGL ℚ h) (unimodularDivisor R g) = unimodularDivisor R (h * g) := by
  simp [unimodularDivisor_def, mul_smul]

/-- The two-term Manin relation: right multiplication by `S` reverses the path. -/
@[simp]
theorem unimodularDivisor_mul_S (g : SL(2, ℤ)) :
    unimodularDivisor R (g * S) = -unimodularDivisor R g := by
  simp [unimodularDivisor_def, mul_smul]

/-- The unimodular divisor is unchanged when its matrix is multiplied by the central element
`-1`. -/
@[simp]
theorem unimodularDivisor_neg (g : SL(2, ℤ)) :
    unimodularDivisor R (-g) = unimodularDivisor R g := by
  have hg : -g = g * S * S := by rw [mul_assoc, S_mul_S_eq, mul_neg_one]
  rw [hg, unimodularDivisor_mul_S, unimodularDivisor_mul_S, neg_neg]

/-- The three-term Manin relation: the paths `g ∞ → g 0`, `g 0 → g 1` and `g 1 → g ∞` around
the ideal triangle with vertices `g 0`, `g 1`, `g ∞`, permuted cyclically by `T * S`, sum to
zero. -/
theorem unimodularDivisor_add_mul_T_mul_S_add_mul_T_mul_S_sq (g : SL(2, ℤ)) :
    unimodularDivisor R g + unimodularDivisor R (g * (T * S)) +
      unimodularDivisor R (g * (T * S) ^ 2) = 0 := by
  simp only [unimodularDivisor_def, map_mul, map_pow, mul_smul (mapGL ℚ g),
    mapGL_T_mul_S_smul_infty, mapGL_T_mul_S_smul_zero, mapGL_T_mul_S_sq_smul_infty,
    mapGL_T_mul_S_sq_smul_zero]
  rw [add_right_comm, divisor_add_divisor, divisor_add_divisor, divisor_self]

/-- **Manin's lemma.** The unimodular divisors `{g 0} - {g ∞}`, `g ∈ SL(2, ℤ)`, span the
degree-zero divisors on the cusps. -/
theorem span_unimodularDivisor_eq_top :
    Submodule.span R (Set.range (unimodularDivisor R)) = ⊤ := by
  refine eq_top_iff.2 (span_degreeZeroRep_eq_top.symm.le.trans
    (Submodule.span_le.2 (Set.range_subset_iff.2 fun g ↦ ?_)))
  have h : degreeZeroRep R g ⟨_, single_sub_single_mem_degreeZero ∞ ((0 : ℚ) : OnePoint ℚ)⟩ =
      -unimodularDivisor R g := by
    ext1
    simp [unimodularDivisor_def]
  rw [h]
  exact neg_mem (Submodule.subset_span ⟨g, rfl⟩)

end Divisor

/-! ### Modular symbols -/

section Symbol

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- An additive map on the degree-zero divisors is determined by its values on the unimodular
divisors `{g 0} - {g ∞}`, which span by Manin's lemma. -/
theorem addMonoidHom_ext {φ ψ : degreeZero ℤ →+ V}
    (h : ∀ g : SL(2, ℤ), φ (unimodularDivisor ℤ g) = ψ (unimodularDivisor ℤ g)) : φ = ψ :=
  AddMonoidHom.toIntLinearMap_injective (LinearMap.ext_on_range span_unimodularDivisor_eq_top h)

variable {Γ : Subgroup SL(2, ℤ)} (ρ : Representation R Γ V)

/-- **The module of `V`-valued modular symbols** `Symb_Γ(V) = Hom_{ℤ[Γ]}(Δ₀, V)` for a
representation `ρ` of a subgroup `Γ ≤ SL(2, ℤ)` on `V`: the additive maps `φ` on the integral
degree-zero divisors on the cusps with `φ(γ D) = ρ(γ) (φ D)` for every `γ ∈ Γ`, where `Γ` acts on
the divisors by Möbius transformations. They form an `R`-submodule of the additive maps. -/
def symb : Submodule R (degreeZero ℤ →+ V) where
  carrier := {φ | ∀ (γ : Γ) (D : degreeZero ℤ), φ (degreeZeroRep ℤ (γ : SL(2, ℤ)) D) = ρ γ (φ D)}
  add_mem' {φ ψ} hφ hψ γ D := by
    simp only [AddMonoidHom.add_apply, hφ γ D, hψ γ D, map_add]
  zero_mem' γ D := by simp
  smul_mem' a φ hφ γ D := by
    simp only [AddMonoidHom.smul_apply, hφ γ D, _root_.map_smul]

variable {ρ}

theorem mem_symb_iff {φ : degreeZero ℤ →+ V} :
    φ ∈ symb ρ ↔
      ∀ (γ : Γ) (D : degreeZero ℤ), φ (degreeZeroRep ℤ (γ : SL(2, ℤ)) D) = ρ γ (φ D) :=
  Iff.rfl

/-- The equivariance of a modular symbol: `φ(γ D) = ρ(γ) (φ D)`. -/
theorem apply_degreeZeroRep {φ : degreeZero ℤ →+ V} (hφ : φ ∈ symb ρ) (γ : Γ)
    (D : degreeZero ℤ) : φ (degreeZeroRep ℤ (γ : SL(2, ℤ)) D) = ρ γ (φ D) :=
  hφ γ D

/-- The value of a modular symbol on the translate by `γ ∈ Γ` of the path from `a` to `b`. -/
theorem apply_divisor_smul {φ : degreeZero ℤ →+ V} (hφ : φ ∈ symb ρ) (γ : Γ)
    (a b : OnePoint ℚ) :
    φ (divisor ℤ (mapGL ℚ (γ : SL(2, ℤ)) • a) (mapGL ℚ (γ : SL(2, ℤ)) • b)) =
      ρ γ (φ (divisor ℤ a b)) := by
  rw [← apply_degreeZeroRep hφ, degreeZeroRep_apply, degreeZeroGLRep_divisor]

/-- The value of a modular symbol on the unimodular divisor of `γ g`, for `γ ∈ Γ`. -/
theorem apply_unimodularDivisor_mul {φ : degreeZero ℤ →+ V} (hφ : φ ∈ symb ρ) (γ : Γ)
    (g : SL(2, ℤ)) :
    φ (unimodularDivisor ℤ ((γ : SL(2, ℤ)) * g)) = ρ γ (φ (unimodularDivisor ℤ g)) := by
  rw [← apply_degreeZeroRep hφ, degreeZeroRep_apply, degreeZeroGLRep_mapGL_unimodularDivisor]

/-- A modular symbol for `Γ` is determined by its values on the unimodular divisors
`{t 0} - {t ∞}` for `t` running over a set `s` meeting every right coset `Γ g` of `SL(2, ℤ)`. -/
theorem eq_of_forall_unimodularDivisor_eq {s : Set SL(2, ℤ)}
    (hs : ∀ g : SL(2, ℤ), ∃ γ ∈ Γ, ∃ t ∈ s, γ * t = g) {φ ψ : degreeZero ℤ →+ V}
    (hφ : φ ∈ symb ρ) (hψ : ψ ∈ symb ρ)
    (h : ∀ t ∈ s, φ (unimodularDivisor ℤ t) = ψ (unimodularDivisor ℤ t)) : φ = ψ := by
  refine addMonoidHom_ext fun g ↦ ?_
  obtain ⟨γ, hγ, t, ht, rfl⟩ := hs g
  rw [apply_unimodularDivisor_mul hφ ⟨γ, hγ⟩, apply_unimodularDivisor_mul hψ ⟨γ, hγ⟩, h t ht]

/-- For a subgroup `Γ' ≤ Γ`, every modular symbol for `Γ` is a modular symbol for `Γ'`, with the
restricted representation. -/
theorem symb_le_symb_comp_inclusion {Γ' : Subgroup SL(2, ℤ)} (h : Γ' ≤ Γ) :
    symb ρ ≤ symb (ρ.comp (Subgroup.inclusion h)) :=
  fun _ hφ γ D ↦ hφ (Subgroup.inclusion h γ) D

variable (R V) in
/-- The modular symbols of the full modular group `SL(2, ℤ)` with values in a trivial
representation vanish: the value `v` on `{0} - {∞}` satisfies `2 v = 0` by the two-term Manin
relation and `3 v = 0` by the three-term one, and it determines the symbol. -/
theorem symb_trivial_eq_bot :
    symb (Representation.trivial R (⊤ : Subgroup SL(2, ℤ)) V) = ⊥ := by
  refine eq_bot_iff.2 fun φ hφ ↦ (Submodule.mem_bot R).2 ?_
  -- Every unimodular divisor has the same value as `{0} - {∞}`.
  have hconst (g : SL(2, ℤ)) : φ (unimodularDivisor ℤ g) = φ (unimodularDivisor ℤ 1) := by
    simpa using apply_unimodularDivisor_mul hφ ⟨g, Subgroup.mem_top g⟩ 1
  have hv : φ (unimodularDivisor ℤ 1) = 0 := by
    -- `2 v = 0` from the two-term relation.
    have h2 := hconst S
    rw [← one_mul S, unimodularDivisor_mul_S, map_neg, neg_eq_iff_add_eq_zero] at h2
    -- `3 v = 0` from the three-term relation.
    have h3 := congrArg φ (unimodularDivisor_add_mul_T_mul_S_add_mul_T_mul_S_sq (R := ℤ) 1)
    rwa [map_add, map_add, map_zero, hconst (1 * (T * S)), hconst (1 * (T * S) ^ 2), h2,
      zero_add] at h3
  exact addMonoidHom_ext fun g ↦ by rw [hconst, hv, AddMonoidHom.zero_apply]

end Symbol

end TauCeti.ModularSymbol

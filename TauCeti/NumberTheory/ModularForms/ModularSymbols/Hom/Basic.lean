/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.ModularSymbols.Basic

/-!
# Modular symbols as equivariant maps on degree-zero cusp divisors

Let `Γ ≤ SL(2, ℤ)` be a subgroup, `R` a commutative semiring and `V` an `R`-module with an
`R`-linear representation `ρ` of `Γ`. The `V`-valued **modular symbols** for `Γ` are the
equivariant maps
`Symb_Γ(V) = Hom_{ℤ[Γ]}(Δ₀, V)`,
from the integral degree-zero divisors `Δ₀ = Div⁰(ℙ¹(ℚ))` on the cusps: the additive maps
`φ : Δ₀ → V` with `φ(γ D) = ρ(γ) φ(D)` for `γ ∈ Γ`, where `Γ` acts on `Δ₀` through
`SL(2, ℤ) → GL(2, ℚ)` and the Möbius action on the cusps. Writing the right action on `V` as
`v ∣ γ = ρ(γ⁻¹) v`, the condition reads `φ(γ D) = φ(D) ∣ γ⁻¹`.

This is the cohomological counterpart of the homological module `TauCeti.ModularSymbols`
(coinvariants of `Div⁰ ⊗ Sym^w`). The divisor module stays over `ℤ` whatever the coefficients,
so `Symb_Γ(V)` is an `R`-submodule of the additive maps `Δ₀ →+ V` with pointwise scalar
multiplication; its additive view, obtained by forgetting scalars, depends only on the underlying
action (`TauCeti.ModularSymbol.toAddSubmonoid_symb_eq_toAddSubmonoid_symb`).

A divisor is written as an oriented path: `TauCeti.ModularSymbol.divisor a b` is `{b} - {a}`,
the path from `a` to `b`. The unimodular paths from `g ∞` to `g 0`, for `g ∈ SL(2, ℤ)`, span
`Δ₀` (Manin's lemma, `TauCeti.ModularSymbols.span_degreeZeroRep_eq_top`), so a modular symbol is
determined by its values on them, and even on those for `g` running over representatives of the
right cosets `Γ \ SL(2, ℤ)`.

## Main definitions

* `TauCeti.ModularSymbol.divisor a b`: the oriented cusp divisor `{b} - {a}` in `Div⁰(ℙ¹(ℚ))`.
* `TauCeti.ModularSymbol.symb ρ`: the `R`-module `Symb_Γ(V)` of `V`-valued modular symbols.

## Main results

* `TauCeti.ModularSymbol.divisor_add_divisor`, `TauCeti.ModularSymbol.neg_divisor`,
  `TauCeti.ModularSymbol.degreeZeroGLRep_divisor`: paths compose, reverse and are moved by
  `GL(2, ℚ)` through their endpoints.
* `TauCeti.ModularSymbol.span_divisor_unimodular`: the unimodular paths `g ∞ → g 0` span `Δ₀`.
* `TauCeti.ModularSymbol.addMonoidHom_ext_unimodular`: an additive map on `Δ₀` is determined by
  its values on the unimodular paths.
* `TauCeti.ModularSymbol.mem_symb_iff_divisor`: the equivariance of a modular symbol may be
  checked on paths, `φ({γ b} - {γ a}) = ρ(γ) φ({b} - {a})`.
* `TauCeti.ModularSymbol.ext_of_coset_reps`: a modular symbol is determined by its values on the
  unimodular paths of a set of representatives of `Γ \ SL(2, ℤ)`.
* `TauCeti.ModularSymbol.symb_le_symb_comp_inclusion`: a `Γ`-symbol is a `Γ'`-symbol for
  `Γ' ≤ Γ`.
* `TauCeti.ModularSymbol.symb_trivial_eq_bot`: there are no nonzero modular symbols for
  `SL(2, ℤ)` with trivial coefficients, since `S` reverses the path `∞ → 0` and `TS` permutes the
  sides of the triangle `∞, 0, 1`.

## References

* R. Pollack and G. Stevens, *Overconvergent modular symbols and p-adic L-functions*,
  Ann. Sci. Éc. Norm. Supér. (4) **44** (2011), 1–42, §2.1.
* Y. I. Manin, *Parabolic points and zeta functions of modular curves*, Izv. Akad. Nauk SSSR
  Ser. Mat. **36** (1972), 19–66, §1.
-/

public noncomputable section

open Matrix.SpecialLinearGroup ModularGroup OnePoint MonoidAlgebra
open TauCeti.ModularSymbols
open scoped MatrixGroups

namespace TauCeti.ModularSymbol

/-! ### Oriented cusp divisors -/

section Divisor

variable {R : Type*} [Ring R]

/-- The oriented cusp divisor `{b} - {a}` in `Div⁰(ℙ¹(ℚ))`: the path from the cusp `a` to the
cusp `b`. -/
def divisor (a b : OnePoint ℚ) : degreeZero R :=
  ⟨single b 1 - single a 1, single_sub_single_mem_degreeZero b a⟩

@[simp]
theorem coe_divisor (a b : OnePoint ℚ) :
    ((divisor a b : degreeZero R) : R[OnePoint ℚ]) = single b 1 - single a 1 := by
  unfold divisor
  rfl

/-- The constant path is zero. -/
@[simp]
theorem divisor_self (a : OnePoint ℚ) : (divisor a a : degreeZero R) = 0 := by
  ext1
  simp

/-- Reversing a path negates it. -/
@[simp]
theorem neg_divisor (a b : OnePoint ℚ) : -(divisor a b : degreeZero R) = divisor b a := by
  ext1
  simp

/-- Composing the paths `a → b` and `b → c` gives the path `a → c`. -/
@[simp]
theorem divisor_add_divisor (a b c : OnePoint ℚ) :
    (divisor a b : degreeZero R) + divisor b c = divisor a c := by
  ext1
  simp only [Submodule.coe_add, coe_divisor]
  abel

/-- `GL(2, ℚ)` moves a path through its endpoints. -/
@[simp]
theorem degreeZeroGLRep_divisor (g : GL (Fin 2) ℚ) (a b : OnePoint ℚ) :
    degreeZeroGLRep R g (divisor a b) = divisor (g • a) (g • b) :=
  degreeZeroGLRep_single_sub_single g b a

/-- **Manin's lemma** for paths: the unimodular paths `g ∞ → g 0`, that is the divisors
`{g 0} - {g ∞}` for `g ∈ SL(2, ℤ)`, span `Div⁰(ℙ¹(ℚ))`. -/
theorem span_divisor_unimodular :
    Submodule.span R (Set.range fun g : SL(2, ℤ) ↦
      (divisor (mapGL ℚ g • ∞) (mapGL ℚ g • ((0 : ℚ) : OnePoint ℚ)) : degreeZero R)) = ⊤ := by
  refine eq_top_iff.2 (span_degreeZeroRep_eq_top.symm.le.trans (Submodule.span_mono ?_))
  -- The translate of `{∞} - {0}` by `g` is the unimodular path of `g S`.
  rintro _ ⟨g, rfl⟩
  refine ⟨g * S, ?_⟩
  ext1
  simp [mul_smul, mapGL_S_smul_infty, mapGL_S_smul_zero]

/-- An additive map on the integral divisors `Div⁰(ℙ¹(ℚ))` is determined by its values on the
unimodular paths `g ∞ → g 0`, `g ∈ SL(2, ℤ)`. -/
theorem addMonoidHom_ext_unimodular {V : Type*} [AddMonoid V] {φ ψ : degreeZero ℤ →+ V}
    (h : ∀ g : SL(2, ℤ), φ (divisor (mapGL ℚ g • ∞) (mapGL ℚ g • ((0 : ℚ) : OnePoint ℚ))) =
      ψ (divisor (mapGL ℚ g • ∞) (mapGL ℚ g • ((0 : ℚ) : OnePoint ℚ)))) :
    φ = ψ := by
  refine AddMonoidHom.eq_of_eqOn_dense ?_ (Set.forall_mem_range.2 h)
  rw [← Submodule.span_int_eq_addSubgroupClosure, span_divisor_unimodular,
    Submodule.top_toAddSubgroup]

end Divisor

/-! ### Modular symbols -/

section Symb

variable {R V : Type*} [CommSemiring R] [AddCommMonoid V] [Module R V] {Γ : Subgroup SL(2, ℤ)}

/-- The `R`-module `Symb_Γ(V) = Hom_{ℤ[Γ]}(Δ₀, V)` of **modular symbols** for `Γ ≤ SL(2, ℤ)` with
values in a representation `ρ` of `Γ` on `V`: the additive maps `φ` on the integral degree-zero
cusp divisors `Δ₀ = Div⁰(ℙ¹(ℚ))` with `φ(γ D) = ρ(γ) φ(D)` for all `γ ∈ Γ`, where `Γ` acts on
`Δ₀` through `GL(2, ℚ)`. It is a submodule of `Δ₀ →+ V` with pointwise scalar multiplication.

The divisors are taken over `ℤ` for every coefficient ring `R`, so this is neither the module of
invariants of `Representation.linHom` nor `Representation.IntertwiningMap`, both of which require
the source and target over the same ring. -/
def symb (ρ : Representation R Γ V) : Submodule R (degreeZero ℤ →+ V) where
  carrier := {φ | ∀ (γ : Γ) (D : degreeZero ℤ),
    φ (degreeZeroGLRep ℤ (mapGL ℚ (γ : SL(2, ℤ))) D) = ρ γ (φ D)}
  add_mem' {φ ψ} hφ hψ γ D := by simp [hφ γ D, hψ γ D]
  zero_mem' _ _ := by simp
  smul_mem' a φ hφ γ D := by simp [hφ γ D]

variable {ρ : Representation R Γ V}

/-- Membership in `Symb_Γ(V)`, unfolded: `φ(γ D) = ρ(γ) φ(D)` for all `γ ∈ Γ` and `D ∈ Δ₀`. -/
theorem mem_symb_iff {φ : degreeZero ℤ →+ V} :
    φ ∈ symb ρ ↔ ∀ (γ : Γ) (D : degreeZero ℤ),
      φ (degreeZeroGLRep ℤ (mapGL ℚ (γ : SL(2, ℤ))) D) = ρ γ (φ D) :=
  Iff.rfl

/-- The equivariance of a modular symbol: `φ(γ D) = ρ(γ) φ(D)`. -/
@[simp]
theorem apply_degreeZeroGLRep (φ : symb ρ) (γ : Γ) (D : degreeZero ℤ) :
    (φ : degreeZero ℤ →+ V) (degreeZeroGLRep ℤ (mapGL ℚ (γ : SL(2, ℤ))) D) =
      ρ γ ((φ : degreeZero ℤ →+ V) D) :=
  φ.property γ D

/-- The equivariance of a modular symbol on paths: `φ({γ b} - {γ a}) = ρ(γ) φ({b} - {a})`. -/
@[simp]
theorem apply_divisor_smul (φ : symb ρ) (γ : Γ) (a b : OnePoint ℚ) :
    (φ : degreeZero ℤ →+ V) (divisor (mapGL ℚ (γ : SL(2, ℤ)) • a) (mapGL ℚ (γ : SL(2, ℤ)) • b)) =
      ρ γ ((φ : degreeZero ℤ →+ V) (divisor a b)) := by
  rw [← apply_degreeZeroGLRep, degreeZeroGLRep_divisor]

/-- The equivariance of a modular symbol may be checked on paths: an additive map `φ` on `Δ₀` is
a modular symbol as soon as `φ({γ b} - {γ a}) = ρ(γ) φ({b} - {a})` for all `γ ∈ Γ` and cusps
`a`, `b`. -/
theorem mem_symb_iff_divisor {φ : degreeZero ℤ →+ V} :
    φ ∈ symb ρ ↔ ∀ (γ : Γ) (a b : OnePoint ℚ),
      φ (divisor (mapGL ℚ (γ : SL(2, ℤ)) • a) (mapGL ℚ (γ : SL(2, ℤ)) • b)) =
        ρ γ (φ (divisor a b)) := by
  refine ⟨fun hφ γ a b ↦ apply_divisor_smul ⟨φ, hφ⟩ γ a b, fun h γ ↦ ?_⟩
  -- Both sides of the equivariance are additive maps on `Δ₀` agreeing on the paths.
  have := addMonoidHom_ext_unimodular (V := V)
    (φ := φ.comp (degreeZeroGLRep ℤ (mapGL ℚ (γ : SL(2, ℤ)))).toAddMonoidHom)
    (ψ := (ρ γ).toAddMonoidHom.comp φ) fun g ↦ by simpa using h γ _ _
  exact fun D ↦ DFunLike.congr_fun this D

/-- **Modular symbols are determined by their values on coset representatives.** If every right
coset `Γ g` of `Γ` in `SL(2, ℤ)` meets the set `s`, then two modular symbols agreeing on the
unimodular paths `h ∞ → h 0` for `h ∈ s` are equal. -/
theorem ext_of_coset_reps {s : Set SL(2, ℤ)} (hs : ∀ g : SL(2, ℤ), ∃ h ∈ s, g * h⁻¹ ∈ Γ)
    {φ ψ : symb ρ}
    (h : ∀ h ∈ s,
      (φ : degreeZero ℤ →+ V) (divisor (mapGL ℚ h • ∞) (mapGL ℚ h • ((0 : ℚ) : OnePoint ℚ))) =
        (ψ : degreeZero ℤ →+ V)
          (divisor (mapGL ℚ h • ∞) (mapGL ℚ h • ((0 : ℚ) : OnePoint ℚ)))) :
    φ = ψ := by
  refine Subtype.ext (addMonoidHom_ext_unimodular fun g ↦ ?_)
  obtain ⟨k, hk, hgk⟩ := hs g
  -- Write `g = γ k` with `γ = g k⁻¹ ∈ Γ` and move `γ` out by equivariance.
  have hg : g = ((⟨g * k⁻¹, hgk⟩ : Γ) : SL(2, ℤ)) * k := by simp
  rw [hg, map_mul, mul_smul, mul_smul, apply_divisor_smul, apply_divisor_smul, h k hk]

/-- **Monotonicity.** For `Γ' ≤ Γ`, every modular symbol for `Γ` is a modular symbol for `Γ'`,
with the restricted representation. -/
theorem symb_le_symb_comp_inclusion {Γ' : Subgroup SL(2, ℤ)} (hΓ : Γ' ≤ Γ)
    (ρ : Representation R Γ V) : symb ρ ≤ symb (ρ.comp (Subgroup.inclusion hΓ)) :=
  fun _ hφ γ D ↦ hφ (Subgroup.inclusion hΓ γ) D

/-- Membership in `Symb_Γ(V)` depends only on the action of `Γ` on `V`, not on the scalars: two
representations of `Γ` on `V` over different semirings with the same underlying maps have the same
modular symbols, as an additive submonoid of `Δ₀ →+ V`. -/
theorem toAddSubmonoid_symb_eq_toAddSubmonoid_symb {S : Type*} [CommSemiring S] [Module S V]
    {σ : Representation S Γ V} (h : ∀ (γ : Γ) (v : V), ρ γ v = σ γ v) :
    (symb ρ).toAddSubmonoid = (symb σ).toAddSubmonoid := by
  ext φ
  simp only [Submodule.mem_toAddSubmonoid, mem_symb_iff, h]

/-- **There are no modular symbols for `SL(2, ℤ)` with trivial coefficients.** The value
`v = φ({0} - {∞})` of such a symbol satisfies `v + v = 0`, because `S` reverses the path `∞ → 0`,
and `v + v + v = 0`, because `TS` permutes the sides of the triangle with vertices `∞`, `0`
and `1`; so `v = 0`, and `v` determines `φ`. -/
theorem symb_trivial_eq_bot :
    symb (Representation.trivial R (⊤ : Subgroup SL(2, ℤ)) V) = ⊥ := by
  refine eq_bot_iff.2 fun φ hφ ↦ (Submodule.mem_bot R).2 ?_
  -- With trivial coefficients, `φ` is invariant under every translation of paths.
  have hinv (g : SL(2, ℤ)) (a b : OnePoint ℚ) :
      φ (divisor (mapGL ℚ g • a) (mapGL ℚ g • b)) = φ (divisor a b) :=
    mem_symb_iff_divisor.1 hφ ⟨g, Subgroup.mem_top g⟩ a b
  have hS := hinv S ∞ (0 : ℚ)
  rw [mapGL_S_smul_infty, mapGL_S_smul_zero] at hS
  have hU := hinv (T * S) ∞ (0 : ℚ)
  rw [map_mul, mapGL_T_mul_S_smul_infty, mapGL_T_mul_S_smul_zero] at hU
  have hU2 := hinv ((T * S) ^ 2) ∞ (0 : ℚ)
  rw [map_pow, map_mul, mapGL_T_mul_S_sq_smul_infty, mapGL_T_mul_S_sq_smul_zero] at hU2
  have h2 : φ (divisor ∞ ((0 : ℚ) : OnePoint ℚ) + divisor ((0 : ℚ) : OnePoint ℚ) ∞) = 0 := by
    rw [divisor_add_divisor, divisor_self, map_zero]
  have h3 : φ (divisor ∞ ((0 : ℚ) : OnePoint ℚ) + divisor ((0 : ℚ) : OnePoint ℚ) (1 : ℚ) +
      divisor ((1 : ℚ) : OnePoint ℚ) ∞) = 0 := by
    rw [divisor_add_divisor, divisor_add_divisor, divisor_self, map_zero]
  rw [map_add, hS] at h2
  rw [map_add, map_add, hU, hU2] at h3
  have hv : φ (divisor ∞ ((0 : ℚ) : OnePoint ℚ)) = 0 := by rw [← h3, add_assoc, h2, add_zero]
  refine addMonoidHom_ext_unimodular fun g ↦ ?_
  rw [hinv, AddMonoidHom.zero_apply]
  exact hv

end Symb

end TauCeti.ModularSymbol

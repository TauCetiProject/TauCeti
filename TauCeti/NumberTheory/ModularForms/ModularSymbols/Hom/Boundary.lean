/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.ModularSymbols.Hom.Basic

/-!
# Boundary symbols and Eisenstein symbols

Let `Γ ≤ SL(2, ℤ)` act on an `R`-module `V` through a representation `ρ`. The **boundary symbols**
`BSymb_Γ(V) = Hom_{ℤ[Γ]}(ℤ[ℙ¹(ℚ)], V)` are the `Γ`-equivariant functions on the cusps,
`ψ : ℙ¹(ℚ) → V` with `ψ(γ c) = ρ(γ) (ψ c)`. Extending such a function additively to all integral
divisors on the cusps and restricting to the degree-zero divisors `Δ₀` gives a modular symbol, with
value `ψ b - ψ a` on the path `{b} - {a}` from `a` to `b`. The image of this restriction map
`BSymb_Γ(V) → Symb_Γ(V)` is the module `Eis_Γ(V)` of **Eisenstein symbols**.

A function on the cusps restricts to zero on `Δ₀` exactly when it is constant, and a constant
function is a boundary symbol exactly when its value is `Γ`-invariant. So the sequence
`0 → V^Γ → BSymb_Γ(V) → Symb_Γ(V)` is exact, the first map sending `v` to the constant function
with value `v`. It is the beginning of the boundary exact sequence of modular symbols, which
continues with the connecting map `Symb_Γ(V) → H¹(Γ, V)` whose kernel is `Eis_Γ(V)`
(`TauCeti.NumberTheory.ModularForms.ModularSymbols.Hom.Cohomology`).

## Main definitions

* `TauCeti.ModularSymbol.restrictDivisor R ψ`: the additive map on `Δ₀` with value `ψ b - ψ a`
  on `{b} - {a}`, the restriction to `Δ₀` of the additive extension of `ψ : ℙ¹(ℚ) → V`.
* `TauCeti.ModularSymbol.bsymb ρ`: the `R`-module `BSymb_Γ(V)` of boundary symbols.
* `TauCeti.ModularSymbol.bsymbRes ρ`: the restriction map `BSymb_Γ(V) → Symb_Γ(V)`.
* `TauCeti.ModularSymbol.eis ρ`: the `R`-module `Eis_Γ(V)` of Eisenstein symbols.
* `TauCeti.ModularSymbol.bsymbConst ρ`: the map `V^Γ → BSymb_Γ(V)` to constant functions.

## Main results

* `TauCeti.ModularSymbol.restrictDivisor_divisor`: the value on the path from `a` to `b` is
  `ψ b - ψ a`.
* `TauCeti.ModularSymbol.restrictDivisor_eq_zero_iff`: a function restricts to zero on `Δ₀` iff
  it is constant.
* `TauCeti.ModularSymbol.eis_le_symb`: Eisenstein symbols are modular symbols, and
  `TauCeti.ModularSymbol.map_subtype_range_bsymbRes`: they are the image of the restriction map.
* `TauCeti.ModularSymbol.bsymbConst_injective` and
  `TauCeti.ModularSymbol.range_bsymbConst_eq_ker_bsymbRes`: exactness of
  `0 → V^Γ → BSymb_Γ(V) → Symb_Γ(V)`.

## References

* R. Pollack and G. Stevens, *Overconvergent modular symbols and `p`-adic `L`-functions*,
  Ann. Sci. Éc. Norm. Supér. (4) **44** (2011), 1–42, §2.1.
* G. Wiese, *Computational arithmetic of modular forms*, in *Notes from the International Autumn
  School on Computational Number Theory*, Tutor. Sch. Workshops Math. Sci., Birkhäuser, 2019,
  Definition 1.5 and Proposition 4.14 (boundary symbols).
-/

public section

open MonoidAlgebra Matrix.SpecialLinearGroup OnePoint Representation
open scoped MatrixGroups

namespace TauCeti.ModularSymbol

open ModularSymbols

/-! ### Boundary symbols -/

section AddCommMonoid

variable {R V : Type*} [Semiring R] [AddCommMonoid V] [Module R V] {Γ : Subgroup SL(2, ℤ)}
  (ρ : Representation R Γ V)

/-- **The module of boundary symbols** `BSymb_Γ(V) = Hom_{ℤ[Γ]}(ℤ[ℙ¹(ℚ)], V)` of a representation
`ρ` of a subgroup `Γ ≤ SL(2, ℤ)` on `V`: the functions `ψ` on the cusps `ℙ¹(ℚ)` with
`ψ(γ c) = ρ(γ) (ψ c)` for every `γ ∈ Γ`, where `Γ` acts on the cusps by Möbius transformations.
They form an `R`-submodule of the functions `ℙ¹(ℚ) → V`. -/
def bsymb : Submodule R (OnePoint ℚ → V) where
  carrier := {ψ | ∀ (γ : Γ) (c : OnePoint ℚ), ψ (mapGL ℚ (γ : SL(2, ℤ)) • c) = ρ γ (ψ c)}
  add_mem' {ψ χ} hψ hχ γ c := by simp [hψ γ c, hχ γ c]
  zero_mem' γ c := by simp
  smul_mem' a ψ hψ γ c := by simp [hψ γ c]

variable {ρ}

@[simp]
theorem mem_bsymb_iff {ψ : OnePoint ℚ → V} :
    ψ ∈ bsymb ρ ↔ ∀ (γ : Γ) (c : OnePoint ℚ), ψ (mapGL ℚ (γ : SL(2, ℤ)) • c) = ρ γ (ψ c) :=
  Iff.rfl

/-- The equivariance of a boundary symbol: `ψ(γ c) = ρ(γ) (ψ c)`. -/
theorem apply_mapGL_smul {ψ : OnePoint ℚ → V} (hψ : ψ ∈ bsymb ρ) (γ : Γ) (c : OnePoint ℚ) :
    ψ (mapGL ℚ (γ : SL(2, ℤ)) • c) = ρ γ (ψ c) :=
  hψ γ c

end AddCommMonoid

/-! ### Restriction of functions on the cusps to degree-zero divisors -/

section Restriction

variable {R V : Type*} [Semiring R] [AddCommGroup V] [Module R V]

variable (R) in
/-- The restriction to the integral degree-zero divisors `Δ₀` of the additive extension
`∑ n_c {c} ↦ ∑ n_c ψ(c)` of a function `ψ : ℙ¹(ℚ) → V` on the cusps. Its value on the path
`{b} - {a}` from `a` to `b` is `ψ b - ψ a` (`TauCeti.ModularSymbol.restrictDivisor_divisor`). It is
`R`-linear in `ψ`. -/
noncomputable def restrictDivisor : (OnePoint ℚ → V) →ₗ[R] (degreeZero ℤ →+ V) where
  toFun ψ :=
    { toFun D := Finsupp.linearCombination ℤ ψ (D : ℤ[OnePoint ℚ]).coeff
      map_zero' := by simp
      map_add' D E := by simp [coeff_add] }
  map_add' ψ χ := by
    ext D
    simp [Finsupp.linearCombination_apply, Finsupp.sum_add]
  map_smul' a ψ := by
    ext D
    simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, Finsupp.linearCombination_apply,
      Finsupp.sum, Pi.smul_apply, RingHom.id_apply, AddMonoidHom.smul_apply, Finset.smul_sum]
    exact Finset.sum_congr rfl fun c _ ↦ smul_comm _ _ _

/-- The restriction of `ψ` to `Δ₀` takes the value `ψ b - ψ a` on the path from `a` to `b`. -/
@[simp]
theorem restrictDivisor_divisor (ψ : OnePoint ℚ → V) (a b : OnePoint ℚ) :
    restrictDivisor R ψ (divisor ℤ a b) = ψ b - ψ a := by
  simp [restrictDivisor, coe_divisor, coeff_sub, coeff_single, Finsupp.linearCombination_single]

/-- A function on the cusps restricts to zero on the degree-zero divisors exactly when it is
constant. -/
theorem restrictDivisor_eq_zero_iff {ψ : OnePoint ℚ → V} :
    restrictDivisor R ψ = 0 ↔ ∃ v : V, ψ = Function.const _ v := by
  refine ⟨fun h ↦ ⟨ψ ∞, funext fun c ↦ ?_⟩, ?_⟩
  · simpa [sub_eq_zero] using DFunLike.congr_fun h (divisor ℤ ∞ c)
  · rintro ⟨v, rfl⟩
    exact addMonoidHom_ext_divisor fun a b ↦ by simp

/-- The restriction of a function on the cusps to `Δ₀` is a modular symbol as soon as the
function is `Γ`-equivariant. -/
theorem restrictDivisor_mem_symb {Γ : Subgroup SL(2, ℤ)} {ρ : Representation R Γ V}
    {ψ : OnePoint ℚ → V} (hψ : ∀ (γ : Γ) (c : OnePoint ℚ),
      ψ (mapGL ℚ (γ : SL(2, ℤ)) • c) = ρ γ (ψ c)) :
    restrictDivisor R ψ ∈ symb ρ :=
  mem_symb_iff_divisor.2 fun γ a b ↦ by simp [hψ, map_sub]

/-! ### Restriction of boundary symbols and Eisenstein symbols -/

variable {Γ : Subgroup SL(2, ℤ)} {ρ : Representation R Γ V}

variable (ρ)

/-- **The restriction map** `res : BSymb_Γ(V) → Symb_Γ(V)`, restricting the additive extension of a
boundary symbol to the degree-zero divisors. -/
noncomputable def bsymbRes : bsymb ρ →ₗ[R] symb ρ :=
  ((restrictDivisor R).comp (bsymb ρ).subtype).codRestrict (symb ρ) fun ψ ↦
    restrictDivisor_mem_symb ψ.property

@[simp]
theorem coe_bsymbRes (ψ : bsymb ρ) :
    (bsymbRes ρ ψ : degreeZero ℤ →+ V) = restrictDivisor R (ψ : OnePoint ℚ → V) :=
  (rfl)

/-- **The module of Eisenstein symbols** `Eis_Γ(V)`: the restrictions to the degree-zero divisors
of the boundary symbols. It is a submodule of the modular symbols
(`TauCeti.ModularSymbol.eis_le_symb`). -/
noncomputable def eis : Submodule R (degreeZero ℤ →+ V) :=
  (bsymb ρ).map (restrictDivisor R)

variable {ρ}

theorem mem_eis_iff {φ : degreeZero ℤ →+ V} :
    φ ∈ eis ρ ↔ ∃ ψ ∈ bsymb ρ, restrictDivisor R ψ = φ :=
  Submodule.mem_map

/-- The restriction of a boundary symbol is an Eisenstein symbol. -/
theorem restrictDivisor_mem_eis {ψ : OnePoint ℚ → V} (hψ : ψ ∈ bsymb ρ) :
    restrictDivisor R ψ ∈ eis ρ :=
  Submodule.mem_map_of_mem hψ

variable (ρ)

/-- Eisenstein symbols are modular symbols. -/
theorem eis_le_symb : eis ρ ≤ symb ρ :=
  Submodule.map_le_iff_le_comap.2 fun _ hψ ↦ restrictDivisor_mem_symb hψ

/-- The Eisenstein symbols are the image of the restriction map `BSymb_Γ(V) → Symb_Γ(V)`. -/
theorem map_subtype_range_bsymbRes :
    (LinearMap.range (bsymbRes ρ)).map (symb ρ).subtype = eis ρ := by
  rw [← LinearMap.range_comp, bsymbRes, LinearMap.subtype_comp_codRestrict, LinearMap.range_comp,
    Submodule.range_subtype, eis]

end Restriction

/-! ### Exactness at the invariants and at the boundary symbols -/

section CommRing

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] {Γ : Subgroup SL(2, ℤ)}
  {ρ : Representation R Γ V}

/-- A constant function on the cusps is a boundary symbol exactly when its value is
`Γ`-invariant. -/
theorem const_mem_bsymb_iff {v : V} : Function.const (OnePoint ℚ) v ∈ bsymb ρ ↔ v ∈ invariants ρ :=
  ⟨fun h γ ↦ (h γ ∞).symm, fun h γ _ ↦ (h γ).symm⟩

variable (ρ)

/-- **The map `V^Γ → BSymb_Γ(V)`** sending an invariant vector `v` to the constant function on the
cusps with value `v`. -/
def bsymbConst : invariants ρ →ₗ[R] bsymb ρ where
  toFun v := ⟨Function.const _ v, const_mem_bsymb_iff.2 v.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem coe_bsymbConst_apply (v : invariants ρ) (c : OnePoint ℚ) :
    (bsymbConst ρ v : OnePoint ℚ → V) c = v :=
  (rfl)

/-- The map `V^Γ → BSymb_Γ(V)` is injective. -/
theorem bsymbConst_injective : Function.Injective (bsymbConst ρ) := fun _ _ h ↦
  Subtype.ext (congr_fun (congrArg Subtype.val h) ∞)

/-- **Exactness of `V^Γ → BSymb_Γ(V) → Symb_Γ(V)`**: a boundary symbol restricts to zero on the
degree-zero divisors exactly when it is a constant function, whose value is then `Γ`-invariant. -/
theorem range_bsymbConst_eq_ker_bsymbRes :
    LinearMap.range (bsymbConst ρ) = LinearMap.ker (bsymbRes ρ) := by
  ext ψ
  simp only [LinearMap.mem_range, LinearMap.mem_ker]
  rw [← Subtype.coe_inj (b := (0 : symb ρ)), coe_bsymbRes, Submodule.coe_zero,
    restrictDivisor_eq_zero_iff]
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨v, rfl⟩
  · rintro ⟨v, hv⟩
    have hv' : v ∈ invariants ρ := const_mem_bsymb_iff.1 (hv ▸ ψ.property)
    exact ⟨⟨v, hv'⟩, Subtype.ext hv.symm⟩

end CommRing

end TauCeti.ModularSymbol

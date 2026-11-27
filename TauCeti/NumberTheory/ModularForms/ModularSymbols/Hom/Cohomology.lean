/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
public import TauCeti.NumberTheory.ModularForms.ModularSymbols.Hom.Boundary
import TauCeti.RepresentationTheory.Homological.GroupCohomology.Cocycle
import TauCeti.RepresentationTheory.Homological.GroupCohomology.Functoriality

/-!
# Modular symbols and the first group cohomology

Let `Γ ≤ SL(2, ℤ)` act on an `R`-module `V` through a representation `ρ`. A modular symbol
`φ ∈ Symb_Γ(V)` and a base cusp `x` give the function `γ ↦ φ({γ x} - {x})` on `Γ`, the value of
`φ` on the path from `x` to `γ x`. Additivity of `φ` on paths and its equivariance give the
cocycle identity `φ({γ η x} - {x}) = ρ(γ) φ({η x} - {x}) + φ({γ x} - {x})`, and moving the base
cusp from `x` to `y` changes the cocycle by the coboundary of `φ({y} - {x})`. So `φ` has a class
`δ(φ) ∈ H¹(Γ, V)` independent of the base cusp. Up to sign, `δ` is the connecting map of
`Hom_Γ(-, V)` on the sequence `0 → Δ₀ → ℤ[ℙ¹(ℚ)] → ℤ → 0`; it is built here from the explicit
cocycle, in Mathlib's degree-one group cohomology.

Together with the boundary symbols of
`TauCeti.NumberTheory.ModularForms.ModularSymbols.Hom.Boundary`, this gives the **boundary exact
sequence of modular symbols**
`0 → V^Γ → BSymb_Γ(V) → Symb_Γ(V) → H¹(Γ, V) → ∏_c H¹(Γ_c, V)`,
exact for every subgroup `Γ` and every representation `V`, with no invertibility hypothesis.
The last map is the product of the restrictions to the stabilisers `Γ_c` of the cusps `c`. Its
kernel, the classes vanishing on every cusp stabiliser, is parabolic cohomology; the sequence
identifies it with the image of `δ`, and identifies the kernel of `δ` with the Eisenstein symbols.

* The kernel of `δ` is `Eis_Γ(V)`: if `φ({γ x} - {x}) = ρ(γ) v - v`, then `c ↦ φ({c} - {x}) + v`
  is a boundary symbol restricting to `φ`.
* The image of `δ` is the kernel of the restrictions: moving the base point to a cusp `c` shows
  that `δ(φ)` vanishes on `Γ_c`; conversely, a cocycle that is a coboundary on every cusp
  stabiliser is the defect `F(γ c) - ρ(γ) F(c)` of a function `F` on the cusps
  (`groupCohomology.exists_forall_apply_smul_eq_iff`), and `F` restricts to a modular symbol
  with class `δ(F)` equal to the class of the cocycle.

Since the stabiliser of `γ c` is the conjugate of the stabiliser of `c`, it suffices to restrict
to one cusp in each `Γ`-orbit; the statement here quantifies over all cusps. Mathlib's group
cohomology takes the scalars and the coefficients in the universe of the group, so `R` and `V`
live in `Type` here.

## Main definitions

* `TauCeti.ModularSymbol.toCocycles₁ ρ x`: the cocycle `γ ↦ φ({γ x} - {x})` of a modular symbol,
  for a base cusp `x`.
* `TauCeti.ModularSymbol.toH1 ρ`: the map `δ : Symb_Γ(V) → H¹(Γ, V)`.
* `TauCeti.ModularSymbol.cuspStabilizer Γ c`: the stabiliser `Γ_c` of a cusp `c` in `Γ`.

## Main results

* `TauCeti.ModularSymbol.toH1_eq_H1π_toCocycles₁`: `δ(φ)` is the class of the cocycle at every
  base cusp.
* `TauCeti.ModularSymbol.toH1_eq_zero_iff` and `TauCeti.ModularSymbol.ker_toH1`: exactness at
  `Symb_Γ(V)`, the kernel of `δ` is `Eis_Γ(V)`.
* `TauCeti.ModularSymbol.toH1_comp_bsymbRes`: `δ ∘ res = 0`.
* `TauCeti.ModularSymbol.range_bsymbRes_eq_ker_toH1`: exactness of
  `BSymb_Γ(V) → Symb_Γ(V) → H¹(Γ, V)`, the image of `res` is the kernel of `δ`.
* `TauCeti.ModularSymbol.resNatTrans_app_toH1_eq_zero`: `δ(φ)` vanishes on every cusp stabiliser.
* `TauCeti.ModularSymbol.mem_range_toH1_iff`: exactness at `H¹(Γ, V)`, a class is in the image of
  `δ` iff it restricts to zero on every cusp stabiliser.

## References

* G. Wiese, *Computational arithmetic of modular forms*, in *Notes from the International Autumn
  School on Computational Number Theory*, Tutor. Sch. Workshops Math. Sci., Birkhäuser, 2019,
  Lemma 5.2, Proposition 4.14 and the proof of Proposition 6.7(a).
* R. Pollack and G. Stevens, *Overconvergent modular symbols and `p`-adic `L`-functions*,
  Ann. Sci. Éc. Norm. Supér. (4) **44** (2011), 1–42, §2.1.
-/

public section

open MonoidAlgebra Matrix.SpecialLinearGroup OnePoint Representation groupCohomology
open scoped MatrixGroups

namespace TauCeti.ModularSymbol

open ModularSymbols

variable {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] {Γ : Subgroup SL(2, ℤ)}

/-! ### The cocycle of a modular symbol -/

section Cocycle

variable (ρ : Representation R Γ V)

/-- **The cocycle of a modular symbol** at the base cusp `x`: the one-cocycle
`γ ↦ φ({γ x} - {x})` of `Γ` with values in `V`, the value of `φ` on the path from `x` to `γ x`.
Its class in `H¹(Γ, V)` does not depend on `x` (`TauCeti.ModularSymbol.toH1_eq_H1π_toCocycles₁`). -/
noncomputable def toCocycles₁ (x : OnePoint ℚ) : symb ρ →ₗ[R] cocycles₁ (Rep.of ρ) where
  toFun φ := ⟨fun γ ↦ (φ : degreeZero ℤ →+ V) (divisor ℤ x (mapGL ℚ (γ : SL(2, ℤ)) • x)), by
    refine (mem_cocycles₁_iff _).2 fun γ η ↦ ?_
    -- The path from `x` to `γ η x` passes through `γ x`, and its second leg is `γ` applied to
    -- the path from `x` to `η x`.
    rw [Subgroup.coe_mul, map_mul, mul_smul,
      ← divisor_add_divisor (R := ℤ) x (mapGL ℚ (γ : SL(2, ℤ)) • x), map_add,
      apply_divisor_smul φ.property, add_comm]⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable {ρ}

@[simp]
theorem toCocycles₁_apply (x : OnePoint ℚ) (φ : symb ρ) (γ : Γ) :
    toCocycles₁ ρ x φ γ = (φ : degreeZero ℤ →+ V) (divisor ℤ x (mapGL ℚ (γ : SL(2, ℤ)) • x)) :=
  (rfl)

/-- Moving the base cusp from `x` to `y` changes the cocycle of a modular symbol by the
coboundary of `φ({y} - {x})`. -/
theorem toCocycles₁_sub_toCocycles₁ (x y : OnePoint ℚ) (φ : symb ρ) :
    ⇑(toCocycles₁ ρ y φ) - ⇑(toCocycles₁ ρ x φ) = fun γ ↦
      ρ γ ((φ : degreeZero ℤ →+ V) (divisor ℤ x y)) - (φ : degreeZero ℤ →+ V) (divisor ℤ x y) := by
  funext γ
  -- `{γ y} - {y} = ({γ y} - {γ x}) + ({γ x} - {x}) + ({x} - {y})`.
  have h : divisor ℤ y (mapGL ℚ (γ : SL(2, ℤ)) • y) =
      divisor ℤ (mapGL ℚ (γ : SL(2, ℤ)) • x) (mapGL ℚ (γ : SL(2, ℤ)) • y) +
        divisor ℤ x (mapGL ℚ (γ : SL(2, ℤ)) • x) - divisor ℤ x y := by
    rw [sub_eq_add_neg, neg_divisor, add_comm (divisor ℤ _ _), divisor_add_divisor, add_comm,
      divisor_add_divisor]
  simp only [Pi.sub_apply, toCocycles₁_apply, h, map_sub, map_add, apply_divisor_smul φ.property]
  abel

end Cocycle

/-! ### The map to `H¹(Γ, V)` -/

section ToH1

variable (ρ : Representation R Γ V)

/-- **The map `δ : Symb_Γ(V) → H¹(Γ, V)`** sending a modular symbol `φ` to the class of the
cocycle `γ ↦ φ({γ x} - {x})`. The class does not depend on the base cusp `x`
(`TauCeti.ModularSymbol.toH1_eq_H1π_toCocycles₁`); the definition uses `x = ∞`. -/
noncomputable def toH1 : symb ρ →ₗ[R] H1 (Rep.of ρ) :=
  (H1π (Rep.of ρ)).hom ∘ₗ toCocycles₁ ρ ∞

variable {ρ}

/-- `δ(φ)` is the class of the cocycle `γ ↦ φ({γ x} - {x})` for every base cusp `x`. -/
theorem toH1_eq_H1π_toCocycles₁ (x : OnePoint ℚ) (φ : symb ρ) :
    toH1 ρ φ = H1π (Rep.of ρ) (toCocycles₁ ρ x φ) := by
  refine ((H1π_eq_iff _ _).2 ?_).symm
  rw [toCocycles₁_sub_toCocycles₁]
  exact ⟨_, funext fun γ ↦ d₀₁_hom_apply _ _ γ⟩

/-- **Exactness at `Symb_Γ(V)`**: a modular symbol has zero class in `H¹(Γ, V)` iff it is an
Eisenstein symbol. -/
theorem toH1_eq_zero_iff (φ : symb ρ) : toH1 ρ φ = 0 ↔ (φ : degreeZero ℤ →+ V) ∈ eis ρ := by
  rw [toH1_eq_H1π_toCocycles₁ ∞, H1π_eq_zero_iff, mem_eis_iff]
  constructor
  · -- If `φ({γ ∞} - {∞}) = ρ(γ) v - v`, then `c ↦ φ({c} - {∞}) + v` is a boundary symbol.
    rintro ⟨v, hv⟩
    have hv' (γ : Γ) : (φ : degreeZero ℤ →+ V) (divisor ℤ ∞ (mapGL ℚ (γ : SL(2, ℤ)) • ∞)) =
        ρ γ v - v := by
      rw [← toCocycles₁_apply, ← hv, d₀₁_hom_apply]
    refine ⟨fun c ↦ (φ : degreeZero ℤ →+ V) (divisor ℤ ∞ c) + v, mem_bsymb_iff.2 fun γ c ↦ ?_,
      addMonoidHom_ext_divisor fun a b ↦ ?_⟩
    · rw [← divisor_add_divisor (R := ℤ) ∞ (mapGL ℚ (γ : SL(2, ℤ)) • ∞), map_add,
        apply_divisor_smul φ.property, hv', map_add]
      abel
    · rw [restrictDivisor_divisor, ← divisor_add_divisor (R := ℤ) a ∞ b,
        ← neg_divisor (R := ℤ) ∞ a, map_add, map_neg]
      abel
  · -- The cocycle of the restriction of `ψ` is the coboundary of `ψ ∞`.
    rintro ⟨ψ, hψ, hφ⟩
    refine ⟨ψ ∞, funext fun γ ↦ ?_⟩
    rw [d₀₁_hom_apply, toCocycles₁_apply, ← hφ, restrictDivisor_divisor, apply_mapGL_smul hψ]

/-- **Exactness at `Symb_Γ(V)`**: the kernel of `δ : Symb_Γ(V) → H¹(Γ, V)` is `Eis_Γ(V)`. -/
theorem ker_toH1 : LinearMap.ker (toH1 ρ) = (eis ρ).comap (symb ρ).subtype := by
  ext φ
  exact toH1_eq_zero_iff φ

variable (ρ) in
/-- `δ ∘ res = 0`: the restriction of a boundary symbol has zero class in `H¹(Γ, V)`. -/
theorem toH1_comp_bsymbRes : toH1 ρ ∘ₗ bsymbRes ρ = 0 :=
  LinearMap.ext fun ψ ↦ (toH1_eq_zero_iff _).2 <| by
    rw [coe_bsymbRes]
    exact restrictDivisor_mem_eis ψ.property

variable (ρ) in
/-- **Exactness of `BSymb_Γ(V) → Symb_Γ(V) → H¹(Γ, V)`**: the image of the restriction map is the
kernel of `δ`. -/
theorem range_bsymbRes_eq_ker_toH1 : LinearMap.range (bsymbRes ρ) = LinearMap.ker (toH1 ρ) := by
  rw [ker_toH1, ← map_subtype_range_bsymbRes,
    Submodule.comap_map_eq_of_injective (symb ρ).injective_subtype]

end ToH1

/-! ### Restriction to the cusp stabilisers -/

section CuspStabilizer

/-- **The stabiliser `Γ_c` of a cusp** `c ∈ ℙ¹(ℚ)` in a subgroup `Γ ≤ SL(2, ℤ)`: the elements
of `Γ` fixing `c` under the Möbius action, as a subgroup of `Γ`. -/
def cuspStabilizer (Γ : Subgroup SL(2, ℤ)) (c : OnePoint ℚ) : Subgroup Γ :=
  (MulAction.stabilizer (GL (Fin 2) ℚ) c).comap ((mapGL ℚ).comp Γ.subtype)

@[simp]
theorem mem_cuspStabilizer_iff {c : OnePoint ℚ} {γ : Γ} :
    γ ∈ cuspStabilizer Γ c ↔ mapGL ℚ (γ : SL(2, ℤ)) • c = c :=
  Iff.rfl

variable {ρ : Representation R Γ V}

/-- The class `δ(φ)` restricts to zero on every cusp stabiliser `Γ_c`: with base cusp `c`, the
cocycle `γ ↦ φ({γ c} - {c})` vanishes on `Γ_c`. -/
theorem resNatTrans_app_toH1_eq_zero (c : OnePoint ℚ) (φ : symb ρ) :
    (resNatTrans R (cuspStabilizer Γ c).subtype 1).app (Rep.of ρ) (toH1 ρ φ) = 0 := by
  rw [toH1_eq_H1π_toCocycles₁ c, resNatTrans_app_H1π_eq_zero_iff]
  exact ⟨0, fun γ hγ ↦ by rw [toCocycles₁_apply, mem_cuspStabilizer_iff.1 hγ]; simp⟩

/-- **Exactness at `H¹(Γ, V)`** of the boundary exact sequence: a class in `H¹(Γ, V)` is `δ(φ)` for
a modular symbol `φ` iff it restricts to zero on the stabiliser `Γ_c` of every cusp `c`. A cocycle
that is a coboundary on every cusp stabiliser is the defect `F(γ c) - ρ(γ) F(c)` of a function `F`
on the cusps, and its class is `δ` of the restriction of `F` to the degree-zero divisors. -/
theorem mem_range_toH1_iff (y : H1 (Rep.of ρ)) :
    y ∈ LinearMap.range (toH1 ρ) ↔
      ∀ c : OnePoint ℚ, (resNatTrans R (cuspStabilizer Γ c).subtype 1).app (Rep.of ρ) y = 0 := by
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨φ, rfl⟩ c
    exact resNatTrans_app_toH1_eq_zero c φ
  induction y using H1_induction_on with | h f => ?_
  -- Integrate the cocycle along the action of `Γ` on the cusps through `mapGL ℚ`, whose
  -- stabilisers are the cusp stabilisers `Γ_c`.
  let : MulAction Γ (OnePoint ℚ) := MulAction.compHom _ ((mapGL ℚ).comp Γ.subtype)
  obtain ⟨F, hF⟩ := (exists_forall_apply_smul_eq_iff (X := OnePoint ℚ) f).2 fun c ↦ by
    obtain ⟨v, hv⟩ := (resNatTrans_app_H1π_eq_zero_iff _ f).1 (h c)
    exact ⟨v, fun γ hγ ↦ hv γ (by
      rw [MulAction.mem_stabilizer_iff, MulAction.compHom_smul_def] at hγ
      exact mem_cuspStabilizer_iff.2 hγ)⟩
  have hF' (γ : Γ) (c : OnePoint ℚ) :
      F (mapGL ℚ (γ : SL(2, ℤ)) • c) = ρ γ (F c) + f γ := by
    simpa only [MulAction.compHom_smul_def, MonoidHom.comp_apply, Subgroup.coe_subtype]
      using hF γ c
  -- The restriction of `F` to `Δ₀` is a modular symbol whose cocycle differs from `f` by the
  -- coboundary of `F ∞`.
  refine ⟨⟨restrictDivisor R F, mem_symb_iff_divisor.2 fun γ a b ↦ ?_⟩, ?_⟩
  · rw [restrictDivisor_divisor, restrictDivisor_divisor, hF', hF', map_sub]
    abel
  rw [toH1_eq_H1π_toCocycles₁ ∞, H1π_eq_iff]
  refine ⟨F ∞, funext fun γ ↦ ?_⟩
  rw [d₀₁_hom_apply, Pi.sub_apply, toCocycles₁_apply, restrictDivisor_divisor, hF']
  abel

end CuspStabilizer

end TauCeti.ModularSymbol

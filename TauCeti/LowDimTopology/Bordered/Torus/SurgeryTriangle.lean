/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.Bordered.Torus.TypeD
import TauCeti.Algebra.CharP.Two

/-!
# The surgery exact triangle of the solid-torus type `D` structures

The surgery exact triangle of Heegaard Floer homology relates the three-manifolds obtained by
filling a torus boundary along three slopes with pairwise intersection number one. In bordered
Floer homology Lipshitz, Ozsváth and Thurston deduce it from a statement about three type `D`
structures over the torus algebra, those of solid tori with framings `∞`, `-1` and `0`: the third
is homotopy equivalent to the mapping cone of a homomorphism from the first to the second. Pairing
with the type `A` module of the complement of a knot then turns the mapping cone of type `D`
structures into a mapping cone of chain complexes, whose long exact sequence is the exact
triangle. This file proves the statement about type `D` structures, over any ring `R` of
characteristic two.

The torus algebra and its chords `ρ₁, ρ₂, ρ₃, ρ₁₂, ρ₂₃, ρ₁₂₃` and idempotents `ι₀, ι₁` are those of
`TauCeti.LowDimTopology.Bordered.Torus.TypeD`; an arrow `x → y` labelled `a` means that `a ⊗ y` is
a term of `δ¹ x`. The three structures are

* `N_∞ = TauCeti.StrandsAlgebra.torusRho₂₃TypeD`, one generator `y` at `ι₁` with `y → y` labelled
  `ρ₂₃`;
* `N_{-1} = TauCeti.StrandsAlgebra.torusChainTypeD 0`, generators `x` at `ι₀` and `γ` at `ι₁` with
  `x → γ` labelled `ρ₁ + ρ₃`;
* `N_0 = TauCeti.StrandsAlgebra.torusRho₁₂TypeD`, one generator `a` at `ι₀` with `a → a` labelled
  `ρ₁₂`.

**The surgery map.** For every `n`, the map `TauCeti.StrandsAlgebra.torusSurgeryMap n` from `N_∞`
to the chain `torusChainTypeD n` of framing `-(n + 1)`, with generators `x` and `γ₀, …, γₙ`, is
`y ↦ ρ₂ ⊗ x + ∑ₗ ι₁ ⊗ γₗ`. It is a homomorphism
(`TauCeti.StrandsAlgebra.torusSurgeryMap_mem_morphisms`,
`TauCeti.StrandsAlgebra.morphismDifferential_torusSurgeryMap`): its differential from `y` to `γₗ`
has the term `ρ₂₃ ι₁` and one more term equal to `ρ₂₃`, either `ι₁ ρ₂₃` through `γₗ₊₁` or, for the
last generator, `ρ₂ ρ₃`, and the two cancel in characteristic two; the remaining products
`ρ₂₃ ρ₂` and `ρ₂ ρ₁` vanish. Its mapping cone is `TauCeti.StrandsAlgebra.torusSurgeryCone n`.

**The triangle `∞, -1, 0`.** For `n = 0` the cone has the generators `y, x, γ` and the arrows
`y → y` labelled `ρ₂₃`, `y → x` labelled `ρ₂`, `y → γ` labelled `ι₁` and `x → γ` labelled
`ρ₁ + ρ₃`. Cancelling the arrow `y → γ`, whose label is the idempotent, leaves the generator `x`
with the arrow `x → x` labelled `(ρ₁ + ρ₃) ρ₂ = ρ₁₂`, which is `N_0`. Accordingly the cone is
homotopy equivalent to `N_0`
(`TauCeti.StrandsAlgebra.exists_homotopyEquiv_torusRho₁₂TypeD_torusSurgeryCone_zero`), by the
morphisms

* `F : N_0 → cone`, `a ↦ (ρ₁ + ρ₃) ⊗ y + ι₀ ⊗ x`,
* `G : cone → N_0`, `x ↦ ι₀ ⊗ a`, `γ ↦ ρ₂ ⊗ a`, `y ↦ 0`,

with `F G = 1`, and the homotopy `H : γ ↦ ι₁ ⊗ y` with `∂H = G F + 1`, the inverse of the cancelled
arrow.

These are algebraic structures. Identifying them with the type `D` structures of the framed solid
tori defined by holomorphic curves, the homotopy equivalences for the other framings
`∞, -(n + 2), -(n + 1)`, between `torusSurgeryCone (n + 1)` and `torusChainTypeD n`, and the long
exact sequence obtained by pairing are not part of this file.

## Main definitions

* `TauCeti.StrandsAlgebra.torusSurgeryMap`: the homomorphism from `N_∞` to the chain
  `torusChainTypeD n`.
* `TauCeti.StrandsAlgebra.torusSurgeryCone`: its mapping cone.

## Main results

* `TauCeti.StrandsAlgebra.morphismDifferential_torusSurgeryMap`: the surgery map is a cycle.
* `TauCeti.StrandsAlgebra.exists_homotopyEquiv_torusRho₁₂TypeD_torusSurgeryCone_zero`: for `n = 0`
  its mapping cone is homotopy equivalent to `N_0`.

## References

* R. Lipshitz, P. S. Ozsváth and D. P. Thurston, *Bordered Heegaard Floer homology*, Mem. Amer.
  Math. Soc. **254** (2018), no. 1216, [arXiv:0810.0687](https://arxiv.org/abs/0810.0687),
  Chapter 11 (the type `D` structures of solid tori and the surgery exact triangle).
-/

public section

noncomputable section

namespace TauCeti

namespace StrandsAlgebra

open PointedMatchedCircle StrandDiagram

variable (R : Type*) [CommRing R]

/-- **The surgery map** of the solid-torus type `D` structures, from `N_∞ = torusRho₂₃TypeD` to the
chain `torusChainTypeD n`: it sends the generator `y` to `ρ₂ ⊗ x + ∑ₗ ι₁ ⊗ γₗ`, where `x = none`
and `γₗ = some l` are the generators of the chain. For `n = 0` its mapping cone
`torusSurgeryCone 0` is homotopy equivalent to `N_0 = torusRho₁₂TypeD`
(`TauCeti.StrandsAlgebra.exists_homotopyEquiv_torusRho₁₂TypeD_torusSurgeryCone_zero`). -/
def torusSurgeryMap (n : ℕ) :
    Matrix Unit (Option (Fin (n + 1))) (matchedSummand R genusOne.pair 1) :=
  Matrix.of fun _ ↦ fun
    | none => oneStrandChord R genusOne.pair (by decide : (1 : Fin 4) < 2)
    | some _ => oneStrandIdem R genusOne.pair (Set.rangeFactorization genusOne.pair 1)

@[simp]
theorem torusSurgeryMap_none (n : ℕ) (y : Unit) :
    torusSurgeryMap R n y none = oneStrandChord R genusOne.pair (by decide : (1 : Fin 4) < 2) :=
  (rfl)

@[simp]
theorem torusSurgeryMap_some (n : ℕ) (y : Unit) (l : Fin (n + 1)) :
    torusSurgeryMap R n y (some l) =
      oneStrandIdem R genusOne.pair (Set.rangeFactorization genusOne.pair 1) :=
  (rfl)

/-- The surgery map respects the idempotents: `ρ₂` runs from `ι₁` to `ι₀`. -/
theorem torusSurgeryMap_mem_morphisms (n : ℕ) :
    torusSurgeryMap R n ∈ (torusRho₂₃TypeD R).morphisms (torusChainTypeD R n) := by
  rw [TypeDStructure.mem_morphisms_iff]
  rintro - (_ | l) <;> simp [genusOne_pair_one, genusOne_pair_two]

/-- **The surgery map is a homomorphism**, over a ring of characteristic two. Its differential
from `y` to `γₗ` has the term `ρ₂₃ ι₁` and either the term `ι₁ ρ₂₃` through `γₗ₊₁` or, for the
last generator `γₙ`, the term `ρ₂ ρ₃`; these are all `ρ₂₃`, and the two terms cancel. The other
products `ρ₂₃ ρ₂` and `ρ₂ ρ₁` vanish. -/
theorem morphismDifferential_torusSurgeryMap [CharP R 2] (n : ℕ) :
    (torusRho₂₃TypeD R).morphismDifferential (torusChainTypeD R n) (torusSurgeryMap R n) = 0 := by
  refine Matrix.ext fun y x ↦ ?_
  simp only [TypeDStructure.morphismDifferential_apply, Matrix.add_apply, Matrix.mul_apply,
    Matrix.map_apply, matchedSummandDifferential_apply_of_le_one le_rfl, Fintype.sum_option,
    Fintype.sum_unique, Matrix.zero_apply]
  rcases x with _ | l
  · simp [oneStrandChord_mul_oneStrandChord_of_ne _ _ _ (by decide : (3 : Fin 4) ≠ 1)]
  · -- Only `γₗ₊₁` contributes to the sum over the generators of the chain.
    have hsum (a : ℕ) : ∑ m : Fin (n + 1), (if (m : ℕ) = a then
        oneStrandChord R genusOne.pair (by decide : (1 : Fin 4) < 3) else 0) =
        if a < n + 1 then oneStrandChord R genusOne.pair (by decide : (1 : Fin 4) < 3) else 0 := by
      rw [Fin.sum_univ_eq_sum_range (fun i ↦ if i = a then
        oneStrandChord R genusOne.pair (by decide : (1 : Fin 4) < 3) else 0), Finset.sum_ite_eq']
      simp only [Finset.mem_range]
    by_cases hl : l = Fin.last n
    · simp [hl, mul_add, hsum, genusOne_pair_one, genusOne_pair_three,
        add_self_eq_zero_of_charTwo R,
        oneStrandChord_mul_oneStrandChord_of_ne _ _ _ (by decide : (2 : Fin 4) ≠ 0)]
    · have : (l : ℕ) + 1 < n + 1 := by
        have := Fin.val_lt_last hl
        omega
      simp [hl, this, hsum, genusOne_pair_one, genusOne_pair_three,
        add_self_eq_zero_of_charTwo R,
        oneStrandChord_mul_oneStrandChord_of_ne _ _ _ (by decide : (2 : Fin 4) ≠ 0)]

/-- **The mapping cone of the surgery map** into `torusChainTypeD n`, the type `D` structure on the
generators `Unit ⊕ Option (Fin (n + 1))`, that is `y`, `x` and `γ₀, …, γₙ`, with the arrows of the
chain, `y → y` labelled `ρ₂₃`, `y → x` labelled `ρ₂` and `y → γₗ` labelled `ι₁` for every `l`. -/
abbrev torusSurgeryCone [CharP R 2] (n : ℕ) :
    TypeDStructure (matchedSummandDifferential R genusOne.pair 1) (oneStrandIdem R genusOne.pair)
      (Unit ⊕ Option (Fin (n + 1))) :=
  (torusRho₂₃TypeD R).cone (torusChainTypeD R n) (torusSurgeryMap R n)
    (torusSurgeryMap_mem_morphisms R n) (morphismDifferential_torusSurgeryMap R n)

/-- **The surgery exact triangle `∞, -1, 0` of the solid-torus type `D` structures.** Over a ring
of characteristic two, the type `D` structure `N_0 = torusRho₁₂TypeD` is homotopy equivalent to the
mapping cone `torusSurgeryCone 0` of the surgery map `torusSurgeryMap 0` from
`N_∞ = torusRho₂₃TypeD` to `N_{-1} = torusChainTypeD 0`. The morphisms are
`F a = (ρ₁ + ρ₃) ⊗ y + ι₀ ⊗ x` to the cone and `G x = ι₀ ⊗ a`, `G γ = ρ₂ ⊗ a`, `G y = 0` back; both
are cycles, `F G` is the identity, and the morphism `H` with the single coefficient `ι₁` from `γ`
to `y` satisfies `∂H = G F + 1`. -/
theorem exists_homotopyEquiv_torusRho₁₂TypeD_torusSurgeryCone_zero [CharP R 2] :
    ∃ F ∈ (torusRho₁₂TypeD R).morphisms (torusSurgeryCone R 0),
    ∃ G ∈ (torusSurgeryCone R 0).morphisms (torusRho₁₂TypeD R),
      (torusRho₁₂TypeD R).morphismDifferential (torusSurgeryCone R 0) F = 0 ∧
      (torusSurgeryCone R 0).morphismDifferential (torusRho₁₂TypeD R) G = 0 ∧
      F * G = (torusRho₁₂TypeD R).idMorphism ∧
      ∃ H ∈ (torusSurgeryCone R 0).morphisms (torusSurgeryCone R 0),
        (torusSurgeryCone R 0).morphismDifferential (torusSurgeryCone R 0) H =
          G * F + (torusSurgeryCone R 0).idMorphism := by
  refine ⟨Matrix.of fun _ ↦ Sum.elim
      (fun _ ↦ oneStrandChord R genusOne.pair (by decide : (0 : Fin 4) < 1) +
        oneStrandChord R genusOne.pair (by decide : (2 : Fin 4) < 3))
      fun
        | none => oneStrandIdem R genusOne.pair (Set.rangeFactorization genusOne.pair 0)
        | some _ => 0, ?memF,
    Matrix.of fun u _ ↦ match u with
      | .inl _ => 0
      | .inr none => oneStrandIdem R genusOne.pair (Set.rangeFactorization genusOne.pair 0)
      | .inr (some _) => oneStrandChord R genusOne.pair (by decide : (1 : Fin 4) < 2), ?memG,
    ?cycleF, ?cycleG, ?FG,
    Matrix.of fun u v ↦ match u, v with
      | .inr (some _), .inl _ =>
        oneStrandIdem R genusOne.pair (Set.rangeFactorization genusOne.pair 1)
      | _, _ => 0, ?memH, ?dH⟩
  -- `F`, `G` and `H` respect the idempotents, checked entrywise.
  case memF | memG | memH =>
    rw [TypeDStructure.mem_morphisms_iff]
    intro u v
    rcases u with u | (_ | l) <;> rcases v with v | (_ | l') <;> (try fin_cases l) <;>
      (try fin_cases l') <;> simp [mul_add, add_mul, genusOne_pair_zero, genusOne_pair_one,
        genusOne_pair_two, genusOne_pair_three]
  -- The cycle conditions, `F G = 1` and `∂H = G F + 1` are identities between explicit matrices
  -- over the torus algebra, checked entrywise. In `∂F = 0` the entry at `x` is
  -- `(ρ₁ + ρ₃) ρ₂ + ρ₁₂ = 0`; in `∂H = G F + 1` the entry from `γ` to `y` is `ρ₂ (ρ₁ + ρ₃) = ρ₂₃`,
  -- matching the term `ι₁ ρ₂₃` of `H δ`.
  case cycleF | cycleG | FG | dH =>
    refine Matrix.ext fun u v ↦ ?_
    simp only [TypeDStructure.morphismDifferential_apply, Matrix.add_apply, Matrix.mul_apply,
      Matrix.map_apply, matchedSummandDifferential_apply_of_le_one le_rfl, Fintype.sum_sum_type,
      Fintype.sum_option, Fintype.sum_unique, Matrix.zero_apply]
    rcases u with u | (_ | l) <;> rcases v with v | (_ | l') <;> (try fin_cases l) <;>
      (try fin_cases l') <;>
      simp [Fin.default_eq_zero, genusOne_pair_zero, genusOne_pair_one, genusOne_pair_two,
        genusOne_pair_three, add_self_eq_zero_of_charTwo R, mul_add, add_mul,
        oneStrandChord_mul_oneStrandChord_of_ne _ _ _ (by decide : (3 : Fin 4) ≠ 1),
        oneStrandChord_mul_oneStrandChord_of_ne _ _ _ (by decide : (2 : Fin 4) ≠ 0)]

end StrandsAlgebra

end TauCeti

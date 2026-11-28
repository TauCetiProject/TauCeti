/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.Bordered.PointedMatchedCircle
public import TauCeti.LowDimTopology.Bordered.StrandsAlgebra.Occupancy
public import TauCeti.LowDimTopology.Bordered.TypeD

/-!
# Type `D` structures over the torus algebra

The torus algebra is the summand `A(Z, 0)` with one strand of the algebra of the genus-one pointed
matched circle `Z`, whose points `0, 1, 2, 3` are matched as `{0, 2}` and `{1, 3}`
(`TauCeti.PointedMatchedCircle.genusOne`); it is `matchedSummand R genusOne.pair 1`, a differential
algebra with the restricted differential `matchedSummandDifferential R genusOne.pair 1`, which
vanishes. Its idempotents are the `I({p})` of the matched pairs `p`
(`TauCeti.StrandsAlgebra.oneStrandIdem R genusOne.pair p`): `ι₀ = I({0, 2})` and `ι₁ = I({1, 3})`.
Its chords (`TauCeti.StrandsAlgebra.oneStrandChord R genusOne.pair`) are `ρ₁ = (0 ↦ 1)`,
`ρ₂ = (1 ↦ 2)`, `ρ₃ = (2 ↦ 3)`, `ρ₁₂ = (0 ↦ 2)`, `ρ₂₃ = (1 ↦ 3)` and `ρ₁₂₃ = (0 ↦ 3)`; a chord
starts at the idempotent of the pair of its first point and ends at that of its last point.

This file constructs the type `D` structures over the torus algebra that the solid tori of the
genus-one Heegaard splittings give in bordered Floer homology, following Lipshitz, Ozsváth and
Thurston. A type `D` structure is described by generators with idempotents and the coefficients
of `δ¹`; an arrow `x → y` labelled `a` below means that `a ⊗ y` is a term of `δ¹ x`.

* **The unbounded structure `δ¹ x = ρ₁₂ ⊗ x`** (`TauCeti.StrandsAlgebra.torusRho₁₂TypeD`), with one
  generator `x` at `ι₀`, the shape of the type `D` structure of the complement of the unknot with
  framing `0`. Its structure equation `d ρ₁₂ + ρ₁₂ ρ₁₂ = 0` holds since a single strand has no
  crossing and `ρ₁₂` ends at `2`, where it does not start. Its iterates are
  `δᵏ x = ρ₁₂ ⊗ ⋯ ⊗ ρ₁₂ ⊗ x` (`TauCeti.StrandsAlgebra.iteratedCoeff_torusRho₁₂TypeD`), which are
  nonzero over every nontrivial ring although `ρ₁₂ ρ₁₂ = 0`: the iterates are tensor powers, not
  products. So the structure is not bounded
  (`TauCeti.StrandsAlgebra.not_isBounded_torusRho₁₂TypeD`), and paired with a type `A` module whose
  operations `m_{k+1}(y, ρ₁₂, …, ρ₁₂)` are nonzero for every `k` its box tensor differential would
  be an infinite sum. A finite set of generators is therefore not a boundedness hypothesis for the
  box tensor product.
* **A bounded model of it** (`TauCeti.StrandsAlgebra.torusBoundedRho₁₂TypeD`), with generators
  `y₁, x, y₂` at `ι₁, ι₀, ι₁` and arrows `y₁ → x` labelled `ρ₂`, `x → y₂` labelled `ρ₁` and
  `y₁ → y₂` labelled `ι₁`. Cancelling the arrow `y₁ → y₂` with coefficient the idempotent leaves
  the arrow `x → x` labelled `ρ₁ ρ₂ = ρ₁₂`: the two structures are homotopy equivalent
  (`TauCeti.StrandsAlgebra.exists_homotopyEquiv_torusRho₁₂TypeD_torusBoundedRho₁₂TypeD`), by
  explicit morphisms `F` and `G` with `F G = 1` and an explicit homotopy `H` with `∂H = G F + 1`
  over a ring of characteristic two. The model is bounded
  (`TauCeti.StrandsAlgebra.isBounded_torusBoundedRho₁₂TypeD`), so it can be paired with type `A`
  modules whose higher operations never vanish.
* **The structure `δ¹ y = ρ₂₃ ⊗ y`** (`TauCeti.StrandsAlgebra.torusRho₂₃TypeD`), with one
  generator `y` at `ι₁`: the same shape with the roles of the two idempotents exchanged, the chord
  `ρ₂₃` starting and ending at the pair `{1, 3}`. It is the structure `N_∞` of the surgery exact
  triangle of `TauCeti.LowDimTopology.Bordered.Torus.SurgeryTriangle`.
* **The chains `torusChainTypeD n`** (`TauCeti.StrandsAlgebra.torusChainTypeD`), with a generator
  `x` at `ι₀` and generators `γ₀, …, γₙ` at `ι₁`, and arrows `x → γ₀` labelled `ρ₁`, `x → γₙ`
  labelled `ρ₃` and `γₗ₊₁ → γₗ` labelled `ρ₂₃`. This is the shape of the type `D` structure of the
  complement of the unknot with framing `-(n + 1)`, the unstable chain of Lipshitz, Ozsváth and
  Thurston for a knot of genus zero. Its structure equation holds because `ρ₃ ρ₂₃ = ρ₂₃ ρ₂₃ = 0`
  and the only nonzero product `ρ₁ ρ₂₃` would need an arrow out of `γ₀`. It is bounded
  (`TauCeti.StrandsAlgebra.isBounded_torusChainTypeD`).

These are algebraic structures: identifying them with the type `D` structures defined by
holomorphic curves is not part of this file. Their pairings with the solid-torus type `A` modules
are computed in `TauCeti.LowDimTopology.Bordered.Torus.Pairing`.

## Main definitions

* `TauCeti.StrandsAlgebra.torusRho₁₂TypeD`: the type `D` structure `δ¹ x = ρ₁₂ ⊗ x`.
* `TauCeti.StrandsAlgebra.torusRho₂₃TypeD`: the type `D` structure `δ¹ y = ρ₂₃ ⊗ y`.
* `TauCeti.StrandsAlgebra.torusBoundedRho₁₂TypeD`: its bounded model with three generators.
* `TauCeti.StrandsAlgebra.torusChainTypeD`: the chain with `n + 2` generators.

## Main results

* `TauCeti.StrandsAlgebra.iteratedCoeff_torusRho₁₂TypeD`: `δᵏ x = ρ₁₂^{⊗ k} ⊗ x`.
* `TauCeti.StrandsAlgebra.not_isBounded_torusRho₁₂TypeD`: over a nontrivial ring the structure
  `δ¹ x = ρ₁₂ ⊗ x` is not bounded.
* `TauCeti.StrandsAlgebra.exists_homotopyEquiv_torusRho₁₂TypeD_torusBoundedRho₁₂TypeD`: it is
  homotopy equivalent to its bounded model.
* `TauCeti.StrandsAlgebra.isBounded_torusBoundedRho₁₂TypeD`,
  `TauCeti.StrandsAlgebra.isBounded_torusChainTypeD`: the bounded model and the chains are bounded.

## References

* R. Lipshitz, P. S. Ozsváth and D. P. Thurston, *Bordered Heegaard Floer homology*, Mem. Amer.
  Math. Soc. **254** (2018), no. 1216, [arXiv:0810.0687](https://arxiv.org/abs/0810.0687),
  §2.2 (boundedness of type `D` structures and the box tensor product), §3.2 (the torus
  algebra), Chapter 11 and Appendix A (the type `D` structures of knot complements, whose case of
  the unknot gives `torusRho₁₂TypeD` in framing `0` and `torusChainTypeD n` in framing `-(n + 1)`).
-/

public section

noncomputable section

namespace TauCeti

namespace StrandsAlgebra

open PointedMatchedCircle StrandDiagram

variable (R : Type*) [CommRing R]

/-- **The type `D` structure `δ¹ x = ρ₁₂ ⊗ x`** over the torus algebra: one generator `x` at the
idempotent `ι₀ = I({0}) + I({2})` of the pair `genusOne.pair 0 = {0, 2}`, whose only coefficient is
the chord `ρ₁₂` from `0` to `2`. -/
def torusRho₁₂TypeD :
    TypeDStructure (matchedSummandDifferential R genusOne.pair 1) (oneStrandIdem R genusOne.pair)
      Unit where
  idem _ := Set.rangeFactorization genusOne.pair 0
  coeff := Matrix.of fun _ _ ↦ oneStrandChord R genusOne.pair (by decide : (0 : Fin 4) < 2)
  idem_mul_coeff _ _ := by simp
  coeff_mul_idem _ _ := by simp
  map_coeff_add_coeff_mul_coeff := Matrix.ext fun _ _ ↦ by
    simp [Matrix.mul_apply,
      oneStrandChord_mul_oneStrandChord_of_ne _ _ _ (by decide : (2 : Fin 4) ≠ 0)]

@[simp]
theorem torusRho₁₂TypeD_idem (x : Unit) :
    (torusRho₁₂TypeD R).idem x = Set.rangeFactorization genusOne.pair 0 :=
  (rfl)

@[simp]
theorem torusRho₁₂TypeD_coeff (x y : Unit) :
    (torusRho₁₂TypeD R).coeff x y = oneStrandChord R genusOne.pair (by decide : (0 : Fin 4) < 2) :=
  (rfl)

/-- **The iterates of `δ¹ x = ρ₁₂ ⊗ x`** are `δᵏ x = ρ₁₂ ⊗ ⋯ ⊗ ρ₁₂ ⊗ x`, with `k` factors `ρ₁₂`. -/
@[simp]
theorem iteratedCoeff_torusRho₁₂TypeD (k : ℕ) (x z : Unit) :
    (torusRho₁₂TypeD R).iteratedCoeff k x z = PiTensorProduct.tprod R fun _ ↦
      oneStrandChord R genusOne.pair (by decide : (0 : Fin 4) < 2) :=
  (torusRho₁₂TypeD R).iteratedCoeff_self_of_coeff_eq_zero
    (fun y hy ↦ absurd (Subsingleton.elim y x) hy) k

/-- **The type `D` structure `δ¹ x = ρ₁₂ ⊗ x` is not bounded.** Over a nontrivial ring its iterates
`δᵏ x = ρ₁₂^{⊗ k} ⊗ x` never vanish, although `ρ₁₂ ρ₁₂ = 0` and there is a single generator. -/
theorem not_isBounded_torusRho₁₂TypeD [Nontrivial R] : ¬(torusRho₁₂TypeD R).IsBounded := by
  refine (torusRho₁₂TypeD R).not_isBounded_of_coeff_eq_zero_of_tprod_ne_zero (x := ())
    (fun y hy ↦ absurd (Subsingleton.elim y ()) hy) fun k h ↦ ?_
  -- The coordinate of the strand `ρ₁₂` takes the value `1` on each factor of `ρ₁₂^{⊗ k}`.
  have := congrArg (PiTensorProduct.dualDistrib (PiTensorProduct.tprod R fun _ : Fin k ↦
    oneStrandChordCoord R genusOne.pair (by decide : (0 : Fin 4) < 2))) h
  simp [PiTensorProduct.dualDistrib_apply] at this

/-- **The type `D` structure `δ¹ y = ρ₂₃ ⊗ y`** over the torus algebra: one generator `y` at the
idempotent `ι₁ = I({1}) + I({3})` of the pair `genusOne.pair 1 = {1, 3}`, whose only coefficient is
the chord `ρ₂₃` from `1` to `3`. Its structure equation `d ρ₂₃ + ρ₂₃ ρ₂₃ = 0` holds since a single
strand has no crossing and `ρ₂₃` ends at `3`, where it does not start. -/
def torusRho₂₃TypeD :
    TypeDStructure (matchedSummandDifferential R genusOne.pair 1) (oneStrandIdem R genusOne.pair)
      Unit where
  idem _ := Set.rangeFactorization genusOne.pair 1
  coeff := Matrix.of fun _ _ ↦ oneStrandChord R genusOne.pair (by decide : (1 : Fin 4) < 3)
  idem_mul_coeff _ _ := by simp
  coeff_mul_idem _ _ := by simp
  map_coeff_add_coeff_mul_coeff := Matrix.ext fun _ _ ↦ by
    simp [Matrix.mul_apply,
      oneStrandChord_mul_oneStrandChord_of_ne _ _ _ (by decide : (3 : Fin 4) ≠ 1)]

@[simp]
theorem torusRho₂₃TypeD_idem (y : Unit) :
    (torusRho₂₃TypeD R).idem y = Set.rangeFactorization genusOne.pair 1 :=
  (rfl)

@[simp]
theorem torusRho₂₃TypeD_coeff (y z : Unit) :
    (torusRho₂₃TypeD R).coeff y z = oneStrandChord R genusOne.pair (by decide : (1 : Fin 4) < 3) :=
  (rfl)

/-! ### A bounded model of `δ¹ x = ρ₁₂ ⊗ x` -/

/-- **A bounded model of the type `D` structure `δ¹ x = ρ₁₂ ⊗ x`**: generators `y₁, x, y₂` (the
indices `0, 1, 2`) at the idempotents `ι₁, ι₀, ι₁`, with `δ¹ y₁ = ρ₂ ⊗ x + ι₁ ⊗ y₂`,
`δ¹ x = ρ₁ ⊗ y₂` and `δ¹ y₂ = 0`. Its structure equation holds since `ρ₂ ρ₁ = 0`. It is homotopy
equivalent to `torusRho₁₂TypeD`
(`TauCeti.StrandsAlgebra.exists_homotopyEquiv_torusRho₁₂TypeD_torusBoundedRho₁₂TypeD`), and
bounded (`TauCeti.StrandsAlgebra.isBounded_torusBoundedRho₁₂TypeD`). -/
def torusBoundedRho₁₂TypeD :
    TypeDStructure (matchedSummandDifferential R genusOne.pair 1) (oneStrandIdem R genusOne.pair)
      (Fin 3) where
  idem := ![Set.rangeFactorization genusOne.pair 1, Set.rangeFactorization genusOne.pair 0,
    Set.rangeFactorization genusOne.pair 1]
  coeff := !![0, oneStrandChord R genusOne.pair (by decide : (1 : Fin 4) < 2),
      oneStrandIdem R genusOne.pair (Set.rangeFactorization genusOne.pair 1);
    0, 0, oneStrandChord R genusOne.pair (by decide : (0 : Fin 4) < 1);
    0, 0, 0]
  idem_mul_coeff x y := by
    fin_cases x <;> fin_cases y <;> simp [genusOne_pair_zero, genusOne_pair_one]
  coeff_mul_idem x y := by
    fin_cases x <;> fin_cases y <;> simp [genusOne_pair_zero, genusOne_pair_one, genusOne_pair_two]
  map_coeff_add_coeff_mul_coeff := Matrix.ext fun x z ↦ by
    -- The only composable pair of coefficients is `ρ₂ ρ₁ = 0`.
    fin_cases x <;> fin_cases z <;>
      simp [oneStrandChord_mul_oneStrandChord_of_ne _ _ _ (by decide : (2 : Fin 4) ≠ 0)]

@[simp]
theorem torusBoundedRho₁₂TypeD_idem :
    (torusBoundedRho₁₂TypeD R).idem = ![Set.rangeFactorization genusOne.pair 1,
      Set.rangeFactorization genusOne.pair 0, Set.rangeFactorization genusOne.pair 1] :=
  (rfl)

@[simp]
theorem torusBoundedRho₁₂TypeD_coeff :
    (torusBoundedRho₁₂TypeD R).coeff =
      !![0, oneStrandChord R genusOne.pair (by decide : (1 : Fin 4) < 2),
          oneStrandIdem R genusOne.pair (Set.rangeFactorization genusOne.pair 1);
        0, 0, oneStrandChord R genusOne.pair (by decide : (0 : Fin 4) < 1);
        0, 0, 0] :=
  (rfl)

/-- **The bounded model is bounded**: its coefficients increase the index of the generators. -/
theorem isBounded_torusBoundedRho₁₂TypeD : (torusBoundedRho₁₂TypeD R).IsBounded :=
  (torusBoundedRho₁₂TypeD R).isBounded_of_lt (fun x ↦ x) fun x y h ↦ by
    fin_cases x <;> fin_cases y <;> simp_all

/-- **`δ¹ x = ρ₁₂ ⊗ x` is homotopy equivalent to its bounded model**, over a ring of characteristic
two. The morphisms are `F x = ρ₁ ⊗ y₁ + ι₀ ⊗ x` from `torusRho₁₂TypeD` and `G x = ι₀ ⊗ x`,
`G y₂ = ρ₂ ⊗ x`, `G y₁ = 0` back; both are cycles, `F G` is the identity, and the morphism `H`
with the single coefficient `ι₁` from `y₂` to `y₁` satisfies `∂H = G F + 1`. -/
theorem exists_homotopyEquiv_torusRho₁₂TypeD_torusBoundedRho₁₂TypeD [CharP R 2] :
    ∃ F ∈ (torusRho₁₂TypeD R).morphisms (torusBoundedRho₁₂TypeD R),
    ∃ G ∈ (torusBoundedRho₁₂TypeD R).morphisms (torusRho₁₂TypeD R),
      (torusRho₁₂TypeD R).morphismDifferential (torusBoundedRho₁₂TypeD R) F = 0 ∧
      (torusBoundedRho₁₂TypeD R).morphismDifferential (torusRho₁₂TypeD R) G = 0 ∧
      F * G = (torusRho₁₂TypeD R).idMorphism ∧
      ∃ H ∈ (torusBoundedRho₁₂TypeD R).morphisms (torusBoundedRho₁₂TypeD R),
        (torusBoundedRho₁₂TypeD R).morphismDifferential (torusBoundedRho₁₂TypeD R) H =
          G * F + (torusBoundedRho₁₂TypeD R).idMorphism := by
  refine ⟨Matrix.of fun _ y ↦
      if y = 0 then oneStrandChord R genusOne.pair (by decide : (0 : Fin 4) < 1)
      else if y = 1 then oneStrandIdem R genusOne.pair (Set.rangeFactorization genusOne.pair 0)
      else 0, ?memF,
    Matrix.of fun x _ ↦
      if x = 1 then oneStrandIdem R genusOne.pair (Set.rangeFactorization genusOne.pair 0)
      else if x = 2 then oneStrandChord R genusOne.pair (by decide : (1 : Fin 4) < 2)
      else 0, ?memG, ?cycleF, ?cycleG, ?FG,
    !![0, 0, 0; 0, 0, 0;
      oneStrandIdem R genusOne.pair (Set.rangeFactorization genusOne.pair 1), 0, 0], ?memH, ?dH⟩
  -- `F`, `G` and `H` respect the idempotents, checked entrywise.
  case memF | memG | memH =>
    rw [TypeDStructure.mem_morphisms_iff]
    intro x y
    fin_cases x <;> fin_cases y <;> simp [genusOne_pair_zero, genusOne_pair_one, genusOne_pair_two]
  -- The cycle conditions, `F G = 1` and `∂H = G F + 1` are identities between explicit matrices
  -- over the torus algebra, checked entrywise. In `∂H = G F + 1`, the entry `(y₂, y₁)` of `G F`
  -- is `ρ₂ ρ₁ = 0`, and its entry `(x, x)`, `ι₀`, cancels against the identity in characteristic
  -- two.
  case cycleF | cycleG | FG | dH =>
    refine Matrix.ext fun x y ↦ ?_
    simp only [TypeDStructure.morphismDifferential_apply, Matrix.add_apply, Matrix.mul_apply]
    fin_cases x <;> fin_cases y <;>
      simp [Fin.sum_univ_three, genusOne_pair_zero, genusOne_pair_one, genusOne_pair_two,
        add_self_eq_zero_of_charTwo R,
        oneStrandChord_mul_oneStrandChord_of_ne _ _ _ (by decide : (2 : Fin 4) ≠ 0)]

/-! ### The chains of the unknot complements with negative framing -/

/-- **The chain `torusChainTypeD n`**: a generator `x = none` at `ι₀` and generators
`γₗ = some l`, `l ≤ n`, at `ι₁`, with `δ¹ x = ρ₁ ⊗ γ₀ + ρ₃ ⊗ γₙ`, `δ¹ γₗ₊₁ = ρ₂₃ ⊗ γₗ` and
`δ¹ γ₀ = 0`. It has the shape of the type `D` structure of the complement of the unknot with
framing `-(n + 1)`. Its structure equation holds since `ρ₃ ρ₂₃ = ρ₂₃ ρ₂₃ = 0`, while `ρ₁` leads to
`γ₀`, which has no outgoing coefficient. -/
def torusChainTypeD (n : ℕ) :
    TypeDStructure (matchedSummandDifferential R genusOne.pair 1) (oneStrandIdem R genusOne.pair)
      (Option (Fin (n + 1))) where
  idem
    | none => Set.rangeFactorization genusOne.pair 0
    | some _ => Set.rangeFactorization genusOne.pair 1
  coeff := Matrix.of fun
    | none, some l =>
      (if l = 0 then oneStrandChord R genusOne.pair (by decide : (0 : Fin 4) < 1) else 0) +
        if l = Fin.last n then oneStrandChord R genusOne.pair (by decide : (2 : Fin 4) < 3) else 0
    | some l, some l' =>
      if (l : ℕ) = l' + 1 then oneStrandChord R genusOne.pair (by decide : (1 : Fin 4) < 3) else 0
    | _, none => 0
  idem_mul_coeff x y := by
    rcases x with _ | l <;> rcases y with _ | l' <;>
      simp [mul_add, mul_ite, genusOne_pair_zero, genusOne_pair_one, genusOne_pair_two]
  coeff_mul_idem x y := by
    rcases x with _ | l <;> rcases y with _ | l' <;>
      simp [add_mul, ite_mul, genusOne_pair_one, genusOne_pair_three]
  map_coeff_add_coeff_mul_coeff := Matrix.ext fun x z ↦ by
    rcases x with _ | l <;> rcases z with _ | l' <;>
      simp only [Matrix.map_apply, matchedSummandDifferential_apply_of_le_one le_rfl,
        Matrix.zero_apply, Matrix.add_apply, Matrix.mul_apply, Fintype.sum_option, Matrix.of_apply,
        zero_add, mul_zero, zero_mul, Finset.sum_const_zero]
    all_goals refine Finset.sum_eq_zero fun x _ ↦ ?_
    · -- `ρ₁ ρ₂₃` would need an arrow out of `γ₀`, and `ρ₃ ρ₂₃ = 0`.
      by_cases h : (x : ℕ) = l' + 1
      · have hx : x ≠ 0 := fun h0 ↦ by simp [h0] at h
        simp [hx, ite_mul,
          oneStrandChord_mul_oneStrandChord_of_ne _ _ _ (by decide : (3 : Fin 4) ≠ 1)]
      · simp [h]
    · -- `ρ₂₃ ρ₂₃ = 0`.
      simp [ite_mul, oneStrandChord_mul_oneStrandChord_of_ne _ _ _ (by decide : (3 : Fin 4) ≠ 1)]

@[simp]
theorem torusChainTypeD_idem_none (n : ℕ) :
    (torusChainTypeD R n).idem none = Set.rangeFactorization genusOne.pair 0 :=
  (rfl)

@[simp]
theorem torusChainTypeD_idem_some (n : ℕ) (l : Fin (n + 1)) :
    (torusChainTypeD R n).idem (some l) = Set.rangeFactorization genusOne.pair 1 :=
  (rfl)

@[simp]
theorem torusChainTypeD_coeff_none_some (n : ℕ) (l : Fin (n + 1)) :
    (torusChainTypeD R n).coeff none (some l) =
      (if l = 0 then oneStrandChord R genusOne.pair (by decide : (0 : Fin 4) < 1) else 0) +
        if l = Fin.last n then oneStrandChord R genusOne.pair (by decide : (2 : Fin 4) < 3)
        else 0 :=
  (rfl)

@[simp]
theorem torusChainTypeD_coeff_some_some (n : ℕ) (l l' : Fin (n + 1)) :
    (torusChainTypeD R n).coeff (some l) (some l') =
      if (l : ℕ) = l' + 1 then oneStrandChord R genusOne.pair (by decide : (1 : Fin 4) < 3)
      else 0 :=
  (rfl)

@[simp]
theorem torusChainTypeD_coeff_none_right (n : ℕ) (x : Option (Fin (n + 1))) :
    (torusChainTypeD R n).coeff x none = 0 := by
  cases x <;> rfl

/-- **The chains are bounded**: their coefficients increase the height `0` of `x` and `n + 1 - l`
of `γₗ`. -/
theorem isBounded_torusChainTypeD (n : ℕ) : (torusChainTypeD R n).IsBounded :=
  (torusChainTypeD R n).isBounded_of_lt (fun | none => 0 | some l => n + 1 - l) fun x y h ↦ by
    rcases x with _ | l <;> rcases y with _ | l'
    · simp at h
    · simp only
      omega
    · simp at h
    · have : (l : ℕ) = l' + 1 := by
        by_contra hne
        simp [hne] at h
      simp only
      omega

end StrandsAlgebra

end TauCeti

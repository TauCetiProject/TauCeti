/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.Bordered.PointedMatchedCircle
public import TauCeti.LowDimTopology.Bordered.StrandsAlgebra.Occupancy
public import TauCeti.LowDimTopology.Bordered.TypeDD

/-!
# The identity type `DD` bimodule of the torus algebra

The identity cobordism of the surface `F(Z)` of a pointed matched circle `Z` has a type `DD`
bimodule over `A(Z)` and `A(-Z)`. Lipshitz, Ozsváth and Thurston compute it combinatorially: it
has one generator for each pair of complementary idempotents, `I(s)` on the side of `Z` and
`I(sᶜ)` on the side of `-Z`, and the structure map

`δ¹ = ∑_ξ a(ξ) ⊗ a(-ξ)`,

summed over the chords `ξ` of `Z`, where `-ξ` is the same chord seen from the reversed circle `-Z`.
This file constructs it for the genus-one pointed matched circle `Z`
(`TauCeti.PointedMatchedCircle.genusOne`), whose points `0, 1, 2, 3` are matched as `{0, 2}` and
`{1, 3}`, over the torus algebras with one strand of `Z` and of `-Z`.

The torus algebra of `Z` is `matchedSummand R genusOne.pair 1`, with idempotents
`ι₀ = I({0, 2})` and `ι₁ = I({1, 3})` and the chords `ρ₁ = (0 ↦ 1)`, `ρ₂ = (1 ↦ 2)`,
`ρ₃ = (2 ↦ 3)`, `ρ₁₂ = (0 ↦ 2)`, `ρ₂₃ = (1 ↦ 3)` and `ρ₁₂₃ = (0 ↦ 3)`. The reversed circle `-Z`
(`TauCeti.PointedMatchedCircle.reverse`) numbers the same four points in the opposite order, the
point `i` of `Z` becoming the point `3 - i` of `-Z`; its pairs are again `{0, 2}` and `{1, 3}`.
A chord `ξ` from `i` to `j` of `Z` is the chord `-ξ` from `3 - j` to `3 - i` of `-Z`
(`TauCeti.StrandsAlgebra.torusChordTensor` is the elementary tensor `a(ξ) ⊗ a(-ξ)`). Writing
`σ₁ = (0 ↦ 1)`, `σ₂ = (1 ↦ 2)`, `σ₃ = (2 ↦ 3)` and `σ₁₂₃ = (0 ↦ 3)` for the chords of `-Z`, the
chords `ρ₁, ρ₂, ρ₃, ρ₁₂₃` of `Z` correspond to `σ₃, σ₂, σ₁, σ₁₂₃`.

The complement of the pair `{0, 2}` of `Z` is `{1, 3}`, which is the pair `{0, 2}` of `-Z`. So the
two generators are `x₀` over `ι₀ ⊗ ι₀` and `x₁` over `ι₁ ⊗ ι₁`, writing `ι₀` and `ι₁` also for
the idempotents of `-Z` (`TauCeti.StrandsAlgebra.torusIdentityTypeDD`), and the structure map is

`δ¹ x₀ = (ρ₁ ⊗ σ₃ + ρ₃ ⊗ σ₁ + ρ₁₂₃ ⊗ σ₁₂₃) ⊗ x₁`, `δ¹ x₁ = ρ₂ ⊗ σ₂ ⊗ x₀`.

These are exactly the terms of `∑_ξ a(ξ) ⊗ a(-ξ)` between the two generators: the coefficient from
`x` to `y` is `I(x) (∑_ξ a(ξ) ⊗ a(-ξ)) I(y)`
(`TauCeti.StrandsAlgebra.torusIdentityTypeDD_coeff_eq_mul_torusChordSum_mul`). The chords `ρ₁₂`
and `ρ₂₃`, whose ends are matched, drop out, since on the side of `-Z` they start at the other
idempotent.

The torus algebras have no differential, and the structure equation `δ * δ = 0` holds because
every product of two of these terms vanishes in one of the factors: `ρ₁ ρ₂ = ρ₁₂` but
`σ₃ σ₂ = 0`, and `ρ₂ ρ₃ = ρ₂₃` but `σ₂ σ₁ = 0`, while the other products already vanish in `A(Z)`.
The type `DD` structure is not bounded
(`TauCeti.StrandsAlgebra.not_isBounded_torusIdentityTypeDD`): the path `x₀ → x₁ → x₀ → ⋯`
gives nonzero iterates `δᵏ` of every length, although `δ * δ = 0`. So its box tensor product with
a type `A` module needs that module to be bounded
(`TauCeti.LowDimTopology.Bordered.TypeA.TypeDD`).

## Main definitions

* `TauCeti.StrandsAlgebra.torusChordTensor`: the elementary tensor `a(ξ) ⊗ a(-ξ)` of a chord.
* `TauCeti.StrandsAlgebra.torusChordSum`: the sum `∑_ξ a(ξ) ⊗ a(-ξ)` over the six chords.
* `TauCeti.StrandsAlgebra.torusIdentityTypeDD`: the identity type `DD` bimodule of the torus
  algebra.

## Main results

* `TauCeti.StrandsAlgebra.torusIdentityTypeDD_idem_snd_eq_iff`: each generator sits over
  complementary idempotents of `Z` and `-Z`.
* `TauCeti.StrandsAlgebra.torusIdentityTypeDD_coeff_eq_mul_torusChordSum_mul`: its coefficients
  are the parts of `∑_ξ a(ξ) ⊗ a(-ξ)` between the idempotents of the generators.
* `TauCeti.StrandsAlgebra.not_isBounded_torusIdentityTypeDD`: over a nontrivial ring it is not
  bounded.

## References

* R. Lipshitz, P. S. Ozsváth and D. P. Thurston, *Bimodules in bordered Heegaard Floer homology*,
  Geom. Topol. **19** (2015), 525–724, [arXiv:1003.0598](https://arxiv.org/abs/1003.0598)
  (the type `DD` bimodule of the identity cobordism, `δ¹ = ∑_ξ a(ξ) ⊗ a(-ξ)` over the
  complementary idempotents).
* R. Lipshitz, P. S. Ozsváth and D. P. Thurston, *Bordered Heegaard Floer homology*, Mem. Amer.
  Math. Soc. **254** (2018), no. 1216, [arXiv:0810.0687](https://arxiv.org/abs/0810.0687), §3.2
  (the genus-one pointed matched circle and the torus algebra).
-/

public section

noncomputable section

open scoped TensorProduct

namespace TauCeti

namespace StrandsAlgebra

open PointedMatchedCircle StrandDiagram

variable (R : Type*) [CommRing R]

/-- The elementary tensor `a(ξ) ⊗ a(-ξ)` of the chord `ξ` from `i` to `j` of the genus-one pointed
matched circle `Z`: the chord itself in the torus algebra of `Z`, tensored with the same chord in
the torus algebra of `-Z`, where it runs from `3 - j` to `3 - i`. -/
def torusChordTensor {i j : Fin 4} (h : i < j) :
    matchedSummand R genusOne.pair 1 ⊗[R] matchedSummand R genusOne.reverse.pair 1 :=
  oneStrandChord R genusOne.pair h ⊗ₜ oneStrandChord R genusOne.reverse.pair (Fin.rev_lt_rev.2 h)

/-- The sum `∑_ξ a(ξ) ⊗ a(-ξ)` over the six chords `ξ` of the genus-one pointed matched circle. -/
def torusChordSum :
    matchedSummand R genusOne.pair 1 ⊗[R] matchedSummand R genusOne.reverse.pair 1 :=
  ∑ i : Fin 4, ∑ j : Fin 4, if h : i < j then torusChordTensor R h else 0

/-- The elementary tensor of the chord `ξ` from `i` to `j` is `a(ξ) ⊗ a(-ξ)`, where `-ξ` runs from
`3 - j` to `3 - i`. -/
theorem torusChordTensor_def {i j : Fin 4} (h : i < j) :
    torusChordTensor R h = oneStrandChord R genusOne.pair h ⊗ₜ
      oneStrandChord R genusOne.reverse.pair (Fin.rev_lt_rev.2 h) :=
  (rfl)

/-- The chord sum `∑_ξ a(ξ) ⊗ a(-ξ)` written out over the six chords
`ρ₁, ρ₁₂, ρ₁₂₃, ρ₂, ρ₂₃, ρ₃`. -/
theorem torusChordSum_eq :
    torusChordSum R = torusChordTensor R (by decide : (0 : Fin 4) < 1) +
      torusChordTensor R (by decide : (0 : Fin 4) < 2) +
      torusChordTensor R (by decide : (0 : Fin 4) < 3) +
      torusChordTensor R (by decide : (1 : Fin 4) < 2) +
      torusChordTensor R (by decide : (1 : Fin 4) < 3) +
      torusChordTensor R (by decide : (2 : Fin 4) < 3) := by
  simp [torusChordSum, Fin.sum_univ_four, add_assoc]

/-- **The identity type `DD` bimodule of the torus algebra.** It has the generator `x₀` over the
idempotents `I({0, 2})` of `Z` and of `-Z`, and the generator `x₁` over the idempotents
`I({1, 3})`; its structure map is `δ¹ x₀ = (ρ₁ ⊗ σ₃ + ρ₃ ⊗ σ₁ + ρ₁₂₃ ⊗ σ₁₂₃) ⊗ x₁` and
`δ¹ x₁ = ρ₂ ⊗ σ₂ ⊗ x₀`, the terms `a(ξ) ⊗ a(-ξ)` of the chords `ξ` between the two generators. -/
def torusIdentityTypeDD :
    TypeDDStructure (matchedSummandDifferential R genusOne.pair 1)
      (matchedSummandDifferential R genusOne.reverse.pair 1) (oneStrandIdem R genusOne.pair)
      (oneStrandIdem R genusOne.reverse.pair) (Fin 2) where
  idem := ![(⟨genusOne.pair 0, 0, rfl⟩, ⟨genusOne.reverse.pair 0, 0, rfl⟩),
    (⟨genusOne.pair 1, 1, rfl⟩, ⟨genusOne.reverse.pair 1, 1, rfl⟩)]
  coeff := !![0, torusChordTensor R (by decide : (0 : Fin 4) < 1) +
      torusChordTensor R (by decide : (2 : Fin 4) < 3) +
      torusChordTensor R (by decide : (0 : Fin 4) < 3);
    torusChordTensor R (by decide : (1 : Fin 4) < 2), 0]
  idem_mul_coeff x y := by
    fin_cases x <;> fin_cases y <;>
      simp [torusChordTensor, Algebra.TensorProduct.tmul_mul_tmul, mul_add]
  coeff_mul_idem x y := by
    fin_cases x <;> fin_cases y <;>
      simp [torusChordTensor, Algebra.TensorProduct.tmul_mul_tmul, add_mul]
  map_coeff_add_coeff_mul_coeff := by
    ext x z
    fin_cases x <;> fin_cases z <;>
      simp [torusChordTensor, Algebra.TensorProduct.tmul_mul_tmul, add_mul, mul_add,
        oneStrandChord_mul_oneStrandChord_of_ne]

@[simp]
theorem torusIdentityTypeDD_idem_zero :
    (torusIdentityTypeDD R).idem 0 =
      (⟨genusOne.pair 0, 0, rfl⟩, ⟨genusOne.reverse.pair 0, 0, rfl⟩) :=
  (rfl)

@[simp]
theorem torusIdentityTypeDD_idem_one :
    (torusIdentityTypeDD R).idem 1 =
      (⟨genusOne.pair 1, 1, rfl⟩, ⟨genusOne.reverse.pair 1, 1, rfl⟩) :=
  (rfl)

/-- **The generators sit over complementary idempotents.** A point `j` of `Z`, which is the point
`3 - j` of `-Z`, lies in the pair of the idempotent of a generator on the side of `-Z` exactly when
it does not lie in the pair of its idempotent on the side of `Z`. -/
theorem torusIdentityTypeDD_idem_snd_eq_iff (x : Fin 2) (j : Fin 4) :
    ((torusIdentityTypeDD R).idem x).2.val = genusOne.reverse.pair j.rev ↔
      ((torusIdentityTypeDD R).idem x).1.val ≠ genusOne.pair j := by
  fin_cases x <;> fin_cases j <;> simp

/-- The generators correspond to the idempotents of the torus algebra of `Z`. -/
theorem torusIdentityTypeDD_idem_fst_bijective :
    Function.Bijective fun x ↦ ((torusIdentityTypeDD R).idem x).1 := by
  refine ⟨fun x y h ↦ ?_, ?_⟩
  · fin_cases x <;> fin_cases y <;> simp_all
  · rintro ⟨_, i, rfl⟩
    fin_cases i
    exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨0, Subtype.ext (by simp)⟩, ⟨1, Subtype.ext (by simp)⟩]

/-- `δ¹ x₀ = (ρ₁ ⊗ σ₃ + ρ₃ ⊗ σ₁ + ρ₁₂₃ ⊗ σ₁₂₃) ⊗ x₁`. -/
@[simp]
theorem torusIdentityTypeDD_coeff_zero_one :
    (torusIdentityTypeDD R).coeff 0 1 = torusChordTensor R (by decide : (0 : Fin 4) < 1) +
      torusChordTensor R (by decide : (2 : Fin 4) < 3) +
      torusChordTensor R (by decide : (0 : Fin 4) < 3) :=
  (rfl)

/-- `δ¹ x₁ = ρ₂ ⊗ σ₂ ⊗ x₀`. -/
@[simp]
theorem torusIdentityTypeDD_coeff_one_zero :
    (torusIdentityTypeDD R).coeff 1 0 = torusChordTensor R (by decide : (1 : Fin 4) < 2) :=
  (rfl)

/-- Neither generator has a coefficient to itself. -/
@[simp]
theorem torusIdentityTypeDD_coeff_self (x : Fin 2) : (torusIdentityTypeDD R).coeff x x = 0 := by
  fin_cases x <;> rfl

/-- **The coefficients of the identity type `DD` bimodule are the terms of `∑_ξ a(ξ) ⊗ a(-ξ)`.**
The coefficient from `x` to `y` is the part `I(x) (∑_ξ a(ξ) ⊗ a(-ξ)) I(y)` of the chord sum between
the idempotents of the two generators. -/
theorem torusIdentityTypeDD_coeff_eq_mul_torusChordSum_mul (x y : Fin 2) :
    (torusIdentityTypeDD R).coeff x y =
      (oneStrandIdem R genusOne.pair ((torusIdentityTypeDD R).idem x).1 ⊗ₜ
          oneStrandIdem R genusOne.reverse.pair ((torusIdentityTypeDD R).idem x).2) *
        torusChordSum R *
        (oneStrandIdem R genusOne.pair ((torusIdentityTypeDD R).idem y).1 ⊗ₜ
          oneStrandIdem R genusOne.reverse.pair ((torusIdentityTypeDD R).idem y).2) := by
  fin_cases x <;> fin_cases y <;>
    simp [torusChordSum, torusChordTensor, Fin.sum_univ_four, Algebra.TensorProduct.tmul_mul_tmul,
      add_mul, mul_add]
  -- Only the coefficient from `x₀` to `x₁` has several terms, which the chord sum lists in another
  -- order.
  abel

/-- Each generator has a functional which takes the value `1` on its coefficient to the other
generator: the coordinate of `ρ₁ ⊗ σ₃` for `x₀`, and that of `ρ₂ ⊗ σ₂` for `x₁`. -/
private theorem exists_dual_coeff_add_one_eq_one :
    ∃ ψ : Fin 2 → Module.Dual R
        (matchedSummand R genusOne.pair 1 ⊗[R] matchedSummand R genusOne.reverse.pair 1),
      ∀ a, ψ a ((torusIdentityTypeDD R).coeff a (a + 1)) = 1 := by
  refine ⟨![TensorProduct.dualDistrib R _ _
      (oneStrandChordCoord R genusOne.pair (by decide : (0 : Fin 4) < 1) ⊗ₜ
        oneStrandChordCoord R genusOne.reverse.pair (by decide : (2 : Fin 4) < 3)),
    TensorProduct.dualDistrib R _ _
      (oneStrandChordCoord R genusOne.pair (by decide : (1 : Fin 4) < 2) ⊗ₜ
        oneStrandChordCoord R genusOne.reverse.pair (by decide : (1 : Fin 4) < 2))], fun a ↦ ?_⟩
  fin_cases a <;>
    simp [torusChordTensor, TensorProduct.dualDistrib_apply]

-- The path through the generators is `i ↦ i mod 2`, written with the cast `ℕ → Fin 2`.
open Fin.NatCast in
/-- **The identity type `DD` bimodule of the torus algebra is not bounded.** Over a nontrivial
ring, the path `x₀ → x₁ → x₀ → ⋯` gives nonzero iterates `δᵏ x₀` of every length, although
`δ * δ = 0`: the iterates are tensor products of coefficients, not products. -/
theorem not_isBounded_torusIdentityTypeDD [Nontrivial R] :
    ¬(torusIdentityTypeDD R).IsBounded := by
  refine (torusIdentityTypeDD R).not_isBounded_of_forall_coeff_eq_zero_of_tprod_ne_zero
    (fun i ↦ (i : Fin 2)) (fun i y hy ↦ ?_) fun k h ↦ ?_
  · -- The only generator besides the next one on the path is the current one.
    obtain rfl : y = (i : Fin 2) := by
      rw [Nat.cast_add_one] at hy
      generalize (i : Fin 2) = a at hy ⊢
      fin_cases a <;> fin_cases y <;> simp_all
    exact torusIdentityTypeDD_coeff_self R _
  · -- Pair the tensor product of the coefficients with the functionals taking the value `1` on
    -- them.
    obtain ⟨ψ, hψ⟩ := exists_dual_coeff_add_one_eq_one R
    have := congrArg (PiTensorProduct.dualDistrib
      (PiTensorProduct.tprod R fun t : Fin k ↦ ψ ((t : ℕ) : Fin 2))) h
    simp [PiTensorProduct.dualDistrib_apply, hψ] at this

end StrandsAlgebra

end TauCeti

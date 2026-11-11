/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.Bordered.PointedMatchedCircle
public import TauCeti.LowDimTopology.Bordered.StrandsAlgebra.Occupancy
public import TauCeti.LowDimTopology.Bordered.TypeD
import TauCeti.LowDimTopology.Bordered.StrandsAlgebra.StrandCount

/-!
# An unbounded type `D` structure over the torus algebra

The box tensor product `M ⊠ N` of a type `A` module with a type `D` structure has the differential
`∂ (m ⊗ x) = ∑_k (m_{k+1} ⊗ 1) (m ⊗ δ^k x)`, a finite sum only under a boundedness hypothesis
(`TauCeti.TypeDStructure.IsBounded`). This file shows that a finite set of generators is not such a
hypothesis, with the one-generator example of Lipshitz, Ozsváth and Thurston over the torus
algebra.

The torus algebra is the summand `A(Z, 0)` with one strand of the algebra of the genus-one pointed
matched circle `Z`, whose points `0, 1, 2, 3` are matched as `{0, 2}` and `{1, 3}`
(`TauCeti.PointedMatchedCircle.genusOne`); it is `matchedSummand R genusOne.pair 1`, a differential
algebra with the restricted differential `matchedSummandDifferential R genusOne.pair 1`. Its
idempotents are the `I({p})` of the pairs `p` (`TauCeti.StrandsAlgebra.torusIdem`), and the chord
`ρ₁₂` from `0` to `2` (`TauCeti.StrandsAlgebra.torusRho₁₂`) runs between the two matched points
`0` and `2`, so it starts and ends at the idempotent `ι₀ = I({0, 2})`.

The type `D` structure `TauCeti.StrandsAlgebra.torusLoop` has one generator `x` at `ι₀` and
structure map `δ¹ x = ρ₁₂ ⊗ x`. Its structure equation `d ρ₁₂ + ρ₁₂ ρ₁₂ = 0` holds since a single
strand has no crossing and `ρ₁₂` ends at `2`, where it does not start. Its iterates are
`δᵏ x = ρ₁₂ ⊗ ⋯ ⊗ ρ₁₂ ⊗ x` (`TauCeti.StrandsAlgebra.iteratedCoeff_torusLoop`), which are nonzero
over a field although `ρ₁₂ ρ₁₂ = 0`: the iterates are tensor powers, not products. So the structure
is not bounded (`TauCeti.StrandsAlgebra.not_isBounded_torusLoop`), and paired with a type `A`
module whose operations `m_{k+1}(y, ρ₁₂, …, ρ₁₂)` are nonzero for every `k` its box tensor
differential would be an infinite sum.

## Main definitions

* `TauCeti.StrandsAlgebra.torusIdem`: the idempotent `I({p})` of a pair `p` in the torus algebra.
* `TauCeti.StrandsAlgebra.torusRho₁₂`: the chord `ρ₁₂` in the torus algebra.
* `TauCeti.StrandsAlgebra.torusLoop`: the type `D` structure `δ¹ x = ρ₁₂ ⊗ x`.

## Main results

* `TauCeti.StrandsAlgebra.matchedSummandDifferential_torusRho₁₂`,
  `TauCeti.StrandsAlgebra.torusRho₁₂_mul_torusRho₁₂`: `d ρ₁₂ = 0` and `ρ₁₂ ρ₁₂ = 0`.
* `TauCeti.StrandsAlgebra.iteratedCoeff_torusLoop`: `δᵏ x = ρ₁₂^{⊗ k} ⊗ x`.
* `TauCeti.StrandsAlgebra.not_isBounded_torusLoop`: over a field the structure is not bounded.

## References

* R. Lipshitz, P. S. Ozsváth and D. P. Thurston, *Bordered Heegaard Floer homology*, Mem. Amer.
  Math. Soc. **254** (2018), no. 1216, [arXiv:0810.0687](https://arxiv.org/abs/0810.0687),
  §2.2 (boundedness of type `D` structures and the box tensor product) and §3.2 (the torus
  algebra).
-/

public section

noncomputable section

namespace TauCeti

namespace StrandsAlgebra

open Finset PointedMatchedCircle StrandDiagram

variable (R : Type*) [CommRing R]

/-- The idempotent `I({p})` of a pair `p` of the genus-one pointed matched circle, as an element of
the torus algebra `A(Z, 0)`, the summand of `A(Z)` with one strand. For `p = {0, 2}` it is
`ι₀ = I({0}) + I({2})`, and for `p = {1, 3}` it is `ι₁ = I({1}) + I({3})`. -/
def torusIdem (p : Sym2 (Fin 4)) : matchedSummand R genusOne.pair 1 :=
  ⟨matchedIdem R genusOne.pair {p}, by
    simpa using matchedIdem_mem_matchedSummand (R := R) genusOne.pair {p}⟩

@[simp]
theorem coe_torusIdem (p : Sym2 (Fin 4)) :
    (torusIdem R p : StrandsAlgebra R (Fin 4)) = matchedIdem R genusOne.pair {p} :=
  (rfl)

/-- The chord `ρ₁₂` of the torus algebra: the single strand from `0` to `2`, between the matched
points `0` and `2`. -/
def torusRho₁₂ : matchedSummand R genusOne.pair 1 :=
  ⟨of (single 0 2 (by decide)), by
    refine mem_matchedSummand.2 ⟨?_, of_mem_strandSummand (by rw [source_single, card_singleton])⟩
    simpa using oneStrandFamily_mem_matchedSubalgebra (R := R) genusOne.pair
      (.inr ⟨(0, 2), by decide⟩)⟩

@[simp]
theorem coe_torusRho₁₂ :
    (torusRho₁₂ R : StrandsAlgebra R (Fin 4)) = of (single 0 2 (by decide)) :=
  (rfl)

/-- `ρ₁₂` is the generator `a(ρ₁₂, ∅)` of the algebra of the genus-one matching, with no horizontal
strands. -/
private theorem isMatchedGenerator_single_zero_two :
    IsMatchedGenerator genusOne.pair (single (0 : Fin 4) 2 (by decide)) ∅ where
  notMem_self i := by simp only [single_apply]; split_ifs with h <;> simp [h]
  injOn_source := by simp [source_single]
  injOn_target := by simp [target_single]
  disjoint_source := Finset.disjoint_empty_right _
  disjoint_target := Finset.disjoint_empty_right _

/-- `ρ₁₂` starts at the idempotent `ι₀ = I({0, 2})`. -/
@[simp]
theorem torusIdem_mul_torusRho₁₂ : torusIdem R s(0, 2) * torusRho₁₂ R = torusRho₁₂ R := by
  refine Subtype.ext ?_
  rw [MulMemClass.coe_mul, coe_torusIdem, coe_torusRho₁₂,
    ← horizontalCompletion_empty (M := genusOne.pair),
    matchedIdem_mul_horizontalCompletion _ isMatchedGenerator_single_zero_two, ite_eq_left]
  simp only [source_single, Finset.image_singleton, Finset.union_empty, pair_def,
    genusOne_matching]
  decide

/-- `ρ₁₂` ends at the idempotent `ι₀ = I({0, 2})`. -/
@[simp]
theorem torusRho₁₂_mul_torusIdem : torusRho₁₂ R * torusIdem R s(0, 2) = torusRho₁₂ R := by
  refine Subtype.ext ?_
  rw [MulMemClass.coe_mul, coe_torusIdem, coe_torusRho₁₂,
    ← horizontalCompletion_empty (M := genusOne.pair),
    horizontalCompletion_mul_matchedIdem isMatchedGenerator_single_zero_two, ite_eq_left]
  simp only [target_single, Finset.image_singleton, Finset.union_empty, pair_def,
    genusOne_matching]
  decide

/-- `ρ₁₂ ρ₁₂ = 0`: `ρ₁₂` ends at `2`, where it does not start. -/
@[simp]
theorem torusRho₁₂_mul_torusRho₁₂ : torusRho₁₂ R * torusRho₁₂ R = 0 :=
  Subtype.ext (of_single_mul_of_single_of_ne _ _ (by decide))

/-- `d ρ₁₂ = 0`: a single strand has no crossing to resolve. -/
@[simp]
theorem matchedSummandDifferential_torusRho₁₂ :
    matchedSummandDifferential R genusOne.pair 1 (torusRho₁₂ R) = 0 :=
  Subtype.ext <| by
    rw [coe_matchedSummandDifferential, coe_torusRho₁₂, ZeroMemClass.coe_zero]
    exact differential_eq_zero_of_mem_strandCountPart le_rfl (by
      simpa using oneStrandFamily_mem_strandCountPart (R := R) genusOne.pair
        (.inr ⟨(0, 2), by decide⟩))

/-- Over a nontrivial ring the chord `ρ₁₂` is nonzero. -/
theorem torusRho₁₂_ne_zero [Nontrivial R] : torusRho₁₂ R ≠ 0 := fun h ↦
  (basis R (Fin 4)).ne_zero (single 0 2 (by decide)) (by
    simpa [basis_apply] using congrArg Subtype.val h)

/-- **The type `D` structure `δ¹ x = ρ₁₂ ⊗ x`** over the torus algebra: one generator `x` at the
idempotent `ι₀ = I({0, 2})`, whose only coefficient is `ρ₁₂`. -/
def torusLoop :
    TypeDStructure (matchedSummandDifferential R genusOne.pair 1) (torusIdem R) Unit where
  idem _ := s(0, 2)
  coeff := Matrix.of fun _ _ ↦ torusRho₁₂ R
  idem_mul_coeff _ _ := torusIdem_mul_torusRho₁₂ R
  coeff_mul_idem _ _ := torusRho₁₂_mul_torusIdem R
  map_coeff_add_coeff_mul_coeff := Matrix.ext fun _ _ ↦ by simp [Matrix.mul_apply]

@[simp]
theorem torusLoop_idem (x : Unit) : (torusLoop R).idem x = s(0, 2) :=
  (rfl)

@[simp]
theorem torusLoop_coeff (x y : Unit) : (torusLoop R).coeff x y = torusRho₁₂ R :=
  (rfl)

/-- **The iterates of `δ¹ x = ρ₁₂ ⊗ x`** are `δᵏ x = ρ₁₂ ⊗ ⋯ ⊗ ρ₁₂ ⊗ x`, with `k` factors `ρ₁₂`. -/
theorem iteratedCoeff_torusLoop (k : ℕ) (x z : Unit) :
    (torusLoop R).iteratedCoeff k x z = PiTensorProduct.tprod R fun _ ↦ torusRho₁₂ R :=
  (torusLoop R).iteratedCoeff_self_of_forall_ne (fun y hy ↦ absurd (Subsingleton.elim y x) hy) k

/-- **The type `D` structure `δ¹ x = ρ₁₂ ⊗ x` is not bounded.** Over a field its iterates
`δᵏ x = ρ₁₂^{⊗ k} ⊗ x` never vanish, although `ρ₁₂ ρ₁₂ = 0` and there is a single generator. -/
theorem not_isBounded_torusLoop (K : Type*) [Field K] : ¬(torusLoop K).IsBounded :=
  (torusLoop K).not_isBounded_of_forall_ne_of_coeff_ne_zero (x := ())
    (fun y hy ↦ absurd (Subsingleton.elim y ()) hy) (torusRho₁₂_ne_zero K)

end StrandsAlgebra

end TauCeti

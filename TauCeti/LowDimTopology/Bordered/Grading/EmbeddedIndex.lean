/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.Bordered.Grading.Domain
public import TauCeti.LowDimTopology.Bordered.StrandsAlgebra.Grading.Maslov
import Mathlib.Tactic.Linarith

/-!
# The embedded index of domains with Reeb chords

The holomorphic curves counted by the bordered invariants of Lipshitz, Ozsváth and Thurston
connect a generator `x` to a generator `y` through a domain `B` and leave the Heegaard surface
at its boundary along a sequence `ρ = (ρ₁, …, ρₖ)` of sets of Reeb chords, the chords of each
`ρᵢ` sitting at one height. Lipshitz, Ozsváth and Thurston show that the expected dimension of
the moduli space of such curves that are embedded is the *embedded index*

  `ind(B, ρ) = e(B) + n_x(B) + n_y(B) + k + ι(ρ)`,  `ι(ρ) = ∑ᵢ ι(ρᵢ) + ∑_{i < j} L(ρᵢ, ρⱼ)`,

where `e(B)` is the Euler measure of `B`, `n_x(B)` and `n_y(B)` are its point measures at the two
generators, `ι(ρᵢ) = -|ρᵢ| / 2 - ∑ |L(ρ_a, ρ_b)|` over the pairs of chords of `ρᵢ`, and `L` is the
bilinear form of the grading group of the strands algebra. Here a set of Reeb chords is recorded
as a strand diagram of `{0, …, n - 1}`, a chord running up from `s` to `t` being a strand from `s`
to `t`; horizontal strands, which complete a set of chords to a generator of the algebra, do not
change `ι`. The pair `(B, ρ)` is *compatible* when the part `∂^∂ B` of the boundary of `B` along
`∂Σ` is the sum of the classes of the chords, that is when its border class
(`TauCeti.BorderedHeegaardRegionSystem.borderClass`) is the sum of the boundaries of the `ρᵢ`.

This file defines `ind(B, ρ)` (`TauCeti.BorderedHeegaardRegionSystem.embeddedIndex`), taking
`ι(ρ)` to be the Maslov component of `gr(ρ₁) ⋯ gr(ρₖ)`, and proves that this is the formula
above (`TauCeti.BorderedHeegaardRegionSystem.embeddedIndex_ofFn`, with
`TauCeti.StrandDiagram.grading_maslov_eq` for the terms `ι(ρᵢ)`). It then proves the three
algebraic properties of the index that the analysis of the moduli spaces relies on.

* **Gradings.** For a compatible pair, the grading of the domain is
  `g'(B) = λ^(k - ind(B, ρ)) gr(ρ₁) ⋯ gr(ρₖ)`
  (`TauCeti.BorderedHeegaardRegionSystem.domainGrading_eq_lambda_zpow_mul_prod`). This is how the
  index of the curves counted by an operation of the bordered modules determines its degree.
* **Juxtaposition.** The index is additive when compatible pairs from `x` to `y` and from `y` to
  `w` are juxtaposed, `ind(B₁ + B₂, ρ ++ σ) = ind(B₁, ρ) + ind(B₂, σ)`
  (`TauCeti.BorderedHeegaardRegionSystem.IsDomainBetween.embeddedIndex_add`): the correction
  `L(∂^∂ B₁, ∂^∂ B₂)` in the point measures of a juxtaposition cancels the linking of the two
  chord sequences.
* **Collisions.** When the product of two consecutive sets `ρᵢ` and `ρᵢ₊₁` in the strands
  algebra is nonzero, replacing them by their product lowers the index by exactly one
  (`TauCeti.BorderedHeegaardRegionSystem.embeddedIndex_append_trans_cons`), since their gradings
  multiply. Two levels of chords colliding is one of the ends of the one-dimensional moduli
  spaces, matched in the structure relations of the bordered modules with the multiplication of
  the algebra.

## Main definitions

* `TauCeti.BorderedHeegaardRegionSystem.embeddedIndex`: the embedded index `ind(B, ρ)`.

## Main results

* `TauCeti.BorderedHeegaardRegionSystem.embeddedIndex_ofFn`: the explicit formula for the index.
* `TauCeti.BorderedHeegaardRegionSystem.domainGrading_eq_mk_mul_prod`,
  `TauCeti.BorderedHeegaardRegionSystem.domainGrading_eq_lambda_zpow_mul_prod`: the grading of a
  domain through a compatible chord sequence.
* `TauCeti.BorderedHeegaardRegionSystem.IsDomainBetween.embeddedIndex_add`: additivity under
  juxtaposition.
* `TauCeti.BorderedHeegaardRegionSystem.embeddedIndex_append_trans_cons`: collisions lower the
  index by one.

## References

* R. Lipshitz, P. Ozsváth and D. Thurston, *Bordered Heegaard Floer homology*, Mem. Amer. Math.
  Soc. **254** (2018), no. 1216, [arXiv:0810.0687](https://arxiv.org/abs/0810.0687), §5.7 (the
  embedded index `ind(B, ρ)` and the quantity `ι(ρ)`) and Chapter 10 (the gradings of the
  bordered modules, through the grading `g'` of domains).
-/

public section

open Finset

namespace TauCeti

open StrandGradingGroup

namespace BorderedHeegaardRegionSystem

universe u v w r

variable {g n : ℕ} {Arc : Type u} {AlphaCircle : Type v} {Point : Type w} {Region : Type r}
  (H : BorderedHeegaardRegionSystem g n Arc AlphaCircle Point Region)
  [Fintype Point] [DecidableEq Region] [Fintype Region]

/-- The **embedded index** `ind(B, ρ) = e(B) + n_x(B) + n_y(B) + |ρ| + ι(ρ)` of a domain `B`
from the generator `x` to the generator `y` with the sequence `ρ` of sets of Reeb chords, each
given as a strand diagram, for the Euler characteristics `χ` of the regions. Here `|ρ|` is the
length of the sequence and `ι(ρ)` is the Maslov component of the product of the gradings of its
terms, which is `∑ᵢ ι(ρᵢ) + ∑_{i < j} L(ρᵢ, ρⱼ)`
(`TauCeti.BorderedHeegaardRegionSystem.embeddedIndex_ofFn`). -/
def embeddedIndex (χ : Region → ℤ) (x y : H.Generator) (B : Region → ℤ)
    (ρ : List (StrandDiagram (Fin n))) : ℚ :=
  H.eulerMeasure χ B + H.generatorPointMeasure x B + H.generatorPointMeasure y B + ρ.length +
    (ρ.map StrandDiagram.grading).prod.maslov

theorem embeddedIndex_def (χ : Region → ℤ) (x y : H.Generator) (B : Region → ℤ)
    (ρ : List (StrandDiagram (Fin n))) :
    H.embeddedIndex χ x y B ρ =
      H.eulerMeasure χ B + H.generatorPointMeasure x B + H.generatorPointMeasure y B + ρ.length +
        (ρ.map StrandDiagram.grading).prod.maslov :=
  (rfl)

/-- Without Reeb chords, the embedded index is `e(B) + n_x(B) + n_y(B)`, the Maslov index of a
domain in a closed Heegaard diagram. -/
@[simp]
theorem embeddedIndex_nil (χ : Region → ℤ) (x y : H.Generator) (B : Region → ℤ) :
    H.embeddedIndex χ x y B [] =
      H.eulerMeasure χ B + H.generatorPointMeasure x B + H.generatorPointMeasure y B := by
  simp [embeddedIndex_def]

/-- **The embedded index of a sequence of chord sets.** For `ρ = (ρ₀, …, ρₖ₋₁)`,
`ind(B, ρ) = e(B) + n_x(B) + n_y(B) + k + ∑ᵢ ι(ρᵢ) + ∑_{i < j} L(ρᵢ, ρⱼ)`, where `ι(ρᵢ)` is the
Maslov component of the grading of `ρᵢ`, computed by `TauCeti.StrandDiagram.grading_maslov_eq`. -/
theorem embeddedIndex_ofFn (χ : Region → ℤ) (x y : H.Generator) (B : Region → ℤ) {k : ℕ}
    (ρ : Fin k → StrandDiagram (Fin n)) :
    H.embeddedIndex χ x y B (List.ofFn ρ) =
      H.eulerMeasure χ B + H.generatorPointMeasure x B + H.generatorPointMeasure y B + k +
        (∑ i, (ρ i).grading.maslov +
          ∑ i, ∑ j with i < j, linking (ρ i).boundary (ρ j).boundary) := by
  rw [embeddedIndex_def, List.map_ofFn, maslov_prod_ofFn, List.length_ofFn]
  simp

variable {H}

/-- **The grading of a domain through a chord sequence.** If the border class of `B` is the sum
of the classes of the chord sets `ρᵢ` of `ρ = (ρ₁, …, ρₘ)`, then `g'(B)` is `gr(ρ₁) ⋯ gr(ρₘ)`
with Maslov component shifted by `m - ind(B, ρ)`. -/
theorem domainGrading_eq_mk_mul_prod (χ : Region → ℤ) (x y : H.Generator) {B : Region → ℤ}
    {ρ : List (StrandDiagram (Fin n))}
    (hρ : H.borderClass B = (ρ.map StrandDiagram.boundary).sum) :
    H.domainGrading χ x y B =
      StrandGradingGroup.mk ((ρ.length : ℚ) - H.embeddedIndex χ x y B ρ) 0 *
        (ρ.map StrandDiagram.grading).prod := by
  refine StrandGradingGroup.ext ?_ ?_
  · simp only [domainGrading_maslov, mul_maslov, mk_maslov, mk_boundary, map_zero,
      AddMonoidHom.zero_apply, embeddedIndex_def]
    ring
  · simp only [domainGrading_boundary, mul_boundary, mk_boundary, zero_add, boundary_list_prod,
      List.map_map, Function.comp_def, StrandDiagram.grading_boundary, hρ]

/-- **The grading of a domain through a chord sequence, for an integral index.** If the border
class of `B` is the sum of the classes of the chord sets `ρᵢ` of `ρ = (ρ₁, …, ρₘ)` and
`ind(B, ρ) = k`, then `g'(B) = λ^(m - k) gr(ρ₁) ⋯ gr(ρₘ)`. -/
theorem domainGrading_eq_lambda_zpow_mul_prod (χ : Region → ℤ) (x y : H.Generator)
    {B : Region → ℤ} {ρ : List (StrandDiagram (Fin n))}
    (hρ : H.borderClass B = (ρ.map StrandDiagram.boundary).sum) {k : ℤ}
    (hk : H.embeddedIndex χ x y B ρ = k) :
    H.domainGrading χ x y B =
      lambda ^ ((ρ.length : ℤ) - k) * (ρ.map StrandDiagram.grading).prod := by
  rw [domainGrading_eq_mk_mul_prod χ x y hρ, hk, lambda_zpow, Int.cast_sub, Int.cast_natCast]

variable {x y w : H.Generator} {D E : Region → ℤ}

/-- **The embedded index is additive under juxtaposition.** If `D` connects `x` to `y` and `E`
connects `y` to `w`, with compatible chord sequences `ρ` and `σ`, then
`ind(D + E, ρ ++ σ) = ind(D, ρ) + ind(E, σ)`. -/
theorem IsDomainBetween.embeddedIndex_add (χ : Region → ℤ) (hD : H.IsDomainBetween x y D)
    (hE : H.IsDomainBetween y w E) {ρ σ : List (StrandDiagram (Fin n))}
    (hρ : H.borderClass D = (ρ.map StrandDiagram.boundary).sum)
    (hσ : H.borderClass E = (σ.map StrandDiagram.boundary).sum) :
    H.embeddedIndex χ x w (D + E) (ρ ++ σ) =
      H.embeddedIndex χ x y D ρ + H.embeddedIndex χ y w E σ := by
  have hn := hD.generatorPointMeasure_add_generatorPointMeasure hE
  have hprod : ((ρ ++ σ).map StrandDiagram.grading).prod.maslov =
      (ρ.map StrandDiagram.grading).prod.maslov + (σ.map StrandDiagram.grading).prod.maslov +
        linking (H.borderClass D) (H.borderClass E) := by
    rw [List.map_append, List.prod_append, mul_maslov, boundary_list_prod, boundary_list_prod,
      hρ, hσ]
    simp only [List.map_map, Function.comp_def, StrandDiagram.grading_boundary]
  simp only [embeddedIndex_def, map_add, hprod, List.length_append, Nat.cast_add]
  linarith

/-- **Collisions lower the embedded index by one.** If the product of the consecutive chord sets
`φ` and `ψ` in the strands algebra is nonzero, replacing them by their product `φ ψ` lowers the
embedded index by one. The border class is unchanged, since the class of `φ ψ` is the sum of
those of `φ` and `ψ`. -/
theorem embeddedIndex_append_trans_cons (χ : Region → ℤ) (x y : H.Generator) (B : Region → ℤ)
    (l₁ l₂ : List (StrandDiagram (Fin n))) {φ ψ : StrandDiagram (Fin n)} (h : φ.Composable ψ) :
    H.embeddedIndex χ x y B (l₁ ++ φ.trans ψ :: l₂) =
      H.embeddedIndex χ x y B (l₁ ++ φ :: ψ :: l₂) - 1 := by
  simp only [embeddedIndex_def, List.map_append, List.map_cons, List.prod_append, List.prod_cons,
    StrandDiagram.grading_trans h, mul_assoc, List.length_append, List.length_cons, Nat.cast_add,
    Nat.cast_one]
  ring

end BorderedHeegaardRegionSystem

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Twisted.RowFinite.Coefficients
public import TauCeti.AlgebraicTopology.Singular.Cubical.MonoidAlgebra.Pairing

/-!
# Pairing twisted complexes of cubical chains with solutions of the cocycle equation

Let `G` be a topological monoid and `m` a row-finite twisting cocycle over the normalized cubical
chains `C_*(G; R)`, on generators `P`. Let `Y` be a space with a left action of `G`, and
`c : P → C_*(Y; R)` a family of chains solving the cocycle equation `∑_y m_{x,y} · c_y = ∂ c_x`:
the generator `x` goes to `c_x`, and the free module `K_m` maps to `C_*(Y; R)`, linearly over the
chains of `G` and compatibly with the differentials. A Brown model of the chains on a based path
space is of this kind (`TauCeti.BrownModel`).

Let `X` be a space with a right action of `G` and `f : X × Y → Z` a continuous map balanced over
`G`, `f (x · g, y) = f (x, g · y)`. The twisted complex of `m` with coefficients in the right DG
module `C_*(X; R)` is the module `P →₀ C_*(X; R)` of finitely supported coefficient vectors, with
differential `D (σ e_x) = ∂σ e_x + (-1)^{|σ|} ∑_y (σ · m_{x,y}) e_y`. Pairing the coefficient at
`x` with `c_x` (`TauCeti.coefficientPairing`),

`P →₀ C_*(X; R) → C_*(Z; R)`,  `σ e_x ↦ f_*(σ × c_x)`,

commutes with the differentials (`TauCeti.coefficientPairing_coefficientDifferential`): the
boundary is a derivation for the pairing, the pairing is balanced over the chains of `G`, and the
cocycle equation turns the twisting part of `D` into the boundary of `c_x`. Pushing the
coefficients forward along an equivariant map of right `G`-spaces also commutes with the twisted
differentials
(`TauCeti.RowFiniteTwistingCocycle.coefficientDifferential_mapRange_cubicalChainModuleLinearMap`).

Concatenating paths gives the instances of interest: the change of basepoint of a Brown model
(`TauCeti.BrownModel.basepointChangeComparison`), and its comparison with the total space of a
map (`TauCeti.BrownModel.fibrationComparison`).

## Main definitions

* `TauCeti.coefficientPairing c f`: the map `σ e_x ↦ f_*(σ × c_x)` on coefficient vectors.

## Main results

* `TauCeti.coefficientPairing_coefficientDifferential`: it commutes with the differentials.

## References

* E. H. Brown, *Twisted tensor products, I*, Ann. of Math. (2) 69 (1959), 223–246.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapter 2 and §7.1.
-/

public section

noncomputable section

open MulOpposite

namespace TauCeti

universe uX uY uZ

section CoefficientPairing

variable {G K : Type*} {X : Type uX} {Y : Type uY} {Z : Type uZ} [TopologicalSpace X]
  [TopologicalSpace Y] [TopologicalSpace Z] {R : Type*} [CommRing R] {P : Type*}

/-- The **pairing of coefficient vectors with a family of chains** `c : P → C_*(Y; R)` along a
map `f : X × Y → Z`: the map `P →₀ C_*(X; R) → C_*(Z; R)`, `σ e_x ↦ f_*(σ × c_x)`, which pairs
the coefficient at each generator `x` with the chain `c_x`. -/
def coefficientPairing (c : P → cubicalChainModule Y K R) (f : C(X × Y, Z)) :
    (P →₀ cubicalChainModule X G R) →ₗ[R] cubicalChainModule Z K R :=
  Finsupp.lsum R fun x ↦ (cubicalChainPairing G K R f).flip (c x)

/-- The pairing of a coefficient `σ` at a single generator `x` is `f_*(σ × c_x)`. -/
@[simp]
theorem coefficientPairing_single (c : P → cubicalChainModule Y K R) (f : C(X × Y, Z)) (x : P)
    (σ : cubicalChainModule X G R) :
    coefficientPairing c f (Finsupp.single x σ) = cubicalChainPairing G K R f σ (c x) := by
  simp [coefficientPairing]

/-- **Pushing the pairing forward** along `g : Z → Z'` is the pairing along `g ∘ f`. -/
theorem cubicalChainModuleLinearMap_coefficientPairing {Z' : Type uZ} [TopologicalSpace Z']
    (c : P → cubicalChainModule Y K R) (f : C(X × Y, Z)) (g : C(Z, Z'))
    (u : P →₀ cubicalChainModule X G R) :
    cubicalChainModuleLinearMap R g (coefficientPairing c f u) =
      coefficientPairing c (g.comp f) u := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u u' hu hu' => simp only [map_add, hu, hu']
  | single x σ =>
    rw [coefficientPairing_single, coefficientPairing_single,
      cubicalChainModuleLinearMap_cubicalChainPairing]

/-- **Pairing push-forwards of the coefficients** along `h : X' → X` is the pairing along
`f ∘ (h × 1)`. -/
theorem coefficientPairing_mapRange_cubicalChainModuleLinearMap {X' : Type uX}
    [TopologicalSpace X'] (c : P → cubicalChainModule Y K R) (f : C(X × Y, Z)) (h : C(X', X))
    (u : P →₀ cubicalChainModule X' G R) :
    coefficientPairing c f
        (Finsupp.mapRange.linearMap (cubicalChainModuleLinearMap (G' := G) R h) u) =
      coefficientPairing c (f.comp (h.prodMap (ContinuousMap.id Y))) u := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u u' hu hu' => simp only [map_add, hu, hu']
  | single x σ =>
    rw [Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single, coefficientPairing_single,
      coefficientPairing_single, cubicalChainPairing_cubicalChainModuleLinearMap_left]

variable [Monoid G] [TopologicalSpace G] [ContinuousMul G] [MulAction Gᵐᵒᵖ X]
  [ContinuousSMul Gᵐᵒᵖ X] [MulAction G Y] [ContinuousSMul G Y] {ind : P → ℤ}

/-- **The coefficient pairing commutes with the differentials.** Let `m` be a row-finite twisting
cocycle over `C_*(G; R)`, `c : P → C_*(Y; R)` a solution of its cocycle equation
`∑_y m_{x,y} · c_y = ∂ c_x`, and `f : X × Y → Z` balanced over `G`. Then pairing with `c` sends
the twisted differential, with coefficients in `C_*(X; R)`, to the boundary of chains of `Z`. -/
theorem coefficientPairing_coefficientDifferential
    (m : RowFiniteTwistingCocycle (R := R) (A := normalizedCubicalChainAlgebra G R)
      (cubicalChainGrading G R) (cubicalChainDifferential G R) P ind)
    {c : P → cubicalChainModule Y K R}
    (hc : ∀ x, Finsupp.linearCombination (normalizedCubicalChainAlgebra G R) c (m.m x) =
      cubicalChainModuleDifferential Y K R (c x))
    {f : C(X × Y, Z)} (hf : ∀ (g : G) (x : X) (y : Y), f (op g • x, y) = f (x, g • y))
    (u : P →₀ cubicalChainModule X G R) :
    coefficientPairing c f
        (m.coefficientDifferential (cubicalChainModule_isDGRightModule X G R) u) =
      cubicalChainModuleDifferential Z K R (coefficientPairing c f u) := by
  classical
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u u' hu hu' => simp only [map_add, hu, hu']
  | single x σ =>
    induction σ using DirectSum.Decomposition.inductionOn (cubicalChainModuleGrading X G R) with
    | zero => simp
    | add σ σ' hσ hσ' => simp only [Finsupp.single_add, map_add, hσ, hσ']
    | @homogeneous q σ =>
      -- The Leibniz rule for the pairing splits off `f_*(∂σ × c_x)`; the remaining term
      -- `(-1)^q f_*(σ × ∂ c_x)` is the twisting part, by the cocycle equation for `c`.
      rw [m.coefficientDifferential_single _ x σ.property, map_add, Units.smul_def, map_zsmul,
        coefficientPairing_single, coefficientPairing_single,
        cubicalChainModuleDifferential_cubicalChainPairing _ σ.property, ← hc,
        Finsupp.linearCombination_apply, map_finsuppSum, map_finsuppSum, Units.smul_def]
      congr 2
      refine Finsupp.sum_congr fun y _ ↦ ?_
      rw [coefficientPairing_single, cubicalChainPairing_op_smul_left _ hf]

/-- **Pushing the coefficients forward** along a `G`-equivariant map `h : X → X'` commutes with
the twisted differentials, with coefficients in `C_*(X; R)` and in `C_*(X'; R)`. -/
theorem RowFiniteTwistingCocycle.coefficientDifferential_mapRange_cubicalChainModuleLinearMap
    (m : RowFiniteTwistingCocycle (R := R) (A := normalizedCubicalChainAlgebra G R)
      (cubicalChainGrading G R) (cubicalChainDifferential G R) P ind)
    {X' : Type uX} [TopologicalSpace X'] [MulAction Gᵐᵒᵖ X'] [ContinuousSMul Gᵐᵒᵖ X']
    (h : C(X, X')) (hh : ∀ (g : G) (x : X), h (op g • x) = op g • h x)
    (u : P →₀ cubicalChainModule X G R) :
    m.coefficientDifferential (cubicalChainModule_isDGRightModule X' G R)
        (Finsupp.mapRange.linearMap (cubicalChainModuleLinearMap R h) u) =
      Finsupp.mapRange.linearMap (cubicalChainModuleLinearMap R h)
        (m.coefficientDifferential (cubicalChainModule_isDGRightModule X G R) u) := by
  have hl : (cubicalChainModuleMap R h hh).toLinearMap.restrictScalars R =
      cubicalChainModuleLinearMap R h :=
    LinearMap.ext (cubicalChainModuleMap_apply h hh)
  rw [← hl]
  exact m.coefficientDifferential_mapRange _ _ _ u

end CoefficientPairing

end TauCeti

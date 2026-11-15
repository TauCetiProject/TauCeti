/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Torus.Basic
public import TauCeti.LinearAlgebra.Matrix.Determinant.BlockPermutation
import Mathlib.LinearAlgebra.Determinant

/-!
# Leading weight-block minors detect the weight action

Let an automorphism of an integral lattice carry weight vectors of weight `μ` to weight
vectors of weight `φ μ`, where `φ` is injective on the occurring weights. In a weight basis
its matrix permutes the
weight spaces, but need not permute the individual basis vectors. Over any nontrivial
commutative ring, all its leading weight-block minors are units exactly when it fixes every
occurring weight. If the weights span the character lattice, this forces `φ = 1`.

This is the weight-space step in the big-cell argument: a Weyl representative can have all
leading weight-block minors invertible only if its action on the weights is trivial. The
ordering is supplied as an equivalence from the distinct occurring weights to an ordered
label type; repeated weights form a single block, of unrestricted dimension. No compatibility
of the weight order with `φ` is assumed, and reduction may have arbitrary characteristic.

The coordinate-support argument uses
`TauCeti.UniversalEnvelopingAlgebra.repr_eq_zero_of_isCartanWeightVector`; the determinant
argument uses `Matrix.isUnit_det_toSquareBlockProp_le_iff_eqOn_range`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 5, Theorem 7.
* J. C. Jantzen, *Representations of Algebraic Groups*, Part II, Chapter 1.
-/

public section

namespace TauCeti.UniversalEnvelopingAlgebra

variable {L V κ η β A : Type*} [LieRing L] [LieAlgebra ℚ L]
  [AddCommGroup V] [Module ℚ V] [Fintype η] [DecidableEq η]
  [PartialOrder β] [DecidableLE β] [CommRing A] [Nontrivial A]
  (h : κ → L) (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V)
  (M : AddSubgroup V) (b : Module.Basis η ℤ M) (wt : η → κ → ℤ)
  (hwt : ∀ j, IsCartanWeightVector h ρ (wt j) (b j : V))

include hwt

omit [Nontrivial A] in
/-- A lattice map carrying basis weight vectors to their `φ`-weights has matrix support only
between the corresponding weight spaces, also after arbitrary change of coefficients. -/
theorem toMatrix_map_eq_zero_of_weight_ne (θ : M →ₗ[ℤ] M) (φ : (κ → ℤ) → (κ → ℤ))
    (hθ : ∀ j, IsCartanWeightVector h ρ (φ (wt j)) (θ (b j) : V))
    (i j : η) (hij : wt i ≠ φ (wt j)) :
    ((LinearMap.toMatrix b b θ).map (Int.castRingHom A)) i j = 0 := by
  simp only [Matrix.map_apply, LinearMap.toMatrix_apply,
    repr_eq_zero_of_isCartanWeightVector h ρ M b wt hwt (hθ j) hij, map_zero]

/-- All leading weight-block minors of a lattice automorphism are units exactly when its
weight action, assumed injective on the occurring weights, fixes every occurring weight `wt j`.
This holds over every nontrivial commutative ring, including rings in which some nonzero entries
of the integral matrix vanish. -/
theorem isUnit_leading_weight_minors_iff (θ : M ≃ₗ[ℤ] M) (φ : (κ → ℤ) → (κ → ℤ))
    (hφ : Set.InjOn φ (Set.range wt))
    (hθ : ∀ j, IsCartanWeightVector h ρ (φ (wt j)) (θ (b j) : V))
    (r : Set.range wt ≃ β) :
    (∀ a, IsUnit ((((LinearMap.toMatrix b b θ).map (Int.castRingHom A)).toSquareBlockProp
      fun i => r ⟨wt i, Set.mem_range_self i⟩ ≤ a).det)) ↔ ∀ j, φ (wt j) = wt j := by
  let N := (LinearMap.toMatrix b b θ).map (Int.castRingHom A)
  have hN : IsUnit N.det := by
    dsimp only [N]
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (θ.isUnit_det b b).map (Int.castRingHom A)
  have hs (i j : η) (hij : wt i ≠ φ (wt j)) : N i j = 0 :=
    toMatrix_map_eq_zero_of_weight_ne h ρ M b wt hwt θ φ hθ i j hij
  simpa only [Set.eqOn_range, Function.comp_def, id_eq, funext_iff] using
    Matrix.isUnit_det_toSquareBlockProp_le_iff_eqOn_range N hN wt φ hφ r hs

/-- If the weights span the character lattice, the leading weight-block minors detect the
identity weight endomorphism. In particular this rules out a nontrivial faithful Weyl action
in the matrix open set defined by these minors. -/
theorem isUnit_leading_weight_minors_iff_eq_one
    (hspan : Submodule.span ℤ (Set.range wt) = ⊤)
    (θ : M ≃ₗ[ℤ] M) (φ : Module.End ℤ (κ → ℤ)) (hφ : Set.InjOn φ (Set.range wt))
    (hθ : ∀ j, IsCartanWeightVector h ρ (φ (wt j)) (θ (b j) : V))
    (r : Set.range wt ≃ β) :
    (∀ a, IsUnit ((((LinearMap.toMatrix b b θ).map (Int.castRingHom A)).toSquareBlockProp
      fun i => r ⟨wt i, Set.mem_range_self i⟩ ≤ a).det)) ↔ φ = 1 := by
  rw [isUnit_leading_weight_minors_iff h ρ M b wt hwt θ φ hφ hθ r]
  constructor
  · intro hfix
    apply (Submodule.linearMap_eq_iff_of_span_eq_top φ 1 hspan).mpr
    rintro ⟨_, j, rfl⟩
    exact hfix j
  · rintro rfl j
    rfl

end TauCeti.UniversalEnvelopingAlgebra

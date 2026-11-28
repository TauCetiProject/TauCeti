/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Instances.AddCircle.Real
public import TauCeti.AlgebraicTopology.ThricePuncturedSphere.PuncturedNeighborhoods
public import TauCeti.Geometry.Symplectic.Floer.PeriodGroup
public import TauCeti.RingTheory.NovikovModule.Bilinear
public import TauCeti.RingTheory.NovikovModule.MapOfMatrix
public import TauCeti.Topology.Connected.TotallyDisconnected

/-!
# The point algebra: the pair-of-pants product on a zero-dimensional target

A closed zero-dimensional symplectic manifold is a finite set `X` of points with the discrete
topology. Working componentwise, every point is a copy of the one-point target, and the
pair-of-pants product is the *point algebra*. This file computes it from the counts of the
moduli spaces.

On a zero-dimensional target the tangent spaces are zero, so every Hamiltonian vector field
vanishes and every map satisfies the Floer equation `(du - X_K)^{0,1} = 0`; smooth maps into `X`
are the continuous ones. The one-periodic orbits of every Hamiltonian are the constant loops, one at
each point of `X`, and the capped generators of the point `x` are a torsor under the period group
`Γ`. The moduli spaces are therefore spaces of continuous maps with prescribed asymptotic values.
Since the pair of pants `S = ℂ ∖ {0, 1}` and the plane `ℂ` are connected, such a map is constant
(`Continuous.eq_const_of_tendsto`), so its class is `0` and

* the pairs of pants asymptotic to `x₁`, `x₂` at the inputs and to `x₀` at the output form a single
  point when `x₁ = x₀` and `x₂ = x₀`, and are empty otherwise
  (`TauCeti.Floer.discretePantsCount_eq`), the asymptotics being taken along the ends
  `TauCeti.ThricePuncturedSphere.Puncture.endFilter` of the pair of pants;
* the planes asymptotic to `x` at their end form a single point
  (`TauCeti.Floer.discretePlaneCount_eq`);
* every continuous cylinder `ℝ × S¹ → X` is invariant under translation, so the set of
  nonstationary cylinders is empty (`TauCeti.Floer.discreteCylinderCount_eq_zero`).

Each pair of pants and each plane is rigid, being a point of a moduli space whose linearized
operator acts between zero spaces, and its orientation line is canonically oriented, so these
cardinalities are the counts. The Floer differential counts nonstationary cylinders modulo
translation; that quotient is not formalized here, but the set it quotients is empty, so the map of
the matrix of cardinalities `discreteCylinderCount`, the zero matrix, vanishes
(`TauCeti.Floer.novikovMapOfMatrix_discreteCylinderCount`) and every capped combination is a
cocycle. In coordinates relative to reference caps, the product of the matrix of pair-of-pants
counts (`TauCeti.NovikovModule.novikovProductOfMatrix`) is then the pointwise product of
functions `X → Λ` with values in the Floer Novikov ring
(`TauCeti.Floer.coordinates_novikovProductOfMatrix_discretePantsCount`): the point algebra is the
ring of `Λ`-valued functions on `X`, the product that the cup product gives on `H⁰(X; Λ)`. The
combination of the plane counts has the constant coordinates `1`
(`TauCeti.Floer.coordinates_symm_discretePlaneCount`) and is a two-sided identity for the product
(`TauCeti.Floer.novikovProductOfMatrix_discretePantsCount_unit_left` and
`TauCeti.Floer.novikovProductOfMatrix_discretePantsCount_unit_right`), and the product is
commutative and associative at the chain level
(`TauCeti.Floer.novikovProductOfMatrix_discretePantsCount_comm`,
`TauCeti.Floer.novikovProductOfMatrix_discretePantsCount_assoc`), not merely up to homotopy. For a
single point, `X = {pt}`, the product is the multiplication of `Λ` with unit `1`. In the full
theory this combination is the PSS image of the fundamental cycle `∑ₓ x`; neither the PSS map nor
that identification is formalized here.

The results hold for any period group `Γ` and actions on the capped generators; on a
zero-dimensional target `Γ` is trivial, since every sphere is constant.

## References

* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the pair-of-pants product.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, the chapter on
  Floer homology and the pair-of-pants product.
-/

public section

noncomputable section

open Filter Topology

namespace TauCeti.Floer

open NovikovModule NovikovSeries PeriodGroup ThricePuncturedSphere

variable {X : Type*} [TopologicalSpace X] [DiscreteTopology X]

section Counts

/-- **The number of pairs of pants in a zero-dimensional target.** For a discrete target `X`, this
is the number of continuous maps from the pair of pants `S = ℂ ∖ {0, 1}` to `X` asymptotic to `x₁`
at the input `0`, to `x₂` at the input `1` and to `x₀` at the output `∞`, along the ends
`Puncture.endFilter` of `S`: the number of Floer pairs of pants with these asymptotic orbits, every
map into `X` being a solution of the Floer equation. -/
def discretePantsCount (x₁ x₂ x₀ : X) : ℕ :=
  Nat.card {u : C(ThricePuncturedSphere, X) // Tendsto u Puncture.zero.endFilter (𝓝 x₁) ∧
    Tendsto u Puncture.one.endFilter (𝓝 x₂) ∧ Tendsto u Puncture.inf.endFilter (𝓝 x₀)}

/-- **The number of planes in a zero-dimensional target.** For a discrete target `X`, this is the
number of continuous maps `ℂ → X` asymptotic to `x` at the end `∞` of the plane: the number of PSS
planes asymptotic to the constant orbit `x`, every map into `X` being a solution of the Floer
equation. -/
def discretePlaneCount (x : X) : ℕ :=
  Nat.card {u : C(ℂ, X) // Tendsto u (cocompact ℂ) (𝓝 x)}

/-- **The number of nonstationary cylinders in a zero-dimensional target.** For a discrete target
`X`, this is the number of continuous maps `ℝ × S¹ → X` asymptotic to `x` at the positive end
`s → ∞` and to `y` at the negative end `s → -∞` that are not invariant under every translation in
`s`: the cardinality of the set of nonstationary Floer cylinders between these orbits, not of its
quotient by translation. On a discrete target this set is empty
(`discreteCylinderCount_eq_zero`). -/
def discreteCylinderCount (x y : X) : ℕ :=
  Nat.card {u : C(ℝ × AddCircle (1 : ℝ), X) //
    Tendsto u (comap Prod.fst atTop) (𝓝 x) ∧ Tendsto u (comap Prod.fst atBot) (𝓝 y) ∧
      ∃ s, u ∘ (fun z => (z.1 + s, z.2)) ≠ u}

/-- **Pairs of pants in a zero-dimensional target are constant.** There is exactly one pair of
pants asymptotic to `x₁`, `x₂` and `x₀` when the three points agree, the constant map, and none
otherwise. -/
@[simp]
theorem discretePantsCount_eq [DecidableEq X] (x₁ x₂ x₀ : X) :
    discretePantsCount x₁ x₂ x₀ = if x₁ = x₀ ∧ x₂ = x₀ then 1 else 0 := by
  obtain ⟨w⟩ := Puncture.zero.endFilter.nonempty_of_neBot
  rw [discretePantsCount]
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    refine Nat.card_eq_one_iff_unique.2 ⟨⟨fun u v => ?_⟩,
      ⟨⟨.const _ _, tendsto_const_nhds, tendsto_const_nhds, tendsto_const_nhds⟩⟩⟩
    exact Subtype.ext <| DFunLike.coe_injective <|
      (u.val.continuous.eq_const_of_tendsto u.property.1).trans
        (v.val.continuous.eq_const_of_tendsto v.property.1).symm
  · refine Nat.card_eq_zero.2 (.inl ⟨fun ⟨u, h₁, h₂, h₀⟩ => h ?_⟩)
    have e₁ := congrFun (u.continuous.eq_const_of_tendsto h₁) w
    have e₂ := congrFun (u.continuous.eq_const_of_tendsto h₂) w
    have e₀ := congrFun (u.continuous.eq_const_of_tendsto h₀) w
    simp only [Function.const_apply] at e₁ e₂ e₀
    exact ⟨e₁.symm.trans e₀, e₂.symm.trans e₀⟩

/-- **Planes in a zero-dimensional target are constant.** There is exactly one plane asymptotic
to each point, the constant map. -/
@[simp]
theorem discretePlaneCount_eq (x : X) : discretePlaneCount x = 1 := by
  refine Nat.card_eq_one_iff_unique.2 ⟨⟨fun u v => ?_⟩, ⟨⟨.const _ x, tendsto_const_nhds⟩⟩⟩
  exact Subtype.ext <| DFunLike.coe_injective <|
    (u.val.continuous.eq_const_of_tendsto u.property).trans (v.val.continuous.eq_const_of_tendsto
        v.property).symm

/-- **Cylinders in a zero-dimensional target are stationary.** Every Floer cylinder in a discrete
target is constant, hence invariant under translation, so there are no nonstationary cylinders. -/
@[simp]
theorem discreteCylinderCount_eq_zero (x y : X) : discreteCylinderCount x y = 0 := by
  refine Nat.card_eq_zero.2 (.inl ⟨fun ⟨u, hx, _, s, hs⟩ => hs ?_⟩)
  rw [u.continuous.eq_const_of_tendsto hx, Function.const_comp]

end Counts

section Product

variable {R S : Type*} [CommSemiring R] [AddCommGroup S] {ω : S →+ ℝ} {c : S →+ ℤ}
  [Finite X] {P : X → Type*} [∀ x, AddTorsor (PeriodGroup ω c) (P x)]
  (r : ∀ x, P x) {F : (Σ x, P x) → ℝ}
  (hF : ∀ x γ (D : P x), F ⟨x, γ +ᵥ D⟩ = F ⟨x, D⟩ - (-area ω c) γ)

/-- **The cylinder matrix of a zero-dimensional target has zero map.** On a finite discrete target
there are no nonstationary cylinders, so the matrix `discreteCylinderCount` is zero and so is its
map on completed capped modules. -/
theorem novikovMapOfMatrix_discreteCylinderCount :
    novikovMapOfMatrix hF hF r r
        (fun x y => (discreteCylinderCount x y : NovikovSeries R _ (-area ω c))) = 0 := by
  simp only [discreteCylinderCount_eq_zero, Nat.cast_zero]
  exact novikovMapOfMatrix_zero hF hF r r

/-- **The point algebra.** On a finite discrete target, the product of the pair-of-pants counts
is the pointwise product in coordinates: relative to reference caps `r`, the coordinates of
`a ⋆ b` at the point `x` are the product of those of `a` and `b` at `x`. -/
theorem coordinates_novikovProductOfMatrix_discretePantsCount (a b : NovikovModule R F) :
    coordinates hF r (novikovProductOfMatrix hF hF hF r r r
        (fun x₁ x₂ x₀ => (discretePantsCount x₁ x₂ x₀ : NovikovSeries R _ (-area ω c))) a b) =
      coordinates hF r a * coordinates hF r b := by
  classical
  have := Fintype.ofFinite X
  funext x
  simp [coordinates_novikovProductOfMatrix, ite_and]

/-- On a finite discrete target, the combination of the plane counts has the constant
coordinates `1`. -/
theorem coordinates_symm_discretePlaneCount :
    (coordinates hF r).symm (fun x => (discretePlaneCount x : NovikovSeries R _ (-area ω c))) =
      (coordinates hF r).symm 1 := by
  simp [Pi.one_def]

/-- **The unit of the point algebra, on the left.** On a finite discrete target, the combination
of the plane counts is a left identity for the product of the pair-of-pants counts. -/
theorem novikovProductOfMatrix_discretePantsCount_unit_left (b : NovikovModule R F) :
    novikovProductOfMatrix hF hF hF r r r
        (fun x₁ x₂ x₀ => (discretePantsCount x₁ x₂ x₀ : NovikovSeries R _ (-area ω c)))
        ((coordinates hF r).symm fun x => (discretePlaneCount x : NovikovSeries R _ _)) b = b := by
  refine (coordinates hF r).injective ?_
  rw [coordinates_novikovProductOfMatrix_discretePantsCount, coordinates_symm_discretePlaneCount,
    LinearEquiv.apply_symm_apply, one_mul]

/-- **The unit of the point algebra, on the right.** On a finite discrete target, the combination
of the plane counts is a right identity for the product of the pair-of-pants counts. -/
theorem novikovProductOfMatrix_discretePantsCount_unit_right (a : NovikovModule R F) :
    novikovProductOfMatrix hF hF hF r r r
        (fun x₁ x₂ x₀ => (discretePantsCount x₁ x₂ x₀ : NovikovSeries R _ (-area ω c))) a
        ((coordinates hF r).symm fun x => (discretePlaneCount x : NovikovSeries R _ _)) = a := by
  refine (coordinates hF r).injective ?_
  rw [coordinates_novikovProductOfMatrix_discretePantsCount, coordinates_symm_discretePlaneCount,
    LinearEquiv.apply_symm_apply, mul_one]

/-- **The point algebra is commutative.** On a finite discrete target, the product of the
pair-of-pants counts is commutative at the chain level. -/
theorem novikovProductOfMatrix_discretePantsCount_comm (a b : NovikovModule R F) :
    novikovProductOfMatrix hF hF hF r r r
        (fun x₁ x₂ x₀ => (discretePantsCount x₁ x₂ x₀ : NovikovSeries R _ (-area ω c))) a b =
      novikovProductOfMatrix hF hF hF r r r
        (fun x₁ x₂ x₀ => (discretePantsCount x₁ x₂ x₀ : NovikovSeries R _ (-area ω c))) b a := by
  refine (coordinates hF r).injective ?_
  rw [coordinates_novikovProductOfMatrix_discretePantsCount,
    coordinates_novikovProductOfMatrix_discretePantsCount, mul_comm]

/-- **The point algebra is associative.** On a finite discrete target, the product of the
pair-of-pants counts is associative at the chain level. -/
theorem novikovProductOfMatrix_discretePantsCount_assoc (a b d : NovikovModule R F) :
    novikovProductOfMatrix hF hF hF r r r
        (fun x₁ x₂ x₀ => (discretePantsCount x₁ x₂ x₀ : NovikovSeries R _ (-area ω c)))
        (novikovProductOfMatrix hF hF hF r r r
          (fun x₁ x₂ x₀ => (discretePantsCount x₁ x₂ x₀ : NovikovSeries R _ _)) a b) d =
      novikovProductOfMatrix hF hF hF r r r
        (fun x₁ x₂ x₀ => (discretePantsCount x₁ x₂ x₀ : NovikovSeries R _ (-area ω c))) a
        (novikovProductOfMatrix hF hF hF r r r
          (fun x₁ x₂ x₀ => (discretePantsCount x₁ x₂ x₀ : NovikovSeries R _ _)) b d) := by
  refine (coordinates hF r).injective ?_
  simp only [coordinates_novikovProductOfMatrix_discretePantsCount, mul_assoc]

end Product

end TauCeti.Floer

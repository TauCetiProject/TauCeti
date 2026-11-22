/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Algebraic.Cone.LatticeNormal
public import TauCeti.Geometry.Toric.Algebraic.Fan.Basic

/-!
# Minkowski weights of a fan

A *Minkowski weight* of codimension `j` on a fan `Φ` is an integer function `c` on the cones of
codimension `j` that is balanced at every cone `τ` of codimension `j + 1`: for every integral
character `u` vanishing on `τ`,

  `∑_{σ ⊃ τ} c(σ) ⟨u, n_{σ,τ}⟩ = 0`,

the sum running over the cones of codimension `j` containing `τ`, where `n_{σ,τ}` is a lattice
normal of `σ` along its facet `τ` (`TauCeti.Toric.IsLatticeNormal`). For a complete fan,
Fulton and Sturmfels identify the Minkowski weights of codimension `j` with the operational Chow
group `A^j` of the toric variety, by evaluating a class on the orbit closures of the cones of
codimension `j`. Weights depend only on the fan, never on a coefficient field.

The balancing condition is the vanishing of finitely many integer linear functionals
`TauCeti.Toric.Fan.balancing`, so the Minkowski weights form a `ℤ`-submodule of the integer
functions on the cones of codimension `j`.

## Main declarations

* `TauCeti.Toric.Fan.ConeOfCodim`: the cones of a fan of a given codimension.
* `TauCeti.Toric.Fan.balancing`: the integer linear functional `c ↦ ∑_{σ ⊃ τ} c(σ) ⟨u, n_{σ,τ}⟩`
  attached to a cone `τ` and a character `u`.
* `TauCeti.Toric.Fan.balancing_apply_of_isLatticeNormal`: at a cone of codimension `j + 1` and a
  character vanishing on it, the balancing functional may be computed with any lattice normals.
* `TauCeti.Toric.Fan.minkowskiWeights`: the `ℤ`-submodule of Minkowski weights of codimension
  `j`, with membership `TauCeti.Toric.Fan.mem_minkowskiWeights` and extensionality
  `TauCeti.Toric.Fan.minkowskiWeights_ext`.

## References

* W. Fulton and B. Sturmfels, *Intersection theory on toric varieties*, Topology 36 (1997),
  §1 and §2, in particular Proposition 1.4 and Theorem 2.1.
-/

public section

open Module

namespace TauCeti.Toric.Fan

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}
  (Φ : Fan i)

/-- A cone of codimension `j` of a fan: a cone of the fan whose real span has codimension `j` in
the ambient real vector space. -/
abbrev ConeOfCodim (j : ℕ) : Type _ :=
  {σ : Φ.cones // finrank ℝ (Submodule.span ℝ (σ.val : Set V)) + j = finrank ℝ V}

/-- The *balancing functional* of a cone `τ` and an integral character `u`: the integer linear
functional `c ↦ ∑_{σ ⊃ τ} c(σ) ⟨u, n_{σ,τ}⟩` on integer functions on the cones of codimension
`j`, the sum running over the cones of codimension `j` containing `τ`. -/
noncomputable def balancing (j : ℕ) (τ : PointedCone ℝ V) (u : N →+ ℤ) :
    (Φ.ConeOfCodim j → ℤ) →ₗ[ℤ] ℤ :=
  letI := Fintype.ofFinite (Φ.ConeOfCodim j)
  open Classical in
  ∑ σ : Φ.ConeOfCodim j with τ ≤ σ.val.val, u (latticeNormal i τ σ.val.val) • LinearMap.proj σ

variable {Φ} {j : ℕ}

/-- The balancing functional evaluated on a weight, for any enumeration of the cones of
codimension `j`. -/
theorem balancing_apply [Fintype (Φ.ConeOfCodim j)] (τ : PointedCone ℝ V) (u : N →+ ℤ)
    [DecidablePred fun σ : Φ.ConeOfCodim j ↦ τ ≤ σ.val.val] (c : Φ.ConeOfCodim j → ℤ) :
    Φ.balancing j τ u c = ∑ σ with τ ≤ σ.val.val, c σ * u (latticeNormal i τ σ.val.val) := by
  classical
  rw [balancing, LinearMap.sum_apply]
  exact Finset.sum_congr (by ext; simp) fun σ _ ↦ by simp [mul_comm]

/-- At a cone `τ` of codimension `j + 1` and a character `u` vanishing on `τ`, the balancing
functional may be computed with any lattice normals `n σ` of the cones `σ ⊃ τ` along `τ`: the
value does not depend on the choice made by `TauCeti.Toric.latticeNormal`. -/
theorem balancing_apply_of_isLatticeNormal [Fintype (Φ.ConeOfCodim j)]
    (τ : Φ.ConeOfCodim (j + 1)) {u : N →+ ℤ} (hu : coneSublattice i τ.val.val ≤ u.ker)
    (n : Φ.ConeOfCodim j → N) (hn : ∀ σ : Φ.ConeOfCodim j, τ.val.val ≤ σ.val.val →
      IsLatticeNormal i τ.val.val σ.val.val (n σ))
    [DecidablePred fun σ : Φ.ConeOfCodim j ↦ τ.val.val ≤ σ.val.val] (c : Φ.ConeOfCodim j → ℤ) :
    Φ.balancing j τ.val.val u c = ∑ σ with τ.val.val ≤ σ.val.val, c σ * u (n σ) := by
  rw [balancing_apply]
  refine Finset.sum_congr rfl fun σ hσ ↦ ?_
  have hτσ := (Finset.mem_filter.1 hσ).2
  have hσr := (Φ.isToricCone σ.val.property).rational
  have hτr := (Φ.isToricCone τ.val.property).rational
  have hdim : finrank ℝ (Submodule.span ℝ (τ.val.val : Set V)) + 1 =
      finrank ℝ (Submodule.span ℝ (σ.val.val : Set V)) := by
    have := τ.property
    have := σ.property
    omega
  rw [(isLatticeNormal_latticeNormal Φ.lattice hσr hτr hτσ hdim).apply_eq
    (Φ.isFaceOf_of_le σ.val.property τ.val.property hτσ) (hn σ hτσ) hu]

variable (Φ j) in
/-- The *Minkowski weights* of codimension `j` of a fan: the integer functions on the cones of
codimension `j` annihilated by the balancing functional of every cone `τ` of codimension `j + 1`
and every integral character vanishing on `τ`. -/
noncomputable def minkowskiWeights : Submodule ℤ (Φ.ConeOfCodim j → ℤ) :=
  ⨅ τ : Φ.ConeOfCodim (j + 1), ⨅ u : {u : N →+ ℤ // coneSublattice i τ.val.val ≤ u.ker},
    LinearMap.ker (Φ.balancing j τ.val.val u)

/-- An integer function on the cones of codimension `j` is a Minkowski weight exactly when every
balancing sum vanishes. -/
theorem mem_minkowskiWeights {c : Φ.ConeOfCodim j → ℤ} :
    c ∈ Φ.minkowskiWeights j ↔ ∀ τ : Φ.ConeOfCodim (j + 1), ∀ u : N →+ ℤ,
      coneSublattice i τ.val.val ≤ u.ker → Φ.balancing j τ.val.val u c = 0 := by
  simp [minkowskiWeights]

/-- Two Minkowski weights agree exactly when their values on all cones of codimension `j`
agree. -/
theorem minkowskiWeights_ext {c d : Φ.minkowskiWeights j}
    (h : ∀ σ : Φ.ConeOfCodim j, (c : Φ.ConeOfCodim j → ℤ) σ = (d : Φ.ConeOfCodim j → ℤ) σ) :
    c = d :=
  Subtype.ext (funext h)

end TauCeti.Toric.Fan

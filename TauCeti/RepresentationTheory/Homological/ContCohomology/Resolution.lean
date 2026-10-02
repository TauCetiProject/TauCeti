/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Homological.ContCohomology.Basic

/-!
# Pointwise formulas for the coinduced resolution

Mathlib computes the continuous cohomology of a topological representation `X` from the coinduced
resolution `TopRep.resolutionX X n`, the iterated function space `C(G, C(G, …, C(G, X)))`, whose
differential `TopRep.d` is defined recursively by `d (n + 1) F x = F - d n (F x)`. This file
records the pointwise formulas that the recursion gives for the action and for the differential on
a successor level, and their consequence that evaluation at any point `x : G` contracts the
resolution: `d n (F x) + (d (n + 1) F) x = F`, summed over finitely many points. Evaluation at a
point is not `G`-equivariant, so the contraction does not descend to the invariants, which are the
homogeneous cochains; it is nevertheless what drives the acyclicity of coinduced modules, and a sum
of such contractions over suitably chosen points can descend.

In degree zero, the cocycle equation says that a homogeneous cochain is constant. The formula
`TopRep.homogeneousCochains.eq_d_zero_apply_of_d_eq_zero` records that the cochain is the constant
resolution element at its value at `1`.

## Main results

* `TopRep.resolutionX_succ_ρ_apply_apply` and `TopRep.hom_d_succ_apply_apply`: the action and
  the differential on a successor level of the resolution, at a point.
* `TopRep.d_sum_apply_add_sum_d_apply`: evaluation at finitely many points, summed, contracts the
  coinduced resolution up to the number of points.
* `TopRep.homogeneousCochains.eq_d_zero_apply_of_d_eq_zero`: a homogeneous zero-cocycle is
  constant.
* `TopRep.homogeneousCochains.d_one_apply`: the differential of a homogeneous one-cochain,
  evaluated, is `(d a) g₀ g₁ g₂ = a g₁ g₂ - (a g₀ g₂ - a g₀ g₁)`; so a one-cocycle satisfies
  `a g₀ g₂ = a g₀ g₁ + a g₁ g₂` (`TopRep.homogeneousCochains.apply_eq_add_of_d_eq_zero`).
-/

public section

namespace TopRep

variable {k G : Type*} [Ring k] [TopologicalSpace k] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] (X : TopRep k G)

/-- The action on a successor level of the coinduced resolution, at a point:
`(g • F) x = g • F (g⁻¹ * x)`. -/
@[simp]
theorem resolutionX_succ_ρ_apply_apply (n : ℕ) (g : G) (F : (resolutionX X (n + 1)).V) (x : G) :
    ((resolutionX X (n + 1)).ρ g F) x = (resolutionX X n).ρ g (F (g⁻¹ * x)) :=
  ContRepresentation.coind₁_apply_apply (resolutionX X n).ρ g F x

/-- The successor differential of the coinduced resolution, at a point:
`(d (n + 1) F) x = F - d n (F x)`. -/
@[simp]
theorem hom_d_succ_apply_apply (n : ℕ) (F : (resolutionX X (n + 1)).V) (x : G) :
    ((d X (n + 1)).hom F) x = F - (d X n).hom (F x) :=
  (rfl)

/-- **Summed evaluations contract the coinduced resolution up to a multiple.** For an element
`F : C(G, Xₘ)` of the degree `m + 1` term of the coinduced resolution and finitely many points
`σ i` of `G`, `dₘ (∑ᵢ F (σ i)) + ∑ᵢ (dₘ₊₁ F) (σ i) = |ι| • F`. Each summand is the identity
`dₘ (F x) + (dₘ₊₁ F) x = F` saying that evaluation at a point contracts the resolution. -/
theorem d_sum_apply_add_sum_d_apply {ι : Type*} [Fintype ι] (σ : ι → G) (m : ℕ)
    (F : (resolutionX X (m + 1)).V) :
    (d X m).hom (∑ i, (F : C(G, (resolutionX X m).V)) (σ i)) +
      ∑ i, ((d X (m + 1)).hom F : C(G, (resolutionX X (m + 1)).V)) (σ i) =
        Fintype.card ι • F := by
  rw [map_sum, ← Finset.sum_add_distrib]
  simp [hom_d_succ, ContIntertwiningMap.sub_apply]

variable {X}

/-- A homogeneous zero-cocycle is the constant resolution element at its value at `1`. -/
theorem homogeneousCochains.eq_d_zero_apply_of_d_eq_zero
    {a : (homogeneousCochains X).X 0}
    (ha : ((homogeneousCochains X).d 0 1).hom a = 0) :
    a.val = (d X 0).hom (a.val 1) := by
  have hd : (d X 1).hom a.val = 0 :=
    (homogeneousCochains.d_apply X 0 a).symm.trans (congrArg Subtype.val ha)
  have h := congrArg (fun F : (resolutionX X 2).V ↦ F 1) hd
  rw [hom_d_succ_apply_apply, ContinuousMap.zero_apply] at h
  exact sub_eq_zero.mp h

/-- The homogeneous differential of a one-cochain, evaluated:
`(d a) g₀ g₁ g₂ = a g₁ g₂ - (a g₀ g₂ - a g₀ g₁)`. -/
-- Not a `simp` lemma: `simp` rewrites the differential `(homogeneousCochains X).d 1 (1 + 1)` on
-- the left-hand side through `CategoryTheory.Functor.mapHomologicalComplex_obj_d` and
-- `CochainComplex.of_d`, so the statement is not in `simp`-normal form; use it with `rw` or
-- `simp only`.
theorem homogeneousCochains.d_one_apply (a : (homogeneousCochains X).X 1) (g₀ g₁ g₂ : G) :
    ((((homogeneousCochains X).d 1 (1 + 1)).hom a).val : C(G, C(G, C(G, X.V)))) g₀ g₁ g₂ =
      a.val g₁ g₂ - (a.val g₀ g₂ - a.val g₀ g₁) := by
  rw [homogeneousCochains.d_apply]
  simp only [hom_d_succ, d_zero, hom_ofHom, ContIntertwiningMap.sub_apply,
    ContRepresentation.coind₁ι_toFun, ContRepresentation.coind₁Map_toFun, ContinuousMap.sub_apply,
    ContinuousMap.const_apply, ContinuousMap.comp_apply, ContinuousMap.coe_mk]

/-- A homogeneous one-cocycle satisfies `a g₀ g₂ = a g₀ g₁ + a g₁ g₂`. -/
theorem homogeneousCochains.apply_eq_add_of_d_eq_zero {a : (homogeneousCochains X).X 1}
    (ha : ((homogeneousCochains X).d 1 (1 + 1)).hom a = 0) (g₀ g₁ g₂ : G) :
    a.val g₀ g₂ = a.val g₀ g₁ + a.val g₁ g₂ := by
  have h := congrArg (fun z : (homogeneousCochains X).X (1 + 1) ↦
    (z.val : C(G, C(G, C(G, X.V)))) g₀ g₁ g₂) ha
  rw [homogeneousCochains.d_one_apply] at h
  -- the right-hand side is the zero cochain, evaluated
  change _ = (0 : X.V) at h
  rw [sub_sub_eq_add_sub, sub_eq_zero] at h
  rw [← h, add_comm]

end TopRep

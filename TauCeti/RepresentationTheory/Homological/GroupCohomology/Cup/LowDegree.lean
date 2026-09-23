/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors; adapted from Dzack Garza
-/
module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import Mathlib.Tactic

/-!
# The ordinary `(1,1)` cup product

This file supplies the positive ordinary-cohomology slice

```text
H¹(G, ℤ_triv) × H¹(G, A) → H²(G, A),
```

for an integral `G`-representation `A`. The cochain formula is the inhomogeneous formula

```text
(σ ∪ τ)(g, h) = σ(g) • A.ρ(g) (τ(h)).
```

The proof first establishes that this is a `2`-cocycle. It then proves descent in the second
variable by an explicit `1`-cochain. Descent in the first variable uses
`coboundaries₁ (Rep.trivial ℤ G ℤ) = ⊥`.

The class-level definition chooses representatives of the two `H¹` classes. This choice is
intentional: Mathlib exposes `H¹` as a `ModuleCat` quotient, and `Classical.choose` is used only
to select a cocycle representative. `cup11_cocycle_eq_of_H1π_eq` records independence of the
explicit cochain formula, and `cup11_respects_cocycles` records the corresponding class-level
independence.
`cup11_mk` records the resulting pointwise formula on any supplied representatives.

This is a deliberately scoped `(1,1)` ordinary cochain/descent component that can be reused by a
future all-degree Tate construction. It is not itself a Tate cup product and does not claim an
all-degree ordinary cup product, negative-degree constructions, graded commutativity, or naturality.

## References

* K. S. Brown, *Cohomology of Groups*, Chapter VI, §5.
* The inhomogeneous cup-product proof spine was adapted from
  `dzackgarza/lean-categories`, `LeanCategories/Homological/GroupCohomologyCupProduct.lean`,
  commit `eb00e55e2d63e86be04c08dd2520c1e7e26aead1` (Apache-2.0).
-/
public noncomputable section

namespace TauCeti.groupCohomology

open CategoryTheory Rep
open _root_.groupCohomology

variable {G : Type} [Group G]
variable {A : Rep.{0} ℤ G}

private abbrev ZRep : Rep.{0} ℤ G := Rep.trivial ℤ G ℤ

private lemma rho_smul (A : Rep.{0} ℤ G) (g : G) (c : ℤ) (x : A) :
    A.ρ g (c • x) = c • A.ρ g x := by
  change (A.ρ g : A →ₗ[ℤ] A) (c • x) = _
  rw [map_smul]
  rfl

private lemma hs_add (σ : groupCohomology.cocycles₁ (G := G) (A := ZRep)) (g h : G) :
    σ (g * h) = σ h + σ g := by
  simpa [Rep.trivial_ρ_apply] using
    (groupCohomology.mem_cocycles₁_iff (σ : G → ℤ)).1 σ.property g h

/-- The inhomogeneous `(1,1)` formula is a `2`-cocycle. -/
lemma cup11_mem_cocycles₂ (σ : groupCohomology.cocycles₁ (G := G) (A := Rep.trivial ℤ G ℤ))
    (τ : groupCohomology.cocycles₁ (G := G) A) :
    (fun q : G × G => σ q.1 • A.ρ q.1 (τ q.2)) ∈
      groupCohomology.cocycles₂ (G := G) A := by
  have ht : ∀ g h : G, τ (g * h) = A.ρ g (τ h) + τ g := by
    intro g h
    exact (groupCohomology.mem_cocycles₁_iff (τ : G → A)).1 τ.property g h
  rw [groupCohomology.mem_cocycles₂_iff]
  intro g h j
  -- Beta-reduce the inhomogeneous cochain before applying the two cocycle equations.
  change
    ((σ (g * h) : ℤ) • A.ρ (g * h) (τ j) + σ g • A.ρ g (τ h)) =
      A.ρ g (σ h • A.ρ h (τ j)) + σ g • A.ρ g (τ (h * j))
  rw [hs_add σ g h, ht h j]
  rw [Rep.ρ_mul]
  simp only [LinearMap.coe_comp, Function.comp_apply]
  rw [map_add, rho_smul]
  module

/-- The inhomogeneous `(1,1)` cup of two ordinary one-cocycles. -/
private def cup11Cocycle
    (σ : groupCohomology.cocycles₁ (G := G) (Rep.trivial ℤ G ℤ))
    (τ : groupCohomology.cocycles₁ (G := G) A) :
    groupCohomology.cocycles₂ (G := G) A :=
  ⟨fun q : G × G => σ q.1 • A.ρ q.1 (τ q.2), cup11_mem_cocycles₂ σ τ⟩

private theorem cup11Cocycle_eq_mk
    (σ : groupCohomology.cocycles₁ (G := G) (Rep.trivial ℤ G ℤ))
    (τ : groupCohomology.cocycles₁ (G := G) A) :
    cup11Cocycle σ τ =
      ⟨fun q : G × G => σ q.1 • A.ρ q.1 (τ q.2), cup11_mem_cocycles₂ σ τ⟩ := by
  rfl

private theorem cup11Cocycle_add_left
    (σ σ' : groupCohomology.cocycles₁ (G := G) (Rep.trivial ℤ G ℤ))
    (τ : groupCohomology.cocycles₁ (G := G) A) :
    cup11Cocycle (σ + σ') τ = cup11Cocycle σ τ + cup11Cocycle σ' τ := by
  apply Subtype.ext
  funext q
  change (σ q.1 + σ' q.1) • A.ρ q.1 (τ q.2) =
    σ q.1 • A.ρ q.1 (τ q.2) + σ' q.1 • A.ρ q.1 (τ q.2)
  exact add_zsmul _ _ _

private theorem cup11Cocycle_zsmul_left
    (n : ℤ) (σ : groupCohomology.cocycles₁ (G := G) (Rep.trivial ℤ G ℤ))
    (τ : groupCohomology.cocycles₁ (G := G) A) :
    cup11Cocycle (n • σ) τ = n • cup11Cocycle σ τ := by
  apply Subtype.ext
  funext q
  -- Unfold the subtype-valued scalar action and the cochain constructor.
  dsimp [cup11Cocycle]
  change (n • (σ q.1 : ℤ)) • A.ρ q.1 (τ q.2) =
    n • ((σ q.1 : ℤ) • A.ρ q.1 (τ q.2))
  simp [smul_smul]

private theorem cup11Cocycle_zsmul_right
    (n : ℤ) (σ : groupCohomology.cocycles₁ (G := G) (Rep.trivial ℤ G ℤ))
    (τ : groupCohomology.cocycles₁ (G := G) A) :
    cup11Cocycle σ (n • τ) = n • cup11Cocycle σ τ := by
  apply Subtype.ext
  funext q
  -- Unfold the subtype-valued scalar action and use ℤ-linearity of the representation map.
  dsimp [cup11Cocycle]
  change σ q.1 • A.ρ q.1 (n • τ q.2) =
    n • (σ q.1 • A.ρ q.1 (τ q.2))
  rw [rho_smul]
  simp [smul_smul, mul_comm]

private theorem cup11Cocycle_add_right
    (σ : groupCohomology.cocycles₁ (G := G) (Rep.trivial ℤ G ℤ))
    (τ τ' : groupCohomology.cocycles₁ (G := G) A) :
    cup11Cocycle σ (τ + τ') = cup11Cocycle σ τ + cup11Cocycle σ τ' := by
  apply Subtype.ext
  funext q
  change σ q.1 • A.ρ q.1 (τ q.2 + τ' q.2) =
    σ q.1 • A.ρ q.1 (τ q.2) + σ q.1 • A.ρ q.1 (τ' q.2)
  rw [map_add, zsmul_add]

private lemma cup11_right_coboundary
    (σ : groupCohomology.cocycles₁ (G := G) (A := Rep.trivial ℤ G ℤ))
    (y : A) :
    (fun q : G × G => σ q.1 • A.ρ q.1 (A.ρ q.2 y - y)) ∈
      groupCohomology.coboundaries₂ A := by
  let z : G → A := fun g => -(σ g • A.ρ g y)
  let dz : G × G → A := (groupCohomology.d₁₂ A).hom z
  have hdz : dz =
      (fun q : G × G => σ q.1 • A.ρ q.1 (A.ρ q.2 y - y)) := by
    funext q
    dsimp [dz, z]
    simp only [groupCohomology.d₁₂_hom_apply]
    -- The primitive is the usual right-boundary homotopy for the prefix action.
    change
      A.ρ q.1 (-(σ q.2 • A.ρ q.2 y)) -
          (-(σ (q.1 * q.2) • A.ρ (q.1 * q.2) y)) +
          (-(σ q.1 • A.ρ q.1 y)) =
        σ q.1 • A.ρ q.1 (A.ρ q.2 y - y)
    rw [map_neg, map_sub, Rep.ρ_mul]
    simp only [LinearMap.coe_comp, Function.comp_apply]
    rw [hs_add σ q.1 q.2]
    simp only [rho_smul]
    module
  have hmem : (fun q : G × G => σ q.1 • A.ρ q.1 (A.ρ q.2 y - y)) ∈
      groupCohomology.coboundaries₂ A := by
    rw [← hdz]
    change ∃ z' : G → A, (groupCohomology.d₁₂ A).hom z' = dz
    refine ⟨z, ?_⟩
    dsimp [dz]
  exact hmem

private def cup11CocycleToH2 (σ : groupCohomology.cocycles₁ (G := G) (A := ZRep)) :
    groupCohomology.cocycles₁ (G := G) A →+ groupCohomology.H2 (G := G) A :=
  AddMonoidHom.mk'
    (fun τ => groupCohomology.H2π (G := G) A (cup11Cocycle σ τ))
    (by
      intro τ₁ τ₂
      change groupCohomology.H2π (G := G) A (cup11Cocycle σ (τ₁ + τ₂)) =
        groupCohomology.H2π (G := G) A (cup11Cocycle σ τ₁) +
          groupCohomology.H2π (G := G) A (cup11Cocycle σ τ₂)
      rw [cup11Cocycle_add_right, map_add])

private noncomputable def chooseCocycle₁ (A : Rep.{0} ℤ G) (x : groupCohomology.H1 (G := G) A) :
    groupCohomology.cocycles₁ (G := G) A :=
  Classical.choose ((ModuleCat.epi_iff_surjective (groupCohomology.H1π (G := G) A)).mp
    (inferInstance : Epi (groupCohomology.H1π (G := G) A)) x)

private lemma chooseCocycle₁_spec (A : Rep.{0} ℤ G) (x : groupCohomology.H1 (G := G) A) :
    groupCohomology.H1π (G := G) A (chooseCocycle₁ A x) = x :=
  Classical.choose_spec ((ModuleCat.epi_iff_surjective (groupCohomology.H1π (G := G) A)).mp
    (inferInstance : Epi (groupCohomology.H1π (G := G) A)) x)

/-- The `(1,1)` cup product on ordinary degree-one classes. -/
noncomputable def cup11 (x : groupCohomology.H1 (G := G) (Rep.trivial ℤ G ℤ))
    (y : groupCohomology.H1 (G := G) A) : groupCohomology.H2 (G := G) A :=
  cup11CocycleToH2 (chooseCocycle₁ (Rep.trivial ℤ G ℤ) x) (chooseCocycle₁ A y)

private lemma cup11_h2_coboundary_zero
    (σ : groupCohomology.cocycles₁ (G := G) (Rep.trivial ℤ G ℤ))
    {τ : groupCohomology.cocycles₁ (G := G) A}
    (hτ : (τ : G → A) ∈ groupCohomology.coboundaries₁ A) :
    cup11CocycleToH2 σ τ = 0 := by
  rcases hτ with ⟨y, hy⟩
  have hτy : τ = ⟨groupCohomology.d₀₁ A y,
      groupCohomology.d₀₁_apply_mem_cocycles₁ y⟩ := by
    apply Subtype.ext
    exact hy.symm
  rw [hτy]
  apply (groupCohomology.H2π_eq_zero_iff _).2
  exact cup11_right_coboundary σ y

/-- On cocycle representatives, the class-level cup is the explicit inhomogeneous formula. -/
lemma cup11_mk
    (σ : groupCohomology.cocycles₁ (G := G) (Rep.trivial ℤ G ℤ))
    (τ : groupCohomology.cocycles₁ (G := G) A) :
    cup11 (G := G) (groupCohomology.H1π (Rep.trivial ℤ G ℤ) σ)
      (groupCohomology.H1π A τ) =
      groupCohomology.H2π A
        ⟨fun q : G × G => σ q.1 • A.ρ q.1 (τ q.2),
          cup11_mem_cocycles₂ σ τ⟩ := by
  let σ' := chooseCocycle₁ (Rep.trivial ℤ G ℤ) (groupCohomology.H1π (Rep.trivial ℤ G ℤ) σ)
  let τ' := chooseCocycle₁ A (groupCohomology.H1π A τ)
  have hσ : σ' = σ := by
    have hmem := (groupCohomology.H1π_eq_iff σ' σ).1
      (chooseCocycle₁_spec (Rep.trivial ℤ G ℤ) (groupCohomology.H1π (Rep.trivial ℤ G ℤ) σ))
    have : (σ' : G → ℤ) - (σ : G → ℤ) ∈
        (groupCohomology.coboundaries₁ (Rep.trivial ℤ G ℤ)) := by simpa using hmem
    rw [show groupCohomology.coboundaries₁ (Rep.trivial ℤ G ℤ) = ⊥ by
      simpa using groupCohomology.coboundaries₁_eq_bot_of_isTrivial
        (A := Rep.trivial ℤ G ℤ)] at this
    have hz : (σ' : G → ℤ) - (σ : G → ℤ) = 0 := by
      simpa using this
    apply Subtype.ext
    funext g
    exact sub_eq_zero.mp (congrFun hz g)
  have hτmem : ((τ' : G → A) - (τ : G → A)) ∈
      groupCohomology.coboundaries₁ A := by
    have hmem := (groupCohomology.H1π_eq_iff τ' τ).1
      (chooseCocycle₁_spec A (groupCohomology.H1π A τ))
    -- The subtraction in `H1π_eq_iff` is pointwise on the underlying functions.
    change τ'.1 - τ.1 ∈ groupCohomology.coboundaries₁ A
    exact hmem
  have hτzero : cup11CocycleToH2 σ (τ' - τ) = 0 := by
    apply cup11_h2_coboundary_zero σ
    exact hτmem
  have hdecomp : τ' = (τ' - τ) + τ := by abel
  have hclass : cup11CocycleToH2 σ τ' =
      cup11CocycleToH2 σ τ := by
    rw [hdecomp, map_add, hτzero]
    simp
  -- Unfold the two representative choices; the preceding equations identify them with σ and τ.
  simp only [cup11]
  change cup11CocycleToH2 (chooseCocycle₁ (Rep.trivial ℤ G ℤ)
      (groupCohomology.H1π (Rep.trivial ℤ G ℤ) σ))
    (chooseCocycle₁ A (groupCohomology.H1π A τ)) = _
  change cup11CocycleToH2 σ' τ' = _
  rw [hσ, hclass]
  rfl

/-- The explicit `(1,1)` formula is independent of the chosen cocycle representatives. -/
theorem cup11_cocycle_eq_of_H1π_eq
    (σ₁ σ₂ : groupCohomology.cocycles₁ (G := G) (Rep.trivial ℤ G ℤ))
    (τ₁ τ₂ : groupCohomology.cocycles₁ (G := G) A)
    (hσ : groupCohomology.H1π (Rep.trivial ℤ G ℤ) σ₁ =
      groupCohomology.H1π (Rep.trivial ℤ G ℤ) σ₂)
    (hτ : groupCohomology.H1π A τ₁ = groupCohomology.H1π A τ₂) :
    groupCohomology.H2π A
        ⟨fun q : G × G => σ₁ q.1 • A.ρ q.1 (τ₁ q.2),
          cup11_mem_cocycles₂ σ₁ τ₁⟩ =
      groupCohomology.H2π A
        ⟨fun q : G × G => σ₂ q.1 • A.ρ q.1 (τ₂ q.2),
          cup11_mem_cocycles₂ σ₂ τ₂⟩ := by
  rw [← cup11_mk σ₁ τ₁, ← cup11_mk σ₂ τ₂]
  rw [hσ, hτ]

/-- The class-level cup depends only on the two cohomology classes, not on chosen cocycles. -/
theorem cup11_respects_cocycles
    (σ₁ σ₂ : groupCohomology.cocycles₁ (G := G) (Rep.trivial ℤ G ℤ))
    (τ₁ τ₂ : groupCohomology.cocycles₁ (G := G) A)
    (hσ : groupCohomology.H1π (Rep.trivial ℤ G ℤ) σ₁ =
      groupCohomology.H1π (Rep.trivial ℤ G ℤ) σ₂)
    (hτ : groupCohomology.H1π A τ₁ = groupCohomology.H1π A τ₂) :
    cup11 (G := G) (groupCohomology.H1π (Rep.trivial ℤ G ℤ) σ₁)
        (groupCohomology.H1π A τ₁) =
      cup11 (G := G) (groupCohomology.H1π (Rep.trivial ℤ G ℤ) σ₂)
        (groupCohomology.H1π A τ₂) := by
  rw [hσ, hτ]

/-- The `(1,1)` cup is ℤ-linear in its second class argument. -/
theorem cup11_zsmul_right
    (n : ℤ) (x : groupCohomology.H1 (G := G) (Rep.trivial ℤ G ℤ))
    (y : groupCohomology.H1 (G := G) A) :
    cup11 (G := G) x (n • y) = n • cup11 (G := G) x y := by
  let σ : groupCohomology.cocycles₁ (G := G) (Rep.trivial ℤ G ℤ) := chooseCocycle₁ _ x
  let τ : groupCohomology.cocycles₁ (G := G) A := chooseCocycle₁ _ y
  have hσx : groupCohomology.H1π (Rep.trivial ℤ G ℤ) σ = x := by
    exact chooseCocycle₁_spec _ x
  have hτy : groupCohomology.H1π A τ = y := by
    exact chooseCocycle₁_spec _ y
  have hs : groupCohomology.H1π A (n • τ) =
      n • groupCohomology.H1π A τ := by
    exact map_zsmul (ModuleCat.Hom.hom (groupCohomology.H1π A)) n τ
  have hτn : groupCohomology.H1π A (n • τ) = n • y := by
    rw [hs, hτy]
  calc
    cup11 (G := G) x (n • y) =
        cup11 (G := G) (groupCohomology.H1π (Rep.trivial ℤ G ℤ) σ)
          (groupCohomology.H1π A (n • τ)) := by rw [hσx, hτn]
    _ = groupCohomology.H2π A (cup11Cocycle σ (n • τ)) :=
      cup11_mk σ (n • τ)
    _ = groupCohomology.H2π A (n • cup11Cocycle σ τ) := by
      rw [cup11Cocycle_zsmul_right]
    _ = n • groupCohomology.H2π A (cup11Cocycle σ τ) := by
      exact map_zsmul (ModuleCat.Hom.hom (groupCohomology.H2π A)) n (cup11Cocycle σ τ)
    _ = n • cup11 (G := G)
          (groupCohomology.H1π (Rep.trivial ℤ G ℤ) σ) (groupCohomology.H1π A τ) := by
      rw [cup11Cocycle_eq_mk σ τ, cup11_mk]
    _ = n • cup11 (G := G) x y := by
      rw [hσx, hτy]

/-- The `(1,1)` cup is ℤ-linear in its first class argument. -/
theorem cup11_zsmul_left
    (n : ℤ) (x : groupCohomology.H1 (G := G) (Rep.trivial ℤ G ℤ))
    (y : groupCohomology.H1 (G := G) A) :
    cup11 (G := G) (n • x) y = n • cup11 (G := G) x y := by
  let σ : groupCohomology.cocycles₁ (G := G) (Rep.trivial ℤ G ℤ) := chooseCocycle₁ _ x
  let τ : groupCohomology.cocycles₁ (G := G) A := chooseCocycle₁ _ y
  have hσx : groupCohomology.H1π (Rep.trivial ℤ G ℤ) σ = x := by
    exact chooseCocycle₁_spec _ x
  have hτy : groupCohomology.H1π A τ = y := by
    exact chooseCocycle₁_spec _ y
  have hs : groupCohomology.H1π (Rep.trivial ℤ G ℤ) (n • σ) =
      n • groupCohomology.H1π (Rep.trivial ℤ G ℤ) σ := by
    exact map_zsmul (ModuleCat.Hom.hom (groupCohomology.H1π (Rep.trivial ℤ G ℤ))) n σ
  have hσn : groupCohomology.H1π (Rep.trivial ℤ G ℤ) (n • σ) = n • x := by
    rw [hs, hσx]
  calc
    cup11 (G := G) (n • x) y =
        cup11 (G := G) (groupCohomology.H1π (Rep.trivial ℤ G ℤ) (n • σ))
          (groupCohomology.H1π A τ) := by rw [hσn, hτy]
    _ = groupCohomology.H2π A (cup11Cocycle (n • σ) τ) :=
      cup11_mk (n • σ) τ
    _ = groupCohomology.H2π A (n • cup11Cocycle σ τ) := by
      rw [cup11Cocycle_zsmul_left]
    _ = n • groupCohomology.H2π A (cup11Cocycle σ τ) := by
      exact map_zsmul (ModuleCat.Hom.hom (groupCohomology.H2π A)) n (cup11Cocycle σ τ)
    _ = n • cup11 (G := G)
          (groupCohomology.H1π (Rep.trivial ℤ G ℤ) σ) (groupCohomology.H1π A τ) := by
      rw [cup11Cocycle_eq_mk σ τ, cup11_mk]
    _ = n • cup11 (G := G) x y := by
      rw [hσx, hτy]

/-- The `(1,1)` cup is additive in its first class argument. -/
theorem cup11_add_left
    (x x' : groupCohomology.H1 (G := G) (Rep.trivial ℤ G ℤ))
    (y : groupCohomology.H1 (G := G) A) :
    cup11 (G := G) (x + x') y = cup11 (G := G) x y + cup11 (G := G) x' y := by
  let σ : groupCohomology.cocycles₁ (G := G) (Rep.trivial ℤ G ℤ) := chooseCocycle₁ _ x
  let σ' : groupCohomology.cocycles₁ (G := G) (Rep.trivial ℤ G ℤ) := chooseCocycle₁ _ x'
  let τ : groupCohomology.cocycles₁ (G := G) A := chooseCocycle₁ _ y
  have hσx : groupCohomology.H1π (Rep.trivial ℤ G ℤ) σ = x := by
    exact chooseCocycle₁_spec _ x
  have hσx' : groupCohomology.H1π (Rep.trivial ℤ G ℤ) σ' = x' := by
    exact chooseCocycle₁_spec _ x'
  have hτy : groupCohomology.H1π A τ = y := by
    exact chooseCocycle₁_spec _ y
  have hσ : groupCohomology.H1π (Rep.trivial ℤ G ℤ) (σ + σ') = x + x' := by
    rw [map_add, hσx, hσx']
  -- Compare the class representatives with the sum, then use the cochain additivity law.
  calc
    cup11 (G := G) (x + x') y =
        cup11 (G := G) (groupCohomology.H1π (Rep.trivial ℤ G ℤ) (σ + σ'))
          (groupCohomology.H1π A τ) := by simp only [hσ, hτy]
    _ = groupCohomology.H2π A (cup11Cocycle (σ + σ') τ) :=
      cup11_mk (σ + σ') τ
    _ = groupCohomology.H2π A (cup11Cocycle σ τ) +
        groupCohomology.H2π A (cup11Cocycle σ' τ) := by
          rw [cup11Cocycle_add_left, map_add]
    _ = cup11 (G := G) (groupCohomology.H1π (Rep.trivial ℤ G ℤ) σ)
          (groupCohomology.H1π A τ) +
        cup11 (G := G) (groupCohomology.H1π (Rep.trivial ℤ G ℤ) σ')
          (groupCohomology.H1π A τ) := by
          rw [cup11Cocycle_eq_mk σ τ, cup11Cocycle_eq_mk σ' τ]
          have h₁ : groupCohomology.H2π A
                ⟨fun q : G × G => σ q.1 • A.ρ q.1 (τ q.2),
                  cup11_mem_cocycles₂ σ τ⟩ =
              cup11 (G := G)
                (groupCohomology.H1π (Rep.trivial ℤ G ℤ) σ)
                (groupCohomology.H1π A τ) := (cup11_mk σ τ).symm
          have h₂ : groupCohomology.H2π A
                ⟨fun q : G × G => σ' q.1 • A.ρ q.1 (τ q.2),
                  cup11_mem_cocycles₂ σ' τ⟩ =
              cup11 (G := G)
                (groupCohomology.H1π (Rep.trivial ℤ G ℤ) σ')
                (groupCohomology.H1π A τ) := (cup11_mk σ' τ).symm
          exact congrArg₂ (fun u v => u + v) h₁ h₂
    _ = cup11 (G := G) x y + cup11 (G := G) x' y := by
      calc
        cup11 (G := G) (groupCohomology.H1π (Rep.trivial ℤ G ℤ) σ)
              (groupCohomology.H1π A τ) +
            cup11 (G := G) (groupCohomology.H1π (Rep.trivial ℤ G ℤ) σ')
              (groupCohomology.H1π A τ) =
            cup11 (G := G) x (groupCohomology.H1π A τ) +
              cup11 (G := G) x' (groupCohomology.H1π A τ) := by
                rw [hσx, hσx']
        _ = cup11 (G := G) x y + cup11 (G := G) x' y := by
          rw [hτy]

/-- The `(1,1)` cup is additive in its second class argument. -/
theorem cup11_add_right
    (x : groupCohomology.H1 (G := G) (Rep.trivial ℤ G ℤ))
    (y y' : groupCohomology.H1 (G := G) A) :
    cup11 (G := G) x (y + y') = cup11 (G := G) x y + cup11 (G := G) x y' := by
  let σ : groupCohomology.cocycles₁ (G := G) (Rep.trivial ℤ G ℤ) := chooseCocycle₁ _ x
  let τ : groupCohomology.cocycles₁ (G := G) A := chooseCocycle₁ _ y
  let τ' : groupCohomology.cocycles₁ (G := G) A := chooseCocycle₁ _ y'
  have hσx : groupCohomology.H1π (Rep.trivial ℤ G ℤ) σ = x := by
    exact chooseCocycle₁_spec _ x
  have hτy : groupCohomology.H1π A τ = y := by
    exact chooseCocycle₁_spec _ y
  have hτy' : groupCohomology.H1π A τ' = y' := by
    exact chooseCocycle₁_spec _ y'
  have hτ : groupCohomology.H1π A (τ + τ') = y + y' := by
    rw [map_add, hτy, hτy']
  -- The right-variable proof mirrors the left-variable proof, using the same
  -- representative choices.
  calc
    cup11 (G := G) x (y + y') =
        cup11 (G := G) (groupCohomology.H1π (Rep.trivial ℤ G ℤ) σ)
          (groupCohomology.H1π A (τ + τ')) := by rw [hσx, hτ]
    _ = groupCohomology.H2π A (cup11Cocycle σ (τ + τ')) :=
      cup11_mk σ (τ + τ')
    _ = groupCohomology.H2π A (cup11Cocycle σ τ) +
        groupCohomology.H2π A (cup11Cocycle σ τ') := by
          rw [cup11Cocycle_add_right, map_add]
    _ = cup11 (G := G) (groupCohomology.H1π (Rep.trivial ℤ G ℤ) σ)
          (groupCohomology.H1π A τ) +
        cup11 (G := G) (groupCohomology.H1π (Rep.trivial ℤ G ℤ) σ)
          (groupCohomology.H1π A τ') := by
          rw [cup11Cocycle_eq_mk σ τ, cup11Cocycle_eq_mk σ τ']
          exact congrArg₂ (fun u v => u + v) (cup11_mk σ τ).symm
            (cup11_mk σ τ').symm
    _ = cup11 (G := G) x y + cup11 (G := G) x y' := by
      calc
        cup11 (G := G) (groupCohomology.H1π (Rep.trivial ℤ G ℤ) σ)
              (groupCohomology.H1π A τ) +
            cup11 (G := G) (groupCohomology.H1π (Rep.trivial ℤ G ℤ) σ)
              (groupCohomology.H1π A τ') =
            cup11 (G := G) x (groupCohomology.H1π A τ) +
              cup11 (G := G) x (groupCohomology.H1π A τ') := by
                rw [hσx]
        _ = cup11 (G := G) x y + cup11 (G := G) x y' := by
          rw [hτy, hτy']

/-- The `(1,1)` cup vanishes when its first class argument is zero. -/
theorem cup11_zero_left (y : groupCohomology.H1 (G := G) A) :
    cup11 (G := G) (0 : groupCohomology.H1 (G := G) (Rep.trivial ℤ G ℤ)) y = 0 := by
  have h := cup11_add_left (G := G) (x := 0) (x' := 0) y
  simpa using h

/-- The `(1,1)` cup vanishes when its second class argument is zero. -/
theorem cup11_zero_right
    (x : groupCohomology.H1 (G := G) (Rep.trivial ℤ G ℤ)) :
    cup11 (G := G) x (0 : groupCohomology.H1 (G := G) A) = 0 := by
  have h := cup11_add_right (G := G) (A := A) x (y := 0) (y' := 0)
  simpa using h

end TauCeti.groupCohomology

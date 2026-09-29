/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Invariants

/-!
# Tensoring a representation with an invariant

For an invariant `y` of a representation `N`, this file constructs the morphism of
representations `M ⟶ M ⊗ N` that sends `m` to `m ⊗ₜ y`. It also records its additivity,
linearity, and naturality in both representations.
-/

public noncomputable section

universe u

open CategoryTheory MonoidalCategory
open scoped TensorProduct

namespace Rep

variable {k G : Type u} [CommRing k] [Group G]

/-- For an invariant `y` of the representation `N`, the morphism of representations
`M ⟶ M ⊗ N`, `m ↦ m ⊗ₜ y`. -/
def tensorInvariant (M : Rep k G) {N : Rep k G} (y : N.ρ.invariants) : M ⟶ M ⊗ N :=
  Rep.ofHom <| ((TensorProduct.mk k M.V N.V).flip y).intertwiningMap_of_isIntertwiningMap
    (ρ := M.ρ) (σ := (M ⊗ N).ρ) fun g m ↦ by
      simp [Representation.tprod_apply, y.2 g]

-- `simp` rewrites the carrier `(M ⊗ N).V` to `M.V ⊗[k] N.V` in the implicit arguments of the
-- left-hand side before it looks a term up, so the left-hand side is stated in that form through
-- `dsimp%`, as in #8315.
/-- The morphism `m ↦ m ⊗ₜ y` evaluated at `m`. -/
@[simp]
theorem tensorInvariant_hom_apply (M : Rep k G) {N : Rep k G} (y : N.ρ.invariants) (m : M.V) :
    (dsimp% ((tensorInvariant M y).hom m)) = m ⊗ₜ[k] (y : N.V) :=
  (rfl)

variable (M : Rep k G) {N : Rep k G}

/-- `m ↦ m ⊗ 0` is the zero morphism. -/
@[simp]
theorem tensorInvariant_zero : tensorInvariant M (0 : N.ρ.invariants) = 0 := by
  ext m
  simp

/-- `m ↦ m ⊗ y` is additive in `y`. -/
@[simp]
theorem tensorInvariant_add (y z : N.ρ.invariants) :
    tensorInvariant M (y + z) = tensorInvariant M y + tensorInvariant M z := by
  ext m
  simp [Rep.add_hom, TensorProduct.tmul_add]

/-- `m ↦ m ⊗ y` is `k`-linear in `y`. -/
@[simp]
theorem tensorInvariant_smul (c : k) (y : N.ρ.invariants) :
    tensorInvariant M (c • y) = c • tensorInvariant M y := by
  ext m
  simp [Rep.smul_hom]

/-- `m ↦ m ⊗ y` is natural in `M`. -/
@[reassoc]
theorem hom_comp_tensorInvariant {M' : Rep k G} (f : M ⟶ M') (y : N.ρ.invariants) :
    f ≫ tensorInvariant M' y = tensorInvariant M y ≫ f ▷ N := by
  ext m
  simp

/-- After braiding, tensoring with an invariant is natural in the other factor. -/
@[reassoc]
theorem hom_comp_tensorInvariant_braiding {M' : Rep k G} (f : M ⟶ M')
    {P : Rep k G} (x : P.ρ.invariants) :
    f ≫ tensorInvariant M' x ≫ (β_ M' P).hom =
      tensorInvariant M x ≫ (β_ M P).hom ≫ P ◁ f := by
  rw [← Category.assoc, hom_comp_tensorInvariant, Category.assoc,
    BraidedCategory.braiding_naturality_left]

/-- `m ↦ m ⊗ y` is natural in `N`: composing with `M ◁ g` gives `m ↦ m ⊗ g y`. -/
theorem tensorInvariant_comp_whiskerLeft {N' : Rep k G} (g : N ⟶ N') (y : N.ρ.invariants)
    (y' : N'.ρ.invariants) (hy : g.hom y = y') :
    tensorInvariant M y ≫ M ◁ g = tensorInvariant M y' := by
  ext m
  simp [hy]

end Rep

namespace TauCeti.Rep

variable {k G : Type u} [CommRing k] [Group G] {M N : _root_.Rep k G}

/-- Braiding the tensor of a vector with an invariant puts the invariant first. -/
theorem tensorInvariant_braiding_hom_apply (x : M.ρ.invariants) (y : N.V) :
    (((_root_.Rep.tensorInvariant N x) ≫ (β_ N M).hom).hom y) =
      (x : M.V) ⊗ₜ[k] y := by
  simp [_root_.Rep.hom_braiding]

/-- Restricting `y ↦ x ⊗ₜ y` along a monoid homomorphism gives the same map for the restricted
representations, tensoring with `x` viewed as an invariant of the restriction. -/
theorem resMap_tensorInvariant_braiding (N : _root_.Rep k G) {H : Type u} [Group H] (f : H →* G)
    (x : M.ρ.invariants) (x' : (_root_.Rep.res f M).ρ.invariants) (hx : (x' : M.V) = x) :
    _root_.Rep.resMap f (_root_.Rep.tensorInvariant N x ≫ (β_ N M).hom) =
      _root_.Rep.tensorInvariant (_root_.Rep.res f N) x' ≫
        (β_ (_root_.Rep.res f N) (_root_.Rep.res f M)).hom := by
  ext y
  -- Restriction keeps the underlying linear map, so both sides are evaluations of
  -- `tensorInvariant_braiding_hom_apply`.
  exact (tensorInvariant_braiding_hom_apply x y).trans
    ((congrArg (· ⊗ₜ[k] y) hx.symm).trans (tensorInvariant_braiding_hom_apply x' y).symm)

end TauCeti.Rep

namespace Rep

variable {k G : Type u} [CommRing k] [Group G]

/-- Tensoring with the invariant `1` of the trivial representation, then braiding and applying
the left unitor, is the identity. -/
@[simp]
theorem tensorInvariant_one_braiding_leftUnitor (M : Rep k G) :
    tensorInvariant M (⟨1, by simp [Representation.invariants]⟩ :
      (Rep.trivial k G k).ρ.invariants) ≫
      (β_ M (Rep.trivial k G k)).hom ≫ (λ_ M).hom = 𝟙 M := by
  have h : tensorInvariant M (⟨1, by simp [Representation.invariants]⟩ :
      (Rep.trivial k G k).ρ.invariants) = (ρ_ M).inv := by
    ext x
    rw [Rep.hom_inv_rightUnitor]
    exact tensorInvariant_hom_apply M _ x
  rw [h]
  -- `braiding_leftUnitor` is stated for the monoidal unit. Mathlib's `Rep` monoidal instance
  -- defines that unit as `Rep.trivial k G k`; `change` checks precisely this definitional equality.
  change (ρ_ M).inv ≫ (β_ M (𝟙_ (Rep k G))).hom ≫ (λ_ M).hom = 𝟙 M
  rw [braiding_leftUnitor, Iso.inv_hom_id]

end Rep

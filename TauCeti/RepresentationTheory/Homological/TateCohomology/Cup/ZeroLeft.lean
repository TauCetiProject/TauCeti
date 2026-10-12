/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.RepresentationTheory.Homological.TateCohomology.Cup.DegreeZero

/-!
# The Tate cup product with a degree-zero class in the first factor

The degree-zero cup product in the second factor also gives a product with a degree-zero
class in the first factor. The symmetry of the tensor product of representations transports
the existing product without introducing a second cohomological construction. Its value on
classes represented by invariants is the class of the elementary tensor in the stated order.

This is the `(0,n)` edge of the all-bidegree Tate cup product used in Tate's theorem.
Its compatibility with connecting maps is the left-factor/braided analogue of `δ_cupH0`.

## References

* J. W. S. Cassels and A. Fröhlich (eds.), *Algebraic Number Theory*, Chapter IV (Atiyah–Wall),
  §7.
-/

public noncomputable section

universe u

open CategoryTheory Limits MonoidalCategory
open scoped TensorProduct

namespace TauCeti.TateCohomology

variable {k G : Type u} [CommRing k] [Group G] [Fintype G] {M N : Rep k G}

/-- Cup product with a degree-zero class in the first factor. It is the degree-zero product
in the second factor followed by the symmetry `N ⊗ M ≅ M ⊗ N`. -/
def cup0H (M N : Rep k G) (n : ℤ) :
    tateCohomology M 0 →ₗ[k] tateCohomology N n →ₗ[k] tateCohomology (M ⊗ N) n where
  toFun x := ((tateCohomologyFunctor n).map (β_ N M).hom).hom.comp
    (LinearMap.flip (cupH0 N M n) x)
  map_add' x y := by
    ext z
    simp [LinearMap.flip_apply]
  map_smul' c x := by
    ext z
    simp [LinearMap.flip_apply]

/-- The left degree-zero product is the right degree-zero product followed by the
symmetry of coefficients. -/
theorem cup0H_apply (n : ℤ) (x : tateCohomology M 0) (y : tateCohomology N n) :
    cup0H M N n x y =
      (tateCohomologyFunctor n).map (β_ N M).hom (cupH0 N M n y x) :=
  by simp [cup0H, LinearMap.flip_apply]

/-- For an invariant `x`, the left cup product is induced by `y ↦ x ⊗ y`. -/
@[simp]
theorem cup0H_H0π (n : ℤ) (x : M.ρ.invariants) (y : tateCohomology N n) :
    (dsimp% only (cup0H M N n (H0π M x) y)) =
      (tateCohomologyFunctor n).map
        ((Rep.tensorInvariant N x) ≫ (β_ N M).hom) y := by
  rw [cup0H_apply, cupH0_H0π, ← ModuleCat.comp_apply, ← Functor.map_comp]

/-- In bidegree `(0,0)`, the product is represented by the tensor of the two
invariants in their original order. -/
@[simp high]
theorem cup0H_H0π_H0π (x : M.ρ.invariants) (y : N.ρ.invariants) :
    (dsimp% only (cup0H M N 0 (H0π M x) (H0π N y))) =
      H0π (M ⊗ N) ⟨(x : M.V) ⊗ₜ[k] (y : N.V), fun g ↦ by
        simp [Representation.tprod_apply, x.2 g, y.2 g]⟩ := by
  rw [cup0H_H0π, H0π_comp_tateCohomologyFunctor_map_apply]
  apply congrArg (H0π (M ⊗ N))
  apply Subtype.ext
  exact TauCeti.Rep.tensorInvariant_braiding_hom_apply x (y : N.V)

variable (M N) in
/-- In bidegree `(0, 0)` the product with a degree-zero class in the first factor is the product
with a degree-zero class in the second factor. -/
theorem cup0H_zero : cup0H M N 0 = cupH0 M N 0 := by
  ext x y
  induction x using H0_induction_on with
  | h x =>
    induction y using H0_induction_on with
    | h y => simp

/-- Naturality of the left degree-zero product in its first coefficient. -/
theorem cup0H_map_left {M' : Rep k G} (f : M ⟶ M') (n : ℤ)
    (x : tateCohomology M 0) (y : tateCohomology N n) :
    cup0H M' N n ((tateCohomologyFunctor 0).map f x) y =
      (tateCohomologyFunctor n).map (f ▷ N) (cup0H M N n x y) := by
  rw [cup0H_apply, cup0H_apply, cupH0_map_right]
  rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, ← Functor.map_comp,
    ← Functor.map_comp]
  congr 1
  rw [BraidedCategory.braiding_naturality_right N f]

/-- Naturality of the left degree-zero product in its second coefficient. -/
theorem cup0H_map_right {N' : Rep k G} (g : N ⟶ N') (n : ℤ)
    (x : tateCohomology M 0) (y : tateCohomology N n) :
    cup0H M N' n x ((tateCohomologyFunctor n).map g y) =
      (tateCohomologyFunctor n).map (M ◁ g) (cup0H M N n x y) := by
  rw [cup0H_apply, cup0H_apply, cupH0_map_left]
  rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, ← Functor.map_comp,
    ← Functor.map_comp]
  congr 1
  rw [BraidedCategory.braiding_naturality_left g M]

/-- Cup product with a degree-zero class in the first factor commutes with the connecting map
in the second factor, provided tensoring the short exact sequence with that first factor
preserves exactness. This is the left-factor/braided analogue of `δ_cupH0`. -/
theorem δ_cup0H (M : Rep k G) {S : ShortComplex (Rep k G)} (hS : S.ShortExact)
    (hMS : (S.map (tensorLeft M)).ShortExact) (n : ℤ)
    (x : tateCohomology M 0) (y : tateCohomology S.X₃ n) :
    _root_.TateCohomology.δ hMS n (cup0H M S.X₃ n x y) =
      cup0H M S.X₁ (n + 1) x (_root_.TateCohomology.δ hS n y) := by
  induction x using H0_induction_on with
  | h x =>
    let F : S ⟶ S.map (tensorLeft M) :=
      { τ₁ := Rep.tensorInvariant S.X₁ x ≫ (β_ S.X₁ M).hom
        τ₂ := Rep.tensorInvariant S.X₂ x ≫ (β_ S.X₂ M).hom
        τ₃ := Rep.tensorInvariant S.X₃ x ≫ (β_ S.X₃ M).hom
        comm₁₂ := by simpa using (Rep.hom_comp_tensorInvariant_braiding S.X₁ S.f x).symm
        comm₂₃ := by simpa using (Rep.hom_comp_tensorInvariant_braiding S.X₂ S.g x).symm }
    rw [cup0H_H0π, cup0H_H0π, ← ModuleCat.comp_apply, ← ModuleCat.comp_apply]
    exact congrArg (fun φ ↦ φ y) (_root_.TateCohomology.δ_naturality hS hMS F n).symm

end TauCeti.TateCohomology

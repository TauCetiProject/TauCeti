/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.RestrictedProduct.Map

/-!
# Changing the factors of a restricted product

A family of multiplicative equivalences induces an equivalence of restricted products when it
carries the reference subgroups bijectively onto one another at all but finitely many indices.
The `Set.BijOn` hypothesis supplies both the forward and inverse restrictedness conditions; a
one-sided `Set.MapsTo` hypothesis would only produce a homomorphism in one direction. It cannot be
weakened: for coordinatewise equivalences that eventually map the reference subgroups into one
another, the induced homomorphism is surjective exactly when they are eventually bijections of
the reference subgroups, and the file ends with a family of identity maps for which it is not.

The algebraic construction is adapted from `MulEquiv.restrictedProductCongrRight` in the FLT
project (`ImperialCollegeLondon/FLT`, file
`FLT/Mathlib/Topology/Algebra/RestrictedProduct/Equiv.lean`, source commit
`a9efe585de92be60be84ac1d14ced5a1b0944333`, Apache 2.0), by Kevin Buzzard and Salvatore
Mercuri. The continuity results are the two directions of FLT's
`ContinuousMulEquiv.restrictedProductCongrRight`.

## References

* N. Bourbaki, *General Topology*.
* A. Weil, *Basic Number Theory*.
-/

public section

namespace TauCeti

open Filter
open scoped RestrictedProduct

universe u v w

variable {ι : Type u} {G : ι → Type v}
variable [∀ i, Group (G i)]

/-- The multiplicative equivalence of restricted products induced by coordinatewise equivalences
that eventually carry the reference subgroups bijectively onto one another. -/
def restrictedProductCongrRight {H : ι → Type w} [∀ i, Group (H i)]
    (U : ∀ i, Subgroup (G i)) (U' : ∀ i, Subgroup (H i))
    (φ : ∀ i, G i ≃* H i)
    (hφ : ∀ᶠ i in cofinite, Set.BijOn (φ i) (U i) (U' i)) :
    (Πʳ i, [G i, (U i : Set (G i))]) ≃*
      (Πʳ i, [H i, (U' i : Set (H i))]) where
  toFun x := ⟨fun i ↦ φ i (x i), by
    filter_upwards [x.2, hφ] with i hx hi using hi.mapsTo hx⟩
  invFun y := ⟨fun i ↦ (φ i).symm (y i), by
    filter_upwards [y.2, hφ] with i hy hi using hi.equiv_symm.mapsTo hy⟩
  left_inv x := by
    ext i
    exact (φ i).symm_apply_apply (x i)
  right_inv y := by
    ext i
    exact (φ i).apply_symm_apply (y i)
  map_mul' x y := by
    ext i
    exact map_mul (φ i) (x i) (y i)

/-- The forward change-of-factors equivalence applies the given equivalence in each coordinate. -/
@[simp]
theorem restrictedProductCongrRight_apply {H : ι → Type w} [∀ i, Group (H i)]
    (U : ∀ i, Subgroup (G i)) (U' : ∀ i, Subgroup (H i))
    (φ : ∀ i, G i ≃* H i)
    (hφ : ∀ᶠ i in cofinite, Set.BijOn (φ i) (U i) (U' i))
    (x : Πʳ i, [G i, (U i : Set (G i))]) (i : ι) :
    restrictedProductCongrRight U U' φ hφ x i = φ i (x i) := by
  rfl

/-- The inverse change-of-factors equivalence applies the inverse equivalence in each coordinate. -/
@[simp]
theorem restrictedProductCongrRight_symm_apply {H : ι → Type w} [∀ i, Group (H i)]
    (U : ∀ i, Subgroup (G i)) (U' : ∀ i, Subgroup (H i))
    (φ : ∀ i, G i ≃* H i)
    (hφ : ∀ᶠ i in cofinite, Set.BijOn (φ i) (U i) (U' i))
    (y : Πʳ i, [H i, (U' i : Set (H i))]) (i : ι) :
    (restrictedProductCongrRight U U' φ hφ).symm y i = (φ i).symm (y i) := by
  rfl

/-- The forward change-of-factors equivalence is continuous when its coordinate maps are
continuous. -/
theorem continuous_restrictedProductCongrRight {H : ι → Type w} [∀ i, Group (H i)]
    [∀ i, TopologicalSpace (G i)] [∀ i, TopologicalSpace (H i)]
    (U : ∀ i, Subgroup (G i)) (U' : ∀ i, Subgroup (H i))
    (φ : ∀ i, G i ≃* H i)
    (hφ : ∀ᶠ i in cofinite, Set.BijOn (φ i) (U i) (U' i))
    (hcont : ∀ i, Continuous (φ i)) :
    Continuous (restrictedProductCongrRight U U' φ hφ) := by
  convert continuous_restrictedProductMap U U' (fun i ↦ (φ i).toMonoidHom)
    (hφ.mono fun _ hi ↦ hi.mapsTo) hcont using 1
  ext x i
  simp

/-- The inverse change-of-factors equivalence is continuous when the inverse coordinate maps are
continuous. -/
theorem continuous_restrictedProductCongrRight_symm {H : ι → Type w} [∀ i, Group (H i)]
    [∀ i, TopologicalSpace (G i)] [∀ i, TopologicalSpace (H i)]
    (U : ∀ i, Subgroup (G i)) (U' : ∀ i, Subgroup (H i))
    (φ : ∀ i, G i ≃* H i)
    (hφ : ∀ᶠ i in cofinite, Set.BijOn (φ i) (U i) (U' i))
    (hcont : ∀ i, Continuous (φ i).symm) :
    Continuous (restrictedProductCongrRight U U' φ hφ).symm := by
  convert continuous_restrictedProductMap U' U (fun i ↦ (φ i).symm.toMonoidHom)
    (hφ.mono fun _ hi ↦ hi.equiv_symm.mapsTo) hcont using 1
  ext y i
  simp

/-- For coordinatewise equivalences that eventually map the reference subgroups into one another,
the induced homomorphism of restricted products is surjective exactly when the equivalences are
eventually bijections of the reference subgroups. So the `Set.BijOn` hypothesis of
`restrictedProductCongrRight` is not only sufficient but necessary. -/
theorem surjective_restrictedProductMap_iff_eventually_bijOn {H : ι → Type w}
    [∀ i, Group (H i)] (U : ∀ i, Subgroup (G i)) (U' : ∀ i, Subgroup (H i))
    (φ : ∀ i, G i ≃* H i)
    (hφ : ∀ᶠ i in cofinite, Set.MapsTo (φ i) (U i) (U' i)) :
    Function.Surjective (restrictedProductMap U U' (fun i ↦ (φ i).toMonoidHom) hφ) ↔
      ∀ᶠ i in cofinite, Set.BijOn (φ i) (U i) (U' i) := by
  refine (surjective_restrictedProductMap_iff U U' _ hφ).trans
    ⟨fun h ↦ ?_, fun h ↦ ⟨fun i ↦ (φ i).surjective, h.mono fun _ hi ↦ hi.surjOn⟩⟩
  filter_upwards [hφ, h.2] with i hmaps hsurj
  exact ⟨hmaps, (φ i).injective.injOn, hsurj⟩

/-- Coordinatewise equivalences that merely map the reference subgroups into one another need not
induce an equivalence of restricted products. The witness uses identity maps on
`Multiplicative ℤ`, with every source reference subgroup `⊥` and every target reference subgroup
`⊤`: the induced map is the inclusion of the finitely supported elements into the full product,
which is not surjective. -/
theorem not_forall_surjective_restrictedProductMap :
    ¬ ∀ (U U' : ℕ → Subgroup (Multiplicative ℤ))
        (φ : ∀ _ : ℕ, Multiplicative ℤ ≃* Multiplicative ℤ)
        (hφ : ∀ᶠ i in cofinite, Set.MapsTo (φ i) (U i) (U' i)),
        Function.Surjective (restrictedProductMap U U' (fun i ↦ (φ i).toMonoidHom) hφ) := by
  intro h
  have hbij := (surjective_restrictedProductMap_iff_eventually_bijOn (fun _ ↦ ⊥) (fun _ ↦ ⊤)
    (fun _ ↦ MulEquiv.refl _) (.of_forall fun _ _ _ ↦ Subgroup.mem_top _)).mp (h _ _ _ _)
  obtain ⟨i, hi⟩ := hbij.exists
  obtain ⟨a, ha, hae⟩ := hi.surjOn (Subgroup.mem_top (Multiplicative.ofAdd (1 : ℤ)))
  rw [SetLike.mem_coe, Subgroup.mem_bot] at ha
  rw [ha, map_one, eq_comm, ofAdd_eq_one] at hae
  exact one_ne_zero hae

end TauCeti

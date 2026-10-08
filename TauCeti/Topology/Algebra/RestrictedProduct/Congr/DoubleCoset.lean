/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.RestrictedProduct.Congr.Basic
public import TauCeti.GroupTheory.DoubleCoset.Map

/-!
# Change of reference family and double cosets

A componentwise multiplicative equivalence which eventually carries one reference family
bijectively to another gives an equivalence of the ambient restricted products. The induced
bijection on double-coset spaces is `doubleCosetCongrRight`.

For the coordinatewise identity comparison, `restrictedProductCongr` identifies the ambient
restricted products only. It need not carry the everywhere-integral subgroup of one family onto
that of the other; the counterexample `exists_map_integralSubgroup_ne` is recorded alongside the
isomorphism in `TauCeti.Topology.Algebra.RestrictedProduct.Congr.Basic`. For this reason
`doubleCosetCongr` is stated along the transported subgroups rather than along the integral
subgroup of the new family.

## References

* A. Weil, *Basic Number Theory*.
-/

public section

namespace TauCeti

open Filter
open scoped RestrictedProduct

universe u v w

variable {ι : Type u} {G : ι → Type v}
variable [∀ i, Group (G i)]

/-- Transport of a double-coset space along a componentwise equivalence of restricted products.
The subgroups on the right are the images of the subgroups on the left. -/
def doubleCosetCongrRight {H : ι → Type w} [∀ i, Group (H i)]
    (U : ∀ i, Subgroup (G i)) (U' : ∀ i, Subgroup (H i))
    (φ : ∀ i, G i ≃* H i)
    (hφ : ∀ᶠ i in cofinite, Set.BijOn (φ i) (U i) (U' i))
    (Γ K : Subgroup (Πʳ i, [G i, (U i : Set (G i))])) :
    DoubleCoset.Quotient (Γ : Set (Πʳ i, [G i, (U i : Set (G i))])) K ≃
      DoubleCoset.Quotient
        (Γ.map (restrictedProductCongrRight U U' φ hφ :
            (Πʳ i, [G i, (U i : Set (G i))]) →* Πʳ i, [H i, (U' i : Set (H i))]) :
          Set (Πʳ i, [H i, (U' i : Set (H i))]))
        (K.map (restrictedProductCongrRight U U' φ hφ :
            (Πʳ i, [G i, (U i : Set (G i))]) →* Πʳ i, [H i, (U' i : Set (H i))]) :
          Set (Πʳ i, [H i, (U' i : Set (H i))])) :=
  DoubleCoset.quotientCongr Γ K (restrictedProductCongrRight U U' φ hφ) rfl rfl

/-- The transported double-coset space sends the class of `x` to the class of the
componentwise image of `x`. -/
theorem doubleCosetCongrRight_apply_mk {H : ι → Type w} [∀ i, Group (H i)]
    (U : ∀ i, Subgroup (G i)) (U' : ∀ i, Subgroup (H i))
    (φ : ∀ i, G i ≃* H i)
    (hφ : ∀ᶠ i in cofinite, Set.BijOn (φ i) (U i) (U' i))
    (Γ K : Subgroup (Πʳ i, [G i, (U i : Set (G i))]))
    (x : Πʳ i, [G i, (U i : Set (G i))]) :
    doubleCosetCongrRight U U' φ hφ Γ K (DoubleCoset.mk Γ K x) =
      DoubleCoset.mk
        (Γ.map (restrictedProductCongrRight U U' φ hφ :
          (Πʳ i, [G i, (U i : Set (G i))]) →* Πʳ i, [H i, (U' i : Set (H i))]))
        (K.map (restrictedProductCongrRight U U' φ hφ :
          (Πʳ i, [G i, (U i : Set (G i))]) →* Πʳ i, [H i, (U' i : Set (H i))]))
        (restrictedProductCongrRight U U' φ hφ x) :=
  DoubleCoset.quotientCongr_apply_mk Γ K _ rfl rfl x

/-- The inverse transport sends the class of `y` to the class of its componentwise inverse
image. -/
theorem doubleCosetCongrRight_symm_apply_mk {H : ι → Type w} [∀ i, Group (H i)]
    (U : ∀ i, Subgroup (G i)) (U' : ∀ i, Subgroup (H i))
    (φ : ∀ i, G i ≃* H i)
    (hφ : ∀ᶠ i in cofinite, Set.BijOn (φ i) (U i) (U' i))
    (Γ K : Subgroup (Πʳ i, [G i, (U i : Set (G i))]))
    (y : Πʳ i, [H i, (U' i : Set (H i))]) :
    (doubleCosetCongrRight U U' φ hφ Γ K).symm
        (DoubleCoset.mk
          (Γ.map (restrictedProductCongrRight U U' φ hφ :
            (Πʳ i, [G i, (U i : Set (G i))]) →* Πʳ i, [H i, (U' i : Set (H i))]))
          (K.map (restrictedProductCongrRight U U' φ hφ :
            (Πʳ i, [G i, (U i : Set (G i))]) →* Πʳ i, [H i, (U' i : Set (H i))]))
          y) =
      DoubleCoset.mk Γ K ((restrictedProductCongrRight U U' φ hφ).symm y) :=
  DoubleCoset.quotientCongr_symm_apply_mk Γ K _ rfl rfl y

/-- Transport of a double-coset space along a change of reference family. The subgroups on the
right are the images of those on the left under `restrictedProductCongr`, not the integral
subgroups of the new family; see `exists_map_integralSubgroup_ne`. -/
def doubleCosetCongr (U U' : ∀ i, Subgroup (G i))
    (h : ∀ᶠ i in cofinite, U i = U' i)
    (Γ K : Subgroup (Πʳ i, [G i, (U i : Set (G i))])) :
    DoubleCoset.Quotient (Γ : Set (Πʳ i, [G i, (U i : Set (G i))])) K ≃
      DoubleCoset.Quotient
        (Γ.map (restrictedProductCongr U U' h :
            (Πʳ i, [G i, (U i : Set (G i))]) →* Πʳ i, [G i, (U' i : Set (G i))]) :
          Set (Πʳ i, [G i, (U' i : Set (G i))]))
        (K.map (restrictedProductCongr U U' h :
            (Πʳ i, [G i, (U i : Set (G i))]) →* Πʳ i, [G i, (U' i : Set (G i))]) :
          Set (Πʳ i, [G i, (U' i : Set (G i))])) :=
  DoubleCoset.quotientCongr Γ K (restrictedProductCongr U U' h) rfl rfl

/-- The transported double-coset space sends the double coset of `x` to the double coset of its
image under the change-of-family equivalence.

Not a `simp` lemma: the type of `doubleCosetCongr` mentions the coercions `↑(Γ.map e)` and
`↑(K.map e)`, which `Subgroup.coe_map` rewrites, so the left-hand side is not in simp-normal form.
Use `DoubleCoset.quotientCongr_apply_mk` after unfolding, or rewrite with this lemma directly. -/
theorem doubleCosetCongr_apply_mk (U U' : ∀ i, Subgroup (G i))
    (h : ∀ᶠ i in cofinite, U i = U' i)
    (Γ K : Subgroup (Πʳ i, [G i, (U i : Set (G i))]))
    (x : Πʳ i, [G i, (U i : Set (G i))]) :
    doubleCosetCongr U U' h Γ K (DoubleCoset.mk Γ K x) =
      DoubleCoset.mk
        (Γ.map (restrictedProductCongr U U' h :
          (Πʳ i, [G i, (U i : Set (G i))]) →* Πʳ i, [G i, (U' i : Set (G i))]))
        (K.map (restrictedProductCongr U U' h :
          (Πʳ i, [G i, (U i : Set (G i))]) →* Πʳ i, [G i, (U' i : Set (G i))]))
        (restrictedProductCongr U U' h x) :=
  DoubleCoset.quotientCongr_apply_mk Γ K _ rfl rfl x

/-- The inverse of the transported double-coset space sends the double coset of `y` to the double
coset of its image under the inverse change-of-family equivalence.

Not a `simp` lemma, for the same reason as `doubleCosetCongr_apply_mk`. -/
theorem doubleCosetCongr_symm_apply_mk (U U' : ∀ i, Subgroup (G i))
    (h : ∀ᶠ i in cofinite, U i = U' i)
    (Γ K : Subgroup (Πʳ i, [G i, (U i : Set (G i))]))
    (y : Πʳ i, [G i, (U' i : Set (G i))]) :
    (doubleCosetCongr U U' h Γ K).symm
        (DoubleCoset.mk
          (Γ.map (restrictedProductCongr U U' h :
            (Πʳ i, [G i, (U i : Set (G i))]) →* Πʳ i, [G i, (U' i : Set (G i))]))
          (K.map (restrictedProductCongr U U' h :
            (Πʳ i, [G i, (U i : Set (G i))]) →* Πʳ i, [G i, (U' i : Set (G i))]))
          y) =
      DoubleCoset.mk Γ K ((restrictedProductCongr U U' h).symm y) :=
  DoubleCoset.quotientCongr_symm_apply_mk Γ K _ rfl rfl y

end TauCeti

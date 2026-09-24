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

The change-of-family isomorphism `restrictedProductCongr` identifies the ambient restricted
products only.  It need not carry the everywhere-integral subgroup of one family onto that of the
other; the counterexample `exists_map_integralSubgroup_ne` is recorded alongside the isomorphism
in `TauCeti.Topology.Algebra.RestrictedProduct.Congr.Basic`.  For this reason the induced
bijection of double-coset spaces, `doubleCosetCongr`, is stated along the transported subgroups
rather than along the integral subgroup of the new family.

## References

* A. Weil, *Basic Number Theory*.
-/

public section

namespace TauCeti

open Filter
open scoped RestrictedProduct

universe u v

variable {ι : Type u} {G : ι → Type v}
variable [∀ i, Group (G i)]

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

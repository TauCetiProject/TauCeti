/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SemidirectProduct
public import TauCeti.Algebra.Group.Subgroup.Pointwise

/-!
# Gluing homomorphisms on a subgroup and a normalizing subgroup

If `K` normalizes `H`, multiplication maps the external semidirect product `H ⋊ K` onto
`H ⊔ K`. Its kernel consists of the pairs `(a, b)` with `a = b⁻¹` in the ambient group.
Consequently, equivariant homomorphisms on `H` and `K` descend to their join precisely when
they agree on `H ⊓ K`. No trivial-intersection hypothesis is needed.

`Subgroup.liftSupOfRightLeNormalizer` is this descended homomorphism. Its value on a product,
its restrictions to both factors, and its uniqueness characterize it without choosing a
factorization. This permits extending a map on an elementary group by a compatible map on
its torus, even when their intersection is nontrivial.

The construction uses Mathlib's `SemidirectProduct.lift` and `MonoidHom.liftOfSurjective`,
and `SemidirectProduct.range_monoidHomSubgroup` for the image of multiplication.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 28 and the comparison of
  representations following Theorem 4′.
-/

public section

namespace Subgroup

variable {G D : Type*} [Group G] [Group D] (H K : Subgroup G)
variable (hLE : K ≤ normalizer (H : Set G)) (f : H →* D) (g : K →* D)
variable (hconj : ∀ b : K,
  f.comp (((H.normalizerMonoidHom).comp (inclusion hLE)) b).toMonoidHom =
    (MulAut.conj (g b)).toMonoidHom.comp f)
variable (hagree : ∀ a : ↥(H ⊓ K), f ⟨a, a.property.1⟩ = g ⟨a, a.property.2⟩)

/-- Glue equivariant homomorphisms from `H` and `K` to their join, assuming that `K` normalizes
`H` and that the maps agree on the intersection. -/
noncomputable def liftSupOfRightLeNormalizer : ↥(H ⊔ K) →* D :=
  let m := SemidirectProduct.monoidHomSubgroup hLE
  let l := SemidirectProduct.lift f g hconj
  let hk : m.rangeRestrict.ker ≤ l.ker :=
    (MonoidHom.ker_rangeRestrict m).le.trans
      ((SemidirectProduct.ker_monoidHomSubgroup_le_ker_lift_iff hLE f g hconj).mpr hagree)
  (m.rangeRestrict.liftOfSurjective m.rangeRestrict_surjective ⟨l, hk⟩).comp
    (MulEquiv.subgroupCongr (SemidirectProduct.range_monoidHomSubgroup hLE)).symm.toMonoidHom

/-- The glued map sends a product of elements of the two factors to the product of their
images. This formula is independent of the chosen factorization. -/
@[simp]
theorem liftSupOfRightLeNormalizer_mul (a : H) (b : K) :
    liftSupOfRightLeNormalizer H K hLE f g hconj hagree
      ⟨(a : G) * b, mul_mem_sup a.property b.property⟩ = f a * g b := by
  let x : H ⋊[(H.normalizerMonoidHom).comp (inclusion hLE)] K := ⟨a, b⟩
  -- Transport from the join to the range identifies this product with the image of (a,b).
  have htransport :
      (MulEquiv.subgroupCongr (SemidirectProduct.range_monoidHomSubgroup hLE)).symm
        ⟨(a : G) * b, mul_mem_sup a.property b.property⟩ =
      (SemidirectProduct.monoidHomSubgroup hLE).rangeRestrict x := by
    apply Subtype.ext
    exact (SemidirectProduct.monoidHomSubgroup_apply hLE x).symm
  -- Intentionally unfold liftOfSurjective to apply the right-inverse evaluation lemma;
  -- Mathlib provides no corresponding evaluation lemma for the surjective abbreviation.
  simp only [liftSupOfRightLeNormalizer, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    htransport, MonoidHom.liftOfSurjective, MonoidHom.liftOfRightInverse_comp_apply]
  exact SemidirectProduct.lift_apply f g hconj x

/-- The restriction of the glued map to `H` is the original map. -/
@[simp]
theorem liftSupOfRightLeNormalizer_left (a : H) :
    liftSupOfRightLeNormalizer H K hLE f g hconj hagree (inclusion le_sup_left a) = f a := by
  have hincl : inclusion (le_sup_left : H ≤ H ⊔ K) a =
      ⟨(a : G) * (1 : K), mul_mem_sup a.property (K.one_mem)⟩ := by
    apply Subtype.ext
    simp
  rw [hincl, liftSupOfRightLeNormalizer_mul, map_one, mul_one]

/-- The restriction of the glued map to `K` is the original map. -/
@[simp]
theorem liftSupOfRightLeNormalizer_right (b : K) :
    liftSupOfRightLeNormalizer H K hLE f g hconj hagree (inclusion le_sup_right b) = g b := by
  have hincl : inclusion (le_sup_right : K ≤ H ⊔ K) b =
      ⟨(1 : H) * (b : G), mul_mem_sup H.one_mem b.property⟩ := by
    apply Subtype.ext
    simp
  rw [hincl, liftSupOfRightLeNormalizer_mul, map_one, one_mul]

/-- Restricting the glued homomorphism along the left inclusion recovers `f`. -/
@[simp]
theorem liftSupOfRightLeNormalizer_comp_left :
    (liftSupOfRightLeNormalizer H K hLE f g hconj hagree).comp (inclusion le_sup_left) = f := by
  ext a
  exact liftSupOfRightLeNormalizer_left H K hLE f g hconj hagree a

/-- Restricting the glued homomorphism along the right inclusion recovers `g`. -/
@[simp]
theorem liftSupOfRightLeNormalizer_comp_right :
    (liftSupOfRightLeNormalizer H K hLE f g hconj hagree).comp (inclusion le_sup_right) = g := by
  ext b
  exact liftSupOfRightLeNormalizer_right H K hLE f g hconj hagree b

/-- A homomorphism from the join is the glued map if it restricts to the prescribed maps on
both subgroups. -/
theorem eq_liftSupOfRightLeNormalizer (F : ↥(H ⊔ K) →* D)
    (hF : F.comp (inclusion le_sup_left) = f)
    (hG : F.comp (inclusion le_sup_right) = g) :
    F = liftSupOfRightLeNormalizer H K hLE f g hconj hagree := by
  apply MonoidHom.ext
  intro x
  obtain ⟨a, ha, b, hb, hab⟩ := (mem_sup_of_right_le_normalizer_left hLE).mp x.property
  have hfactor : x = inclusion le_sup_left ⟨a, ha⟩ * inclusion le_sup_right ⟨b, hb⟩ := by
    apply Subtype.ext
    exact hab.symm
  rw [hfactor, map_mul, map_mul, liftSupOfRightLeNormalizer_left,
    liftSupOfRightLeNormalizer_right]
  exact congrArg₂ (· * ·) (DFunLike.congr_fun hF ⟨a, ha⟩) (DFunLike.congr_fun hG ⟨b, hb⟩)

end Subgroup

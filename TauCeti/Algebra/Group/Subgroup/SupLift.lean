/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SemidirectProduct

/-!
# Gluing homomorphisms on normalizing subgroups

Suppose `K` normalizes `H`. Homomorphisms from `H` and `K` extend to `H ⊔ K` precisely when
it is possible to multiply their values independently of the factorization: they must
intertwine conjugation by `K` and agree on `H ⊓ K`. `Subgroup.supLift` constructs this
extension, and `Subgroup.existsUnique_supLift_iff` gives its universal property.

In particular this glues a homomorphism on an elementary Chevalley group with a map on its
actual character-lattice torus. No complement or trivial-intersection hypothesis is needed.
The construction uses `SemidirectProduct.lift`, the antidiagonal-kernel criterion
`SemidirectProduct.ker_monoidHomSubgroup_le_ker_lift_iff`, and Mathlib's
`MonoidHom.liftOfSurjective`; it makes no choice of unique subgroup factors.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Corollary 5 to Theorem 4′
  (extension of elementary comparisons by the torus).
-/

public section

namespace Subgroup

variable {G D : Type*} [Group G] [Group D] (H K : Subgroup G)
variable (hLE : K ≤ normalizer (H : Set G)) (f : H →* D) (g : K →* D)
variable (hconj : ∀ b : K,
  f.comp (((H.normalizerMonoidHom).comp (inclusion hLE)) b).toMonoidHom =
    (MulAut.conj (g b)).toMonoidHom.comp f)
variable (hagree : ∀ a : ↥(H ⊓ K), f ⟨a, a.property.1⟩ = g ⟨a, a.property.2⟩)

/-- Extend homomorphisms on normalizing subgroups to their join, provided they intertwine
conjugation and agree on the intersection. -/
noncomputable def supLift : ↥(H ⊔ K) →* D :=
  ((SemidirectProduct.monoidHomSubgroup hLE).rangeRestrict.liftOfSurjective
    (MonoidHom.rangeRestrict_surjective _)
    ⟨SemidirectProduct.lift f g hconj, by
      rw [MonoidHom.ker_rangeRestrict]
      exact (SemidirectProduct.ker_monoidHomSubgroup_le_ker_lift_iff
        hLE f g hconj).mpr hagree⟩).comp
    (MulEquiv.subgroupCongr (SemidirectProduct.range_monoidHomSubgroup hLE)).symm.toMonoidHom

/-- The glued homomorphism evaluates any product factorization by multiplying the two images.
The factors need not be unique. -/
@[simp]
theorem supLift_mul (a : H) (b : K) :
    H.supLift K hLE f g hconj hagree ⟨(a : G) * b, mul_mem_sup a.property b.property⟩ =
      f a * g b := by
  let x : H ⋊[(H.normalizerMonoidHom).comp (inclusion hLE)] K := ⟨a, b⟩
  have hx :
      (MulEquiv.subgroupCongr (SemidirectProduct.range_monoidHomSubgroup hLE)).symm
        ⟨(a : G) * b, mul_mem_sup a.property b.property⟩ =
      (SemidirectProduct.monoidHomSubgroup hLE).rangeRestrict x := by
    apply Subtype.ext
    simp [x]
  simp only [supLift, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hx,
    MonoidHom.liftOfSurjective, MonoidHom.liftOfRightInverse_comp_apply,
    SemidirectProduct.lift_apply, x]

/-- The extension restricts to the prescribed homomorphism on the first subgroup. -/
@[simp]
theorem supLift_inclusion_left (a : H) :
    H.supLift K hLE f g hconj hagree (inclusion le_sup_left a) = f a := by
  have h := H.supLift_mul K hLE f g hconj hagree a 1
  have heq : (⟨(a : G) * (1 : K), mul_mem_sup a.property (1 : K).property⟩ : ↥(H ⊔ K)) =
      inclusion le_sup_left a := by
    apply Subtype.ext
    simp
  simpa only [heq, map_one, mul_one] using h

/-- The extension restricts to the prescribed homomorphism on the second subgroup. -/
@[simp]
theorem supLift_inclusion_right (b : K) :
    H.supLift K hLE f g hconj hagree (inclusion le_sup_right b) = g b := by
  have h := H.supLift_mul K hLE f g hconj hagree 1 b
  have heq : (⟨((1 : H) : G) * b, mul_mem_sup (1 : H).property b.property⟩ : ↥(H ⊔ K)) =
      inclusion le_sup_right b := by
    apply Subtype.ext
    simp
  simpa only [heq, map_one, one_mul] using h

/-- A homomorphism out of a join of subgroups is determined by its restrictions to both
factors, without any normalization hypothesis. -/
theorem sup_hom_ext {M : Type*} [Monoid M] {F F' : ↥(H ⊔ K) →* M}
    (hH : ∀ a : H, F (inclusion le_sup_left a) = F' (inclusion le_sup_left a))
    (hK : ∀ b : K, F (inclusion le_sup_right b) = F' (inclusion le_sup_right b)) : F = F' := by
  have hsup : H ⊔ K ≤ (F.eqLocus F').map (H ⊔ K).subtype := by
    apply sup_le
    · intro a ha
      exact ⟨inclusion le_sup_left (⟨a, ha⟩ : H), hH ⟨a, ha⟩, by simp⟩
    · intro b hb
      exact ⟨inclusion le_sup_right (⟨b, hb⟩ : K), hK ⟨b, hb⟩, by simp⟩
  apply MonoidHom.ext
  intro x
  obtain ⟨y, hy, heq⟩ := hsup x.property
  have hxy : y = x := Subtype.ext heq
  exact hxy ▸ hy

/-- The two compatibility conditions are necessary and sufficient for a unique extension to
the join. In particular, agreement on the intersection cannot be omitted when the factors
are not complementary. -/
theorem existsUnique_supLift_iff :
    (∃! F : ↥(H ⊔ K) →* D,
      (∀ a : H, F (inclusion le_sup_left a) = f a) ∧
        ∀ b : K, F (inclusion le_sup_right b) = g b) ↔
    (∀ b : K,
      f.comp (((H.normalizerMonoidHom).comp (inclusion hLE)) b).toMonoidHom =
        (MulAut.conj (g b)).toMonoidHom.comp f) ∧
      ∀ a : ↥(H ⊓ K), f ⟨a, a.property.1⟩ = g ⟨a, a.property.2⟩ := by
  constructor
  · rintro ⟨F, ⟨hH, hK⟩, _⟩
    constructor
    · intro b
      apply MonoidHom.ext
      intro a
      have hval : inclusion le_sup_left
          (((H.normalizerMonoidHom).comp (inclusion hLE)) b a) =
          inclusion le_sup_right b * inclusion le_sup_left a * (inclusion le_sup_right b)⁻¹ := by
        -- The normalizer action is defined by conjugation in the ambient group.
        apply Subtype.ext
        rfl
      simp only [MonoidHom.comp_apply] at hval
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [← hH, hval, map_mul, map_mul, map_inv, hH, hK]
    · intro a
      rw [← hH, ← hK]
      congr 1
  · rintro ⟨hc, ha⟩
    refine ⟨H.supLift K hLE f g hc ha, ⟨?_, ?_⟩, ?_⟩
    · exact H.supLift_inclusion_left K hLE f g hc ha
    · exact H.supLift_inclusion_right K hLE f g hc ha
    · intro F hF
      apply H.sup_hom_ext K
      · intro a
        simp [hF.1 a]
      · intro b
        simp [hF.2 b]

end Subgroup

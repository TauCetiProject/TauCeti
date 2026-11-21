/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Basic
import TauCeti.GroupTheory.QuotientGroup.KerEquiv

/-!
# Ranges and equality loci of group homomorphisms

This file supplies the characteristic membership equation for the subgroup equality locus, the
invariance of the range of a group homomorphism under precomposition with a surjection, the
range and kernel of the pointwise inverse of a homomorphism into a commutative group, and the
homomorphism between the ranges of two homomorphisms out of the same group when the first kernel
lies in the second, an isomorphism when the kernels are equal.

## Main results

* `MonoidHom.mem_eqLocus`: membership in the equality locus is pointwise equality.
* `MonoidHom.range_comp_of_surjective`: precomposition with a surjection preserves the range.
* `MonoidHom.range_inv`, `MonoidHom.ker_inv`: the pointwise inverse `f⁻¹` has the same range and
  kernel as `f`.
* `MonoidHom.rangeHom`: for `f : C →* N` and `g : C →* N'` with `f.ker ≤ g.ker`, the
  homomorphism `f.range →* g.range` sending `f c` to `g c`.
* `MonoidHom.rangeEquivRange`: for `f.ker = g.ker`, the isomorphism `f.range ≃* g.range` sending
  `f c` to `g c`.
* `Subgroup.sup_hom_ext`: homomorphisms out of a join are determined by their restrictions.
-/

public section

namespace MonoidHom

variable {G M : Type*} [Group G] [Monoid M]

/-- Membership in the equality locus of two monoid homomorphisms out of a group is pointwise
equality. -/
@[to_additive (attr := simp)]
theorem mem_eqLocus {f g : G →* M} {x : G} : x ∈ f.eqLocus g ↔ f x = g x :=
  Iff.rfl

/-- Precomposition with a surjective group homomorphism does not change the range. -/
@[to_additive /-- Precomposition with a surjective additive group homomorphism does not change the
range. -/]
theorem range_comp_of_surjective {N P : Type*} [Group N] [Group P] (g : N →* P) (f : G →* N)
    (hf : Function.Surjective f) : (g.comp f).range = g.range :=
  SetLike.coe_injective <| by simpa only [coe_range, coe_comp] using hf.range_comp g

/-- The pointwise inverse of a homomorphism into a commutative group has the same range. -/
@[to_additive (attr := simp) /-- The pointwise negation of a homomorphism into a commutative
additive group has the same range. -/]
theorem range_inv {H : Type*} [CommGroup H] (f : G →* H) : f⁻¹.range = f.range := by
  ext
  simp only [mem_range]
  exact inv_surjective.exists.trans (by simp)

/-- The pointwise inverse of a homomorphism into a commutative group has the same kernel. -/
@[to_additive (attr := simp) /-- The pointwise negation of a homomorphism into a commutative
additive group has the same kernel. -/]
theorem ker_inv {H : Type*} [CommGroup H] (f : G →* H) : f⁻¹.ker = f.ker := by
  ext x
  simp

section rangeEquivRange

variable {C N N' : Type*} [Group C] [Group N] [Group N'] (f : C →* N) (g : C →* N')

/-- Two injective homomorphisms out of the same group have the same kernel, the trivial one. -/
@[to_additive /-- Two injective additive homomorphisms out of the same additive group have the
same kernel, the trivial one. -/]
theorem ker_eq_ker_of_injective {f : C →* N} {g : C →* N'} (hf : Function.Injective f)
    (hg : Function.Injective g) : f.ker = g.ker := by
  rw [(ker_eq_bot_iff f).2 hf, (ker_eq_bot_iff g).2 hg]

/-- For `f.ker ≤ g.ker`, the homomorphism `f.range →* g.range` sending `f c` to `g c`. -/
@[to_additive /-- For `f.ker ≤ g.ker`, the additive homomorphism `f.range →+ g.range` sending
`f c` to `g c`. -/]
noncomputable def rangeHom (h : f.ker ≤ g.ker) : f.range →* g.range :=
  f.rangeRestrict.liftOfSurjective f.rangeRestrict_surjective
    ⟨g.rangeRestrict, by rwa [ker_rangeRestrict, ker_rangeRestrict]⟩

/-- For homomorphisms `f : C →* N` and `g : C →* N'` with the same kernel, the isomorphism
`f.range ≃* g.range` sending `f c` to `g c`: both ranges are the quotient of `C` by the kernel. -/
@[to_additive /-- For additive homomorphisms `f : C →+ N` and `g : C →+ N'` with the same kernel,
the isomorphism `f.range ≃+ g.range` sending `f c` to `g c`: both ranges are the quotient of `C` by
the kernel. -/]
noncomputable def rangeEquivRange (h : f.ker = g.ker) : f.range ≃* g.range :=
  (QuotientGroup.quotientKerEquivRange f).symm.trans <|
    (QuotientGroup.quotientMulEquivOfEq h).trans (QuotientGroup.quotientKerEquivRange g)

variable {f g}

@[to_additive (attr := simp)]
theorem rangeHom_rangeRestrict (h : f.ker ≤ g.ker) (c : C) :
    rangeHom f g h (f.rangeRestrict c) = g.rangeRestrict c :=
  liftOfRightInverse_comp_apply ..

@[to_additive (attr := simp)]
theorem rangeHom_comp_rangeRestrict (h : f.ker ≤ g.ker) :
    (rangeHom f g h).comp f.rangeRestrict = g.rangeRestrict :=
  ext (rangeHom_rangeRestrict h)

@[to_additive (attr := simp)]
theorem rangeEquivRange_rangeRestrict (h : f.ker = g.ker) (c : C) :
    rangeEquivRange f g h (f.rangeRestrict c) = g.rangeRestrict c :=
  Subtype.ext <| by simp [rangeEquivRange]

@[to_additive (attr := simp)]
theorem rangeEquivRange_symm_rangeRestrict (h : f.ker = g.ker) (c : C) :
    (rangeEquivRange f g h).symm (g.rangeRestrict c) = f.rangeRestrict c := by
  rw [MulEquiv.symm_apply_eq, rangeEquivRange_rangeRestrict]

end rangeEquivRange

end MonoidHom

namespace Subgroup

/-- A homomorphism out of a join of subgroups is determined by its restrictions to both
factors, without any normalization hypothesis. -/
theorem sup_hom_ext {G M : Type*} [Group G] [Monoid M] (H K : Subgroup G)
    {F F' : ↥(H ⊔ K) →* M}
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

end Subgroup

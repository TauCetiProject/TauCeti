/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# Ranges and equality loci of group homomorphisms

This file supplies the characteristic membership equation for the subgroup equality locus, the
invariance of the range of a group homomorphism under precomposition with a surjection, the
compatibility of ranges and kernels with a commutative square, and the range and kernel of the
pointwise inverse of a homomorphism into a commutative group, and the kernel of a pointwise
product of homomorphisms.

## Main results

* `MonoidHom.mem_eqLocus`: membership in the equality locus is pointwise equality.
* `MonoidHom.range_comp_of_surjective`: precomposition with a surjection preserves the range.
* `MonoidHom.range_le_comap_range_of_comp_eq`: in a commutative square, the range of one side is
  carried into the range of the opposite side.
* `MonoidHom.ker_le_comap_ker_of_comp_eq`: in a commutative square, the kernel of one side is
  carried into the kernel of the opposite side.
* `MonoidHom.range_inv`, `MonoidHom.ker_inv`: the pointwise inverse `f⁻¹` has the same range and
  kernel as `f`.
* `MonoidHom.ker_compl₂_compr₂_of_injective`, `AddMonoidHom.ker_compl₂_compr₂_of_injective`:
  postcomposing a bimultiplicative or biadditive pairing with an injective homomorphism on its
  target preserves the kernel of precomposition in the second slot.
* `MonoidHom.mem_ker_compl₂_subtype_iff`, `AddMonoidHom.mem_ker_compl₂_subtype_iff`:
  membership in the kernel of a pairing restricted on its second slot to a subgroup is pointwise
  triviality against that subgroup.
* `MonoidHom.ker_inf_ker_le_ker_mul`: the kernel of `f * g` contains the kernels' intersection.
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

/-- In a commutative square `f₁ ∘ d = d' ∘ f₀` of group homomorphisms, `f₁` carries the range of
`d` into the range of `d'`; this is what makes the square induce a map of cokernels
`H ⧸ range d → H' ⧸ range d'` when the ranges are normal. -/
@[to_additive /-- In a commutative square `f₁ ∘ d = d' ∘ f₀` of additive group homomorphisms, `f₁`
carries the range of `d` into the range of `d'`; this is what makes the square induce a map
`H ⧸ range d → H' ⧸ range d'` of cokernels. -/]
theorem range_le_comap_range_of_comp_eq {H G' H' : Type*} [Group H] [Group G'] [Group H']
    {d : G →* H} {d' : G' →* H'} {f₀ : G →* G'} {f₁ : H →* H'} (h : f₁.comp d = d'.comp f₀) :
    d.range ≤ d'.range.comap f₁ := by
  rintro _ ⟨a, rfl⟩
  exact ⟨f₀ a, (DFunLike.congr_fun h a).symm⟩

/-- In a commutative square `f₁ ∘ d = d' ∘ f₀` of monoid homomorphisms out of the groups `G` and
`G'`, `f₀` carries the kernel of `d` into the kernel of `d'`; this is what makes the square restrict
to a map of kernels `ker d → ker d'`. -/
@[to_additive /-- In a commutative square `f₁ ∘ d = d' ∘ f₀` of additive monoid homomorphisms out of
the additive groups `G` and `G'`, `f₀` carries the kernel of `d` into the kernel of `d'`; this is
what makes the square restrict to a map `ker d → ker d'` of kernels. -/]
theorem ker_le_comap_ker_of_comp_eq {H G' H' : Type*} [MulOneClass H] [Group G'] [MulOneClass H']
    {d : G →* H} {d' : G' →* H'} {f₀ : G →* G'} {f₁ : H →* H'} (h : f₁.comp d = d'.comp f₀) :
    d.ker ≤ d'.ker.comap f₀ := fun a ha => by
  rw [Subgroup.mem_comap, mem_ker, ← comp_apply, ← h, comp_apply, mem_ker.mp ha, map_one]

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

/-- Postcomposing a bimultiplicative pairing with an injective monoid homomorphism on its target
preserves the kernel of precomposition in the second slot. -/
@[to_additive /-- Postcomposing a biadditive pairing with an injective additive homomorphism on
its target preserves the kernel of precomposition in the second slot. -/]
theorem ker_compl₂_compr₂_of_injective {A B C D Q : Type*} [Group A] [MulOneClass B]
    [CommMonoid C] [CommMonoid D] [MulOneClass Q]
    (f : A →* B →* C) (g : Q →* B) (i : C →* D) (hi : Function.Injective i) :
    ((f.compr₂ i).compl₂ g).ker = (f.compl₂ g).ker := by
  ext a
  simp only [mem_ker, DFunLike.ext_iff, compl₂_apply, compr₂_apply, one_apply]
  exact forall_congr' fun q ↦ map_eq_one_iff i hi

/-- Membership in the kernel of a bimultiplicative pairing restricted on the second slot to a
subgroup `H` is pointwise triviality against `H`. -/
@[to_additive /-- Membership in the kernel of a biadditive pairing restricted on the second slot
to an additive subgroup `H` is pointwise triviality against `H`. -/]
theorem mem_ker_compl₂_subtype_iff {A B C : Type*} [Group A] [Group B] [CommMonoid C]
    (f : A →* B →* C) (H : Subgroup B) {a : A} :
    a ∈ (f.compl₂ H.subtype).ker ↔ ∀ b ∈ H, f a b = 1 := by
  simp only [mem_ker, DFunLike.ext_iff, compl₂_apply, one_apply, Subtype.forall,
    Subgroup.subtype_apply]

/-- An element in the kernels of both `f` and `g` is in the kernel of their pointwise product. -/
@[to_additive /-- An element in the kernels of both `f` and `g` is in the kernel of their
pointwise sum. -/]
theorem ker_inf_ker_le_ker_mul {H : Type*} [CommMonoid H] (f g : G →* H) :
    f.ker ⊓ g.ker ≤ (f * g).ker :=
  fun x hx ↦ by simp [mem_ker.mp hx.1, mem_ker.mp hx.2]

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

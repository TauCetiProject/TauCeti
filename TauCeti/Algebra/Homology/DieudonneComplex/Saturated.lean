/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DieudonneComplex.Basic

/-!
# Saturated Dieudonné complexes and the Verschiebung

A Dieudonné complex `M` is *saturated* (Bhatt–Lurie–Mathew) when its terms are `p`-torsion-free
and the Frobenius maps `Mⁿ` bijectively onto `{x ∈ Mⁿ | d x ∈ p Mⁿ⁺¹}`. Equivalently, the
cochain map `α_F : M ⟶ E_p(M)` into the normalized décalage is an isomorphism. On a saturated
Dieudonné complex the Verschiebung `V` is the unique map with `F (V x) = p • x`. It satisfies
`F V = V F = p`, `F d V = d` and `V d = p d V`, and every morphism of saturated Dieudonné
complexes commutes with it. Moreover `Fʳ` maps `Mⁿ` onto `{x | d x ∈ pʳ Mⁿ⁺¹}` for every `r`,
so every cocycle lies in the image of every power of the Frobenius.

Saturated Dieudonné complexes are the input of the strict completion that produces the
de Rham–Witt complex.

## Main definitions

* `TauCeti.DieudonneComplex.IsSaturated`: saturation of a Dieudonné complex.
* `TauCeti.DieudonneComplex.IsSaturated.V`: the Verschiebung of a saturated Dieudonné complex.

## Main results

* `TauCeti.DieudonneComplex.isSaturated_iff_isIso_toNormalizedDecalage`: saturation means that
  `α_F : M ⟶ E_p(M)` is an isomorphism.
* `TauCeti.DieudonneComplex.IsSaturated.range_F`: the image of `F` is `{x | d x ∈ p Mⁿ⁺¹}`.
* `TauCeti.DieudonneComplex.IsSaturated.F_V_apply`,
  `TauCeti.DieudonneComplex.IsSaturated.V_F_apply`: `F V = V F = p`.
* `TauCeti.DieudonneComplex.IsSaturated.F_d_V_apply`: `F d V = d`.
* `TauCeti.DieudonneComplex.IsSaturated.V_d_apply`: `V d = p d V`.
* `TauCeti.DieudonneComplex.Hom.comm_V_apply`: morphisms commute with the Verschiebung.
* `TauCeti.DieudonneComplex.IsSaturated.mem_range_F_iterate_iff`: `x` is in the image of `Fʳ`
  iff `d x` is divisible by `pʳ`.

## References

* B. Bhatt, J. Lurie, A. Mathew, *Revisiting the de Rham–Witt complex*, Astérisque 424 (2021),
  arXiv:1805.05501, Definition 2.2.1, Remarks 2.2.2 and 2.2.3, Propositions 2.2.4 and 2.2.5.
-/

public section

open CategoryTheory CochainComplex

universe u

namespace TauCeti

namespace DieudonneComplex

variable {p : ℕ} {M : DieudonneComplex.{u} p}

variable (M) in
/-- A Dieudonné complex is *saturated* if its terms are `p`-torsion-free and, in every degree,
the Frobenius is injective with image `{x | d x ∈ p Mⁿ⁺¹}`. -/
structure IsSaturated : Prop where
  /-- Multiplication by `p` is injective in every degree. -/
  isSMulRegular (n : ℤ) : IsSMulRegular (M.X n) p
  /-- The Frobenius is injective in every degree. -/
  injective_F (n : ℤ) : Function.Injective (M.F n).hom
  /-- Every element whose differential is divisible by `p` is in the image of the Frobenius. -/
  decalageAddSubgroup_le_range (n : ℤ) :
    decalageAddSubgroup M.toCochainComplex p n ≤ (M.F n).hom.range

namespace IsSaturated

variable (hM : M.IsSaturated)
include hM

/-- On a saturated Dieudonné complex the image of the Frobenius is `{x | d x ∈ p Mⁿ⁺¹}`. -/
lemma range_F (n : ℤ) : (M.F n).hom.range = decalageAddSubgroup M.toCochainComplex p n :=
  le_antisymm (by rintro _ ⟨x, rfl⟩; exact M.F_mem_decalageAddSubgroup n x)
    (hM.decalageAddSubgroup_le_range n)

lemma mem_range_F_iff {n : ℤ} {x : M.X n} :
    x ∈ (M.F n).hom.range ↔ ∃ y, p • y = (M.d n (n + 1)).hom x := by
  rw [hM.range_F, mem_decalageAddSubgroup_iff]

/-- On a saturated Dieudonné complex, `p • x` is in the image of the Frobenius. -/
lemma smul_mem_range_F {n : ℤ} (x : M.X n) : p • x ∈ (M.F n).hom.range :=
  hM.mem_range_F_iff.2 ⟨_, (map_nsmul _ _ _).symm⟩

/-- The Verschiebung of a saturated Dieudonné complex: `V x` is the unique element with
`F (V x) = p • x`. -/
noncomputable def V (n : ℤ) : M.X n ⟶ M.X n :=
  AddCommGrpCat.ofHom <|
    ((AddMonoidHom.ofInjective (hM.injective_F n)).symm : _ →+ M.X n).comp
      ((DistribSMul.toAddMonoidHom (M.X n) p).codRestrict _ hM.smul_mem_range_F)

/-- `F V = p`. -/
@[simp]
lemma F_V_apply {n : ℤ} (x : M.X n) : (M.F n).hom ((hM.V n).hom x) = p • x :=
  AddMonoidHom.apply_ofInjective_symm (hM.injective_F n) _

/-- `V x` is the unique `y` with `F y = p • x`. -/
lemma V_eq_iff {n : ℤ} {x y : M.X n} : (hM.V n).hom x = y ↔ (M.F n).hom y = p • x :=
  ⟨fun h ↦ h ▸ hM.F_V_apply x, fun h ↦ hM.injective_F n (by rw [F_V_apply, h])⟩

/-- `V F = p`. -/
@[simp]
lemma V_F_apply {n : ℤ} (x : M.X n) : (hM.V n).hom ((M.F n).hom x) = p • x :=
  hM.V_eq_iff.2 (map_nsmul _ _ _)

/-- The Verschiebung is injective. -/
lemma injective_V (n : ℤ) : Function.Injective (hM.V n).hom := fun x y hxy ↦
  hM.isSMulRegular n (by beta_reduce; rw [← F_V_apply hM x, hxy, F_V_apply])

/-- `F d V = d`. -/
@[simp]
lemma F_d_V_apply {n : ℤ} (x : M.X n) :
    (M.F (n + 1)).hom ((M.d n (n + 1)).hom ((hM.V n).hom x)) = (M.d n (n + 1)).hom x :=
  hM.isSMulRegular (n + 1) (by beta_reduce; rw [← M.d_F, F_V_apply, map_nsmul])

/-- `V d = p d V`: the Verschiebung commutes with the differential only up to a factor of
`p`. -/
lemma V_d_apply {n : ℤ} (x : M.X n) :
    (hM.V (n + 1)).hom ((M.d n (n + 1)).hom x) = p • (M.d n (n + 1)).hom ((hM.V n).hom x) := by
  conv_lhs => rw [← hM.F_d_V_apply x]
  exact hM.V_F_apply _

end IsSaturated

/-- A morphism between saturated Dieudonné complexes commutes with the Verschiebung. -/
lemma Hom.comm_V_apply {N : DieudonneComplex.{u} p} (hM : M.IsSaturated) (hN : N.IsSaturated)
    (f : M ⟶ N) {n : ℤ} (x : M.X n) :
    (f.hom.f n).hom ((hM.V n).hom x) = (hN.V n).hom ((f.hom.f n).hom x) :=
  ((hN.V_eq_iff).2 (by rw [← Hom.comm_F_apply, hM.F_V_apply, map_nsmul])).symm

/-- A `p`-torsion-free Dieudonné complex is saturated iff `α_F : M ⟶ E_p(M)` is an
isomorphism of cochain complexes. -/
lemma isSaturated_iff_isIso_toNormalizedDecalage (hM : ∀ n, IsSMulRegular (M.X n) p) :
    M.IsSaturated ↔ IsIso (M.toNormalizedDecalage hM) := by
  have hbij (n : ℤ) : Function.Bijective ((M.toNormalizedDecalage hM).f n).hom ↔
      Function.Injective (M.F n).hom ∧
        decalageAddSubgroup M.toCochainComplex p n ≤ (M.F n).hom.range := by
    refine and_congr ?_ ⟨fun h z hz ↦ ?_, fun h z ↦ ?_⟩
    · have hcomp : Subtype.val ∘ ⇑((M.toNormalizedDecalage hM).f n).hom = ⇑(M.F n).hom :=
        funext (toNormalizedDecalage_f_apply M hM n)
      rw [← Subtype.val_injective.of_comp_iff, hcomp]
    · obtain ⟨x, hx⟩ := h ⟨z, hz⟩
      exact ⟨x, (toNormalizedDecalage_f_apply M hM n x).symm.trans (congrArg Subtype.val hx)⟩
    · obtain ⟨x, hx⟩ := h z.property
      exact ⟨x, Subtype.ext ((toNormalizedDecalage_f_apply M hM n x).trans hx)⟩
  refine ⟨fun h ↦ ?_, fun _ ↦ ⟨hM, fun n ↦ ?_, fun n ↦ ?_⟩⟩
  · have (n : ℤ) : IsIso ((M.toNormalizedDecalage hM).f n) :=
      (ConcreteCategory.isIso_iff_bijective _).2
        ((hbij n).2 ⟨h.injective_F n, h.decalageAddSubgroup_le_range n⟩)
    exact HomologicalComplex.Hom.isIso_of_components _
  · exact ((hbij n).1 (ConcreteCategory.bijective_of_isIso _)).1
  · exact ((hbij n).1 (ConcreteCategory.bijective_of_isIso _)).2

namespace IsSaturated

variable (hM : M.IsSaturated)
include hM

/-- On a saturated Dieudonné complex, `x` lies in the image of `Fʳ` iff `d x` is divisible by
`pʳ`. -/
lemma mem_range_F_iterate_iff {n : ℤ} (r : ℕ) {x : M.X n} :
    x ∈ Set.range (⇑(M.F n).hom)^[r] ↔ ∃ y, p ^ r • y = (M.d n (n + 1)).hom x := by
  refine ⟨?_, ?_⟩
  · rintro ⟨z, rfl⟩
    exact ⟨_, (M.d_F_iterate_apply n r z).symm⟩
  rintro ⟨y, hy⟩
  induction r generalizing x y with
  | zero => exact ⟨x, rfl⟩
  | succ r ih =>
    -- `x = F x'` and `y = F y'`, since `d x` is divisible by `p` and `y` is a cocycle.
    obtain ⟨x', rfl⟩ := hM.mem_range_F_iff.2 ⟨p ^ r • y, by rw [smul_smul, ← pow_succ', hy]⟩
    have hdy : (M.d (n + 1) (n + 1 + 1)).hom y = 0 :=
      ((hM.isSMulRegular (n + 1 + 1)).pow (r + 1)) <| by
        beta_reduce
        rw [smul_zero, ← map_nsmul, hy, ← AddCommGrpCat.comp_apply, M.d_comp_d]
        simp
    obtain ⟨y', rfl⟩ := hM.mem_range_F_iff.2 ⟨0, by rw [smul_zero, hdy]⟩
    -- Cancelling `p F` in `p F (d x') = d (F x') = p ^ (r + 1) F y'` gives `d x' = p ^ r y'`.
    have hx' : p ^ r • y' = (M.d n (n + 1)).hom x' := by
      refine hM.injective_F (n + 1) (hM.isSMulRegular (n + 1) ?_)
      beta_reduce
      rw [map_nsmul, smul_smul, ← pow_succ', hy, M.d_F]
    obtain ⟨z, rfl⟩ := ih y' hx'
    exact ⟨z, Function.iterate_succ_apply' _ _ _⟩

/-- On a saturated Dieudonné complex every cocycle is in the image of every power of the
Frobenius. -/
lemma mem_range_F_iterate_of_d_eq_zero {n : ℤ} (r : ℕ) {x : M.X n}
    (hx : (M.d n (n + 1)).hom x = 0) : x ∈ Set.range (⇑(M.F n).hom)^[r] :=
  (hM.mem_range_F_iterate_iff r).2 ⟨0, by rw [smul_zero, hx]⟩

end IsSaturated

end DieudonneComplex

end TauCeti

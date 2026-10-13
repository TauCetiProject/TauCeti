/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Excision

/-!
# Local homology at two points exchanged by an involution

Let `a` be an involution of a T₁ space `S`, and let `p` be a point with `a p ≠ p`. The relative
homology `Hₙ(S, S ∖ {p, a p})` is detected by its images in `Hₙ(S, S ∖ {p})` and
`Hₙ(S, S ∖ {a p})` (`TopPair.singularHomology_inter_hom_ext`), so a class of it is the sum of a
contribution near `p` and a contribution near `a p`, and `a` exchanges the two.

Consequently, let `f : S ⟶ Y` satisfy `f ∘ a = f` and send `S ∖ {p, a p}` into `Y ∖ {y}`, and let
`a` act on a class `s` of `Hₙ(S, S ∖ {p, a p})` by an integer `ε`. Then the image of `s` in
`Hₙ(Y, Y ∖ {y})` is `1 + ε` times the image under `f` of the contribution of `s` near `p`, read in
`Hₙ(U, U ∖ {p})` for any set `U` not containing `a p`
(`TopPair.comp_singularHomologyMap_ofSubsetMap_eq_one_add_smul`). When `U` is an open
neighbourhood of `p`, excision identifies `Hₙ(U, U ∖ {p})` with the local homology `Hₙ(S, S ∖ {p})`.

This is the local-degree computation for a map that factors through the quotient by a free
involution. For instance, the attaching map `Sⁿ → RPⁿ` of the top cell of real projective space is
invariant under the antipodal map, which acts on `Hₙ(Sⁿ)` by `(-1) ^ (n + 1)`, so its local degree
at a point of the top cell of `RPⁿ` is `1 + (-1) ^ (n + 1)` times a local degree `±1`.

Coefficients are an object of an abelian category with coproducts.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 2.2: Proposition 2.30 (degrees as sums of local degrees) and the cellular boundary
  computation for `RPⁿ` in Example 2.42.
-/

public section

noncomputable section

open CategoryTheory Limits Topology

universe w v u

namespace TopPair

variable {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A] (R : A)
  {S Y : TopCat.{w}} [T1Space S] {a : S ⟶ S} {p : S} {U : Set S}

/-- The inclusion `(U, U ∖ {p}) ⟶ (S, S ∖ {p, a p})` for a set `U` not containing `a p`. -/
private def interPairToComplPair (hapU : a p ∉ U) :
    interPair U {p}ᶜ ⟶ ofSubset ({p}ᶜ ∩ {a p}ᶜ : Set S) :=
  ofSubsetMap (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩)
    fun u hu ↦ ⟨hu, fun h ↦ hapU (Set.mem_singleton_iff.1 h ▸ u.2)⟩

omit [T1Space S] in
private lemma interPairToComplPair_fst_apply (hapU : a p ∉ U) (u : (interPair U {p}ᶜ).fst) :
    Hom.fst (interPairToComplPair hapU) u = u.1 :=
  ofSubsetMap_fst_apply _ _ u

omit [T1Space S] in
/-- Followed by the inclusion `(S, S ∖ {p, a p}) ⟶ (S, S ∖ {p})`, the inclusion of
`(U, U ∖ {p})` is the excision map. -/
private lemma interPairToComplPair_comp_ofSubsetMap_id (hapU : a p ∉ U) :
    interPairToComplPair hapU ≫ ofSubsetMap (𝟙 S) (fun _ h ↦ h.1) = excisionMap U {p}ᶜ := by
  refine hom_ext_of_fst _ ?_
  ext u
  -- The ambient spaces of the pairs are `S` and `U` only up to unfolding `TopPair.ofSubset`.
  erw [Hom.fst_comp, ConcreteCategory.comp_apply, interPairToComplPair_fst_apply,
    ofSubsetMap_fst_apply, excisionMap_fst_apply]
  rfl

omit [T1Space S] in
/-- Since `U` misses `a p`, the inclusion `(U, U ∖ {p}) ⟶ (S, S ∖ {a p})` is zero on homology. -/
private lemma singularHomologyMap_interPairToComplPair_comp_eq_zero (hapU : a p ∉ U) (n : ℕ) :
    TopPair.singularHomologyMap
      (interPairToComplPair hapU ≫ ofSubsetMap (𝟙 S) (B' := ({a p}ᶜ : Set S)) fun _ h ↦ h.2)
      R n = 0 :=
  singularHomologyMap_eq_zero_of_fac _ R (TopCat.ofHom (⟨fun u ↦ ⟨u.1, fun h ↦
      hapU (Set.mem_singleton_iff.1 h ▸ u.2)⟩, continuous_subtype_val.subtype_mk _⟩ :
      C(U, ({a p}ᶜ : Set S)))) (by
    ext u
    -- The ambient spaces of the pairs are `S` and `U` only up to unfolding `TopPair.ofSubset`.
    erw [Hom.fst_comp, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
      interPairToComplPair_fst_apply, ofSubsetMap_fst_apply]
    rfl) n

omit [T1Space S] in
/-- Since `a` carries `U` into the complement of `p`, the map `(U, U ∖ {p}) ⟶ (S, S ∖ {p})`
induced by `a` is zero on homology. -/
private lemma singularHomologyMap_interPairToComplPair_comp_ofSubsetMap_comp_eq_zero
    (ha : Function.Involutive a) (hapU : a p ∉ U)
    (haP : Set.MapsTo a ({p}ᶜ ∩ {a p}ᶜ) ({p}ᶜ ∩ {a p}ᶜ)) (n : ℕ) :
    TopPair.singularHomologyMap (interPairToComplPair hapU ≫ ofSubsetMap a haP ≫
      ofSubsetMap (𝟙 S) (fun _ h ↦ h.1)) R n = 0 :=
  singularHomologyMap_eq_zero_of_fac _ R (TopCat.ofHom (⟨fun u ↦ ⟨a u.1, fun h ↦
      hapU ((ha u.1).symm.trans (congrArg a (Set.mem_singleton_iff.1 h)) ▸ u.2)⟩,
      (a.hom.continuous.comp continuous_subtype_val).subtype_mk _⟩ :
      C(U, ({p}ᶜ : Set S)))) (by
    ext u
    -- The ambient spaces of the pairs are `S` and `U` only up to unfolding `TopPair.ofSubset`.
    erw [Hom.fst_comp, Hom.fst_comp, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
      ConcreteCategory.comp_apply, interPairToComplPair_fst_apply, ofSubsetMap_fst_apply,
      ofSubsetMap_fst_apply]
    rfl) n

/-- The map `(S, S ∖ {p}) ⟶ (S, S ∖ {a p})` induced by an involution `a`. -/
private def complSingletonMap (ha : Function.Involutive a) :
    ofSubset ({p}ᶜ : Set S) ⟶ ofSubset ({a p}ᶜ : Set S) :=
  ofSubsetMap a fun _ hs hs' ↦ hs (ha.injective hs')

omit [T1Space S] in
private lemma ofSubsetMap_comp_ofSubsetMap_id_eq (ha : Function.Involutive a)
    (haP : Set.MapsTo a ({p}ᶜ ∩ {a p}ᶜ) ({p}ᶜ ∩ {a p}ᶜ)) :
    ofSubsetMap a haP ≫ ofSubsetMap (𝟙 S) (B' := ({a p}ᶜ : Set S)) (fun _ h ↦ h.2) =
      ofSubsetMap (𝟙 S) (fun _ h ↦ h.1) ≫ complSingletonMap ha := by
  refine hom_ext_of_fst _ ?_
  ext s
  -- The ambient spaces of the pairs are `S` only up to unfolding `TopPair.ofSubset`.
  erw [Hom.fst_comp, Hom.fst_comp, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
    ofSubsetMap_fst_apply, ofSubsetMap_fst_apply, ofSubsetMap_fst_apply, ofSubsetMap_fst_apply]
  rfl

omit [T1Space S] in
private lemma ofSubsetMap_comp_ofSubsetMap_id_comp_complSingletonMap (ha : Function.Involutive a)
    (haP : Set.MapsTo a ({p}ᶜ ∩ {a p}ᶜ) ({p}ᶜ ∩ {a p}ᶜ)) :
    ofSubsetMap a haP ≫ ofSubsetMap (𝟙 S) (fun _ h ↦ h.1) ≫ complSingletonMap ha =
      ofSubsetMap (𝟙 S) (fun _ h ↦ h.2) := by
  refine hom_ext_of_fst _ ?_
  ext s
  erw [Hom.fst_comp, Hom.fst_comp, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
    ofSubsetMap_fst_apply, ofSubsetMap_fst_apply, ofSubsetMap_fst_apply, ofSubsetMap_fst_apply]
  exact ha s

omit [T1Space S] in
private lemma interPairToComplPair_comp_ofSubsetMap (hapU : a p ∉ U) {y : Y} (f : S ⟶ Y)
    (hfP : Set.MapsTo f ({p}ᶜ ∩ {a p}ᶜ) {y}ᶜ)
    (hfU : Set.MapsTo (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ ≫ f)
      (Subtype.val ⁻¹' {p}ᶜ : Set U) {y}ᶜ) :
    interPairToComplPair hapU ≫ ofSubsetMap f hfP = ofSubsetMap _ hfU := by
  refine hom_ext_of_fst _ ?_
  ext u
  erw [Hom.fst_comp, ConcreteCategory.comp_apply, interPairToComplPair_fst_apply,
    ofSubsetMap_fst_apply, ofSubsetMap_fst_apply]
  rfl

omit [T1Space S] in
private lemma interPairToComplPair_comp_ofSubsetMap_comp_ofSubsetMap (hapU : a p ∉ U) {y : Y}
    (f : S ⟶ Y) (hf : ∀ s, f (a s) = f s) (haP : Set.MapsTo a ({p}ᶜ ∩ {a p}ᶜ) ({p}ᶜ ∩ {a p}ᶜ))
    (hfP : Set.MapsTo f ({p}ᶜ ∩ {a p}ᶜ) {y}ᶜ)
    (hfU : Set.MapsTo (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ ≫ f)
      (Subtype.val ⁻¹' {p}ᶜ : Set U) {y}ᶜ) :
    interPairToComplPair hapU ≫ ofSubsetMap a haP ≫ ofSubsetMap f hfP = ofSubsetMap _ hfU := by
  refine hom_ext_of_fst _ ?_
  ext u
  erw [Hom.fst_comp, Hom.fst_comp, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
    interPairToComplPair_fst_apply, ofSubsetMap_fst_apply, ofSubsetMap_fst_apply,
    ofSubsetMap_fst_apply]
  exact hf u.1

/-- **The local degree of a map invariant under an involution.** Let `a` be an involution of a
T₁ space `S`, `p` a point with `a p ≠ p`, and `U` a set not containing `a p`. Let `f : S ⟶ Y`
satisfy `f ∘ a = f` and send `S ∖ {p, a p}` into `Y ∖ {y}`. If `a` acts by `ε` on a class `s` of
`Hₙ(S, S ∖ {p, a p})`, and `t` is a class of `Hₙ(U, U ∖ {p})` with the same image as `s` in
`Hₙ(S, S ∖ {p})`, then `f` sends `s` to `(1 + ε)` times the image of `t` in `Hₙ(Y, Y ∖ {y})`.
The inclusions `haP`, `hfP` and `hfU` are arguments, so that the maps of pairs match those of the
caller. -/
theorem comp_singularHomologyMap_ofSubsetMap_eq_one_add_smul (ha : Function.Involutive a)
    (hp : a p ≠ p) (hapU : a p ∉ U) {y : Y} (f : S ⟶ Y) (hf : ∀ s, f (a s) = f s)
    (haP : Set.MapsTo a ({p}ᶜ ∩ {a p}ᶜ) ({p}ᶜ ∩ {a p}ᶜ))
    (hfP : Set.MapsTo f ({p}ᶜ ∩ {a p}ᶜ) {y}ᶜ)
    (hfU : Set.MapsTo (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ ≫ f)
      (Subtype.val ⁻¹' {p}ᶜ : Set U) {y}ᶜ)
    (n : ℕ) (ε : ℤ) {M : A} (s : M ⟶ (ofSubset ({p}ᶜ ∩ {a p}ᶜ : Set S)).singularHomology R n)
    (hs : s ≫ TopPair.singularHomologyMap (ofSubsetMap a haP) R n = ε • s)
    (t : M ⟶ (interPair U {p}ᶜ).singularHomology R n)
    (ht : t ≫ TopPair.singularHomologyMap (excisionMap U {p}ᶜ) R n =
      s ≫ TopPair.singularHomologyMap (ofSubsetMap (𝟙 S) fun _ h ↦ h.1) R n) :
    s ≫ TopPair.singularHomologyMap (ofSubsetMap f hfP) R n =
      (1 + ε) • (t ≫ TopPair.singularHomologyMap (ofSubsetMap _ hfU) R n) := by
  have hcov : interior ({p}ᶜ : Set S) ∪ interior {a p}ᶜ = Set.univ := by
    rw [isOpen_compl_singleton.interior_eq, isOpen_compl_singleton.interior_eq,
      ← Set.compl_inter, Set.singleton_inter_eq_empty.2 (Set.mem_singleton_iff.not.2 hp.symm),
      Set.compl_empty]
  have hρa := ofSubsetMap_comp_ofSubsetMap_id_eq ha haP
  have haρ := ofSubsetMap_comp_ofSubsetMap_id_comp_complSingletonMap ha haP
  -- The class `s` is the sum of its contribution `t` near `p` and the image of `ε • t` under `a`.
  have hdec : s = t ≫ TopPair.singularHomologyMap (interPairToComplPair hapU) R n + ε • (t ≫
      TopPair.singularHomologyMap (interPairToComplPair hapU ≫ ofSubsetMap a haP) R n) := by
    refine singularHomology_inter_hom_ext R hcov (fun _ h ↦ h.1) (fun _ h ↦ h.2) n ?_ ?_
    · rw [Preadditive.add_comp, Linear.smul_comp, Category.assoc, Category.assoc,
        ← TopPair.singularHomologyMap_comp, ← TopPair.singularHomologyMap_comp,
        interPairToComplPair_comp_ofSubsetMap_id, ht, Category.assoc,
        singularHomologyMap_interPairToComplPair_comp_ofSubsetMap_comp_eq_zero R ha hapU haP,
        comp_zero, smul_zero, add_zero]
    · calc s ≫ TopPair.singularHomologyMap (ofSubsetMap (𝟙 S) fun _ h ↦ h.2) R n
          = (s ≫ TopPair.singularHomologyMap (ofSubsetMap a haP) R n) ≫
              TopPair.singularHomologyMap (ofSubsetMap (𝟙 S) (fun _ h ↦ h.1)) R n ≫
                TopPair.singularHomologyMap (complSingletonMap ha) R n := by
            rw [Category.assoc, ← TopPair.singularHomologyMap_comp,
              ← TopPair.singularHomologyMap_comp, haρ]
        _ = ε • (t ≫ TopPair.singularHomologyMap (excisionMap U {p}ᶜ) R n ≫
              TopPair.singularHomologyMap (complSingletonMap ha) R n) := by
            rw [hs, Linear.smul_comp, reassoc_of% ht]
        _ = (t ≫ TopPair.singularHomologyMap (interPairToComplPair hapU) R n +
              ε • (t ≫ TopPair.singularHomologyMap
                (interPairToComplPair hapU ≫ ofSubsetMap a haP) R n)) ≫
              TopPair.singularHomologyMap (ofSubsetMap (𝟙 S) fun _ h ↦ h.2) R n := by
            conv_rhs => rw [Preadditive.add_comp, Linear.smul_comp, Category.assoc,
              Category.assoc, ← TopPair.singularHomologyMap_comp,
              ← TopPair.singularHomologyMap_comp,
              singularHomologyMap_interPairToComplPair_comp_eq_zero R hapU, comp_zero, zero_add,
              Category.assoc, hρa, ← Category.assoc, interPairToComplPair_comp_ofSubsetMap_id,
              TopPair.singularHomologyMap_comp]
  rw [hdec, Preadditive.add_comp, Linear.smul_comp, Category.assoc, Category.assoc,
    ← TopPair.singularHomologyMap_comp, ← TopPair.singularHomologyMap_comp,
    interPairToComplPair_comp_ofSubsetMap hapU f hfP hfU, Category.assoc,
    interPairToComplPair_comp_ofSubsetMap_comp_ofSubsetMap hapU f hf haP hfP hfU, add_smul,
    one_smul]

end TopPair

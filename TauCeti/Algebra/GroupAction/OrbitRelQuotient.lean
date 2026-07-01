/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.GroupTheory.GroupAction.Quotient
public import TauCeti.Algebra.Group.NormalizerQuotient

/-!
# Generic orbit-relation quotient helpers

This file records small generic additions to Mathlib's `MulAction.orbitRel.Quotient` API.

## Main declarations

* `TauCeti.MulAction.orbitRelQuotientBotEquiv`: the quotient by the trivial subgroup is the
  original space.
* `TauCeti.MulAction.orbitRelQuotientMapOfLE_bot_eq_iff`: equality after the bottom-to-`H`
  quotient map is membership in an `H`-orbit.
* `TauCeti.MulAction.orbitRelQuotient_smul_eq_base_iff`: in a cancellative action, a
  translate has the same `H`-orbit class as the base point exactly when the translator is in
  `H`.
* `TauCeti.MulAction.orbitRelQuotient_smul_eq_smul_iff_normalizerQuotientMk_inv_eq`: for a
  normal subgroup, equality of two translates in the `H`-orbit quotient is equality of the
  corresponding inverse representatives in `N(H) / H`.
* `TauCeti.MulAction.normalizerOrbitRelQuotientPermHom`: the normalizer action on the
  quotient by `H`-orbits.
* `TauCeti.MulAction.normalizerQuotientOrbitRelQuotientPermHom`: the descended action of
  `N(H) / H` on the quotient by `H`-orbits.
-/

public section

namespace TauCeti

namespace MulAction

variable {G X : Type*} [Group G] [MulAction G X]

private lemma eq_of_bot_orbitRel {x y : X}
    (h : _root_.MulAction.orbitRel (⊥ : Subgroup G) X x y) : x = y := by
  rw [_root_.MulAction.orbitRel_apply] at h
  rcases h with ⟨g, hg⟩
  have hg_one : (g : G) = 1 := Subgroup.mem_bot.mp g.2
  have hsmul : (g : G) • y = x := by
    simpa [Subgroup.smul_def] using hg
  rw [hg_one, one_smul] at hsmul
  exact hsmul.symm

/-- Quotienting a group action by the trivial subgroup gives back the original space. -/
noncomputable def orbitRelQuotientBotEquiv :
    _root_.MulAction.orbitRel.Quotient (⊥ : Subgroup G) X ≃ X :=
  { toFun := Quotient.lift (fun x : X => x) fun _ _ h => eq_of_bot_orbitRel h
    invFun := Quotient.mk''
    left_inv := by
      intro x
      refine Quotient.inductionOn' x ?_
      intro x
      rfl
    right_inv := by
      intro x
      rfl }

/-- The bottom-subgroup quotient equivalence sends a class to its representative. -/
@[simp]
lemma orbitRelQuotientBotEquiv_mk (x : X) :
    orbitRelQuotientBotEquiv
        (G := G) (X := X) (Quotient.mk'' x :
          _root_.MulAction.orbitRel.Quotient (⊥ : Subgroup G) X) = x :=
  (orbitRelQuotientBotEquiv (G := G) (X := X)).right_inv x

/-- The inverse bottom-subgroup quotient equivalence sends a point to its quotient class. -/
@[simp]
lemma orbitRelQuotientBotEquiv_symm_apply (x : X) :
    (orbitRelQuotientBotEquiv (G := G) (X := X)).symm x =
      (Quotient.mk'' x : _root_.MulAction.orbitRel.Quotient (⊥ : Subgroup G) X) :=
  ((orbitRelQuotientBotEquiv (G := G) (X := X)).apply_eq_iff_eq_symm_apply).mp
    (orbitRelQuotientBotEquiv_mk (G := G) (X := X) x)

/-- Equality of bottom-subgroup orbit classes is equality of representatives. -/
@[simp]
lemma orbitRelQuotientBot_mk_eq_iff (x y : X) :
    (Quotient.mk'' x : _root_.MulAction.orbitRel.Quotient (⊥ : Subgroup G) X) =
        Quotient.mk'' y ↔
      x = y := by
  constructor
  · intro h
    exact congrArg (orbitRelQuotientBotEquiv (G := G) (X := X)) h
  · intro h
    rw [h]

/-- Orbit relations are monotone in the acting subgroup. -/
lemma orbitRel_le_of_subgroup_le {H K : Subgroup G} (hHK : H ≤ K) :
    _root_.MulAction.orbitRel H X ≤ _root_.MulAction.orbitRel K X := by
  intro x y h
  rw [_root_.MulAction.orbitRel_apply] at h ⊢
  rcases h with ⟨g, hg⟩
  exact ⟨⟨g.1, hHK g.2⟩, hg⟩

/-- The map from the bottom-subgroup quotient to the `H`-quotient is the `H`-orbit class map
under the bottom quotient equivalence. -/
@[simp]
lemma orbitRelQuotientMapOfLE_bot_eq (H : Subgroup G) :
    Setoid.map_of_le (orbitRel_le_of_subgroup_le (G := G) (X := X)
        (bot_le : (⊥ : Subgroup G) ≤ H)) =
      (fun x : X => (Quotient.mk'' x : _root_.MulAction.orbitRel.Quotient H X)) ∘
        orbitRelQuotientBotEquiv (G := G) (X := X) := by
  ext x
  refine Quotient.inductionOn' x ?_
  intro x
  rfl

/-- Equality in an `H`-orbit quotient can be checked after choosing representatives through
the bottom-subgroup quotient. -/
lemma orbitRelQuotientMapOfLE_bot_eq_iff (H : Subgroup G)
    (x y : _root_.MulAction.orbitRel.Quotient (⊥ : Subgroup G) X) :
    Setoid.map_of_le (orbitRel_le_of_subgroup_le (G := G) (X := X)
        (bot_le : (⊥ : Subgroup G) ≤ H)) x =
        Setoid.map_of_le (orbitRel_le_of_subgroup_le (G := G) (X := X)
          (bot_le : (⊥ : Subgroup G) ≤ H)) y ↔
      orbitRelQuotientBotEquiv (G := G) (X := X) x ∈
        _root_.MulAction.orbit H (orbitRelQuotientBotEquiv (G := G) (X := X) y) := by
  simp [orbitRelQuotientMapOfLE_bot_eq, Quotient.eq'', _root_.MulAction.orbitRel_apply]

/-- In a cancellative action, a translate has the same subgroup-orbit quotient class as the
base point exactly when the translating group element belongs to the subgroup. -/
lemma orbitRelQuotient_smul_eq_base_iff [IsCancelSMul G X] (H : Subgroup G) (g : G) (x : X) :
    (Quotient.mk'' (g • x) : _root_.MulAction.orbitRel.Quotient H X) =
        Quotient.mk'' x ↔
      g ∈ H := by
  constructor
  · intro h
    rw [Quotient.eq'', _root_.MulAction.orbitRel_apply] at h
    rcases h with ⟨k, hk⟩
    have hkG : (k : G) • x = g • x := by
      simpa [Subgroup.smul_def] using hk
    exact (IsCancelSMul.right_cancel (k : G) g x hkG).symm ▸ k.2
  · intro hg
    rw [Quotient.eq'', _root_.MulAction.orbitRel_apply]
    exact ⟨⟨g, hg⟩, rfl⟩

/-- In a cancellative action by `G`, equality of two translates in the quotient by a normal
subgroup `H` is equality of the corresponding inverse representatives in the normalizer
quotient `N(H) / H`. -/
lemma orbitRelQuotient_smul_eq_smul_iff_normalizerQuotientMk_inv_eq [IsCancelSMul G X]
    (H : Subgroup G) [H.Normal] (x : X) (g k : G) :
    (Quotient.mk'' (g • x) : _root_.MulAction.orbitRel.Quotient H X) =
        Quotient.mk'' (k • x) ↔
      Subgroup.normalizerQuotientMk H
          ⟨g⁻¹, by simp [_root_.Subgroup.normalizer_eq_top (H := H)]⟩ =
        Subgroup.normalizerQuotientMk H
          ⟨k⁻¹, by simp [_root_.Subgroup.normalizer_eq_top (H := H)]⟩ := by
  constructor
  · intro h
    rw [Quotient.eq'', _root_.MulAction.orbitRel_apply] at h
    rcases h with ⟨l, hl⟩
    rw [Subgroup.normalizerQuotientMk_eq_iff_div_mem]
    have hmul : ((l : G) * k) • x = g • x := by
      simpa [Subgroup.smul_def, smul_smul] using hl
    have hg : (l : G) * k = g := IsCancelSMul.right_cancel _ _ x hmul
    rw [← hg]
    simpa [div_eq_mul_inv, mul_assoc] using
      (inferInstance : H.Normal).conj_mem' _ (H.inv_mem l.2) k
  · intro h
    rw [Subgroup.normalizerQuotientMk_eq_iff_div_mem] at h
    rw [Quotient.eq'', _root_.MulAction.orbitRel_apply]
    have hmem : g * k⁻¹ ∈ H := by
      simpa [mul_assoc] using (inferInstance : H.Normal).conj_mem _ (H.inv_mem h) g
    exact ⟨⟨g * k⁻¹, hmem⟩, by simp [Subgroup.smul_def, smul_smul]⟩

private lemma normalizer_smul_mem_orbit (H : Subgroup G)
    (g : _root_.Subgroup.normalizer (H : Set G))
    {x y : X} (hxy : x ∈ _root_.MulAction.orbit H y) :
    (g : G) • x ∈ _root_.MulAction.orbit H ((g : G) • y) := by
  rcases hxy with ⟨h, hh⟩
  refine ⟨⟨(g : G) * h * (g : G)⁻¹, ?_⟩, ?_⟩
  · exact ((_root_.Subgroup.mem_normalizer_iff.mp g.2) (h : G)).1 h.2
  · rw [← hh]
    simp [Subgroup.smul_def, mul_smul]

/-- A normalizer representative acts on the quotient by `H`-orbits. -/
def normalizerOrbitRelQuotientMap (H : Subgroup G)
    (g : _root_.Subgroup.normalizer (H : Set G)) :
    _root_.MulAction.orbitRel.Quotient H X → _root_.MulAction.orbitRel.Quotient H X :=
  Quotient.map' (fun x : X => (g : G) • x) fun x y hxy => by
    rw [_root_.MulAction.orbitRel_apply] at hxy ⊢
    exact normalizer_smul_mem_orbit H g hxy

/-- The normalizer action on an orbit quotient sends a class to the class of its translate. -/
@[simp]
lemma normalizerOrbitRelQuotientMap_apply (H : Subgroup G)
    (g : _root_.Subgroup.normalizer (H : Set G)) (x : X) :
    normalizerOrbitRelQuotientMap H g
        (Quotient.mk'' x : _root_.MulAction.orbitRel.Quotient H X) =
      Quotient.mk'' ((g : G) • x) :=
  by simp [normalizerOrbitRelQuotientMap]

/-- The normalizer representative `1` acts trivially on the orbit quotient. -/
@[simp]
lemma normalizerOrbitRelQuotientMap_one (H : Subgroup G) :
    normalizerOrbitRelQuotientMap (X := X) H ⟨1, by simp⟩ = id := by
  ext x
  refine Quotient.inductionOn' x ?_
  intro x
  simp [normalizerOrbitRelQuotientMap]

/-- Normalizer representatives act by composition on the orbit quotient. -/
@[simp]
lemma normalizerOrbitRelQuotientMap_mul (H : Subgroup G)
    (g k : _root_.Subgroup.normalizer (H : Set G)) :
    normalizerOrbitRelQuotientMap (X := X) H (g * k) =
      normalizerOrbitRelQuotientMap H g ∘ normalizerOrbitRelQuotientMap H k := by
  ext x
  refine Quotient.inductionOn' x ?_
  intro x
  simp [normalizerOrbitRelQuotientMap, mul_smul]

/-- A normalizer representative acts on the orbit quotient by a permutation. -/
def normalizerOrbitRelQuotientEquiv (H : Subgroup G)
    (g : _root_.Subgroup.normalizer (H : Set G)) :
    Equiv.Perm (_root_.MulAction.orbitRel.Quotient H X) where
  toFun := normalizerOrbitRelQuotientMap H g
  invFun := normalizerOrbitRelQuotientMap H g⁻¹
  left_inv := by
    intro x
    refine Quotient.inductionOn' x ?_
    intro x
    simp [normalizerOrbitRelQuotientMap]
  right_inv := by
    intro x
    refine Quotient.inductionOn' x ?_
    intro x
    simp [normalizerOrbitRelQuotientMap]

/-- A normalizer representative permutes orbit classes by translating representatives. -/
@[simp]
lemma normalizerOrbitRelQuotientEquiv_apply (H : Subgroup G)
    (g : _root_.Subgroup.normalizer (H : Set G)) (x : X) :
    normalizerOrbitRelQuotientEquiv H g
        (Quotient.mk'' x : _root_.MulAction.orbitRel.Quotient H X) =
      Quotient.mk'' ((g : G) • x) :=
  by simp [normalizerOrbitRelQuotientEquiv]

/-- The inverse normalizer permutation translates representatives by the inverse element. -/
@[simp]
lemma normalizerOrbitRelQuotientEquiv_symm_apply (H : Subgroup G)
    (g : _root_.Subgroup.normalizer (H : Set G)) (x : X) :
    (normalizerOrbitRelQuotientEquiv H g).symm
        (Quotient.mk'' x : _root_.MulAction.orbitRel.Quotient H X) =
      Quotient.mk'' ((g : G)⁻¹ • x) :=
  by simp [normalizerOrbitRelQuotientEquiv]

/-- The normalizer action on the orbit quotient as a permutation representation. -/
noncomputable def normalizerOrbitRelQuotientPermHom (H : Subgroup G) :
    _root_.Subgroup.normalizer (H : Set G) →*
      Equiv.Perm (_root_.MulAction.orbitRel.Quotient H X) where
  toFun := normalizerOrbitRelQuotientEquiv H
  map_one' := by
    ext x
    refine Quotient.inductionOn' x ?_
    intro x
    simp [normalizerOrbitRelQuotientEquiv, normalizerOrbitRelQuotientMap]
  map_mul' := by
    intro g k
    ext x
    refine Quotient.inductionOn' x ?_
    intro x
    simp only [normalizerOrbitRelQuotientEquiv_apply, Equiv.Perm.coe_mul, Function.comp_apply]
    have hgk : ((g * k : _root_.Subgroup.normalizer (H : Set G)) : G) = (g : G) * (k : G) :=
      rfl
    rw [hgk]
    rw [mul_smul]

/-- The normalizer permutation homomorphism sends representatives to their translates. -/
@[simp]
lemma normalizerOrbitRelQuotientPermHom_apply (H : Subgroup G)
    (g : _root_.Subgroup.normalizer (H : Set G)) (x : X) :
    normalizerOrbitRelQuotientPermHom (X := X) H g
        (Quotient.mk'' x : _root_.MulAction.orbitRel.Quotient H X) =
      Quotient.mk'' ((g : G) • x) :=
  by simp [normalizerOrbitRelQuotientPermHom]

/-- Any normalizer representative whose underlying group element lies in `H` acts trivially
on the quotient by `H`-orbits. -/
lemma normalizerOrbitRelQuotientPermHom_eq_one_of_mem
    (H : Subgroup G) (g : _root_.Subgroup.normalizer (H : Set G)) (hg : (g : G) ∈ H) :
    normalizerOrbitRelQuotientPermHom (X := X) H g = 1 := by
  ext x
  refine Quotient.inductionOn' x ?_
  intro x
  rw [normalizerOrbitRelQuotientPermHom_apply]
  exact Quotient.sound' ⟨⟨(g : G), hg⟩, rfl⟩

/-- The action of the normalizer on an orbit quotient descends to `N(H) / H`. -/
noncomputable def normalizerQuotientOrbitRelQuotientPermHom (H : Subgroup G) :
    Subgroup.normalizerQuotient H →*
      Equiv.Perm (_root_.MulAction.orbitRel.Quotient H X) :=
  Subgroup.normalizerQuotientLift H (normalizerOrbitRelQuotientPermHom (X := X) H)
    (normalizerOrbitRelQuotientPermHom_eq_one_of_mem (X := X) H)

/-- The descended normalizer-quotient action sends a normalizer representative to the
corresponding translate on orbit classes. -/
@[simp]
lemma normalizerQuotientOrbitRelQuotientPermHom_mk_apply (H : Subgroup G)
    (g : _root_.Subgroup.normalizer (H : Set G)) (x : X) :
    normalizerQuotientOrbitRelQuotientPermHom (X := X) H
        (Subgroup.normalizerQuotientMk H g)
        (Quotient.mk'' x : _root_.MulAction.orbitRel.Quotient H X) =
      Quotient.mk'' ((g : G) • x) :=
  by simp [normalizerQuotientOrbitRelQuotientPermHom]

/-- The normalizer quotient `N(H) / H` acts on the quotient by `H`-orbits. -/
noncomputable abbrev normalizerQuotientOrbitRelQuotientMulAction (H : Subgroup G) :
    MulAction (Subgroup.normalizerQuotient H) (_root_.MulAction.orbitRel.Quotient H X) :=
  MulAction.compHom (_root_.MulAction.orbitRel.Quotient H X)
    (normalizerQuotientOrbitRelQuotientPermHom (X := X) H)

end MulAction

end TauCeti

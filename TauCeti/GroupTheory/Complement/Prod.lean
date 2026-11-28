/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.Subgroup.Prod
public import TauCeti.GroupTheory.Complement.Local
import Mathlib.GroupTheory.NoncommCoprod

/-!
# Global, local, and product decompositions for complementary subgroups

This file collects two complementary sets of results around `Subgroup.IsComplement'` and direct
products:

1. **Complements in direct products (`G × G'`)**: Product subgroups `H₁.prod H₂` and `D₁.prod D₂`
   are global (or local) complements in `G × G'` precisely when their coordinate factors are
   complements in `G` and `G'`. More generally, even against an arbitrary subgroup of `G × G'`
   that is not itself a product subgroup, a coordinate subgroup `N.prod ⊥` has a global complement
   in `G × G'` (or a local complement in `H.prod ⊥`) if and only if `N` has a global complement in
   `G` (or a local complement in `H`), and similarly for `⊥.prod N`. No normality, commutativity,
   or finiteness assumptions are required.
2. **Product isomorphism and character extension (`P × H ≃* G`)**: Given normal complementary
   subgroups `P` and `H` (`P.IsComplement' H`, `[P.Normal]`, `[H.Normal]`) of a group `G`:
   * `Subgroup.IsComplement'.prodMulEquiv`: the canonical multiplicative isomorphism `P × H ≃* G`
     sending `(p, h)` to `(p : G) * (h : G)`.
   * `Subgroup.IsComplement'.extendChar`: given any commutative monoid `M` and homomorphisms
     `φ : P →* M` and `χ : H →* M`, the unique homomorphism `G →* M` sending
     `(p : G) * (h : G)` to `φ p * χ h`.
-/

public section

namespace Subgroup

variable {G G' : Type*} [Group G] [Group G']

/-- Coordinatewise complements form a complement in the direct product. -/
@[to_additive IsComplement'.prod /-- Coordinatewise additive complements form a complement in the
direct product. -/]
theorem IsComplement'.prod {H₁ D₁ : Subgroup G} {H₂ D₂ : Subgroup G'}
    (h₁ : H₁.IsComplement' D₁) (h₂ : H₂.IsComplement' D₂) :
    (H₁.prod H₂).IsComplement' (D₁.prod D₂) := by
  rw [isComplement'_def, isComplement_iff_existsUnique_inv_mul_mem]
  intro ⟨g₁, g₂⟩
  obtain ⟨x₁, hx₁, hux₁⟩ := isComplement_iff_existsUnique_inv_mul_mem.mp h₁ g₁
  obtain ⟨x₂, hx₂, hux₂⟩ := isComplement_iff_existsUnique_inv_mul_mem.mp h₂ g₂
  refine ⟨⟨(x₁, x₂), x₁.property, x₂.property⟩, ⟨hx₁, hx₂⟩, ?_⟩
  rintro ⟨⟨y₁, y₂⟩, hy₁, hy₂⟩ ⟨hdy₁, hdy₂⟩
  ext
  · exact congrArg Subtype.val (hux₁ ⟨y₁, hy₁⟩ hdy₁)
  · exact congrArg Subtype.val (hux₂ ⟨y₂, hy₂⟩ hdy₂)

/-- If two product subgroups are complements, so are their first factors. -/
@[to_additive IsComplement'.of_prod_left /-- If two products of additive subgroups are complements,
so are their first factors. -/]
theorem IsComplement'.of_prod_left {H₁ D₁ : Subgroup G} {H₂ D₂ : Subgroup G'}
    (h : (H₁.prod H₂).IsComplement' (D₁.prod D₂)) : H₁.IsComplement' D₁ := by
  rw [isComplement'_def, isComplement_iff_existsUnique_inv_mul_mem]
  intro g₁
  obtain ⟨⟨⟨x₁, x₂⟩, hx₁, _⟩, ⟨hdx₁, _⟩, hu⟩ :=
    isComplement_iff_existsUnique_inv_mul_mem.mp h (g₁, 1)
  refine ⟨⟨x₁, hx₁⟩, hdx₁, fun ⟨y₁, hy₁⟩ hdy₁ => ?_⟩
  have hy := hu ⟨(y₁, 1), hy₁, H₂.one_mem⟩ ⟨hdy₁, by simp⟩
  have hx := hu ⟨(x₁, 1), hx₁, H₂.one_mem⟩ ⟨hdx₁, by simp⟩
  exact Subtype.ext (congrArg (Prod.fst ∘ Subtype.val) (hy.trans hx.symm))

/-- If two product subgroups are complements, so are their second factors. -/
@[to_additive IsComplement'.of_prod_right /-- If two products of additive subgroups are complements,
so are their second factors. -/]
theorem IsComplement'.of_prod_right {H₁ D₁ : Subgroup G} {H₂ D₂ : Subgroup G'}
    (h : (H₁.prod H₂).IsComplement' (D₁.prod D₂)) : H₂.IsComplement' D₂ := by
  rw [isComplement'_def, isComplement_iff_existsUnique_inv_mul_mem]
  intro g₂
  obtain ⟨⟨⟨x₁, x₂⟩, _, hx₂⟩, ⟨_, hdx₂⟩, hu⟩ :=
    isComplement_iff_existsUnique_inv_mul_mem.mp h (1, g₂)
  refine ⟨⟨x₂, hx₂⟩, hdx₂, fun ⟨y₂, hy₂⟩ hdy₂ => ?_⟩
  have hy := hu ⟨(1, y₂), H₁.one_mem, hy₂⟩ ⟨by simp, hdy₂⟩
  have hx := hu ⟨(1, x₂), H₁.one_mem, hx₂⟩ ⟨by simp, hdx₂⟩
  exact Subtype.ext (congrArg (Prod.snd ∘ Subtype.val) (hy.trans hx.symm))

/-- Product subgroups are complements in `G × G'` if and only if their factors are complements. -/
@[to_additive (attr := simp) isComplement'_prod_prod /-- Products of additive subgroups are
complements if and only if their factors are complements. -/]
theorem isComplement'_prod_prod {H₁ D₁ : Subgroup G} {H₂ D₂ : Subgroup G'} :
    (H₁.prod H₂).IsComplement' (D₁.prod D₂) ↔ H₁.IsComplement' D₁ ∧ H₂.IsComplement' D₂ :=
  ⟨fun h => ⟨h.of_prod_left, h.of_prod_right⟩, fun ⟨h₁, h₂⟩ => h₁.prod h₂⟩

/-- Any complement of `N.prod ⊥` in `G × G'` pulls back along the left inclusion to a complement
of `N` in `G`. -/
theorem IsComplement'.of_prod_bot {N : Subgroup G} {D : Subgroup (G × G')}
    (h : (N.prod (⊥ : Subgroup G')).IsComplement' D) :
    N.IsComplement' (D.comap (MonoidHom.inl G G')) := by
  rw [← map_inl] at h
  exact h.of_map fun _ _ hx => congrArg Prod.fst hx

/-- Any complement of `⊥.prod N` in `G × G'` pulls back along the right inclusion to a complement
of `N` in `G'`. -/
theorem IsComplement'.of_bot_prod {N : Subgroup G'} {D : Subgroup (G × G')}
    (h : ((⊥ : Subgroup G).prod N).IsComplement' D) :
    N.IsComplement' (D.comap (MonoidHom.inr G G')) := by
  rw [← map_inr] at h
  exact h.of_map fun _ _ hy => congrArg Prod.snd hy

/-- `N.prod ⊥` has a complement in `G × G'` if and only if `N` has a complement in `G`. -/
@[simp]
theorem exists_isComplement'_prod_bot_iff {N : Subgroup G} :
    (∃ D : Subgroup (G × G'), (N.prod (⊥ : Subgroup G')).IsComplement' D) ↔
      ∃ D : Subgroup G, N.IsComplement' D :=
  ⟨fun ⟨_, hD⟩ => ⟨_, hD.of_prod_bot⟩, fun ⟨D, hD⟩ => ⟨D.prod ⊤, hD.prod isComplement'_bot_top⟩⟩

/-- `⊥.prod N` has a complement in `G × G'` if and only if `N` has a complement in `G'`. -/
@[simp]
theorem exists_isComplement'_bot_prod_iff {N : Subgroup G'} :
    (∃ D : Subgroup (G × G'), ((⊥ : Subgroup G).prod N).IsComplement' D) ↔
      ∃ D : Subgroup G', N.IsComplement' D :=
  ⟨fun ⟨_, hD⟩ => ⟨_, hD.of_bot_prod⟩,
    fun ⟨D, hD⟩ => ⟨(⊤ : Subgroup G).prod D, isComplement'_bot_top.prod hD⟩⟩

/-- Product subgroups form a local complement in `G × G'` if and only if they do in each factor. -/
@[simp]
theorem isLocalComplement_prod_prod {N₁ K₁ H₁ : Subgroup G} {N₂ K₂ H₂ : Subgroup G'} :
    (N₁.prod N₂).IsLocalComplement (K₁.prod K₂) (H₁.prod H₂) ↔
      N₁.IsLocalComplement K₁ H₁ ∧ N₂.IsLocalComplement K₂ H₂ := by
  simp only [isLocalComplement_iff, prod_inf_prod, prod_sup_prod, prod_eq_bot_iff,
    prod_eq_prod_iff, and_and_and_comm]

/-- Coordinatewise local complements form a local complement in the direct product. -/
theorem IsLocalComplement.prod {N₁ K₁ H₁ : Subgroup G} {N₂ K₂ H₂ : Subgroup G'}
    (h₁ : N₁.IsLocalComplement K₁ H₁) (h₂ : N₂.IsLocalComplement K₂ H₂) :
    (N₁.prod N₂).IsLocalComplement (K₁.prod K₂) (H₁.prod H₂) :=
  isLocalComplement_prod_prod.mpr ⟨h₁, h₂⟩

/-- Any local complement of `N.prod ⊥` in `H.prod ⊥` pulls back along the left inclusion to a
local complement of `N` in `H`. -/
theorem IsLocalComplement.of_prod_bot {N H : Subgroup G} {K : Subgroup (G × G')}
    (h : (N.prod (⊥ : Subgroup G')).IsLocalComplement K (H.prod ⊥)) :
    N.IsLocalComplement (K.comap (MonoidHom.inl G G')) H := by
  rw [← map_inl, ← map_inl] at h
  exact h.of_map fun _ _ hx => congrArg Prod.fst hx

/-- Any local complement of `⊥.prod N` in `⊥.prod H` pulls back along the right inclusion to a
local complement of `N` in `H`. -/
theorem IsLocalComplement.of_bot_prod {N H : Subgroup G'} {K : Subgroup (G × G')}
    (h : ((⊥ : Subgroup G).prod N).IsLocalComplement K ((⊥ : Subgroup G).prod H)) :
    N.IsLocalComplement (K.comap (MonoidHom.inr G G')) H := by
  rw [← map_inr, ← map_inr] at h
  exact h.of_map fun _ _ hy => congrArg Prod.snd hy

/-- `N.prod ⊥` has a local complement in `H.prod ⊥` if and only if `N` has a local complement in
`H`. -/
@[simp]
theorem exists_isLocalComplement_prod_bot_iff {N H : Subgroup G} :
    (∃ K : Subgroup (G × G'), (N.prod (⊥ : Subgroup G')).IsLocalComplement K (H.prod ⊥)) ↔
      ∃ K : Subgroup G, N.IsLocalComplement K H := by
  rw [← map_inl, ← map_inl]
  exact exists_isLocalComplement_map_iff fun _ _ hx => congrArg Prod.fst hx

/-- `⊥.prod N` has a local complement in `⊥.prod H` if and only if `N` has a local complement in
`H`. -/
@[simp]
theorem exists_isLocalComplement_bot_prod_iff {N H : Subgroup G'} :
    (∃ K : Subgroup (G × G'),
      ((⊥ : Subgroup G).prod N).IsLocalComplement K ((⊥ : Subgroup G).prod H)) ↔
      ∃ K : Subgroup G', N.IsLocalComplement K H := by
  rw [← map_inr, ← map_inr]
  exact exists_isLocalComplement_map_iff fun _ _ hy => congrArg Prod.snd hy

end Subgroup

namespace Subgroup.IsComplement'

section ProdMulEquiv

variable {G : Type*} [Group G] {P H : Subgroup G} [P.Normal] [H.Normal]

/-- The multiplicative isomorphism `P × H ≃* G` induced by normal complementary subgroups
`P.IsComplement' H` in a group `G`. -/
noncomputable def prodMulEquiv (hPH : P.IsComplement' H) : P × H ≃* G :=
  MulEquiv.ofBijective
    (P.subtype.noncommCoprod H.subtype fun p h ↦
      Subgroup.commute_of_normal_of_disjoint P H ‹_› ‹_› hPH.disjoint
        p h p.property h.property) <| by
    convert (Subgroup.isComplement_iff_bijective P H).mp hPH using 1
    ext ⟨p, h⟩
    exact MonoidHom.noncommCoprod_apply P.subtype H.subtype _ (p, h)

/-- `prodMulEquiv` sends `(p, h)` to `(p : G) * (h : G)`. -/
@[simp]
theorem prodMulEquiv_apply (hPH : P.IsComplement' H) (p : P) (h : H) :
    hPH.prodMulEquiv (p, h) = (p : G) * (h : G) := by
  simpa [prodMulEquiv] using MonoidHom.noncommCoprod_apply P.subtype H.subtype _ (p, h)

/-- The inverse of `prodMulEquiv` sends `(p : G) * (h : G)` to `(p, h)`. -/
@[simp]
theorem prodMulEquiv_symm_mul (hPH : P.IsComplement' H) (p : P) (h : H) :
    hPH.prodMulEquiv.symm ((p : G) * (h : G)) = (p, h) :=
  (MulEquiv.symm_apply_eq hPH.prodMulEquiv).mpr (hPH.prodMulEquiv_apply p h).symm

end ProdMulEquiv

section ExtendChar

variable {M G : Type*} [CommMonoid M] [Group G] {P H : Subgroup G} [P.Normal] [H.Normal]

/-- Given normal complementary subgroups `P` and `H` of a group `G` and a commutative monoid `M`,
combine homomorphisms `φ : P →* M` and `χ : H →* M` into the unique homomorphism `G →* M`
sending `p * h ↦ φ(p) χ(h)`. -/
noncomputable def extendChar (hPH : P.IsComplement' H) (φ : P →* M) (χ : H →* M) : G →* M :=
  (φ.coprod χ).comp hPH.prodMulEquiv.symm.toMonoidHom

/-- `extendChar hPH φ χ` evaluates at `g : G` via the coordinates of `hPH.prodMulEquiv.symm g`. -/
theorem extendChar_apply (hPH : P.IsComplement' H) (φ : P →* M) (χ : H →* M) (g : G) :
    hPH.extendChar φ χ g = φ (hPH.prodMulEquiv.symm g).1 * χ (hPH.prodMulEquiv.symm g).2 := by
  simp [extendChar]

/-- `extendChar hPH φ χ` sends `(p : G) * (h : G)` to `φ p * χ h`. -/
theorem extendChar_mul (hPH : P.IsComplement' H) (φ : P →* M) (χ : H →* M) (p : P) (h : H) :
    hPH.extendChar φ χ ((p : G) * (h : G)) = φ p * χ h := by
  simp [extendChar]

/-- Evaluating `extendChar hPH φ χ` at `(p : G)` for `p : P` gives `φ p`. -/
@[simp]
theorem extendChar_coe_left (hPH : P.IsComplement' H) (φ : P →* M) (χ : H →* M) (p : P) :
    hPH.extendChar φ χ (p : G) = φ p := by
  simpa using hPH.extendChar_mul φ χ p 1

/-- Evaluating `extendChar hPH φ χ` at `(h : G)` for `h : H` gives `χ h`. -/
@[simp]
theorem extendChar_coe_right (hPH : P.IsComplement' H) (φ : P →* M) (χ : H →* M) (h : H) :
    hPH.extendChar φ χ (h : G) = χ h := by
  simpa using hPH.extendChar_mul φ χ 1 h

/-- Restricting `extendChar hPH φ χ` to `P` recovers `φ`. -/
@[simp]
theorem extendChar_comp_left (hPH : P.IsComplement' H) (φ : P →* M) (χ : H →* M) :
    (hPH.extendChar φ χ).comp P.subtype = φ :=
  MonoidHom.ext fun p ↦ by simp

/-- Restricting `extendChar hPH φ χ` to `H` recovers `χ`. -/
@[simp]
theorem extendChar_comp_right (hPH : P.IsComplement' H) (φ : P →* M) (χ : H →* M) :
    (hPH.extendChar φ χ).comp H.subtype = χ :=
  MonoidHom.ext fun h ↦ by simp

/-- Every homomorphism of `G` into `M` is `extendChar` of its restrictions to `P` and `H`. -/
@[simp]
theorem extendChar_comp_self (hPH : P.IsComplement' H) (ψ : G →* M) :
    hPH.extendChar (ψ.comp P.subtype) (ψ.comp H.subtype) = ψ :=
  MonoidHom.ext fun g ↦ by
    obtain ⟨⟨p, h⟩, rfl⟩ := hPH.prodMulEquiv.surjective g
    rw [prodMulEquiv_apply]
    simp

end ExtendChar

end Subgroup.IsComplement'

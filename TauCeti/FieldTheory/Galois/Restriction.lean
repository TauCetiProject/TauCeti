/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Galois.Infinite
import TauCeti.FieldTheory.Galois.FixedField
import TauCeti.FieldTheory.KrullTopology
import TauCeti.GroupTheory.Index.Basic

/-!
# Restricting automorphisms along an embedding of a normal extension

Mathlib's `AlgEquiv.restrictNormalHom` restricts automorphisms of `K/F` to a normal subextension
`M/F` given by a scalar tower `F → M → K`. This file restricts along an arbitrary embedding
`f : M →ₐ[F] K` instead, which is convenient when `M` is an intermediate field sitting inside `K`
through a map other than the algebra map (for example an `IntermediateField.inclusion`).

In an abstract scalar tower with a normal intermediate field, restriction to the intermediate
field is the identity precisely when the automorphism fixes it pointwise; its kernel is the image
of restriction of scalars. For any scalar tower `M/L/K`, `TauCeti.embeddingSubgroup K L M` packages
the subgroup of `Gal(M/K)` fixing the image of `L`, together with its Galois-correspondence,
restriction, and conjugation transport properties.

## Main definitions and results

* `AlgHom.restrictNormalHom`: restriction `Gal(K/F) →* Gal(M/F)` along `f : M →ₐ[F] K`.
* `AlgHom.restrictNormalHom_eq_iff`: `f.restrictNormalHom σ` is the unique automorphism of `M`
  intertwined with `σ` by `f`.
* `AlgHom.restrictNormalHom_toAlgHom`: for the algebra map of a scalar tower this is
  `AlgEquiv.restrictNormalHom`.
* `IntermediateField.restrictNormalHom_val`: for the inclusion of an intermediate field this is
  `AlgEquiv.restrictNormalHom`.
* `IntermediateField.units_map_val_restrictNormalHom`: the inclusion of units of a normal
  intermediate field intertwines restriction with the action on units.
* `AlgHom.restrictNormalHom_comp`: precomposing the embedding with an automorphism conjugates
  restriction.
* `AlgHom.restrictNormalHom_restrictNormalHom`: restriction along a composite of embeddings is
  the composite of the restrictions.
* `IntermediateField.normalClosure_eq_fieldRange` and `AlgHom.exists_comp_eq_of_normal`: the
  embeddings of a normal extension all have the same image and differ by automorphisms.
* `AlgHom.restrictNormalHom_surjective` and `AlgHom.ker_restrictNormalHom`: for a normal `K/F`
  restriction is surjective, and its kernel is the subgroup fixing the image of `f`.
* `IntermediateField.fixingSubgroup_normal`: the fixing subgroup of a normal intermediate field is
  a normal subgroup.
* `AlgHom.normal_fieldRange`: the image of a normal extension is normal.
* `AlgHom.restrictNormalHomOfLE`: in the other direction, restriction `Gal(M/F) →* Gal(N/F)` to a
  normal intermediate field `N` of `K` lying in the image of `f`, with
  `AlgHom.coe_restrictNormalHomOfLE_apply` and `AlgHom.restrictNormalHomOfLE_surjective`.
* `TauCeti.embeddingSubgroup`: the subgroup `Gal(M/L) ≤ Gal(M/K)` fixing the image of `L` in `M`,
  with `TauCeti.range_restrictScalarsHom_eq_embeddingSubgroup`,
  `TauCeti.embeddingSubgroup_normal`, `TauCeti.algEquivEquivEmbeddingSubgroup`,
  `TauCeti.equivFixedFieldEmbeddingSubgroup`, `TauCeti.coe_equivFixedFieldEmbeddingSubgroup_apply`,
  `TauCeti.autCongr_equivFixedFieldEmbeddingSubgroup_comp_restrictNormalHom`,
  `IsGalois.tower_bot_of_normal`,
  `TauCeti.embeddingSubgroup_intermediateField`, `TauCeti.fixedField_embeddingSubgroup`,
  `TauCeti.natCard_embeddingSubgroup`, `TauCeti.index_embeddingSubgroup`,
  `TauCeti.comap_restrictNormalHom_embeddingSubgroup`, and
  `TauCeti.map_autCongr_embeddingSubgroup`.
* `AlgEquiv.restrictNormal_eq_one_iff_algebraMap`: restriction is trivial precisely when the
  automorphism fixes the intermediate field pointwise.
* `AlgEquiv.mem_range_restrictScalarsHom_iff_restrictNormal_eq_one` and
  `AlgEquiv.range_restrictScalarsHom_eq_ker_restrictNormalHom`: the restriction kernel is
  the image of restriction of scalars.
* `AlgEquiv.index_range_restrictScalarsHom`: in a finite Galois tower `K ⊆ L ⊆ M`, the image of
  `Gal(M/L)` in `Gal(M/K)` has index `[L : K]`.
* `AlgEquiv.restrictNormal_mul_restrictScalars`: multiplying by an automorphism of the top field
  over the intermediate one does not change the restriction.
* `AlgEquiv.restrictNormalHom_of_compatible`: a compatible pair of maps between normal
  intermediate fields of `Ω/K` carries restriction to the larger field to restriction to the
  smaller field.
* `AlgEquiv.restrictNormalHom_adjoin_simple_eq_one_iff`: restriction to a normal simple
  subextension `F⟮α⟯` is trivial precisely when the automorphism fixes `α`.
-/

public section

namespace TauCeti

section RestrictAlong

variable {F K M : Type*} [Field F] [Field K] [Field M] [Algebra F K] [Algebra F M]

/-- The image of a normal extension `M/F` under an `F`-embedding is normal over `F`. -/
instance _root_.AlgHom.normal_fieldRange (f : M →ₐ[F] K) [Normal F M] : Normal F f.fieldRange :=
  Normal.of_algEquiv f.equivFieldRange

/-- Restriction of automorphisms along an embedding `f : M →ₐ[F] K` of a normal extension `M/F`.
Every `σ : Gal(K/F)` maps the image of `f` to itself, and `f.restrictNormalHom σ` is the
automorphism of `M` it induces, so that `f (f.restrictNormalHom σ x) = σ (f x)`
(`AlgHom.restrictNormalHom_commutes`). For the algebra map of a scalar tower this is
`AlgEquiv.restrictNormalHom` (`AlgHom.restrictNormalHom_toAlgHom`). -/
noncomputable def _root_.AlgHom.restrictNormalHom (f : M →ₐ[F] K) [Normal F M] :
    Gal(K/F) →* Gal(M/F) :=
  letI := f.toRingHom.toAlgebra
  haveI : IsScalarTower F M K := IsScalarTower.of_algebraMap_eq fun x ↦ (f.commutes x).symm
  AlgEquiv.restrictNormalHom M

@[simp]
theorem _root_.AlgHom.restrictNormalHom_commutes (f : M →ₐ[F] K) [Normal F M] (σ : Gal(K/F))
    (x : M) : f (f.restrictNormalHom σ x) = σ (f x) :=
  letI := f.toRingHom.toAlgebra
  haveI : IsScalarTower F M K := IsScalarTower.of_algebraMap_eq fun x ↦ (f.commutes x).symm
  AlgEquiv.restrictNormal_commutes σ M x

/-- `f.restrictNormalHom σ` is the unique automorphism of `M` intertwined with `σ` by `f`. -/
theorem _root_.AlgHom.restrictNormalHom_eq_iff (f : M →ₐ[F] K) [Normal F M] {σ : Gal(K/F)}
    {τ : Gal(M/F)} : f.restrictNormalHom σ = τ ↔ ∀ x, σ (f x) = f (τ x) := by
  refine ⟨fun h x ↦ by rw [← h, AlgHom.restrictNormalHom_commutes], fun h ↦ ?_⟩
  ext x
  exact f.injective ((f.restrictNormalHom_commutes σ x).trans (h x))

/-- For the algebra map of a scalar tower, restriction along it is Mathlib's
`AlgEquiv.restrictNormalHom`. -/
@[simp]
theorem _root_.AlgHom.restrictNormalHom_toAlgHom [Algebra M K] [IsScalarTower F M K]
    [Normal F M] :
    (IsScalarTower.toAlgHom F M K).restrictNormalHom = AlgEquiv.restrictNormalHom M :=
  MonoidHom.ext fun σ ↦ (IsScalarTower.toAlgHom F M K).restrictNormalHom_eq_iff.2
    fun y ↦ (AlgEquiv.restrictNormal_commutes σ M y).symm

/-- For a normal `K/F`, every automorphism of `M/F` is the restriction of one of `K/F`. -/
theorem _root_.AlgHom.restrictNormalHom_surjective (f : M →ₐ[F] K) [Normal F M] [Normal F K] :
    Function.Surjective f.restrictNormalHom :=
  letI := f.toRingHom.toAlgebra
  haveI : IsScalarTower F M K := IsScalarTower.of_algebraMap_eq fun x ↦ (f.commutes x).symm
  AlgEquiv.restrictNormalHom_surjective K

/-- The kernel of restriction along `f` is the subgroup fixing the image of `f` pointwise. -/
theorem _root_.AlgHom.ker_restrictNormalHom (f : M →ₐ[F] K) [Normal F M] :
    f.restrictNormalHom.ker = f.fieldRange.fixingSubgroup := by
  ext σ
  simp [f.restrictNormalHom_eq_iff]

/-- **The fixing subgroup of a normal intermediate field is normal**, being the kernel of
restriction. Neither separability nor normality of the ambient extension `K/F` is used. -/
instance _root_.IntermediateField.fixingSubgroup_normal (L : IntermediateField F K) [Normal F L] :
    L.fixingSubgroup.Normal :=
  L.restrictNormalHom_ker (K := F) (L := K) ▸ (AlgEquiv.restrictNormalHom L).normal_ker

/-- Restriction along the inclusion of an intermediate field is Mathlib's
`AlgEquiv.restrictNormalHom`. -/
@[simp]
theorem _root_.IntermediateField.restrictNormalHom_val (L : IntermediateField F K) [Normal F L] :
    L.val.restrictNormalHom = AlgEquiv.restrictNormalHom L :=
  MonoidHom.ext fun σ ↦ L.val.restrictNormalHom_eq_iff.2 fun x ↦
    (AlgEquiv.restrictNormal_commutes σ L x).symm

/-- Including the units of a normal intermediate field `L` into `Kˣ` intertwines the action of
`Gal(L/F)` on `Lˣ`, through restriction, with the action of `Gal(K/F)` on `Kˣ`. -/
theorem _root_.IntermediateField.units_map_val_restrictNormalHom (L : IntermediateField F K)
    [Normal F L] (σ : Gal(K/F)) (u : Lˣ) :
    Units.map L.val.toRingHom.toMonoidHom (Units.map (AlgEquiv.restrictNormalHom L σ) u) =
      σ • Units.map L.val.toRingHom.toMonoidHom u := by
  rw [AlgEquiv.smul_units_def]
  exact Units.ext (AlgEquiv.restrictNormal_commutes σ L u)

/-- **Restriction along a twisted embedding is conjugate**: precomposing `f` with an automorphism
`τ` of `M/F` conjugates restriction along `f` by `τ`. -/
theorem _root_.AlgHom.restrictNormalHom_comp (f : M →ₐ[F] K) [Normal F M] (τ : Gal(M/F))
    (σ : Gal(K/F)) :
    (f.comp (τ : M →ₐ[F] M)).restrictNormalHom σ = τ⁻¹ * f.restrictNormalHom σ * τ := by
  rw [AlgHom.restrictNormalHom_eq_iff]
  intro x
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgHom.comp_apply,
    AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply,
    AlgHom.restrictNormalHom_commutes]

/-- **Restriction is transitive along composed embeddings**: restricting `σ` along `f : M → K`
and then along `h : N → M` is restricting `σ` along `f ∘ h`. -/
@[simp]
theorem _root_.AlgHom.restrictNormalHom_restrictNormalHom {N : Type*} [Field N] [Algebra F N]
    (f : M →ₐ[F] K) (h : N →ₐ[F] M) [Normal F M] [Normal F N] (σ : Gal(K/F)) :
    h.restrictNormalHom (f.restrictNormalHom σ) = (f.comp h).restrictNormalHom σ :=
  ((f.comp h).restrictNormalHom_eq_iff.2 fun x ↦ by
    rw [AlgHom.comp_apply, AlgHom.comp_apply, h.restrictNormalHom_commutes,
      f.restrictNormalHom_commutes]).symm

/-- **The normal closure of a normal extension is its image**: every `F`-embedding of a normal
extension `M/F` into `K` has image the normal closure of `M` in `K`, so all of them have the
same image. -/
theorem _root_.IntermediateField.normalClosure_eq_fieldRange (f : M →ₐ[F] K)
    [Normal F M] : IntermediateField.normalClosure F M K = f.fieldRange := by
  refine le_antisymm (iSup_le fun g y hy ↦ ?_) f.fieldRange_le_normalClosure
  -- `g` factors through the image of `f`, whose `F`-embeddings into `K` all have that image.
  obtain ⟨x, rfl⟩ := AlgHom.mem_fieldRange.1 hy
  rw [← (g.comp f.equivFieldRange.symm.toAlgHom).fieldRange_of_normal]
  exact ⟨f.equivFieldRange x, by simp⟩

/-- **Two embeddings of a normal extension differ by an automorphism**: for `F`-embeddings
`f g : M →ₐ[F] K` of a normal extension `M/F`, there is `τ ∈ Gal(M/F)` with `g = f ∘ τ`. -/
theorem _root_.AlgHom.exists_comp_eq_of_normal (f g : M →ₐ[F] K) [Normal F M] :
    ∃ τ : Gal(M/F), f.comp (τ : M →ₐ[F] M) = g := by
  have h : g.fieldRange = f.fieldRange := by
    rw [← IntermediateField.normalClosure_eq_fieldRange,
      ← IntermediateField.normalClosure_eq_fieldRange]
  refine ⟨g.equivFieldRange.trans
    ((IntermediateField.equivOfEq h).trans f.equivFieldRange.symm), ?_⟩
  ext x
  rw [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.trans_apply, AlgEquiv.trans_apply,
    ← AlgHom.equivFieldRange_apply_coe, AlgEquiv.apply_symm_apply,
    IntermediateField.equivOfEq_apply, AlgHom.equivFieldRange_apply_coe]

/-- Restriction of automorphisms of `M/F` to a normal intermediate field `N` of `K` lying in the
image of an embedding `f : M →ₐ[F] K`. Through `f`, the field `N` is a
subextension of `M`, and `f.restrictNormalHomOfLE h σ` is the automorphism of `N` induced by `σ`:
it sends `f x` to `f (σ x)` (`AlgHom.coe_restrictNormalHomOfLE_apply`). -/
noncomputable def _root_.AlgHom.restrictNormalHomOfLE (f : M →ₐ[F] K)
    {N : IntermediateField F K} [Normal F N] (h : N ≤ f.fieldRange) : Gal(M/F) →* Gal(N/F) :=
  ((f.equivFieldRange.symm : f.fieldRange →ₐ[F] M).comp
    (IntermediateField.inclusion h)).restrictNormalHom

/-- `f.restrictNormalHomOfLE h σ` sends `f x` to `f (σ x)`. -/
theorem _root_.AlgHom.coe_restrictNormalHomOfLE_apply (f : M →ₐ[F] K)
    {N : IntermediateField F K} [Normal F N] (h : N ≤ f.fieldRange) (σ : Gal(M/F)) {x : M}
    {y : N} (hxy : f x = y) : (f.restrictNormalHomOfLE h σ y : K) = f (σ x) := by
  set g := (f.equivFieldRange.symm : f.fieldRange →ₐ[F] M).comp (IntermediateField.inclusion h)
  -- `g` is the inverse of `f` on `N`.
  have hg (z : N) : f (g z) = z := by
    simpa [g] using (AlgHom.equivFieldRange_apply_coe f
      (f.equivFieldRange.symm (IntermediateField.inclusion h z))).symm
  have hgy : g y = x := f.injective ((hg y).trans hxy.symm)
  rw [← hg, AlgHom.restrictNormalHomOfLE, AlgHom.restrictNormalHom_commutes, hgy]

/-- Restriction to a normal intermediate field in the image of `f` is surjective. -/
theorem _root_.AlgHom.restrictNormalHomOfLE_surjective (f : M →ₐ[F] K) [Normal F M]
    {N : IntermediateField F K} [Normal F N] (h : N ≤ f.fieldRange) :
    Function.Surjective (f.restrictNormalHomOfLE h) :=
  AlgHom.restrictNormalHom_surjective _

end RestrictAlong

/-! ### The fixing subgroup of an intermediate extension -/

section EmbeddingSubgroup

variable (K L M : Type*) [Field K] [Field L] [Field M]
  [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]

/-- The subgroup `H = Gal(M/L)` of `G = Gal(M/K)` fixing the image of `L` inside `M`. -/
noncomputable def embeddingSubgroup : Subgroup (M ≃ₐ[K] M) :=
  (IsScalarTower.toAlgHom K L M).fieldRange.fixingSubgroup

/-- Defining formula for `embeddingSubgroup` as the fixing subgroup of the image of `L` in `M`. -/
theorem embeddingSubgroup_def :
    embeddingSubgroup K L M = (IsScalarTower.toAlgHom K L M).fieldRange.fixingSubgroup := (rfl)

variable {K L M} in
/-- An automorphism `σ : M ≃ₐ[K] M` belongs to `embeddingSubgroup K L M` iff it fixes every
element in the image of `L`. -/
@[simp]
theorem mem_embeddingSubgroup_iff {σ : M ≃ₐ[K] M} :
    σ ∈ embeddingSubgroup K L M ↔ ∀ x : L, σ (algebraMap L M x) = algebraMap L M x := by
  rw [embeddingSubgroup_def, IntermediateField.mem_fixingSubgroup_iff]
  exact ⟨fun h x ↦ h _ ⟨x, rfl⟩, fun h _ ⟨x, hx⟩ ↦ hx ▸ h x⟩

/-- `embeddingSubgroup K L M` is the image of
`AlgEquiv.restrictScalarsHom K : Gal(M/L) →* Gal(M/K)`. No normality or finiteness is needed. -/
theorem range_restrictScalarsHom_eq_embeddingSubgroup :
    (AlgEquiv.restrictScalarsHom (S := L) K : (M ≃ₐ[L] M) →* (M ≃ₐ[K] M)).range =
      embeddingSubgroup K L M := by
  ext σ; rw [MonoidHom.mem_range, mem_embeddingSubgroup_iff]
  exact ⟨fun ⟨τ, h⟩ x ↦ h ▸ τ.commutes x, fun h ↦ ⟨{ σ with commutes' := h }, rfl⟩⟩

/-- For `L = M`, the fixing subgroup of `M` in `Gal(M/K)` is trivial. -/
@[simp]
theorem embeddingSubgroup_self : embeddingSubgroup K M M = ⊥ := by ext; simp [AlgEquiv.ext_iff]

/-- For `L = K`, every `K`-automorphism of `M` fixes the image of `K`. -/
@[simp]
theorem embeddingSubgroup_base : embeddingSubgroup K K M = ⊤ := by ext; simp

/-- For an intermediate field `E : IntermediateField K M`, `embeddingSubgroup K E M` is
`E.fixingSubgroup`. -/
@[simp]
theorem embeddingSubgroup_intermediateField (E : IntermediateField K M) :
    embeddingSubgroup K E M = E.fixingSubgroup := by
  ext σ; rw [mem_embeddingSubgroup_iff, IntermediateField.mem_fixingSubgroup_iff]
  exact ⟨fun h x hx ↦ h ⟨x, hx⟩, fun h x ↦ h x.val x.property⟩

/-- In a Galois extension `M/K`, the fixed field of `embeddingSubgroup K L M` is the image
of `L` in `M`. -/
@[simp]
theorem fixedField_embeddingSubgroup [IsGalois K M] :
    IntermediateField.fixedField (embeddingSubgroup K L M) =
      (IsScalarTower.toAlgHom K L M).fieldRange := by
  rw [embeddingSubgroup_def, InfiniteGalois.fixedField_fixingSubgroup]

/-- In a tower `M / L / E / K`, the fixing subgroup of `L` is contained in that of `E`. -/
theorem embeddingSubgroup_antitone (E : Type*) [Field E] [Algebra K E] [Algebra E L]
    [Algebra E M] [IsScalarTower K E M] [IsScalarTower E L M] :
    embeddingSubgroup K L M ≤ embeddingSubgroup K E M := fun _ hσ ↦
  mem_embeddingSubgroup_iff.2 fun x ↦ by
    rw [IsScalarTower.algebraMap_apply E L M]; exact mem_embeddingSubgroup_iff.1 hσ _

/-- In a Galois extension `M/K` containing `L`, the order of `embeddingSubgroup K L M`
equals `[M : L]`. When `M/L` is infinite, both sides are `0`. -/
theorem natCard_embeddingSubgroup [IsGalois K M] :
    Nat.card (embeddingSubgroup K L M) = Module.finrank L M := by
  have := IsGalois.tower_top_of_isGalois K L M
  rw [← range_restrictScalarsHom_eq_embeddingSubgroup K L M, ← Subgroup.map_top,
    Subgroup.card_map_of_injective (AlgEquiv.restrictScalarsHom_injective K),
    ← Subgroup.finrank_fixedField_eq_card (⊤ : Subgroup (M ≃ₐ[L] M)),
    InfiniteGalois.fixedField_bot, IntermediateField.finrank_bot']

/-- In a Galois extension `M/K` containing `L`, the index of `embeddingSubgroup K L M` in
`Gal(M/K)` equals `[L : K]`. -/
@[simp]
theorem index_embeddingSubgroup [IsGalois K M] :
    (embeddingSubgroup K L M).index = Module.finrank K L := by
  rw [embeddingSubgroup_def, ← IntermediateField.finrank_eq_fixingSubgroup_index,
    ← (IsScalarTower.toAlgHom K L M).equivFieldRange.toLinearEquiv.finrank_eq]

/-- In a tower `M' / M / L / K` with `M/K` normal, pulling `embeddingSubgroup K L M` back along
restriction `Gal(M'/K) →* Gal(M/K)` recovers `embeddingSubgroup K L M'`. -/
theorem comap_restrictNormalHom_embeddingSubgroup (M' : Type*) [Field M']
    [Algebra K M'] [Algebra L M'] [Algebra M M']
    [IsScalarTower K M M'] [IsScalarTower L M M'] [IsScalarTower K L M'] [Normal K M] :
    (embeddingSubgroup K L M).comap
        (AlgEquiv.restrictNormalHom M : (M' ≃ₐ[K] M') →* (M ≃ₐ[K] M)) =
      embeddingSubgroup K L M' := by
  rw [embeddingSubgroup_def, embeddingSubgroup_def, ← IntermediateField.map_fixingSubgroup M',
    AlgHom.map_fieldRange]
  congr 2
  exact AlgHom.ext fun x ↦ (IsScalarTower.algebraMap_apply L M M' x).symm

/-- Transport of `embeddingSubgroup` along an `L`-algebra equivalence `e : M ≃ₐ[L] M'`. -/
theorem map_autCongr_embeddingSubgroup {M' : Type*} [Field M'] [Algebra K M'] [Algebra L M']
    [IsScalarTower K L M'] (e : M ≃ₐ[L] M') :
    (embeddingSubgroup K L M).map ((e.restrictScalars K).autCongr :
        (M ≃ₐ[K] M) →* (M' ≃ₐ[K] M')) = embeddingSubgroup K L M' := by
  have hcomp : ((e.restrictScalars K : M ≃ₐ[K] M').toAlgHom).comp (IsScalarTower.toAlgHom K L M) =
      IsScalarTower.toAlgHom K L M' := AlgHom.ext fun x ↦ e.commutes x
  ext σ'
  rw [← MulEquiv.toMonoidHom_eq_coe, Subgroup.mem_map_equiv, embeddingSubgroup_def,
    embeddingSubgroup_def, AlgEquiv.autCongr_symm, AlgEquiv.autCongr_mem_fixingSubgroup_iff,
    AlgEquiv.symm_symm, AlgHom.map_fieldRange, hcomp]

/-- For a normal subextension `L / K` inside `M / K`, `embeddingSubgroup K L M` is normal. -/
instance embeddingSubgroup_normal [Normal K L] : (embeddingSubgroup K L M).Normal :=
  (IsScalarTower.toAlgHom K L M).fieldRange.fixingSubgroup_normal

/-- Restriction of scalars identifies `Gal(M/L)` with `embeddingSubgroup K L M`. -/
noncomputable def algEquivEquivEmbeddingSubgroup : (M ≃ₐ[L] M) ≃* embeddingSubgroup K L M :=
  (MonoidHom.ofInjective (AlgEquiv.restrictScalarsHom_injective K)).trans
    (MulEquiv.subgroupCongr (range_restrictScalarsHom_eq_embeddingSubgroup K L M))

/-- `algEquivEquivEmbeddingSubgroup` acts on `M` as `AlgEquiv.restrictScalars`. -/
@[simp]
theorem coe_algEquivEquivEmbeddingSubgroup_apply (σ : M ≃ₐ[L] M) :
    ((algEquivEquivEmbeddingSubgroup K L M σ : M ≃ₐ[K] M)) = σ.restrictScalars K := by
  simp [algEquivEquivEmbeddingSubgroup, MonoidHom.ofInjective_apply]

/-- In a Galois extension `M / K` containing `L`, `L` is `K`-isomorphic to the fixed field of
`embeddingSubgroup K L M`. -/
noncomputable def equivFixedFieldEmbeddingSubgroup [IsGalois K M] :
    L ≃ₐ[K] IntermediateField.fixedField (embeddingSubgroup K L M) :=
  (IsScalarTower.toAlgHom K L M).equivFieldRange.trans
    (IntermediateField.equivOfEq (fixedField_embeddingSubgroup K L M).symm)

/-- The equivalence `equivFixedFieldEmbeddingSubgroup K L M` preserves coercion into `M`. -/
@[simp]
theorem coe_equivFixedFieldEmbeddingSubgroup_apply [IsGalois K M] (x : L) :
    ((equivFixedFieldEmbeddingSubgroup K L M x :
      IntermediateField.fixedField (embeddingSubgroup K L M)) : M) = algebraMap L M x := by
  simp [equivFixedFieldEmbeddingSubgroup]

/-- Restricting `Gal(M/K)` to a normal intermediate field `L` and conjugating along
`equivFixedFieldEmbeddingSubgroup K L M` equals quotienting by `embeddingSubgroup K L M` followed
by `IsGalois.normalAutEquivQuotient`. -/
theorem autCongr_equivFixedFieldEmbeddingSubgroup_comp_restrictNormalHom
    [Normal K L] [IsGalois K M] [FiniteDimensional K M] :
    MonoidHom.comp (MonoidHom.ofClass (equivFixedFieldEmbeddingSubgroup K L M).autCongr)
        (AlgEquiv.restrictNormalHom L) =
      MonoidHom.comp (MonoidHom.ofClass (IsGalois.normalAutEquivQuotient
          (embeddingSubgroup K L M)))
        (QuotientGroup.mk' (embeddingSubgroup K L M)) := by
  ext σ y
  have heK : algebraMap L M ((equivFixedFieldEmbeddingSubgroup K L M).symm y) = y := by
    rw [← coe_equivFixedFieldEmbeddingSubgroup_apply K L M,
      (equivFixedFieldEmbeddingSubgroup K L M).apply_symm_apply]
  change ((equivFixedFieldEmbeddingSubgroup K L M)
    ((AlgEquiv.restrictNormalHom L σ) ((equivFixedFieldEmbeddingSubgroup K L M).symm y)) : M) =
    (IsGalois.normalAutEquivQuotient (embeddingSubgroup K L M)
      (QuotientGroup.mk' (embeddingSubgroup K L M) σ) y : M)
  rw [coe_equivFixedFieldEmbeddingSubgroup_apply,
    show AlgEquiv.restrictNormalHom L σ = σ.restrictNormal L from rfl,
    AlgEquiv.restrictNormal_commutes, heK, QuotientGroup.coe_mk',
    IsGalois.normalAutEquivQuotient_apply]
  exact (σ.restrictNormal_commutes (IntermediateField.fixedField (embeddingSubgroup K L M)) y).symm

/-- In a tower `K ⊆ L ⊆ M` with `M / K` Galois and `L / K` normal, `L / K` is Galois. -/
theorem _root_.IsGalois.tower_bot_of_normal [IsGalois K M] [Normal K L] : IsGalois K L :=
  have := Algebra.isSeparable_tower_bot_of_isSeparable K L M
  ⟨⟩

end EmbeddingSubgroup

end TauCeti

/-! ### Restriction along compatible normal subextensions -/

section CompatibleRestriction

open IntermediateField

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
  {E M : IntermediateField K Ω} [Normal K E] [Normal K M]
  (pi : (M ≃ₐ[K] M) → (E ≃ₐ[K] E)) (iota : E → M)
  (hpiiota : ∀ g x, iota (pi g x) = g (iota x))
  (hiota : ∀ x, M.val (iota x) = E.val x)
include hpiiota hiota

/-- Along a compatible pair of maps `(pi, iota)` between normal intermediate fields of `Ω/K`, with
`iota` compatible with their inclusions into `Ω`, `pi` carries restriction to `M` to restriction to
`E`. Only the underlying functions are used: a monoid hom `pi` and an algebra hom `iota` apply
through their coercions. -/
theorem AlgEquiv.restrictNormalHom_of_compatible (g : Ω ≃ₐ[K] Ω) :
    pi (AlgEquiv.restrictNormalHom M g) = AlgEquiv.restrictNormalHom E g :=
  AlgEquiv.ext fun x ↦ E.val.injective <| (hiota _).symm.trans <|
    (congrArg M.val (hpiiota _ x)).trans <| (AlgEquiv.restrictNormal_commutes g M (iota x)).trans <|
      (congrArg g (hiota x)).trans (AlgEquiv.restrictNormal_commutes g E x).symm

end CompatibleRestriction

/-! ### Restriction to an intermediate field in a tower -/

section Tower

variable (K L : Type*) [Field K] [Field L] [Algebra K L] [Normal K L]
  (M : Type*) [Field M] [Algebra K M] [Algebra L M] [IsScalarTower K L M]

/-- **`σ` restricts to the identity on `L` exactly when it fixes `L` pointwise.** Mathlib's
`AlgEquiv.restrictNormal_eq_one_iff` says this for an `IntermediateField`, while
`AlgEquiv.restrictNormal` itself is already stated for an abstract algebra `L`, so only the
characterisation needs transporting to a tower `K ⊆ L ⊆ M`. -/
theorem AlgEquiv.restrictNormal_eq_one_iff_algebraMap (σ : M ≃ₐ[K] M) :
    σ.restrictNormal L = 1 ↔ ∀ x : L, σ (algebraMap L M x) = algebraMap L M x := by
  constructor
  · intro h x
    rw [← AlgEquiv.restrictNormal_commutes σ L x, h, AlgEquiv.one_apply]
  · intro h
    ext x
    have hx := AlgEquiv.restrictNormal_commutes σ L x
    rw [h x] at hx
    exact (algebraMap L M).injective hx

/-- Restriction as a group homomorphism agrees with restriction of an automorphism. -/
theorem AlgEquiv.restrictNormalHom_apply_eq_restrictNormal (σ : M ≃ₐ[K] M) :
    (AlgEquiv.restrictNormalHom L) σ = σ.restrictNormal L :=
  rfl

/-- An automorphism of `M/K` comes from an automorphism of `M/L` exactly when its restriction to
`L` is the identity. -/
theorem AlgEquiv.mem_range_restrictScalarsHom_iff_restrictNormal_eq_one
    (σ : M ≃ₐ[K] M) :
    σ ∈ (AlgEquiv.restrictScalarsHom (S := L) K).range ↔ σ.restrictNormal L = 1 := by
  constructor
  · rintro ⟨τ, rfl⟩
    apply (AlgEquiv.restrictNormal_eq_one_iff_algebraMap K L M _).2
    intro x
    exact τ.commutes x
  · intro h
    let τ : M ≃ₐ[L] M := AlgEquiv.ofRingEquiv (f := σ.toRingEquiv)
      ((AlgEquiv.restrictNormal_eq_one_iff_algebraMap K L M σ).1 h)
    exact ⟨τ, AlgEquiv.ext fun x ↦ by simp [τ]⟩

/-- The image of `Gal(M/L)` in `Gal(M/K)` under restriction of scalars is the kernel of
restriction to `L`. -/
theorem AlgEquiv.range_restrictScalarsHom_eq_ker_restrictNormalHom :
    (AlgEquiv.restrictScalarsHom (S := L) K).range =
      (AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L).ker := by
  ext σ
  rw [AlgEquiv.mem_range_restrictScalarsHom_iff_restrictNormal_eq_one K L M, MonoidHom.mem_ker,
    AlgEquiv.restrictNormalHom_apply_eq_restrictNormal]

/-- Multiplying by an automorphism of `M/L` does not change the restriction to `L`. -/
@[simp]
theorem AlgEquiv.restrictNormal_mul_restrictScalars (σ : M ≃ₐ[K] M) (τ : M ≃ₐ[L] M) :
    (σ * τ.restrictScalars K).restrictNormal L = σ.restrictNormal L := by
  rw [← AlgEquiv.restrictNormalHom_apply_eq_restrictNormal K L M, map_mul,
    AlgEquiv.restrictNormalHom_apply_eq_restrictNormal,
    AlgEquiv.restrictNormalHom_apply_eq_restrictNormal,
    (AlgEquiv.mem_range_restrictScalarsHom_iff_restrictNormal_eq_one K L M
      (τ.restrictScalars K)).1 ⟨τ, rfl⟩, mul_one]

omit [Normal K L] in
/-- In a finite Galois tower `K ⊆ L ⊆ M`, the image of `Gal(M/L)` in `Gal(M/K)` under restriction
of scalars has index `[L : K]`. -/
@[simp]
theorem AlgEquiv.index_range_restrictScalarsHom [FiniteDimensional K M] [IsGalois K M] :
    (AlgEquiv.restrictScalarsHom K : Gal(M/L) →* Gal(M/K)).range.index =
      Module.finrank K L := by
  have : IsGalois L M := IsGalois.tower_top_of_isGalois K L M
  have : FiniteDimensional L M := Module.Finite.right K L M
  exact TauCeti.index_eq_of_natCard_eq_mul (Module.finrank_pos (R := L) (M := M))
    (by rw [← Nat.card_congr (MonoidHom.ofInjective (AlgEquiv.restrictScalarsHom_injective K
          (S := L) (A := M))).toEquiv, IsGalois.card_aut_eq_finrank])
    (by rw [IsGalois.card_aut_eq_finrank K M, ← Module.finrank_mul_finrank K L M, mul_comm])

end Tower

/-! ### Restriction to a simple normal subextension -/

section AdjoinSimple

open IntermediateField

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/-- **`σ` restricts to the identity on `F⟮α⟯` exactly when it fixes `α`**, for a normal simple
subextension `F⟮α⟯` of `E/F`. -/
theorem AlgEquiv.restrictNormalHom_adjoin_simple_eq_one_iff {α : E} [Normal F F⟮α⟯]
    (σ : Gal(E/F)) : AlgEquiv.restrictNormalHom F⟮α⟯ σ = 1 ↔ σ α = α := by
  refine ⟨fun h ↦ ?_, fun h ↦ AlgEquiv.coe_toAlgHom_injective (adjoin_algHom_ext F fun x hx ↦ ?_)⟩
  · simpa [h] using (AlgEquiv.restrictNormalHom_apply F⟮α⟯ σ (AdjoinSimple.gen F α)).symm
  · obtain rfl := Set.mem_singleton_iff.1 hx
    exact Subtype.ext ((AlgEquiv.restrictNormalHom_apply _ σ _).trans h)

end AdjoinSimple

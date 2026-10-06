/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.Basic

/-!
# Restricting automorphisms along an embedding of a normal extension

Mathlib's `AlgEquiv.restrictNormalHom` restricts automorphisms of `K/F` to a normal subextension
`M/F` given by a scalar tower `F → M → K`. This file restricts along an arbitrary embedding
`f : M →ₐ[F] K` instead, which is convenient when `M` is an intermediate field sitting inside `K`
through a map other than the algebra map (for example an `IntermediateField.inclusion`).

In an abstract scalar tower with a normal intermediate field, restriction to the intermediate
field is the identity precisely when the automorphism fixes it pointwise; its kernel is the image
of restriction of scalars.

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
* `IntermediateField.normalClosure_eq_fieldRange` and `AlgHom.exists_comp_eq_of_normal`: the
  embeddings of a normal extension all have the same image and differ by automorphisms.
* `AlgHom.restrictNormalHom_surjective` and `AlgHom.ker_restrictNormalHom`: for a normal `K/F`
  restriction is surjective, and its kernel is the subgroup fixing the image of `f`.
* `AlgHom.normal_fieldRange`: the image of a normal extension is normal.
* `AlgHom.restrictNormalHomOfLE`: in the other direction, restriction `Gal(M/F) →* Gal(N/F)` to a
  normal intermediate field `N` of `K` lying in the image of `f`, with
  `AlgHom.coe_restrictNormalHomOfLE_apply` and `AlgHom.restrictNormalHomOfLE_surjective`.
* `AlgEquiv.restrictNormal_eq_one_iff_algebraMap`: restriction is trivial precisely when the
  automorphism fixes the intermediate field pointwise.
* `AlgEquiv.mem_range_restrictScalarsHom_iff_restrictNormal_eq_one` and
  `AlgEquiv.range_restrictScalarsHom_eq_ker_restrictNormalHom`: the restriction kernel is
  the image of restriction of scalars.
* `AlgEquiv.restrictNormal_mul_restrictScalars`: multiplying by an automorphism of the top field
  over the intermediate one does not change the restriction.
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

end TauCeti

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

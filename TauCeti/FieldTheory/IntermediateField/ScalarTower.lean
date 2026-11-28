/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Scalar-change equivalences for intermediate fields

Mathlib's `IntermediateField.isScalarTower_mid` supplies `IsScalarTower K E L` for an intermediate
field `E` of `L / K`.  The same statement holds one step further down: a semiring `k`
whose actions on `K` and on `L` form a scalar tower `k → K → L` also acts compatibly through `E`.
Conversely, restricting the scalars of an intermediate field of `L / K` to `k` does not change the
field, as a `k`-algebra.

Building on `restrictScalarsAlgEquiv`, this file also packages scalar restriction, scalar extension,
and field-range transport for intermediate fields and their algebra equivalences:

* in a tower `K → L' → L` of fields, intermediate fields of `L / L'` correspond order-isomorphically
  to intermediate fields of `L / K` containing the image of `L'`, and `L'`-algebra equivalences
  `E₁ ≃ₐ[L'] E₂` correspond to `K`-algebra equivalences `E₁.restrictScalars K ≃ₐ[K]
  E₂.restrictScalars K` fixing the image of `L'` pointwise;
* `U`-algebra equivalences `extendScalars h₁ ≃ₐ[U] extendScalars h₂` over an intermediate field
  `U` of `Ω / K` correspond to `K`-algebra equivalences `L₁ ≃ₐ[K] L₂` fixing `U` pointwise;
* for a scalar tower `K → F → Ω` of fields whose middle step has image `U` in `Ω`, intermediate
  fields of `Ω / F` and their `F`-algebra equivalences correspond to intermediate fields of `Ω / U`
  and their `U`-algebra equivalences.

## Main definitions

* `IntermediateField.restrictScalarsAlgEquiv`: an intermediate field `E` of `L / L'` and its
  restriction of scalars `E.restrictScalars K` are `K`-isomorphic.
* `IntermediateField.restrictScalarsOrderIso`: order isomorphism between `IntermediateField L' L`
  and `{E : IntermediateField K L // ∀ x : L', algebraMap L' L x ∈ E}`.
* `IntermediateField.restrictScalarsAlgEquivEquiv`: `L'`-algebra equivalences `E₁ ≃ₐ[L'] E₂`
  correspond to `K`-algebra equivalences `E₁.restrictScalars K ≃ₐ[K] E₂.restrictScalars K` fixing
  the image of `L'` pointwise.
* `IntermediateField.extendScalarsAlgEquivEquiv`: `U`-algebra equivalences `extendScalars h₁ ≃ₐ[U]
  extendScalars h₂` correspond to `K`-algebra equivalences `L₁ ≃ₐ[K] L₂` fixing `U` pointwise.
* `IntermediateField.extendScalarsAlgEquivHom`: the injective homomorphism
  `(extendScalars h ≃ₐ[U] extendScalars h) →* (L ≃ₐ[K] L)`.
* `IntermediateField.orderIsoOfFieldRangeEq`: order isomorphism
  `IntermediateField F Ω ≃o IntermediateField U Ω` when
  `(IsScalarTower.toAlgHom K F Ω).fieldRange = U`.
* `IntermediateField.algEquivEquivOfFieldRangeEq`: equivalence `(E₁ ≃ₐ[F] E₂) ≃
  (orderIsoOfFieldRangeEq hU E₁ ≃ₐ[U] orderIsoOfFieldRangeEq hU E₂)`.

## Main results

* `IntermediateField.instIsScalarTower`: `IsScalarTower k E L` for an intermediate field
  `E` of `L / K` and a semiring `k` acting compatibly on `K` and `L`.
* `IntermediateField.pow_eq_algebraMap_iff`: an element `x` of `E` satisfies
  `x ^ n = algebraMap R E r` if and only if `(x : L) ^ n = algebraMap R L r`.
* `IntermediateField.le_of_isScalarTower`: an intermediate field `E` lies in an intermediate
  field `E'` as soon as some algebra structure of `E'` over `E` is compatible with `L`.
* `IntermediateField.restrictScalars_self`: restricting the scalars of an intermediate field of
  `L / K` to `K` itself is the identity.
* `IntermediateField.mem_bot_iff_mem`: for an intermediate field `F` of `L / K`, an element of
  `L` lies in the bottom intermediate field of `L / F` if and only if it lies in `F`.
* `IntermediateField.finrank_restrictScalars_eq`: restricting the scalars of an intermediate
  field `E` of `L / L'` to `K` does not change the degree of `L` over it.
* `IntermediateField.nonempty_extendScalars_algEquiv_iff`: `extendScalars h₁` and
  `extendScalars h₂` are `U`-isomorphic precisely when some `L₁ ≃ₐ[K] L₂` fixes `U` pointwise.
* `IntermediateField.extendScalarsAlgEquivHom_injective` and
  `IntermediateField.mem_range_extendScalarsAlgEquivHom_iff`: `extendScalarsAlgEquivHom h` is
  injective with range the `K`-automorphisms of `L` fixing `U` pointwise.
* `IntermediateField.le_restrictScalars_of_fieldRange_eq`,
  `IntermediateField.orderIsoOfFieldRangeEq_apply`,
  `IntermediateField.mem_orderIsoOfFieldRangeEq`,
  `IntermediateField.mem_orderIsoOfFieldRangeEq_symm`,
  `IntermediateField.restrictScalars_orderIsoOfFieldRangeEq`,
  `IntermediateField.restrictScalars_orderIsoOfFieldRangeEq_symm`,
  `IntermediateField.coe_algEquivEquivOfFieldRangeEq_apply`, and
  `IntermediateField.coe_algEquivEquivOfFieldRangeEq_symm_apply`: inclusion, explicit formula via
  `extendScalars`, membership and `restrictScalars` compatibility in both directions, and evaluation
  of `algEquivEquivOfFieldRangeEq` and its inverse.
-/

public section

namespace IntermediateField

/-- Mathlib's `IntermediateField.isScalarTower_mid` supplies `IsScalarTower K E L` for an
intermediate field `E` of `L / K`; this is the same statement for a semiring `k` that acts on `K`
compatibly with its module structure on `L`, which is what an object of `L` defined over `k` needs
in order to be restricted to `E`. -/
instance instIsScalarTower {k K L : Type*} [Semiring k] [Field K] [Field L]
    [SMul k K] [Module k L] [Algebra K L] [IsScalarTower k K L]
    (E : IntermediateField K L) : IsScalarTower k E L :=
  IsScalarTower.to₁₃₄ k K E L

/-- An element `x` of an intermediate field `E` of `L / K` has `n`-th power `algebraMap R E r` in
`E` if and only if `(x : L)` has `n`-th power `algebraMap R L r` in `L`. -/
theorem pow_eq_algebraMap_iff {R K L : Type*} [CommSemiring R] [Field K] [Field L]
    [Algebra R K] [Algebra R L] [Algebra K L] [IsScalarTower R K L]
    {E : IntermediateField K L} {x : E} {n : ℕ} {r : R} :
    x ^ n = algebraMap R E r ↔ (x : L) ^ n = algebraMap R L r := by
  rw [← (algebraMap E L).injective.eq_iff, map_pow, algebraMap_apply,
    ← IsScalarTower.algebraMap_apply R E L]

/-- If `E'` is an algebra over `E` compatibly with their inclusions in `L`, then `E ≤ E'`: every
`x ∈ E` is the image in `L` of `algebraMap E E' x ∈ E'`. -/
theorem le_of_isScalarTower {K L : Type*} [Field K] [Field L] [Algebra K L]
    {E E' : IntermediateField K L} [Algebra E E'] [IsScalarTower E E' L] : E ≤ E' := fun x hx ↦ by
  have h := (algebraMap E E' ⟨x, hx⟩).property
  rwa [← algebraMap_apply, ← IsScalarTower.algebraMap_apply] at h

section RestrictScalars

/-- Restricting the scalars of an intermediate field of `L / K` from `K` to `K` itself is the
identity. -/
@[simp]
theorem restrictScalars_self {K L : Type*} [Field K] [Field L] [Algebra K L]
    (E : IntermediateField K L) : E.restrictScalars K = E :=
  SetLike.coe_injective (coe_restrictScalars (K := K))

/-- For an intermediate field `F` of `L / K`, an element of `L` lies in the bottom intermediate
field of `L / F` exactly when it lies in `F`. This is the membership form of Mathlib's
`IntermediateField.restrictScalars_bot_eq_self`. -/
@[simp]
theorem mem_bot_iff_mem {K L : Type*} [Field K] [Field L] [Algebra K L]
    {F : IntermediateField K L} {x : L} : x ∈ (⊥ : IntermediateField F L) ↔ x ∈ F := by
  rw [← mem_restrictScalars K, restrictScalars_bot_eq_self]

/-- Restricting the scalars of an intermediate field `E` of `L / L'` to `K` does not change the
degree of `L` over it: `[L : E.restrictScalars K] = [L : E]`. -/
@[simp]
theorem finrank_restrictScalars_eq {K L' L : Type*} [Field K] [Field L'] [Field L]
    [Algebra K L'] [Algebra K L] [Algebra L' L] [IsScalarTower K L' L]
    (E : IntermediateField L' L) :
    Module.finrank (E.restrictScalars K) L = Module.finrank E L :=
  rfl

variable (K : Type*) {L' L : Type*} [Field K] [Field L'] [Field L] [Algebra K L'] [Algebra K L]
  [Algebra L' L] [IsScalarTower K L' L]

/-- An intermediate field `E` of `L / L'` and its restriction of scalars `E.restrictScalars K`
have the same carrier; this is the resulting `K`-algebra equivalence between them, where `E` is a
`K`-algebra through `L'`. It lets a statement about `E` over `K` be read on the intermediate field
`E.restrictScalars K` of `L / K`, and conversely. -/
def restrictScalarsAlgEquiv (E : IntermediateField L' L) : E.restrictScalars K ≃ₐ[K] E where
  toFun x := ⟨x, x.property⟩
  invFun x := ⟨x, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

@[simp]
theorem coe_restrictScalarsAlgEquiv_apply (E : IntermediateField L' L) (x : E.restrictScalars K) :
    (restrictScalarsAlgEquiv K E x : L) = x :=
  (rfl)

@[simp]
theorem coe_restrictScalarsAlgEquiv_symm_apply (E : IntermediateField L' L) (x : E) :
    ((restrictScalarsAlgEquiv K E).symm x : L) = x :=
  (rfl)

/-- Restricting scalars from `L'` to `K` in a tower `K → L' → L` identifies the intermediate fields
of `L / L'` order-isomorphically with the intermediate fields of `L / K` containing the image of
`L'`. -/
def restrictScalarsOrderIso :
    IntermediateField L' L ≃o
      {E : IntermediateField K L // ∀ x : L', algebraMap L' L x ∈ E} where
  toFun E := ⟨E.restrictScalars K, E.algebraMap_mem⟩
  invFun E := E.val.toSubfield.toIntermediateField E.property
  left_inv E := by
    ext x
    simp [← SetLike.mem_coe]
  right_inv E := by
    ext x
    simp [← SetLike.mem_coe]
  map_rel_iff' {E₁ E₂} :=
    Subtype.mk_le_mk.trans
      ⟨fun h _ hx ↦ (mem_restrictScalars K).1 (h ((mem_restrictScalars K).2 hx)),
       fun h _ hx ↦ (mem_restrictScalars K).2 (h ((mem_restrictScalars K).1 hx))⟩

@[simp]
theorem coe_restrictScalarsOrderIso_apply (E : IntermediateField L' L) :
    ((restrictScalarsOrderIso K E :
      {E : IntermediateField K L // ∀ x : L', algebraMap L' L x ∈ E}) :
        IntermediateField K L) = E.restrictScalars K :=
  (rfl)

@[simp]
theorem restrictScalars_restrictScalarsOrderIso_symm
    (E : {E : IntermediateField K L // ∀ x : L', algebraMap L' L x ∈ E}) :
    ((restrictScalarsOrderIso K).symm E).restrictScalars K = E.val := by
  rw [← coe_restrictScalarsOrderIso_apply K ((restrictScalarsOrderIso K).symm E),
    OrderIso.apply_symm_apply]

@[simp]
theorem mem_restrictScalarsOrderIso_symm
    (E : {E : IntermediateField K L // ∀ x : L', algebraMap L' L x ∈ E}) {x : L} :
    x ∈ (restrictScalarsOrderIso K).symm E ↔ x ∈ E.val := by
  rw [← mem_restrictScalars K, restrictScalars_restrictScalarsOrderIso_symm]

/-- In a tower `K → L' → L` of fields, `L'`-algebra equivalences `E₁ ≃ₐ[L'] E₂` between intermediate
fields of `L / L'` correspond to `K`-algebra equivalences between `E₁.restrictScalars K` and
`E₂.restrictScalars K` fixing the image of `L'` pointwise. -/
def restrictScalarsAlgEquivEquiv (E₁ E₂ : IntermediateField L' L) :
    (E₁ ≃ₐ[L'] E₂) ≃
      {e : E₁.restrictScalars K ≃ₐ[K] E₂.restrictScalars K //
        ∀ x : L', (e ⟨algebraMap L' L x, E₁.algebraMap_mem x⟩ : L) = algebraMap L' L x} where
  toFun f :=
    ⟨(restrictScalarsAlgEquiv K E₁).trans
        ((f.restrictScalars K).trans (restrictScalarsAlgEquiv K E₂).symm),
     fun x ↦ congrArg Subtype.val (f.commutes x)⟩
  invFun e := AlgEquiv.ofRingEquiv
    (f := ((restrictScalarsAlgEquiv K E₁).symm.trans
      (e.val.trans (restrictScalarsAlgEquiv K E₂))).toRingEquiv)
    fun x ↦ Subtype.ext (e.property x)
  left_inv f := AlgEquiv.ext fun z ↦ Subtype.ext (by simp)
  right_inv e := Subtype.ext <| AlgEquiv.ext fun z ↦ Subtype.ext (by simp)

@[simp]
theorem coe_restrictScalarsAlgEquivEquiv_apply (E₁ E₂ : IntermediateField L' L)
    (f : E₁ ≃ₐ[L'] E₂) (x : E₁.restrictScalars K) :
    ((restrictScalarsAlgEquivEquiv K E₁ E₂ f).val x : L) = f ⟨x.val, x.property⟩ := by
  simp only [restrictScalarsAlgEquivEquiv, Equiv.coe_fn_mk, AlgEquiv.trans_apply,
    AlgEquiv.restrictScalars_apply, coe_restrictScalarsAlgEquiv_symm_apply]
  exact congrArg (fun z : E₁ ↦ (f z : L))
    (Subtype.ext (coe_restrictScalarsAlgEquiv_apply K E₁ x))

@[simp]
theorem coe_restrictScalarsAlgEquivEquiv_symm_apply (E₁ E₂ : IntermediateField L' L)
    (e : {e : E₁.restrictScalars K ≃ₐ[K] E₂.restrictScalars K //
      ∀ x : L', (e ⟨algebraMap L' L x, E₁.algebraMap_mem x⟩ : L) = algebraMap L' L x})
    (x : E₁) :
    ((restrictScalarsAlgEquivEquiv K E₁ E₂).symm e x : L) = e.val ⟨x.val, x.property⟩ := by
  simp only [restrictScalarsAlgEquivEquiv, Equiv.coe_fn_symm_mk, AlgEquiv.ofRingEquiv_apply,
    AlgEquiv.coe_toRingEquiv, AlgEquiv.trans_apply, coe_restrictScalarsAlgEquiv_apply]
  exact congrArg (fun z : E₁.restrictScalars K ↦ (e.val z : L))
    (Subtype.ext (coe_restrictScalarsAlgEquiv_symm_apply K E₁ x))

end RestrictScalars

section ExtendScalars

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] {U L L₁ L₂ : IntermediateField K Ω}

/-- An algebra equivalence `extendScalars h₁ ≃ₐ[U] extendScalars h₂` over an intermediate field
`U` is the same data as a `K`-algebra equivalence `L₁ ≃ₐ[K] L₂` fixing `U` pointwise. -/
def extendScalarsAlgEquivEquiv (h₁ : U ≤ L₁) (h₂ : U ≤ L₂) :
    (extendScalars h₁ ≃ₐ[U] extendScalars h₂) ≃
      {e : L₁ ≃ₐ[K] L₂ // ∀ x : U, (e ⟨x.val, h₁ x.property⟩ : Ω) = x} :=
  (restrictScalarsAlgEquivEquiv K (extendScalars h₁) (extendScalars h₂)).trans <|
    Equiv.subtypeEquiv
      ((equivOfEq (extendScalars_restrictScalars h₁)).equivCongr
        (equivOfEq (extendScalars_restrictScalars h₂)))
      fun _ ↦ by simp [AlgEquiv.equivCongr, -extendScalars_restrictScalars]

@[simp]
theorem coe_extendScalarsAlgEquivEquiv_apply (h₁ : U ≤ L₁) (h₂ : U ≤ L₂)
    (f : extendScalars h₁ ≃ₐ[U] extendScalars h₂) (x : L₁) :
    ((extendScalarsAlgEquivEquiv h₁ h₂ f).val x : Ω) = f ⟨x.val, x.property⟩ := by
  rw [extendScalarsAlgEquivEquiv, Equiv.trans_apply, Equiv.subtypeEquiv_apply]
  simp only [AlgEquiv.equivCongr, Equiv.coe_fn_mk, AlgEquiv.trans_apply, equivOfEq_symm,
    equivOfEq_apply]
  exact coe_restrictScalarsAlgEquivEquiv_apply K (extendScalars h₁) (extendScalars h₂) f
    ⟨x.val, x.property⟩

@[simp]
theorem coe_extendScalarsAlgEquivEquiv_symm_apply (h₁ : U ≤ L₁) (h₂ : U ≤ L₂)
    (e : {e : L₁ ≃ₐ[K] L₂ // ∀ x : U, (e ⟨x.val, h₁ x.property⟩ : Ω) = x}) (x : extendScalars h₁) :
    ((extendScalarsAlgEquivEquiv h₁ h₂).symm e x : Ω) = e.val ⟨x.val, x.property⟩ := by
  rw [extendScalarsAlgEquivEquiv, Equiv.symm_trans_apply, Equiv.subtypeEquiv_symm,
    coe_restrictScalarsAlgEquivEquiv_symm_apply, Equiv.subtypeEquiv_apply]
  simp [AlgEquiv.equivCongr, -extendScalars_restrictScalars]

/-- Two extensions `extendScalars h₁` and `extendScalars h₂` are `U`-isomorphic precisely when
there is a `K`-isomorphism `L₁ ≃ₐ[K] L₂` fixing `U` pointwise. -/
theorem nonempty_extendScalars_algEquiv_iff (h₁ : U ≤ L₁) (h₂ : U ≤ L₂) :
    Nonempty (extendScalars h₁ ≃ₐ[U] extendScalars h₂) ↔
      ∃ e : L₁ ≃ₐ[K] L₂, ∀ x : U, (e ⟨x.val, h₁ x.property⟩ : Ω) = x :=
  (extendScalarsAlgEquivEquiv h₁ h₂).nonempty_congr.trans nonempty_subtype

/-- Viewing a `U`-automorphism of `extendScalars h` as a `K`-automorphism of `L`. -/
def extendScalarsAlgEquivHom (h : U ≤ L) :
    (extendScalars h ≃ₐ[U] extendScalars h) →* (L ≃ₐ[K] L) where
  toFun f := (extendScalarsAlgEquivEquiv h h f).val
  map_one' := by
    ext x
    simp
  map_mul' _ _ := by
    ext x
    simp

@[simp]
theorem coe_extendScalarsAlgEquivHom_apply (h : U ≤ L)
    (f : extendScalars h ≃ₐ[U] extendScalars h) (x : L) :
    (extendScalarsAlgEquivHom h f x : Ω) = f ⟨x.val, x.property⟩ := by
  simp [extendScalarsAlgEquivHom]

@[simp]
theorem extendScalarsAlgEquivHom_extendScalarsAlgEquivEquiv_symm (h : U ≤ L)
    (e : {e : L ≃ₐ[K] L // ∀ x : U, (e ⟨x.val, h x.property⟩ : Ω) = x}) :
    extendScalarsAlgEquivHom h ((extendScalarsAlgEquivEquiv h h).symm e) = e.val :=
  congrArg Subtype.val ((extendScalarsAlgEquivEquiv h h).apply_symm_apply e)

/-- Forgetting the `U`-algebra structure on automorphisms of `extendScalars h` is injective. -/
theorem extendScalarsAlgEquivHom_injective (h : U ≤ L) :
    Function.Injective (extendScalarsAlgEquivHom h) := by
  intro f g hfg
  ext x
  simpa using congrArg (fun σ : L ≃ₐ[K] L ↦ (σ ⟨x.val, x.property⟩ : Ω)) hfg

/-- A `K`-automorphism of `L` comes from a `U`-automorphism of `extendScalars h` precisely when it
fixes `U` pointwise. -/
theorem mem_range_extendScalarsAlgEquivHom_iff (h : U ≤ L) {σ : L ≃ₐ[K] L} :
    σ ∈ (extendScalarsAlgEquivHom h).range ↔ ∀ x : U, (σ ⟨x.val, h x.property⟩ : Ω) = x :=
  ⟨fun ⟨f, hf⟩ ↦ hf ▸ (extendScalarsAlgEquivEquiv h h f).property,
   fun hσ ↦ ⟨(extendScalarsAlgEquivEquiv h h).symm ⟨σ, hσ⟩,
     extendScalarsAlgEquivHom_extendScalarsAlgEquivEquiv_symm h ⟨σ, hσ⟩⟩⟩

end ExtendScalars

section FieldRangeBridge

variable {K F Ω : Type*} [Field K] [Field F] [Field Ω] [Algebra K F] [Algebra K Ω]
  [Algebra F Ω] [IsScalarTower K F Ω]

/-- If `U` is the image of `F` in `Ω` along a scalar tower `K → F → Ω`, then every intermediate
field `E` of `Ω / F` contains `U` after restricting scalars to `K`. -/
theorem le_restrictScalars_of_fieldRange_eq {U : IntermediateField K Ω}
    (hU : (IsScalarTower.toAlgHom K F Ω).fieldRange = U) (E : IntermediateField F Ω) :
    U ≤ E.restrictScalars K := by
  rw [← hU]
  rintro _ ⟨x, rfl⟩
  exact E.algebraMap_mem x

/-- Given a scalar tower `K → F → Ω` of fields and `U = (IsScalarTower.toAlgHom K F Ω).fieldRange`,
intermediate fields of `Ω / F` correspond order-isomorphically to intermediate fields of `Ω / U`. -/
def orderIsoOfFieldRangeEq {U : IntermediateField K Ω}
    (hU : (IsScalarTower.toAlgHom K F Ω).fieldRange = U) :
    IntermediateField F Ω ≃o IntermediateField U Ω :=
  have hmem (L : IntermediateField K Ω) :
      (∀ x : F, algebraMap F Ω x ∈ L) ↔ U ≤ L := by
    rw [← hU]
    exact ⟨by rintro h _ ⟨x, rfl⟩; exact h x, fun h x ↦ h ⟨x, rfl⟩⟩
  (restrictScalarsOrderIso K).trans <|
    ({ toFun := fun L ↦ ⟨L.val, (hmem L.val).1 L.property⟩
       invFun := fun L ↦ ⟨L.val, (hmem L.val).2 L.property⟩
       left_inv := fun _ ↦ rfl
       right_inv := fun _ ↦ rfl
       map_rel_iff' := Iff.rfl } : _ ≃o {L : IntermediateField K Ω // U ≤ L}).trans
      (extendScalars.orderIso U)

/-- `orderIsoOfFieldRangeEq hU` sends `E` to the extension of scalars of `E.restrictScalars K`
along `U ≤ E.restrictScalars K`. -/
theorem orderIsoOfFieldRangeEq_apply {U : IntermediateField K Ω}
    (hU : (IsScalarTower.toAlgHom K F Ω).fieldRange = U) (E : IntermediateField F Ω) :
    orderIsoOfFieldRangeEq hU E =
      extendScalars (le_restrictScalars_of_fieldRange_eq hU E) :=
  (rfl)

/-- Transporting an intermediate field along `orderIsoOfFieldRangeEq hU` preserves membership in
`Ω`. -/
@[simp]
theorem mem_orderIsoOfFieldRangeEq {U : IntermediateField K Ω}
    (hU : (IsScalarTower.toAlgHom K F Ω).fieldRange = U) (E : IntermediateField F Ω) {x : Ω} :
    x ∈ orderIsoOfFieldRangeEq hU E ↔ x ∈ E := by
  rw [orderIsoOfFieldRangeEq_apply, mem_extendScalars, mem_restrictScalars]

/-- Transporting an intermediate field along `(orderIsoOfFieldRangeEq hU).symm` preserves
membership in `Ω`. -/
@[simp]
theorem mem_orderIsoOfFieldRangeEq_symm {U : IntermediateField K Ω}
    (hU : (IsScalarTower.toAlgHom K F Ω).fieldRange = U) (E : IntermediateField U Ω) {x : Ω} :
    x ∈ (orderIsoOfFieldRangeEq hU).symm E ↔ x ∈ E := by
  rw [← mem_orderIsoOfFieldRangeEq hU ((orderIsoOfFieldRangeEq hU).symm E),
    OrderIso.apply_symm_apply]

/-- Transporting an intermediate field along `orderIsoOfFieldRangeEq hU` preserves its underlying
intermediate field over `K`. -/
@[simp]
theorem restrictScalars_orderIsoOfFieldRangeEq {U : IntermediateField K Ω}
    (hU : (IsScalarTower.toAlgHom K F Ω).fieldRange = U) (E : IntermediateField F Ω) :
    (orderIsoOfFieldRangeEq hU E).restrictScalars K = E.restrictScalars K := by
  rw [orderIsoOfFieldRangeEq_apply, extendScalars_restrictScalars]

/-- Transporting an intermediate field along `(orderIsoOfFieldRangeEq hU).symm` preserves its
underlying intermediate field over `K`. -/
@[simp]
theorem restrictScalars_orderIsoOfFieldRangeEq_symm {U : IntermediateField K Ω}
    (hU : (IsScalarTower.toAlgHom K F Ω).fieldRange = U) (E : IntermediateField U Ω) :
    ((orderIsoOfFieldRangeEq hU).symm E).restrictScalars K = E.restrictScalars K := by
  rw [← restrictScalars_orderIsoOfFieldRangeEq hU ((orderIsoOfFieldRangeEq hU).symm E),
    OrderIso.apply_symm_apply]

/-- Under `orderIsoOfFieldRangeEq hU`, `F`-algebra equivalences `E₁ ≃ₐ[F] E₂` correspond to
`U`-algebra equivalences between the corresponding intermediate fields of `Ω / U`. -/
def algEquivEquivOfFieldRangeEq {U : IntermediateField K Ω}
    (hU : (IsScalarTower.toAlgHom K F Ω).fieldRange = U) (E₁ E₂ : IntermediateField F Ω) :
    (E₁ ≃ₐ[F] E₂) ≃
      (orderIsoOfFieldRangeEq hU E₁ ≃ₐ[U] orderIsoOfFieldRangeEq hU E₂) :=
  let h₁ := le_restrictScalars_of_fieldRange_eq hU E₁
  let h₂ := le_restrictScalars_of_fieldRange_eq hU E₂
  have hfix (e : E₁.restrictScalars K ≃ₐ[K] E₂.restrictScalars K) :
      (∀ x : F, (e ⟨algebraMap F Ω x, E₁.algebraMap_mem x⟩ : Ω) = algebraMap F Ω x) ↔
        ∀ y : U, (e ⟨y.val, h₁ y.property⟩ : Ω) = y := by
    refine ⟨fun h y ↦ ?_, fun h x ↦ h ⟨algebraMap F Ω x, hU ▸ ⟨x, rfl⟩⟩⟩
    obtain ⟨x, hx⟩ : y.val ∈ (IsScalarTower.toAlgHom K F Ω).fieldRange := hU ▸ y.property
    have hy : (⟨y.val, h₁ y.property⟩ : E₁.restrictScalars K) =
        ⟨algebraMap F Ω x, E₁.algebraMap_mem x⟩ := Subtype.ext hx.symm
    exact (congrArg (fun z ↦ (e z : Ω)) hy).trans ((h x).trans hx)
  (restrictScalarsAlgEquivEquiv K E₁ E₂).trans <|
    (Equiv.subtypeEquivRight hfix).trans <|
      (extendScalarsAlgEquivEquiv h₁ h₂).symm.trans <|
        (equivOfEq (orderIsoOfFieldRangeEq_apply hU E₁).symm).equivCongr
          (equivOfEq (orderIsoOfFieldRangeEq_apply hU E₂).symm)

@[simp]
theorem coe_algEquivEquivOfFieldRangeEq_apply {U : IntermediateField K Ω}
    (hU : (IsScalarTower.toAlgHom K F Ω).fieldRange = U) (E₁ E₂ : IntermediateField F Ω)
    (f : E₁ ≃ₐ[F] E₂) (x : orderIsoOfFieldRangeEq hU E₁) :
    (algEquivEquivOfFieldRangeEq hU E₁ E₂ f x : Ω) =
      f ⟨x.val, (mem_orderIsoOfFieldRangeEq hU E₁).1 x.property⟩ := by
  simp [algEquivEquivOfFieldRangeEq, AlgEquiv.equivCongr]

@[simp]
theorem coe_algEquivEquivOfFieldRangeEq_symm_apply {U : IntermediateField K Ω}
    (hU : (IsScalarTower.toAlgHom K F Ω).fieldRange = U) (E₁ E₂ : IntermediateField F Ω)
    (g : orderIsoOfFieldRangeEq hU E₁ ≃ₐ[U] orderIsoOfFieldRangeEq hU E₂)
    (x : E₁) :
    ((algEquivEquivOfFieldRangeEq hU E₁ E₂).symm g x : Ω) =
      g ⟨x.val, (mem_orderIsoOfFieldRangeEq hU E₁).2 x.property⟩ := by
  simp [algEquivEquivOfFieldRangeEq, AlgEquiv.equivCongr]

end FieldRangeBridge

end IntermediateField

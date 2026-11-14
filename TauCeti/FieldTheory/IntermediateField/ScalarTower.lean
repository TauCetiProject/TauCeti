/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IntermediateField.Basic

/-!
# Scalar-change equivalences for intermediate fields

Mathlib's `IntermediateField.isScalarTower_mid` supplies `IsScalarTower K E L` for an intermediate
field `E` of `L / K`.  The same statement holds one step further down: a semiring `k`
whose actions on `K` and on `L` form a scalar tower `k → K → L` also acts compatibly through `E`.
Conversely, restricting the scalars of an intermediate field of `L / K` to `k` does not change the
field, as a `k`-algebra.

Building on `restrictScalarsAlgEquiv`, this file also packages scalar extension and field-range
transport for intermediate fields and their algebra equivalences:

* `U`-algebra equivalences `extendScalars h₁ ≃ₐ[U] extendScalars h₂` over an intermediate field
  `U` of `Ω / K` correspond to `K`-algebra equivalences `L₁ ≃ₐ[K] L₂` fixing `U` pointwise;
* for a scalar tower `K → F → Ω` of fields whose middle step has image `U` in `Ω`, intermediate
  fields of `Ω / F` and their `F`-algebra equivalences correspond to intermediate fields of `Ω / U`
  and their `U`-algebra equivalences.

## Main definitions

* `IntermediateField.restrictScalarsAlgEquiv`: an intermediate field `E` of `L / L'` and its
  restriction of scalars `E.restrictScalars K` are `K`-isomorphic.
* `IntermediateField.extendScalarsAlgEquiv`: `U`-algebra equivalences `extendScalars h₁ ≃ₐ[U]
  extendScalars h₂` correspond to `K`-algebra equivalences `L₁ ≃ₐ[K] L₂` fixing `U` pointwise.
* `IntermediateField.extendScalarsAlgEquivHom`: the injective homomorphism
  `(extendScalars h ≃ₐ[U] extendScalars h) →* (L ≃ₐ[K] L)`.
* `IntermediateField.intermediateFieldEquivOfFieldRangeEq`: equivalence
  `IntermediateField F Ω ≃ IntermediateField U Ω` when
  `(IsScalarTower.toAlgHom K F Ω).fieldRange = U`.
* `IntermediateField.algEquivOfFieldRangeEq`: equivalence `(E₁ ≃ₐ[F] E₂) ≃
  (intermediateFieldEquivOfFieldRangeEq hU E₁ ≃ₐ[U] intermediateFieldEquivOfFieldRangeEq hU E₂)`.

## Main results

* `IntermediateField.instIsScalarTower`: `IsScalarTower k E L` for an intermediate field
  `E` of `L / K` and a semiring `k` acting compatibly on `K` and `L`.
* `IntermediateField.le_of_isScalarTower`: an intermediate field `E` lies in an intermediate
  field `E'` as soon as some algebra structure of `E'` over `E` is compatible with `L`.
* `IntermediateField.nonempty_extendScalars_algEquiv_iff`: `extendScalars h₁` and
  `extendScalars h₂` are `U`-isomorphic precisely when some `L₁ ≃ₐ[K] L₂` fixes `U` pointwise.
* `IntermediateField.extendScalarsAlgEquivHom_injective` and
  `IntermediateField.mem_range_extendScalarsAlgEquivHom_iff`: `extendScalarsAlgEquivHom h` is
  injective with range the `K`-automorphisms of `L` fixing `U` pointwise.
* `IntermediateField.le_restrictScalars_of_fieldRange_eq`,
  `IntermediateField.intermediateFieldEquivOfFieldRangeEq_apply`,
  `IntermediateField.mem_intermediateFieldEquivOfFieldRangeEq`,
  `IntermediateField.restrictScalars_intermediateFieldEquivOfFieldRangeEq`,
  `IntermediateField.coe_algEquivOfFieldRangeEq_apply`, and
  `IntermediateField.coe_algEquivOfFieldRangeEq_symm_apply`: inclusion, explicit formula via
  `extendScalars`, membership and `restrictScalars` compatibility, and evaluation of
  `algEquivOfFieldRangeEq` and its inverse.
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

/-- If `E'` is an algebra over `E` compatibly with their inclusions in `L`, then `E ≤ E'`: every
`x ∈ E` is the image in `L` of `algebraMap E E' x ∈ E'`. -/
theorem le_of_isScalarTower {K L : Type*} [Field K] [Field L] [Algebra K L]
    {E E' : IntermediateField K L} [Algebra E E'] [IsScalarTower E E' L] : E ≤ E' := fun x hx ↦ by
  have h := (algebraMap E E' ⟨x, hx⟩).2
  rwa [← algebraMap_apply, ← IsScalarTower.algebraMap_apply] at h

section RestrictScalars

variable (K : Type*) {L' L : Type*} [Field K] [Field L'] [Field L] [Algebra K L'] [Algebra K L]
  [Algebra L' L] [IsScalarTower K L' L] (E : IntermediateField L' L)

/-- An intermediate field `E` of `L / L'` and its restriction of scalars `E.restrictScalars K`
have the same carrier; this is the resulting `K`-algebra equivalence between them, where `E` is a
`K`-algebra through `L'`. It lets a statement about `E` over `K` be read on the intermediate field
`E.restrictScalars K` of `L / K`, and conversely. -/
def restrictScalarsAlgEquiv : E.restrictScalars K ≃ₐ[K] E where
  toFun x := ⟨x, x.2⟩
  invFun x := ⟨x, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

@[simp]
theorem coe_restrictScalarsAlgEquiv_apply (x : E.restrictScalars K) :
    (restrictScalarsAlgEquiv K E x : L) = x :=
  (rfl)

@[simp]
theorem coe_restrictScalarsAlgEquiv_symm_apply (x : E) :
    ((restrictScalarsAlgEquiv K E).symm x : L) = x :=
  (rfl)

end RestrictScalars

section ExtendScalars

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] {U L L₁ L₂ : IntermediateField K Ω}

/-- An algebra equivalence `extendScalars h₁ ≃ₐ[U] extendScalars h₂` over an intermediate field
`U` is the same data as a `K`-algebra equivalence `L₁ ≃ₐ[K] L₂` fixing `U` pointwise. -/
def extendScalarsAlgEquiv (h₁ : U ≤ L₁) (h₂ : U ≤ L₂) :
    (extendScalars h₁ ≃ₐ[U] extendScalars h₂) ≃
      {e : L₁ ≃ₐ[K] L₂ // ∀ x : U, (e ⟨x.1, h₁ x.2⟩ : Ω) = x} where
  toFun f :=
    ⟨(restrictScalarsAlgEquiv K (extendScalars h₁)).trans
        ((f.restrictScalars K).trans (restrictScalarsAlgEquiv K (extendScalars h₂)).symm),
     fun x ↦ congrArg Subtype.val (f.commutes x)⟩
  invFun e := AlgEquiv.ofRingEquiv
    (f := ((restrictScalarsAlgEquiv K (extendScalars h₁)).symm.trans
      (e.1.trans (restrictScalarsAlgEquiv K (extendScalars h₂)))).toRingEquiv)
    fun u ↦ Subtype.ext (e.2 u)
  left_inv f := by
    ext x
    rfl
  right_inv e := by
    ext x
    rfl

@[simp]
theorem coe_extendScalarsAlgEquiv_apply (h₁ : U ≤ L₁) (h₂ : U ≤ L₂)
    (f : extendScalars h₁ ≃ₐ[U] extendScalars h₂) (x : L₁) :
    ((extendScalarsAlgEquiv h₁ h₂ f).1 x : Ω) = f ⟨x.1, x.2⟩ :=
  (rfl)

@[simp]
theorem coe_extendScalarsAlgEquiv_symm_apply (h₁ : U ≤ L₁) (h₂ : U ≤ L₂)
    (e : {e : L₁ ≃ₐ[K] L₂ // ∀ x : U, (e ⟨x.1, h₁ x.2⟩ : Ω) = x}) (x : extendScalars h₁) :
    ((extendScalarsAlgEquiv h₁ h₂).symm e x : Ω) = e.1 ⟨x.1, x.2⟩ :=
  (rfl)

/-- Two extensions `extendScalars h₁` and `extendScalars h₂` are `U`-isomorphic precisely when
there is a `K`-isomorphism `L₁ ≃ₐ[K] L₂` fixing `U` pointwise. -/
theorem nonempty_extendScalars_algEquiv_iff (h₁ : U ≤ L₁) (h₂ : U ≤ L₂) :
    Nonempty (extendScalars h₁ ≃ₐ[U] extendScalars h₂) ↔
      ∃ e : L₁ ≃ₐ[K] L₂, ∀ x : U, (e ⟨x.1, h₁ x.2⟩ : Ω) = x :=
  (extendScalarsAlgEquiv h₁ h₂).nonempty_congr.trans nonempty_subtype

/-- Viewing a `U`-automorphism of `extendScalars h` as a `K`-automorphism of `L`. -/
def extendScalarsAlgEquivHom (h : U ≤ L) :
    (extendScalars h ≃ₐ[U] extendScalars h) →* (L ≃ₐ[K] L) where
  toFun f := (extendScalarsAlgEquiv h h f).1
  map_one' := by
    ext x
    rfl
  map_mul' _ _ := by
    ext x
    rfl

@[simp]
theorem coe_extendScalarsAlgEquivHom_apply (h : U ≤ L)
    (f : extendScalars h ≃ₐ[U] extendScalars h) (x : L) :
    (extendScalarsAlgEquivHom h f x : Ω) = f ⟨x.1, x.2⟩ :=
  (rfl)

@[simp]
theorem extendScalarsAlgEquivHom_symm (h : U ≤ L)
    (e : {e : L ≃ₐ[K] L // ∀ x : U, (e ⟨x.1, h x.2⟩ : Ω) = x}) :
    extendScalarsAlgEquivHom h ((extendScalarsAlgEquiv h h).symm e) = e.1 :=
  congrArg Subtype.val ((extendScalarsAlgEquiv h h).apply_symm_apply e)

/-- Forgetting the `U`-algebra structure on automorphisms of `extendScalars h` is injective. -/
theorem extendScalarsAlgEquivHom_injective (h : U ≤ L) :
    Function.Injective (extendScalarsAlgEquivHom h) := by
  intro f g hfg
  ext x
  exact congrArg (fun σ : L ≃ₐ[K] L ↦ (σ ⟨x.1, x.2⟩ : Ω)) hfg

/-- A `K`-automorphism of `L` comes from a `U`-automorphism of `extendScalars h` precisely when it
fixes `U` pointwise. -/
theorem mem_range_extendScalarsAlgEquivHom_iff (h : U ≤ L) {σ : L ≃ₐ[K] L} :
    σ ∈ (extendScalarsAlgEquivHom h).range ↔ ∀ x : U, (σ ⟨x.1, h x.2⟩ : Ω) = x :=
  ⟨fun ⟨f, hf⟩ ↦ hf ▸ (extendScalarsAlgEquiv h h f).2,
   fun hσ ↦ ⟨(extendScalarsAlgEquiv h h).symm ⟨σ, hσ⟩,
     extendScalarsAlgEquivHom_symm h ⟨σ, hσ⟩⟩⟩

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
intermediate fields of `Ω / F` correspond to intermediate fields of `Ω / U`. -/
def intermediateFieldEquivOfFieldRangeEq {U : IntermediateField K Ω}
    (hU : (IsScalarTower.toAlgHom K F Ω).fieldRange = U) :
    IntermediateField F Ω ≃ IntermediateField U Ω :=
  have hmem (L : IntermediateField K Ω) :
      (∀ x : F, algebraMap F Ω x ∈ L) ↔ U ≤ L := by
    rw [← hU]
    exact ⟨by rintro h _ ⟨x, rfl⟩; exact h x, fun h x ↦ h ⟨x, rfl⟩⟩
  let ρ : IntermediateField F Ω ≃
      {L : IntermediateField K Ω // ∀ x : F, algebraMap F Ω x ∈ L} :=
    { toFun E := ⟨E.restrictScalars K, E.algebraMap_mem⟩
      invFun L := L.1.toSubfield.toIntermediateField L.2
      left_inv _ := rfl
      right_inv _ := rfl }
  ρ.trans ((Equiv.subtypeEquivRight hmem).trans (extendScalars.orderIso U).toEquiv)

/-- `intermediateFieldEquivOfFieldRangeEq hU` sends `E` to the extension of scalars of
`E.restrictScalars K` along `U ≤ E.restrictScalars K`. -/
theorem intermediateFieldEquivOfFieldRangeEq_apply {U : IntermediateField K Ω}
    (hU : (IsScalarTower.toAlgHom K F Ω).fieldRange = U) (E : IntermediateField F Ω) :
    intermediateFieldEquivOfFieldRangeEq hU E =
      extendScalars (le_restrictScalars_of_fieldRange_eq hU E) := by
  simp [intermediateFieldEquivOfFieldRangeEq]

/-- Transporting an intermediate field along `intermediateFieldEquivOfFieldRangeEq hU` preserves
membership in `Ω`. -/
@[simp]
theorem mem_intermediateFieldEquivOfFieldRangeEq {U : IntermediateField K Ω}
    (hU : (IsScalarTower.toAlgHom K F Ω).fieldRange = U) (E : IntermediateField F Ω) {x : Ω} :
    x ∈ intermediateFieldEquivOfFieldRangeEq hU E ↔ x ∈ E := by
  rw [intermediateFieldEquivOfFieldRangeEq_apply]
  rfl

/-- Transporting an intermediate field along `intermediateFieldEquivOfFieldRangeEq hU` preserves
its underlying intermediate field over `K`. -/
@[simp]
theorem restrictScalars_intermediateFieldEquivOfFieldRangeEq {U : IntermediateField K Ω}
    (hU : (IsScalarTower.toAlgHom K F Ω).fieldRange = U) (E : IntermediateField F Ω) :
    (intermediateFieldEquivOfFieldRangeEq hU E).restrictScalars K = E.restrictScalars K := by
  rw [intermediateFieldEquivOfFieldRangeEq_apply, extendScalars_restrictScalars]

/-- Under `intermediateFieldEquivOfFieldRangeEq hU`, `F`-algebra equivalences `E₁ ≃ₐ[F] E₂`
correspond to `U`-algebra equivalences between the corresponding intermediate fields of `Ω / U`. -/
def algEquivOfFieldRangeEq {U : IntermediateField K Ω}
    (hU : (IsScalarTower.toAlgHom K F Ω).fieldRange = U) (E₁ E₂ : IntermediateField F Ω) :
    (E₁ ≃ₐ[F] E₂) ≃
      (intermediateFieldEquivOfFieldRangeEq hU E₁ ≃ₐ[U]
        intermediateFieldEquivOfFieldRangeEq hU E₂) :=
  let h₁ := le_restrictScalars_of_fieldRange_eq hU E₁
  let h₂ := le_restrictScalars_of_fieldRange_eq hU E₂
  let ebase : (E₁ ≃ₐ[F] E₂) ≃
      {e : E₁.restrictScalars K ≃ₐ[K] E₂.restrictScalars K //
        ∀ y : U, (e ⟨y.1, h₁ y.2⟩ : Ω) = y.1} :=
    { toFun f := ⟨(restrictScalarsAlgEquiv K E₁).trans
          ((f.restrictScalars K).trans (restrictScalarsAlgEquiv K E₂).symm), fun y ↦ by
        have hyU : y.1 ∈ (IsScalarTower.toAlgHom K F Ω).fieldRange := hU.symm ▸ y.2
        obtain ⟨x, hx⟩ := hyU
        have hy : restrictScalarsAlgEquiv K E₁ ⟨y.1, h₁ y.2⟩ = algebraMap F E₁ x :=
          Subtype.ext (by simp [← hx])
        simp only [AlgEquiv.trans_apply, coe_restrictScalarsAlgEquiv_symm_apply, hy]
        exact (congrArg Subtype.val (f.commutes x)).trans (by simp [← hx])⟩
      invFun e := AlgEquiv.ofRingEquiv
        (f := ((restrictScalarsAlgEquiv K E₁).symm.trans
          (e.1.trans (restrictScalarsAlgEquiv K E₂))).toRingEquiv)
        fun x ↦ Subtype.ext <| by
          let y : U := ⟨algebraMap F Ω x, hU ▸ ⟨x, rfl⟩⟩
          have hx : (restrictScalarsAlgEquiv K E₁).symm (algebraMap F E₁ x) = ⟨y.1, h₁ y.2⟩ :=
            Subtype.ext (by simp [y])
          simp [AlgEquiv.trans_apply, hx, e.2 y, y]
      left_inv f := AlgEquiv.ext fun z ↦ Subtype.ext (by simp)
      right_inv e := Subtype.ext <| AlgEquiv.ext fun z ↦ Subtype.ext (by simp) }
  ebase.trans <| (extendScalarsAlgEquiv h₁ h₂).symm.trans <|
    (equivOfEq (intermediateFieldEquivOfFieldRangeEq_apply hU E₁).symm).equivCongr
      (equivOfEq (intermediateFieldEquivOfFieldRangeEq_apply hU E₂).symm)

@[simp]
theorem coe_algEquivOfFieldRangeEq_apply {U : IntermediateField K Ω}
    (hU : (IsScalarTower.toAlgHom K F Ω).fieldRange = U) (E₁ E₂ : IntermediateField F Ω)
    (f : E₁ ≃ₐ[F] E₂) (x : intermediateFieldEquivOfFieldRangeEq hU E₁) :
    (algEquivOfFieldRangeEq hU E₁ E₂ f x : Ω) =
      f ⟨x.1, (mem_intermediateFieldEquivOfFieldRangeEq hU E₁).1 x.2⟩ :=
  (rfl)

@[simp]
theorem coe_algEquivOfFieldRangeEq_symm_apply {U : IntermediateField K Ω}
    (hU : (IsScalarTower.toAlgHom K F Ω).fieldRange = U) (E₁ E₂ : IntermediateField F Ω)
    (g : intermediateFieldEquivOfFieldRangeEq hU E₁ ≃ₐ[U]
      intermediateFieldEquivOfFieldRangeEq hU E₂)
    (x : E₁) :
    ((algEquivOfFieldRangeEq hU E₁ E₂).symm g x : Ω) =
      g ⟨x.1, (mem_intermediateFieldEquivOfFieldRangeEq hU E₁).2 x.2⟩ :=
  (rfl)

end FieldRangeBridge

end IntermediateField

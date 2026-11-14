/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.Restriction
public import TauCeti.FieldTheory.IntermediateField.ScalarTower

/-!
# Automorphisms and isomorphism classes over a normal intermediate field

Let `Ω / K` be a field extension and `U` a normal intermediate field of `Ω / K`. Every
`K`-isomorphism `e : L₁ ≃ₐ[K] L₂` between intermediate fields of `Ω / K` with `U ≤ L₁` carries `U`
onto itself (`IntermediateField.le_of_algEquiv_of_normal`) and therefore restricts to an
automorphism `IntermediateField.restrictNormalOfLE h₁ e` of `U / K`.

For a single intermediate field `L` with `h : U ≤ L`, this restriction is the group homomorphism
`(inclusion h).restrictNormalHom : (L ≃ₐ[K] L) →* (U ≃ₐ[K] U)`:

* its kernel is the image of `(extendScalars h ≃ₐ[U] extendScalars h)` in `L ≃ₐ[K] L`, the
  `K`-automorphisms of `L` fixing `U` pointwise
  (`IntermediateField.range_extendScalarsAlgEquivHom_eq_ker`);
* its image consists of the automorphisms of `U / K` that extend to `L`
  (`IntermediateField.mem_range_restrictNormalHom_inclusion_iff`).

This decomposes the automorphism count of `L / K` into automorphisms over `U` and extendable
automorphisms of `U / K` (`IntermediateField.natCard_algEquiv_eq_mul_of_le`):

`#Aut_K(L) = #Aut_U(extendScalars h) · #{τ ∈ Aut_K(U) | τ extends to L}`.

Conjugation by any `K`-isomorphism `L₁ ≃ₐ[K] L₂` carries the `U`-automorphisms of `L₁` onto those
of `L₂` (`IntermediateField.extendScalarsAlgEquivCongr`), even when `Aut_K(U)` is non-abelian,
because conjugation of the identity on `U` is again the identity on `U`.

When the ambient extension `Ω / K` is also normal, the `U`-isomorphism classes of intermediate
fields `E` of `Ω / U` whose underlying `K`-field `E.restrictScalars K` is `K`-isomorphic to `L`
correspond bijectively to the left cosets `(U ≃ₐ[K] U) ⧸ (inclusion h).restrictNormalHom.range`
(`IntermediateField.restrictNormalCoset_eq_iff`, `IntermediateField.restrictNormalCoset_surjective`,
`IntermediateField.restrictNormalCosetEquiv`), giving the orbit-size formula
`IntermediateField.ncard_isomorphic_restrictScalars_mul_natCard_eq`.

## Main definitions

* `IntermediateField.extendScalarsAlgEquiv`: `U`-algebra equivalences `extendScalars h₁ ≃ₐ[U]
  extendScalars h₂` correspond to `K`-algebra equivalences `L₁ ≃ₐ[K] L₂` fixing `U` pointwise.
* `IntermediateField.extendScalarsAlgEquivHom`: the injective homomorphism
  `(extendScalars h ≃ₐ[U] extendScalars h) →* (L ≃ₐ[K] L)`.
* `IntermediateField.restrictNormalOfLE`: the automorphism of `U / K` induced by `e : L₁ ≃ₐ[K] L₂`
  when `U ≤ L₁` and `U / K` is normal.
* `IntermediateField.extendScalarsAlgEquivCongr`: the group isomorphism
  `(extendScalars h₁ ≃ₐ[U] extendScalars h₁) ≃* (extendScalars h₂ ≃ₐ[U] extendScalars h₂)` induced
  by conjugation along `e : L₁ ≃ₐ[K] L₂`.
* `IntermediateField.restrictNormalCoset`: the invariant in
  `(U ≃ₐ[K] U) ⧸ (inclusion h).restrictNormalHom.range` attached to `E : IntermediateField U Ω`
  with `Nonempty (L ≃ₐ[K] E.restrictScalars K)`.
* `IntermediateField.restrictNormalCosetEquiv`: bijection between `U`-isomorphism representatives
  in the `K`-isomorphism class of `L` and `(U ≃ₐ[K] U) ⧸ (inclusion h).restrictNormalHom.range`.

## Main results

* `IntermediateField.le_of_algEquiv_of_normal`: if `U / K` is normal and `U ≤ L₁`, then `U ≤ L₂`
  for any `e : L₁ ≃ₐ[K] L₂`.
* `IntermediateField.natCard_algEquiv_eq_mul_of_le`: decomposition of `Nat.card (L ≃ₐ[K] L)` along
  a normal intermediate field `U ≤ L`.
* `IntermediateField.natCard_algEquiv_eq_mul_of_normal`: when `L / K` is also normal, every
  automorphism of `U / K` extends to `L`, so `#Aut_K(L) = #Aut_U(extendScalars h) · #Aut_K(U)`.
* `IntermediateField.restrictNormalCoset_eq_iff`: two intermediate fields of `Ω / U` in the
  `K`-isomorphism class of `L` have the same coset invariant if and only if they are `U`-isomorphic.
* `IntermediateField.ncard_isomorphic_restrictScalars_mul_natCard_eq`: the number of
  `U`-isomorphism classes inside the `K`-isomorphism class of `L`, times the number of extendable
  automorphisms of `U / K`, equals `Nat.card (U ≃ₐ[K] U)`.
-/

public section
noncomputable section

open TauCeti

namespace IntermediateField

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]

/-! ### Extending scalars on algebra equivalences -/

section ExtendScalars

variable {U L L₁ L₂ : IntermediateField K Ω}

/-- An algebra equivalence `extendScalars h₁ ≃ₐ[U] extendScalars h₂` over an intermediate field
`U` is the same data as a `K`-algebra equivalence `L₁ ≃ₐ[K] L₂` fixing `U` pointwise. -/
def extendScalarsAlgEquiv (h₁ : U ≤ L₁) (h₂ : U ≤ L₂) :
    (extendScalars h₁ ≃ₐ[U] extendScalars h₂) ≃
      {e : L₁ ≃ₐ[K] L₂ // ∀ x : U, (e ⟨x.1, h₁ x.2⟩ : Ω) = x} where
  toFun f :=
    ⟨{ toFun x := ⟨(f ⟨x.1, x.2⟩).1, (f ⟨x.1, x.2⟩).2⟩
       invFun y := ⟨(f.symm ⟨y.1, y.2⟩).1, (f.symm ⟨y.1, y.2⟩).2⟩
       left_inv x := Subtype.ext (congrArg Subtype.val (f.symm_apply_apply ⟨x.1, x.2⟩))
       right_inv y := Subtype.ext (congrArg Subtype.val (f.apply_symm_apply ⟨y.1, y.2⟩))
       map_mul' x y := Subtype.ext (congrArg Subtype.val (f.map_mul ⟨x.1, x.2⟩ ⟨y.1, y.2⟩))
       map_add' x y := Subtype.ext (congrArg Subtype.val (f.map_add ⟨x.1, x.2⟩ ⟨y.1, y.2⟩))
       commutes' k := Subtype.ext <| by
         have hk : (⟨(algebraMap K L₁ k).1, (algebraMap K L₁ k).2⟩ : extendScalars h₁) =
             algebraMap U (extendScalars h₁) (algebraMap K U k) := Subtype.ext rfl
         rw [hk, f.commutes]
         rfl },
     fun x ↦ congrArg Subtype.val (f.commutes x)⟩
  invFun e :=
    { toFun x := ⟨(e.1 ⟨x.1, x.2⟩).1, (e.1 ⟨x.1, x.2⟩).2⟩
      invFun y := ⟨(e.1.symm ⟨y.1, y.2⟩).1, (e.1.symm ⟨y.1, y.2⟩).2⟩
      left_inv x := Subtype.ext (congrArg Subtype.val (e.1.symm_apply_apply ⟨x.1, x.2⟩))
      right_inv y := Subtype.ext (congrArg Subtype.val (e.1.apply_symm_apply ⟨y.1, y.2⟩))
      map_mul' x y := Subtype.ext (congrArg Subtype.val (e.1.map_mul ⟨x.1, x.2⟩ ⟨y.1, y.2⟩))
      map_add' x y := Subtype.ext (congrArg Subtype.val (e.1.map_add ⟨x.1, x.2⟩ ⟨y.1, y.2⟩))
      commutes' u := Subtype.ext (e.2 u) }
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

/-! ### Restriction to a normal intermediate field and automorphism count -/

section Normal

variable {U L L₁ L₂ L₃ : IntermediateField K Ω} [Normal K U]

/-- If `U / K` is normal and `U ≤ L₁`, then every `K`-isomorphism `L₁ ≃ₐ[K] L₂` carries `U` into
`L₂`: all `K`-embeddings of `U` into `Ω` have image `U`. -/
theorem le_of_algEquiv_of_normal (h₁ : U ≤ L₁) (e : L₁ ≃ₐ[K] L₂) : U ≤ L₂ := by
  let φ : U →ₐ[K] Ω := L₂.val.comp (e.toAlgHom.comp (inclusion h₁))
  have hφ : φ.fieldRange = U := by
    rw [← normalClosure_eq_fieldRange, normalClosure_eq_fieldRange U.val, fieldRange_val]
  rw [← hφ]
  rintro _ ⟨x, rfl⟩
  exact (e (inclusion h₁ x)).2

/-- The automorphism of a normal intermediate field `U / K` induced by a `K`-isomorphism
`e : L₁ ≃ₐ[K] L₂` when `U ≤ L₁`. On elements of `U` it acts as `e`. -/
def restrictNormalOfLE (h₁ : U ≤ L₁) (e : L₁ ≃ₐ[K] L₂) : U ≃ₐ[K] U :=
  (L₂.val.comp (e.toAlgHom.comp (inclusion h₁))).equivFieldRange.trans
    (equivOfEq (by
      rw [← normalClosure_eq_fieldRange, normalClosure_eq_fieldRange U.val, fieldRange_val]))

@[simp]
theorem coe_restrictNormalOfLE_apply (h₁ : U ≤ L₁) (e : L₁ ≃ₐ[K] L₂) (x : U) :
    (restrictNormalOfLE h₁ e x : Ω) = e ⟨x.1, h₁ x.2⟩ := by
  have hx : inclusion h₁ x = ⟨x.1, h₁ x.2⟩ := Subtype.ext rfl
  simp [restrictNormalOfLE, hx]

/-- `restrictNormalOfLE h₁ e` is characterized by agreeing with `e` on every element of `U`. -/
theorem restrictNormalOfLE_eq_iff (h₁ : U ≤ L₁) (e : L₁ ≃ₐ[K] L₂) {τ : U ≃ₐ[K] U} :
    restrictNormalOfLE h₁ e = τ ↔ ∀ x : U, (e ⟨x.1, h₁ x.2⟩ : Ω) = τ x := by
  refine ⟨fun h x ↦ h ▸ (coe_restrictNormalOfLE_apply h₁ e x).symm, fun h ↦ ?_⟩
  ext x
  exact (coe_restrictNormalOfLE_apply h₁ e x).trans (h x)

@[simp]
theorem restrictNormalOfLE_refl (h : U ≤ L) :
    restrictNormalOfLE h (AlgEquiv.refl : L ≃ₐ[K] L) = 1 := by
  rw [restrictNormalOfLE_eq_iff]
  intro x
  rfl

/-- Composition of `K`-isomorphisms reverses into group multiplication in `U ≃ₐ[K] U`, since
`(τ₂ * τ₁) x = τ₂ (τ₁ x) = (τ₁.trans τ₂) x`. -/
theorem restrictNormalOfLE_trans (h₁ : U ≤ L₁) (h₂ : U ≤ L₂) (e₁ : L₁ ≃ₐ[K] L₂)
    (e₂ : L₂ ≃ₐ[K] L₃) :
    restrictNormalOfLE h₁ (e₁.trans e₂) =
      restrictNormalOfLE h₂ e₂ * restrictNormalOfLE h₁ e₁ := by
  rw [restrictNormalOfLE_eq_iff]
  intro x
  have hx : (⟨(restrictNormalOfLE h₁ e₁ x : Ω), h₂ (restrictNormalOfLE h₁ e₁ x).2⟩ : L₂) =
      e₁ ⟨x.1, h₁ x.2⟩ := Subtype.ext (coe_restrictNormalOfLE_apply h₁ e₁ x)
  rw [AlgEquiv.mul_apply, coe_restrictNormalOfLE_apply, hx, AlgEquiv.trans_apply]

@[simp]
theorem restrictNormalOfLE_symm (h₁ : U ≤ L₁) (h₂ : U ≤ L₂) (e : L₁ ≃ₐ[K] L₂) :
    restrictNormalOfLE h₂ e.symm = (restrictNormalOfLE h₁ e)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← restrictNormalOfLE_trans h₁ h₂ e e.symm, AlgEquiv.self_trans_symm, restrictNormalOfLE_refl]

/-- On `K`-automorphisms of a single intermediate field `L` containing `U`, `restrictNormalOfLE h`
agrees with `(inclusion h).restrictNormalHom`. -/
theorem restrictNormalOfLE_eq_restrictNormalHom (h : U ≤ L) (σ : L ≃ₐ[K] L) :
    restrictNormalOfLE h σ = (inclusion h).restrictNormalHom σ := by
  rw [restrictNormalOfLE_eq_iff]
  intro x
  have hx : inclusion h x = ⟨x.1, h x.2⟩ := Subtype.ext rfl
  rw [← hx]
  exact congrArg Subtype.val ((inclusion h).restrictNormalHom_commutes σ x).symm

/-- The image of `extendScalarsAlgEquivHom h` is the kernel of `(inclusion h).restrictNormalHom`. -/
theorem range_extendScalarsAlgEquivHom_eq_ker (h : U ≤ L) :
    (extendScalarsAlgEquivHom h).range = (inclusion h).restrictNormalHom.ker := by
  ext σ
  rw [mem_range_extendScalarsAlgEquivHom_iff, MonoidHom.mem_ker,
    ← restrictNormalOfLE_eq_restrictNormalHom, restrictNormalOfLE_eq_iff]
  rfl

/-- An automorphism `τ` of `U / K` lies in the range of `(inclusion h).restrictNormalHom` precisely
when it extends to a `K`-automorphism of `L`. -/
theorem mem_range_restrictNormalHom_inclusion_iff (h : U ≤ L) {τ : U ≃ₐ[K] U} :
    τ ∈ (inclusion h).restrictNormalHom.range ↔
      ∃ σ : L ≃ₐ[K] L, ∀ x : U, (σ ⟨x.1, h x.2⟩ : Ω) = τ x := by
  simp only [MonoidHom.mem_range, ← restrictNormalOfLE_eq_restrictNormalHom,
    restrictNormalOfLE_eq_iff]

/-- Conjugating by a `K`-isomorphism `e : L₁ ≃ₐ[K] L₂` identifies the `U`-automorphism group of
`extendScalars h₁` with that of `extendScalars h₂`. Even when `U ≃ₐ[K] U` is non-abelian, an
automorphism fixing `U` pointwise restricts to `1` on `U`, and any conjugate of `1` in `U ≃ₐ[K] U`
is still `1`. -/
def extendScalarsAlgEquivCongr (h₁ : U ≤ L₁) (h₂ : U ≤ L₂) (e : L₁ ≃ₐ[K] L₂) :
    (extendScalars h₁ ≃ₐ[U] extendScalars h₁) ≃*
      (extendScalars h₂ ≃ₐ[U] extendScalars h₂) := by
  have hconj : ∀ {M₁ M₂ : IntermediateField K Ω} (hm₁ : U ≤ M₁) (hm₂ : U ≤ M₂) (g : M₁ ≃ₐ[K] M₂)
      (f : extendScalars hm₁ ≃ₐ[U] extendScalars hm₁),
      ∀ x : U, ((g.symm.trans ((extendScalarsAlgEquivHom hm₁ f).trans g)) ⟨x.1, hm₂ x.2⟩ : Ω) =
        x := by
    intro M₁ M₂ hm₁ hm₂ g f
    have hker : restrictNormalOfLE hm₁ (extendScalarsAlgEquivHom hm₁ f) = 1 := by
      rw [restrictNormalOfLE_eq_restrictNormalHom, ← MonoidHom.mem_ker,
        ← range_extendScalarsAlgEquivHom_eq_ker]
      exact ⟨f, rfl⟩
    have hres : restrictNormalOfLE hm₂
        (g.symm.trans ((extendScalarsAlgEquivHom hm₁ f).trans g)) = 1 := by
      rw [restrictNormalOfLE_trans hm₂ hm₁, restrictNormalOfLE_trans hm₁ hm₁,
        restrictNormalOfLE_symm hm₁ hm₂, hker, mul_one, mul_inv_cancel]
    exact (restrictNormalOfLE_eq_iff hm₂ _).1 hres
  refine
    { toFun f := (extendScalarsAlgEquiv h₂ h₂).symm
        ⟨e.symm.trans ((extendScalarsAlgEquivHom h₁ f).trans e), hconj h₁ h₂ e f⟩
      invFun f := (extendScalarsAlgEquiv h₁ h₁).symm
        ⟨e.trans ((extendScalarsAlgEquivHom h₂ f).trans e.symm), hconj h₂ h₁ e.symm f⟩
      left_inv f := by
        ext x
        simp
      right_inv f := by
        ext x
        simp
      map_mul' f g := by
        ext x
        simp }

@[simp]
theorem coe_extendScalarsAlgEquivCongr_apply (h₁ : U ≤ L₁) (h₂ : U ≤ L₂) (e : L₁ ≃ₐ[K] L₂)
    (f : extendScalars h₁ ≃ₐ[U] extendScalars h₁) (x : extendScalars h₂) :
    (extendScalarsAlgEquivCongr h₁ h₂ e f x : Ω) =
      e (extendScalarsAlgEquivHom h₁ f (e.symm ⟨x.1, x.2⟩)) :=
  (rfl)

/-- Two `K`-isomorphic intermediate fields containing a normal `U / K` have the same number of
`U`-automorphisms. -/
theorem natCard_extendScalars_algEquiv_eq_of_algEquiv (h₁ : U ≤ L₁) (h₂ : U ≤ L₂)
    (e : L₁ ≃ₐ[K] L₂) :
    Nat.card (extendScalars h₁ ≃ₐ[U] extendScalars h₁) =
      Nat.card (extendScalars h₂ ≃ₐ[U] extendScalars h₂) :=
  Nat.card_congr (extendScalarsAlgEquivCongr h₁ h₂ e).toEquiv

/-- If `E` is an intermediate field of `Ω / U` whose restriction of scalars `E.restrictScalars K`
is `K`-isomorphic to `L`, then `E` has the same number of `U`-automorphisms as `extendScalars h`. -/
theorem natCard_extendScalars_algEquiv_eq_of_algEquiv_restrictScalars (h : U ≤ L)
    {E : IntermediateField U Ω} (e : L ≃ₐ[K] E.restrictScalars K) :
    Nat.card (extendScalars h ≃ₐ[U] extendScalars h) = Nat.card (E ≃ₐ[U] E) := by
  have hE : U ≤ E.restrictScalars K := fun x hx ↦ E.algebraMap_mem ⟨x, hx⟩
  have heq : extendScalars hE = E := (extendScalars.orderIso U).apply_symm_apply E
  rw [natCard_extendScalars_algEquiv_eq_of_algEquiv h hE e, heq]

/-- **Decomposition of the automorphism count along a normal intermediate field.** For an
intermediate field `L` of `Ω / K` containing a normal `U / K`, the restriction homomorphism
`(inclusion h).restrictNormalHom : (L ≃ₐ[K] L) →* (U ≃ₐ[K] U)` has kernel isomorphic to
`extendScalars h ≃ₐ[U] extendScalars h` and image the automorphisms of `U / K` extending to `L`.
No finiteness or separability hypothesis is needed. -/
theorem natCard_algEquiv_eq_mul_of_le (h : U ≤ L) :
    Nat.card (L ≃ₐ[K] L) =
      Nat.card (extendScalars h ≃ₐ[U] extendScalars h) *
        Nat.card {τ : U ≃ₐ[K] U //
          ∃ σ : L ≃ₐ[K] L, ∀ x : U, (σ ⟨x.1, h x.2⟩ : Ω) = τ x} := by
  rw [← Subgroup.card_ker_mul_card_range (inclusion h).restrictNormalHom,
    ← range_extendScalarsAlgEquivHom_eq_ker h]
  congr 1
  · exact (Nat.card_congr (Equiv.ofInjective _ (extendScalarsAlgEquivHom_injective h))).symm
  · exact Nat.card_congr (Equiv.subtypeEquivRight fun _ ↦
      mem_range_restrictNormalHom_inclusion_iff h)

/-- When `L / K` is also normal, every automorphism of `U / K` extends to `L`, so
`#Aut_K(L) = #Aut_U(extendScalars h) · #Aut_K(U)`. -/
theorem natCard_algEquiv_eq_mul_of_normal [Normal K L] (h : U ≤ L) :
    Nat.card (L ≃ₐ[K] L) =
      Nat.card (extendScalars h ≃ₐ[U] extendScalars h) * Nat.card (U ≃ₐ[K] U) := by
  rw [← Subgroup.card_ker_mul_card_of_surjective (inclusion h).restrictNormalHom_surjective,
    ← range_extendScalarsAlgEquivHom_eq_ker h]
  congr 1
  exact (Nat.card_congr (Equiv.ofInjective _ (extendScalarsAlgEquivHom_injective h))).symm

end Normal

/-! ### Galois orbits of `U`-isomorphism classes inside a `K`-isomorphism class -/

section Coset

variable {U L : IntermediateField K Ω} [Normal K U]

/-- For an intermediate field `E` of `Ω / U` whose restriction of scalars `E.restrictScalars K` is
`K`-isomorphic to `L` (where `h : U ≤ L`), any `K`-isomorphism `e : L ≃ₐ[K] E.restrictScalars K`
restricts to an element of `U ≃ₐ[K] U` whose left coset modulo
`(inclusion h).restrictNormalHom.range` depends only on the `U`-isomorphism class of `E`. -/
def restrictNormalCoset (h : U ≤ L) (E : IntermediateField U Ω)
    (hE : Nonempty (L ≃ₐ[K] E.restrictScalars K)) :
    (U ≃ₐ[K] U) ⧸ (inclusion h).restrictNormalHom.range :=
  QuotientGroup.mk (restrictNormalOfLE h (Classical.choice hE))

/-- Any choice of `K`-isomorphism `e : L ≃ₐ[K] E.restrictScalars K` computes
`restrictNormalCoset h E hE`. -/
theorem restrictNormalCoset_eq_mk (h : U ≤ L) {E : IntermediateField U Ω}
    (hE : Nonempty (L ≃ₐ[K] E.restrictScalars K)) (e : L ≃ₐ[K] E.restrictScalars K) :
    restrictNormalCoset h E hE = QuotientGroup.mk (restrictNormalOfLE h e) := by
  let e₀ := Classical.choice hE
  have hE_le : U ≤ E.restrictScalars K := fun x hx ↦ E.algebraMap_mem ⟨x, hx⟩
  rw [restrictNormalCoset, QuotientGroup.eq, MonoidHom.mem_range]
  refine ⟨e.trans e₀.symm, ?_⟩
  rw [← restrictNormalOfLE_eq_restrictNormalHom, restrictNormalOfLE_trans h hE_le,
    restrictNormalOfLE_symm h hE_le]

/-- **Coset classification of `U`-isomorphism classes inside a `K`-isomorphism class.** Two
intermediate fields `E₁, E₂` of `Ω / U` whose underlying `K`-fields are `K`-isomorphic to `L` have
the same coset in `(U ≃ₐ[K] U) ⧸ (inclusion h).restrictNormalHom.range` if and only if `E₁` and
`E₂` are `U`-isomorphic. -/
theorem restrictNormalCoset_eq_iff (h : U ≤ L) {E₁ E₂ : IntermediateField U Ω}
    (h₁ : Nonempty (L ≃ₐ[K] E₁.restrictScalars K))
    (h₂ : Nonempty (L ≃ₐ[K] E₂.restrictScalars K)) :
    restrictNormalCoset h E₁ h₁ = restrictNormalCoset h E₂ h₂ ↔ Nonempty (E₁ ≃ₐ[U] E₂) := by
  obtain ⟨e₁⟩ := h₁
  obtain ⟨e₂⟩ := h₂
  have hle₁ : U ≤ E₁.restrictScalars K := fun x hx ↦ E₁.algebraMap_mem ⟨x, hx⟩
  have hle₂ : U ≤ E₂.restrictScalars K := fun x hx ↦ E₂.algebraMap_mem ⟨x, hx⟩
  have hext₁ : extendScalars hle₁ = E₁ := (extendScalars.orderIso U).apply_symm_apply E₁
  have hext₂ : extendScalars hle₂ = E₂ := (extendScalars.orderIso U).apply_symm_apply E₂
  have hiso : Nonempty (extendScalars hle₁ ≃ₐ[U] extendScalars hle₂) ↔ Nonempty (E₁ ≃ₐ[U] E₂) := by
    rw [hext₁, hext₂]
  rw [restrictNormalCoset_eq_mk h ⟨e₁⟩ e₁, restrictNormalCoset_eq_mk h ⟨e₂⟩ e₂,
    QuotientGroup.eq, ← hiso, nonempty_extendScalars_algEquiv_iff]
  constructor
  · rintro ⟨σ, hσ⟩
    refine ⟨(σ.trans e₁).symm.trans e₂, ?_⟩
    have h1 : restrictNormalOfLE hle₁ ((σ.trans e₁).symm.trans e₂) = 1 := by
      rw [restrictNormalOfLE_trans hle₁ h, restrictNormalOfLE_symm h hle₁,
        restrictNormalOfLE_trans h h, restrictNormalOfLE_eq_restrictNormalHom, hσ,
        mul_inv_cancel_left, mul_inv_cancel]
    exact (restrictNormalOfLE_eq_iff hle₁ _).1 h1
  · rintro ⟨f, hf⟩
    have hf_one : restrictNormalOfLE hle₁ f = 1 :=
      (restrictNormalOfLE_eq_iff hle₁ f).2 hf
    refine ⟨e₂.trans (f.symm.trans e₁.symm), ?_⟩
    rw [← restrictNormalOfLE_eq_restrictNormalHom, restrictNormalOfLE_trans h hle₂,
      restrictNormalOfLE_trans hle₂ hle₁, restrictNormalOfLE_symm hle₁ hle₂,
      restrictNormalOfLE_symm h hle₁, hf_one, inv_one, mul_one]

/-- When the ambient extension `Ω / K` is normal, every coset in
`(U ≃ₐ[K] U) ⧸ (inclusion h).restrictNormalHom.range` is realized by some
`E : IntermediateField U Ω` whose restriction of scalars is `K`-isomorphic to `L`: lifting
`τ : U ≃ₐ[K] U` to `Ω ≃ₐ[K] Ω` and mapping `L` along the lift produces an intermediate field
containing `U` with coset `τ`. -/
theorem restrictNormalCoset_surjective [Normal K Ω] (h : U ≤ L)
    (c : (U ≃ₐ[K] U) ⧸ (inclusion h).restrictNormalHom.range) :
    ∃ (E : IntermediateField U Ω) (hE : Nonempty (L ≃ₐ[K] E.restrictScalars K)),
      restrictNormalCoset h E hE = c := by
  induction c using QuotientGroup.induction_on with
  | H τ =>
    let g : Ω ≃ₐ[K] Ω := τ.liftNormal Ω
    let e₀ : L ≃ₐ[K] L.map g.toAlgHom := intermediateFieldMap g L
    have hM : U ≤ L.map g.toAlgHom := le_of_algEquiv_of_normal h e₀
    let e₁ : L ≃ₐ[K] (extendScalars hM).restrictScalars K :=
      e₀.trans (equivOfEq (extendScalars_restrictScalars hM).symm)
    refine ⟨extendScalars hM, ⟨e₁⟩, ?_⟩
    rw [restrictNormalCoset_eq_mk h ⟨e₁⟩ e₁]
    congr 1
    rw [restrictNormalOfLE_eq_iff]
    intro x
    exact τ.liftNormal_commutes Ω x

/-- If `R` contains a unique `U`-isomorphic representative of every `E : IntermediateField U Ω`
with `Nonempty (L ≃ₐ[K] E.restrictScalars K)`, then `restrictNormalCoset h` gives a bijection from
the members of `R` in the `K`-isomorphism class of `L` onto
`(U ≃ₐ[K] U) ⧸ (inclusion h).restrictNormalHom.range`. -/
def restrictNormalCosetEquiv [Normal K Ω] (h : U ≤ L) {R : Set (IntermediateField U Ω)}
    (hR : ∀ E : IntermediateField U Ω, Nonempty (L ≃ₐ[K] E.restrictScalars K) →
      ∃! F, F ∈ R ∧ Nonempty (E ≃ₐ[U] F)) :
    {E : IntermediateField U Ω // E ∈ R ∧ Nonempty (L ≃ₐ[K] E.restrictScalars K)} ≃
      ((U ≃ₐ[K] U) ⧸ (inclusion h).restrictNormalHom.range) := by
  refine Equiv.ofBijective (fun E ↦ restrictNormalCoset h E.1 E.2.2) ⟨?_, ?_⟩
  · rintro ⟨E₁, hR₁, hL₁⟩ ⟨E₂, hR₂, hL₂⟩ heq
    have hiso : Nonempty (E₁ ≃ₐ[U] E₂) := (restrictNormalCoset_eq_iff h hL₁ hL₂).1 heq
    exact Subtype.ext (((hR E₁ hL₁).unique ⟨hR₁, ⟨.refl⟩⟩ ⟨hR₂, hiso⟩))
  · intro c
    obtain ⟨E, ⟨e⟩, rfl⟩ := restrictNormalCoset_surjective h c
    obtain ⟨F, ⟨hFR, ⟨f⟩⟩, -⟩ := hR E ⟨e⟩
    have hLF : Nonempty (L ≃ₐ[K] F.restrictScalars K) :=
      ⟨e.trans ((restrictScalarsAlgEquiv K E).trans
        ((f.restrictScalars K).trans (restrictScalarsAlgEquiv K F).symm))⟩
    exact ⟨⟨F, hFR, hLF⟩, ((restrictNormalCoset_eq_iff h ⟨e⟩ hLF).2 ⟨f⟩).symm⟩

/-- **The Galois orbit count of `U`-classes inside a `K`-class.** When `Ω / K` and `U / K` are
normal, `h : U ≤ L`, and `R` contains a unique `U`-isomorphic representative of every
`E : IntermediateField U Ω` whose underlying `K`-field is `K`-isomorphic to `L`, the number of
such representatives in `R`, multiplied by the number of automorphisms of `U / K` extending to `L`,
is `Nat.card (U ≃ₐ[K] U)`. No finiteness hypothesis is needed. -/
theorem ncard_isomorphic_restrictScalars_mul_natCard_eq [Normal K Ω] (h : U ≤ L)
    {R : Set (IntermediateField U Ω)}
    (hR : ∀ E : IntermediateField U Ω, Nonempty (L ≃ₐ[K] E.restrictScalars K) →
      ∃! F, F ∈ R ∧ Nonempty (E ≃ₐ[U] F)) :
    {E ∈ R | Nonempty (L ≃ₐ[K] E.restrictScalars K)}.ncard *
        Nat.card {τ : U ≃ₐ[K] U //
          ∃ σ : L ≃ₐ[K] L, ∀ x : U, (σ ⟨x.1, h x.2⟩ : Ω) = τ x} =
      Nat.card (U ≃ₐ[K] U) := by
  have hdom : {E : IntermediateField U Ω // E ∈ R ∧ Nonempty (L ≃ₐ[K] E.restrictScalars K)} ≃
      {E ∈ R | Nonempty (L ≃ₐ[K] E.restrictScalars K)} := Equiv.refl _
  rw [← Nat.card_coe_set_eq, ← Nat.card_congr hdom,
    Nat.card_congr (restrictNormalCosetEquiv h hR), ← Subgroup.index_eq_card,
    ← Nat.card_congr (Equiv.subtypeEquivRight fun _ ↦ mem_range_restrictNormalHom_inclusion_iff h),
    Subgroup.index_mul_card]

end Coset

end IntermediateField

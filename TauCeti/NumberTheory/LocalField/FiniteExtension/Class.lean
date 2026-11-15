/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.ExtensionClass
public import TauCeti.NumberTheory.LocalField.Unramified.Basic
import TauCeti.NumberTheory.LocalField.FiniteExtension.Basic
import TauCeti.NumberTheory.LocalField.Unramified.Factorization

/-!
# Local-field invariants of finite extension classes

Every finite extension `L/K` of a nonarchimedean local field `K` carries a unique valuative
relation and local-field topology extending those of `K`
(`TauCeti.algebraicExtensionValuativeRel`, `TauCeti.finiteExtension_isNonarchimedeanLocalField`),
and its residue degree `f(L/K)` and ramification index `e(L/K)` depend only on the `K`-algebra
isomorphism class of `L`. This file descends these invariants and the predicates `IsUnramified`
and `IsTotallyRamified` to `TauCeti.FiniteExtensionClass K`, proves the fundamental identity
`e · f = [L : K]` and tower multiplicativity under `FiniteExtensionClass.restrictScalars`, and
establishes their invariance under valuation-preserving ring equivalences and the transport-of-
structure action of `F ≃ₐ[K] F`.

## Main definitions

* `TauCeti.FiniteExtensionClass.inertiaDegree`: the residue degree of a finite extension class of
  a nonarchimedean local field.
* `TauCeti.FiniteExtensionClass.ramificationIndex`: the ramification index of a finite extension
  class of a nonarchimedean local field.
* `TauCeti.FiniteExtensionClass.IsUnramified`: predicate that a finite extension class has
  ramification index `1`.
* `TauCeti.FiniteExtensionClass.IsTotallyRamified`: predicate that a finite extension class has
  residue degree `1`.

## Main results

* `TauCeti.FiniteExtensionClass.induction_on_localField`: elimination principle representing any
  `c : FiniteExtensionClass K` by a compatible nonarchimedean local-field extension `L : Type u`.
* `TauCeti.FiniteExtensionClass.inertiaDegree_mk`,
  `TauCeti.FiniteExtensionClass.ramificationIndex_mk`,
  `TauCeti.FiniteExtensionClass.isUnramified_mk_iff`,
  `TauCeti.FiniteExtensionClass.isTotallyRamified_mk_iff`: evaluation on `mk K L` for any
  compatible nonarchimedean local-field extension `L` in any universe.
* `TauCeti.FiniteExtensionClass.ramificationIndex_mul_inertiaDegree`: `e(c) · f(c) = c.finrank`.
* `TauCeti.FiniteExtensionClass.inertiaDegree_restrictScalars` and
  `TauCeti.FiniteExtensionClass.ramificationIndex_restrictScalars`: multiplicativity under
  restriction of scalars along a local-field extension `F/K`.
* `TauCeti.FiniteExtensionClass.inertiaDegree_mapEquiv_of_vle_iff`,
  `TauCeti.FiniteExtensionClass.ramificationIndex_mapEquiv_of_vle_iff`,
  `TauCeti.FiniteExtensionClass.inertiaDegree_smul`, and
  `TauCeti.FiniteExtensionClass.ramificationIndex_smul`: invariance under valuation-preserving
  transport of structure and under `Gal(F/K)`.
-/

public section

noncomputable section

open ValuativeRel

namespace TauCeti.FiniteExtensionClass

universe u v w

section Invariants

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- Elimination principle for `FiniteExtensionClass K` over a nonarchimedean local field `K`: every
class is `mk K L` for a finite extension `L : Type u` equipped with a compatible nonarchimedean
local-field structure. -/
@[elab_as_elim]
theorem induction_on_localField {motive : FiniteExtensionClass K → Prop}
    (c : FiniteExtensionClass K)
    (h : ∀ (L : Type u) [Field L] [ValuativeRel L] [TopologicalSpace L]
      [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [Module.Finite K L],
      motive (mk K L)) :
    motive c := by
  induction c using induction_on with | h L =>
  let : ValuativeRel L := algebraicExtensionValuativeRel K L
  let : TopologicalSpace L := algebraicExtensionNormedFieldTopology K L
  have : IsNonarchimedeanLocalField L := finiteExtension_isNonarchimedeanLocalField K L
  have : ValuativeExtension K L := algebraicExtension_valuativeExtension K L
  exact h L

/-- The residue degree `f(c)` of a finite extension class `c` of a nonarchimedean local field `K`,
computed in the canonical spectral-norm local-field structure on any representative. -/
def inertiaDegree (c : FiniteExtensionClass K) : ℕ :=
  c.lift
    (fun L _ _ _ ↦
      letI : ValuativeRel L := algebraicExtensionValuativeRel K L
      letI : TopologicalSpace L := algebraicExtensionNormedFieldTopology K L
      haveI : IsNonarchimedeanLocalField L := finiteExtension_isNonarchimedeanLocalField K L
      haveI : ValuativeExtension K L := algebraicExtension_valuativeExtension K L
      TauCeti.inertiaDegree K L)
    fun L₁ L₂ _ _ _ _ _ _ e ↦ by
      let : ValuativeRel L₁ := algebraicExtensionValuativeRel K L₁
      let : TopologicalSpace L₁ := algebraicExtensionNormedFieldTopology K L₁
      have : IsNonarchimedeanLocalField L₁ := finiteExtension_isNonarchimedeanLocalField K L₁
      have : ValuativeExtension K L₁ := algebraicExtension_valuativeExtension K L₁
      let : ValuativeRel L₂ := algebraicExtensionValuativeRel K L₂
      let : TopologicalSpace L₂ := algebraicExtensionNormedFieldTopology K L₂
      have : IsNonarchimedeanLocalField L₂ := finiteExtension_isNonarchimedeanLocalField K L₂
      have : ValuativeExtension K L₂ := algebraicExtension_valuativeExtension K L₂
      exact TauCeti.inertiaDegree_eq_of_algEquiv K L₁ L₂ e

/-- The ramification index `e(c)` of a finite extension class `c` of a nonarchimedean local field
`K`, computed in the canonical spectral-norm local-field structure on any representative. -/
def ramificationIndex (c : FiniteExtensionClass K) : ℕ :=
  c.lift
    (fun L _ _ _ ↦
      letI : ValuativeRel L := algebraicExtensionValuativeRel K L
      letI : TopologicalSpace L := algebraicExtensionNormedFieldTopology K L
      haveI : IsNonarchimedeanLocalField L := finiteExtension_isNonarchimedeanLocalField K L
      haveI : ValuativeExtension K L := algebraicExtension_valuativeExtension K L
      TauCeti.ramificationIndex K L)
    fun L₁ L₂ _ _ _ _ _ _ e ↦ by
      let : ValuativeRel L₁ := algebraicExtensionValuativeRel K L₁
      let : TopologicalSpace L₁ := algebraicExtensionNormedFieldTopology K L₁
      have : IsNonarchimedeanLocalField L₁ := finiteExtension_isNonarchimedeanLocalField K L₁
      have : ValuativeExtension K L₁ := algebraicExtension_valuativeExtension K L₁
      let : ValuativeRel L₂ := algebraicExtensionValuativeRel K L₂
      let : TopologicalSpace L₂ := algebraicExtensionNormedFieldTopology K L₂
      have : IsNonarchimedeanLocalField L₂ := finiteExtension_isNonarchimedeanLocalField K L₂
      have : ValuativeExtension K L₂ := algebraicExtension_valuativeExtension K L₂
      exact TauCeti.ramificationIndex_eq_of_algEquiv K L₁ L₂ e

@[simp]
theorem inertiaDegree_mk (L : Type v) [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [Module.Finite K L] :
    (mk K L).inertiaDegree = TauCeti.inertiaDegree K L := by
  obtain ⟨M, _, _, _, hM⟩ := exists_mk (mk K L)
  obtain ⟨e⟩ := (mk_eq_mk_iff L M).1 hM
  rw [hM, inertiaDegree, lift_mk]
  let : ValuativeRel M := algebraicExtensionValuativeRel K M
  let : TopologicalSpace M := algebraicExtensionNormedFieldTopology K M
  have : IsNonarchimedeanLocalField M := finiteExtension_isNonarchimedeanLocalField K M
  have : ValuativeExtension K M := algebraicExtension_valuativeExtension K M
  exact TauCeti.inertiaDegree_eq_of_algEquiv K M L e.symm

@[simp]
theorem ramificationIndex_mk (L : Type v) [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [Module.Finite K L] :
    (mk K L).ramificationIndex = TauCeti.ramificationIndex K L := by
  obtain ⟨M, _, _, _, hM⟩ := exists_mk (mk K L)
  obtain ⟨e⟩ := (mk_eq_mk_iff L M).1 hM
  rw [hM, ramificationIndex, lift_mk]
  let : ValuativeRel M := algebraicExtensionValuativeRel K M
  let : TopologicalSpace M := algebraicExtensionNormedFieldTopology K M
  have : IsNonarchimedeanLocalField M := finiteExtension_isNonarchimedeanLocalField K M
  have : ValuativeExtension K M := algebraicExtension_valuativeExtension K M
  exact TauCeti.ramificationIndex_eq_of_algEquiv K M L e.symm

theorem inertiaDegree_pos (c : FiniteExtensionClass K) : 0 < c.inertiaDegree := by
  induction c using induction_on_localField with | h L =>
  rw [inertiaDegree_mk]
  exact TauCeti.inertiaDegree_pos

theorem inertiaDegree_ne_zero (c : FiniteExtensionClass K) : c.inertiaDegree ≠ 0 :=
  c.inertiaDegree_pos.ne'

theorem ramificationIndex_pos (c : FiniteExtensionClass K) : 0 < c.ramificationIndex := by
  induction c using induction_on_localField with | h L =>
  rw [ramificationIndex_mk]
  exact TauCeti.ramificationIndex_pos

theorem ramificationIndex_ne_zero (c : FiniteExtensionClass K) : c.ramificationIndex ≠ 0 :=
  c.ramificationIndex_pos.ne'

/-- **Fundamental identity on isomorphism classes**: `e(c) · f(c) = c.finrank`. -/
theorem ramificationIndex_mul_inertiaDegree (c : FiniteExtensionClass K) :
    c.ramificationIndex * c.inertiaDegree = c.finrank := by
  induction c using induction_on_localField with | h L =>
  rw [ramificationIndex_mk, inertiaDegree_mk, finrank_mk,
    TauCeti.ramificationIndex_mul_inertiaDegree]

theorem inertiaDegree_dvd_finrank (c : FiniteExtensionClass K) :
    c.inertiaDegree ∣ c.finrank :=
  ⟨c.ramificationIndex, by rw [mul_comm, c.ramificationIndex_mul_inertiaDegree]⟩

theorem ramificationIndex_dvd_finrank (c : FiniteExtensionClass K) :
    c.ramificationIndex ∣ c.finrank :=
  ⟨c.inertiaDegree, c.ramificationIndex_mul_inertiaDegree.symm⟩

@[simp]
theorem inertiaDegree_self : (self K).inertiaDegree = 1 :=
  (mul_eq_one.mp ((self K).ramificationIndex_mul_inertiaDegree.trans finrank_self)).2

@[simp]
theorem ramificationIndex_self : (self K).ramificationIndex = 1 :=
  (mul_eq_one.mp ((self K).ramificationIndex_mul_inertiaDegree.trans finrank_self)).1

/-- A finite extension class of a nonarchimedean local field is **unramified** when its
ramification index is `1`. -/
def IsUnramified (c : FiniteExtensionClass K) : Prop :=
  c.ramificationIndex = 1

theorem isUnramified_iff_ramificationIndex_eq_one {c : FiniteExtensionClass K} :
    c.IsUnramified ↔ c.ramificationIndex = 1 :=
  (Iff.rfl)

@[simp]
theorem isUnramified_mk_iff (L : Type v) [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [Module.Finite K L] :
    (mk K L).IsUnramified ↔ TauCeti.IsUnramified K L := by
  rw [isUnramified_iff_ramificationIndex_eq_one, ramificationIndex_mk,
    TauCeti.isUnramified_iff_ramificationIndex_eq_one]

theorem isUnramified_iff_inertiaDegree_eq_finrank {c : FiniteExtensionClass K} :
    c.IsUnramified ↔ c.inertiaDegree = c.finrank := by
  induction c using induction_on_localField with | h L =>
  rw [isUnramified_mk_iff, inertiaDegree_mk, finrank_mk,
    TauCeti.isUnramified_iff_inertiaDegree_eq_finrank]

@[simp]
theorem isUnramified_self : (self K).IsUnramified := by
  rw [isUnramified_iff_ramificationIndex_eq_one, ramificationIndex_self]

theorem IsUnramified.isSeparable {c : FiniteExtensionClass K} (hc : c.IsUnramified) :
    c.IsSeparable := by
  induction c using induction_on_localField with | h L =>
  rw [isUnramified_mk_iff] at hc
  have := TauCeti.IsUnramified.isGalois K L
  exact (isSeparable_mk_iff L).2 inferInstance

/-- A finite extension class of a nonarchimedean local field is **totally ramified** when its
residue degree is `1`. -/
def IsTotallyRamified (c : FiniteExtensionClass K) : Prop :=
  c.inertiaDegree = 1

theorem isTotallyRamified_iff_inertiaDegree_eq_one {c : FiniteExtensionClass K} :
    c.IsTotallyRamified ↔ c.inertiaDegree = 1 :=
  (Iff.rfl)

@[simp]
theorem isTotallyRamified_mk_iff (L : Type v) [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [Module.Finite K L] :
    (mk K L).IsTotallyRamified ↔ TauCeti.IsTotallyRamified K L := by
  rw [isTotallyRamified_iff_inertiaDegree_eq_one, inertiaDegree_mk,
    TauCeti.isTotallyRamified_iff_inertiaDegree_eq_one]

theorem isTotallyRamified_iff_ramificationIndex_eq_finrank {c : FiniteExtensionClass K} :
    c.IsTotallyRamified ↔ c.ramificationIndex = c.finrank := by
  induction c using induction_on_localField with | h L =>
  rw [isTotallyRamified_mk_iff, ramificationIndex_mk, finrank_mk,
    TauCeti.isTotallyRamified_iff_ramificationIndex_eq_finrank]

@[simp]
theorem isTotallyRamified_self : (self K).IsTotallyRamified := by
  rw [isTotallyRamified_iff_inertiaDegree_eq_one, inertiaDegree_self]

end Invariants

section RestrictScalars

variable (K : Type u) {F : Type v}
  [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Algebra K F] [ValuativeExtension K F] [Module.Finite K F]

/-- **Multiplicativity of the residue degree under restriction of scalars.** -/
@[simp]
theorem inertiaDegree_restrictScalars (c : FiniteExtensionClass F) :
    (c.restrictScalars K).inertiaDegree = TauCeti.inertiaDegree K F * c.inertiaDegree := by
  induction c using induction_on_localField with | h L =>
  let : Algebra K L := RingHom.toAlgebra ((algebraMap F L).comp (algebraMap K F))
  have : IsScalarTower K F L := IsScalarTower.of_algebraMap_eq' rfl
  have : Module.Finite K L := Module.Finite.trans F L
  have : ValuativeExtension K L :=
    ⟨fun {a b} ↦ by
      rw [IsScalarTower.algebraMap_apply K F L a, IsScalarTower.algebraMap_apply K F L b,
        ValuativeExtension.vle_iff_vle, ValuativeExtension.vle_iff_vle]⟩
  rw [restrictScalars_mk (F := F) K L, inertiaDegree_mk, inertiaDegree_mk,
    TauCeti.inertiaDegree_tower (K := K) (L := F) L]

/-- **Multiplicativity of the ramification index under restriction of scalars.** -/
@[simp]
theorem ramificationIndex_restrictScalars (c : FiniteExtensionClass F) :
    (c.restrictScalars K).ramificationIndex =
      TauCeti.ramificationIndex K F * c.ramificationIndex := by
  induction c using induction_on_localField with | h L =>
  let : Algebra K L := RingHom.toAlgebra ((algebraMap F L).comp (algebraMap K F))
  have : IsScalarTower K F L := IsScalarTower.of_algebraMap_eq' rfl
  have : Module.Finite K L := Module.Finite.trans F L
  have : ValuativeExtension K L :=
    ⟨fun {a b} ↦ by
      rw [IsScalarTower.algebraMap_apply K F L a, IsScalarTower.algebraMap_apply K F L b,
        ValuativeExtension.vle_iff_vle, ValuativeExtension.vle_iff_vle]⟩
  rw [restrictScalars_mk (F := F) K L, ramificationIndex_mk, ramificationIndex_mk,
    TauCeti.ramificationIndex_tower (K := K) (L := F) L]

theorem isUnramified_restrictScalars_iff (c : FiniteExtensionClass F) :
    (c.restrictScalars K).IsUnramified ↔ TauCeti.IsUnramified K F ∧ c.IsUnramified := by
  rw [isUnramified_iff_ramificationIndex_eq_one, isUnramified_iff_ramificationIndex_eq_one,
    ramificationIndex_restrictScalars, mul_eq_one,
    TauCeti.isUnramified_iff_ramificationIndex_eq_one]

theorem isTotallyRamified_restrictScalars_iff (c : FiniteExtensionClass F) :
    (c.restrictScalars K).IsTotallyRamified ↔
      TauCeti.IsTotallyRamified K F ∧ c.IsTotallyRamified := by
  rw [isTotallyRamified_iff_inertiaDegree_eq_one, isTotallyRamified_iff_inertiaDegree_eq_one,
    inertiaDegree_restrictScalars, mul_eq_one, TauCeti.isTotallyRamified_iff_inertiaDegree_eq_one]

end RestrictScalars

section Transport

/-- Transport of structure along a valuation-preserving ring isomorphism preserves the residue
degree of finite extension classes. -/
theorem inertiaDegree_mapEquiv_of_vle_iff {F₁ : Type u} {F₂ : Type v}
    [Field F₁] [ValuativeRel F₁] [TopologicalSpace F₁] [IsNonarchimedeanLocalField F₁]
    [Field F₂] [ValuativeRel F₂] [TopologicalSpace F₂] [IsNonarchimedeanLocalField F₂]
    (e : F₁ ≃+* F₂) (he : ∀ a b : F₁, e a ≤ᵥ e b ↔ a ≤ᵥ b)
    (c : FiniteExtensionClass F₁) :
    (mapEquiv e c).inertiaDegree = c.inertiaDegree := by
  induction c using induction_on_localField with | h L₁ =>
  obtain ⟨L₂, _, _, _, hL₂⟩ := exists_mk (mapEquiv e (mk F₁ L₁))
  let : ValuativeRel L₂ := algebraicExtensionValuativeRel F₂ L₂
  let : TopologicalSpace L₂ := algebraicExtensionNormedFieldTopology F₂ L₂
  have : IsNonarchimedeanLocalField L₂ := finiteExtension_isNonarchimedeanLocalField F₂ L₂
  have : ValuativeExtension F₂ L₂ := algebraicExtension_valuativeExtension F₂ L₂
  obtain ⟨φ, hφ⟩ := (mapEquiv_mk_eq_mk_iff e).1 hL₂
  rw [hL₂, inertiaDegree_mk, inertiaDegree_mk]
  exact (TauCeti.inertiaDegree_eq_of_vle_iff e he φ hφ).symm

/-- Transport of structure along a valuation-preserving ring isomorphism preserves the ramification
index of finite extension classes. -/
theorem ramificationIndex_mapEquiv_of_vle_iff {F₁ : Type u} {F₂ : Type v}
    [Field F₁] [ValuativeRel F₁] [TopologicalSpace F₁] [IsNonarchimedeanLocalField F₁]
    [Field F₂] [ValuativeRel F₂] [TopologicalSpace F₂] [IsNonarchimedeanLocalField F₂]
    (e : F₁ ≃+* F₂) (he : ∀ a b : F₁, e a ≤ᵥ e b ↔ a ≤ᵥ b)
    (c : FiniteExtensionClass F₁) :
    (mapEquiv e c).ramificationIndex = c.ramificationIndex := by
  induction c using induction_on_localField with | h L₁ =>
  obtain ⟨L₂, _, _, _, hL₂⟩ := exists_mk (mapEquiv e (mk F₁ L₁))
  let : ValuativeRel L₂ := algebraicExtensionValuativeRel F₂ L₂
  let : TopologicalSpace L₂ := algebraicExtensionNormedFieldTopology F₂ L₂
  have : IsNonarchimedeanLocalField L₂ := finiteExtension_isNonarchimedeanLocalField F₂ L₂
  have : ValuativeExtension F₂ L₂ := algebraicExtension_valuativeExtension F₂ L₂
  obtain ⟨φ, hφ⟩ := (mapEquiv_mk_eq_mk_iff e).1 hL₂
  rw [hL₂, ramificationIndex_mk, ramificationIndex_mk]
  exact (TauCeti.ramificationIndex_eq_of_vle_iff e he φ hφ).symm

theorem isUnramified_mapEquiv_iff_of_vle_iff {F₁ : Type u} {F₂ : Type v}
    [Field F₁] [ValuativeRel F₁] [TopologicalSpace F₁] [IsNonarchimedeanLocalField F₁]
    [Field F₂] [ValuativeRel F₂] [TopologicalSpace F₂] [IsNonarchimedeanLocalField F₂]
    (e : F₁ ≃+* F₂) (he : ∀ a b : F₁, e a ≤ᵥ e b ↔ a ≤ᵥ b)
    (c : FiniteExtensionClass F₁) :
    (mapEquiv e c).IsUnramified ↔ c.IsUnramified := by
  rw [isUnramified_iff_ramificationIndex_eq_one, isUnramified_iff_ramificationIndex_eq_one,
    ramificationIndex_mapEquiv_of_vle_iff e he]

theorem isTotallyRamified_mapEquiv_iff_of_vle_iff {F₁ : Type u} {F₂ : Type v}
    [Field F₁] [ValuativeRel F₁] [TopologicalSpace F₁] [IsNonarchimedeanLocalField F₁]
    [Field F₂] [ValuativeRel F₂] [TopologicalSpace F₂] [IsNonarchimedeanLocalField F₂]
    (e : F₁ ≃+* F₂) (he : ∀ a b : F₁, e a ≤ᵥ e b ↔ a ≤ᵥ b)
    (c : FiniteExtensionClass F₁) :
    (mapEquiv e c).IsTotallyRamified ↔ c.IsTotallyRamified := by
  rw [isTotallyRamified_iff_inertiaDegree_eq_one, isTotallyRamified_iff_inertiaDegree_eq_one,
    inertiaDegree_mapEquiv_of_vle_iff e he]

end Transport

section GaloisAction

variable {K : Type u} {F : Type v}
  [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Algebra K F] [ValuativeExtension K F]

@[simp]
theorem inertiaDegree_smul (τ : F ≃ₐ[K] F) (c : FiniteExtensionClass F) :
    (τ • c).inertiaDegree = c.inertiaDegree := by
  have := finite_of_valuativeExtension K F
  exact inertiaDegree_mapEquiv_of_vle_iff (τ : F ≃+* F)
    (fun _ _ ↦ (τ.toAlgHom : F →ₐ[K] F).valuativeExtension.vle_iff_vle) c

@[simp]
theorem ramificationIndex_smul (τ : F ≃ₐ[K] F) (c : FiniteExtensionClass F) :
    (τ • c).ramificationIndex = c.ramificationIndex := by
  have := finite_of_valuativeExtension K F
  exact ramificationIndex_mapEquiv_of_vle_iff (τ : F ≃+* F)
    (fun _ _ ↦ (τ.toAlgHom : F →ₐ[K] F).valuativeExtension.vle_iff_vle) c

@[simp]
theorem isUnramified_smul_iff (τ : F ≃ₐ[K] F) (c : FiniteExtensionClass F) :
    (τ • c).IsUnramified ↔ c.IsUnramified := by
  rw [isUnramified_iff_ramificationIndex_eq_one, isUnramified_iff_ramificationIndex_eq_one,
    ramificationIndex_smul]

@[simp]
theorem isTotallyRamified_smul_iff (τ : F ≃ₐ[K] F) (c : FiniteExtensionClass F) :
    (τ • c).IsTotallyRamified ↔ c.IsTotallyRamified := by
  rw [isTotallyRamified_iff_inertiaDegree_eq_one, isTotallyRamified_iff_inertiaDegree_eq_one,
    inertiaDegree_smul]

end GaloisAction

end TauCeti.FiniteExtensionClass

end

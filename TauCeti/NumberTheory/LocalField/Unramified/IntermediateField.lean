/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.MassFormula.Basic
public import TauCeti.NumberTheory.LocalField.Unramified.Factorization
public import TauCeti.NumberTheory.LocalField.Unramified.Maximal
import TauCeti.FieldTheory.IntermediateField.Map
import TauCeti.FieldTheory.IntermediateField.ScalarTower
import TauCeti.FieldTheory.IsSepClosed

/-!
# The unramified part of a finite subextension

For a finite subextension `L` of the separable closure of a nonarchimedean local field `K`,
the intersection of `L` with the maximal unramified extension is the canonical unramified
extension of degree `f(L/K)`. In particular, that canonical field is contained in `L`.
This identifies the unramified base over which extensions with a prescribed residue degree
are totally ramified, as needed in counting extensions by residue degree.

`IntermediateField.inertiaDegree` extends the residue degree to all subextensions, taking
value zero on infinite extensions. It uses the same local-field adapters and totalization as
`IntermediateField.discriminantExponent`. Its invariance under algebra equivalence includes
the infinite case, so residue degree can be used as a weight on isomorphism classes.

## Main definitions

* `IntermediateField.inertiaDegree`: the residue degree of a subextension of `SeparableClosure K`,
  extended by zero to infinite subextensions.
* `IntermediateField.equivTotallyRamifiedOfDegree`: the bijection between subextensions of
  `SeparableClosure K / K` containing an unramified extension `F` of degree `f(F / K) * e` and
  residue degree `f(F / K)` and `totallyRamifiedOfDegree F e`.

## Main results

* `IntermediateField.inertiaDegree_eq_of_algEquiv`: residue degree is an isomorphism invariant.
* `IntermediateField.isTotallyRamified_iff_inertiaDegree_eq_one`: a subextension is totally
  ramified exactly when its residue degree is one.
* `IntermediateField.unramifiedExtension_inertiaDegree_le`: `K_{f(L/K)} ≤ L` for finite `L`.
* `IntermediateField.inf_maximalUnramifiedExtension`: `L ∩ K^{ur} = K_{f(L/K)}` for finite `L`.
* `TauCeti.encard_finrank_and_inertiaDegree_eq`: the extended cardinality of subextensions of
  degree `f * e` and residue degree `f ≠ 0` equals `#σ_{K_f}(e)`.

## References

* J.-P. Serre, *Local Fields*, Chapter III, §5.
* J. Neukirch, *Algebraic Number Theory*, Chapter II, §7.
-/

public section
noncomputable section

open ValuativeRel TauCeti

namespace IntermediateField

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

open Classical in
/-- The residue degree of a subextension of `SeparableClosure K`, using the canonical
local-field structures when the extension is finite, and zero otherwise. -/
def inertiaDegree (L : IntermediateField K (SeparableClosure K)) : ℕ :=
  if _ : Module.Finite K L then
    letI := finiteIntermediateFieldValuativeRel K (SeparableClosure K) L
    letI := finiteIntermediateFieldTopology K (SeparableClosure K) L
    haveI := finiteIntermediateField_isNonarchimedeanLocalField K (SeparableClosure K) L
    haveI := finiteIntermediateField_valuativeExtension K (SeparableClosure K) L
    TauCeti.inertiaDegree K L
  else 0

/-- On a finite subextension, the totalized residue degree agrees with the residue degree
for its canonical local-field structure. -/
theorem inertiaDegree_eq (L : IntermediateField K (SeparableClosure K))
    [hfin : Module.Finite K L] :
    L.inertiaDegree =
      (letI := finiteIntermediateFieldValuativeRel K (SeparableClosure K) L
      letI := finiteIntermediateFieldTopology K (SeparableClosure K) L
      haveI := finiteIntermediateField_isNonarchimedeanLocalField K (SeparableClosure K) L
      haveI := finiteIntermediateField_valuativeExtension K (SeparableClosure K) L
      TauCeti.inertiaDegree K L) :=
  dite_eq_left hfin

/-- On an infinite subextension the totalized residue degree is zero. -/
theorem inertiaDegree_of_not_finite {L : IntermediateField K (SeparableClosure K)}
    (h : ¬ Module.Finite K L) : L.inertiaDegree = 0 :=
  dite_eq_right h

/-- The residue degree of a finite subextension is positive. -/
theorem inertiaDegree_pos (L : IntermediateField K (SeparableClosure K))
    [Module.Finite K L] : 0 < L.inertiaDegree := by
  rw [inertiaDegree_eq]
  let _ := finiteIntermediateFieldValuativeRel K (SeparableClosure K) L
  let _ := finiteIntermediateFieldTopology K (SeparableClosure K) L
  have := finiteIntermediateField_isNonarchimedeanLocalField K (SeparableClosure K) L
  have := finiteIntermediateField_valuativeExtension K (SeparableClosure K) L
  exact TauCeti.inertiaDegree_pos

/-- The residue degree vanishes exactly on infinite subextensions. -/
@[simp]
theorem inertiaDegree_eq_zero_iff (L : IntermediateField K (SeparableClosure K)) :
    L.inertiaDegree = 0 ↔ ¬ Module.Finite K L := by
  by_cases h : Module.Finite K L
  · have := h
    simp [h, (inertiaDegree_pos L).ne']
  · simp [h, inertiaDegree_of_not_finite h]

/-- The residue degree is invariant under `K`-algebra equivalence, including the infinite case. -/
theorem inertiaDegree_eq_of_algEquiv {L M : IntermediateField K (SeparableClosure K)}
    (e : L ≃ₐ[K] M) : L.inertiaDegree = M.inertiaDegree := by
  by_cases hL : Module.Finite K L
  · have : Module.Finite K M := Module.Finite.equiv e.toLinearEquiv
    rw [inertiaDegree_eq, inertiaDegree_eq]
    let _ := finiteIntermediateFieldValuativeRel K (SeparableClosure K) L
    let _ := finiteIntermediateFieldTopology K (SeparableClosure K) L
    have := finiteIntermediateField_isNonarchimedeanLocalField K (SeparableClosure K) L
    have := finiteIntermediateField_valuativeExtension K (SeparableClosure K) L
    let _ := finiteIntermediateFieldValuativeRel K (SeparableClosure K) M
    let _ := finiteIntermediateFieldTopology K (SeparableClosure K) M
    have := finiteIntermediateField_isNonarchimedeanLocalField K (SeparableClosure K) M
    have := finiteIntermediateField_valuativeExtension K (SeparableClosure K) M
    exact TauCeti.inertiaDegree_eq_of_algEquiv K L M e
  · rw [inertiaDegree_of_not_finite hL, inertiaDegree_of_not_finite
      fun h ↦ hL (Module.Finite.equiv e.symm.toLinearEquiv)]

/-- A subextension is totally ramified exactly when its totalized residue degree is one; no
finiteness hypothesis is needed, since an infinite subextension has residue degree zero. -/
theorem isTotallyRamified_iff_inertiaDegree_eq_one (L : IntermediateField K (SeparableClosure K)) :
    L.IsTotallyRamified ↔ L.inertiaDegree = 1 := by
  by_cases h : Module.Finite K L
  · rw [L.isTotallyRamified_iff, inertiaDegree_eq]
    let _ := finiteIntermediateFieldValuativeRel K (SeparableClosure K) L
    let _ := finiteIntermediateFieldTopology K (SeparableClosure K) L
    have := finiteIntermediateField_isNonarchimedeanLocalField K (SeparableClosure K) L
    have := finiteIntermediateField_valuativeExtension K (SeparableClosure K) L
    exact TauCeti.isTotallyRamified_iff_inertiaDegree_eq_one K L
  · rw [inertiaDegree_of_not_finite h]
    exact iff_of_false (fun h' ↦ h h'.finite) zero_ne_one

/-- The bottom subextension has residue degree one. -/
@[simp]
theorem inertiaDegree_bot :
    (⊥ : IntermediateField K (SeparableClosure K)).inertiaDegree = 1 := by
  rw [inertiaDegree_eq]
  let _ := finiteIntermediateFieldValuativeRel K (SeparableClosure K) ⊥
  let _ := finiteIntermediateFieldTopology K (SeparableClosure K) ⊥
  have := finiteIntermediateField_isNonarchimedeanLocalField K (SeparableClosure K) ⊥
  have := finiteIntermediateField_valuativeExtension K (SeparableClosure K) ⊥
  have h := ramificationIndex_mul_inertiaDegree K (⊥ : IntermediateField K (SeparableClosure K))
  rw [IntermediateField.finrank_bot] at h
  exact Nat.eq_one_of_mul_eq_one_left h

/-- The canonical unramified extension of degree `f(L/K)` is contained in every finite
subextension `L`. -/
theorem unramifiedExtension_inertiaDegree_le (L : IntermediateField K (SeparableClosure K))
    [Module.Finite K L] :
    unramifiedExtension K (SeparableClosure K) L.inertiaDegree ≤ L := by
  rw [inertiaDegree_eq]
  let _ := finiteIntermediateFieldValuativeRel K (SeparableClosure K) L
  let _ := finiteIntermediateFieldTopology K (SeparableClosure K) L
  have := finiteIntermediateField_isNonarchimedeanLocalField K (SeparableClosure K) L
  have := finiteIntermediateField_valuativeExtension K (SeparableClosure K) L
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_natCard_pow_inertiaDegree_sub_one K L
  rw [unramifiedExtension_eq_adjoin_simple TauCeti.inertiaDegree_pos.ne'
    (hζ.map_of_injective L.val.injective), adjoin_simple_le_iff]
  exact ζ.2

/-- The unramified part of a finite subextension is the canonical unramified extension of
its residue degree. No normality hypothesis on `L/K` is required. -/
@[simp]
theorem inf_maximalUnramifiedExtension (L : IntermediateField K (SeparableClosure K))
    [Module.Finite K L] :
    L ⊓ maximalUnramifiedExtension K (SeparableClosure K) =
      unramifiedExtension K (SeparableClosure K) L.inertiaDegree := by
  apply le_antisymm
  · let E := L ⊓ maximalUnramifiedExtension K (SeparableClosure K)
    have hEL : E ≤ L := inf_le_left
    let _ : Algebra E L := (inclusion hEL).toAlgebra
    have : IsScalarTower K E L := .of_algebraMap_eq fun _ ↦ rfl
    have : Module.Finite K E := Module.Finite.of_injective (inclusion hEL).toLinearMap
      (inclusion_injective hEL)
    let _ := finiteIntermediateFieldValuativeRel K (SeparableClosure K) E
    let _ := finiteIntermediateFieldTopology K (SeparableClosure K) E
    have := finiteIntermediateField_isNonarchimedeanLocalField K (SeparableClosure K) E
    have := finiteIntermediateField_valuativeExtension K (SeparableClosure K) E
    let _ := finiteIntermediateFieldValuativeRel K (SeparableClosure K) L
    let _ := finiteIntermediateFieldTopology K (SeparableClosure K) L
    have := finiteIntermediateField_isNonarchimedeanLocalField K (SeparableClosure K) L
    have := finiteIntermediateField_valuativeExtension K (SeparableClosure K) L
    have : ValuativeExtension E L := (inclusion hEL).valuativeExtension
    have : IsUnramified K E := (E.le_maximalUnramifiedExtension_iff).1 inf_le_right
    calc
      L ⊓ maximalUnramifiedExtension K (SeparableClosure K) =
          unramifiedExtension K (SeparableClosure K) (Module.finrank K E) :=
        E.eq_unramifiedExtension_finrank
      _ ≤ unramifiedExtension K (SeparableClosure K) L.inertiaDegree := by
        rw [inertiaDegree_eq, ← IsUnramified.inertiaDegree_eq_finrank (K := K) (L := E)]
        exact unramifiedExtension_le_of_dvd TauCeti.inertiaDegree_pos.ne'
          (Dvd.intro _ (TauCeti.inertiaDegree_tower (K := K) (L := E) L).symm)
  · exact le_inf (unramifiedExtension_inertiaDegree_le L)
      (unramifiedExtension_le_maximalUnramifiedExtension K (SeparableClosure K) _)

section Transport

variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Algebra K F] [ValuativeExtension K F] [Algebra F (SeparableClosure K)]
  [IsScalarTower K F (SeparableClosure K)] (Φ : SeparableClosure F ≃ₐ[F] SeparableClosure K)

/-- Over a finite base extension `F / K`, the residue degree of `E.restrictScalars K` over `K` is
`f(F / K)` times that of the transported intermediate field over `F`. -/
theorem inertiaDegree_restrictScalars_eq_mul (E : IntermediateField F (SeparableClosure K))
    (hE : Module.Finite F (E.map Φ.symm.toAlgHom)) :
    (E.restrictScalars K).inertiaDegree =
      TauCeti.inertiaDegree K F * (E.map Φ.symm.toAlgHom).inertiaDegree := by
  let e₁ := restrictScalarsAlgEquiv K E
  let e₂ : E ≃ₐ[F] E.map Φ.symm.toAlgHom := intermediateFieldMap Φ.symm E
  have : Module.Finite K F := finite_of_valuativeExtension K F
  have : Module.Finite F E := Module.Finite.equiv e₂.symm.toLinearEquiv
  have : Module.Finite K E := Module.Finite.trans F E
  have : Module.Finite K (E.restrictScalars K) := Module.Finite.equiv e₁.symm.toLinearEquiv
  rw [IntermediateField.inertiaDegree_eq, IntermediateField.inertiaDegree_eq]
  let _ := finiteIntermediateFieldValuativeRel K (SeparableClosure K) (E.restrictScalars K)
  let _ := finiteIntermediateFieldTopology K (SeparableClosure K) (E.restrictScalars K)
  have := finiteIntermediateField_isNonarchimedeanLocalField K (SeparableClosure K)
    (E.restrictScalars K)
  have := finiteIntermediateField_valuativeExtension K (SeparableClosure K) (E.restrictScalars K)
  let _ := finiteIntermediateFieldValuativeRel F (SeparableClosure F) (E.map Φ.symm.toAlgHom)
  let _ := finiteIntermediateFieldTopology F (SeparableClosure F) (E.map Φ.symm.toAlgHom)
  have := finiteIntermediateField_isNonarchimedeanLocalField F (SeparableClosure F)
    (E.map Φ.symm.toAlgHom)
  have := finiteIntermediateField_valuativeExtension F (SeparableClosure F) (E.map Φ.symm.toAlgHom)
  let _ := finiteIntermediateFieldValuativeRel F (SeparableClosure K) E
  let _ := finiteIntermediateFieldTopology F (SeparableClosure K) E
  have := finiteIntermediateField_isNonarchimedeanLocalField F (SeparableClosure K) E
  have := finiteIntermediateField_valuativeExtension F (SeparableClosure K) E
  have : ValuativeExtension K E := ValuativeExtension.trans K F E
  rw [TauCeti.inertiaDegree_eq_of_algEquiv K _ E e₁, TauCeti.inertiaDegree_tower K F E,
    TauCeti.inertiaDegree_eq_of_algEquiv F E _ e₂]

/-- Over a finite base extension `F / K`, the transported intermediate field lies in `σ_F(e)` if
and only if `E.restrictScalars K` has degree `[F : K] * e` and residue degree `f(F / K)` over
`K`. -/
theorem map_mem_totallyRamifiedOfDegree_iff (E : IntermediateField F (SeparableClosure K))
    (e : ℕ) :
    E.map Φ.symm.toAlgHom ∈ totallyRamifiedOfDegree F e ↔
      Module.finrank K (E.restrictScalars K) = Module.finrank K F * e ∧
        (E.restrictScalars K).inertiaDegree = TauCeti.inertiaDegree K F := by
  let e₁ := restrictScalarsAlgEquiv K E
  let e₂ : E ≃ₐ[F] E.map Φ.symm.toAlgHom := intermediateFieldMap Φ.symm E
  have : Module.Finite K F := finite_of_valuativeExtension K F
  have hrank : Module.finrank K (E.restrictScalars K) =
      Module.finrank K F * Module.finrank F (E.map Φ.symm.toAlgHom) := by
    rw [e₁.toLinearEquiv.finrank_eq, ← e₂.toLinearEquiv.finrank_eq, Module.finrank_mul_finrank]
  have hf : 0 < TauCeti.inertiaDegree K F := TauCeti.inertiaDegree_pos
  rw [mem_totallyRamifiedOfDegree_iff, hrank,
    IntermediateField.isTotallyRamified_iff_inertiaDegree_eq_one]
  constructor
  · rintro ⟨he, hM⟩
    have : Module.Finite F (E.map Φ.symm.toAlgHom) := by
      by_contra h
      rw [← inertiaDegree_eq_zero_iff] at h
      omega
    rw [he, inertiaDegree_restrictScalars_eq_mul F Φ E this, hM, mul_one]
    exact ⟨rfl, rfl⟩
  · rintro ⟨he, hi⟩
    have : Module.Finite K (E.restrictScalars K) := by
      by_contra h
      rw [← inertiaDegree_eq_zero_iff] at h
      omega
    have : Module.Finite K E := Module.Finite.equiv e₁.toLinearEquiv
    have : Module.Finite F E := Module.Finite.of_restrictScalars_finite K F E
    have : Module.Finite F (E.map Φ.symm.toAlgHom) := Module.Finite.equiv e₂.toLinearEquiv
    rw [inertiaDegree_restrictScalars_eq_mul F Φ E this] at hi
    exact ⟨Nat.eq_of_mul_eq_mul_left Module.finrank_pos he,
      Nat.eq_of_mul_eq_mul_left hf (hi.trans (mul_one _).symm)⟩

variable [IsUnramified K F]

/-- Over an unramified extension `F / K` inside `SeparableClosure K`, an `F`-algebra equivalence
`Φ : SeparableClosure F ≃ₐ[F] SeparableClosure K` identifies the subextensions of
`SeparableClosure K / K` containing `F` of degree `f(F / K) * e` and residue degree `f(F / K)`
with `totallyRamifiedOfDegree F e`. -/
def equivTotallyRamifiedOfDegree (e : ℕ) :
    {L : IntermediateField K (SeparableClosure K) //
      (∀ x : F, algebraMap F (SeparableClosure K) x ∈ L) ∧
        Module.finrank K L = TauCeti.inertiaDegree K F * e ∧
          L.inertiaDegree = TauCeti.inertiaDegree K F} ≃
      totallyRamifiedOfDegree F e :=
  let ρ : IntermediateField F (SeparableClosure K) ≃
      {L : IntermediateField K (SeparableClosure K) //
        ∀ x : F, algebraMap F (SeparableClosure K) x ∈ L} :=
    { toFun E := ⟨E.restrictScalars K, E.algebraMap_mem⟩
      invFun L := L.1.toSubfield.toIntermediateField L.2
      left_inv _ := rfl
      right_inv _ := rfl }
  have hfr : Module.finrank K F = TauCeti.inertiaDegree K F :=
    IsUnramified.inertiaDegree_eq_finrank.symm
  (Equiv.subtypeSubtypeEquivSubtypeInter _ _).symm.trans
    (Equiv.subtypeEquiv (ρ.symm.trans (orderIsoMapComap Φ.symm).toEquiv) fun L ↦ by
      rw [Equiv.trans_apply, OrderIso.coe_toEquiv, orderIsoMapComap_apply,
        map_mem_totallyRamifiedOfDegree_iff F Φ (ρ.symm L) e, hfr]
      rfl)

/-- `equivTotallyRamifiedOfDegree` acts by viewing `L` over `F` and transporting along `Φ.symm`. -/
@[simp]
theorem coe_equivTotallyRamifiedOfDegree_apply {e : ℕ}
    (L : {L : IntermediateField K (SeparableClosure K) //
      (∀ x : F, algebraMap F (SeparableClosure K) x ∈ L) ∧
        Module.finrank K L = TauCeti.inertiaDegree K F * e ∧
          L.inertiaDegree = TauCeti.inertiaDegree K F}) :
    (equivTotallyRamifiedOfDegree F Φ e L : IntermediateField F (SeparableClosure F)) =
      (L.1.toSubfield.toIntermediateField L.2.1).map Φ.symm.toAlgHom := by
  simp only [equivTotallyRamifiedOfDegree, Equiv.trans_apply, Equiv.subtypeEquiv_apply,
    OrderIso.coe_toEquiv, orderIsoMapComap_apply]
  rfl

/-- The inverse of `equivTotallyRamifiedOfDegree` pulls back along `Φ.symm` and restricts scalars
to `K`. -/
@[simp]
theorem coe_equivTotallyRamifiedOfDegree_symm_apply {e : ℕ} (M : totallyRamifiedOfDegree F e) :
    ((equivTotallyRamifiedOfDegree F Φ e).symm M : IntermediateField K (SeparableClosure K)) =
      (M.1.comap Φ.symm.toAlgHom).restrictScalars K := by
  simp only [equivTotallyRamifiedOfDegree, Equiv.symm_trans_apply, Equiv.subtypeEquiv_symm,
    Equiv.subtypeEquiv_apply, Equiv.symm_symm]
  exact congrArg (restrictScalars K) (orderIsoMapComap_symm_apply Φ.symm M.1)

end Transport

/-- **Tower decomposition of fixed-residue-degree extensions.** For `f ≠ 0`, the subextensions of
`SeparableClosure K / K` of degree `f * e` and residue degree `f` have the same extended
cardinality as `totallyRamifiedOfDegree K_f e`, where `K_f` is the canonical unramified extension
of degree `f` equipped with any compatible local-field structure. -/
theorem _root_.TauCeti.encard_finrank_and_inertiaDegree_eq {f : ℕ} (hf : f ≠ 0) (e : ℕ)
    [ValuativeRel (unramifiedExtension K (SeparableClosure K) f)]
    [TopologicalSpace (unramifiedExtension K (SeparableClosure K) f)]
    [IsNonarchimedeanLocalField (unramifiedExtension K (SeparableClosure K) f)]
    [ValuativeExtension K (unramifiedExtension K (SeparableClosure K) f)] :
    {L : IntermediateField K (SeparableClosure K) |
      Module.finrank K L = f * e ∧ L.inertiaDegree = f}.encard =
      (totallyRamifiedOfDegree (unramifiedExtension K (SeparableClosure K) f) e).encard := by
  have : IsUnramified K (unramifiedExtension K (SeparableClosure K) f) :=
    isUnramified_unramifiedExtension
  have hUf : TauCeti.inertiaDegree K (unramifiedExtension K (SeparableClosure K) f) = f := by
    rw [IsUnramified.inertiaDegree_eq_finrank, finrank_unramifiedExtension hf]
  have := isSepClosure_tower_top K (unramifiedExtension K (SeparableClosure K) f)
    (SeparableClosure K)
  let Φ := IsSepClosure.equiv (unramifiedExtension K (SeparableClosure K) f)
    (SeparableClosure (unramifiedExtension K (SeparableClosure K) f)) (SeparableClosure K)
  have hle : ∀ {L : IntermediateField K (SeparableClosure K)}, L.inertiaDegree = f →
      unramifiedExtension K (SeparableClosure K) f ≤ L := by
    intro L hL
    have : Module.Finite K L := by
      by_contra h
      rw [← inertiaDegree_eq_zero_iff] at h
      omega
    simpa [hL] using L.unramifiedExtension_inertiaDegree_le
  let τ : {L : IntermediateField K (SeparableClosure K) //
      Module.finrank K L = f * e ∧ L.inertiaDegree = f} ≃
      {L : IntermediateField K (SeparableClosure K) //
        (∀ x : unramifiedExtension K (SeparableClosure K) f,
            algebraMap (unramifiedExtension K (SeparableClosure K) f) (SeparableClosure K) x ∈ L) ∧
          Module.finrank K L =
            TauCeti.inertiaDegree K (unramifiedExtension K (SeparableClosure K) f) * e ∧
            L.inertiaDegree =
              TauCeti.inertiaDegree K (unramifiedExtension K (SeparableClosure K) f)} :=
    Equiv.subtypeEquivRight fun L ↦ by
      rw [hUf]
      exact ⟨fun h ↦ ⟨fun x ↦ hle h.2 x.2, h⟩, And.right⟩
  exact Set.encard_congr
    (τ.trans (equivTotallyRamifiedOfDegree (unramifiedExtension K (SeparableClosure K) f) Φ e))

end IntermediateField

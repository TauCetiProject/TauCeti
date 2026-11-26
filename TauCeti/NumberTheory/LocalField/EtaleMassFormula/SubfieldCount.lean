/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.MassFormula.Main
public import TauCeti.NumberTheory.LocalField.Unramified.IntermediateField
import TauCeti.FieldTheory.IntermediateField.Map
import TauCeti.FieldTheory.IsSepClosed
import TauCeti.NumberTheory.LocalField.Discriminant.Tower

/-!
# Subextensions of given degree and residue degree, weighted by discriminant

Let `K` be a nonarchimedean local field with `q` residue classes. For `f ≥ 1` and `e ≥ 0`, the
subextensions `L` of `SeparableClosure K` of degree `f * e` and residue degree `f` satisfy
`∑_L q ^ (-d(L)) = e · q ^ (-f(e - 1))`, where `d(L)` is the discriminant exponent of `L / K`.
This is the count of finite extensions of `K` by residue degree from which the mass of the
transitive Galois sets with a given splitting symbol is computed.

It is Serre's mass formula over the unramified extension `K_f` of degree `f`. Every such `L`
contains `K_f` (`IntermediateField.unramifiedExtension_inertiaDegree_le`) and is totally ramified
of degree `e` over it; conversely every totally ramified extension of `K_f` of degree `e` inside
`SeparableClosure K` has degree `f * e` and residue degree `f` over `K`. Since `SeparableClosure K`
is a separable closure of `K_f`, `IsSepClosure.equiv` identifies these extensions with Serre's
`σ_{K_f}(e)`, the totally ramified subextensions of degree `e` of `SeparableClosure K_f`. The
residue field of `K_f` has `q ^ f` elements, and the tower law for discriminants with
`d(K_f / K) = 0` gives `d(L / K) = f · d(L / K_f)`; the wild exponent `c = d(L / K_f) - e + 1`
then turns Serre's `∑ (q ^ f) ^ (-c) = e` into the formula above.

## Main results

* `TauCeti.map_mem_totallyRamifiedOfDegree_iff`: over a finite extension `F / K`, transporting an
  intermediate field of `SeparableClosure K / F` to `SeparableClosure F` lands in `σ_F(e)`
  precisely when its restriction of scalars to `K` has degree `[F : K] * e` and residue degree
  `f(F / K)`.
* `TauCeti.one_div_natCard_residueField_pow_discriminantExponent_restrictScalars`: the discriminant
  weight `q ^ (-d)` over `K` factors into the wild-exponent weight `(q ^ f) ^ (-c)` over `F` times
  `q ^ (-f(e - 1))`.
* `TauCeti.tsum_inertiaDegree_eq`: the subextensions of degree `f * e` and residue degree `f`
  satisfy `∑_L q ^ (-d(L)) = e · q ^ (-f(e - 1))`.
* `TauCeti.finite_setOf_finrank_eq_and_inertiaDegree_eq`: if `e` is nonzero in `K`, there are
  finitely many such subextensions, by Serre's finiteness of `σ_{K_f}(e)`.

## References

* M. Bhargava, *Mass formulae for extensions of local fields, and conjectures on the density of
  number field discriminants*, IMRN **2007**, rnm052, §2.
* J.-P. Serre, *Une « formule de masse » pour les extensions totalement ramifiées de degré donné
  d'un corps local*, C. R. Acad. Sci. Paris Sér. A **286** (1978), 1031–1036, Théorème 1.
-/

public section
noncomputable section

open ValuativeRel IntermediateField
open scoped ENNReal

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-! ### Transport from `SeparableClosure K` to the separable closure of a finite base

Throughout, `F` is a finite extension of `K` with an embedding into `SeparableClosure K` (assumed
unramified over `K` once discriminants enter), and `Φ` identifies the separable closure of `F` with
`SeparableClosure K` over `F`. An intermediate field `E` of `SeparableClosure K / F` is then read
over `K` as `E.restrictScalars K`, and over `F` inside the separable closure of `F` as its image
under `Φ.symm`. -/

section Transport

variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Algebra K F] [ValuativeExtension K F] [Algebra F (SeparableClosure K)]
  [IsScalarTower K F (SeparableClosure K)] (Φ : SeparableClosure F ≃ₐ[F] SeparableClosure K)
  (E : IntermediateField F (SeparableClosure K))

/-- Over a finite extension `F / K`, the residue degree of `E.restrictScalars K` over `K` is
`f(F / K)` times that of the transported intermediate field over `F`, by multiplicativity of
residue degrees in the tower `K ⊆ F ⊆ E`. -/
private theorem inertiaDegree_restrictScalars
    (hE : Module.Finite F (E.map Φ.symm.toAlgHom)) :
    (E.restrictScalars K).inertiaDegree =
      inertiaDegree K F * (E.map Φ.symm.toAlgHom).inertiaDegree := by
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

/-- Over a finite extension `F / K`, the transported intermediate field lies in `σ_F(e)` exactly
when `E.restrictScalars K` has degree `[F : K] * e` and residue degree `f(F / K)` over `K`. -/
theorem map_mem_totallyRamifiedOfDegree_iff (e : ℕ) :
    E.map Φ.symm.toAlgHom ∈ totallyRamifiedOfDegree F e ↔
      Module.finrank K (E.restrictScalars K) = Module.finrank K F * e ∧
        (E.restrictScalars K).inertiaDegree = inertiaDegree K F := by
  let e₁ := restrictScalarsAlgEquiv K E
  let e₂ : E ≃ₐ[F] E.map Φ.symm.toAlgHom := intermediateFieldMap Φ.symm E
  have : Module.Finite K F := finite_of_valuativeExtension K F
  have hrank : Module.finrank K (E.restrictScalars K) =
      Module.finrank K F * Module.finrank F (E.map Φ.symm.toAlgHom) := by
    rw [e₁.toLinearEquiv.finrank_eq, ← e₂.toLinearEquiv.finrank_eq, Module.finrank_mul_finrank]
  have hf : 0 < inertiaDegree K F := inertiaDegree_pos
  rw [mem_totallyRamifiedOfDegree_iff, hrank,
    IntermediateField.isTotallyRamified_iff_inertiaDegree_eq_one]
  constructor
  · rintro ⟨he, hM⟩
    have : Module.Finite F (E.map Φ.symm.toAlgHom) := by
      by_contra h
      rw [← inertiaDegree_eq_zero_iff] at h
      omega
    rw [he, inertiaDegree_restrictScalars F Φ E this, hM, mul_one]
    exact ⟨rfl, rfl⟩
  · rintro ⟨he, hi⟩
    -- A subextension of positive residue degree is finite.
    have : Module.Finite K (E.restrictScalars K) := by
      by_contra h
      rw [← inertiaDegree_eq_zero_iff] at h
      omega
    have : Module.Finite K E := Module.Finite.equiv e₁.toLinearEquiv
    have : Module.Finite F E := Module.Finite.of_restrictScalars_finite K F E
    have : Module.Finite F (E.map Φ.symm.toAlgHom) := Module.Finite.equiv e₂.toLinearEquiv
    rw [inertiaDegree_restrictScalars F Φ E this] at hi
    exact ⟨Nat.eq_of_mul_eq_mul_left Module.finrank_pos he,
      Nat.eq_of_mul_eq_mul_left hf (hi.trans (mul_one _).symm)⟩

/-- Over a finite extension `F / K`, the intermediate fields of `SeparableClosure K` containing `F`,
of degree `[F : K] * e` and residue degree `f(F / K)` over `K`, correspond to `σ_F(e)`: read them
over `F` and transport them along `Φ`. -/
private def subtypeEquivTotallyRamifiedOfDegree (e : ℕ) :
    {L : IntermediateField K (SeparableClosure K) //
        (∀ x : F, algebraMap F (SeparableClosure K) x ∈ L) ∧
          Module.finrank K L = Module.finrank K F * e ∧ L.inertiaDegree = inertiaDegree K F} ≃
      totallyRamifiedOfDegree F e :=
  (Equiv.subtypeSubtypeEquivSubtypeInter _ _).symm.trans
    (Equiv.subtypeEquiv ((restrictScalarsOrderIso K).symm.trans
        (orderIsoMapComap Φ.symm)).toEquiv fun L ↦ by
      rw [OrderIso.coe_toEquiv, OrderIso.trans_apply, orderIsoMapComap_apply,
        map_mem_totallyRamifiedOfDegree_iff F Φ _ e, restrictScalars_restrictScalarsOrderIso_symm])

variable [IsUnramified K F]

/-- Over an unramified base `F`, the discriminant exponent of `E.restrictScalars K` over `K` is
`f(F / K)` times that of the transported intermediate field over `F`, since `d(F / K) = 0` in the
tower law for discriminants. -/
private theorem discriminantExponent_restrictScalars
    (hE : Module.Finite F (E.map Φ.symm.toAlgHom)) :
    (E.restrictScalars K).discriminantExponent =
      inertiaDegree K F * (E.map Φ.symm.toAlgHom).discriminantExponent := by
  let e₁ := restrictScalarsAlgEquiv K E
  let e₂ : E ≃ₐ[F] E.map Φ.symm.toAlgHom := intermediateFieldMap Φ.symm E
  have : Module.Finite K F := finite_of_valuativeExtension K F
  have : Module.Finite F E := Module.Finite.equiv e₂.symm.toLinearEquiv
  have : Module.Finite K E := Module.Finite.trans F E
  have : Module.Finite K (E.restrictScalars K) := Module.Finite.equiv e₁.symm.toLinearEquiv
  rw [IntermediateField.discriminantExponent_eq, IntermediateField.discriminantExponent_eq]
  -- The local-field structures: `E.restrictScalars K` over `K`, the transported field over `F`,
  -- and `E` itself over `F`, which is also an extension of `K` through `F`.
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
  have : Algebra.IsSeparable K F :=
    Algebra.isSeparable_tower_bot_of_isSeparable K F (SeparableClosure K)
  have : Algebra.IsSeparable K E :=
    Algebra.isSeparable_tower_bot_of_isSeparable K E (SeparableClosure K)
  have : Algebra.IsSeparable F (SeparableClosure K) :=
    Algebra.isSeparable_tower_top_of_isSeparable K F (SeparableClosure K)
  have : Algebra.IsSeparable F E :=
    Algebra.isSeparable_tower_bot_of_isSeparable F E (SeparableClosure K)
  rw [TauCeti.discriminantExponent_eq_of_algEquiv K _ E e₁]
  convert TauCeti.discriminantExponent_tower K F E using 1
  rw [(discriminantExponent_eq_zero_iff K F).2 ‹_›, mul_zero, zero_add,
    TauCeti.discriminantExponent_eq_of_algEquiv F E _ e₂]

/-- For `E` whose transport lies in `σ_F(e)`, the weight `q ^ (-d)` of `E.restrictScalars K`
splits as `(q ^ f) ^ (-c) · q ^ (-f(e - 1))`, where `f = f(F / K)`, `q ^ f` is the residue
cardinality of `F` and `c` is the wild exponent of the transport over `F`: indeed
`d(E / K) = f · d(E / F)` and `d(E / F) = c + e - 1`. -/
theorem one_div_natCard_residueField_pow_discriminantExponent_restrictScalars {e : ℕ}
    (hE : E.map Φ.symm.toAlgHom ∈ totallyRamifiedOfDegree F e) :
    1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (E.restrictScalars K).discriminantExponent =
      1 / (Nat.card 𝓀[F] : ℝ≥0∞) ^ (E.map Φ.symm.toAlgHom).wildExponent *
        (1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (inertiaDegree K F * (e - 1))) := by
  have he : e ≠ 0 := by
    rintro rfl
    simp at hE
  have hc := IntermediateField.wildExponent_add_eq_discriminantExponent_add_one hE
  have hd := discriminantExponent_restrictScalars F Φ E
    (mem_totallyRamifiedOfDegree_iff.1 hE).2.finite
  have hdc : (E.map Φ.symm.toAlgHom).discriminantExponent =
      (E.map Φ.symm.toAlgHom).wildExponent + (e - 1) := by
    omega
  rw [hd, natCard_residueField K F, Nat.cast_pow, hdc]
  simp only [one_div, ← pow_mul, mul_add, pow_add]
  exact ENNReal.mul_inv (.inr (by simp)) (.inl (by simp))

/-- **Serre's mass formula over an unramified base, read over `K`**: for `F` unramified over `K`
with residue degree `f`, the subextensions of `SeparableClosure K` containing `F`, of degree
`f * e` and residue degree `f` over `K`, satisfy `∑_L q ^ (-d(L)) = e · q ^ (-f(e - 1))`. -/
private theorem tsum_one_div_natCard_residueField_pow_discriminantExponent_eq (e : ℕ) :
    ∑' L : {L : IntermediateField K (SeparableClosure K) //
        (∀ x : F, algebraMap F (SeparableClosure K) x ∈ L) ∧
          Module.finrank K L = Module.finrank K F * e ∧ L.inertiaDegree = inertiaDegree K F},
      1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ L.val.discriminantExponent =
      e / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (inertiaDegree K F * (e - 1)) := by
  have := isSepClosure_tower_top K F (SeparableClosure K)
  let Φ := IsSepClosure.equiv F (SeparableClosure F) (SeparableClosure K)
  let ε := subtypeEquivTotallyRamifiedOfDegree F Φ e
  have hw (L) : 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ L.val.discriminantExponent =
      1 / (Nat.card 𝓀[F] : ℝ≥0∞) ^ (ε L).val.wildExponent *
        (1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (inertiaDegree K F * (e - 1))) := by
    let ρ := restrictScalarsOrderIso K (L' := F) (L := SeparableClosure K)
    have hε : (ε L).val = (ρ.symm ⟨L.val, L.property.1⟩).map Φ.symm.toAlgHom
        := orderIsoMapComap_apply _ _
    have hM := (ε L).property
    rw [hε] at hM ⊢
    have h := one_div_natCard_residueField_pow_discriminantExponent_restrictScalars F Φ
      (ρ.symm ⟨L.val, L.property.1⟩) hM
    rwa [restrictScalars_restrictScalarsOrderIso_symm] at h
  calc _ = ∑' L, 1 / (Nat.card 𝓀[F] : ℝ≥0∞) ^ (ε L).val.wildExponent *
        (1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (inertiaDegree K F * (e - 1))) := tsum_congr hw
    _ = (∑' M : totallyRamifiedOfDegree F e, 1 / (Nat.card 𝓀[F] : ℝ≥0∞) ^ M.val.wildExponent) *
        (1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (inertiaDegree K F * (e - 1))) := by
      rw [ε.tsum_eq (fun M ↦ 1 / (Nat.card 𝓀[F] : ℝ≥0∞) ^ M.val.wildExponent *
        (1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (inertiaDegree K F * (e - 1)))), ENNReal.tsum_mul_right]
    _ = _ := by rw [tsum_one_div_natCard_residueField_pow_wildExponent, mul_one_div]

end Transport

/-- The subextensions of degree `f * e` and residue degree `f ≥ 1` are those of the same degree
and residue degree that contain the unramified extension of degree `f`. -/
private def subtypeEquivSubtypeUnramifiedExtension {f : ℕ} (hf : f ≠ 0) (e : ℕ) :
    {L : IntermediateField K (SeparableClosure K) //
        Module.finrank K L = f * e ∧ L.inertiaDegree = f} ≃
      {L : IntermediateField K (SeparableClosure K) //
        (∀ x : unramifiedExtension K (SeparableClosure K) f,
          algebraMap (unramifiedExtension K (SeparableClosure K) f) (SeparableClosure K) x ∈ L) ∧
          Module.finrank K L = f * e ∧ L.inertiaDegree = f} :=
  Equiv.subtypeEquivRight fun L ↦ ⟨fun h ↦ ⟨fun x ↦ by
    have : Module.Finite K L := by
      by_contra h'
      rw [← inertiaDegree_eq_zero_iff] at h'
      omega
    exact L.unramifiedExtension_inertiaDegree_le (h.2 ▸ x.property), h⟩, And.right⟩

/-- **The subfield count by residue degree** ([Bhargava 2007, §2]): for `f ≥ 1`, the
subextensions `L` of `SeparableClosure K` of degree `f * e` and residue degree `f` satisfy
`∑_L q ^ (-d(L)) = e · q ^ (-f(e - 1))`, where `q` is the residue cardinality of `K` and `d(L)` the
discriminant exponent of `L / K`. The sum is in `ℝ≥0∞`, so the equation also asserts that it is
finite. For `e = 0` both sides vanish. -/
theorem tsum_inertiaDegree_eq {f : ℕ} (hf : f ≠ 0) (e : ℕ) :
    ∑' L : {L : IntermediateField K (SeparableClosure K) //
        Module.finrank K L = f * e ∧ L.inertiaDegree = f},
      1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ L.val.discriminantExponent =
      e / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (f * (e - 1)) := by
  set U := unramifiedExtension K (SeparableClosure K) f
  let _ := finiteIntermediateFieldValuativeRel K (SeparableClosure K) U
  let _ := finiteIntermediateFieldTopology K (SeparableClosure K) U
  have := finiteIntermediateField_isNonarchimedeanLocalField K (SeparableClosure K) U
  have := finiteIntermediateField_valuativeExtension K (SeparableClosure K) U
  have : IsUnramified K U := isUnramified_unramifiedExtension
  have hUr : Module.finrank K U = f := finrank_unramifiedExtension hf
  have hUf : inertiaDegree K U = f := by rw [IsUnramified.inertiaDegree_eq_finrank, hUr]
  have h := tsum_one_div_natCard_residueField_pow_discriminantExponent_eq (K := K) U e
  rw [hUr, hUf] at h
  rw [← h]
  exact (subtypeEquivSubtypeUnramifiedExtension hf e).tsum_eq
    (fun L ↦ 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ L.val.discriminantExponent)

/-- **Finitely many subextensions of a given degree and residue degree**: for `f ≥ 1` and `e`
nonzero in `K`, `SeparableClosure K` has only finitely many subextensions of degree `f * e` and
residue degree `f`. They are the totally ramified extensions of degree `e` of the unramified
extension `K_f` of degree `f`, and `σ_{K_f}(e)` is finite because `e` is nonzero in `K_f`. -/
theorem finite_setOf_finrank_eq_and_inertiaDegree_eq {f e : ℕ} (hf : f ≠ 0) (he : (e : K) ≠ 0) :
    {L : IntermediateField K (SeparableClosure K) |
      Module.finrank K L = f * e ∧ L.inertiaDegree = f}.Finite := by
  set U := unramifiedExtension K (SeparableClosure K) f
  let _ := finiteIntermediateFieldValuativeRel K (SeparableClosure K) U
  let _ := finiteIntermediateFieldTopology K (SeparableClosure K) U
  have := finiteIntermediateField_isNonarchimedeanLocalField K (SeparableClosure K) U
  have := finiteIntermediateField_valuativeExtension K (SeparableClosure K) U
  have : IsUnramified K U := isUnramified_unramifiedExtension
  have hUr : Module.finrank K U = f := finrank_unramifiedExtension hf
  have hUf : inertiaDegree K U = f := by rw [IsUnramified.inertiaDegree_eq_finrank, hUr]
  have heU : (e : U) ≠ 0 := by
    rwa [← map_natCast (algebraMap K U), map_ne_zero]
  have : Finite (totallyRamifiedOfDegree U e) :=
    ((tsum_one_div_natCard_residueField_pow_wildExponent_ne_top_iff_finite heU).1
      (by rw [tsum_one_div_natCard_residueField_pow_wildExponent]; exact ENNReal.natCast_ne_top e))
      |>.to_subtype
  have := isSepClosure_tower_top K U (SeparableClosure K)
  let Φ := IsSepClosure.equiv U (SeparableClosure U) (SeparableClosure K)
  rw [← Set.finite_coe_iff]
  exact Finite.of_equiv _ ((subtypeEquivSubtypeUnramifiedExtension hf e).trans
    ((Equiv.subtypeEquivRight fun L ↦ by rw [hUr, hUf]).trans
      (subtypeEquivTotallyRamifiedOfDegree U Φ e))).symm

end TauCeti

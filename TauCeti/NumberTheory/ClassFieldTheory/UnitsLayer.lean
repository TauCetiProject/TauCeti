/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.FiniteExtension
public import TauCeti.NumberTheory.ClassFieldTheory.Formation.Units
public import TauCeti.RingTheory.Norm.Units

/-!
# The layer of a finite Galois extension in the formation of units

Let `L/K` be a finite Galois extension. Every `K`-embedding `ι : L →ₐ[K] Kˢ` into the separable
closure has the same image, so the subgroup of `G_K = Gal(Kˢ/K)` fixing it does not depend on
`ι`: it is the open normal subgroup `TauCeti.fixingOpenNormalSubgroup K L`, the fixing subgroup of
the normal closure of `L` in `Kˢ`, equal to `TauCeti.galoisOpenNormalSubgroup K L ι` for every
`ι`.
Its layer `V ◁ G_K` in the formation `unitsFormation K` of `(Kˢ)ˣ` is the abstract counterpart of
`L/K`, and this file identifies its two ends with the concrete objects of finite class field
theory:

* the Galois group `G_K ⧸ V` of the layer is `Gal(L/K)` (`layerGalEquiv ι`), through restriction
  along `ι` (`TauCeti.quotientFixingSubgroupFieldRangeEquiv`); another embedding changes this
  identification by an inner automorphism of `Gal(L/K)` (`layerGalEquiv_comp`), so its
  abelianization does not depend on `ι` (`abelianizationCongr_layerGalEquiv`);
* the ground and top levels of the layer are `Kˣ` and `Lˣ`
  (`TauCeti.ClassFieldTheory.unitsLevelEquiv`), the norm of the
  layer is the field norm `N_{L/K}` (`norm_unitsLevelEquiv`), and so the norm quotient of the layer
  is `Kˣ / N_{L/K}(Lˣ)` (`layerNormQuotientEquiv`).

These are the two identifications through which the abstract Artin map of a class formation on
`unitsFormation K` becomes the norm-residue map `Kˣ / N_{L/K}(Lˣ) ≃ Gal(L/K)^ab` of finite local
reciprocity. Nothing here uses that `K` is local.

## Main definitions

* `TauCeti.ClassFieldTheory.layerGalEquiv ι`: the Galois group of the layer is `Gal(L/K)`.
* `TauCeti.ClassFieldTheory.layerNormQuotientEquiv K L`: the norm quotient of the layer is
  `Kˣ / N_{L/K}(Lˣ)`.

## Main results

* `TauCeti.ClassFieldTheory.fixedField_top_ofOpenNormal_fixingOpenNormalSubgroup`: the top
  level of the layer is cut out by the image of any embedding of `L`, so that
  `TauCeti.ClassFieldTheory.unitsLevelEquiv` identifies it with `Lˣ`.
* `TauCeti.ClassFieldTheory.abelianizationCongr_layerGalEquiv`: the identification of the
  abelianized Galois group does not depend on the embedding.
* `TauCeti.ClassFieldTheory.norm_unitsLevelEquiv`: the norm of the layer is the field norm.
* `TauCeti.ClassFieldTheory.unitsLevelEquiv_mem_normSubgroup_iff`: an element of `Kˣ` lies in
  the norm subgroup of the layer exactly when it is a field norm from `L`.

## References

* E. Artin and J. Tate, *Class Field Theory*, Chapter XIV, §1.
* J.-P. Serre, *Local Fields*, Chapter XI, §3.
-/

public section

noncomputable section

namespace TauCeti.ClassFieldTheory

open IntermediateField

variable {K : Type} [Field K]

/-! ### The ground and top levels of the layer -/

section Level

variable (K) in
/-- The fixed field of the ground subgroup `G_K` of a layer `V ◁ G_K` is `K`, the image of the
structure map `K →ₐ[K] Kˢ`. This is the hypothesis under which `unitsLevelEquiv` identifies the
ground level of such a layer with `Kˣ`. -/
theorem fixedField_ground_ofOpenNormal (V : OpenNormalSubgroup (AbsoluteGaloisGroup K)) :
    fixedField (NormalLayer.ofOpenNormal V).ground.toSubgroup =
      (Algebra.ofId K (SeparableClosure K)).fieldRange := by
  rw [NormalLayer.ground_ofOpenNormal, OpenSubgroup.toSubgroup_top, InfiniteGalois.fixedField_bot]
  ext x
  simp [mem_bot, Algebra.ofId_apply]

variable {L : Type*} [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- The fixed field of the top subgroup of the layer of a finite Galois extension `L/K` is the
image of `L` under any `K`-embedding `ι`. This is the hypothesis under which `unitsLevelEquiv`
identifies the top level of the layer with `Lˣ`. -/
theorem fixedField_top_ofOpenNormal_fixingOpenNormalSubgroup (ι : L →ₐ[K] SeparableClosure K) :
    fixedField (NormalLayer.ofOpenNormal (fixingOpenNormalSubgroup K L)).top.toSubgroup =
      ι.fieldRange := by
  rw [NormalLayer.top_ofOpenNormal,
    fixingOpenNormalSubgroup_toSubgroup ι, InfiniteGalois.fixedField_fixingSubgroup]

end Level

/-! ### The Galois group of the layer -/

section Galois

variable {L : Type*} [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- **The Galois group of the layer of a finite Galois extension `L/K` is `Gal(L/K)`**: the class
of `σ ∈ G_K` in `G_K ⧸ V`, for `V = fixingOpenNormalSubgroup K L`, is sent to the restriction
`ι.restrictNormalHom σ` of `σ` along the embedding `ι` (`layerGalEquiv_mk`). It is
`TauCeti.quotientFixingSubgroupFieldRangeEquiv K L ι` read on the layer. Another embedding changes
this identification by an inner automorphism (`layerGalEquiv_comp`). -/
def layerGalEquiv (ι : L →ₐ[K] SeparableClosure K) :
    (NormalLayer.ofOpenNormal (fixingOpenNormalSubgroup K L)).Gal ≃* Gal(L/K) :=
  (NormalLayer.galOfOpenNormalEquiv _).trans <|
    (QuotientGroup.quotientMulEquivOfEq (fixingOpenNormalSubgroup_toSubgroup ι)).trans
      (quotientFixingSubgroupFieldRangeEquiv K L ι)

/-- `layerGalEquiv ι` sends the class of `σ ∈ G_K` to the restriction of `σ` along `ι`. -/
@[simp]
theorem layerGalEquiv_mk (ι : L →ₐ[K] SeparableClosure K)
    (σ : (NormalLayer.ofOpenNormal (fixingOpenNormalSubgroup K L)).ground) :
    layerGalEquiv ι (σ : (NormalLayer.ofOpenNormal (fixingOpenNormalSubgroup K L)).Gal) =
      ι.restrictNormalHom (σ : AbsoluteGaloisGroup K) := by
  rw [layerGalEquiv, MulEquiv.trans_apply, NormalLayer.galOfOpenNormalEquiv_mk,
    MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk,
    quotientFixingSubgroupFieldRangeEquiv_mk]

/-- **Changing the embedding conjugates the identification of the Galois group**: precomposing
`ι` with `τ ∈ Gal(L/K)` changes `layerGalEquiv` by the inner automorphism of `τ`. -/
theorem layerGalEquiv_comp (ι : L →ₐ[K] SeparableClosure K) (τ : Gal(L/K))
    (γ : (NormalLayer.ofOpenNormal (fixingOpenNormalSubgroup K L)).Gal) :
    layerGalEquiv (ι.comp (τ : L →ₐ[K] L)) γ = τ⁻¹ * layerGalEquiv ι γ * τ := by
  induction γ using QuotientGroup.induction_on with
  | H σ => rw [layerGalEquiv_mk, layerGalEquiv_mk, AlgHom.restrictNormalHom_comp]

/-- **The abelianized Galois group of the layer is `Gal(L/K)^ab` independently of the
embedding**: the identifications `layerGalEquiv ι` for different `ι` differ by inner
automorphisms, which become trivial on abelianizations. -/
theorem abelianizationCongr_layerGalEquiv (ι ι' : L →ₐ[K] SeparableClosure K) :
    (layerGalEquiv ι).abelianizationCongr = (layerGalEquiv ι').abelianizationCongr := by
  obtain ⟨τ, rfl⟩ := ι.exists_comp_eq_of_normal ι'
  refine MulEquiv.toMonoidHom_injective (Abelianization.hom_ext _ _ (MonoidHom.ext fun γ => ?_))
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, abelianizationCongr_of,
    layerGalEquiv_comp, map_mul, map_inv]
  rw [mul_comm, ← mul_assoc, mul_inv_cancel, one_mul]

end Galois

/-! ### The norm quotient of the layer -/

section Norm

variable {L : Type*} [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- **The Galois action on the top level of the layer is the action of `Gal(L/K)` on `Lˣ`**,
through `layerGalEquiv ι` and `unitsLevelEquiv ι`. -/
@[simp]
theorem rep_ρ_unitsLevelEquiv (ι : L →ₐ[K] SeparableClosure K)
    (γ : (NormalLayer.ofOpenNormal (fixingOpenNormalSubgroup K L)).Gal) (y : Additive Lˣ) :
    (dsimp% only
      (((NormalLayer.ofOpenNormal (fixingOpenNormalSubgroup K L)).rep (unitsFormation K)).ρ γ
        (unitsLevelEquiv ι (fixedField_top_ofOpenNormal_fixingOpenNormalSubgroup ι) y))) =
      unitsLevelEquiv ι (fixedField_top_ofOpenNormal_fixingOpenNormalSubgroup ι)
        (Additive.ofMul (layerGalEquiv ι γ • y.toMul)) := by
  induction γ using QuotientGroup.induction_on with
  | H σ =>
    refine Subtype.ext ?_
    rw [NormalLayer.rep_ρ_mk_apply_coe, unitsLevelEquiv_apply_coe, unitsLevelEquiv_apply_coe,
      ← unitsCoeffEquivUnitsFormation_smul]
    congr 1
    refine Additive.toMul.injective (Units.ext ?_)
    simp [AlgEquiv.smul_units_def]

/-- **The norm of the layer is the field norm**: under the identifications of its top and ground
levels with `Lˣ` and `Kˣ`, the norm `N_{G_K/V}` of the layer of `L` is `N_{L/K}`. -/
theorem norm_unitsLevelEquiv (ι : L →ₐ[K] SeparableClosure K) (y : Additive Lˣ) :
    (NormalLayer.ofOpenNormal (fixingOpenNormalSubgroup K L)).norm (unitsFormation K)
        (unitsLevelEquiv ι (fixedField_top_ofOpenNormal_fixingOpenNormalSubgroup ι) y) =
      unitsLevelEquiv (Algebra.ofId K (SeparableClosure K))
        (fixedField_ground_ofOpenNormal K (fixingOpenNormalSubgroup K L))
        (Additive.ofMul (Algebra.normUnits K y.toMul)) := by
  refine Subtype.ext ?_
  rw [NormalLayer.norm_apply_coe, ← (layerGalEquiv ι).symm.toEquiv.sum_comp]
  calc _ = ∑ g : Gal(L/K), unitsCoeffEquivUnitsFormation K
        (Additive.ofMul (Units.map (ι : L →* SeparableClosure K) (g • y.toMul))) :=
      Finset.sum_congr rfl fun g _ => by
        rw [MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe, rep_ρ_unitsLevelEquiv,
          MulEquiv.apply_symm_apply, unitsLevelEquiv_apply_coe, toMul_ofMul]
    _ = _ := by
      rw [← map_sum, unitsLevelEquiv_apply_coe]
      congr 1
      refine Additive.toMul.injective (Units.ext ?_)
      simp only [toMul_sum, Units.coe_prod, Units.coe_map, MonoidHom.coe_ofClass, toMul_ofMul,
        AlgEquiv.smul_units_def, Algebra.coe_normUnits, Algebra.ofId_apply]
      rw [← map_prod, ← Algebra.norm_eq_prod_automorphisms, AlgHom.commutes]

variable (K L) in
/-- **The norm subgroup of the layer is the norm group** `N_{L/K}(Lˣ)`: an element of `Kˣ` lies
in the norm subgroup of the layer of `L` exactly when it is the field norm of a unit of `L`. -/
theorem unitsLevelEquiv_mem_normSubgroup_iff (a : Kˣ) :
    unitsLevelEquiv (Algebra.ofId K (SeparableClosure K))
        (fixedField_ground_ofOpenNormal K (fixingOpenNormalSubgroup K L)) (Additive.ofMul a) ∈
      (NormalLayer.ofOpenNormal (fixingOpenNormalSubgroup K L)).normSubgroup (unitsFormation K) ↔
      a ∈ normGroup K L := by
  let ι : L →ₐ[K] SeparableClosure K := IsSepClosed.lift
  rw [NormalLayer.mem_normSubgroup, mem_normGroup_iff,
    (unitsLevelEquiv ι (fixedField_top_ofOpenNormal_fixingOpenNormalSubgroup ι)).surjective.exists]
  constructor
  · rintro ⟨y, hy⟩
    rw [norm_unitsLevelEquiv, EmbeddingLike.apply_eq_iff_eq] at hy
    exact ⟨y.toMul, by rw [← Algebra.coe_normUnits, Additive.ofMul.injective hy]⟩
  · rintro ⟨y, hy⟩
    refine ⟨Additive.ofMul y, ?_⟩
    rw [norm_unitsLevelEquiv, EmbeddingLike.apply_eq_iff_eq]
    exact congrArg Additive.ofMul (Units.ext (by rw [Algebra.coe_normUnits]; exact hy))

variable (K L) in
/-- The map `Kˣ → A^U / N(A^V)` to the norm quotient of the layer of `L`, written
multiplicatively. -/
private def groundNormQuotientHom :
    Kˣ →* Multiplicative
      ((NormalLayer.ofOpenNormal (fixingOpenNormalSubgroup K L)).NormQuotient (unitsFormation K)) :=
  AddMonoidHom.toMultiplicativeRight
    (((NormalLayer.ofOpenNormal (fixingOpenNormalSubgroup K L)).normQuotientMk
        (unitsFormation K)).toAddMonoidHom.comp
      (unitsLevelEquiv (Algebra.ofId K (SeparableClosure K))
        (fixedField_ground_ofOpenNormal K (fixingOpenNormalSubgroup K L))).toAddMonoidHom)

omit [IsGalois K L] in
private theorem groundNormQuotientHom_apply (a : Kˣ) :
    groundNormQuotientHom K L a = Multiplicative.ofAdd
      ((NormalLayer.ofOpenNormal (fixingOpenNormalSubgroup K L)).normQuotientMk (unitsFormation K)
        (unitsLevelEquiv (Algebra.ofId K (SeparableClosure K))
          (fixedField_ground_ofOpenNormal K (fixingOpenNormalSubgroup K L)) (Additive.ofMul a))) :=
  (rfl)

variable (K L) in
private theorem ker_groundNormQuotientHom :
    normGroup K L = (groundNormQuotientHom K L).ker := by
  ext a
  rw [MonoidHom.mem_ker, ← unitsLevelEquiv_mem_normSubgroup_iff K L, groundNormQuotientHom_apply,
    ofAdd_eq_one, NormalLayer.normQuotientMk_apply, Submodule.Quotient.mk_eq_zero]

omit [IsGalois K L] in
variable (K L) in
private theorem surjective_groundNormQuotientHom :
    Function.Surjective (groundNormQuotientHom K L) := fun z => by
  obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective _ z.toAdd
  obtain ⟨a, rfl⟩ := (unitsLevelEquiv (Algebra.ofId K (SeparableClosure K))
    (fixedField_ground_ofOpenNormal K (fixingOpenNormalSubgroup K L))).surjective x
  refine ⟨a.toMul, ?_⟩
  rw [groundNormQuotientHom_apply, ofMul_toMul, NormalLayer.normQuotientMk_apply, hx, ofAdd_toAdd]

variable (K L) in
/-- **The norm quotient of the layer of `L` is `Kˣ / N_{L/K}(Lˣ)`**: the identification
`unitsLevelEquiv` of the ground level of the layer with `Kˣ` descends to the quotients by
`N_{L/K}(Lˣ)` and by the norm subgroup of the layer (`unitsLevelEquiv_mem_normSubgroup_iff`). -/
def layerNormQuotientEquiv :
    Additive (Kˣ ⧸ normGroup K L) ≃+
      (NormalLayer.ofOpenNormal (fixingOpenNormalSubgroup K L)).NormQuotient (unitsFormation K) :=
  MulEquiv.toAdditiveLeft
    ((QuotientGroup.quotientMulEquivOfEq (ker_groundNormQuotientHom K L)).trans
      (QuotientGroup.quotientKerEquivOfSurjective (groundNormQuotientHom K L)
        (surjective_groundNormQuotientHom K L)))

/-- `layerNormQuotientEquiv K L` sends the class of `a ∈ Kˣ` to the class of `a` in the norm
quotient of the layer. -/
@[simp]
theorem layerNormQuotientEquiv_mk (a : Kˣ) :
    layerNormQuotientEquiv K L (Additive.ofMul (a : Kˣ ⧸ normGroup K L)) =
      (NormalLayer.ofOpenNormal (fixingOpenNormalSubgroup K L)).normQuotientMk (unitsFormation K)
        (unitsLevelEquiv (Algebra.ofId K (SeparableClosure K))
          (fixedField_ground_ofOpenNormal K (fixingOpenNormalSubgroup K L)) (Additive.ofMul a)) :=
  (rfl)

end Norm

end TauCeti.ClassFieldTheory

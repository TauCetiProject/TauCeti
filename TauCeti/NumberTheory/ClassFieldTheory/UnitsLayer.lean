/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.FiniteExtension
public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Norm
public import TauCeti.NumberTheory.ClassFieldTheory.Formation.GroundNorm
public import TauCeti.NumberTheory.ClassFieldTheory.Formation.NormLimitation
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
  is `Kˣ / N_{L/K}(Lˣ)` (`layerNormQuotientEquiv`);
* the layer cohomology is ordinary Galois cohomology of `L/K` with coefficients in `Lˣ`
  (`layerCohomologyEquiv`).

These are the two identifications through which the abstract Artin map of a class formation on
`unitsFormation K` becomes the norm-residue map `Kˣ / N_{L/K}(Lˣ) ≃ Gal(L/K)^ab` of finite local
reciprocity. Nothing here uses that `K` is local.

The norm computation is done more generally, for the level of an arbitrary finite subextension
`ι : E →ₐ[K] Kˢ`, with no normality assumption: the norm `Formation.levelNorm` from that level to
the level of `G_K` is the field norm `N_{E/K}` (`levelNorm_unitsLevelEquiv`). The norm of the layer
of `L` is the field norm `N_{L/K}` (`norm_unitsLevelEquiv`), the case `E = L`, because the norm of
a layer is `Formation.levelNorm` between its top and ground levels
(`TauCeti.ClassFieldTheory.NormalLayer.toAddMonoidHom_norm`). The non-normal case is needed for
the norm functoriality of the absolute local Artin map, where the ground level of a restricted
layer is cut out by a subextension that need not be normal.

## Main definitions

* `TauCeti.ClassFieldTheory.layerGalEquiv ι`: the Galois group of the layer is `Gal(L/K)`.
* `TauCeti.ClassFieldTheory.layerNormQuotientEquiv K L`: the norm quotient of the layer is
  `Kˣ / N_{L/K}(Lˣ)`.
* `TauCeti.ClassFieldTheory.layerCohomologyEquiv ι`: the cohomology of the layer is the concrete
  Galois cohomology of `L/K` with coefficients in `Lˣ`.

## Main results

* `TauCeti.ClassFieldTheory.fixedField_top_ofOpenNormal_fixingOpenNormalSubgroup`: the top
  level of the layer is cut out by the image of any embedding of `L`, so that
  `TauCeti.ClassFieldTheory.unitsLevelEquiv` identifies it with `Lˣ`.
* `TauCeti.ClassFieldTheory.eq_top_of_fixedField_toSubgroup_eq`: the only open subgroup of `G_K`
  with fixed field `K` is `G_K`.
* `TauCeti.ClassFieldTheory.abelianizationCongr_layerGalEquiv`: the identification of the
  abelianized Galois group does not depend on the embedding.
* `TauCeti.ClassFieldTheory.levelNorm_unitsLevelEquiv`: for a finite extension `E/K` embedded in
  `Kˢ`, not necessarily normal, the norm `Formation.levelNorm` from the level of `Gal(Kˢ/E)` to the
  level of `G_K` is the field norm `N_{E/K}`.
* `TauCeti.ClassFieldTheory.norm_unitsLevelEquiv`: in particular, the norm of the layer of `L` is
  the field norm `N_{L/K}`.
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
/-- The fixed field of the whole group `G_K` is `K`, the image of the structure map
`K →ₐ[K] Kˢ`. This is the hypothesis under which `unitsLevelEquiv` identifies the level
`((Kˢ)ˣ)^{G_K}` with `Kˣ`. -/
theorem fixedField_toSubgroup_top_eq_fieldRange :
    fixedField (⊤ : OpenSubgroup (AbsoluteGaloisGroup K)).toSubgroup =
      (Algebra.ofId K (SeparableClosure K)).fieldRange := by
  rw [TauCeti.fixedField_toSubgroup_top]
  ext x
  simp [mem_bot, Algebra.ofId_apply]

/-- The only open subgroup of `G_K` whose fixed field is `K` is `G_K` itself. -/
theorem eq_top_of_fixedField_toSubgroup_eq {W : OpenSubgroup (AbsoluteGaloisGroup K)}
    (h : fixedField W.toSubgroup = (Algebra.ofId K (SeparableClosure K)).fieldRange) : W = ⊤ :=
  OpenSubgroup.toSubgroup_injective <|
    (toSubgroup_eq_fixingSubgroup_of_fixedField_eq
      (h.trans (fixedField_toSubgroup_top_eq_fieldRange K).symm)).trans
      (toSubgroup_eq_fixingSubgroup_of_fixedField_eq rfl).symm

variable (K) in
/-- The fixed field of the ground subgroup `G_K` of a layer `V ◁ G_K` is `K`, the image of the
structure map `K →ₐ[K] Kˢ`. This is the hypothesis under which `unitsLevelEquiv` identifies the
ground level of such a layer with `Kˣ`. -/
theorem fixedField_ground_ofOpenNormal (V : OpenNormalSubgroup (AbsoluteGaloisGroup K)) :
    fixedField (NormalLayer.ofOpenNormal V).ground.toSubgroup =
      (Algebra.ofId K (SeparableClosure K)).fieldRange := by
  rw [NormalLayer.ground_ofOpenNormal, fixedField_toSubgroup_top_eq_fieldRange]

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

/-- `(layerGalEquiv ι).symm` sends the restriction of `σ ∈ G_K` along `ι` to the class of `σ` in
`G_K ⧸ V`, read in the Galois group of the layer. -/
theorem layerGalEquiv_symm_restrictNormalHom (ι : L →ₐ[K] SeparableClosure K)
    (σ : AbsoluteGaloisGroup K) :
    (layerGalEquiv ι).symm (ι.restrictNormalHom σ) =
      (NormalLayer.galOfOpenNormalEquiv (fixingOpenNormalSubgroup K L)).symm
        (σ : AbsoluteGaloisGroup K ⧸ (fixingOpenNormalSubgroup K L).toSubgroup) := by
  rw [MulEquiv.symm_apply_eq, layerGalEquiv, MulEquiv.trans_apply, MulEquiv.apply_symm_apply,
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

/-! ### The norm from the level of a finite extension -/

section LevelNorm

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

variable {E : Type*} [Field E] [Algebra K E] [FiniteDimensional K E]

/-- **The norm from the level of a finite extension is the field norm**: if the fixed field of the
open subgroup `W` is the image of a `K`-embedding `ι : E →ₐ[K] Kˢ` of a finite extension `E/K`, and
that of `W₀ ⊇ W` is `K`, then under the identifications `unitsLevelEquiv` of the two levels with
`Eˣ` and `Kˣ`, the norm `Formation.levelNorm` from `((Kˢ)ˣ)^W` to `((Kˢ)ˣ)^{W₀}` is `N_{E/K}`. The
extension `E/K` need not be normal. -/
theorem levelNorm_unitsLevelEquiv (ι : E →ₐ[K] SeparableClosure K)
    {W W₀ : OpenSubgroup (AbsoluteGaloisGroup K)} (h : W ≤ W₀)
    (hW : fixedField W.toSubgroup = ι.fieldRange)
    (hW₀ : fixedField W₀.toSubgroup = (Algebra.ofId K (SeparableClosure K)).fieldRange)
    (y : Additive Eˣ) :
    (unitsFormation K).levelNorm h (unitsLevelEquiv ι hW y) =
      unitsLevelEquiv (Algebra.ofId K (SeparableClosure K)) hW₀
        (Additive.ofMul (Algebra.normUnits K y.toMul)) := by
  obtain rfl : W₀ = ⊤ := eq_top_of_fixedField_toSubgroup_eq hW₀
  -- The representatives of the cosets of `W` in `G_K` are a transversal of `Gal(Kˢ/ι(E))`, so the
  -- norm is the product of the conjugates of `ι y` (`TauCeti.algebraMap_norm_eq_prod_transversal`).
  have hfix := toSubgroup_eq_fixingSubgroup_of_fixedField_eq hW
  let e := Subgroup.quotientEquivOfEq hfix
  refine Subtype.ext ?_
  rw [Formation.levelNorm_top_apply_coe, unitsLevelEquiv_apply_coe, unitsLevelEquiv_apply_coe,
    finsum_eq_sum_of_fintype]
  calc _ = ∑ q : AbsoluteGaloisGroup K ⧸ W.toSubgroup,
        unitsCoeffEquivUnitsFormation K ((q.out : AbsoluteGaloisGroup K) •
          Additive.ofMul (Units.map (ι : E →* SeparableClosure K) y.toMul)) :=
      Finset.sum_congr rfl fun q _ => (unitsCoeffEquivUnitsFormation_smul K _ _).symm
    _ = _ := by
      rw [← map_sum]
      congr 1
      refine Additive.toMul.injective (Units.ext ?_)
      simp only [toMul_sum, Units.coe_prod, Additive.toMul_smul, toMul_ofMul,
        AlgEquiv.smul_units_def, Units.coe_map, MonoidHom.coe_ofClass, Algebra.coe_normUnits,
        Algebra.ofId_apply]
      rw [algebraMap_norm_eq_prod_transversal K E ι (fun u => (e.symm u).out) (fun u => by
        rw [← Subgroup.quotientEquivOfEq_mk hfix, QuotientGroup.out_eq', Equiv.apply_symm_apply]),
        ← e.symm.prod_comp]

end LevelNorm

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
levels with `Lˣ` and `Kˣ`, the norm `N_{G_K/V}` of the layer of `L` is `N_{L/K}`. This is the
case `E = L` of `levelNorm_unitsLevelEquiv`, since the norm of a layer is `Formation.levelNorm`
between its top and ground levels (`NormalLayer.toAddMonoidHom_norm`). -/
theorem norm_unitsLevelEquiv (ι : L →ₐ[K] SeparableClosure K) (y : Additive Lˣ) :
    (NormalLayer.ofOpenNormal (fixingOpenNormalSubgroup K L)).norm (unitsFormation K)
        (unitsLevelEquiv ι (fixedField_top_ofOpenNormal_fixingOpenNormalSubgroup ι) y) =
      unitsLevelEquiv (Algebra.ofId K (SeparableClosure K))
        (fixedField_ground_ofOpenNormal K (fixingOpenNormalSubgroup K L))
        (Additive.ofMul (Algebra.normUnits K y.toMul)) := by
  rw [← LinearMap.toAddMonoidHom_coe, NormalLayer.toAddMonoidHom_norm]
  exact levelNorm_unitsLevelEquiv ι _ _ _ y

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

/-! ### Cohomology -/

section Cohomology

variable {L : Type} [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- The coefficient identification from the representation of the layer of `L` to the standard
Galois representation on `Lˣ`. -/
noncomputable def layerCoefficientEquiv (ι : L →ₐ[K] SeparableClosure K) :
    (NormalLayer.ofOpenNormal (fixingOpenNormalSubgroup K L)).rep (unitsFormation K) ≃ₗ[ℤ]
      Rep.ofMulDistribMulAction Gal(L/K) Lˣ :=
  (unitsLevelEquiv ι
    (fixedField_top_ofOpenNormal_fixingOpenNormalSubgroup (K := K) ι)).symm.toIntLinearEquiv

/-- The coefficient identification inverts `unitsLevelEquiv`. -/
@[simp]
theorem layerCoefficientEquiv_unitsLevelEquiv (ι : L →ₐ[K] SeparableClosure K)
    (y : Additive Lˣ) :
    layerCoefficientEquiv ι
        (unitsLevelEquiv ι (fixedField_top_ofOpenNormal_fixingOpenNormalSubgroup ι) y) = y :=
  AddEquiv.symm_apply_apply _ _

/-- Reading the concrete coefficient of a layer element through `ι` recovers its value in the
separable closure. -/
theorem layerCoefficientEquiv_apply_coe (ι : L →ₐ[K] SeparableClosure K)
    (x : (NormalLayer.ofOpenNormal (fixingOpenNormalSubgroup K L)).rep (unitsFormation K)) :
    Additive.ofMul (Units.map (ι : L →* SeparableClosure K)
        (Rep.toAdditive (layerCoefficientEquiv ι x)).toMul) =
      (unitsCoeffEquivUnitsFormation K).symm
        ((x : (unitsFormation K).level
          (NormalLayer.ofOpenNormal (fixingOpenNormalSubgroup K L)).top) :
            (unitsFormation K).toRep.V) := by
  apply (unitsCoeffEquivUnitsFormation K).eq_symm_apply.2
  rw [← unitsLevelEquiv_apply_coe ι
    (fixedField_top_ofOpenNormal_fixingOpenNormalSubgroup ι)]
  exact congrArg Subtype.val ((unitsLevelEquiv ι
    (fixedField_top_ofOpenNormal_fixingOpenNormalSubgroup ι)).apply_symm_apply x)

/-- The coefficient identification intertwines the layer action with the concrete Galois
action. -/
theorem layerCoefficientEquiv_ρ (ι : L →ₐ[K] SeparableClosure K)
    (γ : (NormalLayer.ofOpenNormal (fixingOpenNormalSubgroup K L)).Gal)
    (x : (NormalLayer.ofOpenNormal (fixingOpenNormalSubgroup K L)).rep (unitsFormation K)) :
    layerCoefficientEquiv ι
        (((NormalLayer.ofOpenNormal (fixingOpenNormalSubgroup K L)).rep
          (unitsFormation K)).ρ γ x) =
      (Rep.ofMulDistribMulAction Gal(L/K) Lˣ).ρ (layerGalEquiv ι γ)
        (layerCoefficientEquiv ι x) := by
  obtain ⟨y, rfl⟩ := (unitsLevelEquiv ι
    (fixedField_top_ofOpenNormal_fixingOpenNormalSubgroup (K := K) ι)).surjective x
  rw [rep_ρ_unitsLevelEquiv, layerCoefficientEquiv_unitsLevelEquiv,
    layerCoefficientEquiv_unitsLevelEquiv, Rep.ofMulDistribMulAction_ρ_apply_apply]

/-- The morphism of representations underlying `layerCohomologyEquiv`. -/
noncomputable def layerCoefficientHom (ι : L →ₐ[K] SeparableClosure K) :
    Rep.res (layerGalEquiv ι).symm
        ((NormalLayer.ofOpenNormal (fixingOpenNormalSubgroup K L)).rep (unitsFormation K)) ⟶
      Rep.ofMulDistribMulAction Gal(L/K) Lˣ :=
  Rep.ofHom ⟨(layerCoefficientEquiv ι).toLinearMap, fun h => LinearMap.ext fun x => by
    -- This is `layerCoefficientEquiv_ρ` at `(layerGalEquiv ι).symm h`, read through the
    -- `Rep.res`, `Rep.of` and `LinearMap.comp` wrappers. These agree definitionally, but their
    -- module instances differ syntactically, so `rw` and `simp` cannot unfold them.
    refine (layerCoefficientEquiv_ρ ι ((layerGalEquiv ι).symm h) x).trans ?_
    rw [MulEquiv.apply_symm_apply]
    rfl⟩

/-- The representation morphism underlying the layer comparison is the coefficient
identification. -/
@[simp]
theorem layerCoefficientHom_apply (ι : L →ₐ[K] SeparableClosure K)
    (x : (NormalLayer.ofOpenNormal (fixingOpenNormalSubgroup K L)).rep (unitsFormation K)) :
    (layerCoefficientHom ι).hom x = layerCoefficientEquiv ι x :=
  (rfl)

/-- **The cohomology of the layer of `L` is the ordinary Galois cohomology of `L/K`**:
restriction along `ι` identifies the layer Galois group with `Gal(L/K)`, while
`unitsLevelEquiv` identifies the layer coefficients with `Lˣ`. -/
noncomputable def layerCohomologyEquiv (ι : L →ₐ[K] SeparableClosure K) (n : ℕ) :
    (NormalLayer.ofOpenNormal (fixingOpenNormalSubgroup K L)).H (unitsFormation K) n ≃+
      groupCohomology (Rep.ofMulDistribMulAction Gal(L/K) Lˣ) n :=
  (groupCohomology.mapIso
    (A := Rep.ofMulDistribMulAction Gal(L/K) Lˣ)
    (B := (NormalLayer.ofOpenNormal (fixingOpenNormalSubgroup K L)).rep (unitsFormation K))
    (layerGalEquiv (K := K) (L := L) ι)
    (layerCoefficientEquiv ι)
    (fun γ => LinearMap.ext fun x => layerCoefficientEquiv_ρ ι γ x)
    n).toLinearEquiv.toAddEquiv

/-- `layerCohomologyEquiv` is induced by the concrete group and coefficient identifications. -/
theorem layerCohomologyEquiv_apply (ι : L →ₐ[K] SeparableClosure K) (n : ℕ)
    (x : (NormalLayer.ofOpenNormal (fixingOpenNormalSubgroup K L)).H (unitsFormation K) n) :
    layerCohomologyEquiv ι n x =
      groupCohomology.map (layerGalEquiv ι).symm (layerCoefficientHom ι) n x := by
  rfl

/-- A ground-field unit, viewed in the layer and then in `Lˣ`, is its image under the algebra
map `K → L`. -/
theorem layerCoefficientEquiv_groundLevel (ι : L →ₐ[K] SeparableClosure K) (a : Kˣ) :
    Rep.toAdditive (layerCoefficientEquiv ι
      (((NormalLayer.ofOpenNormal (fixingOpenNormalSubgroup K L)).groundLevelEquiv
        (unitsFormation K)).symm
          (unitsLevelEquiv (Algebra.ofId K (SeparableClosure K))
            (fixedField_ground_ofOpenNormal K (fixingOpenNormalSubgroup K L))
            (Additive.ofMul a)))) =
      Additive.ofMul (Units.map (algebraMap K L : K →* L) a) := by
  apply Additive.toMul.injective
  apply Units.map_injective (f := (ι : L →* SeparableClosure K)) ι.injective
  have hx := layerCoefficientEquiv_apply_coe ι
    (((NormalLayer.ofOpenNormal (fixingOpenNormalSubgroup K L)).groundLevelEquiv
      (unitsFormation K)).symm
        (unitsLevelEquiv (Algebra.ofId K (SeparableClosure K))
          (fixedField_ground_ofOpenNormal K (fixingOpenNormalSubgroup K L))
          (Additive.ofMul a)))
  have hx' := congrArg Additive.toMul hx
  rw [toMul_ofMul] at hx'
  rw [hx']
  rw [NormalLayer.groundLevelEquiv_symm_apply_coe]
  have he :
      (unitsCoeffEquivUnitsFormation K).symm
          (((unitsLevelEquiv (Algebra.ofId K (SeparableClosure K))
            (fixedField_ground_ofOpenNormal K (fixingOpenNormalSubgroup K L))
            (Additive.ofMul a) :
              (unitsFormation K).level
                (NormalLayer.ofOpenNormal (fixingOpenNormalSubgroup K L)).ground) :
            (unitsFormation K).toRep.V)) =
        Additive.ofMul (Units.map
          (Algebra.ofId K (SeparableClosure K) : K →* SeparableClosure K) a) := by
    apply (unitsCoeffEquivUnitsFormation K).injective
    rw [AddEquiv.apply_symm_apply, unitsLevelEquiv_apply_coe]
    simp only [toMul_ofMul]
  rw [he]
  apply Units.ext
  simp only [toMul_ofMul, Units.coe_map, MonoidHom.coe_ofClass, Algebra.ofId_apply,
    AlgHom.commutes]

end Cohomology

end TauCeti.ClassFieldTheory

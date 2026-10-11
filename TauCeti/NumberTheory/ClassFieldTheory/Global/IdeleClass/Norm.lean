/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Formation.AbsoluteArtinMap
public import TauCeti.NumberTheory.ClassFieldTheory.Global.IdeleClass.Level
public import TauCeti.NumberTheory.NumberField.Global.Ideles.Norm.Galois
import TauCeti.NumberTheory.ClassFieldTheory.Formation.GroundNorm

/-!
# The norm of the idele-class formation

Let `K` be a number field, `V` an open normal subgroup of `G_K` and `E` its fixed field, a finite
Galois subextension of `Kˢ/K`. The layer `V ◁ G_K` of the idele-class formation
`globalFormation K` has top level `C_E` and ground level `C_K` (`ideleClassLevelEquiv`,
`globalGroundEquiv`). This file shows that its norm, the sum of the Galois conjugates, is the norm
map of idele classes `N_{E/K} : C_E → C_K` (`norm_ideleClassLevelEquiv`). Hence the norm subgroup
of the layer is the idele-class norm group `N_{E/K}(C_E)`
(`globalGroundEquiv_mem_normSubgroup_iff`), and its norm quotient is `C_K / N_{E/K}(C_E)`
(`globalNormQuotientEquiv`). For a finite Galois extension `L/K` given abstractly, the layer of
`fixingOpenNormalSubgroup K L` has fixed field the image `E` of any `K`-embedding of `L`, and `E`
has the same idele-class norm group as `L`, so its norm quotient is `C_K / N_{L/K}(C_L)`
(`globalLayerNormQuotientEquiv`).

The norm of the layer is computed on an idele `a` of `E`: by `Formation.levelNorm_top_apply_coe`
it is the sum of the translates of the class of `a` by coset representatives of `V`, which act
through their restrictions to `E`; these restrictions run through `Gal(E/K)` once each
(`TauCeti.prod_restrictNormal_out`). The product of the Galois conjugates of `a` is the idele norm
`N_{E/K}(a)` extended back to `E` (`TauCeti.GlobalNumberFields.ideleExtension_ideleNormMap`).

This identifies the abstract norm quotient that the class formation axioms and the Artin map are
stated on with the concrete quotient `C_K / N_{E/K}(C_E)` that the fundamental inequalities and
global reciprocity are about.

## Main definitions

* `TauCeti.ClassFieldTheory.globalNormQuotientEquiv`: the norm quotient of the layer of `E` is
  `C_K / N_{E/K}(C_E)`.
* `TauCeti.ClassFieldTheory.globalLayerNormQuotientEquiv`: the norm quotient of the layer of a
  finite Galois extension `L/K` is `C_K / N_{L/K}(C_L)`.

## Main results

* `TauCeti.ClassFieldTheory.norm_ideleClassLevelEquiv`: the norm of the layer of `E` is the norm
  map of idele classes `N_{E/K}`.
* `TauCeti.ClassFieldTheory.globalGroundEquiv_mem_normSubgroup_iff`: an idele class of `K` lies
  in the norm subgroup of the layer of `E` exactly when it is a norm from `C_E`.
* `TauCeti.ClassFieldTheory.globalGroundEquiv_mem_layerNormSubgroup_iff`: the same for the layer
  of a finite Galois extension `L/K` and norms from `C_L`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §§2 and 5.
* E. Artin and J. Tate, *Class Field Theory*, Chapter XIV, §1.
-/

public section

noncomputable section

open IntermediateField NumberField

namespace TauCeti.ClassFieldTheory

variable {K : Type} [Field K] [NumberField K]

local notation "Ω" => FiniteGaloisIntermediateField K (SeparableClosure K)

/-- An idele of `K`, extended to the bottom subextension of `Kˢ/K` or to `E`, is the same idele of
`Kˢ`. -/
private theorem ideleCoeffOf_bot_ideleExtension (E : Ω) (b : IdeleGroup (𝓞 K) K) :
    ideleCoeffOf K ⊥ (.ofMul (GlobalNumberFields.ideleExtension K
        ((⊥ : Ω) : IntermediateField K (SeparableClosure K)) b)) =
      ideleCoeffOf K E (.ofMul (GlobalNumberFields.ideleExtension K E b)) := by
  rw [← ideleCoeffOf_ideleTransition (bot_le : (⊥ : Ω) ≤ E)]
  refine congrArg _ (congrArg _ (Units.ext ?_))
  let _ := (IntermediateField.inclusion (bot_le : (⊥ : Ω) ≤ E)).toRingHom.toAlgebra
  -- Both ways round, `x ∈ K` goes to the element `x` of `Kˢ`.
  have : IsScalarTower K ((⊥ : Ω) : IntermediateField K (SeparableClosure K)) E :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  rw [coe_ideleTransition, adeleTransition_apply, ← GlobalNumberFields.coe_ideleExtension,
    ← MonoidHom.comp_apply, GlobalNumberFields.ideleExtension_comp]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex in
/-- The norm from the level of `W` to the level of `G_K`, where the fixed field of `W` is `E`, is
the norm map of idele classes `N_{E/K}`. It is stated in the ambient module, for any `W₀ = ⊤`, so
that it applies to the ground of a layer, which is `⊤` only propositionally. -/
private theorem coe_levelNorm_ideleClassLevelEquiv (E : Ω)
    {W W₀ : OpenSubgroup (AbsoluteGaloisGroup K)} (h : W ≤ W₀) (hW₀ : W₀ = ⊤)
    (hW : fixedField W.toSubgroup = E) (c : IdeleClassGroup (𝓞 E) E) :
    ((globalFormation K).levelNorm h (ideleClassLevelEquiv E hW (.ofMul c)) :
        (globalFormation K).toRep.V) =
      (globalGroundEquiv K (.ofMul (GlobalNumberFields.ideleClassNormMap K E c)) :
        (globalFormation K).toRep.V) := by
  subst hW₀
  induction c using QuotientGroup.induction_on with | H a => ?_
  -- Restricting the coset representatives of `W` to `E` runs through `Gal(E/K)` once each.
  have hprod := prod_restrictNormal_out hW fun σ ↦
    (Units.map (GlobalNumberFields.adeleGaloisAction K E σ) a : IdeleGroup (𝓞 E) E)
  rw [Formation.levelNorm_top_apply_coe, finsum_eq_sum_of_fintype, ideleClassLevelEquiv_mk,
    GlobalNumberFields.ideleClassNormMap_mk, globalGroundEquiv_mk, ideleCoeffOf_bot_ideleExtension,
    GlobalNumberFields.ideleExtension_ideleNormMap, ← hprod, ofMul_prod, map_sum (ideleCoeffOf K E),
    map_sum (ideleClassMk K), map_sum (ideleClassCoeffEquivGlobalFormation K)]
  -- Each coset representative acts on the class of `a` through its restriction to `E`.
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  rw [← ideleClassCoeffEquivGlobalFormation_smul, ← map_smul (ideleClassMk K), smul_ideleCoeffOf]

/-- **The norm of the idele-class formation is the idele-class norm**: if the fixed field of the
open normal subgroup `V` of `G_K` is `E`, then under the identifications of the top and ground
levels of the layer `V ◁ G_K` with `C_E` and `C_K`, the norm of the layer is the norm map of idele
classes `N_{E/K} : C_E → C_K`. -/
theorem norm_ideleClassLevelEquiv (E : Ω) {V : OpenNormalSubgroup (AbsoluteGaloisGroup K)}
    (hV : fixedField (NormalLayer.ofOpenNormal V).top.toSubgroup = E)
    (c : IdeleClassGroup (𝓞 E) E) :
    (NormalLayer.ofOpenNormal V).norm (globalFormation K) (ideleClassLevelEquiv E hV (.ofMul c)) =
      NormalLayer.groundEquivOfOpenNormal (globalFormation K) V
        (globalGroundEquiv K (.ofMul (GlobalNumberFields.ideleClassNormMap K E c))) := by
  refine Subtype.ext ?_
  rw [← LinearMap.toAddMonoidHom_coe, NormalLayer.toAddMonoidHom_norm,
    NormalLayer.groundEquivOfOpenNormal_apply_coe]
  exact coe_levelNorm_ideleClassLevelEquiv E _ (NormalLayer.ground_ofOpenNormal V) hV c

/-- **The norm subgroup of the layer of `E` is `N_{E/K}(C_E)`**: an idele class of `K` lies in the
norm subgroup of the layer `V ◁ G_K` of the idele-class formation, where `E` is the fixed field of
`V`, exactly when it is the norm of an idele class of `E`. -/
theorem globalGroundEquiv_mem_normSubgroup_iff (E : Ω)
    {V : OpenNormalSubgroup (AbsoluteGaloisGroup K)}
    (hV : fixedField (NormalLayer.ofOpenNormal V).top.toSubgroup = E)
    (c : IdeleClassGroup (𝓞 K) K) :
    NormalLayer.groundEquivOfOpenNormal (globalFormation K) V (globalGroundEquiv K (.ofMul c)) ∈
        (NormalLayer.ofOpenNormal V).normSubgroup (globalFormation K) ↔
      c ∈ (GlobalNumberFields.ideleClassNormMap K E :
        IdeleClassGroup (𝓞 E) E →* IdeleClassGroup (𝓞 K) K).range := by
  rw [NormalLayer.mem_normSubgroup, (ideleClassLevelEquiv E hV).surjective.exists,
    Additive.ofMul.surjective.exists, MonoidHom.mem_range]
  refine exists_congr fun x ↦ ?_
  rw [norm_ideleClassLevelEquiv, EmbeddingLike.apply_eq_iff_eq, EmbeddingLike.apply_eq_iff_eq,
    EmbeddingLike.apply_eq_iff_eq, MonoidHom.coe_ofClass]

/-- **The norm quotient of the layer of `E` is `C_K / N_{E/K}(C_E)`**: if the fixed field of the
open normal subgroup `V` of `G_K` is `E`, then the identification `globalGroundEquiv` of `C_K` with
the ground level of the layer `V ◁ G_K` of the idele-class formation descends to the quotients by
`N_{E/K}(C_E)` and by the norm subgroup of the layer (`globalGroundEquiv_mem_normSubgroup_iff`). -/
def globalNormQuotientEquiv (E : Ω) {V : OpenNormalSubgroup (AbsoluteGaloisGroup K)}
    (hV : fixedField (NormalLayer.ofOpenNormal V).top.toSubgroup = E) :
    Additive (IdeleClassGroup (𝓞 K) K ⧸ (GlobalNumberFields.ideleClassNormMap K E :
        IdeleClassGroup (𝓞 E) E →* IdeleClassGroup (𝓞 K) K).range) ≃+
      (NormalLayer.ofOpenNormal V).NormQuotient (globalFormation K) :=
  (NormalLayer.ofOpenNormal V).normQuotientEquivOfGroundEquiv (globalFormation K)
    ((globalGroundEquiv K).trans (NormalLayer.groundEquivOfOpenNormal (globalFormation K) V))
    (globalGroundEquiv_mem_normSubgroup_iff E hV)

/-- `globalNormQuotientEquiv E hV` sends the class of `c ∈ C_K` to the class of `c` in the norm
quotient of the layer. -/
@[simp]
theorem globalNormQuotientEquiv_mk (E : Ω) {V : OpenNormalSubgroup (AbsoluteGaloisGroup K)}
    (hV : fixedField (NormalLayer.ofOpenNormal V).top.toSubgroup = E)
    (c : IdeleClassGroup (𝓞 K) K) :
    globalNormQuotientEquiv E hV (.ofMul (c : IdeleClassGroup (𝓞 K) K ⧸
        (GlobalNumberFields.ideleClassNormMap K E :
          IdeleClassGroup (𝓞 E) E →* IdeleClassGroup (𝓞 K) K).range)) =
      (NormalLayer.ofOpenNormal V).normQuotientMk (globalFormation K)
        (NormalLayer.groundEquivOfOpenNormal (globalFormation K) V
          (globalGroundEquiv K (.ofMul c))) :=
  NormalLayer.normQuotientEquivOfGroundEquiv_mk _ _ _ _ c

section Layer

variable (L : Type*) [Field L] [NumberField L] [Algebra K L] [IsGalois K L]

variable (K) in
/-- **The norm subgroup of the layer of `L` is `N_{L/K}(C_L)`**: for a finite Galois extension
`L/K`, an idele class of `K` lies in the norm subgroup of the layer of
`fixingOpenNormalSubgroup K L` exactly when it is the norm of an idele class of `L`. The fixed
field of the layer is the image `E` of a `K`-embedding of `L` into `Kˢ`, and `E` and `L` have the
same idele-class norm group (`range_ideleClassNormMap_eq_of_algEquiv`). -/
theorem globalGroundEquiv_mem_layerNormSubgroup_iff (c : IdeleClassGroup (𝓞 K) K) :
    NormalLayer.groundEquivOfOpenNormal (globalFormation K) (fixingOpenNormalSubgroup K L)
        (globalGroundEquiv K (.ofMul c)) ∈
        (NormalLayer.ofOpenNormal (fixingOpenNormalSubgroup K L)).normSubgroup (globalFormation K) ↔
      c ∈ (GlobalNumberFields.ideleClassNormMap K L :
        IdeleClassGroup (𝓞 L) L →* IdeleClassGroup (𝓞 K) K).range := by
  let ι : L →ₐ[K] SeparableClosure K := IsSepClosed.lift
  have : FiniteDimensional K ι.fieldRange := ι.equivFieldRange.toLinearEquiv.finiteDimensional
  have : IsGalois K ι.fieldRange := IsGalois.of_algEquiv ι.equivFieldRange
  obtain ⟨E, hE⟩ : ∃ E : Ω, (E : IntermediateField K (SeparableClosure K)) = ι.fieldRange :=
    ⟨⟨ι.fieldRange⟩, rfl⟩
  have hV : fixedField (NormalLayer.ofOpenNormal (fixingOpenNormalSubgroup K L)).top.toSubgroup =
      E := by
    rw [NormalLayer.top_ofOpenNormal, fixingOpenNormalSubgroup_toSubgroup ι,
      InfiniteGalois.fixedField_fixingSubgroup, hE]
  rw [globalGroundEquiv_mem_normSubgroup_iff E hV,
    GlobalNumberFields.range_ideleClassNormMap_eq_of_algEquiv
      (ι.equivFieldRange.trans (IntermediateField.equivOfEq hE.symm))]

variable (K) in
/-- **The norm quotient of the layer of `L` is `C_K / N_{L/K}(C_L)`**: for a finite Galois
extension `L/K`, the identification `globalGroundEquiv` of `C_K` with the ground level of the
layer of `fixingOpenNormalSubgroup K L` in the idele-class formation descends to the quotients by
`N_{L/K}(C_L)` and by the norm subgroup of the layer
(`globalGroundEquiv_mem_layerNormSubgroup_iff`). -/
def globalLayerNormQuotientEquiv :
    Additive (IdeleClassGroup (𝓞 K) K ⧸ (GlobalNumberFields.ideleClassNormMap K L :
        IdeleClassGroup (𝓞 L) L →* IdeleClassGroup (𝓞 K) K).range) ≃+
      (NormalLayer.ofOpenNormal (fixingOpenNormalSubgroup K L)).NormQuotient (globalFormation K) :=
  (NormalLayer.ofOpenNormal (fixingOpenNormalSubgroup K L)).normQuotientEquivOfGroundEquiv
    (globalFormation K) ((globalGroundEquiv K).trans
      (NormalLayer.groundEquivOfOpenNormal (globalFormation K) (fixingOpenNormalSubgroup K L)))
    (globalGroundEquiv_mem_layerNormSubgroup_iff K L)

/-- `globalLayerNormQuotientEquiv K L` sends the class of `c ∈ C_K` to the class of `c` in the
norm quotient of the layer. -/
@[simp]
theorem globalLayerNormQuotientEquiv_mk (c : IdeleClassGroup (𝓞 K) K) :
    globalLayerNormQuotientEquiv K L (.ofMul (c : IdeleClassGroup (𝓞 K) K ⧸
        (GlobalNumberFields.ideleClassNormMap K L :
          IdeleClassGroup (𝓞 L) L →* IdeleClassGroup (𝓞 K) K).range)) =
      (NormalLayer.ofOpenNormal (fixingOpenNormalSubgroup K L)).normQuotientMk (globalFormation K)
        (NormalLayer.groundEquivOfOpenNormal (globalFormation K) (fixingOpenNormalSubgroup K L)
          (globalGroundEquiv K (.ofMul c))) :=
  NormalLayer.normQuotientEquivOfGroundEquiv_mk _ _ _ _ c

end Layer

end TauCeti.ClassFieldTheory

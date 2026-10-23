/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Formation.AbsoluteArtinMap
public import TauCeti.NumberTheory.ClassFieldTheory.Global.IdeleClass.Level
public import TauCeti.NumberTheory.NumberField.Global.Ideles.Norm.Galois
import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Norm
import TauCeti.NumberTheory.ClassFieldTheory.ClassField
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

More generally, let `W' ≤ W` be any open subgroups of `G_K`, with fixed fields `F ⊆ L`; neither
`W'` need be normal in `W` nor `L/F` normal. The levels of `W` and `W'` are `C_F` and `C_L`
(`ideleClassLevelEquiv`), and the norm `Formation.levelNorm` between them is the norm map of idele
classes `N_{L/F} : C_L → C_F` (`levelNorm_ideleClassLevelEquiv`). The cosets of `W'` in `W` are
the `F`-embeddings of `L` into `Kˢ`, so `N_{L/F}(y)` is the product of the translates of `y ∈ L`
by their representatives (`TauCeti.coe_norm_eq_prod_quotient_out`); read in the normal closure `M`
of `L/K`, this product formula transfers to the ideles of `L`
(`TauCeti.GlobalNumberFields.ideleExtension_ideleNormMap_of_algebraMap_norm_eq_prod`), which is
the identity of the two norms. This is the form in which norms from finite extensions that are not
Galois, such as the extension cut out by an open subgroup of `G_K` that is not normal, are read on
idele class groups.

In particular, for an arbitrary layer `V ◁ U` of `globalFormation K`, whose ground subgroup `U` is
any open subgroup of `G_K`, with fixed fields `F` and `L`, the norm of the layer is
`N_{L/F} : C_L → C_F` (`NormalLayer.norm_ideleClassLevelEquiv`), and its norm quotient is
`C_F / N_{L/F}(C_L)` (`NormalLayer.ideleClassNormQuotientEquiv`). This is the form in which
statements about the layers of prime degree inside a given layer, whose ground fields need not be
`K`, are read on number fields.

This identifies the abstract norm quotient that the class formation axioms and the Artin map are
stated on with the concrete quotient `C_K / N_{E/K}(C_E)` that the fundamental inequalities and
global reciprocity are about.

## Main definitions

* `TauCeti.ClassFieldTheory.globalNormQuotientEquiv`: the norm quotient of the layer of `E` is
  `C_K / N_{E/K}(C_E)`.
* `TauCeti.ClassFieldTheory.globalLayerNormQuotientEquiv`: the norm quotient of the layer of a
  finite Galois extension `L/K` is `C_K / N_{L/K}(C_L)`.
* `TauCeti.ClassFieldTheory.NormalLayer.ideleClassNormQuotientEquiv`: the norm quotient of a layer
  whose ground and top subgroups have fixed fields `F` and `L` is `C_F / N_{L/F}(C_L)`.

## Main results

* `TauCeti.ClassFieldTheory.norm_ideleClassLevelEquiv`: the norm of the layer of `E` is the norm
  map of idele classes `N_{E/K}`.
* `TauCeti.ClassFieldTheory.globalGroundEquiv_mem_normSubgroup_iff`: an idele class of `K` lies
  in the norm subgroup of the layer of `E` exactly when it is a norm from `C_E`.
* `TauCeti.ClassFieldTheory.globalGroundEquiv_mem_layerNormSubgroup_iff`: the same for the layer
  of a finite Galois extension `L/K` and norms from `C_L`.
* `TauCeti.ClassFieldTheory.levelNorm_ideleClassLevelEquiv`: the norm between the levels of two
  open subgroups `W' ≤ W` with fixed fields `F ⊆ L` is the norm map of idele classes `N_{L/F}`.
* `TauCeti.ClassFieldTheory.NormalLayer.norm_ideleClassLevelEquiv`: the norm of a layer whose
  ground and top subgroups have fixed fields `F` and `L` is the norm map of idele classes
  `N_{L/F}`.
* `TauCeti.ClassFieldTheory.NormalLayer.ideleClassLevelEquiv_mem_normSubgroup_iff`: an idele class
  of `F` lies in the norm subgroup of such a layer exactly when it is a norm from `C_L`.

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
    ((globalFormation K).levelNorm h (ideleClassLevelEquiv hW (.ofMul c)) :
        (globalFormation K).toRep.V) =
      (globalGroundEquiv K (.ofMul (GlobalNumberFields.ideleClassNormMap K E c)) :
        (globalFormation K).toRep.V) := by
  subst hW₀
  induction c using QuotientGroup.induction_on with | H a => ?_
  -- Restricting the coset representatives of `W` to `E` runs through `Gal(E/K)` once each.
  have hprod := prod_restrictNormal_out hW fun σ ↦
    (Units.map (GlobalNumberFields.adeleGaloisAction K E σ) a : IdeleGroup (𝓞 E) E)
  rw [Formation.levelNorm_top_apply_coe, finsum_eq_sum_of_fintype, ideleClassLevelEquiv_mk,
    ideleCoeffOfIntermediateField_coe, GlobalNumberFields.ideleClassNormMap_mk,
    globalGroundEquiv_mk, ideleCoeffOf_bot_ideleExtension,
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
    (NormalLayer.ofOpenNormal V).norm (globalFormation K) (ideleClassLevelEquiv hV (.ofMul c)) =
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
  rw [NormalLayer.mem_normSubgroup, (ideleClassLevelEquiv hV).surjective.exists,
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

/-! ### Arbitrary layers -/

section FixedField

variable {F L : IntermediateField K (SeparableClosure K)} [NumberField F] [NumberField L]
  [Algebra F L] [IsScalarTower F L (SeparableClosure K)] (Lay : NormalLayer (AbsoluteGaloisGroup K))

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex in
/-- **The norm between two levels of the idele-class formation is the idele-class norm**: if the
open subgroups `W' ≤ W` of `G_K` have fixed fields `F ⊆ L`, then under the identifications of the
levels of `W` and `W'` with `C_F` and `C_L` (`ideleClassLevelEquiv`), the norm
`Formation.levelNorm` from the level of `W'` to that of `W` is the norm map of idele classes
`N_{L/F} : C_L → C_F`. The extension `L/F` need not be normal, nor `W'` normal in `W`. -/
theorem levelNorm_ideleClassLevelEquiv {W W' : OpenSubgroup (AbsoluteGaloisGroup K)}
    (h : W' ≤ W) (hF : fixedField W.toSubgroup = F) (hL : fixedField W'.toSubgroup = L)
    (c : IdeleClassGroup (𝓞 L) L) :
    (globalFormation K).levelNorm h (ideleClassLevelEquiv hL (.ofMul c)) =
      ideleClassLevelEquiv hF (.ofMul (GlobalNumberFields.ideleClassNormMap F L c)) := by
  refine Subtype.ext ?_
  induction c using QuotientGroup.induction_on with | H a => ?_
  -- Compute in the ideles of the normal closure `M` of `L/K`, which contains `F`.
  let M : Ω := FiniteGaloisIntermediateField.normalClosure K L
  have hLM : L ≤ M := FiniteGaloisIntermediateField.le_normalClosure K L
  have hFM : F ≤ M := (IntermediateField.le_of_isScalarTower (E := F) (E' := L)).trans hLM
  let := (IntermediateField.inclusion hLM).toRingHom.toAlgebra
  let := (IntermediateField.inclusion hFM).toRingHom.toAlgebra
  -- Read in `M`, the norm of `L/F` is the product of the conjugates by the coset representatives
  -- of `W'` in `W`, so the same holds for the idele norm.
  have hσ (y : L) : algebraMap F M (Algebra.norm F y) =
      ∏ q : W.toSubgroup ⧸ W'.toSubgroup.subgroupOf W.toSubgroup,
        ((q.out : AbsoluteGaloisGroup K).restrictNormal M).toRingEquiv (algebraMap L M y) := by
    refine Subtype.ext ((coe_norm_eq_prod_quotient_out hF hL y).trans ?_)
    rw [IntermediateField.coe_prod]
    exact Finset.prod_congr rfl fun q _ ↦
      (AlgEquiv.restrictNormal_commutes (q.out : AbsoluteGaloisGroup K) M (algebraMap L M y)).symm
  rw [Formation.levelNorm_apply_coe, finsum_eq_sum_of_fintype, ideleClassLevelEquiv_mk,
    GlobalNumberFields.ideleClassNormMap_mk, ideleClassLevelEquiv_mk,
    ← ideleCoeffOf_ideleExtension M hFM,
    GlobalNumberFields.ideleExtension_ideleNormMap_of_algebraMap_norm_eq_prod F L M _ hσ,
    ofMul_prod, map_sum, map_sum, map_sum]
  -- Each coset representative acts on the ideles of `M` through its restriction to `M`.
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  rw [← ideleCoeffOf_ideleExtension M hLM, ← ideleClassCoeffEquivGlobalFormation_smul,
    ← map_smul (ideleClassMk K), smul_ideleCoeffOf]
  exact congrArg (fun b ↦ ideleClassCoeffEquivGlobalFormation K (ideleClassMk K
    (ideleCoeffOf K M (.ofMul b)))) (Units.ext (GlobalNumberFields.adeleGaloisAction_apply K M _ _))

namespace NormalLayer

/-- **The norm of an arbitrary layer of the idele-class formation is the idele-class norm**: if the
ground and top subgroups of a layer `V ◁ U` of `globalFormation K` have fixed fields `F` and `L`,
then under the identifications of its ground and top levels with `C_F` and `C_L`
(`ideleClassLevelEquiv`), the norm of the layer is the norm map of idele classes
`N_{L/F} : C_L → C_F`. -/
theorem norm_ideleClassLevelEquiv (hF : fixedField Lay.ground.toSubgroup = F)
    (hL : fixedField Lay.top.toSubgroup = L) (c : IdeleClassGroup (𝓞 L) L) :
    Lay.norm (globalFormation K) (ideleClassLevelEquiv hL (.ofMul c)) =
      ideleClassLevelEquiv hF (.ofMul (GlobalNumberFields.ideleClassNormMap F L c)) := by
  rw [← LinearMap.toAddMonoidHom_coe, NormalLayer.toAddMonoidHom_norm]
  exact levelNorm_ideleClassLevelEquiv Lay.top_le_ground hF hL c

/-- **The norm subgroup of an arbitrary layer is `N_{L/F}(C_L)`**: if the ground and top subgroups
of a layer of `globalFormation K` have fixed fields `F` and `L`, an idele class of `F` lies in the
norm subgroup of the layer exactly when it is the norm of an idele class of `L`. -/
theorem ideleClassLevelEquiv_mem_normSubgroup_iff (hF : fixedField Lay.ground.toSubgroup = F)
    (hL : fixedField Lay.top.toSubgroup = L) (c : IdeleClassGroup (𝓞 F) F) :
    ideleClassLevelEquiv hF (.ofMul c) ∈ Lay.normSubgroup (globalFormation K) ↔
      c ∈ (GlobalNumberFields.ideleClassNormMap F L :
        IdeleClassGroup (𝓞 L) L →* IdeleClassGroup (𝓞 F) F).range := by
  rw [NormalLayer.mem_normSubgroup, (ideleClassLevelEquiv hL).surjective.exists,
    Additive.ofMul.surjective.exists, MonoidHom.mem_range]
  refine exists_congr fun x ↦ ?_
  rw [Lay.norm_ideleClassLevelEquiv hF hL, EmbeddingLike.apply_eq_iff_eq,
    EmbeddingLike.apply_eq_iff_eq, MonoidHom.coe_ofClass]

/-- **The norm quotient of an arbitrary layer is `C_F / N_{L/F}(C_L)`**: if the ground and top
subgroups of a layer of `globalFormation K` have fixed fields `F` and `L`, the identification
`ideleClassLevelEquiv` of `C_F` with the ground level descends to the quotients by
`N_{L/F}(C_L)` and by the norm subgroup of the layer. -/
def ideleClassNormQuotientEquiv (hF : fixedField Lay.ground.toSubgroup = F)
    (hL : fixedField Lay.top.toSubgroup = L) :
    Additive (IdeleClassGroup (𝓞 F) F ⧸ (GlobalNumberFields.ideleClassNormMap F L :
        IdeleClassGroup (𝓞 L) L →* IdeleClassGroup (𝓞 F) F).range) ≃+
      Lay.NormQuotient (globalFormation K) :=
  Lay.normQuotientEquivOfGroundEquiv (globalFormation K) (ideleClassLevelEquiv hF)
    (Lay.ideleClassLevelEquiv_mem_normSubgroup_iff hF hL)

/-- `ideleClassNormQuotientEquiv` sends the class of `c ∈ C_F` to the class of `c` in the norm
quotient of the layer. -/
@[simp]
theorem ideleClassNormQuotientEquiv_mk (hF : fixedField Lay.ground.toSubgroup = F)
    (hL : fixedField Lay.top.toSubgroup = L) (c : IdeleClassGroup (𝓞 F) F) :
    Lay.ideleClassNormQuotientEquiv hF hL (.ofMul (c : IdeleClassGroup (𝓞 F) F ⧸
        (GlobalNumberFields.ideleClassNormMap F L :
          IdeleClassGroup (𝓞 L) L →* IdeleClassGroup (𝓞 F) F).range)) =
      Lay.normQuotientMk (globalFormation K) (ideleClassLevelEquiv hF (.ofMul c)) :=
  NormalLayer.normQuotientEquivOfGroundEquiv_mk _ _ _ _ c

end NormalLayer

end FixedField

end TauCeti.ClassFieldTheory

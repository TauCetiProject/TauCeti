/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Formation.PrimeDegree
public import TauCeti.NumberTheory.ClassFieldTheory.Global.IdeleClass.Norm
public import TauCeti.NumberTheory.ClassFieldTheory.Global.IdeleClass.SIdeles
public import TauCeti.NumberTheory.ClassFieldTheory.UnitsLayer

/-!
# The layers of the idele-class formation as Galois modules

Let `K` be a number field, `V` an open normal subgroup of `G_K` and `E` its fixed field, a finite
Galois subextension of `Kˢ/K`. The layer `V ◁ G_K` of the idele-class formation
`globalFormation K` has Galois group `G_K ⧸ V` and coefficient module the level `(C_{Kˢ})^V`. This
file identifies the pair with the `Gal(E/K)`-module `C_E` of idele classes of `E`,
`TauCeti.ClassFieldTheory.ideleClassRep K E`:

* the Galois group `G_K ⧸ V` is `Gal(E/K)` by restriction to `E`
  (`TauCeti.ClassFieldTheory.layerGalEquivOfFixedField`);
* the coefficient module is `C_E` (`ideleClassLayerCoeffEquiv`, which is `ideleClassLevelEquiv`),
  and the two actions correspond (`ideleClassLayerCoeffEquiv_ρ`).

Consequently the cohomology of the layer is the Galois cohomology `Hⁿ(Gal(E/K), C_E)`
(`ideleClassLayerCohomologyEquiv`), its Tate cohomology is `\hat{H}ⁿ(Gal(E/K), C_E)` in every
integer degree (`ideleClassLayerTateCohomologyIso`), and its Herbrand quotient is the Herbrand
quotient of `C_E` (`herbrandQuotient_rep_ofOpenNormal_globalFormation`).

This is how the computation of `h(C_E)` on the idele classes of a number field
(`TauCeti.ClassFieldTheory.herbrandQuotient_ideleClassRep`) reaches the formation, where the
fundamental inequalities are stated. For a cyclic extension, `h(C_E) = [E : K]` gives the first
fundamental inequality `[C_K : N_{E/K}(C_E)] ≥ [E : K]`
(`finrank_le_natCard_ideleClassNormQuotient_of_herbrandQuotient_eq`), through the formation-level
`NormalLayer.degree_le_natCard_normQuotient_of_herbrandQuotient_eq` and the identification
`globalNormQuotientEquiv` of the norm quotient of the layer with `C_K / N_{E/K}(C_E)`.

## Main definitions

* `TauCeti.ClassFieldTheory.ideleClassLayerCoeffEquiv E hV`: `C_E` is the coefficient module of
  the layer of `V`.
* `TauCeti.ClassFieldTheory.ideleClassLayerCohomologyEquiv E hV n`: the cohomology of the layer is
  `Hⁿ(Gal(E/K), C_E)`.
* `TauCeti.ClassFieldTheory.ideleClassLayerTateCohomologyIso E hV n`: the Tate cohomology of the
  layer is `\hat{H}ⁿ(Gal(E/K), C_E)`.

## Main results

* `TauCeti.ClassFieldTheory.ideleClassLayerCoeffEquiv_ρ`: the coefficient identification is
  equivariant along `layerGalEquivOfFixedField`.
* `TauCeti.ClassFieldTheory.herbrandQuotient_rep_ofOpenNormal_globalFormation`: the Herbrand
  quotient of the layer is `h(C_E)`.
* `TauCeti.ClassFieldTheory.finrank_le_natCard_ideleClassNormQuotient_of_herbrandQuotient_eq`:
  for a cyclic extension `E/K` with `h(C_E) = [E : K]`, the norm index `[C_K : N_{E/K}(C_E)]` is at
  least `[E : K]`.

## References

* J. S. Milne, *Class Field Theory*, Chapter VII, §4, Corollary 4.4.
* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §§2 and 4.
-/

public section

noncomputable section

open IntermediateField NumberField

namespace TauCeti.ClassFieldTheory

variable {K : Type} [Field K] [NumberField K]

variable (E : FiniteGaloisIntermediateField K (SeparableClosure K))
  {V : OpenNormalSubgroup (AbsoluteGaloisGroup K)}
  (hV : fixedField (NormalLayer.ofOpenNormal V).top.toSubgroup = E)

/-! ### The coefficient module -/

/-- **The coefficient module of a layer of the idele-class formation is `C_E`**: if the fixed field
of the open normal subgroup `V` of `G_K` is `E`, the idele class group `C_E`, the module of
`ideleClassRep K E`, is the coefficient module `(C_{Kˢ})^V` of the layer `V ◁ G_K` of
`globalFormation K`, through `ideleClassLevelEquiv`. It intertwines the two Galois actions along
`layerGalEquivOfFixedField` (`ideleClassLayerCoeffEquiv_ρ`). -/
def ideleClassLayerCoeffEquiv :
    (ideleClassRep K E).V ≃ₗ[ℤ] ((NormalLayer.ofOpenNormal V).rep (globalFormation K)).V :=
  (ideleClassLevelEquiv E hV).toIntLinearEquiv

/-- `ideleClassLayerCoeffEquiv` is `ideleClassLevelEquiv`. -/
@[simp]
theorem ideleClassLayerCoeffEquiv_apply (c : Additive (IdeleClassGroup (𝓞 E) E)) :
    ideleClassLayerCoeffEquiv E hV c = ideleClassLevelEquiv E hV c :=
  (rfl)

/-- `ideleClassLayerCoeffEquiv` is equivariant: `τ ∈ Gal(E/K)` acts on `C_E` as the class of any
`σ ∈ G_K` restricting to `τ` acts on the coefficient module of the layer. -/
theorem ideleClassLayerCoeffEquiv_ρ (τ : Gal(E/K)) (c : (ideleClassRep K E).V) :
    ideleClassLayerCoeffEquiv E hV ((ideleClassRep K E).ρ τ c) =
      ((NormalLayer.ofOpenNormal V).rep (globalFormation K)).ρ
        ((layerGalEquivOfFixedField hV).symm τ) (ideleClassLayerCoeffEquiv E hV c) := by
  obtain ⟨γ, rfl⟩ := (layerGalEquivOfFixedField hV).surjective τ
  rw [MulEquiv.symm_apply_apply]
  induction γ using QuotientGroup.induction_on with | H σ => ?_
  obtain ⟨a, rfl⟩ : ∃ a : IdeleGroup (𝓞 E) E,
      (Additive.ofMul (a : IdeleClassGroup (𝓞 E) E) : (ideleClassRep K E).V) = c :=
    (QuotientGroup.mk_surjective (Additive.toMul c)).imp fun _ ha ↦ congrArg Additive.ofMul ha
  -- The restriction of `σ` to `E` acts on the class of an idele `a` of `E` through its action on
  -- the adeles of `E`, which is how `σ` acts on `a` read as an idele of `Kˢ`.
  have hτ : (ideleClassRep K E).ρ (layerGalEquivOfFixedField hV (σ : _))
      (Additive.ofMul (a : IdeleClassGroup (𝓞 E) E)) =
        Additive.ofMul ((Units.map (GlobalNumberFields.adeleGaloisAction K E
          ((σ : AbsoluteGaloisGroup K).restrictNormal E)) a : IdeleGroup (𝓞 E) E) :
            IdeleClassGroup (𝓞 E) E) := by
    rw [layerGalEquivOfFixedField_mk]
    exact congrArg (fun z : IdeleGroup (𝓞 E) E ↦ Additive.ofMul (z : IdeleClassGroup (𝓞 E) E))
      (GlobalNumberFields.idele_smul_def _ a)
  refine (congrArg (ideleClassLayerCoeffEquiv E hV) hτ).trans (Subtype.ext ?_)
  exact (ideleClassLevelEquiv_smul E hV (σ : AbsoluteGaloisGroup K) a).trans
    (NormalLayer.rep_ρ_mk_apply_coe _ _ σ _).symm

/-- `ideleClassLayerCoeffEquiv` and the inverse of `layerGalEquivOfFixedField` form a compatible
pair, in the form taken by the change-of-group maps of Tate cohomology. -/
theorem isIntertwiningMap_ideleClassLayerCoeffEquiv :
    (ideleClassRep K E).ρ.IsIntertwiningMap
      (((NormalLayer.ofOpenNormal V).rep (globalFormation K)).ρ.comp
        ((layerGalEquivOfFixedField hV).symm : Gal(E/K) →* (NormalLayer.ofOpenNormal V).Gal))
      (ideleClassLayerCoeffEquiv E hV :
        (ideleClassRep K E).V →ₗ[ℤ] ((NormalLayer.ofOpenNormal V).rep (globalFormation K)).V) :=
  ⟨ideleClassLayerCoeffEquiv_ρ E hV⟩

/-! ### Cohomology and the Herbrand quotient -/

/-- **The cohomology of a layer of the idele-class formation is the Galois cohomology of the
idele classes**: if the fixed field of the open normal subgroup `V` of `G_K` is `E`, then
`Hⁿ(G_K ⧸ V, (C_{Kˢ})^V) ≃ Hⁿ(Gal(E/K), C_E)` in every degree `n`. -/
def ideleClassLayerCohomologyEquiv (n : ℕ) :
    (NormalLayer.ofOpenNormal V).H (globalFormation K) n ≃+
      groupCohomology (ideleClassRep K E) n :=
  (groupCohomology.mapIso (layerGalEquivOfFixedField hV).symm (ideleClassLayerCoeffEquiv E hV)
    (fun τ ↦ LinearMap.ext (ideleClassLayerCoeffEquiv_ρ E hV τ)) n).toLinearEquiv.toAddEquiv.symm

/-- **The Tate cohomology of a layer of the idele-class formation is the Tate cohomology of the
idele classes**: if the fixed field of the open normal subgroup `V` of `G_K` is `E`, then
`\hat{H}ⁿ(G_K ⧸ V, (C_{Kˢ})^V) ≅ \hat{H}ⁿ(Gal(E/K), C_E)` in every integer degree `n`. -/
def ideleClassLayerTateCohomologyIso (n : ℤ) :
    (NormalLayer.ofOpenNormal V).TateH (globalFormation K) n ≅
      tateCohomology (ideleClassRep K E) n :=
  (TateCohomology.mapIso (isIntertwiningMap_ideleClassLayerCoeffEquiv E hV) n).symm

include hV in
/-- **The Herbrand quotient of a layer of the idele-class formation is that of the idele
classes**: if the fixed field of the open normal subgroup `V` of `G_K` is `E`, the coefficient
module of the layer `V ◁ G_K` of `globalFormation K` has Herbrand quotient `h(C_E)`, computed for
the action of `Gal(E/K)`. -/
theorem herbrandQuotient_rep_ofOpenNormal_globalFormation :
    TateCohomology.herbrandQuotient ((NormalLayer.ofOpenNormal V).rep (globalFormation K)) =
      TateCohomology.herbrandQuotient (ideleClassRep K E) :=
  (TateCohomology.herbrandQuotient_eq_of_isIntertwiningMap
    (isIntertwiningMap_ideleClassLayerCoeffEquiv E hV)).symm

/-! ### The first fundamental inequality -/

/-- **The first fundamental inequality from the Herbrand quotient of the idele classes**: if `E/K`
is cyclic and the idele classes of `E` have Herbrand quotient `h(C_E) = [E : K]`, then the norm
index `[C_K : N_{E/K}(C_E)]` is at least `[E : K]`. -/
theorem finrank_le_natCard_ideleClassNormQuotient_of_herbrandQuotient_eq [IsCyclic Gal(E/K)]
    (h : TateCohomology.herbrandQuotient (ideleClassRep K E) = Module.finrank K E) :
    Module.finrank K E ≤ Nat.card (IdeleClassGroup (𝓞 K) K ⧸
      (GlobalNumberFields.ideleClassNormMap K E :
        IdeleClassGroup (𝓞 E) E →* IdeleClassGroup (𝓞 K) K).range) := by
  -- The layer of the subgroup fixing `E`, whose fixed field is `E`.
  have hV : fixedField (NormalLayer.ofOpenNormal (fixingOpenNormalSubgroup K E)).top.toSubgroup =
      E :=
    (fixedField_top_ofOpenNormal_fixingOpenNormalSubgroup
      (E : IntermediateField K (SeparableClosure K)).val).trans (fieldRange_val _)
  have : IsCyclic (NormalLayer.ofOpenNormal (fixingOpenNormalSubgroup K E)).Gal :=
    isCyclic_of_surjective (layerGalEquivOfFixedField hV).symm.toMonoidHom
      (layerGalEquivOfFixedField hV).symm.surjective
  have hdeg : (NormalLayer.ofOpenNormal (fixingOpenNormalSubgroup K E)).degree =
      Module.finrank K E := by
    rw [NormalLayer.degree_eq_natCard_gal, Nat.card_congr (layerGalEquivOfFixedField hV).toEquiv,
      IsGalois.card_aut_eq_finrank]
  rw [← hdeg, Nat.card_congr (Additive.ofMul.trans (globalNormQuotientEquiv E hV).toEquiv)]
  refine NormalLayer.degree_le_natCard_normQuotient_of_herbrandQuotient_eq _ _ ?_
  rw [herbrandQuotient_rep_ofOpenNormal_globalFormation E hV, h, hdeg]

end TauCeti.ClassFieldTheory

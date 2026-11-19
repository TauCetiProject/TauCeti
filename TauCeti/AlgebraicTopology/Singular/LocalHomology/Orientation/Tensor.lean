/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.Prod
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import TauCeti.Algebra.Category.ModuleCat.Monoidal.Unit

/-!
# The tensor identification of orientation lines of vector spaces

For a real normed space `E` of dimension `m + 1`, the integral orientation line of `E` is the
local homology group `o_E = Hₘ₊₁(E, E ∖ {0}; ℤ)`, free of rank one over `ℤ`. This file constructs
the ordered identification of orientation lines

`o_E ⊗ o_F ≅ o_{E × F}`

as an isomorphism in the monoidal category of `ℤ`-modules (`TauCeti.LocalOrientation.tensorIso`).
It sends `z ⊗ z'` to the ordered product `z × z'` (`TauCeti.LocalOrientation.prod`) for all local
orientations `z` of `E` and `z'` of `F` at the origin
(`TauCeti.LocalOrientation.tensorIso_hom_tmul`); this determines it, because a local orientation
identifies `ℤ` with its orientation line (`TauCeti.IsLocalOrientation.linearEquiv`).

The laws of the generator-level product become laws of the isomorphism.

* It is natural in continuous linear equivalences `f : E ≃L[ℝ] E'` and `g : F ≃L[ℝ] F'`: it
  intertwines the tensor product of the maps they induce on orientation lines with the map induced
  by `f × g` (`TauCeti.LocalOrientation.tensorIso_hom_naturality`).
* Exchanging the factors acts by the Koszul sign: the map induced by `E × F ≃ F × E` corresponds to
  `(-1) ^ ((m + 1) * (n + 1))` times the braiding `o_E ⊗ o_F ≅ o_F ⊗ o_E`
  (`TauCeti.LocalOrientation.tensorIso_hom_comp_prodComm`).
* It is associative: the map induced by `(E × F) × G ≃ E × (F × G)` corresponds to the associator
  `(o_E ⊗ o_F) ⊗ o_G ≅ o_E ⊗ (o_F ⊗ o_G)` (`TauCeti.LocalOrientation.tensorIso_hom_comp_prodAssoc`).

As in `TauCeti.LocalOrientation.prod`, the factors have positive dimension and the degree of the
product is written `d + 1` together with a proof of `(m + 1) + (n + 1) = d + 1`. The spaces live
in `Type`, so that the orientation lines are objects of `ModuleCat.{0} ℤ`, where Mathlib's
monoidal structure on modules over `ℤ` lives.

## Main definitions

* `TauCeti.LocalOrientation.tensorIso`: the isomorphism `o_E ⊗ o_F ≅ o_{E × F}`.

## Main results

* `TauCeti.LocalOrientation.tensorIso_hom_tmul`: it sends `z ⊗ z'` to `z × z'`.
* `TauCeti.LocalOrientation.tensorIso_hom_naturality`: naturality.
* `TauCeti.LocalOrientation.tensorIso_hom_comp_prodComm`: the exchange sign.
* `TauCeti.LocalOrientation.tensorIso_hom_comp_prodAssoc`: associativity.

## References

* J. Pardon, *An algebraic approach to virtual fundamental cycles on moduli spaces of
  pseudo-holomorphic curves*, Geom. Topol. 20 (2016), Definition 4.1.1 and Appendix A.0
  (orientation lines and the ordering of their tensor products).
-/
public section

noncomputable section

open CategoryTheory MonoidalCategory Module

namespace TauCeti.LocalOrientation

variable {E F G E' F' : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedAddCommGroup F'] [NormedSpace ℝ F']
  {m n p d : ℕ}

/-- The identification of the orientation line `o_E` with the unit `ℤ` of the tensor product,
sending a local orientation `z` of `E` at the origin to `1`. -/
private def unitIso (hE : finrank ℝ E = m + 1) (z : LocalOrientation E 0 (m + 1)) :
    localHomology (A := ModuleCat.{0} ℤ) (ModuleCat.of ℤ (ULift.{0} ℤ)) ({0} : Set E) (m + 1) ≅
      𝟙_ (ModuleCat.{0} ℤ) :=
  (z.property.linearEquiv (singularHomologyComplZeroIso hE)).symm.toModuleIso

@[simp]
private theorem unitIso_inv_one (hE : finrank ℝ E = m + 1) (z : LocalOrientation E 0 (m + 1)) :
    (unitIso hE z).inv.hom (1 : ℤ) = z.val :=
  IsLocalOrientation.linearEquiv_apply_one _ _

/-- The identification of `o_E ⊗ o_F` with the unit `ℤ`, sending `z ⊗ z'` to `1`. -/
private def tensorUnitIso (hE : finrank ℝ E = m + 1) (hF : finrank ℝ F = n + 1)
    (z : LocalOrientation E 0 (m + 1)) (z' : LocalOrientation F 0 (n + 1)) :
    (localHomology (A := ModuleCat.{0} ℤ) (ModuleCat.of ℤ (ULift.{0} ℤ)) ({0} : Set E) (m + 1)) ⊗
      (localHomology (A := ModuleCat.{0} ℤ) (ModuleCat.of ℤ (ULift.{0} ℤ)) ({0} : Set F) (n + 1)) ≅
      𝟙_ (ModuleCat.{0} ℤ) :=
  (unitIso hE z ⊗ᵢ unitIso hF z') ≪≫ λ_ _

@[simp]
private theorem tensorUnitIso_inv_one (hE : finrank ℝ E = m + 1) (hF : finrank ℝ F = n + 1)
    (z : LocalOrientation E 0 (m + 1)) (z' : LocalOrientation F 0 (n + 1)) :
    (tensorUnitIso hE hF z z').inv.hom (1 : ℤ) = z.val ⊗ₜ[ℤ] z'.val := by
  simp [tensorUnitIso]

@[simp]
private theorem tensorUnitIso_hom_tmul (hE : finrank ℝ E = m + 1) (hF : finrank ℝ F = n + 1)
    (z : LocalOrientation E 0 (m + 1)) (z' : LocalOrientation F 0 (n + 1)) :
    (tensorUnitIso hE hF z z').hom.hom (z.val ⊗ₜ[ℤ] z'.val) = 1 := by
  rw [← tensorUnitIso_inv_one hE hF, Iso.inv_hom_id_apply]

/-- **The tensor identification of orientation lines.** For real normed spaces `E` and `F` of
dimensions `m + 1` and `n + 1`, the isomorphism `o_E ⊗ o_F ≅ o_{E × F}` of integral orientation
lines sending `z ⊗ z'` to the ordered product `z × z'` of local orientations
(`TauCeti.LocalOrientation.tensorIso_hom_tmul`). -/
def tensorIso (hE : finrank ℝ E = m + 1) (hF : finrank ℝ F = n + 1)
    (hd : m + 1 + (n + 1) = d + 1) :
    (localHomology (A := ModuleCat.{0} ℤ) (ModuleCat.of ℤ (ULift.{0} ℤ)) ({0} : Set E) (m + 1)) ⊗
      (localHomology (A := ModuleCat.{0} ℤ) (ModuleCat.of ℤ (ULift.{0} ℤ)) ({0} : Set F) (n + 1)) ≅
      localHomology (A := ModuleCat.{0} ℤ) (ModuleCat.of ℤ (ULift.{0} ℤ)) ({0} : Set (E × F))
        (d + 1) :=
  haveI := exists_localOrientation_of_chart (0 : E) hE
  haveI := exists_localOrientation_of_chart (0 : F) hF
  let z := Classical.arbitrary (LocalOrientation E 0 (m + 1))
  let z' := Classical.arbitrary (LocalOrientation F 0 (n + 1))
  tensorUnitIso hE hF z z' ≪≫ (unitIso (finrank_prod_eq_succ hE hF hd) (prod hE hF hd z z')).symm

/-- The tensor identification sends `z ⊗ z'` to the ordered product `z × z'`. -/
@[simp]
theorem tensorIso_hom_tmul (hE : finrank ℝ E = m + 1) (hF : finrank ℝ F = n + 1)
    (hd : m + 1 + (n + 1) = d + 1) (z : LocalOrientation E 0 (m + 1))
    (z' : LocalOrientation F 0 (n + 1)) :
    (tensorIso hE hF hd).hom.hom (z.val ⊗ₜ[ℤ] z'.val) = (prod hE hF hd z z').val := by
  have := exists_localOrientation_of_chart (0 : E) hE
  have := exists_localOrientation_of_chart (0 : F) hF
  -- The identification sends the chosen pair of generators to their product by construction; the
  -- other local orientations differ from the chosen ones by signs, which both sides pull out.
  have key : (tensorIso hE hF hd).hom.hom
      ((Classical.arbitrary (LocalOrientation E 0 (m + 1))).val ⊗ₜ
        (Classical.arbitrary (LocalOrientation F 0 (n + 1))).val) =
      (prod hE hF hd (Classical.arbitrary _) (Classical.arbitrary _)).val := by
    simp [tensorIso]
  rcases eq_or_eq_neg (singularHomologyComplZeroIso hE) z (Classical.arbitrary _)
    with rfl | rfl <;>
    rcases eq_or_eq_neg (singularHomologyComplZeroIso hF) z' (Classical.arbitrary _)
      with rfl | rfl <;>
    simp [key, TensorProduct.neg_tmul, TensorProduct.tmul_neg]

/-- The inverse of the tensor identification sends `z × z'` to `z ⊗ z'`. -/
@[simp]
theorem tensorIso_inv_prod (hE : finrank ℝ E = m + 1) (hF : finrank ℝ F = n + 1)
    (hd : m + 1 + (n + 1) = d + 1) (z : LocalOrientation E 0 (m + 1))
    (z' : LocalOrientation F 0 (n + 1)) :
    (tensorIso hE hF hd).inv.hom (prod hE hF hd z z').val = z.val ⊗ₜ[ℤ] z'.val := by
  rw [← tensorIso_hom_tmul hE hF hd z z', Iso.hom_inv_id_apply]

/-- **Naturality of the tensor identification.** For continuous linear equivalences
`f : E ≃L[ℝ] E'` and `g : F ≃L[ℝ] F'`, identifying `o_E' ⊗ o_F'` with `o_{E' × F'}` after
transporting along `f` and `g` agrees with transporting along `f × g` after identifying
`o_E ⊗ o_F` with `o_{E × F}`. -/
@[reassoc]
theorem tensorIso_hom_naturality (hE : finrank ℝ E = m + 1) (hF : finrank ℝ F = n + 1)
    (hE' : finrank ℝ E' = m + 1) (hF' : finrank ℝ F' = n + 1) (hd : m + 1 + (n + 1) = d + 1)
    (f : E ≃L[ℝ] E') (g : F ≃L[ℝ] F') :
    (TopPair.singularHomologyMap f.complZeroPairIso.hom (ModuleCat.of ℤ (ULift.{0} ℤ)) (m + 1) ⊗ₘ
        TopPair.singularHomologyMap g.complZeroPairIso.hom (ModuleCat.of ℤ (ULift.{0} ℤ)) (n + 1)) ≫
        (tensorIso hE' hF' hd).hom =
      (tensorIso hE hF hd).hom ≫ TopPair.singularHomologyMap (f.prodCongr g).complZeroPairIso.hom
        (ModuleCat.of ℤ (ULift.{0} ℤ)) (d + 1) := by
  obtain ⟨z⟩ := exists_localOrientation_of_chart (0 : E) hE
  obtain ⟨z'⟩ := exists_localOrientation_of_chart (0 : F) hF
  -- Both sides are determined by their value on `z ⊗ z'`, which corresponds to `1 : ℤ`.
  refine ModuleCat.hom_ext_of_iso_tensorUnit (tensorUnitIso hE hF z z') ?_
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, tensorUnitIso_inv_one,
    ModuleCat.MonoidalCategory.tensorHom_tmul, tensorIso_hom_tmul]
  rw [← coe_map, ← coe_map, tensorIso_hom_tmul, prod_map_complZeroPairIso, coe_map]

/-- **The exchange sign of the tensor identification.** Transport along the exchange
`E × F ≃ F × E` corresponds to `(-1) ^ ((m + 1) * (n + 1))` times the exchange of tensor factors
`o_E ⊗ o_F ≅ o_F ⊗ o_E`, where `m + 1` and `n + 1` are the dimensions of `E` and `F`. -/
@[reassoc]
theorem tensorIso_hom_comp_prodComm (hE : finrank ℝ E = m + 1) (hF : finrank ℝ F = n + 1)
    (hd : m + 1 + (n + 1) = d + 1) (hd' : n + 1 + (m + 1) = d + 1) :
    (tensorIso hE hF hd).hom ≫ TopPair.singularHomologyMap
        (ContinuousLinearEquiv.prodComm ℝ E F).complZeroPairIso.hom
        (ModuleCat.of ℤ (ULift.{0} ℤ)) (d + 1) =
      (-1 : ℤ) ^ ((m + 1) * (n + 1)) • ((β_ _ _).hom ≫ (tensorIso hF hE hd').hom) := by
  obtain ⟨z⟩ := exists_localOrientation_of_chart (0 : E) hE
  obtain ⟨z'⟩ := exists_localOrientation_of_chart (0 : F) hF
  -- Both sides are determined by their value on `z ⊗ z'`, which corresponds to `1 : ℤ`.
  refine ModuleCat.hom_ext_of_iso_tensorUnit (tensorUnitIso hE hF z z') ?_
  simp only [ModuleCat.hom_comp, ModuleCat.hom_smul, LinearMap.comp_apply, LinearMap.smul_apply,
    tensorUnitIso_inv_one, tensorIso_hom_tmul, ModuleCat.MonoidalCategory.braiding_hom_apply]
  rw [← coe_map, coe_map_prodComm_prod hE hF hd hd']
  -- The braiding produces `z' ⊗ z` in Mathlib's tensor product object, whose module structure
  -- agrees with the one in `tensorIso_hom_tmul` only after unfolding, so `rw` cannot match it.
  exact congrArg _ (tensorIso_hom_tmul hF hE hd' z' z).symm

/-- **Associativity of the tensor identification.** Transport along `(E × F) × G ≃ E × (F × G)`
corresponds to the associator `(o_E ⊗ o_F) ⊗ o_G ≅ o_E ⊗ (o_F ⊗ o_G)` of tensor products. -/
@[reassoc]
theorem tensorIso_hom_comp_prodAssoc {e f : ℕ} (hE : finrank ℝ E = m + 1)
    (hF : finrank ℝ F = n + 1) (hG : finrank ℝ G = p + 1) (he : m + 1 + (n + 1) = e + 1)
    (hf : n + 1 + (p + 1) = f + 1) (hd : e + 1 + (p + 1) = d + 1)
    (he' : m + 1 + (f + 1) = d + 1) :
    ((tensorIso hE hF he).hom ▷ _) ≫ (tensorIso (finrank_prod_eq_succ hE hF he) hG hd).hom ≫
        TopPair.singularHomologyMap (ContinuousLinearEquiv.prodAssoc ℝ E F G).complZeroPairIso.hom
          (ModuleCat.of ℤ (ULift.{0} ℤ)) (d + 1) =
      (α_ _ _ _).hom ≫ (_ ◁ (tensorIso hF hG hf).hom) ≫
        (tensorIso hE (finrank_prod_eq_succ hF hG hf) he').hom := by
  obtain ⟨z⟩ := exists_localOrientation_of_chart (0 : E) hE
  obtain ⟨z'⟩ := exists_localOrientation_of_chart (0 : F) hF
  obtain ⟨z''⟩ := exists_localOrientation_of_chart (0 : G) hG
  -- Both sides are determined by their value on `(z ⊗ z') ⊗ z''`, which corresponds to `1 : ℤ`.
  refine ModuleCat.hom_ext_of_iso_tensorUnit
    ((tensorUnitIso hE hF z z' ⊗ᵢ unitIso hG z'') ≪≫ λ_ _) ?_
  simp only [Iso.trans_inv, ModuleCat.hom_comp, LinearMap.comp_apply, tensorIso_inv,
    ModuleCat.MonoidalCategory.tensorHom_tmul, ModuleCat.MonoidalCategory.leftUnitor_inv_apply,
    tensorUnitIso_inv_one, unitIso_inv_one, ModuleCat.MonoidalCategory.whiskerRight_apply,
    ModuleCat.MonoidalCategory.associator_hom_apply, tensorIso_hom_tmul]
  rw [← coe_map, map_prodAssoc_prod hE hF hG he hf hd he', ModuleCat.hom_whiskerLeft]
  -- As for the braiding, the associator produces `z ⊗ (z' ⊗ z'')` in Mathlib's tensor product
  -- object, which `tensorIso_hom_tmul` matches only after unfolding.
  exact (tensorIso_hom_tmul hE _ he' z _).symm.trans
    (congrArg _ (congrArg _ (tensorIso_hom_tmul hF hG hf z' z'').symm))

end TauCeti.LocalOrientation

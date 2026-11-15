/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Monoidal.Homology.Kunneth.Basic
public import TauCeti.Algebra.Homology.Monoidal.KoszulBraiding

/-!
# The Künneth map and the interchange of factors

For nonnegative chain complexes `K` and `L` in a braided preadditive monoidal category, the Koszul
interchange `K ⊗ L ⟶ L ⊗ K` (`TauCeti.NatChainComplex.koszulBraidingHom`) sends the tensor
product `x ⊗ y` of cycles of degrees `p` and `q` to `(-1)^(p * q) • y ⊗ x`.  So on homology it
sends the cross product `x × y` to `(-1)^(p * q) • y × x`
(`TauCeti.NatChainComplex.homologyCross_comp_homologyMap_koszulBraidingHom`).

In a braided category, the signed interchange of the summands `Hₚ(K) ⊗ H_q(L)` is an
isomorphism of the sources of the Künneth maps, so the Künneth map of `K` and `L` is an
isomorphism exactly when that of `L` and `K` is
(`TauCeti.NatChainComplex.isIso_homologyKunneth_comm`).
In particular the Künneth theorem for a factor with zero differentials and flat terms holds with
that factor on either side (`HomologicalComplex.isIso_homologyKunneth_of_d_eq_zero_of_flat_right`).
With the factor on the right, it computes the homology of `K ⊗ Z(L)` for the complex of cycles
`Z(L)`, as the Künneth short exact sequence requires
(`HomologicalComplex.homologyKunnethShortComplex_shortExact`).

## Main results

* `TauCeti.NatChainComplex.cyclesCross_comp_cyclesMap_koszulBraidingHom` and
  `TauCeti.NatChainComplex.homologyCross_comp_homologyMap_koszulBraidingHom`: interchange on
  tensor products of cycles and on cross products.
* `TauCeti.NatChainComplex.isIso_homologyKunneth_comm`: symmetry of the Künneth theorem.
* `HomologicalComplex.isIso_homologyKunneth_of_d_eq_zero_of_flat_right`: the Künneth theorem when
  the second complex of modules has zero differentials and flat terms.

## References

* C. Weibel, *An Introduction to Homological Algebra*, Section 3.6, the Künneth formula.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory HomologicalComplex

namespace TauCeti.NatChainComplex

variable {C : Type*} [Category* C] [Preadditive C] [MonoidalCategory C] [MonoidalPreadditive C]
  (K L : ChainComplex C ℕ) [K.HasTensor L] [L.HasTensor K]

section Braided

variable [BraidedCategory C]

section Cycles

variable (p q n : ℕ) (h : p + q = n) [K.HasHomology p] [L.HasHomology q]
  [(tensorObj K L).HasHomology n] [(tensorObj L K).HasHomology n]

/-- Koszul interchange sends the tensor product of cycles `x ⊗ y` to `(-1)^(p*q) • y ⊗ x`. -/
@[reassoc]
lemma cyclesCross_comp_cyclesMap_koszulBraidingHom :
    cyclesCross K L p q n h ≫ cyclesMap (koszulBraidingHom K L) n =
      ((-1 : ℤ) ^ (p * q)) • ((β_ (K.cycles p) (L.cycles q)).hom ≫
        cyclesCross L K q p n (by omega)) := by
  rw [← cancel_mono ((tensorObj L K).iCycles n)]
  simp [BraidedCategory.braiding_naturality_assoc]

end Cycles

section Homology

variable (p q n : ℕ) (h : p + q = n) [K.HasHomology p] [L.HasHomology q]
  [(tensorObj K L).HasHomology n] [(tensorObj L K).HasHomology n]
  [PreservesColimitsOfShape WalkingParallelPair (tensorLeft (K.homology p))]
  [PreservesColimitsOfShape WalkingParallelPair (tensorRight (L.cycles q))]
  [PreservesColimitsOfShape WalkingParallelPair (tensorRight (L.X ((ComplexShape.down ℕ).prev q)))]
  [PreservesColimitsOfShape WalkingParallelPair (tensorLeft (L.homology q))]
  [PreservesColimitsOfShape WalkingParallelPair (tensorRight (K.cycles p))]
  [PreservesColimitsOfShape WalkingParallelPair (tensorRight (K.X ((ComplexShape.down ℕ).prev p)))]

/-- Koszul interchange on homology: the cross product `x × y` is sent to
`(-1)^(p*q) • y × x`. -/
@[reassoc]
lemma homologyCross_comp_homologyMap_koszulBraidingHom :
    homologyCross K L p q n h ≫ homologyMap (koszulBraidingHom K L) n =
      ((-1 : ℤ) ^ (p * q)) • ((β_ (K.homology p) (L.homology q)).hom ≫
        homologyCross L K q p n (by omega)) := by
  refine homology_tensor_homology_hom_ext K L p q ?_
  simp [cyclesCross_comp_cyclesMap_koszulBraidingHom_assoc,
    BraidedCategory.braiding_naturality_assoc]

end Homology

end Braided

section Kunneth

variable [BraidedCategory C]

variable (n : ℕ) [∀ p, K.HasHomology p] [∀ q, L.HasHomology q]
  [(tensorObj K L).HasHomology n] [(tensorObj L K).HasHomology n]
  [∀ p, PreservesColimitsOfShape WalkingParallelPair (tensorLeft (K.homology p))]
  [∀ q, PreservesColimitsOfShape WalkingParallelPair (tensorRight (L.cycles q))]
  [∀ q, PreservesColimitsOfShape WalkingParallelPair
    (tensorRight (L.X ((ComplexShape.down ℕ).prev q)))]
  [∀ q, PreservesColimitsOfShape WalkingParallelPair (tensorLeft (L.homology q))]
  [∀ p, PreservesColimitsOfShape WalkingParallelPair (tensorRight (K.cycles p))]
  [∀ p, PreservesColimitsOfShape WalkingParallelPair
    (tensorRight (K.X ((ComplexShape.down ℕ).prev p)))]
  [GradedObject.HasTensor (fun p ↦ K.homology p) (fun q ↦ L.homology q)]
  [GradedObject.HasTensor (fun q ↦ L.homology q) (fun p ↦ K.homology p)]

/-- **The Künneth map is symmetric**: in a braided category, the Künneth map of `K` and `L`
is an isomorphism exactly when that of `L` and `K` is, since Koszul interchange identifies them. -/
theorem isIso_homologyKunneth_comm :
    IsIso (homologyKunneth K L n) ↔ IsIso (homologyKunneth L K n) := by
  -- the signed interchange of the summands `Hₚ(K) ⊗ H_q(L)` of degree `n`; it differs from
  -- Mathlib's `GradedObject.Monoidal.braiding` by the Koszul sign `(-1)^(p * q)`
  let σ (X Y : GradedObject ℕ C) [GradedObject.HasTensor X Y] [GradedObject.HasTensor Y X] :
      GradedObject.Monoidal.tensorObj X Y n ⟶ GradedObject.Monoidal.tensorObj Y X n :=
    GradedObject.Monoidal.tensorObjDesc fun p q h ↦ ((-1 : ℤ) ^ (p * q)) •
      ((β_ (X p) (Y q)).hom ≫ GradedObject.Monoidal.ιTensorObj Y X q p n (by omega))
  -- its inverse, the signed inverse interchange
  let τ (X Y : GradedObject ℕ C) [GradedObject.HasTensor X Y] [GradedObject.HasTensor Y X] :
      GradedObject.Monoidal.tensorObj Y X n ⟶ GradedObject.Monoidal.tensorObj X Y n :=
    GradedObject.Monoidal.tensorObjDesc fun q p h ↦ ((-1 : ℤ) ^ (p * q)) •
      ((β_ (X p) (Y q)).inv ≫ GradedObject.Monoidal.ιTensorObj X Y p q n (by omega))
  have hστ (X Y : GradedObject ℕ C) [GradedObject.HasTensor X Y] [GradedObject.HasTensor Y X] :
      σ X Y ≫ τ X Y = 𝟙 _ := by
    refine GradedObject.Monoidal.tensorObj_ext _ _ fun p q h ↦ ?_
    simp only [σ, τ, GradedObject.Monoidal.ι_tensorObjDesc_assoc, Preadditive.zsmul_comp,
      Category.assoc, GradedObject.Monoidal.ι_tensorObjDesc, Preadditive.comp_zsmul, smul_smul,
      Iso.hom_inv_id_assoc, Category.comp_id]
    rw [← pow_add, ← two_mul, pow_mul]
    simp
  have hτσ (X Y : GradedObject ℕ C) [GradedObject.HasTensor X Y] [GradedObject.HasTensor Y X] :
      τ X Y ≫ σ X Y = 𝟙 _ := by
    refine GradedObject.Monoidal.tensorObj_ext _ _ fun q p h ↦ ?_
    simp only [σ, τ, GradedObject.Monoidal.ι_tensorObjDesc_assoc, Preadditive.zsmul_comp,
      Category.assoc, GradedObject.Monoidal.ι_tensorObjDesc, Preadditive.comp_zsmul, smul_smul,
      Iso.inv_hom_id_assoc, Category.comp_id]
    rw [← pow_add, ← two_mul, pow_mul]
    simp
  -- Koszul interchange carries the Künneth map of `K` and `L` to that of `L` and `K`
  have hκ : homologyKunneth K L n ≫ homologyMap (koszulBraidingHom K L) n =
      σ _ _ ≫ homologyKunneth L K n := by
    refine GradedObject.Monoidal.tensorObj_ext _ _ fun p q h ↦ ?_
    simp [σ, homologyCross_comp_homologyMap_koszulBraidingHom]
  have : IsIso (σ (fun p ↦ K.homology p) (fun q ↦ L.homology q)) := ⟨τ _ _, hστ _ _, hτσ _ _⟩
  rw [← isIso_comp_right_iff _ (homologyMap (koszulBraidingHom K L) n), hκ, isIso_comp_left_iff]

end Kunneth

end TauCeti.NatChainComplex

namespace HomologicalComplex

universe u

variable {R : Type u} [CommRing R] (K L : ChainComplex (ModuleCat.{u} R) ℕ)
  [∀ q, Module.Flat R (L.X q)]

/-- **The Künneth theorem when the second factor has zero differentials and flat terms**: if `L`
is a complex of flat modules with zero differentials, so that `H_q(L) = L_q`, then for every
complex `K` the Künneth map `⨁_{p + q = n} Hₚ(K) ⊗ H_q(L) ⟶ Hₙ(K ⊗ L)` is an isomorphism.  This
is `HomologicalComplex.isIso_homologyKunneth_of_d_eq_zero_of_flat` with the factors interchanged.
-/
theorem isIso_homologyKunneth_of_d_eq_zero_of_flat_right (hL : ∀ i j, L.d i j = 0) (n : ℕ) :
    IsIso (homologyKunneth K L n) :=
  (TauCeti.NatChainComplex.isIso_homologyKunneth_comm K L n).2
    (isIso_homologyKunneth_of_d_eq_zero_of_flat L K hL n)

end HomologicalComplex

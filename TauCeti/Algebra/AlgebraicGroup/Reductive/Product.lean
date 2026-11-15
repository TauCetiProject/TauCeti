/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Connected.Product
public import TauCeti.Algebra.AlgebraicGroup.FiniteType.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal.Image
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Image.Smooth
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Image.Unipotent
public import TauCeti.Algebra.AlgebraicGroup.Reductive.Basic

/-!
# Products of reductive affine groups

The direct product of two reductive affine groups over a field is reductive. After extending
scalars to an algebraic closure, a connected normal smooth unipotent subgroup of the product maps
to such a subgroup of each factor. Reductivity makes both projection images trivial. Since the
two coordinate inclusions generate the tensor-product coordinate algebra, the original subgroup
is trivial as well.

The proof uses scheme-theoretic images rather than only algebraic-closure-valued points. This
retains normality and is valid in every characteristic.

## Main declaration

* `TauCeti.reductiveCommHopfAlgProperty.tensorProduct`: direct products of reductive finite-type
  affine groups are reductive.

## References

* J. S. Milne, *Algebraic Groups* (2017), Section 19.b.
* T. A. Springer, *Linear Algebraic Groups*, Chapter 8.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti

universe u

noncomputable section

namespace reductiveCommHopfAlgProperty

variable {k : Type u} [Field k]

private theorem ker_projection_eq_augmentation
    {H : FiniteTypeCommHopfAlgCat.{u, u} k}
    (hH : reductiveCommHopfAlgProperty k H)
    {P : FiniteTypeCommHopfAlgCat.{u, u} (AlgebraicClosure k)}
    (f : FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H ⟶ P)
    (hf : Function.Injective (FiniteTypeCommHopfAlgCat.toBialgHom f))
    (I : HopfIdeal (AlgebraicClosure k) P)
    (hI : I.IsNormal)
    (hconnected : geometricallyConnectedCommHopfAlgProperty (AlgebraicClosure k)
      (FiniteTypeCommHopfAlgCat.quotient P I).obj)
    (hunipotent : smoothUnipotentCommHopfAlgProperty (AlgebraicClosure k)
      (FiniteTypeCommHopfAlgCat.quotient P I)) :
    HopfIdeal.ker
        (FiniteTypeCommHopfAlgCat.toBialgHom
          (f ≫ FiniteTypeCommHopfAlgCat.mkQuotient P I)) =
      HopfIdeal.augmentation (AlgebraicClosure k)
        (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H) := by
  let g :
      (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H).obj ⟶
        (FiniteTypeCommHopfAlgCat.quotient P I).obj :=
    f.hom ≫ (FiniteTypeCommHopfAlgCat.mkQuotient P I).hom
  have hker : HopfIdeal.ker g.hom =
      I.comap (FiniteTypeCommHopfAlgCat.toBialgHom f) := by
    ext x
    rw [HopfIdeal.mem_ker, HopfIdeal.mem_comap]
    -- Unfold the categorical composite just enough to expose the underlying quotient map;
    -- `mkQuotient_eq_zero_iff` is stated for this concrete map rather than its wrappers.
    change (FiniteTypeCommHopfAlgCat.mkQuotient P I).hom.hom
        (FiniteTypeCommHopfAlgCat.toBialgHom f x) = 0 ↔ _
    exact FiniteTypeCommHopfAlgCat.mkQuotient_eq_zero_iff P I _
  have hnormal : (HopfIdeal.ker g.hom).IsNormal := by
    rw [hker]
    exact hI.comap_of_injective _ hf
  have himageConnected : geometricallyConnectedCommHopfAlgProperty (AlgebraicClosure k)
      (CommHopfAlgCat.image g) :=
    geometricallyConnectedCommHopfAlgProperty.image g hconnected
  have hsource := (smoothUnipotentCommHopfAlgProperty_iff _ _).mp hunipotent
  have hsmooth : smoothCommHopfAlgProperty (AlgebraicClosure k)
      (FiniteTypeCommHopfAlgCat.quotient P I).obj :=
    (smoothCommHopfAlgProperty_iff _).mpr hsource.1
  let _ : Algebra.Smooth (AlgebraicClosure k) (FiniteTypeCommHopfAlgCat.quotient P I) :=
    hsource.1
  let _ : IsReduced (FiniteTypeCommHopfAlgCat.quotient P I) :=
    isReduced_of_smooth (AlgebraicClosure k) _
  have himageUnipotent : geometricallyUnipotentPointsCommHopfAlgProperty (AlgebraicClosure k)
      (CommHopfAlgCat.image g) :=
    geometricallyUnipotentPointsCommHopfAlgProperty.image_of_reduced g
      ((geometricallyUnipotentPointsCommHopfAlgProperty_iff _ _).mpr hsource.2)
  have himageSmooth : smoothCommHopfAlgProperty (AlgebraicClosure k)
      (CommHopfAlgCat.image g) := smoothCommHopfAlgProperty.image g hsmooth
  have himageSmoothUnipotent : smoothUnipotentCommHopfAlgProperty (AlgebraicClosure k)
      (FiniteTypeCommHopfAlgCat.quotient
        (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H)
        (HopfIdeal.ker g.hom)) := by
    rw [smoothUnipotentCommHopfAlgProperty_iff]
    exact ⟨(smoothCommHopfAlgProperty_iff _).mp himageSmooth,
      (geometricallyUnipotentPointsCommHopfAlgProperty_iff _ _).mp himageUnipotent⟩
  have h := hH.eq_augmentation (HopfIdeal.ker g.hom) hnormal himageConnected
    himageSmoothUnipotent
  exact h

/-- **A direct product of reductive finite-type affine groups is reductive.** -/
theorem tensorProduct (H K : FiniteTypeCommHopfAlgCat.{u, u} k)
    (hH : reductiveCommHopfAlgProperty k H)
    (hK : reductiveCommHopfAlgProperty k K) :
    reductiveCommHopfAlgProperty k (FiniteTypeCommHopfAlgCat.tensorProduct H K) := by
  let Hbar := FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H
  let Kbar := FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) K
  let P₀ := FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k)
    (FiniteTypeCommHopfAlgCat.tensorProduct H K)
  let P := FiniteTypeCommHopfAlgCat.tensorProduct Hbar Kbar
  let e : P₀ ≅ P :=
    FiniteTypeCommHopfAlgCat.baseChangeTensorProductIso (AlgebraicClosure k) H K
  -- First discharge the smoothness and connectedness fields of reductivity.
  have hsmooth : Algebra.Smooth k (FiniteTypeCommHopfAlgCat.tensorProduct H K) := by
    let smoothH : Algebra.Smooth k H := hH.smooth
    let smoothK : Algebra.Smooth k K := hK.smooth
    let smoothOverH : Algebra.Smooth H (H ⊗[k] K) :=
      @Algebra.Smooth.baseChange k _ K H _ _ _ _ smoothK
    exact @Algebra.Smooth.comp k _ H (H ⊗[k] K) _ _ _ _ _ _ smoothH smoothOverH
  have hconnected : geometricallyConnectedCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.tensorProduct H K).obj :=
    geometricallyConnectedCommHopfAlgProperty.tensorProduct H.obj K.obj
      hH.geometricallyConnected hK.geometricallyConnected
  rw [reductiveCommHopfAlgProperty_iff]
  refine ⟨hsmooth, hconnected, ?_⟩
  intro I hI hsourceConnected hU
  let q := FiniteTypeCommHopfAlgCat.mkQuotient P₀ I
  let fH := FiniteTypeCommHopfAlgCat.baseChangeMap (K := AlgebraicClosure k)
    (FiniteTypeCommHopfAlgCat.includeLeft H K)
  let fK := FiniteTypeCommHopfAlgCat.baseChangeMap (K := AlgebraicClosure k)
    (FiniteTypeCommHopfAlgCat.includeRight H K)
  -- Project the candidate unipotent subgroup to each factor.
  have hfH : Function.Injective (FiniteTypeCommHopfAlgCat.toBialgHom fH) := by
    simpa only [fH] using FiniteTypeCommHopfAlgCat.baseChangeMap_includeLeft_injective
      (K := AlgebraicClosure k) H K
  have hfK : Function.Injective (FiniteTypeCommHopfAlgCat.toBialgHom fK) := by
    simpa only [fK] using FiniteTypeCommHopfAlgCat.baseChangeMap_includeRight_injective
      (K := AlgebraicClosure k) H K
  have hleft : HopfIdeal.ker
      (FiniteTypeCommHopfAlgCat.toBialgHom (fH ≫ q)) =
        HopfIdeal.augmentation (AlgebraicClosure k) Hbar := by
    exact ker_projection_eq_augmentation hH fH hfH I hI hsourceConnected hU
  have hright : HopfIdeal.ker
      (FiniteTypeCommHopfAlgCat.toBialgHom (fK ≫ q)) =
        HopfIdeal.augmentation (AlgebraicClosure k) Kbar := by
    exact ker_projection_eq_augmentation hK fK hfK I hI hsourceConnected hU
  -- Transport the subgroup to the product of the geometric fibres. Its two projection
  -- images are trivial, so the shared product criterion makes the subgroup trivial.
  let J := I.comap (FiniteTypeCommHopfAlgCat.toBialgHom e.inv)
  have hleftComp : FiniteTypeCommHopfAlgCat.includeLeft Hbar Kbar ≫ e.inv ≫ q = fH ≫ q := by
    rw [← FiniteTypeCommHopfAlgCat.baseChangeMap_includeLeft_comp_baseChangeTensorProductIso_hom
        (AlgebraicClosure k) H K, Category.assoc, e.hom_inv_id_assoc]
  have hrightComp : FiniteTypeCommHopfAlgCat.includeRight Hbar Kbar ≫ e.inv ≫ q = fK ≫ q := by
    rw [← FiniteTypeCommHopfAlgCat.baseChangeMap_includeRight_comp_baseChangeTensorProductIso_hom
        (AlgebraicClosure k) H K, Category.assoc, e.hom_inv_id_assoc]
  have hJ : J = HopfIdeal.augmentation (AlgebraicClosure k) P := by
    apply J.eq_augmentation_of_comap_includeLeft_of_comap_includeRight
    · rw [← hleft, ← hleftComp]
      ext x
      simp only [J, HopfIdeal.mem_comap, HopfIdeal.mem_ker,
        FiniteTypeCommHopfAlgCat.toBialgHom_comp, BialgHom.comp_apply]
      exact (FiniteTypeCommHopfAlgCat.mkQuotient_eq_zero_iff P₀ I _).symm
    · rw [← hright, ← hrightComp]
      ext x
      simp only [J, HopfIdeal.mem_comap, HopfIdeal.mem_ker,
        FiniteTypeCommHopfAlgCat.toBialgHom_comp, BialgHom.comp_apply]
      exact (FiniteTypeCommHopfAlgCat.mkQuotient_eq_zero_iff P₀ I _).symm
  ext x
  have h := SetLike.ext_iff.mp hJ (FiniteTypeCommHopfAlgCat.toBialgHom e.hom x)
  have hinv : FiniteTypeCommHopfAlgCat.toBialgHom e.inv
      (FiniteTypeCommHopfAlgCat.toBialgHom e.hom x) = x := by
    rw [← BialgHom.comp_apply, ← FiniteTypeCommHopfAlgCat.toBialgHom_comp, e.hom_inv_id]
    rw [FiniteTypeCommHopfAlgCat.toBialgHom_id, BialgHom.id_apply]
  simpa only [J, HopfIdeal.mem_comap, hinv, HopfIdeal.mem_augmentation,
    CoalgHomClass.counit_comp_apply] using h

end reductiveCommHopfAlgProperty

end

end TauCeti

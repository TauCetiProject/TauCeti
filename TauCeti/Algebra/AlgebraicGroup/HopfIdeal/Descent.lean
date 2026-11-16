/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.BaseChange
public import Mathlib.FieldTheory.Galois.Basic
import TauCeti.Algebra.TensorProduct.Galois

/-!
# Descent of Hopf ideals

A closed subgroup of an affine group over a field `k` is cut out by a Hopf ideal of the coordinate
Hopf algebra `H`. This file identifies the Hopf ideals of a scalar extension `L ⊗[k] H` that come
from Hopf ideals of `H`, that is, the closed subgroups of the base-changed group that are defined
over `k`.

When the ground-field map is surjective, every Hopf ideal after scalar extension comes from a Hopf
ideal over the original field. The coefficient Hopf ideal for the one-element basis supplies the
descent. This applies to an algebraic extension of an algebraically closed field and allows
geometric subgroup conditions to be checked over that field itself.

Along a Galois extension `L / k`, possibly infinite, a Hopf ideal of `L ⊗[k] H` descends exactly
when it is stable under the action of `Gal(L / k)` on the scalar factor. The descended Hopf ideal is
unique, consists of the elements `h` with `1 ⊗ h` in the given ideal, and is the coefficient Hopf
ideal in any basis of `L`. Galois descent of subspaces supplies the underlying ideal, and the
coefficient Hopf ideal supplies the Hopf structure without rechecking it. This is the descent step
for closed subgroups characterized geometrically, such as the unipotent radical, over a perfect
field, whose algebraic closure is Galois.

## Main declarations

* `TauCeti.CommHopfAlgCat.baseChangeHopfIdeal_surjective`: every Hopf ideal descends along a
  surjective map of ground fields.
* `TauCeti.CommHopfAlgCat.mapBaseChangeHopfIdeal`: transport of a Hopf ideal of `K₁ ⊗[k] H` to
  `K₂ ⊗[k] H` along a `k`-algebra equivalence `e : K₁ ≃ₐ[k] K₂`, without introducing a global
  `Algebra K₁ K₂` instance.
* `TauCeti.CommHopfAlgCat.mem_mapBaseChangeHopfIdeal_iff`: membership in the transported Hopf
  ideal is tested by applying `e.symm ⊗ id`.
* `Module.Basis.baseChangeHopfIdeal_coefficientHopfIdeal_of_forall_map_mem`: a Galois-stable Hopf
  ideal is the base change of its coefficient Hopf ideal.
* `Module.Basis.mem_coefficientHopfIdeal_iff_of_forall_map_mem`: that coefficient Hopf ideal
  consists of the elements `h` with `1 ⊗ h` in the Galois-stable Hopf ideal.
* `TauCeti.CommHopfAlgCat.existsUnique_baseChangeHopfIdeal_eq_iff`: along a Galois extension, the
  base-changed Hopf ideals are exactly the Galois-stable ones, each descending uniquely.
* `TauCeti.CommHopfAlgCat.existsUnique_baseChangeHopfIdeal_eq_iff_mapBaseChangeHopfIdeal`:
  restates Galois stability directly in terms of `mapBaseChangeHopfIdeal`.

## References

* A. Borel, *Linear Algebraic Groups*, 2nd ed. (1991), §AG.14.
* J. S. Milne, *Algebraic Groups* (2017), Appendix A.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti.CommHopfAlgCat

universe u v w x y

section Surjective

variable {k : Type u} {K : Type w} [Field k] [Field K] [Algebra k K]
variable {H : _root_.CommHopfAlgCat.{v} k}

/-- Every Hopf ideal descends along a surjective map of ground fields. -/
theorem baseChangeHopfIdeal_surjective (h : Function.Surjective (algebraMap k K)) :
    Function.Surjective (baseChangeHopfIdeal (H := H) (K := K)) := by
  classical
  let e : k ≃ₐ[k] K := AlgEquiv.ofBijective (Algebra.ofId k K)
    ⟨(algebraMap k K).injective, h⟩
  let b := (Module.Basis.singleton Unit k).map e.toLinearEquiv
  have hb (j : Unit) : b j = 1 := by
    simp only [b, Module.Basis.map_apply, Module.Basis.singleton_apply,
      AlgEquiv.toLinearEquiv_apply, map_one]
  have coefficient_one_tmul (x : H) (j : Unit) :
      TensorProduct.equivFinsuppOfBasisLeft b (1 ⊗ₜ[k] x) j = x := by
    rw [← hb j, TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply]
    simp
  intro I
  refine ⟨b.coefficientHopfIdeal I, le_antisymm ?_ ?_⟩
  · rw [← HopfIdeal.toIdeal_le_toIdeal, baseChangeHopfIdeal_toIdeal,
      Ideal.map_le_iff_le_comap, Module.Basis.coefficientHopfIdeal_toIdeal_le_iff]
    intro z hz j
    obtain ⟨x, rfl⟩ := Algebra.TensorProduct.includeRight_surjective (T := H) h z
    simpa only [Ideal.mem_comap, Algebra.TensorProduct.includeRight_apply,
      coefficient_one_tmul, HopfIdeal.mem_toIdeal] using hz
  · exact (b.coefficientHopfIdeal_le_iff_le_baseChangeHopfIdeal I _).mp le_rfl

end Surjective

section Equiv

variable {k : Type u} [CommRing k] {H : _root_.CommHopfAlgCat.{v} k}

/-- Applying `e ⊗ id` after `e.symm ⊗ id` is the identity on `K₂ ⊗[k] H`. -/
private theorem tensorProduct_map_apply_symm
    {K₁ : Type w} {K₂ : Type x} [CommRing K₁] [CommRing K₂] [Algebra k K₁] [Algebra k K₂]
    (e : K₁ ≃ₐ[k] K₂) (y : K₂ ⊗[k] H) :
    TensorProduct.map e.toLinearMap LinearMap.id
      (TensorProduct.map e.symm.toLinearMap LinearMap.id y) = y := by
  rw [← LinearMap.comp_apply, ← TensorProduct.map_comp, LinearMap.id_comp]
  have hcomp : e.toLinearMap ∘ₗ e.symm.toLinearMap = LinearMap.id := by
    ext s
    exact e.apply_symm_apply s
  rw [hcomp, TensorProduct.map_id, LinearMap.id_apply]

/-- Along a ring equivalence `e : K₁ ≃ₐ[k] K₂` giving the `K₁`-algebra structure on `K₂`, an
element `x ∈ K₁ ⊗[k] H` lies in `I` if and only if `1 ⊗ x` lies in `baseChangeHopfIdeal I`. -/
private theorem one_tmul_mem_baseChangeHopfIdeal_iff_of_algEquiv
    {K₁ : Type w} {K₂ : Type x} [CommRing K₁] [CommRing K₂]
    [Algebra k K₁] [Algebra k K₂] [Algebra K₁ K₂]
    (e : K₁ ≃ₐ[k] K₂) (he : ∀ s : K₁, algebraMap K₁ K₂ s = e s)
    (I : HopfIdeal K₁ (baseChange (K := K₁) H)) (x : K₁ ⊗[k] H) :
    (1 : K₂) ⊗ₜ[K₁] x ∈ baseChangeHopfIdeal (K := K₂) I ↔ x ∈ I := by
  refine ⟨fun hx ↦ ?_, one_tmul_mem_baseChangeHopfIdeal⟩
  rw [mem_baseChangeHopfIdeal_iff, baseChangeMap_apply_tmul] at hx
  let Q := _root_.CommHopfAlgCat.quotient (baseChange (K := K₁) H) I
  let eLin : K₂ →ₗ[K₁] K₁ :=
    { toFun := e.symm
      map_add' := map_add e.symm
      map_smul' := fun r c ↦ by
        rw [Algebra.smul_def, he r, map_mul, e.symm_apply_apply, RingHom.id_apply, smul_eq_mul] }
  let r : K₂ ⊗[K₁] Q →ₗ[K₁] Q :=
    (TensorProduct.lid K₁ Q).toLinearMap.comp (LinearMap.rTensor Q eLin)
  have h0 : r ((1 : K₂) ⊗ₜ[K₁] (_root_.CommHopfAlgCat.mkQuotient _ I).hom x) = 0 := by
    rw [hx, map_zero]
  simp only [r, eLin, LinearMap.comp_apply, LinearMap.rTensor_tmul, LinearMap.coe_mk,
    AddHom.coe_mk, map_one, LinearEquiv.coe_coe, TensorProduct.lid_tmul, one_smul] at h0
  exact (_root_.CommHopfAlgCat.mkQuotient_eq_zero_iff _ _ _).mp h0

/-- On a scalar-extended element, the inverse tower comparison for a `k`-algebra equivalence
`e : K₁ ≃ₐ[k] K₂` inserts `1` on the left. -/
private theorem baseChangeTowerBialgEquiv_symm_map_eq_one_tmul
    {K₁ : Type w} {K₂ : Type x} [CommRing K₁] [CommRing K₂]
    [Algebra k K₁] [Algebra k K₂] [Algebra K₁ K₂] [IsScalarTower k K₁ K₂]
    (e : K₁ ≃ₐ[k] K₂) (he : ∀ s : K₁, algebraMap K₁ K₂ s = e s) (x : K₁ ⊗[k] H) :
    (TauCeti.Bialgebra.TensorProduct.baseChangeTowerBialgEquiv k K₁ H K₂).symm
        (TensorProduct.map e.toLinearMap LinearMap.id x) =
      (1 : K₂) ⊗ₜ[K₁] x := by
  apply EquivLike.injective
    (TauCeti.Bialgebra.TensorProduct.baseChangeTowerBialgEquiv k K₁ H K₂)
  rw [BialgEquiv.apply_symm_apply, TensorProduct.baseChangeTowerBialgEquiv_one_tmul]
  induction x with
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul s h =>
    simp only [TensorProduct.map_tmul, AlgEquiv.toLinearMap_apply, LinearMap.id_apply,
      Algebra.TensorProduct.map_tmul, IsScalarTower.coe_toAlgHom', AlgHom.id_apply, he s]

/-- Any `k`-algebra homomorphism `f : A →ₐ[k] B` carries `baseChangeHopfIdeal J` into
`baseChangeHopfIdeal J`. -/
private theorem map_mem_baseChangeHopfIdeal_of_algHom
    {A : Type w} {B : Type x} [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
    (J : HopfIdeal k H) (f : A →ₐ[k] B) {z : A ⊗[k] H}
    (hz : z ∈ baseChangeHopfIdeal (K := A) J) :
    TensorProduct.map f.toLinearMap LinearMap.id z ∈ baseChangeHopfIdeal (K := B) J := by
  let g : A ⊗[k] H →ₐ[k] B ⊗[k] H := Algebra.TensorProduct.map f (AlgHom.id k H)
  rw [← HopfIdeal.mem_toIdeal, baseChangeHopfIdeal_toIdeal] at hz ⊢
  have hle : J.toIdeal.map (Algebra.TensorProduct.includeRight : H →ₐ[k] A ⊗[k] H) ≤
      (J.toIdeal.map (Algebra.TensorProduct.includeRight : H →ₐ[k] B ⊗[k] H)).comap g := by
    rw [Ideal.map_le_iff_le_comap]
    intro h hh
    simpa [g] using Ideal.mem_map_of_mem Algebra.TensorProduct.includeRight hh
  exact hle hz

/-- Transport a Hopf ideal of `K₁ ⊗[k] H` to `K₂ ⊗[k] H` along a `k`-algebra equivalence
`e : K₁ ≃ₐ[k] K₂`.

The intermediate `K₁`-algebra structure on `K₂` is introduced locally inside the definition, so
specializing to an automorphism `σ : L ≃ₐ[k] L` produces no `Algebra L L` instance diamond. -/
noncomputable def mapBaseChangeHopfIdeal
    {K₁ : Type w} {K₂ : Type x} [CommRing K₁] [CommRing K₂] [Algebra k K₁] [Algebra k K₂]
    (e : K₁ ≃ₐ[k] K₂) (I : HopfIdeal K₁ (baseChange (K := K₁) H)) :
    HopfIdeal K₂ (baseChange (K := K₂) H) :=
  letI : Algebra K₁ K₂ := e.toRingHom.toAlgebra
  letI : IsScalarTower k K₁ K₂ :=
    IsScalarTower.of_algebraMap_eq fun c ↦ (e.commutes c).symm
  (baseChangeHopfIdeal (K := K₂) I).comapOfSurjective
    (TauCeti.Bialgebra.TensorProduct.baseChangeTowerBialgEquiv k K₁ H K₂).symm.toBialgHom
    (EquivLike.surjective
      (TauCeti.Bialgebra.TensorProduct.baseChangeTowerBialgEquiv k K₁ H K₂).symm)

/-- An element `e ⊗ id` applied to `x ∈ K₁ ⊗[k] H` lies in `mapBaseChangeHopfIdeal e I` exactly
when `x ∈ I`. -/
@[simp]
theorem mem_mapBaseChangeHopfIdeal_map_iff
    {K₁ : Type w} {K₂ : Type x} [CommRing K₁] [CommRing K₂] [Algebra k K₁] [Algebra k K₂]
    (e : K₁ ≃ₐ[k] K₂) (I : HopfIdeal K₁ (baseChange (K := K₁) H)) (x : K₁ ⊗[k] H) :
    TensorProduct.map e.toLinearMap LinearMap.id x ∈ mapBaseChangeHopfIdeal e I ↔ x ∈ I := by
  let _ : Algebra K₁ K₂ := e.toRingHom.toAlgebra
  let _ : IsScalarTower k K₁ K₂ :=
    IsScalarTower.of_algebraMap_eq fun c ↦ (e.commutes c).symm
  refine (HopfIdeal.mem_comapOfSurjective (I := baseChangeHopfIdeal (K := K₂) I)).trans ?_
  rw [BialgEquiv.toBialgHom_eq_coe, BialgEquiv.coe_coe,
    baseChangeTowerBialgEquiv_symm_map_eq_one_tmul e (fun _ ↦ rfl) x]
  exact one_tmul_mem_baseChangeHopfIdeal_iff_of_algEquiv e (fun _ ↦ rfl) I x

/-- Membership in `mapBaseChangeHopfIdeal e I` is tested by applying `e.symm ⊗ id`. -/
@[simp]
theorem mem_mapBaseChangeHopfIdeal_iff
    {K₁ : Type w} {K₂ : Type x} [CommRing K₁] [CommRing K₂] [Algebra k K₁] [Algebra k K₂]
    (e : K₁ ≃ₐ[k] K₂) (I : HopfIdeal K₁ (baseChange (K := K₁) H)) (y : K₂ ⊗[k] H) :
    y ∈ mapBaseChangeHopfIdeal e I ↔
      TensorProduct.map e.symm.toLinearMap LinearMap.id y ∈ I := by
  conv_lhs => rw [← tensorProduct_map_apply_symm e y]
  exact mem_mapBaseChangeHopfIdeal_map_iff e I _

/-- When `K₂` already carries a compatible `K₁`-algebra structure agreeing with `e : K₁ ≃ₐ[k] K₂`,
`mapBaseChangeHopfIdeal e I` is the pullback of `baseChangeHopfIdeal I` along the inverse
categorical tower comparison. -/
theorem mapBaseChangeHopfIdeal_eq_comapOfSurjective_baseChangeTowerIso
    {K₁ : Type v} {K₂ : Type w} [CommRing K₁] [CommRing K₂]
    [Algebra k K₁] [Algebra k K₂] [Algebra K₁ K₂] [IsScalarTower k K₁ K₂]
    (e : K₁ ≃ₐ[k] K₂) (he : ∀ s : K₁, algebraMap K₁ K₂ s = e s)
    (I : HopfIdeal K₁ (baseChange (K := K₁) H)) :
    mapBaseChangeHopfIdeal e I =
      (baseChangeHopfIdeal (K := K₂) I).comapOfSurjective
        (baseChangeTowerIso (E := K₁) k K₂ H).inv.hom
        (ConcreteCategory.bijective_of_isIso
          (baseChangeTowerIso (E := K₁) k K₂ H).inv).2 := by
  ext y
  rw [mem_mapBaseChangeHopfIdeal_iff, HopfIdeal.mem_comapOfSurjective]
  have hinv (x : K₁ ⊗[k] H) :
      (baseChangeTowerIso (E := K₁) k K₂ H).inv.hom
          (TensorProduct.map e.toLinearMap LinearMap.id x) =
        (1 : K₂) ⊗ₜ[K₁] x := by
    apply (ConcreteCategory.bijective_of_isIso (baseChangeTowerIso (E := K₁) k K₂ H).hom).1
    rw [_root_.CommHopfAlgCat.hom_inv_apply, baseChangeTowerIso_hom_one_tmul]
    induction x with
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul s h =>
      simp only [TensorProduct.map_tmul, AlgEquiv.toLinearMap_apply, LinearMap.id_apply,
        Algebra.TensorProduct.map_tmul, IsScalarTower.coe_toAlgHom', AlgHom.id_apply, he s]
  conv_rhs => rw [← tensorProduct_map_apply_symm e y, hinv]
  exact (one_tmul_mem_baseChangeHopfIdeal_iff_of_algEquiv e he I _).symm

/-- Transporting Hopf ideals along an algebra equivalence is monotone. -/
theorem mapBaseChangeHopfIdeal_mono
    {K₁ : Type w} {K₂ : Type x} [CommRing K₁] [CommRing K₂] [Algebra k K₁] [Algebra k K₂]
    (e : K₁ ≃ₐ[k] K₂) {I₁ I₂ : HopfIdeal K₁ (baseChange (K := K₁) H)} (h : I₁ ≤ I₂) :
    mapBaseChangeHopfIdeal e I₁ ≤ mapBaseChangeHopfIdeal e I₂ := by
  intro y hy
  rw [mem_mapBaseChangeHopfIdeal_iff] at hy ⊢
  exact h hy

/-- Transport along the identity equivalence fixes every Hopf ideal. -/
@[simp]
theorem mapBaseChangeHopfIdeal_refl
    {K : Type w} [CommRing K] [Algebra k K]
    (I : HopfIdeal K (baseChange (K := K) H)) :
    mapBaseChangeHopfIdeal (AlgEquiv.refl (R := k) (A₁ := K)) I = I := by
  ext y
  rw [mem_mapBaseChangeHopfIdeal_iff]
  have hid : (AlgEquiv.refl (R := k) (A₁ := K)).symm.toLinearMap = LinearMap.id := rfl
  rw [hid, TensorProduct.map_id, LinearMap.id_apply]

/-- Transport along a composite algebra equivalence is the composition of transports. -/
@[simp]
theorem mapBaseChangeHopfIdeal_trans
    {K₁ : Type w} {K₂ : Type x} {K₃ : Type y} [CommRing K₁] [CommRing K₂] [CommRing K₃]
    [Algebra k K₁] [Algebra k K₂] [Algebra k K₃]
    (e₁ : K₁ ≃ₐ[k] K₂) (e₂ : K₂ ≃ₐ[k] K₃) (I : HopfIdeal K₁ (baseChange (K := K₁) H)) :
    mapBaseChangeHopfIdeal (e₁.trans e₂) I =
      mapBaseChangeHopfIdeal e₂ (mapBaseChangeHopfIdeal e₁ I) := by
  ext y
  rw [mem_mapBaseChangeHopfIdeal_iff, mem_mapBaseChangeHopfIdeal_iff,
    mem_mapBaseChangeHopfIdeal_iff, ← LinearMap.comp_apply, ← TensorProduct.map_comp,
    LinearMap.id_comp]
  rfl

/-- Transport along `e` followed by transport along `e.symm` recovers the original Hopf ideal. -/
@[simp]
theorem mapBaseChangeHopfIdeal_symm_mapBaseChangeHopfIdeal
    {K₁ : Type w} {K₂ : Type x} [CommRing K₁] [CommRing K₂] [Algebra k K₁] [Algebra k K₂]
    (e : K₁ ≃ₐ[k] K₂) (I : HopfIdeal K₁ (baseChange (K := K₁) H)) :
    mapBaseChangeHopfIdeal e.symm (mapBaseChangeHopfIdeal e I) = I := by
  rw [← mapBaseChangeHopfIdeal_trans, AlgEquiv.self_trans_symm, mapBaseChangeHopfIdeal_refl]

/-- Transport along `e.symm` followed by transport along `e` recovers the original Hopf ideal. -/
@[simp]
theorem mapBaseChangeHopfIdeal_mapBaseChangeHopfIdeal_symm
    {K₁ : Type w} {K₂ : Type x} [CommRing K₁] [CommRing K₂] [Algebra k K₁] [Algebra k K₂]
    (e : K₁ ≃ₐ[k] K₂) (I : HopfIdeal K₂ (baseChange (K := K₂) H)) :
    mapBaseChangeHopfIdeal e (mapBaseChangeHopfIdeal e.symm I) = I := by
  rw [← mapBaseChangeHopfIdeal_trans, AlgEquiv.symm_trans_self, mapBaseChangeHopfIdeal_refl]

/-- Transporting Hopf ideals along an algebra equivalence is injective. -/
theorem mapBaseChangeHopfIdeal_injective
    {K₁ : Type w} {K₂ : Type x} [CommRing K₁] [CommRing K₂] [Algebra k K₁] [Algebra k K₂]
    (e : K₁ ≃ₐ[k] K₂) :
    Function.Injective (mapBaseChangeHopfIdeal (H := H) e) :=
  Function.LeftInverse.injective (mapBaseChangeHopfIdeal_symm_mapBaseChangeHopfIdeal e)

/-- Transport carries the base change of a Hopf ideal `J` of `H` to its base change in the
target scalar ring. -/
@[simp]
theorem mapBaseChangeHopfIdeal_baseChangeHopfIdeal
    {K₁ : Type w} {K₂ : Type x} [CommRing K₁] [CommRing K₂] [Algebra k K₁] [Algebra k K₂]
    (e : K₁ ≃ₐ[k] K₂) (J : HopfIdeal k H) :
    mapBaseChangeHopfIdeal e (baseChangeHopfIdeal (K := K₁) J) =
      baseChangeHopfIdeal (K := K₂) J := by
  ext y
  rw [mem_mapBaseChangeHopfIdeal_iff]
  refine ⟨fun hy ↦ ?_, fun hy ↦ by
    simpa only [AlgEquiv.toAlgHom_toLinearMap] using
      map_mem_baseChangeHopfIdeal_of_algHom J e.symm.toAlgHom hy⟩
  have hy' := map_mem_baseChangeHopfIdeal_of_algHom J e.toAlgHom hy
  rw [AlgEquiv.toAlgHom_toLinearMap, tensorProduct_map_apply_symm e y] at hy'
  exact hy'

/-- Transport preserves the augmentation ideal. -/
@[simp]
theorem mapBaseChangeHopfIdeal_augmentation
    {K₁ : Type w} {K₂ : Type x} [CommRing K₁] [CommRing K₂] [Algebra k K₁] [Algebra k K₂]
    (e : K₁ ≃ₐ[k] K₂) :
    mapBaseChangeHopfIdeal e (HopfIdeal.augmentation K₁ (baseChange (K := K₁) H)) =
      HopfIdeal.augmentation K₂ (baseChange (K := K₂) H) := by
  rw [← baseChangeHopfIdeal_augmentation, mapBaseChangeHopfIdeal_baseChangeHopfIdeal,
    baseChangeHopfIdeal_augmentation]

/-- Transport preserves the zero Hopf ideal. -/
@[simp]
theorem mapBaseChangeHopfIdeal_bot
    {K₁ : Type w} {K₂ : Type x} [CommRing K₁] [CommRing K₂] [Algebra k K₁] [Algebra k K₂]
    (e : K₁ ≃ₐ[k] K₂) :
    mapBaseChangeHopfIdeal e (⊥ : HopfIdeal K₁ (baseChange (K := K₁) H)) = ⊥ := by
  rw [← baseChangeHopfIdeal_bot, mapBaseChangeHopfIdeal_baseChangeHopfIdeal,
    baseChangeHopfIdeal_bot]

end Equiv

section Galois

variable {k : Type u} {L : Type w} [Field k] [Field L] [Algebra k L] [IsGalois k L]
variable {H : _root_.CommHopfAlgCat.{v} k}

/-- For a Galois-stable Hopf ideal `I` of `L ⊗[k] H`, every coefficient `c` of an element of `I`,
in a basis of `L`, satisfies `1 ⊗ c ∈ I`. -/
private theorem one_tmul_equivFinsuppOfBasisLeft_mem {κ : Type*} [DecidableEq κ]
    (b : Module.Basis κ k L) (I : HopfIdeal L (baseChange (K := L) H))
    (hI : ∀ σ : L ≃ₐ[k] L, ∀ x ∈ I, TensorProduct.map σ.toLinearMap LinearMap.id x ∈ I)
    {z : L ⊗[k] H} (hz : z ∈ I) (j : κ) :
    1 ⊗ₜ[k] TensorProduct.equivFinsuppOfBasisLeft b z j ∈ I := by
  let W : Submodule L (L ⊗[k] H) := I.toIdeal.restrictScalars L
  let p := (W.restrictScalars k).comap (TensorProduct.mk k L H 1)
  have hz : z ∈ p.baseChange L := by
    rw [W.baseChange_comap_eq_of_forall_map_mem hI]
    exact HopfIdeal.mem_toIdeal.mpr hz
  obtain ⟨y, rfl⟩ := hz
  -- The coefficients of an element of `p.baseChange L` lie in `p`.
  have hy := b.equivFinsuppOfBasisLeft_lTensor_apply p.subtype y j
  exact HopfIdeal.mem_toIdeal.mp (hy ▸ (TensorProduct.equivFinsuppOfBasisLeft b y j).2)

/-- **Galois descent of Hopf ideals.** Along a Galois extension `L / k`, a Hopf ideal of
`L ⊗[k] H` stable under the scalar-factor Galois action is the base change of its coefficient Hopf
ideal in any basis of `L`. -/
theorem _root_.Module.Basis.baseChangeHopfIdeal_coefficientHopfIdeal_of_forall_map_mem
    {κ : Type*} [DecidableEq κ] (b : Module.Basis κ k L)
    (I : HopfIdeal L (baseChange (K := L) H))
    (hI : ∀ σ : L ≃ₐ[k] L, ∀ x ∈ I, TensorProduct.map σ.toLinearMap LinearMap.id x ∈ I) :
    baseChangeHopfIdeal (K := L) (b.coefficientHopfIdeal I) = I := by
  refine le_antisymm ?_ ((b.coefficientHopfIdeal_le_iff_le_baseChangeHopfIdeal I _).mp le_rfl)
  rw [← HopfIdeal.toIdeal_le_toIdeal, baseChangeHopfIdeal_toIdeal, Ideal.map_le_iff_le_comap,
    b.coefficientHopfIdeal_toIdeal_le_iff]
  intro z hz j
  exact HopfIdeal.mem_toIdeal.mpr (one_tmul_equivFinsuppOfBasisLeft_mem b I hI hz j)

/-- The Hopf ideal descended from a Galois-stable Hopf ideal `I` of `L ⊗[k] H` consists of the
elements `h` of `H` with `1 ⊗ h ∈ I`. -/
theorem _root_.Module.Basis.mem_coefficientHopfIdeal_iff_of_forall_map_mem
    {κ : Type*} [DecidableEq κ] (b : Module.Basis κ k L)
    (I : HopfIdeal L (baseChange (K := L) H))
    (hI : ∀ σ : L ≃ₐ[k] L, ∀ x ∈ I, TensorProduct.map σ.toLinearMap LinearMap.id x ∈ I)
    (h : H) : h ∈ b.coefficientHopfIdeal I ↔ 1 ⊗ₜ[k] h ∈ I := by
  conv_rhs => rw [← b.baseChangeHopfIdeal_coefficientHopfIdeal_of_forall_map_mem I hI,
    mem_baseChangeHopfIdeal_iff, baseChangeMap_apply_tmul,
    Module.FaithfullyFlat.one_tmul_eq_zero_iff, _root_.CommHopfAlgCat.mkQuotient_eq_zero_iff]

/-- Along a Galois extension `L / k`, a Hopf ideal of `L ⊗[k] H` is the base change of a Hopf ideal
of `H` exactly when it is stable under the scalar-factor Galois action, and that Hopf ideal of `H`
is then unique. Geometrically, a closed subgroup of the base-changed group is defined over `k`
exactly when it is stable under `Gal(L / k)`. -/
theorem existsUnique_baseChangeHopfIdeal_eq_iff (I : HopfIdeal L (baseChange (K := L) H)) :
    (∃! J : HopfIdeal k H, baseChangeHopfIdeal (K := L) J = I) ↔
      ∀ σ : L ≃ₐ[k] L, ∀ x ∈ I, TensorProduct.map σ.toLinearMap LinearMap.id x ∈ I := by
  constructor
  · rintro ⟨J, rfl, -⟩ σ x hx
    exact map_mem_baseChangeHopfIdeal J σ.toAlgHom hx
  · intro hI
    classical
    let b := Module.Free.chooseBasis k L
    have hb := b.baseChangeHopfIdeal_coefficientHopfIdeal_of_forall_map_mem I hI
    exact ⟨b.coefficientHopfIdeal I, hb, fun J hJ ↦
      baseChangeHopfIdeal_injective (hJ.trans hb.symm)⟩

/-- Along a Galois extension `L / k`, a Hopf ideal of `L ⊗[k] H` descends uniquely to `H` exactly
when it is fixed by `mapBaseChangeHopfIdeal σ` for every `σ ∈ Gal(L / k)`. -/
theorem existsUnique_baseChangeHopfIdeal_eq_iff_mapBaseChangeHopfIdeal
    (I : HopfIdeal L (baseChange (K := L) H)) :
    (∃! J : HopfIdeal k H, baseChangeHopfIdeal (K := L) J = I) ↔
      ∀ σ : L ≃ₐ[k] L, mapBaseChangeHopfIdeal σ I = I := by
  rw [existsUnique_baseChangeHopfIdeal_eq_iff]
  refine ⟨fun hI σ ↦ ?_, fun hI σ x hx ↦ ?_⟩
  · ext y
    rw [mem_mapBaseChangeHopfIdeal_iff]
    refine ⟨fun hy ↦ ?_, fun hy ↦ hI σ.symm y hy⟩
    have hy' := hI σ _ hy
    rwa [tensorProduct_map_apply_symm σ y] at hy'
  · rw [← hI σ, mem_mapBaseChangeHopfIdeal_map_iff]
    exact hx

end Galois

end TauCeti.CommHopfAlgCat

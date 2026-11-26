/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import TauCeti.Algebra.Category.GradedModuleCat.Monoidal
public import TauCeti.Algebra.Category.GradedModuleCat.RestrictScalars

/-!
# Extension of scalars of graded modules

Let `A` be a commutative `k`-algebra and `B` an `A`-algebra, graded by `𝒜` and `ℬ`, such that
`A → B` sends each homogeneous piece `𝒜ᵢ` into `ℬᵢ`. A graded `𝒜`-module `M` gives the graded
`ℬ`-module `B ⊗[A] M`, graded by total degree: `b ⊗ₜ m` has degree `|b| + |m|` for homogeneous
`b` and `m`. This is the tensor product `InternalGrading.tensorProductOver` of the regular module
`B`, viewed as a graded `𝒜`-module, with `M`. Its degree pieces are `k`-submodules, not
`B`-submodules.

Extension of scalars is a functor `GradedModuleCat 𝒜 ⥤ GradedModuleCat ℬ`, left adjoint to
restriction of scalars `TauCeti.GradedModuleCat.restrictScalars`: a degree-zero `B`-linear map
`B ⊗[A] M → N` is the same as a degree-zero `A`-linear map `M → N`. Neither the functor nor the
adjunction needs `B` to be commutative, since `A` acts through the centre of `B`. Extension of
scalars commutes with the grading shifts `M{n}`, with identity components on underlying modules.
When `B` is commutative, lives in the same universe as `A`, and the graded `𝒜`-modules live in
that universe too, it is a strong symmetric monoidal functor for the tensor products over `A` and
over `B`: the comparison `B ⊗[A] (M ⊗[A] N) ≅ (B ⊗[A] M) ⊗[B] (B ⊗[A] N)` is Mathlib's
`TensorProduct.AlgebraTensorModule.distribBaseChange`, which preserves total degree, and it
intertwines the unsigned symmetries.

No flatness, finiteness or field hypothesis is imposed. A typical use is a graded specialization
of a ring of symmetric polynomials, such as sending every elementary symmetric polynomial of
positive degree to zero. A specialization to scalars of nonzero degree, such as sending an element
of degree two to `1`, is not graded and is not covered here.

## Main definitions

* `TauCeti.GradedModuleCat.extendScalars`: extension of scalars `M ↦ B ⊗[A] M`.
* `TauCeti.GradedModuleCat.extendRestrictScalarsAdj`: extension of scalars is left adjoint to
  restriction of scalars.
* `TauCeti.GradedModuleCat.extendScalarsShiftIso`: extension of scalars commutes with the
  grading shift `M ↦ M{n}`.
* `TauCeti.GradedModuleCat.extendScalarsTensorIso`: the comparison
  `B ⊗[A] (M ⊗ N) ≅ (B ⊗[A] M) ⊗ (B ⊗[A] N)`.
* The `Functor.Monoidal` and `Functor.Braided` instances on `extendScalars`.

## Main results

* `TauCeti.GradedModuleCat.tmul_mem_extendScalarsObj_piece`: `b ⊗ₜ m` has degree `|b| + |m|`.
* `TauCeti.GradedModuleCat.extendScalars_hom_ext`: morphisms out of `B ⊗[A] M` are determined
  by their values on the tensors `1 ⊗ₜ m`.
* `TauCeti.GradedModuleCat.mem_extendScalarsObj_shiftObj_piece_iff`: shifting `M` by `n` shifts
  the grading of `B ⊗[A] M` by `n`.
* `TauCeti.GradedModuleCat.extendScalarsTensorIso_hom_associativity`,
  `TauCeti.GradedModuleCat.extendScalarsTensorIso_hom_left_unitality` and
  `TauCeti.GradedModuleCat.extendScalarsTensorIso_hom_right_unitality`: the coherence of the
  tensor and unit comparisons.
* `TauCeti.GradedModuleCat.extendScalarsTensorIso_hom_braiding`: the tensor comparison
  intertwines the unsigned symmetries.
* `TauCeti.GradedModuleCat.extendScalars_μ`, `TauCeti.GradedModuleCat.extendScalars_δ`,
  `TauCeti.GradedModuleCat.extendScalars_ε` and `TauCeti.GradedModuleCat.extendScalars_η`: the
  structure maps of the monoidal functor are the explicit comparisons.

## Implementation notes

The adjunction follows Mathlib's `ModuleCat.extendRestrictScalarsAdj` in
`Mathlib/Algebra/Category/ModuleCat/ChangeOfRings.lean` (Jujian Zhang): the hom-equivalence sends
`g` to `m ↦ g (1 ⊗ₜ m)` and `h` to `b ⊗ₜ m ↦ b • h m`, and the unit, counit and hom-equivalence
lemmas mirror Mathlib's.

The strong monoidal structure follows Mathlib's monoidal instance on `ModuleCat.extendScalars` in
`Mathlib/Algebra/Category/ModuleCat/Monoidal/Adjunction.lean` (Joël Riou): it is built with
`Functor.CoreMonoidal.mk'` from `distribBaseChange` and `AlgebraTensorModule.rid`, and the
structure-map lemmas `extendScalars_μ`, `extendScalars_δ`, `extendScalars_ε` and `extendScalars_η`
mirror Mathlib's.

## References

* C. Năstăsescu and F. Van Oystaeyen, *Methods of Graded Rings*, Lecture Notes in Mathematics
  1836, Springer (2004), Section 2.2, for change of rings between categories of graded modules.
-/

public section

namespace TauCeti

open CategoryTheory MonoidalCategory TensorProduct

universe v uk uA uB

namespace GradedModuleCat

section ExtendScalars

variable {k : Type uk} [CommRing k] {A : Type uA} [CommRing A] [Algebra k A]
  {B : Type uB} [Ring B] [Algebra k B] [Algebra A B] [IsScalarTower k A B]
  {𝒜 : ℤ → Submodule k A} {ℬ : ℤ → Submodule k B} [GradedAlgebra 𝒜] [GradedAlgebra ℬ]
  (hf : ∀ ⦃i : ℤ⦄ ⦃a : A⦄, a ∈ 𝒜 i → algebraMap A B a ∈ ℬ i)

/-- The graded `ℬ`-module `B ⊗[A] M`, graded by total degree. -/
noncomputable abbrev extendScalarsObj (M : GradedModuleCat.{v} 𝒜) :
    GradedModuleCat.{max uB v} ℬ :=
  haveI := InternalGrading.gradedSMul_ofDecomposition_of_algebraMap_mem hf
  { carrier := B ⊗[A] M
    grading := (InternalGrading.ofDecomposition ℬ).tensorProductOver 𝒜 M.grading
    gradedSMul := ⟨fun {i d} b z hb hz ↦ by
      -- Multiplication by `b` on `B ⊗[A] M` is `(b • ·) ⊗ id`, of degree `i` on pure tensors.
      rw [vadd_eq_add, AlgebraTensorModule.smul_eq_lsmul_rTensor, add_comm]
      refine ((InternalGrading.ofDecomposition ℬ).isHomogeneous_of_tmul_mem_tensorProductOver 𝒜
        M.grading _ _ i fun {p q x m} hx hm ↦ ?_).map_mem hz
      simp only [LinearMap.rTensor_tmul, Algebra.lsmul_coe, smul_eq_mul]
      rw [add_right_comm]
      rw [InternalGrading.ofDecomposition_piece] at hx
      refine (InternalGrading.ofDecomposition ℬ).tmul_mem_tensorProductOver 𝒜 M.grading ?_ hm
      rw [InternalGrading.ofDecomposition_piece, add_comm]
      exact SetLike.GradedMul.mul_mem hb hx⟩ }

variable (M : GradedModuleCat.{v} 𝒜)

/-- The grading of `B ⊗[A] M` is the total-degree grading of the tensor product over `A`. -/
theorem extendScalarsObj_grading :
    haveI := InternalGrading.gradedSMul_ofDecomposition_of_algebraMap_mem hf
    (extendScalarsObj hf M).grading =
      (InternalGrading.ofDecomposition ℬ).tensorProductOver 𝒜 M.grading :=
  (rfl)

/-- A pure tensor `b ⊗ₜ m` of elements of degrees `p` and `q` has degree `p + q`. -/
theorem tmul_mem_extendScalarsObj_piece {p q : ℤ} {b : B} {m : M} (hb : b ∈ ℬ p)
    (hm : m ∈ M.grading.piece q) :
    (b ⊗ₜ[A] m : extendScalarsObj hf M) ∈ (extendScalarsObj hf M).grading.piece (p + q) :=
  haveI := InternalGrading.gradedSMul_ofDecomposition_of_algebraMap_mem hf
  (InternalGrading.ofDecomposition ℬ).tmul_mem_tensorProductOver 𝒜 M.grading
    (by rwa [InternalGrading.ofDecomposition_piece]) hm

/-- A `k`-submodule of `B ⊗[A] M` containing every pure tensor of homogeneous elements whose
degrees sum to `d` contains the degree-`d` piece. -/
theorem extendScalarsObj_piece_le_of_add_eq {d : ℤ} {C : Submodule k (B ⊗[A] M)}
    (h : ∀ p q : ℤ, p + q = d → ∀ b ∈ ℬ p, ∀ m ∈ M.grading.piece q, b ⊗ₜ[A] m ∈ C) :
    (extendScalarsObj hf M).grading.piece d ≤ C :=
  haveI := InternalGrading.gradedSMul_ofDecomposition_of_algebraMap_mem hf
  (InternalGrading.ofDecomposition ℬ).tensorProductOver_piece_le_of_add_eq 𝒜 M.grading
    fun p q hpq b hb m hm ↦ h p q hpq b (by rwa [InternalGrading.ofDecomposition_piece] at hb) m hm

/-- **Extension of scalars** of graded modules along a homomorphism `A → B` sending each `𝒜ᵢ`
into `ℬᵢ`: the functor `M ↦ B ⊗[A] M`, with the total-degree grading.
Its objects compute during type inference, agreeing with `extendScalarsObj` in morphism types. -/
@[expose, implicit_reducible]
noncomputable def extendScalars : GradedModuleCat.{v} 𝒜 ⥤ GradedModuleCat.{max uB v} ℬ where
  obj := extendScalarsObj hf
  map {M N} g := ofHom (M := extendScalarsObj hf M) (N := extendScalarsObj hf N)
    (g.hom.baseChange B) <|
      haveI := InternalGrading.gradedSMul_ofDecomposition_of_algebraMap_mem hf
      LinearMap.isHomogeneous_def.2 fun _ _ hz ↦
        -- `g.baseChange B` is `id ⊗ g` on underlying elements.
        (LinearMap.IsHomogeneous.tensorProductOver_zero 𝒜
          (LinearMap.isHomogeneous_id (InternalGrading.ofDecomposition ℬ).piece)
          g.isHomogeneous).map_mem hz
  map_id _ := hom_ext LinearMap.baseChange_id
  map_comp _ _ := hom_ext (LinearMap.baseChange_comp _ _)

/-- The objects of the extension functor are the modules `B ⊗[A] M`. -/
theorem extendScalars_obj : (extendScalars hf).obj M = extendScalarsObj hf M :=
  (rfl)

/-- Extension of scalars acts on morphisms by `LinearMap.baseChange`. -/
theorem extendScalars_map_hom {M N : GradedModuleCat.{v} 𝒜} (g : M ⟶ N) :
    ((extendScalars hf).map g).hom = g.hom.baseChange B :=
  (rfl)

/-- Extension of scalars acts on morphisms by `id ⊗ g`. -/
@[simp]
theorem extendScalars_map_tmul {M N : GradedModuleCat.{v} 𝒜} (g : M ⟶ N) (b : B) (m : M) :
    ((extendScalars hf).map g).hom (b ⊗ₜ[A] m) = b ⊗ₜ[A] g.hom m :=
  (rfl)

/-- Morphisms out of `B ⊗[A] M` are determined by their values on the tensors `1 ⊗ₜ m`. -/
@[ext]
theorem extendScalars_hom_ext {N : GradedModuleCat.{max uB v} ℬ}
    {f g : (extendScalars hf).obj M ⟶ N}
    (h : ∀ m : M, f.hom ((1 : B) ⊗ₜ[A] m) = g.hom ((1 : B) ⊗ₜ[A] m)) : f = g := by
  refine hom_ext (LinearMap.ext fun z ↦ ?_)
  induction z using TensorProduct.inductionOn with
  | tmul b m =>
    -- `b ⊗ₜ m = b • (1 ⊗ₜ m)`, and both maps are `B`-linear.
    rw [← mul_one b, ← smul_eq_mul, ← smul_tmul', map_smul, map_smul, h]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

instance : (extendScalars.{v} hf).Additive where
  map_add := by intros; ext; simp [tmul_add]

instance : (extendScalars.{v} hf).Linear k where
  map_smul := by intros; ext; simp [tmul_smul]

section Shift

variable {M} in
/-- Shifting `M` by `n` shifts the total degree of `B ⊗[A] M` by `n`. -/
theorem mem_extendScalarsObj_shiftObj_piece_iff (n p : ℤ) (z : B ⊗[A] M) :
    z ∈ (extendScalarsObj hf (M.shiftObj n)).grading.piece p ↔
      z ∈ (extendScalarsObj hf M).grading.piece (p - n) := by
  constructor
  · refine fun hz ↦ extendScalarsObj_piece_le_of_add_eq hf (M.shiftObj n)
      (C := (extendScalarsObj hf M).grading.piece (p - n)) (fun p₁ p₂ hp b hb m hm ↦ ?_) hz
    rw [mem_shiftObj_piece_iff] at hm
    convert tmul_mem_extendScalarsObj_piece hf M hb hm using 2
    omega
  · refine fun hz ↦ extendScalarsObj_piece_le_of_add_eq hf M
      (C := (extendScalarsObj hf (M.shiftObj n)).grading.piece p)
      (fun p₁ p₂ hp b hb m hm ↦ ?_) hz
    have hm' : m ∈ (M.shiftObj n).grading.piece (p₂ + n) := by
      rwa [mem_shiftObj_piece_iff, add_sub_cancel_right]
    convert tmul_mem_extendScalarsObj_piece hf (M.shiftObj n) hb hm' using 2
    omega

/-- Extension of scalars commutes with the grading shift `M ↦ M{n}`: both composites send `M`
to `B ⊗[A] M` with its grading shifted by `n`, so the components are identities. -/
noncomputable def extendScalarsShiftIso (n : ℤ) :
    shiftFunctor n ⋙ extendScalars.{v} hf ≅ extendScalars.{v} hf ⋙ shiftFunctor n :=
  NatIso.ofComponents (fun M ↦ isoMk (LinearEquiv.refl B (B ⊗[A] M)) fun p z ↦
    (mem_extendScalarsObj_shiftObj_piece_iff hf (M := M) n p z).trans
      (mem_shiftObj_piece_iff (extendScalarsObj hf M) n p z).symm) fun _ ↦ rfl

/-- The components of `TauCeti.GradedModuleCat.extendScalarsShiftIso` are identities. -/
@[simp]
theorem extendScalarsShiftIso_hom_app_hom (n : ℤ) :
    ((extendScalarsShiftIso hf n).hom.app M).hom = LinearMap.id :=
  (rfl)

/-- The inverse components of `TauCeti.GradedModuleCat.extendScalarsShiftIso` are identities. -/
@[simp]
theorem extendScalarsShiftIso_inv_app_hom (n : ℤ) :
    ((extendScalarsShiftIso hf n).inv.app M).hom = LinearMap.id :=
  (rfl)

end Shift

end ExtendScalars

section Adjunction

variable {k : Type uk} [CommRing k] {A : Type uA} [CommRing A] [Algebra k A]
  {B : Type uB} [Ring B] [Algebra k B] [Algebra A B] [IsScalarTower k A B]
  {𝒜 : ℤ → Submodule k A} {ℬ : ℤ → Submodule k B} [GradedAlgebra 𝒜] [GradedAlgebra ℬ]
  (hf : ∀ ⦃i : ℤ⦄ ⦃a : A⦄, a ∈ 𝒜 i → algebraMap A B a ∈ ℬ i)

variable {M : GradedModuleCat.{max v uB} 𝒜} {N : GradedModuleCat.{max v uB} ℬ}

/-- The degree-zero `A`-linear map `m ↦ g (1 ⊗ₜ m)` into the restriction of scalars of `N`,
for a morphism `g : B ⊗[A] M ⟶ N`. -/
private noncomputable def extendScalarsHomEquivToFun (g : (extendScalars hf).obj M ⟶ N) :
    M ⟶ restrictScalarsObj (IsScalarTower.toAlgHom k A B) hf N :=
  ofHom (N := restrictScalarsObj (IsScalarTower.toAlgHom k A B) hf N)
    { toFun m := g.hom ((1 : B) ⊗ₜ[A] m)
      map_add' x y := by rw [tmul_add, map_add]
      map_smul' a m := by
        -- `1 ⊗ₜ (a • m) = algebraMap A B a • (1 ⊗ₜ m)`, and `g` is `B`-linear.
        have h : ((1 : B) ⊗ₜ[A] (a • m) : (extendScalars hf).obj M) =
            algebraMap A B a • ((1 : B) ⊗ₜ[A] m) := by
          simp [Algebra.smul_def, smul_tmul']
        rw [restrictScalarsObj_smul_def]
        exact (congrArg g.hom h).trans (map_smul g.hom _ _) } <|
    LinearMap.isHomogeneous_def.2 fun p m hm ↦ by
      rw [add_zero, ← zero_add p]
      exact map_mem g (tmul_mem_extendScalarsObj_piece hf M SetLike.GradedOne.one_mem hm)

/-- The degree-zero `B`-linear map `b ⊗ₜ m ↦ b • h m` out of `B ⊗[A] M`, for a morphism
`h : M ⟶ N` into the restriction of scalars of `N`. -/
private noncomputable def extendScalarsHomEquivInvFun
    (h : M ⟶ restrictScalarsObj (IsScalarTower.toAlgHom k A B) hf N) :
    (extendScalars hf).obj M ⟶ N :=
  -- `A` acts on the restriction of scalars of `N` through the centre of `B`, so `B` acts on
  -- `A`-linear maps into it.
  haveI : IsScalarTower A B (restrictScalarsObj (IsScalarTower.toAlgHom k A B) hf N) :=
    ⟨fun a b n ↦ by
      rw [restrictScalarsObj_smul_def, IsScalarTower.coe_toAlgHom', Algebra.smul_def, mul_smul]⟩
  haveI : SMulCommClass A B (restrictScalarsObj (IsScalarTower.toAlgHom k A B) hf N) :=
    ⟨fun a b n ↦ by
      rw [restrictScalarsObj_smul_def, restrictScalarsObj_smul_def, IsScalarTower.coe_toAlgHom',
        smul_smul, smul_smul, Algebra.commutes]⟩
  haveI := InternalGrading.gradedSMul_ofDecomposition_of_algebraMap_mem hf
  ofHom (M := (extendScalars hf).obj M)
    (AlgebraTensorModule.lift (P := restrictScalarsObj (IsScalarTower.toAlgHom k A B) hf N)
      (LinearMap.toSpanSingleton B _ h.hom)) <|
    (InternalGrading.ofDecomposition ℬ).isHomogeneous_of_tmul_mem_tensorProductOver 𝒜 M.grading
      _ _ 0 fun {p q b m} hb hm ↦ by
        rw [InternalGrading.ofDecomposition_piece] at hb
        rw [add_zero]
        exact N.gradedSMul.smul_mem hb (by simpa using h.isHomogeneous.map_mem hm)

variable (M N) in
/-- Morphisms `B ⊗[A] M ⟶ N` of graded `ℬ`-modules correspond to morphisms of graded
`𝒜`-modules from `M` to the restriction of scalars of `N`. -/
private noncomputable def extendScalarsHomEquiv :
    ((extendScalars hf).obj M ⟶ N) ≃
      (M ⟶ (restrictScalars (IsScalarTower.toAlgHom k A B) hf).obj N) where
  toFun := extendScalarsHomEquivToFun hf
  invFun := extendScalarsHomEquivInvFun hf
  -- Both round trips are `1 • -` on underlying elements.
  left_inv g := extendScalars_hom_ext hf _ fun m ↦ one_smul B (g.hom ((1 : B) ⊗ₜ[A] m))
  right_inv h := hom_ext <| LinearMap.ext fun m ↦ one_smul B (α := N) (h.hom m)

/-- **Extension of scalars is left adjoint to restriction of scalars**: a degree-zero
`B`-linear map `B ⊗[A] M → N` corresponds to the degree-zero `A`-linear map `m ↦ g (1 ⊗ₜ m)`
into `N`. -/
noncomputable def extendRestrictScalarsAdj :
    extendScalars.{max v uB} hf ⊣
      restrictScalars.{max v uB} (IsScalarTower.toAlgHom k A B) hf :=
  Adjunction.mkOfHomEquiv
    { homEquiv := extendScalarsHomEquiv hf
      -- Both naturality squares hold on underlying elements by unfolding.
      homEquiv_naturality_left_symm _ _ := extendScalars_hom_ext hf _ fun _ ↦ rfl
      homEquiv_naturality_right _ _ := rfl }

/-- The adjunction sends `g : B ⊗[A] M ⟶ N` to `m ↦ g (1 ⊗ₜ m)`. -/
@[simp]
theorem extendRestrictScalarsAdj_homEquiv_apply_hom (g : (extendScalars hf).obj M ⟶ N) (m : M) :
    ((extendRestrictScalarsAdj hf).homEquiv M N g).hom m = g.hom ((1 : B) ⊗ₜ[A] m) :=
  (rfl)

/-- The inverse of the adjunction sends `h` to `b ⊗ₜ m ↦ b • h m`. -/
@[simp]
theorem extendRestrictScalarsAdj_homEquiv_symm_apply_hom_tmul
    (h : M ⟶ restrictScalarsObj (IsScalarTower.toAlgHom k A B) hf N)
    (b : B) (m : M) :
    (((extendRestrictScalarsAdj hf).homEquiv M N).symm h).hom (b ⊗ₜ[A] m) = b • h.hom m :=
  (rfl)

/-- The unit of the adjunction is `m ↦ 1 ⊗ₜ m`. The source and target are written explicitly, so
that the left-hand side is in simp normal form. -/
@[simp]
theorem extendRestrictScalarsAdj_unit_app_hom (M : GradedModuleCat.{max v uB} 𝒜) (m : M) :
    Hom.hom (M := M) (N := (restrictScalars (IsScalarTower.toAlgHom k A B) hf).obj
      ((extendScalars hf).obj M)) ((extendRestrictScalarsAdj hf).unit.app M) m =
        (1 : B) ⊗ₜ[A] m :=
  (rfl)

/-- The counit of the adjunction is `b ⊗ₜ n ↦ b • n`. The source and target are written
explicitly, so that the left-hand side is in simp normal form. -/
@[simp]
theorem extendRestrictScalarsAdj_counit_app_hom_tmul (N : GradedModuleCat.{max v uB} ℬ) (b : B)
    (n : restrictScalarsObj (IsScalarTower.toAlgHom k A B) hf N) :
    Hom.hom (M := (extendScalars hf).obj
      ((restrictScalars (IsScalarTower.toAlgHom k A B) hf).obj N)) (N := N)
      ((extendRestrictScalarsAdj hf).counit.app N) (b ⊗ₜ[A] n) = b • n :=
  (rfl)

end Adjunction

section Monoidal

variable {k : Type uk} [CommRing k] {A B : Type uA} [CommRing A] [Algebra k A]
  [CommRing B] [Algebra k B] [Algebra A B] [IsScalarTower k A B]
  {𝒜 : ℤ → Submodule k A} {ℬ : ℤ → Submodule k B} [GradedAlgebra 𝒜] [GradedAlgebra ℬ]
  (hf : ∀ ⦃i : ℤ⦄ ⦃a : A⦄, a ∈ 𝒜 i → algebraMap A B a ∈ ℬ i)

/-- The comparison `B ⊗[A] (M ⊗ N) ≅ (B ⊗[A] M) ⊗ (B ⊗[A] N)`, sending `b ⊗ₜ (m ⊗ₜ n)` to
`(b ⊗ₜ m) ⊗ₜ (1 ⊗ₜ n)`. It preserves total degree. -/
noncomputable def extendScalarsTensorIso (M N : GradedModuleCat.{uA} 𝒜) :
    (extendScalars hf).obj (M ⊗ N) ≅ (extendScalars hf).obj M ⊗ (extendScalars hf).obj N :=
  isoMk (AlgebraTensorModule.distribBaseChange A B M N) fun d z ↦
    haveI := InternalGrading.gradedSMul_ofDecomposition_of_algebraMap_mem hf
    (LinearMap.IsHomogeneous.linearEquiv_mem_piece_iff
      ((InternalGrading.ofDecomposition ℬ).isHomogeneous_of_tmul_mem_tensorProductOver 𝒜
        (M ⊗ N).grading _ _ 0 fun {p q b x} hb hx ↦ by
        -- Fix `b` and check the second factor on homogeneous pure tensors `m ⊗ₜ n`.
        rw [InternalGrading.ofDecomposition_piece] at hb
        rw [add_zero, add_comm]
        rw [tensorObj_grading] at hx
        refine (M.grading.isHomogeneous_of_tmul_mem_tensorProductOver 𝒜 N.grading _
          ((AlgebraTensorModule.distribBaseChange A B M N).toLinearMap.restrictScalars A ∘ₗ
            TensorProduct.mk A B (M ⊗[A] N) b) p fun {q₁ q₂ m n} hm hn ↦ ?_).map_mem hx
        simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, mk_apply,
          LinearEquiv.coe_coe, AlgebraTensorModule.distribBaseChange_tmul]
        convert ((extendScalars hf).obj M).grading.tmul_mem_tensorProductOver ℬ
          ((extendScalars hf).obj N).grading (tmul_mem_extendScalarsObj_piece hf M hb hm)
          (tmul_mem_extendScalarsObj_piece hf N SetLike.GradedOne.one_mem hn) using 2
        omega) d z).symm

/-- The comparison `B ⊗[A] (M ⊗ N) ≅ (B ⊗[A] M) ⊗ (B ⊗[A] N)` on pure tensors. -/
@[simp]
theorem extendScalarsTensorIso_hom_tmul (M N : GradedModuleCat.{uA} 𝒜) (b : B) (m : M) (n : N) :
    (extendScalarsTensorIso hf M N).hom.hom (b ⊗ₜ[A] (m ⊗ₜ[A] n)) =
      (b ⊗ₜ[A] m) ⊗ₜ[B] ((1 : B) ⊗ₜ[A] n) :=
  (rfl)

/-- The inverse comparison `(B ⊗[A] M) ⊗ (B ⊗[A] N) ≅ B ⊗[A] (M ⊗ N)` on pure tensors. -/
@[simp]
theorem extendScalarsTensorIso_inv_tmul (M N : GradedModuleCat.{uA} 𝒜) (b b' : B) (m : M)
    (n : N) :
    (extendScalarsTensorIso hf M N).inv.hom ((b ⊗ₜ[A] m) ⊗ₜ[B] (b' ⊗ₜ[A] n)) =
      (b * b') ⊗ₜ[A] (m ⊗ₜ[A] n) :=
  AlgebraTensorModule.distribBaseChange_symm_tmul ..

/-- The unit comparison `B ⊗[A] A ≅ B`, sending `b ⊗ₜ a` to `a • b`. It preserves total
degree. -/
noncomputable def extendScalarsUnitIso :
    (extendScalars hf).obj (𝟙_ (GradedModuleCat.{uA} 𝒜)) ≅ 𝟙_ (GradedModuleCat.{uA} ℬ) :=
  haveI := InternalGrading.gradedSMul_ofDecomposition_of_algebraMap_mem hf
  isoMk (AlgebraTensorModule.rid A B B) fun d z ↦
    (LinearMap.IsHomogeneous.linearEquiv_mem_piece_iff
      (LinearMap.isHomogeneous_def.2 fun p z hz ↦ by
        -- `B ⊗[A] A` carries the total-degree grading, as in `extendScalarsObj_grading`.
        change z ∈ ((InternalGrading.ofDecomposition ℬ).tensorProductOver 𝒜
          (𝟙_ (GradedModuleCat.{uA} 𝒜)).grading).piece p at hz
        simp only [tensorUnit_grading] at hz ⊢
        -- `AlgebraTensorModule.rid A B B` and `TensorProduct.rid A B` agree on elements.
        exact ((InternalGrading.ofDecomposition ℬ).isHomogeneous_rid_tensorProductOver 𝒜).map_mem
          hz) d z).symm

/-- The unit comparison `B ⊗[A] A ≅ B` sends `b ⊗ₜ a` to `a • b`. -/
@[simp]
theorem extendScalarsUnitIso_hom_tmul (b : B) (a : A) :
    (extendScalarsUnitIso hf).hom.hom (b ⊗ₜ[A] a) = a • b :=
  (rfl)

/-- The inverse unit comparison `B ≅ B ⊗[A] A` sends `b` to `b ⊗ₜ 1`. -/
@[simp]
theorem extendScalarsUnitIso_inv_apply (b : B) :
    (extendScalarsUnitIso hf).inv.hom b = b ⊗ₜ[A] (1 : A) :=
  (rfl)

/-- Morphisms out of `B ⊗[A] (M ⊗ N)` are determined by their values on the tensors
`1 ⊗ₜ (m ⊗ₜ n)`. -/
theorem extendScalars_tensorObj_hom_ext {M N : GradedModuleCat.{uA} 𝒜}
    {P : GradedModuleCat.{uA} ℬ} {f g : (extendScalars hf).obj (M ⊗ N) ⟶ P}
    (h : ∀ (m : M) (n : N), f.hom ((1 : B) ⊗ₜ[A] (m ⊗ₜ[A] n)) =
      g.hom ((1 : B) ⊗ₜ[A] (m ⊗ₜ[A] n))) : f = g :=
  extendScalars_hom_ext hf _ fun z ↦ by
    induction z using TensorProduct.inductionOn with
    | tmul m n => exact h m n
    | add x y hx hy => rw [tmul_add, map_add, map_add, hx, hy]

/-- Morphisms out of `B ⊗[A] ((M ⊗ N) ⊗ P)` are determined by their values on the tensors
`1 ⊗ₜ ((m ⊗ₜ n) ⊗ₜ p)`. -/
theorem extendScalars_tensorObj_tensorObj_hom_ext {M N P : GradedModuleCat.{uA} 𝒜}
    {Q : GradedModuleCat.{uA} ℬ} {f g : (extendScalars hf).obj ((M ⊗ N) ⊗ P) ⟶ Q}
    (h : ∀ (m : M) (n : N) (p : P), f.hom ((1 : B) ⊗ₜ[A] ((m ⊗ₜ[A] n) ⊗ₜ[A] p)) =
      g.hom ((1 : B) ⊗ₜ[A] ((m ⊗ₜ[A] n) ⊗ₜ[A] p))) : f = g :=
  extendScalars_tensorObj_hom_ext hf fun x p ↦ by
    induction x using TensorProduct.inductionOn with
    | tmul m n => exact h m n p
    | add x y hx hy => rw [add_tmul, tmul_add, map_add, map_add, hx, hy]

/-- The comparison `B ⊗[A] (M ⊗ N) ≅ (B ⊗[A] M) ⊗ (B ⊗[A] N)` is natural in `M`. -/
@[reassoc]
theorem extendScalarsTensorIso_hom_naturality_left {M M' : GradedModuleCat.{uA} 𝒜}
    (f : M ⟶ M') (N : GradedModuleCat.{uA} 𝒜) :
    (extendScalarsTensorIso hf M N).hom ≫ (extendScalars hf).map f ▷ (extendScalars hf).obj N =
      (extendScalars hf).map (f ▷ N) ≫ (extendScalarsTensorIso hf M' N).hom :=
  extendScalars_tensorObj_hom_ext hf fun _ _ ↦ rfl

/-- The comparison `B ⊗[A] (M ⊗ N) ≅ (B ⊗[A] M) ⊗ (B ⊗[A] N)` is natural in `N`. -/
@[reassoc]
theorem extendScalarsTensorIso_hom_naturality_right (M : GradedModuleCat.{uA} 𝒜)
    {N N' : GradedModuleCat.{uA} 𝒜} (f : N ⟶ N') :
    (extendScalarsTensorIso hf M N).hom ≫ (extendScalars hf).obj M ◁ (extendScalars hf).map f =
      (extendScalars hf).map (M ◁ f) ≫ (extendScalarsTensorIso hf M N').hom :=
  extendScalars_tensorObj_hom_ext hf fun _ _ ↦ rfl

/-- The comparison `B ⊗[A] (M ⊗ N) ≅ (B ⊗[A] M) ⊗ (B ⊗[A] N)` is compatible with the
associators. -/
@[reassoc]
theorem extendScalarsTensorIso_hom_associativity (M N P : GradedModuleCat.{uA} 𝒜) :
    (extendScalarsTensorIso hf (M ⊗ N) P).hom ≫
        (extendScalarsTensorIso hf M N).hom ▷ (extendScalars hf).obj P ≫
          (α_ ((extendScalars hf).obj M) ((extendScalars hf).obj N)
            ((extendScalars hf).obj P)).hom =
      (extendScalars hf).map (α_ M N P).hom ≫ (extendScalarsTensorIso hf M (N ⊗ P)).hom ≫
        (extendScalars hf).obj M ◁ (extendScalarsTensorIso hf N P).hom :=
  extendScalars_tensorObj_tensorObj_hom_ext hf fun _ _ _ ↦ rfl

/-- The comparisons `B ⊗[A] (A ⊗ M) ≅ (B ⊗[A] A) ⊗ (B ⊗[A] M)` and `B ⊗[A] A ≅ B` are compatible
with the left unitors. -/
theorem extendScalarsTensorIso_hom_left_unitality (M : GradedModuleCat.{uA} 𝒜) :
    (λ_ ((extendScalars hf).obj M)).inv =
      (extendScalars hf).map (λ_ M).inv ≫
        (extendScalarsTensorIso hf (𝟙_ (GradedModuleCat.{uA} 𝒜)) M).hom ≫
          (extendScalarsUnitIso hf).hom ▷ (extendScalars hf).obj M :=
  -- The unit comparison sends `1 ⊗ₜ 1` to `(1 : A) • (1 : B)`.
  extendScalars_hom_ext hf _ fun m ↦
    (congrArg (· ⊗ₜ[B] ((1 : B) ⊗ₜ[A] m)) (one_smul A (1 : B))).symm

/-- The comparisons `B ⊗[A] (M ⊗ A) ≅ (B ⊗[A] M) ⊗ (B ⊗[A] A)` and `B ⊗[A] A ≅ B` are compatible
with the right unitors. -/
theorem extendScalarsTensorIso_hom_right_unitality (M : GradedModuleCat.{uA} 𝒜) :
    (ρ_ ((extendScalars hf).obj M)).inv =
      (extendScalars hf).map (ρ_ M).inv ≫
        (extendScalarsTensorIso hf M (𝟙_ (GradedModuleCat.{uA} 𝒜))).hom ≫
          (extendScalars hf).obj M ◁ (extendScalarsUnitIso hf).hom :=
  extendScalars_hom_ext hf _ fun m ↦
    (congrArg (((1 : B) ⊗ₜ[A] m) ⊗ₜ[B] ·) (one_smul A (1 : B))).symm

/-- Extension of scalars is a strong monoidal functor, with tensor comparison
`(B ⊗[A] M) ⊗ (B ⊗[A] N) ≅ B ⊗[A] (M ⊗ N)` and unit comparison `B ≅ B ⊗[A] A`. -/
noncomputable instance : (extendScalars.{uA} hf).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    (.mk' (εIso := (extendScalarsUnitIso hf).symm)
      (μIso := fun M N ↦ (extendScalarsTensorIso hf M N).symm)
      (extendScalarsTensorIso_hom_naturality_left hf)
      (fun M f ↦ extendScalarsTensorIso_hom_naturality_right hf M f)
      (extendScalarsTensorIso_hom_associativity hf)
      (extendScalarsTensorIso_hom_left_unitality hf)
      (extendScalarsTensorIso_hom_right_unitality hf))

open Functor.LaxMonoidal Functor.OplaxMonoidal

/-- The tensor comparison of extension of scalars is the inverse of `extendScalarsTensorIso`,
`(b ⊗ₜ m) ⊗ₜ (b' ⊗ₜ n) ↦ bb' ⊗ₜ (m ⊗ₜ n)`. -/
@[simp]
theorem extendScalars_μ (M N : GradedModuleCat.{uA} 𝒜) :
    μ (extendScalars hf) M N = (extendScalarsTensorIso hf M N).inv :=
  (rfl)

/-- The inverse tensor comparison of extension of scalars is `extendScalarsTensorIso`,
`b ⊗ₜ (m ⊗ₜ n) ↦ (b ⊗ₜ m) ⊗ₜ (1 ⊗ₜ n)`. -/
@[simp]
theorem extendScalars_δ (M N : GradedModuleCat.{uA} 𝒜) :
    δ (extendScalars hf) M N = (extendScalarsTensorIso hf M N).hom :=
  (rfl)

/-- The unit comparison of extension of scalars is `b ↦ b ⊗ₜ 1`. -/
@[simp]
theorem extendScalars_ε : ε (extendScalars hf) = (extendScalarsUnitIso hf).inv :=
  (rfl)

/-- The inverse unit comparison of extension of scalars is `b ⊗ₜ a ↦ a • b`. -/
@[simp]
theorem extendScalars_η : η (extendScalars hf) = (extendScalarsUnitIso hf).hom :=
  (rfl)

/-- The comparison `B ⊗[A] (M ⊗ N) ≅ (B ⊗[A] M) ⊗ (B ⊗[A] N)` intertwines the symmetries: no sign
appears on either side. -/
@[reassoc]
theorem extendScalarsTensorIso_hom_braiding (M N : GradedModuleCat.{uA} 𝒜) :
    (extendScalars hf).map (β_ M N).hom ≫ (extendScalarsTensorIso hf N M).hom =
      (extendScalarsTensorIso hf M N).hom ≫ (β_ ((extendScalars hf).obj M)
        ((extendScalars hf).obj N)).hom :=
  extendScalars_tensorObj_hom_ext hf fun _ _ ↦ rfl

/-- Extension of scalars is a braided, hence symmetric, monoidal functor: it intertwines the
unsigned symmetries of graded `𝒜`-modules and graded `ℬ`-modules. -/
noncomputable instance : (extendScalars.{uA} hf).Braided where
  braided M N := by
    rw [extendScalars_μ, extendScalars_μ, Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
    exact extendScalarsTensorIso_hom_braiding hf M N

end Monoidal

end GradedModuleCat

end TauCeti

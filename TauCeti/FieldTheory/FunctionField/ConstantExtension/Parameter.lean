/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.ConstantExtension.FractionField
public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Tensor presentations over an extended parameter field

Let `F' = F · K` be a linearly disjoint extension of constants of `F/k`, and let `C` be
an intermediate field with `F/C` algebraic. Multiplication identifies
`(C · K) ⊗[C] F` with `F'`, as algebras over `C · K`. More generally, for any external
subfield `E` of `F` over `k` with `F/E` algebraic and any field `E'` with `E' = E · K`
mapping compatibly into `F'`, multiplication gives an `E'`-algebra isomorphism
`E' ⊗[E] F ≃ₐ[E'] F'` and transports `E`-bases of `F` to `E'`-bases of `F'`.
In particular, when `F/k` is algebraic over `RatFunc k`, this presents `F'` (or any
specified fraction field `Q` of `F ⊗[k] K`) as `RatFunc K ⊗[RatFunc k] F`, proves
`[Q : RatFunc K] = [F : RatFunc k]`, shows that `RatFunc K ⊗[RatFunc k] F` is a field
whenever `F ⊗[k] K` is a domain, and shows that `AlgHom.fractionRingTensorMap` acts as
`id ⊗ g` for every `RatFunc k`-algebra map `g : F₁ →ₐ[RatFunc k] F₂`.

The extension `K/k` can be transcendental. The original extension `F/C` (or `F/E`) need
only be algebraic, and need not be separable or finite. It does not assert that the
original tensor product `F ⊗[k] K` is itself a field.

The construction uses `constantExtensionBasisOfLinearDisjoint` for basis transport
and Mathlib's `Module.Basis.baseChange` and `AlgHom.liftEquiv` for the tensor algebra.

## Main declarations

* `TauCeti.constantExtensionParameterBasis`, `IntermediateField.fractionFieldParameterBasis`:
  transport a `C`-basis of `F` to a `(C · K)`-basis of `F'`.
* `TauCeti.constantExtensionTensorEquiv`, `IntermediateField.fractionFieldParameterEquiv`:
  the `(C · K)`-algebra isomorphism `(C · K) ⊗[C] F ≃ₐ[C · K] F'`.
* `TauCeti.constantExtensionTowerBasis`, `TauCeti.constantExtensionTowerTensorEquiv`,
  `TauCeti.finrank_eq_of_linearDisjoint_tower`: external-base counterparts `E' ⊗[E] F ≃ₐ[E'] F'`
  and `[F' : E'] = [F : E]`.
* `TauCeti.fractionFieldTowerBasis`, `TauCeti.fractionFieldTowerTensorEquiv`,
  `TauCeti.finrank_fractionRing_tensorProduct_eq`,
  `TauCeti.isField_tensorProduct_of_isFractionRing_tensorProduct`: specialization to specified
  fraction fields `Q₁` of `E ⊗[k] K` and `Q₂` of `F ⊗[k] K`, together with naturality
  (`TauCeti.fractionRingTowerAlgHom`,
  `TauCeti.fractionRingTensorMap_fractionFieldTowerTensorEquiv`).
* `TauCeti.ratFuncFractionFieldBasis`, `TauCeti.ratFuncFractionFieldTensorEquiv`,
  `TauCeti.finrank_ratFunc_eq_of_isFractionRing_tensorProduct`,
  `TauCeti.isField_ratFunc_tensorProduct`, `TauCeti.isField_ratFunc_tensorProduct_of_isAlgClosed`,
  `TauCeti.isFractionRing_of_ratFunc_tensorProduct`, `TauCeti.ratFuncFractionRingAlgHom`,
  `TauCeti.fractionRingTensorMap_ratFuncFractionFieldTensorEquiv`: rational-parameter
  specializations for `E = RatFunc k` and `Q₁ = RatFunc K`.

## References

* S. Lang, *Algebra*, the theory of linearly disjoint field extensions.
* H. Stichtenoth, *Algebraic Function Fields and Codes*, second edition, Section III.6.
-/

public section

open scoped TensorProduct IntermediateField

namespace TauCeti

section Compositum

variable {k K F F' : Type*} [Field k] [Field K] [Field F] [Field F']
  [Algebra k K] [Algebra k F] [Algebra k F'] [Algebra K F'] [Algebra F F']
  [IsScalarTower k K F'] [IsScalarTower k F F']

/-- A `C`-basis of an algebraic extension `F/C` transported to a `(C · K)`-basis of the linearly
disjoint constant compositum `F' = F · K`. -/
noncomputable def constantExtensionParameterBasis
    (H : (IsScalarTower.toAlgHom k K F').fieldRange.LinearDisjoint F)
    (h : constantCompositum F K F' = ⊤) (C : IntermediateField k F)
    [Algebra.IsAlgebraic C F] {ι : Type*} (b : Module.Basis ι C F) :
    Module.Basis ι (constantCompositum C K F') F' :=
  (constantExtensionBasisOfLinearDisjoint H h C b).mapCoeffs
    (RingEquiv.subfieldCongr (_root_.IntermediateField.constantCompositum_toSubfield C).symm)
    (fun _ _ ↦ rfl)

/-- `TauCeti.constantExtensionParameterBasis` maps each index `i` to `algebraMap F F' (b i)`. -/
@[simp]
theorem constantExtensionParameterBasis_apply
    (H : (IsScalarTower.toAlgHom k K F').fieldRange.LinearDisjoint F)
    (h : constantCompositum F K F' = ⊤) (C : IntermediateField k F)
    [Algebra.IsAlgebraic C F] {ι : Type*} (b : Module.Basis ι C F) (i : ι) :
    constantExtensionParameterBasis H h C b i = algebraMap F F' (b i) :=
  ((constantExtensionBasisOfLinearDisjoint H h C b).mapCoeffs_apply
    (RingEquiv.subfieldCongr (_root_.IntermediateField.constantCompositum_toSubfield C).symm)
    (fun _ _ ↦ rfl) i).trans (constantExtensionBasisOfLinearDisjoint_apply H h C b i)

/-- Multiplication over the enlarged intermediate field is bijective. -/
private theorem bijective_parameterLift
    (H : (IsScalarTower.toAlgHom k K F').fieldRange.LinearDisjoint F)
    (h : constantCompositum F K F' = ⊤) (C : IntermediateField k F)
    [Algebra.IsAlgebraic C F] :
    Function.Bijective
      (AlgHom.liftEquiv C (constantCompositum C K F') F F'
        (IsScalarTower.toAlgHom C F F')) := by
  let b := Module.Basis.ofVectorSpace C F
  let b' := constantExtensionParameterBasis H h C b
  let e := (b.baseChange (constantCompositum C K F')).equiv b' (Equiv.refl _)
  have he : (AlgHom.liftEquiv C (constantCompositum C K F') F F'
      (IsScalarTower.toAlgHom C F F')).toLinearMap = e.toLinearMap := by
    apply (b.baseChange (constantCompositum C K F')).ext
    intro i
    calc
      _ = algebraMap F F' (b i) := by simp
      _ = b' i := (constantExtensionParameterBasis_apply H h C b i).symm
      _ = e ((b.baseChange _) i) := ((b.baseChange _).equiv_apply i b' (Equiv.refl _)).symm
  have hb : Function.Bijective
      (AlgHom.liftEquiv C (constantCompositum C K F') F F'
        (IsScalarTower.toAlgHom C F F')).toLinearMap := by
    rw [he]
    exact e.bijective
  exact hb

/-- **The tensor presentation over an extended intermediate field.** If `F' = F · K`
linearly disjointly over `k`, and `F/C` is algebraic, multiplication gives an algebra
isomorphism `(C · K) ⊗[C] F ≃ₐ[C · K] F'`. For a function field and `C = k(t)`,
this presents the extended field as a finite algebra over `K(t)`. -/
noncomputable def constantExtensionTensorEquiv
    (H : (IsScalarTower.toAlgHom k K F').fieldRange.LinearDisjoint F)
    (h : constantCompositum F K F' = ⊤) (C : IntermediateField k F)
    [Algebra.IsAlgebraic C F] :
    (constantCompositum C K F') ⊗[C] F ≃ₐ[constantCompositum C K F'] F' :=
  AlgEquiv.ofBijective
    (AlgHom.liftEquiv C (constantCompositum C K F') F F' (IsScalarTower.toAlgHom C F F'))
    (bijective_parameterLift H h C)

/-- On pure tensors the presentation is multiplication in the ambient field. -/
@[simp]
theorem constantExtensionTensorEquiv_tmul
    (H : (IsScalarTower.toAlgHom k K F').fieldRange.LinearDisjoint F)
    (h : constantCompositum F K F' = ⊤) (C : IntermediateField k F)
    [Algebra.IsAlgebraic C F] (a : constantCompositum C K F') (f : F) :
    constantExtensionTensorEquiv H h C (a ⊗ₜ[C] f) = (a : F') * algebraMap F F' f := by
  simp [constantExtensionTensorEquiv, AlgHom.liftEquiv_tmul, Algebra.smul_def]

/-- The inverse presentation sends a product of the two scalar images to a pure tensor. -/
@[simp]
theorem constantExtensionTensorEquiv_symm_mul
    (H : (IsScalarTower.toAlgHom k K F').fieldRange.LinearDisjoint F)
    (h : constantCompositum F K F' = ⊤) (C : IntermediateField k F)
    [Algebra.IsAlgebraic C F] (a : constantCompositum C K F') (f : F) :
    (constantExtensionTensorEquiv H h C).symm ((a : F') * algebraMap F F' f) = a ⊗ₜ[C] f := by
  apply (constantExtensionTensorEquiv H h C).injective
  simp

/-- On the enlarged intermediate field `C · K`, the inverse sends `a` to `a ⊗ₜ 1`. -/
@[simp]
theorem constantExtensionTensorEquiv_symm_coe
    (H : (IsScalarTower.toAlgHom k K F').fieldRange.LinearDisjoint F)
    (h : constantCompositum F K F' = ⊤) (C : IntermediateField k F)
    [Algebra.IsAlgebraic C F] (a : constantCompositum C K F') :
    (constantExtensionTensorEquiv H h C).symm (a : F') = a ⊗ₜ[C] 1 := by
  simpa using constantExtensionTensorEquiv_symm_mul H h C a 1

/-- On the original field `F`, the inverse sends `algebraMap F F' f` to `1 ⊗ₜ f`. -/
@[simp]
theorem constantExtensionTensorEquiv_symm_algebraMap
    (H : (IsScalarTower.toAlgHom k K F').fieldRange.LinearDisjoint F)
    (h : constantCompositum F K F' = ⊤) (C : IntermediateField k F)
    [Algebra.IsAlgebraic C F] (f : F) :
    (constantExtensionTensorEquiv H h C).symm (algebraMap F F' f) = 1 ⊗ₜ[C] f := by
  simpa using constantExtensionTensorEquiv_symm_mul H h C 1 f

end Compositum

section CompositumTower

variable {k K E E' F F' : Type*} [Field k] [Field K] [Field E] [Field E'] [Field F] [Field F']
  [Algebra k K] [Algebra k E] [Algebra k F] [Algebra E F] [IsScalarTower k E F]
  [Algebra k F'] [Algebra K F'] [Algebra F F'] [IsScalarTower k K F'] [IsScalarTower k F F']
  [Algebra K E'] [Algebra E E'] [Algebra E' F'] [IsScalarTower K E' F']

omit [Algebra k K] [Algebra k F'] [IsScalarTower k K F'] [IsScalarTower k F F'] in
/-- When `E' = E · K` and `E → E' → F'` agrees with `E → F → F'`, the image of `E'` in `F'` has
the same underlying subfield as `(image of E) · K`. -/
private theorem fieldRange_toSubfield_eq_constantCompositum
    (hE' : constantCompositum E K E' = ⊤)
    (hcomm : ∀ e : E, algebraMap E' F' (algebraMap E E' e) = algebraMap F F' (algebraMap E F e)) :
    (IsScalarTower.toAlgHom K E' F').fieldRange.toSubfield =
      (constantCompositum (IsScalarTower.toAlgHom k E F).fieldRange K F').toSubfield := by
  set C := (IsScalarTower.toAlgHom k E F).fieldRange
  set C' := (IsScalarTower.toAlgHom K E' F').fieldRange
  refine le_antisymm ?_ ?_
  · rintro _ ⟨y, rfl⟩
    let M : IntermediateField E E' :=
      ((constantCompositum C K F').toSubfield.comap (algebraMap E' F')).toIntermediateField
        fun e ↦ by
          rw [Subfield.mem_comap, hcomm e]
          exact (constantCompositum C K F').algebraMap_mem ⟨algebraMap E F e, ⟨e, rfl⟩⟩
    have hle : constantCompositum E K E' ≤ M :=
      (constantCompositum_le_iff E K E' (K := M)).mpr fun c ↦ by
        rw [← IntermediateField.mem_toSubfield]
        simp only [M, Subfield.toIntermediateField_toSubfield, Subfield.mem_comap,
          ← IsScalarTower.algebraMap_apply K E' F']
        exact algebraMap_mem_constantCompositum C K F' c
    exact hle (hE' ▸ IntermediateField.mem_top)
  · rw [constantCompositum_def, IntermediateField.adjoin_toSubfield, Subfield.closure_le]
    rintro _ (⟨⟨_, ⟨e, rfl⟩⟩, rfl⟩ | ⟨c, rfl⟩)
    · exact ⟨algebraMap E E' e, hcomm e⟩
    · exact ⟨algebraMap K E' c, (IsScalarTower.algebraMap_apply K E' F' c).symm⟩

/-- Transport an `E`-basis of an algebraic extension `F/E` to an `E'`-basis of `F' = F · K` when
`E' = E · K` maps compatibly into `F'`. -/
noncomputable def constantExtensionTowerBasis [Algebra.IsAlgebraic E F]
    (H : (IsScalarTower.toAlgHom k K F').fieldRange.LinearDisjoint F)
    (h : constantCompositum F K F' = ⊤) (hE' : constantCompositum E K E' = ⊤)
    (hcomm : ∀ e : E, algebraMap E' F' (algebraMap E E' e) = algebraMap F F' (algebraMap E F e))
    {ι : Type*} (b : Module.Basis ι E F) : Module.Basis ι E' F' :=
  let fE := IsScalarTower.toAlgHom k E F
  let C := fE.fieldRange
  let eC := fE.equivFieldRange
  let _ : Algebra E C := eC.toRingHom.toAlgebra
  have : IsScalarTower E C F := .of_algebraMap_eq fun _ ↦ rfl
  have : Algebra.IsAlgebraic C F := Algebra.IsAlgebraic.tower_top (K := E) (L := C) (A := F)
  let bC : Module.Basis ι C F := b.mapCoeffs eC.toRingEquiv fun _ _ ↦ by
    simp [Algebra.smul_def, eC, fE, AlgHom.equivFieldRange_apply_coe]
  let fE' := IsScalarTower.toAlgHom K E' F'
  let eE' : E' ≃+* constantCompositum C K F' :=
    fE'.equivFieldRange.toRingEquiv.trans
      (RingEquiv.subfieldCongr (fieldRange_toSubfield_eq_constantCompositum hE' hcomm))
  (constantExtensionParameterBasis H h C bC).mapCoeffs eE'.symm fun a x ↦ by
    obtain ⟨y, rfl⟩ := eE'.surjective a
    rw [RingEquiv.symm_apply_apply, Algebra.smul_def, Algebra.smul_def]
    rfl

/-- `TauCeti.constantExtensionTowerBasis` sends `i` to `algebraMap F F' (b i)`. -/
@[simp]
theorem constantExtensionTowerBasis_apply [Algebra.IsAlgebraic E F]
    (H : (IsScalarTower.toAlgHom k K F').fieldRange.LinearDisjoint F)
    (h : constantCompositum F K F' = ⊤) (hE' : constantCompositum E K E' = ⊤)
    (hcomm : ∀ e : E, algebraMap E' F' (algebraMap E E' e) = algebraMap F F' (algebraMap E F e))
    {ι : Type*} (b : Module.Basis ι E F) (i : ι) :
    constantExtensionTowerBasis H h hE' hcomm b i = algebraMap F F' (b i) := by
  simp [constantExtensionTowerBasis]

/-- Linearly disjoint constant extension preserves the degree over any algebraic base field `E`:
if `F' = F · K` and `E' = E · K` compatibly, then `[F' : E'] = [F : E]`. -/
theorem finrank_eq_of_linearDisjoint_tower [Algebra.IsAlgebraic E F]
    (H : (IsScalarTower.toAlgHom k K F').fieldRange.LinearDisjoint F)
    (h : constantCompositum F K F' = ⊤) (hE' : constantCompositum E K E' = ⊤)
    (hcomm : ∀ e : E, algebraMap E' F' (algebraMap E E' e) = algebraMap F F' (algebraMap E F e)) :
    Module.finrank E' F' = Module.finrank E F := by
  let b := Module.Basis.ofVectorSpace E F
  exact (Module.finrank_eq_nat_card_basis (constantExtensionTowerBasis H h hE' hcomm b)).trans
    (Module.finrank_eq_nat_card_basis b).symm

/-- **External-base tensor presentation of a linearly disjoint constant extension.** If `F/E` is
algebraic, `F' = F · K` linearly disjointly over `k`, and `E' = E · K` maps compatibly into `F'`,
multiplication gives an `E'`-algebra isomorphism `E' ⊗[E] F ≃ₐ[E'] F'`. -/
noncomputable def constantExtensionTowerTensorEquiv [Algebra.IsAlgebraic E F]
    (H : (IsScalarTower.toAlgHom k K F').fieldRange.LinearDisjoint F)
    (h : constantCompositum F K F' = ⊤) (hE' : constantCompositum E K E' = ⊤)
    (hcomm : ∀ e : E, algebraMap E' F' (algebraMap E E' e) = algebraMap F F' (algebraMap E F e)) :
    E' ⊗[E] F ≃ₐ[E'] F' :=
  let _ : Algebra E F' := ((algebraMap E' F').comp (algebraMap E E')).toAlgebra
  have : IsScalarTower E E' F' := .of_algebraMap_eq fun _ ↦ rfl
  let φ : F →ₐ[E] F' :=
    { toRingHom := algebraMap F F'
      commutes' := fun e ↦ (hcomm e).symm }
  AlgEquiv.ofBijective (AlgHom.liftEquiv E E' F F' φ) <| by
    let b := Module.Basis.ofVectorSpace E F
    let b' := constantExtensionTowerBasis H h hE' hcomm b
    let e := (b.baseChange E').equiv b' (Equiv.refl _)
    have he : (AlgHom.liftEquiv E E' F F' φ).toLinearMap = e.toLinearMap := by
      apply (b.baseChange E').ext
      intro i
      calc
        _ = algebraMap F F' (b i) := by simp [φ]
        _ = b' i := (constantExtensionTowerBasis_apply H h hE' hcomm b i).symm
        _ = e ((b.baseChange E') i) := ((b.baseChange E').equiv_apply i b' (Equiv.refl _)).symm
    have hb : Function.Bijective (AlgHom.liftEquiv E E' F F' φ).toLinearMap := by
      rw [he]
      exact e.bijective
    exact hb

/-- On pure tensors `constantExtensionTowerTensorEquiv` multiplies the two images in `F'`. -/
@[simp]
theorem constantExtensionTowerTensorEquiv_tmul [Algebra.IsAlgebraic E F]
    (H : (IsScalarTower.toAlgHom k K F').fieldRange.LinearDisjoint F)
    (h : constantCompositum F K F' = ⊤) (hE' : constantCompositum E K E' = ⊤)
    (hcomm : ∀ e : E, algebraMap E' F' (algebraMap E E' e) = algebraMap F F' (algebraMap E F e))
    (a : E') (f : F) :
    constantExtensionTowerTensorEquiv H h hE' hcomm (a ⊗ₜ[E] f) =
      algebraMap E' F' a * algebraMap F F' f :=
  Algebra.smul_def a (algebraMap F F' f)

/-- The inverse of `constantExtensionTowerTensorEquiv` sends a product of images to a pure
tensor. -/
@[simp]
theorem constantExtensionTowerTensorEquiv_symm_mul [Algebra.IsAlgebraic E F]
    (H : (IsScalarTower.toAlgHom k K F').fieldRange.LinearDisjoint F)
    (h : constantCompositum F K F' = ⊤) (hE' : constantCompositum E K E' = ⊤)
    (hcomm : ∀ e : E, algebraMap E' F' (algebraMap E E' e) = algebraMap F F' (algebraMap E F e))
    (a : E') (f : F) :
    (constantExtensionTowerTensorEquiv H h hE' hcomm).symm
        (algebraMap E' F' a * algebraMap F F' f) = a ⊗ₜ[E] f := by
  apply (constantExtensionTowerTensorEquiv H h hE' hcomm).injective
  simp

/-- On `E'`, the inverse of `constantExtensionTowerTensorEquiv` sends `algebraMap E' F' a` to
`a ⊗ₜ 1`. -/
theorem constantExtensionTowerTensorEquiv_symm_algebraMap_left [Algebra.IsAlgebraic E F]
    (H : (IsScalarTower.toAlgHom k K F').fieldRange.LinearDisjoint F)
    (h : constantCompositum F K F' = ⊤) (hE' : constantCompositum E K E' = ⊤)
    (hcomm : ∀ e : E, algebraMap E' F' (algebraMap E E' e) = algebraMap F F' (algebraMap E F e))
    (a : E') :
    (constantExtensionTowerTensorEquiv H h hE' hcomm).symm (algebraMap E' F' a) = a ⊗ₜ[E] 1 := by
  simp

/-- On `F`, the inverse of `constantExtensionTowerTensorEquiv` sends `algebraMap F F' f` to
`1 ⊗ₜ f`. -/
@[simp]
theorem constantExtensionTowerTensorEquiv_symm_algebraMap_right [Algebra.IsAlgebraic E F]
    (H : (IsScalarTower.toAlgHom k K F').fieldRange.LinearDisjoint F)
    (h : constantCompositum F K F' = ⊤) (hE' : constantCompositum E K E' = ⊤)
    (hcomm : ∀ e : E, algebraMap E' F' (algebraMap E E' e) = algebraMap F F' (algebraMap E F e))
    (f : F) :
    (constantExtensionTowerTensorEquiv H h hE' hcomm).symm (algebraMap F F' f) = 1 ⊗ₜ[E] f := by
  simpa using constantExtensionTowerTensorEquiv_symm_mul H h hE' hcomm 1 f

end CompositumTower

section FractionField

attribute [local instance] Algebra.TensorProduct.rightAlgebra
  Algebra.TensorProduct.right_isScalarTower

variable {k F F' : Type*} [Field k] [Field F] [Field F']
  [Algebra k F] [Algebra k F'] [Algebra F F'] [IsScalarTower k F F']

/-- Transport a `C`-basis of an algebraic extension `F/C` to a `(C · K)`-basis of any specified
fraction field `F'` of `F ⊗[k] K`. -/
noncomputable def _root_.IntermediateField.fractionFieldParameterBasis (C : IntermediateField k F)
    (K : Type*) [Field K] [Algebra k K] [Algebra K F'] [IsScalarTower k K F']
    [Algebra (F ⊗[k] K) F'] [IsScalarTower k (F ⊗[k] K) F'] [IsScalarTower F (F ⊗[k] K) F']
    [IsScalarTower K (F ⊗[k] K) F'] [IsFractionRing (F ⊗[k] K) F']
    [Algebra.IsAlgebraic C F] {ι : Type*} (b : Module.Basis ι C F) :
    Module.Basis ι (constantCompositum C K F') F' :=
  constantExtensionParameterBasis (linearDisjoint_of_isFractionRing_tensorProduct (k := k))
    (constantCompositum_eq_top_of_isFractionRing_tensorProduct (k := k) (K := K)) C b

/-- `IntermediateField.fractionFieldParameterBasis` sends `i` to `algebraMap F F' (b i)`. -/
@[simp]
theorem _root_.IntermediateField.fractionFieldParameterBasis_apply (C : IntermediateField k F)
    (K : Type*) [Field K] [Algebra k K] [Algebra K F'] [IsScalarTower k K F']
    [Algebra (F ⊗[k] K) F'] [IsScalarTower k (F ⊗[k] K) F'] [IsScalarTower F (F ⊗[k] K) F']
    [IsScalarTower K (F ⊗[k] K) F'] [IsFractionRing (F ⊗[k] K) F']
    [Algebra.IsAlgebraic C F] {ι : Type*} (b : Module.Basis ι C F) (i : ι) :
    C.fractionFieldParameterBasis K b i = algebraMap F F' (b i) :=
  constantExtensionParameterBasis_apply _ _ C b i

variable {K : Type*} [Field K] [Algebra k K] [Algebra K F'] [IsScalarTower k K F']
  [Algebra (F ⊗[k] K) F'] [IsScalarTower k (F ⊗[k] K) F'] [IsScalarTower F (F ⊗[k] K) F']
  [IsScalarTower K (F ⊗[k] K) F'] [IsFractionRing (F ⊗[k] K) F']

/-- **A tensor presentation of the fraction field after extension of constants.**
For any specified fraction field `F'` of the domain `F ⊗[k] K`, and any intermediate
field `C` with `F/C` algebraic, multiplication identifies `(C · K) ⊗[C] F` with `F'`.
For a transcendental parameter `t` of a function field, take `C = k(t)`; the
coefficient field is `K(t)` by `constantCompositum_adjoin_simple_toSubfield`.
No algebraicity or separability of `K/k` is required. -/
noncomputable def _root_.IntermediateField.fractionFieldParameterEquiv (C : IntermediateField k F)
    [Algebra.IsAlgebraic C F] :
    (constantCompositum C K F') ⊗[C] F ≃ₐ[constantCompositum C K F'] F' :=
  constantExtensionTensorEquiv (linearDisjoint_of_isFractionRing_tensorProduct (k := k))
    (constantCompositum_eq_top_of_isFractionRing_tensorProduct (k := k) (K := K)) C

/-- The fraction-field presentation respects the specified maps of the two factors. -/
@[simp]
theorem _root_.IntermediateField.fractionFieldParameterEquiv_tmul (C : IntermediateField k F)
    [Algebra.IsAlgebraic C F] (a : constantCompositum C K F') (f : F) :
    C.fractionFieldParameterEquiv (a ⊗ₜ[C] f) = (a : F') * algebraMap F F' f := by
  simp only [IntermediateField.fractionFieldParameterEquiv, constantExtensionTensorEquiv_tmul]

/-- The inverse fraction-field presentation recovers pure tensors from products. -/
@[simp]
theorem _root_.IntermediateField.fractionFieldParameterEquiv_symm_mul (C : IntermediateField k F)
    [Algebra.IsAlgebraic C F] (a : constantCompositum C K F') (f : F) :
    (C.fractionFieldParameterEquiv).symm ((a : F') * algebraMap F F' f) = a ⊗ₜ[C] f := by
  apply (C.fractionFieldParameterEquiv).injective
  simp

end FractionField

section FractionFieldTower

attribute [local instance] Algebra.TensorProduct.rightAlgebra
  Algebra.TensorProduct.right_isScalarTower

section Single

variable {k K E F Q₁ Q₂ : Type*} [Field k] [Field K] [Field E] [Field F] [Field Q₁] [Field Q₂]
  [Algebra k K] [Algebra k E] [Algebra k F] [Algebra E F] [IsScalarTower k E F]
  [Algebra (E ⊗[k] K) Q₁] [Algebra E Q₁] [Algebra K Q₁]
  [IsScalarTower E (E ⊗[k] K) Q₁] [IsScalarTower K (E ⊗[k] K) Q₁] [IsFractionRing (E ⊗[k] K) Q₁]
  [Algebra (F ⊗[k] K) Q₂] [Algebra k Q₂] [Algebra F Q₂] [Algebra K Q₂]
  [IsScalarTower k (F ⊗[k] K) Q₂] [IsScalarTower F (F ⊗[k] K) Q₂] [IsScalarTower K (F ⊗[k] K) Q₂]
  [IsScalarTower k F Q₂] [IsScalarTower k K Q₂] [IsFractionRing (F ⊗[k] K) Q₂]
  [Algebra Q₁ Q₂] [IsScalarTower K Q₁ Q₂]

include k K in
/-- Transport an `E`-basis of an algebraic extension `F/E` to a `Q₁`-basis of `Q₂`, for specified
fraction fields `Q₁` of `E ⊗[k] K` and `Q₂` of `F ⊗[k] K`. -/
noncomputable def fractionFieldTowerBasis [Algebra.IsAlgebraic E F]
    (hcomm : ∀ e : E, algebraMap Q₁ Q₂ (algebraMap E Q₁ e) = algebraMap F Q₂ (algebraMap E F e))
    {ι : Type*} (b : Module.Basis ι E F) : Module.Basis ι Q₁ Q₂ :=
  constantExtensionTowerBasis (linearDisjoint_of_isFractionRing_tensorProduct (k := k))
    (constantCompositum_eq_top_of_isFractionRing_tensorProduct (k := k) (K := K))
    (constantCompositum_eq_top_of_isFractionRing_tensorProduct (k := k) (K := K)) hcomm b

/-- `TauCeti.fractionFieldTowerBasis` sends `i` to `algebraMap F Q₂ (b i)`. -/
@[simp]
theorem fractionFieldTowerBasis_apply [Algebra.IsAlgebraic E F]
    (hcomm : ∀ e : E, algebraMap Q₁ Q₂ (algebraMap E Q₁ e) = algebraMap F Q₂ (algebraMap E F e))
    {ι : Type*} (b : Module.Basis ι E F) (i : ι) :
    (fractionFieldTowerBasis (k := k) (K := K) hcomm b) i = algebraMap F Q₂ (b i) :=
  constantExtensionTowerBasis_apply _ _ _ hcomm b i

include k K in
/-- Extending constants via fraction fields of tensor products preserves `[F : E]` for any
algebraic extension `F/E`. -/
theorem finrank_fractionRing_tensorProduct_eq [Algebra.IsAlgebraic E F]
    (hcomm : ∀ e : E, algebraMap Q₁ Q₂ (algebraMap E Q₁ e) = algebraMap F Q₂ (algebraMap E F e)) :
    Module.finrank Q₁ Q₂ = Module.finrank E F :=
  finrank_eq_of_linearDisjoint_tower (linearDisjoint_of_isFractionRing_tensorProduct (k := k))
    (constantCompositum_eq_top_of_isFractionRing_tensorProduct (k := k) (K := K))
    (constantCompositum_eq_top_of_isFractionRing_tensorProduct (k := k) (K := K)) hcomm

include k K in
/-- **Tensor presentation of a fraction field over a base fraction field.** For an algebraic
extension `F/E` over `k` and specified fraction fields `Q₁` of `E ⊗[k] K` and `Q₂` of `F ⊗[k] K`
mapping compatibly on `E` and `K`, multiplication gives `Q₁ ⊗[E] F ≃ₐ[Q₁] Q₂` (and hence
`Q₁ ⊗[E] F ≃ₐ[K] Q₂` via `AlgEquiv.restrictScalars K`). -/
noncomputable def fractionFieldTowerTensorEquiv [Algebra.IsAlgebraic E F]
    (hcomm : ∀ e : E, algebraMap Q₁ Q₂ (algebraMap E Q₁ e) = algebraMap F Q₂ (algebraMap E F e)) :
    Q₁ ⊗[E] F ≃ₐ[Q₁] Q₂ :=
  constantExtensionTowerTensorEquiv (linearDisjoint_of_isFractionRing_tensorProduct (k := k))
    (constantCompositum_eq_top_of_isFractionRing_tensorProduct (k := k) (K := K))
    (constantCompositum_eq_top_of_isFractionRing_tensorProduct (k := k) (K := K)) hcomm

/-- On pure tensors `fractionFieldTowerTensorEquiv` multiplies the two images in `Q₂`. -/
@[simp]
theorem fractionFieldTowerTensorEquiv_tmul [Algebra.IsAlgebraic E F]
    (hcomm : ∀ e : E, algebraMap Q₁ Q₂ (algebraMap E Q₁ e) = algebraMap F Q₂ (algebraMap E F e))
    (q : Q₁) (f : F) :
    (fractionFieldTowerTensorEquiv (k := k) (K := K) hcomm) (q ⊗ₜ[E] f) =
      algebraMap Q₁ Q₂ q * algebraMap F Q₂ f :=
  constantExtensionTowerTensorEquiv_tmul _ _ _ hcomm q f

/-- The inverse of `fractionFieldTowerTensorEquiv` sends a product of images to a pure tensor. -/
@[simp]
theorem fractionFieldTowerTensorEquiv_symm_mul [Algebra.IsAlgebraic E F]
    (hcomm : ∀ e : E, algebraMap Q₁ Q₂ (algebraMap E Q₁ e) = algebraMap F Q₂ (algebraMap E F e))
    (q : Q₁) (f : F) :
    ((fractionFieldTowerTensorEquiv (k := k) (K := K) hcomm).symm)
        (algebraMap Q₁ Q₂ q * algebraMap F Q₂ f) = q ⊗ₜ[E] f :=
  constantExtensionTowerTensorEquiv_symm_mul _ _ _ hcomm q f

/-- On `Q₁`, `(fractionFieldTowerTensorEquiv hcomm).symm` sends `algebraMap Q₁ Q₂ q` to
`q ⊗ₜ 1`. -/
theorem fractionFieldTowerTensorEquiv_symm_algebraMap_left [Algebra.IsAlgebraic E F]
    (hcomm : ∀ e : E, algebraMap Q₁ Q₂ (algebraMap E Q₁ e) = algebraMap F Q₂ (algebraMap E F e))
    (q : Q₁) :
    ((fractionFieldTowerTensorEquiv (k := k) (K := K) hcomm).symm) (algebraMap Q₁ Q₂ q) =
      q ⊗ₜ[E] 1 :=
  constantExtensionTowerTensorEquiv_symm_algebraMap_left _ _ _ hcomm q

/-- On `F`, `(fractionFieldTowerTensorEquiv hcomm).symm` sends `algebraMap F Q₂ f` to
`1 ⊗ₜ f`. -/
@[simp]
theorem fractionFieldTowerTensorEquiv_symm_algebraMap_right [Algebra.IsAlgebraic E F]
    (hcomm : ∀ e : E, algebraMap Q₁ Q₂ (algebraMap E Q₁ e) = algebraMap F Q₂ (algebraMap E F e))
    (f : F) :
    ((fractionFieldTowerTensorEquiv (k := k) (K := K) hcomm).symm) (algebraMap F Q₂ f) =
      1 ⊗ₜ[E] f :=
  constantExtensionTowerTensorEquiv_symm_algebraMap_right _ _ _ hcomm f

end Single

section FieldCriterion

variable {k K E : Type*} [Field k] [Field K] [Field E] [Algebra k K] [Algebra k E]
  (F Q₁ : Type*) [Field F] [Field Q₁] [Algebra k F] [Algebra E F] [IsScalarTower k E F]
  [Algebra.IsAlgebraic E F] [IsDomain (F ⊗[k] K)]
  [Algebra (E ⊗[k] K) Q₁] [Algebra E Q₁] [Algebra K Q₁]
  [IsScalarTower E (E ⊗[k] K) Q₁] [IsScalarTower K (E ⊗[k] K) Q₁] [IsFractionRing (E ⊗[k] K) Q₁]

include k K in
/-- **If `F ⊗[k] K` is a domain and `F/E` is algebraic, `Q₁ ⊗[E] F` is a field**, for any
specified fraction field `Q₁` of `E ⊗[k] K`: it is isomorphic as a `Q₁`-algebra to
`FractionRing (F ⊗[k] K)`. -/
theorem isField_tensorProduct_of_isFractionRing_tensorProduct : IsField (Q₁ ⊗[E] F) := by
  let Q₂ := FractionRing (F ⊗[k] K)
  let j : Q₁ →ₐ[K] Q₂ :=
    (IsScalarTower.toAlgHom k E F).fractionRingTensorMap (algebraMap E F).injective K Q₁ Q₂
  let _ : Algebra Q₁ Q₂ := j.toRingHom.toAlgebra
  have : IsScalarTower K Q₁ Q₂ := .of_algebraMap_eq fun c ↦ (j.commutes c).symm
  have hcomm (e : E) :
      algebraMap Q₁ Q₂ (algebraMap E Q₁ e) = algebraMap F Q₂ (algebraMap E F e) :=
    (IsScalarTower.toAlgHom k E F).fractionRingTensorMap_algebraMap_left
      (algebraMap E F).injective K Q₁ Q₂ e
  exact ((fractionFieldTowerTensorEquiv (k := k) (K := K) (Q₂ := Q₂) hcomm).toMulEquiv).isField
    (Field.toIsField Q₂)

include k K in
/-- Under the hypotheses of `TauCeti.isField_tensorProduct_of_isFractionRing_tensorProduct`,
`Q₁ ⊗[E] F` is an integral domain. -/
theorem isDomain_tensorProduct_of_isFractionRing_tensorProduct_tower : IsDomain (Q₁ ⊗[E] F) :=
  let _ : Field (Q₁ ⊗[E] F) :=
    (isField_tensorProduct_of_isFractionRing_tensorProduct (k := k) (K := K) F Q₁).toField
  inferInstance

end FieldCriterion

section Morphism

variable {k K E F₁ F₂ Q₁ Q₂ Q₂' : Type*}
  [Field k] [Field K] [Field E] [Field F₁] [Field F₂] [Field Q₁] [Field Q₂] [Field Q₂']
  [Algebra k K] [Algebra k E] [Algebra k F₁] [Algebra k F₂]
  [Algebra E F₁] [Algebra E F₂] [IsScalarTower k E F₁] [IsScalarTower k E F₂]
  [Algebra (E ⊗[k] K) Q₁] [Algebra E Q₁] [Algebra K Q₁]
  [IsScalarTower E (E ⊗[k] K) Q₁] [IsScalarTower K (E ⊗[k] K) Q₁] [IsFractionRing (E ⊗[k] K) Q₁]
  [Algebra (F₁ ⊗[k] K) Q₂] [Algebra F₁ Q₂] [Algebra K Q₂]
  [IsScalarTower F₁ (F₁ ⊗[k] K) Q₂] [IsScalarTower K (F₁ ⊗[k] K) Q₂]
  [IsFractionRing (F₁ ⊗[k] K) Q₂]
  [Algebra (F₂ ⊗[k] K) Q₂'] [Algebra F₂ Q₂'] [Algebra K Q₂']
  [IsScalarTower F₂ (F₂ ⊗[k] K) Q₂'] [IsScalarTower K (F₂ ⊗[k] K) Q₂']
  [IsFractionRing (F₂ ⊗[k] K) Q₂']
  [Algebra Q₁ Q₂] [Algebra Q₁ Q₂'] [IsScalarTower K Q₁ Q₂] [IsScalarTower K Q₁ Q₂']

/-- For any `E`-algebra map `g : F₁ →ₐ[E] F₂`, the induced `K`-algebra map `Q₂ →ₐ[K] Q₂'` on
specified fraction fields automatically fixes the base fraction field `Q₁`. -/
theorem fractionRingTensorMap_algebraMap_tower
    (hcomm₁ : ∀ e : E,
      algebraMap Q₁ Q₂ (algebraMap E Q₁ e) = algebraMap F₁ Q₂ (algebraMap E F₁ e))
    (hcomm₂ : ∀ e : E,
      algebraMap Q₁ Q₂' (algebraMap E Q₁ e) = algebraMap F₂ Q₂' (algebraMap E F₂ e))
    (g : F₁ →ₐ[E] F₂) (q : Q₁) :
    (g.restrictScalars k).fractionRingTensorMap (g.restrictScalars k).injective K Q₂ Q₂'
        (algebraMap Q₁ Q₂ q) =
      algebraMap Q₁ Q₂' q := by
  have hG :
      ((g.restrictScalars k).fractionRingTensorMap (g.restrictScalars k).injective K Q₂ Q₂').comp
        (IsScalarTower.toAlgHom K Q₁ Q₂) = IsScalarTower.toAlgHom K Q₁ Q₂' := by
    refine algHom_ext_of_isFractionRing_tensorProduct (k := k) (A := E) (K := K) (Q := Q₁)
      fun e ↦ ?_
    simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', hcomm₁ e, hcomm₂ e]
    rw [AlgHom.fractionRingTensorMap_algebraMap_left, AlgHom.restrictScalars_apply, g.commutes]
  exact congr($hG q)

include k K in
/-- An `E`-algebra map `g : F₁ →ₐ[E] F₂` induces a canonical `Q₁`-algebra map `Q₂ →ₐ[Q₁] Q₂'`
between specified fraction fields of `F₁ ⊗[k] K` and `F₂ ⊗[k] K`, extending `g` on `F₁`. -/
noncomputable def fractionRingTowerAlgHom
    (hcomm₁ : ∀ e : E,
      algebraMap Q₁ Q₂ (algebraMap E Q₁ e) = algebraMap F₁ Q₂ (algebraMap E F₁ e))
    (hcomm₂ : ∀ e : E,
      algebraMap Q₁ Q₂' (algebraMap E Q₁ e) = algebraMap F₂ Q₂' (algebraMap E F₂ e))
    (g : F₁ →ₐ[E] F₂) : Q₂ →ₐ[Q₁] Q₂' :=
  { (g.restrictScalars k).fractionRingTensorMap (g.restrictScalars k).injective K Q₂ Q₂' with
    commutes' := fractionRingTensorMap_algebraMap_tower hcomm₁ hcomm₂ g }

/-- Underlying function of `TauCeti.fractionRingTowerAlgHom`. -/
theorem coe_fractionRingTowerAlgHom
    (hcomm₁ : ∀ e : E,
      algebraMap Q₁ Q₂ (algebraMap E Q₁ e) = algebraMap F₁ Q₂ (algebraMap E F₁ e))
    (hcomm₂ : ∀ e : E,
      algebraMap Q₁ Q₂' (algebraMap E Q₁ e) = algebraMap F₂ Q₂' (algebraMap E F₂ e))
    (g : F₁ →ₐ[E] F₂) :
    ⇑(fractionRingTowerAlgHom (k := k) (K := K) hcomm₁ hcomm₂ g) =
      (g.restrictScalars k).fractionRingTensorMap (g.restrictScalars k).injective K Q₂ Q₂' := by
  ext
  rfl

/-- On `F₁`, `TauCeti.fractionRingTowerAlgHom` agrees with `g`. -/
@[simp]
theorem fractionRingTowerAlgHom_algebraMap_left
    (hcomm₁ : ∀ e : E,
      algebraMap Q₁ Q₂ (algebraMap E Q₁ e) = algebraMap F₁ Q₂ (algebraMap E F₁ e))
    (hcomm₂ : ∀ e : E,
      algebraMap Q₁ Q₂' (algebraMap E Q₁ e) = algebraMap F₂ Q₂' (algebraMap E F₂ e))
    (g : F₁ →ₐ[E] F₂) (f : F₁) :
    (fractionRingTowerAlgHom (k := k) (K := K) hcomm₁ hcomm₂ g) (algebraMap F₁ Q₂ f) =
      algebraMap F₂ Q₂' (g f) :=
  (g.restrictScalars k).fractionRingTensorMap_algebraMap_left
    (g.restrictScalars k).injective K Q₂ Q₂' f

/-- **Naturality of `fractionFieldTowerTensorEquiv`.** Under the tensor presentations
`Q₁ ⊗[E] F₁ ≃ₐ[Q₁] Q₂` and `Q₁ ⊗[E] F₂ ≃ₐ[Q₁] Q₂'`, the map induced on fraction fields by an
`E`-algebra homomorphism `g : F₁ →ₐ[E] F₂` is `id ⊗ g`. -/
theorem fractionRingTensorMap_fractionFieldTowerTensorEquiv
    [Algebra k Q₂] [IsScalarTower k (F₁ ⊗[k] K) Q₂] [IsScalarTower k F₁ Q₂]
    [IsScalarTower k K Q₂] [Algebra k Q₂'] [IsScalarTower k (F₂ ⊗[k] K) Q₂']
    [IsScalarTower k F₂ Q₂'] [IsScalarTower k K Q₂']
    [Algebra.IsAlgebraic E F₁] [Algebra.IsAlgebraic E F₂]
    (hcomm₁ : ∀ e : E,
      algebraMap Q₁ Q₂ (algebraMap E Q₁ e) = algebraMap F₁ Q₂ (algebraMap E F₁ e))
    (hcomm₂ : ∀ e : E,
      algebraMap Q₁ Q₂' (algebraMap E Q₁ e) = algebraMap F₂ Q₂' (algebraMap E F₂ e))
    (g : F₁ →ₐ[E] F₂) (x : Q₁ ⊗[E] F₁) :
    (g.restrictScalars k).fractionRingTensorMap (g.restrictScalars k).injective K Q₂ Q₂'
        ((fractionFieldTowerTensorEquiv (k := k) (K := K) hcomm₁) x) =
      (fractionFieldTowerTensorEquiv (k := k) (K := K) hcomm₂)
        (Algebra.TensorProduct.map (AlgHom.id Q₁ Q₁) g x) := by
  induction x with
  | tmul q f =>
    rw [fractionFieldTowerTensorEquiv_tmul, map_mul,
      fractionRingTensorMap_algebraMap_tower hcomm₁ hcomm₂ g q,
      (g.restrictScalars k).fractionRingTensorMap_algebraMap_left
        (g.restrictScalars k).injective K Q₂ Q₂' f]
    simp
  | add x y hx hy =>
    rw [map_add, map_add, map_add, map_add, hx, hy]

end Morphism

end FractionFieldTower

section RatFunc

attribute [local instance] Algebra.TensorProduct.rightAlgebra
  Algebra.TensorProduct.right_isScalarTower

section Presentation

variable {k K F Q : Type*} [Field k] [Field K] [Field F] [Field Q]
  [Algebra k K] [Algebra k F] [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
  [Algebra.IsAlgebraic (RatFunc k) F]
  [Algebra (RatFunc k) (RatFunc K)] [IsScalarTower k (RatFunc k) (RatFunc K)]
  [Algebra (F ⊗[k] K) Q] [Algebra k Q] [Algebra F Q] [Algebra K Q]
  [IsScalarTower k (F ⊗[k] K) Q] [IsScalarTower F (F ⊗[k] K) Q] [IsScalarTower K (F ⊗[k] K) Q]
  [IsScalarTower k F Q] [IsScalarTower k K Q] [IsFractionRing (F ⊗[k] K) Q]
  [Algebra (RatFunc K) Q] [IsScalarTower K (RatFunc K) Q]

/-- Transport a `RatFunc k`-basis of an algebraic extension `F / RatFunc k` to a `RatFunc K`-basis
of any specified fraction field `Q` of `F ⊗[k] K`. -/
noncomputable def ratFuncFractionFieldBasis
    (hX : algebraMap (RatFunc k) (RatFunc K) RatFunc.X = RatFunc.X)
    (hX' : algebraMap F Q (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc K) Q RatFunc.X)
    {ι : Type*} (b : Module.Basis ι (RatFunc k) F) : Module.Basis ι (RatFunc K) Q :=
  constantExtensionTowerBasis (linearDisjoint_of_isFractionRing_tensorProduct (k := k))
    (constantCompositum_eq_top_of_isFractionRing_tensorProduct (k := k) (K := K))
    (constantCompositum_ratFunc_eq_top hX)
    (algebraMap_ratFunc_apply_eq hX hX') b

/-- `TauCeti.ratFuncFractionFieldBasis` sends `i` to `algebraMap F Q (b i)`. -/
@[simp]
theorem ratFuncFractionFieldBasis_apply
    (hX : algebraMap (RatFunc k) (RatFunc K) RatFunc.X = RatFunc.X)
    (hX' : algebraMap F Q (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc K) Q RatFunc.X)
    {ι : Type*} (b : Module.Basis ι (RatFunc k) F) (i : ι) :
    ratFuncFractionFieldBasis hX hX' b i = algebraMap F Q (b i) :=
  constantExtensionTowerBasis_apply _ _ _ _ b i

/-- Extending constants through a fraction field of `F ⊗[k] K` preserves the degree over the
rational function field: `[Q : RatFunc K] = [F : RatFunc k]`. Here `K/k` may be transcendental. -/
theorem finrank_ratFunc_eq_of_isFractionRing_tensorProduct
    (hX : algebraMap (RatFunc k) (RatFunc K) RatFunc.X = RatFunc.X)
    (hX' : algebraMap F Q (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc K) Q RatFunc.X) :
    Module.finrank (RatFunc K) Q = Module.finrank (RatFunc k) F :=
  finrank_eq_of_linearDisjoint_tower (linearDisjoint_of_isFractionRing_tensorProduct (k := k))
    (constantCompositum_eq_top_of_isFractionRing_tensorProduct (k := k) (K := K))
    (constantCompositum_ratFunc_eq_top hX)
    (algebraMap_ratFunc_apply_eq hX hX')

/-- **Tensor presentation of a fraction field over `RatFunc K`.** If `F` is algebraic over
`RatFunc k` and `Q` is a specified fraction field of `F ⊗[k] K` on which the variables of
`RatFunc k` and `RatFunc K` act compatibly, multiplication gives an isomorphism
`RatFunc K ⊗[RatFunc k] F ≃ₐ[RatFunc K] Q` (and hence `RatFunc K ⊗[RatFunc k] F ≃ₐ[K] Q` via
`AlgEquiv.restrictScalars K`). -/
noncomputable def ratFuncFractionFieldTensorEquiv
    (hX : algebraMap (RatFunc k) (RatFunc K) RatFunc.X = RatFunc.X)
    (hX' : algebraMap F Q (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc K) Q RatFunc.X) :
    RatFunc K ⊗[RatFunc k] F ≃ₐ[RatFunc K] Q :=
  constantExtensionTowerTensorEquiv (linearDisjoint_of_isFractionRing_tensorProduct (k := k))
    (constantCompositum_eq_top_of_isFractionRing_tensorProduct (k := k) (K := K))
    (constantCompositum_ratFunc_eq_top hX)
    (algebraMap_ratFunc_apply_eq hX hX')

/-- On pure tensors `ratFuncFractionFieldTensorEquiv` multiplies the two images in `Q`. -/
@[simp]
theorem ratFuncFractionFieldTensorEquiv_tmul
    (hX : algebraMap (RatFunc k) (RatFunc K) RatFunc.X = RatFunc.X)
    (hX' : algebraMap F Q (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc K) Q RatFunc.X)
    (a : RatFunc K) (f : F) :
    ratFuncFractionFieldTensorEquiv hX hX' (a ⊗ₜ[RatFunc k] f) =
      algebraMap (RatFunc K) Q a * algebraMap F Q f :=
  constantExtensionTowerTensorEquiv_tmul _ _ _ _ a f

/-- The inverse of `ratFuncFractionFieldTensorEquiv` sends a product of images to a pure tensor. -/
@[simp]
theorem ratFuncFractionFieldTensorEquiv_symm_mul
    (hX : algebraMap (RatFunc k) (RatFunc K) RatFunc.X = RatFunc.X)
    (hX' : algebraMap F Q (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc K) Q RatFunc.X)
    (a : RatFunc K) (f : F) :
    (ratFuncFractionFieldTensorEquiv hX hX').symm (algebraMap (RatFunc K) Q a * algebraMap F Q f) =
      a ⊗ₜ[RatFunc k] f :=
  constantExtensionTowerTensorEquiv_symm_mul _ _ _ _ a f

/-- On `RatFunc K`, `(ratFuncFractionFieldTensorEquiv hX hX').symm` sends `a` to `a ⊗ₜ 1`. -/
theorem ratFuncFractionFieldTensorEquiv_symm_algebraMap_left
    (hX : algebraMap (RatFunc k) (RatFunc K) RatFunc.X = RatFunc.X)
    (hX' : algebraMap F Q (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc K) Q RatFunc.X)
    (a : RatFunc K) :
    (ratFuncFractionFieldTensorEquiv hX hX').symm (algebraMap (RatFunc K) Q a) =
      a ⊗ₜ[RatFunc k] 1 :=
  constantExtensionTowerTensorEquiv_symm_algebraMap_left _ _ _ _ a

/-- On `F`, `(ratFuncFractionFieldTensorEquiv hX hX').symm` sends `f` to `1 ⊗ₜ f`. -/
@[simp]
theorem ratFuncFractionFieldTensorEquiv_symm_algebraMap_right
    (hX : algebraMap (RatFunc k) (RatFunc K) RatFunc.X = RatFunc.X)
    (hX' : algebraMap F Q (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc K) Q RatFunc.X)
    (f : F) :
    (ratFuncFractionFieldTensorEquiv hX hX').symm (algebraMap F Q f) = 1 ⊗ₜ[RatFunc k] f :=
  constantExtensionTowerTensorEquiv_symm_algebraMap_right _ _ _ _ f

end Presentation

section FieldCriterion

variable {k K F : Type*} [Field k] [Field K] [Field F]
  [Algebra k K] [Algebra k F] [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
  [Algebra.IsAlgebraic (RatFunc k) F]
  [Algebra (RatFunc k) (RatFunc K)] [IsScalarTower k (RatFunc k) (RatFunc K)]

/-- **If `F ⊗[k] K` is a domain and `F` is algebraic over `RatFunc k`, then
`RatFunc K ⊗[RatFunc k] F` is a field**, even when `K/k` is transcendental. -/
theorem isField_ratFunc_tensorProduct [IsDomain (F ⊗[k] K)]
    (hX : algebraMap (RatFunc k) (RatFunc K) RatFunc.X = RatFunc.X) :
    IsField (RatFunc K ⊗[RatFunc k] F) := by
  let _ : Algebra (RatFunc k ⊗[k] K) (RatFunc K) :=
    (Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom k (RatFunc k) (RatFunc K))
      (IsScalarTower.toAlgHom k K (RatFunc K))).toRingHom.toAlgebra
  have : IsScalarTower (RatFunc k) (RatFunc k ⊗[k] K) (RatFunc K) :=
    .of_algebraMap_eq fun _ ↦ by simp [RingHom.algebraMap_toAlgebra]
  have : IsScalarTower K (RatFunc k ⊗[k] K) (RatFunc K) :=
    .of_algebraMap_eq fun _ ↦ by simp [RingHom.algebraMap_toAlgebra]
  have := isFractionRing_ratFunc_tensorProduct hX
  exact isField_tensorProduct_of_isFractionRing_tensorProduct (k := k) (K := K) F (RatFunc K)

/-- Under the hypotheses of `TauCeti.isField_ratFunc_tensorProduct`, `RatFunc K ⊗[RatFunc k] F` is
an integral domain. -/
theorem isDomain_ratFunc_tensorProduct [IsDomain (F ⊗[k] K)]
    (hX : algebraMap (RatFunc k) (RatFunc K) RatFunc.X = RatFunc.X) :
    IsDomain (RatFunc K ⊗[RatFunc k] F) :=
  let _ : Field (RatFunc K ⊗[RatFunc k] F) := (isField_ratFunc_tensorProduct (F := F) hX).toField
  inferInstance

/-- If `F/k` is geometrically reduced with exact constants and `F` is algebraic over `RatFunc k`,
then `RatFunc K ⊗[RatFunc k] F` is a field for every field extension `K/k`. -/
theorem isField_ratFunc_tensorProduct_of_isGeometricallyReduced
    (hex : IsIntegrallyClosedIn k F) [Algebra.IsGeometricallyReduced k F]
    (hX : algebraMap (RatFunc k) (RatFunc K) RatFunc.X = RatFunc.X) :
    IsField (RatFunc K ⊗[RatFunc k] F) :=
  have := isDomain_tensorProduct_of_isGeometricallyReduced hex K
  isField_ratFunc_tensorProduct hX

/-- Over an algebraically closed field `k`, `RatFunc K ⊗[RatFunc k] F` is a field for every
algebraic extension `F / RatFunc k` and every field extension `K/k`. -/
theorem isField_ratFunc_tensorProduct_of_isAlgClosed [IsAlgClosed k]
    (hX : algebraMap (RatFunc k) (RatFunc K) RatFunc.X = RatFunc.X) :
    IsField (RatFunc K ⊗[RatFunc k] F) :=
  isField_ratFunc_tensorProduct hX

/-- **`RatFunc K ⊗[RatFunc k] F` is itself a fraction ring of `F ⊗[k] K`** along any compatible
`F ⊗[k] K`-algebra map sending `f ⊗ₜ c` to `algebraMap K (RatFunc K) c ⊗ₜ f`. -/
theorem isFractionRing_of_ratFunc_tensorProduct [IsDomain (F ⊗[k] K)]
    [Algebra (F ⊗[k] K) (RatFunc K ⊗[RatFunc k] F)]
    (hX : algebraMap (RatFunc k) (RatFunc K) RatFunc.X = RatFunc.X)
    (hmap : ∀ (f : F) (c : K),
      algebraMap (F ⊗[k] K) (RatFunc K ⊗[RatFunc k] F) (f ⊗ₜ[k] c) =
        algebraMap K (RatFunc K) c ⊗ₜ[RatFunc k] f) :
    IsFractionRing (F ⊗[k] K) (RatFunc K ⊗[RatFunc k] F) := by
  let Q := FractionRing (F ⊗[k] K)
  let _ : Algebra (RatFunc k ⊗[k] K) (RatFunc K) :=
    (Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom k (RatFunc k) (RatFunc K))
      (IsScalarTower.toAlgHom k K (RatFunc K))).toRingHom.toAlgebra
  have : IsScalarTower (RatFunc k) (RatFunc k ⊗[k] K) (RatFunc K) :=
    .of_algebraMap_eq fun _ ↦ by simp [RingHom.algebraMap_toAlgebra]
  have : IsScalarTower K (RatFunc k ⊗[k] K) (RatFunc K) :=
    .of_algebraMap_eq fun _ ↦ by simp [RingHom.algebraMap_toAlgebra]
  have := isFractionRing_ratFunc_tensorProduct hX
  let j : RatFunc K →ₐ[K] Q :=
    (IsScalarTower.toAlgHom k (RatFunc k) F).fractionRingTensorMap
      (IsScalarTower.toAlgHom k (RatFunc k) F).injective K (RatFunc K) Q
  let _ : Algebra (RatFunc K) Q := j.toRingHom.toAlgebra
  have : IsScalarTower K (RatFunc K) Q := .of_algebraMap_eq fun c ↦ (j.commutes c).symm
  have hX' : algebraMap F Q (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc K) Q RatFunc.X := by
    calc
      algebraMap F Q (algebraMap (RatFunc k) F RatFunc.X)
        = j (algebraMap (RatFunc k) (RatFunc K) RatFunc.X) :=
          ((IsScalarTower.toAlgHom k (RatFunc k) F).fractionRingTensorMap_algebraMap_left
            (IsScalarTower.toAlgHom k (RatFunc k) F).injective K (RatFunc K) Q RatFunc.X).symm
      _ = j RatFunc.X := congrArg j hX
  let e := (ratFuncFractionFieldTensorEquiv (Q := Q) hX hX').symm
  exact _root_.IsFractionRing.of_algEquiv <|
    AlgEquiv.ofRingEquiv (f := e.toRingEquiv) fun x ↦ by
      rw [AlgEquiv.coe_toRingEquiv]
      induction x with
      | tmul f c =>
        have htmul : (f ⊗ₜ[k] c : F ⊗[k] K) =
            algebraMap F (F ⊗[k] K) f * algebraMap K (F ⊗[k] K) c := by
          simp [Algebra.TensorProduct.algebraMap_apply,
            Algebra.TensorProduct.right_algebraMap_apply]
        rw [htmul, map_mul, map_mul, map_mul,
          ← IsScalarTower.algebraMap_apply F (F ⊗[k] K) Q,
          ← IsScalarTower.algebraMap_apply K (F ⊗[k] K) Q,
          IsScalarTower.algebraMap_apply K (RatFunc K) Q,
          ratFuncFractionFieldTensorEquiv_symm_algebraMap_right hX hX' f,
          ratFuncFractionFieldTensorEquiv_symm_algebraMap_left hX hX'
            (algebraMap K (RatFunc K) c),
          ← map_mul, ← htmul, hmap f c, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      | add x y hx hy =>
        rw [map_add, map_add, map_add, hx, hy]

end FieldCriterion

section Morphism

variable {k K F₁ F₂ Q₁ Q₂ : Type*}
  [Field k] [Field K] [Field F₁] [Field F₂] [Field Q₁] [Field Q₂]
  [Algebra k K] [Algebra k F₁] [Algebra k F₂]
  [Algebra (RatFunc k) F₁] [Algebra (RatFunc k) F₂]
  [IsScalarTower k (RatFunc k) F₁] [IsScalarTower k (RatFunc k) F₂]
  [Algebra (RatFunc k) (RatFunc K)] [IsScalarTower k (RatFunc k) (RatFunc K)]
  [Algebra (F₁ ⊗[k] K) Q₁] [Algebra k Q₁] [Algebra F₁ Q₁] [Algebra K Q₁]
  [IsScalarTower k (F₁ ⊗[k] K) Q₁] [IsScalarTower F₁ (F₁ ⊗[k] K) Q₁]
  [IsScalarTower K (F₁ ⊗[k] K) Q₁] [IsScalarTower k F₁ Q₁] [IsScalarTower k K Q₁]
  [IsFractionRing (F₁ ⊗[k] K) Q₁]
  [Algebra (F₂ ⊗[k] K) Q₂] [Algebra k Q₂] [Algebra F₂ Q₂] [Algebra K Q₂]
  [IsScalarTower k (F₂ ⊗[k] K) Q₂] [IsScalarTower F₂ (F₂ ⊗[k] K) Q₂]
  [IsScalarTower K (F₂ ⊗[k] K) Q₂] [IsScalarTower k F₂ Q₂] [IsScalarTower k K Q₂]
  [IsFractionRing (F₂ ⊗[k] K) Q₂]
  [Algebra (RatFunc K) Q₁] [Algebra (RatFunc K) Q₂]
  [IsScalarTower K (RatFunc K) Q₁] [IsScalarTower K (RatFunc K) Q₂]

omit [IsScalarTower k (F₁ ⊗[k] K) Q₁] [IsScalarTower k (F₂ ⊗[k] K) Q₂] in
/-- For a `RatFunc k`-algebra map `g : F₁ →ₐ[RatFunc k] F₂`, the induced `K`-algebra map
`Q₁ →ₐ[K] Q₂` on specified fraction fields automatically fixes `RatFunc K`. -/
theorem fractionRingTensorMap_algebraMap_ratFunc
    (hX : algebraMap (RatFunc k) (RatFunc K) RatFunc.X = RatFunc.X)
    (hX₁ : algebraMap F₁ Q₁ (algebraMap (RatFunc k) F₁ RatFunc.X) =
      algebraMap (RatFunc K) Q₁ RatFunc.X)
    (hX₂ : algebraMap F₂ Q₂ (algebraMap (RatFunc k) F₂ RatFunc.X) =
      algebraMap (RatFunc K) Q₂ RatFunc.X)
    (g : F₁ →ₐ[RatFunc k] F₂) (a : RatFunc K) :
    (g.restrictScalars k).fractionRingTensorMap (g.restrictScalars k).injective K Q₁ Q₂
        (algebraMap (RatFunc K) Q₁ a) =
      algebraMap (RatFunc K) Q₂ a := by
  let _ : Algebra (RatFunc k ⊗[k] K) (RatFunc K) :=
    (Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom k (RatFunc k) (RatFunc K))
      (IsScalarTower.toAlgHom k K (RatFunc K))).toRingHom.toAlgebra
  have : IsScalarTower (RatFunc k) (RatFunc k ⊗[k] K) (RatFunc K) :=
    .of_algebraMap_eq fun _ ↦ by simp [RingHom.algebraMap_toAlgebra]
  have : IsScalarTower K (RatFunc k ⊗[k] K) (RatFunc K) :=
    .of_algebraMap_eq fun _ ↦ by simp [RingHom.algebraMap_toAlgebra]
  have := isFractionRing_ratFunc_tensorProduct hX
  exact fractionRingTensorMap_algebraMap_tower
    (algebraMap_ratFunc_apply_eq hX hX₁) (algebraMap_ratFunc_apply_eq hX hX₂) g a

omit [IsScalarTower k (F₁ ⊗[k] K) Q₁] [IsScalarTower k (F₂ ⊗[k] K) Q₂] in
/-- Canonical `RatFunc K`-algebra map `Q₁ →ₐ[RatFunc K] Q₂` induced on specified fraction fields by
a `RatFunc k`-algebra homomorphism `g : F₁ →ₐ[RatFunc k] F₂`. -/
noncomputable def ratFuncFractionRingAlgHom
    (hX : algebraMap (RatFunc k) (RatFunc K) RatFunc.X = RatFunc.X)
    (hX₁ : algebraMap F₁ Q₁ (algebraMap (RatFunc k) F₁ RatFunc.X) =
      algebraMap (RatFunc K) Q₁ RatFunc.X)
    (hX₂ : algebraMap F₂ Q₂ (algebraMap (RatFunc k) F₂ RatFunc.X) =
      algebraMap (RatFunc K) Q₂ RatFunc.X)
    (g : F₁ →ₐ[RatFunc k] F₂) : Q₁ →ₐ[RatFunc K] Q₂ :=
  { (g.restrictScalars k).fractionRingTensorMap (g.restrictScalars k).injective K Q₁ Q₂ with
    commutes' := fractionRingTensorMap_algebraMap_ratFunc hX hX₁ hX₂ g }

omit [IsScalarTower k (F₁ ⊗[k] K) Q₁] [IsScalarTower k (F₂ ⊗[k] K) Q₂] in
/-- On `F₁`, `TauCeti.ratFuncFractionRingAlgHom` agrees with `g`. -/
@[simp]
theorem ratFuncFractionRingAlgHom_algebraMap_left
    (hX : algebraMap (RatFunc k) (RatFunc K) RatFunc.X = RatFunc.X)
    (hX₁ : algebraMap F₁ Q₁ (algebraMap (RatFunc k) F₁ RatFunc.X) =
      algebraMap (RatFunc K) Q₁ RatFunc.X)
    (hX₂ : algebraMap F₂ Q₂ (algebraMap (RatFunc k) F₂ RatFunc.X) =
      algebraMap (RatFunc K) Q₂ RatFunc.X)
    (g : F₁ →ₐ[RatFunc k] F₂) (f : F₁) :
    ratFuncFractionRingAlgHom hX hX₁ hX₂ g (algebraMap F₁ Q₁ f) = algebraMap F₂ Q₂ (g f) :=
  (g.restrictScalars k).fractionRingTensorMap_algebraMap_left
    (g.restrictScalars k).injective K Q₁ Q₂ f

/-- **Naturality of `ratFuncFractionFieldTensorEquiv`.** Under the tensor presentations
`RatFunc K ⊗[RatFunc k] F₁ ≃ₐ[RatFunc K] Q₁` and `RatFunc K ⊗[RatFunc k] F₂ ≃ₐ[RatFunc K] Q₂`, the
map induced on fraction fields by `g : F₁ →ₐ[RatFunc k] F₂` is `id ⊗ g`. -/
theorem fractionRingTensorMap_ratFuncFractionFieldTensorEquiv
    [Algebra.IsAlgebraic (RatFunc k) F₁] [Algebra.IsAlgebraic (RatFunc k) F₂]
    (hX : algebraMap (RatFunc k) (RatFunc K) RatFunc.X = RatFunc.X)
    (hX₁ : algebraMap F₁ Q₁ (algebraMap (RatFunc k) F₁ RatFunc.X) =
      algebraMap (RatFunc K) Q₁ RatFunc.X)
    (hX₂ : algebraMap F₂ Q₂ (algebraMap (RatFunc k) F₂ RatFunc.X) =
      algebraMap (RatFunc K) Q₂ RatFunc.X)
    (g : F₁ →ₐ[RatFunc k] F₂) (x : RatFunc K ⊗[RatFunc k] F₁) :
    (g.restrictScalars k).fractionRingTensorMap (g.restrictScalars k).injective K Q₁ Q₂
        (ratFuncFractionFieldTensorEquiv hX hX₁ x) =
      ratFuncFractionFieldTensorEquiv hX hX₂
        (Algebra.TensorProduct.map (AlgHom.id (RatFunc K) (RatFunc K)) g x) := by
  induction x with
  | tmul a f =>
    rw [ratFuncFractionFieldTensorEquiv_tmul, map_mul,
      fractionRingTensorMap_algebraMap_ratFunc hX hX₁ hX₂ g a,
      (g.restrictScalars k).fractionRingTensorMap_algebraMap_left
        (g.restrictScalars k).injective K Q₁ Q₂ f]
    simp
  | add x y hx hy =>
    rw [map_add, map_add, map_add, map_add, hx, hy]

end Morphism

end RatFunc

end TauCeti

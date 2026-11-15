/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.ConstantExtension.FractionField
public import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.Algebra.Field.Equiv
import TauCeti.FieldTheory.IntermediateField.Adjoin.Basic
import TauCeti.FieldTheory.RatFunc.Automorphism
import TauCeti.FieldTheory.RatFunc.Transcendental

/-!
# Tensor presentations over an extended parameter field

Let `F' = F · K` be a linearly disjoint extension of constants of `F/k`, and let `C` be
an intermediate field with `F/C` algebraic. Multiplication identifies
`(C · K) ⊗[C] F` with `F'`, as algebras over `C · K`. In particular, when `F` is an
algebraic extension of `RatFunc k` over `k` and `RatFunc.X` acts compatibly on `F` and
`F'`, basis transport gives `RatFunc K ⊗[RatFunc k] F ≃ₐ[RatFunc K] F'` together with
preservation of `[F : k(X)]` and separability over `k(X)`.
The extension `K/k` can be transcendental. The original extension `F/C` need only
be algebraic, and need not be separable or finite.

The same construction applies to any specified fraction field `F'` of a domain tensor
product `F ⊗[k] K`. In particular, when `F` is algebraic over `RatFunc k` and
`F ⊗[k] K` is a domain (for instance when `F/k` is geometrically reduced with exact
constants), `RatFunc K ⊗[RatFunc k] F` is itself a field, and `F'` is canonically
isomorphic as a `K`-algebra to `RatFunc K ⊗[RatFunc k] F` via
`TauCeti.fractionFieldEquivRatFuncTensor`, without assuming that `F ⊗[k] K` is a field.

The construction uses `constantExtensionBasisOfLinearDisjoint` for basis transport
and Mathlib's `Module.Basis.baseChange` and `AlgHom.liftEquiv` for the tensor algebra.

## Main definitions and results

* `TauCeti.constantExtensionTensorEquiv`, `IntermediateField.fractionFieldParameterEquiv`:
  the `(C · K)`-algebra isomorphism `(C · K) ⊗[C] F ≃ₐ[C · K] F'` for an intermediate
  field `C` with `F/C` algebraic.
* `TauCeti.ratFuncConstantExtensionBasis`, `TauCeti.finrank_ratFunc_eq_of_linearDisjoint`,
  `TauCeti.isSeparable_ratFunc_of_constantCompositum_eq_top`: basis transport, degree
  equality `[F' : K(X)] = [F : k(X)]`, and separability preservation over `RatFunc` for
  arbitrary constant extensions.
* `TauCeti.ratFuncConstantExtensionTensorEquiv`, `TauCeti.ratFuncFractionFieldEquiv`:
  the `RatFunc K`-algebra isomorphism `RatFunc K ⊗[RatFunc k] F ≃ₐ[RatFunc K] F'`.
* `TauCeti.isField_ratFunc_tensorProduct_of_isDomain_tensorProduct`,
  `TauCeti.isDomain_ratFunc_tensorProduct_of_isDomain_tensorProduct`,
  `TauCeti.isField_ratFunc_tensorProduct_of_isGeometricallyReduced`: when `F ⊗[k] K` is
  a domain, `RatFunc K ⊗[RatFunc k] F` is a field (and in particular a domain).
* `TauCeti.fractionFieldEquivRatFuncTensor`: the canonical `K`-algebra equivalence
  `F' ≃ₐ[K] RatFunc K ⊗[RatFunc k] F` for any fraction field `F'` of `F ⊗[k] K`, with
  explicit formulas on pure tensors and rational functions in both directions.

## References

* S. Lang, *Algebra*, the theory of linearly disjoint field extensions.
* S. Lang, *Introduction to Algebraic Geometry*, Chapter III, Section 1.
* H. Stichtenoth, *Algebraic Function Fields and Codes*, second edition, Section III.6.
-/

public section

open scoped TensorProduct IntermediateField Polynomial

namespace TauCeti

variable {k K F F' : Type*} [Field k] [Field K] [Field F] [Field F']
  [Algebra k K] [Algebra k F] [Algebra k F'] [Algebra K F'] [Algebra F F']
  [IsScalarTower k K F'] [IsScalarTower k F F']

/-- A basis transported to the compositum, with scalars viewed as an extension of `C`. -/
private noncomputable def parameterBasis
    (H : (IsScalarTower.toAlgHom k K F').fieldRange.LinearDisjoint F)
    (h : constantCompositum F K F' = ⊤) (C : IntermediateField k F)
    [Algebra.IsAlgebraic C F] {ι : Type*} (b : Module.Basis ι C F) :
    Module.Basis ι (constantCompositum C K F') F' :=
  (constantExtensionBasisOfLinearDisjoint H h C b).mapCoeffs
    (RingEquiv.subfieldCongr (_root_.IntermediateField.constantCompositum_toSubfield C).symm)
    (fun _ _ ↦ rfl)

/-- Multiplication over the enlarged intermediate field is bijective. -/
private theorem bijective_parameterLift
    (H : (IsScalarTower.toAlgHom k K F').fieldRange.LinearDisjoint F)
    (h : constantCompositum F K F' = ⊤) (C : IntermediateField k F)
    [Algebra.IsAlgebraic C F] :
    Function.Bijective
      (AlgHom.liftEquiv C (constantCompositum C K F') F F'
        (IsScalarTower.toAlgHom C F F')) := by
  let b := Module.Basis.ofVectorSpace C F
  let b' := parameterBasis H h C b
  let e := (b.baseChange (constantCompositum C K F')).equiv b' (Equiv.refl _)
  have he : (AlgHom.liftEquiv C (constantCompositum C K F') F F'
      (IsScalarTower.toAlgHom C F F')).toLinearMap = e.toLinearMap := by
    apply (b.baseChange (constantCompositum C K F')).ext
    intro i
    calc
      _ = algebraMap F F' (b i) := by simp
      _ = b' i := by
        exact ((constantExtensionBasisOfLinearDisjoint H h C b).mapCoeffs_apply
          (RingEquiv.subfieldCongr (_root_.IntermediateField.constantCompositum_toSubfield C).symm)
          (fun _ _ ↦ rfl) i |>.trans
            (constantExtensionBasisOfLinearDisjoint_apply H h C b i)).symm
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

section FractionField

attribute [local instance] Algebra.TensorProduct.rightAlgebra
  Algebra.TensorProduct.right_isScalarTower

variable [Algebra (F ⊗[k] K) F']
  [IsScalarTower k (F ⊗[k] K) F'] [IsScalarTower F (F ⊗[k] K) F']
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
    (by
      rw [constantCompositum_def]
      exact adjoin_range_right_eq_top_of_isFractionRing_tensorProduct (k := k)) C

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

section RatFunc

variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]

/-- Under a linearly disjoint extension of constants, the image of the rational-function
variable `RatFunc.X` remains transcendental over the enlarged constant field `K`. -/
theorem transcendental_algebraMap_X_of_linearDisjoint
    (H : (IsScalarTower.toAlgHom k K F').fieldRange.LinearDisjoint F) :
    Transcendental K (algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X)) :=
  H.transcendental_algebraMap <|
    (transcendental_algebraMap_iff
      (FaithfulSMul.algebraMap_injective (RatFunc k) F)).mpr RatFunc.transcendental_X

omit [Algebra k K] [Algebra k F'] [Algebra K F'] [Algebra F F']
    [IsScalarTower k K F'] [IsScalarTower k F F'] in
private theorem isAlgebraic_adjoin_algebraMap_X [Algebra.IsAlgebraic (RatFunc k) F] :
    Algebra.IsAlgebraic k⟮algebraMap (RatFunc k) F RatFunc.X⟯ F := by
  have hx : Transcendental k (algebraMap (RatFunc k) F RatFunc.X) :=
    (transcendental_algebraMap_iff
      (FaithfulSMul.algebraMap_injective (RatFunc k) F)).mpr RatFunc.transcendental_X
  exact (Algebra.isAlgebraic_ringHom_iff_of_comp_eq
    (RatFunc.algEquivOfTranscendental _ hx).toRingEquiv (RingEquiv.refl F)
    (RingHom.ext coe_algEquivOfTranscendental_algebraMap_X_apply)).mpr inferInstance

section WithRatFuncTarget

variable [Algebra (RatFunc K) F'] [IsScalarTower K (RatFunc K) F']

/-- If `RatFunc k → RatFunc K` fixes `RatFunc.X` and `RatFunc.X` acts on `F'` as the image of
its action on `F`, then the two composite maps `RatFunc k → F'` through `RatFunc K` and through
`F` agree. -/
theorem algebraMap_ratFunc_eq_algebraMap
    [Algebra (RatFunc k) (RatFunc K)] [IsScalarTower k (RatFunc k) (RatFunc K)]
    (hX : algebraMap (RatFunc k) (RatFunc K) RatFunc.X = RatFunc.X)
    (hXF' : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc K) F' RatFunc.X)
    (r : RatFunc k) :
    algebraMap (RatFunc K) F' (algebraMap (RatFunc k) (RatFunc K) r) =
      algebraMap F F' (algebraMap (RatFunc k) F r) := by
  have : IsScalarTower k (RatFunc K) F' := .to₁₃₄ k K (RatFunc K) F'
  have h : (IsScalarTower.toAlgHom k (RatFunc K) F').comp
        (IsScalarTower.toAlgHom k (RatFunc k) (RatFunc K)) =
      (IsScalarTower.toAlgHom k F F').comp (IsScalarTower.toAlgHom k (RatFunc k) F) :=
    RatFunc.algHom_ext (by simp [hX, hXF'])
  exact DFunLike.congr_fun h r

/-- Extending constants to `F' = F · K` preserves separability over the rational function field
when `RatFunc.X` acts compatibly on `F` and `F'`. Neither algebraicity nor separability of
`K/k` is required. -/
theorem isSeparable_ratFunc_of_constantCompositum_eq_top [Algebra.IsSeparable (RatFunc k) F]
    (h : constantCompositum F K F' = ⊤)
    (hXF' : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc K) F' RatFunc.X) :
    Algebra.IsSeparable (RatFunc K) F' := by
  have : Algebra.IsSeparable k⟮algebraMap (RatFunc k) F RatFunc.X⟯ F :=
    isSeparable_adjoin_algebraMap_X_iff.mpr inferInstance
  have hsep := isSeparable_adjoin_image_of_constantCompositum_eq_top (k := k)
    (S := {algebraMap (RatFunc k) F RatFunc.X}) h
  rw [Set.image_singleton, hXF'] at hsep
  exact isSeparable_adjoin_algebraMap_X_iff.mp hsep

/-- **Basis transport over `RatFunc` along a linearly disjoint constant extension.**
If `F' = F · K` linearly disjointly over `k`, `F` is algebraic over `RatFunc k`, and
`RatFunc.X` acts compatibly on `F` and `F'`, then any `RatFunc k`-basis of `F` maps to a
`RatFunc K`-basis of `F'`. The constant extension `K/k` may be transcendental. -/
noncomputable def ratFuncConstantExtensionBasis
    (H : (IsScalarTower.toAlgHom k K F').fieldRange.LinearDisjoint F)
    (h : constantCompositum F K F' = ⊤)
    (hXF' : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc K) F' RatFunc.X)
    [Algebra.IsAlgebraic (RatFunc k) F] {ι : Type*} (b : Module.Basis ι (RatFunc k) F) :
    Module.Basis ι (RatFunc K) F' :=
  let hx : Transcendental k (algebraMap (RatFunc k) F RatFunc.X) :=
    (transcendental_algebraMap_iff
      (FaithfulSMul.algebraMap_injective (RatFunc k) F)).mpr RatFunc.transcendental_X
  let hx' : Transcendental K (algebraMap (RatFunc K) F' RatFunc.X) :=
    (transcendental_algebraMap_iff
      (FaithfulSMul.algebraMap_injective (RatFunc K) F')).mpr RatFunc.transcendental_X
  let e₁ := RatFunc.algEquivOfTranscendental _ hx
  let b₁ := b.mapCoeffs e₁.toRingEquiv fun c x ↦ by
    simp [Algebra.smul_def, e₁, coe_algEquivOfTranscendental_algebraMap_X_apply]
  let _ : Algebra.IsAlgebraic k⟮algebraMap (RatFunc k) F RatFunc.X⟯ F :=
    isAlgebraic_adjoin_algebraMap_X
  let hC' : IntermediateField.adjoin K
      (Set.range (algebraMap k⟮algebraMap (RatFunc k) F RatFunc.X⟯ F')) =
      K⟮algebraMap (RatFunc K) F' RatFunc.X⟯ := by
    rw [IntermediateField.range_algebraMap_adjoin_simple,
      IntermediateField.adjoin_adjoin_right, hXF']
  let e₂ := (IntermediateField.equivOfEq hC').trans
    (RatFunc.algEquivOfTranscendental _ hx').symm
  (constantExtensionBasisOfLinearDisjoint H h _ b₁).mapCoeffs e₂.toRingEquiv fun c x ↦ by
    have hc : algebraMap (RatFunc K) F' (e₂ c) = (c : F') := by
      rw [← coe_algEquivOfTranscendental_algebraMap_X_apply (k := K) (F := F') (e₂ c)]
      simp [e₂]
    rw [Algebra.smul_def, Algebra.smul_def, AlgEquiv.coe_toRingEquiv, hc]
    rfl

/-- `ratFuncConstantExtensionBasis` sends each basis vector to its image in `F'`. -/
@[simp]
theorem ratFuncConstantExtensionBasis_apply
    (H : (IsScalarTower.toAlgHom k K F').fieldRange.LinearDisjoint F)
    (h : constantCompositum F K F' = ⊤)
    (hXF' : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc K) F' RatFunc.X)
    [Algebra.IsAlgebraic (RatFunc k) F] {ι : Type*} (b : Module.Basis ι (RatFunc k) F) (i : ι) :
    ratFuncConstantExtensionBasis H h hXF' b i = algebraMap F F' (b i) := by
  simp [ratFuncConstantExtensionBasis]

/-- **A linearly disjoint constant extension preserves the degree over `RatFunc`.**
If `F' = F · K` linearly disjointly over `k`, `F` is algebraic over `RatFunc k`, and
`RatFunc.X` acts compatibly on `F` and `F'`, then `[F' : K(X)] = [F : k(X)]`. The constant
extension `K/k` need not be algebraic or separable. -/
theorem finrank_ratFunc_eq_of_linearDisjoint
    (H : (IsScalarTower.toAlgHom k K F').fieldRange.LinearDisjoint F)
    (h : constantCompositum F K F' = ⊤)
    (hXF' : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc K) F' RatFunc.X)
    [Algebra.IsAlgebraic (RatFunc k) F] :
    Module.finrank (RatFunc K) F' = Module.finrank (RatFunc k) F := by
  let b := Module.Basis.ofVectorSpace (RatFunc k) F
  exact (Module.finrank_eq_nat_card_basis (ratFuncConstantExtensionBasis H h hXF' b)).trans
    (Module.finrank_eq_nat_card_basis b).symm

section TensorEquiv

variable [Algebra (RatFunc k) (RatFunc K)] [IsScalarTower k (RatFunc k) (RatFunc K)]

/-- Multiplication map `RatFunc K ⊗[RatFunc k] F →ₐ[RatFunc K] F'` induced by compatible
`RatFunc`-algebra structures. -/
private noncomputable def ratFuncTensorLift
    (hX : algebraMap (RatFunc k) (RatFunc K) RatFunc.X = RatFunc.X)
    (hXF' : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc K) F' RatFunc.X) :
    RatFunc K ⊗[RatFunc k] F →ₐ[RatFunc K] F' :=
  let : Algebra (RatFunc k) F' :=
    ((algebraMap F F').comp (algebraMap (RatFunc k) F)).toAlgebra
  have : IsScalarTower (RatFunc k) F F' := .of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower (RatFunc k) (RatFunc K) F' :=
    .of_algebraMap_eq fun r ↦ (algebraMap_ratFunc_eq_algebraMap hX hXF' r).symm
  AlgHom.liftEquiv (RatFunc k) (RatFunc K) F F' (IsScalarTower.toAlgHom (RatFunc k) F F')

private theorem ratFuncTensorLift_tmul
    (hX : algebraMap (RatFunc k) (RatFunc K) RatFunc.X = RatFunc.X)
    (hXF' : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc K) F' RatFunc.X)
    (r : RatFunc K) (f : F) :
    ratFuncTensorLift hX hXF' (r ⊗ₜ[RatFunc k] f) =
      algebraMap (RatFunc K) F' r * algebraMap F F' f := by
  let : Algebra (RatFunc k) F' :=
    ((algebraMap F F').comp (algebraMap (RatFunc k) F)).toAlgebra
  have : IsScalarTower (RatFunc k) F F' := .of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower (RatFunc k) (RatFunc K) F' :=
    .of_algebraMap_eq fun s ↦ (algebraMap_ratFunc_eq_algebraMap hX hXF' s).symm
  simp [ratFuncTensorLift, AlgHom.liftEquiv_tmul, Algebra.smul_def]

variable [Algebra.IsAlgebraic (RatFunc k) F]

private theorem bijective_ratFuncTensorLift
    (H : (IsScalarTower.toAlgHom k K F').fieldRange.LinearDisjoint F)
    (h : constantCompositum F K F' = ⊤)
    (hX : algebraMap (RatFunc k) (RatFunc K) RatFunc.X = RatFunc.X)
    (hXF' : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc K) F' RatFunc.X) :
    Function.Bijective (ratFuncTensorLift hX hXF') := by
  let b := Module.Basis.ofVectorSpace (RatFunc k) F
  let b' := ratFuncConstantExtensionBasis H h hXF' b
  let e := (b.baseChange (RatFunc K)).equiv b' (Equiv.refl _)
  have he : (ratFuncTensorLift hX hXF').toLinearMap = e.toLinearMap := by
    apply (b.baseChange (RatFunc K)).ext
    intro i
    calc
      _ = ratFuncTensorLift hX hXF' (1 ⊗ₜ[RatFunc k] b i) := by simp
      _ = algebraMap F F' (b i) := by simp [ratFuncTensorLift_tmul]
      _ = b' i := (ratFuncConstantExtensionBasis_apply H h hXF' b i).symm
      _ = e ((b.baseChange (RatFunc K)) i) :=
        ((b.baseChange (RatFunc K)).equiv_apply i b' (Equiv.refl _)).symm
  have hb : Function.Bijective (ratFuncTensorLift hX hXF').toLinearMap := by
    rw [he]
    exact e.bijective
  exact hb

/-- **Tensor presentation over `RatFunc K` of a linearly disjoint constant extension.**
If `F' = F · K` linearly disjointly over `k`, `F` is algebraic over `RatFunc k`, and
`RatFunc.X` acts compatibly on `RatFunc K` and `F'`, multiplication identifies
`RatFunc K ⊗[RatFunc k] F` with `F'` as `RatFunc K`-algebras. -/
noncomputable def ratFuncConstantExtensionTensorEquiv
    (H : (IsScalarTower.toAlgHom k K F').fieldRange.LinearDisjoint F)
    (h : constantCompositum F K F' = ⊤)
    (hX : algebraMap (RatFunc k) (RatFunc K) RatFunc.X = RatFunc.X)
    (hXF' : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc K) F' RatFunc.X) :
    RatFunc K ⊗[RatFunc k] F ≃ₐ[RatFunc K] F' :=
  AlgEquiv.ofBijective (ratFuncTensorLift hX hXF') (bijective_ratFuncTensorLift H h hX hXF')

/-- `ratFuncConstantExtensionTensorEquiv` evaluates a pure tensor by multiplying in `F'`. -/
@[simp]
theorem ratFuncConstantExtensionTensorEquiv_tmul
    (H : (IsScalarTower.toAlgHom k K F').fieldRange.LinearDisjoint F)
    (h : constantCompositum F K F' = ⊤)
    (hX : algebraMap (RatFunc k) (RatFunc K) RatFunc.X = RatFunc.X)
    (hXF' : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc K) F' RatFunc.X)
    (r : RatFunc K) (f : F) :
    ratFuncConstantExtensionTensorEquiv H h hX hXF' (r ⊗ₜ[RatFunc k] f) =
      algebraMap (RatFunc K) F' r * algebraMap F F' f :=
  ratFuncTensorLift_tmul hX hXF' r f

/-- The inverse of `ratFuncConstantExtensionTensorEquiv` sends products to pure tensors. -/
@[simp]
theorem ratFuncConstantExtensionTensorEquiv_symm_mul
    (H : (IsScalarTower.toAlgHom k K F').fieldRange.LinearDisjoint F)
    (h : constantCompositum F K F' = ⊤)
    (hX : algebraMap (RatFunc k) (RatFunc K) RatFunc.X = RatFunc.X)
    (hXF' : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc K) F' RatFunc.X)
    (r : RatFunc K) (f : F) :
    (ratFuncConstantExtensionTensorEquiv H h hX hXF').symm
        (algebraMap (RatFunc K) F' r * algebraMap F F' f) =
      r ⊗ₜ[RatFunc k] f := by
  apply (ratFuncConstantExtensionTensorEquiv H h hX hXF').injective
  simp

/-- The inverse of `ratFuncConstantExtensionTensorEquiv` sends `algebraMap F F' f` to
`1 ⊗ₜ f`. -/
@[simp]
theorem ratFuncConstantExtensionTensorEquiv_symm_algebraMap
    (H : (IsScalarTower.toAlgHom k K F').fieldRange.LinearDisjoint F)
    (h : constantCompositum F K F' = ⊤)
    (hX : algebraMap (RatFunc k) (RatFunc K) RatFunc.X = RatFunc.X)
    (hXF' : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc K) F' RatFunc.X)
    (f : F) :
    (ratFuncConstantExtensionTensorEquiv H h hX hXF').symm (algebraMap F F' f) =
      1 ⊗ₜ[RatFunc k] f := by
  apply (ratFuncConstantExtensionTensorEquiv H h hX hXF').injective
  simp

end TensorEquiv

end WithRatFuncTarget

section RatFuncFractionField

attribute [local instance] Algebra.TensorProduct.rightAlgebra
  Algebra.TensorProduct.right_isScalarTower

section DomainAndField

omit [Field F'] [Algebra k F'] [Algebra K F'] [Algebra F F']
  [IsScalarTower k K F'] [IsScalarTower k F F']

variable [Algebra (RatFunc k) (RatFunc K)] [IsScalarTower k (RatFunc k) (RatFunc K)]
  [Algebra.IsAlgebraic (RatFunc k) F]

/-- **When `F ⊗[k] K` is a domain and `F` is algebraic over `RatFunc k`, the base-changed
algebra `RatFunc K ⊗[RatFunc k] F` is a field.** -/
theorem isField_ratFunc_tensorProduct_of_isDomain_tensorProduct
    [IsDomain (F ⊗[k] K)]
    (hX : algebraMap (RatFunc k) (RatFunc K) RatFunc.X = RatFunc.X) :
    IsField (RatFunc K ⊗[RatFunc k] F) := by
  let Q := FractionRing (F ⊗[k] K)
  have htop : constantCompositum F K Q = ⊤ := by
    rw [constantCompositum_def]
    exact adjoin_range_right_eq_top_of_isFractionRing_tensorProduct (k := k)
  have hxQ : Transcendental K (algebraMap F Q (algebraMap (RatFunc k) F RatFunc.X)) :=
    transcendental_algebraMap_X_of_linearDisjoint
      (linearDisjoint_of_isFractionRing_tensorProduct (k := k))
  let : Algebra (RatFunc K) Q := ratFuncAlgebraOfTranscendental hxQ
  have : IsScalarTower K (RatFunc K) Q := isScalarTower_ratFuncAlgebraOfTranscendental hxQ
  have hXQ : algebraMap F Q (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc K) Q RatFunc.X :=
    (algebraMap_ratFuncAlgebraOfTranscendental_X hxQ).symm
  exact MulEquiv.isField (Field.toIsField Q)
    (ratFuncConstantExtensionTensorEquiv
      (linearDisjoint_of_isFractionRing_tensorProduct (k := k)) htop hX hXQ).toMulEquiv

/-- When `F ⊗[k] K` is a domain and `F` is algebraic over `RatFunc k`, the tensor product
`RatFunc K ⊗[RatFunc k] F` is an integral domain. -/
theorem isDomain_ratFunc_tensorProduct_of_isDomain_tensorProduct
    [IsDomain (F ⊗[k] K)]
    (hX : algebraMap (RatFunc k) (RatFunc K) RatFunc.X = RatFunc.X) :
    IsDomain (RatFunc K ⊗[RatFunc k] F) :=
  (isField_ratFunc_tensorProduct_of_isDomain_tensorProduct hX).isDomain

/-- For a geometrically reduced extension `F/k` with exact constants that is algebraic over
`RatFunc k`, the base-changed algebra `RatFunc K ⊗[RatFunc k] F` is a field for every field
extension `K/k`. -/
theorem isField_ratFunc_tensorProduct_of_isGeometricallyReduced
    (hex : IsIntegrallyClosedIn k F) [Algebra.IsGeometricallyReduced k F]
    (hX : algebraMap (RatFunc k) (RatFunc K) RatFunc.X = RatFunc.X) :
    IsField (RatFunc K ⊗[RatFunc k] F) := by
  have := isDomain_tensorProduct_of_isGeometricallyReduced hex K
  exact isField_ratFunc_tensorProduct_of_isDomain_tensorProduct hX

end DomainAndField

variable [Algebra (F ⊗[k] K) F']
  [IsScalarTower k (F ⊗[k] K) F'] [IsScalarTower F (F ⊗[k] K) F']
  [IsScalarTower K (F ⊗[k] K) F'] [IsFractionRing (F ⊗[k] K) F']

/-- In any fraction field `F'` of `F ⊗[k] K`, the image of `RatFunc.X` from `F` is
transcendental over `K`. -/
theorem transcendental_algebraMap_X_of_isFractionRing_tensorProduct :
    Transcendental K (algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X)) :=
  transcendental_algebraMap_X_of_linearDisjoint
    (linearDisjoint_of_isFractionRing_tensorProduct (k := k))

section WithRatFuncOnFractionField

variable [Algebra (RatFunc K) F'] [IsScalarTower K (RatFunc K) F']

omit [IsScalarTower k (F ⊗[k] K) F'] in
/-- If `F` is finite over `RatFunc k`, then any fraction field `F'` of `F ⊗[k] K` with a
compatible `RatFunc K`-algebra structure is finite over `RatFunc K`. -/
theorem finiteDimensional_ratFunc_of_isFractionRing_tensorProduct
    [FiniteDimensional (RatFunc k) F]
    (hXF' : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc K) F' RatFunc.X) :
    FiniteDimensional (RatFunc K) F' :=
  finiteDimensional_ratFunc_of_constantCompositum_eq_top (k := k)
    (by
      rw [constantCompositum_def]
      exact adjoin_range_right_eq_top_of_isFractionRing_tensorProduct (k := k))
    hXF'

omit [IsScalarTower k (F ⊗[k] K) F'] in
/-- If `F` is separable over `RatFunc k`, then any fraction field `F'` of `F ⊗[k] K` with a
compatible `RatFunc K`-algebra structure is separable over `RatFunc K`. -/
theorem isSeparable_ratFunc_of_isFractionRing_tensorProduct
    [Algebra.IsSeparable (RatFunc k) F]
    (hXF' : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc K) F' RatFunc.X) :
    Algebra.IsSeparable (RatFunc K) F' :=
  isSeparable_ratFunc_of_constantCompositum_eq_top (k := k)
    (by
      rw [constantCompositum_def]
      exact adjoin_range_right_eq_top_of_isFractionRing_tensorProduct (k := k))
    hXF'

/-- Tensor-fraction-field extension of constants preserves the degree over `RatFunc`:
`[F' : K(X)] = [F : k(X)]`. Neither `K/k` nor `F/k(X)` need be separable. -/
theorem finrank_ratFunc_eq_of_isFractionRing_tensorProduct
    [Algebra.IsAlgebraic (RatFunc k) F]
    (hXF' : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc K) F' RatFunc.X) :
    Module.finrank (RatFunc K) F' = Module.finrank (RatFunc k) F :=
  finrank_ratFunc_eq_of_linearDisjoint
    (linearDisjoint_of_isFractionRing_tensorProduct (k := k))
    (by
      rw [constantCompositum_def]
      exact adjoin_range_right_eq_top_of_isFractionRing_tensorProduct (k := k))
    hXF'

section Equiv

variable [Algebra (RatFunc k) (RatFunc K)] [IsScalarTower k (RatFunc k) (RatFunc K)]
  [Algebra.IsAlgebraic (RatFunc k) F]

/-- **The `RatFunc K`-algebra isomorphism `RatFunc K ⊗[RatFunc k] F ≃ₐ[RatFunc K] F'`** for
any fraction field `F'` of `F ⊗[k] K` equipped with a compatible `RatFunc K`-algebra
structure. -/
noncomputable def ratFuncFractionFieldEquiv
    (hX : algebraMap (RatFunc k) (RatFunc K) RatFunc.X = RatFunc.X)
    (hXF' : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc K) F' RatFunc.X) :
    RatFunc K ⊗[RatFunc k] F ≃ₐ[RatFunc K] F' :=
  ratFuncConstantExtensionTensorEquiv
    (linearDisjoint_of_isFractionRing_tensorProduct (k := k))
    (by
      rw [constantCompositum_def]
      exact adjoin_range_right_eq_top_of_isFractionRing_tensorProduct (k := k))
    hX hXF'

@[simp]
theorem ratFuncFractionFieldEquiv_tmul
    (hX : algebraMap (RatFunc k) (RatFunc K) RatFunc.X = RatFunc.X)
    (hXF' : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc K) F' RatFunc.X)
    (r : RatFunc K) (f : F) :
    ratFuncFractionFieldEquiv hX hXF' (r ⊗ₜ[RatFunc k] f) =
      algebraMap (RatFunc K) F' r * algebraMap F F' f :=
  ratFuncConstantExtensionTensorEquiv_tmul _ _ hX hXF' r f

@[simp]
theorem ratFuncFractionFieldEquiv_symm_mul
    (hX : algebraMap (RatFunc k) (RatFunc K) RatFunc.X = RatFunc.X)
    (hXF' : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc K) F' RatFunc.X)
    (r : RatFunc K) (f : F) :
    (ratFuncFractionFieldEquiv hX hXF').symm
        (algebraMap (RatFunc K) F' r * algebraMap F F' f) =
      r ⊗ₜ[RatFunc k] f :=
  ratFuncConstantExtensionTensorEquiv_symm_mul _ _ hX hXF' r f

@[simp]
theorem ratFuncFractionFieldEquiv_symm_algebraMap
    (hX : algebraMap (RatFunc k) (RatFunc K) RatFunc.X = RatFunc.X)
    (hXF' : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc K) F' RatFunc.X)
    (f : F) :
    (ratFuncFractionFieldEquiv hX hXF').symm (algebraMap F F' f) = 1 ⊗ₜ[RatFunc k] f :=
  ratFuncConstantExtensionTensorEquiv_symm_algebraMap _ _ hX hXF' f

end Equiv

end WithRatFuncOnFractionField

section CanonicalEquiv

variable [Algebra (RatFunc k) (RatFunc K)] [IsScalarTower k (RatFunc k) (RatFunc K)]
  [Algebra.IsAlgebraic (RatFunc k) F]

variable (F F') in
/-- **Canonical `K`-algebra equivalence `F' ≃ₐ[K] RatFunc K ⊗[RatFunc k] F`** for any fraction
field `F'` of `F ⊗[k] K` when `F` is algebraic over `RatFunc k`. No prior `RatFunc K`-algebra
structure on `F'` is needed: `RatFunc.X` acts on `F'` as the image of `RatFunc.X` from `F`,
localizing pure tensors at nonzero polynomials in the parameter. -/
noncomputable def fractionFieldEquivRatFuncTensor
    (hX : algebraMap (RatFunc k) (RatFunc K) RatFunc.X = RatFunc.X) :
    F' ≃ₐ[K] RatFunc K ⊗[RatFunc k] F :=
  let hx' : Transcendental K (algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X)) :=
    transcendental_algebraMap_X_of_isFractionRing_tensorProduct (k := k)
  let : Algebra (RatFunc K) F' := ratFuncAlgebraOfTranscendental hx'
  have : IsScalarTower K (RatFunc K) F' := isScalarTower_ratFuncAlgebraOfTranscendental hx'
  have : IsScalarTower K (RatFunc K) (RatFunc K ⊗[RatFunc k] F) := .of_algebraMap_eq fun _ ↦ rfl
  have hXF' : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc K) F' RatFunc.X :=
    (algebraMap_ratFuncAlgebraOfTranscendental_X hx').symm
  ((ratFuncFractionFieldEquiv (k := k) hX hXF').restrictScalars K).symm

/-- On a polynomial in `K[X]` tensored with `f ∈ F`, the inverse of
`fractionFieldEquivRatFuncTensor` evaluates the polynomial at the image of `RatFunc.X` in `F'`
and multiplies by `algebraMap F F' f`. -/
@[simp]
theorem fractionFieldEquivRatFuncTensor_symm_algebraMap_polynomial_tmul
    (hX : algebraMap (RatFunc k) (RatFunc K) RatFunc.X = RatFunc.X) (p : K[X]) (f : F) :
    (fractionFieldEquivRatFuncTensor F F' hX).symm
        (algebraMap K[X] (RatFunc K) p ⊗ₜ[RatFunc k] f) =
      Polynomial.aeval (algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X)) p *
        algebraMap F F' f := by
  let hx' : Transcendental K (algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X)) :=
    transcendental_algebraMap_X_of_isFractionRing_tensorProduct (k := k)
  let : Algebra (RatFunc K) F' := ratFuncAlgebraOfTranscendental hx'
  have : IsScalarTower K (RatFunc K) F' := isScalarTower_ratFuncAlgebraOfTranscendental hx'
  have hp : algebraMap (RatFunc K) F' (algebraMap K[X] (RatFunc K) p) =
      Polynomial.aeval (algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X)) p := by
    rw [← RatFunc.aeval_X_left_eq_algebraMap, ← IsScalarTower.coe_toAlgHom' K (RatFunc K) F',
      ← Polynomial.aeval_algHom_apply, IsScalarTower.coe_toAlgHom',
      algebraMap_ratFuncAlgebraOfTranscendental_X]
  change ratFuncFractionFieldEquiv (k := k) hX _
      (algebraMap K[X] (RatFunc K) p ⊗ₜ[RatFunc k] f) = _
  rw [ratFuncFractionFieldEquiv_tmul, hp]

@[simp]
theorem fractionFieldEquivRatFuncTensor_symm_one_tmul
    (hX : algebraMap (RatFunc k) (RatFunc K) RatFunc.X = RatFunc.X) (f : F) :
    (fractionFieldEquivRatFuncTensor F F' hX).symm (1 ⊗ₜ[RatFunc k] f) =
      algebraMap F F' f := by
  rw [← map_one (algebraMap K[X] (RatFunc K)),
    fractionFieldEquivRatFuncTensor_symm_algebraMap_polynomial_tmul, map_one, one_mul]

/-- On a fraction of polynomials in `K[X]` tensored with `f ∈ F`, the inverse of
`fractionFieldEquivRatFuncTensor` evaluates numerator and denominator at the parameter in
`F'`. -/
theorem fractionFieldEquivRatFuncTensor_symm_div_algebraMap_polynomial_tmul
    (hX : algebraMap (RatFunc k) (RatFunc K) RatFunc.X = RatFunc.X) (p q : K[X]) (f : F) :
    (fractionFieldEquivRatFuncTensor F F' hX).symm
        ((algebraMap K[X] (RatFunc K) p / algebraMap K[X] (RatFunc K) q) ⊗ₜ[RatFunc k] f) =
      (Polynomial.aeval (algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X)) p /
        Polynomial.aeval (algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X)) q) *
        algebraMap F F' f := by
  let φ : RatFunc K →+* F' :=
    (fractionFieldEquivRatFuncTensor F F' hX).symm.toRingHom.comp
      Algebra.TensorProduct.includeLeftRingHom
  have hmul (r : RatFunc K) :
      (fractionFieldEquivRatFuncTensor F F' hX).symm (r ⊗ₜ[RatFunc k] f) =
        φ r * (fractionFieldEquivRatFuncTensor F F' hX).symm (1 ⊗ₜ[RatFunc k] f) := by
    change (fractionFieldEquivRatFuncTensor F F' hX).symm (r ⊗ₜ[RatFunc k] f) =
      (fractionFieldEquivRatFuncTensor F F' hX).symm (r ⊗ₜ[RatFunc k] 1) *
        (fractionFieldEquivRatFuncTensor F F' hX).symm (1 ⊗ₜ[RatFunc k] f)
    rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  have hφ (g : K[X]) :
      φ (algebraMap K[X] (RatFunc K) g) =
        Polynomial.aeval (algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X)) g := by
    simp [φ]
  rw [hmul, fractionFieldEquivRatFuncTensor_symm_one_tmul, map_div₀ φ, hφ, hφ]

@[simp]
theorem fractionFieldEquivRatFuncTensor_symm_X_tmul
    (hX : algebraMap (RatFunc k) (RatFunc K) RatFunc.X = RatFunc.X) (f : F) :
    (fractionFieldEquivRatFuncTensor F F' hX).symm (RatFunc.X ⊗ₜ[RatFunc k] f) =
      algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X * f) := by
  rw [← RatFunc.algebraMap_X, fractionFieldEquivRatFuncTensor_symm_algebraMap_polynomial_tmul,
    Polynomial.aeval_X, ← map_mul]

/-- `fractionFieldEquivRatFuncTensor` sends an element from `F` to `1 ⊗ₜ f`. -/
@[simp]
theorem fractionFieldEquivRatFuncTensor_algebraMap_left
    (hX : algebraMap (RatFunc k) (RatFunc K) RatFunc.X = RatFunc.X) (f : F) :
    fractionFieldEquivRatFuncTensor F F' hX (algebraMap F F' f) = 1 ⊗ₜ[RatFunc k] f := by
  apply (fractionFieldEquivRatFuncTensor F F' hX).symm.injective
  simp

/-- `fractionFieldEquivRatFuncTensor` sends a constant `c ∈ K` to
`algebraMap K (RatFunc K) c ⊗ₜ 1`. -/
theorem fractionFieldEquivRatFuncTensor_algebraMap_right
    (hX : algebraMap (RatFunc k) (RatFunc K) RatFunc.X = RatFunc.X) (c : K) :
    fractionFieldEquivRatFuncTensor F F' hX (algebraMap K F' c) =
      algebraMap K (RatFunc K) c ⊗ₜ[RatFunc k] 1 :=
  (fractionFieldEquivRatFuncTensor F F' hX).commutes c

/-- On the image of a pure tensor `f ⊗ₜ[k] c` in `F'`, `fractionFieldEquivRatFuncTensor` is
`algebraMap K (RatFunc K) c ⊗ₜ[RatFunc k] f`. -/
@[simp]
theorem fractionFieldEquivRatFuncTensor_algebraMap_tmul
    (hX : algebraMap (RatFunc k) (RatFunc K) RatFunc.X = RatFunc.X) (f : F) (c : K) :
    fractionFieldEquivRatFuncTensor F F' hX (algebraMap (F ⊗[k] K) F' (f ⊗ₜ[k] c)) =
      algebraMap K (RatFunc K) c ⊗ₜ[RatFunc k] f := by
  have hfc :
      algebraMap (F ⊗[k] K) F' (f ⊗ₜ[k] c) = algebraMap F F' f * algebraMap K F' c := by
    have htmul : f ⊗ₜ[k] c = (f ⊗ₜ[k] (1 : K)) * ((1 : F) ⊗ₜ[k] c) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [htmul, map_mul, IsScalarTower.algebraMap_apply F (F ⊗[k] K) F' f,
      IsScalarTower.algebraMap_apply K (F ⊗[k] K) F' c]
    rfl
  rw [hfc, map_mul, fractionFieldEquivRatFuncTensor_algebraMap_left,
    fractionFieldEquivRatFuncTensor_algebraMap_right, Algebra.TensorProduct.tmul_mul_tmul,
    one_mul, mul_one]

end CanonicalEquiv

end RatFuncFractionField

end RatFunc

end TauCeti

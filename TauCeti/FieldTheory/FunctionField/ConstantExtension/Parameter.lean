/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.ConstantExtension.FractionField
public import TauCeti.FieldTheory.RatFunc.Transcendental
public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Tensor presentations over an extended parameter field

Let `F' = F · K` be a linearly disjoint extension of constants of `F/k`, and let `C` be
an intermediate field with `F/C` algebraic. Multiplication identifies
`(C · K) ⊗[C] F` with `F'`, as algebras over `C · K`. In particular, when `F` and `F'`
carry compatible algebras over the rational function fields `k(X)` and `K(X)` with `F/k(X)`
algebraic, multiplication gives an algebra isomorphism `K(X) ⊗[k(X)] F ≃ₐ[K(X)] F'`.
The extension `K/k` can be transcendental, and `F/C` (or `F/k(X)`) need only be algebraic
and need not be separable or finite.

The same constructions apply to any specified fraction field of a domain `F ⊗[k] K`.
They keep the scalar maps and compute both directions on pure tensors, so the
presentations can be used to compare field maps, degrees, and bases after extending
constants. While `F ⊗[k] K` itself need not be a field when `K/k` is transcendental,
`K(X) ⊗[k(X)] F` is an integral domain whenever `F ⊗[k] K` is a domain, and a field when
`F/k(X)` is also algebraic.

The constructions use `TauCeti.constantExtensionBasisOfLinearDisjoint` and
`TauCeti.constantExtensionRatFuncBasis` for basis transport, and Mathlib's
`Module.Basis.baseChange` and `AlgHom.liftEquiv` for the tensor algebras.

## Main definitions

* `TauCeti.constantExtensionTensorEquiv` and
  `IntermediateField.fractionFieldParameterEquiv`: the `C · K`-algebra isomorphism
  `(C · K) ⊗[C] F ≃ₐ[C · K] F'` for an algebraic extension `F/C`, in a linearly disjoint
  compositum or a fraction field of `F ⊗[k] K`.
* `TauCeti.constantExtensionRatFuncTensorEquiv` and
  `TauCeti.fractionFieldRatFuncTensorEquiv`: the `RatFunc K`-algebra isomorphism
  `RatFunc K ⊗[RatFunc k] F ≃ₐ[RatFunc K] F'`.

## Main results

* `TauCeti.isDomain_ratFunc_tensorProduct` and `TauCeti.isField_ratFunc_tensorProduct`:
  when `F ⊗[k] K` is a domain, `RatFunc K ⊗[RatFunc k] F` is an integral domain, and a field when
  `F / RatFunc k` is algebraic.

## References

* S. Lang, *Algebra*, the theory of linearly disjoint field extensions.
* H. Stichtenoth, *Algebraic Function Fields and Codes*, second edition, Section III.6.
-/

public section

open scoped TensorProduct IntermediateField

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

section RatFunc

variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
  [Algebra (RatFunc K) F'] [IsScalarTower K (RatFunc K) F']
  [Algebra (RatFunc k) (RatFunc K)] [IsScalarTower k (RatFunc k) (RatFunc K)]

/-- The multiplication `RatFunc K`-algebra homomorphism `RatFunc K ⊗[RatFunc k] F →ₐ[RatFunc K] F'`,
built without assuming an external `Algebra (RatFunc k) F'` instance. -/
private noncomputable def ratFuncParameterLift
    (hX : algebraMap (RatFunc k) (RatFunc K) RatFunc.X = RatFunc.X)
    (hXF : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc K) F' RatFunc.X) :
    RatFunc K ⊗[RatFunc k] F →ₐ[RatFunc K] F' :=
  have hcomm := algebraMap_ratFunc_eq hX hXF
  letI : Algebra (RatFunc k) F' :=
    ((algebraMap (RatFunc K) F').comp (algebraMap (RatFunc k) (RatFunc K))).toAlgebra
  haveI : IsScalarTower (RatFunc k) (RatFunc K) F' := IsScalarTower.of_algebraMap_eq' rfl
  AlgHom.liftEquiv (RatFunc k) (RatFunc K) F F'
    { toRingHom := algebraMap F F'
      commutes' := hcomm }

/-- Multiplication `RatFunc K ⊗[RatFunc k] F → F'` is bijective when `F' = F · K` is linearly
disjoint over `k` and `F / RatFunc k` is algebraic. -/
private theorem bijective_ratFuncParameterLift
    (H : (IsScalarTower.toAlgHom k K F').fieldRange.LinearDisjoint F)
    (h : constantCompositum F K F' = ⊤)
    (hX : algebraMap (RatFunc k) (RatFunc K) RatFunc.X = RatFunc.X)
    (hXF : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc K) F' RatFunc.X)
    [Algebra.IsAlgebraic (RatFunc k) F] :
    Function.Bijective (ratFuncParameterLift hX hXF) := by
  let b := Module.Basis.ofVectorSpace (RatFunc k) F
  let b' := constantExtensionRatFuncBasis H h hXF b
  let e := (b.baseChange (RatFunc K)).equiv b' (Equiv.refl _)
  have he : (ratFuncParameterLift hX hXF).toLinearMap = e.toLinearMap := by
    apply (b.baseChange (RatFunc K)).ext
    intro i
    calc
      _ = algebraMap F F' (b i) := by
        simp [ratFuncParameterLift, AlgHom.liftEquiv_tmul]
      _ = b' i := (constantExtensionRatFuncBasis_apply H h hXF b i).symm
      _ = e ((b.baseChange _) i) := ((b.baseChange _).equiv_apply i b' (Equiv.refl _)).symm
  have hb : Function.Bijective (ratFuncParameterLift hX hXF).toLinearMap := by
    rw [he]
    exact e.bijective
  exact hb

/-- **The tensor presentation over the extended rational function field.**
If `F' = F · K` linearly disjointly over `k`, `F / RatFunc k` is algebraic, and the rational
variable `X` maps compatibly along `RatFunc k → RatFunc K` and `F → F'`, multiplication gives
an algebra isomorphism `RatFunc K ⊗[RatFunc k] F ≃ₐ[RatFunc K] F'`. The constant extension `K/k`
may be transcendental, and `F / RatFunc k` need not be separable or finite. -/
noncomputable def constantExtensionRatFuncTensorEquiv
    (H : (IsScalarTower.toAlgHom k K F').fieldRange.LinearDisjoint F)
    (h : constantCompositum F K F' = ⊤)
    (hX : algebraMap (RatFunc k) (RatFunc K) RatFunc.X = RatFunc.X)
    (hXF : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc K) F' RatFunc.X)
    [Algebra.IsAlgebraic (RatFunc k) F] :
    RatFunc K ⊗[RatFunc k] F ≃ₐ[RatFunc K] F' :=
  AlgEquiv.ofBijective (ratFuncParameterLift hX hXF)
    (bijective_ratFuncParameterLift H h hX hXF)

/-- On pure tensors, `constantExtensionRatFuncTensorEquiv` multiplies the `RatFunc K` scalar
and the image of `F` in `F'`. -/
@[simp]
theorem constantExtensionRatFuncTensorEquiv_tmul
    (H : (IsScalarTower.toAlgHom k K F').fieldRange.LinearDisjoint F)
    (h : constantCompositum F K F' = ⊤)
    (hX : algebraMap (RatFunc k) (RatFunc K) RatFunc.X = RatFunc.X)
    (hXF : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc K) F' RatFunc.X)
    [Algebra.IsAlgebraic (RatFunc k) F] (r : RatFunc K) (f : F) :
    constantExtensionRatFuncTensorEquiv H h hX hXF (r ⊗ₜ[RatFunc k] f) =
      algebraMap (RatFunc K) F' r * algebraMap F F' f := by
  simp [constantExtensionRatFuncTensorEquiv, ratFuncParameterLift, AlgHom.liftEquiv_tmul,
    Algebra.smul_def]

/-- The inverse of `constantExtensionRatFuncTensorEquiv` sends a product of the two images to a
pure tensor. -/
@[simp]
theorem constantExtensionRatFuncTensorEquiv_symm_mul
    (H : (IsScalarTower.toAlgHom k K F').fieldRange.LinearDisjoint F)
    (h : constantCompositum F K F' = ⊤)
    (hX : algebraMap (RatFunc k) (RatFunc K) RatFunc.X = RatFunc.X)
    (hXF : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc K) F' RatFunc.X)
    [Algebra.IsAlgebraic (RatFunc k) F] (r : RatFunc K) (f : F) :
    (constantExtensionRatFuncTensorEquiv H h hX hXF).symm
        (algebraMap (RatFunc K) F' r * algebraMap F F' f) =
      r ⊗ₜ[RatFunc k] f := by
  apply (constantExtensionRatFuncTensorEquiv H h hX hXF).injective
  simp

/-- The inverse of `constantExtensionRatFuncTensorEquiv` embeds `K` into the left factor. -/
@[simp]
theorem constantExtensionRatFuncTensorEquiv_symm_algebraMap_left
    (H : (IsScalarTower.toAlgHom k K F').fieldRange.LinearDisjoint F)
    (h : constantCompositum F K F' = ⊤)
    (hX : algebraMap (RatFunc k) (RatFunc K) RatFunc.X = RatFunc.X)
    (hXF : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc K) F' RatFunc.X)
    [Algebra.IsAlgebraic (RatFunc k) F] (c : K) :
    (constantExtensionRatFuncTensorEquiv H h hX hXF).symm (algebraMap K F' c) =
      algebraMap K (RatFunc K) c ⊗ₜ[RatFunc k] 1 := by
  apply (constantExtensionRatFuncTensorEquiv H h hX hXF).injective
  simp [-RatFunc.algebraMap_eq_C, ← IsScalarTower.algebraMap_apply K (RatFunc K) F']

/-- The inverse of `constantExtensionRatFuncTensorEquiv` embeds `F` into the right factor. -/
@[simp]
theorem constantExtensionRatFuncTensorEquiv_symm_algebraMap_right
    (H : (IsScalarTower.toAlgHom k K F').fieldRange.LinearDisjoint F)
    (h : constantCompositum F K F' = ⊤)
    (hX : algebraMap (RatFunc k) (RatFunc K) RatFunc.X = RatFunc.X)
    (hXF : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc K) F' RatFunc.X)
    [Algebra.IsAlgebraic (RatFunc k) F] (f : F) :
    (constantExtensionRatFuncTensorEquiv H h hX hXF).symm (algebraMap F F' f) =
      1 ⊗ₜ[RatFunc k] f := by
  apply (constantExtensionRatFuncTensorEquiv H h hX hXF).injective
  simp

end RatFunc

section FractionField

attribute [local instance] Algebra.TensorProduct.rightAlgebra
  Algebra.TensorProduct.right_isScalarTower

section SpecifiedFractionField

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
    (constantCompositum_eq_top_of_isFractionRing_tensorProduct (k := k)) C

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

section RatFunc

variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
  [Algebra (RatFunc K) F'] [IsScalarTower K (RatFunc K) F']
  [Algebra (RatFunc k) (RatFunc K)] [IsScalarTower k (RatFunc k) (RatFunc K)]

/-- **Tensor presentation of a fraction field of `F ⊗[k] K` over `RatFunc K`.**
For any fraction field `F'` of a domain `F ⊗[k] K`, if `F / RatFunc k` is algebraic and `X`
maps compatibly along `RatFunc k → RatFunc K` and `F → F'`, multiplication identifies
`RatFunc K ⊗[RatFunc k] F` with `F'` as `RatFunc K`-algebras. -/
noncomputable def fractionFieldRatFuncTensorEquiv
    (hX : algebraMap (RatFunc k) (RatFunc K) RatFunc.X = RatFunc.X)
    (hXF : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc K) F' RatFunc.X)
    [Algebra.IsAlgebraic (RatFunc k) F] :
    RatFunc K ⊗[RatFunc k] F ≃ₐ[RatFunc K] F' :=
  constantExtensionRatFuncTensorEquiv
    (linearDisjoint_of_isFractionRing_tensorProduct (k := k))
    (constantCompositum_eq_top_of_isFractionRing_tensorProduct (k := k)) hX hXF

/-- On pure tensors, `fractionFieldRatFuncTensorEquiv` multiplies the two images in `F'`. -/
@[simp]
theorem fractionFieldRatFuncTensorEquiv_tmul
    (hX : algebraMap (RatFunc k) (RatFunc K) RatFunc.X = RatFunc.X)
    (hXF : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc K) F' RatFunc.X)
    [Algebra.IsAlgebraic (RatFunc k) F] (r : RatFunc K) (f : F) :
    fractionFieldRatFuncTensorEquiv hX hXF (r ⊗ₜ[RatFunc k] f) =
      algebraMap (RatFunc K) F' r * algebraMap F F' f :=
  constantExtensionRatFuncTensorEquiv_tmul _ _ hX hXF r f

/-- The inverse of `fractionFieldRatFuncTensorEquiv` recovers pure tensors from products. -/
@[simp]
theorem fractionFieldRatFuncTensorEquiv_symm_mul
    (hX : algebraMap (RatFunc k) (RatFunc K) RatFunc.X = RatFunc.X)
    (hXF : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc K) F' RatFunc.X)
    [Algebra.IsAlgebraic (RatFunc k) F] (r : RatFunc K) (f : F) :
    (fractionFieldRatFuncTensorEquiv hX hXF).symm
        (algebraMap (RatFunc K) F' r * algebraMap F F' f) =
      r ⊗ₜ[RatFunc k] f :=
  constantExtensionRatFuncTensorEquiv_symm_mul _ _ hX hXF r f

/-- The inverse of `fractionFieldRatFuncTensorEquiv` embeds `K` into the left factor. -/
@[simp]
theorem fractionFieldRatFuncTensorEquiv_symm_algebraMap_left
    (hX : algebraMap (RatFunc k) (RatFunc K) RatFunc.X = RatFunc.X)
    (hXF : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc K) F' RatFunc.X)
    [Algebra.IsAlgebraic (RatFunc k) F] (c : K) :
    (fractionFieldRatFuncTensorEquiv hX hXF).symm (algebraMap K F' c) =
      algebraMap K (RatFunc K) c ⊗ₜ[RatFunc k] 1 :=
  constantExtensionRatFuncTensorEquiv_symm_algebraMap_left _ _ hX hXF c

/-- The inverse of `fractionFieldRatFuncTensorEquiv` embeds `F` into the right factor. -/
@[simp]
theorem fractionFieldRatFuncTensorEquiv_symm_algebraMap_right
    (hX : algebraMap (RatFunc k) (RatFunc K) RatFunc.X = RatFunc.X)
    (hXF : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc K) F' RatFunc.X)
    [Algebra.IsAlgebraic (RatFunc k) F] (f : F) :
    (fractionFieldRatFuncTensorEquiv hX hXF).symm (algebraMap F F' f) =
      1 ⊗ₜ[RatFunc k] f :=
  constantExtensionRatFuncTensorEquiv_symm_algebraMap_right _ _ hX hXF f

/-- The inverse of `fractionFieldRatFuncTensorEquiv` carries a pure tensor `f ⊗ₜ c` from
`F ⊗[k] K` inside `F'` to `c ⊗ₜ f` in `RatFunc K ⊗[RatFunc k] F`. -/
@[simp]
theorem fractionFieldRatFuncTensorEquiv_symm_algebraMap_tensorProduct_tmul
    (hX : algebraMap (RatFunc k) (RatFunc K) RatFunc.X = RatFunc.X)
    (hXF : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc K) F' RatFunc.X)
    [Algebra.IsAlgebraic (RatFunc k) F] (f : F) (c : K) :
    (fractionFieldRatFuncTensorEquiv hX hXF).symm (algebraMap (F ⊗[k] K) F' (f ⊗ₜ[k] c)) =
      algebraMap K (RatFunc K) c ⊗ₜ[RatFunc k] f := by
  apply (fractionFieldRatFuncTensorEquiv hX hXF).injective
  have hfc : (f ⊗ₜ[k] c : F ⊗[k] K) =
      algebraMap K (F ⊗[k] K) c * algebraMap F (F ⊗[k] K) f := by
    simp [Algebra.TensorProduct.right_algebraMap_apply]
  rw [AlgEquiv.apply_symm_apply, fractionFieldRatFuncTensorEquiv_tmul,
    ← IsScalarTower.algebraMap_apply K (RatFunc K) F', hfc, map_mul,
    ← IsScalarTower.algebraMap_apply K (F ⊗[k] K) F',
    ← IsScalarTower.algebraMap_apply F (F ⊗[k] K) F']

end RatFunc

end SpecifiedFractionField

section RatFuncTensorIsField

variable [IsDomain (F ⊗[k] K)] [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
  [Algebra (RatFunc k) (RatFunc K)] [IsScalarTower k (RatFunc k) (RatFunc K)]

/-- **The parameter tensor product `RatFunc K ⊗[RatFunc k] F` is an integral domain** whenever
`F ⊗[k] K` is an integral domain and `RatFunc.X` maps to `RatFunc.X`. -/
theorem isDomain_ratFunc_tensorProduct
    (hX : algebraMap (RatFunc k) (RatFunc K) RatFunc.X = RatFunc.X) :
    IsDomain (RatFunc K ⊗[RatFunc k] F) := by
  let Q := FractionRing (F ⊗[k] K)
  have hx : Transcendental k (algebraMap (RatFunc k) F RatFunc.X) :=
    (transcendental_algebraMap_iff
      (FaithfulSMul.algebraMap_injective (RatFunc k) F)).mpr RatFunc.transcendental_X
  have hxQ : Transcendental K (algebraMap F Q (algebraMap (RatFunc k) F RatFunc.X)) :=
    hx.algebraMap_of_isFractionRing_tensorProduct
  let _ : Algebra (RatFunc K) Q := ratFuncAlgebraOfTranscendental hxQ
  have _ : IsScalarTower K (RatFunc K) Q := isScalarTower_ratFuncAlgebraOfTranscendental hxQ
  have hXF : algebraMap F Q (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc K) Q RatFunc.X :=
    (algebraMap_ratFuncAlgebraOfTranscendental_X hxQ).symm
  let b := Module.Basis.ofVectorSpace (RatFunc k) F
  have hli := (linearDisjoint_of_isFractionRing_tensorProduct
    (k := k)).linearIndependent_ratFunc_algebraMap_comp hXF b.linearIndependent
  have hconstr : (ratFuncParameterLift (F' := Q) hX hXF).toLinearMap =
      (b.baseChange (RatFunc K)).constr (RatFunc K) (algebraMap F Q ∘ b) :=
    (b.baseChange (RatFunc K)).ext fun i ↦ by
      rw [Module.Basis.constr_basis]
      simp [ratFuncParameterLift, AlgHom.liftEquiv_tmul]
  have hinj : Function.Injective (ratFuncParameterLift (F' := Q) hX hXF) := by
    have : Function.Injective (ratFuncParameterLift (F' := Q) hX hXF).toLinearMap := by
      rw [hconstr]
      exact (b.baseChange (RatFunc K)).injective_constr_of_linearIndependent hli
    exact this
  exact Function.Injective.isDomain (ratFuncParameterLift (F' := Q) hX hXF).toRingHom hinj

/-- **The algebraic parameter tensor product `RatFunc K ⊗[RatFunc k] F` is a field** whenever
`F ⊗[k] K` is an integral domain, `F / RatFunc k` is algebraic, and `RatFunc.X` maps to
`RatFunc.X`. -/
theorem isField_ratFunc_tensorProduct [Algebra.IsAlgebraic (RatFunc k) F]
    (hX : algebraMap (RatFunc k) (RatFunc K) RatFunc.X = RatFunc.X) :
    IsField (RatFunc K ⊗[RatFunc k] F) := by
  have := isDomain_ratFunc_tensorProduct (F := F) hX
  exact Algebra.TensorProduct.isField_of_isAlgebraic (RatFunc k) (RatFunc K) F (.inr inferInstance)

end RatFuncTensorIsField

end FractionField

end TauCeti

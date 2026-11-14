/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.RatFunc.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import TauCeti.FieldTheory.FunctionField.ConstantExtension.FractionField
public import TauCeti.FieldTheory.FunctionField.ConstantExtension.Regular
import TauCeti.FieldTheory.RatFunc.Automorphism

/-!
# Tensor presentations and morphism lifting over an extended parameter field

Let `F' = F · K` be a linearly disjoint extension of constants of `F/k`, and let `C` be
an intermediate field with `F/C` algebraic. Multiplication identifies
`(C · K) ⊗[C] F` with `F'`, as algebras over `C · K`. In particular, when `F/k` is
a function field and `C = k(t)`, this is the finite algebra over `K(t)` presenting
the extended function field.
The extension `K/k` can be transcendental. The original extension `F/C` need only
be algebraic, and need not be separable or finite.

The same construction applies to a specified fraction field of `F ⊗[k] K`.
It keeps the scalar maps and computes both directions on pure tensors, so the
presentation can be used to compare field maps and bases after extending constants.
It does not assert that the original tensor product `F ⊗[k] K` is a field.

Using the fraction-field description of linearly disjoint composita from
`TauCeti.FieldTheory.FunctionField.ConstantExtension.Regular`, any `k`-algebra map `E →ₐ[k] F` lifts
uniquely to a `K`-algebra map `E' →ₐ[K] F'` (`TauCeti.constantExtensionAlgHom`), and any
`k(t)`-algebra map `E →ₐ[RatFunc k] F` lifts uniquely to a `K(t)`-algebra map
`E' →ₐ[RatFunc K] F'` (`TauCeti.ratFuncConstantExtensionAlgHom`). When `k` is algebraically closed
and `E / k(t)` is algebraic, `F` is relatively algebraically closed in `F'`, so every `K(t)`-algebra
map `E' →ₐ[RatFunc K] F'` descends back to `E →ₐ[RatFunc k] F`, giving bijections on `t`-morphisms,
`t`-isomorphisms, and `t`-automorphism groups (`TauCeti.ratFuncConstantExtensionAlgHomEquiv`,
`TauCeti.ratFuncConstantExtensionAlgEquivEquiv`, `TauCeti.ratFuncConstantExtensionAutMulEquiv`).

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

section Morphisms

variable {E E' : Type*} [Field E] [Field E'] [Algebra k E] [Algebra k E']
  [Algebra K E'] [Algebra E E'] [IsScalarTower k K E'] [IsScalarTower k E E']

/-- Two `K`-algebra homomorphisms out of `E' = E · K` that agree on `E` are equal. -/
theorem algHom_ext_of_constantCompositum_eq_top
    (hE : constantCompositum E K E' = ⊤) {φ₁ φ₂ : E' →ₐ[K] F'}
    (h : ∀ y : E, φ₁ (algebraMap E E' y) = φ₂ (algebraMap E E' y)) : φ₁ = φ₂ := by
  let L : IntermediateField E E' :=
    (φ₁.toRingHom.eqLocusField φ₂.toRingHom).toIntermediateField h
  have hle : constantCompositum E K E' ≤ L := by
    rw [constantCompositum_def, IntermediateField.adjoin_le_iff]
    rintro _ ⟨c, rfl⟩
    exact (φ₁.commutes c).trans (φ₂.commutes c).symm
  have htop : L = ⊤ := top_le_iff.mp (hE ▸ hle)
  exact AlgHom.ext fun z ↦ (htop ▸ IntermediateField.mem_top : z ∈ L)

/-- If `K` and `F` are linearly disjoint over `k` in `F'`, then for any `ψ : E →ₐ[k] F` the induced
multiplication map `E ⊗[k] K →ₐ[k] F'` is injective. -/
private theorem productMap_comp_injective
    (HF : (IsScalarTower.toAlgHom k K F').fieldRange.LinearDisjoint F) (ψ : E →ₐ[k] F) :
    Function.Injective (Algebra.TensorProduct.productMap
      ((IsScalarTower.toAlgHom k F F').comp ψ) (IsScalarTower.toAlgHom k K F')) := by
  let _ : Algebra E F' := ((IsScalarTower.toAlgHom k F F').comp ψ).toRingHom.toAlgebra
  have : IsScalarTower k E F' := .of_algebraMap_eq fun c ↦
    (((IsScalarTower.toAlgHom k F F').comp ψ).commutes c).symm
  have hdisj : (IsScalarTower.toAlgHom k K F').fieldRange.LinearDisjoint E := by
    rw [IntermediateField.linearDisjoint_iff]
    exact Subalgebra.LinearDisjoint.of_le_right_of_flat HF
      (AlgHom.range_comp_le_range ψ (IsScalarTower.toAlgHom k F F'))
  exact productMap_injective_iff_linearDisjoint.mpr hdisj

/-- **Base change of a `k`-algebra map along a linearly disjoint constant extension.** If
`E' = E · K` linearly disjointly over `k` and `K` is linearly disjoint from `F` in `F'`, every
`ψ : E →ₐ[k] F` extends uniquely to `E' →ₐ[K] F'`. The extension `K / k` may be transcendental. -/
noncomputable def constantExtensionAlgHom
    (HE : (IsScalarTower.toAlgHom k K E').fieldRange.LinearDisjoint E)
    (hE : constantCompositum E K E' = ⊤)
    (HF : (IsScalarTower.toAlgHom k K F').fieldRange.LinearDisjoint F)
    (ψ : E →ₐ[k] F) : E' →ₐ[K] F' :=
  letI := (Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom k E E')
    (IsScalarTower.toAlgHom k K E')).toRingHom.toAlgebra
  haveI : IsFractionRing (E ⊗[k] K) E' := isFractionRing_tensorProduct_of_linearDisjoint HE hE
  have hinj : Function.Injective (Algebra.TensorProduct.productMap
      ((IsScalarTower.toAlgHom k F F').comp ψ) (IsScalarTower.toAlgHom k K F')).toRingHom :=
    productMap_comp_injective HF ψ
  { IsFractionRing.lift (A := E ⊗[k] K) (K := E') hinj with
    commutes' := fun c ↦ by
      have hc : algebraMap (E ⊗[k] K) E' (1 ⊗ₜ[k] c) = algebraMap K E' c := by
        simp [RingHom.algebraMap_toAlgebra]
      change IsFractionRing.lift (A := E ⊗[k] K) (K := E') hinj (algebraMap K E' c) = _
      rw [← hc, IsFractionRing.lift_algebraMap]
      simp }

/-- `constantExtensionAlgHom` extends `ψ` along the scalar embeddings `E → E'` and `F → F'`. -/
@[simp]
theorem constantExtensionAlgHom_algebraMap
    (HE : (IsScalarTower.toAlgHom k K E').fieldRange.LinearDisjoint E)
    (hE : constantCompositum E K E' = ⊤)
    (HF : (IsScalarTower.toAlgHom k K F').fieldRange.LinearDisjoint F)
    (ψ : E →ₐ[k] F) (y : E) :
    constantExtensionAlgHom HE hE HF ψ (algebraMap E E' y) = algebraMap F F' (ψ y) := by
  let _ := (Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom k E E')
    (IsScalarTower.toAlgHom k K E')).toRingHom.toAlgebra
  have : IsFractionRing (E ⊗[k] K) E' := isFractionRing_tensorProduct_of_linearDisjoint HE hE
  have hy : algebraMap (E ⊗[k] K) E' (y ⊗ₜ[k] 1) = algebraMap E E' y := by
    simp [RingHom.algebraMap_toAlgebra]
  change IsFractionRing.lift (A := E ⊗[k] K) (K := E') (productMap_comp_injective HF ψ)
    (algebraMap E E' y) = _
  rw [← hy, IsFractionRing.lift_algebraMap]
  simp

@[simp]
theorem constantExtensionAlgHom_id
    (HE : (IsScalarTower.toAlgHom k K E').fieldRange.LinearDisjoint E)
    (hE : constantCompositum E K E' = ⊤) :
    constantExtensionAlgHom HE hE HE (AlgHom.id k E) = AlgHom.id K E' :=
  algHom_ext_of_constantCompositum_eq_top hE fun y ↦ by simp

theorem constantExtensionAlgHom_comp {L L' : Type*} [Field L] [Field L']
    [Algebra k L] [Algebra k L'] [Algebra K L'] [Algebra L L']
    [IsScalarTower k K L'] [IsScalarTower k L L']
    (HE : (IsScalarTower.toAlgHom k K E').fieldRange.LinearDisjoint E)
    (hE : constantCompositum E K E' = ⊤)
    (HF : (IsScalarTower.toAlgHom k K F').fieldRange.LinearDisjoint F)
    (hF : constantCompositum F K F' = ⊤)
    (HL : (IsScalarTower.toAlgHom k K L').fieldRange.LinearDisjoint L)
    (ψ₂ : F →ₐ[k] L) (ψ₁ : E →ₐ[k] F) :
    constantExtensionAlgHom HE hE HL (ψ₂.comp ψ₁) =
      (constantExtensionAlgHom HF hF HL ψ₂).comp (constantExtensionAlgHom HE hE HF ψ₁) :=
  algHom_ext_of_constantCompositum_eq_top hE fun y ↦ by simp

/-- **Base change of a `k`-algebra isomorphism along a linearly disjoint constant extension.** -/
noncomputable def constantExtensionAlgEquiv
    (HE : (IsScalarTower.toAlgHom k K E').fieldRange.LinearDisjoint E)
    (hE : constantCompositum E K E' = ⊤)
    (HF : (IsScalarTower.toAlgHom k K F').fieldRange.LinearDisjoint F)
    (hF : constantCompositum F K F' = ⊤)
    (e : E ≃ₐ[k] F) : E' ≃ₐ[K] F' :=
  AlgEquiv.ofAlgHom
    (constantExtensionAlgHom HE hE HF e.toAlgHom)
    (constantExtensionAlgHom HF hF HE e.symm.toAlgHom)
    (algHom_ext_of_constantCompositum_eq_top hF fun y ↦ by simp)
    (algHom_ext_of_constantCompositum_eq_top hE fun y ↦ by simp)

@[simp]
theorem constantExtensionAlgEquiv_algebraMap
    (HE : (IsScalarTower.toAlgHom k K E').fieldRange.LinearDisjoint E)
    (hE : constantCompositum E K E' = ⊤)
    (HF : (IsScalarTower.toAlgHom k K F').fieldRange.LinearDisjoint F)
    (hF : constantCompositum F K F' = ⊤)
    (e : E ≃ₐ[k] F) (y : E) :
    constantExtensionAlgEquiv HE hE HF hF e (algebraMap E E' y) = algebraMap F F' (e y) := by
  exact constantExtensionAlgHom_algebraMap HE hE HF e.toAlgHom y

end Morphisms

section RatFuncMorphisms

variable {E E' : Type*} [Field E] [Field E'] [Algebra k E] [Algebra k E']
  [Algebra K E'] [Algebra E E'] [IsScalarTower k K E'] [IsScalarTower k E E']
  [Algebra (RatFunc k) E] [IsScalarTower k (RatFunc k) E]
  [Algebra (RatFunc K) E'] [IsScalarTower K (RatFunc K) E']
  [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
  [Algebra (RatFunc K) F'] [IsScalarTower K (RatFunc K) F']

/-- Two `K(t)`-algebra homomorphisms out of `E' = E · K` that agree on `E` are equal. -/
theorem ratFuncAlgHom_ext_of_constantCompositum_eq_top
    (hE : constantCompositum E K E' = ⊤) {φ₁ φ₂ : E' →ₐ[RatFunc K] F'}
    (h : ∀ y : E, φ₁ (algebraMap E E' y) = φ₂ (algebraMap E E' y)) : φ₁ = φ₂ :=
  AlgHom.ext fun z ↦ DFunLike.congr_fun
    (algHom_ext_of_constantCompositum_eq_top hE
      (φ₁ := φ₁.restrictScalars K) (φ₂ := φ₂.restrictScalars K) h) z

/-- **Base change of a fixed-`t` morphism along a linearly disjoint constant extension.** -/
noncomputable def ratFuncConstantExtensionAlgHom
    (HE : (IsScalarTower.toAlgHom k K E').fieldRange.LinearDisjoint E)
    (hE : constantCompositum E K E' = ⊤)
    (HF : (IsScalarTower.toAlgHom k K F').fieldRange.LinearDisjoint F)
    (hXE : algebraMap E E' (algebraMap (RatFunc k) E RatFunc.X) =
      algebraMap (RatFunc K) E' RatFunc.X)
    (hXF : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc K) F' RatFunc.X)
    (ψ : E →ₐ[RatFunc k] F) : E' →ₐ[RatFunc K] F' :=
  let φ := constantExtensionAlgHom HE hE HF (ψ.restrictScalars k)
  { φ with
    commutes' := fun r ↦ DFunLike.congr_fun (RatFunc.algHom_ext
      (σ := φ.comp (IsScalarTower.toAlgHom K (RatFunc K) E'))
      (τ := IsScalarTower.toAlgHom K (RatFunc K) F') (by
        simp [φ, ← hXE, ψ.commutes, hXF])) r }

@[simp]
theorem ratFuncConstantExtensionAlgHom_algebraMap
    (HE : (IsScalarTower.toAlgHom k K E').fieldRange.LinearDisjoint E)
    (hE : constantCompositum E K E' = ⊤)
    (HF : (IsScalarTower.toAlgHom k K F').fieldRange.LinearDisjoint F)
    (hXE : algebraMap E E' (algebraMap (RatFunc k) E RatFunc.X) =
      algebraMap (RatFunc K) E' RatFunc.X)
    (hXF : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc K) F' RatFunc.X)
    (ψ : E →ₐ[RatFunc k] F) (y : E) :
    ratFuncConstantExtensionAlgHom HE hE HF hXE hXF ψ (algebraMap E E' y) =
      algebraMap F F' (ψ y) := by
  exact constantExtensionAlgHom_algebraMap HE hE HF (ψ.restrictScalars k) y

@[simp]
theorem ratFuncConstantExtensionAlgHom_id
    (HE : (IsScalarTower.toAlgHom k K E').fieldRange.LinearDisjoint E)
    (hE : constantCompositum E K E' = ⊤)
    (hXE : algebraMap E E' (algebraMap (RatFunc k) E RatFunc.X) =
      algebraMap (RatFunc K) E' RatFunc.X) :
    ratFuncConstantExtensionAlgHom HE hE HE hXE hXE (AlgHom.id (RatFunc k) E) =
      AlgHom.id (RatFunc K) E' :=
  ratFuncAlgHom_ext_of_constantCompositum_eq_top hE fun y ↦ by simp

theorem ratFuncConstantExtensionAlgHom_comp {L L' : Type*} [Field L] [Field L']
    [Algebra k L] [Algebra k L'] [Algebra K L'] [Algebra L L']
    [IsScalarTower k K L'] [IsScalarTower k L L']
    [Algebra (RatFunc k) L] [IsScalarTower k (RatFunc k) L]
    [Algebra (RatFunc K) L'] [IsScalarTower K (RatFunc K) L']
    (HE : (IsScalarTower.toAlgHom k K E').fieldRange.LinearDisjoint E)
    (hE : constantCompositum E K E' = ⊤)
    (HF : (IsScalarTower.toAlgHom k K F').fieldRange.LinearDisjoint F)
    (hF : constantCompositum F K F' = ⊤)
    (HL : (IsScalarTower.toAlgHom k K L').fieldRange.LinearDisjoint L)
    (hXE : algebraMap E E' (algebraMap (RatFunc k) E RatFunc.X) =
      algebraMap (RatFunc K) E' RatFunc.X)
    (hXF : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc K) F' RatFunc.X)
    (hXL : algebraMap L L' (algebraMap (RatFunc k) L RatFunc.X) =
      algebraMap (RatFunc K) L' RatFunc.X)
    (ψ₂ : F →ₐ[RatFunc k] L) (ψ₁ : E →ₐ[RatFunc k] F) :
    ratFuncConstantExtensionAlgHom HE hE HL hXE hXL (ψ₂.comp ψ₁) =
      (ratFuncConstantExtensionAlgHom HF hF HL hXF hXL ψ₂).comp
        (ratFuncConstantExtensionAlgHom HE hE HF hXE hXF ψ₁) :=
  ratFuncAlgHom_ext_of_constantCompositum_eq_top hE fun y ↦ by simp

/-- **Base change of a fixed-`t` isomorphism along a linearly disjoint constant extension.** -/
noncomputable def ratFuncConstantExtensionAlgEquiv
    (HE : (IsScalarTower.toAlgHom k K E').fieldRange.LinearDisjoint E)
    (hE : constantCompositum E K E' = ⊤)
    (HF : (IsScalarTower.toAlgHom k K F').fieldRange.LinearDisjoint F)
    (hF : constantCompositum F K F' = ⊤)
    (hXE : algebraMap E E' (algebraMap (RatFunc k) E RatFunc.X) =
      algebraMap (RatFunc K) E' RatFunc.X)
    (hXF : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc K) F' RatFunc.X)
    (e : E ≃ₐ[RatFunc k] F) : E' ≃ₐ[RatFunc K] F' :=
  AlgEquiv.ofAlgHom
    (ratFuncConstantExtensionAlgHom HE hE HF hXE hXF e.toAlgHom)
    (ratFuncConstantExtensionAlgHom HF hF HE hXF hXE e.symm.toAlgHom)
    (ratFuncAlgHom_ext_of_constantCompositum_eq_top hF fun y ↦ by simp)
    (ratFuncAlgHom_ext_of_constantCompositum_eq_top hE fun y ↦ by simp)

@[simp]
theorem ratFuncConstantExtensionAlgEquiv_algebraMap
    (HE : (IsScalarTower.toAlgHom k K E').fieldRange.LinearDisjoint E)
    (hE : constantCompositum E K E' = ⊤)
    (HF : (IsScalarTower.toAlgHom k K F').fieldRange.LinearDisjoint F)
    (hF : constantCompositum F K F' = ⊤)
    (hXE : algebraMap E E' (algebraMap (RatFunc k) E RatFunc.X) =
      algebraMap (RatFunc K) E' RatFunc.X)
    (hXF : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc K) F' RatFunc.X)
    (e : E ≃ₐ[RatFunc k] F) (y : E) :
    ratFuncConstantExtensionAlgEquiv HE hE HF hF hXE hXF e (algebraMap E E' y) =
      algebraMap F F' (e y) := by
  exact ratFuncConstantExtensionAlgHom_algebraMap HE hE HF hXE hXF e.toAlgHom y

/-- Over an algebraically closed base field `k`, every `K(t)`-morphism `E' →ₐ[RatFunc K] F'`
carries `E` into the image of `F`, because `E` is algebraic over `k(t) ⊆ F` and `F` is relatively
algebraically closed in `F'`. -/
private theorem map_algebraMap_mem_fieldRange_of_isAlgClosed [IsAlgClosed k]
    [Algebra.IsAlgebraic (RatFunc k) E]
    (HF : (IsScalarTower.toAlgHom k K F').fieldRange.LinearDisjoint F)
    (hF : constantCompositum F K F' = ⊤)
    (hXE : algebraMap E E' (algebraMap (RatFunc k) E RatFunc.X) =
      algebraMap (RatFunc K) E' RatFunc.X)
    (hXF : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc K) F' RatFunc.X)
    (φ : E' →ₐ[RatFunc K] F') :
    (((φ.restrictScalars K).restrictScalars k).comp (IsScalarTower.toAlgHom k E E')).comp
        (IsScalarTower.toAlgHom k (RatFunc k) E) =
      (IsScalarTower.toAlgHom k F F').comp (IsScalarTower.toAlgHom k (RatFunc k) F) ∧
      ∀ y : E, φ (algebraMap E E' y) ∈ (IsScalarTower.toAlgHom k F F').fieldRange := by
  have hrat : (((φ.restrictScalars K).restrictScalars k).comp (IsScalarTower.toAlgHom k E E')).comp
        (IsScalarTower.toAlgHom k (RatFunc k) E) =
      (IsScalarTower.toAlgHom k F F').comp (IsScalarTower.toAlgHom k (RatFunc k) F) :=
    RatFunc.algHom_ext (by simp [hXE, φ.commutes, hXF])
  refine ⟨hrat, fun y ↦ ?_⟩
  have hexF := isIntegrallyClosedIn_of_isAlgClosed_of_linearDisjoint HF hF
  obtain ⟨p, hp0, hp⟩ := Algebra.IsAlgebraic.isAlgebraic (R := RatFunc k) y
  let q : Polynomial F := p.map (algebraMap (RatFunc k) F)
  have hq0 : q ≠ 0 :=
    (Polynomial.map_ne_zero_iff (FaithfulSMul.algebraMap_injective (RatFunc k) F)).mpr hp0
  have hq : Polynomial.aeval (φ (algebraMap E E' y)) q = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_map]
    have hcomp : (algebraMap F F').comp (algebraMap (RatFunc k) F) =
        (φ.toRingHom.comp (algebraMap E E')).comp (algebraMap (RatFunc k) E) :=
      congrArg AlgHom.toRingHom hrat.symm
    have heval := Polynomial.hom_eval₂ p (algebraMap (RatFunc k) E)
      (φ.toRingHom.comp (algebraMap E E')) y
    rw [hcomp]
    exact heval.symm.trans (by rw [← Polynomial.aeval_def, hp, map_zero])
  obtain ⟨w, hw⟩ := isIntegrallyClosedIn_iff_forall_isAlgebraic.mp hexF _ ⟨q, hq0, hq⟩
  exact ⟨w, hw⟩

/-- Descent of a `K(t)`-morphism `E' →ₐ[RatFunc K] F'` to `E →ₐ[RatFunc k] F` when `k` is
algebraically closed. -/
private noncomputable def descendRatFuncAlgHom [IsAlgClosed k]
    [Algebra.IsAlgebraic (RatFunc k) E]
    (HF : (IsScalarTower.toAlgHom k K F').fieldRange.LinearDisjoint F)
    (hF : constantCompositum F K F' = ⊤)
    (hXE : algebraMap E E' (algebraMap (RatFunc k) E RatFunc.X) =
      algebraMap (RatFunc K) E' RatFunc.X)
    (hXF : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc K) F' RatFunc.X)
    (φ : E' →ₐ[RatFunc K] F') : E →ₐ[RatFunc k] F :=
  let hφ := map_algebraMap_mem_fieldRange_of_isAlgClosed HF hF hXE hXF φ
  let ψ₀ : E →ₐ[k] F :=
    (IsScalarTower.toAlgHom k F F').equivFieldRange.symm.toAlgHom.comp
      ((((φ.restrictScalars K).restrictScalars k).comp
        (IsScalarTower.toAlgHom k E E')).codRestrict _ hφ.2)
  have hψ₀ : ∀ y : E, algebraMap F F' (ψ₀ y) = φ (algebraMap E E' y) := fun y ↦ by
    let z : (IsScalarTower.toAlgHom k F F').fieldRange := ⟨φ (algebraMap E E' y), hφ.2 y⟩
    exact congrArg Subtype.val ((IsScalarTower.toAlgHom k F F').equivFieldRange.apply_symm_apply z)
  { ψ₀ with
    commutes' := fun r ↦ (algebraMap F F').injective (by
      change algebraMap F F' (ψ₀ (algebraMap (RatFunc k) E r)) = _
      rw [hψ₀]
      exact DFunLike.congr_fun hφ.1 r) }

/-- **Full faithfulness on fixed-`t` morphisms over an algebraically closed base field.** If `k` is
algebraically closed, `E / k(t)` is algebraic, and `E' = E · K`, `F' = F · K` are linearly disjoint
constant extensions (possibly transcendental, such as `AlgebraicClosure ℚ ⊂ ℂ`), base change
identifies `(E →ₐ[RatFunc k] F)` with `(E' →ₐ[RatFunc K] F')`. -/
noncomputable def ratFuncConstantExtensionAlgHomEquiv [IsAlgClosed k]
    [Algebra.IsAlgebraic (RatFunc k) E]
    (HE : (IsScalarTower.toAlgHom k K E').fieldRange.LinearDisjoint E)
    (hE : constantCompositum E K E' = ⊤)
    (HF : (IsScalarTower.toAlgHom k K F').fieldRange.LinearDisjoint F)
    (hF : constantCompositum F K F' = ⊤)
    (hXE : algebraMap E E' (algebraMap (RatFunc k) E RatFunc.X) =
      algebraMap (RatFunc K) E' RatFunc.X)
    (hXF : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc K) F' RatFunc.X) :
    (E →ₐ[RatFunc k] F) ≃ (E' →ₐ[RatFunc K] F') where
  toFun := ratFuncConstantExtensionAlgHom HE hE HF hXE hXF
  invFun := descendRatFuncAlgHom HF hF hXE hXF
  left_inv ψ := AlgHom.ext fun y ↦ (algebraMap F F').injective <| by
    have h := congrArg Subtype.val ((IsScalarTower.toAlgHom k F F').equivFieldRange.apply_symm_apply
      ⟨_, (map_algebraMap_mem_fieldRange_of_isAlgClosed HF hF hXE hXF
        (ratFuncConstantExtensionAlgHom HE hE HF hXE hXF ψ)).2 y⟩)
    exact h.trans (ratFuncConstantExtensionAlgHom_algebraMap HE hE HF hXE hXF ψ y)
  right_inv φ := ratFuncAlgHom_ext_of_constantCompositum_eq_top hE fun y ↦ by
    rw [ratFuncConstantExtensionAlgHom_algebraMap]
    exact congrArg Subtype.val ((IsScalarTower.toAlgHom k F F').equivFieldRange.apply_symm_apply
      ⟨_, (map_algebraMap_mem_fieldRange_of_isAlgClosed HF hF hXE hXF φ).2 y⟩)

@[simp]
theorem ratFuncConstantExtensionAlgHomEquiv_apply [IsAlgClosed k]
    [Algebra.IsAlgebraic (RatFunc k) E]
    (HE : (IsScalarTower.toAlgHom k K E').fieldRange.LinearDisjoint E)
    (hE : constantCompositum E K E' = ⊤)
    (HF : (IsScalarTower.toAlgHom k K F').fieldRange.LinearDisjoint F)
    (hF : constantCompositum F K F' = ⊤)
    (hXE : algebraMap E E' (algebraMap (RatFunc k) E RatFunc.X) =
      algebraMap (RatFunc K) E' RatFunc.X)
    (hXF : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc K) F' RatFunc.X)
    (ψ : E →ₐ[RatFunc k] F) :
    ratFuncConstantExtensionAlgHomEquiv HE hE HF hF hXE hXF ψ =
      ratFuncConstantExtensionAlgHom HE hE HF hXE hXF ψ := by
  rfl

/-- **Full faithfulness on fixed-`t` isomorphisms over an algebraically closed base field.** For
algebraic extensions `E, F` of `k(t)` with `k` algebraically closed, extending constants to `K`
gives a bijection `(E ≃ₐ[RatFunc k] F) ≃ (E' ≃ₐ[RatFunc K] F')`. -/
noncomputable def ratFuncConstantExtensionAlgEquivEquiv [IsAlgClosed k]
    [Algebra.IsAlgebraic (RatFunc k) E] [Algebra.IsAlgebraic (RatFunc k) F]
    (HE : (IsScalarTower.toAlgHom k K E').fieldRange.LinearDisjoint E)
    (hE : constantCompositum E K E' = ⊤)
    (HF : (IsScalarTower.toAlgHom k K F').fieldRange.LinearDisjoint F)
    (hF : constantCompositum F K F' = ⊤)
    (hXE : algebraMap E E' (algebraMap (RatFunc k) E RatFunc.X) =
      algebraMap (RatFunc K) E' RatFunc.X)
    (hXF : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc K) F' RatFunc.X) :
    (E ≃ₐ[RatFunc k] F) ≃ (E' ≃ₐ[RatFunc K] F') where
  toFun := ratFuncConstantExtensionAlgEquiv HE hE HF hF hXE hXF
  invFun e' :=
    let ψ₁ := (ratFuncConstantExtensionAlgHomEquiv HE hE HF hF hXE hXF).symm e'.toAlgHom
    let ψ₂ := (ratFuncConstantExtensionAlgHomEquiv HF hF HE hE hXF hXE).symm e'.symm.toAlgHom
    AlgEquiv.ofAlgHom ψ₁ ψ₂
      ((ratFuncConstantExtensionAlgHomEquiv HF hF HF hF hXF hXF).injective <| by
        have h₁ : ratFuncConstantExtensionAlgHom HE hE HF hXE hXF ψ₁ = e'.toAlgHom :=
          (ratFuncConstantExtensionAlgHomEquiv HE hE HF hF hXE hXF).apply_symm_apply e'.toAlgHom
        have h₂ : ratFuncConstantExtensionAlgHom HF hF HE hXF hXE ψ₂ = e'.symm.toAlgHom :=
          (ratFuncConstantExtensionAlgHomEquiv HF hF HE hE hXF hXE).apply_symm_apply
            e'.symm.toAlgHom
        rw [ratFuncConstantExtensionAlgHomEquiv_apply,
          ratFuncConstantExtensionAlgHom_comp HF hF HE hE HF hXF hXE hXF, h₁, h₂,
          ratFuncConstantExtensionAlgHomEquiv_apply, ratFuncConstantExtensionAlgHom_id]
        exact AlgHom.ext fun z ↦ e'.apply_symm_apply z)
      ((ratFuncConstantExtensionAlgHomEquiv HE hE HE hE hXE hXE).injective <| by
        have h₁ : ratFuncConstantExtensionAlgHom HE hE HF hXE hXF ψ₁ = e'.toAlgHom :=
          (ratFuncConstantExtensionAlgHomEquiv HE hE HF hF hXE hXF).apply_symm_apply e'.toAlgHom
        have h₂ : ratFuncConstantExtensionAlgHom HF hF HE hXF hXE ψ₂ = e'.symm.toAlgHom :=
          (ratFuncConstantExtensionAlgHomEquiv HF hF HE hE hXF hXE).apply_symm_apply
            e'.symm.toAlgHom
        rw [ratFuncConstantExtensionAlgHomEquiv_apply,
          ratFuncConstantExtensionAlgHom_comp HE hE HF hF HE hXE hXF hXE, h₁, h₂,
          ratFuncConstantExtensionAlgHomEquiv_apply, ratFuncConstantExtensionAlgHom_id]
        exact AlgHom.ext fun z ↦ e'.symm_apply_apply z)
  left_inv e := AlgEquiv.ext fun y ↦
    DFunLike.congr_fun ((ratFuncConstantExtensionAlgHomEquiv HE hE HF hF hXE hXF).symm_apply_apply
      e.toAlgHom) y
  right_inv e' := AlgEquiv.ext fun z ↦ by
    change ((ratFuncConstantExtensionAlgHomEquiv HE hE HF hF hXE hXF)
      ((ratFuncConstantExtensionAlgHomEquiv HE hE HF hF hXE hXF).symm e'.toAlgHom)) z = e' z
    simp

@[simp]
theorem ratFuncConstantExtensionAlgEquivEquiv_apply_algebraMap [IsAlgClosed k]
    [Algebra.IsAlgebraic (RatFunc k) E] [Algebra.IsAlgebraic (RatFunc k) F]
    (HE : (IsScalarTower.toAlgHom k K E').fieldRange.LinearDisjoint E)
    (hE : constantCompositum E K E' = ⊤)
    (HF : (IsScalarTower.toAlgHom k K F').fieldRange.LinearDisjoint F)
    (hF : constantCompositum F K F' = ⊤)
    (hXE : algebraMap E E' (algebraMap (RatFunc k) E RatFunc.X) =
      algebraMap (RatFunc K) E' RatFunc.X)
    (hXF : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc K) F' RatFunc.X)
    (e : E ≃ₐ[RatFunc k] F) (y : E) :
    ratFuncConstantExtensionAlgEquivEquiv HE hE HF hF hXE hXF e (algebraMap E E' y) =
      algebraMap F F' (e y) := by
  exact ratFuncConstantExtensionAlgEquiv_algebraMap HE hE HF hF hXE hXF e y

/-- **Automorphism groups of fixed-`t` extensions are invariant under constant extension from an
algebraically closed base field.** -/
noncomputable def ratFuncConstantExtensionAutMulEquiv [IsAlgClosed k]
    [Algebra.IsAlgebraic (RatFunc k) F]
    (HF : (IsScalarTower.toAlgHom k K F').fieldRange.LinearDisjoint F)
    (hF : constantCompositum F K F' = ⊤)
    (hXF : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc K) F' RatFunc.X) :
    (F ≃ₐ[RatFunc k] F) ≃* (F' ≃ₐ[RatFunc K] F') :=
  { ratFuncConstantExtensionAlgEquivEquiv HF hF HF hF hXF hXF with
    map_mul' := fun e₁ e₂ ↦ AlgEquiv.ext fun z ↦
      DFunLike.congr_fun (ratFuncAlgHom_ext_of_constantCompositum_eq_top hF
        (φ₁ := (ratFuncConstantExtensionAlgEquiv HF hF HF hF hXF hXF (e₁ * e₂)).toAlgHom)
        (φ₂ := ((ratFuncConstantExtensionAlgEquiv HF hF HF hF hXF hXF e₁) *
          (ratFuncConstantExtensionAlgEquiv HF hF HF hF hXF hXF e₂)).toAlgHom)
        fun y ↦ by simp [AlgEquiv.mul_apply]) z }

end RatFuncMorphisms

end TauCeti

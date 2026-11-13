/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.ConstantExtension.FractionField
public import TauCeti.FieldTheory.RatFunc.Transcendental
public import Mathlib.LinearAlgebra.TensorProduct.Basis
import TauCeti.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# Tensor presentations over an extended parameter field

Let `F' = F · K` be a linearly disjoint extension of constants of `F/k`, and let `C` be
an intermediate field with `F/C` algebraic. Multiplication identifies
`(C · K) ⊗[C] F` with `F'`, as algebras over `C · K`. In particular, when `F` and `F'`
carry compatible algebras over the rational function fields `k(X)` and `K(X)` with `F/k(X)`
algebraic, bases over `k(X)` transport to bases over `K(X)`, the degree `[F' : K(X)]`
equals `[F : k(X)]`, separability over `k(X)` persists over `K(X)`, and multiplication
gives an algebra isomorphism `K(X) ⊗[k(X)] F ≃ₐ[K(X)] F'`.
The extension `K/k` can be transcendental. The original extension `F/C` (or `F/k(X)`) need
only be algebraic for basis transport and the tensor presentation, and need not be separable
or finite.

The same constructions apply to any specified fraction field of a domain `F ⊗[k] K`.
They keep the scalar maps and compute both directions on pure tensors, so the
presentations can be used to compare field maps, degrees, and bases after extending
constants. While `F ⊗[k] K` itself need not be a field when `K/k` is transcendental,
`K(X) ⊗[k(X)] F` is an integral domain whenever `F ⊗[k] K` is a domain, and a field when
`F/k(X)` is also algebraic.

The constructions use `TauCeti.constantExtensionBasisOfLinearDisjoint` for basis transport
and Mathlib's `Module.Basis.baseChange` and `AlgHom.liftEquiv` for the tensor algebras.

## Main definitions

* `TauCeti.constantExtensionTensorEquiv` and
  `IntermediateField.fractionFieldParameterEquiv`: the `C · K`-algebra isomorphism
  `(C · K) ⊗[C] F ≃ₐ[C · K] F'` for an algebraic extension `F/C`, in a linearly disjoint
  compositum or a fraction field of `F ⊗[k] K`.
* `TauCeti.constantExtensionRatFuncBasis`: transport a `RatFunc k`-basis of `F` to a
  `RatFunc K`-basis of `F'`.
* `TauCeti.constantExtensionRatFuncTensorEquiv` and
  `TauCeti.fractionFieldRatFuncTensorEquiv`: the `RatFunc K`-algebra isomorphism
  `RatFunc K ⊗[RatFunc k] F ≃ₐ[RatFunc K] F'`.

## Main results

* `TauCeti.constantExtensionRatFuncBasis_repr_algebraMap`: the coordinates of an element of `F` in
  `TauCeti.constantExtensionRatFuncBasis` are the images of its coordinates over `RatFunc k`.
* `TauCeti.isSeparable_ratFunc_of_constantCompositum_eq_top` and
  `TauCeti.isSeparable_ratFunc_of_isFractionRing_tensorProduct`: separability over
  `RatFunc k` persists over `RatFunc K`.
* `TauCeti.finrank_ratFunc_eq_of_linearDisjoint` and
  `TauCeti.finrank_ratFunc_eq_of_isFractionRing_tensorProduct`: linearly disjoint (possibly
  transcendental) constant extensions preserve `[F : RatFunc k]`.
* `TauCeti.isField_ratFunc_tensorProduct` and `TauCeti.isDomain_ratFunc_tensorProduct`:
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

/-- **Separability over the rational parameter field persists in a constant compositum.**
If `F' = F · K`, the rational variable `X` acts compatibly on `F` and `F'`, and `F` is
separable algebraic over `RatFunc k`, then `F'` is separable algebraic over `RatFunc K`.
Neither linear disjointness nor algebraicity of `K/k` is required. -/
theorem isSeparable_ratFunc_of_constantCompositum_eq_top
    (h : constantCompositum F K F' = ⊤)
    (hXF : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc K) F' RatFunc.X)
    [Algebra.IsSeparable (RatFunc k) F] :
    Algebra.IsSeparable (RatFunc K) F' := by
  have : Algebra.IsSeparable k⟮algebraMap (RatFunc k) F RatFunc.X⟯ F :=
    isSeparable_adjoin_algebraMap_X_iff.mpr ‹_›
  have hsep := isSeparable_adjoin_image_of_constantCompositum_eq_top (k := k) (k' := K) h
    (S := {algebraMap (RatFunc k) F RatFunc.X})
  rw [Set.image_singleton, hXF] at hsep
  exact isSeparable_adjoin_algebraMap_X_iff.mp hsep

/-- **Transport of a `RatFunc k`-basis along a linearly disjoint extension of constants.**
If `F' = F · K` linearly disjointly over `k`, `F / RatFunc k` is algebraic, and the rational
variable `X` acts compatibly on `F` and `F'`, any `RatFunc k`-basis of `F` maps to a
`RatFunc K`-basis of `F'`. The constant extension `K/k` may be transcendental. -/
noncomputable def constantExtensionRatFuncBasis
    (H : (IsScalarTower.toAlgHom k K F').fieldRange.LinearDisjoint F)
    (h : constantCompositum F K F' = ⊤)
    (hXF : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc K) F' RatFunc.X)
    [Algebra.IsAlgebraic (RatFunc k) F] {ι : Type*} (b : Module.Basis ι (RatFunc k) F) :
    Module.Basis ι (RatFunc K) F' := by
  let x := algebraMap (RatFunc k) F RatFunc.X
  let x' := algebraMap (RatFunc K) F' RatFunc.X
  have hx : Transcendental k x := (transcendental_algebraMap_iff
    (FaithfulSMul.algebraMap_injective (RatFunc k) F)).mpr RatFunc.transcendental_X
  have hx' : Transcendental K x' := (transcendental_algebraMap_iff
    (FaithfulSMul.algebraMap_injective (RatFunc K) F')).mpr RatFunc.transcendental_X
  let ek := RatFunc.algEquivOfTranscendental x hx
  have hcomp : RingHom.comp (algebraMap k⟮x⟯ F) ek.toRingEquiv =
      RingHom.comp (RingEquiv.refl F) (algebraMap (RatFunc k) F) :=
    RingHom.ext coe_algEquivOfTranscendental_algebraMap_X_apply
  have : Algebra.IsAlgebraic k⟮x⟯ F :=
    (Algebra.isAlgebraic_ringHom_iff_of_comp_eq ek.toRingEquiv (RingEquiv.refl F) hcomp).mpr ‹_›
  let b₀ : Module.Basis ι k⟮x⟯ F := b.mapCoeffs ek.toRingEquiv fun r v ↦ by
    rw [Algebra.smul_def, Algebra.smul_def]
    exact congrArg (· * v) (coe_algEquivOfTranscendental_algebraMap_X_apply r)
  have hadj : IntermediateField.adjoin K (Set.range (algebraMap k⟮x⟯ F')) = K⟮x'⟯ := by
    rw [IntermediateField.range_algebraMap_adjoin_simple, IntermediateField.adjoin_adjoin_right,
      hXF]
  let σ : IntermediateField.adjoin K (Set.range (algebraMap k⟮x⟯ F')) ≃+* RatFunc K :=
    (IntermediateField.equivOfEq hadj).toRingEquiv.trans
      (RatFunc.algEquivOfTranscendental x' hx').symm.toRingEquiv
  refine (constantExtensionBasisOfLinearDisjoint H h k⟮x⟯ b₀).mapCoeffs σ fun c y ↦ ?_
  simp only [Algebra.smul_def]
  refine congrArg (· * y) ?_
  have hr := coe_algEquivOfTranscendental_algebraMap_X_apply (k := K) (F := F') (σ c)
  simpa [σ, x'] using hr.symm

/-- The transported `RatFunc K`-basis consists of the images of the original basis vectors. -/
@[simp]
theorem constantExtensionRatFuncBasis_apply
    (H : (IsScalarTower.toAlgHom k K F').fieldRange.LinearDisjoint F)
    (h : constantCompositum F K F' = ⊤)
    (hXF : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc K) F' RatFunc.X)
    [Algebra.IsAlgebraic (RatFunc k) F] {ι : Type*} (b : Module.Basis ι (RatFunc k) F) (i : ι) :
    constantExtensionRatFuncBasis H h hXF b i = algebraMap F F' (b i) := by
  simp [constantExtensionRatFuncBasis]

/-- Linearly disjoint constant extensions preserve `RatFunc`-linear independence of a
`RatFunc k`-basis of `F`, without requiring `F / RatFunc k` to be algebraic. -/
private theorem linearIndependent_ratFunc_of_linearDisjoint
    (H : (IsScalarTower.toAlgHom k K F').fieldRange.LinearDisjoint F)
    (hXF : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc K) F' RatFunc.X)
    {ι : Type*} (b : Module.Basis ι (RatFunc k) F) :
    LinearIndependent (RatFunc K) (fun i ↦ algebraMap F F' (b i)) := by
  let x := algebraMap (RatFunc k) F RatFunc.X
  let x' := algebraMap (RatFunc K) F' RatFunc.X
  have hx : Transcendental k x := (transcendental_algebraMap_iff
    (FaithfulSMul.algebraMap_injective (RatFunc k) F)).mpr RatFunc.transcendental_X
  have hx' : Transcendental K x' := (transcendental_algebraMap_iff
    (FaithfulSMul.algebraMap_injective (RatFunc K) F')).mpr RatFunc.transcendental_X
  let ek := RatFunc.algEquivOfTranscendental x hx
  let b₀ : Module.Basis ι k⟮x⟯ F := b.mapCoeffs ek.toRingEquiv fun r v ↦ by
    rw [Algebra.smul_def, Algebra.smul_def]
    exact congrArg (· * v) (coe_algEquivOfTranscendental_algebraMap_X_apply r)
  have hli := H.linearIndependent_adjoin_algebraMap_comp k⟮x⟯ b₀.linearIndependent
  have hadj : IntermediateField.adjoin K (Set.range (algebraMap k⟮x⟯ F')) = K⟮x'⟯ := by
    rw [IntermediateField.range_algebraMap_adjoin_simple, IntermediateField.adjoin_adjoin_right,
      hXF]
  let σ : IntermediateField.adjoin K (Set.range (algebraMap k⟮x⟯ F')) ≃+* RatFunc K :=
    (IntermediateField.equivOfEq hadj).toRingEquiv.trans
      (RatFunc.algEquivOfTranscendental x' hx').symm.toRingEquiv
  have hσ (c : IntermediateField.adjoin K (Set.range (algebraMap k⟮x⟯ F'))) (y : F') :
      σ c • y = c • y := by
    simp only [Algebra.smul_def]
    refine congrArg (· * y) ?_
    have hr := coe_algEquivOfTranscendental_algebraMap_X_apply (k := K) (F := F') (σ c)
    simpa [σ, x'] using hr.symm
  rw [linearIndependent_iff'] at hli ⊢
  intro s g hg i hi
  have hg' : ∑ j ∈ s, σ.symm (g j) • (algebraMap F F' ∘ b₀) j = 0 := by
    simpa [← hσ, b₀] using hg
  simpa using hli s (fun j ↦ σ.symm (g j)) hg' i hi

/-- **Linearly disjoint constant extensions preserve degree over the rational function field.**
If `F' = F · K` linearly disjointly over `k` and `X` acts compatibly on `F` and `F'`, then
`[F' : RatFunc K] = [F : RatFunc k]`. Unlike
`TauCeti.finrank_ratFunc_eq_of_constantCompositum_eq_top`, the extension `K/k` may be
transcendental or inseparable once linear disjointness holds. -/
theorem finrank_ratFunc_eq_of_linearDisjoint
    (H : (IsScalarTower.toAlgHom k K F').fieldRange.LinearDisjoint F)
    (h : constantCompositum F K F' = ⊤)
    (hXF : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc K) F' RatFunc.X) :
    Module.finrank (RatFunc K) F' = Module.finrank (RatFunc k) F := by
  let b := Module.Basis.ofVectorSpace (RatFunc k) F
  by_cases hfin : FiniteDimensional (RatFunc k) F
  · have : Algebra.IsAlgebraic (RatFunc k) F := Algebra.IsAlgebraic.of_finite (RatFunc k) F
    exact (Module.finrank_eq_nat_card_basis (constantExtensionRatFuncBasis H h hXF b)).trans
      (Module.finrank_eq_nat_card_basis b).symm
  · have hfin' : ¬ FiniteDimensional (RatFunc K) F' := fun hfin' ↦ hfin <| by
      have : Finite (Module.Basis.ofVectorSpaceIndex (RatFunc k) F) :=
        (linearIndependent_ratFunc_of_linearDisjoint H hXF b).finite
      exact Module.Finite.of_basis b
    rw [Module.finrank_of_not_finite hfin', Module.finrank_of_not_finite hfin]

section TensorPresentation

variable [Algebra (RatFunc k) (RatFunc K)] [IsScalarTower k (RatFunc k) (RatFunc K)]

/-- The coordinates of an element of `F` in `constantExtensionRatFuncBasis` are the images of its
coordinates over `RatFunc k`. -/
theorem constantExtensionRatFuncBasis_repr_algebraMap
    (H : (IsScalarTower.toAlgHom k K F').fieldRange.LinearDisjoint F)
    (h : constantCompositum F K F' = ⊤)
    (hX : algebraMap (RatFunc k) (RatFunc K) RatFunc.X = RatFunc.X)
    (hXF : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc K) F' RatFunc.X)
    [Algebra.IsAlgebraic (RatFunc k) F] {ι : Type*} (b : Module.Basis ι (RatFunc k) F)
    (x : F) (i : ι) :
    (constantExtensionRatFuncBasis H h hXF b).repr (algebraMap F F' x) i =
      algebraMap (RatFunc k) (RatFunc K) (b.repr x i) := by
  have hx : algebraMap F F' x = Finsupp.linearCombination (RatFunc K)
      (constantExtensionRatFuncBasis H h hXF b)
      ((b.repr x).mapRange (algebraMap (RatFunc k) (RatFunc K)) (map_zero _)) := by
    conv_lhs => rw [← b.linearCombination_repr x]
    rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply, map_finsuppSum,
      Finsupp.sum_mapRange_index (by simp)]
    refine Finsupp.sum_congr fun j _ ↦ ?_
    simp only [Algebra.smul_def, map_mul, algebraMap_ratFunc_eq hX hXF,
      constantExtensionRatFuncBasis_apply]
  rw [hx, Module.Basis.repr_linearCombination, Finsupp.mapRange_apply]

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

end TensorPresentation

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

omit [IsScalarTower k (F ⊗[k] K) F'] in
/-- Separability over `RatFunc k` persists in any fraction field `F'` of `F ⊗[k] K` over
`RatFunc K` when the rational variable `X` maps compatibly. -/
theorem isSeparable_ratFunc_of_isFractionRing_tensorProduct
    (hXF : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc K) F' RatFunc.X)
    [Algebra.IsSeparable (RatFunc k) F] :
    Algebra.IsSeparable (RatFunc K) F' :=
  isSeparable_ratFunc_of_constantCompositum_eq_top (k := k)
    (constantCompositum_eq_top_of_isFractionRing_tensorProduct (k := k)) hXF

/-- **Degree over the rational function field is preserved in any fraction field of `F ⊗[k] K`.**
When `X` acts compatibly on `F` and `F'`, we have `[F' : RatFunc K] = [F : RatFunc k]`, with no
algebraicity or separability hypothesis on `K/k` or `F / RatFunc k`. -/
theorem finrank_ratFunc_eq_of_isFractionRing_tensorProduct
    (hXF : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc K) F' RatFunc.X) :
    Module.finrank (RatFunc K) F' = Module.finrank (RatFunc k) F :=
  finrank_ratFunc_eq_of_linearDisjoint
    (linearDisjoint_of_isFractionRing_tensorProduct (k := k))
    (constantCompositum_eq_top_of_isFractionRing_tensorProduct (k := k)) hXF

section TensorPresentation

variable [Algebra (RatFunc k) (RatFunc K)] [IsScalarTower k (RatFunc k) (RatFunc K)]

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

end TensorPresentation

end RatFunc

end SpecifiedFractionField

section RatFuncTensorIsField

variable [IsDomain (F ⊗[k] K)] [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
  [Algebra (RatFunc k) (RatFunc K)] [IsScalarTower k (RatFunc k) (RatFunc K)]
  [Algebra.IsAlgebraic (RatFunc k) F]

/-- **The finite parameter tensor product `RatFunc K ⊗[RatFunc k] F` is a field** whenever
`F ⊗[k] K` is an integral domain, `F / RatFunc k` is algebraic, and `RatFunc.X` maps to
`RatFunc.X`: it is isomorphic as a `RatFunc K`-algebra to `FractionRing (F ⊗[k] K)`. -/
theorem isField_ratFunc_tensorProduct
    (hX : algebraMap (RatFunc k) (RatFunc K) RatFunc.X = RatFunc.X) :
    IsField (RatFunc K ⊗[RatFunc k] F) := by
  let Q := FractionRing (F ⊗[k] K)
  have hx : Transcendental k (algebraMap (RatFunc k) F RatFunc.X) :=
    (transcendental_algebraMap_iff
      (FaithfulSMul.algebraMap_injective (RatFunc k) F)).mpr RatFunc.transcendental_X
  have hxQ : Transcendental K (algebraMap F Q (algebraMap (RatFunc k) F RatFunc.X)) :=
    transcendental_algebraMap_of_isFractionRing_tensorProduct (k := k) hx
  let _ : Algebra (RatFunc K) Q := ratFuncAlgebraOfTranscendental hxQ
  have _ : IsScalarTower K (RatFunc K) Q := isScalarTower_ratFuncAlgebraOfTranscendental hxQ
  have hXF : algebraMap F Q (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc K) Q RatFunc.X :=
    (algebraMap_ratFuncAlgebraOfTranscendental_X hxQ).symm
  exact (fractionFieldRatFuncTensorEquiv (F' := Q) hX hXF).toRingEquiv.toMulEquiv.isField
    (Field.toIsField Q)

omit [Algebra.IsAlgebraic (RatFunc k) F] in
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
    transcendental_algebraMap_of_isFractionRing_tensorProduct (k := k) hx
  let _ : Algebra (RatFunc K) Q := ratFuncAlgebraOfTranscendental hxQ
  have _ : IsScalarTower K (RatFunc K) Q := isScalarTower_ratFuncAlgebraOfTranscendental hxQ
  have hXF : algebraMap F Q (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc K) Q RatFunc.X :=
    (algebraMap_ratFuncAlgebraOfTranscendental_X hxQ).symm
  let b := Module.Basis.ofVectorSpace (RatFunc k) F
  have hli := linearIndependent_ratFunc_of_linearDisjoint
    (linearDisjoint_of_isFractionRing_tensorProduct (k := k)) hXF b
  have hconstr : (ratFuncParameterLift (F' := Q) hX hXF).toLinearMap =
      (b.baseChange (RatFunc K)).constr (RatFunc K) (fun i ↦ algebraMap F Q (b i)) :=
    (b.baseChange (RatFunc K)).ext fun i ↦ by
      rw [Module.Basis.constr_basis]
      simp [ratFuncParameterLift, AlgHom.liftEquiv_tmul]
  have hinj : Function.Injective (ratFuncParameterLift (F' := Q) hX hXF) := by
    have : Function.Injective (ratFuncParameterLift (F' := Q) hX hXF).toLinearMap := by
      rw [hconstr]
      exact (b.baseChange (RatFunc K)).injective_constr_of_linearIndependent hli
    exact this
  exact Function.Injective.isDomain (ratFuncParameterLift (F' := Q) hX hXF).toRingHom hinj

end RatFuncTensorIsField

end FractionField

end TauCeti

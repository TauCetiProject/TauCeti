/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Complex.Module
public import TauCeti.Analysis.CStarAlgebra.State.Space
public import TauCeti.Analysis.Normed.Order.OrderUnit.StateSpace

/-!
# C⋆-algebra states and order-unit states

For a unital C⋆-algebra `A` equipped with a compatible star order (`PartialOrder A` and
`StarOrderedRing A`), the C⋆-algebra state space `TauCeti.stateSpace A` is weak-* homeomorphic
to the real order-unit state space `TauCeti.OrderUnit.stateSpace (1 : selfAdjoint A)` via
restriction to `selfAdjoint A` and unique complex-linear extension along the Cartesian
decomposition `a = ℜ a + I • ℑ a`.

## Main definitions

* `TauCeti.OrderUnit.cstarStateSpaceHomeomorph`: the weak-* homeomorphism
  `TauCeti.stateSpace A ≃ₜ TauCeti.OrderUnit.stateSpace (1 : selfAdjoint A)`.

## Main results

* `TauCeti.OrderUnit.cstarStateSpaceHomeomorph_pullback`,
  `TauCeti.OrderUnit.cstarStateSpaceHomeomorph_symm_pullback`: naturality of the dictionary
  with respect to pulling back states along a unital star homomorphism and its real restriction
  to self-adjoint parts.

## References

* R. V. Kadison, *A representation theory for commutative topological algebra*, Mem. Amer. Math.
  Soc. **7** (1951).
* M. A. Rieffel, *Metrics on state spaces*, Doc. Math. **4** (1999), 559–600, §1.
-/

public section

noncomputable section

open Set Topology
open scoped ComplexOrder ComplexStarModule

namespace TauCeti

namespace OrderUnit

section CStarStates

variable (A : Type*) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

private theorem ofReal_re_apply_of_mem_stateSpace {ψ : WeakDual ℂ A}
    (hψ : ψ ∈ TauCeti.stateSpace A) {a : A} (ha : IsSelfAdjoint a) :
    ((ψ a).re : ℂ) = ψ a := by
  have him : (ψ a).im = 0 := by
    simpa using RCLike.conj_eq_iff_im.1 (isSelfAdjoint_apply_of_mem_stateSpace hψ ha).star_eq
  exact Complex.ext rfl him.symm

private def cstarStateRestrict (ψ : TauCeti.stateSpace A) :
    OrderUnit.stateSpace (1 : selfAdjoint A) :=
  let f : selfAdjoint A →L[ℝ] ℝ :=
    { toFun := fun a => (ψ.val a).re
      map_add' := fun a b => by simp
      map_smul' := fun r a => by
        simp [selfAdjoint.val_smul, ← Complex.coe_smul]
      cont := Complex.continuous_re.comp ((WeakDual.toStrongDual ψ.val).continuous.comp
        continuous_subtypeVal) }
  -- Local helper lemma unfolding the evaluation of the local `ContinuousLinearMap` literal `f`.
  have hf (x : selfAdjoint A) : f x = (ψ.val x).re := rfl
  ⟨StrongDual.toWeakDual f,
    OrderUnit.mem_stateSpace_iff.2 ⟨fun a b hab => by
      have hle : ψ.val (a : A) ≤ ψ.val (b : A) :=
        WeakDual.monotone_toStrongDual_of_map_nonneg
          (fun _ => TauCeti.map_nonneg_of_mem_stateSpace ψ.property) hab
      rw [← ofReal_re_apply_of_mem_stateSpace A ψ.property a.property,
        ← ofReal_re_apply_of_mem_stateSpace A ψ.property b.property, Complex.real_le_real] at hle
      simpa [hf] using hle,
    by simp [hf, TauCeti.map_one_of_mem_stateSpace ψ.property]⟩⟩

private theorem cstarStateRestrict_apply (ψ : TauCeti.stateSpace A) (a : selfAdjoint A) :
    (cstarStateRestrict A ψ).val a = (ψ.val a).re := (rfl)

private def cstarStateExtend (φ : OrderUnit.stateSpace (1 : selfAdjoint A)) :
    TauCeti.stateSpace A :=
  let g : A →L[ℂ] ℂ :=
    { toFun := fun a => (φ.val (ℜ a) : ℂ) + Complex.I * (φ.val (ℑ a) : ℂ)
      map_add' := fun a b => by simp [map_add]; ring
      map_smul' := fun z a => by
        have hre : φ.val (ℜ (z • a)) = z.re * φ.val (ℜ a) - z.im * φ.val (ℑ a) := by
          simp [realPart_smul, map_sub, map_smul]
        have him : φ.val (ℑ (z • a)) = z.re * φ.val (ℑ a) + z.im * φ.val (ℜ a) := by
          simp [imaginaryPart_smul, map_add, map_smul]
        apply Complex.ext <;> simp [hre, him]
      cont :=
        have hre : Continuous (fun a : A => ℜ a) := Continuous.subtype_mk (by fun_prop) _
        have him : Continuous (fun a : A => ℑ a) :=
          Continuous.subtype_mk (by simp only [skewAdjointPart_apply_coe]; fun_prop) _
        (Complex.continuous_ofReal.comp ((WeakDual.toStrongDual φ.val).continuous.comp hre)).add
          (continuous_const.mul (Complex.continuous_ofReal.comp
            ((WeakDual.toStrongDual φ.val).continuous.comp him))) }
  -- Local helper lemma unfolding the evaluation of the local `ContinuousLinearMap` literal `g`.
  have hg (x : A) : g x = (φ.val (ℜ x) : ℂ) + Complex.I * (φ.val (ℑ x) : ℂ) := rfl
  ⟨StrongDual.toWeakDual g,
    TauCeti.mem_stateSpace_iff_map_one.mpr ⟨fun a ha => by
      have hsa : IsSelfAdjoint a := ha.isSelfAdjoint
      have him : ℑ a = 0 := hsa.imaginaryPart
      have hre : 0 ≤ ℜ a := by
        rw [← Subtype.coe_le_coe, hsa.coe_realPart, ZeroMemClass.coe_zero]
        exact ha
      have hre_nonneg : 0 ≤ φ.val (ℜ a) := map_nonneg_of_mem_stateSpace φ.property hre
      simpa [hg, him, Complex.le_def] using hre_nonneg,
    by
      have hre : ℜ (1 : A) = (1 : selfAdjoint A) :=
        selfAdjoint.realPart_coe (x := (1 : selfAdjoint A))
      have him : ℑ (1 : A) = 0 := selfAdjoint.imaginaryPart_coe (x := (1 : selfAdjoint A))
      simp [hg, hre, him, OrderUnit.apply_eq_one_of_mem_stateSpace φ.property]⟩⟩

private theorem cstarStateExtend_apply (φ : OrderUnit.stateSpace (1 : selfAdjoint A)) (a : A) :
    (cstarStateExtend A φ).val a = (φ.val (ℜ a) : ℂ) + Complex.I * (φ.val (ℑ a) : ℂ) := (rfl)

/-- Restriction to `selfAdjoint A` and unique complex-linear extension via `a = ℜ a + I • ℑ a`
form a weak-* homeomorphism between the C⋆-states `TauCeti.stateSpace A` of a unital
C⋆-algebra `A` (equipped with a compatible star order, supplied as `PartialOrder A` and
`StarOrderedRing A`) and the real order-unit states
`TauCeti.OrderUnit.stateSpace (1 : selfAdjoint A)`. -/
def cstarStateSpaceHomeomorph :
    TauCeti.stateSpace A ≃ₜ OrderUnit.stateSpace (1 : selfAdjoint A) where
  toFun := cstarStateRestrict A
  invFun := cstarStateExtend A
  left_inv ψ := by
    apply Subtype.ext
    apply DFunLike.ext
    intro a
    have hdecomp : ψ.val a = ψ.val (ℜ a) + Complex.I * ψ.val (ℑ a) := by
      simpa only [map_add, map_smul, smul_eq_mul] using
        congrArg ψ.val (realPart_add_I_smul_imaginaryPart a).symm
    simp only [cstarStateExtend_apply, cstarStateRestrict_apply,
      ofReal_re_apply_of_mem_stateSpace A ψ.property (ℜ a).property,
      ofReal_re_apply_of_mem_stateSpace A ψ.property (ℑ a).property, hdecomp]
  right_inv φ := by
    apply Subtype.ext
    apply DFunLike.ext
    intro a
    simp only [cstarStateRestrict_apply, cstarStateExtend_apply, selfAdjoint.realPart_coe,
      selfAdjoint.imaginaryPart_coe, map_zero, Complex.ofReal_zero, mul_zero, add_zero,
      Complex.ofReal_re]
  continuous_toFun := continuous_induced_rng.mpr <|
    WeakDual.continuous_of_continuous_eval fun a => by
      simpa only [Function.comp_def, cstarStateRestrict_apply] using
        Complex.continuous_re.comp ((WeakDual.eval_continuous (a : A)).comp continuous_subtypeVal)
  continuous_invFun := continuous_induced_rng.mpr <|
    WeakDual.continuous_of_continuous_eval fun a => by
      simpa only [Function.comp_def, Pi.add_def, Pi.mul_def, cstarStateExtend_apply] using
        (Complex.continuous_ofReal.comp (continuous_eval_stateSpace (ℜ a))).add
          (continuous_const.mul (Complex.continuous_ofReal.comp
            (continuous_eval_stateSpace (ℑ a))))

@[simp]
theorem cstarStateSpaceHomeomorph_apply (ψ : TauCeti.stateSpace A) (a : selfAdjoint A) :
    (cstarStateSpaceHomeomorph A ψ).val a = (ψ.val a).re :=
  cstarStateRestrict_apply A ψ a

@[simp]
theorem cstarStateSpaceHomeomorph_symm_apply (φ : OrderUnit.stateSpace (1 : selfAdjoint A))
    (a : A) :
    ((cstarStateSpaceHomeomorph A).symm φ).val a =
      (φ.val (ℜ a) : ℂ) + Complex.I * (φ.val (ℑ a) : ℂ) :=
  cstarStateExtend_apply A φ a

/-- **Naturality of the C⋆/order-unit state dictionary:** `cstarStateSpaceHomeomorph` commutes
with pulling back states along a unital star homomorphism `f : A → B` and its real restriction
`T : selfAdjoint A →L[ℝ] selfAdjoint B`. -/
theorem cstarStateSpaceHomeomorph_pullback {B F : Type*} [CStarAlgebra B] [PartialOrder B]
    [StarOrderedRing B] [FunLike F A B] [AlgHomClass F ℂ A B] [StarHomClass F A B]
    (f : F) (T : selfAdjoint A →L[ℝ] selfAdjoint B)
    (hTf : ∀ a : selfAdjoint A, (T a : B) = f a) (ψ : TauCeti.stateSpace B) :
    cstarStateSpaceHomeomorph A
        ⟨pullbackFunctional A f ψ.val,
          (by exact mapsTo_pullbackFunctional_stateSpace f ψ.property)⟩ =
      OrderUnit.statePullback T
        (by
          intro a b hab
          simpa only [← Subtype.coe_le_coe, hTf] using
            OrderHomClass.mono f (Subtype.coe_le_coe.mpr hab))
        (by exact Subtype.ext (by simp only [hTf, selfAdjoint.val_one, map_one]))
        (cstarStateSpaceHomeomorph B ψ) := by
  refine Subtype.ext <| DFunLike.ext _ _ fun a => ?_
  rw [cstarStateSpaceHomeomorph_apply, OrderUnit.statePullback_apply,
    cstarStateSpaceHomeomorph_apply, hTf]
  simp [pullbackFunctional_apply]

/-- Inverse form of `cstarStateSpaceHomeomorph_pullback`: `(cstarStateSpaceHomeomorph _).symm`
intertwines `OrderUnit.statePullback` along the real restriction `T` with `pullbackFunctional`
along `f`. -/
theorem cstarStateSpaceHomeomorph_symm_pullback {B F : Type*} [CStarAlgebra B] [PartialOrder B]
    [StarOrderedRing B] [FunLike F A B] [AlgHomClass F ℂ A B] [StarHomClass F A B]
    (f : F) (T : selfAdjoint A →L[ℝ] selfAdjoint B)
    (hTf : ∀ a : selfAdjoint A, (T a : B) = f a)
    (φ : OrderUnit.stateSpace (1 : selfAdjoint B)) :
    (cstarStateSpaceHomeomorph A).symm
        (OrderUnit.statePullback T
          (by
            intro a b hab
            simpa only [← Subtype.coe_le_coe, hTf] using
              OrderHomClass.mono f (Subtype.coe_le_coe.mpr hab))
          (by exact Subtype.ext (by simp only [hTf, selfAdjoint.val_one, map_one])) φ) =
      ⟨pullbackFunctional A f ((cstarStateSpaceHomeomorph B).symm φ).val,
        (by
          exact mapsTo_pullbackFunctional_stateSpace f
            ((cstarStateSpaceHomeomorph B).symm φ).property)⟩ := by
  symm
  rw [(cstarStateSpaceHomeomorph A).eq_symm_apply]
  simpa using cstarStateSpaceHomeomorph_pullback A f T hTf
    ((cstarStateSpaceHomeomorph B).symm φ)

end CStarStates

end OrderUnit

end TauCeti

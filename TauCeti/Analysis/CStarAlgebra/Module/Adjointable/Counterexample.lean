/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Module.Adjointable
import Mathlib.Topology.ContinuousMap.ContinuousSqrt
import Mathlib.Topology.UnitInterval
import TauCeti.Analysis.CStarAlgebra.Module.Self

/-!
# A bounded module map that is not adjointable

Unlike on Hilbert spaces, a bounded `A`-linear operator between complete Hilbert C⋆-modules over a
C⋆-algebra `A` need not admit an adjoint. This file verifies the standard counterexample: in
`A = C([0, 1], ℂ)` viewed as a right Hilbert `A`-module over itself, the inclusion of the closed
maximal ideal `J = {f ∈ C([0, 1], ℂ) | f 0 = 0}` into `A` is bounded and `A`-linear, yet admits no
adjoint.

## Main declarations

* `TauCeti.AdjointableMap.exists_continuousLinearMap_smul_not_adjointable`: there exist complete
  right Hilbert modules over a unital C⋆-algebra and a bounded module map between them with no
  adjoint.

## References

* E. Christopher Lance, *Hilbert C⋆-Modules: A Toolkit for Operator Algebraists*, Chapter 1.
* Iain Raeburn and Dana P. Williams, *Morita Equivalence and Continuous-Trace C⋆-Algebras*,
  Chapter 2.
-/

public section

open MulOpposite unitInterval
open scoped ComplexOrder

namespace TauCeti

namespace AdjointableMap

/-- A bounded `A`-linear map between complete right Hilbert `A`-modules over a unital C⋆-algebra
`A` need not be adjointable. -/
theorem exists_continuousLinearMap_smul_not_adjointable :
    ∃ (A E F : Type) (_ : CStarAlgebra A) (_ : PartialOrder A) (_ : StarOrderedRing A)
      (_ : NormedAddCommGroup E) (_ : NormedSpace ℂ E) (_ : CompleteSpace E)
      (_ : SMul Aᵐᵒᵖ E) (_ : CStarModule Aᵐᵒᵖ E)
      (_ : NormedAddCommGroup F) (_ : NormedSpace ℂ F) (_ : CompleteSpace F)
      (_ : SMul Aᵐᵒᵖ F) (_ : CStarModule Aᵐᵒᵖ F)
      (T : E →L[ℂ] F),
      (∀ (a : A) (x : E), T (op a • x) = op a • T x) ∧
      ¬∃ T' : AdjointableMap Aᵐᵒᵖ E F, ⇑T' = ⇑T := by
  let J : Submodule ℂ C(I, ℂ) := (ContinuousMap.evalCLM ℂ (0 : I)).ker
  let _ : SMul C(I, ℂ)ᵐᵒᵖ J :=
    { smul a f := ⟨op (unop a) • f.val, by
        have hf : f.val 0 = 0 := f.property
        simp [J, MulOpposite.smul_eq_mul_unop, hf]⟩ }
  let _ : CStarModule C(I, ℂ)ᵐᵒᵖ J :=
    { inner f g := inner C(I, ℂ)ᵐᵒᵖ f.val g.val
      inner_add_right {x _ _} := CStarModule.inner_add_right (A := C(I, ℂ)ᵐᵒᵖ) (x := x.val)
      inner_self_nonneg {x} := CStarModule.inner_self_nonneg (A := C(I, ℂ)ᵐᵒᵖ) (x := x.val)
      inner_self {x} :=
        (CStarModule.inner_self (A := C(I, ℂ)ᵐᵒᵖ) (x := x.val)).trans Submodule.coe_eq_zero
      inner_op_smul_right {a x y} :=
        CStarModule.inner_op_smul_right (A := C(I, ℂ)ᵐᵒᵖ) (a := a) (x := x.val) (y := y.val)
      inner_smul_right_complex {z x y} :=
        CStarModule.inner_smul_right_complex (A := C(I, ℂ)ᵐᵒᵖ) (z := z) (x := x.val) (y := y.val)
      star_inner x y := CStarModule.star_inner (A := C(I, ℂ)ᵐᵒᵖ) x.val y.val
      norm_eq_sqrt_norm_inner_self {x} :=
        CStarModule.norm_eq_sqrt_norm_inner_self (A := C(I, ℂ)ᵐᵒᵖ) x.val }
  refine ⟨C(I, ℂ), J, C(I, ℂ), inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    J.subtypeL, fun _ _ => rfl, ?_⟩
  rintro ⟨T', hT'⟩
  let coord : J :=
    ⟨⟨fun t : I => ((t : ℝ) : ℂ), Complex.continuous_ofReal.comp continuous_subtypeVal⟩,
      by simp [J]⟩
  let s1 : J := T'.adjoint 1
  have hid : unop (inner C(I, ℂ)ᵐᵒᵖ (T' coord) (1 : C(I, ℂ))) =
      unop (inner C(I, ℂ)ᵐᵒᵖ coord s1) :=
    (T'.unop_adjoint_inner_right coord 1).symm
  rw [congrFun hT' coord] at hid
  have hs1_pos : ∀ t ∈ Set.Ioc (0 : I) 1, s1.val t = 1 := fun t ht => by
    have hval := DFunLike.congr_fun hid t
    have hcoord_inner : unop (inner C(I, ℂ)ᵐᵒᵖ coord s1) = star coord.val * s1.val := rfl
    rw [hcoord_inner] at hval
    simp only [CStarModule.unop_inner_mulOpposite, Submodule.coe_subtypeL, Submodule.subtype_apply,
      ContinuousMap.mul_apply, ContinuousMap.star_apply, ContinuousMap.one_apply,
      ContinuousMap.coe_mk, coord] at hval
    have htpos : (0 : ℝ) < (t : ℝ) := ht.1
    have hne : star (((t : ℝ) : ℂ)) ≠ 0 := star_ne_zero.mpr (Complex.ofReal_ne_zero.mpr htpos.ne')
    exact (mul_right_inj' hne).mp hval.symm
  have hclosed : IsClosed {t : I | s1.val t = 1} := isClosed_eq s1.val.continuous continuous_const
  have h0_mem : (0 : I) ∈ closure (Set.Ioc (0 : I) 1) := by
    rw [closure_Ioc (zero_ne_one : (0 : I) ≠ 1)]
    exact Set.left_mem_Icc.mpr zero_le_one
  have hs1_zero_one : s1.val 0 = 1 := hclosed.closure_subset_iff.mpr hs1_pos h0_mem
  have hs1_zero : s1.val 0 = 0 := s1.property
  exact one_ne_zero (hs1_zero_one.symm.trans hs1_zero)

end AdjointableMap

end TauCeti

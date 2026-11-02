/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Continuous
public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho

/-!
# The Gram-Schmidt process: diagonal coefficients and continuity

Mathlib's `InnerProductSpace.gramSchmidt_triangular` records that, in the basis `b` it is fed,
`gramSchmidt 𝕜 b i` has no component along `b j` for `i < j`.  This file supplies the diagonal
companion: the component along `b i` itself is `1`, because the Gram-Schmidt step subtracts from
`b i` only vectors spanned by the earlier basis vectors.  Together the two say that the matrix of
the Gram-Schmidt process is lower unitriangular.

The file also proves that the Gram-Schmidt process, normalized or not, depends continuously on its
input at every linearly independent family. Linear independence keeps every denominator
`‖gramSchmidt 𝕜 f i‖ ^ 2` of the recursive formula `gramSchmidt_def''` away from zero, so
continuity follows by well-founded induction on the index. This is what makes orthonormalization
a continuous retraction of linearly independent frames onto orthonormal ones. The induction is the
fixed-space form of the sectionwise argument of Patrick Massot and Michael Rothgang in Mathlib PR
[#26221](https://github.com/leanprover-community/mathlib4/pull/26221), which
`ContinuousWithinAt.gramSchmidt_bundle` adapts to continuous Riemannian vector bundles.

## Main results

* `Module.Basis.repr_gramSchmidt_self_eq_one` — the Gram-Schmidt process leaves the coefficient of a
  basis vector along itself equal to `1`.
* `ContinuousWithinAt.gramSchmidt`, `ContinuousWithinAt.gramSchmidtNormed` — Gram-Schmidt applied to
  a family of vectors depending continuously on a parameter is continuous at every parameter where
  the family is linearly independent, with `ContinuousAt`, `ContinuousOn` and `Continuous`
  variants for the normalized process.
-/

public section

open Finset InnerProductSpace Module Topology

namespace TauCeti

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {ι : Type*} [LinearOrder ι] [LocallyFiniteOrderBot ι]

/-- The Gram-Schmidt process does not change the coefficient of a basis vector along itself:
`gramSchmidt 𝕜 b i` differs from `b i` by a combination of the strictly earlier `gramSchmidt`
vectors, each of which has no component along `b i`. -/
@[simp]
theorem _root_.Module.Basis.repr_gramSchmidt_self_eq_one (b : Basis ι 𝕜 E) (i : ι) :
    b.repr (gramSchmidt 𝕜 b i) i = 1 := by
  have h := congrArg (fun x ↦ b.repr x i) (gramSchmidt_def'' 𝕜 (b : ι → E) i)
  simp only [Basis.repr_self, Finsupp.single_eq_same, map_add, map_sum, map_smul,
    Finsupp.add_apply, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply,
    smul_eq_mul] at h
  rw [Finset.sum_eq_zero (fun j hj ↦ ?_), add_zero] at h
  · exact h.symm
  · rw [gramSchmidt_triangular (Finset.mem_Iio.mp hj) b, mul_zero]

end TauCeti

section Continuity

open scoped InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {ι : Type*} [LinearOrder ι] [LocallyFiniteOrderBot ι]
variable {X : Type*} [TopologicalSpace X] {v : ι → X → E} {s : Set X} {x : X}

attribute [local instance] IsWellOrder.toHasWellFounded

/-- The Gram-Schmidt process applied to a continuously varying family of vectors is continuous at
every parameter where the family is linearly independent. -/
theorem ContinuousWithinAt.gramSchmidt (hv : ∀ i, ContinuousWithinAt (v i) s x)
    (hli : LinearIndependent 𝕜 (fun i ↦ v i x)) (n : ι) :
    ContinuousWithinAt (fun y ↦ InnerProductSpace.gramSchmidt 𝕜 (fun i ↦ v i y) n) s x := by
  induction n using WellFoundedLT.induction with
  | ind n ih =>
    -- Unfold one step of the recursion `gramSchmidt_def''`.
    have hformula (y : X) : InnerProductSpace.gramSchmidt 𝕜 (fun i ↦ v i y) n =
        v n y - ∑ i ∈ Iio n,
          (⟪InnerProductSpace.gramSchmidt 𝕜 (fun j ↦ v j y) i, v n y⟫_𝕜 /
            (‖InnerProductSpace.gramSchmidt 𝕜 (fun j ↦ v j y) i‖ : 𝕜) ^ 2) •
              InnerProductSpace.gramSchmidt 𝕜 (fun j ↦ v j y) i :=
      eq_sub_of_add_eq (InnerProductSpace.gramSchmidt_def'' 𝕜 (fun i ↦ v i y) n).symm
    simp only [hformula]
    refine (hv n).sub <| tendsto_finsetSum _ fun i hi ↦ ?_
    have hi := mem_Iio.mp hi
    have hnorm : ContinuousWithinAt
        (fun y ↦ ((‖InnerProductSpace.gramSchmidt 𝕜 (fun j ↦ v j y) i‖ : ℝ) : 𝕜)) s x :=
      RCLike.continuous_ofReal.continuousAt.comp_continuousWithinAt (ih i hi).norm
    exact (((ih i hi).inner (hv n)).div (hnorm.pow 2) (pow_ne_zero 2 <| RCLike.ofReal_ne_zero.2 <|
      norm_ne_zero_iff.2 <| InnerProductSpace.gramSchmidt_ne_zero i hli)).smul (ih i hi)

/-- The normalized Gram-Schmidt process applied to a continuously varying family of vectors is
continuous at every parameter where the family is linearly independent. -/
theorem ContinuousWithinAt.gramSchmidtNormed (hv : ∀ i, ContinuousWithinAt (v i) s x)
    (hli : LinearIndependent 𝕜 (fun i ↦ v i x)) (n : ι) :
    ContinuousWithinAt (fun y ↦ InnerProductSpace.gramSchmidtNormed 𝕜 (fun i ↦ v i y) n) s x := by
  have hg := ContinuousWithinAt.gramSchmidt hv hli n
  have hnorm : ContinuousWithinAt
      (fun y ↦ ((‖InnerProductSpace.gramSchmidt 𝕜 (fun i ↦ v i y) n‖ : ℝ) : 𝕜)) s x :=
    RCLike.continuous_ofReal.continuousAt.comp_continuousWithinAt hg.norm
  exact (hnorm.inv₀ <| RCLike.ofReal_ne_zero.2 <| norm_ne_zero_iff.2 <|
    InnerProductSpace.gramSchmidt_ne_zero n hli).smul hg

/-- The normalized Gram-Schmidt process applied to a continuously varying family of vectors is
continuous at every parameter where the family is linearly independent. -/
theorem ContinuousAt.gramSchmidtNormed (hv : ∀ i, ContinuousAt (v i) x)
    (hli : LinearIndependent 𝕜 (fun i ↦ v i x)) (n : ι) :
    ContinuousAt (fun y ↦ InnerProductSpace.gramSchmidtNormed 𝕜 (fun i ↦ v i y) n) x := by
  simp only [← continuousWithinAt_univ] at hv ⊢
  exact ContinuousWithinAt.gramSchmidtNormed hv hli n

/-- The normalized Gram-Schmidt process preserves continuity on a set where the input family is
linearly independent. -/
theorem ContinuousOn.gramSchmidtNormed (hv : ∀ i, ContinuousOn (v i) s)
    (hli : ∀ y ∈ s, LinearIndependent 𝕜 (fun i ↦ v i y)) (n : ι) :
    ContinuousOn (fun y ↦ InnerProductSpace.gramSchmidtNormed 𝕜 (fun i ↦ v i y) n) s :=
  fun y hy ↦ ContinuousWithinAt.gramSchmidtNormed (fun i ↦ hv i y hy) (hli y hy) n

/-- The normalized Gram-Schmidt process preserves a continuous family of linearly independent
vectors. -/
theorem Continuous.gramSchmidtNormed (hv : ∀ i, Continuous (v i))
    (hli : ∀ y, LinearIndependent 𝕜 (fun i ↦ v i y)) (n : ι) :
    Continuous (fun y ↦ InnerProductSpace.gramSchmidtNormed 𝕜 (fun i ↦ v i y) n) := by
  simp only [← continuousOn_univ] at hv ⊢
  exact ContinuousOn.gramSchmidtNormed hv (fun y _ ↦ hli y) n

end Continuity

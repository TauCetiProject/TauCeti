/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Homotopy
public import TauCeti.CategoryTheory.Exact.Acyclic
public import TauCeti.CategoryTheory.Exact.Projective
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift

/-!
# Maps from complexes of projectives to acyclic complexes

Let `E` be an exact structure. A map `φ : P ⟶ A` from a bounded above complex of `E`-projective
objects to an `E`-acyclic complex is null-homotopic (Bühler, Corollary 12.5). This is the dual of
`TauCeti.ExactStructure.AcyclicData.homotopyZero`.

The null-homotopy `hⁿ : Pⁿ⁺¹ ⟶ Aⁿ` is built downwards from the upper bound of `P`. Write the
differentials of `A` as `Aⁿ ↠ Zⁿ⁺¹ ↣ Aⁿ⁺¹`. If `φⁿ⁺¹ - d ≫ hⁿ⁺¹` vanishes after `Aⁿ⁺¹ ↠ Zⁿ⁺²`, it
lands in `Zⁿ⁺¹ ↣ Aⁿ⁺¹`, and its lift along `Aⁿ ↠ Zⁿ⁺¹`, out of the projective `Pⁿ⁺¹`, is `hⁿ`; the
next correction `φⁿ - d ≫ hⁿ` again vanishes after `Aⁿ ↠ Zⁿ⁺¹`, since `Zⁿ⁺¹ ↣ Aⁿ⁺¹` is a
monomorphism.

## Main definitions

* `TauCeti.ExactStructure.AcyclicData.homotopyStepDown`: one step of a null-homotopy out of a
  projective term, with `homotopyStepDown_comp_d` and `sub_d_comp_homotopyStepDown_comp_p`.
* `TauCeti.ExactStructure.AcyclicData.homotopyZeroOfProjective`: the null-homotopy, for `P`
  strictly bounded above at `0`.

## Main results

* `TauCeti.ExactStructure.AcyclicData.quotient_map_eq_zero_of_projective`: a map from a bounded
  above complex of projectives to an acyclic complex vanishes in the homotopy category.

## References

* Theo Bühler, *Exact categories*, Expositiones Mathematicae **28** (2010), 1--69,
  <https://arxiv.org/abs/0811.1480>, Corollary 12.5.
-/

public section

namespace TauCeti.ExactStructure

open CategoryTheory CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
  {E : ExactStructure C}

namespace AcyclicData

variable {P A : CochainComplex C ℤ} (hA : E.AcyclicData A) (φ : P ⟶ A)

section homotopyStepDown

variable {n : ℤ} (hP : E.isProjective (P.X (n + 1))) (h : P.X (n + 1 + 1) ⟶ A.X (n + 1))
  (hh : (φ.f (n + 1) - P.d (n + 1) (n + 1 + 1) ≫ h) ≫ hA.p (n + 1) = 0)

/-- **One step of a null-homotopy out of a projective object.** Let `h : Pⁿ⁺² ⟶ Aⁿ⁺¹` be a
component such that the correction `φⁿ⁺¹ - d ≫ h` vanishes after `Aⁿ⁺¹ ↠ Zⁿ⁺²`. The correction
then lands in the cycles `Zⁿ⁺¹ ↣ Aⁿ⁺¹`, and its lift along `Aⁿ ↠ Zⁿ⁺¹`, out of the projective
`Pⁿ⁺¹`, is the next component `Pⁿ⁺¹ ⟶ Aⁿ`. -/
noncomputable def homotopyStepDown : P.X (n + 1) ⟶ A.X n :=
  hP.factorThru (E.isDeflation_g (hA.conflation n)) (hA.liftZ (n + 1) _ hh)

/-- The homotopy identity of a step: `d ≫ hⁿ⁺¹ + hⁿ ≫ d = φⁿ⁺¹`. -/
@[reassoc]
theorem homotopyStepDown_comp_d :
    hA.homotopyStepDown φ hP h hh ≫ A.d n (n + 1) = φ.f (n + 1) - P.d (n + 1) (n + 1 + 1) ≫ h := by
  rw [← hA.fac, ← Category.assoc, homotopyStepDown, hP.factorThru_comp, liftZ_i]

/-- The next correction `φⁿ - d ≫ hⁿ` again vanishes after `Aⁿ ↠ Zⁿ⁺¹`, so the step can be
repeated. -/
theorem sub_d_comp_homotopyStepDown_comp_p :
    (φ.f n - P.d n (n + 1) ≫ hA.homotopyStepDown φ hP h hh) ≫ hA.p n = 0 := by
  rw [← cancel_mono (hA.i (n + 1)), zero_comp, Category.assoc, hA.fac, Preadditive.sub_comp,
    φ.comm, Category.assoc, homotopyStepDown_comp_d, Preadditive.comp_sub,
    HomologicalComplex.d_comp_d_assoc, zero_comp, sub_zero, sub_self]

end homotopyStepDown

variable (hP : ∀ n, E.isProjective (P.X n))

variable [P.IsStrictlyLE 0]

/-- The start of the recursion: the correction `φ⁰ - d ≫ 0` vanishes after `A⁰ ↠ Z¹`, since
`P¹ = 0`. -/
private theorem sub_comp_p_eq_zero_zero :
    (φ.f (Int.negSucc 0 + 1) - P.d (Int.negSucc 0 + 1) (Int.negSucc 0 + 1 + 1) ≫ 0) ≫
      hA.p (Int.negSucc 0 + 1) = 0 := by
  rw [comp_zero, sub_zero, ← cancel_mono (hA.i (Int.negSucc 0 + 1 + 1)), zero_comp,
    Category.assoc, hA.fac, φ.comm,
    (P.isZero_of_isStrictlyLE 0 (Int.negSucc 0 + 1 + 1) (by decide)).eq_of_tgt
      (P.d (Int.negSucc 0 + 1) (Int.negSucc 0 + 1 + 1)) 0, zero_comp]

include hP in
/-- The components `Pⁿ⁺¹ ⟶ Aⁿ` of the null-homotopy in negative degrees `n`, by repeated
`homotopyStepDown`s from the zero component `P¹ ⟶ A⁰`. -/
private noncomputable def homNeg : ∀ k : ℕ,
    { h : P.X (Int.negSucc k + 1) ⟶ A.X (Int.negSucc k) //
      (φ.f (Int.negSucc k) - P.d (Int.negSucc k) (Int.negSucc k + 1) ≫ h) ≫
        hA.p (Int.negSucc k) = 0 }
  | 0 => ⟨hA.homotopyStepDown (n := Int.negSucc 0) φ (hP _) 0 (sub_comp_p_eq_zero_zero hA φ),
      hA.sub_d_comp_homotopyStepDown_comp_p (n := Int.negSucc 0) φ (hP _) 0
        (sub_comp_p_eq_zero_zero hA φ)⟩
  | k + 1 => ⟨hA.homotopyStepDown (n := Int.negSucc (k + 1)) φ (hP _) (homNeg k).1 (homNeg k).2,
      hA.sub_d_comp_homotopyStepDown_comp_p (n := Int.negSucc (k + 1)) φ (hP _) (homNeg k).1
        (homNeg k).2⟩

/-- The components `Pⁿ⁺¹ ⟶ Aⁿ` of the null-homotopy: zero in nonnegative degrees, where
`Pⁿ⁺¹ = 0`. -/
private noncomputable def homotopyHom : ∀ n : ℤ, P.X (n + 1) ⟶ A.X n
  | Int.ofNat _ => 0
  | Int.negSucc k => (homNeg hA φ hP k).1

private theorem comm_ofNat (k : ℕ) :
    φ.f (Int.ofNat k + 1) = P.d (Int.ofNat k + 1) (Int.ofNat k + 1 + 1) ≫
      homotopyHom hA φ hP (Int.ofNat k + 1) +
        homotopyHom hA φ hP (Int.ofNat k) ≫ A.d (Int.ofNat k) (Int.ofNat k + 1) :=
  (P.isZero_of_isStrictlyLE 0 _ (by change (0 : ℤ) < (k : ℤ) + 1; omega)).eq_of_src _ _

private theorem comm_negSucc_zero :
    φ.f (Int.negSucc 0 + 1) = P.d (Int.negSucc 0 + 1) (Int.negSucc 0 + 1 + 1) ≫
      homotopyHom hA φ hP (Int.negSucc 0 + 1) +
        homotopyHom hA φ hP (Int.negSucc 0) ≫ A.d (Int.negSucc 0) (Int.negSucc 0 + 1) := by
  rw [← sub_eq_iff_eq_add']
  exact (hA.homotopyStepDown_comp_d (n := Int.negSucc 0) φ (hP _) 0
    (sub_comp_p_eq_zero_zero hA φ)).symm

private theorem comm_negSucc_succ (k : ℕ) :
    φ.f (Int.negSucc (k + 1) + 1) =
      P.d (Int.negSucc (k + 1) + 1) (Int.negSucc (k + 1) + 1 + 1) ≫
        homotopyHom hA φ hP (Int.negSucc (k + 1) + 1) +
          homotopyHom hA φ hP (Int.negSucc (k + 1)) ≫
            A.d (Int.negSucc (k + 1)) (Int.negSucc (k + 1) + 1) := by
  rw [← sub_eq_iff_eq_add']
  exact (hA.homotopyStepDown_comp_d (n := Int.negSucc (k + 1)) φ (hP _) _
    (homNeg hA φ hP k).2).symm

/-- **Maps from complexes of projectives to acyclic complexes are null-homotopic**: a map from a
complex of `E`-projective objects vanishing in positive degrees to an `E`-acyclic complex. -/
noncomputable def homotopyZeroOfProjective : Homotopy φ 0 :=
  Homotopy.mkCochainComplexInt φ (homotopyHom hA φ hP) fun n => by
    match n with
    | Int.ofNat k => exact comm_ofNat hA φ hP k
    | Int.negSucc 0 => exact comm_negSucc_zero hA φ hP
    | Int.negSucc (k + 1) => exact comm_negSucc_succ hA φ hP k

omit [P.IsStrictlyLE 0]

include hA hP in
/-- **Maps from bounded above complexes of projectives to acyclic complexes vanish in the
homotopy category** (Bühler, Corollary 12.5). The bound is moved to `0` by shifting. -/
theorem quotient_map_eq_zero_of_projective (n : ℤ) [P.IsStrictlyLE n] :
    (HomotopyCategory.quotient C (.up ℤ)).map φ = 0 := by
  have : (P⟦n⟧).IsStrictlyLE 0 := P.isStrictlyLE_shift n n 0 (by simp)
  have h := HomotopyCategory.eq_of_homotopy _ _
    ((hA.shift n).homotopyZeroOfProjective (φ⟦n⟧') fun k ↦ hP (k + n))
  rw [Functor.map_zero] at h
  apply (shiftFunctor (HomotopyCategory C (.up ℤ)) n).map_injective
  rw [Functor.map_zero, ← cancel_epi (((HomotopyCategory.quotient C (.up ℤ)).commShiftIso n).hom.app
    P), ← Functor.commShiftIso_hom_naturality, h, zero_comp, comp_zero]

end AcyclicData

end TauCeti.ExactStructure

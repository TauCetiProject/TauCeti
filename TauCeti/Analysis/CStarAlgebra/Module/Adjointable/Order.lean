/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Module.Adjointable.Basic

/-!
# Self-adjointness, spectral order, and positivity for adjointable operators

This file equips the C⋆-algebra `CStarModule.Adjointable A E E` of adjointable endomorphisms of a
complete Hilbert C⋆-module `E` with its spectral order (`CStarAlgebra.spectralOrder`) and
`StarOrderedRing` structure (`CStarAlgebra.spectralOrderedRing`), relating operator order to the
`A`-valued inner product:

* **Self-adjointness via the inner product**
  (`CStarModule.Adjointable.isSelfAdjoint_iff_forall_isSelfAdjoint_inner`): `IsSelfAdjoint T` iff
  `IsSelfAdjoint ⟪x, T x⟫_A` for all `x : E`, proved algebraically via complex polarization.
* **Paschke–Lance positivity theorem**
  (`CStarModule.Adjointable.nonneg_iff_forall_inner_nonneg`): `0 ≤ T` iff `0 ≤ ⟪x, T x⟫_A` for all
  `x : E`, whence `S ≤ T` iff `⟪x, S x⟫_A ≤ ⟪x, T x⟫_A` for all `x`.
* **Cross-module positivity and Paschke's bound**: for `T : Adjointable A E F`, `T* ∘ T` is
  nonnegative, `S ↦ T* ∘ S ∘ T` is monotone, and `⟪T x, T x⟫_A ≤ ‖T‖² • ⟪x, x⟫_A`.

## Main declarations

* `CStarModule.Adjointable.isSelfAdjoint_iff_forall_isSelfAdjoint_inner`
* `CStarModule.Adjointable.instPartialOrder`, `CStarModule.Adjointable.instStarOrderedRing`
* `CStarModule.Adjointable.nonneg_iff_forall_inner_nonneg`,
  `CStarModule.Adjointable.le_iff_forall_inner_le`
* `CStarModule.Adjointable.adjoint_conj_nonneg`, `CStarModule.Adjointable.adjoint_conj_mono`
* `CStarModule.Adjointable.adjoint_comp_self_le_norm_sq_smul_one`,
  `CStarModule.Adjointable.inner_map_map_le_norm_sq_smul`

## References

* E. Christopher Lance, *Hilbert C⋆-Modules: A Toolkit for Operator Algebraists*, Prop. 1.2,
  Lemma 4.1.
* William L. Paschke, *Inner product modules over B⋆-algebras*, Trans. AMS 182 (1973), Prop. 2.6.
* Iain Raeburn and Dana P. Williams, *Morita Equivalence and Continuous-Trace C⋆-Algebras*,
  Prop. 2.21.
-/

public section

open MulOpposite

namespace CStarModule

namespace Adjointable

/-! ### Self-adjointness via diagonal inner products -/

section SelfAdjoint

variable {A E : Type*}
  [NonUnitalRing A] [StarRing A] [Module ℂ A] [StarModule ℂ A] [PartialOrder A] [Norm A]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [CStarModule A E]

/-- If `T` is self-adjoint, then `⟪T x, y⟫_A = ⟪x, T y⟫_A`. -/
theorem inner_eq_right_of_isSelfAdjoint {T : Adjointable A E E} (hT : IsSelfAdjoint T) (x y : E) :
    inner A (T x) y = inner A x (T y) := by
  rw [← T.adjoint_inner_right, isSelfAdjoint_iff'.mp hT]

/-- If `T` is self-adjoint, every diagonal inner product `⟪x, T x⟫_A` is self-adjoint in `A`. -/
theorem isSelfAdjoint_inner_of_isSelfAdjoint {T : Adjointable A E E} (hT : IsSelfAdjoint T)
    (x : E) : IsSelfAdjoint (inner A x (T x)) := by
  rw [IsSelfAdjoint, star_inner, inner_eq_right_of_isSelfAdjoint hT]

/-- An adjointable endomorphism `T` is self-adjoint if and only if every diagonal inner product
`⟪x, T x⟫_A` is self-adjoint in `A`. -/
theorem isSelfAdjoint_iff_forall_isSelfAdjoint_inner {T : Adjointable A E E} :
    IsSelfAdjoint T ↔ ∀ x : E, IsSelfAdjoint (inner A x (T x)) := by
  refine ⟨fun hT x ↦ isSelfAdjoint_inner_of_isSelfAdjoint hT x, fun h ↦ isSelfAdjoint_iff'.mpr ?_⟩
  exact ext_inner_map.mp fun x ↦ by rw [adjoint_inner_right, ← star_inner, (h x).star_eq]

end SelfAdjoint

/-- Right-module form of `isSelfAdjoint_iff_forall_isSelfAdjoint_inner` for `CStarModule Bᵐᵒᵖ`. -/
theorem isSelfAdjoint_iff_forall_isSelfAdjoint_unop_inner {B E : Type*}
    [NonUnitalSeminormedRing B] [StarRing B] [Module ℂ B] [StarModule ℂ B] [PartialOrder B]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
    {T : Adjointable Bᵐᵒᵖ E E} :
    IsSelfAdjoint T ↔ ∀ x : E, IsSelfAdjoint (unop (inner Bᵐᵒᵖ x (T x))) :=
  isSelfAdjoint_iff_forall_isSelfAdjoint_inner.trans <|
    forall_congr' fun _ ↦ by rw [IsSelfAdjoint, IsSelfAdjoint, ← unop_star, unop_inj]

/-! ### Spectral order and the Paschke–Lance positivity characterization -/

section Order

variable {A E F : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] [SMul A E] [CStarModule A E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul A F] [CStarModule A F]

/-- The spectral partial order on the C⋆-algebra `Adjointable A E E`. -/
noncomputable instance instPartialOrder : PartialOrder (Adjointable A E E) :=
  CStarAlgebra.spectralOrder _

/-- `Adjointable A E E` is a `StarOrderedRing` under its spectral partial order. -/
instance instStarOrderedRing : StarOrderedRing (Adjointable A E E) :=
  CStarAlgebra.spectralOrderedRing _

/-- **Paschke–Lance positivity characterization**: an adjointable endomorphism `T` of a complete
Hilbert C⋆-module `E` is nonnegative in `Adjointable A E E` iff `0 ≤ ⟪x, T x⟫_A` for all `x`. -/
theorem nonneg_iff_forall_inner_nonneg {T : Adjointable A E E} :
    0 ≤ T ↔ ∀ x : E, 0 ≤ inner A x (T x) := by
  refine ⟨fun hT x ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨S, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hT
    rw [mul_apply, star_apply, adjoint_inner_right]
    exact inner_self_nonneg
  · have hT : IsSelfAdjoint T :=
      isSelfAdjoint_iff_forall_isSelfAdjoint_inner.mpr fun x ↦ (h x).isSelfAdjoint
    rw [CStarAlgebra.nonneg_iff_isSelfAdjoint_and_negPart_eq_zero]
    refine ⟨hT, ?_⟩
    set N : Adjointable A E E := T⁻
    have hN : 0 ≤ N := CFC.negPart_nonneg T
    set R : Adjointable A E E := CFC.sqrt N
    have hR_adj : R.adjoint = R := isSelfAdjoint_iff'.mp (CFC.sqrt_nonneg N).isSelfAdjoint
    have hRR : R * R = N := CFC.sqrt_mul_sqrt_self N hN
    have hTN : T * N = -(N * N) := by
      calc T * N = (T⁺ - N) * N := by rw [CFC.posPart_sub_negPart T hT]
        _ = T⁺ * N - N * N := sub_mul _ _ _
        _ = -(N * N) := by simp [N, CFC.posPart_mul_negPart]
    have hRN : R * N = 0 := by
      ext x
      rw [zero_apply, ← inner_self (A := A), mul_apply]
      refine le_antisymm ?_ inner_self_nonneg
      have key : inner A (R (N x)) (R (N x)) = -inner A (N x) (T (N x)) := by
        calc inner A (R (N x)) (R (N x))
            = inner A (N x) (R.adjoint (R (N x))) := (R.adjoint_inner_right _ _).symm
          _ = inner A (N x) ((R * R) (N x)) := by rw [hR_adj, mul_apply]
          _ = inner A (N x) ((N * N) x) := by rw [hRR, mul_apply]
          _ = -inner A (N x) ((-(N * N)) x) := by rw [neg_apply, inner_neg_right, neg_neg]
          _ = -inner A (N x) (T (N x)) := by rw [← hTN, mul_apply]
      exact key ▸ neg_nonpos.mpr (h (N x))
    have hNN : N.adjoint.comp N = 0 := by
      rw [isSelfAdjoint_iff'.mp hN.isSelfAdjoint, ← mul_def]
      calc N * N = R * R * N := by rw [hRR]
        _ = 0 := by rw [mul_assoc, hRN, mul_zero]
    exact adjoint_comp_self_eq_zero.mp hNN

/-- `S ≤ T` in `Adjointable A E E` iff `⟪x, S x⟫_A ≤ ⟪x, T x⟫_A` for all `x : E`. -/
theorem le_iff_forall_inner_le {S T : Adjointable A E E} :
    S ≤ T ↔ ∀ x : E, inner A x (S x) ≤ inner A x (T x) := by
  rw [← sub_nonneg, nonneg_iff_forall_inner_nonneg]
  simp only [sub_apply, inner_sub_right, sub_nonneg]

/-- For `0 ≤ T`, the square root `CFC.sqrt T` satisfies `⟪√T x, √T x⟫_A = ⟪x, T x⟫_A`. -/
theorem inner_sqrt_self {T : Adjointable A E E} (hT : 0 ≤ T) (x : E) :
    inner A (CFC.sqrt T x) (CFC.sqrt T x) = inner A x (T x) := by
  rw [← adjoint_inner_right, isSelfAdjoint_iff'.mp (CFC.sqrt_nonneg T).isSelfAdjoint, ← mul_apply,
    CFC.sqrt_mul_sqrt_self T hT]

/-! ### Cross-module positivity, congruence monotonicity, and Paschke's bound -/

/-- For `T : Adjointable A E F` (`E` complete), `0 ≤ T* ∘ T` in `Adjointable A E E`. -/
theorem adjoint_comp_self_nonneg (T : Adjointable A E F) : 0 ≤ T.adjoint.comp T :=
  nonneg_iff_forall_inner_nonneg.mpr fun _ ↦ by
    rw [comp_apply, adjoint_inner_right]; exact inner_self_nonneg

omit [CompleteSpace E] in
/-- Dual form of `adjoint_comp_self_nonneg`: when `F` is complete, `0 ≤ T ∘ T*`. -/
theorem self_comp_adjoint_nonneg [CompleteSpace F] (T : Adjointable A E F) :
    0 ≤ T.comp T.adjoint := by
  simpa only [adjoint_adjoint] using adjoint_comp_self_nonneg T.adjoint

/-- Conjugating `0 ≤ S` by `T : Adjointable A E F` gives `0 ≤ T* ∘ S ∘ T`. -/
theorem adjoint_conj_nonneg [CompleteSpace F] (T : Adjointable A E F) {S : Adjointable A F F}
    (hS : 0 ≤ S) : 0 ≤ (T.adjoint.comp S).comp T :=
  nonneg_iff_forall_inner_nonneg.mpr fun x ↦ by
    rw [comp_apply, comp_apply, adjoint_inner_right]
    exact nonneg_iff_forall_inner_nonneg.mp hS (T x)

/-- Operator-order congruence across modules: `S₁ ≤ S₂` implies `T* ∘ S₁ ∘ T ≤ T* ∘ S₂ ∘ T`. -/
theorem adjoint_conj_mono [CompleteSpace F] (T : Adjointable A E F) {S₁ S₂ : Adjointable A F F}
    (h : S₁ ≤ S₂) : (T.adjoint.comp S₁).comp T ≤ (T.adjoint.comp S₂).comp T :=
  le_iff_forall_inner_le.mpr fun x ↦ by
    rw [comp_apply, comp_apply, adjoint_inner_right, comp_apply, comp_apply, adjoint_inner_right]
    exact le_iff_forall_inner_le.mp h (T x)

/-- In `Adjointable A E E`, `T* ∘ T ≤ ‖T‖² • 1` for every `T : Adjointable A E F`. -/
theorem adjoint_comp_self_le_norm_sq_smul_one (T : Adjointable A E F) :
    T.adjoint.comp T ≤ (‖T‖ ^ 2 : ℝ) • (1 : Adjointable A E E) := by
  calc T.adjoint.comp T
      ≤ algebraMap ℝ (Adjointable A E E) ‖T.adjoint.comp T‖ :=
        (adjoint_comp_self_nonneg T).isSelfAdjoint.le_algebraMap_norm_self
    _ = (‖T‖ ^ 2 : ℝ) • (1 : Adjointable A E E) := by
      rw [Algebra.algebraMap_eq_smul_one, norm_adjoint_comp_self]

/-- **Paschke's C⋆-valued operator bound**: `⟪T x, T x⟫_A ≤ ‖T‖² • ⟪x, x⟫_A` in `A`. -/
theorem inner_map_map_le_norm_sq_smul (T : Adjointable A E F) (x : E) :
    inner A (T x) (T x) ≤ ‖T‖ ^ 2 • inner A x x := by
  have h := le_iff_forall_inner_le.mp (adjoint_comp_self_le_norm_sq_smul_one T) x
  rw [comp_apply, adjoint_inner_right] at h
  exact h.trans_eq <| by
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ), RCLike.real_smul_eq_coe_smul (K := ℂ),
      smul_apply, one_apply, inner_smul_right_complex]

end Order

section RightOrder

variable {B E F : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F]

/-- Right-module form of `nonneg_iff_forall_inner_nonneg` for `CStarModule Bᵐᵒᵖ`. -/
theorem nonneg_iff_forall_unop_inner_nonneg {T : Adjointable Bᵐᵒᵖ E E} :
    0 ≤ T ↔ ∀ x : E, 0 ≤ unop (inner Bᵐᵒᵖ x (T x)) :=
  nonneg_iff_forall_inner_nonneg.trans <| forall_congr' fun _ ↦ unop_nonneg.symm

/-- Right-module form of `le_iff_forall_inner_le` for `CStarModule Bᵐᵒᵖ`. -/
theorem le_iff_forall_unop_inner_le {S T : Adjointable Bᵐᵒᵖ E E} :
    S ≤ T ↔ ∀ x : E, unop (inner Bᵐᵒᵖ x (S x)) ≤ unop (inner Bᵐᵒᵖ x (T x)) :=
  le_iff_forall_inner_le.trans <| forall_congr' fun _ ↦ unop_le_unop.symm

/-- Right-module form of `inner_map_map_le_norm_sq_smul` for `CStarModule Bᵐᵒᵖ`. -/
theorem unop_inner_map_map_le_norm_sq_smul (T : Adjointable Bᵐᵒᵖ E F) (x : E) :
    unop (inner Bᵐᵒᵖ (T x) (T x)) ≤ ‖T‖ ^ 2 • unop (inner Bᵐᵒᵖ x x) := by
  simpa only [unop_smul] using unop_le_unop.mpr (inner_map_map_le_norm_sq_smul T x)

end RightOrder

end Adjointable

end CStarModule

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.StarProjection
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RingTheory.Finiteness.Projective
public import TauCeti.Analysis.CStarAlgebra.Module.Gram
public import TauCeti.Analysis.CStarAlgebra.Module.Self
public import TauCeti.Analysis.CStarAlgebra.Module.Unitary

import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Idempotent

/-!
# Finite Parseval frames and finitely generated projective Hilbert C⋆-modules

For a right Hilbert `A`-module `E` (represented as `CStarModule Aᵐᵒᵖ E`, with right action
`x a = MulOpposite.op a • x` and `A`-valued inner product `⟨x, y⟩_A = unop (inner Aᵐᵒᵖ x y)`), a
finite family `x : ι → E` is a *Parseval frame* (`CStarModule.IsParsevalFrame Aᵐᵒᵖ x`) if
`z = ∑ i, x i ⟨x i, z⟩_A` for every `z : E`, that is, the finite sum of the module rank-one
operators `z ↦ x i ⟨x i, z⟩_A` is the identity on `E`.

Even over a non-unital C⋆-algebra `A` and without assuming completeness of `E`, every finite family
`x : ι → E` determines an adjoint pair of bounded complex-linear maps between `E` and the finite
free module `C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)`:
* the *analysis map* `CStarModule.frameAnalysisCLM A x : E →L[ℂ] C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)`, sending `z` to
  `i ↦ ⟨x i, z⟩_A`, and
* the *synthesis map* `CStarModule.frameSynthesisCLM A x : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A) →L[ℂ] E`, sending `v`
  to `∑ i, x i (v i)`.

Their composition on `C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)` is left multiplication by the Gram matrix
`CStarMatrix.gram A x`, while their composition on `E` is `z ↦ ∑ i, x i ⟨x i, z⟩_A`. Consequently,
`x` is a Parseval frame if and only if it satisfies Parseval's identity
`∑ i, ⟨x i, z⟩_A⋆ ⟨x i, z⟩_A = ⟨z, z⟩_A` for all `z`, and if and only if `CStarMatrix.gram A x` is
a star projection and the synthesis map is surjective.

Over a unital C⋆-algebra `A`:
* A finite Parseval frame `x : ι → E` identifies `E` unitarily (`E ≃ₗᵢ[Aᵐᵒᵖ] _`) with the
  projection-cutdown module `p A^ι = LinearMap.range (CStarMatrix.mulVecLinearMap p)` for the star
  projection `p = CStarMatrix.gram A x` (`CStarModule.IsParsevalFrame.equivRangeGram`), and hence
  forces `E` to be complete (`CStarModule.IsParsevalFrame.completeSpace`), finitely generated, and
  projective. Conversely, every module unitarily isomorphic to `p A^ι` for a star projection `p`
  admits a Parseval frame with Gram matrix `p`
  (`CStarModule.exists_isParsevalFrame_and_gram_eq_of_isStarProjection`).
* **Frank–Larson / Kasparov stabilization in finite rank**
  (`CStarModule.exists_parseval_frame_iff_finite_projective`): a complete right Hilbert `A`-module
  `E` admits a finite Parseval frame if and only if `E` is finitely generated and projective as an
  algebraic right `A`-module. Completeness of `E` is essential for the reverse implication: on
  `C([0, 1], ℂ)` with `⟨a, b⟩(t) = t · star (a t) * b t`, the module is free of rank `1` over
  itself yet incomplete and admits no finite Parseval frame.
* Every algebraic finitely generated projective right `A`-module admits a complete Hilbert
  `A`-module structure (`CStarModule.exists_completeSpace_cstarModule_of_finite_projective`).
* Every right `A`-linear map out of a Hilbert `A`-module with a finite Parseval frame is
  automatically adjointable (`CStarModule.IsParsevalFrame.isAdjointPair_adjoint`), and every right
  `A`-linear equivalence `T : E ≃ₗ[Aᵐᵒᵖ] F` into a complete right Hilbert `A`-module admits an
  explicit frame-formula polar decomposition `T = U ∘ |T|` with `U : E ≃ₗᵢ[Aᵐᵒᵖ] F` unitary
  (`CStarModule.IsParsevalFrame.polarUnitary`). In particular, two complete finitely generated
  projective right Hilbert `A`-modules are unitarily isomorphic if and only if they are
  algebraically isomorphic as right `A`-modules
  (`CStarModule.nonempty_linearIsometryEquiv_iff_nonempty_linearEquiv`).

## References

* M. Frank and D. R. Larson, *Frames in Hilbert C⋆-modules and C⋆-algebras*, J. Operator Theory 48
  (2002), 273–314.
* E. C. Lance, *Hilbert C⋆-Modules: A Toolkit for Operator Algebraists*, Chapters 1–4 and 6.
* I. Raeburn and D. P. Williams, *Morita Equivalence and Continuous-Trace C⋆-Algebras*, Chapter 2.
* J. Roe, *Lectures on K-Theory and Operator Algebras*, Proposition 10.2.
-/

public section

open MulOpposite Matrix CStarModule
open scoped WithCStarModule

/-! ### Column-vector action of `CStarMatrix` on finite right Hilbert C⋆-modules -/

namespace CStarMatrix

section NonUnital

variable {l m n A : Type*} [Fintype n] [NonUnitalCStarAlgebra A]

/-- Left multiplication by a `CStarMatrix m n A` on column vectors in `C⋆ᵐᵒᵈ(Aᵐᵒᵖ, n → A)`, bundled
as a continuous complex-linear map. Unlike `CStarMatrix.toCLM`, which acts by `Matrix.vecMul` on the
left module `C⋆ᵐᵒᵈ(A, m → A)`, this acts by `Matrix.mulVec` and commutes with the right `A`-action.
-/
noncomputable def mulVecCLM (M : CStarMatrix m n A) :
    C⋆ᵐᵒᵈ(Aᵐᵒᵖ, n → A) →L[ℂ] C⋆ᵐᵒᵈ(Aᵐᵒᵖ, m → A) :=
  let L : (n → A) →L[ℂ] (m → A) :=
    { toLinearMap := Matrix.mulVecBilin ℂ ℂ (ofMatrix.symm M)
      cont := by
        change Continuous fun (v : n → A) (i : m) ↦ ∑ j, M i j * v j
        fun_prop }
  (WithCStarModule.equivL ℂ (A := Aᵐᵒᵖ) (E := m → A)).symm.toContinuousLinearMap.comp <|
    L.comp (WithCStarModule.equivL ℂ (A := Aᵐᵒᵖ) (E := n → A)).toContinuousLinearMap

theorem mulVecCLM_apply (M : CStarMatrix m n A) (v : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, n → A)) :
    mulVecCLM M v = (WithCStarModule.equiv Aᵐᵒᵖ (m → A)).symm (ofMatrix.symm M *ᵥ v) := (rfl)

@[simp]
theorem mulVecCLM_apply_apply (M : CStarMatrix m n A) (v : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, n → A)) (i : m) :
    mulVecCLM M v i = ∑ j, M i j * v j := (rfl)

theorem mulVecCLM_comp [Fintype m] (M : CStarMatrix l m A) (N : CStarMatrix m n A) :
    (mulVecCLM M).comp (mulVecCLM N) = mulVecCLM (M * N) := by
  ext v i
  simp only [ContinuousLinearMap.comp_apply, mulVecCLM_apply_apply, mul_apply, Finset.sum_mul,
    Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

theorem isIdempotentElem_mulVecCLM {p : CStarMatrix n n A} (hp : IsIdempotentElem p) :
    IsIdempotentElem (mulVecCLM p) := by
  change (mulVecCLM p).comp (mulVecCLM p) = mulVecCLM p
  rw [mulVecCLM_comp, hp.eq]

/-- Column-vector multiplication by `M` and by `M.conjTranspose` form a module adjoint pair on the
finite free right Hilbert `A`-modules. -/
theorem isAdjointPair_mulVecCLM_conjTranspose [Fintype m] [PartialOrder A] [StarOrderedRing A]
    (M : CStarMatrix m n A) :
    LinearMap.IsAdjointPair
      (innerₛₗ (A := Aᵐᵒᵖ) (E := C⋆ᵐᵒᵈ(Aᵐᵒᵖ, n → A))).flip
      (innerₛₗ (A := Aᵐᵒᵖ) (E := C⋆ᵐᵒᵈ(Aᵐᵒᵖ, m → A))).flip
      (mulVecCLM M) (mulVecCLM M.conjTranspose) := by
  rw [isAdjointPair_inner_iff]
  intro v w
  apply unop_injective
  simp only [WithCStarModule.pi_inner, Finset.unop_sum, unop_inner_mulOpposite,
    mulVecCLM_apply_apply, star_sum, star_mul, Finset.sum_mul, conjTranspose_apply]
  rw [Finset.sum_comm]
  simp_rw [Finset.mul_sum, mul_assoc]

/-- Column-vector multiplication by a square matrix `M` and by `star M` form a module adjoint pair
on `C⋆ᵐᵒᵈ(Aᵐᵒᵖ, n → A)`. -/
theorem isAdjointPair_mulVecCLM_star [PartialOrder A] [StarOrderedRing A]
    (M : CStarMatrix n n A) :
    LinearMap.IsAdjointPair
      (innerₛₗ (A := Aᵐᵒᵖ) (E := C⋆ᵐᵒᵈ(Aᵐᵒᵖ, n → A))).flip
      (innerₛₗ (A := Aᵐᵒᵖ) (E := C⋆ᵐᵒᵈ(Aᵐᵒᵖ, n → A))).flip
      (mulVecCLM M) (mulVecCLM (star M)) :=
  isAdjointPair_mulVecCLM_conjTranspose M

end NonUnital

section Unital

variable {l m n A : Type*} [Fintype n]

/-- Left multiplication by a `CStarMatrix m n A` on `C⋆ᵐᵒᵈ(Aᵐᵒᵖ, n → A)`, bundled as a right
`A`-linear (`Aᵐᵒᵖ`-linear) map. -/
def mulVecLinearMap [Ring A] (M : CStarMatrix m n A) :
    C⋆ᵐᵒᵈ(Aᵐᵒᵖ, n → A) →ₗ[Aᵐᵒᵖ] C⋆ᵐᵒᵈ(Aᵐᵒᵖ, m → A) :=
  (WithCStarModule.linearEquiv Aᵐᵒᵖ Aᵐᵒᵖ (m → A)).symm.toLinearMap ∘ₗ
    Matrix.mulVecBilin ℤ Aᵐᵒᵖ (ofMatrix.symm M) ∘ₗ
    (WithCStarModule.linearEquiv Aᵐᵒᵖ Aᵐᵒᵖ (n → A)).toLinearMap

@[simp]
theorem coe_mulVecLinearMap [CStarAlgebra A] (M : CStarMatrix m n A) :
    ⇑(mulVecLinearMap M) = ⇑(mulVecCLM M) := (rfl)

@[simp]
theorem mulVecLinearMap_apply_apply [Ring A] (M : CStarMatrix m n A) (v : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, n → A))
    (i : m) : mulVecLinearMap M v i = ∑ j, M i j * v j := (rfl)

theorem mulVecLinearMap_comp [Fintype m] [Ring A] (M : CStarMatrix l m A)
    (N : CStarMatrix m n A) :
    (mulVecLinearMap M).comp (mulVecLinearMap N) = mulVecLinearMap (M * N) := by
  ext v i
  simp only [LinearMap.comp_apply, mulVecLinearMap_apply_apply, mul_apply, Finset.sum_mul,
    Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

@[simp]
theorem mulVecLinearMap_one [DecidableEq n] [Ring A] :
    mulVecLinearMap (1 : CStarMatrix n n A) = LinearMap.id := by
  ext v i
  simpa [mulVecLinearMap_apply_apply, one_apply] using
    Finset.sum_ite_eq_of_mem Finset.univ i (WithCStarModule.equiv Aᵐᵒᵖ (n → A) v)
      (Finset.mem_univ i)

@[simp]
theorem mulVecCLM_one [DecidableEq n] [CStarAlgebra A] :
    mulVecCLM (1 : CStarMatrix n n A) = .id ℂ _ := by
  ext v i
  simpa [mulVecCLM_apply_apply, one_apply] using
    Finset.sum_ite_eq_of_mem Finset.univ i (WithCStarModule.equiv Aᵐᵒᵖ (n → A) v)
      (Finset.mem_univ i)

theorem isIdempotentElem_mulVecLinearMap [Ring A] {p : CStarMatrix n n A}
    (hp : IsIdempotentElem p) : IsIdempotentElem (mulVecLinearMap p) := by
  change (mulVecLinearMap p).comp (mulVecLinearMap p) = mulVecLinearMap p
  rw [mulVecLinearMap_comp, hp.eq]

end Unital

end CStarMatrix

/-! ### Finite Parseval frames: definition, edge cases, and unitary invariance -/

namespace CStarModule

section Defs

variable {A ι κ E : Type*} [Fintype ι] [Inner A E] [AddCommMonoid E] [SMul A E]

/-- A finite family `x : ι → E` in a C⋆-module is a *Parseval frame* if
`z = ∑ i, ⟪x i, z⟫_A • x i` for every `z : E`. For a right Hilbert `A`-module `E` represented as
`CStarModule Aᵐᵒᵖ E`, `IsParsevalFrame Aᵐᵒᵖ x` states `z = ∑ i, x i ⟨x i, z⟩_A`. -/
@[expose]
def IsParsevalFrame (A : Type*) {ι E : Type*} [Fintype ι] [Inner A E] [AddCommMonoid E]
    [SMul A E] (x : ι → E) : Prop :=
  ∀ z : E, ∑ i, inner A (x i) z • x i = z

theorem isParsevalFrame_iff {x : ι → E} :
    IsParsevalFrame A x ↔ ∀ z : E, ∑ i, inner A (x i) z • x i = z :=
  Iff.rfl

theorem IsParsevalFrame.sum_inner_smul {x : ι → E} (hx : IsParsevalFrame A x) (z : E) :
    ∑ i, inner A (x i) z • x i = z :=
  hx z

/-- Every finite family in a subsingleton module is a Parseval frame. In particular, `Fin.elim0` on
`Fin 0` is a Parseval frame of the zero module, and over a subsingleton C⋆-algebra `A` every unital
module is subsingleton (`Module.subsingleton`). -/
theorem isParsevalFrame_of_subsingleton [Subsingleton E] (x : ι → E) : IsParsevalFrame A x :=
  fun _ ↦ Subsingleton.elim _ _

/-- An empty family is a Parseval frame if and only if the module is subsingleton. -/
theorem isParsevalFrame_empty_iff [IsEmpty ι] (x : ι → E) :
    IsParsevalFrame A x ↔ Subsingleton E :=
  ⟨fun hx ↦ ⟨fun y z ↦ by rw [← hx y, ← hx z]; simp⟩, fun _ ↦ isParsevalFrame_of_subsingleton x⟩

/-- Reindexing a Parseval frame along an equivalence of finite index types preserves the Parseval
property. -/
theorem IsParsevalFrame.comp_equiv [Fintype κ] {x : ι → E} (hx : IsParsevalFrame A x)
    (e : κ ≃ ι) : IsParsevalFrame A (x ∘ e) := fun z ↦ by
  simpa [Function.comp_apply] using
    (e.sum_comp fun i ↦ inner A (x i) z • x i).trans (hx z)

@[simp]
theorem isParsevalFrame_comp_equiv_iff [Fintype κ] {x : ι → E} (e : κ ≃ ι) :
    IsParsevalFrame A (x ∘ e) ↔ IsParsevalFrame A x :=
  ⟨fun h ↦ by simpa [Function.comp_def] using h.comp_equiv e.symm, fun h ↦ h.comp_equiv e⟩

end Defs

end CStarModule

namespace LinearIsometryEquiv

variable {A ι E F : Type*} [Fintype ι] [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [SeminormedAddCommGroup E] [Module ℂ E] [Module A E] [CStarModule A E]
  [SeminormedAddCommGroup F] [Module ℂ F] [Module A F] [CStarModule A F]

/-- Over a unital C⋆-algebra, a unitary isomorphism `f : E ≃ₗᵢ[A] F` preserves Parseval frames. -/
@[simp]
theorem isParsevalFrame_comp_iff (f : E ≃ₗᵢ[A] F) {x : ι → E} :
    IsParsevalFrame A (f ∘ x) ↔ IsParsevalFrame A x := by
  refine ⟨fun h z ↦ f.injective ?_, fun h w ↦ ?_⟩
  · simpa [Function.comp_apply, map_sum, f.map_smul, f.inner_map_map_cstarModule] using h (f z)
  · obtain ⟨z, rfl⟩ := f.surjective w
    simpa [Function.comp_apply, map_sum, f.map_smul, f.inner_map_map_cstarModule] using
      congrArg f (h z)

end LinearIsometryEquiv

/-! ### Analysis and synthesis operators, Parseval's identity, and Gram projections -/

namespace CStarModule

section NonUnital

variable {A ι E : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Aᵐᵒᵖ E] [CStarModule Aᵐᵒᵖ E]

/-- Right scalar multiplication `a ↦ x a` for a fixed vector `x : E`, bundled as a bounded
complex-linear map `A →L[ℂ] E`. -/
private noncomputable def opSMulCLM (A : Type*) [NonUnitalCStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [SMul Aᵐᵒᵖ E] [CStarModule Aᵐᵒᵖ E] (x : E) : A →L[ℂ] E :=
  have : IsScalarTower ℂ Aᵐᵒᵖ E := CStarModule.isScalarTower Aᵐᵒᵖ E
  LinearMap.mkContinuous
    { toFun := fun a ↦ op a • x
      map_add' := fun a b ↦ by rw [op_add, CStarModule.add_smul]
      map_smul' := fun c a ↦ by simp [op_smul, smul_assoc] }
    ‖x‖ fun a ↦ norm_op_smul_le a x

@[simp]
private theorem opSMulCLM_apply (x : E) (a : A) : opSMulCLM A x a = op a • x := (rfl)

/-- The *analysis operator* of a family `x : ι → E` in a right Hilbert `A`-module, sending `z : E`
to the tuple `i ↦ ⟨x i, z⟩_A` in `C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)`. -/
noncomputable def frameAnalysisCLM (A : Type*) [NonUnitalCStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [SMul Aᵐᵒᵖ E] [CStarModule Aᵐᵒᵖ E] (x : ι → E) :
    E →L[ℂ] C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A) :=
  (WithCStarModule.equivL ℂ (A := Aᵐᵒᵖ) (E := ι → A)).symm.toContinuousLinearMap.comp <|
    ContinuousLinearMap.pi fun i ↦
      (MulOpposite.opContinuousLinearEquiv ℂ).symm.toContinuousLinearMap.comp (innerSL (x i))

@[simp]
theorem frameAnalysisCLM_apply_apply (x : ι → E) (z : E) (i : ι) :
    frameAnalysisCLM A x z i = unop (inner Aᵐᵒᵖ (x i) z) := (rfl)

theorem frameAnalysisCLM_op_smul (x : ι → E) (a : A) (z : E) :
    frameAnalysisCLM A x (op a • z) = op a • frameAnalysisCLM A x z := by
  ext i
  simp [MulOpposite.smul_eq_mul_unop]

variable [Fintype ι]

/-- The *synthesis operator* of a finite family `x : ι → E` in a right Hilbert `A`-module, sending
`v : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)` to `∑ i, x i (v i)`. -/
noncomputable def frameSynthesisCLM (A : Type*) [NonUnitalCStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [SMul Aᵐᵒᵖ E] [CStarModule Aᵐᵒᵖ E] (x : ι → E) :
    C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A) →L[ℂ] E :=
  ∑ i : ι, ((opSMulCLM A (x i)).comp <|
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι ↦ A) i).comp
      (WithCStarModule.equivL ℂ (A := Aᵐᵒᵖ) (E := ι → A)).toContinuousLinearMap)

@[simp]
theorem frameSynthesisCLM_apply (x : ι → E) (v : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)) :
    frameSynthesisCLM A x v = ∑ i, op (v i) • x i := by
  simp [frameSynthesisCLM]

theorem frameSynthesisCLM_op_smul (x : ι → E) (a : A) (v : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)) :
    frameSynthesisCLM A x (op a • v) = op a • frameSynthesisCLM A x v := by
  let _ := CStarModule.distribSMul Aᵐᵒᵖ E
  rw [frameSynthesisCLM_apply, frameSynthesisCLM_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [WithCStarModule.smul_apply, MulOpposite.smul_eq_mul_unop, unop_op, op_mul,
    (CStarModule.semigroupAction Aᵐᵒᵖ E).mul_smul]

/-- The synthesis and analysis operators of any finite family form a module adjoint pair:
`⟨∑ i, x i (v i), z⟩_A = ⟨v, (i ↦ ⟨x i, z⟩_A)⟩_A`. -/
theorem isAdjointPair_frameSynthesisCLM_frameAnalysisCLM (x : ι → E) :
    LinearMap.IsAdjointPair
      (innerₛₗ (A := Aᵐᵒᵖ) (E := C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A))).flip
      (innerₛₗ (A := Aᵐᵒᵖ) (E := E)).flip
      (frameSynthesisCLM A x) (frameAnalysisCLM A x) := by
  rw [isAdjointPair_inner_iff]
  intro v z
  apply unop_injective
  simp [WithCStarModule.pi_inner, inner_sum_left, Finset.unop_sum]

theorem frameSynthesisCLM_frameAnalysisCLM_apply (x : ι → E) (z : E) :
    frameSynthesisCLM A x (frameAnalysisCLM A x z) = ∑ i, inner Aᵐᵒᵖ (x i) z • x i := by
  simp

theorem frameAnalysisCLM_frameSynthesisCLM_apply (x : ι → E) (v : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)) :
    frameAnalysisCLM A x (frameSynthesisCLM A x v) =
      CStarMatrix.mulVecCLM (CStarMatrix.gram A x) v := by
  ext i
  simp [inner_sum_right, Finset.unop_sum]

theorem frameAnalysisCLM_comp_frameSynthesisCLM (x : ι → E) :
    (frameAnalysisCLM A x).comp (frameSynthesisCLM A x) =
      CStarMatrix.mulVecCLM (CStarMatrix.gram A x) :=
  ContinuousLinearMap.ext fun v ↦ frameAnalysisCLM_frameSynthesisCLM_apply x v

/-- A finite family `x` is a Parseval frame if and only if synthesis after analysis is the identity
operator on `E`. -/
theorem isParsevalFrame_iff_frameSynthesisCLM_comp_frameAnalysisCLM {x : ι → E} :
    IsParsevalFrame Aᵐᵒᵖ x ↔ (frameSynthesisCLM A x).comp (frameAnalysisCLM A x) = .id ℂ E := by
  simp [IsParsevalFrame, ContinuousLinearMap.ext_iff]

/-- A finite family `x` is a Parseval frame if and only if its analysis operator preserves the
`Aᵐᵒᵖ`-valued inner product. -/
theorem isParsevalFrame_iff_inner_frameAnalysisCLM {x : ι → E} :
    IsParsevalFrame Aᵐᵒᵖ x ↔
      ∀ y z : E,
        inner Aᵐᵒᵖ (frameAnalysisCLM A x y) (frameAnalysisCLM A x z) = inner Aᵐᵒᵖ y z := by
  have hadj := (isAdjointPair_frameSynthesisCLM_frameAnalysisCLM (A := A) x).symm_cstarModule
  constructor
  · intro hx y z
    rw [hadj.inner_eq_cstarModule, frameSynthesisCLM_frameAnalysisCLM_apply, hx z]
  · intro h z
    refine ext_inner_left (A := Aᵐᵒᵖ) fun y ↦ ?_
    rw [← frameSynthesisCLM_frameAnalysisCLM_apply, ← hadj.inner_eq_cstarModule, h y z]

/-- **Parseval's identity**: a finite family `x : ι → E` is a Parseval frame if and only if
`∑ i, ⟨x i, z⟩_A⋆ ⟨x i, z⟩_A = ⟨z, z⟩_A` for every `z : E`. -/
theorem isParsevalFrame_iff_sum_star_mul_inner_self {x : ι → E} :
    IsParsevalFrame Aᵐᵒᵖ x ↔
      ∀ z : E,
        ∑ i, star (unop (inner Aᵐᵒᵖ (x i) z)) * unop (inner Aᵐᵒᵖ (x i) z) =
          unop (inner Aᵐᵒᵖ z z) := by
  rw [isParsevalFrame_iff_inner_frameAnalysisCLM]
  constructor
  · intro h z
    simpa [WithCStarModule.pi_inner, Finset.unop_sum] using congrArg unop (h z z)
  · intro h y z
    have hdiag (w : E) :
        inner Aᵐᵒᵖ (frameAnalysisCLM A x w) (frameAnalysisCLM A x w) = inner Aᵐᵒᵖ w w := by
      apply unop_injective
      simpa [WithCStarModule.pi_inner, Finset.unop_sum] using h w
    rw [inner_polarization (frameAnalysisCLM A x y) (frameAnalysisCLM A x z),
      inner_polarization y z]
    simp only [← map_smul, ← map_add, ← map_sub, hdiag]

/-- The Gram matrix of any Parseval frame is a star projection in `CStarMatrix ι ι A`. Neither a
unit in `A` nor completeness of `E` is needed. -/
theorem IsParsevalFrame.isStarProjection_gram {x : ι → E} (hx : IsParsevalFrame Aᵐᵒᵖ x) :
    IsStarProjection (CStarMatrix.gram A x) where
  isSelfAdjoint := (CStarMatrix.gram_nonneg x).isSelfAdjoint
  isIdempotentElem := by
    ext i j
    simp only [CStarMatrix.mul_apply, CStarMatrix.gram_apply]
    have hsum :
        ∑ k, unop (inner Aᵐᵒᵖ (x i) (x k)) * unop (inner Aᵐᵒᵖ (x k) (x j)) =
          unop (inner Aᵐᵒᵖ (x i) (∑ k, inner Aᵐᵒᵖ (x k) (x j) • x k)) := by
      simp [inner_sum_right, Finset.unop_sum]
    rw [hsum, hx (x j)]

/-- Over any C⋆-algebra (possibly non-unital), a finite family `x` is a Parseval frame if and only
if its Gram matrix is a star projection and its synthesis operator is surjective. -/
theorem isParsevalFrame_iff_isStarProjection_gram_and_surjective_frameSynthesisCLM {x : ι → E} :
    IsParsevalFrame Aᵐᵒᵖ x ↔
      IsStarProjection (CStarMatrix.gram A x) ∧ Function.Surjective (frameSynthesisCLM A x) := by
  constructor
  · refine fun hx ↦ ⟨hx.isStarProjection_gram, fun z ↦ ⟨frameAnalysisCLM A x z, ?_⟩⟩
    simpa using hx z
  · rintro ⟨hp, hsurj⟩ z
    obtain ⟨v, rfl⟩ := hsurj z
    set G := CStarMatrix.gram A x
    set w := CStarMatrix.mulVecCLM G v - v
    have hΘΦw : frameAnalysisCLM A x (frameSynthesisCLM A x w) = 0 := by
      rw [frameAnalysisCLM_frameSynthesisCLM_apply, map_sub]
      have hGG : CStarMatrix.mulVecCLM G (CStarMatrix.mulVecCLM G v) =
          CStarMatrix.mulVecCLM G v := by
        rw [← ContinuousLinearMap.comp_apply, CStarMatrix.mulVecCLM_comp, hp.isIdempotentElem.eq]
      exact sub_eq_zero.mpr hGG
    have hΦw : frameSynthesisCLM A x w = 0 := by
      apply (inner_self (A := Aᵐᵒᵖ)).mp
      rw [(isAdjointPair_frameSynthesisCLM_frameAnalysisCLM (A := A) x).inner_eq_cstarModule,
        hΘΦw, inner_zero_right]
    have hsub : frameSynthesisCLM A x (CStarMatrix.mulVecCLM G v) = frameSynthesisCLM A x v := by
      rw [← sub_eq_zero, ← map_sub]
      exact hΦw
    rw [← frameAnalysisCLM_frameSynthesisCLM_apply,
      frameSynthesisCLM_frameAnalysisCLM_apply] at hsub
    exact hsub

end NonUnital

/-! ### Unital coefficient algebras: projection comparison and algebraic projectivity -/

section Unital

variable {A ι E : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [Module Aᵐᵒᵖ E] [CStarModule Aᵐᵒᵖ E]

/-- The analysis operator of a family `x : ι → E` bundled as a right `A`-linear (`Aᵐᵒᵖ`-linear)
map. -/
noncomputable def frameAnalysisLinearMap (A : Type*) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [Module Aᵐᵒᵖ E] [CStarModule Aᵐᵒᵖ E] (x : ι → E) :
    E →ₗ[Aᵐᵒᵖ] C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A) where
  toFun := frameAnalysisCLM A x
  map_add' := map_add (frameAnalysisCLM A x)
  map_smul' a z := frameAnalysisCLM_op_smul x (unop a) z

@[simp]
theorem coe_frameAnalysisLinearMap (x : ι → E) :
    ⇑(frameAnalysisLinearMap A x) = ⇑(frameAnalysisCLM A x) := (rfl)

@[simp]
theorem frameAnalysisLinearMap_apply_apply (x : ι → E) (z : E) (i : ι) :
    frameAnalysisLinearMap A x z i = unop (inner Aᵐᵒᵖ (x i) z) := (rfl)

variable [Fintype ι]

/-- The standard basis `i ↦ Pi.single i 1` of the finite free right Hilbert `A`-module
`C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)` is a Parseval frame. -/
theorem isParsevalFrame_single_one [DecidableEq ι] :
    IsParsevalFrame Aᵐᵒᵖ
      (fun i : ι ↦ (WithCStarModule.equiv Aᵐᵒᵖ (ι → A)).symm (Pi.single i (1 : A))) := by
  intro v
  apply (WithCStarModule.linearEquiv ℂ Aᵐᵒᵖ (ι → A)).injective
  rw [map_sum]
  ext j
  simp only [Finset.sum_apply, WithCStarModule.linearEquiv_apply, WithCStarModule.equiv_pi_apply,
    WithCStarModule.smul_apply, WithCStarModule.equiv_symm_pi_apply,
    WithCStarModule.inner_single_left, inner_mulOpposite, star_one, one_mul,
    MulOpposite.smul_eq_mul_unop, unop_op, Pi.single_apply, ite_mul, zero_mul]
  exact Finset.sum_ite_eq_of_mem Finset.univ j (WithCStarModule.equiv Aᵐᵒᵖ (ι → A) v)
    (Finset.mem_univ j)

/-- Every vector in `C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)` expands in the standard basis `i ↦ Pi.single i 1`. -/
theorem sum_op_smul_single_one [DecidableEq ι] (v : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)) :
    ∑ i : ι, op (v i) • (WithCStarModule.equiv Aᵐᵒᵖ (ι → A)).symm (Pi.single i (1 : A)) = v := by
  simpa [WithCStarModule.inner_single_left, inner_mulOpposite] using isParsevalFrame_single_one v

/-- The synthesis operator of a finite family `x : ι → E` bundled as a right `A`-linear
(`Aᵐᵒᵖ`-linear) map. -/
noncomputable def frameSynthesisLinearMap (A : Type*) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [Module Aᵐᵒᵖ E] [CStarModule Aᵐᵒᵖ E] (x : ι → E) :
    C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A) →ₗ[Aᵐᵒᵖ] E where
  toFun := frameSynthesisCLM A x
  map_add' := map_add (frameSynthesisCLM A x)
  map_smul' a v := frameSynthesisCLM_op_smul x (unop a) v

@[simp]
theorem coe_frameSynthesisLinearMap (x : ι → E) :
    ⇑(frameSynthesisLinearMap A x) = ⇑(frameSynthesisCLM A x) := (rfl)

@[simp]
theorem frameSynthesisLinearMap_apply (x : ι → E) (v : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)) :
    frameSynthesisLinearMap A x v = ∑ i, op (v i) • x i :=
  frameSynthesisCLM_apply x v

theorem frameAnalysisLinearMap_comp_frameSynthesisLinearMap (x : ι → E) :
    (frameAnalysisLinearMap A x).comp (frameSynthesisLinearMap A x) =
      CStarMatrix.mulVecLinearMap (CStarMatrix.gram A x) :=
  LinearMap.ext fun v ↦ frameAnalysisCLM_frameSynthesisCLM_apply x v

theorem IsParsevalFrame.frameSynthesisLinearMap_comp_frameAnalysisLinearMap {x : ι → E}
    (hx : IsParsevalFrame Aᵐᵒᵖ x) :
    (frameSynthesisLinearMap A x).comp (frameAnalysisLinearMap A x) = LinearMap.id := by
  ext z
  simpa [LinearMap.comp_apply] using hx z

/-- Over a unital C⋆-algebra, a finite family `x` is a Parseval frame if and only if its Gram
matrix is a star projection and its module-linear synthesis map is surjective. -/
theorem isParsevalFrame_iff_isStarProjection_gram_and_surjective {x : ι → E} :
    IsParsevalFrame Aᵐᵒᵖ x ↔
      IsStarProjection (CStarMatrix.gram A x) ∧
        Function.Surjective (frameSynthesisLinearMap A x) :=
  isParsevalFrame_iff_isStarProjection_gram_and_surjective_frameSynthesisCLM

/-- Right `A`-linear identification between `(ι → Aᵐᵒᵖ)` and `C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)`. -/
private def piOpLinearEquiv (A ι : Type*) [Ring A] :
    (ι → Aᵐᵒᵖ) ≃ₗ[Aᵐᵒᵖ] C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A) :=
  LinearEquiv.piCongrRight (fun _ ↦ (MulOpposite.opLinearEquiv Aᵐᵒᵖ).symm) ≪≫ₗ
    (WithCStarModule.linearEquiv Aᵐᵒᵖ Aᵐᵒᵖ (ι → A)).symm

/-- A right Hilbert `A`-module admitting a finite Parseval frame is finitely generated as a right
`A`-module; completeness of `E` is not needed. -/
theorem IsParsevalFrame.finite {x : ι → E} (hx : IsParsevalFrame Aᵐᵒᵖ x) :
    Module.Finite Aᵐᵒᵖ E := by
  let e : (ι → Aᵐᵒᵖ) ≃ₗ[Aᵐᵒᵖ] C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A) := piOpLinearEquiv A ι
  let Φ₀ : (ι → Aᵐᵒᵖ) →ₗ[Aᵐᵒᵖ] E := (frameSynthesisLinearMap A x).comp e.toLinearMap
  refine Module.Finite.of_surjective Φ₀ ?_
  exact (isParsevalFrame_iff_isStarProjection_gram_and_surjective.mp hx).2.comp e.surjective

/-- A right Hilbert `A`-module admitting a finite Parseval frame is projective as a right
`A`-module; completeness of `E` is not needed. -/
theorem IsParsevalFrame.projective {x : ι → E} (hx : IsParsevalFrame Aᵐᵒᵖ x) :
    Module.Projective Aᵐᵒᵖ E := by
  classical
  let e : (ι → Aᵐᵒᵖ) ≃ₗ[Aᵐᵒᵖ] C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A) := piOpLinearEquiv A ι
  let i₀ : E →ₗ[Aᵐᵒᵖ] (ι → Aᵐᵒᵖ) := e.symm.toLinearMap.comp (frameAnalysisLinearMap A x)
  let s₀ : (ι → Aᵐᵒᵖ) →ₗ[Aᵐᵒᵖ] E := (frameSynthesisLinearMap A x).comp e.toLinearMap
  refine Module.Projective.of_split i₀ s₀ ?_
  ext z
  simpa [i₀, s₀, LinearMap.comp_apply] using hx z

/-- The analysis map of a Parseval frame is a right `A`-linear isometry into
`C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)`. -/
noncomputable def IsParsevalFrame.frameAnalysisIsometry {x : ι → E}
    (hx : IsParsevalFrame Aᵐᵒᵖ x) : E →ₗᵢ[Aᵐᵒᵖ] C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A) :=
  (frameAnalysisLinearMap A x).isometryOfInnerCStarModule fun z ↦
    isParsevalFrame_iff_inner_frameAnalysisCLM.mp hx z z

@[simp]
theorem IsParsevalFrame.coe_frameAnalysisIsometry {x : ι → E} (hx : IsParsevalFrame Aᵐᵒᵖ x) :
    ⇑hx.frameAnalysisIsometry = ⇑(frameAnalysisCLM A x) :=
  (LinearMap.coe_isometryOfInnerCStarModule (frameAnalysisLinearMap A x) _).trans
    (coe_frameAnalysisLinearMap x)

/-- The range of the analysis operator of a Parseval frame `x` is the projection-cutdown submodule
`LinearMap.range (CStarMatrix.mulVecLinearMap (CStarMatrix.gram A x))`. -/
theorem IsParsevalFrame.range_frameAnalysisLinearMap {x : ι → E} (hx : IsParsevalFrame Aᵐᵒᵖ x) :
    LinearMap.range (frameAnalysisLinearMap A x) =
      LinearMap.range (CStarMatrix.mulVecLinearMap (CStarMatrix.gram A x)) := by
  rw [← frameAnalysisLinearMap_comp_frameSynthesisLinearMap]
  refine le_antisymm ?_ (LinearMap.range_comp_le_range _ _)
  rintro _ ⟨z, rfl⟩
  exact ⟨frameAnalysisLinearMap A x z, by simp [hx z]⟩

/-- A Parseval frame `x : ι → E` identifies `E` unitarily (`E ≃ₗᵢ[Aᵐᵒᵖ] _`) with the
projection-cutdown module `p A^ι = LinearMap.range (CStarMatrix.mulVecLinearMap p)` for
`p = CStarMatrix.gram A x`, with explicit inverse given by restricting
`frameSynthesisLinearMap A x`. -/
noncomputable def IsParsevalFrame.equivRangeGram {x : ι → E} (hx : IsParsevalFrame Aᵐᵒᵖ x) :
    E ≃ₗᵢ[Aᵐᵒᵖ] LinearMap.range (CStarMatrix.mulVecLinearMap (CStarMatrix.gram A x)) := by
  let S := LinearMap.range (CStarMatrix.mulVecLinearMap (CStarMatrix.gram A x))
  let f : E →ₗᵢ[Aᵐᵒᵖ] S :=
    { toLinearMap := (frameAnalysisLinearMap A x).codRestrict S fun z ↦ by
        change frameAnalysisLinearMap A x z ∈
          LinearMap.range (CStarMatrix.mulVecLinearMap (CStarMatrix.gram A x))
        rw [← hx.range_frameAnalysisLinearMap]
        exact LinearMap.mem_range_self _ z
      norm_map' := fun z ↦ by simpa using hx.frameAnalysisIsometry.norm_map z }
  let g : S →ₗ[Aᵐᵒᵖ] E := (frameSynthesisLinearMap A x).comp S.subtype
  refine LinearIsometryEquiv.ofLinearIsometry f g ?_ ?_
  · apply LinearMap.ext
    rintro ⟨w, v, hv⟩
    apply Subtype.ext
    have hidem := hx.isStarProjection_gram.isIdempotentElem
    have hw : CStarMatrix.mulVecLinearMap (CStarMatrix.gram A x) w = w := by
      rw [← hv, ← LinearMap.comp_apply, CStarMatrix.mulVecLinearMap_comp, hidem.eq]
    change frameAnalysisLinearMap A x (frameSynthesisLinearMap A x w) = w
    rw [← LinearMap.comp_apply, frameAnalysisLinearMap_comp_frameSynthesisLinearMap, hw]
  · apply LinearMap.ext
    intro z
    simpa [f, g, LinearMap.comp_apply] using hx z

@[simp]
theorem IsParsevalFrame.coe_equivRangeGram_apply {x : ι → E} (hx : IsParsevalFrame Aᵐᵒᵖ x)
    (z : E) : (hx.equivRangeGram z : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)) = frameAnalysisCLM A x z := (rfl)

@[simp]
theorem IsParsevalFrame.equivRangeGram_symm_apply {x : ι → E} (hx : IsParsevalFrame Aᵐᵒᵖ x)
    (u : LinearMap.range (CStarMatrix.mulVecLinearMap (CStarMatrix.gram A x))) :
    hx.equivRangeGram.symm u = frameSynthesisLinearMap A x u.1 := (rfl)

/-- Every right Hilbert `A`-module admitting a finite Parseval frame is automatically complete:
`hx.equivRangeGram` identifies it isometrically with the closed range of the idempotent operator
`CStarMatrix.mulVecCLM (CStarMatrix.gram A x)` inside the complete module `C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)`. -/
theorem IsParsevalFrame.completeSpace {x : ι → E} (hx : IsParsevalFrame Aᵐᵒᵖ x) :
    CompleteSpace E := by
  set G := CStarMatrix.gram A x
  have hclosed : IsClosed ((CStarMatrix.mulVecCLM G).range : Set C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)) :=
    ContinuousLinearMap.IsIdempotentElem.isClosed_range
      (CStarMatrix.isIdempotentElem_mulVecCLM hx.isStarProjection_gram.isIdempotentElem)
  have hrange :
      Set.range hx.frameAnalysisIsometry =
        ((CStarMatrix.mulVecCLM G).range : Set C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)) := by
    ext w
    rw [Set.mem_range, SetLike.mem_coe, LinearMap.mem_range]
    simp only [hx.coe_frameAnalysisIsometry, ← coe_frameAnalysisLinearMap,
      ← LinearMap.mem_range, hx.range_frameAnalysisLinearMap]
    rfl
  refine hx.frameAnalysisIsometry.isometry.isUniformInducing.completeSpace ?_
  rw [hrange]
  exact hclosed.isComplete

/-- Converse of the projection/Gram-matrix comparison: if `p : CStarMatrix ι ι A` is a star
projection and `U : E ≃ₗᵢ[Aᵐᵒᵖ] LinearMap.range (CStarMatrix.mulVecLinearMap p)` is a unitary
isomorphism, pulling back the columns of `p` along `U` produces a Parseval frame of `E` whose Gram
matrix is `p`. -/
theorem exists_isParsevalFrame_and_gram_eq_of_isStarProjection
    {p : CStarMatrix ι ι A} (hp : IsStarProjection p)
    (U : E ≃ₗᵢ[Aᵐᵒᵖ] LinearMap.range (CStarMatrix.mulVecLinearMap p)) :
    ∃ x : ι → E, IsParsevalFrame Aᵐᵒᵖ x ∧ CStarMatrix.gram A x = p := by
  classical
  have : IsScalarTower ℂ Aᵐᵒᵖ C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A) :=
    CStarModule.isScalarTower Aᵐᵒᵖ C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)
  set S := LinearMap.range (CStarMatrix.mulVecLinearMap p)
  -- Temporarily equip `S` with the restricted `CStarModule Aᵐᵒᵖ` structure so Lance's theorem
  -- applies to `U.symm : S ≃ₗᵢ[Aᵐᵒᵖ] E`.
  let _ : Module ℂ S := S.restrictScalars ℂ |>.module
  let _ : CStarModule Aᵐᵒᵖ S :=
    { inner u v := inner Aᵐᵒᵖ u.1 v.1
      inner_add_right := inner_add_right
      inner_self_nonneg := inner_self_nonneg
      inner_self := by simp [inner_self]
      inner_op_smul_right := inner_op_smul_right
      inner_smul_right_complex := inner_smul_right_complex
      star_inner u v := star_inner u.1 v.1
      norm_eq_sqrt_norm_inner_self {u} := norm_eq_sqrt_norm_inner_self (A := Aᵐᵒᵖ) (x := u.1) }
  let e : ι → C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A) :=
    fun j ↦ (WithCStarModule.equiv Aᵐᵒᵖ (ι → A)).symm (Pi.single j (1 : A))
  let u : ι → S := fun j ↦ ⟨CStarMatrix.mulVecLinearMap p (e j), e j, rfl⟩
  let x : ι → E := fun j ↦ U.symm (u j)
  have hgram : CStarMatrix.gram A x = p := by
    ext i j
    have hU : unop (inner Aᵐᵒᵖ (x i) (x j)) = unop (inner Aᵐᵒᵖ (u i).1 (u j).1) :=
      U.symm.unop_inner_map_map_cstarModule (u i) (u j)
    have hadj := (CStarMatrix.isAdjointPair_mulVecCLM_star p).inner_eq_cstarModule (e i)
      (CStarMatrix.mulVecCLM p (e j))
    have hcomp :
        CStarMatrix.mulVecCLM (star p) (CStarMatrix.mulVecCLM p (e j)) =
          CStarMatrix.mulVecCLM p (e j) := by
      rw [← ContinuousLinearMap.comp_apply, CStarMatrix.mulVecCLM_comp, hp.isSelfAdjoint.star_eq,
        hp.isIdempotentElem.eq]
    rw [CStarMatrix.gram_apply, hU]
    calc unop (inner Aᵐᵒᵖ (u i).1 (u j).1)
        = unop (inner Aᵐᵒᵖ (CStarMatrix.mulVecCLM p (e i))
            (CStarMatrix.mulVecCLM p (e j))) := rfl
      _ = unop (inner Aᵐᵒᵖ (e i) (CStarMatrix.mulVecCLM p (e j))) := by
            rw [hadj, hcomp]
      _ = p i j := by
            simp [e, WithCStarModule.inner_single_left, inner_mulOpposite, Pi.single_apply]
  refine ⟨x, isParsevalFrame_iff_isStarProjection_gram_and_surjective.mpr ⟨hgram ▸ hp, ?_⟩, hgram⟩
  intro z
  obtain ⟨v, hv⟩ := (U z).2
  refine ⟨v, ?_⟩
  let a : ι → A := WithCStarModule.equiv Aᵐᵒᵖ (ι → A) v
  have hv_sum : U z = ∑ j, op (a j) • u j := by
    apply Subtype.ext
    calc (U z : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)) = CStarMatrix.mulVecLinearMap p v := hv.symm
      _ = CStarMatrix.mulVecLinearMap p (∑ j, op (a j) • e j) :=
            congrArg (CStarMatrix.mulVecLinearMap p) (sum_op_smul_single_one v).symm
      _ = ∑ j, op (a j) • (u j).1 := by simp [map_sum, u]
      _ = (∑ j, op (a j) • u j : S).1 := by simp
  calc frameSynthesisLinearMap A x v = ∑ j, op (a j) • U.symm.toLinearEquiv (u j) :=
        frameSynthesisLinearMap_apply x v
    _ = U.symm.toLinearEquiv (∑ j, op (a j) • u j) := by simp [map_sum]
    _ = z := by rw [← hv_sum]; exact U.symm_apply_apply z

/-- Over a unital C⋆-algebra, `E` admits an `ι`-indexed Parseval frame if and only if `E` is
unitarily isomorphic to `LinearMap.range (CStarMatrix.mulVecLinearMap p)` for a star projection
`p : CStarMatrix ι ι A`. -/
theorem exists_isParsevalFrame_iff_exists_isStarProjection_linearIsometryEquiv :
    (∃ x : ι → E, IsParsevalFrame Aᵐᵒᵖ x) ↔
      ∃ p : CStarMatrix ι ι A, IsStarProjection p ∧
        Nonempty (E ≃ₗᵢ[Aᵐᵒᵖ] LinearMap.range (CStarMatrix.mulVecLinearMap p)) :=
  ⟨fun ⟨x, hx⟩ ↦ ⟨CStarMatrix.gram A x, hx.isStarProjection_gram, ⟨hx.equivRangeGram⟩⟩,
    fun ⟨_, hp, ⟨U⟩⟩ ↦
      let ⟨x, hx, _⟩ := exists_isParsevalFrame_and_gram_eq_of_isStarProjection hp U
      ⟨x, hx⟩⟩

end Unital

/-! ### Characterization of finitely generated projective Hilbert C⋆-modules -/

section FiniteProjective

variable {A E F : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- Any right `A`-linear map out of `C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)` into a right Hilbert `A`-module equals the
synthesis map of its values on the standard basis, and is therefore bounded and complex-linear. -/
private theorem eq_frameSynthesisCLM_of_linearMap {ι : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [Module Aᵐᵒᵖ E] [CStarModule Aᵐᵒᵖ E]
    (f : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A) →ₗ[Aᵐᵒᵖ] E) (v : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)) :
    f v = frameSynthesisCLM A
      (fun i ↦ f ((WithCStarModule.equiv Aᵐᵒᵖ (ι → A)).symm (Pi.single i (1 : A)))) v := by
  conv_lhs => rw [← sum_op_smul_single_one v]
  simp [map_sum]

/-- If `f : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A) →ₗ[Aᵐᵒᵖ] E` and `g : E →ₗ[Aᵐᵒᵖ] C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)` satisfy
`f ∘ₗ g = .id` on a complete right Hilbert `A`-module `E`, then `g` is continuous. -/
private theorem continuous_rightInverse_of_comp_eq_id {ι : Type*} [Finite ι]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] [Module Aᵐᵒᵖ E]
    [CStarModule Aᵐᵒᵖ E]
    (f : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A) →ₗ[Aᵐᵒᵖ] E) (g : E →ₗ[Aᵐᵒᵖ] C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A))
    (hfg : f ∘ₗ g = LinearMap.id) : Continuous g := by
  classical
  cases nonempty_fintype ι
  have : IsScalarTower ℂ Aᵐᵒᵖ E := CStarModule.isScalarTower Aᵐᵒᵖ E
  have : IsScalarTower ℂ Aᵐᵒᵖ C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A) :=
    CStarModule.isScalarTower Aᵐᵒᵖ C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)
  set F_ι := C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)
  let e : ι → F_ι := fun i ↦ (WithCStarModule.equiv Aᵐᵒᵖ (ι → A)).symm (Pi.single i (1 : A))
  let fL : F_ι →L[ℂ] E := frameSynthesisCLM A (fun i ↦ f (e i))
  have hfL (v : F_ι) : fL v = f v := (eq_frameSynthesisCLM_of_linearMap f v).symm
  let P : F_ι →ₗ[Aᵐᵒᵖ] F_ι := g ∘ₗ f
  let PL : F_ι →L[ℂ] F_ι := frameSynthesisCLM A (fun i ↦ P (e i))
  have hPL (v : F_ι) : PL v = g (f v) := (eq_frameSynthesisCLM_of_linearMap P v).symm
  have hfg_apply (z : E) : f (g z) = z := LinearMap.congr_fun hfg z
  refine (g.restrictScalars ℂ).continuous_of_isClosed_graph ?_
  have hgraph :
      ((g.restrictScalars ℂ).graph : Set (E × F_ι)) =
        {p : E × F_ι | fL p.2 = p.1 ∧ PL p.2 = p.2} := by
    ext ⟨x, y⟩
    simp only [SetLike.mem_coe, LinearMap.mem_graph_iff, LinearMap.restrictScalars_apply,
      Set.mem_ofPred_eq, hfL, hPL]
    exact ⟨fun h ↦ ⟨by rw [h, hfg_apply], by rw [h, hfg_apply]⟩,
      fun ⟨h1, h2⟩ ↦ by rw [← h1, h2]⟩
  rw [hgraph]
  exact (isClosed_eq (fL.continuous.comp continuous_snd) continuous_fst).inter
    (isClosed_eq (PL.continuous.comp continuous_snd) continuous_snd)

/-- Core positive-quadratic-form lower bound: if `u, v, w : A` satisfy `0 ≤ u`, `0 ≤ v`, and
`w ≤ (2 : ℝ) • (C • u + v)` with `0 ≤ C`, then `((2 * (1 + C))⁻¹ : ℝ) • w ≤ u + v`. -/
private theorem inv_two_one_add_smul_le {u v w : A} {C : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hC : 0 ≤ C) (hw : w ≤ (2 : ℝ) • (C • u + v)) :
    ((2 * (1 + C))⁻¹ : ℝ) • w ≤ u + v := by
  have hCu_le : C • u + v ≤ (1 + C) • (u + v) := by
    calc C • u + v
        ≤ (u + C • u) + (v + C • v) :=
          add_le_add (le_add_of_nonneg_left hu) (le_add_of_nonneg_right (smul_nonneg hC hv))
      _ = (1 + C) • (u + v) := by module
  set c : ℝ := 2 * (1 + C)
  have hc : 0 < c := by positivity
  have hw' : w ≤ c • (u + v) := by
    refine hw.trans ?_
    rw [show c = 2 * (1 + C) from rfl, mul_smul]
    refine sub_nonneg.mp ?_
    simpa [smul_sub] using smul_nonneg (zero_le_two : (0 : ℝ) ≤ 2) (sub_nonneg.mpr hCu_le)
  refine sub_nonneg.mp ?_
  have hscaled := smul_nonneg (inv_nonneg.mpr hc.le) (sub_nonneg.mpr hw')
  rwa [smul_sub, smul_smul, inv_mul_cancel₀ hc.ne', one_smul] at hscaled

/-- Over a unital C⋆-algebra `A`, a complete right Hilbert `A`-module `E` admits a finite Parseval
frame if and only if `E` is finitely generated and projective as a right `A`-module. -/
theorem exists_isParsevalFrame_iff_finite_projective
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] [Module Aᵐᵒᵖ E]
    [CStarModule Aᵐᵒᵖ E] :
    (∃ (n : ℕ) (x : Fin n → E), IsParsevalFrame Aᵐᵒᵖ x) ↔
      Module.Finite Aᵐᵒᵖ E ∧ Module.Projective Aᵐᵒᵖ E := by
  constructor
  · rintro ⟨n, x, hx⟩
    exact ⟨hx.finite, hx.projective⟩
  · rintro ⟨_, _⟩
    have : IsScalarTower ℂ Aᵐᵒᵖ E := CStarModule.isScalarTower Aᵐᵒᵖ E
    obtain ⟨n, f₀, g₀, _, _, hfg₀⟩ := Module.Finite.exists_comp_eq_id_of_projective Aᵐᵒᵖ E
    set F_n := C⋆ᵐᵒᵈ(Aᵐᵒᵖ, Fin n → A)
    let e_pi : (Fin n → Aᵐᵒᵖ) ≃ₗ[Aᵐᵒᵖ] F_n := piOpLinearEquiv A (Fin n)
    let f : F_n →ₗ[Aᵐᵒᵖ] E := f₀ ∘ₗ e_pi.symm.toLinearMap
    let g : E →ₗ[Aᵐᵒᵖ] F_n := e_pi.toLinearMap ∘ₗ g₀
    have hfg : f ∘ₗ g = LinearMap.id := by
      ext z
      simpa [f, g, LinearMap.comp_apply] using LinearMap.congr_fun hfg₀ z
    have hfg_apply (z : E) : f (g z) = z := LinearMap.congr_fun hfg z
    have hg_cont : Continuous g := continuous_rightInverse_of_comp_eq_id f g hfg
    let gL : E →L[ℂ] F_n := { toLinearMap := g.restrictScalars ℂ, cont := hg_cont }
    -- Embed `F_n` into `W = C⋆ᵐᵒᵈ(Aᵐᵒᵖ, E × F_n)` by `w ↦ (f w, w - g (f w))`, whose Gram matrix
    -- `M` is strictly positive in `CStarMatrix (Fin n) (Fin n) A`.
    set W := C⋆ᵐᵒᵈ(Aᵐᵒᵖ, E × F_n)
    let e : Fin n → F_n :=
      fun i ↦ (WithCStarModule.equiv Aᵐᵒᵖ (Fin n → A)).symm (Pi.single i (1 : A))
    let h : F_n →ₗ[Aᵐᵒᵖ] W :=
      (WithCStarModule.linearEquiv Aᵐᵒᵖ Aᵐᵒᵖ (E × F_n)).symm.toLinearMap ∘ₗ
        f.prod (LinearMap.id - g ∘ₗ f)
    have hh_fst (w : F_n) : (h w).fst = f w := (rfl)
    have hh_snd (w : F_n) : (h w).snd = w - g (f w) := (rfl)
    let y : Fin n → W := fun i ↦ h (e i)
    let M : CStarMatrix (Fin n) (Fin n) A := CStarMatrix.gram A y
    set δ : ℝ := (2 * (1 + ‖gL‖ ^ 2))⁻¹
    have hδ : 0 < δ := by positivity
    have hM_ge : algebraMap ℝ (CStarMatrix (Fin n) (Fin n) A) δ ≤ M := by
      rw [← sub_nonneg, Algebra.algebraMap_eq_smul_one, CStarMatrix.nonneg_iff_forall_sum_nonneg]
      intro a
      let w : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, Fin n → A) := (WithCStarModule.equiv Aᵐᵒᵖ (Fin n → A)).symm a
      have hw_sum : ∑ i, op (a i) • y i = h w := by
        conv_rhs => rw [← sum_op_smul_single_one w, map_sum]
        simp [y, e, w]
      have hquad_M :
          ∑ i, ∑ j, star (a i) * M i j * a j =
            unop (inner Aᵐᵒᵖ (f w) (f w)) + unop (inner Aᵐᵒᵖ (w - g (f w)) (w - g (f w))) := by
        rw [CStarMatrix.sum_star_mul_gram_mul, hw_sum, WithCStarModule.prod_inner, unop_add,
          hh_fst, hh_snd]
      have hquad_one :
          ∑ i, ∑ j, star (a i) * (δ • (1 : CStarMatrix (Fin n) (Fin n) A)) i j * a j =
            δ • unop (inner Aᵐᵒᵖ w w) := by
        have hw_inner : unop (inner Aᵐᵒᵖ w w) = ∑ i, star (a i) * a i := by
          simp [WithCStarModule.pi_inner, Finset.unop_sum, w]
        simp [CStarMatrix.one_apply, ite_mul, mul_ite, ← Finset.smul_sum, hw_inner]
      have hquad_sub :
          ∑ i, ∑ j, star (a i) * (M - δ • (1 : CStarMatrix (Fin n) (Fin n) A)) i j * a j =
            (unop (inner Aᵐᵒᵖ (f w) (f w)) + unop (inner Aᵐᵒᵖ (w - g (f w)) (w - g (f w)))) -
              δ • unop (inner Aᵐᵒᵖ w w) := by
        simp_rw [CStarMatrix.sub_apply, mul_sub, sub_mul, Finset.sum_sub_distrib, hquad_M,
          hquad_one]
      rw [hquad_sub, sub_nonneg]
      have hg_bound :
          unop (inner Aᵐᵒᵖ (g (f w)) (g (f w))) ≤ ‖gL‖ ^ 2 • unop (inner Aᵐᵒᵖ (f w) (f w)) :=
        unop_inner_apply_self_le gL (fun b z ↦ g.map_smul (op b) z) (f w)
      have hw_split :
          unop (inner Aᵐᵒᵖ w w) ≤
            (2 : ℝ) • (unop (inner Aᵐᵒᵖ (g (f w)) (g (f w))) +
              unop (inner Aᵐᵒᵖ (w - g (f w)) (w - g (f w)))) := by
        have hadd := unop_le_unop.mpr (inner_add_self_le (A := Aᵐᵒᵖ) (g (f w)) (w - g (f w)))
        rw [add_sub_cancel, unop_smul, ← ofNat_smul_eq_nsmul ℝ 2, unop_add] at hadd
        exact hadd
      refine inv_two_one_add_smul_le (unop_nonneg.mpr inner_self_nonneg)
        (unop_nonneg.mpr inner_self_nonneg) (sq_nonneg _) (hw_split.trans ?_)
      gcongr
    -- Invert `S = CFC.sqrt M` and normalize `y` to `η j = ∑ k, y k (B k j)`, then project to `E`.
    have : ContinuousFunctionalCalculus ℝ (CStarMatrix (Fin n) (Fin n) A) IsSelfAdjoint :=
      IsSelfAdjoint.instContinuousFunctionalCalculus
    have hsp : IsStrictlyPositive (algebraMap ℝ (CStarMatrix (Fin n) (Fin n) A) √δ) :=
      IsStrictlyPositive.iff_of_unital.mpr
        ⟨algebraMap_nonneg _ (Real.sqrt_nonneg δ),
          (isUnit_iff_ne_zero.mpr (Real.sqrt_ne_zero'.mpr hδ)).map (algebraMap ℝ _)⟩
    have hsqrt_le : algebraMap ℝ (CStarMatrix (Fin n) (Fin n) A) √δ ≤ CFC.sqrt M :=
      CFC.algebraMap_le_sqrt hM_ge
    obtain ⟨u, hu⟩ := CStarAlgebra.isUnit_of_le _ hsqrt_le hsp
    set S := CFC.sqrt M
    have hS_sa : star S = S := (CFC.sqrt_nonneg M).isSelfAdjoint.star_eq
    have hS_sq : S * S = M := CFC.sqrt_mul_sqrt_self M (CStarMatrix.gram_nonneg y)
    set B : CStarMatrix (Fin n) (Fin n) A := ↑u⁻¹
    have hSB : S * B = 1 := by simp [S, B, ← hu]
    have hBS : B * S = 1 := by simp [S, B, ← hu]
    have hB_sa : star B = B := by
      calc star B = (B * S) * star B := by rw [hBS, one_mul]
        _ = B * star (B * S) := by rw [mul_assoc, star_mul, hS_sa]
        _ = B := by rw [hBS, star_one, mul_one]
    let η : Fin n → W := fun j ↦ ∑ k, op (B k j) • y k
    let x : Fin n → E := fun j ↦ ∑ k, op (B k j) • f (e k)
    let π_fst : W →+ E :=
      (AddMonoidHom.fst E F_n).comp (WithCStarModule.addEquiv Aᵐᵒᵖ (E × F_n)).toAddMonoidHom
    have hη_fst (j : Fin n) : (η j).fst = x j :=
      map_sum π_fst (fun k ↦ op (B k j) • y k) Finset.univ
    have hgram_η : CStarMatrix.gram A η = 1 := by
      ext i j
      rw [CStarMatrix.gram_apply, ← CStarMatrix.sum_star_mul_gram_mul]
      change ∑ k, ∑ l, star (B k i) * M k l * B l j = (1 : CStarMatrix (Fin n) (Fin n) A) i j
      have hmul : (star B * M * B) i j = ∑ k, ∑ l, star (B k i) * M k l * B l j := by
        simp only [CStarMatrix.mul_apply, CStarMatrix.star_apply, Finset.sum_mul, mul_assoc]
        exact Finset.sum_comm
      rw [← hmul, hB_sa, ← hS_sq]
      have h1 : B * (S * S) * B = (B * S) * (S * B) := by noncomm_ring
      rw [h1, hBS, hSB, mul_one]
    have hy_recover (k : Fin n) : ∑ j, op (S j k) • η j = y k := by
      simp only [η, Finset.smul_sum, ← mul_smul, ← op_mul]
      rw [Finset.sum_comm]
      have hsum (m : Fin n) :
          ∑ j, op (B m j * S j k) • y m = op ((B * S) m k) • y m := by
        rw [← Finset.sum_smul, ← Finset.op_sum]
        rfl
      simp_rw [hsum, hBS]
      simp [CStarMatrix.one_apply, apply_ite op, ite_smul]
    refine ⟨n, x, fun z ↦ ?_⟩
    -- `(z, 0) = h (g z)` lies in the span of `η`, where `gram A η = 1` gives exact reconstruction.
    let u₀ : W := (WithCStarModule.equiv Aᵐᵒᵖ (E × F_n)).symm (z, 0)
    have hu₀_eq : h (g z) = u₀ := by
      apply (WithCStarModule.equiv Aᵐᵒᵖ (E × F_n)).injective
      ext
      · simp [u₀, hh_fst, hfg_apply]
      · simp [u₀, hh_snd, hfg_apply]
    let c : Fin n → A := fun j ↦ ∑ k, S j k * g z k
    have hu₀_span : ∑ j, op (c j) • η j = u₀ := by
      calc ∑ j, op (c j) • η j
          = ∑ j, ∑ k, op (S j k * g z k) • η j := by
              simp_rw [c, Finset.op_sum, Finset.sum_smul]
        _ = ∑ k, op (g z k) • ∑ j, op (S j k) • η j := by
              rw [Finset.sum_comm]
              simp_rw [op_mul, mul_smul, Finset.smul_sum]
        _ = ∑ k, op (g z k) • h (e k) := by simp_rw [hy_recover, y]
        _ = h (∑ k, op (g z k) • e k) := by simp [map_sum]
        _ = u₀ := by rw [sum_op_smul_single_one, hu₀_eq]
    have hinner_η (i : Fin n) : inner Aᵐᵒᵖ (η i) u₀ = op (c i) := by
      apply unop_injective
      rw [← hu₀_span, inner_sum_right, Finset.unop_sum]
      simp_rw [unop_inner_op_smul_right, ← CStarMatrix.gram_apply (A := A) η, hgram_η]
      simp [CStarMatrix.one_apply]
    have hinner_x (i : Fin n) : inner Aᵐᵒᵖ (x i) z = op (c i) := by
      rw [← hinner_η i, WithCStarModule.prod_inner]
      simp [u₀, hη_fst]
    have hfst_sum :
        (∑ i, op (c i) • η i).fst = ∑ i, op (c i) • (η i).fst :=
      map_sum π_fst (fun i ↦ op (c i) • η i) Finset.univ
    calc ∑ i, inner Aᵐᵒᵖ (x i) z • x i = ∑ i, op (c i) • (η i).fst := by simp_rw [hinner_x, hη_fst]
      _ = (∑ i, op (c i) • η i).fst := hfst_sum.symm
      _ = z := by rw [hu₀_span]; rfl

/-- Over a unital C⋆-algebra `A`, a complete right Hilbert `A`-module `E` has a finite Parseval
frame, vectors `x₁, …, xₙ` with `z = ∑ i, x i ⟨x i, z⟩_A` for every `z`, if and only if `E` is
finitely generated and projective as a right `A`-module (Roe, *Lectures on K-Theory and Operator
Algebras*, Proposition 10.2). -/
theorem exists_parseval_frame_iff_finite_projective
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] [Module Aᵐᵒᵖ E]
    [CStarModule Aᵐᵒᵖ E] :
    (∃ (n : ℕ) (x : Fin n → E), ∀ z, ∑ i, inner Aᵐᵒᵖ (x i) z • x i = z) ↔
      Module.Finite Aᵐᵒᵖ E ∧ Module.Projective Aᵐᵒᵖ E :=
  exists_isParsevalFrame_iff_finite_projective

/-! ### Existence of complete Hilbert module structures and frame-formula polar unitaries -/

/-- Every algebraic finitely generated projective right `A`-module `M` (with compatible complex
scalar multiplication, for example via `Module.compHom M (algebraMap ℂ Aᵐᵒᵖ)`) admits a complete
right Hilbert `A`-module structure extending its given additive group and module structures. -/
theorem exists_completeSpace_cstarModule_of_finite_projective {M : Type*}
    [instAdd : AddCommGroup M] [instModC : Module ℂ M] [Module Aᵐᵒᵖ M] [IsScalarTower ℂ Aᵐᵒᵖ M]
    [Module.Finite Aᵐᵒᵖ M] [Module.Projective Aᵐᵒᵖ M] :
    ∃ (inst₁ : NormedAddCommGroup M) (inst₂ : @NormedSpace ℂ M _ inst₁.toSeminormedAddCommGroup),
      inst₁.toAddCommGroup = instAdd ∧ inst₂.toSMul = instModC.toSMul ∧
        @CompleteSpace M inst₁.toUniformSpace ∧
        let _ : Norm M := inst₁.toNorm
        Nonempty (CStarModule Aᵐᵒᵖ M) := by
  obtain ⟨n, f₀, g₀, _, hg₀_inj, hfg₀⟩ := Module.Finite.exists_comp_eq_id_of_projective Aᵐᵒᵖ M
  set F_n := C⋆ᵐᵒᵈ(Aᵐᵒᵖ, Fin n → A)
  have : IsScalarTower ℂ Aᵐᵒᵖ F_n := CStarModule.isScalarTower Aᵐᵒᵖ F_n
  let e_pi : (Fin n → Aᵐᵒᵖ) ≃ₗ[Aᵐᵒᵖ] F_n := piOpLinearEquiv A (Fin n)
  let f : F_n →ₗ[Aᵐᵒᵖ] M := f₀ ∘ₗ e_pi.symm.toLinearMap
  let g : M →ₗ[Aᵐᵒᵖ] F_n := e_pi.toLinearMap ∘ₗ g₀
  have hg_inj : Function.Injective g := e_pi.injective.comp hg₀_inj
  have hfg_apply (m : M) : f (g m) = m := LinearMap.congr_fun hfg₀ m
  let gC : M →ₗ[ℂ] F_n := g.restrictScalars ℂ
  let inst₁ : NormedAddCommGroup M := NormedAddCommGroup.induced M F_n gC hg_inj
  let inst₂ : @NormedSpace ℂ M _ inst₁.toSeminormedAddCommGroup :=
    NormedSpace.induced ℂ M F_n gC
  refine ⟨inst₁, inst₂, rfl, rfl, ?_, ?_⟩
  · let _ : NormedAddCommGroup M := inst₁
    let e : Fin n → F_n :=
      fun i ↦ (WithCStarModule.equiv Aᵐᵒᵖ (Fin n → A)).symm (Pi.single i (1 : A))
    let P : F_n →ₗ[Aᵐᵒᵖ] F_n := g ∘ₗ f
    let PL : F_n →L[ℂ] F_n := frameSynthesisCLM A (fun i ↦ P (e i))
    have hPL (v : F_n) : PL v = g (f v) := (eq_frameSynthesisCLM_of_linearMap P v).symm
    have hidem : IsIdempotentElem PL := by
      change PL.comp PL = PL
      ext v i
      simp [hPL, hfg_apply]
    have hrange : Set.range g = (PL.range : Set F_n) := by
      ext w
      rw [Set.mem_range, SetLike.mem_coe, LinearMap.mem_range]
      exact ⟨fun ⟨m, hm⟩ ↦ ⟨g m, by change PL (g m) = w; rw [hPL, hfg_apply, hm]⟩,
        fun ⟨v, hv⟩ ↦ ⟨f v, by have hv' : PL v = w := hv; rwa [hPL] at hv'⟩⟩
    have hisom : Isometry g := AddMonoidHomClass.isometry_of_norm gC fun _ ↦ rfl
    refine hisom.isUniformInducing.completeSpace ?_
    rw [hrange]
    exact (ContinuousLinearMap.IsIdempotentElem.isClosed_range hidem).isComplete
  · let _ : NormedAddCommGroup M := inst₁
    exact ⟨{
      inner x y := inner Aᵐᵒᵖ (g x) (g y)
      inner_add_right {x y z} := by simp [inner_add_right]
      inner_self_nonneg {x} := inner_self_nonneg
      inner_self {x} := by simp [inner_self, map_eq_zero_iff g hg_inj]
      inner_op_smul_right {a x y} := by simp [inner_op_smul_right]
      inner_smul_right_complex {c x y} := by simp
      star_inner x y := star_inner (g x) (g y)
      norm_eq_sqrt_norm_inner_self {x} :=
        norm_eq_sqrt_norm_inner_self (A := Aᵐᵒᵖ) (x := g x) }⟩

omit [StarOrderedRing A] in
/-- Explicit frame-formula adjoint `y ↦ ∑ i, x i ⟨T (x i), y⟩_A` of any right `A`-linear map
`T : E →ₗ[Aᵐᵒᵖ] F` out of a right Hilbert `A`-module `E` equipped with a finite Parseval frame
`x : ι → E`. Neither continuity of `T` nor completeness of `E` or `F` is assumed. -/
noncomputable def IsParsevalFrame.adjoint {ι : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [Module Aᵐᵒᵖ E] [CStarModule Aᵐᵒᵖ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [Module Aᵐᵒᵖ F] [CStarModule Aᵐᵒᵖ F]
    {x : ι → E} (_hx : IsParsevalFrame Aᵐᵒᵖ x) (T : E →ₗ[Aᵐᵒᵖ] F) : F →ₗ[Aᵐᵒᵖ] E where
  toFun y := ∑ i, inner Aᵐᵒᵖ (T (x i)) y • x i
  map_add' y₁ y₂ := by simp [inner_add_right, add_smul, Finset.sum_add_distrib]
  map_smul' a y := by simp [inner_op_smul_right, mul_smul, Finset.smul_sum]

omit [StarOrderedRing A] in
@[simp]
theorem IsParsevalFrame.adjoint_apply {ι : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [Module Aᵐᵒᵖ E] [CStarModule Aᵐᵒᵖ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [Module Aᵐᵒᵖ F] [CStarModule Aᵐᵒᵖ F]
    {x : ι → E} (hx : IsParsevalFrame Aᵐᵒᵖ x) (T : E →ₗ[Aᵐᵒᵖ] F) (y : F) :
    hx.adjoint T y = ∑ i, inner Aᵐᵒᵖ (T (x i)) y • x i := (rfl)

omit [StarOrderedRing A] in
/-- Every right `A`-linear map `T : E →ₗ[Aᵐᵒᵖ] F` out of a module with a finite Parseval frame
`x : ι → E` forms a module adjoint pair with `hx.adjoint T`. -/
theorem IsParsevalFrame.isAdjointPair_adjoint {ι : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [Module Aᵐᵒᵖ E] [CStarModule Aᵐᵒᵖ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [Module Aᵐᵒᵖ F] [CStarModule Aᵐᵒᵖ F]
    {x : ι → E} (hx : IsParsevalFrame Aᵐᵒᵖ x) (T : E →ₗ[Aᵐᵒᵖ] F) :
    LinearMap.IsAdjointPair (innerₛₗ (A := Aᵐᵒᵖ) (E := E)).flip
      (innerₛₗ (A := Aᵐᵒᵖ) (E := F)).flip T (hx.adjoint T) := by
  rw [isAdjointPair_inner_iff]
  intro z y
  apply unop_injective
  conv_lhs => rw [← hx z, map_sum]
  simp only [T.map_smul, inner_sum_left, inner_sum_right, inner_op_smul_left, inner_op_smul_right,
    IsParsevalFrame.adjoint_apply, Finset.unop_sum, unop_mul, star_inner]

/-- Every right `A`-linear map out of a complete finitely generated projective right Hilbert
`A`-module is automatically adjointable. -/
theorem exists_isAdjointPair_of_finite_projective
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] [Module Aᵐᵒᵖ E]
    [CStarModule Aᵐᵒᵖ E] [Module.Finite Aᵐᵒᵖ E] [Module.Projective Aᵐᵒᵖ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [Module Aᵐᵒᵖ F] [CStarModule Aᵐᵒᵖ F]
    (T : E →ₗ[Aᵐᵒᵖ] F) :
    ∃ S : F →ₗ[Aᵐᵒᵖ] E,
      LinearMap.IsAdjointPair (innerₛₗ (A := Aᵐᵒᵖ) (E := E)).flip
        (innerₛₗ (A := Aᵐᵒᵖ) (E := F)).flip T S := by
  obtain ⟨_, _, hx⟩ :=
    exists_isParsevalFrame_iff_finite_projective.mpr ⟨‹_›, ‹_›⟩
  exact ⟨hx.adjoint T, hx.isAdjointPair_adjoint T⟩

section Polar

variable {ι : Type*} [Fintype ι]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [Module Aᵐᵒᵖ E] [CStarModule Aᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [Module Aᵐᵒᵖ F] [CStarModule Aᵐᵒᵖ F]

/-- Strictly positive matrix `M_T = gram A (T ∘ x) + (1 - gram A x)` representing `T* T ⊕ 1` on
`C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)` for a Parseval frame `x : ι → E` and a right `A`-linear equivalence
`T : E ≃ₗ[Aᵐᵒᵖ] F`. -/
private noncomputable def polarMatrix [DecidableEq ι] {x : ι → E} (_hx : IsParsevalFrame Aᵐᵒᵖ x)
    (T : E ≃ₗ[Aᵐᵒᵖ] F) : CStarMatrix ι ι A :=
  CStarMatrix.gram A (fun i ↦ T (x i)) + (1 - CStarMatrix.gram A x)

private theorem polarMatrix_nonneg [DecidableEq ι] {x : ι → E} (hx : IsParsevalFrame Aᵐᵒᵖ x)
    (T : E ≃ₗ[Aᵐᵒᵖ] F) : 0 ≤ polarMatrix hx T :=
  add_nonneg (CStarMatrix.gram_nonneg _) hx.isStarProjection_gram.one_sub.nonneg

private theorem polarMatrix_mul_gram [DecidableEq ι] {x : ι → E} (hx : IsParsevalFrame Aᵐᵒᵖ x)
    (T : E ≃ₗ[Aᵐᵒᵖ] F) :
    polarMatrix hx T * CStarMatrix.gram A x = CStarMatrix.gram A (fun i ↦ T (x i)) := by
  rw [polarMatrix, add_mul, hx.isStarProjection_gram.one_sub_mul_self, add_zero]
  ext i j
  simp only [CStarMatrix.mul_apply, CStarMatrix.gram_apply]
  have hsum :
      ∑ k, unop (inner Aᵐᵒᵖ (T (x i)) (T (x k))) * unop (inner Aᵐᵒᵖ (x k) (x j)) =
        unop (inner Aᵐᵒᵖ (T (x i)) (T (∑ k, inner Aᵐᵒᵖ (x k) (x j) • x k))) := by
    simp [map_sum, inner_sum_right, Finset.unop_sum]
  rw [hsum, hx (x j)]

private theorem commute_polarMatrix_gram [DecidableEq ι] {x : ι → E} (hx : IsParsevalFrame Aᵐᵒᵖ x)
    (T : E ≃ₗ[Aᵐᵒᵖ] F) : Commute (polarMatrix hx T) (CStarMatrix.gram A x) := by
  have hsa₁ := (polarMatrix_nonneg hx T).isSelfAdjoint.star_eq
  have hsa₂ := hx.isStarProjection_gram.isSelfAdjoint.star_eq
  have hsa₃ := (CStarMatrix.gram_nonneg (A := A) (fun i ↦ T (x i))).isSelfAdjoint.star_eq
  rw [Commute, SemiconjBy, polarMatrix_mul_gram hx T]
  calc CStarMatrix.gram A (fun i ↦ T (x i))
      = star (polarMatrix hx T * CStarMatrix.gram A x) := by rw [polarMatrix_mul_gram hx T, hsa₃]
    _ = CStarMatrix.gram A x * polarMatrix hx T := by rw [star_mul, hsa₂, hsa₁]

variable [CompleteSpace F]

private theorem isUnit_sqrt_polarMatrix [DecidableEq ι] {x : ι → E} (hx : IsParsevalFrame Aᵐᵒᵖ x)
    (T : E ≃ₗ[Aᵐᵒᵖ] F) : IsUnit (CFC.sqrt (polarMatrix hx T)) := by
  have : CompleteSpace E := hx.completeSpace
  have : IsScalarTower ℂ Aᵐᵒᵖ E := CStarModule.isScalarTower Aᵐᵒᵖ E
  have : IsScalarTower ℂ Aᵐᵒᵖ F := CStarModule.isScalarTower Aᵐᵒᵖ F
  have hT_cont : Continuous T := (hx.isAdjointPair_adjoint T.toLinearMap).continuous_cstarModule
  have hTsymm_cont : Continuous T.symm := (T.restrictScalars ℂ).continuous_symm hT_cont
  let TinvL : F →L[ℂ] E :=
    { toLinearMap := T.symm.toLinearMap.restrictScalars ℂ, cont := hTsymm_cont }
  set p := CStarMatrix.gram A x
  have hp : IsStarProjection p := hx.isStarProjection_gram
  set M := polarMatrix hx T
  set δ : ℝ := (2 * (1 + ‖TinvL‖ ^ 2))⁻¹
  have hδ : 0 < δ := by positivity
  have hM_ge : algebraMap ℝ (CStarMatrix ι ι A) δ ≤ M := by
    rw [← sub_nonneg, Algebra.algebraMap_eq_smul_one, CStarMatrix.nonneg_iff_forall_sum_nonneg]
    intro a
    let w : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A) := (WithCStarModule.equiv Aᵐᵒᵖ (ι → A)).symm a
    have hquad_GT :
        ∑ i, ∑ j, star (a i) * CStarMatrix.gram A (fun k ↦ T (x k)) i j * a j =
          unop (inner Aᵐᵒᵖ (T (frameSynthesisLinearMap A x w))
            (T (frameSynthesisLinearMap A x w))) := by
      rw [CStarMatrix.sum_star_mul_gram_mul]
      simp [frameSynthesisLinearMap_apply, map_sum, w]
    have h1p_vec :
        CStarMatrix.mulVecCLM (1 - p) w = w - frameAnalysisCLM A x (frameSynthesisCLM A x w) := by
      rw [frameAnalysisCLM_frameSynthesisCLM_apply]
      ext i
      simp only [CStarMatrix.mulVecCLM_apply_apply, CStarMatrix.sub_apply, sub_mul,
        Finset.sum_sub_distrib, WithCStarModule.sub_apply, CStarMatrix.one_apply, ite_mul,
        one_mul, zero_mul, WithCStarModule.equiv_symm_pi_apply, w]
      rw [Finset.sum_ite_eq_of_mem Finset.univ i a (Finset.mem_univ i)]
    have hquad_1p :
        ∑ i, ∑ j, star (a i) * (1 - p) i j * a j =
          unop (inner Aᵐᵒᵖ (w - frameAnalysisCLM A x (frameSynthesisCLM A x w))
            (w - frameAnalysisCLM A x (frameSynthesisCLM A x w))) := by
      have hadj := (CStarMatrix.isAdjointPair_mulVecCLM_star (1 - p)).inner_eq_cstarModule
        w (CStarMatrix.mulVecCLM (1 - p) w)
      have hinner :
          inner Aᵐᵒᵖ (CStarMatrix.mulVecCLM (1 - p) w) (CStarMatrix.mulVecCLM (1 - p) w) =
            inner Aᵐᵒᵖ w (CStarMatrix.mulVecCLM (1 - p) w) := by
        rw [hadj, ← ContinuousLinearMap.comp_apply, CStarMatrix.mulVecCLM_comp,
          hp.one_sub.isSelfAdjoint.star_eq, hp.one_sub.isIdempotentElem.eq]
      rw [← h1p_vec, hinner]
      simp [WithCStarModule.pi_inner, Finset.unop_sum, mul_assoc, w]
    have hquad_one :
        ∑ i, ∑ j, star (a i) * (δ • (1 : CStarMatrix ι ι A)) i j * a j =
          δ • unop (inner Aᵐᵒᵖ w w) := by
      have hw_inner : unop (inner Aᵐᵒᵖ w w) = ∑ i, star (a i) * a i := by
        simp [WithCStarModule.pi_inner, Finset.unop_sum, w]
      simp [CStarMatrix.one_apply, ite_mul, mul_ite, ← Finset.smul_sum, hw_inner]
    have hquad_sub :
        ∑ i, ∑ j, star (a i) * (M - δ • (1 : CStarMatrix ι ι A)) i j * a j =
          (unop (inner Aᵐᵒᵖ (T (frameSynthesisLinearMap A x w))
              (T (frameSynthesisLinearMap A x w))) +
            unop (inner Aᵐᵒᵖ (w - frameAnalysisCLM A x (frameSynthesisCLM A x w))
              (w - frameAnalysisCLM A x (frameSynthesisCLM A x w)))) -
            δ • unop (inner Aᵐᵒᵖ w w) := by
      rw [← hquad_GT, ← hquad_1p, ← hquad_one, ← Finset.sum_add_distrib,
        ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      change star (a i) *
          ((CStarMatrix.gram A (fun k ↦ T (x k)) i j + (1 - p) i j) -
            (δ • (1 : CStarMatrix ι ι A)) i j) * a j = _
      noncomm_ring
    rw [hquad_sub, sub_nonneg]
    set z := frameSynthesisLinearMap A x w
    have hΘz :
        unop (inner Aᵐᵒᵖ (frameAnalysisCLM A x z) (frameAnalysisCLM A x z)) =
          unop (inner Aᵐᵒᵖ z z) :=
      congrArg unop (isParsevalFrame_iff_inner_frameAnalysisCLM.mp hx z z)
    have hz_bound :
        unop (inner Aᵐᵒᵖ z z) ≤ ‖TinvL‖ ^ 2 • unop (inner Aᵐᵒᵖ (T z) (T z)) := by
      have h := unop_inner_apply_self_le TinvL (fun b y ↦ T.symm.map_smul (op b) y) (T z)
      have hTinv : TinvL (T z) = z := T.symm_apply_apply z
      rwa [hTinv] at h
    have hw_split :
        unop (inner Aᵐᵒᵖ w w) ≤
          (2 : ℝ) • (unop (inner Aᵐᵒᵖ z z) +
            unop (inner Aᵐᵒᵖ (w - frameAnalysisCLM A x (frameSynthesisCLM A x w))
              (w - frameAnalysisCLM A x (frameSynthesisCLM A x w)))) := by
      have hadd := unop_le_unop.mpr
        (inner_add_self_le (A := Aᵐᵒᵖ) (frameAnalysisCLM A x z) (w - frameAnalysisCLM A x z))
      rw [add_sub_cancel, unop_smul, ← ofNat_smul_eq_nsmul ℝ 2, unop_add, hΘz] at hadd
      exact hadd
    refine inv_two_one_add_smul_le (unop_nonneg.mpr inner_self_nonneg)
      (unop_nonneg.mpr inner_self_nonneg) (sq_nonneg _) (hw_split.trans ?_)
    gcongr
  have : ContinuousFunctionalCalculus ℝ (CStarMatrix ι ι A) IsSelfAdjoint :=
    IsSelfAdjoint.instContinuousFunctionalCalculus
  have hsp : IsStrictlyPositive (algebraMap ℝ (CStarMatrix ι ι A) √δ) :=
    IsStrictlyPositive.iff_of_unital.mpr
      ⟨algebraMap_nonneg _ (Real.sqrt_nonneg δ),
        (isUnit_iff_ne_zero.mpr (Real.sqrt_ne_zero'.mpr hδ)).map (algebraMap ℝ _)⟩
  exact CStarAlgebra.isUnit_of_le _ (CFC.algebraMap_le_sqrt hM_ge) hsp

/-- Positive self-adjoint modulus `|T| : E ≃ₗ[Aᵐᵒᵖ] E` of a right `A`-linear equivalence
`T : E ≃ₗ[Aᵐᵒᵖ] F`, constructed in frame coordinates from a Parseval frame `x : ι → E` by
`|T| z = Φ (CFC.sqrt (gram A (T ∘ x) + (1 - gram A x)) *ᵥ Θ z)`. -/
noncomputable def IsParsevalFrame.polarModulus {x : ι → E} (hx : IsParsevalFrame Aᵐᵒᵖ x)
    (T : E ≃ₗ[Aᵐᵒᵖ] F) : E ≃ₗ[Aᵐᵒᵖ] E := by
  classical
  let S := CFC.sqrt (polarMatrix hx T)
  let B : CStarMatrix ι ι A := ↑(isUnit_sqrt_polarMatrix hx T).unit⁻¹
  have hSB : S * B = 1 := IsUnit.mul_val_inv (isUnit_sqrt_polarMatrix hx T)
  have hBS : B * S = 1 := IsUnit.val_inv_mul (isUnit_sqrt_polarMatrix hx T)
  have hcomm_S : Commute S (CStarMatrix.gram A x) :=
    (commute_polarMatrix_gram hx T).cfcₙ_nnreal NNReal.sqrt
  have hcomm_B : Commute B (CStarMatrix.gram A x) := by
    rw [Commute, SemiconjBy]
    calc B * CStarMatrix.gram A x = B * CStarMatrix.gram A x * (S * B) := by rw [hSB, mul_one]
      _ = B * (CStarMatrix.gram A x * S) * B := by noncomm_ring
      _ = (B * S) * CStarMatrix.gram A x * B := by rw [← hcomm_S.eq]; noncomm_ring
      _ = CStarMatrix.gram A x * B := by rw [hBS, one_mul]
  let f : E →ₗ[Aᵐᵒᵖ] E :=
    (frameSynthesisLinearMap A x).comp
      ((CStarMatrix.mulVecLinearMap S).comp (frameAnalysisLinearMap A x))
  let g : E →ₗ[Aᵐᵒᵖ] E :=
    (frameSynthesisLinearMap A x).comp
      ((CStarMatrix.mulVecLinearMap B).comp (frameAnalysisLinearMap A x))
  have hpΘ (z : E) :
      CStarMatrix.mulVecLinearMap (CStarMatrix.gram A x) (frameAnalysisLinearMap A x z) =
        frameAnalysisLinearMap A x z := by
    rw [← frameAnalysisLinearMap_comp_frameSynthesisLinearMap, LinearMap.comp_apply,
      coe_frameSynthesisLinearMap, coe_frameAnalysisLinearMap,
      frameSynthesisCLM_frameAnalysisCLM_apply, hx z]
  refine LinearEquiv.ofLinearMap f g ?_ ?_
  · ext z
    have hmul : S * (CStarMatrix.gram A x * B) = CStarMatrix.gram A x := by
      rw [← hcomm_B.eq, ← mul_assoc, hSB, one_mul]
    calc f (g z)
        = frameSynthesisLinearMap A x
            (CStarMatrix.mulVecLinearMap (S * (CStarMatrix.gram A x * B))
              (frameAnalysisLinearMap A x z)) := by
          simp only [f, g, LinearMap.comp_apply, ← CStarMatrix.mulVecLinearMap_comp,
            ← frameAnalysisLinearMap_comp_frameSynthesisLinearMap]
      _ = z := by
          rw [hmul, hpΘ]
          simpa using hx z
  · ext z
    have hmul : B * (CStarMatrix.gram A x * S) = CStarMatrix.gram A x := by
      rw [← hcomm_S.eq, ← mul_assoc, hBS, one_mul]
    calc g (f z)
        = frameSynthesisLinearMap A x
            (CStarMatrix.mulVecLinearMap (B * (CStarMatrix.gram A x * S))
              (frameAnalysisLinearMap A x z)) := by
          simp only [f, g, LinearMap.comp_apply, ← CStarMatrix.mulVecLinearMap_comp,
            ← frameAnalysisLinearMap_comp_frameSynthesisLinearMap]
      _ = z := by
          rw [hmul, hpΘ]
          simpa using hx z

/-- `hx.polarModulus T` is self-adjoint as a module operator on `E`. -/
theorem IsParsevalFrame.isAdjointPair_polarModulus {x : ι → E} (hx : IsParsevalFrame Aᵐᵒᵖ x)
    (T : E ≃ₗ[Aᵐᵒᵖ] F) :
    LinearMap.IsAdjointPair (innerₛₗ (A := Aᵐᵒᵖ) (E := E)).flip
      (innerₛₗ (A := Aᵐᵒᵖ) (E := E)).flip (hx.polarModulus T) (hx.polarModulus T) := by
  classical
  rw [isAdjointPair_inner_iff]
  intro y z
  set S := CFC.sqrt (polarMatrix hx T)
  have hS_sa : star S = S := (CFC.sqrt_nonneg (polarMatrix hx T)).isSelfAdjoint.star_eq
  have hadj_ΦΘ := isAdjointPair_frameSynthesisCLM_frameAnalysisCLM (A := A) x
  have hadj_S := CStarMatrix.isAdjointPair_mulVecCLM_star S
  change inner Aᵐᵒᵖ (frameSynthesisCLM A x (CStarMatrix.mulVecCLM S (frameAnalysisCLM A x y))) z =
    inner Aᵐᵒᵖ y (frameSynthesisCLM A x (CStarMatrix.mulVecCLM S (frameAnalysisCLM A x z)))
  rw [hadj_ΦΘ.inner_eq_cstarModule, hadj_S.inner_eq_cstarModule, hS_sa,
    hadj_ΦΘ.symm_cstarModule.inner_eq_cstarModule]

/-- `hx.polarModulus T` is positive: `0 ≤ ⟨z, |T| z⟩_A` for all `z : E`. -/
theorem IsParsevalFrame.polarModulus_inner_nonneg {x : ι → E} (hx : IsParsevalFrame Aᵐᵒᵖ x)
    (T : E ≃ₗ[Aᵐᵒᵖ] F) (z : E) : 0 ≤ inner Aᵐᵒᵖ z (hx.polarModulus T z) := by
  classical
  set S := CFC.sqrt (polarMatrix hx T)
  set R := CFC.sqrt S
  have hR_sa : star R = R := (CFC.sqrt_nonneg S).isSelfAdjoint.star_eq
  have hR_sq : R * R = S := CFC.sqrt_mul_sqrt_self S (CFC.sqrt_nonneg _)
  have hadj_ΦΘ := (isAdjointPair_frameSynthesisCLM_frameAnalysisCLM (A := A) x).symm_cstarModule
  have hadj_R := CStarMatrix.isAdjointPair_mulVecCLM_star R
  have hRR (v : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)) :
      CStarMatrix.mulVecCLM S v = CStarMatrix.mulVecCLM (star R) (CStarMatrix.mulVecCLM R v) := by
    rw [hR_sa, ← ContinuousLinearMap.comp_apply, CStarMatrix.mulVecCLM_comp, hR_sq]
  change 0 ≤ inner Aᵐᵒᵖ z
    (frameSynthesisCLM A x (CStarMatrix.mulVecCLM S (frameAnalysisCLM A x z)))
  rw [← hadj_ΦΘ.inner_eq_cstarModule, hRR, ← hadj_R.inner_eq_cstarModule]
  exact inner_self_nonneg

/-- `hx.polarModulus T` has the same Gram inner products as `T`:
`⟨|T| y, |T| z⟩_A = ⟨T y, T z⟩_A`. -/
theorem IsParsevalFrame.inner_polarModulus {x : ι → E} (hx : IsParsevalFrame Aᵐᵒᵖ x)
    (T : E ≃ₗ[Aᵐᵒᵖ] F) (y z : E) :
    inner Aᵐᵒᵖ (hx.polarModulus T y) (hx.polarModulus T z) = inner Aᵐᵒᵖ (T y) (T z) := by
  classical
  apply unop_injective
  set S := CFC.sqrt (polarMatrix hx T)
  have hS_sa : star S = S := (CFC.sqrt_nonneg (polarMatrix hx T)).isSelfAdjoint.star_eq
  have hS_sq : S * S = polarMatrix hx T := CFC.sqrt_mul_sqrt_self _ (polarMatrix_nonneg hx T)
  have hcomm_S : Commute S (CStarMatrix.gram A x) :=
    (commute_polarMatrix_gram hx T).cfcₙ_nnreal NNReal.sqrt
  have hSpS : S * CStarMatrix.gram A x * S = CStarMatrix.gram A (fun i ↦ T (x i)) := by
    rw [mul_assoc, ← hcomm_S.eq, ← mul_assoc, hS_sq, polarMatrix_mul_gram hx T]
  have hadj_ΦΘ := isAdjointPair_frameSynthesisCLM_frameAnalysisCLM (A := A) x
  have hadj_S := CStarMatrix.isAdjointPair_mulVecCLM_star S
  change unop (inner Aᵐᵒᵖ
    (frameSynthesisCLM A x (CStarMatrix.mulVecCLM S (frameAnalysisCLM A x y)))
    (frameSynthesisCLM A x (CStarMatrix.mulVecCLM S (frameAnalysisCLM A x z)))) =
      unop (inner Aᵐᵒᵖ (T y) (T z))
  rw [hadj_ΦΘ.inner_eq_cstarModule, frameAnalysisCLM_frameSynthesisCLM_apply,
    hadj_S.inner_eq_cstarModule, hS_sa, ← ContinuousLinearMap.comp_apply,
    ← ContinuousLinearMap.comp_apply, CStarMatrix.mulVecCLM_comp, CStarMatrix.mulVecCLM_comp,
    hSpS]
  have hquad := CStarMatrix.sum_star_mul_gram_mul (A := A) (fun i ↦ T (x i))
    (frameAnalysisCLM A x y) (frameAnalysisCLM A x z)
  have hTy : ∑ i, op (frameAnalysisCLM A x y i) • T (x i) = T y := by
    conv_rhs => rw [← hx y, map_sum]
    simp
  have hTz : ∑ j, op (frameAnalysisCLM A x z j) • T (x j) = T z := by
    conv_rhs => rw [← hx z, map_sum]
    simp
  rw [hTy, hTz] at hquad
  simpa [WithCStarModule.pi_inner, Finset.unop_sum, CStarMatrix.mulVecCLM_apply_apply,
    Finset.mul_sum, mul_assoc] using hquad

/-- Polar unitary `U = T ∘ |T|⁻¹ : E ≃ₗᵢ[Aᵐᵒᵖ] F` of a right `A`-linear equivalence
`T : E ≃ₗ[Aᵐᵒᵖ] F`, constructed via the frame formulas of `hx : IsParsevalFrame Aᵐᵒᵖ x`. -/
noncomputable def IsParsevalFrame.polarUnitary {x : ι → E} (hx : IsParsevalFrame Aᵐᵒᵖ x)
    (T : E ≃ₗ[Aᵐᵒᵖ] F) : E ≃ₗᵢ[Aᵐᵒᵖ] F :=
  ((hx.polarModulus T).symm.trans T).isometryOfInnerCStarModule fun z ↦ by
    simp only [LinearEquiv.trans_apply]
    rw [← hx.inner_polarModulus T, LinearEquiv.apply_symm_apply]

theorem IsParsevalFrame.polarUnitary_apply {x : ι → E} (hx : IsParsevalFrame Aᵐᵒᵖ x)
    (T : E ≃ₗ[Aᵐᵒᵖ] F) (z : E) :
    hx.polarUnitary T z = T ((hx.polarModulus T).symm z) := by
  simp [IsParsevalFrame.polarUnitary]

theorem IsParsevalFrame.polarUnitary_symm_apply {x : ι → E} (hx : IsParsevalFrame Aᵐᵒᵖ x)
    (T : E ≃ₗ[Aᵐᵒᵖ] F) (w : F) :
    (hx.polarUnitary T).symm w = hx.polarModulus T (T.symm w) := by
  simp [IsParsevalFrame.polarUnitary]

@[simp]
theorem IsParsevalFrame.polarUnitary_polarModulus_apply {x : ι → E} (hx : IsParsevalFrame Aᵐᵒᵖ x)
    (T : E ≃ₗ[Aᵐᵒᵖ] F) (z : E) :
    hx.polarUnitary T (hx.polarModulus T z) = T z := by
  simp [IsParsevalFrame.polarUnitary]

end Polar

/-- Every right `A`-linear equivalence `T : E ≃ₗ[Aᵐᵒᵖ] F` between complete finitely generated
projective right Hilbert `A`-modules admits a polar decomposition `T = U ∘ |T|` into a self-adjoint
positive module automorphism `|T| : E ≃ₗ[Aᵐᵒᵖ] E` and a unitary isomorphism `U : E ≃ₗᵢ[Aᵐᵒᵖ] F`. -/
theorem exists_polar_linearIsometryEquiv_of_finite_projective
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] [Module Aᵐᵒᵖ E]
    [CStarModule Aᵐᵒᵖ E] [Module.Finite Aᵐᵒᵖ E] [Module.Projective Aᵐᵒᵖ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] [Module Aᵐᵒᵖ F]
    [CStarModule Aᵐᵒᵖ F] (T : E ≃ₗ[Aᵐᵒᵖ] F) :
    ∃ (U : E ≃ₗᵢ[Aᵐᵒᵖ] F) (P : E ≃ₗ[Aᵐᵒᵖ] E),
      LinearMap.IsAdjointPair (innerₛₗ (A := Aᵐᵒᵖ) (E := E)).flip
        (innerₛₗ (A := Aᵐᵒᵖ) (E := E)).flip P P ∧
      (∀ z : E, 0 ≤ inner Aᵐᵒᵖ z (P z)) ∧
      (∀ z : E, U (P z) = T z) := by
  obtain ⟨_, _, hx⟩ :=
    exists_isParsevalFrame_iff_finite_projective.mpr ⟨‹_›, ‹_›⟩
  exact ⟨hx.polarUnitary T, hx.polarModulus T, hx.isAdjointPair_polarModulus T,
    hx.polarModulus_inner_nonneg T, hx.polarUnitary_polarModulus_apply T⟩

/-- Two complete finitely generated projective right Hilbert `A`-modules are unitarily isomorphic
(`E ≃ₗᵢ[Aᵐᵒᵖ] F`) if and only if they are algebraically isomorphic as right `A`-modules
(`E ≃ₗ[Aᵐᵒᵖ] F`). In particular, the complete Hilbert `A`-module structure on any finitely generated
projective right `A`-module is unique up to unitary isomorphism. -/
theorem nonempty_linearIsometryEquiv_iff_nonempty_linearEquiv
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] [Module Aᵐᵒᵖ E]
    [CStarModule Aᵐᵒᵖ E] [Module.Finite Aᵐᵒᵖ E] [Module.Projective Aᵐᵒᵖ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] [Module Aᵐᵒᵖ F]
    [CStarModule Aᵐᵒᵖ F] :
    Nonempty (E ≃ₗᵢ[Aᵐᵒᵖ] F) ↔ Nonempty (E ≃ₗ[Aᵐᵒᵖ] F) :=
  ⟨fun ⟨U⟩ ↦ ⟨U.toLinearEquiv⟩, fun ⟨T⟩ ↦
    let ⟨U, _, _, _, _⟩ := exists_polar_linearIsometryEquiv_of_finite_projective T
    ⟨U⟩⟩

end FiniteProjective

end CStarModule

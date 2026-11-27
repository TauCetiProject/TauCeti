/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Projective
public import TauCeti.Analysis.CStarAlgebra.Module.Adjointable.Compact
public import TauCeti.Analysis.CStarAlgebra.Module.Gram
public import TauCeti.Analysis.CStarAlgebra.Module.Self
public import TauCeti.Analysis.CStarAlgebra.Module.Synonym
public import TauCeti.Analysis.CStarAlgebra.Module.Unitary

/-!
# Finite Parseval frames in Hilbert C⋆-modules

A finite family `x : ι → E` in a Hilbert C⋆-module over `A` is a *Parseval frame* when every
vector is reconstructed from its inner products with the family, `z = ∑ i, ⟪x i, z⟫_A • x i`. For
a right Hilbert `B`-module (`A = Bᵐᵒᵖ`) this is the familiar `z = ∑ i, x i ⟨x i, z⟩_B`, i.e.
`∑ i, θ_{x i, x i} = id_E`.

The family sits between `E` and the standard module `A^ι = C⋆ᵐᵒᵈ(A, ι → A)` through two
adjointable operators, adjoint to each other:

* the *synthesis* operator `a ↦ ∑ i, a i • x i`, from `A^ι` to `E`;
* the *analysis* operator `z ↦ (⟪x i, z⟫_A)_i`, from `E` to `A^ι`.

Synthesis after analysis is `∑ i, θ_{x i, x i}`, so `x` is a Parseval frame exactly when the
analysis operator is an isometry for the `A`-valued inner products. Analysis after synthesis is
then a projection on `A^ι`; for right modules it is left multiplication by the Gram matrix
`(⟨x i, x j⟩_B)_(i,j)`, which is therefore a projection in `CStarMatrix ι ι B`. Thus a module with a
finite Parseval frame is a complemented submodule of a free module of finite rank: over a unital
coefficient algebra it is finitely generated and projective as an algebraic module, and its
identity operator is module-compact.

## Main declarations

* `CStarModule.IsParsevalFrame A x`: the reconstruction formula `∑ i, ⟪x i, z⟫_A • x i = z`,
  with edge cases (`CStarModule.isParsevalFrame_of_subsingleton`,
  `CStarModule.isParsevalFrame_empty_iff`), invariance (`Equiv.isParsevalFrame_comp_iff`,
  `TauCeti.CStarModuleUnitary.isParsevalFrame_comp_iff`,
  `LinearIsometryEquiv.isParsevalFrame_comp_iff`), and algebraic Parseval identity
  (`CStarModule.isParsevalFrame_iff_sum_inner_mul_star_inner`,
  `CStarModule.isParsevalFrame_iff_sum_star_unop_inner_mul_unop_inner`).
* `TauCeti.AdjointableMap.synthesis A x` and `TauCeti.AdjointableMap.analysis A x`: the synthesis
  and analysis operators, with `adjoint_synthesis`, `adjoint_analysis`, and
  `synthesis_comp_analysis` (`= ∑ i, θ_{x i, x i}`).
* `TauCeti.AdjointableMap.isParsevalFrame_iff_sum_rankOne_eq_one` and
  `TauCeti.AdjointableMap.isParsevalFrame_iff_inner_analysis_analysis`: a family is a Parseval
  frame iff its rank-one operators sum to the identity, iff its analysis operator preserves the
  `A`-valued inner product.
* `CStarModule.IsParsevalFrame.one_mem_compactOperator`: the identity operator of a module with a
  finite Parseval frame is module-compact.
* `CStarModule.IsParsevalFrame.isStarProjection_analysis_comp_synthesis` and
  `CStarMatrix.isStarProjection_gram`: for a Parseval frame, analysis after synthesis is a
  projection on `A^ι`, and for a right Hilbert module the Gram matrix is a projection;
  `TauCeti.AdjointableMap.unop_analysis_synthesis_apply` shows that the former acts as left
  multiplication by the latter.
* `CStarModule.IsParsevalFrame.completeSpace` and
  `TauCeti.CStarModule.isParsevalFrame_iff_isStarProjection_gram_and_synthesis_surjective`: a
  Hilbert C⋆-module with a finite Parseval frame is automatically complete, and a finite family in
  a right Hilbert module is a Parseval frame iff its Gram matrix is a star projection and its
  synthesis operator is surjective.
* `TauCeti.CStarModule.frameAdjoint` and `CStarModule.IsParsevalFrame.isAdjointPair_frameAdjoint`:
  explicit adjoint of any `A`-linear map out of a module with a finite Parseval frame.
* `CStarModule.isParsevalFrame_single` and `CStarModule.isParsevalFrame_single_one`: over a unital
  `A`, the standard bases of `A^ι` and `C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)` are Parseval frames.
* `CStarModule.analysisLinearMap`, `Module.Finite.of_isParsevalFrame`, and
  `Module.Projective.of_isParsevalFrame`: over a unital `A`, a module with a finite Parseval frame
  is finitely generated and projective.

## References

* John Roe, *Lectures on K-Theory and Operator Algebras*, Proposition 10.2.
* E. Christopher Lance, *Hilbert C⋆-Modules: A Toolkit for Operator Algebraists*, Chapter 1.
* Iain Raeburn and Dana P. Williams, *Morita Equivalence and Continuous-Trace C⋆-Algebras*,
  Section 2.2.
-/

public section

open CStarModule MulOpposite WithCStarModule

namespace CStarModule

/-- A finite family `x : ι → E` in a C⋆-module over `A` is a *Parseval frame* if every vector is
reconstructed from its inner products with the family: `∑ i, ⟪x i, z⟫_A • x i = z` for every `z`.
For right Hilbert `B`-modules (`A = Bᵐᵒᵖ`) this reads `z = ∑ i, x i ⟨x i, z⟩_B`, that is,
`∑ i, θ_{x i, x i} = id_E`. -/
def IsParsevalFrame (A : Type*) {E ι : Type*} [Fintype ι] [AddCommMonoid E] [SMul A E] [Inner A E]
    (x : ι → E) : Prop :=
  ∀ z : E, ∑ i, inner A (x i) z • x i = z

/-- Unfolds `IsParsevalFrame` to the reconstruction formula. -/
theorem isParsevalFrame_iff {A E ι : Type*} [Fintype ι] [AddCommMonoid E] [SMul A E] [Inner A E]
    {x : ι → E} : IsParsevalFrame A x ↔ ∀ z : E, ∑ i, inner A (x i) z • x i = z :=
  Iff.rfl

section Basic

variable {A ι κ E : Type*} [Fintype ι] [Inner A E] [AddCommMonoid E] [SMul A E]

@[simp]
theorem IsParsevalFrame.sum_inner_smul {x : ι → E} (hx : IsParsevalFrame A x) (z : E) :
    ∑ i, inner A (x i) z • x i = z :=
  isParsevalFrame_iff.mp hx z

/-- Every finite family in a subsingleton module is a Parseval frame. -/
theorem isParsevalFrame_of_subsingleton [Subsingleton E] (x : ι → E) : IsParsevalFrame A x :=
  isParsevalFrame_iff.mpr fun _ ↦ Subsingleton.elim _ _

/-- An empty family is a Parseval frame if and only if the module is subsingleton. -/
@[simp]
theorem isParsevalFrame_empty_iff [IsEmpty ι] (x : ι → E) :
    IsParsevalFrame A x ↔ Subsingleton E :=
  ⟨fun hx ↦ ⟨fun y z ↦ by rw [← hx.sum_inner_smul y, ← hx.sum_inner_smul z]; simp⟩,
    fun _ ↦ isParsevalFrame_of_subsingleton x⟩

/-- Reindexing a Parseval frame along an equivalence of finite index types preserves the Parseval
property. -/
theorem IsParsevalFrame.comp_equiv [Fintype κ] {x : ι → E} (hx : IsParsevalFrame A x)
    (e : κ ≃ ι) : IsParsevalFrame A (x ∘ e) :=
  isParsevalFrame_iff.mpr fun z ↦ by
    simpa [Function.comp_apply] using
      (e.sum_comp fun i ↦ inner A (x i) z • x i).trans (hx.sum_inner_smul z)

@[simp]
theorem _root_.Equiv.isParsevalFrame_comp_iff [Fintype κ] {x : ι → E} (e : κ ≃ ι) :
    IsParsevalFrame A (x ∘ e) ↔ IsParsevalFrame A x :=
  ⟨fun h ↦ by simpa [Function.comp_def] using h.comp_equiv e.symm, fun h ↦ h.comp_equiv e⟩

private theorem isParsevalFrame_comp_iff_of_bijective {A ι E F G : Type*} [Fintype ι]
    [Inner A E] [AddCommGroup E] [SMul A E] [Inner A F] [AddCommGroup F] [SMul A F]
    [FunLike G E F] [AddMonoidHomClass G E F] (f : G) (hf_bij : Function.Bijective f)
    (hf_smul : ∀ (a : A) (x : E), f (a • x) = a • f x)
    (hf_inner : ∀ x y : E, inner A (f x) (f y) = inner A x y) {x : ι → E} :
    IsParsevalFrame A (f ∘ x) ↔ IsParsevalFrame A x := by
  refine ⟨fun h ↦ isParsevalFrame_iff.mpr fun z ↦ hf_bij.injective ?_,
    fun h ↦ isParsevalFrame_iff.mpr fun w ↦ ?_⟩
  · simpa [Function.comp_apply, map_sum, hf_smul, hf_inner] using h.sum_inner_smul (f z)
  · obtain ⟨z, rfl⟩ := hf_bij.surjective w
    simpa [Function.comp_apply, map_sum, hf_smul, hf_inner] using
      congrArg f (h.sum_inner_smul z)

end Basic

/-- **Parseval's identity** (general algebraic form): `x : ι → E` is a Parseval frame iff
`∑ i, ⟪x i, z⟫_A * (⟪x i, z⟫_A)⋆ = ⟪z, z⟫_A` for all `z : E`. -/
theorem isParsevalFrame_iff_sum_inner_mul_star_inner {A ι E : Type*} [Fintype ι] [NonUnitalRing A]
    [StarRing A] [Module ℂ A] [PartialOrder A] [Norm A]
    [AddCommGroup E] [Module ℂ E] [SMul A E] [Norm E] [CStarModule A E] {x : ι → E} :
    IsParsevalFrame A x ↔ ∀ z : E, ∑ i, inner A (x i) z * star (inner A (x i) z) = inner A z z := by
  refine ⟨fun hx z ↦ ?_, fun h ↦ isParsevalFrame_iff.mpr fun z ↦ ?_⟩
  · conv_rhs => arg 3; rw [← hx.sum_inner_smul z]
    rw [TauCeti.CStarModule.inner_sum_right']; simp
  · let Q : E → E := fun w ↦ (∑ i, inner A (x i) w • x i) - w
    have hQ_add (u v : E) : Q (u + v) = Q u + Q v := by
      simp only [Q, CStarModule.inner_add_right, CStarModule.add_smul, Finset.sum_add_distrib]
      abel
    have hQ_sa (u v : E) : inner A u (Q v) = inner A (Q u) v := by
      have h_l : inner A (∑ i, inner A (x i) u • x i) v =
          ∑ i, inner A (x i) v * inner A u (x i) := star_injective <| by
        simp [TauCeti.CStarModule.inner_sum_right', CStarModule.inner_op_smul_right, star_sum]
      simp [Q, sub_eq_add_neg, CStarModule.inner_neg_right', CStarModule.inner_neg_left',
        TauCeti.CStarModule.inner_sum_right', h_l]
    have hQ_diag (w : E) : inner A w (Q w) = 0 := by
      have hw := h w; simp only [star_inner] at hw
      simp [Q, sub_eq_add_neg, CStarModule.inner_neg_right',
        TauCeti.CStarModule.inner_sum_right', hw]
    have h2 : (2 : ℂ) • inner A (Q z) (Q z) = 0 := by
      simpa [hQ_add, hQ_diag z, hQ_diag (Q z), hQ_sa z (Q z), ← two_smul ℂ] using hQ_diag (z + Q z)
    exact sub_eq_zero.mp <| (CStarModule.inner_self (A := A)).mp <| by
      simpa using congrArg ((2 : ℂ)⁻¹ • ·) h2

/-- **Parseval's identity** (right-module algebraic form): `x : ι → E` is a Parseval frame iff
`∑ i, ⟨x i, z⟩_A⋆ ⟨x i, z⟩_A = ⟨z, z⟩_A` for all `z : E`. -/
theorem isParsevalFrame_iff_sum_star_unop_inner_mul_unop_inner {A ι E : Type*} [Fintype ι]
    [NonUnitalRing A] [StarRing A] [Module ℂ A] [PartialOrder A] [Norm Aᵐᵒᵖ]
    [AddCommGroup E] [Module ℂ E] [SMul Aᵐᵒᵖ E] [Norm E]
    [CStarModule Aᵐᵒᵖ E] {x : ι → E} : IsParsevalFrame Aᵐᵒᵖ x ↔ ∀ z : E, ∑ i,
      star (unop (inner Aᵐᵒᵖ (x i) z)) * unop (inner Aᵐᵒᵖ (x i) z) = unop (inner Aᵐᵒᵖ z z) := by
  rw [isParsevalFrame_iff_sum_inner_mul_star_inner]
  exact ⟨fun h z ↦ by simpa only [Finset.unop_sum, unop_mul, unop_star] using congrArg unop (h z),
    fun h z ↦ unop_injective (by simpa only [Finset.unop_sum, unop_mul, unop_star] using h z)⟩

end CStarModule

namespace TauCeti.CStarModuleUnitary

variable {A ι E F : Type*} [Fintype ι] [NonUnitalRing A] [StarRing A] [Module ℂ A]
  [StarModule ℂ A] [PartialOrder A] [Norm A]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [CStarModule A E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul A F] [CStarModule A F]

/-- Over a (possibly non-unital) coefficient ring, a Hilbert C⋆-module unitary
`U : CStarModuleUnitary A E F` preserves Parseval frames. -/
@[simp]
theorem isParsevalFrame_comp_iff (U : CStarModuleUnitary A E F) {x : ι → E} :
    IsParsevalFrame A (U ∘ x) ↔ IsParsevalFrame A x :=
  CStarModule.isParsevalFrame_comp_iff_of_bijective U U.bijective U.map_smul_coeff U.inner_map_map

end TauCeti.CStarModuleUnitary

namespace LinearIsometryEquiv

variable {A ι E F : Type*} [Fintype ι] [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [SeminormedAddCommGroup E] [Module ℂ E] [Module A E] [CStarModule A E]
  [SeminormedAddCommGroup F] [Module ℂ F] [Module A F] [CStarModule A F]

/-- Over a unital C⋆-algebra, a unitary isomorphism `f : E ≃ₗᵢ[A] F` preserves Parseval frames. -/
@[simp]
theorem isParsevalFrame_comp_iff (f : E ≃ₗᵢ[A] F) {x : ι → E} :
    IsParsevalFrame A (f ∘ x) ↔ IsParsevalFrame A x :=
  CStarModule.isParsevalFrame_comp_iff_of_bijective f f.bijective f.map_smul
    f.inner_map_map_cstarModule

end LinearIsometryEquiv

namespace TauCeti.AdjointableMap

variable {A E ι : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [CStarModule A E] [Fintype ι]

/-! ### Synthesis and analysis operators -/

section Operators

variable (A) in
/-- The bounded complex-linear map `a ↦ ∑ i, a i • x i` underlying `synthesis A x`. -/
private noncomputable def synthesisCLM (x : ι → E) : C⋆ᵐᵒᵈ(A, ι → A) →L[ℂ] E :=
  LinearMap.mkContinuous
    { toFun a := ∑ i, a i • x i
      map_add' a b := by simp [CStarModule.add_smul, Finset.sum_add_distrib]
      map_smul' c a := by
        simp [Finset.smul_sum, (CStarModule.isScalarTower A E).smul_assoc] }
    (∑ i, ‖x i‖) fun a ↦ by
      refine (norm_sum_le _ _).trans ?_
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun i _ ↦ (CStarModule.norm_smul_le _ _).trans ?_
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left (norm_apply_le_norm a i) (norm_nonneg _)

variable (A) in
/-- The bounded complex-linear map `z ↦ (⟪x i, z⟫_A)_i` underlying `analysis A x`. -/
private noncomputable def analysisCLM (x : ι → E) : E →L[ℂ] C⋆ᵐᵒᵈ(A, ι → A) :=
  LinearMap.mkContinuous
    { toFun z := (WithCStarModule.equiv A (ι → A)).symm fun i ↦ inner A (x i) z
      map_add' z w := by ext i; simp [CStarModule.inner_add_right]
      map_smul' c z := by ext i; simp [inner_smul_right_complex] }
    (∑ i, ‖x i‖) fun z ↦ by
      refine (pi_norm_le_sum_norm _).trans ?_
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum fun i _ ↦ CStarModule.norm_inner_le E

variable (A) in
/-- The synthesis operator `a ↦ ∑ i, a i • x i` of a finite family `x : ι → E`, from the standard
module `A^ι = C⋆ᵐᵒᵈ(A, ι → A)` to `E`. Its adjoint is the analysis operator `analysis A x`. For
right Hilbert `B`-modules (`A = Bᵐᵒᵖ`) it is `a ↦ ∑ i, x i a i`. -/
noncomputable def synthesis (x : ι → E) : AdjointableMap A C⋆ᵐᵒᵈ(A, ι → A) E where
  toContinuousLinearMap := synthesisCLM A x
  adjoint' := analysisCLM A x
  inner_map_eq' a z := by
    simp [synthesisCLM, analysisCLM, pi_inner, WithCStarModule.inner_def, inner_sum_left,
      inner_op_smul_left]

variable (A) in
/-- The analysis operator `z ↦ (⟪x i, z⟫_A)_i` of a finite family `x : ι → E`, from `E` to the
standard module `A^ι = C⋆ᵐᵒᵈ(A, ι → A)`: the adjoint of the synthesis operator. -/
noncomputable def analysis (x : ι → E) : AdjointableMap A E C⋆ᵐᵒᵈ(A, ι → A) :=
  (synthesis A x).adjoint

@[simp]
theorem synthesis_apply (x : ι → E) (a : C⋆ᵐᵒᵈ(A, ι → A)) :
    synthesis A x a = ∑ i, a i • x i :=
  (rfl)

@[simp]
theorem analysis_apply (x : ι → E) (z : E) (i : ι) : analysis A x z i = inner A (x i) z := by
  simp [analysis, synthesis, analysisCLM]

@[simp]
theorem adjoint_synthesis (x : ι → E) : (synthesis A x).adjoint = analysis A x :=
  (rfl)

@[simp]
theorem adjoint_analysis (x : ι → E) : (analysis A x).adjoint = synthesis A x :=
  adjoint_adjoint _

/-- The synthesis operator sends the `i`-th coordinate vector with entry `a` to `a • x i`. -/
theorem synthesis_single [DecidableEq ι] (x : ι → E) (i : ι) (a : A) :
    synthesis A x ((WithCStarModule.equiv A (ι → A)).symm (Pi.single i a)) = a • x i := by
  rw [synthesis_apply, Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Pi.single_eq_of_ne hj, (CStarModule.smulWithZero A E).zero_smul]
  · simp

/-- Synthesis after analysis is the sum of the rank-one operators `θ_{x i, x i}`. -/
theorem synthesis_comp_analysis (x : ι → E) :
    (synthesis A x).comp (analysis A x) = ∑ i, rankOne A (x i) (x i) :=
  ext fun z ↦ by simp

/-- Analysis after synthesis has entries `∑ j, a j * ⟪x i, x j⟫_A`. -/
theorem analysis_synthesis_apply (x : ι → E) (a : C⋆ᵐᵒᵈ(A, ι → A)) (i : ι) :
    analysis A x (synthesis A x a) i = ∑ j, a j * inner A (x i) (x j) := by
  simp [inner_sum_right, inner_op_smul_right]

/-- For a right Hilbert `B`-module, analysis after synthesis is left multiplication by the Gram
matrix: its `i`-th entry is `∑ j, ⟨x i, x j⟩_B a j`. -/
theorem unop_analysis_synthesis_apply {B E₁ : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B]
    [StarOrderedRing B] [NormedAddCommGroup E₁] [NormedSpace ℂ E₁] [SMul Bᵐᵒᵖ E₁]
    [CStarModule Bᵐᵒᵖ E₁] (x : ι → E₁) (a : C⋆ᵐᵒᵈ(Bᵐᵒᵖ, ι → Bᵐᵒᵖ)) (i : ι) :
    unop (analysis Bᵐᵒᵖ x (synthesis Bᵐᵒᵖ x a) i) =
      ∑ j, CStarMatrix.gram B x i j * unop (a j) := by
  simp [Finset.unop_sum, inner_sum_right, inner_op_smul_right]

end Operators

/-! ### Parseval frames -/

section Parseval

/-- A family is a Parseval frame exactly when synthesis after analysis is the identity. -/
theorem isParsevalFrame_iff_synthesis_comp_analysis_eq_id {x : ι → E} :
    IsParsevalFrame A x ↔ (synthesis A x).comp (analysis A x) = .id A E := by
  simp [isParsevalFrame_iff, AdjointableMap.ext_iff]

/-- A family is a Parseval frame exactly when its rank-one operators sum to the identity,
`∑ i, θ_{x i, x i} = 1`. -/
theorem isParsevalFrame_iff_sum_rankOne_eq_one {x : ι → E} :
    IsParsevalFrame A x ↔ ∑ i, rankOne A (x i) (x i) = 1 := by
  rw [isParsevalFrame_iff_synthesis_comp_analysis_eq_id, synthesis_comp_analysis, one_def]

/-- A family is a Parseval frame exactly when its analysis operator preserves the `A`-valued inner
product: `∑ i, ⟪x i, w⟫_A * star ⟪x i, z⟫_A = ⟪z, w⟫_A` for all `z, w`. For right Hilbert
`B`-modules this is `∑ i, ⟨z, x i⟩_B ⟨x i, w⟩_B = ⟨z, w⟩_B`. -/
theorem isParsevalFrame_iff_inner_analysis_analysis {x : ι → E} :
    IsParsevalFrame A x ↔
      ∀ z w : E, inner A (analysis A x z) (analysis A x w) = inner A z w := by
  rw [isParsevalFrame_iff_synthesis_comp_analysis_eq_id, ← adjoint_analysis,
    adjoint_comp_self_eq_id_iff_inner_map_map]

end Parseval

end TauCeti.AdjointableMap

namespace CStarModule.IsParsevalFrame

open TauCeti TauCeti.AdjointableMap

variable {A E ι : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [CStarModule A E] [Fintype ι]
  {x : ι → E}

/-- For a Parseval frame, synthesis after analysis is the identity. -/
theorem synthesis_comp_analysis_eq_id (hx : IsParsevalFrame A x) :
    (synthesis A x).comp (analysis A x) = .id A E :=
  isParsevalFrame_iff_synthesis_comp_analysis_eq_id.mp hx

/-- The rank-one operators of a Parseval frame sum to the identity, `∑ i, θ_{x i, x i} = 1`. -/
theorem sum_rankOne_eq_one (hx : IsParsevalFrame A x) : ∑ i, rankOne A (x i) (x i) = 1 :=
  isParsevalFrame_iff_sum_rankOne_eq_one.mp hx

/-- The analysis operator of a Parseval frame preserves the `A`-valued inner product. -/
theorem inner_analysis_analysis (hx : IsParsevalFrame A x) (z w : E) :
    inner A (analysis A x z) (analysis A x w) = inner A z w :=
  isParsevalFrame_iff_inner_analysis_analysis.mp hx z w

/-- The analysis operator of a Parseval frame is isometric. -/
theorem norm_analysis_apply (hx : IsParsevalFrame A x) (z : E) : ‖analysis A x z‖ = ‖z‖ :=
  norm_map_of_adjoint_comp_self_eq_id
    (by rw [adjoint_analysis]; exact hx.synthesis_comp_analysis_eq_id) z

/-- The identity operator of a Hilbert C⋆-module with a finite Parseval frame is module-compact:
it is the finite sum `∑ i, θ_{x i, x i}`. -/
theorem one_mem_compactOperator (hx : IsParsevalFrame A x) :
    (1 : AdjointableMap A E E) ∈ compactOperator A E E := by
  rw [← hx.sum_rankOne_eq_one]
  exact Submodule.sum_mem _ fun i _ ↦ rankOne_mem_compactOperator _ _

/-- For a Parseval frame, analysis after synthesis is a projection on the standard module
`A^ι = C⋆ᵐᵒᵈ(A, ι → A)`. -/
theorem isStarProjection_analysis_comp_synthesis (hx : IsParsevalFrame A x) :
    IsStarProjection ((analysis A x).comp (synthesis A x)) := by
  rw [← adjoint_analysis]
  refine isStarProjection_self_comp_adjoint_of_adjoint_comp_self_eq_id ?_
  rw [adjoint_analysis]
  exact hx.synthesis_comp_analysis_eq_id

end CStarModule.IsParsevalFrame

namespace CStarMatrix

variable {B E ι : Type*} [NonUnitalRing B] [StarRing B] [Module ℂ B] [PartialOrder B] [Norm Bᵐᵒᵖ]
  [AddCommGroup E] [Module ℂ E] [SMul Bᵐᵒᵖ E] [Norm E] [CStarModule Bᵐᵒᵖ E] [Fintype ι]

/-- The Gram matrix `(⟨x i, x j⟩_B)_(i,j)` of a Parseval frame of a right Hilbert `B`-module is a
projection in `CStarMatrix ι ι B`. Only the algebraic `CStarModule` axioms are used. -/
theorem isStarProjection_gram {x : ι → E} (hx : IsParsevalFrame Bᵐᵒᵖ x) :
    IsStarProjection (gram B x) where
  isIdempotentElem := by
    ext i j
    conv_rhs => rw [gram_apply, ← hx (x j)]
    simp [mul_apply, TauCeti.CStarModule.inner_sum_right', inner_op_smul_right, Finset.unop_sum]
  isSelfAdjoint := TauCeti.CStarMatrix.isSelfAdjoint_gram x

end CStarMatrix

namespace TauCeti.CStarModule

open TauCeti

section NonUnital

/-- Over any (possibly non-unital) C⋆-algebra `A`, every Hilbert C⋆-module admitting a finite
Parseval frame is automatically complete. -/
theorem _root_.CStarModule.IsParsevalFrame.completeSpace {A ι E : Type*} [Fintype ι]
    [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [SeminormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [CStarModule A E]
    {x : ι → E} (hx : IsParsevalFrame A x) : CompleteSpace E := by
  let : NormedAddCommGroup E := NormedAddCommGroup.ofSeparation fun x ↦
    (CStarModule.norm_zero_iff A x).mp
  let f : E →ₗᵢ[ℂ] C⋆ᵐᵒᵈ(A, ι → A) :=
    (AdjointableMap.analysis A x).toContinuousLinearMap.toLinearMap.isometryOfInnerCStarModule
      fun z ↦ hx.inner_analysis_analysis z z
  exact f.isometry.isUniformInducing.completeSpace
    (Function.LeftInverse.isClosed_range (fun z ↦ by simpa [f] using hx.sum_inner_smul z)
      (AdjointableMap.synthesis A x).continuous f.continuous).isComplete

/-- Over any C⋆-algebra (possibly non-unital), a finite family `x` in a right Hilbert `A`-module
is a Parseval frame iff its Gram matrix is a star projection and its synthesis operator is
surjective. -/
theorem isParsevalFrame_iff_isStarProjection_gram_and_synthesis_surjective {A ι E : Type*}
    [Fintype ι] [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Aᵐᵒᵖ E] [CStarModule Aᵐᵒᵖ E] {x : ι → E} :
    IsParsevalFrame Aᵐᵒᵖ x ↔
      IsStarProjection (CStarMatrix.gram A x) ∧
        Function.Surjective (AdjointableMap.synthesis Aᵐᵒᵖ x) := by
  refine ⟨fun hx ↦ ⟨CStarMatrix.isStarProjection_gram hx, fun z ↦
    ⟨AdjointableMap.analysis Aᵐᵒᵖ x z, by simpa using hx.sum_inner_smul z⟩⟩,
    fun ⟨hp, hsurj⟩ ↦ isParsevalFrame_iff.mpr fun z ↦ ?_⟩
  obtain ⟨v, rfl⟩ := hsurj z
  set w := AdjointableMap.analysis Aᵐᵒᵖ x (AdjointableMap.synthesis Aᵐᵒᵖ x v) - v
  have haw : AdjointableMap.analysis Aᵐᵒᵖ x (AdjointableMap.synthesis Aᵐᵒᵖ x w) = 0 := by
    ext i
    apply unop_injective
    rw [AdjointableMap.unop_analysis_synthesis_apply]
    have hmul : ∑ j, CStarMatrix.gram A x i j *
        (unop (AdjointableMap.analysis Aᵐᵒᵖ x (AdjointableMap.synthesis Aᵐᵒᵖ x v) j) -
          unop (v j)) = 0 := by
      simp only [AdjointableMap.unop_analysis_synthesis_apply, mul_sub, Finset.sum_sub_distrib,
        Finset.mul_sum, ← mul_assoc]
      rw [Finset.sum_comm]
      have hidem (k : ι) : ∑ j, CStarMatrix.gram A x i j * CStarMatrix.gram A x j k =
          CStarMatrix.gram A x i k := by
        simpa [CStarMatrix.mul_apply] using congrFun (congrFun hp.isIdempotentElem.eq i) k
      simp_rw [← Finset.sum_mul, hidem, sub_self]
    simpa [w] using hmul
  have hΦw : AdjointableMap.synthesis Aᵐᵒᵖ x w = 0 := (inner_self (A := Aᵐᵒᵖ)).mp <| by
    rw [← (AdjointableMap.synthesis Aᵐᵒᵖ x).adjoint_inner_right,
      AdjointableMap.adjoint_synthesis, haw]
    simp
  rw [map_sub, sub_eq_zero] at hΦw
  simpa only [AdjointableMap.synthesis_apply, AdjointableMap.analysis_apply] using hΦw

end NonUnital

/-- Explicit frame-formula candidate adjoint `y ↦ ∑ i, ⟪T (x i), y⟫_A • x i` of a function
`T : E → F` with respect to a finite family `x : ι → E`. -/
def frameAdjoint (A : Type*) {ι E F : Type*} [Fintype ι] [Semiring A] [StarRing A] [Module ℂ A]
    [PartialOrder A] [Norm A] [AddCommMonoid E] [Module A E] [AddCommGroup F] [Module ℂ F]
    [Module A F] [Norm F] [CStarModule A F] (x : ι → E) (T : E → F) : F →ₗ[A] E where
  toFun y := ∑ i, inner A (T (x i)) y • x i
  map_add' _ _ := by simp [CStarModule.inner_add_right, add_smul, Finset.sum_add_distrib]
  map_smul' _ _ := by simp [inner_op_smul_right, mul_smul, Finset.smul_sum]

@[simp] theorem frameAdjoint_apply {A ι E F : Type*} [Fintype ι] [Semiring A] [StarRing A]
    [Module ℂ A] [PartialOrder A] [Norm A] [AddCommMonoid E] [Module A E] [AddCommGroup F]
    [Module ℂ F] [Module A F] [Norm F] [CStarModule A F] (x : ι → E) (T : E → F) (y : F) :
    frameAdjoint A x T y = ∑ i, inner A (T (x i)) y • x i := by simp [frameAdjoint]

/-- Every `A`-linear map `T` out of a C⋆-module equipped with a finite Parseval frame `x : ι → E`
forms a module adjoint pair with `frameAdjoint A x T`. -/
theorem _root_.CStarModule.IsParsevalFrame.isAdjointPair_frameAdjoint {A ι E F 𝓕 : Type*}
    [Fintype ι] [Ring A] [StarRing A] [Module ℂ A] [StarModule ℂ A] [PartialOrder A] [Norm A]
    [AddCommGroup E] [Module ℂ E] [Module A E] [Norm E] [CStarModule A E]
    [AddCommGroup F] [Module ℂ F] [Module A F] [Norm F] [CStarModule A F]
    [FunLike 𝓕 E F] [LinearMapClass 𝓕 A E F] {x : ι → E} (hx : IsParsevalFrame A x) (T : 𝓕) :
    LinearMap.IsAdjointPair (innerₛₗ (A := A) (E := E)).flip
      (innerₛₗ (A := A) (E := F)).flip T (frameAdjoint A x T) := by
  rw [isAdjointPair_inner_iff]; intro z y
  conv_lhs => rw [← hx.sum_inner_smul z, map_sum]
  simp only [map_smul, inner_sum_left, inner_sum_right, inner_op_smul_left, inner_op_smul_right,
    frameAdjoint_apply, star_inner]

end TauCeti.CStarModule

/-! ### The standard module and finite projectivity -/

namespace CStarModule

variable {A E ι : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Fintype ι]

/-- Over a unital C⋆-algebra `A`, the coordinate vectors of the standard module
`A^ι = C⋆ᵐᵒᵈ(A, ι → A)` form a Parseval frame. -/
theorem isParsevalFrame_single [DecidableEq ι] :
    IsParsevalFrame A fun i : ι ↦ (WithCStarModule.equiv A (ι → A)).symm (Pi.single i 1) := by
  intro z
  ext j
  -- Mathlib states the coordinates of `C⋆ᵐᵒᵈ(A, ι → A)` as plain function applications, so the
  -- motive of a rewrite by `Finset.sum_ite_eq` is not type-correct; supply it as a term.
  simpa [WithCStarModule.inner_def, Pi.single_apply] using
    Finset.sum_ite_eq_of_mem _ j (fun i ↦ z i) (Finset.mem_univ j)

/-- Over a unital C⋆-algebra `A`, the standard basis `i ↦ Pi.single i 1` of the right module
`C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)` is a Parseval frame. -/
theorem isParsevalFrame_single_one [DecidableEq ι] : IsParsevalFrame Aᵐᵒᵖ
    (fun i : ι ↦ (WithCStarModule.equiv Aᵐᵒᵖ (ι → A)).symm (Pi.single i (1 : A))) :=
  isParsevalFrame_iff.mpr fun v ↦ by
    simpa [WithCStarModule.inner_single_left, inner_mulOpposite] using
      WithCStarModule.sum_op_smul_single_one v

end CStarModule

section Projective

namespace CStarModule

variable {A E ι : Type*} [Ring A] [StarRing A] [Module ℂ A] [PartialOrder A] [Norm A]
  [AddCommGroup E] [Module ℂ E] [Module A E] [Norm E] [CStarModule A E]
  {x : ι → E}

/-- The analysis map `z ↦ (⟪x i, z⟫_A)_i` of a finite family, as an `A`-linear map to the free
module `ι → A`. -/
noncomputable def analysisLinearMap (x : ι → E) : E →ₗ[A] ι → A where
  toFun z i := inner A (x i) z
  map_add' z w := by ext i; simp [CStarModule.inner_add_right]
  map_smul' a z := by ext i; simp [inner_op_smul_right]

@[simp]
theorem analysisLinearMap_apply (x : ι → E) (z : E) (i : ι) :
    analysisLinearMap x z i = inner A (x i) z := (rfl)

/-- For a Parseval frame, `Fintype.linearCombination A x` after `analysisLinearMap x` is the
identity. -/
theorem IsParsevalFrame.linearCombination_comp_analysisLinearMap [Fintype ι]
    (hx : IsParsevalFrame A x) :
    (Fintype.linearCombination A x).comp (analysisLinearMap x) = LinearMap.id :=
  LinearMap.ext fun z ↦ by
    simpa [Fintype.linearCombination_apply] using hx z

end CStarModule

variable {A E ι : Type*} [Ring A] [StarRing A] [Module ℂ A] [PartialOrder A] [Norm A]
  [AddCommGroup E] [Module ℂ E] [Module A E] [Norm E] [CStarModule A E] [Fintype ι]
  {x : ι → E}

/-- Over a unital coefficient ring `A`, such as a unital C⋆-algebra, a C⋆-module with a finite
Parseval frame is finitely generated as an algebraic `A`-module. -/
theorem Module.Finite.of_isParsevalFrame (hx : IsParsevalFrame A x) : Module.Finite A E :=
  Module.Finite.of_surjective (Fintype.linearCombination A x) fun z ↦
    ⟨CStarModule.analysisLinearMap x z,
      LinearMap.congr_fun hx.linearCombination_comp_analysisLinearMap z⟩

/-- Over a unital coefficient ring `A`, such as a unital C⋆-algebra, a C⋆-module with a finite
Parseval frame is projective as an algebraic `A`-module: the analysis map splits the synthesis map
from the free module `ι → A`. -/
theorem Module.Projective.of_isParsevalFrame (hx : IsParsevalFrame A x) :
    Module.Projective A E :=
  Module.Projective.of_split (CStarModule.analysisLinearMap x) (Fintype.linearCombination A x)
    hx.linearCombination_comp_analysisLinearMap

end Projective

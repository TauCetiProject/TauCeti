/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Projective
public import TauCeti.Analysis.CStarAlgebra.Module.Adjointable.Compact
public import TauCeti.Analysis.CStarAlgebra.Module.Gram
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

* `CStarModule.IsParsevalFrame A x`: the reconstruction formula `∑ i, ⟪x i, z⟫_A • x i = z`.
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
* `CStarModule.isParsevalFrame_single`: over a unital `A`, the standard basis of `A^ι` is a
  Parseval frame.
* `Module.Finite.of_isParsevalFrame` and `Module.Projective.of_isParsevalFrame`: over a unital
  `A`, a module with a finite Parseval frame is finitely generated and projective.

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

end CStarModule

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

variable {B E ι : Type*} [NonUnitalSeminormedRing B] [StarRing B] [Module ℂ B] [StarModule ℂ B]
  [PartialOrder B] [AddCommGroup E] [Module ℂ E] [SMul Bᵐᵒᵖ E] [Norm E] [CStarModule Bᵐᵒᵖ E]
  [Fintype ι]

/-- The Gram matrix `(⟨x i, x j⟩_B)_(i,j)` of a Parseval frame of a right Hilbert `B`-module is a
projection in `CStarMatrix ι ι B`. Only the algebraic `CStarModule` axioms are used. -/
theorem isStarProjection_gram {x : ι → E} (hx : IsParsevalFrame Bᵐᵒᵖ x) :
    IsStarProjection (gram B x) where
  isIdempotentElem := by
    ext i j
    conv_rhs => rw [gram_apply, ← hx (x j)]
    simp [mul_apply, inner_sum_right, inner_op_smul_right, Finset.unop_sum]
  isSelfAdjoint := by
    ext i j
    rw [star_apply, gram_apply, gram_apply, ← unop_star, star_inner]

end CStarMatrix

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

end CStarModule

section Projective

variable {A E ι : Type*} [Ring A] [StarRing A] [Module ℂ A] [PartialOrder A] [Norm A]
  [AddCommGroup E] [Module ℂ E] [Module A E] [Norm E] [CStarModule A E] [Fintype ι]
  {x : ι → E}

/-- The analysis map `z ↦ (⟪x i, z⟫_A)_i` of a finite family, as an `A`-linear map to the free
module `ι → A`. -/
private noncomputable def analysisLinearMap (x : ι → E) : E →ₗ[A] ι → A where
  toFun z i := inner A (x i) z
  map_add' z w := by ext i; simp [CStarModule.inner_add_right]
  map_smul' a z := by ext i; simp [inner_op_smul_right]

private theorem linearCombination_comp_analysisLinearMap (hx : IsParsevalFrame A x) :
    (Fintype.linearCombination A x).comp (analysisLinearMap x) = LinearMap.id :=
  LinearMap.ext fun z ↦ by
    simpa [Fintype.linearCombination_apply, analysisLinearMap] using hx z

/-- Over a unital coefficient ring `A`, such as a unital C⋆-algebra, a C⋆-module with a finite
Parseval frame is finitely generated as an algebraic `A`-module. -/
theorem Module.Finite.of_isParsevalFrame (hx : IsParsevalFrame A x) : Module.Finite A E :=
  Module.Finite.of_surjective (Fintype.linearCombination A x) fun z ↦
    ⟨analysisLinearMap x z, LinearMap.congr_fun (linearCombination_comp_analysisLinearMap hx) z⟩

/-- Over a unital coefficient ring `A`, such as a unital C⋆-algebra, a C⋆-module with a finite
Parseval frame is projective as an algebraic `A`-module: the analysis map splits the synthesis map
from the free module `ι → A`. -/
theorem Module.Projective.of_isParsevalFrame (hx : IsParsevalFrame A x) :
    Module.Projective A E :=
  Module.Projective.of_split (analysisLinearMap x) (Fintype.linearCombination A x)
    (linearCombination_comp_analysisLinearMap hx)

end Projective

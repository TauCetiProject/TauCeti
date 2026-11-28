/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Projective
public import TauCeti.Analysis.CStarAlgebra.Module.Gram
public import TauCeti.Analysis.CStarAlgebra.Module.Synonym
public import TauCeti.Analysis.CStarAlgebra.Module.Unitary

/-!
# Finite Parseval frames in Hilbert C⋆-modules

A finite family `x : ι → E` in a Hilbert C⋆-module over `A` is a *Parseval frame* when every
vector is reconstructed from its inner products with the family, `z = ∑ i, ⟪x i, z⟫_A • x i`. For
a right Hilbert `B`-module (`A = Bᵐᵒᵖ`) this is `z = ∑ i, x i ⟨x i, z⟩_B`.

This file develops the basic algebraic predicate and properties of finite Parseval frames without
compact-operator, matrix-action, or polar-decomposition dependencies:

* `CStarModule.IsParsevalFrame`: definition, edge cases (`isParsevalFrame_of_subsingleton`,
  `isParsevalFrame_empty_iff`), index-equivalence and unitary invariance
  (`Equiv.isParsevalFrame_comp_iff`, `TauCeti.CStarModuleUnitary.isParsevalFrame_comp_iff`,
  `LinearIsometryEquiv.isParsevalFrame_comp_iff`), and the algebraic Parseval identities
  (`TauCeti.CStarModule.isParsevalFrame_iff_sum_inner_mul_star_inner`,
  `TauCeti.CStarModule.isParsevalFrame_iff_sum_star_unop_inner_mul_unop_inner`).
* `CStarMatrix.isStarProjection_gram`: the Gram matrix `(⟨x i, x j⟩_B)_(i,j)` of a Parseval frame
  in a right Hilbert `B`-module is a star projection in `CStarMatrix ι ι B`.
* `TauCeti.CStarModule.frameAdjoint`, `CStarModule.IsParsevalFrame.isAdjointPair_frameAdjoint`,
  and `CStarModule.IsParsevalFrame.frameAdjoint_eq`: explicit adjoint of any `A`-linear map out of a
  module with a finite Parseval frame, and its independence of the frame.
* `CStarModule.isParsevalFrame_single` and `TauCeti.CStarModule.isParsevalFrame_single_one`: over a
  unital `A`, the standard bases of `A^ι` and `C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)` are Parseval frames.
* `TauCeti.CStarModule.analysisLinearMap`, `Module.Finite.of_isParsevalFrame`, and
  `Module.Projective.of_isParsevalFrame`: over a unital coefficient ring `A`, a C⋆-module with a
  finite Parseval frame is finitely generated and projective as an algebraic `A`-module.

## References

* E. Christopher Lance, *Hilbert C⋆-Modules: A Toolkit for Operator Algebraists*, Chapter 1.
* Iain Raeburn and Dana P. Williams, *Morita Equivalence and Continuous-Trace C⋆-Algebras*,
  Section 2.2.
* John Roe, *Lectures on K-Theory and Operator Algebras*, Proposition 10.2.
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

/-- Reindexing a Parseval frame along an equivalence of finite index types preserves the Parseval
property. -/
theorem IsParsevalFrame.comp_equiv [Fintype κ] {x : ι → E} (hx : IsParsevalFrame A x)
    (e : κ ≃ ι) : IsParsevalFrame A (x ∘ e) :=
  isParsevalFrame_iff.mpr fun z ↦ by
    simpa [Function.comp_apply] using
      (e.sum_comp fun i ↦ inner A (x i) z • x i).trans (hx.sum_inner_smul z)

/-- Reindexing a family along an equivalence of finite index types preserves and reflects the
Parseval frame property. -/
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

end CStarModule

namespace TauCeti.CStarModule

section Basic

variable {A ι E : Type*} [Fintype ι] [Inner A E] [AddCommMonoid E] [SMul A E]

/-- Every finite family in a subsingleton module is a Parseval frame. -/
theorem isParsevalFrame_of_subsingleton [Subsingleton E] (x : ι → E) : IsParsevalFrame A x :=
  isParsevalFrame_iff.mpr fun _ ↦ Subsingleton.elim _ _

/-- An empty family is a Parseval frame if and only if the module is subsingleton. -/
@[simp]
theorem isParsevalFrame_empty_iff [IsEmpty ι] (x : ι → E) :
    IsParsevalFrame A x ↔ Subsingleton E :=
  ⟨fun hx ↦ ⟨fun y z ↦ by rw [← hx.sum_inner_smul y, ← hx.sum_inner_smul z]; simp⟩,
    fun _ ↦ isParsevalFrame_of_subsingleton x⟩

end Basic

/-- **Parseval's identity** (general algebraic form): `x : ι → E` is a Parseval frame iff
`∑ i, ⟪x i, z⟫_A * (⟪x i, z⟫_A)⋆ = ⟪z, z⟫_A` for all `z : E`. -/
theorem isParsevalFrame_iff_sum_inner_mul_star_inner {A ι E : Type*} [Fintype ι] [NonUnitalRing A]
    [StarRing A] [Module ℂ A] [PartialOrder A] [Norm A]
    [AddCommGroup E] [Module ℂ E] [SMul A E] [Norm E] [CStarModule A E] {x : ι → E} :
    IsParsevalFrame A x ↔ ∀ z : E, ∑ i, inner A (x i) z * star (inner A (x i) z) = inner A z z := by
  refine ⟨fun hx z ↦ ?_, fun h ↦ isParsevalFrame_iff.mpr fun z ↦ ?_⟩
  · have hz := congrArg (inner A z) (hx.sum_inner_smul z)
    rw [inner_sum_right'] at hz
    simpa using hz
  · let Q : E → E := fun w ↦ (∑ i, inner A (x i) w • x i) - w
    have hQ_add (u v : E) : Q (u + v) = Q u + Q v := by
      simp only [Q, _root_.CStarModule.inner_add_right, _root_.CStarModule.add_smul,
        Finset.sum_add_distrib]
      abel
    have hQ_sa (u v : E) : inner A u (Q v) = inner A (Q u) v := by
      have h_l : inner A (∑ i, inner A (x i) u • x i) v =
          ∑ i, inner A (x i) v * inner A u (x i) := star_injective <| by
        simp [inner_sum_right', _root_.CStarModule.inner_op_smul_right, star_sum]
      simp [Q, sub_eq_add_neg, _root_.CStarModule.inner_neg_right',
        _root_.CStarModule.inner_neg_left', inner_sum_right', h_l]
    have hQ_diag (w : E) : inner A w (Q w) = 0 := by
      have hw := h w; simp only [star_inner] at hw
      simp [Q, sub_eq_add_neg, _root_.CStarModule.inner_neg_right', inner_sum_right', hw]
    have h2 : (2 : ℂ) • inner A (Q z) (Q z) = 0 := by
      simpa [hQ_add, hQ_diag z, hQ_diag (Q z), hQ_sa z (Q z), ← two_smul ℂ] using hQ_diag (z + Q z)
    exact sub_eq_zero.mp <| (_root_.CStarModule.inner_self (A := A)).mp <| by
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

end TauCeti.CStarModule

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

/-- Explicit frame-formula candidate adjoint `y ↦ ∑ i, ⟪T (x i), y⟫_A • x i` of a function
`T : E → F` with respect to a finite family `x : ι → E`. -/
def frameAdjoint (A : Type*) {ι E F : Type*} [Fintype ι] [Semiring A] [StarRing A] [Module ℂ A]
    [PartialOrder A] [Norm A] [AddCommMonoid E] [Module A E] [AddCommGroup F] [Module ℂ F]
    [Module A F] [Norm F] [CStarModule A F] (x : ι → E) (T : E → F) : F →ₗ[A] E where
  toFun y := ∑ i, inner A (T (x i)) y • x i
  map_add' _ _ := by simp [_root_.CStarModule.inner_add_right, add_smul, Finset.sum_add_distrib]
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

/-- The explicit frame adjoint `frameAdjoint A x T` is independent of the choice of finite
Parseval frame `x` (even across different finite index types). -/
theorem _root_.CStarModule.IsParsevalFrame.frameAdjoint_eq {A ι κ E F 𝓕 : Type*}
    [Fintype ι] [Fintype κ] [Ring A] [StarRing A] [Module ℂ A] [StarModule ℂ A] [PartialOrder A]
    [Norm A] [AddCommGroup E] [Module ℂ E] [Module A E] [Norm E] [CStarModule A E]
    [AddCommGroup F] [Module ℂ F] [Module A F] [Norm F] [CStarModule A F]
    [FunLike 𝓕 E F] [LinearMapClass 𝓕 A E F] {x : ι → E} (hx : IsParsevalFrame A x)
    {y : κ → E} (hy : IsParsevalFrame A y) (T : 𝓕) :
    frameAdjoint A x T = frameAdjoint A y T :=
  LinearMap.coe_injective <|
    (hx.isAdjointPair_frameAdjoint T).unique_right_cstarModule (hy.isAdjointPair_frameAdjoint T)

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

end CStarModule

namespace TauCeti.CStarModule

variable {A E ι : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Fintype ι]

/-- Over a unital C⋆-algebra `A`, the standard basis `i ↦ Pi.single i 1` of the right module
`C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)` is a Parseval frame. -/
theorem isParsevalFrame_single_one [DecidableEq ι] : IsParsevalFrame Aᵐᵒᵖ
    (fun i : ι ↦ (WithCStarModule.equiv Aᵐᵒᵖ (ι → A)).symm (Pi.single i (1 : A))) :=
  isParsevalFrame_iff.mpr fun v ↦ by
    simpa [WithCStarModule.inner_single_left, inner_mulOpposite] using
      WithCStarModule.sum_op_smul_single_one v

end TauCeti.CStarModule

section Projective

namespace TauCeti.CStarModule

variable {A E ι : Type*} [Ring A] [StarRing A] [Module ℂ A] [PartialOrder A] [Norm A]
  [AddCommGroup E] [Module ℂ E] [Module A E] [Norm E] [CStarModule A E]

/-- The analysis map `z ↦ (⟪x i, z⟫_A)_i` of a finite family, as an `A`-linear map to the free
module `ι → A`. -/
noncomputable def analysisLinearMap (x : ι → E) : E →ₗ[A] ι → A where
  toFun z i := inner A (x i) z
  map_add' z w := by ext i; simp [_root_.CStarModule.inner_add_right]
  map_smul' a z := by ext i; simp [inner_op_smul_right]

@[simp]
theorem analysisLinearMap_apply (x : ι → E) (z : E) (i : ι) :
    analysisLinearMap x z i = inner A (x i) z := (rfl)

end TauCeti.CStarModule

variable {A E ι : Type*} [Ring A] [StarRing A] [Module ℂ A] [PartialOrder A] [Norm A]
  [AddCommGroup E] [Module ℂ E] [Module A E] [Norm E] [CStarModule A E] [Fintype ι]
  {x : ι → E}

/-- For a Parseval frame, `Fintype.linearCombination A x` after `analysisLinearMap x` is the
identity. -/
theorem CStarModule.IsParsevalFrame.linearCombination_comp_analysisLinearMap
    (hx : IsParsevalFrame A x) :
    (Fintype.linearCombination A x).comp (TauCeti.CStarModule.analysisLinearMap x) = LinearMap.id :=
  LinearMap.ext fun z ↦ by
    simpa [Fintype.linearCombination_apply] using hx z

/-- Over a unital coefficient ring `A`, such as a unital C⋆-algebra, a C⋆-module with a finite
Parseval frame is finitely generated as an algebraic `A`-module. -/
theorem Module.Finite.of_isParsevalFrame (hx : IsParsevalFrame A x) : Module.Finite A E :=
  Module.Finite.of_surjective (Fintype.linearCombination A x) fun z ↦
    ⟨TauCeti.CStarModule.analysisLinearMap x z,
      LinearMap.congr_fun hx.linearCombination_comp_analysisLinearMap z⟩

/-- Over a unital coefficient ring `A`, such as a unital C⋆-algebra, a C⋆-module with a finite
Parseval frame is projective as an algebraic `A`-module: the analysis map splits the synthesis map
from the free module `ι → A`. -/
theorem Module.Projective.of_isParsevalFrame (hx : IsParsevalFrame A x) :
    Module.Projective A E :=
  Module.Projective.of_split (TauCeti.CStarModule.analysisLinearMap x)
    (Fintype.linearCombination A x) hx.linearCombination_comp_analysisLinearMap

end Projective

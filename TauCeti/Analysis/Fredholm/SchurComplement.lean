/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Fredholm.Open
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
public import Mathlib.Topology.Algebra.Module.Equiv.Prod
public import TauCeti.Analysis.Fredholm.OrthogonalPackage
public import TauCeti.Analysis.Fredholm.Prod
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Invertible
import TauCeti.Analysis.Normed.Module.ContinuousInverse

/-!
# Block decompositions, Schur complements, and triangular normal forms of Fredholm packages

Given a `ContinuousLinearMap.FredholmPackage` `pkg` for a reference operator `T₀ : E →L[𝕜] F`, the
domain and codomain split topologically into their essential and finite-dimensional summands
`E = X₁ ⊕ X₀` and `F = Y₁ ⊕ Y₀`. Relative to these fixed splittings, any continuous linear map
`T : E →L[𝕜] F` decomposes into four continuous linear blocks

* `pkg.blockA T : X₁ →L[𝕜] Y₁` (at `T₀`, the isomorphism `pkg.equiv`),
* `pkg.blockB T : X₀ →L[𝕜] Y₁` (zero at `T₀`),
* `pkg.blockC T : X₁ →L[𝕜] Y₀` (zero at `T₀`),
* `pkg.blockD T : X₀ →L[𝕜] Y₀` (zero at `T₀`).

Using the totalized operator inverse `(pkg.blockA T).inverse : Y₁ →L[𝕜] X₁`, we form for every `T`
the finite-dimensional **Schur complement**

`pkg.schurComplement T = pkg.blockD T - pkg.blockC T ∘L (pkg.blockA T).inverse ∘L pkg.blockB T`

between `X₀` and `Y₀`, together with total triangularizing continuous linear equivalences
`pkg.domTriangularEquiv T : (X₁ × X₀) ≃L[𝕜] E` and
`pkg.codomTriangularEquiv T : F ≃L[𝕜] (Y₁ × Y₀)` built from `ContinuousLinearEquiv.skewProd`.

Whenever `(pkg.blockA T).IsInvertible` holds — in particular on an open operator-norm neighborhood
of `T₀` when `E` is complete — these equivalences conjugate `T` to the block-diagonal operator
`(pkg.blockA T).prodMap (pkg.schurComplement T)`. Consequently:

* `T.ker` and `F ⧸ T.range` are continuously linearly equivalent to `(pkg.schurComplement T).ker`
  and `Y₀ ⧸ (pkg.schurComplement T).range` via explicit coordinate formulas,
* `T` is Fredholm with `T.index = (pkg.schurComplement T).index = T₀.index`,
* when `E` is complete, `(pkg.blockA S).inverse`, `pkg.schurComplement S`, and both directions of
  `pkg.domTriangularEquiv S` and `pkg.codomTriangularEquiv S` are continuous in operator norm at
  every `T` where `pkg.blockA T` is invertible.

Specializing `pkg` to `hT₀.orthogonalFredholmPackage` on Hilbert spaces places the Schur complement
directly between `ker T₀` and `ker T₀†`.

## Main declarations

* `ContinuousLinearMap.FredholmPackage.blockA`, `blockB`, `blockC`, `blockD`: the four block
  operators of `T` with respect to `pkg`.
* `ContinuousLinearMap.FredholmPackage.schurComplement`: the finite-dimensional Schur complement
  `D - C A⁻¹ B : decDom.X₀ →L[𝕜] decCodom.X₀`.
* `ContinuousLinearMap.FredholmPackage.domTriangularEquiv`,
  `ContinuousLinearMap.FredholmPackage.codomTriangularEquiv`: the triangularizing equivalences on
  domain and codomain.
* `ContinuousLinearMap.FredholmPackage.codomTriangularEquiv_comp_comp_domTriangularEquiv`:
  triangular conjugation of `T` to `(pkg.blockA T).prodMap (pkg.schurComplement T)`.
* `ContinuousLinearMap.FredholmPackage.kerEquivSchur`,
  `ContinuousLinearMap.FredholmPackage.cokerEquivSchur`: explicit continuous linear equivalences
  identifying `ker T` and `F ⧸ range T` with the kernel and cokernel of `pkg.schurComplement T`.
* `ContinuousLinearMap.FredholmPackage.continuousAt_schurComplement`,
  `ContinuousLinearMap.FredholmPackage.continuousAt_domTriangularEquiv`,
  `ContinuousLinearMap.FredholmPackage.continuousAt_codomTriangularEquiv`: operator-norm continuity
  where `pkg.blockA T` is invertible.

## References

* [N. Bourbaki, *Théories Spectrales*, Chapitre III, § 3, n° 2][bourbaki2023]
* M. F. Atiyah, *K-Theory*, Appendix (Atiyah–Jänich theorem).
* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, Appendix A.1.
-/

public section

noncomputable section

open Filter Module Submodule Topology
open scoped InnerProduct Ring

namespace ContinuousLinearMap.FredholmPackage

/-! ### Block decomposition and algebraic triangular normal form -/

section TVS

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]
  {T₀ : E →L[𝕜] F} (pkg : T₀.FredholmPackage)

/-- The essential-to-essential (`X₁ → X₁`) block of an operator `T` with respect to `pkg`. -/
def blockA (T : E →L[𝕜] F) : pkg.decDom.X₁ →L[𝕜] pkg.decCodom.X₁ :=
  pkg.decCodom.proj ∘L T ∘L pkg.decDom.X₁.subtypeL

/-- The kernel-to-essential (`X₀ → X₁`) block of an operator `T` with respect to `pkg`. -/
def blockB (T : E →L[𝕜] F) : pkg.decDom.X₀ →L[𝕜] pkg.decCodom.X₁ :=
  pkg.decCodom.proj ∘L T ∘L pkg.decDom.X₀.subtypeL

theorem blockA_def (T : E →L[𝕜] F) :
    pkg.blockA T = pkg.decCodom.proj ∘L T ∘L pkg.decDom.X₁.subtypeL :=
  (rfl)

theorem blockB_def (T : E →L[𝕜] F) :
    pkg.blockB T = pkg.decCodom.proj ∘L T ∘L pkg.decDom.X₀.subtypeL :=
  (rfl)

@[simp]
theorem blockA_apply (T : E →L[𝕜] F) (x : pkg.decDom.X₁) :
    pkg.blockA T x = pkg.decCodom.proj (T x) :=
  (rfl)

@[simp]
theorem blockB_apply (T : E →L[𝕜] F) (x : pkg.decDom.X₀) :
    pkg.blockB T x = pkg.decCodom.proj (T x) :=
  (rfl)

/-- At the reference operator `T₀`, the essential block `pkg.blockA T₀` is `pkg.equiv`. -/
@[simp]
theorem blockA_self : pkg.blockA T₀ = (pkg.equiv : pkg.decDom.X₁ →L[𝕜] pkg.decCodom.X₁) := by
  refine ContinuousLinearMap.ext fun x ↦ ?_
  have hx : T₀ (x : E) = (pkg.decCodom.X₁.subtypeL ∘L pkg.equiv ∘L pkg.decDom.proj) (x : E) :=
    DFunLike.congr_fun pkg.eq_equiv (x : E)
  rw [blockA_apply, hx]
  simp only [comp_apply, ContinuousLinearEquiv.coe_coe, Submodule.subtypeL_apply]
  rw [Submodule.projectionOntoL_apply_left pkg.decDom.isTopCompl,
    Submodule.projectionOntoL_apply_left pkg.decCodom.isTopCompl]

/-- The essential block of `pkg` is invertible at the reference operator `T₀`. -/
theorem isInvertible_blockA_self : (pkg.blockA T₀).IsInvertible := by
  rw [pkg.blockA_self]
  exact isInvertible_equiv

/-- Expressing `(pkg.blockA T).inverse` through `Ring.inverse` on the fixed endomorphism algebra
`pkg.decDom.X₁ →L[𝕜] pkg.decDom.X₁` via `pkg.equiv.symm`. -/
theorem inverse_blockA_eq_ringInverse (T : E →L[𝕜] F) :
    (pkg.blockA T).inverse =
      ((pkg.equiv.symm : pkg.decCodom.X₁ →L[𝕜] pkg.decDom.X₁) ∘L pkg.blockA T)⁻¹ʳ ∘L
        (pkg.equiv.symm : pkg.decCodom.X₁ →L[𝕜] pkg.decDom.X₁) :=
  inverse_eq_ringInverse pkg.equiv (pkg.blockA T)

@[simp]
theorem blockB_self : pkg.blockB T₀ = 0 := by
  refine ContinuousLinearMap.ext fun x ↦ ?_
  have hx : T₀ (x : E) = (pkg.decCodom.X₁.subtypeL ∘L pkg.equiv ∘L pkg.decDom.proj) (x : E) :=
    DFunLike.congr_fun pkg.eq_equiv (x : E)
  rw [blockB_apply, hx]
  simp only [comp_apply, Submodule.projectionOntoL_apply_right pkg.decDom.isTopCompl, map_zero,
    zero_apply]

section DomTriangular

variable [IsTopologicalAddGroup E]

/-- The domain triangularizing coordinate equivalence `(X₁ × X₀) ≃L[𝕜] E` sending `(x₁, x₀)` to
`↑(x₁ - A⁻¹ (B x₀)) + ↑x₀`. Built via `ContinuousLinearEquiv.skewProd`, it is a continuous linear
equivalence for every `T : E →L[𝕜] F`, whether or not `pkg.blockA T` is invertible. -/
def domTriangularEquiv (T : E →L[𝕜] F) :
    (pkg.decDom.X₁ × pkg.decDom.X₀) ≃L[𝕜] E :=
  ((ContinuousLinearEquiv.prodComm 𝕜 pkg.decDom.X₁ pkg.decDom.X₀).trans
    (((ContinuousLinearEquiv.refl 𝕜 pkg.decDom.X₀).skewProd
      (ContinuousLinearEquiv.refl 𝕜 pkg.decDom.X₁)
      (-((pkg.blockA T).inverse ∘L pkg.blockB T))).trans
      (ContinuousLinearEquiv.prodComm 𝕜 pkg.decDom.X₀ pkg.decDom.X₁))).trans
    (pkg.decDom.X₁.prodEquivOfIsTopCompl pkg.decDom.X₀ pkg.decDom.isTopCompl)

@[simp]
theorem domTriangularEquiv_apply (T : E →L[𝕜] F) (p : pkg.decDom.X₁ × pkg.decDom.X₀) :
    pkg.domTriangularEquiv T p =
      ((p.1 - (pkg.blockA T).inverse (pkg.blockB T p.2) : pkg.decDom.X₁) : E) + (p.2 : E) := by
  simp [domTriangularEquiv, sub_eq_add_neg]

@[simp]
theorem domTriangularEquiv_symm_apply (T : E →L[𝕜] F) (x : E) :
    (pkg.domTriangularEquiv T).symm x =
      (pkg.decDom.proj x + (pkg.blockA T).inverse (pkg.blockB T (pkg.decDom.proj₀ x)),
        pkg.decDom.proj₀ x) := by
  simp [domTriangularEquiv, Submodule.prodEquivOfIsTopCompl_symm_apply]

@[simp]
theorem domTriangularEquiv_self :
    pkg.domTriangularEquiv T₀ =
      pkg.decDom.X₁.prodEquivOfIsTopCompl pkg.decDom.X₀ pkg.decDom.isTopCompl :=
  ContinuousLinearEquiv.ext (funext fun p ↦ by simp [domTriangularEquiv])

/-- When `pkg.blockA T` is invertible, the essential codomain projection of
`T (pkg.domTriangularEquiv T p)` depends only on `p.1` via `pkg.blockA T`. -/
theorem decCodom_proj_apply_domTriangularEquiv {T : E →L[𝕜] F} (hA : (pkg.blockA T).IsInvertible)
    (p : pkg.decDom.X₁ × pkg.decDom.X₀) :
    pkg.decCodom.proj (T (pkg.domTriangularEquiv T p)) = pkg.blockA T p.1 := by
  rw [domTriangularEquiv_apply, map_add, map_add]
  change pkg.blockA T (p.1 - (pkg.blockA T).inverse (pkg.blockB T p.2)) + pkg.blockB T p.2 =
    pkg.blockA T p.1
  rw [map_sub, hA.self_apply_inverse, sub_add_cancel]

end DomTriangular

variable [IsTopologicalAddGroup F]

/-- The essential-to-cokernel (`X₁ → X₀`) block of an operator `T` with respect to `pkg`. -/
def blockC (T : E →L[𝕜] F) : pkg.decDom.X₁ →L[𝕜] pkg.decCodom.X₀ :=
  pkg.decCodom.proj₀ ∘L T ∘L pkg.decDom.X₁.subtypeL

/-- The finite-dimensional (`X₀ → X₀`) corner block of an operator `T` with respect to `pkg`. -/
def blockD (T : E →L[𝕜] F) : pkg.decDom.X₀ →L[𝕜] pkg.decCodom.X₀ :=
  pkg.decCodom.proj₀ ∘L T ∘L pkg.decDom.X₀.subtypeL

theorem blockC_def (T : E →L[𝕜] F) :
    pkg.blockC T = pkg.decCodom.proj₀ ∘L T ∘L pkg.decDom.X₁.subtypeL :=
  (rfl)

theorem blockD_def (T : E →L[𝕜] F) :
    pkg.blockD T = pkg.decCodom.proj₀ ∘L T ∘L pkg.decDom.X₀.subtypeL :=
  (rfl)

@[simp]
theorem blockC_apply (T : E →L[𝕜] F) (x : pkg.decDom.X₁) :
    pkg.blockC T x = pkg.decCodom.proj₀ (T x) :=
  (rfl)

@[simp]
theorem blockD_apply (T : E →L[𝕜] F) (x : pkg.decDom.X₀) :
    pkg.blockD T x = pkg.decCodom.proj₀ (T x) :=
  (rfl)

@[simp]
theorem blockC_self : pkg.blockC T₀ = 0 := by
  refine ContinuousLinearMap.ext fun x ↦ ?_
  have hx : T₀ x ∈ pkg.decCodom.X₁ := pkg.range_eq ▸ LinearMap.mem_range_self (T₀ : E →ₗ[𝕜] F) x
  exact Submodule.projectionOntoL_apply_right pkg.decCodom.isTopCompl.symm ⟨T₀ x, hx⟩

@[simp]
theorem blockD_self : pkg.blockD T₀ = 0 := by
  refine ContinuousLinearMap.ext fun x ↦ ?_
  have hx : T₀ x ∈ pkg.decCodom.X₁ := pkg.range_eq ▸ LinearMap.mem_range_self (T₀ : E →ₗ[𝕜] F) x
  exact Submodule.projectionOntoL_apply_right pkg.decCodom.isTopCompl.symm ⟨T₀ x, hx⟩

/-- The finite-dimensional **Schur complement** `D - C A⁻¹ B : decDom.X₀ →L[𝕜] decCodom.X₀` of `T`
with respect to `pkg`, defined totally for every `T` via `ContinuousLinearMap.inverse`. -/
def schurComplement (T : E →L[𝕜] F) : pkg.decDom.X₀ →L[𝕜] pkg.decCodom.X₀ :=
  pkg.blockD T - pkg.blockC T ∘L (pkg.blockA T).inverse ∘L pkg.blockB T

theorem schurComplement_def (T : E →L[𝕜] F) :
    pkg.schurComplement T =
      pkg.blockD T - pkg.blockC T ∘L (pkg.blockA T).inverse ∘L pkg.blockB T :=
  (rfl)

@[simp]
theorem schurComplement_apply (T : E →L[𝕜] F) (x : pkg.decDom.X₀) :
    pkg.schurComplement T x =
      pkg.blockD T x - pkg.blockC T ((pkg.blockA T).inverse (pkg.blockB T x)) :=
  (rfl)

@[simp]
theorem schurComplement_self : pkg.schurComplement T₀ = 0 := by
  simp [schurComplement_def]

/-- For every `T`, the finite-dimensional Schur complement `pkg.schurComplement T` has index equal
to `T₀.index`. -/
@[simp]
theorem index_schurComplement (T : E →L[𝕜] F) :
    (pkg.schurComplement T).index = T₀.index := by
  have := pkg.decDom.finite_X₀
  have := pkg.decCodom.finite_X₀
  rw [index_eq_of_finiteDimensional, pkg.index_eq]

/-- The codomain triangularizing coordinate equivalence `F ≃L[𝕜] (Y₁ × Y₀)` sending `y` to
`(proj y, proj₀ y - C (A⁻¹ (proj y)))`. It is a continuous linear equivalence for every `T`. -/
def codomTriangularEquiv (T : E →L[𝕜] F) :
    F ≃L[𝕜] (pkg.decCodom.X₁ × pkg.decCodom.X₀) :=
  (pkg.decCodom.X₁.prodEquivOfIsTopCompl pkg.decCodom.X₀ pkg.decCodom.isTopCompl).symm.trans
    ((ContinuousLinearEquiv.refl 𝕜 pkg.decCodom.X₁).skewProd
      (ContinuousLinearEquiv.refl 𝕜 pkg.decCodom.X₀)
      (-(pkg.blockC T ∘L (pkg.blockA T).inverse)))

@[simp]
theorem codomTriangularEquiv_apply (T : E →L[𝕜] F) (y : F) :
    pkg.codomTriangularEquiv T y =
      (pkg.decCodom.proj y,
        pkg.decCodom.proj₀ y - pkg.blockC T ((pkg.blockA T).inverse (pkg.decCodom.proj y))) := by
  simp [codomTriangularEquiv, Submodule.prodEquivOfIsTopCompl_symm_apply, sub_eq_add_neg]

@[simp]
theorem codomTriangularEquiv_symm_apply (T : E →L[𝕜] F) (q : pkg.decCodom.X₁ × pkg.decCodom.X₀) :
    (pkg.codomTriangularEquiv T).symm q =
      (q.1 : F) + ((q.2 + pkg.blockC T ((pkg.blockA T).inverse q.1) : pkg.decCodom.X₀) : F) := by
  simp [codomTriangularEquiv, Submodule.prodEquivOfIsTopCompl_apply]

@[simp]
theorem codomTriangularEquiv_self :
    pkg.codomTriangularEquiv T₀ =
      (pkg.decCodom.X₁.prodEquivOfIsTopCompl pkg.decCodom.X₀ pkg.decCodom.isTopCompl).symm :=
  ContinuousLinearEquiv.ext (funext fun y ↦ by simp [codomTriangularEquiv])

variable [IsTopologicalAddGroup E]

/-- The inessential codomain projection of `T (pkg.domTriangularEquiv T p)` is
`C p.1 + schurComplement T p.2`. -/
theorem decCodom_proj₀_apply_domTriangularEquiv (T : E →L[𝕜] F)
    (p : pkg.decDom.X₁ × pkg.decDom.X₀) :
    pkg.decCodom.proj₀ (T (pkg.domTriangularEquiv T p)) =
      pkg.blockC T p.1 + pkg.schurComplement T p.2 := by
  rw [domTriangularEquiv_apply, map_add, map_add]
  change pkg.blockC T (p.1 - (pkg.blockA T).inverse (pkg.blockB T p.2)) + pkg.blockD T p.2 =
    pkg.blockC T p.1 + pkg.schurComplement T p.2
  rw [map_sub, schurComplement_apply]
  abel

/-- **Schur-complement block diagonalization.** Whenever the essential block `pkg.blockA T` is
invertible, `pkg.codomTriangularEquiv T` and `pkg.domTriangularEquiv T` conjugate `T` to the
block-diagonal operator `(pkg.blockA T).prodMap (pkg.schurComplement T)`. -/
theorem codomTriangularEquiv_comp_comp_domTriangularEquiv {T : E →L[𝕜] F}
    (hA : (pkg.blockA T).IsInvertible) :
    (pkg.codomTriangularEquiv T : F →L[𝕜] pkg.decCodom.X₁ × pkg.decCodom.X₀) ∘L T ∘L
        (pkg.domTriangularEquiv T : pkg.decDom.X₁ × pkg.decDom.X₀ →L[𝕜] E) =
      (pkg.blockA T).prodMap (pkg.schurComplement T) := by
  refine ContinuousLinearMap.ext fun p ↦ ?_
  simp only [comp_apply, ContinuousLinearEquiv.coe_coe, coe_prodMap',
    codomTriangularEquiv_apply, pkg.decCodom_proj_apply_domTriangularEquiv hA,
    pkg.decCodom_proj₀_apply_domTriangularEquiv, hA.inverse_apply_self, add_sub_cancel_left]
  rfl

/-- Pointwise form of the Schur-complement factorization: `T (domTriangularEquiv T p)` equals
`(codomTriangularEquiv T).symm (blockA T p.1, schurComplement T p.2)`. -/
theorem apply_domTriangularEquiv_eq_symm_codomTriangularEquiv {T : E →L[𝕜] F}
    (hA : (pkg.blockA T).IsInvertible) (p : pkg.decDom.X₁ × pkg.decDom.X₀) :
    T (pkg.domTriangularEquiv T p) =
      (pkg.codomTriangularEquiv T).symm (pkg.blockA T p.1, pkg.schurComplement T p.2) := by
  apply (pkg.codomTriangularEquiv T).injective
  rw [ContinuousLinearEquiv.apply_symm_apply]
  exact DFunLike.congr_fun (pkg.codomTriangularEquiv_comp_comp_domTriangularEquiv hA) p

/-- On the graph slice `(0, x₀)`, `T (domTriangularEquiv T (0, x₀))` lies in `decCodom.X₀` and
equals `schurComplement T x₀`. -/
theorem apply_domTriangularEquiv_zero_left {T : E →L[𝕜] F} (hA : (pkg.blockA T).IsInvertible)
    (x₀ : pkg.decDom.X₀) :
    T (pkg.domTriangularEquiv T (0, x₀)) = (pkg.schurComplement T x₀ : F) := by
  rw [pkg.apply_domTriangularEquiv_eq_symm_codomTriangularEquiv hA]
  simp

/-! ### Kernel, cokernel, Fredholmness, and index via the Schur complement -/

private theorem prod_domTriangularEquiv_symm_of_mem_ker {T : E →L[𝕜] F}
    (hA : (pkg.blockA T).IsInvertible) (x : T.ker) :
    (pkg.blockA T ((pkg.domTriangularEquiv T).symm (x : E)).1,
      pkg.schurComplement T ((pkg.domTriangularEquiv T).symm (x : E)).2) = 0 := by
  apply (pkg.codomTriangularEquiv T).symm.injective
  rw [map_zero, ← pkg.apply_domTriangularEquiv_eq_symm_codomTriangularEquiv hA,
    ContinuousLinearEquiv.apply_symm_apply]
  exact x.2

private theorem proj₀_mem_ker_schurComplement {T : E →L[𝕜] F} (hA : (pkg.blockA T).IsInvertible)
    (x : T.ker) : (pkg.decDom.proj₀ ∘L T.ker.subtypeL) x ∈ (pkg.schurComplement T).ker := by
  rw [LinearMap.mem_ker]
  simpa only [comp_apply, Submodule.subtypeL_apply, domTriangularEquiv_symm_apply,
    Prod.snd_zero, coe_coe] using
      congrArg Prod.snd (pkg.prod_domTriangularEquiv_symm_of_mem_ker hA x)

private theorem domTriangularEquiv_zero_mem_ker {T : E →L[𝕜] F} (hA : (pkg.blockA T).IsInvertible)
    (x₀ : (pkg.schurComplement T).ker) :
    ((pkg.domTriangularEquiv T : (pkg.decDom.X₁ × pkg.decDom.X₀) →L[𝕜] E) ∘L
      ContinuousLinearMap.inr 𝕜 pkg.decDom.X₁ pkg.decDom.X₀ ∘L
      (pkg.schurComplement T).ker.subtypeL) x₀ ∈ T.ker := by
  have hx₀ : pkg.schurComplement T (x₀ : pkg.decDom.X₀) = 0 := x₀.2
  simp only [comp_apply, inr_apply, Submodule.subtypeL_apply, ContinuousLinearEquiv.coe_coe]
  rw [LinearMap.mem_ker, coe_coe, pkg.apply_domTriangularEquiv_zero_left hA, hx₀,
    ZeroMemClass.coe_zero]

/-- When `pkg.blockA T` is invertible, `pkg.decDom.proj₀` restricts to a continuous linear
equivalence `ker T ≃L[𝕜] ker (pkg.schurComplement T)`, with inverse `x₀ ↦ x₀ - A⁻¹ (B x₀)`. -/
def kerEquivSchur {T : E →L[𝕜] F} (hA : (pkg.blockA T).IsInvertible) :
    T.ker ≃L[𝕜] (pkg.schurComplement T).ker :=
  ContinuousLinearEquiv.equivOfInverse
    ((pkg.decDom.proj₀ ∘L T.ker.subtypeL).codRestrict (pkg.schurComplement T).ker
      (pkg.proj₀_mem_ker_schurComplement hA))
    (((pkg.domTriangularEquiv T : (pkg.decDom.X₁ × pkg.decDom.X₀) →L[𝕜] E) ∘L
        ContinuousLinearMap.inr 𝕜 pkg.decDom.X₁ pkg.decDom.X₀ ∘L
        (pkg.schurComplement T).ker.subtypeL).codRestrict T.ker
      (pkg.domTriangularEquiv_zero_mem_ker hA))
    (fun x => by
      apply Subtype.ext
      apply (pkg.domTriangularEquiv T).symm.injective
      have hprod := pkg.prod_domTriangularEquiv_symm_of_mem_ker hA x
      have hp₁ : ((pkg.domTriangularEquiv T).symm (x : E)).1 = 0 :=
        hA.injective ((congrArg Prod.fst hprod).trans (map_zero _).symm)
      have hp₂ : pkg.decDom.proj₀ (x : E) = ((pkg.domTriangularEquiv T).symm (x : E)).2 := by
        simp
      simp only [coe_codRestrict_apply, comp_apply, inr_apply, Submodule.subtypeL_apply,
        ContinuousLinearEquiv.coe_coe, hp₂, ContinuousLinearEquiv.symm_apply_apply]
      exact Prod.ext hp₁.symm rfl)
    (fun x₀ => by
      apply Subtype.ext
      simp only [coe_codRestrict_apply, comp_apply, inr_apply, Submodule.subtypeL_apply,
        ContinuousLinearEquiv.coe_coe]
      have h := congrArg Prod.snd
        ((pkg.domTriangularEquiv T).symm_apply_apply (0, (x₀ : pkg.decDom.X₀)))
      simpa only [domTriangularEquiv_symm_apply] using h)

@[simp]
theorem coe_kerEquivSchur_apply {T : E →L[𝕜] F} (hA : (pkg.blockA T).IsInvertible) (x : T.ker) :
    (pkg.kerEquivSchur hA x : pkg.decDom.X₀) = pkg.decDom.proj₀ (x : E) :=
  (rfl)

@[simp]
theorem coe_kerEquivSchur_symm_apply {T : E →L[𝕜] F} (hA : (pkg.blockA T).IsInvertible)
    (x₀ : (pkg.schurComplement T).ker) :
    ((pkg.kerEquivSchur hA).symm x₀ : E) =
      (x₀ : E) - ((pkg.blockA T).inverse (pkg.blockB T (x₀ : pkg.decDom.X₀)) : E) := by
  simp only [kerEquivSchur, ContinuousLinearEquiv.symm_equivOfInverse,
    ContinuousLinearEquiv.equivOfInverse_apply, coe_codRestrict_apply, comp_apply, inr_apply,
    Submodule.subtypeL_apply, ContinuousLinearEquiv.coe_coe, domTriangularEquiv_apply, zero_sub,
    NegMemClass.coe_neg]
  rw [add_comm, ← sub_eq_add_neg]

private theorem range_le_ker_mkQL_codomTriangularEquiv {T : E →L[𝕜] F}
    (hA : (pkg.blockA T).IsInvertible) :
    T.range ≤ ((pkg.schurComplement T).range.mkQL ∘L
      ContinuousLinearMap.snd 𝕜 pkg.decCodom.X₁ pkg.decCodom.X₀ ∘L
      (pkg.codomTriangularEquiv T : F →L[𝕜] pkg.decCodom.X₁ × pkg.decCodom.X₀)).ker := by
  rintro _ ⟨x, rfl⟩
  set p := (pkg.domTriangularEquiv T).symm x
  have hx : T x = T (pkg.domTriangularEquiv T p) :=
    congrArg T ((pkg.domTriangularEquiv T).apply_symm_apply x).symm
  rw [LinearMap.mem_ker]
  change (pkg.schurComplement T).range.mkQ ((pkg.codomTriangularEquiv T (T x)).2) = 0
  rw [hx, pkg.apply_domTriangularEquiv_eq_symm_codomTriangularEquiv hA,
    ContinuousLinearEquiv.apply_symm_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact LinearMap.mem_range_self _ p.2

private theorem range_schurComplement_le_ker_mkQL_subtypeL {T : E →L[𝕜] F}
    (hA : (pkg.blockA T).IsInvertible) :
    (pkg.schurComplement T).range ≤ (T.range.mkQL ∘L pkg.decCodom.X₀.subtypeL).ker := by
  rintro _ ⟨x₀, rfl⟩
  rw [LinearMap.mem_ker]
  change T.range.mkQ (pkg.schurComplement T x₀ : F) = 0
  rw [← pkg.apply_domTriangularEquiv_zero_left hA, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero]
  exact LinearMap.mem_range_self _ _

/-- When `pkg.blockA T` is invertible, the second component of `pkg.codomTriangularEquiv T`
descends to a continuous linear equivalence
`(F ⧸ T.range) ≃L[𝕜] (pkg.decCodom.X₀ ⧸ (pkg.schurComplement T).range)`, whose inverse is induced
by the inclusion `pkg.decCodom.X₀ ↪ F`. -/
def cokerEquivSchur {T : E →L[𝕜] F} (hA : (pkg.blockA T).IsInvertible) :
    (F ⧸ T.range) ≃L[𝕜] (pkg.decCodom.X₀ ⧸ (pkg.schurComplement T).range) :=
  ContinuousLinearEquiv.equivOfInverse
    (T.range.liftQL ((pkg.schurComplement T).range.mkQL ∘L
        ContinuousLinearMap.snd 𝕜 pkg.decCodom.X₁ pkg.decCodom.X₀ ∘L
        (pkg.codomTriangularEquiv T : F →L[𝕜] pkg.decCodom.X₁ × pkg.decCodom.X₀))
      (pkg.range_le_ker_mkQL_codomTriangularEquiv hA))
    ((pkg.schurComplement T).range.liftQL (T.range.mkQL ∘L pkg.decCodom.X₀.subtypeL)
      (pkg.range_schurComplement_le_ker_mkQL_subtypeL hA))
    (fun z => by
      obtain ⟨y, rfl⟩ := T.range.mkQ_surjective z
      set q := pkg.codomTriangularEquiv T y
      change Submodule.Quotient.mk (q.2 : F) = Submodule.Quotient.mk y
      symm
      rw [Submodule.Quotient.eq]
      have hq : (q.1, 0) + (0, q.2) = q := Prod.ext (add_zero q.1) (zero_add q.2)
      have hy : y = (pkg.codomTriangularEquiv T).symm (q.1, 0) + (q.2 : F) := by
        calc y = (pkg.codomTriangularEquiv T).symm ((q.1, 0) + (0, q.2)) := by
              rw [hq]
              exact ((pkg.codomTriangularEquiv T).symm_apply_apply y).symm
          _ = (pkg.codomTriangularEquiv T).symm (q.1, 0) +
              (pkg.codomTriangularEquiv T).symm (0, q.2) := map_add _ _ _
          _ = (pkg.codomTriangularEquiv T).symm (q.1, 0) + (q.2 : F) := by simp
      have hmem : (pkg.codomTriangularEquiv T).symm (q.1, 0) ∈ T.range :=
        ⟨pkg.domTriangularEquiv T ((pkg.blockA T).inverse q.1, 0), by
          rw [coe_coe, pkg.apply_domTriangularEquiv_eq_symm_codomTriangularEquiv hA,
            hA.self_apply_inverse, map_zero]⟩
      simpa only [hy, add_sub_cancel_right] using hmem)
    (fun w => by
      obtain ⟨y₀, rfl⟩ := (pkg.schurComplement T).range.mkQ_surjective w
      change Submodule.Quotient.mk (pkg.codomTriangularEquiv T (y₀ : F)).2 =
        Submodule.Quotient.mk y₀
      have hproj : pkg.decCodom.proj (y₀ : F) = 0 :=
        Submodule.projectionOntoL_apply_right pkg.decCodom.isTopCompl y₀
      have hproj₀ : pkg.decCodom.proj₀ (y₀ : F) = y₀ :=
        Submodule.projectionOntoL_apply_left pkg.decCodom.isTopCompl.symm y₀
      simp [codomTriangularEquiv_apply, hproj, hproj₀])

@[simp]
theorem cokerEquivSchur_apply_mk {T : E →L[𝕜] F} (hA : (pkg.blockA T).IsInvertible) (y : F) :
    pkg.cokerEquivSchur hA (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk
        (pkg.decCodom.proj₀ y - pkg.blockC T ((pkg.blockA T).inverse (pkg.decCodom.proj y))) := by
  simp [cokerEquivSchur]

@[simp]
theorem cokerEquivSchur_symm_apply_mk {T : E →L[𝕜] F} (hA : (pkg.blockA T).IsInvertible)
    (y₀ : pkg.decCodom.X₀) :
    (pkg.cokerEquivSchur hA).symm (Submodule.Quotient.mk y₀) =
      Submodule.Quotient.mk (y₀ : F) := by
  simp [cokerEquivSchur]

/-- When `pkg.blockA T` is invertible, `ker T` has the same dimension as
`ker (pkg.schurComplement T)`. -/
theorem finrank_ker_eq_finrank_ker_schurComplement {T : E →L[𝕜] F}
    (hA : (pkg.blockA T).IsInvertible) :
    finrank 𝕜 T.ker = finrank 𝕜 (pkg.schurComplement T).ker :=
  (pkg.kerEquivSchur hA).toLinearEquiv.finrank_eq

/-- When `pkg.blockA T` is invertible, `F ⧸ range T` has the same dimension as
`decCodom.X₀ ⧸ range (pkg.schurComplement T)`. -/
theorem finrank_coker_eq_finrank_coker_schurComplement {T : E →L[𝕜] F}
    (hA : (pkg.blockA T).IsInvertible) :
    finrank 𝕜 (F ⧸ T.range) = finrank 𝕜 (pkg.decCodom.X₀ ⧸ (pkg.schurComplement T).range) :=
  (pkg.cokerEquivSchur hA).toLinearEquiv.finrank_eq

/-- When `pkg.blockA T` is invertible, `T` has the same index as `pkg.schurComplement T`. -/
theorem index_eq_index_schurComplement {T : E →L[𝕜] F} (hA : (pkg.blockA T).IsInvertible) :
    T.index = (pkg.schurComplement T).index := by
  rw [index_eq_finrank_sub, index_eq_finrank_sub,
    pkg.finrank_ker_eq_finrank_ker_schurComplement hA,
    pkg.finrank_coker_eq_finrank_coker_schurComplement hA]

/-- When `pkg.blockA T` is invertible, `T` has the same index as the reference operator `T₀`. -/
theorem index_eq_of_isInvertible_blockA {T : E →L[𝕜] F} (hA : (pkg.blockA T).IsInvertible) :
    T.index = T₀.index :=
  (pkg.index_eq_index_schurComplement hA).trans (pkg.index_schurComplement T)

/-- Over a complete scalar field, any operator `T` whose essential block `pkg.blockA T` is
invertible is Fredholm: it is conjugate to the product of an isomorphism and a map between
finite-dimensional spaces. -/
theorem isFredholm_of_isInvertible_blockA [CompleteSpace 𝕜]
    [ContinuousSMul 𝕜 E] [ContinuousSMul 𝕜 F] [T2Space F]
    {T : E →L[𝕜] F} (hA : (pkg.blockA T).IsInvertible) :
    T.IsFredholm := by
  have := pkg.decDom.finite_X₀
  have := pkg.decCodom.finite_X₀
  obtain ⟨eA, heA⟩ := hA
  have hprod : ((pkg.blockA T).prodMap (pkg.schurComplement T)).IsFredholm := by
    rw [← heA]
    exact eA.isFredholm.prodMap (isFredholm_of_finiteDimensional (pkg.schurComplement T))
  have hT : T = ((pkg.codomTriangularEquiv T).symm : _ →L[𝕜] F) ∘L
      ((pkg.blockA T).prodMap (pkg.schurComplement T)) ∘L
      ((pkg.domTriangularEquiv T).symm : E →L[𝕜] _) := by
    refine ContinuousLinearMap.ext fun x ↦ ?_
    rw [comp_apply, comp_apply, ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.coe_coe,
      coe_prodMap', Prod.map_apply,
      ← pkg.apply_domTriangularEquiv_eq_symm_codomTriangularEquiv ⟨eA, heA⟩,
      ContinuousLinearEquiv.apply_symm_apply]
  rw [hT]
  exact (hprod.equiv_comp (pkg.codomTriangularEquiv T).symm).comp_equiv
    (pkg.domTriangularEquiv T).symm

end TVS

/-! ### Operator-norm continuity on Banach spaces -/

section Normed

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {T₀ : E →L[𝕜] F} (pkg : T₀.FredholmPackage)

@[fun_prop]
theorem continuous_blockA : Continuous pkg.blockA := by
  rw [funext pkg.blockA_def]
  fun_prop

@[fun_prop]
theorem continuous_blockB : Continuous pkg.blockB := by
  rw [funext pkg.blockB_def]
  fun_prop

@[fun_prop]
theorem continuous_blockC : Continuous pkg.blockC := by
  rw [funext pkg.blockC_def]
  fun_prop

@[fun_prop]
theorem continuous_blockD : Continuous pkg.blockD := by
  rw [funext pkg.blockD_def]
  fun_prop

variable [CompleteSpace E]

/-- When `E` is complete, invertibility of `pkg.blockA` is an open condition in operator norm. -/
theorem eventually_nhds_isInvertible_blockA_of_isInvertible {T : E →L[𝕜] F}
    (hA : (pkg.blockA T).IsInvertible) :
    ∀ᶠ S in 𝓝 T, (pkg.blockA S).IsInvertible := by
  have : CompleteSpace pkg.decDom.X₁ :=
    pkg.decDom.isTopCompl.isClosed.isComplete.completeSpace_coe
  exact pkg.continuous_blockA.tendsto T |>.eventually hA.eventually_nhds

/-- On a Banach domain, `pkg.blockA S` is invertible for all `S` near `T₀`. -/
theorem eventually_nhds_isInvertible_blockA :
    ∀ᶠ S in 𝓝 T₀, (pkg.blockA S).IsInvertible :=
  pkg.eventually_nhds_isInvertible_blockA_of_isInvertible pkg.isInvertible_blockA_self

/-- Operator-norm continuity of `S ↦ (pkg.blockA S).inverse` at any `T` where `pkg.blockA T` is
invertible. -/
theorem continuousAt_inverse_blockA {T : E →L[𝕜] F} (hA : (pkg.blockA T).IsInvertible) :
    ContinuousAt (fun S ↦ (pkg.blockA S).inverse) T :=
  pkg.continuous_blockA.continuousAt.clm_inverse_of_eventually_isInvertible
    (pkg.eventually_nhds_isInvertible_blockA_of_isInvertible hA)

/-- Operator-norm continuity of the Schur complement `pkg.schurComplement` at any `T` where
`pkg.blockA T` is invertible. -/
theorem continuousAt_schurComplement {T : E →L[𝕜] F} (hA : (pkg.blockA T).IsInvertible) :
    ContinuousAt pkg.schurComplement T := by
  rw [funext pkg.schurComplement_def]
  exact pkg.continuous_blockD.continuousAt.sub
    ((pkg.continuous_blockC.continuousAt.clm_comp (pkg.continuousAt_inverse_blockA hA)).clm_comp
      pkg.continuous_blockB.continuousAt)

/-- Operator-norm continuity of `S ↦ (pkg.domTriangularEquiv S : _ →L[𝕜] E)` where `pkg.blockA T`
is invertible. -/
theorem continuousAt_domTriangularEquiv {T : E →L[𝕜] F} (hA : (pkg.blockA T).IsInvertible) :
    ContinuousAt (fun S ↦
      (pkg.domTriangularEquiv S : (pkg.decDom.X₁ × pkg.decDom.X₀) →L[𝕜] E)) T := by
  have hEq : (fun S ↦ (pkg.domTriangularEquiv S : (pkg.decDom.X₁ × pkg.decDom.X₀) →L[𝕜] E)) =
      fun S ↦ pkg.decDom.X₁.subtypeL ∘L
          (ContinuousLinearMap.fst 𝕜 pkg.decDom.X₁ pkg.decDom.X₀ -
            (pkg.blockA S).inverse ∘L pkg.blockB S ∘L
              ContinuousLinearMap.snd 𝕜 pkg.decDom.X₁ pkg.decDom.X₀) +
        pkg.decDom.X₀.subtypeL ∘L ContinuousLinearMap.snd 𝕜 pkg.decDom.X₁ pkg.decDom.X₀ := by
    refine funext fun S ↦ ContinuousLinearMap.ext fun p ↦ ?_
    simp
  rw [hEq]
  have hinvB : ContinuousAt (fun S ↦
      (pkg.blockA S).inverse ∘L pkg.blockB S ∘L
        ContinuousLinearMap.snd 𝕜 pkg.decDom.X₁ pkg.decDom.X₀) T :=
    (pkg.continuousAt_inverse_blockA hA).clm_comp
      (pkg.continuous_blockB.continuousAt.clm_comp continuousAt_const)
  exact (continuousAt_const.clm_comp (continuousAt_const.sub hinvB)).add continuousAt_const

/-- Operator-norm continuity of `S ↦ ((pkg.domTriangularEquiv S).symm : E →L[𝕜] _)` where
`pkg.blockA T` is invertible. -/
theorem continuousAt_domTriangularEquiv_symm {T : E →L[𝕜] F} (hA : (pkg.blockA T).IsInvertible) :
    ContinuousAt (fun S ↦
      ((pkg.domTriangularEquiv S).symm : E →L[𝕜] (pkg.decDom.X₁ × pkg.decDom.X₀))) T := by
  have hEq : (fun S ↦
      ((pkg.domTriangularEquiv S).symm : E →L[𝕜] (pkg.decDom.X₁ × pkg.decDom.X₀))) =
      fun S ↦ ContinuousLinearMap.inl 𝕜 pkg.decDom.X₁ pkg.decDom.X₀ ∘L
          (pkg.decDom.proj + (pkg.blockA S).inverse ∘L pkg.blockB S ∘L pkg.decDom.proj₀) +
        ContinuousLinearMap.inr 𝕜 pkg.decDom.X₁ pkg.decDom.X₀ ∘L pkg.decDom.proj₀ := by
    refine funext fun S ↦ ContinuousLinearMap.ext fun x ↦ ?_
    simp
  rw [hEq]
  have hinvB : ContinuousAt (fun S ↦
      (pkg.blockA S).inverse ∘L pkg.blockB S ∘L pkg.decDom.proj₀) T :=
    (pkg.continuousAt_inverse_blockA hA).clm_comp
      (pkg.continuous_blockB.continuousAt.clm_comp continuousAt_const)
  exact (continuousAt_const.clm_comp (continuousAt_const.add hinvB)).add continuousAt_const

/-- Operator-norm continuity of `S ↦ (pkg.codomTriangularEquiv S : F →L[𝕜] _)` where `pkg.blockA T`
is invertible. -/
theorem continuousAt_codomTriangularEquiv {T : E →L[𝕜] F} (hA : (pkg.blockA T).IsInvertible) :
    ContinuousAt (fun S ↦
      (pkg.codomTriangularEquiv S : F →L[𝕜] (pkg.decCodom.X₁ × pkg.decCodom.X₀))) T := by
  have hEq : (fun S ↦
      (pkg.codomTriangularEquiv S : F →L[𝕜] (pkg.decCodom.X₁ × pkg.decCodom.X₀))) =
      fun S ↦ ContinuousLinearMap.inl 𝕜 pkg.decCodom.X₁ pkg.decCodom.X₀ ∘L pkg.decCodom.proj +
        ContinuousLinearMap.inr 𝕜 pkg.decCodom.X₁ pkg.decCodom.X₀ ∘L
          (pkg.decCodom.proj₀ - pkg.blockC S ∘L (pkg.blockA S).inverse ∘L pkg.decCodom.proj) := by
    refine funext fun S ↦ ContinuousLinearMap.ext fun y ↦ ?_
    simp
  rw [hEq]
  have hCinv : ContinuousAt (fun S ↦
      pkg.blockC S ∘L (pkg.blockA S).inverse ∘L pkg.decCodom.proj) T :=
    pkg.continuous_blockC.continuousAt.clm_comp
      ((pkg.continuousAt_inverse_blockA hA).clm_comp continuousAt_const)
  exact continuousAt_const.add (continuousAt_const.clm_comp (continuousAt_const.sub hCinv))

/-- Operator-norm continuity of `S ↦ ((pkg.codomTriangularEquiv S).symm : _ →L[𝕜] F)` where
`pkg.blockA T` is invertible. -/
theorem continuousAt_codomTriangularEquiv_symm {T : E →L[𝕜] F} (hA : (pkg.blockA T).IsInvertible) :
    ContinuousAt (fun S ↦
      ((pkg.codomTriangularEquiv S).symm : (pkg.decCodom.X₁ × pkg.decCodom.X₀) →L[𝕜] F)) T := by
  have hEq : (fun S ↦
      ((pkg.codomTriangularEquiv S).symm : (pkg.decCodom.X₁ × pkg.decCodom.X₀) →L[𝕜] F)) =
      fun S ↦
        pkg.decCodom.X₁.subtypeL ∘L ContinuousLinearMap.fst 𝕜 pkg.decCodom.X₁ pkg.decCodom.X₀ +
        pkg.decCodom.X₀.subtypeL ∘L
          (ContinuousLinearMap.snd 𝕜 pkg.decCodom.X₁ pkg.decCodom.X₀ +
            pkg.blockC S ∘L (pkg.blockA S).inverse ∘L
              ContinuousLinearMap.fst 𝕜 pkg.decCodom.X₁ pkg.decCodom.X₀) := by
    refine funext fun S ↦ ContinuousLinearMap.ext fun q ↦ ?_
    simp
  rw [hEq]
  have hCinv : ContinuousAt (fun S ↦
      pkg.blockC S ∘L (pkg.blockA S).inverse ∘L
        ContinuousLinearMap.fst 𝕜 pkg.decCodom.X₁ pkg.decCodom.X₀) T :=
    pkg.continuous_blockC.continuousAt.clm_comp
      ((pkg.continuousAt_inverse_blockA hA).clm_comp continuousAt_const)
  exact continuousAt_const.add (continuousAt_const.clm_comp (continuousAt_const.add hCinv))

end Normed

end ContinuousLinearMap.FredholmPackage

/-! ### Specialization to the orthogonal Fredholm package on Hilbert spaces -/

namespace ContinuousLinearMap.IsFredholm

section Hilbert

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  {T₀ : E →L[𝕜] F} (hT₀ : T₀.IsFredholm)

/-- On Hilbert spaces, `hT₀.orthogonalFredholmPackage` provides throughout a neighborhood of `T₀`
an invertible `(ker T₀)ᗮ → range T₀` block and a triangular conjugation of every nearby operator `S`
to `(blockA S).prodMap (schurComplement S)`, with `schurComplement S : ker T₀ →L[𝕜] ker T₀†`
continuous in operator norm on that neighborhood. -/
theorem eventually_nhds_orthogonal_triangular_normal_form :
    ∀ᶠ S in 𝓝 T₀,
      (hT₀.orthogonalFredholmPackage.blockA S).IsInvertible ∧
      ((hT₀.orthogonalFredholmPackage.codomTriangularEquiv S).toContinuousLinearMap :
          F →L[𝕜] T₀.range × (T₀†).ker) ∘L S ∘L
        ((hT₀.orthogonalFredholmPackage.domTriangularEquiv S).toContinuousLinearMap :
          T₀.kerᗮ × T₀.ker →L[𝕜] E) =
          (hT₀.orthogonalFredholmPackage.blockA S).prodMap
            (hT₀.orthogonalFredholmPackage.schurComplement S) ∧
      ContinuousAt hT₀.orthogonalFredholmPackage.schurComplement S ∧
      S.IsFredholm ∧
      S.index = (hT₀.orthogonalFredholmPackage.schurComplement S).index := by
  filter_upwards [hT₀.orthogonalFredholmPackage.eventually_nhds_isInvertible_blockA] with S hA
  exact ⟨hA,
    hT₀.orthogonalFredholmPackage.codomTriangularEquiv_comp_comp_domTriangularEquiv hA,
    hT₀.orthogonalFredholmPackage.continuousAt_schurComplement hA,
    hT₀.orthogonalFredholmPackage.isFredholm_of_isInvertible_blockA hA,
    hT₀.orthogonalFredholmPackage.index_eq_index_schurComplement hA⟩

end Hilbert

end ContinuousLinearMap.IsFredholm

end

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import TauCeti.Analysis.Fredholm.Basic
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Tactic.Abel
import TauCeti.Analysis.Fredholm.Prod
import TauCeti.Analysis.Normed.Module.ContinuousInverse
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Invertible
import TauCeti.Topology.Algebra.Module.Spaces.ContinuousLinearMap

/-!
# Block triangular reduction and Schur complements for Fredholm packages

Given a `FredholmPackage` `pkg` for an operator `T₀ : E →L[𝕜] F`, the topological decompositions
`E = X₁ ⊕ X₀` and `F = Y₁ ⊕ Y₀` identify every continuous linear operator `T : E →L[𝕜] F` with a
`2 × 2` block matrix
$$\begin{pmatrix} A & B \\ C & D \end{pmatrix} : X₁ \times X₀ \to Y₁ \times Y₀,$$
where at `T = T₀` the top-left block `A` is `pkg.equiv` and `B`, `C`, `D` vanish.

Whenever the top-left block `A = pkg.topLeftBlock T` is invertible—which on Banach spaces holds for
every `T` in an operator-norm neighborhood of `T₀`—block Gaussian elimination via the triangular
coordinate equivalences `pkg.domTriangularEquiv T` and `pkg.codomTriangularEquiv T` conjugates `T`
into the exact block-diagonal operator `A.prodMap (pkg.schurComplement T)`, where
`pkg.schurComplement T = D - C ∘L A.inverse ∘L B : X₀ →L[𝕜] Y₀` acts between the finite-dimensional
inessential summands.

Consequently:
* the kernel and cokernel of `T` are canonically isomorphic as topological vector spaces to the
  kernel and cokernel of the finite-dimensional Schur complement `pkg.schurComplement T`;
* `T` is invertible if and only if `pkg.schurComplement T` is invertible;
* `T` is Fredholm with `T.index = (pkg.schurComplement T).index = dim X₀ - dim Y₀ = T₀.index`;
* on Banach spaces, `A.inverse`, `pkg.schurComplement T`, and both directions of the triangular
  coordinate equivalences depend continuously in operator norm on `T` at every operator with
  invertible top-left block.

## Main declarations

* `ContinuousLinearMap.FredholmPackage.topLeftBlock`,
  `ContinuousLinearMap.FredholmPackage.topRightBlock`,
  `ContinuousLinearMap.FredholmPackage.botLeftBlock`, and
  `ContinuousLinearMap.FredholmPackage.botRightBlock`: the four entries of `T` in the package
  splittings.
* `ContinuousLinearMap.FredholmPackage.schurComplement`: the finite-dimensional Schur complement
  `D - C ∘L A.inverse ∘L B : X₀ →L[𝕜] Y₀`.
* `ContinuousLinearMap.FredholmPackage.domTriangularEquiv` and
  `ContinuousLinearMap.FredholmPackage.codomTriangularEquiv`: the column- and row-elimination
  continuous linear equivalences.
* `ContinuousLinearMap.FredholmPackage.codomTriangularEquiv_comp_self_comp_domTriangularEquiv`:
  exact block-diagonalization into `A.prodMap (pkg.schurComplement T)`.
* `ContinuousLinearMap.FredholmPackage.kerEquivSchurComplementKer` and
  `ContinuousLinearMap.FredholmPackage.cokerEquivSchurComplementCoker`: continuous linear
  equivalences identifying `ker T` and `F ⧸ range T` with the kernel and cokernel of the Schur
  complement.
* `ContinuousLinearMap.FredholmPackage.isInvertible_iff_isInvertible_schurComplement`:
  invertibility reduction to the finite-dimensional Schur complement.
* `ContinuousLinearMap.FredholmPackage.isFredholm_of_isInvertible_topLeftBlock` and
  `ContinuousLinearMap.FredholmPackage.index_eq_index_schurComplement`: Fredholmness and index
  reduction to the finite-dimensional Schur complement.
* `ContinuousLinearMap.FredholmPackage.continuousAt_schurComplement`,
  `ContinuousLinearMap.FredholmPackage.continuousAt_domTriangularEquiv`,
  `ContinuousLinearMap.FredholmPackage.continuousAt_domTriangularEquiv_symm`,
  `ContinuousLinearMap.FredholmPackage.continuousAt_codomTriangularEquiv`, and
  `ContinuousLinearMap.FredholmPackage.continuousAt_codomTriangularEquiv_symm`: operator-norm
  continuity on Banach spaces.

## References

* N. Bourbaki, *Théories Spectrales*, Chapitre III, §3, n° 2–3.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Appendix A.1.
-/

public section

open Filter Module Submodule Topology

namespace ContinuousLinearMap.FredholmPackage

section Blocks

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousConstSMul 𝕜 F]
  {T₀ : E →L[𝕜] F} (pkg : T₀.FredholmPackage)

/-- Common block extractor `T ↦ P ∘L T ∘L i` as a continuous linear map on operators. -/
private noncomputable def block {X Y : Type*}
    [AddCommGroup X] [Module 𝕜 X] [TopologicalSpace X]
    [AddCommGroup Y] [Module 𝕜 Y] [TopologicalSpace Y]
    [IsTopologicalAddGroup Y] [ContinuousConstSMul 𝕜 Y]
    (i : X →L[𝕜] E) (P : F →L[𝕜] Y) :
    (E →L[𝕜] F) →L[𝕜] (X →L[𝕜] Y) :=
  (P.postcomp X).comp (i.precomp F)

/-! ### `2 × 2` blocks -/

/-- Top-left (essential-to-essential) block `X₁ →L[𝕜] Y₁` of an operator `T`. -/
noncomputable def topLeftBlock :
    (E →L[𝕜] F) →L[𝕜] (pkg.decDom.X₁ →L[𝕜] pkg.decCodom.X₁) :=
  block pkg.decDom.X₁.subtypeL pkg.decCodom.proj

/-- Defining formula for `topLeftBlock`. -/
theorem topLeftBlock_def (T : E →L[𝕜] F) :
    pkg.topLeftBlock T = pkg.decCodom.proj ∘L T ∘L pkg.decDom.X₁.subtypeL :=
  (rfl)

/-- Pointwise formula for `topLeftBlock`. -/
@[simp]
theorem topLeftBlock_apply (T : E →L[𝕜] F) (x : pkg.decDom.X₁) :
    pkg.topLeftBlock T x = pkg.decCodom.proj (T x) :=
  (rfl)

/-- Top-right (inessential-to-essential) block `X₀ →L[𝕜] Y₁` of an operator `T`. -/
noncomputable def topRightBlock :
    (E →L[𝕜] F) →L[𝕜] (pkg.decDom.X₀ →L[𝕜] pkg.decCodom.X₁) :=
  block pkg.decDom.X₀.subtypeL pkg.decCodom.proj

/-- Defining formula for `topRightBlock`. -/
theorem topRightBlock_def (T : E →L[𝕜] F) :
    pkg.topRightBlock T = pkg.decCodom.proj ∘L T ∘L pkg.decDom.X₀.subtypeL :=
  (rfl)

/-- Pointwise formula for `topRightBlock`. -/
@[simp]
theorem topRightBlock_apply (T : E →L[𝕜] F) (k : pkg.decDom.X₀) :
    pkg.topRightBlock T k = pkg.decCodom.proj (T k) :=
  (rfl)

/-- Bottom-left (essential-to-inessential) block `X₁ →L[𝕜] Y₀` of an operator `T`. -/
noncomputable def botLeftBlock :
    (E →L[𝕜] F) →L[𝕜] (pkg.decDom.X₁ →L[𝕜] pkg.decCodom.X₀) :=
  block pkg.decDom.X₁.subtypeL
    (pkg.decCodom.X₀.projectionOntoL pkg.decCodom.X₁ pkg.decCodom.isTopCompl.symm)

/-- Defining formula for `botLeftBlock`. -/
theorem botLeftBlock_def (T : E →L[𝕜] F) :
    pkg.botLeftBlock T =
      (pkg.decCodom.X₀.projectionOntoL pkg.decCodom.X₁ pkg.decCodom.isTopCompl.symm) ∘L
        T ∘L pkg.decDom.X₁.subtypeL :=
  (rfl)

/-- Pointwise formula for `botLeftBlock`. -/
@[simp]
theorem botLeftBlock_apply (T : E →L[𝕜] F) (x : pkg.decDom.X₁) :
    pkg.botLeftBlock T x =
      pkg.decCodom.X₀.projectionOntoL pkg.decCodom.X₁ pkg.decCodom.isTopCompl.symm (T x) :=
  (rfl)

/-- Bottom-right (inessential-to-inessential) block `X₀ →L[𝕜] Y₀` of an operator `T`. -/
noncomputable def botRightBlock :
    (E →L[𝕜] F) →L[𝕜] (pkg.decDom.X₀ →L[𝕜] pkg.decCodom.X₀) :=
  block pkg.decDom.X₀.subtypeL
    (pkg.decCodom.X₀.projectionOntoL pkg.decCodom.X₁ pkg.decCodom.isTopCompl.symm)

/-- Defining formula for `botRightBlock`. -/
theorem botRightBlock_def (T : E →L[𝕜] F) :
    pkg.botRightBlock T =
      (pkg.decCodom.X₀.projectionOntoL pkg.decCodom.X₁ pkg.decCodom.isTopCompl.symm) ∘L
        T ∘L pkg.decDom.X₀.subtypeL :=
  (rfl)

/-- Pointwise formula for `botRightBlock`. -/
@[simp]
theorem botRightBlock_apply (T : E →L[𝕜] F) (k : pkg.decDom.X₀) :
    pkg.botRightBlock T k =
      pkg.decCodom.X₀.projectionOntoL pkg.decCodom.X₁ pkg.decCodom.isTopCompl.symm (T k) :=
  (rfl)

/-- At the base operator `T₀`, the top-left block is `pkg.equiv`. -/
@[simp]
theorem topLeftBlock_self :
    pkg.topLeftBlock T₀ = (pkg.equiv : pkg.decDom.X₁ →L[𝕜] pkg.decCodom.X₁) := by
  ext x
  simp [topLeftBlock_def, pkg.eq_equiv]

/-- At the base operator `T₀`, the top-left block is invertible. -/
theorem isInvertible_topLeftBlock_self : (pkg.topLeftBlock T₀).IsInvertible := by
  rw [pkg.topLeftBlock_self]
  exact ContinuousLinearMap.isInvertible_equiv

/-- At the base operator `T₀`, the inverse of the top-left block is `pkg.equiv.symm`. -/
theorem inverse_topLeftBlock_self :
    (pkg.topLeftBlock T₀).inverse = (pkg.equiv.symm : pkg.decCodom.X₁ →L[𝕜] pkg.decDom.X₁) := by
  rw [pkg.topLeftBlock_self, ContinuousLinearMap.inverse_equiv]

/-- At the base operator `T₀`, the top-right block vanishes. -/
@[simp]
theorem topRightBlock_self : pkg.topRightBlock T₀ = 0 := by
  ext k
  have hk : pkg.decDom.proj (k : E) = 0 :=
    pkg.decDom.X₁.projectionOntoL_apply_right pkg.decDom.isTopCompl k
  simp [topRightBlock_def, pkg.eq_equiv, hk]

/-- At the base operator `T₀`, the bottom-left block vanishes. -/
@[simp]
theorem botLeftBlock_self : pkg.botLeftBlock T₀ = 0 := by
  ext x
  simp [botLeftBlock_def, pkg.eq_equiv,
    pkg.decCodom.X₀.projectionOntoL_apply_right pkg.decCodom.isTopCompl.symm]

/-- At the base operator `T₀`, the bottom-right block vanishes. -/
@[simp]
theorem botRightBlock_self : pkg.botRightBlock T₀ = 0 := by
  ext k
  simp [botRightBlock_def, pkg.eq_equiv]

/-! ### Schur complement and triangular coordinate equivalences -/

/-- The finite-dimensional **Schur complement** `D - C ∘L A.inverse ∘L B : X₀ →L[𝕜] Y₀` of `T`
with respect to the Fredholm package `pkg`. Outside operators with invertible top-left block `A`,
`A.inverse` is `0` and this reduces to `D`. -/
noncomputable def schurComplement (T : E →L[𝕜] F) : pkg.decDom.X₀ →L[𝕜] pkg.decCodom.X₀ :=
  pkg.botRightBlock T - pkg.botLeftBlock T ∘L (pkg.topLeftBlock T).inverse ∘L pkg.topRightBlock T

/-- Defining formula for `schurComplement`. -/
theorem schurComplement_def (T : E →L[𝕜] F) :
    pkg.schurComplement T =
      pkg.botRightBlock T -
        pkg.botLeftBlock T ∘L (pkg.topLeftBlock T).inverse ∘L pkg.topRightBlock T :=
  (rfl)

/-- Pointwise formula for `schurComplement`. -/
theorem schurComplement_apply (T : E →L[𝕜] F) (k : pkg.decDom.X₀) :
    pkg.schurComplement T k =
      pkg.botRightBlock T k -
        pkg.botLeftBlock T ((pkg.topLeftBlock T).inverse (pkg.topRightBlock T k)) :=
  (rfl)

/-- At the base operator `T₀`, the Schur complement vanishes. -/
@[simp]
theorem schurComplement_self : pkg.schurComplement T₀ = 0 := by
  simp [schurComplement]

/-- Row-elimination coordinate equivalence `F ≃L[𝕜] (Y₁ × Y₀)` sending
`y ↦ (proj y, P_Y₀ y - C (A.inverse (proj y)))`. -/
noncomputable def codomTriangularEquiv (T : E →L[𝕜] F) :
    F ≃L[𝕜] (pkg.decCodom.X₁ × pkg.decCodom.X₀) :=
  (pkg.decCodom.X₁.prodEquivOfIsTopCompl pkg.decCodom.X₀ pkg.decCodom.isTopCompl).symm.trans <|
    (ContinuousLinearEquiv.refl 𝕜 pkg.decCodom.X₁).skewProd (.refl 𝕜 pkg.decCodom.X₀)
      (-(pkg.botLeftBlock T ∘L (pkg.topLeftBlock T).inverse))

/-- Pointwise formula for `codomTriangularEquiv`. -/
@[simp]
theorem codomTriangularEquiv_apply (T : E →L[𝕜] F) (y : F) :
    pkg.codomTriangularEquiv T y =
      (pkg.decCodom.proj y,
        pkg.decCodom.X₀.projectionOntoL pkg.decCodom.X₁ pkg.decCodom.isTopCompl.symm y -
          pkg.botLeftBlock T ((pkg.topLeftBlock T).inverse (pkg.decCodom.proj y))) := by
  simp [codomTriangularEquiv, Submodule.prodEquivOfIsTopCompl_symm_apply, sub_eq_add_neg]

/-- Pointwise formula for `codomTriangularEquiv.symm`. -/
@[simp]
theorem codomTriangularEquiv_symm_apply (T : E →L[𝕜] F)
    (q : pkg.decCodom.X₁ × pkg.decCodom.X₀) :
    (pkg.codomTriangularEquiv T).symm q =
      (q.1 : F) +
        ((q.2 + pkg.botLeftBlock T ((pkg.topLeftBlock T).inverse q.1) : pkg.decCodom.X₀) : F) := by
  simp [codomTriangularEquiv, Submodule.prodEquivOfIsTopCompl_apply, sub_neg_eq_add]

/-- At the base operator `T₀`, `codomTriangularEquiv` reduces to
`(pkg.decCodom.X₁.prodEquivOfIsTopCompl pkg.decCodom.X₀ pkg.decCodom.isTopCompl).symm`. -/
@[simp]
theorem codomTriangularEquiv_self :
    pkg.codomTriangularEquiv T₀ =
      (pkg.decCodom.X₁.prodEquivOfIsTopCompl pkg.decCodom.X₀ pkg.decCodom.isTopCompl).symm := by
  ext y <;> simp [Submodule.prodEquivOfIsTopCompl_symm_apply]

/-- Operator-level expression for `pkg.codomTriangularEquiv T` as a continuous linear map. -/
theorem toContinuousLinearMap_codomTriangularEquiv (T : E →L[𝕜] F) :
    (pkg.codomTriangularEquiv T : F →L[𝕜] pkg.decCodom.X₁ × pkg.decCodom.X₀) =
      pkg.decCodom.proj.prod
        (pkg.decCodom.X₀.projectionOntoL pkg.decCodom.X₁ pkg.decCodom.isTopCompl.symm -
          pkg.botLeftBlock T ∘L (pkg.topLeftBlock T).inverse ∘L pkg.decCodom.proj) :=
  ContinuousLinearMap.ext fun y ↦ Prod.ext (by simp) (by simp)

section DomTriangular

variable [IsTopologicalAddGroup E]

/-- Column-elimination coordinate equivalence `(X₁ × X₀) ≃L[𝕜] E` sending
`(x, k) ↦ ((x - A.inverse (B k) : X₁) : E) + (k : E)`. -/
noncomputable def domTriangularEquiv (T : E →L[𝕜] F) :
    (pkg.decDom.X₁ × pkg.decDom.X₀) ≃L[𝕜] E :=
  ((ContinuousLinearEquiv.prodComm 𝕜 pkg.decDom.X₁ pkg.decDom.X₀).trans <|
    ((ContinuousLinearEquiv.refl 𝕜 pkg.decDom.X₀).skewProd
      (.refl 𝕜 pkg.decDom.X₁) (-((pkg.topLeftBlock T).inverse ∘L pkg.topRightBlock T))).trans
      (.prodComm 𝕜 pkg.decDom.X₀ pkg.decDom.X₁)).trans
    (pkg.decDom.X₁.prodEquivOfIsTopCompl pkg.decDom.X₀ pkg.decDom.isTopCompl)

/-- Pointwise formula for `domTriangularEquiv`. -/
@[simp]
theorem domTriangularEquiv_apply (T : E →L[𝕜] F) (p : pkg.decDom.X₁ × pkg.decDom.X₀) :
    pkg.domTriangularEquiv T p =
      ((p.1 - (pkg.topLeftBlock T).inverse (pkg.topRightBlock T p.2) : pkg.decDom.X₁) : E) +
        (p.2 : E) := by
  simp [domTriangularEquiv, Submodule.prodEquivOfIsTopCompl_apply, sub_eq_add_neg]

/-- Pointwise formula for `domTriangularEquiv.symm`. -/
@[simp]
theorem domTriangularEquiv_symm_apply (T : E →L[𝕜] F) (v : E) :
    (pkg.domTriangularEquiv T).symm v =
      (pkg.decDom.proj v +
          (pkg.topLeftBlock T).inverse
            (pkg.topRightBlock T
              (pkg.decDom.X₀.projectionOntoL pkg.decDom.X₁ pkg.decDom.isTopCompl.symm v)),
        pkg.decDom.X₀.projectionOntoL pkg.decDom.X₁ pkg.decDom.isTopCompl.symm v) := by
  simp [domTriangularEquiv, Submodule.prodEquivOfIsTopCompl_symm_apply]

/-- At the base operator `T₀`, `domTriangularEquiv` reduces to
`pkg.decDom.X₁.prodEquivOfIsTopCompl pkg.decDom.X₀ pkg.decDom.isTopCompl`. -/
@[simp]
theorem domTriangularEquiv_self :
    pkg.domTriangularEquiv T₀ =
      pkg.decDom.X₁.prodEquivOfIsTopCompl pkg.decDom.X₀ pkg.decDom.isTopCompl := by
  ext p
  simp [Submodule.prodEquivOfIsTopCompl_apply]

/-- Operator-level expression for `pkg.domTriangularEquiv T` as a continuous linear map. -/
theorem toContinuousLinearMap_domTriangularEquiv (T : E →L[𝕜] F) :
    (pkg.domTriangularEquiv T : (pkg.decDom.X₁ × pkg.decDom.X₀) →L[𝕜] E) =
      (pkg.decDom.X₁.prodEquivOfIsTopCompl pkg.decDom.X₀ pkg.decDom.isTopCompl :
          (pkg.decDom.X₁ × pkg.decDom.X₀) →L[𝕜] E) ∘L
        ((ContinuousLinearMap.fst 𝕜 pkg.decDom.X₁ pkg.decDom.X₀ -
            (pkg.topLeftBlock T).inverse ∘L pkg.topRightBlock T ∘L
              ContinuousLinearMap.snd 𝕜 pkg.decDom.X₁ pkg.decDom.X₀).prod
          (ContinuousLinearMap.snd 𝕜 pkg.decDom.X₁ pkg.decDom.X₀)) :=
  ContinuousLinearMap.ext fun p ↦ by simp [Submodule.prodEquivOfIsTopCompl_apply]

end DomTriangular

end Blocks

section TVS

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousConstSMul 𝕜 F]
  {T₀ : E →L[𝕜] F} (pkg : T₀.FredholmPackage)

/-- Action of `T` in the product coordinates `X₁ × X₀` and `Y₁ × Y₀` in terms of its four blocks. -/
theorem decCodom_prodEquiv_symm_apply_decDom_prodEquiv (T : E →L[𝕜] F)
    (p : pkg.decDom.X₁ × pkg.decDom.X₀) :
    (pkg.decCodom.X₁.prodEquivOfIsTopCompl pkg.decCodom.X₀ pkg.decCodom.isTopCompl).symm
        (T (pkg.decDom.X₁.prodEquivOfIsTopCompl pkg.decDom.X₀ pkg.decDom.isTopCompl p)) =
      (pkg.topLeftBlock T p.1 + pkg.topRightBlock T p.2,
        pkg.botLeftBlock T p.1 + pkg.botRightBlock T p.2) := by
  simp [Submodule.prodEquivOfIsTopCompl_apply, Submodule.prodEquivOfIsTopCompl_symm_apply, map_add]

/-! ### Exact block-diagonalization and kernel/cokernel reduction -/

/-- **Block-diagonalization of an operator with invertible top-left block.** Whenever
`A = pkg.topLeftBlock T` is invertible, the triangular coordinate equivalences conjugate `T` into
the block-diagonal operator `A.prodMap (pkg.schurComplement T)`. -/
theorem codomTriangularEquiv_comp_self_comp_domTriangularEquiv {T : E →L[𝕜] F}
    (hA : (pkg.topLeftBlock T).IsInvertible) :
    (pkg.codomTriangularEquiv T : F →L[𝕜] pkg.decCodom.X₁ × pkg.decCodom.X₀) ∘L T ∘L
        (pkg.domTriangularEquiv T : (pkg.decDom.X₁ × pkg.decDom.X₀) →L[𝕜] E) =
      (pkg.topLeftBlock T).prodMap (pkg.schurComplement T) := by
  refine ContinuousLinearMap.ext fun ⟨x, k⟩ ↦ ?_
  have hdom : pkg.domTriangularEquiv T (x, k) =
      pkg.decDom.X₁.prodEquivOfIsTopCompl pkg.decDom.X₀ pkg.decDom.isTopCompl
        (x - (pkg.topLeftBlock T).inverse (pkg.topRightBlock T k), k) := by
    simp [Submodule.prodEquivOfIsTopCompl_apply]
  have h12 := pkg.decCodom_prodEquiv_symm_apply_decDom_prodEquiv T
      (x - (pkg.topLeftBlock T).inverse (pkg.topRightBlock T k), k)
  -- First coordinate: `A (x - A⁻¹ (B k)) + B k = A x`.
  have h1 : pkg.decCodom.proj (T (pkg.domTriangularEquiv T (x, k))) = pkg.topLeftBlock T x := by
    have hf := congrArg Prod.fst h12
    simp only [Submodule.prodEquivOfIsTopCompl_symm_apply, map_sub,
      hA.self_apply_inverse] at hf
    rw [hdom, hf]
    abel
  refine Prod.ext ?_ ?_
  · simp only [comp_apply, ContinuousLinearEquiv.coe_coe, codomTriangularEquiv_apply, h1,
      coe_prodMap', Prod.map_fst]
  · -- Second coordinate: `C (x - A⁻¹ (B k)) + D k - C (A⁻¹ (A x)) = (D - C A⁻¹ B) k`.
    have h2 : pkg.decCodom.X₀.projectionOntoL pkg.decCodom.X₁ pkg.decCodom.isTopCompl.symm
          (T (pkg.domTriangularEquiv T (x, k))) =
        pkg.botLeftBlock T (x - (pkg.topLeftBlock T).inverse (pkg.topRightBlock T k)) +
          pkg.botRightBlock T k := by
      simpa only [Submodule.prodEquivOfIsTopCompl_symm_apply, ← hdom] using congrArg Prod.snd h12
    simp only [comp_apply, ContinuousLinearEquiv.coe_coe, codomTriangularEquiv_apply, h1, h2,
      map_sub, hA.inverse_apply_self, coe_prodMap', Prod.map_snd, schurComplement_apply]
    abel

/-- Pointwise form of the block-diagonalization identity. -/
theorem codomTriangularEquiv_apply_domTriangularEquiv {T : E →L[𝕜] F}
    (hA : (pkg.topLeftBlock T).IsInvertible) (p : pkg.decDom.X₁ × pkg.decDom.X₀) :
    pkg.codomTriangularEquiv T (T (pkg.domTriangularEquiv T p)) =
      (pkg.topLeftBlock T p.1, pkg.schurComplement T p.2) :=
  congr($(pkg.codomTriangularEquiv_comp_self_comp_domTriangularEquiv hA) p)

/-- Reconstruction of `T` from its invertible top-left block and finite-dimensional Schur
complement. -/
theorem eq_codomTriangularEquiv_symm_comp_prodMap_comp_domTriangularEquiv_symm {T : E →L[𝕜] F}
    (hA : (pkg.topLeftBlock T).IsInvertible) :
    T = ((pkg.codomTriangularEquiv T).symm : (pkg.decCodom.X₁ × pkg.decCodom.X₀) →L[𝕜] F) ∘L
        ((pkg.topLeftBlock T).prodMap (pkg.schurComplement T)) ∘L
        ((pkg.domTriangularEquiv T).symm : E →L[𝕜] pkg.decDom.X₁ × pkg.decDom.X₀) := by
  refine ContinuousLinearMap.ext fun v ↦ (pkg.codomTriangularEquiv T).injective ?_
  have h := pkg.codomTriangularEquiv_apply_domTriangularEquiv hA
    ((pkg.domTriangularEquiv T).symm v)
  rw [(pkg.domTriangularEquiv T).apply_symm_apply] at h
  simp only [comp_apply, ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]
  exact h

/-- For a kernel vector `v : T.ker`, `(pkg.domTriangularEquiv T).symm v` has zero first coordinate
and second coordinate the `X₀`-projection of `v`, which lies in the kernel of the Schur
complement. -/
private theorem domTriangularEquiv_symm_apply_ker {T : E →L[𝕜] F}
    (hA : (pkg.topLeftBlock T).IsInvertible) (v : T.ker) :
    (pkg.domTriangularEquiv T).symm (v : E) =
        (0, pkg.decDom.X₀.projectionOntoL pkg.decDom.X₁ pkg.decDom.isTopCompl.symm (v : E)) ∧
      pkg.schurComplement T
          (pkg.decDom.X₀.projectionOntoL pkg.decDom.X₁ pkg.decDom.isTopCompl.symm (v : E)) = 0 := by
  let p := (pkg.domTriangularEquiv T).symm (v : E)
  have hp2 :
      p.2 = pkg.decDom.X₀.projectionOntoL pkg.decDom.X₁ pkg.decDom.isTopCompl.symm (v : E) := by
    simp [p]
  have hv0 : T (v : E) = 0 := v.property
  have hdiag := pkg.codomTriangularEquiv_apply_domTriangularEquiv hA p
  rw [(pkg.domTriangularEquiv T).apply_symm_apply, hv0, map_zero] at hdiag
  have hp1 : p.1 = 0 := hA.injective ((congrArg Prod.fst hdiag).symm.trans (map_zero _).symm)
  exact ⟨Prod.ext hp1 hp2, hp2 ▸ (congrArg Prod.snd hdiag).symm⟩

/-- Projecting a kernel vector of `T` onto `X₀` lands in the kernel of the Schur complement. -/
private theorem projectionOntoL_mem_ker_schurComplement {T : E →L[𝕜] F}
    (hA : (pkg.topLeftBlock T).IsInvertible) (v : T.ker) :
    ((pkg.decDom.X₀.projectionOntoL pkg.decDom.X₁ pkg.decDom.isTopCompl.symm) ∘L
        T.ker.subtypeL) v ∈ (pkg.schurComplement T).ker := by
  simpa only [comp_apply, subtypeL_apply] using
    LinearMap.mem_ker.mpr (pkg.domTriangularEquiv_symm_apply_ker hA v).2

/-- Lifting a vector from the kernel of the Schur complement via `domTriangularEquiv` lands in
`ker T`. -/
private theorem domTriangularEquiv_inr_mem_ker {T : E →L[𝕜] F}
    (hA : (pkg.topLeftBlock T).IsInvertible) (k : (pkg.schurComplement T).ker) :
    ((pkg.domTriangularEquiv T : (pkg.decDom.X₁ × pkg.decDom.X₀) →L[𝕜] E) ∘L
        .inr 𝕜 pkg.decDom.X₁ pkg.decDom.X₀ ∘L (pkg.schurComplement T).ker.subtypeL) k ∈ T.ker := by
  have hk0 : pkg.schurComplement T (k : pkg.decDom.X₀) = 0 := k.property
  apply LinearMap.mem_ker.mpr
  rw [ContinuousLinearMap.coe_coe]
  simp only [comp_apply, inr_apply, subtypeL_apply, ContinuousLinearEquiv.coe_coe]
  apply (pkg.codomTriangularEquiv T).injective
  rw [pkg.codomTriangularEquiv_apply_domTriangularEquiv hA, map_zero, hk0, map_zero]
  rfl

/-- **Kernel reduction to the Schur complement.** When the top-left block of `T` is invertible,
projection to `X₀` restricts to a continuous linear equivalence between `ker T` and the kernel of
the finite-dimensional Schur complement. -/
noncomputable def kerEquivSchurComplementKer {T : E →L[𝕜] F}
    (hA : (pkg.topLeftBlock T).IsInvertible) :
    T.ker ≃L[𝕜] (pkg.schurComplement T).ker :=
  ContinuousLinearEquiv.ofContinuousLinearMap
    (((pkg.decDom.X₀.projectionOntoL pkg.decDom.X₁ pkg.decDom.isTopCompl.symm ∘L
        T.ker.subtypeL)).codRestrict (pkg.schurComplement T).ker
      (pkg.projectionOntoL_mem_ker_schurComplement hA))
    (((pkg.domTriangularEquiv T : (pkg.decDom.X₁ × pkg.decDom.X₀) →L[𝕜] E) ∘L
        .inr 𝕜 pkg.decDom.X₁ pkg.decDom.X₀ ∘L (pkg.schurComplement T).ker.subtypeL).codRestrict
      T.ker (pkg.domTriangularEquiv_inr_mem_ker hA))
    (ContinuousLinearMap.ext fun k ↦ by
      rw [← Subtype.coe_inj]
      simp only [comp_apply, coe_codRestrict_apply, inr_apply, subtypeL_apply,
        ContinuousLinearEquiv.coe_coe, domTriangularEquiv_apply, map_add,
        pkg.decDom.X₀.projectionOntoL_apply_right pkg.decDom.isTopCompl.symm, zero_add,
        pkg.decDom.X₀.projectionOntoL_apply_left pkg.decDom.isTopCompl.symm, id_apply])
    (ContinuousLinearMap.ext fun v ↦ by
      rw [← Subtype.coe_inj]
      simp only [comp_apply, coe_codRestrict_apply, inr_apply, subtypeL_apply,
        ContinuousLinearEquiv.coe_coe, id_apply]
      rw [← (pkg.domTriangularEquiv_symm_apply_ker hA v).1,
        (pkg.domTriangularEquiv T).apply_symm_apply])

/-- `kerEquivSchurComplementKer` acts by the projection onto `pkg.decDom.X₀` along
`pkg.decDom.X₁`. -/
@[simp]
theorem coe_kerEquivSchurComplementKer_apply {T : E →L[𝕜] F}
    (hA : (pkg.topLeftBlock T).IsInvertible) (v : T.ker) :
    (pkg.kerEquivSchurComplementKer hA v : pkg.decDom.X₀) =
      pkg.decDom.X₀.projectionOntoL pkg.decDom.X₁ pkg.decDom.isTopCompl.symm v :=
  (rfl)

/-- `kerEquivSchurComplementKer.symm` lifts a Schur-complement kernel vector via
`domTriangularEquiv`. -/
@[simp]
theorem coe_kerEquivSchurComplementKer_symm_apply {T : E →L[𝕜] F}
    (hA : (pkg.topLeftBlock T).IsInvertible) (k : (pkg.schurComplement T).ker) :
    ((pkg.kerEquivSchurComplementKer hA).symm k : E) =
      pkg.domTriangularEquiv T (0, k) :=
  (rfl)

/-- Every value of the Schur complement, viewed in the ambient codomain `F`, lies in `range T`. -/
private theorem coe_schurComplement_mem_range {T : E →L[𝕜] F}
    (hA : (pkg.topLeftBlock T).IsInvertible) (k : pkg.decDom.X₀) :
    ((pkg.schurComplement T k : pkg.decCodom.X₀) : F) ∈ T.range := by
  refine ⟨pkg.domTriangularEquiv T (0, k), ?_⟩
  rw [ContinuousLinearMap.coe_coe]
  apply (pkg.codomTriangularEquiv T).injective
  rw [pkg.codomTriangularEquiv_apply_domTriangularEquiv hA, map_zero]
  simp

/-- **Cokernel reduction to the Schur complement.** When the top-left block of `T` is invertible,
the second coordinate of `pkg.codomTriangularEquiv T` descends to a continuous linear equivalence
from `F ⧸ range T` onto `Y₀ ⧸ range (pkg.schurComplement T)`, with inverse induced by the inclusion
`Y₀ ↪ F`. -/
noncomputable def cokerEquivSchurComplementCoker {T : E →L[𝕜] F}
    (hA : (pkg.topLeftBlock T).IsInvertible) :
    (F ⧸ T.range) ≃L[𝕜] (pkg.decCodom.X₀ ⧸ (pkg.schurComplement T).range) :=
  ContinuousLinearEquiv.ofContinuousLinearMap
    (T.range.liftQL
      ((pkg.schurComplement T).range.mkQL ∘L .snd 𝕜 pkg.decCodom.X₁ pkg.decCodom.X₀ ∘L
        (pkg.codomTriangularEquiv T : F →L[𝕜] pkg.decCodom.X₁ × pkg.decCodom.X₀))
      (by
        rintro _ ⟨u, rfl⟩
        rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, ContinuousLinearMap.coe_coe]
        let p := (pkg.domTriangularEquiv T).symm u
        have hp : pkg.domTriangularEquiv T p = u := (pkg.domTriangularEquiv T).apply_symm_apply u
        simp only [comp_apply, ContinuousLinearEquiv.coe_coe, coe_snd', mkQL_apply,
          Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, ← hp,
          pkg.codomTriangularEquiv_apply_domTriangularEquiv hA]
        exact LinearMap.mem_range_self _ p.2))
    ((pkg.schurComplement T).range.liftQL (T.range.mkQL ∘L pkg.decCodom.X₀.subtypeL)
      (by
        rintro _ ⟨k, rfl⟩
        rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, ContinuousLinearMap.coe_coe]
        simp only [comp_apply, subtypeL_apply, mkQL_apply, Submodule.mkQ_apply,
          Submodule.Quotient.mk_eq_zero]
        exact pkg.coe_schurComplement_mem_range hA k))
    (ContinuousLinearMap.ext fun w ↦ by
      obtain ⟨y₀, rfl⟩ := (pkg.schurComplement T).range.mkQ_surjective w
      simp)
    (ContinuousLinearMap.ext fun z ↦ by
      obtain ⟨y, rfl⟩ := T.range.mkQ_surjective z
      simp only [comp_apply, liftQL_apply, Submodule.mkQ_apply, Submodule.liftQ_apply,
        ContinuousLinearMap.coe_coe, ContinuousLinearEquiv.coe_coe, coe_snd',
        mkQL_apply, subtypeL_apply, id_apply]
      symm
      rw [Submodule.Quotient.eq]
      let q := pkg.codomTriangularEquiv T y
      have hdiff : pkg.codomTriangularEquiv T (y - ((q.2 : pkg.decCodom.X₀) : F)) = (q.1, 0) := by
        rw [map_sub]
        have hq2 : pkg.codomTriangularEquiv T ((q.2 : pkg.decCodom.X₀) : F) = (0, q.2) := by simp
        rw [hq2]
        ext <;> simp [q]
      refine ⟨pkg.domTriangularEquiv T ((pkg.topLeftBlock T).inverse q.1, 0), ?_⟩
      rw [ContinuousLinearMap.coe_coe]
      apply (pkg.codomTriangularEquiv T).injective
      rw [hdiff, pkg.codomTriangularEquiv_apply_domTriangularEquiv hA, hA.self_apply_inverse,
        map_zero])

/-- On a quotient representative `y : F`, `cokerEquivSchurComplementCoker` takes the class of the
second coordinate of `pkg.codomTriangularEquiv T y`. -/
@[simp]
theorem cokerEquivSchurComplementCoker_apply_mk {T : E →L[𝕜] F}
    (hA : (pkg.topLeftBlock T).IsInvertible) (y : F) :
    pkg.cokerEquivSchurComplementCoker hA (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk ((pkg.codomTriangularEquiv T y).2) :=
  (rfl)

/-- `cokerEquivSchurComplementCoker.symm` sends the class of `y₀ : Y₀` to the class of
`(y₀ : F)`. -/
@[simp]
theorem cokerEquivSchurComplementCoker_symm_apply_mk {T : E →L[𝕜] F}
    (hA : (pkg.topLeftBlock T).IsInvertible) (y₀ : pkg.decCodom.X₀) :
    (pkg.cokerEquivSchurComplementCoker hA).symm (Submodule.Quotient.mk y₀) =
      Submodule.Quotient.mk (y₀ : F) :=
  (rfl)

/-- **Invertibility reduction to the Schur complement.** Whenever `A = pkg.topLeftBlock T` is
invertible, `T` is invertible if and only if its finite-dimensional Schur complement is. -/
theorem isInvertible_iff_isInvertible_schurComplement {T : E →L[𝕜] F}
    (hA : (pkg.topLeftBlock T).IsInvertible) :
    T.IsInvertible ↔ (pkg.schurComplement T).IsInvertible := by
  have h := congrArg ContinuousLinearMap.IsInvertible
    (pkg.codomTriangularEquiv_comp_self_comp_domTriangularEquiv hA)
  simpa only [isInvertible_equiv_comp, isInvertible_comp_equiv, isInvertible_prodMap_iff,
    hA, true_and] using iff_of_eq h

/-- **Index reduction to the Schur complement.** Whenever the top-left block of `T` is invertible,
`T` has the same index as its finite-dimensional Schur complement. -/
theorem index_eq_index_schurComplement {T : E →L[𝕜] F}
    (hA : (pkg.topLeftBlock T).IsInvertible) :
    T.index = (pkg.schurComplement T).index := by
  rw [T.index_eq_finrank_sub, (pkg.schurComplement T).index_eq_finrank_sub,
    LinearEquiv.finrank_eq (pkg.kerEquivSchurComplementKer hA).toLinearEquiv,
    LinearEquiv.finrank_eq (pkg.cokerEquivSchurComplementCoker hA).toLinearEquiv]

/-- Whenever the top-left block of `T` is invertible, the index of `T` is `dim X₀ - dim Y₀`. -/
theorem index_eq_finrank_sub_of_isInvertible_topLeftBlock {T : E →L[𝕜] F}
    (hA : (pkg.topLeftBlock T).IsInvertible) :
    T.index = (finrank 𝕜 pkg.decDom.X₀ : ℤ) - finrank 𝕜 pkg.decCodom.X₀ := by
  have := pkg.decDom.finite_X₀
  have := pkg.decCodom.finite_X₀
  rw [pkg.index_eq_index_schurComplement hA, ContinuousLinearMap.index_eq_of_finiteDimensional]

/-- Whenever the top-left block of `T` is invertible, `T` has the same index as `T₀`. -/
theorem index_eq_of_isInvertible_topLeftBlock {T : E →L[𝕜] F}
    (hA : (pkg.topLeftBlock T).IsInvertible) :
    T.index = T₀.index := by
  rw [pkg.index_eq_finrank_sub_of_isInvertible_topLeftBlock hA,
    pkg.index_eq_finrank_sub_of_isInvertible_topLeftBlock pkg.isInvertible_topLeftBlock_self]

/-- **Fredholmness from an invertible top-left block.** Over a complete scalar field, any operator
whose top-left block in `pkg` is invertible is Fredholm. -/
theorem isFredholm_of_isInvertible_topLeftBlock [CompleteSpace 𝕜]
    [ContinuousSMul 𝕜 E] [ContinuousSMul 𝕜 F] [T2Space F]
    {T : E →L[𝕜] F} (hA : (pkg.topLeftBlock T).IsInvertible) :
    T.IsFredholm := by
  have := pkg.decDom.finite_X₀
  have := pkg.decCodom.finite_X₀
  have hprod : ((pkg.topLeftBlock T).prodMap (pkg.schurComplement T)).IsFredholm :=
    hA.isFredholm.prodMap (ContinuousLinearMap.isFredholm_of_finiteDimensional _)
  rw [pkg.eq_codomTriangularEquiv_symm_comp_prodMap_comp_domTriangularEquiv_symm hA]
  exact (hprod.equiv_comp (pkg.codomTriangularEquiv T).symm).comp_equiv
    (pkg.domTriangularEquiv T).symm

end TVS

/-! ### Continuity and openness in operator norm -/

section Normed

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {T₀ : E →L[𝕜] F} (pkg : T₀.FredholmPackage)

section CompleteDom

variable [CompleteSpace E]

/-- If `pkg.topLeftBlock T` is invertible, it stays invertible in an operator-norm neighborhood
of `T`. -/
theorem eventually_nhds_isInvertible_topLeftBlock_of_isInvertible {T : E →L[𝕜] F}
    (hA : (pkg.topLeftBlock T).IsInvertible) :
    ∀ᶠ S in 𝓝 T, (pkg.topLeftBlock S).IsInvertible := by
  have : CompleteSpace pkg.decDom.X₁ := pkg.decDom.isTopCompl.isClosed.isComplete.completeSpace_coe
  exact pkg.topLeftBlock.continuous.continuousAt.eventually hA.eventually_nhds

/-- The inverse of the top-left block is continuous in operator norm at every operator where the
top-left block is invertible. -/
theorem continuousAt_inverse_topLeftBlock {T : E →L[𝕜] F}
    (hA : (pkg.topLeftBlock T).IsInvertible) :
    ContinuousAt (fun S ↦ (pkg.topLeftBlock S).inverse) T :=
  pkg.topLeftBlock.continuous.continuousAt.clm_inverse_of_eventually_isInvertible
    (pkg.eventually_nhds_isInvertible_topLeftBlock_of_isInvertible hA)

/-- The Schur complement is continuous in operator norm at every operator where the top-left block
is invertible. -/
theorem continuousAt_schurComplement {T : E →L[𝕜] F}
    (hA : (pkg.topLeftBlock T).IsInvertible) :
    ContinuousAt pkg.schurComplement T := by
  have := pkg.continuousAt_inverse_topLeftBlock hA
  unfold schurComplement
  fun_prop

/-- The forward column-elimination equivalence `pkg.domTriangularEquiv S` depends continuously on
`S` in operator norm at every `T` with invertible top-left block. -/
theorem continuousAt_domTriangularEquiv {T : E →L[𝕜] F}
    (hA : (pkg.topLeftBlock T).IsInvertible) :
    ContinuousAt
      (fun S ↦ (pkg.domTriangularEquiv S : (pkg.decDom.X₁ × pkg.decDom.X₀) →L[𝕜] E)) T := by
  have := pkg.continuousAt_inverse_topLeftBlock hA
  simp_rw [pkg.toContinuousLinearMap_domTriangularEquiv]
  fun_prop

/-- The inverse column-elimination equivalence `(pkg.domTriangularEquiv S).symm` depends
continuously on `S` in operator norm at every `T` with invertible top-left block. -/
theorem continuousAt_domTriangularEquiv_symm {T : E →L[𝕜] F}
    (hA : (pkg.topLeftBlock T).IsInvertible) :
    ContinuousAt
      (fun S ↦ ((pkg.domTriangularEquiv S).symm : E →L[𝕜] pkg.decDom.X₁ × pkg.decDom.X₀)) T := by
  simpa only [ContinuousLinearMap.inverse_equiv] using
    (pkg.continuousAt_domTriangularEquiv hA).clm_inverse_of_eventually_isInvertible
      (.of_forall fun _ ↦ ContinuousLinearMap.isInvertible_equiv)

/-- The forward row-elimination equivalence `pkg.codomTriangularEquiv S` depends continuously on
`S` in operator norm at every `T` with invertible top-left block. -/
theorem continuousAt_codomTriangularEquiv {T : E →L[𝕜] F}
    (hA : (pkg.topLeftBlock T).IsInvertible) :
    ContinuousAt
      (fun S ↦ (pkg.codomTriangularEquiv S : F →L[𝕜] pkg.decCodom.X₁ × pkg.decCodom.X₀)) T := by
  have := pkg.continuousAt_inverse_topLeftBlock hA
  simp_rw [pkg.toContinuousLinearMap_codomTriangularEquiv]
  fun_prop

/-- The inverse row-elimination equivalence `(pkg.codomTriangularEquiv S).symm` depends
continuously on `S` in operator norm at every `T` with invertible top-left block. -/
theorem continuousAt_codomTriangularEquiv_symm {T : E →L[𝕜] F}
    (hA : (pkg.topLeftBlock T).IsInvertible) :
    ContinuousAt
      (fun S ↦ ((pkg.codomTriangularEquiv S).symm :
        (pkg.decCodom.X₁ × pkg.decCodom.X₀) →L[𝕜] F)) T := by
  simpa only [ContinuousLinearMap.inverse_equiv] using
    (pkg.continuousAt_codomTriangularEquiv hA).clm_inverse_of_eventually_isInvertible
      (.of_forall fun _ ↦ ContinuousLinearMap.isInvertible_equiv)

end CompleteDom

end Normed

end ContinuousLinearMap.FredholmPackage

end

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.SesquilinearForm.Orthogonal
public import TauCeti.Analysis.Normed.Module.Dual.Bilinear
import Mathlib.Analysis.LocallyConvex.WeakSpace
import TauCeti.Analysis.Normed.Module.DoubleDual
import TauCeti.Analysis.Normed.Module.Dual.Adjoint
import TauCeti.Analysis.Normed.Module.Dual.Functoriality
import TauCeti.Analysis.Normed.Module.Dual.Goldstine
import TauCeti.Analysis.Normed.Module.Dual.Quotient
import TauCeti.Analysis.Normed.Module.Dual.Submodule

/-!
# Biduals of submodules, kernels of bidual adjoints, and norm approximation from the bidual

For a submodule `S` of a seminormed space `E` over a field satisfying `IsRCLikeNormedField`,
Hahn–Banach identifies `S*` isometrically with `E* ⧸ Sᗮ` (`Submodule.quotientAnnihilatorEquivDual`),
and quotient duality identifies `(E* ⧸ Sᗮ)*` isometrically with the annihilator `Sᗮᗮ` of `Sᗮ` in
`E**` (`Submodule.quotientDualEquivAnnihilator`). Composing the two identifies `S**` isometrically
with `Sᗮᗮ`, with underlying map the bidual adjoint `S.subtypeL**` of the inclusion. Neither
completeness of `E` nor closedness of `S` is needed.

When `T : E →L[𝕜] F` is a bounded operator between Banach spaces with closed range, the
closed-range theorem gives `range T* = (ker T)ᗮ`, so `ker T** = (range T*)ᗮ = (ker T)ᗮᗮ`. Combined
with the submodule identification, `(ker T).subtypeL**` identifies `(ker T)**` isometrically with
`ker T**`.

Finally, over `ℝ` or `ℂ`, an operator equation solved in the bidual can be approximated in norm on
the corresponding ball of the original space: if `Φ ∈ E**` has `‖Φ‖ ≤ r` and `T** Φ = J_F y`, then
Goldstine's theorem places `Φ` in the weak-star closure of the `r`-ball of `E`, weak-star
continuity of `T**` places `y` in the weak closure of `T '' closedBall 0 r`, and convexity upgrades
weak closure to norm closure (`Convex.toWeakSpace_closure`). Applied to a finite product, finitely
many operator equations `Sᵢ** Φ = J (zᵢ)` can be approximately solved simultaneously in norm by a
single vector of norm at most `r`.

## Main definitions

* `LinearIsometryEquiv.precomp`: precomposition with a linear isometric equivalence as a linear
  isometric equivalence on continuous duals.
* `Submodule.bidualEquivAnnihilator`: the isometric equivalence `S** ≃ₗᵢ[𝕜] Sᗮᗮ`.
* `ContinuousLinearMap.bidualKerEquivKerPrecompPrecomp`: the isometric equivalence
  `(ker T)** ≃ₗᵢ[𝕜] ker T**` for a closed-range operator `T` between Banach spaces.

## Main results

* `Submodule.coe_bidualEquivAnnihilator`, `Submodule.norm_comp_precomp_subtypeL`,
  `Submodule.range_precomp_precomp_subtypeL`: `S.subtypeL**` is an isometry onto `Sᗮᗮ`.
* `ContinuousLinearMap.ker_precomp_precomp_eq_orthogonalBilin_ker`: `ker T** = (ker T)ᗮᗮ` when
  `T` has closed range.
* `ContinuousLinearMap.mem_closure_image_closedBall_of_precomp_precomp_eq`: if `‖Φ‖ ≤ r` and
  `T** Φ = J_F y`, then `y ∈ closure (T '' closedBall 0 r)`.
* `StrongDual.exists_norm_le_and_forall_norm_sub_lt`: simultaneous norm approximation on a closed
  ball for finitely many operators whose bidual adjoints send `Φ` into canonical images.

## References

* R. E. Megginson, *An Introduction to Banach Space Theory*, §2.6.
* W. Rudin, *Functional Analysis*, 2nd ed., Chapter 4.
-/

public section

open Metric NormedSpace Set

-- Shorten instance search for submodules and operators on iterated duals.
attribute [local instance] ContinuousLinearMap.strongDualSeminormedAddCommGroup
  ContinuousLinearMap.strongDualNormedSpace
  ContinuousLinearMap.strongBidualSeminormedAddCommGroup
  ContinuousLinearMap.strongBidualNormedSpace

namespace LinearIsometryEquiv

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Precomposition with a linear isometric equivalence is a linear isometric equivalence between
continuous duals. -/
def precomp (e : E ≃ₗᵢ[𝕜] F) : StrongDual 𝕜 F ≃ₗᵢ[𝕜] StrongDual 𝕜 E where
  toFun f := f.comp e.toLinearIsometry.toContinuousLinearMap
  invFun g := g.comp e.symm.toLinearIsometry.toContinuousLinearMap
  left_inv f := by ext x; simp
  right_inv g := by ext x; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' f := by
    apply le_antisymm
    · exact (f.opNorm_comp_le _).trans <|
        (mul_le_of_le_one_right (norm_nonneg f) e.toLinearIsometry.norm_toContinuousLinearMap_le)
    · have h : f = (f.comp e.toLinearIsometry.toContinuousLinearMap).comp
          e.symm.toLinearIsometry.toContinuousLinearMap := by ext x; simp
      exact (congrArg norm h).le.trans <| ((f.comp _).opNorm_comp_le _).trans <|
        mul_le_of_le_one_right (norm_nonneg _) e.symm.toLinearIsometry.norm_toContinuousLinearMap_le

/-- Precomposing a functional with `e` evaluates on `x` by applying the functional to `e x`. -/
@[simp]
theorem precomp_apply (e : E ≃ₗᵢ[𝕜] F) (f : StrongDual 𝕜 F) (x : E) :
    e.precomp f x = f (e x) :=
  (rfl)

/-- The inverse of `LinearIsometryEquiv.precomp` is precomposition with `e.symm`. -/
@[simp]
theorem precomp_symm (e : E ≃ₗᵢ[𝕜] F) : e.precomp.symm = e.symm.precomp :=
  (rfl)

end LinearIsometryEquiv

namespace Submodule

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The bidual of a submodule `S` is isometrically the annihilator in `E**` of the annihilator of
`S` in `E*`. Its underlying map into `E**` is the bidual adjoint of `S.subtypeL`. -/
noncomputable def bidualEquivAnnihilator (S : Submodule 𝕜 E) :
    StrongDual 𝕜 (StrongDual 𝕜 S) ≃ₗᵢ[𝕜]
      (S.orthogonalBilin (topDualPairing 𝕜 E).flip).orthogonalBilin
        (topDualPairing 𝕜 (StrongDual 𝕜 E)).flip :=
  S.quotientAnnihilatorEquivDual.precomp.trans
    (S.orthogonalBilin (topDualPairing 𝕜 E).flip).quotientDualEquivAnnihilator

/-- `S.bidualEquivAnnihilator` evaluates on an ambient functional `f` by restricting `f` to `S`. -/
@[simp]
theorem bidualEquivAnnihilator_apply (S : Submodule 𝕜 E) (Φ : StrongDual 𝕜 (StrongDual 𝕜 S))
    (f : StrongDual 𝕜 E) :
    (S.bidualEquivAnnihilator Φ : StrongDual 𝕜 (StrongDual 𝕜 E)) f = Φ (f.comp S.subtypeL) := by
  simp [bidualEquivAnnihilator]

/-- Forgetting the annihilator subtype recovers the bidual adjoint of `S.subtypeL`. -/
theorem coe_bidualEquivAnnihilator (S : Submodule 𝕜 E) (Φ : StrongDual 𝕜 (StrongDual 𝕜 S)) :
    (S.bidualEquivAnnihilator Φ : StrongDual 𝕜 (StrongDual 𝕜 E)) =
      ContinuousLinearMap.precomp 𝕜 (ContinuousLinearMap.precomp 𝕜 S.subtypeL) Φ := by
  ext f
  simp

/-- Evaluating `S.bidualEquivAnnihilator.symm` on the restriction of an ambient functional `f`
applies the ambient bidual element to `f`. -/
@[simp]
theorem bidualEquivAnnihilator_symm_apply_comp_subtypeL (S : Submodule 𝕜 E)
    (Ψ : (S.orthogonalBilin (topDualPairing 𝕜 E).flip).orthogonalBilin
      (topDualPairing 𝕜 (StrongDual 𝕜 E)).flip)
    (f : StrongDual 𝕜 E) :
    S.bidualEquivAnnihilator.symm Ψ (f.comp S.subtypeL) =
      (Ψ : StrongDual 𝕜 (StrongDual 𝕜 E)) f := by
  simp [bidualEquivAnnihilator]

/-- Precomposing a bidual element of `S` with restriction `E* → S*` preserves norms. -/
@[simp]
theorem norm_comp_precomp_subtypeL (S : Submodule 𝕜 E) (Φ : StrongDual 𝕜 (StrongDual 𝕜 S)) :
    ‖Φ.comp (ContinuousLinearMap.precomp 𝕜 S.subtypeL)‖ = ‖Φ‖ := by
  change ‖ContinuousLinearMap.precomp 𝕜 (ContinuousLinearMap.precomp 𝕜 S.subtypeL) Φ‖ = ‖Φ‖
  rw [← coe_bidualEquivAnnihilator, Submodule.norm_coe, LinearIsometryEquiv.norm_map]

/-- The bidual adjoint of the inclusion of a submodule preserves norms. -/
theorem norm_precomp_precomp_subtypeL (S : Submodule 𝕜 E) (Φ : StrongDual 𝕜 (StrongDual 𝕜 S)) :
    ‖ContinuousLinearMap.precomp 𝕜 (ContinuousLinearMap.precomp 𝕜 S.subtypeL) Φ‖ = ‖Φ‖ :=
  S.norm_comp_precomp_subtypeL Φ

/-- The range of the bidual adjoint of `S.subtypeL` is the annihilator in `E**` of `Sᗮ`. -/
theorem range_precomp_precomp_subtypeL (S : Submodule 𝕜 E) :
    (ContinuousLinearMap.precomp 𝕜
      (ContinuousLinearMap.precomp 𝕜 S.subtypeL : StrongDual 𝕜 E →L[𝕜] StrongDual 𝕜 S)).range =
      (S.orthogonalBilin (topDualPairing 𝕜 E).flip).orthogonalBilin
        (topDualPairing 𝕜 (StrongDual 𝕜 E)).flip := by
  ext Ψ
  constructor
  · rintro ⟨Φ, rfl⟩
    simp only [ContinuousLinearMap.coe_coe, ← coe_bidualEquivAnnihilator]
    exact (S.bidualEquivAnnihilator Φ).2
  · intro hΨ
    refine ⟨S.bidualEquivAnnihilator.symm ⟨Ψ, hΨ⟩, ?_⟩
    simp only [ContinuousLinearMap.coe_coe, ← coe_bidualEquivAnnihilator,
      LinearIsometryEquiv.apply_symm_apply]

end Submodule

namespace ContinuousLinearMap

section ClosedRange

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

/-- If a bounded operator between Banach spaces has closed range, the kernel of its bidual adjoint
is the annihilator in `E**` of `(ker T)ᗮ`. -/
theorem ker_precomp_precomp_eq_orthogonalBilin_ker (T : E →L[𝕜] F)
    (hT : IsClosed (T.range : Set F)) :
    (precomp 𝕜 (precomp 𝕜 T : StrongDual 𝕜 F →L[𝕜] StrongDual 𝕜 E) :
        StrongDual 𝕜 (StrongDual 𝕜 E) →L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 F)).ker =
      (T.ker.orthogonalBilin (topDualPairing 𝕜 E).flip).orthogonalBilin
        (topDualPairing 𝕜 (StrongDual 𝕜 E)).flip := by
  rw [ker_precomp_eq_orthogonalBilin_range, T.range_precomp_eq_orthogonalBilin_ker hT]

/-- For a bounded operator `T` between Banach spaces with closed range, the bidual adjoint of the
inclusion of `ker T` identifies `(ker T)**` isometrically with `ker T**`. -/
noncomputable def bidualKerEquivKerPrecompPrecomp (T : E →L[𝕜] F)
    (hT : IsClosed (T.range : Set F)) :
    StrongDual 𝕜 (StrongDual 𝕜 T.ker) ≃ₗᵢ[𝕜]
      (precomp 𝕜 (precomp 𝕜 T : StrongDual 𝕜 F →L[𝕜] StrongDual 𝕜 E) :
        StrongDual 𝕜 (StrongDual 𝕜 E) →L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 F)).ker :=
  T.ker.bidualEquivAnnihilator.trans
    (LinearIsometryEquiv.ofEq (R' := 𝕜) _ _ (T.ker_precomp_precomp_eq_orthogonalBilin_ker hT).symm)

/-- `T.bidualKerEquivKerPrecompPrecomp` evaluates on an ambient functional `f` by restricting `f`
to `ker T`. -/
@[simp]
theorem bidualKerEquivKerPrecompPrecomp_apply (T : E →L[𝕜] F) (hT : IsClosed (T.range : Set F))
    (Φ : StrongDual 𝕜 (StrongDual 𝕜 T.ker)) (f : StrongDual 𝕜 E) :
    (T.bidualKerEquivKerPrecompPrecomp hT Φ : StrongDual 𝕜 (StrongDual 𝕜 E)) f =
      Φ (f.comp T.ker.subtypeL) := by
  simp [bidualKerEquivKerPrecompPrecomp]

/-- Forgetting the kernel subtype recovers the bidual adjoint of `T.ker.subtypeL`. -/
theorem coe_bidualKerEquivKerPrecompPrecomp (T : E →L[𝕜] F) (hT : IsClosed (T.range : Set F))
    (Φ : StrongDual 𝕜 (StrongDual 𝕜 T.ker)) :
    (T.bidualKerEquivKerPrecompPrecomp hT Φ : StrongDual 𝕜 (StrongDual 𝕜 E)) =
      precomp 𝕜 (precomp 𝕜 T.ker.subtypeL) Φ := by
  ext f
  simp

/-- Evaluating `(T.bidualKerEquivKerPrecompPrecomp hT).symm` on the restriction of an ambient
functional `f` applies the ambient bidual element to `f`. -/
@[simp]
theorem bidualKerEquivKerPrecompPrecomp_symm_apply_comp_subtypeL (T : E →L[𝕜] F)
    (hT : IsClosed (T.range : Set F))
    (Ψ : (precomp 𝕜 (precomp 𝕜 T : StrongDual 𝕜 F →L[𝕜] StrongDual 𝕜 E) :
      StrongDual 𝕜 (StrongDual 𝕜 E) →L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 F)).ker)
    (f : StrongDual 𝕜 E) :
    (T.bidualKerEquivKerPrecompPrecomp hT).symm Ψ (f.comp T.ker.subtypeL) =
      (Ψ : StrongDual 𝕜 (StrongDual 𝕜 E)) f := by
  simp [bidualKerEquivKerPrecompPrecomp]

end ClosedRange

section Approximation

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- If `Φ ∈ E**` has `‖Φ‖ ≤ r` and the bidual adjoint of `T : E →L[𝕜] F` sends `Φ` to the canonical
image of `y ∈ F`, then `y` lies in the norm closure of `T '' closedBall 0 r`. -/
theorem mem_closure_image_closedBall_of_precomp_precomp_eq (T : E →L[𝕜] F)
    {Φ : StrongDual 𝕜 (StrongDual 𝕜 E)} {r : ℝ} (hr : ‖Φ‖ ≤ r) {y : F}
    (hy : precomp 𝕜 (precomp 𝕜 T : StrongDual 𝕜 F →L[𝕜] StrongDual 𝕜 E) Φ =
      inclusionInDoubleDual 𝕜 F y) :
    y ∈ closure (T '' closedBall 0 r) := by
  let : NormedSpace ℝ E := .restrictScalars ℝ 𝕜 E
  let : IsScalarTower ℝ 𝕜 E := .restrictScalars ℝ 𝕜 E
  let : NormedSpace ℝ F := .restrictScalars ℝ 𝕜 F
  let : IsScalarTower ℝ 𝕜 F := .restrictScalars ℝ 𝕜 F
  -- Goldstine places `Φ` in the weak-star closure of the `r`-ball of `E`; `T**` pushes this to
  -- the weak-star bidual of `F`.
  have hΦ : StrongDual.toWeakDual Φ ∈
      closure (inclusionInDoubleDualWeak 𝕜 E '' (toWeakSpace 𝕜 E '' closedBall 0 r)) := by
    rw [closure_image_inclusionInDoubleDualWeak_closedBall, map_zero, mem_preimage,
      StrongDual.toStrongDual_toWeakDual]
    exact (mem_closedBall_zero_iff (E := StrongDual 𝕜 (StrongDual 𝕜 E))).2 hr
  have himg := image_closure_subset_closure_image T.continuous_toWeakDual_precomp_precomp
    (mem_image_of_mem _ hΦ)
  simp only [StrongDual.toStrongDual_toWeakDual, hy, image_image,
    T.toWeakDual_precomp_precomp_inclusionInDoubleDualWeak] at himg
  have hy' : inclusionInDoubleDualWeak 𝕜 F (toWeakSpace 𝕜 F y) ∈
      closure (inclusionInDoubleDualWeak 𝕜 F '' (toWeakSpace 𝕜 F '' (T '' closedBall 0 r))) := by
    simpa only [inclusionInDoubleDualWeak_apply, LinearEquiv.symm_apply_apply, image_image]
      using himg
  -- Pull back along the inducing canonical map into `F**`, then upgrade weak closure to norm
  -- closure by convexity of `T '' closedBall 0 r`.
  rw [← mem_preimage,
    ← (isInducing_inclusionInDoubleDualWeak 𝕜 F).closure_eq_preimage_closure_image] at hy'
  have hconv : Convex ℝ (T '' closedBall 0 r) :=
    (convex_closedBall 0 r).linear_image ((T : E →ₗ[𝕜] F).restrictScalars ℝ)
  rw [← hconv.toWeakSpace_closure 𝕜] at hy'
  exact (toWeakSpace 𝕜 F).injective.mem_set_image.1 hy'

/-- Pointwise form of `mem_closure_image_closedBall_of_precomp_precomp_eq`: if `‖Φ‖ ≤ r` and
`Φ (f ∘ T) = f y` for every `f ∈ F*`, then `y ∈ closure (T '' closedBall 0 r)`. -/
theorem mem_closure_image_closedBall_of_forall_apply_comp_eq (T : E →L[𝕜] F)
    {Φ : StrongDual 𝕜 (StrongDual 𝕜 E)} {r : ℝ} (hr : ‖Φ‖ ≤ r) {y : F}
    (hy : ∀ f : StrongDual 𝕜 F, Φ (f.comp T) = f y) :
    y ∈ closure (T '' closedBall 0 r) :=
  T.mem_closure_image_closedBall_of_precomp_precomp_eq hr (ext hy)

end Approximation

end ContinuousLinearMap

namespace StrongDual

/-- Simultaneous norm approximation from a bidual element: if `Φ ∈ E**` satisfies `‖Φ‖ ≤ r` and
`Φ (f ∘ S i) = f (z i)` for every `i` in a finite index type and every `f ∈ (Z i)*`, then for every
`ε > 0` there is `x : E` with `‖x‖ ≤ r` and `‖S i x - z i‖ < ε` for all `i`. -/
theorem exists_norm_le_and_forall_norm_sub_lt {𝕜 E : Type*} [RCLike 𝕜]
    [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
    (Φ : StrongDual 𝕜 (StrongDual 𝕜 E)) {ι : Type*} [Finite ι] {Z : ι → Type*}
    [∀ i, SeminormedAddCommGroup (Z i)] [∀ i, NormedSpace 𝕜 (Z i)]
    (S : ∀ i, E →L[𝕜] Z i) (z : ∀ i, Z i)
    (hz : ∀ i (f : StrongDual 𝕜 (Z i)), Φ (f.comp (S i)) = f (z i))
    {r : ℝ} (hr : ‖Φ‖ ≤ r) {ε : ℝ} (hε : 0 < ε) :
    ∃ x : E, ‖x‖ ≤ r ∧ ∀ i, ‖S i x - z i‖ < ε := by
  cases nonempty_fintype ι
  classical
  have hmem : z ∈ closure ((ContinuousLinearMap.pi S) '' closedBall 0 r) := by
    refine (ContinuousLinearMap.pi S).mem_closure_image_closedBall_of_forall_apply_comp_eq hr
      fun F ↦ ?_
    have hF : F.comp (ContinuousLinearMap.pi S) =
        ∑ i, (F.comp (.single 𝕜 Z i)).comp (S i) := by
      ext x
      rw [ContinuousLinearMap.comp_apply,
        ← ContinuousLinearMap.sum_comp_single (L := F) (v := ContinuousLinearMap.pi S x)]
      simp
    rw [hF, map_sum]
    simpa only [hz] using ContinuousLinearMap.sum_comp_single (L := F) (v := z)
  obtain ⟨_, ⟨x, hx, rfl⟩, hdist⟩ := Metric.mem_closure_iff.1 hmem ε hε
  rw [dist_comm, dist_eq_norm] at hdist
  exact ⟨x, mem_closedBall_zero_iff.1 hx, (pi_norm_lt_iff hε).1 hdist⟩

end StrongDual

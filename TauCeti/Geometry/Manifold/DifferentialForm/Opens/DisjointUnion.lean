/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
public import TauCeti.Geometry.Manifold.DifferentialForm.Regularity

import TauCeti.Geometry.Manifold.DifferentialForm.Naturality
import TauCeti.Geometry.Manifold.DifferentialForm.Opens

/-!
# Smooth differential forms on disjoint open unions

For pairwise disjoint open subsets `U : ι → Opens M` of a manifold with union `W = ⨆ i, U i`,
restriction along the open inclusions `U i ≤ W` identifies `F`-valued smooth differential forms on
`W` linearly with families of smooth differential forms on the `U i`
(`TauCeti.SmoothForm.piEquiv`), and this product equivalence commutes componentwise with the
exterior derivative (`TauCeti.SmoothForm.piEquiv_mextDerivₗ`).

## References
* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapters 14 and 17.
-/

public section

noncomputable section

open Function TopologicalSpace
open scoped Manifold

namespace TauCeti

variable {E H M F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {U : ι → Opens M} {k : ℕ}

private theorem ext_roughForm_iSup {γ₁ γ₂ : RoughForm I (⨆ i, U i : Opens M) F k}
    (h : ∀ i, TauCeti.mpullback I I (Opens.inclusion (le_iSup U i)) γ₁ =
      TauCeti.mpullback I I (Opens.inclusion (le_iSup U i)) γ₂) : γ₁ = γ₂ := by
  funext x; obtain ⟨i, hi⟩ := Opens.mem_iSup.mp x.property; ext v
  have hx := DFunLike.congr_fun (congrFun (h i) ⟨x, hi⟩) v
  rwa [mpullback_inclusion_apply, mpullback_inclusion_apply] at hx

private def piecewiseRoughForm (U : ι → Opens M) (η : ∀ i, RoughForm I (U i) F k) :
    RoughForm I (⨆ i, U i : Opens M) F k :=
  fun x ↦ η (Classical.choose (Opens.mem_iSup.mp x.property))
    ⟨x, Classical.choose_spec (Opens.mem_iSup.mp x.property)⟩

private theorem mpullback_inclusion_piecewiseRoughForm (hdisj : Pairwise (Disjoint on U))
    (η : ∀ i, RoughForm I (U i) F k) (i : ι) :
    TauCeti.mpullback I I (Opens.inclusion (le_iSup U i)) (piecewiseRoughForm U η) = η i := by
  funext y; ext v; rw [mpullback_inclusion_apply]
  have haux : ∀ {j : ι} (hj : (y : M) ∈ U j), (η j ⟨y, hj⟩ : E [⋀^Fin k]→L[ℝ] F) = η i y := by
    intro j hj
    obtain rfl := hdisj.eq fun h ↦ (h.le_bot ⟨hj, y.property⟩).elim
    rfl
  exact DFunLike.congr_fun
    (haux (Classical.choose_spec
      (Opens.mem_iSup.mp (Opens.inclusion (le_iSup U i) y).property))) v

variable (I) in
/-- Smooth forms on a union of pairwise disjoint opens `U i` are linearly equivalent to families of
smooth forms on the `U i`, via restriction along the open inclusions. -/
def SmoothForm.piEquiv [IsManifold I 1 M] (hdisj : Pairwise (Disjoint on U)) (k : ℕ) :
    SmoothForm I (⨆ i, U i : Opens M) F k ≃ₗ[ℝ] ∀ i, SmoothForm I (U i) F k where
  toFun φ i := SmoothForm.mpullback (Opens.inclusion (le_iSup U i)) (contMDiff_inclusion _) φ
  map_add' φ ψ := funext fun _ ↦ map_add _ φ ψ
  map_smul' c φ := funext fun _ ↦ map_smul _ c φ
  invFun η := ⟨piecewiseRoughForm U fun i ↦ (η i).val,
    (IsSmoothForm.of_mpullback_inclusion (le_iSup U) (fun x ↦ Opens.mem_iSup.mp x.property)
      fun i ↦ by
        rw [mpullback_inclusion_piecewiseRoughForm hdisj]; exact (η i).isSmoothForm
    ).mem_smoothBundleForms⟩
  left_inv _ := Subtype.ext <| ext_roughForm_iSup fun _ ↦ by
    dsimp only; rw [mpullback_inclusion_piecewiseRoughForm hdisj, SmoothForm.coe_mpullback]
  right_inv _ := funext fun _ ↦ Subtype.ext <| by
    dsimp only; rw [SmoothForm.coe_mpullback, mpullback_inclusion_piecewiseRoughForm hdisj]

variable (I) in
/-- Component `i` of `SmoothForm.piEquiv` is pullback along `U i ≤ ⨆ j, U j`. -/
@[simp]
theorem SmoothForm.piEquiv_apply [IsManifold I 1 M] (hdisj : Pairwise (Disjoint on U)) (k : ℕ)
    (φ : SmoothForm I (⨆ i, U i : Opens M) F k) (i : ι) :
    SmoothForm.piEquiv I hdisj k φ i =
      SmoothForm.mpullback (Opens.inclusion (le_iSup U i)) (contMDiff_inclusion _) φ := (rfl)

variable (I) in
/-- The product decomposition of smooth forms on pairwise disjoint opens commutes with `d`. -/
theorem SmoothForm.piEquiv_mextDerivₗ [IsManifold I 2 M] (hdisj : Pairwise (Disjoint on U))
    (k : ℕ) (φ : SmoothForm I (⨆ i, U i : Opens M) F k) (i : ι) :
    SmoothForm.piEquiv I hdisj (k + 1) (mextDerivₗ I k φ) i =
      mextDerivₗ I k (SmoothForm.piEquiv I hdisj k φ i) :=
  (SmoothForm.mextDerivₗ_mpullback (Opens.inclusion (le_iSup U i)) (contMDiff_inclusion _) k φ).symm

end TauCeti

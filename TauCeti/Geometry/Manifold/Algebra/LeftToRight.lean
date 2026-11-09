/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import Mathlib.Geometry.Manifold.Algebra.SMul
public import TauCeti.Topology.Algebra.MulAction.LeftToRight

/-!
# Manifold structure and smooth actions on left-to-right group action conversions

When `M` is a charted space (or a `C^n` manifold), the type copy `TauCeti.LeftToRightAction G M`
inherits the charted-space and `C^n` manifold structures of `M` and is canonically `C^n`
diffeomorphic to `M` via `TauCeti.LeftToRightAction.diffeomorph`.

When a group `G` acts on `M` by `C^n` maps (`ContMDiffConstSMul`), the converted right action
`MulOpposite.op g • y = g⁻¹ • y` on `LeftToRightAction G M` is also pointwise `C^n`. When `G` is a
`C^n` Lie group acting jointly `C^n`-smoothly on `M` (`ContMDiffSMul`), the converted right action
`(y, g) ↦ MulOpposite.op g • y` and its orbit maps `g ↦ MulOpposite.op g • y` are `C^n`.

## Main definitions

* `TauCeti.LeftToRightAction.diffeomorph I' n G M`: the canonical `C^n` diffeomorphism
  `M ≃ₘ^n⟮I', I'⟯ LeftToRightAction G M`.

## Main results

* `TauCeti.LeftToRightAction.instChartedSpace`, `TauCeti.LeftToRightAction.instIsManifold`:
  `LeftToRightAction G M` inherits the charted-space and `C^n` manifold structures of `M`.
* `TauCeti.LeftToRightAction.inverse_mfderiv_equiv`: the inverse of `mfderiv I' I' (equiv G M) x`
  is `mfderiv I' I' (equiv G M).symm (equiv G M x)`.
* `TauCeti.LeftToRightAction.instContMDiffConstSMul`: converting a pointwise `C^n` left action
  yields a pointwise `C^n` right action on `LeftToRightAction G M`.
* `TauCeti.LeftToRightAction.contMDiff_op_smul`, `TauCeti.LeftToRightAction.contMDiff_orbit`:
  converting a jointly `C^n` left action of a `C^n` Lie group yields a jointly `C^n` right action
  and `C^n` orbit maps on `LeftToRightAction G M`.

## Implementation notes

We do not register a `ChartedSpace H Gᵐᵒᵖ` instance on `Gᵐᵒᵖ` (which would conflict with
`chartedSpaceSelf : ChartedSpace Eᵐᵒᵖ Eᵐᵒᵖ` on normed opposite algebras), so joint smoothness of the
converted right action is stated directly on `(p : LeftToRightAction G M × G) ↦ op p.2 • p.1` rather
than via `ContMDiffSMul` on `Gᵐᵒᵖ`. Pointwise smoothness uses `ContMDiffConstSMul`, which requires
no manifold structure on `Gᵐᵒᵖ`.

## References

* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, Springer, 1993,
  §10.2 and §10.6 (conversion between left and right principal actions via inversion).
-/

public section

open MulOpposite
open scoped ContDiff Manifold

namespace TauCeti.LeftToRightAction

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {G : Type*}
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {M : Type*} [TopologicalSpace M] [chartsM : ChartedSpace H' M]

/-- `LeftToRightAction G M` inherits the charted-space structure of `M`. -/
instance instChartedSpace : ChartedSpace H' (LeftToRightAction G M) := chartsM

/-- `LeftToRightAction G M` inherits the `C^n` manifold structure of `M`. -/
instance instIsManifold {n : ℕ∞ω} [IsManifold I' n M] :
    IsManifold I' n (LeftToRightAction G M) := ‹_›

variable (I') in
/-- The canonical `C^n` diffeomorphism between `M` and `LeftToRightAction G M`. -/
def diffeomorph (n : ℕ∞ω) (G M : Type*) [TopologicalSpace M] [ChartedSpace H' M] :
    M ≃ₘ^n⟮I', I'⟯ LeftToRightAction G M where
  toEquiv := equiv G M
  contMDiff_toFun := contMDiff_id
  contMDiff_invFun := contMDiff_id

@[simp]
theorem diffeomorph_toEquiv (n : ℕ∞ω) :
    (diffeomorph I' n G M).toEquiv = equiv G M :=
  (rfl)

@[simp]
theorem coe_diffeomorph (n : ℕ∞ω) :
    ⇑(diffeomorph I' n G M) = equiv G M :=
  (rfl)

@[simp]
theorem coe_diffeomorph_symm (n : ℕ∞ω) :
    ⇑(diffeomorph I' n G M).symm = (equiv G M).symm :=
  (rfl)

/-- `equiv G M` is `C^n` for every `n`. -/
theorem contMDiff_equiv {n : ℕ∞ω} :
    ContMDiff I' I' n (equiv G M) :=
  (diffeomorph I' n G M).contMDiff

/-- `(equiv G M).symm` is `C^n` for every `n`. -/
theorem contMDiff_equiv_symm {n : ℕ∞ω} :
    ContMDiff I' I' n (equiv G M).symm :=
  (diffeomorph I' n G M).symm.contMDiff

/-- The inverse of `mfderiv I' I' (equiv G M) x` is
`mfderiv I' I' (equiv G M).symm (equiv G M x)`. -/
@[simp]
theorem inverse_mfderiv_equiv (x : M) :
    (mfderiv I' I' (equiv G M) x).inverse =
      mfderiv I' I' (equiv G M).symm (equiv G M x) := by
  have h1 : mfderiv I' I' ((equiv G M).symm ∘ equiv G M) x = ContinuousLinearMap.id 𝕜 _ := by
    rw [Equiv.symm_comp_self, mfderiv_id]
  rw [mfderiv_comp x ((contMDiff_equiv_symm (n := 1)).mdifferentiableAt one_ne_zero)
    ((contMDiff_equiv (n := 1)).mdifferentiableAt one_ne_zero)] at h1
  have h2 : mfderiv I' I' (equiv G M ∘ (equiv G M).symm) (equiv G M x) =
      ContinuousLinearMap.id 𝕜 _ := by
    rw [Equiv.self_comp_symm, mfderiv_id]
  rw [mfderiv_comp (equiv G M x) ((contMDiff_equiv (n := 1)).mdifferentiableAt one_ne_zero)
    ((contMDiff_equiv_symm (n := 1)).mdifferentiableAt one_ne_zero),
    Equiv.symm_apply_apply] at h2
  exact ContinuousLinearMap.inverse_eq h2 h1

variable [Group G]

/-- If `G` acts on `M` by `C^n` maps (`ContMDiffConstSMul`), then `Gᵐᵒᵖ` acts on
`LeftToRightAction G M` by `C^n` maps via `op g • p = g⁻¹ • p`. -/
instance instContMDiffConstSMul {n : ℕ∞ω} [MulAction G M] [ContMDiffConstSMul I' n G M] :
    ContMDiffConstSMul I' n Gᵐᵒᵖ (LeftToRightAction G M) where
  contMDiff_const_smul γ := by
    have hfun : (fun y : LeftToRightAction G M => γ • y) =
        fun y : LeftToRightAction G M => equiv G M ((unop γ)⁻¹ • (equiv G M).symm y) := by
      funext y
      obtain ⟨x, rfl⟩ := (equiv G M).surjective y
      conv_lhs => rw [← op_unop γ]
      rw [op_smul_equiv, Equiv.symm_apply_apply]
    rw [hfun]
    exact contMDiff_equiv.comp ((contMDiff_const_smul (unop γ)⁻¹).comp contMDiff_equiv_symm)

section LieGroup

variable [TopologicalSpace G] [ChartedSpace H G]

/-- Converting a jointly `C^n` left action of a `C^n` Lie group `G` on `M` produces a jointly `C^n`
right action `(p, g) ↦ op g • p = g⁻¹ • p` on `LeftToRightAction G M`. -/
theorem contMDiff_op_smul {n : ℕ∞ω} [LieGroup I n G] [MulAction G M]
    [ContMDiffSMul I I' n G M] :
    ContMDiff (I'.prod I) I' n (fun p : LeftToRightAction G M × G => op p.2 • p.1) := by
  have hfun : (fun p : LeftToRightAction G M × G => op p.2 • p.1) =
      fun p : LeftToRightAction G M × G =>
        equiv G M (p.2⁻¹ • (equiv G M).symm p.1) := by
    funext ⟨y, g⟩
    obtain ⟨x, rfl⟩ := (equiv G M).surjective y
    simp
  rw [hfun]
  exact contMDiff_equiv.comp
    (contMDiff_snd.inv.smul (contMDiff_equiv_symm.comp contMDiff_fst))

/-- Each right orbit map `g ↦ op g • y` on `LeftToRightAction G M` is `C^n` when `G` is a `C^n`
Lie group acting `C^n`-smoothly on `M`. -/
theorem contMDiff_orbit {n : ℕ∞ω} [LieGroup I n G] [MulAction G M]
    [ContMDiffSMul I I' n G M] (y : LeftToRightAction G M) :
    ContMDiff I I' n (fun g : G => op g • y) :=
  contMDiff_op_smul.comp (contMDiff_const.prodMk contMDiff_id)

end LieGroup

end TauCeti.LeftToRightAction

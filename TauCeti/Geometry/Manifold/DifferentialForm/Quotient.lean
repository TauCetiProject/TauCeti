/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.LocalDiffeomorph
public import TauCeti.Geometry.Manifold.Instances.Quotient

/-!
# Descending invariant forms to quotient manifolds

Let a group `G` act freely and properly discontinuously by `C^n` maps on a `C^n` manifold `M`,
with `n ≠ 0`. The orbit projection `q : M → M ⧸ G` is then a surjective `C^n` local
diffeomorphism (`TauCeti.isLocalDiffeomorph_quotientMk`). A form `α` on `M` that is invariant
under every element of `G` descends to the orbit space: there is exactly one form `β` on `M ⧸ G`
with `q^* β = α`. At the orbit of `x` it is `α_x` read through the inverse of the derivative of
`q` at `x`; invariance makes this independent of the representative.

The descended form `TauCeti.RoughForm.descend G α` is defined for any form, through a chosen
representative of each orbit, and `TauCeti.RoughForm.mpullback_quotientMk_descend` shows that it
pulls back to `α` when `α` is invariant. For a smooth action, the descent of an invariant smooth
form is smooth, which gives `TauCeti.SmoothForm.descend`. It is the unique form pulling back to
`α`, it commutes with the exterior derivative, and it is closed exactly when `α` is.

This is how forms are put on quotients of covering spaces, such as the mapping torus of a
diffeomorphism, whose forms are the forms on `ℝ × M` invariant under the deck group.

## Main definitions

* `TauCeti.RoughForm.descend G α`: the descent of a form `α` on `M` to the orbit space of `G`.
* `TauCeti.SmoothForm.descend α hα`: the descent of a `G`-invariant smooth form, as a smooth form.

## Main results

* `TauCeti.RoughForm.mpullback_quotientMk_descend`: an invariant form is the pullback of its
  descent along the orbit projection.
* `TauCeti.SmoothForm.eq_descend_iff`: the descent is the unique form pulling back to `α`.
* `TauCeti.SmoothForm.mextDerivₗ_descend`: the exterior derivative of the descent of `α` is the
  descent of the exterior derivative of `α`.
* `TauCeti.SmoothForm.isClosed_descend_iff`: the descent of `α` is closed exactly when `α` is.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in
  Mathematics 218, Springer, 2013, Chapter 21 (quotients by discrete group actions) and
  Chapter 14 (pullbacks of differential forms).
-/

public section

noncomputable section

open Bundle Set Filter
open scoped Manifold Topology ContDiff

namespace TauCeti

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}
  {G : Type*} [Group G] [MulAction G M]
  [ProperlyDiscontinuousSMul G M] [ContinuousConstSMul G M] [IsCancelSMul G M] [T2Space M]
  [LocallyCompactSpace M]

namespace RoughForm

variable (G) in
/-- The descent of a form `α` on `M` to the orbit space of `G`. At an orbit `y` it is the form `α`
at the chosen representative `y.out`, read through the inverse of the derivative of the orbit
projection there. When `α` is invariant under `G` this does not depend on the choice of
representatives, and the descent pulls back to `α` along the orbit projection
(`TauCeti.RoughForm.mpullback_quotientMk_descend`). -/
def descend (α : RoughForm I M F k) : RoughForm I (MulAction.orbitRel.Quotient G M) F k :=
  fun y ↦ (α y.out).compContinuousLinearMap
    ((mfderiv I I (Quotient.mk (MulAction.orbitRel G M)) y.out).inverse ∘L
      (tangentSpaceCast I y (Quotient.mk (MulAction.orbitRel G M) y.out) :
        TangentSpace I y →L[ℝ] TangentSpace I (Quotient.mk (MulAction.orbitRel G M) y.out)))

/-- Evaluation of the descent of a form: tangent vectors at the orbit `y` are sent through the
inverse of the derivative of the orbit projection at the chosen representative `y.out`. -/
theorem descend_apply (α : RoughForm I M F k) (y : MulAction.orbitRel.Quotient G M)
    (v : Fin k → TangentSpace I y) :
    descend G α y v = α y.out fun i ↦
      (mfderiv I I (Quotient.mk (MulAction.orbitRel G M)) y.out).inverse
        (tangentSpaceCast I y (Quotient.mk (MulAction.orbitRel G M) y.out) (v i)) :=
  (rfl)

variable {n : WithTop ℕ∞} [IsManifold I n M] [ContMDiffConstSMul I n G M]

omit [IsManifold I n M] in
/-- The derivative of the orbit projection at `g • x`, composed with the derivative of `g • ·` at
`x`, is the derivative of the orbit projection at `x`: the orbit projection is invariant. -/
private theorem mfderiv_quotientMk_smul_apply (hq : MDifferentiable I I
    (Quotient.mk (MulAction.orbitRel G M))) (hn : n ≠ 0) (g : G) (x : M) (v : TangentSpace I x) :
    mfderiv I I (Quotient.mk (MulAction.orbitRel G M)) (g • x)
        (mfderiv I I (g • · : M → M) x v) =
      mfderiv I I (Quotient.mk (MulAction.orbitRel G M)) x v := by
  have hinv : Quotient.mk (MulAction.orbitRel G M) ∘ (g • · : M → M) =
      Quotient.mk (MulAction.orbitRel G M) :=
    funext fun y ↦ Quotient.sound ⟨g, rfl⟩
  rw [← ContinuousLinearMap.comp_apply, ← mfderiv_comp x (hq (g • x))
    ((contMDiff_const_smul (I := I) (n := n) g).mdifferentiable hn x), hinv]
  -- The two sides differ only in how the tangent space at the orbit of `x` is written.
  rfl

/-- A form invariant under `G` is the pullback of its descent along the orbit projection. -/
theorem mpullback_quotientMk_descend (hn : n ≠ 0) {α : RoughForm I M F k}
    (hα : ∀ g : G, mpullback I I (g • ·) α = α) :
    mpullback I I (Quotient.mk (MulAction.orbitRel G M)) (descend G α) = α := by
  have hq := isLocalDiffeomorph_quotientMk (I := I) (n := n) (G := G) (M := M)
  funext x
  refine ContinuousAlternatingMap.ext fun v ↦ ?_
  -- The chosen representative of the orbit of `x` is `g • x` for some `g`.
  obtain ⟨g, hg⟩ : ∃ g : G, g • x = (Quotient.mk (MulAction.orbitRel G M) x).out :=
    MulAction.mem_orbit_iff.mp (Quotient.mk_out (s := MulAction.orbitRel G M) x)
  have hderiv (w : TangentSpace I x) :
      (mfderiv I I (Quotient.mk (MulAction.orbitRel G M)) (g • x)).inverse
          (mfderiv I I (Quotient.mk (MulAction.orbitRel G M)) x w) =
        mfderiv I I (g • · : M → M) x w :=
    (hq.isInvertible_mfderiv hn (g • x)).inverse_apply_eq.mpr
      (mfderiv_quotientMk_smul_apply (hq.mdifferentiable hn) hn g x w).symm
  -- `tangentSpaceCast` is the identity of the model space.
  have hcast (w : TangentSpace I x) :
      (mfderiv I I (Quotient.mk (MulAction.orbitRel G M)) (g • x)).inverse
          (tangentSpaceCast I (Quotient.mk (MulAction.orbitRel G M) x)
            (Quotient.mk (MulAction.orbitRel G M) (g • x))
            (mfderiv I I (Quotient.mk (MulAction.orbitRel G M)) x w)) =
        mfderiv I I (g • · : M → M) x w :=
    hderiv w
  rw [mpullback_apply, descend_apply, ← hg]
  simp only [hcast]
  rw [← mpullback_apply, hα]

end RoughForm

namespace SmoothForm

variable [IsManifold I ∞ M] [ContMDiffConstSMul I ∞ G M]

omit [ProperlyDiscontinuousSMul G M] [ContinuousConstSMul G M] [IsCancelSMul G M] [T2Space M]
  [LocallyCompactSpace M] in
/-- A smooth form invariant under `G` is invariant as a rough form. -/
private theorem coe_invariant {α : SmoothForm I M F k}
    (hα : ∀ g : G, mpullback (g • ·) (contMDiff_const_smul g) α = α) (g : G) :
    TauCeti.mpullback I I (g • ·) α.1 = α.1 := by
  rw [← coe_mpullback _ (contMDiff_const_smul g), hα g]

variable {α : SmoothForm I M F k}

/-- The descent of a smooth form `α` invariant under `G` to the orbit space of `G`: the unique
smooth form whose pullback along the orbit projection is `α` (`TauCeti.SmoothForm.eq_descend_iff`).
-/
def descend (α : SmoothForm I M F k)
    (hα : ∀ g : G, mpullback (g • ·) (contMDiff_const_smul g) α = α) :
    SmoothForm I (MulAction.orbitRel.Quotient G M) F k :=
  ⟨RoughForm.descend G α.1, IsSmoothForm.mem_smoothForms <|
    ((isLocalDiffeomorph_quotientMk (n := ∞)).isSmoothForm_mpullback_iff (m := ∞)
      Quotient.mk_surjective (by simp)).mp <| by
      rw [RoughForm.mpullback_quotientMk_descend (n := ∞) (by simp) (coe_invariant hα)]
      exact α.isSmoothForm⟩

variable {hα : ∀ g : G, mpullback (g • ·) (contMDiff_const_smul g) α = α}

/-- The underlying rough form of the descent of a smooth form is its rough descent. -/
@[simp]
theorem coe_descend : (descend α hα).1 = RoughForm.descend G α.1 := (rfl)

/-- An invariant smooth form is the pullback of its descent along the orbit projection. -/
@[simp]
theorem mpullback_quotientMk_descend :
    mpullback (Quotient.mk (MulAction.orbitRel G M)) isLocalDiffeomorph_quotientMk.contMDiff
      (descend α hα) = α :=
  Subtype.ext <| (coe_mpullback _ _ _).trans <|
    RoughForm.mpullback_quotientMk_descend (n := ∞) (by simp) (coe_invariant hα)

/-- Pullback of smooth forms along the orbit projection is injective. -/
theorem mpullback_quotientMk_injective :
    Function.Injective (mpullback (F := F) (k := k)
      (Quotient.mk (MulAction.orbitRel G M)) (isLocalDiffeomorph_quotientMk (I := I)).contMDiff) :=
  fun _ _ h ↦
  Subtype.ext <| (isLocalDiffeomorph_quotientMk (n := ∞)).mpullback_injective (by simp)
    Quotient.mk_surjective (by simpa only [coe_mpullback] using congrArg Subtype.val h)

/-- The descent of an invariant smooth form `α` is the unique smooth form on the orbit space whose
pullback along the orbit projection is `α`. -/
theorem eq_descend_iff {β : SmoothForm I (MulAction.orbitRel.Quotient G M) F k} :
    β = descend α hα ↔
      mpullback (Quotient.mk (MulAction.orbitRel G M)) isLocalDiffeomorph_quotientMk.contMDiff β =
        α :=
  ⟨fun h ↦ h ▸ mpullback_quotientMk_descend, fun h ↦
    mpullback_quotientMk_injective (h.trans mpullback_quotientMk_descend.symm)⟩

/-- The exterior derivative of the descent of an invariant smooth form is the descent of its
exterior derivative. -/
theorem mextDerivₗ_descend :
    mextDerivₗ I k (descend α hα) = descend (mextDerivₗ I k α)
      (fun g ↦ by rw [← mextDerivₗ_mpullback, hα g]) := by
  rw [eq_descend_iff, ← mextDerivₗ_mpullback, mpullback_quotientMk_descend]

/-- The descent of an invariant smooth form is closed exactly when the form is closed. -/
@[simp]
theorem isClosed_descend_iff : (descend α hα).IsClosed ↔ α.IsClosed := by
  rw [← (isLocalDiffeomorph_quotientMk (n := ∞)).isClosed_mpullback_iff Quotient.mk_surjective]
  exact iff_of_eq (congrArg IsClosed mpullback_quotientMk_descend)

end SmoothForm

end TauCeti

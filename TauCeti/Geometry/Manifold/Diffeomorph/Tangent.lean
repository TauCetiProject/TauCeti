/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Algebra.SMul
public import TauCeti.Geometry.Manifold.Diffeomorph.Basic
public import TauCeti.Geometry.Manifold.MFDeriv.Curve
import TauCeti.Geometry.Manifold.ContMDiff.MFDeriv

/-!
# Tangent lifts of diffeomorphisms

The differential of a smooth diffeomorphism, bundled over the map itself, is a smooth
diffeomorphism between the tangent bundles. Its inverse is the tangent lift of the inverse
diffeomorphism. This packages the tangent map in a form suitable for transporting vector fields,
integral curves, and their maximal domains.

The construction is functorial: tangent lifts preserve identity maps, inverses, and composition.
The underlying function is Mathlib's `tangentMap`; no parallel tangent-map API is introduced.

## Main definitions and results

* `Diffeomorph.tangent`: the tangent lift of a smooth diffeomorphism.
* `Diffeomorph.tangentHomeomorph`: the tangent map of a `C^n` diffeomorphism, `n ≥ 1`, as a
  homeomorphism of tangent bundles.
* `Diffeomorph.tangent_symm`: taking a tangent lift commutes with inversion.
* `Diffeomorph.tangent_symm_mk`: the inverse tangent lift acts on fibres by `(dh_x)⁻¹`.
* `Diffeomorph.tangent_refl`: the tangent lift of the identity is the identity.
* `Diffeomorph.tangent_trans`: taking a tangent lift commutes with composition.
* `Diffeomorph.tangent_curveVelocityLift`: tangent lifts carry the velocity lift of a curve to
  the velocity lift of its image.
* `TangentBundle.instMulAction`: the tangent lift `g • v = dg_x v` of an action of a group by
  smooth maps, again an action by smooth maps (`TangentBundle.instContMDiffConstSMul`), and jointly
  smooth when the action is (`TangentBundle.instContMDiffSMul`).
* `Diffeomorph.tangent_constSmul`: the tangent lift of `x ↦ g • x` is `v ↦ g • v`.
-/

public section

open Bundle Filter Function
open scoped ContDiff Manifold Topology

noncomputable section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners 𝕜 F H'}
  {H'' : Type*} [TopologicalSpace H''] {K : ModelWithCorners 𝕜 G H''}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J 1 N]
  {P : Type*} [TopologicalSpace P] [ChartedSpace H'' P] [IsManifold K 1 P]

namespace Diffeomorph

open TauCeti.Manifold

/-- The tangent lift of a smooth diffeomorphism. Its value at `(x, v)` is
`(h x, mfderiv I J h x v)`, and its inverse is the tangent lift of `h.symm`. -/
protected def tangent (h : M ≃ₘ⟮I, J⟯ N) :
    TangentBundle I M ≃ₘ⟮I.tangent, J.tangent⟯ TangentBundle J N where
  toEquiv :=
    { toFun := tangentMap I J h
      invFun := tangentMap J I h.symm
      left_inv := tangentMap_symm_apply h (by simp)
      right_inv := tangentMap_apply_symm h (by simp) }
  contMDiff_toFun := h.contMDiff.contMDiff_tangentMap (by simp)
  contMDiff_invFun := h.symm.contMDiff.contMDiff_tangentMap (by simp)

/-- The underlying function of the tangent lift is Mathlib's `tangentMap`. -/
@[simp]
theorem coe_tangent (h : M ≃ₘ⟮I, J⟯ N) :
    ⇑h.tangent = tangentMap I J h := by
  rw [Diffeomorph.tangent]
  rfl

/-- The inverse of a tangent lift is the tangent lift of the inverse diffeomorphism. -/
@[simp]
theorem tangent_symm (h : M ≃ₘ⟮I, J⟯ N) :
    h.tangent.symm = h.symm.tangent :=
  Diffeomorph.ext fun _ ↦ rfl

/-- The inverse tangent lift sends `(h x, w)` to `(x, (dh_x)⁻¹ w)`. -/
theorem tangent_symm_mk (h : M ≃ₘ⟮I, J⟯ N) (x : M) (w : TangentSpace J (h x)) :
    h.tangent.symm (TotalSpace.mk' F (h x) w) =
      TotalSpace.mk' E x ((mfderiv I J h x).inverse w) := by
  simpa only [tangent_symm, coe_tangent] using h.tangentMap_symm_mk (by simp) x w

/-- The tangent lift of the identity diffeomorphism is the identity diffeomorphism of the tangent
bundle. -/
@[simp]
theorem tangent_refl :
    (Diffeomorph.refl I M ∞).tangent = Diffeomorph.refl I.tangent (TangentBundle I M) ∞ := by
  apply Diffeomorph.ext
  intro z
  rw [coe_tangent, coe_refl]
  exact congrFun tangentMap_id z

/-- Tangent lift commutes with composition of smooth diffeomorphisms. -/
@[simp]
theorem tangent_trans (h : M ≃ₘ⟮I, J⟯ N) (g : N ≃ₘ⟮J, K⟯ P) :
    (h.trans g).tangent = h.tangent.trans g.tangent := by
  apply Diffeomorph.ext
  intro z
  simpa only [coe_tangent, coe_trans, Function.comp_apply] using
    tangentMap_comp_at z ((g.mdifferentiable (by simp)) (h z.proj))
      ((h.mdifferentiable (by simp)) z.proj)

/-- The tangent map of a `C^n` diffeomorphism, `n ≥ 1`, as a homeomorphism of tangent bundles.
Its value at `(x, v)` is `(h x, mfderiv I J h x v)`, and its inverse is the tangent map of
`h.symm`. For smooth diffeomorphisms, `Diffeomorph.tangent` upgrades it to a diffeomorphism. -/
def tangentHomeomorph {n : WithTop ℕ∞} (h : M ≃ₘ^n⟮I, J⟯ N) (hn : 1 ≤ n) :
    TangentBundle I M ≃ₜ TangentBundle J N where
  toFun := tangentMap I J h
  invFun := tangentMap J I h.symm
  left_inv := h.tangentMap_symm_apply (zero_lt_one.trans_le hn).ne'
  right_inv := h.tangentMap_apply_symm (zero_lt_one.trans_le hn).ne'
  continuous_toFun := h.contMDiff.continuous_tangentMap hn
  continuous_invFun := h.symm.contMDiff.continuous_tangentMap hn

/-- The underlying function of `Diffeomorph.tangentHomeomorph` is Mathlib's `tangentMap`. -/
@[simp]
theorem coe_tangentHomeomorph {n : WithTop ℕ∞} (h : M ≃ₘ^n⟮I, J⟯ N) (hn : 1 ≤ n) :
    ⇑(h.tangentHomeomorph hn) = tangentMap I J h :=
  (rfl)

/-- The inverse of `Diffeomorph.tangentHomeomorph` is the tangent map of the inverse. -/
@[simp]
theorem coe_tangentHomeomorph_symm {n : WithTop ℕ∞} (h : M ≃ₘ^n⟮I, J⟯ N) (hn : 1 ≤ n) :
    ⇑(h.tangentHomeomorph hn).symm = tangentMap J I h.symm :=
  (rfl)

/-- A tangent lift carries the velocity lift of a curve to the velocity lift of the image curve.
This is the bundled tangent-map form of the chain rule; if the curve is not differentiable, both
velocities are the junk value `0`. -/
theorem tangent_curveVelocityLift (h : M ≃ₘ⟮I, J⟯ N) {γ : 𝕜 → M} {t : 𝕜} :
    h.tangent (curveVelocityLift I γ t) = curveVelocityLift J (h ∘ γ) t := by
  rw [coe_tangent, curveVelocityLift_apply, curveVelocityLift_apply, curveVelocity_apply,
    curveVelocity_apply, h.mfderiv_diffeomorph_comp (by simp) γ t]
  rfl

end Diffeomorph

namespace TangentBundle

variable {G : Type*} [Group G] [MulAction G M] [ContMDiffConstSMul I ∞ G M]

/-- The **tangent lift of a smooth group action**: an element `g` acts on `TM` by the tangent lift
of the diffeomorphism `x ↦ g • x`, sending a tangent vector `v` at `x` to the tangent vector
`dg_x v` at `g • x` (`TangentBundle.smul_eq_tangentMap`). -/
instance instSMul : SMul G (TangentBundle I M) where
  smul g := (Diffeomorph.constSmul I ∞ g).tangent

/-- The tangent-lifted action of `g` is the tangent lift of the diffeomorphism `x ↦ g • x`. -/
theorem smul_def (g : G) (v : TangentBundle I M) :
    g • v = (Diffeomorph.constSmul I ∞ g).tangent v :=
  (rfl)

/-- The tangent-lifted action of `g` is the tangent map of `x ↦ g • x`. -/
theorem smul_eq_tangentMap (g : G) (v : TangentBundle I M) :
    g • v = tangentMap I I (fun x : M ↦ g • x) v := by
  rw [smul_def, Diffeomorph.coe_tangent, Diffeomorph.coe_constSmul]

/-- The tangent-lifted action covers the action on the base. -/
@[simp]
theorem proj_smul (g : G) (v : TangentBundle I M) : (g • v).proj = g • v.proj := by
  rw [smul_eq_tangentMap, tangentMap]

/-- The tangent-lifted action sends a tangent vector `v` at `x` to `dg_x v`. -/
@[simp]
theorem snd_smul (g : G) (v : TangentBundle I M) :
    (g • v).snd = mfderiv I I (fun x : M ↦ g • x) v.proj v.snd := by
  rw [smul_eq_tangentMap, tangentMap]

/-- The tangent lift of a smooth group action is a group action. -/
instance instMulAction : MulAction G (TangentBundle I M) where
  one_smul v := by
    rw [smul_def, Diffeomorph.constSmul_one, Diffeomorph.tangent_refl, Diffeomorph.coe_refl,
      id_eq]
  mul_smul g h v := by
    rw [smul_def, Diffeomorph.constSmul_mul, Diffeomorph.tangent_trans, Diffeomorph.coe_trans,
      Function.comp_apply, ← smul_def, ← smul_def]

/-- The tangent lift of a smooth group action is again an action by smooth maps. -/
instance instContMDiffConstSMul : ContMDiffConstSMul I.tangent ∞ G (TangentBundle I M) where
  contMDiff_const_smul g := (Diffeomorph.constSmul I ∞ g).tangent.contMDiff.congr (smul_def g)

/-- **The tangent lift of a smooth action is smooth.** If `G` acts smoothly on `M`, then
`(g, v) ↦ g • v` is smooth on `G × TM`: the tangent vector `g • v` is the image of `(0, v)` under
the tangent map of the action `G × M → M`. -/
instance instContMDiffSMul {EG HG : Type*} [NormedAddCommGroup EG] [NormedSpace 𝕜 EG]
    [TopologicalSpace HG] {IG : ModelWithCorners 𝕜 EG HG} [TopologicalSpace G]
    [ChartedSpace HG G] [IsManifold IG ∞ G] [ContMDiffSMul IG I ∞ G M] :
    ContMDiffSMul IG I.tangent ∞ G (TangentBundle I M) where
  contMDiff_smul :=
    (ContMDiffSMul.contMDiff_smul.contMDiff_tangentMap_family (f := fun (g : G) (x : M) ↦ g • x)
      (n := ∞) (m := ∞) (by simp)).congr fun p ↦ smul_eq_tangentMap p.1 p.2

end TangentBundle

namespace Diffeomorph

variable {G : Type*} [Group G] [MulAction G M] [ContMDiffConstSMul I ∞ G M]

/-- The tangent lift of the diffeomorphism `x ↦ g • x` is the diffeomorphism `v ↦ g • v` of the
tangent-lifted action. -/
@[simp]
theorem tangent_constSmul (g : G) :
    (constSmul I ∞ g : M ≃ₘ⟮I, I⟯ M).tangent = constSmul I.tangent ∞ g :=
  Diffeomorph.ext fun v ↦ (TangentBundle.smul_def g v).symm.trans (constSmul_apply g v).symm

end Diffeomorph

end

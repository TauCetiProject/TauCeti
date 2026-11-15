/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.LieAlgebroid.Tangent
public import TauCeti.Geometry.Manifold.MFDeriv.Curve
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import TauCeti.Geometry.Manifold.VectorBundle.Scalar

/-!
# `A`-paths of a Lie algebroid

An `A`-path of a Lie algebroid `A → M` with anchor `ρ` is a `C¹` path `a` in the total space of
`A`, parametrised by the unit interval `[0, 1]`, whose anchor is the velocity of its base path
`γ = π ∘ a`: `ρ(a(t)) = γ'(t)`. Velocities are taken within `[0, 1]`, so they are one-sided at the
endpoints. `A`-paths are the algebroid counterparts of paths in the source fibres of a Lie
groupoid, and their homotopy classes form the Weinstein groupoid of `A`.

The base path of an `A`-path is `C²` (`TauCeti.LieAlgebroid.IsAPath.contMDiffOn_proj`): it is
`C¹`, and its velocity `ρ(a(t))` is a `C¹` path in the tangent bundle. Thus the anchor carries
`A`-paths to `A`-paths of the tangent algebroid (`TauCeti.LieAlgebroid.IsAPath.anchor`). For the
tangent algebroid the anchor is the identity, so its `A`-paths are exactly the velocity lifts of
`C²` paths (`TauCeti.LieAlgebroid.isAPath_tangent_iff` and
`TauCeti.LieAlgebroid.isAPath_curveVelocityLiftWithin`).

## Main definitions

* `TauCeti.LieAlgebroid.IsAPath A a`: the path `a : ℝ → TotalSpace F V` is an `A`-path on
  `[0, 1]`.

## Main results

* `TauCeti.LieAlgebroid.isAPath_iff_eqOn`: a `C¹` path is an `A`-path exactly when the velocity
  lift of its base path is its anchor on `[0, 1]`; only values on `[0, 1]` matter
  (`TauCeti.LieAlgebroid.IsAPath.congr`).
* `TauCeti.LieAlgebroid.isAPath_zero`: the constant zero path at a point is an `A`-path.
* `TauCeti.LieAlgebroid.IsAPath.contMDiffOn_proj`: the base path of an `A`-path is `C²`.
* `TauCeti.LieAlgebroid.IsAPath.reparam`: reparametrising by a `C²` self-map `φ` of `[0, 1]`,
  `t ↦ φ'(t) • a(φ(t))`, gives an `A`-path; in particular the reversal `t ↦ -a(1 - t)` is one
  (`TauCeti.LieAlgebroid.IsAPath.reverse`).
* `TauCeti.LieAlgebroid.IsAPath.anchor`: the anchor of an `A`-path is an `A`-path of the tangent
  algebroid.
* `TauCeti.LieAlgebroid.isAPath_tangent_iff`: the `A`-paths of the tangent algebroid are the `C¹`
  paths of tangent vectors which agree on `[0, 1]` with the velocity lifts of their base paths.
* `TauCeti.LieAlgebroid.isAPath_curveVelocityLiftWithin`: the velocity lift of a `C²` path is an
  `A`-path of the tangent algebroid.

## References

* M. Crainic and R. L. Fernandes, *Integrability of Lie brackets*, Annals of Mathematics 157
  (2003), 575–620, Section 1.1.
* M. Crainic and R. L. Fernandes, *Lectures on integrability of Lie brackets*, Geom. Topol.
  Monogr. 17 (2011), 1–107, Section 2.
-/

public section

noncomputable section

open Bundle Set
open scoped ContDiff Manifold

namespace TauCeti

namespace LieAlgebroid

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {V : M → Type*}
  [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  (A : LieAlgebroid I F V)

/-- An **`A`-path** of a Lie algebroid `A`: a `C¹` path `a` in the total space of `A` on the unit
interval `[0, 1]` such that the anchor of `a t` is the velocity at `t` of the base path
`s ↦ (a s).proj`. The velocity is taken within `[0, 1]`, so it is one-sided at the endpoints.
Values of `a` outside `[0, 1]` are irrelevant. -/
structure IsAPath (a : ℝ → TotalSpace F V) : Prop where
  /-- The path is `C¹` on `[0, 1]`. -/
  contMDiffOn : ContMDiffOn 𝓘(ℝ) (I.prod 𝓘(ℝ, F)) 1 a (Icc 0 1)
  /-- The anchor of the path is the velocity of the base path. -/
  anchor_eq (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    A.anchor (a t).proj (a t).snd =
      Manifold.curveVelocityWithin I (fun s ↦ (a s).proj) (Icc 0 1) t

/-- The constant path at the zero vector over a point is an `A`-path: its base path is constant
and the anchor of zero vanishes. -/
theorem isAPath_zero (x : M) : A.IsAPath fun _ ↦ (⟨x, 0⟩ : TotalSpace F V) where
  contMDiffOn := contMDiffOn_const
  anchor_eq t _ := by
    rw [Manifold.curveVelocityWithin_const, map_zero]

namespace IsAPath

variable {A} {a : ℝ → TotalSpace F V}

/-- The base path of an `A`-path is `C¹` on `[0, 1]`. -/
theorem contMDiffOn_proj_one (ha : A.IsAPath a) :
    ContMDiffOn 𝓘(ℝ) I 1 (fun t ↦ (a t).proj) (Icc 0 1) :=
  (contMDiff_proj V).comp_contMDiffOn ha.contMDiffOn

/-- The anchor of an `A`-path is a `C¹` path in the tangent bundle on `[0, 1]`. -/
theorem contMDiffOn_anchor (ha : A.IsAPath a) :
    ContMDiffOn 𝓘(ℝ) (I.prod 𝓘(ℝ, E)) 1
      (fun t ↦ (⟨(a t).proj, A.anchor (a t).proj (a t).snd⟩ : TangentBundle I M)) (Icc 0 1) :=
  ContMDiffOn.clm_bundle_apply
    ((A.anchor.contMDiff.of_le (by simp)).comp_contMDiffOn ha.contMDiffOn_proj_one)
    ha.contMDiffOn

/-- On `[0, 1]` the velocity lift of the base path of an `A`-path is the anchor of the path. -/
theorem curveVelocityLiftWithin_eqOn (ha : A.IsAPath a) :
    EqOn (Manifold.curveVelocityLiftWithin I (fun t ↦ (a t).proj) (Icc 0 1))
      (fun t ↦ (⟨(a t).proj, A.anchor (a t).proj (a t).snd⟩ : TangentBundle I M)) (Icc 0 1) :=
  fun t ht ↦ by rw [Manifold.curveVelocityLiftWithin_apply, ← ha.anchor_eq t ht]

/-- **The base path of an `A`-path is `C²`** on `[0, 1]`: it is `C¹`, and its velocity, the anchor
of the path, is `C¹`. -/
theorem contMDiffOn_proj (ha : A.IsAPath a) :
    ContMDiffOn 𝓘(ℝ) I 2 (fun t ↦ (a t).proj) (Icc 0 1) := by
  have : IsManifold I ((1 : ℕ) + 1) M := .of_le (n := ∞) (by simp)
  exact (Manifold.contMDiffOn_succ_iff_contMDiffOn_curveVelocityLiftWithin (n := 1)
    (uniqueDiffOn_Icc zero_lt_one)).2
    ⟨ha.contMDiffOn_proj_one.mdifferentiableOn one_ne_zero,
      ha.contMDiffOn_anchor.congr ha.curveVelocityLiftWithin_eqOn⟩

end IsAPath

/-- A `C¹` path is an `A`-path exactly when, on `[0, 1]`, the velocity lift of its base path is
its anchor. -/
theorem isAPath_iff_eqOn {a : ℝ → TotalSpace F V} :
    A.IsAPath a ↔ ContMDiffOn 𝓘(ℝ) (I.prod 𝓘(ℝ, F)) 1 a (Icc 0 1) ∧
      EqOn (Manifold.curveVelocityLiftWithin I (fun t ↦ (a t).proj) (Icc 0 1))
        (fun t ↦ (⟨(a t).proj, A.anchor (a t).proj (a t).snd⟩ : TangentBundle I M)) (Icc 0 1) := by
  refine ⟨fun ha ↦ ⟨ha.contMDiffOn, ha.curveVelocityLiftWithin_eqOn⟩,
    fun ⟨h₁, h₂⟩ ↦ ⟨h₁, fun t ht ↦ ?_⟩⟩
  have h := h₂ ht
  rw [Manifold.curveVelocityLiftWithin_apply] at h
  exact (TotalSpace.mk_inj.1 h).symm

namespace IsAPath

variable {A} {a b : ℝ → TotalSpace F V}

/-- Being an `A`-path depends only on the values on `[0, 1]`. -/
theorem congr (ha : A.IsAPath a) (hab : EqOn a b (Icc 0 1)) : A.IsAPath b := by
  refine (isAPath_iff_eqOn A).2 ⟨ha.contMDiffOn.congr fun t ht ↦ (hab ht).symm, fun t ht ↦ ?_⟩
  -- The base paths agree on `[0, 1]`, so their velocity lifts within `[0, 1]` agree there.
  have hproj : (fun s ↦ (a s).proj) =ᶠ[nhdsWithin t (Icc 0 1)] fun s ↦ (b s).proj :=
    Filter.eventually_of_mem self_mem_nhdsWithin fun s hs ↦ congrArg TotalSpace.proj (hab hs)
  rw [← hproj.curveVelocityLiftWithin_eq (congrArg TotalSpace.proj (hab ht)),
    ha.curveVelocityLiftWithin_eqOn ht]
  exact congrArg (fun p : TotalSpace F V ↦
    (⟨p.proj, A.anchor p.proj p.snd⟩ : TangentBundle I M)) (hab ht)

/-- **Reparametrisation of `A`-paths.** If `φ` is `C²` on `[0, 1]` and maps `[0, 1]` into itself,
then `t ↦ φ'(t) • a(φ(t))` is an `A`-path, where `φ'` is the derivative within `[0, 1]`. -/
theorem reparam (ha : A.IsAPath a) {φ : ℝ → ℝ} (hφ : ContDiffOn ℝ 2 φ (Icc 0 1))
    (hmaps : MapsTo φ (Icc 0 1) (Icc 0 1)) :
    A.IsAPath fun t ↦
      (⟨(a (φ t)).proj, derivWithin φ (Icc 0 1) t • (a (φ t)).snd⟩ : TotalSpace F V) where
  contMDiffOn :=
    ((hφ.derivWithin (uniqueDiffOn_Icc zero_lt_one) (by norm_num)).contMDiffOn).smul_totalSpace
      (ha.contMDiffOn.comp (hφ.contMDiffOn.of_le (by norm_num)) hmaps)
  anchor_eq t ht := by
    have hvel := Manifold.curveVelocityWithin_comp (I := I) (γ := fun s ↦ (a s).proj)
      ((hφ.differentiableOn (by norm_num) t ht).hasDerivWithinAt) hmaps
      ((ha.contMDiffOn_proj_one (φ t) (hmaps ht)).mdifferentiableWithinAt one_ne_zero)
      (uniqueDiffOn_Icc zero_lt_one t ht)
    rw [map_smul, ha.anchor_eq (φ t) (hmaps ht)]
    -- The base path of the reparametrised path is `(fun s ↦ (a s).proj) ∘ φ`, by projecting from
    -- the anonymous constructor.
    exact hvel.symm

/-- **Reversal of `A`-paths.** The path `t ↦ -a(1 - t)` is an `A`-path. -/
theorem reverse (ha : A.IsAPath a) :
    A.IsAPath fun t ↦ (⟨(a (1 - t)).proj, -(a (1 - t)).snd⟩ : TotalSpace F V) := by
  have hφ : ContDiffOn ℝ 2 (fun t : ℝ ↦ 1 - t) (Icc 0 1) :=
    (contDiff_const.sub contDiff_id).contDiffOn
  have hmaps : MapsTo (fun t : ℝ ↦ 1 - t) (Icc 0 1) (Icc 0 1) :=
    fun t ht ↦ ⟨by linarith [ht.2], by linarith [ht.1]⟩
  refine (ha.reparam hφ hmaps).congr fun t ht ↦ ?_
  have hderiv : derivWithin (fun t : ℝ ↦ 1 - t) (Icc 0 1) t = -1 :=
    ((hasDerivAt_id' t).const_sub 1).hasDerivWithinAt.derivWithin
      (uniqueDiffOn_Icc zero_lt_one t ht)
  simp only [hderiv, neg_one_smul]

end IsAPath

section Tangent

variable [FiniteDimensional ℝ E]

/-- The `A`-paths of the tangent algebroid are the `C¹` paths of tangent vectors which agree on
`[0, 1]` with the velocity lifts of their base paths. -/
theorem isAPath_tangent_iff {a : ℝ → TangentBundle I M} :
    (tangent I M).IsAPath a ↔
      ContMDiffOn 𝓘(ℝ) (I.prod 𝓘(ℝ, E)) 1 a (Icc 0 1) ∧
        EqOn a (Manifold.curveVelocityLiftWithin I (fun t ↦ (a t).proj) (Icc 0 1)) (Icc 0 1) := by
  refine ⟨fun ha ↦ ⟨ha.contMDiffOn, fun t ht ↦ ?_⟩,
    fun ⟨h₁, h₂⟩ ↦ ⟨h₁, fun t ht ↦ ?_⟩⟩
  · rw [Manifold.curveVelocityLiftWithin_apply, ← ha.anchor_eq t ht, tangent_anchor_apply]
  · rw [tangent_anchor_apply]
    exact (congrArg TotalSpace.snd (h₂ ht)).trans (Manifold.curveVelocityLiftWithin_snd _ _ _)

/-- **The velocity lift of a `C²` path is an `A`-path of the tangent algebroid.** The velocity is
taken within `[0, 1]`. -/
theorem isAPath_curveVelocityLiftWithin {γ : ℝ → M} (hγ : ContMDiffOn 𝓘(ℝ) I 2 γ (Icc 0 1)) :
    (tangent I M).IsAPath (Manifold.curveVelocityLiftWithin I γ (Icc 0 1)) :=
  isAPath_tangent_iff.2 ⟨hγ.contMDiffOn_curveVelocityLiftWithin (by norm_num)
    (uniqueDiffOn_Icc zero_lt_one).uniqueMDiffOn,
    fun _ _ ↦ by simp only [Manifold.curveVelocityLiftWithin_proj]⟩

/-- **The anchor carries `A`-paths to `A`-paths of the tangent algebroid**: the anchor of an
`A`-path is the velocity lift of its base path. -/
theorem IsAPath.anchor {A : LieAlgebroid I F V} {a : ℝ → TotalSpace F V} (ha : A.IsAPath a) :
    (tangent I M).IsAPath fun t ↦
      (⟨(a t).proj, A.anchor (a t).proj (a t).snd⟩ : TangentBundle I M) :=
  isAPath_tangent_iff.2
    ⟨ha.contMDiffOn_anchor, fun _ ht ↦ (ha.curveVelocityLiftWithin_eqOn ht).symm⟩

end Tangent

end LieAlgebroid

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Pullback
public import TauCeti.Geometry.Manifold.VectorBundle.NondegenerateMetric.Signature
import TauCeti.Geometry.Manifold.VectorBundle.Pullback

/-!
# Smooth families of nondegenerate metrics

Let `P` be a parameter manifold. A smooth family of nondegenerate metrics on `M` parametrized by
`P` assigns to each `(p, x) : P × M` a symmetric nondegenerate bilinear form on `T_x M`, smoothly
in `(p, x)` jointly. This file realizes such a family as a native smooth section over `P × M` of
the pullback, along the projection `P × M → M`, of the tangent bilinear-form bundle of `M`.

Freezing the parameter gives a smooth nondegenerate metric on `M` for every `p : P`. Every single
metric is a constant family, and a family can be restricted along a smooth map of parameter
manifolds, for example along a smooth curve `t ↦ p t`. The signature of the frozen metrics is
locally constant jointly in the parameter and the point, so it is fixed on each connected
component of `P × M`.

These families are the carrier for the parameter dependence of the Levi-Civita connection of a
varying, possibly indefinite, metric and for its first variation.

## Main definitions and results

* `TauCeti.Manifold.ContMDiffNondegenerateMetricFamily`: a smooth family of symmetric
  nondegenerate tangent bilinear forms on `M`, parametrized by `P`.
* `TauCeti.Manifold.ContMDiffNondegenerateMetricFamily.contMDiff`: joint smoothness of the
  family as a map into the tangent bilinear-form bundle of `M`.
* `TauCeti.Manifold.ContMDiffNondegenerateMetricFamily.ofContMDiff`: the converse construction.
* `TauCeti.Manifold.ContMDiffNondegenerateMetricFamily.metric`: the metric at a fixed parameter.
* `TauCeti.Manifold.ContMDiffNondegenerateMetricFamily.const` and
  `TauCeti.Manifold.ContMDiffNondegenerateMetricFamily.comp`: constant families and restriction
  along a smooth parameter map.
* `TauCeti.Manifold.ContMDiffNondegenerateMetricFamily.isLocallyConstant_signature_metric`: the
  signature is locally constant on `P × M`.

## References

* B. O'Neill, *Semi-Riemannian Geometry*, Academic Press, 1983, Chapter 3.
-/

public section

noncomputable section

open Bundle
open scoped ContDiff Manifold

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {EP : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP]
  {HP : Type*} [TopologicalSpace HP] {IP : ModelWithCorners ℝ EP HP}
  {P : Type*} [TopologicalSpace P] [ChartedSpace HP P]

variable (I M IP P) in
/-- A smooth family, parametrized by `P`, of symmetric nondegenerate real bilinear forms on the
tangent bundle of `M`.

The family is a native smooth section over `P × M` of the pullback of the tangent
bilinear-form bundle of `M` along the projection `P × M → M`; its value at `(p, x)` is a bilinear
form on `T_x M`. As for a single metric, no positivity or signature is imposed. -/
structure ContMDiffNondegenerateMetricFamily where
  /-- The smooth section of the pulled-back bundle of continuous bilinear forms. -/
  toContMDiffSection :
    Cₛ^∞⟮IP.prod I; E →L[ℝ] E →L[ℝ] ℝ,
      ((ContMDiffMap.snd : C^∞⟮IP.prod I, P × M; I, M⟯) : P × M → M) *ᵖ
        fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ⟯
  /-- The bilinear form at every parameter and point is symmetric. -/
  symm (q : P × M) :
    ContinuousLinearMap.toBilinForm
      (toContMDiffSection q : TangentSpace I q.2 →L[ℝ] TangentSpace I q.2 →L[ℝ] ℝ) |>.IsSymm
  /-- The bilinear form at every parameter and point is nondegenerate. -/
  nondegenerate (q : P × M) :
    ContinuousLinearMap.toBilinForm
      (toContMDiffSection q : TangentSpace I q.2 →L[ℝ] TangentSpace I q.2 →L[ℝ] ℝ)
      |>.Nondegenerate

namespace ContMDiffNondegenerateMetricFamily

/-- The bilinear form of a smooth nondegenerate metric family at a parameter and a point. -/
@[coe]
def toFun (g : ContMDiffNondegenerateMetricFamily I M IP P) (q : P × M) :
    TangentSpace I q.2 →L[ℝ] TangentSpace I q.2 →L[ℝ] ℝ :=
  g.toContMDiffSection q

instance : CoeFun (ContMDiffNondegenerateMetricFamily I M IP P) fun _ ↦
    (q : P × M) → TangentSpace I q.2 →L[ℝ] TangentSpace I q.2 →L[ℝ] ℝ where
  coe := toFun

variable (g : ContMDiffNondegenerateMetricFamily I M IP P)

/-- Evaluation of a smooth nondegenerate metric family is symmetric in its tangent arguments. -/
theorem apply_comm (q : P × M) (v w : TangentSpace I q.2) : g q v w = g q w v :=
  (g.symm q).eq v w

/-- Smooth nondegenerate metric families are equal when all their fibrewise pairings agree. -/
@[ext]
theorem ext {g h : ContMDiffNondegenerateMetricFamily I M IP P}
    (heq : ∀ q v w, g q v w = h q v w) : g = h := by
  cases g with
  | mk gs gsymm gnond =>
    cases h with
    | mk hs hsymm hnond =>
      congr 1
      apply ContMDiffSection.ext
      intro q
      exact ContinuousLinearMap.ext fun v ↦ ContinuousLinearMap.ext fun w ↦ heq q v w

/-- A smooth nondegenerate metric family is jointly smooth in the parameter and the point, as a
map into the tangent bilinear-form bundle of `M`. -/
theorem contMDiff :
    ContMDiff (IP.prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun q : P × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) q.2 (g q)) :=
  ((Pullback.contMDiff_iff (ContMDiffMap.snd : C^∞⟮IP.prod I, P × M; I, M⟯)
    contMDiff_snd).mp g.toContMDiffSection.contMDiff).2

/-- A jointly smooth field of symmetric nondegenerate tangent bilinear forms on `M`,
parametrized by `P`, as a smooth nondegenerate metric family. -/
def ofContMDiff (φ : (q : P × M) → TangentSpace I q.2 →L[ℝ] TangentSpace I q.2 →L[ℝ] ℝ)
    (hφ : ContMDiff (IP.prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun q : P × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) q.2 (φ q)))
    (hsymm : ∀ q, (φ q).toBilinForm.IsSymm) (hnd : ∀ q, (φ q).toBilinForm.Nondegenerate) :
    ContMDiffNondegenerateMetricFamily I M IP P where
  toContMDiffSection :=
    ⟨φ, (Pullback.contMDiff_iff (ContMDiffMap.snd : C^∞⟮IP.prod I, P × M; I, M⟯)
      contMDiff_snd).mpr ⟨contMDiff_id, hφ⟩⟩
  symm := hsymm
  nondegenerate := hnd

/-- The family built from a jointly smooth field of forms evaluates to that field. -/
@[simp]
theorem ofContMDiff_apply
    (φ : (q : P × M) → TangentSpace I q.2 →L[ℝ] TangentSpace I q.2 →L[ℝ] ℝ)
    (hφ : ContMDiff (IP.prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun q : P × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) q.2 (φ q)))
    (hsymm : ∀ q, (φ q).toBilinForm.IsSymm) (hnd : ∀ q, (φ q).toBilinForm.Nondegenerate)
    (q : P × M) :
    ofContMDiff φ hφ hsymm hnd q = φ q :=
  (rfl)

/-- The smooth nondegenerate metric on `M` obtained by freezing the parameter at `p`. -/
def metric (p : P) : ContMDiffNondegenerateMetric (I := I) (M := M) where
  toContMDiffSection :=
    ⟨fun x ↦ g (p, x), g.contMDiff.comp (contMDiff_const.prodMk contMDiff_id)⟩
  symm x := g.symm (p, x)
  nondegenerate x := g.nondegenerate (p, x)

/-- The metric at a fixed parameter evaluates as the family. -/
@[simp]
theorem metric_apply (p : P) (x : M) : g.metric p x = g (p, x) :=
  (rfl)

/-- A smooth nondegenerate metric family is determined by its metrics at fixed parameters. -/
theorem metric_injective :
    Function.Injective (metric : ContMDiffNondegenerateMetricFamily I M IP P → P → _) := by
  intro g h hgh
  ext q v w
  simpa using congr($(congrFun hgh q.1) q.2 v w)

/-- The constant family with value a smooth nondegenerate metric. -/
def const (g₀ : ContMDiffNondegenerateMetric (I := I) (M := M)) :
    ContMDiffNondegenerateMetricFamily I M IP P :=
  ofContMDiff (fun q ↦ g₀ q.2) (g₀.contMDiff.comp contMDiff_snd) (fun q ↦ g₀.symm q.2)
    (fun q ↦ g₀.nondegenerate q.2)

/-- The constant family takes the value of its metric at every parameter. -/
@[simp]
theorem const_apply (g₀ : ContMDiffNondegenerateMetric (I := I) (M := M)) (q : P × M) :
    const (IP := IP) (P := P) g₀ q = g₀ q.2 :=
  (rfl)

/-- Freezing the parameter of a constant family recovers its metric. -/
@[simp]
theorem metric_const (g₀ : ContMDiffNondegenerateMetric (I := I) (M := M)) (p : P) :
    (const (IP := IP) g₀).metric p = g₀ := by
  ext x v w
  simp

section Comp

variable {EP' : Type*} [NormedAddCommGroup EP'] [NormedSpace ℝ EP']
  {HP' : Type*} [TopologicalSpace HP'] {IP' : ModelWithCorners ℝ EP' HP'}
  {P' : Type*} [TopologicalSpace P'] [ChartedSpace HP' P']

/-- The restriction of a smooth nondegenerate metric family along a smooth map of parameter
manifolds `c : P' → P`; its value at `(p', x)` is the value of the family at `(c p', x)`. -/
def comp (c : C^∞⟮IP', P'; IP, P⟯) : ContMDiffNondegenerateMetricFamily I M IP' P' :=
  ofContMDiff (fun q ↦ g (c q.1, q.2))
    (g.contMDiff.comp ((c.contMDiff.comp contMDiff_fst).prodMk contMDiff_snd))
    (fun q ↦ g.symm (c q.1, q.2)) (fun q ↦ g.nondegenerate (c q.1, q.2))

/-- The restriction along a parameter map evaluates the family at the image parameter. -/
@[simp]
theorem comp_apply (c : C^∞⟮IP', P'; IP, P⟯) (q : P' × M) : g.comp c q = g (c q.1, q.2) :=
  (rfl)

/-- Freezing the parameter of a restricted family freezes the original family at the image
parameter. -/
@[simp]
theorem metric_comp (c : C^∞⟮IP', P'; IP, P⟯) (p' : P') :
    (g.comp c).metric p' = g.metric (c p') := by
  ext x v w
  simp

/-- Restricting a family along the identity parameter map gives the family back. -/
@[simp]
theorem comp_id : g.comp (ContMDiffMap.id : C^∞⟮IP, P; IP, P⟯) = g := by
  ext q v w
  rw [comp_apply]
  simp [ContMDiffMap.id]

/-- Restricting a family along two parameter maps in turn is restricting along their
composite. -/
theorem comp_comp {EP'' : Type*} [NormedAddCommGroup EP''] [NormedSpace ℝ EP'']
    {HP'' : Type*} [TopologicalSpace HP''] {IP'' : ModelWithCorners ℝ EP'' HP''}
    {P'' : Type*} [TopologicalSpace P''] [ChartedSpace HP'' P'']
    (c : C^∞⟮IP', P'; IP, P⟯) (c' : C^∞⟮IP'', P''; IP', P'⟯) :
    (g.comp c).comp c' = g.comp (c.comp c') := by
  ext q v w
  simp

/-- Restricting a constant family along a parameter map gives the constant family. -/
@[simp]
theorem const_comp (g₀ : ContMDiffNondegenerateMetric (I := I) (M := M))
    (c : C^∞⟮IP', P'; IP, P⟯) :
    (const (IP := IP) (P := P) g₀).comp c = const g₀ := by
  ext q v w
  simp

end Comp

section Signature

variable [FiniteDimensional ℝ E]

/-- The signature of the metrics of a smooth nondegenerate family is locally constant jointly in
the parameter and the point. -/
theorem isLocallyConstant_signature_metric :
    IsLocallyConstant fun q : P × M ↦ (g.metric q.1).signature q.2 := by
  have hsig : (fun q : P × M ↦ (g.metric q.1).signature q.2) = fun q ↦
      (sigPos (g q).toBilinForm.toQuadraticMap, sigNeg (g q).toBilinForm.toQuadraticMap) := by
    funext q
    ext <;> simp
  rw [hsig]
  exact isLocallyConstant_sigPos_sigNeg_of_continuous
    (q := fun q : P × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) q.2 (g q))
    g.contMDiff.continuous
    (fun q ↦ g.symm q) (fun q ↦ g.nondegenerate q)

/-- A smooth nondegenerate metric family has one fixed signature on each connected component of
`P × M`. -/
theorem signature_metric_eq_of_mem_connectedComponent {q q' : P × M}
    (hq' : q' ∈ connectedComponent q) :
    (g.metric q'.1).signature q'.2 = (g.metric q.1).signature q.2 :=
  g.isLocallyConstant_signature_metric.apply_eq_of_isPreconnected
    isPreconnected_connectedComponent hq' mem_connectedComponent

/-- Over a preconnected parameter manifold and a preconnected manifold, a smooth nondegenerate
metric family has one fixed signature. -/
theorem signature_metric_eq [PreconnectedSpace P] [PreconnectedSpace M] (p p' : P) (x x' : M) :
    (g.metric p).signature x = (g.metric p').signature x' :=
  g.isLocallyConstant_signature_metric.apply_eq_of_preconnectedSpace (p, x) (p', x')

end Signature

end ContMDiffNondegenerateMetricFamily

end TauCeti.Manifold

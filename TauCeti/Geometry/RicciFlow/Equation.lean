/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Ricci
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Regularity

/-!
# The native Ricci-flow equation

`TauCeti.IsRicciFlowAt r t` is the metric equation `∂ₜr = -2 Ric(r)` at one time, with the
canonical Levi-Civita connection of that time slice. `TauCeti.IsRicciFlowOn r s` requires this
equation at every time in `s`; it imposes no condition outside `s`.
-/

public noncomputable section

open Bundle CovariantDerivative Set
open scoped ContDiff Manifold RealInnerProductSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  (r : ℝ → ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))

/-- A family satisfies the Ricci-flow equation at `t` when its metric derivative is
minus twice the Ricci tensor of the canonical Levi-Civita connection of `r t`. -/
def IsRicciFlowAt (t : ℝ) : Prop :=
  ∀ (x : M) (u v : TangentSpace I x),
    HasDerivAt (fun s ↦ (r s).inner x u v)
      (-2 * (let : RiemannianBundle (TangentSpace I : M → Type _) :=
        ⟨(r t).toRiemannianMetric⟩;
        (leviCivitaConnection I M).ricciTensor x u v)) t

/-- The pointwise metric derivative criterion for the Ricci-flow equation. -/
theorem isRicciFlowAt_iff {t : ℝ} :
    IsRicciFlowAt r t ↔ ∀ (x : M) (u v : TangentSpace I x),
      HasDerivAt (fun s ↦ (r s).inner x u v)
        (-2 * (let : RiemannianBundle (TangentSpace I : M → Type _) :=
          ⟨(r t).toRiemannianMetric⟩;
          (leviCivitaConnection I M).ricciTensor x u v)) t :=
  Iff.rfl

/-- The metric derivative of a Ricci flow at a fixed time and tangent pair. -/
theorem IsRicciFlowAt.hasDerivAt {t : ℝ} (h : IsRicciFlowAt r t)
    (x : M) (u v : TangentSpace I x) :
    HasDerivAt (fun s ↦ (r s).inner x u v)
      (-2 * (let : RiemannianBundle (TangentSpace I : M → Type _) :=
        ⟨(r t).toRiemannianMetric⟩;
        (leviCivitaConnection I M).ricciTensor x u v)) t :=
  (isRicciFlowAt_iff r).mp h x u v

/-- A metric family is a Ricci flow on a time set if it satisfies the equation at every
member of that set. -/
def IsRicciFlowOn (s : Set ℝ) : Prop := ∀ t ∈ s, IsRicciFlowAt r t

/-- The timewise criterion for a metric family to be a Ricci flow on a set. -/
theorem isRicciFlowOn_iff {s : Set ℝ} :
    IsRicciFlowOn r s ↔ ∀ t ∈ s, IsRicciFlowAt r t :=
  Iff.rfl

/-- A Ricci flow on a set satisfies the equation at each member of that set. -/
theorem IsRicciFlowOn.at {s : Set ℝ} (h : IsRicciFlowOn r s) {t : ℝ} (ht : t ∈ s) :
    IsRicciFlowAt r t :=
  (isRicciFlowOn_iff r).mp h t ht

/-- Restricting the time set preserves the Ricci-flow equation. -/
theorem IsRicciFlowOn.mono {s u : Set ℝ} (h : IsRicciFlowOn r s) (hu : u ⊆ s) :
    IsRicciFlowOn r u :=
  (isRicciFlowOn_iff r).mpr fun _ ht ↦ h.at r (hu ht)

end TauCeti

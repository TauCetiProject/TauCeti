/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Nondegenerate.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Regularity
public import TauCeti.Geometry.Manifold.VectorBundle.NondegenerateMetric.Musical

/-!
# Regularity of Levi-Civita connections of nondegenerate metrics

A Levi-Civita connection of a smooth symmetric nondegenerate metric is smooth, regardless of
the signature of the metric. More precisely, on an open set it sends a `C^(n+1)` vector field
to a `C^n` section of `Hom(TM, TM)`, for every `n ≤ ∞`.

The Koszul formula gives regularity of the contractions of the connection with the metric.
Testing those covectors on a chart-local frame proves their regularity as bundle sections;
the smooth sharp musical map then recovers the vectors themselves. This supplies the native
`ContMDiffCovariantDerivative` interface without imposing positivity or choosing an auxiliary
Riemannian metric. The result applies to any Levi-Civita connection and does not constrain its
junk values on vector fields that are not differentiable.

## Main results

In the namespace `TauCeti.Manifold.ContMDiffNondegenerateMetric`:

* `IsLeviCivitaConnection.contMDiffOn`: regularity of the hom-bundle section `∇Y`.
* `IsLeviCivitaConnection.contMDiffCovariantDerivative`: smoothness in the native class form.

## References

* B. O'Neill, *Semi-Riemannian Geometry with Applications to Relativity*, Academic Press,
  1983, Chapter 3, Theorem 11.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176, 2018,
  Theorem 5.10.
* `TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Regularity`:
  the local-frame argument for the positive metric, adapted here using the sharp map in
  place of the Riesz dual.
-/

public section

noncomputable section

open Bundle CovariantDerivative FiberBundle Module Riemannian.Tensor Set
open scoped ContDiff Manifold Topology

namespace TauCeti.Manifold.ContMDiffNondegenerateMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {g : ContMDiffNondegenerateMetric (I := I) (M := M)}
  {cov : CovariantDerivative I E (fun x : M ↦ TangentSpace I x)}
  {n : ℕ∞ω} {u : Set M} {X Y : Π x : M, TangentSpace I x}

/-- A Levi-Civita connection of a smooth nondegenerate metric differentiates vector fields
with one derivative lost: `∇_X Y` is `C^n` when `X` and `Y` are `C^(n+1)` on an open set. -/
private theorem IsLeviCivitaConnection.contMDiffOn_apply (h : g.IsLeviCivitaConnection cov)
    (hn : n ≤ ∞) (hu : IsOpen u)
    (hX : ContMDiffOn I (I.prod 𝓘(ℝ, E)) (n + 1) (fun y ↦ TotalSpace.mk' E y (X y)) u)
    (hY : ContMDiffOn I (I.prod 𝓘(ℝ, E)) (n + 1) (fun y ↦ TotalSpace.mk' E y (Y y)) u) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E)) n
      (fun y ↦ TotalSpace.mk' E y (cov Y y (X y))) u := by
  have hn₁ : n + 1 ≤ ∞ := by simpa using hn
  have hn₂ : n + 2 ≤ ∞ := by simpa using hn
  have : IsManifold I (n + 1 + 1) M :=
    IsManifold.of_le (n := ∞) (by simpa only [add_assoc, one_add_one_eq_two] using hn₂)
  have : IsManifold I (n + 1) M := IsManifold.of_le (n := ∞) (by simpa using hn)
  have : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  intro x hx
  let s := u ∩ (chartAt H x).source
  have hs : IsOpen s := hu.inter (chartAt H x).open_source
  have hxs : x ∈ s := ⟨hx, mem_chart_source H x⟩
  have hframe (j : Fin (finrank ℝ E)) : ContMDiffOn I (I.prod 𝓘(ℝ, E)) (n + 1)
      (fun y ↦ TotalSpace.mk' E y (chartLocalFrame (I := I) x j y)) s :=
    (contMDiffOn_chartLocalFrame (I := I) (n := n + 1) x j).mono
      (by rw [TangentBundle.trivializationAt_baseSet]; exact inter_subset_right)
  -- First recover the covector `g(∇_X Y, ·)` from its smooth evaluations on a frame.
  have heval (j : Fin (finrank ℝ E)) : ContMDiffOn I 𝓘(ℝ) n
      (fun y ↦ g y (cov Y y (X y)) (chartLocalFrame (I := I) x j y)) s := by
    have hK := (contMDiffOn_const (c := (2 : ℝ)⁻¹)).mul
      (contMDiffOn_koszulBilinear hs hn₂ (g.contMDiff.of_le hn₁).contMDiffOn
        (hX.mono inter_subset_left) (hY.mono inter_subset_left) (hframe j))
    refine hK.congr fun y hy ↦ ?_
    have hXd := ((hX.mono inter_subset_left).mdifferentiableOn (by simp)).mdifferentiableAt
      (hs.mem_nhds hy)
    have hYd := ((hY.mono inter_subset_left).mdifferentiableOn (by simp)).mdifferentiableAt
      (hs.mem_nhds hy)
    have hZd := ((hframe j).mdifferentiableOn (by simp)).mdifferentiableAt (hs.mem_nhds hy)
    have hkos := h.two_apply_eq_koszul hXd hYd hZd
    have hkeq : g.koszul X Y (chartLocalFrame (I := I) x j) y =
        koszulBilinear I g X Y (chartLocalFrame (I := I) x j) y := by
      simp only [koszul_apply, koszulBilinear_apply]
    rw [hkeq] at hkos
    simp only [Pi.mul_apply]
    linarith
  have hflat : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) n
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] ℝ)
        (E := fun y : M ↦ TangentSpace I y →L[ℝ] ℝ) y (g y (cov Y y (X y)))) s := by
    apply contMDiffOn_hom_of_localFrame (I := I)
      (e := trivializationAt E (TangentSpace I) x)
      (e' := trivializationAt ℝ (Trivial M ℝ) x) (finBasis ℝ E)
      (by
        intro y hy
        exact ⟨by simpa only [TangentBundle.trivializationAt_baseSet] using hy.2,
          by simp [Trivial.eq_trivialization]⟩)
    intro j y hy
    simpa [contMDiffWithinAt_section, Trivial.eq_trivialization, ← chartLocalFrame_def] using
      heval j y hy
  -- The inverse musical map is smooth for a nondegenerate metric of any signature.
  have hsharp : ContMDiffOn I (I.prod 𝓘(ℝ, E)) n
      (fun y ↦ TotalSpace.mk' E y (cov Y y (X y))) s := by
    refine (g.contMDiffOn_sharp hn hflat).congr fun y _ ↦ ?_
    simp only [← g.inverse_apply, (g.isInvertible y).inverse_apply_self]
  exact (hsharp.contMDiffAt (hs.mem_nhds hxs)).contMDiffWithinAt

/-- On an open set, a Levi-Civita connection of a smooth nondegenerate metric carries a
`C^(n+1)` vector field to a `C^n` section of `Hom(TM, TM)`, for `n ≤ ∞`. -/
theorem IsLeviCivitaConnection.contMDiffOn (h : g.IsLeviCivitaConnection cov)
    (hn : n ≤ ∞) (hu : IsOpen u)
    (hY : ContMDiffOn I (I.prod 𝓘(ℝ, E)) (n + 1) (fun y ↦ TotalSpace.mk' E y (Y y)) u) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun y : M ↦ TangentSpace I y →L[ℝ] TangentSpace I y) y (cov Y y)) u := by
  have hn₂ : n + 1 + 1 ≤ ∞ := by simpa using hn
  have : IsManifold I (n + 1 + 1) M := IsManifold.of_le (n := ∞) hn₂
  have : IsManifold I (n + 1) M := IsManifold.of_le (n := ∞) (by simpa using hn)
  have : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  intro x hx
  let s := u ∩ (chartAt H x).source
  have hs : IsOpen s := hu.inter (chartAt H x).open_source
  have hdir (j : Fin (finrank ℝ E)) := h.contMDiffOn_apply hn hs
    ((contMDiffOn_chartLocalFrame (I := I) (n := n + 1) x j).mono
      (by rw [TangentBundle.trivializationAt_baseSet]; exact inter_subset_right))
    (hY.mono inter_subset_left)
  have hhom := contMDiffOn_hom_of_localFrame (I := I)
    (e := trivializationAt E (TangentSpace I) x)
    (e' := trivializationAt E (TangentSpace I) x) (finBasis ℝ E)
    (u := s) (by rw [TangentBundle.trivializationAt_baseSet, inter_self]; exact inter_subset_right)
    (A := fun y ↦ cov Y y) (fun j ↦ by simpa only [← chartLocalFrame_def] using hdir j)
  exact (hhom.contMDiffAt (hs.mem_nhds ⟨hx, mem_chart_source H x⟩)).contMDiffWithinAt

/-- A Levi-Civita connection of a smooth nondegenerate metric is of class `C^n` for every
`n ≤ ∞`, in the native covariant-derivative class. In particular it is smooth. -/
theorem IsLeviCivitaConnection.contMDiffCovariantDerivative
    (h : g.IsLeviCivitaConnection cov) (hn : n ≤ ∞) : ContMDiffCovariantDerivative cov n where
  contMDiff := ⟨fun hY ↦ h.contMDiffOn hn isOpen_univ hY⟩

end TauCeti.Manifold.ContMDiffNondegenerateMetric

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Nondegenerate.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Regularity
public import TauCeti.Geometry.Manifold.VectorBundle.NondegenerateMetric.Family
public import TauCeti.Geometry.Manifold.VectorBundle.NondegenerateMetric.Musical

/-!
# Regularity of Levi-Civita connections of nondegenerate metrics

A Levi-Civita connection of a smooth symmetric nondegenerate metric is smooth, regardless of
the signature of the metric. More precisely, on an open set it sends a `C^(n+1)` vector field
to a `C^n` section of `Hom(TM, TM)`, for every `n ≤ ∞`.

This holds jointly in parameters. Let `g_p` be a family of smooth nondegenerate metrics,
parametrized by a manifold `P` and jointly `C^(n+1)` in `(p, x)`, and let `∇ᵖ` be a Levi-Civita
connection of `g_p` for each `p`. For a vector field `Y` which is `C^(n+1)` on an open set `u`,
the map `(p, x) ↦ ∇ᵖY(x)` into `Hom(TM, TM)` is `C^n` on `P × u`. Applied to the vector fields of
a local frame, this is joint regularity of the connection coefficients in `(p, x)`; for a smooth
nondegenerate metric family the connections are jointly smooth. A single metric is the constant
family.

The Koszul formula gives regularity of the contractions of the connection with the metric,
jointly in the parameter by `TauCeti.Manifold.contMDiffOn_koszulBilinear_family`.
Testing those covectors on a chart-local frame proves their regularity as bundle sections over
`P × M`; the fibrewise inverses of the metrics, which are jointly smooth, then recover the vectors
themselves. This supplies the native `ContMDiffCovariantDerivative` interface without imposing
positivity or choosing an auxiliary Riemannian metric. The result applies to any Levi-Civita
connection and does not constrain its junk values on vector fields that are not differentiable.

## Main results

In the namespace `TauCeti.Manifold`:

* `contMDiffOn_covariantDerivative_of_isLeviCivitaConnection`: joint regularity of
  `(p, x) ↦ ∇ᵖY(x)` for a family of metrics.

In the namespace `TauCeti.Manifold.ContMDiffNondegenerateMetric`:

* `IsLeviCivitaConnection.contMDiffOn`: regularity of the hom-bundle section `∇Y`.
* `IsLeviCivitaConnection.contMDiffCovariantDerivative`: smoothness in the native class form.

In the namespace `TauCeti.Manifold.ContMDiffNondegenerateMetricFamily`:

* `contMDiffOn_covariantDerivative_of_isLeviCivitaConnection` and
  `contMDiff_covariantDerivative_of_isLeviCivitaConnection`: joint regularity of the Levi-Civita
  connections of a smooth nondegenerate metric family.

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

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {n : ℕ∞ω} {u : Set M} {X Y : Π x : M, TangentSpace I x}

section Family

variable {EP : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP]
  {HP : Type*} [TopologicalSpace HP] {IP : ModelWithCorners ℝ EP HP}
  {P : Type*} [TopologicalSpace P] [ChartedSpace HP P] [IsManifold IP 1 P]
  {g : P → ContMDiffNondegenerateMetric (I := I) (M := M)}
  {cov : P → CovariantDerivative I E (fun x : M ↦ TangentSpace I x)}

/-- Levi-Civita connections of a family of nondegenerate metrics, jointly `C^(n+1)` in the
parameter and the point, differentiate vector fields jointly in the parameter and the point with
one derivative lost: `(p, x) ↦ ∇ᵖ_X Y(x)` is `C^n` on `P × u` when `X` and `Y` are `C^(n+1)` on
the open set `u`. -/
private theorem contMDiffOn_covariantDerivative_apply_of_isLeviCivitaConnection
    (hcov : ∀ p, (g p).IsLeviCivitaConnection (cov p)) (hn : n ≤ ∞) (hu : IsOpen u)
    (hg : ContMDiffOn (IP.prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) (n + 1)
      (fun q : P × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y : M ↦ TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) q.2 (g q.1 q.2))
      (univ ×ˢ u))
    (hX : ContMDiffOn I (I.prod 𝓘(ℝ, E)) (n + 1) (fun y ↦ TotalSpace.mk' E y (X y)) u)
    (hY : ContMDiffOn I (I.prod 𝓘(ℝ, E)) (n + 1) (fun y ↦ TotalSpace.mk' E y (Y y)) u) :
    ContMDiffOn (IP.prod I) (I.prod 𝓘(ℝ, E)) n
      (fun q : P × M ↦ TotalSpace.mk' E q.2 (cov q.1 Y q.2 (X q.2))) (univ ×ˢ u) := by
  have hn₂ : n + 2 ≤ ∞ := by simpa using hn
  have : IsManifold I (n + 1 + 1) M :=
    IsManifold.of_le (n := ∞) (by simpa only [add_assoc, one_add_one_eq_two] using hn₂)
  have : IsManifold I (n + 1) M := IsManifold.of_le (n := ∞) (by simpa using hn)
  have : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  rintro ⟨p, x⟩ ⟨-, hx⟩
  let s := u ∩ (chartAt H x).source
  have hs : IsOpen s := hu.inter (chartAt H x).open_source
  have hW : IsOpen (univ ×ˢ s : Set (P × M)) := isOpen_univ.prod hs
  have hsW : (univ ×ˢ s : Set (P × M)) ⊆ univ ×ˢ u := prod_mono subset_rfl inter_subset_left
  have hxW : (p, x) ∈ univ ×ˢ s := ⟨mem_univ p, hx, mem_chart_source H x⟩
  have hframe (j : Fin (finrank ℝ E)) : ContMDiffOn I (I.prod 𝓘(ℝ, E)) (n + 1)
      (fun y ↦ TotalSpace.mk' E y (chartLocalFrame (I := I) x j y)) s :=
    (contMDiffOn_chartLocalFrame (I := I) (n := n + 1) x j).mono
      (by rw [TangentBundle.trivializationAt_baseSet]; exact inter_subset_right)
  have hbase : MapsTo Prod.snd (univ ×ˢ s : Set (P × M))
      ((trivializationAt E (TangentSpace I) x).baseSet ∩
        (trivializationAt ℝ (Trivial M ℝ) x).baseSet) := fun q hq ↦
    ⟨by simpa only [TangentBundle.trivializationAt_baseSet] using hq.2.2,
      by simp [Trivial.eq_trivialization]⟩
  -- First recover the covectors `g_p(∇ᵖ_X Y, ·)` from their evaluations on a frame, which are
  -- half the Koszul expressions.
  have heval (j : Fin (finrank ℝ E)) : ContMDiffOn (IP.prod I) 𝓘(ℝ) n
      (fun q : P × M ↦ g q.1 q.2 (cov q.1 Y q.2 (X q.2)) (chartLocalFrame (I := I) x j q.2))
      (univ ×ˢ s) := by
    have hK := (contMDiffOn_const (c := (2 : ℝ)⁻¹)).mul
      (contMDiffOn_koszulBilinear_family (b := fun p ↦ g p) hs hn₂ (hg.mono hsW)
        (hX.mono inter_subset_left) (hY.mono inter_subset_left) (hframe j))
    refine hK.congr fun q hq ↦ ?_
    have hXd := ((hX.mono inter_subset_left).mdifferentiableOn (by simp)).mdifferentiableAt
      (hs.mem_nhds hq.2)
    have hYd := ((hY.mono inter_subset_left).mdifferentiableOn (by simp)).mdifferentiableAt
      (hs.mem_nhds hq.2)
    have hZd := ((hframe j).mdifferentiableOn (by simp)).mdifferentiableAt (hs.mem_nhds hq.2)
    have hkos := (hcov q.1).two_apply_eq_koszul hXd hYd hZd
    rw [ContMDiffNondegenerateMetric.koszul_apply, ← koszulBilinear_apply] at hkos
    simp only [Pi.mul_apply]
    linarith
  have hflat : ContMDiffOn (IP.prod I) (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) n
      (fun q : P × M ↦ TotalSpace.mk' (E →L[ℝ] ℝ)
        (E := fun y : M ↦ TangentSpace I y →L[ℝ] ℝ) q.2 (g q.1 q.2 (cov q.1 Y q.2 (X q.2))))
      (univ ×ˢ s) := by
    refine contMDiffOn_hom_of_localFrame (I := I) (e := trivializationAt E (TangentSpace I) x)
      (e' := trivializationAt ℝ (Trivial M ℝ) x) (finBasis ℝ E) contMDiffOn_snd hbase
      fun j q hq ↦ ?_
    rw [contMDiffWithinAt_totalSpace]
    refine ⟨contMDiffWithinAt_snd, ?_⟩
    simpa [Trivial.eq_trivialization, ← chartLocalFrame_def] using heval j q hq
  -- The fibrewise inverses of the metrics are jointly regular, and recover the vectors.
  have hinv := ContMDiffOn.clm_bundle_inverse (E₁ := TangentSpace I)
    (E₂ := fun y : M ↦ TangentSpace I y →L[ℝ] ℝ) (ϕ := fun q : P × M ↦ g q.1 q.2)
    ((hg.mono hsW).of_le le_self_add) fun q _ ↦ (g q.1).isInvertible q.2
  have hsharp := hinv.clm_bundle_apply hflat
  refine ((hsharp.congr fun q _ ↦ ?_).contMDiffAt (hW.mem_nhds hxW)).contMDiffWithinAt
  simp only [((g q.1).isInvertible q.2).inverse_apply_self]

/-- Levi-Civita connections of a family of nondegenerate metrics, jointly `C^(n+1)` in the
parameter and the point, are jointly `C^n`: for a vector field `Y` which is `C^(n+1)` on the open
set `u`, the map `(p, x) ↦ ∇ᵖY(x)` into `Hom(TM, TM)` is `C^n` on `P × u`. -/
theorem contMDiffOn_covariantDerivative_of_isLeviCivitaConnection
    (hcov : ∀ p, (g p).IsLeviCivitaConnection (cov p)) (hn : n ≤ ∞) (hu : IsOpen u)
    (hg : ContMDiffOn (IP.prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) (n + 1)
      (fun q : P × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y : M ↦ TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) q.2 (g q.1 q.2))
      (univ ×ˢ u))
    (hY : ContMDiffOn I (I.prod 𝓘(ℝ, E)) (n + 1) (fun y ↦ TotalSpace.mk' E y (Y y)) u) :
    ContMDiffOn (IP.prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
      (fun q : P × M ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun y : M ↦ TangentSpace I y →L[ℝ] TangentSpace I y) q.2 (cov q.1 Y q.2))
      (univ ×ˢ u) := by
  have hn₂ : n + 2 ≤ ∞ := by simpa using hn
  have : IsManifold I (n + 1 + 1) M :=
    IsManifold.of_le (n := ∞) (by simpa only [add_assoc, one_add_one_eq_two] using hn₂)
  have : IsManifold I (n + 1) M := IsManifold.of_le (n := ∞) (by simpa using hn)
  have : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  rintro ⟨p, x⟩ ⟨-, hx⟩
  let s := u ∩ (chartAt H x).source
  have hs : IsOpen s := hu.inter (chartAt H x).open_source
  have hdir (j : Fin (finrank ℝ E)) :=
    contMDiffOn_covariantDerivative_apply_of_isLeviCivitaConnection hcov hn hs
      (hg.mono (prod_mono subset_rfl inter_subset_left))
      ((contMDiffOn_chartLocalFrame (I := I) (n := n + 1) x j).mono
        (by rw [TangentBundle.trivializationAt_baseSet]; exact inter_subset_right))
      (hY.mono inter_subset_left)
  have hhom := contMDiffOn_hom_of_localFrame (I := I)
    (e := trivializationAt E (TangentSpace I) x)
    (e' := trivializationAt E (TangentSpace I) x) (finBasis ℝ E) (u := univ ×ˢ s)
    contMDiffOn_snd
    (fun q hq ↦ by
      rw [TangentBundle.trivializationAt_baseSet, inter_self]
      exact hq.2.2)
    (A := fun q ↦ cov q.1 Y q.2) (fun j ↦ by simpa only [← chartLocalFrame_def] using hdir j)
  exact (hhom.contMDiffAt ((isOpen_univ.prod hs).mem_nhds
    ⟨mem_univ p, hx, mem_chart_source H x⟩)).contMDiffWithinAt

end Family

namespace ContMDiffNondegenerateMetric

variable {g : ContMDiffNondegenerateMetric (I := I) (M := M)}
  {cov : CovariantDerivative I E (fun x : M ↦ TangentSpace I x)}

/-- On an open set, a Levi-Civita connection of a smooth nondegenerate metric carries a
`C^(n+1)` vector field to a `C^n` section of `Hom(TM, TM)`, for `n ≤ ∞`. -/
theorem IsLeviCivitaConnection.contMDiffOn (h : g.IsLeviCivitaConnection cov)
    (hn : n ≤ ∞) (hu : IsOpen u)
    (hY : ContMDiffOn I (I.prod 𝓘(ℝ, E)) (n + 1) (fun y ↦ TotalSpace.mk' E y (Y y)) u) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun y : M ↦ TangentSpace I y →L[ℝ] TangentSpace I y) y (cov Y y)) u := by
  -- Regard `g` as a constant family over `ℝ` and restrict to the slice through `0`.
  have hfam := contMDiffOn_covariantDerivative_of_isLeviCivitaConnection (IP := 𝓘(ℝ))
    (g := fun _ : ℝ ↦ g) (cov := fun _ ↦ cov) (fun _ ↦ h) hn hu
    ((g.contMDiff.of_le (by simpa using hn)).comp contMDiff_snd).contMDiffOn hY
  exact hfam.comp (contMDiffOn_const.prodMk contMDiffOn_id) fun x hx ↦ ⟨mem_univ 0, hx⟩

/-- A Levi-Civita connection of a smooth nondegenerate metric is of class `C^n` for every
`n ≤ ∞`, in the native covariant-derivative class. In particular it is smooth. -/
theorem IsLeviCivitaConnection.contMDiffCovariantDerivative
    (h : g.IsLeviCivitaConnection cov) (hn : n ≤ ∞) : ContMDiffCovariantDerivative cov n where
  contMDiff := ⟨fun hY ↦ h.contMDiffOn hn isOpen_univ hY⟩

end ContMDiffNondegenerateMetric

namespace ContMDiffNondegenerateMetricFamily

variable {EP : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP]
  {HP : Type*} [TopologicalSpace HP] {IP : ModelWithCorners ℝ EP HP}
  {P : Type*} [TopologicalSpace P] [ChartedSpace HP P] [IsManifold IP 1 P]
  {g : ContMDiffNondegenerateMetricFamily I M IP P}
  {cov : P → CovariantDerivative I E (fun x : M ↦ TangentSpace I x)}

/-- **Levi-Civita connections of a smooth nondegenerate metric family are jointly regular.** For
a vector field `Y` which is `C^(n+1)` on the open set `u`, the map `(p, x) ↦ ∇ᵖY(x)` into
`Hom(TM, TM)` is `C^n` on `P × u`, where `∇ᵖ` is a Levi-Civita connection of the metric at the
parameter `p`. -/
theorem contMDiffOn_covariantDerivative_of_isLeviCivitaConnection
    (hcov : ∀ p, (g.metric p).IsLeviCivitaConnection (cov p)) (hn : n ≤ ∞) (hu : IsOpen u)
    (hY : ContMDiffOn I (I.prod 𝓘(ℝ, E)) (n + 1) (fun y ↦ TotalSpace.mk' E y (Y y)) u) :
    ContMDiffOn (IP.prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
      (fun q : P × M ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun y : M ↦ TangentSpace I y →L[ℝ] TangentSpace I y) q.2 (cov q.1 Y q.2))
      (univ ×ˢ u) := by
  have hg : ContMDiffOn (IP.prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) (n + 1)
      (fun q : P × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y : M ↦ TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) q.2 (g.metric q.1 q.2))
      (univ ×ˢ u) :=
    (g.contMDiff.of_le (by simpa using hn)).contMDiffOn.congr fun q _ ↦ by simp
  exact TauCeti.Manifold.contMDiffOn_covariantDerivative_of_isLeviCivitaConnection hcov hn hu hg hY

/-- **Levi-Civita connections of a smooth nondegenerate metric family are jointly regular.** For
a `C^(n+1)` vector field `Y`, the map `(p, x) ↦ ∇ᵖY(x)` into `Hom(TM, TM)` is `C^n`, where `∇ᵖ`
is a Levi-Civita connection of the metric at the parameter `p`. In particular it is smooth for a
smooth vector field. -/
theorem contMDiff_covariantDerivative_of_isLeviCivitaConnection
    (hcov : ∀ p, (g.metric p).IsLeviCivitaConnection (cov p)) (hn : n ≤ ∞)
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) (n + 1) (fun y ↦ TotalSpace.mk' E y (Y y))) :
    ContMDiff (IP.prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
      (fun q : P × M ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun y : M ↦ TangentSpace I y →L[ℝ] TangentSpace I y) q.2 (cov q.1 Y q.2)) := by
  rw [← contMDiffOn_univ, ← univ_prod_univ]
  exact contMDiffOn_covariantDerivative_of_isLeviCivitaConnection hcov hn isOpen_univ
    hY.contMDiffOn

end ContMDiffNondegenerateMetricFamily

end TauCeti.Manifold

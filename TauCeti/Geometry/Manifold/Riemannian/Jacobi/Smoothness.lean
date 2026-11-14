/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Jacobi.Basic
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Reparametrization
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Smoothness
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Bootstrap
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Smoothness
import TauCeti.Geometry.Manifold.VectorBundle.Scalar

/-!
# Smoothness and gluing of Jacobi fields

On a smooth Riemannian manifold (with or without boundary), every `C²` Jacobi field is smooth, as
is its covariant derivative. These statements concern the actual tangent-bundle lifts of sections
along the geodesic. They hold within the parameter set, including the endpoints of nondegenerate
closed intervals, and imply ordinary smoothness at interior parameters.

Using the boundaryless-free geodesic regularity from `Geodesic.Smoothness`, the Jacobi equation
makes the second covariant derivative as regular as the field itself. Solving the fixed-chart
covariant derivative formula for the ordinary derivative upgrades the field and its first covariant
derivative together, and also glues Jacobi fields across interior vertices of a closed interval when
their one-sided covariant derivatives agree (`IsJacobiFieldOn.union_Icc`,
`isJacobiFieldOn_Icc_of_partition`).

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Chapter 10.
-/

public section

open Bundle CovariantDerivative Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {γ : ℝ → M} {J : ∀ t, TangentSpace I (γ t)} {s : Set ℝ}

/-- If the lift of a Jacobi field is `C^(n + 1)` within its parameter set, so is the lift of its
second covariant derivative. -/
private theorem IsJacobiFieldOn.contMDiffOn_alongCurveWithin_alongCurveWithin
    (h : IsJacobiFieldOn I γ J s) (n : ℕ)
    (hJ : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent (n + 1 : ℕ)
      (fun r ↦ TotalSpace.mk' E (γ r) (J r)) s) :
    ContMDiffOn 𝓘(ℝ, ℝ) I.tangent (n + 1 : ℕ)
      (fun r ↦ TotalSpace.mk' E (γ r)
        (alongCurveWithin (leviCivitaConnection I M) γ
          (alongCurveWithin (leviCivitaConnection I M) γ J s) s r)) s := by
  let cov := leviCivitaConnection I M
  have hn_le_infty : (n + 1 : ℕ) ≤ (∞ : ℕ∞ω) := by simp
  have hvel_lift : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent (n + 1 : ℕ) (curveVelocityLiftWithin I γ s) s := by
    exact_mod_cast h.isGeodesicCurveOn.contMDiffOn_curveVelocityLiftWithin_of_le
      (m := ∞) (k := ∞) n (by simp) (by simp)
  have hvel' : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent (n + 1 : ℕ)
      (fun r ↦ TotalSpace.mk' E (γ r) (curveVelocityWithin I γ s r)) s := by
    simpa only [funext (curveVelocityLiftWithin_apply (I := I) γ s)] using hvel_lift
  have hcurv := cov.contMDiffOn_curvatureTensor (F := E) (V := TangentSpace I)
        hn_le_infty hJ hvel' hvel'
  refine (contMDiffOn_const (c := (-1 : ℝ))).smul_totalSpace hcurv |>.congr ?_
  intro r hr
  simp only [neg_one_smul]
  exact congrArg (TotalSpace.mk' E (γ r)) (h.alongCurveWithin_alongCurveWithin_eq hr)

/-- The simultaneous finite-order bootstrap for a Jacobi field and its first derivative. -/
private theorem IsJacobiFieldOn.contMDiffOn_nat_pair (h : IsJacobiFieldOn I γ J s) (n : ℕ) :
    ContMDiffOn 𝓘(ℝ, ℝ) I.tangent (n + 1 : ℕ)
        (fun r ↦ TotalSpace.mk' E (γ r) (J r)) s ∧
      ContMDiffOn 𝓘(ℝ, ℝ) I.tangent (n + 1 : ℕ)
        (fun r ↦ TotalSpace.mk' E (γ r)
          (alongCurveWithin (leviCivitaConnection I M) γ J s r)) s := by
  induction n with
  | zero => exact ⟨h.contMDiffOn.of_le (by norm_num), h.contMDiffOn_alongCurveWithin⟩
  | succ n ih =>
    let cov := leviCivitaConnection I M
    have hDDJ := h.contMDiffOn_alongCurveWithin_alongCurveWithin n ih.1
    -- Both first-order equations now have right-hand sides of class C^(n + 1).
    have hcov (t : ℝ) (_ht : t ∈ s) :
        ContMDiffCovariantDerivativeOn E (n + 1 : ℕ) cov.toFun
          (trivializationAt E (TangentSpace I) (γ t)).baseSet :=
      contMDiffCovariantDerivativeOn_leviCivitaConnection
        (m := ∞) (k := ∞) (trivializationAt E (TangentSpace I) (γ t)).open_baseSet
        (by simp) (by simp)
    have hγ' : ContMDiffOn 𝓘(ℝ, ℝ) I (n + 1 + 1 : ℕ) γ s := by
      exact_mod_cast h.isGeodesicCurveOn.contMDiffOn_of_le (m := ∞) (k := ∞) n (by simp) (by simp)
    exact ⟨contMDiffOn_succ_of_alongCurveWithin cov γ J (by omega) hcov h.uniqueDiffOn
        hγ' ih.1 ih.2,
      contMDiffOn_succ_of_alongCurveWithin cov γ (alongCurveWithin cov γ J s)
        (by omega) hcov h.uniqueDiffOn hγ' ih.2 hDDJ⟩

/-- A `C²` Jacobi field along a geodesic of a smooth metric is smooth within its
parameter set, including at closed interval endpoints. -/
theorem IsJacobiFieldOn.contMDiffOn_infty (h : IsJacobiFieldOn I γ J s) :
    ContMDiffOn 𝓘(ℝ, ℝ) I.tangent ∞
      (fun r ↦ TotalSpace.mk' E (γ r) (J r)) s :=
  _root_.contMDiffOn_infty.2 fun n ↦
    (h.contMDiffOn_nat_pair n).1.of_le (by exact_mod_cast Nat.le_succ n)

/-- The covariant derivative of a Jacobi field for a smooth metric has a smooth
lift to the tangent bundle within the parameter set. -/
theorem IsJacobiFieldOn.contMDiffOn_alongCurveWithin_infty (h : IsJacobiFieldOn I γ J s) :
    ContMDiffOn 𝓘(ℝ, ℝ) I.tangent ∞
      (fun r ↦ TotalSpace.mk' E (γ r)
        (alongCurveWithin (leviCivitaConnection I M) γ J s r)) s :=
  _root_.contMDiffOn_infty.2 fun n ↦
    (h.contMDiffOn_nat_pair n).2.of_le (by exact_mod_cast Nat.le_succ n)

/-- A Jacobi field for a smooth metric is smooth at each interior parameter. -/
theorem IsJacobiFieldOn.contMDiffAt_infty (h : IsJacobiFieldOn I γ J s) {t : ℝ}
    (ht : s ∈ 𝓝 t) :
    ContMDiffAt 𝓘(ℝ, ℝ) I.tangent ∞ (fun r ↦ TotalSpace.mk' E (γ r) (J r)) t :=
  h.contMDiffOn_infty.contMDiffAt ht

/-- **Two-piece Jacobi gluing.** If `γ` is a geodesic on `[a, b]` and `V` is a Jacobi field on
`[a, c]` and on `[c, b]` whose left and right covariant derivatives agree at `c`, then `V` is a
Jacobi field on `[a, b]`. When `c ≤ a` or `b ≤ c`, one piece already covers `[a, b]`. -/
theorem IsJacobiFieldOn.union_Icc {V : ∀ t, TangentSpace I (γ t)} {a c b : ℝ}
    (h₁ : IsJacobiFieldOn I γ V (Icc a c)) (h₂ : IsJacobiFieldOn I γ V (Icc c b))
    (hγ : IsGeodesicCurveOn I γ (Icc a b))
    (hD : alongCurveWithin (leviCivitaConnection I M) γ V (Icc a c) c =
      alongCurveWithin (leviCivitaConnection I M) γ V (Icc c b) c) :
    IsJacobiFieldOn I γ V (Icc a b) := by
  rcases le_or_gt c a with hca | hac
  · exact h₂.mono hγ.uniqueDiffOn (Icc_subset_Icc hca le_rfl)
  rcases le_or_gt b c with hbc | hcb
  · exact h₁.mono hγ.uniqueDiffOn (Icc_subset_Icc le_rfl hbc)
  let cov := leviCivitaConnection I M
  have hγ1 : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc a b) := hγ.contMDiffOn.of_le one_le_two
  have hV1 := contMDiffOn_one_union_Icc_of_alongCurveWithin_eq cov hγ1
    (h₁.contMDiffOn.of_le one_le_two) (h₂.contMDiffOn.of_le one_le_two) hD
  have hD₁ (r : ℝ) (hr : r ∈ Icc a c) :=
    alongCurveWithin_subset_of_contMDiffOn_one cov (Icc_subset_Icc_right hcb.le)
      (uniqueDiffOn_Icc hac r hr) hV1 hr
  have hD₂ (r : ℝ) (hr : r ∈ Icc c b) :=
    alongCurveWithin_subset_of_contMDiffOn_one cov (Icc_subset_Icc_left hac.le)
      (uniqueDiffOn_Icc hcb r hr) hV1 hr
  have hDD₁ (r : ℝ) (hr : r ∈ Icc a c) := alongCurveWithin_congr cov γ _
    (Filter.mem_of_superset self_mem_nhdsWithin fun s hs ↦ (hD₁ s hs).symm) (hD₁ r hr).symm
  have hDD₂ (r : ℝ) (hr : r ∈ Icc c b) := alongCurveWithin_congr cov γ _
    (Filter.mem_of_superset self_mem_nhdsWithin fun s hs ↦ (hD₂ s hs).symm) (hD₂ r hr).symm
  have hvel₁ (r : ℝ) (hr : r ∈ Icc a c) :=
    curveVelocityWithin_subset (Icc_subset_Icc_right hcb.le) (uniqueDiffOn_Icc hac r hr)
      (hγ.mdifferentiableOn r ⟨hr.1, hr.2.trans hcb.le⟩)
  have hvel₂ (r : ℝ) (hr : r ∈ Icc c b) :=
    curveVelocityWithin_subset (Icc_subset_Icc_left hac.le) (uniqueDiffOn_Icc hcb r hr)
      (hγ.mdifferentiableOn r ⟨hac.le.trans hr.1, hr.2⟩)
  have hDV1 : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1
      (fun r ↦ TotalSpace.mk' E (γ r) (alongCurveWithin cov γ V (Icc a b) r)) (Icc a b) := by
    refine contMDiffOn_one_union_Icc_of_alongCurveWithin_eq cov hγ1
      (h₁.contMDiffOn_alongCurveWithin.congr fun r hr ↦ congrArg (TotalSpace.mk' E (γ r))
        (hD₁ r hr).symm)
      (h₂.contMDiffOn_alongCurveWithin.congr fun r hr ↦ congrArg (TotalSpace.mk' E (γ r))
        (hD₂ r hr).symm) ?_
    rw [hDD₁ c ⟨hac.le, le_rfl⟩, h₁.alongCurveWithin_alongCurveWithin_eq ⟨hac.le, le_rfl⟩,
      hDD₂ c ⟨le_rfl, hcb.le⟩, h₂.alongCurveWithin_alongCurveWithin_eq ⟨le_rfl, hcb.le⟩,
      hvel₁ c ⟨hac.le, le_rfl⟩, hvel₂ c ⟨le_rfl, hcb.le⟩]
  have hV2 := contMDiffOn_succ_of_alongCurveWithin cov γ V le_rfl
    (fun t _ ↦ contMDiffCovariantDerivativeOn_leviCivitaConnection (m := ∞) (k := ∞)
      (trivializationAt E (TangentSpace I) (γ t)).open_baseSet (by simp) (by simp))
    (uniqueDiffOn_Icc (hac.trans hcb)) hγ.contMDiffOn hV1 hDV1
  refine ⟨hγ, hV2, fun r hr ↦ ?_⟩
  rcases le_total r c with hrc | hcr
  · rw [← alongCurveWithin_subset_of_contMDiffOn_one cov (Icc_subset_Icc_right hcb.le)
        (uniqueDiffOn_Icc hac r ⟨hr.1, hrc⟩) hDV1 ⟨hr.1, hrc⟩, hDD₁ r ⟨hr.1, hrc⟩,
      ← hvel₁ r ⟨hr.1, hrc⟩]
    exact h₁.equation r ⟨hr.1, hrc⟩
  · rw [← alongCurveWithin_subset_of_contMDiffOn_one cov (Icc_subset_Icc_left hac.le)
        (uniqueDiffOn_Icc hcb r ⟨hcr, hr.2⟩) hDV1 ⟨hcr, hr.2⟩, hDD₂ r ⟨hcr, hr.2⟩,
      ← hvel₂ r ⟨hcr, hr.2⟩]
    exact h₂.equation r ⟨hcr, hr.2⟩

/-- **Partition Jacobi gluing.** If `γ` is a geodesic on `[a, b]` and `V` solves the Jacobi
equation on each closed piece of a strict partition `τ` of `[a, b]` with matching one-sided
covariant derivatives at every interior vertex, then `V` is an unbroken Jacobi field on `[a, b]`. -/
theorem isJacobiFieldOn_Icc_of_partition {V : ∀ t, TangentSpace I (γ t)}
    {a b : ℝ} {k : ℕ} (τ : Fin (k + 2) → ℝ) (hτa : τ 0 = a) (hτb : τ (Fin.last (k + 1)) = b)
    (hτ : ∀ i : Fin (k + 1), τ i.castSucc < τ i.succ)
    (hγ : IsGeodesicCurveOn I γ (Icc a b))
    (hV : ∀ i : Fin (k + 1), IsJacobiFieldOn I γ V (Icc (τ i.castSucc) (τ i.succ)))
    (hjump : ∀ j : Fin k,
      alongCurveWithin (leviCivitaConnection I M) γ V
          (Icc (τ j.castSucc.castSucc) (τ j.castSucc.succ)) (τ j.castSucc.succ) =
        alongCurveWithin (leviCivitaConnection I M) γ V
          (Icc (τ j.succ.castSucc) (τ j.succ.succ)) (τ j.castSucc.succ)) :
    IsJacobiFieldOn I γ V (Icc a b) := by
  induction k generalizing a b with
  | zero =>
    subst hτa hτb
    exact hV 0
  | succ k ih =>
    subst hτa hτb
    let c := τ (Fin.last (k + 1)).castSucc
    have hac : τ 0 < c := Fin.strictMono_iff_lt_succ.mpr hτ (Fin.castSucc_pos Fin.last_pos')
    have hcb : c < τ (Fin.last (k + 2)) := by
      simpa only [Fin.succ_last] using hτ (Fin.last (k + 1))
    have hleft : IsJacobiFieldOn I γ V (Icc (τ 0) c) :=
      ih (fun i ↦ τ i.castSucc) rfl rfl
        (fun i ↦ by simpa only [Fin.succ_castSucc] using hτ i.castSucc)
        (hγ.mono (uniqueDiffOn_Icc hac) (Icc_subset_Icc_right hcb.le))
        (fun i ↦ by simpa only [Fin.succ_castSucc] using hV i.castSucc)
        (fun j ↦ by simpa only [Fin.succ_castSucc] using hjump j.castSucc)
    have hright : IsJacobiFieldOn I γ V (Icc c (τ (Fin.last (k + 2)))) := by
      simpa only [c, Fin.succ_last] using hV (Fin.last (k + 1))
    have hDc : alongCurveWithin (leviCivitaConnection I M) γ V (Icc (τ 0) c) c =
        alongCurveWithin (leviCivitaConnection I M) γ V (Icc c (τ (Fin.last (k + 2)))) c := by
      have hsub : Icc (τ (Fin.last k).castSucc.castSucc) c ⊆ Icc (τ 0) c :=
        Icc_subset_Icc_left ((Fin.strictMono_iff_lt_succ.mpr hτ).monotone (Fin.zero_le _))
      have hlast : τ (Fin.last k).castSucc.castSucc < c := by
        simpa only [c, Fin.succ_last, Fin.succ_castSucc] using hτ (Fin.last k).castSucc
      rw [← hleft.alongCurveWithin_subset (uniqueDiffOn_Icc hlast c ⟨hlast.le, le_rfl⟩)
        hsub ⟨hlast.le, le_rfl⟩]
      simpa only [c, Fin.succ_last, Fin.succ_castSucc] using hjump (Fin.last k)
    exact hleft.union_Icc hright hγ hDc

end TauCeti.Manifold

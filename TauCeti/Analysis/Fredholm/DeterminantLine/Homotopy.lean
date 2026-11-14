/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.DeterminantLine.OrientationCover
import Mathlib.Topology.Homotopy.Lifting

/-!
# Homotopy invariance and covering monodromy of Fredholm determinant orientations

Along a continuous path of Fredholm operators `T : ℝ → E →L[ℝ] F`,
`TauCeti.detLineOrientationTransport` carries orientations of `(T a).detLine` to orientations of
`(T b).detLine` by following coherent families of determinant-line elements
(`TauCeti.Analysis.Fredholm.DeterminantLine.Transport`). Because `ContinuousOn` subsumes `C¹` paths
via `ContDiffOn.continuousOn`, all transport laws proved for continuous Fredholm families apply
directly to `C¹` (and higher-regularity) paths as well.

This file completes the path-algebraic and homotopy-theoretic package for determinant-line
orientation transport in both its unbundled (`ℝ → E →L[ℝ] F`) and bundled
(`{T : E →L[ℝ] F // T.IsFredholm}`) formulations:

* **Canonical identification for equal operators (`LinearMap.detLineOfEq`).** An equality `f = g`
  of linear maps induces a canonical linear equivalence `f.detLine ≃ₗ[R] g.detLine` via
  `LinearMap.detLineCongr`, compatible with reflexivity, symmetry, transitivity, and kernel charts
  (`ContinuousLinearMap.detLineChartEquiv_detLineOfEq`). This avoids raw dependent casts when
  comparing paths whose endpoints agree propositionally.
* **Congruence, reparametrization, rectangle commutativity, and endpoint-relative homotopy
  invariance of `TauCeti.detLineOrientationTransport`.** Transport depends only on the values of the
  family on `[[a, b]]` (`TauCeti.detLineOrientationTransport_congr`) and is invariant under
  continuous reparametrizations (`TauCeti.detLineOrientationTransport_comp`). Over a parameter
  rectangle `[[s₀, s₁]] ×ˢ [[a, b]]`, convexity yields a coherent family over the entire rectangle
  (`TauCeti.exists_isDetLineCoherentOn_of_convex`), so the two boundary routes from `(s₀, a)` to
  `(s₁, b)` induce the same orientation transport (`TauCeti.detLineOrientationTransport_prod_comm`).
  Specializing to families constant on the vertical edges gives endpoint-relative homotopy
  invariance (`TauCeti.detLineOrientationTransport_eq_of_homotopy`,
  `TauCeti.detLineOrientationTransport_eq_of_homotopy_rel`) and path-independence inside any convex
  set of Fredholm operators (`TauCeti.detLineOrientationTransport_eq_of_convex`).
* **Bundled path and homotopy-class transport via covering monodromy.** Lifting paths in
  `{T : E →L[ℝ] F // T.IsFredholm}` to the orientation double cover
  `TauCeti.VectorBundleOrientationCover ℝ (FredholmDetLine ℝ E F) (Fin 1)` via
  `IsCoveringMap.monodromy` defines orientation transport on path homotopy classes
  (`TauCeti.FredholmDetLine.quotientOrientationTransport`) and on paths
  (`TauCeti.FredholmDetLine.pathOrientationTransport`), satisfying identity, reversal,
  concatenation, negation, and endpoint-relative homotopy invariance, and agreeing with
  `TauCeti.detLineOrientationTransport` (`TauCeti.FredholmDetLine.pathOrientationTransport_apply`).
  Restricting to loops at a basepoint `T₀` yields the orientation monodromy sign character
  `TauCeti.FredholmDetLine.orientationMonodromySign : FundamentalGroup _ T₀ →* ℤˣ`.

## Main definitions

* `LinearMap.detLineOfEq`: canonical linear equivalence `f.detLine ≃ₗ[R] g.detLine` from `f = g`.
* `TauCeti.FredholmDetLine.quotientOrientationTransport`: orientation transport along a homotopy
  class of paths in `{T : E →L[ℝ] F // T.IsFredholm}` via covering monodromy.
* `TauCeti.FredholmDetLine.pathOrientationTransport`: orientation transport along a continuous
  `Path` of Fredholm operators.
* `TauCeti.FredholmDetLine.orientationMonodromySign`: homomorphism `FundamentalGroup _ T₀ →* ℤˣ`
  recording whether monodromy around a loop preserves (`1`) or reverses (`-1`) determinant-line
  orientation.

## Main results

* `TauCeti.detLineOrientationTransport_congr`: congruence of transport for families agreeing on
  `[[a, b]]`.
* `TauCeti.detLineOrientationTransport_comp`: reparametrization law for continuous maps into
  `[[a, b]]`.
* `TauCeti.detLineOrientationTransport_prod_comm`: commutativity of orientation transport around the
  boundary of a parameter rectangle `[[s₀, s₁]] ×ˢ [[a, b]]`.
* `TauCeti.detLineOrientationTransport_eq_of_homotopy`,
  `TauCeti.detLineOrientationTransport_eq_of_homotopy_rel`: endpoint-relative homotopy invariance of
  `TauCeti.detLineOrientationTransport`.
* `TauCeti.detLineOrientationTransport_eq_of_convex`: path-independence of orientation transport for
  paths with common endpoints in a convex set of Fredholm operators.
* `TauCeti.FredholmDetLine.pathOrientationTransport_of_continuousOn`,
  `TauCeti.FredholmDetLine.pathOrientationTransport_apply`: agreement between covering monodromy
  transport and `TauCeti.detLineOrientationTransport`.
* `TauCeti.FredholmDetLine.orientationMonodromySign_eq_one_iff`: a loop has trivial orientation
  monodromy sign if and only if its orientation transport is the identity.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  AMS Colloquium Publications 52, 2012, Section A.2 (determinant line bundles).
* A. Zinger, *The determinant line bundle for Fredholm operators: construction, properties, and
  classification*, Math. Scand. 118 (2016), 203–268, arXiv:1304.6368.
-/

public section

noncomputable section

open Bundle Filter Set Topology Module ContinuousLinearMap

namespace LinearMap

section CommRing

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

/-- The canonical linear equivalence `f.detLine ≃ₗ[R] g.detLine` induced by an equality `f = g` of
linear maps, defined as `LinearMap.detLineCongr` along the identity equivalences of `M` and `N`. -/
def detLineOfEq {f g : M →ₗ[R] N} (h : f = g) : f.detLine ≃ₗ[R] g.detLine :=
  f.detLineCongr (.refl R M) (.refl R N) (by simp [h])

@[simp]
theorem detLineOfEq_rfl (f : M →ₗ[R] N) :
    detLineOfEq (rfl : f = f) = LinearEquiv.refl R f.detLine :=
  detLineCongr_refl

@[simp]
theorem detLineOfEq_symm {f g : M →ₗ[R] N} (h : f = g) :
    (detLineOfEq h).symm = detLineOfEq h.symm := by
  subst h
  simp

/-- Composing `LinearMap.detLineOfEq` along two chained equalities equals `LinearMap.detLineOfEq`
of their transitivity. -/
theorem detLineOfEq_trans {f g k : M →ₗ[R] N} (h₁ : f = g) (h₂ : g = k) :
    (detLineOfEq h₁).trans (detLineOfEq h₂) = detLineOfEq (h₁.trans h₂) := by
  subst h₁
  subst h₂
  simp

end CommRing

section OrderedRing

variable {R M N : Type*} [CommRing R] [PartialOrder R] [IsStrictOrderedRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

@[simp]
theorem ray_map_detLineOfEq_neg {f g : M →ₗ[R] N} (h : f = g) (r : Module.Ray R f.detLine) :
    Module.Ray.map (detLineOfEq h) (-r) = -Module.Ray.map (detLineOfEq h) r := by
  subst h
  simp

@[simp]
theorem ray_map_detLineOfEq_trans {f g k : M →ₗ[R] N} (h₁ : f = g) (h₂ : g = k)
    (r : Module.Ray R f.detLine) :
    Module.Ray.map (detLineOfEq h₂) (Module.Ray.map (detLineOfEq h₁) r) =
      Module.Ray.map (detLineOfEq (h₁.trans h₂)) r := by
  subst h₁
  subst h₂
  simp

end OrderedRing

end LinearMap

/-- Kernel charts `ContinuousLinearMap.detLineChartEquiv` commute with `LinearMap.detLineOfEq`. -/
theorem ContinuousLinearMap.detLineChartEquiv_detLineOfEq
    {𝕜 E F Λ G : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [NormedAddCommGroup Λ] [NormedSpace 𝕜 Λ] [FiniteDimensional 𝕜 Λ]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G] [FiniteDimensional 𝕜 G]
    {T₀ T₁ : E →L[𝕜] F} (hT : T₀ = T₁) (D₂ : Λ →L[𝕜] F) (q : E × Λ →L[𝕜] G)
    (h₀ : ((T₀.coprod D₂).prod q).IsInvertible) (h₁ : ((T₁.coprod D₂).prod q).IsInvertible)
    (v : (T₀ : E →ₗ[𝕜] F).detLine) :
    detLineChartEquiv T₁ D₂ q h₁
        (LinearMap.detLineOfEq (congrArg ContinuousLinearMap.toLinearMap hT) v) =
      detLineChartEquiv T₀ D₂ q h₀ v := by
  subst hT
  simp

namespace TauCeti

section UnbundledHomotopy

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Transporting a coherent family along pointwise operator equalities `T₀ x = T₁ x` on `s` via
`LinearMap.detLineOfEq` preserves coherence on `s`. -/
theorem IsDetLineCoherentOn.congr_eq {X : Type*} [TopologicalSpace X]
    {T₀ T₁ : X → E →L[ℝ] F} {v : ∀ x, (T₀ x : E →ₗ[ℝ] F).detLine}
    {w : ∀ x, (T₁ x : E →ₗ[ℝ] F).detLine} {s : Set X}
    (hv : IsDetLineCoherentOn T₀ v s) (hT : ∀ x ∈ s, T₀ x = T₁ x)
    (hw : ∀ x (hx : x ∈ s),
      w x = LinearMap.detLineOfEq (congrArg ContinuousLinearMap.toLinearMap (hT x hx)) (v x)) :
    IsDetLineCoherentOn T₁ w s := by
  rw [isDetLineCoherentOn_iff] at hv ⊢
  intro x₀ hx₀
  obtain ⟨hv₀, S, hS, G, hG, q, h₀, hev⟩ := isDetLineCoherentWithinAt_iff.1 (hv x₀ hx₀)
  have h₁ : (((T₁ x₀).coprod S.subtypeL).prod q).IsInvertible := hT x₀ hx₀ ▸ h₀
  have hw₀ : w x₀ ≠ 0 := by
    rw [hw x₀ hx₀]
    exact (LinearEquiv.map_ne_zero_iff _).2 hv₀
  refine isDetLineCoherentWithinAt_iff.2 ⟨hw₀, S, hS, G, hG, q, h₁, ?_⟩
  filter_upwards [hev, self_mem_nhdsWithin] with x hx hxs
  obtain ⟨hxinv, hsr⟩ := hx
  have hxinv₁ : (((T₁ x).coprod S.subtypeL).prod q).IsInvertible := hT x hxs ▸ hxinv
  refine ⟨hxinv₁, ?_⟩
  rw [hw x hxs, hw x₀ hx₀, detLineChartEquiv_detLineOfEq (hT x hxs) S.subtypeL q hxinv hxinv₁,
    detLineChartEquiv_detLineOfEq (hT x₀ hx₀) S.subtypeL q h₀ h₁]
  exact hsr

variable [CompleteSpace E] [CompleteSpace F]

/-- **Congruence of orientation transport.** Two Fredholm families `T₀, T₁ : ℝ → E →L[ℝ] F` that
agree at every point of `[[a, b]]` induce the same orientation transport, intertwined by
`LinearMap.detLineOfEq` at the endpoints. -/
theorem detLineOrientationTransport_congr {T₀ T₁ : ℝ → E →L[ℝ] F} {a b : ℝ}
    (hT₀ : ContinuousOn T₀ (uIcc a b)) (hT₁ : ContinuousOn T₁ (uIcc a b))
    (hF₀ : ∀ t ∈ uIcc a b, (T₀ t).IsFredholm) (hF₁ : ∀ t ∈ uIcc a b, (T₁ t).IsFredholm)
    (hTU : ∀ t ∈ uIcc a b, T₀ t = T₁ t) (o : Module.Ray ℝ (T₀ a : E →ₗ[ℝ] F).detLine) :
    detLineOrientationTransport a b hT₁ hF₁
        (Module.Ray.map (LinearMap.detLineOfEq
          (congrArg ContinuousLinearMap.toLinearMap (hTU a left_mem_uIcc))) o) =
      Module.Ray.map (LinearMap.detLineOfEq
          (congrArg ContinuousLinearMap.toLinearMap (hTU b right_mem_uIcc)))
        (detLineOrientationTransport a b hT₀ hF₀ o) := by
  induction o using Module.Ray.ind with | h v₀ hv₀ =>
  obtain ⟨v, rfl, hv⟩ := exists_isDetLineCoherentOn_Icc hT₀ hF₀ left_mem_uIcc hv₀
  classical
  let w : ∀ t, (T₁ t : E →ₗ[ℝ] F).detLine := fun t ↦
    if ht : t ∈ uIcc a b then
      LinearMap.detLineOfEq (congrArg ContinuousLinearMap.toLinearMap (hTU t ht)) (v t)
    else 0
  have hw_coh : IsDetLineCoherentOn T₁ w (uIcc a b) :=
    hv.congr_eq hTU fun t ht ↦ dite_eq_left ht
  have hwa : Module.Ray.map (LinearMap.detLineOfEq
      (congrArg ContinuousLinearMap.toLinearMap (hTU a left_mem_uIcc)))
        (rayOfNeZero ℝ (v a) hv₀) = rayOfNeZero ℝ (w a) (hw_coh.ne_zero left_mem_uIcc) := by
    rw [Module.Ray.map_apply, ray_eq_iff]
    simpa only [w, dite_eq_left left_mem_uIcc] using SameRay.rfl
  rw [hwa, detLineOrientationTransport_rayOfNeZero hT₁ hF₁ hw_coh,
    detLineOrientationTransport_rayOfNeZero hT₀ hF₀ hv, Module.Ray.map_apply, ray_eq_iff]
  simpa only [w, dite_eq_left right_mem_uIcc] using SameRay.rfl

/-- **Reparametrization law for orientation transport.** If `φ : ℝ → ℝ` is continuous on
`[[a', b']]` and maps `[[a', b']]` into `[[a, b]]`, then orientation transport for `T ∘ φ` from `a'`
to `b'` equals orientation transport for `T` from `φ a'` to `φ b'`. -/
theorem detLineOrientationTransport_comp {T : ℝ → E →L[ℝ] F} {φ : ℝ → ℝ} {a b a' b' : ℝ}
    (hT : ContinuousOn T (uIcc a b)) (hF : ∀ t ∈ uIcc a b, (T t).IsFredholm)
    (hφ : ContinuousOn φ (uIcc a' b')) (hmaps : MapsTo φ (uIcc a' b') (uIcc a b))
    (hTφ : ContinuousOn (T ∘ φ) (uIcc a' b')) (hFφ : ∀ t ∈ uIcc a' b', (T (φ t)).IsFredholm)
    (hT' : ContinuousOn T (uIcc (φ a') (φ b')))
    (hF' : ∀ t ∈ uIcc (φ a') (φ b'), (T t).IsFredholm)
    (o : Module.Ray ℝ (T (φ a') : E →ₗ[ℝ] F).detLine) :
    detLineOrientationTransport (T := T ∘ φ) a' b' hTφ hFφ o =
      detLineOrientationTransport (T := T) (φ a') (φ b') hT' hF' o := by
  induction o using Module.Ray.ind with | h v₀ hv₀ =>
  obtain ⟨v, rfl, hv⟩ := exists_isDetLineCoherentOn_Icc hT hF (hmaps left_mem_uIcc) hv₀
  have hsub : uIcc (φ a') (φ b') ⊆ uIcc a b :=
    ordConnected_Icc.uIcc_subset (hmaps left_mem_uIcc) (hmaps right_mem_uIcc)
  rw [detLineOrientationTransport_rayOfNeZero hTφ hFφ (hv.comp hφ hmaps),
    detLineOrientationTransport_rayOfNeZero hT' hF' (hv.mono hsub)]

/-- **Commutativity of orientation transport around a parameter rectangle.** For a family
`H : ℝ × ℝ → E →L[ℝ] F` that is continuous and Fredholm on `[[s₀, s₁]] ×ˢ [[a, b]]`, transporting an
orientation from `(s₀, a)` to `(s₀, b)` and then to `(s₁, b)` agrees with transporting from
`(s₀, a)` to `(s₁, a)` and then to `(s₁, b)`. -/
theorem detLineOrientationTransport_prod_comm {H : ℝ × ℝ → E →L[ℝ] F} {s₀ s₁ a b : ℝ}
    (hH : ContinuousOn H (uIcc s₀ s₁ ×ˢ uIcc a b))
    (hF : ∀ p ∈ uIcc s₀ s₁ ×ˢ uIcc a b, (H p).IsFredholm)
    (hHs₀ : ContinuousOn (fun t ↦ H (s₀, t)) (uIcc a b))
    (hFs₀ : ∀ t ∈ uIcc a b, (H (s₀, t)).IsFredholm)
    (hHs₁ : ContinuousOn (fun t ↦ H (s₁, t)) (uIcc a b))
    (hFs₁ : ∀ t ∈ uIcc a b, (H (s₁, t)).IsFredholm)
    (hHa : ContinuousOn (fun s ↦ H (s, a)) (uIcc s₀ s₁))
    (hFa : ∀ s ∈ uIcc s₀ s₁, (H (s, a)).IsFredholm)
    (hHb : ContinuousOn (fun s ↦ H (s, b)) (uIcc s₀ s₁))
    (hFb : ∀ s ∈ uIcc s₀ s₁, (H (s, b)).IsFredholm)
    (o : Module.Ray ℝ (H (s₀, a) : E →ₗ[ℝ] F).detLine) :
    detLineOrientationTransport (T := fun s ↦ H (s, b)) s₀ s₁ hHb hFb
        (detLineOrientationTransport (T := fun t ↦ H (s₀, t)) a b hHs₀ hFs₀ o) =
      detLineOrientationTransport (T := fun t ↦ H (s₁, t)) a b hHs₁ hFs₁
        (detLineOrientationTransport (T := fun s ↦ H (s, a)) s₀ s₁ hHa hFa o) := by
  induction o using Module.Ray.ind with | h v₀ hv₀ =>
  -- Extend `v₀` at `(s₀, a)` to a coherent family on the convex rectangle `[[s₀, s₁]] ×ˢ [[a, b]]`.
  obtain ⟨v, rfl, hv⟩ := exists_isDetLineCoherentOn_of_convex
    ((convex_uIcc s₀ s₁).prod (convex_uIcc a b)) hH hF ⟨left_mem_uIcc, left_mem_uIcc⟩ hv₀
  have hvs₀ : IsDetLineCoherentOn (fun t ↦ H (s₀, t)) (fun t ↦ v (s₀, t)) (uIcc a b) :=
    hv.comp (continuous_const.prodMk continuous_id).continuousOn fun _ ht ↦ ⟨left_mem_uIcc, ht⟩
  have hvs₁ : IsDetLineCoherentOn (fun t ↦ H (s₁, t)) (fun t ↦ v (s₁, t)) (uIcc a b) :=
    hv.comp (continuous_const.prodMk continuous_id).continuousOn fun _ ht ↦ ⟨right_mem_uIcc, ht⟩
  have hva : IsDetLineCoherentOn (fun s ↦ H (s, a)) (fun s ↦ v (s, a)) (uIcc s₀ s₁) :=
    hv.comp (continuous_id.prodMk continuous_const).continuousOn fun _ hs ↦ ⟨hs, left_mem_uIcc⟩
  have hvb : IsDetLineCoherentOn (fun s ↦ H (s, b)) (fun s ↦ v (s, b)) (uIcc s₀ s₁) :=
    hv.comp (continuous_id.prodMk continuous_const).continuousOn fun _ hs ↦ ⟨hs, right_mem_uIcc⟩
  rw [detLineOrientationTransport_rayOfNeZero hHs₀ hFs₀ hvs₀,
    detLineOrientationTransport_rayOfNeZero hHb hFb hvb,
    detLineOrientationTransport_rayOfNeZero hHa hFa hva,
    detLineOrientationTransport_rayOfNeZero hHs₁ hFs₁ hvs₁]

/-- **Endpoint-relative homotopy invariance of orientation transport.** If `H : ℝ × ℝ → E →L[ℝ] F`
is continuous and Fredholm on `[[s₀, s₁]] ×ˢ [[a, b]]` and keeps both endpoints `H (·, a)` and
`H (·, b)` constant on `[[s₀, s₁]]`, then the slices `H (s₀, ·)` and `H (s₁, ·)` induce the same
orientation transport from `a` to `b`. -/
theorem detLineOrientationTransport_eq_of_homotopy {H : ℝ × ℝ → E →L[ℝ] F} {s₀ s₁ a b : ℝ}
    (hH : ContinuousOn H (uIcc s₀ s₁ ×ˢ uIcc a b))
    (hF : ∀ p ∈ uIcc s₀ s₁ ×ˢ uIcc a b, (H p).IsFredholm)
    (ha : ∀ s ∈ uIcc s₀ s₁, H (s, a) = H (s₀, a))
    (hb : ∀ s ∈ uIcc s₀ s₁, H (s, b) = H (s₀, b))
    (hHs₀ : ContinuousOn (fun t ↦ H (s₀, t)) (uIcc a b))
    (hFs₀ : ∀ t ∈ uIcc a b, (H (s₀, t)).IsFredholm)
    (hHs₁ : ContinuousOn (fun t ↦ H (s₁, t)) (uIcc a b))
    (hFs₁ : ∀ t ∈ uIcc a b, (H (s₁, t)).IsFredholm)
    (o : Module.Ray ℝ (H (s₀, a) : E →ₗ[ℝ] F).detLine) :
    detLineOrientationTransport (T := fun t ↦ H (s₁, t)) a b hHs₁ hFs₁
        (Module.Ray.map (LinearMap.detLineOfEq
          (congrArg ContinuousLinearMap.toLinearMap (ha s₁ right_mem_uIcc).symm)) o) =
      Module.Ray.map (LinearMap.detLineOfEq
          (congrArg ContinuousLinearMap.toLinearMap (hb s₁ right_mem_uIcc).symm))
        (detLineOrientationTransport (T := fun t ↦ H (s₀, t)) a b hHs₀ hFs₀ o) := by
  have hHa : ContinuousOn (fun s ↦ H (s, a)) (uIcc s₀ s₁) :=
    hH.comp (continuous_id.prodMk continuous_const).continuousOn fun _ hs ↦ ⟨hs, left_mem_uIcc⟩
  have hFa : ∀ s ∈ uIcc s₀ s₁, (H (s, a)).IsFredholm := fun s hs ↦ hF (s, a) ⟨hs, left_mem_uIcc⟩
  have hHb : ContinuousOn (fun s ↦ H (s, b)) (uIcc s₀ s₁) :=
    hH.comp (continuous_id.prodMk continuous_const).continuousOn fun _ hs ↦ ⟨hs, right_mem_uIcc⟩
  have hFb : ∀ s ∈ uIcc s₀ s₁, (H (s, b)).IsFredholm := fun s hs ↦ hF (s, b) ⟨hs, right_mem_uIcc⟩
  have hleft : detLineOrientationTransport (T := fun s ↦ H (s, a)) s₀ s₁ hHa hFa o =
      Module.Ray.map (LinearMap.detLineOfEq
        (congrArg ContinuousLinearMap.toLinearMap (ha s₁ right_mem_uIcc).symm)) o := by
    have hc := detLineOrientationTransport_congr (T₀ := fun _ ↦ H (s₀, a))
      (T₁ := fun s ↦ H (s, a)) continuousOn_const hHa
      (fun _ _ ↦ hFs₀ a left_mem_uIcc) hFa (fun s hs ↦ (ha s hs).symm) o
    simpa only [ha s₀ left_mem_uIcc, LinearMap.detLineOfEq_rfl, Module.Ray.map_refl,
      Equiv.refl_apply, detLineOrientationTransport_const, id_eq] using hc
  have hright (r : Module.Ray ℝ (H (s₀, b) : E →ₗ[ℝ] F).detLine) :
      detLineOrientationTransport (T := fun s ↦ H (s, b)) s₀ s₁ hHb hFb r =
        Module.Ray.map (LinearMap.detLineOfEq
          (congrArg ContinuousLinearMap.toLinearMap (hb s₁ right_mem_uIcc).symm)) r := by
    have hc := detLineOrientationTransport_congr (T₀ := fun _ ↦ H (s₀, b))
      (T₁ := fun s ↦ H (s, b)) continuousOn_const hHb
      (fun _ _ ↦ hFs₀ b right_mem_uIcc) hFb (fun s hs ↦ (hb s hs).symm) r
    simpa only [hb s₀ left_mem_uIcc, LinearMap.detLineOfEq_rfl, Module.Ray.map_refl,
      Equiv.refl_apply, detLineOrientationTransport_const, id_eq] using hc
  rw [← hleft, ← detLineOrientationTransport_prod_comm hH hF hHs₀ hFs₀ hHs₁ hFs₁ hHa hFa hHb hFb o,
    hright]

/-- **Endpoint-relative homotopy invariance between two paths.** If `T₀, T₁ : ℝ → E →L[ℝ] F` are
joined on `[[s₀, s₁]] ×ˢ [[a, b]]` by a continuous Fredholm homotopy `H` with `H (s₀, ·) = T₀`,
`H (s₁, ·) = T₁`, and constant vertical edges `H (·, a) = T₀ a`, `H (·, b) = T₀ b`, then `T₀` and
`T₁` induce the same orientation transport. -/
theorem detLineOrientationTransport_eq_of_homotopy_rel
    {T₀ T₁ : ℝ → E →L[ℝ] F} {H : ℝ × ℝ → E →L[ℝ] F} {s₀ s₁ a b : ℝ}
    (hT₀ : ContinuousOn T₀ (uIcc a b)) (hF₀ : ∀ t ∈ uIcc a b, (T₀ t).IsFredholm)
    (hT₁ : ContinuousOn T₁ (uIcc a b)) (hF₁ : ∀ t ∈ uIcc a b, (T₁ t).IsFredholm)
    (hH : ContinuousOn H (uIcc s₀ s₁ ×ˢ uIcc a b))
    (hFH : ∀ p ∈ uIcc s₀ s₁ ×ˢ uIcc a b, (H p).IsFredholm)
    (hs₀ : ∀ t ∈ uIcc a b, H (s₀, t) = T₀ t)
    (hs₁ : ∀ t ∈ uIcc a b, H (s₁, t) = T₁ t)
    (ha : ∀ s ∈ uIcc s₀ s₁, H (s, a) = T₀ a)
    (hb : ∀ s ∈ uIcc s₀ s₁, H (s, b) = T₀ b)
    (ha₀₁ : T₀ a = T₁ a) (hb₀₁ : T₀ b = T₁ b)
    (o : Module.Ray ℝ (T₀ a : E →ₗ[ℝ] F).detLine) :
    detLineOrientationTransport a b hT₁ hF₁
        (Module.Ray.map (LinearMap.detLineOfEq (congrArg ContinuousLinearMap.toLinearMap ha₀₁)) o) =
      Module.Ray.map (LinearMap.detLineOfEq (congrArg ContinuousLinearMap.toLinearMap hb₀₁))
        (detLineOrientationTransport a b hT₀ hF₀ o) := by
  have hHs₀ : ContinuousOn (fun t ↦ H (s₀, t)) (uIcc a b) :=
    hH.comp (continuous_const.prodMk continuous_id).continuousOn fun _ ht ↦ ⟨left_mem_uIcc, ht⟩
  have hFs₀ : ∀ t ∈ uIcc a b, (H (s₀, t)).IsFredholm := fun t ht ↦ hFH (s₀, t) ⟨left_mem_uIcc, ht⟩
  have hHs₁ : ContinuousOn (fun t ↦ H (s₁, t)) (uIcc a b) :=
    hH.comp (continuous_const.prodMk continuous_id).continuousOn fun _ ht ↦ ⟨right_mem_uIcc, ht⟩
  have hFs₁ : ∀ t ∈ uIcc a b, (H (s₁, t)).IsFredholm := fun t ht ↦ hFH (s₁, t) ⟨right_mem_uIcc, ht⟩
  have ha' (s : ℝ) (hs : s ∈ uIcc s₀ s₁) : H (s, a) = H (s₀, a) :=
    (ha s hs).trans (ha s₀ left_mem_uIcc).symm
  have hb' (s : ℝ) (hs : s ∈ uIcc s₀ s₁) : H (s, b) = H (s₀, b) :=
    (hb s hs).trans (hb s₀ left_mem_uIcc).symm
  let e₀a := congrArg ContinuousLinearMap.toLinearMap (hs₀ a left_mem_uIcc).symm
  let ea := congrArg ContinuousLinearMap.toLinearMap (ha' s₁ right_mem_uIcc).symm
  let e₁a := congrArg ContinuousLinearMap.toLinearMap (hs₁ a left_mem_uIcc)
  let o' := Module.Ray.map (LinearMap.detLineOfEq e₀a) o
  let o₁ := Module.Ray.map (LinearMap.detLineOfEq ea) o'
  have hin₁ : Module.Ray.map (LinearMap.detLineOfEq e₁a) o₁ =
      Module.Ray.map (LinearMap.detLineOfEq (congrArg ContinuousLinearMap.toLinearMap ha₀₁)) o := by
    simp only [o₁, o', LinearMap.ray_map_detLineOfEq_trans]
  have hin₀ : Module.Ray.map (LinearMap.detLineOfEq
      (congrArg ContinuousLinearMap.toLinearMap (hs₀ a left_mem_uIcc))) o' = o := by
    simp only [o', LinearMap.ray_map_detLineOfEq_trans,
      LinearMap.detLineOfEq_rfl, Module.Ray.map_refl, Equiv.refl_apply]
  have hc₀ := detLineOrientationTransport_congr hHs₀ hT₀ hFs₀ hF₀ hs₀ o'
  rw [hin₀] at hc₀
  have hc₁ := detLineOrientationTransport_congr hHs₁ hT₁ hFs₁ hF₁ hs₁ o₁
  have hhom := detLineOrientationTransport_eq_of_homotopy hH hFH ha' hb' hHs₀ hFs₀ hHs₁ hFs₁ o'
  rw [← hin₁, hc₁, hhom, hc₀, LinearMap.ray_map_detLineOfEq_trans,
    LinearMap.ray_map_detLineOfEq_trans]

/-- **Path-independence in a convex set of Fredholm operators.** Any two continuous paths
`T₀, T₁ : ℝ → E →L[ℝ] F` taking values in a convex set `U` of Fredholm operators (for example, an
affine coset of compact perturbations of a fixed Fredholm operator) and sharing endpoints at `a` and
`b` induce the same orientation transport. -/
theorem detLineOrientationTransport_eq_of_convex {U : Set (E →L[ℝ] F)} (hU : Convex ℝ U)
    (hUF : ∀ S ∈ U, S.IsFredholm) {T₀ T₁ : ℝ → E →L[ℝ] F} {a b : ℝ}
    (hT₀ : ContinuousOn T₀ (uIcc a b)) (hT₁ : ContinuousOn T₁ (uIcc a b))
    (hT₀U : ∀ t ∈ uIcc a b, T₀ t ∈ U) (hT₁U : ∀ t ∈ uIcc a b, T₁ t ∈ U)
    (ha : T₀ a = T₁ a) (hb : T₀ b = T₁ b)
    (o : Module.Ray ℝ (T₀ a : E →ₗ[ℝ] F).detLine) :
    detLineOrientationTransport a b hT₁ (fun t ht ↦ hUF _ (hT₁U t ht))
        (Module.Ray.map (LinearMap.detLineOfEq (congrArg ContinuousLinearMap.toLinearMap ha)) o) =
      Module.Ray.map (LinearMap.detLineOfEq (congrArg ContinuousLinearMap.toLinearMap hb))
        (detLineOrientationTransport a b hT₀ (fun t ht ↦ hUF _ (hT₀U t ht)) o) := by
  let H : ℝ × ℝ → E →L[ℝ] F := fun p ↦ (1 - p.1) • T₀ p.2 + p.1 • T₁ p.2
  have hmaps : MapsTo Prod.snd (uIcc (0 : ℝ) 1 ×ˢ uIcc a b) (uIcc a b) := fun _ hp ↦ hp.2
  have hH : ContinuousOn H (uIcc (0 : ℝ) 1 ×ˢ uIcc a b) :=
    ((continuousOn_const.sub continuous_fst.continuousOn).smul
      (hT₀.comp continuous_snd.continuousOn hmaps)).add
      (continuous_fst.continuousOn.smul (hT₁.comp continuous_snd.continuousOn hmaps))
  have hHU (p : ℝ × ℝ) (hp : p ∈ uIcc (0 : ℝ) 1 ×ˢ uIcc a b) : H p ∈ U := by
    have hs : p.1 ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le (zero_le_one' ℝ)] using hp.1
    exact hU (hT₀U p.2 hp.2) (hT₁U p.2 hp.2) (sub_nonneg.2 hs.2) hs.1 (sub_add_cancel 1 p.1)
  exact detLineOrientationTransport_eq_of_homotopy_rel
    hT₀ (fun t ht ↦ hUF _ (hT₀U t ht)) hT₁ (fun t ht ↦ hUF _ (hT₁U t ht))
    hH (fun p hp ↦ hUF _ (hHU p hp))
    (fun t _ ↦ by simp [H]) (fun t _ ↦ by simp [H])
    (fun s _ ↦ by simp [H, ← ha, sub_smul])
    (fun s _ ↦ by simp [H, ← hb, sub_smul])
    ha hb o

end UnbundledHomotopy

namespace FredholmDetLine

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

-- As in `LinearMap.instNegRayDetLine`, transfer ray negation facts across `orientationEquivRay` so
-- typeclass search does not need to resolve `AddCommGroup` on the tensor product `f.detLine`.
private theorem detLine_ray_ne_neg_self {T : {T : E →L[ℝ] F // T.IsFredholm}}
    (r : Module.Ray ℝ (T.1 : E →ₗ[ℝ] F).detLine) : r ≠ -r := by
  intro h
  have h' := congrArg (orientationEquivRay (ι := Fin 1) T).symm h
  rw [orientationEquivRay_symm_neg] at h'
  exact Module.Ray.ne_neg_self _ h'

private theorem detLine_ray_eq_or_eq_neg {T : {T : E →L[ℝ] F // T.IsFredholm}}
    (r₁ r₂ : Module.Ray ℝ (T.1 : E →ₗ[ℝ] F).detLine) : r₁ = r₂ ∨ r₁ = -r₂ := by
  have h := Orientation.eq_or_eq_neg_of_card_eq_finrank
    ((orientationEquivRay (ι := Fin 1) T).symm r₁)
    ((orientationEquivRay (ι := Fin 1) T).symm r₂) (by simp)
  exact h.imp (fun h₁ ↦ (orientationEquivRay (ι := Fin 1) T).symm.injective h₁) fun h₂ ↦
    (orientationEquivRay (ι := Fin 1) T).symm.injective
      (h₂.trans (orientationEquivRay_symm_neg T r₂).symm)

variable [CompleteSpace E] [CompleteSpace F]

/-- **Orientation transport along a path homotopy class.** Lifting paths in
`{T : E →L[ℝ] F // T.IsFredholm}` to the orientation double cover via `IsCoveringMap.monodromy`
transports orientations of `T₀.detLine` to orientations of `T₁.detLine`, depending only on the
endpoint-relative homotopy class of the path. -/
def quotientOrientationTransport {T₀ T₁ : {T : E →L[ℝ] F // T.IsFredholm}}
    (γ : Path.Homotopic.Quotient T₀ T₁) :
    Module.Ray ℝ (T₀.1 : E →ₗ[ℝ] F).detLine ≃ Module.Ray ℝ (T₁.1 : E →ₗ[ℝ] F).detLine where
  toFun r := orientationCoverFiberEquiv (Fin 1) T₁
    ((isCoveringMap_orientationCover_proj (E := E) (F := F) (ι := Fin 1)).monodromy γ
      ((orientationCoverFiberEquiv (Fin 1) T₀).symm r))
  invFun r := orientationCoverFiberEquiv (Fin 1) T₀
    ((isCoveringMap_orientationCover_proj (E := E) (F := F) (ι := Fin 1)).monodromy γ.symm
      ((orientationCoverFiberEquiv (Fin 1) T₁).symm r))
  left_inv r := by
    simp only [Equiv.symm_apply_apply, ← IsCoveringMap.monodromy_trans_apply,
      Path.Homotopic.Quotient.trans_symm, IsCoveringMap.monodromy_refl, id_eq,
      Equiv.apply_symm_apply]
  right_inv r := by
    simp only [Equiv.symm_apply_apply, ← IsCoveringMap.monodromy_trans_apply,
      Path.Homotopic.Quotient.symm_trans, IsCoveringMap.monodromy_refl, id_eq,
      Equiv.apply_symm_apply]

@[simp]
theorem quotientOrientationTransport_refl (T₀ : {T : E →L[ℝ] F // T.IsFredholm}) :
    quotientOrientationTransport (.refl T₀) = Equiv.refl _ := by
  ext r
  simp only [quotientOrientationTransport, Equiv.coe_fn_mk, IsCoveringMap.monodromy_refl, id_eq,
    Equiv.apply_symm_apply, Equiv.refl_apply]

@[simp]
theorem quotientOrientationTransport_symm {T₀ T₁ : {T : E →L[ℝ] F // T.IsFredholm}}
    (γ : Path.Homotopic.Quotient T₀ T₁) :
    (quotientOrientationTransport γ).symm = quotientOrientationTransport γ.symm :=
  Equiv.ext fun _ ↦ rfl

/-- Concatenation law for orientation transport along path homotopy classes. -/
theorem quotientOrientationTransport_trans {T₀ T₁ T₂ : {T : E →L[ℝ] F // T.IsFredholm}}
    (γ₁ : Path.Homotopic.Quotient T₀ T₁) (γ₂ : Path.Homotopic.Quotient T₁ T₂) :
    quotientOrientationTransport (γ₁.trans γ₂) =
      (quotientOrientationTransport γ₁).trans (quotientOrientationTransport γ₂) := by
  ext r
  simp only [quotientOrientationTransport, Equiv.coe_fn_mk, Equiv.trans_apply,
    Equiv.symm_apply_apply, IsCoveringMap.monodromy_trans_apply]

/-- **Orientation transport along a continuous path of Fredholm operators.** Defined by descending
`γ : Path T₀ T₁` to its homotopy class in `Path.Homotopic.Quotient T₀ T₁`. -/
def pathOrientationTransport {T₀ T₁ : {T : E →L[ℝ] F // T.IsFredholm}} (γ : Path T₀ T₁) :
    Module.Ray ℝ (T₀.1 : E →ₗ[ℝ] F).detLine ≃ Module.Ray ℝ (T₁.1 : E →ₗ[ℝ] F).detLine :=
  quotientOrientationTransport (.mk γ)

theorem pathOrientationTransport_def {T₀ T₁ : {T : E →L[ℝ] F // T.IsFredholm}} (γ : Path T₀ T₁) :
    pathOrientationTransport γ = quotientOrientationTransport (.mk γ) :=
  (rfl)

@[simp]
theorem pathOrientationTransport_refl (T₀ : {T : E →L[ℝ] F // T.IsFredholm}) :
    pathOrientationTransport (Path.refl T₀) = Equiv.refl _ := by
  rw [pathOrientationTransport_def, Path.Homotopic.Quotient.mk_refl,
    quotientOrientationTransport_refl]

@[simp]
theorem pathOrientationTransport_symm {T₀ T₁ : {T : E →L[ℝ] F // T.IsFredholm}} (γ : Path T₀ T₁) :
    pathOrientationTransport γ.symm = (pathOrientationTransport γ).symm := by
  rw [pathOrientationTransport_def, Path.Homotopic.Quotient.mk_symm,
    ← quotientOrientationTransport_symm, pathOrientationTransport_def]

/-- Concatenation law for orientation transport along continuous paths of Fredholm operators. -/
theorem pathOrientationTransport_trans {T₀ T₁ T₂ : {T : E →L[ℝ] F // T.IsFredholm}}
    (γ₁ : Path T₀ T₁) (γ₂ : Path T₁ T₂) :
    pathOrientationTransport (γ₁.trans γ₂) =
      (pathOrientationTransport γ₁).trans (pathOrientationTransport γ₂) := by
  rw [pathOrientationTransport_def, Path.Homotopic.Quotient.mk_trans,
    quotientOrientationTransport_trans, pathOrientationTransport_def, pathOrientationTransport_def]

/-- **Endpoint-relative homotopy invariance** for `Path`s in `{T : E →L[ℝ] F // T.IsFredholm}`. -/
theorem pathOrientationTransport_eq_of_homotopic {T₀ T₁ : {T : E →L[ℝ] F // T.IsFredholm}}
    {γ₀ γ₁ : Path T₀ T₁} (h : γ₀.Homotopic γ₁) :
    pathOrientationTransport γ₀ = pathOrientationTransport γ₁ := by
  rw [pathOrientationTransport_def, pathOrientationTransport_def, Path.Homotopic.Quotient.eq.2 h]

/-- Compatibility of `pathOrientationTransport` with `Path.cast` along endpoint equalities. -/
theorem pathOrientationTransport_cast {S₀ S₁ T₀ T₁ : {T : E →L[ℝ] F // T.IsFredholm}}
    (γ : Path S₀ S₁) (h₀ : T₀ = S₀) (h₁ : T₁ = S₁)
    (o : Module.Ray ℝ (T₀.1 : E →ₗ[ℝ] F).detLine) :
    pathOrientationTransport (γ.cast h₀ h₁) o =
      Module.Ray.map (LinearMap.detLineOfEq
          (congrArg (fun x : {T : E →L[ℝ] F // T.IsFredholm} ↦ (x.1 : E →ₗ[ℝ] F)) h₁.symm))
        (pathOrientationTransport γ
          (Module.Ray.map (LinearMap.detLineOfEq
            (congrArg (fun x : {T : E →L[ℝ] F // T.IsFredholm} ↦ (x.1 : E →ₗ[ℝ] F)) h₀)) o)) := by
  subst h₀
  subst h₁
  simp

/-- **Agreement of covering monodromy and coherent-family transport.** For a family
`T : ℝ → {T : E →L[ℝ] F // T.IsFredholm}` continuous on `[0, 1]`, the covering-monodromy transport
along its restriction to `unitInterval` coincides with `TauCeti.detLineOrientationTransport` from
`0` to `1`. -/
theorem pathOrientationTransport_of_continuousOn {T : ℝ → {T : E →L[ℝ] F // T.IsFredholm}}
    (hT : ContinuousOn T (Icc 0 1)) (hTu : ContinuousOn (fun t ↦ (T t).1) (uIcc 0 1))
    (hFu : ∀ t ∈ uIcc (0 : ℝ) 1, ((T t).1).IsFredholm)
    (o : Module.Ray ℝ ((T 0).1 : E →ₗ[ℝ] F).detLine) :
    pathOrientationTransport ⟨⟨fun t : unitInterval ↦ T t.1,
        hT.comp_continuous continuous_subtype_val fun t ↦ t.2⟩, rfl, rfl⟩ o =
      detLineOrientationTransport (T := fun t ↦ (T t).1) 0 1 hTu hFu o := by
  induction o using Module.Ray.ind with | h v₀ hv₀ =>
  obtain ⟨v, rfl, hv⟩ := exists_isDetLineCoherentOn_Icc hTu hFu left_mem_uIcc hv₀
  have hcov := (isDetLineCoherentOn_iff_continuous_orientationCoverMk (ι := Fin 1) hTu hFu).1 hv
  rcases hcov with ⟨hv_ne, hg⟩
  let g_sub : uIcc (0 : ℝ) 1 → VectorBundleOrientationCover ℝ (FredholmDetLine ℝ E F) (Fin 1) :=
    fun x ↦ orientationCoverMk (Fin 1) ⟨(T x.1).1, hFu x.1 x.2⟩
      (rayOfNeZero ℝ (v x.1) (hv_ne x.1 x.2))
  let ιI : unitInterval → uIcc (0 : ℝ) 1 :=
    fun t ↦ ⟨t.1, by simpa only [uIcc_of_le (zero_le_one' ℝ)] using t.2⟩
  have hιI : Continuous ιI := continuous_subtype_val.subtype_mk _
  let Γ : C(unitInterval, VectorBundleOrientationCover ℝ (FredholmDetLine ℝ E F) (Fin 1)) :=
    ⟨g_sub ∘ ιI, hg.comp hιI⟩
  let γ : Path (T 0) (T 1) :=
    ⟨⟨fun t : unitInterval ↦ T t.1, hT.comp_continuous continuous_subtype_val fun t ↦ t.2⟩,
      rfl, rfl⟩
  have hpΓ : (VectorBundleOrientationCover.proj :
      VectorBundleOrientationCover ℝ (FredholmDetLine ℝ E F) (Fin 1) → _) ∘ ⇑Γ = ⇑γ :=
    funext fun t ↦ (proj_orientationCoverMk _ _).trans (Subtype.ext rfl)
  have hι0 : ιI 0 = ⟨0, left_mem_uIcc⟩ := Subtype.ext rfl
  have hι1 : ιI 1 = ⟨1, right_mem_uIcc⟩ := Subtype.ext rfl
  have hΓ0 : Γ 0 = ((orientationCoverFiberEquiv (Fin 1) (T 0)).symm
      (rayOfNeZero ℝ (v 0) hv₀)).1 := by
    refine (congrArg g_sub hι0).trans ?_
    rw [orientationCoverFiberEquiv_symm_apply]
  have hΓ1_eq : Γ 1 = orientationCoverMk (Fin 1) (T 1)
      (rayOfNeZero ℝ (v 1) (hv_ne 1 right_mem_uIcc)) :=
    congrArg g_sub hι1
  have hmon : (isCoveringMap_orientationCover_proj (E := E) (F := F) (ι := Fin 1)).monodromy
      (.mk γ) ((orientationCoverFiberEquiv (Fin 1) (T 0)).symm (rayOfNeZero ℝ (v 0) hv₀)) =
        ⟨orientationCoverMk (Fin 1) (T 1) (rayOfNeZero ℝ (v 1) (hv_ne 1 right_mem_uIcc)),
          proj_orientationCoverMk (T 1) _⟩ :=
    Subtype.ext (((isCoveringMap_orientationCover_proj (E := E) (F := F)
      (ι := Fin 1)).monodromy_eq_apply_one hpΓ hΓ0).trans hΓ1_eq)
  have hpot : pathOrientationTransport γ (rayOfNeZero ℝ (v 0) hv₀) =
      orientationCoverFiberEquiv (Fin 1) (T 1)
        ((isCoveringMap_orientationCover_proj (E := E) (F := F) (ι := Fin 1)).monodromy
          (.mk γ) ((orientationCoverFiberEquiv (Fin 1) (T 0)).symm (rayOfNeZero ℝ (v 0) hv₀))) :=
    rfl
  exact hpot.trans ((congrArg (orientationCoverFiberEquiv (Fin 1) (T 1)) hmon).trans
    ((orientationCoverFiberEquiv_mk (T 1) _).trans
      (detLineOrientationTransport_rayOfNeZero hTu hFu hv).symm))

/-- **Bridge between `pathOrientationTransport` and `detLineOrientationTransport`.** For any path
`γ : Path T₀ T₁` in `{T : E →L[ℝ] F // T.IsFredholm}`, covering-monodromy orientation transport
along `γ` agrees with `TauCeti.detLineOrientationTransport` along `γ.extend` from `0` to `1`. -/
theorem pathOrientationTransport_apply {T₀ T₁ : {T : E →L[ℝ] F // T.IsFredholm}}
    (γ : Path T₀ T₁) (o : Module.Ray ℝ (T₀.1 : E →ₗ[ℝ] F).detLine) :
    pathOrientationTransport γ o =
      Module.Ray.map (LinearMap.detLineOfEq
          (congrArg (fun x : {T : E →L[ℝ] F // T.IsFredholm} ↦ (x.1 : E →ₗ[ℝ] F)) γ.extend_one))
        (detLineOrientationTransport (T := fun t ↦ (γ.extend t).1) 0 1
          (continuous_subtype_val.comp γ.continuous_extend).continuousOn
          (fun t _ ↦ (γ.extend t).2)
          (Module.Ray.map (LinearMap.detLineOfEq
            (congrArg (fun x : {T : E →L[ℝ] F // T.IsFredholm} ↦ (x.1 : E →ₗ[ℝ] F))
              γ.extend_zero.symm)) o)) := by
  let γ' : Path (γ.extend 0) (γ.extend 1) :=
    ⟨⟨fun t : unitInterval ↦ γ.extend t.1,
      γ.continuous_extend.continuousOn.comp_continuous continuous_subtype_val fun t ↦ t.2⟩,
      rfl, rfl⟩
  have hγ : γ = γ'.cast γ.extend_zero.symm γ.extend_one.symm :=
    Path.ext (funext fun t ↦ (γ.extend_extends' t).symm)
  exact (congrFun (congrArg DFunLike.coe (congrArg pathOrientationTransport hγ)) o).trans
    ((pathOrientationTransport_cast γ' γ.extend_zero.symm γ.extend_one.symm o).trans
      (congrArg _ (pathOrientationTransport_of_continuousOn γ.continuous_extend.continuousOn
        (continuous_subtype_val.comp γ.continuous_extend).continuousOn
        (fun t _ ↦ (γ.extend t).2) _)))

@[simp]
theorem pathOrientationTransport_neg {T₀ T₁ : {T : E →L[ℝ] F // T.IsFredholm}}
    (γ : Path T₀ T₁) (o : Module.Ray ℝ (T₀.1 : E →ₗ[ℝ] F).detLine) :
    pathOrientationTransport γ (-o) = -pathOrientationTransport γ o := by
  let h0 := congrArg (fun x : {T : E →L[ℝ] F // T.IsFredholm} ↦ (x.1 : E →ₗ[ℝ] F))
    γ.extend_zero.symm
  let h1 := congrArg (fun x : {T : E →L[ℝ] F // T.IsFredholm} ↦ (x.1 : E →ₗ[ℝ] F)) γ.extend_one
  have step1 := congrArg (Module.Ray.map (LinearMap.detLineOfEq h1))
    (congrArg (detLineOrientationTransport (T := fun t ↦ (γ.extend t).1) 0 1
      (continuous_subtype_val.comp γ.continuous_extend).continuousOn (fun t _ ↦ (γ.extend t).2))
      (LinearMap.ray_map_detLineOfEq_neg h0 o))
  have step2 := congrArg (Module.Ray.map (LinearMap.detLineOfEq h1))
    (detLineOrientationTransport_neg
      (continuous_subtype_val.comp γ.continuous_extend).continuousOn (fun t _ ↦ (γ.extend t).2)
      (Module.Ray.map (LinearMap.detLineOfEq h0) o))
  have step3 := LinearMap.ray_map_detLineOfEq_neg h1
    (detLineOrientationTransport (T := fun t ↦ (γ.extend t).1) 0 1
      (continuous_subtype_val.comp γ.continuous_extend).continuousOn (fun t _ ↦ (γ.extend t).2)
      (Module.Ray.map (LinearMap.detLineOfEq h0) o))
  exact (pathOrientationTransport_apply γ (-o)).trans
    (step1.trans (step2.trans (step3.trans
      (congrArg Neg.neg (pathOrientationTransport_apply γ o).symm))))

@[simp]
theorem quotientOrientationTransport_neg {T₀ T₁ : {T : E →L[ℝ] F // T.IsFredholm}}
    (γ : Path.Homotopic.Quotient T₀ T₁) (o : Module.Ray ℝ (T₀.1 : E →ₗ[ℝ] F).detLine) :
    quotientOrientationTransport γ (-o) = -quotientOrientationTransport γ o := by
  obtain ⟨γ⟩ := γ
  exact pathOrientationTransport_neg γ o

/-- Around any loop homotopy class based at `T₀`, orientation transport either fixes every ray or
reverses every ray. -/
theorem quotientOrientationTransport_loop_eq_refl_or_neg {T₀ : {T : E →L[ℝ] F // T.IsFredholm}}
    (γ : Path.Homotopic.Quotient T₀ T₀) :
    (∀ r, quotientOrientationTransport γ r = r) ∨
      (∀ r, quotientOrientationTransport γ r = -r) := by
  have : Nontrivial (T₀.1 : E →ₗ[ℝ] F).detLine :=
    Module.nontrivial_of_finrank_eq_succ (LinearMap.finrank_detLine _)
  obtain ⟨v₀, hv₀⟩ := exists_ne (0 : (T₀.1 : E →ₗ[ℝ] F).detLine)
  let r₀ := rayOfNeZero ℝ v₀ hv₀
  rcases detLine_ray_eq_or_eq_neg (quotientOrientationTransport γ r₀) r₀ with h₀ | h₀
  · refine Or.inl fun r ↦ ?_
    rcases detLine_ray_eq_or_eq_neg r r₀ with rfl | rfl
    · exact h₀
    · rw [quotientOrientationTransport_neg, h₀]
  · refine Or.inr fun r ↦ ?_
    rcases detLine_ray_eq_or_eq_neg r r₀ with rfl | rfl
    · exact h₀
    · rw [quotientOrientationTransport_neg, h₀]

private def loopSign (T₀ : {T : E →L[ℝ] F // T.IsFredholm})
    (γ : Path.Homotopic.Quotient T₀ T₀) : ℤˣ := by
  classical
  exact if quotientOrientationTransport γ = Equiv.refl _ then 1 else -1

private theorem loopSign_refl (T₀ : {T : E →L[ℝ] F // T.IsFredholm}) :
    loopSign T₀ (.refl T₀) = 1 := by
  classical
  unfold loopSign
  split_ifs with h
  · rfl
  · exact absurd (quotientOrientationTransport_refl T₀) h

private theorem loopSign_eq_one_iff {T₀ : {T : E →L[ℝ] F // T.IsFredholm}}
    (γ : Path.Homotopic.Quotient T₀ T₀) :
    loopSign T₀ γ = 1 ↔ quotientOrientationTransport γ = Equiv.refl _ := by
  classical
  unfold loopSign
  split_ifs with h
  · exact ⟨fun _ ↦ h, fun _ ↦ rfl⟩
  · exact ⟨fun h1 ↦ absurd h1 (by decide), fun h' ↦ absurd h' h⟩

private theorem loopSign_eq_neg_one_iff {T₀ : {T : E →L[ℝ] F // T.IsFredholm}}
    (γ : Path.Homotopic.Quotient T₀ T₀) :
    loopSign T₀ γ = -1 ↔ ∀ r, quotientOrientationTransport γ r = -r := by
  classical
  have : Nontrivial (T₀.1 : E →ₗ[ℝ] F).detLine :=
    Module.nontrivial_of_finrank_eq_succ (LinearMap.finrank_detLine _)
  obtain ⟨v₀, hv₀⟩ := exists_ne (0 : (T₀.1 : E →ₗ[ℝ] F).detLine)
  let r₀ := rayOfNeZero ℝ v₀ hv₀
  unfold loopSign
  split_ifs with h'
  · exact ⟨fun h1 ↦ absurd h1 (by decide), fun hneg ↦ (detLine_ray_ne_neg_self r₀
      ((congrFun (congrArg DFunLike.coe h') r₀).symm.trans (hneg r₀))).elim⟩
  · rcases quotientOrientationTransport_loop_eq_refl_or_neg γ with h | h
    · exact absurd (Equiv.ext h) h'
    · exact ⟨fun _ ↦ h, fun _ ↦ rfl⟩

private theorem loopSign_trans {T₀ : {T : E →L[ℝ] F // T.IsFredholm}}
    (γ₁ γ₂ : Path.Homotopic.Quotient T₀ T₀) :
    loopSign T₀ (γ₁.trans γ₂) = loopSign T₀ γ₂ * loopSign T₀ γ₁ := by
  have htr (r : Module.Ray ℝ (T₀.1 : E →ₗ[ℝ] F).detLine) :
      quotientOrientationTransport (γ₁.trans γ₂) r =
        quotientOrientationTransport γ₂ (quotientOrientationTransport γ₁ r) :=
    congrFun (congrArg DFunLike.coe (quotientOrientationTransport_trans γ₁ γ₂)) r
  rcases quotientOrientationTransport_loop_eq_refl_or_neg γ₁ with h₁ | h₁ <;>
    rcases quotientOrientationTransport_loop_eq_refl_or_neg γ₂ with h₂ | h₂
  · have h₁₂ : quotientOrientationTransport (γ₁.trans γ₂) = Equiv.refl _ :=
      Equiv.ext fun r ↦ (htr r).trans ((congrArg _ (h₁ r)).trans (h₂ r))
    rw [(loopSign_eq_one_iff _).2 h₁₂, (loopSign_eq_one_iff _).2 (Equiv.ext h₂),
      (loopSign_eq_one_iff _).2 (Equiv.ext h₁), mul_one]
  · have h₁₂ : ∀ r, quotientOrientationTransport (γ₁.trans γ₂) r = -r :=
      fun r ↦ (htr r).trans ((congrArg _ (h₁ r)).trans (h₂ r))
    rw [(loopSign_eq_neg_one_iff _).2 h₁₂, (loopSign_eq_neg_one_iff _).2 h₂,
      (loopSign_eq_one_iff _).2 (Equiv.ext h₁), mul_one]
  · have h₁₂ : ∀ r, quotientOrientationTransport (γ₁.trans γ₂) r = -r :=
      fun r ↦ (htr r).trans ((congrArg _ (h₁ r)).trans (h₂ (-r)))
    rw [(loopSign_eq_neg_one_iff _).2 h₁₂, (loopSign_eq_one_iff _).2 (Equiv.ext h₂),
      (loopSign_eq_neg_one_iff _).2 h₁, one_mul]
  · have h₁₂ : quotientOrientationTransport (γ₁.trans γ₂) = Equiv.refl _ :=
      Equiv.ext fun r ↦ (htr r).trans ((congrArg _ (h₁ r)).trans ((h₂ (-r)).trans (neg_neg r)))
    rw [(loopSign_eq_one_iff _).2 h₁₂, (loopSign_eq_neg_one_iff _).2 h₂,
      (loopSign_eq_neg_one_iff _).2 h₁]
    decide

/-- **Orientation monodromy sign character.** Homomorphism from the fundamental group of
`{T : E →L[ℝ] F // T.IsFredholm}` at `T₀` to `ℤˣ` taking value `1` on orientation-preserving loops
and `-1` on orientation-reversing loops. -/
def orientationMonodromySign (T₀ : {T : E →L[ℝ] F // T.IsFredholm}) :
    FundamentalGroup {T : E →L[ℝ] F // T.IsFredholm} T₀ →* ℤˣ where
  toFun γ := loopSign T₀ γ.toPath
  map_one' := loopSign_refl T₀
  map_mul' p q := loopSign_trans q.toPath p.toPath

/-- A loop class based at `T₀` has orientation monodromy sign `1` if and only if its orientation
transport is the identity. -/
theorem orientationMonodromySign_eq_one_iff {T₀ : {T : E →L[ℝ] F // T.IsFredholm}}
    (γ : FundamentalGroup {T : E →L[ℝ] F // T.IsFredholm} T₀) :
    orientationMonodromySign T₀ γ = 1 ↔ quotientOrientationTransport γ.toPath = Equiv.refl _ :=
  loopSign_eq_one_iff γ.toPath

/-- A loop class based at `T₀` has orientation monodromy sign `-1` if and only if its orientation
transport reverses every determinant-line orientation. -/
theorem orientationMonodromySign_eq_neg_one_iff {T₀ : {T : E →L[ℝ] F // T.IsFredholm}}
    (γ : FundamentalGroup {T : E →L[ℝ] F // T.IsFredholm} T₀) :
    orientationMonodromySign T₀ γ = -1 ↔
      ∀ r, quotientOrientationTransport γ.toPath r = -r :=
  loopSign_eq_neg_one_iff γ.toPath

end FredholmDetLine

end TauCeti

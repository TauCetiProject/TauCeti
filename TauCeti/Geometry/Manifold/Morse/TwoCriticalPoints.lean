/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Geometry.Manifold.Morse.CriticalPoints
import TauCeti.Geometry.Manifold.ContMDiff.Parametrization
import TauCeti.Geometry.Manifold.Morse.Deformation

/-!
# Two Euclidean open sets covering a manifold with two critical points

Let `f` be a smooth function on a compact boundaryless manifold `M` of dimension `m`, with
exactly two critical points. Then `M` is the union of two open sets, each homeomorphic to `ℝᵐ`
(`TauCeti.exists_twoEuclideanOpenCover_of_two_criticalPoints`). The critical points may be
degenerate: no Hessian condition is assumed, so the Morse lemma is not available and the proof
uses only the descending flow of `f`.

When `f` is not constant, its two critical points are its unique minimum `x₀` and its unique
maximum `x₁`, and every value strictly between `f x₀` and `f x₁` is regular. Choose open
neighbourhoods `B` of `x₀` and `V` of `x₁`, each homeomorphic to `ℝᵐ`. Since `x₀` is the unique
minimum, a whole sublevel `{f ≤ a}` with `a > f x₀` lies in `B`; since `x₁` is the unique maximum,
the compact set `M \ V` lies in a sublevel `{f ≤ b}` with `b < f x₁`. The band `f⁻¹[a, b]` is
compact and free of critical points, so a diffeomorphism `Φ` of `M` carries `{f ≤ b}` onto
`{f ≤ a}` (`TauCeti.exists_diffeomorph_sublevel`). Hence `Φ` maps `M \ V` into `B`, and the open
sets `Φ⁻¹(B) ≃ₜ B` and `V` cover `M`. When `f` is constant, every point is critical, so `M`
consists of the two critical points, and their coordinate neighbourhoods cover it.

By Brown's generalized Schoenflies theorem, a compact Hausdorff space covered by two open sets
homeomorphic to `ℝᵐ`, `m > 0`, is homeomorphic to the sphere `Sᵐ` (Milnor 1959, Corollary 1;
Rosen 1960, Lemma 1). Such a cover is therefore the analytic input of Reeb's sphere theorem for
functions with two possibly degenerate critical points; for Morse functions that theorem is
`TauCeti.IsMorse.nonempty_homeomorph_sphere_of_totalCriticalCount_eq_two`.

## Main results

* `TauCeti.exists_diffeomorph_mem_of_two_criticalPoints`: a diffeomorphism of `M` carrying the
  complement of a neighbourhood of the maximum into a neighbourhood of the minimum.
* `TauCeti.exists_twoEuclideanOpenCover_of_two_criticalPoints`: the cover of `M` by two open sets
  homeomorphic to `ℝᵐ`.

## References

* J. Milnor, *Sommes de variétés différentiables et structures différentiables des sphères*,
  Bull. Soc. Math. France 87 (1959), 439–444, Theorem 1 and Corollary 1.
* R. H. Rosen, *A weak form of the star conjecture for manifolds*, Notices Amer. Math. Soc. 7
  (1960), abstract 570-28, p. 380, Lemma 1.
* M. Brown, *A proof of the generalized Schoenflies theorem*, Bull. Amer. Math. Soc. 66 (1960),
  74–76.
* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Theorem 3.1 and Remark 1 after Theorem 4.1.
-/

public section

open Filter Set Module
open scoped ContDiff Manifold

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
  {f : M → ℝ}

/-- **Pushing a manifold into a neighbourhood of the minimum.** Let `f` be a smooth function on a
compact manifold with minimum `x₀` and maximum `x₁`, where `f x₀ < f x₁`, and whose only critical
points are `x₀` and `x₁`. For any open neighbourhoods `B` of `x₀` and `V` of `x₁`, there is a
diffeomorphism of `M` carrying every point outside `V` into `B`. -/
theorem exists_diffeomorph_mem_of_two_criticalPoints (hf : ContMDiff I 𝓘(ℝ) ∞ f) {x₀ x₁ : M}
    (hx₀ : IsMinOn f univ x₀) (hx₁ : IsMaxOn f univ x₁) (hlt : f x₀ < f x₁)
    (hcrit : ∀ x ∈ criticalPoints I f, x = x₀ ∨ x = x₁) {B V : Set M} (hB : IsOpen B)
    (hx₀B : x₀ ∈ B) (hV : IsOpen V) (hx₁V : x₁ ∈ V) :
    ∃ Φ : M ≃ₘ⟮I, I⟯ M, ∀ x ∉ V, Φ x ∈ B := by
  have hfc : Continuous f := hf.continuous
  -- The minimum and the maximum are strict: another point attaining either value is critical.
  have hmin (y : M) (hy : y ≠ x₀) : f x₀ < f y :=
    (hx₀ (mem_univ y)).lt_of_ne fun h ↦ hy (hx₀.eq_of_le_of_two_criticalPoints hlt hcrit h.ge)
  have hmax (y : M) (hy : y ≠ x₁) : f y < f x₁ :=
    (hx₁ (mem_univ y)).lt_of_ne fun h ↦ hy (hx₁.eq_of_le_of_two_criticalPoints hlt hcrit h.ge)
  -- On the compact sets `M \ B` and `M \ V`, `f` stays away from its minimum and its maximum.
  obtain ⟨a', ha', ha'B⟩ := hB.isClosed_compl.isCompact.exists_forall_le' hfc.continuousOn
    fun y hy ↦ hmin y fun h ↦ hy (h ▸ hx₀B)
  obtain ⟨b', hb', hb'V⟩ := hV.isClosed_compl.isCompact.exists_forall_le' hfc.neg.continuousOn
    fun y hy ↦ neg_lt_neg (hmax y fun h ↦ hy (h ▸ hx₁V))
  -- A band `[a, b]` strictly between the two critical values, with `{f ≤ a} ⊆ B` and
  -- `M \ V ⊆ {f ≤ b}`.
  set c := (f x₀ + f x₁) / 2 with hc
  set a := min ((f x₀ + a') / 2) c
  set b := max (-b') c
  have hxa : f x₀ < a := lt_min (by linarith) (by linarith)
  have haa' : a < a' := (min_le_left _ _).trans_lt (by linarith)
  have hbx : b < f x₁ := max_lt (by linarith) (by linarith)
  have hab : a ≤ b := (min_le_right _ _).trans (le_max_right _ _)
  obtain ⟨Φ, hΦ⟩ := exists_diffeomorph_sublevel hf hab (isClosed_Icc.preimage hfc).isCompact
    fun x hax hxb h0 ↦ by
      rcases hcrit x (mem_criticalPoints_iff_mfderiv_eq_zero.2 h0) with rfl | rfl <;> linarith
  refine ⟨Φ, fun x hx ↦ by_contra fun hΦB ↦ ?_⟩
  have h₁ : a' ≤ f (Φ x) := ha'B _ hΦB
  have h₂ : f (Φ x) ≤ a := (hΦ x).1.2 ((le_neg.1 (hb'V x hx)).trans (le_max_left _ _))
  linarith

/-- **Two Euclidean open sets covering a manifold with two critical points.** If a smooth function
on a compact boundaryless manifold `M` modelled on a real vector space of dimension `m` has exactly
two critical points, then `M` is the union of two open sets, each homeomorphic to `ℝᵐ`. The
critical points may be degenerate. No dimension or connectedness hypothesis is needed; in
dimension `0` the manifold consists of the two critical points. -/
theorem exists_twoEuclideanOpenCover_of_two_criticalPoints (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (h2 : totalCriticalCount I f = 2) :
    ∃ U V : Set M, IsOpen U ∧ IsOpen V ∧ U ∪ V = univ ∧
      Nonempty (U ≃ₜ EuclideanSpace ℝ (Fin (finrank ℝ E))) ∧
      Nonempty (V ≃ₜ EuclideanSpace ℝ (Fin (finrank ℝ E))) := by
  obtain ⟨x₀, x₁, hx₀, hx₁, -, hcrit, hlt | ⟨-, huniv⟩⟩ :=
    exists_isMinOn_isMaxOn_of_totalCriticalCount_eq_two hf.continuous h2
  · -- The critical points are the minimum `x₀` and the maximum `x₁`.
    obtain ⟨B, hB, hx₀B, ⟨eB⟩⟩ := exists_isOpen_mem_nonempty_homeomorph_euclideanSpace I x₀
    obtain ⟨V, hV, hx₁V, hVe⟩ := exists_isOpen_mem_nonempty_homeomorph_euclideanSpace I x₁
    obtain ⟨Φ, hΦ⟩ := exists_diffeomorph_mem_of_two_criticalPoints hf hx₀ hx₁ hlt
      (fun x hx ↦ by rwa [hcrit] at hx) hB hx₀B hV hx₁V
    refine ⟨Φ ⁻¹' B, V, hB.preimage Φ.continuous, hV,
      eq_univ_of_forall fun x ↦ (em (x ∈ V)).elim Or.inr fun hx ↦ Or.inl (hΦ x hx),
      ⟨(Φ.toHomeomorph.sets (by rw [Diffeomorph.coe_toHomeomorph])).trans eB⟩, hVe⟩
  -- A constant function: every point is critical, so `M = {x₀, x₁}`.
  obtain ⟨U, hU, hx₀U, hUe⟩ := exists_isOpen_mem_nonempty_homeomorph_euclideanSpace I x₀
  obtain ⟨V, hV, hx₁V, hVe⟩ := exists_isOpen_mem_nonempty_homeomorph_euclideanSpace I x₁
  refine ⟨U, V, hU, hV, eq_univ_of_forall fun x ↦ ?_, hUe, hVe⟩
  have hx : x ∈ criticalPoints I f := huniv ▸ mem_univ x
  rw [hcrit, mem_insert_iff, mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  exacts [Or.inl hx₀U, Or.inr hx₁V]

end TauCeti

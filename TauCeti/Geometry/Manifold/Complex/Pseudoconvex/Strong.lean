/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.LeviForm
public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Strong
public import TauCeti.Geometry.Manifold.ExtChartAt

/-!
# Pseudoconvexity in the strong Whitney topology

Strong `q`-pseudoconvexity everywhere is open in the strong Whitney topology on real-valued
`C^r` functions, for every `r ≥ 2`. More precisely,
`TauCeti.exists_strongCkControl_isManifoldStronglyPseudoconvexAt` constructs a control of order
exactly two whose ball preserves the positivity. The compact coordinate sets cover the manifold,
and their tolerances may tend to zero at infinity. Thus the control can be supplied directly to
approximation theorems formulated with strong Whitney balls.

The proof tests the second coordinate jet against the open set of bilinear forms positive on a
complex subspace of codimension at most `q`. Compactness gives a uniform tolerance on each
member of a locally finite compact chart cover; holomorphic chart invariance then transports the
test back to the manifold. Strict plurisubharmonicity is the case `q = 0`.

## References

* R. Hain, *Notes on the Morse theory of complex manifolds*, Section 2.
* M. Hirsch, *Differential Topology*, Chapter 2, Section 1 (strong Whitney topology).
-/

public section

open Set Topology ContMDiffMap
open scoped Manifold ContDiff TauCeti.ManifoldStrongWhitney

universe u

namespace TauCeti

variable {E : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [TopologicalSpace M] [ChartedSpace E M]
  {r : ℕ∞ω} [IsManifold 𝓘(ℂ, E) r M]

local instance : IsManifold 𝓘(ℝ, E) r M :=
  IsManifold.restrictScalars ℝ (inferInstance : IsManifold 𝓘(ℂ, E) r M)

/-- Strong `q`-pseudoconvexity at a point is detected by the second chart jet: there is an open
set `V` of second-order jets such that, in every chart, the second jet of `g` at a point of the
chart target lies in `V` exactly when `g` is strongly `q`-pseudoconvex at the corresponding
point of the manifold. -/
theorem exists_isOpen_chartIteratedFDeriv_mem_iff_isManifoldStronglyPseudoconvexAt
    (hr : 2 ≤ r) (q : ℕ) :
    ∃ V : Set (E [×2]→L[ℝ] ℝ), IsOpen V ∧
      ∀ (g : C^r⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯) (a : M) (z : (extChartAt 𝓘(ℝ, E) a).target),
        chartIteratedFDeriv g a 2 hr z ∈ V ↔
          IsManifoldStronglyPseudoconvexAt E q g ((extChartAt 𝓘(ℝ, E) a).symm z) := by
  have : IsManifold 𝓘(ℂ, E) 2 M := IsManifold.of_le hr
  let curry : (E [×2]→L[ℝ] ℝ) →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ :=
    (ContinuousLinearMap.compL ℝ E (E [×1]→L[ℝ] ℝ) (E →L[ℝ] ℝ)
      (continuousMultilinearCurryFin1 ℝ E ℝ).toContinuousLinearEquiv.toContinuousLinearMap).comp
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 2 ↦ E) ℝ
        ).toContinuousLinearEquiv.toContinuousLinearMap
  let V : Set (E [×2]→L[ℝ] ℝ) := curry ⁻¹'
    {B : E →L[ℝ] E →L[ℝ] ℝ | ∃ P : Submodule ℂ E,
      Module.finrank ℂ E ≤ Module.finrank ℂ P + q ∧
        ∀ v ∈ P, v ≠ 0 → 0 < (B.toBilinForm.leviForm v v).re}
  have hV : IsOpen V :=
    (isOpen_setOf_re_leviForm_posOnSubspace q).preimage curry.continuous
  -- Currying the second chart jet gives the ordinary coordinate Hessian on the chart target.
  have hjet (g : C^r⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯) (a : M)
      (z : (extChartAt 𝓘(ℝ, E) a).target) :
      curry (chartIteratedFDeriv g a 2 hr z) =
        fderiv ℝ (fderiv ℝ (g ∘ (chartAt E a).symm)) z := by
    rw [chartIteratedFDeriv_self_target_apply,
      iteratedFDerivWithin_of_isOpen 2 (isOpen_extChartAt_target a) z.2]
    ext v w
    simp [curry, iteratedFDeriv_two_apply]
  have htest (g : C^r⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯) (a : M)
      (z : (extChartAt 𝓘(ℝ, E) a).target) :
      chartIteratedFDeriv g a 2 hr z ∈ V ↔
        IsManifoldStronglyPseudoconvexAt E q g ((extChartAt 𝓘(ℝ, E) a).symm z) := by
    rw [Set.mem_preimage, hjet, Set.mem_ofPred_eq, ← leviForm_def,
      ← isStronglyPseudoconvexAt_iff]
    have hz : z.1 ∈ (chartAt E a).target := by simpa using z.2
    have hx := (chartAt E a).map_target hz
    simpa only [extChartAt_coe_symm, modelWithCornersSelf_coe_symm, Function.comp_id,
      (chartAt E a).right_inv hz] using
      (isManifoldStronglyPseudoconvexAt_iff_of_mem_maximalAtlas
        (IsManifold.chart_mem_maximalAtlas a) hx (g.contMDiff.of_le hr).contMDiffAt).symm
  exact ⟨V, hV, htest⟩

/-- A globally strongly `q`-pseudoconvex `C^r` function, `r ≥ 2`, has a strong Whitney ball of
order exactly two consisting of globally strongly `q`-pseudoconvex functions. The control uses a
locally finite compact chart cover and separate positive tolerances on its members. -/
theorem exists_strongCkControl_isManifoldStronglyPseudoconvexAt [T2Space M]
    [SigmaCompactSpace M] (hr : 2 ≤ r) (q : ℕ)
    (f : C^r⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯)
    (hf : ∀ x, IsManifoldStronglyPseudoconvexAt E q f x) :
    ∃ c : StrongCkControl 𝓘(ℝ, E) M r, c.order = 2 ∧
      ∀ g ∈ c.ball f, ∀ x, IsManifoldStronglyPseudoconvexAt E q g x := by
  obtain ⟨V, hV, htest⟩ :=
    exists_isOpen_chartIteratedFDeriv_mem_iff_isManifoldStronglyPseudoconvexAt (E := E) (M := M)
      hr q
  obtain ⟨α, a, K, hlf, hcover⟩ :=
    exists_locallyFinite_compact_extChartAt_cover (I := 𝓘(ℝ, E)) (M := M)
  have hmaps (i : α) : MapsTo (chartIteratedFDeriv f (a i) 2 hr) (K i) V :=
    fun z _ ↦ (htest f (a i) z).mpr (hf _)
  -- Each compact jet test contains a seminorm ball; assemble their separate tolerances.
  have htolerance (i : α) : ∃ (ε : ℝ) (hε : 0 < ε),
      (StrongCkControl.single (a i) (K i) 2 hr hε).ball f ⊆
        chartJetSet (a i) (0 : ℝ) 2 (K i) V :=
    exists_ball_single_subset_chartJetSet (a i) (0 : ℝ) hr (K i).isCompact hV
      (by rw [chartJetSet_self_target (a i) (0 : ℝ) 2 hr]; exact hmaps i)
  choose ε hε hsub using htolerance
  let c : StrongCkControl 𝓘(ℝ, E) M r :=
    { ι := α, center := a, compact := K, order := 2, order_le := hr,
      tolerance := ε, tolerance_pos := hε, locallyFinite := hlf }
  refine ⟨c, rfl, fun g hg x ↦ ?_⟩
  obtain ⟨i, z, hz, hx⟩ := Set.mem_iUnion.mp (hcover.symm ▸ Set.mem_univ x)
  obtain ⟨z, hz, rfl⟩ := hz
  -- The global control implies the single-chart test at a chart containing the chosen point.
  have hsingle : g ∈ (StrongCkControl.single (a i) (K i) 2 hr (hε i)).ball f := by
    rw [StrongCkControl.ball_single, Seminorm.mem_ball]
    exact StrongCkControl.mem_ball.mp hg i
  have hmem := hsub i hsingle
  rw [chartJetSet_self_target (a i) (0 : ℝ) 2 hr] at hmem
  rw [← hx]
  exact (htest g (a i) z).mp (hmem hz)

/-- Everywhere strong `q`-pseudoconvexity is open in the strong Whitney topology, with no
uniform positivity bound at infinity. -/
theorem isOpen_setOf_forall_isManifoldStronglyPseudoconvexAt [T2Space M]
    [SigmaCompactSpace M] (hr : 2 ≤ r) (q : ℕ) :
    IsOpen {f : C^r⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯ |
      ∀ x, IsManifoldStronglyPseudoconvexAt E q f x} := by
  refine isOpen_iff_mem_nhds.mpr fun f hf ↦ ?_
  obtain ⟨c, _, hc⟩ := exists_strongCkControl_isManifoldStronglyPseudoconvexAt hr q f hf
  exact mem_nhds_manifoldStrongWhitney_iff.mpr ⟨c, hc⟩

/-- Everywhere strict plurisubharmonicity is open in the strong Whitney topology. -/
theorem isOpen_setOf_forall_isManifoldStrictlyPlurisubharmonicAt [T2Space M]
    [SigmaCompactSpace M] (hr : 2 ≤ r) :
    IsOpen {f : C^r⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯ |
      ∀ x, IsManifoldStrictlyPlurisubharmonicAt E f x} := by
  simpa only [isManifoldStronglyPseudoconvexAt_zero_iff] using
    isOpen_setOf_forall_isManifoldStronglyPseudoconvexAt (E := E) (M := M) hr 0

end TauCeti

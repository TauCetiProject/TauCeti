/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import TauCeti.Geometry.Manifold.GroupAction.Linearization

import TauCeti.Analysis.Calculus.FDeriv.Comp
import TauCeti.Analysis.Calculus.GroupAction.FaceKernel
import TauCeti.Analysis.Calculus.GroupAction.Submersion
import TauCeti.Analysis.Calculus.TangentCone.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.MFDeriv.Submersion

/-!
# Faces detect the ineffective kernel of a finite smooth action

Let a finite group `G` act by `C^n` maps, `1 ≤ n`, on a manifold `M` without boundary, modelled
on a real Banach space, and let `x` be a common fixed point. Let `ρ : ι → M → ℝ` be finitely many
locally invariant functions, `C¹` at `x`, whose differentials at `x` are linearly independent for
the labels active at `x`, that is, those with `ρ i x = 0`. For a set `s` of labels, the face
`{y | (∀ i, 0 ≤ ρ i y) ∧ ∀ i ∈ s, ρ i y = 0}` is a corner of the domain cut out by the
inequalities `0 ≤ ρ i`.

If `x` lies on this face, an element of `G` acts as the identity near `x` exactly when it acts as
the identity on the face near `x` (`TauCeti.eventually_nhdsWithin_face_smul_eq_iff`). So the
germ kernel of the action at `x`, the subgroup of elements acting as the identity near `x`, is
also the germ kernel of the action on every face through `x`, including faces of codimension
greater than one and at corners where further labels are active. No faithfulness is assumed:
the statement concerns the actual group elements, including those acting trivially everywhere.

Preserving each `ρ i` individually is essential. A reflection fixing a hypersurface pointwise is
not the identity near it; it does not preserve a defining function of that hypersurface, it
negates it.

The proof combines three local results. Smooth Bochner linearization gives a chart at `x` in which
`G` acts linearly. Equivariant straightening of the active defining functions makes them the
linear coordinates of their derivative, so that near `x` the face is a convex cone in the kernel
of its normal coordinates, with nonempty interior there. Finally, an element of finite order
preserving linear normal coordinates and fixing such a cone near the origin is the identity near
the origin.

## Main results

* `TauCeti.exists_equivariant_straightened_chart`: invariant functions vanishing at `x` with
  linearly independent differentials are linear coordinates of a chart at `x` in which the action
  is linear.
* `TauCeti.eventually_nhdsWithin_face_smul_eq_iff`: an element acts as the identity near `x`
  exactly when it acts as the identity on a face through `x` near `x`.

## References

* S. Bochner, *Compact groups of differentiable transformations*, Ann. of Math. (2) 46
  (1945), 372–381.
* A. Adem, J. Leida and Y. Ruan, *Orbifolds and Stringy Topology*, Cambridge Tracts in
  Mathematics 171, Cambridge University Press, 2007, Chapter 1.
-/

public section

open Set Filter Topology
open scoped Manifold ContDiff

namespace TauCeti

variable {E H M G ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] {n : WithTop ℕ∞} [IsManifold I n M]
  [Group G] [Finite G] [MulAction G M] [Finite ι]

/-- **Equivariant straightened charts.** Let a finite group act by `C^n` maps, `1 ≤ n`, fixing
`x`, and let the functions `ρ i` vanish at `x`, be locally invariant and `C¹` at `x`, with
linearly independent differentials at `x`. Then some chart `χ` centred at `x`, with invariant
source, makes the action linear through a representation `σ` and the functions `ρ i` linear
coordinates: they are the components of a surjective continuous linear map `q`, which is
invariant under `σ`. -/
theorem exists_equivariant_straightened_chart
    (hsmooth : ∀ g : G, ContMDiff I I n fun y : M ↦ g • y) (hn : 1 ≤ n)
    {x : M} (hx : ∀ g : G, g • x = x) {ρ : ι → M → ℝ} (h0 : ∀ i, ρ i x = 0)
    (hρ : ∀ i, ContMDiffAt I 𝓘(ℝ) 1 (ρ i) x)
    (hinv : ∀ i (g : G), ∀ᶠ y in 𝓝 x, ρ i (g • y) = ρ i y)
    (hlin : LinearIndependent ℝ fun i ↦ mvfderiv I (ρ i) x) :
    ∃ (σ : ContRepresentation ℝ G E) (χ : OpenPartialHomeomorph M E) (q : E →L[ℝ] ι → ℝ),
      x ∈ χ.source ∧ χ x = 0 ∧
      (∀ g : G, ∀ z ∈ χ.source, g • z ∈ χ.source ∧ χ (g • z) = σ g (χ z)) ∧
      Function.Surjective q ∧ (∀ g : G, q.comp (σ g) = q) ∧
      ∀ z ∈ χ.source, ∀ i, q (χ z) i = ρ i z := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  have hn0 : n ≠ 0 := (zero_lt_one.trans_le hn).ne'
  -- Linearize the action in a smooth chart `e` centred at `x`.
  obtain ⟨σ, e, hxe, hex, hes, het, he, -⟩ :=
    exists_equivariant_contMDiff_chart (𝕜 := ℝ) hsmooth hn hx
  have h0t : (0 : E) ∈ e.target := hex ▸ e.map_source hxe
  have hsymm0 : e.symm 0 = x := by rw [← hex, e.left_inv hxe]
  have hsymm : ContMDiffAt 𝓘(ℝ, E) I 1 e.symm 0 :=
    (het.contMDiffAt (e.open_target.mem_nhds h0t)).of_le hn
  have hsymmT : Tendsto e.symm (𝓝 0) (𝓝 x) := hsymm0 ▸ e.continuousAt_symm h0t
  have hesmul (g : G) {v : E} (hv : v ∈ e.target) : e.symm (σ g v) = g • e.symm v := by
    obtain ⟨hmem, heq⟩ := he g _ (e.map_target hv)
    rw [← e.left_inv hmem, heq, e.right_inv hv]
  -- The defining functions read in the chart.
  let r : E → ι → ℝ := fun v i ↦ ρ i (e.symm v)
  have hr0 : r 0 = 0 := funext fun i ↦ by simp only [r, hsymm0, h0, Pi.zero_apply]
  have hrC : ContDiffAt ℝ 1 r 0 := contDiffAt_pi.mpr fun i ↦
    contMDiffAt_iff_contDiffAt.mp ((hρ i).comp_of_eq hsymm hsymm0)
  obtain ⟨U, hUsub, hU, h0U⟩ := mem_nhds_iff.mp (hrC.eventually (by simp))
  have hrU : ContDiffOn ℝ 1 r U := fun v hv ↦ (hUsub hv).contDiffWithinAt
  -- Its derivative is surjective, since `e.symm` is a local diffeomorphism at `0`.
  let q : E →L[ℝ] ι → ℝ := fderiv ℝ r 0
  have hd : HasFDerivAt r q 0 := (hrC.differentiableAt one_ne_zero).hasFDerivAt
  have hq : Function.Surjective q := by
    refine e.surjective_fderiv_pi_comp_symm hes het hn0 h0t (fun i ↦ ?_) ?_
    · rw [hsymm0]
      exact (hρ i).mdifferentiableAt one_ne_zero
    · rw [hsymm0]
      exact hlin
  -- Local invariance of the defining functions, read in the linear chart.
  have hinvr (g : G) : r ∘ σ g =ᶠ[𝓝 0] r := by
    filter_upwards [e.open_target.mem_nhds h0t,
      hsymmT.eventually (eventually_all.mpr fun i ↦ hinv i g)] with v hv hvinv
    funext i
    simp only [Function.comp_apply, r, hesmul g hv, hvinv i]
  have hqσ (g : G) : q.comp (σ g) = q :=
    hd.comp_eq_of_eventuallyEq (σ g).hasFDerivAt (map_zero _) (hinvr g)
  -- Straighten the defining functions equivariantly, and compose the charts.
  obtain ⟨e', h0e', he'0, -, -, -, -, hqe', -, he's, -⟩ :=
    σ.exists_equivariant_straightening hrU hU h0U le_rfl hr0 hd hq hinvr
  refine ⟨σ, e.trans e', q, ⟨hxe, by simpa [hex] using h0e'⟩, by simp [hex, he'0],
    fun g z hz ↦ ?_, hq, hqσ, fun z hz i ↦ ?_⟩
  · obtain ⟨hgz, hegz⟩ := he g z hz.1
    obtain ⟨hσz, he'σz⟩ := he's g _ hz.2
    refine ⟨⟨hgz, by simpa [hegz] using hσz⟩, ?_⟩
    simp only [OpenPartialHomeomorph.coe_trans, Function.comp_apply, hegz]
    exact he'σz
  · simpa [r, e.left_inv hz.1] using congrFun (hqe' _ hz.2) i

omit [CompleteSpace E] in
/-- Near `x`, the inverse of a chart in which the active defining functions are the coordinates
`q` maps the cone of `ker qs` on which `q` is nonnegative into the face of `s`. Here `qs` collects
the coordinates labelled by `s`, and the inactive defining functions stay positive near `x`. -/
private theorem tendsto_symm_nhdsWithin_face {ρ : ι → M → ℝ} {x : M}
    (hρ : ∀ i, ContinuousAt (ρ i) x) {s : Set ι} (hxD : ∀ i, 0 ≤ ρ i x)
    (hxs : ∀ i ∈ s, ρ i x = 0) (χ : OpenPartialHomeomorph M E) (hxχ : x ∈ χ.source)
    (hχx : χ x = 0) {q : E →L[ℝ] {i // ρ i x = 0} → ℝ}
    (hρχ : ∀ v ∈ χ.target, ∀ a : {i // ρ i x = 0}, ρ a (χ.symm v) = q v a) :
    Tendsto (fun v : (ContinuousLinearMap.pi fun a : {a : {i // ρ i x = 0} | (a : ι) ∈ s} ↦
        (ContinuousLinearMap.proj (a : {i // ρ i x = 0})).comp q).ker ↦ χ.symm (v : E))
      (𝓝[{v | ∀ a, 0 ≤ q v a}] 0) (𝓝[{y | (∀ i, 0 ≤ ρ i y) ∧ ∀ i ∈ s, ρ i y = 0}] x) := by
  have h0χ : (0 : E) ∈ χ.target := hχx ▸ χ.map_source hxχ
  have hval := continuous_subtype_val.tendsto (0 : (ContinuousLinearMap.pi fun a :
    {a : {i // ρ i x = 0} | (a : ι) ∈ s} ↦ (ContinuousLinearMap.proj (a : {i // ρ i x = 0})).comp
      q).ker)
  have hT := (χ.continuousAt_symm h0χ).tendsto.comp hval
  rw [Function.comp_def, ← hχx, χ.left_inv hxχ] at hT
  have hinact : ∀ᶠ y in 𝓝 x, ∀ i, ρ i x ≠ 0 → 0 < ρ i y := eventually_all.mpr fun i ↦ by
    by_cases hi : ρ i x = 0
    · exact Eventually.of_forall fun _ h ↦ (h hi).elim
    · filter_upwards [continuousAt_const.eventually_lt (hρ i) ((hxD i).lt_of_ne' hi)]
        with y hy _ using hy
  refine tendsto_nhdsWithin_iff.mpr ⟨hT.mono_left nhdsWithin_le_nhds, ?_⟩
  filter_upwards [nhdsWithin_le_nhds (hval.eventually (χ.open_target.mem_nhds h0χ)),
    nhdsWithin_le_nhds (hT.eventually hinact), self_mem_nhdsWithin] with v hvt hvpos hvS
  refine ⟨fun i ↦ ?_, fun i hi ↦ ?_⟩
  · by_cases hi : ρ i x = 0
    · exact (hρχ v hvt ⟨i, hi⟩).symm ▸ hvS ⟨i, hi⟩
    · exact (hvpos i hi).le
  · rw [hρχ v hvt ⟨i, hxs i hi⟩]
    exact congrFun (LinearMap.mem_ker.mp v.2) ⟨⟨i, hxs i hi⟩, hi⟩

/-- **Faces detect the germ kernel.** Let a finite group act by `C^n` maps, `1 ≤ n`, fixing `x`,
and let the functions `ρ i` be locally invariant and `C¹` at `x`, with linearly independent
differentials at `x` for the labels active at `x`. If `x` lies on the face of a set `s` of labels,
then an element `g` acts as the identity on this face near `x` exactly when it acts as the
identity near `x`. -/
theorem eventually_nhdsWithin_face_smul_eq_iff
    (hsmooth : ∀ g : G, ContMDiff I I n fun y : M ↦ g • y) (hn : 1 ≤ n)
    {x : M} (hx : ∀ g : G, g • x = x) {ρ : ι → M → ℝ}
    (hρ : ∀ i, ContMDiffAt I 𝓘(ℝ) 1 (ρ i) x)
    (hinv : ∀ i (g : G), ∀ᶠ y in 𝓝 x, ρ i (g • y) = ρ i y)
    (hlin : LinearIndependent ℝ fun i : {i // ρ i x = 0} ↦ mvfderiv I (ρ i) x)
    {s : Set ι} (hxD : ∀ i, 0 ≤ ρ i x) (hxs : ∀ i ∈ s, ρ i x = 0) (g : G) :
    (∀ᶠ y in 𝓝[{y | (∀ i, 0 ≤ ρ i y) ∧ ∀ i ∈ s, ρ i y = 0}] x, g • y = y) ↔
      ∀ᶠ y in 𝓝 x, g • y = y := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let : Fintype G := Fintype.ofFinite G
  let : Invertible (Fintype.card G : ℝ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  let : ContinuousConstSMul G M := ⟨fun g ↦ (hsmooth g).continuous⟩
  refine ⟨fun hg ↦ ?_, fun h ↦ nhdsWithin_le_nhds h⟩
  obtain ⟨σ, χ, q, hxχ, hχx, hχ, hq, hqσ, hqχ⟩ :=
    exists_equivariant_straightened_chart (ρ := fun a : {i // ρ i x = 0} ↦ ρ a) hsmooth hn hx
      (fun a ↦ a.2) (fun a ↦ hρ a) (fun a ↦ hinv a) hlin
  let A := {i // ρ i x = 0}
  have h0χ : (0 : E) ∈ χ.target := hχx ▸ χ.map_source hxχ
  have hρχ (v : E) (hv : v ∈ χ.target) (a : A) : ρ a (χ.symm v) = q v a := by
    rw [← hqχ _ (χ.map_target hv), χ.right_inv hv]
  -- In the chart the action is linear, and the labels in `s` give its normal coordinates `qs`.
  have hL (g : G) : HasStrictFDerivAt (χ ∘ (g • ·) ∘ χ.symm) (σ g : E →L[ℝ] E) 0 := by
    refine (σ g).hasStrictFDerivAt.congr_of_eventuallyEq ?_
    filter_upwards [χ.open_target.mem_nhds h0χ] with w hw
    simp [(hχ g _ (χ.map_target hw)).2, χ.right_inv hw]
  let t : Set A := {a | (a : ι) ∈ s}
  let qs := ContinuousLinearMap.pi fun a : t ↦ (ContinuousLinearMap.proj (a : A)).comp q
  have hqs : qs ∘ χ ∘ (g • ·) ∘ χ.symm =ᶠ[𝓝 0] qs := by
    filter_upwards [χ.open_target.mem_nhds h0χ] with w hw
    funext a
    simp only [Function.comp_apply, (hχ g _ (χ.map_target hw)).2, χ.right_inv hw]
    exact congrFun (DFunLike.congr_fun (hqσ g) w) _
  -- Near `0` the face is the cone of `ker qs` cut out by the remaining active coordinates.
  let S : Set qs.ker := {v | ∀ a, 0 ≤ q v a}
  have hS : UniqueDiffWithinAt ℝ S 0 := uniqueDiffWithinAt_ker_setOf_nonneg hq t
  refine (χ.eventually_smul_eq_iff_on_ker hxχ hχx hx qs hS hL g hqs).mpr ?_
  -- Pull the face germ condition back along the chart inverse restricted to the cone.
  exact (tendsto_symm_nhdsWithin_face (fun i ↦ (hρ i).continuousAt) hxD hxs χ hxχ hχx
    hρχ).eventually hg

end TauCeti

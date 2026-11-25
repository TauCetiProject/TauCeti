/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.BorderedHolomorphic.SchottkyDouble.Basic
public import Mathlib.Geometry.Manifold.PartitionOfUnity
import TauCeti.Geometry.Manifold.MFDeriv.ModelChart
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.PartitionOfUnity.MVFDeriv
import TauCeti.Analysis.Complex.FDerivSign

/-!
# An odd defining function of the seam of a Schottky double

Let `M` be a Riemann surface with boundary and `D` its Schottky double, with sheet swap `τ`. The
seam of `D` is the image of the boundary of `M` in the first copy, the fixed set of `τ`. This file
constructs a smooth real function `g` on `D` which defines the seam and is odd under `τ`
(`TauCeti.SchottkyDouble.exists_odd_definingFunction`):

* `g ∘ τ = -g`;
* `g` vanishes exactly on the seam, is positive on the first copy of the interior of `M` and
  negative on the second;
* the differential of `g` does not vanish on the seam.

The imaginary part of a doubled chart already has these properties on the chart domain: it is
positive on the first interior sheet, negative on the second and zero on the seam
(`TauCeti.SchottkyDouble.mem_range_interiorInl_iff_im_chartAt_pos` and its companions). At a seam
point `q` its differential is positive on the vector `i` of the preferred chart at `q`: it vanishes
on the real direction, along which the chart stays on the seam, is nonnegative on `i`, along which
the chart enters the first sheet, and is nonzero since the chart is a local diffeomorphism
(`TauCeti.Complex.fderiv_apply_I_pos`). A smooth partition of unity subordinate to the chart
domains glues these local functions into `g₀`, with the same signs and differential positive on `i`
at the seam (`SmoothPartitionOfUnity.mvfderiv_finsum_smul_pos`, the gluing step also used for
boundary defining functions in `TauCeti.Geometry.Manifold.Boundary.DefiningFunction.Basic`). Its
antisymmetrization `g = g₀ - g₀ ∘ τ` is odd, keeps the signs because `τ` exchanges the two sheets
and fixes the seam, and on the seam has twice the differential of `g₀` on `i`, because `τ` reads as
`z ↦ conj z` in the doubled charts (`TauCeti.SchottkyDouble.hasMFDerivAt_swap`) and so reverses
`i`.

Such a function is the input for a collar projection of the seam which is invariant under `τ`, by
flowing to its zero level along a field which `τ` reverses.

## Main results

* `TauCeti.SchottkyDouble.exists_odd_definingFunction`: a smooth defining function of the seam
  which is odd under the sheet swap and positive on the first sheet.

## References

* L. V. Ahlfors and L. Sario, *Riemann Surfaces*, Princeton University Press, 1960, Ch. II, for
  the double of a bordered Riemann surface.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix C.3, for the doubled bundle built on it.
-/

public section

open Set Complex Filter Topology
open scoped Manifold ContDiff ComplexConjugate

namespace TauCeti.SchottkyDouble

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ClosedUpperHalfPlane M]
  [IsManifold closedUpperHalfPlaneModel 1 M]

local notation "A" => (borderedInterior M : Set M)ᶜ
local notation "D" => SchottkyDouble M

/-- **Antisymmetrizing at a fixed point of the swap.** At a fixed point `q` of the sheet swap, the
differential of `g₀ - g₀ ∘ τ` on the vector `i` of the preferred chart is twice that of `g₀`, since
`τ` reads as conjugation and so reverses `i`. -/
private theorem mvfderiv_sub_comp_swap_I {g₀ : D → ℝ}
    (hg₀ : MDifferentiable 𝓘(ℝ, ℂ) 𝓘(ℝ) g₀) {q : D} (hq : DoubleAlong.swap A q = q) :
    mvfderiv 𝓘(ℝ, ℂ) (fun z ↦ g₀ z - g₀ (DoubleAlong.swap A z)) q I =
      2 * mvfderiv 𝓘(ℝ, ℂ) g₀ q I := by
  -- The vector `i`, read as a tangent vector at `q`.
  set w : TangentSpace 𝓘(ℝ, ℂ) q := I with hw
  have hswap := hasMFDerivAt_swap (M := M) q
  have hcomp : mvfderiv 𝓘(ℝ, ℂ) (fun z ↦ g₀ (DoubleAlong.swap A z)) q w =
      -mvfderiv 𝓘(ℝ, ℂ) g₀ q w := by
    have h := mvfderiv_comp_apply q (hg₀ _) hswap.mdifferentiableAt w
    rw [hswap.mfderiv] at h
    have hc : ((conjCLE : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ) w = -w := by
      rw [ContinuousLinearEquiv.coe_coe, conjCLE_apply, hw, conj_I]
      -- `-I` in `ℂ` and `-w` in the tangent space at `q` are the same element.
      rfl
    have key : mvfderiv 𝓘(ℝ, ℂ) g₀ (DoubleAlong.swap A q)
        (((conjCLE : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ) w) = -mvfderiv 𝓘(ℝ, ℂ) g₀ q w := by
      rw [hq]
      exact (congrArg (mvfderiv 𝓘(ℝ, ℂ) g₀ q) hc).trans (map_neg _ _)
    exact h.trans key
  have hsub := congrArg (fun L ↦ L w) (mvfderiv_fun_sub (g' := fun z ↦ g₀ (DoubleAlong.swap A z))
    (hg₀ q) ((hg₀ _).comp q hswap.mdifferentiableAt))
  simp only [sub_apply] at hsub
  exact hsub.trans (by rw [hcomp]; ring)

variable [HasGroupoid M borderedHolomorphicGroupoid]

/-- The imaginary part of a doubled chart is differentiable on the chart domain. -/
private theorem mdifferentiableAt_im_chartAt {p q : D} (hqp : q ∈ (chartAt ℂ p).source) :
    MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ) (fun z ↦ (chartAt ℂ p z).im) q :=
  have : IsManifold 𝓘(ℝ, ℂ) 1 D := IsManifold.of_le (n := ω) le_top
  ((imCLM.contMDiff (n := 1)).mdifferentiableAt one_ne_zero).comp q
    (mdifferentiableAt_atlas (chart_mem_atlas ℂ p) hqp)

/-- **The imaginary part of a doubled chart at the seam.** If `q` lies on the seam and in the
domain of the doubled chart at `p`, the imaginary part of that chart has positive differential at
`q` on the vector `i` of the preferred chart at `q`. -/
private theorem mvfderiv_im_chartAt_I_pos {p q : D} (hqp : q ∈ (chartAt ℂ p).source)
    (hq : q ∈ DoubleAlong.inl A '' A) :
    0 < mvfderiv 𝓘(ℝ, ℂ) (fun z ↦ (chartAt ℂ p z).im) q I := by
  have : IsManifold 𝓘(ℝ, ℂ) 1 D := IsManifold.of_le (n := ω) le_top
  set e := chartAt ℂ q
  set x₀ := e q
  set F : ℂ → ℝ := fun w ↦ (chartAt ℂ p (e.symm w)).im
  -- Near `x₀`, the inverse chart lands in the domains of both charts.
  have hev : ∀ᶠ w in 𝓝 x₀, w ∈ e.target ∧ e.symm w ∈ (chartAt ℂ p).source := by
    refine (e.open_target.eventually_mem (mem_chart_target ℂ q)).and ?_
    exact e.continuousAt_symm (mem_chart_target ℂ q)
      ((chartAt ℂ p).open_source.mem_nhds (by rwa [e.left_inv (mem_chart_source ℂ q)]))
  -- The sign of `F` is the sign of the imaginary part of its argument.
  have hsign : ∀ w, w ∈ e.target → e.symm w ∈ (chartAt ℂ p).source →
      (w.im = 0 → F w = 0) ∧ (0 < w.im → 0 < F w) := fun w hwt hwp ↦ by
    have hws : e.symm w ∈ e.source := e.map_target hwt
    refine ⟨fun hw ↦ ?_, fun hw ↦ ?_⟩
    · have h := (mem_image_inl_compl_iff_im_chartAt_eq_zero hws).2 (by rwa [e.right_inv hwt])
      exact (mem_image_inl_compl_iff_im_chartAt_eq_zero hwp).1 h
    · have h := (mem_range_interiorInl_iff_im_chartAt_pos hws).2 (by rwa [e.right_inv hwt])
      exact (mem_range_interiorInl_iff_im_chartAt_pos hwp).1 h
  have hx₀ : x₀.im = 0 := (mem_image_inl_compl_iff_im_chartAt_eq_zero (mem_chart_source ℂ q)).1 hq
  -- The differential of `im ∘ chart` at `q` is the derivative of `F` at `x₀`.
  have hh := mdifferentiableAt_im_chartAt hqp
  have hLv : ∀ v : ℂ, mvfderiv 𝓘(ℝ, ℂ) (fun z ↦ (chartAt ℂ p z).im) q v = fderiv ℝ F x₀ v := by
    intro v
    have h := congrArg (fun L ↦ L v) (mvfderiv_eq_fderivWithin_extChartAt_target hh)
    simp only [extChartAt_coe_symm, extChartAt_target, extChartAt_coe, modelWithCornersSelf_coe,
      modelWithCornersSelf_coe_symm, Function.comp_id, range_id, inter_univ, Function.id_comp,
      preimage_id_eq, id_eq] at h
    rw [fderivWithin_of_isOpen e.open_target (mem_chart_target ℂ q)] at h
    exact h
  -- The differential is nonzero, since the chart is a local diffeomorphism.
  obtain ⟨v, hv⟩ :=
    (isInvertible_mfderiv_chart (𝕜 := ℝ) (IsManifold.chart_mem_maximalAtlas p) hqp).surjective I
  have hLne : fderiv ℝ F x₀ v ≠ 0 := by
    have hc := mdifferentiableAt_atlas (I := 𝓘(ℝ, ℂ)) (chart_mem_atlas ℂ p) hqp
    have h := mvfderiv_comp_apply_of_differentiableAt imCLM.differentiableAt hc v
    rw [ContinuousLinearMap.fderiv, mvfderiv_apply_eq_mfderiv_apply (chartAt ℂ p) q v, hv,
      imCLM_apply, I_im] at h
    exact fun h0 ↦ one_ne_zero (h.symm.trans ((hLv v).trans h0))
  rw [hLv]
  refine TauCeti.Complex.fderiv_apply_I_pos hLne ?_ ?_
  · filter_upwards [hev] with w hw hwi
    exact (hsign w hw.1 hw.2).1 (hwi.trans hx₀)
  · filter_upwards [hev] with w hw hwi
    exact (hsign w hw.1 hw.2).2 (hx₀ ▸ hwi)

/-- **Gluing the imaginary parts of the doubled charts.** There is a smooth function on the double
which is positive on the first interior sheet, negative on the second, and whose differential at
each seam point is positive on the vector `i` of the preferred chart there. -/
private theorem exists_sheet_sign_function [T2Space M] [SecondCountableTopology M] :
    ∃ g₀ : D → ℝ, ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ g₀ ∧ (∀ z ∈ range (interiorInl M), 0 < g₀ z) ∧
      (∀ z ∈ range (interiorInr M), g₀ z < 0) ∧
      ∀ q ∈ DoubleAlong.inl A '' A, 0 < mvfderiv 𝓘(ℝ, ℂ) g₀ q I := by
  have : IsManifold 𝓘(ℝ, ℂ) ∞ D := IsManifold.of_le (n := ω) le_top
  have : LocallyCompactSpace D := ChartedSpace.locallyCompactSpace ℂ D
  obtain ⟨φ, hφ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, ℂ) isClosed_univ
    (fun i : D ↦ (chartAt ℂ i).source) (fun i ↦ (chartAt ℂ i).open_source)
    fun x _ ↦ mem_iUnion.2 ⟨x, mem_chart_source ℂ x⟩
  set g₀ : D → ℝ := fun z ↦ ∑ᶠ i, φ i z • (chartAt ℂ i z).im
  have hmem {i z : D} (hz : φ i z ≠ 0) : z ∈ (chartAt ℂ i).source := hφ i (subset_tsupport _ hz)
  have hg₀ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ g₀ :=
    hφ.contMDiff_finsum_smul (fun i ↦ (chartAt ℂ i).open_source)
      fun i ↦ imCLM.contMDiff.comp_contMDiffOn contMDiffOn_chart
  -- `g₀` has the sign of the sheet.
  have hpos : ∀ z ∈ range (interiorInl M), 0 < g₀ z := fun z hz ↦
    φ.finsum_smul_mem_convex (g := fun i z ↦ (chartAt ℂ i z).im) (t := Ioi 0) (mem_univ z)
      (fun i hi ↦ (mem_range_interiorInl_iff_im_chartAt_pos (hmem hi)).1 hz) (convex_Ioi 0)
  have hneg : ∀ z ∈ range (interiorInr M), g₀ z < 0 := fun z hz ↦
    φ.finsum_smul_mem_convex (g := fun i z ↦ (chartAt ℂ i z).im) (t := Iio 0) (mem_univ z)
      (fun i hi ↦ (mem_range_interiorInr_iff_im_chartAt_neg (hmem hi)).1 hz) (convex_Iio 0)
  -- At the seam every local function vanishes and has positive differential on `i`.
  exact ⟨g₀, hg₀, hpos, hneg, fun q hq ↦ φ.mvfderiv_finsum_smul_pos hφ (mem_univ q)
    (fun i hi ↦ mdifferentiableAt_im_chartAt hi)
    (fun i hi ↦ (mem_image_inl_compl_iff_im_chartAt_eq_zero hi).1 hq)
    fun i hi ↦ mvfderiv_im_chartAt_I_pos hi hq⟩

/-- **An odd defining function of the seam.** On the Schottky double of a Hausdorff,
second-countable Riemann surface with boundary there is a smooth real function `g` which is odd
under the sheet swap, vanishes exactly on the seam, is positive on the first copy of the interior,
and whose differential at every seam point is positive on the vector `i` of the preferred chart
there; in particular it does not vanish. -/
theorem exists_odd_definingFunction [T2Space M] [SecondCountableTopology M] :
    ∃ g : D → ℝ, ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ g ∧ (∀ z, g (DoubleAlong.swap A z) = -g z) ∧
      (∀ z, g z = 0 ↔ z ∈ DoubleAlong.inl A '' A) ∧
      (∀ x ∈ borderedInterior M, 0 < g (DoubleAlong.inl A x)) ∧
      ∀ z ∈ DoubleAlong.inl A '' A, 0 < mvfderiv 𝓘(ℝ, ℂ) g z I := by
  obtain ⟨g₀, hg₀, hpos, hneg, hderiv⟩ := exists_sheet_sign_function (M := M)
  -- The swap exchanges the two interior sheets and fixes the seam.
  have hswapl (u : borderedInterior M) :
      DoubleAlong.swap A (interiorInl M u) = interiorInr M u := by
    rw [interiorInl_apply, interiorInr_apply, DoubleAlong.swap_inl]
  have hswapr (u : borderedInterior M) :
      DoubleAlong.swap A (interiorInr M u) = interiorInl M u := by
    rw [interiorInl_apply, interiorInr_apply, DoubleAlong.swap_inr]
  have hswap0 : ∀ z ∈ DoubleAlong.inl A '' A, DoubleAlong.swap A z = z := fun z hz ↦ by
    rw [← DoubleAlong.fixed_locus] at hz
    exact hz
  set g : D → ℝ := fun z ↦ g₀ z - g₀ (DoubleAlong.swap A z) with hg_def
  have hgl : ∀ u, 0 < g (interiorInl M u) := fun u ↦ by
    simp only [hg_def, hswapl]
    linarith [hpos _ ⟨u, rfl⟩, hneg _ ⟨u, rfl⟩]
  have hgr : ∀ u, g (interiorInr M u) < 0 := fun u ↦ by
    simp only [hg_def, hswapr]
    linarith [hpos _ ⟨u, rfl⟩, hneg _ ⟨u, rfl⟩]
  refine ⟨g, hg₀.sub (hg₀.comp contMDiff_swap), fun z ↦ ?_, fun z ↦ ?_,
    fun x hx ↦ by simpa only [interiorInl_apply] using hgl ⟨x, hx⟩, fun q hq ↦ ?_⟩
  · simp only [hg_def, DoubleAlong.swap_swap, neg_sub]
  · refine ⟨fun h0 ↦ ?_, fun hz ↦ by simp only [hg_def, hswap0 z hz, sub_self]⟩
    rcases mem_range_interiorInl_or_mem_range_interiorInr_or_mem_image_inl_compl z with
      ⟨u, rfl⟩ | ⟨u, rfl⟩ | hz
    · exact absurd h0 (hgl u).ne'
    · exact absurd h0 (hgr u).ne
    · exact hz
  · rw [mvfderiv_sub_comp_swap_I (hg₀.mdifferentiable (by simp)) (hswap0 q hq)]
    linarith [hderiv q hq]

end TauCeti.SchottkyDouble

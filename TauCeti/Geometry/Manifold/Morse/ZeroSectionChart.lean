/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.ZeroSectionChart
public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Constructions
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Prod.Ball

/-!
# The parametric Morse lemma along the zero section over a manifold

Let `1 ≤ n ≤ ∞`, let `S` be a finite-dimensional boundaryless `C^{n+2}` manifold, `E` a
finite-dimensional real normed space and `F (b, v)` a real function on `S × E`, `C^{n+2}` near the
zero section `S × {0}` over an open set `U` of `S`, whose zero section is critical in the
fibres, with invertible vertical Hessians `H_b = D²(F (b, ·))(0)` for `b ∈ U`. This file shows
that the canonical parametric Morse coordinate `TauCeti.parametricMorseCoord F (b, v)` of
`TauCeti.Analysis.Calculus.Morse.Parametric` is a fibre coordinate on a neighbourhood of the whole
zero section over `U`: the map `(b, v) ↦ (b, parametricMorseCoord F (b, v))` is a single `C^n`
partial diffeomorphism of `S × E`, preserving the base in both directions, in which `F` is its
vertical Hessian quadratic form, `F (b, v) = F (b, 0) + ½ H_b (ψ (b, v)).2 (ψ (b, v)).2`
(`TauCeti.exists_partialDiffeomorph_parametricMorseCoord`). Its source contains the zero section
over `U` and meets each fibre in a set star-convex about `0`.

This is the parametric Morse lemma of `TauCeti.exists_parametricMorseCoord_chart` with the base
vector space replaced by a manifold. The canonical coordinate reads `F` only along the fibres, so
in an extended chart `φ` of `S` it is the canonical coordinate of `(x, v) ↦ F (φ⁻¹ x, v)`
(`TauCeti.parametricMorseCoord_comp_prodMap`). The local normal forms near the points of the zero
section are therefore the chart normal forms of
`TauCeti.exists_parametricMorseCoord_partialDiffeomorph_prod_ball`, read back through `φ × id`.
They are all restrictions of the one map `(b, v) ↦ (b, parametricMorseCoord F (b, v))`, and their
sources contain products of open sets of `S` with balls about `0`. Over each base point these balls
are nested, so the map is injective on their union and glues to a single partial diffeomorphism
(`TauCeti.exists_partialDiffeomorph_source_eq_biUnion_prod_ball`).

Families of this form arise along a Morse–Bott critical submanifold, from a function read in
normal coordinates once the normal spaces over an open set `S` of it are presented inside a
product `S × E`, for instance by a trivialization of the normal bundle over `S`. The canonical
coordinate is then defined along the whole of `S` at once, with no choice of charts of `S`.

## Main declarations

* `TauCeti.exists_partialDiffeomorph_parametricMorseCoord`: the parametric Morse lemma along the
  zero section over an open set of a manifold, as a single partial diffeomorphism given by the
  canonical coordinate.

## References

* R. S. Palais, *Morse theory on Hilbert manifolds*, Topology **2** (1963), 299--340, Section 2,
  for the operator square root.
* R. Bott, *Nondegenerate critical manifolds*, Ann. of Math. (2) **60** (1954), 248--261.
-/

public section

noncomputable section

open Filter Set Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [FiniteDimensional ℝ EB]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ EB H}
  {S : Type*} [TopologicalSpace S] [ChartedSpace H S]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {F : S × E → ℝ} {W : Set (S × E)} {U : Set S} {n : ℕ∞}

variable [IsManifold I (n + 2) S] [BoundarylessManifold I S]

/-- **The parametric Morse chart of `F` read in a chart of `S`.** Let `φ` be the extended chart of
`S` at a point `b₀` of the critical zero section over `U`. The family
`F_φ (x, v) = F (φ⁻¹ x, v)` on the model space `EB × E` is in normal form in its canonical
coordinate, on the source `U₀ ×ˢ ball 0 r` of a `C^n` partial diffeomorphism `Θ` of `EB × E`, by
`TauCeti.exists_parametricMorseCoord_partialDiffeomorph_prod_ball`. The source lies over the
interior of the chart target, and is carried into `W` by `φ⁻¹ × id`. -/
private theorem exists_extChartAt_parametricMorseCoord_prod_ball (hW : IsOpen W)
    (hF : ContMDiffOn (I.prod 𝓘(ℝ, E)) 𝓘(ℝ) (n + 2) F W) (hU : IsOpen U) {b₀ : S} (hb₀ : b₀ ∈ U)
    (hb₀W : (b₀, (0 : E)) ∈ W) (hcrit : ∀ b ∈ U, fderiv ℝ (fun v ↦ F (b, v)) 0 = 0)
    (hH : (fderiv ℝ (fderiv ℝ (fun v ↦ F (b₀, v))) 0).IsInvertible) (hn : n ≠ 0) :
    ∃ (U₀ : Set EB) (r : ℝ) (Θ : PartialDiffeomorph 𝓘(ℝ, EB × E) 𝓘(ℝ, EB × E) (EB × E) (EB × E) n),
      IsOpen U₀ ∧ extChartAt I b₀ b₀ ∈ U₀ ∧ 0 < r ∧ Θ.source = U₀ ×ˢ Metric.ball 0 r ∧
      (∀ z ∈ Θ.source, z.1 ∈ interior (extChartAt I b₀).target ∧
        ((extChartAt I b₀).symm z.1, z.2) ∈ W) ∧
      (∀ z ∈ Θ.source,
        Θ z = (z.1, parametricMorseCoord (fun z ↦ F ((extChartAt I b₀).symm z.1, z.2)) z)) ∧
      ∀ z ∈ Θ.source, F ((extChartAt I b₀).symm z.1, z.2) =
        F ((extChartAt I b₀).symm z.1, 0) + (2 : ℝ)⁻¹ *
          fderiv ℝ (fderiv ℝ (fun v ↦ F ((extChartAt I b₀).symm z.1, v))) 0
            (parametricMorseCoord (fun z ↦ F ((extChartAt I b₀).symm z.1, z.2)) z)
            (parametricMorseCoord (fun z ↦ F ((extChartAt I b₀).symm z.1, z.2)) z) := by
  set φ := extChartAt I b₀
  set Fc : EB × E → ℝ := fun z ↦ F (φ.symm z.1, z.2) with hFc
  set Wc : Set (EB × E) := (interior φ.target ×ˢ univ) ∩ {z | (φ.symm z.1, z.2) ∈ W}
  have hsymm : ContMDiffOn (𝓘(ℝ, EB).prod 𝓘(ℝ, E)) (I.prod 𝓘(ℝ, E)) (n + 2)
      (fun z : EB × E ↦ (φ.symm z.1, z.2)) (interior φ.target ×ˢ univ) :=
    (((contMDiffOn_extChartAt_symm b₀).mono interior_subset).comp contMDiffOn_fst
      fun z (hz : z ∈ interior φ.target ×ˢ univ) ↦ hz.1).prodMk contMDiffOn_snd
  have hWc : IsOpen Wc :=
    hsymm.continuousOn.isOpen_inter_preimage (isOpen_interior.prod isOpen_univ) hW
  have hFcW : ContDiffOn ℝ (n + 2) Fc Wc := by
    have h : ContMDiffOn (𝓘(ℝ, EB).prod 𝓘(ℝ, E)) 𝓘(ℝ) (n + 2) Fc Wc :=
      hF.comp (hsymm.mono inter_subset_left) fun z (hz : z ∈ Wc) ↦ hz.2
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at h
    exact h.contDiffOn
  have hint : φ b₀ ∈ interior φ.target :=
    (ModelWithCorners.isInteriorPoint_iff (I := I)).mp BoundarylessManifold.isInteriorPoint
  have hφb₀ : φ.symm (φ b₀) = b₀ := extChartAt_to_inv b₀
  have hWcmem : Wc ∈ 𝓝 (φ b₀, 0) :=
    hWc.mem_nhds ⟨⟨hint, mem_univ _⟩, by simpa only [mem_ofPred_eq, hφb₀] using hb₀W⟩
  have hcritc : ∀ᶠ x in 𝓝 (φ b₀), fderiv ℝ (fun v ↦ Fc (x, v)) 0 = 0 := by
    have hUmem : φ.symm ⁻¹' U ∈ 𝓝 (φ b₀) :=
      (continuousAt_extChartAt_symm b₀).preimage_mem_nhds (by
        rw [hφb₀]; exact hU.mem_nhds hb₀)
    filter_upwards [hUmem] with x hx
    exact hcrit _ hx
  have hHc : (fderiv ℝ (fderiv ℝ (fun v ↦ Fc (φ b₀, v))) 0).IsInvertible := by
    simpa only [hFc, hφb₀] using hH
  obtain ⟨U₀, r, Θ, hU₀, hbU₀, hr, hΘsource, hsubWc, hΘeq, hnf⟩ :=
    exists_parametricMorseCoord_partialDiffeomorph_prod_ball hWcmem hFcW hcritc hHc hn
  refine ⟨U₀, r, Θ, hU₀, hbU₀, hr, hΘsource, fun z hz ↦ ?_, fun z hz ↦ hΘeq z (hΘsource ▸ hz),
    fun z hz ↦ hnf z (hΘsource ▸ hz)⟩
  obtain ⟨⟨hz₁, -⟩, hzW⟩ := hsubWc (hΘsource ▸ hz)
  exact ⟨hz₁, hzW⟩

/-- **The local parametric Morse chart over a manifold.** Near a point `(b₀, 0)` of the critical
zero section over `U`, the canonical map `(b, v) ↦ (b, parametricMorseCoord F (b, v))` agrees on
its source with a `C^n` partial diffeomorphism `e` of `S × E`, whose source contains a product
`V ×ˢ ball 0 r` of an open neighbourhood `V` of `b₀` with a ball, inside `W`, on which `F` is in
normal form. The map `e` is the chart normal form of
`TauCeti.exists_extChartAt_parametricMorseCoord_prod_ball` conjugated by the extended chart of
`S × E` at `(b₀, 0)`, which is `φ × id`. -/
private theorem exists_partialDiffeomorph_parametricMorseCoord_prod_ball (hW : IsOpen W)
    (hF : ContMDiffOn (I.prod 𝓘(ℝ, E)) 𝓘(ℝ) (n + 2) F W) (hU : IsOpen U) {b₀ : S} (hb₀ : b₀ ∈ U)
    (hb₀W : (b₀, (0 : E)) ∈ W) (hcrit : ∀ b ∈ U, fderiv ℝ (fun v ↦ F (b, v)) 0 = 0)
    (hH : (fderiv ℝ (fderiv ℝ (fun v ↦ F (b₀, v))) 0).IsInvertible) (hn : n ≠ 0) :
    ∃ (V : Set S) (r : ℝ) (e : PartialDiffeomorph (I.prod 𝓘(ℝ, E)) (I.prod 𝓘(ℝ, E)) (S × E)
      (S × E) n),
      IsOpen V ∧ b₀ ∈ V ∧ 0 < r ∧ V ×ˢ Metric.ball 0 r ⊆ e.source ∧ V ×ˢ Metric.ball 0 r ⊆ W ∧
      (∀ z ∈ e.source, e z = (z.1, parametricMorseCoord F z)) ∧
      ∀ z ∈ V ×ˢ Metric.ball 0 r, F z = F (z.1, 0) + (2 : ℝ)⁻¹ *
        fderiv ℝ (fderiv ℝ (fun v ↦ F (z.1, v))) 0
          (parametricMorseCoord F z) (parametricMorseCoord F z) := by
  have : IsManifold I n S := IsManifold.of_le (le_self_add : (n : ℕ∞ω) ≤ n + 2)
  obtain ⟨U₀, r, Θ, hU₀, hbU₀, hr, hΘsource, hΘW, hΘeq, hnf⟩ :=
    exists_extChartAt_parametricMorseCoord_prod_ball hW hF hU hb₀ hb₀W hcrit hH hn
  set φ := extChartAt I b₀
  -- The canonical coordinate only reads the family along the fibres.
  have hcoord {b : S} (hb : b ∈ φ.source) (v : E) :
      parametricMorseCoord (fun z ↦ F (φ.symm z.1, z.2)) (φ b, v) =
        parametricMorseCoord F (b, v) := by
    rw [parametricMorseCoord_comp_prodMap (fun z : S × E ↦ F z) φ.symm, φ.left_inv hb]
  -- The extended chart of `S × E` at `(b₀, 0)`, which is `φ` on the base and the identity on `E`.
  set C := extChartPartialDiffeomorph (I.prod 𝓘(ℝ, E)) n (b₀, (0 : E)) with hC
  set e := (C.trans Θ).trans C.symm with he
  have hCext : extChartAt (I.prod 𝓘(ℝ, E)) (b₀, (0 : E)) = φ.prod (PartialEquiv.refl E) := by
    rw [extChartAt_prod, extChartAt_model_space_eq_id]
  have hCsource : C.source = (φ.source ∩ φ ⁻¹' interior φ.target) ×ˢ univ := by
    rw [hC, extChartPartialDiffeomorph_source, hCext]
    ext z
    simp [interior_prod_eq]
  have hCtarget : C.target = interior φ.target ×ˢ univ := by
    rw [hC, extChartPartialDiffeomorph_target, hCext]
    simp [interior_prod_eq]
  have hCapply (z : S × E) : C z = (φ z.1, z.2) := by
    rw [hC, coe_extChartPartialDiffeomorph, hCext]
    simp
  have hCsymm (z : EB × E) : C.symm z = (φ.symm z.1, z.2) := by
    refine (extChartPartialDiffeomorph_symm_apply (I.prod 𝓘(ℝ, E)) n (b₀, (0 : E)) z).trans ?_
    rw [hCext]
    simp
  -- The source and the values of the composite `e = C⁻¹ ∘ Θ ∘ C`.
  have hemem {z : S × E} :
      z ∈ e.source ↔ z ∈ C.source ∧ C z ∈ Θ.source ∧ Θ (C z) ∈ C.target := by
    simp only [he, PartialDiffeomorph.trans_source, PartialDiffeomorph.coe_trans,
      PartialDiffeomorph.symm_toPartialEquiv, PartialEquiv.symm_source, mem_inter_iff,
      mem_preimage, Function.comp_apply, and_assoc]
  have heapply (z : S × E) : e z = C.symm (Θ (C z)) := by
    simp only [he, PartialDiffeomorph.coe_trans, Function.comp_apply]
  set V : Set S := φ.source ∩ φ ⁻¹' U₀
  have hVopen : IsOpen V := isOpen_extChartAt_preimage' b₀ hU₀
  have hΘmem {z : S × E} (hz : z ∈ V ×ˢ Metric.ball (0 : E) r) : C z ∈ Θ.source := by
    rw [hCapply, hΘsource]
    exact ⟨hz.1.2, hz.2⟩
  refine ⟨V, r, e, hVopen, ⟨mem_extChartAt_source b₀, hbU₀⟩, hr, fun z hz ↦ ?_, fun z hz ↦ ?_,
    fun z hz ↦ ?_, fun z hz ↦ ?_⟩
  · have hint := (hΘW _ (hΘmem hz)).1
    rw [hCapply] at hint
    refine hemem.mpr ⟨hCsource ▸ ⟨⟨hz.1.1, hint⟩, mem_univ _⟩, hΘmem hz, ?_⟩
    rw [hΘeq _ (hΘmem hz), hCtarget, hCapply]
    exact ⟨hint, mem_univ _⟩
  · have h := (hΘW _ (hΘmem hz)).2
    rw [hCapply, φ.left_inv hz.1.1] at h
    exact h
  · obtain ⟨hzC, hzΘ, -⟩ := hemem.mp hz
    rw [hCsource] at hzC
    rw [heapply, hΘeq _ hzΘ, hCsymm, hCapply, φ.left_inv hzC.1.1, hcoord hzC.1.1]
  · obtain ⟨b, v⟩ := z
    have h := hnf (C (b, v)) (hΘmem hz)
    rw [hCapply, hcoord hz.1.1, φ.left_inv hz.1.1] at h
    exact h


/-- **The parametric Morse lemma along the zero section over a manifold.** Let `F (b, v)` be
`C^{n+2}`, with `1 ≤ n ≤ ∞`, on an open set `W` of `S × E` containing the zero section over an
open set `U` of the finite-dimensional boundaryless `C^{n+2}` manifold `S`, with `E` a
finite-dimensional real normed space, with critical zero section and invertible vertical Hessian
`H_b` at every `(b, 0)`, `b ∈ U`. Then there is a single `C^n` partial diffeomorphism `ψ`
of `S × E`, with source in `W` containing the whole zero section over `U` and meeting each fibre in
a set star-convex about `0`, which is given on its source by the canonical parametric Morse
coordinate, `ψ (b, v) = (b, parametricMorseCoord F (b, v))`, preserves the base in both
directions, and puts `F` in normal form:
`F (b, v) = F (b, 0) + ½ H_b (ψ (b, v)).2 (ψ (b, v)).2`. -/
theorem exists_partialDiffeomorph_parametricMorseCoord (hW : IsOpen W)
    (hF : ContMDiffOn (I.prod 𝓘(ℝ, E)) 𝓘(ℝ) (n + 2) F W) (hU : IsOpen U)
    (hUW : ∀ b ∈ U, (b, (0 : E)) ∈ W) (hcrit : ∀ b ∈ U, fderiv ℝ (fun v ↦ F (b, v)) 0 = 0)
    (hH : ∀ b ∈ U, (fderiv ℝ (fderiv ℝ (fun v ↦ F (b, v))) 0).IsInvertible) (hn : n ≠ 0) :
    ∃ ψ : PartialDiffeomorph (I.prod 𝓘(ℝ, E)) (I.prod 𝓘(ℝ, E)) (S × E) (S × E) n,
      ψ.source ⊆ W ∧ (∀ b ∈ U, (b, (0 : E)) ∈ ψ.source) ∧
      (∀ z ∈ ψ.source, ∀ t ∈ Icc (0 : ℝ) 1, (z.1, t • z.2) ∈ ψ.source) ∧
      (∀ z ∈ ψ.source, ψ z = (z.1, parametricMorseCoord F z)) ∧
      (∀ z ∈ ψ.target, (ψ.symm z).1 = z.1) ∧
      ∀ z ∈ ψ.source, F z = F (z.1, 0) + (2 : ℝ)⁻¹ *
        fderiv ℝ (fderiv ℝ (fun v ↦ F (z.1, v))) 0 (ψ z).2 (ψ z).2 := by
  -- Near each point `(b, 0)` of the zero section over `U`, the canonical map is a partial
  -- diffeomorphism on a source containing the product of an open set with a ball.
  have hloc := fun b (hb : b ∈ U) ↦
    exists_partialDiffeomorph_parametricMorseCoord_prod_ball hW hF hU hb (hUW b hb) hcrit
      (hH b hb) hn
  have : Nonempty (PartialDiffeomorph (I.prod 𝓘(ℝ, E)) (I.prod 𝓘(ℝ, E)) (S × E) (S × E) n) :=
    ⟨(Diffeomorph.refl (I.prod 𝓘(ℝ, E)) (S × E) n).toPartialDiffeomorph⟩
  choose! V r e hV hbV hr hVe hVW hΦe hnf using hloc
  -- These local partial diffeomorphisms glue along the nested balls of their sources.
  obtain ⟨ψ, hψsource, hψ⟩ := exists_partialDiffeomorph_source_eq_biUnion_prod_ball
    (Φ := fun z : S × E ↦ (z.1, parametricMorseCoord F z)) (fun _ _ ↦ rfl) hV hVe
    fun b hb z hz ↦ (hΦe b hb z (hVe b hb hz)).symm
  have hmem {z : S × E} : z ∈ ψ.source ↔ ∃ b ∈ U, z ∈ V b ×ˢ Metric.ball 0 (r b) := by
    simp only [hψsource, mem_iUnion, exists_prop]
  refine ⟨ψ, fun z hz ↦ ?_, fun b hb ↦ ?_, fun z hz t ht ↦ ?_, fun z _ ↦ by rw [hψ],
    fun z hz ↦ ?_, fun z hz ↦ ?_⟩
  · obtain ⟨b, hb, hzb⟩ := hmem.mp hz
    exact hVW b hb hzb
  · exact hmem.mpr ⟨b, hb, hbV b hb, Metric.mem_ball_self (hr b hb)⟩
  · obtain ⟨b, hb, hzb⟩ := hmem.mp hz
    exact hmem.mpr ⟨b, hb, hzb.1, (convex_ball (0 : E) (r b)).smul_mem_of_zero_mem
      (Metric.mem_ball_self (hr b hb)) hzb.2 ht⟩
  · -- the first coordinate of `ψ (ψ.symm z) = z` is that of `ψ.symm z`
    have h := congrArg Prod.fst (ψ.right_inv hz)
    rwa [hψ] at h
  · obtain ⟨b, hb, hzb⟩ := hmem.mp hz
    rw [hψ]
    exact hnf b hb z hzb

end TauCeti

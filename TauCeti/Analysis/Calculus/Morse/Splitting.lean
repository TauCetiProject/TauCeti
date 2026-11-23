/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.Bott
import TauCeti.Analysis.Calculus.ContDiff.Shear
import TauCeti.Analysis.Calculus.SecondDerivative

/-!
# The splitting lemma in product coordinates

Let `f (b, v)` be a function on a product `P × F` and `(a, c)` a point at which `f` is critical
in the fibre direction, `D(f (a, ·))(c) = 0`, with invertible vertical Hessian
`D²(f (a, ·))(c)`. Nothing is assumed about the derivatives in the base direction, so `f` may be
degenerate at `(a, c)` in an arbitrary way along `P`. The **splitting lemma** of Gromoll and
Meyer separates the nondegenerate fibre directions from the base: near `(a, c)`, after a change
of coordinates preserving the base parameter,

`f (b, v) = g b - Σ_{i < λ} yᵢ² + Σ_{i ≥ λ} yᵢ²`,

where `g b = f (b, h b)` is the *reduced function* along the section `h` of vertical critical
points, and `λ` is the Morse index of `f (a, ·)` at `c`. Taking for `P` the kernel of the Hessian
of a function at a degenerate critical point, together with any parameters, this reduces the
study of the function or family near the point to the reduced function on the kernel: this is the
first step of the normal forms of degenerate critical points, such as the birth–death normal form
of `TauCeti.birthDeathPotential` for one-parameter families of functions.

**The section of vertical critical points.** By the implicit function theorem applied to the
vertical derivative `(b, v) ↦ D(f (b, ·))(v)`, there is a `C^n` section `h` with `h a = c` whose
graph consists of vertical critical points, and near `(a, c)` it consists of all of them
(`TauCeti.exists_vertical_critical_section_of_contDiffOn`, in
`TauCeti.Analysis.Calculus.Morse.CriticalPointContinuation`, which continues critical points in
families). Along such a section, the critical
points of `f` near `(a, h a)` are exactly the points `(b, h b)` where `b` is a critical point of
the reduced function `b ↦ f (b, h b)`
(`TauCeti.eventually_fderiv_eq_zero_iff_snd_eq_and_fderiv_comp_graph_eq_zero`), since the
derivative of the reduced function is the base derivative of `f` along the graph.

**The chart.** Given a `C^{n+2}` section `h` of vertical critical points, the shifted family
`(b, w) ↦ f (b, w + h b) - f (b, h b)` vanishes on the zero section, which consists of vertical
critical points, and its vertical Hessian at `a` is that of `f`. The parametric Morse lemma
`TauCeti.exists_parametric_morse_chart_of_contDiffOn` applies to it, and composing with the shear
`(b, v) ↦ (b, v - h b)` gives a `C^n` chart `ψ` preserving the base parameter in which

`f z = f (z.1, h z.1) + ½ D²(f (z.1, ·))(h z.1) ((ψ z).2, (ψ z).2)`

(`TauCeti.exists_splitting_chart_of_contDiffOn`). Normalizing the fibre form as in the Morse–Bott
lemma (`OpenPartialHomeomorph.exists_normalized_morseBott_chart`) gives the sum of squares above
(`TauCeti.exists_normalized_splitting_chart_of_contDiffOn`). When `h` is the zero section and the
zero section is critical, the reduced function is constant and these are the Morse–Bott lemmas
`TauCeti.exists_morseBott_chart_of_contDiffOn` and
`TauCeti.exists_normalized_morseBott_chart_of_contDiffOn`.

The implicit function theorem gives a section one derivative less regular than `f`, and the
chart needs a `C^{n+2}` section, so a `C^{n+3}` family gives a `C^n` chart.

## Main declarations

* `TauCeti.exists_splitting_chart_of_contDiffOn`: the splitting lemma with the vertical Hessian
  as fibre form.
* `TauCeti.exists_normalized_splitting_chart_of_contDiffOn`: the splitting lemma with a sum of
  squares as fibre form.

## References

* D. Gromoll and W. Meyer, *On differentiable functions with isolated critical points*, Topology 8
  (1969), 361–369 (the splitting lemma).
-/

public section

open Filter Set Topology
open scoped ContDiff

namespace TauCeti

variable {P F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {f : P × F → ℝ} {a : P}

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
/-- The vertical Hessians of the shifted family `(b, w) ↦ f (b, w + h b) - f (b, h b)` are those
of `f` translated by `h b`. -/
private theorem fderiv_fderiv_shift (f : P × F → ℝ) (h : P → F) (b : P) (w : F) :
    fderiv ℝ (fderiv ℝ fun v ↦ f (b, v + h b) - f (b, h b)) w =
      fderiv ℝ (fderiv ℝ fun v ↦ f (b, v)) (w + h b) := by
  have hD : (fderiv ℝ fun v ↦ f (b, v + h b) - f (b, h b)) = fderiv ℝ fun v ↦ f (b, v + h b) :=
    funext fun _ ↦ fderiv_sub_const _
  rw [hD]
  exact fderiv_fderiv_comp_add_right (fun v ↦ f (b, v)) (h b) w

/-- Composing a chart `ψ₀` which preserves the base, fixes the zero section and has product source
`U₁ ×ˢ V` with the shear along a `C^n` section `h` over an open set `U ⊇ U₁` gives a chart `ψ`
with the same properties along the graph of `h`, whose source is the set of points `z` with
`z.1 ∈ U₁` and `z.2 - h z.1 ∈ V`. An identity
`f (z.1, z.2 + h z.1) - f (z.1, h z.1) = Q z.1 (ψ₀ z).2` for the shifted family on the source of
`ψ₀` becomes `f z = f (z.1, h z.1) + Q z.1 (ψ z).2`. -/
private theorem exists_shear_trans {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {n : ℕ∞} {h : P → F} {U U₁ : Set P} {V : Set F} {W : Set (P × F)} (hU : IsOpen U)
    (hh : ContDiffOn ℝ n h U) (ψ₀ : OpenPartialHomeomorph (P × F) (P × G)) (hU₁U : U₁ ⊆ U)
    (hsource : ψ₀.source = U₁ ×ˢ V) (hψfst : ∀ z, (ψ₀ z).1 = z.1)
    (hψ0 : ∀ b, ψ₀ (b, 0) = (b, 0)) (hψsymm : ∀ z ∈ ψ₀.target, (ψ₀.symm z).1 = z.1)
    (hψ : ContDiffOn ℝ n ψ₀ ψ₀.source) (hψinv : ContDiffOn ℝ n ψ₀.symm ψ₀.target)
    (hW : ∀ z ∈ ψ₀.source, (z.1, z.2 + h z.1) ∈ W) (Q : P → G → ℝ)
    (hQ : ∀ z ∈ ψ₀.source, f (z.1, z.2 + h z.1) - f (z.1, h z.1) = Q z.1 (ψ₀ z).2) :
    ∃ ψ : OpenPartialHomeomorph (P × F) (P × G),
      ψ.source = {z | z.1 ∈ U₁ ∧ z.2 - h z.1 ∈ V} ∧ ψ.source ⊆ W ∧
      (∀ z, (ψ z).1 = z.1) ∧ (∀ b, ψ (b, h b) = (b, 0)) ∧
      (∀ z ∈ ψ.target, (ψ.symm z).1 = z.1) ∧
      ContDiffOn ℝ n ψ ψ.source ∧ ContDiffOn ℝ n ψ.symm ψ.target ∧
      ∀ z ∈ ψ.source, f z = f (z.1, h z.1) + Q z.1 (ψ z).2 := by
  obtain ⟨Ψ, hΨC, hΨCinv, hΨsrc, hΨ⟩ := hh.exists_contDiffOn_graphShear hU
  have happly (z : P × F) : Ψ.trans ψ₀ z = ψ₀ (z.1, z.2 - h z.1) := by
    rw [OpenPartialHomeomorph.coe_trans, Function.comp_apply, hΨ]
  have hsrc : (Ψ.trans ψ₀).source = {z | z.1 ∈ U₁ ∧ z.2 - h z.1 ∈ V} := by
    ext z
    simp only [OpenPartialHomeomorph.trans_source, hsource, mem_inter_iff, mem_preimage, hΨsrc,
      hΨ, mem_prod, mem_ofPred_eq]
    exact ⟨fun hz ↦ hz.2, fun hz ↦ ⟨hU₁U hz.1, hz⟩⟩
  -- The shear sends the source into the source of `ψ₀`.
  have hmem (z : P × F) (hz : z ∈ (Ψ.trans ψ₀).source) : (z.1, z.2 - h z.1) ∈ ψ₀.source := by
    rw [hsrc] at hz
    exact hsource ▸ ⟨hz.1, hz.2⟩
  refine ⟨Ψ.trans ψ₀, hsrc, fun z hz ↦ by simpa using hW _ (hmem z hz),
    fun z ↦ by rw [happly, hψfst], fun b ↦ by rw [happly, sub_self, hψ0], fun z hz ↦ ?_,
    hψ.comp (hΨC.mono fun _ hz ↦ hz.1) fun _ hz ↦ hz.2,
    hΨCinv.comp (hψinv.mono fun _ hz ↦ hz.1) fun _ hz ↦ hz.2, fun z hz ↦ ?_⟩
  · -- `Ψ` preserves the base coordinate, hence so does its inverse on its target.
    obtain ⟨hz₀, hzΨ⟩ := hz
    have hfst := congrArg Prod.fst (Ψ.right_inv hzΨ)
    rw [hΨ] at hfst
    rw [OpenPartialHomeomorph.coe_trans_symm, Function.comp_apply, hfst, hψsymm z hz₀]
  · have hz' := hQ _ (hmem z hz)
    dsimp only at hz'
    rw [sub_add_cancel, Prod.mk.eta] at hz'
    rw [happly]
    exact sub_eq_iff_eq_add'.1 hz'

variable [FiniteDimensional ℝ P] [FiniteDimensional ℝ F] {n : ℕ∞} {h : P → F} {U : Set P}
  {W : Set (P × F)}

/-- The shifted family `(b, w) ↦ f (b, w + h b) - f (b, h b)` along a `C^{n+2}` section `h` of
vertical critical points has a parametric Morse chart over a base `U₁ ⊆ U`. -/
private theorem exists_shifted_parametric_morse_chart (hW : W ∈ 𝓝 (a, h a))
    (hf : ContDiffOn ℝ (n + 2) f W) (hU : IsOpen U) (haU : a ∈ U)
    (hh : ContDiffOn ℝ (n + 2) h U) (hcrit : ∀ b ∈ U, fderiv ℝ (fun v ↦ f (b, v)) (h b) = 0)
    (hH : (fderiv ℝ (fderiv ℝ (fun v ↦ f (a, v))) (h a)).IsInvertible) (hn : n ≠ 0) :
    ∃ (ψ₀ : OpenPartialHomeomorph (P × F) (P × F)) (U₁ : Set P) (V : Set F),
      IsOpen U₁ ∧ IsOpen V ∧ a ∈ U₁ ∧ (0 : F) ∈ V ∧ U₁ ⊆ U ∧ ψ₀.source = U₁ ×ˢ V ∧
      (∀ z ∈ U₁ ×ˢ V, (z.1, z.2 + h z.1) ∈ W) ∧
      (∀ z, (ψ₀ z).1 = z.1) ∧ (∀ b, ψ₀ (b, 0) = (b, 0)) ∧
      (∀ z ∈ ψ₀.target, (ψ₀.symm z).1 = z.1) ∧
      ContDiffOn ℝ n ψ₀ ψ₀.source ∧ ContDiffOn ℝ n ψ₀.symm ψ₀.target ∧
      (∀ᶠ z in 𝓝 (a, (0 : F)),
        ContDiffAt ℝ (n + 2) (fun z ↦ f (z.1, z.2 + h z.1) - f (z.1, h z.1)) z) ∧
      (fderiv ℝ (fderiv ℝ fun v ↦ f (a, v + h a) - f (a, h a)) 0).IsInvertible ∧
      ∀ z ∈ ψ₀.source, f (z.1, z.2 + h z.1) - f (z.1, h z.1) = (2 : ℝ)⁻¹ *
        fderiv ℝ (fderiv ℝ (fun v ↦ f (z.1, v))) (h z.1) (ψ₀ z).2 (ψ₀ z).2 := by
  set g : P × F → ℝ := fun z ↦ f (z.1, z.2 + h z.1) - f (z.1, h z.1) with hg_def
  have hgslice (b : P) : (fun v ↦ g (b, v)) = fun v ↦ f (b, v + h b) - f (b, h b) := rfl
  have hgHess (b : P) (w : F) : fderiv ℝ (fderiv ℝ (fun v ↦ g (b, v))) w =
      fderiv ℝ (fderiv ℝ (fun v ↦ f (b, v))) (w + h b) :=
    fderiv_fderiv_shift f h b w
  -- The open set of points `z` over `U` such that `(z.1, h z.1)` and `(z.1, z.2 + h z.1)` lie in
  -- the interior of `W`, on which `g` is `C^{n+2}`.
  have hγ : ContDiffOn ℝ (n + 2) (fun z : P × F ↦ (z.1, h z.1)) (U ×ˢ univ) :=
    contDiffOn_fst.prodMk (hh.comp contDiffOn_fst fun _ hz ↦ hz.1)
  have hσ : ContDiffOn ℝ (n + 2) (fun z : P × F ↦ (z.1, z.2 + h z.1)) (U ×ˢ univ) :=
    contDiffOn_fst.prodMk (contDiffOn_snd.add (hh.comp contDiffOn_fst fun _ hz ↦ hz.1))
  set W' : Set (P × F) := U ×ˢ univ ∩
    (fun z : P × F ↦ ((z.1, h z.1), (z.1, z.2 + h z.1))) ⁻¹' (interior W ×ˢ interior W)
  have hW' : IsOpen W' :=
    (hγ.prodMk hσ).continuousOn.isOpen_inter_preimage (hU.prod isOpen_univ)
      (isOpen_interior.prod isOpen_interior)
  have haW : (a, h a) ∈ interior W := mem_interior_iff_mem_nhds.2 hW
  have ha0 : (a, (0 : F)) ∈ W' := ⟨⟨haU, mem_univ _⟩, haW, by simpa using haW⟩
  have hfi : ContDiffOn ℝ (n + 2) f (interior W) := hf.mono interior_subset
  have hg : ContDiffOn ℝ (n + 2) g W' :=
    (hfi.comp (hσ.mono inter_subset_left) fun _ (hz : _ ∈ W') ↦ hz.2.2).sub
      (hfi.comp (hγ.mono inter_subset_left) fun _ (hz : _ ∈ W') ↦ hz.2.1)
  -- The zero section of `g` consists of vertical critical points, with the vertical Hessians of
  -- `f` along the graph of `h`.
  have hgcrit : ∀ᶠ b in 𝓝 a, fderiv ℝ (fun v ↦ g (b, v)) 0 = 0 := by
    filter_upwards [hU.mem_nhds haU] with b hb
    rw [hgslice, fderiv_sub_const]
    exact (fderiv_comp_add_right (f := fun v ↦ f (b, v)) (h b)).trans (by rw [zero_add, hcrit b hb])
  have hgH : (fderiv ℝ (fderiv ℝ (fun v ↦ g (a, v))) 0).IsInvertible := by
    rwa [hgHess, zero_add]
  obtain ⟨ψ₀, U₁, V, hU₁, hV, haU₁, h0V, hsource, hUV, -, hψfst, hψ0, hψsymm, hψ, hψinv, hψg⟩ :=
    exists_parametric_morse_chart_of_contDiffOn (hW'.mem_nhds ha0) hg hgcrit hgH hn
  refine ⟨ψ₀, U₁, V, hU₁, hV, haU₁, h0V, fun b hb ↦ (hUV (mk_mem_prod hb h0V)).1.1, hsource,
    fun z hz ↦ interior_subset (hUV hz).2.2, hψfst, hψ0, hψsymm, hψ, hψinv, ?_, hgH,
    fun z hz ↦ ?_⟩
  · filter_upwards [hW'.mem_nhds ha0] with z hz using hg.contDiffAt (hW'.mem_nhds hz)
  · have hz' := hψg z hz
    have hg0 : g (z.1, 0) = 0 := by simp [hg_def]
    rwa [hg0, zero_add, hgHess, zero_add] at hz'

/-- **The splitting lemma in product coordinates.** Let `f` be `C^{n+2}` on a neighbourhood `W` of
`(a, h a)`, with `1 ≤ n ≤ ∞`, where `h` is `C^{n+2}` on an open neighbourhood `U` of `a`, every
point `(b, h b)` with `b ∈ U` is a critical point of the fibre restriction `v ↦ f (b, v)`, and the
vertical Hessian at `(a, h a)` is invertible. Then there is a `C^n` chart `ψ` with source in `W`,
preserving the base parameter in both directions and sending the graph of `h` to the zero section,
on whose source

`f z = f (z.1, h z.1) + ½ D²(f (z.1, ·))(h z.1) ((ψ z).2, (ψ z).2)`.

Its source is the set of points `z` with `z.1 ∈ U'` and `z.2 - h z.1 ∈ V`, for open
neighbourhoods `U' ⊆ U` of `a` and `V` of `0`. A section `h` with these properties is supplied by
`TauCeti.exists_vertical_critical_section_of_contDiffOn` for a `C^{n+3}` family. -/
theorem exists_splitting_chart_of_contDiffOn (hW : W ∈ 𝓝 (a, h a))
    (hf : ContDiffOn ℝ (n + 2) f W) (hU : IsOpen U) (haU : a ∈ U)
    (hh : ContDiffOn ℝ (n + 2) h U) (hcrit : ∀ b ∈ U, fderiv ℝ (fun v ↦ f (b, v)) (h b) = 0)
    (hH : (fderiv ℝ (fderiv ℝ (fun v ↦ f (a, v))) (h a)).IsInvertible) (hn : n ≠ 0) :
    ∃ (ψ : OpenPartialHomeomorph (P × F) (P × F)) (U' : Set P) (V : Set F),
      IsOpen U' ∧ IsOpen V ∧ a ∈ U' ∧ (0 : F) ∈ V ∧ U' ⊆ U ∧
      ψ.source = {z | z.1 ∈ U' ∧ z.2 - h z.1 ∈ V} ∧ ψ.source ⊆ W ∧
      (∀ z, (ψ z).1 = z.1) ∧ (∀ b, ψ (b, h b) = (b, 0)) ∧
      (∀ z ∈ ψ.target, (ψ.symm z).1 = z.1) ∧
      ContDiffOn ℝ n ψ ψ.source ∧ ContDiffOn ℝ n ψ.symm ψ.target ∧
      ∀ z ∈ ψ.source, f z = f (z.1, h z.1) + (2 : ℝ)⁻¹ *
        fderiv ℝ (fderiv ℝ (fun v ↦ f (z.1, v))) (h z.1) (ψ z).2 (ψ z).2 := by
  obtain ⟨ψ₀, U₁, V, hU₁, hV, haU₁, h0V, hU₁U, hsource, hUVW, hψfst, hψ0, hψsymm, hψ, hψinv, -, -,
    hψf⟩ := exists_shifted_parametric_morse_chart hW hf hU haU hh hcrit hH hn
  obtain ⟨ψ, hsrc, hW', hfst, hgraph, hsymm, hC, hCinv, hψf'⟩ :=
    exists_shear_trans hU (hh.of_le le_self_add) ψ₀ hU₁U hsource hψfst hψ0 hψsymm hψ hψinv
      (fun z hz ↦ hUVW z (hsource ▸ hz))
      (fun b y ↦ (2 : ℝ)⁻¹ * fderiv ℝ (fderiv ℝ (fun v ↦ f (b, v))) (h b) y y) hψf
  exact ⟨ψ, U₁, V, hU₁, hV, haU₁, h0V, hU₁U, hsrc, hW', hfst, hgraph, hsymm, hC, hCinv, hψf'⟩

/-- **The normalized splitting lemma in product coordinates.** Under the hypotheses of
`TauCeti.exists_splitting_chart_of_contDiffOn`, there is a `C^n` chart `ψ` from a neighbourhood of
`(a, h a)` in `W` onto an open subset of `P × ℝᵐ`, `m = dim F`, preserving the base parameter in
both directions and sending the graph of `h` to the zero section, in which

`f z = f (z.1, h z.1) - Σ_{i < λ} (ψ z).2ᵢ² + Σ_{i ≥ λ} (ψ z).2ᵢ²`

on the whole source, where `λ` is the Morse index of `v ↦ f (a, v)` at `h a`. Its source is the
set of points `z` with `z.1 ∈ U'` and `z.2 - h z.1 ∈ V`, for open neighbourhoods `U' ⊆ U` of `a`
and `V` of `0`. -/
theorem exists_normalized_splitting_chart_of_contDiffOn (hW : W ∈ 𝓝 (a, h a))
    (hf : ContDiffOn ℝ (n + 2) f W) (hU : IsOpen U) (haU : a ∈ U)
    (hh : ContDiffOn ℝ (n + 2) h U) (hcrit : ∀ b ∈ U, fderiv ℝ (fun v ↦ f (b, v)) (h b) = 0)
    (hH : (fderiv ℝ (fderiv ℝ (fun v ↦ f (a, v))) (h a)).IsInvertible) (hn : n ≠ 0) :
    ∃ (ψ : OpenPartialHomeomorph (P × F) (P × EuclideanSpace ℝ (Fin (Module.finrank ℝ F))))
      (U' : Set P) (V : Set F),
      IsOpen U' ∧ IsOpen V ∧ a ∈ U' ∧ (0 : F) ∈ V ∧ U' ⊆ U ∧
      ψ.source = {z | z.1 ∈ U' ∧ z.2 - h z.1 ∈ V} ∧ ψ.source ⊆ W ∧
      (∀ z, (ψ z).1 = z.1) ∧ (∀ b, ψ (b, h b) = (b, 0)) ∧
      (∀ z ∈ ψ.target, (ψ.symm z).1 = z.1) ∧
      ContDiffOn ℝ n ψ ψ.source ∧ ContDiffOn ℝ n ψ.symm ψ.target ∧
      ∀ z ∈ ψ.source, f z = f (z.1, h z.1) + ∑ i,
        (if i.val < morseIndex (fun v ↦ f (a, v)) (h a) then -1 else 1) * (ψ z).2 i ^ 2 := by
  obtain ⟨ψ₀, U₁, V, hU₁, hV, haU₁, h0V, hU₁U, hsource, hUVW, hψfst, hψ0, hψsymm, hψ, hψinv, hgC,
    hgH, hψf⟩ := exists_shifted_parametric_morse_chart hW hf hU haU hh hcrit hH hn
  -- Normalize the fibre form of the chart of the shifted family.
  obtain ⟨ψ', U₂, hU₂, haU₂, hU₂U₁, hsource', hψ'fst, hψ'0, hψ'symm, hψ', hψ'inv, hψ'g⟩ :=
    ψ₀.exists_normalized_morseBott_chart (c := 0) hU₁ haU₁ hsource hψfst hψ0 hψsymm hψ hψinv hgC
      hgH fun z hz ↦ by dsimp only; rw [zero_add, fderiv_fderiv_shift, zero_add]; exact hψf z hz
  have hidx : morseIndex (fun v ↦ f (a, v + h a) - f (a, h a)) 0 =
      morseIndex (fun v ↦ f (a, v)) (h a) := by
    rw [morseIndex_def, morseIndex_def, hessianQuadraticForm_def, hessianQuadraticForm_def,
      fderiv_fderiv_shift, zero_add]
  -- Move the graph of `h` to the zero section.
  obtain ⟨ψ, hsrc, hW', hfst, hgraph, hsymm, hC, hCinv, hψf'⟩ :=
    exists_shear_trans hU (hh.of_le le_self_add) ψ' (hU₂U₁.trans hU₁U) hsource' hψ'fst hψ'0
      hψ'symm hψ' hψ'inv
      (fun z hz ↦ hUVW z (by rw [hsource'] at hz; exact ⟨hU₂U₁ hz.1, hz.2⟩))
      (fun _ y ↦ ∑ i,
        (if i.val < morseIndex (fun v ↦ f (a, v)) (h a) then -1 else 1) * y i ^ 2)
      fun z hz ↦ by
        have hz' := hψ'g z hz
        dsimp only at hz'
        rwa [hidx, zero_add] at hz'
  exact ⟨ψ, U₂, V, hU₂, hV, haU₂, h0V, hU₂U₁.trans hU₁U, hsrc, hW', hfst, hgraph, hsymm, hC,
    hCinv, hψf'⟩

end TauCeti

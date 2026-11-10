/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.NormalForm
public import TauCeti.Analysis.Calculus.Morse.Parametric
import TauCeti.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# The local Morse lemma

`TauCeti.IsNondegenerateCriticalPoint.exists_morse_chart` puts a globally `C^{n+2}` function in
quadratic normal form in `C^n` coordinates, for `1 ≤ n ≤ ∞`, near a nondegenerate critical
point. The normal form only depends on the function near the point, and this file states it
for a function that is `C^{n+2}` on a neighbourhood of the critical point only. This is the form
in which the Morse lemma applies to the coordinate expressions of a function on a manifold,
which are only defined on chart targets.

The same localization applies to the parametric Morse lemma
`TauCeti.exists_parametric_morse_chart`, for a family `f (b, v)` which is `C^{n+2}` only near a
point `(a, 0)` of its zero section. This is the form in which it applies to the coordinate
expressions of a function near a critical submanifold.

## Main declarations

* `TauCeti.IsNondegenerateCriticalPoint.exists_morse_chart_of_contDiffOn`: the Morse lemma for a
  function `C^{n+2}` on a neighbourhood of a nondegenerate critical point, with a `C^n` chart whose
  source lies in that neighbourhood.
* `TauCeti.exists_parametric_morse_chart_of_contDiffOn`: the parametric Morse lemma for a family
  `C^{n+2}` on a neighbourhood of a point of its critical zero section, with a fibred `C^n` chart
  whose source lies in that neighbourhood.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Theorem 1.3.1.
-/

public section

open Set Topology
open scoped ContDiff

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {g : E → ℝ} {a : E} {U : Set E} {n : ℕ∞}

/-- **The local Morse lemma.** If `g` is `C^{n+2}` on a
neighbourhood `U` of a nondegenerate critical point `a`, with `1 ≤ n ≤ ∞`, there is a chart `ψ`
with source in `U`, sending `a` to `0`, `C^n` in both directions, on whose source `g` is its
Hessian quadratic form read in the chart. -/
theorem IsNondegenerateCriticalPoint.exists_morse_chart_of_contDiffOn (hU : U ∈ 𝓝 a)
    (hg : ContDiffOn ℝ (n + 2) g U) (h : IsNondegenerateCriticalPoint g a) (hn : n ≠ 0) :
    ∃ ψ : OpenPartialHomeomorph E E, ψ.source ⊆ U ∧ a ∈ ψ.source ∧ ψ a = 0 ∧
      ContDiffOn ℝ n ψ ψ.source ∧ ContDiffOn ℝ n ψ.symm ψ.target ∧
      ∀ y ∈ ψ.source, g y = g a + (2 : ℝ)⁻¹ * fderiv ℝ (fderiv ℝ g) a (ψ y) (ψ y) := by
  obtain ⟨G, hG, -, hGg⟩ := hg.exists_contDiff_eventuallyEq_of_finiteDimensional hU
  obtain ⟨V, hGV, hVopen, haV⟩ := _root_.eventually_nhds_iff.1 hGg
  obtain ⟨φ, haφ, hφa, hφ, hφsymm, hφG⟩ :=
    (h.congr_of_eventuallyEq hGg.symm).exists_morse_chart hG hn
  have hD : fderiv ℝ (fderiv ℝ G) a = fderiv ℝ (fderiv ℝ g) a := hGg.fderiv.fderiv_eq
  refine ⟨φ.restrOpen (V ∩ interior U) (hVopen.inter isOpen_interior), ?_, ?_, hφa, ?_, ?_, ?_⟩
  · intro y hy
    rw [OpenPartialHomeomorph.restrOpen_source] at hy
    exact interior_subset hy.2.2
  · rw [OpenPartialHomeomorph.restrOpen_source]
    exact ⟨haφ, haV, mem_interior_iff_mem_nhds.2 hU⟩
  · exact hφ.mono (by simp)
  · exact hφsymm.mono fun y hy ↦ hy.1
  · intro y hy
    rw [OpenPartialHomeomorph.restrOpen_source] at hy
    rw [← hGV y hy.2.1, ← hGV a haV, ← hD]
    exact hφG y hy.1

section Parametric

variable {P F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {f : P × F → ℝ} {b₀ : P} {W : Set (P × F)}

/-- **The local parametric Morse lemma.** If a family `f (b, v)` is `C^{n+2}` on a neighbourhood
`W` of `(b₀, 0)`, with `1 ≤ n ≤ ∞`, its zero section is critical in the fibre direction near
`b₀`, and its vertical Hessian at `b₀` is invertible, then there is a `C^n` chart `ψ` with
product source in `W`, preserving the base parameter in both directions and fixing the zero
section, on whose source `f` is its value on the zero section plus half the vertical Hessian read
in the chart. -/
theorem exists_parametric_morse_chart_of_contDiffOn (hW : W ∈ 𝓝 (b₀, 0))
    (hf : ContDiffOn ℝ (n + 2) f W)
    (hcrit : ∀ᶠ b in 𝓝 b₀, fderiv ℝ (fun v ↦ f (b, v)) 0 = 0)
    (hH : (fderiv ℝ (fderiv ℝ (fun v ↦ f (b₀, v))) 0).IsInvertible) (hn : n ≠ 0) :
    ∃ (ψ : OpenPartialHomeomorph (P × F) (P × F)) (U : Set P) (V : Set F),
      IsOpen U ∧ IsOpen V ∧ b₀ ∈ U ∧ (0 : F) ∈ V ∧ ψ.source = U ×ˢ V ∧ U ×ˢ V ⊆ W ∧
      (∀ z, (ψ z).1 = z.1) ∧ (∀ b, ψ (b, 0) = (b, 0)) ∧
      (∀ z ∈ ψ.target, (ψ.symm z).1 = z.1) ∧
      ContDiffOn ℝ n ψ ψ.source ∧ ContDiffOn ℝ n ψ.symm ψ.target ∧
      ∀ z ∈ ψ.source,
        f z = f (z.1, 0) + (2 : ℝ)⁻¹ *
          fderiv ℝ (fderiv ℝ (fun v ↦ f (z.1, v))) 0 (ψ z).2 (ψ z).2 := by
  obtain ⟨G, hG, -, hGf⟩ := hf.exists_contDiff_eventuallyEq_of_finiteDimensional hW
  -- A product neighbourhood of `(b₀, 0)` inside `W` on which `G` and `f` agree.
  have hmem : {z | G z = f z} ∩ interior W ∈ 𝓝 (b₀, (0 : F)) :=
    Filter.inter_mem hGf (interior_mem_nhds.mpr hW)
  obtain ⟨U₀, V₀, hU₀, hb₀U₀, hV₀, h0V₀, hUV₀⟩ := mem_nhds_prod_iff'.mp hmem
  -- On it, the fibre restrictions of `G` and `f` have the same germ at `0`.
  have hslice {b : P} (hb : b ∈ U₀) : (fun v ↦ G (b, v)) =ᶠ[𝓝 0] fun v ↦ f (b, v) :=
    Filter.mem_of_superset (hV₀.mem_nhds h0V₀) fun v hv ↦ (hUV₀ (mk_mem_prod hb hv)).1
  have hH' {b : P} (hb : b ∈ U₀) : fderiv ℝ (fderiv ℝ (fun v ↦ G (b, v))) 0 =
      fderiv ℝ (fderiv ℝ (fun v ↦ f (b, v))) 0 :=
    (hslice hb).fderiv.fderiv_eq
  have hcritG : ∀ᶠ b in 𝓝 b₀, fderiv ℝ (fun v ↦ G (b, v)) 0 = 0 := by
    filter_upwards [hcrit, hU₀.mem_nhds hb₀U₀] with b hb hbU₀
    rw [(hslice hbU₀).fderiv_eq, hb]
  obtain ⟨ψ, U, V, hU, hV, hb₀U, h0V, hsource, hψfst, hψ0, hψsymm, hψ, hψinv, hψG⟩ :=
    exists_parametric_morse_chart hG hcritG (hH' hb₀U₀ ▸ hH) hn
  let ψ' := ψ.restrOpen (U₀ ×ˢ V₀) (hU₀.prod hV₀)
  have hsource' : ψ'.source = (U ∩ U₀) ×ˢ (V ∩ V₀) := by
    rw [OpenPartialHomeomorph.restrOpen_source, hsource, prod_inter_prod]
  refine ⟨ψ', U ∩ U₀, V ∩ V₀, hU.inter hU₀, hV.inter hV₀, ⟨hb₀U, hb₀U₀⟩, ⟨h0V, h0V₀⟩,
    hsource', fun z hz ↦ interior_subset (hUV₀ ⟨hz.1.2, hz.2.2⟩).2, hψfst, hψ0,
    fun z hz ↦ hψsymm z hz.1, hψ.mono (by simp [ψ']), hψinv.mono fun z hz ↦ hz.1, ?_⟩
  intro z hz
  rw [hsource'] at hz
  have hz₀ : z ∈ U₀ ×ˢ V₀ := ⟨hz.1.2, hz.2.2⟩
  have hzψ : z ∈ ψ.source := hsource ▸ ⟨hz.1.1, hz.2.1⟩
  have hfz : G z = f z := (hUV₀ hz₀).1
  have hfz₀ : G (z.1, 0) = f (z.1, 0) := (hUV₀ (mk_mem_prod hz.1.2 h0V₀)).1
  rw [← hfz, ← hfz₀, ← hH' hz.1.2]
  exact hψG z hzψ

end Parametric

end TauCeti

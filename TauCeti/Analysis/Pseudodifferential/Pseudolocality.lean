/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Composition.Sobolev
public import TauCeti.Analysis.Sobolev.BesselPotential.Embedding

/-!
# Pseudolocality of pseudodifferential operators

Let `a` be a symbol of order `m` on `ℝⁿ` with compact spatial support, acting as the bounded
operator `Op(a) : H^t → H^{t - m}` on the Bessel-potential spaces `H^t = H^{t,2}(ℝⁿ; V)`
(`TauCeti.Symbol.quantizeSobolev`). Regularity of a distribution `v ∈ H^t` near a set `K` is
measured with cutoffs: `v` is `H^s` near `K` when `χ v ∈ H^s` for a compactly supported Schwartz
function `χ` equal to `1` on a neighbourhood of `K`.

A pseudodifferential operator is *pseudolocal*: near every point, `Op(a) v` is as regular as `v`,
up to the `m` derivatives that `Op(a)` loses. Its kernel is singular only on the diagonal, so
`Op(a)` creates no new singularities and does not move the existing ones. Since a
distribution lying in every `H^s` is a smooth function, `Op(a)` does not enlarge the singular
support. This file proves these statements on the Bessel-potential spaces:

* `TauCeti.Symbol.memSobolev_toDistr_quantizeSobolev_of_memSobolev_smulLeftCLM`: **locality**.
  If the symbol `c` vanishes at positions outside `K`, `χ = 1` on a neighbourhood of `K` and
  `χ v ∈ H^s`, then `Op(c) v ∈ H^{s - m}`, however irregular `v` is away from `K`.
* `TauCeti.Symbol.memSobolev_smulLeftCLM_quantizeSobolev_of_memSobolev_smulLeftCLM`:
  **pseudolocality**. If `χ = 1` on a neighbourhood of the support of `ψ` and `χ v ∈ H^s`, then
  `ψ Op(a) v ∈ H^{s - m}`: if `v` is `H^s` near a point, then `Op(a) v` is `H^{s - m}` near it.
* `TauCeti.Symbol.exists_contDiff_smulLeftCLM_quantizeSobolev_of_forall_memSobolev`: if `χ v`
  lies in every `H^s`, then `ψ Op(a) v` is a smooth function. So `Op(a) v` is smooth wherever `v`
  is.

## Proof outline

Locality modulo smoothing operators
(`TauCeti.Symbol.exists_isSmoothing_and_toDistr_quantizeSobolev_eq_quantizeSobolev_smulLeftCLM_add`)
writes `Op(c) v = Op(c) (χ v) + Op(e) v` with `e` smoothing. The first term lies in `H^{s - m}`
since `χ v ∈ H^s`, and the second one in every `H^r`. For pseudolocality, multiplication by `ψ`
is the quantization of the symbol `ψ(x)`, so `ψ Op(a) = Op(ψ # a)` by the composition theorem,
and `ψ # a = ψ a` vanishes at positions outside the support of `ψ`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1
  (pseudodifferential operators are pseudolocal).
* G. B. Folland, *Introduction to Partial Differential Equations*, 2nd ed., Princeton University
  Press, 1995, Chapter 8.
-/

public section

noncomputable section

open scoped SchwartzMap BesselPotentialSpace ContDiff Topology

namespace TauCeti

namespace Symbol

variable {n : ℕ} {m : ℝ} {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [CompleteSpace V] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]

/-- **Locality.** Let the symbol `c` with compact spatial support vanish at positions outside `K`,
and let the compactly supported Schwartz function `χ` equal `1` on a neighbourhood of `K`. If
`χ v ∈ H^s` for some `v ∈ H^t`, then `Op(c) v ∈ H^{s - m}`. -/
theorem memSobolev_toDistr_quantizeSobolev_of_memSobolev_smulLeftCLM {c : Symbol n V W m}
    (hc : c.HasCompactSpatialSupport) {K : Set (CoordinateSpace n)}
    (hcK : ∀ x ∉ K, ∀ ξ, c.coefficient (x, ξ) = 0) {χ : 𝓢(CoordinateSpace n, ℂ)}
    (hχ : HasCompactSupport χ) (hχK : ∀ᶠ x in 𝓝ˢ K, χ x = 1) {s t : ℝ}
    {v : H^{t}(CoordinateSpace n, V)}
    (hv : (BesselPotentialSpace.smulLeftCLM t χ v).toDistr.MemSobolev s 2) :
    (c.quantizeSobolev hc t v).toDistr.MemSobolev (s - m) 2 := by
  obtain ⟨e, he, hsm, hdec⟩ :=
    exists_isSmoothing_and_toDistr_quantizeSobolev_eq_quantizeSobolev_smulLeftCLM_add hc hcK hχ
      hχK
  rw [hdec t v, toDistr_quantizeSobolev_congr rfl hc hc (v := hv.toBesselPotentialSpace)
    hv.toBesselPotentialSpace_toDistr.symm]
  exact (BesselPotentialSpace.memSobolev_toDistr _).add
    (hsm.memSobolev_toDistr_quantizeSobolev he t _ v)

/-- **Pseudolocality.** Let `a` be a symbol of order `m` with compact spatial support, and let the
compactly supported Schwartz function `χ` equal `1` on a neighbourhood of the support of `ψ`. If
`χ v ∈ H^s` for some `v ∈ H^t`, then `ψ Op(a) v ∈ H^{s - m}`: where `v` is `H^s`, `Op(a) v` is
`H^{s - m}`. -/
theorem memSobolev_smulLeftCLM_quantizeSobolev_of_memSobolev_smulLeftCLM {a : Symbol n V W m}
    (ha : a.HasCompactSpatialSupport) {ψ χ : 𝓢(CoordinateSpace n, ℂ)} (hχ : HasCompactSupport χ)
    (hχψ : ∀ᶠ x in 𝓝ˢ (tsupport ψ), χ x = 1) {s t : ℝ} {v : H^{t}(CoordinateSpace n, V)}
    (hv : (BesselPotentialSpace.smulLeftCLM t χ v).toDistr.MemSobolev s 2) :
    (BesselPotentialSpace.smulLeftCLM (t - m) ψ (a.quantizeSobolev ha t v)).toDistr.MemSobolev
      (s - m) 2 := by
  have hψ : HasCompactSupport ψ :=
    hχ.of_forall_mem_support_eq_one fun x hx ↦ hχψ.self_of_nhdsSet x (subset_tsupport ψ hx)
  have hF := hasCompactSpatialSupport_ofSpatial_smul_id (V := W) hψ
  -- `ψ Op(a) = Op(ψ # a)`, and `ψ # a` vanishes outside the support of `ψ`.
  have h := memSobolev_toDistr_quantizeSobolev_of_memSobolev_smulLeftCLM (hF.sharp ha)
    (fun _ hx ↦ coefficient_ofSpatial_smul_id_sharp_eq_zero_of_notMem_tsupport ha hx) hχ hχψ hv
  rw [BesselPotentialSpace.toDistr_smulLeftCLM]
  rwa [← smulLeftCLM_toDistr_quantizeSobolev ha hF, zero_add] at h

/-- **Pseudodifferential operators do not enlarge the singular support.** Let `a` have compact
spatial support, and let the compactly supported Schwartz function `χ` equal `1` on a neighbourhood
of the support of `ψ`. If `χ v` lies in every `H^s`, then `ψ Op(a) v` is a smooth function `g`: it
pairs with every Schwartz function `φ` as `∫ φ • g`. -/
theorem exists_contDiff_smulLeftCLM_quantizeSobolev_of_forall_memSobolev {a : Symbol n V W m}
    (ha : a.HasCompactSpatialSupport) {ψ χ : 𝓢(CoordinateSpace n, ℂ)} (hχ : HasCompactSupport χ)
    (hχψ : ∀ᶠ x in 𝓝ˢ (tsupport ψ), χ x = 1) {t : ℝ} {v : H^{t}(CoordinateSpace n, V)}
    (hv : ∀ s, (BesselPotentialSpace.smulLeftCLM t χ v).toDistr.MemSobolev s 2) :
    ∃ g : CoordinateSpace n → W, ContDiff ℝ ∞ g ∧ ∀ φ : 𝓢(CoordinateSpace n, ℂ),
      (BesselPotentialSpace.smulLeftCLM (t - m) ψ (a.quantizeSobolev ha t v)).toDistr φ =
        ∫ x, φ x • g x :=
  TemperedDistribution.exists_contDiff_eq_integral_of_forall_memSobolev fun s ↦ by
    simpa using memSobolev_smulLeftCLM_quantizeSobolev_of_memSobolev_smulLeftCLM ha hχ hχψ
      (hv (s + m))

end Symbol

end TauCeti

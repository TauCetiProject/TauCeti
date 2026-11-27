/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import TauCeti.Analysis.Calculus.InverseFunctionTheorem
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
import TauCeti.Analysis.Analytic.Inverse
import TauCeti.Analysis.Calculus.FDeriv.Analytic
import TauCeti.Analysis.Calculus.FDeriv.Dimension
import TauCeti.Analysis.Calculus.MeanValue
import TauCeti.Analysis.Normed.Module.ContinuousInverse
import TauCeti.LinearAlgebra.LinearMap.PseudoInverse
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.IdempotentRange

/-!
# The constant rank theorem

Let `f : E → F` be a `C^n` map, `1 ≤ n`, on an open subset `s` of a finite-dimensional space `E`
over `ℝ` or `ℂ`, with values in a Banach space `F`, and let `a ∈ s`. If the rank of the derivative
of `f` does not exceed its rank at `a` anywhere on `s` (for instance if the rank is constant on
`s`), then near `a` and `f a` there are `C^n` coordinates, tangent to the identity, in which `f`
*is its own derivative* `L = Df(a)`:
`ψ (f x) = L (φ x)` for every `x` near `a`.

Choosing a basis of `E` adapted to `ker L` and a basis of `F` extending a basis of the range of
`L`, the linear map `L` reads `(u, v) ↦ (u, 0)`, which is the classical normal form of a map of
constant rank. The derivative of a `C^1` map at nearby points can only have larger rank, so on a
small enough neighbourhood the hypothesis is equivalent to the rank being constant. This is the
local form underlying the rank theorem for maps between manifolds.

Since `ψ` is injective near `f a`, the level set of `f` through `a` is, near `a`, the preimage
under the chart `φ` of the linear subspace `ker L`; this gives the level sets of a constant rank map
their local structure of submanifolds of dimension `dim E - rank L`.

The same holds for analytic maps from a Banach space to a finite-dimensional space over a complete
nontrivially normed field of characteristic zero, such as `ℚ_p`, with analytic charts with analytic
inverses.
Characteristic zero is essential: over a field of characteristic `p`, the map `z ↦ z ^ p` has
derivative zero everywhere, hence constant rank `0`, but is not locally constant. The target is
finite-dimensional because a finite-dimensional subspace of a Banach space over a nonarchimedean
field need not have a closed complement, so the derivative need not have a continuous
pseudo-inverse.

## Main results

* `ContDiffOn.exists_openPartialHomeomorph_comp_eq_fderiv_comp`: the constant rank theorem. Near
  `a` and `f a` there are charts `φ` and `ψ`, `C^n` with `C^n` inverses, sending `a` and `f a` to
  `0` with derivative the identity there, such that `ψ ∘ f = Df(a) ∘ φ` near `a`.
* `ContDiffOn.exists_openPartialHomeomorph_apply_eq_iff_mem_ker`: near `a`, the level set of `f`
  through `a` is the preimage under a chart `φ` of the kernel of `Df(a)`.
* `AnalyticOnNhd.exists_openPartialHomeomorph_comp_eq_fderiv_comp`: the analytic constant rank
  theorem over a complete field of characteristic zero, with analytic charts.
* `AnalyticOnNhd.exists_openPartialHomeomorph_apply_eq_iff_mem_ker`: the analytic level set
  version.

## Implementation notes

Let `T` be a continuous pseudo-inverse of `L = Df(a)` (`L ∘ T ∘ L = L`). Then `P = L ∘ T` is a
projection onto the range of `L` and `Q = 1 - T ∘ L` is a projection onto `ker L`. The first chart
is `φ x = T (f x - f a) + Q (x - a)`, whose derivative at `a` is the identity; it satisfies
`L (φ x) = P (f x - f a)`. In this chart `g z = f (φ⁻¹ z) - f a` satisfies `P ∘ g = L`, so the
derivative of `g` maps `E` onto the range of `L` after projecting with `P`; as it has rank at most
`rank L`, its kernel is that of `L` (`HasFDerivAt.apply_eq_zero_iff_of_comp_eventuallyEq`).
Hence, by the mean value theorem along segments parallel to `ker L`
(`TauCeti.apply_add_eq_of_fderiv_apply_eq_zero`), near `0` the value `g z` only depends on the
component of `z` in `range (T ∘ L)` for the decomposition `E = range (T ∘ L) ⊕ ker L`, and the
second chart `ψ w = (w - f a) - (1 - P) (g (c w))`, where
`c = T ∘ L ∘ T (· - f a)`, removes the component of `f` transverse to the range of `L`.

In the analytic case, `T` is any linear pseudo-inverse, continuous because `F` is
finite-dimensional, the charts come from the analytic inverse function theorem
(`AnalyticAt.exists_openPartialHomeomorph`), and the mean value theorem, unavailable over
nonarchimedean fields, is replaced by the power series of `g` at `0`: in characteristic zero, an
analytic function stationary along `ker L` factors through the projection `T ∘ L` on a
neighbourhood of `0`, where `‖(T ∘ L) z‖ₑ + ‖z - (T ∘ L) z‖ₑ` is below the radius of convergence
(`HasFPowerSeriesOnBall.apply_proj_eq_of_fderiv_apply_eq_zero`).

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Theorem 4.12 (the rank theorem).
* S. Lang, *Fundamentals of Differential Geometry*, Graduate Texts in Mathematics 191, Springer,
  1999, Chapter I, §5 (the constant rank theorem in Banach spaces).
* P. Schneider, *p-Adic Lie Groups*, Grundlehren der mathematischen Wissenschaften 344, Springer,
  2011, §5, Corollary 5.8 and Proposition 5.9, and §9, Proposition 9.3 (the analytic setting).
-/

public section

open Filter Set Module
open scoped Topology

section Charts

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The first chart of the constant rank theorem is tangent to the identity: if `T` is a
pseudo-inverse of the derivative `L` of `f` at `a`, then `x ↦ T (f x - f a) + (1 - T ∘ L) (x - a)`
has derivative the identity at `a`. -/
private theorem HasFDerivAt.add_sub_comp_pseudoInverse {f : E → F} {L : E →L[𝕜] F}
    {T : F →L[𝕜] E} {a : E} (hf : HasFDerivAt f L a) :
    HasFDerivAt (fun x ↦ T (f x - f a) + (ContinuousLinearMap.id 𝕜 E - T ∘L L) (x - a))
      (ContinuousLinearMap.id 𝕜 E) a := by
  have h := (T.hasFDerivAt.comp a (hf.sub_const (f a))).add
    ((ContinuousLinearMap.id 𝕜 E - T ∘L L).hasFDerivAt.comp a ((hasFDerivAt_id a).sub_const a))
  refine h.congr_fderiv ?_
  ext v
  simp

/-- The second chart of the constant rank theorem is tangent to the identity: if `T` is a
pseudo-inverse of `L` and `g` has derivative `L` at `0`, then
`w ↦ (w - b) - (1 - L ∘ T) (g (T (L (T (w - b)))))` has derivative the identity at `b`. -/
private theorem hasFDerivAt_sub_sub_comp_pseudoInverse {g : E → F} {L : E →L[𝕜] F}
    {T : F →L[𝕜] E} (hT : L ∘L T ∘L L = L) (hg : HasFDerivAt g L 0) (b : F) :
    HasFDerivAt (fun w ↦ (w - b) - (ContinuousLinearMap.id 𝕜 F - L ∘L T)
      (g ((T ∘L L) (T (w - b))))) (ContinuousLinearMap.id 𝕜 F) b := by
  have hT' (v : E) : L (T (L v)) = L v := by simpa using congr($hT v)
  have hc : HasFDerivAt (fun w ↦ (T ∘L L) (T (w - b))) ((T ∘L L) ∘L T) b :=
    (T ∘L L).hasFDerivAt.comp b (T.hasFDerivAt.comp b ((hasFDerivAt_id b).sub_const b))
  have hg' : HasFDerivAt g L ((T ∘L L) (T (b - b))) := by simpa using hg
  have h := ((hasFDerivAt_id b).sub_const b).sub
    ((ContinuousLinearMap.id 𝕜 F - L ∘L T).hasFDerivAt.comp b (hg'.comp b hc))
  refine h.congr_fderiv ?_
  ext w
  simp [hT']

/-- If a local homeomorphism `Φ` has derivative the identity at `a` and sends `a` to `0`, then in
the chart `Φ` the map `z ↦ f (Φ⁻¹ z) - f a` has at `0` the derivative `L` of `f` at `a`. -/
private theorem hasFDerivAt_comp_symm_sub {f : E → F} {L : E →L[𝕜] F} {a : E}
    {Φ : OpenPartialHomeomorph E E} (h0 : 0 ∈ Φ.target) (hΦa : Φ.symm 0 = a)
    (hΦ : HasFDerivAt Φ (ContinuousLinearMap.id 𝕜 E) a) (hf : HasFDerivAt f L a) :
    HasFDerivAt (fun z ↦ f (Φ.symm z) - f a) L 0 := by
  have hsymm : HasFDerivAt Φ.symm (ContinuousLinearMap.id 𝕜 E) 0 := by
    simpa using Φ.hasFDerivAt_symm h0 (f' := ContinuousLinearEquiv.refl 𝕜 E)
      (by rw [hΦa]; exact hΦ)
  rw [← hΦa] at hf
  simpa using (hf.comp 0 hsymm).sub_const (f a)

/-- In a first chart `Φ` of the constant rank theorem, with `L ∘ Φ = L ∘ T (f - f a)` for a
pseudo-inverse `T` of `L`, the map `z ↦ f (Φ⁻¹ z) - f a` is stationary along `ker L` at every
point of the target where `Df` has rank at most that of `L`: its composite with the projection
`L ∘ T` is `L`, and projecting the range of its derivative does not lower its dimension. -/
private theorem fderiv_comp_symm_apply_eq_zero {f : E → F}
    {L : E →L[𝕜] F} {T : F →L[𝕜] E} {a : E} {Φ : OpenPartialHomeomorph E E}
    (hLΦ : ∀ x, L (Φ x) = L (T (f x - f a))) {z : E} (hz : z ∈ Φ.target)
    (hf : DifferentiableAt 𝕜 f (Φ.symm z)) (hΦ : DifferentiableAt 𝕜 Φ.symm z)
    [FiniteDimensional 𝕜 (LinearMap.range (fderiv 𝕜 f (Φ.symm z)).toLinearMap)]
    (hrank : finrank 𝕜 (LinearMap.range (fderiv 𝕜 f (Φ.symm z)).toLinearMap) ≤
      finrank 𝕜 (LinearMap.range L.toLinearMap)) {v : E} (hv : L v = 0) :
    fderiv 𝕜 (fun z ↦ f (Φ.symm z) - f a) z v = 0 := by
  have hgd : HasFDerivAt (fun z ↦ f (Φ.symm z) - f a)
      (fderiv 𝕜 f (Φ.symm z) ∘L fderiv 𝕜 Φ.symm z) z :=
    (hf.hasFDerivAt.comp z hΦ.hasFDerivAt).sub_const (f a)
  have hle := LinearMap.range_comp_le_range (fderiv 𝕜 Φ.symm z : E →ₗ[𝕜] E)
    (fderiv 𝕜 f (Φ.symm z) : E →ₗ[𝕜] F)
  have : FiniteDimensional 𝕜
      (LinearMap.range (fderiv 𝕜 f (Φ.symm z) ∘L fderiv 𝕜 Φ.symm z).toLinearMap) :=
    Submodule.finiteDimensional_of_le hle
  rw [hgd.fderiv]
  refine (hgd.apply_eq_zero_iff_of_comp_eventuallyEq (P := L ∘L T)
    (eventually_of_mem (Φ.open_target.mem_nhds hz) fun w hw ↦ ?_) ?_).2 hv
  · simp only [ContinuousLinearMap.comp_apply]
    rw [← hLΦ, Φ.right_inv hw]
  · exact (Submodule.finrank_mono hle).trans hrank

/-- The first chart of the constant rank theorem only changes `f` along `ker L`: if `T` is a
pseudo-inverse of `L`, then `L (T w + (1 - T ∘ L) u) = L (T w)`. -/
private theorem apply_add_sub_comp_pseudoInverse {L : E →L[𝕜] F} {T : F →L[𝕜] E}
    (hT : L ∘L T ∘L L = L) (w : F) (u : E) :
    L (T w + (ContinuousLinearMap.id 𝕜 E - T ∘L L) u) = L (T w) := by
  have hT' (v : E) : L (T (L v)) = L v := by simpa using congr($hT v)
  simp [hT']

/-- **Shrinking the charts of the constant rank theorem.** Let
`Φ x = T (f x - f a) + (1 - T ∘ L) (x - a)` and
`Ψ w = (w - f a) - (1 - L ∘ T) (g (T (L (T (w - f a)))))`, where `g z = f (Φ⁻¹ z) - f a`, be the
two charts, and let `U` be an open neighbourhood of `Φ a` on which `g` factors through `T ∘ L`.
Then on an open neighbourhood `V` of `a`, `f` maps `V` to the source of `Ψ` and
`Ψ (f x) = L (Φ x)`. -/
private theorem exists_isOpen_apply_eq_apply {f : E → F} {L : E →L[𝕜] F} {T : F →L[𝕜] E} {a : E}
    {s : Set E} {Φ : OpenPartialHomeomorph E E} {Ψ : OpenPartialHomeomorph F F}
    (hT : L ∘L T ∘L L = L) (hf : ContinuousOn f s) (hΦs : Φ.source ⊆ s) (ha : a ∈ Φ.source)
    (hfa : f a ∈ Ψ.source) (U : Set E) (hU : IsOpen U) (haU : Φ a ∈ U)
    (hΦ : ∀ x, Φ x = T (f x - f a) + (ContinuousLinearMap.id 𝕜 E - T ∘L L) (x - a))
    (hΨ : ∀ w, Ψ w = (w - f a) - (ContinuousLinearMap.id 𝕜 F - L ∘L T)
      (f (Φ.symm ((T ∘L L) (T (w - f a)))) - f a))
    (hgU : ∀ z ∈ U, f (Φ.symm ((T ∘L L) z)) - f a = f (Φ.symm z) - f a) :
    ∃ V : Set E, IsOpen V ∧ a ∈ V ∧ MapsTo f V Ψ.source ∧ ∀ x ∈ V, Ψ (f x) = L (Φ x) := by
  refine ⟨(Φ.source ∩ Φ ⁻¹' U) ∩ f ⁻¹' Ψ.source,
    ((hf.mono hΦs).mono inter_subset_left).isOpen_inter_preimage (Φ.isOpen_inter_preimage hU)
      Ψ.open_source, ⟨⟨ha, haU⟩, hfa⟩, fun x hx ↦ hx.2, fun x hx ↦ ?_⟩
  obtain ⟨⟨hxΦ, hxU⟩, -⟩ := hx
  /- `T (L (T (f x - f a))) = T (L (Φ x))` and `g` does not see the `ker L` component of `Φ x`,
  so `Ψ (f x) = L (T (f x - f a)) = L (Φ x)`. -/
  have hT' (v : E) : L (T (L v)) = L v := by simpa using congr($hT v)
  have hcx : (T ∘L L) (T (f x - f a)) = (T ∘L L) (Φ x) := by simp [hΦ, hT']
  rw [hΨ, hcx, hgU _ hxU, Φ.left_inv hxΦ, hΦ, apply_add_sub_comp_pseudoInverse hT]
  simp

/-- In charts `φ` and `ψ` in which `f` is the linear map `L`, the level set of `f` through `a` is
the preimage of `ker L` under `φ`. -/
private theorem apply_eq_iff_mem_ker_of_apply_eq_apply {f : E → F} {L : E →L[𝕜] F} {a : E}
    {φ : OpenPartialHomeomorph E E} {ψ : OpenPartialHomeomorph F F} (ha : a ∈ φ.source)
    (hψa : ψ (f a) = 0) (hmaps : MapsTo f φ.source ψ.source)
    (hψf : ∀ x ∈ φ.source, ψ (f x) = L (φ x)) {x : E} (hx : x ∈ φ.source) :
    f x = f a ↔ φ x ∈ LinearMap.ker L.toLinearMap := by
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, ← hψf x hx, ← hψa]
  exact (ψ.injOn.eq_iff (hmaps hx) (hmaps ha)).symm

end Charts

section RCLike

variable {𝕂 : Type*} [RCLike 𝕂]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕂 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕂 F]

variable [FiniteDimensional 𝕂 E] [CompleteSpace F] {n : WithTop ℕ∞} {f : E → F} {s : Set E}
  {a : E}

/-- **The constant rank theorem.** Let `f` be `C^n`, `1 ≤ n`, on an open subset `s` of a
finite-dimensional space, with values in a Banach space, and assume that the rank of `Df` on `s`
never exceeds its rank at `a ∈ s` (for instance, that it is constant on `s`). Then there are
charts `φ` of `E` near `a` and `ψ` of `F` near `f a`, `C^n` with `C^n` inverses, sending `a` and
`f a` to `0` with derivative the identity there, in which `f` is its derivative `L = Df(a)`:
`ψ (f x) = L (φ x)` for every `x` in the source of `φ`, a neighbourhood of `a` inside `s`. -/
theorem ContDiffOn.exists_openPartialHomeomorph_comp_eq_fderiv_comp (hf : ContDiffOn 𝕂 n f s)
    (hs : IsOpen s) (ha : a ∈ s) (hn : 1 ≤ n)
    (hrank : ∀ x ∈ s, finrank 𝕂 (LinearMap.range (fderiv 𝕂 f x).toLinearMap) ≤
      finrank 𝕂 (LinearMap.range (fderiv 𝕂 f a).toLinearMap)) :
    ∃ (φ : OpenPartialHomeomorph E E) (ψ : OpenPartialHomeomorph F F),
      a ∈ φ.source ∧ φ.source ⊆ s ∧ φ a = 0 ∧ HasFDerivAt φ (ContinuousLinearMap.id 𝕂 E) a ∧
      ContDiffOn 𝕂 n φ φ.source ∧ ContDiffOn 𝕂 n φ.symm φ.target ∧
      ψ (f a) = 0 ∧ HasFDerivAt ψ (ContinuousLinearMap.id 𝕂 F) (f a) ∧
      ContDiffOn 𝕂 n ψ ψ.source ∧ ContDiffOn 𝕂 n ψ.symm ψ.target ∧
      MapsTo f φ.source ψ.source ∧ ∀ x ∈ φ.source, ψ (f x) = fderiv 𝕂 f a (φ x) := by
  have hn0 : n ≠ 0 := by rintro rfl; exact absurd hn (by simp)
  have : CompleteSpace E := FiniteDimensional.completeSpace 𝕂 E
  have hfd : ∀ x ∈ s, HasFDerivAt f (fderiv 𝕂 f x) x := fun x hx ↦
    ((hf.differentiableOn hn0).differentiableAt (hs.mem_nhds hx)).hasFDerivAt
  set L := fderiv 𝕂 f a
  /- Linear algebra: a pseudo-inverse `T` of `L`, the projection `P = L ∘ T` onto the range of `L`,
  and the complementary projections `π = T ∘ L` and `Q = 1 - π` of `E`, the latter onto `ker L`. -/
  obtain ⟨T, hT⟩ := L.exists_comp_comp_eq_self
  have hT' (v : E) : L (T (L v)) = L v := by simpa using congr($hT v)
  set π : E →L[𝕂] E := T ∘L L with hπ
  have hπidem : IsIdempotentElem π :=
    ContinuousLinearMap.isIdempotentElem_comp_of_comp_comp_eq_self hT
  set Q : E →L[𝕂] E := ContinuousLinearMap.id 𝕂 E - π
  /- The first chart `φ₀ x = T (f x - f a) + Q (x - a)`, whose derivative at `a` is the identity,
  so that the inverse function theorem applies. -/
  set φ₀ : E → E := fun x ↦ T (f x - f a) + Q (x - a) with hφ₀
  have hφ₀s : ContDiffOn 𝕂 n φ₀ s :=
    (T.contDiff.comp_contDiffOn (hf.sub contDiffOn_const)).add
      (Q.contDiff.comp_contDiffOn (contDiffOn_id.sub contDiffOn_const))
  have hφ₀a : φ₀ a = 0 := by simp [hφ₀]
  have hφ₀d : HasFDerivAt φ₀ (ContinuousLinearMap.id 𝕂 E) a :=
    (hfd a ha).add_sub_comp_pseudoInverse
  have hLφ₀ (x : E) : L (φ₀ x) = L (T (f x - f a)) := apply_add_sub_comp_pseudoInverse hT _ _
  obtain ⟨Φ₀, hΦ₀, haΦ₀, hΦ₀s, hΦ₀symm⟩ := TauCeti.ContDiffOn.exists_openPartialHomeomorph hφ₀s hs
    ha hn (e := ContinuousLinearEquiv.refl 𝕂 E) (by simpa using hφ₀d.fderiv.symm)
  clear_value φ₀
  subst hΦ₀
  have h0Φ₀ : (0 : E) ∈ Φ₀.target := hφ₀a ▸ Φ₀.map_source haΦ₀
  have hΦ₀symm0 : Φ₀.symm 0 = a := by rw [← hφ₀a, Φ₀.left_inv haΦ₀]
  /- In the chart `Φ₀`, the map `g z = f (Φ₀⁻¹ z) - f a` satisfies `P ∘ g = L`. -/
  set g : E → F := fun z ↦ f (Φ₀.symm z) - f a with hg
  have hgC : ContDiffOn 𝕂 n g Φ₀.target :=
    (hf.comp hΦ₀symm fun z hz ↦ hΦ₀s (Φ₀.map_target hz)).sub contDiffOn_const
  /- The derivative of `g` has rank at most that of `L` and becomes `L` after projecting with
  `P = L ∘ T`, so its kernel is `ker L`: `g` is stationary along `ker L`. -/
  have hker : ∀ z ∈ Φ₀.target, ∀ v : E, L v = 0 → fderiv 𝕂 g z v = 0 := fun z hz _ hv ↦
    fderiv_comp_symm_apply_eq_zero hLφ₀ hz
      (hfd _ (hΦ₀s (Φ₀.map_target hz))).differentiableAt
      ((hΦ₀symm.differentiableOn hn0).differentiableAt (Φ₀.open_target.mem_nhds hz))
      (hrank _ (hΦ₀s (Φ₀.map_target hz))) hv
  /- Hence `g` only depends on the `range π` component on a neighbourhood of `0`. -/
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (Φ₀.open_target.mem_nhds h0Φ₀)
  have hgπ : ∀ z, ‖π z‖ + ‖z - π z‖ < ε → g (π z) = g z := fun z hz ↦
    TauCeti.apply_proj_eq_of_fderiv_apply_eq_zero hπidem ((hgC.differentiableOn hn0).mono hball)
      (fun u hu v hv ↦ hker u (hball hu) v (by simpa [hπ, hT'] using congrArg L hv)) hz
  /- The second chart `ψ w = (w - f a) - (1 - P) (g (c w))` with `c w = π (T (w - f a))`. -/
  set c : F → E := fun w ↦ π (T (w - f a)) with hc
  set R : F →L[𝕂] F := ContinuousLinearMap.id 𝕂 F - L ∘L T
  set ψ₀ : F → F := fun w ↦ (w - f a) - R (g (c w)) with hψ₀
  set W : Set F := c ⁻¹' Φ₀.target with hW
  have hc_cont : Continuous c :=
    π.continuous.comp (T.continuous.comp (continuous_id.sub continuous_const))
  have hWopen : IsOpen W := Φ₀.open_target.preimage hc_cont
  have hc0 : c (f a) = 0 := by simp [hc]
  have hfaW : f a ∈ W := by simp [hW, hc0, h0Φ₀]
  have hψ₀C : ContDiffOn 𝕂 n ψ₀ W := by
    have hcC : ContDiff 𝕂 n c :=
      π.contDiff.comp (T.contDiff.comp (contDiff_id.sub contDiff_const))
    exact (contDiffOn_id.sub contDiffOn_const).sub
      (R.contDiff.comp_contDiffOn (hgC.comp hcC.contDiffOn fun w hw ↦ hw))
  have hψ₀a : ψ₀ (f a) = 0 := by simp [hψ₀, hc0, hg, hΦ₀symm0]
  have hψ₀d : HasFDerivAt ψ₀ (ContinuousLinearMap.id 𝕂 F) (f a) :=
    hasFDerivAt_sub_sub_comp_pseudoInverse hT
      (hasFDerivAt_comp_symm_sub h0Φ₀ hΦ₀symm0 hφ₀d (hfd a ha)) (f a)
  obtain ⟨Ψ, hΨ, hfaΨ, hΨW, hΨsymm⟩ := TauCeti.ContDiffOn.exists_openPartialHomeomorph hψ₀C hWopen
    hfaW hn (e := ContinuousLinearEquiv.refl 𝕂 F) (by simpa using hψ₀d.fderiv.symm)
  clear_value ψ₀
  subst hΨ
  /- Shrink the first chart so that `hgπ` applies on its image and `f` lands in the source of
  the second chart, where `ψ₀ (f x) = P (f x - f a) = L (φ₀ x)`. -/
  obtain ⟨V, hVopen, haV, hVΨ, hVf⟩ := exists_isOpen_apply_eq_apply hT hf.continuousOn hΦ₀s haΦ₀
    hfaΨ {z | ‖π z‖ + ‖z - π z‖ < ε} (isOpen_lt (by fun_prop) continuous_const)
    (by simp [hφ₀a, hε]) (congrFun hφ₀) (congrFun hψ₀) hgπ
  exact ⟨Φ₀.restrOpen V hVopen, Ψ, ⟨haΦ₀, haV⟩, fun x hx ↦ hΦ₀s hx.1, hφ₀a, hφ₀d,
    hφ₀s.mono fun x hx ↦ hΦ₀s hx.1, hΦ₀symm.mono fun z hz ↦ hz.1, hψ₀a, hψ₀d,
    hψ₀C.mono hΨW, hΨsymm, fun x hx ↦ hVΨ hx.2, fun x hx ↦ hVf x hx.2⟩

/-- **Level sets of a map of constant rank.** Under the hypotheses of the constant rank theorem,
there is a chart `φ` of `E` near `a`, inside `s`, `C^n` with `C^n` inverse, sending `a` to `0`
with derivative the identity there, in which the level set of `f` through `a` is the kernel of
`Df(a)`: for `x` in the source of `φ`, `f x = f a` exactly when `φ x ∈ ker Df(a)`. -/
theorem ContDiffOn.exists_openPartialHomeomorph_apply_eq_iff_mem_ker (hf : ContDiffOn 𝕂 n f s)
    (hs : IsOpen s) (ha : a ∈ s) (hn : 1 ≤ n)
    (hrank : ∀ x ∈ s, finrank 𝕂 (LinearMap.range (fderiv 𝕂 f x).toLinearMap) ≤
      finrank 𝕂 (LinearMap.range (fderiv 𝕂 f a).toLinearMap)) :
    ∃ φ : OpenPartialHomeomorph E E,
      a ∈ φ.source ∧ φ.source ⊆ s ∧ φ a = 0 ∧ HasFDerivAt φ (ContinuousLinearMap.id 𝕂 E) a ∧
      ContDiffOn 𝕂 n φ φ.source ∧ ContDiffOn 𝕂 n φ.symm φ.target ∧
      ∀ x ∈ φ.source, f x = f a ↔ φ x ∈ LinearMap.ker (fderiv 𝕂 f a).toLinearMap := by
  obtain ⟨φ, ψ, haφ, hφs, hφa, hφd, hφC, hφsymm, hψa, -, -, -, hmaps, hψf⟩ :=
    hf.exists_openPartialHomeomorph_comp_eq_fderiv_comp hs ha hn hrank
  exact ⟨φ, haφ, hφs, hφa, hφd, hφC, hφsymm,
    fun _ ↦ apply_eq_iff_mem_ker_of_apply_eq_apply haφ hψa hmaps hψf⟩

end RCLike

section Analytic

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [CharZero 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  {f : E → F} {s : Set E} {a : E}

/-- **The analytic constant rank theorem.** Let `f` be analytic on an open subset `s` of a Banach
space over a complete field of characteristic zero, with values in a finite-dimensional space, and
assume that the rank of `Df` on `s` never exceeds its rank at
`a ∈ s` (for instance, that it is constant on `s`). Then there are charts `φ` of `E` near `a` and
`ψ` of `F` near `f a`, analytic with analytic inverses, sending `a` and `f a` to `0` with
derivative the identity there, in which `f` is its derivative `L = Df(a)`:
`ψ (f x) = L (φ x)` for every `x` in the source of `φ`, a neighbourhood of `a` inside `s`. -/
theorem AnalyticOnNhd.exists_openPartialHomeomorph_comp_eq_fderiv_comp (hf : AnalyticOnNhd 𝕜 f s)
    (hs : IsOpen s) (ha : a ∈ s)
    (hrank : ∀ x ∈ s, finrank 𝕜 (LinearMap.range (fderiv 𝕜 f x).toLinearMap) ≤
      finrank 𝕜 (LinearMap.range (fderiv 𝕜 f a).toLinearMap)) :
    ∃ (φ : OpenPartialHomeomorph E E) (ψ : OpenPartialHomeomorph F F),
      a ∈ φ.source ∧ φ.source ⊆ s ∧ φ a = 0 ∧ HasFDerivAt φ (ContinuousLinearMap.id 𝕜 E) a ∧
      AnalyticOnNhd 𝕜 φ φ.source ∧ AnalyticOnNhd 𝕜 φ.symm φ.target ∧
      ψ (f a) = 0 ∧ HasFDerivAt ψ (ContinuousLinearMap.id 𝕜 F) (f a) ∧
      AnalyticOnNhd 𝕜 ψ ψ.source ∧ AnalyticOnNhd 𝕜 ψ.symm ψ.target ∧
      MapsTo f φ.source ψ.source ∧ ∀ x ∈ φ.source, ψ (f x) = fderiv 𝕜 f a (φ x) := by
  have : CompleteSpace F := FiniteDimensional.completeSpace 𝕜 F
  have hfd : ∀ x ∈ s, HasFDerivAt f (fderiv 𝕜 f x) x := fun x hx ↦
    (hf x hx).differentiableAt.hasFDerivAt
  set L := fderiv 𝕜 f a
  /- Linear algebra: a pseudo-inverse `T` of `L`, continuous since `F` is finite-dimensional, the
  projection `P = L ∘ T` onto the range of `L`, and the complementary projections `π = T ∘ L` and
  `Q = 1 - π` of `E`, the latter onto `ker L`. -/
  obtain ⟨T₀, hT₀⟩ := (L : E →ₗ[𝕜] F).exists_comp_comp_eq_self
  set T : F →L[𝕜] E := LinearMap.toContinuousLinearMap T₀
  have hT : L ∘L T ∘L L = L := by
    ext v
    exact LinearMap.congr_fun hT₀ v
  have hT' (v : E) : L (T (L v)) = L v := by simpa using congr($hT v)
  set π : E →L[𝕜] E := T ∘L L with hπ
  have hπidem : IsIdempotentElem π :=
    ContinuousLinearMap.isIdempotentElem_comp_of_comp_comp_eq_self hT
  set Q : E →L[𝕜] E := ContinuousLinearMap.id 𝕜 E - π
  /- The first chart `φ₀ x = T (f x - f a) + Q (x - a)`, whose derivative at `a` is the identity,
  so that the analytic inverse function theorem applies. -/
  set φ₀ : E → E := fun x ↦ T (f x - f a) + Q (x - a) with hφ₀
  have hφ₀s : AnalyticOnNhd 𝕜 φ₀ s := fun x hx ↦
    ((T.analyticAt _).comp ((hf x hx).sub analyticAt_const)).add
      ((Q.analyticAt _).comp (analyticAt_id.sub analyticAt_const))
  have hφ₀a : φ₀ a = 0 := by simp [hφ₀]
  have hφ₀d : HasFDerivAt φ₀ (ContinuousLinearMap.id 𝕜 E) a :=
    (hfd a ha).add_sub_comp_pseudoInverse
  have hLφ₀ (x : E) : L (φ₀ x) = L (T (f x - f a)) := apply_add_sub_comp_pseudoInverse hT _ _
  obtain ⟨Φ₀, hΦ₀, haΦ₀, hΦ₀s, hΦ₀A, hΦ₀symm⟩ := (hφ₀s a ha).exists_openPartialHomeomorph
    (L := ContinuousLinearEquiv.refl 𝕜 E) (by simpa using hφ₀d.fderiv) (hs.mem_nhds ha)
  clear_value φ₀
  subst hΦ₀
  have h0Φ₀ : (0 : E) ∈ Φ₀.target := hφ₀a ▸ Φ₀.map_source haΦ₀
  have hΦ₀symm0 : Φ₀.symm 0 = a := by rw [← hφ₀a, Φ₀.left_inv haΦ₀]
  /- In the chart `Φ₀`, the map `g z = f (Φ₀⁻¹ z) - f a` satisfies `P ∘ g = L`. -/
  set g : E → F := fun z ↦ f (Φ₀.symm z) - f a with hg
  have hgA : AnalyticOnNhd 𝕜 g Φ₀.target := fun z hz ↦
    ((hf _ (hΦ₀s (Φ₀.map_target hz))).comp (hΦ₀symm z hz)).sub analyticAt_const
  /- The derivative of `g` has rank at most that of `L` and becomes `L` after projecting with
  `P = L ∘ T`, so its kernel is `ker L`: `g` is stationary along `ker L`. -/
  have hker : ∀ z ∈ Φ₀.target, ∀ v : E, L v = 0 → fderiv 𝕜 g z v = 0 := fun z hz _ hv ↦
    fderiv_comp_symm_apply_eq_zero hLφ₀ hz (hf _ (hΦ₀s (Φ₀.map_target hz))).differentiableAt
      (hΦ₀symm z hz).differentiableAt (hrank _ (hΦ₀s (Φ₀.map_target hz))) hv
  /- Hence, by the power series of `g` at `0`, `g` only depends on the `range π` component on a
  ball about `0` inside the target of `Φ₀`. -/
  obtain ⟨p, r, hp⟩ := hgA 0 h0Φ₀
  obtain ⟨δ, hδ, hball⟩ := EMetric.mem_nhds_iff.1 (Φ₀.open_target.mem_nhds h0Φ₀)
  set ε := min r δ
  have hε : 0 < ε := lt_min hp.r_pos hδ
  have hgπ : ∀ z, ‖π z‖ₑ + ‖z - π z‖ₑ < ε → g (π z) = g z := fun z hz ↦
    (hp.mono hε (min_le_left _ _)).apply_proj_eq_of_fderiv_apply_eq_zero hπidem
      (fun u hu v hv ↦ hker u (hball (Metric.eball_subset_eball (min_le_right _ _) hu)) v
        (by simpa [hπ, hT'] using congrArg L hv)) hz
  /- The second chart `ψ w = (w - f a) - (1 - P) (g (c w))` with `c w = π (T (w - f a))`. -/
  set c : F → E := fun w ↦ π (T (w - f a)) with hc
  set R : F →L[𝕜] F := ContinuousLinearMap.id 𝕜 F - L ∘L T
  set ψ₀ : F → F := fun w ↦ (w - f a) - R (g (c w)) with hψ₀
  set W : Set F := c ⁻¹' Φ₀.target with hW
  have hc_cont : Continuous c :=
    π.continuous.comp (T.continuous.comp (continuous_id.sub continuous_const))
  have hWopen : IsOpen W := Φ₀.open_target.preimage hc_cont
  have hc0 : c (f a) = 0 := by simp [hc]
  have hfaW : f a ∈ W := by simp [hW, hc0, h0Φ₀]
  have hψ₀A : AnalyticOnNhd 𝕜 ψ₀ W := fun w hw ↦
    (analyticAt_id.sub analyticAt_const).sub ((R.analyticAt _).comp ((hgA _ hw).comp
      ((π.analyticAt _).comp ((T.analyticAt _).comp (analyticAt_id.sub analyticAt_const)))))
  have hψ₀a : ψ₀ (f a) = 0 := by simp [hψ₀, hc0, hg, hΦ₀symm0]
  have hψ₀d : HasFDerivAt ψ₀ (ContinuousLinearMap.id 𝕜 F) (f a) :=
    hasFDerivAt_sub_sub_comp_pseudoInverse hT
      (hasFDerivAt_comp_symm_sub h0Φ₀ hΦ₀symm0 hφ₀d (hfd a ha)) (f a)
  obtain ⟨Ψ, hΨ, hfaΨ, hΨW, hΨA, hΨsymm⟩ := (hψ₀A _ hfaW).exists_openPartialHomeomorph
    (L := ContinuousLinearEquiv.refl 𝕜 F) (by simpa using hψ₀d.fderiv) (hWopen.mem_nhds hfaW)
  clear_value ψ₀
  subst hΨ
  /- Shrink the first chart so that `hgπ` applies on its image and `f` lands in the source of
  the second chart, where `ψ₀ (f x) = P (f x - f a) = L (φ₀ x)`. -/
  obtain ⟨V, hVopen, haV, hVΨ, hVf⟩ := exists_isOpen_apply_eq_apply hT hf.continuousOn hΦ₀s haΦ₀
    hfaΨ {z | ‖π z‖ₑ + ‖z - π z‖ₑ < ε} (isOpen_lt (by fun_prop) continuous_const)
    (by simp [hφ₀a, hε]) (congrFun hφ₀) (congrFun hψ₀) hgπ
  exact ⟨Φ₀.restrOpen V hVopen, Ψ, ⟨haΦ₀, haV⟩, fun x hx ↦ hΦ₀s hx.1, hφ₀a, hφ₀d,
    hΦ₀A.mono fun x hx ↦ hx.1, hΦ₀symm.mono fun z hz ↦ hz.1, hψ₀a, hψ₀d,
    hΨA, hΨsymm, fun x hx ↦ hVΨ hx.2, fun x hx ↦ hVf x hx.2⟩

/-- **Level sets of an analytic map of constant rank.** Under the hypotheses of the analytic
constant rank theorem, there is a chart `φ` of `E` near `a`, inside `s`, analytic with analytic
inverse, sending `a` to `0` with derivative the identity there, in which the level set of `f`
through `a` is the kernel of `Df(a)`: for `x` in the source of `φ`, `f x = f a` exactly when
`φ x ∈ ker Df(a)`. -/
theorem AnalyticOnNhd.exists_openPartialHomeomorph_apply_eq_iff_mem_ker
    (hf : AnalyticOnNhd 𝕜 f s) (hs : IsOpen s) (ha : a ∈ s)
    (hrank : ∀ x ∈ s, finrank 𝕜 (LinearMap.range (fderiv 𝕜 f x).toLinearMap) ≤
      finrank 𝕜 (LinearMap.range (fderiv 𝕜 f a).toLinearMap)) :
    ∃ φ : OpenPartialHomeomorph E E,
      a ∈ φ.source ∧ φ.source ⊆ s ∧ φ a = 0 ∧ HasFDerivAt φ (ContinuousLinearMap.id 𝕜 E) a ∧
      AnalyticOnNhd 𝕜 φ φ.source ∧ AnalyticOnNhd 𝕜 φ.symm φ.target ∧
      ∀ x ∈ φ.source, f x = f a ↔ φ x ∈ LinearMap.ker (fderiv 𝕜 f a).toLinearMap := by
  obtain ⟨φ, ψ, haφ, hφs, hφa, hφd, hφA, hφsymm, hψa, -, -, -, hmaps, hψf⟩ :=
    hf.exists_openPartialHomeomorph_comp_eq_fderiv_comp hs ha hrank
  exact ⟨φ, haφ, hφs, hφa, hφd, hφA, hφsymm,
    fun _ ↦ apply_eq_iff_mem_ker_of_apply_eq_apply haφ hψa hmaps hψf⟩

end Analytic

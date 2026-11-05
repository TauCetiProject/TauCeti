/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import TauCeti.Analysis.Calculus.InverseFunctionTheorem
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
import Mathlib.Analysis.Calculus.MeanValue
import TauCeti.Analysis.Normed.Module.ContinuousInverse
import TauCeti.LinearAlgebra.Dimension.Submodule

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
small enough neighbourhood the hypothesis is equivalent to the rank being constant. Read in charts,
this local statement is the rank theorem for maps between manifolds; being local, it needs no
separation or countability assumption on them.

Since `ψ` is injective near `f a`, the level set of `f` through `a` is, near `a`, the preimage
under the chart `φ` of the linear subspace `ker L`; this gives the level sets of a constant rank map
their local structure of submanifolds of dimension `dim E - rank L`.

## Main results

* `ContDiffOn.exists_openPartialHomeomorph_comp_eq_fderiv_comp`: the constant rank theorem. Near
  `a` and `f a` there are charts `φ` and `ψ`, `C^n` with `C^n` inverses, sending `a` and `f a` to
  `0` with derivative the identity there, such that `ψ ∘ f = Df(a) ∘ φ` near `a`.
* `ContDiffOn.exists_openPartialHomeomorph_apply_eq_iff_mem_ker`: near `a`, the level set of `f`
  through `a` is the preimage under a chart `φ` of the kernel of `Df(a)`.

## Implementation notes

Let `T` be a continuous pseudo-inverse of `L = Df(a)` (`L ∘ T ∘ L = L`). Then `P = L ∘ T` is a
projection onto the range of `L` and `Q = 1 - T ∘ L` is a projection onto `ker L`. The first chart
is `φ x = T (f x - f a) + Q (x - a)`, whose derivative at `a` is the identity; it satisfies
`L (φ x) = P (f x - f a)`. In this chart `g z = f (φ⁻¹ z) - f a` satisfies `P ∘ g = L`, so the
derivative of `g` maps `E` onto the range of `L` after projecting with `P`; as it has rank at most
`rank L`, its kernel is that of `L` (`LinearMap.ker_comp_eq_of_finrank_range_le`). Hence `g` is
constant along `ker L` on a neighbourhood of `0` which is a product in the decomposition
`E = range (T ∘ L) ⊕ ker L`, and the second chart `ψ w = (w - f a) - (1 - P) (g (c w))`, where
`c = T ∘ L ∘ T (· - f a)`, removes the component of `f` transverse to the range of `L`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Theorem 4.12 (the rank theorem).
* S. Lang, *Fundamentals of Differential Geometry*, Graduate Texts in Mathematics 191, Springer,
  1999, Chapter I, §5 (the constant rank theorem in Banach spaces).
-/

public section

open Filter Set Module
open scoped Topology

variable {𝕂 : Type*} [RCLike 𝕂]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕂 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕂 F]

/-- A differentiable map whose derivative kills `v` on an open set containing every point
`z + t • v` with `‖t‖ < ρ`, for some `ρ > 1`, takes the same value at `z` and at `z + v`. -/
private theorem apply_add_eq_of_fderiv_apply_eq_zero {g : E → F} {O : Set E} (hO : IsOpen O)
    (hg : DifferentiableOn 𝕂 g O) {z v : E} (hv : ∀ u ∈ O, fderiv 𝕂 g u v = 0) {ρ : ℝ}
    (hρ : 1 < ρ) (hline : ∀ t : 𝕂, ‖t‖ < ρ → z + t • v ∈ O) : g (z + v) = g z := by
  -- The restriction of `g` to the line through `z` in direction `v` has zero derivative on the
  -- disc of radius `ρ`, which is connected and contains `0` and `1`.
  let q : 𝕂 → F := fun t ↦ g (z + t • v)
  have hline' : ∀ t ∈ Metric.ball (0 : 𝕂) ρ, z + t • v ∈ O := fun t ht ↦
    hline t (by simpa using ht)
  have hq : ∀ t ∈ Metric.ball (0 : 𝕂) ρ, HasFDerivAt q ((fderiv 𝕂 g (z + t • v)).comp
      ((ContinuousLinearMap.id 𝕂 𝕂).smulRight v)) t := fun t ht ↦ by
    have hgt := (hg.differentiableAt (hO.mem_nhds (hline' t ht))).hasFDerivAt
    exact hgt.comp t ((hasFDerivAt_id t).smul_const v |>.const_add z)
  have h := Metric.isOpen_ball.is_const_of_fderiv_eq_zero (convex_ball (0 : 𝕂) ρ).isPreconnected
    (fun t ht ↦ (hq t ht).differentiableAt.differentiableWithinAt)
    (fun t ht ↦ by
      rw [(hq t ht).fderiv]
      ext
      simp [hv _ (hline' t ht)])
    (show (1 : 𝕂) ∈ Metric.ball 0 ρ by simpa using hρ) (Metric.mem_ball_self (by linarith))
  simpa [q] using h

/-- If `P ∘ g` agrees near `z` with a continuous linear map `L`, and the derivative `D` of `g` at
`z` has rank at most that of `L`, then `D` vanishes on the kernel of `L`: projecting the range of
`D` with `P` does not lower its dimension, so it does not enlarge its kernel. -/
private theorem HasFDerivAt.apply_eq_zero_of_comp_eventuallyEq [FiniteDimensional 𝕂 E]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕂 G] {g : E → F} {D : E →L[𝕂] F}
    {P : F →L[𝕂] G} {L : E →L[𝕂] G} {z : E} (hg : HasFDerivAt g D z)
    (hPg : (fun w ↦ P (g w)) =ᶠ[𝓝 z] L)
    (hrank : finrank 𝕂 (LinearMap.range D.toLinearMap) ≤
      finrank 𝕂 (LinearMap.range L.toLinearMap))
    {v : E} (hv : L v = 0) : D v = 0 := by
  have hcomp : (P : F →ₗ[𝕂] G) ∘ₗ (D : E →ₗ[𝕂] F) = L := congrArg ContinuousLinearMap.toLinearMap
    ((P.hasFDerivAt.comp z hg).unique (L.hasFDerivAt.congr_of_eventuallyEq hPg))
  have hker := LinearMap.ker_comp_eq_of_finrank_range_le (D : E →ₗ[𝕂] F) (P : F →ₗ[𝕂] G)
    (by rwa [hcomp])
  rw [hcomp] at hker
  exact (hker ▸ hv : v ∈ LinearMap.ker (D : E →ₗ[𝕂] F))

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
  have : CompleteSpace E := FiniteDimensional.complete 𝕂 E
  have hfd : ∀ x ∈ s, HasFDerivAt f (fderiv 𝕂 f x) x := fun x hx ↦
    ((hf.differentiableOn hn0).differentiableAt (hs.mem_nhds hx)).hasFDerivAt
  set L := fderiv 𝕂 f a
  /- Linear algebra: a pseudo-inverse `T` of `L`, the projection `P = L ∘ T` onto the range of `L`,
  and the complementary projections `π = T ∘ L` and `Q = 1 - π` of `E`, the latter onto `ker L`. -/
  obtain ⟨T, hT⟩ := L.exists_comp_comp_eq_self
  have hT' (v : E) : L (T (L v)) = L v := by simpa using congr($hT v)
  set π : E →L[𝕂] E := T ∘L L with hπ
  set Q : E →L[𝕂] E := ContinuousLinearMap.id 𝕂 E - π with hQ
  have hππ (z : E) : π (π z) = π z := by simp [hπ, hT']
  have hπQ (z : E) : π (Q z) = 0 := by simp [hQ, hππ]
  have hQπ (z : E) : Q (π z) = 0 := by simp [hQ, hππ]
  have hLQ (z : E) : L (Q z) = 0 := by simp [hQ, hπ, hT']
  have hπQ_add (z : E) : π z + Q z = z := by simp [hQ]
  /- The first chart `φ₀ x = T (f x - f a) + Q (x - a)`, whose derivative at `a` is the identity,
  so that the inverse function theorem applies. -/
  set φ₀ : E → E := fun x ↦ T (f x - f a) + Q (x - a) with hφ₀
  have hφ₀s : ContDiffOn 𝕂 n φ₀ s :=
    (T.contDiff.comp_contDiffOn (hf.sub contDiffOn_const)).add
      (Q.contDiff.comp_contDiffOn (contDiffOn_id.sub contDiffOn_const))
  have hφ₀a : φ₀ a = 0 := by simp [hφ₀]
  have hφ₀d : HasFDerivAt φ₀ (ContinuousLinearMap.id 𝕂 E) a := by
    have h : HasFDerivAt φ₀ (T ∘L L + Q ∘L ContinuousLinearMap.id 𝕂 E) a :=
      (T.hasFDerivAt.comp a ((hfd a ha).sub_const (f a))).add
        (Q.hasFDerivAt.comp a ((hasFDerivAt_id a).sub_const a))
    refine h.congr_fderiv ?_
    ext v
    simp [hQ, hπ]
  have hLφ₀ (x : E) : L (φ₀ x) = L (T (f x - f a)) := by simp [hφ₀, hLQ]
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
  have hPg : ∀ z ∈ Φ₀.target, L (T (g z)) = L z := fun z hz ↦ by
    rw [← hLφ₀, ← Φ₀.right_inv hz]
    simp only [Φ₀.left_inv (Φ₀.map_target hz)]
  have hgd : ∀ z ∈ Φ₀.target, HasFDerivAt g (fderiv 𝕂 f (Φ₀.symm z) ∘L fderiv 𝕂 Φ₀.symm z) z :=
    fun z hz ↦ by
      have hsymm := ((hΦ₀symm.differentiableOn hn0).differentiableAt
        (Φ₀.open_target.mem_nhds hz)).hasFDerivAt
      exact ((hfd _ (hΦ₀s (Φ₀.map_target hz))).comp z hsymm).sub_const (f a)
  /- The derivative of `g` has rank at most that of `L` and becomes `L` after projecting with
  `P = L ∘ T`, so its kernel is `ker L`: `g` is stationary along `ker L`. -/
  have hker : ∀ z ∈ Φ₀.target, ∀ v : E, L v = 0 → fderiv 𝕂 g z v = 0 := by
    intro z hz v hv
    rw [(hgd z hz).fderiv]
    refine (hgd z hz).apply_eq_zero_of_comp_eventuallyEq (P := L ∘L T)
      (eventually_of_mem (Φ₀.open_target.mem_nhds hz) fun w hw ↦ hPg w hw) ?_ hv
    refine (Submodule.finrank_mono ?_).trans (hrank _ (hΦ₀s (Φ₀.map_target hz)))
    exact LinearMap.range_comp_le_range (fderiv 𝕂 Φ₀.symm z : E →ₗ[𝕂] E)
      (fderiv 𝕂 f (Φ₀.symm z) : E →ₗ[𝕂] F)
  /- A neighbourhood `U` of `0`, a product in `E = range π ⊕ ker L`, on which `g` only depends on
  the `range π` component. The slightly larger product `O` contains the segments used. -/
  obtain ⟨ε', hε', hball⟩ := Metric.mem_nhds_iff.1 (Φ₀.open_target.mem_nhds h0Φ₀)
  set ε := ε' / 3 with hε
  have hε0 : 0 < ε := by positivity
  set O : Set E := {z | ‖π z‖ < ε ∧ ‖Q z‖ < 2 * ε}
  have hOopen : IsOpen O :=
    (isOpen_lt (continuous_norm.comp π.continuous) continuous_const).inter
      (isOpen_lt (continuous_norm.comp Q.continuous) continuous_const)
  have hOt : O ⊆ Φ₀.target := fun z hz ↦ hball <| by
    rw [Metric.mem_ball, dist_zero_right, ← hπQ_add z]
    exact (norm_add_le _ _).trans_lt (by linarith [hz.1, hz.2])
  have hgπ : ∀ z, ‖π z‖ < ε → ‖Q z‖ < ε → g (π z) = g z := by
    intro z hz₁ hz₂
    conv_rhs => rw [← hπQ_add z]
    refine (apply_add_eq_of_fderiv_apply_eq_zero hOopen
      ((hgC.differentiableOn hn0).mono hOt) (fun u hu ↦ hker u (hOt hu) _ (hLQ z))
      one_lt_two fun t ht ↦ ?_).symm
    refine ⟨by simpa [hππ, hπQ] using hz₁, ?_⟩
    rw [map_add, map_smul, hQπ, zero_add, norm_smul]
    have : ‖Q (Q z)‖ = ‖Q z‖ := by simp [hQ, hππ]
    rw [this]
    nlinarith [norm_nonneg (Q z), norm_nonneg t]
  /- The second chart `ψ w = (w - f a) - (1 - P) (g (c w))` with `c w = π (T (w - f a))`. -/
  set c : F → E := fun w ↦ π (T (w - f a)) with hc
  set R : F →L[𝕂] F := ContinuousLinearMap.id 𝕂 F - L ∘L T with hR
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
  have hψ₀d : HasFDerivAt ψ₀ (ContinuousLinearMap.id 𝕂 F) (f a) := by
    have hsymm : HasFDerivAt Φ₀.symm (ContinuousLinearMap.id 𝕂 E) 0 := by
      have h := Φ₀.hasFDerivAt_symm h0Φ₀ (f' := ContinuousLinearEquiv.refl 𝕂 E)
        (by rw [hΦ₀symm0]; exact hφ₀d)
      simpa using h
    have hg0 : HasFDerivAt g (L ∘L ContinuousLinearMap.id 𝕂 E) (c (f a)) := by
      have hf0 : HasFDerivAt f L (Φ₀.symm 0) := by rw [hΦ₀symm0]; exact hfd a ha
      rw [hc0]
      exact (hf0.comp 0 hsymm).sub_const (f a)
    have hcd : HasFDerivAt c (π ∘L T) (f a) :=
      π.hasFDerivAt.comp (f a) (T.hasFDerivAt.comp (f a) ((hasFDerivAt_id _).sub_const (f a)))
    have h : HasFDerivAt ψ₀ (ContinuousLinearMap.id 𝕂 F - R ∘L ((L ∘L ContinuousLinearMap.id 𝕂 E)
        ∘L (π ∘L T))) (f a) :=
      ((hasFDerivAt_id (f a)).sub_const (f a)).sub (R.hasFDerivAt.comp (f a) (hg0.comp (f a) hcd))
    refine h.congr_fderiv ?_
    ext w
    simp [hR, hT']
  obtain ⟨Ψ, hΨ, hfaΨ, hΨW, hΨsymm⟩ := TauCeti.ContDiffOn.exists_openPartialHomeomorph hψ₀C hWopen
    hfaW hn (e := ContinuousLinearEquiv.refl 𝕂 F) (by simpa using hψ₀d.fderiv.symm)
  clear_value ψ₀
  subst hΨ
  /- Shrink the first chart so that it lands in the product `U` and `f` lands in the source of
  the second chart. -/
  set V : Set E := (Φ₀.source ∩ Φ₀ ⁻¹' {z | ‖π z‖ < ε ∧ ‖Q z‖ < ε}) ∩ f ⁻¹' Ψ.source
  have hVopen : IsOpen V :=
    ((hf.continuousOn.mono hΦ₀s).mono inter_subset_left).isOpen_inter_preimage
      (Φ₀.isOpen_inter_preimage <|
        (isOpen_lt (continuous_norm.comp π.continuous) continuous_const).inter
          (isOpen_lt (continuous_norm.comp Q.continuous) continuous_const)) Ψ.open_source
  have haV : a ∈ V := ⟨⟨haΦ₀, by simp [hφ₀a, hε0]⟩, hfaΨ⟩
  refine ⟨Φ₀.restrOpen V hVopen, Ψ, ⟨haΦ₀, haV⟩, fun x hx ↦ hΦ₀s hx.1, hφ₀a, hφ₀d,
    hφ₀s.mono fun x hx ↦ hΦ₀s hx.1, hΦ₀symm.mono fun z hz ↦ hz.1, hψ₀a, hψ₀d,
    hψ₀C.mono hΨW, hΨsymm, fun x hx ↦ hx.2.2, fun x hx ↦ ?_⟩
  /- On the shrunken chart, `c (f x) = π (φ₀ x)` and `g` does not see the `ker L` component of
  `φ₀ x`, so `ψ₀ (f x) = P (f x - f a) = L (φ₀ x)`. -/
  rw [OpenPartialHomeomorph.restrOpen_source] at hx
  obtain ⟨hxΦ₀, ⟨-, hxU₁, hxU₂⟩, -⟩ := hx
  have hcx : c (f x) = π (Φ₀ x) := by
    simp only [hc, hφ₀, map_add, hπQ, add_zero]
  have hgx : g (Φ₀ x) = f x - f a := by simp [hg, Φ₀.left_inv hxΦ₀]
  simpa [hψ₀, hcx, hgπ _ hxU₁ hxU₂, hgx, hR] using (hLφ₀ x).symm

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
  refine ⟨φ, haφ, hφs, hφa, hφd, hφC, hφsymm, fun x hx ↦ ?_⟩
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, ← hψf x hx, ← hψa]
  exact (ψ.injOn.eq_iff (hmaps hx) (hmaps haφ)).symm

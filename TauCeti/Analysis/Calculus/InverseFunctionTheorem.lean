/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
public import TauCeti.Analysis.Calculus.ContinuousLinearMapInverse
import TauCeti.Order.Monotone.InvFunOn

/-!
# The inverse function theorem with a `C^n` inverse on a whole open set

Mathlib's `ContDiffAt.toOpenPartialHomeomorph` turns a `C^n` map with invertible derivative at a
point into an `OpenPartialHomeomorph`, but `ContDiffAt.to_localInverse` only produces a `C^n`
inverse *at the image point*: `OpenPartialHomeomorph.contDiffAt_symm` needs an invertible
derivative at the point one inverts around, and invertibility is assumed at the base point alone.
Building a partial diffeomorphism of manifolds, or comparing two implicit-function charts of a
level set, needs more: the inverse has to be `C^n` on the whole target.

The invertibility does in fact persist. Mathlib's construction goes through
`ApproximatesLinearOn`: the source of the homeomorphism is an open set on which the map
approximates its derivative `L` at the base point with a constant `c` strictly below `‖L⁻¹‖⁻¹`.
On such a set every Fréchet derivative of the map is within `c` of `L` in norm, hence is still
invertible by `ContinuousLinearMap.isInvertible_of_norm_sub_le_half`. This file extracts that
estimate and runs Mathlib's smooth inverse function theorem at every point of the target.

Three forms are given. The first is about Mathlib's own homeomorphism, over an arbitrary
nontrivially normed field: strict differentiability alone makes derivative invertibility persist,
while inverse `C^n` regularity also assumes the corresponding `C^n` regularity of the map. It is
the form a consumer that cannot choose its homeomorphism — such as the implicit-function chart of
a level set — needs. The second packages the classical statement over `ℝ` or `ℂ`: a `C^n` map with
invertible derivative at a point of an open set `s` restricts to an `OpenPartialHomeomorph` inside
`s` whose inverse is `C^n` on its target. The third is the global one-dimensional form for the
scalar inverse `Function.invFunOn f s` of an injective change of variables `f` with nonvanishing
derivative on `s`, giving its strict derivative, `C^n` regularity and continuity on `f '' s`,
together with evaluation, continuity and real positivity of its divided difference
`dslope (Function.invFunOn f s) (f a)` across `f a`.

## Main results

* `ApproximatesLinearOn.norm_sub_le_of_hasFDerivAt`: on a set where `f` approximates `L` with
  constant `c`, every derivative of `f` at an interior point is within `c` of `L`.
* `HasStrictFDerivAt.exists_mem_nhds_injOn`: a map with an invertible strict derivative at a point
  is injective near it, without completeness.
* `HasStrictFDerivAt.approximatesLinearOn_toOpenPartialHomeomorph_source`: the source of the
  inverse function theorem's homeomorphism carries the approximation estimate its construction
  chose.
* `HasStrictFDerivAt.isInvertible_of_mem_toOpenPartialHomeomorph_source`: hence the derivative of
  `f` is invertible at every point of that source, not only at the base point.
* `HasStrictFDerivAt.contDiffAt_toOpenPartialHomeomorph_symm` and
  `HasStrictFDerivAt.contDiffOn_toOpenPartialHomeomorph_symm`: the local inverse is `C^n` at every
  point of the target, and hence on the target.
* `OpenPartialHomeomorph.contDiffOn_symm_inter_preimage`: inverse regularity on the part of the
  target corresponding to an open portion of the source.
* `OpenPartialHomeomorph.contDiffOn_symm_of_isInvertible_fderiv`: a `C^n` open partial
  homeomorphism from a complete normed space whose derivative is invertible on its source has a
  `C^n` inverse on its target.
* `ApproximatesLinearOn.contDiffOn_toOpenPartialHomeomorph_symm`: the same for the homeomorphism
  of a `C^n` map approximating `L` on an open set with a constant less than `‖L⁻¹‖⁻¹`.
* `TauCeti.ContDiffOn.exists_openPartialHomeomorph`: a `C^n` map (`1 ≤ n`) on an open set with
  invertible derivative at a point restricts to an `OpenPartialHomeomorph` around that point whose
  inverse is `C^n` on the whole target.
* `ContDiffOn.exists_openPartialHomeomorph_fderiv_symm_apply_eq`: the same local inverse
  carries differential identities `dg_z (u i) = v i (g z)` over to `d(g⁻¹)_y (v i y) = u i`.
* `Set.MapsTo.interior_of_contDiffOn`: a `C¹` map with invertible derivative on the interior of
  `s` and mapping `s` into `t` maps `interior s` into `interior t`.
* `TauCeti.exists_contDiffAt_graph_of_isInvertible`: a disc `z ↦ (a z, b z)` whose second
  component has invertible derivative at `z₀` is, near `z₀`, the graph of a map `C^n` at `b z₀`.
* `HasStrictDerivAt.invFunOn`, `HasStrictDerivAt.deriv_invFunOn`,
  `HasStrictDerivAt.dslope_invFunOn_eq`, `ContDiffOn.invFunOn`,
  `ContDiffOn.continuousOn_dslope_invFunOn`, `StrictMonoOn.dslope_invFunOn_pos`,
  `TauCeti.isOpen_image_of_hasStrictDerivAt`,
  `TauCeti.continuousOn_invFunOn_of_hasStrictDerivAt`,
  `TauCeti.continuousOn_dslope_invFunOn_of_hasStrictDerivAt`: one-dimensional `Function.invFunOn`
  strict differentiability, derivative formula, `C^n` regularity, open image, continuity on
  `f '' s`, and evaluation, continuity and real positivity of
  `dslope (Function.invFunOn f s) (f a)`.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS Colloquium
  Publications 52, 2012, Appendix A.3.
-/

public section

noncomputable section

open Filter Set
open scoped ContDiff NNReal Topology

section Approximation

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- On a set on which `f` approximates the continuous linear map `L` with constant `c`, every
Fréchet derivative of `f` at an interior point is within `c` of `L` in operator norm. -/
theorem ApproximatesLinearOn.norm_sub_le_of_hasFDerivAt {f : E → F} {L A : E →L[𝕜] F} {s : Set E}
    {c : ℝ≥0} (hf : ApproximatesLinearOn f L s c) {x : E} (hs : s ∈ 𝓝 x)
    (hA : HasFDerivAt f A x) : ‖A - L‖ ≤ c := by
  exact (hA.sub L.hasFDerivAt).le_of_lipschitzOn hs hf.lipschitzOnWith

namespace HasStrictFDerivAt

/-- **Local injectivity from a strict derivative.** A map whose strict derivative at `a` is a
continuous linear equivalence is injective on a neighbourhood of `a`; no completeness is needed,
since `ApproximatesLinearOn.injOn` only uses the approximation estimate. -/
theorem exists_mem_nhds_injOn {f : E → F} {L : E ≃L[𝕜] F} {a : E}
    (hf : HasStrictFDerivAt f (L : E →L[𝕜] F) a) : ∃ s ∈ 𝓝 a, InjOn f s := by
  obtain ⟨s, has, hso, happ⟩ := hf.approximates_deriv_on_open_nhds
  exact ⟨s, hso.mem_nhds has, happ.injOn (L.subsingleton_or_nnNorm_symm_pos.imp id
    fun h => NNReal.half_lt_self (inv_pos.2 h).ne')⟩

variable [CompleteSpace E] {f : E → F} {L : E ≃L[𝕜] F} {a : E}

/-- On the source of the homeomorphism built by the inverse function theorem, `f` approximates its
derivative at the base point with the constant `‖L⁻¹‖⁻¹ / 2` that the construction chose. -/
theorem approximatesLinearOn_toOpenPartialHomeomorph_source
    (hf : HasStrictFDerivAt f (L : E →L[𝕜] F) a) :
    ApproximatesLinearOn f (L : E →L[𝕜] F) (hf.toOpenPartialHomeomorph f).source
      (‖(L.symm : F →L[𝕜] E)‖₊⁻¹ / 2) := by
  have h := (Classical.choose_spec hf.approximates_deriv_on_open_nhds).2.2
  convert h using 1
  exact ApproximatesLinearOn.toOpenPartialHomeomorph_source ..

/-- **The derivative of `f` is invertible throughout the inverse-function neighbourhood.**
Invertibility of the derivative is assumed at the base point only, but it propagates to every
point of the source of `HasStrictFDerivAt.toOpenPartialHomeomorph`. -/
theorem isInvertible_of_mem_toOpenPartialHomeomorph_source
    (hf : HasStrictFDerivAt f (L : E →L[𝕜] F) a) {x : E}
    (hx : x ∈ (hf.toOpenPartialHomeomorph f).source) {A : E →L[𝕜] F} (hA : HasFDerivAt f A x) :
    A.IsInvertible := by
  refine ContinuousLinearMap.isInvertible_of_norm_sub_le_half L ?_
  have hbound := hf.approximatesLinearOn_toOpenPartialHomeomorph_source.norm_sub_le_of_hasFDerivAt
    ((hf.toOpenPartialHomeomorph f).open_source.mem_nhds hx) hA
  rwa [← NNReal.coe_le_coe, coe_nnNorm]

/-- **The local inverse of the inverse function theorem is `C^n` at every point of its target.**
The original inverse-function hypotheses provide an invertible derivative only at the base point.
Here we prove the missing invertibility throughout the constructed source, then apply Mathlib's
`OpenPartialHomeomorph.contDiffAt_symm` pointwise on the target. -/
theorem contDiffAt_toOpenPartialHomeomorph_symm {n : ℕ∞ω}
    (hf : HasStrictFDerivAt f (L : E →L[𝕜] F) a) {y : F}
    (hy : y ∈ (hf.toOpenPartialHomeomorph f).target)
    (hcont : ContDiffAt 𝕜 n f ((hf.toOpenPartialHomeomorph f).symm y)) :
    ContDiffAt 𝕜 n (hf.toOpenPartialHomeomorph f).symm y := by
  rcases eq_or_ne n 0 with rfl | hn
  · exact contDiffAt_zero.2 ⟨_, (hf.toOpenPartialHomeomorph f).open_target.mem_nhds hy,
      (hf.toOpenPartialHomeomorph f).continuousOn_symm⟩
  set x := (hf.toOpenPartialHomeomorph f).symm y with _
  have hxs : x ∈ (hf.toOpenPartialHomeomorph f).source :=
    (hf.toOpenPartialHomeomorph f).map_target hy
  have hA : HasFDerivAt f (fderiv 𝕜 f x) x := (hcont.differentiableAt hn).hasFDerivAt
  obtain ⟨A, hA'⟩ := hf.isInvertible_of_mem_toOpenPartialHomeomorph_source hxs hA
  refine (hf.toOpenPartialHomeomorph f).contDiffAt_symm (f₀' := A) hy ?_ ?_
  · simpa [hA'] using hA
  · simpa using hcont

/-- **The inverse function theorem produces a `C^n` inverse.** If `f` is `C^n` on the source of the
homeomorphism built by the inverse function theorem, then the inverse is `C^n` on the target. -/
theorem contDiffOn_toOpenPartialHomeomorph_symm {n : ℕ∞ω}
    (hf : HasStrictFDerivAt f (L : E →L[𝕜] F) a)
    (hcont : ContDiffOn 𝕜 n f (hf.toOpenPartialHomeomorph f).source) :
    ContDiffOn 𝕜 n (hf.toOpenPartialHomeomorph f).symm (hf.toOpenPartialHomeomorph f).target := by
  intro y hy
  refine (hf.contDiffAt_toOpenPartialHomeomorph_symm hy ?_).contDiffWithinAt
  exact hcont.contDiffAt ((hf.toOpenPartialHomeomorph f).open_source.mem_nhds
    ((hf.toOpenPartialHomeomorph f).map_target hy))

end HasStrictFDerivAt

end Approximation

section ContDiffInverse

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- A `C^n` open partial homeomorphism of a complete normed space whose derivative is invertible at
every point of its source has a `C^n` inverse on its target. -/
theorem OpenPartialHomeomorph.contDiffOn_symm_of_isInvertible_fderiv [CompleteSpace E] {n : ℕ∞ω}
    (ψ : OpenPartialHomeomorph E F) (hψ : ContDiffOn 𝕜 n ψ ψ.source)
    (hinv : ∀ x ∈ ψ.source, (fderiv 𝕜 ψ x).IsInvertible) :
    ContDiffOn 𝕜 n ψ.symm ψ.target := by
  rcases eq_or_ne n 0 with rfl | hn
  · exact contDiffOn_zero.2 ψ.continuousOn_symm
  intro y hy
  have hx := ψ.map_target hy
  have hat : ContDiffAt 𝕜 n ψ (ψ.symm y) :=
    (hψ _ hx).contDiffAt (ψ.open_source.mem_nhds hx)
  obtain ⟨e, he⟩ := hinv _ hx
  refine (ψ.contDiffAt_symm hy (f₀' := e) ?_ hat).contDiffWithinAt
  rw [he]
  exact (hat.differentiableAt hn).hasFDerivAt

/-- Regularity and invertibility on a local part of the source give inverse regularity on
the corresponding part of the target. -/
theorem OpenPartialHomeomorph.contDiffOn_symm_inter_preimage [CompleteSpace E] {n : ℕ∞ω}
    (ψ : OpenPartialHomeomorph E F) {s : Set E} (hs : IsOpen s)
    (hψ : ContDiffOn 𝕜 n ψ (ψ.source ∩ s))
    (hinv : ∀ x ∈ ψ.source ∩ s, (fderiv 𝕜 ψ x).IsInvertible) :
    ContDiffOn 𝕜 n ψ.symm (ψ.target ∩ ψ.symm ⁻¹' s) := by
  have hcoe : ⇑(ψ.restr s) = ψ := ψ.restr_apply s
  have hsource : (ψ.restr s).source = ψ.source ∩ s := ψ.restr_source' s hs
  have hC : ContDiffOn 𝕜 n (ψ.restr s) (ψ.restr s).source := by
    simpa only [hcoe, hsource] using hψ
  have hInv : ∀ x ∈ (ψ.restr s).source, (fderiv 𝕜 (ψ.restr s) x).IsInvertible := by
    simpa only [hcoe, hsource] using hinv
  simpa only [ψ.restr_symm_apply, ψ.restr_target, hs.interior_eq] using
    (ψ.restr s).contDiffOn_symm_of_isInvertible_fderiv hC hInv

/-- A map that is `C^n` on an open set `s` and approximates a continuous linear equivalence `L`
there with a constant less than `‖L⁻¹‖⁻¹` restricts to an open partial homeomorphism with source
`s` whose inverse is `C^n` on its target. -/
theorem ApproximatesLinearOn.contDiffOn_toOpenPartialHomeomorph_symm [CompleteSpace E]
    {n : ℕ∞ω} {f : E → F} {L : E ≃L[𝕜] F} {s : Set E} {c : ℝ≥0}
    (hf : ApproximatesLinearOn f (L : E →L[𝕜] F) s c)
    (hc : Subsingleton E ∨ c < ‖(L.symm : F →L[𝕜] E)‖₊⁻¹) (hs : IsOpen s)
    (hcont : ContDiffOn 𝕜 n f s) :
    ContDiffOn 𝕜 n (hf.toOpenPartialHomeomorph f s hc hs).symm
      (hf.toOpenPartialHomeomorph f s hc hs).target := by
  rcases eq_or_ne n 0 with rfl | hn
  · exact contDiffOn_zero.2 (hf.toOpenPartialHomeomorph f s hc hs).continuousOn_symm
  refine (hf.toOpenPartialHomeomorph f s hc hs).contDiffOn_symm_of_isInvertible_fderiv
    (by simpa using hcont) fun x hx ↦ ?_
  simp only [toOpenPartialHomeomorph_source, toOpenPartialHomeomorph_coe] at hx ⊢
  rcases hc with hE | hc
  · exact ⟨L, by ext x; simp [Subsingleton.elim x 0]⟩
  refine ContinuousLinearMap.isInvertible_of_norm_sub_lt L (lt_of_le_of_lt ?_ hc)
  have h := hf.norm_sub_le_of_hasFDerivAt (hs.mem_nhds hx)
    ((hcont.contDiffAt (hs.mem_nhds hx)).differentiableAt hn).hasFDerivAt
  rwa [← NNReal.coe_le_coe, coe_nnNorm]

end ContDiffInverse

namespace TauCeti

variable {𝕂 : Type*} [RCLike 𝕂]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕂 E] [CompleteSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕂 F]
  {n : WithTop ℕ∞} {g : E → F} {s : Set E} {a : E}

/-- **The inverse function theorem, with a `C^n` inverse on the whole target.** A map which is
`C^n` on an open set `s`, with `1 ≤ n`, and whose derivative at `a ∈ s` is a continuous linear
equivalence, coincides on a neighbourhood of `a` with an `OpenPartialHomeomorph` whose source is
contained in `s` and whose inverse is `C^n` on its target. -/
theorem ContDiffOn.exists_openPartialHomeomorph
    (hg : ContDiffOn 𝕂 n g s) (hs : IsOpen s) (ha : a ∈ s) (hn : 1 ≤ n)
    {e : E ≃L[𝕂] F} (he : (e : E →L[𝕂] F) = fderiv 𝕂 g a) :
    ∃ Θ : OpenPartialHomeomorph E F, (Θ : E → F) = g ∧ a ∈ Θ.source ∧ Θ.source ⊆ s ∧
      ContDiffOn 𝕂 n Θ.symm Θ.target := by
  have hn0 : n ≠ 0 := by rintro rfl; exact absurd hn (by simp)
  have hgAt : ∀ y ∈ s, ContDiffAt 𝕂 n g y := fun y hy => hg.contDiffAt (hs.mem_nhds hy)
  have he₀ : HasFDerivAt g (e : E →L[𝕂] F) a :=
    he ▸ ((hg.differentiableOn hn0).differentiableAt (hs.mem_nhds ha)).hasFDerivAt
  have hstrict := (hgAt a ha).hasStrictFDerivAt he₀ hn0
  refine ⟨((hgAt a ha).toOpenPartialHomeomorph g he₀ hn0).restrOpen s hs, rfl,
    ⟨(hgAt a ha).mem_toOpenPartialHomeomorph_source he₀ hn0, ha⟩, fun y hy => hy.2, ?_⟩
  intro w hw
  exact (hstrict.contDiffAt_toOpenPartialHomeomorph_symm hw.1 (hgAt _ hw.2)).contDiffWithinAt

/-- **Local inversion transports differential identities.** In the setting of
`TauCeti.ContDiffOn.exists_openPartialHomeomorph`, if for each index `i` the derivative of `g` at
every point `z ∈ s` sends a fixed vector `u i` to `v i (g z)`, then the `C^n` local inverse can be
chosen so that its derivative at every point `y` of its target sends each `v i y` back to `u i`. -/
theorem _root_.ContDiffOn.exists_openPartialHomeomorph_fderiv_symm_apply_eq
    (hg : ContDiffOn 𝕂 n g s) (hs : IsOpen s) (ha : a ∈ s) (hn : 1 ≤ n)
    {e : E ≃L[𝕂] F} (he : (e : E →L[𝕂] F) = fderiv 𝕂 g a) {ι : Type*} {v : ι → F → F}
    {u : ι → E} (hgu : ∀ z ∈ s, ∀ i, fderiv 𝕂 g z (u i) = v i (g z)) :
    ∃ Θ : OpenPartialHomeomorph E F, (Θ : E → F) = g ∧ a ∈ Θ.source ∧ Θ.source ⊆ s ∧
      ContDiffOn 𝕂 n Θ.symm Θ.target ∧ ∀ y ∈ Θ.target, ∀ i, fderiv 𝕂 Θ.symm y (v i y) = u i := by
  have hn0 : n ≠ 0 := by rintro rfl; exact absurd hn (by simp)
  obtain ⟨Θ, hΘ, haΘ, hΘs, hΘc⟩ := TauCeti.ContDiffOn.exists_openPartialHomeomorph hg hs ha hn he
  refine ⟨Θ, hΘ, haΘ, hΘs, hΘc, fun y hy i ↦ ?_⟩
  -- Differentiate `Θ.symm ∘ g = id`, valid near `Θ.symm y`, at `Θ.symm y`.
  have hz := Θ.map_target hy
  have hgy : g (Θ.symm y) = y := hΘ ▸ Θ.right_inv hy
  have hd : HasFDerivAt (Θ.symm ∘ g) ((fderiv 𝕂 Θ.symm y).comp (fderiv 𝕂 g (Θ.symm y)))
      (Θ.symm y) := by
    refine HasFDerivAt.comp _ ?_
      ((hg.differentiableOn hn0).differentiableAt (hs.mem_nhds (hΘs hz))).hasFDerivAt
    rw [hgy]
    exact ((hΘc.contDiffAt (Θ.open_target.mem_nhds hy)).differentiableAt hn0).hasFDerivAt
  have hid : Θ.symm ∘ g =ᶠ[𝓝 (Θ.symm y)] id :=
    eventually_of_mem (Θ.open_source.mem_nhds hz) fun x hx ↦ by
      rw [Function.comp_apply, ← hΘ, Θ.left_inv hx, id]
  have h := congrArg (fun L : E →L[𝕂] E ↦ L (u i))
    ((hd.congr_of_eventuallyEq hid.symm).unique (hasFDerivAt_id _))
  simpa only [ContinuousLinearMap.comp_apply, hgu _ (hΘs hz) i, hgy,
    ContinuousLinearMap.id_apply] using h

/-- **Invariance of the interior.** A map which is `C^n` on `s`, with `1 ≤ n`, has invertible
derivative at every interior point of `s` and maps `s` into `t` also maps `interior s` into
`interior t`: by the inverse function theorem it carries neighbourhoods to neighbourhoods. -/
theorem _root_.Set.MapsTo.interior_of_contDiffOn {t : Set F} (h : MapsTo g s t)
    (hg : ContDiffOn 𝕂 n g s) (hn : 1 ≤ n)
    (hinv : ∀ x ∈ interior s, (fderiv 𝕂 g x).IsInvertible) :
    MapsTo g (interior s) (interior t) := by
  have hn0 : n ≠ 0 := by rintro rfl; exact absurd hn (by simp)
  intro x hx
  have hs : s ∈ 𝓝 x := mem_interior_iff_mem_nhds.1 hx
  have hat : ContDiffAt 𝕂 n g x := hg.contDiffAt hs
  obtain ⟨e, he⟩ := hinv x hx
  have hd : HasFDerivAt g (e : E →L[𝕂] F) x := he ▸ (hat.differentiableAt hn0).hasFDerivAt
  rw [mem_interior_iff_mem_nhds, ← (hat.hasStrictFDerivAt hd hn0).map_nhds_eq_of_equiv]
  exact mem_map.2 (mem_of_superset hs fun y hy => h hy)

/-- **A transverse disc is a graph.** Let `z ↦ (a z, b z)` be a disc, `C^n` at `z₀` with
`n ≠ 0`, whose second component `b` has invertible derivative at `z₀`. Then there is a map `g`,
`C^n` at `b z₀`, with `g (b z₀) = a z₀` whose graph near `b z₀` is covered by the part of the disc
over any prescribed neighbourhood `U` of `z₀`: every `w` near `b z₀` is `b z` for some `z ∈ U`
with `a z = g w`.

The map `g` is `a ∘ b⁻¹` for the local inverse of `b` given by the inverse function theorem. -/
theorem exists_contDiffAt_graph_of_isInvertible {G : Type*} [NormedAddCommGroup G]
    [NormedSpace 𝕂 G] {a : E → G} {b : E → F} {b' : E →L[𝕂] F} {z₀ : E}
    (ha : ContDiffAt 𝕂 n a z₀) (hb : ContDiffAt 𝕂 n b z₀) (hb' : HasFDerivAt b b' z₀)
    (hb'i : b'.IsInvertible) (hn : n ≠ 0) {U : Set E} (hU : U ∈ 𝓝 z₀) :
    ∃ g : F → G, ContDiffAt 𝕂 n g (b z₀) ∧ g (b z₀) = a z₀ ∧
      ∀ᶠ w in 𝓝 (b z₀), ∃ z ∈ U, a z = g w ∧ b z = w := by
  obtain ⟨e, rfl⟩ := hb'i
  have hσ₀ := hb.localInverse_apply_image hb' hn
  have hσ := hb.to_localInverse hb' hn
  refine ⟨a ∘ hb.localInverse hb' hn, (hσ₀ ▸ ha).comp _ hσ, by simp [hσ₀], ?_⟩
  filter_upwards [(hb.hasStrictFDerivAt hb' hn).eventually_right_inverse,
    hσ.continuousAt.preimage_mem_nhds (hσ₀ ▸ hU)] with w hw hwU
  exact ⟨_, hwU, rfl, hw⟩

end TauCeti

section OneDim

section NormedField

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]

/-- If `f : 𝕜 → 𝕜` has a nonzero strict derivative `f'` at `a` and is injective on a neighbourhood
`s` of `a`, then `Function.invFunOn f s` has strict derivative `f'⁻¹` at `f a`. -/
theorem HasStrictDerivAt.invFunOn {f : 𝕜 → 𝕜} {f' a : 𝕜} {s : Set 𝕜}
    (hf : HasStrictDerivAt f f' a) (hf' : f' ≠ 0) (hs : s ∈ 𝓝 a) (hinj : InjOn f s) :
    HasStrictDerivAt (Function.invFunOn f s) f'⁻¹ (f a) :=
  hf.to_local_left_inverse hf' (eventually_of_mem hs fun _ hx ↦ hinj.leftInvOn_invFunOn hx)

/-- If `f : 𝕜 → 𝕜` is injective on a neighbourhood `s` of `Function.invFunOn f s y` and has a
nonzero strict derivative `f'` there, then at `y ∈ f '' s` the derivative of
`Function.invFunOn f s` is `(deriv f (Function.invFunOn f s y))⁻¹`. -/
theorem HasStrictDerivAt.deriv_invFunOn {f : 𝕜 → 𝕜} {f' y : 𝕜} {s : Set 𝕜}
    (hf : HasStrictDerivAt f f' (Function.invFunOn f s y)) (hy : y ∈ f '' s) (hf' : f' ≠ 0)
    (hs : s ∈ 𝓝 (Function.invFunOn f s y)) (hinj : InjOn f s) :
    deriv (Function.invFunOn f s) y = (deriv f (Function.invFunOn f s y))⁻¹ := by
  have h := hf.invFunOn hf' hs hinj
  rw [Function.invFunOn_eq hy] at h
  rw [h.hasDerivAt.deriv, hf.hasDerivAt.deriv]

/-- If `f : 𝕜 → 𝕜` is injective on a neighbourhood `s` of `a ∈ s` and has a nonzero strict
derivative `f'` at `a` with `f a = b`, then `dslope (Function.invFunOn f s) b` evaluates to `f'⁻¹`
at `b` and to `(Function.invFunOn f s y - a) / (y - b)` away from `b`. -/
theorem HasStrictDerivAt.dslope_invFunOn_eq {f : 𝕜 → 𝕜} {f' a b : 𝕜} {s : Set 𝕜}
    [∀ y, Decidable (y = b)] (hf : HasStrictDerivAt f f' a) (hf' : f' ≠ 0) (ha : a ∈ s)
    (hs : s ∈ 𝓝 a) (hinj : InjOn f s) (hb : f a = b) (y : 𝕜) :
    dslope (Function.invFunOn f s) b y =
      if y = b then f'⁻¹ else (Function.invFunOn f s y - a) / (y - b) := by
  subst hb
  by_cases hy : y = f a
  · simp [hy, dslope_same, (hf.invFunOn hf' hs hinj).hasDerivAt.deriv]
  · simp [hy, dslope_of_ne _ hy, slope_def_field, hinj.leftInvOn_invFunOn ha]

namespace TauCeti

/-- If `f : 𝕜 → 𝕜` has a nonzero strict derivative at every point of an open set `s`, then
`f '' s` is open. -/
theorem isOpen_image_of_hasStrictDerivAt {f f' : 𝕜 → 𝕜} {s : Set 𝕜} (hs : IsOpen s)
    (hf : ∀ x ∈ s, HasStrictDerivAt f (f' x) x) (hf' : ∀ x ∈ s, f' x ≠ 0) :
    IsOpen (f '' s) := by
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨x, hx, rfl⟩
  rw [← (hf x hx).map_nhds_eq (hf' x hx)]
  exact image_mem_map (hs.mem_nhds hx)

/-- If `f : 𝕜 → 𝕜` is injective on an open set `s` and has a nonzero strict derivative at every
point of `s`, then `Function.invFunOn f s` is continuous on `f '' s`. -/
theorem continuousOn_invFunOn_of_hasStrictDerivAt {f f' : 𝕜 → 𝕜} {s : Set 𝕜} (hs : IsOpen s)
    (hinj : InjOn f s) (hf : ∀ x ∈ s, HasStrictDerivAt f (f' x) x) (hf' : ∀ x ∈ s, f' x ≠ 0) :
    ContinuousOn (Function.invFunOn f s) (f '' s) := by
  rintro _ ⟨x, hx, rfl⟩
  exact ((hf x hx).invFunOn (hf' x hx) (hs.mem_nhds hx) hinj).hasDerivAt.continuousAt
    |>.continuousWithinAt

/-- If `f : 𝕜 → 𝕜` is injective on an open set `s` and has a nonzero strict derivative at every
point of `s`, then for any `a ∈ s` the divided difference `dslope (Function.invFunOn f s) (f a)` is
continuous on `f '' s`. -/
theorem continuousOn_dslope_invFunOn_of_hasStrictDerivAt {f f' : 𝕜 → 𝕜} {s : Set 𝕜} {a : 𝕜}
    (hs : IsOpen s) (ha : a ∈ s) (hinj : InjOn f s)
    (hf : ∀ x ∈ s, HasStrictDerivAt f (f' x) x) (hf' : ∀ x ∈ s, f' x ≠ 0) :
    ContinuousOn (dslope (Function.invFunOn f s) (f a)) (f '' s) :=
  (continuousOn_dslope
    ((isOpen_image_of_hasStrictDerivAt hs hf hf').mem_nhds (mem_image_of_mem f ha))).mpr
    ⟨continuousOn_invFunOn_of_hasStrictDerivAt hs hinj hf hf',
      ((hf a ha).invFunOn (hf' a ha) (hs.mem_nhds ha) hinj).hasDerivAt.differentiableAt⟩

end TauCeti

end NormedField

/-- If `f : 𝕂 → 𝕂` is `C^n` (`n ≠ 0`) and injective on an open set `s` with nonvanishing
derivative on `s`, then `Function.invFunOn f s` is `C^n` on `f '' s`. -/
theorem ContDiffOn.invFunOn {𝕂 : Type*} [RCLike 𝕂] {f : 𝕂 → 𝕂} {s : Set 𝕂} {n : ℕ∞ω}
    (hf : ContDiffOn 𝕂 n f s) (hn : n ≠ 0) (hs : IsOpen s) (hinj : InjOn f s)
    (hd : ∀ x ∈ s, deriv f x ≠ 0) :
    ContDiffOn 𝕂 n (Function.invFunOn f s) (f '' s) := by
  rintro _ ⟨x, hx, rfl⟩
  have hca : ContDiffAt 𝕂 n f x := hf.contDiffAt (hs.mem_nhds hx)
  have hfd := ((hca.hasStrictDerivAt_deriv hn).hasStrictFDerivAt_equiv (hd x hx)).hasFDerivAt
  have hloc : ContDiffAt 𝕂 n (hca.localInverse hfd hn) (f x) := hca.to_localInverse hfd hn
  have hmem : ∀ᶠ y in 𝓝 (f x), hca.localInverse hfd hn y ∈ s :=
    hloc.continuousAt.preimage_mem_nhds
      (by rw [hca.localInverse_apply_image hfd hn]; exact hs.mem_nhds hx)
  have hright : ∀ᶠ y in 𝓝 (f x), f (hca.localInverse hfd hn y) = y :=
    (hca.hasStrictFDerivAt hfd hn).eventually_right_inverse
  have heq : Function.invFunOn f s =ᶠ[𝓝 (f x)] hca.localInverse hfd hn := by
    filter_upwards [hmem, hright] with y hys hyr
    simpa only [hyr] using hinj.leftInvOn_invFunOn hys
  exact (hloc.congr_of_eventuallyEq heq).contDiffWithinAt

/-- If `f : 𝕂 → 𝕂` is `C^n` (`n ≠ 0`) and injective on an open set `s` with nonvanishing
derivative on `s`, then for any `a ∈ s` the divided difference
`dslope (Function.invFunOn f s) (f a)` is continuous on `f '' s`. -/
theorem ContDiffOn.continuousOn_dslope_invFunOn {𝕂 : Type*} [RCLike 𝕂] {f : 𝕂 → 𝕂}
    {s : Set 𝕂} {n : ℕ∞ω} {a : 𝕂} (hf : ContDiffOn 𝕂 n f s) (hn : n ≠ 0) (hs : IsOpen s)
    (ha : a ∈ s) (hinj : InjOn f s) (hd : ∀ x ∈ s, deriv f x ≠ 0) :
    ContinuousOn (dslope (Function.invFunOn f s) (f a)) (f '' s) :=
  TauCeti.continuousOn_dslope_invFunOn_of_hasStrictDerivAt hs ha hinj
    (fun _ hx ↦ (hf.contDiffAt (hs.mem_nhds hx)).hasStrictDerivAt_deriv hn) hd

/-- If `f : ℝ → ℝ` is strictly monotone on a neighbourhood `s` of `a ∈ s` and has a positive
strict derivative `f'` at `a`, then `dslope (Function.invFunOn f s) (f a)` is strictly positive on
`f '' s`. -/
theorem StrictMonoOn.dslope_invFunOn_pos {f : ℝ → ℝ} {f' a y : ℝ} {s : Set ℝ}
    (hmono : StrictMonoOn f s) (ha : a ∈ s) (hy : y ∈ f '' s) (hs : s ∈ 𝓝 a)
    (hf : HasStrictDerivAt f f' a) (hf' : 0 < f') :
    0 < dslope (Function.invFunOn f s) (f a) y := by
  rcases eq_or_ne y (f a) with rfl | hne
  · rw [dslope_same, (hf.invFunOn hf'.ne' hs hmono.injOn).hasDerivAt.deriv]
    exact inv_pos.mpr hf'
  · rw [dslope_of_ne _ hne]
    exact hmono.invFunOn.slope_pos (mem_image_of_mem f ha) hy hne.symm

end OneDim

end

end

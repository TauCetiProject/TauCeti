/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Darboux.Relative
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
import TauCeti.Analysis.Calculus.DifferentialForm.Regularity
import TauCeti.Analysis.Calculus.InverseFunctionTheorem
import TauCeti.Analysis.Normed.Module.Alternating.Bilinear
import TauCeti.Geometry.Manifold.Diffeomorph.Basic
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.LocalDiffeomorph

/-!
# The relative Darboux theorem along an immersion

Let `E` and `E'` be finite-dimensional real normed spaces, and let `g : E' → E` be a map of class
`C^(r + 1)` near `y₀` whose derivative at `y₀` is injective. Let `ω₀`, `ω₁` be closed two-forms of
class `C^r` (`r ≥ 1`) near `g y₀`, nondegenerate at `g y₀`, whose pullbacks along `g` agree near
`y₀`. The pullbacks may have any rank. The **relative Darboux theorem along an immersion**
(`TauCeti.exists_partialDiffeomorph_fix_immersion_compContinuousLinearMap_fderiv_eq`) gives a
`C^r` partial diffeomorphism `Φ` of `E`, defined near `g y₀`, which fixes `g y` for every `y` near
`y₀` and pulls `ω₁` back to `ω₀` on its source.

This removes the adapted coordinates from the relative Darboux theorem
`TauCeti.exists_diffeomorph_fix_zeroSection_eventually_compContinuousLinearMap_fderiv_eq`, in
which the submanifold is the zero section of a product. To straighten `g`, choose a complement `N`
of the range of `dg_{y₀}` and put

`θ : E' × N → E`, `θ (y, n) = g y + n`.

Its derivative at `(y₀, 0)` is the isomorphism `(u, n) ↦ dg_{y₀} u + n`, so by the inverse function
theorem `θ` restricts to a `C^(r + 1)` partial diffeomorphism near `(y₀, 0)`, and it sends the zero
section `(y, 0)` to `g y`. The forms `θ^* ω₀` and `θ^* ω₁` are closed, of class `C^r`,
nondegenerate at `(y₀, 0)`, and have the same pullback to the zero section, because
`dθ_{(y, 0)} ∘ inl = dg_y`. The adapted theorem gives a diffeomorphism `Ψ` of `E' × N` fixing the
zero section near `(y₀, 0)` with `Ψ^* θ^* ω₁ = θ^* ω₀` there, and `Φ = θ ∘ Ψ ∘ θ⁻¹` is the
required partial diffeomorphism. Pulling back along `θ` costs one derivative, which is why `g` is
assumed one degree more regular than the forms.

This is the local, coordinate form of the point-germ relative Darboux theorem for an arbitrary
immersed submanifold, consumed by its version on manifolds.

As in `TauCeti.exists_diffeomorph_eventually_compContinuousLinearMap_fderiv_eq`, forms are Mathlib's
continuous alternating maps with its exterior derivative `extDeriv`, the pullback of `ω` along `ψ`
at `x` is `(ω (ψ x)).compContinuousLinearMap (fderiv ℝ ψ x)`, and nondegeneracy of `ω(x)` says that
no nonzero `v` has `ω(x)(v, w) = 0` for every `w`.

## References

* A. Weinstein, *Symplectic manifolds and their Lagrangian submanifolds*, Advances in Mathematics
  6 (1971), 329–346 (the relative Darboux theorem).
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 7 (Moser's relative theorem).
-/

public section

open Set Filter Topology
open scoped Manifold ContDiff

namespace TauCeti

variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']

omit [FiniteDimensional ℝ E] in
/-- **The relative Darboux theorem through a straightening chart.** Let `Θ` be a partial
diffeomorphism of class `C^(r + 1)` from `E' × N` to `E`, defined at `(y₀, 0)`, with derivative
`e` there, and mapping into an open set `W`. Let `ω₀`, `ω₁` be closed `C^r` two-forms on `W`,
nondegenerate at `Θ (y₀, 0)`, with the same pullback along `y ↦ Θ (y, 0)` wherever this is defined.
Then some `C^r` partial diffeomorphism of `E` with `Θ (y₀, 0)` in its source fixes `Θ (y, 0)` for
`y` near `y₀` and pulls `ω₁` back to `ω₀` on its source. -/
private theorem exists_partialDiffeomorph_fix_image_zeroSection {N : Type*}
    [NormedAddCommGroup N] [NormedSpace ℝ N] [FiniteDimensional ℝ N]
    {ω₀ ω₁ : E → E [⋀^Fin 2]→L[ℝ] ℝ} {W : Set E} {r : ℕ∞} (hr : 1 ≤ r) (hW : IsOpen W)
    (hω₀ : ContDiffOn ℝ r ω₀ W) (hω₁ : ContDiffOn ℝ r ω₁ W) (hdω₀ : ∀ x ∈ W, extDeriv ω₀ x = 0)
    (hdω₁ : ∀ x ∈ W, extDeriv ω₁ x = 0) (Θ : OpenPartialHomeomorph (E' × N) E)
    (hΘ : ContDiffOn ℝ (r + 1) Θ Θ.source) (hΘsymm : ContDiffOn ℝ (r + 1) Θ.symm Θ.target)
    (hΘW : MapsTo Θ Θ.source W) {y₀ : E'} (hy₀ : (y₀, (0 : N)) ∈ Θ.source)
    (e : (E' × N) ≃L[ℝ] E) (he : (e : E' × N →L[ℝ] E) = fderiv ℝ Θ (y₀, 0))
    (htan : ∀ q : E', (q, (0 : N)) ∈ Θ.source →
      (ω₁ (Θ (q, 0))).compContinuousLinearMap ((fderiv ℝ Θ (q, 0)).comp (.inl ℝ E' N)) =
        (ω₀ (Θ (q, 0))).compContinuousLinearMap ((fderiv ℝ Θ (q, 0)).comp (.inl ℝ E' N)))
    (hnd₀ : ∀ v, (∀ w, ω₀ (Θ (y₀, 0)) ![v, w] = 0) → v = 0)
    (hnd₁ : ∀ v, (∀ w, ω₁ (Θ (y₀, 0)) ![v, w] = 0) → v = 0) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E r, Θ (y₀, 0) ∈ Φ.source ∧
      (∀ᶠ y in 𝓝 y₀, Φ (Θ (y, 0)) = Θ (y, 0)) ∧
      ∀ x ∈ Φ.source, (ω₁ (Φ x)).compContinuousLinearMap (fderiv ℝ Φ x) = ω₀ x := by
  have hr1 : (1 : WithTop ℕ∞) ≤ r := by exact_mod_cast hr
  have hr2 : (2 : WithTop ℕ∞) ≤ r + 1 :=
    one_add_one_eq_two (R := WithTop ℕ∞) ▸ add_le_add_left hr1 1
  -- The pulled-back forms `Θ^* η` satisfy the hypotheses of the adapted theorem on `Θ.source`.
  let pb (η : E → E [⋀^Fin 2]→L[ℝ] ℝ) : E' × N → (E' × N) [⋀^Fin 2]→L[ℝ] ℝ :=
    fun z ↦ (η (Θ z)).compContinuousLinearMap (fderiv ℝ Θ z)
  have hpb (η : E → E [⋀^Fin 2]→L[ℝ] ℝ) (hη : ContDiffOn ℝ r η W) :
      ContDiffOn ℝ r (pb η) Θ.source := fun z hz ↦
    ((hΘ.contDiffAt (Θ.open_source.mem_nhds hz)).differentialForm_pullback
      (hη.contDiffAt (hW.mem_nhds (hΘW hz)))).contDiffWithinAt
  have hdpb (η : E → E [⋀^Fin 2]→L[ℝ] ℝ) (hη : ContDiffOn ℝ r η W)
      (hdη : ∀ x ∈ W, extDeriv η x = 0) : ∀ z ∈ Θ.source, extDeriv (pb η) z = 0 := fun z hz ↦ by
    rw [extDeriv_pullback ((hη.contDiffAt (hW.mem_nhds (hΘW hz))).differentiableAt
      (lt_of_lt_of_le zero_lt_one hr1).ne') (hΘ.contDiffAt (Θ.open_source.mem_nhds hz))
      (by simpa using hr2), hdη _ (hΘW hz)]
    ext v
    simp
  have htanpb (q : E') (hq : (q, (0 : N)) ∈ Θ.source) :
      (pb ω₁ (q, 0)).compContinuousLinearMap (.inl ℝ E' N) =
        (pb ω₀ (q, 0)).compContinuousLinearMap (.inl ℝ E' N) := by
    ext v
    simpa [pb, Function.comp_def] using congrArg (· v) (htan q hq)
  have hndpb (η : E → E [⋀^Fin 2]→L[ℝ] ℝ) (hnd : ∀ v, (∀ w, η (Θ (y₀, 0)) ![v, w] = 0) → v = 0) :
      ∀ v, (∀ w, pb η (y₀, 0) ![v, w] = 0) → v = 0 := by
    simpa only [pb, ← he] using (η (Θ (y₀, 0))).nondegenerate_compContinuousLinearEquiv e hnd
  -- The adapted theorem gives `Ψ`; restrict to an open neighbourhood `O` of `(y₀, 0)` on which
  -- its pullback identity holds and which it maps into `Θ.source`, and conjugate back by `Θ`.
  obtain ⟨Ψ, hfix, hΨ⟩ :=
    exists_diffeomorph_fix_zeroSection_eventually_compContinuousLinearMap_fderiv_eq hr
      Θ.open_source hy₀ (hpb ω₀ hω₀) (hpb ω₁ hω₁) (hdpb ω₀ hω₀ hdω₀) (hdpb ω₁ hω₁ hdω₁) htanpb
      (hndpb ω₀ hnd₀) (hndpb ω₁ hnd₁)
  have hOmem : Θ.source ∩ Ψ ⁻¹' Θ.source ∩
      {z | (pb ω₁ (Ψ z)).compContinuousLinearMap (fderiv ℝ Ψ z) = pb ω₀ z} ∈ 𝓝 (y₀, 0) :=
    inter_mem (inter_mem (Θ.open_source.mem_nhds hy₀)
      (Ψ.continuous.continuousAt.preimage_mem_nhds (by
        rw [hfix.self_of_nhds]
        exact Θ.open_source.mem_nhds hy₀))) hΨ
  obtain ⟨O, hOsub, hOo, hy₀O⟩ := mem_nhds_iff.1 hOmem
  have hΨc : (Ψ.toPartialDiffeomorph : E' × N → E' × N) = Ψ := funext fun _ ↦ by simp
  obtain ⟨Φ, hΦO, hΦ⟩ :=
    exists_partialDiffeomorph_compContinuousLinearMap_fderiv_eq_of_conj hr Θ
      (hΘ.of_le le_self_add) (hΘsymm.of_le le_self_add) Ψ.toPartialDiffeomorph hOo
      (fun z hz ↦ (hOsub hz).1.1) (fun _ _ ↦ by simp)
      (by rw [hΨc]; exact fun z hz ↦ (hOsub hz).1.2) (by rw [hΨc]; exact fun z hz ↦ (hOsub hz).2)
  refine ⟨Φ, (hΦO _ hy₀O).1, ?_, hΦ⟩
  have hc : Tendsto (fun y : E' ↦ ((y, 0) : E' × N)) (𝓝 y₀) (𝓝 (y₀, 0)) :=
    (continuous_id.prodMk continuous_const).tendsto y₀
  filter_upwards [hc.eventually (hOo.mem_nhds hy₀O), hfix] with y hyO hy
  rw [(hΦO _ hyO).2, hΨc, hy]

/-- **The relative Darboux theorem along an immersion.** Let `g : E' → E` be of class `C^(r + 1)`
near `y₀` with injective derivative at `y₀`, and let `ω₀`, `ω₁` be closed `C^r` two-forms (`r ≥ 1`)
on an open set `W ∋ g y₀`, both nondegenerate at `g y₀`, whose pullbacks along `g` agree near `y₀`.
Then some `C^r` partial diffeomorphism `Φ` of `E` with `g y₀` in its source fixes `g y` for every
`y` near `y₀` and pulls `ω₁` back to `ω₀` on its source. The pullbacks along `g` may be degenerate,
of any rank. -/
theorem exists_partialDiffeomorph_fix_immersion_compContinuousLinearMap_fderiv_eq
    {ω₀ ω₁ : E → E [⋀^Fin 2]→L[ℝ] ℝ} {W : Set E} {g : E' → E} {y₀ : E'} {r : ℕ∞}
    (hr : 1 ≤ r) (hW : IsOpen W) (hy₀ : g y₀ ∈ W) (hω₀ : ContDiffOn ℝ r ω₀ W)
    (hω₁ : ContDiffOn ℝ r ω₁ W) (hdω₀ : ∀ x ∈ W, extDeriv ω₀ x = 0)
    (hdω₁ : ∀ x ∈ W, extDeriv ω₁ x = 0) (hg : ∀ᶠ y in 𝓝 y₀, ContDiffAt ℝ (r + 1) g y)
    (hinj : Function.Injective (fderiv ℝ g y₀))
    (htan : ∀ᶠ y in 𝓝 y₀, (ω₁ (g y)).compContinuousLinearMap (fderiv ℝ g y) =
      (ω₀ (g y)).compContinuousLinearMap (fderiv ℝ g y))
    (hnd₀ : ∀ v, (∀ w, ω₀ (g y₀) ![v, w] = 0) → v = 0)
    (hnd₁ : ∀ v, (∀ w, ω₁ (g y₀) ![v, w] = 0) → v = 0) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E r, g y₀ ∈ Φ.source ∧
      (∀ᶠ y in 𝓝 y₀, Φ (g y) = g y) ∧
      ∀ x ∈ Φ.source, (ω₁ (Φ x)).compContinuousLinearMap (fderiv ℝ Φ x) = ω₀ x := by
  -- A complement `N` of the range of `dg_{y₀}`, and the straightening map `θ (y, n) = g y + n`,
  -- on an open set `s ∋ (y₀, 0)` inside `U × N`, where `g` is `C^(r + 1)` and the pullbacks agree.
  obtain ⟨N, hN⟩ := Submodule.exists_isCompl (LinearMap.range (fderiv ℝ g y₀).toLinearMap)
  let θ : E' × N → E := fun z ↦ g z.1 + z.2
  have hθ0 (y : E') : θ (y, 0) = g y := by simp [θ]
  obtain ⟨U, hUsub, hUo, hy₀U⟩ := mem_nhds_iff.1 (hg.and htan)
  have hθU : ContDiffOn ℝ (r + 1) θ (U ×ˢ univ) := by
    have hgU : ContDiffOn ℝ (r + 1) g U := fun y hy ↦ (hUsub hy).1.contDiffWithinAt
    exact (hgU.comp contDiffOn_fst fun z (hz : z ∈ U ×ˢ univ) ↦ hz.1).add
      (N.subtypeL.contDiff.comp contDiff_snd).contDiffOn
  have hθd (z : E' × N) (hz : z.1 ∈ U) : fderiv ℝ θ z =
      (fderiv ℝ g z.1).comp (ContinuousLinearMap.fst ℝ E' N) +
        N.subtypeL.comp (ContinuousLinearMap.snd ℝ E' N) :=
    ((((hUsub hz).1.differentiableAt (by simp)).hasFDerivAt.comp z hasFDerivAt_fst).add
      (N.subtypeL.hasFDerivAt.comp z hasFDerivAt_snd)).fderiv
  let s : Set (E' × N) := U ×ˢ univ ∩ θ ⁻¹' W
  have hs : IsOpen s := hθU.continuousOn.isOpen_inter_preimage (hUo.prod isOpen_univ) hW
  have hz₀ : ((y₀, 0) : E' × N) ∈ s := ⟨⟨hy₀U, trivial⟩, by simpa [hθ0] using hy₀⟩
  -- The derivative of `θ` at `(y₀, 0)` is a linear isomorphism, so by the inverse function theorem
  -- `θ` is a partial diffeomorphism `Θ` near `(y₀, 0)`.
  let e : (E' × N) ≃L[ℝ] E := (((LinearEquiv.ofInjective _ hinj).prodCongr
    (LinearEquiv.refl ℝ N)).trans (Submodule.prodEquivOfIsCompl _ _ hN)).toContinuousLinearEquiv
  have he : (e : E' × N →L[ℝ] E) = fderiv ℝ θ (y₀, 0) := by
    rw [hθd _ hy₀U]
    ext z <;> simp [e]
  obtain ⟨Θ, hΘ, hz₀Θ, hΘs, hΘsymm⟩ := TauCeti.ContDiffOn.exists_openPartialHomeomorph
    (hθU.mono inter_subset_left) hs hz₀ le_add_self he
  have hΘ0 (y : E') : Θ (y, 0) = g y := by rw [hΘ, hθ0]
  -- Along the zero section `Θ (y, 0) = g y` and `dΘ_{(y, 0)} ∘ inl = dg_y`.
  have htanΘ (q : E') (hq : (q, (0 : N)) ∈ Θ.source) :
      (ω₁ (Θ (q, 0))).compContinuousLinearMap ((fderiv ℝ Θ (q, 0)).comp (.inl ℝ E' N)) =
        (ω₀ (Θ (q, 0))).compContinuousLinearMap ((fderiv ℝ Θ (q, 0)).comp (.inl ℝ E' N)) := by
    have hinl : (fderiv ℝ Θ (q, 0)).comp (.inl ℝ E' N) = fderiv ℝ g q := by
      rw [hΘ, hθd _ (hΘs hq).1.1]
      ext u
      simp
    rw [hinl, hΘ0]
    exact (hUsub (hΘs hq).1.1).2
  obtain ⟨Φ, hΦ₀, hfix, hΦ⟩ := exists_partialDiffeomorph_fix_image_zeroSection hr hW hω₀ hω₁ hdω₀
    hdω₁ Θ (hΘ ▸ (hθU.mono inter_subset_left).mono hΘs) hΘsymm
    (fun z hz ↦ by rw [hΘ]; exact (hΘs hz).2) hz₀Θ e (by rw [hΘ]; exact he) htanΘ
    (hΘ0 y₀ ▸ hnd₀) (hΘ0 y₀ ▸ hnd₁)
  exact ⟨Φ, hΘ0 y₀ ▸ hΦ₀, by simpa only [hΘ0] using hfix, hΦ⟩

end TauCeti

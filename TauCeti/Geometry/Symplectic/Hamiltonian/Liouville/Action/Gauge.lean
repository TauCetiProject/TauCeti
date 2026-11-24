/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.Liouville.Action.Uniqueness
public import TauCeti.Analysis.Calculus.DifferentialForm.Gradient

/-!
# The angle gauge of action-angle coordinates

Let `σ` be a symplectic form on a boundaryless manifold `M`, and let `F : M → (ι → ℝ)` be a smooth
family of pairwise Poisson-commuting functions with complete Hamiltonian vector fields, with the
conventions `ι_{X_f} σ = df` and `{f, g} = σ(X_f, X_g) = df(X_g)`. Their flows generate an action
`v • y` of `ι → ℝ` on `M` (`TauCeti.SmoothTwoForm.IsSymplectic.hamiltonianFlowAction`).

Action-angle coordinates are built from an isotropic section `s` of `F`, periods `λ⁽ⁱ⁾` along it
and action variables `A`, `dAᵢ = (2π)⁻¹ ∑ⱼ λ⁽ⁱ⁾ⱼ dcⱼ`, through the angle map
`Ψ(θ, c) = (∑ᵢ (θᵢ / 2π) λ⁽ⁱ⁾(c)) • s(c)` (`TauCeti.SmoothTwoForm.IsSymplectic.angleMap`), which
pulls `σ` back to `∑ᵢ dθᵢ ∧ dAᵢ`. Along a fixed section these data are unique up to integral affine
changes `(θ, I) ↦ (P⁻ᵀ θ, P I + b)`
(`TauCeti.SmoothTwoForm.IsSymplectic.exists_eq_mulVec_add_and_angleMap_eq`). This file accounts for
the choice of the section, which contributes the second ambiguity, the **angle gauge**
`(θ, I) ↦ (θ + ∂S/∂I, I)` for a function `S` of the actions alone.

This file takes a second section through the same orbits as `s` in the form `h • s` for a given
differentiable map `h : (ι → ℝ) → (ι → ℝ)`; constructing such a lift `h` from an arbitrary second
section is not done here. Moving `s` by `h` changes `s^* σ` by `∑ᵢ dhᵢ ∧ dcᵢ`
(`TauCeti.SmoothTwoForm.IsSymplectic.eval₂_mfderiv_hamiltonianFlowAction_section`). So for an
isotropic `s`, the moved section is isotropic exactly when the one-form `∑ᵢ hᵢ dcᵢ` is closed
(`TauCeti.SmoothTwoForm.IsSymplectic.eval₂_mfderiv_hamiltonianFlowAction_section_eq_zero_iff`). On
a star-convex set of values this makes `h` a gradient, `∑ᵢ hᵢ dcᵢ = dS`, by the Poincaré lemma
(`StarConvex.exists_contDiffOn_forall_hasFDerivAt_of_fderiv_dotProduct_comm`,
`exists_contDiffOn_hasFDerivAt_of_eval₂_mfderiv_hamiltonianFlowAction_section_eq_zero`), and
conversely every gradient keeps an isotropic section isotropic
(`eval₂_mfderiv_hamiltonianFlowAction_section_eq_zero_of_hasFDerivAt`).

The angle map of `h • s` is the angle map of `s` followed by the action of `h`
(`TauCeti.SmoothTwoForm.IsSymplectic.angleMap_hamiltonianFlowAction_section`), since the action is
commutative. If `∑ᵢ gᵢ dAᵢ = ∑ⱼ hⱼ dcⱼ`, this shifts the angles by `g`:

`Ψ_{h • s}(θ, c) = Ψ_s(θ + g, c)`

(`TauCeti.SmoothTwoForm.IsSymplectic.angleMap_hamiltonianFlowAction_section_of_fderiv`). For a
gradient `h`, the condition reads `∑ᵢ gᵢ dAᵢ = dS`, that is `g = ∂S/∂I` in the actions `I = A`.

Combining both ambiguities: two systems of isotropic action-angle data over a star-convex set of
values, the second section being the move `h • s` of the first by a `C¹` map `h`, are related by
an integral affine change of the actions and an angle gauge,

`A' = P A + b` and `Ψ'(θ, c) = Ψ(θ P + g(c), c)` with `∑ᵢ gᵢ dAᵢ = dS`

(`exists_eq_mulVec_add_and_angleMap_hamiltonianFlowAction_section_eq`, in the namespace
`TauCeti.SmoothTwoForm.IsSymplectic`).

## Main results

All in the namespace `TauCeti.SmoothTwoForm.IsSymplectic`:

* `eval₂_mfderiv_hamiltonianFlowAction_section_eq_zero_iff`: an isotropic section moved by `h`
  stays isotropic exactly when the derivative of `h` is symmetric.
* `exists_contDiffOn_hasFDerivAt_of_eval₂_mfderiv_hamiltonianFlowAction_section_eq_zero`: over a
  star-convex set, if `s` and `h • s` are both isotropic, then `∑ⱼ hⱼ dcⱼ = dS`.
* `eval₂_mfderiv_hamiltonianFlowAction_section_eq_zero_of_hasFDerivAt`: moving an isotropic
  section along a gradient keeps it isotropic.
* `angleMap_hamiltonianFlowAction_section_of_fderiv`: the angle gauge `θ ↦ θ + g`.
* `exists_eq_mulVec_add_and_angleMap_hamiltonianFlowAction_section_eq`: action-angle data are
  unique up to integral affine changes and angle gauge.

## References

* J. J. Duistermaat, *On global action-angle coordinates*, Comm. Pure Appl. Math. 33 (1980),
  687–706, Section 2 (Lagrangian sections and the ambiguity of action-angle coordinates).
* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Section 50 (action-angle variables).
-/

public section

open Set Filter Module Topology Function Real Matrix
open ContinuousLinearMap (proj)
open scoped Manifold ContDiff

namespace TauCeti

namespace SmoothTwoForm

namespace IsSymplectic

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [BoundarylessManifold I M]
  {σ : SmoothTwoForm I M} (hσ : σ.IsSymplectic)
  {ι : Type*} [Fintype ι] {F : M → ι → ℝ} (hF : ContMDiff I 𝓘(ℝ, ι → ℝ) ∞ F)
  (hcomm : ∀ i j x, σ.poissonBracket (F · i) (F · j) x = 0)
  (hc : ∀ i, IsCompleteVectorField (σ.hamiltonianVectorField (F · i)))
  {s : (ι → ℝ) → M} {h : (ι → ℝ) → ι → ℝ} {c : ι → ℝ}

include hσ hF hcomm hc

/-! ### Moving isotropic sections -/

/-- **When a moved isotropic section is isotropic.** Let `s` be a section of `F` near `c`,
differentiable and isotropic at `c`, and let `h` be differentiable at `c`. Then the moved section
`h • s` is isotropic at `c` exactly when the one-form `∑ᵢ hᵢ dcᵢ` is closed at `c`, that is, when
the derivative of `h` at `c` is symmetric: `∂ⱼ hᵢ = ∂ᵢ hⱼ`. -/
theorem eval₂_mfderiv_hamiltonianFlowAction_section_eq_zero_iff
    (hs : MDifferentiableAt 𝓘(ℝ, ι → ℝ) I s c) (hFs : ∀ᶠ c' in 𝓝 c, F (s c') = c')
    (hL : ∀ b b' : ι → ℝ, SmoothBundleForm.eval₂ σ (s c) (mfderiv 𝓘(ℝ, ι → ℝ) I s c b)
      (mfderiv 𝓘(ℝ, ι → ℝ) I s c b') = 0)
    (hh : DifferentiableAt ℝ h c) :
    (∀ b b' : ι → ℝ,
      SmoothBundleForm.eval₂ σ ((hσ.hamiltonianFlowAction hF hcomm hc (h c)).toMul (s c))
        (mfderiv 𝓘(ℝ, ι → ℝ) I (fun c ↦ (hσ.hamiltonianFlowAction hF hcomm hc (h c)).toMul (s c))
          c b)
        (mfderiv 𝓘(ℝ, ι → ℝ) I (fun c ↦ (hσ.hamiltonianFlowAction hF hcomm hc (h c)).toMul (s c))
          c b') = 0) ↔
      ∀ b b' : ι → ℝ, fderiv ℝ h c b ⬝ᵥ b' = fderiv ℝ h c b' ⬝ᵥ b := by
  simp only [hσ.eval₂_mfderiv_hamiltonianFlowAction_section hF hcomm hc hs hFs hh, hL, zero_add,
    sub_eq_zero]

/-- **A move between isotropic sections is a gradient.** Let `s` be an isotropic differentiable
section of `F` over an open set `D`, star-convex with respect to `c₀`, and let `h` be a `Cʳ` map
on `D`, `r ≥ 1`, such that the moved section `h • s` is isotropic on `D` as well. Then `h` is the
gradient of a `Cʳ⁺¹` function `S` on `D`: `dS = ∑ⱼ hⱼ dcⱼ`. -/
theorem exists_contDiffOn_hasFDerivAt_of_eval₂_mfderiv_hamiltonianFlowAction_section_eq_zero
    {D : Set (ι → ℝ)} {c₀ : ι → ℝ} (hDo : IsOpen D) (hD : StarConvex ℝ c₀ D)
    (hs : MDifferentiableOn 𝓘(ℝ, ι → ℝ) I s D) (hFs : ∀ c ∈ D, F (s c) = c)
    (hL : ∀ c ∈ D, ∀ b b' : ι → ℝ, SmoothBundleForm.eval₂ σ (s c)
      (mfderiv 𝓘(ℝ, ι → ℝ) I s c b) (mfderiv 𝓘(ℝ, ι → ℝ) I s c b') = 0)
    {r : ℕ∞} (hr : 1 ≤ r) (hh : ContDiffOn ℝ r h D)
    (hL' : ∀ c ∈ D, ∀ b b' : ι → ℝ,
      SmoothBundleForm.eval₂ σ ((hσ.hamiltonianFlowAction hF hcomm hc (h c)).toMul (s c))
        (mfderiv 𝓘(ℝ, ι → ℝ) I (fun c ↦ (hσ.hamiltonianFlowAction hF hcomm hc (h c)).toMul (s c))
          c b)
        (mfderiv 𝓘(ℝ, ι → ℝ) I (fun c ↦ (hσ.hamiltonianFlowAction hF hcomm hc (h c)).toMul (s c))
          c b') = 0) :
    ∃ S : (ι → ℝ) → ℝ, ContDiffOn ℝ (r + 1) S D ∧
      ∀ c ∈ D, HasFDerivAt S (∑ j, h c j • (proj j : (ι → ℝ) →L[ℝ] ℝ)) c := by
  have hr' : (r : ℕ∞ω) ≠ 0 := (lt_of_lt_of_le zero_lt_one (by exact_mod_cast hr)).ne'
  -- The isotropy of `s` and `h • s` makes the derivative of `h` symmetric.
  refine hD.exists_contDiffOn_forall_hasFDerivAt_of_fderiv_dotProduct_comm hDo hr hh
    fun c hcD ↦ ?_
  have hcn := hDo.mem_nhds hcD
  exact (hσ.eval₂_mfderiv_hamiltonianFlowAction_section_eq_zero_iff hF hcomm hc
    ((hs c hcD).mdifferentiableAt hcn) (eventually_of_mem hcn hFs) (hL c hcD)
    ((hh.differentiableOn hr' c hcD).differentiableAt hcn)).1 (hL' c hcD)

/-- **Moving an isotropic section along a gradient keeps it isotropic.** Let `s` be a section of
`F` near `c`, differentiable and isotropic at `c`, and let `h`, differentiable at `c`, be a
gradient near `c`: `dS = ∑ⱼ hⱼ dcⱼ` near `c` for a function `S`. Then the moved section `h • s` is
isotropic at `c`. -/
theorem eval₂_mfderiv_hamiltonianFlowAction_section_eq_zero_of_hasFDerivAt
    (hs : MDifferentiableAt 𝓘(ℝ, ι → ℝ) I s c) (hFs : ∀ᶠ c' in 𝓝 c, F (s c') = c')
    (hL : ∀ b b' : ι → ℝ, SmoothBundleForm.eval₂ σ (s c) (mfderiv 𝓘(ℝ, ι → ℝ) I s c b)
      (mfderiv 𝓘(ℝ, ι → ℝ) I s c b') = 0)
    (hh : DifferentiableAt ℝ h c) {S : (ι → ℝ) → ℝ}
    (hSh : ∀ᶠ c' in 𝓝 c, HasFDerivAt S (∑ j, h c' j • (proj j : (ι → ℝ) →L[ℝ] ℝ)) c')
    (b b' : ι → ℝ) :
    SmoothBundleForm.eval₂ σ ((hσ.hamiltonianFlowAction hF hcomm hc (h c)).toMul (s c))
      (mfderiv 𝓘(ℝ, ι → ℝ) I (fun c ↦ (hσ.hamiltonianFlowAction hF hcomm hc (h c)).toMul (s c))
        c b)
      (mfderiv 𝓘(ℝ, ι → ℝ) I (fun c ↦ (hσ.hamiltonianFlowAction hF hcomm hc (h c)).toMul (s c))
        c b') = 0 :=
  (hσ.eval₂_mfderiv_hamiltonianFlowAction_section_eq_zero_iff hF hcomm hc hs hFs hL hh).2
    (fderiv_dotProduct_comm_of_eventually_hasFDerivAt hh hSh) b b'

/-! ### The angle gauge -/

/-- **Moving the section moves the angle map.** The angle map of the moved map `h • s` is the angle
map of `s` followed by the action of `h`: `Ψ_{h • s}(θ, c) = h(c) • Ψ_s(θ, c)`. -/
theorem angleMap_hamiltonianFlowAction_section (p : ι → (ι → ℝ) → ι → ℝ)
    (q : (ι → ℝ) × (ι → ℝ)) :
    hσ.angleMap hF hcomm hc (fun c ↦ (hσ.hamiltonianFlowAction hF hcomm hc (h c)).toMul (s c)) p
        q =
      (hσ.hamiltonianFlowAction hF hcomm hc (h q.2)).toMul (hσ.angleMap hF hcomm hc s p q) := by
  rw [angleMap_apply, angleMap_apply, ← hσ.hamiltonianFlowAction_add_apply hF hcomm hc, add_comm,
    hσ.hamiltonianFlowAction_add_apply hF hcomm hc]

/-- **The angle gauge.** Let `A` be action variables at `c`, `dAᵢ = (2π)⁻¹ ∑ⱼ λ⁽ⁱ⁾ⱼ dcⱼ`, and let
`g` satisfy `∑ᵢ gᵢ dAᵢ = ∑ⱼ hⱼ(c) dcⱼ` at `c`. Then the angle map of the moved section `h • s` is
the angle map of `s` with the angles shifted by `g`:

`Ψ_{h • s}(θ, c) = Ψ_s(θ + g, c)`.

When `dS = ∑ⱼ hⱼ dcⱼ`, the condition says `∑ᵢ gᵢ dAᵢ = dS`, that is `g = ∂S/∂I` in the actions
`I = A`. -/
theorem angleMap_hamiltonianFlowAction_section_of_fderiv {p : ι → (ι → ℝ) → ι → ℝ}
    {A : (ι → ℝ) → ι → ℝ}
    (hA : ∀ i, HasFDerivAt (fun c ↦ A c i)
      ((2 * π)⁻¹ • ∑ j, p i c j • (proj j : (ι → ℝ) →L[ℝ] ℝ)) c)
    {g : ι → ℝ} (hg : ∀ w, ∑ i, g i * fderiv ℝ (fun c ↦ A c i) c w = h c ⬝ᵥ w) (θ : ι → ℝ) :
    hσ.angleMap hF hcomm hc (fun c ↦ (hσ.hamiltonianFlowAction hF hcomm hc (h c)).toMul (s c)) p
        (θ, c) =
      hσ.angleMap hF hcomm hc s p (θ + g, c) := by
  rw [hσ.angleMap_hamiltonianFlowAction_section hF hcomm hc,
    hσ.hamiltonianFlowAction_apply_angleMap_of_fderiv hF hcomm hc hA hg]

/-- **Action-angle data are unique up to integral affine changes and angle gauge.** Let `s` be an
isotropic differentiable section of `F` over an open set `D` of values, star-convex with respect
to `c₀`, and let `h` be a `C¹` map on `D` such that the moved section `s' = h • s`, through the
same orbits, is isotropic as well. Let `λ⁽ⁱ⁾` and `λ'⁽ⁱ⁾` be continuous families of vectors on `D`,
the `λ⁽ⁱ⁾(c)` linearly independent, with action variables `A` and `A'`:
`dAᵢ = (2π)⁻¹ ∑ⱼ λ⁽ⁱ⁾ⱼ dcⱼ` and `dA'ᵢ = (2π)⁻¹ ∑ⱼ λ'⁽ⁱ⁾ⱼ dcⱼ`. Suppose both describe the period
lattice: for every `c ∈ D`, the periods of `s c` form the transpose lattice `2π (DA_c)ᵀ ℤ^ι`, and
the periods of `s' c` form `2π (DA'_c)ᵀ ℤ^ι`. Then there are `P ∈ GL(ι, ℤ)`, `b : ι → ℝ`, a `C²`
function `S` on `D` and angle shifts `g(c)` such that on `D`

* the actions change by the integral affine map `A' = P A + b`;
* the periods change by `λ'⁽ⁱ⁾ = ∑ₖ Pᵢₖ λ⁽ᵏ⁾`;
* the angle shift is a gradient in the actions: `∑ᵢ gᵢ dAᵢ = dS`, that is `g = ∂S/∂I`;
* the angle maps `Ψ` of `(s, λ)` and `Ψ'` of `(s', λ')` are related by
  `Ψ'(θ, c) = Ψ(θ P + g(c), c)`.

In action-angle coordinates `(θ, I)` this is the composite of the integral affine change
`(θ, I) ↦ (P⁻ᵀ θ, P I + b)` with the angle gauge `(θ, I) ↦ (θ + ∂S/∂I, I)`. -/
theorem exists_eq_mulVec_add_and_angleMap_hamiltonianFlowAction_section_eq [DecidableEq ι]
    {D : Set (ι → ℝ)} {c₀ : ι → ℝ} (hDo : IsOpen D) (hD : StarConvex ℝ c₀ D)
    (hs : MDifferentiableOn 𝓘(ℝ, ι → ℝ) I s D) (hFs : ∀ c ∈ D, F (s c) = c)
    (hL : ∀ c ∈ D, ∀ b b' : ι → ℝ, SmoothBundleForm.eval₂ σ (s c)
      (mfderiv 𝓘(ℝ, ι → ℝ) I s c b) (mfderiv 𝓘(ℝ, ι → ℝ) I s c b') = 0)
    (hh : ContDiffOn ℝ 1 h D)
    (hL' : ∀ c ∈ D, ∀ b b' : ι → ℝ,
      SmoothBundleForm.eval₂ σ ((hσ.hamiltonianFlowAction hF hcomm hc (h c)).toMul (s c))
        (mfderiv 𝓘(ℝ, ι → ℝ) I (fun c ↦ (hσ.hamiltonianFlowAction hF hcomm hc (h c)).toMul (s c))
          c b)
        (mfderiv 𝓘(ℝ, ι → ℝ) I (fun c ↦ (hσ.hamiltonianFlowAction hF hcomm hc (h c)).toMul (s c))
          c b') = 0)
    {p p' : ι → (ι → ℝ) → ι → ℝ} {A A' : (ι → ℝ) → ι → ℝ}
    (hp : ∀ i, ContinuousOn (p i) D) (hp' : ∀ i, ContinuousOn (p' i) D)
    (hli : ∀ c ∈ D, LinearIndependent ℝ fun i ↦ p i c)
    (hA : ∀ c ∈ D, ∀ i, HasFDerivAt (fun c ↦ A c i)
      ((2 * π)⁻¹ • ∑ j, p i c j • (proj j : (ι → ℝ) →L[ℝ] ℝ)) c)
    (hA' : ∀ c ∈ D, ∀ i, HasFDerivAt (fun c ↦ A' c i)
      ((2 * π)⁻¹ • ∑ j, p' i c j • (proj j : (ι → ℝ) →L[ℝ] ℝ)) c)
    (hΛ : ∀ c ∈ D, hσ.hamiltonianFlowStabilizer hF hcomm hc (s c) =
      ((2 * π) • fderiv ℝ A c).transposeLattice)
    (hΛ' : ∀ c ∈ D, hσ.hamiltonianFlowStabilizer hF hcomm hc
      ((hσ.hamiltonianFlowAction hF hcomm hc (h c)).toMul (s c)) =
        ((2 * π) • fderiv ℝ A' c).transposeLattice) :
    ∃ (P : GL ι ℤ) (b : ι → ℝ) (S : (ι → ℝ) → ℝ) (g : (ι → ℝ) → ι → ℝ), ContDiffOn ℝ 2 S D ∧
      ∀ c ∈ D, A' c = (P : Matrix ι ι ℤ).map (↑) *ᵥ A c + b ∧
        (∀ i, p' i c = ∑ k, ((P : Matrix ι ι ℤ) i k : ℝ) • p k c) ∧
        HasFDerivAt S (∑ i, g c i • fderiv ℝ (fun c ↦ A c i) c) c ∧
        ∀ θ, hσ.angleMap hF hcomm hc
            (fun c ↦ (hσ.hamiltonianFlowAction hF hcomm hc (h c)).toMul (s c)) p' (θ, c) =
          hσ.angleMap hF hcomm hc s p (θ ᵥ* (P : Matrix ι ι ℤ).map (↑) + g c, c) := by
  -- The move `h` is the gradient of a function `S`.
  obtain ⟨S, hS, hSh⟩ :=
    hσ.exists_contDiffOn_hasFDerivAt_of_eval₂_mfderiv_hamiltonianFlowAction_section_eq_zero hF
      hcomm hc hDo hD hs hFs hL le_rfl hh hL'
  -- The sections `s` and `h • s` have the same period lattices, so along `s` the two systems of
  -- periods are related by an integral affine change.
  have hDc : IsPreconnected D := by
    rcases D.eq_empty_or_nonempty with rfl | hne
    · exact isPreconnected_empty
    · exact (hD.isPathConnected (hD.mem hne)).isConnected.isPreconnected
  obtain ⟨P, b, hPb⟩ := hσ.exists_eq_mulVec_add_and_angleMap_eq hF hcomm hc hDo hDc hp hp' hli
    hA hA' hΛ fun c hcD ↦
      (hσ.hamiltonianFlowStabilizer_hamiltonianFlowAction_apply hF hcomm hc (h c) (s c)).symm.trans
        (hΛ' c hcD)
  -- The independent periods `λ⁽ⁱ⁾(c)` span `ι → ℝ`, so `h c = ∑ᵢ wᵢ λ⁽ⁱ⁾(c)`.
  have hw (c : ι → ℝ) : ∃ w : ι → ℝ, c ∈ D → ∑ i, w i • p i c = h c := by
    by_cases hcD : c ∈ D
    · obtain ⟨w, hw⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1
        (((hli c hcD).span_eq_top_of_card_eq_finrank' (by simp)).symm ▸ Submodule.mem_top :
          h c ∈ Submodule.span ℝ (range fun i ↦ p i c))
      exact ⟨w, fun _ ↦ hw⟩
    · exact ⟨0, fun h ↦ absurd h hcD⟩
  choose w hw using hw
  refine ⟨P, b, S, fun c ↦ (2 * π) • w c, hS.of_le (by norm_num), fun c hcD ↦
    ⟨(hPb c hcD).1, (hPb c hcD).2.1, (hSh c hcD).congr_fderiv ?_, fun θ ↦ ?_⟩⟩
  · -- `∑ᵢ 2π wᵢ dAᵢ = ∑ᵢ wᵢ (λ⁽ⁱ⁾ ⬝ dc) = h ⬝ dc`.
    refine ContinuousLinearMap.ext fun v ↦ ?_
    have hv : h c ⬝ᵥ v = ∑ i, w c i * (p i c ⬝ᵥ v) := by
      rw [← hw c hcD, sum_dotProduct]
      simp [smul_dotProduct]
    rw [sum_smul_proj_apply, hv]
    simp only [FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul,
      fun i ↦ fderiv_apply_eq_of_hasFDerivAt_action (hA c hcD i) v]
    exact Finset.sum_congr rfl fun i _ ↦ by field_simp
  · rw [hσ.angleMap_hamiltonianFlowAction_section hF hcomm hc, (hPb c hcD).2.2 θ, ← hw c hcD,
      hσ.hamiltonianFlowAction_apply_angleMap hF hcomm hc]

end IsSymplectic

end SmoothTwoForm

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.AdaptedChart
public import TauCeti.Analysis.Calculus.InverseFunctionTheorem.Family

/-!
# Families of adapted charts

Let `γ : V → W` parametrize a totally real submanifold for a structure `J₀`, as in
`TauCeti.exists_adaptedChart`, and let `J i → J₀` be structures converging in `C^ℓ` along the
submanifold, with `1 ≤ ℓ`. The adapted normal extensions `Φ i = adaptedNormalExtension γ (J i)`
then converge to `Φ₀ = adaptedNormalExtension γ J₀` in `C^ℓ`
(`TauCeti.tendstoContDiffAt_adaptedNormalExtension`). By the inverse function theorem for
converging families, the adapted extensions restrict to adapted charts `e i` (partial
homeomorphisms with underlying map `Φ i`) with one common source, whose targets all contain a
neighbourhood `T` of `γ x₀`; on `T` the inverses `(e i)⁻¹` converge to `e₀⁻¹` in `C^ℓ`
(`TauCeti.exists_adaptedChart_family`). This is the last clause of McDuff–Salamon Exercise
B.4.10 in the model case `M = W`, `L = γ (U)`: for `J_m → J` in `C^ℓ` the adapted charts can be
chosen to converge in `C^ℓ`.

The charts of the family are adapted charts for the structures `J i` in the sense of
`TauCeti.Analysis.Calculus.AdaptedChart`: their underlying maps are the adapted extensions,
which are normal extensions (`TauCeti.adaptedNormalExtension_eq_normalExtension`), so
flattening (`OpenPartialHomeomorph.isImage_of_coe_eq_normalExtension`) applies to each of
them unconditionally. Intertwining
(`OpenPartialHomeomorph.fderiv_symm_apply_of_coe_eq_adaptedNormalExtension`) applies to a chart
`e i` at a point `γ x` with `(x, 0)` in the common source, once `γ` is `C^1` at `x`, `J i` is
continuous at `γ x` with `(J i (γ x))² = -1`, and `(e i)⁻¹` is differentiable at `γ x`; the
theorem assumes the square identity only for `J₀` at `γ x₀`. Convergence is continuous
convergence of the derivatives of order at most `ℓ` (`TauCeti.TendstoContDiffAt`), which on open
sets is locally uniform convergence of these derivatives
(`TauCeti.tendstoContDiffAt_iff_tendstoLocallyUniformlyOn`).

For `ℓ : ℕ∞`, in particular `ℓ = ∞`, the same holds with convergence at every finite order
`k ≤ ℓ`: for `J i → J₀` in `C^k` for every finite `k ≤ ℓ`, the inverse charts converge in `C^k`
for every finite `k ≤ ℓ` (`TauCeti.exists_adaptedChart_family_forall_tendstoContDiffAt`). For
smooth structures converging in `C^∞`, the adapted charts can be chosen to converge in `C^∞`.
The statement for finite `ℓ : ℕ` is its specialization to the order `k = ℓ`.

## Main declarations

* `TauCeti.exists_adaptedChart_family`: adapted charts with a common domain converging in
  `C^ℓ`.
* `TauCeti.exists_adaptedChart_family_forall_tendstoContDiffAt`: the same for `ℓ : ℕ∞`, with
  convergence at every finite order `k ≤ ℓ`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Exercise B.4.10.
-/

public section

open Set Filter Topology
open scoped ContDiff

namespace TauCeti

variable {𝕜 V W : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  [NormedAddCommGroup W] [NormedSpace 𝕜 W] {γ : V → W} {ι : Type*} {l : Filter ι}
  {J : ι → W → W →L[𝕜] W} {J₀ : W → W →L[𝕜] W} {U : Set V} {Ω : Set W} {ℓ : ℕ}

/-- **Adapted charts converging at every finite order.** The version of
`TauCeti.exists_adaptedChart_family` for a regularity `ℓ : ℕ∞`, possibly `∞`. Let `γ` be
`C^(ℓ+1)` on an open `U`, with `1 ≤ ℓ`, mapping `U` into an open `Ω`, and let `J₀` and
eventually all `J i` be `C^ℓ` on `Ω` with `J i → J₀` in `C^k` at every point of `γ (U)`, for
every finite `k ≤ ℓ`. If at `x₀ ∈ U` the tangent map `Dγ x₀` is injective with image maximal
totally real for `J₀ (γ x₀)`, and `J₀ (γ x₀)² = -1`, then the adapted extensions of `J₀` and,
eventually along `l`, of all `J i` restrict to partial homeomorphisms with a common source
containing `(x₀, 0)` inside `U × V`, whose inverses are `C^ℓ` on their targets, and whose
targets contain a common open neighbourhood `T ⊆ Ω` of `γ x₀`. On `T` the inverses `(e i)⁻¹` of
these adapted charts converge to `e₀⁻¹` in `C^k` for every finite `k ≤ ℓ`. -/
theorem exists_adaptedChart_family_forall_tendstoContDiffAt [CompleteSpace V] [CompleteSpace W]
    {m : ℕ∞} (hU : IsOpen U) (hΩ : IsOpen Ω) {x₀ : V} (hx₀ : x₀ ∈ U) (hm : 1 ≤ m)
    (hγ : ContDiffOn 𝕜 ((m : ℕ∞ω) + 1) γ U) (hγΩ : MapsTo γ U Ω)
    (hJ : ∀ᶠ i in l, ContDiffOn 𝕜 m (J i) Ω) (hJ₀ : ContDiffOn 𝕜 m J₀ Ω)
    (hconv : ∀ k : ℕ, (k : ℕ∞) ≤ m → ∀ x ∈ U, TendstoContDiffAt 𝕜 k J J₀ l (γ x))
    (hsq : ∀ v, J₀ (γ x₀) (J₀ (γ x₀) v) = -v) (hinj : Function.Injective (fderiv 𝕜 γ x₀))
    (htr : IsMaximalTotallyReal (J₀ (γ x₀)).toLinearMap (fderiv 𝕜 γ x₀).range) :
    ∃ (e₀ : OpenPartialHomeomorph (V × V) W) (e : ι → OpenPartialHomeomorph (V × V) W)
      (T : Set W), IsOpen T ∧ γ x₀ ∈ T ∧ T ⊆ Ω ∧
      ⇑e₀ = adaptedNormalExtension γ J₀ ∧ (x₀, 0) ∈ e₀.source ∧ e₀.source ⊆ U ×ˢ univ ∧
      T ⊆ e₀.target ∧ ContDiffOn 𝕜 m e₀.symm e₀.target ∧
      (∀ᶠ i in l, ⇑(e i) = adaptedNormalExtension γ (J i) ∧ (e i).source = e₀.source ∧
        T ⊆ (e i).target ∧ ContDiffOn 𝕜 m (e i).symm (e i).target) ∧
      ∀ k : ℕ, (k : ℕ∞) ≤ m → ∀ y ∈ T,
        TendstoContDiffAt 𝕜 k (fun i ↦ ⇑(e i).symm) e₀.symm l y := by
  have hUo : IsOpen (U ×ˢ (univ : Set V)) := hU.prod isOpen_univ
  have hm₁ : ((1 : ℕ∞) : ℕ∞ω) ≤ (m : ℕ∞ω) + 1 := by exact_mod_cast hm.trans le_self_add
  have hγ₁ : ContDiffAt 𝕜 1 γ x₀ := (hγ.contDiffAt (hU.mem_nhds hx₀)).of_le hm₁
  have hJc : ContinuousAt J₀ (γ x₀) := hJ₀.continuousOn.continuousAt (hΩ.mem_nhds (hγΩ hx₀))
  have hinv := (isInvertible_fderiv_adaptedNormalExtension_zero_iff hγ₁ hJc hsq hinj).2 htr
  -- At a finite order `k ≤ m`, the data have the regularity of `exists_adaptedChart_family`.
  have hconvΦ (k : ℕ) (hk : (k : ℕ∞) ≤ m) (p : V × V) (hp : p ∈ U ×ˢ (univ : Set V)) :
      TendstoContDiffAt 𝕜 k (fun i ↦ adaptedNormalExtension γ (J i))
        (adaptedNormalExtension γ J₀) l p := by
    have hk' : ((k : ℕ∞) : ℕ∞ω) ≤ m := by exact_mod_cast hk
    exact tendstoContDiffAt_adaptedNormalExtension hU hΩ
      (hγ.of_le (by exact_mod_cast add_le_add_left hk' 1)) hγΩ
      (hJ.mono fun i hi ↦ hi.of_le hk') (hJ₀.of_le hk') hp.1 (hconv k hk _ hp.1)
  obtain ⟨e₀, e, T, hT, hx₀T, he₀, hx₀s, hs, hT₀, hc₀, hev, hlim⟩ :=
    exists_openPartialHomeomorph_forall_tendstoContDiffAt_symm
      (Φ := fun i ↦ adaptedNormalExtension γ (J i)) hUo ⟨hx₀, mem_univ (0 : V)⟩ hm
      (by filter_upwards [hJ] with i hi using contDiffOn_adaptedNormalExtension hU hγ hi hγΩ)
      (contDiffOn_adaptedNormalExtension hU hγ hJ₀ hγΩ) hconvΦ hinv
  rw [adaptedNormalExtension_zero] at hx₀T
  refine ⟨e₀, e, T ∩ Ω, hT.inter hΩ, ⟨hx₀T, hγΩ hx₀⟩, inter_subset_right, he₀, hx₀s, hs,
    inter_subset_left.trans hT₀, hc₀, ?_, fun k hk y hy ↦ hlim k hk y hy.1⟩
  filter_upwards [hev] with i hi
  exact ⟨hi.1, hi.2.1, inter_subset_left.trans hi.2.2.1, hi.2.2.2⟩

/-- **Adapted charts converging in `C^ℓ`.** Let `γ` be `C^(ℓ+1)` on an open `U`, with `1 ≤ ℓ`,
mapping `U` into an open `Ω`, and let `J₀` and eventually all `J i` be `C^ℓ` on `Ω` with
`J i → J₀` in `C^ℓ` at every point of `γ (U)`. If at `x₀ ∈ U` the tangent map `Dγ x₀` is injective
with image maximal totally real for `J₀ (γ x₀)`, and `J₀ (γ x₀)² = -1`, then the adapted
extensions of `J₀` and, eventually along `l`, of all `J i` restrict to partial homeomorphisms
with a common source containing `(x₀, 0)` inside `U × V`, whose inverses are `C^ℓ` on their
targets, and whose targets contain a common open neighbourhood `T ⊆ Ω` of `γ x₀`. On `T` the
inverses `(e i)⁻¹` of these adapted charts converge to `e₀⁻¹` in `C^ℓ`. -/
theorem exists_adaptedChart_family [CompleteSpace V] [CompleteSpace W] (hU : IsOpen U)
    (hΩ : IsOpen Ω) {x₀ : V} (hx₀ : x₀ ∈ U) (hℓ : 1 ≤ ℓ) (hγ : ContDiffOn 𝕜 (ℓ + 1) γ U)
    (hγΩ : MapsTo γ U Ω)
    (hJ : ∀ᶠ i in l, ContDiffOn 𝕜 ℓ (J i) Ω) (hJ₀ : ContDiffOn 𝕜 ℓ J₀ Ω)
    (hconv : ∀ x ∈ U, TendstoContDiffAt 𝕜 ℓ J J₀ l (γ x))
    (hsq : ∀ v, J₀ (γ x₀) (J₀ (γ x₀) v) = -v) (hinj : Function.Injective (fderiv 𝕜 γ x₀))
    (htr : IsMaximalTotallyReal (J₀ (γ x₀)).toLinearMap (fderiv 𝕜 γ x₀).range) :
    ∃ (e₀ : OpenPartialHomeomorph (V × V) W) (e : ι → OpenPartialHomeomorph (V × V) W)
      (T : Set W), IsOpen T ∧ γ x₀ ∈ T ∧ T ⊆ Ω ∧
      ⇑e₀ = adaptedNormalExtension γ J₀ ∧ (x₀, 0) ∈ e₀.source ∧ e₀.source ⊆ U ×ˢ univ ∧
      T ⊆ e₀.target ∧ ContDiffOn 𝕜 ℓ e₀.symm e₀.target ∧
      (∀ᶠ i in l, ⇑(e i) = adaptedNormalExtension γ (J i) ∧ (e i).source = e₀.source ∧
        T ⊆ (e i).target ∧ ContDiffOn 𝕜 ℓ (e i).symm (e i).target) ∧
      ∀ y ∈ T, TendstoContDiffAt 𝕜 ℓ (fun i ↦ ⇑(e i).symm) e₀.symm l y := by
  obtain ⟨e₀, e, T, hT, hx₀T, hTΩ, he₀, hx₀s, hs, hT₀, hc₀, hev, hlim⟩ :=
    exists_adaptedChart_family_forall_tendstoContDiffAt (m := ℓ) hU hΩ hx₀
      (by exact_mod_cast hℓ) hγ hγΩ hJ hJ₀
      (fun k hk x hx ↦ (hconv x hx).of_le (by exact_mod_cast hk)) hsq hinj htr
  exact ⟨e₀, e, T, hT, hx₀T, hTΩ, he₀, hx₀s, hs, hT₀, hc₀, hev, hlim ℓ le_rfl⟩

end TauCeti

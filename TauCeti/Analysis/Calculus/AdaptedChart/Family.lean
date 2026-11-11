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
`TauCeti.Analysis.Calculus.AdaptedChart`: their underlying maps are the adapted extensions, so
flattening (`OpenPartialHomeomorph.isImage_of_coe_eq_adaptedNormalExtension`) applies to each of
them unconditionally. Intertwining
(`OpenPartialHomeomorph.fderiv_symm_apply_of_coe_eq_adaptedNormalExtension`) applies at a point
`γ x` of the submanifold in the target of a chart once `(J i (γ x))² = -1` there; the theorem
assumes this only for `J₀` at `γ x₀`. Convergence is continuous convergence of the
derivatives of order at most `ℓ` (`TauCeti.TendstoContDiffAt`), which on open sets is locally
uniform convergence of these derivatives
(`TauCeti.tendstoContDiffAt_iff_tendstoLocallyUniformlyOn`).

## Main declarations

* `TauCeti.tendstoContDiffAt_adaptedNormalExtension`: `C^ℓ` convergence of the adapted
  extensions.
* `TauCeti.exists_adaptedChart_family`: adapted charts with a common domain converging in
  `C^ℓ`.

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

/-- **The adapted extensions converge in `C^ℓ`.** Let `γ` be `C^(ℓ+1)` on an open `U`, mapping
it into an open `Ω` on which `J₀` and eventually all `J i` are `C^ℓ`. If `J i → J₀` in `C^ℓ` at
`γ x` for some `x ∈ U`, then the adapted extensions `adaptedNormalExtension γ (J i)` converge in
`C^ℓ` to `adaptedNormalExtension γ J₀` at every point `(x, y)`. -/
theorem tendstoContDiffAt_adaptedNormalExtension (hU : IsOpen U) (hΩ : IsOpen Ω)
    (hγ : ContDiffOn 𝕜 (ℓ + 1) γ U) (hγΩ : MapsTo γ U Ω)
    (hJ : ∀ᶠ i in l, ContDiffOn 𝕜 ℓ (J i) Ω) (hJ₀ : ContDiffOn 𝕜 ℓ J₀ Ω) {p : V × V}
    (hp : p.1 ∈ U) (hconv : TendstoContDiffAt 𝕜 ℓ J J₀ l (γ p.1)) :
    TendstoContDiffAt 𝕜 ℓ (fun i ↦ adaptedNormalExtension γ (J i))
      (adaptedNormalExtension γ J₀) l p := by
  -- Write the extension as a fixed smooth map of `(J (γ q.1), (Dγ q.1 q.2, γ q.1))`.
  let G : (W →L[𝕜] W) × (W × W) → W := fun x ↦ x.2.2 + x.1 x.2.1
  let H : V × V → W × W := fun q ↦ (fderiv 𝕜 γ q.1 q.2, γ q.1)
  have hfun (K : W → W →L[𝕜] W) :
      adaptedNormalExtension γ K = G ∘ fun q : V × V ↦ (K (γ q.1), H q) := by
    funext q
    simp [G, H, adaptedNormalExtension_apply]
  have hG : ContDiff 𝕜 ℓ G := by fun_prop
  have hUo : IsOpen (U ×ˢ (univ : Set V)) := hU.prod isOpen_univ
  have hpU : p ∈ U ×ˢ (univ : Set V) := ⟨hp, mem_univ _⟩
  have hfst : MapsTo (Prod.fst : V × V → V) (U ×ˢ univ) U := fun _ hq ↦ hq.1
  have hγℓ : ContDiffOn 𝕜 ℓ γ U := hγ.of_le le_self_add
  have hγf : ContDiffOn 𝕜 ℓ (fun q : V × V ↦ γ q.1) (U ×ˢ univ) := hγℓ.comp contDiffOn_fst hfst
  have hH : ContDiffOn 𝕜 ℓ H (U ×ˢ univ) :=
    (((hγ.fderiv_of_isOpen hU le_rfl).comp contDiffOn_fst hfst).clm_apply contDiffOn_snd).prodMk
      hγf
  -- Eventual regularity near `p`, uniformly along `l`.
  have hnear : ∀ᶠ q in l ×ˢ 𝓝 p, q.2 ∈ U ×ˢ univ := tendsto_snd.eventually (hUo.mem_nhds hpU)
  have hJq : ∀ᶠ q in l ×ˢ 𝓝 p, ContDiffAt 𝕜 ℓ (J q.1) (γ q.2.1) := by
    filter_upwards [tendsto_fst.eventually hJ, hnear] with q hq hqU
    exact hq.contDiffAt (hΩ.mem_nhds (hγΩ hqU.1))
  have hγq : ∀ᶠ q in l ×ˢ 𝓝 p, ContDiffAt 𝕜 ℓ (fun q : V × V ↦ γ q.1) q.2 := by
    filter_upwards [hnear] with q hqU
    exact hγf.contDiffAt (hUo.mem_nhds hqU)
  have hγp : ContDiffAt 𝕜 ℓ (fun q : V × V ↦ γ q.1) p := hγf.contDiffAt (hUo.mem_nhds hpU)
  have hJp : ContDiffAt 𝕜 ℓ J₀ (γ p.1) := hJ₀.contDiffAt (hΩ.mem_nhds (hγΩ hp))
  have h₁ : TendstoContDiffAt 𝕜 ℓ (fun i ↦ J i ∘ fun q : V × V ↦ γ q.1)
      (J₀ ∘ fun q : V × V ↦ γ q.1) l p :=
    TendstoContDiffAt.comp (f := fun _ q ↦ γ q.1) (f₀ := fun q ↦ γ q.1) (x₀ := p) hconv
      hγp.tendstoContDiffAt_const hJq hγq hJp hγp
  have h₂ := h₁.prodMk (g := fun _ ↦ H) (hH.contDiffAt (hUo.mem_nhds hpU)).tendstoContDiffAt_const
    (by filter_upwards [hJq, hγq] with q h1 h2 using h1.comp q.2 h2)
    (by filter_upwards [hnear] with q hqU using hH.contDiffAt (hUo.mem_nhds hqU))
    (hJp.comp p hγp) (hH.contDiffAt (hUo.mem_nhds hpU))
  have h₃ := hG.contDiffAt.tendstoContDiffAt_const.comp h₂
    (Eventually.of_forall fun _ ↦ hG.contDiffAt) (by
      filter_upwards [hJq, hγq, hnear] with q h1 h2 hqU
      exact (h1.comp q.2 h2).prodMk (hH.contDiffAt (hUo.mem_nhds hqU)))
    hG.contDiffAt ((hJp.comp p hγp).prodMk (hH.contDiffAt (hUo.mem_nhds hpU)))
  simp only [hfun]
  exact h₃

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
  have hUo : IsOpen (U ×ˢ (univ : Set V)) := hU.prod isOpen_univ
  have hγ₁ : ContDiffAt 𝕜 1 γ x₀ :=
    (hγ.contDiffAt (hU.mem_nhds hx₀)).of_le (by exact_mod_cast Nat.le_succ_of_le hℓ)
  have hJc : ContinuousAt J₀ (γ x₀) := hJ₀.continuousOn.continuousAt (hΩ.mem_nhds (hγΩ hx₀))
  have hinv := (isInvertible_fderiv_adaptedNormalExtension_zero_iff hγ₁ hJc hsq hinj).2 htr
  obtain ⟨e₀, e, T, hT, hx₀T, he₀, hx₀s, hs, hT₀, hc₀, hev, hlim⟩ :=
    exists_openPartialHomeomorph_tendstoContDiffAt_symm
      (Φ := fun i ↦ adaptedNormalExtension γ (J i)) hUo ⟨hx₀, mem_univ (0 : V)⟩ hℓ
      (by filter_upwards [hJ] with i hi using contDiffOn_adaptedNormalExtension hU hγ hi hγΩ)
      (contDiffOn_adaptedNormalExtension hU hγ hJ₀ hγΩ)
      (fun p hp ↦ tendstoContDiffAt_adaptedNormalExtension hU hΩ hγ hγΩ hJ hJ₀ hp.1
        (hconv _ hp.1))
      hinv
  rw [adaptedNormalExtension_zero] at hx₀T
  refine ⟨e₀, e, T ∩ Ω, hT.inter hΩ, ⟨hx₀T, hγΩ hx₀⟩, inter_subset_right, he₀, hx₀s, hs,
    inter_subset_left.trans hT₀, hc₀, ?_, fun y hy ↦ hlim y hy.1⟩
  filter_upwards [hev] with i hi
  exact ⟨hi.1, hi.2.1, inter_subset_left.trans hi.2.2.1, hi.2.2.2⟩

end TauCeti

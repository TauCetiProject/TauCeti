/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.DivergenceFormSchauder.BoundaryData
import TauCeti.Analysis.Holder.Superposition
import TauCeti.Analysis.PDE.Quasilinear.GlobalHolder
import TauCeti.Analysis.Sobolev.LipschitzDomain.ContDiff
import TauCeti.Topology.Instances.Matrix
import TauCeti.Topology.MetricSpace.Bounded
import TauCeti.Topology.MetricSpace.Holder

/-!
# Gradient regularity up to the boundary for quasilinear divergence-form equations

Let `Ω ⊆ ℝⁿ⁺¹` be a bounded open set with `C^{1,α}` boundary: near every frontier point, in rigid
coordinates, `Ω` is the region above the graph of a `C¹` function with `α`-Hölder derivative.
Consider the quasilinear Dirichlet problem

`-∂ᵢ(Aⁱʲ(x, u) ∂ⱼu) = f - div G` in `Ω`, `u = g` on `∂Ω`,

whose coefficient matrix depends on the solution, with the boundary values attained in the sense
that `u - g ∈ H¹₀(Ω)`. Suppose that `A(·, s)` is uniformly elliptic with constants `λ, Λ` on
`closure Ω` for every `s`, `α`-Hölder in `x` uniformly in `s` and Lipschitz in `s` uniformly in `x`,
that `G` is `α`-Hölder on `closure Ω`, that `∇g` agrees almost everywhere with a field that is
`α`-Hölder on `closure Ω`, and that `f ∈ L^q(Ω)`, `q ≥ 2`. This file proves that the gradient of a
weak solution is Hölder continuous up to the boundary.

* If the solution itself is `γ`-Hölder on `Ω`, then `∇u` agrees almost everywhere on `Ω` with a
  function that is `β`-Hölder on `closure Ω`, for every `0 < β < 1` with `β ≤ α`, `β ≤ γ` and
  `β ≤ 1 - (n + 1) / q`
  (`TauCeti.PDE.exists_gradient_ae_eq_and_holderOnWith_closure_quasilinear_of_holderOnWith`).
* Every weak solution is Hölder continuous up to the boundary as soon as its boundary values are
  Lipschitz, with an exponent `α₀ > 0` that depends only on `Ω`, `λ`, `Λ` and `q`
  (`Set.IsLipschitzDomain.exists_ae_eq_and_holderOnWith_quasilinear`). So `∇u` agrees almost
  everywhere with a function that is `β`-Hölder on `closure Ω` for every such `β` with `β ≤ α₀`
  (`TauCeti.PDE.exists_gradient_ae_eq_and_holderOnWith_closure_quasilinear`). This applies in
  particular to the weak solutions constructed by Schauder's fixed-point theorem, in
  `Set.IsLipschitzDomain`,
  `exists_sub_mem_w1p0Submodule_forall_energyFormH1_quasilinear_eq_and_holderOnWith`. Like that
  theorem, it is stated for `-div (A(x, u) ∇u) = f + div F` tested against `H¹₀(Ω)`, that is for
  `G = -F`.

This is the first step of the bootstrap from the Hölder continuity of weak solutions to their
regularity up to the boundary: the solution is Hölder, so the frozen coefficient is Hölder, so the
gradient is Hölder.

## The argument

A weak solution `u` solves the linear equation with the frozen coefficient `a(x) = A(x, v(x))`,
where `v` is the Hölder representative of `u`, extended to `closure Ω`. With
`α' = min α γ` (and `α' ≤ 1`), the coefficient `a` is `α'`-Hölder on `closure Ω`
(`HolderOnWith.superposition`), so the global Schauder estimate with boundary
values (`TauCeti.PDE.exists_holderOnWith_gradient_closure_of_sub_mem_w1p0Submodule`) applies at the
exponent `α'`. It needs a domain with `C^{1,α'}` boundary: the boundary graphs, `C¹` with
`α`-Hölder derivative, agree near the chart centres with graphs whose derivative is globally
`α'`-Hölder (`TauCeti.PDE.forall_frontier_exists_graph_holderWith_fderiv_of_le`).

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorems 8.29 and 8.33, and the global regularity of quasilinear equations in Chapter 13.
-/

public section

noncomputable section

open InnerProductSpace MeasureTheory Metric Set TopologicalSpace
open scoped Distributions ENNReal Gradient InnerProductSpace NNReal Topology

namespace TauCeti

namespace PDE

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable {Ω : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
  {A : EuclideanSpace ℝ (Fin (n + 1)) → ℝ → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
  {lam Lam : ℝ} {Kx L KG Kg : ℝ≥0}
  {Dg : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
  {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} {u g : W1p volume Ω 2} {q : ℝ≥0∞}

/-- **Gradient regularity up to the boundary for quasilinear equations with Hölder solutions.**
Let `Ω ⊆ ℝⁿ⁺¹` be a bounded open set with `C^{1,α}` boundary: for every frontier point `x` there
are rigid coordinates `e` with `e x = 0` and a `C¹` function `ψ` with `ψ 0 = 0` and `α`-Hölder
derivative such that, inside a normal cylinder, `Ω` is the region above the graph of `ψ`. Let
`A(x, s)` be uniformly elliptic with constants `λ, Λ` on `closure Ω` for every `s`, `α`-Hölder in
`x ∈ closure Ω` uniformly in `s` and Lipschitz in `s` uniformly in `x ∈ closure Ω`. Let `G` be
`α`-Hölder on `closure Ω`, let `f ∈ L^q(Ω)` with `q ≥ 2`, and let `u, g ∈ H¹(Ω)` with
`u - g ∈ H¹₀(Ω)` and `∇g` almost everywhere equal to a field `Dg` that is `α`-Hölder on
`closure Ω`. If `u` is a weak solution of

`-∂ᵢ(Aⁱʲ(x, u) ∂ⱼu) = f - div G` in `Ω`,

that is `∫_Ω ⟨A(x, u) ∇u, ∇φ⟩ = ∫_Ω ⟨G, ∇φ⟩ + ∫_Ω f φ` for every test function `φ`, and `u` agrees
almost everywhere on `Ω` with a `γ`-Hölder function, then `∇u` agrees almost everywhere on `Ω` with
a function that is `β`-Hölder on `closure Ω`, for every `0 < β < 1` with `β ≤ α`, `β ≤ γ` and
`β ≤ 1 - (n + 1) / q`, where `(n + 1) / ∞ = 0`. -/
theorem exists_gradient_ae_eq_and_holderOnWith_closure_quasilinear_of_holderOnWith
    {α β γ : ℝ≥0} (hβ : 0 < β) (hβ1 : β < 1) (hβα : β ≤ α) (hβγ : β ≤ γ) (hq : 2 ≤ q)
    (hβq : (β : ℝ) ≤ 1 - ((n : ℝ) + 1) / q.toReal)
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    (hchart : ∀ x ∈ frontier (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))),
      ∃ (e : EuclideanSpace ℝ (Fin (n + 1)) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) (ψ : E → ℝ) (h₀ r₀ : ℝ)
        (Kψ : ℝ≥0), e x = 0 ∧ 0 < h₀ ∧ 0 < r₀ ∧ ψ 0 = 0 ∧ ContDiff ℝ 1 ψ ∧
        HolderWith Kψ α (fderiv ℝ ψ) ∧
        ∀ z ∈ normalCylinder h₀ r₀, (e.symm z ∈ Ω ↔ ψ z.snd < z.fst))
    (hA : ∀ s, UniformlyEllipticOn (closure (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))))
      (fun x => A x s) lam Lam)
    (hAx : ∀ s, HolderOnWith Kx α (fun x => matrixBilinearForm (A x s))
      (closure (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))))
    (hAs : ∀ x ∈ closure (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))),
      LipschitzWith L fun s => matrixBilinearForm (A x s))
    {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    (hG : HolderOnWith KG α G (closure (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))))
    (hf : MemLp f q (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))))
    (hug : u - g ∈ w1p0Submodule volume Ω 2)
    (hDg : ⇑(W1p.gradient g) =ᵐ[volume.restrict Ω] Dg)
    (hDgK : HolderOnWith Kg α Dg (closure (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))))
    {v : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} {Kv : ℝ≥0}
    (hv : ⇑(W1p.value u) =ᵐ[volume.restrict Ω] v)
    (hvK : HolderOnWith Kv γ v Ω)
    (hu : ∀ φ : 𝓓(Ω, ℝ), energyFormH1 (fun x => A x (W1p.value u x)) 0 0 u
        (W1p.ofTestFunctionₗ volume Ω 2 φ) =
      (∫ x in Ω, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) +
        ∫ x in Ω, f x * φ x) :
    ∃ (h : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))) (C : ℝ≥0),
      ⇑(W1p.gradient u) =ᵐ[volume.restrict Ω] h ∧
      HolderOnWith C β h (closure (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))) := by
  set s := closure (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))
  -- The common exponent `α' = min α γ`, at most one.
  set α' : ℝ≥0 := min (min α γ) 1
  have hα'α : α' ≤ α := (min_le_left _ _).trans (min_le_left _ _)
  have hα'γ : α' ≤ γ := (min_le_left _ _).trans (min_le_right _ _)
  have hβα' : β ≤ α' := le_min (le_min hβα hβγ) hβ1.le
  -- The Hölder representative of `u`, extended to `closure Ω`.
  obtain ⟨w, hwv, hwK⟩ := hvK.exists_eqOn_holderOnWith_closure (hβ.trans_le hβγ)
  obtain ⟨D, hD⟩ : ∃ D : ℝ≥0, ∀ x ∈ s, ∀ y ∈ s, edist x y ≤ D :=
    ⟨_, fun x hx y hy => Metric.edist_le_diam_of_mem hΩ.closure hx hy⟩
  -- The coefficient frozen at `w` is `α'`-Hölder on `closure Ω`.
  have haK := (hwK.of_le hD hα'γ).superposition (mapsTo_univ _ _)
    (fun s _ => (hAx s).of_le hD hα'α) fun x hx => (hAs x hx).lipschitzOnWith
  obtain ⟨C, -, H⟩ := exists_holderOnWith_gradient_closure_of_sub_mem_w1p0Submodule hβ hβ1 hβα'
    hq hβq hΩ (forall_frontier_exists_graph_holderWith_fderiv_of_le hα'α (min_le_right _ _) hchart)
    lam Lam
    (Kx * D ^ ((α : ℝ) - α') + L * (Kv * D ^ ((γ : ℝ) - α')) : ℝ≥0)
  obtain ⟨Mg, hMg⟩ := (hDgK.isBounded_image hΩ.closure).exists_norm_le
  -- `u` solves the linear equation with the coefficient frozen at `w`.
  have hu' : ∀ φ : 𝓓(Ω, ℝ), energyFormH1 (fun x => A x (w x)) 0 0 u
      (W1p.ofTestFunctionₗ volume Ω 2 φ) =
      (∫ x in Ω, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) +
        ∫ x in Ω, f x * φ x := fun φ => by
    rw [← hu φ]
    refine energyFormH1_congr_ae ?_ .rfl .rfl _ _
    filter_upwards [hv, ae_restrict_mem Ω.isOpen.measurableSet] with x hx hxΩ
    rw [hx, hwv hxΩ]
  obtain ⟨h, hae, hK, -⟩ := H (Mg := Mg.toNNReal) (UniformlyEllipticOn.apply_of_forall hA w) haK
    le_rfl (hG.of_le hD hα'α) hf hug hDg (hDgK.of_le hD hα'α)
    (fun y hy => (hMg _ (mem_image_of_mem _ hy)).trans (Real.le_coe_toNNReal _)) hu'
  exact ⟨h, _, hae, hK⟩

/-- **Gradient regularity up to the boundary for quasilinear equations.** Let `Ω ⊆ ℝⁿ⁺¹` be a
bounded open set with `C^{1,α}` boundary: for every frontier point `x` there are rigid coordinates
`e` with `e x = 0` and a `C¹` function `ψ` with `ψ 0 = 0` and `α`-Hölder derivative such that,
inside a normal cylinder, `Ω` is the region above the graph of `ψ`. Let `q ≥ 2` and `λ, Λ` be
given. There is an exponent `α₀ > 0`, depending on `Ω`, its boundary charts, `α`, `n`, `q`, `λ`
and `Λ`, with the following property.

Let `A(x, s)` be uniformly elliptic with constants `λ, Λ` on `closure Ω` for every `s`,
`α`-Hölder in `x ∈ closure Ω` uniformly in `s` and Lipschitz in `s` uniformly in `x ∈ closure Ω`.
Let `F` be `α`-Hölder on `closure Ω` and `f ∈ L^q(Ω)`. Let `g ∈ H¹(Ω)` have a value `G` that is
bounded and Lipschitz on `Ω` and a gradient almost everywhere equal to a field `Dg` that is
`α`-Hölder on `closure Ω`. If `u ∈ H¹(Ω)` with `u - g ∈ H¹₀(Ω)` is a weak solution of

`-div (A(x, u) ∇u) = f + div F` in `Ω`,

that is `∫_Ω ⟨A(x, u) ∇u, ∇φ⟩ = ∫_Ω f φ - ∫_Ω ⟨F, ∇φ⟩` for every `φ ∈ H¹₀(Ω)`, then `∇u` agrees
almost everywhere on `Ω` with a function that is `β`-Hölder on `closure Ω`, for every `0 < β < 1`
with `β ≤ α`, `β ≤ α₀` and `β ≤ 1 - (n + 1) / q`, where `(n + 1) / ∞ = 0`. -/
theorem exists_gradient_ae_eq_and_holderOnWith_closure_quasilinear {α : ℝ≥0} (hq : 2 ≤ q)
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    (hchart : ∀ x ∈ frontier (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))),
      ∃ (e : EuclideanSpace ℝ (Fin (n + 1)) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) (ψ : E → ℝ) (h₀ r₀ : ℝ)
        (Kψ : ℝ≥0), e x = 0 ∧ 0 < h₀ ∧ 0 < r₀ ∧ ψ 0 = 0 ∧ ContDiff ℝ 1 ψ ∧
        HolderWith Kψ α (fderiv ℝ ψ) ∧
        ∀ z ∈ normalCylinder h₀ r₀, (e.symm z ∈ Ω ↔ ψ z.snd < z.fst))
    (lam Lam : ℝ) :
    ∃ α₀ : ℝ≥0, 0 < α₀ ∧ ∀ {β : ℝ≥0}, 0 < β → β < 1 → β ≤ α → β ≤ α₀ →
      (β : ℝ) ≤ 1 - ((n : ℝ) + 1) / q.toReal →
      ∀ {A : EuclideanSpace ℝ (Fin (n + 1)) → ℝ → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
        {F Dg : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
        {f G : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} {u g : W1p volume Ω 2}
        {Kx L KF Kg K₀ K₁ : ℝ≥0},
        (∀ s, UniformlyEllipticOn (closure (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))))
          (fun x => A x s) lam Lam) →
        (∀ s, HolderOnWith Kx α (fun x => matrixBilinearForm (A x s))
          (closure (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))))) →
        (∀ x ∈ closure (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))),
          LipschitzWith L fun s => matrixBilinearForm (A x s)) →
        HolderOnWith KF α F (closure (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))) →
        MemLp f q (volume.restrict Ω) →
        u - g ∈ w1p0Submodule volume Ω 2 →
        ⇑(W1p.gradient g) =ᵐ[volume.restrict Ω] Dg →
        HolderOnWith Kg α Dg (closure (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))) →
        ⇑(W1p.value g) =ᵐ[volume.restrict Ω] G →
        LipschitzOnWith K₁ G Ω → (∀ x ∈ (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))), |G x| ≤ K₀) →
        (∀ φ : W1p0 volume Ω 2,
          energyFormH1 (fun x => A x (W1p.value u x)) 0 0 u (φ : W1p volume Ω 2) =
            ∫ x in Ω, f x * W1p.value (φ : W1p volume Ω 2) x ∂volume -
              ∫ x in Ω, ⟪F x, W1p.gradient (φ : W1p volume Ω 2) x⟫_ℝ ∂volume) →
        ∃ (h : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))) (C : ℝ≥0),
          ⇑(W1p.gradient u) =ᵐ[volume.restrict Ω] h ∧
          HolderOnWith C β h (closure (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))) := by
  by_cases hqn : (n : ℝ≥0∞) + 1 < q
  swap
  · exact ⟨1, one_pos, fun hβ _ _ _ hβq =>
      absurd (natCast_add_one_lt_of_le_one_sub_div hβ (zero_lt_two.trans_le hq).ne' hβq) hqn⟩
  -- The exponents of the global Hölder estimate: `f ∈ Lʳ` with `n + 1 < r < q`, and the bounded
  -- field `F` in `L^{n + 3}`.
  obtain ⟨r, hnr, hrq⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hqn
  have hnr' : (n : ℝ) + 1 < r := by exact_mod_cast hnr
  have hcard : (Fintype.card (Fin (n + 1)) : ℝ) = n + 1 := by simp
  have : (0 : ℝ) ≤ n := n.cast_nonneg
  have hΩL : (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))).IsLipschitzDomain E :=
    isLipschitzDomain_of_contDiffAt fun x hx => by
      obtain ⟨e, ψ, h₀, r₀, -, hex, hh₀, hr₀, hψ0, hψ, -, hgraph⟩ := hchart x hx
      exact ⟨e, ψ, h₀, r₀, hex, hh₀, hr₀, hψ0, hψ.contDiffAt, hgraph⟩
  obtain ⟨α₀, C₀, hα₀, -, -, hreg⟩ := hΩL.exists_ae_eq_and_holderOnWith_quasilinear (mu := volume)
    hΩ (lam := lam) (Lam := Lam) (r := r) (q := n + 3)
    (by exact_mod_cast (show (1 : ℝ) < r by linarith)) (by rw [hcard]; linarith)
    (by push_cast; linarith) (by rw [hcard]; push_cast; linarith)
  refine ⟨α₀, hα₀, fun {β} hβ hβ1 hβα hβα₀ hβq {A F Dg f G u g Kx L KF Kg K₀ K₁} hA hAx hAs hF hf
    hug hDg hDgK hgG hGL hG0 hu => ?_⟩
  have hα : 0 < α := hβ.trans_le hβα
  have : IsFiniteMeasure (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))) :=
    isFiniteMeasure_restrict.2 hΩ.measure_lt_top.ne
  -- The bounded field `F` lies in every `Lᵖ(Ω)`.
  obtain ⟨MF, hMF⟩ := (hF.isBounded_image hΩ.closure).exists_norm_le
  have hFtop : MemLp F ⊤ (volume.restrict Ω) :=
    memLp_top_of_bound (((hF.continuousOn hα).mono subset_closure).aestronglyMeasurable
      Ω.isOpen.measurableSet) MF (ae_restrict_of_forall_mem Ω.isOpen.measurableSet fun x hx =>
        hMF _ (mem_image_of_mem _ (subset_closure hx)))
  -- The global Hölder estimate: `u` agrees with an `α₀`-Hölder function.
  obtain ⟨v, hv, hvK⟩ := hreg (fun s => (hA s).mono_set subset_closure)
    (fun s => ((continuousOn_of_continuousOn_matrixBilinearForm ((hAx s).continuousOn hα)).mono
      subset_closure).aestronglyMeasurable Ω.isOpen.measurableSet)
    (ae_restrict_of_forall_mem Ω.isOpen.measurableSet fun x hx =>
      continuous_of_continuous_matrixBilinearForm (hAs x (subset_closure hx)).continuous)
    (hf.mono_exponent hrq.le) (hFtop.mono_exponent le_top) hug hu hgG hGL hG0
  exact exists_gradient_ae_eq_and_holderOnWith_closure_quasilinear_of_holderOnWith hβ hβ1 hβα
    hβα₀ hq hβq hΩ hchart hA hAx hAs hF.neg hf hug hDg hDgK hv hvK
    (energyFormH1_ofTestFunctionₗ_eq_of_forall_w1p0 hu)

end PDE

end TauCeti

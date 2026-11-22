/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Quasilinear.Existence
import TauCeti.Analysis.Sobolev.RellichKondrachov
import TauCeti.Topology.Instances.Matrix
import TauCeti.Topology.UniformSpace.LocallyUniformConvergence

/-!
# Stability and compactness of quasilinear solution sets

Let `Ω ⊆ ℝⁿ⁺¹` be a bounded open set and consider the quasilinear Dirichlet problem

`-div (A(x, u) ∇u) = ℓ` in `Ω`, `u - g ∈ H¹₀(Ω)`,

with a Carathéodory coefficient `A`, uniformly elliptic and bounded with constants `λ, Λ`,
boundary values `g ∈ H¹(Ω)` and forcing `ℓ ∈ H⁻¹(Ω)`. A weak solution exists
(`TauCeti.PDE.exists_sub_mem_w1p0Submodule_forall_energyFormH1_quasilinear_eq`), but it need not
be unique, so the solutions are described as a set. This file shows that this set is compact in
`H¹(Ω)` and depends upper semicontinuously on the data. No regularity of `∂Ω` is assumed.

* **Stability**. Let `Aₖ → A` locally uniformly in the second variable for almost every `x ∈ Ω`,
  with common constants `λ, Λ`, let `gₖ → g` in `H¹(Ω)` and `ℓₖ → ℓ` in `H⁻¹(Ω)`. Then
  every sequence of solutions `uₖ` of the problems with data `(Aₖ, gₖ, ℓₖ)` has a subsequence
  converging in `H¹(Ω)` to a solution of the limit problem. This is
  `TauCeti.PDE.exists_sub_mem_w1p0Submodule_forall_energyFormH1_quasilinear_eq_and_tendsto_subseq`
* **Compactness** (`TauCeti.PDE.isCompact_setOf_forall_energyFormH1_quasilinear_eq`). The
  solutions of one problem form a compact subset of `H¹(Ω)`, nonempty by the existence theorem.
* **Upper semicontinuity**
  (`TauCeti.PDE.eventually_setOf_forall_energyFormH1_quasilinear_eq_subset`). Every open subset
  of `H¹(Ω)` containing the solutions of the limit problem contains those of the `k`-th problem
  for all large `k`.

## The argument

By the energy bound
(`PDE.norm_sub_le_of_sub_mem_w1p0Submodule_of_forall_energyFormH1_quasilinear_eq_of_subset_ball`)
the functions
`uₖ - gₖ` are bounded in `H¹₀(Ω)`, so by the Rellich–Kondrachov theorem
(`TauCeti.W1p0.isCompactOperator_valueL`) a subsequence of the values `uₖ` converges in `L²(Ω)`,
to `v` say, and a further subsequence converges almost everywhere. Along it the frozen
coefficients `Aₖ(x, uₖ(x))` converge to `A(x, v(x))` almost everywhere. Each `uₖ` is the solution
of the linear problem with its own frozen coefficient and data, and these linear solutions
converge in `H¹(Ω)` to the solution `u` of the linear problem with coefficient `A(·, v)` and data
`(g, ℓ)` (`TauCeti.PDE.tendsto_frozenSolution`). The values of `u` are then the `L²` limit `v`,
so `u` solves the quasilinear limit problem.

The convergence is in the norm of `H¹(Ω)`, not merely weak: the frozen coefficients converge
almost everywhere and are uniformly bounded, so the gradients converge by dominated convergence.

## References

* M. Chipot, *Elliptic Equations: An Introductory Course*, Birkhäuser, 2009, Section 11.2 (the
  `L²` compactness argument for quasilinear equations).
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 7.22 (the Rellich–Kondrachov theorem).
-/

public section

open Filter MeasureTheory Metric Set TopologicalSpace
open scoped Topology

namespace TauCeti

namespace PDE

attribute [local instance] instSeminormedAddCommGroupW1p instNormedSpaceW1p

variable {n : ℕ} {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
  {A : EuclideanSpace ℝ (Fin (n + 1)) → ℝ → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
  {An : ℕ → EuclideanSpace ℝ (Fin (n + 1)) → ℝ → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
  {lam Lam : ℝ}

/-- The solutions `uₖ` of problems whose boundary values `gₖ` and forcings `ℓₖ` converge have
`uₖ - gₖ` bounded in `H¹(Ω)`, by the energy bound. -/
private theorem bddAbove_range_norm_sub
    (hAn : ∀ k s, UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))
      (fun x => An k x s) lam Lam)
    (hAnm : ∀ k s, AEStronglyMeasurable (fun x => An k x s) (volume.restrict Omega))
    (hAnc : ∀ k, ∀ᵐ x ∂volume.restrict Omega, Continuous (An k x))
    (hΩ : Bornology.IsBounded (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    {g : W1p volume Omega 2} {gn : ℕ → W1p volume Omega 2} (hg : Tendsto gn atTop (𝓝 g))
    {ℓ : StrongDual ℝ (W1p0 volume Omega 2)} {ℓn : ℕ → StrongDual ℝ (W1p0 volume Omega 2)}
    (hℓ : Tendsto ℓn atTop (𝓝 ℓ)) {un : ℕ → W1p volume Omega 2}
    (hun : ∀ k, un k - gn k ∈ w1p0Submodule volume Omega 2 ∧
      ∀ φ : W1p0 volume Omega 2,
        energyFormH1 (fun x => An k x (W1p.value (un k) x)) 0 0 (un k) φ = ℓn k φ) :
    BddAbove (range fun k => ‖un k - gn k‖) := by
  have hR := hΩ.subset_ball (0 : EuclideanSpace ℝ (Fin (n + 1)))
  obtain ⟨R, hball⟩ := hR
  -- The type is given explicitly so that the dual's norm topology is found.
  have hℓn := Tendsto.norm (E := StrongDual ℝ (W1p0 volume Omega 2)) hℓ
  have hK : Tendsto (fun k => 2 * ((2 * R) ^ 2 + 1) * (‖ℓn k‖ + Lam * ‖gn k‖) / lam) atTop
      (𝓝 (2 * ((2 * R) ^ 2 + 1) * (‖ℓ‖ + Lam * ‖g‖) / lam)) :=
    ((hℓn.add (hg.norm.const_mul Lam)).const_mul _).div_const _
  exact hK.bddAbove_range.range_mono _ fun k =>
    norm_sub_le_of_sub_mem_w1p0Submodule_of_forall_energyFormH1_quasilinear_eq_of_subset_ball
      (hAn k) (hAnm k) (hAnc k) hball (hun k).1 (hun k).2

/-- **Stability of the quasilinear Dirichlet problem under perturbation of the data.** Let
`Ω ⊆ ℝⁿ⁺¹` be a bounded open set. Let `Aₖ` be Carathéodory coefficients on `Ω`, uniformly elliptic
and bounded with common constants `λ, Λ`, converging for almost every `x ∈ Ω` locally uniformly in
the second variable to a coefficient `A` with the same bounds. Let the boundary values converge,
`gₖ → g` in `H¹(Ω)`, and the forcings converge, `ℓₖ → ℓ` in `H⁻¹(Ω)`. If each
`uₖ ∈ H¹(Ω)` solves the problem with data `(Aₖ, gₖ, ℓₖ)`,

`-div (Aₖ(x, uₖ) ∇uₖ) = ℓₖ` in `Ω`, `uₖ - gₖ ∈ H¹₀(Ω)`,

then a subsequence of `uₖ` converges in `H¹(Ω)` to a solution `u` of the problem with data
`(A, g, ℓ)`.

The measurability and the continuity of the limit coefficient are not assumed: they are inherited
from the `Aₖ`. The bounds on `A` are assumed on all of `Ω`, since the convergence is only almost
everywhere. -/
theorem exists_sub_mem_w1p0Submodule_forall_energyFormH1_quasilinear_eq_and_tendsto_subseq
    (hA : ∀ s, UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))
      (fun x => A x s) lam Lam)
    (hAn : ∀ k s, UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))
      (fun x => An k x s) lam Lam)
    (hAnm : ∀ k s, AEStronglyMeasurable (fun x => An k x s) (volume.restrict Omega))
    (hAnc : ∀ k, ∀ᵐ x ∂volume.restrict Omega, Continuous (An k x))
    (hAlim : ∀ᵐ x ∂volume.restrict Omega, TendstoLocallyUniformly (fun k => An k x) (A x) atTop)
    (hΩ : Bornology.IsBounded (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    {g : W1p volume Omega 2} {gn : ℕ → W1p volume Omega 2} (hg : Tendsto gn atTop (𝓝 g))
    {ℓ : StrongDual ℝ (W1p0 volume Omega 2)} {ℓn : ℕ → StrongDual ℝ (W1p0 volume Omega 2)}
    (hℓ : Tendsto ℓn atTop (𝓝 ℓ)) {un : ℕ → W1p volume Omega 2}
    (hun : ∀ k, un k - gn k ∈ w1p0Submodule volume Omega 2 ∧
      ∀ φ : W1p0 volume Omega 2,
        energyFormH1 (fun x => An k x (W1p.value (un k) x)) 0 0 (un k) φ = ℓn k φ) :
    ∃ u : W1p volume Omega 2,
      (u - g ∈ w1p0Submodule volume Omega 2 ∧
        ∀ φ : W1p0 volume Omega 2,
          energyFormH1 (fun x => A x (W1p.value u x)) 0 0 u φ = ℓ φ) ∧
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ Tendsto (fun j => un (ψ j)) atTop (𝓝 u) := by
  -- The limit coefficient inherits continuity and measurability from the `Aₖ`; the functions in
  -- `aestronglyMeasurable_of_tendsto_ae` are given explicitly, as unification does not find them.
  have hAc : ∀ᵐ x ∂volume.restrict Omega, Continuous (A x) := by
    filter_upwards [hAlim, ae_all_iff.2 hAnc] with x hx hcx
    exact hx.continuous (Frequently.of_forall hcx)
  have hAm (s : ℝ) : AEStronglyMeasurable (fun x => A x s) (volume.restrict Omega) :=
    aestronglyMeasurable_of_tendsto_ae (f := fun k x => An k x s) (g := fun x => A x s) atTop
      (fun k => hAnm k s) (hAlim.mono fun _ hx => hx.tendstoLocallyUniformlyOn.tendsto_at
        (mem_univ s))
  -- By the energy bound and Rellich, a subsequence of the values converges in `L²(Ω)` and almost
  -- everywhere.
  have hsub := W1p.exists_tendsto_value_subseq_of_sub_mem_w1p0Submodule ENNReal.ofNat_ne_top hΩ hg
    (fun k => (hun k).1)
    (bddAbove_range_norm_sub hAn hAnm hAnc hΩ hg hℓ hun)
  obtain ⟨v, ψ, hψ, hv, hae⟩ := hsub
  -- Along the subsequence the frozen coefficients converge almost everywhere.
  have hlim : ∀ᵐ x ∂volume.restrict Omega, Tendsto (fun j => An (ψ j) x (W1p.value (un (ψ j)) x))
      atTop (𝓝 (A x (v x))) := by
    filter_upwards [hAlim, hAc, hae] with x hx hcx hvx
    exact (hx.comp_tendsto hψ.tendsto_atTop).tendsto_comp hcx.continuousAt hvx
  -- Each `uₖ` is the frozen solution with its own coefficient and data, and these converge in
  -- `H¹(Ω)` to the frozen solution `u` with coefficient `A(·, v)` and the limit data.
  have hfrozen (j : ℕ) : un (ψ j) = frozenSolution (An (ψ j)) (gn (ψ j)) (ℓn (ψ j))
      (W1p.value (un (ψ j))) :=
    eq_frozenSolution_of_sub_mem_w1p0Submodule_of_forall_energyFormH1_eq (hAn (ψ j))
      (hAnm (ψ j)) (hAnc (ψ j)) hΩ (Lp.aestronglyMeasurable _) (hun (ψ j)).1 (hun (ψ j)).2
  have hu : Tendsto (fun j => un (ψ j)) atTop (𝓝 (frozenSolution A g ℓ v)) := by
    refine (tendsto_frozenSolution hA hAm hAc (fun j => hAn (ψ j)) (fun j => hAnm (ψ j))
      (fun j => hAnc (ψ j)) hΩ (Lp.aestronglyMeasurable v) (fun _ => Lp.aestronglyMeasurable _)
      hlim (hg.comp hψ.tendsto_atTop) (hℓ.comp hψ.tendsto_atTop)).congr fun j => (hfrozen j).symm
  -- The values of `u` are the `L²` limit `v`, so `u` solves the quasilinear limit problem.
  have hval : W1p.value (frozenSolution A g ℓ v) = v := by
    refine tendsto_nhds_unique ?_ hv
    simpa only [Function.comp_def, W1p.valueL_apply] using
      (W1p.valueL.continuous.tendsto _).comp hu
  have hU₁ := frozenSolution_sub_mem_w1p0Submodule hA hAm hAc hΩ g ℓ (Lp.aestronglyMeasurable v)
  have hU₂ := forall_energyFormH1_frozenSolution_eq hA hAm hAc hΩ g ℓ (Lp.aestronglyMeasurable v)
  have hcoef : (fun x => A x (W1p.value (frozenSolution A g ℓ v) x)) = fun x => A x (v x) := by
    rw [hval]
  exact ⟨frozenSolution A g ℓ v, ⟨hU₁, fun φ => (congrArg
    (fun a => energyFormH1 a 0 0 (frozenSolution A g ℓ v) (φ : W1p volume Omega 2)) hcoef).trans
      (hU₂ φ)⟩, ψ, hψ, hu⟩

/-- **The solution set of the quasilinear Dirichlet problem is compact.** Under the hypotheses of
the existence theorem `TauCeti.PDE.exists_sub_mem_w1p0Submodule_forall_energyFormH1_quasilinear_eq`,
the weak solutions `u ∈ H¹(Ω)` of

`-div (A(x, u) ∇u) = ℓ` in `Ω`, `u - g ∈ H¹₀(Ω)`

form a compact subset of `H¹(Ω)`. It is nonempty by that theorem. -/
theorem isCompact_setOf_forall_energyFormH1_quasilinear_eq
    (hA : ∀ s, UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))
      (fun x => A x s) lam Lam)
    (hAm : ∀ s, AEStronglyMeasurable (fun x => A x s) (volume.restrict Omega))
    (hAc : ∀ᵐ x ∂volume.restrict Omega, Continuous (A x))
    (hΩ : Bornology.IsBounded (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    (g : W1p volume Omega 2) (ℓ : StrongDual ℝ (W1p0 volume Omega 2)) :
    IsCompact {u : W1p volume Omega 2 | u - g ∈ w1p0Submodule volume Omega 2 ∧
      ∀ φ : W1p0 volume Omega 2, energyFormH1 (fun x => A x (W1p.value u x)) 0 0 u φ = ℓ φ} := by
  refine IsSeqCompact.isCompact fun un hun => ?_
  -- The constant family of problems converges to the problem itself.
  have hsub := exists_sub_mem_w1p0Submodule_forall_energyFormH1_quasilinear_eq_and_tendsto_subseq
    (An := fun _ => A) (gn := fun _ => g) (ℓn := fun _ => ℓ) hA (fun _ => hA) (fun _ => hAm)
    (fun _ => hAc)
    (ae_of_all _ fun x => tendstoLocallyUniformly_const (A x)) hΩ tendsto_const_nhds
    tendsto_const_nhds hun
  obtain ⟨u, hu, ψ, hψ, hlim⟩ := hsub
  exact ⟨u, hu, ψ, hψ, hlim⟩

/-- **Upper semicontinuity of the solution set.** Under the hypotheses of
`TauCeti.PDE.exists_sub_mem_w1p0Submodule_forall_energyFormH1_quasilinear_eq_and_tendsto_subseq`,
let `U` be an open subset of `H¹(Ω)` containing every solution of the limit problem with data
`(A, g, ℓ)`. Then for all large `k`, `U` contains every solution of the problem with data
`(Aₖ, gₖ, ℓₖ)`. -/
theorem eventually_setOf_forall_energyFormH1_quasilinear_eq_subset
    (hA : ∀ s, UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))
      (fun x => A x s) lam Lam)
    (hAn : ∀ k s, UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))
      (fun x => An k x s) lam Lam)
    (hAnm : ∀ k s, AEStronglyMeasurable (fun x => An k x s) (volume.restrict Omega))
    (hAnc : ∀ k, ∀ᵐ x ∂volume.restrict Omega, Continuous (An k x))
    (hAlim : ∀ᵐ x ∂volume.restrict Omega, TendstoLocallyUniformly (fun k => An k x) (A x) atTop)
    (hΩ : Bornology.IsBounded (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    {g : W1p volume Omega 2} {gn : ℕ → W1p volume Omega 2} (hg : Tendsto gn atTop (𝓝 g))
    {ℓ : StrongDual ℝ (W1p0 volume Omega 2)} {ℓn : ℕ → StrongDual ℝ (W1p0 volume Omega 2)}
    (hℓ : Tendsto ℓn atTop (𝓝 ℓ)) {U : Set (W1p volume Omega 2)}
    (hU : IsOpen U)
    (hSU : {u : W1p volume Omega 2 | u - g ∈ w1p0Submodule volume Omega 2 ∧
      ∀ φ : W1p0 volume Omega 2,
        energyFormH1 (fun x => A x (W1p.value u x)) 0 0 u φ = ℓ φ} ⊆ U) :
    ∀ᶠ k in atTop, {u : W1p volume Omega 2 | u - gn k ∈ w1p0Submodule volume Omega 2 ∧
      ∀ φ : W1p0 volume Omega 2,
        energyFormH1 (fun x => An k x (W1p.value u x)) 0 0 u φ = ℓn k φ} ⊆ U := by
  by_contra h
  -- Otherwise a subsequence of problems has solutions `uⱼ ∉ U`.
  have hfreq := extraction_of_frequently_atTop (not_eventually.1 h)
  obtain ⟨ψ, hψ, hψU⟩ := hfreq
  choose un hun hunU using fun j => not_subset.1 (hψU j)
  have hψt := hψ.tendsto_atTop
  have hsub := exists_sub_mem_w1p0Submodule_forall_energyFormH1_quasilinear_eq_and_tendsto_subseq
    (An := fun j => An (ψ j)) (gn := fun j => gn (ψ j)) (ℓn := fun j => ℓn (ψ j)) hA
    (fun j => hAn (ψ j)) (fun j => hAnm (ψ j)) (fun j => hAnc (ψ j))
    (hAlim.mono fun _ hx => hx.comp_tendsto hψt) hΩ (hg.comp hψt) (hℓ.comp hψt) hun
  obtain ⟨u, hu, ψ', -, hlim⟩ := hsub
  -- The limit is a solution of the limit problem, so lies in the open set `U`, and so do the
  -- `uⱼ` for large `j`.
  have hev := (hlim.eventually (hU.mem_nhds (hSU hu))).exists
  obtain ⟨j, hj⟩ := hev
  exact hunU _ hj

end PDE

end TauCeti

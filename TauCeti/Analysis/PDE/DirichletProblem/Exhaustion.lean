/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.DirichletProblem
public import TauCeti.Analysis.Sobolev.W1p.Extension
import TauCeti.Analysis.PDE.EnergyForm.Restriction

/-!
# The Dirichlet problem along an exhaustion of the domain

Let `L u = -∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u` be a divergence-form operator whose energy form `B` is
bounded and coercive on `H¹₀(Ω)`, with `C ‖w‖² ≤ B(w, w)`, and let `ℓ ∈ H⁻¹(Ω)`. The same
coercivity constant works on every open `U ⊆ Ω`, because zero extension `H¹₀(U) → H¹₀(Ω)` is an
isometry that preserves the energy, so the Dirichlet problem `L w = ℓ` on `U`, tested against
`H¹₀(U)` through zero extension, also has a unique weak solution. This file compares it with the
solution `u` on `Ω`.

The zero extension of `w` is the Galerkin approximation of `u` in the closed subspace of `H¹₀(Ω)`
formed by the zero extensions of `H¹₀(U)`: `B(u - w, v) = ℓ(v) - ℓ(v) = 0` for every such `v`.
Céa's lemma (`LinearMap.norm_sub_le_div_mul_norm_sub`) therefore gives

`‖u - w‖ ≤ ‖B‖ / C * ‖u - v‖` for every `v ∈ H¹₀(U)`,

with `‖B‖` the norm of `B` on `H¹(Ω)` and `v`, `w` identified with their zero extensions
(`TauCeti.PDE.norm_sub_extendByZeroL_le_of_forall_energyFormH1_eq`). Along an increasing family of
open sets `U k` covering `Ω`, the zero extensions of the spaces `H¹₀(U k)` are dense in `H¹₀(Ω)`
(`TauCeti.W1p0.dense_iUnion_range_extendByZeroL`), so the solutions on `U k` converge to `u` in
`H¹₀(Ω)` (`TauCeti.PDE.tendsto_extendByZeroL_of_forall_energyFormH1_eq`). No boundedness or
regularity of `Ω` or of the `U k` is used beyond the coercivity of `B` on `H¹₀(Ω)`.

For an `L²` datum `f` the problems on `U k` have the datum `f` restricted to `U k`
(`TauCeti.PDE.tendsto_extendByZeroL_of_isWeakSolutionDirichlet`). For instance, for
`L = -Δ + λ` with `λ > 0` on `Ω = ℝⁿ`, whose energy form is coercive on `H¹(ℝⁿ)`
(`TauCeti.PDE.UniformlyEllipticOn.isCoercive_energyFormH1L0_of_mass_lower_bound`), and an
exhaustion of `ℝⁿ` by balls, the weak solutions of `(λ - Δ) w = f` on the balls with zero
boundary values, extended by zero, converge in `H¹(ℝⁿ)` to the weak solution of `(λ - Δ) u = f`
on `ℝⁿ`. This is the stationary half of the comparison between the heat flows of bounded domains
with the Dirichlet condition and the heat flow of `ℝⁿ`, as the domains exhaust `ℝⁿ`.

## Main declarations

* `TauCeti.PDE.dirichletForcing_extendByZeroL`: the `L²` forcing functional tested against a zero
  extension is the integral over the smaller set.
* `TauCeti.PDE.norm_sub_extendByZeroL_le_of_forall_energyFormH1_eq`: Céa's estimate comparing the
  solutions on `U ⊆ Ω` and on `Ω`.
* `TauCeti.PDE.tendsto_extendByZeroL_of_forall_energyFormH1_eq`: convergence of the solutions
  along an exhaustion, for data in `H⁻¹(Ω)`.
* `TauCeti.PDE.tendsto_extendByZeroL_of_isWeakSolutionDirichlet`: the same for data in `L²(Ω)`.

## References

* J. Céa, *Approximation variationnelle des problèmes aux limites*, Ann. Inst. Fourier 14 (1964),
  345–444.
* L. C. Evans, *Partial Differential Equations*, 2nd ed., Section 6.2.
-/

public section

namespace TauCeti

namespace PDE

open Filter MeasureTheory Set TopologicalSpace Topology

variable {ι : Type*} [Fintype ι] {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
  {Omega U : Opens (EuclideanSpace ℝ ι)}
  {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
  {c : EuclideanSpace ℝ ι → ℝ} {C : ℝ}

attribute [local instance] W1p0.instNormedAddCommGroup W1p0.instInnerProductSpace
-- The shortcut instances of the energy-form file, so that the operator norm of the bundled
-- energy form `TauCeti.PDE.energyFormH1L` is found by instance search.
attribute [local instance] instSeminormedAddCommGroupW1p instNormedSpaceW1p

/-- **The `L²` forcing functional on a zero extension.** For open sets `U ⊆ Ω`, `f ∈ L²(Ω)` and
`v ∈ H¹₀(U)`, testing `f` against the zero extension of `v` to `Ω` is integrating `f v` over `U`. -/
theorem dirichletForcing_extendByZeroL (hU : U ≤ Omega) (f : Lp ℝ 2 (mu.restrict Omega))
    (v : W1p0 mu U 2) :
    dirichletForcing f (W1p0.extendByZeroL hU v) =
      ∫ x in U, f x * W1p.value (v : W1p mu U 2) x ∂mu := by
  rw [dirichletForcing_apply_eq_setIntegral, W1p0.value_extendByZeroL]
  exact setIntegral_extendByZeroLpₗᵢ ℝ _ _ (fun x y => f x * y) (fun _ => mul_zero _) _

/-- **Céa's estimate for the Dirichlet problem on a smaller domain.** Let the energy form `B` of
`(a, b, c)` satisfy `C ‖w‖² ≤ B(w, w)` on `H¹₀(Ω)` with `C > 0`, let `u ∈ H¹₀(Ω)` solve
`B(u, v) = ℓ(v)` for every `v ∈ H¹₀(Ω)`, and for an open `U ⊆ Ω` let `w ∈ H¹₀(U)` solve
`B(w, v) = ℓ(v)` for every `v ∈ H¹₀(U)`, both `v` and `w` extended by zero to `Ω`. Then, for
every `v ∈ H¹₀(U)`,

`‖u - w‖ ≤ ‖B‖ / C * ‖u - v‖`,

where `‖B‖` is the norm of the energy form as a bounded bilinear form on `H¹(Ω)`. So the solution
on `U` approximates `u` as well as `H¹₀(U)` does, up to the factor `‖B‖ / C`. -/
theorem norm_sub_extendByZeroL_le_of_forall_energyFormH1_eq
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hC : 0 < C)
    (hlower : ∀ w : W1p0 mu Omega 2,
      C * ‖w‖ ^ 2 ≤ energyFormH1 a b c (w : W1p mu Omega 2) (w : W1p mu Omega 2))
    {ℓ : StrongDual ℝ (W1p0 mu Omega 2)} {u : W1p0 mu Omega 2}
    (hu : ∀ v : W1p0 mu Omega 2, energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) =
      ℓ v)
    (hU : U ≤ Omega) {w : W1p0 mu U 2}
    (hw : ∀ v : W1p0 mu U 2, energyFormH1 a b c (w : W1p mu U 2) (v : W1p mu U 2) =
      ℓ (W1p0.extendByZeroL hU v))
    (v : W1p0 mu U 2) :
    ‖u - W1p0.extendByZeroL hU w‖ ≤
      ‖energyFormH1L hcoeff‖ / C * ‖u - W1p0.extendByZeroL hU v‖ := by
  refine (energyFormH1L0 hcoeff).toLinearMap₁₂.norm_sub_le_div_mul_norm_sub hC
    (fun x ↦ by
      rw [ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply, energyFormH1L0_apply, mul_assoc,
        ← sq]
      exact hlower x)
    (fun x y ↦ by
      rw [ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply, energyFormH1L0_apply,
        ← energyFormH1L_apply hcoeff, ← Submodule.norm_coe x, ← Submodule.norm_coe y]
      exact (le_abs_self _).trans ((Real.norm_eq_abs _).symm.trans_le
        ((energyFormH1L hcoeff).le_opNorm₂ _ _)))
    (S := LinearMap.range (W1p0.extendByZeroL (mu := mu) (p := 2) hU).toLinearMap)
    ⟨w, rfl⟩ ⟨v, rfl⟩ ?_
  rintro _ ⟨y, rfl⟩
  simp only [ContinuousLinearMap.coe_coe, map_sub, LinearMap.sub_apply,
    ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply, energyFormH1L0_apply, hu,
    energyFormH1_extendByZeroL, hw, sub_self]

/-- **The Dirichlet problem along an exhaustion.** Let the energy form `B` of `(a, b, c)` be
coercive on `H¹₀(Ω)` and let `u ∈ H¹₀(Ω)` solve `B(u, v) = ℓ(v)` for every `v ∈ H¹₀(Ω)`. Let
`U k ⊆ Ω` be a monotone family of open sets, indexed by a directed order, that covers `Ω`, and
let `w k ∈ H¹₀(U k)` solve `B(w k, v) = ℓ(v)` for every `v ∈ H¹₀(U k)`, extended by zero to `Ω`.
Then the zero extensions of the `w k` converge to `u` in `H¹₀(Ω)`.

The solutions `w k` exist and are unique by Lax–Milgram, since coercivity passes to smaller
domains (`TauCeti.PDE.isCoercive_energyFormH1L0_of_domain_le`). -/
theorem tendsto_extendByZeroL_of_forall_energyFormH1_eq {κ : Type*} [Preorder κ]
    [IsDirectedOrder κ] [Nonempty κ]
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hcoercive : IsCoercive (energyFormH1L0 hcoeff))
    {ℓ : StrongDual ℝ (W1p0 mu Omega 2)} {u : W1p0 mu Omega 2}
    (hu : ∀ v : W1p0 mu Omega 2, energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) =
      ℓ v)
    {U : κ → Opens (EuclideanSpace ℝ ι)} (hmono : Monotone U) (hU : ∀ k, U k ≤ Omega)
    (hcover : (Omega : Set (EuclideanSpace ℝ ι)) ⊆ ⋃ k, (U k : Set (EuclideanSpace ℝ ι)))
    {w : ∀ k, W1p0 mu (U k) 2}
    (hw : ∀ k, ∀ v : W1p0 mu (U k) 2,
      energyFormH1 a b c (w k : W1p mu (U k) 2) (v : W1p mu (U k) 2) =
        ℓ (W1p0.extendByZeroL (hU k) v)) :
    Tendsto (fun k ↦ W1p0.extendByZeroL (hU k) (w k)) atTop (𝓝 u) := by
  obtain ⟨C, hC, hle⟩ := hcoercive
  have hlower : ∀ x : W1p0 mu Omega 2,
      C * ‖x‖ ^ 2 ≤ energyFormH1 a b c (x : W1p mu Omega 2) (x : W1p mu Omega 2) := fun x ↦ by
    rw [sq, ← mul_assoc, ← energyFormH1L0_apply hcoeff]; exact hle x
  have hK : 0 ≤ ‖energyFormH1L hcoeff‖ / C := by positivity
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine Metric.tendsto_nhds.2 fun ε hε ↦ ?_
  have harith : ∀ K : ℝ, 0 ≤ K → K * (ε / (K + 1)) < ε := fun K hK ↦ by
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith
  -- Approximate `u` by a zero extension from one `U k₀`; it stays one from every larger `U k`.
  obtain ⟨y, hy, hdist⟩ := (W1p0.dense_iUnion_range_extendByZeroL hmono.directed_le hU
    hcover).exists_dist_lt u
      (div_pos hε (by positivity : (0 : ℝ) < ‖energyFormH1L hcoeff‖ / C + 1))
  obtain ⟨k₀, v, rfl⟩ := mem_iUnion.1 hy
  filter_upwards [eventually_ge_atTop k₀] with k hk
  have hv : W1p0.extendByZeroL (hU k) (W1p0.extendByZeroL (hmono hk) v) =
      W1p0.extendByZeroL (hU k₀) v := W1p0.extendByZeroL_extendByZeroL _ _ v
  have hcea := norm_sub_extendByZeroL_le_of_forall_energyFormH1_eq hcoeff hC hlower hu (hU k)
    (hw k) (W1p0.extendByZeroL (hmono hk) v)
  rw [hv] at hcea
  rw [dist_eq_norm] at hdist
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _), norm_sub_rev]
  calc ‖u - W1p0.extendByZeroL (hU k) (w k)‖
      ≤ ‖energyFormH1L hcoeff‖ / C * ‖u - W1p0.extendByZeroL (hU k₀) v‖ := hcea
    _ ≤ ‖energyFormH1L hcoeff‖ / C * (ε / (‖energyFormH1L hcoeff‖ / C + 1)) :=
        mul_le_mul_of_nonneg_left hdist.le hK
    _ < ε := harith _ hK

/-- **The Dirichlet problem with an `L²` datum along an exhaustion.** Let the energy form of
`(a, b, c)` be coercive on `H¹₀(Ω)`, let `f ∈ L²(Ω)` and let `u ∈ H¹₀(Ω)` be the weak solution of
`L u = f` in `Ω`, `u = 0` on `∂Ω`. Let `U k ⊆ Ω` be a monotone family of open sets, indexed by a
directed order, that covers `Ω`, and let `w k ∈ H¹₀(U k)` be the weak solution of `L w = f` in
`U k`, `w = 0` on `∂(U k)`: `B(w k, v) = ∫_{U k} f v` for every `v ∈ H¹₀(U k)`. Then the zero
extensions of the `w k` converge to `u` in `H¹₀(Ω)`. -/
theorem tendsto_extendByZeroL_of_isWeakSolutionDirichlet {κ : Type*} [Preorder κ]
    [IsDirectedOrder κ] [Nonempty κ]
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hcoercive : IsCoercive (energyFormH1L0 hcoeff)) {f : Lp ℝ 2 (mu.restrict Omega)}
    {u : W1p0 mu Omega 2} (hu : IsWeakSolutionDirichlet a b c f u)
    {U : κ → Opens (EuclideanSpace ℝ ι)} (hmono : Monotone U) (hU : ∀ k, U k ≤ Omega)
    (hcover : (Omega : Set (EuclideanSpace ℝ ι)) ⊆ ⋃ k, (U k : Set (EuclideanSpace ℝ ι)))
    {w : ∀ k, W1p0 mu (U k) 2}
    (hw : ∀ k, ∀ v : W1p0 mu (U k) 2,
      energyFormH1 a b c (w k : W1p mu (U k) 2) (v : W1p mu (U k) 2) =
        ∫ x in U k, f x * W1p.value (v : W1p mu (U k) 2) x ∂mu) :
    Tendsto (fun k ↦ W1p0.extendByZeroL (hU k) (w k)) atTop (𝓝 u) :=
  tendsto_extendByZeroL_of_forall_energyFormH1_eq hcoeff hcoercive
    hu.energyFormH1_eq_dirichletForcing hmono hU hcover fun k v ↦
      (hw k v).trans (dirichletForcing_extendByZeroL (hU k) f v).symm

end PDE

end TauCeti

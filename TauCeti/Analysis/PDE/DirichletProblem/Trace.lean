/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.DirichletProblem
public import TauCeti.Analysis.Sobolev.LipschitzDomain.Trace.Frontier

/-!
# The Dirichlet problem with boundary values as traces

On an arbitrary open set `Ω ⊆ ℝⁿ` the weak Dirichlet problem `L u = ℓ` in `Ω`, `u = g` on `∂Ω`,
for `L u = -∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u`, `g ∈ H¹(Ω)` and `ℓ ∈ H⁻¹(Ω) = (H¹₀(Ω))*`, asks for
`u ∈ H¹(Ω)` with

`u - g ∈ H¹₀(Ω)` and `a(u, v) = ℓ v` for every `v ∈ H¹₀(Ω)`,

and it has exactly one solution when the energy form is coercive on `H¹₀(Ω)`
(`TauCeti.PDE.existsUnique_sub_mem_w1p0Submodule_forall_energyFormH1_eq`). The boundary condition
is membership of `u - g` in the closure of the test functions, which needs no regularity of `∂Ω`.

On a bounded Lipschitz domain it is the boundary condition in its classical sense. The trace
`W^{1,2}(Ω) → L²(∂Ω)` for surface measure on the frontier has kernel exactly `H¹₀(Ω)`
(`TauCeti.W1p.ker_frontierTrace`), so `u - g ∈ H¹₀(Ω)` says that `u` and `g` have the same
boundary trace. Lipschitz domains are set in the product `ℝ × E` of their boundary charts, while
the energy form lives on `EuclideanSpace ℝ ι`; the two are matched by an affine isometry `e`
carrying `Ω` onto the Lipschitz domain `V`, and the boundary values of `u ∈ H¹(Ω)` are the trace
of `u ∘ e⁻¹` on `frontier V`. This file states the Dirichlet problem with this trace condition.

## Main declarations

* `TauCeti.PDE.existsUnique_frontierTrace_eq_forall_energyFormH1_eq`: for a coercive energy form
  on a bounded Lipschitz domain, there is exactly one `u ∈ H¹(Ω)` with the same trace as `g` and
  `a(u, v) = ℓ v` for every `v ∈ H¹₀(Ω)`.
* `TauCeti.PDE.UniformlyEllipticOn.existsUnique_frontierTrace_eq_forall_energyFormH1_eq`: the
  same for `-∂ᵢ(aⁱʲ ∂ⱼu) + c u` with uniformly elliptic measurable `a` and bounded measurable
  `c ≥ 0`, where coercivity follows from the Poincaré inequality of the bounded domain.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.5, Theorem 2 (the kernel of the
  trace) and §6.2.2, Theorem 3 with the lifting of §6.2.1 (the Dirichlet problem with boundary
  data).
* D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 8.3.
-/

public section

noncomputable section

namespace TauCeti

namespace PDE

open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {V : Opens (WithLp 2 (ℝ × E))} {L : ℝ≥0}

section Domain

variable {ι : Type*} [Fintype ι] {Omega : Opens (EuclideanSpace ℝ ι)}
  {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
  {c : EuclideanSpace ℝ ι → ℝ}

/-- **The Dirichlet problem with trace boundary values.** Let an affine isometry `e` carry
`Ω ⊆ EuclideanSpace ℝ ι` onto a bounded Lipschitz domain `V`, and let the energy form be bounded
and coercive on `H¹₀(Ω)`. For every `g ∈ H¹(Ω)` and every `ℓ ∈ H⁻¹(Ω)` there is exactly one
`u ∈ H¹(Ω)` such that `u ∘ e⁻¹` and `g ∘ e⁻¹` have the same trace on `frontier V` and

`a(u, v) = ℓ v` for every `v ∈ H¹₀(Ω)`.

This is the weak form of `L u = ℓ` in `Ω`, `u = g` on `∂Ω`, with the boundary condition read
through the trace operator `TauCeti.W1p.frontierTrace`. -/
theorem existsUnique_frontierTrace_eq_forall_energyFormH1_eq
    (hV : (V : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : Bornology.IsBounded (V : Set (WithLp 2 (ℝ × E))))
    (e : EuclideanSpace ℝ ι ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E))
    (hVΩ : (V : Set (WithLp 2 (ℝ × E))) = e.symm ⁻¹' Omega)
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (volume.restrict Omega))
    (hcoercive : IsCoercive (energyFormH1L0 hcoeff)) (g : W1p volume Omega 2)
    (ℓ : StrongDual ℝ (W1p0 volume Omega 2)) :
    ∃! u : W1p volume Omega 2,
      W1p.frontierTrace ENNReal.ofNat_ne_top hV hb (W1p.compAffineIsometryEquivL e.symm hVΩ u) =
          W1p.frontierTrace ENNReal.ofNat_ne_top hV hb
            (W1p.compAffineIsometryEquivL e.symm hVΩ g) ∧
        ∀ v : W1p0 volume Omega 2, energyFormH1 a b c u (v : W1p volume Omega 2) = ℓ v := by
  simpa only [W1p.sub_mem_w1p0Submodule_iff_frontierTrace_compAffineIsometryEquivL_eq (p := 2)
    ENNReal.ofNat_ne_top hV hb e hVΩ] using
    existsUnique_sub_mem_w1p0Submodule_forall_energyFormH1_eq hcoeff hcoercive g ℓ

end Domain

section Euclidean

variable {n : ℕ} {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
  {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
  {c : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} {lam Lam gamma : ℝ}

namespace UniformlyEllipticOn

/-- **The Dirichlet problem on a bounded Lipschitz domain.** Let an affine isometry `e` carry
`Ω ⊆ ℝ^{n+1}` onto a bounded Lipschitz domain `V`, let `a` be measurable and uniformly elliptic
on `Ω`, and let `c` be measurable with `0 ≤ c ≤ γ` on `Ω`. For every `g ∈ H¹(Ω)` and every
`ℓ ∈ H⁻¹(Ω)` there is exactly one `u ∈ H¹(Ω)` solving `-∂ᵢ(aⁱʲ ∂ⱼu) + c u = ℓ` weakly in `Ω`
with `u = g` on `∂Ω` in the sense of traces: `u ∘ e⁻¹` and `g ∘ e⁻¹` have the same trace on
`frontier V`. The principal coefficient need not be symmetric. Coercivity of the energy form
comes from the Poincaré inequality on a ball containing the bounded set `Ω`. -/
theorem existsUnique_frontierTrace_eq_forall_energyFormH1_eq
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) a lam Lam)
    (ha : AEStronglyMeasurable a (volume.restrict Omega))
    (hc : AEStronglyMeasurable c (volume.restrict Omega))
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))), ‖c x‖ ≤ gamma)
    (hc_nonneg : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))), 0 ≤ c x)
    (hV : (V : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : Bornology.IsBounded (V : Set (WithLp 2 (ℝ × E))))
    (e : EuclideanSpace ℝ (Fin (n + 1)) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E))
    (hVΩ : (V : Set (WithLp 2 (ℝ × E))) = e.symm ⁻¹' Omega) (g : W1p volume Omega 2)
    (ℓ : StrongDual ℝ (W1p0 volume Omega 2)) :
    ∃! u : W1p volume Omega 2,
      W1p.frontierTrace ENNReal.ofNat_ne_top hV hb (W1p.compAffineIsometryEquivL e.symm hVΩ u) =
          W1p.frontierTrace ENNReal.ofNat_ne_top hV hb
            (W1p.compAffineIsometryEquivL e.symm hVΩ g) ∧
        ∀ v : W1p0 volume Omega 2, energyFormH1 a 0 c u (v : W1p volume Omega 2) = ℓ v := by
  -- `Ω = e⁻¹(V)` is bounded, hence contained in a ball of positive radius.
  have hΩ : Bornology.IsBounded (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) := by
    have himage := e.symm.lipschitzWith.isBounded_image hb
    rwa [hVΩ, Set.image_preimage_eq _ e.symm.surjective] at himage
  have hball := Bornology.IsBounded.subset_ball_lt hΩ 0 (e.symm 0)
  rcases hball with ⟨R, hR⟩
  have hb0 : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))),
      ‖(0 : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))) x‖ ≤ 0 :=
    fun _ _ => by rw [Pi.zero_apply, norm_zero]
  have hcoeff := memLp_energyIntegrand_of_bounds h.upper_nonneg ha aestronglyMeasurable_const hc
    (fun _x hx eta xi => h.upper_bound hx eta xi) hb0 hc_bound
  have hC := energyFormH1_poincare_constant_pos h.pos le_rfl (P := 2 * R) (by linarith [hR.1])
    (by rw [zero_mul]; exact h.pos)
  have hcoercive := isCoercive_energyFormH1L0 hcoeff hC fun w =>
    mul_norm_sq_le_energyFormH1_self_of_subset_ball h ha aestronglyMeasurable_const hc hb0
      hc_bound hc_nonneg hR.2 w.2
  exact PDE.existsUnique_frontierTrace_eq_forall_energyFormH1_eq hV hb e hVΩ hcoeff hcoercive g ℓ

end UniformlyEllipticOn

end Euclidean

end PDE

end TauCeti

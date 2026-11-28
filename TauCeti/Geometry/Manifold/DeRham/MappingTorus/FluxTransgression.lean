/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.MappingTorus.SeamedTorusClass
public import TauCeti.Geometry.Manifold.DeRham.HomologyPeriod.Circle
public import TauCeti.Topology.UnitInterval.PathConnected

/-!
# The flux transgression of loops of seamed paths

Let `φ` be a homeomorphism of a manifold `M`, with mapping torus `Y_φ`, and let `θ` be a closed
`C¹` one-form on `M`. A loop `s ↦ γ_s` of `φ`-seamed paths sweeps out a torus
`(t, s) ↦ [γ_s(t), t]` in `Y_φ` (`TauCeti.SeamedPath.torusClassHom`), and the mapping-torus
boundary `∂ : H₂(Y_φ; ℤ) → H₁(M; ℤ)`, the Wang boundary up to the sign `ε = torusWangSign`, sends
its class to the class of the loop `s ↦ γ_s(0)` of start points
(`TauCeti.SeamedPath.torusWangSign_smul_wangδ_torusClassHom_ofMul_mk`). The **flux
transgression** of `θ` (`TauCeti.MappingTorus.fluxTransgression`) is the homomorphism

`H₂(Y_φ; ℤ) → F`,  `A ↦ ⟨[θ], ε • ∂ A⟩`,

the period of `θ` (`TauCeti.homologyPeriodHom`) on the mapping-torus boundary.

In the Floer–Novikov theory of a symplectomorphism, `θ = ι_X ω` for a symplectic vector field `X`,
and the action one-form on seamed paths has the flux term `ξ ↦ ∫₀¹ θ_t(ξ(t)) dt`. Integrated
over a loop of seamed paths traced by a smooth map `u`, this term gives the swept integral

`∫₀¹ ∫₀¹ θ_t(∂_s u(s, t)) ds dt`,

and the flux transgression is what this swept integral computes:

* for a single closed form `θ`, the line integral along each `C¹` loop `s ↦ u(s, t)` of the
  family is the value of the flux transgression on the swept torus
  (`TauCeti.MappingTorus.fluxTransgression_torusClassHom`); the loops are freely homotopic through
  the family to the loop of start points, so they have its class in `H₁(M; ℤ)`;
* for a family `θ_t` of closed forms, the swept integral is the time integral
  `∫₀¹ ⟨[θ_t], ε • ∂ A⟩ dt` of the flux transgressions
  (`TauCeti.MappingTorus.intervalIntegral_fluxTransgression_torusClassHom`).

This is the flux half `⟨[θ_X], ∂_f A⟩` of the period character `P_X(A) = -⟨[ω^f], A⟩ +
⟨[θ_X], ∂_f A⟩` of the Floer–Novikov theory of Lee; the other half is the area transgression of the
fibre form.

## Main definitions

* `TauCeti.MappingTorus.fluxTransgression φ θ`: the homomorphism `A ↦ ⟨[θ], ε • ∂ A⟩` from
  `H₂(Y_φ; ℤ)`.

## Main results

* `TauCeti.MappingTorus.fluxTransgression_singularHomologyMap_sectionFamily`,
  `TauCeti.MappingTorus.fluxTransgression_torusClassHom`: the flux transgression of the torus swept
  out by a loop of seamed paths is the line integral along each of its loops `s ↦ γ_s(t)` that is
  `C¹`.
* `TauCeti.MappingTorus.intervalIntegral_fluxTransgression_torusClassHom`: for a family of closed
  forms, the time integral of the flux transgressions is the swept integral.

## References

* Y.-J. Lee, *Reidemeister torsion in Floer–Novikov theory and counting pseudo-holomorphic tori,
  I*, J. Symplectic Geom. 3 (2005), 221–311, §3.1, on the period characters of loops of sections of
  the mapping torus and their flux term.
* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford University
  Press, 2017, Section 10.2, on the flux of symplectic vector fields.
-/

public section

noncomputable section

open Set CategoryTheory AlgebraicTopology TauCeti.HurewiczOne
open scoped Manifold ContDiff Topology.Homotopy

namespace TauCeti

variable {E H : Type*} {M F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ E] [T2Space M] [IsManifold I ∞ M] [CompleteSpace F]
  {θ : RoughForm I M F 1}

/-! ### The flux transgression -/

namespace MappingTorus

variable (φ : M ≃ₜ M)

/-- **The flux transgression** of a one-form `θ` on `M`: the homomorphism
`H₂(Y_φ; ℤ) → F`, `A ↦ ⟨[θ], ε • ∂ A⟩`, the period of `θ` on the mapping-torus boundary of `A`,
the Wang boundary `∂` with the sign `ε = torusWangSign`, which sends the torus swept out by a loop
of seamed paths to its loop of start points. It is meaningful for closed `C¹` forms. -/
def fluxTransgression (θ : RoughForm I M F 1) :
    ((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).obj
      (TopCat.of (MappingTorus φ)) →+ F :=
  (homologyPeriodHom θ).comp
    (torusWangSign • (wangδ φ (ModuleCat.of ℤ ℤ) 1).hom.toAddMonoidHom)

/-- The flux transgression is the period on the mapping-torus boundary. -/
theorem fluxTransgression_apply
    (A : ((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).obj
      (TopCat.of (MappingTorus φ))) :
    fluxTransgression φ θ A =
      homologyPeriodHom θ (torusWangSign • (wangδ φ (ModuleCat.of ℤ ℤ) 1).hom A) :=
  (rfl)

/-- The flux transgression of an exact form vanishes. -/
theorem fluxTransgression_mextDeriv {ψ : RoughForm I M F 0} (hψ : IsSmoothForm I 2 ψ) :
    fluxTransgression φ (mextDeriv ψ) = 0 :=
  AddMonoidHom.ext fun A ↦ by
    rw [fluxTransgression_apply, homologyPeriodHom_mextDeriv hψ, AddMonoidHom.zero_apply,
      AddMonoidHom.zero_apply]

/-- The flux transgression is additive in the form. -/
theorem fluxTransgression_add {ψ : RoughForm I M F 1} (hθ : IsSmoothForm I 1 θ)
    (hθc : mextDeriv θ = 0) (hψ : IsSmoothForm I 1 ψ) (hψc : mextDeriv ψ = 0) :
    fluxTransgression φ (θ + ψ) = fluxTransgression φ θ + fluxTransgression φ ψ :=
  AddMonoidHom.ext fun A ↦ by
    rw [fluxTransgression_apply, homologyPeriodHom_add hθ hθc hψ hψc, AddMonoidHom.add_apply,
      AddMonoidHom.add_apply, fluxTransgression_apply, fluxTransgression_apply]

/-- The flux transgression of the zero form vanishes. -/
@[simp]
theorem fluxTransgression_zero : fluxTransgression φ (0 : RoughForm I M F 1) = 0 :=
  AddMonoidHom.ext fun A ↦ by
    rw [fluxTransgression_apply, homologyPeriodHom_zero, AddMonoidHom.zero_apply,
      AddMonoidHom.zero_apply]

/-- The flux transgression is homogeneous in the form. -/
@[simp]
theorem fluxTransgression_smul (a : ℝ) :
    fluxTransgression φ (a • θ) = a • fluxTransgression φ θ :=
  AddMonoidHom.ext fun A ↦ by
    rw [fluxTransgression_apply, homologyPeriodHom_smul, AddMonoidHom.smul_apply,
      AddMonoidHom.smul_apply, fluxTransgression_apply]

/-- **The flux transgression of the torus swept out by a loop of seamed paths.** Let `s ↦ γ_s`
be a loop of `φ`-seamed paths parametrized by the circle, and let `t ∈ [0, 1]` be a time whose loop
`s ↦ γ_s(t)` reads `s ↦ c s` on `[0, 1]` for a `C¹` curve `c`. The flux transgression of a closed
`C¹` one-form `θ` on the class of the swept torus `(t, s) ↦ [γ_s(t), t]` is the line integral of
`θ` along `c`. -/
theorem fluxTransgression_singularHomologyMap_sectionFamily (hθ : IsSmoothForm I 1 θ)
    (hclosed : mextDeriv θ = 0) (ℓ : C(UnitAddCircle, SeamedPath φ)) (t : unitInterval)
    {c : ℝ → M} (hc : ContMDiff 𝓘(ℝ, ℝ) I 1 c)
    (hℓc : ∀ s : unitInterval, (ℓ (s : ℝ)).val t = c s) :
    fluxTransgression φ θ
        (ContinuousMap.singularHomologyMap ℤ 2
          ((SeamedPath.sectionFamily φ ℓ).comp ContinuousMap.prodSwap)
          (addCircleProdFundamentalClass 1 1)) =
      pathIntegral θ c 0 1 := by
  -- The loops `s ↦ γ_s(r)` of the family; the loop of start points is homotopic to the loop at
  -- the time `t` along a path from `0` to `t`.
  let g : unitInterval → C(UnitAddCircle, M) := fun r ↦ ⟨fun s ↦ (ℓ s).val r, by fun_prop⟩
  let γ : Path 0 t := PathConnectedSpace.somePath 0 t
  let K : (g 0).Homotopy (g t) :=
    { toFun := fun p ↦ (ℓ p.2).val (γ p.1)
      continuous_toFun := by fun_prop
      map_zero_left := fun s ↦ by simp [g]
      map_one_left := fun s ↦ by simp [g] }
  -- `rw [fluxTransgression_apply]` fails here: the class is stated in the homology of the singular
  -- chains, the domain of `fluxTransgression` in singular homology, and these agree only up to
  -- unfolding `singularHomologyFunctor`.
  refine (fluxTransgression_apply φ _).trans ?_
  rw [SeamedPath.torusWangSign_smul_wangδ_singularHomologyMap_sectionFamily_comp_prodSwap φ ℓ (g 0)
      fun s ↦ rfl,
    ContinuousMap.singularHomologyMap_eq_of_homotopic ℤ 1 ⟨K⟩]
  exact homologyPeriodHom_singularHomologyMap_fundamentalClass hθ hclosed (g t) hc hℓc

/-- **The flux transgression of the torus class of a loop of seamed paths.** For a loop `p` of
`φ`-seamed paths at `γ`, parametrized by the circle as `ℓ`, and a time `t ∈ [0, 1]` whose loop
`s ↦ γ_s(t)` reads `s ↦ c s` on `[0, 1]` for a `C¹` curve `c`, the flux transgression of a closed
`C¹` one-form `θ` on the torus class of `p` is the line integral of `θ` along `c`. -/
theorem fluxTransgression_torusClassHom (hθ : IsSmoothForm I 1 θ) (hclosed : mextDeriv θ = 0)
    {γ : SeamedPath φ} (p : Ω^ (Fin 1) (SeamedPath φ) γ) (ℓ : C(UnitAddCircle, SeamedPath φ))
    (hℓ : ∀ t : unitInterval, ℓ (t : ℝ) = p (fun _ ↦ t)) (t : unitInterval) {c : ℝ → M}
    (hc : ContMDiff 𝓘(ℝ, ℝ) I 1 c) (hℓc : ∀ s : unitInterval, (ℓ (s : ℝ)).val t = c s) :
    fluxTransgression φ θ (SeamedPath.torusClassHom φ γ (Additive.ofMul ⟦p⟧)) =
      pathIntegral θ c 0 1 := by
  rw [SeamedPath.torusClassHom_ofMul_mk_eq_singularHomologyMap φ p ℓ hℓ]
  exact fluxTransgression_singularHomologyMap_sectionFamily φ hθ hclosed ℓ t hc hℓc

/-- **The swept flux integral of a family of closed forms.** For a family `θ_t` of closed `C¹`
one-forms and a loop `p` of `φ`-seamed paths, parametrized by the circle as `ℓ` and traced by a map
`u`, `γ_s(t) = u(s, t)` for `t ∈ [0, 1]`, whose loops `s ↦ u(s, t)` are `C¹`, the time integral
of the flux transgressions of the forms `θ_t` on the torus class `A` of `p` is the swept integral of
the family:

`∫₀¹ ⟨[θ_t], ε • ∂ A⟩ dt = ∫₀¹ ∫₀¹ θ_t(∂_s u(s, t)) ds dt`.

This is the flux term of the period of the action one-form of seamed paths. -/
theorem intervalIntegral_fluxTransgression_torusClassHom {θ : ℝ → RoughForm I M F 1}
    (hθ : ∀ t ∈ Icc (0 : ℝ) 1, IsSmoothForm I 1 (θ t))
    (hclosed : ∀ t ∈ Icc (0 : ℝ) 1, mextDeriv (θ t) = 0)
    {γ : SeamedPath φ} (p : Ω^ (Fin 1) (SeamedPath φ) γ) (ℓ : C(UnitAddCircle, SeamedPath φ))
    (hℓ : ∀ t : unitInterval, ℓ (t : ℝ) = p (fun _ ↦ t)) {u : ℝ × ℝ → M}
    (hu : ∀ t : unitInterval, ContMDiff 𝓘(ℝ, ℝ) I 1 fun s ↦ u (s, t))
    (hℓu : ∀ s t : unitInterval, (ℓ (s : ℝ)).val t = u (s, t)) :
    ∫ t in (0 : ℝ)..1,
        fluxTransgression φ (θ t) (SeamedPath.torusClassHom φ γ (Additive.ofMul ⟦p⟧)) =
      ∫ t in (0 : ℝ)..1, ∫ s in (0 : ℝ)..1,
        θ t (u (s, t)) fun _ ↦ Manifold.curveVelocity I (fun s ↦ u (s, t)) s := by
  refine intervalIntegral.integral_congr fun t ht ↦ ?_
  rw [uIcc_of_le zero_le_one] at ht
  exact (fluxTransgression_torusClassHom φ (hθ t ht) (hclosed t ht) p ℓ hℓ ⟨t, ht⟩ (hu ⟨t, ht⟩)
    fun s ↦ hℓu s ⟨t, ht⟩).trans (pathIntegral_def _ _ _ _)

end MappingTorus

end TauCeti

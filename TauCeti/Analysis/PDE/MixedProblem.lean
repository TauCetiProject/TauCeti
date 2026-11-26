/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.LaxMilgram
public import TauCeti.Analysis.PDE.EnergyForm.InverseCoercive
public import TauCeti.Analysis.Sobolev.LipschitzDomain.BoundaryPart
import TauCeti.Analysis.InnerProductSpace.Variational.Lifting
import TauCeti.Analysis.Variational.QuadraticEnergy

/-!
# The mixed boundary value problem in the coercive case

Let `Ω` be an open set, `Γ` a set, typically a part of the boundary, and
`L u = -∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u` a divergence-form operator with energy form `B`
(`TauCeti.PDE.energyFormH1`). For `g ∈ H¹(Ω)` and `ℓ ∈ (H¹_Γ(Ω))*` the weak form of the mixed
problem asks for `u ∈ H¹(Ω)` with

`u - g ∈ H¹_Γ(Ω)` and `B(u, v) = ℓ v` for every `v ∈ H¹_Γ(Ω)`,

where `H¹_Γ(Ω)` is the space `TauCeti.W1pVanishingOn` of Sobolev functions vanishing on `Γ`. The
Dirichlet condition `u = g` on `Γ` is carried by membership of `u - g` in `H¹_Γ(Ω)`. Nothing is
imposed on the rest of the boundary: testing against all of `H¹_Γ(Ω)` makes the conormal
derivative there the natural boundary condition, and a prescribed conormal derivative `h` enters
through `ℓ`, as `v ↦ ∫ h v` over the boundary. For `Γ` the whole frontier this is the Dirichlet
problem, and for `Γ = ∅` the Neumann problem.

## Coercivity and Lax–Milgram

When `B` is coercive on `H¹_Γ(Ω)`, the problem has exactly one solution, for every `g` and `ℓ`
(`TauCeti.PDE.existsUnique_sub_mem_w1pVanishingOnSubmodule_forall_energyFormH1_eq`). It is
Lax–Milgram on the closed subspace `H¹_Γ(Ω)` applied to `u - g`, with forcing `ℓ - B(g, ·)`, and
the solution map `(g, ℓ) ↦ u` is a bounded linear operator `TauCeti.PDE.mixedSolutionL`, with
`‖u - g‖ ≤ (‖ℓ‖ + ‖B‖ ‖g‖) / C` for a coercivity constant `C`. Without drift, two hypotheses give
coercivity, for a principal coefficient with ellipticity constant `λ`:

* a mass floor `c ≥ δ > 0` gives the constant `min λ δ`, for every `Γ`;
* `c ≥ 0` and a Poincaré–Friedrichs inequality `‖u‖_{L²} ≤ P ‖∇u‖_{L²}` on `H¹_Γ(Ω)` give the
  constant `λ / (1 + P²)`.

The second applies on a bounded connected Lipschitz domain when `Γ` meets the frontier in a set of
positive surface measure: this is the Poincaré–Friedrichs inequality
`TauCeti.W1p.exists_norm_value_le_mul_norm_gradient_of_mem_w1pVanishingOnSubmodule`.
Lipschitz domains are set in the product `ℝ × E` of their boundary charts while the energy form
lives on `EuclideanSpace ℝ ι`, so, as in `TauCeti/Analysis/PDE/DirichletProblem/Trace.lean`, the
domain is an isometric copy of a Lipschitz domain. This gives unique solvability of the mixed
problem for inverse-coercive `a`, no drift and `c ≥ 0`.

## Dirichlet's principle

For a symmetric form, nonnegative on `H¹_Γ(Ω)`, the solutions are the minimizers of the energy:
`w₀ ∈ H¹_Γ(Ω)` minimizes `J(w) = B(g + w, g + w) / 2 - ℓ w` exactly when `g + w₀` solves the
mixed problem. Since `J(w) = B(u, u) / 2 - ℓ (u - g)` for `u = g + w`, this is the minimization of
`B(u, u) / 2 - ℓ (u - g)` over the affine space `g + H¹_Γ(Ω)`. For a coercive symmetric form the
minimizer exists and is unique, and `g + w₀` is the solution `mixedSolutionL (g, ℓ)`. This holds on
a bounded connected Lipschitz domain with a Dirichlet part of positive surface measure, for an
almost everywhere symmetric inverse-coercive `a`, no drift and `c ≥ 0`.

## Main declarations

* `TauCeti.PDE.energyFormH1LVanishingOn`: the energy form as a bounded bilinear form on
  `H¹_Γ(Ω)`.
* `TauCeti.PDE.mixedSolutionL`: the bounded linear solution map `(g, ℓ) ↦ u` of a coercive
  form, characterized by `TauCeti.PDE.mixedSolutionL_eq_iff`, with the bounds
  `TauCeti.PDE.norm_mixedSolutionL_sub_le` and `TauCeti.PDE.norm_mixedSolutionL_apply_le`.
* `TauCeti.PDE.existsUnique_sub_mem_w1pVanishingOnSubmodule_forall_energyFormH1_eq`: existence
  and uniqueness of the weak solution of the mixed problem for a coercive form.
* `TauCeti.PDE.UniformlyEllipticOn.isCoercive_energyFormH1LVanishingOn_of_mass_lower_bound` and
  `TauCeti.PDE.UniformlyEllipticOn.isCoercive_energyFormH1LVanishingOn_of_poincare`: the two
  sources of coercivity, and their versions
  `TauCeti.PDE.IsUniformlyEllipticAE.isCoercive_energyFormH1LVanishingOn_of_mass_lower_bound` and
  `TauCeti.PDE.IsUniformlyEllipticAE.isCoercive_energyFormH1LVanishingOn_of_poincare` for an
  inverse-coercive principal coefficient, a drift vanishing almost everywhere and almost
  everywhere bounds on the mass coefficient, from which the pointwise versions follow.
* `existsUnique_sub_mem_w1pVanishingOnSubmodule_forall_energyFormH1_eq_of_isLipschitzDomainWith`
  and `isCoercive_energyFormH1LVanishingOn_of_isLipschitzDomainWith`, in the namespace
  `TauCeti.PDE.IsUniformlyEllipticAE`: the mixed problem on a bounded connected Lipschitz domain,
  with a Dirichlet part of positive surface measure.
* `TauCeti.PDE.isMinOn_w1pVanishingOn_iff_forall_energyFormH1_eq`: Dirichlet's principle for the
  mixed problem, for a symmetric form nonnegative on `H¹_Γ(Ω)`.
* `TauCeti.PDE.isMinOn_iff_mixedSolutionL_eq` and
  `TauCeti.PDE.existsUnique_w1pVanishingOn_isMinOn_energyFormH1`: for a coercive symmetric form,
  the energy has exactly one minimizer, and it gives `mixedSolutionL`.
* `existsUnique_w1pVanishingOn_isMinOn_energyFormH1_of_isLipschitzDomainWith`, in the namespace
  `TauCeti.PDE.IsUniformlyEllipticAE`: the same on a bounded connected Lipschitz domain, for an
  almost everywhere symmetric principal coefficient.

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
  Proposition 9.24 (the Neumann problem for `-Δu + u = f`) and §8.4, Example 5 (a mixed problem
  in one dimension).
* P. Grisvard, *Elliptic Problems in Nonsmooth Domains*, §1.5 (mixed boundary conditions).
* L. C. Evans, *Partial Differential Equations*, 2nd ed., §6.2.1–§6.2.2 (the lifting of the
  Dirichlet datum and Lax–Milgram) and §2.2.5, Theorem 17 (Dirichlet's principle).
-/

public section

noncomputable section

namespace TauCeti

namespace PDE

open MeasureTheory Module Set TopologicalSpace
open scoped ENNReal NNReal InnerProductSpace

section Domain

variable {ι : Type*} [Fintype ι] {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
  {Omega : Opens (EuclideanSpace ℝ ι)} {Γ : Set (EuclideanSpace ℝ ι)}
  {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
  {c : EuclideanSpace ℝ ι → ℝ} {C : ℝ}

attribute [local instance] instSeminormedAddCommGroupW1p instNormedSpaceW1p
  W1pVanishingOn.instNormedAddCommGroup W1pVanishingOn.instInnerProductSpace

/-! ### The energy form on `H¹_Γ(Ω)` -/

/-- **The energy form on `H¹_Γ(Ω)`** as a continuous bilinear form, obtained by restricting
`TauCeti.PDE.energyFormH1L` along the closed-subspace inclusion. -/
def energyFormH1LVanishingOn
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (Γ : Set (EuclideanSpace ℝ ι)) :
    W1pVanishingOn mu Omega 2 Γ →L[ℝ] W1pVanishingOn mu Omega 2 Γ →L[ℝ] ℝ :=
  (energyFormH1L hcoeff).bilinearComp (W1pVanishingOn mu Omega 2 Γ).subtypeL
    (W1pVanishingOn mu Omega 2 Γ).subtypeL

-- Stated by `rfl` rather than by unfolding: the generated equation lemma of the definition is
-- expensive to type-check through the nested Sobolev subspace instances.
private theorem energyFormH1LVanishingOn_eq_bilinearComp
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega)) :
    energyFormH1LVanishingOn hcoeff Γ = (energyFormH1L hcoeff).bilinearComp
      (W1pVanishingOn mu Omega 2 Γ).subtypeL (W1pVanishingOn mu Omega 2 Γ).subtypeL :=
  rfl

/-- The energy form on `H¹_Γ(Ω)` evaluates to `energyFormH1` on the underlying Sobolev
functions. -/
@[simp]
theorem energyFormH1LVanishingOn_apply
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (u v : W1pVanishingOn mu Omega 2 Γ) :
    energyFormH1LVanishingOn hcoeff Γ u v =
      energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) := by
  rw [energyFormH1LVanishingOn_eq_bilinearComp, ContinuousLinearMap.bilinearComp_apply,
    energyFormH1L_apply]
  simp only [Submodule.subtypeL_apply]

/-- **A diagonal lower bound is coercivity.** A bound `C ‖w‖² ≤ B(w, w)` on `H¹_Γ(Ω)` with
`0 < C` makes the energy form coercive there. -/
theorem isCoercive_energyFormH1LVanishingOn
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hC : 0 < C)
    (hlower : ∀ w : W1pVanishingOn mu Omega 2 Γ,
      C * ‖w‖ ^ 2 ≤ energyFormH1 a b c (w : W1p mu Omega 2) (w : W1p mu Omega 2)) :
    IsCoercive (energyFormH1LVanishingOn hcoeff Γ) := by
  refine ⟨C, hC, fun w => ?_⟩
  rw [energyFormH1LVanishingOn_apply]
  calc C * ‖w‖ * ‖w‖ = C * ‖w‖ ^ 2 := by ring
    _ ≤ _ := hlower w

/-! ### The solution operator -/

variable (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
  (hcoercive : IsCoercive (energyFormH1LVanishingOn hcoeff Γ))

include hcoercive in
/-- The coercivity hypothesis, in the form of the abstract lifting construction. -/
private theorem isCoercive_bilinearComp :
    IsCoercive ((energyFormH1L hcoeff).bilinearComp (W1pVanishingOn mu Omega 2 Γ).subtypeL
      (W1pVanishingOn mu Omega 2 Γ).subtypeL) :=
  energyFormH1LVanishingOn_eq_bilinearComp hcoeff ▸ hcoercive

/-- **The solution map of the mixed problem.** For a form coercive on `H¹_Γ(Ω)` it sends a
Dirichlet datum `g ∈ H¹(Ω)` and a forcing `ℓ ∈ (H¹_Γ(Ω))*` to the unique `u ∈ H¹(Ω)` with
`u - g ∈ H¹_Γ(Ω)` and `B(u, v) = ℓ v` for every `v ∈ H¹_Γ(Ω)`, and it is linear and bounded in
the pair `(g, ℓ)`. It is characterized by `TauCeti.PDE.mixedSolutionL_eq_iff`. -/
def mixedSolutionL :
    (W1p mu Omega 2 × StrongDual ℝ (W1pVanishingOn mu Omega 2 Γ)) →L[ℝ] W1p mu Omega 2 :=
  (isCoercive_bilinearComp hcoeff hcoercive).solutionWithLifting

private theorem mixedSolutionL_eq :
    mixedSolutionL hcoeff hcoercive =
      (isCoercive_bilinearComp hcoeff hcoercive).solutionWithLifting :=
  rfl

/-- The solution of the mixed problem satisfies the weak equation against every test function
in `H¹_Γ(Ω)`. -/
@[simp]
theorem energyFormH1_mixedSolutionL (g : W1p mu Omega 2)
    (ℓ : StrongDual ℝ (W1pVanishingOn mu Omega 2 Γ)) (v : W1pVanishingOn mu Omega 2 Γ) :
    energyFormH1 a b c (mixedSolutionL hcoeff hcoercive (g, ℓ)) v = ℓ v := by
  simpa only [mixedSolutionL_eq, energyFormH1L_apply, Submodule.subtypeL_apply] using
    (isCoercive_bilinearComp hcoeff hcoercive).apply_solutionWithLifting g ℓ v

/-- **Characterization of the solution of the mixed problem** by its Dirichlet datum and its weak
equation: `u` is the solution for `(g, ℓ)` exactly when `u - g ∈ H¹_Γ(Ω)` and `B(u, v) = ℓ v` for
every `v ∈ H¹_Γ(Ω)`. -/
theorem mixedSolutionL_eq_iff {g u : W1p mu Omega 2}
    {ℓ : StrongDual ℝ (W1pVanishingOn mu Omega 2 Γ)} :
    mixedSolutionL hcoeff hcoercive (g, ℓ) = u ↔
      u - g ∈ w1pVanishingOnSubmodule mu Omega 2 Γ ∧
        ∀ v : W1pVanishingOn mu Omega 2 Γ, energyFormH1 a b c u v = ℓ v := by
  rw [mixedSolutionL_eq, IsCoercive.solutionWithLifting_eq_iff]
  refine and_congr ⟨fun ⟨w, hw⟩ => ?_, fun h => ⟨⟨u - g, h⟩, rfl⟩⟩
    (forall_congr' fun v => by rw [energyFormH1L_apply, Submodule.subtypeL_apply])
  rw [← hw, Submodule.subtypeL_apply, ← ClosedSubmodule.mem_toSubmodule_iff]
  exact w.property

/-- The solution of the mixed problem has Dirichlet datum `g` on `Γ`: `u - g ∈ H¹_Γ(Ω)`. -/
theorem mixedSolutionL_sub_mem (g : W1p mu Omega 2)
    (ℓ : StrongDual ℝ (W1pVanishingOn mu Omega 2 Γ)) :
    mixedSolutionL hcoeff hcoercive (g, ℓ) - g ∈ w1pVanishingOnSubmodule mu Omega 2 Γ :=
  ((mixedSolutionL_eq_iff hcoeff hcoercive).1 rfl).1

include hcoercive in
/-- **The mixed problem with a coercive form.** For a divergence-form operator whose energy form
is bounded and coercive on `H¹_Γ(Ω)`, every Dirichlet datum `g ∈ H¹(Ω)` and every forcing
`ℓ ∈ (H¹_Γ(Ω))*`, there is exactly one `u ∈ H¹(Ω)` with `u - g ∈ H¹_Γ(Ω)` and

`B(u, v) = ℓ v` for every `v ∈ H¹_Γ(Ω)`.

This is the weak form of `L u = ℓ` in `Ω`, `u = g` on `Γ`, with the natural (conormal) boundary
condition on the rest of the boundary. -/
theorem existsUnique_sub_mem_w1pVanishingOnSubmodule_forall_energyFormH1_eq (g : W1p mu Omega 2)
    (ℓ : StrongDual ℝ (W1pVanishingOn mu Omega 2 Γ)) :
    ∃! u : W1p mu Omega 2, u - g ∈ w1pVanishingOnSubmodule mu Omega 2 Γ ∧
      ∀ v : W1pVanishingOn mu Omega 2 Γ, energyFormH1 a b c u v = ℓ v :=
  ⟨mixedSolutionL hcoeff hcoercive (g, ℓ), (mixedSolutionL_eq_iff hcoeff hcoercive).1 rfl,
    fun _ hu => ((mixedSolutionL_eq_iff hcoeff hcoercive).2 hu).symm⟩

/-! ### Dirichlet's principle -/

omit hcoercive in
include hcoeff in
/-- **Dirichlet's principle for the mixed problem.** Let the energy form be symmetric on `H¹(Ω)`
and nonnegative on `H¹_Γ(Ω)`. For a Dirichlet datum `g ∈ H¹(Ω)` and a forcing
`ℓ ∈ (H¹_Γ(Ω))*`, the energy `J(w) = B(g + w, g + w) / 2 - ℓ w` has a minimum on `H¹_Γ(Ω)` at
`w₀` exactly when `u = g + w₀` solves the mixed problem: `B(u, v) = ℓ v` for every
`v ∈ H¹_Γ(Ω)`.

The functions `g + w` run over the affine space `g + H¹_Γ(Ω)` of functions with Dirichlet datum
`g` on `Γ`, and `J(w) = B(g + w, g + w) / 2 - ℓ ((g + w) - g)`, so this says that the solutions are
the minimizers of `B(u, u) / 2 - ℓ (u - g)` over `g + H¹_Γ(Ω)`. With no drift and an almost
everywhere symmetric principal coefficient the symmetry hypothesis is
`TauCeti.PDE.energyFormH1_comm_of_isSymm_ae`. -/
theorem isMinOn_w1pVanishingOn_iff_forall_energyFormH1_eq
    (hsymm : ∀ v w : W1p mu Omega 2, energyFormH1 a b c v w = energyFormH1 a b c w v)
    (hnonneg : ∀ w : W1pVanishingOn mu Omega 2 Γ,
      0 ≤ energyFormH1 a b c (w : W1p mu Omega 2) (w : W1p mu Omega 2))
    (g : W1p mu Omega 2) (ℓ : StrongDual ℝ (W1pVanishingOn mu Omega 2 Γ))
    (w₀ : W1pVanishingOn mu Omega 2 Γ) :
    IsMinOn (fun w : W1pVanishingOn mu Omega 2 Γ =>
        energyFormH1 a b c (g + (w : W1p mu Omega 2)) (g + (w : W1p mu Omega 2)) / 2 - ℓ w)
      univ w₀ ↔
      ∀ v : W1pVanishingOn mu Omega 2 Γ,
        energyFormH1 a b c (g + (w₀ : W1p mu Omega 2)) v = ℓ v := by
  simpa only [energyFormH1L_apply, Submodule.subtypeL_apply] using
    (energyFormH1L hcoeff).isMinOn_iff_forall_apply_eq (W1pVanishingOn mu Omega 2 Γ).subtypeL
      (fun v w => by simpa only [energyFormH1L_apply] using hsymm v w)
      (fun w => by simpa only [energyFormH1L_apply, Submodule.subtypeL_apply] using hnonneg w)
      g ℓ w₀

/-- **Dirichlet's principle for a coercive symmetric form.** If the energy form is symmetric on
`H¹(Ω)` and coercive on `H¹_Γ(Ω)`, then `w₀ ∈ H¹_Γ(Ω)` minimizes the energy
`J(w) = B(g + w, g + w) / 2 - ℓ w` exactly when `g + w₀` is the solution of the mixed problem for
`(g, ℓ)`. -/
theorem isMinOn_iff_mixedSolutionL_eq
    (hsymm : ∀ v w : W1p mu Omega 2, energyFormH1 a b c v w = energyFormH1 a b c w v)
    (g : W1p mu Omega 2) (ℓ : StrongDual ℝ (W1pVanishingOn mu Omega 2 Γ))
    (w₀ : W1pVanishingOn mu Omega 2 Γ) :
    IsMinOn (fun w : W1pVanishingOn mu Omega 2 Γ =>
        energyFormH1 a b c (g + (w : W1p mu Omega 2)) (g + (w : W1p mu Omega 2)) / 2 - ℓ w)
      univ w₀ ↔
      mixedSolutionL hcoeff hcoercive (g, ℓ) = g + (w₀ : W1p mu Omega 2) := by
  rw [mixedSolutionL_eq]
  simpa only [energyFormH1L_apply, Submodule.subtypeL_apply] using
    (isCoercive_bilinearComp hcoeff hcoercive).isMinOn_iff_solutionWithLifting_eq
      (fun v w => by simpa only [energyFormH1L_apply] using hsymm v w) g ℓ w₀

include hcoercive in
/-- **The energy of the mixed problem has exactly one minimizer.** If the energy form is symmetric
on `H¹(Ω)` and coercive on `H¹_Γ(Ω)`, then for every Dirichlet datum `g ∈ H¹(Ω)` and every forcing
`ℓ ∈ (H¹_Γ(Ω))*` the energy `J(w) = B(g + w, g + w) / 2 - ℓ w` has exactly one minimizer `w₀` on
`H¹_Γ(Ω)`, and `g + w₀` is the solution of the mixed problem
(`TauCeti.PDE.isMinOn_iff_mixedSolutionL_eq`). -/
theorem existsUnique_w1pVanishingOn_isMinOn_energyFormH1
    (hsymm : ∀ v w : W1p mu Omega 2, energyFormH1 a b c v w = energyFormH1 a b c w v)
    (g : W1p mu Omega 2) (ℓ : StrongDual ℝ (W1pVanishingOn mu Omega 2 Γ)) :
    ∃! w₀ : W1pVanishingOn mu Omega 2 Γ, IsMinOn (fun w : W1pVanishingOn mu Omega 2 Γ =>
      energyFormH1 a b c (g + (w : W1p mu Omega 2)) (g + (w : W1p mu Omega 2)) / 2 - ℓ w)
        univ w₀ := by
  simp only [isMinOn_iff_mixedSolutionL_eq hcoeff hcoercive hsymm]
  refine ⟨⟨_, mixedSolutionL_sub_mem hcoeff hcoercive g ℓ⟩, (add_sub_cancel g _).symm,
    fun w hw => Subtype.ext (eq_sub_of_add_eq' hw.symm)⟩

variable (hC : 0 < C)
  (hlower : ∀ w : W1pVanishingOn mu Omega 2 Γ,
    C * ‖w‖ ^ 2 ≤ energyFormH1 a b c (w : W1p mu Omega 2) (w : W1p mu Omega 2))

include hC hlower

/-- **The energy estimate for the mixed problem.** If `C ‖w‖² ≤ B(w, w)` on `H¹_Γ(Ω)` with
`0 < C`, the solution `u` for `(g, ℓ)` satisfies `‖u - g‖ ≤ (‖ℓ‖ + ‖B‖ ‖g‖) / C`, where `‖B‖` is
the norm of the energy form as a bounded bilinear form on `H¹(Ω)`. -/
theorem norm_mixedSolutionL_sub_le (g : W1p mu Omega 2)
    (ℓ : StrongDual ℝ (W1pVanishingOn mu Omega 2 Γ)) :
    ‖mixedSolutionL hcoeff hcoercive (g, ℓ) - g‖ ≤ (‖ℓ‖ + ‖energyFormH1L hcoeff‖ * ‖g‖) / C := by
  have h := (isCoercive_bilinearComp hcoeff hcoercive).norm_solutionWithLifting_sub_le hC
    (fun w => by simpa only [energyFormH1L_apply, Submodule.subtypeL_apply] using hlower w) g ℓ
  rw [← mixedSolutionL_eq] at h
  refine h.trans ?_
  -- The inclusion `H¹_Γ(Ω) → H¹(Ω)` has norm at most one.
  calc ‖(W1pVanishingOn mu Omega 2 Γ).subtypeL‖ *
        ((‖ℓ‖ + ‖energyFormH1L hcoeff‖ * ‖g‖ * ‖(W1pVanishingOn mu Omega 2 Γ).subtypeL‖) / C)
      ≤ 1 * ((‖ℓ‖ + ‖energyFormH1L hcoeff‖ * ‖g‖ * 1) / C) := by
        gcongr <;> exact Submodule.norm_subtypeL_le _
    _ = (‖ℓ‖ + ‖energyFormH1L hcoeff‖ * ‖g‖) / C := by ring

/-- **The solution of the mixed problem depends boundedly on the data**:
`‖u‖ ≤ ‖g‖ + (‖ℓ‖ + ‖B‖ ‖g‖) / C` for a coercivity constant `C`. -/
theorem norm_mixedSolutionL_apply_le (g : W1p mu Omega 2)
    (ℓ : StrongDual ℝ (W1pVanishingOn mu Omega 2 Γ)) :
    ‖mixedSolutionL hcoeff hcoercive (g, ℓ)‖ ≤
      ‖g‖ + (‖ℓ‖ + ‖energyFormH1L hcoeff‖ * ‖g‖) / C := by
  calc _ ≤ ‖mixedSolutionL hcoeff hcoercive (g, ℓ) - g‖ + ‖g‖ := norm_le_norm_sub_add _ _
    _ ≤ _ := by linarith [norm_mixedSolutionL_sub_le hcoeff hcoercive hC hlower g ℓ]

omit hC hlower

/-! ### Sources of coercivity -/

namespace IsUniformlyEllipticAE

variable [DecidableEq ι] {lam Lam : ℝ}

/-- **Coercivity on `H¹_Γ(Ω)` from a mass floor, for an inverse-coercive principal coefficient.**
For a measurable inverse-coercive principal coefficient `a` with lower constant `λ`, a drift
vanishing almost everywhere on `Ω` and an essentially bounded mass coefficient with `c ≥ δ > 0`
almost everywhere on `Ω`, the energy form is coercive on `H¹_Γ(Ω)` for every `Γ`, with constant
`min λ δ`. -/
theorem isCoercive_energyFormH1LVanishingOn_of_mass_lower_bound {delta : ℝ}
    (h : IsUniformlyEllipticAE mu (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hc : MemLp c ⊤ (mu.restrict Omega)) (hb : b =ᵐ[mu.restrict Omega] 0) (hdelta : 0 < delta)
    (hc_lower : ∀ᵐ x ∂mu.restrict Omega, delta ≤ c x)
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega)) :
    IsCoercive (energyFormH1LVanishingOn hcoeff Γ) :=
  isCoercive_energyFormH1LVanishingOn hcoeff (lt_min h.pos hdelta) fun w =>
    h.min_mul_norm_sq_le_energyFormH1_self_of_zero_drift ha hcoeff hc hb hc_lower
      (w : W1p mu Omega 2)

/-- **Coercivity on `H¹_Γ(Ω)` from a Poincaré–Friedrichs inequality, for an inverse-coercive
principal coefficient.** For a measurable inverse-coercive principal coefficient `a` with lower
constant `λ`, a drift vanishing almost everywhere on `Ω` and an essentially bounded mass
coefficient `c ≥ 0` almost everywhere on `Ω`, if `‖u‖_{L²} ≤ P ‖∇u‖_{L²}` for every
`u ∈ H¹_Γ(Ω)`, the energy form is coercive on `H¹_Γ(Ω)` with constant `λ / (P² + 1)`. -/
theorem isCoercive_energyFormH1LVanishingOn_of_poincare {P : ℝ}
    (h : IsUniformlyEllipticAE mu (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hc : MemLp c ⊤ (mu.restrict Omega)) (hb : b =ᵐ[mu.restrict Omega] 0)
    (hc_nonneg : ∀ᵐ x ∂mu.restrict Omega, 0 ≤ c x)
    (hP : ∀ u ∈ w1pVanishingOnSubmodule mu Omega 2 Γ, ‖W1p.value u‖ ≤ P * ‖W1p.gradient u‖)
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega)) :
    IsCoercive (energyFormH1LVanishingOn hcoeff Γ) :=
  isCoercive_energyFormH1LVanishingOn hcoeff (div_pos h.pos (by positivity)) fun w =>
    h.div_mul_norm_sq_le_energyFormH1_self_of_zero_drift ha hcoeff hc hb hc_nonneg
      (hP _ w.property)

end IsUniformlyEllipticAE

namespace UniformlyEllipticOn

variable [DecidableEq ι] {lam Lam gamma : ℝ}

/-- **Coercivity on `H¹_Γ(Ω)` from a mass floor.** For a uniformly elliptic principal
coefficient with constant `λ`, no drift and a mass coefficient with `0 < δ ≤ c` on `Ω`, the energy
form is coercive on `H¹_Γ(Ω)` for every `Γ`, with constant `min λ δ`. -/
theorem isCoercive_energyFormH1LVanishingOn_of_mass_lower_bound {delta : ℝ}
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (hb_zero : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), b x = 0)
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma)
    (hdelta : 0 < delta) (hc_lower : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), delta ≤ c x)
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega)) :
    IsCoercive (energyFormH1LVanishingOn hcoeff Γ) :=
  have hmem := ae_restrict_mem (μ := mu) Omega.isOpen.measurableSet
  (h.isUniformlyEllipticAE Omega.isOpen.measurableSet.nullMeasurableSet
    ).isCoercive_energyFormH1LVanishingOn_of_mass_lower_bound ha
    (memLp_top_of_bound hc gamma (hmem.mono hc_bound)) (hmem.mono hb_zero) hdelta
    (hmem.mono hc_lower) hcoeff

/-- **Coercivity on `H¹_Γ(Ω)` from a Poincaré–Friedrichs inequality.** For a uniformly elliptic
principal coefficient with constant `λ`, no drift and a bounded mass coefficient `c ≥ 0`, if
`‖u‖_{L²} ≤ P ‖∇u‖_{L²}` for every `u ∈ H¹_Γ(Ω)`, the energy form is coercive on `H¹_Γ(Ω)` with
constant `λ / (P² + 1)`. -/
theorem isCoercive_energyFormH1LVanishingOn_of_poincare {P : ℝ}
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (hb_zero : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), b x = 0)
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma)
    (hc_nonneg : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), 0 ≤ c x)
    (hP : ∀ u ∈ w1pVanishingOnSubmodule mu Omega 2 Γ, ‖W1p.value u‖ ≤ P * ‖W1p.gradient u‖)
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega)) :
    IsCoercive (energyFormH1LVanishingOn hcoeff Γ) :=
  have hmem := ae_restrict_mem (μ := mu) Omega.isOpen.measurableSet
  (h.isUniformlyEllipticAE Omega.isOpen.measurableSet.nullMeasurableSet
    ).isCoercive_energyFormH1LVanishingOn_of_poincare ha
    (memLp_top_of_bound hc gamma (hmem.mono hc_bound)) (hmem.mono hb_zero)
    (hmem.mono hc_nonneg) hP hcoeff

end UniformlyEllipticOn

end Domain

/-! ### Lipschitz domains -/

section Lipschitz

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {V : Opens (WithLp 2 (ℝ × E))} {L : ℝ≥0}
  {ι : Type*} [Fintype ι] [DecidableEq ι] {Omega : Opens (EuclideanSpace ℝ ι)}
  {Γ : Set (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
  {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {c : EuclideanSpace ℝ ι → ℝ} {lam Lam : ℝ}

namespace IsUniformlyEllipticAE

/-- **Coercivity of the mixed problem on a Lipschitz domain.** Let an affine isometry `e` carry
the connected open set `Ω ⊆ EuclideanSpace ℝ ι` onto a bounded Lipschitz domain `V`, and let `Γ`
meet the frontier of `Ω` in a set of positive surface measure. For a measurable inverse-coercive
principal coefficient `a` with lower constant `λ`, a drift vanishing almost everywhere, and an
essentially bounded mass coefficient `c ≥ 0`, the energy form is coercive on `H¹_Γ(Ω)`, with
constant `λ / (1 + P²)` for a Poincaré–Friedrichs constant `P` of `(Ω, Γ)`. -/
theorem isCoercive_energyFormH1LVanishingOn_of_isLipschitzDomainWith
    (h : IsUniformlyEllipticAE volume (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (volume.restrict Omega))
    (hc : MemLp c ⊤ (volume.restrict Omega)) (hb : b =ᵐ[volume.restrict Omega] 0)
    (hc_nonneg : ∀ᵐ x ∂volume.restrict Omega, 0 ≤ c x)
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (volume.restrict Omega))
    (hV : (V : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hVb : Bornology.IsBounded (V : Set (WithLp 2 (ℝ × E))))
    (e : EuclideanSpace ℝ ι ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E))
    (hVΩ : (V : Set (WithLp 2 (ℝ × E))) = e.symm ⁻¹' Omega)
    (hconn : IsPreconnected (Omega : Set (EuclideanSpace ℝ ι)))
    (hΓ : (μHE[finrank ℝ E] : Measure (EuclideanSpace ℝ ι))
      (Γ ∩ frontier (Omega : Set (EuclideanSpace ℝ ι))) ≠ 0) :
    IsCoercive (energyFormH1LVanishingOn hcoeff Γ) := by
  obtain ⟨P, -, hP⟩ :=
    W1p.exists_norm_value_le_mul_norm_gradient_of_mem_w1pVanishingOnSubmodule_of_affineIsometryEquiv
      (p := 2) ENNReal.ofNat_ne_top hV hVb e hVΩ hconn hΓ
  exact h.isCoercive_energyFormH1LVanishingOn_of_poincare ha hc hb hc_nonneg hP hcoeff

/-- **The mixed problem on a Lipschitz domain.** Let an affine isometry `e` carry the connected
open set `Ω ⊆ EuclideanSpace ℝ ι` onto a bounded Lipschitz domain `V`, and let `Γ` meet the
frontier of `Ω` in a set of positive surface measure. For a measurable inverse-coercive principal
coefficient `a`, a drift vanishing almost everywhere and an essentially bounded mass coefficient
`c ≥ 0`, every Dirichlet datum `g ∈ H¹(Ω)` and every forcing `ℓ ∈ (H¹_Γ(Ω))*`, there is exactly
one `u ∈ H¹(Ω)` with `u - g ∈ H¹_Γ(Ω)` and

`∫_Ω ⟨a ∇u, ∇v⟩ + c u v = ℓ v` for every `v ∈ H¹_Γ(Ω)`. -/
theorem existsUnique_sub_mem_w1pVanishingOnSubmodule_forall_energyFormH1_eq_of_isLipschitzDomainWith
    (h : IsUniformlyEllipticAE volume (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (volume.restrict Omega))
    (hc : MemLp c ⊤ (volume.restrict Omega)) (hb : b =ᵐ[volume.restrict Omega] 0)
    (hc_nonneg : ∀ᵐ x ∂volume.restrict Omega, 0 ≤ c x)
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (volume.restrict Omega))
    (hV : (V : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hVb : Bornology.IsBounded (V : Set (WithLp 2 (ℝ × E))))
    (e : EuclideanSpace ℝ ι ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E))
    (hVΩ : (V : Set (WithLp 2 (ℝ × E))) = e.symm ⁻¹' Omega)
    (hconn : IsPreconnected (Omega : Set (EuclideanSpace ℝ ι)))
    (hΓ : (μHE[finrank ℝ E] : Measure (EuclideanSpace ℝ ι))
      (Γ ∩ frontier (Omega : Set (EuclideanSpace ℝ ι))) ≠ 0)
    (g : W1p volume Omega 2) (ℓ : StrongDual ℝ (W1pVanishingOn volume Omega 2 Γ)) :
    ∃! u : W1p volume Omega 2, u - g ∈ w1pVanishingOnSubmodule volume Omega 2 Γ ∧
      ∀ v : W1pVanishingOn volume Omega 2 Γ, energyFormH1 a b c u v = ℓ v :=
  existsUnique_sub_mem_w1pVanishingOnSubmodule_forall_energyFormH1_eq hcoeff
    (h.isCoercive_energyFormH1LVanishingOn_of_isLipschitzDomainWith ha hc hb hc_nonneg hcoeff hV
      hVb e hVΩ hconn hΓ) g ℓ

/-- **Dirichlet's principle for the mixed problem on a Lipschitz domain.** Let an affine isometry
`e` carry the connected open set `Ω ⊆ EuclideanSpace ℝ ι` onto a bounded Lipschitz domain `V`, and
let `Γ` meet the frontier of `Ω` in a set of positive surface measure. For a measurable
inverse-coercive principal coefficient `a`, symmetric almost everywhere, a drift vanishing almost
everywhere and an essentially bounded mass coefficient `c ≥ 0`, every Dirichlet datum
`g ∈ H¹(Ω)` and every forcing `ℓ ∈ (H¹_Γ(Ω))*`, the energy

`J(w) = (∫_Ω ⟨a ∇(g + w), ∇(g + w)⟩ + c (g + w)²) / 2 - ℓ w`

has exactly one minimizer `w₀` on `H¹_Γ(Ω)`, and `g + w₀` is the solution of the mixed problem
(`TauCeti.PDE.isMinOn_iff_mixedSolutionL_eq`). -/
theorem existsUnique_w1pVanishingOn_isMinOn_energyFormH1_of_isLipschitzDomainWith
    (h : IsUniformlyEllipticAE volume (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (volume.restrict Omega))
    (ha_symm : ∀ᵐ x ∂volume.restrict Omega, (a x).IsSymm)
    (hc : MemLp c ⊤ (volume.restrict Omega)) (hb : b =ᵐ[volume.restrict Omega] 0)
    (hc_nonneg : ∀ᵐ x ∂volume.restrict Omega, 0 ≤ c x)
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (volume.restrict Omega))
    (hV : (V : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hVb : Bornology.IsBounded (V : Set (WithLp 2 (ℝ × E))))
    (e : EuclideanSpace ℝ ι ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E))
    (hVΩ : (V : Set (WithLp 2 (ℝ × E))) = e.symm ⁻¹' Omega)
    (hconn : IsPreconnected (Omega : Set (EuclideanSpace ℝ ι)))
    (hΓ : (μHE[finrank ℝ E] : Measure (EuclideanSpace ℝ ι))
      (Γ ∩ frontier (Omega : Set (EuclideanSpace ℝ ι))) ≠ 0)
    (g : W1p volume Omega 2) (ℓ : StrongDual ℝ (W1pVanishingOn volume Omega 2 Γ)) :
    ∃! w₀ : W1pVanishingOn volume Omega 2 Γ, IsMinOn (fun w : W1pVanishingOn volume Omega 2 Γ =>
      energyFormH1 a b c (g + (w : W1p volume Omega 2)) (g + (w : W1p volume Omega 2)) / 2 - ℓ w)
        univ w₀ := by
  -- With the drift replaced by `0`, almost everywhere symmetry of `a` makes the form symmetric.
  have hsymm (u v : W1p volume Omega 2) : energyFormH1 a b c u v = energyFormH1 a b c v u := by
    rw [energyFormH1_congr_ae .rfl hb .rfl, energyFormH1_congr_ae .rfl hb .rfl v,
      energyFormH1_comm_of_isSymm_ae ha_symm]
  exact existsUnique_w1pVanishingOn_isMinOn_energyFormH1 hcoeff
    (h.isCoercive_energyFormH1LVanishingOn_of_isLipschitzDomainWith ha hc hb hc_nonneg hcoeff hV
      hVb e hVΩ hconn hΓ) hsymm g ℓ

end IsUniformlyEllipticAE

end Lipschitz

end PDE

end TauCeti

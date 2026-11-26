/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Variational.Compatibility
public import TauCeti.Analysis.InnerProductSpace.Variational.Fredholm
public import TauCeti.Analysis.PDE.DirichletProblem
public import TauCeti.Analysis.Sobolev.RellichKondrachov

/-!
# The Fredholm alternative for the Dirichlet problem

Let `B` be the bounded energy form of a divergence-form operator on `H¹₀(Ω)`, and first suppose
that `B` is coercive.  Shifting its mass coefficient by a constant `-κ` changes the weak
equation to

`B(u, v) - κ ⟪u, v⟫_{L²} = ⟪f, v⟫_{L²}`.

When `Ω` is bounded, Rellich--Kondrachov makes the value inclusion
`H¹₀(Ω) → L²(Ω)` compact.  The abstract variational Fredholm alternative therefore gives the
classical dichotomy: either the homogeneous shifted problem has a nonzero solution, or every
`L²` forcing has a unique weak solution.  The homogeneous solution space is always finite
dimensional.

This is the compact-resolvent step of the Fredholm theory.  The unshifted coercive form `B` can
itself contain bounded measurable principal, drift, and mass coefficients; only the additional
perturbation is the scalar mass shift.  This is the standard reduction of a Gårding form to a
coercive form by adding a sufficiently large constant.

More generally, drop coercivity and let the energy form satisfy **Gårding's inequality**
`C₀‖w‖²_{H¹} ≤ B(w, w) + β‖w‖²_{L²}` on `H¹₀(Ω)`, with `C₀ > 0` and no sign condition on `β`.
Then for every `ℓ ∈ H⁻¹(Ω)` the weak problem `B(u, ·) = ℓ` is solvable exactly when `ℓ`
vanishes on the **weak adjoint kernel** `{w ∈ H¹₀(Ω) | ∀ v, B(v, w) = 0}`, the space of weak
solutions of the homogeneous adjoint problem; for `L²` forcing `f` the condition reads
`∫_Ω f w = 0`. For a non-symmetric principal coefficient or a nonzero drift the adjoint kernel
differs from the kernel `{u | ∀ v, B(u, v) = 0}`, but the two have the same finite dimension.
So if the homogeneous problem has only the trivial solution, every problem `B(u, ·) = ℓ` has
exactly one solution, although `B` need not be coercive. Every uniformly elliptic operator with
bounded measurable coefficients satisfies Gårding's inequality on a bounded domain.

For boundary values `g ∈ H¹(Ω)`, the problem `B(u, ·) = ℓ` with `u - g ∈ H¹₀(Ω)` is the problem
`B(w, ·) = ℓ - B(g, ·)` for `w = u - g ∈ H¹₀(Ω)`, so it is solvable exactly when `ℓ w = B(g, w)`
for every `w` in the adjoint kernel. Its solution set, when nonempty, is a translate of the kernel
`{w ∈ H¹₀(Ω) | ∀ v, B(w, v) = 0}`: solutions are unique up to this finite-dimensional space.

Boundedness of `Ω` enters only through the compactness of `H¹₀(Ω) → L²(Ω)`. On `ℝⁿ`, `n ≤ 2`, the
Laplacian satisfies Gårding's inequality and has zero adjoint kernel, yet `-Δu = f` has no
solution `u ∈ H¹(ℝⁿ)` when `∫ f ≠ 0`
(`TauCeti/Analysis/PDE/FredholmAlternative/WholeSpace.lean`).

## Main declarations

* `TauCeti.PDE.dirichletMassOperator`: the operator representing the `L²` mass form relative to
  the coercive energy form; `TauCeti.PDE.isCompactOperator_dirichletMassOperator` proves it compact
  on bounded domains.
* `TauCeti.PDE.IsWeakSolutionDirichletMassShift`: the weak equation with scalar mass shift.
* `TauCeti.PDE.finiteDimensional_ker_one_sub_smul_dirichletMassOperator`: finite dimensionality
  of its homogeneous solution space.
* `TauCeti.PDE.fredholmAlternative_isWeakSolutionDirichlet_sub_const`: the Fredholm dichotomy
  for the operator with mass coefficient `c - κ`.
* `TauCeti.PDE.exists_forall_energyFormH1L0_eq_iff_of_garding` and
  `TauCeti.PDE.exists_isWeakSolutionDirichlet_iff_of_garding`: the compatibility condition for
  `H⁻¹` and for `L²` forcing.
* `TauCeti.PDE.finiteDimensional_ker_energyFormH1L0_of_garding` and
  `TauCeti.PDE.finrank_ker_flip_energyFormH1L0_eq_of_garding`: the kernel and the adjoint kernel
  are finite dimensional of the same dimension.
* `TauCeti.PDE.existsUnique_forall_energyFormH1L0_eq_of_garding`: unique solvability when the
  homogeneous problem has only the trivial solution.
* `TauCeti.PDE.setOf_sub_mem_w1p0Submodule_forall_energyFormH1_eq_eq_vadd`: the solutions with
  prescribed boundary values form a translate of the kernel.
* `TauCeti.PDE.exists_sub_mem_w1p0Submodule_forall_energyFormH1_eq_iff_of_garding` and
  `TauCeti.PDE.existsUnique_sub_mem_w1p0Submodule_forall_energyFormH1_eq_of_garding`: the
  compatibility condition and unique solvability with boundary values `g ∈ H¹(Ω)`.
* `TauCeti.PDE.UniformlyEllipticOn.exists_forall_energyFormH1_eq_iff` and
  `TauCeti.PDE.UniformlyEllipticOn.existsUnique_forall_energyFormH1_eq`: the same two statements
  for every uniformly elliptic operator with bounded measurable coefficients, and
  `TauCeti.PDE.UniformlyEllipticOn.exists_sub_mem_w1p0Submodule_forall_energyFormH1_eq_iff` and
  `TauCeti.PDE.UniformlyEllipticOn.existsUnique_sub_mem_w1p0Submodule_forall_energyFormH1_eq`,
  their versions with boundary values.

## References

L. C. Evans, *Partial Differential Equations*, Section 6.2.3; D. Gilbarg and N. Trudinger,
*Elliptic Partial Differential Equations of Second Order*, Chapter 8, Theorems 8.3 and 8.6.
-/

public section

noncomputable section

namespace TauCeti

namespace PDE

open Bornology MeasureTheory Module Set TopologicalSpace
open scoped ENNReal InnerProductSpace

variable {ι : Type*} [Fintype ι] {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
  {Omega : Opens (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
  {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
  {c : EuclideanSpace ℝ ι → ℝ}

attribute [local instance] W1p0.instNormedAddCommGroup W1p0.instInnerProductSpace

/-- The Lax--Milgram operator representing the `L²` mass form on `H¹₀(Ω)`.  It is characterized
by `TauCeti.PDE.energyFormH1_dirichletMassOperator`. -/
def dirichletMassOperator
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hcoercive : IsCoercive (energyFormH1L0 hcoeff)) :
    W1p0 mu Omega 2 →L[ℝ] W1p0 mu Omega 2 :=
  hcoercive.formPerturbationOperator W1p0.valueL

/-- The Dirichlet mass operator represents the `L²` inner product relative to the base energy
form. -/
@[simp]
theorem energyFormH1_dirichletMassOperator
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hcoercive : IsCoercive (energyFormH1L0 hcoeff)) (u v : W1p0 mu Omega 2) :
    energyFormH1 a b c (dirichletMassOperator hcoeff hcoercive u : W1p mu Omega 2)
        (v : W1p mu Omega 2) =
      ⟪W1p.value (u : W1p mu Omega 2), W1p.value (v : W1p mu Omega 2)⟫_ℝ := by
  unfold dirichletMassOperator
  rw [← energyFormH1L0_apply hcoeff, hcoercive.apply_formPerturbationOperator, W1p0.valueL_apply,
    W1p0.valueL_apply]

/-- On a bounded domain, the Dirichlet mass operator is compact by Rellich--Kondrachov. -/
theorem isCompactOperator_dirichletMassOperator
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hcoercive : IsCoercive (energyFormH1L0 hcoeff))
    (hOmega : IsBounded (Omega : Set (EuclideanSpace ℝ ι))) :
    IsCompactOperator (dirichletMassOperator hcoeff hcoercive) := by
  apply hcoercive.isCompactOperator_formPerturbationOperator
  exact W1p0.isCompactOperator_valueL (by simp) hOmega

/-- The weak Dirichlet equation obtained by shifting the base operator's mass coefficient by the
constant `-κ`.  It says `B(u,v) - κ⟪u,v⟫_{L²} = ⟪f,v⟫_{L²}` for every
`v ∈ H¹₀(Ω)`. -/
def IsWeakSolutionDirichletMassShift (a : EuclideanSpace ℝ ι → Matrix ι ι ℝ)
    (b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) (c : EuclideanSpace ℝ ι → ℝ)
    (kappa : ℝ) (f : Lp ℝ 2 (mu.restrict Omega)) (u : W1p0 mu Omega 2) : Prop :=
  ∀ v : W1p0 mu Omega 2,
    energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) -
        kappa * ⟪W1p.value (u : W1p mu Omega 2), W1p.value (v : W1p mu Omega 2)⟫_ℝ =
      dirichletForcing f v

/-- Being a mass-shifted weak solution, written out as the integral identity
`B(u, v) - κ⟪u, v⟫_{L²} = ∫_Ω f v`. -/
@[simp]
theorem isWeakSolutionDirichletMassShift_iff (kappa : ℝ)
    (f : Lp ℝ 2 (mu.restrict Omega)) (u : W1p0 mu Omega 2) :
    IsWeakSolutionDirichletMassShift a b c kappa f u ↔
      ∀ v : W1p0 mu Omega 2,
        energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) -
            kappa * ⟪W1p.value (u : W1p mu Omega 2), W1p.value (v : W1p mu Omega 2)⟫_ℝ =
          ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu := by
  simp only [IsWeakSolutionDirichletMassShift, dirichletForcing_apply_eq_setIntegral]

/-- A zero mass shift recovers the unshifted Dirichlet weak equation.

This named specialization is not a simp lemma because
`isWeakSolutionDirichletMassShift_iff` already reduces its left-hand side; registering both
lemmas would violate the `simpNF` linter. -/
theorem isWeakSolutionDirichletMassShift_zero_iff (f : Lp ℝ 2 (mu.restrict Omega))
    (u : W1p0 mu Omega 2) :
    IsWeakSolutionDirichletMassShift a b c 0 f u ↔ IsWeakSolutionDirichlet a b c f u := by
  rw [isWeakSolutionDirichletMassShift_iff, isWeakSolutionDirichlet_iff]
  simp only [zero_mul, sub_zero]

/-- For essentially bounded energy coefficients, the mass-shifted equation is the usual weak
Dirichlet equation with mass coefficient `c - κ`. -/
theorem isWeakSolutionDirichletMassShift_iff_isWeakSolutionDirichlet_sub_const
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (kappa : ℝ) (f : Lp ℝ 2 (mu.restrict Omega)) (u : W1p0 mu Omega 2) :
    IsWeakSolutionDirichletMassShift a b c kappa f u ↔
      IsWeakSolutionDirichlet a b (fun x ↦ c x - kappa) f u := by
  simp only [isWeakSolutionDirichletMassShift_iff, isWeakSolutionDirichlet_iff,
    energyFormH1_mass_sub_const hcoeff]

/-- The mass-shifted weak equation written as an operator equation on `H¹₀(Ω)`. -/
theorem isWeakSolutionDirichletMassShift_iff_operator_eq
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hcoercive : IsCoercive (energyFormH1L0 hcoeff)) (kappa : ℝ)
    (f : Lp ℝ 2 (mu.restrict Omega)) (u : W1p0 mu Omega 2) :
    IsWeakSolutionDirichletMassShift a b c kappa f u ↔
      (1 - kappa • dirichletMassOperator hcoeff hcoercive :
          W1p0 mu Omega 2 →L[ℝ] W1p0 mu Omega 2) u =
        weakSolutionDirichlet hcoeff hcoercive f := by
  have habstract :
      IsWeakSolutionDirichletMassShift a b c kappa f u ↔
        (1 - kappa • dirichletMassOperator hcoeff hcoercive :
            W1p0 mu Omega 2 →L[ℝ] W1p0 mu Omega 2) u =
          hcoercive.solutionOfFunctional (dirichletForcing f) := by
    unfold dirichletMassOperator
    simpa only [IsWeakSolutionDirichletMassShift, energyFormH1L0_apply, W1p0.valueL_apply] using
      (hcoercive.one_sub_smul_formPerturbationOperator_apply_eq_iff_functional
        (W1p0.valueL (mu := mu) (Omega := Omega) (p := 2)) kappa (dirichletForcing f) u).symm
  have hsolution :
      weakSolutionDirichlet hcoeff hcoercive f =
        hcoercive.solutionOfFunctional (dirichletForcing f) :=
    hcoercive.eq_solutionOfFunctional fun v => by
    rw [energyFormH1L0_apply, dirichletForcing_apply_eq_setIntegral]
    exact (isWeakSolutionDirichlet_iff f _).mp
      (isWeakSolutionDirichlet_weakSolutionDirichlet hcoeff hcoercive f) v
  constructor
  · exact fun h => (habstract.mp h).trans hsolution.symm
  · exact fun h => habstract.mpr (h.trans hsolution)

/-- The homogeneous solution space of a scalar mass shift of a coercive Dirichlet form is finite
dimensional on a bounded domain. -/
theorem finiteDimensional_ker_one_sub_smul_dirichletMassOperator
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hcoercive : IsCoercive (energyFormH1L0 hcoeff))
    (hOmega : IsBounded (Omega : Set (EuclideanSpace ℝ ι)))
    (kappa : ℝ) :
    FiniteDimensional ℝ
      (LinearMap.ker
        ((1 - kappa • dirichletMassOperator hcoeff hcoercive :
          W1p0 mu Omega 2 →L[ℝ] W1p0 mu Omega 2) :
            W1p0 mu Omega 2 →ₗ[ℝ] W1p0 mu Omega 2)) :=
  hcoercive.finiteDimensional_ker_one_sub_smul_formPerturbationOperator
    (W1p0.isCompactOperator_valueL (by simp) hOmega) kappa

/-- **The Fredholm alternative for the mass-shifted Dirichlet problem.** On a bounded domain,
the operator with mass coefficient `c - κ` either has a nonzero homogeneous weak solution, or
admits a unique weak solution for every `L²` forcing. -/
theorem fredholmAlternative_isWeakSolutionDirichlet_sub_const
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hcoercive : IsCoercive (energyFormH1L0 hcoeff))
    (hOmega : IsBounded (Omega : Set (EuclideanSpace ℝ ι)))
    (kappa : ℝ) :
    (∃ u : W1p0 mu Omega 2, u ≠ 0 ∧
      IsWeakSolutionDirichlet a b (fun x ↦ c x - kappa) 0 u) ∨
      ∀ f : Lp ℝ 2 (mu.restrict Omega),
        ∃! u : W1p0 mu Omega 2,
          IsWeakSolutionDirichlet a b (fun x ↦ c x - kappa) f u := by
  simp only [← isWeakSolutionDirichletMassShift_iff_isWeakSolutionDirichlet_sub_const hcoeff]
  rcases hcoercive.fredholmAlternative_formPerturbation
      (W1p0.isCompactOperator_valueL (by simp) hOmega) kappa with hkernel | hunique
  · left
    obtain ⟨u, hune, hu⟩ := hkernel
    refine ⟨u, hune, fun v => ?_⟩
    simpa only [energyFormH1L0_apply, W1p0.valueL_apply, dirichletForcing_apply, inner_zero_left]
      using hu v
  · right
    intro f
    obtain ⟨u, hu, huniq⟩ := hunique (dirichletForcing f)
    refine ⟨u, fun v => ?_, fun y hy => huniq y fun v => ?_⟩
    · simpa only [energyFormH1L0_apply, W1p0.valueL_apply] using hu v
    · simpa only [energyFormH1L0_apply, W1p0.valueL_apply] using hy v

/-! ### The structure of the solution set -/

open scoped Pointwise in
/-- **The solution set is a translate of the kernel.** Let `u₀ ∈ H¹(Ω)` solve `B(u₀, ·) = ℓ` on
`H¹₀(Ω)` with boundary values `g`, that is `u₀ - g ∈ H¹₀(Ω)`. Then the solutions `u` with the same
boundary values are exactly the functions `u₀ + w` with `w` in the kernel
`{w ∈ H¹₀(Ω) | ∀ v, B(w, v) = 0}` of weak solutions of the homogeneous problem. So two solutions
differ by an element of the kernel, and the solution is unique when the kernel is zero. Nothing is
assumed about the coefficients beyond boundedness; under Gårding's inequality on a bounded set the
kernel is finite dimensional (`TauCeti.PDE.finiteDimensional_ker_energyFormH1L0_of_garding`). -/
theorem setOf_sub_mem_w1p0Submodule_forall_energyFormH1_eq_eq_vadd
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    {g u₀ : W1p mu Omega 2} {ℓ : StrongDual ℝ (W1p0 mu Omega 2)}
    (hu₀g : u₀ - g ∈ w1p0Submodule mu Omega 2)
    (hu₀ : ∀ v : W1p0 mu Omega 2, energyFormH1 a b c u₀ (v : W1p mu Omega 2) = ℓ v) :
    {u : W1p mu Omega 2 | u - g ∈ w1p0Submodule mu Omega 2 ∧
        ∀ v : W1p0 mu Omega 2, energyFormH1 a b c u (v : W1p mu Omega 2) = ℓ v} =
      u₀ +ᵥ ((energyFormH1L0 hcoeff).ker.map (W1p0 mu Omega 2).subtype :
        Set (W1p mu Omega 2)) := by
  -- `u` solves the problem exactly when `u - u₀` solves the homogeneous problem.
  have hsol (u : W1p mu Omega 2) :=
    forall_energyFormH1_eq_iff_forall_energyFormH1_sub_eq hcoeff u u₀ ℓ
  have hker (w : W1p0 mu Omega 2) : w ∈ (energyFormH1L0 hcoeff).ker ↔
      ∀ v : W1p0 mu Omega 2, energyFormH1 a b c (w : W1p mu Omega 2) (v : W1p mu Omega 2) = 0 := by
    simp [LinearMap.mem_ker, ContinuousLinearMap.ext_iff]
  ext u
  simp only [Set.mem_ofPred_eq, Set.mem_vadd_set, SetLike.mem_coe, Submodule.mem_map,
    Submodule.coe_subtype, vadd_eq_add]
  constructor
  · rintro ⟨hu, hu'⟩
    have hmem : u - u₀ ∈ W1p0 mu Omega 2 := by
      rw [← sub_sub_sub_cancel_right u u₀ g]
      exact sub_mem ((ClosedSubmodule.mem_toSubmodule_iff _ _).2 hu)
        ((ClosedSubmodule.mem_toSubmodule_iff _ _).2 hu₀g)
    refine ⟨u - u₀, ⟨⟨u - u₀, hmem⟩, (hker _).2 fun v => ?_, rfl⟩, add_sub_cancel u₀ u⟩
    rw [(hsol u).1 hu' v, hu₀ v, sub_self]
  · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    refine ⟨?_, (hsol _).2 fun v => ?_⟩
    · rw [add_sub_right_comm]
      exact add_mem hu₀g ((ClosedSubmodule.mem_toSubmodule_iff _ _).1 w.property)
    · rw [add_sub_cancel_left, (hker w).1 hw v, hu₀ v, sub_self]

/-! ### The compatibility condition under Gårding's inequality

The abstract theorems are applied with the Hilbert spaces `H¹₀(Ω)` and `L²(Ω)` named explicitly:
inferring them from the compact value map would make instance search unify the structures of
`H¹₀(Ω)` against metavariables, which times out. -/

section Garding

variable (hOmega : IsBounded (Omega : Set (EuclideanSpace ℝ ι)))
  (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
  {C₀ β : ℝ} (hC₀ : 0 < C₀)
  (hgarding : ∀ w : W1p0 mu Omega 2,
    C₀ * ‖w‖ ^ 2 ≤ energyFormH1L0 hcoeff w w + β * ‖W1p0.valueL w‖ ^ 2)
include hOmega hC₀ hgarding

/-- **The Fredholm compatibility condition for the Dirichlet problem.** On a bounded open set,
let the energy form `B` of `-∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u` satisfy Gårding's inequality
`C₀‖w‖²_{H¹} ≤ B(w, w) + β‖w‖²_{L²}` on `H¹₀(Ω)`, with `C₀ > 0`. For `ℓ ∈ H⁻¹(Ω)` the weak
problem `B(u, ·) = ℓ` has a solution `u ∈ H¹₀(Ω)` exactly when `ℓ` vanishes on the weak adjoint
kernel `{w | ∀ v, B(v, w) = 0}`. -/
theorem exists_forall_energyFormH1L0_eq_iff_of_garding (ℓ : StrongDual ℝ (W1p0 mu Omega 2)) :
    (∃ u : W1p0 mu Omega 2, ∀ v, energyFormH1L0 hcoeff u v = ℓ v) ↔
      ∀ w : W1p0 mu Omega 2, (∀ v, energyFormH1L0 hcoeff v w = 0) → ℓ w = 0 :=
  IsCompactOperator.exists_forall_apply_eq_iff_of_garding
    (V := W1p0 mu Omega 2) (H := Lp ℝ 2 (mu.restrict Omega))
    (W1p0.isCompactOperator_valueL (by simp) hOmega) hC₀ hgarding ℓ

/-- **The compatibility condition for `L²` forcing.** Under Gårding's inequality on a bounded
open set, the Dirichlet problem `L u = f` in `Ω`, `u = 0` on `∂Ω`, has a weak solution exactly
when `∫_Ω f w = 0` for every weak solution `w` of the homogeneous adjoint problem. -/
theorem exists_isWeakSolutionDirichlet_iff_of_garding (f : Lp ℝ 2 (mu.restrict Omega)) :
    (∃ u : W1p0 mu Omega 2, IsWeakSolutionDirichlet a b c f u) ↔
      ∀ w : W1p0 mu Omega 2,
        (∀ v : W1p0 mu Omega 2,
          energyFormH1 a b c (v : W1p mu Omega 2) (w : W1p mu Omega 2) = 0) →
        ∫ x in Omega, f x * W1p.value (w : W1p mu Omega 2) x ∂mu = 0 := by
  simpa only [isWeakSolutionDirichlet_iff, energyFormH1L0_apply,
    dirichletForcing_apply_eq_setIntegral] using
    exists_forall_energyFormH1L0_eq_iff_of_garding hOmega hcoeff hC₀ hgarding (dirichletForcing f)

/-- Under Gårding's inequality on a bounded open set, the weak solutions of the homogeneous
Dirichlet problem form a finite-dimensional space. -/
theorem finiteDimensional_ker_energyFormH1L0_of_garding :
    FiniteDimensional ℝ (energyFormH1L0 hcoeff).ker :=
  IsCompactOperator.finiteDimensional_ker_of_garding
    (V := W1p0 mu Omega 2) (H := Lp ℝ 2 (mu.restrict Omega))
    (W1p0.isCompactOperator_valueL (by simp) hOmega) hC₀ hgarding

/-- **The kernel and the adjoint kernel have the same dimension.** Under Gårding's inequality on
a bounded open set, the weak solutions `w` of the homogeneous adjoint problem, `B(v, w) = 0` for
every `v`, and the weak solutions `u` of the homogeneous problem, `B(u, v) = 0` for every `v`,
form spaces of the same finite dimension. -/
theorem finrank_ker_flip_energyFormH1L0_eq_of_garding :
    finrank ℝ (energyFormH1L0 hcoeff).flip.ker = finrank ℝ (energyFormH1L0 hcoeff).ker :=
  IsCompactOperator.finrank_ker_flip_eq_finrank_ker_of_garding
    (V := W1p0 mu Omega 2) (H := Lp ℝ 2 (mu.restrict Omega))
    (W1p0.isCompactOperator_valueL (by simp) hOmega) hC₀ hgarding

/-- **Uniqueness implies existence.** Under Gårding's inequality on a bounded open set, if the
homogeneous Dirichlet problem has only the trivial weak solution, then for every `ℓ ∈ H⁻¹(Ω)`
the weak problem `B(u, ·) = ℓ` has exactly one solution `u ∈ H¹₀(Ω)`. -/
theorem existsUnique_forall_energyFormH1L0_eq_of_garding
    (hker : ∀ u : W1p0 mu Omega 2, (∀ v, energyFormH1L0 hcoeff u v = 0) → u = 0)
    (ℓ : StrongDual ℝ (W1p0 mu Omega 2)) :
    ∃! u : W1p0 mu Omega 2, ∀ v, energyFormH1L0 hcoeff u v = ℓ v :=
  IsCompactOperator.existsUnique_forall_apply_eq_of_garding
    (V := W1p0 mu Omega 2) (H := Lp ℝ 2 (mu.restrict Omega))
    (W1p0.isCompactOperator_valueL (by simp) hOmega) hC₀ hgarding hker ℓ

/-- **The compatibility condition with boundary values.** Under Gårding's inequality on a bounded
open set, let `g ∈ H¹(Ω)` and `ℓ ∈ H⁻¹(Ω)`. The weak problem `B(u, ·) = ℓ` on `H¹₀(Ω)` with
boundary values `g`, that is `u - g ∈ H¹₀(Ω)`, has a solution `u ∈ H¹(Ω)` exactly when
`ℓ w = B(g, w)` for every `w` in the weak adjoint kernel `{w | ∀ v, B(v, w) = 0}`. This is the
compatibility condition for the functional `ℓ - B(g, ·)`, whose solutions `w ∈ H¹₀(Ω)` give the
solutions `u = g + w`. -/
theorem exists_sub_mem_w1p0Submodule_forall_energyFormH1_eq_iff_of_garding
    (g : W1p mu Omega 2) (ℓ : StrongDual ℝ (W1p0 mu Omega 2)) :
    (∃ u : W1p mu Omega 2, u - g ∈ w1p0Submodule mu Omega 2 ∧
        ∀ v : W1p0 mu Omega 2, energyFormH1 a b c u (v : W1p mu Omega 2) = ℓ v) ↔
      ∀ w : W1p0 mu Omega 2,
        (∀ v : W1p0 mu Omega 2,
          energyFormH1 a b c (v : W1p mu Omega 2) (w : W1p mu Omega 2) = 0) →
        ℓ w = energyFormH1 a b c g (w : W1p mu Omega 2) := by
  rw [exists_sub_mem_w1p0Submodule_forall_energyFormH1_eq_iff_exists_w1p0 hcoeff]
  simpa [sub_eq_zero] using exists_forall_energyFormH1L0_eq_iff_of_garding hOmega hcoeff hC₀
    hgarding (ℓ - (energyFormH1L hcoeff g).comp (W1p0 mu Omega 2).subtypeL)

/-- **Uniqueness implies existence, with boundary values.** Under Gårding's inequality on a bounded
open set, if the homogeneous Dirichlet problem has only the trivial weak solution, then for every
`g ∈ H¹(Ω)` and `ℓ ∈ H⁻¹(Ω)` there is exactly one `u ∈ H¹(Ω)` with `u - g ∈ H¹₀(Ω)` and
`B(u, v) = ℓ v` for every `v ∈ H¹₀(Ω)`. -/
theorem existsUnique_sub_mem_w1p0Submodule_forall_energyFormH1_eq_of_garding
    (hker : ∀ u : W1p0 mu Omega 2, (∀ v, energyFormH1L0 hcoeff u v = 0) → u = 0)
    (g : W1p mu Omega 2) (ℓ : StrongDual ℝ (W1p0 mu Omega 2)) :
    ∃! u : W1p mu Omega 2, u - g ∈ w1p0Submodule mu Omega 2 ∧
      ∀ v : W1p0 mu Omega 2, energyFormH1 a b c u (v : W1p mu Omega 2) = ℓ v :=
  (existsUnique_sub_mem_w1p0Submodule_forall_energyFormH1_eq_iff_existsUnique_w1p0
    hcoeff g ℓ).2 <| by
    simpa using existsUnique_forall_energyFormH1L0_eq_of_garding hOmega hcoeff hC₀ hgarding hker
      (ℓ - (energyFormH1L hcoeff g).comp (W1p0 mu Omega 2).subtypeL)

end Garding

namespace UniformlyEllipticOn

variable [DecidableEq ι] {lam Lam beta gamma : ℝ}

/-- Gårding's inequality for the bundled energy form of a uniformly elliptic operator with bounded
measurable coefficients, in the form consumed by the compatibility theorems. -/
private theorem garding_energyFormH1L0
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hb : AEStronglyMeasurable b (mu.restrict Omega))
    (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (hb_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b x‖ ≤ beta)
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma)
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (w : W1p0 mu Omega 2) :
    lam / 2 * ‖w‖ ^ 2 ≤ energyFormH1L0 hcoeff w w +
      (lam / 2 + gamma + beta ^ 2 / (2 * lam)) * ‖W1p0.valueL w‖ ^ 2 := by
  rw [energyFormH1L0_apply, W1p0.valueL_apply]
  exact sub_le_iff_le_add.mp (h.garding_energyFormH1_self_norm_of_norm_le ha hb hc hb_bound
    hc_bound w)

/-- **The Fredholm compatibility condition for uniformly elliptic operators.** On a bounded open
set, let `a` be uniformly elliptic and let `b` and `c` be bounded and measurable, with no sign
condition on `c` and no smallness of `b`. For `ℓ ∈ H⁻¹(Ω)` the weak problem `B(u, ·) = ℓ` for
`-∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u` has a solution `u ∈ H¹₀(Ω)` exactly when `ℓ` vanishes on the weak
adjoint kernel `{w | ∀ v, B(v, w) = 0}`. -/
theorem exists_forall_energyFormH1_eq_iff
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hb : AEStronglyMeasurable b (mu.restrict Omega))
    (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (hb_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b x‖ ≤ beta)
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma)
    (hOmega : IsBounded (Omega : Set (EuclideanSpace ℝ ι)))
    (ℓ : StrongDual ℝ (W1p0 mu Omega 2)) :
    (∃ u : W1p0 mu Omega 2, ∀ v : W1p0 mu Omega 2,
        energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) = ℓ v) ↔
      ∀ w : W1p0 mu Omega 2,
        (∀ v : W1p0 mu Omega 2,
          energyFormH1 a b c (v : W1p mu Omega 2) (w : W1p mu Omega 2) = 0) → ℓ w = 0 := by
  have hcoeff := memLp_energyIntegrand_of_bounds h.upper_nonneg ha hb hc
    (fun _x hx eta xi => h.upper_bound hx eta xi) hb_bound hc_bound
  simpa only [energyFormH1L0_apply] using
    exists_forall_energyFormH1L0_eq_iff_of_garding hOmega hcoeff (half_pos h.pos)
      (h.garding_energyFormH1L0 ha hb hc hb_bound hc_bound hcoeff) ℓ

/-- **Uniqueness implies existence for uniformly elliptic operators.** On a bounded open set, let
`a` be uniformly elliptic and let `b` and `c` be bounded and measurable. If the homogeneous
Dirichlet problem for `-∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u` has only the trivial weak solution, then for
every `ℓ ∈ H⁻¹(Ω)` the weak problem `B(u, ·) = ℓ` has exactly one solution `u ∈ H¹₀(Ω)`. -/
theorem existsUnique_forall_energyFormH1_eq
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hb : AEStronglyMeasurable b (mu.restrict Omega))
    (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (hb_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b x‖ ≤ beta)
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma)
    (hOmega : IsBounded (Omega : Set (EuclideanSpace ℝ ι)))
    (hker : ∀ u : W1p0 mu Omega 2,
      (∀ v : W1p0 mu Omega 2, energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) = 0) →
        u = 0)
    (ℓ : StrongDual ℝ (W1p0 mu Omega 2)) :
    ∃! u : W1p0 mu Omega 2, ∀ v : W1p0 mu Omega 2,
      energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) = ℓ v := by
  have hcoeff := memLp_energyIntegrand_of_bounds h.upper_nonneg ha hb hc
    (fun _x hx eta xi => h.upper_bound hx eta xi) hb_bound hc_bound
  simpa only [energyFormH1L0_apply] using
    existsUnique_forall_energyFormH1L0_eq_of_garding hOmega hcoeff (half_pos h.pos)
      (h.garding_energyFormH1L0 ha hb hc hb_bound hc_bound hcoeff)
      (by simpa only [energyFormH1L0_apply] using hker) ℓ

/-- **The compatibility condition with boundary values for uniformly elliptic operators.** On a
bounded open set, let `a` be uniformly elliptic and let `b` and `c` be bounded and measurable,
with no sign condition on `c` and no smallness of `b`. For `g ∈ H¹(Ω)` and `ℓ ∈ H⁻¹(Ω)` the
weak problem `L u = ℓ` in `Ω`, `u = g` on `∂Ω`, for `L u = -∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u`, has a
solution exactly when `ℓ w = B(g, w)` for every `w` in the weak adjoint kernel
`{w | ∀ v, B(v, w) = 0}`. -/
theorem exists_sub_mem_w1p0Submodule_forall_energyFormH1_eq_iff
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hb : AEStronglyMeasurable b (mu.restrict Omega))
    (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (hb_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b x‖ ≤ beta)
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma)
    (hOmega : IsBounded (Omega : Set (EuclideanSpace ℝ ι)))
    (g : W1p mu Omega 2) (ℓ : StrongDual ℝ (W1p0 mu Omega 2)) :
    (∃ u : W1p mu Omega 2, u - g ∈ w1p0Submodule mu Omega 2 ∧
        ∀ v : W1p0 mu Omega 2, energyFormH1 a b c u (v : W1p mu Omega 2) = ℓ v) ↔
      ∀ w : W1p0 mu Omega 2,
        (∀ v : W1p0 mu Omega 2,
          energyFormH1 a b c (v : W1p mu Omega 2) (w : W1p mu Omega 2) = 0) →
        ℓ w = energyFormH1 a b c g (w : W1p mu Omega 2) := by
  have hcoeff := memLp_energyIntegrand_of_bounds h.upper_nonneg ha hb hc
    (fun _x hx eta xi => h.upper_bound hx eta xi) hb_bound hc_bound
  exact exists_sub_mem_w1p0Submodule_forall_energyFormH1_eq_iff_of_garding hOmega hcoeff
    (half_pos h.pos) (h.garding_energyFormH1L0 ha hb hc hb_bound hc_bound hcoeff) g ℓ

/-- **Uniqueness implies existence for uniformly elliptic operators, with boundary values.** On a
bounded open set, let `a` be uniformly elliptic and let `b` and `c` be bounded and measurable. If
the homogeneous Dirichlet problem for `-∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u` has only the trivial weak
solution, then for every `g ∈ H¹(Ω)` and `ℓ ∈ H⁻¹(Ω)` there is exactly one `u ∈ H¹(Ω)` with
`u - g ∈ H¹₀(Ω)` and `B(u, v) = ℓ v` for every `v ∈ H¹₀(Ω)`. -/
theorem existsUnique_sub_mem_w1p0Submodule_forall_energyFormH1_eq
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hb : AEStronglyMeasurable b (mu.restrict Omega))
    (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (hb_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b x‖ ≤ beta)
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma)
    (hOmega : IsBounded (Omega : Set (EuclideanSpace ℝ ι)))
    (hker : ∀ u : W1p0 mu Omega 2,
      (∀ v : W1p0 mu Omega 2, energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) = 0) →
        u = 0)
    (g : W1p mu Omega 2) (ℓ : StrongDual ℝ (W1p0 mu Omega 2)) :
    ∃! u : W1p mu Omega 2, u - g ∈ w1p0Submodule mu Omega 2 ∧
      ∀ v : W1p0 mu Omega 2, energyFormH1 a b c u (v : W1p mu Omega 2) = ℓ v := by
  have hcoeff := memLp_energyIntegrand_of_bounds h.upper_nonneg ha hb hc
    (fun _x hx eta xi => h.upper_bound hx eta xi) hb_bound hc_bound
  exact existsUnique_sub_mem_w1p0Submodule_forall_energyFormH1_eq_of_garding hOmega hcoeff
    (half_pos h.pos) (h.garding_energyFormH1L0 ha hb hc hb_bound hc_bound hcoeff)
    (by simpa only [energyFormH1L0_apply] using hker) g ℓ

end UniformlyEllipticOn

end PDE

end TauCeti

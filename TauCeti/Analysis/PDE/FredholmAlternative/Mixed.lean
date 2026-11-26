/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Variational.Compatibility
public import TauCeti.Analysis.PDE.MixedProblem
import TauCeti.Analysis.Sobolev.LipschitzDomain.RellichKondrachov

/-!
# The Fredholm alternative for the mixed problem

Let `Ω` be an open set, `Γ` a set, typically a part of the boundary, and
`L u = -∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u` a divergence-form operator with bounded energy form `B`
(`TauCeti.PDE.energyFormH1`). The weak mixed problem asks, for `g ∈ H¹(Ω)` and
`ℓ ∈ (H¹_Γ(Ω))*`, for `u ∈ H¹(Ω)` with

`u - g ∈ H¹_Γ(Ω)` and `B(u, v) = ℓ v` for every `v ∈ H¹_Γ(Ω)`,

where `H¹_Γ(Ω)` is the space `TauCeti.W1pVanishingOn` of Sobolev functions vanishing on `Γ`; for
`Γ` the frontier this is the Dirichlet problem and for `Γ = ∅` the Neumann problem. The coercive
case is `TauCeti/Analysis/PDE/MixedProblem.lean`. This file drops coercivity.

Suppose that `B` satisfies **Gårding's inequality** `C₀‖w‖²_{H¹} ≤ B(w, w) + β‖w‖²_{L²}` on
`H¹_Γ(Ω)`, with `C₀ > 0` and no sign condition on `β`, and that the value map
`H¹_Γ(Ω) → L²(Ω)` is compact. This holds when `Ω` has the **Rellich property**, that the value map
`H¹(Ω) → L²(Ω)` is compact. Then the abstract variational Fredholm alternative
(`IsCompactOperator.exists_forall_apply_eq_iff_of_garding`) applies on the closed subspace
`H¹_Γ(Ω)`:

* `B(u, ·) = ℓ` has a solution `u ∈ g + H¹_Γ(Ω)` exactly when `ℓ w = B(g, w)` for every `w` in the
  **weak adjoint kernel** `{w ∈ H¹_Γ(Ω) | ∀ v ∈ H¹_Γ(Ω), B(v, w) = 0}`;
* the kernel `{w ∈ H¹_Γ(Ω) | ∀ v, B(w, v) = 0}` and the adjoint kernel are finite dimensional of
  the same dimension, and the solution set is a translate of the kernel;
* so if the homogeneous problem has only the trivial solution, the mixed problem has exactly one
  solution for every `g` and `ℓ`, although `B` need not be coercive.

No regularity of `Γ` is used, and `Γ` may meet `Ω`. Every uniformly elliptic operator with
bounded measurable coefficients satisfies Gårding's inequality on all of `H¹(Ω)`
(`TauCeti.PDE.UniformlyEllipticOn.garding_energyFormH1_self_norm_of_norm_le`), and so on every
`H¹_Γ(Ω)`. A bounded Lipschitz domain has the Rellich property
(`TauCeti.W1p.isCompactOperator_valueL_of_isLipschitzDomainWith_of_affineIsometryEquiv`), which
gives the Fredholm alternative for the mixed problem of every such operator on a bounded Lipschitz
domain. On a merely bounded open set the Rellich property can fail, which is why it is a
hypothesis here, rather than boundedness as in the Dirichlet case
(`TauCeti/Analysis/PDE/FredholmAlternative.lean`), where `H¹₀(Ω) → L²(Ω)` is always compact.

## Main declarations

* `TauCeti.PDE.setOf_sub_mem_w1pVanishingOnSubmodule_forall_energyFormH1_eq_eq_vadd`: the
  solutions with Dirichlet datum `g` on `Γ` form a translate of the kernel.
* `TauCeti.PDE.exists_forall_energyFormH1LVanishingOn_eq_iff_of_garding`: the compatibility
  condition on `H¹_Γ(Ω)`.
* `TauCeti.PDE.finiteDimensional_ker_energyFormH1LVanishingOn_of_garding` and
  `TauCeti.PDE.finrank_ker_flip_energyFormH1LVanishingOn_eq_of_garding`: the kernel and the
  adjoint kernel are finite dimensional of the same dimension.
* `TauCeti.PDE.existsUnique_forall_energyFormH1LVanishingOn_eq_of_garding`: unique solvability
  when the homogeneous problem has only the trivial solution.
* `TauCeti.PDE.exists_sub_mem_w1pVanishingOnSubmodule_forall_energyFormH1_eq_iff_of_garding` and
  `TauCeti.PDE.existsUnique_sub_mem_w1pVanishingOnSubmodule_forall_energyFormH1_eq_of_garding`:
  the same with a Dirichlet datum `g ∈ H¹(Ω)` on `Γ`.
* `exists_sub_mem_w1pVanishingOnSubmodule_forall_energyFormH1_eq_iff`,
  `finiteDimensional_ker_energyFormH1LVanishingOn` and
  `existsUnique_sub_mem_w1pVanishingOnSubmodule_forall_energyFormH1_eq`, in the namespace
  `TauCeti.PDE.UniformlyEllipticOn`: the statements for uniformly elliptic operators with
  bounded measurable coefficients, and the versions `..._of_isLipschitzDomainWith` of the first
  and last on an isometric copy of a bounded Lipschitz domain.

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
  Theorem 9.23 (the Fredholm alternative for the Dirichlet problem, whose proof carries over to
  `H¹_Γ(Ω)` with the compact inclusion `H¹(Ω) → L²(Ω)`).
* L. C. Evans, *Partial Differential Equations*, 2nd ed., §6.2.3, Theorem 4.
-/

public section

noncomputable section

namespace TauCeti

namespace PDE

open Bornology MeasureTheory Module Set TopologicalSpace
open scoped ENNReal NNReal InnerProductSpace

section Domain

variable {ι : Type*} [Fintype ι] {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
  {Omega : Opens (EuclideanSpace ℝ ι)} {Γ : Set (EuclideanSpace ℝ ι)}
  {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
  {c : EuclideanSpace ℝ ι → ℝ}

attribute [local instance] instSeminormedAddCommGroupW1p instNormedSpaceW1p
  W1pVanishingOn.instNormedAddCommGroup W1pVanishingOn.instInnerProductSpace

/-! ### The solution set -/

/-- Two functions with the same Dirichlet datum `g` on `Γ` differ by an element of `H¹_Γ(Ω)`. -/
private theorem sub_mem_w1pVanishingOnSubmodule_of_sub_mem {g u u₀ : W1p mu Omega 2}
    (hu : u - g ∈ w1pVanishingOnSubmodule mu Omega 2 Γ)
    (hu₀ : u₀ - g ∈ w1pVanishingOnSubmodule mu Omega 2 Γ) :
    u - u₀ ∈ w1pVanishingOnSubmodule mu Omega 2 Γ := by
  rw [← sub_sub_sub_cancel_right u u₀ g, ← ClosedSubmodule.mem_toSubmodule_iff]
  exact sub_mem ((ClosedSubmodule.mem_toSubmodule_iff _ _).2 hu)
    ((ClosedSubmodule.mem_toSubmodule_iff _ _).2 hu₀)

open scoped Pointwise in
/-- **The solution set of the mixed problem is a translate of the kernel.** Let `u₀ ∈ H¹(Ω)` solve
`B(u₀, ·) = ℓ` on `H¹_Γ(Ω)` with Dirichlet datum `g` on `Γ`, that is `u₀ - g ∈ H¹_Γ(Ω)`. Then
the solutions `u` with the same datum are exactly the functions `u₀ + w` with `w` in the kernel
`{w ∈ H¹_Γ(Ω) | ∀ v, B(w, v) = 0}` of weak solutions of the homogeneous problem. Nothing is
assumed about the coefficients beyond boundedness; under Gårding's inequality, with a compact
value map on `H¹_Γ(Ω)`, the kernel is finite dimensional
(`TauCeti.PDE.finiteDimensional_ker_energyFormH1LVanishingOn_of_garding`). -/
theorem setOf_sub_mem_w1pVanishingOnSubmodule_forall_energyFormH1_eq_eq_vadd
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    {g u₀ : W1p mu Omega 2} {ℓ : StrongDual ℝ (W1pVanishingOn mu Omega 2 Γ)}
    (hu₀g : u₀ - g ∈ w1pVanishingOnSubmodule mu Omega 2 Γ)
    (hu₀ : ∀ v : W1pVanishingOn mu Omega 2 Γ, energyFormH1 a b c u₀ v = ℓ v) :
    {u : W1p mu Omega 2 | u - g ∈ w1pVanishingOnSubmodule mu Omega 2 Γ ∧
        ∀ v : W1pVanishingOn mu Omega 2 Γ, energyFormH1 a b c u v = ℓ v} =
      u₀ +ᵥ ((energyFormH1LVanishingOn hcoeff Γ).ker.map
        (W1pVanishingOn mu Omega 2 Γ).subtype : Set (W1p mu Omega 2)) := by
  -- `u` solves the problem exactly when `u - u₀` solves the homogeneous problem.
  have hsol (u : W1p mu Omega 2) :
      (∀ v : W1pVanishingOn mu Omega 2 Γ, energyFormH1 a b c u v = ℓ v) ↔
        ∀ v : W1pVanishingOn mu Omega 2 Γ, energyFormH1 a b c (u - u₀) v = 0 :=
    forall_congr' fun v => by rw [energyFormH1_sub_left hcoeff, hu₀ v, sub_eq_zero]
  have hker (w : W1pVanishingOn mu Omega 2 Γ) : w ∈ (energyFormH1LVanishingOn hcoeff Γ).ker ↔
      ∀ v : W1pVanishingOn mu Omega 2 Γ, energyFormH1 a b c (w : W1p mu Omega 2) v = 0 := by
    simp [LinearMap.mem_ker, ContinuousLinearMap.ext_iff]
  ext u
  simp only [Set.mem_ofPred_eq, Set.mem_vadd_set, SetLike.mem_coe, Submodule.mem_map,
    Submodule.coe_subtype, vadd_eq_add]
  constructor
  · rintro ⟨hu, hu'⟩
    exact ⟨u - u₀, ⟨⟨u - u₀, sub_mem_w1pVanishingOnSubmodule_of_sub_mem hu hu₀g⟩,
      (hker _).2 ((hsol u).1 hu'), rfl⟩, add_sub_cancel u₀ u⟩
  · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    refine ⟨?_, (hsol _).2 ?_⟩
    · rw [add_sub_right_comm]
      exact add_mem hu₀g ((ClosedSubmodule.mem_toSubmodule_iff _ _).1 w.property)
    · rw [add_sub_cancel_left]
      exact (hker w).1 hw

/-! ### The compatibility condition under Gårding's inequality

The abstract theorems are applied with the Hilbert spaces `H¹_Γ(Ω)` and `L²(Ω)` named explicitly,
as in the Dirichlet case: inferring them from the compact value map would make instance search
unify the structures of `H¹_Γ(Ω)` against metavariables. -/

section Garding

variable (hJ : IsCompactOperator ((W1p.valueL (mu := mu) (Omega := Omega) (p := 2)).comp
    (W1pVanishingOn mu Omega 2 Γ).subtypeL))
  (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
  {C₀ β : ℝ} (hC₀ : 0 < C₀)
  (hgarding : ∀ w : W1pVanishingOn mu Omega 2 Γ,
    C₀ * ‖w‖ ^ 2 ≤ energyFormH1 a b c (w : W1p mu Omega 2) (w : W1p mu Omega 2) +
      β * ‖W1p.value (w : W1p mu Omega 2)‖ ^ 2)
include hJ hC₀ hgarding

omit hJ hC₀ in
/-- Gårding's inequality in the form of the abstract Fredholm theorems. -/
private theorem garding_energyFormH1LVanishingOn (w : W1pVanishingOn mu Omega 2 Γ) :
    C₀ * ‖w‖ ^ 2 ≤ energyFormH1LVanishingOn hcoeff Γ w w +
      β * ‖((W1p.valueL (mu := mu) (Omega := Omega) (p := 2)).comp
        (W1pVanishingOn mu Omega 2 Γ).subtypeL) w‖ ^ 2 := by
  rw [energyFormH1LVanishingOn_apply, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
    W1p.valueL_apply]
  exact hgarding w

/-- **The Fredholm compatibility condition for the mixed problem.** Let the value map
`H¹_Γ(Ω) → L²(Ω)` be compact and let the energy form `B` of `-∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u`
satisfy Gårding's inequality `C₀‖w‖²_{H¹} ≤ B(w, w) + β‖w‖²_{L²}` on `H¹_Γ(Ω)`, with `C₀ > 0`.
For `ℓ ∈ (H¹_Γ(Ω))*` the weak problem `B(u, ·) = ℓ` has a solution `u ∈ H¹_Γ(Ω)` exactly when `ℓ`
vanishes on the weak adjoint kernel `{w | ∀ v, B(v, w) = 0}`. -/
theorem exists_forall_energyFormH1LVanishingOn_eq_iff_of_garding
    (ℓ : StrongDual ℝ (W1pVanishingOn mu Omega 2 Γ)) :
    (∃ u : W1pVanishingOn mu Omega 2 Γ, ∀ v, energyFormH1LVanishingOn hcoeff Γ u v = ℓ v) ↔
      ∀ w : W1pVanishingOn mu Omega 2 Γ,
        (∀ v, energyFormH1LVanishingOn hcoeff Γ v w = 0) → ℓ w = 0 :=
  IsCompactOperator.exists_forall_apply_eq_iff_of_garding
    (V := W1pVanishingOn mu Omega 2 Γ) (H := Lp ℝ 2 (mu.restrict Omega))
    hJ hC₀ (garding_energyFormH1LVanishingOn hcoeff hgarding) ℓ

/-- Under Gårding's inequality, with a compact value map on `H¹_Γ(Ω)`, the weak solutions in
`H¹_Γ(Ω)` of the homogeneous mixed problem form a finite-dimensional space. -/
theorem finiteDimensional_ker_energyFormH1LVanishingOn_of_garding :
    FiniteDimensional ℝ (energyFormH1LVanishingOn hcoeff Γ).ker :=
  IsCompactOperator.finiteDimensional_ker_of_garding
    (V := W1pVanishingOn mu Omega 2 Γ) (H := Lp ℝ 2 (mu.restrict Omega))
    hJ hC₀ (garding_energyFormH1LVanishingOn hcoeff hgarding)

/-- **The kernel and the adjoint kernel of the mixed problem have the same dimension.** Under
Gårding's inequality, with a compact value map on `H¹_Γ(Ω)`, the weak solutions `w ∈ H¹_Γ(Ω)` of
the homogeneous adjoint problem, `B(v, w) = 0` for every `v ∈ H¹_Γ(Ω)`, and those `u` of the
homogeneous problem, `B(u, v) = 0` for every `v ∈ H¹_Γ(Ω)`, form spaces of the same finite
dimension. -/
theorem finrank_ker_flip_energyFormH1LVanishingOn_eq_of_garding :
    finrank ℝ (energyFormH1LVanishingOn hcoeff Γ).flip.ker =
      finrank ℝ (energyFormH1LVanishingOn hcoeff Γ).ker :=
  IsCompactOperator.finrank_ker_flip_eq_finrank_ker_of_garding
    (V := W1pVanishingOn mu Omega 2 Γ) (H := Lp ℝ 2 (mu.restrict Omega))
    hJ hC₀ (garding_energyFormH1LVanishingOn hcoeff hgarding)

/-- **Uniqueness implies existence for the mixed problem.** Under Gårding's inequality, with a
compact value map on `H¹_Γ(Ω)`, if the homogeneous mixed problem has only the trivial weak solution
in `H¹_Γ(Ω)`, then for every `ℓ ∈ (H¹_Γ(Ω))*` the weak problem `B(u, ·) = ℓ` has exactly one
solution `u ∈ H¹_Γ(Ω)`. -/
theorem existsUnique_forall_energyFormH1LVanishingOn_eq_of_garding
    (hker : ∀ u : W1pVanishingOn mu Omega 2 Γ,
      (∀ v, energyFormH1LVanishingOn hcoeff Γ u v = 0) → u = 0)
    (ℓ : StrongDual ℝ (W1pVanishingOn mu Omega 2 Γ)) :
    ∃! u : W1pVanishingOn mu Omega 2 Γ, ∀ v, energyFormH1LVanishingOn hcoeff Γ u v = ℓ v :=
  IsCompactOperator.existsUnique_forall_apply_eq_of_garding
    (V := W1pVanishingOn mu Omega 2 Γ) (H := Lp ℝ 2 (mu.restrict Omega))
    hJ hC₀ (garding_energyFormH1LVanishingOn hcoeff hgarding) hker ℓ

include hcoeff in
/-- **The compatibility condition for the mixed problem with a Dirichlet datum.** Under Gårding's
inequality, with a compact value map on `H¹_Γ(Ω)`, let `g ∈ H¹(Ω)` and `ℓ ∈ (H¹_Γ(Ω))*`. The weak
mixed problem `B(u, ·) = ℓ` on `H¹_Γ(Ω)` with `u - g ∈ H¹_Γ(Ω)` has a solution `u ∈ H¹(Ω)` exactly
when `ℓ w = B(g, w)` for every `w` in the weak adjoint kernel
`{w ∈ H¹_Γ(Ω) | ∀ v ∈ H¹_Γ(Ω), B(v, w) = 0}`. -/
theorem exists_sub_mem_w1pVanishingOnSubmodule_forall_energyFormH1_eq_iff_of_garding
    (g : W1p mu Omega 2) (ℓ : StrongDual ℝ (W1pVanishingOn mu Omega 2 Γ)) :
    (∃ u : W1p mu Omega 2, u - g ∈ w1pVanishingOnSubmodule mu Omega 2 Γ ∧
        ∀ v : W1pVanishingOn mu Omega 2 Γ, energyFormH1 a b c u v = ℓ v) ↔
      ∀ w : W1pVanishingOn mu Omega 2 Γ,
        (∀ v : W1pVanishingOn mu Omega 2 Γ,
          energyFormH1 a b c (v : W1p mu Omega 2) (w : W1p mu Omega 2) = 0) →
        ℓ w = energyFormH1 a b c g (w : W1p mu Omega 2) := by
  rw [exists_sub_mem_w1pVanishingOnSubmodule_forall_energyFormH1_eq_iff_exists_w1pVanishingOn
    hcoeff]
  simpa only [energyFormH1LVanishingOn_apply, sub_apply, ContinuousLinearMap.comp_apply,
    Submodule.subtypeL_apply, energyFormH1L_apply, sub_eq_zero] using
    exists_forall_energyFormH1LVanishingOn_eq_iff_of_garding hJ hcoeff hC₀ hgarding
      (ℓ - (energyFormH1L hcoeff g).comp (W1pVanishingOn mu Omega 2 Γ).subtypeL)

include hcoeff in
/-- **Uniqueness implies existence for the mixed problem, with a Dirichlet datum.** Under
Gårding's inequality, with a compact value map on `H¹_Γ(Ω)`, if the homogeneous mixed problem has
only the trivial weak solution in `H¹_Γ(Ω)`, then for every `g ∈ H¹(Ω)` and `ℓ ∈ (H¹_Γ(Ω))*` there
is exactly one `u ∈ H¹(Ω)` with `u - g ∈ H¹_Γ(Ω)` and `B(u, v) = ℓ v` for every `v ∈ H¹_Γ(Ω)`. -/
theorem existsUnique_sub_mem_w1pVanishingOnSubmodule_forall_energyFormH1_eq_of_garding
    (hker : ∀ u : W1pVanishingOn mu Omega 2 Γ,
      (∀ v : W1pVanishingOn mu Omega 2 Γ,
        energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) = 0) → u = 0)
    (g : W1p mu Omega 2) (ℓ : StrongDual ℝ (W1pVanishingOn mu Omega 2 Γ)) :
    ∃! u : W1p mu Omega 2, u - g ∈ w1pVanishingOnSubmodule mu Omega 2 Γ ∧
      ∀ v : W1pVanishingOn mu Omega 2 Γ, energyFormH1 a b c u v = ℓ v :=
  (existsUnique_sub_mem_w1pVanishingOnSubmodule_forall_energyFormH1_eq_iff_existsUnique
    hcoeff g ℓ).2 <| by
    simpa only [energyFormH1LVanishingOn_apply, sub_apply, ContinuousLinearMap.comp_apply,
      Submodule.subtypeL_apply, energyFormH1L_apply] using
      existsUnique_forall_energyFormH1LVanishingOn_eq_of_garding hJ hcoeff hC₀ hgarding
        (fun u hu => hker u fun v => by simpa only [energyFormH1LVanishingOn_apply] using hu v)
        (ℓ - (energyFormH1L hcoeff g).comp (W1pVanishingOn mu Omega 2 Γ).subtypeL)

end Garding

/-! ### Uniformly elliptic operators -/

namespace UniformlyEllipticOn

variable [DecidableEq ι] {lam Lam beta gamma : ℝ}

/-- Gårding's inequality on `H¹_Γ(Ω)` for a uniformly elliptic operator with bounded measurable
coefficients, in the form consumed by the compatibility theorems: it is the inequality on all of
`H¹(Ω)`, applied to the elements of `H¹_Γ(Ω)`. -/
private theorem garding_w1pVanishingOn
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hb : AEStronglyMeasurable b (mu.restrict Omega))
    (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (hb_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b x‖ ≤ beta)
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma)
    (w : W1pVanishingOn mu Omega 2 Γ) :
    lam / 2 * ‖w‖ ^ 2 ≤ energyFormH1 a b c (w : W1p mu Omega 2) (w : W1p mu Omega 2) +
      (lam / 2 + gamma + beta ^ 2 / (2 * lam)) * ‖W1p.value (w : W1p mu Omega 2)‖ ^ 2 :=
  sub_le_iff_le_add.mp (h.garding_energyFormH1_self_norm_of_norm_le ha hb hc hb_bound hc_bound
    (w : W1p mu Omega 2))

/-- **The Fredholm compatibility condition for the mixed problem of a uniformly elliptic
operator.** Let the value map `H¹_Γ(Ω) → L²(Ω)` be compact, as it is when `Ω` has the Rellich
property. Let `a` be uniformly elliptic and let `b` and `c` be bounded and measurable, with no sign
condition on `c` and no smallness of `b`. For `g ∈ H¹(Ω)` and `ℓ ∈ (H¹_Γ(Ω))*` the weak problem
`L u = ℓ` in `Ω`, `u = g` on `Γ`, with the natural boundary condition on the rest of the boundary,
for `L u = -∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u`, has a solution exactly when `ℓ w = B(g, w)` for every
`w` in the weak adjoint kernel
`{w ∈ H¹_Γ(Ω) | ∀ v ∈ H¹_Γ(Ω), B(v, w) = 0}`. -/
theorem exists_sub_mem_w1pVanishingOnSubmodule_forall_energyFormH1_eq_iff
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hb : AEStronglyMeasurable b (mu.restrict Omega))
    (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (hb_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b x‖ ≤ beta)
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma)
    (hJ : IsCompactOperator ((W1p.valueL (mu := mu) (Omega := Omega) (p := 2)).comp
      (W1pVanishingOn mu Omega 2 Γ).subtypeL))
    (g : W1p mu Omega 2) (ℓ : StrongDual ℝ (W1pVanishingOn mu Omega 2 Γ)) :
    (∃ u : W1p mu Omega 2, u - g ∈ w1pVanishingOnSubmodule mu Omega 2 Γ ∧
        ∀ v : W1pVanishingOn mu Omega 2 Γ, energyFormH1 a b c u v = ℓ v) ↔
      ∀ w : W1pVanishingOn mu Omega 2 Γ,
        (∀ v : W1pVanishingOn mu Omega 2 Γ,
          energyFormH1 a b c (v : W1p mu Omega 2) (w : W1p mu Omega 2) = 0) →
        ℓ w = energyFormH1 a b c g (w : W1p mu Omega 2) :=
  exists_sub_mem_w1pVanishingOnSubmodule_forall_energyFormH1_eq_iff_of_garding hJ
    (memLp_energyIntegrand_of_bounds h.upper_nonneg ha hb hc
      (fun _x hx eta xi => h.upper_bound hx eta xi) hb_bound hc_bound)
    (half_pos h.pos) (h.garding_w1pVanishingOn ha hb hc hb_bound hc_bound) g ℓ

/-- For a uniformly elliptic operator with bounded measurable coefficients and a compact value
map `H¹_Γ(Ω) → L²(Ω)`, the weak solutions in `H¹_Γ(Ω)` of the homogeneous mixed problem form a
finite-dimensional space. -/
theorem finiteDimensional_ker_energyFormH1LVanishingOn
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hb : AEStronglyMeasurable b (mu.restrict Omega))
    (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (hb_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b x‖ ≤ beta)
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma)
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hJ : IsCompactOperator ((W1p.valueL (mu := mu) (Omega := Omega) (p := 2)).comp
      (W1pVanishingOn mu Omega 2 Γ).subtypeL)) :
    FiniteDimensional ℝ (energyFormH1LVanishingOn hcoeff Γ).ker :=
  finiteDimensional_ker_energyFormH1LVanishingOn_of_garding hJ hcoeff (half_pos h.pos)
    (h.garding_w1pVanishingOn ha hb hc hb_bound hc_bound)

/-- **Uniqueness implies existence for the mixed problem of a uniformly elliptic operator.** Let
the value map `H¹_Γ(Ω) → L²(Ω)` be compact, as it is when `Ω` has the Rellich property. Let `a`
be uniformly elliptic and let `b` and `c` be bounded and measurable. If the homogeneous mixed
problem for `-∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u` has only the trivial weak solution in `H¹_Γ(Ω)`, then
for every `g ∈ H¹(Ω)` and `ℓ ∈ (H¹_Γ(Ω))*` there is exactly one `u ∈ H¹(Ω)` with
`u - g ∈ H¹_Γ(Ω)` and `B(u, v) = ℓ v` for every `v ∈ H¹_Γ(Ω)`. -/
theorem existsUnique_sub_mem_w1pVanishingOnSubmodule_forall_energyFormH1_eq
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hb : AEStronglyMeasurable b (mu.restrict Omega))
    (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (hb_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b x‖ ≤ beta)
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma)
    (hJ : IsCompactOperator ((W1p.valueL (mu := mu) (Omega := Omega) (p := 2)).comp
      (W1pVanishingOn mu Omega 2 Γ).subtypeL))
    (hker : ∀ u : W1pVanishingOn mu Omega 2 Γ,
      (∀ v : W1pVanishingOn mu Omega 2 Γ,
        energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) = 0) → u = 0)
    (g : W1p mu Omega 2) (ℓ : StrongDual ℝ (W1pVanishingOn mu Omega 2 Γ)) :
    ∃! u : W1p mu Omega 2, u - g ∈ w1pVanishingOnSubmodule mu Omega 2 Γ ∧
      ∀ v : W1pVanishingOn mu Omega 2 Γ, energyFormH1 a b c u v = ℓ v :=
  existsUnique_sub_mem_w1pVanishingOnSubmodule_forall_energyFormH1_eq_of_garding hJ
    (memLp_energyIntegrand_of_bounds h.upper_nonneg ha hb hc
      (fun _x hx eta xi => h.upper_bound hx eta xi) hb_bound hc_bound)
    (half_pos h.pos) (h.garding_w1pVanishingOn ha hb hc hb_bound hc_bound) hker g ℓ

end UniformlyEllipticOn

end Domain

/-! ### Lipschitz domains -/

section Lipschitz

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {V : Opens (WithLp 2 (ℝ × E))} {L : ℝ≥0}
  {ι : Type*} [Fintype ι] [DecidableEq ι] {Omega : Opens (EuclideanSpace ℝ ι)}
  {Γ : Set (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
  {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {c : EuclideanSpace ℝ ι → ℝ}
  {lam Lam beta gamma : ℝ}

namespace UniformlyEllipticOn

/-- **The Fredholm alternative for the mixed problem on a Lipschitz domain.** Let an affine
isometry `e` carry the open set `Ω ⊆ EuclideanSpace ℝ ι` onto a bounded Lipschitz domain `V`, and
let `Γ` be any set. Let `a` be uniformly elliptic and let `b` and `c` be bounded and measurable.
For `g ∈ H¹(Ω)` and `ℓ ∈ (H¹_Γ(Ω))*` the weak mixed problem `B(u, ·) = ℓ` on `H¹_Γ(Ω)` with
`u - g ∈ H¹_Γ(Ω)` has a solution exactly when `ℓ w = B(g, w)` for every `w` in the weak adjoint
kernel `{w ∈ H¹_Γ(Ω) | ∀ v ∈ H¹_Γ(Ω), B(v, w) = 0}`. -/
theorem exists_sub_mem_w1pVanishingOnSubmodule_forall_energyFormH1_eq_iff_of_isLipschitzDomainWith
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (volume.restrict Omega))
    (hb : AEStronglyMeasurable b (volume.restrict Omega))
    (hc : AEStronglyMeasurable c (volume.restrict Omega))
    (hb_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b x‖ ≤ beta)
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma)
    (hV : (V : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hVb : IsBounded (V : Set (WithLp 2 (ℝ × E))))
    (e : EuclideanSpace ℝ ι ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E))
    (hVΩ : (V : Set (WithLp 2 (ℝ × E))) = e.symm ⁻¹' Omega)
    (g : W1p volume Omega 2) (ℓ : StrongDual ℝ (W1pVanishingOn volume Omega 2 Γ)) :
    (∃ u : W1p volume Omega 2, u - g ∈ w1pVanishingOnSubmodule volume Omega 2 Γ ∧
        ∀ v : W1pVanishingOn volume Omega 2 Γ, energyFormH1 a b c u v = ℓ v) ↔
      ∀ w : W1pVanishingOn volume Omega 2 Γ,
        (∀ v : W1pVanishingOn volume Omega 2 Γ,
          energyFormH1 a b c (v : W1p volume Omega 2) (w : W1p volume Omega 2) = 0) →
        ℓ w = energyFormH1 a b c g (w : W1p volume Omega 2) :=
  h.exists_sub_mem_w1pVanishingOnSubmodule_forall_energyFormH1_eq_iff ha hb hc hb_bound hc_bound
    ((W1p.isCompactOperator_valueL_of_isLipschitzDomainWith_of_affineIsometryEquiv hV hVb e
      hVΩ).comp_clm _) g ℓ

/-- **Uniqueness implies existence for the mixed problem on a Lipschitz domain.** Let an affine
isometry `e` carry the open set `Ω ⊆ EuclideanSpace ℝ ι` onto a bounded Lipschitz domain `V`, and
let `Γ` be any set. Let `a` be uniformly elliptic and let `b` and `c` be bounded and measurable.
If the homogeneous mixed problem has only the trivial weak solution in `H¹_Γ(Ω)`, then for every
`g ∈ H¹(Ω)` and `ℓ ∈ (H¹_Γ(Ω))*` there is exactly one `u ∈ H¹(Ω)` with `u - g ∈ H¹_Γ(Ω)` and
`B(u, v) = ℓ v` for every `v ∈ H¹_Γ(Ω)`. -/
theorem existsUnique_sub_mem_w1pVanishingOnSubmodule_forall_energyFormH1_eq_of_isLipschitzDomainWith
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (volume.restrict Omega))
    (hb : AEStronglyMeasurable b (volume.restrict Omega))
    (hc : AEStronglyMeasurable c (volume.restrict Omega))
    (hb_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b x‖ ≤ beta)
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma)
    (hV : (V : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hVb : IsBounded (V : Set (WithLp 2 (ℝ × E))))
    (e : EuclideanSpace ℝ ι ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E))
    (hVΩ : (V : Set (WithLp 2 (ℝ × E))) = e.symm ⁻¹' Omega)
    (hker : ∀ u : W1pVanishingOn volume Omega 2 Γ,
      (∀ v : W1pVanishingOn volume Omega 2 Γ,
        energyFormH1 a b c (u : W1p volume Omega 2) (v : W1p volume Omega 2) = 0) → u = 0)
    (g : W1p volume Omega 2) (ℓ : StrongDual ℝ (W1pVanishingOn volume Omega 2 Γ)) :
    ∃! u : W1p volume Omega 2, u - g ∈ w1pVanishingOnSubmodule volume Omega 2 Γ ∧
      ∀ v : W1pVanishingOn volume Omega 2 Γ, energyFormH1 a b c u v = ℓ v :=
  h.existsUnique_sub_mem_w1pVanishingOnSubmodule_forall_energyFormH1_eq ha hb hc hb_bound hc_bound
    ((W1p.isCompactOperator_valueL_of_isLipschitzDomainWith_of_affineIsometryEquiv hV hVb e
      hVΩ).comp_clm _) hker g ℓ

end UniformlyEllipticOn

end Lipschitz

end PDE

end TauCeti

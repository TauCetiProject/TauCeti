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

Let `Ω` be an open set, `Γ` a set, typically a part of the boundary, and `B` the energy form of
`L u = -∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u` (`TauCeti.PDE.energyFormH1`). The weak mixed problem asks, for
`g ∈ H¹(Ω)` and `ℓ ∈ (H¹_Γ(Ω))*`, for `u ∈ H¹(Ω)` with

`u - g ∈ H¹_Γ(Ω)` and `B(u, v) = ℓ v` for every `v ∈ H¹_Γ(Ω)`,

where `H¹_Γ(Ω)` is the space `TauCeti.W1pVanishingOn` of Sobolev functions vanishing on `Γ`. When
`B` is coercive on `H¹_Γ(Ω)` this has exactly one solution
(`TauCeti.PDE.existsUnique_sub_mem_w1pVanishingOnSubmodule_forall_energyFormH1_eq`). This file
drops coercivity. Suppose instead that `B` satisfies **Gårding's inequality**

`C₀ ‖w‖²_{H¹} ≤ B(w, w) + β ‖w‖²_{L²}` for every `w ∈ H¹_Γ(Ω)`, with `C₀ > 0`,

and that the value map `H¹_Γ(Ω) → L²(Ω)` is compact. This holds when the value map of all of
`H¹(Ω)` is compact, which on a bounded Lipschitz domain is the Rellich–Kondrachov theorem, and for
`H¹_Γ(Ω) ⊆ H¹₀(Ω)` on every bounded open set. Then the abstract Fredholm theory of Gårding forms
(`IsCompactOperator.exists_forall_apply_eq_iff_of_garding`) applies on the Hilbert space
`H¹_Γ(Ω)`:

* the problem is solvable exactly when `ℓ w = B(g, w)` for every `w` in the **weak adjoint
  kernel** `{w ∈ H¹_Γ(Ω) | ∀ v ∈ H¹_Γ(Ω), B(v, w) = 0}`;
* the kernel `{w ∈ H¹_Γ(Ω) | ∀ v ∈ H¹_Γ(Ω), B(w, v) = 0}` and the adjoint kernel are finite
  dimensional of the same dimension, and the solution set, when nonempty, is a translate of the
  kernel (`TauCeti.PDE.setOf_sub_mem_w1pVanishingOnSubmodule_forall_energyFormH1_eq_eq_vadd`);
* if the homogeneous problem has only the trivial solution, the problem has exactly one solution
  for every `g` and `ℓ`.

No hypothesis relates `Γ` to `Ω`: the argument only uses that `H¹_Γ(Ω)` is a closed subspace of
`H¹(Ω)`. For `Γ = frontier Ω` this is the Fredholm alternative for the Dirichlet problem in
`TauCeti.Analysis.PDE.FredholmAlternative`. For `Γ = ∅` the test space `H¹_∅(Ω)` is the closure of
the restrictions of test functions on the whole space, which can be a proper subspace of `H¹(Ω)`;
where it is all of `H¹(Ω)`, for example on a bounded Lipschitz domain, this is the Fredholm
alternative for the Neumann problem with lower-order terms.

Every uniformly elliptic operator with bounded measurable drift and mass coefficients satisfies
Gårding's inequality on all of `H¹(Ω)`
(`TauCeti.PDE.UniformlyEllipticOn.garding_energyFormH1_self_norm_of_norm_le`), with no sign
condition on `c` and no smallness of `b`, so for such operators the alternative holds
on every bounded Lipschitz domain. As in `TauCeti.Analysis.PDE.MixedProblem`, Lipschitz domains are
set in the product `ℝ × E` of their boundary charts while the energy form lives on
`EuclideanSpace ℝ ι`, and the domain is an isometric copy of a Lipschitz domain.

## Main declarations

* `TauCeti.PDE.exists_forall_energyFormH1LVanishingOn_eq_iff_of_garding` and
  `TauCeti.PDE.exists_sub_mem_w1pVanishingOnSubmodule_forall_energyFormH1_eq_iff_of_garding`: the
  compatibility condition, for the homogeneous Dirichlet datum and for a datum `g`.
* `TauCeti.PDE.finiteDimensional_ker_energyFormH1LVanishingOn_of_garding` and
  `TauCeti.PDE.finrank_ker_flip_energyFormH1LVanishingOn_eq_of_garding`: the kernel and the
  adjoint kernel are finite dimensional of the same dimension.
* `TauCeti.PDE.existsUnique_forall_energyFormH1LVanishingOn_eq_of_garding` and
  `TauCeti.PDE.existsUnique_sub_mem_w1pVanishingOnSubmodule_forall_energyFormH1_eq_of_garding`:
  uniqueness implies existence.
* `exists_sub_mem_w1pVanishingOnSubmodule_forall_energyFormH1_eq_iff` and
  `existsUnique_sub_mem_w1pVanishingOnSubmodule_forall_energyFormH1_eq`, in the namespace
  `TauCeti.PDE.UniformlyEllipticOn`: the same for uniformly elliptic operators with bounded
  measurable coefficients, given the compact value map, with their versions
  `…_of_isLipschitzDomainWith` on bounded Lipschitz domains.

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
  Theorem 9.23 (the Fredholm alternative for the Dirichlet problem).
* L. C. Evans, *Partial Differential Equations*, 2nd ed., Section 6.2.3.
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 8.6.
* P. Grisvard, *Elliptic Problems in Nonsmooth Domains*, §1.5 (mixed boundary conditions).
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

variable (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))

/-! ### The compatibility condition under Gårding's inequality

The abstract theorems are applied with the Hilbert spaces `H¹_Γ(Ω)` and `L²(Ω)` named explicitly,
as in `TauCeti.Analysis.PDE.FredholmAlternative`: inferring them from the compact value map would
make instance search unify the structures of `H¹_Γ(Ω)` against metavariables. -/

section Garding

variable (hK : IsCompactOperator ((W1p.valueL (mu := mu) (Omega := Omega) (p := 2)).comp
    (W1pVanishingOn mu Omega 2 Γ).subtypeL))
  {C₀ β : ℝ} (hC₀ : 0 < C₀)
  (hgarding : ∀ w : W1pVanishingOn mu Omega 2 Γ, C₀ * ‖w‖ ^ 2 ≤
    energyFormH1 a b c (w : W1p mu Omega 2) w + β * ‖W1p.value (w : W1p mu Omega 2)‖ ^ 2)

include hgarding in
/-- Gårding's inequality in the form of the abstract Fredholm theory. -/
private theorem garding_energyFormH1LVanishingOn (w : W1pVanishingOn mu Omega 2 Γ) :
    C₀ * ‖w‖ ^ 2 ≤ energyFormH1LVanishingOn hcoeff Γ w w +
      β * ‖((W1p.valueL (mu := mu) (Omega := Omega) (p := 2)).comp
        (W1pVanishingOn mu Omega 2 Γ).subtypeL) w‖ ^ 2 := by
  rw [energyFormH1LVanishingOn_apply, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
    W1p.valueL_apply]
  exact hgarding w

include hcoeff hK hC₀ hgarding

/-- **The Fredholm compatibility condition for the mixed problem.** Let the value map
`H¹_Γ(Ω) → L²(Ω)` be compact, and let the energy form `B` of `-∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u` satisfy
Gårding's inequality `C₀‖w‖²_{H¹} ≤ B(w, w) + β‖w‖²_{L²}` on `H¹_Γ(Ω)`, with `C₀ > 0`. For
`ℓ ∈ (H¹_Γ(Ω))*` the weak problem `B(u, ·) = ℓ` on `H¹_Γ(Ω)` has a solution `u ∈ H¹_Γ(Ω)` exactly
when `ℓ` vanishes on the weak adjoint kernel `{w | ∀ v, B(v, w) = 0}`. -/
theorem exists_forall_energyFormH1LVanishingOn_eq_iff_of_garding
    (ℓ : StrongDual ℝ (W1pVanishingOn mu Omega 2 Γ)) :
    (∃ u : W1pVanishingOn mu Omega 2 Γ, ∀ v, energyFormH1LVanishingOn hcoeff Γ u v = ℓ v) ↔
      ∀ w : W1pVanishingOn mu Omega 2 Γ,
        (∀ v, energyFormH1LVanishingOn hcoeff Γ v w = 0) → ℓ w = 0 :=
  IsCompactOperator.exists_forall_apply_eq_iff_of_garding
    (V := W1pVanishingOn mu Omega 2 Γ) (H := Lp ℝ 2 (mu.restrict Omega))
    hK hC₀
    (garding_energyFormH1LVanishingOn hcoeff hgarding) ℓ

/-- Under Gårding's inequality and with a compact value map, the weak solutions in `H¹_Γ(Ω)` of
the homogeneous mixed problem form a finite-dimensional space. -/
theorem finiteDimensional_ker_energyFormH1LVanishingOn_of_garding :
    FiniteDimensional ℝ (energyFormH1LVanishingOn hcoeff Γ).ker :=
  IsCompactOperator.finiteDimensional_ker_of_garding
    (V := W1pVanishingOn mu Omega 2 Γ) (H := Lp ℝ 2 (mu.restrict Omega))
    hK hC₀
    (garding_energyFormH1LVanishingOn hcoeff hgarding)

/-- **The kernel and the adjoint kernel have the same dimension.** Under Gårding's inequality
and with a compact value map, the weak solutions `w ∈ H¹_Γ(Ω)` of the homogeneous adjoint mixed
problem, `B(v, w) = 0` for every `v ∈ H¹_Γ(Ω)`, and those `u` of the homogeneous mixed problem,
`B(u, v) = 0` for every `v ∈ H¹_Γ(Ω)`, form spaces of the same finite dimension. -/
theorem finrank_ker_flip_energyFormH1LVanishingOn_eq_of_garding :
    finrank ℝ (energyFormH1LVanishingOn hcoeff Γ).flip.ker =
      finrank ℝ (energyFormH1LVanishingOn hcoeff Γ).ker :=
  IsCompactOperator.finrank_ker_flip_eq_finrank_ker_of_garding
    (V := W1pVanishingOn mu Omega 2 Γ) (H := Lp ℝ 2 (mu.restrict Omega))
    hK hC₀
    (garding_energyFormH1LVanishingOn hcoeff hgarding)

/-- **Uniqueness implies existence for the mixed problem.** Under Gårding's inequality and with a
compact value map, if the homogeneous mixed problem has only the trivial weak solution, then for
every `ℓ ∈ (H¹_Γ(Ω))*` the weak problem `B(u, ·) = ℓ` has exactly one solution `u ∈ H¹_Γ(Ω)`. -/
theorem existsUnique_forall_energyFormH1LVanishingOn_eq_of_garding
    (hker : ∀ u : W1pVanishingOn mu Omega 2 Γ,
      (∀ v, energyFormH1LVanishingOn hcoeff Γ u v = 0) → u = 0)
    (ℓ : StrongDual ℝ (W1pVanishingOn mu Omega 2 Γ)) :
    ∃! u : W1pVanishingOn mu Omega 2 Γ, ∀ v, energyFormH1LVanishingOn hcoeff Γ u v = ℓ v :=
  IsCompactOperator.existsUnique_forall_apply_eq_of_garding
    (V := W1pVanishingOn mu Omega 2 Γ) (H := Lp ℝ 2 (mu.restrict Omega))
    hK hC₀
    (garding_energyFormH1LVanishingOn hcoeff hgarding) hker ℓ

/-- **The compatibility condition for the mixed problem with a Dirichlet datum.** Under Gårding's
inequality on `H¹_Γ(Ω)` and with a compact value map, let `g ∈ H¹(Ω)` and `ℓ ∈ (H¹_Γ(Ω))*`. The
mixed problem `u - g ∈ H¹_Γ(Ω)`, `B(u, v) = ℓ v` for every `v ∈ H¹_Γ(Ω)`, has a solution
`u ∈ H¹(Ω)` exactly when `ℓ w = B(g, w)` for every `w` in the weak adjoint kernel
`{w ∈ H¹_Γ(Ω) | ∀ v ∈ H¹_Γ(Ω), B(v, w) = 0}`. -/
theorem exists_sub_mem_w1pVanishingOnSubmodule_forall_energyFormH1_eq_iff_of_garding
    (g : W1p mu Omega 2) (ℓ : StrongDual ℝ (W1pVanishingOn mu Omega 2 Γ)) :
    (∃ u : W1p mu Omega 2, u - g ∈ w1pVanishingOnSubmodule mu Omega 2 Γ ∧
        ∀ v : W1pVanishingOn mu Omega 2 Γ, energyFormH1 a b c u v = ℓ v) ↔
      ∀ w : W1pVanishingOn mu Omega 2 Γ,
        (∀ v : W1pVanishingOn mu Omega 2 Γ, energyFormH1 a b c (v : W1p mu Omega 2) w = 0) →
        ℓ w = energyFormH1 a b c g w := by
  rw [
    exists_sub_mem_w1pVanishingOnSubmodule_forall_energyFormH1_eq_iff_exists_w1pVanishingOn hcoeff]
  simpa [sub_eq_zero] using exists_forall_energyFormH1LVanishingOn_eq_iff_of_garding hcoeff hK hC₀
    hgarding (ℓ - (energyFormH1L hcoeff g).comp (W1pVanishingOn mu Omega 2 Γ).subtypeL)

/-- **Uniqueness implies existence for the mixed problem with a Dirichlet datum.** Under Gårding's
inequality on `H¹_Γ(Ω)` and with a compact value map, if the homogeneous mixed problem has only
the trivial weak solution in `H¹_Γ(Ω)`, then for every `g ∈ H¹(Ω)` and `ℓ ∈ (H¹_Γ(Ω))*` there is
exactly one `u ∈ H¹(Ω)` with `u - g ∈ H¹_Γ(Ω)` and `B(u, v) = ℓ v` for every `v ∈ H¹_Γ(Ω)`. -/
theorem existsUnique_sub_mem_w1pVanishingOnSubmodule_forall_energyFormH1_eq_of_garding
    (hker : ∀ u : W1pVanishingOn mu Omega 2 Γ,
      (∀ v : W1pVanishingOn mu Omega 2 Γ, energyFormH1 a b c (u : W1p mu Omega 2) v = 0) → u = 0)
    (g : W1p mu Omega 2) (ℓ : StrongDual ℝ (W1pVanishingOn mu Omega 2 Γ)) :
    ∃! u : W1p mu Omega 2, u - g ∈ w1pVanishingOnSubmodule mu Omega 2 Γ ∧
      ∀ v : W1pVanishingOn mu Omega 2 Γ, energyFormH1 a b c u v = ℓ v :=
  (
existsUnique_sub_mem_w1pVanishingOnSubmodule_forall_energyFormH1_eq_iff_existsUnique_w1pVanishingOn
    hcoeff g ℓ).2 <| by
    simpa using existsUnique_forall_energyFormH1LVanishingOn_eq_of_garding hcoeff hK hC₀ hgarding
      (fun u hu => hker u fun v => by simpa using hu v)
      (ℓ - (energyFormH1L hcoeff g).comp (W1pVanishingOn mu Omega 2 Γ).subtypeL)

end Garding

namespace UniformlyEllipticOn

variable [DecidableEq ι] {lam Lam beta gamma : ℝ}

/-- Gårding's inequality on `H¹_Γ(Ω)` for a uniformly elliptic operator with bounded measurable
coefficients, in the form consumed by the compatibility theorems. -/
private theorem garding_energyFormH1_vanishingOn
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hb : AEStronglyMeasurable b (mu.restrict Omega))
    (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (hb_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b x‖ ≤ beta)
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma)
    (w : W1pVanishingOn mu Omega 2 Γ) :
    lam / 2 * ‖w‖ ^ 2 ≤ energyFormH1 a b c (w : W1p mu Omega 2) w +
      (lam / 2 + gamma + beta ^ 2 / (2 * lam)) * ‖W1p.value (w : W1p mu Omega 2)‖ ^ 2 :=
  sub_le_iff_le_add.mp
    (h.garding_energyFormH1_self_norm_of_norm_le ha hb hc hb_bound hc_bound (w : W1p mu Omega 2))

/-- **The Fredholm compatibility condition for the mixed problem of a uniformly elliptic
operator.** Let the value map `H¹_Γ(Ω) → L²(Ω)` be compact, let `a` be uniformly elliptic and let
`b` and `c` be bounded and measurable, with no sign condition on `c` and no smallness of `b`. For
`g ∈ H¹(Ω)` and `ℓ ∈ (H¹_Γ(Ω))*` the weak mixed problem for `-∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u`,
`u - g ∈ H¹_Γ(Ω)` and `B(u, v) = ℓ v` for every `v ∈ H¹_Γ(Ω)`, has a solution exactly when
`ℓ w = B(g, w)` for every `w` in the weak adjoint kernel
`{w ∈ H¹_Γ(Ω) | ∀ v ∈ H¹_Γ(Ω), B(v, w) = 0}`. -/
theorem exists_sub_mem_w1pVanishingOnSubmodule_forall_energyFormH1_eq_iff
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hb : AEStronglyMeasurable b (mu.restrict Omega))
    (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (hb_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b x‖ ≤ beta)
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma)
    (hK : IsCompactOperator ((W1p.valueL (mu := mu) (Omega := Omega) (p := 2)).comp
      (W1pVanishingOn mu Omega 2 Γ).subtypeL))
    (g : W1p mu Omega 2) (ℓ : StrongDual ℝ (W1pVanishingOn mu Omega 2 Γ)) :
    (∃ u : W1p mu Omega 2, u - g ∈ w1pVanishingOnSubmodule mu Omega 2 Γ ∧
        ∀ v : W1pVanishingOn mu Omega 2 Γ, energyFormH1 a b c u v = ℓ v) ↔
      ∀ w : W1pVanishingOn mu Omega 2 Γ,
        (∀ v : W1pVanishingOn mu Omega 2 Γ, energyFormH1 a b c (v : W1p mu Omega 2) w = 0) →
        ℓ w = energyFormH1 a b c g w :=
  exists_sub_mem_w1pVanishingOnSubmodule_forall_energyFormH1_eq_iff_of_garding
    (memLp_energyIntegrand_of_bounds h.upper_nonneg ha hb hc
      (fun _x hx eta xi => h.upper_bound hx eta xi) hb_bound hc_bound)
    hK (half_pos h.pos) (h.garding_energyFormH1_vanishingOn ha hb hc hb_bound hc_bound) g ℓ

/-- **Uniqueness implies existence for the mixed problem of a uniformly elliptic operator.** Let
the value map `H¹_Γ(Ω) → L²(Ω)` be compact, let `a` be uniformly elliptic and let `b` and `c` be
bounded and measurable. If the homogeneous mixed problem for `-∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u` has only
the trivial weak solution in `H¹_Γ(Ω)`, then for every `g ∈ H¹(Ω)` and `ℓ ∈ (H¹_Γ(Ω))*` there is
exactly one `u ∈ H¹(Ω)` with `u - g ∈ H¹_Γ(Ω)` and `B(u, v) = ℓ v` for every `v ∈ H¹_Γ(Ω)`. -/
theorem existsUnique_sub_mem_w1pVanishingOnSubmodule_forall_energyFormH1_eq
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hb : AEStronglyMeasurable b (mu.restrict Omega))
    (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (hb_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b x‖ ≤ beta)
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma)
    (hK : IsCompactOperator ((W1p.valueL (mu := mu) (Omega := Omega) (p := 2)).comp
      (W1pVanishingOn mu Omega 2 Γ).subtypeL))
    (hker : ∀ u : W1pVanishingOn mu Omega 2 Γ,
      (∀ v : W1pVanishingOn mu Omega 2 Γ, energyFormH1 a b c (u : W1p mu Omega 2) v = 0) → u = 0)
    (g : W1p mu Omega 2) (ℓ : StrongDual ℝ (W1pVanishingOn mu Omega 2 Γ)) :
    ∃! u : W1p mu Omega 2, u - g ∈ w1pVanishingOnSubmodule mu Omega 2 Γ ∧
      ∀ v : W1pVanishingOn mu Omega 2 Γ, energyFormH1 a b c u v = ℓ v :=
  existsUnique_sub_mem_w1pVanishingOnSubmodule_forall_energyFormH1_eq_of_garding
    (memLp_energyIntegrand_of_bounds h.upper_nonneg ha hb hc
      (fun _x hx eta xi => h.upper_bound hx eta xi) hb_bound hc_bound)
    hK (half_pos h.pos) (h.garding_energyFormH1_vanishingOn ha hb hc hb_bound hc_bound) hker g ℓ

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
isometry `e` carry the open set `Ω ⊆ EuclideanSpace ℝ ι` onto a bounded Lipschitz domain `V`, let
`Γ` be any set, let `a` be uniformly elliptic and let `b` and `c` be bounded and measurable, with
no sign condition on `c` and no smallness of `b`. For `g ∈ H¹(Ω)` and `ℓ ∈ (H¹_Γ(Ω))*` the weak
mixed problem for `-∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u`, `u - g ∈ H¹_Γ(Ω)` and `B(u, v) = ℓ v` for every
`v ∈ H¹_Γ(Ω)`, has a solution exactly when `ℓ w = B(g, w)` for every `w` in the weak adjoint
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
          energyFormH1 a b c (v : W1p volume Omega 2) w = 0) →
        ℓ w = energyFormH1 a b c g w :=
  h.exists_sub_mem_w1pVanishingOnSubmodule_forall_energyFormH1_eq_iff ha hb hc hb_bound hc_bound
    ((W1p.isCompactOperator_valueL_of_isLipschitzDomainWith_of_affineIsometryEquiv hV hVb e
      hVΩ).comp_clm _)
    g ℓ

/-- **Uniqueness implies existence for the mixed problem on a Lipschitz domain.** Let an affine
isometry `e` carry the open set `Ω ⊆ EuclideanSpace ℝ ι` onto a bounded Lipschitz domain `V`, let
`a` be uniformly elliptic and let `b` and `c` be bounded and measurable. If the homogeneous mixed
problem for `-∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u` has only the trivial weak solution in `H¹_Γ(Ω)`, then
for every `g ∈ H¹(Ω)` and `ℓ ∈ (H¹_Γ(Ω))*` there is exactly one `u ∈ H¹(Ω)` with
`u - g ∈ H¹_Γ(Ω)` and `B(u, v) = ℓ v` for every `v ∈ H¹_Γ(Ω)`. -/
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
        energyFormH1 a b c (u : W1p volume Omega 2) v = 0) → u = 0)
    (g : W1p volume Omega 2) (ℓ : StrongDual ℝ (W1pVanishingOn volume Omega 2 Γ)) :
    ∃! u : W1p volume Omega 2, u - g ∈ w1pVanishingOnSubmodule volume Omega 2 Γ ∧
      ∀ v : W1pVanishingOn volume Omega 2 Γ, energyFormH1 a b c u v = ℓ v :=
  h.existsUnique_sub_mem_w1pVanishingOnSubmodule_forall_energyFormH1_eq ha hb hc hb_bound
    hc_bound
    ((W1p.isCompactOperator_valueL_of_isLipschitzDomainWith_of_affineIsometryEquiv hV hVb e
      hVΩ).comp_clm _)
    hker g ℓ

end UniformlyEllipticOn

end Lipschitz

end PDE

end TauCeti

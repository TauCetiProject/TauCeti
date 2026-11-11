/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.QuantumSpin.GibbsState
import TauCeti.Analysis.Normed.Algebra.MatrixExponential

/-!
# Interactions of quantum spin systems and their finite-volume theory

An *interaction* `Φ` of a quantum spin system assigns to every finite region `X` of the site set
`L` a self-adjoint observable `Φ X` of the local algebra `A_X`, the energy of the sites of `X`
interacting with each other, `QuantumSpin.Interaction`. The empty region carries no energy.

The *local Hamiltonian* of a finite region `Λ` is the total energy of the interactions inside it,
`H_Φ(Λ) = ∑_{X ⊆ Λ} Φ X`, each term included into `A_Λ`,
`QuantumSpin.Interaction.localHamiltonian`. It is self-adjoint. For `Λ ⊆ Λ'` it splits as the
inclusion of `H_Φ(Λ)` plus the interactions of `Λ'` that leave `Λ`,
`QuantumSpin.Interaction.localHamiltonian_eq_inclusion_add`. Only interactions meeting the
support of an observable fail to commute with it, so the commutator `[H_Φ(Λ'), a]` with an
observable `a` of `A_Λ` is the sum of the commutators `[Φ X, a]` over the regions `X ⊆ Λ'` that
meet `Λ`, `QuantumSpin.Interaction.localHamiltonian_mul_inclusion_sub_inclusion_mul`.

Over `ℂ` the local Hamiltonian generates the *local dynamics*
`τ^Λ_t a = exp (it H_Φ(Λ)) a exp (-it H_Φ(Λ))` on `A_Λ`,
`QuantumSpin.Interaction.localDynamics`. Its generator is the finite-volume local derivation:
on an observable `a` localized in `Λ ⊆ Λ'`, the generator of `τ^Λ'` is
`i ∑_{X ⊆ Λ', X ∩ Λ ≠ ∅} [Φ X, a]`,
`QuantumSpin.Interaction.generator_localDynamics_inclusion`. At inverse temperature `β` the
*finite-volume Gibbs state* `Tr (exp (-β H_Φ(Λ)) ·) / Tr (exp (-β H_Φ(Λ)))` is the unique β-KMS
state of `τ^Λ`, `QuantumSpin.Interaction.isKMSState_localDynamics_iff`.

The finite-volume Gibbs state of `Λ` extends to every larger region `Λ'` by the normalized trace
on the sites of `Λ'` outside `Λ`: it is the Gibbs state composed with the normalized partial trace
`A_Λ' → A_Λ`, `QuantumSpin.Interaction.gibbsExtension`. These extensions restrict to the Gibbs
state of `Λ` and are compatible with the inclusions between larger regions,
`QuantumSpin.Interaction.gibbsExtension_inclusion_of_subset`: this is the consistency a family
of states of the local algebras needs to define a state of their inductive limit. The extension to
`Λ'` is the Gibbs state of the included Hamiltonian `H_Φ(Λ) ⊗ 1`,
`QuantumSpin.Interaction.gibbsExtension_eq_gibbsState`, and hence the unique β-KMS state of the
dynamics this Hamiltonian generates on `A_Λ'`,
`QuantumSpin.Interaction.isKMSState_iff_eq_gibbsExtension`. This rests on a fact about any
Hermitian matrix `K` of `A_Λ`: the inclusion commutes with the exponential,
`QuantumSpin.exp_inclusion`, so the Gibbs state of `K` evaluated on the normalized partial trace
is the Gibbs state of `K ⊗ 1`, `QuantumSpin.gibbsState_expectation`.

## References

Bratteli–Robinson, *Operator Algebras and Quantum Statistical Mechanics 2*, second edition,
Section 6.2.1, for interactions, local Hamiltonians and local dynamics, and Section 6.2.2 for
finite-volume Gibbs states and their extension by the trace state.
-/

public section

noncomputable section

open Matrix Complex NormedSpace
open TauCeti CStarAction
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace TauCeti.QuantumSpin

/-- An **interaction** of a quantum spin system with sites `L` and single-site basis states `S`:
a Hermitian observable `Φ X` of the local algebra of every finite region `X`, the energy of the
sites of `X` interacting with each other, with no energy on the empty region. -/
structure Interaction (R L S : Type*) [Zero R] [Star R] where
  /-- The observable `Φ X` of the local algebra of the region `X`. -/
  toFun : (X : Finset L) → Matrix (X → S) (X → S) R
  /-- Each observable `Φ X` is Hermitian. -/
  isHermitian' (X : Finset L) : (toFun X).IsHermitian
  /-- The empty region carries no energy. -/
  apply_empty' : toFun ∅ = 0

namespace Interaction

variable {R L S : Type*}

section Basic

variable [Zero R] [Star R]

instance : DFunLike (Interaction R L S) (Finset L) fun X => Matrix (X → S) (X → S) R where
  coe := toFun
  coe_injective Φ Ψ h := by
    cases Φ
    cases Ψ
    congr

@[simp]
theorem toFun_eq_coe (Φ : Interaction R L S) : Φ.toFun = Φ :=
  (rfl)

@[simp]
theorem coe_mk (f : (X : Finset L) → Matrix (X → S) (X → S) R) (hf : ∀ X, (f X).IsHermitian)
    (h₀ : f ∅ = 0) : ⇑(Interaction.mk f hf h₀) = f :=
  (rfl)

@[ext]
theorem ext {Φ Ψ : Interaction R L S} (h : ∀ X, Φ X = Ψ X) : Φ = Ψ :=
  DFunLike.ext Φ Ψ h

/-- The observables of an interaction are Hermitian. -/
theorem isHermitian (Φ : Interaction R L S) (X : Finset L) : (Φ X).IsHermitian :=
  Φ.isHermitian' X

/-- An interaction carries no energy on the empty region. -/
@[simp]
theorem apply_empty (Φ : Interaction R L S) : Φ ∅ = 0 :=
  Φ.apply_empty'

end Basic

variable [DecidableEq L] [Fintype S] [DecidableEq S] {Λ Λ' : Finset L}

section LocalHamiltonian

variable [CommSemiring R] [StarRing R]

/-- The **local Hamiltonian** `H_Φ(Λ) = ∑_{X ⊆ Λ} Φ X` of an interaction in a finite region `Λ`,
the sum over all subregions `X` of `Λ` of the observables `Φ X` included into the local algebra
of `Λ`. -/
def localHamiltonian (Φ : Interaction R L S) (Λ : Finset L) : Matrix (Λ → S) (Λ → S) R :=
  ∑ X ∈ Λ.powerset.attach, inclusion (Finset.mem_powerset.1 X.2) (Φ X)

theorem localHamiltonian_def (Φ : Interaction R L S) (Λ : Finset L) :
    Φ.localHamiltonian Λ =
      ∑ X ∈ Λ.powerset.attach, inclusion (Finset.mem_powerset.1 X.2) (Φ X) :=
  (rfl)

/-- The local Hamiltonian is Hermitian. -/
theorem isHermitian_localHamiltonian (Φ : Interaction R L S) (Λ : Finset L) :
    (Φ.localHamiltonian Λ).IsHermitian := by
  rw [localHamiltonian_def, isHermitian_iff_isSelfAdjoint]
  exact isSelfAdjoint_sum _ fun X _ => (Φ.isHermitian X).isSelfAdjoint.map _

/-- The local Hamiltonian of a region `Λ`, included into the local algebra of a larger region,
is Hermitian. -/
theorem isHermitian_inclusion_localHamiltonian (Φ : Interaction R L S) (h : Λ ⊆ Λ') :
    (inclusion h (Φ.localHamiltonian Λ)).IsHermitian :=
  ((Φ.isHermitian_localHamiltonian Λ).isSelfAdjoint.map _).isHermitian

/-- The local Hamiltonian of the empty region vanishes. -/
@[simp]
theorem localHamiltonian_empty (Φ : Interaction R L S) : Φ.localHamiltonian ∅ = 0 := by
  refine Finset.sum_eq_zero fun ⟨X, hX⟩ _ => ?_
  obtain rfl : X = ∅ := by simpa using hX
  simp

/-- For regions `Λ ⊆ Λ'`, the local Hamiltonian of `Λ'` is the local Hamiltonian of `Λ`, included
into the local algebra of `Λ'`, plus the interactions of the subregions of `Λ'` not contained in
`Λ`. -/
theorem localHamiltonian_eq_inclusion_add (Φ : Interaction R L S) (h : Λ ⊆ Λ') :
    Φ.localHamiltonian Λ' = inclusion h (Φ.localHamiltonian Λ) +
      ∑ X ∈ Λ'.powerset.attach.filter fun X : Λ'.powerset => ¬(X : Finset L) ⊆ Λ,
        inclusion (Finset.mem_powerset.1 X.2) (Φ X) := by
  rw [localHamiltonian_def,
    ← Finset.sum_filter_add_sum_filter_not _ fun X : Λ'.powerset => (X : Finset L) ⊆ Λ,
    localHamiltonian_def, map_sum]
  -- the subregions of `Λ'` contained in `Λ` are the subregions of `Λ`
  congr 1
  refine Finset.sum_bij' (fun X hX => ⟨X, Finset.mem_powerset.2 (Finset.mem_filter.1 hX).2⟩)
    (fun X _ => ⟨X, Finset.mem_powerset.2 ((Finset.mem_powerset.1 X.2).trans h)⟩)
    (fun _ _ => Finset.mem_attach _ _) (fun X _ => Finset.mem_filter.2 ⟨Finset.mem_attach _ _,
      Finset.mem_powerset.1 X.2⟩) (fun _ _ => rfl) (fun _ _ => rfl) fun X _ => ?_
  rw [inclusion_inclusion]

end LocalHamiltonian

section Commutator

variable [CommRing R] [StarRing R]

/-- **The finite-volume local derivation.** For regions `Λ ⊆ Λ'` and an observable `a` localized
in `Λ`, only the interactions of the subregions of `Λ'` that meet `Λ` fail to commute with `a`:
`[H_Φ(Λ'), a] = ∑_{X ⊆ Λ', X ∩ Λ ≠ ∅} [Φ X, a]`. -/
theorem localHamiltonian_mul_inclusion_sub_inclusion_mul (Φ : Interaction R L S) (h : Λ ⊆ Λ')
    (a : Matrix (Λ → S) (Λ → S) R) :
    Φ.localHamiltonian Λ' * inclusion h a - inclusion h a * Φ.localHamiltonian Λ' =
      ∑ X ∈ Λ'.powerset.attach.filter fun X : Λ'.powerset => ¬Disjoint (X : Finset L) Λ,
        (inclusion (Finset.mem_powerset.1 X.2) (Φ X) * inclusion h a -
          inclusion h a * inclusion (Finset.mem_powerset.1 X.2) (Φ X)) := by
  rw [localHamiltonian_def, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_filter_add_sum_filter_not _ fun X : Λ'.powerset => Disjoint (X : Finset L) Λ,
    Finset.sum_eq_zero (s := Finset.filter _ _) fun X hX => ?_, zero_add]
  -- interactions in regions disjoint from `Λ` commute with `a`
  exact sub_eq_zero.2 (commute_inclusion_inclusion _ h (Finset.mem_filter.1 hX).2 _ a).eq

end Commutator

section Dynamics

/-- The **local dynamics** `τ^Λ_t a = exp (it H_Φ(Λ)) a exp (-it H_Φ(Λ))` of an interaction on
the local algebra of a finite region `Λ`: the inner dynamics of its local Hamiltonian. -/
def localDynamics (Φ : Interaction ℂ L S) (Λ : Finset L) :
    CStarAction (Multiplicative ℝ) (Matrix (Λ → S) (Λ → S) ℂ) :=
  selfAdjoint.cstarAction ⟨Φ.localHamiltonian Λ, (Φ.isHermitian_localHamiltonian Λ).isSelfAdjoint⟩

theorem localDynamics_def (Φ : Interaction ℂ L S) (Λ : Finset L) :
    Φ.localDynamics Λ = selfAdjoint.cstarAction
      ⟨Φ.localHamiltonian Λ, (Φ.isHermitian_localHamiltonian Λ).isSelfAdjoint⟩ :=
  (rfl)

/-- The local dynamics is `τ^Λ_t a = exp (it H_Φ(Λ)) a exp (-it H_Φ(Λ))`. -/
@[simp]
theorem localDynamics_apply (Φ : Interaction ℂ L S) (Λ : Finset L) (t : Multiplicative ℝ)
    (a : Matrix (Λ → S) (Λ → S) ℂ) :
    Φ.localDynamics Λ t a = exp ((I * t.toAdd) • Φ.localHamiltonian Λ) * a *
      exp (-(I * t.toAdd) • Φ.localHamiltonian Λ) := by
  simp [localDynamics_def]

/-- Every observable lies in the domain of the generator of the local dynamics. -/
@[simp]
theorem generator_localDynamics_domain (Φ : Interaction ℂ L S) (Λ : Finset L) :
    (Φ.localDynamics Λ).generator.domain = ⊤ :=
  selfAdjoint.generator_cstarAction_domain _

/-- The generator of the local dynamics is the inner derivation `a ↦ i [H_Φ(Λ), a]`. -/
theorem generator_localDynamics (Φ : Interaction ℂ L S) (Λ : Finset L)
    (a : (Φ.localDynamics Λ).generator.domain) :
    (Φ.localDynamics Λ).generator a =
      I • (Φ.localHamiltonian Λ * a - a * Φ.localHamiltonian Λ) :=
  selfAdjoint.generator_cstarAction _ a

/-- **The generator of the local dynamics on local observables.** For regions `Λ ⊆ Λ'` and an
observable `a` localized in `Λ`, the generator of the local dynamics of `Λ'` is
`i ∑_{X ⊆ Λ', X ∩ Λ ≠ ∅} [Φ X, a]`. -/
theorem generator_localDynamics_inclusion (Φ : Interaction ℂ L S) (h : Λ ⊆ Λ')
    (a : Matrix (Λ → S) (Λ → S) ℂ) :
    (Φ.localDynamics Λ').generator ⟨inclusion h a, by simp⟩ =
      I • ∑ X ∈ Λ'.powerset.attach.filter fun X : Λ'.powerset => ¬Disjoint (X : Finset L) Λ,
        (inclusion (Finset.mem_powerset.1 X.2) (Φ X) * inclusion h a -
          inclusion h a * inclusion (Finset.mem_powerset.1 X.2) (Φ X)) := by
  rw [generator_localDynamics, localHamiltonian_mul_inclusion_sub_inclusion_mul]

variable [Nonempty S]

/-- **The finite-volume Gibbs state is the unique KMS state.** A state of the local algebra of a
finite region `Λ` is a β-KMS state of the local dynamics exactly when it is the Gibbs state
`Tr (exp (-β H_Φ(Λ)) ·) / Tr (exp (-β H_Φ(Λ)))`, for every real `β`. -/
theorem isKMSState_localDynamics_iff (Φ : Interaction ℂ L S) (Λ : Finset L) (β : ℝ)
    {ω : Matrix (Λ → S) (Λ → S) ℂ →P[ℂ] ℂ} :
    (Φ.localDynamics Λ).IsKMSState β ω ↔
      ω = gibbsState (Φ.localHamiltonian Λ) (Φ.isHermitian_localHamiltonian Λ) β := by
  rw [localDynamics_def]
  exact (Φ.isHermitian_localHamiltonian Λ).isKMSState_iff_eq_gibbsState β

end Dynamics

section GibbsExtension

variable [Nonempty S]

/-- The **extension of the finite-volume Gibbs state** of a region `Λ` to a larger region `Λ'` by
the normalized trace on the sites of `Λ'` outside `Λ`: the Gibbs state
`Tr (exp (-β H_Φ(Λ)) ·) / Tr (exp (-β H_Φ(Λ)))` of `Λ` composed with the normalized partial trace
`A_Λ' → A_Λ`. -/
def gibbsExtension (Φ : Interaction ℂ L S) (β : ℝ) (h : Λ ⊆ Λ') :
    Matrix (Λ' → S) (Λ' → S) ℂ →P[ℂ] ℂ :=
  .mk₀ ((gibbsState (Φ.localHamiltonian Λ) (Φ.isHermitian_localHamiltonian Λ) β :
      Matrix (Λ → S) (Λ → S) ℂ →L[ℂ] ℂ).comp (LinearMap.toContinuousLinearMap (expectation h)))
    fun _ hX => (gibbsState _ _ β).map_nonneg <|
      nonneg_iff_posSemidef.2 ((nonneg_iff_posSemidef.1 hX).quantumSpinExpectation h)

/-- The extended Gibbs state is the Gibbs state of `Λ` evaluated on the normalized partial
trace. -/
theorem gibbsExtension_apply (Φ : Interaction ℂ L S) (β : ℝ) (h : Λ ⊆ Λ')
    (X : Matrix (Λ' → S) (Λ' → S) ℂ) :
    Φ.gibbsExtension β h X =
      gibbsState (Φ.localHamiltonian Λ) (Φ.isHermitian_localHamiltonian Λ) β (expectation h X) :=
  (rfl)

/-- The extended Gibbs state restricts to the Gibbs state of `Λ` on the observables localized in
`Λ`. -/
@[simp]
theorem gibbsExtension_inclusion (Φ : Interaction ℂ L S) (β : ℝ) (h : Λ ⊆ Λ')
    (x : Matrix (Λ → S) (Λ → S) ℂ) :
    Φ.gibbsExtension β h (inclusion h x) =
      gibbsState (Φ.localHamiltonian Λ) (Φ.isHermitian_localHamiltonian Λ) β x := by
  rw [gibbsExtension_apply, expectation_inclusion]

/-- The extension of the Gibbs state of `Λ` to `Λ` itself is the Gibbs state. -/
@[simp]
theorem gibbsExtension_self (Φ : Interaction ℂ L S) (β : ℝ) :
    Φ.gibbsExtension β (subset_refl Λ) =
      gibbsState (Φ.localHamiltonian Λ) (Φ.isHermitian_localHamiltonian Λ) β := by
  ext x
  rw [gibbsExtension_apply, expectation_self]

/-- The extended Gibbs state is normalized: it is a state. -/
@[simp]
theorem gibbsExtension_one (Φ : Interaction ℂ L S) (β : ℝ) (h : Λ ⊆ Λ') :
    Φ.gibbsExtension β h 1 = 1 := by
  have hβ : (-(β • Φ.localHamiltonian Λ)).IsHermitian :=
    ((Φ.isHermitian_localHamiltonian Λ).smul (IsSelfAdjoint.all β)).neg
  rw [gibbsExtension_apply, expectation_one, IsHermitian.gibbsState_apply, Matrix.mul_one,
    div_self hβ.trace_exp_pos.ne']

/-- Extending the Gibbs state of `Λ` to `Λ''` and then evaluating on the normalized partial trace
from `Λ''` to an intermediate region `Λ'` gives its extension to `Λ'`. -/
@[simp]
theorem gibbsExtension_expectation {Λ'' : Finset L} (Φ : Interaction ℂ L S) (β : ℝ) (h₁ : Λ ⊆ Λ')
    (h₂ : Λ' ⊆ Λ'') (X : Matrix (Λ'' → S) (Λ'' → S) ℂ) :
    Φ.gibbsExtension β h₁ (expectation h₂ X) = Φ.gibbsExtension β (h₁.trans h₂) X := by
  rw [gibbsExtension_apply, gibbsExtension_apply, expectation_expectation]

/-- **Consistency of the extended Gibbs states.** For regions `Λ ⊆ Λ' ⊆ Λ''`, the extension of
the Gibbs state of `Λ` to `Λ''` restricts on `A_Λ'` to its extension to `Λ'`. -/
@[simp]
theorem gibbsExtension_inclusion_of_subset {Λ'' : Finset L} (Φ : Interaction ℂ L S) (β : ℝ)
    (h₁ : Λ ⊆ Λ') (h₂ : Λ' ⊆ Λ'') (X : Matrix (Λ' → S) (Λ' → S) ℂ) :
    Φ.gibbsExtension β (h₁.trans h₂) (inclusion h₂ X) = Φ.gibbsExtension β h₁ X := by
  rw [← gibbsExtension_expectation Φ β h₁ h₂, expectation_inclusion]

/-- **The extended Gibbs state is a Gibbs state.** The extension of the Gibbs state of `Λ` to a
larger region `Λ'` by the normalized trace is the Gibbs state of the included Hamiltonian
`H_Φ(Λ) ⊗ 1`. -/
theorem gibbsExtension_eq_gibbsState (Φ : Interaction ℂ L S) (β : ℝ) (h : Λ ⊆ Λ') :
    Φ.gibbsExtension β h =
      gibbsState (inclusion h (Φ.localHamiltonian Λ)) (Φ.isHermitian_inclusion_localHamiltonian h)
        β := by
  ext X
  rw [gibbsExtension_apply, gibbsState_expectation]

/-- **The extended Gibbs state is the unique KMS state of the included dynamics.** A state of the
local algebra of a larger region `Λ'` is a β-KMS state of the dynamics generated by the included
Hamiltonian `H_Φ(Λ) ⊗ 1` exactly when it is the extension of the Gibbs state of `Λ`. -/
theorem isKMSState_iff_eq_gibbsExtension (Φ : Interaction ℂ L S) (β : ℝ) (h : Λ ⊆ Λ')
    {ω : Matrix (Λ' → S) (Λ' → S) ℂ →P[ℂ] ℂ} :
    (selfAdjoint.cstarAction ⟨inclusion h (Φ.localHamiltonian Λ),
      (Φ.isHermitian_inclusion_localHamiltonian h).isSelfAdjoint⟩).IsKMSState β ω ↔
      ω = Φ.gibbsExtension β h := by
  rw [gibbsExtension_eq_gibbsState]
  exact (Φ.isHermitian_inclusion_localHamiltonian h).isKMSState_iff_eq_gibbsState β

end GibbsExtension

end Interaction

end TauCeti.QuantumSpin

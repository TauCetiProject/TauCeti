/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Derivation.Basic
public import TauCeti.RingTheory.Kaehler.DeRham.Basic
public import TauCeti.RingTheory.Kaehler.LieDeriv
import TauCeti.LinearAlgebra.ExteriorAlgebra.Derivation
import TauCeti.LinearAlgebra.ExteriorPower.Basic

/-!
# Lie derivatives on the algebraic de Rham complex

Let `R` and `S` be commutative rings with `[Algebra R S]`, and let `δ : Derivation k S S` be a
`k`-derivation of `S` over any commutative ring `k` with `[Algebra k S]` (without requiring `δ` to
vanish on `R`, covering lifted base/total derivations in a ring tower `k → R → S` as well as
relative derivations `Derivation R S S`).

Whenever `δ` satisfies the Kähler lift condition `∀ r : R, D R S (δ (algebraMap R S r)) = 0`
(studied in `TauCeti.RingTheory.Kaehler.LieDeriv`), its degree-one Kähler Lie derivative
`δ.kaehlerLieDeriv hδ : Module.End k Ω[S⁄R]` extends to an even `k`-linear algebra derivation
`δ.deRhamLieDeriv hδ : Module.End k (ExteriorAlgebra S Ω[S⁄R])` of the algebraic de Rham complex:

* `δ.deRhamLieDeriv hδ` extends `δ` on `S`, acts through `δ.kaehlerLieDeriv hδ` on `1`-forms, and
  satisfies the even Leibniz rule `L (x * y) = L x * y + x * L y`;
* `δ.deRhamLieDeriv hδ` preserves each exterior power `⋀[S]^n Ω[S⁄R]` and each integer degree
  `TauCeti.KaehlerDeRham.grading R S p`;
* `δ.deRhamLieDeriv hδ` commutes with `TauCeti.KaehlerDeRham.extDeriv R S`
  (`Derivation.extDeriv_deRhamLieDeriv`) and is uniquely determined as a `k`-linear derivation of
  `ExteriorAlgebra S Ω[S⁄R]` by these properties (`Derivation.deRhamLieDeriv_unique`);
* `deRhamLieDeriv` preserves commutators (`Derivation.deRhamLieDeriv_commutator`), so commuting
  derivations of `S` lift to commuting derivations of `ExteriorAlgebra S Ω[S⁄R]`
  (`Derivation.commute_deRhamLieDeriv_of_bracket_eq_zero`).

## Main definitions

* `Derivation.deRhamLieDeriv`: Lie derivative on `ExteriorAlgebra S Ω[S⁄R]` along a `k`-derivation
  `δ : Derivation k S S` satisfying `∀ r : R, D R S (δ (algebraMap R S r)) = 0`.

## Main results

* `Derivation.deRhamLieDeriv_mul`, `Derivation.deRhamLieDeriv_smul`: even Leibniz rule and
  `S`-scalar Leibniz rule.
* `Derivation.extDeriv_deRhamLieDeriv`: `extDeriv R S` commutes with `δ.deRhamLieDeriv hδ`.
* `Derivation.deRhamLieDeriv_unique`: uniqueness of `δ.deRhamLieDeriv hδ` as a `k`-derivation of
  `ExteriorAlgebra S Ω[S⁄R]` extending `δ` on `S` and commuting with `extDeriv R S`.
* `Derivation.deRhamLieDeriv_commutator`: `(⁅δ₁, δ₂⁆).deRhamLieDeriv` is the commutator of
  `δ₁.deRhamLieDeriv` and `δ₂.deRhamLieDeriv`.
* `Derivation.commute_deRhamLieDeriv_of_bracket_eq_zero`: commuting derivations of `S` lift to
  commuting Lie derivatives on `ExteriorAlgebra S Ω[S⁄R]`.

## Implementation notes

`Derivation.deRhamLieDeriv` assumes only `[CommRing k]` and `[Algebra k S]` (alongside
`[CommRing R]` and `[Algebra R S]`), without requiring `[Algebra k R]` or `[IsScalarTower k R S]`:
`Ω[S⁄R]` and `ExteriorAlgebra S Ω[S⁄R]` inherit `Module k` and `[IsScalarTower k S _]` directly
from `[Algebra k S]`. The extension from `(δ, δ.kaehlerLieDeriv hδ)` to `ExteriorAlgebra S Ω[S⁄R]`
is obtained from `TauCeti.ExteriorAlgebra.liftTwistedDerivation` with untwisted endomorphism
`σ = AlgHom.id S _`.

## References

* N. Bourbaki, *Algebra*, Chapter III, §10.
* I. M. Anderson, *The Variational Bicomplex*, Chapter 1.
-/

public section

open CliffordAlgebra TauCeti.KaehlerDeRham

namespace Derivation

attribute [local instance 100] LieRing.ofAssociativeRing

variable {k R S : Type*} [CommRing k] [CommRing R] [CommRing S] [Algebra k S] [Algebra R S]

/-- **Lie derivative on the algebraic de Rham complex**: for a `k`-derivation `δ : Derivation k S S`
satisfying `∀ r : R, D R S (δ (algebraMap R S r)) = 0`, `δ.deRhamLieDeriv hδ` is the `k`-linear
derivation of `ExteriorAlgebra S Ω[S⁄R]` extending `δ` in degree zero and `δ.kaehlerLieDeriv hδ` in
degree one. -/
noncomputable def deRhamLieDeriv (δ : Derivation k S S)
    (hδ : ∀ r : R, KaehlerDifferential.D R S (δ (algebraMap R S r)) = 0) :
    Module.End k (ExteriorAlgebra S Ω[S⁄R]) :=
  TauCeti.ExteriorAlgebra.liftTwistedDerivation
    (AlgHom.id S (ExteriorAlgebra S Ω[S⁄R]))
    ((Algebra.linearMap S (ExteriorAlgebra S Ω[S⁄R])).compDer δ)
    (fun s x ↦ by simpa using Algebra.commutes (δ s) x)
    (((ExteriorAlgebra.ι S).restrictScalars k).comp (δ.kaehlerLieDeriv hδ))
    (fun s ω ↦ by simp [Algebra.smul_def])
    (fun ω ↦ ExteriorAlgebra.ι_add_mul_swap (δ.kaehlerLieDeriv hδ ω) ω)

/-- On degree-zero elements `algebraMap S _ s`, `δ.deRhamLieDeriv hδ` acts by `δ`. -/
@[simp]
theorem deRhamLieDeriv_algebraMap (δ : Derivation k S S)
    (hδ : ∀ r : R, KaehlerDifferential.D R S (δ (algebraMap R S r)) = 0) (s : S) :
    δ.deRhamLieDeriv hδ (algebraMap S (ExteriorAlgebra S Ω[S⁄R]) s) =
      algebraMap S (ExteriorAlgebra S Ω[S⁄R]) (δ s) := by
  simpa [deRhamLieDeriv] using
    TauCeti.ExteriorAlgebra.liftTwistedDerivation_algebraMap
      (AlgHom.id S (ExteriorAlgebra S Ω[S⁄R]))
      ((Algebra.linearMap S (ExteriorAlgebra S Ω[S⁄R])).compDer δ)
      (fun s x ↦ by simpa using Algebra.commutes (δ s) x)
      (((ExteriorAlgebra.ι S).restrictScalars k).comp (δ.kaehlerLieDeriv hδ))
      (fun s ω ↦ by simp [Algebra.smul_def])
      (fun ω ↦ ExteriorAlgebra.ι_add_mul_swap (δ.kaehlerLieDeriv hδ ω) ω) s

/-- `δ.deRhamLieDeriv hδ` annihilates `1`. -/
@[simp]
theorem deRhamLieDeriv_one (δ : Derivation k S S)
    (hδ : ∀ r : R, KaehlerDifferential.D R S (δ (algebraMap R S r)) = 0) :
    δ.deRhamLieDeriv hδ 1 = 0 :=
  TauCeti.ExteriorAlgebra.liftTwistedDerivation_one
    (AlgHom.id S (ExteriorAlgebra S Ω[S⁄R]))
    ((Algebra.linearMap S (ExteriorAlgebra S Ω[S⁄R])).compDer δ)
    (fun s x ↦ by simpa using Algebra.commutes (δ s) x)
    (((ExteriorAlgebra.ι S).restrictScalars k).comp (δ.kaehlerLieDeriv hδ))
    (fun s ω ↦ by simp [Algebra.smul_def])
    (fun ω ↦ ExteriorAlgebra.ι_add_mul_swap (δ.kaehlerLieDeriv hδ ω) ω)

/-- On `1`-forms `ι ω`, `δ.deRhamLieDeriv hδ` acts through `δ.kaehlerLieDeriv hδ`. -/
@[simp]
theorem deRhamLieDeriv_ι (δ : Derivation k S S)
    (hδ : ∀ r : R, KaehlerDifferential.D R S (δ (algebraMap R S r)) = 0) (ω : Ω[S⁄R]) :
    δ.deRhamLieDeriv hδ (ExteriorAlgebra.ι S ω) =
      ExteriorAlgebra.ι S (δ.kaehlerLieDeriv hδ ω) := by
  simpa [deRhamLieDeriv] using
    TauCeti.ExteriorAlgebra.liftTwistedDerivation_ι
      (AlgHom.id S (ExteriorAlgebra S Ω[S⁄R]))
      ((Algebra.linearMap S (ExteriorAlgebra S Ω[S⁄R])).compDer δ)
      (fun s x ↦ by simpa using Algebra.commutes (δ s) x)
      (((ExteriorAlgebra.ι S).restrictScalars k).comp (δ.kaehlerLieDeriv hδ))
      (fun s ω ↦ by simp [Algebra.smul_def])
      (fun ω ↦ ExteriorAlgebra.ι_add_mul_swap (δ.kaehlerLieDeriv hδ ω) ω) ω

/-- On exact `1`-forms `ι (D R S s)`, `δ.deRhamLieDeriv hδ` sends `ι (D s)` to `ι (D (δ s))`. -/
theorem deRhamLieDeriv_ι_D (δ : Derivation k S S)
    (hδ : ∀ r : R, KaehlerDifferential.D R S (δ (algebraMap R S r)) = 0) (s : S) :
    δ.deRhamLieDeriv hδ (ExteriorAlgebra.ι S (KaehlerDifferential.D R S s)) =
      ExteriorAlgebra.ι S (KaehlerDifferential.D R S (δ s)) := by
  simp

/-- **Even Leibniz rule** for `δ.deRhamLieDeriv hδ` on exterior products. -/
@[simp]
theorem deRhamLieDeriv_mul (δ : Derivation k S S)
    (hδ : ∀ r : R, KaehlerDifferential.D R S (δ (algebraMap R S r)) = 0)
    (x y : ExteriorAlgebra S Ω[S⁄R]) :
    δ.deRhamLieDeriv hδ (x * y) =
      δ.deRhamLieDeriv hδ x * y + x * δ.deRhamLieDeriv hδ y := by
  simpa [deRhamLieDeriv] using
    TauCeti.ExteriorAlgebra.liftTwistedDerivation_mul
      (AlgHom.id S (ExteriorAlgebra S Ω[S⁄R]))
      ((Algebra.linearMap S (ExteriorAlgebra S Ω[S⁄R])).compDer δ)
      (fun s x ↦ by simpa using Algebra.commutes (δ s) x)
      (((ExteriorAlgebra.ι S).restrictScalars k).comp (δ.kaehlerLieDeriv hδ))
      (fun s ω ↦ by simp [Algebra.smul_def])
      (fun ω ↦ ExteriorAlgebra.ι_add_mul_swap (δ.kaehlerLieDeriv hδ ω) ω) x y

/-- `δ.deRhamLieDeriv hδ` belongs to the Lie algebra of `k`-derivations of
`ExteriorAlgebra S Ω[S⁄R]`. -/
theorem deRhamLieDeriv_mem_derivationLieAlgebra (δ : Derivation k S S)
    (hδ : ∀ r : R, KaehlerDifferential.D R S (δ (algebraMap R S r)) = 0) :
    δ.deRhamLieDeriv hδ ∈ TauCeti.derivationLieAlgebra k (ExteriorAlgebra S Ω[S⁄R]) :=
  TauCeti.mem_derivationLieAlgebra.mpr (δ.deRhamLieDeriv_mul hδ)

/-- Scalar multiplication by `s : S` obeys `L_δ (s • x) = δ s • x + s • L_δ x`. -/
@[simp]
theorem deRhamLieDeriv_smul (δ : Derivation k S S)
    (hδ : ∀ r : R, KaehlerDifferential.D R S (δ (algebraMap R S r)) = 0)
    (s : S) (x : ExteriorAlgebra S Ω[S⁄R]) :
    δ.deRhamLieDeriv hδ (s • x) = δ s • x + s • δ.deRhamLieDeriv hδ x := by
  rw [Algebra.smul_def, deRhamLieDeriv_mul, deRhamLieDeriv_algebraMap, ← Algebra.smul_def,
    ← Algebra.smul_def]

/-- `δ.deRhamLieDeriv hδ` preserves each exterior power `⋀[S]^n Ω[S⁄R]`. -/
theorem deRhamLieDeriv_mem_exteriorPower (δ : Derivation k S S)
    (hδ : ∀ r : R, KaehlerDifferential.D R S (δ (algebraMap R S r)) = 0)
    {n : ℕ} {x : ExteriorAlgebra S Ω[S⁄R]} (hx : x ∈ ⋀[S]^n Ω[S⁄R]) :
    δ.deRhamLieDeriv hδ x ∈ ⋀[S]^n Ω[S⁄R] := by
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap s =>
    rw [deRhamLieDeriv_algebraMap, _root_.ExteriorAlgebra.exteriorPower, pow_zero]
    exact Submodule.algebraMap_mem (δ s)
  | add x y i _ _ ihx ihy =>
    rw [map_add]
    exact add_mem ihx ihy
  | mem_mul m hm i x hx ih =>
    obtain ⟨ω, rfl⟩ := hm
    rw [deRhamLieDeriv_mul, deRhamLieDeriv_ι, Nat.succ_eq_one_add]
    exact add_mem
      (SetLike.mul_mem_graded (TauCeti.ExteriorAlgebra.ι_mem_exteriorPower_one _) hx)
      (SetLike.mul_mem_graded (TauCeti.ExteriorAlgebra.ι_mem_exteriorPower_one _) ih)

/-- `δ.deRhamLieDeriv hδ` preserves each homogeneous piece `grading R S p`. -/
theorem deRhamLieDeriv_mem_grading (δ : Derivation k S S)
    (hδ : ∀ r : R, KaehlerDifferential.D R S (δ (algebraMap R S r)) = 0)
    {p : ℤ} {x : ExteriorAlgebra S Ω[S⁄R]} (hx : x ∈ grading R S p) :
    δ.deRhamLieDeriv hδ x ∈ grading R S p := by
  rcases lt_or_ge p 0 with hp | hp
  · rw [grading_of_neg hp, Submodule.mem_bot] at hx
    rw [hx, map_zero]
    exact zero_mem _
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hp
    rw [mem_grading_natCast] at hx ⊢
    exact δ.deRhamLieDeriv_mem_exteriorPower hδ hx

/-- `δ.deRhamLieDeriv hδ` commutes with the grade involution on `ExteriorAlgebra S Ω[S⁄R]`. -/
theorem deRhamLieDeriv_involute (δ : Derivation k S S)
    (hδ : ∀ r : R, KaehlerDifferential.D R S (δ (algebraMap R S r)) = 0)
    (x : ExteriorAlgebra S Ω[S⁄R]) :
    δ.deRhamLieDeriv hδ (involute (Q := (0 : QuadraticForm S Ω[S⁄R])) x) =
      involute (Q := (0 : QuadraticForm S Ω[S⁄R])) (δ.deRhamLieDeriv hδ x) := by
  induction x using CliffordAlgebra.induction with
  | algebraMap s => rw [AlgHom.commutes, deRhamLieDeriv_algebraMap, AlgHom.commutes]
  | ι ω => rw [involute_ι, map_neg, deRhamLieDeriv_ι, involute_ι]
  | mul x y ihx ihy =>
    rw [map_mul, deRhamLieDeriv_mul, ihx, ihy, deRhamLieDeriv_mul, map_add, map_mul, map_mul]
  | add x y ihx ihy =>
    rw [map_add, map_add, ihx, ihy, ← map_add involute, ← map_add (δ.deRhamLieDeriv hδ)]

/-- **The exterior derivative commutes with the Lie derivative** on `ExteriorAlgebra S Ω[S⁄R]`. -/
theorem extDeriv_deRhamLieDeriv (δ : Derivation k S S)
    (hδ : ∀ r : R, KaehlerDifferential.D R S (δ (algebraMap R S r)) = 0)
    (x : ExteriorAlgebra S Ω[S⁄R]) :
    extDeriv R S (δ.deRhamLieDeriv hδ x) = δ.deRhamLieDeriv hδ (extDeriv R S x) := by
  induction x using TauCeti.KaehlerDeRham.inductionOn with
  | algebraMap s => simp
  | ι_D s => simp
  | mul x y ihx ihy =>
    simp only [deRhamLieDeriv_mul, extDeriv_mul, map_add, ihx, ihy, deRhamLieDeriv_involute]
    abel
  | add x y ihx ihy => simp [ihx, ihy]

/-- **Uniqueness of the Lie derivative on the algebraic de Rham complex**: `δ.deRhamLieDeriv hδ`
is the unique `k`-linear algebra derivation of `ExteriorAlgebra S Ω[S⁄R]` that extends `δ` on `S`
and commutes with `extDeriv R S`. -/
theorem deRhamLieDeriv_unique (δ : Derivation k S S)
    (hδ : ∀ r : R, KaehlerDifferential.D R S (δ (algebraMap R S r)) = 0)
    {L : Module.End k (ExteriorAlgebra S Ω[S⁄R])}
    (hder : L ∈ TauCeti.derivationLieAlgebra k (ExteriorAlgebra S Ω[S⁄R]))
    (halg : ∀ s : S,
      L (algebraMap S (ExteriorAlgebra S Ω[S⁄R]) s) =
        algebraMap S (ExteriorAlgebra S Ω[S⁄R]) (δ s))
    (hcomm : ∀ x : ExteriorAlgebra S Ω[S⁄R], extDeriv R S (L x) = L (extDeriv R S x)) :
    L = δ.deRhamLieDeriv hδ := by
  have hleib := TauCeti.mem_derivationLieAlgebra.mp hder
  refine LinearMap.ext fun x ↦ ?_
  induction x using TauCeti.KaehlerDeRham.inductionOn with
  | algebraMap s => rw [halg, deRhamLieDeriv_algebraMap]
  | ι_D s =>
    rw [← extDeriv_algebraMap, ← hcomm, halg, extDeriv_algebraMap, extDeriv_algebraMap,
      deRhamLieDeriv_ι_D]
  | mul x y ihx ihy => rw [hleib, deRhamLieDeriv_mul, ihx, ihy]
  | add x y ihx ihy => rw [map_add, map_add, ihx, ihy]

/-- `deRhamLieDeriv` is additive in the derivation `δ`. -/
theorem deRhamLieDeriv_add {δ₁ δ₂ : Derivation k S S}
    (h₁ : ∀ r : R, KaehlerDifferential.D R S (δ₁ (algebraMap R S r)) = 0)
    (h₂ : ∀ r : R, KaehlerDifferential.D R S (δ₂ (algebraMap R S r)) = 0) :
    (δ₁ + δ₂).deRhamLieDeriv (fun r ↦ by simp [h₁ r, h₂ r]) =
      δ₁.deRhamLieDeriv h₁ + δ₂.deRhamLieDeriv h₂ := by
  symm
  refine deRhamLieDeriv_unique (δ₁ + δ₂) _
    (Submodule.add_mem _ (δ₁.deRhamLieDeriv_mem_derivationLieAlgebra h₁)
      (δ₂.deRhamLieDeriv_mem_derivationLieAlgebra h₂))
    (fun s ↦ by simp)
    fun x ↦ ?_
  rw [LinearMap.add_apply, map_add, extDeriv_deRhamLieDeriv, extDeriv_deRhamLieDeriv,
    LinearMap.add_apply]

/-- `deRhamLieDeriv` maps the zero derivation to zero. -/
@[simp]
theorem deRhamLieDeriv_zero :
    (0 : Derivation k S S).deRhamLieDeriv (fun _ : R ↦ by simp) = 0 := by
  symm
  exact deRhamLieDeriv_unique 0 (fun _ : R ↦ by simp) (Submodule.zero_mem _)
    (fun _ ↦ by simp) (fun _ ↦ by simp)

/-- **Lie bracket preservation (`L_{⁅δ₁, δ₂⁆} = [L_{δ₁}, L_{δ₂}]`)**: the Lie derivative of a
commutator of `k`-derivations of `S` is the commutator of their Lie derivatives on
`ExteriorAlgebra S Ω[S⁄R]`. -/
theorem deRhamLieDeriv_commutator {δ₁ δ₂ : Derivation k S S}
    (h₁ : ∀ r : R, KaehlerDifferential.D R S (δ₁ (algebraMap R S r)) = 0)
    (h₂ : ∀ r : R, KaehlerDifferential.D R S (δ₂ (algebraMap R S r)) = 0) :
    (⁅δ₁, δ₂⁆).deRhamLieDeriv (D_commutator_algebraMap_eq_zero h₁ h₂) =
      (δ₁.deRhamLieDeriv h₁).comp (δ₂.deRhamLieDeriv h₂) -
        (δ₂.deRhamLieDeriv h₂).comp (δ₁.deRhamLieDeriv h₁) := by
  let L₁ : TauCeti.derivationLieAlgebra k (ExteriorAlgebra S Ω[S⁄R]) :=
    ⟨δ₁.deRhamLieDeriv h₁, δ₁.deRhamLieDeriv_mem_derivationLieAlgebra h₁⟩
  let L₂ : TauCeti.derivationLieAlgebra k (ExteriorAlgebra S Ω[S⁄R]) :=
    ⟨δ₂.deRhamLieDeriv h₂, δ₂.deRhamLieDeriv_mem_derivationLieAlgebra h₂⟩
  have hbr : (⁅L₁, L₂⁆ : TauCeti.derivationLieAlgebra k (ExteriorAlgebra S Ω[S⁄R])).1 =
      (δ₁.deRhamLieDeriv h₁).comp (δ₂.deRhamLieDeriv h₂) -
        (δ₂.deRhamLieDeriv h₂).comp (δ₁.deRhamLieDeriv h₁) :=
    LinearMap.ext fun _ ↦ by
      simp [LieSubalgebra.coe_bracket, Ring.lie_def, _root_.mul_apply_eq_comp, L₁, L₂]
  rw [← hbr]
  symm
  refine deRhamLieDeriv_unique ⁅δ₁, δ₂⁆ _ ⁅L₁, L₂⁆.2 (fun s ↦ ?_) (fun x ↦ ?_)
  · simp [hbr, Derivation.commutator_apply]
  · simp [hbr, extDeriv_deRhamLieDeriv]

/-- **Commuting derivations lift to commuting Lie derivatives** on the algebraic de Rham complex. -/
theorem commute_deRhamLieDeriv_of_bracket_eq_zero {δ₁ δ₂ : Derivation k S S}
    (h₁ : ∀ r : R, KaehlerDifferential.D R S (δ₁ (algebraMap R S r)) = 0)
    (h₂ : ∀ r : R, KaehlerDifferential.D R S (δ₂ (algebraMap R S r)) = 0)
    (hcomm : ⁅δ₁, δ₂⁆ = 0) :
    Function.Commute (δ₁.deRhamLieDeriv h₁) (δ₂.deRhamLieDeriv h₂) := by
  intro x
  have h := congrFun (congrArg DFunLike.coe (deRhamLieDeriv_commutator h₁ h₂)) x
  have h0 : (⁅δ₁, δ₂⁆).deRhamLieDeriv (D_commutator_algebraMap_eq_zero h₁ h₂) = 0 := by
    symm
    exact deRhamLieDeriv_unique ⁅δ₁, δ₂⁆ _ (Submodule.zero_mem _)
      (fun s ↦ by simp [hcomm]) (fun _ ↦ by simp)
  rw [h0, LinearMap.zero_apply, LinearMap.sub_apply, LinearMap.comp_apply,
    LinearMap.comp_apply] at h
  exact sub_eq_zero.mp h.symm

end Derivation

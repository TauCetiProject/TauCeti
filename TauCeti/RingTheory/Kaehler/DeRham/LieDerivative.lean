/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Derivation.Basic
public import TauCeti.RingTheory.Kaehler.DeRham.Basic
public import TauCeti.RingTheory.Kaehler.LieDeriv
import TauCeti.LinearAlgebra.ExteriorAlgebra.Derivation.Basic
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
  `ExteriorAlgebra S Ω[S⁄R]` by its action on `S` and commutation with `extDeriv R S` on `S`
  (`Derivation.deRhamLieDeriv_unique`);
* `deRhamLieDeriv` respects linearity in the derivation, naturality along `R`-algebra homomorphisms
  (`Derivation.map_deRhamLieDeriv`), and commutators (`Derivation.deRhamLieDeriv_commutator`), so
  commuting derivations of `S` lift to commuting derivations of `ExteriorAlgebra S Ω[S⁄R]`
  (`Derivation.commute_deRhamLieDeriv_of_lie_eq_zero`).

## Main definitions

* `Derivation.deRhamLieDeriv`: Lie derivative on `ExteriorAlgebra S Ω[S⁄R]` along a `k`-derivation
  `δ : Derivation k S S` satisfying `∀ r : R, D R S (δ (algebraMap R S r)) = 0`.

## Main results

* `Derivation.deRhamLieDeriv_mul`, `Derivation.deRhamLieDeriv_smul`: even Leibniz rule and
  `S`-scalar Leibniz rule.
* `Derivation.extDeriv_deRhamLieDeriv`: `extDeriv R S` commutes with `δ.deRhamLieDeriv hδ`.
* `Derivation.deRhamLieDeriv_unique`: uniqueness of `δ.deRhamLieDeriv hδ` as a `k`-derivation of
  `ExteriorAlgebra S Ω[S⁄R]` extending `δ` on `S` and commuting with `extDeriv R S` on `S`.
* `Derivation.deRhamLieDeriv_congr`, `Derivation.deRhamLieDeriv_zero`,
  `Derivation.deRhamLieDeriv_add`, `Derivation.deRhamLieDeriv_neg`,
  `Derivation.deRhamLieDeriv_sub`, `Derivation.deRhamLieDeriv_sum`,
  `Derivation.smul_deRhamLieDeriv`: congruence and linearity in the derivation.
* `Derivation.map_deRhamLieDeriv`: naturality with `TauCeti.KaehlerDeRham.map`.
* `Derivation.deRhamLieDeriv_commutator`: `(⁅δ₁, δ₂⁆).deRhamLieDeriv` is the commutator of
  `δ₁.deRhamLieDeriv` and `δ₂.deRhamLieDeriv`.
* `Derivation.commute_deRhamLieDeriv_of_lie_eq_zero`: commuting derivations of `S` lift to
  commuting Lie derivatives on `ExteriorAlgebra S Ω[S⁄R]`.

## Implementation notes

`Derivation.deRhamLieDeriv` assumes only `[CommRing k]` and `[Algebra k S]` (alongside
`[CommRing R]` and `[Algebra R S]`), without requiring `[Algebra k R]` or `[IsScalarTower k R S]`:
`Ω[S⁄R]` and `ExteriorAlgebra S Ω[S⁄R]` inherit `Module k` and `[IsScalarTower k S _]` directly
from `[Algebra k S]`. The extension from `(δ, δ.kaehlerLieDeriv hδ)` to `ExteriorAlgebra S Ω[S⁄R]`
is obtained from `ExteriorAlgebra.liftTwistedDerivation` with untwisted endomorphism
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
  ExteriorAlgebra.liftTwistedDerivation
    (AlgHom.id S (ExteriorAlgebra S Ω[S⁄R]))
    ((Algebra.linearMap S (ExteriorAlgebra S Ω[S⁄R])).compDer δ)
    (fun s ω ↦ by simpa using Algebra.commutes (δ s) (ExteriorAlgebra.ι S ω))
    (((ExteriorAlgebra.ι S).restrictScalars k).comp (δ.kaehlerLieDeriv hδ))
    (fun s ω ↦ by simp [Algebra.smul_def])
    (fun ω ↦ by simp)

/-- On degree-zero elements `algebraMap S _ s`, `δ.deRhamLieDeriv hδ` acts by `δ`. -/
@[simp]
theorem deRhamLieDeriv_algebraMap (δ : Derivation k S S)
    (hδ : ∀ r : R, KaehlerDifferential.D R S (δ (algebraMap R S r)) = 0) (s : S) :
    δ.deRhamLieDeriv hδ (algebraMap S (ExteriorAlgebra S Ω[S⁄R]) s) =
      algebraMap S (ExteriorAlgebra S Ω[S⁄R]) (δ s) := by
  simp [deRhamLieDeriv]

/-- `δ.deRhamLieDeriv hδ` annihilates `1`. -/
@[simp]
theorem deRhamLieDeriv_one (δ : Derivation k S S)
    (hδ : ∀ r : R, KaehlerDifferential.D R S (δ (algebraMap R S r)) = 0) :
    δ.deRhamLieDeriv hδ 1 = 0 := by
  simp [deRhamLieDeriv]

/-- On `1`-forms `ι ω`, `δ.deRhamLieDeriv hδ` acts through `δ.kaehlerLieDeriv hδ`. -/
@[simp]
theorem deRhamLieDeriv_ι (δ : Derivation k S S)
    (hδ : ∀ r : R, KaehlerDifferential.D R S (δ (algebraMap R S r)) = 0) (ω : Ω[S⁄R]) :
    δ.deRhamLieDeriv hδ (ExteriorAlgebra.ι S ω) =
      ExteriorAlgebra.ι S (δ.kaehlerLieDeriv hδ ω) := by
  simp [deRhamLieDeriv]

/-- **Even Leibniz rule** for `δ.deRhamLieDeriv hδ` on exterior products. -/
@[simp]
theorem deRhamLieDeriv_mul (δ : Derivation k S S)
    (hδ : ∀ r : R, KaehlerDifferential.D R S (δ (algebraMap R S r)) = 0)
    (x y : ExteriorAlgebra S Ω[S⁄R]) :
    δ.deRhamLieDeriv hδ (x * y) =
      δ.deRhamLieDeriv hδ x * y + x * δ.deRhamLieDeriv hδ y :=
  ExteriorAlgebra.liftTwistedDerivation_mul _ _ _ _ _ _ x y

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
  simp [deRhamLieDeriv, ← Algebra.smul_def]

/-- `δ.deRhamLieDeriv hδ` preserves each exterior power `⋀[S]^n Ω[S⁄R]`. -/
theorem deRhamLieDeriv_mem_exteriorPower (δ : Derivation k S S)
    (hδ : ∀ r : R, KaehlerDifferential.D R S (δ (algebraMap R S r)) = 0)
    {n : ℕ} {x : ExteriorAlgebra S Ω[S⁄R]} (hx : x ∈ ⋀[S]^n Ω[S⁄R]) :
    δ.deRhamLieDeriv hδ x ∈ ⋀[S]^n Ω[S⁄R] :=
  ExteriorAlgebra.liftTwistedDerivation_mem_exteriorPower _ _ _ _ _ _ (r := 0)
    (fun ω ↦ by simp)
    (fun s ↦ by
      rw [_root_.ExteriorAlgebra.exteriorPower, pow_zero]
      exact Submodule.algebraMap_mem (δ s))
    (fun ω ↦ by simp)
    hx

/-- `δ.deRhamLieDeriv hδ` preserves each homogeneous piece `grading R S p`. -/
theorem deRhamLieDeriv_mem_grading (δ : Derivation k S S)
    (hδ : ∀ r : R, KaehlerDifferential.D R S (δ (algebraMap R S r)) = 0)
    {p : ℤ} {x : ExteriorAlgebra S Ω[S⁄R]} (hx : x ∈ grading R S p) :
    δ.deRhamLieDeriv hδ x ∈ grading R S p := by
  simpa [deRhamLieDeriv] using mem_grading_iff.mpr <|
    ExteriorAlgebra.liftTwistedDerivation_mem_integerGrading _ _ _ _ _ _ (r := 0)
      (fun ω ↦ by simpa using TauCeti.ExteriorAlgebra.ι_mem_integerGrading_one ω)
      (fun s ↦ by simpa using mem_grading_iff.mp (algebraMap_mem_grading_zero (R := R) (δ s)))
      (fun ω ↦ by
        simpa using TauCeti.ExteriorAlgebra.ι_mem_integerGrading_one (δ.kaehlerLieDeriv hδ ω))
      (mem_grading_iff.mp hx)

/-- `δ.deRhamLieDeriv hδ` commutes with the grade involution on `ExteriorAlgebra S Ω[S⁄R]`. -/
theorem deRhamLieDeriv_involute (δ : Derivation k S S)
    (hδ : ∀ r : R, KaehlerDifferential.D R S (δ (algebraMap R S r)) = 0)
    (x : ExteriorAlgebra S Ω[S⁄R]) :
    δ.deRhamLieDeriv hδ (involute (Q := (0 : QuadraticForm S Ω[S⁄R])) x) =
      involute (Q := (0 : QuadraticForm S Ω[S⁄R])) (δ.deRhamLieDeriv hδ x) := by
  simpa using ExteriorAlgebra.map_involute_of_map_mem_integerGrading (δ.deRhamLieDeriv hδ)
    0 (fun hx ↦ by
      simpa using mem_grading_iff.mp (δ.deRhamLieDeriv_mem_grading hδ (mem_grading_iff.mpr hx))) x

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
and commutes with `extDeriv R S` on `S`. -/
theorem deRhamLieDeriv_unique (δ : Derivation k S S)
    (hδ : ∀ r : R, KaehlerDifferential.D R S (δ (algebraMap R S r)) = 0)
    {L : Module.End k (ExteriorAlgebra S Ω[S⁄R])}
    (hder : L ∈ TauCeti.derivationLieAlgebra k (ExteriorAlgebra S Ω[S⁄R]))
    (halg : ∀ s : S,
      L (algebraMap S (ExteriorAlgebra S Ω[S⁄R]) s) =
        algebraMap S (ExteriorAlgebra S Ω[S⁄R]) (δ s))
    (hcomm : ∀ s : S,
      extDeriv R S (L (algebraMap S (ExteriorAlgebra S Ω[S⁄R]) s)) =
        L (extDeriv R S (algebraMap S (ExteriorAlgebra S Ω[S⁄R]) s))) :
    L = δ.deRhamLieDeriv hδ := by
  have hleib := TauCeti.mem_derivationLieAlgebra.mp hder
  refine LinearMap.ext fun x ↦ ?_
  induction x using TauCeti.KaehlerDeRham.inductionOn with
  | algebraMap s => rw [halg, deRhamLieDeriv_algebraMap]
  | ι_D s =>
    rw [← extDeriv_algebraMap, ← hcomm, halg]
    simp
  | mul x y ihx ihy => rw [hleib, deRhamLieDeriv_mul, ihx, ihy]
  | add x y ihx ihy => rw [map_add, map_add, ihx, ihy]

/-- `deRhamLieDeriv` depends only on the derivation, not on the lift-condition proof. -/
theorem deRhamLieDeriv_congr {δ₁ δ₂ : Derivation k S S}
    (h₁ : ∀ r : R, KaehlerDifferential.D R S (δ₁ (algebraMap R S r)) = 0)
    (h₂ : ∀ r : R, KaehlerDifferential.D R S (δ₂ (algebraMap R S r)) = 0)
    (h : δ₁ = δ₂) :
    δ₁.deRhamLieDeriv h₁ = δ₂.deRhamLieDeriv h₂ := by
  subst h
  rfl

/-- `deRhamLieDeriv` maps the zero derivation to zero. -/
@[simp]
theorem deRhamLieDeriv_zero
    (h₀ : ∀ r : R, KaehlerDifferential.D R S ((0 : Derivation k S S) (algebraMap R S r)) = 0) :
    (0 : Derivation k S S).deRhamLieDeriv h₀ = 0 :=
  ((0 : Derivation k S S).deRhamLieDeriv_unique h₀ (Submodule.zero_mem _)
    (fun _ ↦ by simp) (fun _ ↦ by simp)).symm

/-- `deRhamLieDeriv` is additive in the derivation `δ`. -/
theorem deRhamLieDeriv_add {δ₁ δ₂ : Derivation k S S}
    (h₁ : ∀ r : R, KaehlerDifferential.D R S (δ₁ (algebraMap R S r)) = 0)
    (h₂ : ∀ r : R, KaehlerDifferential.D R S (δ₂ (algebraMap R S r)) = 0) :
    (δ₁ + δ₂).deRhamLieDeriv (D_add_algebraMap_eq_zero h₁ h₂) =
      δ₁.deRhamLieDeriv h₁ + δ₂.deRhamLieDeriv h₂ := by
  symm
  refine deRhamLieDeriv_unique (δ₁ + δ₂) _
    (Submodule.add_mem _ (δ₁.deRhamLieDeriv_mem_derivationLieAlgebra h₁)
      (δ₂.deRhamLieDeriv_mem_derivationLieAlgebra h₂))
    (fun s ↦ by simp)
    fun s ↦ by simp

/-- `deRhamLieDeriv` respects negation of the derivation `δ`. -/
theorem deRhamLieDeriv_neg {δ : Derivation k S S}
    (hδ : ∀ r : R, KaehlerDifferential.D R S (δ (algebraMap R S r)) = 0) :
    (-δ).deRhamLieDeriv (D_neg_algebraMap_eq_zero hδ) = -δ.deRhamLieDeriv hδ := by
  symm
  refine deRhamLieDeriv_unique (-δ) _
    (Submodule.neg_mem _ (δ.deRhamLieDeriv_mem_derivationLieAlgebra hδ))
    (fun s ↦ by simp)
    fun s ↦ by simp

/-- `deRhamLieDeriv` respects subtraction of derivations. -/
theorem deRhamLieDeriv_sub {δ₁ δ₂ : Derivation k S S}
    (h₁ : ∀ r : R, KaehlerDifferential.D R S (δ₁ (algebraMap R S r)) = 0)
    (h₂ : ∀ r : R, KaehlerDifferential.D R S (δ₂ (algebraMap R S r)) = 0) :
    (δ₁ - δ₂).deRhamLieDeriv (D_sub_algebraMap_eq_zero h₁ h₂) =
      δ₁.deRhamLieDeriv h₁ - δ₂.deRhamLieDeriv h₂ := by
  rw [deRhamLieDeriv_congr _ (D_add_algebraMap_eq_zero h₁ (D_neg_algebraMap_eq_zero h₂))
    (sub_eq_add_neg δ₁ δ₂), deRhamLieDeriv_add h₁ (D_neg_algebraMap_eq_zero h₂),
    deRhamLieDeriv_neg h₂, ← sub_eq_add_neg]

/-- `deRhamLieDeriv` respects finite sums of derivations. -/
theorem deRhamLieDeriv_sum {ι : Type*} (t : Finset ι) (δ : ι → Derivation k S S)
    (hδ : ∀ i ∈ t, ∀ r : R, KaehlerDifferential.D R S (δ i (algebraMap R S r)) = 0) :
    (∑ i ∈ t, δ i).deRhamLieDeriv (D_sum_algebraMap_eq_zero t δ hδ) =
      ∑ i ∈ t.attach, (δ i.val).deRhamLieDeriv (hδ i.val i.property) := by
  symm
  refine deRhamLieDeriv_unique (∑ i ∈ t, δ i) _
    (Submodule.sum_mem _ fun i _ ↦
      (δ i.val).deRhamLieDeriv_mem_derivationLieAlgebra (hδ i.val i.property))
    (fun s ↦ by simp [Finset.sum_attach t (fun i ↦ algebraMap S _ (δ i s))])
    fun s ↦ by simp [map_sum]

/-- In a scalar tower `k → R → S`, `deRhamLieDeriv` is `k`-linear in the derivation `δ`. -/
theorem smul_deRhamLieDeriv [Algebra k R] [IsScalarTower k R S] (c : k) {δ : Derivation k S S}
    (hδ : ∀ r : R, KaehlerDifferential.D R S (δ (algebraMap R S r)) = 0) :
    (c • δ).deRhamLieDeriv (D_smul_algebraMap_eq_zero c hδ) = c • δ.deRhamLieDeriv hδ := by
  symm
  refine deRhamLieDeriv_unique (c • δ) _
    (Submodule.smul_mem _ c (δ.deRhamLieDeriv_mem_derivationLieAlgebra hδ))
    (fun s ↦ ?_) fun s ↦ ?_
  · rw [LinearMap.smul_apply, deRhamLieDeriv_algebraMap, _root_.smul_apply,
      Algebra.algebraMap_eq_smul_one, ← smul_assoc, ← Algebra.algebraMap_eq_smul_one]
  · simp only [LinearMap.smul_apply]
    rw [← IsScalarTower.algebraMap_smul R c, LinearMap.map_smul, extDeriv_deRhamLieDeriv,
      IsScalarTower.algebraMap_smul]

/-- **Naturality of `deRhamLieDeriv` along an `R`-algebra homomorphism**: if `f : A →ₐ[R] B`
intertwines derivations `δA` and `δB`, then `TauCeti.KaehlerDeRham.map f` intertwines their
de Rham Lie derivatives. -/
theorem map_deRhamLieDeriv {kA kB R A B : Type*}
    [CommRing kA] [CommRing kB] [CommRing R] [CommRing A] [CommRing B]
    [Algebra kA A] [Algebra kB B] [Algebra R A] [Algebra R B]
    (f : A →ₐ[R] B) {δA : Derivation kA A A} {δB : Derivation kB B B}
    (hA : ∀ r : R, KaehlerDifferential.D R A (δA (algebraMap R A r)) = 0)
    (hB : ∀ r : R, KaehlerDifferential.D R B (δB (algebraMap R B r)) = 0)
    (hf : ∀ a : A, f (δA a) = δB (f a)) (x : ExteriorAlgebra A Ω[A⁄R]) :
    TauCeti.KaehlerDeRham.map f (δA.deRhamLieDeriv hA x) =
      δB.deRhamLieDeriv hB (TauCeti.KaehlerDeRham.map f x) := by
  induction x using TauCeti.KaehlerDeRham.inductionOn with
  | algebraMap a => simp [hf]
  | ι_D a =>
    simp only [deRhamLieDeriv_ι, kaehlerLieDeriv_D, map_ι, KaehlerDifferential.mapSemilinear_D, hf]
  | mul x y ihx ihy => simp [ihx, ihy]
  | add x y ihx ihy => simp [ihx, ihy]

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
  have hbr : (⁅L₁, L₂⁆ : TauCeti.derivationLieAlgebra k (ExteriorAlgebra S Ω[S⁄R])).val =
      (δ₁.deRhamLieDeriv h₁).comp (δ₂.deRhamLieDeriv h₂) -
        (δ₂.deRhamLieDeriv h₂).comp (δ₁.deRhamLieDeriv h₁) :=
    LinearMap.ext fun _ ↦ by
      simp [LieSubalgebra.coe_bracket, Ring.lie_def, _root_.mul_apply_eq_comp, L₁, L₂]
  rw [← hbr]
  symm
  refine deRhamLieDeriv_unique ⁅δ₁, δ₂⁆ _ ⁅L₁, L₂⁆.property (fun s ↦ ?_) (fun s ↦ ?_)
  · simp [hbr, Derivation.commutator_apply]
  · simp [hbr]

/-- **Commuting derivations lift to commuting Lie derivatives** on the algebraic de Rham complex. -/
theorem commute_deRhamLieDeriv_of_lie_eq_zero {δ₁ δ₂ : Derivation k S S}
    (h₁ : ∀ r : R, KaehlerDifferential.D R S (δ₁ (algebraMap R S r)) = 0)
    (h₂ : ∀ r : R, KaehlerDifferential.D R S (δ₂ (algebraMap R S r)) = 0)
    (hcomm : ⁅δ₁, δ₂⁆ = 0) :
    Function.Commute (δ₁.deRhamLieDeriv h₁) (δ₂.deRhamLieDeriv h₂) := by
  intro x
  have h := LinearMap.congr_fun (deRhamLieDeriv_commutator h₁ h₂) x
  rw [deRhamLieDeriv_congr _ (fun _ ↦ by simp) hcomm] at h
  simp only [deRhamLieDeriv_zero, LinearMap.zero_apply, LinearMap.sub_apply,
    LinearMap.comp_apply] at h
  exact sub_eq_zero.mp h.symm

end Derivation

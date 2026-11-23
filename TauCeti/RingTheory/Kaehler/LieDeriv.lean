/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Derivation.Lie
public import TauCeti.RingTheory.Kaehler.Basic
public import TauCeti.RingTheory.Kaehler.MapSemilinear

/-!
# Lie derivatives on Kähler differentials

Let `R` and `S` be commutative rings with `[Algebra R S]`, and let `δ : Derivation k S S` be a
`k`-derivation of `S` over any commutative ring `k` with `[Algebra k S]` (without requiring `δ` to
vanish on `R`, covering lifted base/total derivations in a ring tower `k → R → S` as well as
relative derivations `Derivation R S S`).

A `k`-linear endomorphism `L` of `Ω[S⁄R]` satisfying `L (D R S s) = D R S (δ s)` exists **if and
only if** `∀ r : R, D R S (δ (algebraMap R S r)) = 0` (`Derivation.exists_apply_D_eq_iff`).
This condition holds automatically for relative derivations `δ : Derivation R S S`
(`Derivation.D_apply_algebraMap_eq_zero`), for compatible derivation pairs in
`Derivation.couple k R S` (`Derivation.Compatible.D_apply_algebraMap_eq_zero`), and is closed under
addition, negation, subtraction, finite sums, `k`-scalar multiplication in a tower `k → R → S`, and
Lie brackets (`Derivation.D_commutator_algebraMap_eq_zero`).

Whenever the condition holds, `δ.kaehlerLieDeriv hδ : Module.End k Ω[S⁄R]` is constructed by
descending `single x c ↦ δ c • D R S x + c • D R S (δ x)` through
`TauCeti.KaehlerDifferential.liftOfKerTotal`, obeys the module Leibniz rule
`L (s • ω) = δ s • ω + s • L ω`, is uniquely characterized by these two properties, respects
linearity, commutators (`Derivation.kaehlerLieDeriv_commutator`), and pullback along `R`-algebra
homomorphisms (`Derivation.mapSemilinear_kaehlerLieDeriv`).

## Main definitions

* `Derivation.kaehlerLieDeriv`: Lie derivative on `Ω[S⁄R]` along `δ : Derivation k S S` satisfying
  `∀ r : R, D R S (δ (algebraMap R S r)) = 0`.

## Main results

* `Derivation.kaehlerLieDeriv_D`, `Derivation.kaehlerLieDeriv_smul`: action on exact differentials
  and `S`-scalar Leibniz rule.
* `Derivation.exists_apply_D_eq_iff`: exact criterion for a `k`-linear endomorphism `L` of
  `Ω[S⁄R]` to satisfy `L (D R S s) = D R S (δ s)`.
* `Derivation.kaehlerLieDeriv_unique`: uniqueness of `δ.kaehlerLieDeriv hδ`.
* `Derivation.kaehlerLieDeriv_congr`, `Derivation.kaehlerLieDeriv_zero`,
  `Derivation.kaehlerLieDeriv_add`, `Derivation.kaehlerLieDeriv_neg`,
  `Derivation.kaehlerLieDeriv_sub`, `Derivation.kaehlerLieDeriv_sum`,
  `Derivation.smul_kaehlerLieDeriv`: congruence and linearity in the derivation.
* `Derivation.kaehlerLieDeriv_commutator`: `(⁅δ₁, δ₂⁆).kaehlerLieDeriv` is the commutator of
  `δ₁.kaehlerLieDeriv` and `δ₂.kaehlerLieDeriv`.
* `Derivation.mapSemilinear_kaehlerLieDeriv`: naturality with `KaehlerDifferential.mapSemilinear`.

## References

* N. Bourbaki, *Algebra*, Chapter III, §10.
* I. M. Anderson, *The Variational Bicomplex*, Chapter 1.
-/

public section

namespace Derivation

variable {k R S : Type*} [CommRing k] [CommRing R] [CommRing S] [Algebra k S] [Algebra R S]

/-- Auxiliary `k`-linear map `(S →₀ S) →ₗ[k] Ω[S⁄R]` sending `single x c` to
`δ c • D R S x + c • D R S (δ x)`. -/
private noncomputable def preKaehlerLieDeriv (R : Type*) [CommRing R] [Algebra R S]
    (δ : Derivation k S S) : (S →₀ S) →ₗ[k] Ω[S⁄R] :=
  Finsupp.lsum k fun x : S ↦
    ((LinearMap.lsmul S Ω[S⁄R]).restrictScalars k).flip (KaehlerDifferential.D R S x) ∘ₗ
      δ.toLinearMap +
      ((LinearMap.lsmul S Ω[S⁄R]).restrictScalars k).flip (KaehlerDifferential.D R S (δ x))

private theorem preKaehlerLieDeriv_single (δ : Derivation k S S) (x c : S) :
    preKaehlerLieDeriv R δ (Finsupp.single x c) =
      δ c • KaehlerDifferential.D R S x + c • KaehlerDifferential.D R S (δ x) := by
  simp [preKaehlerLieDeriv]

private theorem preKaehlerLieDeriv_smul (δ : Derivation k S S) (s : S) (v : S →₀ S) :
    preKaehlerLieDeriv R δ (s • v) =
      s • preKaehlerLieDeriv R δ v +
        δ s • Finsupp.linearCombination S (KaehlerDifferential.D R S) v := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v₁ v₂ ih₁ ih₂ =>
    simp only [smul_add, map_add, ih₁, ih₂]
    abel
  | single x c =>
    simp only [Finsupp.smul_single, smul_eq_mul, preKaehlerLieDeriv_single,
      Finsupp.linearCombination_single, δ.leibniz, add_smul, smul_add, smul_smul, mul_comm c (δ s)]
    abel

private theorem preKaehlerLieDeriv_eq_zero_of_mem_kerTotal (δ : Derivation k S S)
    (hδ : ∀ r : R, KaehlerDifferential.D R S (δ (algebraMap R S r)) = 0)
    {v : S →₀ S} (hv : v ∈ KaehlerDifferential.kerTotal R S) :
    preKaehlerLieDeriv R δ v = 0 :=
  TauCeti.KaehlerDifferential.map_eq_zero_of_mem_kerTotal (preKaehlerLieDeriv R δ)
    (fun _ _ ↦ by
      simp only [map_sub, map_add, preKaehlerLieDeriv_single, Derivation.map_one_eq_zero,
        zero_smul, zero_add, one_smul]
      abel)
    (fun _ _ ↦ by
      simp only [map_sub, map_add, preKaehlerLieDeriv_single, Derivation.map_one_eq_zero,
        zero_smul, zero_add, one_smul, δ.leibniz, smul_eq_mul, Derivation.leibniz]
      abel)
    (fun r ↦ by simp [preKaehlerLieDeriv_single, hδ r])
    (fun s v hker ih ↦ by simp [preKaehlerLieDeriv_smul, ih, hker])
    hv

/-- **Lie derivative on Kähler differentials**: for a `k`-derivation `δ : Derivation k S S` such
that `D R S (δ (algebraMap R S r)) = 0` for all `r : R`, `δ.kaehlerLieDeriv hδ` is the unique
`k`-linear endomorphism of `Ω[S⁄R]` sending `D R S s` to `D R S (δ s)` and obeying the `S`-module
Leibniz rule `L (s • ω) = δ s • ω + s • L ω`. -/
noncomputable def kaehlerLieDeriv (δ : Derivation k S S)
    (hδ : ∀ r : R, KaehlerDifferential.D R S (δ (algebraMap R S r)) = 0) :
    Module.End k Ω[S⁄R] :=
  TauCeti.KaehlerDifferential.liftOfKerTotal R (preKaehlerLieDeriv R δ)
    fun _ hv ↦ preKaehlerLieDeriv_eq_zero_of_mem_kerTotal δ hδ hv

/-- On exact Kähler differentials `D R S s`, `δ.kaehlerLieDeriv hδ` acts by `D R S (δ s)`. -/
@[simp]
theorem kaehlerLieDeriv_D (δ : Derivation k S S)
    (hδ : ∀ r : R, KaehlerDifferential.D R S (δ (algebraMap R S r)) = 0) (s : S) :
    δ.kaehlerLieDeriv hδ (KaehlerDifferential.D R S s) = KaehlerDifferential.D R S (δ s) := by
  simp [kaehlerLieDeriv, preKaehlerLieDeriv_single]

/-- **Leibniz rule for scalar multiplication on `Ω[S⁄R]`**:
`δ.kaehlerLieDeriv hδ (s • ω) = δ s • ω + s • δ.kaehlerLieDeriv hδ ω`. -/
@[simp]
theorem kaehlerLieDeriv_smul (δ : Derivation k S S)
    (hδ : ∀ r : R, KaehlerDifferential.D R S (δ (algebraMap R S r)) = 0)
    (s : S) (ω : Ω[S⁄R]) :
    δ.kaehlerLieDeriv hδ (s • ω) = δ s • ω + s • δ.kaehlerLieDeriv hδ ω := by
  obtain ⟨v, rfl⟩ := KaehlerDifferential.linearCombination_surjective R S ω
  rw [← LinearMap.map_smul, kaehlerLieDeriv,
    TauCeti.KaehlerDifferential.liftOfKerTotal_linearCombination,
    TauCeti.KaehlerDifferential.liftOfKerTotal_linearCombination, preKaehlerLieDeriv_smul, add_comm]

/-- **Necessary and sufficient condition for lifting a `k`-derivation of `S` to `Ω[S⁄R]`**:
there exists a `k`-linear endomorphism `L` of `Ω[S⁄R]` satisfying `L (D R S s) = D R S (δ s)` for
all `s : S` if and only if `D R S (δ (algebraMap R S r)) = 0` for all `r : R`. -/
theorem exists_apply_D_eq_iff (δ : Derivation k S S) :
    (∃ L : Module.End k Ω[S⁄R],
      ∀ s : S, L (KaehlerDifferential.D R S s) = KaehlerDifferential.D R S (δ s)) ↔
      ∀ r : R, KaehlerDifferential.D R S (δ (algebraMap R S r)) = 0 :=
  ⟨fun ⟨L, hL⟩ r ↦ by rw [← hL, Derivation.map_algebraMap, map_zero],
    fun hδ ↦ ⟨δ.kaehlerLieDeriv hδ, δ.kaehlerLieDeriv_D hδ⟩⟩

/-- Uniqueness of `δ.kaehlerLieDeriv hδ` from its action on `D R S s` and the `S`-module Leibniz
rule. -/
theorem kaehlerLieDeriv_unique (δ : Derivation k S S)
    (hδ : ∀ r : R, KaehlerDifferential.D R S (δ (algebraMap R S r)) = 0)
    {L : Module.End k Ω[S⁄R]}
    (hD : ∀ s : S, L (KaehlerDifferential.D R S s) = KaehlerDifferential.D R S (δ s))
    (hsmul : ∀ (s : S) (ω : Ω[S⁄R]), L (s • ω) = δ s • ω + s • L ω) :
    L = δ.kaehlerLieDeriv hδ := by
  refine LinearMap.ext fun ω ↦ ?_
  induction ω using KaehlerDifferential.inductionOn with
  | D s => rw [hD, kaehlerLieDeriv_D]
  | smul s ω ih => rw [hsmul, kaehlerLieDeriv_smul, ih]
  | add _ _ ih₁ ih₂ => rw [map_add, map_add, ih₁, ih₂]

/-- `kaehlerLieDeriv` depends only on the derivation, not on the lift-condition proof. -/
theorem kaehlerLieDeriv_congr {δ₁ δ₂ : Derivation k S S}
    (h₁ : ∀ r : R, KaehlerDifferential.D R S (δ₁ (algebraMap R S r)) = 0)
    (h₂ : ∀ r : R, KaehlerDifferential.D R S (δ₂ (algebraMap R S r)) = 0)
    (h : δ₁ = δ₂) :
    δ₁.kaehlerLieDeriv h₁ = δ₂.kaehlerLieDeriv h₂ := by
  subst h
  rfl

/-- Every `R`-linear derivation `δ : Derivation R S S` automatically satisfies the lift condition
`D R S (δ (algebraMap R S r)) = 0`. -/
theorem D_apply_algebraMap_eq_zero (δ : Derivation R S S) (r : R) :
    KaehlerDifferential.D R S (δ (algebraMap R S r)) = 0 := by
  rw [Derivation.map_algebraMap, map_zero]

/-- If `δ₁, δ₂ : Derivation k S S` satisfy the lift condition for `Ω[S⁄R]`, so does `δ₁ + δ₂`. -/
theorem D_add_algebraMap_eq_zero {δ₁ δ₂ : Derivation k S S}
    (h₁ : ∀ r : R, KaehlerDifferential.D R S (δ₁ (algebraMap R S r)) = 0)
    (h₂ : ∀ r : R, KaehlerDifferential.D R S (δ₂ (algebraMap R S r)) = 0) (r : R) :
    KaehlerDifferential.D R S ((δ₁ + δ₂) (algebraMap R S r)) = 0 := by
  simp [h₁ r, h₂ r]

/-- If `δ : Derivation k S S` satisfies the lift condition for `Ω[S⁄R]`, so does `-δ`. -/
theorem D_neg_algebraMap_eq_zero {δ : Derivation k S S}
    (hδ : ∀ r : R, KaehlerDifferential.D R S (δ (algebraMap R S r)) = 0) (r : R) :
    KaehlerDifferential.D R S ((-δ) (algebraMap R S r)) = 0 := by
  simp [hδ r]

/-- If `δ₁, δ₂ : Derivation k S S` satisfy the lift condition for `Ω[S⁄R]`, so does `δ₁ - δ₂`. -/
theorem D_sub_algebraMap_eq_zero {δ₁ δ₂ : Derivation k S S}
    (h₁ : ∀ r : R, KaehlerDifferential.D R S (δ₁ (algebraMap R S r)) = 0)
    (h₂ : ∀ r : R, KaehlerDifferential.D R S (δ₂ (algebraMap R S r)) = 0) (r : R) :
    KaehlerDifferential.D R S ((δ₁ - δ₂) (algebraMap R S r)) = 0 := by
  simp [h₁ r, h₂ r]

/-- If each `δ i : Derivation k S S` for `i ∈ t` satisfies the lift condition for `Ω[S⁄R]`, so
does `∑ i ∈ t, δ i`. -/
theorem D_sum_algebraMap_eq_zero {ι : Type*} (t : Finset ι) (δ : ι → Derivation k S S)
    (hδ : ∀ i ∈ t, ∀ r : R, KaehlerDifferential.D R S (δ i (algebraMap R S r)) = 0) (r : R) :
    KaehlerDifferential.D R S ((∑ i ∈ t, δ i) (algebraMap R S r)) = 0 := by
  simp [Finset.sum_eq_zero fun i hi ↦ hδ i hi r]

/-- In a scalar tower `k → R → S`, if `δ : Derivation k S S` satisfies the lift condition for
`Ω[S⁄R]`, so does `c • δ` for any `c : k`. -/
theorem D_smul_algebraMap_eq_zero [Algebra k R] [IsScalarTower k R S] (c : k)
    {δ : Derivation k S S}
    (hδ : ∀ r : R, KaehlerDifferential.D R S (δ (algebraMap R S r)) = 0) (r : R) :
    KaehlerDifferential.D R S ((c • δ) (algebraMap R S r)) = 0 := by
  rw [_root_.smul_apply, ← IsScalarTower.algebraMap_smul R c, map_smul, hδ, smul_zero]

/-- If `δ₁, δ₂ : Derivation k S S` satisfy the lift condition for `Ω[S⁄R]`, so does their
commutator `⁅δ₁, δ₂⁆`. -/
theorem D_commutator_algebraMap_eq_zero {δ₁ δ₂ : Derivation k S S}
    (h₁ : ∀ r : R, KaehlerDifferential.D R S (δ₁ (algebraMap R S r)) = 0)
    (h₂ : ∀ r : R, KaehlerDifferential.D R S (δ₂ (algebraMap R S r)) = 0) (r : R) :
    KaehlerDifferential.D R S (⁅δ₁, δ₂⁆ (algebraMap R S r)) = 0 := by
  rw [Derivation.commutator_apply, map_sub, ← δ₁.kaehlerLieDeriv_D h₁ (δ₂ _),
    ← δ₂.kaehlerLieDeriv_D h₂ (δ₁ _), h₂ r, h₁ r, map_zero, map_zero, sub_self]

/-- `kaehlerLieDeriv` maps the zero derivation to zero. -/
@[simp]
theorem kaehlerLieDeriv_zero
    (h₀ : ∀ r : R, KaehlerDifferential.D R S ((0 : Derivation k S S) (algebraMap R S r)) = 0) :
    (0 : Derivation k S S).kaehlerLieDeriv h₀ = 0 :=
  ((0 : Derivation k S S).kaehlerLieDeriv_unique h₀ (fun _ ↦ by simp) (fun _ _ ↦ by simp)).symm

/-- `kaehlerLieDeriv` is additive in the derivation `δ`. -/
theorem kaehlerLieDeriv_add {δ₁ δ₂ : Derivation k S S}
    (h₁ : ∀ r : R, KaehlerDifferential.D R S (δ₁ (algebraMap R S r)) = 0)
    (h₂ : ∀ r : R, KaehlerDifferential.D R S (δ₂ (algebraMap R S r)) = 0) :
    (δ₁ + δ₂).kaehlerLieDeriv (D_add_algebraMap_eq_zero h₁ h₂) =
      δ₁.kaehlerLieDeriv h₁ + δ₂.kaehlerLieDeriv h₂ := by
  refine ((δ₁ + δ₂).kaehlerLieDeriv_unique _ (fun s ↦ by simp) fun s ω ↦ ?_).symm
  simp only [LinearMap.add_apply, kaehlerLieDeriv_smul, _root_.add_apply, add_smul, smul_add]
  abel

/-- `kaehlerLieDeriv` respects negation of the derivation `δ`. -/
theorem kaehlerLieDeriv_neg {δ : Derivation k S S}
    (hδ : ∀ r : R, KaehlerDifferential.D R S (δ (algebraMap R S r)) = 0) :
    (-δ).kaehlerLieDeriv (D_neg_algebraMap_eq_zero hδ) = -δ.kaehlerLieDeriv hδ := by
  refine ((-δ).kaehlerLieDeriv_unique _ (fun s ↦ by simp) fun s ω ↦ ?_).symm
  simp only [LinearMap.neg_apply, kaehlerLieDeriv_smul, _root_.neg_apply, neg_smul, smul_neg,
    neg_add_rev]
  abel

/-- `kaehlerLieDeriv` respects subtraction of derivations. -/
theorem kaehlerLieDeriv_sub {δ₁ δ₂ : Derivation k S S}
    (h₁ : ∀ r : R, KaehlerDifferential.D R S (δ₁ (algebraMap R S r)) = 0)
    (h₂ : ∀ r : R, KaehlerDifferential.D R S (δ₂ (algebraMap R S r)) = 0) :
    (δ₁ - δ₂).kaehlerLieDeriv (D_sub_algebraMap_eq_zero h₁ h₂) =
      δ₁.kaehlerLieDeriv h₁ - δ₂.kaehlerLieDeriv h₂ := by
  rw [kaehlerLieDeriv_congr _ (D_add_algebraMap_eq_zero h₁ (D_neg_algebraMap_eq_zero h₂))
    (sub_eq_add_neg δ₁ δ₂), kaehlerLieDeriv_add h₁ (D_neg_algebraMap_eq_zero h₂),
    kaehlerLieDeriv_neg h₂, ← sub_eq_add_neg]

/-- `kaehlerLieDeriv` respects finite sums of derivations. -/
theorem kaehlerLieDeriv_sum {ι : Type*} (t : Finset ι) (δ : ι → Derivation k S S)
    (hδ : ∀ i ∈ t, ∀ r : R, KaehlerDifferential.D R S (δ i (algebraMap R S r)) = 0) :
    (∑ i ∈ t, δ i).kaehlerLieDeriv (D_sum_algebraMap_eq_zero t δ hδ) =
      ∑ i ∈ t.attach, (δ i.val).kaehlerLieDeriv (hδ i.val i.property) := by
  refine ((∑ i ∈ t, δ i).kaehlerLieDeriv_unique _ (fun s ↦ ?_) fun s ω ↦ ?_).symm
  · simp [Finset.sum_attach t (fun i ↦ KaehlerDifferential.D R S (δ i s))]
  · simp [LinearMap.sum_apply, kaehlerLieDeriv_smul, Finset.sum_add_distrib, Finset.sum_smul,
      Finset.smul_sum, Finset.sum_attach t (fun i ↦ δ i s • ω)]

/-- In a scalar tower `k → R → S`, `kaehlerLieDeriv` is `k`-linear in the derivation `δ`. -/
theorem smul_kaehlerLieDeriv [Algebra k R] [IsScalarTower k R S] (c : k) {δ : Derivation k S S}
    (hδ : ∀ r : R, KaehlerDifferential.D R S (δ (algebraMap R S r)) = 0) :
    (c • δ).kaehlerLieDeriv (D_smul_algebraMap_eq_zero c hδ) = c • δ.kaehlerLieDeriv hδ := by
  refine ((c • δ).kaehlerLieDeriv_unique _ (fun s ↦ ?_) fun s ω ↦ ?_).symm
  · rw [LinearMap.smul_apply, kaehlerLieDeriv_D, _root_.smul_apply,
      ← IsScalarTower.algebraMap_smul R c (δ s), map_smul, IsScalarTower.algebraMap_smul]
  · simp [smul_add, smul_comm c s]

/-- On `Ω[S⁄R]`, the Lie derivative of `⁅δ₁, δ₂⁆` is the commutator of the degree-one Lie
derivatives. -/
theorem kaehlerLieDeriv_commutator {δ₁ δ₂ : Derivation k S S}
    (h₁ : ∀ r : R, KaehlerDifferential.D R S (δ₁ (algebraMap R S r)) = 0)
    (h₂ : ∀ r : R, KaehlerDifferential.D R S (δ₂ (algebraMap R S r)) = 0) :
    (⁅δ₁, δ₂⁆).kaehlerLieDeriv (D_commutator_algebraMap_eq_zero h₁ h₂) =
      (δ₁.kaehlerLieDeriv h₁).comp (δ₂.kaehlerLieDeriv h₂) -
        (δ₂.kaehlerLieDeriv h₂).comp (δ₁.kaehlerLieDeriv h₁) := by
  refine (kaehlerLieDeriv_unique ⁅δ₁, δ₂⁆ _ (fun s ↦ ?_) (fun s ω ↦ ?_)).symm
  · simp [Derivation.commutator_apply]
  · simp only [LinearMap.sub_apply, LinearMap.comp_apply, kaehlerLieDeriv_smul, map_add,
      Derivation.commutator_apply, sub_smul, smul_sub]
    abel

/-- **Naturality of `kaehlerLieDeriv` along an `R`-algebra homomorphism**: if `f : A →ₐ[R] B`
intertwines derivations `δA` and `δB`, then `KaehlerDifferential.mapSemilinear f` intertwines
their Kähler Lie derivatives. -/
theorem mapSemilinear_kaehlerLieDeriv {kA kB R A B : Type*}
    [CommRing kA] [CommRing kB] [CommRing R] [CommRing A] [CommRing B]
    [Algebra kA A] [Algebra kB B] [Algebra R A] [Algebra R B]
    (f : A →ₐ[R] B) {δA : Derivation kA A A} {δB : Derivation kB B B}
    (hA : ∀ r : R, KaehlerDifferential.D R A (δA (algebraMap R A r)) = 0)
    (hB : ∀ r : R, KaehlerDifferential.D R B (δB (algebraMap R B r)) = 0)
    (hf : ∀ a : A, f (δA a) = δB (f a)) (ω : Ω[A⁄R]) :
    KaehlerDifferential.mapSemilinear f (δA.kaehlerLieDeriv hA ω) =
      δB.kaehlerLieDeriv hB (KaehlerDifferential.mapSemilinear f ω) := by
  induction ω using KaehlerDifferential.inductionOn with
  | D a => simp only [kaehlerLieDeriv_D, KaehlerDifferential.mapSemilinear_D, hf]
  | smul a ω ih =>
    simp only [kaehlerLieDeriv_smul, map_add, KaehlerDifferential.mapSemilinear_smul, hf, ih]
  | add _ _ ih₁ ih₂ => simp only [map_add, ih₁, ih₂]

/-- Any compatible derivation couple `c : Derivation.couple k R S` satisfies the lift condition for
`Ω[S⁄R]` because `c.1.1` preserves the image of `algebraMap R S`. -/
theorem Compatible.D_apply_algebraMap_eq_zero [Algebra k R] [IsScalarTower k R S]
    (c : Derivation.couple k R S) (r : R) :
    KaehlerDifferential.D R S (c.val.1 (algebraMap R S r)) = 0 := by
  have hc : c.val.1 (algebraMap R S r) = algebraMap R S (c.val.2 r) := Compatible.apply c r
  rw [hc, Derivation.map_algebraMap]

end Derivation

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Lift
public import Mathlib.RingTheory.Kaehler.Basic
public import TauCeti.RingTheory.Derivation.DifferentialOperator.Basic

/-!
# Modules of principal parts and universal factorization of differential operators

Let `A` be a commutative `R`-algebra and `M` an `A`-module. Grothendieck's `A`-module of principal
parts of order `m` of `M`, denoted `PrincipalParts R A M m`, represents differential operators of
order at most `m` out of `M`: there is a universal operator `PrincipalParts.jet R A M m` of order at
most `m`, and pre-composition with `jet` gives an `A`-linear isomorphism between `A`-linear maps
`PrincipalParts R A M m →ₗ[A] N` and `differentialOperators R A M N m`. No characteristic,
smoothness, or finiteness assumption is imposed.

We construct `PrincipalParts R A M m` as the quotient of `A ⊗[R] M` (carrying its left `A`-module
structure `a • (b ⊗ₜ x) = (a * b) ⊗ₜ x`) by the `A`-submodule `principalPartsRel R A M m` generated
recursively by the `A`-linear diagonal difference endomorphisms
`diagDiff R a : b ⊗ₜ x ↦ b ⊗ₜ (a • x) - (a * b) ⊗ₜ x`. Under the base-change adjunction
`LinearMap.liftBaseChangeEquiv A : (M →ₗ[R] N) ≃ₗ[A] (A ⊗[R] M →ₗ[A] N)`, pre-composing with
`diagDiff R a` corresponds identically to `smulCommutator R a`. For `M = A`, `diagDiff R a` is
multiplication by `1 ⊗ₜ a - a ⊗ₜ 1 ∈ KaehlerDifferential.ideal R A`, so `principalPartsRel R A A m`
is `(KaehlerDifferential.ideal R A) ^ (m + 1)` (`principalPartsRel_self`) and
`PrincipalParts R A A m` is `A`-linearly isomorphic to
`(A ⊗[R] A) ⧸ (KaehlerDifferential.ideal R A) ^ (m + 1)` (`PrincipalParts.selfEquiv`). More
generally, `(A ⊗[R] A) ⧸ (KaehlerDifferential.ideal R A) ^ (m + 1)` acts on
`PrincipalParts R A M m` via `PrincipalParts.quotientIdealPowLsmul`, with the class of `a ⊗ₜ b`
sending `jet m x` to `a • jet m (b • x)`.

## Main definitions

* `TauCeti.diagDiff`: the `A`-linear diagonal difference endomorphism of `A ⊗[R] M` attached to
  `a : A`, sending `b ⊗ₜ x` to `b ⊗ₜ (a • x) - (a * b) ⊗ₜ x`.
* `TauCeti.principalPartsRel`: the decreasing sequence of `A`-submodules of `A ⊗[R] M` cutting out
  principal parts of each order `m`.
* `TauCeti.PrincipalParts`: the `A`-module of principal parts of order `m` of `M` over `A / R`.
* `TauCeti.PrincipalParts.jet`: the universal differential operator `M →ₗ[R] PrincipalParts R A M m`
  sending `x` to the class of `1 ⊗ₜ x`.
* `TauCeti.PrincipalParts.liftEquiv`: the universal `A`-linear equivalence
  `(PrincipalParts R A M m →ₗ[A] N) ≃ₗ[A] differentialOperators R A M N m`.
* `TauCeti.PrincipalParts.map`, `TauCeti.PrincipalParts.mapAlgebra`, and
  `TauCeti.PrincipalParts.transition`: functoriality in `M` and along algebra towers `R → A → B`,
  together with surjective order-transition maps for `n ≤ m`.
* `TauCeti.PrincipalParts.zeroEquiv`, `TauCeti.PrincipalParts.counit`, and
  `TauCeti.PrincipalParts.oneEquiv`: the order-zero identification `P^0(M) ≃ₗ[A] M`, the counit
  `P^m(M) →ₗ[A] M`, and the first-order splitting `P^1(A) ≃ₗ[A] Ω[A⁄R] × A`.
* `TauCeti.PrincipalParts.comul`: Grothendieck's composition map
  `P^(m + n)(M) →ₗ[A] P^m(P^n(M))` carrying `jet (m + n) x` to `jet m (jet n x)`.

## Main results

* `TauCeti.principalPartsRel_eq_span`: `principalPartsRel R A M m` is spanned over `A` by the
  `(m + 1)`-fold diagonal differences applied to `1 ⊗ₜ x`.
* `TauCeti.principalPartsRel_self`: for `M = A`, the relation submodule is
  `(KaehlerDifferential.ideal R A) ^ (m + 1)`.
* `TauCeti.PrincipalParts.jet_mem_differentialOperators`: the universal `m`-jet has order at most
  `m`.
* `TauCeti.PrincipalParts.counit_comp_comul`, `TauCeti.PrincipalParts.map_counit_comp_comul`,
  `TauCeti.PrincipalParts.comul_coassoc`, `TauCeti.PrincipalParts.transition_comp_comul`, and
  `TauCeti.PrincipalParts.lift_comp`: counitality, coassociativity, transition compatibility, and
  compatibility of `comul` with composition of differential operators.

## References

* A. Grothendieck, *Éléments de géométrie algébrique IV*, Quatrième partie, §§16.7–16.8,
  especially (16.7.2), Proposition (16.8.8), and Proposition (16.8.9).
-/

public section

noncomputable section

open scoped TensorProduct

namespace TauCeti

section DiagDiff

variable (R : Type*) {A M N : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
  [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N]

/-- The `A`-linear diagonal difference endomorphism of `A ⊗[R] M` attached to `a : A`, sending
`b ⊗ₜ x` to `b ⊗ₜ (a • x) - (a * b) ⊗ₜ x`. -/
def diagDiff (a : A) : Module.End A (A ⊗[R] M) :=
  (Algebra.lsmul R R M a).baseChange A - LinearMap.lsmul A (A ⊗[R] M) a

variable {R}

@[simp]
theorem diagDiff_tmul (a b : A) (x : M) :
    diagDiff R a (b ⊗ₜ[R] x) = b ⊗ₜ[R] (a • x) - (a * b) ⊗ₜ[R] x := by
  simp [diagDiff, TensorProduct.smul_tmul']

theorem diagDiff_one_tmul (a : A) (x : M) :
    diagDiff R a ((1 : A) ⊗ₜ[R] x) = (1 : A) ⊗ₜ[R] (a • x) - a ⊗ₜ[R] x := by
  simp

@[simp]
theorem diagDiff_zero : diagDiff R (0 : A) = (0 : Module.End A (A ⊗[R] M)) := by
  ext x
  simp

theorem diagDiff_add (a₁ a₂ : A) :
    diagDiff R (a₁ + a₂) = (diagDiff R a₁ + diagDiff R a₂ : Module.End A (A ⊗[R] M)) := by
  ext x
  simp only [TensorProduct.AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
    LinearMap.coe_restrictScalars, diagDiff_tmul, add_smul, TensorProduct.tmul_add, add_mul,
    TensorProduct.add_tmul, LinearMap.add_apply]
  abel

@[simp]
theorem diagDiff_algebraMap (r : R) :
    diagDiff R (algebraMap R A r) = (0 : Module.End A (A ⊗[R] M)) := by
  ext x
  simp [TensorProduct.smul_tmul', Algebra.algebraMap_eq_smul_one]

@[simp]
theorem diagDiff_one : diagDiff R (1 : A) = (0 : Module.End A (A ⊗[R] M)) := by
  simpa using diagDiff_algebraMap (A := A) (M := M) (1 : R)

/-- Diagonal difference endomorphisms for two elements of `A` commute. -/
theorem commute_diagDiff (a₁ a₂ : A) :
    Commute (diagDiff R a₁ : Module.End A (A ⊗[R] M)) (diagDiff R a₂) := by
  ext x
  simp only [TensorProduct.AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
    LinearMap.coe_restrictScalars, mul_apply_eq_comp, diagDiff_tmul, map_sub, smul_smul, mul_one,
    mul_comm a₁ a₂]
  abel

/-- Pre-composing `D.liftBaseChange A` with `diagDiff R a` corresponds to taking the commutator
`smulCommutator R a D`. -/
theorem liftBaseChange_comp_diagDiff (a : A) (D : M →ₗ[R] N) :
    D.liftBaseChange A ∘ₗ diagDiff R a = (smulCommutator R a D).liftBaseChange A := by
  ext x
  simp

end DiagDiff

/-! ### The diagonal relation submodule -/

section Rel

variable (R A M : Type*) [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]

/-- The `A`-submodule of `A ⊗[R] M` cutting out principal parts of order `m`: at order `0` it is
generated by the images of `diagDiff R a`, and at order `m + 1` by the images of the order-`m`
relations under `diagDiff R a` for all `a : A`. -/
def principalPartsRel : ℕ → Submodule A (A ⊗[R] M)
  | 0 => ⨆ a : A, LinearMap.range (diagDiff R a)
  | m + 1 => ⨆ a : A, (principalPartsRel m).map (diagDiff R a)

theorem principalPartsRel_zero :
    principalPartsRel R A M 0 = ⨆ a : A, LinearMap.range (diagDiff R a) := by
  rfl

theorem principalPartsRel_succ (m : ℕ) :
    principalPartsRel R A M (m + 1) = ⨆ a : A, (principalPartsRel R A M m).map (diagDiff R a) := by
  rfl

variable {R A M}

theorem diagDiff_mem_principalPartsRel_zero (a : A) (z : A ⊗[R] M) :
    diagDiff R a z ∈ principalPartsRel R A M 0 :=
  Submodule.mem_iSup_of_mem a ⟨z, rfl⟩

theorem diagDiff_mem_principalPartsRel_succ {m : ℕ} (a : A) {z : A ⊗[R] M}
    (hz : z ∈ principalPartsRel R A M m) :
    diagDiff R a z ∈ principalPartsRel R A M (m + 1) :=
  Submodule.mem_iSup_of_mem a (Submodule.mem_map_of_mem hz)

theorem principalPartsRel_succ_le (m : ℕ) :
    principalPartsRel R A M (m + 1) ≤ principalPartsRel R A M m := by
  induction m with
  | zero =>
    rw [principalPartsRel_succ, principalPartsRel_zero]
    exact iSup_mono fun a ↦ LinearMap.map_le_range
  | succ m ih =>
    rw [principalPartsRel_succ, principalPartsRel_succ]
    exact iSup_mono fun a ↦ Submodule.map_mono ih

/-- Higher-order principal parts divide out smaller relation submodules. -/
theorem principalPartsRel_antitone : Antitone (principalPartsRel R A M) :=
  antitone_nat_of_succ_le principalPartsRel_succ_le

/-- An `R`-linear map `D : M →ₗ[R] N` has differential order at most `m` if and only if its
`A`-linear base-change lift `A ⊗[R] M →ₗ[A] N` vanishes on `principalPartsRel R A M m`. -/
theorem principalPartsRel_le_ker_liftBaseChange_iff {N : Type*} [AddCommGroup N]
    [Module R N] [Module A N] [IsScalarTower R A N] {D : M →ₗ[R] N} {m : ℕ} :
    principalPartsRel R A M m ≤ LinearMap.ker (D.liftBaseChange A) ↔
      D ∈ differentialOperators R A M N m := by
  induction m generalizing D with
  | zero =>
    rw [principalPartsRel_zero, iSup_le_iff, mem_differentialOperators_zero_iff_smulCommutator]
    refine forall_congr' fun a ↦ ?_
    rw [LinearMap.range_le_ker_iff, liftBaseChange_comp_diagDiff, LinearEquiv.map_eq_zero_iff]
  | succ m ih =>
    rw [principalPartsRel_succ, iSup_le_iff, mem_differentialOperators_succ_iff]
    refine forall_congr' fun a ↦ ?_
    rw [Submodule.map_le_iff_le_comap, ← LinearMap.ker_comp, liftBaseChange_comp_diagDiff, ih]

/-- `principalPartsRel R A M m` is spanned as an `A`-module by the `(m + 1)`-fold diagonal
differences `(∏ i, diagDiff R (a i)) (1 ⊗ₜ x)`. -/
theorem principalPartsRel_eq_span (m : ℕ) :
    principalPartsRel R A M m =
      Submodule.span A { z | ∃ (a : Fin (m + 1) → A) (x : M),
        (List.ofFn fun i ↦ diagDiff R (a i)).prod ((1 : A) ⊗ₜ[R] x) = z } := by
  induction m with
  | zero =>
    apply le_antisymm
    · rw [principalPartsRel_zero, iSup_le_iff]
      rintro a _ ⟨z, rfl⟩
      induction z using TensorProduct.inductionOn with
      | tmul b x =>
        have hb : b ⊗ₜ[R] x = b • ((1 : A) ⊗ₜ[R] x) := by simp [TensorProduct.smul_tmul']
        rw [hb, map_smul]
        refine Submodule.smul_mem _ b (Submodule.subset_span ⟨fun _ ↦ a, x, ?_⟩)
        simp
      | add y z hy hz => rw [map_add]; exact add_mem hy hz
    · rw [Submodule.span_le]
      rintro _ ⟨a, x, rfl⟩
      simpa using diagDiff_mem_principalPartsRel_zero (a 0) ((1 : A) ⊗ₜ[R] x)
  | succ m ih =>
    apply le_antisymm
    · rw [principalPartsRel_succ, iSup_le_iff]
      intro c
      rw [ih, Submodule.map_span_le]
      rintro _ ⟨a, x, rfl⟩
      refine Submodule.subset_span ⟨Fin.cons c a, x, ?_⟩
      simp [List.ofFn_succ, mul_apply_eq_comp]
    · rw [Submodule.span_le]
      rintro _ ⟨a, x, rfl⟩
      rw [List.ofFn_succ, List.prod_cons, mul_apply_eq_comp]
      refine diagDiff_mem_principalPartsRel_succ (a 0) ?_
      rw [ih]
      exact Submodule.subset_span ⟨fun i ↦ a i.succ, x, rfl⟩

/-- On `A ⊗[R] A`, `diagDiff R a` is multiplication by the diagonal generator
`1 ⊗ₜ a - a ⊗ₜ 1 ∈ KaehlerDifferential.ideal R A`. -/
theorem diagDiff_self_apply (a : A) (z : A ⊗[R] A) :
    diagDiff R a z = ((1 : A) ⊗ₜ[R] a - a ⊗ₜ[R] (1 : A)) * z := by
  induction z using TensorProduct.inductionOn with
  | tmul b c =>
    rw [sub_mul]
    simp [mul_comm]
  | add x y hx hy => rw [map_add, mul_add, hx, hy]

private theorem iSup_map_diagDiff_self (J : Ideal (A ⊗[R] A)) :
    (⨆ a : A, (J.restrictScalars A).map (diagDiff R a)) =
      (KaehlerDifferential.ideal R A * J).restrictScalars A := by
  apply le_antisymm
  · rw [iSup_le_iff]
    rintro a _ ⟨z, hz, rfl⟩
    rw [Submodule.restrictScalars_mem, diagDiff_self_apply]
    exact Submodule.mul_mem_mul (KaehlerDifferential.one_smul_sub_smul_one_mem_ideal R a) hz
  · intro z (hz : z ∈ KaehlerDifferential.ideal R A * J)
    refine Submodule.mul_induction_on hz (fun u hu y hy ↦ ?_) fun _ _ h₁ h₂ ↦ add_mem h₁ h₂
    rw [← Submodule.restrictScalars_mem A,
      ← KaehlerDifferential.submodule_span_range_eq_ideal] at hu
    refine Submodule.span_induction ?_ (by simp)
      (fun _ _ _ _ ih₁ ih₂ ↦ by rw [add_mul]; exact add_mem ih₁ ih₂)
      (fun c _ _ ih₁ ↦ by rw [smul_mul_assoc]; exact Submodule.smul_mem _ c ih₁) hu
    rintro _ ⟨a, rfl⟩
    rw [← diagDiff_self_apply]
    exact Submodule.mem_iSup_of_mem a (Submodule.mem_map_of_mem hy)

/-- For `M = A`, `principalPartsRel R A A m` is `(KaehlerDifferential.ideal R A) ^ (m + 1)` viewed
as a left `A`-submodule of `A ⊗[R] A`. -/
theorem principalPartsRel_self (R A : Type*) [CommRing R] [CommRing A] [Algebra R A] (m : ℕ) :
    principalPartsRel R A A m = ((KaehlerDifferential.ideal R A) ^ (m + 1)).restrictScalars A := by
  induction m with
  | zero =>
    rw [pow_one, ← Ideal.mul_top (KaehlerDifferential.ideal R A), ← iSup_map_diagDiff_self,
      principalPartsRel_zero]
    refine iSup_congr fun a ↦ ?_
    ext z
    simp
  | succ m ih =>
    rw [principalPartsRel_succ, ih, iSup_map_diagDiff_self, ← pow_succ']

end Rel

/-! ### The module of principal parts and its universal property -/

/-- Grothendieck's `A`-module of principal parts of order `m` of an `A`-module `M` relative to `R`,
constructed as the quotient of `A ⊗[R] M` by `principalPartsRel R A M m`. -/
abbrev PrincipalParts (R A M : Type*) [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M] (m : ℕ) : Type _ :=
  (A ⊗[R] M) ⧸ principalPartsRel R A M m

namespace PrincipalParts

section Basic

variable (R A M : Type*) [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]

/-- The canonical `A`-linear quotient projection `A ⊗[R] M →ₗ[A] PrincipalParts R A M m`. -/
def mkQ (m : ℕ) : A ⊗[R] M →ₗ[A] PrincipalParts R A M m :=
  (principalPartsRel R A M m).mkQ

theorem mkQ_surjective (m : ℕ) : Function.Surjective (mkQ R A M m) :=
  Submodule.mkQ_surjective (principalPartsRel R A M m)

@[simp]
theorem ker_mkQ (m : ℕ) : LinearMap.ker (mkQ R A M m) = principalPartsRel R A M m :=
  Submodule.ker_mkQ (principalPartsRel R A M m)

/-- The universal `m`-jet `M →ₗ[R] PrincipalParts R A M m`, sending `x` to the class of `1 ⊗ₜ x`. -/
def jet (m : ℕ) : M →ₗ[R] PrincipalParts R A M m :=
  (mkQ R A M m).restrictScalars R ∘ₗ TensorProduct.mk R A M 1

variable {R A M}

theorem jet_apply (m : ℕ) (x : M) :
    jet R A M m x = mkQ R A M m ((1 : A) ⊗ₜ[R] x) := by
  rfl

@[simp]
theorem mkQ_tmul (m : ℕ) (a : A) (x : M) :
    mkQ R A M m (a ⊗ₜ[R] x) = a • jet R A M m x := by
  have h : a ⊗ₜ[R] x = a • ((1 : A) ⊗ₜ[R] x) := by simp [TensorProduct.smul_tmul']
  rw [h, map_smul, jet_apply]

@[simp]
theorem liftBaseChange_jet (m : ℕ) :
    (jet R A M m).liftBaseChange A = mkQ R A M m := by
  ext x
  simp

/-- The image of the universal `m`-jet spans `PrincipalParts R A M m` as an `A`-module. -/
theorem span_range_jet (m : ℕ) :
    Submodule.span A (Set.range (jet R A M m)) = ⊤ := by
  rw [eq_top_iff]
  rintro z -
  obtain ⟨y, rfl⟩ := mkQ_surjective R A M m z
  induction y using TensorProduct.inductionOn with
  | tmul a x =>
    rw [mkQ_tmul]
    exact Submodule.smul_mem _ a (Submodule.subset_span ⟨x, rfl⟩)
  | add u v hu hv =>
    rw [map_add]
    exact add_mem hu hv

/-- Two `A`-linear maps out of `PrincipalParts R A M m` are equal as soon as they agree on
`jet R A M m x` for all `x : M`. -/
@[ext high + 1]
theorem hom_ext {N : Type*} [AddCommGroup N] [Module A N] {m : ℕ}
    {f g : PrincipalParts R A M m →ₗ[A] N}
    (h : ∀ x : M, f (jet R A M m x) = g (jet R A M m x)) : f = g := by
  refine LinearMap.ext_on (span_range_jet m) ?_
  rintro _ ⟨x, rfl⟩
  exact h x

/-- The universal `m`-jet is a differential operator of order at most `m`. -/
theorem jet_mem_differentialOperators (m : ℕ) :
    jet R A M m ∈ differentialOperators R A M (PrincipalParts R A M m) m := by
  rw [← principalPartsRel_le_ker_liftBaseChange_iff, liftBaseChange_jet, ker_mkQ]

section Universal

variable {N : Type*} [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N]

/-- Descend a differential operator `D` of order at most `m` to an `A`-linear map out of
`PrincipalParts R A M m`. -/
def lift {m : ℕ} (D : differentialOperators R A M N m) :
    PrincipalParts R A M m →ₗ[A] N :=
  (principalPartsRel R A M m).liftQ (D.val.liftBaseChange A)
    (principalPartsRel_le_ker_liftBaseChange_iff.2 D.property)

@[simp]
theorem lift_mkQ {m : ℕ} (D : differentialOperators R A M N m) (z : A ⊗[R] M) :
    lift D (mkQ R A M m z) = D.val.liftBaseChange A z :=
  Submodule.liftQ_apply _ _ z

@[simp]
theorem lift_jet {m : ℕ} (D : differentialOperators R A M N m) (x : M) :
    lift D (jet R A M m x) = (D : M →ₗ[R] N) x := by
  rw [jet_apply, lift_mkQ, LinearMap.liftBaseChange_tmul, one_smul]

@[simp]
theorem lift_restrictScalars_comp_jet {m : ℕ} (D : differentialOperators R A M N m) :
    (lift D).restrictScalars R ∘ₗ jet R A M m = (D : M →ₗ[R] N) := by
  ext x
  exact lift_jet D x

variable (R A M N) in
/-- **Universal property of principal parts** (EGA IV₄, Proposition 16.8.8): pre-composing with
`jet R A M m` is an `A`-linear equivalence between `A`-linear maps `PrincipalParts R A M m →ₗ[A] N`
and differential operators `M → N` of order at most `m`. -/
def liftEquiv (m : ℕ) :
    (PrincipalParts R A M m →ₗ[A] N) ≃ₗ[A] differentialOperators R A M N m where
  toFun f := ⟨f.restrictScalars R ∘ₗ jet R A M m,
    f.restrictScalars_comp_mem_differentialOperators (jet_mem_differentialOperators m)⟩
  invFun := lift
  map_add' f g := by ext x; rfl
  map_smul' a f := by ext x; rfl
  left_inv f := hom_ext fun x ↦ lift_jet _ x
  right_inv D := Subtype.ext <| lift_restrictScalars_comp_jet D

@[simp]
theorem coe_liftEquiv_apply {m : ℕ} (f : PrincipalParts R A M m →ₗ[A] N) :
    (liftEquiv R A M N m f : M →ₗ[R] N) = f.restrictScalars R ∘ₗ jet R A M m := by
  rfl

theorem liftEquiv_apply_apply {m : ℕ} (f : PrincipalParts R A M m →ₗ[A] N) (x : M) :
    (liftEquiv R A M N m f : M →ₗ[R] N) x = f (jet R A M m x) := by
  rfl

@[simp]
theorem liftEquiv_symm_apply {m : ℕ} (D : differentialOperators R A M N m) :
    (liftEquiv R A M N m).symm D = lift D := by
  rfl

/-- Uniqueness of the `A`-linear factorization of a differential operator through `jet`. -/
theorem eq_lift_of_comp_jet {m : ℕ} {f : PrincipalParts R A M m →ₗ[A] N}
    (D : differentialOperators R A M N m)
    (hf : ∀ x : M, f (jet R A M m x) = (D : M →ₗ[R] N) x) : f = lift D :=
  hom_ext fun x ↦ (hf x).trans (lift_jet D x).symm

end Universal

end Basic

/-! ### Functoriality, order transitions, and low-order identifications -/

section Functoriality

variable (R : Type*) {A M M' M'' N N' : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
  [AddCommGroup M'] [Module R M'] [Module A M'] [IsScalarTower R A M']
  [AddCommGroup M''] [Module R M''] [Module A M''] [IsScalarTower R A M'']
  [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N]
  [AddCommGroup N'] [Module R N'] [Module A N'] [IsScalarTower R A N']

section MapAlgebra

variable (B : Type*) [CommRing B] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
  {M_B : Type*} [AddCommGroup M_B] [Module R M_B] [Module A M_B] [Module B M_B]
  [IsScalarTower A B M_B] [IsScalarTower R B M_B]

/-- Functoriality of `PrincipalParts` along a tower of commutative algebras `R → A → B` and an
`A`-linear map `fM : M →ₗ[A] M_B` into a `B`-module: `jet m x` maps to `jet m (fM x)`. -/
def mapAlgebra (fM : M →ₗ[A] M_B) (m : ℕ) :
    PrincipalParts R A M m →ₗ[A] PrincipalParts R B M_B m :=
  have := IsScalarTower.to₁₂₄ R A B (PrincipalParts R B M_B m)
  lift (differentialOperators.restrictOfAlgebra B fM m
    ⟨jet R B M_B m, jet_mem_differentialOperators m⟩)

variable {R B}

@[simp]
theorem mapAlgebra_jet (fM : M →ₗ[A] M_B) (m : ℕ) (x : M) :
    mapAlgebra R B fM m (jet R A M m x) = jet R B M_B m (fM x) := by
  simp [mapAlgebra]

end MapAlgebra

/-- Functoriality of `PrincipalParts` in the `A`-module `M`: an `A`-linear map `φ : M →ₗ[A] M'`
induces `PrincipalParts.map R m φ : PrincipalParts R A M m →ₗ[A] PrincipalParts R A M' m` carrying
`jet m x` to `jet m (φ x)`. -/
def map (m : ℕ) (φ : M →ₗ[A] M') : PrincipalParts R A M m →ₗ[A] PrincipalParts R A M' m :=
  mapAlgebra R A φ m

variable {R}

@[simp]
theorem map_jet (m : ℕ) (φ : M →ₗ[A] M') (x : M) :
    map R m φ (jet R A M m x) = jet R A M' m (φ x) :=
  mapAlgebra_jet φ m x

theorem map_mkQ (m : ℕ) (φ : M →ₗ[A] M') (a : A) (x : M) :
    map R m φ (mkQ R A M m (a ⊗ₜ[R] x)) = mkQ R A M' m (a ⊗ₜ[R] φ x) := by
  rw [mkQ_tmul, map_smul, map_jet, ← mkQ_tmul]

@[simp]
theorem map_id (m : ℕ) : map R m (LinearMap.id : M →ₗ[A] M) = LinearMap.id := by
  ext x
  simp

theorem map_comp (m : ℕ) (ψ : M' →ₗ[A] M'') (φ : M →ₗ[A] M') :
    map R m (ψ ∘ₗ φ) = map R m ψ ∘ₗ map R m φ := by
  ext x
  simp

/-- Naturality of `liftEquiv` in the source module `M`. -/
theorem coe_liftEquiv_comp_map (m : ℕ) (φ : M →ₗ[A] M') (f : PrincipalParts R A M' m →ₗ[A] N) :
    (liftEquiv R A M N m (f ∘ₗ map R m φ) : M →ₗ[R] N) =
      (liftEquiv R A M' N m f : M' →ₗ[R] N) ∘ₗ φ.restrictScalars R := by
  ext x
  simp

/-- Naturality of `liftEquiv` in the target module `N`. -/
theorem coe_liftEquiv_postcomp (m : ℕ) (ψ : N →ₗ[A] N') (f : PrincipalParts R A M m →ₗ[A] N) :
    (liftEquiv R A M N' m (ψ ∘ₗ f) : M →ₗ[R] N') =
      ψ.restrictScalars R ∘ₗ (liftEquiv R A M N m f : M →ₗ[R] N) := by
  ext x
  simp

variable (R) in
/-- The surjective `A`-linear transition map `P^m(M) →ₗ[A] P^n(M)` for `n ≤ m`, carrying `jet m x`
to `jet n x`. -/
def transition {n m : ℕ} (h : n ≤ m) :
    PrincipalParts R A M m →ₗ[A] PrincipalParts R A M n :=
  lift ⟨jet R A M n, differentialOperators_mono h (jet_mem_differentialOperators n)⟩

@[simp]
theorem transition_jet {n m : ℕ} (h : n ≤ m) (x : M) :
    transition R h (jet R A M m x) = jet R A M n x :=
  lift_jet _ x

@[simp]
theorem transition_mkQ {n m : ℕ} (h : n ≤ m) (z : A ⊗[R] M) :
    transition R h (mkQ R A M m z) = mkQ R A M n z := by
  induction z using TensorProduct.inductionOn with
  | tmul a x => rw [mkQ_tmul, map_smul, transition_jet, ← mkQ_tmul]
  | add y z hy hz => simp only [map_add, hy, hz]

theorem transition_surjective {n m : ℕ} (h : n ≤ m) :
    Function.Surjective (transition R (A := A) (M := M) h) := by
  intro z
  obtain ⟨y, rfl⟩ := mkQ_surjective R A M n z
  exact ⟨mkQ R A M m y, transition_mkQ h y⟩

@[simp]
theorem transition_rfl {m : ℕ} :
    transition R (A := A) (M := M) (le_refl m) = LinearMap.id := by
  ext x
  simp

theorem transition_trans {k n m : ℕ} (h₁ : k ≤ n) (h₂ : n ≤ m) :
    transition R (A := A) (M := M) h₁ ∘ₗ transition R h₂ = transition R (h₁.trans h₂) := by
  ext x
  simp

theorem transition_comp_mapAlgebra {B M_B : Type*} [CommRing B] [Algebra R B] [Algebra A B]
    [IsScalarTower R A B] [AddCommGroup M_B] [Module R M_B] [Module A M_B] [Module B M_B]
    [IsScalarTower A B M_B] [IsScalarTower R B M_B] {n m : ℕ} (h : n ≤ m) (fM : M →ₗ[A] M_B) :
    (transition R h).restrictScalars A ∘ₗ mapAlgebra R B fM m =
      mapAlgebra R B fM n ∘ₗ transition R h := by
  ext x
  simp

theorem transition_comp_map {n m : ℕ} (h : n ≤ m) (φ : M →ₗ[A] M') :
    transition R h ∘ₗ map R m φ = map R n φ ∘ₗ transition R h := by
  ext x
  simp

/-- Pre-composing with `transition R h` corresponds under `liftEquiv` to the order-monotonicity
inclusion `differentialOperators_mono h`. -/
theorem liftEquiv_comp_transition {n m : ℕ} (h : n ≤ m) (f : PrincipalParts R A M n →ₗ[A] N) :
    liftEquiv R A M N m (f ∘ₗ transition R h) =
      Submodule.inclusion (differentialOperators_mono h) (liftEquiv R A M N n f) := by
  ext x
  simp

/-- At order `0`, the universal jet `M → PrincipalParts R A M 0` is `A`-linear. -/
private def jetZeroLinearMap (R A M : Type*) [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M] :
    M →ₗ[A] PrincipalParts R A M 0 where
  toFun := jet R A M 0
  map_add' := map_add _
  map_smul' a x := by
    rw [RingHom.id_apply, ← sub_eq_zero, jet_apply, ← mkQ_tmul, ← map_sub]
    have hmem : (1 : A) ⊗ₜ[R] (a • x) - a ⊗ₜ[R] x ∈ principalPartsRel R A M 0 := by
      rw [← diagDiff_one_tmul]
      exact diagDiff_mem_principalPartsRel_zero a ((1 : A) ⊗ₜ[R] x)
    rwa [← ker_mkQ, LinearMap.mem_ker] at hmem

variable (R A M) in
/-- Principal parts of order `0` are canonically `A`-linearly isomorphic to `M`. -/
def zeroEquiv : PrincipalParts R A M 0 ≃ₗ[A] M :=
  LinearEquiv.ofLinearMap
    (lift ⟨(LinearMap.id : M →ₗ[A] M).restrictScalars R,
      LinearMap.restrictScalars_mem_differentialOperators_zero _⟩)
    (jetZeroLinearMap R A M)
    (LinearMap.ext fun x ↦ lift_jet _ x)
    (by ext x; simp [jetZeroLinearMap])

@[simp]
theorem zeroEquiv_jet (x : M) : zeroEquiv R A M (jet R A M 0 x) = x := by
  simp [zeroEquiv]

@[simp]
theorem zeroEquiv_symm_apply (x : M) : (zeroEquiv R A M).symm x = jet R A M 0 x := by
  rfl

variable (R A M) in
/-- The `A`-linear counit (augmentation) `PrincipalParts R A M m →ₗ[A] M`, sending `jet m x` to
`x`. -/
def counit (m : ℕ) : PrincipalParts R A M m →ₗ[A] M :=
  (zeroEquiv R A M).toLinearMap ∘ₗ transition R (Nat.zero_le m)

@[simp]
theorem counit_jet (m : ℕ) (x : M) : counit R A M m (jet R A M m x) = x := by
  simp [counit]

@[simp]
theorem counit_zero : counit R A M 0 = (zeroEquiv R A M).toLinearMap := by
  simp [counit]

theorem counit_comp_transition {n m : ℕ} (h : n ≤ m) :
    counit R A M n ∘ₗ transition R h = counit R A M m := by
  ext x
  simp

theorem counit_comp_map (m : ℕ) (φ : M →ₗ[A] M') :
    counit R A M' m ∘ₗ map R m φ = φ ∘ₗ counit R A M m := by
  ext x
  simp

end Functoriality

/-! ### Self principal parts, `(A ⊗[R] A) ⧸ I^(m+1)`-module action, and order one -/

section AlgebraAndOrderOne

variable (R A : Type*) [CommRing R] [CommRing A] [Algebra R A]

/-- For `M = A`, `PrincipalParts R A A m` is `A`-linearly isomorphic to the truncated diagonal
quotient ring `(A ⊗[R] A) ⧸ (KaehlerDifferential.ideal R A) ^ (m + 1)` with its left `A`-module
structure. -/
def selfEquiv (m : ℕ) :
    PrincipalParts R A A m ≃ₗ[A] (A ⊗[R] A) ⧸ (KaehlerDifferential.ideal R A) ^ (m + 1) :=
  Submodule.quotEquivOfEq _ _ (principalPartsRel_self R A m) ≪≫ₗ
    Submodule.Quotient.restrictScalarsEquiv A ((KaehlerDifferential.ideal R A) ^ (m + 1))

@[simp]
theorem selfEquiv_mkQ (m : ℕ) (z : A ⊗[R] A) :
    selfEquiv R A m (mkQ R A A m z) = Ideal.Quotient.mk _ z := by
  rfl

@[simp]
theorem selfEquiv_jet (m : ℕ) (a : A) :
    selfEquiv R A m (jet R A A m a) = Ideal.Quotient.mk _ ((1 : A) ⊗ₜ[R] a) := by
  rfl

@[simp]
theorem selfEquiv_symm_mk (m : ℕ) (z : A ⊗[R] A) :
    (selfEquiv R A m).symm (Ideal.Quotient.mk _ z) = mkQ R A A m z := by
  rfl

section ModuleAction

variable (M : Type*) [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]

/-- The `A`-algebra action of `A ⊗[R] A` on `A ⊗[R] M` sending `a ⊗ₜ b` to
`c ⊗ₜ x ↦ (a * c) ⊗ₜ (b • x)`. -/
private def tensorLsmul : A ⊗[R] A →ₐ[A] Module.End A (A ⊗[R] M) :=
  Algebra.TensorProduct.lift (Algebra.ofId A _)
    ((Module.End.baseChangeHom R A M).comp (Algebra.lsmul R R M))
    fun a _ ↦ by rw [Algebra.ofId_apply]; exact Algebra.commute_algebraMap_left a _

private theorem tensorLsmul_tmul_tmul (a b c : A) (x : M) :
    tensorLsmul R A M (a ⊗ₜ[R] b) (c ⊗ₜ[R] x) = (a * c) ⊗ₜ[R] (b • x) := by
  simp [tensorLsmul, TensorProduct.liftAux_tmul, Algebra.algebraMap_eq_smul_one,
    TensorProduct.smul_tmul']

private theorem tensorLsmul_diag (a : A) :
    tensorLsmul R A M ((1 : A) ⊗ₜ[R] a - a ⊗ₜ[R] (1 : A)) = diagDiff R a := by
  ext x
  simp [map_sub, tensorLsmul_tmul_tmul]

private theorem commute_tensorLsmul_diagDiff (u : A ⊗[R] A) (a : A) :
    Commute (tensorLsmul R A M u) (diagDiff R a) := by
  rw [← tensorLsmul_diag]
  exact (Commute.all u _).map (tensorLsmul R A M)

private theorem map_principalPartsRel_le_of_tensorLsmul (m : ℕ) (u : A ⊗[R] A) :
    (principalPartsRel R A M m).map (tensorLsmul R A M u) ≤ principalPartsRel R A M m := by
  induction m with
  | zero =>
    rw [principalPartsRel_zero, Submodule.map_iSup]
    refine iSup_mono fun a ↦ ?_
    rintro _ ⟨_, ⟨z, rfl⟩, rfl⟩
    have hcomm := congr($((commute_tensorLsmul_diagDiff R A M u a).eq) z)
    simp only [mul_apply_eq_comp] at hcomm
    exact ⟨tensorLsmul R A M u z, hcomm.symm⟩
  | succ m ih =>
    rw [principalPartsRel_succ, Submodule.map_iSup]
    refine iSup_mono fun a ↦ ?_
    rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    have hcomm := congr($((commute_tensorLsmul_diagDiff R A M u a).eq) z)
    simp only [mul_apply_eq_comp] at hcomm
    rw [hcomm]
    exact Submodule.mem_map_of_mem (ih (Submodule.mem_map_of_mem hz))

private theorem tensorLsmul_mem_of_mem_ideal_pow :
    ∀ (m : ℕ) {u : A ⊗[R] A}, u ∈ (KaehlerDifferential.ideal R A) ^ (m + 1) →
      ∀ z : A ⊗[R] M, tensorLsmul R A M u z ∈ principalPartsRel R A M m
  | 0, u, hu, z => by
    rw [pow_one, ← Submodule.restrictScalars_mem A,
      ← KaehlerDifferential.submodule_span_range_eq_ideal] at hu
    refine Submodule.span_induction ?_ (by simp)
      (fun _ _ _ _ ih₁ ih₂ ↦ by rw [map_add, LinearMap.add_apply]; exact add_mem ih₁ ih₂)
      (fun c _ _ ih₁ ↦ by rw [map_smul, LinearMap.smul_apply]; exact Submodule.smul_mem _ c ih₁) hu
    rintro _ ⟨a, rfl⟩
    rw [tensorLsmul_diag]
    exact diagDiff_mem_principalPartsRel_zero a z
  | m + 1, u, hu, z => by
    rw [pow_succ'] at hu
    refine Submodule.mul_induction_on hu (fun v hv w hw ↦ ?_) fun _ _ hx hy ↦ by
      rw [map_add, LinearMap.add_apply]; exact add_mem hx hy
    rw [← Submodule.restrictScalars_mem A,
      ← KaehlerDifferential.submodule_span_range_eq_ideal] at hv
    refine Submodule.span_induction ?_ (by simp)
      (fun _ _ _ _ ih₁ ih₂ ↦ by
        rw [add_mul, map_add, LinearMap.add_apply]; exact add_mem ih₁ ih₂)
      (fun c _ _ ih₁ ↦ by
        rw [smul_mul_assoc, map_smul, LinearMap.smul_apply]; exact Submodule.smul_mem _ c ih₁) hv
    rintro _ ⟨a, rfl⟩
    rw [map_mul, mul_apply_eq_comp, tensorLsmul_diag]
    exact diagDiff_mem_principalPartsRel_succ a (tensorLsmul_mem_of_mem_ideal_pow m hw z)

private def endOfTensor (m : ℕ) (u : A ⊗[R] A) : Module.End A (PrincipalParts R A M m) :=
  (principalPartsRel R A M m).mapQ (principalPartsRel R A M m) (tensorLsmul R A M u)
    (Submodule.map_le_iff_le_comap.1 (map_principalPartsRel_le_of_tensorLsmul R A M m u))

private theorem endOfTensor_mkQ (m : ℕ) (u : A ⊗[R] A) (z : A ⊗[R] M) :
    endOfTensor R A M m u (mkQ R A M m z) = mkQ R A M m (tensorLsmul R A M u z) :=
  Submodule.mapQ_apply _ _ _ z

private theorem endOfTensor_jet (m : ℕ) (u : A ⊗[R] A) (x : M) :
    endOfTensor R A M m u (jet R A M m x) = mkQ R A M m (tensorLsmul R A M u ((1 : A) ⊗ₜ[R] x)) :=
  endOfTensor_mkQ R A M m u ((1 : A) ⊗ₜ[R] x)

private def endOfTensorAlgHom (m : ℕ) :
    A ⊗[R] A →ₐ[A] Module.End A (PrincipalParts R A M m) where
  toFun := endOfTensor R A M m
  map_one' := hom_ext fun x ↦ by simp [endOfTensor_jet]
  map_mul' u v := hom_ext fun x ↦ by simp [mul_apply_eq_comp, endOfTensor_jet, endOfTensor_mkQ]
  map_zero' := hom_ext fun x ↦ by simp [endOfTensor_jet]
  map_add' u v := hom_ext fun x ↦ by simp [endOfTensor_jet]
  commutes' a := hom_ext fun x ↦ by simp [Algebra.algebraMap_eq_smul_one, endOfTensor_jet]

@[simp]
private theorem endOfTensorAlgHom_apply (m : ℕ) (u : A ⊗[R] A) :
    endOfTensorAlgHom R A M m u = endOfTensor R A M m u :=
  rfl

/-- The action of the principal-parts algebra `(A ⊗[R] A) ⧸ (KaehlerDifferential.ideal R A) ^ (m+1)`
on `PrincipalParts R A M m`: the class of `a ⊗ₜ b` sends `jet m x` to `a • jet m (b • x)`. -/
def quotientIdealPowLsmul (m : ℕ) :
    (A ⊗[R] A) ⧸ (KaehlerDifferential.ideal R A) ^ (m + 1) →ₐ[A]
      Module.End A (PrincipalParts R A M m) :=
  Ideal.Quotient.liftₐ ((KaehlerDifferential.ideal R A) ^ (m + 1)) (endOfTensorAlgHom R A M m)
    fun u hu ↦ hom_ext fun x ↦ by
      rw [endOfTensorAlgHom_apply, LinearMap.zero_apply, endOfTensor_jet, ← LinearMap.mem_ker,
        ker_mkQ]
      exact tensorLsmul_mem_of_mem_ideal_pow R A M m hu ((1 : A) ⊗ₜ[R] x)

@[simp]
theorem quotientIdealPowLsmul_mk_jet (m : ℕ) (a b : A) (x : M) :
    quotientIdealPowLsmul R A M m (Ideal.Quotient.mk _ (a ⊗ₜ[R] b)) (jet R A M m x) =
      a • jet R A M m (b • x) := by
  rw [← Ideal.Quotient.mkₐ_eq_mk A, ← AlgHom.comp_apply, quotientIdealPowLsmul,
    Ideal.Quotient.liftₐ_comp, endOfTensorAlgHom_apply, jet_apply, endOfTensor_mkQ,
    tensorLsmul_tmul_tmul, mul_one, mkQ_tmul]

end ModuleAction

/-- The universal first-order derivation `A → PrincipalParts R A A 1`, sending `a` to
`jet 1 a - a • jet 1 1`. -/
def jetDerivation : Derivation R A (PrincipalParts R A A 1) :=
  (jet R A A 1).derivationOfMemDifferentialOperatorsOne (jet_mem_differentialOperators 1)

@[simp]
theorem jetDerivation_apply (a : A) :
    jetDerivation R A a = jet R A A 1 a - a • jet R A A 1 1 := by
  simp [jetDerivation]

/-- First-order principal parts of `A` split canonically as `Ω[A⁄R] × A`, sending `jet 1 a` to
`(KaehlerDifferential.D R A a, a)` and `(KaehlerDifferential.D R A a, b)` to
`(jet 1 a - a • jet 1 1) + b • jet 1 1`. -/
def oneEquiv : PrincipalParts R A A 1 ≃ₗ[A] Ω[A⁄R] × A :=
  LinearEquiv.ofLinearMap
    ((lift ⟨KaehlerDifferential.D R A,
        (KaehlerDifferential.D R A).mem_differentialOperators_one⟩).prod (counit R A A 1))
    ((jetDerivation R A).liftKaehlerDifferential.coprod
      (LinearMap.toSpanSingleton A (PrincipalParts R A A 1) (jet R A A 1 1)))
    (by ext <;> simp)
    (hom_ext fun a ↦ by simp)

@[simp]
theorem oneEquiv_jet (a : A) :
    oneEquiv R A (jet R A A 1 a) = (KaehlerDifferential.D R A a, a) := by
  simp [oneEquiv]

@[simp]
theorem oneEquiv_symm_apply (a b : A) :
    (oneEquiv R A).symm (KaehlerDifferential.D R A a, b) =
      (jet R A A 1 a - a • jet R A A 1 1) + b • jet R A A 1 1 := by
  simp [oneEquiv]

end AlgebraAndOrderOne

/-! ### Composition comultiplication (`P^(m + n)(M) → P^m(P^n(M))`) -/

section Comul

variable (R A M : Type*) [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]

/-- Grothendieck's composition map (EGA IV₄, 16.8.9.2): the unique `A`-linear map
`PrincipalParts R A M (m + n) →ₗ[A] PrincipalParts R A (PrincipalParts R A M n) m` carrying the
universal `(m + n)`-jet to the iterated jet `x ↦ jet m (jet n x)`. -/
def comul (m n : ℕ) :
    PrincipalParts R A M (m + n) →ₗ[A] PrincipalParts R A (PrincipalParts R A M n) m :=
  lift ⟨jet R A (PrincipalParts R A M n) m ∘ₗ jet R A M n,
    comp_mem_differentialOperators (jet_mem_differentialOperators m)
      (jet_mem_differentialOperators n)⟩

variable {R A M}

@[simp]
theorem comul_jet (m n : ℕ) (x : M) :
    comul R A M m n (jet R A M (m + n) x) =
      jet R A (PrincipalParts R A M n) m (jet R A M n x) :=
  lift_jet _ x

/-- An `A`-linear map out of `PrincipalParts R A M (m + n)` into `P^m(P^n(M))` sending
`jet (m + n) x` to `jet m (jet n x)` equals `comul R A M m n`. -/
theorem eq_comul_of_forall_jet {m n : ℕ}
    {f : PrincipalParts R A M (m + n) →ₗ[A] PrincipalParts R A (PrincipalParts R A M n) m}
    (hf : ∀ x : M, f (jet R A M (m + n) x) =
      jet R A (PrincipalParts R A M n) m (jet R A M n x)) :
    f = comul R A M m n :=
  hom_ext fun x ↦ (hf x).trans (comul_jet m n x).symm

/-- Left counit law for `comul`: applying `counit` at the outer order `0` recovers the canonical
order transition from `0 + n` to `n`. -/
theorem counit_comp_comul (n : ℕ) :
    counit R A (PrincipalParts R A M n) 0 ∘ₗ comul R A M 0 n =
      transition R (Nat.le_add_left n 0) := by
  ext x
  simp

/-- Right counit law for `comul`: applying `PrincipalParts.map R m (counit 0)` at the inner order
`0` is the identity on `PrincipalParts R A M m`. -/
theorem map_counit_comp_comul (m : ℕ) :
    map R m (counit R A M 0) ∘ₗ comul R A M m 0 = LinearMap.id := by
  ext x
  rw [LinearMap.comp_apply, comul_jet]
  simp

/-- Coassociativity of `comul`: the two ways of decomposing `k + (m + n)`-jets into iterated
`k`-, `m`-, and `n`-jets agree up to the associativity transition `k + m + n ≤ k + (m + n)`. -/
theorem comul_coassoc (k m n : ℕ) :
    map R k (comul R A M m n) ∘ₗ comul R A M k (m + n) =
      comul R A (PrincipalParts R A M n) k m ∘ₗ comul R A M (k + m) n ∘ₗ
        transition R (by omega : k + m + n ≤ k + (m + n)) := by
  ext x
  simp

/-- Compatibility of `comul` with order transitions in both indices. -/
theorem transition_comp_comul {m m' n n' : ℕ} (hm : m' ≤ m) (hn : n' ≤ n) :
    transition R hm ∘ₗ map R m (transition R hn) ∘ₗ comul R A M m n =
      comul R A M m' n' ∘ₗ transition R (Nat.add_le_add hm hn) := by
  ext x
  simp

/-- Naturality of `comul` with respect to an `A`-linear map `φ : M →ₗ[A] M'`. -/
theorem map_comp_comul {M' : Type*} [AddCommGroup M'] [Module R M'] [Module A M']
    [IsScalarTower R A M'] (m n : ℕ) (φ : M →ₗ[A] M') :
    map R m (map R n φ) ∘ₗ comul R A M m n = comul R A M' m n ∘ₗ map R (m + n) φ := by
  ext x
  simp

/-- Under the universal property `lift`, composition `P ∘ₗ Q` of differential operators of orders
at most `m` and `n` factors as `lift P ∘ₗ map R m (lift Q) ∘ₗ comul R A M m n`. -/
theorem lift_comp {N O : Type*} [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N]
    [AddCommGroup O] [Module R O] [Module A O] [IsScalarTower R A O]
    {m n : ℕ} (P : differentialOperators R A N O m) (Q : differentialOperators R A M N n) :
    lift ⟨(P : N →ₗ[R] O) ∘ₗ (Q : M →ₗ[R] N),
      comp_mem_differentialOperators P.property Q.property⟩ =
      lift P ∘ₗ map R m (lift Q) ∘ₗ comul R A M m n := by
  ext x
  simp

/-- Additive splitting of `comul` on an infinitesimal coordinate increment
`jet (m + n) a - a • jet (m + n) 1`: under `comul`, `jet (m + n) a - a • jet (m + n) 1` decomposes
as the sum of the inner increment `jet m (jet n a - a • jet n 1)` and the outer increment
`smulCommutator R a (jet m) (jet n 1)`. -/
theorem comul_jet_sub_smul_one (m n : ℕ) (a : A) :
    comul R A A m n (jet R A A (m + n) a - a • jet R A A (m + n) 1) =
      jet R A (PrincipalParts R A A n) m (jet R A A n a - a • jet R A A n 1) +
        smulCommutator R a (jet R A (PrincipalParts R A A n) m) (jet R A A n 1) := by
  rw [map_sub, map_smul, comul_jet, comul_jet, map_sub, smulCommutator_apply_apply]
  abel

end Comul

end PrincipalParts

end TauCeti

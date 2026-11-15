/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Idempotents.Module
public import TauCeti.RingTheory.Morita.ModuleEnd
-- Private: `dualTensorHom_bijective` supplies a finite coordinate family `∑ᵢ φᵢ(t) vᵢ = t` inside
-- the bijectivity proof.
import Mathlib.LinearAlgebra.Contraction

/-!
# Morita evaluation at a central idempotent and over a two-block algebra

Let `k` be a commutative semiring, `A` a `k`-algebra, and `S` a finite projective `k`-module on
which `A` acts onto the whole endomorphism algebra `End_k S`, with a central element `e ∈ A` that
fixes `S` pointwise and annihilates the kernel of the action (`lsmul a = lsmul b → e * a = e * b`).
Then `e` is automatically a central idempotent, the fixed-point locus

`TauCeti.centralFixedSubmodule M hc = {x : M | e • x = x}`

is an `A`-submodule of any `A`-module `M` (unlike the piece `e • (⊤ : Submodule k M)` for a
non-central idempotent in `TauCeti.RingTheory.Idempotents.Module`, which is only a `k`-submodule),
and evaluation

`TauCeti.isotypicEval k : S ⊗[k] (S →ₗ[A] M) →ₗ[A] M`,  `s ⊗ T ↦ T s`,

is injective with range equal to `centralFixedSubmodule M hc`. It therefore restricts to an
`A`-linear isomorphism `TauCeti.isotypicTensorEquivOfCentral` onto `centralFixedSubmodule M hc`,
without requiring `k` to be a field or `M` to be finite, projective, or semisimple.

When `A` acts on two finite projective `k`-modules `S₁` and `S₂` so that the combined action
`A →ₐ[k] End_k S₁ × End_k S₂` is bijective, the preimages `e₁` and `e₂` of `(1, 0)` and `(0, 1)`
satisfy the single-factor hypotheses and sum to `1`. Assembling the two single-factor evaluations
gives the **two-factor Morita evaluation**

`TauCeti.isotypicProdTensorEquivOfBijective :`
`  ((S₁ ⊗[k] (S₁ →ₗ[A] M)) × (S₂ ⊗[k] (S₂ →ₗ[A] M))) ≃ₗ[A] M`,
sending `(s₁ ⊗ T₁, s₂ ⊗ T₂)` to `T₁ s₁ + T₂ s₂`.

This is the situation of an odd-dimensional complexified Clifford algebra, which splits as
`End_ℂ S_+ × End_ℂ S_-` along the `±1` eigenspaces of its central volume element.

## Main definitions

* `TauCeti.homOfDualOfCentral`: the multiplicity map `M →ₗ[k] (S →ₗ[A] M)` attached to a dual
  functional on `S` and a central idempotent factor.
* `TauCeti.isotypicTensorEquivOfCentral`: single-factor evaluation
  `S ⊗[k] (S →ₗ[A] M) ≃ₗ[A] centralFixedSubmodule M hc`.
* `TauCeti.isotypicProdTensorEquivOfBijective`: two-factor evaluation
  `((S₁ ⊗[k] (S₁ →ₗ[A] M)) × (S₂ ⊗[k] (S₂ →ₗ[A] M))) ≃ₗ[A] M` for `A ≅ End_k S₁ × End_k S₂`.

## Main results

* `TauCeti.isIdempotentElem_of_smul_eq_self`: `e` is idempotent whenever it fixes `S` and kills the
  kernel of `lsmul`.
* `TauCeti.sum_homOfDualOfCentral_coord_apply`: coordinate reconstruction of `e • x` in a finite
  basis of `S`.
* `TauCeti.isotypicEval_injective_of_central` and
  `TauCeti.range_isotypicEval_eq_centralFixedSubmodule`: injectivity and exact range of
  single-factor evaluation.
* `TauCeti.finrank_centralFixedSubmodule_eq_finrank_mul_finrank_linearMap` and
  `TauCeti.finrank_eq_add_finrank_mul_finrank_linearMap_of_bijective_prod`: dimension formulas over
  a field.

## Relation to single-block Morita evaluation

When the action `A →ₐ[k] End_k S` is already bijective (for example, for an even-dimensional
complexified Clifford algebra), use `TauCeti.homOfDual` and `TauCeti.isotypicTensorEquivOfBijective`
from `TauCeti.RingTheory.Morita.ModuleEnd`. The declarations `TauCeti.homOfDualOfCentral` and
`TauCeti.isotypicTensorEquivOfCentral` adapt that single-block evaluation API to the case where
`A →ₐ[k] End_k S` is only surjective and a central element `e ∈ A` isolates the corresponding block
inside every `A`-module `M`; `TauCeti.isotypicProdTensorEquivOfBijective` packages the two-block
product case `A →ₐ[k] End_k S₁ × End_k S₂` directly into an isomorphism onto `M`.

## References

* T. Y. Lam, *Lectures on Modules and Rings*, GTM 189 (1999), Chapter 7.
* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5.
-/

public section

open Module TensorProduct

namespace TauCeti

/-! ### Single-factor Morita evaluation at a central idempotent -/

section SingleFactor

variable {k A S M N : Type*} [CommSemiring k] [Semiring A] [Algebra k A]
  [AddCommMonoid S] [Module k S] [Module A S] [IsScalarTower k A S]
  [AddCommMonoid M] [Module k M] [Module A M] [IsScalarTower k A M]
  [AddCommMonoid N] [Module k N] [Module A N] [IsScalarTower k A N]
  {e : A}

/-- An element `e ∈ A` that fixes `S` pointwise and kills the kernel of `lsmul` is automatically
idempotent: `e` and `1` have the same image in `End_k S`, so `e * e = e * 1 = e`. -/
theorem isIdempotentElem_of_smul_eq_self (heS : ∀ s : S, e • s = s)
    (hker : ∀ a b : A, Algebra.lsmul k k S a = Algebra.lsmul k k S b → e * a = e * b) :
    IsIdempotentElem e := by
  have he1 : Algebra.lsmul k k S e = Algebra.lsmul k k S (1 : A) := by
    ext s
    simp [heS s]
  simpa only [IsIdempotentElem, mul_one] using hker e 1 he1

/-- Canonical lift of an endomorphism `f : End_k S` into `e * A`, defined as `e * a` for any chosen
preimage `a` of `f`. Under `hker`, this element does not depend on the choice of `a`. -/
private noncomputable def centralLift (e : A)
    (hsurj : Function.Surjective (Algebra.lsmul k k S : A →ₐ[k] Module.End k S))
    (f : Module.End k S) : A :=
  e * Classical.choose (hsurj f)

private theorem centralLift_eq_mul
    (hsurj : Function.Surjective (Algebra.lsmul k k S : A →ₐ[k] Module.End k S))
    (hker : ∀ a b : A, Algebra.lsmul k k S a = Algebra.lsmul k k S b → e * a = e * b)
    {f : Module.End k S} {a : A} (ha : Algebra.lsmul k k S a = f) :
    centralLift e hsurj f = e * a :=
  hker _ a ((Classical.choose_spec (hsurj f)).trans ha.symm)

private theorem centralLift_add
    (hsurj : Function.Surjective (Algebra.lsmul k k S : A →ₐ[k] Module.End k S))
    (hker : ∀ a b : A, Algebra.lsmul k k S a = Algebra.lsmul k k S b → e * a = e * b)
    (f g : Module.End k S) :
    centralLift e hsurj (f + g) = centralLift e hsurj f + centralLift e hsurj g := by
  obtain ⟨a, rfl⟩ := hsurj f
  obtain ⟨b, rfl⟩ := hsurj g
  rw [← map_add, centralLift_eq_mul hsurj hker rfl, centralLift_eq_mul hsurj hker rfl,
    centralLift_eq_mul hsurj hker rfl, mul_add]

private theorem centralLift_smul
    (hsurj : Function.Surjective (Algebra.lsmul k k S : A →ₐ[k] Module.End k S))
    (hker : ∀ a b : A, Algebra.lsmul k k S a = Algebra.lsmul k k S b → e * a = e * b)
    (c : k) (f : Module.End k S) :
    centralLift e hsurj (c • f) = c • centralLift e hsurj f := by
  obtain ⟨a, rfl⟩ := hsurj f
  rw [← map_smul, centralLift_eq_mul hsurj hker rfl, centralLift_eq_mul hsurj hker rfl,
    mul_smul_comm]

private theorem centralLift_one
    (hsurj : Function.Surjective (Algebra.lsmul k k S : A →ₐ[k] Module.End k S))
    (hker : ∀ a b : A, Algebra.lsmul k k S a = Algebra.lsmul k k S b → e * a = e * b) :
    centralLift e hsurj (1 : Module.End k S) = e := by
  rw [centralLift_eq_mul hsurj hker (map_one _), mul_one]

private theorem centralLift_lsmul_mul (hc : ∀ a : A, Commute e a)
    (hsurj : Function.Surjective (Algebra.lsmul k k S : A →ₐ[k] Module.End k S))
    (hker : ∀ a b : A, Algebra.lsmul k k S a = Algebra.lsmul k k S b → e * a = e * b)
    (a : A) (f : Module.End k S) :
    centralLift e hsurj (Algebra.lsmul k k S a * f) = a * centralLift e hsurj f := by
  obtain ⟨b, rfl⟩ := hsurj f
  rw [← map_mul, centralLift_eq_mul hsurj hker rfl, centralLift_eq_mul hsurj hker rfl,
    ← mul_assoc, hc a, mul_assoc]

private theorem centralLift_smul_self (heS : ∀ s : S, e • s = s)
    (hsurj : Function.Surjective (Algebra.lsmul k k S : A →ₐ[k] Module.End k S))
    (f : Module.End k S) (s : S) :
    centralLift e hsurj f • s = f s := by
  rw [centralLift, mul_smul, heS]
  exact congr($(Classical.choose_spec (hsurj f)) s)

/-- Given a central element `e ∈ A` killing the kernel of a surjective action `A →ₐ[k] End_k S`,
a dual form `φ : Dual k S` and a vector `x : M` define the `A`-linear map `s ↦ (e * a) • x`, where
`a ∈ A` acts on `S` as the rank-one endomorphism `t ↦ φ t • s`. -/
noncomputable def homOfDualOfCentral (hc : ∀ a : A, Commute e a)
    (hsurj : Function.Surjective (Algebra.lsmul k k S : A →ₐ[k] Module.End k S))
    (hker : ∀ a b : A, Algebra.lsmul k k S a = Algebra.lsmul k k S b → e * a = e * b)
    (φ : Dual k S) : M →ₗ[k] S →ₗ[A] M where
  toFun x :=
    { toFun s := centralLift e hsurj (φ.smulRight s) • x
      map_add' s t := by
        rw [← LinearMap.smulRightₗ_apply, map_add, LinearMap.smulRightₗ_apply,
          LinearMap.smulRightₗ_apply, centralLift_add hsurj hker, add_smul]
      map_smul' a s := by
        have hmul : φ.smulRight (a • s) = Algebra.lsmul k k S a * φ.smulRight s := by
          ext t
          simp [smul_comm (φ t) a s]
        rw [hmul, centralLift_lsmul_mul hc hsurj hker, mul_smul, RingHom.id_apply] }
  map_add' x y := by
    ext s
    exact smul_add _ x y
  map_smul' c x := by
    ext s
    exact smul_comm _ c x

@[simp]
private theorem homOfDualOfCentral_apply (hc : ∀ a : A, Commute e a)
    (hsurj : Function.Surjective (Algebra.lsmul k k S : A →ₐ[k] Module.End k S))
    (hker : ∀ a b : A, Algebra.lsmul k k S a = Algebra.lsmul k k S b → e * a = e * b)
    (φ : Dual k S) (x : M) (s : S) :
    homOfDualOfCentral hc hsurj hker φ x s = centralLift e hsurj (φ.smulRight s) • x :=
  (rfl)

/-- Evaluating `homOfDualOfCentral` at `s` applies `e * a` to `x` for any `a ∈ A` acting on `S` as
`t ↦ φ t • s`. -/
theorem homOfDualOfCentral_apply_eq_mul_smul (hc : ∀ a : A, Commute e a)
    (hsurj : Function.Surjective (Algebra.lsmul k k S : A →ₐ[k] Module.End k S))
    (hker : ∀ a b : A, Algebra.lsmul k k S a = Algebra.lsmul k k S b → e * a = e * b)
    (φ : Dual k S) (x : M) (s : S) {a : A} (ha : Algebra.lsmul k k S a = φ.smulRight s) :
    homOfDualOfCentral hc hsurj hker φ x s = (e * a) • x := by
  rw [homOfDualOfCentral_apply, centralLift_eq_mul hsurj hker ha]

/-- **Matrix-unit relation at a central idempotent.** When `e` fixes `S` pointwise, evaluating
`homOfDualOfCentral` on `T s` for any `A`-linear `T : S →ₗ[A] M` returns `φ s • T`. -/
@[simp]
theorem homOfDualOfCentral_apply_map (hc : ∀ a : A, Commute e a) (heS : ∀ s : S, e • s = s)
    (hsurj : Function.Surjective (Algebra.lsmul k k S : A →ₐ[k] Module.End k S))
    (hker : ∀ a b : A, Algebra.lsmul k k S a = Algebra.lsmul k k S b → e * a = e * b)
    (φ : Dual k S) (T : S →ₗ[A] M) (s : S) :
    homOfDualOfCentral hc hsurj hker φ (T s) = φ s • T := by
  ext t
  rw [homOfDualOfCentral_apply, ← T.map_smul, centralLift_smul_self heS hsurj,
    LinearMap.smulRight_apply, LinearMap.smul_apply, T.map_smul_of_tower]

/-- The candidate projection-inverse `M →ₗ[k] S ⊗[k] (S →ₗ[A] M)` attached to a dual coordinate
family `∑ᵢ φᵢ(t) vᵢ = t`. -/
private noncomputable def isotypicEvalCentralInv (hc : ∀ a : A, Commute e a)
    (hsurj : Function.Surjective (Algebra.lsmul k k S : A →ₐ[k] Module.End k S))
    (hker : ∀ a b : A, Algebra.lsmul k k S a = Algebra.lsmul k k S b → e * a = e * b)
    {ι : Type*} (s : Finset ι) (φ : ι → Dual k S) (v : ι → S) :
    M →ₗ[k] S ⊗[k] (S →ₗ[A] M) :=
  ∑ i ∈ s, TensorProduct.mk k S (S →ₗ[A] M) (v i) ∘ₗ homOfDualOfCentral hc hsurj hker (φ i)

private theorem centralLift_sum {ι : Type*}
    (hsurj : Function.Surjective (Algebra.lsmul k k S : A →ₐ[k] Module.End k S))
    (hker : ∀ a b : A, Algebra.lsmul k k S a = Algebra.lsmul k k S b → e * a = e * b)
    (s : Finset ι) (f : ι → Module.End k S) :
    centralLift e hsurj (∑ i ∈ s, f i) = ∑ i ∈ s, centralLift e hsurj (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty, centralLift_eq_mul hsurj hker (map_zero _), mul_zero]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, centralLift_add hsurj hker, ih]

private theorem isotypicEval_isotypicEvalCentralInv (hc : ∀ a : A, Commute e a)
    (hsurj : Function.Surjective (Algebra.lsmul k k S : A →ₐ[k] Module.End k S))
    (hker : ∀ a b : A, Algebra.lsmul k k S a = Algebra.lsmul k k S b → e * a = e * b)
    {ι : Type*} (s : Finset ι) (φ : ι → Dual k S) (v : ι → S)
    (hv : ∀ t, ∑ i ∈ s, φ i t • v i = t) (x : M) :
    isotypicEval k (isotypicEvalCentralInv hc hsurj hker s φ v x) = e • x := by
  have hsum : ∑ i ∈ s, (φ i).smulRight (v i) = (1 : Module.End k S) := by
    ext t
    simp [hv t]
  have hlift : ∑ i ∈ s, centralLift e hsurj ((φ i).smulRight (v i)) = e := by
    rw [← centralLift_sum hsurj hker, hsum, centralLift_one hsurj hker]
  simp only [isotypicEvalCentralInv, LinearMap.sum_apply, LinearMap.comp_apply,
    TensorProduct.mk_apply, map_sum, isotypicEval_tmul, homOfDualOfCentral_apply,
    ← Finset.sum_smul, hlift]

private theorem isotypicEvalCentralInv_isotypicEval (hc : ∀ a : A, Commute e a)
    (heS : ∀ s : S, e • s = s)
    (hsurj : Function.Surjective (Algebra.lsmul k k S : A →ₐ[k] Module.End k S))
    (hker : ∀ a b : A, Algebra.lsmul k k S a = Algebra.lsmul k k S b → e * a = e * b)
    {ι : Type*} (s : Finset ι) (φ : ι → Dual k S) (v : ι → S)
    (hv : ∀ t, ∑ i ∈ s, φ i t • v i = t) (y : S ⊗[k] (S →ₗ[A] M)) :
    isotypicEvalCentralInv hc hsurj hker s φ v (isotypicEval k y) = y := by
  induction y using TensorProduct.inductionOn with
  | tmul t T =>
    simp only [isotypicEvalCentralInv, LinearMap.sum_apply, LinearMap.comp_apply,
      TensorProduct.mk_apply, isotypicEval_tmul, homOfDualOfCentral_apply_map hc heS hsurj hker,
      ← TensorProduct.smul_tmul, ← TensorProduct.sum_tmul, hv t]
  | add y z hy hz => rw [map_add, map_add, hy, hz]

/-- **Single-factor evaluation is injective** when `S` is finite projective over `k` and `e` is a
central element fixing `S` and annihilating the kernel of a surjective action `A →ₐ[k] End_k S`. -/
theorem isotypicEval_injective_of_central [Module.Finite k S] [Module.Projective k S]
    (hc : ∀ a : A, Commute e a) (heS : ∀ s : S, e • s = s)
    (hsurj : Function.Surjective (Algebra.lsmul k k S : A →ₐ[k] Module.End k S))
    (hker : ∀ a b : A, Algebra.lsmul k k S a = Algebra.lsmul k k S b → e * a = e * b) :
    Function.Injective (isotypicEval k (A := A) (S := S) (M := M)) := by
  obtain ⟨u, hu⟩ := (dualTensorHom_bijective (R := k) (M := S) (N := S)).2 LinearMap.id
  obtain ⟨s, rfl⟩ := TensorProduct.exists_finset u
  have hs (t : S) : ∑ p ∈ s, p.1 t • p.2 = t := by
    simpa [dualTensorHom_apply] using LinearMap.congr_fun hu t
  exact Function.LeftInverse.injective
    (isotypicEvalCentralInv_isotypicEval hc heS hsurj hker s _ _ hs)

/-- **Exact range of single-factor evaluation.** Under the single-factor Morita hypotheses, the
image of `S ⊗[k] (S →ₗ[A] M) →ₗ[A] M` is precisely the fixed-point submodule
`centralFixedSubmodule M hc = {x : M | e • x = x}`. -/
theorem range_isotypicEval_eq_centralFixedSubmodule [Module.Finite k S] [Module.Projective k S]
    (hc : ∀ a : A, Commute e a) (heS : ∀ s : S, e • s = s)
    (hsurj : Function.Surjective (Algebra.lsmul k k S : A →ₐ[k] Module.End k S))
    (hker : ∀ a b : A, Algebra.lsmul k k S a = Algebra.lsmul k k S b → e * a = e * b) :
    LinearMap.range (isotypicEval k (A := A) (S := S) (M := M)) = centralFixedSubmodule M hc := by
  obtain ⟨u, hu⟩ := (dualTensorHom_bijective (R := k) (M := S) (N := S)).2 LinearMap.id
  obtain ⟨s, rfl⟩ := TensorProduct.exists_finset u
  have hs (t : S) : ∑ p ∈ s, p.1 t • p.2 = t := by
    simpa [dualTensorHom_apply] using LinearMap.congr_fun hu t
  refine le_antisymm ?_ fun x hx ↦ ?_
  · rintro _ ⟨y, rfl⟩
    induction y using TensorProduct.inductionOn with
    | tmul t T =>
      rw [isotypicEval_tmul]
      exact apply_mem_centralFixedSubmodule hc heS T t
    | add y z hy hz =>
      rw [map_add]
      exact (centralFixedSubmodule M hc).add_mem hy hz
  · exact ⟨isotypicEvalCentralInv hc hsurj hker s _ _ x,
      (isotypicEval_isotypicEvalCentralInv hc hsurj hker s _ _ hs x).trans
        ((mem_centralFixedSubmodule hc).mp hx)⟩

/-- A finite basis of `S` reconstructs the projection `e • x` of any vector `x : M` from its
single-factor multiplicity components `homOfDualOfCentral hc hsurj hker (b.coord i) x`. -/
theorem sum_homOfDualOfCentral_coord_apply (hc : ∀ a : A, Commute e a)
    (hsurj : Function.Surjective (Algebra.lsmul k k S : A →ₐ[k] Module.End k S))
    (hker : ∀ a b : A, Algebra.lsmul k k S a = Algebra.lsmul k k S b → e * a = e * b)
    {ι : Type*} [Fintype ι] (b : Basis ι k S) (x : M) :
    ∑ i, homOfDualOfCentral hc hsurj hker (b.coord i) x (b i) = e • x := by
  have hsum := isotypicEval_isotypicEvalCentralInv hc hsurj hker Finset.univ b.coord b
    (fun t ↦ by simp [Basis.coord_apply]) x
  simpa only [isotypicEvalCentralInv, LinearMap.sum_apply, LinearMap.comp_apply,
    TensorProduct.mk_apply, map_sum, isotypicEval_tmul] using hsum

/-- **Single-factor Morita evaluation.** Evaluation `s ⊗ T ↦ T s` identifies `S ⊗[k] (S →ₗ[A] M)`
with the `A`-submodule `centralFixedSubmodule M hc = {x : M | e • x = x}`. -/
noncomputable def isotypicTensorEquivOfCentral [Module.Finite k S] [Module.Projective k S]
    (hc : ∀ a : A, Commute e a) (heS : ∀ s : S, e • s = s)
    (hsurj : Function.Surjective (Algebra.lsmul k k S : A →ₐ[k] Module.End k S))
    (hker : ∀ a b : A, Algebra.lsmul k k S a = Algebra.lsmul k k S b → e * a = e * b) :
    S ⊗[k] (S →ₗ[A] M) ≃ₗ[A] centralFixedSubmodule M hc :=
  (LinearEquiv.ofInjective (isotypicEval k)
      (isotypicEval_injective_of_central hc heS hsurj hker)).trans
    (LinearEquiv.ofEq _ _ (range_isotypicEval_eq_centralFixedSubmodule hc heS hsurj hker))

/-- Coercing `isotypicTensorEquivOfCentral` to `M` recovers `isotypicEval k`. -/
@[simp]
theorem coe_isotypicTensorEquivOfCentral_apply [Module.Finite k S] [Module.Projective k S]
    (hc : ∀ a : A, Commute e a) (heS : ∀ s : S, e • s = s)
    (hsurj : Function.Surjective (Algebra.lsmul k k S : A →ₐ[k] Module.End k S))
    (hker : ∀ a b : A, Algebra.lsmul k k S a = Algebra.lsmul k k S b → e * a = e * b)
    (x : S ⊗[k] (S →ₗ[A] M)) :
    (isotypicTensorEquivOfCentral hc heS hsurj hker x : M) = isotypicEval k x :=
  (rfl)

/-- The inverse of `isotypicTensorEquivOfCentral` for any finite coordinate family
`∑ᵢ φᵢ(t) vᵢ = t` on `S`. -/
theorem isotypicTensorEquivOfCentral_symm_apply [Module.Finite k S] [Module.Projective k S]
    (hc : ∀ a : A, Commute e a) (heS : ∀ s : S, e • s = s)
    (hsurj : Function.Surjective (Algebra.lsmul k k S : A →ₐ[k] Module.End k S))
    (hker : ∀ a b : A, Algebra.lsmul k k S a = Algebra.lsmul k k S b → e * a = e * b)
    {ι : Type*} (s : Finset ι) (φ : ι → Dual k S) (v : ι → S)
    (hv : ∀ t, ∑ i ∈ s, φ i t • v i = t) (x : centralFixedSubmodule M hc) :
    (isotypicTensorEquivOfCentral hc heS hsurj hker).symm x =
      ∑ i ∈ s, v i ⊗ₜ homOfDualOfCentral hc hsurj hker (φ i) (x : M) := by
  apply (isotypicTensorEquivOfCentral hc heS hsurj hker).injective
  apply Subtype.ext
  rw [LinearEquiv.apply_symm_apply, coe_isotypicTensorEquivOfCentral_apply]
  calc
    (x : M) = e • (x : M) := ((mem_centralFixedSubmodule hc).mp x.2).symm
    _ = isotypicEval k (isotypicEvalCentralInv hc hsurj hker s φ v (x : M)) :=
      (isotypicEval_isotypicEvalCentralInv hc hsurj hker s φ v hv (x : M)).symm
    _ = isotypicEval k (∑ i ∈ s, v i ⊗ₜ homOfDualOfCentral hc hsurj hker (φ i) (x : M)) := by
      simp [isotypicEvalCentralInv]

/-- The inverse of `isotypicTensorEquivOfCentral` in a finite basis `b` of `S`. -/
theorem isotypicTensorEquivOfCentral_symm_apply_basis [Module.Finite k S] [Module.Projective k S]
    (hc : ∀ a : A, Commute e a) (heS : ∀ s : S, e • s = s)
    (hsurj : Function.Surjective (Algebra.lsmul k k S : A →ₐ[k] Module.End k S))
    (hker : ∀ a b : A, Algebra.lsmul k k S a = Algebra.lsmul k k S b → e * a = e * b)
    {ι : Type*} [Fintype ι] (b : Basis ι k S) (x : centralFixedSubmodule M hc) :
    (isotypicTensorEquivOfCentral hc heS hsurj hker).symm x =
      ∑ i, b i ⊗ₜ homOfDualOfCentral hc hsurj hker (b.coord i) (x : M) :=
  isotypicTensorEquivOfCentral_symm_apply hc heS hsurj hker Finset.univ b.coord b
    (fun t ↦ by simp [Basis.coord_apply]) x

/-- **Naturality of the single-factor inverse** along any `A`-linear map `g : M →ₗ[A] N`. -/
@[simp]
theorem isotypicTensorEquivOfCentral_symm_apply_map [Module.Finite k S] [Module.Projective k S]
    (hc : ∀ a : A, Commute e a) (heS : ∀ s : S, e • s = s)
    (hsurj : Function.Surjective (Algebra.lsmul k k S : A →ₐ[k] Module.End k S))
    (hker : ∀ a b : A, Algebra.lsmul k k S a = Algebra.lsmul k k S b → e * a = e * b)
    (g : M →ₗ[A] N) (x : centralFixedSubmodule M hc) :
    (isotypicTensorEquivOfCentral (M := N) hc heS hsurj hker).symm
        ⟨g x, by
          rw [mem_centralFixedSubmodule, ← g.map_smul, (mem_centralFixedSubmodule hc).mp x.2]⟩ =
      AlgebraTensorModule.map (LinearMap.id (R := A) (M := S))
        (LinearMap.compRight (M := S) k g)
        ((isotypicTensorEquivOfCentral hc heS hsurj hker).symm x) := by
  apply (isotypicTensorEquivOfCentral (M := N) hc heS hsurj hker).injective
  apply Subtype.ext
  rw [LinearEquiv.apply_symm_apply, coe_isotypicTensorEquivOfCentral_apply, isotypicEval_map_apply,
    ← coe_isotypicTensorEquivOfCentral_apply hc heS hsurj hker, LinearEquiv.apply_symm_apply]

end SingleFactor

/-! ### Two-factor Morita evaluation for `A ≅ End_k S₁ × End_k S₂` -/

section TwoFactor

variable {k A S₁ S₂ M N : Type*} [CommSemiring k] [Semiring A] [Algebra k A]
  [AddCommMonoid S₁] [Module k S₁] [Module A S₁] [IsScalarTower k A S₁]
  [AddCommMonoid S₂] [Module k S₂] [Module A S₂] [IsScalarTower k A S₂]
  [AddCommMonoid M] [Module k M] [Module A M] [IsScalarTower k A M]
  [AddCommMonoid N] [Module k N] [Module A N] [IsScalarTower k A N]
  (h : Function.Bijective
    ((Algebra.lsmul k k S₁).prod (Algebra.lsmul k k S₂) :
      A →ₐ[k] Module.End k S₁ × Module.End k S₂))

private noncomputable def prodIdempotentFst : A :=
  (AlgEquiv.ofBijective _ h).symm (1, 0)

private noncomputable def prodIdempotentSnd : A :=
  (AlgEquiv.ofBijective _ h).symm (0, 1)

private theorem apply_prodIdempotentFst :
    AlgEquiv.ofBijective _ h (prodIdempotentFst h) = (1, 0) :=
  (AlgEquiv.ofBijective _ h).apply_symm_apply (1, 0)

private theorem apply_prodIdempotentSnd :
    AlgEquiv.ofBijective _ h (prodIdempotentSnd h) = (0, 1) :=
  (AlgEquiv.ofBijective _ h).apply_symm_apply (0, 1)

private theorem commute_prodIdempotentFst (a : A) : Commute (prodIdempotentFst h) a := by
  rw [commute_iff_eq]
  apply (AlgEquiv.ofBijective _ h).injective
  rw [map_mul, map_mul, apply_prodIdempotentFst]
  ext1 <;> simp

private theorem commute_prodIdempotentSnd (a : A) : Commute (prodIdempotentSnd h) a := by
  rw [commute_iff_eq]
  apply (AlgEquiv.ofBijective _ h).injective
  rw [map_mul, map_mul, apply_prodIdempotentSnd]
  ext1 <;> simp

private theorem prodIdempotentFst_smul (s : S₁) : prodIdempotentFst h • s = s := by
  have h1 := congrArg Prod.fst (apply_prodIdempotentFst h)
  rw [AlgEquiv.ofBijective_apply, AlgHom.prod_apply] at h1
  exact congr($h1 s)

private theorem prodIdempotentSnd_smul (s : S₂) : prodIdempotentSnd h • s = s := by
  have h2 := congrArg Prod.snd (apply_prodIdempotentSnd h)
  rw [AlgEquiv.ofBijective_apply, AlgHom.prod_apply] at h2
  exact congr($h2 s)

include h in
private theorem lsmul_fst_surjective :
    Function.Surjective (Algebra.lsmul k k S₁ : A →ₐ[k] Module.End k S₁) := fun f ↦
  ⟨(AlgEquiv.ofBijective _ h).symm (f, 0),
    congrArg Prod.fst ((AlgEquiv.ofBijective _ h).apply_symm_apply (f, 0))⟩

include h in
private theorem lsmul_snd_surjective :
    Function.Surjective (Algebra.lsmul k k S₂ : A →ₐ[k] Module.End k S₂) := fun g ↦
  ⟨(AlgEquiv.ofBijective _ h).symm (0, g),
    congrArg Prod.snd ((AlgEquiv.ofBijective _ h).apply_symm_apply (0, g))⟩

private theorem prodIdempotentFst_mul_eq {a b : A}
    (hab : Algebra.lsmul k k S₁ a = Algebra.lsmul k k S₁ b) :
    prodIdempotentFst h * a = prodIdempotentFst h * b := by
  apply (AlgEquiv.ofBijective _ h).injective
  rw [map_mul, map_mul, apply_prodIdempotentFst]
  ext1 <;> simp [hab]

private theorem prodIdempotentSnd_mul_eq {a b : A}
    (hab : Algebra.lsmul k k S₂ a = Algebra.lsmul k k S₂ b) :
    prodIdempotentSnd h * a = prodIdempotentSnd h * b := by
  apply (AlgEquiv.ofBijective _ h).injective
  rw [map_mul, map_mul, apply_prodIdempotentSnd]
  ext1 <;> simp [hab]

private theorem prodIdempotent_add : prodIdempotentFst h + prodIdempotentSnd h = 1 := by
  apply (AlgEquiv.ofBijective _ h).injective
  rw [map_add, map_one, apply_prodIdempotentFst, apply_prodIdempotentSnd]
  ext1 <;> simp

private theorem prodIdempotent_mul_fst_snd : prodIdempotentFst h * prodIdempotentSnd h = 0 := by
  apply (AlgEquiv.ofBijective _ h).injective
  rw [map_mul, map_zero, apply_prodIdempotentFst, apply_prodIdempotentSnd]
  ext1 <;> simp

private theorem prodIdempotent_mul_snd_fst : prodIdempotentSnd h * prodIdempotentFst h = 0 := by
  apply (AlgEquiv.ofBijective _ h).injective
  rw [map_mul, map_zero, apply_prodIdempotentFst, apply_prodIdempotentSnd]
  ext1 <;> simp

variable [Module.Finite k S₁] [Module.Projective k S₁]
  [Module.Finite k S₂] [Module.Projective k S₂]

include h in
/-- **Two-factor evaluation is bijective** when `A` acts on the finite projective modules `S₁` and
`S₂` as `End_k S₁ × End_k S₂`. -/
theorem isotypicProdEval_bijective_of_bijective_prod :
    Function.Bijective
      ((isotypicEval k (A := A) (S := S₁) (M := M)).coprod
        (isotypicEval k (A := A) (S := S₂) (M := M))) := by
  let e₁ := isotypicTensorEquivOfCentral (M := M) (commute_prodIdempotentFst h)
    (prodIdempotentFst_smul h) (lsmul_fst_surjective h) (fun _ _ ↦ prodIdempotentFst_mul_eq h)
  let e₂ := isotypicTensorEquivOfCentral (M := M) (commute_prodIdempotentSnd h)
    (prodIdempotentSnd_smul h) (lsmul_snd_surjective h) (fun _ _ ↦ prodIdempotentSnd_mul_eq h)
  have idem₁ := isIdempotentElem_of_smul_eq_self (prodIdempotentFst_smul h)
    (fun _ _ ↦ prodIdempotentFst_mul_eq h)
  have idem₂ := isIdempotentElem_of_smul_eq_self (prodIdempotentSnd_smul h)
    (fun _ _ ↦ prodIdempotentSnd_mul_eq h)
  let inv : M → ((S₁ ⊗[k] (S₁ →ₗ[A] M)) × (S₂ ⊗[k] (S₂ →ₗ[A] M))) := fun m ↦
    (e₁.symm ⟨prodIdempotentFst h • m, by rw [mem_centralFixedSubmodule, ← mul_smul, idem₁]⟩,
     e₂.symm ⟨prodIdempotentSnd h • m, by rw [mem_centralFixedSubmodule, ← mul_smul, idem₂]⟩)
  have coe_e₁ (z) : isotypicEval k z = (e₁ z : M) := by simp [e₁]
  have coe_e₂ (z) : isotypicEval k z = (e₂ z : M) := by simp [e₂]
  refine ⟨Function.LeftInverse.injective (g := inv) fun ⟨x, y⟩ ↦ ?_,
    Function.RightInverse.surjective (g := inv) fun m ↦ ?_⟩
  · have hx : prodIdempotentFst h • isotypicEval k x = isotypicEval k x := by
      rw [coe_e₁]
      exact (mem_centralFixedSubmodule _).mp (e₁ x).2
    have hy : prodIdempotentSnd h • isotypicEval k y = isotypicEval k y := by
      rw [coe_e₂]
      exact (mem_centralFixedSubmodule _).mp (e₂ y).2
    have hxy : prodIdempotentFst h • isotypicEval k y = 0 := by
      rw [← hy, ← mul_smul, prodIdempotent_mul_fst_snd h, zero_smul]
    have hyx : prodIdempotentSnd h • isotypicEval k x = 0 := by
      rw [← hx, ← mul_smul, prodIdempotent_mul_snd_fst h, zero_smul]
    refine Prod.ext (e₁.injective (Subtype.ext ?_)) (e₂.injective (Subtype.ext ?_))
    · rw [e₁.apply_symm_apply]
      simpa only [inv, LinearMap.coprod_apply, smul_add, hx, hxy, add_zero] using coe_e₁ x
    · rw [e₂.apply_symm_apply]
      simpa only [inv, LinearMap.coprod_apply, smul_add, hyx, hy, zero_add] using coe_e₂ y
  · simp only [inv, LinearMap.coprod_apply, coe_e₁, coe_e₂, e₁.apply_symm_apply,
      e₂.apply_symm_apply]
    rw [← add_smul, prodIdempotent_add h, one_smul]

/-- **Two-factor Morita evaluation.** When `A` acts on two finite projective `k`-modules `S₁` and
`S₂` via a bijection `A →ₐ[k] End_k S₁ × End_k S₂`, every `A`-module `M` decomposes canonically as
`(S₁ ⊗[k] (S₁ →ₗ[A] M)) × (S₂ ⊗[k] (S₂ →ₗ[A] M))` under `(s₁ ⊗ T₁, s₂ ⊗ T₂) ↦ T₁ s₁ + T₂ s₂`. -/
noncomputable def isotypicProdTensorEquivOfBijective :
    ((S₁ ⊗[k] (S₁ →ₗ[A] M)) × (S₂ ⊗[k] (S₂ →ₗ[A] M))) ≃ₗ[A] M :=
  .ofBijective ((isotypicEval k).coprod (isotypicEval k))
    (isotypicProdEval_bijective_of_bijective_prod h)

/-- Applying `isotypicProdTensorEquivOfBijective` sums the two single-factor evaluations. -/
@[simp]
theorem isotypicProdTensorEquivOfBijective_apply
    (p : (S₁ ⊗[k] (S₁ →ₗ[A] M)) × (S₂ ⊗[k] (S₂ →ₗ[A] M))) :
    isotypicProdTensorEquivOfBijective h p = isotypicEval k p.1 + isotypicEval k p.2 :=
  (rfl)

/-- **Naturality of the two-factor inverse**: through the two-factor decomposition, an `A`-linear
map `g : M →ₗ[A] N` acts by `1 ⊗ (g ∘ ·)` on each factor. -/
@[simp]
theorem isotypicProdTensorEquivOfBijective_symm_apply_map (g : M →ₗ[A] N) (m : M) :
    (isotypicProdTensorEquivOfBijective (M := N) h).symm (g m) =
      (AlgebraTensorModule.map (LinearMap.id (R := A) (M := S₁))
          (LinearMap.compRight (M := S₁) k g)
          ((isotypicProdTensorEquivOfBijective h).symm m).1,
       AlgebraTensorModule.map (LinearMap.id (R := A) (M := S₂))
          (LinearMap.compRight (M := S₂) k g)
          ((isotypicProdTensorEquivOfBijective h).symm m).2) := by
  apply (isotypicProdTensorEquivOfBijective (M := N) h).injective
  rw [LinearEquiv.apply_symm_apply, isotypicProdTensorEquivOfBijective_apply,
    isotypicEval_map_apply, isotypicEval_map_apply, ← map_add,
    ← isotypicProdTensorEquivOfBijective_apply h, LinearEquiv.apply_symm_apply]

end TwoFactor

/-! ### Dimension formulas over a field -/

section Field

variable {k A S S₁ S₂ M : Type*} [Field k] [Semiring A] [Algebra k A]
  [AddCommGroup S] [Module k S] [Module A S] [IsScalarTower k A S] [FiniteDimensional k S]
  [AddCommGroup S₁] [Module k S₁] [Module A S₁] [IsScalarTower k A S₁] [FiniteDimensional k S₁]
  [AddCommGroup S₂] [Module k S₂] [Module A S₂] [IsScalarTower k A S₂] [FiniteDimensional k S₂]
  [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]

/-- Over a field, the dimension of `centralFixedSubmodule M hc` is `dim S · dim (S →ₗ[A] M)`,
without assuming `M` is finite-dimensional. -/
theorem finrank_centralFixedSubmodule_eq_finrank_mul_finrank_linearMap
    {e : A} (hc : ∀ a : A, Commute e a) (heS : ∀ s : S, e • s = s)
    (hsurj : Function.Surjective (Algebra.lsmul k k S : A →ₐ[k] Module.End k S))
    (hker : ∀ a b : A, Algebra.lsmul k k S a = Algebra.lsmul k k S b → e * a = e * b) :
    finrank k (centralFixedSubmodule M hc) = finrank k S * finrank k (S →ₗ[A] M) := by
  rw [← ((isotypicTensorEquivOfCentral (M := M) hc heS hsurj hker).restrictScalars k).finrank_eq,
    finrank_tensorProduct]

/-- Over a field, a finite-dimensional module `M` over `A ≅ End_k S₁ × End_k S₂` has dimension
`dim S₁ · dim (S₁ →ₗ[A] M) + dim S₂ · dim (S₂ →ₗ[A] M)`. Finite-dimensionality of `M` is needed
because `finrank` returns zero on infinite-dimensional spaces. -/
theorem finrank_eq_add_finrank_mul_finrank_linearMap_of_bijective_prod [FiniteDimensional k M]
    (h : Function.Bijective
      ((Algebra.lsmul k k S₁).prod (Algebra.lsmul k k S₂) :
        A →ₐ[k] Module.End k S₁ × Module.End k S₂)) :
    finrank k M =
      finrank k S₁ * finrank k (S₁ →ₗ[A] M) + finrank k S₂ * finrank k (S₂ →ₗ[A] M) := by
  have heq := ((isotypicProdTensorEquivOfBijective (M := M) h).restrictScalars k).symm
  have hfin₁ : FiniteDimensional k (S₁ ⊗[k] (S₁ →ₗ[A] M)) :=
    Module.Finite.of_surjective ((LinearMap.fst k _ _).comp heq.toLinearMap)
      (Prod.fst_surjective.comp heq.surjective)
  have hfin₂ : FiniteDimensional k (S₂ ⊗[k] (S₂ →ₗ[A] M)) :=
    Module.Finite.of_surjective ((LinearMap.snd k _ _).comp heq.toLinearMap)
      (Prod.snd_surjective.comp heq.surjective)
  rw [← ((isotypicProdTensorEquivOfBijective (M := M) h).restrictScalars k).finrank_eq,
    Module.finrank_prod, finrank_tensorProduct, finrank_tensorProduct]

end Field

end TauCeti

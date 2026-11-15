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

The first section records the companion facts on intertwiner spaces: an `A`-submodule containing
every homomorphic image of `S` captures the whole intertwiner space
(`Submodule.linearMapSubtypeEquiv`), and any `A`-linear map between modules on which an element
`z ∈ A` acts by scalars `μ` and `ν` with `μ - ν` regular on the target vanishes
(`LinearMap.eq_zero_of_smul_eq_of_isSMulRegular`).

## Main definitions

* `Submodule.linearMapSubtypeEquiv`: postcomposition `(S →ₗ[A] p) ≃ₗ[k] (S →ₗ[A] M)` when every
  `A`-linear map `S →ₗ[A] M` lands in `p`.
* `TauCeti.centralFixedSubmodule`: the `A`-submodule `{x : M | e • x = x}` cut out by an element
  `e` commuting with `A`.
* `TauCeti.homOfDualOfCentral`: the multiplicity map `M →ₗ[k] (S →ₗ[A] M)` attached to a dual
  functional on `S` and a central idempotent factor.
* `TauCeti.isotypicTensorEquivOfCentral`: single-factor evaluation
  `S ⊗[k] (S →ₗ[A] M) ≃ₗ[A] centralFixedSubmodule M hc`.
* `TauCeti.isotypicProdTensorEquivOfBijective`: two-factor evaluation
  `((S₁ ⊗[k] (S₁ →ₗ[A] M)) × (S₂ ⊗[k] (S₂ →ₗ[A] M))) ≃ₗ[A] M` for `A ≅ End_k S₁ × End_k S₂`.

## Main results

* `LinearMap.eq_zero_of_smul_eq_of_isSMulRegular` and
  `TauCeti.subsingleton_linearMap_of_smul_eq_of_ne`: cross-eigenvalue vanishing of `A`-linear maps.
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

## Implementation notes

`TauCeti.homOfDualOfCentral` and `TauCeti.isotypicTensorEquivOfCentral` adapt the matrix-unit
construction of `TauCeti.homOfDual` and `TauCeti.isotypicTensorEquivOfBijective` in
`TauCeti.RingTheory.Morita.ModuleEnd` from a bijective action `A ≃ₐ[k] End_k S` to a surjective
action with a central idempotent factor. Rather than choosing a splitting of `A →ₐ[k] End_k S`
directly, the inverse lifts an endomorphism `f : End_k S` to `e * a` for any preimage `a` of `f`.
The kernel hypothesis `lsmul a = lsmul b → e * a = e * b` makes `e * a` independent of the chosen
preimage, so additivity, `k`-linearity, and left `A`-equivariance follow without additional
assumptions on `A`.

## References

* T. Y. Lam, *Lectures on Modules and Rings*, GTM 189 (1999), Chapter 7.
* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5.
-/

public section

open Module TensorProduct
open scoped Pointwise

/-! ### Intertwiners into invariant submodules and cross-eigenvalue vanishing -/

namespace Submodule

variable (k : Type*) {A S M : Type*} [Semiring k] [Semiring A] [SMul k A]
  [AddCommMonoid S] [Module A S]
  [AddCommMonoid M] [Module k M] [Module A M] [IsScalarTower k A M] [SMulCommClass A k M]

/-- Postcomposition with `p.subtype` identifies `S →ₗ[A] p` with `S →ₗ[A] M` whenever every
`A`-linear map from `S` to `M` lands inside the `A`-submodule `p`. -/
def linearMapSubtypeEquiv (p : Submodule A M) (hp : ∀ (f : S →ₗ[A] M) (s : S), f s ∈ p) :
    (S →ₗ[A] p) ≃ₗ[k] (S →ₗ[A] M) where
  toFun g := p.subtype.comp g
  invFun f := f.codRestrict p (hp f)
  map_add' g₁ g₂ := by
    ext s
    simp
  map_smul' c g := by
    ext s
    simp
  left_inv g := by
    ext s
    rfl
  right_inv f := by
    ext s
    rfl

/-- Applying `p.linearMapSubtypeEquiv` postcomposes with `p.subtype`. -/
@[simp]
theorem linearMapSubtypeEquiv_apply (p : Submodule A M)
    (hp : ∀ (f : S →ₗ[A] M) (s : S), f s ∈ p) (g : S →ₗ[A] p) :
    p.linearMapSubtypeEquiv k hp g = p.subtype.comp g :=
  (rfl)

/-- Applying the inverse of `p.linearMapSubtypeEquiv` restricts the codomain to `p`. -/
@[simp]
theorem coe_linearMapSubtypeEquiv_symm_apply (p : Submodule A M)
    (hp : ∀ (f : S →ₗ[A] M) (s : S), f s ∈ p) (f : S →ₗ[A] M) (s : S) :
    ((p.linearMapSubtypeEquiv k hp).symm f s : M) = f s :=
  (rfl)

end Submodule

namespace LinearMap

section Semiring

variable {k A S M : Type*} [Semiring k] [Semiring A] [SMul k A]
  [AddCommMonoid S] [Module k S] [Module A S] [IsScalarTower k A S]
  [AddCommMonoid M] [Module k M] [Module A M] [IsScalarTower k A M]

/-- An `A`-linear map carries a `μ`-eigenvector of `z ∈ A` to a `μ`-eigenvector of `z`. -/
theorem smul_apply_of_smul_eq (f : S →ₗ[A] M) {z : A} {μ : k}
    (hz : ∀ s : S, z • s = μ • s) (s : S) :
    z • f s = μ • f s := by
  rw [← f.map_smul, hz, f.map_smul_of_tower]

end Semiring

section Ring

variable {k A S M : Type*} [Ring k] [Semiring A] [SMul k A]
  [AddCommMonoid S] [Module k S] [Module A S] [IsScalarTower k A S]
  [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]

/-- **Cross-eigenvalue vanishing.** If `z ∈ A` acts on `S` by `μ : k` and on `M` by `ν : k`, and
`μ - ν` acts regularly on `M`, then every `A`-linear map `S →ₗ[A] M` is zero. -/
theorem eq_zero_of_smul_eq_of_isSMulRegular (f : S →ₗ[A] M) {z : A} {μ ν : k}
    (hzS : ∀ s : S, z • s = μ • s) (hzM : ∀ x : M, z • x = ν • x)
    (hreg : IsSMulRegular M (μ - ν)) :
    f = 0 := by
  ext s
  refine hreg.eq_iff.mp ?_
  rw [LinearMap.zero_apply, smul_zero, sub_smul, ← f.smul_apply_of_smul_eq hzS, hzM, sub_self]

end Ring

end LinearMap

namespace TauCeti

section Vanishing

/-- The space of `A`-linear maps `S →ₗ[A] M` is a subsingleton when `z ∈ A` acts by scalars `μ` and
`ν` whose difference `μ - ν` is regular on `M`. -/
theorem subsingleton_linearMap_of_smul_eq_of_isSMulRegular
    {k A S M : Type*} [Ring k] [Semiring A] [SMul k A]
    [AddCommMonoid S] [Module k S] [Module A S] [IsScalarTower k A S]
    [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
    {z : A} {μ ν : k} (hzS : ∀ s : S, z • s = μ • s) (hzM : ∀ x : M, z • x = ν • x)
    (hreg : IsSMulRegular M (μ - ν)) :
    Subsingleton (S →ₗ[A] M) :=
  subsingleton_of_forall_eq 0 fun f ↦ f.eq_zero_of_smul_eq_of_isSMulRegular hzS hzM hreg

/-- Over a division ring, `S →ₗ[A] M` is trivial whenever `z ∈ A` acts on `S` and `M` by distinct
scalars `μ ≠ ν`. -/
theorem subsingleton_linearMap_of_smul_eq_of_ne
    {k A S M : Type*} [DivisionRing k] [Semiring A] [SMul k A]
    [AddCommMonoid S] [Module k S] [Module A S] [IsScalarTower k A S]
    [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
    {z : A} {μ ν : k} (hzS : ∀ s : S, z • s = μ • s) (hzM : ∀ x : M, z • x = ν • x)
    (hne : μ ≠ ν) :
    Subsingleton (S →ₗ[A] M) :=
  subsingleton_linearMap_of_smul_eq_of_isSMulRegular hzS hzM
    ((isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hne)).isSMulRegular M)

end Vanishing

/-! ### The `A`-submodule fixed by a central element -/

section CentralFixedSubmodule

variable {A : Type*} [Semiring A] {e : A}

/-- The `A`-submodule `{x : M | e • x = x}` of elements fixed by a central element `e ∈ A`.
Centrality makes `{x | e • x = x}` closed under the full `A`-action, even when `A` is
noncommutative. -/
def centralFixedSubmodule (M : Type*) [AddCommMonoid M] [Module A M]
    (hc : ∀ a : A, Commute e a) : Submodule A M where
  carrier := {x : M | e • x = x}
  zero_mem' := smul_zero e
  add_mem' {x y} hx hy := by
    rw [Set.mem_ofPred, smul_add, hx.out, hy.out]
  smul_mem' a x hx := by
    rw [Set.mem_ofPred, ← mul_smul, (hc a).eq, mul_smul, hx.out]

/-- Membership in `centralFixedSubmodule M hc` is the fixed-point equation `e • x = x`. -/
@[simp]
theorem mem_centralFixedSubmodule {M : Type*} [AddCommMonoid M] [Module A M]
    (hc : ∀ a : A, Commute e a) {x : M} :
    x ∈ centralFixedSubmodule M hc ↔ e • x = x :=
  Iff.rfl

/-- For an idempotent central element `e`, restricting scalars of `centralFixedSubmodule M hc` to
`k` recovers the Peirce piece `e • (⊤ : Submodule k M)`. -/
theorem centralFixedSubmodule_restrictScalars {k M : Type*} [Semiring k] [SMul k A]
    [AddCommMonoid M] [Module k M] [Module A M] [IsScalarTower k A M] [SMulCommClass A k M]
    (hc : ∀ a : A, Commute e a) (he : IsIdempotentElem e) :
    (centralFixedSubmodule M hc).restrictScalars k = e • (⊤ : Submodule k M) := by
  ext x
  exact he.mem_smul_top_iff_smul_eq_self.symm

/-- When `e` fixes `S` pointwise, every `A`-linear map out of `S` lands in `centralFixedSubmodule`.
-/
theorem apply_mem_centralFixedSubmodule {S M : Type*}
    [AddCommMonoid S] [Module A S] [AddCommMonoid M] [Module A M]
    (hc : ∀ a : A, Commute e a) (heS : ∀ s : S, e • s = s) (f : S →ₗ[A] M) (s : S) :
    f s ∈ centralFixedSubmodule M hc := by
  rw [mem_centralFixedSubmodule, ← f.map_smul, heS]

/-- Postcomposition with `subtype` identifies `S →ₗ[A] centralFixedSubmodule M hc` with
`S →ₗ[A] M` whenever `e` fixes `S` pointwise. -/
def centralFixedSubmoduleLinearMapEquiv (k : Type*) {S M : Type*} [Semiring k] [SMul k A]
    [AddCommMonoid S] [Module A S]
    [AddCommMonoid M] [Module k M] [Module A M] [IsScalarTower k A M] [SMulCommClass A k M]
    (hc : ∀ a : A, Commute e a) (heS : ∀ s : S, e • s = s) :
    (S →ₗ[A] centralFixedSubmodule M hc) ≃ₗ[k] (S →ₗ[A] M) :=
  (centralFixedSubmodule M hc).linearMapSubtypeEquiv k (apply_mem_centralFixedSubmodule hc heS)

/-- Applying `centralFixedSubmoduleLinearMapEquiv` postcomposes with the submodule inclusion. -/
@[simp]
theorem centralFixedSubmoduleLinearMapEquiv_apply (k : Type*) {S M : Type*}
    [Semiring k] [SMul k A] [AddCommMonoid S] [Module A S]
    [AddCommMonoid M] [Module k M] [Module A M] [IsScalarTower k A M] [SMulCommClass A k M]
    (hc : ∀ a : A, Commute e a) (heS : ∀ s : S, e • s = s)
    (g : S →ₗ[A] centralFixedSubmodule M hc) :
    centralFixedSubmoduleLinearMapEquiv k hc heS g =
      (centralFixedSubmodule M hc).subtype.comp g :=
  (rfl)

/-- Applying the inverse of `centralFixedSubmoduleLinearMapEquiv` restricts the codomain to
`centralFixedSubmodule M hc`. -/
@[simp]
theorem coe_centralFixedSubmoduleLinearMapEquiv_symm_apply (k : Type*) {S M : Type*}
    [Semiring k] [SMul k A] [AddCommMonoid S] [Module A S]
    [AddCommMonoid M] [Module k M] [Module A M] [IsScalarTower k A M] [SMulCommClass A k M]
    (hc : ∀ a : A, Commute e a) (heS : ∀ s : S, e • s = s)
    (f : S →ₗ[A] M) (s : S) :
    ((centralFixedSubmoduleLinearMapEquiv k hc heS).symm f s : M) = f s :=
  (rfl)

end CentralFixedSubmodule

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
      (isotypicEval_isotypicEvalCentralInv hc hsurj hker s _ _ hs x).trans hx⟩

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
    (x : M) = e • (x : M) := x.2.symm
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
        ⟨g x, by rw [mem_centralFixedSubmodule, ← g.map_smul, x.2]⟩ =
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
  refine ⟨Function.LeftInverse.injective (g := inv) fun ⟨x, y⟩ ↦ ?_,
    Function.RightInverse.surjective (g := inv) fun m ↦ ?_⟩
  · have hx : prodIdempotentFst h • isotypicEval k x = isotypicEval k x := (e₁ x).2
    have hy : prodIdempotentSnd h • isotypicEval k y = isotypicEval k y := (e₂ y).2
    have hxy : prodIdempotentFst h • isotypicEval k y = 0 := by
      rw [← hy, ← mul_smul, prodIdempotent_mul_fst_snd h, zero_smul]
    have hyx : prodIdempotentSnd h • isotypicEval k x = 0 := by
      rw [← hx, ← mul_smul, prodIdempotent_mul_snd_fst h, zero_smul]
    refine Prod.ext (e₁.injective (Subtype.ext ?_)) (e₂.injective (Subtype.ext ?_))
    · rw [e₁.apply_symm_apply]
      simp only [LinearMap.coprod_apply, smul_add, hx, hxy, add_zero]
      rfl
    · rw [e₂.apply_symm_apply]
      simp only [LinearMap.coprod_apply, smul_add, hyx, hy, zero_add]
      rfl
  · have coe_e₁ (z) : isotypicEval k z = (e₁ z : M) := rfl
    have coe_e₂ (z) : isotypicEval k z = (e₂ z : M) := rfl
    simp only [inv, LinearMap.coprod_apply, coe_e₁, coe_e₂, e₁.apply_symm_apply,
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

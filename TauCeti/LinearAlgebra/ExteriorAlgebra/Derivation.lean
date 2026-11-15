/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
public import Mathlib.RingTheory.Derivation.Basic

/-!
# Twisted derivations of an exterior algebra

Given a commutative `k`-algebra `S`, an `S`-module `M`, and an `S`-algebra endomorphism
`σ : ExteriorAlgebra S M →ₐ[S] ExteriorAlgebra S M`, a `σ`-twisted derivation of
`ExteriorAlgebra S M` over `k` is a `k`-linear endomorphism `D` obeying the `σ`-Leibniz rule

`D (x * y) = D x * y + σ x * D y`.

Both ordinary (`σ = AlgHom.id S _`) and graded odd (`σ = CliffordAlgebra.involute`) derivations on
exterior algebras have this shape. Following Bourbaki (*Algebra*, Chapter III, §10), any compatible
pair consisting of a `k`-derivation `d₀ : Derivation k S (ExteriorAlgebra S M)` in degree zero and
a `k`-linear map `d₁ : M →ₗ[k] ExteriorAlgebra S M` in degree one extends uniquely to a `σ`-twisted
`k`-linear derivation `liftTwistedDerivation` of `ExteriorAlgebra S M`.

## Main definitions

* `TauCeti.ExteriorAlgebra.liftTwistedDerivation`: extends a compatible pair `(d₀, d₁)` to a
  `σ`-twisted `k`-linear derivation of `ExteriorAlgebra S M`.

## Main results

* `TauCeti.ExteriorAlgebra.liftTwistedDerivation_algebraMap`,
  `TauCeti.ExteriorAlgebra.liftTwistedDerivation_ι`: action on scalars from `S` and generators from
  `M`.
* `TauCeti.ExteriorAlgebra.liftTwistedDerivation_mul`,
  `TauCeti.ExteriorAlgebra.liftTwistedDerivation_smul`: the `σ`-Leibniz and `S`-scalar Leibniz
  rules.
* `TauCeti.ExteriorAlgebra.liftTwistedDerivation_unique`: uniqueness of a `σ`-twisted derivation
  from its values on `S` and `M`.

## Implementation notes

Rather than reusing `TrivSqZeroExt`, whose global untwisted `Algebra S` instance (`s ↦ (s, 0)`)
would create an `SMul S` diamond against the derivation-twisted `S`-algebra map `s ↦ (s, d₀ s)`,
we construct a private `σ`-twisted square-zero `S`-algebra `TwistedDual σ d₀ hd₀` on pairs
`(fst, snd)` with multiplication `(a, a') * (b, b') = (a * b, a' * b + σ a * b')`. Applying
`ExteriorAlgebra.lift` to `m ↦ (ι m, d₁ m)` produces an `S`-algebra homomorphism whose first
projection is the identity and whose second projection is `liftTwistedDerivation`.

## References

* N. Bourbaki, *Algebra*, Chapter III, §10.
-/

public section

namespace TauCeti.ExteriorAlgebra

variable {k S M : Type*} [CommSemiring k] [CommRing S] [Algebra k S]
  [AddCommGroup M] [Module k M] [Module S M] [IsScalarTower k S M]

/-- Private `σ`-twisted square-zero `S`-algebra on `ExteriorAlgebra S M × ExteriorAlgebra S M` with
multiplication `(a, a') * (b, b') = (a * b, a' * b + σ a * b')`. -/
@[ext]
private structure TwistedDual (σ : ExteriorAlgebra S M →ₐ[S] ExteriorAlgebra S M)
    (_d₀ : Derivation k S (ExteriorAlgebra S M))
    (_hd₀ : ∀ (s : S) (x : ExteriorAlgebra S M), _d₀ s * x = σ x * _d₀ s) where
  fst : ExteriorAlgebra S M
  snd : ExteriorAlgebra S M

section TwistedDualInstances

variable {σ : ExteriorAlgebra S M →ₐ[S] ExteriorAlgebra S M}
  {d₀ : Derivation k S (ExteriorAlgebra S M)}
  {hd₀ : ∀ (s : S) (x : ExteriorAlgebra S M), d₀ s * x = σ x * d₀ s}

private noncomputable instance : Zero (TwistedDual σ d₀ hd₀) := ⟨⟨0, 0⟩⟩
private noncomputable instance : One (TwistedDual σ d₀ hd₀) := ⟨⟨1, 0⟩⟩
private noncomputable instance : Add (TwistedDual σ d₀ hd₀) :=
  ⟨fun x y ↦ ⟨x.fst + y.fst, x.snd + y.snd⟩⟩
private noncomputable instance : Neg (TwistedDual σ d₀ hd₀) := ⟨fun x ↦ ⟨-x.fst, -x.snd⟩⟩
private noncomputable instance : Sub (TwistedDual σ d₀ hd₀) :=
  ⟨fun x y ↦ ⟨x.fst - y.fst, x.snd - y.snd⟩⟩
private noncomputable instance : SMul ℕ (TwistedDual σ d₀ hd₀) :=
  ⟨fun n x ↦ ⟨n • x.fst, n • x.snd⟩⟩
private noncomputable instance : SMul ℤ (TwistedDual σ d₀ hd₀) :=
  ⟨fun z x ↦ ⟨z • x.fst, z • x.snd⟩⟩
private noncomputable instance : Mul (TwistedDual σ d₀ hd₀) :=
  ⟨fun x y ↦ ⟨x.fst * y.fst, x.snd * y.fst + σ x.fst * y.snd⟩⟩

@[simp]
private theorem TwistedDual.zero_fst : (0 : TwistedDual σ d₀ hd₀).fst = 0 := rfl

@[simp]
private theorem TwistedDual.zero_snd : (0 : TwistedDual σ d₀ hd₀).snd = 0 := rfl

@[simp]
private theorem TwistedDual.one_fst : (1 : TwistedDual σ d₀ hd₀).fst = 1 := rfl

@[simp]
private theorem TwistedDual.one_snd : (1 : TwistedDual σ d₀ hd₀).snd = 0 := rfl

@[simp]
private theorem TwistedDual.add_fst (x y : TwistedDual σ d₀ hd₀) :
    (x + y).fst = x.fst + y.fst := rfl

@[simp]
private theorem TwistedDual.add_snd (x y : TwistedDual σ d₀ hd₀) :
    (x + y).snd = x.snd + y.snd := rfl

@[simp]
private theorem TwistedDual.neg_fst (x : TwistedDual σ d₀ hd₀) : (-x).fst = -x.fst := rfl

@[simp]
private theorem TwistedDual.neg_snd (x : TwistedDual σ d₀ hd₀) : (-x).snd = -x.snd := rfl

@[simp]
private theorem TwistedDual.sub_fst (x y : TwistedDual σ d₀ hd₀) :
    (x - y).fst = x.fst - y.fst := rfl

@[simp]
private theorem TwistedDual.sub_snd (x y : TwistedDual σ d₀ hd₀) :
    (x - y).snd = x.snd - y.snd := rfl

@[simp]
private theorem TwistedDual.nsmul_fst (n : ℕ) (x : TwistedDual σ d₀ hd₀) :
    (n • x).fst = n • x.fst := rfl

@[simp]
private theorem TwistedDual.nsmul_snd (n : ℕ) (x : TwistedDual σ d₀ hd₀) :
    (n • x).snd = n • x.snd := rfl

@[simp]
private theorem TwistedDual.zsmul_fst (z : ℤ) (x : TwistedDual σ d₀ hd₀) :
    (z • x).fst = z • x.fst := rfl

@[simp]
private theorem TwistedDual.zsmul_snd (z : ℤ) (x : TwistedDual σ d₀ hd₀) :
    (z • x).snd = z • x.snd := rfl

@[simp]
private theorem TwistedDual.mul_fst (x y : TwistedDual σ d₀ hd₀) :
    (x * y).fst = x.fst * y.fst := rfl

@[simp]
private theorem TwistedDual.mul_snd (x y : TwistedDual σ d₀ hd₀) :
    (x * y).snd = x.snd * y.fst + σ x.fst * y.snd := rfl

private noncomputable instance : Ring (TwistedDual σ d₀ hd₀) where
  add_assoc x y z := by ext <;> exact add_assoc _ _ _
  zero_add x := by ext <;> exact zero_add _
  add_zero x := by ext <;> exact add_zero _
  nsmul n x := n • x
  nsmul_zero x := by ext <;> exact zero_smul ℕ _
  nsmul_succ n x := by ext <;> exact succ_nsmul _ n
  zsmul z x := z • x
  zsmul_zero' x := by ext <;> exact zero_smul ℤ _
  zsmul_succ' n x := by ext <;> exact SubNegMonoid.zsmul_succ' n _
  zsmul_neg' n x := by ext <;> exact SubNegMonoid.zsmul_neg' n _
  neg_add_cancel x := by ext <;> exact neg_add_cancel _
  add_comm x y := by ext <;> exact add_comm _ _
  sub_eq_add_neg x y := by ext <;> exact sub_eq_add_neg _ _
  left_distrib x y z := by
    ext <;> simp only [TwistedDual.mul_fst, TwistedDual.mul_snd, TwistedDual.add_fst,
      TwistedDual.add_snd, mul_add]
    abel
  right_distrib x y z := by
    ext <;> simp only [TwistedDual.mul_fst, TwistedDual.mul_snd, TwistedDual.add_fst,
      TwistedDual.add_snd, map_add, add_mul]
    abel
  zero_mul x := by ext <;> simp
  mul_zero x := by ext <;> simp
  mul_assoc x y z := by
    ext <;> simp only [TwistedDual.mul_fst, TwistedDual.mul_snd, map_mul, add_mul, mul_add,
      mul_assoc]
    abel
  one_mul x := by ext <;> simp
  mul_one x := by ext <;> simp

private noncomputable def twistedDualRingHom : S →+* TwistedDual σ d₀ hd₀ where
  toFun s := ⟨algebraMap S _ s, d₀ s⟩
  map_one' := by ext <;> simp
  map_mul' s t := by
    ext
    · exact map_mul _ s t
    · simp only [TwistedDual.mul_snd, d₀.leibniz, AlgHom.commutes]
      rw [← Algebra.commutes t (d₀ s), ← Algebra.smul_def, ← Algebra.smul_def, add_comm]
  map_zero' := by ext <;> simp
  map_add' s t := by ext <;> simp

private noncomputable instance : Algebra S (TwistedDual σ d₀ hd₀) :=
  (twistedDualRingHom (σ := σ) (d₀ := d₀) (hd₀ := hd₀)).toAlgebra' fun s z ↦ by
    ext
    · exact Algebra.commutes s z.fst
    · simp only [TwistedDual.mul_snd, twistedDualRingHom, RingHom.coe_mk, MonoidHom.coe_mk,
        OneHom.coe_mk]
      rw [hd₀ s z.fst, AlgHom.commutes, Algebra.commutes s z.snd, add_comm]

@[simp]
private theorem TwistedDual.algebraMap_fst (s : S) :
    (algebraMap S (TwistedDual σ d₀ hd₀) s).fst = algebraMap S (ExteriorAlgebra S M) s := rfl

@[simp]
private theorem TwistedDual.algebraMap_snd (s : S) :
    (algebraMap S (TwistedDual σ d₀ hd₀) s).snd = d₀ s := rfl

@[simp]
private theorem TwistedDual.smul_fst (s : S) (z : TwistedDual σ d₀ hd₀) :
    (s • z).fst = algebraMap S (ExteriorAlgebra S M) s * z.fst := rfl

@[simp]
private theorem TwistedDual.smul_snd (s : S) (z : TwistedDual σ d₀ hd₀) :
    (s • z).snd = d₀ s * z.fst + σ (algebraMap S (ExteriorAlgebra S M) s) * z.snd := rfl

private noncomputable def twistedDualGenerator (d₁ : M →ₗ[k] ExteriorAlgebra S M)
    (hsmul : ∀ (s : S) (m : M), d₁ (s • m) = d₀ s * ExteriorAlgebra.ι S m + s • d₁ m) :
    M →ₗ[S] TwistedDual σ d₀ hd₀ where
  toFun m := ⟨ExteriorAlgebra.ι S m, d₁ m⟩
  map_add' m₁ m₂ := by ext <;> exact map_add _ m₁ m₂
  map_smul' s m := by
    ext
    · simp [Algebra.smul_def]
    · simp [hsmul, AlgHom.commutes, Algebra.smul_def]

@[simp]
private theorem twistedDualGenerator_fst (d₁ : M →ₗ[k] ExteriorAlgebra S M)
    (hsmul : ∀ (s : S) (m : M), d₁ (s • m) = d₀ s * ExteriorAlgebra.ι S m + s • d₁ m) (m : M) :
    (twistedDualGenerator (σ := σ) (d₀ := d₀) (hd₀ := hd₀) d₁ hsmul m).fst =
      ExteriorAlgebra.ι S m := rfl

@[simp]
private theorem twistedDualGenerator_snd (d₁ : M →ₗ[k] ExteriorAlgebra S M)
    (hsmul : ∀ (s : S) (m : M), d₁ (s • m) = d₀ s * ExteriorAlgebra.ι S m + s • d₁ m) (m : M) :
    (twistedDualGenerator (σ := σ) (d₀ := d₀) (hd₀ := hd₀) d₁ hsmul m).snd = d₁ m := rfl

private noncomputable def twistedDualLift (d₁ : M →ₗ[k] ExteriorAlgebra S M)
    (hsmul : ∀ (s : S) (m : M), d₁ (s • m) = d₀ s * ExteriorAlgebra.ι S m + s • d₁ m)
    (hsq : ∀ m : M, d₁ m * ExteriorAlgebra.ι S m + σ (ExteriorAlgebra.ι S m) * d₁ m = 0) :
    ExteriorAlgebra S M →ₐ[S] TwistedDual σ d₀ hd₀ :=
  ExteriorAlgebra.lift S ⟨twistedDualGenerator (σ := σ) (d₀ := d₀) (hd₀ := hd₀) d₁ hsmul, fun m ↦ by
    ext
    · exact ExteriorAlgebra.ι_sq_zero m
    · simp only [TwistedDual.mul_snd, TwistedDual.zero_snd, twistedDualGenerator_fst,
        twistedDualGenerator_snd]
      exact hsq m⟩

private noncomputable def twistedDualFstAlgHom :
    TwistedDual σ d₀ hd₀ →ₐ[S] ExteriorAlgebra S M where
  toFun z := z.fst
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

@[simp]
private theorem twistedDualFstAlgHom_apply (z : TwistedDual σ d₀ hd₀) :
    twistedDualFstAlgHom z = z.fst := rfl

private theorem twistedDualLift_fst (d₁ : M →ₗ[k] ExteriorAlgebra S M)
    (hsmul : ∀ (s : S) (m : M), d₁ (s • m) = d₀ s * ExteriorAlgebra.ι S m + s • d₁ m)
    (hsq : ∀ m : M, d₁ m * ExteriorAlgebra.ι S m + σ (ExteriorAlgebra.ι S m) * d₁ m = 0)
    (x : ExteriorAlgebra S M) :
    (twistedDualLift (σ := σ) (d₀ := d₀) (hd₀ := hd₀) d₁ hsmul hsq x).fst = x := by
  have h : (twistedDualFstAlgHom (σ := σ) (d₀ := d₀) (hd₀ := hd₀)).comp
      (twistedDualLift (σ := σ) (d₀ := d₀) (hd₀ := hd₀) d₁ hsmul hsq) = AlgHom.id S _ :=
    ExteriorAlgebra.hom_ext <| LinearMap.ext fun m ↦ by simp [twistedDualLift]
  simpa using AlgHom.congr_fun h x

end TwistedDualInstances

/-- **Extension of a compatible `(d₀, d₁)` pair to a `σ`-twisted derivation of
`ExteriorAlgebra S M`**: given an `S`-algebra endomorphism `σ` of `ExteriorAlgebra S M`, a
`k`-derivation `d₀ : Derivation k S (ExteriorAlgebra S M)` satisfying `d₀ s * x = σ x * d₀ s`, and a
`k`-linear map `d₁ : M →ₗ[k] ExteriorAlgebra S M` satisfying
`d₁ (s • m) = d₀ s * ι m + s • d₁ m` and `d₁ m * ι m + σ (ι m) * d₁ m = 0`,
`liftTwistedDerivation` is the `k`-linear endomorphism of `ExteriorAlgebra S M` extending `d₀` on
`S` and `d₁` on `M` and obeying `D (x * y) = D x * y + σ x * D y`. -/
noncomputable def liftTwistedDerivation (σ : ExteriorAlgebra S M →ₐ[S] ExteriorAlgebra S M)
    (d₀ : Derivation k S (ExteriorAlgebra S M))
    (hd₀ : ∀ (s : S) (x : ExteriorAlgebra S M), d₀ s * x = σ x * d₀ s)
    (d₁ : M →ₗ[k] ExteriorAlgebra S M)
    (hsmul : ∀ (s : S) (m : M), d₁ (s • m) = d₀ s * ExteriorAlgebra.ι S m + s • d₁ m)
    (hsq : ∀ m : M, d₁ m * ExteriorAlgebra.ι S m + σ (ExteriorAlgebra.ι S m) * d₁ m = 0) :
    ExteriorAlgebra S M →ₗ[k] ExteriorAlgebra S M where
  toFun x := (twistedDualLift (σ := σ) (d₀ := d₀) (hd₀ := hd₀) d₁ hsmul hsq x).snd
  map_add' x y :=
    congrArg TwistedDual.snd
      (map_add (twistedDualLift (σ := σ) (d₀ := d₀) (hd₀ := hd₀) d₁ hsmul hsq) x y)
  map_smul' c x := by
    rw [← IsScalarTower.algebraMap_smul S c x, AlgHom.map_smul_of_tower,
      TwistedDual.smul_snd, Derivation.map_algebraMap, zero_mul, zero_add,
      AlgHom.commutes, ← Algebra.smul_def, IsScalarTower.algebraMap_smul, RingHom.id_apply]

private theorem liftTwistedDerivation_apply (σ : ExteriorAlgebra S M →ₐ[S] ExteriorAlgebra S M)
    (d₀ : Derivation k S (ExteriorAlgebra S M))
    (hd₀ : ∀ (s : S) (x : ExteriorAlgebra S M), d₀ s * x = σ x * d₀ s)
    (d₁ : M →ₗ[k] ExteriorAlgebra S M)
    (hsmul : ∀ (s : S) (m : M), d₁ (s • m) = d₀ s * ExteriorAlgebra.ι S m + s • d₁ m)
    (hsq : ∀ m : M, d₁ m * ExteriorAlgebra.ι S m + σ (ExteriorAlgebra.ι S m) * d₁ m = 0)
    (x : ExteriorAlgebra S M) :
    liftTwistedDerivation σ d₀ hd₀ d₁ hsmul hsq x =
      (twistedDualLift (σ := σ) (d₀ := d₀) (hd₀ := hd₀) d₁ hsmul hsq x).snd := rfl

/-- On scalars `algebraMap S _ s`, `liftTwistedDerivation` acts by `d₀`. -/
@[simp]
theorem liftTwistedDerivation_algebraMap (σ : ExteriorAlgebra S M →ₐ[S] ExteriorAlgebra S M)
    (d₀ : Derivation k S (ExteriorAlgebra S M))
    (hd₀ : ∀ (s : S) (x : ExteriorAlgebra S M), d₀ s * x = σ x * d₀ s)
    (d₁ : M →ₗ[k] ExteriorAlgebra S M)
    (hsmul : ∀ (s : S) (m : M), d₁ (s • m) = d₀ s * ExteriorAlgebra.ι S m + s • d₁ m)
    (hsq : ∀ m : M, d₁ m * ExteriorAlgebra.ι S m + σ (ExteriorAlgebra.ι S m) * d₁ m = 0)
    (s : S) :
    liftTwistedDerivation σ d₀ hd₀ d₁ hsmul hsq (algebraMap S (ExteriorAlgebra S M) s) = d₀ s := by
  rw [liftTwistedDerivation_apply, AlgHom.commutes, TwistedDual.algebraMap_snd]

/-- `liftTwistedDerivation` annihilates `1`. -/
@[simp]
theorem liftTwistedDerivation_one (σ : ExteriorAlgebra S M →ₐ[S] ExteriorAlgebra S M)
    (d₀ : Derivation k S (ExteriorAlgebra S M))
    (hd₀ : ∀ (s : S) (x : ExteriorAlgebra S M), d₀ s * x = σ x * d₀ s)
    (d₁ : M →ₗ[k] ExteriorAlgebra S M)
    (hsmul : ∀ (s : S) (m : M), d₁ (s • m) = d₀ s * ExteriorAlgebra.ι S m + s • d₁ m)
    (hsq : ∀ m : M, d₁ m * ExteriorAlgebra.ι S m + σ (ExteriorAlgebra.ι S m) * d₁ m = 0) :
    liftTwistedDerivation σ d₀ hd₀ d₁ hsmul hsq 1 = 0 := by
  rw [← map_one (algebraMap S (ExteriorAlgebra S M)), liftTwistedDerivation_algebraMap,
    Derivation.map_one_eq_zero]

/-- On degree-one generators `ι S m`, `liftTwistedDerivation` acts by `d₁`. -/
@[simp]
theorem liftTwistedDerivation_ι (σ : ExteriorAlgebra S M →ₐ[S] ExteriorAlgebra S M)
    (d₀ : Derivation k S (ExteriorAlgebra S M))
    (hd₀ : ∀ (s : S) (x : ExteriorAlgebra S M), d₀ s * x = σ x * d₀ s)
    (d₁ : M →ₗ[k] ExteriorAlgebra S M)
    (hsmul : ∀ (s : S) (m : M), d₁ (s • m) = d₀ s * ExteriorAlgebra.ι S m + s • d₁ m)
    (hsq : ∀ m : M, d₁ m * ExteriorAlgebra.ι S m + σ (ExteriorAlgebra.ι S m) * d₁ m = 0)
    (m : M) :
    liftTwistedDerivation σ d₀ hd₀ d₁ hsmul hsq (ExteriorAlgebra.ι S m) = d₁ m := by
  rw [liftTwistedDerivation_apply, twistedDualLift, ExteriorAlgebra.lift_ι_apply,
    twistedDualGenerator_snd]

/-- **The `σ`-twisted Leibniz rule** for `liftTwistedDerivation`. -/
theorem liftTwistedDerivation_mul (σ : ExteriorAlgebra S M →ₐ[S] ExteriorAlgebra S M)
    (d₀ : Derivation k S (ExteriorAlgebra S M))
    (hd₀ : ∀ (s : S) (x : ExteriorAlgebra S M), d₀ s * x = σ x * d₀ s)
    (d₁ : M →ₗ[k] ExteriorAlgebra S M)
    (hsmul : ∀ (s : S) (m : M), d₁ (s • m) = d₀ s * ExteriorAlgebra.ι S m + s • d₁ m)
    (hsq : ∀ m : M, d₁ m * ExteriorAlgebra.ι S m + σ (ExteriorAlgebra.ι S m) * d₁ m = 0)
    (x y : ExteriorAlgebra S M) :
    liftTwistedDerivation σ d₀ hd₀ d₁ hsmul hsq (x * y) =
      liftTwistedDerivation σ d₀ hd₀ d₁ hsmul hsq x * y +
        σ x * liftTwistedDerivation σ d₀ hd₀ d₁ hsmul hsq y := by
  rw [liftTwistedDerivation_apply, map_mul, TwistedDual.mul_snd,
    twistedDualLift_fst, twistedDualLift_fst, ← liftTwistedDerivation_apply,
    ← liftTwistedDerivation_apply]

/-- Scalar multiplication by `s : S` obeys `D (s • x) = d₀ s * x + s • D x`. -/
@[simp]
theorem liftTwistedDerivation_smul (σ : ExteriorAlgebra S M →ₐ[S] ExteriorAlgebra S M)
    (d₀ : Derivation k S (ExteriorAlgebra S M))
    (hd₀ : ∀ (s : S) (x : ExteriorAlgebra S M), d₀ s * x = σ x * d₀ s)
    (d₁ : M →ₗ[k] ExteriorAlgebra S M)
    (hsmul : ∀ (s : S) (m : M), d₁ (s • m) = d₀ s * ExteriorAlgebra.ι S m + s • d₁ m)
    (hsq : ∀ m : M, d₁ m * ExteriorAlgebra.ι S m + σ (ExteriorAlgebra.ι S m) * d₁ m = 0)
    (s : S) (x : ExteriorAlgebra S M) :
    liftTwistedDerivation σ d₀ hd₀ d₁ hsmul hsq (s • x) =
      d₀ s * x + s • liftTwistedDerivation σ d₀ hd₀ d₁ hsmul hsq x := by
  rw [Algebra.smul_def, liftTwistedDerivation_mul, liftTwistedDerivation_algebraMap,
    AlgHom.commutes, ← Algebra.smul_def]

/-- **Uniqueness of `liftTwistedDerivation`**: any `k`-linear map on `ExteriorAlgebra S M` that
extends `d₀` on `S`, extends `d₁` on `M`, and satisfies the `σ`-Leibniz rule equals
`liftTwistedDerivation`. -/
theorem liftTwistedDerivation_unique (σ : ExteriorAlgebra S M →ₐ[S] ExteriorAlgebra S M)
    (d₀ : Derivation k S (ExteriorAlgebra S M))
    (hd₀ : ∀ (s : S) (x : ExteriorAlgebra S M), d₀ s * x = σ x * d₀ s)
    (d₁ : M →ₗ[k] ExteriorAlgebra S M)
    (hsmul : ∀ (s : S) (m : M), d₁ (s • m) = d₀ s * ExteriorAlgebra.ι S m + s • d₁ m)
    (hsq : ∀ m : M, d₁ m * ExteriorAlgebra.ι S m + σ (ExteriorAlgebra.ι S m) * d₁ m = 0)
    {D : ExteriorAlgebra S M →ₗ[k] ExteriorAlgebra S M}
    (halg : ∀ s : S, D (algebraMap S (ExteriorAlgebra S M) s) = d₀ s)
    (hι : ∀ m : M, D (ExteriorAlgebra.ι S m) = d₁ m)
    (hmul : ∀ x y : ExteriorAlgebra S M, D (x * y) = D x * y + σ x * D y) :
    D = liftTwistedDerivation σ d₀ hd₀ d₁ hsmul hsq := by
  ext x
  induction x using CliffordAlgebra.induction with
  | algebraMap s => rw [halg, liftTwistedDerivation_algebraMap]
  | ι m => rw [hι, liftTwistedDerivation_ι]
  | mul x y ihx ihy => rw [hmul, liftTwistedDerivation_mul, ihx, ihy]
  | add x y ihx ihy => rw [map_add, map_add, ihx, ihy]

end TauCeti.ExteriorAlgebra

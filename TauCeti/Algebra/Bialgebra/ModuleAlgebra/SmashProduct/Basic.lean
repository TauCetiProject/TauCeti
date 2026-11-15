/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Bialgebra.ModuleAlgebra.Basic
public import Mathlib.RingTheory.Coalgebra.GroupLike
public import Mathlib.RingTheory.Bialgebra.Primitive
public import Mathlib.RingTheory.Finiteness.Bilinear
public import Mathlib.LinearAlgebra.TensorProduct.Projective
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# The smash product of a left module algebra

Given a bialgebra `H` over a commutative semiring `R` and a left `H`-module algebra `A`
(`TauCeti.LeftModuleAlgebra R H A`), the **smash product** `SmashProduct μ` (traditionally written
`A # H`) is the `R`-module `A ⊗[R] H` equipped with the twisted multiplication

`(a # h) * (b # l) = ∑ (a * (h₁ · b)) # (h₂ * l)`

and unit `1 # 1`. Associativity expresses the compatibility between multiplication in `H`,
coassociativity of `H`, and the module-algebra product law on `A`; unitality uses the counit laws
and `h · 1 = ε(h) • 1`. Neither an antipode nor finite generation is required.

This file constructs `SmashProduct μ` as a one-field wrapper around `A ⊗[R] H` so that its
multiplication does not conflict with the untwisted tensor-product algebra structure on `A ⊗[R] H`,
establishes its `Semiring`, `Ring`, and `Algebra R` instances, constructs the canonical algebra
homomorphisms `includeLeft : A →ₐ[R] SmashProduct μ` (`a ↦ a # 1`) and
`includeRight : H →ₐ[R] SmashProduct μ` (`h ↦ 1 # h`), proves the universal property classifying
`R`-algebra homomorphisms out of `SmashProduct μ` by covariant pairs (`SmashCompatible`), and
characterizes injectivity of the two factor maps together with commutation on group-like,
skew-primitive, and primitive elements.

## Main definitions

* `TauCeti.LeftModuleAlgebra.smashMulPure`: the smash-product formula on pure tensors in `A ⊗[R] H`.
* `TauCeti.LeftModuleAlgebra.smashMul`: the bilinear smash multiplication on `A ⊗[R] H`.
* `TauCeti.SmashProduct`: the smash-product `R`-algebra `A # H` of a left module algebra `μ`.
* `TauCeti.SmashProduct.addEquiv`, `TauCeti.SmashProduct.linearEquiv`: the underlying additive and
  `R`-linear equivalences between `SmashProduct μ` and `A ⊗[R] H`.
* `TauCeti.SmashProduct.tmul`: the pure smash tensor `a # h`.
* `TauCeti.SmashProduct.includeLeft`, `TauCeti.SmashProduct.includeRight`: the canonical `R`-algebra
  homomorphisms from `A` and `H` into `SmashProduct μ`.
* `TauCeti.LeftModuleAlgebra.SmashCompatible`: the covariance relation
  `fH h * fA a = ∑ fA (h₁ · a) * fH h₂` for a pair of `R`-algebra maps out of `A` and `H`.
* `TauCeti.SmashProduct.lift`, `TauCeti.SmashProduct.liftEquiv`: the universal property of the
  smash product.

## Main results

* `TauCeti.SmashProduct.tmul_mul_tmul_eq_sum`: pure-tensor multiplication in any `Coalgebra.Repr`.
* `TauCeti.SmashProduct.lift_unique`: unique factorization of covariant algebra-map pairs.
* `TauCeti.SmashProduct.includeLeft_injective`: `a ↦ a # 1` is unconditionally injective, split
  `R`-linearly by `id_A ⊗ ε`.
* `TauCeti.SmashProduct.includeRight_injective_iff`: over a semifield on a projective algebra (in
  particular over any field), `h ↦ 1 # h` is injective if and only if `A` is nontrivial; for
  `Subsingleton A` the smash product is trivial.
* `TauCeti.SmashProduct.commute_includeRight_includeLeft_of_isGroupLikeElem`: a group-like element
  commutes with `a # 1` in `SmashProduct μ` if and only if it fixes `a`.

## References

* S. Montgomery, *Hopf Algebras and Their Actions on Rings*, CBMS Regional Conference Series in
  Mathematics 82, AMS, 1993, §4.1.
* Y. Qi, *Hopfological algebra*, Compos. Math. 150 (2014), 1–45, Example 2.8.
-/

public section

open scoped TensorProduct Coalgebra
open Coalgebra

namespace TauCeti

universe u v w

namespace LeftModuleAlgebra

section Semiring

variable {R : Type u} {H : Type v} {A : Type w}
variable [CommSemiring R] [Semiring H] [Bialgebra R H] [Semiring A] [Algebra R A]

/-- The smash-product formula `(a, h, b, l) ↦ ∑ (a * (h₁ · b)) ⊗ₜ (h₂ * l)` on pure tensors,
expressed directly from `Coalgebra.comul` without choosing a coproduct representation. -/
def smashMulPure (μ : LeftModuleAlgebra R H A) (a : A) (h : H) (b : A) (l : H) : A ⊗[R] H :=
  TensorProduct.map (LinearMap.mulLeft R a ∘ₗ μ.action.toLinearMap.flip b)
    (LinearMap.mulRight R l) (comul (R := R) h)

/-- The pure-tensor smash product in any finite representation of the coproduct. -/
theorem smashMulPure_eq_sum (μ : LeftModuleAlgebra R H A) (a : A) {h : H} {ι : Type*}
    (r : Coalgebra.Repr R h ι) (b : A) (l : H) :
    μ.smashMulPure a h b l =
      ∑ i ∈ r.index, (a * μ.action (r.left i) b) ⊗ₜ[R] (r.right i * l) := by
  simp [smashMulPure, ← r.eq, map_sum]

private def smashMulRightAux (μ : LeftModuleAlgebra R H A) (a : A) (h : H) :
    A ⊗[R] H →ₗ[R] A ⊗[R] H :=
  TensorProduct.lift <| LinearMap.mk₂ R (fun b l => μ.smashMulPure a h b l)
    (fun b₁ b₂ l => by
      have hleft :
          LinearMap.mulLeft R a ∘ₗ μ.action.toLinearMap.flip (b₁ + b₂) =
            (LinearMap.mulLeft R a ∘ₗ μ.action.toLinearMap.flip b₁) +
              (LinearMap.mulLeft R a ∘ₗ μ.action.toLinearMap.flip b₂) := by
        ext k
        simp [mul_add]
      rw [smashMulPure, smashMulPure, smashMulPure, hleft, TensorProduct.map_add_left,
        LinearMap.add_apply])
    (fun r b l => by
      have hleft :
          LinearMap.mulLeft R a ∘ₗ μ.action.toLinearMap.flip (r • b) =
            r • (LinearMap.mulLeft R a ∘ₗ μ.action.toLinearMap.flip b) := by
        ext k
        simp
      rw [smashMulPure, smashMulPure, hleft, TensorProduct.map_smul_left, LinearMap.smul_apply])
    (fun b l₁ l₂ => by
      have hright :
          LinearMap.mulRight R (l₁ + l₂) =
            LinearMap.mulRight R l₁ + LinearMap.mulRight R l₂ := by
        ext k
        simp [mul_add]
      rw [smashMulPure, smashMulPure, smashMulPure, hright, TensorProduct.map_add_right,
        LinearMap.add_apply])
    (fun r b l => by
      have hright :
          LinearMap.mulRight R (r • l) = r • LinearMap.mulRight R l := by
        ext k
        simp [Algebra.mul_smul_comm]
      rw [smashMulPure, smashMulPure, hright, TensorProduct.map_smul_right, LinearMap.smul_apply])

private theorem smashMulRightAux_tmul (μ : LeftModuleAlgebra R H A) (a b : A) (h l : H) :
    smashMulRightAux μ a h (b ⊗ₜ[R] l) = μ.smashMulPure a h b l :=
  rfl

/-- The `R`-bilinear smash multiplication on `A ⊗[R] H` extending `smashMulPure`. -/
def smashMul (μ : LeftModuleAlgebra R H A) :
    (A ⊗[R] H) →ₗ[R] (A ⊗[R] H) →ₗ[R] (A ⊗[R] H) :=
  TensorProduct.lift <| LinearMap.mk₂ R (smashMulRightAux μ)
    (fun a₁ a₂ h => LinearMap.ext fun z =>
      TensorProduct.inductionOn z
        (fun b l => by
          have hleft :
              LinearMap.mulLeft R (a₁ + a₂) ∘ₗ μ.action.toLinearMap.flip b =
                (LinearMap.mulLeft R a₁ ∘ₗ μ.action.toLinearMap.flip b) +
                  (LinearMap.mulLeft R a₂ ∘ₗ μ.action.toLinearMap.flip b) := by
            ext k
            simp [add_mul]
          rw [LinearMap.add_apply, smashMulRightAux_tmul, smashMulRightAux_tmul,
            smashMulRightAux_tmul, smashMulPure, smashMulPure, smashMulPure, hleft,
            TensorProduct.map_add_left, LinearMap.add_apply])
        (fun x y hx hy => by simp [map_add, hx, hy, add_add_add_comm]))
    (fun r a h => LinearMap.ext fun z =>
      TensorProduct.inductionOn z
        (fun b l => by
          have hleft :
              LinearMap.mulLeft R (r • a) ∘ₗ μ.action.toLinearMap.flip b =
                r • (LinearMap.mulLeft R a ∘ₗ μ.action.toLinearMap.flip b) := by
            ext k
            simp [Algebra.smul_mul_assoc]
          rw [LinearMap.smul_apply, smashMulRightAux_tmul, smashMulRightAux_tmul, smashMulPure,
            smashMulPure, hleft, TensorProduct.map_smul_left, LinearMap.smul_apply])
        (fun x y hx hy => by simp [map_add, hx, hy]))
    (fun a h₁ h₂ => LinearMap.ext fun z =>
      TensorProduct.inductionOn z
        (fun b l => by simp [smashMulRightAux_tmul, smashMulPure, map_add])
        (fun x y hx hy => by simp [map_add, hx, hy, add_add_add_comm]))
    (fun r a h => LinearMap.ext fun z =>
      TensorProduct.inductionOn z
        (fun b l => by simp [smashMulRightAux_tmul, smashMulPure, map_smul])
        (fun x y hx hy => by simp [map_add, hx, hy]))

@[simp]
theorem smashMul_tmul (μ : LeftModuleAlgebra R H A) (a b : A) (h l : H) :
    μ.smashMul (a ⊗ₜ[R] h) (b ⊗ₜ[R] l) = μ.smashMulPure a h b l :=
  (rfl)

/-- The covariance relation `fH(h) * fA(a) = ∑ fA(h₁ · a) * fH(h₂)` characterizing pairs of
`R`-algebra homomorphisms out of `A` and `H` that assemble to an algebra map on `A # H`. -/
def SmashCompatible (μ : LeftModuleAlgebra R H A) {C : Type*} [Semiring C] [Algebra R C]
    (fA : A →ₐ[R] C) (fH : H →ₐ[R] C) : Prop :=
  ∀ h a, fH h * fA a =
    LinearMap.mul' R C
      (TensorProduct.map (fA.toLinearMap ∘ₗ μ.action.toLinearMap.flip a) fH.toLinearMap
        (comul (R := R) h))

/-- Unfolded characterization of `SmashCompatible`. -/
theorem smashCompatible_iff (μ : LeftModuleAlgebra R H A) {C : Type*} [Semiring C] [Algebra R C]
    (fA : A →ₐ[R] C) (fH : H →ₐ[R] C) :
    μ.SmashCompatible fA fH ↔
      ∀ h a, fH h * fA a =
        LinearMap.mul' R C
          (TensorProduct.map (fA.toLinearMap ∘ₗ μ.action.toLinearMap.flip a) fH.toLinearMap
            (comul (R := R) h)) :=
  Iff.rfl

/-- Evaluate `SmashCompatible` on an element `h : H` and `a : A`. -/
theorem SmashCompatible.apply {μ : LeftModuleAlgebra R H A} {C : Type*} [Semiring C] [Algebra R C]
    {fA : A →ₐ[R] C} {fH : H →ₐ[R] C} (hcompat : μ.SmashCompatible fA fH) (h : H) (a : A) :
    fH h * fA a =
      LinearMap.mul' R C
        (TensorProduct.map (fA.toLinearMap ∘ₗ μ.action.toLinearMap.flip a) fH.toLinearMap
          (comul (R := R) h)) :=
  hcompat h a

/-- The covariance equation expanded in any finite representation of the coproduct. -/
theorem SmashCompatible.mul_eq_sum {μ : LeftModuleAlgebra R H A} {C : Type*} [Semiring C]
    [Algebra R C] {fA : A →ₐ[R] C} {fH : H →ₐ[R] C} (hcompat : μ.SmashCompatible fA fH)
    {h : H} {ι : Type*} (r : Coalgebra.Repr R h ι) (a : A) :
    fH h * fA a = ∑ i ∈ r.index, fA (μ.action (r.left i) a) * fH (r.right i) := by
  simpa [← r.eq, map_sum] using hcompat h a

/-- Smash compatibility can be checked in any chosen family of coproduct representations. -/
theorem smashCompatible_iff_sum (μ : LeftModuleAlgebra R H A) {C : Type*} [Semiring C]
    [Algebra R C] (fA : A →ₐ[R] C) (fH : H →ₐ[R] C) {ι : Type*}
    (r : ∀ h : H, Coalgebra.Repr R h ι) :
    μ.SmashCompatible fA fH ↔
      ∀ h a, fH h * fA a =
        ∑ i ∈ (r h).index, fA (μ.action ((r h).left i) a) * fH ((r h).right i) := by
  refine ⟨fun hc h a => hc.mul_eq_sum (r h) a, fun hc h a => ?_⟩
  simpa [← (r h).eq, map_sum] using hc h a

end Semiring

end LeftModuleAlgebra

/-- The **smash product** `A # H` of a left `H`-module algebra `μ : LeftModuleAlgebra R H A`:
a wrapper around `A ⊗[R] H` carrying the twisted algebra multiplication
`(a # h) * (b # l) = ∑ (a * (h₁ · b)) # (h₂ * l)` and unit `1 # 1`. -/
@[ext]
structure SmashProduct {R : Type u} {H : Type v} {A : Type w}
    [CommSemiring R] [Semiring H] [Bialgebra R H] [Semiring A] [Algebra R A]
    (μ : LeftModuleAlgebra R H A) : Type (max w v) where
  /-- Wrap an element of `A ⊗[R] H` as an element of the smash product. -/
  ofTensor ::
  /-- The underlying element of `A ⊗[R] H`. -/
  toTensor : A ⊗[R] H

namespace SmashProduct

section Semiring

variable {R : Type u} {H : Type v} {A : Type w}
variable [CommSemiring R] [Semiring H] [Bialgebra R H] [Semiring A] [Algebra R A]
variable {μ : LeftModuleAlgebra R H A}

variable (μ) in
instance : AddCommMonoid (SmashProduct μ) :=
  Equiv.addCommMonoid ⟨toTensor, ofTensor, fun _ => rfl, fun _ => rfl⟩

variable (μ) in
/-- The underlying additive equivalence between `SmashProduct μ` and `A ⊗[R] H`, forgetting the
multiplication. -/
def addEquiv : SmashProduct μ ≃+ A ⊗[R] H where
  toFun := toTensor
  invFun := ofTensor
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

variable (μ) in
instance : Module R (SmashProduct μ) :=
  (addEquiv μ).module R

variable (μ) in
/-- The underlying `R`-linear equivalence between `SmashProduct μ` and `A ⊗[R] H`. -/
def linearEquiv : SmashProduct μ ≃ₗ[R] A ⊗[R] H :=
  (addEquiv μ).linearEquiv R

@[simp]
theorem toTensor_zero : (0 : SmashProduct μ).toTensor = 0 :=
  (rfl)

@[simp]
theorem toTensor_add (x y : SmashProduct μ) : (x + y).toTensor = x.toTensor + y.toTensor :=
  (rfl)

@[simp]
theorem toTensor_smul (r : R) (x : SmashProduct μ) : (r • x).toTensor = r • x.toTensor :=
  (rfl)

@[simp]
theorem toTensor_sum {ι : Type*} (s : Finset ι) (f : ι → SmashProduct μ) :
    (∑ i ∈ s, f i).toTensor = ∑ i ∈ s, (f i).toTensor :=
  map_sum (addEquiv μ) f s

@[simp]
theorem ofTensor_zero : (ofTensor 0 : SmashProduct μ) = 0 :=
  (rfl)

@[simp]
theorem ofTensor_add (x y : A ⊗[R] H) :
    (ofTensor (x + y) : SmashProduct μ) = ofTensor x + ofTensor y :=
  (rfl)

@[simp]
theorem ofTensor_smul (r : R) (x : A ⊗[R] H) :
    (ofTensor (r • x) : SmashProduct μ) = r • ofTensor x :=
  (rfl)

@[simp]
theorem addEquiv_apply (x : SmashProduct μ) : addEquiv μ x = x.toTensor :=
  (rfl)

@[simp]
theorem addEquiv_symm_apply (x : A ⊗[R] H) : (addEquiv μ).symm x = ofTensor x :=
  (rfl)

@[simp]
theorem linearEquiv_apply (x : SmashProduct μ) : linearEquiv μ x = x.toTensor :=
  (rfl)

@[simp]
theorem linearEquiv_symm_apply (x : A ⊗[R] H) : (linearEquiv μ).symm x = ofTensor x :=
  (rfl)

variable (μ) in
/-- The pure smash tensor `a # h` in `SmashProduct μ`, corresponding to `a ⊗ₜ[R] h`. -/
def tmul (a : A) (h : H) : SmashProduct μ :=
  ofTensor (a ⊗ₜ[R] h)

@[simp]
theorem toTensor_tmul (a : A) (h : H) : (tmul μ a h).toTensor = a ⊗ₜ[R] h :=
  (rfl)

@[simp]
theorem ofTensor_tmul (a : A) (h : H) : (ofTensor (a ⊗ₜ[R] h) : SmashProduct μ) = tmul μ a h :=
  (rfl)

@[simp]
theorem add_tmul (a₁ a₂ : A) (h : H) :
    tmul μ (a₁ + a₂) h = tmul μ a₁ h + tmul μ a₂ h := by
  ext
  exact TensorProduct.add_tmul a₁ a₂ h

@[simp]
theorem tmul_add (a : A) (h₁ h₂ : H) :
    tmul μ a (h₁ + h₂) = tmul μ a h₁ + tmul μ a h₂ := by
  ext
  exact TensorProduct.tmul_add a h₁ h₂

@[simp]
theorem smul_tmul (r : R) (a : A) (h : H) :
    tmul μ (r • a) h = r • tmul μ a h := by
  ext
  exact TensorProduct.smul_tmul' r a h

@[simp]
theorem tmul_smul (r : R) (a : A) (h : H) :
    tmul μ a (r • h) = r • tmul μ a h := by
  ext
  exact TensorProduct.tmul_smul r a h

@[simp]
theorem zero_tmul (h : H) : tmul μ 0 h = 0 := by
  ext
  simp

@[simp]
theorem tmul_zero (a : A) : tmul μ a 0 = 0 := by
  ext
  simp

/-- An induction principle for `SmashProduct μ`: a predicate containing all pure smash tensors
`tmul μ a h` and closed under addition holds everywhere. -/
@[elab_as_elim]
theorem inductionOn {motive : SmashProduct μ → Prop} (x : SmashProduct μ)
    (tmul : ∀ a h, motive (tmul μ a h))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive x := by
  rcases x with ⟨t⟩
  exact TensorProduct.inductionOn (motive := fun t => motive ⟨t⟩) t tmul
    fun s t hs ht => add ⟨s⟩ ⟨t⟩ hs ht

/-- Two `R`-linear maps out of `SmashProduct μ` are equal when they agree on pure smash tensors. -/
theorem lhom_ext {M : Type*} [AddCommMonoid M] [Module R M]
    {f g : SmashProduct μ →ₗ[R] M}
    (h : ∀ a x, f (tmul μ a x) = g (tmul μ a x)) : f = g := by
  ext z
  exact SmashProduct.inductionOn z h fun x y hx hy => by simp [hx, hy]

/-! ### Algebra structure on the smash product -/

private theorem one_smashMul (x : A ⊗[R] H) : μ.smashMul (1 ⊗ₜ[R] 1) x = x :=
  TensorProduct.inductionOn x
    (fun b l => by
      simp [LeftModuleAlgebra.smashMulPure, Bialgebra.comul_one, Algebra.TensorProduct.one_def])
    (fun s t hs ht => by simp [map_add, hs, ht])

private theorem smashMul_one (x : A ⊗[R] H) : μ.smashMul x (1 ⊗ₜ[R] 1) = x :=
  TensorProduct.inductionOn x
    (fun a h => by
      have hmap : LinearMap.mulLeft R a ∘ₗ μ.action.toLinearMap.flip 1 =
          LinearMap.toSpanSingleton R A a ∘ₗ counit (R := R) := by
        ext k
        simp [Algebra.smul_def, Algebra.commutes]
      have hmr : LinearMap.mulRight R (1 : H) = LinearMap.id := by
        ext k
        exact mul_one k
      calc
        μ.smashMul (a ⊗ₜ[R] h) (1 ⊗ₜ[R] 1)
            = TensorProduct.map (LinearMap.toSpanSingleton R A a ∘ₗ counit (R := R)) LinearMap.id
                (comul (R := R) h) := by
              rw [LeftModuleAlgebra.smashMul_tmul, LeftModuleAlgebra.smashMulPure, hmap, hmr]
        _ = (LinearMap.toSpanSingleton R A a).rTensor H
              ((counit (R := R)).rTensor H (comul h)) := by
              rw [← LinearMap.rTensor_def, LinearMap.rTensor_comp, LinearMap.comp_apply]
        _ = a ⊗ₜ[R] h := by
              rw [Coalgebra.rTensor_counit_comul]
              simp)
    (fun s t hs ht => by simp [LinearMap.add_apply, hs, ht])

/-- Helper 3-tensor contraction `(u ⊗ v) ⊗ w ↦ (a * (u · b) * (v · d)) ⊗ (w * n)` used to compare
the two parenthesizations of a triple smash product via `Coalgebra.coassoc_symm`. -/
private def assocTripleMap (μ : LeftModuleAlgebra R H A) (a b d : A) (n : H) :
    (H ⊗[R] H) ⊗[R] H →ₗ[R] A ⊗[R] H :=
  TensorProduct.map
    (LinearMap.mul' R A ∘ₗ
      TensorProduct.map (LinearMap.mulLeft R a ∘ₗ μ.action.toLinearMap.flip b)
        (μ.action.toLinearMap.flip d))
    (LinearMap.mulRight R n)

private theorem assocTripleMap_lhs (a b c : A) (h₁ l₁ l₂ m : H) (p : H ⊗[R] H) :
    TensorProduct.map
      (LinearMap.mulLeft R (a * μ.action h₁ b) ∘ₗ μ.action.toLinearMap.flip c)
      (LinearMap.mulRight R m) (p * (l₁ ⊗ₜ[R] l₂)) =
    assocTripleMap μ a b (μ.action l₁ c) (l₂ * m)
      ((TensorProduct.assoc R H H H).symm (h₁ ⊗ₜ[R] p)) :=
  TensorProduct.inductionOn p
    (fun u v => by simp [assocTripleMap, mul_assoc])
    (fun p₁ p₂ hp₁ hp₂ => by
      rw [add_mul, map_add, TensorProduct.tmul_add, map_add, map_add, hp₁, hp₂])

private theorem assocTripleMap_rhs (a b d : A) (n : H) (w : H ⊗[R] H) :
    TensorProduct.map (LinearMap.mulLeft R a ∘ₗ μ.action.toLinearMap.flip (b * d))
      (LinearMap.mulRight R n) w =
    assocTripleMap μ a b d n ((comul (R := R)).rTensor H w) :=
  TensorProduct.inductionOn w
    (fun h₁ h₂ => by
      classical
      let rh := ℛ R h₁
      simp only [TensorProduct.map_tmul, LinearMap.comp_apply, LinearMap.mulLeft_apply,
        LinearMap.flip_apply, AlgHom.toLinearMap_apply, LinearMap.mulRight_apply,
        LinearMap.rTensor_tmul]
      rw [μ.action_mul_eq_sum rh b d, ← rh.eq]
      have hsum_tmul (s : Finset (H × H)) (f : H × H → A) :
          (∑ i ∈ s, f i) ⊗ₜ[R] (h₂ * n) = ∑ i ∈ s, f i ⊗ₜ[R] (h₂ * n) :=
        map_sum ((TensorProduct.mk R A H).flip (h₂ * n)) f s
      have hsum_rt (s : Finset (H × H)) (f : H × H → H ⊗[R] H) :
          (∑ i ∈ s, f i) ⊗ₜ[R] h₂ = ∑ i ∈ s, f i ⊗ₜ[R] h₂ :=
        map_sum ((TensorProduct.mk R (H ⊗[R] H) H).flip h₂) f s
      rw [Finset.mul_sum, hsum_tmul, hsum_rt, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [assocTripleMap, mul_assoc])
    (fun w₁ w₂ hw₁ hw₂ => by rw [map_add, map_add, map_add, hw₁, hw₂])

private theorem smashMul_tmul_assoc (a b c : A) (h l m : H) :
    μ.smashMul (μ.smashMul (a ⊗ₜ[R] h) (b ⊗ₜ[R] l)) (c ⊗ₜ[R] m) =
      μ.smashMul (a ⊗ₜ[R] h) (μ.smashMul (b ⊗ₜ[R] l) (c ⊗ₜ[R] m)) := by
  classical
  let rl := ℛ R l
  have hlhs_w (w : H ⊗[R] H) :
      μ.smashMul (TensorProduct.map (LinearMap.mulLeft R a ∘ₗ μ.action.toLinearMap.flip b)
        (LinearMap.mulRight R l) w) (c ⊗ₜ[R] m) =
      ∑ j ∈ rl.index,
        assocTripleMap μ a b (μ.action (rl.left j) c) (rl.right j * m)
          ((TensorProduct.assoc R H H H).symm ((comul (R := R)).lTensor H w)) :=
    TensorProduct.inductionOn w
      (fun h₁ h₂ => by
        simp only [TensorProduct.map_tmul, LinearMap.comp_apply, LinearMap.mulLeft_apply,
          LinearMap.flip_apply, AlgHom.toLinearMap_apply, LinearMap.mulRight_apply,
          LeftModuleAlgebra.smashMul_tmul, LeftModuleAlgebra.smashMulPure, Bialgebra.comul_mul,
          ← rl.eq, Finset.mul_sum, map_sum, LinearMap.lTensor_tmul]
        exact Finset.sum_congr rfl fun j _ =>
          assocTripleMap_lhs a b c h₁ _ _ m (comul (R := R) h₂))
      (fun w₁ w₂ hw₁ hw₂ => by
        rw [map_add, map_add, LinearMap.add_apply, hw₁, hw₂, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← map_add, ← map_add, ← map_add])
  calc
    μ.smashMul (μ.smashMul (a ⊗ₜ[R] h) (b ⊗ₜ[R] l)) (c ⊗ₜ[R] m)
        = ∑ j ∈ rl.index,
            assocTripleMap μ a b (μ.action (rl.left j) c) (rl.right j * m)
              ((TensorProduct.assoc R H H H).symm ((comul (R := R)).lTensor H (comul h))) :=
          hlhs_w (comul (R := R) h)
    _ = ∑ j ∈ rl.index,
          assocTripleMap μ a b (μ.action (rl.left j) c) (rl.right j * m)
            ((comul (R := R)).rTensor H (comul h)) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Coalgebra.coassoc_symm_apply]
    _ = ∑ j ∈ rl.index,
          μ.smashMul (a ⊗ₜ[R] h)
            ((b * μ.action (rl.left j) c) ⊗ₜ[R] (rl.right j * m)) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          exact (assocTripleMap_rhs a b _ _ (comul (R := R) h)).symm
    _ = μ.smashMul (a ⊗ₜ[R] h) (μ.smashMul (b ⊗ₜ[R] l) (c ⊗ₜ[R] m)) := by
          rw [← map_sum, LeftModuleAlgebra.smashMul_tmul, μ.smashMulPure_eq_sum b rl c m]

private theorem smashMul_assoc (x y z : A ⊗[R] H) :
    μ.smashMul (μ.smashMul x y) z = μ.smashMul x (μ.smashMul y z) :=
  TensorProduct.inductionOn x
    (fun a h => TensorProduct.inductionOn y
      (fun b l => TensorProduct.inductionOn z
        (fun c m => smashMul_tmul_assoc a b c h l m)
        (fun z₁ z₂ hz₁ hz₂ => by rw [map_add, map_add, map_add, hz₁, hz₂]))
      (fun y₁ y₂ hy₁ hy₂ => by
        rw [map_add, map_add μ.smashMul, LinearMap.add_apply, map_add μ.smashMul,
          LinearMap.add_apply, map_add, hy₁, hy₂]))
    (fun x₁ x₂ hx₁ hx₂ => by
      rw [map_add, LinearMap.add_apply, map_add, LinearMap.add_apply, hx₁, hx₂,
        LinearMap.add_apply])

variable (μ) in
instance : Mul (SmashProduct μ) where
  mul x y := ofTensor (μ.smashMul x.toTensor y.toTensor)

variable (μ) in
instance : One (SmashProduct μ) where
  one := tmul μ 1 1

theorem one_def : (1 : SmashProduct μ) = tmul μ 1 1 :=
  (rfl)

@[simp]
theorem toTensor_one : (1 : SmashProduct μ).toTensor = 1 ⊗ₜ[R] 1 :=
  (rfl)

theorem toTensor_mul (x y : SmashProduct μ) :
    (x * y).toTensor = μ.smashMul x.toTensor y.toTensor :=
  (rfl)

variable (μ) in
instance instSemiring : Semiring (SmashProduct μ) where
  left_distrib x y z := by ext; exact map_add (μ.smashMul x.toTensor) y.toTensor z.toTensor
  right_distrib x y z := by ext; simp [toTensor_mul]
  zero_mul x := by ext; simp [toTensor_mul]
  mul_zero x := by ext; simp [toTensor_mul]
  mul_assoc x y z := by ext; exact smashMul_assoc x.toTensor y.toTensor z.toTensor
  one_mul x := by ext; exact one_smashMul x.toTensor
  mul_one x := by ext; exact smashMul_one x.toTensor

/-- Multiplication of pure smash tensors in terms of `LeftModuleAlgebra.smashMulPure`. -/
theorem tmul_mul_tmul (a b : A) (h l : H) :
    tmul μ a h * tmul μ b l = ofTensor (μ.smashMulPure a h b l) :=
  (rfl)

/-- Multiplication of pure smash tensors expanded in any finite representation of the coproduct:
`(a # h) * (b # l) = ∑ (a * (h₁ · b)) # (h₂ * l)`. -/
theorem tmul_mul_tmul_eq_sum (a : A) {h : H} {ι : Type*} (r : Coalgebra.Repr R h ι)
    (b : A) (l : H) :
    tmul μ a h * tmul μ b l =
      ∑ i ∈ r.index, tmul μ (a * μ.action (r.left i) b) (r.right i * l) := by
  ext
  simp [toTensor_mul, μ.smashMulPure_eq_sum a r b l]

@[simp]
theorem tmul_one_mul_tmul (a b : A) (l : H) :
    tmul μ a 1 * tmul μ b l = tmul μ (a * b) l := by
  ext
  simp [toTensor_mul, LeftModuleAlgebra.smashMulPure, Bialgebra.comul_one,
    Algebra.TensorProduct.one_def]

@[simp]
theorem tmul_mul_one_tmul (a : A) (h l : H) :
    tmul μ a h * tmul μ 1 l = tmul μ a (h * l) := by
  classical
  rw [tmul_mul_tmul_eq_sum (μ := μ) a (ℛ R h) 1 l]
  have hterm (i : H × H) :
      tmul μ (a * μ.action ((ℛ R h).left i) 1) (((ℛ R h).right i) * l) =
        tmul μ a ((counit (R := R) ((ℛ R h).left i) • (ℛ R h).right i) * l) := by
    rw [μ.action_one, Algebra.mul_smul_comm, mul_one, smul_tmul, smul_mul_assoc, tmul_smul]
  simp_rw [hterm]
  have hsum :
      ∑ i ∈ (ℛ R h).index, tmul μ a ((counit (R := R) ((ℛ R h).left i) • (ℛ R h).right i) * l) =
        tmul μ a (∑ i ∈ (ℛ R h).index,
          (counit (R := R) ((ℛ R h).left i) • (ℛ R h).right i) * l) :=
    (map_sum ((linearEquiv μ).symm.toLinearMap ∘ₗ TensorProduct.mk R A H a) _ _).symm
  rw [hsum, ← Finset.sum_mul, Coalgebra.sum_counit_smul (ℛ R h)]

variable (μ) in
instance instAlgebra : Algebra R (SmashProduct μ) :=
  Algebra.ofModule
    (fun r x y => by ext; simp [toTensor_mul])
    (fun r x y => by ext; simp [toTensor_mul])

theorem algebraMap_apply (r : R) :
    algebraMap R (SmashProduct μ) r = tmul μ (algebraMap R A r) 1 := by
  rw [Algebra.algebraMap_eq_smul_one, one_def, ← smul_tmul, Algebra.algebraMap_eq_smul_one]

/-! ### Canonical inclusions and the universal property -/

variable (μ) in
/-- The canonical `R`-algebra homomorphism `A →ₐ[R] SmashProduct μ`, `a ↦ a # 1`. -/
def includeLeft : A →ₐ[R] SmashProduct μ where
  toFun a := tmul μ a 1
  map_one' := rfl
  map_mul' a b := (tmul_one_mul_tmul a b 1).symm
  map_zero' := zero_tmul 1
  map_add' a b := add_tmul a b 1
  commutes' r := (algebraMap_apply r).symm

variable (μ) in
/-- The canonical `R`-algebra homomorphism `H →ₐ[R] SmashProduct μ`, `h ↦ 1 # h`. -/
def includeRight : H →ₐ[R] SmashProduct μ where
  toFun h := tmul μ 1 h
  map_one' := rfl
  map_mul' h l := (tmul_mul_one_tmul 1 h l).symm
  map_zero' := tmul_zero 1
  map_add' h l := tmul_add 1 h l
  commutes' r := by
    rw [algebraMap_apply, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
      smul_tmul, tmul_smul]

@[simp]
theorem includeLeft_apply (a : A) : includeLeft μ a = tmul μ a 1 :=
  (rfl)

@[simp]
theorem includeRight_apply (h : H) : includeRight μ h = tmul μ 1 h :=
  (rfl)

/-- Every pure smash tensor factors as `(a # 1) * (1 # h)`. -/
theorem includeLeft_mul_includeRight (a : A) (h : H) :
    includeLeft μ a * includeRight μ h = tmul μ a h := by
  simp

/-- The commutation relation `(1 # h) * (a # 1) = ∑ (h₁ · a) # h₂` in any coproduct
representation. -/
theorem one_tmul_mul_tmul_one_eq_sum {h : H} {ι : Type*} (r : Coalgebra.Repr R h ι) (a : A) :
    tmul μ 1 h * tmul μ a 1 = ∑ i ∈ r.index, tmul μ (μ.action (r.left i) a) (r.right i) := by
  simpa using tmul_mul_tmul_eq_sum (μ := μ) 1 r a 1

/-- The canonical inclusions satisfy `LeftModuleAlgebra.SmashCompatible`. -/
theorem smashCompatible_include : μ.SmashCompatible (includeLeft μ) (includeRight μ) := by
  intro h a
  simp only [includeRight_apply, includeLeft_apply, tmul_mul_tmul, LeftModuleAlgebra.smashMulPure]
  exact TensorProduct.inductionOn (comul (R := R) h)
    (fun h₁ h₂ => by simp)
    (fun x y hx hy => by rw [map_add, ofTensor_add, map_add, map_add, hx, hy])

/-- Two `R`-algebra homomorphisms out of `SmashProduct μ` are equal when they agree on `A` and
`H`. -/
@[ext]
theorem algHom_ext {C : Type*} [Semiring C] [Algebra R C]
    {f g : SmashProduct μ →ₐ[R] C}
    (hA : ∀ a, f (includeLeft μ a) = g (includeLeft μ a))
    (hH : ∀ h, f (includeRight μ h) = g (includeRight μ h)) : f = g := by
  apply AlgHom.toLinearMap_injective
  refine lhom_ext fun a h => ?_
  simp only [AlgHom.toLinearMap_apply, ← includeLeft_mul_includeRight, map_mul, hA a, hH h]

/-- Universal property of `SmashProduct μ`: a pair of `R`-algebra homomorphisms `fA : A →ₐ[R] C`
and `fH : H →ₐ[R] C` satisfying `μ.SmashCompatible fA fH` extends to `SmashProduct μ →ₐ[R] C`
via `a # h ↦ fA a * fH h`. -/
def lift {C : Type*} [Semiring C] [Algebra R C]
    (fA : A →ₐ[R] C) (fH : H →ₐ[R] C) (hcompat : μ.SmashCompatible fA fH) :
    SmashProduct μ →ₐ[R] C :=
  let φ : SmashProduct μ →ₗ[R] C :=
    (LinearMap.mul' R C ∘ₗ TensorProduct.map fA.toLinearMap fH.toLinearMap) ∘ₗ
      (linearEquiv μ).toLinearMap
  AlgHom.ofLinearMap φ
    (by simp [φ])
    (fun x y =>
      SmashProduct.inductionOn x
        (fun a h =>
          SmashProduct.inductionOn y
            (fun b l => by
              simp only [φ, LinearMap.comp_apply, LinearEquiv.coe_coe, linearEquiv_apply,
                toTensor_tmul, TensorProduct.map_tmul, AlgHom.toLinearMap_apply,
                LinearMap.mul'_apply, tmul_mul_tmul, LeftModuleAlgebra.smashMulPure]
              have hmid (w : H ⊗[R] H) :
                  LinearMap.mul' R C
                    (TensorProduct.map fA.toLinearMap fH.toLinearMap
                      (TensorProduct.map (LinearMap.mulLeft R a ∘ₗ μ.action.toLinearMap.flip b)
                        (LinearMap.mulRight R l) w)) =
                  fA a * LinearMap.mul' R C
                    (TensorProduct.map (fA.toLinearMap ∘ₗ μ.action.toLinearMap.flip b)
                      fH.toLinearMap w) * fH l :=
                TensorProduct.inductionOn w
                  (fun h₁ h₂ => by simp [mul_assoc])
                  (fun w₁ w₂ hw₁ hw₂ => by simp [map_add, hw₁, hw₂, mul_add, add_mul])
              rw [hmid (comul (R := R) h), ← hcompat h b]
              simp only [mul_assoc])
            (fun y₁ y₂ hy₁ hy₂ => by rw [mul_add, map_add, map_add, hy₁, hy₂, mul_add]))
        (fun x₁ x₂ hx₁ hx₂ => by rw [add_mul, map_add, map_add, hx₁, hx₂, add_mul]))

@[simp]
theorem lift_tmul {C : Type*} [Semiring C] [Algebra R C]
    (fA : A →ₐ[R] C) (fH : H →ₐ[R] C) (hcompat : μ.SmashCompatible fA fH) (a : A) (h : H) :
    lift fA fH hcompat (tmul μ a h) = fA a * fH h :=
  (rfl)

@[simp]
theorem lift_comp_includeLeft {C : Type*} [Semiring C] [Algebra R C]
    (fA : A →ₐ[R] C) (fH : H →ₐ[R] C) (hcompat : μ.SmashCompatible fA fH) :
    (lift fA fH hcompat).comp (includeLeft μ) = fA := by
  ext a
  simp

@[simp]
theorem lift_comp_includeRight {C : Type*} [Semiring C] [Algebra R C]
    (fA : A →ₐ[R] C) (fH : H →ₐ[R] C) (hcompat : μ.SmashCompatible fA fH) :
    (lift fA fH hcompat).comp (includeRight μ) = fH := by
  ext h
  simp

@[simp]
theorem lift_include : lift (includeLeft μ) (includeRight μ) smashCompatible_include =
    AlgHom.id R (SmashProduct μ) := by
  ext <;> simp

/-- Unique factorization of covariant algebra-map pairs through `SmashProduct μ`. -/
theorem lift_unique {C : Type*} [Semiring C] [Algebra R C]
    (fA : A →ₐ[R] C) (fH : H →ₐ[R] C) (hcompat : μ.SmashCompatible fA fH) :
    ∃! f : SmashProduct μ →ₐ[R] C,
      (∀ a, f (includeLeft μ a) = fA a) ∧ (∀ h, f (includeRight μ h) = fH h) := by
  refine ⟨lift fA fH hcompat, ⟨fun a => by simp, fun h => by simp⟩, ?_⟩
  rintro g ⟨hgA, hgH⟩
  ext x
  · simpa using hgA x
  · simpa using hgH x

/-- Restriction of any algebra map out of `SmashProduct μ` to `A` and `H` yields a
`SmashCompatible` pair. -/
theorem smashCompatible_comp {C : Type*} [Semiring C] [Algebra R C]
    (f : SmashProduct μ →ₐ[R] C) :
    μ.SmashCompatible (f.comp (includeLeft μ)) (f.comp (includeRight μ)) := by
  intro h a
  have key := congrArg f (smashCompatible_include (μ := μ) h a)
  rw [map_mul] at key
  refine key.trans ?_
  exact TensorProduct.inductionOn (comul (R := R) h)
    (fun h₁ h₂ => by
      simp only [TensorProduct.map_tmul, LinearMap.comp_apply, LinearMap.flip_apply,
        AlgHom.toLinearMap_apply, LinearMap.mul'_apply, AlgHom.comp_apply, ← map_mul,
        includeLeft_mul_includeRight])
    (fun x y hx hy => by simp [map_add, hx, hy])

variable (μ) in
/-- Equivalence between `R`-algebra homomorphisms out of `SmashProduct μ` and `SmashCompatible`
pairs of `R`-algebra homomorphisms out of `A` and `H`. -/
def liftEquiv {C : Type*} [Semiring C] [Algebra R C] :
    (SmashProduct μ →ₐ[R] C) ≃
      {p : (A →ₐ[R] C) × (H →ₐ[R] C) // μ.SmashCompatible p.1 p.2} where
  toFun f := ⟨(f.comp (includeLeft μ), f.comp (includeRight μ)), smashCompatible_comp f⟩
  invFun p := lift p.1.1 p.1.2 p.2
  left_inv f := by ext <;> simp [← one_def]
  right_inv p := by
    ext a
    · exact AlgHom.congr_fun (lift_comp_includeLeft p.1.1 p.1.2 p.2) a
    · exact AlgHom.congr_fun (lift_comp_includeRight p.1.1 p.1.2 p.2) a

/-! ### Group-like, skew-primitive, and primitive commutation rules -/

/-- Multiplication on the left by `a # g` for a group-like element `g`. -/
theorem tmul_mul_tmul_of_isGroupLikeElem (a b : A) {g : H} (hg : IsGroupLikeElem R g) (l : H) :
    tmul μ a g * tmul μ b l = tmul μ (a * μ.action g b) (g * l) := by
  ext
  simp [toTensor_mul, LeftModuleAlgebra.smashMulPure, hg.comul_eq_tmul_self]

/-- Straightening `(1 # g) * (a # 1) = (g · a) # g` for a group-like element `g`. -/
theorem one_tmul_mul_tmul_one_of_isGroupLikeElem {g : H} (hg : IsGroupLikeElem R g) (a : A) :
    tmul μ 1 g * tmul μ a 1 = tmul μ (μ.action g a) g := by
  simpa using tmul_mul_tmul_of_isGroupLikeElem (μ := μ) 1 a hg 1

/-- Multiplication on the left by `a # d` for a `(g, h)`-skew-primitive element `d`. -/
theorem tmul_mul_tmul_of_isSkewPrimitiveElem (a b : A) {g h d : H}
    (hd : IsSkewPrimitiveElem R g h d) (l : H) :
    tmul μ a d * tmul μ b l =
      tmul μ (a * μ.action g b) (d * l) + tmul μ (a * μ.action d b) (h * l) := by
  ext
  simp [toTensor_mul, LeftModuleAlgebra.smashMulPure, hd.comul_eq_tmul_add_tmul]

/-- Straightening `(1 # d) * (a # 1) = (g · a) # d + (d · a) # h` for a `(g, h)`-skew-primitive
element `d`. -/
theorem one_tmul_mul_tmul_one_of_isSkewPrimitiveElem {g h d : H}
    (hd : IsSkewPrimitiveElem R g h d) (a : A) :
    tmul μ 1 d * tmul μ a 1 = tmul μ (μ.action g a) d + tmul μ (μ.action d a) h := by
  simpa using tmul_mul_tmul_of_isSkewPrimitiveElem (μ := μ) 1 a hd 1

/-- Multiplication on the left by `a # d` for a primitive element `d`. -/
theorem tmul_mul_tmul_of_isPrimitiveElem (a b : A) {d : H} (hd : Bialgebra.IsPrimitiveElem R d)
    (l : H) :
    tmul μ a d * tmul μ b l = tmul μ (a * μ.action d b) l + tmul μ (a * b) (d * l) := by
  rw [tmul_mul_tmul_of_isSkewPrimitiveElem a b hd l, map_one, one_apply_eq_self, one_mul,
    add_comm]

/-- Straightening `(1 # d) * (a # 1) = (d · a) # 1 + a # d` for a primitive element `d`,
yielding the twisted derivation commutator `[1 # d, a # 1] = (d · a) # 1`. -/
theorem one_tmul_mul_tmul_one_of_isPrimitiveElem {d : H} (hd : Bialgebra.IsPrimitiveElem R d)
    (a : A) :
    tmul μ 1 d * tmul μ a 1 = tmul μ (μ.action d a) 1 + tmul μ a d := by
  simpa using tmul_mul_tmul_of_isPrimitiveElem (μ := μ) 1 a hd 1

/-! ### Counit retraction, injectivity, and module properties -/

variable (μ) in
/-- The `R`-linear map `id_A ⊗ ε : SmashProduct μ →ₗ[R] A` sending `a # h ↦ ε(h) • a`.
It is a left inverse to `includeLeft μ`. -/
def counitRetraction : SmashProduct μ →ₗ[R] A :=
  (TensorProduct.rid R A).toLinearMap ∘ₗ
    (counit (R := R) (A := H)).lTensor A ∘ₗ (linearEquiv μ).toLinearMap

@[simp]
theorem counitRetraction_tmul (a : A) (h : H) :
    counitRetraction μ (tmul μ a h) = counit (R := R) h • a := by
  simp [counitRetraction]

theorem counitRetraction_includeLeft (a : A) :
    counitRetraction μ (includeLeft μ a) = a := by
  simp

/-- The canonical map `a ↦ a # 1` is unconditionally injective for every bialgebra `H` and
module algebra `A`, split `R`-linearly by `counitRetraction`. -/
theorem includeLeft_injective : Function.Injective (includeLeft μ) :=
  Function.LeftInverse.injective counitRetraction_includeLeft

theorem includeLeft_inj {a b : A} : includeLeft μ a = includeLeft μ b ↔ a = b :=
  includeLeft_injective.eq_iff

@[simp]
theorem tmul_one_inj {a b : A} : tmul μ a 1 = tmul μ b 1 ↔ a = b :=
  includeLeft_inj

/-- A group-like element `g` commutes with `a # 1` in `SmashProduct μ` if and only if `g` fixes
`a`. In particular, any nontrivial group-like action produces a noncommutative smash product even
when `A` and `H` are commutative. -/
theorem commute_includeRight_includeLeft_of_isGroupLikeElem {g : H}
    (hg : IsGroupLikeElem R g) (a : A) :
    Commute (includeRight μ g) (includeLeft μ a) ↔ μ.action g a = a := by
  rw [Commute, SemiconjBy, includeRight_apply, includeLeft_apply,
    one_tmul_mul_tmul_one_of_isGroupLikeElem hg, tmul_one_mul_tmul, mul_one]
  refine ⟨fun h => ?_, fun h => by rw [h]⟩
  have hc := congrArg (counitRetraction μ) h
  simpa [hg.counit_eq_one] using hc

instance [Subsingleton A] : Subsingleton (SmashProduct μ) :=
  (linearEquiv μ).toEquiv.subsingleton

instance [Subsingleton H] : Subsingleton (SmashProduct μ) :=
  (linearEquiv μ).toEquiv.subsingleton

/-- When `A` is trivial (`Subsingleton A`), `includeRight μ` sends every element of `H` to `0`. -/
theorem includeRight_eq_zero [Subsingleton A] (h : H) : includeRight μ h = 0 :=
  Subsingleton.elim _ _

/-- Any `R`-linear functional `φ : A →ₗ[R] R` with `φ 1 = 1` splits `includeRight μ` `R`-linearly,
making `h ↦ 1 # h` injective. -/
theorem includeRight_injective_of_apply_one_eq_one (φ : A →ₗ[R] R) (hφ : φ 1 = 1) :
    Function.Injective (includeRight μ) := by
  refine Function.LeftInverse.injective (g := fun x =>
    TensorProduct.lid R H (φ.rTensor H x.toTensor)) fun h => ?_
  simp [hφ]

/-- Over a semifield on which `A` is projective (in particular over any field), every bialgebra
`H` is nontrivial because `ε(1) = 1 ≠ 0`, and `includeRight μ` is injective if and only if `A` is
nontrivial. -/
theorem includeRight_injective_iff {K : Type u} [Semifield K]
    {H : Type v} [Semiring H] [Bialgebra K H]
    {A : Type w} [Semiring A] [Algebra K A] [Module.Projective K A]
    (μ : LeftModuleAlgebra K H A) :
    Function.Injective (includeRight μ) ↔ Nontrivial A := by
  have : Nontrivial H := ⟨⟨1, 0, fun h10 => one_ne_zero (α := K) <| by
    simpa using congrArg (counit (R := K)) h10⟩⟩
  refine ⟨fun hinj => ?_, fun _ => ?_⟩
  · contrapose! hinj
    intro h
    exact one_ne_zero (h (Subsingleton.elim (includeRight μ 1) (includeRight μ 0)))
  · obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one K (one_ne_zero (α := A))
    exact includeRight_injective_of_apply_one_eq_one φ hφ

instance [Module.Finite R A] [Module.Finite R H] : Module.Finite R (SmashProduct μ) :=
  Module.Finite.equiv (linearEquiv μ).symm

instance [Module.Free R A] [Module.Free R H] : Module.Free R (SmashProduct μ) :=
  Module.Free.of_equiv (linearEquiv μ).symm

instance [Module.Projective R A] [Module.Projective R H] : Module.Projective R (SmashProduct μ) :=
  Module.Projective.of_equiv (linearEquiv μ).symm

/-- For free `R`-modules `A` and `H` over a base satisfying `StrongRankCondition`, the `finrank`
of `SmashProduct μ` is `finrank R A * finrank R H`. -/
@[simp]
theorem finrank_eq [StrongRankCondition R] [Module.Free R A] [Module.Free R H] :
    Module.finrank R (SmashProduct μ) = Module.finrank R A * Module.finrank R H := by
  rw [(linearEquiv μ).finrank_eq, Module.finrank_tensorProduct]

end Semiring

section Ring

variable {R : Type u} {H : Type v} {A : Type w}
variable [CommRing R] [Ring H] [Bialgebra R H] [Ring A] [Algebra R A]
variable {μ : LeftModuleAlgebra R H A}

variable (μ) in
instance : AddCommGroup (SmashProduct μ) :=
  Equiv.addCommGroup ⟨toTensor, ofTensor, fun _ => rfl, fun _ => rfl⟩

variable (μ) in
instance instRing : Ring (SmashProduct μ) :=
  { (inferInstance : AddCommGroup (SmashProduct μ)),
    (inferInstance : Semiring (SmashProduct μ)) with }

@[simp]
theorem toTensor_neg (x : SmashProduct μ) : (-x).toTensor = -x.toTensor :=
  (rfl)

@[simp]
theorem toTensor_sub (x y : SmashProduct μ) : (x - y).toTensor = x.toTensor - y.toTensor :=
  (rfl)

@[simp]
theorem neg_tmul (a : A) (h : H) : tmul μ (-a) h = -tmul μ a h := by
  ext
  exact TensorProduct.neg_tmul a h

@[simp]
theorem tmul_neg (a : A) (h : H) : tmul μ a (-h) = -tmul μ a h := by
  ext
  exact TensorProduct.tmul_neg a h

/-- When `A` is trivial (`Subsingleton A`), the kernel of `includeRight μ` is all of `H`. -/
theorem ker_includeRight_of_subsingleton [Subsingleton A] :
    RingHom.ker (includeRight μ).toRingHom = ⊤ := by
  ext h
  simpa only [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Submodule.mem_top,
    iff_true] using Subsingleton.elim _ _

/-- A primitive element `d` commutes with `a # 1` in `SmashProduct μ` if and only if `d · a = 0`. -/
theorem commute_includeRight_includeLeft_of_isPrimitiveElem {d : H}
    (hd : Bialgebra.IsPrimitiveElem R d) (a : A) :
    Commute (includeRight μ d) (includeLeft μ a) ↔ μ.action d a = 0 := by
  rw [Commute, SemiconjBy, includeRight_apply, includeLeft_apply,
    one_tmul_mul_tmul_one_of_isPrimitiveElem hd, tmul_one_mul_tmul, mul_one,
    add_eq_right, ← includeLeft_apply, ← map_zero (includeLeft μ), includeLeft_inj]

end Ring

end SmashProduct

end TauCeti

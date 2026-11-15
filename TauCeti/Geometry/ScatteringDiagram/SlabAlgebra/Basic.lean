/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import TauCeti.Algebra.DirectSum.Internal

/-!
# Slab algebras and their normal-form basis

For a commutative ring `B` and an element `q ∈ B`, the *slab algebra* `SlabAlgebra B q` is the
quotient `B[X, Y] / (X Y - q)`. In log Calabi–Yau mirror symmetry and wall-crossing diagrams,
taking `B = S[Λ_b]` for a tangential lattice `Λ_b` and `q ∈ S[Λ_b]` models the local coordinate
ring across a codimension-one slab, where `X` and `Y` are the incoming monomials from the two
adjacent chambers whose product equals the tangential slab function `q`.

Every mixed monomial `X^a Y^b` reduces modulo `X Y - q` to `q^{\min(a, b)}` times a pure power of
`X` or `Y`. Indexing these pure powers by `n ∈ ℤ` via `Z q n = X^{-n}` for `n < 0` and
`Z q n = Y^n` for `n ≥ 0` (so `Z q 0 = 1`) yields:

* a free `B`-basis `SlabAlgebra.slabBasis q : Module.Basis ℤ B (SlabAlgebra B q)` for arbitrary
  `q` (without any regularity or domain assumption on `B` or `q`), making `SlabAlgebra B q` free
  and hence flat over `B`, with injective structure map `algebraMap B (SlabAlgebra B q)`;
* the multiplication law `Z q n * Z q m = q^r • Z q (n + m)` with
  `r = (|n| + |m| - |n + m|) / 2`;
* the normal-weight `ℤ`-grading `SlabAlgebra.weightSubmodule q` in which `X` has weight `-1`, `Y`
  has weight `1`, `B` has weight `0`, and the weight-`n` piece is `B ∙ Z q n`;
* functorial ring and algebra homomorphisms `SlabAlgebra.map` and `SlabAlgebra.mapAlgHom` along
  coefficient maps sending `q` to `q'`.

## Main definitions and results

* `TauCeti.SlabVar`, `TauCeti.slabIdeal`, `TauCeti.SlabAlgebra`: the presentation
  `B[X, Y] / (X Y - q)`.
* `TauCeti.SlabAlgebra.X`, `TauCeti.SlabAlgebra.Y`, `TauCeti.SlabAlgebra.lift`,
  `TauCeti.SlabAlgebra.liftEquiv`, `TauCeti.SlabAlgebra.liftRingHom`: generators and universal
  properties.
* `TauCeti.SlabAlgebra.Z`, `TauCeti.SlabAlgebra.Z_mul`: the integer-indexed normal-form elements
  and their product formula.
* `TauCeti.SlabAlgebra.slabBasis`: the `B`-basis `n ↦ Z q n`
  (`{X^a | a ≥ 0} ∪ {Y^a | a ≥ 1}`).
* `TauCeti.SlabAlgebra.weightSubmodule`: the normal-weight `ℤ`-graded `B`-algebra decomposition.
* `TauCeti.SlabAlgebra.map`, `TauCeti.SlabAlgebra.mapAlgHom`: functoriality in `(B, q)`.

## References

* M. Gross and B. Siebert, *An Invitation to Toric Degenerations*, §2.3, arXiv:0808.2749v2.
* M. Gross, P. Hacking, and B. Siebert, *Theta functions on varieties with effective
  anti-canonical class*, §3.1, arXiv:1601.07081v4.
-/

public section

noncomputable section

namespace TauCeti

/-- The two transverse variables `X` and `Y` of a slab algebra `B[X, Y] / (X Y - q)`. -/
inductive SlabVar : Type
  | X
  | Y
  deriving DecidableEq

/-- The defining principal ideal `(X Y - q)` in `B[X, Y]`. -/
def slabIdeal (B : Type*) [CommRing B] (q : B) : Ideal (MvPolynomial SlabVar B) :=
  Ideal.span {MvPolynomial.X SlabVar.X * MvPolynomial.X SlabVar.Y - MvPolynomial.C q}

/-- Unfold the defining ideal `(X Y - q)` of the slab algebra. -/
theorem slabIdeal_def (B : Type*) [CommRing B] (q : B) :
    slabIdeal B q =
      Ideal.span {MvPolynomial.X SlabVar.X * MvPolynomial.X SlabVar.Y - MvPolynomial.C q} :=
  (rfl)

/-- The slab algebra `B[X, Y] / (X Y - q)` over a commutative ring `B` with parameter `q : B`. -/
abbrev SlabAlgebra (B : Type*) [CommRing B] (q : B) :=
  MvPolynomial SlabVar B ⧸ slabIdeal B q

namespace SlabAlgebra

variable {B B' B'' C R : Type*} [CommRing B] [CommRing B'] [CommRing B''] [CommRing C]

/-- The quotient map `B[X, Y] →ₐ[B] SlabAlgebra B q`. -/
def mkAlgHom (q : B) : MvPolynomial SlabVar B →ₐ[B] SlabAlgebra B q :=
  Ideal.Quotient.mkₐ B (slabIdeal B q)

@[simp]
theorem coe_mkAlgHom (q : B) :
    (mkAlgHom q : MvPolynomial SlabVar B →+* SlabAlgebra B q) =
      Ideal.Quotient.mk (slabIdeal B q) :=
  (rfl)

theorem mkAlgHom_surjective (q : B) : Function.Surjective (mkAlgHom q) :=
  Ideal.Quotient.mk_surjective

/-- The left incoming generator `X` in `SlabAlgebra B q`. -/
def X (q : B) : SlabAlgebra B q :=
  mkAlgHom q (MvPolynomial.X SlabVar.X)

/-- The right incoming generator `Y` in `SlabAlgebra B q`. -/
def Y (q : B) : SlabAlgebra B q :=
  mkAlgHom q (MvPolynomial.X SlabVar.Y)

theorem mk_X_eq_X (q : B) :
    Ideal.Quotient.mk (slabIdeal B q) (MvPolynomial.X SlabVar.X) = X q :=
  (rfl)

theorem mk_Y_eq_Y (q : B) :
    Ideal.Quotient.mk (slabIdeal B q) (MvPolynomial.X SlabVar.Y) = Y q :=
  (rfl)

/-- The defining relation `X * Y = q` in `SlabAlgebra B q`. -/
@[simp]
theorem X_mul_Y (q : B) : X q * Y q = algebraMap B (SlabAlgebra B q) q := by
  rw [← mk_X_eq_X, ← mk_Y_eq_Y, ← map_mul,
    IsScalarTower.algebraMap_apply B (MvPolynomial SlabVar B) (SlabAlgebra B q),
    MvPolynomial.algebraMap_eq, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq, slabIdeal_def]
  exact Ideal.subset_span rfl

/-- Commuted form `Y * X = q` of the defining slab relation. -/
@[simp]
theorem Y_mul_X (q : B) : Y q * X q = algebraMap B (SlabAlgebra B q) q := by
  rw [mul_comm, X_mul_Y]

/-- Two ring homomorphisms out of `SlabAlgebra B q` agree when they agree on `B`, `X` and `Y`. -/
theorem ringHom_ext {q : B} {f g : SlabAlgebra B q →+* C}
    (hB : ∀ b : B, f (algebraMap B (SlabAlgebra B q) b) = g (algebraMap B (SlabAlgebra B q) b))
    (hX : f (X q) = g (X q)) (hY : f (Y q) = g (Y q)) : f = g := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro b
    simpa [IsScalarTower.algebraMap_apply B (MvPolynomial SlabVar B) (SlabAlgebra B q)] using hB b
  · rintro (_ | _)
    · exact hX
    · exact hY

/-- Two `R`-algebra homomorphisms out of `SlabAlgebra B q` agree when they agree on `B`, `X` and
`Y`. -/
theorem algHom_ext_of_algebra [CommSemiring R] [Algebra R B] [Algebra R C]
    {q : B} {f g : SlabAlgebra B q →ₐ[R] C}
    (hB : ∀ b : B, f (algebraMap B (SlabAlgebra B q) b) = g (algebraMap B (SlabAlgebra B q) b))
    (hX : f (X q) = g (X q)) (hY : f (Y q) = g (Y q)) : f = g :=
  AlgHom.toRingHom_injective (ringHom_ext hB hX hY)

/-- Two `B`-algebra homomorphisms out of `SlabAlgebra B q` agree when they agree on `X` and `Y`. -/
@[ext]
theorem algHom_ext [Algebra B C] {q : B} {f g : SlabAlgebra B q →ₐ[B] C}
    (hX : f (X q) = g (X q)) (hY : f (Y q) = g (Y q)) : f = g :=
  algHom_ext_of_algebra (fun b => by rw [AlgHom.commutes, AlgHom.commutes]) hX hY

/-- Universal property of `SlabAlgebra B q` for ring homomorphisms: a ring map `φ : B →+* C` and
elements `x, y : C` satisfying `x * y = φ q` determine a unique ring homomorphism
`SlabAlgebra B q →+* C`. -/
def liftRingHom {q : B} (φ : B →+* C) (x y : C) (hxy : x * y = φ q) :
    SlabAlgebra B q →+* C :=
  Ideal.Quotient.lift (slabIdeal B q)
    (MvPolynomial.eval₂Hom φ fun v => SlabVar.casesOn v x y)
    (by
      intro p hp
      rw [slabIdeal_def, Ideal.mem_span_singleton] at hp
      rcases hp with ⟨r, rfl⟩
      simp [hxy])

@[simp]
theorem liftRingHom_algebraMap {q : B} (φ : B →+* C) (x y : C) (hxy : x * y = φ q) (b : B) :
    liftRingHom φ x y hxy (algebraMap B (SlabAlgebra B q) b) = φ b := by
  rw [IsScalarTower.algebraMap_apply B (MvPolynomial SlabVar B) (SlabAlgebra B q)]
  exact MvPolynomial.eval₂_C _ _ b

@[simp]
theorem liftRingHom_X {q : B} (φ : B →+* C) (x y : C) (hxy : x * y = φ q) :
    liftRingHom φ x y hxy (X q) = x :=
  MvPolynomial.eval₂_X _ _ SlabVar.X

@[simp]
theorem liftRingHom_Y {q : B} (φ : B →+* C) (x y : C) (hxy : x * y = φ q) :
    liftRingHom φ x y hxy (Y q) = y :=
  MvPolynomial.eval₂_X _ _ SlabVar.Y

/-- Universal property of `SlabAlgebra B q` as a `B`-algebra: pairs `(x, y)` in a commutative
`B`-algebra `C` satisfying `x * y = algebraMap B C q` correspond to `B`-algebra maps
`SlabAlgebra B q →ₐ[B] C`. -/
def lift [Algebra B C] (q : B) (x y : C) (hxy : x * y = algebraMap B C q) :
    SlabAlgebra B q →ₐ[B] C where
  toRingHom := liftRingHom (algebraMap B C) x y hxy
  commutes' := liftRingHom_algebraMap (algebraMap B C) x y hxy

@[simp]
theorem coe_lift [Algebra B C] (q : B) (x y : C) (hxy : x * y = algebraMap B C q) :
    (lift q x y hxy : SlabAlgebra B q →+* C) = liftRingHom (algebraMap B C) x y hxy :=
  (rfl)

@[simp]
theorem lift_X [Algebra B C] (q : B) (x y : C) (hxy : x * y = algebraMap B C q) :
    lift q x y hxy (X q) = x :=
  liftRingHom_X (algebraMap B C) x y hxy

@[simp]
theorem lift_Y [Algebra B C] (q : B) (x y : C) (hxy : x * y = algebraMap B C q) :
    lift q x y hxy (Y q) = y :=
  liftRingHom_Y (algebraMap B C) x y hxy

/-- Equivalence between `B`-algebra homomorphisms `SlabAlgebra B q →ₐ[B] C` and pairs `(x, y)`
in `C` with `x * y = algebraMap B C q`. -/
def liftEquiv (q : B) (C : Type*) [CommRing C] [Algebra B C] :
    (SlabAlgebra B q →ₐ[B] C) ≃ { p : C × C // p.1 * p.2 = algebraMap B C q } where
  toFun f := ⟨(f (X q), f (Y q)), by rw [← map_mul, X_mul_Y, AlgHom.commutes]⟩
  invFun p := lift q p.1.1 p.1.2 p.2
  left_inv f := algHom_ext (lift_X _ _ _ _) (lift_Y _ _ _ _)
  right_inv p := Subtype.ext (Prod.ext (lift_X _ _ _ _) (lift_Y _ _ _ _))

@[simp]
theorem liftEquiv_apply_fst [Algebra B C] (q : B) (f : SlabAlgebra B q →ₐ[B] C) :
    ((liftEquiv q C f : C × C).1) = f (X q) :=
  (rfl)

@[simp]
theorem liftEquiv_apply_snd [Algebra B C] (q : B) (f : SlabAlgebra B q →ₐ[B] C) :
    ((liftEquiv q C f : C × C).2) = f (Y q) :=
  (rfl)

@[simp]
theorem liftEquiv_symm_apply [Algebra B C] (q : B)
    (p : { p : C × C // p.1 * p.2 = algebraMap B C q }) :
    (liftEquiv q C).symm p = lift q p.1.1 p.1.2 p.2 :=
  (rfl)

/-! ### Normal-form elements `Z_n` and multiplication -/

/-- The integer-indexed normal-form elements of `SlabAlgebra B q`: `Z q n = X^{-n}` for `n < 0`,
`Z q 0 = 1`, and `Z q n = Y^n` for `n > 0`. -/
def Z (q : B) (n : ℤ) : SlabAlgebra B q :=
  if n < 0 then X q ^ n.natAbs else Y q ^ n.natAbs

theorem Z_def (q : B) (n : ℤ) :
    Z q n = if n < 0 then X q ^ n.natAbs else Y q ^ n.natAbs :=
  (rfl)

theorem Z_of_lt_zero (q : B) {n : ℤ} (hn : n < 0) : Z q n = X q ^ n.natAbs :=
  ite_eq_left hn

theorem Z_of_nonneg (q : B) {n : ℤ} (hn : 0 ≤ n) : Z q n = Y q ^ n.natAbs :=
  ite_eq_right (not_lt.mpr hn)

@[simp]
theorem Z_zero (q : B) : Z q 0 = 1 := by
  simp [Z_def]

@[simp]
theorem Z_one (q : B) : Z q 1 = Y q := by
  simp [Z_def]

@[simp]
theorem Z_neg_one (q : B) : Z q (-1) = X q := by
  simp [Z_def]

@[simp]
theorem Z_natCast (q : B) (a : ℕ) : Z q (a : ℤ) = Y q ^ a := by
  rw [Z_of_nonneg q (Int.natCast_nonneg a), Int.natAbs_natCast]

@[simp]
theorem Z_neg_natCast (q : B) (a : ℕ) : Z q (-(a : ℤ)) = X q ^ a := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  · rw [Z_of_lt_zero q (by omega), Int.natAbs_neg, Int.natAbs_natCast]

@[simp]
theorem liftRingHom_Z {q : B} (φ : B →+* C) (x y : C) (hxy : x * y = φ q) (n : ℤ) :
    liftRingHom φ x y hxy (Z q n) = if n < 0 then x ^ n.natAbs else y ^ n.natAbs := by
  rw [Z_def]
  split_ifs <;> simp

@[simp]
theorem lift_Z [Algebra B C] (q : B) (x y : C) (hxy : x * y = algebraMap B C q) (n : ℤ) :
    lift q x y hxy (Z q n) = if n < 0 then x ^ n.natAbs else y ^ n.natAbs :=
  liftRingHom_Z (algebraMap B C) x y hxy n

/-- A mixed monomial `X^a Y^b` reduces in `SlabAlgebra B q` to `q^{\min(a, b)} Z_{b - a}`. -/
theorem X_pow_mul_Y_pow (q : B) (a b : ℕ) :
    X q ^ a * Y q ^ b = algebraMap B (SlabAlgebra B q) (q ^ min a b) * Z q ((b : ℤ) - a) := by
  induction a generalizing b with
  | zero => simp
  | succ a ih =>
    cases b with
    | zero =>
      have h0 : ((0 : ℕ) : ℤ) - ((a + 1 : ℕ) : ℤ) = -((a + 1 : ℕ) : ℤ) := by omega
      rw [pow_zero, mul_one, Nat.min_zero, pow_zero, map_one, one_mul, h0, Z_neg_natCast]
    | succ b =>
      have hsub : ((b + 1 : ℕ) : ℤ) - ((a + 1 : ℕ) : ℤ) = (b : ℤ) - a := by omega
      calc
        X q ^ (a + 1) * Y q ^ (b + 1)
            = (X q * Y q) * (X q ^ a * Y q ^ b) := by ring
        _ = algebraMap B (SlabAlgebra B q) q *
              (algebraMap B (SlabAlgebra B q) (q ^ min a b) * Z q ((b : ℤ) - a)) := by
              rw [X_mul_Y, ih b]
        _ = algebraMap B (SlabAlgebra B q) (q ^ min (a + 1) (b + 1)) *
              Z q (((b + 1 : ℕ) : ℤ) - ((a + 1 : ℕ) : ℤ)) := by
              rw [Nat.succ_min_succ, pow_succ', map_mul, mul_assoc, hsub]

/-- **Product formula for the normal-form basis of a slab algebra.** For all `n, m : ℤ` and
`r = (|n| + |m| - |n + m|) / 2`, `Z q n * Z q m = q^r • Z q (n + m)`. -/
theorem Z_mul (q : B) (n m : ℤ) :
    let r := (n.natAbs + m.natAbs - (n + m).natAbs) / 2
    Z q n * Z q m = algebraMap B (SlabAlgebra B q) (q ^ r) * Z q (n + m) := by
  dsimp only
  by_cases hn : n < 0 <;> by_cases hm : m < 0
  · have hnm : n + m < 0 := by omega
    have hr : (n.natAbs + m.natAbs - (n + m).natAbs) / 2 = 0 := by omega
    have habs : (n + m).natAbs = n.natAbs + m.natAbs := by omega
    rw [Z_of_lt_zero q hn, Z_of_lt_zero q hm, Z_of_lt_zero q hnm, hr, habs, pow_zero, map_one,
      one_mul, pow_add]
  · have hm' : 0 ≤ m := not_lt.mp hm
    have hr : min n.natAbs m.natAbs = (n.natAbs + m.natAbs - (n + m).natAbs) / 2 := by omega
    have hdiff : (m.natAbs : ℤ) - (n.natAbs : ℤ) = n + m := by omega
    rw [Z_of_lt_zero q hn, Z_of_nonneg q hm', X_pow_mul_Y_pow, hr, hdiff]
  · have hn' : 0 ≤ n := not_lt.mp hn
    have hr : min m.natAbs n.natAbs = (n.natAbs + m.natAbs - (n + m).natAbs) / 2 := by omega
    have hdiff : (n.natAbs : ℤ) - (m.natAbs : ℤ) = n + m := by omega
    rw [Z_of_nonneg q hn', Z_of_lt_zero q hm, mul_comm, X_pow_mul_Y_pow, hr, hdiff]
  · have hn' : 0 ≤ n := not_lt.mp hn
    have hm' : 0 ≤ m := not_lt.mp hm
    have hnm : 0 ≤ n + m := by omega
    have hr : (n.natAbs + m.natAbs - (n + m).natAbs) / 2 = 0 := by omega
    have habs : (n + m).natAbs = n.natAbs + m.natAbs := by omega
    rw [Z_of_nonneg q hn', Z_of_nonneg q hm', Z_of_nonneg q hnm, hr, habs, pow_zero, map_one,
      one_mul, pow_add]

/-! ### Normal-form basis and freeness -/

/-- Monomial reduction map `B[X, Y] →ₗ[B] (ℤ →₀ B)` sending `b X^i Y^j` to
`b q^{\min(i, j)} e_{j - i}`. -/
private def reducePoly (q : B) : MvPolynomial SlabVar B →ₗ[B] (ℤ →₀ B) :=
  (Finsupp.lsum B fun d : SlabVar →₀ ℕ =>
    (Finsupp.lsingle ((d SlabVar.Y : ℤ) - (d SlabVar.X : ℤ))).comp
      (LinearMap.mulRight B (q ^ min (d SlabVar.X) (d SlabVar.Y)))).comp
    (AddMonoidAlgebra.coeffLinearEquiv B).toLinearMap

private theorem reducePoly_monomial (q : B) (d : SlabVar →₀ ℕ) (b : B) :
    reducePoly q (MvPolynomial.monomial d b) =
      Finsupp.single ((d SlabVar.Y : ℤ) - (d SlabVar.X : ℤ))
        (b * q ^ min (d SlabVar.X) (d SlabVar.Y)) := by
  simp [reducePoly, ← MvPolynomial.single_eq_monomial]

private theorem reducePoly_eq_zero_of_mem_slabIdeal (q : B) {p : MvPolynomial SlabVar B}
    (hp : p ∈ slabIdeal B q) : reducePoly q p = 0 := by
  rw [slabIdeal_def, Ideal.mem_span_singleton] at hp
  rcases hp with ⟨r, rfl⟩
  induction r using MvPolynomial.induction_on' with
  | monomial d b =>
    rw [sub_mul, ← pow_one (MvPolynomial.X SlabVar.X), ← pow_one (MvPolynomial.X SlabVar.Y),
      MvPolynomial.X_pow_eq_monomial, MvPolynomial.X_pow_eq_monomial,
      MvPolynomial.monomial_mul_monomial, MvPolynomial.monomial_mul_monomial,
      MvPolynomial.C_mul_monomial, map_sub, reducePoly_monomial, reducePoly_monomial]
    have hX : (Finsupp.single SlabVar.X 1 + Finsupp.single SlabVar.Y 1 + d :
          SlabVar →₀ ℕ) SlabVar.X = d SlabVar.X + 1 := by simp [add_comm]
    have hY : (Finsupp.single SlabVar.X 1 + Finsupp.single SlabVar.Y 1 + d :
          SlabVar →₀ ℕ) SlabVar.Y = d SlabVar.Y + 1 := by simp [add_comm]
    have hdiff : ((d SlabVar.Y + 1 : ℕ) : ℤ) - ((d SlabVar.X + 1 : ℕ) : ℤ) =
        (d SlabVar.Y : ℤ) - (d SlabVar.X : ℤ) := by omega
    rw [hX, hY, hdiff, Nat.succ_min_succ, pow_succ', one_mul, one_mul, ← mul_assoc,
      mul_comm b q, mul_assoc, sub_self]
  | add f g hf hg =>
    rw [mul_add, map_add, hf, hg, add_zero]

private def reduceQuot (q : B) : SlabAlgebra B q →ₗ[B] (ℤ →₀ B) where
  toFun := Quotient.lift (reducePoly q) fun a b hab => by
    have h : a - b ∈ slabIdeal B q :=
      (Submodule.quotientRel_def (slabIdeal B q)).mp hab
    have h0 := reducePoly_eq_zero_of_mem_slabIdeal q h
    exact sub_eq_zero.mp (by rwa [map_sub] at h0)
  map_add' u v := by
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective u
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective v
    exact (reducePoly q).map_add f g
  map_smul' c u := by
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective u
    exact (reducePoly q).map_smul c f

private theorem reduceQuot_mk (q : B) (p : MvPolynomial SlabVar B) :
    reduceQuot q (Ideal.Quotient.mk (slabIdeal B q) p) = reducePoly q p :=
  rfl

/-- Coordinate equivalence `SlabAlgebra B q ≃ₗ[B] (ℤ →₀ B)` sending `Z q n` to
`Finsupp.single n 1`. -/
private def slabReprEquiv (q : B) : SlabAlgebra B q ≃ₗ[B] (ℤ →₀ B) :=
  LinearEquiv.ofLinearMap
    (reduceQuot q)
    (Finsupp.linearCombination B (Z q))
    (by
      ext n a
      simp only [LinearMap.comp_apply, LinearMap.id_apply, Finsupp.lsingle_apply,
        Finsupp.linearCombination_single, one_smul]
      rcases lt_or_ge n 0 with hn | hn
      · rw [Z_of_lt_zero q hn, ← mk_X_eq_X, ← map_pow, MvPolynomial.X_pow_eq_monomial,
          reduceQuot_mk, reducePoly_monomial]
        simp [abs_of_neg hn]
      · rw [Z_of_nonneg q hn, ← mk_Y_eq_Y, ← map_pow, MvPolynomial.X_pow_eq_monomial,
          reduceQuot_mk, reducePoly_monomial]
        simp [abs_of_nonneg hn])
    (by
      refine LinearMap.ext fun u => ?_
      obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective u
      induction p using MvPolynomial.induction_on' with
      | monomial d b =>
        simp only [LinearMap.comp_apply, LinearMap.id_apply]
        have hpoly : MvPolynomial.monomial d b =
            MvPolynomial.C b *
              (MvPolynomial.X SlabVar.X ^ d SlabVar.X *
                MvPolynomial.X SlabVar.Y ^ d SlabVar.Y) := by
          have hd : Finsupp.single SlabVar.X (d SlabVar.X) +
              Finsupp.single SlabVar.Y (d SlabVar.Y) = d := by
            ext v
            cases v <;> simp
          rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.X_pow_eq_monomial,
            MvPolynomial.monomial_mul_monomial, MvPolynomial.C_mul_monomial, hd, mul_one, mul_one]
        have hmk : Ideal.Quotient.mk (slabIdeal B q) (MvPolynomial.monomial d b) =
            b • (X q ^ d SlabVar.X * Y q ^ d SlabVar.Y) := by
          rw [hpoly, map_mul, map_mul, map_pow, map_pow, mk_X_eq_X, mk_Y_eq_Y,
            ← Ideal.Quotient.algebraMap_eq, ← MvPolynomial.algebraMap_eq,
            ← IsScalarTower.algebraMap_apply B (MvPolynomial SlabVar B) (SlabAlgebra B q),
            ← Algebra.smul_def]
        rw [reduceQuot_mk, reducePoly_monomial, Finsupp.linearCombination_single, hmk,
          X_pow_mul_Y_pow, ← Algebra.smul_def, smul_smul]
      | add f g hf hg =>
        rw [map_add]
        simpa only [map_add] using congrArg₂ (· + ·) hf hg)

/-- **Slab normal form**: `SlabAlgebra B q` is a free `B`-module with integer-indexed basis
`n ↦ Z q n`, corresponding to `{X^a | a ≥ 0} ∪ {Y^a | a ≥ 1}` (`Z q (-a) = X^a`, `Z q 0 = 1`,
and `Z q a = Y^a`). -/
def slabBasis (q : B) : Module.Basis ℤ B (SlabAlgebra B q) :=
  Module.Basis.ofRepr (slabReprEquiv q)

@[simp]
theorem slabBasis_apply (q : B) (n : ℤ) : slabBasis q n = Z q n := by
  simp [slabBasis, Module.Basis.coe_ofRepr, slabReprEquiv]

@[simp]
theorem coe_slabBasis (q : B) : ⇑(slabBasis q) = Z q :=
  funext (slabBasis_apply q)

@[simp]
theorem slabBasis_repr_Z (q : B) (n : ℤ) :
    (slabBasis q).repr (Z q n) = Finsupp.single n 1 := by
  rw [← slabBasis_apply, Module.Basis.repr_self]

@[simp]
theorem slabBasis_repr_algebraMap (q : B) (b : B) :
    (slabBasis q).repr (algebraMap B (SlabAlgebra B q) b) = Finsupp.single 0 b := by
  rw [← mul_one (algebraMap B (SlabAlgebra B q) b), ← Algebra.smul_def, ← Z_zero q,
    map_smul, slabBasis_repr_Z, Finsupp.smul_single, smul_eq_mul, mul_one]

@[simp]
theorem slabBasis_repr_X (q : B) :
    (slabBasis q).repr (X q) = Finsupp.single (-1) 1 := by
  rw [← Z_neg_one q, slabBasis_repr_Z]

@[simp]
theorem slabBasis_repr_Y (q : B) :
    (slabBasis q).repr (Y q) = Finsupp.single 1 1 := by
  rw [← Z_one q, slabBasis_repr_Z]

theorem slabBasis_repr_mk_monomial (q : B) (d : SlabVar →₀ ℕ) (b : B) :
    (slabBasis q).repr (Ideal.Quotient.mk (slabIdeal B q) (MvPolynomial.monomial d b)) =
      Finsupp.single ((d SlabVar.Y : ℤ) - (d SlabVar.X : ℤ))
        (b * q ^ min (d SlabVar.X) (d SlabVar.Y)) :=
  reducePoly_monomial q d b

/-- Every slab algebra is free as a module over its base ring `B` (and hence flat over `B`). -/
instance instModuleFree (q : B) : Module.Free B (SlabAlgebra B q) :=
  Module.Free.of_basis (slabBasis q)

/-- The structure map `B →+* SlabAlgebra B q` is injective for every `B` and `q`. -/
theorem algebraMap_injective (q : B) : Function.Injective (algebraMap B (SlabAlgebra B q)) := by
  intro a b hab
  have h := congrArg (fun u => (slabBasis q).repr u 0) hab
  simpa using h

theorem nontrivial_iff (q : B) : Nontrivial (SlabAlgebra B q) ↔ Nontrivial B :=
  ⟨fun _ => (algebraMap B (SlabAlgebra B q)).domain_nontrivial,
    fun _ => (algebraMap_injective q).nontrivial⟩

instance instNontrivial [Nontrivial B] (q : B) : Nontrivial (SlabAlgebra B q) :=
  (nontrivial_iff q).mpr ‹_›

/-! ### Normal-weight `ℤ`-grading -/

/-- The normal-weight `n` piece `B ∙ Z q n` of `SlabAlgebra B q`, giving `X` weight `-1`, `Y`
weight `1` and scalars in `B` weight `0`. -/
def weightSubmodule (q : B) (n : ℤ) : Submodule B (SlabAlgebra B q) :=
  Submodule.span B {Z q n}

theorem mem_weightSubmodule_iff (q : B) (n : ℤ) (u : SlabAlgebra B q) :
    u ∈ weightSubmodule q n ↔ ∃ b : B, b • Z q n = u :=
  Submodule.mem_span_singleton

theorem Z_mem_weightSubmodule (q : B) (n : ℤ) : Z q n ∈ weightSubmodule q n :=
  Submodule.mem_span_singleton_self (Z q n)

theorem X_mem_weightSubmodule (q : B) : X q ∈ weightSubmodule q (-1) := by
  simpa using Z_mem_weightSubmodule q (-1)

theorem Y_mem_weightSubmodule (q : B) : Y q ∈ weightSubmodule q 1 := by
  simpa using Z_mem_weightSubmodule q 1

theorem algebraMap_mem_weightSubmodule_zero (q : B) (b : B) :
    algebraMap B (SlabAlgebra B q) b ∈ weightSubmodule q 0 := by
  refine (mem_weightSubmodule_iff q 0 _).mpr ⟨b, ?_⟩
  rw [Z_zero]
  exact (Algebra.algebraMap_eq_smul_one b).symm

instance instGradedMonoidWeightSubmodule (q : B) :
    SetLike.GradedMonoid (weightSubmodule q) where
  one_mem := by simpa using Z_mem_weightSubmodule q 0
  mul_mem i j u v hu hv := by
    obtain ⟨a, rfl⟩ := (mem_weightSubmodule_iff q i u).mp hu
    obtain ⟨b, rfl⟩ := (mem_weightSubmodule_iff q j v).mp hv
    refine (mem_weightSubmodule_iff q (i + j) _).mpr
      ⟨a * b * q ^ ((i.natAbs + j.natAbs - (i + j).natAbs) / 2), ?_⟩
    rw [smul_mul_smul_comm, Z_mul, ← Algebra.smul_def, smul_smul]

theorem weightSubmodule_isInternal (q : B) : DirectSum.IsInternal (weightSubmodule q) := by
  have h := (slabBasis q).isInternal_span_image_fiber id
  have heq :
      (fun c => Submodule.span B (⇑(slabBasis q) '' {i | id i = c})) = weightSubmodule q := by
    ext c u
    simp [weightSubmodule]
  rwa [heq] at h

/-- The normal-weight `ℤ`-decomposition of `SlabAlgebra B q`. -/
instance instDecompositionWeightSubmodule (q : B) :
    DirectSum.Decomposition (weightSubmodule q) :=
  (weightSubmodule_isInternal q).chooseDecomposition

/-- `SlabAlgebra B q` is a `ℤ`-graded `B`-algebra with `n`-th piece `B ∙ Z q n`. -/
instance instGradedAlgebraWeightSubmodule (q : B) :
    GradedAlgebra (weightSubmodule q) :=
  { instGradedMonoidWeightSubmodule q, instDecompositionWeightSubmodule q with }

@[simp]
theorem coe_decompose_weightSubmodule (q : B) (u : SlabAlgebra B q) (n : ℤ) :
    (DirectSum.decompose (weightSubmodule q) u n : SlabAlgebra B q) =
      ((slabBasis q).repr u n) • Z q n := by
  induction u using DirectSum.Decomposition.inductionOn (weightSubmodule q) with
  | zero => simp
  | add x y hx hy => simp [hx, hy, add_smul]
  | @homogeneous m x =>
    obtain ⟨b, hb⟩ := (mem_weightSubmodule_iff q m x.1).mp x.2
    rw [DirectSum.decompose_of_mem (weightSubmodule q) x.2, DirectSum.coe_of_apply]
    by_cases h : m = n
    · subst h
      simp only [↓reduceIte]
      rw [← hb, map_smul, slabBasis_repr_Z]
      simp
    · simp only [h, ↓reduceIte, ZeroMemClass.coe_zero]
      rw [← hb, map_smul, slabBasis_repr_Z]
      simp [Finsupp.single_eq_of_ne (Ne.symm h)]

/-! ### Functoriality in `(B, q)` -/

/-- Functorial ring homomorphism `SlabAlgebra B q →+* SlabAlgebra B' q'` along a ring homomorphism
`φ : B →+* B'` sending `q` to `q'`. -/
def map (φ : B →+* B') {q : B} {q' : B'} (hq : φ q = q') :
    SlabAlgebra B q →+* SlabAlgebra B' q' :=
  liftRingHom ((algebraMap B' (SlabAlgebra B' q')).comp φ) (X q') (Y q') (by
    simp [hq])

@[simp]
theorem map_algebraMap (φ : B →+* B') {q : B} {q' : B'} (hq : φ q = q') (b : B) :
    map φ hq (algebraMap B (SlabAlgebra B q) b) = algebraMap B' (SlabAlgebra B' q') (φ b) :=
  liftRingHom_algebraMap _ _ _ _ b

@[simp]
theorem map_X (φ : B →+* B') {q : B} {q' : B'} (hq : φ q = q') :
    map φ hq (X q) = X q' :=
  liftRingHom_X _ _ _ _

@[simp]
theorem map_Y (φ : B →+* B') {q : B} {q' : B'} (hq : φ q = q') :
    map φ hq (Y q) = Y q' :=
  liftRingHom_Y _ _ _ _

@[simp]
theorem map_Z (φ : B →+* B') {q : B} {q' : B'} (hq : φ q = q') (n : ℤ) :
    map φ hq (Z q n) = Z q' n := by
  rw [map, liftRingHom_Z, Z_def]

@[simp]
theorem slabBasis_repr_map (φ : B →+* B') {q : B} {q' : B'} (hq : φ q = q')
    (u : SlabAlgebra B q) (n : ℤ) :
    (slabBasis q').repr (map φ hq u) n = φ ((slabBasis q).repr u n) := by
  induction u using DirectSum.Decomposition.inductionOn (weightSubmodule q) with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | @homogeneous m x =>
    obtain ⟨b, hb⟩ := (mem_weightSubmodule_iff q m x.1).mp x.2
    rw [← hb, Algebra.smul_def b (Z q m), map_mul, map_algebraMap, map_Z,
      ← Algebra.smul_def (φ b) (Z q' m), ← Algebra.smul_def b (Z q m),
      map_smul, map_smul, slabBasis_repr_Z, slabBasis_repr_Z]
    by_cases h : m = n
    · subst h; simp
    · simp [Finsupp.single_eq_of_ne (Ne.symm h)]

@[simp]
theorem map_id (q : B) : map (RingHom.id B) (rfl : RingHom.id B q = q) = RingHom.id _ :=
  ringHom_ext (fun _ => by simp) (by simp) (by simp)

theorem map_comp (ψ : B' →+* B'') (φ : B →+* B') {q : B} {q' : B'} {q'' : B''}
    (hq : φ q = q') (hq' : ψ q' = q'') :
    (map ψ hq').comp (map φ hq) = map (ψ.comp φ) (by rw [RingHom.comp_apply, hq, hq']) :=
  ringHom_ext (fun _ => by simp) (by simp) (by simp)

/-- Functorial `R`-algebra homomorphism `SlabAlgebra B q →ₐ[R] SlabAlgebra B' q'` along an
`R`-algebra homomorphism `φ : B →ₐ[R] B'` sending `q` to `q'`. -/
def mapAlgHom [CommSemiring R] [Algebra R B] [Algebra R B']
    (φ : B →ₐ[R] B') {q : B} {q' : B'} (hq : φ q = q') :
    SlabAlgebra B q →ₐ[R] SlabAlgebra B' q' where
  toRingHom := map φ.toRingHom hq
  commutes' r := by
    simp [IsScalarTower.algebraMap_apply R B (SlabAlgebra B q),
      IsScalarTower.algebraMap_apply R B' (SlabAlgebra B' q')]

@[simp]
theorem coe_mapAlgHom [CommSemiring R] [Algebra R B] [Algebra R B']
    (φ : B →ₐ[R] B') {q : B} {q' : B'} (hq : φ q = q') :
    (mapAlgHom φ hq : SlabAlgebra B q →+* SlabAlgebra B' q') = map φ.toRingHom hq :=
  (rfl)

theorem mapAlgHom_apply [CommSemiring R] [Algebra R B] [Algebra R B']
    (φ : B →ₐ[R] B') {q : B} {q' : B'} (hq : φ q = q') (u : SlabAlgebra B q) :
    mapAlgHom φ hq u = map φ.toRingHom hq u :=
  (rfl)

@[simp]
theorem mapAlgHom_algebraMap [CommSemiring R] [Algebra R B] [Algebra R B']
    (φ : B →ₐ[R] B') {q : B} {q' : B'} (hq : φ q = q') (b : B) :
    mapAlgHom φ hq (algebraMap B (SlabAlgebra B q) b) =
      algebraMap B' (SlabAlgebra B' q') (φ b) :=
  map_algebraMap φ.toRingHom hq b

@[simp]
theorem mapAlgHom_X [CommSemiring R] [Algebra R B] [Algebra R B']
    (φ : B →ₐ[R] B') {q : B} {q' : B'} (hq : φ q = q') :
    mapAlgHom φ hq (X q) = X q' :=
  map_X φ.toRingHom hq

@[simp]
theorem mapAlgHom_Y [CommSemiring R] [Algebra R B] [Algebra R B']
    (φ : B →ₐ[R] B') {q : B} {q' : B'} (hq : φ q = q') :
    mapAlgHom φ hq (Y q) = Y q' :=
  map_Y φ.toRingHom hq

@[simp]
theorem mapAlgHom_Z [CommSemiring R] [Algebra R B] [Algebra R B']
    (φ : B →ₐ[R] B') {q : B} {q' : B'} (hq : φ q = q') (n : ℤ) :
    mapAlgHom φ hq (Z q n) = Z q' n :=
  map_Z φ.toRingHom hq n

/-- Functorial `R`-algebra equivalence `SlabAlgebra B q ≃ₐ[R] SlabAlgebra B' q'` along an
`R`-algebra equivalence `φ : B ≃ₐ[R] B'` sending `q` to `q'`. -/
def mapAlgEquiv [CommSemiring R] [Algebra R B] [Algebra R B']
    (φ : B ≃ₐ[R] B') {q : B} {q' : B'} (hq : φ q = q') :
    SlabAlgebra B q ≃ₐ[R] SlabAlgebra B' q' :=
  AlgEquiv.ofAlgHom
    (mapAlgHom (φ : B →ₐ[R] B') (by simpa using hq))
    (mapAlgHom (φ.symm : B' →ₐ[R] B) (by simpa using φ.symm_apply_eq.mpr hq.symm))
    (algHom_ext_of_algebra (fun b => by simp) (by simp) (by simp))
    (algHom_ext_of_algebra (fun b => by simp) (by simp) (by simp))

@[simp]
theorem mapAlgEquiv_apply [CommSemiring R] [Algebra R B] [Algebra R B']
    (φ : B ≃ₐ[R] B') {q : B} {q' : B'} (hq : φ q = q') (u : SlabAlgebra B q) :
    mapAlgEquiv φ hq u = map φ.toRingHom hq u :=
  (rfl)

@[simp]
theorem mapAlgEquiv_symm [CommSemiring R] [Algebra R B] [Algebra R B']
    (φ : B ≃ₐ[R] B') {q : B} {q' : B'} (hq : φ q = q') :
    (mapAlgEquiv φ hq).symm = mapAlgEquiv φ.symm (φ.symm_apply_eq.mpr hq.symm) :=
  (rfl)

end SlabAlgebra

end TauCeti

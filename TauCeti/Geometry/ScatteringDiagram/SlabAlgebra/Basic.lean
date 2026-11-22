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
public import TauCeti.RingTheory.Node.Basic
public import TauCeti.RingTheory.Node.Flat
import TauCeti.Algebra.DirectSum.Internal

/-!
# Normal-form basis and grading for nodal slab algebras

For a commutative ring `B` and an element `q ∈ B`, the nodal algebra
`NodeAlgebra B q = B[x, y] / (x y - q)` models the local coordinate ring across a codimension-one
slab in log Calabi–Yau mirror symmetry and wall-crossing diagrams (taking `B = S[Λ_b]` for a
tangential lattice `Λ_b` and `q ∈ S[Λ_b]`). Here `coord q 0` and `coord q 1` are the incoming
monomials from the two adjacent chambers whose product equals the tangential slab function `q`.

Every mixed monomial `(coord q 0)^a (coord q 1)^b` reduces modulo `x y - q` to `q^{\min(a, b)}`
times a pure power of `coord q 0` or `coord q 1`. Indexing these pure powers by `n ∈ ℤ` via
`Z q n = (coord q 0)^{-n}` for `n < 0` and `Z q n = (coord q 1)^n` for `n ≥ 0` (so `Z q 0 = 1`)
yields:

* a free `B`-basis `NodeAlgebra.slabBasis q : Module.Basis ℤ B (NodeAlgebra B q)` for arbitrary
  `q` (without any regularity or domain assumption on `B` or `q`), making the structure map
  `algebraMap B (NodeAlgebra B q)` injective;
* the multiplication law `Z q n * Z q m = q^r • Z q (n + m)` with
  `r = (|n| + |m| - |n + m|) / 2`;
* the normal-weight `ℤ`-grading `NodeAlgebra.weightSubmodule q` in which `coord q 0` has weight
  `-1`, `coord q 1` has weight `1`, `B` has weight `0`, and the weight-`n` piece is `B ∙ Z q n`;
* general ring and algebra homomorphisms `NodeAlgebra.liftRingHom`, `NodeAlgebra.mapRingHom`,
  `NodeAlgebra.mapAlgHom`, and `NodeAlgebra.mapAlgEquiv` extending `NodeAlgebra.lift` and
  `NodeAlgebra.map` to arbitrary coefficient ring maps sending `q` to `q'`.

## Main definitions and results

* `TauCeti.NodeAlgebra.ringHom_ext`, `TauCeti.NodeAlgebra.algHom_ext_of_algebra`,
  `TauCeti.NodeAlgebra.liftRingHom`, `TauCeti.NodeAlgebra.liftEquiv`: ring-homomorphism and
  tower-algebra universal properties for `NodeAlgebra B q`.
* `TauCeti.NodeAlgebra.Z`, `TauCeti.NodeAlgebra.Z_mul`: the integer-indexed normal-form elements
  and their product formula.
* `TauCeti.NodeAlgebra.slabBasis`, `TauCeti.NodeAlgebra.induction_linear`,
  `TauCeti.NodeAlgebra.algebraMap_injective`: the `B`-basis `n ↦ Z q n`, linear induction along
  it, and injectivity of the structure map.
* `TauCeti.NodeAlgebra.weightSubmodule`: the normal-weight `ℤ`-graded `B`-algebra decomposition.
* `TauCeti.NodeAlgebra.mapRingHom`, `TauCeti.NodeAlgebra.mapAlgHom`,
  `TauCeti.NodeAlgebra.mapAlgEquiv`: functoriality in `(B, q)` along general coefficient maps.

## References

* M. Gross and B. Siebert, *An Invitation to Toric Degenerations*, §2.3, arXiv:0808.2749v2.
* M. Gross, P. Hacking, and B. Siebert, *Theta functions on varieties with effective
  anti-canonical class*, §3.1, arXiv:1601.07081v4.
-/

public section

noncomputable section

namespace TauCeti

namespace NodeAlgebra

variable {B B' B'' C R : Type*} [CommRing B] [CommRing B'] [CommRing B'']

/-- Two ring homomorphisms out of `NodeAlgebra B q` agree when they agree on `B`, `coord q 0`,
and `coord q 1`. -/
theorem ringHom_ext [Semiring C] {q : B} {f g : NodeAlgebra B q →+* C}
    (hB : ∀ b : B, f (algebraMap B (NodeAlgebra B q) b) = g (algebraMap B (NodeAlgebra B q) b))
    (h0 : f (coord q 0) = g (coord q 0)) (h1 : f (coord q 1) = g (coord q 1)) : f = g := by
  ext u
  obtain ⟨p, rfl⟩ := mk_surjective q u
  induction p using MvPolynomial.induction_on with
  | C b =>
    have hb := hB b
    rwa [← (mk q).commutes b] at hb
  | add p₁ p₂ hp₁ hp₂ => simp only [map_add, hp₁, hp₂]
  | mul_X p i hp =>
    simp only [map_mul, mk_X, hp]
    fin_cases i <;> simp [h0, h1]

/-- Two `R`-algebra homomorphisms out of `NodeAlgebra B q` agree when they agree on `B`,
`coord q 0`, and `coord q 1`. -/
theorem algHom_ext_of_algebra [CommSemiring R] [CommSemiring C] [Algebra R B] [Algebra R C]
    {q : B} {f g : NodeAlgebra B q →ₐ[R] C}
    (hB : ∀ b : B, f (algebraMap B (NodeAlgebra B q) b) = g (algebraMap B (NodeAlgebra B q) b))
    (h0 : f (coord q 0) = g (coord q 0)) (h1 : f (coord q 1) = g (coord q 1)) : f = g :=
  AlgHom.toRingHom_injective (ringHom_ext hB h0 h1)

/-- Universal property of `NodeAlgebra B q` for ring homomorphisms: a ring map `φ : B →+* C` and
elements `x, y : C` satisfying `x * y = φ q` determine a unique ring homomorphism
`NodeAlgebra B q →+* C`. -/
def liftRingHom [CommSemiring C] {q : B} (φ : B →+* C) (x y : C) (hxy : x * y = φ q) :
    NodeAlgebra B q →+* C :=
  letI : Algebra B C := φ.toAlgebra
  (lift q x y hxy).toRingHom

@[simp] theorem liftRingHom_algebraMap [CommSemiring C] {q : B} (φ : B →+* C) (x y : C)
    (hxy : x * y = φ q) (b : B) :
    liftRingHom φ x y hxy (algebraMap B (NodeAlgebra B q) b) = φ b := by
  let _ : Algebra B C := φ.toAlgebra
  exact (lift q x y hxy).commutes b

@[simp] theorem liftRingHom_coord [CommSemiring C] {q : B} (φ : B →+* C) (x y : C)
    (hxy : x * y = φ q) (i : Fin 2) :
    liftRingHom φ x y hxy (coord q i) = ![x, y] i := by
  let _ : Algebra B C := φ.toAlgebra
  exact lift_coord q x y hxy i

theorem liftRingHom_coord_zero [CommSemiring C] {q : B} (φ : B →+* C) (x y : C)
    (hxy : x * y = φ q) : liftRingHom φ x y hxy (coord q 0) = x := by
  simp

theorem liftRingHom_coord_one [CommSemiring C] {q : B} (φ : B →+* C) (x y : C)
    (hxy : x * y = φ q) : liftRingHom φ x y hxy (coord q 1) = y := by
  simp

/-- Equivalence between `B`-algebra homomorphisms `NodeAlgebra B q →ₐ[B] C` and pairs `(x, y)`
in `C` with `x * y = algebraMap B C q`. -/
def liftEquiv (q : B) (C : Type*) [CommSemiring C] [Algebra B C] :
    (NodeAlgebra B q →ₐ[B] C) ≃ { p : C × C // p.1 * p.2 = algebraMap B C q } where
  toFun f := ⟨(f (coord q 0), f (coord q 1)), by
    rw [← map_mul, coord_zero_mul_coord_one, AlgHom.commutes]⟩
  invFun p := lift q p.val.1 p.val.2 p.property
  left_inv f := hom_ext q (lift_coord_zero q _ _ _) (lift_coord_one q _ _ _)
  right_inv p := Subtype.ext (Prod.ext (lift_coord_zero q _ _ _) (lift_coord_one q _ _ _))

@[simp] theorem liftEquiv_apply_fst [CommSemiring C] [Algebra B C] (q : B)
    (f : NodeAlgebra B q →ₐ[B] C) : ((liftEquiv q C f : C × C).1) = f (coord q 0) := (rfl)

@[simp] theorem liftEquiv_apply_snd [CommSemiring C] [Algebra B C] (q : B)
    (f : NodeAlgebra B q →ₐ[B] C) : ((liftEquiv q C f : C × C).2) = f (coord q 1) := (rfl)

@[simp] theorem liftEquiv_symm_apply [CommSemiring C] [Algebra B C] (q : B)
    (p : { p : C × C // p.1 * p.2 = algebraMap B C q }) :
    (liftEquiv q C).symm p = lift q p.val.1 p.val.2 p.property := (rfl)

/-! ### Normal-form elements `Z_n` and multiplication -/

/-- The integer-indexed normal-form elements of `NodeAlgebra B q`: `Z q n = (coord q 0)^{-n}` for
`n < 0`, `Z q 0 = 1`, and `Z q n = (coord q 1)^n` for `n > 0`. -/
def Z (q : B) (n : ℤ) : NodeAlgebra B q :=
  if n < 0 then coord q 0 ^ n.natAbs else coord q 1 ^ n.natAbs

theorem Z_def (q : B) (n : ℤ) :
    Z q n = if n < 0 then coord q 0 ^ n.natAbs else coord q 1 ^ n.natAbs := (rfl)

theorem Z_of_lt_zero (q : B) {n : ℤ} (hn : n < 0) : Z q n = coord q 0 ^ n.natAbs :=
  ite_eq_left hn

theorem Z_of_nonneg (q : B) {n : ℤ} (hn : 0 ≤ n) : Z q n = coord q 1 ^ n.natAbs :=
  ite_eq_right (not_lt.mpr hn)

@[simp] theorem Z_zero (q : B) : Z q 0 = 1 := by simp [Z_def]
@[simp] theorem Z_one (q : B) : Z q 1 = coord q 1 := by simp [Z_def]
@[simp] theorem Z_neg_one (q : B) : Z q (-1) = coord q 0 := by simp [Z_def]

@[simp] theorem Z_natCast (q : B) (a : ℕ) : Z q (a : ℤ) = coord q 1 ^ a := by
  rw [Z_of_nonneg q (Int.natCast_nonneg a), Int.natAbs_natCast]

@[simp] theorem Z_neg_natCast (q : B) (a : ℕ) : Z q (-(a : ℤ)) = coord q 0 ^ a := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  · rw [Z_of_lt_zero q (by omega), Int.natAbs_neg, Int.natAbs_natCast]

@[simp] theorem liftRingHom_Z [CommSemiring C] {q : B} (φ : B →+* C) (x y : C)
    (hxy : x * y = φ q) (n : ℤ) :
    liftRingHom φ x y hxy (Z q n) = if n < 0 then x ^ n.natAbs else y ^ n.natAbs := by
  rw [Z_def]; split_ifs <;> simp

@[simp] theorem lift_Z [CommSemiring C] [Algebra B C] (q : B) (x y : C)
    (hxy : x * y = algebraMap B C q) (n : ℤ) :
    lift q x y hxy (Z q n) = if n < 0 then x ^ n.natAbs else y ^ n.natAbs := by
  rw [Z_def]; split_ifs <;> simp

/-- A mixed monomial `(coord q 0)^a (coord q 1)^b` reduces in `NodeAlgebra B q` to
`q^{\min(a, b)} Z_{b - a}`. -/
theorem coord_zero_pow_mul_coord_one_pow (q : B) (a b : ℕ) :
    coord q 0 ^ a * coord q 1 ^ b =
      algebraMap B (NodeAlgebra B q) (q ^ min a b) * Z q ((b : ℤ) - a) := by
  induction a generalizing b with
  | zero => simp
  | succ a ih =>
    cases b with
    | zero =>
      rw [pow_zero, mul_one, Nat.min_zero, pow_zero, map_one, one_mul, Nat.cast_zero, zero_sub,
        Z_neg_natCast]
    | succ b =>
      calc coord q 0 ^ (a + 1) * coord q 1 ^ (b + 1)
          = (coord q 0 * coord q 1) * (coord q 0 ^ a * coord q 1 ^ b) := by ring
        _ = algebraMap B (NodeAlgebra B q) (q ^ min (a + 1) (b + 1)) *
              Z q (((b + 1 : ℕ) : ℤ) - ((a + 1 : ℕ) : ℤ)) := by
            rw [coord_zero_mul_coord_one, ih b, Nat.succ_min_succ, pow_succ', map_mul, mul_assoc,
              Nat.cast_succ, Nat.cast_succ, add_sub_add_right_eq_sub]

/-- **Product formula for the normal-form basis of a slab algebra.** For all `n, m : ℤ` and
`r = (|n| + |m| - |n + m|) / 2`, `Z q n * Z q m = q^r • Z q (n + m)`. -/
theorem Z_mul (q : B) (n m : ℤ) :
    let r := (n.natAbs + m.natAbs - (n + m).natAbs) / 2
    Z q n * Z q m = algebraMap B (NodeAlgebra B q) (q ^ r) * Z q (n + m) := by
  dsimp only
  by_cases hn : n < 0 <;> by_cases hm : m < 0
  · rw [Z_of_lt_zero q hn, Z_of_lt_zero q hm, Z_of_lt_zero q (by omega),
      Int.natAbs_add_of_nonpos hn.le hm.le, Nat.sub_self, Nat.zero_div,
      pow_zero, map_one, one_mul, pow_add]
  · rw [Z_of_lt_zero q hn, Z_of_nonneg q (not_lt.mp hm), coord_zero_pow_mul_coord_one_pow]
    congr 1 <;> [congr 2; congr 1] <;> omega
  · rw [Z_of_nonneg q (not_lt.mp hn), Z_of_lt_zero q hm, mul_comm,
      coord_zero_pow_mul_coord_one_pow]
    congr 1 <;> [congr 2; congr 1] <;> omega
  · rw [Z_of_nonneg q (not_lt.mp hn), Z_of_nonneg q (not_lt.mp hm),
      Z_of_nonneg q (by omega), Int.natAbs_add_of_nonneg (not_lt.mp hn) (not_lt.mp hm),
      Nat.sub_self, Nat.zero_div, pow_zero, map_one, one_mul, pow_add]

/-! ### Normal-form basis and injectivity of the structure map -/

/-- Monomial reduction map `B[x, y] →ₗ[B] (ℤ →₀ B)` sending `b x^i y^j` to
`b q^{\min(i, j)} e_{j - i}`. -/
private def reducePoly (q : B) : MvPolynomial (Fin 2) B →ₗ[B] (ℤ →₀ B) :=
  (Finsupp.lsum B fun d : Fin 2 →₀ ℕ =>
    (Finsupp.lsingle ((d 1 : ℤ) - (d 0 : ℤ))).comp
      (LinearMap.mulRight B (q ^ min (d 0) (d 1)))).comp
    (AddMonoidAlgebra.coeffLinearEquiv B).toLinearMap

private theorem reducePoly_monomial (q : B) (d : Fin 2 →₀ ℕ) (b : B) :
    reducePoly q (MvPolynomial.monomial d b) =
      Finsupp.single ((d 1 : ℤ) - (d 0 : ℤ)) (b * q ^ min (d 0) (d 1)) := by
  simp [reducePoly, ← MvPolynomial.single_eq_monomial]

private theorem reducePoly_eq_zero_of_mem_ideal (q : B) {p : MvPolynomial (Fin 2) B}
    (hp : p ∈ Ideal.span {MvPolynomial.X (0 : Fin 2) * MvPolynomial.X 1 - MvPolynomial.C q}) :
    reducePoly q p = 0 := by
  rw [Ideal.mem_span_singleton] at hp
  rcases hp with ⟨r, rfl⟩
  induction r using MvPolynomial.induction_on' with
  | monomial d b =>
    rw [sub_mul, ← pow_one (MvPolynomial.X (0 : Fin 2)),
      ← pow_one (MvPolynomial.X (1 : Fin 2)), MvPolynomial.X_pow_eq_monomial,
      MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul_monomial,
      MvPolynomial.monomial_mul_monomial, MvPolynomial.C_mul_monomial, map_sub,
      reducePoly_monomial, reducePoly_monomial]
    have h0 : (Finsupp.single (0 : Fin 2) 1 + Finsupp.single (1 : Fin 2) 1 + d : Fin 2 →₀ ℕ) 0 =
        d 0 + 1 := by simp [add_comm]
    have h1 : (Finsupp.single (0 : Fin 2) 1 + Finsupp.single (1 : Fin 2) 1 + d : Fin 2 →₀ ℕ) 1 =
        d 1 + 1 := by simp [add_comm]
    rw [h0, h1, Nat.cast_succ, Nat.cast_succ, add_sub_add_right_eq_sub, Nat.succ_min_succ,
      pow_succ', one_mul, one_mul, ← mul_assoc, mul_comm b q, mul_assoc, sub_self]
  | add f g hf hg => rw [mul_add, map_add, hf, hg, add_zero]

private theorem ker_mk_toLinearMap_le (q : B) :
    LinearMap.ker (mk q).toLinearMap ≤ LinearMap.ker (reducePoly q) := by
  intro p hp
  rw [LinearMap.mem_ker, AlgHom.toLinearMap_apply] at hp
  have hp' : p ∈ RingHom.ker (mk q : MvPolynomial (Fin 2) B →+* NodeAlgebra B q) := hp
  rw [ker_mk] at hp'
  exact LinearMap.mem_ker.mpr (reducePoly_eq_zero_of_mem_ideal q hp')

private def reduceQuot (q : B) : NodeAlgebra B q →ₗ[B] (ℤ →₀ B) :=
  ((LinearMap.ker (mk q).toLinearMap).liftQ (reducePoly q) (ker_mk_toLinearMap_le q)).comp
    ((mk q).toLinearMap.quotKerEquivOfSurjective (mk_surjective q)).symm.toLinearMap

private theorem reduceQuot_mk (q : B) (p : MvPolynomial (Fin 2) B) :
    reduceQuot q (mk q p) = reducePoly q p := by
  rw [reduceQuot, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
  have h : ((mk q).toLinearMap.quotKerEquivOfSurjective (mk_surjective q)).symm (mk q p) =
      Submodule.Quotient.mk p := by
    apply ((mk q).toLinearMap.quotKerEquivOfSurjective (mk_surjective q)).injective
    simp [LinearMap.quotKerEquivOfSurjective]
  rw [h, Submodule.liftQ_apply]

/-- Coordinate equivalence `NodeAlgebra B q ≃ₗ[B] (ℤ →₀ B)` sending `Z q n` to
`Finsupp.single n 1`. -/
private def slabReprEquiv (q : B) : NodeAlgebra B q ≃ₗ[B] (ℤ →₀ B) :=
  LinearEquiv.ofLinearMap (reduceQuot q) (Finsupp.linearCombination B (Z q))
    (by
      ext n a
      simp only [LinearMap.comp_apply, LinearMap.id_apply, Finsupp.lsingle_apply,
        Finsupp.linearCombination_single, one_smul]
      rcases lt_or_ge n 0 with hn | hn
      · rw [Z_of_lt_zero q hn, ← mk_X q 0, ← map_pow, MvPolynomial.X_pow_eq_monomial,
          reduceQuot_mk, reducePoly_monomial]
        simp [abs_of_neg hn]
      · rw [Z_of_nonneg q hn, ← mk_X q 1, ← map_pow, MvPolynomial.X_pow_eq_monomial,
          reduceQuot_mk, reducePoly_monomial]
        simp [abs_of_nonneg hn])
    (by
      refine LinearMap.ext fun u => ?_
      obtain ⟨p, rfl⟩ := mk_surjective q u
      induction p using MvPolynomial.induction_on' with
      | monomial d b =>
        simp only [LinearMap.comp_apply, LinearMap.id_apply]
        have hd : Finsupp.single (0 : Fin 2) (d 0) + Finsupp.single (1 : Fin 2) (d 1) = d := by
          ext i; fin_cases i <;> simp
        have hpoly : MvPolynomial.monomial d b = MvPolynomial.C b *
            (MvPolynomial.X (0 : Fin 2) ^ d 0 * MvPolynomial.X (1 : Fin 2) ^ d 1) := by
          rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.X_pow_eq_monomial,
            MvPolynomial.monomial_mul_monomial, MvPolynomial.C_mul_monomial, hd, mul_one, mul_one]
        have hmk : mk q (MvPolynomial.monomial d b) = b • (coord q 0 ^ d 0 * coord q 1 ^ d 1) := by
          rw [hpoly, map_mul, map_mul, map_pow, map_pow, mk_X, mk_X,
            ← MvPolynomial.algebraMap_eq, AlgHom.commutes, ← Algebra.smul_def]
        rw [reduceQuot_mk, reducePoly_monomial, Finsupp.linearCombination_single, hmk,
          coord_zero_pow_mul_coord_one_pow, ← Algebra.smul_def, smul_smul]
      | add f g hf hg => rw [map_add]; simpa only [map_add] using congrArg₂ (· + ·) hf hg)

/-- **Slab normal form**: `NodeAlgebra B q` has the integer-indexed `B`-basis `n ↦ Z q n`,
corresponding to `{(coord q 0)^a | a ≥ 0} ∪ {(coord q 1)^a | a ≥ 1}` (`Z q (-a) = (coord q 0)^a`,
`Z q 0 = 1`, and `Z q a = (coord q 1)^a`). -/
def slabBasis (q : B) : Module.Basis ℤ B (NodeAlgebra B q) :=
  Module.Basis.ofRepr (slabReprEquiv q)

private theorem slabBasis_repr_apply (q : B) (u : NodeAlgebra B q) :
    (slabBasis q).repr u = reduceQuot q u := rfl

@[simp] theorem slabBasis_apply (q : B) (n : ℤ) : slabBasis q n = Z q n := by
  simp [slabBasis, Module.Basis.coe_ofRepr, slabReprEquiv]

@[simp] theorem coe_slabBasis (q : B) : ⇑(slabBasis q) = Z q := funext (slabBasis_apply q)

@[simp] theorem slabBasis_repr_Z (q : B) (n : ℤ) :
    (slabBasis q).repr (Z q n) = Finsupp.single n 1 := by
  rw [← slabBasis_apply, Module.Basis.repr_self]

@[simp] theorem slabBasis_repr_algebraMap (q : B) (b : B) :
    (slabBasis q).repr (algebraMap B (NodeAlgebra B q) b) = Finsupp.single 0 b := by
  rw [← mul_one (algebraMap B (NodeAlgebra B q) b), ← Algebra.smul_def, ← Z_zero q,
    map_smul, slabBasis_repr_Z, Finsupp.smul_single, smul_eq_mul, mul_one]

@[simp] theorem slabBasis_repr_coord_zero (q : B) :
    (slabBasis q).repr (coord q 0) = Finsupp.single (-1) 1 := by
  rw [← Z_neg_one q, slabBasis_repr_Z]

@[simp] theorem slabBasis_repr_coord_one (q : B) :
    (slabBasis q).repr (coord q 1) = Finsupp.single 1 1 := by
  rw [← Z_one q, slabBasis_repr_Z]

theorem slabBasis_repr_mk_monomial (q : B) (d : Fin 2 →₀ ℕ) (b : B) :
    (slabBasis q).repr (mk q (MvPolynomial.monomial d b)) =
      Finsupp.single ((d 1 : ℤ) - (d 0 : ℤ)) (b * q ^ min (d 0) (d 1)) := by
  rw [slabBasis_repr_apply, reduceQuot_mk, reducePoly_monomial]

/-- Linear induction principle on `NodeAlgebra B q` along its normal-form basis `n ↦ Z q n`. -/
theorem induction_linear {q : B} {P : NodeAlgebra B q → Prop}
    (zero : P 0) (add : ∀ x y, P x → P y → P (x + y))
    (smul_Z : ∀ (b : B) (n : ℤ), P (b • Z q n)) (u : NodeAlgebra B q) : P u := by
  rw [← (slabBasis q).linearCombination_repr u, Finsupp.linearCombination_apply, Finsupp.sum]
  refine Finset.sum_induction _ _ add zero fun m _ => ?_
  rw [slabBasis_apply]
  exact smul_Z _ m

/-- The structure map `B →+* NodeAlgebra B q` is injective for every `B` and `q`. -/
theorem algebraMap_injective (q : B) : Function.Injective (algebraMap B (NodeAlgebra B q)) :=
  fun _ _ hab => by simpa using congrArg (fun u => (slabBasis q).repr u 0) hab

theorem nontrivial_iff (q : B) : Nontrivial (NodeAlgebra B q) ↔ Nontrivial B :=
  ⟨fun _ => (algebraMap B (NodeAlgebra B q)).domain_nontrivial, fun _ => inferInstance⟩

/-! ### Normal-weight `ℤ`-grading -/

/-- The normal-weight `n` piece `B ∙ Z q n` of `NodeAlgebra B q`, giving `coord q 0` weight `-1`,
`coord q 1` weight `1`, and scalars in `B` weight `0`. -/
def weightSubmodule (q : B) (n : ℤ) : Submodule B (NodeAlgebra B q) := Submodule.span B {Z q n}

theorem mem_weightSubmodule_iff (q : B) (n : ℤ) (u : NodeAlgebra B q) :
    u ∈ weightSubmodule q n ↔ ∃ b : B, b • Z q n = u := Submodule.mem_span_singleton

theorem Z_mem_weightSubmodule (q : B) (n : ℤ) : Z q n ∈ weightSubmodule q n :=
  Submodule.mem_span_singleton_self (Z q n)

theorem coord_zero_mem_weightSubmodule (q : B) : coord q 0 ∈ weightSubmodule q (-1) := by
  simpa using Z_mem_weightSubmodule q (-1)

theorem coord_one_mem_weightSubmodule (q : B) : coord q 1 ∈ weightSubmodule q 1 := by
  simpa using Z_mem_weightSubmodule q 1

theorem algebraMap_mem_weightSubmodule_zero (q : B) (b : B) :
    algebraMap B (NodeAlgebra B q) b ∈ weightSubmodule q 0 :=
  (mem_weightSubmodule_iff q 0 _).mpr ⟨b, by rw [Z_zero, Algebra.algebraMap_eq_smul_one]⟩

instance instGradedMonoidWeightSubmodule (q : B) : SetLike.GradedMonoid (weightSubmodule q) where
  one_mem := by simpa using Z_mem_weightSubmodule q 0
  mul_mem i j u v hu hv := by
    obtain ⟨a, rfl⟩ := (mem_weightSubmodule_iff q i u).mp hu
    obtain ⟨b, rfl⟩ := (mem_weightSubmodule_iff q j v).mp hv
    exact (mem_weightSubmodule_iff q (i + j) _).mpr
      ⟨a * b * q ^ ((i.natAbs + j.natAbs - (i + j).natAbs) / 2),
        by rw [smul_mul_smul_comm, Z_mul, ← Algebra.smul_def, smul_smul]⟩

theorem weightSubmodule_isInternal (q : B) : DirectSum.IsInternal (weightSubmodule q) := by
  convert (slabBasis q).isInternal_span_image_fiber id using 1; ext c u; simp [weightSubmodule]

/-- The normal-weight `ℤ`-decomposition of `NodeAlgebra B q`. -/
instance instDecompositionWeightSubmodule (q : B) :
    DirectSum.Decomposition (weightSubmodule q) :=
  (weightSubmodule_isInternal q).chooseDecomposition

/-- `NodeAlgebra B q` is a `ℤ`-graded `B`-algebra with `n`-th piece `B ∙ Z q n`. -/
instance instGradedAlgebraWeightSubmodule (q : B) : GradedAlgebra (weightSubmodule q) :=
  { instGradedMonoidWeightSubmodule q, instDecompositionWeightSubmodule q with }

@[simp] theorem coe_decompose_weightSubmodule (q : B) (u : NodeAlgebra B q) (n : ℤ) :
    (DirectSum.decompose (weightSubmodule q) u n : NodeAlgebra B q) =
      ((slabBasis q).repr u n) • Z q n := by
  induction u using induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy, add_smul]
  | smul_Z b m =>
    have hm : b • Z q m ∈ weightSubmodule q m :=
      Submodule.smul_mem _ _ (Z_mem_weightSubmodule q m)
    rw [DirectSum.decompose_of_mem (weightSubmodule q) hm, DirectSum.coe_of_apply,
      map_smul, slabBasis_repr_Z, Finsupp.smul_single, smul_eq_mul, mul_one]
    rcases eq_or_ne m n with rfl | h <;> simp [Finsupp.single_eq_of_ne, Ne.symm, *]

/-! ### Functoriality in `(B, q)` along general coefficient maps -/

/-- Functorial ring homomorphism `NodeAlgebra B q →+* NodeAlgebra B' q'` along a ring homomorphism
`φ : B →+* B'` sending `q` to `q'`, extending `NodeAlgebra.map` beyond algebra structure maps. -/
def mapRingHom (φ : B →+* B') {q : B} {q' : B'} (hq : φ q = q') :
    NodeAlgebra B q →+* NodeAlgebra B' q' :=
  liftRingHom ((algebraMap B' (NodeAlgebra B' q')).comp φ) (coord q' 0) (coord q' 1)
    (by simp [hq])

@[simp] theorem mapRingHom_algebraMap (φ : B →+* B') {q : B} {q' : B'} (hq : φ q = q') (b : B) :
    mapRingHom φ hq (algebraMap B (NodeAlgebra B q) b) =
      algebraMap B' (NodeAlgebra B' q') (φ b) :=
  liftRingHom_algebraMap _ _ _ _ b

@[simp] theorem mapRingHom_coord (φ : B →+* B') {q : B} {q' : B'} (hq : φ q = q') (i : Fin 2) :
    mapRingHom φ hq (coord q i) = coord q' i := by
  fin_cases i <;> simp [mapRingHom]

@[simp] theorem mapRingHom_Z (φ : B →+* B') {q : B} {q' : B'} (hq : φ q = q') (n : ℤ) :
    mapRingHom φ hq (Z q n) = Z q' n := by
  rw [mapRingHom, liftRingHom_Z, Z_def]

@[simp] theorem slabBasis_repr_mapRingHom (φ : B →+* B') {q : B} {q' : B'} (hq : φ q = q')
    (u : NodeAlgebra B q) (n : ℤ) :
    (slabBasis q').repr (mapRingHom φ hq u) n = φ ((slabBasis q).repr u n) := by
  induction u using induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | smul_Z b m =>
    rw [Algebra.smul_def b (Z q m), map_mul, mapRingHom_algebraMap, mapRingHom_Z,
      ← Algebra.smul_def (φ b) (Z q' m), ← Algebra.smul_def b (Z q m),
      map_smul, map_smul, slabBasis_repr_Z, slabBasis_repr_Z]
    rcases eq_or_ne m n with rfl | h <;> simp [Finsupp.single_eq_of_ne, Ne.symm, *]

@[simp] theorem mapRingHom_id (q : B) :
    mapRingHom (RingHom.id B) (rfl : RingHom.id B q = q) = RingHom.id _ :=
  ringHom_ext (fun _ => by simp) (by simp) (by simp)

theorem mapRingHom_comp (ψ : B' →+* B'') (φ : B →+* B') {q : B} {q' : B'} {q'' : B''}
    (hq : φ q = q') (hq' : ψ q' = q'') :
    (mapRingHom ψ hq').comp (mapRingHom φ hq) =
      mapRingHom (ψ.comp φ) (by rw [RingHom.comp_apply, hq, hq']) :=
  ringHom_ext (fun _ => by simp) (by simp) (by simp)

/-- Functorial `R`-algebra homomorphism `NodeAlgebra B q →ₐ[R] NodeAlgebra B' q'` along an
`R`-algebra homomorphism `φ : B →ₐ[R] B'` sending `q` to `q'`. -/
def mapAlgHom [CommSemiring R] [Algebra R B] [Algebra R B']
    (φ : B →ₐ[R] B') {q : B} {q' : B'} (hq : φ q = q') :
    NodeAlgebra B q →ₐ[R] NodeAlgebra B' q' where
  toRingHom := mapRingHom φ.toRingHom hq
  commutes' r := by
    simp [IsScalarTower.algebraMap_apply R B (NodeAlgebra B q),
      IsScalarTower.algebraMap_apply R B' (NodeAlgebra B' q')]

@[simp] theorem coe_mapAlgHom [CommSemiring R] [Algebra R B] [Algebra R B']
    (φ : B →ₐ[R] B') {q : B} {q' : B'} (hq : φ q = q') :
    (mapAlgHom φ hq : NodeAlgebra B q →+* NodeAlgebra B' q') = mapRingHom φ.toRingHom hq := (rfl)

theorem mapAlgHom_apply [CommSemiring R] [Algebra R B] [Algebra R B']
    (φ : B →ₐ[R] B') {q : B} {q' : B'} (hq : φ q = q') (u : NodeAlgebra B q) :
    mapAlgHom φ hq u = mapRingHom φ.toRingHom hq u := (rfl)

@[simp] theorem mapAlgHom_algebraMap [CommSemiring R] [Algebra R B] [Algebra R B']
    (φ : B →ₐ[R] B') {q : B} {q' : B'} (hq : φ q = q') (b : B) :
    mapAlgHom φ hq (algebraMap B (NodeAlgebra B q) b) =
      algebraMap B' (NodeAlgebra B' q') (φ b) := mapRingHom_algebraMap φ.toRingHom hq b

@[simp] theorem mapAlgHom_coord [CommSemiring R] [Algebra R B] [Algebra R B']
    (φ : B →ₐ[R] B') {q : B} {q' : B'} (hq : φ q = q') (i : Fin 2) :
    mapAlgHom φ hq (coord q i) = coord q' i := mapRingHom_coord φ.toRingHom hq i

@[simp] theorem mapAlgHom_Z [CommSemiring R] [Algebra R B] [Algebra R B']
    (φ : B →ₐ[R] B') {q : B} {q' : B'} (hq : φ q = q') (n : ℤ) :
    mapAlgHom φ hq (Z q n) = Z q' n := mapRingHom_Z φ.toRingHom hq n

/-- Functorial `R`-algebra equivalence `NodeAlgebra B q ≃ₐ[R] NodeAlgebra B' q'` along an
`R`-algebra equivalence `φ : B ≃ₐ[R] B'` sending `q` to `q'`. -/
def mapAlgEquiv [CommSemiring R] [Algebra R B] [Algebra R B']
    (φ : B ≃ₐ[R] B') {q : B} {q' : B'} (hq : φ q = q') :
    NodeAlgebra B q ≃ₐ[R] NodeAlgebra B' q' :=
  AlgEquiv.ofAlgHom
    (mapAlgHom (φ : B →ₐ[R] B') (by simpa using hq))
    (mapAlgHom (φ.symm : B' →ₐ[R] B) (by simpa using φ.symm_apply_eq.mpr hq.symm))
    (algHom_ext_of_algebra (fun b => by simp) (by simp) (by simp))
    (algHom_ext_of_algebra (fun b => by simp) (by simp) (by simp))

@[simp] theorem mapAlgEquiv_apply [CommSemiring R] [Algebra R B] [Algebra R B']
    (φ : B ≃ₐ[R] B') {q : B} {q' : B'} (hq : φ q = q') (u : NodeAlgebra B q) :
    mapAlgEquiv φ hq u = mapRingHom φ.toRingHom hq u := (rfl)

@[simp] theorem mapAlgEquiv_symm [CommSemiring R] [Algebra R B] [Algebra R B']
    (φ : B ≃ₐ[R] B') {q : B} {q' : B'} (hq : φ q = q') :
    (mapAlgEquiv φ hq).symm = mapAlgEquiv φ.symm (φ.symm_apply_eq.mpr hq.symm) := (rfl)

end NodeAlgebra

end TauCeti

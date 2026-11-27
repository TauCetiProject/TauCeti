/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import TauCeti.RingTheory.Node.Basic
import TauCeti.Algebra.DirectSum.Internal

/-!
# Normal-form basis and grading for nodal algebras

For a commutative ring `B` and `q ∈ B`, indexing pure powers of the generators of
`NodeAlgebra B q = B[x, y] / (x y - q)` by `n ∈ ℤ` (`Z q n = (coord q 0)^{-n}` for `n < 0`,
`Z q 0 = 1`, `Z q n = (coord q 1)^n` for `n > 0`) yields:
* the free `B`-basis `NodeAlgebra.slabBasis q : Module.Basis ℤ B (NodeAlgebra B q)` (hence
  injectivity of `algebraMap B (NodeAlgebra B q)`);
* the product law `Z q n * Z q m = algebraMap B _ (q ^ r) * Z q (n + m)` for
  `r = (|n| + |m| - |n + m|) / 2` (`NodeAlgebra.Z_mul`);
* the normal-weight `ℤ`-grading `NodeAlgebra.weightSubmodule q` with `n`-th piece `B ∙ Z q n`;
* normal-form compatibility with coefficient maps (`NodeAlgebra.mapRingHom_Z`,
  `NodeAlgebra.slabBasis_repr_mapRingHom`, `NodeAlgebra.mapAlgHom_Z`).

## References

* M. Gross and B. Siebert, *An Invitation to Toric Degenerations*, §2.3, arXiv:0808.2749v2.
* M. Gross, P. Hacking, and B. Siebert, *Theta functions on varieties with effective
  anti-canonical class*, §3.1, arXiv:1601.07081v4.
-/

public section

noncomputable section

namespace TauCeti

namespace NodeAlgebra

variable {B B' C R : Type*} [CommRing B] [CommRing B']

/-! ### Normal-form elements `Z_n` and multiplication -/

/-- The integer-indexed normal-form elements of `NodeAlgebra B q`: `Z q n = (coord q 0)^{-n}` for
`n < 0`, `Z q 0 = 1`, and `Z q n = (coord q 1)^n` for `n > 0`. -/
def Z (q : B) (n : ℤ) : NodeAlgebra B q :=
  if n < 0 then coord q 0 ^ n.natAbs else coord q 1 ^ n.natAbs

theorem Z_def (q : B) (n : ℤ) :
    Z q n = if n < 0 then coord q 0 ^ n.natAbs else coord q 1 ^ n.natAbs := (rfl)

theorem Z_of_neg (q : B) {n : ℤ} (hn : n < 0) : Z q n = coord q 0 ^ n.natAbs := ite_eq_left hn

theorem Z_of_nonneg (q : B) {n : ℤ} (hn : 0 ≤ n) : Z q n = coord q 1 ^ n.natAbs :=
  ite_eq_right (not_lt.mpr hn)

@[simp] theorem Z_zero (q : B) : Z q 0 = 1 := by simp [Z_def]
@[simp] theorem Z_one (q : B) : Z q 1 = coord q 1 := by simp [Z_def]
@[simp] theorem Z_neg_one (q : B) : Z q (-1) = coord q 0 := by simp [Z_def]

@[simp] theorem Z_natCast (q : B) (a : ℕ) : Z q (a : ℤ) = coord q 1 ^ a := by
  rw [Z_of_nonneg q (Int.natCast_nonneg a), Int.natAbs_natCast]

@[simp] theorem Z_neg_natCast (q : B) (a : ℕ) : Z q (-(a : ℤ)) = coord q 0 ^ a := by
  rcases eq_or_ne a 0 with rfl | ha <;>
    [simp; rw [Z_of_neg q (by omega), Int.natAbs_neg, Int.natAbs_natCast]]

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
  | succ a ih => cases b with
    | zero =>
      rw [pow_zero, mul_one, min_zero, pow_zero, map_one, one_mul, Nat.cast_zero, zero_sub,
        Z_neg_natCast]
    | succ b =>
      calc coord q 0 ^ (a + 1) * coord q 1 ^ (b + 1)
          = (coord q 0 * coord q 1) * (coord q 0 ^ a * coord q 1 ^ b) := by ring
        _ = algebraMap B (NodeAlgebra B q) (q ^ min (a + 1) (b + 1)) *
              Z q (((b + 1 : ℕ) : ℤ) - ((a + 1 : ℕ) : ℤ)) := by
            rw [coord_zero_mul_coord_one, ih b, Nat.succ_min_succ, pow_succ', map_mul, mul_assoc,
              Nat.cast_succ, Nat.cast_succ, add_sub_add_right_eq_sub]

/-- **Product formula for the normal-form basis of a nodal algebra.** For all `n, m : ℤ` and
`r = (|n| + |m| - |n + m|) / 2`, `Z q n * Z q m = q^r • Z q (n + m)`. -/
theorem Z_mul (q : B) (n m : ℤ) :
    let r := (n.natAbs + m.natAbs - (n + m).natAbs) / 2
    Z q n * Z q m = algebraMap B (NodeAlgebra B q) (q ^ r) * Z q (n + m) := by
  dsimp only; by_cases hn : n < 0 <;> by_cases hm : m < 0
  · have hnat : (n + m).natAbs = n.natAbs + m.natAbs := by omega
    rw [Z_of_neg q hn, Z_of_neg q hm, Z_of_neg q (by omega)]
    simp [hnat, pow_add]
  · have hmin : min n.natAbs m.natAbs = (n.natAbs + m.natAbs - (n + m).natAbs) / 2 := by omega
    have hdiff : (m.natAbs : ℤ) - n.natAbs = n + m := by omega
    rw [Z_of_neg q hn, Z_of_nonneg q (not_lt.mp hm), coord_zero_pow_mul_coord_one_pow, hmin, hdiff]
  · have hmin : min m.natAbs n.natAbs = (n.natAbs + m.natAbs - (n + m).natAbs) / 2 := by omega
    have hdiff : (n.natAbs : ℤ) - m.natAbs = n + m := by omega
    rw [Z_of_nonneg q (not_lt.mp hn), Z_of_neg q hm, mul_comm, coord_zero_pow_mul_coord_one_pow,
      hmin, hdiff]
  · have hnat : (n + m).natAbs = n.natAbs + m.natAbs := by omega
    rw [Z_of_nonneg q (not_lt.mp hn), Z_of_nonneg q (not_lt.mp hm), Z_of_nonneg q (by omega)]
    simp [hnat, pow_add]

/-- When `a` and `b` have the same sign, `Z q (a + b) = Z q a * Z q b` without any factor of
`q`. -/
theorem Z_add_eq_mul_of_same_sign (q : B) {a b : ℤ}
    (hab : (0 ≤ a ∧ 0 ≤ b) ∨ (a ≤ 0 ∧ b ≤ 0)) : Z q (a + b) = Z q a * Z q b := by
  have hexp : (a.natAbs + b.natAbs - (a + b).natAbs) / 2 = 0 := by omega
  rw [Z_mul, hexp, pow_zero, map_one, one_mul]

/-- Reduction of a polynomial monomial `b X₀^(d 0) X₁^(d 1)` in `NodeAlgebra B q` to normal form:
`mk q (monomial d b) = algebraMap B _ (b * q ^ min (d 0) (d 1)) * Z q (d 1 - d 0)`. -/
theorem mk_monomial (q : B) (d : Fin 2 →₀ ℕ) (b : B) :
    mk q (MvPolynomial.monomial d b) =
      algebraMap B (NodeAlgebra B q) (b * q ^ min (d 0) (d 1)) * Z q ((d 1 : ℤ) - (d 0 : ℤ)) := by
  rw [MvPolynomial.monomial_eq, map_mul, ← MvPolynomial.algebraMap_eq, AlgHom.commutes,
    Finsupp.prod_fintype _ _ (fun _ => by simp), Fin.prod_univ_two]
  simp [coord_zero_pow_mul_coord_one_pow, mul_assoc]

/-! ### Normal-form basis and injectivity of the structure map -/

/-- Monomial reduction map `B[x, y] →ₗ[B] (ℤ →₀ B)` sending `b x^i y^j` to
`b q^{\min(i, j)} e_{j - i}`. -/
private def reducePoly (q : B) : MvPolynomial (Fin 2) B →ₗ[B] (ℤ →₀ B) :=
  (Finsupp.lsum B fun d : Fin 2 →₀ ℕ => (Finsupp.lsingle ((d 1 : ℤ) - (d 0 : ℤ))).comp
    (LinearMap.mulRight B (q ^ min (d 0) (d 1)))).comp
    (AddMonoidAlgebra.coeffLinearEquiv B).toLinearMap

private theorem reducePoly_monomial (q : B) (d : Fin 2 →₀ ℕ) (b : B) :
    reducePoly q (MvPolynomial.monomial d b) =
      Finsupp.single ((d 1 : ℤ) - (d 0 : ℤ)) (b * q ^ min (d 0) (d 1)) := by
  simp [reducePoly, ← MvPolynomial.single_eq_monomial]

private theorem reducePoly_X_mul_X_mul_monomial (q : B) (d : Fin 2 →₀ ℕ) (b : B) :
    reducePoly q (MvPolynomial.X (0 : Fin 2) * MvPolynomial.X 1 * MvPolynomial.monomial d b) =
      reducePoly q (MvPolynomial.C q * MvPolynomial.monomial d b) := by
  have hX : MvPolynomial.X (0 : Fin 2) * MvPolynomial.X 1 =
      MvPolynomial.monomial (Finsupp.single 0 1 + Finsupp.single 1 1) (1 : B) := by
    rw [MvPolynomial.X, MvPolynomial.X, MvPolynomial.monomial_mul_monomial, mul_one]
  rw [hX, MvPolynomial.monomial_mul_monomial, one_mul, MvPolynomial.C_mul_monomial,
    reducePoly_monomial, reducePoly_monomial]
  have hi (i : Fin 2) :
      (Finsupp.single (0 : Fin 2) 1 + Finsupp.single 1 1 + d : Fin 2 →₀ ℕ) i = d i + 1 := by
    fin_cases i <;> simp [add_comm]
  rw [hi 0, hi 1, Nat.cast_succ, Nat.cast_succ, add_sub_add_right_eq_sub, Nat.succ_min_succ,
    pow_succ', ← mul_assoc, mul_comm b q]

private theorem reducePoly_eq_zero_of_mem_ideal (q : B) {p : MvPolynomial (Fin 2) B}
    (hp : p ∈ Ideal.span {MvPolynomial.X (0 : Fin 2) * MvPolynomial.X 1 - MvPolynomial.C q}) :
    reducePoly q p = 0 := by
  obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton.mp hp
  clear hp
  induction r using MvPolynomial.induction_on' with
  | monomial d b => rw [sub_mul, map_sub, reducePoly_X_mul_X_mul_monomial, sub_self]
  | add f g hf hg => rw [mul_add, map_add, hf, hg, add_zero]

private theorem ker_mk_toLinearMap_le (q : B) :
    LinearMap.ker (mk q).toLinearMap ≤ LinearMap.ker (reducePoly q) := fun _ hp => by
  rw [LinearMap.mem_ker, AlgHom.toLinearMap_apply, ← AlgHom.coe_toRingHom, ← RingHom.mem_ker,
    ker_mk] at hp
  exact LinearMap.mem_ker.mpr (reducePoly_eq_zero_of_mem_ideal q hp)

private def reduceQuot (q : B) : NodeAlgebra B q →ₗ[B] (ℤ →₀ B) :=
  (mk q).toLinearMap.liftOfSurjective (mk_surjective q) ⟨reducePoly q, ker_mk_toLinearMap_le q⟩

private theorem reduceQuot_mk (q : B) (p : MvPolynomial (Fin 2) B) :
    reduceQuot q (mk q p) = reducePoly q p :=
  LinearMap.equivOfSurjective_apply (f := (mk q).toLinearMap) (g := reducePoly q) (m := p) _ _

/-- Coordinate equivalence `NodeAlgebra B q ≃ₗ[B] (ℤ →₀ B)` sending `Z q n` to
`Finsupp.single n 1`. -/
private def slabReprEquiv (q : B) : NodeAlgebra B q ≃ₗ[B] (ℤ →₀ B) :=
  LinearEquiv.ofLinearMap (reduceQuot q) (Finsupp.linearCombination B (Z q))
    (by
      ext n a; simp only [LinearMap.comp_apply, LinearMap.id_apply, Finsupp.lsingle_apply,
        Finsupp.linearCombination_single, one_smul]
      rcases lt_or_ge n 0 with hn | hn
      · rw [Z_of_neg q hn, ← mk_X q 0, ← map_pow, MvPolynomial.X_pow_eq_monomial,
          reduceQuot_mk, reducePoly_monomial]; simp [abs_of_neg hn]
      · rw [Z_of_nonneg q hn, ← mk_X q 1, ← map_pow, MvPolynomial.X_pow_eq_monomial,
          reduceQuot_mk, reducePoly_monomial]; simp [abs_of_nonneg hn])
    (LinearMap.ext fun u => by
      obtain ⟨p, rfl⟩ := mk_surjective q u
      induction p using MvPolynomial.induction_on' with
      | monomial d b =>
        rw [LinearMap.comp_apply, reduceQuot_mk]
        simp [reducePoly_monomial, mk_monomial, Algebra.smul_def]
      | add f g hf hg => rw [map_add]; simpa only [map_add] using congrArg₂ (· + ·) hf hg)

/-- **Slab normal form**: `NodeAlgebra B q` has the integer-indexed `B`-basis `n ↦ Z q n`,
corresponding to `{(coord q 0)^a | a ≥ 0} ∪ {(coord q 1)^a | a ≥ 1}`
(`Z q (-a) = (coord q 0)^a`, `Z q 0 = 1`, and `Z q a = (coord q 1)^a`). -/
def slabBasis (q : B) : Module.Basis ℤ B (NodeAlgebra B q) :=
  Module.Basis.ofRepr (slabReprEquiv q)

private theorem slabBasis_repr_apply (q : B) (u : NodeAlgebra B q) :
    (slabBasis q).repr u = reduceQuot q u := by simp [slabBasis, slabReprEquiv]

@[simp] theorem slabBasis_apply (q : B) (n : ℤ) : slabBasis q n = Z q n := by
  simp [slabBasis, Module.Basis.coe_ofRepr, slabReprEquiv]

@[simp] theorem coe_slabBasis (q : B) : ⇑(slabBasis q) = Z q := funext (slabBasis_apply q)

@[simp] theorem slabBasis_repr_Z (q : B) (n : ℤ) :
    (slabBasis q).repr (Z q n) = Finsupp.single n 1 := by
  rw [← slabBasis_apply, Module.Basis.repr_self]

@[simp] theorem slabBasis_repr_algebraMap (q : B) (b : B) :
    (slabBasis q).repr (algebraMap B (NodeAlgebra B q) b) = Finsupp.single 0 b := by
  rw [Algebra.algebraMap_eq_smul_one, ← Z_zero q, map_smul, slabBasis_repr_Z, Finsupp.smul_single,
    smul_eq_mul, mul_one]

theorem slabBasis_repr_mk_monomial (q : B) (d : Fin 2 →₀ ℕ) (b : B) :
    (slabBasis q).repr (mk q (MvPolynomial.monomial d b)) =
      Finsupp.single ((d 1 : ℤ) - (d 0 : ℤ)) (b * q ^ min (d 0) (d 1)) := by
  rw [slabBasis_repr_apply, reduceQuot_mk, reducePoly_monomial]

/-- Linear induction principle on `NodeAlgebra B q` along its normal-form basis `n ↦ Z q n`. -/
theorem induction_linear {q : B} {P : NodeAlgebra B q → Prop}
    (zero : P 0) (add : ∀ x y, P x → P y → P (x + y))
    (smul_Z : ∀ (b : B) (n : ℤ), P (b • Z q n)) (u : NodeAlgebra B q) : P u := by
  rw [← (slabBasis q).linearCombination_repr u, Finsupp.linearCombination_apply, Finsupp.sum]
  exact Finset.sum_induction _ _ add zero fun m _ => by simpa [slabBasis_apply] using smul_Z _ m

/-- The structure map `B →+* NodeAlgebra B q` is injective for every `B` and `q`. -/
theorem algebraMap_injective (q : B) : Function.Injective (algebraMap B (NodeAlgebra B q)) :=
  fun _ _ hab => by simpa using congrArg (fun u => (slabBasis q).repr u 0) hab

theorem nontrivial_iff (q : B) : Nontrivial (NodeAlgebra B q) ↔ Nontrivial B :=
  ⟨fun _ => (algebraMap B (NodeAlgebra B q)).domain_nontrivial,
    fun _ => (algebraMap_injective q).nontrivial⟩

/-! ### Normal-weight `ℤ`-grading -/

/-- The normal-weight `n` piece `B ∙ Z q n` of `NodeAlgebra B q`, giving `coord q 0` weight `-1`,
`coord q 1` weight `1`, and scalars in `B` weight `0`. -/
def weightSubmodule (q : B) (n : ℤ) : Submodule B (NodeAlgebra B q) := Submodule.span B {Z q n}

theorem weightSubmodule_def (q : B) (n : ℤ) :
    weightSubmodule q n = Submodule.span B {Z q n} := (rfl)

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

theorem isInternal_weightSubmodule (q : B) : DirectSum.IsInternal (weightSubmodule q) := by
  convert (slabBasis q).isInternal_span_image_fiber id using 1; ext c u; simp [weightSubmodule]

/-- The normal-weight `ℤ`-decomposition of `NodeAlgebra B q`. -/
instance instDecompositionWeightSubmodule (q : B) : DirectSum.Decomposition (weightSubmodule q) :=
  (isInternal_weightSubmodule q).chooseDecomposition

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
    rw [DirectSum.decompose_of_mem (weightSubmodule q)
        (Submodule.smul_mem _ _ (Z_mem_weightSubmodule q m)), DirectSum.coe_of_apply,
      map_smul, slabBasis_repr_Z, Finsupp.smul_single, smul_eq_mul, mul_one]
    rcases eq_or_ne m n with rfl | h <;> simp [Finsupp.single_eq_of_ne, Ne.symm, *]

/-! ### Normal-form compatibility with coefficient maps -/

@[simp] theorem mapRingHom_Z (φ : B →+* B') {q : B} {q' : B'} (hq : φ q = q') (n : ℤ) :
    mapRingHom φ hq (Z q n) = Z q' n := by
  rw [Z_def, Z_def]; split_ifs <;> simp

@[simp] theorem slabBasis_repr_mapRingHom (φ : B →+* B') {q : B} {q' : B'} (hq : φ q = q')
    (u : NodeAlgebra B q) (n : ℤ) :
    (slabBasis q').repr (mapRingHom φ hq u) n = φ ((slabBasis q).repr u n) := by
  induction u using induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | smul_Z b m =>
    rw [Algebra.smul_def b (Z q m), map_mul, mapRingHom_algebraMap, mapRingHom_Z,
      ← Algebra.smul_def (φ b) (Z q' m), map_smul, slabBasis_repr_Z,
      ← Algebra.smul_def b (Z q m), map_smul, slabBasis_repr_Z]
    rcases eq_or_ne m n with rfl | h <;> simp [Finsupp.single_eq_of_ne, Ne.symm, *]

@[simp] theorem mapAlgHom_Z [CommSemiring R] [Algebra R B] [Algebra R B']
    (φ : B →ₐ[R] B') {q : B} {q' : B'} (hq : φ q = q') (n : ℤ) :
    mapAlgHom φ hq (Z q n) = Z q' n := by
  rw [← AlgHom.coe_toRingHom, toRingHom_mapAlgHom, mapRingHom_Z]

end NodeAlgebra

end TauCeti

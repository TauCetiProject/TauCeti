/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Basic
public import Mathlib.RingTheory.Bialgebra.Equiv
public import Mathlib.RingTheory.HopfAlgebra.Primitive
public import TauCeti.Algebra.Bialgebra.Module.TensorProduct
public import TauCeti.Algebra.Bialgebra.ModuleAlgebra.Basic
public import TauCeti.Algebra.Homology.SlashHomology
public import TauCeti.Algebra.HopfAlgebra.SymmetricAlgebra.PowIdeal
public import TauCeti.LinearAlgebra.SymmetricAlgebra.RankOne
public import TauCeti.RingTheory.AdjoinRoot.Basic

import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.LinearAlgebra.TensorProduct.Basis
import TauCeti.Algebra.Bialgebra.Primitive
import TauCeti.LinearAlgebra.Basis.Basic

/-!
# Truncated primitive Hopf algebras and slash-homology projectivity detection

Whenever `0 < n` and all intermediate binomial coefficients `n.choose i` (`0 < i < n`) vanish in
`k` (e.g. `n = p ^ r` in prime characteristic `p`), `(1 + X) ^ n = 1 + X ^ n` in `k[X]`, so
`(d ^ n)` is a Hopf ideal of `k[d]` and `H_n = k[d] / (d ^ n)` is a cocommutative Hopf algebra
with primitive generator `d` (`Δ d = d ⊗ 1 + 1 ⊗ d`, `ε d = 0`, `S d = -d`).

Left `H`-modules carry the `k`-linear `p`-differential `m ↦ d • m`, with unsigned Leibniz rules on
tensor products and left `H`-module algebras. This file axiomatizes truncated primitive bialgebras
(`TauCeti.TruncatedPrimitive`), constructs `TruncatedPrimitiveAlg R n = R[d] / (d ^ n)` via
`TauCeti.SymmetricAlgebra.spanPowHopfIdeal`, proves algebra and bialgebra uniqueness, establishes
**Khovanov–Qi's slash-homology detection theorem**
(`TauCeti.slashHomology_subsingleton_iff_projective`) for arbitrary (not necessarily
finite-dimensional) `H`-modules over a field `k`, and computes the slash homology of the trivial
module and the slash-homology ranks of the cyclic quotients `H ⧸ (d ^ r)` for `r < p` over any
nontrivial commutative ring `k`.

## Main definitions and results

* `TauCeti.TruncatedPrimitive`, `natCast_choose_eq_zero`, `natCast_eq_zero`, `isEmpty_of_charZero`,
  `charP`, `adjoinRootAlgEquiv`, `bialgEquivTruncatedPrimitiveAlg`.
* `TauCeti.TruncatedPrimitiveAlg` (equipped automatically with `HopfAlgebra` structure in prime
  characteristic `p` for `n = p` and `n = p ^ r`, and via
  `TauCeti.SymmetricAlgebra.isHopfIdeal_span_pow_of_choose_eq_zero` whenever `0 < n` and all
  intermediate binomial coefficients vanish), `TruncatedPrimitiveAlg.algHom_ext`, and
  `TruncatedPrimitiveAlg.mkTruncatedPrimitive`.
* `TauCeti.TruncatedPrimitive.moduleDifferential`, `moduleDifferential_tmul`, `action_d_mul`,
  `isPHomotopic_id_zero_of_projective`.
* `TauCeti.slashHomology_subsingleton_iff_projective` and `slashHomology_subsingleton_iff_free`.
* `TauCeti.TruncatedPrimitive.slashHomologyZeroTrivialEquiv`, `not_projective_trivial`,
  `finrank_slashHomology_quotient_span_pow`, `not_projective_quotient_span_pow`.

## References

* M. Kapranov, *On the q-analog of homological algebra*, arXiv:q-alg/9611005, 1996.
* M. Khovanov, *Hopfological algebra and categorification at a root of unity: the first steps*,
  J. Knot Theory Ramifications **25** (2016), no. 3, 1640006.
* M. Khovanov and Y. Qi, *An approach to categorification of some small quantum groups*,
  Quantum Topol. **6** (2015), 185–311, §2.
-/

public section

open scoped TensorProduct
open Polynomial

namespace TauCeti

universe u v w

/-! ### Truncated primitive bialgebras and automatic characteristic forcing -/

/-- A `p`-truncated primitive structure on a `k`-bialgebra `H` consists of a primitive element
`d ∈ H` with `d ^ p = 0` whose powers `1, d, …, d ^ (p - 1)` form a `k`-basis of `H`. -/
structure TruncatedPrimitive {k : Type u} (H : Type v) [CommSemiring k] [Semiring H]
    [Bialgebra k H] (p : ℕ) where
  /-- The distinguished primitive `p`-nilpotent generator. -/
  d : H
  /-- `d` has primitive coproduct `Δ d = d ⊗ 1 + 1 ⊗ d`. -/
  comul_d : Coalgebra.comul (R := k) d = d ⊗ₜ[k] 1 + 1 ⊗ₜ[k] d
  /-- `d` is `p`-nilpotent. -/
  pow_d : d ^ p = 0
  /-- The `k`-basis `1, d, …, d ^ (p - 1)` of `H`. -/
  basis : Module.Basis (Fin p) k H
  /-- The `i`-th basis vector is `d ^ i`. -/
  basis_apply : ∀ i : Fin p, basis i = d ^ (i : ℕ)

attribute [simp] TruncatedPrimitive.comul_d TruncatedPrimitive.pow_d
  TruncatedPrimitive.basis_apply

namespace TruncatedPrimitive

section Semiring

variable {k : Type u} {H : Type v} [CommSemiring k] [Semiring H] [Bialgebra k H] {p : ℕ}

/-- A `TruncatedPrimitive` structure is uniquely determined by its generator `d`. -/
@[ext]
theorem ext {P Q : TruncatedPrimitive (k := k) H p} (hd : P.d = Q.d) : P = Q := by
  cases P with
  | mk _ _ _ _ hb₁ =>
    cases Q with
    | mk _ _ _ _ hb₂ =>
      simp only at hd; subst hd; congr; ext i; rw [hb₁, hb₂]

/-- Over a nontrivial `k`-bialgebra `H`, the truncation exponent `p` is positive. -/
theorem pos [Nontrivial H] (P : TruncatedPrimitive (k := k) H p) : 0 < p := by
  by_contra hp
  obtain rfl : p = 0 := by omega
  exact one_ne_zero (by simpa using P.pow_d : (1 : H) = 0)

/-- When `2 ≤ p` and `k` is nontrivial, the generator `d` is nonzero. -/
theorem d_ne_zero [Nontrivial k] (P : TruncatedPrimitive (k := k) H p) (hp : 2 ≤ p) :
    P.d ≠ 0 := by
  have hb := P.basis.ne_zero ⟨1, by omega⟩
  rwa [P.basis_apply, pow_one] at hb

/-- **Binomial obstruction.** Every intermediate binomial coefficient `p.choose i` (`0 < i < p`)
vanishes in `k`. -/
theorem natCast_choose_eq_zero (P : TruncatedPrimitive (k := k) H p) {i : ℕ}
    (hi₀ : 0 < i) (hi : i < p) : (p.choose i : k) = 0 := by
  let B := P.basis.tensorProduct P.basis
  let idx : Fin p × Fin p := (⟨i, hi⟩, ⟨p - i, by omega⟩)
  have hΔ := TauCeti.Bialgebra.comul_pow_of_primitive P.d P.comul_d p
  rw [P.pow_d, map_zero] at hΔ
  have hcoord := congrArg (B.coord idx) hΔ.symm
  rw [map_zero, map_sum, Finset.sum_eq_single (i, p - i)] at hcoord
  · have hb : (P.d ^ i) ⊗ₜ[k] (P.d ^ (p - i)) = B idx := by
      simp [B, idx, Module.Basis.tensorProduct_apply]
    rw [← Nat.cast_smul_eq_nsmul k, hb] at hcoord
    simpa using hcoord
  · rintro ⟨a, b⟩ hab hne
    rw [Finset.mem_antidiagonal] at hab
    rcases Nat.eq_zero_or_pos a with rfl | ha0
    · simp [show b = p by omega, P.pow_d]
    · rcases Nat.eq_zero_or_pos b with rfl | hb0
      · simp [show a = p by omega, P.pow_d]
      · have ha : a < p := by omega
        have hb : b < p := by omega
        have hb_vec : (P.d ^ a) ⊗ₜ[k] (P.d ^ b) = B (⟨a, ha⟩, ⟨b, hb⟩) := by
          simp [B, Module.Basis.tensorProduct_apply]
        have hidx_ne : (⟨a, ha⟩, ⟨b, hb⟩) ≠ idx := fun heq ↦
          hne <| Prod.ext (congrArg (fun x : Fin p × Fin p ↦ (x.1 : ℕ)) heq)
            (congrArg (fun x : Fin p × Fin p ↦ (x.2 : ℕ)) heq)
        rw [← Nat.cast_smul_eq_nsmul k, hb_vec]
        simp [hidx_ne.symm]
  · exact fun hmem ↦ absurd (Finset.mem_antidiagonal.mpr (by omega)) hmem

/-- **Characteristic forcing.** Any `TruncatedPrimitive H p` with `2 ≤ p` forces `(p : k) = 0`. -/
theorem natCast_eq_zero (P : TruncatedPrimitive (k := k) H p) (hp : 2 ≤ p) : (p : k) = 0 := by
  simpa [Nat.choose_one_right] using P.natCast_choose_eq_zero Nat.zero_lt_one hp

/-- **Characteristic-zero obstruction.** Over a characteristic-zero base semiring, there is no
`TruncatedPrimitive H p` for `2 ≤ p`. -/
theorem isEmpty_of_charZero [CharZero k] (hp : 2 ≤ p) :
    IsEmpty (TruncatedPrimitive (k := k) H p) :=
  ⟨fun P ↦ (Nat.cast_ne_zero.mpr (by omega : p ≠ 0)) (P.natCast_eq_zero hp)⟩

/-- When `p` is prime and `k` is nontrivial, `TruncatedPrimitive H p` forces `CharP k p`. -/
theorem charP [Nontrivial k] [Fact p.Prime] (P : TruncatedPrimitive (k := k) H p) : CharP k p :=
  (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr
    (P.natCast_eq_zero (Fact.out : p.Prime).two_le)

/-- The `k`-rank of `H` is `p`. -/
theorem finrank_eq [StrongRankCondition k] (P : TruncatedPrimitive (k := k) H p) :
    Module.finrank k H = p := by
  rw [Module.finrank_eq_card_basis P.basis, Fintype.card_fin]

/-- The counit vanishes on `d`. -/
@[simp]
theorem counit_d (P : TruncatedPrimitive (k := k) H p) : Coalgebra.counit (R := k) P.d = 0 := by
  match p with
  | 0 =>
    have : Subsingleton H := subsingleton_of_zero_eq_one (by simpa using P.pow_d.symm)
    rw [Subsingleton.elim P.d 0, map_zero]
  | 1 =>
    rw [show P.d = 0 by simpa using P.pow_d, map_zero]
  | p + 2 =>
    have hc := congrArg (TensorProduct.lid k H) (Coalgebra.rTensor_counit_comul (R := k) P.d)
    rw [P.comul_d, map_add, LinearMap.rTensor_tmul, LinearMap.rTensor_tmul, map_add,
      TensorProduct.lid_tmul, TensorProduct.lid_tmul, TensorProduct.lid_tmul,
      Bialgebra.counit_one, one_smul] at hc
    let b := P.basis
    have h0 : (1 : H) = b ⟨0, by omega⟩ := by simp [b]
    have h1 : P.d = b ⟨1, by omega⟩ := by simp [b]
    have hcoord := congrArg (b.coord ⟨0, by omega⟩) hc
    rw [h0, h1] at hcoord
    rw [h1]
    simpa [-basis_apply] using hcoord

/-- The generator `d` is a primitive element in Mathlib's `Bialgebra.IsPrimitiveElem` sense. -/
theorem isPrimitiveElem_d (P : TruncatedPrimitive (k := k) H p) :
    Bialgebra.IsPrimitiveElem k P.d where
  counit_eq_zero := P.counit_d
  comul_eq_tmul_add_tmul := by rw [P.comul_d, add_comm]

/-- Multiplication in any `TruncatedPrimitive` bialgebra is commutative. -/
theorem mul_comm (P : TruncatedPrimitive (k := k) H p) (x y : H) : x * y = y * x := by
  have hx := P.basis.linearCombination_repr x
  have hy := P.basis.linearCombination_repr y
  rw [Finsupp.linearCombination_apply, Finsupp.sum] at hx hy
  rw [← hx, ← hy]
  simp_rw [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, P.basis_apply, ← pow_add]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ ?_
  rw [smul_comm, add_comm]

/-- In a Hopf algebra, the antipode sends `d` to `-d`. -/
@[simp]
theorem antipode_d {H : Type v} [Ring H] [HopfAlgebra k H]
    (P : TruncatedPrimitive (k := k) H p) : HopfAlgebra.antipode k P.d = -P.d :=
  P.isPrimitiveElem_d.antipode_eq_neg

end Semiring

section CommRing

variable {k : Type u} {H : Type v} [CommRing k] [Semiring H] [Bialgebra k H] {p : ℕ}

/-- **Algebra classification.** Every `p`-truncated primitive bialgebra `H` over a commutative ring
`k` is canonically `k`-algebra isomorphic to `AdjoinRoot (X ^ p : k[X]) = k[X] / (X ^ p)`, sending
the root `X` to `P.d`. -/
noncomputable def adjoinRootAlgEquiv (P : TruncatedPrimitive (k := k) H p) :
    AdjoinRoot (X ^ p : k[X]) ≃ₐ[k] H := by
  let φ : AdjoinRoot (X ^ p : k[X]) →ₐ[k] H :=
    (AdjoinRoot.algHomEquiv H (X ^ p : k[X])).symm ⟨P.d, by simp [P.pow_d]⟩
  refine AlgEquiv.ofBijective φ
    ((AdjoinRoot.xPowBasis k p).bijective_of_map_basis P.basis φ fun i ↦ ?_)
  rw [AdjoinRoot.xPowBasis_apply, P.basis_apply, map_pow, AdjoinRoot.algHomEquiv_symm_apply_root]

/-- `adjoinRootAlgEquiv` sends the class of `X` to `P.d`. -/
@[simp]
theorem adjoinRootAlgEquiv_root (P : TruncatedPrimitive (k := k) H p) :
    P.adjoinRootAlgEquiv (AdjoinRoot.root (X ^ p : k[X])) = P.d :=
  AdjoinRoot.algHomEquiv_symm_apply_root _

/-- The inverse of `adjoinRootAlgEquiv` sends `P.d` to the class of `X`. -/
@[simp]
theorem adjoinRootAlgEquiv_symm_d (P : TruncatedPrimitive (k := k) H p) :
    P.adjoinRootAlgEquiv.symm P.d = AdjoinRoot.root (X ^ p : k[X]) := by
  apply P.adjoinRootAlgEquiv.injective; simp

end CommRing

end TruncatedPrimitive

/-! ### The concrete Hopf algebra `TruncatedPrimitiveAlg R n = R[d] / (d ^ n)` -/

/-- The truncated polynomial algebra `R[d] / (d ^ n)`, realized as the quotient of
`SymmetricAlgebra R R` by `(ι 1 ^ n)` so that Mathlib's quotient bialgebra and Hopf-algebra
instances apply whenever `(ι 1 ^ n)` is a coideal or Hopf ideal. -/
abbrev TruncatedPrimitiveAlg (R : Type u) [CommRing R] (n : ℕ) : Type u :=
  SymmetricAlgebra R R ⧸ Ideal.span {(SymmetricAlgebra.ι R R 1 : SymmetricAlgebra R R) ^ n}

namespace TruncatedPrimitiveAlg

section CommRing

variable (R : Type u) [CommRing R] (n : ℕ)

/-- The distinguished generator `d` of `TruncatedPrimitiveAlg R n`, the image of `ι R R 1`. -/
def d : TruncatedPrimitiveAlg R n := Ideal.Quotient.mk _ (SymmetricAlgebra.ι R R 1)

/-- Definitional characterization of `TruncatedPrimitiveAlg.d`. -/
theorem d_def : d R n = Ideal.Quotient.mk _ (SymmetricAlgebra.ι R R 1) := (rfl)

/-- In `TruncatedPrimitiveAlg R n`, `d ^ n = 0`. -/
@[simp]
theorem pow_d : (d R n) ^ n = 0 := by
  rw [d_def, ← map_pow]; exact Ideal.Quotient.mk_singleton_self _

/-- Canonical `R`-algebra equivalence
`TruncatedPrimitiveAlg R n ≃ₐ[R] AdjoinRoot (X ^ n : R[X])`. -/
noncomputable def algEquivAdjoinRoot :
    TruncatedPrimitiveAlg R n ≃ₐ[R] AdjoinRoot (X ^ n : R[X]) :=
  Ideal.quotientEquivAlg
    (Ideal.span {(SymmetricAlgebra.ι R R 1 : SymmetricAlgebra R R) ^ n})
    (Ideal.span {(X ^ n : R[X])}) (SymmetricAlgebra.equivPolynomial (R := R))
    (by simp [Ideal.map_span])

/-- `algEquivAdjoinRoot` sends the class of `z` to the class of
`SymmetricAlgebra.equivPolynomial z`. -/
@[simp]
theorem algEquivAdjoinRoot_mk (z : SymmetricAlgebra R R) :
    algEquivAdjoinRoot R n (Ideal.Quotient.mk _ z) =
      AdjoinRoot.mk (X ^ n : R[X]) (SymmetricAlgebra.equivPolynomial z) :=
  Ideal.quotientEquivAlg_mk _ _ _ z

/-- `algEquivAdjoinRoot` sends `d R n` to the root `X` of `AdjoinRoot (X ^ n)`. -/
@[simp]
theorem algEquivAdjoinRoot_d : algEquivAdjoinRoot R n (d R n) = AdjoinRoot.root (X ^ n : R[X]) := by
  rw [d_def, algEquivAdjoinRoot_mk]; simp

/-- The inverse of `algEquivAdjoinRoot` sends the root `X` to `d R n`. -/
@[simp]
theorem algEquivAdjoinRoot_symm_root :
    (algEquivAdjoinRoot R n).symm (AdjoinRoot.root (X ^ n : R[X])) = d R n := by
  apply (algEquivAdjoinRoot R n).injective; simp

/-- Monomial `R`-basis `1, d, …, d ^ (n - 1)` of `TruncatedPrimitiveAlg R n`. -/
noncomputable def basis : Module.Basis (Fin n) R (TruncatedPrimitiveAlg R n) :=
  (AdjoinRoot.xPowBasis R n).map (algEquivAdjoinRoot R n).symm.toLinearEquiv

/-- The `i`-th element of `TruncatedPrimitiveAlg.basis R n` is `d ^ i`. -/
@[simp]
theorem basis_apply (i : Fin n) : basis R n i = (d R n) ^ (i : ℕ) := by simp [basis]

variable {R n} in
/-- Two `R`-algebra homomorphisms out of `TruncatedPrimitiveAlg R n` into any `R`-algebra agree if
they agree on `d R n`. -/
@[ext]
theorem algHom_ext {B : Type*} [Semiring B] [Algebra R B]
    {f g : TruncatedPrimitiveAlg R n →ₐ[R] B} (h : f (d R n) = g (d R n)) : f = g := by
  apply Ideal.Quotient.algHom_ext R
  suffices (f.comp (Ideal.Quotient.mkₐ R _)).comp
        (SymmetricAlgebra.equivPolynomial (R := R)).symm.toAlgHom =
      (g.comp (Ideal.Quotient.mkₐ R _)).comp
        (SymmetricAlgebra.equivPolynomial (R := R)).symm.toAlgHom from
    AlgHom.ext fun z ↦ by
      simpa using AlgHom.congr_fun this (SymmetricAlgebra.equivPolynomial z)
  exact Polynomial.algHom_ext (by simpa [d_def] using h)

/-- Build a `TruncatedPrimitive` structure on `TruncatedPrimitiveAlg R n` whenever `(ι 1 ^ n)` is
a coideal (for instance, from `Ideal.IsHopfIdeal`). -/
noncomputable def mkTruncatedPrimitive
    [((Ideal.span {(SymmetricAlgebra.ι R R 1 : SymmetricAlgebra R R) ^ n}).restrictScalars
      R).IsCoideal] :
    TruncatedPrimitive (k := R) (TruncatedPrimitiveAlg R n) n where
  d := d R n
  comul_d := by
    rw [d_def, ← Bialgebra.Quotient.mkBialgHom_apply (R := R),
      ← CoalgHomClass.map_comp_comul_apply, SymmetricAlgebra.comul_ι]
    simp [Bialgebra.Quotient.mkBialgHom_apply]
  pow_d := pow_d R n
  basis := basis R n
  basis_apply := basis_apply R n

/-- The distinguished generator of `mkTruncatedPrimitive R n` is `d R n`. -/
@[simp]
theorem mkTruncatedPrimitive_d
    [((Ideal.span {(SymmetricAlgebra.ι R R 1 : SymmetricAlgebra R R) ^ n}).restrictScalars
      R).IsCoideal] :
    (mkTruncatedPrimitive R n).d = d R n := (rfl)

end CommRing

end TruncatedPrimitiveAlg

namespace TruncatedPrimitive

section BialgUniqueness

variable {k : Type u} {H : Type v} [CommRing k] [Semiring H] [Bialgebra k H] {p : ℕ}

/-- For `0 < p`, the existence of `TruncatedPrimitive H p` automatically makes
`Ideal.span {ι 1 ^ p}` a Hopf ideal of `SymmetricAlgebra k k`. -/
theorem isHopfIdeal_span_pow (P : TruncatedPrimitive (k := k) H p) (hp : 0 < p) :
    (Ideal.span {(SymmetricAlgebra.ι k k 1 : SymmetricAlgebra k k) ^ p}).IsHopfIdeal k :=
  TauCeti.SymmetricAlgebra.isHopfIdeal_span_pow_of_choose_eq_zero (R := k) (1 : k) hp
    fun _ hi₀ hi ↦ P.natCast_choose_eq_zero hi₀ hi

/-- **Bialgebra uniqueness.** Whenever `(ι 1 ^ p)` is a coideal of `SymmetricAlgebra k k` (e.g.
via `P.isHopfIdeal_span_pow hp` when `0 < p`, or automatically for prime and prime-power exponents
in characteristic `p`), `H` is canonically bialgebra-isomorphic to `TruncatedPrimitiveAlg k p`. -/
noncomputable def bialgEquivTruncatedPrimitiveAlg (P : TruncatedPrimitive (k := k) H p)
    [((Ideal.span {(SymmetricAlgebra.ι k k 1 : SymmetricAlgebra k k) ^ p}).restrictScalars
      k).IsCoideal] :
    H ≃ₐc[k] TruncatedPrimitiveAlg k p := by
  let eAlg : TruncatedPrimitiveAlg k p ≃ₐ[k] H :=
    (TruncatedPrimitiveAlg.algEquivAdjoinRoot k p).trans P.adjoinRootAlgEquiv
  have hcounit : (Bialgebra.counitAlgHom k H).comp eAlg.toAlgHom =
      Bialgebra.counitAlgHom k (TruncatedPrimitiveAlg k p) :=
    TruncatedPrimitiveAlg.algHom_ext <| by
      simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, eAlg, AlgEquiv.trans_apply,
        TruncatedPrimitiveAlg.algEquivAdjoinRoot_d, P.adjoinRootAlgEquiv_root,
        Bialgebra.counitAlgHom_apply, P.counit_d]
      rw [TruncatedPrimitiveAlg.d_def, ← Bialgebra.Quotient.mkBialgHom_apply (R := k),
        CoalgHomClass.counit_comp_apply, SymmetricAlgebra.counit_ι]
  have hcomul :
      (Algebra.TensorProduct.map eAlg.toAlgHom eAlg.toAlgHom).comp
          (Bialgebra.comulAlgHom k _) =
        (Bialgebra.comulAlgHom k H).comp eAlg.toAlgHom :=
    TruncatedPrimitiveAlg.algHom_ext <| by
      simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, eAlg, AlgEquiv.trans_apply,
        TruncatedPrimitiveAlg.algEquivAdjoinRoot_d, P.adjoinRootAlgEquiv_root,
        Bialgebra.comulAlgHom_apply, P.comul_d]
      rw [TruncatedPrimitiveAlg.d_def, ← Bialgebra.Quotient.mkBialgHom_apply (R := k),
        ← CoalgHomClass.map_comp_comul_apply, SymmetricAlgebra.comul_ι]
      simp
  exact (BialgEquiv.ofBijective (BialgHom.ofAlgHom eAlg.toAlgHom hcounit hcomul)
    eAlg.bijective).symm

/-- The inverse of `bialgEquivTruncatedPrimitiveAlg` sends `TruncatedPrimitiveAlg.d k p` to
`P.d`. -/
@[simp]
theorem bialgEquivTruncatedPrimitiveAlg_symm_d (P : TruncatedPrimitive (k := k) H p)
    [((Ideal.span {(SymmetricAlgebra.ι k k 1 : SymmetricAlgebra k k) ^ p}).restrictScalars
      k).IsCoideal] :
    P.bialgEquivTruncatedPrimitiveAlg.symm (TruncatedPrimitiveAlg.d k p) = P.d := by
  rw [← BialgEquiv.coe_toEquiv, BialgEquiv.toEquiv_symm, bialgEquivTruncatedPrimitiveAlg,
    BialgEquiv.toEquiv_symm, Equiv.symm_symm, BialgEquiv.coe_toEquiv]
  exact (congrFun (BialgEquiv.coe_ofBijective _ _) _).trans (by simp)

/-- `bialgEquivTruncatedPrimitiveAlg` sends `P.d` to `TruncatedPrimitiveAlg.d k p`. -/
@[simp]
theorem bialgEquivTruncatedPrimitiveAlg_d (P : TruncatedPrimitive (k := k) H p)
    [((Ideal.span {(SymmetricAlgebra.ι k k 1 : SymmetricAlgebra k k) ^ p}).restrictScalars
      k).IsCoideal] :
    P.bialgEquivTruncatedPrimitiveAlg P.d = TruncatedPrimitiveAlg.d k p := by
  rw [← P.bialgEquivTruncatedPrimitiveAlg_symm_d, BialgEquiv.apply_symm_apply]

end BialgUniqueness

/-! ### The `p`-differential on left `H`-modules, unsigned Leibniz rules, and contractibility -/

section ModuleDifferential

variable {k : Type u} {H : Type v} [CommSemiring k] [Semiring H] [Bialgebra k H] {p : ℕ}
variable {M N : Type*} [AddCommMonoid M] [Module k M] [Module H M] [IsScalarTower k H M]
  [AddCommMonoid N] [Module k N] [Module H N] [IsScalarTower k H N]

/-- Multiplication by `P.d` as a `k`-linear endomorphism of any left `H`-module `M`. -/
def moduleDifferential (P : TruncatedPrimitive (k := k) H p) : M →ₗ[k] M :=
  Algebra.lsmul k k M P.d

/-- `P.moduleDifferential` acts by `P.d • m`. -/
@[simp]
theorem moduleDifferential_apply (P : TruncatedPrimitive (k := k) H p) (m : M) :
    P.moduleDifferential m = P.d • m := (rfl)

/-- Iterates of `P.moduleDifferential` act by `(P.d ^ r) • m`. -/
@[simp]
theorem moduleDifferential_pow_apply (P : TruncatedPrimitive (k := k) H p) (r : ℕ) (m : M) :
    ((P.moduleDifferential (M := M)) ^ r) m = (P.d ^ r) • m := by
  rw [moduleDifferential, ← map_pow, Algebra.lsmul_apply]

/-- On every left `H`-module `M`, `P.moduleDifferential ^ p = 0`. -/
@[simp]
theorem moduleDifferential_pow_self (P : TruncatedPrimitive (k := k) H p) :
    (P.moduleDifferential (M := M)) ^ p = 0 := by
  rw [moduleDifferential, ← map_pow, P.pow_d, map_zero]

/-- On the counit trivial module `BialgebraModule.Trivial k H`, `P.moduleDifferential` vanishes. -/
@[simp]
theorem moduleDifferential_trivial_eq_zero (P : TruncatedPrimitive (k := k) H p) :
    P.moduleDifferential (M := BialgebraModule.Trivial k H) = 0 := by
  ext x; apply (BialgebraModule.trivialEquiv k H).injective; simp [P.counit_d]

/-- **Unsigned tensor-product Leibniz rule.** `P.moduleDifferential` acts on
`BialgebraModule.Tensor k H M N` by `d(m ⊗ n) = d m ⊗ n + m ⊗ d n` without Koszul signs. -/
theorem moduleDifferential_tmul (P : TruncatedPrimitive (k := k) H p) (m : M) (n : N) :
    P.moduleDifferential (BialgebraModule.tmul k H m n) =
      BialgebraModule.tmul k H (P.moduleDifferential m) n +
        BialgebraModule.tmul k H m (P.moduleDifferential n) := by
  apply (BialgebraModule.tensorEquiv k H M N).injective
  simp [BialgebraModule.tensorAction_apply, P.comul_d]

/-- **Unsigned `p`-DG Leibniz rule on left module algebras.** On any left `H`-module algebra `A`,
`P.d` acts as an unsigned `k`-derivation: `d · (a * b) = (d · a) * b + a * (d · b)`. -/
theorem action_d_mul (P : TruncatedPrimitive (k := k) H p) {A : Type*} [Semiring A] [Algebra k A]
    (μ : LeftModuleAlgebra k H A) (a b : A) :
    μ.action P.d (a * b) = μ.action P.d a * b + a * μ.action P.d b := by
  rw [μ.action_mul]; simp [AlgHom.comp_apply, P.comul_d, Module.endTensorEndAlgHom_apply]

/-- Every `H`-linear map `f : M →ₗ[H] N` intertwines `P.moduleDifferential`. -/
theorem comp_moduleDifferential (P : TruncatedPrimitive (k := k) H p) (f : M →ₗ[H] N) :
    f.restrictScalars k ∘ₗ P.moduleDifferential = P.moduleDifferential ∘ₗ f.restrictScalars k := by
  ext m; simp

private noncomputable def selfContractingHomotopy (P : TruncatedPrimitive (k := k) H p) :
    H →ₗ[k] H :=
  P.basis.constr k fun i : Fin p ↦ if (i : ℕ) = p - 1 then (1 : H) else 0

private theorem nullHomotopicMap_selfContractingHomotopy (P : TruncatedPrimitive (k := k) H p) :
    SlashHomology.nullHomotopicMap p
        (P.moduleDifferential (M := H)) (P.moduleDifferential (M := H))
        P.selfContractingHomotopy =
      LinearMap.id := by
  apply P.basis.ext
  rintro ⟨m, hm⟩
  rw [LinearMap.id_apply, SlashHomology.nullHomotopicMap_apply, Finset.sum_eq_single m]
  · have hb : P.d ^ (p - 1) = P.basis ⟨p - 1, by omega⟩ := by simp
    simp only [moduleDifferential_pow_apply, P.basis_apply, smul_eq_mul, ← pow_add,
      show p - 1 - m + m = p - 1 by omega]
    rw [hb, selfContractingHomotopy, Module.Basis.constr_basis]; simp
  · intro i hi hne
    rw [Finset.mem_range] at hi
    rcases lt_trichotomy i m with hlt | rfl | hgt
    · have hpow : P.d ^ (p - 1 - i) * P.d ^ m = 0 := by
        rw [← pow_add, pow_eq_zero_of_le (by omega : p ≤ p - 1 - i + m) P.pow_d]
      simp [smul_eq_mul, P.basis_apply, hpow]
    · exact absurd rfl hne
    · have hb : P.d ^ (p - 1 - i + m) = P.basis ⟨p - 1 - i + m, by omega⟩ := by simp
      simp only [moduleDifferential_pow_apply, P.basis_apply, smul_eq_mul, ← pow_add]
      rw [hb, selfContractingHomotopy, Module.Basis.constr_basis]
      split_ifs with h
      · dsimp at h; omega
      · simp
  · exact fun hm_mem ↦ absurd (Finset.mem_range.mpr hm) hm_mem

private theorem nullHomotopicMap_finsupp (P : TruncatedPrimitive (k := k) H p) (ι : Type*) :
    SlashHomology.nullHomotopicMap p
        (P.moduleDifferential (M := ι →₀ H)) (P.moduleDifferential (M := ι →₀ H))
        (Finsupp.mapRange.linearMap P.selfContractingHomotopy) =
      LinearMap.id := by
  refine Finsupp.lhom_ext' fun i ↦ ?_
  have hcomm : Finsupp.lsingle (R := k) i ∘ₗ P.moduleDifferential (M := H) =
      P.moduleDifferential (M := ι →₀ H) ∘ₗ Finsupp.lsingle (R := k) i := by
    ext x; simp [Finsupp.smul_single]
  have hmap : Finsupp.mapRange.linearMap P.selfContractingHomotopy ∘ₗ Finsupp.lsingle (R := k) i =
      Finsupp.lsingle (R := k) i ∘ₗ P.selfContractingHomotopy := by ext x; simp
  rw [SlashHomology.nullHomotopicMap_comp_of_comp_eq p _ hcomm, hmap,
    ← SlashHomology.comp_nullHomotopicMap_of_comp_eq p _ hcomm,
    P.nullHomotopicMap_selfContractingHomotopy, LinearMap.comp_id, LinearMap.id_comp]

end ModuleDifferential

section Contractibility

variable {k : Type u} {H : Type v} [CommRing k] [Semiring H] [Bialgebra k H] {p : ℕ}
variable {M : Type*} [AddCommGroup M] [Module k M] [Module H M] [IsScalarTower k H M]

/-- **Contractibility of `H` over itself.** As a `p`-complex over `k`, `id_H` is `p`-homotopic
to `0`. -/
theorem isPHomotopic_id_zero_self {H : Type v} [Ring H] [Bialgebra k H]
    (P : TruncatedPrimitive (k := k) H p) :
    SlashHomology.IsPHomotopic p
      (P.moduleDifferential (M := H)) (P.moduleDifferential (M := H)) LinearMap.id 0 :=
  (SlashHomology.isPHomotopic_iff ..).mpr
    ⟨P.selfContractingHomotopy, by rw [sub_zero, P.nullHomotopicMap_selfContractingHomotopy]⟩

/-- **Every projective `H`-module is `p`-contractible over `k`.** -/
theorem isPHomotopic_id_zero_of_projective (P : TruncatedPrimitive (k := k) H p)
    [Module.Projective H M] :
    SlashHomology.IsPHomotopic p
      (P.moduleDifferential (M := M)) (P.moduleDifferential (M := M)) LinearMap.id 0 := by
  obtain ⟨s, hs⟩ := Module.projective_def'.mp ‹Module.Projective H M›
  let π : (M →₀ H) →ₗ[H] M := Finsupp.linearCombination H id
  refine (SlashHomology.isPHomotopic_iff ..).mpr
    ⟨π.restrictScalars k ∘ₗ Finsupp.mapRange.linearMap P.selfContractingHomotopy ∘ₗ
      s.restrictScalars k, ?_⟩
  rw [sub_zero, ← SlashHomology.comp_nullHomotopicMap_of_comp_eq p _ (P.comp_moduleDifferential π),
    ← SlashHomology.nullHomotopicMap_comp_of_comp_eq p _ (P.comp_moduleDifferential s),
    P.nullHomotopicMap_finsupp, LinearMap.id_comp]
  ext m; simpa [π] using (LinearMap.congr_fun hs m).symm

/-- **Projective `H`-modules have vanishing slash homology** in every degree `j : ℕ`. -/
theorem slashHomology_subsingleton_of_projective (P : TruncatedPrimitive (k := k) H p)
    [Module.Projective H M] (j : ℕ) :
    Subsingleton (SlashHomology p (P.moduleDifferential (M := M)) j) := by
  have hMap := SlashHomology.map_eq_of_isPHomotopic
    (P.moduleDifferential_pow_self (M := M)) (P.moduleDifferential_pow_self (M := M))
    (by simp : LinearMap.id ∘ₗ P.moduleDifferential = P.moduleDifferential ∘ₗ LinearMap.id)
    (by simp : (0 : M →ₗ[k] M) ∘ₗ P.moduleDifferential = P.moduleDifferential ∘ₗ 0)
    P.isPHomotopic_id_zero_of_projective j
  rw [SlashHomology.map_id, SlashHomology.map_zero] at hMap
  exact ⟨fun x y ↦ by
    have hx : x = 0 := by simpa using LinearMap.congr_fun hMap x
    have hy : y = 0 := by simpa using LinearMap.congr_fun hMap y
    rw [hx, hy]⟩

end Contractibility

end TruncatedPrimitive

/-! ### Khovanov–Qi's slash-homology projectivity detection theorem -/

section DetectionTheorem

variable {k : Type u} {H : Type v} {M : Type w}
  [Field k] [Semiring H] [Bialgebra k H] {p : ℕ}
  [AddCommGroup M] [Module k M] [Module H M] [IsScalarTower k H M]

/-- Over a field `k` (without assuming finite dimensionality, primality of `p`, or an antipode),
vanishing of all `p - 1` slash homology groups implies that `M` is a **free** `H`-module. -/
theorem TruncatedPrimitive.free_of_slashHomology_subsingleton
    (P : TruncatedPrimitive (k := k) H p)
    (hsub : ∀ j, j + 1 < p → Subsingleton (SlashHomology p (P.moduleDifferential (M := M)) j)) :
    Module.Free H M := by
  obtain ⟨ι, v, b, hb⟩ :=
    SlashHomology.exists_basis_pow_of_forall_subsingleton
      (P.moduleDifferential_pow_self (M := M)) hsub
  let Φ : (ι →₀ H) →ₗ[H] M := Finsupp.linearCombination H v
  let bFree : Module.Basis (ι × Fin p) k (ι →₀ H) :=
    (Finsupp.basis fun _ : ι ↦ P.basis).reindex (Equiv.sigmaEquivProd ι (Fin p))
  have hbij : Function.Bijective Φ := by
    rw [← LinearMap.coe_restrictScalars k]
    exact bFree.bijective_of_map_basis b (Φ.restrictScalars k) fun ⟨i, r⟩ ↦ by
      simp [bFree, Φ, hb i r, Equiv.sigmaEquivProd]
  exact Module.Free.of_basis (Module.Basis.ofRepr (LinearEquiv.ofBijective Φ hbij).symm)

/-- **Khovanov–Qi's slash-homology detection theorem** (Khovanov–Qi 2015, §2). Over a field `k`, a
left `H`-module `M` is projective over `H` iff all `p - 1` slash homology groups vanish. -/
theorem slashHomology_subsingleton_iff_projective (P : TruncatedPrimitive (k := k) H p) :
    (∀ j, j + 1 < p → Subsingleton (SlashHomology p (P.moduleDifferential (M := M)) j)) ↔
      Module.Projective H M :=
  ⟨fun hsub ↦ have := P.free_of_slashHomology_subsingleton hsub; inferInstance,
    fun _ j _ ↦ P.slashHomology_subsingleton_of_projective j⟩

/-- Over a field `k`, vanishing of all `p - 1` slash homology groups is also equivalent to `M`
being free over `H`; in particular, every projective `H`-module is free over `H`. -/
theorem slashHomology_subsingleton_iff_free (P : TruncatedPrimitive (k := k) H p) :
    (∀ j, j + 1 < p → Subsingleton (SlashHomology p (P.moduleDifferential (M := M)) j)) ↔
      Module.Free H M :=
  ⟨P.free_of_slashHomology_subsingleton,
    fun hfree ↦ have := hfree; (slashHomology_subsingleton_iff_projective P).mpr inferInstance⟩

end DetectionTheorem

/-! ### Explicit slash-homology calculations on the trivial module and cyclic quotients -/

namespace TruncatedPrimitive

section TrivialModule

variable {k : Type u} {H : Type v} [CommRing k] [Semiring H] [Bialgebra k H] {p : ℕ}

/-- For `2 ≤ p`, the `0`-th slash homology of `BialgebraModule.Trivial k H` is canonically
`k`-linearly isomorphic to `k`. -/
noncomputable def slashHomologyZeroTrivialEquiv (P : TruncatedPrimitive (k := k) H p)
    (hp : 2 ≤ p) :
    SlashHomology p (P.moduleDifferential (M := BialgebraModule.Trivial k H)) 0 ≃ₗ[k] k :=
  (SlashHomology.equiv p (LinearEquiv.refl k (BialgebraModule.Trivial k H)) (by simp) 0).trans <|
    (SlashHomology.zeroDiffZeroEquiv hp).trans (BialgebraModule.trivialEquiv k H)

/-- `slashHomologyZeroTrivialEquiv` sends the class of a cycle `z` to the underlying scalar. -/
@[simp]
theorem slashHomologyZeroTrivialEquiv_mk (P : TruncatedPrimitive (k := k) H p) (hp : 2 ≤ p)
    (z : LinearMap.ker ((P.moduleDifferential (M := BialgebraModule.Trivial k H)) ^ (0 + 1))) :
    P.slashHomologyZeroTrivialEquiv hp (Submodule.Quotient.mk z) =
      BialgebraModule.trivialEquiv k H z.val := by
  simp [slashHomologyZeroTrivialEquiv]

/-- The inverse of `slashHomologyZeroTrivialEquiv` sends `c : k` to the slash-homology class of
`(BialgebraModule.trivialEquiv k H).symm c`. -/
@[simp]
theorem slashHomologyZeroTrivialEquiv_symm_apply (P : TruncatedPrimitive (k := k) H p)
    (hp : 2 ≤ p) (c : k) :
    (P.slashHomologyZeroTrivialEquiv hp).symm c =
      Submodule.Quotient.mk ⟨(BialgebraModule.trivialEquiv k H).symm c, by simp⟩ := by
  apply (P.slashHomologyZeroTrivialEquiv hp).injective; simp

/-- For `0 < j`, the `j`-th slash homology of the counit trivial module vanishes. -/
theorem slashHomology_trivial_subsingleton_of_pos (P : TruncatedPrimitive (k := k) H p)
    {j : ℕ} (hj : 0 < j) :
    Subsingleton (SlashHomology p (P.moduleDifferential (M := BialgebraModule.Trivial k H)) j) := by
  rw [P.moduleDifferential_trivial_eq_zero]
  exact SlashHomology.subsingleton_zero_of_pos hj

/-- Over a nontrivial commutative ring `k`, `BialgebraModule.Trivial k H` is never projective over
`H` when `2 ≤ p`. -/
theorem not_projective_trivial [Nontrivial k] (P : TruncatedPrimitive (k := k) H p) (hp : 2 ≤ p) :
    ¬ Module.Projective H (BialgebraModule.Trivial k H) := fun _ ↦ by
  have := P.slashHomology_subsingleton_of_projective (M := BialgebraModule.Trivial k H) 0
  exact not_subsingleton k (P.slashHomologyZeroTrivialEquiv hp).symm.subsingleton

end TrivialModule

section CyclicQuotients

variable {k : Type u} {H : Type v} [CommRing k] [Ring H] [Bialgebra k H] {p : ℕ}

private noncomputable def quotientSpanPowLinearEquiv (P : TruncatedPrimitive (k := k) H p)
    {r : ℕ} (hr : r ≤ p) :
    (H ⧸ Ideal.span {P.d ^ r}) ≃ₗ[k] AdjoinRoot (X ^ r : k[X]) :=
  (Submodule.Quotient.restrictScalarsEquiv k (Ideal.span {P.d ^ r})).symm.trans <|
    (Submodule.Quotient.equiv _ _ P.adjoinRootAlgEquiv.symm.toLinearEquiv (by
      ext y
      simp only [Submodule.mem_map, Submodule.restrictScalars_mem, Ideal.mem_span_singleton',
        AlgEquiv.toLinearEquiv_toLinearMap, AlgEquiv.toLinearMap_apply]
      exact ⟨fun ⟨_, ⟨a, rfl⟩, hy⟩ ↦ ⟨P.adjoinRootAlgEquiv.symm a, by
          rw [← hy, map_mul, map_pow, P.adjoinRootAlgEquiv_symm_d]⟩,
        fun ⟨b, hb⟩ ↦ ⟨P.adjoinRootAlgEquiv b * P.d ^ r, ⟨P.adjoinRootAlgEquiv b, rfl⟩, by
          simpa [map_mul, map_pow] using hb⟩⟩)).trans <|
      (Submodule.Quotient.restrictScalarsEquiv k _).trans
        (AdjoinRoot.quotientSpanRootXPowAlgEquiv hr).toLinearEquiv

private theorem quotientSpanPowLinearEquiv_mk (P : TruncatedPrimitive (k := k) H p)
    {r : ℕ} (hr : r ≤ p) (x : H) :
    P.quotientSpanPowLinearEquiv hr (Submodule.Quotient.mk (p := Ideal.span {P.d ^ r}) x) =
      AdjoinRoot.quotientSpanRootXPowAlgEquiv hr
        (Ideal.Quotient.mk _ (P.adjoinRootAlgEquiv.symm x)) := by
  simp [quotientSpanPowLinearEquiv]

private theorem quotientSpanPowLinearEquiv_comp_moduleDifferential
    (P : TruncatedPrimitive (k := k) H p) {r : ℕ} (hr : r ≤ p) :
    (P.quotientSpanPowLinearEquiv hr).toLinearMap ∘ₗ
        P.moduleDifferential (M := H ⧸ Ideal.span {P.d ^ r}) =
      Algebra.lsmul k k (AdjoinRoot (X ^ r : k[X])) (AdjoinRoot.root (X ^ r : k[X])) ∘ₗ
        (P.quotientSpanPowLinearEquiv hr).toLinearMap := by
  ext q; obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [moduleDifferential_apply, ← Submodule.Quotient.mk_smul, smul_eq_mul,
    P.quotientSpanPowLinearEquiv_mk hr, P.quotientSpanPowLinearEquiv_mk hr, map_mul,
    P.adjoinRootAlgEquiv_symm_d, Algebra.lsmul_apply, smul_eq_mul, map_mul, map_mul,
    AdjoinRoot.quotientSpanRootXPowAlgEquiv_mk_root]

/-- **Monomial `k`-basis of cyclic quotients `H ⧸ (d ^ r)`.** For `r ≤ p`, the classes
`1, [d], …, [d ^ (r - 1)]` form a `k`-basis of `H ⧸ Ideal.span {P.d ^ r}`. -/
noncomputable def quotientSpanPowBasis (P : TruncatedPrimitive (k := k) H p) {r : ℕ}
    (hr : r ≤ p) : Module.Basis (Fin r) k (H ⧸ Ideal.span {P.d ^ r}) :=
  (AdjoinRoot.xPowBasis k r).map (P.quotientSpanPowLinearEquiv hr).symm

/-- The `i`-th basis vector of `P.quotientSpanPowBasis hr` is the class of `P.d ^ i`. -/
@[simp]
theorem quotientSpanPowBasis_apply (P : TruncatedPrimitive (k := k) H p) {r : ℕ}
    (hr : r ≤ p) (i : Fin r) :
    P.quotientSpanPowBasis hr i =
      Submodule.Quotient.mk (p := Ideal.span {P.d ^ r}) (P.d ^ (i : ℕ)) := by
  apply (P.quotientSpanPowLinearEquiv hr).injective
  simp [quotientSpanPowBasis, quotientSpanPowLinearEquiv_mk]

/-- For `r ≤ p`, the `k`-rank of the cyclic quotient `H ⧸ Ideal.span {P.d ^ r}` is `r`. -/
theorem finrank_quotient_span_pow [Nontrivial k] (P : TruncatedPrimitive (k := k) H p)
    {r : ℕ} (hr : r ≤ p) : Module.finrank k (H ⧸ Ideal.span {P.d ^ r}) = r := by
  rw [(P.quotientSpanPowLinearEquiv hr).finrank_eq,
    ← (AdjoinRoot.quotientSpanRootXPowAlgEquiv hr).toLinearEquiv.finrank_eq,
    AdjoinRoot.finrank_quotient_span_root_X_pow_pow hr]

/-- **Slash-homology ranks of cyclic quotients `H ⧸ (d ^ r)`.** Over any nontrivial commutative
ring `k`, for `r < p` and any `j : ℕ`, `SlashHomology p P.moduleDifferential j` on
`H ⧸ Ideal.span {P.d ^ r}` has `k`-rank `1` when `j < r` and `0` when `r ≤ j`. -/
theorem finrank_slashHomology_quotient_span_pow [Nontrivial k]
    (P : TruncatedPrimitive (k := k) H p) {r j : ℕ} (hr : r < p) :
    Module.finrank k
        (SlashHomology p (P.moduleDifferential (M := H ⧸ Ideal.span {P.d ^ r})) j) =
      if j < r then 1 else 0 := by
  rw [(SlashHomology.equiv p (P.quotientSpanPowLinearEquiv hr.le)
    (P.quotientSpanPowLinearEquiv_comp_moduleDifferential hr.le) j).finrank_eq,
    SlashHomology.finrank_adjoinRoot_X_pow hr]

/-- **No nontrivial proper cyclic quotient `H ⧸ (d ^ r)` (`1 ≤ r < p`) is projective over `H`.** -/
theorem not_projective_quotient_span_pow [Nontrivial k] (P : TruncatedPrimitive (k := k) H p)
    {r : ℕ} (hr₀ : 0 < r) (hr : r < p) :
    ¬ Module.Projective H (H ⧸ Ideal.span {P.d ^ r}) := fun _ ↦ by
  have := P.slashHomology_subsingleton_of_projective (M := H ⧸ Ideal.span {P.d ^ r}) 0
  have hfin := P.finrank_slashHomology_quotient_span_pow (j := 0) hr
  simp [hr₀, Module.finrank_zero_of_subsingleton] at hfin

end CyclicQuotients

end TruncatedPrimitive

end TauCeti

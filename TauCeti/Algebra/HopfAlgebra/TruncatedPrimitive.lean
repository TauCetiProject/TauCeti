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
public import TauCeti.Algebra.HopfAlgebra.HopfIdeal.Basic
public import TauCeti.Algebra.HopfAlgebra.SymmetricAlgebra.Basic
public import TauCeti.RingTheory.AdjoinRoot.Basic

import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.LinearAlgebra.TensorProduct.Basis
import TauCeti.Algebra.Bialgebra.Primitive
import TauCeti.Algebra.Bialgebra.Quotient

/-!
# Truncated primitive Hopf algebras and slash-homology projectivity detection

In characteristic `p`, the truncated polynomial algebra `H_p = k[d] / (d ^ p)` carries a
cocommutative Hopf algebra structure in which the generator `d` is primitive
(`Δ d = d ⊗ 1 + 1 ⊗ d`, `ε d = 0`, `S d = -d`). More generally, whenever all intermediate binomial
coefficients `n.choose i` (`0 < i < n`) vanish in `k` — for instance when `n = p ^ r` is any prime
power in characteristic `p` — `(1 + X) ^ n = 1 + X ^ n` in `k[X]`, so `(d ^ n)` is a Hopf ideal of
`k[d]`.

Left `H_p`-modules are `p`-complexes: multiplication by `d` defines a `k`-linear `p`-differential
`d_M` with `d_M ^ p = 0`, and because `Δ d = d ⊗ 1 + 1 ⊗ d` has no group-like twist, tensor
products of `H_p`-modules and left `H_p`-module algebras obey the **unsigned** Leibniz rule
`d(x ⊗ y) = d x ⊗ y + x ⊗ d y` without Koszul signs.

This file axiomatizes truncated primitive bialgebras (`TauCeti.TruncatedPrimitive`), constructs the
concrete Hopf algebras `TruncatedPrimitiveAlg R n = R[d] / (d ^ n)` for both prime and prime-power
exponents without importing scheme-theoretic machinery, proves uniqueness up to bialgebra
isomorphism, and establishes **Khovanov–Qi's slash-homology detection theorem**
(`TauCeti.slashHomology_subsingleton_iff_projective`): over a field `k`, a left `H`-module `M`
(finite- or infinite-dimensional) is projective — equivalently, free — over `H` if and only if all
`p - 1` slash homology groups `SlashHomology p P.moduleDifferential j` (`j + 1 < p`) vanish.

## Main definitions

* `TauCeti.TruncatedPrimitive`: a primitive generator `d ∈ H` with `d ^ p = 0` whose powers
  `1, d, …, d ^ (p - 1)` form a `k`-basis of `H`.
* `TauCeti.TruncatedPrimitive.moduleDifferential`: the `k`-linear `p`-differential `m ↦ d • m` on
  any left `H`-module `M`.
* `TauCeti.TruncatedPrimitiveAlg`: the quotient `SymmetricAlgebra R R ⧸ Ideal.span {ι 1 ^ n}`,
  equipped with `HopfAlgebra` structure whenever intermediate binomial coefficients vanish (with
  instances for `p` and `p ^ r` in characteristic `p`).
* `TauCeti.TruncatedPrimitiveAlg.truncatedPrimitive` and
  `TauCeti.TruncatedPrimitiveAlg.truncatedPrimitivePow`: canonical `TruncatedPrimitive` structures
  on `R[d] / (d ^ p)` and `R[d] / (d ^ (p ^ r))` in characteristic `p`.
* `TauCeti.TruncatedPrimitive.adjoinRootAlgEquiv` and
  `TauCeti.TruncatedPrimitive.bialgEquivTruncatedPrimitiveAlg`: algebra and bialgebra uniqueness of
  truncated primitive bialgebras.

## Main results

* `TauCeti.TruncatedPrimitive.natCast_choose_eq_zero`, `natCast_eq_zero`, `isEmpty_of_charZero`,
  `charP`: `TruncatedPrimitive H p` automatically forces `(p.choose i : k) = 0` (`0 < i < p`),
  hence `(p : k) = 0` for `2 ≤ p`, impossibility in characteristic zero, and `CharP k p` for prime
  `p` without assuming `CharP` in advance.
* `TauCeti.TruncatedPrimitive.moduleDifferential_tmul` and
  `TauCeti.TruncatedPrimitive.action_d_mul`: unsigned `p`-DG Leibniz rules on tensor products of
  `H`-modules and on left `H`-module algebras.
* `TauCeti.TruncatedPrimitive.isPHomotopic_id_zero_of_projective`: every projective `H`-module is
  `p`-contractible as a `p`-complex over `k`.
* `TauCeti.slashHomology_subsingleton_iff_projective` and
  `TauCeti.slashHomology_subsingleton_iff_free`: vanishing of all `p - 1` slash homology groups
  characterizes projective (and free) `H`-modules over a field `k`.
* `TauCeti.TruncatedPrimitive.finrank_slashHomology_quotient_span_pow` and
  `not_projective_quotient_span_pow`: explicit slash-homology dimensions (`1` for `j < r`, `0` for
  `r ≤ j < p - 1`) and non-projectivity of all nontrivial cyclic quotients `H ⧸ (d ^ r)`
  (`1 ≤ r < p`), together with the counit trivial module `BialgebraModule.Trivial k H`.

## Implementation notes

The Hopf-algebra structure on `TruncatedPrimitiveAlg R n` reuses `SymmetricAlgebra.instHopfAlgebra`
from `TauCeti.Algebra.HopfAlgebra.SymmetricAlgebra.Basic`, `HopfIdeal.ofSpan` from
`TauCeti.Algebra.HopfAlgebra.HopfIdeal.Basic`, and `TauCeti.Bialgebra.comul_pow_of_primitive` from
`TauCeti.Algebra.Bialgebra.Primitive`. At prime `n = p`, the underlying quotient ring and
`Ideal.IsHopfIdeal` instance agree definitionally with `TauCeti.AlphaP.CoordinateRing p`, while
remaining independent of algebraic geometry and extending to prime powers `p ^ r`. Algebra and
bialgebra classification reuse `AdjoinRoot.algHomEquiv` (`TauCeti.RingTheory.AdjoinRoot.Basic`) and
`Bialgebra.Quotient.liftBialgHom` (`TauCeti.Algebra.Bialgebra.Quotient`).

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
`d ∈ H` with `d ^ p = 0` whose powers `1, d, …, d ^ (p - 1)` form a `k`-basis of `H`.

Primality of `p` and characteristic `p` are not assumed:
`TruncatedPrimitive.natCast_choose_eq_zero` derives `(p.choose i : k) = 0` for all `0 < i < p` from
the bialgebra axioms, which covers both `H_p = k[d] / (d ^ p)` for prime `p` and iterated Frobenius
truncations `k[d] / (d ^ (p ^ r))` in characteristic `p`. -/
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

/-- A `TruncatedPrimitive` structure is uniquely determined by its generator `d`, because `basis`
is pinned pointwise by `basis_apply`. -/
@[ext]
theorem ext {P Q : TruncatedPrimitive (k := k) H p} (hd : P.d = Q.d) : P = Q := by
  cases P with
  | mk d₁ hc₁ hp₁ b₁ hb₁ =>
    cases Q with
    | mk d₂ hc₂ hp₂ b₂ hb₂ =>
      simp only at hd
      subst hd
      congr
      ext i
      rw [hb₁, hb₂]

/-- Over a nontrivial `k`-bialgebra `H`, the truncation exponent `p` is positive. -/
theorem pos [Nontrivial H] (P : TruncatedPrimitive (k := k) H p) : 0 < p := by
  by_contra hp
  have hp0 : p = 0 := by omega
  subst hp0
  have h1 : (1 : H) = 0 := by simpa using P.pow_d
  exact one_ne_zero h1

/-- When `2 ≤ p` and `k` is nontrivial, the generator `d` is nonzero. -/
theorem d_ne_zero [Nontrivial k] (P : TruncatedPrimitive (k := k) H p) (hp : 2 ≤ p) :
    P.d ≠ 0 := by
  have hb := P.basis.ne_zero ⟨1, by omega⟩
  rwa [P.basis_apply, pow_one] at hb

/-- **Binomial obstruction.** Every intermediate binomial coefficient `p.choose i` (`0 < i < p`)
vanishes in `k`: expanding `0 = Δ(d ^ p) = (d ⊗ 1 + 1 ⊗ d) ^ p` in the tensor basis `d ^ a ⊗ d ^ b`
isolates `(p.choose i : k)` as the `(i, p - i)` coordinate. -/
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
    rw [← Nat.cast_smul_eq_nsmul k, hb, map_smul, Module.Basis.coord_apply,
      Module.Basis.repr_self, Finsupp.single_eq_same, smul_eq_mul, mul_one] at hcoord
    exact hcoord
  · rintro ⟨a, b⟩ hab hne
    rw [Finset.mem_antidiagonal] at hab
    rcases Nat.eq_zero_or_pos a with rfl | ha0
    · have hb_eq : b = p := by simpa using hab
      simp [hb_eq, P.pow_d]
    · rcases Nat.eq_zero_or_pos b with rfl | hb0
      · have ha_eq : a = p := by simpa using hab
        simp [ha_eq, P.pow_d]
      · have ha : a < p := by omega
        have hb : b < p := by omega
        have hb_vec : (P.d ^ a) ⊗ₜ[k] (P.d ^ b) = B (⟨a, ha⟩, ⟨b, hb⟩) := by
          simp [B, Module.Basis.tensorProduct_apply]
        have hidx_ne : (⟨a, ha⟩, ⟨b, hb⟩) ≠ idx := fun heq ↦
          hne <| Prod.ext (congrArg (fun x : Fin p × Fin p ↦ (x.1 : ℕ)) heq)
            (congrArg (fun x : Fin p × Fin p ↦ (x.2 : ℕ)) heq)
        rw [← Nat.cast_smul_eq_nsmul k, hb_vec, map_smul, Module.Basis.coord_apply,
          Module.Basis.repr_self, Finsupp.single_eq_of_ne hidx_ne.symm, smul_zero]
  · exact fun hmem ↦ absurd (Finset.mem_antidiagonal.mpr (by omega)) hmem

/-- **Characteristic forcing.** Any `TruncatedPrimitive H p` with `2 ≤ p` forces `(p : k) = 0` in
the base semiring `k`. -/
theorem natCast_eq_zero (P : TruncatedPrimitive (k := k) H p) (hp : 2 ≤ p) : (p : k) = 0 := by
  simpa [Nat.choose_one_right] using P.natCast_choose_eq_zero Nat.zero_lt_one hp

/-- **Characteristic-zero obstruction.** Over a characteristic-zero base semiring (such as `ℕ`,
`ℤ`, or `ℚ`), there is no `TruncatedPrimitive H p` for `2 ≤ p`. -/
theorem isEmpty_of_charZero [CharZero k] (hp : 2 ≤ p) :
    IsEmpty (TruncatedPrimitive (k := k) H p) :=
  ⟨fun P ↦ (Nat.cast_ne_zero.mpr (by omega : p ≠ 0)) (P.natCast_eq_zero hp)⟩

/-- When `p` is prime and `k` is nontrivial, the existence of `TruncatedPrimitive H p`
automatically forces `CharP k p` without assuming it as a hypothesis. -/
theorem charP [Nontrivial k] [Fact p.Prime] (P : TruncatedPrimitive (k := k) H p) :
    CharP k p :=
  (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr
    (P.natCast_eq_zero (Fact.out : p.Prime).two_le)

/-- When `p` is prime and `k` is nontrivial, `ringChar k = p`. -/
theorem ringChar_eq [Nontrivial k] [Fact p.Prime] (P : TruncatedPrimitive (k := k) H p) :
    ringChar k = p := by
  have := P.charP
  exact ringChar.eq k p

/-- The `k`-rank of `H` is `p`. -/
theorem finrank_eq [StrongRankCondition k] (P : TruncatedPrimitive (k := k) H p) :
    Module.finrank k H = p := by
  rw [Module.finrank_eq_card_basis P.basis, Fintype.card_fin]

end Semiring

section Ring

variable {k : Type u} {H : Type v} [CommRing k] [Ring H] [Bialgebra k H] {p : ℕ}

/-- The generator `d` is a primitive element in Mathlib's `Bialgebra.IsPrimitiveElem` sense. -/
theorem isPrimitiveElem_d (P : TruncatedPrimitive (k := k) H p) :
    Bialgebra.IsPrimitiveElem k P.d :=
  Bialgebra.isPrimitiveElem_iff_comul_eq_tmul_add_tmul.mpr (by rw [P.comul_d, add_comm])

/-- The counit vanishes on `d`. -/
@[simp]
theorem counit_d (P : TruncatedPrimitive (k := k) H p) :
    Coalgebra.counit (R := k) P.d = 0 :=
  P.isPrimitiveElem_d.counit_eq_zero

/-- In a Hopf algebra, the antipode sends `d` to `-d`. -/
@[simp]
theorem antipode_d {H : Type v} [Ring H] [HopfAlgebra k H]
    (P : TruncatedPrimitive (k := k) H p) :
    HopfAlgebra.antipode k P.d = -P.d :=
  P.isPrimitiveElem_d.antipode_eq_neg

/-- **Algebra classification.** Every `p`-truncated primitive bialgebra `H` over a commutative ring
`k` is canonically `k`-algebra isomorphic to `AdjoinRoot (X ^ p : k[X]) = k[X] / (X ^ p)`, sending
the root `X` to `P.d`. -/
noncomputable def adjoinRootAlgEquiv (P : TruncatedPrimitive (k := k) H p) :
    AdjoinRoot (X ^ p : k[X]) ≃ₐ[k] H := by
  let φ : AdjoinRoot (X ^ p : k[X]) →ₐ[k] H :=
    (AdjoinRoot.algHomEquiv H (X ^ p : k[X])).symm ⟨P.d, by simp [P.pow_d]⟩
  have hroot : φ (AdjoinRoot.root (X ^ p : k[X])) = P.d :=
    AdjoinRoot.algHomEquiv_symm_apply_root _
  refine AlgEquiv.ofBijective φ ?_
  rcases subsingleton_or_nontrivial k with hk | hk
  · have : Subsingleton (AdjoinRoot (X ^ p : k[X])) := Module.subsingleton k _
    have : Subsingleton H := Module.subsingleton k _
    exact ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun _ ↦ ⟨0, Subsingleton.elim _ _⟩⟩
  · rcases Nat.eq_zero_or_pos p with rfl | _
    · have h1 : (1 : AdjoinRoot (X ^ 0 : k[X])) = 0 := by
        rw [← map_one (AdjoinRoot.mk (X ^ 0 : k[X])), ← pow_zero X, AdjoinRoot.mk_self]
      have : Subsingleton (AdjoinRoot (X ^ 0 : k[X])) := subsingleton_of_zero_eq_one h1.symm
      have : Subsingleton H :=
        subsingleton_of_zero_eq_one (by simpa using P.pow_d.symm)
      exact ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun _ ↦ ⟨0, Subsingleton.elim _ _⟩⟩
    · let pb := AdjoinRoot.powerBasis' (monic_X_pow (R := k) p)
      have hdim : pb.dim = p := by rw [AdjoinRoot.powerBasis'_dim, natDegree_X_pow]
      let b₀ : Module.Basis (Fin p) k (AdjoinRoot (X ^ p : k[X])) :=
        pb.basis.reindex (finCongr hdim)
      have hφ_eq : φ.toLinearMap = (b₀.equiv P.basis (Equiv.refl _)).toLinearMap := by
        apply b₀.ext
        intro i
        rw [AlgHom.toLinearMap_apply, LinearEquiv.coe_toLinearMap, Module.Basis.equiv_apply,
          Equiv.refl_apply, P.basis_apply]
        simp [b₀, pb, hroot]
      rw [← AlgHom.coe_toLinearMap, hφ_eq]
      exact (b₀.equiv P.basis (Equiv.refl _)).bijective

/-- `adjoinRootAlgEquiv` sends the class of `X` to `P.d`. -/
@[simp]
theorem adjoinRootAlgEquiv_root (P : TruncatedPrimitive (k := k) H p) :
    P.adjoinRootAlgEquiv (AdjoinRoot.root (X ^ p : k[X])) = P.d :=
  AdjoinRoot.algHomEquiv_symm_apply_root _

/-- Multiplication in any `TruncatedPrimitive` bialgebra over a commutative ring is commutative. -/
theorem mul_comm (P : TruncatedPrimitive (k := k) H p) (x y : H) : x * y = y * x := by
  obtain ⟨a, rfl⟩ := P.adjoinRootAlgEquiv.surjective x
  obtain ⟨b, rfl⟩ := P.adjoinRootAlgEquiv.surjective y
  rw [← map_mul, _root_.mul_comm a b, map_mul]

end Ring

end TruncatedPrimitive

/-! ### The concrete Hopf algebra `TruncatedPrimitiveAlg R n = R[d] / (d ^ n)` -/

/-- The truncated polynomial algebra `R[d] / (d ^ n)`, realized as the quotient of the rank-one
symmetric algebra `SymmetricAlgebra R R` by `(ι 1 ^ n)` so that Mathlib's quotient bialgebra and
Hopf-algebra instances fire directly whenever `(ι 1 ^ n)` is a Hopf ideal. -/
abbrev TruncatedPrimitiveAlg (R : Type u) [CommRing R] (n : ℕ) : Type u :=
  SymmetricAlgebra R R ⧸ Ideal.span {(SymmetricAlgebra.ι R R 1 : SymmetricAlgebra R R) ^ n}

namespace TruncatedPrimitiveAlg

section CommRing

variable {R : Type u} [CommRing R]

/-- The distinguished generator `d` of `TruncatedPrimitiveAlg R n`, the image of `ι R R 1`. -/
def d (R : Type u) [CommRing R] (n : ℕ) : TruncatedPrimitiveAlg R n :=
  Ideal.Quotient.mk _ (SymmetricAlgebra.ι R R 1)

/-- In `TruncatedPrimitiveAlg R n`, `d ^ n = 0`. -/
@[simp]
theorem pow_d (R : Type u) [CommRing R] (n : ℕ) : (d R n) ^ n = 0 := by
  rw [d, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_span_singleton_self _

/-- Canonical `R`-algebra equivalence `SymmetricAlgebra R R ≃ₐ[R] R[X]` sending `ι R R 1` to `X`. -/
noncomputable def symmetricAlgebraAlgEquivPolynomial (R : Type u) [CommRing R] :
    SymmetricAlgebra R R ≃ₐ[R] R[X] :=
  AlgEquiv.ofAlgHom
    (SymmetricAlgebra.lift (LinearMap.toSpanSingleton R R[X] X))
    (aeval (SymmetricAlgebra.ι R R 1))
    (Polynomial.algHom_ext <| by simp)
    (SymmetricAlgebra.algHom_ext <| LinearMap.ext_ring <| by simp)

/-- `symmetricAlgebraAlgEquivPolynomial` sends the generator `ι R R 1` to `X`. -/
@[simp]
theorem symmetricAlgebraAlgEquivPolynomial_ι_one (R : Type u) [CommRing R] :
    symmetricAlgebraAlgEquivPolynomial R (SymmetricAlgebra.ι R R 1) = X := by
  simp [symmetricAlgebraAlgEquivPolynomial]

/-- The inverse of `symmetricAlgebraAlgEquivPolynomial` sends `X` to `ι R R 1`. -/
@[simp]
theorem symmetricAlgebraAlgEquivPolynomial_symm_X (R : Type u) [CommRing R] :
    (symmetricAlgebraAlgEquivPolynomial R).symm X = SymmetricAlgebra.ι R R 1 := by
  simp [symmetricAlgebraAlgEquivPolynomial]

/-- Canonical `R`-algebra equivalence
`TruncatedPrimitiveAlg R n ≃ₐ[R] AdjoinRoot (X ^ n : R[X])`. -/
noncomputable def algEquivAdjoinRoot (R : Type u) [CommRing R] (n : ℕ) :
    TruncatedPrimitiveAlg R n ≃ₐ[R] AdjoinRoot (X ^ n : R[X]) :=
  Ideal.quotientEquivAlg
    (Ideal.span {(SymmetricAlgebra.ι R R 1 : SymmetricAlgebra R R) ^ n})
    (Ideal.span {(X ^ n : R[X])})
    (symmetricAlgebraAlgEquivPolynomial R)
    (by simp [Ideal.map_span])

/-- `algEquivAdjoinRoot` sends `d R n` to the root `X` of `AdjoinRoot (X ^ n)`. -/
@[simp]
theorem algEquivAdjoinRoot_d (R : Type u) [CommRing R] (n : ℕ) :
    algEquivAdjoinRoot R n (d R n) = AdjoinRoot.root (X ^ n : R[X]) :=
  (Ideal.quotientEquivAlg_mk _ _ _ (SymmetricAlgebra.ι R R 1)).trans
    (congrArg (Ideal.Quotient.mk _) (symmetricAlgebraAlgEquivPolynomial_ι_one R))

/-- The inverse of `algEquivAdjoinRoot` sends the root `X` to `d R n`. -/
@[simp]
theorem algEquivAdjoinRoot_symm_root (R : Type u) [CommRing R] (n : ℕ) :
    (algEquivAdjoinRoot R n).symm (AdjoinRoot.root (X ^ n : R[X])) = d R n := by
  apply (algEquivAdjoinRoot R n).injective
  simp

/-- Monomial `R`-basis `1, d, …, d ^ (n - 1)` of `TruncatedPrimitiveAlg R n` for any `n : ℕ`. -/
noncomputable def basis (R : Type u) [CommRing R] :
    (n : ℕ) → Module.Basis (Fin n) R (TruncatedPrimitiveAlg R n)
  | 0 =>
    letI : Subsingleton (TruncatedPrimitiveAlg R 0) :=
      subsingleton_of_zero_eq_one (by simpa using (pow_d R 0).symm)
    Module.Basis.empty _
  | n + 1 => by
    classical
    exact
      if hR : Subsingleton R then
        letI : Subsingleton (TruncatedPrimitiveAlg R (n + 1)) := Module.subsingleton R _
        letI : Subsingleton (Fin (n + 1) →₀ R) := Module.subsingleton R _
        Module.Basis.ofRepr
          { toFun := 0
            invFun := 0
            left_inv := fun _ ↦ Subsingleton.elim _ _
            right_inv := fun _ ↦ Subsingleton.elim _ _
            map_add' := fun _ _ ↦ Subsingleton.elim _ _
            map_smul' := fun _ _ ↦ Subsingleton.elim _ _ }
      else
        letI : Nontrivial R := not_subsingleton_iff_nontrivial.mp hR
        let pb := AdjoinRoot.powerBasis' (monic_X_pow (R := R) (n + 1))
        have hdim : pb.dim = n + 1 := by rw [AdjoinRoot.powerBasis'_dim, natDegree_X_pow]
        (pb.basis.reindex (finCongr hdim)).map
          (algEquivAdjoinRoot R (n + 1)).symm.toLinearEquiv

/-- The `i`-th element of `TruncatedPrimitiveAlg.basis R n` is `d ^ i`. -/
@[simp]
theorem basis_apply (R : Type u) [CommRing R] (n : ℕ) (i : Fin n) :
    basis R n i = (d R n) ^ (i : ℕ) := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ m =>
    unfold basis
    split_ifs with hR
    · have : Subsingleton (TruncatedPrimitiveAlg R (m + 1)) := Module.subsingleton R _
      exact Subsingleton.elim _ _
    · simp

/-- When `0 < n` and all intermediate binomial coefficients `n.choose i` (`0 < i < n`) vanish in
`R`, `Δ(ι 1 ^ n) = ι 1 ^ n ⊗ 1 + 1 ⊗ ι 1 ^ n` in `SymmetricAlgebra R R`. -/
theorem comul_ι_one_pow_of_choose_eq_zero {n : ℕ} (hn : 0 < n)
    (hchoose : ∀ ⦃i : ℕ⦄, 0 < i → i < n → (n.choose i : R) = 0) :
    Coalgebra.comul (R := R) ((SymmetricAlgebra.ι R R 1 : SymmetricAlgebra R R) ^ n) =
      ((SymmetricAlgebra.ι R R 1 : SymmetricAlgebra R R) ^ n) ⊗ₜ[R] 1 +
        1 ⊗ₜ[R] ((SymmetricAlgebra.ι R R 1 : SymmetricAlgebra R R) ^ n) := by
  rw [TauCeti.Bialgebra.comul_pow_of_primitive _ (SymmetricAlgebra.comul_ι R R 1) n]
  have hmem0 : (0, n) ∈ Finset.antidiagonal n := Finset.mem_antidiagonal.mpr (zero_add n)
  have hmemn : (n, 0) ∈ Finset.antidiagonal n := Finset.mem_antidiagonal.mpr (add_zero n)
  rw [← Finset.add_sum_erase _ _ hmemn]
  have hmem0' : (0, n) ∈ (Finset.antidiagonal n).erase (n, 0) :=
    Finset.mem_erase.mpr ⟨fun h ↦ hn.ne (Prod.mk.inj h).1, hmem0⟩
  rw [← Finset.add_sum_erase _ _ hmem0']
  have hrest :
      ∑ ij ∈ ((Finset.antidiagonal n).erase (n, 0)).erase (0, n),
          n.choose ij.1 •
            ((SymmetricAlgebra.ι R R 1 ^ ij.1) ⊗ₜ[R] (SymmetricAlgebra.ι R R 1 ^ ij.2)) = 0 := by
    refine Finset.sum_eq_zero fun ⟨a, b⟩ hab ↦ ?_
    have hne0 : (a, b) ≠ (0, n) := (Finset.mem_erase.mp hab).1
    have hab' := (Finset.mem_erase.mp hab).2
    have hnen : (a, b) ≠ (n, 0) := (Finset.mem_erase.mp hab').1
    have hsum : a + b = n := Finset.mem_antidiagonal.mp (Finset.mem_erase.mp hab').2
    have ha0 : 0 < a := Nat.pos_of_ne_zero fun ha ↦ hne0 (Prod.ext ha (by omega))
    have han : a < n := lt_of_le_of_ne (by omega) fun ha ↦ hnen (Prod.ext ha (by omega))
    rw [← Nat.cast_smul_eq_nsmul R, hchoose ha0 han, zero_smul]
  rw [hrest, add_zero]
  simp

/-- **General Hopf-ideal constructor.** Whenever `0 < n` and all intermediate binomial coefficients
`n.choose i` (`0 < i < n`) vanish in `R`, the ideal `(ι 1 ^ n)` of `SymmetricAlgebra R R` is a
Hopf ideal. -/
noncomputable def hopfIdeal {n : ℕ} (hn : 0 < n)
    (hchoose : ∀ ⦃i : ℕ⦄, 0 < i → i < n → (n.choose i : R) = 0) :
    HopfIdeal R (SymmetricAlgebra R R) :=
  HopfIdeal.ofSpan {(SymmetricAlgebra.ι R R 1 : SymmetricAlgebra R R) ^ n}
    (by
      rintro _ rfl
      rw [comul_ι_one_pow_of_choose_eq_zero hn hchoose]
      exact Ideal.add_mem _
        (Ideal.mem_sup_left
          (Ideal.tmul_mem_leftTensorIdeal (R := R) (B := SymmetricAlgebra R R)
            (Ideal.mem_span_singleton_self _) 1))
        (Ideal.mem_sup_right
          (Ideal.tmul_mem_rightTensorIdeal (R := R) (A := SymmetricAlgebra R R) 1
            (Ideal.mem_span_singleton_self _))))
    (by
      rintro _ rfl
      rw [Bialgebra.counit_pow, SymmetricAlgebra.counit_ι, zero_pow hn.ne'])
    (by
      rintro _ rfl
      have hpow :
          HopfAlgebra.antipode R ((SymmetricAlgebra.ι R R 1 : SymmetricAlgebra R R) ^ n) =
            (HopfAlgebra.antipode R (SymmetricAlgebra.ι R R 1 : SymmetricAlgebra R R)) ^ n :=
        map_pow (HopfAlgebra.antipodeAlgHom R _) _ _
      rw [hpow, SymmetricAlgebra.antipode_ι, neg_pow]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))

/-- `hopfIdeal` yields Mathlib's `Ideal.IsHopfIdeal` on `Ideal.span {ι 1 ^ n}`. -/
theorem isHopfIdeal_of_choose_eq_zero {n : ℕ} (hn : 0 < n)
    (hchoose : ∀ ⦃i : ℕ⦄, 0 < i → i < n → (n.choose i : R) = 0) :
    (Ideal.span {(SymmetricAlgebra.ι R R 1 : SymmetricAlgebra R R) ^ n}).IsHopfIdeal R := by
  have hI := HopfIdeal.instIsHopfIdeal (hopfIdeal hn hchoose)
  rwa [hopfIdeal, HopfIdeal.ofSpan_toIdeal] at hI

/-- Build a `TruncatedPrimitive` structure on `TruncatedPrimitiveAlg R n` inside a scope where
`Ideal.IsHopfIdeal` has been supplied. -/
noncomputable def mkTruncatedPrimitive (R : Type u) [CommRing R] (n : ℕ)
    [hI : (Ideal.span {(SymmetricAlgebra.ι R R 1 : SymmetricAlgebra R R) ^ n}).IsHopfIdeal R] :
    TruncatedPrimitive (k := R) (TruncatedPrimitiveAlg R n) n where
  d := d R n
  comul_d := by
    rw [d, ← Bialgebra.Quotient.mkBialgHom_apply (R := R),
      ← CoalgHomClass.map_comp_comul_apply, SymmetricAlgebra.comul_ι]
    rfl
  pow_d := pow_d R n
  basis := basis R n
  basis_apply := basis_apply R n

/-- In characteristic `p` (`p` prime), `(ι 1 ^ (p ^ r))` is a Hopf ideal of `SymmetricAlgebra R R`
for every `r : ℕ` (for instance `R[d] / (d ^ 4)` in characteristic `2`). -/
instance instIsHopfIdealPrimePow (p r : ℕ) [Fact p.Prime] [CharP R p] :
    (Ideal.span {(SymmetricAlgebra.ι R R 1 : SymmetricAlgebra R R) ^ (p ^ r)}).IsHopfIdeal R :=
  isHopfIdeal_of_choose_eq_zero (pow_pos (Fact.out : p.Prime).pos r) fun _ hi₀ hi ↦
    (CharP.cast_eq_zero_iff R p _).mpr
      (Nat.Prime.dvd_choose_pow (Fact.out : p.Prime) hi₀.ne' hi.ne)

/-- In characteristic `p` (`p` prime), `(ι 1 ^ p)` is a Hopf ideal of `SymmetricAlgebra R R`, so
`TruncatedPrimitiveAlg R p = R[d] / (d ^ p)` inherits `HopfAlgebra R` structure. -/
instance instIsHopfIdealPrime (p : ℕ) [Fact p.Prime] [CharP R p] :
    (Ideal.span {(SymmetricAlgebra.ι R R 1 : SymmetricAlgebra R R) ^ p}).IsHopfIdeal R := by
  simpa using instIsHopfIdealPrimePow (R := R) p 1

/-- **Canonical `p`-truncated primitive Hopf algebra `H_p = R[d] / (d ^ p)`.** -/
noncomputable def truncatedPrimitive (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p] :
    TruncatedPrimitive (k := R) (TruncatedPrimitiveAlg R p) p :=
  mkTruncatedPrimitive R p

/-- The distinguished generator of `truncatedPrimitive R p` is `d R p`. -/
@[simp]
theorem truncatedPrimitive_d (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p] :
    (truncatedPrimitive R p).d = d R p :=
  (rfl)

/-- **Iterated Frobenius truncation `R[d] / (d ^ (p ^ r))`.** In characteristic `p`,
`TruncatedPrimitive` also holds at non-prime prime powers `p ^ r` (such as `R[d] / (d ^ 4)` in
characteristic `2`). -/
noncomputable def truncatedPrimitivePow (R : Type u) [CommRing R] (p r : ℕ)
    [Fact p.Prime] [CharP R p] :
    TruncatedPrimitive (k := R) (TruncatedPrimitiveAlg R (p ^ r)) (p ^ r) :=
  mkTruncatedPrimitive R (p ^ r)

/-- The distinguished generator of `truncatedPrimitivePow R p r` is `d R (p ^ r)`. -/
@[simp]
theorem truncatedPrimitivePow_d (R : Type u) [CommRing R] (p r : ℕ)
    [Fact p.Prime] [CharP R p] :
    (truncatedPrimitivePow R p r).d = d R (p ^ r) :=
  (rfl)

end CommRing

end TruncatedPrimitiveAlg

/-- **Bialgebra uniqueness.** For `0 < p`, every `p`-truncated primitive bialgebra `H` over a
commutative ring `k` is canonically bialgebra-isomorphic to
`TruncatedPrimitiveAlg k p = k[d] / (d ^ p)` (equipped with the Hopf-ideal structure induced by
`P.natCast_choose_eq_zero`). -/
noncomputable def TruncatedPrimitive.bialgEquivTruncatedPrimitiveAlg
    {k : Type u} {H : Type v} [CommRing k] [Ring H] [Bialgebra k H] {p : ℕ}
    (P : TruncatedPrimitive (k := k) H p) (hp : 0 < p) :
    letI : (Ideal.span {(SymmetricAlgebra.ι k k 1 : SymmetricAlgebra k k) ^ p}).IsHopfIdeal k :=
      TruncatedPrimitiveAlg.isHopfIdeal_of_choose_eq_zero hp fun _ hi₀ hi ↦
        P.natCast_choose_eq_zero hi₀ hi
    TruncatedPrimitiveAlg k p ≃ₐc[k] H := by
  letI : (Ideal.span {(SymmetricAlgebra.ι k k 1 : SymmetricAlgebra k k) ^ p}).IsHopfIdeal k :=
    TruncatedPrimitiveAlg.isHopfIdeal_of_choose_eq_zero hp fun _ hi₀ hi ↦
      P.natCast_choose_eq_zero hi₀ hi
  letI : CommRing H := { (inferInstance : Ring H) with mul_comm := P.mul_comm }
  let fAlg : SymmetricAlgebra k k →ₐ[k] H :=
    SymmetricAlgebra.lift (LinearMap.toSpanSingleton k H P.d)
  have hcounit : (Bialgebra.counitAlgHom k H).comp fAlg =
      Bialgebra.counitAlgHom k (SymmetricAlgebra k k) :=
    SymmetricAlgebra.algHom_ext <| LinearMap.ext_ring <| by
      simp [fAlg, SymmetricAlgebra.algebraMapInv_ι]
  have hcomul :
      (Algebra.TensorProduct.map fAlg fAlg).comp (Bialgebra.comulAlgHom k _) =
        (Bialgebra.comulAlgHom k H).comp fAlg :=
    SymmetricAlgebra.algHom_ext <| LinearMap.ext_ring <| by simp [fAlg]
  let fSym : SymmetricAlgebra k k →ₐc[k] H := BialgHom.ofAlgHom fAlg hcounit hcomul
  have hker :
       Ideal.span {(SymmetricAlgebra.ι k k 1 : SymmetricAlgebra k k) ^ p} ≤
        RingHom.ker fSym.toAlgHom.toRingHom := by
    rw [Ideal.span_le]
    rintro _ rfl
    simp [fSym, fAlg, P.pow_d]
  let φ := Bialgebra.Quotient.liftBialgHom
    (Ideal.span {(SymmetricAlgebra.ι k k 1 : SymmetricAlgebra k k) ^ p}) fSym hker
  have hφ_d : φ (TruncatedPrimitiveAlg.d k p) = P.d := by
    simp [φ, TruncatedPrimitiveAlg.d, fSym, fAlg]
  have hφ_lin :
      φ.toAlgHom.toLinearMap =
        ((TruncatedPrimitiveAlg.basis k p).equiv P.basis (Equiv.refl _)).toLinearMap := by
    apply (TruncatedPrimitiveAlg.basis k p).ext
    intro i
    rw [AlgHom.toLinearMap_apply, LinearEquiv.coe_toLinearMap, Module.Basis.equiv_apply,
      Equiv.refl_apply, TruncatedPrimitiveAlg.basis_apply, P.basis_apply, map_pow]
    exact congrArg (· ^ (i : ℕ)) hφ_d
  refine BialgEquiv.ofBijective φ ?_
  have hcoe : (φ : TruncatedPrimitiveAlg k p → H) =
      (TruncatedPrimitiveAlg.basis k p).equiv P.basis (Equiv.refl _) :=
    congrArg DFunLike.coe hφ_lin
  rw [hcoe]
  exact ((TruncatedPrimitiveAlg.basis k p).equiv P.basis (Equiv.refl _)).bijective

/-! ### The `p`-differential on left `H`-modules, unsigned Leibniz rules, and functoriality -/

namespace TruncatedPrimitive

section ModuleDifferential

variable {k : Type u} {H : Type v} [CommSemiring k] [Semiring H] [Bialgebra k H] {p : ℕ}

/-- Multiplication by the generator `P.d` as a `k`-linear endomorphism of any left `H`-module `M`.
Because `k` acts centrally through `algebraMap k H`, `P.d • ·` is `k`-linear and satisfies
`moduleDifferential ^ p = 0`. -/
def moduleDifferential (P : TruncatedPrimitive (k := k) H p) {M : Type w}
    [AddCommMonoid M] [Module k M] [Module H M] [IsScalarTower k H M] : M →ₗ[k] M where
  toFun m := P.d • m
  map_add' := smul_add P.d
  map_smul' c m := by
    rw [RingHom.id_apply, ← algebraMap_smul H c m, ← algebraMap_smul H c (P.d • m),
      ← mul_smul, ← mul_smul, Algebra.commutes]

/-- `P.moduleDifferential` acts by `P.d • m`. -/
@[simp]
theorem moduleDifferential_apply (P : TruncatedPrimitive (k := k) H p) {M : Type w}
    [AddCommMonoid M] [Module k M] [Module H M] [IsScalarTower k H M] (m : M) :
    P.moduleDifferential m = P.d • m :=
  (rfl)

/-- Iterates of `P.moduleDifferential` act by `(P.d ^ r) • m`. -/
@[simp]
theorem moduleDifferential_pow_apply (P : TruncatedPrimitive (k := k) H p) {M : Type w}
    [AddCommMonoid M] [Module k M] [Module H M] [IsScalarTower k H M] (r : ℕ) (m : M) :
    ((P.moduleDifferential (M := M)) ^ r) m = (P.d ^ r) • m := by
  induction r with
  | zero => simp [Module.End.one_eq_id]
  | succ r ih =>
    rw [pow_succ', mul_apply_eq_comp, ih, moduleDifferential_apply, pow_succ', mul_smul]

/-- On every left `H`-module `M`, `P.moduleDifferential ^ p = 0`. -/
@[simp]
theorem moduleDifferential_pow_self (P : TruncatedPrimitive (k := k) H p) {M : Type w}
    [AddCommMonoid M] [Module k M] [Module H M] [IsScalarTower k H M] :
    (P.moduleDifferential (M := M)) ^ p = 0 := by
  ext m
  simp [P.pow_d]

/-- **Unsigned tensor-product Leibniz rule.** Because `Δ d = d ⊗ 1 + 1 ⊗ d` has no group-like
twist, `P.moduleDifferential` acts on `BialgebraModule.Tensor k H M N` by
`d(m ⊗ n) = d m ⊗ n + m ⊗ d n` with no Koszul sign. -/
theorem moduleDifferential_tmul (P : TruncatedPrimitive (k := k) H p)
    {M N : Type*} [AddCommMonoid M] [Module k M] [Module H M] [IsScalarTower k H M]
    [AddCommMonoid N] [Module k N] [Module H N] [IsScalarTower k H N] (m : M) (n : N) :
    P.moduleDifferential (BialgebraModule.tmul k H m n) =
      BialgebraModule.tmul k H (P.moduleDifferential m) n +
        BialgebraModule.tmul k H m (P.moduleDifferential n) := by
  apply (BialgebraModule.tensorEquiv k H M N).injective
  simp [BialgebraModule.tensorAction_apply, P.comul_d]

/-- **Unsigned `p`-DG Leibniz rule on left module algebras.** On any left `H`-module algebra `A`,
the primitive generator `P.d` acts as an unsigned `k`-derivation:
`d · (a * b) = (d · a) * b + a * (d · b)`. -/
theorem action_d_mul (P : TruncatedPrimitive (k := k) H p) {A : Type*} [Semiring A] [Algebra k A]
    (μ : LeftModuleAlgebra k H A) (a b : A) :
    μ.action P.d (a * b) = μ.action P.d a * b + a * μ.action P.d b := by
  rw [μ.action_mul]
  simp [AlgHom.comp_apply, P.comul_d, Module.endTensorEndAlgHom_apply]

/-- Every `H`-linear map `f : M →ₗ[H] N` intertwines `P.moduleDifferential` after restricting
scalars to `k`. -/
theorem comp_moduleDifferential (P : TruncatedPrimitive (k := k) H p)
    {M N : Type*} [AddCommMonoid M] [Module k M] [Module H M] [IsScalarTower k H M]
    [AddCommMonoid N] [Module k N] [Module H N] [IsScalarTower k H N] (f : M →ₗ[H] N) :
    f.restrictScalars k ∘ₗ P.moduleDifferential = P.moduleDifferential ∘ₗ f.restrictScalars k := by
  ext m
  simp

end ModuleDifferential

section FunctorialityAndContractibility

variable {k : Type u} {H : Type v} [CommRing k] [Ring H] [Bialgebra k H] {p : ℕ}

/-- An `H`-linear map `f : M →ₗ[H] N` induces a `k`-linear map on every slash homology group. -/
noncomputable def slashHomologyMap (P : TruncatedPrimitive (k := k) H p)
    {M N : Type*} [AddCommGroup M] [Module k M] [Module H M] [IsScalarTower k H M]
    [AddCommGroup N] [Module k N] [Module H N] [IsScalarTower k H N]
    (f : M →ₗ[H] N) (j : ℕ) :
    SlashHomology p (P.moduleDifferential (M := M)) j →ₗ[k]
      SlashHomology p (P.moduleDifferential (M := N)) j :=
  SlashHomology.map p (f.restrictScalars k) (P.comp_moduleDifferential f) j

/-- An `H`-linear equivalence `f : M ≃ₗ[H] N` induces a `k`-linear equivalence on every slash
homology group. -/
noncomputable def slashHomologyEquiv (P : TruncatedPrimitive (k := k) H p)
    {M N : Type*} [AddCommGroup M] [Module k M] [Module H M] [IsScalarTower k H M]
    [AddCommGroup N] [Module k N] [Module H N] [IsScalarTower k H N]
    (f : M ≃ₗ[H] N) (j : ℕ) :
    SlashHomology p (P.moduleDifferential (M := M)) j ≃ₗ[k]
      SlashHomology p (P.moduleDifferential (M := N)) j :=
  SlashHomology.equiv p (f.restrictScalars k) (P.comp_moduleDifferential f.toLinearMap) j

/-- The `k`-linear contracting operator `h_H : H →ₗ[k] H` sending `d ^ (p - 1) ↦ 1` and lower
basis powers `d ^ r ↦ 0` (`r < p - 1`). -/
noncomputable def selfContractingHomotopy (P : TruncatedPrimitive (k := k) H p) : H →ₗ[k] H :=
  P.basis.constr k fun i : Fin p ↦ if (i : ℕ) = p - 1 then (1 : H) else 0

private theorem nullHomotopicMap_selfContractingHomotopy (P : TruncatedPrimitive (k := k) H p) :
    SlashHomology.nullHomotopicMap p
        (P.moduleDifferential (M := H)) (P.moduleDifferential (M := H))
        P.selfContractingHomotopy =
      LinearMap.id := by
  apply P.basis.ext
  rintro ⟨m, hm⟩
  rw [LinearMap.id_apply, SlashHomology.nullHomotopicMap_apply, Finset.sum_eq_single m]
  · have hsub : p - 1 - m + m = p - 1 := by omega
    have hb : P.d ^ (p - 1) = P.basis ⟨p - 1, by omega⟩ := by simp
    simp only [moduleDifferential_pow_apply, P.basis_apply, smul_eq_mul, ← pow_add, hsub]
    rw [hb, selfContractingHomotopy, Module.Basis.constr_basis]
    simp
  · intro i hi hne
    rw [Finset.mem_range] at hi
    rcases lt_trichotomy i m with hlt | rfl | hgt
    · have hpow : P.d ^ (p - 1 - i) * P.d ^ m = 0 := by
        rw [← pow_add, pow_eq_zero_of_le (by omega : p ≤ p - 1 - i + m) P.pow_d]
      simp [smul_eq_mul, P.basis_apply, hpow]
    · exact absurd rfl hne
    · have hlt_p : p - 1 - i + m < p - 1 := by omega
      have hb : P.d ^ (p - 1 - i + m) = P.basis ⟨p - 1 - i + m, by omega⟩ := by simp
      simp only [moduleDifferential_pow_apply, P.basis_apply, smul_eq_mul, ← pow_add]
      rw [hb, selfContractingHomotopy, Module.Basis.constr_basis]
      simp [hlt_p.ne]
  · intro hm_mem
    exact absurd (Finset.mem_range.mpr hm) hm_mem

/-- **Contractibility of `H` over itself.** As a `p`-complex over `k`, `H` is `p`-contractible:
`id_H` is `p`-homotopic to `0`. -/
theorem isPHomotopic_id_zero_self (P : TruncatedPrimitive (k := k) H p) :
    SlashHomology.IsPHomotopic p
      (P.moduleDifferential (M := H)) (P.moduleDifferential (M := H)) LinearMap.id 0 :=
  ⟨P.selfContractingHomotopy, by rw [sub_zero, P.nullHomotopicMap_selfContractingHomotopy]⟩

private theorem nullHomotopicMap_finsupp (P : TruncatedPrimitive (k := k) H p) (ι : Type*) :
    SlashHomology.nullHomotopicMap p
        (P.moduleDifferential (M := ι →₀ H)) (P.moduleDifferential (M := ι →₀ H))
        (Finsupp.mapRange.linearMap P.selfContractingHomotopy) =
      LinearMap.id := by
  refine Finsupp.lhom_ext' fun i ↦ LinearMap.ext fun x ↦ ?_
  have hsingle : ∀ (r : ℕ) (y : H),
      ((P.moduleDifferential (M := ι →₀ H)) ^ r) (Finsupp.single i y) =
        Finsupp.single i (((P.moduleDifferential (M := H)) ^ r) y) := by
    intro r y
    simp [Finsupp.smul_single, smul_eq_mul]
  rw [LinearMap.comp_apply, Finsupp.lsingle_apply, LinearMap.comp_apply, LinearMap.id_apply,
    Finsupp.lsingle_apply, SlashHomology.nullHomotopicMap_apply]
  have hcongr :
      (∑ r ∈ Finset.range p,
          ((P.moduleDifferential (M := ι →₀ H)) ^ r)
            (Finsupp.mapRange.linearMap P.selfContractingHomotopy
              (((P.moduleDifferential (M := ι →₀ H)) ^ (p - 1 - r)) (Finsupp.single i x)))) =
        Finsupp.single i
          (SlashHomology.nullHomotopicMap p
            (P.moduleDifferential (M := H)) (P.moduleDifferential (M := H))
            P.selfContractingHomotopy x) := by
    rw [SlashHomology.nullHomotopicMap_apply]
    conv_rhs => rw [← Finsupp.lsingle_apply (R := k), map_sum (Finsupp.lsingle (R := k) i)]
    refine Finset.sum_congr rfl fun r _ ↦ ?_
    rw [hsingle, Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single, hsingle,
      Finsupp.lsingle_apply]
  rw [hcongr, P.nullHomotopicMap_selfContractingHomotopy, LinearMap.id_apply]

/-- **Every projective `H`-module is `p`-contractible over `k`.** Over any commutative ring `k`,
if `M` is projective over `H`, then `id_M` is `p`-homotopic to `0` for `P.moduleDifferential`. -/
theorem isPHomotopic_id_zero_of_projective (P : TruncatedPrimitive (k := k) H p)
    {M : Type w} [AddCommGroup M] [Module k M] [Module H M] [IsScalarTower k H M]
    [Module.Projective H M] :
    SlashHomology.IsPHomotopic p
      (P.moduleDifferential (M := M)) (P.moduleDifferential (M := M)) LinearMap.id 0 := by
  obtain ⟨s, hs⟩ := Module.projective_def'.mp ‹Module.Projective H M›
  let π : (M →₀ H) →ₗ[H] M := Finsupp.linearCombination H id
  let s' : M →ₗ[k] M →₀ H := s.restrictScalars k
  let π' : (M →₀ H) →ₗ[k] M := π.restrictScalars k
  let hF : (M →₀ H) →ₗ[k] M →₀ H := Finsupp.mapRange.linearMap P.selfContractingHomotopy
  refine ⟨π' ∘ₗ hF ∘ₗ s', ?_⟩
  ext m
  have hs_comm := fun r ↦ SlashHomology.comp_pow_of_comp_eq s' (P.comp_moduleDifferential s) r
  have hπ_comm := fun r ↦ SlashHomology.comp_pow_of_comp_eq π' (P.comp_moduleDifferential π) r
  have hsplit : π' (s' m) = m := by
    simpa [π', s', π] using LinearMap.congr_fun hs m
  rw [LinearMap.sub_apply, LinearMap.zero_apply, sub_zero, LinearMap.id_apply,
    SlashHomology.nullHomotopicMap_apply]
  have hsum :
      (∑ i ∈ Finset.range p,
          ((P.moduleDifferential (M := M)) ^ i)
            ((π' ∘ₗ hF ∘ₗ s') (((P.moduleDifferential (M := M)) ^ (p - 1 - i)) m))) =
        π' (SlashHomology.nullHomotopicMap p
          (P.moduleDifferential (M := M →₀ H)) (P.moduleDifferential (M := M →₀ H))
          hF (s' m)) := by
    rw [SlashHomology.nullHomotopicMap_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have h1 := LinearMap.congr_fun (hs_comm (p - 1 - i)) m
    have h2 := LinearMap.congr_fun (hπ_comm i)
      (hF (((P.moduleDifferential (M := M →₀ H)) ^ (p - 1 - i)) (s' m)))
    simpa [LinearMap.comp_apply] using
      (congrArg (fun u ↦ ((P.moduleDifferential (M := M)) ^ i) (π' (hF u))) h1).trans h2.symm
  rw [hsum, P.nullHomotopicMap_finsupp, LinearMap.id_apply, hsplit]

/-- **Projective `H`-modules have vanishing slash homology.** Over any commutative ring `k`, if `M`
is projective over `H`, then `SlashHomology p P.moduleDifferential j` is a subsingleton for every
`j : ℕ`. -/
theorem slashHomology_subsingleton_of_projective (P : TruncatedPrimitive (k := k) H p)
    {M : Type w} [AddCommGroup M] [Module k M] [Module H M] [IsScalarTower k H M]
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

end FunctorialityAndContractibility

end TruncatedPrimitive

/-! ### Khovanov–Qi's slash-homology projectivity detection theorem -/

section DetectionTheorem

variable {k : Type u} {H : Type v} {M : Type w}
  [Field k] [Ring H] [Bialgebra k H] {p : ℕ}
  [AddCommGroup M] [Module k M] [Module H M] [IsScalarTower k H M]

/-- Over a field `k` (without assuming finite dimensionality, primality of `p`, or an antipode),
vanishing of all `p - 1` slash homology groups `SlashHomology p P.moduleDifferential j`
(`j + 1 < p`) implies that `M` is a **free** `H`-module. -/
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
  have hΦ_eq : Φ.restrictScalars k = (bFree.equiv b (Equiv.refl _)).toLinearMap := by
    apply bFree.ext
    rintro ⟨i, r⟩
    rw [LinearMap.restrictScalars_apply, LinearEquiv.coe_toLinearMap, Module.Basis.equiv_apply,
      Equiv.refl_apply, hb i r]
    simp [bFree, Φ, Equiv.sigmaEquivProd]
  have hbij : Function.Bijective Φ := by
    rw [← LinearMap.coe_restrictScalars k, hΦ_eq]
    exact (bFree.equiv b (Equiv.refl _)).bijective
  exact Module.Free.of_basis (Module.Basis.ofRepr (LinearEquiv.ofBijective Φ hbij).symm)

/-- **Khovanov–Qi's slash-homology detection theorem** (Khovanov–Qi 2015, §2). Over a field `k`, a
left `H`-module `M` is projective over `H` if and only if all `p - 1` slash homology groups
`SlashHomology p P.moduleDifferential j` (`j + 1 < p`) vanish. -/
theorem slashHomology_subsingleton_iff_projective
    (P : TruncatedPrimitive (k := k) H p) :
    (∀ j, j + 1 < p → Subsingleton (SlashHomology p (P.moduleDifferential (M := M)) j)) ↔
      Module.Projective H M := by
  refine ⟨fun hsub ↦ ?_, fun hproj j _ ↦ P.slashHomology_subsingleton_of_projective j⟩
  have : Module.Free H M := P.free_of_slashHomology_subsingleton hsub
  infer_instance

/-- Over a field `k`, vanishing of all `p - 1` slash homology groups is also equivalent to `M`
being free over `H`; in particular, every projective `H`-module is free over `H`. -/
theorem slashHomology_subsingleton_iff_free
    (P : TruncatedPrimitive (k := k) H p) :
    (∀ j, j + 1 < p → Subsingleton (SlashHomology p (P.moduleDifferential (M := M)) j)) ↔
      Module.Free H M :=
  ⟨P.free_of_slashHomology_subsingleton, fun hfree ↦ by
    have := hfree
    exact (slashHomology_subsingleton_iff_projective P).mpr inferInstance⟩

/-- **Khovanov–Qi dimension decomposition for `H`-modules.** For a finite-dimensional `H`-module
`M` over `k` (`0 < p`),
`finrank k M = p * finrank k (range (d_M ^ (p - 1))) + ∑_{j = 0}^{p - 2} finrank k H^{/j}(M)`. -/
theorem TruncatedPrimitive.finrank_eq_mul_finrank_range_add_sum_slashHomology
    [FiniteDimensional k M] (P : TruncatedPrimitive (k := k) H p) (hp : 0 < p) :
    Module.finrank k M =
      p * Module.finrank k (LinearMap.range ((P.moduleDifferential (M := M)) ^ (p - 1))) +
        ∑ j ∈ Finset.range (p - 1),
          Module.finrank k (SlashHomology p (P.moduleDifferential (M := M)) j) :=
  SlashHomology.finrank_eq_mul_finrank_range_pow_add_sum hp P.moduleDifferential_pow_self

end DetectionTheorem

/-! ### Explicit slash-homology calculations on the trivial module and cyclic quotients -/

namespace TruncatedPrimitive

section TrivialModule

variable {k : Type u} {H : Type v} [CommRing k] [Ring H] [Bialgebra k H] {p : ℕ}

/-- On the counit trivial module `BialgebraModule.Trivial k H`, `P.moduleDifferential` vanishes
because `ε(P.d) = 0`. -/
@[simp]
theorem moduleDifferential_trivial_eq_zero (P : TruncatedPrimitive (k := k) H p) :
    P.moduleDifferential (M := BialgebraModule.Trivial k H) = 0 := by
  ext x
  apply (BialgebraModule.trivialEquiv k H).injective
  simp [P.counit_d]

/-- For `2 ≤ p`, the `0`-th slash homology of the counit trivial module
`BialgebraModule.Trivial k H` is canonically `k`-linearly isomorphic to `k` (`H^{/0}(k) ≃ₗ[k] k`).
-/
noncomputable def slashHomologyZeroTrivialEquiv (P : TruncatedPrimitive (k := k) H p)
    (hp : 2 ≤ p) :
    SlashHomology p (P.moduleDifferential (M := BialgebraModule.Trivial k H)) 0 ≃ₗ[k] k := by
  let d₀ := P.moduleDifferential (M := BialgebraModule.Trivial k H)
  have htop : LinearMap.ker (d₀ ^ (0 + 1)) = ⊤ := by
    simp [d₀]
  have hd0_pow : d₀ ^ (p - 1) = 0 := by
    dsimp only [d₀]
    rw [P.moduleDifferential_trivial_eq_zero, zero_pow (by omega)]
  have hbot : SlashHomology.boundaries p d₀ 0 = ⊥ := by
    ext z
    simp [hd0_pow, Module.End.one_eq_id]
  exact (Submodule.quotEquivOfEqBot _ hbot).trans <|
    (LinearEquiv.ofTop _ htop).trans (BialgebraModule.trivialEquiv k H)

/-- For `1 ≤ j`, the `j`-th slash homology of the counit trivial module vanishes (`H^{/j}(k) = 0`),
since `ker(0 ^ (j + 1)) = ⊤ = ker(0 ^ j)`. -/
theorem slashHomology_trivial_subsingleton_of_pos (P : TruncatedPrimitive (k := k) H p)
    {j : ℕ} (hj : 0 < j) :
    Subsingleton (SlashHomology p (P.moduleDifferential (M := BialgebraModule.Trivial k H)) j) := by
  rw [SlashHomology.subsingleton_iff]
  intro x _
  refine Submodule.mem_sup_right ?_
  simp [zero_pow hj.ne']

/-- Over a field `k`, the counit trivial module `BialgebraModule.Trivial k H` is never projective
over `H` when `2 ≤ p`. -/
theorem not_projective_trivial {k : Type u} {H : Type v} [Field k] [Ring H] [Bialgebra k H]
    {p : ℕ} (P : TruncatedPrimitive (k := k) H p) (hp : 2 ≤ p) :
    ¬ Module.Projective H (BialgebraModule.Trivial k H) := by
  intro hproj
  have := P.slashHomology_subsingleton_of_projective
    (M := BialgebraModule.Trivial k H) 0
  exact not_subsingleton k (P.slashHomologyZeroTrivialEquiv hp).symm.subsingleton

end TrivialModule

section CyclicQuotients

variable {k : Type u} {H : Type v} [Field k] [Ring H] [Bialgebra k H] {p : ℕ}

private theorem restrictScalars_span_pow (P : TruncatedPrimitive (k := k) H p) {r : ℕ}
    (hr : r ≤ p) :
    (Ideal.span {P.d ^ r}).restrictScalars k =
      Submodule.span k (Set.range fun j : Fin (p - r) ↦ P.d ^ (r + j)) := by
  apply le_antisymm
  · rintro x hx
    rw [Submodule.restrictScalars_mem, Ideal.mem_span_singleton'] at hx
    obtain ⟨a, rfl⟩ := hx
    have ha := P.basis.linearCombination_repr a
    rw [Finsupp.linearCombination_apply, Finsupp.sum] at ha
    rw [← ha, Finset.sum_mul]
    refine Submodule.sum_mem _ fun i _ ↦ ?_
    rw [P.basis_apply, smul_mul_assoc, ← pow_add]
    rcases lt_or_ge (i + r : ℕ) p with hlt | hge
    · have hexp : (i : ℕ) + r = r + (i : ℕ) := add_comm _ _
      rw [hexp]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨i, by omega⟩, rfl⟩)
    · rw [pow_eq_zero_of_le hge P.pow_d, smul_zero]
      exact zero_mem _
  · rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    dsimp only
    rw [SetLike.mem_coe, Submodule.restrictScalars_mem, add_comm, pow_add]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

private theorem quotientSpanPow_linearIndependent (P : TruncatedPrimitive (k := k) H p) {r : ℕ}
    (hr : r ≤ p) :
    LinearIndependent k
      (fun i : Fin r ↦ Submodule.Quotient.mk (p := Ideal.span {P.d ^ r}) (P.d ^ (i : ℕ))) := by
  rw [linearIndependent_iff']
  intro s c hc i hi
  let J : Submodule k H := (Ideal.span {P.d ^ r}).restrictScalars k
  have hmem : (∑ t ∈ s, c t • P.d ^ (t : ℕ)) ∈ (Ideal.span {P.d ^ r}).restrictScalars k := by
    rw [Submodule.restrictScalars_mem, ← Submodule.Quotient.mk_eq_zero]
    have hmk :
        Submodule.Quotient.mk (p := Ideal.span {P.d ^ r}) (∑ t ∈ s, c t • P.d ^ (t : ℕ)) =
          ∑ t ∈ s, c t • Submodule.Quotient.mk (p := Ideal.span {P.d ^ r}) (P.d ^ (t : ℕ)) :=
      map_sum J.mkQ _ _
    exact hmk.trans hc
  rw [P.restrictScalars_span_pow hr] at hmem
  obtain ⟨f, hf⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hmem
  -- Evaluate the `⟨i, _⟩`-th `P.basis` coordinate: exponents `≥ r > i` contribute `0`.
  have hcoord := congrArg (P.basis.coord ⟨i, by omega⟩) hf
  have hlhs :
      P.basis.coord ⟨i, by omega⟩ (f.sum fun j a ↦ a • P.d ^ (r + (j : ℕ))) = 0 := by
    rw [Finsupp.sum, map_sum]
    refine Finset.sum_eq_zero fun j _ ↦ ?_
    have hb : P.d ^ (r + (j : ℕ)) = P.basis ⟨r + j, by omega⟩ := by simp
    have hne : (⟨r + j, by omega⟩ : Fin p) ≠ ⟨i, by omega⟩ := fun h ↦ by
      have hval : r + (j : ℕ) = (i : ℕ) := by simpa using congrArg Fin.val h
      omega
    rw [hb, map_smul, Module.Basis.coord_apply, Module.Basis.repr_self,
      Finsupp.single_eq_of_ne hne.symm, smul_zero]
  have hrhs :
      P.basis.coord ⟨i, by omega⟩ (∑ t ∈ s, c t • P.d ^ (t : ℕ)) = c i := by
    rw [map_sum, Finset.sum_eq_single i]
    · have hb : P.d ^ (i : ℕ) = P.basis ⟨i, by omega⟩ := (P.basis_apply ⟨i, by omega⟩).symm
      rw [hb, map_smul, Module.Basis.coord_apply, Module.Basis.repr_self,
        Finsupp.single_eq_same, smul_eq_mul, mul_one]
    · intro t _ htne
      have hb : P.d ^ (t : ℕ) = P.basis ⟨t, by omega⟩ := (P.basis_apply ⟨t, by omega⟩).symm
      have hne : (⟨t, by omega⟩ : Fin p) ≠ ⟨i, by omega⟩ := fun h ↦
        htne (Fin.ext (by simpa using congrArg Fin.val h))
      rw [hb, map_smul, Module.Basis.coord_apply, Module.Basis.repr_self,
        Finsupp.single_eq_of_ne hne.symm, smul_zero]
    · exact fun h ↦ absurd hi h
  simpa [hlhs, hrhs] using hcoord.symm

private theorem quotientSpanPow_span (P : TruncatedPrimitive (k := k) H p) {r : ℕ} :
    (⊤ : Submodule k (H ⧸ Ideal.span {P.d ^ r})) ≤
      Submodule.span k (Set.range fun i : Fin r ↦
        Submodule.Quotient.mk (p := Ideal.span {P.d ^ r}) (P.d ^ (i : ℕ))) := by
  rintro q -
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  have hx := P.basis.linearCombination_repr x
  rw [Finsupp.linearCombination_apply, Finsupp.sum] at hx
  rw [← hx]
  have hsum_mk :
      Submodule.Quotient.mk (p := Ideal.span {P.d ^ r})
          (∑ i ∈ (P.basis.repr x).support, (P.basis.repr x i) • P.basis i) =
        ∑ i ∈ (P.basis.repr x).support,
          (P.basis.repr x i) •
            Submodule.Quotient.mk (p := Ideal.span {P.d ^ r}) (P.basis i) :=
    map_sum ((Ideal.span {P.d ^ r}).restrictScalars k).mkQ _ _
  rw [hsum_mk]
  refine Submodule.sum_mem _ fun i _ ↦ ?_
  rw [P.basis_apply]
  rcases lt_or_ge (i : ℕ) r with hlt | hge
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨i, hlt⟩, rfl⟩)
  · have hzero : Submodule.Quotient.mk (p := Ideal.span {P.d ^ r}) (P.d ^ (i : ℕ)) = 0 := by
      rw [Submodule.Quotient.mk_eq_zero]
      obtain ⟨u, hu⟩ := Nat.exists_eq_add_of_le hge
      rw [hu, add_comm, pow_add]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
    rw [hzero, smul_zero]
    exact zero_mem _

/-- **Monomial `k`-basis of cyclic quotients `H ⧸ (d ^ r)`.** For `r ≤ p`, the classes
`1, [d], …, [d ^ (r - 1)]` form a `k`-basis of the left `H`-module `H ⧸ Ideal.span {P.d ^ r}`. -/
noncomputable def quotientSpanPowBasis (P : TruncatedPrimitive (k := k) H p) {r : ℕ}
    (hr : r ≤ p) :
    Module.Basis (Fin r) k (H ⧸ Ideal.span {P.d ^ r}) :=
  Module.Basis.mk (P.quotientSpanPow_linearIndependent hr) P.quotientSpanPow_span

/-- The `i`-th basis vector of `P.quotientSpanPowBasis hr` is the class of `P.d ^ i`. -/
@[simp]
theorem quotientSpanPowBasis_apply (P : TruncatedPrimitive (k := k) H p) {r : ℕ}
    (hr : r ≤ p) (i : Fin r) :
    P.quotientSpanPowBasis hr i =
      Submodule.Quotient.mk (p := Ideal.span {P.d ^ r}) (P.d ^ (i : ℕ)) := by
  simp [quotientSpanPowBasis]

/-- For `r ≤ p`, the `k`-dimension of the cyclic quotient `H ⧸ Ideal.span {P.d ^ r}` is `r`. -/
theorem finrank_quotient_span_pow (P : TruncatedPrimitive (k := k) H p) {r : ℕ} (hr : r ≤ p) :
    Module.finrank k (H ⧸ Ideal.span {P.d ^ r}) = r := by
  rw [Module.finrank_eq_card_basis (P.quotientSpanPowBasis hr), Fintype.card_fin]

private theorem moduleDifferential_pow_quotientSpanPowBasis_lt
    (P : TruncatedPrimitive (k := k) H p) {r : ℕ} (hr : r ≤ p) (m : ℕ)
    (t : Fin r) (ht : (t : ℕ) + m < r) :
    ((P.moduleDifferential (M := H ⧸ Ideal.span {P.d ^ r})) ^ m)
        (P.quotientSpanPowBasis hr t) =
      P.quotientSpanPowBasis hr ⟨t + m, ht⟩ := by
  simp [← Submodule.Quotient.mk_smul (Ideal.span {P.d ^ r}), smul_eq_mul, ← pow_add, add_comm]

private theorem moduleDifferential_pow_quotientSpanPowBasis_eq_zero
    (P : TruncatedPrimitive (k := k) H p) {r : ℕ} (hr : r ≤ p) (m : ℕ)
    (t : Fin r) (htge : r ≤ (t : ℕ) + m) :
    ((P.moduleDifferential (M := H ⧸ Ideal.span {P.d ^ r})) ^ m)
        (P.quotientSpanPowBasis hr t) = 0 := by
  obtain ⟨u, hu⟩ := Nat.exists_eq_add_of_le htge
  rw [moduleDifferential_pow_apply, quotientSpanPowBasis_apply,
    ← Submodule.Quotient.mk_smul (Ideal.span {P.d ^ r}), smul_eq_mul, ← pow_add,
    add_comm m (t : ℕ), hu, add_comm r u, pow_add, Submodule.Quotient.mk_eq_zero]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

private theorem ker_pow_quotient_span_pow (P : TruncatedPrimitive (k := k) H p)
    {r : ℕ} (hr : r ≤ p) (m : ℕ) :
    LinearMap.ker ((P.moduleDifferential (M := H ⧸ Ideal.span {P.d ^ r})) ^ m) =
      Submodule.span k (Set.range fun j : Fin (min r m) ↦
        P.quotientSpanPowBasis hr ⟨r - min r m + j, by omega⟩) := by
  let b := P.quotientSpanPowBasis hr
  let dM := P.moduleDifferential (M := H ⧸ Ideal.span {P.d ^ r})
  apply le_antisymm
  · intro q hq
    have hrepr := b.linearCombination_repr q
    rw [Finsupp.linearCombination_apply, Finsupp.sum] at hrepr
    have h0 : (dM ^ m) q = 0 := LinearMap.mem_ker.mp hq
    rw [← hrepr, map_sum] at h0
    rw [← hrepr]
    refine Submodule.sum_mem _ fun i hi ↦ ?_
    rcases lt_or_ge ((i : ℕ) + m) r with hlt | hge
    · -- Evaluating `b.coord ⟨i + m, hlt⟩` on `(dM ^ m) q = 0` forces `b.repr q i = 0`.
      have hcoord := congrArg (b.coord ⟨i + m, hlt⟩) h0
      rw [map_zero, map_sum, Finset.sum_eq_single i] at hcoord
      · rw [map_smul, P.moduleDifferential_pow_quotientSpanPowBasis_lt hr m i hlt, map_smul,
          Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same, smul_eq_mul,
          mul_one] at hcoord
        simp [hcoord]
      · intro t _ htne
        rw [map_smul]
        rcases lt_or_ge ((t : ℕ) + m) r with htlt | htge
        · have hne : (⟨t + m, htlt⟩ : Fin r) ≠ ⟨i + m, hlt⟩ := fun h ↦ by
            have hval : (t : ℕ) + m = (i : ℕ) + m := by simpa using congrArg Fin.val h
            exact htne (Fin.ext (by omega))
          rw [P.moduleDifferential_pow_quotientSpanPowBasis_lt hr m t htlt, map_smul,
            Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_of_ne hne.symm,
            smul_zero]
        · rw [P.moduleDifferential_pow_quotientSpanPowBasis_eq_zero hr m t htge, smul_zero,
            map_zero]
      · exact fun h ↦ absurd hi h
    · have hj : (i : ℕ) = r - min r m + ((i : ℕ) - (r - min r m)) := by omega
      have hbeq : b i = b ⟨r - min r m + ((i : ℕ) - (r - min r m)), by omega⟩ :=
        congrArg b (Fin.ext hj)
      rw [hbeq]
      exact Submodule.smul_mem _ _
        (Submodule.subset_span ⟨⟨(i : ℕ) - (r - min r m), by omega⟩, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    exact P.moduleDifferential_pow_quotientSpanPowBasis_eq_zero hr m
      ⟨r - min r m + j, by omega⟩ (by simp; omega)

private theorem finrank_ker_pow_quotient_span_pow (P : TruncatedPrimitive (k := k) H p)
    {r : ℕ} (hr : r ≤ p) (m : ℕ) :
    Module.finrank k
        (LinearMap.ker ((P.moduleDifferential (M := H ⧸ Ideal.span {P.d ^ r})) ^ m)) =
      min r m := by
  let b := P.quotientSpanPowBasis hr
  have : FiniteDimensional k (H ⧸ Ideal.span {P.d ^ r}) := Module.Finite.of_basis b
  have hli : LinearIndependent k (fun j : Fin (min r m) ↦ b ⟨r - min r m + j, by omega⟩) :=
    b.linearIndependent.comp _ fun j₁ j₂ h ↦ by
      have hval : r - min r m + (j₁ : ℕ) = r - min r m + (j₂ : ℕ) := by
        simpa using congrArg Fin.val h
      exact Fin.ext (by omega)
  rw [P.ker_pow_quotient_span_pow hr m, finrank_span_eq_card hli, Fintype.card_fin]

/-- **Slash-homology dimensions of cyclic quotients `H ⧸ (d ^ r)`.** For `r < p` and `j + 1 < p`,
`SlashHomology p P.moduleDifferential j` on `H ⧸ Ideal.span {P.d ^ r}` has `k`-dimension `1` when
`j < r` and `0` when `r ≤ j`.

For `p = 3`:
* `r = 1` (`M = H_3 ⧸ (d) ≅ k`): `dim H^{/0}(k) = 1` and `dim H^{/1}(k) = 0`.
* `r = 2` (`M = H_3 ⧸ (d ^ 2) ≅ k[d] / (d ^ 2)`): `dim H^{/0}(M) = 1` and `dim H^{/1}(M) = 1`,
  matching `2 = 3 · 0 + 1 + 1`. -/
theorem finrank_slashHomology_quotient_span_pow (P : TruncatedPrimitive (k := k) H p)
    {r j : ℕ} (hr : r < p) (hj : j + 1 < p) :
    Module.finrank k
        (SlashHomology p (P.moduleDifferential (M := H ⧸ Ideal.span {P.d ^ r})) j) =
      if j < r then 1 else 0 := by
  let M_r := H ⧸ Ideal.span {P.d ^ r}
  have : FiniteDimensional k M_r := Module.Finite.of_basis (P.quotientSpanPowBasis hr.le)
  have hrd : ((P.moduleDifferential (M := M_r)) ^ (p - 1)) = 0 := by
    ext q
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨u, hu⟩ := Nat.exists_eq_add_of_le (by omega : r ≤ p - 1)
    rw [moduleDifferential_pow_apply, LinearMap.zero_apply,
      ← Submodule.Quotient.mk_smul (Ideal.span {P.d ^ r}), smul_eq_mul,
      Submodule.Quotient.mk_eq_zero, hu, add_comm r u, pow_add, mul_assoc,
      P.mul_comm (P.d ^ r) x, ← mul_assoc]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  have hrange :
      Module.finrank k
          (LinearMap.range ((P.moduleDifferential (M := M_r)) ^ (p - 1))) = 0 := by
    simp [hrd]
  have heq := SlashHomology.finrank_add_finrank_ker_add_finrank_range
    (P.moduleDifferential_pow_self (M := M_r)) hj
  rw [hrange, P.finrank_ker_pow_quotient_span_pow hr.le j,
    P.finrank_ker_pow_quotient_span_pow hr.le (j + 1)] at heq
  split_ifs with hjr <;> omega

/-- **No nontrivial proper cyclic quotient `H ⧸ (d ^ r)` (`1 ≤ r < p`) is projective over `H`.** -/
theorem not_projective_quotient_span_pow (P : TruncatedPrimitive (k := k) H p)
    {r : ℕ} (hr₀ : 0 < r) (hr : r < p) :
    ¬ Module.Projective H (H ⧸ Ideal.span {P.d ^ r}) := by
  rw [← slashHomology_subsingleton_iff_projective P]
  intro hsub
  have := hsub 0 (by omega)
  have hfin := P.finrank_slashHomology_quotient_span_pow hr (by omega : 0 + 1 < p)
  simp only [hr₀, ↓reduceIte, Module.finrank_zero_of_subsingleton] at hfin
  exact zero_ne_one hfin

end CyclicQuotients

end TruncatedPrimitive

end TauCeti

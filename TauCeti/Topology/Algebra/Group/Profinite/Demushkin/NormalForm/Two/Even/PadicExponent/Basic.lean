/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.NormalForm.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Procyclic

/-!
# The even-rank dyadic normal-form word with a `2`-adic exponent

Labute's normal form for the Demushkin relators with `q = 2` of even rank `n` is

  `x₁^{2+α} (x₁, x₂) x₃^{2^f} (x₃, x₄) ⋯ (x_{n-1}, x_n)`

with a `2`-adic exponent `α ∈ 4ℤ₂` and a level `2 ≤ f ≤ ∞`, the factor `x₃^{2^f}` being absent at
`f = ∞`. The word `TauCeti.demushkinWordTwoEven` carries a natural exponent `2 + a`, which is all
the marked classification needs, because the group presented depends on `α` only through its
valuation. The successive-approximation argument, however, produces the relator with a genuine
`2`-adic exponent. This file introduces the word `TauCeti.demushkinWordTwoEvenPadic`, in which
`x₁^{2+α}` is the `2`-adic power `TauCeti.IsProP.padicPow` and the tail is
`x₃^q (x₃, x₄) ⋯ (x_{n-1}, x_n)` for a natural number `q`, so that `q = 2^f` is Labute's level `f`
and `q = 0` is the level `f = ∞`, on an arbitrary tuple of elements of a pro-`2` group, and proves
its elementary properties: it is the natural-exponent word at `α = a`, `q = 2^f`, it is carried by
continuous homomorphisms of pro-`2` groups, it is killed by the characters into commutative
pro-`2` groups which are trivial on `x₁` and whose value on `x₃` has trivial `q`-th power, and for
`α` and `q` even it lies in the pro-`2` Frattini subgroup.

## Main definitions

* `TauCeti.demushkinWordTwoEvenPadic`: the word `x₁^{2+α} (x₁, x₂) x₃^q (x₃, x₄) ⋯ (x_{n-1}, x_n)`
  with `α ∈ ℤ₂`, on a tuple of elements of a pro-`2` group; it is the natural-exponent word at
  `α = a` and `q = 2^f` (`TauCeti.demushkinWordTwoEvenPadic_natCast`), it splits off the tail
  relator `x₃^q (x₃, x₄) ⋯ (x_{n-1}, x_n)` as a `q ≠ 2` word
  (`TauCeti.demushkinWordTwoEvenPadic_eq_padicPow_mul_labuteComm_mul`), and at `α = 0`, `q = 0`
  it is the `q ≠ 2` word at `q = 2` (`TauCeti.demushkinWordTwoEvenPadic_zero_zero`).

## Main results

* `TauCeti.map_demushkinWordTwoEvenPadic`: a continuous homomorphism of pro-`2` groups reads the
  word on the image tuple.
* `TauCeti.map_demushkinWordTwoEvenPadic_eq_one`: a continuous character into a commutative
  pro-`2` group which is trivial on `x₁` and whose value on `x₃` has trivial `q`-th power kills the
  word.
* `TauCeti.demushkinWordTwoEvenPadic_mem_proPFrattini`: for `α` and `q` even the word lies in the
  pro-`2` Frattini subgroup.

## References

* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), 106–132, §3,
  Theorem 3.
* J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Chapter III, §9.
-/

public section

namespace TauCeti

section Word

variable {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
  [TotallyDisconnectedSpace H]

/-- The `q = 2`, `n` even normal-form word `x₁^{2+α} (x₁, x₂) x₃^q (x₃, x₄) ⋯ (x_{n-1}, x_n)` with
a `2`-adic exponent `α`, on a tuple `x : ℕ → H` of elements of a pro-`2` group `H`, with `x 0`
playing the role of `x₁`. The power `x₁^{2+α}` is the `2`-adic power of
`TauCeti.IsProP.padicPow`, and the exponent `q` of `x₃` is the `q`-invariant of the tail relator:
`q = 2^f` is Labute's level `f`, and `q = 0` is the level `f = ∞`, where the factor `x₃^{2^f}` is
absent. At a natural exponent `α = a` and `q = 2^f` the word is `TauCeti.demushkinWordTwoEven a f n`
(`TauCeti.demushkinWordTwoEvenPadic_natCast`). -/
noncomputable def demushkinWordTwoEvenPadic (hH : IsProP 2 H) (α : ℤ_[2]) (q n : ℕ) (x : ℕ → H) :
    H :=
  hH.padicPow (x 0) (2 + α) * labuteComm (x 0) (x 1) * x 2 ^ q *
    ((List.range (n / 2 - 1)).map fun i ↦ labuteComm (x (2 * i + 2)) (x (2 * i + 3))).prod

variable (hH : IsProP 2 H) (α : ℤ_[2]) (q n : ℕ) (x : ℕ → H)

/-- The defining equation of `TauCeti.demushkinWordTwoEvenPadic`. -/
theorem demushkinWordTwoEvenPadic_def :
    demushkinWordTwoEvenPadic hH α q n x =
      hH.padicPow (x 0) (2 + α) * labuteComm (x 0) (x 1) * x 2 ^ q *
        ((List.range (n / 2 - 1)).map fun i ↦ labuteComm (x (2 * i + 2)) (x (2 * i + 3))).prod :=
  (rfl)

/-- At a natural exponent `α = a` and `q = 2^f`, the word is the even dyadic normal-form word
`x₁^{2+a} (x₁, x₂) x₃^{2^f} (x₃, x₄) ⋯ (x_{n-1}, x_n)` with natural exponent. -/
@[simp]
theorem demushkinWordTwoEvenPadic_natCast (a f : ℕ) :
    demushkinWordTwoEvenPadic hH (a : ℤ_[2]) (2 ^ f) n x = demushkinWordTwoEven a f n x := by
  rw [demushkinWordTwoEvenPadic_def, demushkinWordTwoEven_def,
    ← hH.padicPow_natCast (x 0) (2 + a), Nat.cast_add, Nat.cast_ofNat]

/-- At rank two, on a tuple whose third entry is `1` (as for the canonical generator tuple
`TauCeti.freeProPGen 2 2`, whose third generator is out of range), the word is
`x₁^{2+α} (x₁, x₂)`: the factor `x₃^q` is `1` by the hypothesis `x 2 = 1`, and the commutator
product beyond `(x₁, x₂)` is empty. -/
@[simp]
theorem demushkinWordTwoEvenPadic_two (hx : x 2 = 1) :
    demushkinWordTwoEvenPadic hH α q 2 x =
      hH.padicPow (x 0) (2 + α) * labuteComm (x 0) (x 1) := by
  simp [demushkinWordTwoEvenPadic_def, hx]

/-- For `n ≥ 2` the word splits as `x₁^{2+α} (x₁, x₂)` times the tail relator
`x₃^q (x₃, x₄) ⋯ (x_{n-1}, x_n)`, the `q ≠ 2` normal-form word on `n - 2` letters read on the tuple
shifted by two. This is the shape of the relator produced by the successive-approximation argument
for the dyadic relators of even rank. -/
theorem demushkinWordTwoEvenPadic_eq_padicPow_mul_labuteComm_mul (hn : 2 ≤ n) :
    demushkinWordTwoEvenPadic hH α q n x =
      hH.padicPow (x 0) (2 + α) * labuteComm (x 0) (x 1) *
        demushkinWordNeTwo q (n - 2) fun i ↦ x (i + 2) := by
  have hk : (n - 2) / 2 = n / 2 - 1 := by omega
  have hmap : ((List.range (n / 2 - 1)).map fun i ↦
      labuteComm (x (2 * i + 2)) (x (2 * i + 1 + 2))) =
      (List.range (n / 2 - 1)).map fun i ↦ labuteComm (x (2 * i + 2)) (x (2 * i + 3)) :=
    List.map_congr_left fun i _ ↦ by ring_nf
  rw [demushkinWordTwoEvenPadic_def, demushkinWordNeTwo_def, hk, hmap, mul_assoc, mul_assoc]

/-- At `α = 0` and `q = 0` the word is `x₁² (x₁, x₂)(x₃, x₄) ⋯ (x_{n-1}, x_n)`, the `q ≠ 2`
normal-form word at `q = 2`: the even dyadic normal form at level `f = ∞` with `α = 0`. -/
theorem demushkinWordTwoEvenPadic_zero_zero (hn : 2 ≤ n) :
    demushkinWordTwoEvenPadic hH 0 0 n x = demushkinWordNeTwo 2 n x := by
  rw [demushkinWordTwoEvenPadic_eq_padicPow_mul_labuteComm_mul hH 0 0 n x hn, add_zero,
    hH.padicPow_ofNat, demushkinWordNeTwo_eq_pow_mul_labuteComm_mul 2 hn]

variable {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
  [TotallyDisconnectedSpace K] (hK : IsProP 2 K)

/-- A continuous homomorphism of pro-`2` groups reads the word on the image tuple. -/
@[simp]
theorem map_demushkinWordTwoEvenPadic (φ : H →ₜ* K) :
    φ (demushkinWordTwoEvenPadic hH α q n x) = demushkinWordTwoEvenPadic hK α q n (φ ∘ x) := by
  have hpp : φ (hH.padicPow (x 0) (2 + α)) = hK.padicPow (φ (x 0)) (2 + α) :=
    hH.map_padicPow hK (φ : H →* K) φ.continuous (x 0) (2 + α)
  simp only [demushkinWordTwoEvenPadic_def, map_mul, map_pow, map_list_prod, List.map_map,
    Function.comp_def, map_labuteComm, hpp]

variable {A : Type*} [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A] [CompactSpace A]
  [TotallyDisconnectedSpace A]

/-- In a commutative pro-`2` group the word is `x₁^{2+α} x₃^q`. -/
theorem demushkinWordTwoEvenPadic_eq_of_commGroup (hA : IsProP 2 A) (y : ℕ → A) :
    demushkinWordTwoEvenPadic hA α q n y = hA.padicPow (y 0) (2 + α) * y 2 ^ q := by
  simp [demushkinWordTwoEvenPadic_def]

/-- A continuous character into a commutative pro-`2` group which is trivial on `x₁` and whose
value on `x₃` has trivial `q`-th power kills the word. -/
theorem map_demushkinWordTwoEvenPadic_eq_one (hA : IsProP 2 A) (φ : H →ₜ* A) (h₀ : φ (x 0) = 1)
    (h₂ : φ (x 2) ^ q = 1) : φ (demushkinWordTwoEvenPadic hH α q n x) = 1 := by
  rw [map_demushkinWordTwoEvenPadic hH α q n x hA φ, demushkinWordTwoEvenPadic_eq_of_commGroup,
    Function.comp_apply, Function.comp_apply, h₀, hA.one_padicPow, h₂, one_mul]

/-- For `α` and `q` even, the word lies in the pro-`2` Frattini subgroup: `x₁^{2+α}` is a `2`-adic
power with even exponent, `x₃^q` is a square and the remaining factors are commutators. -/
theorem demushkinWordTwoEvenPadic_mem_proPFrattini (hα : 2 ∣ α) (hq : 2 ∣ q) :
    demushkinWordTwoEvenPadic hH α q n x ∈ proPFrattini 2 H := by
  have h2 : ((2 : ℕ) : ℤ_[2]) ∣ 2 + α := by exact_mod_cast dvd_add (dvd_refl (2 : ℤ_[2])) hα
  refine mul_mem (mul_mem (mul_mem (hH.padicPow_mem_proPFrattini_of_dvd h2 _)
    (labuteComm_mem_proPFrattini Nat.prime_two _ _)) (pow_mem_proPFrattini_of_dvd hq _))
    (Subgroup.list_prod_mem _ ?_)
  simpa only [List.forall_mem_map] using fun i _ ↦ labuteComm_mem_proPFrattini Nat.prime_two _ _

end Word

end TauCeti

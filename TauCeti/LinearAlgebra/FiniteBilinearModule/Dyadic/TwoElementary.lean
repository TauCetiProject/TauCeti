/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.FiniteBilinearModule.Decomposition
public import TauCeti.LinearAlgebra.FiniteBilinearModule.Dyadic.GaussSum

/-!
# Two-elementary finite quadratic modules

A finite quadratic module is *`2`-elementary* when its group is killed by `2`, so that it is
`(ℤ/2)^a` for some `a`. This file shows that a nondegenerate `2`-elementary module is an orthogonal
sum of Nikulin's generators of exponent one: the cyclic modules `q_θ^{(2)}(2)` on `ℤ/2` with `θ`
odd, whose quadratic form takes the value `θ/4` on the generator, and the rank-two modules
`u^{(2)}(2)` and `v^{(2)}(2)` on `(ℤ/2)²`, whose quadratic forms take values in `½ℤ/ℤ`.

Reading off the Gauss-sum invariants of the summands, `±1` for each `q_θ^{(2)}(2)`, `0` for
`u^{(2)}(2)` and `4` for `v^{(2)}(2)`, constrains the Gauss-sum invariant `sign q ∈ ℤ/8` of a
nondegenerate `2`-elementary module of order `2^a`:

* `sign q ≡ a (mod 2)`;
* if `q` takes values in `½ℤ/ℤ`, that is, no `q_θ^{(2)}(2)` occurs, then `sign q ∈ {0, 4}`;
* if `a = 1`, then `sign q = ±1`;
* if `a = 2` and `sign q = 4`, then `q` takes values in `½ℤ/ℤ`.

Through Milgram's theorem these become conditions on the signatures of even lattices with
`2`-elementary discriminant group, the arithmetic half of Nikulin's Theorem 3.6.2.

## Main results

* `TauCeti.FiniteQuadraticModule.exists_isometry_prod_pi_of_two_nsmul_eq_zero`: a nondegenerate
  `2`-elementary module is an orthogonal sum of copies of `q_θ^{(2)}(2)`, `u^{(2)}(2)` and
  `v^{(2)}(2)`.
* `TauCeti.FiniteQuadraticModule.exists_gaussSign_eq_add_two_mul_of_two_nsmul_eq_zero`: the parity
  of the Gauss-sum invariant.
* `TauCeti.FiniteQuadraticModule.exists_gaussSign_eq_four_mul_of_quadratic_add_self_eq_zero`: the
  Gauss-sum invariant of a nondegenerate module with values in `½ℤ/ℤ` is `0` or `4`.
* `TauCeti.FiniteQuadraticModule.gaussSign_eq_one_or_eq_neg_one_of_natCard_eq_two`: the
  Gauss-sum invariant of a nondegenerate module of order two is `±1`.
* `TauCeti.FiniteQuadraticModule.quadratic_add_self_eq_zero_of_gaussSign_eq_four`: a
  nondegenerate `2`-elementary module of order four with invariant `4` takes values in `½ℤ/ℤ`.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*,
  Propositions 1.8.1 and 1.11.2, and §3.6 for `2`-elementary forms.
-/

public section

open QuadraticMap.IsometryEquiv

namespace TauCeti.FiniteQuadraticModule

universe u

/-! ## The decomposition -/

/-- A module isometric to a module killed by `2` is killed by `2`. -/
private theorem two_nsmul_eq_zero_of_isometry {B C : FiniteQuadraticModule} (f : Isometry B C)
    (h2 : ∀ x : C, 2 • x = 0) (x : B) : 2 • x = 0 :=
  f.toLinearEquiv.injective (by rw [map_nsmul, map_zero]; exact h2 _)

/-- The first summand of an orthogonal sum killed by `2` is killed by `2`. -/
private theorem two_nsmul_eq_zero_fst {B C : FiniteQuadraticModule}
    (h2 : ∀ x : B.prod C, 2 • x = 0) (y : B) : 2 • y = 0 := by
  simpa using congrArg Prod.fst (h2 (y, 0))

/-- The second summand of an orthogonal sum killed by `2` is killed by `2`. -/
private theorem two_nsmul_eq_zero_snd {B C : FiniteQuadraticModule}
    (h2 : ∀ x : B.prod C, 2 • x = 0) (y : C) : 2 • y = 0 := by
  simpa using congrArg Prod.snd (h2 (0, y))

/-- Each summand of an orthogonal sum of a family killed by `2` is killed by `2`. -/
private theorem two_nsmul_eq_zero_pi {ι : Type*} [Fintype ι] {B : ι → FiniteQuadraticModule}
    (h2 : ∀ x : pi B, 2 • x = 0) (i : ι) (y : B i) : 2 • y = 0 := by
  classical
  have h := congrFun (h2 (Pi.single i y)) i
  simp only [Pi.smul_apply, Pi.single_eq_same] at h
  exact h

/-- If `2` kills `1` in `ℤ/n`, then `n ∣ 2`. -/
private theorem dvd_two_of_two_nsmul_one_eq_zero {n : ℕ} (h : 2 • (1 : ZMod n) = 0) : n ∣ 2 :=
  (ZMod.natCast_eq_zero_iff 2 n).mp (by simpa [nsmul_eq_mul] using h)

/-- If `2` kills `1` in `ℤ/2^{k+1}`, then `k = 0`. -/
private theorem eq_zero_of_two_nsmul_one_eq_zero {k : ℕ} (h : 2 • (1 : ZMod (2 ^ (k + 1))) = 0) :
    k = 0 := by
  have := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp
    ((dvd_two_of_two_nsmul_one_eq_zero h).trans (pow_one 2).symm.dvd)
  omega

/-- **A nondegenerate `2`-elementary module is an orthogonal sum of generators of exponent one**:
of cyclic modules `q_θ^{(2)}(2)` with `θ` odd, and of copies of `u^{(2)}(2)` and `v^{(2)}(2)`.
This is the generator decomposition `exists_isometry_prod_pi_generators` in which `2` kills every
summand. -/
theorem exists_isometry_prod_pi_of_two_nsmul_eq_zero (A : FiniteQuadraticModule.{u})
    (hA : A.IsNondegenerate) (h2 : ∀ x : A, 2 • x = 0) :
    ∃ (b : ℕ) (η : Fin b → ℤ) (c d : ℕ), (∀ i, Odd (η i)) ∧
      Nonempty (Isometry ((pi fun i ↦ dyadicCyclic 1 (η i)).prod
        ((pi fun _ : Fin c ↦ dyadicU 1).prod (pi fun _ : Fin d ↦ dyadicV 1))) A) := by
  obtain ⟨a, m, hm, θ, b, k, η, c, ku, d, kv, hmθ, hη, ⟨f⟩⟩ :=
    exists_isometry_prod_pi_generators A hA
  have hf := two_nsmul_eq_zero_of_isometry f h2
  -- An odd cyclic summand `ℤ/m` with `m > 1` odd is not killed by `2`.
  have ha : a = 0 := by
    by_contra ha
    let i : Fin a := ⟨0, Nat.pos_of_ne_zero ha⟩
    have h : 2 • (1 : ZMod (m i)) = 0 := two_nsmul_eq_zero_pi (two_nsmul_eq_zero_fst hf) i _
    have h2m := Nat.le_of_dvd two_pos (dvd_two_of_two_nsmul_one_eq_zero h)
    have h1m := (hmθ i).1.one_lt
    obtain ⟨t, ht⟩ := hm i
    omega
  -- A summand of exponent `k + 1 ≥ 2` is not killed by `2`.
  have hk (i : Fin b) : k i = 0 := eq_zero_of_two_nsmul_one_eq_zero
    (two_nsmul_eq_zero_pi (two_nsmul_eq_zero_fst (two_nsmul_eq_zero_snd hf)) i _)
  have hku (i : Fin c) : ku i = 0 := by
    have h : 2 • ((1, 0) : ZMod (2 ^ (ku i + 1)) × ZMod (2 ^ (ku i + 1))) = 0 :=
      two_nsmul_eq_zero_pi
        (two_nsmul_eq_zero_fst (two_nsmul_eq_zero_snd (two_nsmul_eq_zero_snd hf))) i _
    exact eq_zero_of_two_nsmul_one_eq_zero (by simpa using congrArg Prod.fst h)
  have hkv (i : Fin d) : kv i = 0 := by
    have h : 2 • ((1, 0) : ZMod (2 ^ (kv i + 1)) × ZMod (2 ^ (kv i + 1))) = 0 :=
      two_nsmul_eq_zero_pi
        (two_nsmul_eq_zero_snd (two_nsmul_eq_zero_snd (two_nsmul_eq_zero_snd hf))) i _
    exact eq_zero_of_two_nsmul_one_eq_zero (by simpa using congrArg Prod.fst h)
  subst ha
  obtain rfl : k = fun _ ↦ 0 := funext hk
  obtain rfl : ku = fun _ ↦ 0 := funext hku
  obtain rfl : kv = fun _ ↦ 0 := funext hkv
  -- The empty orthogonal sum of odd cyclic summands is trivial and can be dropped.
  exact ⟨b, η, c, d, hη, ⟨(uniqueProd _ _).symm.trans f⟩⟩

/-! ## Numerical invariants -/

/-- The order, Gauss-sum invariant and `½ℤ/ℤ`-valuedness of an orthogonal sum of `b` cyclic
generators `q_θ^{(2)}(2)`, `c` copies of `u^{(2)}(2)` and `d` copies of `v^{(2)}(2)`. -/
private theorem exists_invariants_of_two_nsmul_eq_zero {A : FiniteQuadraticModule.{u}}
    (hA : A.IsNondegenerate) (h2 : ∀ x : A, 2 • x = 0) :
    ∃ (b c d : ℕ) (s : Fin b → ZMod 8), (∀ i, s i = 1 ∨ s i = -1) ∧
      Nat.card A = 2 ^ (b + 2 * (c + d)) ∧ A.gaussSign = ∑ i, s i + 4 * d ∧
      ((∀ x : A, A.quadratic x + A.quadratic x = 0) ↔ b = 0) := by
  obtain ⟨b, η, c, d, hη, ⟨f⟩⟩ := exists_isometry_prod_pi_of_two_nsmul_eq_zero A hA h2
  have hcyc : ∀ i, (dyadicCyclic 1 (η i)).IsNondegenerate :=
    fun i ↦ (isNondegenerate_dyadicCyclic_iff _ _).2 (hη i)
  refine ⟨b, c, d, fun i ↦ (dyadicCyclic 1 (η i)).gaussSign,
    fun i ↦ gaussSign_dyadicCyclic_one_eq_one_or_eq_neg_one (hη i), ?_, ?_, ?_⟩
  · rw [← Nat.card_congr f.toLinearEquiv.toEquiv]
    simp only [Nat.card_prod, Nat.card_pi, natCard_dyadicCyclic, natCard_dyadicU, natCard_dyadicV,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [pow_add, pow_mul, pow_add]
    norm_num
  · rw [← f.gaussSign_eq, gaussSign_prod ((isNondegenerate_pi_iff _).2 hcyc)
        (by simp [isNondegenerate_dyadicU, isNondegenerate_dyadicV]),
      gaussSign_prod (by simp [isNondegenerate_dyadicU]) (by simp [isNondegenerate_dyadicV]),
      gaussSign_pi _ hcyc, gaussSign_pi _ fun _ ↦ isNondegenerate_dyadicU _,
      gaussSign_pi _ fun _ ↦ isNondegenerate_dyadicV _]
    simp [gaussSign_dyadicU, gaussSign_dyadicV, mul_comm]
  · -- The rank-two generators take values in `½ℤ/ℤ`; `q_θ^{(2)}(2)` takes `θ/4` on `1`.
    have hU (y : ZMod (2 ^ 1) × ZMod (2 ^ 1)) :
        (dyadicU 1).quadratic y + (dyadicU 1).quadratic y = 0 := by
      rw [dyadicU_quadratic, ← map_add, ← two_mul, show (2 : ZMod (2 ^ 1)) = 0 from rfl,
        zero_mul, map_zero]
    have hV (y : ZMod (2 ^ 1) × ZMod (2 ^ 1)) :
        (dyadicV 1).quadratic y + (dyadicV 1).quadratic y = 0 := by
      rw [dyadicV_quadratic, ← map_add, ← two_mul, show (2 : ZMod (2 ^ 1)) = 0 from rfl,
        zero_mul, map_zero]
    constructor
    · intro h
      by_contra hb
      obtain ⟨i⟩ : Nonempty (Fin b) := ⟨⟨0, Nat.pos_of_ne_zero hb⟩⟩
      -- The generator of the `i`-th cyclic summand has `q = θ/4`, so `q + q = θ/2 ≠ 0`.
      obtain ⟨x₀, hx₀i, hx₀j⟩ : ∃ x₀ : pi fun i ↦ dyadicCyclic 1 (η i),
          x₀ i = (1 : ZMod (2 ^ 1)) ∧ ∀ j ≠ i, x₀ j = 0 :=
        ⟨@Pi.single _ (fun j ↦ dyadicCyclic 1 (η j)) _ _ i (1 : ZMod (2 ^ 1)),
          Pi.single_eq_same _ _, fun j hj ↦ Pi.single_eq_of_ne hj _⟩
      have hq := dyadicCyclic_quadratic_intCast 1 (η i) 1
      rw [Int.cast_one] at hq
      have hi := h (f (x₀, 0))
      rw [f.map_app, prod_quadratic, QuadraticMap.map_zero, add_zero, pi_quadratic,
        Finset.sum_eq_single i (fun j _ hj ↦ by rw [hx₀j j hj, QuadraticMap.map_zero]) (by simp),
        hx₀i, hq, ← AddCircle.coe_add, AddCircle.coe_eq_zero_iff] at hi
      obtain ⟨n, hn⟩ := hi
      have hn' : ((2 * n : ℤ) : ℚ) = η i := by
        rw [zsmul_eq_mul, mul_one] at hn
        push_cast
        rw [hn]
        ring
      obtain ⟨t, ht⟩ := hη i
      have := Int.cast_injective hn'
      omega
    · rintro rfl x
      obtain ⟨y, rfl⟩ := f.toLinearEquiv.surjective x
      -- `f` applies as its underlying linear equivalence.
      rw [show f.toLinearEquiv y = f y from rfl, f.map_app]
      obtain ⟨y₁, y₂, y₃⟩ := y
      have h₁ : (pi fun i : Fin 0 ↦ dyadicCyclic 1 (η i)).quadratic y₁ = 0 := by
        rw [pi_quadratic, Finset.univ_eq_empty, Finset.sum_empty]
      have h₂ : (pi fun _ : Fin c ↦ dyadicU 1).quadratic y₂ +
          (pi fun _ : Fin c ↦ dyadicU 1).quadratic y₂ = 0 := by
        rw [pi_quadratic, ← Finset.sum_add_distrib]
        exact Finset.sum_eq_zero fun i _ ↦ hU _
      have h₃ : (pi fun _ : Fin d ↦ dyadicV 1).quadratic y₃ +
          (pi fun _ : Fin d ↦ dyadicV 1).quadratic y₃ = 0 := by
        rw [pi_quadratic, ← Finset.sum_add_distrib]
        exact Finset.sum_eq_zero fun i _ ↦ hV _
      rw [prod_quadratic, prod_quadratic, h₁, zero_add, add_add_add_comm, h₂, h₃, add_zero]

/-- **The Gauss-sum invariant of a nondegenerate `2`-elementary module of order `2^a` has the
parity of `a`**: each cyclic summand `q_θ^{(2)}(2)` contributes `±1`, and each rank-two summand
contributes `0` or `4` while adding `2` to `a`. -/
theorem exists_gaussSign_eq_add_two_mul_of_two_nsmul_eq_zero {A : FiniteQuadraticModule.{u}}
    (hA : A.IsNondegenerate) (h2 : ∀ x : A, 2 • x = 0) {a : ℕ} (ha : Nat.card A = 2 ^ a) :
    ∃ k : ZMod 8, A.gaussSign = a + 2 * k := by
  obtain ⟨b, c, d, s, hs, hcard, hsign, -⟩ := exists_invariants_of_two_nsmul_eq_zero hA h2
  have hab : a = b + 2 * (c + d) := Nat.pow_right_injective le_rfl (ha.symm.trans hcard)
  -- Write each `s i = 1 + 2 tᵢ` with `tᵢ ∈ {0, -1}`.
  have hst (i : Fin b) : ∃ t : ZMod 8, s i = 1 + 2 * t :=
    (hs i).elim (fun h ↦ ⟨0, by rw [h]; ring⟩) (fun h ↦ ⟨-1, by rw [h]; ring⟩)
  choose t ht using hst
  refine ⟨∑ i, t i + 2 * d - (c + d), ?_⟩
  rw [hsign, hab, Finset.sum_congr rfl fun i _ ↦ ht i, Finset.sum_add_distrib,
    ← Finset.mul_sum]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  push_cast
  ring

/-- A nondegenerate module whose quadratic form takes values in `½ℤ/ℤ` is killed by `2`: the
pairing `q(x + y) - q(x) - q(y)` is then killed by `2`. -/
theorem two_nsmul_eq_zero_of_quadratic_add_self_eq_zero {A : FiniteQuadraticModule.{u}}
    (hA : A.IsNondegenerate) (hq : ∀ x : A, A.quadratic x + A.quadratic x = 0) (x : A) :
    2 • x = 0 := by
  refine FiniteBilinearModule.IsNondegenerate.eq_zero_of_forall_pairing_eq_zero _ hA fun y ↦ ?_
  rw [FiniteBilinearModule.pairing_nsmul_left, ← polar_eq_pairing, QuadraticMap.polar, two_nsmul]
  calc _ = (A.quadratic (x + y) + A.quadratic (x + y)) - (A.quadratic x + A.quadratic x) -
        (A.quadratic y + A.quadratic y) := by abel
    _ = 0 := by rw [hq, hq, hq, sub_zero, sub_zero]

/-- **A nondegenerate module whose quadratic form takes values in `½ℤ/ℤ` has Gauss-sum invariant
`0` or `4`**: it is an orthogonal sum of copies of `u^{(2)}(2)` and `v^{(2)}(2)`. -/
theorem exists_gaussSign_eq_four_mul_of_quadratic_add_self_eq_zero
    {A : FiniteQuadraticModule.{u}} (hA : A.IsNondegenerate)
    (hq : ∀ x : A, A.quadratic x + A.quadratic x = 0) : ∃ k : ZMod 8, A.gaussSign = 4 * k := by
  obtain ⟨b, c, d, s, -, -, hsign, hb⟩ := exists_invariants_of_two_nsmul_eq_zero hA
    (two_nsmul_eq_zero_of_quadratic_add_self_eq_zero hA hq)
  obtain rfl := hb.1 hq
  exact ⟨d, by simp [hsign]⟩

/-- **A nondegenerate module of order two has Gauss-sum invariant `±1`**: it is `q_θ^{(2)}(2)` for
an odd `θ`. -/
theorem gaussSign_eq_one_or_eq_neg_one_of_natCard_eq_two {A : FiniteQuadraticModule.{u}}
    (hA : A.IsNondegenerate) (hcard : Nat.card A = 2) :
    A.gaussSign = 1 ∨ A.gaussSign = -1 := by
  have h2 (x : A) : 2 • x = 0 := hcard ▸ card_nsmul_eq_zero'
  obtain ⟨b, c, d, s, hs, hcard', hsign, -⟩ := exists_invariants_of_two_nsmul_eq_zero hA h2
  have hb : b + 2 * (c + d) = 1 :=
    Nat.pow_right_injective le_rfl (hcard'.symm.trans (hcard.trans (pow_one 2).symm))
  obtain ⟨rfl, hd⟩ : b = 1 ∧ d = 0 := by omega
  simpa [hsign, hd] using hs 0

/-- **A nondegenerate `2`-elementary module of order four with Gauss-sum invariant `4` takes values
in `½ℤ/ℤ`**: two cyclic summands `q_θ^{(2)}(2)` would give an invariant in `{-2, 0, 2}`, so it is
`v^{(2)}(2)`. -/
theorem quadratic_add_self_eq_zero_of_gaussSign_eq_four {A : FiniteQuadraticModule.{u}}
    (hA : A.IsNondegenerate) (h2 : ∀ x : A, 2 • x = 0) (hcard : Nat.card A = 4)
    (hsign : A.gaussSign = 4) (x : A) : A.quadratic x + A.quadratic x = 0 := by
  obtain ⟨b, c, d, s, hs, hcard', hsign', hb⟩ := exists_invariants_of_two_nsmul_eq_zero hA h2
  have hb' : b + 2 * (c + d) = 2 :=
    Nat.pow_right_injective le_rfl (hcard'.symm.trans (hcard.trans (by norm_num)))
  refine hb.2 ?_ x
  by_contra hb0
  obtain ⟨rfl, rfl, rfl⟩ : b = 2 ∧ c = 0 ∧ d = 0 := by omega
  rw [hsign, Fin.sum_univ_two] at hsign'
  rcases hs 0 with h0 | h0 <;> rcases hs 1 with h1 | h1 <;> rw [h0, h1] at hsign' <;>
    revert hsign' <;> decide

end TauCeti.FiniteQuadraticModule

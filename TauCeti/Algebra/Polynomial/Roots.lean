/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Order.Filter.Basic

/-!
# Multiplicities of labelled roots

If a finite family enumerates a polynomial's roots with multiplicity, the multiplicity
at each label depends only on which labels coincide. Consequently an eventually constant
collision relation gives eventually constant multiplicities, without any continuity or
splitting assumptions on the polynomial family.

We also count the root zero: it occurs in `f.roots` with multiplicity the order of vanishing
`f.natTrailingDegree`, so the roots satisfying a predicate that holds at zero number
`f.natTrailingDegree` plus the nonzero roots satisfying it. Over any integral domain, summing
`f.rootMultiplicity` over any finite set of points never exceeds `f.natDegree`
(`Polynomial.sum_rootMultiplicity_le_natDegree`), including for `f = 0`, and summing it over the
distinct roots gives the number of roots counted with multiplicity
(`Polynomial.sum_rootMultiplicity_roots_toFinset_eq_card_roots`). So if
`k ≤ f.rootMultiplicity a` for every `a` in a finite set `s`, then `k * #s ≤ f.natDegree`
(`Polynomial.mul_card_le_natDegree_of_le_rootMultiplicity`).

Over an arbitrary commutative ring, distinct points are not enough (in `ZMod 4`, `2 * X` has the
simple roots `0` and `2` but degree `1`), but points whose pairwise differences are units are: the
powers `(X - a) ^ f.rootMultiplicity a` at such points are pairwise coprime, so their product
divides `f` (`Polynomial.sum_rootMultiplicity_le_natDegree_of_pairwise_isUnit_sub`).

Finally, a nonzero multiple of `∏_{b ∈ E} (X - b)` is divisible by `(X - a)^k` exactly when `a`
occurs at least `k` times in `E` (`Polynomial.X_sub_C_pow_dvd_smul_multiset_prod_iff`), the root
multiplicity of a multiset product of nonzero polynomials is the sum of the root multiplicities of
its factors (`Polynomial.rootMultiplicity_multiset_prod`), and pushing a factorization
`P = C c * s.prod` forward along `φ : A →+* K` gives the nonvanishing criterion
`Polynomial.map_ne_zero_iff_of_eq_C_mul_multiset_prod` and root-multiplicity sum formula
`Polynomial.rootMultiplicity_map_eq_sum`.

Over an infinite commutative ring `R`, polynomial root counting also implies that no positive
power sends every nonzero element to `1` (`TauCeti.not_forall_pow_eq_one`), that no two ring
homomorphisms `g, g' : R →+* S` into a nontrivial commutative ring satisfy a nontrivial identity
`g x ^ d * g' x ^ n = 1` on all nonzero elements (`RingHom.not_forall_map_pow_mul_map_pow_eq_one`,
with `RingHom.not_forall_map_mul_map_eq_one` and `RingHom.not_forall_map_pow_mul_pow_eq_one`),
and that if `R` has no zero divisors then any subring containing all `a`-th powers (`0 < a`) is
infinite (`Subring.infinite_of_pow_mem`).
-/

public section

open Filter Polynomial

private theorem isDomain_of_forall_map_pow_mul_map_pow_eq_one {R S : Type*} [CommRing R]
    [Nontrivial R] [CommRing S] [Nontrivial S] (g g' : R →+* S) {d n : ℕ} (hd : d ≠ 0)
    (h : ∀ x : R, x ≠ 0 → g x ^ d * g' x ^ n = 1) : IsDomain R :=
  let _ : NoZeroDivisors R := ⟨fun {a b} hab => by_contra fun hne => by
    rw [not_or] at hne
    have h1 : (g a ^ d * g' a ^ n) * (g b ^ d * g' b ^ n) = 1 := by
      rw [h a hne.1, h b hne.2, mul_one]
    rw [mul_mul_mul_comm, ← mul_pow, ← map_mul, hab, map_zero, zero_pow hd, zero_mul] at h1
    exact zero_ne_one h1⟩
  NoZeroDivisors.to_isDomain R

namespace TauCeti

/-- A finite enumeration of roots with an eventually constant collision relation has
eventually constant multiplicity at each label. The parameter filter is arbitrary, and
the root enumeration at the reference parameter is supplied separately. -/
theorem eventually_rootMultiplicity_eq_of_roots_eq_map
    {K B ι : Type*} [CommRing K] [IsDomain K]
    {I : Finset ι} {f : ι → B → K} {Q : B → Polynomial K} {x₀ : B} {l : Filter B}
    (hroots₀ : (Q x₀).roots = I.val.map (fun i ↦ f i x₀))
    (hroots : ∀ᶠ x in l, (Q x).roots = I.val.map (fun i ↦ f i x))
    (hrel : ∀ᶠ x in l, ∀ i ∈ I, ∀ j ∈ I, f i x = f j x ↔ f i x₀ = f j x₀) :
    ∀ᶠ x in l, ∀ i ∈ I, (Q x).rootMultiplicity (f i x) =
      (Q x₀).rootMultiplicity (f i x₀) := by
  classical
  filter_upwards [hrel, hroots] with x hx hxroots i hi
  rw [← count_roots, ← count_roots, hxroots, hroots₀,
    Multiset.count_map, Multiset.count_map]
  exact congrArg _ (Multiset.filter_congr fun j hj ↦ hx i hi j (Finset.mem_val.mp hj))

/-- No positive power sends every nonzero element of an infinite commutative ring to `1`. -/
theorem not_forall_pow_eq_one {R : Type*} [CommRing R] [Infinite R] {n : ℕ} (hn : n ≠ 0) :
    ¬ ∀ x : R, x ≠ 0 → x ^ n = 1 := fun h => by
  have : Nontrivial R := Infinite.instNontrivial R
  have : IsDomain R := isDomain_of_forall_map_pow_mul_map_pow_eq_one
    (RingHom.id R) (RingHom.id R) (n := 0) hn fun x hx => by simpa using h x hx
  exact mul_ne_zero (M₀ := R[X]) X_ne_zero
    (fun h1 => by simpa [hn] using congrArg (eval (0 : R)) h1)
    (Polynomial.zero_of_eval_zero (X * (X ^ n - 1) : R[X]) fun c => by
      by_cases hc : c = 0 <;> simp [hc, h])

end TauCeti

namespace Polynomial

variable {R : Type*} [CommRing R] [IsDomain R]

/-- The root zero occurs in `f.roots` with multiplicity the order of vanishing of `f` at zero. -/
theorem count_zero_roots [DecidableEq R] (f : R[X]) : f.roots.count 0 = f.natTrailingDegree := by
  rw [count_roots, rootMultiplicity_eq_natTrailingDegree']

/-- The number of roots satisfying a predicate that holds at zero is the order of vanishing at
zero plus the number of nonzero roots satisfying it. -/
theorem card_filter_roots_eq_natTrailingDegree_add [DecidableEq R] (f : R[X]) {q : R → Prop}
    [DecidablePred q] (hq : q 0) :
    (f.roots.filter q).card =
      f.natTrailingDegree + (f.roots.filter fun α => α ≠ 0 ∧ q α).card := by
  have hsplit : f.roots.filter q =
      f.roots.filter (· = 0) + f.roots.filter fun α => α ≠ 0 ∧ q α := by
    rw [← Multiset.filter_add_not (· = 0) (f.roots.filter q), Multiset.filter_filter,
      Multiset.filter_filter]
    congr 1
    exact Multiset.filter_congr fun α _ => ⟨And.left, fun h => ⟨h, h ▸ hq⟩⟩
  rw [hsplit, Multiset.card_add, Multiset.filter_eq', Multiset.card_replicate, count_zero_roots]

/-- Over a domain, the root multiplicities of `f` at its distinct roots add up to the number of
roots of `f` counted with multiplicity. -/
@[simp]
theorem sum_rootMultiplicity_roots_toFinset_eq_card_roots [DecidableEq R] (f : R[X]) :
    ∑ a ∈ f.roots.toFinset, f.rootMultiplicity a = f.roots.card := by
  simpa only [count_roots] using Multiset.toFinset_sum_count_eq f.roots

/-- Over a domain, the sum of root multiplicities of a polynomial `f` across any finite set of
points is at most `f.natDegree` (also when `f = 0`, where every multiplicity vanishes). -/
theorem sum_rootMultiplicity_le_natDegree (f : R[X]) (s : Finset R) :
    ∑ a ∈ s, f.rootMultiplicity a ≤ f.natDegree := by
  classical
  calc ∑ a ∈ s, f.rootMultiplicity a
      = ∑ a ∈ s, f.roots.count a := Finset.sum_congr rfl fun _ _ ↦ (count_roots f).symm
    _ ≤ ∑ a ∈ f.roots.toFinset, f.roots.count a :=
        Finset.sum_le_sum_of_ne_zero fun _ _ ha ↦
          Multiset.mem_toFinset.mpr (Multiset.count_pos.mp (Nat.pos_of_ne_zero ha))
    _ = f.roots.card := Multiset.toFinset_sum_count_eq f.roots
    _ ≤ f.natDegree := card_roots' f

/-- **The root-count inequality.** Over a domain, if `k ≤ f.rootMultiplicity a` for every `a` in
a finite set `s`, then `k * #s ≤ f.natDegree`. -/
theorem mul_card_le_natDegree_of_le_rootMultiplicity {f : R[X]} {s : Finset R} {k : ℕ}
    (h : ∀ a ∈ s, k ≤ f.rootMultiplicity a) : k * s.card ≤ f.natDegree := by
  rw [mul_comm, ← smul_eq_mul]
  exact (Finset.card_nsmul_le_sum s _ k h).trans (sum_rootMultiplicity_le_natDegree f s)

omit [IsDomain R] in
/-- **Counting roots at points with unit differences.** Over any commutative ring, if the pairwise
differences of the points `a i`, `i ∈ s`, are units, then the root multiplicities of `f` at these
points add up to at most `f.natDegree` (also when `f = 0`, where every multiplicity vanishes). -/
theorem sum_rootMultiplicity_le_natDegree_of_pairwise_isUnit_sub {ι : Type*} {s : Finset ι}
    {a : ι → R} (ha : (s : Set ι).Pairwise fun i j ↦ IsUnit (a i - a j)) (f : R[X]) :
    ∑ i ∈ s, f.rootMultiplicity (a i) ≤ f.natDegree := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  have : Nontrivial R := nontrivial_iff.mp (nontrivial_of_ne f 0 hf)
  have hmonic : ∀ i ∈ s, ((X - C (a i)) ^ f.rootMultiplicity (a i)).Monic :=
    fun i _ ↦ (monic_X_sub_C (a i)).pow _
  -- the powers `(X - a i) ^ mᵢ` are pairwise coprime divisors of `f`, so their product divides it
  have hdvd : ∏ i ∈ s, (X - C (a i)) ^ f.rootMultiplicity (a i) ∣ f :=
    Finset.prod_dvd_of_coprime
      (fun _ hi _ hj hij ↦ (isCoprime_X_sub_C_of_isUnit_sub (ha hi hj hij)).pow)
      fun i _ ↦ pow_rootMultiplicity_dvd f (a i)
  calc ∑ i ∈ s, f.rootMultiplicity (a i)
      = (∏ i ∈ s, (X - C (a i)) ^ f.rootMultiplicity (a i)).natDegree := by
        rw [natDegree_prod_of_monic _ _ hmonic]
        simp only [(monic_X_sub_C _).natDegree_pow, natDegree_X_sub_C, mul_one]
    _ ≤ f.natDegree := (monic_prod_of_monic _ _ hmonic).natDegree_le_of_dvd hf hdvd

/-- Over an integral domain, if `f : α → R` is injective on a finite set `s : Finset α`, then the
number of points `x ∈ s` at which a nonzero polynomial `c : R[X]` vanishes at `f x` is at most
`c.natDegree`. -/
theorem card_filter_eval_comp_eq_zero_le {α : Type*} [DecidableEq R] {c : R[X]} (hc0 : c ≠ 0)
    {s : Finset α} {f : α → R} (hinj : Set.InjOn f (s : Set α)) :
    (s.filter fun x ↦ c.eval (f x) = 0).card ≤ c.natDegree := by
  let s₀ : Finset α := s.filter fun x ↦ c.eval (f x) = 0
  have hinj₀ : Set.InjOn f (s₀ : Set α) :=
    hinj.mono (Finset.coe_subset.mpr (Finset.filter_subset _ s))
  rw [← Finset.card_image_of_injOn hinj₀]
  refine card_le_degree_of_subset_roots fun b hb ↦ ?_
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp (Finset.mem_val.mp hb)
  exact (mem_roots hc0).mpr (Finset.mem_filter.mp hx).2

/-- Over an integral domain, the root multiplicity of a multiset product of nonzero polynomials is
the sum of the root multiplicities of its factors. -/
theorem rootMultiplicity_multiset_prod (a : R) (s : Multiset R[X]) (hs : ∀ p ∈ s, p ≠ 0) :
    s.prod.rootMultiplicity a = (s.map fun p ↦ p.rootMultiplicity a).sum := by
  classical
  rw [← count_roots, roots_multiset_prod s fun h0 ↦ hs 0 h0 rfl, Multiset.count_bind]
  simp [count_roots]

/-- A nonzero multiple of `∏_{b ∈ E} (X - b)` is divisible by `(X - a)^k` exactly when `a` occurs
at least `k` times in `E`. -/
theorem X_sub_C_pow_dvd_smul_multiset_prod_iff [DecidableEq R] {E : Multiset R} {a c : R}
    (hc : c ≠ 0) {k : ℕ} :
    (X - C a) ^ k ∣ c • (E.map fun b ↦ X - C b).prod ↔ k ≤ E.count a := by
  rw [← le_rootMultiplicity_iff (smul_ne_zero hc (monic_multisetProd_X_sub_C E).ne_zero),
    ← count_roots, roots_smul_of_ne_zero _ hc, roots_multiset_prod_X_sub_C]

end Polynomial

namespace Polynomial

/-- Given `P = C c * s.prod`, the mapped factorization
`P.map φ = C (φ c) * (s.map (mapRingHom φ)).prod` is unconditional; if the target `K` has no zero
divisors, then `P.map φ ≠ 0` if and only if `φ c ≠ 0` and `F.map φ ≠ 0` for every factor
`F ∈ s`. -/
theorem map_ne_zero_iff_of_eq_C_mul_multiset_prod {A K : Type*} [CommSemiring A] [CommSemiring K]
    [NoZeroDivisors K] {φ : A →+* K} {P : A[X]} {c : A} {s : Multiset A[X]}
    (hPeq : P = C c * s.prod) :
    P.map φ ≠ 0 ↔ φ c ≠ 0 ∧ ∀ F ∈ s, F.map φ ≠ 0 := by
  rw [hPeq, Polynomial.map_mul, map_C, ← coe_mapRingHom, map_multiset_prod,
    mul_ne_zero_iff, C_ne_zero]
  refine and_congr_right fun hcp ↦ ⟨fun h F hF h0 ↦ ?_, fun h ↦ ?_⟩
  · exact h (Multiset.prod_eq_zero (Multiset.mem_map.mpr ⟨F, hF, h0⟩))
  · have : Nontrivial K := ⟨⟨φ c, 0, hcp⟩⟩
    exact Multiset.prod_ne_zero fun h0 ↦
      let ⟨F, hF, hFeq⟩ := Multiset.mem_map.mp h0
      h F hF hFeq

/-- Over an integral domain `K`, if `P = C c * s.prod` in `A[X]` and `P.map φ ≠ 0` for a ring
homomorphism `φ : A →+* K`, then the root multiplicity of `P.map φ` at `a` equals the sum of the
root multiplicities of `F.map φ` at `a` over `F ∈ s`. -/
theorem rootMultiplicity_map_eq_sum {A K : Type*} [CommSemiring A] [CommRing K] [IsDomain K]
    {φ : A →+* K} {P : A[X]} {c : A} {s : Multiset A[X]}
    (hPeq : P = C c * s.prod) (hPmap : P.map φ ≠ 0) (a : K) :
    (P.map φ).rootMultiplicity a =
      (s.map fun F ↦ (F.map φ).rootMultiplicity a).sum := by
  rw [hPeq, Polynomial.map_mul, map_C, ← coe_mapRingHom, map_multiset_prod] at hPmap ⊢
  have hc0 : C (φ c) ≠ 0 := left_ne_zero_of_mul hPmap
  have hprod_ne : (s.map (mapRingHom φ)).prod ≠ 0 := right_ne_zero_of_mul hPmap
  have hmap_ne : ∀ p ∈ s.map (mapRingHom φ), p ≠ 0 := fun p hp h0 ↦
    hprod_ne (Multiset.prod_eq_zero (h0 ▸ hp))
  rw [rootMultiplicity_mul (mul_ne_zero hc0 hprod_ne),
    rootMultiplicity_eq_zero (by simpa using C_ne_zero.mp hc0), zero_add,
    rootMultiplicity_multiset_prod a _ hmap_ne, Multiset.map_map]
  simp only [Function.comp_apply, coe_mapRingHom]

end Polynomial

namespace RingHom

private theorem not_forall_map_pow_mul_map_pow_eq_one_of_ne_zero {R S : Type*} [CommRing R]
    [Infinite R] [CommRing S] [Nontrivial S] (g g' : R →+* S) {d n : ℕ} (hd : d ≠ 0) :
    ¬ ∀ x : R, x ≠ 0 → g x ^ d * g' x ^ n = 1 := fun h => by
  have : Nontrivial R := Infinite.instNontrivial R
  have hginj : Function.Injective g := (injective_iff_map_eq_zero g).mpr fun x hx => by_contra
    fun hx0 => (zero_ne_one (α := S)) (by simpa [hx, zero_pow hd] using h x hx0)
  have : IsDomain R := isDomain_of_forall_map_pow_mul_map_pow_eq_one g g' hd h
  rcases eq_or_ne n 0 with rfl | hn
  · exact TauCeti.not_forall_pow_eq_one hd fun x hx => hginj (by simpa [map_pow] using h x hx)
  let Q : R[X] := (X ^ n + 1) ^ d * (X ^ d + 1) ^ n - X ^ (d * n)
  let P : R[X] := X * (X ^ n + 1) * Q
  refine mul_ne_zero (mul_ne_zero X_ne_zero fun h1 => by simpa [hn] using congrArg (eval 0) h1)
    (fun h2 => by simpa [Q, hd, hn, Nat.mul_ne_zero hd hn] using congrArg (eval 0) h2)
    (Polynomial.zero_of_eval_zero P fun c => ?_)
  simp only [P, Q, eval_mul, eval_sub, eval_pow, eval_add, eval_X, eval_one]
  by_cases hc0 : c = 0; · simp [hc0]
  by_cases hcn1 : c ^ n + 1 = 0; · simp [hcn1]
  -- When `c ≠ 0` and `c ^ n + 1 ≠ 0`, `g c ^ d * g' c ^ n = 1` gives the linking identity
  -- `g (c ^ d + 1) = g c ^ d * g' (c ^ n + 1)` (`hlink`); substituting this into
  -- `g ((c ^ n + 1) ^ d * (c ^ d + 1) ^ n)` collapses `g (c ^ n + 1) ^ d * g' (c ^ n + 1) ^ n`
  -- to `1`, leaving `g (c ^ (d * n))`. Injectivity of `g` then forces `Q.eval c = 0`, so `P`
  -- vanishes everywhere.
  have hlink : g c ^ d * g' (c ^ n + 1) = g (c ^ d + 1) := by
    simp [mul_add, h c hc0, add_comm]
  have hgeq : g ((c ^ n + 1) ^ d * (c ^ d + 1) ^ n) = g (c ^ (d * n)) := by
    rw [map_mul, map_pow, map_pow, ← hlink, mul_pow]
    calc g (c ^ n + 1) ^ d * ((g c ^ d) ^ n * g' (c ^ n + 1) ^ n)
      _ = (g c ^ d) ^ n * (g (c ^ n + 1) ^ d * g' (c ^ n + 1) ^ n) := by ring
      _ = g (c ^ (d * n)) := by rw [h _ hcn1, mul_one, ← pow_mul, map_pow]
  rw [sub_eq_zero.mpr (hginj hgeq), mul_zero]

/-- **No two ring homomorphisms out of an infinite commutative ring into a nontrivial commutative
ring satisfy a nontrivial negative-exponent power law on nonzero elements.** -/
theorem not_forall_map_pow_mul_map_pow_eq_one {R S : Type*} [CommRing R] [Infinite R]
    [CommRing S] [Nontrivial S] (g g' : R →+* S) {d n : ℕ} (hdn : d ≠ 0 ∨ n ≠ 0) :
    ¬ ∀ x : R, x ≠ 0 → g x ^ d * g' x ^ n = 1 :=
  hdn.elim (not_forall_map_pow_mul_map_pow_eq_one_of_ne_zero g g') fun hn h =>
    not_forall_map_pow_mul_map_pow_eq_one_of_ne_zero g' g hn fun x hx => by
      rw [mul_comm]; exact h x hx

/-- **No two ring homomorphisms out of an infinite commutative ring into a nontrivial commutative
ring are pointwisely inverse on nonzero elements.** -/
theorem not_forall_map_mul_map_eq_one {R S : Type*} [CommRing R] [Infinite R]
    [CommRing S] [Nontrivial S] (g g' : R →+* S) : ¬ ∀ x : R, x ≠ 0 → g x * g' x = 1 := by
  simpa only [pow_one] using
    not_forall_map_pow_mul_map_pow_eq_one g g' (d := 1) (n := 1) (.inl one_ne_zero)

/-- **No ring endomorphism of an infinite commutative ring satisfies a nontrivial negative-exponent
power law on nonzero elements.** -/
theorem not_forall_map_pow_mul_pow_eq_one {R : Type*} [CommRing R] [Infinite R] (g : R →+* R)
    {d n : ℕ} (hdn : d ≠ 0 ∨ n ≠ 0) : ¬ ∀ x : R, x ≠ 0 → g x ^ d * x ^ n = 1 :=
  have : Nontrivial R := Infinite.instNontrivial R
  not_forall_map_pow_mul_map_pow_eq_one g (RingHom.id R) hdn

end RingHom

namespace Subring

/-- A subring of an infinite commutative ring without zero divisors containing every `a`-th power
(`0 < a`) is infinite. -/
theorem infinite_of_pow_mem {R : Type*} [CommRing R] [NoZeroDivisors R] [Infinite R]
    (E : Subring R) {a : ℕ} (ha : 0 < a) (hpow : ∀ x : R, x ^ a ∈ E) : Infinite E := by
  classical
  have : IsDomain R := NoZeroDivisors.to_isDomain R
  by_contra hfin; rw [not_infinite_iff_finite] at hfin
  exact Set.infinite_univ
    ((Set.finite_iUnion fun c : E => (Polynomial.nthRootsFinset a c.val).finite_toSet).subset
      fun x _ => Set.mem_iUnion.mpr ⟨⟨x ^ a, hpow x⟩, by simp [Polynomial.mem_nthRootsFinset ha]⟩)

end Subring

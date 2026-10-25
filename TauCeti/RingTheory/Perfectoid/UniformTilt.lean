/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Perfection
public import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
public import TauCeti.RingTheory.Huber.Uniform
import Mathlib.Algebra.CharP.Lemmas

/-!
# The tilt of a complete uniform Tate ring

Fix a prime `p` and let `B` be a complete Hausdorff uniform Tate ring in which `p` is
topologically nilpotent; `B` is not assumed perfectoid. Its *tilt* is the multiplicative monoid
`B♭ = lim_{x ↦ x ^ p} B` of compatible systems `(x⁽ⁿ⁾)ₙ` with `(x⁽ⁿ⁺¹⁾) ^ p = x⁽ⁿ⁾` (Mathlib's
`Perfection B p`), with coordinatewise multiplication and the *limit addition*
`(x + y)⁽ⁱ⁾ = lim_{m → ∞} (x⁽ⁱ⁺ᵐ⁾ + y⁽ⁱ⁺ᵐ⁾) ^ p ^ m`.
This file constructs that addition and shows that it makes `B♭` a perfect commutative ring of
characteristic `p` (when `B ≠ 0`). Coordinatewise addition is not the ring structure, as it does
not in general preserve compatible systems; when `p = 0` in `B` the two additions agree.

The type synonym `TauCeti.Perfectoid.uniformTilt p B` carries the ring structure, so that it does
not clash with Mathlib's coordinatewise ring structure on `Perfection B p` when `B` has
characteristic `p`.

## Implementation notes

The usual proof of convergence estimates with a power-multiplicative norm. Here the estimates
are made inside the ring, with the power-bounded subring `B°` playing the closed unit ball. For
`c ∈ B°` and `N : ℕ` let `W(c, N) = {z | c * z ^ p ^ N ∈ B°}` (for a power-multiplicative norm,
these are the `z` with `|z| ≤ |c|⁻¹ ^ (1 / p ^ N)`). Since `B°` is integrally closed in `B`, a
product `z₁ ^ a * z₂ ^ b` of elements of `W(c, N)` with `a + b ≤ p ^ N` satisfies
`c * z₁ ^ a * z₂ ^ b ∈ B°`; hence `W(c, N)` is an additive subgroup and degree-`p` monomials in
`W(c, N + 1)` lie in `W(c, N)`. With the binomial theorem this gives, for `β, δ ∈ W(c, N + n)`
and `k ≥ 1`, `(β + p ^ k * δ) ^ p ^ n - β ^ p ^ n ∈ p ^ (k + n) • W(c, N)`.
Every coordinate `x⁽ⁿ⁾` of an element of `B♭` lies in `W(c, n)` once `c` is a power of a
pseudouniformiser with `c * x⁽⁰⁾ ∈ B°`, and `W(c, 0) = c⁻¹ B°` is bounded because `B` is uniform.
So the defining sequence has consecutive differences in `p ^ (m + 1) • c⁻¹ B°`, which tend to zero
because `p` is topologically nilpotent, and its limit is congruent to `x⁽ⁱ⁾ + y⁽ⁱ⁾` modulo
`p • W(c, i)`. The ring axioms follow from this congruence: two sequences congruent modulo `p` in
this sense have the same limit.

## Main definitions

* `TauCeti.Perfectoid.uniformTilt p B`: the tilt `B♭`, a type synonym for `Perfection B p`.
* `TauCeti.Perfectoid.uniformTilt.commRing`: its commutative ring structure (the instance
  `uniformTilt.instCommRing`), with the multiplication of `Perfection B p` and the limit addition.
* `TauCeti.Perfectoid.uniformTilt.coeff n : uniformTilt p B →* B`: the `n`-th coordinate.

## Main results

* `TauCeti.Perfectoid.uniformTilt.coeff_add`: the limit formula for the coordinates of a sum.
* `TauCeti.Perfectoid.uniformTilt.coeff_add_sub_mem`: for `x, y` with power-bounded zeroth
  coordinates, `(x + y)⁽ⁱ⁾ - x⁽ⁱ⁾ - y⁽ⁱ⁾ ∈ p • B°`.
* `TauCeti.Perfectoid.uniformTilt.coeff_add_of_charP`: in characteristic `p` the addition is
  coordinatewise.
* `TauCeti.Perfectoid.uniformTilt.perfectRing` and `TauCeti.Perfectoid.uniformTilt.charP`: the tilt
  is perfect, and of characteristic `p` when `B` is nonzero.

## References

* K. S. Kedlaya, *Nonarchimedean geometry of Witt vectors and the tilting equivalence*, in
  *Perfectoid Spaces: Lectures from the 2017 Arizona Winter School*, Lemma 2.7.1(a).
* P. Scholze, *Étale cohomology of diamonds*, Definition 3.9 and Lemma 3.10.
* P. Scholze, *Perfectoid spaces*, Lemma 3.4 and Proposition 5.17.
-/

public section

open Filter Topology Pointwise TauCeti.Huber

namespace TauCeti.Perfectoid

variable (p : ℕ) (B : Type*) [CommRing B]

/-- The *tilt* `B♭ = lim_{x ↦ x ^ p} B` of a complete uniform Tate ring `B` in which `p` is
topologically nilpotent: Mathlib's monoid `Perfection B p` of compatible systems of `p`-th roots,
renamed to carry the ring structure with the limit addition (`uniformTilt.instCommRing`). -/
@[expose] def uniformTilt : Type _ := Perfection B p

variable {p B}

section Bound

variable [hp : Fact p.Prime] [TopologicalSpace B] [NonarchimedeanAddGroup B]
  [SeparatelyContinuousMul B]

variable (p) in
/-- For `c ∈ B°`, the additive subgroup `W(c, N)` of elements `z` with `c * z ^ p ^ N ∈ B°`. -/
private def boundSubgroup (c : powerBoundedSubring B) (N : ℕ) : AddSubgroup B where
  carrier := {z | (c : B) * z ^ p ^ N ∈ powerBoundedSubring B}
  zero_mem' := by
    simp [zero_pow (pow_ne_zero N hp.out.ne_zero), isPowerBounded_zero]
  add_mem' {S T} hS hT := by
    simp only [Set.mem_ofPred_eq] at hS hT ⊢
    rw [add_pow, Finset.mul_sum]
    refine (powerBoundedSubring B).sum_mem fun m hm ↦ ?_
    rw [← mul_assoc]
    exact mul_mem (mul_pow_mul_pow_mem_powerBoundedSubring
      (by have := Finset.mem_range.mp hm; omega) c.2 hS hT) (natCast_mem _ _)
  neg_mem' {S} hS := by
    simp only [Set.mem_ofPred_eq] at hS ⊢
    rw [neg_pow, mul_left_comm]
    exact mul_mem (pow_mem (neg_mem (one_mem _)) _) hS

variable (p) in
/-- The additive subgroup `p ^ k • W(c, N)`. -/
private def scaledSubgroup (c : powerBoundedSubring B) (N k : ℕ) : AddSubgroup B :=
  (boundSubgroup p c N).map (AddMonoidHom.mulLeft ((p : B) ^ k))

variable {c : powerBoundedSubring B}

private theorem mem_boundSubgroup {N : ℕ} {z : B} :
    z ∈ boundSubgroup p c N ↔ (c : B) * z ^ p ^ N ∈ powerBoundedSubring B := Iff.rfl

private theorem mem_scaledSubgroup {N k : ℕ} {z : B} :
    z ∈ scaledSubgroup p c N k ↔ ∃ δ ∈ boundSubgroup p c N, (p : B) ^ k * δ = z := by
  simp [scaledSubgroup]

private theorem mem_boundSubgroup_one {N : ℕ} {z : B} :
    z ∈ boundSubgroup p (1 : powerBoundedSubring B) N ↔ z ^ p ^ N ∈ powerBoundedSubring B := by
  rw [mem_boundSubgroup, OneMemClass.coe_one, one_mul]

/-- `W(c, N)` is a module over `B°`. -/
private theorem mul_mem_boundSubgroup {N : ℕ} {a z : B} (ha : a ∈ powerBoundedSubring B)
    (hz : z ∈ boundSubgroup p c N) : a * z ∈ boundSubgroup p c N := by
  rw [mem_boundSubgroup, mul_pow, mul_left_comm]
  exact mul_mem (pow_mem ha _) hz

/-- `z ^ p ^ n` lies in `W(c, M)` exactly when `z` lies in `W(c, M + n)`. -/
private theorem pow_mem_boundSubgroup_iff {M n : ℕ} {z : B} :
    z ^ p ^ n ∈ boundSubgroup p c M ↔ z ∈ boundSubgroup p c (M + n) := by
  rw [mem_boundSubgroup, mem_boundSubgroup, ← pow_mul, ← pow_add, add_comm n]

/-- The subgroups `W(c, N)` decrease with `N`. -/
private theorem boundSubgroup_succ_le (N : ℕ) :
    boundSubgroup p c (N + 1) ≤ boundSubgroup p c N := by
  intro z hz
  rw [mem_boundSubgroup] at hz ⊢
  obtain ⟨q, hq⟩ : ∃ q, p = q + 1 := ⟨p - 1, by have := hp.out.two_le; omega⟩
  refine mem_powerBoundedSubring.mpr <| IsPowerBounded.of_pow hp.out.ne_zero <|
    mem_powerBoundedSubring.mp ?_
  have h : ((c : B) * z ^ p ^ N) ^ p = (c : B) ^ q * ((c : B) * z ^ p ^ (N + 1)) := by
    rw [pow_succ, hq]; ring
  rw [h]
  exact mul_mem (pow_mem c.2 q) hz

private theorem antitone_boundSubgroup : Antitone (boundSubgroup p c) :=
  antitone_nat_of_succ_le boundSubgroup_succ_le

/-- Monomials of degree `p` in two elements of `W(c, N + 1)` lie in `W(c, N)`. -/
private theorem pow_mul_pow_mem_boundSubgroup {N j l : ℕ} {S T : B} (hjl : j + l = p)
    (hS : S ∈ boundSubgroup p c (N + 1)) (hT : T ∈ boundSubgroup p c (N + 1)) :
    S ^ j * T ^ l ∈ boundSubgroup p c N := by
  rw [mem_boundSubgroup, mul_pow, ← pow_mul, ← pow_mul]
  exact mul_pow_mul_pow_mem_powerBoundedSubring
    (by rw [← add_mul, hjl, pow_succ, mul_comm]) c.2 hS hT

/-- A multiple `p ^ e * z` of `z ∈ W(c, N)` lies in `p ^ k • W(c, N)` for `k ≤ e`. -/
private theorem pow_mul_mem_scaledSubgroup {N k e : ℕ} (hke : k ≤ e) {z : B}
    (hz : z ∈ boundSubgroup p c N) : (p : B) ^ e * z ∈ scaledSubgroup p c N k := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hke
  refine mem_scaledSubgroup.mpr ⟨(p : B) ^ r * z,
    mul_mem_boundSubgroup (pow_mem (natCast_mem _ p) r) hz, ?_⟩
  ring

/-- **The binomial step for sums**: for `S, T ∈ W(c, N + 1)`,
`(S + T) ^ p - S ^ p - T ^ p ∈ p • W(c, N)`. -/
private theorem add_pow_sub_pow_sub_pow_mem {N : ℕ} {S T : B}
    (hS : S ∈ boundSubgroup p c (N + 1)) (hT : T ∈ boundSubgroup p c (N + 1)) :
    (S + T) ^ p - S ^ p - T ^ p ∈ scaledSubgroup p c N 1 := by
  rw [add_pow_prime_eq' hp.out, show ∀ a b d : B, a + b + d - a - b = d from fun _ _ _ ↦ by ring,
    Finset.mul_sum]
  refine AddSubgroup.sum_mem _ fun j hj ↦ ?_
  have hj := Finset.mem_Ioo.mp hj
  rw [← pow_one (p : B), mul_comm (S ^ j * T ^ (p - j))]
  exact pow_mul_mem_scaledSubgroup le_rfl (mul_mem_boundSubgroup (natCast_mem _ _)
    (pow_mul_pow_mem_boundSubgroup (by omega) hS hT))

/-- **The binomial step for a `p`-adically small perturbation**: for `S, T ∈ W(c, N + 1)` and
`k ≥ 1`, `(S + p ^ k * T) ^ p - S ^ p ∈ p ^ (k + 1) • W(c, N)`. -/
private theorem add_pow_mul_pow_sub_pow_mem {N k : ℕ} (hk : k ≠ 0) {S T : B}
    (hS : S ∈ boundSubgroup p c (N + 1)) (hT : T ∈ boundSubgroup p c (N + 1)) :
    (S + (p : B) ^ k * T) ^ p - S ^ p ∈ scaledSubgroup p c N (k + 1) := by
  have hp2 := hp.out.two_le
  rw [add_pow_prime_eq' hp.out, add_assoc, add_sub_cancel_left, Finset.mul_sum]
  refine add_mem ?_ (AddSubgroup.sum_mem _ fun j hj ↦ ?_)
  · rw [mul_pow, ← pow_mul]
    refine pow_mul_mem_scaledSubgroup
      (le_trans (by omega : k + 1 ≤ k * 2) (Nat.mul_le_mul_left k hp2)) ?_
    have h := (pow_mem_boundSubgroup_iff (c := c) (M := N) (n := 1)).mpr hT
    rwa [pow_one] at h
  · have hj := Finset.mem_Ioo.mp hj
    have h : (p : B) * (S ^ j * ((p : B) ^ k * T) ^ (p - j) * ((p.choose j / p : ℕ) : B)) =
        (p : B) ^ (1 + k * (p - j)) * (((p.choose j / p : ℕ) : B) * (S ^ j * T ^ (p - j))) := by
      rw [mul_pow, ← pow_mul, pow_add]; ring
    rw [h]
    exact pow_mul_mem_scaledSubgroup
      (by have := Nat.le_mul_of_pos_right k (Nat.sub_pos_of_lt hj.2); omega)
      (mul_mem_boundSubgroup (natCast_mem _ _) (pow_mul_pow_mem_boundSubgroup (by omega) hS hT))

/-- The binomial step for negation: for `S ∈ W(c, N + 1)`, `(-S) ^ p + S ^ p ∈ p • W(c, N)`.
It vanishes for odd `p`, and is `2 * S ^ 2` for `p = 2`. -/
private theorem neg_pow_add_pow_mem {N : ℕ} {S : B} (hS : S ∈ boundSubgroup p c (N + 1)) :
    (-S) ^ p + S ^ p ∈ scaledSubgroup p c N 1 := by
  rcases hp.out.eq_two_or_odd' with h | h
  · have h' : (-S) ^ p + S ^ p = (p : B) ^ 1 * S ^ p := by
      rw [(show Even p by rw [h]; exact even_two).neg_pow, pow_one, ← two_mul, h, Nat.cast_ofNat]
    rw [h']
    refine pow_mul_mem_scaledSubgroup le_rfl ?_
    have h'' := (pow_mem_boundSubgroup_iff (c := c) (M := N) (n := 1)).mpr hS
    rwa [pow_one] at h''
  · rw [h.neg_pow, neg_add_cancel]
    exact zero_mem _

/-- **Iterated binomial step**: for `β, δ ∈ W(c, N + n)` and `k ≥ 1`,
`(β + p ^ k * δ) ^ p ^ n - β ^ p ^ n ∈ p ^ (k + n) • W(c, N)`. -/
private theorem add_pow_mul_pow_pow_sub_pow_pow_mem {k : ℕ} (hk : k ≠ 0) :
    ∀ (n N : ℕ) {β δ : B}, β ∈ boundSubgroup p c (N + n) → δ ∈ boundSubgroup p c (N + n) →
      (β + (p : B) ^ k * δ) ^ p ^ n - β ^ p ^ n ∈ scaledSubgroup p c N (k + n)
  | 0, N, β, δ, _, hδ => by
    simpa using mem_scaledSubgroup.mpr ⟨δ, hδ, rfl⟩
  | n + 1, N, β, δ, hβ, hδ => by
    rw [show N + (n + 1) = N + 1 + n by omega] at hβ hδ
    obtain ⟨δ', hδ', he⟩ :=
      mem_scaledSubgroup.mp (add_pow_mul_pow_pow_sub_pow_pow_mem hk n (N + 1) hβ hδ)
    have he' : (β + (p : B) ^ k * δ) ^ p ^ n = β ^ p ^ n + (p : B) ^ (k + n) * δ' := by
      rw [he]; ring
    rw [pow_succ, pow_mul, pow_mul, he', ← add_assoc k]
    exact add_pow_mul_pow_sub_pow_mem (by omega) (pow_mem_boundSubgroup_iff.mpr hβ) hδ'

variable (p c) in
/-- A sequence `σ` is *quasi-compatible* for the bound `c` when `σ N ∈ W(c, N)` and
`σ (N + 1) ^ p ≡ σ N` modulo `p • W(c, N)`. Coordinate sequences of elements of the tilt are
compatible, and sums of quasi-compatible sequences are quasi-compatible. -/
private def IsQuasiCompatible (σ : ℕ → B) : Prop :=
  ∀ N, σ N ∈ boundSubgroup p c N ∧ σ (N + 1) ^ p - σ N ∈ scaledSubgroup p c N 1

private theorem IsQuasiCompatible.add {σ τ : ℕ → B} (hσ : IsQuasiCompatible p c σ)
    (hτ : IsQuasiCompatible p c τ) : IsQuasiCompatible p c (σ + τ) := fun N ↦ by
  refine ⟨add_mem (hσ N).1 (hτ N).1, ?_⟩
  have h : (σ + τ) (N + 1) ^ p - (σ + τ) N = ((σ (N + 1) + τ (N + 1)) ^ p - σ (N + 1) ^ p -
      τ (N + 1) ^ p) + (σ (N + 1) ^ p - σ N) + (τ (N + 1) ^ p - τ N) := by
    simp only [Pi.add_apply]; ring
  rw [h]
  exact add_mem (add_mem (add_pow_sub_pow_sub_pow_mem (hσ (N + 1)).1 (hτ (N + 1)).1) (hσ N).2)
    (hτ N).2

private theorem IsQuasiCompatible.neg {σ : ℕ → B} (hσ : IsQuasiCompatible p c σ) :
    IsQuasiCompatible p c (-σ) := fun N ↦ by
  refine ⟨neg_mem (hσ N).1, ?_⟩
  have h : (-σ) (N + 1) ^ p - (-σ) N =
      ((-σ (N + 1)) ^ p + σ (N + 1) ^ p) - (σ (N + 1) ^ p - σ N) := by
    simp only [Pi.neg_apply]; ring
  rw [h]
  exact sub_mem (neg_pow_add_pow_mem (hσ (N + 1)).1) (hσ N).2

/-- A compatible sequence whose zeroth term is moved into `B°` by `c` is quasi-compatible. -/
private theorem isQuasiCompatible_of_pow {σ : ℕ → B} (hσ : ∀ N, σ (N + 1) ^ p = σ N)
    (h0 : (c : B) * σ 0 ∈ powerBoundedSubring B) : IsQuasiCompatible p c σ := by
  have hpow : ∀ N, σ N ^ p ^ N = σ 0 := fun N ↦ by
    induction N with
    | zero => simp
    | succ N ih => rw [pow_succ', pow_mul, hσ, ih]
  exact fun N ↦ ⟨by rw [mem_boundSubgroup, hpow]; exact h0, by rw [hσ, sub_self]; exact zero_mem _⟩

/-- The coordinate sequence of an element of the tilt is quasi-compatible for any bound moving its
zeroth coordinate into `B°`. -/
private theorem isQuasiCompatible_val (x : Perfection B p)
    (hx : (c : B) * x.1 0 ∈ powerBoundedSubring B) : IsQuasiCompatible p c x.1 :=
  isQuasiCompatible_of_pow x.2 hx

end Bound

section TiltLim

variable [TopologicalSpace B]

variable (p) in
/-- The limit `lim_{m → ∞} σ (i + m) ^ p ^ m` defining the coordinates of the tilt. -/
private noncomputable def tiltLim (σ : ℕ → B) (i : ℕ) : B :=
  limUnder atTop fun m ↦ σ (i + m) ^ p ^ m

/-- The limit of a compatible sequence is the sequence itself. -/
private theorem tiltLim_of_pow [T2Space B] {σ : ℕ → B} (hσ : ∀ N, σ (N + 1) ^ p = σ N) :
    tiltLim p σ = σ := by
  funext i
  have h : ∀ m, σ (i + m) ^ p ^ m = σ i := fun m ↦ by
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ', pow_mul, ← add_assoc, hσ, ih]
  simp only [tiltLim, h]
  exact tendsto_const_nhds.limUnder_eq

end TiltLim

section Huber

variable [hp : Fact p.Prime] [TopologicalSpace B] [IsTopologicalRing B] [IsHuberRing B]
  {c : powerBoundedSubring B}

private theorem isClosed_boundSubgroup (N : ℕ) : IsClosed (boundSubgroup p c N : Set B) :=
  ((powerBoundedSubring B).toAddSubgroup.isClosed_of_isOpen
    (isOpen_powerBoundedSubring B)).preimage (continuous_const.mul (continuous_pow _))

/-- For a unit `c ∈ B°` and `γ m ∈ W(c, 0)`, the multiples `p ^ m * γ m` tend to zero: `W(c, 0)`
is contained in the bounded set `c⁻¹ B°` and `p` is topologically nilpotent. -/
private theorem tendsto_pow_mul [IsUniform B] [hpn : Fact (IsTopologicallyNilpotent (p : B))]
    (hc : IsUnit (c : B)) {γ : ℕ → B}
    (hγ : ∀ m, γ m ∈ boundSubgroup p c 0) :
    Tendsto (fun m ↦ (p : B) ^ m * γ m) atTop (𝓝 0) := by
  refine (((isBounded_singleton ((hc.unit⁻¹ : Bˣ) : B)).mul
    IsUniform.isBounded_powerBoundedSubring)).tendsto_mul hpn.out (Eventually.of_forall fun m ↦ ?_)
  have h := hγ m
  rw [mem_boundSubgroup, pow_zero, pow_one] at h
  exact Set.mem_mul.mpr ⟨_, rfl, _, h, hc.unit.inv_mul_cancel_left (γ m)⟩

end Huber

section Limit

variable [hp : Fact p.Prime] [UniformSpace B] [IsUniformAddGroup B] [IsTopologicalRing B]
  [IsHuberRing B] [CompleteSpace B] [T2Space B] [IsUniform B]
  [hpn : Fact (IsTopologicallyNilpotent (p : B))] {c : powerBoundedSubring B}

omit [T2Space B] in
/-- **The defining limit exists**: for a quasi-compatible `σ`, the sequence `σ (i + m) ^ p ^ m`
converges, to `σ i + p * G` for some `G ∈ W(c, i)`. -/
private theorem exists_tendsto (hc : IsUnit (c : B)) {σ : ℕ → B}
    (hσ : IsQuasiCompatible p c σ) (i : ℕ) : ∃ G ∈ boundSubgroup p c i,
      Tendsto (fun m ↦ σ (i + m) ^ p ^ m) atTop (𝓝 (σ i + p * G)) := by
  -- consecutive differences lie in `p ^ (m + 1) • W(c, i)`
  have hd : ∀ m, σ (i + (m + 1)) ^ p ^ (m + 1) - σ (i + m) ^ p ^ m ∈
      scaledSubgroup p c i (1 + m) := fun m ↦ by
    obtain ⟨δ, hδ, he⟩ := mem_scaledSubgroup.mp (hσ (i + m)).2
    have h := add_pow_mul_pow_pow_sub_pow_pow_mem one_ne_zero m i (hσ (i + m)).1 hδ
    rw [he, add_sub_cancel, ← pow_mul, ← pow_succ'] at h
    rwa [← add_assoc]
  choose γ hγ hγe using fun m ↦ mem_scaledSubgroup.mp (hd m)
  set f : ℕ → B := fun m ↦ (p : B) ^ m * γ m with hf_def
  have hf : ∀ m, f m ∈ boundSubgroup p c i := fun m ↦
    mul_mem_boundSubgroup (pow_mem (natCast_mem _ p) m) (hγ m)
  have hfs : Summable f := NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero <| by
    rw [Nat.cofinite_eq_atTop]
    exact tendsto_pow_mul hc fun m ↦ antitone_boundSubgroup (Nat.zero_le i) (hγ m)
  refine ⟨∑' m, f m, (isClosed_boundSubgroup i).mem_of_tendsto hfs.hasSum.tendsto_sum_nat
    (Eventually.of_forall fun n ↦ AddSubgroup.sum_mem _ fun m _ ↦ hf m), ?_⟩
  -- telescoping: `σ (i + m) ^ p ^ m = σ i + p * ∑_{j < m} f j`
  have htel : ∀ m, σ (i + m) ^ p ^ m = σ i + p * ∑ j ∈ Finset.range m, f j := fun m ↦ by
    induction m with
    | zero => simp
    | succ m ih =>
      have h := hγe m
      rw [Finset.sum_range_succ]
      simp only [hf_def] at h ⊢
      linear_combination (-1 : B) * h + ih
  simp_rw [htel]
  exact tendsto_const_nhds.add (hfs.hasSum.tendsto_sum_nat.const_mul _)

omit [T2Space B] in
private theorem tendsto_tiltLim (hc : IsUnit (c : B)) {σ : ℕ → B}
    (hσ : IsQuasiCompatible p c σ) (i : ℕ) :
    Tendsto (fun m ↦ σ (i + m) ^ p ^ m) atTop (𝓝 (tiltLim p σ i)) :=
  have ⟨_, _, h⟩ := exists_tendsto hc hσ i
  tendsto_nhds_limUnder ⟨_, h⟩

/-- The limit is congruent to `σ i` modulo `p • W(c, i)`. -/
private theorem tiltLim_sub_mem (hc : IsUnit (c : B)) {σ : ℕ → B}
    (hσ : IsQuasiCompatible p c σ) (i : ℕ) :
    tiltLim p σ i - σ i ∈ scaledSubgroup p c i 1 := by
  obtain ⟨G, hG, h⟩ := exists_tendsto hc hσ i
  rw [tendsto_nhds_unique (tendsto_tiltLim hc hσ i) h, add_sub_cancel_left]
  exact mem_scaledSubgroup.mpr ⟨G, hG, by rw [pow_one]⟩

private theorem tiltLim_succ_pow (hc : IsUnit (c : B)) {σ : ℕ → B}
    (hσ : IsQuasiCompatible p c σ) (i : ℕ) : tiltLim p σ (i + 1) ^ p = tiltLim p σ i := by
  refine tendsto_nhds_unique (((tendsto_tiltLim hc hσ (i + 1)).pow p).congr fun m ↦ ?_)
    ((tendsto_add_atTop_iff_nat 1).mpr (tendsto_tiltLim hc hσ i))
  rw [← pow_mul, ← pow_succ, show i + 1 + m = i + (m + 1) by omega]

/-- The limits form a quasi-compatible (indeed compatible) sequence for the same bound. -/
private theorem isQuasiCompatible_tiltLim (hc : IsUnit (c : B)) {σ : ℕ → B}
    (hσ : IsQuasiCompatible p c σ) : IsQuasiCompatible p c (tiltLim p σ) := fun N ↦ by
  refine ⟨?_, by rw [tiltLim_succ_pow hc hσ, sub_self]; exact zero_mem _⟩
  obtain ⟨G, hG, he⟩ := mem_scaledSubgroup.mp (tiltLim_sub_mem hc hσ N)
  rw [← sub_add_cancel (tiltLim p σ N) (σ N), ← he]
  exact add_mem (mul_mem_boundSubgroup (pow_mem (natCast_mem _ p) 1) hG) (hσ N).1

/-- **Sequences congruent modulo `p` have the same limit.** -/
private theorem tiltLim_congr (hc : IsUnit (c : B)) {σ τ : ℕ → B}
    (hσ : IsQuasiCompatible p c σ) (hτ : IsQuasiCompatible p c τ)
    (h : ∀ N, σ N - τ N ∈ scaledSubgroup p c N 1) : tiltLim p σ = tiltLim p τ := by
  funext i
  have hd : ∀ m, σ (i + m) ^ p ^ m - τ (i + m) ^ p ^ m ∈ scaledSubgroup p c i (1 + m) :=
    fun m ↦ by
      obtain ⟨δ, hδ, he⟩ := mem_scaledSubgroup.mp (h (i + m))
      have := add_pow_mul_pow_pow_sub_pow_pow_mem one_ne_zero m i (hτ (i + m)).1 hδ
      rwa [he, add_sub_cancel] at this
  choose γ hγ hγe using fun m ↦ mem_scaledSubgroup.mp (hd m)
  have h0 : Tendsto (fun m ↦ σ (i + m) ^ p ^ m - τ (i + m) ^ p ^ m) atTop (𝓝 0) := by
    have := (tendsto_pow_mul hc fun m ↦ antitone_boundSubgroup (Nat.zero_le i) (hγ m)).const_mul
      (p : B)
    rw [mul_zero] at this
    refine this.congr fun m ↦ ?_
    rw [← hγe, ← mul_assoc, ← pow_succ', add_comm]
  exact sub_eq_zero.mp (tendsto_nhds_unique
    ((tendsto_tiltLim hc hσ i).sub (tendsto_tiltLim hc hτ i)) h0)

end Limit

namespace uniformTilt

private theorem val_mul (x y : Perfection B p) : (x * y).1 = x.1 * y.1 := rfl

private theorem val_pow (x : Perfection B p) (i m : ℕ) : x.1 (i + m) ^ p ^ m = x.1 i :=
  Perfection.coeffMonoidHom_pow_p_pow' x i m

section Zero

variable [hp : Fact p.Prime]

/-- The zero of the tilt, with all coordinates zero. -/
private def zero' : Perfection B p :=
  ⟨0, fun _ ↦ by simp [hp.out.ne_zero]⟩

private theorem val_zero' : (zero' : Perfection B p).1 = 0 := rfl

private theorem zero'_mul (x : Perfection B p) : zero' * x = zero' :=
  Subtype.ext <| funext fun _ ↦ zero_mul _

private theorem mul_zero' (x : Perfection B p) : x * zero' = zero' :=
  Subtype.ext <| funext fun _ ↦ mul_zero _

end Zero

variable [hp : Fact p.Prime] [UniformSpace B] [IsUniformAddGroup B] [IsTopologicalRing B]
  [IsTateRing B] [CompleteSpace B] [T2Space B] [IsUniform B]
  [hpn : Fact (IsTopologicallyNilpotent (p : B))]

/-- The limit addition `(x + y)⁽ⁱ⁾ = lim_m (x⁽ⁱ⁺ᵐ⁾ + y⁽ⁱ⁺ᵐ⁾) ^ p ^ m`. -/
private noncomputable def add' (x y : Perfection B p) : Perfection B p :=
  ⟨tiltLim p (x.1 + y.1), fun i ↦ by
    obtain ⟨c, hc, h⟩ := IsTateRing.exists_isUnit_mul_mem_powerBoundedSubring
      (Set.toFinite {x.1 0, y.1 0})
    exact tiltLim_succ_pow hc ((isQuasiCompatible_val x (h _ (by simp))).add
      (isQuasiCompatible_val y (h _ (by simp)))) i⟩

/-- The negation `(-x)⁽ⁱ⁾ = lim_m (-x⁽ⁱ⁺ᵐ⁾) ^ p ^ m`: coordinatewise for odd `p`, and the identity
for `p = 2`. -/
private noncomputable def neg' (x : Perfection B p) : Perfection B p :=
  ⟨tiltLim p (-x.1), fun i ↦ by
    obtain ⟨c, hc, h⟩ := IsTateRing.exists_isUnit_mul_mem_powerBoundedSubring
      (Set.toFinite {x.1 0})
    exact tiltLim_succ_pow hc (isQuasiCompatible_val x (h _ (by simp))).neg i⟩

private theorem val_add' (x y : Perfection B p) : (add' x y).1 = tiltLim p (x.1 + y.1) := rfl

private theorem val_neg' (x : Perfection B p) : (neg' x).1 = tiltLim p (-x.1) := rfl

private theorem add'_comm (x y : Perfection B p) : add' x y = add' y x :=
  Subtype.ext <| by rw [val_add', val_add', add_comm]

private theorem add'_zero (x : Perfection B p) : add' x zero' = x :=
  Subtype.ext <| by rw [val_add', val_zero', add_zero, tiltLim_of_pow x.2]

private theorem add'_assoc (x y z : Perfection B p) :
    add' (add' x y) z = add' x (add' y z) := by
  obtain ⟨c, hc, h⟩ := IsTateRing.exists_isUnit_mul_mem_powerBoundedSubring
    (Set.toFinite {x.1 0, y.1 0, z.1 0})
  have hx := isQuasiCompatible_val x (h _ (by simp))
  have hy := isQuasiCompatible_val y (h _ (by simp))
  have hz := isQuasiCompatible_val z (h _ (by simp))
  -- both sides are the limit of `x⁽ⁿ⁾ + y⁽ⁿ⁾ + z⁽ⁿ⁾`
  have key : ∀ {σ τ : ℕ → B}, IsQuasiCompatible p c σ → IsQuasiCompatible p c τ →
      tiltLim p (tiltLim p σ + τ) = tiltLim p (σ + τ) := fun hσ hτ ↦
    tiltLim_congr hc ((isQuasiCompatible_tiltLim hc hσ).add hτ) (hσ.add hτ) fun N ↦ by
      simpa using tiltLim_sub_mem hc hσ N
  refine Subtype.ext ?_
  simp only [val_add']
  rw [key (hx.add hy) hz, add_comm x.1 (tiltLim p (y.1 + z.1)), key (hy.add hz) hx]
  congr 1
  abel

private theorem neg'_add' (x : Perfection B p) : add' (neg' x) x = zero' := by
  obtain ⟨c, hc, h⟩ := IsTateRing.exists_isUnit_mul_mem_powerBoundedSubring
    (Set.toFinite {x.1 0})
  have hx := isQuasiCompatible_val x (h _ (by simp))
  refine Subtype.ext ?_
  rw [val_add', val_neg',
    tiltLim_congr hc ((isQuasiCompatible_tiltLim hc hx.neg).add hx) (hx.neg.add hx) fun N ↦ by
      simpa using tiltLim_sub_mem hc hx.neg N, neg_add_cancel,
    tiltLim_of_pow fun _ ↦ by simp [hp.out.ne_zero]]
  exact val_zero'.symm

private theorem mul_add' (x y z : Perfection B p) : x * add' y z = add' (x * y) (x * z) := by
  obtain ⟨c, hc, h⟩ := IsTateRing.exists_isUnit_mul_mem_powerBoundedSubring
    (Set.toFinite {y.1 0, z.1 0})
  have hyz := (isQuasiCompatible_val y (h _ (by simp))).add
    (isQuasiCompatible_val z (h _ (by simp)))
  refine Subtype.ext (funext fun i ↦ ?_)
  simp only [val_mul, val_add', Pi.mul_apply]
  -- the defining sequence of the right side is `x⁽ⁱ⁾` times that of `y + z`
  refine (((tendsto_tiltLim hc hyz i).const_mul (x.1 i)).congr fun m ↦ ?_).limUnder_eq.symm
  rw [Pi.add_apply, Pi.add_apply, Pi.mul_apply, Pi.mul_apply, ← mul_add, mul_pow, val_pow]

private theorem zero'_add' (x : Perfection B p) : add' zero' x = x := by
  rw [add'_comm]; exact add'_zero x

private theorem add'_mul (x y z : Perfection B p) : add' x y * z = add' (x * z) (y * z) := by
  rw [mul_comm, mul_add', mul_comm z x, mul_comm z y]

/-- The ring structure of the tilt, on the underlying type `Perfection B p`. It is not an instance
there, as it would clash with Mathlib's coordinatewise ring structure in characteristic `p`. -/
@[instance_reducible]
private noncomputable def commRingAux : CommRing (Perfection B p) :=
  { (inferInstance : CommMonoid (Perfection B p)) with
    add := add'
    zero := zero'
    neg := neg'
    add_assoc := add'_assoc
    zero_add := zero'_add'
    add_zero := add'_zero
    add_comm := add'_comm
    neg_add_cancel := neg'_add'
    nsmul := fun n x ↦ @nsmulRec _ ⟨zero'⟩ ⟨add'⟩ n x
    zsmul := fun n x ↦ @zsmulRec _ ⟨zero'⟩ ⟨add'⟩ ⟨neg'⟩ (fun n x ↦ @nsmulRec _ ⟨zero'⟩ ⟨add'⟩ n x)
      n x
    left_distrib := mul_add'
    right_distrib := add'_mul
    zero_mul := zero'_mul
    mul_zero := mul_zero' }

/-- **The tilt is a commutative ring** under the multiplication of `Perfection B p` and the limit
addition `(x + y)⁽ⁱ⁾ = lim_{m → ∞} (x⁽ⁱ⁺ᵐ⁾ + y⁽ⁱ⁺ᵐ⁾) ^ p ^ m` (Kedlaya, *Arizona Winter School
notes*, Lemma 2.7.1(a)); it is registered as the instance `uniformTilt.instCommRing`. Its addition
is characterised by `uniformTilt.coeff_add`. -/
@[instance_reducible]
protected noncomputable def commRing : CommRing (uniformTilt p B) :=
  commRingAux

/-- The tilt carries the ring structure `uniformTilt.commRing`. -/
noncomputable instance instCommRing : CommRing (uniformTilt p B) :=
  uniformTilt.commRing

variable (p B) in
/-- The `n`-th coordinate `x ↦ x⁽ⁿ⁾` of the tilt, a monoid homomorphism to `B`. -/
noncomputable def coeff (n : ℕ) : uniformTilt p B →* B :=
  Perfection.coeffMonoidHom B p n

private theorem coeff_apply (x : uniformTilt p B) (n : ℕ) :
    coeff p B n x = (x : Perfection B p).1 n := rfl

private theorem coeff_add_eq (x y : uniformTilt p B) (n : ℕ) :
    coeff p B n (x + y) = tiltLim p ((x : Perfection B p).1 + (y : Perfection B p).1) n := rfl

/-- Elements of the tilt with the same coordinates are equal. -/
@[ext]
theorem ext {x y : uniformTilt p B} (h : ∀ n, coeff p B n x = coeff p B n y) : x = y :=
  Perfection.extMonoid h

/-- The coordinates form a compatible system of `p`-th roots. -/
@[simp]
theorem coeff_pow_p (x : uniformTilt p B) (n : ℕ) : coeff p B (n + 1) x ^ p = coeff p B n x :=
  Perfection.coeffMonoidHom_pow_p' x n

/-- Iterating `coeff_pow_p`: `(x⁽ⁿ⁺ᵐ⁾) ^ p ^ m = x⁽ⁿ⁾`. -/
@[simp]
theorem coeff_pow_p_pow (x : uniformTilt p B) (n m : ℕ) :
    coeff p B (n + m) x ^ p ^ m = coeff p B n x :=
  Perfection.coeffMonoidHom_pow_p_pow' x n m

/-- The coordinates of zero are zero. -/
@[simp]
theorem coeff_zero (n : ℕ) : coeff p B n 0 = 0 := (rfl)

/-- **The limit formula for the addition**:
`(x + y)⁽ⁱ⁾ = lim_{m → ∞} (x⁽ⁱ⁺ᵐ⁾ + y⁽ⁱ⁺ᵐ⁾) ^ p ^ m`. -/
theorem coeff_add (x y : uniformTilt p B) (i : ℕ) :
    Tendsto (fun m ↦ (coeff p B (i + m) x + coeff p B (i + m) y) ^ p ^ m) atTop
      (𝓝 (coeff p B i (x + y))) := by
  obtain ⟨c, hc, h⟩ := IsTateRing.exists_isUnit_mul_mem_powerBoundedSubring
    (s := {(x : Perfection B p).1 0, (y : Perfection B p).1 0}) (Set.toFinite _)
  rw [coeff_add_eq]
  simp only [coeff_apply]
  exact tendsto_tiltLim hc ((isQuasiCompatible_val _ (h _ (by simp))).add
    (isQuasiCompatible_val _ (h _ (by simp)))) i

/-- **The coordinates are additive modulo `p`** on elements with power-bounded zeroth coordinate:
`(x + y)⁽ⁱ⁾ - x⁽ⁱ⁾ - y⁽ⁱ⁾ ∈ p • B°`. -/
theorem coeff_add_sub_mem {x y : uniformTilt p B} (hx : coeff p B 0 x ∈ powerBoundedSubring B)
    (hy : coeff p B 0 y ∈ powerBoundedSubring B) (i : ℕ) :
    coeff p B i (x + y) - coeff p B i x - coeff p B i y ∈
      (p : B) • (powerBoundedSubring B : Set B) := by
  rw [coeff_apply] at hx hy
  -- the bound `c = 1` works, and `W(1, i) ⊆ W(1, 0) = B°`
  have h1 := (isQuasiCompatible_val (c := 1) (x : Perfection B p)
    (by rwa [OneMemClass.coe_one, one_mul])).add
    (isQuasiCompatible_val (c := 1) (y : Perfection B p) (by rwa [OneMemClass.coe_one, one_mul]))
  obtain ⟨δ, hδ, he⟩ := mem_scaledSubgroup.mp (tiltLim_sub_mem isUnit_one h1 i)
  have hδ0 := antitone_boundSubgroup (Nat.zero_le i) hδ
  rw [mem_boundSubgroup_one, pow_zero, pow_one] at hδ0
  refine ⟨δ, hδ0, ?_⟩
  simp only [Pi.add_apply, pow_one] at he
  simp only [smul_eq_mul]
  rw [coeff_add_eq]
  simp only [coeff_apply]
  linear_combination he

/-- **In characteristic `p` the addition is coordinatewise.** -/
@[simp]
theorem coeff_add_of_charP [CharP B p] (x y : uniformTilt p B) (n : ℕ) :
    coeff p B n (x + y) = coeff p B n x + coeff p B n y := by
  refine tendsto_nhds_unique (coeff_add x y n) (tendsto_const_nhds.congr fun m ↦ ?_)
  rw [add_pow_char_pow, coeff_pow_p_pow, coeff_pow_p_pow]

/-- **The tilt is perfect**: `x ↦ x ^ p` is bijective, with inverse shifting the coordinates. -/
instance perfectRing : PerfectRing (uniformTilt p B) p :=
  inferInstanceAs (PerfectRing (Perfection B p) p)

/-- The tilt of a nonzero ring is nonzero. -/
instance nontrivial [Nontrivial B] : Nontrivial (uniformTilt p B) :=
  ⟨⟨0, 1, fun h ↦ zero_ne_one (congrArg (coeff p B 0) h)⟩⟩

/-- The coordinates of the natural number `n` in the tilt are congruent to `n` modulo `p • B°`. -/
private theorem coeff_natCast_sub_mem (n N : ℕ) :
    coeff p B N (n : uniformTilt p B) - n ∈ scaledSubgroup p (1 : powerBoundedSubring B) N 1 := by
  induction n generalizing N with
  | zero =>
    rw [Nat.cast_zero, Nat.cast_zero, coeff_zero, sub_zero]
    exact zero_mem _
  | succ n ih =>
    -- the zeroth coordinate of `n` is power-bounded, so `1` bounds both summands of `n + 1`
    have hn0 : coeff p B 0 (n : uniformTilt p B) ∈ powerBoundedSubring B := by
      obtain ⟨δ, hδ, he⟩ := mem_scaledSubgroup.mp (ih 0)
      rw [mem_boundSubgroup_one, pow_zero, pow_one] at hδ
      rw [← sub_add_cancel (coeff p B 0 (n : uniformTilt p B)) n, ← he]
      exact add_mem (mul_mem (pow_mem (natCast_mem _ _) _) hδ) (natCast_mem _ _)
    set σ : ℕ → B := fun k ↦ coeff p B k (n : uniformTilt p B) + 1 with hσ_def
    have hσ : IsQuasiCompatible p (1 : powerBoundedSubring B) σ :=
      (isQuasiCompatible_val (c := 1) _ (by rw [OneMemClass.coe_one, one_mul]; exact hn0)).add
        (isQuasiCompatible_val (c := 1) (1 : uniformTilt p B)
          (by rw [OneMemClass.coe_one, one_mul]; exact one_mem _))
    -- `σ` is the coordinatewise sum of the coordinate sequences of `n` and `1`
    have hadd : coeff p B N ((n : uniformTilt p B) + 1) = tiltLim p σ N := coeff_add_eq _ _ N
    have h := add_mem (tiltLim_sub_mem isUnit_one hσ N) (ih N)
    rw [Nat.cast_succ, Nat.cast_succ, hadd]
    convert h using 1
    rw [hσ_def]
    ring

/-- **The tilt of a nonzero ring has characteristic `p`.** -/
instance charP [Nontrivial B] : CharP (uniformTilt p B) p := by
  refine (CharP.charP_iff_prime_eq_zero hp.out).mpr (ext fun N ↦ ?_)
  rw [coeff_zero]
  -- the coordinates of `p` are the limits `lim_m p ^ p ^ m = 0` of the constant sequence `p`
  have hp0 : coeff p B 0 (p : uniformTilt p B) ∈ powerBoundedSubring B := by
    obtain ⟨δ, hδ, he⟩ := mem_scaledSubgroup.mp (coeff_natCast_sub_mem (p := p) (B := B) p 0)
    rw [mem_boundSubgroup_one, pow_zero, pow_one] at hδ
    rw [← sub_add_cancel (coeff p B 0 (p : uniformTilt p B)) p, ← he]
    exact add_mem (mul_mem (pow_mem (natCast_mem _ _) _) hδ) (natCast_mem _ _)
  have hσ := isQuasiCompatible_val (c := 1) (p : uniformTilt p B)
    (by rw [OneMemClass.coe_one, one_mul]; exact hp0)
  have hconst : IsQuasiCompatible p (1 : powerBoundedSubring B) fun _ ↦ (p : B) := fun M ↦ by
    obtain ⟨q, hq⟩ : ∃ q, p = q + 1 := ⟨p - 1, by have := hp.out.two_le; omega⟩
    refine ⟨mem_boundSubgroup_one.mpr (pow_mem (natCast_mem _ p) _),
      mem_scaledSubgroup.mpr ⟨(p : B) ^ q - 1, mem_boundSubgroup_one.mpr
        (pow_mem (sub_mem (pow_mem (natCast_mem _ p) q) (one_mem _)) _), ?_⟩⟩
    rw [pow_one, mul_sub, mul_one, ← pow_succ', ← hq]
  have h := congrFun (tiltLim_congr isUnit_one hσ hconst
    fun M ↦ coeff_natCast_sub_mem (p := p) (B := B) p M) N
  rw [tiltLim_of_pow (p : uniformTilt p B).2] at h
  rw [coeff_apply, h]
  exact tendsto_nhds_unique (tendsto_tiltLim isUnit_one hconst N)
    (hpn.out.comp (tendsto_atTop_mono (fun m ↦ (Nat.lt_pow_self hp.out.one_lt).le) tendsto_id))

end uniformTilt

end TauCeti.Perfectoid

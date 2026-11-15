/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.Obstruction.Invariance
public import TauCeti.RepresentationTheory.Quiver.Zigzag.AInfinity.WordPairing
import TauCeti.Data.List.ProdOfFn
import Mathlib.Tactic.LinearCombination

/-!
# Parity of trace pairings on formal deformations of zigzag algebras

Over a ring in which `2` or higher factorials are not invertible, the first obstruction `m_{n+2}`
of a minimal `A∞` algebra `𝒜` isomorphic to a graded algebra `ℋ` need not be a Hochschild
coboundary on the nose: normalizing an `A∞` isomorphism `f : 𝒜 ⟶ ℋ` to have linear part the
identity and writing `ψ = f.taylor - letter` decomposes `m_{n+2}` on every pure word into a
coboundary `δψ` plus the quadratic sum

```text
∑_{2 ≤ d ≤ n} m_ℋ(ψ(x₀, …, x_{d-1}), ψ(x_d, …, x_{n+1}))
```

(see `IsMinimal.exists_obstruction_of_tprod_eq_hochschildDifferential_add_sum_of_isIso` in
`TauCeti.AInfinityAlgebra`).

For the strict path-graded zigzag algebra `Z` (`TauCeti.zigzagStrictAInfinityAlgebra`), this file
shows that **every** trace pairing from `HochschildClass` and `WordPairing` sends the quadratic sum
in even arity `2 m + 2` (`m ≥ 1`) to a multiple of `2`: hence on any formal minimal deformation of
`Z` with `m₃ = ⋯ = m_{2m+1} = 0`, the pairing of the first obstruction lies in the ideal `(2)`.
In particular, whenever such a pairing evaluates to a unit (such as `1`) on a loop deformation, the
deformation cannot be formal when `2` is not a unit — complementing the `ℚ`-algebra and
`Invertible 2` criteria in `Invariance` and removing all characteristic restrictions in arity four.

## Why the quadratic sum pairs to `2 k`

Two involutions combine without dividing by `2`:

1. **Dart reversal on squares of degree-one elements.** Because `ψ` has suspended degree zero, it
   maps every nonempty word of arrows to path length one. For any `u, v` of path length one,
   expanding in the vertex-arrow-volume basis shows
   `tr(u * v) = ∑_d coord_d(u) * coord_{d.symm}(v)`. For `u = v`, the fixed-point-free involution
   `d ↦ d.symm` on `G.Dart` groups the sum into pairs of equal terms
   `coord_d(u) * coord_{d.symm}(u)`, so `tr(u * u) ∈ 2 k` over **every** commutative ring,
   including characteristic `2`.
2. **Swapping the two blocks of a cut.** In even arity `2 m + 2`:
   * For `d ≠ m + 1`, cyclically shifting a word by `2 m + 2 - d` steps exchanges the `(d, 2m+2-d)`
     cut with the `(2m+2-d, d)` cut, commutes the two factors inside `tr`, and multiplies an
     anticyclic weight `a` by `(-1)^{2m+2-d}`, so the sum of the `d` and `2 m + 2 - d` contributions
     is `(1 + (-1)^{2m+2-d}) S_d`, which is either `2 S_d` or `0`.
   * At the midpoint `d = m + 1`, shifting a word by `m + 1` steps is an involution `τ` on words of
     length `2 m + 2`. Free `τ`-orbits contribute `(1 + (-1)^{m+1})` times one representative, while
     a `τ`-fixed word has two identical half-words, reducing its contribution to `tr(u * u) ∈ 2 k`.
   * For the quartic backtrack pairing `TauCeti.zigzagBacktrackPairing` with a symmetric weight
     matrix `a`, exchanging `(d, e) ↔ (e, d)` swaps the two halves of both `B d e` and `B' d e`,
     while diagonal pairs `(d, d)` have two identical halves and again reduce to `tr(u * u) ∈ 2 k`.

## Main results

* `TauCeti.exists_zigzagWordPairing_obstruction_eq_two_mul_of_isFormal`: in even arity `2 m + 2`,
  any anticyclic signless word pairing maps the first obstruction of a formal minimal deformation of
  `Z` into `2 k`.
* `TauCeti.exists_zigzagWordPairing_obstruction_eq_two_mul_of_anticyclic_of_isFormal`: the same for
  word pairings induced by an anticyclic linear functional on a target satisfying the signless
  preprojective relations.
* `TauCeti.exists_zigzagBacktrackPairing_obstruction_eq_two_mul_of_isFormal`: in arity four, any
  balanced symmetric backtrack pairing maps the quartic obstruction of a formal minimal deformation
  of `Z` with `m₃ = 0` into `2 k`.

## References

* Y. Liu and Z. Wang, *A-infinity deformations of zigzag algebras via Ginzburg dg algebras*,
  Section 4, for minimal `A∞` deformations of zigzag algebras.
* T. Kadeishvili, *The structure of the `A(∞)`-algebra, and the Hochschild and Harrison
  cohomologies*, Trudy Tbiliss. Mat. Inst. 91 (1988), 19--27.
* R. S. Huerfano and M. Khovanov, *A category for the adjoint representation*, Sections 3 and 4, for
  the Frobenius trace and quadratic dual of a zigzag algebra.
-/

public section

namespace TauCeti

open PathAlgebra DoubledQuiver AInfinity ReducedTensorWords

universe u w

variable {k : Type w} [CommRing k] {V : Type u} {G : SimpleGraph V} [Finite V]
  {hns : ∀ i : V, ∃ j, G.Adj i j}

local notation "𝒵" => zigzagStrictAInfinityAlgebra k hns

local notation "𝔞" d:max => zigzagMk k G (ofArrow (arrow G (SimpleGraph.Dart.adj d)))

/-! ### Sums over involutions and degree-one traces -/

section TraceParity

omit [Finite V] in
/-- If an involution `τ` on a finite type sends every fixed point `x` to a multiple of `2` under `g`
and satisfies `g x + g (τ x) ∈ 2 k` on every two-element orbit, then `∑ x, g x` is a multiple of
`2`. Ordering `α` via `Fintype.equivFin` picks one representative of each two-element orbit without
dividing by `2`. -/
private theorem exists_sum_eq_two_mul_of_involutive {α : Type*} [Fintype α]
    {τ : α → α} (hτ : Function.Involutive τ) (g : α → k)
    (hfix : ∀ x, τ x = x → ∃ y : k, g x = 2 * y)
    (horb : ∀ x, τ x ≠ x → ∃ y : k, g x + g (τ x) = 2 * y) :
    ∃ y : k, ∑ x : α, g x = 2 * y := by
  classical
  let e := Fintype.equivFin α
  have hsplit (x : α) : g x = (if τ x = x then g x else 0) +
      ((if e x < e (τ x) then g x else 0) + (if e (τ x) < e x then g x else 0)) := by
    rcases eq_or_ne (τ x) x with h | h
    · simp [h]
    · rcases lt_or_gt_of_ne (e.injective.ne h.symm) with hlt | hgt
      · simp [h, hlt, asymm hlt]
      · simp [h, hgt, asymm hgt]
  have hrev : (∑ x : α, if e (τ x) < e x then g x else 0) =
      ∑ x : α, if e x < e (τ x) then g (τ x) else 0 := by
    rw [← Equiv.sum_comp hτ.toPerm (fun x ↦ if e (τ x) < e x then g x else 0)]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    change (if e (τ (τ x)) < e (τ x) then g (τ x) else 0) = _
    simp only [hτ x]
  have h1 : ∀ x : α, ∃ y : k, (if τ x = x then g x else 0) = 2 * y := fun x ↦ by
    by_cases h : τ x = x
    · simpa [h] using hfix x h
    · exact ⟨0, by simp [h]⟩
  have h2 : ∀ x : α, ∃ y : k, (if e x < e (τ x) then g x + g (τ x) else 0) = 2 * y := fun x ↦ by
    by_cases h : e x < e (τ x)
    · simpa [h] using horb x fun hx ↦ (ne_of_lt h) (congrArg e hx.symm)
    · exact ⟨0, by simp [h]⟩
  choose y1 hy1 using h1
  choose y2 hy2 using h2
  refine ⟨∑ x, y1 x + ∑ x, y2 x, ?_⟩
  calc ∑ x : α, g x
      = (∑ x, if τ x = x then g x else 0) +
          ((∑ x, if e x < e (τ x) then g x else 0) +
            (∑ x, if e (τ x) < e x then g x else 0)) := by
        simp_rw [Finset.sum_congr rfl fun x _ ↦ hsplit x, Finset.sum_add_distrib]
    _ = (∑ x, if τ x = x then g x else 0) +
          ∑ x, if e x < e (τ x) then g x + g (τ x) else 0 := by
        rw [hrev, ← Finset.sum_add_distrib]
        congr 1
        exact Finset.sum_congr rfl fun x _ ↦ by split_ifs <;> simp
    _ = 2 * (∑ x, y1 x + ∑ x, y2 x) := by
        simp_rw [hy1, hy2, ← Finset.mul_sum, mul_add]

omit [Finite V] in
private theorem exists_one_add_neg_one_pow_eq_two_mul (r : ℕ) :
    ∃ c : k, 1 + (-1 : k) ^ r = 2 * c := by
  rcases neg_one_pow_eq_or k r with h | h
  · exact ⟨1, by rw [h]; ring⟩
  · exact ⟨0, by rw [h]; ring⟩

/-- On elements `u, v` of path length one, the Frobenius trace of `u * v` is the sum over all darts
`d` of the `d`-coordinate of `u` times the `d.symm`-coordinate of `v`: neither `u` nor `v` has a
vertex-idempotent component, and arrows annihilate volume classes. -/
private theorem zigzagTrace_mul_eq_sum_dart [Fintype G.Dart]
    {u v : nonisolatedZigzagQuotient k G}
    (hu : u ∈ zigzagIntegerGrade k G 1) (hv : v ∈ zigzagIntegerGrade k G 1) :
    zigzagTrace k G hns (u * v) =
      ∑ d : G.Dart, (zigzagBasis k G hns).coord (.inr (.inl d)) u *
        (zigzagBasis k G hns).coord (.inr (.inl d.symm)) v := by
  classical
  have := Fintype.ofFinite V
  rw [← zigzagTracePairing_apply]
  conv_lhs => rw [← (zigzagBasis k G hns).sum_repr v]
  rw [map_sum, Fintype.sum_sum_type, Fintype.sum_sum_type]
  have hleft : ∑ i : V, zigzagTracePairing k G hns u
      ((zigzagBasis k G hns).repr v (.inl i) • (zigzagBasis k G hns) (.inl i)) = 0 :=
    Finset.sum_eq_zero fun i _ ↦ by
      rw [← Module.Basis.coord_apply,
        zigzagBasis_coord_vertex_eq_zero_of_mem_zigzagIntegerGrade k G hns i one_ne_zero hv,
        zero_smul, map_zero]
  have hright : ∑ i : V, zigzagTracePairing k G hns u
      ((zigzagBasis k G hns).repr v (.inr (.inr i)) • (zigzagBasis k G hns) (.inr (.inr i))) = 0 :=
    Finset.sum_eq_zero fun i _ ↦ by
      rw [map_smul, zigzagBasis_apply, ← zigzagDualIndex_inl,
        zigzagTracePairing_apply_zigzagBasisFun_zigzagDualIndex, ← Module.Basis.coord_apply,
        ← Module.Basis.coord_apply,
        zigzagBasis_coord_vertex_eq_zero_of_mem_zigzagIntegerGrade k G hns i one_ne_zero hu,
        smul_zero]
  rw [hleft, hright, zero_add, add_zero,
    ← Equiv.sum_comp (Function.Involutive.toPerm (SimpleGraph.Dart.symm (G := G))
      SimpleGraph.Dart.symm_involutive)]
  refine Finset.sum_congr rfl fun d _ ↦ ?_
  dsimp [Function.Involutive.toPerm]
  rw [map_smul, zigzagBasis_apply, ← zigzagDualIndex_inr_inl,
    zigzagTracePairing_apply_zigzagBasisFun_zigzagDualIndex, ← Module.Basis.coord_apply,
    ← Module.Basis.coord_apply, smul_eq_mul, mul_comm]

/-- **The trace of the square of a degree-one element lies in `2 k`.** Reversing darts is a
fixed-point-free involution on `G.Dart` pairing the `d` and `d.symm` summands of
`zigzagTrace_mul_eq_sum_dart`. -/
private theorem exists_zigzagTrace_mul_self_eq_two_mul
    {u : nonisolatedZigzagQuotient k G} (hu : u ∈ zigzagIntegerGrade k G 1) :
    ∃ y : k, zigzagTrace k G hns (u * u) = 2 * y := by
  classical
  have := Fintype.ofFinite V
  rw [zigzagTrace_mul_eq_sum_dart hu hu]
  refine exists_sum_eq_two_mul_of_involutive SimpleGraph.Dart.symm_involutive _
    (fun d hd ↦ (d.symm_ne hd).elim) fun d _ ↦ ⟨(zigzagBasis k G hns).coord (.inr (.inl d)) u *
      (zigzagBasis k G hns).coord (.inr (.inl d.symm)) u, ?_⟩
  rw [SimpleGraph.Dart.symm_symm]
  ring

/-- A homogeneous cochain `ψ` of suspended degree zero maps any nonempty subword of degree-one
elements into path length one. -/
private theorem apply_subword_mem_zigzagIntegerGrade_one
    {ψ : ReducedTensorWords k (nonisolatedZigzagQuotient k G) →ₗ[k] nonisolatedZigzagQuotient k G}
    (hψ : LinearMap.IsHomogeneous ψ (gradedPiece ((𝒵).grading.shift 1))
      ((𝒵).grading.shift 1).piece 0)
    {N : ℕ} {x : Fin N → nonisolatedZigzagQuotient k G}
    (hx : ∀ i, x i ∈ zigzagIntegerGrade k G 1) {p d : ℕ} (hd : 0 < d) (hpd : p + d ≤ N) :
    ψ (subword k x p d) ∈ zigzagIntegerGrade k G 1 := by
  rw [subword_eq_of_tprod k x hd hpd]
  have h := hψ.map_mem (mem_gradedPiece_of_tprod ((𝒵).grading.shift 1) (n := d) hd
    (fun j ↦ x ⟨p + j.1, by omega⟩) (fun _ ↦ 0) fun j ↦ by
      rw [InternalGrading.shift_piece, zigzagStrictAInfinityAlgebra_grading_piece, zero_add]
      exact hx _)
  simpa [InternalGrading.shift_piece] using h

/-- On two elements `u, v` with `u` of path length one, the binary Taylor component of `𝒵` is
`-(u * v)` because the Koszul twist of degree one is `-1`. -/
private theorem taylor_of_tprod_two_eq_neg_mul
    {u : nonisolatedZigzagQuotient k G} (hu : u ∈ zigzagIntegerGrade k G 1)
    (v : nonisolatedZigzagQuotient k G) :
    (𝒵).taylor (of k _ ⟨2, two_pos⟩ (PiTensorProduct.tprod k ![u, v])) = -(u * v) := by
  have htw : (𝒵).taylor (of k _ ⟨2, two_pos⟩ (PiTensorProduct.tprod k ![u, v])) =
      (𝒵).grading.koszulTwist 1 u * v := by
    rw [AInfinityAlgebra.taylor_of_tprod, zigzagStrictAInfinityAlgebra_m_two_apply]
    norm_num
  rw [htw, (𝒵).grading.koszulTwist_one_apply_of_mem (e := 1)
    (by rwa [zigzagStrictAInfinityAlgebra_grading_piece])]
  simp

end TraceParity

/-! ### Cyclic shifts and even-arity word pairings -/

section WordParity

omit [Finite V] in
private theorem shift_one_eq_snoc_tail {α : Type*} {n : ℕ} (w : Fin (n + 2) → α) :
    (fun i : Fin (n + 2) ↦ w (i + 1)) = Fin.snoc (Fin.tail w) (w 0) :=
  funext (Fin.lastCases (by rw [Fin.last_add_one, Fin.snoc_last]) fun j ↦ by
    rw [Fin.coeSucc_eq_succ, Fin.snoc_castSucc]
    rfl)

omit [Finite V] in
private theorem weight_shift_eq_neg_one_pow_mul {n : ℕ} {a : (Fin (n + 2) → G.Dart) → k}
    (hrot : ∀ (u : Fin (n + 1) → G.Dart) (e : G.Dart), a (Fin.snoc u e) = -a (Fin.cons e u))
    {r : ℕ} (hr : r < n + 2) (w : Fin (n + 2) → G.Dart) :
    a (fun i ↦ w (i + ⟨r, hr⟩)) = (-1 : k) ^ r * a w := by
  induction r with
  | zero =>
    have h0 : (⟨0, hr⟩ : Fin (n + 2)) = 0 := rfl
    simp [h0]
  | succ r ih =>
    let w' : Fin (n + 2) → G.Dart := fun j ↦ w (j + ⟨r, by omega⟩)
    have hstep : (fun i : Fin (n + 2) ↦ w (i + ⟨r + 1, hr⟩)) = fun i ↦ w' (i + 1) :=
      funext fun i ↦ congrArg w <| by
        have h1 : (⟨r + 1, hr⟩ : Fin (n + 2)) = 1 + ⟨r, by omega⟩ :=
          Fin.ext (by
            rw [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < n + 2),
              Nat.add_comm 1 r, Nat.mod_eq_of_lt hr])
        rw [h1, add_assoc]
    rw [hstep, shift_one_eq_snoc_tail w', hrot, Fin.cons_self_tail w', ih (by omega), pow_succ']
    ring

omit [Finite V] in
private theorem subword_shift_zero_eq {M : Type*} [AddCommMonoid M] [Module k M]
    {N d : ℕ} (hdN : d < N) (x : Fin N → M) :
    subword k (fun i : Fin N ↦ x (i + ⟨d, hdN⟩)) 0 (N - d) = subword k x d (N - d) :=
  subword_congr k _ _ (by omega) (by omega) fun j hj ↦ congrArg x <| Fin.ext <| by
    rw [Fin.val_add]
    dsimp only
    rw [Nat.mod_eq_of_lt (by omega)]
    omega

omit [Finite V] in
private theorem subword_shift_right_eq {M : Type*} [AddCommMonoid M] [Module k M]
    {N d : ℕ} (hdN : d < N) (x : Fin N → M) :
    subword k (fun i : Fin N ↦ x (i + ⟨d, hdN⟩)) (N - d) d = subword k x 0 d :=
  subword_congr k _ _ (by omega) (by omega) fun j hj ↦ congrArg x <| Fin.ext <| by
    rw [Fin.val_add]
    dsimp only
    rw [show (N - d + j) + d = j + N by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega), Nat.zero_add]

variable [Fintype G.Dart]

/-- Reindexing by a cyclic shift of `d` steps relates the `(2 * m + 2 - d, d)` cut to the
`(d, 2 * m + 2 - d)` cut up to the anticyclicity sign `(-1) ^ d`. -/
private theorem sum_word_cut_sub_eq_neg_one_pow_mul {m : ℕ}
    {a : (Fin (2 * m + 2) → G.Dart) → k}
    (hrot : ∀ (u : Fin (2 * m + 1) → G.Dart) (e : G.Dart), a (Fin.snoc u e) = -a (Fin.cons e u))
    (ψ : ReducedTensorWords k (nonisolatedZigzagQuotient k G) →ₗ[k] nonisolatedZigzagQuotient k G)
    {d : ℕ} (hdN : d < 2 * m + 2) :
    (∑ w : Fin (2 * m + 2) → G.Dart, a w * zigzagTrace k G hns
        (ψ (subword k (fun t ↦ 𝔞 (w t)) 0 (2 * m + 2 - d)) *
          ψ (subword k (fun t ↦ 𝔞 (w t)) (2 * m + 2 - d) (2 * m + 2 - (2 * m + 2 - d))))) =
      (-1 : k) ^ d * ∑ w : Fin (2 * m + 2) → G.Dart, a w * zigzagTrace k G hns
        (ψ (subword k (fun t ↦ 𝔞 (w t)) 0 d) *
          ψ (subword k (fun t ↦ 𝔞 (w t)) d (2 * m + 2 - d))) := by
  have hsub : 2 * m + 2 - (2 * m + 2 - d) = d := by omega
  let rFin : Fin (2 * m + 2) := ⟨d, hdN⟩
  let σ : (Fin (2 * m + 2) → G.Dart) ≃ (Fin (2 * m + 2) → G.Dart) :=
    { toFun := fun w i ↦ w (i + rFin)
      invFun := fun w i ↦ w (i - rFin)
      left_inv := fun w ↦ funext fun i ↦ congrArg w (sub_add_cancel i rFin)
      right_inv := fun w ↦ funext fun i ↦ congrArg w (add_sub_cancel_right i rFin) }
  rw [hsub, Finset.mul_sum, ← Equiv.sum_comp σ]
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  have hw := weight_shift_eq_neg_one_pow_mul hrot hdN w
  have hs0 := subword_shift_zero_eq (k := k) (N := 2 * m + 2) hdN (fun t ↦ 𝔞 (w t))
  have hs1 := subword_shift_right_eq (k := k) (N := 2 * m + 2) hdN (fun t ↦ 𝔞 (w t))
  dsimp only [σ, Equiv.coe_fn_mk, rFin]
  rw [hw, hs0, hs1, zigzagTrace_mul_comm]
  ring

/-- At the midpoint cut `d = m + 1` of a word of length `2 * m + 2`, shifting by `m + 1` steps is
an involution whose fixed words have two equal half-words and whose two-element orbits pair with
sign `1 + (-1) ^ (m + 1)`. -/
private theorem exists_sum_word_cut_mid_eq_two_mul {m : ℕ}
    {a : (Fin (2 * m + 2) → G.Dart) → k}
    (hrot : ∀ (u : Fin (2 * m + 1) → G.Dart) (e : G.Dart), a (Fin.snoc u e) = -a (Fin.cons e u))
    {ψ : ReducedTensorWords k (nonisolatedZigzagQuotient k G) →ₗ[k] nonisolatedZigzagQuotient k G}
    (hψ : LinearMap.IsHomogeneous ψ (gradedPiece ((𝒵).grading.shift 1))
      ((𝒵).grading.shift 1).piece 0) :
    ∃ y : k, (∑ w : Fin (2 * m + 2) → G.Dart, a w * zigzagTrace k G hns
      (ψ (subword k (fun t ↦ 𝔞 (w t)) 0 (m + 1)) *
        ψ (subword k (fun t ↦ 𝔞 (w t)) (m + 1) (2 * m + 2 - (m + 1))))) = 2 * y := by
  have hsub : 2 * m + 2 - (m + 1) = m + 1 := by omega
  rw [hsub]
  let τ : (Fin (2 * m + 2) → G.Dart) → (Fin (2 * m + 2) → G.Dart) :=
    fun w i ↦ w (i + ⟨m + 1, by omega⟩)
  have hτ : Function.Involutive τ := fun w ↦ funext fun i ↦ congrArg w <| by
    have h0 : (⟨m + 1, by omega⟩ : Fin (2 * m + 2)) + ⟨m + 1, by omega⟩ = 0 :=
      Fin.ext (by rw [Fin.val_add, show (m + 1) + (m + 1) = 2 * m + 2 by omega, Nat.mod_self]; rfl)
    rw [add_assoc, h0, add_zero]
  have hsw0 (w : Fin (2 * m + 2) → G.Dart) :
      subword k (fun t ↦ 𝔞 (τ w t)) 0 (m + 1) =
        subword k (fun t ↦ 𝔞 (w t)) (m + 1) (m + 1) := by
    have h := subword_shift_zero_eq (k := k) (N := 2 * m + 2) (d := m + 1)
      (by omega) (fun t ↦ 𝔞 (w t))
    rwa [hsub] at h
  have hsw1 (w : Fin (2 * m + 2) → G.Dart) :
      subword k (fun t ↦ 𝔞 (τ w t)) (m + 1) (m + 1) =
        subword k (fun t ↦ 𝔞 (w t)) 0 (m + 1) := by
    have h := subword_shift_right_eq (k := k) (N := 2 * m + 2) (d := m + 1)
      (by omega) (fun t ↦ 𝔞 (w t))
    rwa [hsub] at h
  refine exists_sum_eq_two_mul_of_involutive hτ _ (fun w hw ↦ ?_) (fun w _ ↦ ?_)
  · have heq := (hsw0 w).symm
    rw [hw] at heq
    obtain ⟨z, hz⟩ := exists_zigzagTrace_mul_self_eq_two_mul (hns := hns)
      (apply_subword_mem_zigzagIntegerGrade_one hψ (x := fun t ↦ 𝔞 (w t))
        (fun _ ↦ zigzagMk_ofArrow_mem_zigzagIntegerGrade_one k G _)
        (p := 0) (d := m + 1) (by omega) (by omega))
    exact ⟨a w * z, by rw [heq, hz]; ring⟩
  · obtain ⟨c, hc⟩ := exists_one_add_neg_one_pow_eq_two_mul (k := k) (m + 1)
    refine ⟨c * (a w * zigzagTrace k G hns (ψ (subword k (fun t ↦ 𝔞 (w t)) 0 (m + 1)) *
      ψ (subword k (fun t ↦ 𝔞 (w t)) (m + 1) (m + 1)))), ?_⟩
    have haτ : a (τ w) = (-1 : k) ^ (m + 1) * a w :=
      weight_shift_eq_neg_one_pow_mul hrot (by omega) w
    rw [haτ, hsw0, hsw1, zigzagTrace_mul_comm k G hns (ψ (subword k (fun t ↦ 𝔞 (w t)) (m + 1) _))]
    linear_combination (a w * zigzagTrace k G hns (ψ (subword k (fun t ↦ 𝔞 (w t)) 0 (m + 1)) *
      ψ (subword k (fun t ↦ 𝔞 (w t)) (m + 1) (m + 1)))) * hc

/-- Summing over all cuts `d ∈ [2, 2 * m]` of words of length `2 * m + 2` produces an element of
`2 k`. -/
private theorem exists_sum_Icc_word_cut_eq_two_mul {m : ℕ}
    {a : (Fin (2 * m + 2) → G.Dart) → k}
    (hrot : ∀ (u : Fin (2 * m + 1) → G.Dart) (e : G.Dart), a (Fin.snoc u e) = -a (Fin.cons e u))
    {ψ : ReducedTensorWords k (nonisolatedZigzagQuotient k G) →ₗ[k] nonisolatedZigzagQuotient k G}
    (hψ : LinearMap.IsHomogeneous ψ (gradedPiece ((𝒵).grading.shift 1))
      ((𝒵).grading.shift 1).piece 0) :
    ∃ y : k, (∑ d ∈ Finset.Icc 2 (2 * m), ∑ w : Fin (2 * m + 2) → G.Dart,
      a w * zigzagTrace k G hns
        (ψ (subword k (fun t ↦ 𝔞 (w t)) 0 d) *
          ψ (subword k (fun t ↦ 𝔞 (w t)) d (2 * m + 2 - d)))) = 2 * y := by
  let S (d : ℕ) : k := ∑ w : Fin (2 * m + 2) → G.Dart, a w * zigzagTrace k G hns
    (ψ (subword k (fun t ↦ 𝔞 (w t)) 0 d) * ψ (subword k (fun t ↦ 𝔞 (w t)) d (2 * m + 2 - d)))
  rw [← Finset.sum_coe_sort (Finset.Icc 2 (2 * m)) S]
  let τ : Finset.Icc 2 (2 * m) → Finset.Icc 2 (2 * m) := fun d ↦
    ⟨2 * m + 2 - d.1, Finset.mem_Icc.2 (by have := Finset.mem_Icc.1 d.2; omega)⟩
  have hτ : Function.Involutive τ := fun d ↦
    Subtype.ext (by have := Finset.mem_Icc.1 d.2; dsimp [τ]; omega)
  refine exists_sum_eq_two_mul_of_involutive hτ (fun d ↦ S d.1) (fun d hd ↦ ?_) (fun d _ ↦ ?_)
  · have hmid : d.1 = m + 1 := by
      have h1 : 2 * m + 2 - d.1 = d.1 := congrArg Subtype.val hd
      have h2 := Finset.mem_Icc.1 d.2
      omega
    rw [hmid]
    exact exists_sum_word_cut_mid_eq_two_mul hrot hψ
  · have hd := Finset.mem_Icc.1 d.2
    obtain ⟨c, hc⟩ := exists_one_add_neg_one_pow_eq_two_mul (k := k) d.1
    have hS : S (2 * m + 2 - d.1) = (-1 : k) ^ d.1 * S d.1 :=
      sum_word_cut_sub_eq_neg_one_pow_mul hrot ψ (by omega)
    refine ⟨c * S d.1, ?_⟩
    dsimp only [τ]
    rw [hS]
    linear_combination S d.1 * hc

/-- **Even-arity word pairings map formal zigzag obstructions into `2 k`.** Let `𝒜` be a minimal
`A∞` algebra with the grading and binary operation of the strict zigzag algebra `𝒵` and
`m₃ = ⋯ = m_{2m+1} = 0`, and let the weights `a` on words of `2 m + 2` darts be anticyclic and
satisfy the signless relation in every consecutive pair of positions. If `𝒜` is formal, then
`zigzagWordPairing hns (2 * m) a` sends the obstruction `m_{2m+2}` of `𝒜` into `2 k`. -/
theorem exists_zigzagWordPairing_obstruction_eq_two_mul_of_isFormal [DecidableEq V]
    {𝒜 : AInfinityAlgebra k (nonisolatedZigzagQuotient k G)} (h𝒜 : 𝒜.IsMinimal)
    (hG : 𝒜.grading = (𝒵).grading) (h₂ : 𝒜.m 2 = (𝒵).m 2) {m : ℕ}
    (hlow : ∀ r, 3 ≤ r → r ≤ 2 * m + 1 → 𝒜.m r = 0) (hF : 𝒜.IsFormal)
    {a : (Fin (2 * m + 2) → G.Dart) → k}
    (hrot : ∀ (u : Fin (2 * m + 1) → G.Dart) (e : G.Dart), a (Fin.snoc u e) = -a (Fin.cons e u))
    (hrel : ∀ (p : Fin (2 * m + 1)) (u : Fin (2 * m) → G.Dart) (v : V),
      ∑ d : G.Dart with d.snd = v, a (Fin.insertNth p.castSucc d (Fin.insertNth p d.symm u)) = 0) :
    ∃ y : k, zigzagWordPairing hns (2 * m) a
      (𝒜.obstruction 𝒵 ⟨2 * m + 2, by omega⟩) = 2 * y := by
  have hm𝒵 : ∀ r, 3 ≤ r → (𝒵).m r = 0 := fun _ hr ↦
    zigzagStrictAInfinityAlgebra_m_eq_zero (by omega)
  have hZ := isMinimal_zigzagStrictAInfinityAlgebra (k := k) (hns := hns)
  obtain ⟨f, hf⟩ := (h𝒜.isFormal_iff_exists_isIso hZ hm𝒵 hG h₂).1 hF
  obtain ⟨ψ, hψ, -, hdec⟩ :=
    hZ.exists_obstruction_of_tprod_eq_hochschildDifferential_add_sum_of_isIso
      hm𝒵 hG h₂ (n := 2 * m) hlow hf
  have hcob := zigzagWordPairing_hochschildDifferential_eq_zero (hns := hns) hrot hrel hψ
  rw [zigzagWordPairing_apply] at hcob ⊢
  have hterm (w : Fin (2 * m + 2) → G.Dart) :
      a w * zigzagTrace k G hns (𝒜.obstruction 𝒵 ⟨2 * m + 2, by omega⟩
          (of k _ ⟨2 * m + 2, by omega⟩ (PiTensorProduct.tprod k fun t ↦ 𝔞 (w t)))) =
        a w * zigzagTrace k G hns ((𝒵).hochschildDifferential 0 ψ
          (of k _ ⟨2 * m + 2, by omega⟩ (PiTensorProduct.tprod k fun t ↦ 𝔞 (w t)))) -
        ∑ d ∈ Finset.Icc 2 (2 * m), a w * zigzagTrace k G hns
          (ψ (subword k (fun t ↦ 𝔞 (w t)) 0 d) *
            ψ (subword k (fun t ↦ 𝔞 (w t)) d (2 * m + 2 - d))) := by
    rw [hdec, map_add, map_sum, mul_add, Finset.mul_sum]
    have hneg : ∀ d ∈ Finset.Icc 2 (2 * m),
        a w * zigzagTrace k G hns ((𝒵).taylor (of k _ ⟨2, two_pos⟩
          (PiTensorProduct.tprod k ![ψ (subword k (fun t ↦ 𝔞 (w t)) 0 d),
            ψ (subword k (fun t ↦ 𝔞 (w t)) d (2 * m + 2 - d))]))) =
        -(a w * zigzagTrace k G hns (ψ (subword k (fun t ↦ 𝔞 (w t)) 0 d) *
          ψ (subword k (fun t ↦ 𝔞 (w t)) d (2 * m + 2 - d)))) := fun d hd ↦ by
      have hd' := Finset.mem_Icc.1 hd
      rw [taylor_of_tprod_two_eq_neg_mul (apply_subword_mem_zigzagIntegerGrade_one hψ
        (fun _ ↦ zigzagMk_ofArrow_mem_zigzagIntegerGrade_one k G _) (by omega) (by omega)),
        map_neg, mul_neg]
    rw [Finset.sum_congr rfl hneg, Finset.sum_neg_distrib, sub_eq_add_neg]
  simp_rw [Finset.sum_congr rfl fun w _ ↦ hterm w, Finset.sum_sub_distrib, hcob, zero_sub]
  rw [Finset.sum_comm]
  obtain ⟨y, hy⟩ := exists_sum_Icc_word_cut_eq_two_mul hrot hψ
  exact ⟨-y, by rw [hy]; ring⟩

/-- **Anticyclic preprojective functionals map formal even-arity zigzag obstructions into
`2 k`.** -/
theorem exists_zigzagWordPairing_obstruction_eq_two_mul_of_anticyclic_of_isFormal [DecidableEq V]
    {B : Type*} [Semiring B] [Module k B]
    {𝒜 : AInfinityAlgebra k (nonisolatedZigzagQuotient k G)} (h𝒜 : 𝒜.IsMinimal)
    (hG : 𝒜.grading = (𝒵).grading) (h₂ : 𝒜.m 2 = (𝒵).m 2) {m : ℕ}
    (hlow : ∀ r, 3 ≤ r → r ≤ 2 * m + 1 → 𝒜.m r = 0) (hF : 𝒜.IsFormal)
    (β : G.Dart → B) (hβ : ∀ v : V, ∑ d : G.Dart with d.snd = v, β d * β d.symm = 0)
    (f : B →ₗ[k] k) (hf : ∀ (e : G.Dart) (y : B), f (y * β e) = -f (β e * y)) :
    ∃ y : k, zigzagWordPairing hns (2 * m) (fun w ↦ f (List.ofFn fun t ↦ β (w t)).prod)
      (𝒜.obstruction 𝒵 ⟨2 * m + 2, by omega⟩) = 2 * y := by
  refine exists_zigzagWordPairing_obstruction_eq_two_mul_of_isFormal h𝒜 hG h₂ hlow hF
    (fun u e ↦ ?_) (fun p u v ↦ ?_)
  · have hsnoc : (List.ofFn fun t ↦ β ((Fin.snoc u e : Fin (2 * m + 2) → G.Dart) t)).prod =
        (List.ofFn fun t ↦ β (u t)).prod * β e := by
      rw [List.ofFn_succ' (n := 2 * m + 1), List.concat_eq_append, List.prod_append,
        List.prod_singleton]
      simp
    have hcons : (List.ofFn fun t ↦ β ((Fin.cons e u : Fin (2 * m + 2) → G.Dart) t)).prod =
        β e * (List.ofFn fun t ↦ β (u t)).prod := by
      rw [show (fun t ↦ β ((Fin.cons e u : Fin (2 * m + 2) → G.Dart) t)) =
          Fin.cons (β e) fun t ↦ β (u t) from Fin.comp_cons β e u, List.ofFn_cons, List.prod_cons]
    rw [hsnoc, hcons, hf]
  · obtain ⟨L, R, h⟩ := List.exists_prod_ofFn_insertNth_insertNth β p u
    simp_rw [h]
    calc ∑ d : G.Dart with d.snd = v, f (L * β d * β d.symm * R)
        = f (L * (∑ d : G.Dart with d.snd = v, β d * β d.symm) * R) := by
          rw [Finset.mul_sum, Finset.sum_mul, map_sum]
          simp only [mul_assoc]
      _ = 0 := by rw [hβ, mul_zero, zero_mul, map_zero]

end WordParity

/-! ### Quartic backtrack pairings -/

section BacktrackParity

variable [Fintype G.Dart]

/-- If a family `W d e` of four-dart words swaps its two length-two halves when `d` and `e` are
exchanged, then any symmetric matrix `a` pairs the `(2, 2)` quadratic cut of `W` into `2 k`. -/
private theorem exists_sum_dart_pair_cut_eq_two_mul
    {a : Matrix G.Dart G.Dart k} (ha : a.IsSymm)
    {ψ : ReducedTensorWords k (nonisolatedZigzagQuotient k G) →ₗ[k] nonisolatedZigzagQuotient k G}
    (hψ : LinearMap.IsHomogeneous ψ (gradedPiece ((𝒵).grading.shift 1))
      ((𝒵).grading.shift 1).piece 0)
    (W : G.Dart → G.Dart → Fin 4 → G.Dart)
    (hW : ∀ d e : G.Dart, W e d = fun t ↦ W d e (t + (2 : Fin 4))) :
    ∃ y : k, (∑ d : G.Dart, ∑ e : G.Dart, a d e * zigzagTrace k G hns
      (ψ (subword k (fun t ↦ 𝔞 (W d e t)) 0 2) *
        ψ (subword k (fun t ↦ 𝔞 (W d e t)) 2 2))) = 2 * y := by
  rw [← Fintype.sum_prod_type']
  have hsw0 (d e : G.Dart) :
      subword k (fun t ↦ 𝔞 (W e d t)) 0 2 = subword k (fun t ↦ 𝔞 (W d e t)) 2 2 := by
    rw [hW]
    exact subword_shift_zero_eq (k := k) (N := 4) (d := 2) (by decide) (fun t ↦ 𝔞 (W d e t))
  have hsw1 (d e : G.Dart) :
      subword k (fun t ↦ 𝔞 (W e d t)) 2 2 = subword k (fun t ↦ 𝔞 (W d e t)) 0 2 := by
    rw [hW]
    exact subword_shift_right_eq (k := k) (N := 4) (d := 2) (by decide) (fun t ↦ 𝔞 (W d e t))
  refine exists_sum_eq_two_mul_of_involutive (τ := Prod.swap) (fun p ↦ Prod.swap_swap p) _
    (fun p hp ↦ ?_) (fun p _ ↦ ?_)
  · obtain ⟨d, e⟩ := p
    obtain rfl : d = e := (Prod.ext_iff.1 hp).2
    obtain ⟨z, hz⟩ := exists_zigzagTrace_mul_self_eq_two_mul (hns := hns)
      (apply_subword_mem_zigzagIntegerGrade_one hψ (x := fun t ↦ 𝔞 (W d d t))
        (fun _ ↦ zigzagMk_ofArrow_mem_zigzagIntegerGrade_one k G _)
        (p := 0) (d := 2) (by decide) (by decide))
    exact ⟨a d d * z, by rw [← hsw0 d d, hz]; ring⟩
  · obtain ⟨d, e⟩ := p
    refine ⟨a d e * zigzagTrace k G hns
      (ψ (subword k (fun t ↦ 𝔞 (W d e t)) 0 2) * ψ (subword k (fun t ↦ 𝔞 (W d e t)) 2 2)), ?_⟩
    dsimp only [Prod.swap]
    rw [ha.apply d e, hsw0 d e, hsw1 d e,
      zigzagTrace_mul_comm k G hns (ψ (subword k (fun t ↦ 𝔞 (W d e t)) 2 2))]
    ring

omit [Finite V] in
private theorem sum_mul_sub_sub_eq (a : Matrix G.Dart G.Dart k)
    (D₁ Q₁ D₂ Q₂ : G.Dart → G.Dart → k) :
    (∑ d, ∑ e, a d e * ((D₁ d e - Q₁ d e) - (D₂ d e - Q₂ d e))) =
      (∑ d, ∑ e, a d e * (D₁ d e - D₂ d e)) -
        (∑ d, ∑ e, a d e * Q₁ d e) + (∑ d, ∑ e, a d e * Q₂ d e) := by
  have h (d e : G.Dart) : a d e * ((D₁ d e - Q₁ d e) - (D₂ d e - Q₂ d e)) =
      a d e * (D₁ d e - D₂ d e) - a d e * Q₁ d e + a d e * Q₂ d e := by ring
  simp_rw [h, Finset.sum_add_distrib, Finset.sum_sub_distrib]

/-- **Balanced backtrack pairings map formal quartic zigzag obstructions into `2 k`.** Let `𝒜` be a
minimal `A∞` algebra with the grading and binary operation of `𝒵` and `m₃ = 0`, and let `a` be a
symmetric matrix of weights on pairs of darts vanishing on pairs with distinct heads and satisfying
`∑ d, a d e = a e.symm e.symm`. If `𝒜` is formal, then `zigzagBacktrackPairing hns a` sends the
quartic obstruction `m₄` of `𝒜` into `2 k`, over every commutative ring. -/
theorem exists_zigzagBacktrackPairing_obstruction_eq_two_mul_of_isFormal
    {𝒜 : AInfinityAlgebra k (nonisolatedZigzagQuotient k G)} (h𝒜 : 𝒜.IsMinimal)
    (hG : 𝒜.grading = (𝒵).grading) (h₂ : 𝒜.m 2 = (𝒵).m 2) (h₃ : 𝒜.m 3 = 0)
    (hF : 𝒜.IsFormal) {a : Matrix G.Dart G.Dart k} (ha : a.IsSymm)
    (hhead : ∀ d e, d.snd ≠ e.snd → a d e = 0) (hbal : ∀ e, ∑ d, a d e = a e.symm e.symm) :
    ∃ y : k, zigzagBacktrackPairing hns a (𝒜.obstruction 𝒵 ⟨4, by norm_num⟩) = 2 * y := by
  have hm𝒵 : ∀ r, 3 ≤ r → (𝒵).m r = 0 := fun _ hr ↦
    zigzagStrictAInfinityAlgebra_m_eq_zero (by omega)
  have hZ := isMinimal_zigzagStrictAInfinityAlgebra (k := k) (hns := hns)
  obtain ⟨f, hf⟩ := (h𝒜.isFormal_iff_exists_isIso hZ hm𝒵 hG h₂).1 hF
  obtain ⟨ψ, hψ, -, hdec⟩ :=
    hZ.exists_obstruction_of_tprod_eq_hochschildDifferential_add_sum_of_isIso hm𝒵 hG h₂
      (n := 2) (fun r hr1 hr2 ↦ (show r = 3 by omega) ▸ h₃) hf
  have hcob := zigzagBacktrackPairing_hochschildDifferential_eq_zero (hns := hns) ha hhead hbal hψ
  rw [zigzagBacktrackPairing_apply] at hcob ⊢
  have heval (x : Fin 4 → G.Dart) :
      zigzagTrace k G hns (𝒜.obstruction 𝒵 ⟨4, by norm_num⟩
          (of k _ ⟨4, by norm_num⟩ (PiTensorProduct.tprod k fun t ↦ 𝔞 (x t)))) =
        zigzagTrace k G hns ((𝒵).hochschildDifferential 0 ψ
          (of k _ ⟨4, by norm_num⟩ (PiTensorProduct.tprod k fun t ↦ 𝔞 (x t)))) -
        zigzagTrace k G hns (ψ (subword k (fun t ↦ 𝔞 (x t)) 0 2) *
          ψ (subword k (fun t ↦ 𝔞 (x t)) 2 2)) := by
    rw [hdec (fun t ↦ 𝔞 (x t))]
    simp only [Finset.Icc_self, Finset.sum_singleton, Nat.add_sub_cancel]
    rw [taylor_of_tprod_two_eq_neg_mul (apply_subword_mem_zigzagIntegerGrade_one hψ
      (fun _ ↦ zigzagMk_ofArrow_mem_zigzagIntegerGrade_one k G _) (by decide) (by decide)),
      map_add, map_neg, sub_eq_add_neg]
  have hswap2 (d e : G.Dart) : (fun t : Fin 4 ↦ zigzagBacktrackWalk G d.symm e t) =
      fun t ↦ zigzagBacktrackWalk G e.symm d (t + 2) :=
    funext fun t ↦ by fin_cases t <;> simp [zigzagBacktrackWalk_def]
  have hswap1 (d e : G.Dart) : (fun t : Fin 4 ↦ zigzagBacktrackWalk G d.symm e (t + 1)) =
      fun t ↦ zigzagBacktrackWalk G e.symm d ((t + 2) + 1) :=
    funext fun t ↦ by rw [congrFun (hswap2 d e) (t + 1), add_right_comm]
  obtain ⟨y1, hy1⟩ := exists_sum_dart_pair_cut_eq_two_mul ha hψ
    (fun d e t ↦ zigzagBacktrackWalk G e.symm d (t + 1)) hswap1
  obtain ⟨y2, hy2⟩ := exists_sum_dart_pair_cut_eq_two_mul ha hψ
    (fun d e t ↦ zigzagBacktrackWalk G e.symm d t) hswap2
  refine ⟨y2 - y1, ?_⟩
  simp_rw [heval]
  rw [sum_mul_sub_sub_eq, hcob, zero_sub, hy1, hy2]
  ring

end BacktrackParity

end TauCeti

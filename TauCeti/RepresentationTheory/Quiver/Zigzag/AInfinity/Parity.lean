/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.Obstruction.Invariance
public import TauCeti.RepresentationTheory.Quiver.Zigzag.AInfinity.WordPairing
import Mathlib.Algebra.Group.Subgroup.Even
import Mathlib.Algebra.Ring.Parity
import TauCeti.Algebra.BigOperators.Finset.Involution
import TauCeti.Data.List.ProdOfFn
import TauCeti.Logic.Equiv.Fin.Basic

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
shows that anticyclic word pairings satisfying the signless relations in even arity `2 m + 2`
(`m ≥ 1`) and symmetric, head-preserving, balanced backtrack pairings in arity four send the
quadratic sum to a multiple of `2`: hence on any formal minimal deformation of `Z` with
`m₃ = ⋯ = m_{2m+1} = 0` (respectively `m₃ = 0`), such a pairing sends the first obstruction into
the ideal `(2)`.
In particular, whenever such a pairing evaluates to a non-even element (for instance a unit when
`2` is not a unit) on a loop deformation, the deformation cannot be formal — complementing the
`ℚ`-algebra and `Invertible 2` criteria in `Invariance` and removing all characteristic restrictions
in arity four.

## Why the quadratic sum pairs to `2 k`

Two involutions combine without dividing by `2`:

1. **Dart reversal on squares of degree-one elements.** Because `ψ` has suspended degree zero, it
   maps every nonempty word of arrows to path length one. For any `u, v` with vanishing
   vertex-idempotent coordinates, expanding in the vertex-arrow-volume basis shows
   `tr(u * v) = ∑_d coord_d(u) * coord_{d.symm}(v)` (`TauCeti.zigzagTrace_mul_eq_sum_dart`). For
   `u = v`, the fixed-point-free involution `d ↦ d.symm` on `G.Dart` groups the sum into pairs of
   equal terms `coord_d(u) * coord_{d.symm}(u)`, so `tr(u * u) ∈ 2 k` over **every** commutative
   ring, including characteristic `2` (`TauCeti.even_zigzagTrace_mul_self`).
2. **Swapping the two blocks of a cut.** In even arity `2 m + 2`:
   * For `d ≠ m + 1`, cyclically shifting a word by `2 m + 2 - d` steps exchanges the `(d, 2m+2-d)`
     cut with the `(2m+2-d, d)` cut, commutes the two factors inside `tr`, and multiplies an
     anticyclic weight `a` by `(-1)^{2m+2-d}`, so the sum of the `d` and `2 m + 2 - d` contributions
     is `(1 + (-1)^{2m+2-d}) S_d`, which is either `2 S_d` or `0`.
   * At the midpoint `d = m + 1`, shifting a word by `m + 1` steps is an involution `τ` on words of
     length `2 m + 2`. Free `τ`-orbits contribute `(1 + (-1)^{m+1})` times one representative, while
     a `τ`-fixed word has two identical half-words, reducing its contribution to `tr(u * u) ∈ 2 k`.
   * For the quartic backtrack pairing `TauCeti.zigzagBacktrackPairing` with a symmetric weight
     matrix `a`, write `B d e` for the backtrack walk `TauCeti.zigzagBacktrackWalk G e.symm d`
     (`e, e.symm, d, d.symm`) and `B' d e` for its one-step rotation (`e.symm, d, d.symm, e`).
     Exchanging `(d, e) ↔ (e, d)` swaps the two halves of both `B d e` and `B' d e`, while diagonal
     pairs `(d, d)` have two identical halves and again reduce to `tr(u * u) ∈ 2 k`.

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
* R. S. Huerfano and M. Khovanov, *A category for the adjoint representation*, Sections 3 and 6.1,
  for the Frobenius trace and quadratic dual of a zigzag algebra.
-/

public section

namespace TauCeti

open PathAlgebra DoubledQuiver AInfinity ReducedTensorWords

universe u w

variable {k : Type w} [CommRing k] {V : Type u} {G : SimpleGraph V} [Finite V]
  {hns : ∀ i : V, ∃ j, G.Adj i j}

local notation "𝒵" => zigzagStrictAInfinityAlgebra k hns

local notation "𝔞" d:max => zigzagMk k G (ofArrow (arrow G (SimpleGraph.Dart.adj d)))

/-! ### Degree-one subwords and binary Taylor sign -/

section TraceParity

/-- For any homogeneous cochain `ψ` of suspended degree zero, the trace of the square of `ψ` on a
subword of arrows is even. -/
private theorem even_zigzagTrace_mul_self_apply_subword
    {ψ : ReducedTensorWords k (nonisolatedZigzagQuotient k G) →ₗ[k] nonisolatedZigzagQuotient k G}
    (hψ : LinearMap.IsHomogeneous ψ (gradedPiece ((𝒵).grading.shift 1))
      ((𝒵).grading.shift 1).piece 0)
    {N : ℕ} (w : Fin N → G.Dart) (p d : ℕ) :
    Even (zigzagTrace k G hns
      (ψ (subword k (fun t ↦ 𝔞 (w t)) p d) * ψ (subword k (fun t ↦ 𝔞 (w t)) p d))) :=
  even_zigzagTrace_mul_self k G hns fun i ↦
    zigzagBasis_coord_vertex_eq_zero_of_mem_zigzagIntegerGrade k G hns i one_ne_zero
      (zigzagStrictAInfinityAlgebra_apply_subword_mem_zigzagIntegerGrade_one hψ
        (fun _ ↦ zigzagMk_ofArrow_mem_zigzagIntegerGrade_one k G _) p d)

/-- For a homogeneous cochain `ψ` of suspended degree zero, the trace of the binary Taylor
operation of `𝒵` on two subwords of arrows is the negated trace of their product. -/
private theorem zigzagTrace_taylor_of_tprod_two_apply_subword
    {ψ : ReducedTensorWords k (nonisolatedZigzagQuotient k G) →ₗ[k] nonisolatedZigzagQuotient k G}
    (hψ : LinearMap.IsHomogeneous ψ (gradedPiece ((𝒵).grading.shift 1))
      ((𝒵).grading.shift 1).piece 0)
    {N : ℕ} (w : Fin N → G.Dart) (p₁ d₁ p₂ d₂ : ℕ) :
    zigzagTrace k G hns ((𝒵).taylor (of k _ (2 : ℕ+)
        (PiTensorProduct.tprod k
          ![ψ (subword k (fun t ↦ 𝔞 (w t)) p₁ d₁),
            ψ (subword k (fun t ↦ 𝔞 (w t)) p₂ d₂)]))) =
      -zigzagTrace k G hns
        (ψ (subword k (fun t ↦ 𝔞 (w t)) p₁ d₁) * ψ (subword k (fun t ↦ 𝔞 (w t)) p₂ d₂)) := by
  rw [AInfinityAlgebra.taylor_of_two, zigzagStrictAInfinityAlgebra_m_two_apply,
    (𝒵).grading.koszulTwist_one_apply_of_mem (e := 1)
      (by
        rw [zigzagStrictAInfinityAlgebra_grading_piece]
        exact zigzagStrictAInfinityAlgebra_apply_subword_mem_zigzagIntegerGrade_one hψ
          (fun _ ↦ zigzagMk_ofArrow_mem_zigzagIntegerGrade_one k G _) p₁ d₁)]
  simp

/-- A formal minimal `A∞` algebra with the grading and product of `𝒵` and vanishing operations in
arities `3, …, n + 1` admits a homogeneous cochain `ψ` of suspended degree zero decomposing the
trace of its obstruction `m_{n+2}` on arrow words into a Hochschild coboundary minus the quadratic
cut sum. -/
private theorem exists_obstruction_zigzagTrace_eq_sub_sum_of_isFormal
    {𝒜 : AInfinityAlgebra k (nonisolatedZigzagQuotient k G)} (h𝒜 : 𝒜.IsMinimal)
    (hG : 𝒜.grading = (𝒵).grading) (h₂ : 𝒜.m 2 = (𝒵).m 2) {n : ℕ}
    (hlow : ∀ r, 3 ≤ r → r ≤ n + 1 → 𝒜.m r = 0) (hF : 𝒜.IsFormal) :
    ∃ ψ : ReducedTensorWords k (nonisolatedZigzagQuotient k G) →ₗ[k] nonisolatedZigzagQuotient k G,
      LinearMap.IsHomogeneous ψ (gradedPiece ((𝒵).grading.shift 1))
          ((𝒵).grading.shift 1).piece 0 ∧
        ∀ w : Fin (n + 2) → G.Dart,
          zigzagTrace k G hns (𝒜.obstruction 𝒵 ⟨n + 2, by omega⟩
              (of k _ ⟨n + 2, by omega⟩ (PiTensorProduct.tprod k fun t ↦ 𝔞 (w t)))) =
            zigzagTrace k G hns ((𝒵).hochschildDifferential 0 ψ
              (of k _ ⟨n + 2, by omega⟩ (PiTensorProduct.tprod k fun t ↦ 𝔞 (w t)))) -
            ∑ d ∈ Finset.Icc 2 n, zigzagTrace k G hns
              (ψ (subword k (fun t ↦ 𝔞 (w t)) 0 d) *
                ψ (subword k (fun t ↦ 𝔞 (w t)) d (n + 2 - d))) := by
  have hm𝒵 : ∀ r, 3 ≤ r → (𝒵).m r = 0 := fun _ hr ↦
    zigzagStrictAInfinityAlgebra_m_eq_zero (by omega)
  have hZ := isMinimal_zigzagStrictAInfinityAlgebra (k := k) (hns := hns)
  obtain ⟨f, hf⟩ := (h𝒜.isFormal_iff_exists_isIso hZ hm𝒵 hG h₂).1 hF
  obtain ⟨ψ, hψ, -, hdec⟩ :=
    hZ.exists_obstruction_of_tprod_eq_hochschildDifferential_add_sum_of_isIso
      hm𝒵 hG h₂ (n := n) hlow hf
  refine ⟨ψ, hψ, fun w ↦ ?_⟩
  rw [hdec, map_add, map_sum,
    Finset.sum_congr rfl fun d _ ↦ zigzagTrace_taylor_of_tprod_two_apply_subword hψ w 0 d d
      (n + 2 - d),
    Finset.sum_neg_distrib, sub_eq_add_neg]

end TraceParity

/-! ### Cyclic shifts and even-arity word pairings -/

section WordParity

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
    { toFun := fun w ↦ w ∘ finCycle rFin
      invFun := fun w ↦ w ∘ (finCycle rFin).symm
      left_inv := fun w ↦ funext fun i ↦ by simp
      right_inv := fun w ↦ funext fun i ↦ by simp }
  rw [hsub, Finset.mul_sum, ← Equiv.sum_comp σ]
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  have hw : a (σ w) = (-1 : k) ^ d * a w :=
    apply_comp_finCycle_of_anticyclic hrot rFin w
  have hcomp : (fun t ↦ 𝔞 (σ w t)) = fun t ↦ 𝔞 (w (t + rFin)) :=
    funext fun t ↦ congrArg (fun i ↦ 𝔞 (w i)) (finCycle_apply rFin t)
  have hs0 := subword_shift_zero_eq k (fun t ↦ 𝔞 (w t)) rFin
  have hs1 := subword_shift_right_eq k (fun t ↦ 𝔞 (w t)) rFin
  dsimp only [rFin] at hs0 hs1 ⊢
  rw [hw, hcomp, hs0, hs1, zigzagTrace_mul_comm]
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
  rw [hsub, ← even_iff_exists_two_mul, ← AddSubmonoid.mem_even]
  let rFin : Fin (2 * m + 2) := ⟨m + 1, by omega⟩
  let τ : (Fin (2 * m + 2) → G.Dart) → (Fin (2 * m + 2) → G.Dart) := fun w ↦ w ∘ finCycle rFin
  have hτ (w : Fin (2 * m + 2) → G.Dart) : τ (τ w) = w := funext fun i ↦ congrArg w <| by
    have hsum : rFin.val + rFin.val = 2 * m + 2 := by dsimp [rFin]; omega
    have h0 : rFin + rFin = 0 := Fin.ext (by rw [Fin.val_add, Fin.val_zero, hsum, Nat.mod_self])
    rw [finCycle_apply, finCycle_apply, add_assoc, h0, add_zero]
  have hcomp (w : Fin (2 * m + 2) → G.Dart) :
      (fun t ↦ 𝔞 (τ w t)) = fun t ↦ 𝔞 (w (t + rFin)) :=
    funext fun t ↦ congrArg (fun i ↦ 𝔞 (w i)) (finCycle_apply rFin t)
  have hsw0 (w : Fin (2 * m + 2) → G.Dart) :
      subword k (fun t ↦ 𝔞 (τ w t)) 0 (m + 1) =
        subword k (fun t ↦ 𝔞 (w t)) (m + 1) (m + 1) := by
    rw [hcomp]
    simpa only [rFin, hsub] using subword_shift_zero_eq k (fun t ↦ 𝔞 (w t)) rFin
  have hsw1 (w : Fin (2 * m + 2) → G.Dart) :
      subword k (fun t ↦ 𝔞 (τ w t)) (m + 1) (m + 1) =
        subword k (fun t ↦ 𝔞 (w t)) 0 (m + 1) := by
    rw [hcomp]
    simpa only [rFin, hsub] using subword_shift_right_eq k (fun t ↦ 𝔞 (w t)) rFin
  refine Finset.sum_mem_of_involution Finset.univ τ (fun _ _ ↦ Finset.mem_univ _)
    (fun w _ ↦ hτ w) (fun w _ hw ↦ ?_) (fun w _ _ ↦ ?_)
  · have heq := (hsw0 w).symm
    rw [hw] at heq
    rw [AddSubmonoid.mem_even, heq]
    exact (even_zigzagTrace_mul_self_apply_subword hψ w 0 (m + 1)).mul_left _
  · have haτ : a (τ w) = (-1 : k) ^ (m + 1) * a w := apply_comp_finCycle_of_anticyclic hrot rFin w
    rw [AddSubmonoid.mem_even, haτ, hsw0, hsw1,
      zigzagTrace_mul_comm k G hns (ψ (subword k (fun t ↦ 𝔞 (w t)) (m + 1) _)),
      mul_assoc, ← one_add_mul]
    exact ((odd_neg_one (α := k)).pow (n := m + 1)).one_add.mul_right _

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
  rw [← even_iff_exists_two_mul, ← AddSubmonoid.mem_even]
  refine Finset.sum_mem_of_involution (Finset.Icc 2 (2 * m)) (f := S) (fun d ↦ 2 * m + 2 - d)
    (fun d hd ↦ Finset.mem_Icc.2 (by have := Finset.mem_Icc.1 hd; omega))
    (fun d hd ↦ by have := Finset.mem_Icc.1 hd; omega) (fun d hd hfix ↦ ?_) (fun d hd _ ↦ ?_)
  · have hmid : d = m + 1 := by have := Finset.mem_Icc.1 hd; omega
    rw [AddSubmonoid.mem_even, even_iff_exists_two_mul, hmid]
    exact exists_sum_word_cut_mid_eq_two_mul hrot hψ
  · have hd' := Finset.mem_Icc.1 hd
    have hS : S (2 * m + 2 - d) = (-1 : k) ^ d * S d :=
      sum_word_cut_sub_eq_neg_one_pow_mul hrot ψ (by omega)
    rw [AddSubmonoid.mem_even, hS, ← one_add_mul]
    exact ((odd_neg_one (α := k)).pow (n := d)).one_add.mul_right (S d)

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
  obtain ⟨ψ, hψ, heval⟩ := exists_obstruction_zigzagTrace_eq_sub_sum_of_isFormal h𝒜 hG h₂ hlow hF
  have hcob := zigzagWordPairing_hochschildDifferential_eq_zero (hns := hns) hrot hrel hψ
  rw [zigzagWordPairing_apply] at hcob ⊢
  simp_rw [heval, mul_sub, Finset.mul_sum, Finset.sum_sub_distrib, hcob, zero_sub]
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
      (𝒜.obstruction 𝒵 ⟨2 * m + 2, by omega⟩) = 2 * y :=
  exists_zigzagWordPairing_obstruction_eq_two_mul_of_isFormal h𝒜 hG h₂ hlow hF
    (List.apply_prod_ofFn_snoc β f hf)
    (fun p u v ↦ List.sum_apply_prod_ofFn_insertNth_insertNth β f _ id SimpleGraph.Dart.symm
      (hβ v) p u)

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
  rw [← Fintype.sum_prod_type', ← even_iff_exists_two_mul, ← AddSubmonoid.mem_even]
  have hsw0 (d e : G.Dart) :
      subword k (fun t ↦ 𝔞 (W e d t)) 0 2 = subword k (fun t ↦ 𝔞 (W d e t)) 2 2 := by
    rw [hW]
    exact subword_shift_zero_eq k (fun t ↦ 𝔞 (W d e t)) 2
  have hsw1 (d e : G.Dart) :
      subword k (fun t ↦ 𝔞 (W e d t)) 2 2 = subword k (fun t ↦ 𝔞 (W d e t)) 0 2 := by
    rw [hW]
    exact subword_shift_right_eq k (fun t ↦ 𝔞 (W d e t)) 2
  refine Finset.sum_mem_of_involution Finset.univ Prod.swap (fun _ _ ↦ Finset.mem_univ _)
    (fun p _ ↦ Prod.swap_swap p) (fun p _ hp ↦ ?_) (fun p _ _ ↦ ?_)
  · obtain ⟨d, e⟩ := p
    obtain rfl : d = e := (Prod.ext_iff.1 hp).2
    rw [AddSubmonoid.mem_even, ← hsw0 d d]
    exact (even_zigzagTrace_mul_self_apply_subword hψ (W d d) 0 2).mul_left _
  · obtain ⟨d, e⟩ := p
    rw [AddSubmonoid.mem_even]
    refine ⟨a d e * zigzagTrace k G hns
      (ψ (subword k (fun t ↦ 𝔞 (W d e t)) 0 2) * ψ (subword k (fun t ↦ 𝔞 (W d e t)) 2 2)), ?_⟩
    dsimp only [Prod.swap]
    rw [ha.apply d e, hsw0 d e, hsw1 d e,
      zigzagTrace_mul_comm k G hns (ψ (subword k (fun t ↦ 𝔞 (W d e t)) 2 2))]

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
  obtain ⟨ψ, hψ, heval⟩ := exists_obstruction_zigzagTrace_eq_sub_sum_of_isFormal h𝒜 hG h₂
    (n := 2) (fun r hr1 hr2 ↦ by obtain rfl : r = 3 := (by omega); exact h₃) hF
  have hcob := zigzagBacktrackPairing_hochschildDifferential_eq_zero (hns := hns) ha hhead hbal hψ
  rw [zigzagBacktrackPairing_apply] at hcob ⊢
  simp only [Finset.Icc_self, Finset.sum_singleton, Nat.add_sub_cancel] at heval
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
  simp_rw [mul_sub, Finset.sum_sub_distrib] at hcob
  simp_rw [heval, mul_sub, Finset.sum_sub_distrib]
  rw [sub_eq_zero.1 hcob, hy1, hy2]
  ring

end BacktrackParity

end TauCeti

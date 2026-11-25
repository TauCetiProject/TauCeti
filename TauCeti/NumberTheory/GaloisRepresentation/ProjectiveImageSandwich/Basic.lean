/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.ProjGenLinGroup.ProjectiveImage
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.CharAndCard

/-!
# The finite-field projective image condition

Let `k` be a finite field of cardinality `p ^ a`, mapped by `ι : k →+* K` into a commutative ring
`K` (in applications an algebraically closed field), and
let `ρ : G →* GL(2, K)` be a two-dimensional representation of a group `G`. The *projective image
sandwich condition* for `(p, a, n, ι, ρ)` says that `p` is prime, `n ≥ 1`, `#k = p ^ a` with the
strict bound `p ^ a > max(5, 2n - 1)`, and that some conjugate of the projective image of `ρ` lies
between the images of `PSL(2, k)` and of `PGL(2, k)` in `PGL(2, K)`:

`PSL(2, k) ≤ c (Pρ) c⁻¹ ≤ PGL(2, k)` for one `c ∈ PGL(2, K)`.

For `K` an algebraic closure of `𝔽_p` and `ρ` a residual Galois representation, this is the
image hypothesis of Newton–Thorne's Theorem 2.1 on symmetric power functoriality: up to
conjugation, the projective image of the residual representation lies between `PSL(2, k)` and
`PGL(2, k)` for a finite field `k` that is large compared with the rank `n` of the symmetric power
`Sym^{n-1}` under consideration. The condition asserts neither `p > n` nor any automorphy.

## Main declarations

* `TauCeti.IsProjectiveImageSandwich`: the condition.
* `TauCeti.IsProjectiveImageSandwich.max_lt_natCard`: the strict field-size bound
  `max 5 (2n - 1) < #k`, with its consequences `5 < #k` and `2n ≤ #k`.
* `TauCeti.IsProjectiveImageSandwich.one_le_exponent`: the exponent `a` is positive.
* `TauCeti.IsProjectiveImageSandwich.charP`, `TauCeti.IsProjectiveImageSandwich.charP_target`:
  `k`, and a nontrivial `K`, have characteristic `p`.
* `TauCeti.IsProjectiveImageSandwich.of_le`: the condition for `n` implies it for `1 ≤ m ≤ n`.
* `TauCeti.isProjectiveImageSandwich_conj_iff`: the condition is invariant under conjugating `ρ`
  by any element of `GL(2, K)`.
* `TauCeti.isProjectiveImageSandwich_map`: a representation `ρ₀` over `k` whose projective image
  contains `PSL(2, k)` satisfies the condition after extending scalars along `ι`.

## References

* James Newton and Jack A. Thorne, *Symmetric power functoriality for holomorphic modular forms,
  II*, Publ. Math. IHÉS 134 (2021), Theorem 2.1.
-/

public section

open scoped MatrixGroups Pointwise

open Matrix

namespace TauCeti

variable {G : Type*} [Group G] {k K : Type*} [Field k] [CommRing K]

/-- The *projective image sandwich condition* for `(p, a, n, ι, ρ)`: `p` is prime, `n ≥ 1`,
the field `k` has `p ^ a` elements with `p ^ a > max(5, 2n - 1)`, and for some `c ∈ PGL(2, K)`
the conjugate `c (Pρ) c⁻¹` of the projective image of `ρ` contains the image of `PSL(2, k)` and
is contained in the image of `PGL(2, k)`, both embedded into `PGL(2, K)` along `ι`. -/
structure IsProjectiveImageSandwich (p a n : ℕ) (ι : k →+* K) (ρ : G →* GL (Fin 2) K) :
    Prop where
  /-- The characteristic `p` is prime. -/
  prime : p.Prime
  /-- The rank `n` is positive. -/
  one_le_rank : 1 ≤ n
  /-- The field `k` has `p ^ a` elements. -/
  natCard_eq : Nat.card k = p ^ a
  /-- The strict field-size bound. -/
  max_lt_pow : max 5 (2 * n - 1) < p ^ a
  /-- Some conjugate of the projective image lies between `PSL(2, k)` and `PGL(2, k)`. -/
  exists_conj : ∃ c : PGL(2, K),
    ((ProjGenLinGroup.map ι).comp ProjectiveSpecialLinearGroup.toPGL).range ≤
        MulAut.conj c • ρ.projectiveImage ∧
      MulAut.conj c • ρ.projectiveImage ≤ (ProjGenLinGroup.map ι).range

namespace IsProjectiveImageSandwich

variable {p a n : ℕ} {ι : k →+* K} {ρ : G →* GL (Fin 2) K}

/-- The strict field-size bound `max(5, 2n - 1) < #k`. -/
theorem max_lt_natCard (h : IsProjectiveImageSandwich p a n ι ρ) :
    max 5 (2 * n - 1) < Nat.card k :=
  h.natCard_eq ▸ h.max_lt_pow

/-- The field `k` has more than five elements. -/
theorem five_lt_natCard (h : IsProjectiveImageSandwich p a n ι ρ) : 5 < Nat.card k :=
  (le_max_left _ _).trans_lt h.max_lt_natCard

/-- Since `n ≥ 1`, the bound `2n - 1 < #k` says `2n ≤ #k`. -/
theorem two_mul_le_natCard (h : IsProjectiveImageSandwich p a n ι ρ) : 2 * n ≤ Nat.card k := by
  have := (le_max_right _ _).trans_lt h.max_lt_natCard
  have := h.one_le_rank
  omega

/-- The exponent `a` is positive: `p ^ 0 = 1` violates the field-size bound. -/
theorem one_le_exponent (h : IsProjectiveImageSandwich p a n ι ρ) : 1 ≤ a :=
  Nat.one_le_iff_ne_zero.2 fun ha ↦ by simpa [ha] using h.max_lt_pow

/-- The field `k` is finite. -/
theorem finite (h : IsProjectiveImageSandwich p a n ι ρ) : Finite k :=
  Nat.finite_of_card_ne_zero (by have := h.five_lt_natCard; omega)

/-- The field `k` has characteristic `p`. -/
theorem charP (h : IsProjectiveImageSandwich p a n ι ρ) : CharP k p := by
  have := h.finite
  have : Fact p.Prime := ⟨h.prime⟩
  have := Fintype.ofFinite k
  exact charP_of_card_eq_prime_pow (by rw [Fintype.card_eq_nat_card, h.natCard_eq])

/-- A nontrivial ring `K` receiving `ι` has characteristic `p`. Over the zero ring every
subgroup of `PGL(2, K)` is trivial, so the condition holds there while `CharP K p` fails. -/
theorem charP_target [Nontrivial K] (h : IsProjectiveImageSandwich p a n ι ρ) : CharP K p :=
  have := h.charP
  charP_of_injective_ringHom ι.injective p

/-- The condition for rank `n` implies the condition for every rank `1 ≤ m ≤ n`. -/
theorem of_le (h : IsProjectiveImageSandwich p a n ι ρ) {m : ℕ} (hmn : m ≤ n) (hm : 1 ≤ m) :
    IsProjectiveImageSandwich p a m ι ρ where
  prime := h.prime
  one_le_rank := hm
  natCard_eq := h.natCard_eq
  max_lt_pow := lt_of_le_of_lt (max_le_max le_rfl (by omega)) h.max_lt_pow
  exists_conj := h.exists_conj

end IsProjectiveImageSandwich

/-- Over a field with at most five elements the condition never holds. -/
theorem not_isProjectiveImageSandwich_of_natCard_le_five (hk : Nat.card k ≤ 5) {p a n : ℕ}
    (ι : k →+* K) (ρ : G →* GL (Fin 2) K) : ¬ IsProjectiveImageSandwich p a n ι ρ :=
  fun h ↦ (h.five_lt_natCard.trans_le hk).false

/-- The condition is invariant under conjugating `ρ` by an element of `GL(2, K)`. -/
theorem isProjectiveImageSandwich_conj_iff {p a n : ℕ} {ι : k →+* K} {ρ : G →* GL (Fin 2) K}
    (g : GL (Fin 2) K) :
    IsProjectiveImageSandwich p a n ι ((MulAut.conj g : GL (Fin 2) K →* GL (Fin 2) K).comp ρ) ↔
      IsProjectiveImageSandwich p a n ι ρ := by
  have key (c : PGL(2, K)) : MulAut.conj c •
      ((MulAut.conj g : GL (Fin 2) K →* GL (Fin 2) K).comp ρ).projectiveImage =
      MulAut.conj (c * ProjGenLinGroup.mk g) • ρ.projectiveImage := by
    rw [MonoidHom.projectiveImage_conj, map_mul, mul_smul]
  refine ⟨fun ⟨hp, hn, hk, hb, c, hc⟩ ↦ ⟨hp, hn, hk, hb, c * ProjGenLinGroup.mk g, key c ▸ hc⟩,
    fun ⟨hp, hn, hk, hb, c, hc⟩ ↦ ⟨hp, hn, hk, hb, c * (ProjGenLinGroup.mk g)⁻¹, ?_⟩⟩
  rwa [key, inv_mul_cancel_right]

/-- A representation `ρ₀ : G →* GL(2, k)` whose projective image contains `PSL(2, k)` satisfies
the condition after extending scalars along `ι`, as soon as `k` satisfies the numerical part of
the condition; the conjugating element can be taken to be `1`. -/
theorem isProjectiveImageSandwich_map {p a n : ℕ} (hp : p.Prime) (hn : 1 ≤ n)
    (hk : Nat.card k = p ^ a) (hb : max 5 (2 * n - 1) < p ^ a) (ι : k →+* K)
    {ρ₀ : G →* GL (Fin 2) k} (hρ₀ : ProjectiveSpecialLinearGroup.toPGL.range ≤ ρ₀.projectiveImage) :
    IsProjectiveImageSandwich p a n ι ((GeneralLinearGroup.map ι).comp ρ₀) := by
  refine ⟨hp, hn, hk, hb, 1, ?_⟩
  rw [map_one, one_smul, MonoidHom.projectiveImage_map, MonoidHom.range_comp]
  exact ⟨Subgroup.map_mono hρ₀, Subgroup.map_le_range _ _⟩

/-- Extension of scalars `GL(2, k) →* GL(2, K)` along `ι` satisfies the condition as soon as `k`
satisfies its numerical part. -/
theorem isProjectiveImageSandwich_generalLinearGroupMap {p a n : ℕ} (hp : p.Prime) (hn : 1 ≤ n)
    (hk : Nat.card k = p ^ a) (hb : max 5 (2 * n - 1) < p ^ a) (ι : k →+* K) :
    IsProjectiveImageSandwich p a n ι (GeneralLinearGroup.map (n := Fin 2) ι) := by
  simpa using isProjectiveImageSandwich_map hp hn hk hb ι (ρ₀ := MonoidHom.id _)
    (by rw [MonoidHom.projectiveImage_eq_top_of_surjective Function.surjective_id]; exact le_top)

end TauCeti

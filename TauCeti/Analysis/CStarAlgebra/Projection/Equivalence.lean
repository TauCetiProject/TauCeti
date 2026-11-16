/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Unitization
public import TauCeti.Algebra.Star.PartialIsometry
public import TauCeti.Analysis.CStarAlgebra.CStarMatrix.Block

import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
import TauCeti.Analysis.CStarAlgebra.Projection.Nearby
import TauCeti.Data.Matrix.Block

/-!
# Murray–von Neumann equivalence of matrix projections

For star projections `p : CStarMatrix m m A` and `q : CStarMatrix n n A` of possibly different
finite sizes, **Murray–von Neumann equivalence** `CStarMatrix.MurrayVonNeumannEquiv p q` holds
when there exists a rectangular matrix `v : CStarMatrix n m A` with `vᴴ * v = p` and
`v * vᴴ = q`.

This file develops the theory of rectangular Murray–von Neumann equivalence over star rings and
C⋆-algebras (both unital and non-unital):

1. **Equivalence relation and partial isometries.** Over a proper star-ordered ring, `vᴴ * v = p`
   with `p` idempotent implies `v * p = v` and `q * v = v`; hence Murray–von Neumann equivalence
   preserves `IsStarProjection` and is reflexive, symmetric, and transitive on projections. For
   square matrices `m = n`, the implementing elements are precisely `TauCeti.IsPartialIsometry`.
2. **Block sums, orthogonal sums, zero-padding, reindexing, unitary conjugacy, and functoriality.**
   Equivalence is compatible with block-diagonal sums, same-size orthogonal sums, zero-padding on
   either side, arbitrary finite reindexing (yielding commutativity and associativity of block sums
   even for non-unital `A`), unitary conjugacy (in `CStarMatrix n n A`, `(CStarMatrix n n A)⁺¹`, or
   `CStarMatrix n n A⁺¹`), and star-homomorphisms.
3. **Algebraic equivalence implies Murray–von Neumann equivalence.** If `x * y = p` and `y * x = q`
   for rectangular matrices over a C⋆-algebra `A`, then `p` and `q` are Murray–von Neumann
   equivalent (Blackadar, Proposition 4.6.4).
4. **Paths and stabilized unitary conjugacy.** Endpoints of a norm-continuous path of matrix
   projections are Murray–von Neumann equivalent. Conversely, if `p` and `q` are Murray–von
   Neumann equivalent via `v`, the self-adjoint unitary `w = [[1 - p, vᴴ], [v, 1 - q]]` conjugates
   `p ⊕ 0` to `0 ⊕ q` and satisfies `w = expUnitary ((π : ℂ) • ((2 : ℂ)⁻¹ • (1 - w)))`, giving a
   unitary in the identity path component and an explicit continuous path of projections in
   `CStarMatrix (m ⊕ n) (m ⊕ n) A` (and, when `m = n`, composing with the `π / 2` block rotation
   yields a path from `p ⊕ 0` to `q ⊕ 0`).

## Main definitions

* `CStarMatrix.MurrayVonNeumannEquiv`: rectangular Murray–von Neumann equivalence `vᴴ * v = p` and
  `v * vᴴ = q`.
* `CStarMatrix.stabilizedUnitary`: the self-adjoint unitary `[[1 - p, vᴴ], [v, 1 - q]]` witnessing
  stabilized unitary conjugacy of `p ⊕ 0` and `0 ⊕ q`.

## Main results

* `CStarMatrix.MurrayVonNeumannEquiv.refl`, `.symm`, `.trans`: equivalence relation on star
  projections.
* `CStarMatrix.murrayVonNeumannEquiv_iff_exists_isPartialIsometry`: characterization for square
  matrices via `TauCeti.IsPartialIsometry`.
* `CStarMatrix.MurrayVonNeumannEquiv.fromBlocks_zero₁₂_zero₂₁`, `.add`, `.fromBlocks_zero_right`,
  `.fromBlocks_zero_left`, `.reindexₐ`, `.fromBlocks_comm`, `.fromBlocks_assoc`: compatibility with
  block and orthogonal operations.
* `CStarMatrix.MurrayVonNeumannEquiv.of_unitary_conj`, `.of_unitization_unitary_conj`,
  `.of_matrix_unitization_unitary_conj`, `.map`, `.mapₙₐ`, `.mapₐ`: unitary conjugacy and
  functoriality.
* `CStarMatrix.MurrayVonNeumannEquiv.of_mul_eq`: rectangular algebraic equivalence of star
  projections implies Murray–von Neumann equivalence.
* `CStarMatrix.MurrayVonNeumannEquiv.of_path`, `.of_norm_sub_lt_one`: continuous paths and nearby
  projections imply Murray–von Neumann equivalence.
* `CStarMatrix.stabilizedUnitary_conj`, `CStarMatrix.joined_one_stabilizedUnitary`,
  `CStarMatrix.MurrayVonNeumannEquiv.exists_stabilized_unitary_conj`,
  `.exists_stabilized_unitary_conj_same`, `.exists_path_fromBlocks_zero_left`,
  `.exists_path_fromBlocks_zero_right`: stabilized unitary conjugacy in the identity path component
  and continuous paths of projections.

## References

* Bruce Blackadar, *K-Theory for Operator Algebras*, 2nd ed., MSRI Publications 5,
  Cambridge University Press, 1998, Section 4.6 (Definition 4.6.1 and Propositions 4.6.2–4.6.6).
-/

public section

open scoped CStarAlgebra ComplexOrder NNReal Real unitInterval Ring

namespace CStarMatrix

private theorem map_inr_map_snd_of_map_fstHom_eq_zero {m n A : Type*}
    [NonUnitalSemiring A] [Module ℂ A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
    {M : CStarMatrix m n A⁺¹} (hM : M.map (Unitization.fstHom ℂ A) = 0) :
    (M.map (fun x : A⁺¹ => x.snd)).map (Unitization.inr : A → A⁺¹) = M := by
  refine CStarMatrix.ext fun i j => Unitization.ext ?_ rfl
  have h := congrArg (fun X : CStarMatrix m n ℂ => X i j) hM
  simpa using h.symm

/-! ### Definition and basic properties -/

section Basic

variable {l m n A : Type*}

/-- Two square C⋆-matrices `p : CStarMatrix m m A` and `q : CStarMatrix n n A` (of possibly
different finite sizes) are **Murray–von Neumann equivalent** if there exists a rectangular matrix
`v : CStarMatrix n m A` with `vᴴ * v = p` and `v * vᴴ = q`. -/
def MurrayVonNeumannEquiv [Fintype m] [Fintype n] [NonUnitalNonAssocSemiring A] [Star A]
    (p : CStarMatrix m m A) (q : CStarMatrix n n A) : Prop :=
  ∃ v : CStarMatrix n m A, v.conjTranspose * v = p ∧ v * v.conjTranspose = q

/-- A star projection is Murray–von Neumann equivalent to itself. -/
theorem MurrayVonNeumannEquiv.refl [Fintype m] [NonUnitalNonAssocSemiring A] [Star A]
    {p : CStarMatrix m m A} (hp : IsStarProjection p) : p.MurrayVonNeumannEquiv p :=
  ⟨p,
    by simpa only [← star_eq_conjTranspose, hp.isSelfAdjoint.star_eq] using hp.isIdempotentElem.eq,
    by simpa only [← star_eq_conjTranspose, hp.isSelfAdjoint.star_eq] using hp.isIdempotentElem.eq⟩

/-- Murray–von Neumann equivalence is symmetric. -/
theorem MurrayVonNeumannEquiv.symm [Fintype m] [Fintype n] [NonUnitalNonAssocSemiring A]
    [InvolutiveStar A] {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    (h : p.MurrayVonNeumannEquiv q) : q.MurrayVonNeumannEquiv p := by
  obtain ⟨v, hv₁, hv₂⟩ := h
  exact ⟨v.conjTranspose, by rwa [conjTranspose_conjTranspose],
    by rwa [conjTranspose_conjTranspose]⟩

/-- In a proper star-ordered ring, if `vᴴ * v` is idempotent, then `v * (vᴴ * v) = v`. -/
theorem mul_conjTranspose_mul_self_of_isIdempotentElem [Fintype m] [Fintype n]
    [PartialOrder A] [NonUnitalRing A] [StarRing A] [StarOrderedRing A] [IsProperStar A]
    {v : CStarMatrix n m A} (hp : IsIdempotentElem (v.conjTranspose * v)) :
    v * (v.conjTranspose * v) = v := by
  set p := v.conjTranspose * v
  have hps : p.conjTranspose = p := by
    simp only [p, conjTranspose_mul, conjTranspose_conjTranspose]
  have hpp : p * p = p := hp.eq
  have h1 : p * v.conjTranspose * (v * p) = p * p * p := by
    rw [CStarMatrix.mul_assoc p v.conjTranspose (v * p),
      ← CStarMatrix.mul_assoc v.conjTranspose v p, ← CStarMatrix.mul_assoc p p p]
  have h2 : p * v.conjTranspose * v = p * p := by
    rw [CStarMatrix.mul_assoc p v.conjTranspose v]
  have h3 : v.conjTranspose * (v * p) = p * p := by
    rw [← CStarMatrix.mul_assoc v.conjTranspose v p]
  have hzero : (v * p - v).conjTranspose * (v * p - v) = 0 := by
    calc (v * p - v).conjTranspose * (v * p - v)
        = (p * v.conjTranspose - v.conjTranspose) * (v * p - v) := by
          rw [conjTranspose_sub, conjTranspose_mul, hps]
      _ = (p * v.conjTranspose * (v * p) - p * v.conjTranspose * v) -
            (v.conjTranspose * (v * p) - v.conjTranspose * v) := by
          rw [CStarMatrix.sub_mul, CStarMatrix.mul_sub, CStarMatrix.mul_sub]
      _ = (p * p * p - p * p) - (p * p - p) := by rw [h1, h2, h3]
      _ = 0 := by rw [hpp, hpp, sub_self]
  exact sub_eq_zero.mp (conjTranspose_mul_self_eq_zero.mp hzero)

/-- If `vᴴ * v = p` and `v * vᴴ = q` with `p` idempotent over a proper star-ordered ring, then
`v * p = v`, `q * v = v`, `p * vᴴ = vᴴ`, and `vᴴ * q = vᴴ`. -/
theorem mul_eq_self_of_conjTranspose_mul_self [Fintype m] [Fintype n]
    [PartialOrder A] [NonUnitalRing A] [StarRing A] [StarOrderedRing A] [IsProperStar A]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A} {v : CStarMatrix n m A}
    (hv₁ : v.conjTranspose * v = p) (hv₂ : v * v.conjTranspose = q) (hp : IsIdempotentElem p) :
    v * p = v ∧ q * v = v ∧ p * v.conjTranspose = v.conjTranspose ∧
      v.conjTranspose * q = v.conjTranspose := by
  have hvp : v * p = v := by
    rw [← hv₁]
    exact mul_conjTranspose_mul_self_of_isIdempotentElem (hv₁.symm ▸ hp)
  have hqv : q * v = v := by
    rw [← hv₂, CStarMatrix.mul_assoc, hv₁, hvp]
  have hps : p.conjTranspose = p := by
    rw [← hv₁, conjTranspose_mul, conjTranspose_conjTranspose]
  have hqs : q.conjTranspose = q := by
    rw [← hv₂, conjTranspose_mul, conjTranspose_conjTranspose]
  have hpv : p * v.conjTranspose = v.conjTranspose := by
    have := congrArg conjTranspose hvp
    simpa only [conjTranspose_mul, hps] using this
  have hvq : v.conjTranspose * q = v.conjTranspose := by
    have := congrArg conjTranspose hqv
    simpa only [conjTranspose_mul, hqs] using this
  exact ⟨hvp, hqv, hpv, hvq⟩

/-- Murray–von Neumann equivalence preserves star projections (right endpoint). -/
theorem MurrayVonNeumannEquiv.isStarProjection_right [Fintype m] [Fintype n]
    [PartialOrder A] [NonUnitalRing A] [StarRing A] [StarOrderedRing A] [IsProperStar A]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    (h : p.MurrayVonNeumannEquiv q) (hp : IsStarProjection p) : IsStarProjection q := by
  obtain ⟨v, hv₁, hv₂⟩ := h
  obtain ⟨hvp, -, -, -⟩ := mul_eq_self_of_conjTranspose_mul_self hv₁ hv₂ hp.isIdempotentElem
  refine ⟨?_, ?_⟩
  · rw [IsIdempotentElem]
    calc q * q = (v * v.conjTranspose) * (v * v.conjTranspose) := by rw [hv₂]
      _ = v * (v.conjTranspose * v) * v.conjTranspose := by
        rw [CStarMatrix.mul_assoc, ← CStarMatrix.mul_assoc v.conjTranspose v,
          ← CStarMatrix.mul_assoc v (v.conjTranspose * v)]
      _ = v * v.conjTranspose := by rw [hv₁, hvp]
      _ = q := hv₂
  · rw [isSelfAdjoint_iff, star_eq_conjTranspose, ← hv₂, conjTranspose_mul,
      conjTranspose_conjTranspose]

/-- Murray–von Neumann equivalence preserves star projections (left endpoint). -/
theorem MurrayVonNeumannEquiv.isStarProjection_left [Fintype m] [Fintype n]
    [PartialOrder A] [NonUnitalRing A] [StarRing A] [StarOrderedRing A] [IsProperStar A]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    (h : p.MurrayVonNeumannEquiv q) (hq : IsStarProjection q) : IsStarProjection p :=
  h.symm.isStarProjection_right hq

/-- Murray–von Neumann equivalent matrices are either both star projections or neither. -/
theorem MurrayVonNeumannEquiv.isStarProjection_iff [Fintype m] [Fintype n]
    [PartialOrder A] [NonUnitalRing A] [StarRing A] [StarOrderedRing A] [IsProperStar A]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    (h : p.MurrayVonNeumannEquiv q) : IsStarProjection p ↔ IsStarProjection q :=
  ⟨h.isStarProjection_right, h.isStarProjection_left⟩

/-- Murray–von Neumann equivalence is transitive on star projections. -/
theorem MurrayVonNeumannEquiv.trans [Fintype l] [Fintype m] [Fintype n]
    [PartialOrder A] [NonUnitalRing A] [StarRing A] [StarOrderedRing A] [IsProperStar A]
    {p : CStarMatrix l l A} {q : CStarMatrix m m A} {r : CStarMatrix n n A}
    (h₁ : p.MurrayVonNeumannEquiv q) (h₂ : q.MurrayVonNeumannEquiv r)
    (hp : IsStarProjection p) : p.MurrayVonNeumannEquiv r := by
  have hq : IsStarProjection q := h₁.isStarProjection_right hp
  obtain ⟨v, hv₁, hv₂⟩ := h₁
  obtain ⟨w, hw₁, hw₂⟩ := h₂
  obtain ⟨-, hqv, -, -⟩ := mul_eq_self_of_conjTranspose_mul_self hv₁ hv₂ hp.isIdempotentElem
  obtain ⟨hwq, -, -, -⟩ := mul_eq_self_of_conjTranspose_mul_self hw₁ hw₂ hq.isIdempotentElem
  refine ⟨w * v, ?_, ?_⟩
  · rw [conjTranspose_mul, CStarMatrix.mul_assoc, ← CStarMatrix.mul_assoc w.conjTranspose w v,
      hw₁, hqv, hv₁]
  · rw [conjTranspose_mul, CStarMatrix.mul_assoc, ← CStarMatrix.mul_assoc v v.conjTranspose,
      hv₂, ← CStarMatrix.mul_assoc w q w.conjTranspose, hwq, hw₂]

/-- The initial and final projections of a square partial isometry are Murray–von Neumann
equivalent star projections. -/
theorem MurrayVonNeumannEquiv.of_isPartialIsometry [Fintype n] [NonUnitalSemiring A] [StarRing A]
    {v : CStarMatrix n n A} (hv : TauCeti.IsPartialIsometry v) :
    (star v * v).MurrayVonNeumannEquiv (v * star v) ∧
      IsStarProjection (star v * v) ∧ IsStarProjection (v * star v) :=
  ⟨⟨v, by simp [star_eq_conjTranspose]⟩,
    hv.isStarProjection_star_mul_self, hv.isStarProjection_mul_star_self⟩

/-- For square matrices over a proper star-ordered ring, Murray–von Neumann equivalence of star
projections is witnessed precisely by partial isometries `TauCeti.IsPartialIsometry`. -/
theorem murrayVonNeumannEquiv_iff_exists_isPartialIsometry [Fintype n]
    [PartialOrder A] [NonUnitalRing A] [StarRing A] [StarOrderedRing A] [IsProperStar A]
    {p q : CStarMatrix n n A} (hp : IsStarProjection p) :
    p.MurrayVonNeumannEquiv q ↔
      ∃ v : CStarMatrix n n A, TauCeti.IsPartialIsometry v ∧ star v * v = p ∧ v * star v = q := by
  constructor
  · rintro ⟨v, hv₁, hv₂⟩
    obtain ⟨hvp, -, -, -⟩ := mul_eq_self_of_conjTranspose_mul_self hv₁ hv₂ hp.isIdempotentElem
    refine ⟨v, ?_, by simpa only [star_eq_conjTranspose] using hv₁,
      by simpa only [star_eq_conjTranspose] using hv₂⟩
    rw [TauCeti.isPartialIsometry_iff, star_eq_conjTranspose, CStarMatrix.mul_assoc, hv₁, hvp]
  · rintro ⟨v, -, hv₁, hv₂⟩
    exact ⟨v, by simpa only [← star_eq_conjTranspose] using hv₁,
      by simpa only [← star_eq_conjTranspose] using hv₂⟩

end Basic

/-! ### Block sums, orthogonal sums, zero-padding, reindexing, conjugacy, and functoriality -/

section Compatibility

variable {m₁ m₂ m₃ n₁ n₂ m n R A B : Type*}

/-- Murray–von Neumann equivalence is compatible with block-diagonal direct sums. -/
theorem MurrayVonNeumannEquiv.fromBlocks_zero₁₂_zero₂₁ [Fintype m₁] [Fintype m₂]
    [Fintype n₁] [Fintype n₂] [NonUnitalNonAssocSemiring A] [StarAddMonoid A]
    {p₁ : CStarMatrix m₁ m₁ A} {p₂ : CStarMatrix m₂ m₂ A}
    {q₁ : CStarMatrix n₁ n₁ A} {q₂ : CStarMatrix n₂ n₂ A}
    (h₁ : p₁.MurrayVonNeumannEquiv q₁) (h₂ : p₂.MurrayVonNeumannEquiv q₂) :
    (fromBlocks p₁ 0 0 p₂).MurrayVonNeumannEquiv (fromBlocks q₁ 0 0 q₂) := by
  obtain ⟨v₁, hv₁, hw₁⟩ := h₁
  obtain ⟨v₂, hv₂, hw₂⟩ := h₂
  refine ⟨fromBlocks v₁ 0 0 v₂, ?_, ?_⟩ <;> simp [hv₁, hw₁, hv₂, hw₂]

/-- Murray–von Neumann equivalence is compatible with sums of orthogonal star projections. -/
theorem MurrayVonNeumannEquiv.add [Fintype m] [Fintype n]
    [PartialOrder A] [NonUnitalRing A] [StarRing A] [StarOrderedRing A] [IsProperStar A]
    {p₁ p₂ : CStarMatrix m m A} {q₁ q₂ : CStarMatrix n n A}
    (h₁ : p₁.MurrayVonNeumannEquiv q₁) (h₂ : p₂.MurrayVonNeumannEquiv q₂)
    (hp₁ : IsStarProjection p₁) (hp₂ : IsStarProjection p₂)
    (hp : p₁ * p₂ = 0) (hq : q₁ * q₂ = 0) :
    (p₁ + p₂).MurrayVonNeumannEquiv (q₁ + q₂) := by
  obtain ⟨v₁, hv₁, hw₁⟩ := h₁
  obtain ⟨v₂, hv₂, hw₂⟩ := h₂
  obtain ⟨hv₁p, -, -, hv₁q⟩ := mul_eq_self_of_conjTranspose_mul_self hv₁ hw₁ hp₁.isIdempotentElem
  obtain ⟨-, hq₂v, hp₂v, -⟩ := mul_eq_self_of_conjTranspose_mul_self hv₂ hw₂ hp₂.isIdempotentElem
  have h12 : v₁.conjTranspose * v₂ = 0 := by
    calc v₁.conjTranspose * v₂ = (v₁.conjTranspose * q₁) * (q₂ * v₂) := by rw [hv₁q, hq₂v]
      _ = v₁.conjTranspose * (q₁ * q₂) * v₂ := by
        rw [CStarMatrix.mul_assoc, ← CStarMatrix.mul_assoc q₁ q₂,
          ← CStarMatrix.mul_assoc v₁.conjTranspose (q₁ * q₂)]
      _ = 0 := by rw [hq, CStarMatrix.mul_zero, CStarMatrix.zero_mul]
  have h21 : v₂.conjTranspose * v₁ = 0 := by
    simpa only [conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_zero] using
      congrArg conjTranspose h12
  have h12' : v₁ * v₂.conjTranspose = 0 := by
    calc v₁ * v₂.conjTranspose = (v₁ * p₁) * (p₂ * v₂.conjTranspose) := by rw [hv₁p, hp₂v]
      _ = v₁ * (p₁ * p₂) * v₂.conjTranspose := by
        rw [CStarMatrix.mul_assoc, ← CStarMatrix.mul_assoc p₁ p₂,
          ← CStarMatrix.mul_assoc v₁ (p₁ * p₂)]
      _ = 0 := by rw [hp, CStarMatrix.mul_zero, CStarMatrix.zero_mul]
  have h21' : v₂ * v₁.conjTranspose = 0 := by
    simpa only [conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_zero] using
      congrArg conjTranspose h12'
  refine ⟨v₁ + v₂, ?_, ?_⟩
  · rw [conjTranspose_add, CStarMatrix.add_mul, CStarMatrix.mul_add, CStarMatrix.mul_add,
      hv₁, hv₂, h12, h21, add_zero, zero_add]
  · rw [conjTranspose_add, CStarMatrix.add_mul, CStarMatrix.mul_add, CStarMatrix.mul_add,
      hw₁, hw₂, h12', h21', add_zero, zero_add]

/-- A star projection is Murray–von Neumann equivalent to its upper-left zero-padded block
`fromBlocks p 0 0 0` (without requiring `A` to be unital). -/
theorem MurrayVonNeumannEquiv.fromBlocks_zero_right [Fintype m] [Fintype n]
    [NonUnitalNonAssocSemiring A] [StarAddMonoid A]
    {p : CStarMatrix m m A} (hp : IsStarProjection p) :
    p.MurrayVonNeumannEquiv (fromBlocks p 0 0 (0 : CStarMatrix n n A)) := by
  have hps : p.conjTranspose = p := by
    simpa only [← star_eq_conjTranspose] using hp.isSelfAdjoint.star_eq
  have hpp : p * p = p := hp.isIdempotentElem.eq
  let v : CStarMatrix (m ⊕ n) m A :=
    ofMatrix (Matrix.of fun i j => Sum.elim (fun i₁ => p i₁ j) (fun _ => 0) i)
  refine ⟨v, ?_, ?_⟩
  · ext i j
    change ∑ k : m ⊕ n, star (v k i) * v k j = p i j
    rw [Fintype.sum_sum_type]
    have h0 : ∑ k : n, star (0 : A) * 0 = 0 := by simp
    have h1 : ∑ k : m, star (p k i) * p k j = p i j := by
      have hpp' : p.conjTranspose * p = p := by rw [hps, hpp]
      exact congrArg (fun M : CStarMatrix m m A => M i j) hpp'
    simpa only [v, ofMatrix_apply, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr, h0, add_zero]
      using h1
  · have hpp' : p * p.conjTranspose = p := by rw [hps, hpp]
    ext (i | i) (j | j)
    · rw [fromBlocks_apply₁₁]
      change ∑ k : m, v (Sum.inl i) k * star (v (Sum.inl j) k) = p i j
      have h1 : ∑ k : m, p i k * star (p j k) = p i j :=
        congrArg (fun M : CStarMatrix m m A => M i j) hpp'
      simpa only [v, ofMatrix_apply, Matrix.of_apply, Sum.elim_inl] using h1
    · rw [fromBlocks_apply₁₂]
      change ∑ k : m, v (Sum.inl i) k * star (v (Sum.inr j) k) = 0
      simp [v]
    · rw [fromBlocks_apply₂₁]
      change ∑ k : m, v (Sum.inr i) k * star (v (Sum.inl j) k) = 0
      simp [v]
    · rw [fromBlocks_apply₂₂]
      change ∑ k : m, v (Sum.inr i) k * star (v (Sum.inr j) k) = 0
      simp [v]

/-- A star projection is Murray–von Neumann equivalent to its lower-right zero-padded block
`fromBlocks 0 0 0 p` (without requiring `A` to be unital). -/
theorem MurrayVonNeumannEquiv.fromBlocks_zero_left [Fintype m] [Fintype n]
    [NonUnitalNonAssocSemiring A] [StarAddMonoid A]
    {p : CStarMatrix n n A} (hp : IsStarProjection p) :
    p.MurrayVonNeumannEquiv (fromBlocks (0 : CStarMatrix m m A) 0 0 p) := by
  have hps : p.conjTranspose = p := by
    simpa only [← star_eq_conjTranspose] using hp.isSelfAdjoint.star_eq
  have hpp : p * p = p := hp.isIdempotentElem.eq
  let v : CStarMatrix (m ⊕ n) n A :=
    ofMatrix (Matrix.of fun i j => Sum.elim (fun _ => 0) (fun i₂ => p i₂ j) i)
  refine ⟨v, ?_, ?_⟩
  · ext i j
    change ∑ k : m ⊕ n, star (v k i) * v k j = p i j
    rw [Fintype.sum_sum_type]
    have h0 : ∑ k : m, star (0 : A) * 0 = 0 := by simp
    have h1 : ∑ k : n, star (p k i) * p k j = p i j := by
      have hpp' : p.conjTranspose * p = p := by rw [hps, hpp]
      exact congrArg (fun M : CStarMatrix n n A => M i j) hpp'
    simpa only [v, ofMatrix_apply, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr, h0, zero_add]
      using h1
  · have hpp' : p * p.conjTranspose = p := by rw [hps, hpp]
    ext (i | i) (j | j)
    · rw [fromBlocks_apply₁₁]
      change ∑ k : n, v (Sum.inl i) k * star (v (Sum.inl j) k) = 0
      simp [v]
    · rw [fromBlocks_apply₁₂]
      change ∑ k : n, v (Sum.inl i) k * star (v (Sum.inr j) k) = 0
      simp [v]
    · rw [fromBlocks_apply₂₁]
      change ∑ k : n, v (Sum.inr i) k * star (v (Sum.inl j) k) = 0
      simp [v]
    · rw [fromBlocks_apply₂₂]
      change ∑ k : n, v (Sum.inr i) k * star (v (Sum.inr j) k) = p i j
      have h1 : ∑ k : n, p i k * star (p j k) = p i j :=
        congrArg (fun M : CStarMatrix n n A => M i j) hpp'
      simpa only [v, ofMatrix_apply, Matrix.of_apply, Sum.elim_inr] using h1

/-- Reindexing a star projection along any equivalence of finite index types yields a
Murray–von Neumann equivalent projection (without requiring `A` to be unital). -/
theorem MurrayVonNeumannEquiv.reindexₐ [Fintype m] [Fintype n] [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [Star A]
    (e : m ≃ n) {p : CStarMatrix m m A} (hp : IsStarProjection p) :
    p.MurrayVonNeumannEquiv (CStarMatrix.reindexₐ R A e p) := by
  have hps : p.conjTranspose = p := by
    simpa only [← star_eq_conjTranspose] using hp.isSelfAdjoint.star_eq
  have hpp : p * p = p := hp.isIdempotentElem.eq
  let v : CStarMatrix n m A := ofMatrix (Matrix.of fun i j => p (e.symm i) j)
  refine ⟨v, ?_, ?_⟩
  · ext i j
    change ∑ k : n, star (p (e.symm k) i) * p (e.symm k) j = p i j
    rw [Equiv.sum_comp e.symm (fun k => star (p k i) * p k j)]
    have hpp' : p.conjTranspose * p = p := by rw [hps, hpp]
    exact congrArg (fun M : CStarMatrix m m A => M i j) hpp'
  · have hpp' : p * p.conjTranspose = p := by rw [hps, hpp]
    ext i j
    change ∑ k : m, p (e.symm i) k * star (p (e.symm j) k) = p (e.symm i) (e.symm j)
    exact congrArg (fun M : CStarMatrix m m A => M (e.symm i) (e.symm j)) hpp'

/-- Block-diagonal sums of star projections commute up to Murray–von Neumann equivalence. -/
theorem MurrayVonNeumannEquiv.fromBlocks_comm [Fintype m] [Fintype n]
    [NonUnitalNonAssocSemiring A] [StarAddMonoid A]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    (hp : IsStarProjection p) (hq : IsStarProjection q) :
    (fromBlocks p 0 0 q).MurrayVonNeumannEquiv (fromBlocks q 0 0 p) := by
  simpa only [reindexₐ_sumComm_fromBlocks (R := ℕ)] using
    MurrayVonNeumannEquiv.reindexₐ (R := ℕ) (Equiv.sumComm m n)
      (IsStarProjection.fromBlocks_zero₁₂_zero₂₁ hp hq)

/-- Block-diagonal sums of star projections are associative up to Murray–von Neumann equivalence. -/
theorem MurrayVonNeumannEquiv.fromBlocks_assoc [Fintype m₁] [Fintype m₂] [Fintype m₃]
    [NonUnitalNonAssocSemiring A] [StarAddMonoid A]
    {p₁ : CStarMatrix m₁ m₁ A} {p₂ : CStarMatrix m₂ m₂ A} {p₃ : CStarMatrix m₃ m₃ A}
    (hp₁ : IsStarProjection p₁) (hp₂ : IsStarProjection p₂) (hp₃ : IsStarProjection p₃) :
    (fromBlocks (fromBlocks p₁ 0 0 p₂) 0 0 p₃).MurrayVonNeumannEquiv
      (fromBlocks p₁ 0 0 (fromBlocks p₂ 0 0 p₃)) := by
  simpa only [reindexₐ_sumAssoc_fromBlocks (R := ℕ)] using
    MurrayVonNeumannEquiv.reindexₐ (R := ℕ) (Equiv.sumAssoc m₁ m₂ m₃)
      (IsStarProjection.fromBlocks_zero₁₂_zero₂₁
        (IsStarProjection.fromBlocks_zero₁₂_zero₂₁ hp₁ hp₂) hp₃)

/-- Unitary conjugacy of star projections implies Murray–von Neumann equivalence. -/
theorem MurrayVonNeumannEquiv.of_unitary_conj [Fintype n] [DecidableEq n]
    [Semiring A] [StarRing A] {p q : CStarMatrix n n A}
    (hp : IsStarProjection p) (u : unitary (CStarMatrix n n A))
    (h : (u : CStarMatrix n n A) * p * star (u : CStarMatrix n n A) = q) :
    p.MurrayVonNeumannEquiv q := by
  refine ⟨(u : CStarMatrix n n A) * p, ?_, ?_⟩
  · rw [← star_eq_conjTranspose, star_mul, hp.isSelfAdjoint.star_eq, mul_assoc,
      ← mul_assoc (star (u : CStarMatrix n n A)), Unitary.star_mul_self_of_mem u.2, one_mul,
      hp.isIdempotentElem.eq]
  · rw [← star_eq_conjTranspose, star_mul, hp.isSelfAdjoint.star_eq, mul_assoc,
      ← mul_assoc p p, hp.isIdempotentElem.eq, ← mul_assoc, h]

/-- Unitary conjugacy in the unitization `(CStarMatrix n n A)⁺¹` implies Murray–von Neumann
equivalence in `CStarMatrix n n A`. -/
theorem MurrayVonNeumannEquiv.of_unitization_unitary_conj [Fintype n]
    [NonUnitalSemiring A] [StarRing A] [Module ℂ A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
    [StarModule ℂ A]
    {p q : CStarMatrix n n A} (hp : IsStarProjection p)
    (u : unitary (CStarMatrix n n A)⁺¹)
    (h : (u : (CStarMatrix n n A)⁺¹) * (p : (CStarMatrix n n A)⁺¹) *
      star (u : (CStarMatrix n n A)⁺¹) = (q : (CStarMatrix n n A)⁺¹)) :
    p.MurrayVonNeumannEquiv q := by
  let v' : (CStarMatrix n n A)⁺¹ := (u : (CStarMatrix n n A)⁺¹) * (p : (CStarMatrix n n A)⁺¹)
  have hfst : v'.fst = 0 := by simp [v', Unitization.fst_mul, Unitization.fst_inr]
  have hinr : (v'.snd : (CStarMatrix n n A)⁺¹) = v' := Unitization.ext (by simp [hfst]) rfl
  refine ⟨v'.snd, ?_, ?_⟩
  · apply Unitization.inr_injective (R := ℂ)
    rw [← star_eq_conjTranspose, Unitization.inr_mul, Unitization.inr_star, hinr]
    calc star v' * v'
        = (p : (CStarMatrix n n A)⁺¹) * (star (u : (CStarMatrix n n A)⁺¹) *
            (u : (CStarMatrix n n A)⁺¹)) * (p : (CStarMatrix n n A)⁺¹) := by
          simp only [v', star_mul, hp.inr.isSelfAdjoint.star_eq, mul_assoc]
      _ = (p : (CStarMatrix n n A)⁺¹) := by
          rw [Unitary.star_mul_self_of_mem u.2, mul_one, hp.inr.isIdempotentElem.eq]
  · apply Unitization.inr_injective (R := ℂ)
    rw [← star_eq_conjTranspose, Unitization.inr_mul, Unitization.inr_star, hinr]
    calc v' * star v'
        = (u : (CStarMatrix n n A)⁺¹) * ((p : (CStarMatrix n n A)⁺¹) *
            (p : (CStarMatrix n n A)⁺¹)) * star (u : (CStarMatrix n n A)⁺¹) := by
          simp only [v', star_mul, hp.inr.isSelfAdjoint.star_eq, mul_assoc]
      _ = (q : (CStarMatrix n n A)⁺¹) := by rw [hp.inr.isIdempotentElem.eq, h]

/-- Unitary conjugacy in `CStarMatrix n n A⁺¹` implies Murray–von Neumann equivalence in
`CStarMatrix n n A`. -/
theorem MurrayVonNeumannEquiv.of_matrix_unitization_unitary_conj [Fintype n] [DecidableEq n]
    [NonUnitalSemiring A] [StarRing A] [Module ℂ A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
    [StarModule ℂ A]
    {p q : CStarMatrix n n A} (hp : IsStarProjection p)
    (u : unitary (CStarMatrix n n A⁺¹))
    (h : (u : CStarMatrix n n A⁺¹) * p.map (Unitization.inr : A → A⁺¹) *
      star (u : CStarMatrix n n A⁺¹) = q.map (Unitization.inr : A → A⁺¹)) :
    p.MurrayVonNeumannEquiv q := by
  let ι : A →⋆ₙₐ[ℂ] A⁺¹ := Unitization.inrNonUnitalStarAlgHom ℂ A
  have hι : (ι : A → A⁺¹) = Unitization.inr := funext fun _ => rfl
  let p' : CStarMatrix n n A⁺¹ := p.map ι
  let v' : CStarMatrix n n A⁺¹ := (u : CStarMatrix n n A⁺¹) * p'
  have hp'_fst : p'.map (Unitization.fstHom ℂ A) = 0 :=
    CStarMatrix.ext fun i j => by simp [p', ι]
  have hv'_fst : v'.map (Unitization.fstHom ℂ A) = 0 := by
    rw [CStarMatrix.map_mul (Unitization.fstHom ℂ A), hp'_fst, mul_zero]
  let v : CStarMatrix n n A := v'.map fun x : A⁺¹ => x.snd
  have hv_inr : v.map ι = v' := map_inr_map_snd_of_map_fstHom_eq_zero hv'_fst
  have hp' : IsStarProjection p' := hp.map (CStarMatrix.mapₙₐ ι)
  have hinj : Function.Injective (fun M : CStarMatrix n n A => M.map (ι : A → A⁺¹)) := by
    simpa only [hι] using CStarMatrix.map_injective (m := n) (n := n)
      (Unitization.inr_injective (R := ℂ) (A := A))
  refine ⟨v, ?_, ?_⟩
  · apply hinj
    dsimp only
    rw [CStarMatrix.map_mul ι, map_conjTranspose ι, hv_inr]
    calc v'.conjTranspose * v'
        = p' * (star (u : CStarMatrix n n A⁺¹) * (u : CStarMatrix n n A⁺¹)) * p' := by
          rw [← star_eq_conjTranspose]
          simp only [v', star_mul, hp'.isSelfAdjoint.star_eq, mul_assoc]
      _ = p' := by rw [Unitary.star_mul_self_of_mem u.2, mul_one, hp'.isIdempotentElem.eq]
  · apply hinj
    dsimp only
    rw [CStarMatrix.map_mul ι, map_conjTranspose ι, hv_inr]
    calc v' * v'.conjTranspose
        = (u : CStarMatrix n n A⁺¹) * (p' * p') * star (u : CStarMatrix n n A⁺¹) := by
          rw [← star_eq_conjTranspose]
          simp only [v', star_mul, hp'.isSelfAdjoint.star_eq, mul_assoc]
      _ = q.map ι := by rw [hp'.isIdempotentElem.eq, hι]; exact h

/-- Entrywise application of a non-unital star ring homomorphism preserves Murray–von Neumann
equivalence. -/
theorem MurrayVonNeumannEquiv.map [Fintype m] [Fintype n]
    [NonUnitalNonAssocSemiring A] [Star A] [NonUnitalNonAssocSemiring B] [Star B]
    {F : Type*} [FunLike F A B] [NonUnitalRingHomClass F A B] [StarHomClass F A B]
    (f : F) {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    (h : p.MurrayVonNeumannEquiv q) : (p.map f).MurrayVonNeumannEquiv (q.map f) := by
  obtain ⟨v, hv₁, hv₂⟩ := h
  refine ⟨v.map f, ?_, ?_⟩
  · rw [← map_conjTranspose f, ← CStarMatrix.map_mul f, hv₁]
  · rw [← map_conjTranspose f, ← CStarMatrix.map_mul f, hv₂]

/-- Non-unital star-algebra homomorphisms preserve Murray–von Neumann equivalence under `mapₙₐ`. -/
theorem MurrayVonNeumannEquiv.mapₙₐ [Fintype m] [Fintype n] [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [Star A]
    [NonUnitalNonAssocSemiring B] [Module R B] [Star B]
    (φ : A →⋆ₙₐ[R] B) {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    (h : p.MurrayVonNeumannEquiv q) :
    (CStarMatrix.mapₙₐ φ p).MurrayVonNeumannEquiv (CStarMatrix.mapₙₐ φ q) :=
  h.map φ

/-- Unital star-algebra homomorphisms preserve Murray–von Neumann equivalence under `mapₐ`. -/
theorem MurrayVonNeumannEquiv.mapₐ [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [CommSemiring R] [Semiring A] [Algebra R A] [Star A] [Semiring B] [Algebra R B] [Star B]
    (φ : A →⋆ₐ[R] B) {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    (h : p.MurrayVonNeumannEquiv q) :
    (CStarMatrix.mapₐ φ p).MurrayVonNeumannEquiv (CStarMatrix.mapₐ φ q) := by
  convert h.map φ using 1 <;> exact CStarMatrix.ext (mapₐ_apply φ _)

end Compatibility

/-! ### Algebraic equivalence implies Murray–von Neumann equivalence -/

section AlgebraicEquiv

/-- **Rectangular algebraic equivalence of matrix projections implies Murray–von Neumann
equivalence** (Blackadar, Proposition 4.6.4). If `p : CStarMatrix m m A` and
`q : CStarMatrix n n A` are star projections in a (possibly non-unital) C⋆-algebra `A` with
rectangular `x`, `y` satisfying `x * y = p` and `y * x = q`, then `p` and `q` are Murray–von
Neumann equivalent. -/
theorem MurrayVonNeumannEquiv.of_mul_eq {m n A : Type*} [Fintype m] [Fintype n]
    [NonUnitalCStarAlgebra A]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    (hp : IsStarProjection p) (hq : IsStarProjection q)
    {x : CStarMatrix m n A} {y : CStarMatrix n m A}
    (hxy : x * y = p) (hyx : y * x = q) : p.MurrayVonNeumannEquiv q := by
  classical
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  -- Normalize `x` and `y` to `x₁ = p * x * q` and `y₁ = q * y * p`.
  let x₁ : CStarMatrix m n A := p * x * q
  let y₁ : CStarMatrix n m A := q * y * p
  have hx₁y₁ : x₁ * y₁ = p := by
    calc (p * x * q) * (q * y * p)
        = p * x * (q * q) * y * p := by simp only [CStarMatrix.mul_assoc]
      _ = p * x * (y * x) * y * p := by rw [hq.isIdempotentElem.eq, hyx]
      _ = p * (x * y) * (x * y) * p := by simp only [CStarMatrix.mul_assoc]
      _ = p := by rw [hxy, hp.isIdempotentElem.eq, hp.isIdempotentElem.eq, hp.isIdempotentElem.eq]
  have hy₁x₁ : y₁ * x₁ = q := by
    calc (q * y * p) * (p * x * q)
        = q * y * (p * p) * x * q := by simp only [CStarMatrix.mul_assoc]
      _ = q * y * (x * y) * x * q := by rw [hp.isIdempotentElem.eq, hxy]
      _ = q * (y * x) * (y * x) * q := by simp only [CStarMatrix.mul_assoc]
      _ = q := by rw [hyx, hq.isIdempotentElem.eq, hq.isIdempotentElem.eq, hq.isIdempotentElem.eq]
  have hpx₁ : p * x₁ = x₁ := by
    simp only [x₁, ← CStarMatrix.mul_assoc, hp.isIdempotentElem.eq]
  have hx₁q : x₁ * q = x₁ := by
    simp only [x₁, CStarMatrix.mul_assoc, hq.isIdempotentElem.eq]
  have hqy₁ : q * y₁ = y₁ := by
    simp only [y₁, ← CStarMatrix.mul_assoc, hq.isIdempotentElem.eq]
  have hy₁p : y₁ * p = y₁ := by
    simp only [y₁, CStarMatrix.mul_assoc, hp.isIdempotentElem.eq]
  -- Lift to `A⁺¹`.
  let ι : A →⋆ₙₐ[ℂ] A⁺¹ := Unitization.inrNonUnitalStarAlgHom ℂ A
  let p' : CStarMatrix m m A⁺¹ := p.map ι
  let q' : CStarMatrix n n A⁺¹ := q.map ι
  let x' : CStarMatrix m n A⁺¹ := x₁.map ι
  let y' : CStarMatrix n m A⁺¹ := y₁.map ι
  have hp' : IsStarProjection p' := hp.map (CStarMatrix.mapₙₐ ι)
  have hq' : IsStarProjection q' := hq.map (CStarMatrix.mapₙₐ ι)
  have hx'y' : x' * y' = p' := by rw [← CStarMatrix.map_mul ι, hx₁y₁]
  have hy'x' : y' * x' = q' := by rw [← CStarMatrix.map_mul ι, hy₁x₁]
  have hpx' : p' * x' = x' := by rw [← CStarMatrix.map_mul ι, hpx₁]
  have hx'q : x' * q' = x' := by rw [← CStarMatrix.map_mul ι, hx₁q]
  have hqy' : q' * y' = y' := by rw [← CStarMatrix.map_mul ι, hqy₁]
  have hy'p : y' * p' = y' := by rw [← CStarMatrix.map_mul ι, hy₁p]
  have hq's : q'.conjTranspose = q' := by
    simpa only [← star_eq_conjTranspose] using hq'.isSelfAdjoint.star_eq
  have hp's : p'.conjTranspose = p' := by
    simpa only [← star_eq_conjTranspose] using hp'.isSelfAdjoint.star_eq
  have hx's_p : x'.conjTranspose * p' = x'.conjTranspose := by
    simpa only [conjTranspose_mul, hp's] using congrArg conjTranspose hpx'
  have hq_x's : q' * x'.conjTranspose = x'.conjTranspose := by
    simpa only [conjTranspose_mul, hq's] using congrArg conjTranspose hx'q
  have hy's_q : y'.conjTranspose * q' = y'.conjTranspose := by
    simpa only [conjTranspose_mul, hq's] using congrArg conjTranspose hqy'
  -- Construct the strictly positive element `c = (1 - q') + x'ᴴ * x'` with inverse
  -- `b = (1 - q') + y' * y'ᴴ`.
  let c : CStarMatrix n n A⁺¹ := (1 - q') + x'.conjTranspose * x'
  let b : CStarMatrix n n A⁺¹ := (1 - q') + y' * y'.conjTranspose
  have h1q_sq : (1 - q') * (1 - q') = 1 - q' := (hq'.one_sub).isIdempotentElem.eq
  have h1q_y' : (1 - q') * y' = 0 := by
    rw [CStarMatrix.sub_mul, CStarMatrix.one_mul, hqy', sub_self]
  have hx'_1q : x' * (1 - q') = 0 := by
    rw [CStarMatrix.mul_sub, CStarMatrix.mul_one, hx'q, sub_self]
  have hy's_1q : y'.conjTranspose * (1 - q') = 0 := by
    rw [CStarMatrix.mul_sub, CStarMatrix.mul_one, hy's_q, sub_self]
  have h1q_x's : (1 - q') * x'.conjTranspose = 0 := by
    rw [CStarMatrix.sub_mul, CStarMatrix.one_mul, hq_x's, sub_self]
  have hcb : c * b = 1 := by
    have hcross₁ : (1 - q') * (y' * y'.conjTranspose) = 0 := by
      rw [← CStarMatrix.mul_assoc, h1q_y', CStarMatrix.zero_mul]
    have hcross₂ : (x'.conjTranspose * x') * (1 - q') = 0 := by
      rw [CStarMatrix.mul_assoc, hx'_1q, CStarMatrix.mul_zero]
    have hdiag : (x'.conjTranspose * x') * (y' * y'.conjTranspose) = q' := by
      calc (x'.conjTranspose * x') * (y' * y'.conjTranspose)
          = x'.conjTranspose * (x' * y') * y'.conjTranspose := by
            simp only [CStarMatrix.mul_assoc]
        _ = (x'.conjTranspose * p') * y'.conjTranspose := by rw [hx'y']
        _ = x'.conjTranspose * y'.conjTranspose := by rw [hx's_p]
        _ = (y' * x').conjTranspose := (conjTranspose_mul y' x').symm
        _ = q' := by rw [hy'x', hq's]
    change ((1 - q') + x'.conjTranspose * x') * ((1 - q') + y' * y'.conjTranspose) = 1
    rw [add_mul, mul_add, mul_add, h1q_sq, hcross₁, hcross₂, hdiag, add_zero, zero_add,
      sub_add_cancel]
  have hbc : b * c = 1 := by
    have hcross₁ : (1 - q') * (x'.conjTranspose * x') = 0 := by
      rw [← CStarMatrix.mul_assoc, h1q_x's, CStarMatrix.zero_mul]
    have hcross₂ : (y' * y'.conjTranspose) * (1 - q') = 0 := by
      rw [CStarMatrix.mul_assoc, hy's_1q, CStarMatrix.mul_zero]
    have hdiag : (y' * y'.conjTranspose) * (x'.conjTranspose * x') = q' := by
      calc (y' * y'.conjTranspose) * (x'.conjTranspose * x')
          = y' * (y'.conjTranspose * x'.conjTranspose) * x' := by
            simp only [CStarMatrix.mul_assoc]
        _ = y' * (x' * y').conjTranspose * x' := by rw [← conjTranspose_mul]
        _ = (y' * p') * x' := by rw [hx'y', hp's]
        _ = y' * x' := by rw [hy'p]
        _ = q' := hy'x'
    change ((1 - q') + y' * y'.conjTranspose) * ((1 - q') + x'.conjTranspose * x') = 1
    rw [add_mul, mul_add, mul_add, h1q_sq, hcross₁, hcross₂, hdiag, add_zero, zero_add,
      sub_add_cancel]
  have hc_unit : IsUnit c := ⟨⟨c, b, hcb, hbc⟩, rfl⟩
  have hc_inv : c⁻¹ʳ = b := Ring.inverse_unit ⟨c, b, hcb, hbc⟩
  have hc_nonneg : 0 ≤ c :=
    add_nonneg hq'.one_sub.nonneg (CStarMatrix.conjTranspose_mul_self_nonneg x')
  have hc_pos : IsStrictlyPositive c := hc_unit.isStrictlyPositive hc_nonneg
  let s : CStarMatrix n n A⁺¹ := CFC.sqrt c
  have hs_pos : IsStrictlyPositive s := hc_pos.sqrt
  have hs_unit : IsUnit s := hs_pos.isUnit
  have hs_sa : IsSelfAdjoint s := hs_pos.isSelfAdjoint
  have hss : s * s = c := CFC.sqrt_mul_sqrt_self c hc_nonneg
  have hcomm_cq : Commute c q' := by
    have h1 : c * q' = x'.conjTranspose * x' := by
      simp only [c, add_mul, sub_mul, one_mul, hq'.isIdempotentElem.eq, sub_self, zero_add,
        CStarMatrix.mul_assoc, hx'q]
    have h2 : q' * c = x'.conjTranspose * x' := by
      simp only [c, mul_add, mul_sub, mul_one, hq'.isIdempotentElem.eq, sub_self, zero_add,
        ← CStarMatrix.mul_assoc, hq_x's]
    exact h1.trans h2.symm
  have hcomm_sq : Commute s q' := hcomm_cq.cfcₙ_nnreal NNReal.sqrt
  have hsinv_sq : s⁻¹ʳ * s⁻¹ʳ = b := by
    have h : s⁻¹ʳ * s⁻¹ʳ = (s * s)⁻¹ʳ := (Ring.mul_inverse_rev' (Commute.refl s)).symm
    rw [h, hss, hc_inv]
  have hsinv_sa : s⁻¹ʳ.conjTranspose = s⁻¹ʳ := by
    rw [← star_eq_conjTranspose, ← Ring.inverse_star, hs_sa.star_eq]
  -- Define `w' = s⁻¹ʳ * x'ᴴ` and verify `w' * w'ᴴ = q'` and `w'ᴴ * w' = p'`.
  let w' : CStarMatrix n m A⁺¹ := s⁻¹ʳ * x'.conjTranspose
  have hw'₁ : w'.conjTranspose * w' = p' := by
    calc w'.conjTranspose * w'
        = (x' * s⁻¹ʳ) * (s⁻¹ʳ * x'.conjTranspose) := by
          simp only [w', conjTranspose_mul, conjTranspose_conjTranspose, hsinv_sa]
      _ = x' * (s⁻¹ʳ * s⁻¹ʳ) * x'.conjTranspose := by simp only [CStarMatrix.mul_assoc]
      _ = x' * ((1 - q') + y' * y'.conjTranspose) * x'.conjTranspose := by rw [hsinv_sq]
      _ = x' * (1 - q') * x'.conjTranspose +
            (x' * y') * (y'.conjTranspose * x'.conjTranspose) := by
          rw [CStarMatrix.mul_add, CStarMatrix.add_mul]
          simp only [CStarMatrix.mul_assoc]
      _ = p' * p'.conjTranspose := by
          rw [hx'_1q, CStarMatrix.zero_mul, zero_add, ← conjTranspose_mul, hx'y']
      _ = p' := by rw [hp's, hp'.isIdempotentElem.eq]
  have hw'₂ : w' * w'.conjTranspose = q' := by
    have hxx : x'.conjTranspose * x' = s * q' * s := by
      calc x'.conjTranspose * x' = c * q' := by
            simp only [c, add_mul, sub_mul, one_mul, hq'.isIdempotentElem.eq, sub_self, zero_add,
              CStarMatrix.mul_assoc, hx'q]
        _ = (s * s) * q' := by rw [hss]
        _ = s * (s * q') := mul_assoc _ _ _
        _ = s * (q' * s) := by rw [hcomm_sq.eq]
        _ = s * q' * s := (mul_assoc _ _ _).symm
    calc w' * w'.conjTranspose
        = s⁻¹ʳ * (x'.conjTranspose * x') * s⁻¹ʳ := by
          simp only [w', conjTranspose_mul, conjTranspose_conjTranspose, hsinv_sa,
            CStarMatrix.mul_assoc]
      _ = (s⁻¹ʳ * s) * q' * (s * s⁻¹ʳ) := by rw [hxx]; simp only [mul_assoc]
      _ = q' := by
          rw [Ring.inverse_mul_cancel _ hs_unit, Ring.mul_inverse_cancel _ hs_unit, one_mul,
            mul_one]
  -- Pull `w'` back from `A⁺¹` to `A` via `Unitization.snd`.
  have hx's_fst : x'.conjTranspose.map (Unitization.fstHom ℂ A) = 0 :=
    CStarMatrix.ext fun i j => by simp [x', ι]
  have hw'_fst : w'.map (Unitization.fstHom ℂ A) = 0 := by
    rw [CStarMatrix.map_mul (Unitization.fstHom ℂ A), hx's_fst, CStarMatrix.mul_zero]
  let w : CStarMatrix n m A := w'.map fun z : A⁺¹ => z.snd
  have hw_inr : w.map ι = w' := map_inr_map_snd_of_map_fstHom_eq_zero hw'_fst
  refine ⟨w, ?_, ?_⟩
  · refine CStarMatrix.ext fun i j => Unitization.inr_injective (R := ℂ) ?_
    have h := congrArg (fun M : CStarMatrix m m A⁺¹ => M i j) hw'₁
    simpa only [← hw_inr, ← map_conjTranspose ι, ← CStarMatrix.map_mul ι, p',
      CStarMatrix.map_apply, ι, Unitization.inrNonUnitalStarAlgHom_apply] using h
  · refine CStarMatrix.ext fun i j => Unitization.inr_injective (R := ℂ) ?_
    have h := congrArg (fun M : CStarMatrix n n A⁺¹ => M i j) hw'₂
    simpa only [← hw_inr, ← map_conjTranspose ι, ← CStarMatrix.map_mul ι, q',
      CStarMatrix.map_apply, ι, Unitization.inrNonUnitalStarAlgHom_apply] using h

end AlgebraicEquiv

/-! ### Paths of projections and stabilized unitary conjugacy -/

section PathsAndStabilization

/-- Endpoints of a norm-continuous path of matrix projections are Murray–von Neumann equivalent. -/
theorem MurrayVonNeumannEquiv.of_path {n A : Type*} [Fintype n] [NonUnitalCStarAlgebra A]
    {p q : CStarMatrix n n A} (γ : Path p q) (hγ : ∀ t : I, IsStarProjection (γ t)) :
    p.MurrayVonNeumannEquiv q := by
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  obtain ⟨u, hconj, -⟩ := IsStarProjection.exists_unitization_unitary_conj_of_path γ hγ
  have hp : IsStarProjection p := by simpa only [γ.source] using hγ 0
  exact MurrayVonNeumannEquiv.of_unitization_unitary_conj hp u hconj

/-- Nearby matrix projections (`‖p - q‖ < 1`) are Murray–von Neumann equivalent. -/
theorem MurrayVonNeumannEquiv.of_norm_sub_lt_one {n A : Type*} [Fintype n]
    [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {p q : CStarMatrix n n A} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hpq : ‖p - q‖ < 1) : p.MurrayVonNeumannEquiv q := by
  obtain ⟨u, hconj, -, -⟩ :=
    IsStarProjection.exists_unitization_unitary_conj_of_norm_sub_lt_one hp hq hpq
  exact MurrayVonNeumannEquiv.of_unitization_unitary_conj hp u hconj

/-- Given `vᴴ * v = p` and `v * vᴴ = q` for star projections `p : CStarMatrix m m A` and
`q : CStarMatrix n n A` over a unital proper star-ordered ring, the block matrix
`w = [[1 - p, vᴴ], [v, 1 - q]]` is a self-adjoint unitary conjugating `p ⊕ 0` to `0 ⊕ q`. -/
def stabilizedUnitary {m n A : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [PartialOrder A] [Ring A] [StarRing A] [StarOrderedRing A] [IsProperStar A]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A} (v : CStarMatrix n m A)
    (hv₁ : v.conjTranspose * v = p) (hv₂ : v * v.conjTranspose = q)
    (hp : IsStarProjection p) : unitary (CStarMatrix (m ⊕ n) (m ⊕ n) A) :=
  let hq : IsStarProjection q :=
    MurrayVonNeumannEquiv.isStarProjection_right ⟨v, hv₁, hv₂⟩ hp
  have hmul : fromBlocks (1 - p) v.conjTranspose v (1 - q) *
      fromBlocks (1 - p) v.conjTranspose v (1 - q) = 1 := by
    obtain ⟨hvp, -, hpv, -⟩ := mul_eq_self_of_conjTranspose_mul_self hv₁ hv₂ hp.isIdempotentElem
    apply ofMatrix.symm.injective
    have h1 : ofMatrix.symm (1 - p) = 1 - ofMatrix.symm p := rfl
    have h2 : ofMatrix.symm (1 - q) = 1 - ofMatrix.symm q := rfl
    rw [ofMatrix_symm_mul, ofMatrix_symm_fromBlocks, ofMatrix_symm_one,
      ofMatrix_symm_conjTranspose, h1, h2]
    exact Matrix.fromBlocks_one_sub_mul_self_of_mul_eq
      (a := (ofMatrix.symm v).conjTranspose) (b := ofMatrix.symm v)
      (e := ofMatrix.symm p) (f := ofMatrix.symm q)
      (by simpa only [ofMatrix_symm_hMul, ofMatrix_symm_conjTranspose] using
        congrArg ofMatrix.symm hv₁)
      (by simpa only [ofMatrix_symm_hMul, ofMatrix_symm_conjTranspose] using
        congrArg ofMatrix.symm hv₂)
      (by simpa only [ofMatrix_symm_hMul, ofMatrix_symm_conjTranspose] using
        congrArg ofMatrix.symm hpv)
      (by simpa only [ofMatrix_symm_hMul] using congrArg ofMatrix.symm hvp)
  have hsa : star (fromBlocks (1 - p) v.conjTranspose v (1 - q)) =
      fromBlocks (1 - p) v.conjTranspose v (1 - q) := by
    rw [fromBlocks_star, star_sub, star_one, hp.isSelfAdjoint.star_eq,
      star_sub, star_one, hq.isSelfAdjoint.star_eq, conjTranspose_conjTranspose]
  ⟨fromBlocks (1 - p) v.conjTranspose v (1 - q), by
    rw [Unitary.mem_iff, hsa, hmul, and_self]⟩

/-- The underlying matrix of `stabilizedUnitary`. -/
@[simp]
theorem coe_stabilizedUnitary {m n A : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] [PartialOrder A] [Ring A] [StarRing A] [StarOrderedRing A] [IsProperStar A]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A} (v : CStarMatrix n m A)
    (hv₁ : v.conjTranspose * v = p) (hv₂ : v * v.conjTranspose = q)
    (hp : IsStarProjection p) :
    (stabilizedUnitary v hv₁ hv₂ hp : CStarMatrix (m ⊕ n) (m ⊕ n) A) =
      fromBlocks (1 - p) v.conjTranspose v (1 - q) := (rfl)

/-- `stabilizedUnitary` is self-adjoint. -/
theorem isSelfAdjoint_stabilizedUnitary {m n A : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] [PartialOrder A] [Ring A] [StarRing A] [StarOrderedRing A] [IsProperStar A]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A} (v : CStarMatrix n m A)
    (hv₁ : v.conjTranspose * v = p) (hv₂ : v * v.conjTranspose = q)
    (hp : IsStarProjection p) :
    IsSelfAdjoint (stabilizedUnitary v hv₁ hv₂ hp : CStarMatrix (m ⊕ n) (m ⊕ n) A) := by
  have hq : IsStarProjection q :=
    MurrayVonNeumannEquiv.isStarProjection_right ⟨v, hv₁, hv₂⟩ hp
  rw [isSelfAdjoint_iff, coe_stabilizedUnitary, fromBlocks_star, star_sub, star_one,
    hp.isSelfAdjoint.star_eq, star_sub, star_one, hq.isSelfAdjoint.star_eq,
    conjTranspose_conjTranspose]

/-- `stabilizedUnitary` conjugates `fromBlocks p 0 0 0` to `fromBlocks 0 0 0 q`. -/
theorem stabilizedUnitary_conj {m n A : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] [PartialOrder A] [Ring A] [StarRing A] [StarOrderedRing A] [IsProperStar A]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A} (v : CStarMatrix n m A)
    (hv₁ : v.conjTranspose * v = p) (hv₂ : v * v.conjTranspose = q)
    (hp : IsStarProjection p) :
    (stabilizedUnitary v hv₁ hv₂ hp : CStarMatrix (m ⊕ n) (m ⊕ n) A) *
        fromBlocks p 0 0 0 *
        star (stabilizedUnitary v hv₁ hv₂ hp : CStarMatrix (m ⊕ n) (m ⊕ n) A) =
      fromBlocks 0 0 0 q := by
  rw [(isSelfAdjoint_stabilizedUnitary v hv₁ hv₂ hp).star_eq, coe_stabilizedUnitary]
  obtain ⟨hvp, -, -, -⟩ := mul_eq_self_of_conjTranspose_mul_self hv₁ hv₂ hp.isIdempotentElem
  apply ofMatrix.symm.injective
  have h1 : ofMatrix.symm (1 - p) = 1 - ofMatrix.symm p := rfl
  have h2 : ofMatrix.symm (1 - q) = 1 - ofMatrix.symm q := rfl
  have h0mm : ofMatrix.symm (0 : CStarMatrix m m A) = 0 := rfl
  have h0mn : ofMatrix.symm (0 : CStarMatrix m n A) = 0 := rfl
  have h0nm : ofMatrix.symm (0 : CStarMatrix n m A) = 0 := rfl
  have h0nn : ofMatrix.symm (0 : CStarMatrix n n A) = 0 := rfl
  rw [ofMatrix_symm_mul, ofMatrix_symm_mul, ofMatrix_symm_fromBlocks, ofMatrix_symm_fromBlocks,
    ofMatrix_symm_fromBlocks, ofMatrix_symm_conjTranspose, h1, h2, h0mm, h0mn, h0nm, h0nn]
  exact Matrix.fromBlocks_one_sub_mul_fromBlocks_mul_fromBlocks_one_sub_of_mul_eq
    (a := (ofMatrix.symm v).conjTranspose) (b := ofMatrix.symm v)
    (e := ofMatrix.symm p) (f := ofMatrix.symm q)
    (by simpa only [ofMatrix_symm_hMul, ofMatrix_symm_conjTranspose] using
      congrArg ofMatrix.symm hv₁)
    (by simpa only [ofMatrix_symm_hMul, ofMatrix_symm_conjTranspose] using
      congrArg ofMatrix.symm hv₂)
    (by simpa only [ofMatrix_symm_hMul] using congrArg ofMatrix.symm hvp)

/-- `stabilizedUnitary` lies in the identity path component of the unitary group via the explicit
exponential path `t ↦ expUnitary (t • π • ((1 - w) / 2))`. -/
theorem joined_one_stabilizedUnitary {m n A : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A} (v : CStarMatrix n m A)
    (hv₁ : v.conjTranspose * v = p) (hv₂ : v * v.conjTranspose = q)
    (hp : IsStarProjection p) :
    Joined (1 : unitary (CStarMatrix (m ⊕ n) (m ⊕ n) A))
      (stabilizedUnitary v hv₁ hv₂ hp) := by
  set w := stabilizedUnitary v hv₁ hv₂ hp
  have hw_sa : IsSelfAdjoint (w : CStarMatrix (m ⊕ n) (m ⊕ n) A) :=
    isSelfAdjoint_stabilizedUnitary v hv₁ hv₂ hp
  have hmem : (π : ℂ) • ((2 : ℂ)⁻¹ • (1 - (w : CStarMatrix (m ⊕ n) (m ⊕ n) A))) ∈
      selfAdjoint (CStarMatrix (m ⊕ n) (m ⊕ n) A) := by
    rw [selfAdjoint.mem_iff, star_smul, star_smul, star_sub, star_one, hw_sa.star_eq,
      RCLike.star_def, Complex.conj_ofReal, map_inv₀, map_ofNat]
  rw [← Unitary.expUnitary_pi_half_one_sub w hw_sa hmem]
  exact selfAdjoint.joined_one_expUnitary ⟨_, hmem⟩

/-- **Stabilized unitary conjugacy (unequal sizes, unital case).** Murray–von Neumann equivalent
projections `p : CStarMatrix m m A` and `q : CStarMatrix n n A` satisfy
`u * (p ⊕ 0) * u⋆ = 0 ⊕ q` for a unitary `u` in the identity path component. -/
theorem MurrayVonNeumannEquiv.exists_stabilized_unitary_conj {m n A : Type*} [Fintype m]
    [Fintype n] [DecidableEq m] [DecidableEq n] [CStarAlgebra A]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    (hp : IsStarProjection p) (h : p.MurrayVonNeumannEquiv q) :
    ∃ u : unitary (CStarMatrix (m ⊕ n) (m ⊕ n) A),
      (u : CStarMatrix (m ⊕ n) (m ⊕ n) A) * fromBlocks p 0 0 0 *
        star (u : CStarMatrix (m ⊕ n) (m ⊕ n) A) = fromBlocks 0 0 0 q ∧
      Joined (1 : unitary (CStarMatrix (m ⊕ n) (m ⊕ n) A)) u := by
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  obtain ⟨v, hv₁, hv₂⟩ := h
  exact ⟨stabilizedUnitary v hv₁ hv₂ hp, stabilizedUnitary_conj v hv₁ hv₂ hp,
    joined_one_stabilizedUnitary v hv₁ hv₂ hp⟩

/-- **Stabilized unitary conjugacy (equal sizes, unital case).** Murray–von Neumann equivalent
projections `p q : CStarMatrix n n A` satisfy `u * (p ⊕ 0) * u⋆ = q ⊕ 0` for a unitary `u` in the
identity path component of `unitary (CStarMatrix (n ⊕ n) (n ⊕ n) A)`. -/
theorem MurrayVonNeumannEquiv.exists_stabilized_unitary_conj_same {n A : Type*} [Fintype n]
    [DecidableEq n] [CStarAlgebra A]
    {p q : CStarMatrix n n A} (hp : IsStarProjection p) (h : p.MurrayVonNeumannEquiv q) :
    ∃ u : unitary (CStarMatrix (n ⊕ n) (n ⊕ n) A),
      (u : CStarMatrix (n ⊕ n) (n ⊕ n) A) * fromBlocks p 0 0 0 *
        star (u : CStarMatrix (n ⊕ n) (n ⊕ n) A) = fromBlocks q 0 0 0 ∧
      Joined (1 : unitary (CStarMatrix (n ⊕ n) (n ⊕ n) A)) u := by
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  obtain ⟨w, hw_conj, hw_join⟩ := h.exists_stabilized_unitary_conj hp
  let rot := blockRotation (n := n) (A := A) (π / 2)
  refine ⟨rot * w, ?_, ?_⟩
  · calc ((rot * w : unitary _) : CStarMatrix (n ⊕ n) (n ⊕ n) A) * fromBlocks p 0 0 0 *
            star ((rot * w : unitary _) : CStarMatrix (n ⊕ n) (n ⊕ n) A)
        = (rot : CStarMatrix (n ⊕ n) (n ⊕ n) A) *
            ((w : CStarMatrix (n ⊕ n) (n ⊕ n) A) * fromBlocks p 0 0 0 *
              star (w : CStarMatrix (n ⊕ n) (n ⊕ n) A)) *
            star (rot : CStarMatrix (n ⊕ n) (n ⊕ n) A) := by
          simp only [Submonoid.coe_mul, star_mul]
          noncomm_ring
      _ = (rot : CStarMatrix (n ⊕ n) (n ⊕ n) A) * fromBlocks 0 0 0 q *
            star (rot : CStarMatrix (n ⊕ n) (n ⊕ n) A) := by rw [hw_conj]
      _ = fromBlocks q 0 0 0 := blockRotation_pi_div_two_conj 0 q
  · simpa only [one_mul] using (joined_one_blockRotation (n := n) (A := A) (π / 2)).mul hw_join

private theorem path_of_unitization_unitary_path {k A : Type*} [Fintype k] [DecidableEq k]
    [NonUnitalCStarAlgebra A]
    {P Q : CStarMatrix k k A} (hP : IsStarProjection P)
    {u : unitary (CStarMatrix k k A⁺¹)}
    (hconj : (u : CStarMatrix k k A⁺¹) * P.map (Unitization.inr : A → A⁺¹) *
      star (u : CStarMatrix k k A⁺¹) = Q.map (Unitization.inr : A → A⁺¹))
    (hjoin : Joined (1 : unitary (CStarMatrix k k A⁺¹)) u) :
    ∃ γ : Path P Q, ∀ t : I, IsStarProjection (γ t) := by
  let ι : A →⋆ₙₐ[ℂ] A⁺¹ := Unitization.inrNonUnitalStarAlgHom ℂ A
  have hι : (ι : A → A⁺¹) = Unitization.inr := funext fun _ => rfl
  obtain ⟨δ⟩ := hjoin
  have hP_fst : (P.map ι).map (Unitization.fstHom ℂ A) = 0 :=
    CStarMatrix.ext fun i j => by simp [ι]
  have hfst : ∀ t : I,
      ((δ t : CStarMatrix k k A⁺¹) * P.map ι * star (δ t : CStarMatrix k k A⁺¹)).map
        (Unitization.fstHom ℂ A) = 0 := by
    intro t
    rw [CStarMatrix.map_mul (Unitization.fstHom ℂ A),
      CStarMatrix.map_mul (Unitization.fstHom ℂ A), hP_fst, mul_zero, zero_mul]
  let f : I → CStarMatrix k k A := fun t =>
    ((δ t : CStarMatrix k k A⁺¹) * P.map ι * star (δ t : CStarMatrix k k A⁺¹)).map
      (fun x : A⁺¹ => x.snd)
  have hf_inr : ∀ t : I, (f t).map ι =
      (δ t : CStarMatrix k k A⁺¹) * P.map ι * star (δ t : CStarMatrix k k A⁺¹) :=
    fun t => map_inr_map_snd_of_map_fstHom_eq_zero (hfst t)
  have hf_cont : Continuous f := by
    have hδ : Continuous (fun t : I => ((δ t : unitary (CStarMatrix k k A⁺¹)) :
        CStarMatrix k k A⁺¹)) := continuous_subtype_val.comp δ.continuous
    exact (continuous_map (Unitization.continuous_snd (𝕜 := ℂ) (A := A))).comp
      ((hδ.mul continuous_const).mul hδ.star)
  have hinj : Function.Injective (fun M : CStarMatrix k k A => M.map (ι : A → A⁺¹)) := by
    simpa only [hι] using CStarMatrix.map_injective (m := k) (n := k)
      (Unitization.inr_injective (R := ℂ) (A := A))
  refine ⟨⟨⟨f, hf_cont⟩, ?_, ?_⟩, fun t => ?_⟩
  · apply hinj
    dsimp only
    rw [hf_inr 0, δ.source]
    simp
  · apply hinj
    dsimp only
    rw [hf_inr 1, δ.target, hι]
    exact hconj
  · have hP' : IsStarProjection (P.map ι) := hP.map (CStarMatrix.mapₙₐ ι)
    have hproj' : IsStarProjection ((f t).map ι) := by
      rw [hf_inr t]
      simpa only [Unitary.conjStarAlgAut_apply] using
        hP'.map (Unitary.conjStarAlgAut ℂ (CStarMatrix k k A⁺¹) (δ t))
    refine ⟨?_, ?_⟩
    · rw [IsIdempotentElem]
      apply hinj
      dsimp only
      rw [CStarMatrix.map_mul ι]
      exact hproj'.isIdempotentElem.eq
    · rw [isSelfAdjoint_iff]
      apply hinj
      dsimp only
      rw [star_eq_conjTranspose, map_conjTranspose ι, ← star_eq_conjTranspose]
      exact hproj'.isSelfAdjoint.star_eq

/-- **Stabilized homotopy of equivalent projections (unequal sizes, non-unital case).**
If `p : CStarMatrix m m A` and `q : CStarMatrix n n A` are Murray–von Neumann equivalent star
projections in a (possibly non-unital) C⋆-algebra `A`, then `fromBlocks p 0 0 0` and
`fromBlocks 0 0 0 q` are joined by a norm-continuous path of star projections in
`CStarMatrix (m ⊕ n) (m ⊕ n) A`. -/
theorem MurrayVonNeumannEquiv.exists_path_fromBlocks_zero_left {m n A : Type*} [Fintype m]
    [Fintype n] [NonUnitalCStarAlgebra A]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    (hp : IsStarProjection p) (h : p.MurrayVonNeumannEquiv q) :
    ∃ γ : Path (fromBlocks p 0 0 (0 : CStarMatrix n n A))
        (fromBlocks (0 : CStarMatrix m m A) 0 0 q),
      ∀ t : I, IsStarProjection (γ t) := by
  classical
  let ι : A →⋆ₙₐ[ℂ] A⁺¹ := Unitization.inrNonUnitalStarAlgHom ℂ A
  have hι : (ι : A → A⁺¹) = Unitization.inr := funext fun _ => rfl
  have hp' : IsStarProjection (p.map ι) := hp.map (CStarMatrix.mapₙₐ ι)
  obtain ⟨u, hconj, hjoin⟩ := (h.map ι).exists_stabilized_unitary_conj hp'
  refine path_of_unitization_unitary_path
    (IsStarProjection.fromBlocks_zero₁₂_zero₂₁ hp (IsStarProjection.zero _)) ?_ hjoin
  simpa only [← hι, fromBlocks_map, CStarMatrix.map_zero (_root_.map_zero ι)]
    using hconj

/-- **Stabilized homotopy of equivalent projections (equal sizes, non-unital case).**
If `p q : CStarMatrix n n A` are Murray–von Neumann equivalent star projections in a (possibly
non-unital) C⋆-algebra `A`, then `fromBlocks p 0 0 0` and `fromBlocks q 0 0 0` are joined by a
norm-continuous path of star projections in `CStarMatrix (n ⊕ n) (n ⊕ n) A`. -/
theorem MurrayVonNeumannEquiv.exists_path_fromBlocks_zero_right {n A : Type*} [Fintype n]
    [NonUnitalCStarAlgebra A]
    {p q : CStarMatrix n n A} (hp : IsStarProjection p) (h : p.MurrayVonNeumannEquiv q) :
    ∃ γ : Path (fromBlocks p 0 0 (0 : CStarMatrix n n A))
        (fromBlocks q 0 0 (0 : CStarMatrix n n A)),
      ∀ t : I, IsStarProjection (γ t) := by
  classical
  let ι : A →⋆ₙₐ[ℂ] A⁺¹ := Unitization.inrNonUnitalStarAlgHom ℂ A
  have hι : (ι : A → A⁺¹) = Unitization.inr := funext fun _ => rfl
  have hp' : IsStarProjection (p.map ι) := hp.map (CStarMatrix.mapₙₐ ι)
  obtain ⟨u, hconj, hjoin⟩ := (h.map ι).exists_stabilized_unitary_conj_same hp'
  refine path_of_unitization_unitary_path
    (IsStarProjection.fromBlocks_zero₁₂_zero₂₁ hp (IsStarProjection.zero _)) ?_ hjoin
  simpa only [← hι, fromBlocks_map, CStarMatrix.map_zero (_root_.map_zero ι)]
    using hconj

end PathsAndStabilization

/-! ### Concrete checks -/

section Checks

/-- Unequal-size Murray–von Neumann equivalence: `diag(1, 0) : M₂(ℂ)` is equivalent to
`1 : M₁(ℂ)`. -/
example :
    (fromBlocks (1 : CStarMatrix (Fin 1) (Fin 1) ℂ) 0 0
      (0 : CStarMatrix (Fin 1) (Fin 1) ℂ)).MurrayVonNeumannEquiv
      (1 : CStarMatrix (Fin 1) (Fin 1) ℂ) :=
  (MurrayVonNeumannEquiv.fromBlocks_zero_right (IsStarProjection.one _)).symm

/-- Midpoint of the stabilized exponential path for `p = q = 1` in `M₁(ℂ)` and `v = 1`:
with `w = [[0, 1], [1, 0]]` and `r = (1 - w) / 2`, at `t = 1 / 2` the conjugate
`exp(i π r / 2) * diag(1, 0) * exp(-i π r / 2)` equals `[[1 / 2, i / 2], [-i / 2, 1 / 2]]`. -/
example :
    let p : CStarMatrix (Fin 1) (Fin 1) ℂ := 1
    let w : CStarMatrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ := fromBlocks 0 1 1 0
    let r : CStarMatrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ := (2 : ℂ)⁻¹ • (1 - w)
    have hr : IsStarProjection r :=
      IsStarProjection.half_one_sub_of_mul_self_eq_one
        (by simp [w]) (by simp [w, isSelfAdjoint_iff])
    have hmem : ((π / 2 : ℝ) : ℂ) • r ∈
        selfAdjoint (CStarMatrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ) := by
      rw [selfAdjoint.mem_iff, star_smul, RCLike.star_def, Complex.conj_ofReal,
        hr.isSelfAdjoint.star_eq]
    let u : unitary (CStarMatrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ) :=
      selfAdjoint.expUnitary ⟨((π / 2 : ℝ) : ℂ) • r, hmem⟩
    (u : CStarMatrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ) * fromBlocks p 0 0 0 *
        star (u : CStarMatrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ) =
      fromBlocks ((1 / 2 : ℂ) • 1) ((Complex.I / 2 : ℂ) • 1)
        ((-(Complex.I / 2) : ℂ) • 1) ((1 / 2 : ℂ) • 1) := by
  intro p w r hr hmem u
  have hexp : Complex.exp (Complex.I * ((π / 2 : ℝ) : ℂ)) = Complex.I := by
    rw [mul_comm, Complex.ofReal_div, Complex.ofReal_ofNat, Complex.exp_pi_div_two_mul_I]
  have hu : (u : CStarMatrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ) =
      fromBlocks (((1 + Complex.I) / 2 : ℂ) • 1) (((1 - Complex.I) / 2 : ℂ) • 1)
        (((1 - Complex.I) / 2 : ℂ) • 1) (((1 + Complex.I) / 2 : ℂ) • 1) := by
    dsimp only [u]
    rw [hr.coe_expUnitary_smul (π / 2) hmem, hexp]
    ext (i | i) (j | j) <;>
      simp [r, w, ← fromBlocks_one] <;> ring
  have hsu : star (u : CStarMatrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ) =
      fromBlocks (((1 - Complex.I) / 2 : ℂ) • 1) (((1 + Complex.I) / 2 : ℂ) • 1)
        (((1 + Complex.I) / 2 : ℂ) • 1) (((1 - Complex.I) / 2 : ℂ) • 1) := by
    rw [hu, fromBlocks_star]
    ext (i | i) (j | j) <;> simp [Complex.conj_I, sub_eq_add_neg]
  rw [hsu, hu]
  ext (i | i) (j | j) <;>
    simp [p, fromBlocks_mul] <;>
    ring_nf <;>
    simp [Complex.I_sq] <;>
    ring

end Checks

end CStarMatrix

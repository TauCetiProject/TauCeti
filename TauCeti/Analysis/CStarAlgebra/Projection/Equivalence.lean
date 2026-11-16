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

/-!
# Murray–von Neumann equivalence of matrix projections

For star projections `p : CStarMatrix m m A` and `q : CStarMatrix n n A` of possibly different
finite sizes, **Murray–von Neumann equivalence** `CStarMatrix.MurrayVonNeumannEquiv p q` holds
when there exists `v : CStarMatrix n m A` with `vᴴ * v = p` and `v * vᴴ = q`.

## Main definitions and results

* `CStarMatrix.MurrayVonNeumannEquiv`: equivalence relation on star projections (`.refl`, `.symm`,
  `.trans`), characterized by `TauCeti.IsPartialIsometry` for square matrices.
* Compatibility with block sums, orthogonal sums, zero-padding, reindexing, unitary conjugacy
  (in `A`, `(CStarMatrix n n A)⁺¹`, and `CStarMatrix n n A⁺¹`), and ⋆-homomorphisms.
* `CStarMatrix.MurrayVonNeumannEquiv.of_mul_eq`, `.of_path`, `.of_norm_sub_lt_one`: algebraic
  equivalence (Blackadar, Proposition 4.6.4), paths, and nearby projections imply equivalence.
* `CStarMatrix.stabilizedUnitary`, `.stabilizedUnitary_conj`, `.joined_one_stabilizedUnitary`,
  `.exists_stabilized_unitary_conj`, `.exists_stabilized_unitary_conj_same`,
  `.exists_path_fromBlocks_zero_left`, `.exists_path_fromBlocks_zero_right`: stabilized unitary
  conjugacy and projection paths.

## References

* B. Blackadar, *K-Theory for Operator Algebras*, 2nd ed., Cambridge University Press, 1998, §4.6.
-/

public section

open scoped CStarAlgebra ComplexOrder NNReal Real unitInterval Ring

namespace CStarMatrix

private theorem map_inr_map_snd_of_map_fstHom_eq_zero {m n A : Type*}
    [NonUnitalSemiring A] [Module ℂ A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
    {M : CStarMatrix m n A⁺¹} (hM : M.map (Unitization.fstHom ℂ A) = 0) :
    (M.map (fun x : A⁺¹ => x.snd)).map (Unitization.inr : A → A⁺¹) = M := by
  refine CStarMatrix.ext fun i j => Unitization.ext ?_ rfl
  simpa using (congrArg (fun X : CStarMatrix m n ℂ => X i j) hM).symm

private theorem map_fstHom_map_inr {m n A : Type*} [NonUnitalSemiring A] [Star A]
    [Module ℂ A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] (M : CStarMatrix m n A) :
    (M.map (Unitization.inrNonUnitalStarAlgHom ℂ A)).map (Unitization.fstHom ℂ A) = 0 :=
  CStarMatrix.ext fun _ _ => by simp

private theorem conjTranspose_mul_self_of_proj {m A : Type*} [Fintype m]
    [NonUnitalNonAssocSemiring A] [Star A] {p : CStarMatrix m m A} (hp : IsStarProjection p) :
    p.conjTranspose * p = p ∧ p * p.conjTranspose = p := by
  have h : p.conjTranspose = p := by
    simpa only [← star_eq_conjTranspose] using hp.isSelfAdjoint.star_eq
  exact ⟨by rw [h, hp.isIdempotentElem.eq], by rw [h, hp.isIdempotentElem.eq]⟩

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
  ⟨p, conjTranspose_mul_self_of_proj hp⟩

/-- Murray–von Neumann equivalence is symmetric. -/
theorem MurrayVonNeumannEquiv.symm [Fintype m] [Fintype n] [NonUnitalNonAssocSemiring A]
    [InvolutiveStar A] {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    (h : p.MurrayVonNeumannEquiv q) : q.MurrayVonNeumannEquiv p := by
  obtain ⟨v, hv₁, hv₂⟩ := h
  exact ⟨v.conjTranspose, by rwa [conjTranspose_conjTranspose],
    by rwa [conjTranspose_conjTranspose]⟩

section ProperStar

variable [PartialOrder A] [NonUnitalRing A] [StarRing A] [StarOrderedRing A] [IsProperStar A]

/-- In a proper star-ordered ring, if `vᴴ * v` is idempotent, then `v * (vᴴ * v) = v`. -/
theorem mul_conjTranspose_mul_self_of_isIdempotentElem [Fintype m] [Fintype n]
    {v : CStarMatrix n m A} (hp : IsIdempotentElem (v.conjTranspose * v)) :
    v * (v.conjTranspose * v) = v := by
  set p := v.conjTranspose * v
  have hps : p.conjTranspose = p := by simp only [p, conjTranspose_mul, conjTranspose_conjTranspose]
  have hzero : (v * p - v).conjTranspose * (v * p - v) = 0 := by
    calc (v * p - v).conjTranspose * (v * p - v)
        = (p * v.conjTranspose - v.conjTranspose) * (v * p - v) := by
          rw [conjTranspose_sub, conjTranspose_mul, hps]
      _ = (p * (v.conjTranspose * v) * p - p * (v.conjTranspose * v)) -
            ((v.conjTranspose * v) * p - v.conjTranspose * v) := by
          rw [CStarMatrix.sub_mul, CStarMatrix.mul_sub, CStarMatrix.mul_sub]
          simp only [CStarMatrix.mul_assoc]
      _ = 0 := by rw [hp.eq, hp.eq, sub_self]
  exact sub_eq_zero.mp (conjTranspose_mul_self_eq_zero.mp hzero)

/-- If `vᴴ * v = p` and `v * vᴴ = q` with `p` idempotent over a proper star-ordered ring, then
`v * p = v`, `q * v = v`, `p * vᴴ = vᴴ`, and `vᴴ * q = vᴴ`. -/
theorem mul_eq_self_of_conjTranspose_mul_self [Fintype m] [Fintype n]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A} {v : CStarMatrix n m A}
    (hv₁ : v.conjTranspose * v = p) (hv₂ : v * v.conjTranspose = q) (hp : IsIdempotentElem p) :
    v * p = v ∧ q * v = v ∧ p * v.conjTranspose = v.conjTranspose ∧
      v.conjTranspose * q = v.conjTranspose := by
  have hvp : v * p = v := hv₁ ▸ mul_conjTranspose_mul_self_of_isIdempotentElem (hv₁.symm ▸ hp)
  have hqv : q * v = v := by rw [← hv₂, CStarMatrix.mul_assoc, hv₁, hvp]
  have hps : p.conjTranspose = p := by rw [← hv₁, conjTranspose_mul, conjTranspose_conjTranspose]
  have hqs : q.conjTranspose = q := by rw [← hv₂, conjTranspose_mul, conjTranspose_conjTranspose]
  exact ⟨hvp, hqv, by simpa only [conjTranspose_mul, hps] using congrArg conjTranspose hvp,
    by simpa only [conjTranspose_mul, hqs] using congrArg conjTranspose hqv⟩

/-- Murray–von Neumann equivalence preserves star projections (right endpoint). -/
theorem MurrayVonNeumannEquiv.isStarProjection_right [Fintype m] [Fintype n]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    (h : p.MurrayVonNeumannEquiv q) (hp : IsStarProjection p) : IsStarProjection q := by
  obtain ⟨v, hv₁, hv₂⟩ := h
  obtain ⟨hvp, -, -, -⟩ := mul_eq_self_of_conjTranspose_mul_self hv₁ hv₂ hp.isIdempotentElem
  refine ⟨?_, ?_⟩
  · rw [IsIdempotentElem, ← hv₂, CStarMatrix.mul_assoc, ← CStarMatrix.mul_assoc v.conjTranspose v,
      hv₁, ← CStarMatrix.mul_assoc, hvp]
  · rw [isSelfAdjoint_iff, star_eq_conjTranspose, ← hv₂, conjTranspose_mul,
      conjTranspose_conjTranspose]

/-- Murray–von Neumann equivalence preserves star projections (left endpoint). -/
theorem MurrayVonNeumannEquiv.isStarProjection_left [Fintype m] [Fintype n]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    (h : p.MurrayVonNeumannEquiv q) (hq : IsStarProjection q) : IsStarProjection p :=
  h.symm.isStarProjection_right hq

/-- Murray–von Neumann equivalent matrices are either both star projections or neither. -/
theorem MurrayVonNeumannEquiv.isStarProjection_iff [Fintype m] [Fintype n]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    (h : p.MurrayVonNeumannEquiv q) : IsStarProjection p ↔ IsStarProjection q :=
  ⟨h.isStarProjection_right, h.isStarProjection_left⟩

/-- Murray–von Neumann equivalence is transitive on star projections. -/
theorem MurrayVonNeumannEquiv.trans [Fintype l] [Fintype m] [Fintype n]
    {p : CStarMatrix l l A} {q : CStarMatrix m m A} {r : CStarMatrix n n A}
    (h₁ : p.MurrayVonNeumannEquiv q) (h₂ : q.MurrayVonNeumannEquiv r)
    (hp : IsStarProjection p) : p.MurrayVonNeumannEquiv r := by
  have hq := h₁.isStarProjection_right hp
  obtain ⟨v, hv₁, hv₂⟩ := h₁
  obtain ⟨w, hw₁, hw₂⟩ := h₂
  obtain ⟨-, hqv, -, -⟩ := mul_eq_self_of_conjTranspose_mul_self hv₁ hv₂ hp.isIdempotentElem
  obtain ⟨hwq, -, -, -⟩ := mul_eq_self_of_conjTranspose_mul_self hw₁ hw₂ hq.isIdempotentElem
  refine ⟨w * v, ?_, ?_⟩
  · rw [conjTranspose_mul, CStarMatrix.mul_assoc, ← CStarMatrix.mul_assoc w.conjTranspose w v,
      hw₁, hqv, hv₁]
  · rw [conjTranspose_mul, CStarMatrix.mul_assoc, ← CStarMatrix.mul_assoc v v.conjTranspose,
      hv₂, ← CStarMatrix.mul_assoc w q w.conjTranspose, hwq, hw₂]

/-- For square matrices over a proper star-ordered ring, Murray–von Neumann equivalence of star
projections is witnessed precisely by partial isometries `TauCeti.IsPartialIsometry`. -/
theorem murrayVonNeumannEquiv_iff_exists_isPartialIsometry [Fintype n]
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

end ProperStar

/-- The initial and final projections of a square partial isometry are Murray–von Neumann
equivalent star projections. -/
theorem MurrayVonNeumannEquiv.of_isPartialIsometry [Fintype n] [NonUnitalSemiring A] [StarRing A]
    {v : CStarMatrix n n A} (hv : TauCeti.IsPartialIsometry v) :
    (star v * v).MurrayVonNeumannEquiv (v * star v) ∧
      IsStarProjection (star v * v) ∧ IsStarProjection (v * star v) :=
  ⟨⟨v, by simp [star_eq_conjTranspose]⟩,
    hv.isStarProjection_star_mul_self, hv.isStarProjection_mul_star_self⟩

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
  obtain ⟨v₁, hv₁, hw₁⟩ := h₁; obtain ⟨v₂, hv₂, hw₂⟩ := h₂
  refine ⟨fromBlocks v₁ 0 0 v₂, ?_, ?_⟩ <;> simp [hv₁, hw₁, hv₂, hw₂]

/-- Murray–von Neumann equivalence is compatible with sums of orthogonal star projections. -/
theorem MurrayVonNeumannEquiv.add [Fintype m] [Fintype n]
    [PartialOrder A] [NonUnitalRing A] [StarRing A] [StarOrderedRing A] [IsProperStar A]
    {p₁ p₂ : CStarMatrix m m A} {q₁ q₂ : CStarMatrix n n A}
    (h₁ : p₁.MurrayVonNeumannEquiv q₁) (h₂ : p₂.MurrayVonNeumannEquiv q₂)
    (hp₁ : IsStarProjection p₁) (hp₂ : IsStarProjection p₂)
    (hp : p₁ * p₂ = 0) (hq : q₁ * q₂ = 0) :
    (p₁ + p₂).MurrayVonNeumannEquiv (q₁ + q₂) := by
  obtain ⟨v₁, hv₁, hw₁⟩ := h₁; obtain ⟨v₂, hv₂, hw₂⟩ := h₂
  obtain ⟨hv₁p, -, -, hv₁q⟩ := mul_eq_self_of_conjTranspose_mul_self hv₁ hw₁ hp₁.isIdempotentElem
  obtain ⟨-, hq₂v, hp₂v, -⟩ := mul_eq_self_of_conjTranspose_mul_self hv₂ hw₂ hp₂.isIdempotentElem
  have h12 : v₁.conjTranspose * v₂ = 0 := by
    rw [← hv₁q, ← hq₂v, CStarMatrix.mul_assoc, ← CStarMatrix.mul_assoc q₁ q₂, hq,
      CStarMatrix.zero_mul, CStarMatrix.mul_zero]
  have h21 : v₂.conjTranspose * v₁ = 0 := by
    simpa only [conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_zero] using
      congrArg conjTranspose h12
  have h12' : v₁ * v₂.conjTranspose = 0 := by
    rw [← hv₁p, ← hp₂v, CStarMatrix.mul_assoc, ← CStarMatrix.mul_assoc p₁ p₂, hp,
      CStarMatrix.zero_mul, CStarMatrix.mul_zero]
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
  obtain ⟨hpp, hpp'⟩ := conjTranspose_mul_self_of_proj hp
  refine ⟨ofMatrix (Matrix.of fun i j => Sum.elim (fun i₁ => p i₁ j) (fun _ => 0) i), ?_, ?_⟩
  · ext i j
    simpa [mul_apply, Fintype.sum_sum_type] using congrArg (fun M : CStarMatrix m m A => M i j) hpp
  · ext (i | i) (j | j)
    · simpa [mul_apply] using congrArg (fun M : CStarMatrix m m A => M i j) hpp'
    all_goals simp [mul_apply]

/-- A star projection is Murray–von Neumann equivalent to its lower-right zero-padded block
`fromBlocks 0 0 0 p` (without requiring `A` to be unital). -/
theorem MurrayVonNeumannEquiv.fromBlocks_zero_left [Fintype m] [Fintype n]
    [NonUnitalNonAssocSemiring A] [StarAddMonoid A]
    {p : CStarMatrix n n A} (hp : IsStarProjection p) :
    p.MurrayVonNeumannEquiv (fromBlocks (0 : CStarMatrix m m A) 0 0 p) := by
  obtain ⟨hpp, hpp'⟩ := conjTranspose_mul_self_of_proj hp
  refine ⟨ofMatrix (Matrix.of fun i j => Sum.elim (fun _ => 0) (fun i₂ => p i₂ j) i), ?_, ?_⟩
  · ext i j
    simpa [mul_apply, Fintype.sum_sum_type] using congrArg (fun M : CStarMatrix n n A => M i j) hpp
  · ext (i | i) (j | j)
    case inr.inr => simpa [mul_apply] using congrArg (fun M : CStarMatrix n n A => M i j) hpp'
    all_goals simp [mul_apply]

/-- Reindexing a star projection along any equivalence of finite index types yields a
Murray–von Neumann equivalent projection (without requiring `A` to be unital). -/
theorem MurrayVonNeumannEquiv.reindexₐ [Fintype m] [Fintype n] [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [Star A]
    (e : m ≃ n) {p : CStarMatrix m m A} (hp : IsStarProjection p) :
    p.MurrayVonNeumannEquiv (CStarMatrix.reindexₐ R A e p) := by
  obtain ⟨hpp, hpp'⟩ := conjTranspose_mul_self_of_proj hp
  refine ⟨ofMatrix (Matrix.of fun i j => p (e.symm i) j), ?_, ?_⟩
  · ext i j
    change ∑ k : n, star (p (e.symm k) i) * p (e.symm k) j = p i j
    rw [Equiv.sum_comp e.symm (fun k => star (p k i) * p k j)]
    exact congrArg (fun M : CStarMatrix m m A => M i j) hpp
  · ext i j
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
    [StarModule ℂ A] {p q : CStarMatrix n n A} (hp : IsStarProjection p)
    (u : unitary (CStarMatrix n n A)⁺¹)
    (h : (u : (CStarMatrix n n A)⁺¹) * (p : (CStarMatrix n n A)⁺¹) *
      star (u : (CStarMatrix n n A)⁺¹) = (q : (CStarMatrix n n A)⁺¹)) :
    p.MurrayVonNeumannEquiv q := by
  let v' : (CStarMatrix n n A)⁺¹ := (u : (CStarMatrix n n A)⁺¹) * (p : (CStarMatrix n n A)⁺¹)
  have hinr : (v'.snd : (CStarMatrix n n A)⁺¹) = v' :=
    Unitization.ext (by simp [v', Unitization.fst_mul, Unitization.fst_inr]) rfl
  refine ⟨v'.snd, ?_, ?_⟩ <;>
  · apply Unitization.inr_injective (R := ℂ)
    rw [← star_eq_conjTranspose, Unitization.inr_mul, Unitization.inr_star, hinr]
    simp only [v', star_mul, hp.inr.isSelfAdjoint.star_eq, mul_assoc]
    first
    | rw [← mul_assoc (star (u : (CStarMatrix n n A)⁺¹)), Unitary.star_mul_self_of_mem u.2,
        one_mul, hp.inr.isIdempotentElem.eq]
    | rw [← mul_assoc (p : (CStarMatrix n n A)⁺¹) (p : (CStarMatrix n n A)⁺¹),
        hp.inr.isIdempotentElem.eq, ← mul_assoc, h]

/-- Unitary conjugacy in `CStarMatrix n n A⁺¹` implies Murray–von Neumann equivalence in
`CStarMatrix n n A`. -/
theorem MurrayVonNeumannEquiv.of_matrix_unitization_unitary_conj [Fintype n] [DecidableEq n]
    [NonUnitalSemiring A] [StarRing A] [Module ℂ A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
    [StarModule ℂ A] {p q : CStarMatrix n n A} (hp : IsStarProjection p)
    (u : unitary (CStarMatrix n n A⁺¹))
    (h : (u : CStarMatrix n n A⁺¹) * p.map (Unitization.inr : A → A⁺¹) *
      star (u : CStarMatrix n n A⁺¹) = q.map (Unitization.inr : A → A⁺¹)) :
    p.MurrayVonNeumannEquiv q := by
  let ι : A →⋆ₙₐ[ℂ] A⁺¹ := Unitization.inrNonUnitalStarAlgHom ℂ A
  have hι : (ι : A → A⁺¹) = Unitization.inr := funext fun _ => rfl
  let p' : CStarMatrix n n A⁺¹ := p.map ι
  let v' : CStarMatrix n n A⁺¹ := (u : CStarMatrix n n A⁺¹) * p'
  have hv'_fst : v'.map (Unitization.fstHom ℂ A) = 0 := by
    rw [CStarMatrix.map_mul (Unitization.fstHom ℂ A), map_fstHom_map_inr p, mul_zero]
  let v : CStarMatrix n n A := v'.map fun x : A⁺¹ => x.snd
  have hv_inr : v.map ι = v' := map_inr_map_snd_of_map_fstHom_eq_zero hv'_fst
  have hp' : IsStarProjection p' := hp.map (CStarMatrix.mapₙₐ ι)
  have hinj : Function.Injective (fun M : CStarMatrix n n A => M.map (ι : A → A⁺¹)) := by
    simpa only [hι] using CStarMatrix.map_injective (m := n) (n := n)
      (Unitization.inr_injective (R := ℂ) (A := A))
  refine ⟨v, ?_, ?_⟩ <;>
  · apply hinj; dsimp only
    rw [CStarMatrix.map_mul ι, map_conjTranspose ι, hv_inr, ← star_eq_conjTranspose]
    simp only [v', star_mul, hp'.isSelfAdjoint.star_eq, mul_assoc]
    first
    | rw [← mul_assoc (star (u : CStarMatrix n n A⁺¹)), Unitary.star_mul_self_of_mem u.2, one_mul,
        hp'.isIdempotentElem.eq]
    | rw [← mul_assoc p' p', hp'.isIdempotentElem.eq, ← mul_assoc, hι]; exact h

/-- Entrywise application of a non-unital star ring homomorphism preserves Murray–von Neumann
equivalence. -/
theorem MurrayVonNeumannEquiv.map [Fintype m] [Fintype n]
    [NonUnitalNonAssocSemiring A] [Star A] [NonUnitalNonAssocSemiring B] [Star B]
    {F : Type*} [FunLike F A B] [NonUnitalRingHomClass F A B] [StarHomClass F A B]
    (f : F) {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    (h : p.MurrayVonNeumannEquiv q) : (p.map f).MurrayVonNeumannEquiv (q.map f) := by
  obtain ⟨v, hv₁, hv₂⟩ := h
  exact ⟨v.map f, by rw [← map_conjTranspose f, ← CStarMatrix.map_mul f, hv₁],
    by rw [← map_conjTranspose f, ← CStarMatrix.map_mul f, hv₂]⟩

/-- Non-unital star-algebra homomorphisms preserve Murray–von Neumann equivalence under `mapₙₐ`. -/
theorem MurrayVonNeumannEquiv.mapₙₐ [Fintype m] [Fintype n] [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [Star A]
    [NonUnitalNonAssocSemiring B] [Module R B] [Star B]
    (φ : A →⋆ₙₐ[R] B) {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    (h : p.MurrayVonNeumannEquiv q) :
    (CStarMatrix.mapₙₐ φ p).MurrayVonNeumannEquiv (CStarMatrix.mapₙₐ φ q) := h.map φ

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
  let ι : A →⋆ₙₐ[ℂ] A⁺¹ := Unitization.inrNonUnitalStarAlgHom ℂ A
  let p' : CStarMatrix m m A⁺¹ := p.map ι
  let q' : CStarMatrix n n A⁺¹ := q.map ι
  let x₀ : CStarMatrix m n A⁺¹ := x.map ι
  let y₀ : CStarMatrix n m A⁺¹ := y.map ι
  have hp' : IsStarProjection p' := hp.map (CStarMatrix.mapₙₐ ι)
  have hq' : IsStarProjection q' := hq.map (CStarMatrix.mapₙₐ ι)
  have hx₀y₀ : x₀ * y₀ = p' := by rw [← CStarMatrix.map_mul ι, hxy]
  have hy₀x₀ : y₀ * x₀ = q' := by rw [← CStarMatrix.map_mul ι, hyx]
  let x' : CStarMatrix m n A⁺¹ := p' * x₀ * q'
  let y' : CStarMatrix n m A⁺¹ := q' * y₀ * p'
  have hx'y' : x' * y' = p' := by
    calc (p' * x₀ * q') * (q' * y₀ * p') = p' * x₀ * (q' * q') * y₀ * p' := by
          simp only [CStarMatrix.mul_assoc]
      _ = p' * (x₀ * y₀) * (x₀ * y₀) * p' := by
          rw [hq'.isIdempotentElem.eq, ← hy₀x₀]; simp only [CStarMatrix.mul_assoc]
      _ = p' := by
          rw [hx₀y₀, hp'.isIdempotentElem.eq, hp'.isIdempotentElem.eq, hp'.isIdempotentElem.eq]
  have hy'x' : y' * x' = q' := by
    calc (q' * y₀ * p') * (p' * x₀ * q') = q' * y₀ * (p' * p') * x₀ * q' := by
          simp only [CStarMatrix.mul_assoc]
      _ = q' * (y₀ * x₀) * (y₀ * x₀) * q' := by
          rw [hp'.isIdempotentElem.eq, ← hx₀y₀]; simp only [CStarMatrix.mul_assoc]
      _ = q' := by
          rw [hy₀x₀, hq'.isIdempotentElem.eq, hq'.isIdempotentElem.eq, hq'.isIdempotentElem.eq]
  have hpx' : p' * x' = x' := by simp only [x', ← CStarMatrix.mul_assoc, hp'.isIdempotentElem.eq]
  have hx'q : x' * q' = x' := by simp only [x', CStarMatrix.mul_assoc, hq'.isIdempotentElem.eq]
  have hqy' : q' * y' = y' := by simp only [y', ← CStarMatrix.mul_assoc, hq'.isIdempotentElem.eq]
  have hy'p : y' * p' = y' := by simp only [y', CStarMatrix.mul_assoc, hp'.isIdempotentElem.eq]
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
  let c : CStarMatrix n n A⁺¹ := (1 - q') + x'.conjTranspose * x'
  let b : CStarMatrix n n A⁺¹ := (1 - q') + y' * y'.conjTranspose
  have hx'_1q : x' * (1 - q') = 0 := by
    rw [CStarMatrix.mul_sub, CStarMatrix.mul_one, hx'q, sub_self]
  have hcb : c * b = 1 := by
    have hdiag : (x'.conjTranspose * x') * (y' * y'.conjTranspose) = q' := by
      calc (x'.conjTranspose * x') * (y' * y'.conjTranspose)
          = x'.conjTranspose * (x' * y') * y'.conjTranspose := by simp only [CStarMatrix.mul_assoc]
        _ = (y' * x').conjTranspose := by rw [hx'y', hx's_p, ← conjTranspose_mul]
        _ = q' := by rw [hy'x', hq's]
    have h1q_y' : (1 - q') * y' = 0 := by
      rw [CStarMatrix.sub_mul, CStarMatrix.one_mul, hqy', sub_self]
    dsimp only [c, b]
    rw [add_mul, mul_add, mul_add, hq'.one_sub.isIdempotentElem.eq, ← CStarMatrix.mul_assoc,
      h1q_y', CStarMatrix.zero_mul, CStarMatrix.mul_assoc, hx'_1q, CStarMatrix.mul_zero, hdiag,
      add_zero, zero_add, sub_add_cancel]
  have hbc : b * c = 1 := by
    have hdiag : (y' * y'.conjTranspose) * (x'.conjTranspose * x') = q' := by
      calc (y' * y'.conjTranspose) * (x'.conjTranspose * x')
          = y' * (y'.conjTranspose * x'.conjTranspose) * x' := by simp only [CStarMatrix.mul_assoc]
        _ = y' * (x' * y').conjTranspose * x' := by rw [← conjTranspose_mul]
        _ = q' := by rw [hx'y', hp's, hy'p, hy'x']
    have h1q_x's : (1 - q') * x'.conjTranspose = 0 := by
      rw [CStarMatrix.sub_mul, CStarMatrix.one_mul, hq_x's, sub_self]
    have hy's_1q : y'.conjTranspose * (1 - q') = 0 := by
      rw [CStarMatrix.mul_sub, CStarMatrix.mul_one, hy's_q, sub_self]
    dsimp only [c, b]
    rw [add_mul, mul_add, mul_add, hq'.one_sub.isIdempotentElem.eq, ← CStarMatrix.mul_assoc,
      h1q_x's, CStarMatrix.zero_mul, CStarMatrix.mul_assoc, hy's_1q, CStarMatrix.mul_zero, hdiag,
      add_zero, zero_add, sub_add_cancel]
  have hc_nonneg : 0 ≤ c :=
    add_nonneg hq'.one_sub.nonneg (CStarMatrix.conjTranspose_mul_self_nonneg x')
  let s : CStarMatrix n n A⁺¹ := CFC.sqrt c
  have hs_pos : IsStrictlyPositive s :=
    (IsUnit.isStrictlyPositive ⟨⟨c, b, hcb, hbc⟩, rfl⟩ hc_nonneg).sqrt
  have hss : s * s = c := CFC.sqrt_mul_sqrt_self c hc_nonneg
  have hcq : c * q' = x'.conjTranspose * x' := by
    simp only [c, add_mul, sub_mul, one_mul, hq'.isIdempotentElem.eq, sub_self, zero_add,
      CStarMatrix.mul_assoc, hx'q]
  have hcomm_cq : Commute c q' := hcq.trans (by
    simp only [c, mul_add, mul_sub, mul_one, hq'.isIdempotentElem.eq, sub_self, zero_add,
      ← CStarMatrix.mul_assoc, hq_x's])
  have hsinv_sa : s⁻¹ʳ.conjTranspose = s⁻¹ʳ := by
    rw [← star_eq_conjTranspose, ← Ring.inverse_star, hs_pos.isSelfAdjoint.star_eq]
  let w' : CStarMatrix n m A⁺¹ := s⁻¹ʳ * x'.conjTranspose
  have hw'₁ : w'.conjTranspose * w' = p' := by
    have hsinv_sq : s⁻¹ʳ * s⁻¹ʳ = b := by
      rw [← Ring.mul_inverse_rev' (Commute.refl s), hss, Ring.inverse_unit ⟨c, b, hcb, hbc⟩]; rfl
    calc w'.conjTranspose * w'
        = x' * (s⁻¹ʳ * s⁻¹ʳ) * x'.conjTranspose := by
          simp only [w', conjTranspose_mul, conjTranspose_conjTranspose, hsinv_sa,
            CStarMatrix.mul_assoc]
      _ = x' * (1 - q') * x'.conjTranspose + (x' * y') * (y'.conjTranspose * x'.conjTranspose) := by
          rw [hsinv_sq, CStarMatrix.mul_add, CStarMatrix.add_mul]; simp only [CStarMatrix.mul_assoc]
      _ = p' := by
          rw [hx'_1q, CStarMatrix.zero_mul, zero_add, ← conjTranspose_mul, hx'y', hp's,
            hp'.isIdempotentElem.eq]
  have hw'₂ : w' * w'.conjTranspose = q' := by
    have hcomm_sq : Commute s q' := hcomm_cq.cfcₙ_nnreal NNReal.sqrt
    have hxx : x'.conjTranspose * x' = s * q' * s := by
      conv_lhs => rw [← hcq, ← hss, mul_assoc, hcomm_sq.eq, ← mul_assoc]
    calc w' * w'.conjTranspose
        = s⁻¹ʳ * (x'.conjTranspose * x') * s⁻¹ʳ := by
          simp only [w', conjTranspose_mul, conjTranspose_conjTranspose, hsinv_sa,
            CStarMatrix.mul_assoc]
      _ = (s⁻¹ʳ * s) * q' * (s * s⁻¹ʳ) := by rw [hxx]; simp only [CStarMatrix.mul_assoc]
      _ = q' := by
          rw [Ring.inverse_mul_cancel _ hs_pos.isUnit, Ring.mul_inverse_cancel _ hs_pos.isUnit,
            one_mul, mul_one]
  let w : CStarMatrix n m A := w'.map fun z : A⁺¹ => z.snd
  have hw_inr : w.map ι = w' := map_inr_map_snd_of_map_fstHom_eq_zero (by
    rw [CStarMatrix.map_mul (Unitization.fstHom ℂ A), map_conjTranspose (Unitization.fstHom ℂ A),
      CStarMatrix.map_mul (Unitization.fstHom ℂ A), CStarMatrix.map_mul (Unitization.fstHom ℂ A),
      map_fstHom_map_inr p, CStarMatrix.zero_mul, CStarMatrix.zero_mul, conjTranspose_zero,
      CStarMatrix.mul_zero])
  refine ⟨w, CStarMatrix.ext fun i j => Unitization.inr_injective (R := ℂ) ?_,
    CStarMatrix.ext fun i j => Unitization.inr_injective (R := ℂ) ?_⟩
  · simpa only [← hw_inr, ← map_conjTranspose ι, ← CStarMatrix.map_mul ι, p',
      CStarMatrix.map_apply, ι, Unitization.inrNonUnitalStarAlgHom_apply] using
      congrArg (fun M : CStarMatrix m m A⁺¹ => M i j) hw'₁
  · simpa only [← hw_inr, ← map_conjTranspose ι, ← CStarMatrix.map_mul ι, q',
      CStarMatrix.map_apply, ι, Unitization.inrNonUnitalStarAlgHom_apply] using
      congrArg (fun M : CStarMatrix n n A⁺¹ => M i j) hw'₂

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
  exact MurrayVonNeumannEquiv.of_unitization_unitary_conj (by simpa only [γ.source] using hγ 0)
    u hconj

/-- Nearby matrix projections (`‖p - q‖ < 1`) are Murray–von Neumann equivalent. -/
theorem MurrayVonNeumannEquiv.of_norm_sub_lt_one {n A : Type*} [Fintype n]
    [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {p q : CStarMatrix n n A} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hpq : ‖p - q‖ < 1) : p.MurrayVonNeumannEquiv q := by
  obtain ⟨u, hconj, -, -⟩ :=
    IsStarProjection.exists_unitization_unitary_conj_of_norm_sub_lt_one hp hq hpq
  exact MurrayVonNeumannEquiv.of_unitization_unitary_conj hp u hconj

section StabilizedUnitary

variable {m n A : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
  [PartialOrder A] [Ring A] [StarRing A] [StarOrderedRing A] [IsProperStar A]
  {p : CStarMatrix m m A} {q : CStarMatrix n n A}

/-- Given `vᴴ * v = p` and `v * vᴴ = q` for star projections `p : CStarMatrix m m A` and
`q : CStarMatrix n n A` over a unital proper star-ordered ring, the block matrix
`w = [[1 - p, vᴴ], [v, 1 - q]]` is a self-adjoint unitary conjugating `p ⊕ 0` to `0 ⊕ q`. -/
def stabilizedUnitary (v : CStarMatrix n m A) (hv₁ : v.conjTranspose * v = p)
    (hv₂ : v * v.conjTranspose = q) (hp : IsStarProjection p) :
    unitary (CStarMatrix (m ⊕ n) (m ⊕ n) A) :=
  let hq : IsStarProjection q :=
    MurrayVonNeumannEquiv.isStarProjection_right ⟨v, hv₁, hv₂⟩ hp
  have hmul : fromBlocks (1 - p) v.conjTranspose v (1 - q) *
      fromBlocks (1 - p) v.conjTranspose v (1 - q) = 1 := by
    obtain ⟨hvp, hqv, hpv, hvq⟩ := mul_eq_self_of_conjTranspose_mul_self hv₁ hv₂ hp.isIdempotentElem
    simp only [fromBlocks_mul, CStarMatrix.sub_mul, CStarMatrix.mul_sub, CStarMatrix.one_mul,
      CStarMatrix.mul_one, hp.isIdempotentElem.eq, hq.isIdempotentElem.eq, hv₁, hv₂, hvp, hqv,
      hpv, hvq, sub_self, sub_zero, add_zero, sub_add_cancel, add_sub_cancel, fromBlocks_one]
  have hsa : star (fromBlocks (1 - p) v.conjTranspose v (1 - q)) =
      fromBlocks (1 - p) v.conjTranspose v (1 - q) := by
    rw [fromBlocks_star, star_sub, star_one, hp.isSelfAdjoint.star_eq,
      star_sub, star_one, hq.isSelfAdjoint.star_eq, conjTranspose_conjTranspose]
  ⟨fromBlocks (1 - p) v.conjTranspose v (1 - q), by rw [Unitary.mem_iff, hsa, hmul, and_self]⟩

@[simp] theorem coe_stabilizedUnitary (v : CStarMatrix n m A) (hv₁ : v.conjTranspose * v = p)
    (hv₂ : v * v.conjTranspose = q) (hp : IsStarProjection p) :
    (stabilizedUnitary v hv₁ hv₂ hp : CStarMatrix (m ⊕ n) (m ⊕ n) A) =
      fromBlocks (1 - p) v.conjTranspose v (1 - q) := (rfl)

/-- `stabilizedUnitary` is self-adjoint. -/
theorem isSelfAdjoint_stabilizedUnitary (v : CStarMatrix n m A) (hv₁ : v.conjTranspose * v = p)
    (hv₂ : v * v.conjTranspose = q) (hp : IsStarProjection p) :
    IsSelfAdjoint (stabilizedUnitary v hv₁ hv₂ hp : CStarMatrix (m ⊕ n) (m ⊕ n) A) := by
  have hq : IsStarProjection q := MurrayVonNeumannEquiv.isStarProjection_right ⟨v, hv₁, hv₂⟩ hp
  rw [isSelfAdjoint_iff, coe_stabilizedUnitary, fromBlocks_star, star_sub, star_one,
    hp.isSelfAdjoint.star_eq, star_sub, star_one, hq.isSelfAdjoint.star_eq,
    conjTranspose_conjTranspose]

/-- `stabilizedUnitary` conjugates `fromBlocks p 0 0 0` to `fromBlocks 0 0 0 q`. -/
theorem stabilizedUnitary_conj (v : CStarMatrix n m A) (hv₁ : v.conjTranspose * v = p)
    (hv₂ : v * v.conjTranspose = q) (hp : IsStarProjection p) :
    (stabilizedUnitary v hv₁ hv₂ hp : CStarMatrix (m ⊕ n) (m ⊕ n) A) *
        fromBlocks p 0 0 0 *
        star (stabilizedUnitary v hv₁ hv₂ hp : CStarMatrix (m ⊕ n) (m ⊕ n) A) =
      fromBlocks 0 0 0 q := by
  obtain ⟨hvp, -, -, -⟩ := mul_eq_self_of_conjTranspose_mul_self hv₁ hv₂ hp.isIdempotentElem
  rw [(isSelfAdjoint_stabilizedUnitary v hv₁ hv₂ hp).star_eq, coe_stabilizedUnitary]
  simp only [fromBlocks_mul, CStarMatrix.mul_zero, CStarMatrix.zero_mul, CStarMatrix.sub_mul,
    CStarMatrix.mul_sub, CStarMatrix.one_mul, CStarMatrix.mul_one, hp.isIdempotentElem.eq,
    hv₂, hvp, sub_self, add_zero]

end StabilizedUnitary

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
  have hw_sa := isSelfAdjoint_stabilizedUnitary v hv₁ hv₂ hp
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
  refine ⟨rot * w, ?_,
    by simpa only [one_mul] using (joined_one_blockRotation (n := n) (A := A) (π / 2)).mul hw_join⟩
  calc ((rot * w : unitary _) : CStarMatrix (n ⊕ n) (n ⊕ n) A) * fromBlocks p 0 0 0 *
          star ((rot * w : unitary _) : CStarMatrix (n ⊕ n) (n ⊕ n) A)
      = (rot : CStarMatrix (n ⊕ n) (n ⊕ n) A) * ((w : CStarMatrix (n ⊕ n) (n ⊕ n) A) *
          fromBlocks p 0 0 0 * star (w : CStarMatrix (n ⊕ n) (n ⊕ n) A)) *
          star (rot : CStarMatrix (n ⊕ n) (n ⊕ n) A) := by
        simp only [Submonoid.coe_mul, star_mul]; noncomm_ring
    _ = fromBlocks q 0 0 0 := by rw [hw_conj]; exact blockRotation_pi_div_two_conj 0 q

private theorem path_of_unitization_unitary_path {k A : Type*} [Fintype k] [DecidableEq k]
    [NonUnitalCStarAlgebra A] {P Q : CStarMatrix k k A} (hP : IsStarProjection P)
    {u : unitary (CStarMatrix k k A⁺¹)}
    (hconj : (u : CStarMatrix k k A⁺¹) * P.map (Unitization.inr : A → A⁺¹) *
      star (u : CStarMatrix k k A⁺¹) = Q.map (Unitization.inr : A → A⁺¹))
    (hjoin : Joined (1 : unitary (CStarMatrix k k A⁺¹)) u) :
    ∃ γ : Path P Q, ∀ t : I, IsStarProjection (γ t) := by
  let ι : A →⋆ₙₐ[ℂ] A⁺¹ := Unitization.inrNonUnitalStarAlgHom ℂ A
  have hι : (ι : A → A⁺¹) = Unitization.inr := funext fun _ => rfl
  obtain ⟨δ⟩ := hjoin
  have hfst (t : I) :
      ((δ t : CStarMatrix k k A⁺¹) * P.map ι * star (δ t : CStarMatrix k k A⁺¹)).map
        (Unitization.fstHom ℂ A) = 0 := by
    rw [CStarMatrix.map_mul (Unitization.fstHom ℂ A), CStarMatrix.map_mul (Unitization.fstHom ℂ A),
      map_fstHom_map_inr P, mul_zero, zero_mul]
  let f : I → CStarMatrix k k A := fun t =>
    ((δ t : CStarMatrix k k A⁺¹) * P.map ι * star (δ t : CStarMatrix k k A⁺¹)).map
      (fun x : A⁺¹ => x.snd)
  have hf_inr (t : I) : (f t).map ι =
      (δ t : CStarMatrix k k A⁺¹) * P.map ι * star (δ t : CStarMatrix k k A⁺¹) :=
    map_inr_map_snd_of_map_fstHom_eq_zero (hfst t)
  have hf_cont : Continuous f := by
    have hδ : Continuous (fun t : I => ((δ t : unitary (CStarMatrix k k A⁺¹)) :
        CStarMatrix k k A⁺¹)) := continuous_subtype_val.comp δ.continuous
    exact (continuous_map (Unitization.continuous_snd (𝕜 := ℂ) (A := A))).comp
      ((hδ.mul continuous_const).mul hδ.star)
  have hinj : Function.Injective (fun M : CStarMatrix k k A => M.map (ι : A → A⁺¹)) := by
    simpa only [hι] using CStarMatrix.map_injective (m := k) (n := k)
      (Unitization.inr_injective (R := ℂ) (A := A))
  have hP' : IsStarProjection (P.map ι) := hP.map (CStarMatrix.mapₙₐ ι)
  refine ⟨⟨⟨f, hf_cont⟩, hinj (by simp [hf_inr 0, δ.source]),
    hinj (by dsimp only; rw [hf_inr 1, δ.target, hι]; exact hconj)⟩, fun t => ?_⟩
  have hproj' : IsStarProjection ((f t).map ι) := by
    rw [hf_inr t]
    simpa only [Unitary.conjStarAlgAut_apply] using
      hP'.map (Unitary.conjStarAlgAut ℂ (CStarMatrix k k A⁺¹) (δ t))
  exact ⟨hinj (by dsimp only; rw [CStarMatrix.map_mul ι]; exact hproj'.isIdempotentElem.eq),
    hinj (by
      dsimp only; rw [star_eq_conjTranspose, map_conjTranspose ι, ← star_eq_conjTranspose]
      exact hproj'.isSelfAdjoint.star_eq)⟩

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
  simpa only [← hι, fromBlocks_map, CStarMatrix.map_zero (_root_.map_zero ι)] using hconj

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
  simpa only [← hι, fromBlocks_map, CStarMatrix.map_zero (_root_.map_zero ι)] using hconj

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
`exp(i π r / 2) * diag(1, 0) * exp(-i π r / 2) = [[1 / 2, i / 2], [-i / 2, 1 / 2]]`. -/
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
    dsimp only [u]; rw [hr.coe_expUnitary_smul (π / 2) hmem, hexp]
    ext (i | i) (j | j) <;> simp [r, w, ← fromBlocks_one] <;> ring
  have hsu : star (u : CStarMatrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ) =
      fromBlocks (((1 - Complex.I) / 2 : ℂ) • 1) (((1 + Complex.I) / 2 : ℂ) • 1)
        (((1 + Complex.I) / 2 : ℂ) • 1) (((1 - Complex.I) / 2 : ℂ) • 1) := by
    rw [hu, fromBlocks_star]; ext (i | i) (j | j) <;> simp [Complex.conj_I, sub_eq_add_neg]
  rw [hsu, hu]
  ext (i | i) (j | j) <;> simp [p, fromBlocks_mul] <;> ring_nf <;> simp [Complex.I_sq] <;> ring

end Checks

end CStarMatrix

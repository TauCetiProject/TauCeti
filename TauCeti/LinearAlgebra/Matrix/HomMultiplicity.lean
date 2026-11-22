/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.StarAlgHom
public import Mathlib.Data.Matrix.Basis
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.RingTheory.Idempotents
public import TauCeti.Algebra.Star.PartialIsometry
public import TauCeti.LinearAlgebra.Matrix.TensorProduct
import Mathlib.Algebra.Star.StarProjection
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Trace
import TauCeti.LinearAlgebra.Trace.Idempotent

/-!
# Homomorphisms between full matrix algebras

Let `f : Mₙ(K) → Mₘ(K)` be a possibly nonunital algebra homomorphism between full matrix algebras
over a field `K`. The images `f (Eᵢᵢ)` of the diagonal matrix units are orthogonal idempotents of
one common rank, the **multiplicity** `Matrix.homMultiplicity f` of `f`: the number of times the
defining representation of `Mₙ(K)` occurs in `Kᵐ` through `f`. It determines the trace of `f`,
`tr (f x) = homMultiplicity f * tr x`, and the rank of the image of every matrix,
`rank (f x) = homMultiplicity f * rank x`. In particular `n * homMultiplicity f ≤ m`, with
equality exactly when `f` is unital, and the multiplicity of a composite is the product of the
multiplicities. For `n ≠ 0`, every multiplicity allowed by this inequality is realised by a
`⋆`-homomorphism, unital in the case of equality, and a unital homomorphism `Mₙ(K) → Mₘ(K)` exists
exactly when `n ∣ m`.

The rank of an idempotent is its class in `K₀(Mₙ(K)) = ℤ`, so the multiplicity is the map induced
by `f` on `K₀` in these coordinates. Two `⋆`-homomorphisms into a unital `⋆`-ring are conjugate by
a unitary as soon as the images of one diagonal matrix unit, and the complements of the images of
the identity, are the initial and final projections of partial isometries
(`NonUnitalStarAlgHom.exists_mem_unitary_mul_map_mul_star_eq`). Over `ℂ` this reduces the unitary
classification of `⋆`-homomorphisms `Mₙ(ℂ) → Mₘ(ℂ)` to the multiplicity
(`TauCeti/Analysis/Matrix/HomMultiplicity.lean`).

## Main definitions

* `Matrix.homMultiplicity f`: the multiplicity of a homomorphism `f : Mₙ(K) → Mₘ(K)`.

## Main statements

* `Matrix.orthogonalIdempotents_map_single`, `Matrix.map_single_mul_map_single` and
  `Matrix.star_map_single`: the images of the matrix units under a homomorphism out of `Mₙ(R)`
  into any ring multiply like matrix units, and a `⋆`-homomorphism maps adjoints to adjoints.
* `Matrix.homMultiplicity_eq_rank_map_single`: the multiplicity is the rank of the image of any
  diagonal matrix unit.
* `Matrix.homMultiplicity_eq_zero_iff`, `NonUnitalAlgHom.homMultiplicity_zero` and
  `NonUnitalStarAlgHom.homMultiplicity_zero`: the multiplicity vanishes exactly for the zero
  homomorphism.
* `Matrix.trace_map_eq_homMultiplicity_mul` and `Matrix.rank_map_eq_homMultiplicity_mul`: the
  trace and the rank of `f x`.
* `Matrix.card_mul_homMultiplicity_le` and `Matrix.card_mul_homMultiplicity_eq_card_iff`:
  `n * homMultiplicity f ≤ m`, with equality exactly for unital `f`; hence
  `Matrix.card_dvd_card_of_map_one`.
* `Matrix.homMultiplicity_eq_mul_of_apply_eq` and its specialisations
  `NonUnitalAlgHom.homMultiplicity_comp`, `AlgHom.homMultiplicity_comp`,
  `NonUnitalStarAlgHom.homMultiplicity_comp` and `StarAlgHom.homMultiplicity_comp`: the
  multiplicity of a composite.
* `AlgHom.homMultiplicity_id` (and its variants) and
  `Matrix.homMultiplicity_kroneckerOneStarAlgHom`: the identity has multiplicity one and
  `x ↦ x ⊗ 1_ι` has multiplicity `card ι`.
* `Matrix.exists_nonUnitalStarAlgHom_homMultiplicity_eq_iff`,
  `Matrix.exists_starAlgHom_homMultiplicity_eq_iff` and `Matrix.nonempty_starAlgHom_iff`: which
  multiplicities occur.
* `NonUnitalStarAlgHom.exists_mem_unitary_mul_map_mul_star_eq`: unitary conjugacy of two
  `⋆`-homomorphisms `Mₙ(R) → B` from partial isometries implementing the equivalences of the
  relevant projections.

## References

* M. Rørdam, F. Larsen and N. Laustsen, *An Introduction to K-Theory for C⋆-Algebras*,
  Cambridge University Press (2000), Chapter 7 (homomorphisms between finite-dimensional
  C⋆-algebras and their multiplicity matrices).
* K. R. Davidson, *C⋆-Algebras by Example*, Fields Institute Monographs 6 (1996), Chapter III.
-/

public section

open scoped Kronecker

namespace Matrix

variable {K n m l F : Type*} [Field K] [Fintype n] [DecidableEq n]

/-- The **multiplicity** of a homomorphism `f : Mₙ(K) → Mₘ(K)`: the rank of `f 1` divided by `n`.
For an algebra homomorphism this is the common rank of the images of the diagonal matrix units
(`Matrix.homMultiplicity_eq_rank_map_single`), the number of copies of the defining
representation of `Mₙ(K)` in `Kᵐ`. -/
noncomputable def homMultiplicity [FunLike F (Matrix n n K) (Matrix m m K)] (f : F) : ℕ :=
  (f 1).rank / Fintype.card n

/-- A homomorphism out of the zero algebra `M₀(K)` has multiplicity zero. -/
@[simp]
theorem homMultiplicity_of_isEmpty [IsEmpty n] [FunLike F (Matrix n n K) (Matrix m m K)] (f : F) :
    homMultiplicity f = 0 := by
  simp [homMultiplicity]

section MatrixUnits

variable {R B : Type*} [Semiring R] [FunLike F (Matrix n n R) B]

/-- The image of a diagonal matrix unit is idempotent. -/
theorem isIdempotentElem_map_single [Mul B] [MulHomClass F (Matrix n n R) B] (f : F) (i : n) :
    IsIdempotentElem (f (single i i 1)) :=
  IsIdempotentElem.map (by simp [IsIdempotentElem]) f

/-- The images of the diagonal matrix units are orthogonal idempotents. -/
theorem orthogonalIdempotents_map_single [Semiring B] [NonUnitalRingHomClass F (Matrix n n R) B]
    (f : F) : OrthogonalIdempotents fun i : n => f (single i i 1) :=
  ⟨isIdempotentElem_map_single f, fun i j hij => by simp [← map_mul, hij]⟩

/-- The images of the matrix units multiply like matrix units. -/
theorem map_single_mul_map_single [NonUnitalNonAssocSemiring B]
    [NonUnitalRingHomClass F (Matrix n n R) B] (f : F) (i j k l : n) :
    f (single i j 1) * f (single k l 1) = if j = k then f (single i l 1) else 0 := by
  rw [← map_mul]
  split_ifs with h
  · rw [h, single_mul_single_same, mul_one]
  · simp [h]

omit [Fintype n] in
/-- A `⋆`-homomorphism maps the adjoint `Eⱼᵢ` of a matrix unit `Eᵢⱼ` to the adjoint of its
image. -/
theorem star_map_single [StarRing R] [Star B] [StarHomClass F (Matrix n n R) B] (f : F)
    (i j : n) : star (f (single i j 1)) = f (single j i 1) := by
  rw [← map_star, star_eq_conjTranspose, conjTranspose_single, star_one]

end MatrixUnits

section NonUnitalAlgHomClass

variable [Fintype m] [FunLike F (Matrix n n K) (Matrix m m K)]
  [NonUnitalAlgHomClass F K (Matrix n n K) (Matrix m m K)] (f : F)

omit [DecidableEq n] in
/-- The image of a product `a * b * c` has rank at most that of the image of `b`. -/
private theorem rank_map_mul_mul_le (a b c : Matrix n n K) : (f (a * b * c)).rank ≤ (f b).rank := by
  rw [map_mul, map_mul]
  exact (rank_mul_le_left _ _).trans (rank_mul_le_right _ _)

/-- `f (Eⱼⱼ) = f (Eⱼᵢ) f (Eᵢᵢ) f (Eᵢⱼ)`, so its rank is at most that of `f (Eᵢᵢ)`. -/
private theorem rank_map_single_le (i j : n) :
    (f (single j j 1)).rank ≤ (f (single i i 1)).rank := by
  have h : single j j (1 : K) = single j i 1 * single i i 1 * single i j 1 := by
    simp only [single_mul_single_same, mul_one]
  rw [h]
  exact rank_map_mul_mul_le f _ _ _

/-- The images of the diagonal matrix units all have the same rank. -/
theorem rank_map_single_eq (i j : n) : (f (single i i 1)).rank = (f (single j j 1)).rank :=
  le_antisymm (rank_map_single_le f j i) (rank_map_single_le f i j)

/-- The image of an off-diagonal matrix unit `Eₖₗ = Eₖₗ Eₗₗ` is traceless, since its trace is that
of `f (Eₗₗ Eₖₗ) = 0`; the image of a diagonal one is an idempotent whose trace is its rank. -/
private theorem trace_map_single (i k l : n) :
    (f (single k l 1)).trace = if k = l then ((f (single i i 1)).rank : K) else 0 := by
  split_ifs with hkl
  · subst hkl
    rw [IsIdempotentElem.trace_eq_rank (isIdempotentElem_map_single f k), rank_map_single_eq f k i]
  · calc (f (single k l 1)).trace = (f (single k l 1) * f (single l l 1)).trace := by
          rw [← map_mul, single_mul_single_same, mul_one]
      _ = (f (single l l 1) * f (single k l 1)).trace := trace_mul_comm _ _
      _ = 0 := by
          rw [← map_mul]
          simp [Ne.symm hkl]

private theorem trace_map_eq_rank_map_single_mul (i : n) (x : Matrix n n K) :
    (f x).trace = (f (single i i 1)).rank * x.trace := by
  conv_lhs => rw [matrix_eq_sum_single x]
  have hsingle (k l : n) : single k l (x k l) = x k l • single k l (1 : K) := by
    rw [smul_single, smul_eq_mul, mul_one]
  simp only [hsingle, map_sum, map_smul, trace_sum, trace_smul, trace_map_single f i,
    smul_eq_mul, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [trace, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

/-- `f 1` is the sum of the `n` orthogonal idempotents `f (Eᵢᵢ)`, each of rank
`homMultiplicity f`. -/
private theorem card_mul_rank_map_single (i : n) :
    Fintype.card n * (f (single i i 1)).rank = (f 1).rank := by
  classical
  rw [← sum_single_one, map_sum,
    OrthogonalIdempotents.rank_sum (orthogonalIdempotents_map_single f),
    Finset.sum_congr rfl fun j _ => rank_map_single_eq f j i, Finset.sum_const, Finset.card_univ,
    smul_eq_mul]

/-- The multiplicity is the rank of the image of any diagonal matrix unit. -/
theorem homMultiplicity_eq_rank_map_single (i : n) :
    homMultiplicity f = (f (single i i 1)).rank := by
  rw [homMultiplicity, ← card_mul_rank_map_single f i,
    Nat.mul_div_cancel_left _ (Fintype.card_pos_iff.mpr ⟨i⟩)]

/-- The rank of `f 1` is `n` times the multiplicity. -/
theorem card_mul_homMultiplicity : Fintype.card n * homMultiplicity f = (f 1).rank := by
  cases isEmpty_or_nonempty n with
  | inl _ => simp [Subsingleton.elim (1 : Matrix n n K) 0]
  | inr h =>
    obtain ⟨i⟩ := h
    rw [homMultiplicity_eq_rank_map_single f i, card_mul_rank_map_single]

/-- **The trace of a homomorphism between matrix algebras**: `tr (f x) = μ * tr x`, where `μ` is
the multiplicity of `f`. -/
theorem trace_map_eq_homMultiplicity_mul (x : Matrix n n K) :
    (f x).trace = homMultiplicity f * x.trace := by
  cases isEmpty_or_nonempty n with
  | inl _ => simp [Subsingleton.elim x 0]
  | inr h =>
    obtain ⟨i⟩ := h
    rw [homMultiplicity_eq_rank_map_single f i, trace_map_eq_rank_map_single_mul]

/-- The image of a matrix `x` has rank `homMultiplicity f * rank x`. For an idempotent `x` this
says that, in the coordinates `K₀(Mₙ(K)) = ℤ` given by the rank, `f` acts on `K₀` as
multiplication by its multiplicity. -/
theorem rank_map_eq_homMultiplicity_mul (x : Matrix n n K) :
    (f x).rank = homMultiplicity f * x.rank := by
  classical
  -- `V x U = N` for invertible `V`, `U` and `N = ∑ₖ Eₖₖ`, the sum over `rank x` indices
  obtain ⟨_, _, e, ⟨V, rfl⟩, ⟨U, rfl⟩, h⟩ := exists_rank_normal_form x
  set N : Matrix n n K := (fromBlocks 1 0 0 0).submatrix e e
  let σ : Fin x.rank ↪ n := Function.Embedding.inl.trans e.symm.toEmbedding
  have hN : N = ∑ k, single (σ k) (σ k) (1 : K) := by
    ext a b
    obtain ⟨p, rfl⟩ := e.symm.surjective a
    obtain ⟨q, rfl⟩ := e.symm.surjective b
    simp only [N, submatrix_apply, Equiv.apply_symm_apply, Matrix.sum_apply]
    rcases p with k | k <;> rcases q with l | l <;>
      simp [σ, single_apply, ite_and, eq_comm, Matrix.one_apply]
  have hx : x = (↑V⁻¹ : Matrix n n K) * N * (↑U⁻¹ : Matrix n n K) := by
    rw [← h, mul_assoc (V : Matrix n n K), Units.inv_mul_cancel_left, Units.mul_inv_cancel_right]
  have hfN : (f N).rank = homMultiplicity f * x.rank := by
    have hsum := OrthogonalIdempotents.rank_sum
      ((orthogonalIdempotents_map_single f).embedding σ) Finset.univ
    simp only [Function.comp_apply] at hsum
    rw [hN, map_sum, hsum]
    simp [← homMultiplicity_eq_rank_map_single, mul_comm]
  refine le_antisymm ?_ ?_
  · have hle := rank_map_mul_mul_le f (↑V⁻¹ : Matrix n n K) N (↑U⁻¹ : Matrix n n K)
    rw [← hx] at hle
    exact hle.trans hfN.le
  · rw [← hfN, ← h]
    exact rank_map_mul_mul_le f _ _ _

/-- A homomorphism between matrix algebras has multiplicity zero exactly when it is zero. -/
theorem homMultiplicity_eq_zero_iff : homMultiplicity f = 0 ↔ ∀ x, f x = 0 := by
  classical
  refine ⟨fun h x => ?_, fun h => by simp [homMultiplicity, h]⟩
  -- a matrix of rank zero is zero
  have hx : (f x).rank = 0 := by rw [rank_map_eq_homMultiplicity_mul, h, zero_mul]
  rw [← finrank_range_mulVecLin, Submodule.finrank_eq_zero, LinearMap.range_eq_bot] at hx
  exact toLin'.injective (by rw [toLin'_apply', hx, map_zero])

/-- A homomorphism `Mₙ(K) → Mₘ(K)` of multiplicity `μ` has `n * μ ≤ m`. -/
theorem card_mul_homMultiplicity_le : Fintype.card n * homMultiplicity f ≤ Fintype.card m :=
  (card_mul_homMultiplicity f).trans_le (rank_le_card_width _)

/-- A homomorphism `Mₙ(K) → Mₘ(K)` of multiplicity `μ` has `n * μ = m` exactly when it is
unital. -/
theorem card_mul_homMultiplicity_eq_card_iff [DecidableEq m] :
    Fintype.card n * homMultiplicity f = Fintype.card m ↔ f 1 = 1 := by
  rw [card_mul_homMultiplicity]
  refine ⟨fun h => ?_, fun h => by rw [h, rank_one]⟩
  -- an idempotent of full rank is invertible, hence `1`
  have he : IsIdempotentElem (f 1) := IsIdempotentElem.one.map f
  exact (IsIdempotentElem.iff_eq_one_of_isUnit
    (mulVec_surjective_iff_isUnit.mp (mulVec_surjective_iff_rank_eq_card.mpr h))).mp he

/-- If there is a unital homomorphism `Mₙ(K) → Mₘ(K)`, then `n ∣ m`. -/
theorem card_dvd_card_of_map_one [DecidableEq m] (hf : f 1 = 1) : Fintype.card n ∣ Fintype.card m :=
  ⟨homMultiplicity f, ((card_mul_homMultiplicity_eq_card_iff f).mpr hf).symm⟩

end NonUnitalAlgHomClass

section Zero

variable [Fintype m]

/-- The zero homomorphism has multiplicity zero. -/
@[simp]
theorem _root_.NonUnitalAlgHom.homMultiplicity_zero :
    homMultiplicity (0 : Matrix n n K →ₙₐ[K] Matrix m m K) = 0 := by
  simp [homMultiplicity]

/-- The zero `⋆`-homomorphism has multiplicity zero. -/
@[simp]
theorem _root_.NonUnitalStarAlgHom.homMultiplicity_zero [StarRing K] :
    homMultiplicity (0 : Matrix n n K →⋆ₙₐ[K] Matrix m m K) = 0 := by
  simp [homMultiplicity]

end Zero

section Comp

variable [Fintype m] [DecidableEq m] [Fintype l]

/-- The multiplicity of a homomorphism that agrees pointwise with a composite `g ∘ f` of
homomorphisms between matrix algebras is the product of the multiplicities. -/
theorem homMultiplicity_eq_mul_of_apply_eq {G H : Type*}
    [FunLike F (Matrix n n K) (Matrix m m K)]
    [NonUnitalAlgHomClass F K (Matrix n n K) (Matrix m m K)]
    [FunLike G (Matrix m m K) (Matrix l l K)]
    [NonUnitalAlgHomClass G K (Matrix m m K) (Matrix l l K)]
    [FunLike H (Matrix n n K) (Matrix l l K)] (f : F) (g : G) (h : H)
    (hgf : ∀ x, h x = g (f x)) : homMultiplicity h = homMultiplicity g * homMultiplicity f := by
  cases isEmpty_or_nonempty n with
  | inl _ => simp
  | inr hn =>
    rw [homMultiplicity, hgf, rank_map_eq_homMultiplicity_mul g, ← card_mul_homMultiplicity f,
      Nat.mul_left_comm, Nat.mul_div_cancel_left _ Fintype.card_pos]

/-- The multiplicity of a composite of homomorphisms between matrix algebras is the product of
the multiplicities. -/
@[simp]
theorem _root_.NonUnitalAlgHom.homMultiplicity_comp (g : Matrix m m K →ₙₐ[K] Matrix l l K)
    (f : Matrix n n K →ₙₐ[K] Matrix m m K) :
    homMultiplicity (g.comp f) = homMultiplicity g * homMultiplicity f :=
  homMultiplicity_eq_mul_of_apply_eq f g _ (NonUnitalAlgHom.comp_apply g f)

/-- The multiplicity of a composite of unital homomorphisms between matrix algebras is the
product of the multiplicities. -/
@[simp]
theorem _root_.AlgHom.homMultiplicity_comp [DecidableEq l] (g : Matrix m m K →ₐ[K] Matrix l l K)
    (f : Matrix n n K →ₐ[K] Matrix m m K) :
    homMultiplicity (g.comp f) = homMultiplicity g * homMultiplicity f :=
  homMultiplicity_eq_mul_of_apply_eq f g _ (AlgHom.comp_apply g f)

/-- The multiplicity of a composite of `⋆`-homomorphisms between matrix algebras is the product
of the multiplicities. -/
@[simp]
theorem _root_.NonUnitalStarAlgHom.homMultiplicity_comp [Star K]
    (g : Matrix m m K →⋆ₙₐ[K] Matrix l l K) (f : Matrix n n K →⋆ₙₐ[K] Matrix m m K) :
    homMultiplicity (g.comp f) = homMultiplicity g * homMultiplicity f :=
  homMultiplicity_eq_mul_of_apply_eq f g _ (NonUnitalStarAlgHom.comp_apply g f)

/-- The multiplicity of a composite of unital `⋆`-homomorphisms between matrix algebras is the
product of the multiplicities. -/
@[simp]
theorem _root_.StarAlgHom.homMultiplicity_comp [DecidableEq l] [Star K]
    (g : Matrix m m K →⋆ₐ[K] Matrix l l K) (f : Matrix n n K →⋆ₐ[K] Matrix m m K) :
    homMultiplicity (g.comp f) = homMultiplicity g * homMultiplicity f :=
  homMultiplicity_eq_mul_of_apply_eq f g _ (StarAlgHom.comp_apply g f)

end Comp

section Id

variable [Nonempty n]

/-- The identity of `Mₙ(K)`, for `n ≠ 0`, has multiplicity one. -/
@[simp]
theorem _root_.NonUnitalAlgHom.homMultiplicity_id :
    homMultiplicity (NonUnitalAlgHom.id K (Matrix n n K)) = 1 := by
  simp [homMultiplicity, Nat.div_self Fintype.card_pos]

/-- The identity of `Mₙ(K)`, for `n ≠ 0`, has multiplicity one. -/
@[simp]
theorem _root_.AlgHom.homMultiplicity_id : homMultiplicity (AlgHom.id K (Matrix n n K)) = 1 := by
  simp [homMultiplicity, Nat.div_self Fintype.card_pos]

/-- The identity of `Mₙ(K)`, for `n ≠ 0`, has multiplicity one. -/
@[simp]
theorem _root_.NonUnitalStarAlgHom.homMultiplicity_id [Star K] :
    homMultiplicity (NonUnitalStarAlgHom.id K (Matrix n n K)) = 1 := by
  simp [homMultiplicity, Nat.div_self Fintype.card_pos]

/-- The identity of `Mₙ(K)`, for `n ≠ 0`, has multiplicity one. -/
@[simp]
theorem _root_.StarAlgHom.homMultiplicity_id [Star K] :
    homMultiplicity (StarAlgHom.id K (Matrix n n K)) = 1 := by
  simp [homMultiplicity, Nat.div_self Fintype.card_pos]

end Id

section Existence

variable [StarRing K] [Fintype m]

/-- For `n ≠ 0`, the map `x ↦ x ⊗ 1_ι` has multiplicity `card ι`. -/
@[simp]
theorem homMultiplicity_kroneckerOneStarAlgHom [Nonempty n] (ι : Type*) [Fintype ι]
    [DecidableEq ι] : homMultiplicity (kroneckerOneStarAlgHom K ι : Matrix n n K →⋆ₐ[K] _) =
      Fintype.card ι := by
  refine Nat.eq_of_mul_eq_mul_left (Fintype.card_pos (α := n)) ?_
  rw [(card_mul_homMultiplicity_eq_card_iff _).mpr (map_one _), Fintype.card_prod]

/-- For `n * μ ≤ m`, the map `x ↦ (x ⊗ 1_μ) ⊕ 0`, reindexed to `m`, is a `⋆`-homomorphism
`Mₙ(K) → Mₘ(K)` with `rank (φ 1) = n * μ`. -/
private theorem exists_nonUnitalStarAlgHom_rank_map_one_eq {μ : ℕ}
    (hμ : Fintype.card n * μ ≤ Fintype.card m) :
    ∃ φ : Matrix n n K →⋆ₙₐ[K] Matrix m m K, (φ 1).rank = Fintype.card n * μ := by
  classical
  let r := Fintype.card m - Fintype.card n * μ
  let e : (n × Fin μ) ⊕ Fin r ≃ m := Fintype.equivOfCardEq (by simp [r]; omega)
  let corner : Matrix (n × Fin μ) (n × Fin μ) K →⋆ₙₐ[K]
      Matrix ((n × Fin μ) ⊕ Fin r) ((n × Fin μ) ⊕ Fin r) K :=
    { toFun y := fromBlocks y 0 0 0
      map_smul' c y := by simp [fromBlocks_smul]
      map_zero' := by simp
      map_add' y z := by simp [fromBlocks_add]
      map_mul' y z := by simp [fromBlocks_multiply]
      map_star' y := by simp [star_eq_conjTranspose, fromBlocks_conjTranspose] }
  have hrank : (fromBlocks (1 : Matrix (n × Fin μ) (n × Fin μ) K) 0 0
      (0 : Matrix (Fin r) (Fin r) K)).rank = Fintype.card n * μ := by
    rw [← diagonal_one, ← diagonal_zero, fromBlocks_diagonal, rank_diagonal]
    simp [Fintype.card_subtype, Finset.card_filter, Fintype.sum_sum_type]
  refine ⟨(reindexStarAlgEquiv K K e).toNonUnitalStarAlgHom.comp
    (corner.comp (kroneckerOneStarAlgHom K (Fin μ)).toNonUnitalStarAlgHom), ?_⟩
  simpa [corner] using hrank

/-- **Realisation of multiplicities.** For `n ≠ 0`, a `⋆`-homomorphism `Mₙ(K) → Mₘ(K)` of
multiplicity `μ` exists exactly when `n * μ ≤ m`. -/
theorem exists_nonUnitalStarAlgHom_homMultiplicity_eq_iff [Nonempty n] {μ : ℕ} :
    (∃ φ : Matrix n n K →⋆ₙₐ[K] Matrix m m K, homMultiplicity φ = μ) ↔
      Fintype.card n * μ ≤ Fintype.card m := by
  refine ⟨fun ⟨φ, hφ⟩ => hφ ▸ card_mul_homMultiplicity_le φ, fun hμ => ?_⟩
  obtain ⟨φ, hφ⟩ := exists_nonUnitalStarAlgHom_rank_map_one_eq (K := K) hμ
  exact ⟨φ, Nat.eq_of_mul_eq_mul_left Fintype.card_pos ((card_mul_homMultiplicity φ).trans hφ)⟩

/-- For `n * μ = m`, the map `x ↦ x ⊗ 1_μ`, reindexed to `m`, is a unital `⋆`-homomorphism. -/
private theorem nonempty_starAlgHom_of_card_mul_eq [DecidableEq m] {μ : ℕ}
    (hμ : Fintype.card n * μ = Fintype.card m) :
    Nonempty (Matrix n n K →⋆ₐ[K] Matrix m m K) :=
  let e : n × Fin μ ≃ m := Fintype.equivOfCardEq (by simpa using hμ)
  ⟨(reindexStarAlgEquiv K K e).toStarAlgHom.comp (kroneckerOneStarAlgHom K (Fin μ))⟩

/-- **Realisation of unital multiplicities.** For `n ≠ 0`, a unital `⋆`-homomorphism
`Mₙ(K) → Mₘ(K)` of multiplicity `μ` exists exactly when `n * μ = m`. -/
theorem exists_starAlgHom_homMultiplicity_eq_iff [DecidableEq m] [Nonempty n] {μ : ℕ} :
    (∃ φ : Matrix n n K →⋆ₐ[K] Matrix m m K, homMultiplicity φ = μ) ↔
      Fintype.card n * μ = Fintype.card m := by
  refine ⟨fun ⟨φ, hφ⟩ => hφ ▸ (card_mul_homMultiplicity_eq_card_iff φ).mpr (map_one φ),
    fun hμ => ?_⟩
  obtain ⟨φ⟩ := nonempty_starAlgHom_of_card_mul_eq (K := K) hμ
  exact ⟨φ, Nat.eq_of_mul_eq_mul_left (Fintype.card_pos (α := n))
    (((card_mul_homMultiplicity_eq_card_iff φ).mpr (map_one φ)).trans hμ.symm)⟩

/-- A unital `⋆`-homomorphism `Mₙ(K) → Mₘ(K)` exists exactly when `n ∣ m`. -/
theorem nonempty_starAlgHom_iff [DecidableEq m] :
    Nonempty (Matrix n n K →⋆ₐ[K] Matrix m m K) ↔ Fintype.card n ∣ Fintype.card m :=
  ⟨fun ⟨φ⟩ => card_dvd_card_of_map_one φ (map_one φ),
    fun ⟨_, hμ⟩ => nonempty_starAlgHom_of_card_mul_eq hμ.symm⟩

end Existence

section Unitary

open TauCeti

variable {R B : Type*} [CommSemiring R] [StarRing R] [Ring B] [StarRing B] [Algebra R B]

/-- Products of images of matrix units, associated to the right. -/
private theorem map_single_mul_map_single_mul (φ : Matrix n n R →⋆ₙₐ[R] B) (i j k l : n)
    (x : B) : φ (single i j 1) * (φ (single k l 1) * x) =
      if j = k then φ (single i l 1) * x else 0 := by
  rw [← mul_assoc, map_single_mul_map_single, ite_mul, zero_mul]

variable (φ ψ : Matrix n n R →⋆ₙₐ[R] B) (i : n) {v : B}

/-- The element `V = ∑ₖ ψ(Eₖᵢ) v φ(Eᵢₖ)` intertwines `φ` and `ψ` on matrix units. -/
private theorem sum_mul_map_single (k l : n) :
    (∑ j, ψ (single j i 1) * v * φ (single i j 1)) * φ (single k l 1) =
      ψ (single k l 1) * ∑ j, ψ (single j i 1) * v * φ (single i j 1) := by
  simp [Finset.sum_mul, Finset.mul_sum, mul_assoc, map_single_mul_map_single_mul,
    map_single_mul_map_single]

/-- The element `V = ∑ₖ ψ(Eₖᵢ) v φ(Eᵢₖ)` intertwines `φ` and `ψ`. -/
private theorem sum_mul_map (x : Matrix n n R) :
    (∑ j, ψ (single j i 1) * v * φ (single i j 1)) * φ x =
      ψ x * ∑ j, ψ (single j i 1) * v * φ (single i j 1) := by
  induction x using Matrix.induction_on' with
  | h_zero => simp
  | h_add p q hp hq => rw [map_add, map_add, mul_add, add_mul, hp, hq]
  | h_std_basis k l c =>
    have hc : single k l c = c • single k l (1 : R) := by rw [smul_single, smul_eq_mul, mul_one]
    rw [hc, map_smul, map_smul, mul_smul_comm, smul_mul_assoc, sum_mul_map_single]

private theorem map_one_mul_sum :
    ψ 1 * ∑ j, ψ (single j i 1) * v * φ (single i j 1) =
      ∑ j, ψ (single j i 1) * v * φ (single i j 1) := by
  simp only [Finset.mul_sum, ← mul_assoc, ← map_mul, one_mul]

variable {φ ψ i}

/-- If `v` is a partial isometry from `φ(Eᵢᵢ)` to `ψ(Eᵢᵢ)`, then `V = ∑ₖ ψ(Eₖᵢ) v φ(Eᵢₖ)` is a
partial isometry from `φ 1` to `ψ 1`: its initial projection is `φ 1`. -/
private theorem star_sum_mul_sum (hv : IsPartialIsometry v) (hvφ : star v * v = φ (single i i 1))
    (hvψ : v * star v = ψ (single i i 1)) :
    star (∑ j, ψ (single j i 1) * v * φ (single i j 1)) *
      ∑ j, ψ (single j i 1) * v * φ (single i j 1) = φ 1 := by
  have hψv (y : B) : ψ (single i i 1) * (v * y) = v * y := by
    rw [← mul_assoc, ← hvψ, hv.mul_star_mul_self]
  have hvv (y : B) : star v * (v * y) = φ (single i i 1) * y := by rw [← mul_assoc, hvφ]
  simp only [star_sum, star_mul, star_map_single, Finset.sum_mul, Finset.mul_sum, mul_assoc,
    map_single_mul_map_single_mul, map_single_mul_map_single, hψv, hvv, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [← map_sum, sum_single_one]

/-- The final projection of `V = ∑ₖ ψ(Eₖᵢ) v φ(Eᵢₖ)` is `ψ 1`: `star V` is the element built
from `ψ`, `φ` and the partial isometry `star v`, whose initial projection is `ψ 1`. -/
private theorem sum_mul_star_sum (hv : IsPartialIsometry v) (hvφ : star v * v = φ (single i i 1))
    (hvψ : v * star v = ψ (single i i 1)) :
    (∑ j, ψ (single j i 1) * v * φ (single i j 1)) *
      star (∑ j, ψ (single j i 1) * v * φ (single i j 1)) = ψ 1 := by
  have hV : star (∑ j, ψ (single j i 1) * v * φ (single i j 1)) =
      ∑ j, φ (single j i 1) * star v * ψ (single i j 1) := by
    simp [star_sum, star_mul, star_map_single, mul_assoc]
  have h := star_sum_mul_sum (φ := ψ) (ψ := φ) hv.star (by rw [star_star, hvψ])
    (by rw [star_star, hvφ])
  rwa [← hV, star_star] at h

variable (φ ψ i) in
/-- **Unitary conjugacy of `⋆`-homomorphisms out of a matrix algebra.** Let `φ ψ : Mₙ(R) → B` be
`⋆`-homomorphisms into a unital `⋆`-ring `B`. If some partial isometry `v` has initial projection
`φ(Eᵢᵢ)` and final projection `ψ(Eᵢᵢ)`, and some partial isometry `w` has initial projection
`1 - φ 1` and final projection `1 - ψ 1`, then `ψ` is the conjugate of `φ` by a unitary of `B`,
namely `u = ∑ₖ ψ(Eₖᵢ) v φ(Eᵢₖ) + w`. -/
theorem _root_.NonUnitalStarAlgHom.exists_mem_unitary_mul_map_mul_star_eq {w : B}
    (hv : IsPartialIsometry v)
    (hvφ : star v * v = φ (single i i 1)) (hvψ : v * star v = ψ (single i i 1))
    (hw : IsPartialIsometry w) (hwφ : star w * w = 1 - φ 1) (hwψ : w * star w = 1 - ψ 1) :
    ∃ u ∈ unitary B, ∀ x, u * φ x * star u = ψ x := by
  set V := ∑ j, ψ (single j i 1) * v * φ (single i j 1)
  have hVV : star V * V = φ 1 := star_sum_mul_sum hv hvφ hvψ
  have hVV' : V * star V = ψ 1 := sum_mul_star_sum hv hvφ hvψ
  have hψV : ψ 1 * V = V := map_one_mul_sum φ ψ i
  have hVx (x : Matrix n n R) : V * φ x = ψ x * V := sum_mul_map φ ψ i x
  have hVφ : V * φ 1 = V := by rw [hVx, hψV]
  -- `w` vanishes on the range of `φ 1`, and its range is orthogonal to the range of `ψ 1`
  have hwφx (x : Matrix n n R) : w * φ x = 0 := by
    rw [← hw.mul_star_mul_self, mul_assoc w, hwφ]
    simp [mul_assoc, sub_mul, ← map_mul]
  have hψw : ψ 1 * w = 0 := by
    rw [← hw.mul_star_mul_self, hwψ]
    simp [← mul_assoc, mul_sub, ← map_mul]
  have hVw : star V * w = 0 := by
    rw [← hψV]
    simp [mul_assoc, ← map_star, hψw]
  have hwV : star w * V = 0 := by rw [← star_star V, ← star_mul, hVw, star_zero]
  have hwV' : w * star V = 0 := by
    rw [← hVφ]
    simp [← mul_assoc, ← map_star, hwφx]
  have hVw' : V * star w = 0 := by rw [← star_star V, ← star_mul, hwV', star_zero]
  refine ⟨V + w, Unitary.mem_iff.mpr ⟨?_, ?_⟩, fun x => ?_⟩
  · simp [add_mul, mul_add, hVV, hVw, hwV, hwφ]
  · simp [add_mul, mul_add, hVV', hVw', hwV', hwψ]
  · rw [add_mul, hwφx, add_zero, hVx]
    simp [mul_assoc, mul_add, hVV', hVw', ← map_mul]

end Unitary

end Matrix

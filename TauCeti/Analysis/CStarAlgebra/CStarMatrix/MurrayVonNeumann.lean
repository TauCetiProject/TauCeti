/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Unitization
public import Mathlib.Topology.Homotopy.Basic
public import TauCeti.Algebra.Star.PartialIsometry
public import TauCeti.Analysis.CStarAlgebra.CStarMatrix.Block
public import TauCeti.Analysis.CStarAlgebra.Exponential
import TauCeti.Data.Matrix.Block

/-!
# Murray–von Neumann equivalence of projections in matrix C⋆-algebras

Two projections `p : CStarMatrix m m A` and `q : CStarMatrix n n A`, possibly of different finite
matrix sizes, are *Murray–von Neumann equivalent* (`CStarMatrix.MurrayVonNeumannEquivalent p q`)
when there exists a rectangular matrix `v : CStarMatrix n m A` with `v.conjTranspose * v = p` and
`v * v.conjTranspose = q`. Comparing rectangular matrices directly—without casting between unequal
index types—is what lets `diag(1, 0)` in `M₂(A)` and `1` in `M₁(A)` represent the same `K₀`-class
while still distinguishing projections that are equivalent only stably.

Over any star-ordered ring with proper star (and hence over every non-unital C⋆-algebra `A`),
idempotence of `p = v.conjTranspose * v` automatically forces the rectangular partial-isometry
identity `v * v.conjTranspose * v = v` and makes both `p` and `q` star projections. From this we
derive:

* Reflexivity on star projections, symmetry, and transitivity across arbitrary finite index types,
  together with a `Setoid` on `{p : CStarMatrix n n A // IsStarProjection p}`.
* Compatibility with block-diagonal direct sums (`fromBlocks`), orthogonal sums (`p₁ * p₂ = 0`,
  `q₁ * q₂ = 0`), upper-left and lower-right zero-block padding (`inl`, `inr`), finite reindexing
  (`reindexₐ`), unitary conjugacy (both in unital matrix algebras and in the unitization
  `Unitization ℂ (CStarMatrix n n A)`), and entrywise `⋆`-algebra homomorphisms (`mapₙₐ`).
* For square matrices `p, q : CStarMatrix n n A`, characterization of Murray–von Neumann
  equivalence via `TauCeti.IsPartialIsometry`.
* Stabilized unitary conjugacy and the explicit exponential rotation path of projections: for
  unital `A`, the self-adjoint symmetry `w = fromBlocks (1 - p) v.conjTranspose v (1 - q)` is a
  unitary conjugating `fromBlocks p 0 0 0` to `fromBlocks 0 0 0 q` and equals
  `expUnitary (π • ⟨r, _⟩)` for the star projection
  `r = (1 / 2 : ℂ) • fromBlocks p (-v.conjTranspose) (-v) q`. For general (possibly non-unital)
  C⋆-algebras `A`, `r` still lies in `CStarMatrix (m ⊕ n) (m ⊕ n) A`, and conjugating by
  `t ↦ expUnitary ((π * t) • ⟨r, _⟩)` in the unitization defines a norm-continuous path of star
  projections inside `CStarMatrix (m ⊕ n) (m ⊕ n) A` from `fromBlocks p 0 0 0` to
  `fromBlocks 0 0 0 q` (and hence also to `fromBlocks q 0 0 0` when `m = n`).

## Main declarations

* `CStarMatrix.MurrayVonNeumannEquivalent`: rectangular Murray–von Neumann equivalence.
* `CStarMatrix.mul_conjTranspose_mul_self_of_isIdempotentElem`: if `vᴴ * v` is idempotent, then
  `v * vᴴ * v = v`.
* `IsStarProjection.murrayVonNeumannEquivalent_refl`,
  `CStarMatrix.MurrayVonNeumannEquivalent.symm`,
  `CStarMatrix.MurrayVonNeumannEquivalent.trans`: equivalence-relation laws.
* `CStarMatrix.MurrayVonNeumannEquivalent.fromBlocks`,
  `CStarMatrix.MurrayVonNeumannEquivalent.add_of_mul_eq_zero`,
  `IsStarProjection.murrayVonNeumannEquivalent_inl`,
  `IsStarProjection.murrayVonNeumannEquivalent_single`,
  `IsStarProjection.murrayVonNeumannEquivalent_reindexₐ`,
  `CStarMatrix.murrayVonNeumannEquivalent_of_unitization_unitary_conj`,
  `CStarMatrix.MurrayVonNeumannEquivalent.mapₙₐ`: structural permanence properties.
* `CStarMatrix.isStarProjection_and_murrayVonNeumannEquivalent_iff_exists_isPartialIsometry`:
  characterization via `TauCeti.IsPartialIsometry` on square matrices.
* `CStarMatrix.stabilizedSymmetry`, `CStarMatrix.rotationProjection`,
  `CStarMatrix.rotationUnitary`, `CStarMatrix.rotationPath`,
  `CStarMatrix.MurrayVonNeumannEquivalent.joined_inl_inr`,
  `CStarMatrix.MurrayVonNeumannEquivalent.joined_inl_inl`: stabilized unitary conjugacy and
  projection homotopy.

## References

* B. Blackadar, *K-Theory for Operator Algebras*, 2nd ed., Definition 4.6.1 and
  Propositions 4.6.2–4.6.6.
* M. Rørdam, F. Larsen, and N. Laustsen, *An Introduction to K-Theory for C⋆-Algebras*,
  Chapter 2, §§2.2–2.3.
-/

public section

noncomputable section

namespace CStarMatrix

section Basic

variable {l m n o R A B : Type*}

/-- Rectangular Murray–von Neumann equivalence of `p : CStarMatrix m m A` and
`q : CStarMatrix n n A`: there exists `v : CStarMatrix n m A` with `v.conjTranspose * v = p` and
`v * v.conjTranspose = q`. -/
def MurrayVonNeumannEquivalent [Fintype m] [Fintype n] [Mul A] [AddCommMonoid A] [Star A]
    (p : CStarMatrix m m A) (q : CStarMatrix n n A) : Prop :=
  ∃ v : CStarMatrix n m A, v.conjTranspose * v = p ∧ v * v.conjTranspose = q

/-- Unfold `CStarMatrix.MurrayVonNeumannEquivalent`. -/
theorem murrayVonNeumannEquivalent_def [Fintype m] [Fintype n] [Mul A] [AddCommMonoid A] [Star A]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A} :
    p.MurrayVonNeumannEquivalent q ↔
      ∃ v : CStarMatrix n m A, v.conjTranspose * v = p ∧ v * v.conjTranspose = q :=
  Iff.rfl

/-- Any matrix of the form `v.conjTranspose * v` is self-adjoint. -/
theorem isSelfAdjoint_conjTranspose_mul_self [Fintype n] [NonUnitalSemiring A] [StarRing A]
    (v : CStarMatrix n m A) : IsSelfAdjoint (v.conjTranspose * v) := by
  rw [IsSelfAdjoint, star_eq_conjTranspose, conjTranspose_mul, conjTranspose_conjTranspose]

/-- Any matrix of the form `v * v.conjTranspose` is self-adjoint. -/
theorem isSelfAdjoint_self_mul_conjTranspose [Fintype m] [NonUnitalSemiring A] [StarRing A]
    (v : CStarMatrix n m A) : IsSelfAdjoint (v * v.conjTranspose) := by
  rw [IsSelfAdjoint, star_eq_conjTranspose, conjTranspose_mul, conjTranspose_conjTranspose]

/-- Every star projection is Murray–von Neumann equivalent to itself, witnessed by `p` itself. -/
theorem _root_.IsStarProjection.murrayVonNeumannEquivalent_refl [Fintype m]
    [Mul A] [AddCommMonoid A] [Star A] {p : CStarMatrix m m A} (hp : IsStarProjection p) :
    p.MurrayVonNeumannEquivalent p :=
  ⟨p, by rw [← star_eq_conjTranspose, hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq],
    by rw [← star_eq_conjTranspose, hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq]⟩

namespace MurrayVonNeumannEquivalent

/-- Rectangular Murray–von Neumann equivalence is symmetric, witnessed by `v.conjTranspose`. -/
@[symm]
protected theorem symm [Fintype m] [Fintype n] [Mul A] [AddCommMonoid A] [InvolutiveStar A]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A} (h : p.MurrayVonNeumannEquivalent q) :
    q.MurrayVonNeumannEquivalent p := by
  rcases h with ⟨v, hvp, hvq⟩
  exact ⟨v.conjTranspose, by simpa using hvq, by simpa using hvp⟩

/-- The left-hand side of a Murray–von Neumann equivalence is self-adjoint. -/
theorem isSelfAdjoint_left [Fintype m] [Fintype n] [NonUnitalSemiring A] [StarRing A]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A} (h : p.MurrayVonNeumannEquivalent q) :
    IsSelfAdjoint p := by
  rcases h with ⟨v, rfl, -⟩
  exact isSelfAdjoint_conjTranspose_mul_self v

/-- The right-hand side of a Murray–von Neumann equivalence is self-adjoint. -/
theorem isSelfAdjoint_right [Fintype m] [Fintype n] [NonUnitalSemiring A] [StarRing A]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A} (h : p.MurrayVonNeumannEquivalent q) :
    IsSelfAdjoint q := by
  rcases h with ⟨v, -, rfl⟩
  exact isSelfAdjoint_self_mul_conjTranspose v

/-- If `p` and `q` are Murray–von Neumann equivalent and `p` is idempotent, then `p` is a star
projection. -/
theorem isStarProjection_left_of_isIdempotentElem [Fintype m] [Fintype n]
    [NonUnitalSemiring A] [StarRing A]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    (h : p.MurrayVonNeumannEquivalent q) (hp : IsIdempotentElem p) :
    IsStarProjection p :=
  ⟨hp, h.isSelfAdjoint_left⟩

/-- Block-diagonal direct sums preserve Murray–von Neumann equivalence. -/
theorem fromBlocks [Fintype l] [Fintype m] [Fintype n] [Fintype o]
    [NonUnitalNonAssocSemiring A] [StarRing A]
    {p₁ : CStarMatrix l l A} {p₂ : CStarMatrix m m A}
    {q₁ : CStarMatrix n n A} {q₂ : CStarMatrix o o A}
    (h₁ : p₁.MurrayVonNeumannEquivalent q₁) (h₂ : p₂.MurrayVonNeumannEquivalent q₂) :
    (CStarMatrix.fromBlocks p₁ 0 0 p₂).MurrayVonNeumannEquivalent
      (CStarMatrix.fromBlocks q₁ 0 0 q₂) := by
  rcases h₁ with ⟨v₁, hv₁p, hv₁q⟩
  rcases h₂ with ⟨v₂, hv₂p, hv₂q⟩
  refine ⟨CStarMatrix.fromBlocks v₁ 0 0 v₂, ?_, ?_⟩
  · simp [fromBlocks_conjTranspose, fromBlocks_multiply, hv₁p, hv₂p]
  · simp [fromBlocks_conjTranspose, fromBlocks_multiply, hv₁q, hv₂q]

/-- Applying a non-unital `⋆`-algebra homomorphism entrywise preserves Murray–von Neumann
equivalence. -/
theorem mapₙₐ [Fintype m] [Fintype n] [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [Star A]
    [NonUnitalNonAssocSemiring B] [Module R B] [Star B]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    (h : p.MurrayVonNeumannEquivalent q) (f : A →⋆ₙₐ[R] B) :
    (CStarMatrix.mapₙₐ f p).MurrayVonNeumannEquivalent (CStarMatrix.mapₙₐ f q) := by
  rcases h with ⟨v, rfl, rfl⟩
  refine ⟨v.map f, ?_, ?_⟩
  · rw [mapₙₐ_eq_map, ← map_conjTranspose, ← map_mul]
  · rw [mapₙₐ_eq_map, ← map_conjTranspose, ← map_mul]

end MurrayVonNeumannEquivalent

/-- Symmetry of `CStarMatrix.MurrayVonNeumannEquivalent` as an equivalence. -/
theorem murrayVonNeumannEquivalent_comm [Fintype m] [Fintype n]
    [Mul A] [AddCommMonoid A] [InvolutiveStar A]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A} :
    p.MurrayVonNeumannEquivalent q ↔ q.MurrayVonNeumannEquivalent p :=
  ⟨MurrayVonNeumannEquivalent.symm, MurrayVonNeumannEquivalent.symm⟩

/-- Placing a star projection `p : A` in any two diagonal corners `(i, i)` and `(j, j)` of
`CStarMatrix n n A` yields Murray–von Neumann equivalent projections, witnessed by `single j i p`
without requiring `A` to be unital. -/
theorem _root_.IsStarProjection.murrayVonNeumannEquivalent_single [Fintype n] [DecidableEq n]
    [NonUnitalNonAssocSemiring A] [StarRing A] {p : A} (hp : IsStarProjection p) (i j : n) :
    (single i i p).MurrayVonNeumannEquivalent (single j j p) := by
  refine ⟨single j i p, ?_, ?_⟩
  · rw [conjTranspose_single, single_mul_single_same, hp.isSelfAdjoint.star_eq,
      hp.isIdempotentElem.eq]
  · rw [conjTranspose_single, single_mul_single_same, hp.isSelfAdjoint.star_eq,
      hp.isIdempotentElem.eq]

/-- Any two diagonal corner embeddings `singleStarAlgHom i` and `singleStarAlgHom j` send a star
projection `p : A` to Murray–von Neumann equivalent matrix projections. -/
theorem _root_.IsStarProjection.murrayVonNeumannEquivalent_singleStarAlgHom [Fintype n]
    [DecidableEq n] [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A] [StarRing A]
    {p : A} (hp : IsStarProjection p) (i j : n) :
    (singleStarAlgHom (R := R) i p).MurrayVonNeumannEquivalent
      (singleStarAlgHom (R := R) j p) := by
  rw [singleStarAlgHom_apply, singleStarAlgHom_apply]
  exact hp.murrayVonNeumannEquivalent_single i j

/-- Padding a star projection `p` with zero blocks in the lower-right corner yields an equivalent
projection, without requiring `A` to have a unit. -/
theorem _root_.IsStarProjection.murrayVonNeumannEquivalent_inl [Fintype m] [Fintype n]
    [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A] [StarRing A]
    {p : CStarMatrix m m A} (hp : IsStarProjection p) :
    (inl (n := n) (R := R) p).MurrayVonNeumannEquivalent p := by
  let v : CStarMatrix m (m ⊕ n) A := ofMatrix (Matrix.of fun i ↦ Sum.elim (fun j ↦ p i j) 0)
  have hp_star (i j : m) : star (p i j) = p j i := star_apply_of_isSelfAdjoint hp.isSelfAdjoint
  refine ⟨v, ?_, ?_⟩
  · ext (j₁ | j₁) (j₂ | j₂)
    · simpa only [inl_apply, fromBlocks_apply₁₁, mul_apply, conjTranspose_apply, v, ofMatrix_apply,
        Matrix.of_apply, Sum.elim_inl, hp_star] using
          congrFun (congrFun hp.isIdempotentElem.eq j₁) j₂
    · simp [v, mul_apply]
    · simp [v, mul_apply]
    · simp [v, mul_apply]
  · ext i₁ i₂
    have hsum : (∑ x : m ⊕ n, v i₁ x * v.conjTranspose x i₂) = ∑ j : m, p i₁ j * p j i₂ := by
      simp [v, Fintype.sum_sum_type, hp_star]
    exact hsum.trans (congrFun (congrFun hp.isIdempotentElem.eq i₁) i₂)

/-- Padding a star projection `q` with zero blocks in the upper-left corner yields an equivalent
projection, without requiring `A` to have a unit. -/
theorem _root_.IsStarProjection.murrayVonNeumannEquivalent_inr [Fintype m] [Fintype n]
    [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A] [StarRing A]
    {q : CStarMatrix n n A} (hq : IsStarProjection q) :
    (inr (m := m) (R := R) q).MurrayVonNeumannEquivalent q := by
  let v : CStarMatrix n (m ⊕ n) A := ofMatrix (Matrix.of fun i ↦ Sum.elim 0 (fun j ↦ q i j))
  have hq_star (i j : n) : star (q i j) = q j i := star_apply_of_isSelfAdjoint hq.isSelfAdjoint
  refine ⟨v, ?_, ?_⟩
  · ext (j₁ | j₁) (j₂ | j₂)
    · simp [v, mul_apply]
    · simp [v, mul_apply]
    · simp [v, mul_apply]
    · simpa only [inr_apply, fromBlocks_apply₂₂, mul_apply, conjTranspose_apply, v, ofMatrix_apply,
        Matrix.of_apply, Sum.elim_inr, hq_star] using
          congrFun (congrFun hq.isIdempotentElem.eq j₁) j₂
  · ext i₁ i₂
    have hsum : (∑ x : m ⊕ n, v i₁ x * v.conjTranspose x i₂) = ∑ j : n, q i₁ j * q j i₂ := by
      simp [v, Fintype.sum_sum_type, hq_star]
    exact hsum.trans (congrFun (congrFun hq.isIdempotentElem.eq i₁) i₂)

/-- Reindexing a star projection along an equivalence `e : m ≃ n` yields a Murray–von Neumann
equivalent projection, without requiring `A` to have a unit. -/
theorem _root_.IsStarProjection.murrayVonNeumannEquivalent_reindexₐ [Fintype m] [Fintype n]
    [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A] [Star A]
    {p : CStarMatrix m m A} (hp : IsStarProjection p) (e : m ≃ n) :
    (reindexₐ R A e p).MurrayVonNeumannEquivalent p := by
  refine ⟨reindexₗ R A (Equiv.refl m) e p, ?_, ?_⟩
  · rw [reindexₗ_conjTranspose, ← star_eq_conjTranspose, hp.isSelfAdjoint.star_eq,
      reindexₗ_mul, hp.isIdempotentElem.eq, reindexₗ_eq_reindexₐ]
  · rw [reindexₗ_conjTranspose, ← star_eq_conjTranspose, hp.isSelfAdjoint.star_eq,
      reindexₗ_mul, hp.isIdempotentElem.eq]
    ext i j
    rfl

/-- Unitary conjugates of a star projection in `CStarMatrix n n A` are Murray–von Neumann
equivalent to it. -/
theorem _root_.IsStarProjection.murrayVonNeumannEquivalent_unitary_conj [Fintype n] [DecidableEq n]
    [Semiring A] [StarRing A] {p : CStarMatrix n n A} (hp : IsStarProjection p)
    {u : CStarMatrix n n A} (hu : u ∈ unitary (CStarMatrix n n A)) :
    (u * p * star u).MurrayVonNeumannEquivalent p := by
  refine ⟨p * star u, ?_, ?_⟩
  · rw [← star_eq_conjTranspose, star_mul, star_star, hp.isSelfAdjoint.star_eq,
      mul_assoc u p (p * star u), ← mul_assoc p p (star u), hp.isIdempotentElem.eq, mul_assoc]
  · rw [← star_eq_conjTranspose, star_mul, star_star, hp.isSelfAdjoint.star_eq,
      mul_assoc p (star u) (u * p), ← mul_assoc (star u) u p, Unitary.star_mul_self_of_mem hu,
      one_mul, hp.isIdempotentElem.eq]

/-- Any element `x` of `Unitization R B` with zero scalar part equals the image of `x.snd`. -/
private theorem inr_snd_eq_of_fst_eq_zero {R B : Type*} [Zero R]
    {x : Unitization R B} (hx : x.fst = 0) : (x.snd : Unitization R B) = x :=
  Unitization.ext (hx ▸ Unitization.fst_inr R x.snd) rfl

/-- If two matrix projections `p, q : CStarMatrix n n A` over a possibly non-unital `⋆`-algebra `A`
become unitarily conjugate inside the unitization `Unitization R (CStarMatrix n n A)`, then `p` and
`q` are Murray–von Neumann equivalent inside `CStarMatrix n n A`. -/
theorem murrayVonNeumannEquivalent_of_unitization_unitary_conj [Fintype n]
    [CommSemiring R] [StarRing R] [NonUnitalSemiring A] [StarRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A] [StarModule R A]
    {p q : CStarMatrix n n A} (hp : IsStarProjection p)
    {u : Unitization R (CStarMatrix n n A)}
    (hu : u ∈ unitary (Unitization R (CStarMatrix n n A)))
    (hconj : u * (p : Unitization R (CStarMatrix n n A)) * star u =
      (q : Unitization R (CStarMatrix n n A))) :
    p.MurrayVonNeumannEquivalent q := by
  let M := CStarMatrix n n A
  let v : M := (u * (p : Unitization R M)).snd
  have hv_coe : (v : Unitization R M) = u * (p : Unitization R M) := by
    apply inr_snd_eq_of_fst_eq_zero
    rw [Unitization.fst_mul, Unitization.fst_inr, mul_zero]
  have hp_coe_idem : (p : Unitization R M) * (p : Unitization R M) = (p : Unitization R M) := by
    rw [← Unitization.inr_mul, hp.isIdempotentElem.eq]
  have hp_coe_star : star (p : Unitization R M) = (p : Unitization R M) := by
    rw [← Unitization.inr_star, hp.isSelfAdjoint.star_eq]
  refine ⟨v, Unitization.inr_injective (R := R) ?_, Unitization.inr_injective (R := R) ?_⟩
  · rw [Unitization.inr_mul, ← star_eq_conjTranspose, Unitization.inr_star, hv_coe, star_mul,
      hp_coe_star, mul_assoc (p : Unitization R M) (star u) (u * p),
      ← mul_assoc (star u) u (p : Unitization R M), Unitary.star_mul_self_of_mem hu, one_mul,
      hp_coe_idem]
  · rw [Unitization.inr_mul, ← star_eq_conjTranspose, Unitization.inr_star, hv_coe, star_mul,
      hp_coe_star, mul_assoc u (p : Unitization R M),
      ← mul_assoc (p : Unitization R M) (p : Unitization R M) (star u), hp_coe_idem, ← mul_assoc,
      hconj]

end Basic

section ProperStar

variable {l m n A : Type*} [Fintype l] [Fintype m] [Fintype n]
  [NonUnitalRing A] [StarRing A] [PartialOrder A] [StarOrderedRing A] [IsProperStar A]

/-- Over a star-ordered ring with proper star, if `v.conjTranspose * v` is idempotent then `v`
satisfies the rectangular partial-isometry identity `v * v.conjTranspose * v = v`. -/
theorem mul_conjTranspose_mul_self_of_isIdempotentElem {v : CStarMatrix n m A}
    (hv : IsIdempotentElem (v.conjTranspose * v)) :
    v * v.conjTranspose * v = v := by
  let p : CStarMatrix m m A := v.conjTranspose * v
  have hdef : v.conjTranspose * v = p := rfl
  have hp_conj : p.conjTranspose = p := by simp [p]
  have hp_idem : p * p = p := hv.eq
  have hzero : (v * p - v).conjTranspose * (v * p - v) = 0 := by
    calc (v * p - v).conjTranspose * (v * p - v)
        = (p * v.conjTranspose - v.conjTranspose) * (v * p - v) := by
            rw [conjTranspose_sub, conjTranspose_mul, hp_conj]
      _ = p * (v.conjTranspose * v) * p - p * (v.conjTranspose * v) -
            ((v.conjTranspose * v) * p - v.conjTranspose * v) := by
            rw [CStarMatrix.sub_mul, CStarMatrix.mul_sub, CStarMatrix.mul_sub,
              CStarMatrix.mul_assoc p v.conjTranspose (v * p),
              ← CStarMatrix.mul_assoc v.conjTranspose v p,
              ← CStarMatrix.mul_assoc p (v.conjTranspose * v) p,
              CStarMatrix.mul_assoc p v.conjTranspose v]
      _ = 0 := by simp only [hdef, hp_idem, sub_self]
  have hvp : v * p = v := sub_eq_zero.mp (conjTranspose_mul_self_eq_zero.mp hzero)
  rwa [CStarMatrix.mul_assoc]

/-- Dual rectangular partial-isometry identity when `v * v.conjTranspose` is idempotent. -/
theorem mul_conjTranspose_mul_self_of_isIdempotentElem_self_mul {v : CStarMatrix n m A}
    (hv : IsIdempotentElem (v * v.conjTranspose)) :
    v * v.conjTranspose * v = v := by
  have h := mul_conjTranspose_mul_self_of_isIdempotentElem (v := v.conjTranspose)
    (by simpa using hv)
  simpa [CStarMatrix.mul_assoc] using congrArg conjTranspose h

/-- If `v.conjTranspose * v` is idempotent, then `v * v.conjTranspose` is a star projection. -/
theorem isStarProjection_self_mul_conjTranspose_of_isIdempotentElem {v : CStarMatrix n m A}
    (hv : IsIdempotentElem (v.conjTranspose * v)) :
    IsStarProjection (v * v.conjTranspose) where
  isIdempotentElem := by
    rw [IsIdempotentElem, ← CStarMatrix.mul_assoc,
      mul_conjTranspose_mul_self_of_isIdempotentElem hv]
  isSelfAdjoint := isSelfAdjoint_self_mul_conjTranspose v

namespace MurrayVonNeumannEquivalent

/-- If `p` and `q` are Murray–von Neumann equivalent and `p` is idempotent, then `q` is a star
projection. -/
theorem isStarProjection_right_of_isIdempotentElem {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    (h : p.MurrayVonNeumannEquivalent q) (hp : IsIdempotentElem p) :
    IsStarProjection q := by
  rcases h with ⟨v, rfl, rfl⟩
  exact isStarProjection_self_mul_conjTranspose_of_isIdempotentElem hp

/-- Murray–von Neumann equivalence preserves the property of being a star projection. -/
theorem isStarProjection_iff {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    (h : p.MurrayVonNeumannEquivalent q) :
    IsStarProjection p ↔ IsStarProjection q :=
  ⟨fun hp ↦ h.isStarProjection_right_of_isIdempotentElem hp.isIdempotentElem,
    fun hq ↦ h.symm.isStarProjection_right_of_isIdempotentElem hq.isIdempotentElem⟩

/-- Murray–von Neumann equivalence of projections is transitive across arbitrary finite matrix
sizes: if `v₁` implements `p ∼ q` and `v₂` implements `q ∼ r`, then `v₂ * v₁` implements `p ∼ r`. -/
theorem trans {p : CStarMatrix l l A} {q : CStarMatrix m m A} {r : CStarMatrix n n A}
    (h₁ : p.MurrayVonNeumannEquivalent q) (h₂ : q.MurrayVonNeumannEquivalent r)
    (hp : IsIdempotentElem p) :
    p.MurrayVonNeumannEquivalent r := by
  have hq : IsStarProjection q := h₁.isStarProjection_right_of_isIdempotentElem hp
  rcases h₁ with ⟨v₁, hv₁p, hv₁q⟩
  rcases h₂ with ⟨v₂, hv₂q, hv₂r⟩
  have hv₁_pi : v₁ * v₁.conjTranspose * v₁ = v₁ :=
    mul_conjTranspose_mul_self_of_isIdempotentElem (hv₁p.symm ▸ hp)
  have hv₂_pi : v₂ * v₂.conjTranspose * v₂ = v₂ :=
    mul_conjTranspose_mul_self_of_isIdempotentElem (hv₂q.symm ▸ hq.isIdempotentElem)
  refine ⟨v₂ * v₁, ?_, ?_⟩
  · calc (v₂ * v₁).conjTranspose * (v₂ * v₁)
        = v₁.conjTranspose * ((v₂.conjTranspose * v₂) * v₁) := by
            rw [conjTranspose_mul, CStarMatrix.mul_assoc,
              ← CStarMatrix.mul_assoc v₂.conjTranspose v₂ v₁]
      _ = v₁.conjTranspose * (v₁ * v₁.conjTranspose * v₁) := by rw [hv₂q, ← hv₁q]
      _ = p := by rw [hv₁_pi, hv₁p]
  · calc (v₂ * v₁) * (v₂ * v₁).conjTranspose
        = (v₂ * (v₁ * v₁.conjTranspose)) * v₂.conjTranspose := by
            rw [conjTranspose_mul,
              CStarMatrix.mul_assoc v₂ v₁ (v₁.conjTranspose * v₂.conjTranspose),
              ← CStarMatrix.mul_assoc v₁ v₁.conjTranspose v₂.conjTranspose,
              ← CStarMatrix.mul_assoc v₂ (v₁ * v₁.conjTranspose) v₂.conjTranspose]
      _ = (v₂ * v₂.conjTranspose * v₂) * v₂.conjTranspose := by
            rw [hv₁q, ← hv₂q, ← CStarMatrix.mul_assoc v₂ v₂.conjTranspose v₂]
      _ = r := by rw [hv₂_pi, hv₂r]

/-- Orthogonal sums preserve Murray–von Neumann equivalence: if `p₁ * p₂ = 0` and `q₁ * q₂ = 0`,
then adding implementing matrices `v₁ + v₂` implements `(p₁ + p₂) ∼ (q₁ + q₂)`. -/
theorem add_of_mul_eq_zero {p₁ p₂ : CStarMatrix m m A} {q₁ q₂ : CStarMatrix n n A}
    (h₁ : p₁.MurrayVonNeumannEquivalent q₁) (h₂ : p₂.MurrayVonNeumannEquivalent q₂)
    (hp : p₁ * p₂ = 0) (hq : q₁ * q₂ = 0) :
    (p₁ + p₂).MurrayVonNeumannEquivalent (q₁ + q₂) := by
  rcases h₁ with ⟨v₁, rfl, rfl⟩
  rcases h₂ with ⟨v₂, rfl, rfl⟩
  have hv₁₂ : v₁.conjTranspose * v₂ = 0 :=
    (mul_self_mul_conjTranspose_eq_zero v₂ v₁.conjTranspose).mp
      ((self_mul_conjTranspose_mul_eq_zero v₁ (v₂ * v₂.conjTranspose)).mp hq)
  have hv₂₁ : v₂.conjTranspose * v₁ = 0 := by
    simpa using congrArg conjTranspose hv₁₂
  have hw₁₂ : v₁ * v₂.conjTranspose = 0 :=
    (mul_conjTranspose_mul_self_eq_zero v₂ v₁).mp
      ((conjTranspose_mul_self_mul_eq_zero v₁ (v₂.conjTranspose * v₂)).mp hp)
  have hw₂₁ : v₂ * v₁.conjTranspose = 0 := by
    simpa using congrArg conjTranspose hw₁₂
  refine ⟨v₁ + v₂, ?_, ?_⟩
  · rw [conjTranspose_add, CStarMatrix.add_mul, CStarMatrix.mul_add, CStarMatrix.mul_add,
      hv₁₂, hv₂₁, add_zero, zero_add]
  · rw [conjTranspose_add, CStarMatrix.add_mul, CStarMatrix.mul_add, CStarMatrix.mul_add,
      hw₁₂, hw₂₁, add_zero, zero_add]

end MurrayVonNeumannEquivalent

/-- Only the zero matrix is Murray–von Neumann equivalent to `0` on the left. -/
@[simp]
theorem murrayVonNeumannEquivalent_zero_left {q : CStarMatrix n n A} :
    (0 : CStarMatrix m m A).MurrayVonNeumannEquivalent q ↔ q = 0 := by
  refine ⟨fun ⟨v, hv0, hvq⟩ ↦ ?_, fun h ↦ ⟨0, by simp, by simp [h]⟩⟩
  rw [conjTranspose_mul_self_eq_zero.mp hv0, CStarMatrix.zero_mul] at hvq
  exact hvq.symm

/-- Only the zero matrix is Murray–von Neumann equivalent to `0` on the right. -/
@[simp]
theorem murrayVonNeumannEquivalent_zero_right {p : CStarMatrix m m A} :
    p.MurrayVonNeumannEquivalent (0 : CStarMatrix n n A) ↔ p = 0 := by
  rw [murrayVonNeumannEquivalent_comm, murrayVonNeumannEquivalent_zero_left]

/-- Setoid of Murray–von Neumann equivalence on star projections of fixed size `n`. -/
def murrayVonNeumannSetoid (n A : Type*) [Fintype n]
    [NonUnitalRing A] [StarRing A] [PartialOrder A] [StarOrderedRing A] [IsProperStar A] :
    Setoid {p : CStarMatrix n n A // IsStarProjection p} where
  r p q := p.1.MurrayVonNeumannEquivalent q.1
  iseqv := {
    refl p := p.2.murrayVonNeumannEquivalent_refl
    symm h := h.symm
    trans {p _ _} h₁ h₂ := h₁.trans h₂ p.2.isIdempotentElem
  }

/-- For square matrices `p, q : CStarMatrix n n A`, `p` is a star projection Murray–von Neumann
equivalent to `q` iff there exists a partial isometry `v` (`TauCeti.IsPartialIsometry v`) with
initial projection `star v * v = p` and final projection `v * star v = q`. -/
theorem isStarProjection_and_murrayVonNeumannEquivalent_iff_exists_isPartialIsometry
    {p q : CStarMatrix n n A} :
    IsStarProjection p ∧ p.MurrayVonNeumannEquivalent q ↔
      ∃ v : CStarMatrix n n A, TauCeti.IsPartialIsometry v ∧ star v * v = p ∧ v * star v = q := by
  refine ⟨fun ⟨hp, v, hvp, hvq⟩ ↦ ⟨v, ?_, hvp, hvq⟩, fun ⟨v, hv, hvp, hvq⟩ ↦ ?_⟩
  · exact TauCeti.isPartialIsometry_iff.mpr
      (mul_conjTranspose_mul_self_of_isIdempotentElem (hvp.symm ▸ hp.isIdempotentElem))
  · exact ⟨hvp ▸ hv.isStarProjection_star_mul_self, v, hvp, hvq⟩

/-- When `p : CStarMatrix n n A` is idempotent, square Murray–von Neumann equivalence `p ∼ q` is
equivalent to the existence of a partial isometry with initial projection `p` and final projection
`q`. -/
theorem _root_.IsIdempotentElem.murrayVonNeumannEquivalent_iff_exists_isPartialIsometry
    {p q : CStarMatrix n n A} (hp : IsIdempotentElem p) :
    p.MurrayVonNeumannEquivalent q ↔
      ∃ v : CStarMatrix n n A, TauCeti.IsPartialIsometry v ∧ star v * v = p ∧ v * star v = q := by
  refine ⟨fun h ↦ (isStarProjection_and_murrayVonNeumannEquivalent_iff_exists_isPartialIsometry.mp
    ⟨h.isStarProjection_left_of_isIdempotentElem hp, h⟩), ?_⟩
  exact fun h ↦
    (isStarProjection_and_murrayVonNeumannEquivalent_iff_exists_isPartialIsometry.mpr h).2

end ProperStar

section StabilizedUnitaryAndRotationPath

section UnitalAlgebraic

variable {m n A : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
  [Ring A] [StarRing A]

/-- The `2 × 2` block reflection `fromBlocks (1 - p) v.conjTranspose v (1 - q)` over a unital ring,
which is a self-adjoint unitary conjugating `fromBlocks p 0 0 0` to `fromBlocks 0 0 0 q` whenever
`v` implements `p ∼ q` for an idempotent `p`. -/
def stabilizedSymmetry (p : CStarMatrix m m A) (q : CStarMatrix n n A)
    (v : CStarMatrix n m A) : CStarMatrix (m ⊕ n) (m ⊕ n) A :=
  fromBlocks (1 - p) v.conjTranspose v (1 - q)

theorem isSelfAdjoint_stabilizedSymmetry {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    {v : CStarMatrix n m A} (hvp : v.conjTranspose * v = p) (hvq : v * v.conjTranspose = q) :
    IsSelfAdjoint (stabilizedSymmetry p q v) := by
  have hp : IsSelfAdjoint p := hvp ▸ isSelfAdjoint_conjTranspose_mul_self v
  have hq : IsSelfAdjoint q := hvq ▸ isSelfAdjoint_self_mul_conjTranspose v
  rw [stabilizedSymmetry, isSelfAdjoint_fromBlocks_iff]
  exact ⟨.sub (.one _) hp, conjTranspose_conjTranspose v, .sub (.one _) hq⟩

variable [PartialOrder A] [StarOrderedRing A] [IsProperStar A]

theorem stabilizedSymmetry_mul_self {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    {v : CStarMatrix n m A} (hp : IsIdempotentElem p)
    (hvp : v.conjTranspose * v = p) (hvq : v * v.conjTranspose = q) :
    stabilizedSymmetry p q v * stabilizedSymmetry p q v = 1 := by
  have hv_pi : v * v.conjTranspose * v = v :=
    mul_conjTranspose_mul_self_of_isIdempotentElem (hvp.symm ▸ hp)
  have hbe : v * p = v := by rw [← hvp, ← CStarMatrix.mul_assoc, hv_pi]
  have hea : p * v.conjTranspose = v.conjTranspose := by
    have hp_sa : p.conjTranspose = p := by
      rw [← hvp, conjTranspose_mul, conjTranspose_conjTranspose]
    simpa [hp_sa] using congrArg conjTranspose hbe
  apply ofMatrix.symm.injective
  rw [stabilizedSymmetry, ofMatrix_symm_hMul, ofMatrix_symm_fromBlocks]
  exact Matrix.fromBlocks_one_sub_mul_self_of_mul_eq (a := ofMatrix.symm v.conjTranspose)
    (b := ofMatrix.symm v) (e := ofMatrix.symm p) (f := ofMatrix.symm q) hvp hvq hea hbe

theorem stabilizedSymmetry_mem_unitary {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    {v : CStarMatrix n m A} (hp : IsIdempotentElem p)
    (hvp : v.conjTranspose * v = p) (hvq : v * v.conjTranspose = q) :
    stabilizedSymmetry p q v ∈ unitary (CStarMatrix (m ⊕ n) (m ⊕ n) A) := by
  rw [Unitary.mem_iff, (isSelfAdjoint_stabilizedSymmetry hvp hvq).star_eq,
    stabilizedSymmetry_mul_self hp hvp hvq]
  exact ⟨rfl, rfl⟩

/-- `stabilizedSymmetry p q v` conjugates `fromBlocks p 0 0 0` to `fromBlocks 0 0 0 q`. -/
theorem stabilizedSymmetry_conj_inl {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    {v : CStarMatrix n m A} (hp : IsIdempotentElem p)
    (hvp : v.conjTranspose * v = p) (hvq : v * v.conjTranspose = q) :
    stabilizedSymmetry p q v * fromBlocks p 0 0 0 * star (stabilizedSymmetry p q v) =
      fromBlocks 0 0 0 q := by
  have hv_pi : v * v.conjTranspose * v = v :=
    mul_conjTranspose_mul_self_of_isIdempotentElem (hvp.symm ▸ hp)
  have hbe : v * p = v := by rw [← hvp, ← CStarMatrix.mul_assoc, hv_pi]
  rw [(isSelfAdjoint_stabilizedSymmetry hvp hvq).star_eq]
  apply ofMatrix.symm.injective
  rw [stabilizedSymmetry, ofMatrix_symm_hMul, ofMatrix_symm_hMul, ofMatrix_symm_fromBlocks,
    ofMatrix_symm_fromBlocks, ofMatrix_symm_fromBlocks]
  exact Matrix.fromBlocks_one_sub_mul_fromBlocks_mul_fromBlocks_one_sub_of_mul_eq
    (a := ofMatrix.symm v.conjTranspose) (b := ofMatrix.symm v)
    (e := ofMatrix.symm p) (f := ofMatrix.symm q) hvp hvq hbe

end UnitalAlgebraic

section RotationPath

/-- The block projection `(1 / 2 : ℂ) • fromBlocks p (-v.conjTranspose) (-v) q` inside
`CStarMatrix (m ⊕ n) (m ⊕ n) A`, defined without assuming `A` is unital. Its exponential path
`t ↦ expUnitary ((π * t) • ⟨r, _⟩)` in the unitization rotates `fromBlocks p 0 0 0` to
`fromBlocks 0 0 0 q`. -/
def rotationProjection {m n A : Type*} [NonUnitalCStarAlgebra A]
    (p : CStarMatrix m m A) (q : CStarMatrix n n A)
    (v : CStarMatrix n m A) : CStarMatrix (m ⊕ n) (m ⊕ n) A :=
  (1 / 2 : ℂ) • fromBlocks p (-v.conjTranspose) (-v) q

theorem two_smul_rotationProjection {m n A : Type*} [NonUnitalCStarAlgebra A]
    (p : CStarMatrix m m A) (q : CStarMatrix n n A) (v : CStarMatrix n m A) :
    (2 : ℂ) • rotationProjection p q v = fromBlocks p (-v.conjTranspose) (-v) q := by
  rw [rotationProjection, smul_smul]
  norm_num

section NonUnitalCStar

variable {m n A : Type*} [Fintype m] [Fintype n]
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- When `v` implements `p ∼ q` for an idempotent `p`, `rotationProjection p q v` is a star
projection in `CStarMatrix (m ⊕ n) (m ⊕ n) A`. -/
theorem isStarProjection_rotationProjection {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    {v : CStarMatrix n m A} (hp : IsIdempotentElem p)
    (hvp : v.conjTranspose * v = p) (hvq : v * v.conjTranspose = q) :
    IsStarProjection (rotationProjection p q v) := by
  have hp_proj : IsStarProjection p := ⟨hp, hvp ▸ isSelfAdjoint_conjTranspose_mul_self v⟩
  have hq_proj : IsStarProjection q :=
    hvq ▸ isStarProjection_self_mul_conjTranspose_of_isIdempotentElem (hvp.symm ▸ hp)
  have hv_pi : v * v.conjTranspose * v = v :=
    mul_conjTranspose_mul_self_of_isIdempotentElem (hvp.symm ▸ hp)
  have hvp_mul : v * p = v := by rw [← hvp, ← CStarMatrix.mul_assoc, hv_pi]
  have hpv_mul : p * v.conjTranspose = v.conjTranspose := by
    have hp_conj : p.conjTranspose = p := hp_proj.isSelfAdjoint.star_eq
    simpa [hp_conj] using congrArg conjTranspose hvp_mul
  have hqv_mul : q * v = v := by rw [← hvq, hv_pi]
  have hvq_mul : v.conjTranspose * q = v.conjTranspose := by
    have hq_conj : q.conjTranspose = q := hq_proj.isSelfAdjoint.star_eq
    simpa [hq_conj] using congrArg conjTranspose hqv_mul
  rw [isStarProjection_iff, IsIdempotentElem, IsSelfAdjoint, rotationProjection]
  set B := fromBlocks p (-v.conjTranspose) (-v) q
  have hB_sa : IsSelfAdjoint B := by
    rw [isSelfAdjoint_fromBlocks_iff]
    exact ⟨hp_proj.isSelfAdjoint, by simp, hq_proj.isSelfAdjoint⟩
  have hB_sq : B * B = (2 : ℂ) • B := by
    simp only [B, fromBlocks_multiply, fromBlocks_add, hp.eq, hq_proj.isIdempotentElem.eq,
      CStarMatrix.neg_mul, CStarMatrix.mul_neg, neg_neg, hvp, hvq, hpv_mul, hvq_mul, hvp_mul,
      hqv_mul, two_smul]
  refine ⟨?_, ?_⟩
  · rw [smul_mul_smul_comm, hB_sq, smul_smul]
    norm_num
  · rw [star_smul, hB_sa.star_eq]
    norm_num

/-- In the unitization of `CStarMatrix (m ⊕ n) (m ⊕ n) A`, conjugating `fromBlocks p 0 0 0` by
`1 - 2 * rotationProjection p q v` yields `fromBlocks 0 0 0 q` without requiring `A` to be
unital. -/
private theorem unitization_one_sub_two_mul_rotationProjection_conj
    {p : CStarMatrix m m A} {q : CStarMatrix n n A} {v : CStarMatrix n m A}
    (hp : IsIdempotentElem p) (hvp : v.conjTranspose * v = p) (hvq : v * v.conjTranspose = q) :
    ((1 - 2 * (rotationProjection p q v : Unitization ℂ (CStarMatrix (m ⊕ n) (m ⊕ n) A))) *
        (fromBlocks p 0 0 0 : CStarMatrix (m ⊕ n) (m ⊕ n) A) *
        (1 - 2 * (rotationProjection p q v : Unitization ℂ (CStarMatrix (m ⊕ n) (m ⊕ n) A)))) =
      ((fromBlocks 0 0 0 q : CStarMatrix (m ⊕ n) (m ⊕ n) A) :
        Unitization ℂ (CStarMatrix (m ⊕ n) (m ⊕ n) A)) := by
  have hp_proj : IsStarProjection p := ⟨hp, hvp ▸ isSelfAdjoint_conjTranspose_mul_self v⟩
  have hv_pi : v * v.conjTranspose * v = v :=
    mul_conjTranspose_mul_self_of_isIdempotentElem (hvp.symm ▸ hp)
  have hvp_mul : v * p = v := by rw [← hvp, ← CStarMatrix.mul_assoc, hv_pi]
  have hpv_mul : p * v.conjTranspose = v.conjTranspose := by
    have hp_conj : p.conjTranspose = p := hp_proj.isSelfAdjoint.star_eq
    simpa [hp_conj] using congrArg conjTranspose hvp_mul
  set b : CStarMatrix (m ⊕ n) (m ⊕ n) A := fromBlocks p (-v.conjTranspose) (-v) q
  set x : CStarMatrix (m ⊕ n) (m ⊕ n) A := fromBlocks p 0 0 0
  have h2r : 2 * (rotationProjection p q v : Unitization ℂ (CStarMatrix (m ⊕ n) (m ⊕ n) A)) =
      (b : Unitization ℂ (CStarMatrix (m ⊕ n) (m ⊕ n) A)) := by
    rw [two_mul, ← two_smul ℂ, ← Unitization.inr_smul, two_smul_rotationProjection]
  have hbx : b * x = fromBlocks p 0 (-v) 0 := by
    simp [b, x, fromBlocks_multiply, hp.eq, hvp_mul]
  have hxb : x * b = fromBlocks p (-v.conjTranspose) 0 0 := by
    simp [b, x, fromBlocks_multiply, hp.eq, hpv_mul]
  have hbxb : b * x * b = b := by
    rw [hbx]
    simp [b, fromBlocks_multiply, hp.eq, hpv_mul, hvp_mul, hvq]
  have hexpand :
      (1 - (b : Unitization ℂ (CStarMatrix (m ⊕ n) (m ⊕ n) A))) *
          (x : Unitization ℂ (CStarMatrix (m ⊕ n) (m ⊕ n) A)) *
          (1 - (b : Unitization ℂ (CStarMatrix (m ⊕ n) (m ⊕ n) A))) =
        ((x - b * x - (x * b - b * x * b) : CStarMatrix (m ⊕ n) (m ⊕ n) A) :
          Unitization ℂ (CStarMatrix (m ⊕ n) (m ⊕ n) A)) := by
    simp only [sub_mul, one_mul, mul_sub, mul_one, ← Unitization.inr_mul, ← Unitization.inr_sub]
  rw [h2r, hexpand, hbxb, hbx, hxb]
  congr 1
  simp [x, b, fromBlocks_sub]

/-- Any unitary conjugate of an embedded star projection `x : B` inside `Unitization R B` has zero
scalar part and projects to a star projection in `B`. -/
private theorem unitization_conj_snd_eq_and_isStarProjection {R B : Type*}
    [CommSemiring R] [StarRing R] [NonUnitalSemiring B] [StarRing B]
    [Module R B] [IsScalarTower R B B] [SMulCommClass R B B] [StarModule R B]
    {x : B} (hx : IsStarProjection x)
    {u : Unitization R B} (hu : u ∈ unitary (Unitization R B)) :
    ((u * (x : Unitization R B) * star u).snd : Unitization R B) =
        u * (x : Unitization R B) * star u ∧
      IsStarProjection (u * (x : Unitization R B) * star u).snd := by
  have hxU : IsStarProjection (x : Unitization R B) :=
    hx.map (Unitization.inrNonUnitalStarAlgHom R B)
  have hcoe : ((u * (x : Unitization R B) * star u).snd : Unitization R B) =
      u * (x : Unitization R B) * star u := by
    apply inr_snd_eq_of_fst_eq_zero
    simp [Unitization.fst_mul, Unitization.fst_inr]
  have hprojU : IsStarProjection (u * (x : Unitization R B) * star u) := by
    refine ⟨?_, ?_⟩
    · calc u * (x : Unitization R B) * star u * (u * (x : Unitization R B) * star u)
          = u * ((x : Unitization R B) * (star u * u) * (x : Unitization R B)) * star u := by
              simp only [mul_assoc]
        _ = u * (x : Unitization R B) * star u := by
              rw [Unitary.star_mul_self_of_mem hu, mul_one, hxU.isIdempotentElem.eq]
    · simp only [IsSelfAdjoint, star_mul, star_star, hxU.isSelfAdjoint.star_eq, mul_assoc]
  rw [← hcoe] at hprojU
  refine ⟨hcoe, ?_, ?_⟩
  · apply Unitization.inr_injective (R := R)
    simpa [IsIdempotentElem, Unitization.inr_mul] using hprojU.isIdempotentElem
  · apply Unitization.inr_injective (R := R)
    simpa [IsSelfAdjoint, Unitization.inr_star] using hprojU.isSelfAdjoint

/-- The one-parameter family of unitaries `expUnitary ((π * t) • ⟨rotationProjection p q v, _⟩)` in
`Unitization ℂ (CStarMatrix (m ⊕ n) (m ⊕ n) A)` whose conjugation rotates `inl p` to `inr q` on
`[0, 1]`. -/
def rotationUnitary {p : CStarMatrix m m A} {q : CStarMatrix n n A} {v : CStarMatrix n m A}
    (hp : IsIdempotentElem p) (hvp : v.conjTranspose * v = p) (hvq : v * v.conjTranspose = q)
    (t : ℝ) : unitary (Unitization ℂ (CStarMatrix (m ⊕ n) (m ⊕ n) A)) :=
  selfAdjoint.expUnitary ((Real.pi * t) •
    ⟨(rotationProjection p q v : Unitization ℂ (CStarMatrix (m ⊕ n) (m ⊕ n) A)),
      selfAdjoint.mem_iff.mpr
        ((isStarProjection_rotationProjection hp hvp hvq).map
          (Unitization.inrNonUnitalStarAlgHom ℂ _)).isSelfAdjoint⟩)

@[simp]
theorem rotationUnitary_zero {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    {v : CStarMatrix n m A} (hp : IsIdempotentElem p)
    (hvp : v.conjTranspose * v = p) (hvq : v * v.conjTranspose = q) :
    rotationUnitary hp hvp hvq 0 = 1 := by
  have h0 : (0 : ℝ) •
      (⟨(rotationProjection p q v : Unitization ℂ (CStarMatrix (m ⊕ n) (m ⊕ n) A)),
        selfAdjoint.mem_iff.mpr
          ((isStarProjection_rotationProjection hp hvp hvq).map
            (Unitization.inrNonUnitalStarAlgHom ℂ _)).isSelfAdjoint⟩ :
        selfAdjoint (Unitization ℂ (CStarMatrix (m ⊕ n) (m ⊕ n) A))) = 0 :=
    Subtype.ext (zero_smul ℝ _)
  rw [rotationUnitary, mul_zero, h0, selfAdjoint.expUnitary_zero]

theorem coe_rotationUnitary_one {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    {v : CStarMatrix n m A} (hp : IsIdempotentElem p)
    (hvp : v.conjTranspose * v = p) (hvq : v * v.conjTranspose = q) :
    (rotationUnitary hp hvp hvq 1 : Unitization ℂ (CStarMatrix (m ⊕ n) (m ⊕ n) A)) =
      1 - 2 * (rotationProjection p q v : Unitization ℂ (CStarMatrix (m ⊕ n) (m ⊕ n) A)) := by
  have hrU : IsStarProjection
      (rotationProjection p q v : Unitization ℂ (CStarMatrix (m ⊕ n) (m ⊕ n) A)) :=
    (isStarProjection_rotationProjection hp hvp hvq).map (Unitization.inrNonUnitalStarAlgHom ℂ _)
  rw [rotationUnitary, mul_one]
  exact hrU.coe_expUnitary_pi_smul

theorem continuous_rotationUnitary {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    {v : CStarMatrix n m A} (hp : IsIdempotentElem p)
    (hvp : v.conjTranspose * v = p) (hvq : v * v.conjTranspose = q) :
    Continuous (rotationUnitary hp hvp hvq) :=
  selfAdjoint.continuous_expUnitary.comp (by fun_prop)

/-- Explicit norm-continuous path of star projections in `CStarMatrix (m ⊕ n) (m ⊕ n) A` from
`inl p` to `inr q` associated to a concrete rectangular matrix `v` implementing `p ∼ q`, over any
(possibly non-unital) C⋆-algebra `A`. -/
def rotationPath {p : CStarMatrix m m A} {q : CStarMatrix n n A} {v : CStarMatrix n m A}
    (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hvp : v.conjTranspose * v = p) (hvq : v * v.conjTranspose = q) :
    Path
      (⟨inl (n := n) (R := ℂ) p, hp.map (inl (n := n) (R := ℂ))⟩ :
        {P : CStarMatrix (m ⊕ n) (m ⊕ n) A // IsStarProjection P})
      ⟨inr (m := m) (R := ℂ) q, hq.map (inr (m := m) (R := ℂ))⟩ where
  toFun t :=
    ⟨((rotationUnitary hp.isIdempotentElem hvp hvq t :
          Unitization ℂ (CStarMatrix (m ⊕ n) (m ⊕ n) A)) *
        (inl (n := n) (R := ℂ) p : CStarMatrix (m ⊕ n) (m ⊕ n) A) *
        star (rotationUnitary hp.isIdempotentElem hvp hvq t :
          Unitization ℂ (CStarMatrix (m ⊕ n) (m ⊕ n) A))).snd,
      (unitization_conj_snd_eq_and_isStarProjection (hp.map (inl (n := n) (R := ℂ)))
        (rotationUnitary hp.isIdempotentElem hvp hvq t).2).2⟩
  continuous_toFun := by
    have hu : Continuous fun t : unitInterval ↦
        (rotationUnitary hp.isIdempotentElem hvp hvq t :
          Unitization ℂ (CStarMatrix (m ⊕ n) (m ⊕ n) A)) :=
      continuous_subtype_val.comp
        ((continuous_rotationUnitary hp.isIdempotentElem hvp hvq).comp continuous_subtype_val)
    exact Continuous.subtype_mk
      (Unitization.continuous_snd.comp ((hu.mul continuous_const).mul (continuous_star.comp hu))) _
  source' := by
    refine Subtype.ext (Unitization.inr_injective (R := ℂ) ?_)
    rw [(unitization_conj_snd_eq_and_isStarProjection (hp.map (inl (n := n) (R := ℂ)))
      (rotationUnitary hp.isIdempotentElem hvp hvq (0 : unitInterval)).2).1]
    simp
  target' := by
    have hrU : IsStarProjection
        (rotationProjection p q v : Unitization ℂ (CStarMatrix (m ⊕ n) (m ⊕ n) A)) :=
      (isStarProjection_rotationProjection hp.isIdempotentElem hvp hvq).map
        (Unitization.inrNonUnitalStarAlgHom ℂ _)
    refine Subtype.ext (Unitization.inr_injective (R := ℂ) ?_)
    rw [(unitization_conj_snd_eq_and_isStarProjection (hp.map (inl (n := n) (R := ℂ)))
      (rotationUnitary hp.isIdempotentElem hvp hvq (1 : unitInterval)).2).1]
    simp only [Set.Icc.coe_one, coe_rotationUnitary_one, hrU.isSelfAdjoint_one_sub_two_mul.star_eq,
      inl_apply, inr_apply]
    exact unitization_one_sub_two_mul_rotationProjection_conj hp.isIdempotentElem hvp hvq

/-- Evaluated inside `Unitization ℂ (CStarMatrix (m ⊕ n) (m ⊕ n) A)`, `rotationPath` is conjugation
of `inl p` by `rotationUnitary`. -/
theorem inr_coe_rotationPath_apply {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    {v : CStarMatrix n m A} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hvp : v.conjTranspose * v = p) (hvq : v * v.conjTranspose = q) (t : unitInterval) :
    ((rotationPath hp hq hvp hvq t : CStarMatrix (m ⊕ n) (m ⊕ n) A) :
        Unitization ℂ (CStarMatrix (m ⊕ n) (m ⊕ n) A)) =
      (rotationUnitary hp.isIdempotentElem hvp hvq t :
          Unitization ℂ (CStarMatrix (m ⊕ n) (m ⊕ n) A)) *
        (inl (n := n) (R := ℂ) p : CStarMatrix (m ⊕ n) (m ⊕ n) A) *
        star (rotationUnitary hp.isIdempotentElem hvp hvq t :
          Unitization ℂ (CStarMatrix (m ⊕ n) (m ⊕ n) A)) :=
  (unitization_conj_snd_eq_and_isStarProjection (hp.map (inl (n := n) (R := ℂ)))
    (rotationUnitary hp.isIdempotentElem hvp hvq t).2).1

namespace MurrayVonNeumannEquivalent

/-- Murray–von Neumann equivalent projections `p : CStarMatrix m m A` and `q : CStarMatrix n n A`
become path-connected inside the space of star projections of `CStarMatrix (m ⊕ n) (m ⊕ n) A` as
`inl p` and `inr q`. -/
theorem joined_inl_inr {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    (hp : IsStarProjection p) (h : p.MurrayVonNeumannEquivalent q) :
    Joined
      (⟨inl (n := n) (R := ℂ) p, hp.map (inl (n := n) (R := ℂ))⟩ :
        {P : CStarMatrix (m ⊕ n) (m ⊕ n) A // IsStarProjection P})
      ⟨inr (m := m) (R := ℂ) q, (h.isStarProjection_iff.mp hp).map (inr (m := m) (R := ℂ))⟩ := by
  have hq : IsStarProjection q := h.isStarProjection_iff.mp hp
  rcases h with ⟨v, hvp, hvq⟩
  exact ⟨rotationPath hp hq hvp hvq⟩

/-- Two Murray–von Neumann equivalent projections `p, q : CStarMatrix n n A` of the same matrix
size become path-connected after `2 × 2` stabilization `P ↦ fromBlocks P 0 0 0` inside the space
of star projections of `CStarMatrix (n ⊕ n) (n ⊕ n) A`. -/
theorem joined_inl_inl {p q : CStarMatrix n n A}
    (hp : IsStarProjection p) (h : p.MurrayVonNeumannEquivalent q) :
    Joined
      (⟨inl (n := n) (R := ℂ) p, hp.map (inl (n := n) (R := ℂ))⟩ :
        {P : CStarMatrix (n ⊕ n) (n ⊕ n) A // IsStarProjection P})
      ⟨inl (n := n) (R := ℂ) q, (h.isStarProjection_iff.mp hp).map (inl (n := n) (R := ℂ))⟩ := by
  have hq : IsStarProjection q := h.isStarProjection_iff.mp hp
  exact (h.joined_inl_inr hp).trans (hq.murrayVonNeumannEquivalent_refl.joined_inl_inr hq).symm

end MurrayVonNeumannEquivalent

end NonUnitalCStar

section UnitalCStar

variable {m n A : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CStarAlgebra A]

/-- Over a unital C⋆-algebra `A`, `1 - 2 * rotationProjection p q v` equals
`stabilizedSymmetry p q v = fromBlocks (1 - p) v.conjTranspose v (1 - q)`. -/
theorem one_sub_two_mul_rotationProjection
    (p : CStarMatrix m m A) (q : CStarMatrix n n A) (v : CStarMatrix n m A) :
    1 - 2 * rotationProjection p q v = stabilizedSymmetry p q v := by
  have htwo : 2 * rotationProjection p q v = (2 : ℂ) • rotationProjection p q v := by
    rw [two_mul, two_smul]
  rw [htwo, two_smul_rotationProjection, ← fromBlocks_one, fromBlocks_sub, stabilizedSymmetry]
  simp

variable [PartialOrder A] [StarOrderedRing A]

/-- Over a unital C⋆-algebra `A`, `expUnitary (π • ⟨rotationProjection p q v, _⟩)` evaluates to
`stabilizedSymmetry p q v`. -/
theorem expUnitary_pi_smul_rotationProjection
    {p : CStarMatrix m m A} {q : CStarMatrix n n A} {v : CStarMatrix n m A}
    (hp : IsIdempotentElem p) (hvp : v.conjTranspose * v = p) (hvq : v * v.conjTranspose = q) :
    selfAdjoint.expUnitary (Real.pi • ⟨rotationProjection p q v,
      (isStarProjection_rotationProjection hp hvp hvq).isSelfAdjoint⟩) =
      ⟨stabilizedSymmetry p q v, stabilizedSymmetry_mem_unitary hp hvp hvq⟩ :=
  ((isStarProjection_rotationProjection hp hvp hvq).expUnitary_pi_smul).trans
    (Subtype.ext (one_sub_two_mul_rotationProjection p q v))

end UnitalCStar

end RotationPath

end StabilizedUnitaryAndRotationPath

end CStarMatrix

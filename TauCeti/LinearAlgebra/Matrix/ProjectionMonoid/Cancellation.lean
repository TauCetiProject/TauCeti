/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.ProjectionMonoid.KZero

/-!
# Projection cancellation

A star ring `R` has *projection cancellation* when matrix projections `p`, `q` and `r` over `R`
with `p ⊕ r ∼ q ⊕ r` (Murray–von Neumann equivalence of the block sums, of possibly different
sizes) satisfy `p ∼ q`. This is exactly cancellativity of the projection monoid `V(R)`, and
exactly injectivity of the class map `V(R) → K₀(R)`; under it, two matrix projections have the
same class in `K₀(R)` if and only if they are equivalent. Over a unital star ring it suffices to
cancel identity matrices `r = 1ₖ`, since `r ⊕ (1 - r) ∼ 1ₖ`.

Cancellation is not automatic: for a Cuntz pair in `O₂`, `1 ⊕ 1 ∼ 1 = 1 ⊕ 0` while `1 ≁ 0`. Over
`ℝ` or `ℂ` (any `RCLike` field) it holds (`TauCeti.hasProjectionCancellation_rclike` in
`TauCeti.Analysis.Matrix.ProjectionCancellation`), since matrix projections there are equivalent
exactly when they have the same rank, and rank is additive on block sums.

## Main definitions

* `TauCeti.HasProjectionCancellation R`: projection cancellation for the star ring `R`.

## Main statements

* `Matrix.IsMurrayVonNeumannEquivalent.fromBlocks_right_cancel`: if `V(R)` is cancellative, then
  `p ⊕ r ∼ q ⊕ r` implies `p ∼ q` for matrix projections indexed by arbitrary finite types.
* `TauCeti.hasProjectionCancellation_iff_isCancelAdd`: projection cancellation is cancellativity
  of `V(R)`.
* `TauCeti.hasProjectionCancellation_iff_grothendieckAddGroupOf_injective`: projection
  cancellation is injectivity of the class map `V(R) → K₀(R)`.
* `TauCeti.ProjectionKZero.of_mk_eq_of_mk_iff_of_hasProjectionCancellation`: under projection
  cancellation, `[p] = [q]` in `K₀(R)` exactly when `p ∼ q`.
* `TauCeti.hasProjectionCancellation_iff_one`: over a unital star ring, cancelling identity
  matrices suffices.

## References

* M. Rørdam, Part I of Rørdam–Størmer, *Classification of Nuclear C⋆-Algebras. Entropy in
  Operator Algebras*, Encyclopaedia of Mathematical Sciences 126, Springer (2002), Section 1.3.
-/

public section

open Matrix Algebra

namespace TauCeti

variable (R : Type*) [NonUnitalSemiring R] [StarRing R]

/-- A star ring `R` has **projection cancellation** when matrix projections `p`, `q`, `r` over
`R` with `p ⊕ r ∼ q ⊕ r` satisfy `p ∼ q`, where `∼` is Murray–von Neumann equivalence of matrix
projections of possibly different sizes. -/
def HasProjectionCancellation : Prop :=
  ∀ ⦃k l j : ℕ⦄ (p : Matrix (Fin k) (Fin k) R) (q : Matrix (Fin l) (Fin l) R)
    (r : Matrix (Fin j) (Fin j) R),
    IsMurrayVonNeumannEquivalent (fromBlocks p 0 0 r) (fromBlocks q 0 0 r) →
      IsMurrayVonNeumannEquivalent p q

variable {R} {m n l : Type*} [Fintype m] [Fintype n] [Fintype l]

/-- `HasProjectionCancellation R` holds exactly when `p ⊕ r ∼ q ⊕ r` implies `p ∼ q` for all
matrix projections `p`, `q`, `r` over `R` indexed by `Fin k`, `Fin l` and `Fin j`. -/
theorem hasProjectionCancellation_iff :
    HasProjectionCancellation R ↔
      ∀ ⦃k l j : ℕ⦄ (p : Matrix (Fin k) (Fin k) R) (q : Matrix (Fin l) (Fin l) R)
        (r : Matrix (Fin j) (Fin j) R),
        IsMurrayVonNeumannEquivalent (fromBlocks p 0 0 r) (fromBlocks q 0 0 r) →
          IsMurrayVonNeumannEquivalent p q :=
  Iff.rfl

/-- If `p ⊕ r ∼ q ⊕ r`, then `p`, `q` and `r` are projections and `[p] + [r] = [q] + [r]` in
`V(R)`. -/
theorem ProjectionMonoid.exists_mk_add_mk_eq_mk_add_mk_of_isMurrayVonNeumannEquivalent
    {p : Matrix m m R} {q : Matrix n n R} {r : Matrix l l R}
    (hpqr : IsMurrayVonNeumannEquivalent (fromBlocks p 0 0 r) (fromBlocks q 0 0 r)) :
    ∃ (hp : IsStarProjection p) (hq : IsStarProjection q) (hr : IsStarProjection r),
      mk p hp + mk r hr = mk q hq + mk r hr := by
  obtain ⟨hp, hr⟩ := isStarProjection_fromBlocks_zero₁₂_zero₂₁_iff.1 hpqr.isStarProjection_left
  have hq := (isStarProjection_fromBlocks_zero₁₂_zero₂₁_iff.1 hpqr.isStarProjection_right).1
  refine ⟨hp, hq, hr, ?_⟩
  rw [← mk_fromBlocks, ← mk_fromBlocks]
  exact mk_eq_mk hpqr

/-- If `V(R)` is cancellative, then `p ⊕ r ∼ q ⊕ r` implies `p ∼ q` for matrix projections indexed
by arbitrary finite types. -/
theorem _root_.Matrix.IsMurrayVonNeumannEquivalent.fromBlocks_right_cancel
    [IsCancelAdd (ProjectionMonoid R)] {p : Matrix m m R} {q : Matrix n n R} {r : Matrix l l R}
    (hpqr : IsMurrayVonNeumannEquivalent (fromBlocks p 0 0 r) (fromBlocks q 0 0 r)) :
    IsMurrayVonNeumannEquivalent p q := by
  obtain ⟨hp, hq, _, e⟩ :=
    ProjectionMonoid.exists_mk_add_mk_eq_mk_add_mk_of_isMurrayVonNeumannEquivalent hpqr
  exact (ProjectionMonoid.mk_eq_mk_iff hp hq).1 (add_right_cancel e)

/-- **Projection cancellation is cancellativity of `V(R)`.** -/
theorem hasProjectionCancellation_iff_isCancelAdd :
    HasProjectionCancellation R ↔ IsCancelAdd (ProjectionMonoid R) := by
  refine ⟨fun h ↦ ?_, fun _ _ _ _ _ _ _ ↦ IsMurrayVonNeumannEquivalent.fromBlocks_right_cancel⟩
  have : IsRightCancelAdd (ProjectionMonoid R) := ⟨fun z x y hxy ↦ by
    induction x using ProjectionMonoid.ind with | mk _ p hp => ?_
    induction y using ProjectionMonoid.ind with | mk _ q hq => ?_
    induction z using ProjectionMonoid.ind with | mk _ r hr => ?_
    simp only at hxy
    rw [← ProjectionMonoid.mk_fromBlocks, ← ProjectionMonoid.mk_fromBlocks,
      ProjectionMonoid.mk_eq_mk_iff] at hxy
    exact ProjectionMonoid.mk_eq_mk (h p q r hxy)⟩
  exact AddCommMagma.IsRightCancelAdd.toIsCancelAdd _

/-- **Projection cancellation is injectivity of the class map `V(R) → K₀(R)`.** -/
theorem hasProjectionCancellation_iff_grothendieckAddGroupOf_injective :
    HasProjectionCancellation R ↔
      Function.Injective (GrothendieckAddGroup.of : ProjectionMonoid R →+ ProjectionKZero R) := by
  rw [hasProjectionCancellation_iff_isCancelAdd]
  refine ⟨fun _ ↦ GrothendieckAddGroup.of_injective, fun h ↦ ?_⟩
  have : IsRightCancelAdd (ProjectionMonoid R) := ⟨fun z x y hxy ↦ h (by
    simpa using congrArg (GrothendieckAddGroup.of : ProjectionMonoid R →+ ProjectionKZero R) hxy)⟩
  exact AddCommMagma.IsRightCancelAdd.toIsCancelAdd _

namespace HasProjectionCancellation

/-- Under projection cancellation, `p ⊕ r ∼ q ⊕ r` implies `p ∼ q` for matrix projections indexed
by arbitrary finite types. -/
theorem isMurrayVonNeumannEquivalent (h : HasProjectionCancellation R) {p : Matrix m m R}
    {q : Matrix n n R} {r : Matrix l l R}
    (hpqr : IsMurrayVonNeumannEquivalent (fromBlocks p 0 0 r) (fromBlocks q 0 0 r)) :
    IsMurrayVonNeumannEquivalent p q :=
  have := hasProjectionCancellation_iff_isCancelAdd.1 h
  hpqr.fromBlocks_right_cancel

end HasProjectionCancellation

/-- Under projection cancellation, matrix projections have the same class in `K₀(R)` exactly
when they are Murray–von Neumann equivalent. -/
theorem ProjectionKZero.of_mk_eq_of_mk_iff_of_hasProjectionCancellation
    (h : HasProjectionCancellation R) {p : Matrix m m R} {q : Matrix n n R}
    (hp : IsStarProjection p) (hq : IsStarProjection q) :
    (GrothendieckAddGroup.of (ProjectionMonoid.mk p hp) : ProjectionKZero R) =
        GrothendieckAddGroup.of (ProjectionMonoid.mk q hq) ↔
      IsMurrayVonNeumannEquivalent p q := by
  rw [(hasProjectionCancellation_iff_grothendieckAddGroupOf_injective.1 h).eq_iff,
    ProjectionMonoid.mk_eq_mk_iff]

/-- **Cancelling identity matrices suffices.** A unital star ring has projection cancellation
exactly when `p ⊕ 1ⱼ ∼ q ⊕ 1ⱼ` implies `p ∼ q` for all matrix projections `p`, `q` and all
sizes `j` of the identity matrix `1ⱼ`. -/
theorem hasProjectionCancellation_iff_one {A : Type*} [Ring A] [StarRing A] :
    HasProjectionCancellation A ↔
      ∀ ⦃k l j : ℕ⦄ (p : Matrix (Fin k) (Fin k) A) (q : Matrix (Fin l) (Fin l) A),
        IsMurrayVonNeumannEquivalent (fromBlocks p 0 0 (1 : Matrix (Fin j) (Fin j) A))
          (fromBlocks q 0 0 (1 : Matrix (Fin j) (Fin j) A)) →
        IsMurrayVonNeumannEquivalent p q := by
  refine ⟨fun h _ _ _ p q ↦ h p q 1, fun h k l j p q r hpqr ↦ ?_⟩
  -- `p ⊕ r ∼ q ⊕ r` gives `[p] = [q]` in `K₀(A)`, hence `p ⊕ 1ⱼ' ∼ q ⊕ 1ⱼ'` for some `j'`.
  obtain ⟨hp, hq, -⟩ :=
    ProjectionMonoid.exists_mk_add_mk_eq_mk_add_mk_of_isMurrayVonNeumannEquivalent hpqr
  obtain ⟨_, h'⟩ := (ProjectionKZero.of_mk_eq_of_mk_iff_exists_one hp hq).1
    ((ProjectionKZero.of_mk_eq_of_mk_iff hp hq).2 ⟨j, r, hpqr⟩)
  exact h p q h'

/-- The zero ring has projection cancellation: `V(R)` has a single element. -/
theorem hasProjectionCancellation_of_subsingleton [Subsingleton R] :
    HasProjectionCancellation R :=
  hasProjectionCancellation_iff_isCancelAdd.2
    { add_left_cancel _ _ _ _ := Subsingleton.elim _ _
      add_right_cancel _ _ _ _ := Subsingleton.elim _ _ }

end TauCeti

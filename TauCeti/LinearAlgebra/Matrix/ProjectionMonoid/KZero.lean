/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.ProjectionMonoid.Basic
public import TauCeti.RingTheory.GrothendieckRing

/-!
# The projection `K₀`-group

Let `R` be a star ring. Its *projection `K₀`-group* `K₀(R)` is the Grothendieck group of the
projection monoid `V(R)` (`TauCeti.ProjectionMonoid R`), the matrix projections over `R` of all
finite sizes modulo Murray–von Neumann equivalence under block sum. For a unital C⋆-algebra `A`
this is the operator `K₀`-group of `A`. For a nonunital algebra the operator `K₀`-group is
defined differently, through the unitization, and does not agree with this group in general.

Write `[p]` for the image in `K₀(R)` of the class of a matrix projection `p`, that is
`Algebra.GrothendieckAddGroup.of (TauCeti.ProjectionMonoid.mk p hp)`. No cancellation is assumed
in `V(R)`, so `[p] = [q]` does not force `p` and `q` to be equivalent; it holds exactly when
`p ⊕ r` and `q ⊕ r` are equivalent for some matrix projection `r`. Over a unital star ring `r`
can be taken to be an identity matrix, and every element of `K₀(R)` is `[p] - [1ₗ]` for a matrix
projection `p` and the identity matrix `1ₗ` of some size `l`.

The universal property of `K₀(R)` is that of the Grothendieck group: an additive monoid
homomorphism from `V(R)` to an abelian group extends uniquely along the class map, by
`Algebra.GrothendieckAddGroup.lift` (with `Algebra.GrothendieckAddGroup.lift_apply_of` and
`Algebra.GrothendieckAddGroup.addHom_ext`).

## Main definitions

* `TauCeti.ProjectionKZero R`: the group `K₀(R)`, the Grothendieck group of `V(R)`.
* `TauCeti.ProjectionKZero.map f`: the homomorphism `K₀(R) →+ K₀(S)` induced entrywise by a star
  ring homomorphism `f : R →⋆ₙ+* S`, unital or not.
* `TauCeti.ProjectionKZero.mapEquiv e`: the isomorphism `K₀(R) ≃+ K₀(S)` induced by a star ring
  isomorphism `e : R ≃⋆+* S`.

## Main statements

* `TauCeti.ProjectionKZero.exists_eq_sub`: every element of `K₀(R)` is `[p] - [q]` for matrix
  projections `p` and `q`.
* `TauCeti.ProjectionKZero.of_mk_eq_of_mk_iff`: `[p] = [q]` exactly when `p ⊕ r ∼ q ⊕ r` for some
  matrix projection `r`.
* `TauCeti.ProjectionKZero.of_mk_sub_of_mk_eq_of_mk_sub_of_mk_iff`: `[p] - [q] = [p'] - [q']`
  exactly when `p ⊕ q' ⊕ r ∼ p' ⊕ q ⊕ r` for some matrix projection `r`.
* `TauCeti.ProjectionKZero.of_mk_eq_of_mk_iff_exists_one`: over a unital star ring, `[p] = [q]`
  exactly when `p ⊕ 1ₖ ∼ q ⊕ 1ₖ` for some `k`.
* `TauCeti.ProjectionKZero.exists_eq_sub_one`: over a unital star ring, every element of `K₀(R)`
  is `[p] - [1ₗ]`.
* `TauCeti.ProjectionKZero.map_id` and `TauCeti.ProjectionKZero.map_comp`: functoriality.

## References

* B. Blackadar, *K-Theory for Operator Algebras*, 2nd ed., Cambridge University Press (1998),
  Definition 5.3.1.
* M. Rørdam, F. Larsen and N. Laustsen, *An Introduction to K-Theory for C⋆-Algebras*,
  Cambridge University Press (2000), Section 3.1, in particular Proposition 3.1.7.
-/

public section

open Matrix Algebra

namespace TauCeti

variable (R : Type*) [NonUnitalSemiring R] [StarRing R]

/-- The **projection `K₀`-group** of a star ring `R`: the Grothendieck group of the projection
monoid `V(R)` of matrix projections modulo Murray–von Neumann equivalence. For a unital
C⋆-algebra this is its operator `K₀`-group. -/
abbrev ProjectionKZero : Type _ :=
  GrothendieckAddGroup (ProjectionMonoid R)

namespace ProjectionKZero

variable {R} {m n m' n' : Type*} [Fintype m] [Fintype n] [Fintype m'] [Fintype n']

/-- **Generation by differences.** Every element of `K₀(R)` is `[p] - [q]` for matrix
projections `p` and `q`. -/
theorem exists_eq_sub (x : ProjectionKZero R) :
    ∃ (k l : ℕ) (p : Matrix (Fin k) (Fin k) R) (hp : IsStarProjection p)
      (q : Matrix (Fin l) (Fin l) R) (hq : IsStarProjection q),
      x = GrothendieckAddGroup.of (ProjectionMonoid.mk p hp) -
        GrothendieckAddGroup.of (ProjectionMonoid.mk q hq) := by
  obtain ⟨a, b, rfl⟩ := GrothendieckAddGroup.exists_eq_sub_of x
  obtain ⟨k, p, hp, rfl⟩ := ProjectionMonoid.exists_eq_mk a
  obtain ⟨l, q, hq, rfl⟩ := ProjectionMonoid.exists_eq_mk b
  exact ⟨k, l, p, hp, q, hq, rfl⟩

/-- **Equality criterion.** Matrix projections `p` and `q`, of possibly different sizes, have the
same class in `K₀(R)` exactly when `p ⊕ r` and `q ⊕ r` are Murray–von Neumann equivalent for some
matrix projection `r`. -/
theorem of_mk_eq_of_mk_iff {p : Matrix m m R} {q : Matrix n n R} (hp : IsStarProjection p)
    (hq : IsStarProjection q) :
    (GrothendieckAddGroup.of (ProjectionMonoid.mk p hp) : ProjectionKZero R) =
        GrothendieckAddGroup.of (ProjectionMonoid.mk q hq) ↔
      ∃ (k : ℕ) (r : Matrix (Fin k) (Fin k) R),
        IsMurrayVonNeumannEquivalent (fromBlocks p 0 0 r) (fromBlocks q 0 0 r) := by
  rw [GrothendieckAddGroup.of_eq_of_iff]
  constructor
  · rintro ⟨c, h⟩
    obtain ⟨k, r, hr, rfl⟩ := ProjectionMonoid.exists_eq_mk c
    rw [← ProjectionMonoid.mk_fromBlocks, ← ProjectionMonoid.mk_fromBlocks,
      ProjectionMonoid.mk_eq_mk_iff] at h
    exact ⟨k, r, h⟩
  · rintro ⟨k, r, h⟩
    have hr := (isStarProjection_fromBlocks_zero₁₂_zero₂₁_iff.1 h.isStarProjection_left).2
    refine ⟨ProjectionMonoid.mk r hr, ?_⟩
    rw [← ProjectionMonoid.mk_fromBlocks, ← ProjectionMonoid.mk_fromBlocks]
    exact ProjectionMonoid.mk_eq_mk h

/-- **Equality criterion for differences.** For matrix projections `p`, `q`, `p'` and `q'`,
`[p] - [q] = [p'] - [q']` in `K₀(R)` exactly when `p ⊕ q' ⊕ r` and `p' ⊕ q ⊕ r` are
Murray–von Neumann equivalent for some matrix projection `r`. -/
theorem of_mk_sub_of_mk_eq_of_mk_sub_of_mk_iff {p : Matrix m m R} {q : Matrix n n R}
    {p' : Matrix m' m' R} {q' : Matrix n' n' R} (hp : IsStarProjection p)
    (hq : IsStarProjection q) (hp' : IsStarProjection p') (hq' : IsStarProjection q') :
    (GrothendieckAddGroup.of (ProjectionMonoid.mk p hp) -
        GrothendieckAddGroup.of (ProjectionMonoid.mk q hq) : ProjectionKZero R) =
        GrothendieckAddGroup.of (ProjectionMonoid.mk p' hp') -
          GrothendieckAddGroup.of (ProjectionMonoid.mk q' hq') ↔
      ∃ (k : ℕ) (r : Matrix (Fin k) (Fin k) R),
        IsMurrayVonNeumannEquivalent (fromBlocks (fromBlocks p 0 0 q') 0 0 r)
          (fromBlocks (fromBlocks p' 0 0 q) 0 0 r) := by
  rw [sub_eq_sub_iff_add_eq_add, ← map_add, ← map_add, ← ProjectionMonoid.mk_fromBlocks hp hq',
    ← ProjectionMonoid.mk_fromBlocks hp' hq, of_mk_eq_of_mk_iff]

section Ring

variable {A : Type*} [Ring A] [StarRing A]

/-- **Stable equivalence.** Over a unital star ring, matrix projections `p` and `q` have the same
class in `K₀(A)` exactly when `p ⊕ 1ₖ` and `q ⊕ 1ₖ` are Murray–von Neumann equivalent for the
identity matrix `1ₖ` of some size `k`. -/
theorem of_mk_eq_of_mk_iff_exists_one {p : Matrix m m A} {q : Matrix n n A}
    (hp : IsStarProjection p) (hq : IsStarProjection q) :
    (GrothendieckAddGroup.of (ProjectionMonoid.mk p hp) : ProjectionKZero A) =
        GrothendieckAddGroup.of (ProjectionMonoid.mk q hq) ↔
      ∃ k : ℕ, IsMurrayVonNeumannEquivalent (fromBlocks p 0 0 (1 : Matrix (Fin k) (Fin k) A))
        (fromBlocks q 0 0 (1 : Matrix (Fin k) (Fin k) A)) := by
  refine ⟨fun h ↦ ?_, fun ⟨k, h⟩ ↦ (of_mk_eq_of_mk_iff hp hq).2 ⟨k, 1, h⟩⟩
  obtain ⟨k, r, h⟩ := (of_mk_eq_of_mk_iff hp hq).1 h
  have hr := (isStarProjection_fromBlocks_zero₁₂_zero₂₁_iff.1 h.isStarProjection_left).2
  refine ⟨k, ?_⟩
  -- Adding the complement `1 - r` to both sides of `[p] + [r] = [q] + [r]` in `V(A)`.
  rw [← ProjectionMonoid.mk_eq_mk_iff (hp.fromBlocks_zero₁₂_zero₂₁ (.one _))
      (hq.fromBlocks_zero₁₂_zero₂₁ (.one _)), ProjectionMonoid.mk_fromBlocks hp (.one _),
    ProjectionMonoid.mk_fromBlocks hq (.one _), ← ProjectionMonoid.mk_add_mk_one_sub hr,
    ← add_assoc, ← add_assoc, ← ProjectionMonoid.mk_fromBlocks hp hr,
    ← ProjectionMonoid.mk_fromBlocks hq hr, ProjectionMonoid.mk_eq_mk h]

/-- **Generation by differences, unital form.** Over a unital star ring, every element of `K₀(A)`
is `[p] - [1ₗ]` for a matrix projection `p` and the identity matrix `1ₗ` of some size `l`. -/
theorem exists_eq_sub_one (x : ProjectionKZero A) :
    ∃ (k : ℕ) (p : Matrix (Fin k) (Fin k) A) (hp : IsStarProjection p) (l : ℕ),
      x = GrothendieckAddGroup.of (ProjectionMonoid.mk p hp) -
        GrothendieckAddGroup.of (ProjectionMonoid.mk (1 : Matrix (Fin l) (Fin l) A) (.one _)) := by
  obtain ⟨k, l, p, hp, q, hq, rfl⟩ := exists_eq_sub x
  have hpq := hp.fromBlocks_zero₁₂_zero₂₁ hq.one_sub
  refine ⟨k + l, reindex finSumFinEquiv finSumFinEquiv (fromBlocks p 0 0 (1 - q)),
    (hpq.isMurrayVonNeumannEquivalent_reindex _).isStarProjection_right, l, ?_⟩
  -- `[p] - [q] = [p ⊕ (1 - q)] - [q ⊕ (1 - q)]`, and `[q ⊕ (1 - q)] = [1ₗ]`.
  rw [ProjectionMonoid.mk_reindex hpq, ProjectionMonoid.mk_fromBlocks hp hq.one_sub,
    ← ProjectionMonoid.mk_add_mk_one_sub hq, map_add, map_add, add_sub_add_right_eq_sub]

end Ring

section map

variable {S T : Type*} [NonUnitalSemiring S] [StarRing S] [NonUnitalSemiring T] [StarRing T]

/-- **Functoriality.** A star ring homomorphism `f : R →⋆ₙ+* S`, unital or not, applied to
matrix entries induces a homomorphism `K₀(R) →+ K₀(S)`, the extension of
`TauCeti.ProjectionMonoid.map f` to the Grothendieck groups. -/
noncomputable def map (f : R →⋆ₙ+* S) : ProjectionKZero R →+ ProjectionKZero S :=
  GrothendieckAddGroup.lift
    ((GrothendieckAddGroup.of : ProjectionMonoid S →+ _).comp (ProjectionMonoid.map f))

-- Not `@[simp]`: the simp normal form of `Algebra.GrothendieckAddGroup.of x` is
-- `AddLocalization.addMonoidOf ⊤ x`, as for `Algebra.GrothendieckAddGroup.lift_apply_of`.
/-- On the image of `V(R)`, `TauCeti.ProjectionKZero.map f` is `TauCeti.ProjectionMonoid.map f`.
-/
theorem map_of (f : R →⋆ₙ+* S) (x : ProjectionMonoid R) :
    map f (GrothendieckAddGroup.of x) = GrothendieckAddGroup.of (ProjectionMonoid.map f x) :=
  GrothendieckAddGroup.lift_apply_of _ x

/-- The image under `TauCeti.ProjectionKZero.map f` of the class of `p` is the class of the
entrywise image of `p`. -/
theorem map_of_mk (f : R →⋆ₙ+* S) {p : Matrix m m R} (hp : IsStarProjection p) :
    map f (GrothendieckAddGroup.of (ProjectionMonoid.mk p hp)) =
      GrothendieckAddGroup.of (ProjectionMonoid.mk (p.map f) (hp.matrix_map f)) := by
  rw [map_of, ProjectionMonoid.map_mk]

/-- The identity homomorphism induces the identity of `K₀(R)`. -/
@[simp]
theorem map_id : map (NonUnitalStarRingHom.id R) = AddMonoidHom.id (ProjectionKZero R) :=
  GrothendieckAddGroup.addHom_ext fun x ↦ by
    rw [map_of, ProjectionMonoid.map_id, AddMonoidHom.id_apply, AddMonoidHom.id_apply]

/-- The homomorphism induced by a composite is the composite of the induced homomorphisms. -/
theorem map_comp (g : S →⋆ₙ+* T) (f : R →⋆ₙ+* S) :
    map (g.comp f) = (map g).comp (map f) :=
  GrothendieckAddGroup.addHom_ext fun x ↦ by
    rw [AddMonoidHom.comp_apply, map_of, map_of, map_of, ProjectionMonoid.map_comp,
      AddMonoidHom.comp_apply]

/-- Applying the homomorphisms induced by `f` and then by `g` on `K₀` is applying the
homomorphism induced by their composite. -/
theorem map_map (g : S →⋆ₙ+* T) (f : R →⋆ₙ+* S) (x : ProjectionKZero R) :
    map g (map f x) = map (g.comp f) x := by
  rw [map_comp, AddMonoidHom.comp_apply]

/-- If a star ring homomorphism vanishes, so does the homomorphism it induces on `K₀`. -/
theorem map_eq_zero_of_forall_eq_zero {f : R →⋆ₙ+* S} (hf : ∀ r, f r = 0) : map f = 0 :=
  GrothendieckAddGroup.addHom_ext fun x ↦ by
    rw [map_of, ProjectionMonoid.map_eq_zero_of_forall_eq_zero hf, map_zero,
      AddMonoidHom.zero_apply]

/-- **Invariance under isomorphism.** A star ring isomorphism `e : R ≃⋆+* S` induces an
isomorphism `K₀(R) ≃+ K₀(S)`, with inverse induced by `e.symm`. -/
noncomputable def mapEquiv (e : R ≃⋆+* S) : ProjectionKZero R ≃+ ProjectionKZero S :=
  AddMonoidHom.toAddEquiv (map e) (map e.symm)
    (by rw [← map_comp, ← map_id]; exact congrArg map (NonUnitalStarRingHom.ext e.symm_apply_apply))
    (by rw [← map_comp, ← map_id]; exact congrArg map (NonUnitalStarRingHom.ext e.apply_symm_apply))

/-- The isomorphism induced by `e : R ≃⋆+* S` is `TauCeti.ProjectionKZero.map e`. -/
@[simp]
theorem mapEquiv_apply (e : R ≃⋆+* S) (x : ProjectionKZero R) : mapEquiv e x = map e x :=
  (rfl)

/-- The inverse of the isomorphism induced by `e : R ≃⋆+* S` is induced by `e.symm`. -/
@[simp]
theorem mapEquiv_symm_apply (e : R ≃⋆+* S) (x : ProjectionKZero S) :
    (mapEquiv e).symm x = map e.symm x :=
  (rfl)

end map

end ProjectionKZero

end TauCeti

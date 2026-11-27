/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.ProjectionMonoid.KZero

/-!
# The positive cone, scale and order unit of the projection `K₀`-group

Let `R` be a star ring and `K₀(R)` its projection `K₀`-group (`TauCeti.ProjectionKZero R`), the
Grothendieck group of the projection monoid `V(R)`. Its *positive cone* `K₀(R)⁺` is the image of
`V(R)`, the classes `[p]` of matrix projections over `R`, and its *scale* is the set of classes of
projections in `R` itself, written as `1 × 1` matrices. The cone is an additive submonoid; it
defines the preorder `x ≤ y ↔ y - x ∈ K₀(R)⁺`, which is a partial order when the cone is proper
(Mathlib's `PartialOrder.ofAddSubmonoid` under `AddSubmonoid.IsPointed`).

For a unital star ring `A` the class `[1]` of the identity of `A`
(`TauCeti.ProjectionKZero.orderUnit A`) lies in the scale, every element of the scale lies below
it, and it is an *order unit*: every `x ∈ K₀(A)` satisfies `-n[1] ≤ x ≤ n[1]` for some `n : ℕ`.
Writing `x = [p] - [1ₗ]` for a projection `p` in the `k × k` matrices, `k[1] - x = [1ₖ - p] + [1ₗ]`
and `x + l[1] = [p]` are in the cone.

Star ring homomorphisms preserve the cone and the scale, and unital ones preserve the order unit.

## Main definitions

* `TauCeti.ProjectionKZero.positiveCone R`: the positive cone `K₀(R)⁺`, the image of `V(R)`.
* `TauCeti.ProjectionKZero.scale R`: the classes of projections of `R`.
* `TauCeti.ProjectionKZero.orderUnit A`: the class `[1]` of the identity of a unital star ring.

## Main statements

* `TauCeti.ProjectionKZero.scale_subset_positiveCone`: the scale lies in the positive cone.
* `TauCeti.ProjectionKZero.orderUnit_mem_scale` and
  `TauCeti.ProjectionKZero.sub_mem_positiveCone_of_mem_scale`: over a unital star ring, `[1]` lies
  in the scale and above every element of it.
* `TauCeti.ProjectionKZero.exists_nsmul_sub_mem_positiveCone`: `[1]` is an order unit.
* `TauCeti.ProjectionKZero.map_mem_positiveCone`, `TauCeti.ProjectionKZero.map_mem_scale` and
  `TauCeti.ProjectionKZero.map_orderUnit`: star ring homomorphisms preserve the cone and the
  scale, and unital ones the order unit.

## References

* B. Blackadar, *K-Theory for Operator Algebras*, 2nd ed., Cambridge University Press (1998),
  Section 6.3.
-/

public section

open Matrix Algebra

namespace TauCeti

namespace ProjectionKZero

variable (R : Type*) [NonUnitalSemiring R] [StarRing R]

/-- The **positive cone** `K₀(R)⁺` of the projection `K₀`-group: the image of the projection
monoid `V(R)`, the classes of matrix projections over `R`. -/
noncomputable def positiveCone : AddSubmonoid (ProjectionKZero R) :=
  AddMonoidHom.mrange (GrothendieckAddGroup.of : ProjectionMonoid R →+ ProjectionKZero R)

/-- The **scale** of the projection `K₀`-group: the classes of projections of `R` itself, written
as `1 × 1` matrices. -/
def scale : Set (ProjectionKZero R) :=
  {x | ∃ (p : Matrix (Fin 1) (Fin 1) R) (hp : IsStarProjection p),
    GrothendieckAddGroup.of (ProjectionMonoid.mk p hp) = x}

variable {R} {m : Type*} [Fintype m]

/-- An element of `K₀(R)` lies in the positive cone exactly when it is the image of an element
of `V(R)`. -/
theorem mem_positiveCone_iff {x : ProjectionKZero R} :
    x ∈ positiveCone R ↔ ∃ y : ProjectionMonoid R, GrothendieckAddGroup.of y = x :=
  AddMonoidHom.mem_mrange

/-- An element of `K₀(R)` lies in the positive cone exactly when it is the class of a matrix
projection. -/
theorem mem_positiveCone_iff_exists_mk {x : ProjectionKZero R} :
    x ∈ positiveCone R ↔ ∃ (k : ℕ) (p : Matrix (Fin k) (Fin k) R) (hp : IsStarProjection p),
      GrothendieckAddGroup.of (ProjectionMonoid.mk p hp) = x := by
  rw [mem_positiveCone_iff]
  refine ⟨fun ⟨y, hy⟩ ↦ ?_, fun ⟨k, p, hp, h⟩ ↦ ⟨_, h⟩⟩
  obtain ⟨k, p, hp, rfl⟩ := ProjectionMonoid.exists_eq_mk y
  exact ⟨k, p, hp, hy⟩

-- Not `@[simp]`: the simp normal form of `Algebra.GrothendieckAddGroup.of x` is
-- `AddLocalization.addMonoidOf ⊤ x`, as for `TauCeti.ProjectionKZero.map_of`.
/-- The image of an element of `V(R)` lies in the positive cone. -/
theorem of_mem_positiveCone (y : ProjectionMonoid R) :
    (GrothendieckAddGroup.of y : ProjectionKZero R) ∈ positiveCone R :=
  mem_positiveCone_iff.2 ⟨y, rfl⟩

-- Not `@[simp]`: the simp normal form of `Algebra.GrothendieckAddGroup.of x` is
-- `AddLocalization.addMonoidOf ⊤ x`, as for `TauCeti.ProjectionKZero.map_of`.
/-- The class of a matrix projection lies in the positive cone. -/
theorem of_mk_mem_positiveCone {p : Matrix m m R} (hp : IsStarProjection p) :
    (GrothendieckAddGroup.of (ProjectionMonoid.mk p hp) : ProjectionKZero R) ∈ positiveCone R :=
  of_mem_positiveCone _

/-- An element of `K₀(R)` lies in the scale exactly when it is the class of a projection of `R`,
written as a `1 × 1` matrix. -/
theorem mem_scale_iff {x : ProjectionKZero R} :
    x ∈ scale R ↔ ∃ (p : Matrix (Fin 1) (Fin 1) R) (hp : IsStarProjection p),
      GrothendieckAddGroup.of (ProjectionMonoid.mk p hp) = x :=
  Iff.rfl

-- Not `@[simp]`: the simp normal form of `Algebra.GrothendieckAddGroup.of x` is
-- `AddLocalization.addMonoidOf ⊤ x`, as for `TauCeti.ProjectionKZero.map_of`.
/-- The class of a projection of `R`, written as a `1 × 1` matrix, lies in the scale. -/
theorem of_mk_mem_scale {p : Matrix (Fin 1) (Fin 1) R} (hp : IsStarProjection p) :
    (GrothendieckAddGroup.of (ProjectionMonoid.mk p hp) : ProjectionKZero R) ∈ scale R :=
  mem_scale_iff.2 ⟨p, hp, rfl⟩

/-- The scale lies in the positive cone. -/
theorem scale_subset_positiveCone : scale R ⊆ positiveCone R := by
  intro x hx
  obtain ⟨p, hp, rfl⟩ := mem_scale_iff.1 hx
  exact of_mk_mem_positiveCone hp

/-- `0` lies in the scale. -/
@[simp]
theorem zero_mem_scale : (0 : ProjectionKZero R) ∈ scale R :=
  mem_scale_iff.2 ⟨0, .zero _, by rw [ProjectionMonoid.mk_zero, map_zero]⟩

section Semiring

variable (A : Type*) [Semiring A] [StarRing A]

/-- The **order unit** `[1]` of `K₀(A)` for a unital star ring `A`: the class of the identity of
`A`, written as a `1 × 1` matrix. -/
noncomputable def orderUnit : ProjectionKZero A :=
  GrothendieckAddGroup.of (ProjectionMonoid.mk (1 : Matrix (Fin 1) (Fin 1) A) (.one _))

/-- `TauCeti.ProjectionKZero.orderUnit A` is the class of the `1 × 1` identity matrix. -/
theorem orderUnit_def :
    orderUnit A =
      GrothendieckAddGroup.of (ProjectionMonoid.mk (1 : Matrix (Fin 1) (Fin 1) A) (.one _)) :=
  (rfl)

/-- Over a unital star ring, the class `[1]` of the identity lies in the scale. -/
@[simp]
theorem orderUnit_mem_scale : orderUnit A ∈ scale A :=
  of_mk_mem_scale _

variable {A}

/-- Over a unital star ring, the class of the identity matrix of size `k` is `k [1]`. -/
theorem of_mk_one_eq_nsmul (k : ℕ) :
    (GrothendieckAddGroup.of (ProjectionMonoid.mk (1 : Matrix (Fin k) (Fin k) A) (.one _)) :
        ProjectionKZero A) = k • orderUnit A := by
  rw [orderUnit_def, ProjectionMonoid.mk_one, map_nsmul, Fintype.card_fin]

end Semiring

section Ring

variable {A : Type*} [Ring A] [StarRing A]

/-- Over a unital star ring, the class `[1]` of the identity lies above every element of the
scale: `[1] - [p] = [1 - p]`. -/
theorem sub_mem_positiveCone_of_mem_scale {x : ProjectionKZero A} (hx : x ∈ scale A) :
    orderUnit A - x ∈ positiveCone A := by
  obtain ⟨p, hp, rfl⟩ := mem_scale_iff.1 hx
  rw [orderUnit_def, ← ProjectionMonoid.mk_add_mk_one_sub hp, map_add, add_sub_cancel_left]
  exact of_mk_mem_positiveCone _

/-- **The order unit.** Over a unital star ring, the class `[1]` of the identity is an order unit
of `K₀(A)`: every `x` satisfies `-n [1] ≤ x ≤ n [1]` for some `n : ℕ`, that is, `n [1] - x` and
`x + n [1]` lie in the positive cone. -/
theorem exists_nsmul_sub_mem_positiveCone (x : ProjectionKZero A) :
    ∃ n : ℕ, n • orderUnit A - x ∈ positiveCone A ∧ x + n • orderUnit A ∈ positiveCone A := by
  obtain ⟨k, p, hp, l, rfl⟩ := exists_eq_sub_one x
  have hu := scale_subset_positiveCone (orderUnit_mem_scale A)
  -- `[p] + [1ₖ - p] = k [1]`.
  have hk := ProjectionMonoid.mk_add_mk_one_sub hp
  apply_fun (GrothendieckAddGroup.of : ProjectionMonoid A →+ ProjectionKZero A) at hk
  rw [map_add, of_mk_one_eq_nsmul] at hk
  refine ⟨k + l, ?_, ?_⟩
  · -- `(k + l) [1] - ([p] - l [1]) = [1ₖ - p] + (l + l) [1]`.
    rw [of_mk_one_eq_nsmul (A := A) l, add_nsmul, ← hk]
    convert add_mem (of_mk_mem_positiveCone hp.one_sub) (AddSubmonoid.nsmul_mem _ hu (l + l))
      using 1
    rw [add_nsmul]
    abel
  · -- `[p] - l [1] + (k + l) [1] = [p] + k [1]`.
    rw [of_mk_one_eq_nsmul (A := A) l, add_nsmul]
    convert add_mem (of_mk_mem_positiveCone hp) (AddSubmonoid.nsmul_mem _ hu k) using 1
    abel

end Ring

section map

variable {S : Type*} [NonUnitalSemiring S] [StarRing S]

/-- A star ring homomorphism, unital or not, maps the positive cone into the positive cone. -/
theorem map_mem_positiveCone (f : R →⋆ₙ+* S) {x : ProjectionKZero R} (hx : x ∈ positiveCone R) :
    map f x ∈ positiveCone S := by
  obtain ⟨y, rfl⟩ := mem_positiveCone_iff.1 hx
  rw [map_of]
  exact of_mem_positiveCone _

/-- A star ring homomorphism, unital or not, maps the scale into the scale. -/
theorem map_mem_scale (f : R →⋆ₙ+* S) {x : ProjectionKZero R} (hx : x ∈ scale R) :
    map f x ∈ scale S := by
  obtain ⟨p, hp, rfl⟩ := mem_scale_iff.1 hx
  rw [map_of_mk]
  exact of_mk_mem_scale _

/-- A unital star ring homomorphism maps the order unit `[1]` to `[1]`. -/
theorem map_orderUnit {A B : Type*} [Semiring A] [StarRing A] [Semiring B] [StarRing B]
    (f : A →⋆ₙ+* B) (hf : f 1 = 1) : map f (orderUnit A) = orderUnit B := by
  rw [orderUnit_def, orderUnit_def, map_of_mk]
  congr 2
  exact Matrix.map_one _ (map_zero f) hf

end map

end ProjectionKZero

end TauCeti

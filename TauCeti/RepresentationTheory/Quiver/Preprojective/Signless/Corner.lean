/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.PathsInto
public import TauCeti.RepresentationTheory.Quiver.Preprojective.Signless.Grading
public import TauCeti.RepresentationTheory.Quiver.Preprojective.Signless.KoszulComplex

/-!
# Graded corners of the signless preprojective algebra

For vertices `i` and `j` of a finite quiver `R` with involutive reversal, the graded corner
`e_j Π_n e_i` of the signless preprojective algebra `Π = Π^s_k(R)` is the span of the classes of
the paths of length `n` from `i` to `j`; equivalently, it is the intersection of the degree-`n`
piece with the corner of the two vertex idempotents. Over a field it is finite-dimensional.

Left multiplication by an arrow `b : j ⟶ l` maps `e_j Π_n e_i` to `e_l Π_{n+1} e_i`, and every
element of `e_l Π_{n+1} e_i` is a sum of such products. The graded form of the middle exactness of
the Koszul complex `0 → e_v Π → ⨁_{b : j ⟶ v} e_j Π → e_v Π` also holds corner by corner: if
`∑_b b z_b = 0` with `z_b ∈ e_j Π_n e_i`, then `z_b = b* y` for one `y ∈ e_v Π_{n-1} e_i`.
These are the graded inputs to the Koszul complexes of zigzag simple modules, whose generators
are dual to these corners.

## Main definitions

* `TauCeti.signlessPreprojectiveCorner`: the graded corner `e_j Π_n e_i`.

## Main results

* `TauCeti.mem_signlessPreprojectiveCorner_iff`: the graded corner is the degree-`n` part of the
  corner `e_j Π e_i`.
* `TauCeti.signlessPreprojectiveMk_ofArrow_mul_mem_signlessPreprojectiveCorner`: arrows act on
  the graded corners.
* `TauCeti.exists_eq_sum_signlessPreprojectiveMk_ofArrow_mul`: last-arrow decomposition in a
  graded corner of positive degree.
* `TauCeti.exists_mem_signlessPreprojectiveCorner_of_sum_ofArrow_mul_eq_zero`: graded middle
  exactness of the Koszul complex.

## References

* P. Etingof and C.-H. Eu, *Koszulity and the Hilbert series of preprojective algebras*, Math.
  Res. Lett. 14 (2007), Sections 2 and 3, for the graded corners of the vertex Koszul complex.
-/

public section

namespace TauCeti

open _root_.Quiver PathAlgebra

universe u v w

variable (k : Type w) (R : Type u) [CommRing k] [Quiver.{v} R] [HasReverse R] [Finite R]
  [∀ x : R, Fintype (Quiver.Star x)]

local notation "Π" => signlessPreprojectiveAlgebra k R
local notation "σ" => signlessPreprojectiveMk k R

/-- **The graded corner `e_j Π_n e_i`** of the signless preprojective algebra: the span of the
classes of the paths of length `n` from `i` to `j`. -/
noncomputable def signlessPreprojectiveCorner (n : ℕ) (i j : R) : Submodule k Π :=
  (pathsBetween k n i j).map (σ).toLinearMap

variable {k R}

/-- The class of a vertex idempotent is idempotent. -/
private theorem signlessPreprojectiveMk_vertexIdempotent_mul_self (i : R) :
    σ (vertexIdempotent k i) * σ (vertexIdempotent k i) = σ (vertexIdempotent k i) := by
  rw [← map_mul, vertexIdempotent_mul_self]

/-- **The graded corner `e_j Π_n e_i` is the degree-`n` part of the corner `e_j Π e_i`.** -/
theorem mem_signlessPreprojectiveCorner_iff {n : ℕ} {i j : R} {x : Π} :
    x ∈ signlessPreprojectiveCorner k R n i j ↔ x ∈ signlessPreprojectiveGrade k R n ∧
      σ (vertexIdempotent k j) * x * σ (vertexIdempotent k i) = x := by
  simp only [signlessPreprojectiveCorner, Submodule.mem_map, AlgHom.toLinearMap_apply]
  constructor
  · rintro ⟨p, hp, rfl⟩
    rw [mem_pathsBetween_iff] at hp
    exact ⟨signlessPreprojectiveMk_mem_grade k R hp.1, by rw [← map_mul, ← map_mul, hp.2]⟩
  · rintro ⟨hx, hc⟩
    obtain ⟨y, hy, rfl⟩ := (mem_signlessPreprojectiveGrade_iff k R).1 hx
    refine ⟨vertexIdempotent k j * y * vertexIdempotent k i, mem_pathsBetween_iff.2 ⟨?_, ?_⟩,
      by rw [map_mul, map_mul, hc]⟩
    · simpa using SetLike.mul_mem_graded (SetLike.mul_mem_graded
        (vertexIdempotent_mem_grade_zero (k := k) j) hy)
        (vertexIdempotent_mem_grade_zero (k := k) i)
    · rw [← mul_assoc, ← mul_assoc, vertexIdempotent_mul_self, mul_assoc _ _ (vertexIdempotent k i),
        vertexIdempotent_mul_self]

/-- An element of `e_j Π_n e_i` is fixed by left multiplication by `e_j`. -/
theorem signlessPreprojectiveMk_vertexIdempotent_mul_of_mem_signlessPreprojectiveCorner {n : ℕ}
    {i j : R} {x : Π} (hx : x ∈ signlessPreprojectiveCorner k R n i j) :
    σ (vertexIdempotent k j) * x = x := by
  obtain ⟨-, hc⟩ := mem_signlessPreprojectiveCorner_iff.1 hx
  rw [← hc, ← mul_assoc, ← mul_assoc, signlessPreprojectiveMk_vertexIdempotent_mul_self]

/-- An element of `e_j Π_n e_i` is fixed by right multiplication by `e_i`. -/
theorem mul_signlessPreprojectiveMk_vertexIdempotent_of_mem_signlessPreprojectiveCorner {n : ℕ}
    {i j : R} {x : Π} (hx : x ∈ signlessPreprojectiveCorner k R n i j) :
    x * σ (vertexIdempotent k i) = x := by
  obtain ⟨-, hc⟩ := mem_signlessPreprojectiveCorner_iff.1 hx
  rw [← hc, mul_assoc, signlessPreprojectiveMk_vertexIdempotent_mul_self]

/-- Left multiplication by an arrow `b : j ⟶ l` maps `e_j Π_n e_i` into `e_l Π_{n+1} e_i`. -/
theorem signlessPreprojectiveMk_ofArrow_mul_mem_signlessPreprojectiveCorner {n : ℕ}
    {i j l : R} (b : j ⟶ l) {x : Π} (hx : x ∈ signlessPreprojectiveCorner k R n i j) :
    σ (ofArrow b) * x ∈ signlessPreprojectiveCorner k R (n + 1) i l := by
  obtain ⟨hxn, -⟩ := mem_signlessPreprojectiveCorner_iff.1 hx
  refine mem_signlessPreprojectiveCorner_iff.2 ⟨?_, ?_⟩
  · rw [add_comm]
    exact mul_mem_signlessPreprojectiveGrade k R
      (signlessPreprojectiveMk_mem_grade k R (ofArrow_mem_grade_one b)) hxn
  · rw [mul_assoc, mul_assoc (σ (ofArrow b)),
      mul_signlessPreprojectiveMk_vertexIdempotent_of_mem_signlessPreprojectiveCorner hx,
      ← mul_assoc, ← map_mul, ofArrow_eq_ofPath, vertexIdempotent_mul_ofPath]

section Fintype

variable [Fintype R] [∀ i j : R, Fintype (i ⟶ j)]

/-- **Last-arrow decomposition in a graded corner.** Every element of `e_v Π_{n+1} e_i` is a sum
`∑_{b : j ⟶ v} b z_b` with `z_b ∈ e_j Π_n e_i`. -/
theorem exists_eq_sum_signlessPreprojectiveMk_ofArrow_mul {n : ℕ} {i v : R} {x : Π}
    (hx : x ∈ signlessPreprojectiveCorner k R (n + 1) i v) :
    ∃ z : (j : R) → (j ⟶ v) → Π, (∀ j b, z j b ∈ signlessPreprojectiveCorner k R n i j) ∧
      x = ∑ j, ∑ b : j ⟶ v, σ (ofArrow b) * z j b := by
  obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.1 hx
  obtain ⟨hpn, hpc⟩ := mem_pathsBetween_iff.1 hp
  have hpv : vertexIdempotent k v * p = p := by
    rw [← hpc, ← mul_assoc, ← mul_assoc, vertexIdempotent_mul_self]
  obtain ⟨z, hz, hpz⟩ := exists_eq_sum_ofArrow_mul (mem_pathsInto_iff.2 ⟨hpn, hpv⟩)
  refine ⟨fun j b => σ (z j b * vertexIdempotent k i), fun j b => ?_, ?_⟩
  · obtain ⟨hzn, hzj⟩ := mem_pathsInto_iff.1 (hz j b)
    refine Submodule.mem_map_of_mem (mem_pathsBetween_iff.2 ⟨?_, ?_⟩)
    · simpa using SetLike.mul_mem_graded hzn (vertexIdempotent_mem_grade_zero (k := k) i)
    · rw [← mul_assoc, hzj, mul_assoc, vertexIdempotent_mul_self]
  · have hpi : p * vertexIdempotent k i = p := by
      rw [← hpc, mul_assoc, vertexIdempotent_mul_self]
    rw [AlgHom.toLinearMap_apply, ← hpi, hpz, Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_mul, map_sum]
    exact Finset.sum_congr rfl fun b _ => by rw [mul_assoc, map_mul]

end Fintype

section Middle

variable {R : Type u} [Quiver.{v} R] [HasInvolutiveReverse R] [Fintype R]
  [∀ x : R, Fintype (Quiver.Star x)] [∀ i j : R, Fintype (i ⟶ j)]

attribute [local instance] signlessPreprojectiveGradedAlgebra

/-- **Graded middle exactness of the Koszul complex.** Let `z_b ∈ e_j Π_n e_i` for the arrows
`b : j ⟶ v`. If `∑_b b z_b = 0`, then there is `y ∈ e_v Π_{n-1} e_i` with `z_b = b* y` for
every `b`; for `n = 0` every `z_b` vanishes and `y = 0`. -/
theorem exists_mem_signlessPreprojectiveCorner_of_sum_ofArrow_mul_eq_zero {n : ℕ} {i v : R}
    {z : (j : R) → (j ⟶ v) → signlessPreprojectiveAlgebra k R}
    (hz : ∀ j b, z j b ∈ signlessPreprojectiveCorner k R n i j)
    (h : ∑ j, ∑ b : j ⟶ v, signlessPreprojectiveMk k R (ofArrow b) * z j b = 0) :
    ∃ y ∈ signlessPreprojectiveCorner k R (n - 1) i v,
      ∀ j b, z j b = signlessPreprojectiveMk k R (ofArrow (reverse b)) * y := by
  obtain ⟨y, hyv, hyz⟩ := (sum_signlessPreprojectiveMk_ofArrow_mul_eq_zero_iff k v fun j b =>
    signlessPreprojectiveMk_vertexIdempotent_mul_of_mem_signlessPreprojectiveCorner (hz j b)).1 h
  -- Each `z_b` is homogeneous of degree `n`, and `b*` raises degree by one.
  have hdeg (j : R) (b : j ⟶ v) :
      z j b = DirectSum.decompose (signlessPreprojectiveGrade k R)
        (signlessPreprojectiveMk k R (ofArrow (reverse b)) * y) n := by
    rw [← hyz j b, DirectSum.decompose_of_mem_same _
      (mem_signlessPreprojectiveCorner_iff.1 (hz j b)).1]
  have hrev (j : R) (b : j ⟶ v) := signlessPreprojectiveMk_mem_grade k R
    (ofArrow_mem_grade_one (reverse b))
  rcases n with _ | m
  · refine ⟨0, zero_mem _, fun j b => ?_⟩
    rw [hdeg, DirectSum.coe_decompose_mul_of_left_mem_of_not_le _ (hrev j b) (by omega),
      mul_zero]
  · have h0 (u : R) : signlessPreprojectiveMk k R (vertexIdempotent k u) ∈
        signlessPreprojectiveGrade k R 0 :=
      signlessPreprojectiveMk_mem_grade k R (vertexIdempotent_mem_grade_zero u)
    refine ⟨(DirectSum.decompose (signlessPreprojectiveGrade k R) y m :
        signlessPreprojectiveAlgebra k R) * signlessPreprojectiveMk k R (vertexIdempotent k i),
      mem_signlessPreprojectiveCorner_iff.2 ⟨?_, ?_⟩, fun j b => ?_⟩
    · simpa using mul_mem_signlessPreprojectiveGrade k R (Submodule.coe_mem _) (h0 i)
    · have hv : signlessPreprojectiveMk k R (vertexIdempotent k v) *
          (DirectSum.decompose (signlessPreprojectiveGrade k R) y m :
            signlessPreprojectiveAlgebra k R) =
            DirectSum.decompose (signlessPreprojectiveGrade k R) y m := by
        conv_rhs => rw [← hyv]
        rw [DirectSum.coe_decompose_mul_of_left_mem_of_le _ (h0 v) (Nat.zero_le m), Nat.sub_zero]
      rw [← mul_assoc, hv, mul_assoc, signlessPreprojectiveMk_vertexIdempotent_mul_self]
    · have hshift : signlessPreprojectiveMk k R (ofArrow (reverse b)) *
          (DirectSum.decompose (signlessPreprojectiveGrade k R) y m :
            signlessPreprojectiveAlgebra k R) =
            DirectSum.decompose (signlessPreprojectiveGrade k R)
              (signlessPreprojectiveMk k R (ofArrow (reverse b)) * y) (m + 1) := by
        rw [DirectSum.coe_decompose_mul_of_left_mem_of_le _ (hrev j b) (by omega),
          Nat.add_sub_cancel]
      rw [← mul_assoc, hshift, ← hdeg,
        mul_signlessPreprojectiveMk_vertexIdempotent_of_mem_signlessPreprojectiveCorner (hz j b)]

end Middle

section Field

variable (k : Type w) {R : Type u} [Field k] [Quiver.{v} R] [HasReverse R] [Finite R]
  [∀ x : R, Fintype (Quiver.Star x)] [∀ i j : R, Finite (i ⟶ j)]

/-- The graded corners of the signless preprojective algebra of a finite quiver are
finite-dimensional: there are finitely many paths of each length between two vertices. -/
instance (n : ℕ) (i j : R) : FiniteDimensional k (signlessPreprojectiveCorner k R n i j) :=
  Module.Finite.map _ _

end Field

end TauCeti

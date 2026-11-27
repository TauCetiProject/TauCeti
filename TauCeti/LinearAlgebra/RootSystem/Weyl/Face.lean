/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Weyl.ParabolicQuotient

/-!
# The faces of the closed dominant chamber

Let `b` be a base of a root pairing over a linearly ordered ring. The closed dominant chamber
`C = {x | ⟨x, αᵢ^∨⟩ ≥ 0 for every simple root αᵢ}` (`RootPairing.dominantChamber`) is cut into
its **open faces** by the set of simple walls through a point: two dominant weights `x` and `y`
lie in the same open face when `RootPairing.wallIndices b x = RootPairing.wallIndices b y`, that
is, when the same simple coroots vanish on them. This file shows that this face decides both
which roots vanish at a dominant weight and its stabilizer in the Weyl group.

* **Which roots vanish on a face.** For dominant `x`, a coroot `β^∨` vanishes on `x` exactly when
  it lies in the span of the simple coroots of the walls through `x`
  (`TauCeti.coroot'_eq_zero_iff_coroot_mem_span_wallIndices`). Indeed `±β^∨` is a nonnegative
  integer combination of simple coroots, each nonnegative on `x`, so the pairing vanishes only
  when every simple coroot that occurs vanishes on `x`. Consequently the vanishing pattern of all
  the roots at `x` is read off from its face: every root vanishing on `x` vanishes on `y` exactly
  when every wall through `x` passes through `y`
  (`TauCeti.wallIndices_subset_wallIndices_iff`). Here `y` need not be dominant.
* **Stabilizers.** A reflection `s_β` fixes a weight exactly when `β^∨` vanishes on it
  (`TauCeti.ofIdx_smul_eq_self_iff`), so the walls through any `x` pass through every weight fixed
  by the stabilizer of `x` (`TauCeti.wallIndices_subset_of_stabilizer_le`). The Weyl stabilizer of
  a dominant `x` is the standard parabolic subgroup of the walls through `x`
  (`RootPairing.parabolic_wallIndices_eq_stabilizer`), so stabilizers are ordered like faces: for
  dominant `x` and any `y`,

  `W_x ≤ W_y ↔ wallIndices x ⊆ wallIndices y ↔ (∀ β, ⟨x, β^∨⟩ = 0 → ⟨y, β^∨⟩ = 0)`

  (`TauCeti.stabilizer_le_stabilizer_iff`,
  `TauCeti.stabilizer_le_stabilizer_iff_forall_coroot'_eq_zero`), and two dominant weights have
  the same stabilizer exactly when they lie in the same open face
  (`TauCeti.stabilizer_eq_stabilizer_iff`).
* **Every face occurs.** Over a field, every set of simple roots is the set of walls through some
  dominant weight (`TauCeti.exists_mem_dominantChamber_wallIndices_eq`), so the open faces are
  indexed by the subsets of the simple roots, and the stabilizers of dominant weights are exactly
  the standard parabolic subgroups (`TauCeti.image_stabilizer_dominantChamber`).

Since every Weyl orbit meets the closed dominant chamber in exactly one point
(`TauCeti.existsUnique_mem_orbit_inter_dominantChamber`), the stabilizer of an arbitrary weight
is conjugate to the stabilizer of the face containing its dominant representative. Conjugate
stabilizers can come from different faces: in type `A₂` the two walls of the chamber have
conjugate stabilizers, as the two simple reflections are conjugate. So the faces classify the
stabilizers themselves, while the stabilizer types, their conjugacy classes, are a coarser
invariant.

These are the Weyl-group counterparts of the comparison of adjoint stabilizers of a compact Lie
group by vanishing roots in `TauCeti.Geometry.Lie.Subgroup.Torus.OrbitType`.

## Main results

* `TauCeti.wallIndices_subset_of_stabilizer_le`: the walls through `x` pass through every weight
  fixed by the stabilizer of `x`.
* `TauCeti.coroot'_eq_zero_iff_coroot_mem_span_wallIndices`: on a dominant weight, the coroots
  that vanish are those in the span of the simple coroots of its walls.
* `TauCeti.wallIndices_subset_wallIndices_iff`: the walls through a dominant weight determine
  the roots vanishing there.
* `TauCeti.stabilizer_le_stabilizer_iff`, `TauCeti.stabilizer_eq_stabilizer_iff`: Weyl
  stabilizers of dominant weights are compared by their faces.
* `TauCeti.exists_mem_dominantChamber_wallIndices_eq`,
  `TauCeti.image_stabilizer_dominantChamber`: every face is nonempty, and the stabilizers of
  dominant weights are the standard parabolic subgroups.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Chapter V, §1 and §3 (facets of a
  chamber and their stabilizers).
* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, CUP (1990), Section 1.12.
-/

public section

namespace TauCeti

open RootPairing Set Submodule

universe u v w x

variable {ι : Type u} {R : Type v} {M : Type w} {N : Type x} [AddCommGroup M] [AddCommGroup N]

section CommRing

variable [CommRing R] [Module R M] [Module R N] {P : _root_.RootPairing ι R M N} {b : P.Base}
  {x y : M}

/-! ### Walls and the coroots vanishing on a face -/

/-- If the stabilizer of `x` in the Weyl group fixes `y`, every simple wall through `x` passes
through `y`. -/
theorem wallIndices_subset_of_stabilizer_le [NeZero (2 : R)] [NoZeroDivisors R]
    (h : MulAction.stabilizer P.weylGroup x ≤ MulAction.stabilizer P.weylGroup y) :
    P.wallIndices b x ⊆ P.wallIndices b y := fun i hi ↦ by
  have hy := h (ofIdx_smul_eq_self_iff.mpr (mem_wallIndices.mp hi))
  exact mem_wallIndices.mpr (ofIdx_smul_eq_self_iff.mp hy)

/-- A coroot in the span of the simple coroots of the walls through `x` vanishes on `x`. -/
theorem coroot'_eq_zero_of_coroot_mem_span_wallIndices {i : ι}
    (h : P.coroot i ∈ span R ((fun j : b.support ↦ P.coroot j) '' P.wallIndices b x)) :
    P.coroot' i x = 0 := by
  have hle : span R ((fun j : b.support ↦ P.coroot j) '' P.wallIndices b x) ≤
      LinearMap.ker (P.toLinearMap x) := by
    rw [span_le]
    rintro _ ⟨j, hj, rfl⟩
    -- `P.coroot' j x` is by definition the pairing `P.toLinearMap x (P.coroot j)`.
    exact mem_wallIndices.mp hj
  exact hle h

/-- **The coroots vanishing on a face.** A coroot vanishes on a dominant weight `x` exactly when it
lies in the span of the simple coroots of the walls through `x`. -/
theorem coroot'_eq_zero_iff_coroot_mem_span_wallIndices [PartialOrder R] [IsOrderedAddMonoid R]
    (hx : x ∈ dominantChamber P b) (i : ι) :
    P.coroot' i x = 0 ↔
      P.coroot i ∈ span R ((fun j : b.support ↦ P.coroot j) '' P.wallIndices b x) := by
  refine ⟨fun h ↦ ?_, coroot'_eq_zero_of_coroot_mem_span_wallIndices⟩
  -- Write `±β^∨` as a nonnegative integer combination `∑ fⱼ αⱼ^∨` of the simple coroots.
  obtain ⟨f, -, hf⟩ := b.flip.exists_root_eq_sum_nat_or_neg i
  simp only [flip_root, Base.flip_support] at hf
  set s := ∑ j ∈ b.support, f j • P.coroot j
  -- `P.coroot' i x` is by definition the pairing `P.toLinearMap x (P.coroot i)`, which is
  -- linear in the coroot.
  have hs : P.toLinearMap x s = 0 := by
    rcases hf with hf | hf
    · rw [← hf]
      exact h
    · rw [← neg_neg s, ← hf, map_neg, neg_eq_zero]
      exact h
  -- Each term `fⱼ ⟨x, αⱼ^∨⟩` is nonnegative and they sum to zero, so each vanishes.
  have hx := (mem_dominantChamber P b x).mp hx
  rw [map_sum] at hs
  simp only [map_nsmul] at hs
  have hterm : ∀ j ∈ b.support, f j • P.coroot' j x = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun j hj ↦ nsmul_nonneg (hx j hj) _).mp hs
  have hmem : s ∈ span R ((fun j : b.support ↦ P.coroot j) '' P.wallIndices b x) := by
    refine sum_mem fun j hj ↦ ?_
    rcases Nat.eq_zero_or_pos (f j) with hj0 | hj0
    · rw [hj0, zero_smul]
      exact zero_mem _
    -- A simple coroot occurring in the sum vanishes on `x`: `⟨x, αⱼ^∨⟩ ≤ fⱼ ⟨x, αⱼ^∨⟩ = 0`.
    have hzero : P.coroot' j x = 0 := by
      refine le_antisymm ?_ (hx j hj)
      calc P.coroot' j x = 1 • P.coroot' j x := (one_nsmul _).symm
        _ ≤ f j • P.coroot' j x := nsmul_le_nsmul_left (hx j hj) hj0
        _ = 0 := hterm j hj
    have hj' : (⟨j, hj⟩ : b.support) ∈ P.wallIndices b x := mem_wallIndices.mpr hzero
    exact nsmul_mem (subset_span (mem_image_of_mem (fun j : b.support ↦ P.coroot j) hj')) _
  rcases hf with hf | hf
  · exact hf ▸ hmem
  · exact hf ▸ neg_mem hmem

/-- **The walls through a dominant weight determine the roots vanishing there.** For dominant `x`
and any weight `y`, every coroot vanishing on `x` vanishes on `y` exactly when every simple wall
through `x` passes through `y`. -/
theorem wallIndices_subset_wallIndices_iff [PartialOrder R] [IsOrderedAddMonoid R]
    (hx : x ∈ dominantChamber P b) :
    P.wallIndices b x ⊆ P.wallIndices b y ↔ ∀ i, P.coroot' i x = 0 → P.coroot' i y = 0 := by
  refine ⟨fun h i hi ↦ ?_, fun h j hj ↦ mem_wallIndices.mpr (h j (mem_wallIndices.mp hj))⟩
  refine coroot'_eq_zero_of_coroot_mem_span_wallIndices (b := b) ?_
  exact span_mono (image_mono h) ((coroot'_eq_zero_iff_coroot_mem_span_wallIndices hx i).mp hi)

/-! ### Stabilizers of faces -/

section Ordered

variable [LinearOrder R] [IsStrictOrderedRing R] [Finite ι] [P.IsCrystallographic]
  [P.IsReduced] [P.flip.IsReduced]

/-- **Weyl stabilizers are ordered like faces.** For a dominant weight `x` and any weight `y`, the
stabilizer of `x` fixes `y` exactly when every simple wall through `x` passes through `y`. -/
theorem stabilizer_le_stabilizer_iff (hx : x ∈ dominantChamber P b) :
    MulAction.stabilizer P.weylGroup x ≤ MulAction.stabilizer P.weylGroup y ↔
      P.wallIndices b x ⊆ P.wallIndices b y := by
  refine ⟨wallIndices_subset_of_stabilizer_le, fun h ↦ ?_⟩
  rw [← P.parabolic_wallIndices_eq_stabilizer b hx]
  exact ((weylCoxeterSystem P b).parabolic_mono h).trans
    (P.parabolic_wallIndices_le_stabilizer b y)

/-- For a dominant weight `x` and any weight `y`, the stabilizer of `x` in the Weyl group fixes `y`
exactly when every root vanishing on `x` vanishes on `y`. -/
theorem stabilizer_le_stabilizer_iff_forall_coroot'_eq_zero (hx : x ∈ dominantChamber P b) :
    MulAction.stabilizer P.weylGroup x ≤ MulAction.stabilizer P.weylGroup y ↔
      ∀ i, P.coroot' i x = 0 → P.coroot' i y = 0 := by
  rw [stabilizer_le_stabilizer_iff hx, wallIndices_subset_wallIndices_iff hx]

/-- **Two dominant weights have the same Weyl stabilizer exactly when they lie in the same open
face** of the closed dominant chamber, that is, on the same simple walls. -/
theorem stabilizer_eq_stabilizer_iff (hx : x ∈ dominantChamber P b)
    (hy : y ∈ dominantChamber P b) :
    MulAction.stabilizer P.weylGroup x = MulAction.stabilizer P.weylGroup y ↔
      P.wallIndices b x = P.wallIndices b y := by
  rw [le_antisymm_iff, stabilizer_le_stabilizer_iff hx, stabilizer_le_stabilizer_iff hy,
    Set.Subset.antisymm_iff]

end Ordered

end CommRing

/-! ### Every face occurs -/

section Field

variable [Field R] [LinearOrder R] [IsStrictOrderedRing R] [Module R M] [Module R N]
  {P : _root_.RootPairing ι R M N} (b : P.Base)

/-- **Every open face of the closed dominant chamber is nonempty**: every set of simple roots is
the set of walls through some dominant weight. -/
theorem exists_mem_dominantChamber_wallIndices_eq (S : Set b.support) :
    ∃ x ∈ dominantChamber P b, P.wallIndices b x = S := by
  classical
  -- Prescribe the value `0` on the simple coroots of `S` and `1` on the others.
  obtain ⟨x, hx⟩ := b.flip.exists_forall_root'_eq
    fun j ↦ if h : j ∈ b.support then (if (⟨j, h⟩ : b.support) ∈ S then 0 else 1) else 0
  have hx' : ∀ j : b.support, P.coroot' j x = if j ∈ S then 0 else 1 := fun j ↦ by
    have h := hx j (by simp)
    simp only [j.property, ↓reduceDIte] at h
    -- The root functionals of the flipped pairing are by definition the coroot functionals.
    exact h
  refine ⟨x, (mem_dominantChamber P b x).mpr fun j hj ↦ ?_, Set.ext fun j ↦ ?_⟩
  · rw [hx' ⟨j, hj⟩]
    split_ifs <;> simp
  · rw [mem_wallIndices, hx' j]
    split_ifs with hj <;> simp [hj]

variable [Finite ι] [P.IsCrystallographic] [P.IsReduced] [P.flip.IsReduced]

/-- **The stabilizers of dominant weights are the standard parabolic subgroups**, the one of a
dominant weight being generated by the reflections in the walls through it. -/
theorem image_stabilizer_dominantChamber :
    (MulAction.stabilizer P.weylGroup) '' dominantChamber P b =
      range (weylCoxeterSystem P b).parabolic := by
  ext H
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨P.wallIndices b x, P.parabolic_wallIndices_eq_stabilizer b hx⟩
  · rintro ⟨S, rfl⟩
    obtain ⟨x, hx, hS⟩ := exists_mem_dominantChamber_wallIndices_eq b S
    exact ⟨x, hx, hS ▸ (P.parabolic_wallIndices_eq_stabilizer b hx).symm⟩

end Field

end TauCeti

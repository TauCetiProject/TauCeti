/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Basic
public import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Generating tuples in finite quotients of an absolute Galois group

For a field `K`, a tuple in the absolute Galois group generates a finite quotient when its image
generates that quotient. This file records the topology of these conditions: for every finite
tuple length, the set of tuples generating a fixed finite quotient is closed, and generation
descends along quotient maps. These facts let compactness produce a tuple that works in every
finite quotient when each quotient has a generating tuple of that length.

The length can be specialized to the arithmetic bound `[K : ℚ_[p]] + 2` for finite extensions of
`ℚ_[p]`.
-/

public section

namespace TauCeti

variable (K : Type*) [Field K]

/-- The tuples of length `n` whose images generate the finite quotient of `G_K` by an open normal
subgroup. Repetitions are allowed, so a tuple may have greater length than a minimal generating
set. -/
def generatingTuples (n : ℕ) (U : OpenNormalSubgroup (Field.absoluteGaloisGroup K)) :
    Set (Fin n → Field.absoluteGaloisGroup K) :=
  {x | Subgroup.closure (Set.range fun i ↦
    (QuotientGroup.mk (x i) : Field.absoluteGaloisGroup K ⧸ U.toSubgroup)) = ⊤}

/-- Membership in `generatingTuples` means that the images of the tuple generate the quotient. -/
@[simp]
theorem mem_generatingTuples (n : ℕ) (U : OpenNormalSubgroup (Field.absoluteGaloisGroup K))
    (x : Fin n → Field.absoluteGaloisGroup K) :
    x ∈ generatingTuples K n U ↔
      Subgroup.closure (Set.range fun i ↦
        (QuotientGroup.mk (x i) : Field.absoluteGaloisGroup K ⧸ U.toSubgroup)) = ⊤ :=
  Iff.rfl

/-- The tuples generating a fixed finite quotient form a closed set: the condition depends only
on their image in a finite Hausdorff quotient. -/
theorem isClosed_generatingTuples (n : ℕ) (U : OpenNormalSubgroup (Field.absoluteGaloisGroup K)) :
    IsClosed (generatingTuples K n U) := by
  have : Finite (Field.absoluteGaloisGroup K ⧸ U.toSubgroup) :=
    U.toSubgroup.quotient_finite_of_isOpen U.isOpen
  let q : (Fin n → Field.absoluteGaloisGroup K) →
      (Fin n → Field.absoluteGaloisGroup K ⧸ U.toSubgroup) :=
    fun x i ↦ QuotientGroup.mk (x i)
  have hq : Continuous q := by
    apply continuous_pi
    intro i
    exact continuous_quotient_mk'.comp (continuous_apply i)
  let S : Set (Fin n → Field.absoluteGaloisGroup K ⧸ U.toSubgroup) :=
    {y | Subgroup.closure (Set.range y) = ⊤}
  have hS : IsClosed S := (Set.toFinite S).isClosed
  have hEq : generatingTuples K n U = q ⁻¹' S := by
    ext x
    rfl
  rw [hEq]
  exact hS.preimage hq

/-- If `U' ≤ U`, every tuple generating the finer quotient by `U'` also generates the quotient
by `U`. -/
theorem generatingTuples_antitone (n : ℕ) {U U' : OpenNormalSubgroup (Field.absoluteGaloisGroup K)}
    (h : U' ≤ U) : generatingTuples K n U' ⊆ generatingTuples K n U := by
  intro x hx
  rw [mem_generatingTuples] at hx ⊢
  let f : Field.absoluteGaloisGroup K ⧸ U'.toSubgroup →*
      Field.absoluteGaloisGroup K ⧸ U.toSubgroup :=
    QuotientGroup.map U'.toSubgroup U.toSubgroup (MonoidHom.id _) (by
      have hsub : U'.toSubgroup ≤ U.toSubgroup := h
      simpa using hsub)
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective U.toSubgroup y
    exact ⟨QuotientGroup.mk' U'.toSubgroup g, by rfl⟩
  have hmap : Subgroup.map f (Subgroup.closure (Set.range fun i ↦
      (QuotientGroup.mk (x i) : Field.absoluteGaloisGroup K ⧸ U'.toSubgroup))) = ⊤ := by
    rw [hx, Subgroup.map_top]
    exact MonoidHom.range_eq_top.2 hf
  have hle : Subgroup.map f (Subgroup.closure (Set.range fun i ↦
      (QuotientGroup.mk (x i) : Field.absoluteGaloisGroup K ⧸ U'.toSubgroup))) ≤
      Subgroup.closure (Set.range fun i ↦
        (QuotientGroup.mk (x i) : Field.absoluteGaloisGroup K ⧸ U.toSubgroup)) := by
    rw [MonoidHom.map_closure]
    apply Subgroup.closure_mono
    rintro y ⟨z, ⟨i, rfl⟩, rfl⟩
    refine ⟨i, ?_⟩
    -- The source and target quotient types differ, so expose the induced quotient map explicitly.
    change (QuotientGroup.mk (x i) : Field.absoluteGaloisGroup K ⧸ U.toSubgroup) =
      QuotientGroup.map U'.toSubgroup U.toSubgroup (MonoidHom.id _)
        (by
          have hsub : U'.toSubgroup ≤ U.toSubgroup := h
          simpa using hsub)
        (QuotientGroup.mk (x i))
    simp only [QuotientGroup.map_mk, MonoidHom.id_apply]
  have htop : (⊤ : Subgroup (Field.absoluteGaloisGroup K ⧸ U.toSubgroup)) ≤
      Subgroup.closure (Set.range fun i ↦
        (QuotientGroup.mk (x i) : Field.absoluteGaloisGroup K ⧸ U.toSubgroup)) := by
    rw [← hmap]
    exact hle
  exact top_le_iff.mp htop

end TauCeti

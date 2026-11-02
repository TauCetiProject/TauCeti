/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.LSPath.Highest
public import TauCeti.RepresentationTheory.LSPath.Height

/-!
# Highest concatenations and translated chambers

For dominant shapes `λ` and `μ`, a concatenation of LS paths of these shapes is annihilated
by every simple raising operator exactly when its first factor is the straight path of
shape `λ` and its second factor stays in the dominant chamber after translation by `λ`.
The chamber test uses the actual parametrized second path at every time in `[0, 1]`.

This identifies the highest indices used in the path tensor-product rule without assuming
operator stability of LS encodings or a representation-theoretic decomposition theorem.
It includes zero shapes, chamber walls, central weights and empty root systems.

## References

* P. Littelmann, *A Littlewood–Richardson rule for symmetrizable Kac–Moody algebras*,
  Invent. Math. 116 (1994), §4 (dominant concatenations).
* P. Littelmann, *Paths and root operators in representation theory*, Ann. of Math.
  142 (1995), §2 (concatenation).
-/

public section

namespace TauCeti.LSPath

open RootPairing

variable {ι M N : Type*} [AddCommGroup M] [AddCommGroup N]
  {P : RootPairing ι ℤ M N} {b : P.Base} [Finite ι] [P.IsReduced] [P.flip.IsReduced]
  {lam mu : M} {𝕜 V : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup V] [Module 𝕜 V]

/-- Highest concatenations of two dominant-shape LS paths: the left factor is straight,
and each simple-coroot minimum of the right factor is at least minus the left shape's
pairing. Equality is allowed, as required on chamber walls. -/
theorem forall_raise_mul_eq_none_iff
    (π : LSPath P b lam) (ρ : LSPath P b mu)
    (hlam : lam ∈ dominantChamber P b) (hmu : mu ∈ dominantChamber P b)
    (f : M →+ V) (F : b.support → Module.Dual 𝕜 V)
    (hF : ∀ i m, F i (f m) = (P.coroot' i m : 𝕜)) :
    (∀ i, PLPath.raise (F i) (f (P.root i))
      (π.toPLPath 𝕜 f * ρ.toPLPath 𝕜 f) = none) ↔
      π = straight lam ∧ ∀ i : b.support, -(P.coroot' i lam : 𝕜) ≤
        (ρ.toPLPath 𝕜 f).minHeight (F i) := by
  have first : (∀ i, PLPath.raise (F i) (f (P.root i))
      (π.toPLPath 𝕜 f * ρ.toPLPath 𝕜 f) = none) → π = straight lam := by
    intro h
    apply (π.forall_raise_eq_none_iff hlam f F hF).mp
    intro i
    apply PLPath.raise_eq_none_iff.mpr
    exact (PLPath.raise_eq_none_iff.mp (h i)).trans_le (by
      rw [PLPath.minHeight_mul]
      exact min_le_left _ _)
  constructor
  · intro h
    have hπ := first h
    refine ⟨hπ, fun i ↦ ?_⟩
    obtain ⟨z, hz⟩ := ρ.exists_minHeight_eq_intCast hmu f i (F i) (hF i)
    have hi := PLPath.raise_eq_none_iff.mp (h i)
    rw [hπ, toPLPath_straight, PLPath.minHeight_mul, PLPath.endpoint_straight, hF i,
      hz] at hi
    have hzi : (-1 : ℤ) < P.coroot' i lam + z := by
      exact_mod_cast hi.trans_le (min_le_right _ _)
    have hzi_nonneg : (0 : ℤ) ≤ P.coroot' i lam + z := by omega
    have hn : (0 : 𝕜) ≤ (P.coroot' i lam : 𝕜) + (z : 𝕜) := by
      exact_mod_cast hzi_nonneg
    rw [hz]
    linarith
  · rintro ⟨rfl, h⟩ i
    apply PLPath.raise_eq_none_iff.mpr
    rw [toPLPath_straight, PLPath.minHeight_mul, PLPath.minHeight_straight,
      PLPath.endpoint_straight, hF i]
    have hd : (0 : 𝕜) ≤ (P.coroot' i lam : 𝕜) := by
      exact_mod_cast (mem_dominantChamber P b lam).mp hlam i i.2
    have hi := h i
    rw [min_eq_left hd, min_eq_left (by linarith)]
    norm_num

/-- The translated-chamber criterion for highest LS concatenations, stated on the actual
parametrized path. The time endpoints are included. -/
theorem forall_raise_mul_eq_none_iff_forall_evalTimed
    (π : LSPath P b lam) (ρ : LSPath P b mu)
    (hlam : lam ∈ dominantChamber P b) (hmu : mu ∈ dominantChamber P b)
    (f : M →+ V) (F : b.support → Module.Dual 𝕜 V)
    (hF : ∀ i m, F i (f m) = (P.coroot' i m : 𝕜)) :
    (∀ i, PLPath.raise (F i) (f (P.root i))
      (π.toPLPath 𝕜 f * ρ.toPLPath 𝕜 f) = none) ↔
      π = straight lam ∧ ∀ t ∈ Set.Icc (0 : 𝕜) 1, ∀ i,
        0 ≤ F i (f lam + PLPath.evalTimed (ρ.timed 𝕜 f) t) := by
  rw [π.forall_raise_mul_eq_none_iff ρ hlam hmu f F hF]
  refine and_congr Iff.rfl ?_
  simp only [toPLPath_def, PLPath.le_minHeight_ofSegments_iff (ρ.isTimed_timed 𝕜 f),
    duration_timed, map_add, hF, neg_le_iff_add_nonneg]
  constructor
  · intro h t ht i
    simpa only [add_comm] using h i t ht
  · intro h i t ht
    simpa only [add_comm] using h t ht i

end TauCeti.LSPath

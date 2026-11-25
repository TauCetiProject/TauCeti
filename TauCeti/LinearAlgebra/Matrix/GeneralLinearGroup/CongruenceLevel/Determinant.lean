/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `TauCeti.GL2K0` and `TauCeti.GL2K1` occur in the statements below.
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.CongruenceLevel
-- `TauCeti.diagGL` occurs in the statements below.
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Basic
-- Non-public: the entrywise description of the reduction kernel, used only in the proofs.
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Map

/-!
# Determinants of the congruence levels of `GL₂`

For a commutative ring `A` and an ideal `I`, the diagonal matrix `diag(u, 1)` of a unit `u` lies
in `K₁(I) ⊆ K₀(I)` and has determinant `u`, so the determinants of `K₀(I)` and `K₁(I)` fill `Aˣ`.
For any nonempty finite index type `n`, the determinants of the principal level
`ker(GL_n(A) → GL_n(A ⧸ I))` are the units congruent to `1` modulo `I`: `≤` because the
determinant commutes with reduction, `≥` by a diagonal matrix with a single entry `u`.

## Main results

* `TauCeti.GL2K1.diagGL_mem`, `TauCeti.GL2K0.diagGL_mem`: `diag(u, 1) ∈ K₁(I) ⊆ K₀(I)`.
* `TauCeti.GL2K1.map_det`, `TauCeti.GL2K0.map_det`: the determinants of `K₁(I)` and `K₀(I)` are
  all of `Aˣ`.
* `TauCeti.map_det_ker_map_quotientMk`: the determinants of the principal level are the units
  congruent to `1` modulo `I`.

## References

* J. S. Milne, *Introduction to Shimura varieties*, revision of 16 September 2017, Lemma 5.13,
  p. 57.
-/

public section

open Matrix

namespace TauCeti

variable {A : Type*} [CommRing A] (I : Ideal A)

/-- The matrix `diag(u, 1)` lies in `K₁(I)`. -/
theorem GL2K1.diagGL_mem (u : Aˣ) : diagGL ![u, 1] ∈ GL2K1 I := by
  rw [GL2K1.mem_iff]
  simp

/-- The matrix `diag(u, 1)` lies in `K₀(I)`. -/
theorem GL2K0.diagGL_mem (u : Aˣ) : diagGL ![u, 1] ∈ GL2K0 I :=
  GL2K1.le_GL2K0 I (GL2K1.diagGL_mem I u)

/-- **The determinants of `K₁(I)` are all of `Aˣ`.** -/
theorem GL2K1.map_det : (GL2K1 I).map GeneralLinearGroup.det = ⊤ :=
  eq_top_iff.mpr fun u _ ↦ ⟨_, GL2K1.diagGL_mem I u, det_diagGL_unit_one u⟩

/-- **The determinants of `K₀(I)` are all of `Aˣ`.** -/
theorem GL2K0.map_det : (GL2K0 I).map GeneralLinearGroup.det = ⊤ :=
  eq_top_iff.mpr ((GL2K1.map_det I).ge.trans (Subgroup.map_mono (GL2K1.le_GL2K0 I)))

/-- **The determinants of the principal level are the units congruent to `1`**: for a nonempty
finite index type `n`, the image under `det` of `ker(GL_n(A) → GL_n(A ⧸ I))` is
`ker(Aˣ → (A ⧸ I)ˣ)`. -/
theorem map_det_ker_map_quotientMk {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n] :
    (GeneralLinearGroup.map (n := n) (Ideal.Quotient.mk I)).ker.map GeneralLinearGroup.det =
      (Units.map (Ideal.Quotient.mk I : A →* A ⧸ I)).ker := by
  refine le_antisymm ?_ fun u hu ↦ ?_
  · rintro _ ⟨g, hg, rfl⟩
    rw [MonoidHom.mem_ker, ← GeneralLinearGroup.map_det, MonoidHom.mem_ker.mp hg, map_one]
  · let i : n := Classical.arbitrary n
    refine ⟨diagGL (Pi.mulSingle i u), ?_, by rw [det_diagGL, Fintype.prod_pi_mulSingle' i]⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, map_diagGL, ← map_one diagGL]
    congr 1
    funext j
    rcases eq_or_ne j i with rfl | hj
    · simpa using MonoidHom.mem_ker.mp hu
    · simp [hj]

end TauCeti

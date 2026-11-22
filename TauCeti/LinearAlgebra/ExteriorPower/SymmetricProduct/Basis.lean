/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.ExteriorPower.Basis
public import TauCeti.LinearAlgebra.ExteriorPower.SymmetricProduct.Basic
import Mathlib.Tactic.Ring
import TauCeti.LinearAlgebra.Matrix.Trace.Basic
import TauCeti.LinearAlgebra.Trace.Basic

/-!
# Basis matrix entries and trace of the symmetric exterior product

For bases `b` and `c` of finite free modules, `Module.Basis.toMatrix_exteriorPower_symmMap₂`
expresses the matrix entries of `exteriorPower.symmMap₂ f g` in the exterior-square bases
`b.exteriorPower 2` and `c.exteriorPower 2` as symmetrized `2 × 2` minors. Summing the diagonal
entries gives `exteriorPower.trace_symmMap₂`: for every free module `M` over a commutative ring
with `2` invertible, `tr(symmMap₂ f g) = ⅟2 * (tr f · tr g - tr(f ∘ₗ g))`, and in particular
`tr(symmMap₂ f id) = ((finrank R M - 1) * ⅟2) * tr f` (`exteriorPower.trace_symmMap₂_id_right`).

## Main results

* `Module.Basis.toMatrix_exteriorPower_symmMap₂`: matrix entries of `exteriorPower.symmMap₂ f g`
  in exterior-square bases.
* `exteriorPower.trace_symmMap₂`: trace formula `⅟2 * (tr f * tr g - tr(f ∘ₗ g))` on free
  modules.
* `exteriorPower.trace_symmMap₂_id_right`: trace specialization for `symmMap₂ f LinearMap.id`.
-/

public section

namespace Module.Basis

variable {R M N I J : Type*} [CommRing R] [Invertible (2 : R)]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [LinearOrder I] [Fintype I] [LinearOrder J] [Finite J]

/-- Matrix entries of `exteriorPower.symmMap₂ f g` with respect to exterior-square bases. -/
theorem toMatrix_exteriorPower_symmMap₂ (b : Basis I R M) (c : Basis J R N) (f g : M →ₗ[R] N)
    (s : Set.powersetCard J 2) (t : Set.powersetCard I 2) :
    LinearMap.toMatrix (b.exteriorPower 2) (c.exteriorPower 2) (exteriorPower.symmMap₂ f g) s t =
      ⅟(2 : R) *
        (LinearMap.toMatrix b c f (Set.powersetCard.ofFinEmbEquiv.symm s 0)
            (Set.powersetCard.ofFinEmbEquiv.symm t 0) *
          LinearMap.toMatrix b c g (Set.powersetCard.ofFinEmbEquiv.symm s 1)
            (Set.powersetCard.ofFinEmbEquiv.symm t 1) -
        LinearMap.toMatrix b c f (Set.powersetCard.ofFinEmbEquiv.symm s 1)
            (Set.powersetCard.ofFinEmbEquiv.symm t 0) *
          LinearMap.toMatrix b c g (Set.powersetCard.ofFinEmbEquiv.symm s 0)
            (Set.powersetCard.ofFinEmbEquiv.symm t 1) +
        LinearMap.toMatrix b c g (Set.powersetCard.ofFinEmbEquiv.symm s 0)
            (Set.powersetCard.ofFinEmbEquiv.symm t 0) *
          LinearMap.toMatrix b c f (Set.powersetCard.ofFinEmbEquiv.symm s 1)
            (Set.powersetCard.ofFinEmbEquiv.symm t 1) -
        LinearMap.toMatrix b c g (Set.powersetCard.ofFinEmbEquiv.symm s 1)
            (Set.powersetCard.ofFinEmbEquiv.symm t 0) *
          LinearMap.toMatrix b c f (Set.powersetCard.ofFinEmbEquiv.symm s 0)
            (Set.powersetCard.ofFinEmbEquiv.symm t 1)) := by
  have hmat : LinearMap.toMatrix (b.exteriorPower 2) (c.exteriorPower 2)
      (exteriorPower.symmMap₂ f g) =
      ⅟(2 : R) • (LinearMap.toMatrix (b.exteriorPower 2) (c.exteriorPower 2)
          (exteriorPower.map 2 (f + g)) -
        LinearMap.toMatrix (b.exteriorPower 2) (c.exteriorPower 2) (exteriorPower.map 2 f) -
        LinearMap.toMatrix (b.exteriorPower 2) (c.exteriorPower 2) (exteriorPower.map 2 g)) := by
    simp only [exteriorPower.symmMap₂_eq_invOf_two_smul_map_add_sub, map_smul,
      map_sub (LinearMap.toMatrix (b.exteriorPower 2) (c.exteriorPower 2))]
  rw [hmat]
  simp only [Matrix.smul_apply, Matrix.sub_apply, toMatrix_exteriorPower_map, smul_eq_mul,
    Matrix.det_fin_two, Matrix.of_apply, map_add, Matrix.add_apply]
  ring

end Module.Basis

namespace exteriorPower

section Trace

variable {R M : Type*} [CommRing R] [Invertible (2 : R)]
  [AddCommGroup M] [Module R M] [Module.Free R M]

/-- The trace of `symmMap₂ f g` on `⋀[R]^2 M` is `⅟2 * (tr f * tr g - tr(f ∘ₗ g))`.
Neither `f` nor `g` need be symmetric, and `M` need not be finite. -/
theorem trace_symmMap₂ (f g : Module.End R M) :
    LinearMap.trace R (⋀[R]^2 M) (symmMap₂ f g) =
      ⅟(2 : R) * (LinearMap.trace R M f * LinearMap.trace R M g -
        LinearMap.trace R M (f ∘ₗ g)) := by
  cases subsingleton_or_nontrivial R
  · simp [eq_iff_true_of_subsingleton]
  classical
  by_cases hfin : Module.Finite R M
  · let I := Module.Free.ChooseBasisIndex R M
    let _ : LinearOrder I := linearOrderOfSTO WellOrderingRel
    let b := Module.Free.chooseBasis R M
    have : Finite I := Module.Finite.finite_basis b
    let _ : Fintype I := Fintype.ofFinite I
    let A := LinearMap.toMatrix b b f
    let C := LinearMap.toMatrix b b g
    let F (i j : I) : R := A i i * C j j - A j i * C i j + C i i * A j j - C j i * A i j
    have htr : LinearMap.trace R (⋀[R]^2 M) (symmMap₂ f g) =
        ⅟(2 : R) * ∑ s : Set.powersetCard I 2,
          F (Set.powersetCard.ofFinEmbEquiv.symm s 0)
            (Set.powersetCard.ofFinEmbEquiv.symm s 1) := by
      rw [LinearMap.trace_eq_matrix_trace R (b.exteriorPower 2) (symmMap₂ f g), Matrix.trace,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun s _ ↦ ?_
      have h := b.toMatrix_exteriorPower_symmMap₂ b f g s s
      dsimp only [Matrix.diag, F, A, C] at h ⊢
      simpa only [LinearMap.toMatrix_apply] using h
    have hsum : ∑ i : I, ∑ j : I, F i j =
        2 • ∑ s : Set.powersetCard I 2,
          F (Set.powersetCard.ofFinEmbEquiv.symm s 0)
            (Set.powersetCard.ofFinEmbEquiv.symm s 1) :=
      Set.powersetCard.sum_sum_eq_two_nsmul_sum_of_symm_of_diag_eq_zero F
        (fun _ _ ↦ by simp only [F]; ring) (fun _ ↦ by simp only [F]; ring)
    have hF : ∑ i : I, ∑ j : I, F i j =
        2 * (LinearMap.trace R M f * LinearMap.trace R M g - LinearMap.trace R M (f ∘ₗ g)) := by
      rw [LinearMap.trace_eq_matrix_trace R b f, LinearMap.trace_eq_matrix_trace R b g,
        LinearMap.trace_eq_matrix_trace R b (f ∘ₗ g), LinearMap.toMatrix_comp b b b f g]
      exact Matrix.sum_symmMinor_eq_two_mul_trace_sub A C
    have h2 := congrArg (⅟(2 : R) * ·) (hsum.symm.trans hF)
    rw [nsmul_eq_mul, Nat.cast_ofNat, ← mul_assoc, ← mul_assoc, invOf_mul_self, one_mul,
      one_mul] at h2
    rw [htr, h2]
  · have hnotfin : ¬ Module.Finite R (⋀[R]^2 M) := by
      intro hext
      let I := Module.Free.ChooseBasisIndex R M
      let b := Module.Free.chooseBasis R M
      have : Infinite I := by
        by_contra hI
        exact hfin (have := not_infinite_iff_finite.1 hI; Module.Finite.of_basis b)
      let _ : LinearOrder I := linearOrderOfSTO WellOrderingRel
      have := Module.Finite.finite_basis (b.exteriorPower 2)
      exact not_finite (Set.powersetCard I 2)
    rw [TauCeti.LinearMap.trace_eq_zero_of_not_finite hnotfin,
      TauCeti.LinearMap.trace_eq_zero_of_not_finite hfin]
    simp

/-- The trace of `symmMap₂ f id` on `⋀[R]^2 M` is `((finrank R M - 1) * ⅟2) * tr f`. -/
theorem trace_symmMap₂_id_right (f : Module.End R M) :
    LinearMap.trace R (⋀[R]^2 M) (symmMap₂ f LinearMap.id) =
      ((Module.finrank R M : R) - 1) * ⅟(2 : R) * LinearMap.trace R M f := by
  by_cases hfin : Module.Finite R M
  · rw [trace_symmMap₂, LinearMap.trace_id, LinearMap.comp_id]
    ring
  · rw [trace_symmMap₂, TauCeti.LinearMap.trace_eq_zero_of_not_finite hfin]
    simp

end Trace

end exteriorPower

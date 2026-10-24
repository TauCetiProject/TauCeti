/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.BilinearForm.Diagonalization
public import TauCeti.LinearAlgebra.BilinearForm.Modular
public import Mathlib.LinearAlgebra.BilinearForm.IsometryEquiv
public import Mathlib.RingTheory.LocalRing.Basic
import TauCeti.LinearAlgebra.BilinearForm.LinearIndependent
import TauCeti.LinearAlgebra.BilinearForm.Orthogonal
import TauCeti.LinearAlgebra.PerfectPairing.Basis
import TauCeti.LinearAlgebra.Submodule.Compl

/-!
# Bilinear forms over local rings

This file records consequences of a unit Gram determinant or a perfect pairing over a local ring.
A nonunit diagonal
entry forces a unit off-diagonal entry in the same row. A symmetric perfect pairing with nonunit
diagonal values splits off a binary perfect summand whenever a dual vector takes the value one.
For an even symmetric form when `2` is a
nonunit, such an entry determines a perfect binary summand and an orthogonal decomposition.

## Main results

* `LinearMap.BilinForm.exists_index_ne_zero_isUnit_apply_of_not_isUnit_diag_of_isUnit_det` finds
  a unit off-diagonal entry from a nonunit diagonal entry.
* `LinearMap.BilinForm.IsSymm.exists_binary_isPerfPair_isCompl_orthogonal_of_dual_apply_eq_one`
  splits a binary perfect summand from a perfect pairing with nonunit diagonal values.
* `LinearMap.BilinForm.IsSymm.exists_binary_isPerfPair_isCompl_orthogonal` splits a perfect binary
  summand from an even unimodular form.
* `LinearMap.BilinForm.IsSymm.exists_basis_orthogonal` splits off the span of a family with unit
  Gram determinant, with a basis of the complement and the resulting factorization of the Gram
  determinant.
* `LinearMap.BilinForm.IsSymm.exists_basis_orthogonal_span_singleton_isUnit_det`: in particular,
  the orthogonal complement of a vector with unit self-pairing in a unimodular form is unimodular.
* `LinearMap.BilinForm.IsSymm.equivalent_of_equivalent_restrict_orthogonal` recombines two such
  splittings with the same Gram matrix into an isometry.
-/

public section

namespace LinearMap.BilinForm

open LinearMap (BilinForm)
open Module

section Blocks

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {B : BilinForm R M} {C : BilinForm R N}

/-- **Recombining blocks.** If families `v` in `M` and `v'` in `N` have the same Gram matrix `G` of
unit determinant, and the restrictions of `B` and `C` to the orthogonal complements of their
spans are isometric, then `B` and `C` are isometric. -/
theorem IsSymm.equivalent_of_equivalent_restrict_orthogonal {ι : Type*} [Fintype ι]
    [DecidableEq ι] (hB : B.IsSymm) (hC : C.IsSymm) {v : ι → M} {v' : ι → N}
    {G : Matrix ι ι R} (hG : ∀ i j, B (v i) (v j) = G i j) (hG' : ∀ i j, C (v' i) (v' j) = G i j)
    (hdet : IsUnit G.det)
    (hc : IsCompl (Submodule.span R (Set.range v))
      (B.orthogonal (Submodule.span R (Set.range v))))
    (hc' : IsCompl (Submodule.span R (Set.range v'))
      (C.orthogonal (Submodule.span R (Set.range v'))))
    (h : (B.restrict (B.orthogonal (Submodule.span R (Set.range v)))).Equivalent
      (C.restrict (C.orthogonal (Submodule.span R (Set.range v'))))) :
    B.Equivalent C := by
  set S := Submodule.span R (Set.range v)
  set S' := Submodule.span R (Set.range v')
  have hli := linearIndependent_of_isUnit_det (nonZeroDivisors R).one_mem
    (fun i j ↦ by rw [one_mul, hG]) hdet
  have hli' := linearIndependent_of_isUnit_det (nonZeroDivisors R).one_mem
    (fun i j ↦ by rw [one_mul, hG']) hdet
  -- The blocks spanned by `v` and `v'` are isometric, matching the two bases.
  let φ : S ≃ₗ[R] S' := (Basis.span hli).equiv (Basis.span hli') (Equiv.refl _)
  have hφ : (C.restrict S').compl₁₂ φ.toLinearMap φ.toLinearMap = B.restrict S :=
    ext_basis (Basis.span hli) fun i j ↦ by
      simp only [LinearMap.compl₁₂_apply, LinearEquiv.coe_coe, φ, Basis.equiv_apply,
        Equiv.refl_apply, restrict_apply]
      simp [Basis.span_apply hli, Basis.span_apply hli', hG, hG']
  have hS : (B.restrict S).Equivalent (C.restrict S') :=
    ⟨{ toLinearEquiv := φ, map_app' := fun x y ↦ LinearMap.congr_fun₂ hφ x y }⟩
  let P : Fin 2 → Submodule R M := ![S, B.orthogonal S]
  let P' : Fin 2 → Submodule R N := ![S', C.orthogonal S']
  have huniv : (Set.univ : Set (Fin 2)) = {0, 1} := by
    ext i
    fin_cases i <;> simp
  refine equivalent_of_isInternal (N := P) (N' := P')
    ((DirectSum.isInternal_submodule_iff_isCompl P zero_ne_one huniv).mpr hc)
    ((DirectSum.isInternal_submodule_iff_isCompl P' zero_ne_one huniv).mpr hc') ?_ ?_ ?_
  · intro i j hij x hx y hy
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact hy x hx
    · rw [hB.eq]
      exact hx y hy
    · exact absurd rfl hij
  · intro i j hij x hx y hy
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact hy x hx
    · rw [hC.eq]
      exact hx y hy
    · exact absurd rfl hij
  · intro i
    fin_cases i
    · exact hS
    · exact h

variable [IsLocalRing R]

/-- **Splitting off a block.** If the Gram matrix `G` of a family `v` of `k` vectors has unit
determinant, the span `S` of `v` is complementary to its orthogonal complement `T`. If `M` has a
basis of size `m + k`, then `T` has a basis `t` of size `m`, and the Gram determinant of `B` is
`w ^ 2 * det G * det (B|_T)` for a unit `w`. -/
theorem IsSymm.exists_basis_orthogonal (hB : B.IsSymm) {m k : ℕ}
    (b : Basis (Fin (m + k)) R M) {v : Fin k → M} {G : Matrix (Fin k) (Fin k) R}
    (hG : ∀ i j, B (v i) (v j) = G i j) (hdet : IsUnit G.det) :
    IsCompl (Submodule.span R (Set.range v)) (B.orthogonal (Submodule.span R (Set.range v))) ∧
      ∃ t : Basis (Fin m) R (B.orthogonal (Submodule.span R (Set.range v))), ∃ w : R,
        IsUnit w ∧ (B.toMatrix b).det =
          w ^ 2 * (G.det * ((B.restrict (B.orthogonal (Submodule.span R (Set.range v)))).toMatrix
            t).det) := by
  classical
  set S := Submodule.span R (Set.range v)
  set T := B.orthogonal S
  have hG₁ : ∀ i j, B (v i) (v j) = 1 * G i j := fun i j ↦ by rw [one_mul, hG]
  have hc : IsCompl S T := (isModular_restrict_span_range (nonZeroDivisors R).one_mem hG₁
    hdet).isCompl_orthogonal hB (nonZeroDivisors R).one_mem fun _ _ ↦ one_dvd _
  refine ⟨hc, ?_⟩
  have hli : LinearIndependent R v :=
    linearIndependent_of_isUnit_det (nonZeroDivisors R).one_mem hG₁ hdet
  let s : Basis (Fin k) R S := Basis.span hli
  have : Module.Free R M := .of_basis b
  have : Module.Finite R M := .of_basis b
  have : Module.Free R S := .of_basis s
  have : Module.Finite R S := .of_basis s
  obtain ⟨hTfin, hTfree⟩ := T.finite_free_of_isCompl hc.symm
  have hT : finrank R T = m := by
    have hrank := (S.prodEquivOfIsCompl T hc).finrank_eq
    rw [Module.finrank_prod, finrank_eq_card_basis s, finrank_eq_card_basis b] at hrank
    simp only [Fintype.card_fin] at hrank
    omega
  let t : Basis (Fin m) R T := Module.finBasisOfFinrankEq R T hT
  refine ⟨t, ?_⟩
  -- The basis adapted to `M = S ⊕ T` has a block-diagonal Gram matrix.
  let c : Basis (Fin k ⊕ Fin m) R M := (s.prod t).map (S.prodEquivOfIsCompl T hc)
  have hcl (i : Fin k) : c (Sum.inl i) = v i := by simp [c, s, Basis.span_apply hli i]
  have hcr (j : Fin m) : c (Sum.inr j) = t j := by simp [c]
  have hvT (i : Fin k) (j : Fin m) : B (v i) (t j) = 0 :=
    (t j).2 (v i) (Submodule.subset_span ⟨i, rfl⟩)
  have hTv (j : Fin m) (i : Fin k) : B (t j) (v i) = 0 := by rw [← hB.eq, hvT]
  have hblock : B.toMatrix c =
      Matrix.fromBlocks G 0 0 ((B.restrict T).toMatrix t) := by
    ext (i | i) (j | j) <;> simp [toMatrix_apply, hcl, hcr, hG, hvT, hTv]
  let e : Fin k ⊕ Fin m ≃ Fin (m + k) := finSumFinEquiv.trans (finCongr (by omega))
  have hb : (B.toMatrix (b.reindex e.symm)).det = (B.toMatrix b).det := by
    rw [← Matrix.det_submatrix_equiv_self e (B.toMatrix b)]
    congr 1
    ext i j
    simp [toMatrix_apply]
  let := c.invertibleToMatrix (b.reindex e.symm)
  refine ⟨(c.toMatrix (b.reindex e.symm)).det, Matrix.isUnit_det_of_invertible _, ?_⟩
  rw [← hb, det_toMatrix_eq_det_sq_mul_det c, hblock, Matrix.det_fromBlocks_zero₂₁]

/-- The orthogonal complement of a vector `x` with unit self-pairing, for a symmetric form whose
Gram determinant in a basis of size `n + 1` is a unit, has a basis of size `n` in which the Gram
determinant of the restricted form is a unit. -/
theorem IsSymm.exists_basis_orthogonal_span_singleton_isUnit_det (hB : B.IsSymm) {n : ℕ}
    (b : Basis (Fin (n + 1)) R M) (hdet : IsUnit (B.toMatrix b).det) {x : M}
    (hx : IsUnit (B x x)) :
    ∃ t : Basis (Fin n) R (B.orthogonal (R ∙ x)),
      IsUnit ((B.restrict (B.orthogonal (R ∙ x))).toMatrix t).det := by
  let v : Fin 1 → M := fun _ ↦ x
  let G : Matrix (Fin 1) (Fin 1) R := fun _ _ ↦ B x x
  have hGdet : IsUnit G.det := by
    rw [Matrix.det_fin_one]
    exact hx
  obtain ⟨_, t, _w, _hw, hdetT⟩ :=
    hB.exists_basis_orthogonal (m := n) b (v := v) (fun _ _ ↦ rfl) hGdet
  rw [hdetT] at hdet
  have hTdet := isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_right hdet)
  have hvspan : Submodule.span R (Set.range v) = R ∙ x := by simp [v]
  exact hvspan ▸ ⟨t, hTdet⟩

end Blocks

variable {R M : Type*} [CommRing R] [IsLocalRing R] [AddCommGroup M] [Module R M]
  (B : BilinForm R M)

/-- In a positive-rank unimodular form over a local ring, if the first basis vector has
nonunit self-pairing, it pairs to a unit with a different basis vector. -/
theorem exists_index_ne_zero_isUnit_apply_of_not_isUnit_diag_of_isUnit_det
    {n : ℕ} (b : Basis (Fin (n + 1)) R M)
    (hdiag : ¬ IsUnit (B (b 0) (b 0)))
    (hdet : IsUnit (B.toMatrix b).det) :
    ∃ i : Fin (n + 1), i.val ≠ 0 ∧
      IsUnit (B (b 0) (b i)) := by
  obtain ⟨j, _, hj⟩ := IsLocalRing.exists_of_isUnit_sum
    (Matrix.det_succ_row_zero (B.toMatrix b) ▸ hdet)
  have hu : IsUnit (B (b 0) (b j)) := by
    simpa only [toMatrix_apply] using
      isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_left hj)
  have hj0 : j.val ≠ 0 := by
    intro hj0
    have hj0' : j = 0 := Fin.ext hj0
    subst j
    exact hdiag hu
  exact ⟨j, hj0, hu⟩

/-- In a symmetric form over a local ring where `2` is not a unit, two vectors have a unit Gram
determinant if their mutual pairing is a unit and one self-pairing is divisible by `2`. -/
theorem IsSymm.isUnit_pairGramDet_of_dvd_apply_self (hB : B.IsSymm) {x y : M}
    (hxx2 : (2 : R) ∣ B x x) (h2 : ¬ IsUnit (2 : R))
    (hxy : IsUnit (B x y)) :
    IsUnit (!![B x x, B x y; B y x, B y y] : Matrix (Fin 2) (Fin 2) R).det := by
  have hxx : B x x ∈ nonunits R := by
    rw [mem_nonunits_iff]
    exact fun h ↦ h2 (isUnit_of_dvd_unit hxx2 h)
  have hdiag : B x x * B y y ∈ nonunits R := mul_mem_nonunits_left hxx
  have hoff : IsUnit (B x y * B y x) := hxy.mul (hB.eq x y ▸ hxy)
  have hunit : IsUnit (B x x * B y y - B x y * B y x) := by
    by_contra hdet
    have hneg : -(B x x * B y y - B x y * B y x) ∈ nonunits R := by
      simpa only [mem_nonunits_iff, IsUnit.neg_iff] using hdet
    have hnonunit := IsLocalRing.nonunits_add hdiag hneg
    have hcancel : B x x * B y y + -(B x x * B y y - B x y * B y x) =
        B x y * B y x := by
      ring
    rw [hcancel] at hnonunit
    exact hnonunit hoff
  simpa [Matrix.det_fin_two] using hunit

/-- A symmetric perfect pairing with nonunit diagonal values splits off a binary perfect
pairing if some linear functional takes the value one. The summand is supplied with a basis
and is complementary to its orthogonal complement. -/
theorem IsSymm.exists_binary_isPerfPair_isCompl_orthogonal_of_dual_apply_eq_one
    [B.IsPerfPair] (hB : B.IsSymm)
    (hdiag : ∀ x, ¬ IsUnit (B x x)) (x : M) (f : Module.Dual R M) (hfx : f x = 1) :
    ∃ S : Submodule R M, Nonempty (Basis (Fin 2) R S) ∧
      (B.restrict S).IsPerfPair ∧ IsCompl S (B.orthogonal S) := by
  classical
  obtain ⟨w, hw⟩ := (LinearMap.IsPerfPair.bijective_left B).surjective f
  have hxw : B x w = 1 := by rw [hB.eq, hw, hfx]
  obtain ⟨hli, hmod⟩ := hB.linearIndependent_and_isModular_restrict_span_pair (one_mem _)
    hxw (one_mul (B x x)).symm (one_mul (B w w)).symm
    (fun h ↦ hdiag x (isUnit_of_mul_isUnit_left h))
  have hp := isModular_one_iff.mp hmod
  exact ⟨_, ⟨Basis.span hli⟩, hp,
    B.isCompl_orthogonal_of_restrict_bijective _ (hB.restrict _)
      (LinearMap.IsPerfPair.bijective_left _)⟩

/-- **Even unimodular forms split off a perfect binary summand.** In rank at least two, an even
symmetric form with unit Gram determinant has two basis vectors whose span has rank two, carries
a perfect restriction of the form, and is complementary to its orthogonal complement. -/
theorem IsSymm.exists_binary_isPerfPair_isCompl_orthogonal (hB : B.IsSymm)
    {n : ℕ} (b : Basis (Fin (n + 2)) R M)
    (heven : ∀ x, (2 : R) ∣ B x x) (h2 : ¬ IsUnit (2 : R))
    (hdet : IsUnit (B.toMatrix b).det) :
    ∃ S : Submodule R M,
      finrank R S = 2 ∧ (B.restrict S).IsPerfPair ∧ IsCompl S (B.orthogonal S) := by
  have : B.IsPerfPair := b.isPerfPair_of_isUnit_det B hdet
  obtain ⟨S, ⟨c⟩, hS, hc⟩ :=
    hB.exists_binary_isPerfPair_isCompl_orthogonal_of_dual_apply_eq_one B
      (fun x hx ↦ h2 (isUnit_of_dvd_unit (heven x) hx)) (b 0) (b.coord 0) (by simp)
  refine ⟨S, ?_, hS, hc⟩
  simpa using Module.finrank_eq_card_basis c

end LinearMap.BilinForm

end

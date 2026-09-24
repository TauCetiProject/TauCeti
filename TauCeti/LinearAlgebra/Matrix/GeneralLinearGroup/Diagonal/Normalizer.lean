/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Basic
public import TauCeti.Algebra.Group.NormalizerQuotient.Basic

/-!
# The normalizer of the diagonal torus

Over a field with at least two units, an invertible matrix normalizes the diagonal torus exactly
when it is monomial: it is a diagonal matrix followed by a permutation matrix.  The permutation
is unique, and multiplication of monomial matrices multiplies these permutations.  Consequently
the quotient of the normalizer by the diagonal torus is canonically the symmetric group.

This is the group-of-points calculation behind the Weyl group of the diagonal maximal torus in
`GL_n`.  It complements `TauCeti.SplitTorus.coordinatePermMulEquivWeylGroup`, which identifies the
Weyl group of the corresponding coordinate root datum with the same permutation group.

## Main declarations

* `TauCeti.permutationGL`: the permutation-matrix embedding in `GL`.
* `TauCeti.coe_permutationGL_inv_mul_mul_permutationGL_apply`: conjugation by a permutation matrix
  relabels both matrix indices.
* `TauCeti.diagGL_mul_permutationGL`: moving a permutation matrix past a diagonal one relabels
  the diagonal entries.
* `TauCeti.exists_eq_diagGL_mul_permutationGL_of_forall_ne`: an invertible matrix whose
  conjugation keeps a coordinate-separating family of diagonal matrices diagonal is monomial.
* `TauCeti.mem_normalizer_diagonalTorus_iff_exists`: normalizing matrices are precisely products
  of a diagonal matrix and a permutation matrix.
* `TauCeti.diagonalNormalizerPerm`: the permutation homomorphism from the normalizer.
* `TauCeti.diagonalNormalizer_mul_diagGL_mul_inv`: conjugation by a normalizer element relabels
  diagonal coordinates by its coordinate permutation.
* `TauCeti.diagonalNormalizerQuotientMulEquivPerm`: the normalizer quotient is the symmetric
  group.

## References

* J. S. Milne, *Algebraic Groups* (2017), Example 19.7 and Section 21.1.
* J. E. Humphreys, *Linear Algebraic Groups* (1975), Sections 16.1 and 26.3.

This advances Layer 7, "Borel subgroups, maximal tori" and "Root datum `(G, T)`", of the
ReductiveGroups roadmap through the standard split maximal torus of `GL_n`.
-/

public section

open Matrix

namespace TauCeti

universe u

noncomputable section

variable {k : Type u} {n : ℕ}

section Permutation

variable [Semiring k]

/-- A permutation as an invertible matrix.  The inverse in the matrix entry is what makes this a
homomorphism with Mathlib's convention for multiplication in `Equiv.Perm`. -/
def permutationGL {ι : Type*} [Fintype ι] [DecidableEq ι] :
    Equiv.Perm ι →* GL ι k :=
  (Matrix.permMatrixHom (R := k)).toHomUnits

/-- The matrix underlying `permutationGL σ` is the permutation matrix of `σ⁻¹`. -/
@[simp]
theorem permutationGL_coe {ι : Type*} [Fintype ι] [DecidableEq ι] (σ : Equiv.Perm ι) :
    (permutationGL (k := k) σ : Matrix ι ι k) = σ⁻¹.permMatrix k :=
  by
    rw [permutationGL, MonoidHom.coe_toHomUnits]
    rfl

/-- Right multiplication by `permutationGL σ` permutes the columns: the `(i, j)` entry of
`g * permutationGL σ` is the `(i, σ j)` entry of `g`. -/
@[simp]
theorem coe_mul_permutationGL_apply {ι : Type*} [Fintype ι] [DecidableEq ι] (g : GL ι k)
    (σ : Equiv.Perm ι) (i j : ι) :
    ((g * permutationGL (k := k) σ : GL ι k) : Matrix ι ι k) i j =
      (g : Matrix ι ι k) i (σ j) := by
  rw [Units.val_mul, permutationGL_coe, Equiv.Perm.permMatrix, PEquiv.mul_toMatrix_toPEquiv]
  simp [Equiv.Perm.inv_def]

/-- Conjugation by `permutationGL σ` relabels both indices: the `(i, j)` entry of
`(permutationGL σ)⁻¹ * g * permutationGL σ` is the `(σ i, σ j)` entry of `g`. -/
@[simp]
theorem coe_permutationGL_inv_mul_mul_permutationGL_apply {ι : Type*} [Fintype ι]
    [DecidableEq ι] (σ : Equiv.Perm ι) (g : GL ι k) (i j : ι) :
    (((permutationGL (k := k) σ)⁻¹ * g * permutationGL (k := k) σ : GL ι k) :
        Matrix ι ι k) i j = (g : Matrix ι ι k) (σ i) (σ j) := by
  rw [coe_mul_permutationGL_apply, ← map_inv, Units.val_mul, permutationGL_coe, inv_inv,
    Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul, Matrix.submatrix_apply, id]

/-- Conjugating a diagonal matrix by a permutation matrix relabels its diagonal entries. -/
@[simp]
theorem permutationGL_mul_diagGL_mul_inv (σ : Equiv.Perm (Fin n)) (t : Fin n → kˣ) :
    permutationGL (k := k) σ * diagGL t * (permutationGL (k := k) σ)⁻¹ =
      diagGL (fun i ↦ t (σ⁻¹ i)) := by
  rw [mul_diagGL_of_coe_eq_permMatrix
    (g := permutationGL (k := k) σ) (π := σ⁻¹) (permutationGL_coe σ),
    mul_inv_cancel_right]
  congr

/-- Moving a permutation matrix past a diagonal one relabels the diagonal entries. -/
theorem diagGL_mul_permutationGL (σ : Equiv.Perm (Fin n)) (t : Fin n → kˣ) :
    diagGL t * permutationGL (k := k) σ =
      permutationGL (k := k) σ * diagGL fun i ↦ t (σ i) := by
  have h : permutationGL (k := k) σ * (diagGL fun i ↦ t (σ i)) * (permutationGL (k := k) σ)⁻¹
      = diagGL t := by
    rw [permutationGL_mul_diagGL_mul_inv]
    congr 1
    funext i
    simp
  rw [← h, inv_mul_cancel_right]

/-- Permutation matrices normalize the diagonal torus. -/
theorem permutationGL_mem_normalizer (σ : Equiv.Perm (Fin n)) :
    permutationGL (k := k) σ ∈
      Subgroup.normalizer (diagonalTorus k n : Set (GL (Fin n) k)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro d
  constructor
  · rw [mem_diagonalTorus_iff_exists_diagGL]
    rintro ⟨t, rfl⟩
    rw [permutationGL_mul_diagGL_mul_inv]
    exact mem_diagonalTorus_iff_exists_diagGL.mpr ⟨fun i ↦ t (σ⁻¹ i), rfl⟩
  · intro hd
    obtain ⟨t, ht⟩ := mem_diagonalTorus_iff_exists_diagGL.mp hd
    have hback := permutationGL_mul_diagGL_mul_inv (k := k) (n := n) σ⁻¹ t
    rw [map_inv, inv_inv] at hback
    have hback' : (permutationGL (k := k) σ)⁻¹ * diagGL t *
        permutationGL (k := k) σ = diagGL (fun i ↦ t (σ i)) := by
      simpa only [inv_inv] using hback
    rw [ht] at hback'
    group at hback'
    rw [mem_diagonalTorus_iff_exists_diagGL]
    exact ⟨fun i ↦ t (σ i), hback'.symm⟩

end Permutation

section Field

variable [Field k] [Nontrivial kˣ]

omit [Nontrivial kˣ] in
/-- If conjugation by `g` sends the diagonal matrix `t` to a diagonal matrix, then `t` takes the
same value at any two columns in which a row of `g` is nonzero. -/
private theorem apply_eq_apply_of_conj_mem_diagonalTorus {g : GL (Fin n) k} {t : Fin n → kˣ}
    (ht : g * diagGL t * g⁻¹ ∈ diagonalTorus k n) {i j l : Fin n}
    (hj : (g : Matrix (Fin n) (Fin n) k) i j ≠ 0) (hl : (g : Matrix (Fin n) (Fin n) k) i l ≠ 0) :
    t j = t l := by
  -- Writing `g t g⁻¹ = s`, the entries of `g t = s g` read `g_{im} t_m = s_i g_{im}`.
  obtain ⟨s, hs⟩ := mem_diagonalTorus_iff_exists_diagGL.mp ht
  have heq : g * diagGL t = diagGL s * g := by
    rw [hs]
    group
  have hentry (m : Fin n) :
      (g : Matrix (Fin n) (Fin n) k) i m * t m = s i * (g : Matrix (Fin n) (Fin n) k) i m := by
    simpa [Matrix.mul_diagonal, Matrix.diagonal_mul] using
      congrArg (fun x : GL (Fin n) k ↦ (x : Matrix (Fin n) (Fin n) k) i m) heq
  have hj' : (t j : k) = s i := mul_left_cancel₀ hj (by rw [hentry j, mul_comm])
  have hl' : (t l : k) = s i := mul_left_cancel₀ hl (by rw [hentry l, mul_comm])
  exact Units.ext (hj'.trans hl'.symm)

omit [Nontrivial kˣ] in
/-- An invertible matrix is monomial, a diagonal matrix followed by a permutation matrix, as soon
as conjugation by it keeps enough diagonal matrices diagonal to tell every two coordinates
apart. -/
theorem exists_eq_diagGL_mul_permutationGL_of_forall_ne {g : GL (Fin n) k}
    (hsep : ∀ i j, i ≠ j → ∃ t : Fin n → kˣ,
      g * diagGL t * g⁻¹ ∈ diagonalTorus k n ∧ t i ≠ t j) :
    ∃ d : Fin n → kˣ, ∃ σ : Equiv.Perm (Fin n),
      g = diagGL d * permutationGL (k := k) σ := by
  classical
  let G : Matrix (Fin n) (Fin n) k := g
  let Ginv : Matrix (Fin n) (Fin n) k := (g⁻¹ : GL (Fin n) k)
  have hrow (i j l : Fin n) (hj : G i j ≠ 0) (hl : G i l ≠ 0) : j = l := by
    by_contra hjl
    obtain ⟨t, ht, htjl⟩ := hsep j l hjl
    exact htjl (apply_eq_apply_of_conj_mem_diagonalTorus ht hj hl)
  have hGGinv : G * Ginv = 1 := by
    simpa only [G, Ginv, ← Units.inv_eq_val_inv] using g.mul_inv
  have hGinvG : Ginv * G = 1 := by
    simpa only [G, Ginv, ← Units.inv_eq_val_inv] using g.inv_mul
  -- Every row of an invertible matrix has a nonzero entry.
  have hex : ∀ i, ∃ j, G i j ≠ 0 := by
    intro i
    by_contra h
    push Not at h
    have hii := congrArg (fun M : Matrix (Fin n) (Fin n) k ↦ M i i) hGGinv
    simp [Matrix.mul_apply, h] at hii
  choose f hf using hex
  have hf_iff (i j : Fin n) : G i j ≠ 0 ↔ j = f i :=
    ⟨fun h ↦ hrow i j (f i) h (hf i), by rintro rfl; exact hf i⟩
  -- A column missed by `f` would vanish, which is impossible for an invertible matrix.
  have hsurj : Function.Surjective f := by
    intro l
    by_contra h
    push Not at h
    have hcol (r : Fin n) : G r l = 0 := by
      by_contra hne
      exact h r ((hf_iff r l).mp hne).symm
    have hll := congrArg (fun M : Matrix (Fin n) (Fin n) k ↦ M l l) hGinvG
    simp [Matrix.mul_apply, hcol] at hll
  let e : Equiv.Perm (Fin n) :=
    Equiv.ofBijective f ⟨Finite.injective_iff_surjective.mpr hsurj, hsurj⟩
  have he (i : Fin n) : e i = f i := Equiv.ofBijective_apply _ _ i
  refine ⟨fun i ↦ Units.mk0 (G i (f i)) (hf i), e.symm, ?_⟩
  apply Units.ext
  ext i j
  simp only [Units.val_mul, diagGL_coe, permutationGL_coe, Matrix.diagonal_mul, Units.val_mk0]
  by_cases hj : j = f i
  · subst j
    simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, he, G]
  · have hzero : G i j = 0 := by
      by_contra h
      exact hj ((hf_iff i j).mp h)
    simpa [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, he, Ne.symm hj, G] using hzero

/-- An invertible matrix normalizes the diagonal torus exactly when it is a diagonal matrix
followed by a permutation matrix. -/
theorem mem_normalizer_diagonalTorus_iff_exists {g : GL (Fin n) k} :
    g ∈ Subgroup.normalizer (diagonalTorus k n : Set (GL (Fin n) k)) ↔
      ∃ d : Fin n → kˣ, ∃ σ : Equiv.Perm (Fin n),
        g = diagGL d * permutationGL (k := k) σ := by
  classical
  constructor
  · intro hg
    refine exists_eq_diagGL_mul_permutationGL_of_forall_ne fun i j hij ↦ ?_
    obtain ⟨u, hu⟩ : ∃ u : kˣ, u ≠ 1 := exists_ne 1
    refine ⟨Pi.mulSingle i u, (Subgroup.mem_normalizer_iff.mp hg _).mp
      (mem_diagonalTorus_iff_exists_diagGL.mpr ⟨_, rfl⟩), ?_⟩
    simpa [Pi.mulSingle_eq_of_ne hij.symm] using hu
  · rintro ⟨d, σ, rfl⟩
    exact (Subgroup.normalizer (diagonalTorus k n : Set (GL (Fin n) k))).mul_mem
      (Subgroup.le_normalizer (by
        exact mem_diagonalTorus_iff_exists_diagGL.mpr ⟨d, rfl⟩))
      (permutationGL_mem_normalizer σ)

omit [Nontrivial kˣ] in
private theorem permutation_eq_of_diagGL_mul_permutationGL_eq
    {d e : Fin n → kˣ} {σ τ : Equiv.Perm (Fin n)}
    (h : diagGL d * permutationGL (k := k) σ =
      diagGL e * permutationGL (k := k) τ) : σ = τ := by
  apply Equiv.ext
  intro j
  by_contra hj
  have hentry := congrArg
    (fun x : GL (Fin n) k ↦ (x : Matrix (Fin n) (Fin n) k) (σ j) j) h
  simp only [Units.val_mul, diagGL_coe, permutationGL_coe,
    Matrix.diagonal_mul] at hentry
  have hleft : (σ⁻¹.permMatrix k) (σ j) j = 1 := by
    simp [Equiv.Perm.permMatrix]
  have hright : (τ⁻¹.permMatrix k) (σ j) j = 0 := by
    simp [Equiv.Perm.permMatrix, Equiv.symm_apply_eq, hj]
  rw [hleft, hright, mul_one, mul_zero] at hentry
  exact Units.ne_zero (d (σ j)) hentry

/-- The diagonal factor in the chosen monomial factorization of a normalizer element. -/
private noncomputable def diagonalNormalizerDiag
    (g : Subgroup.normalizer (diagonalTorus k n : Set (GL (Fin n) k))) : Fin n → kˣ :=
  Classical.choose (mem_normalizer_diagonalTorus_iff_exists.mp g.property)

/-- The permutation factor in the chosen monomial factorization of a normalizer element. -/
private noncomputable def diagonalNormalizerPermFun
    (g : Subgroup.normalizer (diagonalTorus k n : Set (GL (Fin n) k))) :
    Equiv.Perm (Fin n) :=
  Classical.choose (Classical.choose_spec
    (mem_normalizer_diagonalTorus_iff_exists.mp g.property))

private theorem diagonalNormalizer_factor
    (g : Subgroup.normalizer (diagonalTorus k n : Set (GL (Fin n) k))) :
    (g : GL (Fin n) k) = diagGL (diagonalNormalizerDiag g) *
      permutationGL (k := k) (diagonalNormalizerPermFun g) :=
  Classical.choose_spec (Classical.choose_spec
    (mem_normalizer_diagonalTorus_iff_exists.mp g.property))

private theorem diagonalNormalizerPermFun_one :
    diagonalNormalizerPermFun
      (1 : Subgroup.normalizer (diagonalTorus k n : Set (GL (Fin n) k))) = 1 := by
  have hone : (1 : GL (Fin n) k) =
      diagGL (fun _ ↦ (1 : kˣ)) * permutationGL (k := k) 1 := by
    -- Present both factors as images of the identity under their defining homomorphisms.
    change 1 = diagGL (1 : Fin n → kˣ) * permutationGL (k := k) 1
    rw [map_one, map_one, mul_one]
  apply permutation_eq_of_diagGL_mul_permutationGL_eq (k := k)
  exact (diagonalNormalizer_factor 1).symm.trans hone

private theorem diagonalNormalizerPermFun_mul
    (g h : Subgroup.normalizer (diagonalTorus k n : Set (GL (Fin n) k))) :
    diagonalNormalizerPermFun (g * h) =
      diagonalNormalizerPermFun g * diagonalNormalizerPermFun h := by
  let σ := diagonalNormalizerPermFun g
  let τ := diagonalNormalizerPermFun h
  let d := diagonalNormalizerDiag g
  let e := diagonalNormalizerDiag h
  have hmove : permutationGL (k := k) σ * diagGL e =
      diagGL (fun i ↦ e (σ⁻¹ i)) * permutationGL (k := k) σ :=
    mul_diagGL_of_coe_eq_permMatrix (permutationGL (k := k) σ) σ⁻¹
      (permutationGL_coe σ) e
  have hfactor : ((g * h :
      Subgroup.normalizer (diagonalTorus k n : Set (GL (Fin n) k))) : GL (Fin n) k) =
      diagGL (fun i ↦ d i * e (σ⁻¹ i)) * permutationGL (k := k) (σ * τ) := by
    -- Forget the normalizer subtype so the two chosen monomial factorizations can be substituted.
    change (g : GL (Fin n) k) * (h : GL (Fin n) k) = _
    rw [diagonalNormalizer_factor g, diagonalNormalizer_factor h]
    -- Name the four factors before moving the middle diagonal past the permutation matrix.
    change (diagGL d * permutationGL (k := k) σ) *
      (diagGL e * permutationGL (k := k) τ) = _
    rw [mul_assoc, ← mul_assoc (permutationGL (k := k) σ), hmove]
    have hdiag : diagGL (fun i ↦ d i * e (σ⁻¹ i)) =
        diagGL d * diagGL (fun i ↦ e (σ⁻¹ i)) := by
      rw [← map_mul]
      rfl
    rw [hdiag, map_mul (permutationGL (k := k)) σ τ]
    group
  apply permutation_eq_of_diagGL_mul_permutationGL_eq (k := k)
  exact (diagonalNormalizer_factor (g * h)).symm.trans hfactor

/-- The permutation of coordinate lines induced by a matrix normalizing the diagonal torus. -/
noncomputable def diagonalNormalizerPerm :
    Subgroup.normalizer (diagonalTorus k n : Set (GL (Fin n) k)) →*
      Equiv.Perm (Fin n) where
  toFun := diagonalNormalizerPermFun
  map_one' := diagonalNormalizerPermFun_one
  map_mul' := diagonalNormalizerPermFun_mul

/-- A monomial factorization of a diagonal-normalizer element has the coordinate permutation
selected by `diagonalNormalizerPerm`. -/
theorem diagonalNormalizerPerm_eq_of_eq_diagGL_mul_permutationGL
    (g : Subgroup.normalizer (diagonalTorus k n : Set (GL (Fin n) k)))
    (d : Fin n → kˣ) (σ : Equiv.Perm (Fin n))
    (h : (g : GL (Fin n) k) = diagGL d * permutationGL (k := k) σ) :
    diagonalNormalizerPerm (k := k) (n := n) g = σ := by
  apply permutation_eq_of_diagGL_mul_permutationGL_eq (k := k)
  exact (diagonalNormalizer_factor g).symm.trans h

/-- The coordinate permutation induced by a permutation matrix is the original permutation. -/
@[simp]
theorem diagonalNormalizerPerm_permutationGL (σ : Equiv.Perm (Fin n)) :
    diagonalNormalizerPerm (k := k) (n := n)
        ⟨permutationGL (k := k) σ, permutationGL_mem_normalizer σ⟩ = σ := by
  have hone : permutationGL (k := k) σ =
      diagGL (fun _ ↦ (1 : kˣ)) * permutationGL (k := k) σ := by
    -- Present the trivial diagonal factor as the image of the identity.
    change permutationGL (k := k) σ =
      diagGL (1 : Fin n → kˣ) * permutationGL (k := k) σ
    rw [map_one, one_mul]
  exact diagonalNormalizerPerm_eq_of_eq_diagGL_mul_permutationGL _ _ σ hone

/-- Conjugation by a diagonal-normalizer element relabels the diagonal entries by its coordinate
permutation: the entry at `i` becomes the original entry at the inverse image of `i`. -/
@[simp]
theorem diagonalNormalizer_mul_diagGL_mul_inv
    (g : Subgroup.normalizer (diagonalTorus k n : Set (GL (Fin n) k)))
    (t : Fin n → kˣ) :
    (g : GL (Fin n) k) * diagGL t * (g : GL (Fin n) k)⁻¹ =
      diagGL (fun i ↦ t ((diagonalNormalizerPerm (k := k) (n := n) g).symm i)) := by
  obtain ⟨d, σ, hg⟩ := mem_normalizer_diagonalTorus_iff_exists.mp g.property
  have hσ := diagonalNormalizerPerm_eq_of_eq_diagGL_mul_permutationGL g d σ hg
  rw [hσ, hg]
  calc
    (diagGL d * permutationGL (k := k) σ) * diagGL t *
          (diagGL d * permutationGL (k := k) σ)⁻¹ =
        diagGL d *
          (permutationGL (k := k) σ * diagGL t *
            (permutationGL (k := k) σ)⁻¹) * (diagGL d)⁻¹ := by group
    _ = diagGL d * diagGL (fun i ↦ t (σ⁻¹ i)) * (diagGL d)⁻¹ := by
      rw [permutationGL_mul_diagGL_mul_inv]
    _ = diagGL (fun i ↦ t (σ⁻¹ i)) := by
      have hcomm : Commute (diagGL d) (diagGL (fun i ↦ t (σ⁻¹ i))) :=
        (Commute.all d (fun i ↦ t (σ⁻¹ i))).map diagGL
      rw [hcomm.eq]
      simp

/-- Every coordinate permutation is induced by a permutation matrix in the normalizer. -/
theorem diagonalNormalizerPerm_surjective :
    Function.Surjective (diagonalNormalizerPerm (k := k) (n := n)) := by
  intro σ
  exact ⟨⟨permutationGL (k := k) σ, permutationGL_mem_normalizer σ⟩,
    diagonalNormalizerPerm_permutationGL σ⟩

/-- The coordinate permutation induced by a normalizer element is trivial exactly for elements
of the diagonal torus. -/
@[simp]
theorem diagonalNormalizerPerm_eq_one_iff
    (g : Subgroup.normalizer (diagonalTorus k n : Set (GL (Fin n) k))) :
    diagonalNormalizerPerm (k := k) (n := n) g = 1 ↔
      (g : GL (Fin n) k) ∈ diagonalTorus k n := by
  constructor
  · intro hg
    have hfactor := diagonalNormalizer_factor g
    -- Unfold only the homomorphism's value, keeping the chosen factorization opaque.
    change diagonalNormalizerPermFun g = 1 at hg
    rw [hg, map_one, mul_one] at hfactor
    exact mem_diagonalTorus_iff_exists_diagGL.mpr
      ⟨diagonalNormalizerDiag g, hfactor.symm⟩
  · intro hg
    obtain ⟨d, hd⟩ := mem_diagonalTorus_iff_exists_diagGL.mp hg
    have hone : (g : GL (Fin n) k) =
        diagGL d * permutationGL (k := k) 1 := by
      rw [map_one, mul_one, hd]
    exact diagonalNormalizerPerm_eq_of_eq_diagGL_mul_permutationGL g d 1 hone

/-- The normalizer of the diagonal torus modulo the torus is canonically the symmetric group. -/
noncomputable def diagonalNormalizerQuotientMulEquivPerm :
    Subgroup.normalizerQuotient (diagonalTorus k n) ≃* Equiv.Perm (Fin n) := by
  let φ := diagonalNormalizerPerm (k := k) (n := n)
  have hkill : ∀ g : Subgroup.normalizer
      (diagonalTorus k n : Set (GL (Fin n) k)),
      (g : GL (Fin n) k) ∈ diagonalTorus k n → φ g = 1 := by
    intro g hg
    exact (diagonalNormalizerPerm_eq_one_iff g).mpr hg
  let φbar := Subgroup.normalizerQuotientLift (diagonalTorus k n) φ hkill
  apply MulEquiv.ofBijective φbar
  constructor
  · exact (Subgroup.normalizerQuotientLift_injective_iff
      (diagonalTorus k n) φ hkill).mpr diagonalNormalizerPerm_eq_one_iff
  · exact Subgroup.normalizerQuotientLift_surjective_of_surjective
      (diagonalTorus k n) φ hkill diagonalNormalizerPerm_surjective

/-- The quotient equivalence sends the class of a normalizer element to its coordinate
permutation. -/
@[simp]
theorem diagonalNormalizerQuotientMulEquivPerm_mk
    (g : Subgroup.normalizer (diagonalTorus k n : Set (GL (Fin n) k))) :
    diagonalNormalizerQuotientMulEquivPerm (k := k) (n := n)
        (g : Subgroup.normalizerQuotient (diagonalTorus k n)) =
      diagonalNormalizerPerm (k := k) (n := n) g :=
  by
    unfold diagonalNormalizerQuotientMulEquivPerm
    rfl

/-- The inverse quotient equivalence sends a coordinate permutation to the class of its
permutation matrix. -/
@[simp]
theorem diagonalNormalizerQuotientMulEquivPerm_symm_apply (σ : Equiv.Perm (Fin n)) :
    (diagonalNormalizerQuotientMulEquivPerm (k := k) (n := n)).symm σ =
      Subgroup.normalizerQuotientMk (diagonalTorus k n)
        ⟨permutationGL (k := k) σ, permutationGL_mem_normalizer σ⟩ := by
  apply (diagonalNormalizerQuotientMulEquivPerm (k := k) (n := n)).injective
  simp

end Field

end

end TauCeti

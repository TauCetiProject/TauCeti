/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Elementary

/-!
# Gauss–Jordan factorization and normality of the elementary subgroup over a division ring

Over a division ring `D`, Gaussian elimination reduces every invertible matrix to a diagonal matrix
supported at a single chosen coordinate: for any `i : n` and `g ∈ GL n D`, there exist an
elementary matrix `e ∈ TauCeti.elementarySubgroup n D` and a unit `u : Dˣ` such that
`g = e * diagGL (Pi.mulSingle i u)` (`TauCeti.exists_mem_elementarySubgroup_mul_diagGL_mulSingle`).
Consequently every invertible matrix factors as an elementary matrix times an invertible diagonal
matrix (`TauCeti.exists_mem_elementarySubgroup_mul_diagGL`), and two monoid homomorphisms out of
`GL n D` that vanish on `TauCeti.elementarySubgroup n D` agree as soon as they agree on the
single-entry diagonal matrices at one coordinate
(`Matrix.GeneralLinearGroup.hom_ext_of_elementarySubgroup_le_ker`).

Since invertible diagonal matrices normalize the generators of `TauCeti.elementarySubgroup n D`
(`TauCeti.diagGL_mul_transvectionUnit_mul_inv`), the Gauss–Jordan factorization implies that
`TauCeti.elementarySubgroup n D` is normal in `GL n D` already at every finite matrix size
(`TauCeti.elementarySubgroup_normal`), without stabilization.

## Main results

* `TauCeti.exists_mem_elementarySubgroup_mul_diagGL_mulSingle`: Gauss–Jordan factorization
  `g = e * diagGL (Pi.mulSingle i u)` in `GL n D`.
* `TauCeti.exists_mem_elementarySubgroup_mul_diagGL`: factorization `g = e * diagGL d` in `GL n D`.
* `TauCeti.elementarySubgroup_normal`: `TauCeti.elementarySubgroup n D` is normal in `GL n D`.
* `Matrix.GeneralLinearGroup.hom_ext_of_elementarySubgroup_le_ker`: homomorphisms out of `GL n D`
  vanishing on `TauCeti.elementarySubgroup n D` are determined by single-entry diagonal matrices at
  one coordinate.

## References

* J. Dieudonné, *Les déterminants sur un corps non commutatif*, Bull. Soc. Math. France **71**
  (1943), 27–45.
* E. Artin, *Geometric Algebra*, Interscience (1957), Chapter IV, §3.
-/

public section

noncomputable section

open Matrix

namespace TauCeti

variable {D : Type*} [DivisionRing D]

/-- Over a division ring, any `A ∈ GL (Fin (k + 2)) D` can be left-multiplied by an elementary
matrix so that its `(0, 0)` entry becomes `1`. -/
private theorem exists_mem_elementarySubgroup_mul_apply_zero_zero_eq_one (k : ℕ)
    (A : GL (Fin (k + 2)) D) :
    ∃ e ∈ elementarySubgroup (Fin (k + 2)) D, ((e * A : GL (Fin (k + 2)) D) 0 0 : D) = 1 := by
  have hstep1 : ∃ e₁ ∈ elementarySubgroup (Fin (k + 2)) D,
      ((e₁ * A : GL (Fin (k + 2)) D) 1 0 : D) ≠ 0 := by
    by_cases h10 : A 1 0 ≠ 0
    · exact ⟨1, one_mem _, by simpa using h10⟩
    push Not at h10
    obtain ⟨i, hi⟩ := exists_apply_ne_zero_col A 0
    have hi1 : (1 : Fin (k + 2)) ≠ i := fun h ↦ hi (h ▸ h10)
    refine ⟨transvectionUnit hi1 1, transvectionUnit_mem_elementarySubgroup hi1 1, ?_⟩
    rw [transvectionUnit_mul_apply]; simpa [h10] using hi
  obtain ⟨e₁, he₁, hB10⟩ := hstep1
  let B : GL (Fin (k + 2)) D := e₁ * A
  have hB10' : B 1 0 ≠ 0 := hB10
  have h01 : (0 : Fin (k + 2)) ≠ 1 := Fin.zero_ne_one
  let e₂ := transvectionUnit h01 ((1 - B 0 0) * (B 1 0)⁻¹)
  have hassoc : e₂ * (e₁ * A) = e₂ * B := rfl
  refine ⟨e₂ * e₁, mul_mem (transvectionUnit_mem_elementarySubgroup _ _) he₁, ?_⟩
  rw [mul_assoc, hassoc, transvectionUnit_mul_apply]
  simp [mul_assoc, inv_mul_cancel₀ hB10']

/-- Block elimination step on `Fin 1 ⊕ Fin (k + 1)` when the upper-left `1 × 1` entry is `1`. -/
private theorem exists_mem_elementarySubgroup_mul_fromBlocksGL {k : ℕ}
    (M : GL (Fin 1 ⊕ Fin (k + 1)) D)
    (hM11 : (M : Matrix (Fin 1 ⊕ Fin (k + 1)) (Fin 1 ⊕ Fin (k + 1)) D).toBlocks₁₁ = 1) :
    ∃ e ∈ elementarySubgroup (Fin 1 ⊕ Fin (k + 1)) D, ∃ S : GL (Fin (k + 1)) D,
      M = e * fromBlocksGL (1, S) := by
  let c := (M : Matrix (Fin 1 ⊕ Fin (k + 1)) (Fin 1 ⊕ Fin (k + 1)) D).toBlocks₂₁
  let M' : GL (Fin 1 ⊕ Fin (k + 1)) D := lowerBlockGL (-c) * M
  have hM'11 : (M' : Matrix (Fin 1 ⊕ Fin (k + 1)) (Fin 1 ⊕ Fin (k + 1)) D).toBlocks₁₁ = 1 := by
    have := congrArg Matrix.toBlocks₁₁ (Units.val_mul (lowerBlockGL (-c)) M)
    rw [coe_lowerBlockGL,
      ← Matrix.fromBlocks_toBlocks (M : Matrix (Fin 1 ⊕ Fin (k + 1)) (Fin 1 ⊕ Fin (k + 1)) D),
      hM11, Matrix.fromBlocks_multiply] at this
    simpa [M'] using this
  have hM'21 : (M' : Matrix (Fin 1 ⊕ Fin (k + 1)) (Fin 1 ⊕ Fin (k + 1)) D).toBlocks₂₁ = 0 := by
    have := congrArg Matrix.toBlocks₂₁ (Units.val_mul (lowerBlockGL (-c)) M)
    rw [coe_lowerBlockGL,
      ← Matrix.fromBlocks_toBlocks (M : Matrix (Fin 1 ⊕ Fin (k + 1)) (Fin 1 ⊕ Fin (k + 1)) D),
      hM11, Matrix.fromBlocks_multiply] at this
    simpa [M', c] using this
  let S := upperTriangularToBlocks₂₂GL M' hM'11 hM'21
  let r := (M' : Matrix (Fin 1 ⊕ Fin (k + 1)) (Fin 1 ⊕ Fin (k + 1)) D).toBlocks₁₂
  let rS : Matrix (Fin 1) (Fin (k + 1)) D :=
    r * ((S⁻¹ : GL (Fin (k + 1)) D) : Matrix (Fin (k + 1)) (Fin (k + 1)) D)
  have hM'_eq : M' = upperBlockGL rS * fromBlocksGL (1, S) := by
    apply Units.ext
    rw [Units.val_mul (upperBlockGL rS) (fromBlocksGL (1, S)), coe_upperBlockGL, coe_fromBlocksGL,
      Matrix.fromBlocks_multiply]
    conv_lhs =>
      rw [← Matrix.fromBlocks_toBlocks
        (M' : Matrix (Fin 1 ⊕ Fin (k + 1)) (Fin 1 ⊕ Fin (k + 1)) D), hM'11, hM'21]
    have hrS : rS * (S : Matrix (Fin (k + 1)) (Fin (k + 1)) D) = r := by
      dsimp only [rS]; rw [Matrix.mul_assoc, S.inv_mul, Matrix.mul_one]
    have hrS' : rS * (M' : Matrix (Fin 1 ⊕ Fin (k + 1)) (Fin 1 ⊕ Fin (k + 1)) D).toBlocks₂₂ =
        (M' : Matrix (Fin 1 ⊕ Fin (k + 1)) (Fin 1 ⊕ Fin (k + 1)) D).toBlocks₁₂ := by
      simpa [S] using hrS
    simp [S, hrS']
  refine ⟨(lowerBlockGL (-c))⁻¹ * upperBlockGL rS,
    mul_mem (inv_mem (lowerBlockGL_mem_elementarySubgroup _))
      (upperBlockGL_mem_elementarySubgroup _), S, ?_⟩
  have hM_from_M' : M = (lowerBlockGL (-c))⁻¹ * M' := by dsimp only [M']; group
  rw [hM_from_M', hM'_eq, mul_assoc]

/-- Inductive Gauss–Jordan factorization on `Fin (m + 1)`: every invertible matrix is an elementary
matrix times a diagonal matrix concentrated at `Fin.last m`. -/
private theorem exists_mem_elementarySubgroup_mul_lastDiag :
    ∀ (m : ℕ) (A : GL (Fin (m + 1)) D),
      ∃ e ∈ elementarySubgroup (Fin (m + 1)) D, ∃ u : Dˣ,
        A = e * diagGL (Pi.mulSingle (Fin.last m) u)
  | 0, A => by
    have h00 : A 0 0 * (A⁻¹ : GL (Fin 1) D) 0 0 = 1 := by
      simpa [Matrix.mul_apply] using congrFun (congrFun A.mul_inv 0) 0
    have h00' : (A⁻¹ : GL (Fin 1) D) 0 0 * A 0 0 = 1 := by
      simpa [Matrix.mul_apply] using congrFun (congrFun A.inv_mul 0) 0
    refine ⟨1, one_mem _, ⟨A 0 0, (A⁻¹ : GL (Fin 1) D) 0 0, h00, h00'⟩, ?_⟩
    ext i j; fin_cases i; fin_cases j; simp [Fin.last]
  | k + 1, A => by
    obtain ⟨e₁, he₁, h1⟩ := exists_mem_elementarySubgroup_mul_apply_zero_zero_eq_one k A
    let sw : Fin 1 ⊕ Fin (k + 1) ≃ Fin (k + 2) :=
      finSumFinEquiv.trans (finCongr (Nat.one_add (k + 1)))
    have hsw_inl (i : Fin 1) : sw (Sum.inl i) = 0 := by fin_cases i; ext; simp [sw]
    have hsw_inr (i : Fin (k + 1)) : sw (Sum.inr i) = i.succ := by ext; simp [sw]
    let M : GL (Fin 1 ⊕ Fin (k + 1)) D := sw.symm.reindexGL D (e₁ * A)
    have hM11 : (M : Matrix (Fin 1 ⊕ Fin (k + 1)) (Fin 1 ⊕ Fin (k + 1)) D).toBlocks₁₁ = 1 := by
      ext i j; fin_cases i; fin_cases j; simpa [M, hsw_inl, Matrix.toBlocks₁₁] using h1
    obtain ⟨eM, heM, S, hM⟩ := exists_mem_elementarySubgroup_mul_fromBlocksGL M hM11
    obtain ⟨eS, heS, u, hS⟩ := exists_mem_elementarySubgroup_mul_lastDiag k S
    let e₂ : GL (Fin (k + 2)) D := sw.reindexGL D (eM * fromBlocksGL (1, eS))
    have he₂ : e₂ ∈ elementarySubgroup (Fin (k + 2)) D := by
      rw [← sw.map_reindexGL_elementarySubgroup]
      exact ⟨_, mul_mem heM (map_inr_elementarySubgroup_le_elementarySubgroup ⟨eS, heS, rfl⟩), rfl⟩
    have hdiag_sw : sw.reindexGL D (fromBlocksGL (1, diagGL (Pi.mulSingle (Fin.last k) u))) =
        diagGL (Pi.mulSingle (Fin.last (k + 1)) u) := by
      apply Units.ext; ext i j
      obtain ⟨i, rfl⟩ := sw.surjective i
      obtain ⟨j, rfl⟩ := sw.surjective j
      rw [Equiv.coe_reindexGL, coe_fromBlocksGL, Matrix.submatrix_apply,
        Equiv.symm_apply_apply, Equiv.symm_apply_apply]
      rcases i with i | i <;> rcases j with j | j
      · fin_cases i; fin_cases j; simp [hsw_inl, Fin.ext_iff]
      · simp [hsw_inl, hsw_inr, (Fin.succ_ne_zero j).symm]
      · simp [hsw_inl, hsw_inr]
      · simp [hsw_inr, Matrix.diagonal_apply, Pi.mulSingle_apply, Fin.ext_iff, Fin.val_last]
    have hM_decomp :
        M = (eM * fromBlocksGL (1, eS)) *
          fromBlocksGL (1, diagGL (Pi.mulSingle (Fin.last k) u)) := by
      rw [hM, hS, ← Prod.one_mk_mul_one_mk, map_mul, mul_assoc]
    refine ⟨e₁⁻¹ * e₂, mul_mem (inv_mem he₁) he₂, u, ?_⟩
    have he₁A : e₁ * A = e₂ * diagGL (Pi.mulSingle (Fin.last (k + 1)) u) := by
      simpa [M, map_mul, e₂, hdiag_sw] using congrArg (sw.reindexGL D) hM_decomp
    rw [mul_assoc, ← he₁A, inv_mul_cancel_left]

/-- **Gauss–Jordan factorization over a division ring.** Given any coordinate `i : n`, every
invertible matrix `g ∈ GL n D` factors as an elementary matrix times a diagonal matrix whose only
possibly non-identity diagonal entry sits at `i`. -/
theorem exists_mem_elementarySubgroup_mul_diagGL_mulSingle {n : Type*} [Fintype n] [DecidableEq n]
    (i : n) (g : GL n D) :
    ∃ e ∈ elementarySubgroup n D, ∃ u : Dˣ, g = e * diagGL (Pi.mulSingle i u) := by
  have hpos : 0 < Fintype.card n := Fintype.card_pos_iff.mpr ⟨i⟩
  obtain ⟨m, hm⟩ : ∃ m, Fintype.card n = m + 1 := Nat.exists_eq_succ_of_ne_zero hpos.ne'
  let e₀ : n ≃ Fin (m + 1) := Fintype.equivFinOfCardEq hm
  let eqv : n ≃ Fin (m + 1) := e₀.trans (Equiv.swap (e₀ i) (Fin.last m))
  have heqv_i : eqv i = Fin.last m := by simp [eqv]
  obtain ⟨e', he', u, hg'⟩ :=
    exists_mem_elementarySubgroup_mul_lastDiag m (eqv.reindexGL D g)
  refine ⟨eqv.symm.reindexGL D e', ?_, u, ?_⟩
  · rw [← eqv.symm.map_reindexGL_elementarySubgroup]; exact ⟨e', he', rfl⟩
  · have hdiag : eqv.symm.reindexGL D (diagGL (Pi.mulSingle (Fin.last m) u)) =
        diagGL (Pi.mulSingle i u) := by
      ext a b
      simp only [Equiv.coe_reindexGL, submatrix_apply, Equiv.symm_symm, diagGL_apply,
        eqv.apply_eq_iff_eq, Pi.mulSingle_apply, ← heqv_i]
    simpa [map_mul, hdiag] using congrArg (eqv.symm.reindexGL D) hg'

/-- Over a division ring, every invertible matrix factors as an elementary matrix times an
invertible diagonal matrix. -/
theorem exists_mem_elementarySubgroup_mul_diagGL {n : Type*} [Fintype n] [DecidableEq n]
    (g : GL n D) :
    ∃ e ∈ elementarySubgroup n D, ∃ d : n → Dˣ, g = e * diagGL d := by
  rcases isEmpty_or_nonempty n with hn | ⟨⟨i₀⟩⟩
  · exact ⟨1, one_mem _, 1, Subsingleton.elim _ _⟩
  · obtain ⟨e, he, u, rfl⟩ := exists_mem_elementarySubgroup_mul_diagGL_mulSingle i₀ g
    exact ⟨e, he, Pi.mulSingle i₀ u, rfl⟩

/-- **The elementary subgroup is normal over a division ring**, already at every finite matrix
size. -/
instance elementarySubgroup_normal {n : Type*} [Fintype n] [DecidableEq n] :
    (elementarySubgroup n D).Normal where
  conj_mem x hx g := by
    rcases isEmpty_or_nonempty n with hn | ⟨⟨i₀⟩⟩
    · exact Subsingleton.elim (g * x * g⁻¹) 1 ▸ one_mem _
    have hdiag_norm (d : n → Dˣ) {y : GL n D} (hy : y ∈ elementarySubgroup n D) :
        diagGL d * y * (diagGL d)⁻¹ ∈ elementarySubgroup n D := by
      have hle : elementarySubgroup n D ≤
          (elementarySubgroup n D).comap (MulAut.conj (diagGL d)).toMonoidHom := by
        refine elementarySubgroup_le_iff.2 fun i j hij c ↦ ?_
        rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
          diagGL_mul_transvectionUnit_mul_inv]
        exact transvectionUnit_mem_elementarySubgroup hij _
      exact hle hy
    obtain ⟨e, he, u, rfl⟩ := exists_mem_elementarySubgroup_mul_diagGL_mulSingle i₀ g
    have hrewrite : (e * diagGL (Pi.mulSingle i₀ u)) * x * (e * diagGL (Pi.mulSingle i₀ u))⁻¹ =
        e * (diagGL (Pi.mulSingle i₀ u) * x * (diagGL (Pi.mulSingle i₀ u))⁻¹) * e⁻¹ := by group
    rw [hrewrite]
    exact mul_mem (mul_mem he (hdiag_norm _ hx)) (inv_mem he)

end TauCeti

namespace Matrix.GeneralLinearGroup

/-- Two monoid homomorphisms out of `GL n D` that vanish on `TauCeti.elementarySubgroup n D` and
agree on the single-entry diagonal matrices at a chosen index `i : n` are equal. -/
theorem hom_ext_of_elementarySubgroup_le_ker {n : Type*} [Fintype n] [DecidableEq n]
    {D : Type*} [DivisionRing D] {G : Type*} [Monoid G] {φ ψ : GL n D →* G}
    (hφ : TauCeti.elementarySubgroup n D ≤ φ.ker)
    (hψ : TauCeti.elementarySubgroup n D ≤ ψ.ker) (i : n)
    (hdiag : ∀ u : Dˣ,
      φ (TauCeti.diagGL (Pi.mulSingle i u)) = ψ (TauCeti.diagGL (Pi.mulSingle i u))) :
    φ = ψ := by
  ext g
  obtain ⟨e, he, u, rfl⟩ := TauCeti.exists_mem_elementarySubgroup_mul_diagGL_mulSingle i g
  rw [map_mul, map_mul, hφ he, hψ he, one_mul, one_mul, hdiag]

end Matrix.GeneralLinearGroup

end

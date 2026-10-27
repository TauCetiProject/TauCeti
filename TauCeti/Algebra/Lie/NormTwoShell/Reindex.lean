/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.NormTwoShell.Basic
public import TauCeti.LinearAlgebra.Matrix.OrderedSignCover.Reindex
import TauCeti.LinearAlgebra.Matrix.DotProduct

/-!
# Relabelling the vertices of the signed shell Lie algebra

The bracket of `Matrix.ShellLieAlgebra B` uses the ordered sign `ε` of the Gram matrix
`B : Matrix I I ℤ`, which depends on the linear order of the vertex set `I`. Let `e : I ≃ J` be a
bijection onto a second linearly ordered finite set with `B.reindex e e = B'`, for instance a
change of the order of `I`, or a diagram automorphism (`J = I` and `B' = B`). The two ordered signs
differ by the coboundary of the inversion sign `σ` of `e` (`Matrix.inversionSign`), and the root
vectors are rescaled accordingly: the linear equivalence `Matrix.ShellLieAlgebra.reindex`,

`H_h ↦ H_(h ∘ e.symm)`, `x_a ↦ σ(a) x_(a ∘ e.symm)`,

from `ShellLieAlgebra B` to `ShellLieAlgebra B'` preserves the bracket as soon as `B` is symmetric
(`Matrix.ShellLieAlgebra.reindex_lie`). It is therefore an isomorphism of Lie rings for positive
definite `B` with even diagonal (`Matrix.ShellLieAlgebra.reindexLieEquiv`). Since a coordinate
vector has inversion sign `1`, it sends `x_(αᵢ)` and `x_(-αᵢ)` to `x_(α_(e i))` and
`x_(-α_(e i))` whenever these coordinate vectors lie in the shells. When `B` is a simply laced
Cartan matrix they do, and together with `H_(αᵢ) ↦ H_(α_(e i))` the relabelling sends the
Chevalley generators of `B` to those of `B'` at the vertex `e i`, so it respects the simple
positive pinning. The relabellings are functorial (`Matrix.ShellLieAlgebra.reindex_refl`,
`Matrix.ShellLieAlgebra.reindex_trans`).

## Main definitions

* `Matrix.ShellLieAlgebra.reindex`: the relabelling `H_h ↦ H_(h ∘ e.symm)`,
  `x_a ↦ σ(a) x_(a ∘ e.symm)`, as a linear equivalence.
* `Matrix.ShellLieAlgebra.reindexLieEquiv`: the same map as an equivalence of Lie algebras over
  `ℤ`, for positive definite `B` with even diagonal.

## Main results

* `Matrix.ShellLieAlgebra.reindex_cartan`, `Matrix.ShellLieAlgebra.reindex_root`: the values on
  Cartan and root vectors.
* `Matrix.ShellLieAlgebra.reindex_root_single`, `Matrix.ShellLieAlgebra.reindex_root_neg_single`:
  the relabelling preserves the simple root vectors.
* `Matrix.ShellLieAlgebra.reindex_rootBracket`: the relabelling of a root bracket.
* `Matrix.ShellLieAlgebra.reindex_lie`: the relabelling preserves the bracket, for symmetric `B`.
* `Matrix.ShellLieAlgebra.reindex_refl`, `Matrix.ShellLieAlgebra.reindex_trans`: functoriality.

## References

* V. G. Kac, *Infinite dimensional Lie algebras*, third edition, Cambridge University Press (1990),
  §7.8.
-/

public section

namespace Matrix.ShellLieAlgebra

open Module

variable {I J K : Type*} [Fintype I] [LinearOrder I] [Fintype J] [LinearOrder J] [Fintype K]
  [LinearOrder K] {B : Matrix I I ℤ} {B' : Matrix J J ℤ} (e : I ≃ J) (he : B.reindex e e = B')

/-- **Relabelling the signed shell Lie algebra.** For a relabelling `e : I ≃ J` of the vertices of
`B` with `B.reindex e e = B'`, the linear equivalence `ShellLieAlgebra B ≃ₗ[ℤ] ShellLieAlgebra B'`
sending the Cartan vector `H_h` to `H_(h ∘ e.symm)` and the root vector `x_a` to
`σ(a) x_(a ∘ e.symm)`, where `σ` is the inversion sign `Matrix.inversionSign B e`. It preserves the
bracket for symmetric `B` (`Matrix.ShellLieAlgebra.reindex_lie`). -/
noncomputable def reindex : ShellLieAlgebra B ≃ₗ[ℤ] ShellLieAlgebra B' :=
  (basis B).equiv ((basis B').unitsSMul
      (Sum.elim 1 fun b => inversionSign B e ((normTwoShellCongr he).symm b)))
    (e.sumCongr (normTwoShellCongr he))

/-- The relabelling rescales the root vector `x_a` by the inversion sign `σ(a)` and moves it to the
relabelled root: `x_a ↦ σ(a) x_(a ∘ e.symm)`. -/
@[simp]
theorem reindex_root (a : B.normTwoShell) :
    reindex e he (root B a) = inversionSign B e a • root B' (normTwoShellCongr he a) := by
  rw [← basis_inr, reindex, Basis.equiv_apply, Basis.unitsSMul_apply]
  simp [Function.comp_assoc]

/-- The relabelling sends the Cartan vector `H_h` to the relabelled Cartan vector
`H_(h ∘ e.symm)`, with no sign. -/
@[simp]
theorem reindex_cartan (h : I → ℤ) : reindex e he (cartan B h) = cartan B' (h ∘ e.symm) := by
  classical
  have key : (reindex e he).toLinearMap ∘ₗ cartan B =
      cartan B' ∘ₗ LinearMap.funLeft ℤ ℤ e.symm :=
    (Pi.basisFun ℤ I).ext fun i => by
      have hsingle : LinearMap.funLeft ℤ ℤ e.symm (Pi.single i 1) = Pi.single (e i) 1 := by
        ext j
        simp [LinearMap.funLeft_apply, Pi.single_apply, Equiv.symm_apply_eq]
      rw [Pi.basisFun_apply, LinearMap.comp_apply, LinearMap.comp_apply, hsingle, ← basis_inl,
        ← basis_inl, LinearEquiv.coe_coe, reindex, Basis.equiv_apply]
      simp [Basis.unitsSMul_apply]
  exact congr($key h)

/-- The relabelling sends the simple root vector `x_(αᵢ)` to `x_(α_(e i))`. -/
theorem reindex_root_single [DecidableEq I] [DecidableEq J] (i : I)
    (hi : Pi.single i 1 ∈ B.normTwoShell) (hi' : Pi.single (e i) 1 ∈ B'.normTwoShell) :
    reindex e he (root B ⟨Pi.single i 1, hi⟩) = root B' ⟨Pi.single (e i) 1, hi'⟩ := by
  rw [reindex_root, inversionSign_single, one_smul]
  congr 1
  exact Subtype.ext <| by rw [coe_normTwoShellCongr_apply, Pi.single_comp_equiv, Equiv.symm_symm]

/-- The relabelling sends the simple root vector `x_(-αᵢ)` to `x_(-α_(e i))`. -/
theorem reindex_root_neg_single [DecidableEq I] [DecidableEq J] (i : I)
    (hi : -Pi.single i 1 ∈ B.normTwoShell) (hi' : -Pi.single (e i) 1 ∈ B'.normTwoShell) :
    reindex e he (root B ⟨-Pi.single i 1, hi⟩) = root B' ⟨-Pi.single (e i) 1, hi'⟩ := by
  rw [reindex_root, inversionSign_neg, inversionSign_single, one_smul]
  congr 1
  exact Subtype.ext <| by
    rw [coe_normTwoShellCongr_apply, Pi.neg_comp, Pi.single_comp_equiv, Equiv.symm_symm]

/-- **The relabelling of a root bracket**, for symmetric `B`: the ordered signs of the two
labellings differ by the coboundary of the inversion sign `σ`, so
`⁅x_a, x_b⁆ ↦ σ(a) σ(b) ⁅x_(a ∘ e.symm), x_(b ∘ e.symm)⁆`. -/
theorem reindex_rootBracket (hB : B.IsSymm) (a b : B.normTwoShell) :
    reindex e he (rootBracket B a b) =
      (inversionSign B e a * inversionSign B e b) •
        rootBracket B' (normTwoShellCongr he a) (normTwoShellCongr he b) := by
  have hsum : (normTwoShellCongr he a : J → ℤ) + (normTwoShellCongr he b : J → ℤ) =
      ((a : I → ℤ) + (b : I → ℤ)) ∘ e.symm := by
    funext j
    simp
  have hmem : (normTwoShellCongr he a : J → ℤ) + normTwoShellCongr he b ∈ B'.normTwoShell ↔
      (a : I → ℤ) + b ∈ B.normTwoShell := by
    rw [hsum, ← he, comp_equiv_symm_mem_normTwoShell_reindex_iff]
  have key := negOnePow_orderedSignForm_mul_inversionSign_add B e hB a b
  rw [he] at key
  by_cases hm : (a : I → ℤ) + b ∈ B.normTwoShell
  · have hm' := hmem.2 hm
    have hroot : normTwoShellCongr he ⟨_, hm⟩ = ⟨_, hm'⟩ :=
      Subtype.ext <| by rw [coe_normTwoShellCongr_apply]; exact hsum.symm
    rw [rootBracket_of_mem hm, rootBracket_of_mem hm', map_zsmul_unit, reindex_root, hroot,
      smul_smul, smul_smul]
    congr 1
    rw [coe_normTwoShellCongr_apply, coe_normTwoShellCongr_apply,
      mul_comm _ (orderedSignForm _ _ _).negOnePow]
    exact key
  by_cases hz : (a : I → ℤ) + b = 0
  · have hz' : (normTwoShellCongr he a : J → ℤ) + normTwoShellCongr he b = 0 := by
      rw [hsum, hz, Pi.zero_comp]
    rw [hz, inversionSign_zero, mul_one] at key
    rw [rootBracket_of_add_eq_zero hz, rootBracket_of_add_eq_zero hz', map_zsmul_unit,
      reindex_cartan, smul_smul]
    simp only [coe_normTwoShellCongr_apply]
    rw [key, mul_comm]
  · have hz' : (normTwoShellCongr he a : J → ℤ) + normTwoShellCongr he b ≠ 0 := by
      rw [hsum]
      exact fun h => hz (by simpa [Function.comp_assoc] using congr($h ∘ e))
    rw [rootBracket_of_notMem_of_add_ne_zero hm hz,
      rootBracket_of_notMem_of_add_ne_zero (mt hmem.1 hm) hz', map_zero, smul_zero]

/-- **The relabelling preserves the bracket**, for symmetric `B`. -/
theorem reindex_lie (hB : B.IsSymm) (x y : ShellLieAlgebra B) :
    reindex e he ⁅x, y⁆ = ⁅reindex e he x, reindex e he y⁆ := by
  have hpair (h : I → ℤ) (b : B.normTwoShell) :
      h ∘ e.symm ⬝ᵥ B' *ᵥ (normTwoShellCongr he b : J → ℤ) = h ⬝ᵥ B *ᵥ (b : I → ℤ) := by
    rw [coe_normTwoShellCongr_apply, ← he, comp_equiv_symm_dotProduct_reindex_mulVec]
  have key : (bracketBilin B).compr₂ (reindex e he).toLinearMap =
      (bracketBilin B').compl₁₂ (reindex e he).toLinearMap (reindex e he).toLinearMap :=
    (basis B).ext fun i => (basis B).ext fun j => by
      classical
      simp only [LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, LinearEquiv.coe_coe,
        bracketBilin_apply_apply]
      rcases i with i | a <;> rcases j with j | b
      · simp
      · simp only [basis_inl, basis_inr, cartan_lie_root, map_zsmul, reindex_cartan, reindex_root,
          ShellLieAlgebra.lie_units_smul, hpair]
        exact smul_comm _ _ _
      · simp only [basis_inl, basis_inr, root_lie_cartan, map_neg, map_zsmul, reindex_cartan,
          reindex_root, ShellLieAlgebra.units_smul_lie, hpair, smul_neg]
        rw [smul_comm]
      · simp only [basis_inr, root_lie_root, reindex_root, ShellLieAlgebra.units_smul_lie,
          ShellLieAlgebra.lie_units_smul, reindex_rootBracket e he hB, smul_smul, mul_comm]
  simpa using congr($key x y)

/-- **The identity relabels the signed shell Lie algebra by the identity.** -/
@[simp]
theorem reindex_refl : reindex (Equiv.refl I) (B := B) (by simp) = LinearEquiv.refl ℤ _ := by
  refine (basis B).ext' fun k => ?_
  rcases k with i | a
  · classical
    simp
  · simp only [basis_inr, reindex_root, inversionSign_refl, one_smul, LinearEquiv.refl_apply]
    congr 1
    exact Subtype.ext (by simp)

/-- **Relabellings of the signed shell Lie algebra compose**, for symmetric `B`. -/
theorem reindex_trans {B'' : Matrix K K ℤ} (f : J ≃ K) (hB : B.IsSymm) (hf : B'.reindex f f = B'') :
    (reindex e he).trans (reindex f hf) =
      reindex (e.trans f) (by rw [← hf, ← he]; ext; simp) := by
  subst he hf
  refine (basis B).ext' fun k => ?_
  rcases k with i | a
  · classical
    rw [basis_inl, LinearEquiv.trans_apply, reindex_cartan, reindex_cartan, reindex_cartan]
    rfl
  · rw [basis_inr, LinearEquiv.trans_apply, reindex_root, map_zsmul_unit, reindex_root,
      reindex_root, smul_smul, coe_normTwoShellCongr_apply, inversionSign_trans B e hB f]
    congr 2
    apply Subtype.ext
    rw [coe_normTwoShellCongr_apply, coe_normTwoShellCongr_apply, coe_normTwoShellCongr_apply]
    rfl

/-- **Relabelling as an isomorphism of Lie algebras.** For positive definite `B` with even
diagonal, the relabelling `Matrix.ShellLieAlgebra.reindex` is an isomorphism of the signed Lie
rings of `B` and of `B' = B.reindex e e`, which is again positive definite with even diagonal. -/
noncomputable def reindexLieEquiv (hB : B.PosDef) (hdiag : ∀ i, Even (B i i)) :
    letI := lieRing hB hdiag
    letI := lieRing (B := B') (he ▸ hB.submatrix e.symm.injective) fun j => by
      simpa [← he] using hdiag (e.symm j)
    ShellLieAlgebra B ≃ₗ⁅ℤ⁆ ShellLieAlgebra B' :=
  letI := lieRing hB hdiag
  letI := lieRing (B := B') (he ▸ hB.submatrix e.symm.injective) fun j => by
    simpa [← he] using hdiag (e.symm j)
  { reindex e he with
    map_lie' := reindex_lie e he hB.isHermitian.isSymm _ _ }

@[simp]
theorem reindexLieEquiv_apply (hB : B.PosDef) (hdiag : ∀ i, Even (B i i))
    (x : ShellLieAlgebra B) : reindexLieEquiv e he hB hdiag x = reindex e he x :=
  (rfl)

end Matrix.ShellLieAlgebra

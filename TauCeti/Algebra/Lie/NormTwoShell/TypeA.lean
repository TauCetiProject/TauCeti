/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.NormTwoShell.Serre
public import TauCeti.Algebra.Lie.SpecialLinear.Root.Brackets
public import TauCeti.LinearAlgebra.Matrix.NormTwoShell.TypeA
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Classical

/-!
# The signed shell Lie algebra of type `A` is the special linear Lie algebra

Let `B = CartanMatrix.A r` be the Cartan matrix of type `A_r` with its vertices in the order of
`Fin r`. Its signed shell Lie algebra `Matrix.ShellLieAlgebra B`, the Frenkel--Kac Lie algebra over
`ℤ` with Cartan vectors `H_h` for `h : Fin r → ℤ` and root vectors `x_a` indexed by the roots
`a = ε_p - ε_q` (`TauCeti.typeANormTwoShellEquiv`), is isomorphic over `ℤ` to the trace-zero
matrices `sl (Fin (r + 1)) ℤ` by the signed matrix comparison

```text
H_(αₖ) ↦ E_(k,k) - E_(k+1,k+1),
x_(ε_p - ε_q) ↦ E_(p,q)                         if p < q,
x_(ε_p - ε_q) ↦ (-1) ^ (p - q - 1) E_(p,q)      if q < p.
```

So the interval root `α_i + ⋯ + α_j` of height `l` goes to `E_(i,j+1)` and its negative to
`(-1) ^ (l - 1) E_(j+1,i)`. The images are the integral basis
`TauCeti.specialLinearRootBasis` of adjacent coroots and signed matrix units, whose signs are
`TauCeti.specialLinearRootSign`, so the map is a linear equivalence by construction
(`TauCeti.typeAShellEquiv`); the content is that it preserves the bracket
(`TauCeti.typeAShellEquiv_lie`), which makes it an isomorphism of Lie algebras over `ℤ`
(`TauCeti.typeAShellLieEquiv`).

The negative root vectors of the shell algebra are section vectors, not inverse lifts in the
ordered sign cover, which is why negative roots carry the height-dependent sign. Already for `A₂`
the ordered sign `ε(α₁ + α₂, -α₁ - α₂)` is `-1`, so `x_(α₁+α₂) ↦ E₁₃` while
`x_(-α₁-α₂) ↦ -E₃₁`.

The proof compares brackets on basis vectors. The Cartan vector `H_h` goes to the diagonal
matrix with entries `D h`, where `D` is `TauCeti.typeASimpleRootMatrix r`, and the pairing
`⟪h, ε_p - ε_q⟫` is `(D h)_p - (D h)_q`, the eigenvalue of `ad (diagonal (D h))` on `E_(p,q)`.
For two root vectors the matrix bracket `⁅E_(p,q), E_(s,t)⁆` is nonzero only when `q = s` or
`t = p`, matching the cases `a + b ∈ Φ` and `a + b = 0` of the shell bracket. The remaining check
compares the ordered sign `ε(a, b)` with the signs `σ` of the signed matrix units involved: for a
chain `ε_p - ε_q`, `ε_q - ε_t` it is `σ(p,q) σ(q,t) σ(p,t)`, for a reversed chain `ε_p - ε_q`,
`ε_s - ε_p` it is `-σ(p,q) σ(s,p) σ(s,q)`, and for opposite roots `ε_p - ε_q`, `ε_q - ε_p` it is
`σ(p,q) σ(q,p)`. These are parity identities, proved from the closed form
`TauCeti.orderedSignForm_cartanMatrix_A_typeAPairRoot` of the ordered form on two roots.

## Main definitions

* `TauCeti.typeAShellEquiv`: the signed matrix comparison, as a linear equivalence.
* `TauCeti.typeAShellLieEquiv`: the same map, as an isomorphism of Lie algebras over `ℤ`.

## Main results

* `TauCeti.typeAShellEquiv_cartan`, `TauCeti.typeAShellEquiv_root_typeAPairRoot`: its values on
  Cartan and root vectors.
* `TauCeti.typeAShellEquiv_symm_specialLinearSignedRoot`: the inverse on signed matrix units.
* `TauCeti.typeAShellEquiv_chevalleyE`, `TauCeti.typeAShellEquiv_chevalleyF`: the Chevalley
  generators go to `E_(k,k+1)` and `E_(k+1,k)`.
* `TauCeti.typeAShellEquiv_lie`: the comparison preserves the bracket.

## References

* I. B. Frenkel and V. G. Kac, *Basic representations of affine Lie algebras and dual resonance
  models*, Invent. Math. **62** (1980), 23--66.
* V. G. Kac, *Infinite dimensional Lie algebras*, third edition, Cambridge University Press (1990),
  §7.8.
-/

public section

namespace TauCeti

open _root_.Matrix LieAlgebra.SpecialLinear Matrix.ShellLieAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable (r : ℕ)

/-- **The signed matrix comparison** from the signed shell Lie algebra of `CartanMatrix.A r` to
the trace-zero matrices: `H_(αₖ) ↦ E_(k,k) - E_(k+1,k+1)` and `x_(ε_p - ε_q) ↦ ± E_(p,q)`, with
the sign `TauCeti.specialLinearRootSign` of the pair `(p, q)`. -/
noncomputable def typeAShellEquiv :
    ShellLieAlgebra (CartanMatrix.A r) ≃ₗ[ℤ] sl (Fin (r + 1)) ℤ :=
  (ShellLieAlgebra.basis _).equiv (specialLinearRootBasis r ℤ)
    (Equiv.sumCongr (Equiv.refl _) (typeANormTwoShellEquiv r).symm)

/-- The Cartan vector of a simple root goes to the corresponding adjacent diagonal difference. -/
@[simp]
theorem typeAShellEquiv_cartan_single (k : Fin r) :
    typeAShellEquiv r (cartan _ (Pi.single k 1)) = (specialLinearCorootBasis r ℤ k).val := by
  rw [← basis_inl, typeAShellEquiv, Module.Basis.equiv_apply, Equiv.sumCongr_apply, Sum.map_inl,
    Equiv.refl_apply, specialLinearRootBasis_inl]

/-- The root vector of a root goes to the signed matrix unit of its pair of indices. -/
theorem typeAShellEquiv_root (a : (CartanMatrix.A r).normTwoShell) :
    typeAShellEquiv r (root _ a) =
      specialLinearSignedRoot r ℤ _ _ ((typeANormTwoShellEquiv r).symm a).2 := by
  rw [← basis_inr, typeAShellEquiv, Module.Basis.equiv_apply, Equiv.sumCongr_apply, Sum.map_inr,
    specialLinearRootBasis_inr]

/-- **The root vector of `ε_p - ε_q` goes to the signed matrix unit `± E_(p,q)`.** -/
@[simp]
theorem typeAShellEquiv_root_typeAPairRoot {p q : Fin (r + 1)} (hpq : p ≠ q) :
    typeAShellEquiv r (root _ ⟨typeAPairRoot r p q, typeAPairRoot_mem_normTwoShell r hpq⟩) =
      specialLinearSignedRoot r ℤ p q hpq := by
  rw [← typeANormTwoShellEquiv_mk r hpq, ← basis_inr, typeAShellEquiv, Module.Basis.equiv_apply,
    Equiv.sumCongr_apply, Sum.map_inr, Equiv.symm_apply_apply, specialLinearRootBasis_inr]

/-- **The inverse comparison on signed matrix units.** -/
@[simp]
theorem typeAShellEquiv_symm_specialLinearSignedRoot {p q : Fin (r + 1)} (hpq : p ≠ q) :
    (typeAShellEquiv r).symm (specialLinearSignedRoot r ℤ p q hpq) =
      root _ ⟨typeAPairRoot r p q, typeAPairRoot_mem_normTwoShell r hpq⟩ := by
  rw [LinearEquiv.symm_apply_eq, typeAShellEquiv_root_typeAPairRoot]

/-- **The Cartan vector `H_h` goes to the trace-zero diagonal matrix with simple-coroot
coordinates `h`.** -/
theorem typeAShellEquiv_cartan (h : Fin r → ℤ) :
    typeAShellEquiv r (cartan _ h) = ((specialLinearCorootEquiv r ℤ).symm h).val := by
  have key : (typeAShellEquiv r).toLinearMap ∘ₗ cartan (CartanMatrix.A r) =
      (specialLinearDiagonal r ℤ).subtype ∘ₗ (specialLinearCorootEquiv r ℤ).symm.toLinearMap :=
    (Pi.basisFun ℤ (Fin r)).ext fun k ↦ by
      have hk : (specialLinearCorootEquiv r ℤ).symm (Pi.single k 1) =
          specialLinearCorootBasis r ℤ k := by
        rw [LinearEquiv.symm_apply_eq]
        ext j
        simp only [specialLinearCorootEquiv_apply, ← specialLinearCorootBasis_repr,
          Module.Basis.repr_self, Finsupp.single_apply, Pi.single_apply, eq_comm]
      simp [hk]
  exact congr($key h)

/-- The matrix of the image of `H_h` is the diagonal matrix of the classical coordinates `D h`. -/
theorem coe_typeAShellEquiv_cartan (h : Fin r → ℤ) :
    (typeAShellEquiv r (cartan _ h) : Matrix (Fin (r + 1)) (Fin (r + 1)) ℤ) =
      diagonal (typeASimpleRootMatrix r *ᵥ h) := by
  have key : (sl (Fin (r + 1)) ℤ).toSubmodule.subtype ∘ₗ (typeAShellEquiv r).toLinearMap ∘ₗ
      cartan (CartanMatrix.A r) =
        diagonalLinearMap (Fin (r + 1)) ℤ ℤ ∘ₗ (typeASimpleRootMatrix r).mulVecLin :=
    (Pi.basisFun ℤ (Fin r)).ext fun k ↦ by
      have hcol : typeASimpleRootMatrix r *ᵥ Pi.single k 1 =
          Pi.single k.castSucc 1 - Pi.single k.succ 1 := by
        rw [← typeAPairRoot_castSucc_succ, typeASimpleRootMatrix_mulVec_typeAPairRoot]
      simp only [LinearMap.comp_apply, Pi.basisFun_apply, LinearEquiv.coe_coe,
        typeAShellEquiv_cartan_single, Submodule.subtype_apply, specialLinearCorootBasis_apply,
        val_singleSubSingle, diagonalLinearMap_apply, mulVecLin_apply, hcol]
      rw [← diagonal_single k.castSucc (1 : ℤ), ← diagonal_single k.succ (1 : ℤ)]
      exact diagonal_sub _ _
  exact congr($key h)

/-- The Cartan vector of a root `ε_p - ε_q` goes to `E_(p,p) - E_(q,q)`. -/
theorem typeAShellEquiv_cartan_typeAPairRoot (p q : Fin (r + 1)) :
    typeAShellEquiv r (cartan _ (typeAPairRoot r p q)) = singleSubSingle p q 1 := by
  apply Subtype.ext
  rw [coe_typeAShellEquiv_cartan, typeASimpleRootMatrix_mulVec_typeAPairRoot, val_singleSubSingle,
    ← diagonal_single, ← diagonal_single]
  exact (diagonal_sub _ _).symm

/-- The raising Chevalley generator `Eₖ` goes to the matrix unit `E_(k,k+1)`. -/
@[simp]
theorem typeAShellEquiv_chevalleyE (k : Fin r) :
    typeAShellEquiv r (chevalleyE _ (fun _ ↦ by simp [CartanMatrix.A]) k) =
      single k.castSucc k.succ (Fin.castSucc_lt_succ (i := k)).ne 1 := by
  have hE : chevalleyE (CartanMatrix.A r) (fun _ ↦ by simp [CartanMatrix.A]) k =
      root _ ⟨typeAPairRoot r k.castSucc k.succ,
        typeAPairRoot_mem_normTwoShell r (Fin.castSucc_lt_succ (i := k)).ne⟩ := by
    rw [chevalleyE_def]
    congr 1
    exact Subtype.ext (typeAPairRoot_castSucc_succ r k).symm
  rw [hE, typeAShellEquiv_root_typeAPairRoot r (Fin.castSucc_lt_succ (i := k)).ne]
  apply Subtype.ext
  simp

/-- The lowering Chevalley generator `Fₖ` goes to the matrix unit `E_(k+1,k)`. -/
@[simp]
theorem typeAShellEquiv_chevalleyF (k : Fin r) :
    typeAShellEquiv r (chevalleyF _ (fun _ ↦ by simp [CartanMatrix.A]) k) =
      single k.succ k.castSucc (Fin.castSucc_lt_succ (i := k)).ne' 1 := by
  have hF : chevalleyF (CartanMatrix.A r) (fun _ ↦ by simp [CartanMatrix.A]) k =
      root _ ⟨typeAPairRoot r k.succ k.castSucc,
        typeAPairRoot_mem_normTwoShell r (Fin.castSucc_lt_succ (i := k)).ne'⟩ := by
    rw [chevalleyF_def]
    congr 1
    exact Subtype.ext ((typeAPairRoot_swap r _ _).trans
      (congrArg Neg.neg (typeAPairRoot_castSucc_succ r k))).symm
  rw [hF, typeAShellEquiv_root_typeAPairRoot r (Fin.castSucc_lt_succ (i := k)).ne']
  apply Subtype.ext
  simp

/-! ### The bracket -/

/-- **The ordered sign along a chain of two roots** `ε_p - ε_q` and `ε_q - ε_t` is the product of
the signs of the three signed matrix units involved. -/
private theorem negOnePow_orderedSignForm_middle {p q t : Fin (r + 1)} (hpq : p ≠ q)
    (hqt : q ≠ t) (hpt : p ≠ t) :
    ((orderedSignForm (CartanMatrix.A r) (typeAPairRoot r p q) (typeAPairRoot r q t)).negOnePow :
        ℤ) =
      specialLinearRootSign r ℤ p q * specialLinearRootSign r ℤ q t *
        specialLinearRootSign r ℤ p t := by
  have := Fin.val_injective.ne hpq
  have := Fin.val_injective.ne hqt
  have := Fin.val_injective.ne hpt
  simp only [specialLinearRootSign_eq_negOnePow, ← Units.val_mul, ← Int.negOnePow_add,
    orderedSignForm_cartanMatrix_A_typeAPairRoot]
  congr 1
  rw [Int.negOnePow_eq_iff, Int.even_iff]
  simp only [Fin.lt_def]
  split_ifs <;> omega

/-- **The ordered sign along a reversed chain of two roots** `ε_p - ε_q` and `ε_s - ε_p` is the
negative of the product of the signs of the three signed matrix units involved. -/
private theorem negOnePow_orderedSignForm_outer {p q s : Fin (r + 1)} (hpq : p ≠ q)
    (hsp : s ≠ p) (hsq : s ≠ q) :
    ((orderedSignForm (CartanMatrix.A r) (typeAPairRoot r p q) (typeAPairRoot r s p)).negOnePow :
        ℤ) =
      -(specialLinearRootSign r ℤ p q * specialLinearRootSign r ℤ s p *
        specialLinearRootSign r ℤ s q) := by
  have := Fin.val_injective.ne hpq
  have := Fin.val_injective.ne hsp
  have := Fin.val_injective.ne hsq
  simp only [specialLinearRootSign_eq_negOnePow, ← Units.val_mul, ← Int.negOnePow_add,
    orderedSignForm_cartanMatrix_A_typeAPairRoot, ← Units.val_neg, ← Int.negOnePow_succ]
  congr 1
  rw [Int.negOnePow_eq_iff, Int.even_iff]
  simp only [Fin.lt_def]
  split_ifs <;> omega

/-- **The ordered sign of two opposite roots** `ε_p - ε_q` and `ε_q - ε_p` is the product of the
signs of the two signed matrix units involved. -/
private theorem negOnePow_orderedSignForm_opposite {p q : Fin (r + 1)} (hpq : p ≠ q) :
    ((orderedSignForm (CartanMatrix.A r) (typeAPairRoot r p q) (typeAPairRoot r q p)).negOnePow :
        ℤ) =
      specialLinearRootSign r ℤ p q * specialLinearRootSign r ℤ q p := by
  have := Fin.val_injective.ne hpq
  simp only [specialLinearRootSign_eq_negOnePow, ← Units.val_mul, ← Int.negOnePow_add,
    orderedSignForm_cartanMatrix_A_typeAPairRoot]
  congr 1
  rw [Int.negOnePow_eq_iff, Int.even_iff]
  simp only [Fin.lt_def]
  split_ifs <;> omega

/-- The comparison carries `⁅H_h, x_b⁆` to the bracket of the images. -/
private theorem typeAShellEquiv_cartan_lie_root (h : Fin r → ℤ)
    (b : (CartanMatrix.A r).normTwoShell) :
    typeAShellEquiv r ⁅cartan (CartanMatrix.A r) h, root (CartanMatrix.A r) b⁆ =
      ⁅typeAShellEquiv r (cartan _ h), typeAShellEquiv r (root _ b)⁆ := by
  obtain ⟨⟨⟨p, q⟩, hpq⟩, rfl⟩ := (typeANormTwoShellEquiv r).surjective b
  simp only at hpq
  rw [typeANormTwoShellEquiv_mk r hpq, cartan_lie_root, map_zsmul,
    typeAShellEquiv_root_typeAPairRoot r hpq]
  apply Subtype.ext
  rw [LieSubalgebra.coe_bracket, SetLike.val_smul, specialLinearSignedRoot_val,
    lie_single_of_mem_diagonalCartan (mem_diagonalCartan_iff_isDiag.mpr (by
      rw [coe_typeAShellEquiv_cartan]; exact isDiag_diagonal _)), coe_typeAShellEquiv_cartan,
    diagonal_apply_eq, diagonal_apply_eq, dotProduct_cartanMatrix_A_mulVec,
    typeASimpleRootMatrix_mulVec_typeAPairRoot]
  simp [dotProduct_sub]

/-- The comparison carries the bracket of two root vectors to the bracket of the images. -/
private theorem typeAShellEquiv_root_lie_root (a b : (CartanMatrix.A r).normTwoShell) :
    typeAShellEquiv r ⁅root (CartanMatrix.A r) a, root (CartanMatrix.A r) b⁆ =
      ⁅typeAShellEquiv r (root _ a), typeAShellEquiv r (root _ b)⁆ := by
  obtain ⟨⟨⟨p, q⟩, hpq⟩, rfl⟩ := (typeANormTwoShellEquiv r).surjective a
  obtain ⟨⟨⟨s, t⟩, hst⟩, rfl⟩ := (typeANormTwoShellEquiv r).surjective b
  simp only at hpq hst
  rw [typeANormTwoShellEquiv_mk r hpq, typeANormTwoShellEquiv_mk r hst, root_lie_root,
    typeAShellEquiv_root_typeAPairRoot r hpq, typeAShellEquiv_root_typeAPairRoot r hst]
  by_cases hqs : q = s
  · subst hqs
    by_cases htp : t = p
    · -- Opposite roots: the bracket is `ε(a, -a) H_a`.
      subst htp
      rw [rootBracket_of_add_eq_zero (by dsimp only; rw [typeAPairRoot_swap, neg_add_cancel]),
        Units.smul_def, map_zsmul, typeAShellEquiv_cartan_typeAPairRoot,
        lie_specialLinearSignedRoot_reverse, negOnePow_orderedSignForm_opposite r hpq]
    · -- A chain `ε_p - ε_q`, `ε_q - ε_t`: the bracket is `ε(a, b) x_(ε_p - ε_t)`.
      have hpt : p ≠ t := Ne.symm htp
      rw [rootBracket_of_mem (by
          dsimp only
          rw [typeAPairRoot_add_typeAPairRoot]
          exact typeAPairRoot_mem_normTwoShell r hpt),
        Units.smul_def, map_zsmul]
      simp only [typeAPairRoot_add_typeAPairRoot]
      rw [typeAShellEquiv_root_typeAPairRoot r hpt,
        lie_specialLinearSignedRoot_of_middle_eq _ _ p q t hpq hst hpt,
        negOnePow_orderedSignForm_middle r hpq hst hpt]
  · by_cases htp : t = p
    · -- A reversed chain `ε_p - ε_q`, `ε_s - ε_p`: the bracket is `ε(a, b) x_(ε_s - ε_q)`.
      subst htp
      have hsq : s ≠ q := Ne.symm hqs
      rw [rootBracket_of_mem (by
          dsimp only
          rw [add_comm, typeAPairRoot_add_typeAPairRoot]
          exact typeAPairRoot_mem_normTwoShell r hsq),
        Units.smul_def, map_zsmul]
      simp only [add_comm (typeAPairRoot r t q), typeAPairRoot_add_typeAPairRoot]
      rw [typeAShellEquiv_root_typeAPairRoot r hsq,
        lie_specialLinearSignedRoot_of_outer_eq _ _ t q s hpq hst hsq,
        negOnePow_orderedSignForm_outer r hpq hst hsq]
    · -- Neither endpoint matches: the roots pair to `[p = s] + [q = t] ≥ 0`.
      rw [rootBracket_eq_zero_of_nonneg (CartanMatrix.A_isSymm r) (by
          dsimp only
          simp only [typeAPairRoot_dotProduct_cartanMatrix_A_mulVec, hqs, Ne.symm htp, ↓reduceIte]
          split_ifs <;> norm_num),
        map_zero, lie_specialLinearSignedRoot_eq_zero _ _ p q s t hpq hst hqs htp]

/-- **The signed matrix comparison preserves the bracket.** -/
theorem typeAShellEquiv_lie (x y : ShellLieAlgebra (CartanMatrix.A r)) :
    typeAShellEquiv r ⁅x, y⁆ = ⁅typeAShellEquiv r x, typeAShellEquiv r y⁆ := by
  have key : (bracketBilin (CartanMatrix.A r)).compr₂ (typeAShellEquiv r).toLinearMap =
      (LieAlgebra.ad ℤ (sl (Fin (r + 1)) ℤ)).toLinearMap.compl₁₂ (typeAShellEquiv r).toLinearMap
        (typeAShellEquiv r).toLinearMap := by
    refine (ShellLieAlgebra.basis _).ext fun i ↦ (ShellLieAlgebra.basis _).ext fun j ↦ ?_
    simp only [LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, bracketBilin_apply_apply,
      LieHom.coe_toLinearMap, LieAlgebra.ad_apply, LinearEquiv.coe_coe]
    rcases i with i | a <;> rcases j with j | b
    · simp only [basis_inl, cartan_lie_cartan, map_zero, typeAShellEquiv_cartan_single]
      exact (lie_specialLinearCoroot_eq_zero r ℤ i j).symm
    · simp only [basis_inl, basis_inr]
      exact typeAShellEquiv_cartan_lie_root r _ b
    · simp only [basis_inl, basis_inr]
      rw [← lie_skew, root_lie_cartan, ← cartan_lie_root, map_neg, typeAShellEquiv_cartan_lie_root]
    · simp only [basis_inr]
      exact typeAShellEquiv_root_lie_root r a b
  exact congr($key x y)

/-- **The signed shell Lie algebra of type `A_r` is isomorphic over `ℤ` to `sl_(r+1)`**, by the
signed matrix comparison `TauCeti.typeAShellEquiv`. -/
noncomputable def typeAShellLieEquiv :
    letI := ShellLieAlgebra.lieRing (posDef_cartanMatrix_A r) fun _ ↦ by simp [CartanMatrix.A]
    ShellLieAlgebra (CartanMatrix.A r) ≃ₗ⁅ℤ⁆ sl (Fin (r + 1)) ℤ :=
  letI := ShellLieAlgebra.lieRing (posDef_cartanMatrix_A r) fun _ ↦ by simp [CartanMatrix.A]
  { typeAShellEquiv r with map_lie' := typeAShellEquiv_lie r _ _ }

@[simp]
theorem typeAShellLieEquiv_apply (x : ShellLieAlgebra (CartanMatrix.A r)) :
    typeAShellLieEquiv r x = typeAShellEquiv r x :=
  (rfl)

end TauCeti

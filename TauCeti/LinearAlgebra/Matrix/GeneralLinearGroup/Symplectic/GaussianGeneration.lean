/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Levi
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.UnipotentGeneration
import TauCeti.LinearAlgebra.Matrix.Pivot

/-!
# Block Gaussian decomposition in the symplectic group

Over any commutative ring `R`, a symplectic matrix `[A B; C D]` whose upper-left block `A` is
invertible factors on this open cell by block Gaussian elimination as

```text
[A B; C D] = [1 0; C A⁻¹ 1] [A 0; 0 A⁻ᵀ] [1 A⁻¹B; 0 1].
```

The two off-diagonal blocks `C A⁻¹` and `A⁻¹B` are symmetric by the symplectic equations, so the
outer factors are symmetric unipotents and the middle factor is a general-linear Levi element.
Consequently a subgroup containing the symmetric unipotents and the general-linear Levi subgroup
contains every symplectic matrix on the open cell.

Over a field, every symplectic matrix can be moved onto the open cell: the symmetric pivot of
`TauCeti.LinearAlgebra.Matrix.Pivot` gives a symmetric `X` such that `[1 X; 0 1] g` has an
invertible upper-left block. The field-level generation theorems combine these two steps in
`TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.TorusGeneration`.

## Main results

* `TauCeti.GLSymplecticFin.exists_gaussian_decomposition_of_isUnit_toBlocks₁₁` is the block
  Gaussian decomposition on the open cell where the upper-left block is invertible.
* `TauCeti.GLSymplecticFin.mem_of_isUnit_toBlocks₁₁`: a subgroup containing the symmetric
  unipotents and the general-linear Levi subgroup contains every symplectic matrix whose
  upper-left block is invertible.
* `TauCeti.GLSymplecticFin.exists_isSymm_isUnit_toBlocks₁₁_upperUnipotent_mul`: over a field, an
  upper symmetric unipotent moves every symplectic matrix onto the open cell where the upper-left
  block is invertible.

The generation theorems themselves, `TauCeti.GLSymplecticFin.eq_top_of_root_subgroups` and
`TauCeti.GLSymplecticFin.eq_top_of_adjacent_of_long`, are in
`TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.TorusGeneration`, which also shows
that any subgroup containing the opposite long-root subgroups contains the diagonal Levi subgroup.

## References

* R. W. Carter, *Simple Groups of Lie Type* (1972), §5.2.
* R. Steinberg, *Lectures on Chevalley Groups* (1968), §§3--4.
-/

public section

open Matrix

namespace TauCeti.GLSymplecticFin

universe u

variable {m : ℕ}

/-- A symplectic matrix whose upper-left block is invertible factors as a lower symmetric
unipotent, a general-linear Levi element, and an upper symmetric unipotent. -/
theorem exists_gaussian_decomposition_of_isUnit_toBlocks₁₁
    {R : Type u} [CommRing R]
    (g : GLSymplecticFin m R)
    (hunit : IsUnit (((mulEquivGLSymplectic m R g : GLSymplectic (Fin m) R) :
      GL (Fin m ⊕ Fin m) R) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) R).toBlocks₁₁) :
    ∃ (S T : Matrix (Fin m) (Fin m) R) (P : GL (Fin m) R)
      (hS : S.IsSymm) (hT : T.IsSymm),
        g = lowerUnipotent S hS * leviHom P * upperUnipotent T hT := by
  let M : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) R :=
    ((mulEquivGLSymplectic m R g : GLSymplectic (Fin m) R) : GL (Fin m ⊕ Fin m) R)
  let A := M.toBlocks₁₁
  let B := M.toBlocks₁₂
  let C := M.toBlocks₂₁
  let D := M.toBlocks₂₂
  have hM : M ∈ Matrix.symplecticGroup (Fin m) R := by
    simpa only [M] using GLSymplectic.mem_iff_mem_symplecticGroup.mp
      (mulEquivGLSymplectic m R g).property
  have hMblocks : Matrix.fromBlocks A B C D = M := by
    simpa only [A, B, C, D] using M.fromBlocks_toBlocks
  let P : GL (Fin m) R := Matrix.GeneralLinearGroup.mk'' A
    ((Matrix.isUnit_iff_isUnit_det A).mp hunit)
  set Ainv : Matrix (Fin m) (Fin m) R :=
    ((P⁻¹ : GL (Fin m) R) : Matrix (Fin m) (Fin m) R) with Ainv_def
  have hP : (P : Matrix (Fin m) (Fin m) R) = A := by simp [P]
  have hleft : Ainv * A = 1 := by rw [← hP, Ainv_def]; exact_mod_cast P.inv_mul
  have hright : A * Ainv = 1 := by rw [← hP, Ainv_def]; exact_mod_cast P.mul_inv
  obtain ⟨hS, hT, hD⟩ := SymplecticGroup.symm_and_toBlocks₂₂_of_mem_symplecticGroup hM hright
  set S := C * Ainv with S_def
  set T := Ainv * B with T_def
  replace hS : S.IsSymm := hS
  replace hT : T.IsSymm := hT
  replace hD : D = S * A * T + Ainvᵀ := hD
  have hAT : A * T = B := by rw [T_def, ← mul_assoc, hright, one_mul]
  have hSA : S * A = C := by rw [S_def, mul_assoc, hleft, mul_one]
  have hfactor : g = lowerUnipotent S hS * leviHom P * upperUnipotent T hT := by
    apply (mulEquivGLSymplectic m R).injective
    rw [map_mul, map_mul, mulEquivGLSymplectic_leviHom]
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    apply Units.ext
    -- Here `M` is the local abbreviation for exactly the coerced matrix on the left; this
    -- change only exposes that abbreviation and does not unfold a group or matrix wrapper.
    change M = _
    simp only [Matrix.GeneralLinearGroup.coe_mul, coe_mulEquivGLSymplectic,
      coe_mulEquivGLSymplectic_lowerUnipotent,
      coe_mulEquivGLSymplectic_upperUnipotent, GLSymplectic.coe_ofSymplecticGroup,
      GLSymplectic.coe_leviHom]
    rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp only [Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, Matrix.one_mul,
      add_zero, zero_add, hP]
    rw [← hMblocks]
    ext i j
    cases i <;> cases j <;> simp [hAT, hSA, hD, Ainv_def]
  exact ⟨S, T, P, hS, hT, hfactor⟩

/-- A symplectic matrix whose upper-left block is invertible belongs to every subgroup containing
all upper and lower symmetric unipotents and the general-linear Levi subgroup. -/
theorem mem_of_isUnit_toBlocks₁₁
    {R : Type u} [CommRing R]
    (H : Subgroup (GLSymplecticFin m R))
    (hupper : ∀ (B : Matrix (Fin m) (Fin m) R) (hB : B.IsSymm), upperUnipotent B hB ∈ H)
    (hlower : ∀ (C : Matrix (Fin m) (Fin m) R) (hC : C.IsSymm), lowerUnipotent C hC ∈ H)
    (hlevi : ∀ A : GL (Fin m) R, leviHom A ∈ H)
    (g : GLSymplecticFin m R)
    (hunit : IsUnit (((mulEquivGLSymplectic m R g : GLSymplectic (Fin m) R) :
      GL (Fin m ⊕ Fin m) R) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) R).toBlocks₁₁) :
    g ∈ H := by
  obtain ⟨S, T, P, hS, hT, hfactor⟩ :=
    exists_gaussian_decomposition_of_isUnit_toBlocks₁₁ g hunit
  rw [hfactor]
  exact H.mul_mem (H.mul_mem (hlower S hS) (hlevi P)) (hupper T hT)

section Field

variable {K : Type u} [Field K]

/-- **An upper symmetric unipotent moves every symplectic matrix over a field onto the open
cell**: for every `g` there is a symmetric `X` such that the upper-left block of `[1 X; 0 1] g` is
invertible. -/
theorem exists_isSymm_isUnit_toBlocks₁₁_upperUnipotent_mul (g : GLSymplecticFin m K) :
    ∃ (X : Matrix (Fin m) (Fin m) K) (hX : X.IsSymm),
      IsUnit (((mulEquivGLSymplectic m K (upperUnipotent X hX * g) : GLSymplectic (Fin m) K) :
        GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K).toBlocks₁₁ := by
  let M : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K :=
    ((mulEquivGLSymplectic m K g : GLSymplectic (Fin m) K) : GL (Fin m ⊕ Fin m) K)
  let A := M.toBlocks₁₁
  let C := M.toBlocks₂₁
  have hM : M ∈ Matrix.symplecticGroup (Fin m) K := by
    simpa only [M] using GLSymplectic.mem_iff_mem_symplecticGroup.mp
      (mulEquivGLSymplectic m K g).property
  have hker (x : Fin m → K) (hAx : A *ᵥ x = 0) (hCx : C *ᵥ x = 0) : x = 0 := by
    have hv : M *ᵥ Sum.elim x 0 = M *ᵥ Sum.elim 0 0 := by
      rw [← M.fromBlocks_toBlocks]
      simp [Matrix.fromBlocks_mulVec, A, C, hAx, hCx]
    exact (Sum.elim_eq_iff.mp
      (Matrix.mulVec_injective_iff_isUnit.mpr
        (((mulEquivGLSymplectic m K g : GLSymplectic (Fin m) K) :
          GL (Fin m ⊕ Fin m) K).isUnit) hv)).1
  have hcomm : Aᵀ * C = Cᵀ * A :=
    ((SymplecticGroup.fromBlocks_mem_iff).mp (M.fromBlocks_toBlocks ▸ hM)).1
  obtain ⟨X, hX, hunit⟩ :=
    exists_isSymm_isUnit_add_mul_of_ker_inter_eq_bot_of_transpose_mul_comm hker hcomm
  -- Left multiplication by `[1 X; 0 1]` changes the leading block to `A + XC`.
  refine ⟨X, hX, ?_⟩
  rw [toBlocks₁₁_upperUnipotent_mul]
  exact hunit

end Field

end TauCeti.GLSymplecticFin

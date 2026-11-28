/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.CMField.AdelicLattice
import TauCeti.LinearAlgebra.Matrix.GeneratorChange

/-!
# Gram data for the genus of a definite Hermitian lattice

The Gram matrix of a rational basis determines the Hermitian isometry carrying that
basis to another. The integral lattice is then recovered from its generators modulo the
integral span of that basis. The data can be recorded as two matrices: the basis Gram
matrix and the matrix of pairings of the basis with the approximated generators.

The choice of data follows `New.Space.stdClasses_eq_of_gram_eq` in
`New/UpperBound/Size/ClassCount.lean` of
[grh-lean](https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207/grh).
-/

public section

open Matrix IsDedekindDomain.FiniteAdeleRing
open scoped NumberField NumberField.AdeleRing

namespace NumberField.IsCMField

variable {E n : Type*} [Field E] [NumberField E] [IsCMField E] [Fintype n] [DecidableEq n]

local notation "O" => integralAdeles (𝓞 E) E
local notation "embed" => GeneralLinearGroup.map (algebraMap E 𝔸ᶠ[E])
local notation "uembed" => GeneralLinearGroup.map (algebraMap O 𝔸ᶠ[E])
local notation "adj" => fun X : Matrix n n E ↦
  (Matrix.map X (RingEquiv.toRingHom (AlgEquiv.toRingEquiv (complexConj E))))ᵀ
local notation "adjF" => fun X : Matrix n n 𝔸ᶠ[E] ↦
  (Matrix.map X (RingEquiv.toRingHom (finiteAdeleConj E)))ᵀ

private theorem isUnit_adj (A : GL n E) : IsUnit (adj ↑A) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  dsimp only
  rw [Matrix.det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact ((Matrix.isUnit_iff_isUnit_det _).mp A.isUnit).map (complexConj E).toRingHom

private theorem left_factor_unitary {A B U : GL n E} (hUA : U * A = B)
    (hG : adj ↑A * (A : Matrix n n E) = adj ↑B * (B : Matrix n n E)) :
    adj ↑U * (U : Matrix n n E) = 1 := by
  have h := congrArg (fun u : GL n E ↦ adj ↑u * (u : Matrix n n E)) hUA
  dsimp only at h
  rw [Units.val_mul, Matrix.map_mul (f := (complexConj E).toRingHom), transpose_mul] at h
  have h' : adj ↑A * (adj ↑U * (U : Matrix n n E)) * (A : Matrix n n E) =
      adj ↑A * 1 * (A : Matrix n n E) := by
    simpa only [Matrix.mul_assoc, Matrix.mul_one, Matrix.one_mul, ← hG] using h
  exact (isUnit_adj A).mul_right_injective (A.isUnit.mul_left_injective h')

private theorem right_factor_unitary {U : GL n E} {g h : GL n 𝔸ᶠ[E]} {V : GL n O}
    (heq : h = embed U * g * uembed V) (hu : adj ↑U * (U : Matrix n n E) = 1)
    (hg : adjF ↑g * (g : Matrix n n 𝔸ᶠ[E]) = 1)
    (hh : adjF ↑h * (h : Matrix n n 𝔸ᶠ[E]) = 1) :
    adjF (↑(uembed V)) * (↑(uembed V) : Matrix n n 𝔸ᶠ[E]) = 1 := by
  let U₀ : Matrix n n 𝔸ᶠ[E] := ↑(embed U)
  have hUcoe : U₀ = (U : Matrix n n E).map (algebraMap E 𝔸ᶠ[E]) := by
    ext i j : 1
    exact GeneralLinearGroup.map_apply _ i j U
  have hcomm : (U₀.map (finiteAdeleConj E).toRingHom) =
      ((↑U : Matrix n n E).map (complexConj E).toRingHom).map (algebraMap E 𝔸ᶠ[E]) := by
    ext i j : 1
    simp [hUcoe]
  have huF : adjF U₀ * U₀ = 1 := by
    simpa only [Matrix.map_mul, transpose_map, Matrix.map_one _ (map_zero _) (map_one _),
      hcomm, ← hUcoe] using congrArg (fun M : Matrix n n E ↦ M.map (algebraMap E 𝔸ᶠ[E])) hu
  dsimp only at hh huF hg ⊢
  rw [heq, Units.val_mul, Units.val_mul, Matrix.map_mul (f := (finiteAdeleConj E).toRingHom),
    Matrix.map_mul (f := (finiteAdeleConj E).toRingHom), transpose_mul, transpose_mul] at hh
  let g₀ : Matrix n n 𝔸ᶠ[E] := ↑g
  let V₀ : Matrix n n 𝔸ᶠ[E] := ↑(uembed V)
  calc
    _ = adjF V₀ * (adjF g₀ * (adjF U₀ * U₀) * g₀) * V₀ := by
      rw [huF, Matrix.mul_one, hg, Matrix.mul_one]
    _ = _ := by simp only [Matrix.mul_assoc, U₀, g₀, V₀]
    _ = 1 := hh

/-- Equal basis Gram matrices and equal Gram-weighted generator matrices identify two
adelic Hermitian lattice classes. The matrices `X`, `Y` approximate the generators in
rational basis coordinates modulo the integral finite adeles. The representatives `g`, `h`
are unitary, and their normalized column spans contain the integral coordinate lattice.
The conclusion gives a rational unitary matrix and an integral unitary change of columns,
so the representatives lie in the same unitary double coset. -/
theorem exists_unitary_mul_integral_of_gram_eq
    (A B : GL n E) (g h : GL n 𝔸ᶠ[E]) (X Y : Matrix n n E)
    (hg : adjF ↑g * (g : Matrix n n 𝔸ᶠ[E]) = 1)
    (hh : adjF ↑h * (h : Matrix n n 𝔸ᶠ[E]) = 1)
    (hA : Submodule.span O (Set.range (1 : Matrix n n 𝔸ᶠ[E]).col) ≤
      Submodule.span O (Set.range (↑(embed A⁻¹ * g) : Matrix n n 𝔸ᶠ[E]).col))
    (hB : Submodule.span O (Set.range (1 : Matrix n n 𝔸ᶠ[E]).col) ≤
      Submodule.span O (Set.range (↑(embed B⁻¹ * h) : Matrix n n 𝔸ᶠ[E]).col))
    (hX : ∀ i j, ((↑(embed A⁻¹ * g) : Matrix n n 𝔸ᶠ[E]) -
      X.map (algebraMap E 𝔸ᶠ[E])) i j ∈ O)
    (hY : ∀ i j, ((↑(embed B⁻¹ * h) : Matrix n n 𝔸ᶠ[E]) -
      Y.map (algebraMap E 𝔸ᶠ[E])) i j ∈ O)
    (hG : adj ↑A * (A : Matrix n n E) = adj ↑B * (B : Matrix n n E))
    (hGX : (adj ↑A * (A : Matrix n n E)) * X = (adj ↑B * (B : Matrix n n E)) * Y) :
    ∃ U : GL n E, ∃ V : GL n O,
      adj ↑U * (U : Matrix n n E) = 1 ∧
      adjF (↑(uembed V)) * (↑(uembed V) : Matrix n n 𝔸ᶠ[E]) = 1 ∧
      h = embed U * g * uembed V := by
  -- The Gram matrix is invertible, so the second datum determines the rational approximation.
  have hGunit : IsUnit (adj ↑A * (A : Matrix n n E)) := (isUnit_adj A).mul A.isUnit
  have hxy := hGunit.mul_right_injective (hGX.trans (congrArg (· * Y) hG).symm)
  subst Y
  let a := embed A⁻¹ * g
  let b := embed B⁻¹ * h
  have hspan (D : Matrix n n 𝔸ᶠ[E]) (hD :
      Submodule.span O (Set.range (1 : Matrix n n 𝔸ᶠ[E]).col) ≤
        Submodule.span O (Set.range D.col))
      (hDX : ∀ i j, (D - X.map (algebraMap E 𝔸ᶠ[E])) i j ∈ O) :
      Submodule.span O (Set.range D.col) = Submodule.span O (Set.range (1 : Matrix n n 𝔸ᶠ[E]).col) ⊔
        Submodule.span O (Set.range (X.map (algebraMap E 𝔸ᶠ[E])).col) := by
    refine D.span_col_eq_sup_of_sub_mem _ hD fun j ↦
      (mem_span_range_col_one_iff (Subalgebra.toSubring O) _).mpr ?_
    intro i
    simpa only [Pi.sub_apply, Matrix.col_apply, Matrix.sub_apply, Subalgebra.mem_toSubring]
      using hDX i j
  obtain ⟨V, hV⟩ := a.exists_mul_map_eq_of_span_col_eq b (fun _ _ e ↦ Subtype.ext e)
    ((hspan _ hA hX).trans (hspan _ hB hY).symm)
  let U := B * A⁻¹
  have hUA : U * A = B := by simp [U, mul_assoc]
  have heq : h = embed U * g * uembed V := by
    calc h = embed B * b := by simp [b, ← mul_assoc]
      _ = _ := by rw [← hV, ← hUA]; simp [a, ← mul_assoc]
  have hu := left_factor_unitary hUA hG
  exact ⟨U, V, hu, right_factor_unitary heq hu hg hh, heq⟩

end NumberField.IsCMField

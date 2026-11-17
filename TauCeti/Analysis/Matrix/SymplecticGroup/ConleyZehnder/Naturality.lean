/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps
public import TauCeti.Analysis.Matrix.SymplecticGroup.ConleyZehnder
public import TauCeti.Analysis.Matrix.SymplecticGroup.Connected
public import TauCeti.Analysis.Matrix.UnitaryGroup.Maslov.Multiplicity
import TauCeti.LinearAlgebra.Eigenspace.Matrix

/-!
# Naturality of the Conley–Zehnder index

The Conley–Zehnder index of a path `Ψ` of symplectic matrices
(`TauCeti.GLSymplectic.conleyZehnderIndex`) is invariant under conjugation by a constant
symplectic matrix: `CZ(P Ψ P⁻¹) = CZ(Ψ)` (`TauCeti.GLSymplectic.conleyZehnderIndex_map_conj`).
This is the naturality axiom of the index; together with the loop axiom it describes how the index
changes under a change of symplectic trivialization.

The proof goes through the zero axiom. The straightened graph `T Γ(A)` of a real matrix `A` meets
`ℝ^{n ⊕ n}`, the straightened diagonal, in the image of the fixed vectors of `A`, so the dimension
of that intersection is the dimension of the eigenspace of `A` at `1`
(`Matrix.finrank_realImage_diagonalStraightening_mul_graphFrame_inf_realSubspace`). By the zero
axiom for the Maslov index (`Matrix.UnitaryGroup.maslovIndex_eq_zero_of_finrank_eq`), a path of
symplectic matrices along which the eigenvalue `1` keeps the same geometric multiplicity has
Conley–Zehnder index zero
(`TauCeti.GLSymplectic.conleyZehnderIndex_eq_zero_of_finrank_eigenspace_eq`). The symplectic group
is path connected, so `P` is joined to the identity by a path `δ`, and
`(s, t) ↦ δ s Ψ(t) (δ s)⁻¹` is a homotopy from `Ψ` to `P Ψ P⁻¹`. Its paths
`s ↦ δ s Ψ(0) (δ s)⁻¹` and `s ↦ δ s Ψ(1) (δ s)⁻¹` through the endpoints run through conjugates of
a fixed matrix, so they have index zero, and the two paths have the same index.

## Main results

* `Matrix.finrank_realImage_diagonalStraightening_mul_graphFrame_inf_realSubspace`: the graph of
  `A` meets the diagonal in a space of the dimension of the fixed vectors of `A`.
* `TauCeti.GLSymplectic.conleyZehnderIndex_eq_zero_of_finrank_eigenspace_eq`: the zero axiom for
  the Conley–Zehnder index.
* `TauCeti.GLSymplectic.conleyZehnderIndex_map_conj`: naturality under conjugation by a constant
  symplectic matrix.

## References

* J. Robbin and D. Salamon, *The Maslov index for paths*, Topology **32** (1993), 827–844,
  Theorem 2.3 (the naturality and zero axioms) and Section 4.
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. **7**, AMS, 1999 (the naturality axiom of the Conley–Zehnder index).
-/

public section

open Matrix Module Module.End TauCeti
open scoped unitInterval

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The graph frame of `A`, as a real-linear map on the real vectors. -/
private noncomputable def graphFrameLin (A : Matrix (n ⊕ n) (n ⊕ n) ℝ) :
    (n ⊕ n → ℝ) →ₗ[ℝ] EuclideanSpace ℂ (n ⊕ n) where
  toFun x := WithLp.toLp 2 (graphFrame A *ᵥ fun k ↦ (x k : ℂ))
  map_add' x y := by
    rw [← WithLp.toLp_add, ← mulVec_add]
    congr 2
    ext k
    simp
  map_smul' c x := by
    rw [RingHom.id_apply, ← WithLp.toLp_smul, ← mulVec_smul]
    congr 2
    ext k
    simp

private theorem graphFrameLin_apply (A : Matrix (n ⊕ n) (n ⊕ n) ℝ) (x : n ⊕ n → ℝ) :
    graphFrameLin A x = WithLp.toLp 2 (graphFrame A *ᵥ fun k ↦ (x k : ℂ)) :=
  (rfl)

/-- Graph frames agree on real vectors `x` and `y` exactly when `x = y` and `A x = B y`: the first
factor `conj (φ x)` recovers `x`, and the second is `φ (A x)`. -/
private theorem graphFrame_mulVec_eq_iff (A B : Matrix (n ⊕ n) (n ⊕ n) ℝ) (x y : n ⊕ n → ℝ) :
    (graphFrame A *ᵥ fun k ↦ (x k : ℂ)) = (graphFrame B *ᵥ fun k ↦ (y k : ℂ)) ↔
      x = y ∧ A *ᵥ x = B *ᵥ y := by
  rw [graphFrame_mulVec, graphFrame_mulVec]
  constructor
  · intro h
    have h₁ (i : n) := congrFun h (.inl i)
    have h₂ (i : n) := congrFun h (.inr i)
    simp only [Sum.elim_inl, Sum.elim_inr, Complex.ext_iff] at h₁ h₂
    refine ⟨funext fun k ↦ ?_, funext fun k ↦ ?_⟩ <;> rcases k with i | i <;> simp_all
  · rintro ⟨rfl, h⟩
    rw [h]

private theorem injective_graphFrameLin (A : Matrix (n ⊕ n) (n ⊕ n) ℝ) :
    Function.Injective (graphFrameLin A) := fun x y h ↦
  ((graphFrame_mulVec_eq_iff A A x y).1 (by simpa [graphFrameLin_apply] using h)).1

/-- The graph of `A` meets the diagonal in the image of the fixed vectors of `A`. -/
private theorem realImage_graphFrame_inf_realImage_graphFrame_one
    (A : Matrix (n ⊕ n) (n ⊕ n) ℝ) :
    (graphFrame A).realImage ⊓ (graphFrame 1).realImage =
      (eigenspace (toLin' A) 1).map (graphFrameLin A) := by
  ext v
  simp only [Submodule.mem_inf, mem_realImage_iff_exists_mulVec, Submodule.mem_map,
    mem_eigenspace_iff, toLin'_apply, one_smul, graphFrameLin_apply]
  constructor
  · rintro ⟨⟨x, rfl⟩, y, hy⟩
    obtain ⟨rfl, h⟩ := (graphFrame_mulVec_eq_iff _ _ _ _).1 (WithLp.toLp_injective 2 hy).symm
    exact ⟨x, by simpa using h, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, rfl⟩, x, congrArg (WithLp.toLp 2)
      ((graphFrame_mulVec_eq_iff _ _ _ _).2 ⟨rfl, by simpa using hx.symm⟩)⟩

/-- **The graph of `A` meets the diagonal in the fixed vectors of `A`.** The real dimension of the
intersection of the straightened graph `T Γ(A)` with `ℝ^{n ⊕ n}`, the straightened diagonal, is
the dimension of the eigenspace of `A` at `1`. -/
theorem finrank_realImage_diagonalStraightening_mul_graphFrame_inf_realSubspace
    (A : Matrix (n ⊕ n) (n ⊕ n) ℝ) :
    finrank ℝ ((diagonalStraightening n * graphFrame A).realImage ⊓ realSubspace (n ⊕ n) :
      Submodule ℝ _) = finrank ℝ (eigenspace (toLin' A) 1) := by
  set T := (toEuclideanCLM (𝕜 := ℂ) (diagonalStraightening n) :
      EuclideanSpace ℂ (n ⊕ n) →ₗ[ℂ] EuclideanSpace ℂ (n ⊕ n)).restrictScalars ℝ
  have hT : Function.Injective T := by
    intro x y h
    simp only [T, LinearMap.restrictScalars_apply, ContinuousLinearMap.coe_coe] at h
    have h' := congrArg (toEuclideanCLM (𝕜 := ℂ) (star (diagonalStraightening n))) h
    rwa [← mul_apply_eq_comp, ← mul_apply_eq_comp, ← map_mul,
      Unitary.star_mul_self_of_mem diagonalStraightening_mem_unitaryGroup, map_one] at h'
  rw [← realImage_diagonalStraightening_mul_graphFrame_one, realImage_mul, realImage_mul,
    ← Submodule.map_inf T hT, realImage_graphFrame_inf_realImage_graphFrame_one,
    ← Submodule.map_comp]
  exact (Submodule.equivMapOfInjective (T ∘ₗ graphFrameLin A)
    (hT.comp (injective_graphFrameLin A)) _).finrank_eq.symm

end Matrix

namespace TauCeti.GLSymplectic

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The multiplicity of `1` as an eigenvalue of the Souriau map of the unitary graph frame of a
symplectic matrix `A` is the dimension of the fixed vectors of `A`. -/
theorem rootMultiplicity_charpoly_souriau_graphUnitaryFrame (A : GLSymplectic n ℝ) :
    (UnitaryGroup.souriau (graphUnitaryFrame A) :
      Matrix (n ⊕ n) (n ⊕ n) ℂ).charpoly.rootMultiplicity 1 =
        finrank ℝ (eigenspace (toLin' ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)) 1) := by
  rw [UnitaryGroup.rootMultiplicity_charpoly_souriau, realImage_graphUnitaryFrame,
    finrank_realImage_diagonalStraightening_mul_graphFrame_inf_realSubspace]

/-- **The zero axiom for the Conley–Zehnder index.** A path of symplectic matrices along which the
eigenvalue `1` keeps the same geometric multiplicity has Conley–Zehnder index zero. In particular
a path of symplectic matrices without the eigenvalue `1` has index zero. -/
theorem conleyZehnderIndex_eq_zero_of_finrank_eigenspace_eq {A B : GLSymplectic n ℝ}
    (γ : Path A B) {k : ℕ}
    (h : ∀ t, finrank ℝ (eigenspace (toLin' ((γ t : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ))
      1) = k) :
    conleyZehnderIndex γ = 0 := by
  rw [conleyZehnderIndex_def, UnitaryGroup.maslovIndex_eq_zero_of_rootMultiplicity_eq _ (k := k)
    fun t ↦ by rw [Path.map_coe, Function.comp_apply,
      rootMultiplicity_charpoly_souriau_graphUnitaryFrame, h t], neg_zero]

/-- **Naturality of the Conley–Zehnder index.** Conjugating a path of symplectic matrices by a
constant symplectic matrix `P` does not change its Conley–Zehnder index: `CZ(P Ψ P⁻¹) = CZ(Ψ)`. -/
theorem conleyZehnderIndex_map_conj (P : GLSymplectic n ℝ) {A B : GLSymplectic n ℝ}
    (γ : Path A B) :
    conleyZehnderIndex (γ.map (f := fun X ↦ P * X * P⁻¹) (by fun_prop)) =
      conleyZehnderIndex γ := by
  let δ := PathConnectedSpace.somePath (1 : GLSymplectic n ℝ) P
  -- The homotopy `(s, t) ↦ δ s γ(t) (δ s)⁻¹` from `γ` to its conjugate by `P`.
  let F : ContinuousMap.Homotopy (⟨γ, γ.continuous⟩ : C(I, GLSymplectic n ℝ))
      ⟨fun t ↦ P * γ t * P⁻¹, by fun_prop⟩ :=
    { toFun := fun p ↦ δ p.1 * γ p.2 * (δ p.1)⁻¹
      continuous_toFun := by fun_prop
      map_zero_left := fun t ↦ by simp [δ]
      map_one_left := fun t ↦ by simp [δ] }
  -- Its paths through the endpoints run through conjugates of a fixed matrix.
  have hedge (x : I) : conleyZehnderIndex (F.evalAt x) = 0 :=
    conleyZehnderIndex_eq_zero_of_finrank_eigenspace_eq _ fun s ↦
      finrank_eigenspace_toLin'_conj (δ s : GL (n ⊕ n) ℝ) (γ x : GL (n ⊕ n) ℝ) 1
  have h := conleyZehnderIndex_eq_of_homotopic (Path.Homotopic.map_trans_evalAt F Path.id)
  rw [conleyZehnderIndex_trans, conleyZehnderIndex_trans, hedge, hedge, add_zero, zero_add] at h
  -- Along `Path.id`, the two maps are `γ` and its conjugate, with endpoints written differently.
  rw [conleyZehnderIndex_def, conleyZehnderIndex_def, neg_inj] at h
  rw [conleyZehnderIndex_def, conleyZehnderIndex_def, neg_inj]
  refine Eq.trans ?_ (h.symm.trans ?_) <;>
    exact UnitaryGroup.maslovIndex_eq_of_souriau_eq _ _ fun _ ↦ rfl

end TauCeti.GLSymplectic

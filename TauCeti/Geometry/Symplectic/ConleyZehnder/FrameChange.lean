/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.Contractible
public import TauCeti.Analysis.Matrix.SymplecticGroup.ConleyZehnder.FrameChange
public import TauCeti.Geometry.Symplectic.ConleyZehnder

import TauCeti.LinearAlgebra.BilinearForm.SymplecticBasis

/-!
# The Maslov index of loops of linear symplectic maps and change of frame

Let `(V, ω)` be a finite-dimensional symplectic vector space. The Conley–Zehnder index
`TauCeti.SymplecticForm.conleyZehnderIndex` of a path of linear symplectic maps of `V` is read in a
symplectic basis, and so is the Maslov index of a loop of linear symplectic maps of `V`
(`TauCeti.SymplecticForm.maslovIndex`): it is the Maslov index
`TauCeti.GLSymplectic.maslovIndex` of the loop of its matrices in a symplectic basis. It does not
depend on the basis (`TauCeti.SymplecticForm.maslovIndex_eq`): the matrices in two symplectic bases
are conjugate by the change of basis matrix, and conjugating by a constant symplectic matrix does
not change the Maslov index, by the product axiom `TauCeti.GLSymplectic.maslovIndex_mul`.

* **Loop operations.** The Maslov index vanishes on constant loops, is additive under
  concatenation and pointwise composition, changes sign under reversal, is invariant under
  homotopies through loops, and is preserved by conjugation with a linear symplectomorphism
  (`TauCeti.SymplecticForm.maslovIndex_refl`, `maslovIndex_trans`, `maslovIndex_mul`,
  `maslovIndex_symm`, `maslovIndex_eq_of_homotopy`, `maslovIndex_map_conj`), each read from the
  matrix law in a symplectic basis.
* **Loops through a contractible space.** A loop of linear symplectic maps `t ↦ a(β t)` that
  factors through a continuous map `a` on a contractible space has Maslov index zero
  (`TauCeti.SymplecticForm.maslovIndex_map_eq_zero`): contracting the space contracts the loop
  through loops of symplectic maps.
* **Change of frame.** Let `Ψ(t) = e(t)⁻¹ Φ(t) e(0)` be a path of linear symplectic maps read in a
  symplectic frame `e`, and let `e'(t) = e(t) g(t)` be another frame, with `g` a loop. Then
  `Ψ` read in `e'` is the path `t ↦ g(t)⁻¹ Ψ(t) g(0)`
  (`TauCeti.SymplecticForm.frameChange`, given the pointwise inverses `g'` of `g`), and its
  Conley–Zehnder index is `CZ(Ψ) + 2 μ(g)`
  (`TauCeti.SymplecticForm.conleyZehnderIndex_frameChange`). This is the matrix law
  `TauCeti.GLSymplectic.conleyZehnderIndex_frameChange` read in a symplectic basis.

The law is the reason the Conley–Zehnder index of a contractible periodic orbit depends on the
choice of a trivialization along the orbit only through the Maslov index of the change of
trivialization, which vanishes for trivializations extending over a common disc.

## References

* J. Robbin and D. Salamon, *The Maslov index for paths*, Topology **32** (1993), 827–844,
  Section 4 (the loop axiom of the Conley–Zehnder index).
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. **7**, AMS, 1999, Lecture 2 (the Conley–Zehnder index through a symplectic
  trivialization and its dependence on the trivialization).
-/

public section

noncomputable section

open Matrix Module
open scoped unitInterval

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  (ω : SymplecticForm V)

/-! ### The Maslov index of a loop of linear symplectic maps -/

/-- **The Maslov index does not depend on the symplectic basis.** The matrices of a loop `g` of
linear maps preserving `ω` in two symplectic bases indexed by the same type have the same Maslov
index: they are conjugate by the change of basis matrix. -/
theorem maslovIndex_matrixPath_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    {b b' : Basis (ι ⊕ ι) ℝ V} (hb : LinearMap.BilinForm.toMatrix b ω.toBilinForm = J ι ℝ)
    (hb' : LinearMap.BilinForm.toMatrix b' ω.toBilinForm = J ι ℝ) {A : V →L[ℝ] V} (g : Path A A)
    (hg : ∀ t u v, ω (g t u) (g t v) = ω u v) :
    GLSymplectic.maslovIndex (ω.matrixPath hb' g hg) =
      GLSymplectic.maslovIndex (ω.matrixPath hb g hg) := by
  set P := ω.basisChange hb hb'
  -- In the basis `b'` the loop of matrices is the pointwise product `P M P⁻¹`.
  have h : GLSymplectic.maslovIndex (ω.matrixPath hb' g hg) =
      GLSymplectic.maslovIndex
        (((Path.refl P).mul (ω.matrixPath hb g hg)).mul (Path.refl P⁻¹)) :=
    GLSymplectic.maslovIndex_congr _ _ fun t ↦ by
      simp [ω.toGLSymplectic_eq_basisChange_mul hb hb', P]
  rw [h, GLSymplectic.maslovIndex_mul, GLSymplectic.maslovIndex_mul,
    GLSymplectic.maslovIndex_refl, GLSymplectic.maslovIndex_refl, zero_add, add_zero]

/-- **The Maslov index of a loop of linear symplectic maps.** For a loop `g` of linear maps of a
finite-dimensional symplectic vector space `(V, ω)` preserving `ω`, this is the Maslov index of
the loop of its matrices in a symplectic basis indexed by `Fin m ⊕ Fin m`. By
`TauCeti.SymplecticForm.maslovIndex_eq` it does not depend on the basis. -/
def maslovIndex {A : V →L[ℝ] V} (g : Path A A) (hg : ∀ t u v, ω (g t u) (g t v) = ω u v) : ℤ :=
  GLSymplectic.maslovIndex
    (ω.matrixPath (ω.isAlt.exists_basis_toMatrix_eq_J ω.nondegenerate).choose_spec.choose_spec
      g hg)

/-- **The Maslov index in any symplectic basis.** The Maslov index of a loop of linear symplectic
maps is the Maslov index of its matrices in any symplectic basis indexed by `Fin m ⊕ Fin m`. -/
theorem maslovIndex_eq {m : ℕ} {b : Basis (Fin m ⊕ Fin m) ℝ V}
    (hb : LinearMap.BilinForm.toMatrix b ω.toBilinForm = J (Fin m) ℝ) {A : V →L[ℝ] V}
    (g : Path A A) (hg : ∀ t u v, ω (g t u) (g t v) = ω u v) :
    ω.maslovIndex g hg = GLSymplectic.maslovIndex (ω.matrixPath hb g hg) :=
  ω.eq_of_basis_invariant (fun _ _ hc ↦ GLSymplectic.maslovIndex (ω.matrixPath hc g hg))
    (fun _ _ _ hc hc' ↦ ω.maslovIndex_matrixPath_eq hc' hc g hg) _ hb

/-- The Maslov index of a loop of linear symplectic maps only depends on the loop as a function
of time, not on the way its base point is written. -/
theorem maslovIndex_congr {A A' : V →L[ℝ] V} (g : Path A A) (g' : Path A' A')
    (hg : ∀ t u v, ω (g t u) (g t v) = ω u v) (h : ∀ t, g t = g' t) :
    ω.maslovIndex g hg = ω.maslovIndex g' fun t ↦ h t ▸ hg t := by
  obtain ⟨m, b, hb⟩ := ω.isAlt.exists_basis_toMatrix_eq_J ω.nondegenerate
  rw [ω.maslovIndex_eq hb, ω.maslovIndex_eq hb]
  refine GLSymplectic.maslovIndex_congr _ _ fun t ↦ ?_
  rw [matrixPath_apply, matrixPath_apply]
  exact ω.toGLSymplectic_congr hb (congrArg ContinuousLinearMap.toLinearMap (h t)) _ _

/-- A constant loop of linear symplectic maps has Maslov index zero. -/
@[simp]
theorem maslovIndex_refl (A : V →L[ℝ] V)
    (hA : ∀ t u v, ω (Path.refl A t u) (Path.refl A t v) = ω u v) :
    ω.maslovIndex (Path.refl A) hA = 0 := by
  obtain ⟨m, b, hb⟩ := ω.isAlt.exists_basis_toMatrix_eq_J ω.nondegenerate
  rw [ω.maslovIndex_eq hb, ← GLSymplectic.maslovIndex_refl
    (ω.toGLSymplectic hb A (by simpa using hA 0))]
  exact GLSymplectic.maslovIndex_congr _ _ fun t ↦ by simp

/-- The Maslov index of loops of linear symplectic maps is additive under concatenation. -/
theorem maslovIndex_trans {A : V →L[ℝ] V} (g₁ g₂ : Path A A)
    (h₁ : ∀ t u v, ω (g₁ t u) (g₁ t v) = ω u v) (h₂ : ∀ t u v, ω (g₂ t u) (g₂ t v) = ω u v) :
    ω.maslovIndex (g₁.trans g₂) (ω.apply_path_trans_apply h₁ h₂) =
      ω.maslovIndex g₁ h₁ + ω.maslovIndex g₂ h₂ := by
  obtain ⟨m, b, hb⟩ := ω.isAlt.exists_basis_toMatrix_eq_J ω.nondegenerate
  rw [ω.maslovIndex_eq hb, ω.maslovIndex_eq hb, ω.maslovIndex_eq hb,
    ← GLSymplectic.maslovIndex_trans]
  exact GLSymplectic.maslovIndex_congr _ _ (ω.matrixPath_trans_apply hb g₁ g₂ h₁ h₂)

/-- Reversing a loop of linear symplectic maps negates its Maslov index. -/
theorem maslovIndex_symm {A : V →L[ℝ] V} (g : Path A A)
    (hg : ∀ t u v, ω (g t u) (g t v) = ω u v) :
    ω.maslovIndex g.symm (ω.apply_path_symm_apply hg) = -ω.maslovIndex g hg := by
  obtain ⟨m, b, hb⟩ := ω.isAlt.exists_basis_toMatrix_eq_J ω.nondegenerate
  rw [ω.maslovIndex_eq hb, ω.maslovIndex_eq hb, ← GLSymplectic.maslovIndex_symm]
  exact GLSymplectic.maslovIndex_congr _ _ fun t ↦ by simp [Path.symm_apply]

/-- **The product axiom.** The pointwise composition `t ↦ g₁(t) ∘ g₂(t)` of two loops of linear
symplectic maps has the sum of their Maslov indices. -/
theorem maslovIndex_mul {A B : V →L[ℝ] V} (g₁ : Path A A) (g₂ : Path B B)
    (h₁ : ∀ t u v, ω (g₁ t u) (g₁ t v) = ω u v) (h₂ : ∀ t u v, ω (g₂ t u) (g₂ t v) = ω u v) :
    ω.maslovIndex (g₁.mul g₂) (ω.apply_path_mul_apply h₁ h₂) =
      ω.maslovIndex g₁ h₁ + ω.maslovIndex g₂ h₂ := by
  obtain ⟨m, b, hb⟩ := ω.isAlt.exists_basis_toMatrix_eq_J ω.nondegenerate
  rw [ω.maslovIndex_eq hb, ω.maslovIndex_eq hb, ω.maslovIndex_eq hb,
    ← GLSymplectic.maslovIndex_mul]
  refine GLSymplectic.maslovIndex_congr _ _ fun t ↦ ?_
  conv_rhs => rw [Path.mul_apply, matrixPath_apply, matrixPath_apply]
  rw [matrixPath_apply, ← ω.toGLSymplectic_comp hb (h₁ t) (h₂ t) fun u v ↦ by simp [h₁ t, h₂ t]]
  exact ω.toGLSymplectic_congr hb
    (by rw [Path.mul_apply, ContinuousLinearMap.toLinearMap_mul, Module.End.mul_eq_comp]) _ _

/-- **Homotopy invariance.** If `F` is a homotopy from the loop `g₀` to the loop `g₁` through
loops of linear symplectic maps (`F (s, 0) = F (s, 1)` for every `s`; the base point may move),
the two loops have the same Maslov index. -/
theorem maslovIndex_eq_of_homotopy {A B : V →L[ℝ] V} (g₀ : Path A A) (g₁ : Path B B)
    (F : C(I × I, V →L[ℝ] V)) (hF : ∀ p u v, ω (F p u) (F p v) = ω u v)
    (h₀ : ∀ t, F (0, t) = g₀ t) (h₁ : ∀ t, F (1, t) = g₁ t) (hF₀₁ : ∀ s, F (s, 0) = F (s, 1)) :
    ω.maslovIndex g₀ (fun t ↦ h₀ t ▸ hF (0, t)) = ω.maslovIndex g₁ (fun t ↦ h₁ t ▸ hF (1, t)) := by
  obtain ⟨m, b, hb⟩ := ω.isAlt.exists_basis_toMatrix_eq_J ω.nondegenerate
  rw [ω.maslovIndex_eq hb, ω.maslovIndex_eq hb]
  -- The matrices of `F` form a homotopy of loops of symplectic matrices.
  refine GLSymplectic.maslovIndex_eq_of_homotopy _ _
    ⟨fun p ↦ ω.toGLSymplectic hb (F p) (hF p), ω.continuous_toGLSymplectic hb F.continuous hF⟩
    (fun t ↦ ?_) (fun t ↦ ?_) (fun s ↦ ?_)
  · rw [ContinuousMap.coe_mk, matrixPath_apply]
    exact ω.toGLSymplectic_congr hb (congrArg ContinuousLinearMap.toLinearMap (h₀ t)) _ _
  · rw [ContinuousMap.coe_mk, matrixPath_apply]
    exact ω.toGLSymplectic_congr hb (congrArg ContinuousLinearMap.toLinearMap (h₁ t)) _ _
  · exact ω.toGLSymplectic_congr hb (congrArg ContinuousLinearMap.toLinearMap (hF₀₁ s)) _ _

/-- **Loops through a contractible space have Maslov index zero.** If `a` is a continuous family of
linear symplectic maps of `(V, ω)` parametrized by a contractible space `Y`, the loop
`t ↦ a(β t)` along any loop `β` in `Y` has Maslov index zero. -/
theorem maslovIndex_map_eq_zero {Y : Type*} [TopologicalSpace Y] [ContractibleSpace Y]
    {a : Y → V →L[ℝ] V} (ha : Continuous a) (ha' : ∀ y u v, ω (a y u) (a y v) = ω u v)
    {y₀ : Y} (β : Path y₀ y₀) :
    ω.maslovIndex (β.map ha) (fun t ↦ by simpa using ha' (β t)) = 0 := by
  obtain ⟨m, b, hb⟩ := ω.isAlt.exists_basis_toMatrix_eq_J ω.nondegenerate
  rw [ω.maslovIndex_eq hb]
  -- Contracting `Y` to a point `y₁` contracts the loop of matrices through loops.
  obtain ⟨y₁, ⟨H⟩⟩ := id_nullhomotopic Y
  let F : C(I × I, GLSymplectic (Fin m) ℝ) :=
    ⟨fun p ↦ ω.toGLSymplectic hb (a (H (p.1, β p.2))) (ha' _),
      (ω.continuous_toGLSymplectic hb ha ha').comp
        (H.continuous.comp (continuous_fst.prodMk (β.continuous.comp continuous_snd)))⟩
  rw [GLSymplectic.maslovIndex_eq_of_homotopy _
    (Path.refl (ω.toGLSymplectic hb (a y₁) (ha' y₁))) F (fun t ↦ ?_) (fun t ↦ ?_) (fun s ↦ ?_),
    GLSymplectic.maslovIndex_refl]
  · simp [F]
  · simp [F]
  · simp [F]

/-! ### Change of frame -/

/-- The path `Ψ` read in a frame changed by a loop: `t ↦ g'(t) ∘ Ψ(t) ∘ P`. When `g'(t)` is the
inverse of `g(t)` for a loop `g` based at `P`, this is the coordinate path `t ↦ g(t)⁻¹ Ψ(t) g(0)`:
if `Ψ(t) = e(t)⁻¹ Φ(t) e(0)` in a frame `e`, it is `e'(t)⁻¹ Φ(t) e'(0)` in the frame
`e'(t) = e(t) g(t)`. -/
def frameChange {A B C : V →L[ℝ] V} (g' : Path A A) (Ψ : Path B C) (P : V →L[ℝ] V) :
    Path (A ∘L B ∘L P) (A ∘L C ∘L P) where
  toFun t := g' t ∘L Ψ t ∘L P
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by simp

omit [FiniteDimensional ℝ V] in
/-- The frame-changed path at time `t` is `g'(t) ∘ Ψ(t) ∘ P`. -/
@[simp]
theorem frameChange_apply {A B C : V →L[ℝ] V} (g' : Path A A) (Ψ : Path B C) (P : V →L[ℝ] V)
    (t : I) : frameChange g' Ψ P t = g' t ∘L Ψ t ∘L P :=
  (rfl)

/-- If `g` is a loop of linear symplectic maps with pointwise inverses `g'`, and `Ψ` is a path of
linear symplectic maps, the frame-changed path `t ↦ g'(t) ∘ Ψ(t) ∘ g(0)` runs through linear
symplectic maps. -/
theorem apply_frameChange_apply {A A' B C : V →L[ℝ] V} {g : Path A A} {g' : Path A' A'}
    (hg : ∀ t u v, ω (g t u) (g t v) = ω u v) (hg' : ∀ t u, g' t (g t u) = u) {Ψ : Path B C}
    (hΨ : ∀ t u v, ω (Ψ t u) (Ψ t v) = ω u v) (t : I) (u v : V) :
    ω (frameChange g' Ψ A t u) (frameChange g' Ψ A t v) = ω u v := by
  have hA (u v : V) : ω (A u) (A v) = ω u v := by simpa using hg 0 u v
  have hgt : ∀ u v, ω (g' t u) (g' t v) = ω u v :=
    ω.apply_apply_of_leftInverse (f := g t) (f' := g' t) (hg t) (hg' t)
  rw [frameChange_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hgt, hΨ, hA]

/-- **Change of frame for the Conley–Zehnder index of linear symplectic maps.** Let `g` be a loop
of linear maps preserving `ω`, with pointwise inverses `g'`, and `Ψ` a path of linear maps
preserving `ω`. Reading `Ψ` in the frame changed by `g`, that is, passing to the path
`t ↦ g(t)⁻¹ Ψ(t) g(0)`, adds twice the Maslov index of `g` to its Conley–Zehnder index. -/
theorem conleyZehnderIndex_frameChange {A A' B C : V →L[ℝ] V} (g : Path A A)
    (hg : ∀ t u v, ω (g t u) (g t v) = ω u v) (g' : Path A' A') (hg' : ∀ t u, g' t (g t u) = u)
    (Ψ : Path B C) (hΨ : ∀ t u v, ω (Ψ t u) (Ψ t v) = ω u v) :
    ω.conleyZehnderIndex (frameChange g' Ψ A) (ω.apply_frameChange_apply hg hg' hΨ) =
      ω.conleyZehnderIndex Ψ hΨ + 2 * ω.maslovIndex g hg := by
  obtain ⟨m, b, hb⟩ := ω.isAlt.exists_basis_toMatrix_eq_J ω.nondegenerate
  rw [ω.conleyZehnderIndex_eq hb, ω.conleyZehnderIndex_eq hb, ω.maslovIndex_eq hb,
    ← GLSymplectic.conleyZehnderIndex_frameChange]
  refine GLSymplectic.conleyZehnderIndex_congr _ _ fun t ↦ ?_
  have hA (u v : V) : ω (A u) (A v) = ω u v := by simpa using hg 0 u v
  have hgt : ∀ u v, ω (g' t u) (g' t v) = ω u v :=
    ω.apply_apply_of_leftInverse (f := g t) (f' := g' t) (hg t) (hg' t)
  -- The matrix of `g'(t) ∘ Ψ(t) ∘ g(0)` is the product of the three matrices.
  rw [matrixPath_apply, GLSymplectic.frameChange_apply, matrixPath_apply, matrixPath_apply,
    ← ω.toGLSymplectic_of_leftInverse hb (hg t) hgt (hg' t), mul_assoc,
    ← ω.toGLSymplectic_comp hb (hΨ t) hA fun u v ↦ by simp [hΨ t, hA],
    ← ω.toGLSymplectic_comp hb hgt _ fun u v ↦ by simp [hΨ t, hA, hgt]]
  exact ω.toGLSymplectic_congr hb (by simp [frameChange_apply]) _ _

/-! ### Naturality -/

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {ω' : SymplecticForm W}

/-- **Naturality of the Maslov index.** A linear symplectomorphism `e : (V, ω) ≃ (W, ω')` carries
a loop `g` of linear symplectic maps of `V` to the loop `e ∘ g ∘ e⁻¹` of linear symplectic maps of
`W` with the same Maslov index. -/
theorem maslovIndex_map_conj (e : V ≃L[ℝ] W) (he : IsSymplectomorphism ω ω' e.toLinearEquiv)
    {A : V →L[ℝ] V} (g : Path A A) (hg : ∀ t u v, ω (g t u) (g t v) = ω u v) :
    ω'.maslovIndex (g.map (f := fun C : V →L[ℝ] V ↦ (e : V →L[ℝ] W) ∘L C ∘L
      (e.symm : W →L[ℝ] V)) (by fun_prop)) (apply_path_map_conj_apply ω e he hg) =
      ω.maslovIndex g hg := by
  obtain ⟨m, b, hb⟩ := ω.isAlt.exists_basis_toMatrix_eq_J ω.nondegenerate
  -- The image of a symplectic basis under `e` is a symplectic basis with the same matrices.
  rw [ω'.maslovIndex_eq (ω.toMatrix_map_eq_J e he hb), ω.maslovIndex_eq hb]
  refine GLSymplectic.maslovIndex_congr _ _ fun t ↦ ?_
  rw [matrixPath_apply, matrixPath_apply]
  exact ω.toGLSymplectic_conj e he hb (g t) (hg t) (apply_path_map_conj_apply ω e he hg t)

end TauCeti.SymplecticForm

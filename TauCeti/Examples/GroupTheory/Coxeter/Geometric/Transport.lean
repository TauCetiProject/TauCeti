/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import TauCeti.GroupTheory.Coxeter.Geometric.Transport
public import TauCeti.GroupTheory.Coxeter.Graph

/-!
# Faithfulness and transport of the geometric representation in small cases

These checks run the faithfulness and transport API of the geometric representation of a Coxeter
system on small examples.

* With no generators the group is trivial and acts faithfully on the zero space. In rank one the
  simple reflection acts on `Fin 1 → ℝ` by `-1`, which is not the identity.
* For an infinite entry the Gram matrix of the two simple roots is `!![1, -1; -1, 1]`, of
  determinant zero, yet `(sᵢ sⱼ)ⁿ` sends `αᵢ` to `(2 n + 1) αᵢ + 2 n αⱼ`.
* Reindexing `A₂` by its transposition `Equiv.swap 0 1` sends `α₀` to `α₁`, and conjugates `σ₀`
  to the reflection `σ'₁` of the reindexed system, not to `σ'₀`. For `w = s₀ s₁` both sides of
  the transport equation send `α₀` to `α'₀`.
* For three orthogonal nodes and the cycle `e = (0 1 2)`, the inverse of
  `CoxeterMatrix.reindexGroupEquiv` sends generator `0` to generator `1`, while the forward map
  sends the reindexed generator `0` to the original generator `2`.
* For the parabolic subset `{i}`, extension by zero intertwines the reflections. For the empty
  subset it is the zero map out of the zero space, and for the full subset it is the coordinate
  equivalence.
-/

public section

open Real

namespace TauCeti

/-! ### Empty index set and rank one -/

/-- With no generators the Coxeter group is trivial, the representation space is zero, and the
geometric representation is injective. -/
example {B W : Type*} [Group W] [IsEmpty B] {M : CoxeterMatrix B} (cs : CoxeterSystem M W) :
    Subsingleton W ∧ Subsingleton (B →₀ ℝ) ∧ Function.Injective cs.geometricRepresentation :=
  ⟨cs.subsingleton_of_isEmpty, inferInstance, cs.geometricRepresentation_injective⟩

/-- In rank one the simple reflection acts on coordinate functions by `-1`, so `ρ(s) = -1`
differs from `ρ(1) = 1`. -/
example :
    (∀ v : Fin 1 → ℝ, (CoxeterMatrix.A 1).toCoxeterSystem.geometricRepresentationFun
        ((CoxeterMatrix.A 1).toCoxeterSystem.simple 0) v = -v) ∧
    (CoxeterMatrix.A 1).toCoxeterSystem.geometricRepresentationFun
        ((CoxeterMatrix.A 1).toCoxeterSystem.simple 0) ≠
      (CoxeterMatrix.A 1).toCoxeterSystem.geometricRepresentationFun 1 := by
  have hs (v : Fin 1 → ℝ) : (CoxeterMatrix.A 1).toCoxeterSystem.geometricRepresentationFun
      ((CoxeterMatrix.A 1).toCoxeterSystem.simple 0) v = -v := by
    rw [CoxeterSystem.geometricRepresentationFun_simple_apply]
    ext k
    fin_cases k
    simp [CoxeterMatrix.A]
    ring
  refine ⟨hs, fun h ↦ ?_⟩
  have := congr_fun (LinearMap.congr_fun h fun _ ↦ 1) 0
  rw [hs, map_one, one_apply_eq_self] at this
  norm_num at this

/-! ### An infinite entry -/

section Infinite

variable {B W : Type*} [Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W) {i j : B}

/-- For an infinite entry the Gram matrix of the two simple roots is `!![1, -1; -1, 1]`, which is
singular. -/
example (h : M i j = 0) :
    !![M.geometricForm (Finsupp.single i 1) (Finsupp.single i 1),
        M.geometricForm (Finsupp.single i 1) (Finsupp.single j 1);
      M.geometricForm (Finsupp.single j 1) (Finsupp.single i 1),
        M.geometricForm (Finsupp.single j 1) (Finsupp.single j 1)] = !![1, -1; -1, 1] ∧
    (!![1, -1; -1, 1] : Matrix (Fin 2) (Fin 2) ℝ).det = 0 := by
  refine ⟨?_, by simp [Matrix.det_fin_two]⟩
  ext a b
  fin_cases a <;> fin_cases b <;> simp [M.symmetric j i, h]

/-- For an infinite entry, `(sᵢ sⱼ)ⁿ` sends `αᵢ` to `(2 n + 1) αᵢ + 2 n αⱼ`, with first three
values `(1, 0)`, `(3, 2)` and `(5, 4)`. -/
example (h : M i j = 0) :
    (∀ n : ℕ,
      cs.geometricRepresentation ((cs.simple i * cs.simple j) ^ n) (Finsupp.single i 1) =
        (2 * n + 1 : ℝ) • Finsupp.single i 1 + (2 * n : ℝ) • Finsupp.single j 1) ∧
    cs.geometricRepresentation 1 (Finsupp.single i 1) = Finsupp.single i 1 ∧
    cs.geometricRepresentation (cs.simple i * cs.simple j) (Finsupp.single i 1) =
      Finsupp.single i 3 + Finsupp.single j 2 ∧
    cs.geometricRepresentation ((cs.simple i * cs.simple j) ^ 2) (Finsupp.single i 1) =
      Finsupp.single i 5 + Finsupp.single j 4 := by
  have hn (n : ℕ) :
      cs.geometricRepresentation ((cs.simple i * cs.simple j) ^ n) (Finsupp.single i 1) =
        (2 * n + 1 : ℝ) • Finsupp.single i 1 + (2 * n : ℝ) • Finsupp.single j 1 := by
    rw [map_pow, map_mul, cs.geometricRepresentation_simple, cs.geometricRepresentation_simple]
    exact M.pow_geometricReflection_mul_apply_single_of_eq_zero i j h n
  refine ⟨hn, by simp, ?_, ?_⟩
  · rw [← pow_one (cs.simple i * cs.simple j), hn]
    norm_num [Finsupp.smul_single]
  · rw [hn]
    norm_num [Finsupp.smul_single]

end Infinite

/-! ### Reindexing `A₂` by its transposition -/

section ReindexA₂

/-- The coordinate equivalence of the transposition sends `α₀` to `α₁`. -/
example : Finsupp.domLCongr (R := ℝ) (Equiv.swap (0 : Fin 2) 1) (Finsupp.single 0 (1 : ℝ)) =
    Finsupp.single 1 1 := by
  simp

/-- For `A₂` and the transposition `Equiv.swap 0 1`, the inverse of
`CoxeterMatrix.reindexGroupEquiv` sends generator `0` to generator `1`. -/
example :
    ((CoxeterMatrix.A 2).reindexGroupEquiv (Equiv.swap 0 1)).symm ((CoxeterMatrix.A 2).simple 0) =
      ((CoxeterMatrix.A 2).reindex (Equiv.swap 0 1)).simple 1 := by
  rw [CoxeterMatrix.reindexGroupEquiv_symm_apply_simple, Equiv.swap_apply_left]

/-- Reindexing `A₂` by the transposition `Equiv.swap 0 1` conjugates `σ₀` into `σ'₁`, and not into
`σ'₀`: distinct generators act by distinct reflections. -/
example :
    (Finsupp.domLCongr (Equiv.swap (0 : Fin 2) 1)).conj
        ((CoxeterMatrix.A 2).geometricReflection 0) =
      ((CoxeterMatrix.A 2).reindex (Equiv.swap 0 1)).geometricReflection 1 ∧
    (Finsupp.domLCongr (Equiv.swap (0 : Fin 2) 1)).conj
        ((CoxeterMatrix.A 2).geometricReflection 0) ≠
      ((CoxeterMatrix.A 2).reindex (Equiv.swap 0 1)).geometricReflection 0 := by
  have hconj := (CoxeterMatrix.A 2).geometricRepresentation_reindexGroupEquiv_symm
    (Equiv.swap 0 1) ((CoxeterMatrix.A 2).simple 0)
  rw [CoxeterMatrix.reindexGroupEquiv_symm_apply_simple, Equiv.swap_apply_left,
    ← CoxeterMatrix.toCoxeterSystem_simple, ← CoxeterMatrix.toCoxeterSystem_simple,
    CoxeterSystem.geometricRepresentation_simple,
    CoxeterSystem.geometricRepresentation_simple] at hconj
  refine ⟨hconj.symm, ?_⟩
  rw [← hconj]
  intro h
  set cs := ((CoxeterMatrix.A 2).reindex (Equiv.swap 0 1)).toCoxeterSystem
  rw [← cs.geometricRepresentation_simple, ← cs.geometricRepresentation_simple] at h
  exact absurd (cs.simple_injective (cs.geometricRepresentation_injective h)) (by decide)

/-- For `w = s₀ s₁`, both `T ρ(w) α₀` and `ρ'(f w) T α₀` equal `α'₀`. -/
example :
    Finsupp.domLCongr (R := ℝ) (Equiv.swap (0 : Fin 2) 1)
        ((CoxeterMatrix.A 2).toCoxeterSystem.geometricRepresentation
          ((CoxeterMatrix.A 2).simple 0 * (CoxeterMatrix.A 2).simple 1) (Finsupp.single 0 1)) =
      Finsupp.single 0 1 ∧
    ((CoxeterMatrix.A 2).reindex (Equiv.swap 0 1)).toCoxeterSystem.geometricRepresentation
        (((CoxeterMatrix.A 2).reindexGroupEquiv (Equiv.swap 0 1)).symm
          ((CoxeterMatrix.A 2).simple 0 * (CoxeterMatrix.A 2).simple 1))
        (Finsupp.domLCongr (R := ℝ) (Equiv.swap (0 : Fin 2) 1) (Finsupp.single 0 1)) =
      Finsupp.single 0 1 := by
  have h : Finsupp.domLCongr (R := ℝ) (Equiv.swap (0 : Fin 2) 1)
      ((CoxeterMatrix.A 2).toCoxeterSystem.geometricRepresentation
        ((CoxeterMatrix.A 2).simple 0 * (CoxeterMatrix.A 2).simple 1) (Finsupp.single 0 1)) =
      Finsupp.single 0 1 := by
    rw [← CoxeterMatrix.toCoxeterSystem_simple, map_mul, mul_apply_eq_comp,
      CoxeterSystem.geometricRepresentation_simple, CoxeterSystem.geometricRepresentation_simple]
    ext k
    fin_cases k <;> norm_num [CoxeterMatrix.A, cos_pi_div_three]
  refine ⟨h, ?_⟩
  rw [CoxeterMatrix.geometricRepresentation_reindexGroupEquiv_symm,
    LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply, h]

/-- Reindexing along the transposition and then along its inverse sends each generator `sᵢ` to the
generator `sᵢ` of the doubly reindexed system. -/
example (i : Fin 2) :
    (((CoxeterMatrix.A 2).reindex (Equiv.swap 0 1)).reindexGroupEquiv (Equiv.swap 0 1).symm).symm
        (((CoxeterMatrix.A 2).reindexGroupEquiv (Equiv.swap 0 1)).symm
          ((CoxeterMatrix.A 2).simple i)) =
      (((CoxeterMatrix.A 2).reindex (Equiv.swap 0 1)).reindex (Equiv.swap 0 1).symm).simple i := by
  rw [CoxeterMatrix.reindexGroupEquiv_symm_apply_simple,
    CoxeterMatrix.reindexGroupEquiv_symm_apply_simple, Equiv.symm_apply_apply]

end ReindexA₂

/-! ### Three orthogonal nodes and a three-cycle -/

/-- For three orthogonal nodes and `e = (0 1 2)`, the inverse of
`CoxeterMatrix.reindexGroupEquiv` sends generator `0` to generator `1`, whereas the forward map
sends the reindexed generator `0` to the original generator `2`. -/
example :
    ((⊥ : SimpleGraph (Fin 3)).coxeterMatrix.reindexGroupEquiv (finRotate 3)).symm
        ((⊥ : SimpleGraph (Fin 3)).coxeterMatrix.simple 0) =
      ((⊥ : SimpleGraph (Fin 3)).coxeterMatrix.reindex (finRotate 3)).simple 1 ∧
    (⊥ : SimpleGraph (Fin 3)).coxeterMatrix.reindexGroupEquiv (finRotate 3)
        (((⊥ : SimpleGraph (Fin 3)).coxeterMatrix.reindex (finRotate 3)).simple 0) =
      (⊥ : SimpleGraph (Fin 3)).coxeterMatrix.simple 2 :=
  ⟨by simp [CoxeterMatrix.reindexGroupEquiv_symm_apply_simple],
    by
      rw [CoxeterMatrix.reindexGroupEquiv_apply_simple, ← finRotate_last (n := 2),
        Equiv.symm_apply_apply]
      simp⟩

/-! ### Extension by zero from a parabolic subset -/

section Parabolic

variable {B : Type*} (M : CoxeterMatrix B)

/-- For the parabolic subset `{i}`, every Coxeter matrix on it agrees with `M`. -/
example (i : B) (MJ : CoxeterMatrix ({i} : Set B)) (a b : ({i} : Set B)) : MJ a b = M a b := by
  rw [Subsingleton.elim a b, MJ.diagonal, M.diagonal]

/-- For `J = {i}`, extension by zero sends `σᵢ(1) = -1` to `-αᵢ = σᵢ(E 1)`. -/
example (i : B) (MJ : CoxeterMatrix ({i} : Set B)) :
    (MJ.geometricReflection ⟨i, rfl⟩ (Finsupp.single ⟨i, rfl⟩ 1)).mapDomain Subtype.val =
      -Finsupp.single i 1 ∧
    M.geometricReflection i ((Finsupp.single (⟨i, rfl⟩ : ({i} : Set B)) 1).mapDomain Subtype.val) =
      -Finsupp.single i 1 := by
  refine ⟨?_, ?_⟩
  · rw [MJ.geometricReflection_apply_single_self, ← Finsupp.single_neg, Finsupp.mapDomain_single,
      Finsupp.single_neg]
  · rw [Finsupp.mapDomain_single, M.geometricReflection_apply_single_self]

/-- For the empty subset, extension by zero is the zero map out of the zero space. -/
example : Subsingleton ((∅ : Set B) →₀ ℝ) ∧
    Finsupp.lmapDomain ℝ ℝ (Subtype.val : ↥(∅ : Set B) → B) = 0 :=
  ⟨inferInstance, Subsingleton.elim _ _⟩

/-- For the full subset, extension by zero is the coordinate equivalence. -/
example : Finsupp.lmapDomain ℝ ℝ (Subtype.val : ↥(Set.univ : Set B) → B) =
    (Finsupp.domLCongr (Equiv.Set.univ B)).toLinearMap := by
  ext
  simp [Finsupp.domLCongr_apply, Finsupp.equivMapDomain_eq_mapDomain]

end Parabolic

end TauCeti

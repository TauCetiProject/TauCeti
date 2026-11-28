/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Coxeter.Inversion
public import TauCeti.LinearAlgebra.Matrix.Cartan.Realization.Weyl.Coxeter
import TauCeti.GroupTheory.Coxeter.StrongExchange

/-!
# Real roots, real coroots, and reflections in real roots

For a realization `R : CartanRealization A H` of a matrix `A` with diagonal entries `2` over a
field `K`, the **real roots** `R.realRoots hA` (`Φ^re = W · {αᵢ}`) are the Weyl-group translates of
the simple roots, and conjugating `sᵢ` by `w` reflects along `w(αᵢ)` and `w(hᵢ)`
(`TauCeti.CartanRealization.conj_weylSimple_apply`).

When `A` is an integral generalized Cartan matrix and `K` has characteristic zero, Kac's Lemma 3.11
and the strong exchange condition imply that both `w(hᵢ)` and `w sᵢ w⁻¹` are independent of the
presentation `α = w(αᵢ)`, yielding the canonical **real coroot** `α^∨ = w(hᵢ) ∈ H`
(`R.realCoroot`) and **real reflection** `s_α = w sᵢ w⁻¹ ∈ R.weylGroup _` (`R.realReflection`):

* `R.realCoroot` agrees with `R.ambientAction _ w (R.coroot i)` for every `w, i` with `w(αᵢ) = α`
  (`TauCeti.CartanRealization.realCoroot_eq_of_apply_root`), is `W`-equivariant (`(w α)^∨ = w(α^∨)`,
  `TauCeti.CartanRealization.realCoroot_weylGroup_apply_eq_ambientAction`), and satisfies
  `(-α)^∨ = -α^∨` (`TauCeti.CartanRealization.realCoroot_neg`);
* `R.realReflection` agrees with `w sᵢ w⁻¹` for every `w, i` with `w(αᵢ) = α`
  (`TauCeti.CartanRealization.realReflection_eq_of_apply_root`), conjugates equivariantly
  (`s_{w α} = w s_α w⁻¹`, `TauCeti.CartanRealization.realReflection_weylGroup_apply_eq_conj`),
  satisfies `s_{-α} = s_α` (`TauCeti.CartanRealization.realReflection_neg`), and acts as the
  reflection `φ ↦ φ - φ(α^∨) α` (`TauCeti.CartanRealization.realReflection_apply`).

## Main definitions

* `TauCeti.CartanRealization.realRoots`: the set `Φ^re = W · {αᵢ}` of real roots.
* `TauCeti.CartanRealization.realCoroot`: the real coroot `α^∨ ∈ H` attached to `α ∈ Φ^re`
  for a generalized Cartan matrix over a characteristic-zero field.
* `TauCeti.CartanRealization.realReflection`: the reflection `s_α ∈ W` attached to `α ∈ Φ^re`
  for a generalized Cartan matrix over a characteristic-zero field.

## Main results

* `TauCeti.CartanRealization.mem_posRootCone_or_neg_mem_posRootCone_of_mem_realRoots`: every real
  root is either positive (`∈ Q₊`) or negative (`∈ -Q₊`).
* `TauCeti.CartanRealization.realCoroot_eq_ambientAction_coroot`,
  `TauCeti.CartanRealization.realCoroot_weylGroup_apply_eq_ambientAction`,
  `TauCeti.CartanRealization.realCoroot_neg`:
  presentation-independence, Weyl equivariance, and sign behavior of real coroots.
* `TauCeti.CartanRealization.realReflection_eq_conj_weylSimple`,
  `TauCeti.CartanRealization.realReflection_weylGroup_apply_eq_conj`,
  `TauCeti.CartanRealization.realReflection_neg`,
  `TauCeti.CartanRealization.isReflection_realReflection`: presentation-independence, Weyl
  conjugation equivariance, sign invariance, and Coxeter reflection property of real reflections.

## References

* V. G. Kac, *Infinite-dimensional Lie algebras*, third edition, Cambridge University Press, 1990,
  §§3.7, 3.11, 3.13 and Proposition 5.1.
* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, Cambridge University Press, 1990, §5.4.
-/

public section

open Module
open scoped Pointwise

namespace TauCeti.CartanRealization

/-! ### Real roots over an arbitrary field -/

section RealRootsBasic

variable {I K H : Type*} [Field K] [AddCommGroup H] [Module K H]
  {A : Matrix I I K} (R : CartanRealization A H) (hA : ∀ i, A i i = 2)

/-- Multiplying `w` on the right by `sᵢ` negates `w(αᵢ)`. -/
theorem mul_weylSimple_apply_root (w : R.weylGroup hA) (i : I) :
    ((w * R.weylSimple hA i : R.weylGroup hA) : Dual K H ≃ₗ[K] Dual K H) (R.root i) =
      -((w : Dual K H ≃ₗ[K] Dual K H) (R.root i)) := by
  simp [mul_apply_eq_comp]

/-- Conjugating `sᵢ` by `w` reflects along `w(αᵢ)` and `w(hᵢ)`. -/
theorem conj_weylSimple_apply (w : R.weylGroup hA) (i : I) (φ : Dual K H) :
    ((w * R.weylSimple hA i * w⁻¹ : R.weylGroup hA) : Dual K H ≃ₗ[K] Dual K H) φ =
      φ - φ (R.ambientAction hA w (R.coroot i)) •
        ((w : Dual K H ≃ₗ[K] Dual K H) (R.root i)) := by
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_apply_eq_comp, coe_weylSimple,
    simpleReflection_apply, map_sub, map_smul]
  have hval : ((w : Dual K H ≃ₗ[K] Dual K H)⁻¹ φ) (R.coroot i) =
      φ (R.ambientAction hA w (R.coroot i)) := by
    rw [← Subgroup.coe_inv, R.weylGroup_apply_apply hA w⁻¹ φ (R.coroot i), inv_inv]
  rw [hval, ← mul_apply_eq_comp, mul_inv_cancel]
  simp

/-- The **real roots** `Φ^re = W · {αᵢ}` of the realization. -/
noncomputable def realRoots : Set (Dual K H) :=
  ⋃ i, MulAction.orbit (R.weylGroup hA) (R.root i)

theorem mem_realRoots_iff {α : Dual K H} :
    α ∈ R.realRoots hA ↔
      ∃ (w : R.weylGroup hA) (i : I), (w : Dual K H ≃ₗ[K] Dual K H) (R.root i) = α := by
  simp only [realRoots, Set.mem_iUnion, MulAction.mem_orbit_iff, Subgroup.smul_def,
    LinearEquiv.smul_def]
  exact exists_comm

@[simp]
theorem root_mem_realRoots (i : I) : R.root i ∈ R.realRoots hA :=
  (R.mem_realRoots_iff hA).mpr ⟨1, i, by simp⟩

theorem apply_root_mem_realRoots (w : R.weylGroup hA) (i : I) :
    (w : Dual K H ≃ₗ[K] Dual K H) (R.root i) ∈ R.realRoots hA :=
  (R.mem_realRoots_iff hA).mpr ⟨w, i, rfl⟩

/-- Weyl-group translates preserve and reflect membership in the real roots. -/
@[simp]
theorem apply_mem_realRoots_iff (w : R.weylGroup hA) {α : Dual K H} :
    (w : Dual K H ≃ₗ[K] Dual K H) α ∈ R.realRoots hA ↔ α ∈ R.realRoots hA := by
  have hsmul : w • R.realRoots hA = R.realRoots hA := by
    simp only [realRoots, Set.smul_set_iUnion, MulAction.smul_orbit]
  rw [← LinearEquiv.smul_def, ← Subgroup.smul_def w α]
  nth_rw 1 [← hsmul]
  exact Set.smul_mem_smul_set_iff (a := w) (x := α) (s := R.realRoots hA)

/-- Negation preserves and reflects membership in the real roots. -/
@[simp]
theorem neg_mem_realRoots_iff {α : Dual K H} :
    -α ∈ R.realRoots hA ↔ α ∈ R.realRoots hA := by
  have hmaps {β : Dual K H} (hβ : β ∈ R.realRoots hA) : -β ∈ R.realRoots hA := by
    obtain ⟨w, i, rfl⟩ := (R.mem_realRoots_iff hA).mp hβ
    exact (R.mem_realRoots_iff hA).mpr
      ⟨w * R.weylSimple hA i, i, R.mul_weylSimple_apply_root hA w i⟩
  exact ⟨fun h ↦ by simpa using hmaps h, hmaps⟩

/-- Every real root is nonzero. -/
theorem ne_zero_of_mem_realRoots {α : Dual K H} (hα : α ∈ R.realRoots hA) : α ≠ 0 := by
  obtain ⟨w, i, rfl⟩ := (R.mem_realRoots_iff hA).mp hα
  exact (map_ne_zero_iff _ (w : Dual K H ≃ₗ[K] Dual K H).injective).mpr
    (R.root_linearIndependent.ne_zero i)

end RealRootsBasic

/-! ### Integral matrices: real roots lie in the root lattice -/

section RealRootsIntegral

variable {I K H : Type*} [Field K] [AddCommGroup H] [Module K H]
  {A : Matrix I I ℤ} (R : CartanRealization (A.map (Int.cast : ℤ → K)) H)

/-- Every real root lies in the root lattice `Q`. -/
theorem realRoots_subset_rootLattice (hA : ∀ i, (A.map (Int.cast : ℤ → K)) i i = 2) :
    R.realRoots hA ⊆ R.rootLattice := by
  intro _ hα
  obtain ⟨w, i, rfl⟩ := (R.mem_realRoots_iff hA).mp hα
  exact (R.apply_mem_rootLattice_iff_of_mem_weylGroup hA w.property).mpr (R.root_mem_rootLattice i)

end RealRootsIntegral

/-! ### Generalized Cartan matrices in characteristic zero: real coroots and reflections -/

section RealRootsCoxeter

variable {I K H : Type*} [Field K] [CharZero K] [AddCommGroup H] [Module K H]
  {A : Matrix I I ℤ} (R : CartanRealization (A.map (Int.cast : ℤ → K)) H)

/-- **Every real root is either positive or negative.** -/
theorem mem_posRootCone_or_neg_mem_posRootCone_of_mem_realRoots (hdiag : ∀ i, A i i = 2)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (hzero : ∀ i j, A i j = 0 ↔ A j i = 0)
    {α : Dual K H} (hα : α ∈ R.realRoots (diag_map_intCast hdiag)) :
    α ∈ R.posRootCone ∨ -α ∈ R.posRootCone := by
  obtain ⟨w, i, rfl⟩ := (R.mem_realRoots_iff (diag_map_intCast hdiag)).mp hα
  exact R.apply_root_mem_posRootCone_or_neg_mem_posRootCone hdiag hoff hzero w i

/-- If `w₁(αᵢ) = w₂(αⱼ)`, then strong exchange gives `w₁ sᵢ w₁⁻¹ = w₂ sⱼ w₂⁻¹`. -/
private theorem conj_weylSimple_eq_of_apply_root_eq (hdiag : ∀ i, A i i = 2)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (hzero : ∀ i j, A i j = 0 ↔ A j i = 0)
    {w₁ w₂ : R.weylGroup (diag_map_intCast hdiag)} {i j : I}
    (hw : (w₁ : Dual K H ≃ₗ[K] Dual K H) (R.root i) =
      (w₂ : Dual K H ≃ₗ[K] Dual K H) (R.root j)) :
    w₁ * R.weylSimple (diag_map_intCast hdiag) i * w₁⁻¹ =
      w₂ * R.weylSimple (diag_map_intCast hdiag) j * w₂⁻¹ := by
  classical
  let cs := R.weylCoxeterSystem hdiag hoff hzero
  let u := w₁⁻¹ * w₂
  have huj : (u : Dual K H ≃ₗ[K] Dual K H) (R.root j) = R.root i := by
    simp [u, mul_apply_eq_comp, ← hw]
  have huinv_i : (u⁻¹ : Dual K H ≃ₗ[K] Dual K H) (R.root i) = R.root j := by
    rw [← huj, ← mul_apply_eq_comp, inv_mul_cancel, one_apply_eq_self]
  have hnd_uj : ¬ cs.IsRightDescent u j :=
    (R.not_isRightDescent_weylCoxeterSystem_iff hdiag hoff hzero u j).mpr
      (huj ▸ R.root_mem_posRootCone i)
  have hnd_uinv_i : ¬ cs.IsRightDescent u⁻¹ i :=
    (R.not_isRightDescent_weylCoxeterSystem_iff hdiag hoff hzero u⁻¹ i).mpr
      (huinv_i ▸ R.root_mem_posRootCone j)
  have hd_siu_j : cs.IsRightDescent (cs.simple i * u) j := by
    rw [R.isRightDescent_weylCoxeterSystem_iff hdiag hoff hzero, R.weylCoxeterSystem_simple]
    simp only [Subgroup.coe_mul, mul_apply_eq_comp, huj, coe_weylSimple,
      simpleReflection_root_self, neg_neg]
    exact R.root_mem_posRootCone i
  have hlen_usj : cs.length (u * cs.simple j) = cs.length u + 1 :=
    cs.not_isRightDescent_iff.mp hnd_uj
  have hlen_siu : cs.length (cs.simple i * u) = cs.length u + 1 :=
    cs.not_isLeftDescent_iff.mp (cs.isRightDescent_inv_iff.not.mp hnd_uinv_i)
  have hlen_both : cs.length (cs.simple i * u * cs.simple j) = cs.length u := by
    have := cs.isRightDescent_iff.mp hd_siu_j
    omega
  have hcomm : cs.simple i * u = u * cs.simple j :=
    cs.simple_mul_eq_mul_simple_of_length_eq hlen_both (hlen_siu.trans hlen_usj.symm)
  rw [R.weylCoxeterSystem_simple, R.weylCoxeterSystem_simple] at hcomm
  have hconj_u : u * R.weylSimple (diag_map_intCast hdiag) j * u⁻¹ =
      R.weylSimple (diag_map_intCast hdiag) i := by
    rw [← hcomm, mul_inv_cancel_right]
  rw [← hconj_u]
  simp [u, mul_assoc]

/-- If `w₁(αᵢ) = w₂(αⱼ)`, comparing the reflection formulas against `Dual K H` gives
`w₁(hᵢ) = w₂(hⱼ)`. -/
private theorem ambientAction_coroot_eq_of_apply_root_eq (hdiag : ∀ i, A i i = 2)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (hzero : ∀ i j, A i j = 0 ↔ A j i = 0)
    {w₁ w₂ : R.weylGroup (diag_map_intCast hdiag)} {i j : I}
    (hw : (w₁ : Dual K H ≃ₗ[K] Dual K H) (R.root i) =
      (w₂ : Dual K H ≃ₗ[K] Dual K H) (R.root j)) :
    R.ambientAction (diag_map_intCast hdiag) w₁ (R.coroot i) =
      R.ambientAction (diag_map_intCast hdiag) w₂ (R.coroot j) := by
  have hconj := R.conj_weylSimple_eq_of_apply_root_eq hdiag hoff hzero hw
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff K]
  intro φ
  have hφ : ((w₁ * R.weylSimple (diag_map_intCast hdiag) i * w₁⁻¹ :
      R.weylGroup (diag_map_intCast hdiag)) : Dual K H ≃ₗ[K] Dual K H) φ =
      ((w₂ * R.weylSimple (diag_map_intCast hdiag) j * w₂⁻¹ :
        R.weylGroup (diag_map_intCast hdiag)) : Dual K H ≃ₗ[K] Dual K H) φ := by
    rw [hconj]
  rw [R.conj_weylSimple_apply, R.conj_weylSimple_apply, ← hw, sub_right_inj] at hφ
  have hsub : (φ (R.ambientAction (diag_map_intCast hdiag) w₁ (R.coroot i)) -
      φ (R.ambientAction (diag_map_intCast hdiag) w₂ (R.coroot j))) •
        ((w₁ : Dual K H ≃ₗ[K] Dual K H) (R.root i)) = 0 :=
    (sub_smul _ _ ((w₁ : Dual K H ≃ₗ[K] Dual K H) (R.root i))).trans (by rw [hφ, sub_self])
  rw [← map_sub] at hsub
  exact (smul_eq_zero.mp hsub).resolve_right
    (R.ne_zero_of_mem_realRoots (diag_map_intCast hdiag)
      (R.apply_root_mem_realRoots (diag_map_intCast hdiag) w₁ i))

/-- Existence of a presentation-independent real coroot for `α`. -/
private theorem exists_realCoroot (hdiag : ∀ i, A i i = 2)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (hzero : ∀ i j, A i j = 0 ↔ A j i = 0)
    {α : Dual K H} (hα : α ∈ R.realRoots (diag_map_intCast hdiag)) :
    ∃ h : H, ∀ (w : R.weylGroup (diag_map_intCast hdiag)) (i : I),
      (w : Dual K H ≃ₗ[K] Dual K H) (R.root i) = α →
      h = R.ambientAction (diag_map_intCast hdiag) w (R.coroot i) := by
  obtain ⟨w₀, i₀, hw₀⟩ := (R.mem_realRoots_iff (diag_map_intCast hdiag)).mp hα
  exact ⟨R.ambientAction (diag_map_intCast hdiag) w₀ (R.coroot i₀), fun w i hw ↦
    R.ambientAction_coroot_eq_of_apply_root_eq hdiag hoff hzero (hw₀.trans hw.symm)⟩

/-- **The real coroot `α^∨ ∈ H`** attached to a real root
`α ∈ R.realRoots (diag_map_intCast hdiag)` of a generalized Cartan matrix over a
characteristic-zero field. It equals `w(hᵢ)` for every presentation `α = w(αᵢ)` (see
`TauCeti.CartanRealization.realCoroot_eq_of_apply_root` and
`TauCeti.CartanRealization.realCoroot_eq_ambientAction_coroot`). -/
noncomputable def realCoroot (hdiag : ∀ i, A i i = 2)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (hzero : ∀ i j, A i j = 0 ↔ A j i = 0)
    {α : Dual K H} (hα : α ∈ R.realRoots (diag_map_intCast hdiag)) : H :=
  (R.exists_realCoroot hdiag hoff hzero hα).choose

/-- `R.realCoroot` equals `w(hᵢ)` for every presentation `α = w(αᵢ)`. -/
theorem realCoroot_eq_of_apply_root (hdiag : ∀ i, A i i = 2)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (hzero : ∀ i j, A i j = 0 ↔ A j i = 0)
    {α : Dual K H} (hα : α ∈ R.realRoots (diag_map_intCast hdiag))
    {w : R.weylGroup (diag_map_intCast hdiag)} {i : I}
    (hw : (w : Dual K H ≃ₗ[K] Dual K H) (R.root i) = α) :
    R.realCoroot hdiag hoff hzero hα =
      R.ambientAction (diag_map_intCast hdiag) w (R.coroot i) :=
  (R.exists_realCoroot hdiag hoff hzero hα).choose_spec w i hw

/-- `(w αᵢ)^∨ = w(hᵢ)`, independently of the presentation of the real root. -/
@[simp]
theorem realCoroot_eq_ambientAction_coroot (hdiag : ∀ i, A i i = 2)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (hzero : ∀ i j, A i j = 0 ↔ A j i = 0)
    (w : R.weylGroup (diag_map_intCast hdiag)) (i : I)
    (hα : (w : Dual K H ≃ₗ[K] Dual K H) (R.root i) ∈ R.realRoots (diag_map_intCast hdiag) :=
      R.apply_root_mem_realRoots (diag_map_intCast hdiag) w i) :
    R.realCoroot hdiag hoff hzero hα =
      R.ambientAction (diag_map_intCast hdiag) w (R.coroot i) :=
  R.realCoroot_eq_of_apply_root hdiag hoff hzero hα rfl

/-- Every real root evaluates to `2` on its real coroot. -/
@[simp]
theorem apply_realCoroot_self (hdiag : ∀ i, A i i = 2)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (hzero : ∀ i j, A i j = 0 ↔ A j i = 0)
    {α : Dual K H} (hα : α ∈ R.realRoots (diag_map_intCast hdiag)) :
    α (R.realCoroot hdiag hoff hzero hα) = 2 := by
  obtain ⟨w, i, rfl⟩ := (R.mem_realRoots_iff (diag_map_intCast hdiag)).mp hα
  rw [R.realCoroot_eq_ambientAction_coroot hdiag hoff hzero w i,
    R.apply_ambientAction (diag_map_intCast hdiag), R.root_coroot_two (diag_map_intCast hdiag)]

@[simp]
theorem realCoroot_root (hdiag : ∀ i, A i i = 2)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (hzero : ∀ i j, A i j = 0 ↔ A j i = 0) (i : I) :
    R.realCoroot hdiag hoff hzero (R.root_mem_realRoots (diag_map_intCast hdiag) i) =
      R.coroot i := by
  rw [R.realCoroot_eq_of_apply_root hdiag hoff hzero (R.root_mem_realRoots _ i)
      (w := 1) (i := i) (by simp), map_one, one_apply_eq_self]

/-- **Equivariance of real coroots**: `(w α)^∨ = w(α^∨)`. -/
theorem realCoroot_weylGroup_apply_eq_ambientAction (hdiag : ∀ i, A i i = 2)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (hzero : ∀ i j, A i j = 0 ↔ A j i = 0)
    (w : R.weylGroup (diag_map_intCast hdiag)) {α : Dual K H}
    (hα : α ∈ R.realRoots (diag_map_intCast hdiag)) :
    R.realCoroot hdiag hoff hzero
        ((R.apply_mem_realRoots_iff (diag_map_intCast hdiag) w).mpr hα) =
      R.ambientAction (diag_map_intCast hdiag) w (R.realCoroot hdiag hoff hzero hα) := by
  obtain ⟨u, i, rfl⟩ := (R.mem_realRoots_iff (diag_map_intCast hdiag)).mp hα
  rw [R.realCoroot_eq_of_apply_root hdiag hoff hzero _
      (by rw [Subgroup.coe_mul, mul_apply_eq_comp]),
    map_mul, mul_apply_eq_comp, R.realCoroot_eq_ambientAction_coroot hdiag hoff hzero u i]

/-- Negating a real root negates its real coroot: `(-α)^∨ = -α^∨`. -/
@[simp]
theorem realCoroot_neg (hdiag : ∀ i, A i i = 2)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (hzero : ∀ i j, A i j = 0 ↔ A j i = 0)
    {α : Dual K H} (hα : -α ∈ R.realRoots (diag_map_intCast hdiag)) :
    R.realCoroot hdiag hoff hzero hα =
      -R.realCoroot hdiag hoff hzero
        ((R.neg_mem_realRoots_iff (diag_map_intCast hdiag)).mp hα) := by
  have hmem : α ∈ R.realRoots (diag_map_intCast hdiag) :=
    (R.neg_mem_realRoots_iff (diag_map_intCast hdiag)).mp hα
  obtain ⟨w, i, rfl⟩ := (R.mem_realRoots_iff (diag_map_intCast hdiag)).mp hmem
  rw [R.realCoroot_eq_ambientAction_coroot hdiag hoff hzero w i,
    R.realCoroot_eq_of_apply_root hdiag hoff hzero hα
      (R.mul_weylSimple_apply_root (diag_map_intCast hdiag) w i),
    map_mul, mul_apply_eq_comp, ambientAction_weylSimple, simpleCoreflection_coroot_self, map_neg]

/-- Existence of a presentation-independent real reflection for `α`. -/
private theorem exists_realReflection (hdiag : ∀ i, A i i = 2)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (hzero : ∀ i j, A i j = 0 ↔ A j i = 0)
    {α : Dual K H} (hα : α ∈ R.realRoots (diag_map_intCast hdiag)) :
    ∃ s : R.weylGroup (diag_map_intCast hdiag),
      ∀ (w : R.weylGroup (diag_map_intCast hdiag)) (i : I),
        (w : Dual K H ≃ₗ[K] Dual K H) (R.root i) = α →
        s = w * R.weylSimple (diag_map_intCast hdiag) i * w⁻¹ := by
  obtain ⟨w₀, i₀, hw₀⟩ := (R.mem_realRoots_iff (diag_map_intCast hdiag)).mp hα
  exact ⟨w₀ * R.weylSimple (diag_map_intCast hdiag) i₀ * w₀⁻¹, fun w i hw ↦
    R.conj_weylSimple_eq_of_apply_root_eq hdiag hoff hzero (hw₀.trans hw.symm)⟩

/-- **The reflection `s_α ∈ R.weylGroup (diag_map_intCast hdiag)` attached to a real root
`α ∈ R.realRoots (diag_map_intCast hdiag)`** (not defined for imaginary roots) of a generalized
Cartan matrix over a characteristic-zero field. It equals `w sᵢ w⁻¹` for every presentation
`α = w(αᵢ)` (see `TauCeti.CartanRealization.realReflection_eq_of_apply_root` and
`TauCeti.CartanRealization.realReflection_eq_conj_weylSimple`). -/
noncomputable def realReflection (hdiag : ∀ i, A i i = 2)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (hzero : ∀ i j, A i j = 0 ↔ A j i = 0)
    {α : Dual K H} (hα : α ∈ R.realRoots (diag_map_intCast hdiag)) :
    R.weylGroup (diag_map_intCast hdiag) :=
  (R.exists_realReflection hdiag hoff hzero hα).choose

/-- `R.realReflection` equals `w sᵢ w⁻¹` for every presentation `α = w(αᵢ)`. -/
theorem realReflection_eq_of_apply_root (hdiag : ∀ i, A i i = 2)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (hzero : ∀ i j, A i j = 0 ↔ A j i = 0)
    {α : Dual K H} (hα : α ∈ R.realRoots (diag_map_intCast hdiag))
    {w : R.weylGroup (diag_map_intCast hdiag)} {i : I}
    (hw : (w : Dual K H ≃ₗ[K] Dual K H) (R.root i) = α) :
    R.realReflection hdiag hoff hzero hα =
      w * R.weylSimple (diag_map_intCast hdiag) i * w⁻¹ :=
  (R.exists_realReflection hdiag hoff hzero hα).choose_spec w i hw

/-- The reflection attached to `w(αᵢ)` equals `w sᵢ w⁻¹`, independently of the presentation of the
real root. -/
@[simp]
theorem realReflection_eq_conj_weylSimple (hdiag : ∀ i, A i i = 2)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (hzero : ∀ i j, A i j = 0 ↔ A j i = 0)
    (w : R.weylGroup (diag_map_intCast hdiag)) (i : I)
    (hα : (w : Dual K H ≃ₗ[K] Dual K H) (R.root i) ∈ R.realRoots (diag_map_intCast hdiag) :=
      R.apply_root_mem_realRoots (diag_map_intCast hdiag) w i) :
    R.realReflection hdiag hoff hzero hα =
      w * R.weylSimple (diag_map_intCast hdiag) i * w⁻¹ :=
  R.realReflection_eq_of_apply_root hdiag hoff hzero hα rfl

/-- `s_α` acts on `Dual K H` by the reflection formula `φ ↦ φ - φ(α^∨) • α`. -/
theorem realReflection_apply (hdiag : ∀ i, A i i = 2)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (hzero : ∀ i j, A i j = 0 ↔ A j i = 0)
    {α : Dual K H} (hα : α ∈ R.realRoots (diag_map_intCast hdiag)) (φ : Dual K H) :
    ((R.realReflection hdiag hoff hzero hα : R.weylGroup (diag_map_intCast hdiag)) :
        Dual K H ≃ₗ[K] Dual K H) φ =
      φ - φ (R.realCoroot hdiag hoff hzero hα) • α := by
  obtain ⟨w, i, rfl⟩ := (R.mem_realRoots_iff (diag_map_intCast hdiag)).mp hα
  rw [R.realReflection_eq_conj_weylSimple hdiag hoff hzero w i,
    R.realCoroot_eq_ambientAction_coroot hdiag hoff hzero w i,
    R.conj_weylSimple_apply (diag_map_intCast hdiag)]

@[simp]
theorem realReflection_apply_self (hdiag : ∀ i, A i i = 2)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (hzero : ∀ i j, A i j = 0 ↔ A j i = 0)
    {α : Dual K H} (hα : α ∈ R.realRoots (diag_map_intCast hdiag)) :
    ((R.realReflection hdiag hoff hzero hα : R.weylGroup (diag_map_intCast hdiag)) :
        Dual K H ≃ₗ[K] Dual K H) α = -α := by
  rw [R.realReflection_apply hdiag hoff hzero hα α, R.apply_realCoroot_self, two_smul,
    sub_add_cancel_left]

/-- Every real reflection is a Coxeter reflection in `R.weylCoxeterSystem`. -/
theorem isReflection_realReflection [DecidableEq I] (hdiag : ∀ i, A i i = 2)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (hzero : ∀ i j, A i j = 0 ↔ A j i = 0)
    {α : Dual K H} (hα : α ∈ R.realRoots (diag_map_intCast hdiag)) :
    (R.weylCoxeterSystem hdiag hoff hzero).IsReflection
      (R.realReflection hdiag hoff hzero hα) := by
  obtain ⟨w, i, rfl⟩ := (R.mem_realRoots_iff (diag_map_intCast hdiag)).mp hα
  exact ⟨w, i, by rw [R.weylCoxeterSystem_simple, R.realReflection_eq_conj_weylSimple]⟩

@[simp]
theorem realReflection_mul_self (hdiag : ∀ i, A i i = 2)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (hzero : ∀ i j, A i j = 0 ↔ A j i = 0)
    {α : Dual K H} (hα : α ∈ R.realRoots (diag_map_intCast hdiag)) :
    R.realReflection hdiag hoff hzero hα * R.realReflection hdiag hoff hzero hα = 1 := by
  classical
  exact (R.isReflection_realReflection hdiag hoff hzero hα).mul_self

@[simp]
theorem realReflection_inv (hdiag : ∀ i, A i i = 2)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (hzero : ∀ i j, A i j = 0 ↔ A j i = 0)
    {α : Dual K H} (hα : α ∈ R.realRoots (diag_map_intCast hdiag)) :
    (R.realReflection hdiag hoff hzero hα)⁻¹ = R.realReflection hdiag hoff hzero hα := by
  classical
  exact (R.isReflection_realReflection hdiag hoff hzero hα).inv

@[simp]
theorem realReflection_root (hdiag : ∀ i, A i i = 2)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (hzero : ∀ i j, A i j = 0 ↔ A j i = 0) (i : I) :
    R.realReflection hdiag hoff hzero (R.root_mem_realRoots (diag_map_intCast hdiag) i) =
      R.weylSimple (diag_map_intCast hdiag) i := by
  rw [R.realReflection_eq_of_apply_root hdiag hoff hzero (R.root_mem_realRoots _ i)
      (w := 1) (i := i) (by simp), one_mul, inv_one, mul_one]

/-- **Weyl equivariance of real reflections**: `s_{w α} = w * s_α * w⁻¹`. -/
theorem realReflection_weylGroup_apply_eq_conj (hdiag : ∀ i, A i i = 2)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (hzero : ∀ i j, A i j = 0 ↔ A j i = 0)
    (w : R.weylGroup (diag_map_intCast hdiag)) {α : Dual K H}
    (hα : α ∈ R.realRoots (diag_map_intCast hdiag)) :
    R.realReflection hdiag hoff hzero
        ((R.apply_mem_realRoots_iff (diag_map_intCast hdiag) w).mpr hα) =
      w * R.realReflection hdiag hoff hzero hα * w⁻¹ := by
  obtain ⟨u, i, rfl⟩ := (R.mem_realRoots_iff (diag_map_intCast hdiag)).mp hα
  rw [R.realReflection_eq_of_apply_root hdiag hoff hzero _
      (by rw [Subgroup.coe_mul, mul_apply_eq_comp]),
    R.realReflection_eq_conj_weylSimple hdiag hoff hzero u i]
  simp [mul_assoc]

/-- Negating a real root preserves its real reflection: `s_{-α} = s_α`. -/
@[simp]
theorem realReflection_neg (hdiag : ∀ i, A i i = 2)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (hzero : ∀ i j, A i j = 0 ↔ A j i = 0)
    {α : Dual K H} (hα : -α ∈ R.realRoots (diag_map_intCast hdiag)) :
    R.realReflection hdiag hoff hzero hα =
      R.realReflection hdiag hoff hzero
        ((R.neg_mem_realRoots_iff (diag_map_intCast hdiag)).mp hα) := by
  have hmem : α ∈ R.realRoots (diag_map_intCast hdiag) :=
    (R.neg_mem_realRoots_iff (diag_map_intCast hdiag)).mp hα
  obtain ⟨w, i, rfl⟩ := (R.mem_realRoots_iff (diag_map_intCast hdiag)).mp hmem
  rw [R.realReflection_eq_conj_weylSimple hdiag hoff hzero w i,
    R.realReflection_eq_of_apply_root hdiag hoff hzero hα
      (R.mul_weylSimple_apply_root (diag_map_intCast hdiag) w i)]
  simp [mul_assoc]

end RealRootsCoxeter

end TauCeti.CartanRealization

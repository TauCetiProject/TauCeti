/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Cartan.Realization.WeylGroup

/-!
# Real roots, real coroots, and real reflections of a Cartan realization

For a `TauCeti.CartanRealization` `R` of a generalized Cartan matrix `A` over a characteristic-zero
field `K`, the **real roots** `Δ^re` (`realRoots`) are the Weyl-group translates `w • αᵢ` of the
simple roots, and `Δ₊^re = Δ^re ∩ Q₊` (`posRealRoots`) are the positive real roots (Kac, §5.1).
We prove indivisibility in `Q` (`eq_one_or_neg_one_of_zsmul_mem_realRoots`), sign dichotomy,
stability of `Δ₊^re \ {αᵢ}` under `sᵢ`, and word-independent `realCoroot` and `realReflection`.
-/

public section

open Module

namespace TauCeti.CartanRealization

section Integral

variable {I K H : Type*} [Field K] [AddCommGroup H] [Module K H] {A : Matrix I I ℤ}
  (R : CartanRealization (A.map (Int.cast : ℤ → K)) H)

section

variable (hdiag : ∀ i, A.map (Int.cast : ℤ → K) i i = 2)

/-- The **real roots** `Δ^re` of a Cartan realization: the Weyl-group orbit of the simple roots. -/
def realRoots : Set (Dual K H) := {α | ∃ (w : R.weylGroup hdiag) (i : I), w • R.root i = α}

/-- The **positive real roots** `Δ₊^re = Δ^re ∩ Q₊`. -/
def posRealRoots : Set (Dual K H) := R.realRoots hdiag ∩ R.posRootCone

theorem root_mem_realRoots (i : I) : R.root i ∈ R.realRoots hdiag := ⟨1, i, one_smul _ _⟩
theorem smul_root_mem_realRoots (w : R.weylGroup hdiag) (i : I) :
    w • R.root i ∈ R.realRoots hdiag := ⟨w, i, rfl⟩
theorem smul_mem_realRoots (w : R.weylGroup hdiag) {α : Dual K H} (hα : α ∈ R.realRoots hdiag) :
    w • α ∈ R.realRoots hdiag :=
  let ⟨u, i, hu⟩ := hα; ⟨w * u, i, (mul_smul w u (R.root i)).symm.trans (congrArg (w • ·) hu)⟩
theorem neg_mem_realRoots {α : Dual K H} (hα : α ∈ R.realRoots hdiag) : -α ∈ R.realRoots hdiag := by
  obtain ⟨w, i, rfl⟩ := hα; refine ⟨w * R.simpleReflectionMem hdiag i, i, ?_⟩
  rw [mul_smul, show R.simpleReflectionMem hdiag i • R.root i = -R.root i by
    simp [Subgroup.smul_def, LinearEquiv.smul_def], smul_neg]
theorem zero_notMem_realRoots : (0 : Dual K H) ∉ R.realRoots hdiag := fun ⟨_, i, h0⟩ ↦
  R.root_linearIndependent.ne_zero i (by simpa [Subgroup.smul_def, LinearEquiv.smul_def] using h0)
theorem realRoots_subset_rootLattice : R.realRoots hdiag ⊆ R.rootLattice := fun _ ⟨w, i, h⟩ ↦
  h ▸ R.smul_mem_rootLattice hdiag w (R.root_mem_rootLattice i)
theorem root_mem_posRealRoots (i : I) : R.root i ∈ R.posRealRoots hdiag :=
  ⟨R.root_mem_realRoots hdiag i, R.root_mem_posRootCone i⟩

end

theorem exists_int_apply_coroot_of_mem_rootLattice {α : Dual K H} (hα : α ∈ R.rootLattice)
    (i : I) : ∃ m : ℤ, α (R.coroot i) = m := by
  rw [R.rootLattice_def] at hα
  induction hα using Submodule.span_induction with
  | mem _ hx => obtain ⟨j, rfl⟩ := hx; exact ⟨A i j, by simp [R.root_coroot]⟩
  | zero => exact ⟨0, by simp⟩
  | add _ _ _ _ ihx ihy =>
    obtain ⟨m₁, hm₁⟩ := ihx; obtain ⟨m₂, hm₂⟩ := ihy; exact ⟨m₁ + m₂, by simp [hm₁, hm₂]⟩
  | smul n _ _ ih => obtain ⟨m, hm⟩ := ih; exact ⟨n * m, by simp [hm]⟩

end Integral

section CharZero

variable {I K H : Type*} [Field K] [CharZero K] [AddCommGroup H] [Module K H] {A : Matrix I I ℤ}
  (R : CartanRealization (A.map (Int.cast : ℤ → K)) H)

/-- **Real roots are indivisible in the root lattice** (Kac, Proposition 5.1(b)). -/
theorem eq_one_or_neg_one_of_zsmul_mem_realRoots (hdiag : ∀ i, A.map (Int.cast : ℤ → K) i i = 2)
    {n : ℤ} {β : Dual K H} (hβ : β ∈ R.rootLattice) (hn : n • β ∈ R.realRoots hdiag) :
    n = 1 ∨ n = -1 := by
  obtain ⟨w, i, hwi⟩ := hn
  have hγ := R.smul_mem_rootLattice hdiag w⁻¹ hβ
  have hroot : R.root i = n • (w⁻¹ • β) :=
    (inv_smul_smul w (R.root i)).symm.trans ((congrArg (w⁻¹ • ·) hwi).trans (smul_comm w⁻¹ n β))
  let hli := R.root_linearIndependent.restrict_scalars' ℤ
  have hrepr : hli.repr ⟨R.root i, R.rootLattice_def ▸ R.root_mem_rootLattice i⟩ =
      n • hli.repr ⟨w⁻¹ • β, R.rootLattice_def ▸ hγ⟩ :=
    (congrArg hli.repr (Subtype.ext hroot)).trans (map_zsmul _ _ _)
  rw [hli.repr_eq_single i _ rfl] at hrepr
  exact Int.isUnit_iff.mp <| IsUnit.of_mul_eq_one _ <| by
    simpa using (congrArg (fun f : I →₀ ℤ ↦ f i) hrepr).symm

private theorem exists_nsmul_root_of_add_eq_nsmul_root {α β : Dual K H}
    (hα : α ∈ R.posRootCone) (hβ : β ∈ R.posRootCone) {i : I} {k : ℕ}
    (hsum : α + β = k • R.root i) : ∃ c : ℕ, α = c • R.root i := by
  let hli := R.linearIndependent_nat_root
  let x : Submodule.span ℕ (Set.range R.root) := ⟨α, R.posRootCone_def ▸ hα⟩
  let y : Submodule.span ℕ (Set.range R.root) := ⟨β, R.posRootCone_def ▸ hβ⟩
  have hrepr : hli.repr x + hli.repr y = Finsupp.single i k := by
    rw [← map_add, show x + y = k • ⟨R.root i, R.posRootCone_def ▸ R.root_mem_posRootCone i⟩ from
      Subtype.ext hsum, map_nsmul, hli.repr_eq_single i _ rfl, Finsupp.smul_single_one]
  have hx_single : hli.repr x = Finsupp.single i (hli.repr x i) := by
    ext j; rcases eq_or_ne j i with rfl | hji
    · simp
    · have hj := congrArg (fun f : I →₀ ℕ ↦ f j) hrepr
      simp only [Finsupp.add_apply, Finsupp.single_eq_of_ne hji] at hj ⊢; omega
  exact ⟨hli.repr x i, ((Finsupp.linearCombination_single _ _ _).symm.trans
    (hx_single ▸ hli.linearCombination_repr x)).symm⟩

variable (hA : A.IsGeneralizedCartan)

theorem mem_posRootCone_or_neg_mem_posRootCone_of_mem_realRoots
    {α : Dual K H} (hα : α ∈ R.realRoots (hA.diag_map K)) :
    α ∈ R.posRootCone ∨ -α ∈ R.posRootCone := by
  obtain ⟨w, i, rfl⟩ := hα
  exact (em ((R.weylCoxeterSystem hA).IsRightDescent w i)).symm.imp
    (R.not_isRightDescent_weylCoxeterSystem_iff hA w i).mp
    (R.isRightDescent_weylCoxeterSystem_iff hA w i).mp

theorem simpleReflection_mem_posRealRoots (i : I) {α : Dual K H}
    (hα : α ∈ R.posRealRoots (hA.diag_map K)) (hne : α ≠ R.root i) :
    R.simpleReflection (hA.diag_map K) i α ∈ R.posRealRoots (hA.diag_map K) := by
  have hreal : R.simpleReflection (hA.diag_map K) i α ∈ R.realRoots (hA.diag_map K) := by
    simpa [Subgroup.smul_def, LinearEquiv.smul_def] using
      R.smul_mem_realRoots (hA.diag_map K) (R.simpleReflectionMem (hA.diag_map K) i) hα.1
  refine ⟨hreal, (R.mem_posRootCone_or_neg_mem_posRootCone_of_mem_realRoots hA hreal).resolve_right
    fun hneg ↦ ?_⟩
  obtain ⟨m, hm⟩ := R.exists_int_apply_coroot_of_mem_rootLattice
    (R.realRoots_subset_rootLattice (hA.diag_map K) hα.1) i
  have hsum : α + -(R.simpleReflection (hA.diag_map K) i α) = m • R.root i := by
    rw [simpleReflection_apply, hm, Int.cast_smul_eq_zsmul K m (R.root i)]; abel
  rcases le_or_gt m 0 with hm0 | hmpos
  · have hpt : α + -(R.simpleReflection (hA.diag_map K) i α) = 0 := by
      refine R.isPointed_posRootCone _ (add_mem hα.2 hneg) ?_
      rw [hsum, ← neg_zsmul, ← Int.toNat_of_nonneg (neg_nonneg.mpr hm0), natCast_zsmul]
      exact Submodule.smul_mem _ _ (R.root_mem_posRootCone i)
    exact R.zero_notMem_realRoots (hA.diag_map K)
      (R.isPointed_posRootCone _ hα.2 (by rwa [eq_neg_of_add_eq_zero_right hpt] at hneg) ▸ hα.1)
  · obtain ⟨c, hc⟩ := R.exists_nsmul_root_of_add_eq_nsmul_root hα.2 hneg
      (by rwa [← natCast_zsmul, Int.toNat_of_nonneg hmpos.le])
    rw [← natCast_zsmul] at hc
    rcases R.eq_one_or_neg_one_of_zsmul_mem_realRoots (hA.diag_map K)
        (R.root_mem_rootLattice i) (hc ▸ hα.1) with h1 | hm1
    · exact hne (by rwa [h1, one_smul] at hc)
    · omega

theorem conj_simpleReflectionMem_eq_of_smul_root_eq {w₁ w₂ : R.weylGroup (hA.diag_map K)} {i j : I}
    (h : w₁ • R.root i = w₂ • R.root j) :
    w₁ * R.simpleReflectionMem (hA.diag_map K) i * w₁⁻¹ =
      w₂ * R.simpleReflectionMem (hA.diag_map K) j * w₂⁻¹ := by
  let cs := R.weylCoxeterSystem hA; let u := w₁⁻¹ * w₂
  have hu : u • R.root j = R.root i := by rw [mul_smul, ← h, inv_smul_smul]
  have h_uj : cs.length (u * cs.simple j) = cs.length u + 1 := cs.not_isRightDescent_iff.mp <| by
    rw [R.not_isRightDescent_weylCoxeterSystem_iff hA, hu]; exact R.root_mem_posRootCone i
  have h_iu : cs.length (cs.simple i * u) = cs.length u + 1 := cs.not_isLeftDescent_iff.mp <| by
    rw [← cs.isRightDescent_inv_iff, R.not_isRightDescent_weylCoxeterSystem_iff hA, ← hu,
      inv_smul_smul]; exact R.root_mem_posRootCone j
  have h_iusj : cs.length (cs.simple i * u * cs.simple j) = cs.length u := by
    have hd : cs.IsRightDescent (cs.simple i * u) j := by
      rw [R.isRightDescent_weylCoxeterSystem_iff hA, mul_smul, hu, weylCoxeterSystem_simple,
        Subgroup.smul_def, coe_simpleReflectionMem, LinearEquiv.smul_def,
        simpleReflection_root_self, neg_neg]; exact R.root_mem_posRootCone i
    have hstep := cs.isRightDescent_iff.mp hd; omega
  have hcomm := cs.simple_mul_eq_mul_simple_of_length_eq h_iusj (h_iu.trans h_uj.symm)
  rw [weylCoxeterSystem_simple, weylCoxeterSystem_simple] at hcomm
  calc w₁ * R.simpleReflectionMem (hA.diag_map K) i * w₁⁻¹
    _ = w₁ * (R.simpleReflectionMem (hA.diag_map K) i * u) * w₂⁻¹ := by simp [u, mul_assoc]
    _ = w₁ * (u * R.simpleReflectionMem (hA.diag_map K) j) * w₂⁻¹ := by rw [hcomm]
    _ = w₂ * R.simpleReflectionMem (hA.diag_map K) j * w₂⁻¹ := by simp [u, ← mul_assoc]

theorem corootAut_coroot_eq_of_smul_root_eq {w₁ w₂ : R.weylGroup (hA.diag_map K)} {i j : I}
    (h : w₁ • R.root i = w₂ • R.root j) :
    R.corootAut (hA.diag_map K) w₁ (R.coroot i) = R.corootAut (hA.diag_map K) w₂ (R.coroot j) := by
  let u := w₁⁻¹ * w₂
  have hu : u • R.root j = R.root i := by rw [mul_smul, ← h, inv_smul_smul]
  have hconj : R.simpleReflectionMem (hA.diag_map K) i =
      u * R.simpleReflectionMem (hA.diag_map K) j * u⁻¹ := by
    simpa using R.conj_simpleReflectionMem_eq_of_smul_root_eq hA
      (show (1 : R.weylGroup (hA.diag_map K)) • R.root i = u • R.root j by simpa using hu.symm)
  have heval := congrArg (fun w ↦ R.corootAut (hA.diag_map K) w (R.coroot i)) hconj
  rw [corootAut_simpleReflectionMem, corootReflection_coroot_self, map_mul, map_mul,
    mul_apply_eq_comp, mul_apply_eq_comp, corootAut_simpleReflectionMem, corootReflection_apply,
    map_sub, map_smul, ← R.smul_dual_apply, hu, R.root_coroot, hA.diag_map K i,
    show R.corootAut (hA.diag_map K) u (R.corootAut (hA.diag_map K) u⁻¹ (R.coroot i)) = R.coroot i
      by rw [← mul_apply_eq_comp, ← map_mul, mul_inv_cancel, map_one]; simp,
    eq_sub_iff_add_eq, add_comm, ← sub_eq_add_neg, sub_eq_iff_eq_add, ← two_smul K] at heval
  have hcor : R.corootAut (hA.diag_map K) u (R.coroot j) = R.coroot i := by
    simpa [inv_smul_smul₀ (two_ne_zero (α := K))] using congrArg ((2 : K)⁻¹ • ·) heval
  simpa [u, ← mul_apply_eq_comp, ← map_mul, ← mul_assoc] using
    (congrArg (R.corootAut (hA.diag_map K) w₁) hcor).symm

/-- The **real coroot** `α^∨ ∈ H` attached to a real root `α ∈ R.realRoots (hA.diag_map K)`. -/
noncomputable def realCoroot {α : Dual K H} (hα : α ∈ R.realRoots (hA.diag_map K)) : H :=
  R.corootAut (hA.diag_map K) hα.choose (R.coroot hα.choose_spec.choose)

/-- The **real reflection** `s_α ∈ R.weylGroup (hA.diag_map K)` attached to a real root `α`. -/
noncomputable def realReflection {α : Dual K H}
    (hα : α ∈ R.realRoots (hA.diag_map K)) : R.weylGroup (hA.diag_map K) :=
  hα.choose * R.simpleReflectionMem (hA.diag_map K) hα.choose_spec.choose * hα.choose⁻¹

theorem realCoroot_eq_of_smul_root_eq {w : R.weylGroup (hA.diag_map K)} {i : I} {α : Dual K H}
    (hα : α ∈ R.realRoots (hA.diag_map K)) (hw : w • R.root i = α) :
    R.realCoroot hA hα = R.corootAut (hA.diag_map K) w (R.coroot i) :=
  R.corootAut_coroot_eq_of_smul_root_eq hA (hα.choose_spec.choose_spec.trans hw.symm)
theorem realReflection_eq_of_smul_root_eq {w : R.weylGroup (hA.diag_map K)} {i : I} {α : Dual K H}
    (hα : α ∈ R.realRoots (hA.diag_map K)) (hw : w • R.root i = α) :
    R.realReflection hA hα = w * R.simpleReflectionMem (hA.diag_map K) i * w⁻¹ :=
  R.conj_simpleReflectionMem_eq_of_smul_root_eq hA (hα.choose_spec.choose_spec.trans hw.symm)

@[simp] theorem realCoroot_smul_root (w : R.weylGroup (hA.diag_map K)) (i : I) :
    R.realCoroot hA (R.smul_root_mem_realRoots (hA.diag_map K) w i) =
      R.corootAut (hA.diag_map K) w (R.coroot i) := R.realCoroot_eq_of_smul_root_eq hA _ rfl
@[simp] theorem realCoroot_root (i : I) :
    R.realCoroot hA (R.root_mem_realRoots (hA.diag_map K) i) = R.coroot i := by
  simpa using R.realCoroot_eq_of_smul_root_eq hA (R.root_mem_realRoots (hA.diag_map K) i)
    (one_smul _ _)
@[simp] theorem realCoroot_smul (w : R.weylGroup (hA.diag_map K)) {α : Dual K H}
    (hα : α ∈ R.realRoots (hA.diag_map K)) :
    R.realCoroot hA (R.smul_mem_realRoots (hA.diag_map K) w hα) =
      R.corootAut (hA.diag_map K) w (R.realCoroot hA hα) := by
  obtain ⟨u, i, hui⟩ := id hα
  rw [R.realCoroot_eq_of_smul_root_eq hA _ (show (w * u) • R.root i = w • α by rw [mul_smul, hui]),
    R.realCoroot_eq_of_smul_root_eq hA hα hui, map_mul, mul_apply_eq_comp]
@[simp] theorem apply_realCoroot_self {α : Dual K H} (hα : α ∈ R.realRoots (hA.diag_map K)) :
    α (R.realCoroot hA hα) = 2 := by
  obtain ⟨w, i, hwi⟩ := id hα
  rw [R.realCoroot_eq_of_smul_root_eq hA hα hwi, ← hwi, R.smul_dual_corootAut_apply,
    R.root_coroot, hA.diag_map K i]

@[simp] theorem realReflection_smul_root (w : R.weylGroup (hA.diag_map K)) (i : I) :
    R.realReflection hA (R.smul_root_mem_realRoots (hA.diag_map K) w i) =
      w * R.simpleReflectionMem (hA.diag_map K) i * w⁻¹ :=
  R.realReflection_eq_of_smul_root_eq hA _ rfl
@[simp] theorem realReflection_root (i : I) :
    R.realReflection hA (R.root_mem_realRoots (hA.diag_map K) i) =
      R.simpleReflectionMem (hA.diag_map K) i := by
  simpa using R.realReflection_eq_of_smul_root_eq hA (R.root_mem_realRoots (hA.diag_map K) i)
    (one_smul _ _)
@[simp] theorem realReflection_smul (w : R.weylGroup (hA.diag_map K)) {α : Dual K H}
    (hα : α ∈ R.realRoots (hA.diag_map K)) :
    R.realReflection hA (R.smul_mem_realRoots (hA.diag_map K) w hα) =
      w * R.realReflection hA hα * w⁻¹ := by
  obtain ⟨u, i, hui⟩ := id hα
  rw [R.realReflection_eq_of_smul_root_eq hA _
    (show (w * u) • R.root i = w • α by rw [mul_smul, hui]),
    R.realReflection_eq_of_smul_root_eq hA hα hui]; simp [mul_assoc]

theorem coe_realReflection_apply {α : Dual K H} (hα : α ∈ R.realRoots (hA.diag_map K))
    (φ : Dual K H) :
    (R.realReflection hA hα : Dual K H ≃ₗ[K] Dual K H) φ = φ - φ (R.realCoroot hA hα) • α := by
  obtain ⟨w, i, hwi⟩ := id hα
  rw [← LinearEquiv.smul_def, ← Subgroup.smul_def, R.realReflection_eq_of_smul_root_eq hA hα hwi,
    R.realCoroot_eq_of_smul_root_eq hA hα hwi, ← hwi, mul_assoc, mul_smul, mul_smul,
    Subgroup.smul_def (R.simpleReflectionMem _ i), coe_simpleReflectionMem, LinearEquiv.smul_def,
    simpleReflection_apply, smul_sub, smul_inv_smul, R.smul_dual_apply (hA.diag_map K) w⁻¹ φ,
    inv_inv]
  exact congrArg (φ - ·) (map_smul (w : Dual K H ≃ₗ[K] Dual K H) _ (R.root i))
@[simp] theorem coe_realReflection_self {α : Dual K H} (hα : α ∈ R.realRoots (hA.diag_map K)) :
    (R.realReflection hA hα : Dual K H ≃ₗ[K] Dual K H) α = -α := by
  rw [R.coe_realReflection_apply hA hα α, R.apply_realCoroot_self hA hα, two_smul]; abel
@[simp] theorem realReflection_mul_self {α : Dual K H} (hα : α ∈ R.realRoots (hA.diag_map K)) :
    R.realReflection hA hα * R.realReflection hA hα = 1 := by
  obtain ⟨w, i, hwi⟩ := id hα; rw [R.realReflection_eq_of_smul_root_eq hA hα hwi]
  simp only [mul_assoc, inv_mul_cancel_left]
  rw [← mul_assoc (R.simpleReflectionMem _ i), simpleReflectionMem_mul_self, one_mul,
    mul_inv_cancel]

end CharZero

end TauCeti.CartanRealization

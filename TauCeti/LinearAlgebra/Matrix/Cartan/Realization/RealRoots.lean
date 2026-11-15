/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Cartan.Realization.WeylGroup

/-!
# Real roots, real coroots, and real reflections of a Cartan realization

Let `R` be a `TauCeti.CartanRealization` of a generalized Cartan matrix `A` over a field `K` of
characteristic zero. Following Kac (*Infinite-dimensional Lie algebras*, §5.1), the **real roots**
`Δ^re` (`TauCeti.CartanRealization.realRoots`) are the Weyl-group translates `w • αᵢ` of the simple
roots, and `Δ₊^re = Δ^re ∩ Q₊` (`TauCeti.CartanRealization.posRealRoots`) are the positive real
roots.

Unlike imaginary roots (which satisfy `⟨α, α⟩ ≤ 0` in the symmetrizable case and carry no
reflection), every real root `α = w • αᵢ` carries a well-defined **real coroot**
`α^∨ = w(hᵢ) ∈ H` (`TauCeti.CartanRealization.realCoroot`) and **real reflection**
`s_α = w sᵢ w⁻¹ ∈ R.weylGroup` (`TauCeti.CartanRealization.realReflection`), both independent of
the choice of `(w, i)` representing `α`:

* **Indivisibility** (`eq_one_or_neg_one_of_zsmul_mem_realRoots`, Kac Proposition 5.1(b)): if
  `β ∈ Q` and `n • β ∈ Δ^re`, then `n = 1` or `n = -1`.
* **Sign dichotomy and permutation of `Δ₊^re \ {αᵢ}`**: every real root lies in `Q₊` or `-Q₊`
  (`mem_posRootCone_or_neg_mem_posRootCone_of_mem_realRoots`), and `sᵢ` preserves
  `Δ₊^re \ {αᵢ}` (`simpleReflection_mem_posRealRoots`).
* **Word-independence and equivariance**: if `w₁ • αᵢ = w₂ • αⱼ`, strong exchange on
  `R.weylCoxeterSystem` yields `w₁ sᵢ w₁⁻¹ = w₂ sⱼ w₂⁻¹`
  (`conj_simpleReflectionMem_eq_of_smul_root_eq`) and `w₁(hᵢ) = w₂(hⱼ)`
  (`corootAut_coroot_eq_of_smul_root_eq`), whence `(w • α)^∨ = w(α^∨)` (`realCoroot_smul`),
  `α(α^∨) = 2` (`apply_realCoroot_self`), and `s_α(φ) = φ - φ(α^∨) • α`
  (`coe_realReflection_apply`).

## Main definitions

* `TauCeti.CartanRealization.realRoots`: the set `Δ^re` of real roots.
* `TauCeti.CartanRealization.posRealRoots`: the set `Δ₊^re = Δ^re ∩ Q₊` of positive real roots.
* `TauCeti.CartanRealization.realCoroot`: the real coroot `α^∨ ∈ H` of `α ∈ Δ^re`.
* `TauCeti.CartanRealization.realReflection`: the reflection `s_α ∈ R.weylGroup _` of `α ∈ Δ^re`.

## References

* V. G. Kac, *Infinite-dimensional Lie algebras*, third edition, Cambridge University Press, 1990,
  §3.7, §5.1, and Proposition 5.1.
-/

public section

open Module

namespace TauCeti.CartanRealization

section Integral

variable {I K H : Type*} [Field K] [AddCommGroup H] [Module K H] {A : Matrix I I ℤ}
  (R : CartanRealization (A.map (Int.cast : ℤ → K)) H)

/-- The **real roots** `Δ^re` of a Cartan realization: the Weyl-group orbit of the simple roots. -/
def realRoots (hdiag : ∀ i, A.map (Int.cast : ℤ → K) i i = 2) : Set (Dual K H) :=
  {α | ∃ (w : R.weylGroup hdiag) (i : I), w • R.root i = α}

/-- The **positive real roots** `Δ₊^re = Δ^re ∩ Q₊`. -/
def posRealRoots (hdiag : ∀ i, A.map (Int.cast : ℤ → K) i i = 2) : Set (Dual K H) :=
  R.realRoots hdiag ∩ R.posRootCone

theorem root_mem_realRoots (hdiag : ∀ i, A.map (Int.cast : ℤ → K) i i = 2) (i : I) :
    R.root i ∈ R.realRoots hdiag :=
  ⟨1, i, one_smul _ _⟩

theorem smul_root_mem_realRoots (hdiag : ∀ i, A.map (Int.cast : ℤ → K) i i = 2)
    (w : R.weylGroup hdiag) (i : I) :
    w • R.root i ∈ R.realRoots hdiag :=
  ⟨w, i, rfl⟩

theorem smul_mem_realRoots (hdiag : ∀ i, A.map (Int.cast : ℤ → K) i i = 2)
    (w : R.weylGroup hdiag) {α : Dual K H} (hα : α ∈ R.realRoots hdiag) :
    w • α ∈ R.realRoots hdiag := by
  obtain ⟨u, i, rfl⟩ := hα
  exact ⟨w * u, i, (mul_smul w u (R.root i)).symm⟩

theorem neg_mem_realRoots (hdiag : ∀ i, A.map (Int.cast : ℤ → K) i i = 2)
    {α : Dual K H} (hα : α ∈ R.realRoots hdiag) : -α ∈ R.realRoots hdiag := by
  obtain ⟨w, i, rfl⟩ := hα
  refine ⟨w * R.simpleReflectionMem hdiag i, i, ?_⟩
  have hs : R.simpleReflectionMem hdiag i • R.root i = -R.root i := by
    simp [Subgroup.smul_def, LinearEquiv.smul_def]
  rw [mul_smul, hs, smul_neg]

theorem zero_notMem_realRoots (hdiag : ∀ i, A.map (Int.cast : ℤ → K) i i = 2) :
    (0 : Dual K H) ∉ R.realRoots hdiag := by
  rintro ⟨w, i, h0⟩
  rw [Subgroup.smul_def, LinearEquiv.smul_def, LinearEquiv.map_eq_zero_iff] at h0
  exact R.root_linearIndependent.ne_zero i h0

theorem realRoots_subset_rootLattice (hdiag : ∀ i, A.map (Int.cast : ℤ → K) i i = 2) :
    R.realRoots hdiag ⊆ R.rootLattice := by
  rintro α ⟨w, i, rfl⟩
  exact R.smul_mem_rootLattice hdiag w (R.root_mem_rootLattice i)

theorem root_mem_posRealRoots (hdiag : ∀ i, A.map (Int.cast : ℤ → K) i i = 2) (i : I) :
    R.root i ∈ R.posRealRoots hdiag :=
  ⟨R.root_mem_realRoots hdiag i, R.root_mem_posRootCone i⟩

/-- Pairing any element of the root lattice `Q` against a simple coroot yields an integer. -/
theorem exists_int_apply_coroot_of_mem_rootLattice {α : Dual K H} (hα : α ∈ R.rootLattice)
    (i : I) : ∃ m : ℤ, α (R.coroot i) = m := by
  rw [R.rootLattice_def] at hα
  induction hα using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    exact ⟨A i j, by simp [R.root_coroot]⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ ihx ihy =>
    obtain ⟨m₁, hm₁⟩ := ihx
    obtain ⟨m₂, hm₂⟩ := ihy
    exact ⟨m₁ + m₂, by simp [hm₁, hm₂]⟩
  | smul n x _ ih =>
    obtain ⟨m, hm⟩ := ih
    exact ⟨n * m, by simp [hm]⟩

end Integral

section CharZero

variable {I K H : Type*} [Field K] [CharZero K] [AddCommGroup H] [Module K H] {A : Matrix I I ℤ}
  (R : CartanRealization (A.map (Int.cast : ℤ → K)) H)

/-- **Real roots are indivisible in the root lattice** (Kac, Proposition 5.1(b)). -/
theorem eq_one_or_neg_one_of_zsmul_mem_realRoots (hdiag : ∀ i, A.map (Int.cast : ℤ → K) i i = 2)
    {n : ℤ} {β : Dual K H} (hβ : β ∈ R.rootLattice) (hn : n • β ∈ R.realRoots hdiag) :
    n = 1 ∨ n = -1 := by
  obtain ⟨w, i, hwi⟩ := hn
  have hγ : w⁻¹ • β ∈ R.rootLattice := R.smul_mem_rootLattice hdiag w⁻¹ hβ
  have hroot : R.root i = n • (w⁻¹ • β) := by
    have h := congrArg (w⁻¹ • ·) hwi
    rwa [inv_smul_smul, smul_comm] at h
  let hli := R.root_linearIndependent.restrict_scalars' ℤ
  have hrepr : hli.repr ⟨R.root i, R.rootLattice_def ▸ R.root_mem_rootLattice i⟩ =
      n • hli.repr ⟨w⁻¹ • β, R.rootLattice_def ▸ hγ⟩ := by
    rw [← map_zsmul]
    exact congrArg hli.repr (Subtype.ext hroot)
  rw [hli.repr_eq_single i _ rfl] at hrepr
  have hi := congrArg (fun f : I →₀ ℤ ↦ f i) hrepr
  simp only [Finsupp.single_eq_same, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul] at hi
  exact Int.isUnit_iff.mp (IsUnit.of_mul_eq_one _ hi.symm)

/-- **Positivity dichotomy for real roots**: every real root lies in `Q₊` or in `-Q₊`. -/
theorem mem_posRootCone_or_neg_mem_posRootCone_of_mem_realRoots (hA : A.IsGeneralizedCartan)
    {α : Dual K H} (hα : α ∈ R.realRoots (hA.diag_map K)) :
    α ∈ R.posRootCone ∨ -α ∈ R.posRootCone := by
  obtain ⟨w, i, rfl⟩ := hα
  by_cases hd : (R.weylCoxeterSystem hA).IsRightDescent w i
  · exact Or.inr ((R.isRightDescent_weylCoxeterSystem_iff hA w i).mp hd)
  · exact Or.inl ((R.not_isRightDescent_weylCoxeterSystem_iff hA w i).mp hd)

private theorem exists_nsmul_root_of_add_eq_nsmul_root {α β : Dual K H}
    (hα : α ∈ R.posRootCone) (hβ : β ∈ R.posRootCone) {i : I} {k : ℕ}
    (hsum : α + β = k • R.root i) : ∃ c : ℕ, α = c • R.root i := by
  let hli := R.linearIndependent_nat_root
  let x : Submodule.span ℕ (Set.range R.root) := ⟨α, R.posRootCone_def ▸ hα⟩
  let y : Submodule.span ℕ (Set.range R.root) := ⟨β, R.posRootCone_def ▸ hβ⟩
  have hxy : x + y = k • ⟨R.root i, R.posRootCone_def ▸ R.root_mem_posRootCone i⟩ :=
    Subtype.ext hsum
  have hrepr : hli.repr x + hli.repr y = Finsupp.single i k := by
    rw [← map_add, hxy, map_nsmul, hli.repr_eq_single i _ rfl, Finsupp.smul_single_one]
  have hx_single : hli.repr x = Finsupp.single i (hli.repr x i) := by
    ext j
    rcases eq_or_ne j i with rfl | hji
    · simp
    · have hj := congrArg (fun f : I →₀ ℕ ↦ f j) hrepr
      simp only [Finsupp.add_apply, Finsupp.single_eq_of_ne hji] at hj
      have hx0 : hli.repr x j = 0 := by omega
      simp [hx0, Finsupp.single_eq_of_ne hji]
  refine ⟨hli.repr x i, ?_⟩
  have hcomb := hli.linearCombination_repr x
  rw [hx_single, Finsupp.linearCombination_single] at hcomb
  exact hcomb.symm

/-- **Simple reflection `sᵢ` permutes `Δ₊^re \ {αᵢ}`.** -/
theorem simpleReflection_mem_posRealRoots (hA : A.IsGeneralizedCartan) (i : I) {α : Dual K H}
    (hα : α ∈ R.posRealRoots (hA.diag_map K)) (hne : α ≠ R.root i) :
    R.simpleReflection (hA.diag_map K) i α ∈ R.posRealRoots (hA.diag_map K) := by
  have hreal : R.simpleReflection (hA.diag_map K) i α ∈ R.realRoots (hA.diag_map K) := by
    simpa [Subgroup.smul_def, LinearEquiv.smul_def] using
      R.smul_mem_realRoots (hA.diag_map K) (R.simpleReflectionMem (hA.diag_map K) i) hα.1
  refine ⟨hreal, ?_⟩
  rcases R.mem_posRootCone_or_neg_mem_posRootCone_of_mem_realRoots hA hreal with hpos | hneg
  · exact hpos
  exfalso
  obtain ⟨m, hm⟩ := R.exists_int_apply_coroot_of_mem_rootLattice
    (R.realRoots_subset_rootLattice (hA.diag_map K) hα.1) i
  have hsum : α + -(R.simpleReflection (hA.diag_map K) i α) = m • R.root i := by
    rw [simpleReflection_apply, hm, Int.cast_smul_eq_zsmul K m (R.root i)]
    abel
  rcases le_or_gt m 0 with hm0 | hmpos
  · have hpt : α + -(R.simpleReflection (hA.diag_map K) i α) = 0 := by
      refine R.isPointed_posRootCone _ (add_mem hα.2 hneg) ?_
      rw [hsum, ← neg_zsmul, ← Int.toNat_of_nonneg (neg_nonneg.mpr hm0), natCast_zsmul]
      exact Submodule.smul_mem _ _ (R.root_mem_posRootCone i)
    have hα0 : α = 0 :=
      R.isPointed_posRootCone _ hα.2 (by rwa [eq_neg_of_add_eq_zero_right hpt] at hneg)
    exact R.zero_notMem_realRoots (hA.diag_map K) (hα0 ▸ hα.1)
  · have hsum_nat : α + -(R.simpleReflection (hA.diag_map K) i α) = m.toNat • R.root i := by
      rw [hsum, ← natCast_zsmul, Int.toNat_of_nonneg hmpos.le]
    obtain ⟨c, hc⟩ := R.exists_nsmul_root_of_add_eq_nsmul_root hα.2 hneg hsum_nat
    rw [← natCast_zsmul] at hc
    rcases R.eq_one_or_neg_one_of_zsmul_mem_realRoots (hA.diag_map K)
        (R.root_mem_rootLattice i) (hc ▸ hα.1) with h1 | hm1
    · rw [h1, one_smul] at hc
      exact hne hc
    · omega

/-- If `w₁ • αᵢ = w₂ • αⱼ`, then `w₁ sᵢ w₁⁻¹ = w₂ sⱼ w₂⁻¹` in `R.weylGroup (hA.diag_map K)`. -/
theorem conj_simpleReflectionMem_eq_of_smul_root_eq (hA : A.IsGeneralizedCartan)
    {w₁ w₂ : R.weylGroup (hA.diag_map K)} {i j : I}
    (h : w₁ • R.root i = w₂ • R.root j) :
    w₁ * R.simpleReflectionMem (hA.diag_map K) i * w₁⁻¹ =
      w₂ * R.simpleReflectionMem (hA.diag_map K) j * w₂⁻¹ := by
  let cs := R.weylCoxeterSystem hA
  let u := w₁⁻¹ * w₂
  have hu : u • R.root j = R.root i := by
    rw [mul_smul, ← h, inv_smul_smul]
  have hu_inv : u⁻¹ • R.root i = R.root j := by
    rw [← hu, inv_smul_smul]
  have h_uj : cs.length (u * cs.simple j) = cs.length u + 1 := by
    refine cs.not_isRightDescent_iff.mp ?_
    rw [R.not_isRightDescent_weylCoxeterSystem_iff hA, hu]
    exact R.root_mem_posRootCone i
  have h_iu : cs.length (cs.simple i * u) = cs.length u + 1 := by
    refine cs.not_isLeftDescent_iff.mp ?_
    rw [← cs.isRightDescent_inv_iff, R.not_isRightDescent_weylCoxeterSystem_iff hA, hu_inv]
    exact R.root_mem_posRootCone j
  have h_iusj : cs.length (cs.simple i * u * cs.simple j) = cs.length u := by
    have hd : cs.IsRightDescent (cs.simple i * u) j := by
      rw [R.isRightDescent_weylCoxeterSystem_iff hA, mul_smul, hu, weylCoxeterSystem_simple,
        Subgroup.smul_def, coe_simpleReflectionMem, LinearEquiv.smul_def,
        simpleReflection_root_self, neg_neg]
      exact R.root_mem_posRootCone i
    have hstep := cs.isRightDescent_iff.mp hd
    omega
  have hcomm := cs.simple_mul_eq_mul_simple_of_length_eq h_iusj (h_iu.trans h_uj.symm)
  rw [weylCoxeterSystem_simple, weylCoxeterSystem_simple] at hcomm
  calc
    w₁ * R.simpleReflectionMem (hA.diag_map K) i * w₁⁻¹
    _ = w₁ * (R.simpleReflectionMem (hA.diag_map K) i * u) * w₂⁻¹ := by simp [u, mul_assoc]
    _ = w₁ * (u * R.simpleReflectionMem (hA.diag_map K) j) * w₂⁻¹ := by rw [hcomm]
    _ = w₂ * R.simpleReflectionMem (hA.diag_map K) j * w₂⁻¹ := by simp [u, ← mul_assoc]

/-- **Word-independence of real coroots**: if `w₁ • αᵢ = w₂ • αⱼ`, then `w₁(hᵢ) = w₂(hⱼ)`. -/
theorem corootAut_coroot_eq_of_smul_root_eq (hA : A.IsGeneralizedCartan)
    {w₁ w₂ : R.weylGroup (hA.diag_map K)} {i j : I}
    (h : w₁ • R.root i = w₂ • R.root j) :
    R.corootAut (hA.diag_map K) w₁ (R.coroot i) =
      R.corootAut (hA.diag_map K) w₂ (R.coroot j) := by
  let u := w₁⁻¹ * w₂
  have hu : u • R.root j = R.root i := by
    rw [mul_smul, ← h, inv_smul_smul]
  have hconj : R.simpleReflectionMem (hA.diag_map K) i =
      u * R.simpleReflectionMem (hA.diag_map K) j * u⁻¹ := by
    have h1 : (1 : R.weylGroup (hA.diag_map K)) • R.root i = u • R.root j := by
      simpa using hu.symm
    simpa using R.conj_simpleReflectionMem_eq_of_smul_root_eq hA h1
  have heval := congrArg (fun w ↦ R.corootAut (hA.diag_map K) w (R.coroot i)) hconj
  rw [corootAut_simpleReflectionMem, corootReflection_coroot_self, map_mul, map_mul,
    mul_apply_eq_comp, mul_apply_eq_comp, corootAut_simpleReflectionMem,
    corootReflection_apply, map_sub, map_smul, ← R.smul_dual_apply, hu, R.root_coroot,
    hA.diag_map K i] at heval
  have heval' : (R.corootAut (hA.diag_map K) u * R.corootAut (hA.diag_map K) u⁻¹) (R.coroot i) =
      R.coroot i := by
    rw [← map_mul, mul_inv_cancel, map_one]
    simp
  rw [mul_apply_eq_comp] at heval'
  rw [heval', eq_sub_iff_add_eq, add_comm, ← sub_eq_add_neg, sub_eq_iff_eq_add,
    ← two_smul K] at heval
  have hcor : R.corootAut (hA.diag_map K) u (R.coroot j) = R.coroot i := by
    simpa [inv_smul_smul₀ (two_ne_zero (α := K))] using congrArg ((2 : K)⁻¹ • ·) heval
  have hact := congrArg (R.corootAut (hA.diag_map K) w₁) hcor
  rw [← mul_apply_eq_comp, ← map_mul] at hact
  simpa [u, ← mul_assoc] using hact.symm

/-- The **real coroot** `α^∨ ∈ H` attached to a real root `α ∈ R.realRoots (hA.diag_map K)`. -/
noncomputable def realCoroot (hA : A.IsGeneralizedCartan) {α : Dual K H}
    (hα : α ∈ R.realRoots (hA.diag_map K)) : H :=
  R.corootAut (hA.diag_map K) hα.choose (R.coroot hα.choose_spec.choose)

/-- The **real reflection** `s_α ∈ R.weylGroup (hA.diag_map K)` attached solely to a real root
`α ∈ R.realRoots (hA.diag_map K)`. -/
noncomputable def realReflection (hA : A.IsGeneralizedCartan) {α : Dual K H}
    (hα : α ∈ R.realRoots (hA.diag_map K)) : R.weylGroup (hA.diag_map K) :=
  hα.choose * R.simpleReflectionMem (hA.diag_map K) hα.choose_spec.choose * hα.choose⁻¹

theorem realCoroot_eq_of_smul_root_eq (hA : A.IsGeneralizedCartan)
    {w : R.weylGroup (hA.diag_map K)} {i : I} {α : Dual K H}
    (hα : α ∈ R.realRoots (hA.diag_map K)) (hw : w • R.root i = α) :
    R.realCoroot hA hα = R.corootAut (hA.diag_map K) w (R.coroot i) :=
  R.corootAut_coroot_eq_of_smul_root_eq hA (hα.choose_spec.choose_spec.trans hw.symm)

theorem realReflection_eq_of_smul_root_eq (hA : A.IsGeneralizedCartan)
    {w : R.weylGroup (hA.diag_map K)} {i : I} {α : Dual K H}
    (hα : α ∈ R.realRoots (hA.diag_map K)) (hw : w • R.root i = α) :
    R.realReflection hA hα = w * R.simpleReflectionMem (hA.diag_map K) i * w⁻¹ :=
  R.conj_simpleReflectionMem_eq_of_smul_root_eq hA (hα.choose_spec.choose_spec.trans hw.symm)

@[simp]
theorem realCoroot_smul_root (hA : A.IsGeneralizedCartan) (w : R.weylGroup (hA.diag_map K))
    (i : I) :
    R.realCoroot hA (R.smul_root_mem_realRoots (hA.diag_map K) w i) =
      R.corootAut (hA.diag_map K) w (R.coroot i) :=
  R.realCoroot_eq_of_smul_root_eq hA _ rfl

@[simp]
theorem realCoroot_root (hA : A.IsGeneralizedCartan) (i : I) :
    R.realCoroot hA (R.root_mem_realRoots (hA.diag_map K) i) = R.coroot i := by
  simpa using R.realCoroot_eq_of_smul_root_eq hA (R.root_mem_realRoots (hA.diag_map K) i)
    (one_smul _ _)

/-- **Equivariance of real coroots**: `(w • α)^∨ = w(α^∨)`. -/
@[simp]
theorem realCoroot_smul (hA : A.IsGeneralizedCartan) (w : R.weylGroup (hA.diag_map K))
    {α : Dual K H} (hα : α ∈ R.realRoots (hA.diag_map K)) :
    R.realCoroot hA (R.smul_mem_realRoots (hA.diag_map K) w hα) =
      R.corootAut (hA.diag_map K) w (R.realCoroot hA hα) := by
  have ⟨u, i, hui⟩ := hα
  have hwu : (w * u) • R.root i = w • α := by rw [mul_smul, hui]
  rw [R.realCoroot_eq_of_smul_root_eq hA _ hwu, R.realCoroot_eq_of_smul_root_eq hA hα hui,
    map_mul, mul_apply_eq_comp]

@[simp]
theorem apply_realCoroot_self (hA : A.IsGeneralizedCartan) {α : Dual K H}
    (hα : α ∈ R.realRoots (hA.diag_map K)) :
    α (R.realCoroot hA hα) = 2 := by
  have ⟨w, i, hwi⟩ := hα
  rw [R.realCoroot_eq_of_smul_root_eq hA hα hwi, ← hwi, R.smul_dual_corootAut_apply,
    R.root_coroot, hA.diag_map K i]

@[simp]
theorem realReflection_smul_root (hA : A.IsGeneralizedCartan) (w : R.weylGroup (hA.diag_map K))
    (i : I) :
    R.realReflection hA (R.smul_root_mem_realRoots (hA.diag_map K) w i) =
      w * R.simpleReflectionMem (hA.diag_map K) i * w⁻¹ :=
  R.realReflection_eq_of_smul_root_eq hA _ rfl

@[simp]
theorem realReflection_root (hA : A.IsGeneralizedCartan) (i : I) :
    R.realReflection hA (R.root_mem_realRoots (hA.diag_map K) i) =
      R.simpleReflectionMem (hA.diag_map K) i := by
  simpa using R.realReflection_eq_of_smul_root_eq hA (R.root_mem_realRoots (hA.diag_map K) i)
    (one_smul _ _)

@[simp]
theorem realReflection_smul (hA : A.IsGeneralizedCartan) (w : R.weylGroup (hA.diag_map K))
    {α : Dual K H} (hα : α ∈ R.realRoots (hA.diag_map K)) :
    R.realReflection hA (R.smul_mem_realRoots (hA.diag_map K) w hα) =
      w * R.realReflection hA hα * w⁻¹ := by
  have ⟨u, i, hui⟩ := hα
  have hwu : (w * u) • R.root i = w • α := by rw [mul_smul, hui]
  rw [R.realReflection_eq_of_smul_root_eq hA _ hwu,
    R.realReflection_eq_of_smul_root_eq hA hα hui]
  simp [mul_assoc]

theorem coe_realReflection_apply (hA : A.IsGeneralizedCartan) {α : Dual K H}
    (hα : α ∈ R.realRoots (hA.diag_map K)) (φ : Dual K H) :
    (R.realReflection hA hα : Dual K H ≃ₗ[K] Dual K H) φ = φ - φ (R.realCoroot hA hα) • α := by
  have ⟨w, i, hwi⟩ := hα
  rw [← LinearEquiv.smul_def, ← Subgroup.smul_def, R.realReflection_eq_of_smul_root_eq hA hα hwi,
    R.realCoroot_eq_of_smul_root_eq hA hα hwi, ← hwi, mul_assoc, mul_smul, mul_smul,
    Subgroup.smul_def (R.simpleReflectionMem _ i), coe_simpleReflectionMem, LinearEquiv.smul_def,
    simpleReflection_apply, smul_sub, smul_inv_smul, R.smul_dual_apply (hA.diag_map K) w⁻¹ φ,
    inv_inv]
  exact congrArg (φ - ·) (map_smul (w : Dual K H ≃ₗ[K] Dual K H) _ (R.root i))

@[simp]
theorem coe_realReflection_self (hA : A.IsGeneralizedCartan) {α : Dual K H}
    (hα : α ∈ R.realRoots (hA.diag_map K)) :
    (R.realReflection hA hα : Dual K H ≃ₗ[K] Dual K H) α = -α := by
  rw [R.coe_realReflection_apply hA hα α, R.apply_realCoroot_self hA hα, two_smul]
  abel

@[simp]
theorem realReflection_mul_self (hA : A.IsGeneralizedCartan) {α : Dual K H}
    (hα : α ∈ R.realRoots (hA.diag_map K)) :
    R.realReflection hA hα * R.realReflection hA hα = 1 := by
  have ⟨w, i, hwi⟩ := hα
  rw [R.realReflection_eq_of_smul_root_eq hA hα hwi]
  simp only [mul_assoc, inv_mul_cancel_left]
  rw [← mul_assoc (R.simpleReflectionMem _ i), simpleReflectionMem_mul_self, one_mul,
    mul_inv_cancel]

end CharZero

end TauCeti.CartanRealization

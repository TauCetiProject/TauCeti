/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Coxeter.Dihedral
public import TauCeti.GroupTheory.Coxeter.Length
public import TauCeti.GroupTheory.Coxeter.LowRank
public import TauCeti.LinearAlgebra.Matrix.Cartan.Coxeter.Matrix
public import TauCeti.LinearAlgebra.Matrix.Cartan.Realization.Reflection
public import TauCeti.RingTheory.Polynomial.Chebyshev.Bounds

/-!
# Coxeter presentation and faithfulness of the Weyl group of a Cartan realization

For a `TauCeti.CartanRealization` `R` of a generalized Cartan matrix `A` over a characteristic-zero
field `K`, we prove central-enlargement invariance (`restrictRootLatticeEquiv`,
`restrictWeylGroupEquiv`), exact pairwise reflection orders `orderOf_simpleReflectionMem_mul`,
Kac's Lemma 3.11 and Proposition 3.13 (`coxeterHom`, `coxeterEquiv`, `weylCoxeterSystem`,
`weylCoxeterSystem_length`, `isRightDescent_weylCoxeterSystem_iff`,
`length_mul_simpleReflectionMem_lt_iff`), faithfulness on `Q` (`rootLatticeAut_injective`), and
low-rank/affine checks (`IsEmpty I`, `A₁`, `Fin 2`, `B₂`, `G₂`, and affine `A₁⁽¹⁾`).
-/

public section

open Module Polynomial.Chebyshev

namespace TauCeti.CartanRealization

section Restriction

variable {I K H : Type*} [Field K] [AddCommGroup H] [Module K H] {A : Matrix I I K}
  (R : CartanRealization A H)

theorem apply_eq_zero_of_mem_rootLattice_of_mem_cartanCenter {φ : Dual K H}
    (hφ : φ ∈ R.rootLattice) {z : H} (hz : z ∈ R.cartanCenter) : φ z = 0 := by
  rw [R.rootLattice_def] at hφ
  induction hφ using Submodule.span_induction with
  | mem _ hx => obtain ⟨i, rfl⟩ := hx; exact (R.mem_cartanCenter_iff z).mp hz i
  | zero => rfl
  | add _ _ _ _ ihx ihy => simp [ihx, ihy]
  | smul _ _ _ ih => simp [ih]

private theorem injOn_dualMap_subtype_rootLattice (M : Submodule K H)
    (hs : M ⊔ R.cartanCenter = ⊤) : Set.InjOn M.subtype.dualMap R.rootLattice := by
  intro φ₁ hφ₁ φ₂ hφ₂ h; rw [← sub_eq_zero]; ext x
  obtain ⟨m, hm, z, hz, rfl⟩ := Submodule.mem_sup.mp (hs ▸ Submodule.mem_top : x ∈ _)
  have hm0 : (φ₁ - φ₂) m = 0 := by
    simpa [sub_eq_zero] using congrArg (fun f : Dual K M ↦ f ⟨m, hm⟩) h
  rw [map_add, hm0, R.apply_eq_zero_of_mem_rootLattice_of_mem_cartanCenter (sub_mem hφ₁ hφ₂) hz,
    add_zero]; rfl

theorem corootAut_mem_of_corootSpan_le (hdiag : ∀ i, A i i = 2) {M : Submodule K H}
    (hc : R.corootSpan ≤ M) (w : R.weylGroup hdiag) {m : H} (hm : m ∈ M) :
    R.corootAut hdiag w m ∈ M := by
  obtain ⟨l, rfl⟩ := R.exists_wordProd_eq hdiag w
  induction l generalizing m with
  | nil => simpa using hm
  | cons i l ih =>
    rw [wordProd_cons, map_mul, mul_apply_eq_comp, corootAut_simpleReflectionMem,
      corootReflection_apply]
    exact sub_mem (ih hm) (M.smul_mem _ (hc (R.coroot_mem_corootSpan i)))

private noncomputable def restrictCorootAut (hdiag : ∀ i, A i i = 2) (M : Submodule K H)
    (hc : R.corootSpan ≤ M) : R.weylGroup hdiag →* (M ≃ₗ[K] M) where
  toFun w :=
    { toFun m := ⟨R.corootAut hdiag w m, R.corootAut_mem_of_corootSpan_le hdiag hc w m.2⟩
      map_add' x y := Subtype.ext (map_add (R.corootAut hdiag w) x.1 y.1)
      map_smul' c x := Subtype.ext (map_smul (R.corootAut hdiag w) c x.1)
      invFun m := ⟨R.corootAut hdiag w⁻¹ m, R.corootAut_mem_of_corootSpan_le hdiag hc w⁻¹ m.2⟩
      left_inv m := Subtype.ext <| (mul_apply_eq_comp _ _ _).symm.trans (by simp)
      right_inv m := Subtype.ext <| (mul_apply_eq_comp _ _ _).symm.trans (by simp) }
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp [mul_apply_eq_comp]

section SubRealization

variable (M : Submodule K H) (hc : R.corootSpan ≤ M) (hs : M ⊔ R.cartanCenter = ⊤)

@[simp] theorem dualMap_subtype_root (i : I) :
    M.subtype.dualMap (R.root i) = (R.restrict M hc hs).root i := by ext; simp

private theorem map_dualMap_subtype_rootLattice :
    R.rootLattice.map (M.subtype.dualMap.restrictScalars ℤ) = (R.restrict M hc hs).rootLattice := by
  rw [rootLattice_def, rootLattice_def, Submodule.map_span, ← Set.range_comp]
  exact congrArg (Submodule.span ℤ) (congrArg Set.range (funext (R.dualMap_subtype_root M hc hs)))

/-- **Restriction to a sub-realization identifies root lattices.** -/
noncomputable def restrictRootLatticeEquiv :
    R.rootLattice ≃ₗ[ℤ] (R.restrict M hc hs).rootLattice :=
  LinearEquiv.ofBijective
    ((M.subtype.dualMap.restrictScalars ℤ ∘ₗ R.rootLattice.subtype).codRestrict
      (R.restrict M hc hs).rootLattice fun α ↦
        R.map_dualMap_subtype_rootLattice M hc hs ▸ Submodule.mem_map_of_mem α.2)
    ⟨fun α β h ↦ Subtype.ext <|
        R.injOn_dualMap_subtype_rootLattice M hs α.2 β.2 (congrArg Subtype.val h),
      fun β ↦ by
        have hβ : (β : Dual K M) ∈ R.rootLattice.map (M.subtype.dualMap.restrictScalars ℤ) :=
          (R.map_dualMap_subtype_rootLattice M hc hs).symm ▸ β.2
        obtain ⟨φ, hφ, hφβ⟩ := Submodule.mem_map.mp hβ
        exact ⟨⟨φ, hφ⟩, Subtype.ext hφβ⟩⟩

@[simp] theorem coe_restrictRootLatticeEquiv_apply (α : R.rootLattice) :
    (R.restrictRootLatticeEquiv M hc hs α : Dual K M) = M.subtype.dualMap (α : Dual K H) := (rfl)
@[simp] theorem restrictRootLatticeEquiv_root (i : I) :
    R.restrictRootLatticeEquiv M hc hs ⟨R.root i, R.root_mem_rootLattice i⟩ =
      ⟨(R.restrict M hc hs).root i, (R.restrict M hc hs).root_mem_rootLattice i⟩ :=
  Subtype.ext (R.dualMap_subtype_root M hc hs i)

private theorem restrictCorootAut_simpleReflectionMem (hdiag : ∀ i, A i i = 2) (i : I) :
    R.restrictCorootAut hdiag M hc (R.simpleReflectionMem hdiag i) =
      (R.restrict M hc hs).corootReflection hdiag i :=
  LinearEquiv.ext fun m ↦ Subtype.ext <| by
    simpa [restrictCorootAut] using (R.coe_restrict_corootReflection hdiag M hc hs i m).symm

private theorem restrictCorootAut_mem (hdiag : ∀ i, A i i = 2) (w : R.weylGroup hdiag) :
    R.restrictCorootAut hdiag M hc w ∈ (R.restrict M hc hs).corootWeylGroup hdiag := by
  obtain ⟨l, rfl⟩ := R.exists_wordProd_eq hdiag w
  induction l with
  | nil => simp
  | cons i l ih =>
    rw [wordProd_cons, map_mul, R.restrictCorootAut_simpleReflectionMem M hc hs hdiag i]
    exact mul_mem (by simpa using ((R.restrict M hc hs).corootReflectionMem hdiag i).2) ih

private noncomputable def restrictWeylGroupHom (hdiag : ∀ i, A i i = 2) :
    R.weylGroup hdiag →* (R.restrict M hc hs).weylGroup hdiag :=
  ((R.restrict M hc hs).corootWeylEquiv hdiag).toMonoidHom.comp <|
    (R.restrictCorootAut hdiag M hc).codRestrict _ (R.restrictCorootAut_mem M hc hs hdiag)

private theorem restrictWeylGroupHom_simpleReflectionMem (hdiag : ∀ i, A i i = 2) (i : I) :
    R.restrictWeylGroupHom M hc hs hdiag (R.simpleReflectionMem hdiag i) =
      (R.restrict M hc hs).simpleReflectionMem hdiag i := by
  have hmem : (R.restrictCorootAut hdiag M hc).codRestrict _
      (R.restrictCorootAut_mem M hc hs hdiag) (R.simpleReflectionMem hdiag i) =
      (R.restrict M hc hs).corootReflectionMem hdiag i :=
    Subtype.ext (by simpa using R.restrictCorootAut_simpleReflectionMem M hc hs hdiag i)
  simp [restrictWeylGroupHom, hmem]

/-- **The Weyl group of a realization is canonically isomorphic to that of any sub-realization.** -/
noncomputable def restrictWeylGroupEquiv (hdiag : ∀ i, A i i = 2) :
    R.weylGroup hdiag ≃* (R.restrict M hc hs).weylGroup hdiag :=
  MulEquiv.ofBijective (R.restrictWeylGroupHom M hc hs hdiag)
    ⟨(injective_iff_map_eq_one _).mpr fun w hw ↦ R.corootAut_injective hdiag <| by
      have hM : R.restrictCorootAut hdiag M hc w = 1 := congrArg Subtype.val <|
        ((R.restrict M hc hs).corootWeylEquiv hdiag).injective (hw.trans (map_one _).symm)
      ext x; obtain ⟨m, hm, z, hz, rfl⟩ := Submodule.mem_sup.mp (hs ▸ Submodule.mem_top : x ∈ _)
      have hm' : R.corootAut hdiag w m = m :=
        congrArg Subtype.val (congrArg (fun f : M ≃ₗ[K] M ↦ f ⟨m, hm⟩) hM)
      simp [hm', R.corootAut_eq_self_of_mem_cartanCenter hdiag w hz],
    fun w' ↦ by
      obtain ⟨l, rfl⟩ := (R.restrict M hc hs).exists_wordProd_eq hdiag w'
      refine ⟨R.wordProd hdiag l, ?_⟩
      induction l with
      | nil => simp
      | cons i l ih =>
        rw [wordProd_cons, wordProd_cons, map_mul, ih,
          R.restrictWeylGroupHom_simpleReflectionMem M hc hs hdiag i]⟩

@[simp] theorem restrictWeylGroupEquiv_simpleReflectionMem (hdiag : ∀ i, A i i = 2) (i : I) :
    R.restrictWeylGroupEquiv M hc hs hdiag (R.simpleReflectionMem hdiag i) =
      (R.restrict M hc hs).simpleReflectionMem hdiag i :=
  R.restrictWeylGroupHom_simpleReflectionMem M hc hs hdiag i

theorem dualMap_subtype_smul (hdiag : ∀ i, A i i = 2) (w : R.weylGroup hdiag) (φ : Dual K H) :
    M.subtype.dualMap (w • φ) =
      R.restrictWeylGroupEquiv M hc hs hdiag w • M.subtype.dualMap φ := by
  obtain ⟨l, rfl⟩ := R.exists_wordProd_eq hdiag w
  induction l generalizing φ with
  | nil => simp
  | cons i l ih =>
    rw [wordProd_cons, map_mul, restrictWeylGroupEquiv_simpleReflectionMem, mul_smul, mul_smul,
      ← ih]
    simpa [Subgroup.smul_def, LinearEquiv.smul_def] using
      R.dualMap_subtype_simpleReflection hdiag M hc hs i (R.wordProd hdiag l • φ)

end SubRealization

@[simp] theorem restrictRootLatticeEquiv_rootLatticeAut {I K H : Type*} [Field K] [AddCommGroup H]
    [Module K H] {A : Matrix I I ℤ} (R : CartanRealization (A.map (Int.cast : ℤ → K)) H)
    (M : Submodule K H) (hc : R.corootSpan ≤ M) (hs : M ⊔ R.cartanCenter = ⊤)
    (hdiag : ∀ i, A.map (Int.cast : ℤ → K) i i = 2) (w : R.weylGroup hdiag)
    (α : R.rootLattice) :
    R.restrictRootLatticeEquiv M hc hs (R.rootLatticeAut hdiag w α) =
      (R.restrict M hc hs).rootLatticeAut hdiag (R.restrictWeylGroupEquiv M hc hs hdiag w)
        (R.restrictRootLatticeEquiv M hc hs α) :=
  Subtype.ext (by simpa using R.dualMap_subtype_smul M hc hs hdiag w α.1)

end Restriction

section BraidRelations

variable {I K H : Type*} [Field K] [AddCommGroup H] [Module K H] {A : Matrix I I ℤ}
  (R : CartanRealization (A.map (Int.cast : ℤ → K)) H)
  (hdiag : ∀ i, A.map (Int.cast : ℤ → K) i i = 2)

private theorem eval_coroot_root_sub_two (i j : I) :
    Dual.eval K H (R.coroot i) (R.root j) * Dual.eval K H (R.coroot j) (R.root i) - 2 =
      algebraMap ℤ K (A i j * A j i - 2) := by simp [R.root_coroot]

theorem simpleReflection_mul_pow_root (i j : I) (m : ℕ) :
    ((R.simpleReflection hdiag i * R.simpleReflection hdiag j) ^ m) (R.root i) =
      ((S ℤ m).eval (A i j * A j i - 2) +
          (S ℤ ((m : ℤ) - 1)).eval (A i j * A j i - 2)) • R.root i +
        ((S ℤ ((m : ℤ) - 1)).eval (A i j * A j i - 2) * -A j i) • R.root j := by
  rw [simpleReflection_eq_reflection, simpleReflection_eq_reflection,
    Module.reflection_mul_reflection_pow_apply_self, R.eval_coroot_root_sub_two i j,
    ← algebraMap_eval_S, ← algebraMap_eval_S]
  simp [R.root_coroot, ← Int.cast_add, ← Int.cast_mul, Int.cast_smul_eq_zsmul]

theorem simpleReflection_mul_simpleReflection_mul_pow_root (i j : I) (m : ℕ) :
    (R.simpleReflection hdiag j *
        (R.simpleReflection hdiag i * R.simpleReflection hdiag j) ^ m) (R.root i) =
      ((S ℤ m).eval (A i j * A j i - 2) +
          (S ℤ ((m : ℤ) - 1)).eval (A i j * A j i - 2)) • R.root i +
        ((S ℤ m).eval (A i j * A j i - 2) * -A j i) • R.root j := by
  rw [simpleReflection_eq_reflection, simpleReflection_eq_reflection,
    Module.reflection_mul_reflection_mul_reflection_pow_apply_self, R.eval_coroot_root_sub_two i j,
    ← algebraMap_eval_S, ← algebraMap_eval_S]
  simp [R.root_coroot, ← Int.cast_add, ← Int.cast_mul, Int.cast_smul_eq_zsmul]

private theorem simpleReflection_comm_of_apply_eq_zero {i j : I} (hij0 : A i j = 0)
    (hji0 : A j i = 0) :
    R.simpleReflection hdiag i * R.simpleReflection hdiag j =
      R.simpleReflection hdiag j * R.simpleReflection hdiag i := by
  ext φ h
  simp only [mul_apply_eq_comp, simpleReflection_apply, map_sub, map_smul, R.root_coroot,
    Matrix.map_apply, hij0, hji0, Int.cast_zero, zero_smul, sub_zero, LinearMap.sub_apply,
    LinearMap.smul_apply, smul_eq_mul]; ring

private theorem simpleReflection_mul_pow_eq_one_of_mem {i j : I}
    (hmem : A i j * A j i ∈ ({1, 2, 3} : Set ℤ)) :
    (R.simpleReflection hdiag i * R.simpleReflection hdiag j) ^
        TauCeti.coxeterOrder (A i j * A j i) = 1 := by
  ext φ h
  rw [simpleReflection_eq_reflection, simpleReflection_eq_reflection,
    Module.reflection_mul_reflection_pow_apply]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with hc | hc | hc
  · have hp : (A i j : K) * (A j i : K) = 1 := by rw [← Int.cast_mul, hc, Int.cast_one]
    rw [hc, TauCeti.coxeterOrder_one]; simp [R.root_coroot, hp, S_zero, S_one]; ring
  · have hp : (A i j : K) * (A j i : K) = 2 := by rw [← Int.cast_mul, hc, Int.cast_two]
    rw [hc, TauCeti.coxeterOrder_two]; simp [R.root_coroot, hp, S_one]
  · have hp : (A i j : K) * (A j i : K) = 3 := by rw [← Int.cast_mul, hc]; norm_num
    rw [hc, TauCeti.coxeterOrder_three]; simp [R.root_coroot, hp, S_two]; ring

theorem simpleReflection_mul_pow_cartanCoxeterMatrix
    (hzero : ∀ i j, A i j = 0 ↔ A j i = 0) (i j : I) :
    (R.simpleReflection hdiag i * R.simpleReflection hdiag j) ^ A.cartanCoxeterMatrix i j = 1 := by
  rcases eq_or_ne i j with rfl | hij
  · simp
  by_cases hmem : A i j * A j i ∈ ({0, 1, 2, 3} : Set ℤ)
  · have hle : A i j * A j i ≤ 3 := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
      rcases hmem with h | h | h | h <;> omega
    rw [A.cartanCoxeterMatrix_of_ne_of_le hij hle]
    rcases Set.mem_insert_iff.mp hmem with h0 | h123
    · rw [h0, TauCeti.coxeterOrder_zero]
      have hij0 : A i j = 0 := (mul_eq_zero.mp h0).elim id (hzero i j).mpr
      have hcomm := R.simpleReflection_comm_of_apply_eq_zero hdiag hij0 ((hzero i j).mp hij0)
      rw [sq, ← mul_assoc, mul_assoc (R.simpleReflection hdiag i), ← hcomm,
        ← mul_assoc (R.simpleReflection hdiag i), simpleReflection_mul_self, one_mul,
        simpleReflection_mul_self]
    · exact R.simpleReflection_mul_pow_eq_one_of_mem hdiag h123
  · have hm0 : A.cartanCoxeterMatrix i j = 0 := by
      rw [A.cartanCoxeterMatrix_of_ne hij]; split_ifs with hle
      · exact TauCeti.coxeterOrder_eq_zero_iff.mpr fun h' ↦ by
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem h'
          rcases h' with h | h | h | h | h <;> [exact hmem (Or.inl h);
            exact hmem (Or.inr (Or.inl h)); exact hmem (Or.inr (Or.inr (Or.inl h)));
            exact hmem (Or.inr (Or.inr (Or.inr h))); omega]
      · rfl
    rw [hm0, pow_zero]

theorem simpleReflectionMem_mul_pow_cartanCoxeterMatrix
    (hzero : ∀ i j, A i j = 0 ↔ A j i = 0) (i j : I) :
    (R.simpleReflectionMem hdiag i * R.simpleReflectionMem hdiag j) ^
        A.cartanCoxeterMatrix i j = 1 :=
  Subtype.ext (by simpa using R.simpleReflection_mul_pow_cartanCoxeterMatrix hdiag hzero i j)

private theorem linearIndependent_int_root_pair [CharZero K] {i j : I} (hij : i ≠ j) :
    LinearIndependent ℤ ![R.root i, R.root j] := by
  rw [show ![R.root i, R.root j] = R.root ∘ ![i, j] by ext a; fin_cases a <;> rfl]
  exact (R.root_linearIndependent.restrict_scalars' ℤ).comp ![i, j] fun a b h ↦ by
    fin_cases a <;> fin_cases b <;> simp_all

private theorem false_of_chebyshev_dihedral_lt {a b : ℤ} {k : ℕ}
    (hmem : a * b ∈ ({0, 1, 2, 3} : Set ℤ)) (hlt : k + 1 < TauCeti.coxeterOrder (a * b))
    (hsum : (S ℤ ((k + 1 : ℕ) : ℤ)).eval (a * b - 2) + (S ℤ k).eval (a * b - 2) = 1)
    (hprod : (S ℤ k).eval (a * b - 2) * -b = 0) : False := by
  have hS3 := S_add_two ℤ 1; have hS4 := S_add_two ℤ 2; norm_num at hS3 hS4
  rcases Set.mem_insert_iff.mp hmem with hc | hc123
  · rw [hc, TauCeti.coxeterOrder_zero] at hlt
    obtain rfl : k = 0 := by omega
    rw [hc] at hsum; norm_num [S_zero, S_one] at hsum
  · have hb0 : -b ≠ 0 := neg_ne_zero.mpr fun h0 ↦ by simp [h0] at hc123
    have hSk := (mul_eq_zero.mp hprod).resolve_right hb0
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc123
    rcases hc123 with hc | hc | hc <;> rw [hc] at hlt hsum hSk <;>
      simp only [TauCeti.coxeterOrder_one, TauCeti.coxeterOrder_two,
        TauCeti.coxeterOrder_three] at hlt <;>
      (have hk_lt : k < 5 := by omega) <;> interval_cases k <;>
      first | omega | (norm_num [S_zero, S_one, S_two, hS3, hS4] at hsum; done) |
        norm_num [S_zero, S_one, S_two, hS3, hS4] at hSk

private theorem simpleReflection_mul_pow_ne_one_of_lt [CharZero K] {i j : I} (hij : i ≠ j)
    {k : ℕ} (hk : A.cartanCoxeterMatrix i j = 0 ∨ k + 1 < A.cartanCoxeterMatrix i j) :
    (R.simpleReflection hdiag i * R.simpleReflection hdiag j) ^ (k + 1) ≠ 1 := fun h1 ↦ by
  have hroot : ((R.simpleReflection hdiag i * R.simpleReflection hdiag j) ^ (k + 1)) (R.root i) =
      (1 : ℤ) • R.root i + (0 : ℤ) • R.root j := by simp [h1]
  rw [R.simpleReflection_mul_pow_root hdiag i j (k + 1),
    show (((k + 1 : ℕ) : ℤ) - 1) = (k : ℤ) by omega] at hroot
  obtain ⟨hsum, hprod⟩ := (R.linearIndependent_int_root_pair hij).eq_of_pair hroot
  by_cases hmem : A i j * A j i ∈ ({0, 1, 2, 3} : Set ℤ)
  · have hle : A i j * A j i ≤ 3 := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
      rcases hmem with h | h | h | h <;> omega
    have hm := A.cartanCoxeterMatrix_of_ne_of_le hij hle
    have h2 : 2 ≤ A.cartanCoxeterMatrix i j := hm ▸ TauCeti.two_le_coxeterOrder hmem
    exact false_of_chebyshev_dihedral_lt hmem (hm ▸ hk.resolve_left (by omega)) hsum hprod
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hmem
    have habs : (2 : ℤ) ≤ |A i j * A j i - 2| := by
      rcases lt_or_gt_of_ne hmem.1 with _ | _ <;> [rw [abs_of_neg (by omega)];
        rw [abs_of_nonneg (by omega)]] <;> omega
    have hbound := natCast_add_one_le_abs_S_eval habs k
    exact mul_ne_zero (fun h0 ↦ by rw [h0, abs_zero] at hbound; omega)
      (neg_ne_zero.mpr fun h0 ↦ hmem.1 (by simp [h0])) hprod

@[simp] theorem orderOf_simpleReflectionMem_mul [CharZero K]
    (hzero : ∀ i j, A i j = 0 ↔ A j i = 0) (i j : I) :
    orderOf (R.simpleReflectionMem hdiag i * R.simpleReflectionMem hdiag j) =
      A.cartanCoxeterMatrix i j := by
  rcases eq_or_ne i j with rfl | hij
  · simp
  rcases Nat.eq_zero_or_pos (A.cartanCoxeterMatrix i j) with hm0 | hpos
  · rw [hm0, orderOf_eq_zero_iff']
    intro n hn hpow; obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    exact R.simpleReflection_mul_pow_ne_one_of_lt hdiag hij (Or.inl hm0)
      (by simpa using congrArg Subtype.val hpow)
  · rw [orderOf_eq_iff hpos]
    refine ⟨R.simpleReflectionMem_mul_pow_cartanCoxeterMatrix hdiag hzero i j, fun m hlt hm hp ↦ ?_⟩
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
    exact R.simpleReflection_mul_pow_ne_one_of_lt hdiag hij (Or.inr hlt)
      (by simpa using congrArg Subtype.val hp)

/-- The canonical group homomorphism from `A.cartanCoxeterMatrix.Group` to `R.weylGroup hdiag`. -/
noncomputable def coxeterHom (hzero : ∀ i j, A i j = 0 ↔ A j i = 0) :
    A.cartanCoxeterMatrix.Group →* R.weylGroup hdiag :=
  A.cartanCoxeterMatrix.toCoxeterSystem.lift
    ⟨R.simpleReflectionMem hdiag, R.simpleReflectionMem_mul_pow_cartanCoxeterMatrix hdiag hzero⟩

@[simp] theorem coxeterHom_simple (hzero : ∀ i j, A i j = 0 ↔ A j i = 0) (i : I) :
    R.coxeterHom hdiag hzero (A.cartanCoxeterMatrix.simple i) = R.simpleReflectionMem hdiag i :=
  A.cartanCoxeterMatrix.toCoxeterSystem.lift_apply_simple _ i
@[simp] theorem coxeterHom_wordProd (hzero : ∀ i j, A i j = 0 ↔ A j i = 0) (l : List I) :
    R.coxeterHom hdiag hzero (A.cartanCoxeterMatrix.toCoxeterSystem.wordProd l) =
      R.wordProd hdiag l := by
  induction l with
  | nil => simp
  | cons i l ih =>
    rw [CoxeterSystem.wordProd_cons, map_mul, ih, wordProd_cons]
    exact congrArg (· * R.wordProd hdiag l) (R.coxeterHom_simple hdiag hzero i)
theorem coxeterHom_surjective (hzero : ∀ i j, A i j = 0 ↔ A j i = 0) :
    Function.Surjective (R.coxeterHom hdiag hzero) := fun w ↦ by
  obtain ⟨l, rfl⟩ := R.exists_wordProd_eq hdiag w
  exact ⟨A.cartanCoxeterMatrix.toCoxeterSystem.wordProd l, R.coxeterHom_wordProd hdiag hzero l⟩

end BraidRelations

section GeneralizedCartan

universe u

private theorem alternatingWord_chebyshev_nonneg {c : ℤ} (hc0 : 0 ≤ c) {k : ℕ}
    (hk : 3 < c ∨ (c ≤ 3 ∧ k < TauCeti.coxeterOrder c)) :
    0 ≤ (S ℤ (k / 2)).eval (c - 2) + (S ℤ (((k / 2 : ℕ) : ℤ) - 1)).eval (c - 2) ∧
      0 ≤ (if Even k then (S ℤ (((k / 2 : ℕ) : ℤ) - 1)).eval (c - 2)
        else (S ℤ (k / 2)).eval (c - 2)) := by
  rcases hk with hgt | ⟨hle, hlt⟩
  · have ht : (2 : ℤ) ≤ c - 2 := by omega
    have h1 := S_eval_nonneg ht (k / 2)
    have h2 : 0 ≤ (S ℤ (((k / 2 : ℕ) : ℤ) - 1)).eval (c - 2) := by
      rcases eq_or_ne (k / 2) 0 with h0 | hne
      · simp [h0, S_neg_one]
      · obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hne
        rw [hm, Nat.succ_eq_add_one, show (((m + 1 : ℕ) : ℤ) - 1) = (m : ℤ) by omega]
        exact S_eval_nonneg ht m
    exact ⟨add_nonneg h1 h2, by split_ifs <;> assumption⟩
  · rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3) with rfl | rfl | rfl | rfl <;>
      simp at hlt <;> interval_cases k <;> norm_num [Nat.even_iff, S_neg_one, S_zero, S_one, S_two]

section

variable {I K H : Type*} [Field K] [AddCommGroup H] [Module K H] {A : Matrix I I ℤ}
  (R : CartanRealization (A.map (Int.cast : ℤ → K)) H) (hA : A.IsGeneralizedCartan)

private theorem exists_nsmul_alternatingWord_root {i j : I} (hij : i ≠ j) {k : ℕ}
    (hk : A.cartanCoxeterMatrix i j = 0 ∨ k < A.cartanCoxeterMatrix i j) :
    ∃ a b : ℕ, R.coxeterHom (hA.diag_map K) hA.zero_comm
        (A.cartanCoxeterMatrix.toCoxeterSystem.wordProd (CoxeterSystem.alternatingWord i j k)) •
          R.root i = a • R.root i + b • R.root j := by
  have hk' : 3 < A i j * A j i ∨
      (A i j * A j i ≤ 3 ∧ k < TauCeti.coxeterOrder (A i j * A j i)) := by
    rcases hk with h0 | hlt
    · exact Or.inl (((hA.cartanCoxeterMatrix_eq_zero_iff i j).mp h0).2)
    · exact (le_or_gt (A i j * A j i) 3).symm.imp id fun hle ↦
        ⟨hle, (A.cartanCoxeterMatrix_of_ne_of_le hij hle) ▸ hlt⟩
  obtain ⟨ha, hb⟩ := alternatingWord_chebyshev_nonneg (hA.mul_nonneg i j) hk'
  have hb' : 0 ≤ (if Even k then (S ℤ (((k / 2 : ℕ) : ℤ) - 1)).eval (A i j * A j i - 2)
      else (S ℤ (k / 2)).eval (A i j * A j i - 2)) * -A j i :=
    mul_nonneg hb (neg_nonneg.mpr (hA.offDiag_nonpos j i hij.symm))
  refine ⟨((S ℤ (k / 2)).eval (A i j * A j i - 2) +
      (S ℤ (((k / 2 : ℕ) : ℤ) - 1)).eval (A i j * A j i - 2)).toNat,
    ((if Even k then (S ℤ (((k / 2 : ℕ) : ℤ) - 1)).eval (A i j * A j i - 2)
      else (S ℤ (k / 2)).eval (A i j * A j i - 2)) * -A j i).toNat, ?_⟩
  rw [← natCast_zsmul, ← natCast_zsmul, Int.toNat_of_nonneg ha, Int.toNat_of_nonneg hb',
    CoxeterSystem.prod_alternatingWord_eq_mul_pow]
  by_cases hev : Even k <;>
    simp only [hev, ↓reduceIte, one_mul, map_pow, map_mul, CoxeterMatrix.toCoxeterSystem_simple,
      coxeterHom_simple, Subgroup.smul_def, Subgroup.coe_pow, Subgroup.coe_mul,
      coe_simpleReflectionMem, LinearEquiv.smul_def]
  · exact R.simpleReflection_mul_pow_root (hA.diag_map K) i j (k / 2)
  · exact R.simpleReflection_mul_simpleReflection_mul_pow_root (hA.diag_map K) i j (k / 2)

private theorem coxeterHom_smul_root_mem_posRootCone_of_not_isRightDescent :
    ∀ (n : ℕ) (w : A.cartanCoxeterMatrix.Group),
      A.cartanCoxeterMatrix.toCoxeterSystem.length w = n →
      ∀ i : I, ¬ A.cartanCoxeterMatrix.toCoxeterSystem.IsRightDescent w i →
        R.coxeterHom (hA.diag_map K) hA.zero_comm w • R.root i ∈ R.posRootCone := by
  let cs := A.cartanCoxeterMatrix.toCoxeterSystem
  intro n; induction n using Nat.strongRecOn with
  | ind n ih =>
    intro w hwn i hi
    rcases eq_or_ne w 1 with rfl | hw1
    · simpa using R.root_mem_posRootCone i
    obtain ⟨j, hj⟩ := cs.exists_rightDescent_of_ne_one hw1
    have hij : i ≠ j := fun h ↦ hi (h ▸ hj)
    obtain ⟨⟨u, v⟩, ⟨hu, hv, rfl⟩, -⟩ := cs.existsUnique_isMinimalCosetRep_mul {i, j} w
    have hlen := cs.length_mul_of_isMinimalCosetRep hu hv
    have hui_nd := cs.isMinimalCosetRep_iff.mp hu i (by simp)
    have huj_nd := cs.isMinimalCosetRep_iff.mp hu j (by simp)
    have hvpos : 0 < cs.length v := Nat.pos_of_ne_zero fun h0 ↦
      huj_nd (by simpa [cs.length_eq_zero_iff.mp h0] using hj)
    have hvi : ¬ cs.IsRightDescent v i := fun hdvi ↦ hi <| by
      rw [CoxeterSystem.IsRightDescent, mul_assoc,
        cs.length_mul_of_isMinimalCosetRep hu (mul_mem hv (cs.simple_mem_parabolic (by simp))),
        hlen]
      exact Nat.add_lt_add_left hdvi _
    obtain ⟨hvw, hk⟩ := cs.wordProd_alternatingWord_eq_and_length_lt_of_mem_parabolic_pair hv hvi
    obtain ⟨a, b, hab⟩ := R.exists_nsmul_alternatingWord_root hA hij hk; rw [hvw] at hab
    have hlt : cs.length u < n := (Nat.lt_add_of_pos_right hvpos).trans_eq (hlen.symm.trans hwn)
    rw [map_mul, mul_smul, hab, smul_add, smul_comm, smul_comm _ b]
    exact add_mem (Submodule.smul_mem _ a (ih _ hlt u rfl i hui_nd))
      (Submodule.smul_mem _ b (ih _ hlt u rfl j huj_nd))

variable [CharZero K]

private theorem isRightDescent_coxeterHom_iff (w : A.cartanCoxeterMatrix.Group) (i : I) :
    A.cartanCoxeterMatrix.toCoxeterSystem.IsRightDescent w i ↔
      -(R.coxeterHom (hA.diag_map K) hA.zero_comm w • R.root i) ∈ R.posRootCone := by
  let cs := A.cartanCoxeterMatrix.toCoxeterSystem
  have hnot_both : ¬ (R.coxeterHom (hA.diag_map K) hA.zero_comm w • R.root i ∈ R.posRootCone ∧
      -(R.coxeterHom (hA.diag_map K) hA.zero_comm w • R.root i) ∈ R.posRootCone) := fun ⟨hp, hn⟩ ↦
    R.root_linearIndependent.ne_zero i <| by
      simpa [Subgroup.smul_def, LinearEquiv.smul_def] using R.isPointed_posRootCone _ hp hn
  refine ⟨fun hd ↦ ?_, fun hneg ↦ by_contra fun hnd ↦
    hnot_both ⟨R.coxeterHom_smul_root_mem_posRootCone_of_not_isRightDescent hA _ _ rfl i hnd, hneg⟩⟩
  have hpos := R.coxeterHom_smul_root_mem_posRootCone_of_not_isRightDescent hA _ _ rfl i
    (cs.isRightDescent_iff_not_isRightDescent_mul.mp hd)
  have h1 : R.coxeterHom (hA.diag_map K) hA.zero_comm (cs.simple i) • R.root i = -R.root i := by
    simp [cs, Subgroup.smul_def, LinearEquiv.smul_def]
  rwa [map_mul, mul_smul, h1, smul_neg] at hpos

private theorem eq_one_of_forall_coxeterHom_smul_root_eq {w : A.cartanCoxeterMatrix.Group}
    (hw : ∀ i, R.coxeterHom (hA.diag_map K) hA.zero_comm w • R.root i = R.root i) : w = 1 := by
  by_contra hw1
  obtain ⟨i, hi⟩ := A.cartanCoxeterMatrix.toCoxeterSystem.exists_rightDescent_of_ne_one hw1
  exact R.root_linearIndependent.ne_zero i
    (R.isPointed_posRootCone _ (R.root_mem_posRootCone i)
      (hw i ▸ (R.isRightDescent_coxeterHom_iff hA w i).mp hi))

theorem coxeterHom_injective :
    Function.Injective (R.coxeterHom (hA.diag_map K) hA.zero_comm) :=
  (injective_iff_map_eq_one _).mpr fun _ hw ↦
    R.eq_one_of_forall_coxeterHom_smul_root_eq hA fun i ↦ by rw [hw, one_smul]

/-- **Kac, Proposition 3.13.** Canonical isomorphism from `A.cartanCoxeterMatrix.Group` onto
`R.weylGroup (hA.diag_map K)`. -/
noncomputable def coxeterEquiv :
    A.cartanCoxeterMatrix.Group ≃* R.weylGroup (hA.diag_map K) :=
  MulEquiv.ofBijective (R.coxeterHom (hA.diag_map K) hA.zero_comm)
    ⟨R.coxeterHom_injective hA, R.coxeterHom_surjective (hA.diag_map K) hA.zero_comm⟩

@[simp] theorem coxeterEquiv_simple (i : I) :
    R.coxeterEquiv hA (A.cartanCoxeterMatrix.simple i) =
      R.simpleReflectionMem (hA.diag_map K) i := R.coxeterHom_simple (hA.diag_map K) hA.zero_comm i

/-- **The Weyl group as a Coxeter system** with Coxeter matrix `A.cartanCoxeterMatrix`. -/
noncomputable def weylCoxeterSystem :
    CoxeterSystem A.cartanCoxeterMatrix (R.weylGroup (hA.diag_map K)) :=
  A.cartanCoxeterMatrix.toCoxeterSystem.map (R.coxeterEquiv hA)

@[simp] theorem weylCoxeterSystem_simple (i : I) :
    (R.weylCoxeterSystem hA).simple i = R.simpleReflectionMem (hA.diag_map K) i :=
  R.coxeterEquiv_simple hA i
@[simp] theorem weylCoxeterSystem_wordProd (l : List I) :
    (R.weylCoxeterSystem hA).wordProd l = R.wordProd (hA.diag_map K) l :=
  (CoxeterSystem.wordProd_map _ _ l).trans (R.coxeterHom_wordProd (hA.diag_map K) hA.zero_comm l)

@[simp] theorem weylCoxeterSystem_length (w : R.weylGroup (hA.diag_map K)) :
    (R.weylCoxeterSystem hA).length w = R.length (hA.diag_map K) w := by
  refine le_antisymm ?_ ?_
  · obtain ⟨l, hl, rfl⟩ := R.exists_wordProd_length_eq (hA.diag_map K) w
    rw [← hl, ← R.weylCoxeterSystem_wordProd hA l]
    exact (R.weylCoxeterSystem hA).length_wordProd_le l
  · obtain ⟨l, hl, rfl⟩ := (R.weylCoxeterSystem hA).exists_isReduced w
    rw [hl.eq, R.weylCoxeterSystem_wordProd hA l]
    exact R.length_wordProd_le (hA.diag_map K) l

/-- **Kac, Lemma 3.11 (descent form).** `i` is a right descent of `w` iff `-(w • αᵢ) ∈ Q₊`. -/
theorem isRightDescent_weylCoxeterSystem_iff (w : R.weylGroup (hA.diag_map K)) (i : I) :
    (R.weylCoxeterSystem hA).IsRightDescent w i ↔ -(w • R.root i) ∈ R.posRootCone := by
  let w₀ := (R.coxeterEquiv hA).symm w
  have hw : R.coxeterEquiv hA w₀ = w := (R.coxeterEquiv hA).apply_symm_apply w
  have hdesc : (R.weylCoxeterSystem hA).IsRightDescent w i ↔
      A.cartanCoxeterMatrix.toCoxeterSystem.IsRightDescent w₀ i := by
    rw [CoxeterSystem.IsRightDescent, CoxeterSystem.IsRightDescent, ← hw, weylCoxeterSystem,
      CoxeterSystem.map_simple, CoxeterMatrix.toCoxeterSystem_simple, ← map_mul,
      CoxeterSystem.length_map, CoxeterSystem.length_map]
  exact hdesc.trans ((R.isRightDescent_coxeterHom_iff hA w₀ i).trans (by rw [show
    R.coxeterHom (hA.diag_map K) hA.zero_comm w₀ = w from hw]))

theorem not_isRightDescent_weylCoxeterSystem_iff (w : R.weylGroup (hA.diag_map K)) (i : I) :
    ¬ (R.weylCoxeterSystem hA).IsRightDescent w i ↔ w • R.root i ∈ R.posRootCone := by
  let w₀ := (R.coxeterEquiv hA).symm w
  have hcox : R.coxeterHom (hA.diag_map K) hA.zero_comm w₀ = w :=
    (R.coxeterEquiv hA).apply_symm_apply w
  rw [R.isRightDescent_weylCoxeterSystem_iff hA]
  refine ⟨fun hnot ↦ ?_, fun hpos hneg ↦ R.root_linearIndependent.ne_zero i
    (by simpa [Subgroup.smul_def, LinearEquiv.smul_def] using R.isPointed_posRootCone _ hpos hneg)⟩
  have hnd : ¬ A.cartanCoxeterMatrix.toCoxeterSystem.IsRightDescent w₀ i := by
    rwa [R.isRightDescent_coxeterHom_iff hA, hcox]
  exact hcox ▸ R.coxeterHom_smul_root_mem_posRootCone_of_not_isRightDescent hA _ _ rfl i hnd

theorem length_mul_simpleReflectionMem_lt_iff (w : R.weylGroup (hA.diag_map K)) (i : I) :
    R.length (hA.diag_map K) (w * R.simpleReflectionMem (hA.diag_map K) i) <
        R.length (hA.diag_map K) w ↔ -(w • R.root i) ∈ R.posRootCone := by
  rw [← R.weylCoxeterSystem_length hA, ← R.weylCoxeterSystem_length hA,
    ← R.weylCoxeterSystem_simple hA]
  exact R.isRightDescent_weylCoxeterSystem_iff hA w i

theorem eq_one_of_forall_smul_root_eq {w : R.weylGroup (hA.diag_map K)}
    (hw : ∀ i, w • R.root i = R.root i) : w = 1 := by
  refine (R.coxeterEquiv hA).symm.injective
    ((R.eq_one_of_forall_coxeterHom_smul_root_eq hA fun i ↦ ?_).trans (map_one _).symm)
  exact (congrArg (· • R.root i) ((R.coxeterEquiv hA).apply_symm_apply w)).trans (hw i)

theorem rootLatticeAut_injective : Function.Injective (R.rootLatticeAut (hA.diag_map K)) :=
  (injective_iff_map_eq_one _).mpr fun _ hw ↦ R.eq_one_of_forall_smul_root_eq hA fun i ↦ by
    simpa using congrArg (fun f : R.rootLattice ≃ₗ[ℤ] R.rootLattice ↦
      (f ⟨R.root i, R.root_mem_rootLattice i⟩ : Dual K H)) hw

end

theorem isCoxeterGroup_weylGroup {I' K' H' : Type u} [Field K'] [CharZero K'] [AddCommGroup H']
    [Module K' H'] {A' : Matrix I' I' ℤ} (R' : CartanRealization (A'.map (Int.cast : ℤ → K')) H')
    (hA' : A'.IsGeneralizedCartan) : IsCoxeterGroup (R'.weylGroup (hA'.diag_map K')) :=
  ⟨⟨I', A'.cartanCoxeterMatrix, ⟨R'.weylCoxeterSystem hA'⟩⟩⟩

end GeneralizedCartan

section Checks

variable {K H : Type*} [Field K] [AddCommGroup H] [Module K H]

@[simp] theorem weylGroup_eq_bot_of_isEmpty {I : Type*} [IsEmpty I] {A : Matrix I I K}
    (R : CartanRealization A H) (hdiag : ∀ i, A i i = 2) : R.weylGroup hdiag = ⊥ := by
  simp [weylGroup_def, Set.range_eq_empty]
instance subsingleton_weylGroup_of_isEmpty {I : Type*} [IsEmpty I] {A : Matrix I I K}
    (R : CartanRealization A H) (hdiag : ∀ i, A i i = 2) : Subsingleton (R.weylGroup hdiag) := by
  rw [R.weylGroup_eq_bot_of_isEmpty hdiag]; infer_instance

theorem simpleReflection_eq_neg_of_corootSpan_eq_top_fin_one {A : Matrix (Fin 1) (Fin 1) K}
    (R : CartanRealization A H) (hdiag : ∀ i, A i i = 2) (hmin : R.corootSpan = ⊤)
    (ω : Dual K H) : R.simpleReflection hdiag 0 ω = -ω := by
  ext h; have hh : h ∈ R.corootSpan := hmin ▸ Submodule.mem_top; rw [R.corootSpan_def] at hh
  induction hh using Submodule.span_induction with
  | mem _ hx =>
    obtain ⟨i, rfl⟩ := hx; obtain rfl : i = 0 := Subsingleton.elim i 0
    rw [simpleReflection_apply, LinearMap.sub_apply, LinearMap.smul_apply, R.root_coroot, hdiag 0,
      smul_eq_mul, LinearMap.neg_apply]; ring
  | zero => simp
  | add _ _ _ _ ihx ihy => simp [ihx, ihy, add_comm]
  | smul _ _ _ ih => simp [ih]

theorem simpleReflection_mul_root_two_neg_two
    (R : CartanRealization ((!![2, -2; -2, 2] : Matrix (Fin 2) (Fin 2) ℤ).map
      (Int.cast : ℤ → K)) H)
    (hdiag : ∀ i, (!![2, -2; -2, 2] : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → K) i i = 2) :
    (R.simpleReflection hdiag 0 * R.simpleReflection hdiag 1) (R.root 1) =
      -R.root 1 - (2 : ℤ) • R.root 0 := by
  rw [mul_apply_eq_comp, simpleReflection_root_self, map_neg, simpleReflection_root_int]
  have h01 : (!![2, -2; -2, 2] : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = -2 := rfl
  rw [h01, neg_zsmul, sub_neg_eq_add, neg_add, sub_eq_add_neg]

@[simp] theorem cartanCoxeterMatrix_B_two_zero_one :
    (CartanMatrix.B 2).cartanCoxeterMatrix 0 1 = 4 := by
  have hprod : CartanMatrix.B 2 0 1 * CartanMatrix.B 2 1 0 = 2 := by decide
  rw [Matrix.cartanCoxeterMatrix_of_ne_of_le _ (by decide) (by omega), hprod,
    TauCeti.coxeterOrder_two]
theorem isGeneralizedCartan_two_neg_two :
    (!![2, -2; -2, 2] : Matrix (Fin 2) (Fin 2) ℤ).IsGeneralizedCartan :=
  ⟨fun i ↦ by fin_cases i <;> decide, fun i j _ ↦ by fin_cases i <;> fin_cases j <;> simp_all,
    fun i j ↦ by fin_cases i <;> fin_cases j <;> decide⟩
@[simp] theorem cartanCoxeterMatrix_two_neg_two_zero_one :
    (!![2, -2; -2, 2] : Matrix (Fin 2) (Fin 2) ℤ).cartanCoxeterMatrix 0 1 = 0 :=
  Matrix.cartanCoxeterMatrix_of_ne_of_lt _ (by decide) (by decide)

variable [CharZero K]

/-- **Type `A₁`**: the Weyl group is isomorphic to `Multiplicative (ZMod 2)` via length parity. -/
noncomputable def weylGroupAOneEquivZModTwo
    (R : CartanRealization ((CartanMatrix.A 1).map (Int.cast : ℤ → K)) H) :
    R.weylGroup ((CartanMatrix.isGeneralizedCartan_A 1).diag_map K) ≃* Multiplicative (ZMod 2) :=
  (R.weylCoxeterSystem (CartanMatrix.isGeneralizedCartan_A 1)).uniqueEquivZModTwo
@[simp] theorem natCard_weylGroup_A_one
    (R : CartanRealization ((CartanMatrix.A 1).map (Int.cast : ℤ → K)) H) :
    Nat.card (R.weylGroup ((CartanMatrix.isGeneralizedCartan_A 1).diag_map K)) = 2 :=
  (R.weylCoxeterSystem (CartanMatrix.isGeneralizedCartan_A 1)).natCard_of_unique

/-- **Rank-two generalized Cartan matrices**: `R.weylGroup` is isomorphic to `DihedralGroup`. -/
noncomputable def weylGroupFinTwoEquivDihedralGroup {A : Matrix (Fin 2) (Fin 2) ℤ}
    (hA : A.IsGeneralizedCartan) (R : CartanRealization (A.map (Int.cast : ℤ → K)) H) :
    R.weylGroup (hA.diag_map K) ≃* DihedralGroup (A.cartanCoxeterMatrix 0 1) :=
  (R.weylCoxeterSystem hA).finTwoEquivDihedralGroup
@[simp] theorem natCard_weylGroup_fin_two {A : Matrix (Fin 2) (Fin 2) ℤ}
    (hA : A.IsGeneralizedCartan) (R : CartanRealization (A.map (Int.cast : ℤ → K)) H) :
    Nat.card (R.weylGroup (hA.diag_map K)) = 2 * A.cartanCoxeterMatrix 0 1 :=
  (R.weylCoxeterSystem hA).natCard_of_fin_two

@[simp] theorem natCard_weylGroup_B_two
    (R : CartanRealization ((CartanMatrix.B 2).map (Int.cast : ℤ → K)) H) :
    Nat.card (R.weylGroup ((CartanMatrix.isGeneralizedCartan_B 2).diag_map K)) = 8 := by
  rw [R.natCard_weylGroup_fin_two (CartanMatrix.isGeneralizedCartan_B 2),
    cartanCoxeterMatrix_B_two_zero_one]
@[simp] theorem natCard_weylGroup_G₂
    (R : CartanRealization (CartanMatrix.G₂.map (Int.cast : ℤ → K)) H) :
    Nat.card (R.weylGroup (CartanMatrix.isGeneralizedCartan_G₂.diag_map K)) = 12 := by
  have hm : CartanMatrix.G₂.cartanCoxeterMatrix 0 1 = 6 := by
    rw [CartanMatrix.cartanCoxeterMatrix_G₂]; rfl
  rw [R.natCard_weylGroup_fin_two CartanMatrix.isGeneralizedCartan_G₂, hm]

/-- **Affine `A₁⁽¹⁾`**: its Weyl group is isomorphic to `DihedralGroup 0`. -/
noncomputable def weylGroupTwoNegTwoEquivDihedralGroup
    (R : CartanRealization ((!![2, -2; -2, 2] : Matrix (Fin 2) (Fin 2) ℤ).map
      (Int.cast : ℤ → K)) H) :
    R.weylGroup (isGeneralizedCartan_two_neg_two.diag_map K) ≃* DihedralGroup 0 := by
  have h := R.weylGroupFinTwoEquivDihedralGroup isGeneralizedCartan_two_neg_two
  rwa [cartanCoxeterMatrix_two_neg_two_zero_one] at h
theorem orderOf_simpleReflectionMem_mul_two_neg_two
    (R : CartanRealization ((!![2, -2; -2, 2] : Matrix (Fin 2) (Fin 2) ℤ).map
      (Int.cast : ℤ → K)) H) :
    orderOf (R.simpleReflectionMem (isGeneralizedCartan_two_neg_two.diag_map K) 0 *
      R.simpleReflectionMem (isGeneralizedCartan_two_neg_two.diag_map K) 1) = 0 := by simp

end Checks

end TauCeti.CartanRealization

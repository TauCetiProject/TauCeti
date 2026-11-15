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

Let `R` be a `TauCeti.CartanRealization` of a square matrix `A` over a field `K`. Building on
`TauCeti.LinearAlgebra.Matrix.Cartan.Realization.Reflection` and
`TauCeti.LinearAlgebra.Matrix.Cartan.Coxeter.Matrix`, this file proves the Coxeter-group
theorems for the Weyl group of a generalized Cartan matrix (Kac, *Infinite-dimensional Lie
algebras*, §3.7–§3.13):

* **Central-enlargement invariance**: restricting a realization to any subspace `M` with
  `R.corootSpan ≤ M` and `M ⊔ R.cartanCenter = ⊤` (in particular a minimal sub-realization) induces
  canonical isomorphisms on the root lattice (`restrictRootLatticeEquiv`) and on the Weyl group
  (`restrictWeylGroupEquiv`), intertwining `rootLatticeAut`
  (`restrictRootLatticeEquiv_rootLatticeAut`).
* **Braid relations and pairwise orders**: for any `A : Matrix I I ℤ` with diagonal `2` and
  symmetric zero pattern, `(sᵢ sⱼ) ^ (A.cartanCoxeterMatrix i j) = 1`; over a field of
  characteristic zero, `orderOf (sᵢ sⱼ) = A.cartanCoxeterMatrix i j` (`1` on the diagonal,
  `2, 3, 4, 6` for off-diagonal Cartan products `0, 1, 2, 3`, and `0` beyond `3`).
* **Coxeter presentation and length characterization** (Kac, Lemma 3.11 and Proposition 3.13): for
  a generalized Cartan matrix `A` over a characteristic-zero field `K`, the lift
  `coxeterHom : A.cartanCoxeterMatrix.Group →* R.weylGroup _` is an isomorphism (`coxeterEquiv`),
  equipping `R.weylGroup _` with a `CoxeterSystem A.cartanCoxeterMatrix` (`weylCoxeterSystem`) whose
  length agrees with `R.length`, satisfying `ℓ(w sᵢ) < ℓ(w) ↔ -(w • αᵢ) ∈ R.posRootCone`, and acting
  faithfully on `R.rootLattice` (`rootLatticeAut_injective`).
* **Low-rank and affine checks**: rank `0` (`IsEmpty I`), rank `1` (`A₁`), general rank `2`
  (`R.weylGroup _ ≃* DihedralGroup (A.cartanCoxeterMatrix 0 1)`), finite types `B₂` and `G₂`, and
  affine `A₁⁽¹⁾` (`!![2, -2; -2, 2]`, whose Weyl group is the infinite dihedral group
  `DihedralGroup 0`).

Note that `CoxeterSystem.reflectionRepresentation` in
`TauCeti.GroupTheory.Coxeter.Geometric.Integral` requires symmetric matrices matching
`-2 cos(π / M i j)`, which excludes nonsymmetric Cartan matrices (`B₂`, `G₂`) and arbitrary
off-diagonal entries with `A i j * A j i > 3`. Here the argument is purely algebraic over any
characteristic-zero field `K`: Mathlib's Chebyshev reflection power formulas and the bounds of
`TauCeti.RingTheory.Polynomial.Chebyshev.Bounds` supply rank-two root positivity, and parabolic
coset factorization (`CoxeterSystem.existsUnique_isMinimalCosetRep_mul`) lifts it to arbitrary rank.

## Main definitions

* `TauCeti.CartanRealization.restrictRootLatticeEquiv`,
  `TauCeti.CartanRealization.restrictWeylGroupEquiv`: invariance of `Q` and `W` under restriction
  to a sub-realization.
* `TauCeti.CartanRealization.coxeterHom`, `TauCeti.CartanRealization.coxeterEquiv`,
  `TauCeti.CartanRealization.weylCoxeterSystem`: the Coxeter presentation of the Weyl group.
* `TauCeti.CartanRealization.weylGroupFinTwoEquivDihedralGroup`: identification of any rank-two
  Weyl group with `DihedralGroup (A.cartanCoxeterMatrix 0 1)`.

## References

* V. G. Kac, *Infinite-dimensional Lie algebras*, third edition, Cambridge University Press, 1990,
  §3.7, Lemma 3.11, and Proposition 3.13.
-/

public section

open Module Polynomial.Chebyshev

namespace TauCeti.CartanRealization

/-! ### Invariance of the root lattice and Weyl group under sub-realizations -/

section Restriction

variable {I K H : Type*} [Field K] [AddCommGroup H] [Module K H] {A : Matrix I I K}
  (R : CartanRealization A H)

theorem apply_eq_zero_of_mem_rootLattice_of_mem_cartanCenter {φ : Dual K H}
    (hφ : φ ∈ R.rootLattice) {z : H} (hz : z ∈ R.cartanCenter) : φ z = 0 := by
  rw [R.rootLattice_def] at hφ
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact (R.mem_cartanCenter_iff z).mp hz i
  | zero => rfl
  | add x y _ _ ihx ihy => simp [ihx, ihy]
  | smul n x _ ih => simp [ih]

@[simp]
theorem dualMap_subtype_root (M : Submodule K H) (hc : R.corootSpan ≤ M)
    (hs : M ⊔ R.cartanCenter = ⊤) (i : I) :
    M.subtype.dualMap (R.root i) = (R.restrict M hc hs).root i := by
  ext m
  simp

private theorem dualMap_subtype_mem_restrict_rootLattice (M : Submodule K H)
    (hc : R.corootSpan ≤ M) (hs : M ⊔ R.cartanCenter = ⊤) {φ : Dual K H}
    (hφ : φ ∈ R.rootLattice) :
    M.subtype.dualMap φ ∈ (R.restrict M hc hs).rootLattice := by
  rw [R.rootLattice_def] at hφ
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    rw [R.dualMap_subtype_root M hc hs i]
    exact (R.restrict M hc hs).root_mem_rootLattice i
  | zero => simp
  | add x y _ _ ihx ihy => rw [map_add]; exact add_mem ihx ihy
  | smul n x _ ih => rw [map_zsmul]; exact Submodule.smul_mem _ n ih

private theorem injOn_dualMap_subtype_rootLattice (M : Submodule K H)
    (hs : M ⊔ R.cartanCenter = ⊤) : Set.InjOn M.subtype.dualMap R.rootLattice := by
  intro φ₁ hφ₁ φ₂ hφ₂ h
  rw [← sub_eq_zero]
  ext x
  have hx : x ∈ M ⊔ R.cartanCenter := hs ▸ Submodule.mem_top
  obtain ⟨m, hm, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
  have hm0 : (φ₁ - φ₂) m = 0 := by
    have hm' := congrArg (fun f : Dual K M ↦ f ⟨m, hm⟩) h
    simpa [sub_eq_zero] using hm'
  have hz0 := R.apply_eq_zero_of_mem_rootLattice_of_mem_cartanCenter (sub_mem hφ₁ hφ₂) hz
  rw [map_add, hm0, hz0, add_zero]
  rfl

private theorem exists_rootLattice_dualMap_subtype_eq (M : Submodule K H)
    (hc : R.corootSpan ≤ M) (hs : M ⊔ R.cartanCenter = ⊤) {ψ : Dual K M}
    (hψ : ψ ∈ (R.restrict M hc hs).rootLattice) :
    ∃ α : R.rootLattice, M.subtype.dualMap α.1 = ψ := by
  rw [(R.restrict M hc hs).rootLattice_def] at hψ
  induction hψ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact ⟨⟨R.root i, R.root_mem_rootLattice i⟩, R.dualMap_subtype_root M hc hs i⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ ihx ihy =>
    obtain ⟨α₁, rfl⟩ := ihx
    obtain ⟨α₂, rfl⟩ := ihy
    exact ⟨α₁ + α₂, map_add M.subtype.dualMap α₁.1 α₂.1⟩
  | smul n x _ ih =>
    obtain ⟨α, rfl⟩ := ih
    exact ⟨n • α, map_zsmul M.subtype.dualMap n α.1⟩

/-- **Restriction to a sub-realization identifies root lattices.** In particular, a central
enlargement has canonically the same root lattice `Q` as its minimal sub-realization. -/
noncomputable def restrictRootLatticeEquiv (M : Submodule K H) (hc : R.corootSpan ≤ M)
    (hs : M ⊔ R.cartanCenter = ⊤) :
    R.rootLattice ≃ₗ[ℤ] (R.restrict M hc hs).rootLattice :=
  LinearEquiv.ofBijective
    { toFun α := ⟨M.subtype.dualMap α.1, R.dualMap_subtype_mem_restrict_rootLattice M hc hs α.2⟩
      map_add' α β := Subtype.ext (map_add M.subtype.dualMap α.1 β.1)
      map_smul' n α := Subtype.ext (map_zsmul M.subtype.dualMap n α.1) }
    ⟨fun α β h ↦ Subtype.ext <|
      R.injOn_dualMap_subtype_rootLattice M hs α.2 β.2 (congrArg Subtype.val h),
      fun β ↦ (R.exists_rootLattice_dualMap_subtype_eq M hc hs β.2).imp fun _ ↦ Subtype.ext⟩

@[simp]
theorem coe_restrictRootLatticeEquiv_apply (M : Submodule K H) (hc : R.corootSpan ≤ M)
    (hs : M ⊔ R.cartanCenter = ⊤) (α : R.rootLattice) :
    (R.restrictRootLatticeEquiv M hc hs α : Dual K M) = M.subtype.dualMap (α : Dual K H) :=
  (rfl)

@[simp]
theorem restrictRootLatticeEquiv_root (M : Submodule K H) (hc : R.corootSpan ≤ M)
    (hs : M ⊔ R.cartanCenter = ⊤) (i : I) :
    R.restrictRootLatticeEquiv M hc hs ⟨R.root i, R.root_mem_rootLattice i⟩ =
      ⟨(R.restrict M hc hs).root i, (R.restrict M hc hs).root_mem_rootLattice i⟩ :=
  Subtype.ext (R.dualMap_subtype_root M hc hs i)

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
      map_add' m₁ m₂ := Subtype.ext (map_add (R.corootAut hdiag w) m₁.1 m₂.1)
      map_smul' c m := Subtype.ext (map_smul (R.corootAut hdiag w) c m.1)
      invFun m := ⟨R.corootAut hdiag w⁻¹ m, R.corootAut_mem_of_corootSpan_le hdiag hc w⁻¹ m.2⟩
      left_inv m := Subtype.ext <| by
        have h : (R.corootAut hdiag w⁻¹ * R.corootAut hdiag w) m.1 = m.1 := by
          rw [← map_mul, inv_mul_cancel, map_one]
          simp
        exact (mul_apply_eq_comp _ _ _).symm.trans h
      right_inv m := Subtype.ext <| by
        have h : (R.corootAut hdiag w * R.corootAut hdiag w⁻¹) m.1 = m.1 := by
          rw [← map_mul, mul_inv_cancel, map_one]
          simp
        exact (mul_apply_eq_comp _ _ _).symm.trans h }
  map_one' := by ext m; simp
  map_mul' w₁ w₂ := by ext m; simp [mul_apply_eq_comp]

private theorem restrictCorootAut_simpleReflectionMem (hdiag : ∀ i, A i i = 2) (M : Submodule K H)
    (hc : R.corootSpan ≤ M) (hs : M ⊔ R.cartanCenter = ⊤) (i : I) :
    R.restrictCorootAut hdiag M hc (R.simpleReflectionMem hdiag i) =
      (R.restrict M hc hs).corootReflection hdiag i := by
  ext m
  simp only [restrictCorootAut, MonoidHom.coe_mk, OneHom.coe_mk, LinearEquiv.coe_mk,
    LinearMap.coe_mk, AddHom.coe_mk, corootAut_simpleReflectionMem]
  exact (R.coe_restrict_corootReflection hdiag M hc hs i m).symm

private theorem restrictCorootAut_mem (hdiag : ∀ i, A i i = 2) (M : Submodule K H)
    (hc : R.corootSpan ≤ M) (hs : M ⊔ R.cartanCenter = ⊤) (w : R.weylGroup hdiag) :
    R.restrictCorootAut hdiag M hc w ∈ (R.restrict M hc hs).corootWeylGroup hdiag := by
  obtain ⟨l, rfl⟩ := R.exists_wordProd_eq hdiag w
  induction l with
  | nil => simp
  | cons i l ih =>
    rw [wordProd_cons, map_mul, R.restrictCorootAut_simpleReflectionMem hdiag M hc hs i]
    exact mul_mem (by simpa using ((R.restrict M hc hs).corootReflectionMem hdiag i).2) ih

private noncomputable def restrictWeylGroupHom (M : Submodule K H) (hc : R.corootSpan ≤ M)
    (hs : M ⊔ R.cartanCenter = ⊤) (hdiag : ∀ i, A i i = 2) :
    R.weylGroup hdiag →* (R.restrict M hc hs).weylGroup hdiag :=
  ((R.restrict M hc hs).corootWeylEquiv hdiag).toMonoidHom.comp
    { toFun w := ⟨R.restrictCorootAut hdiag M hc w, R.restrictCorootAut_mem hdiag M hc hs w⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' w₁ w₂ := Subtype.ext (map_mul _ w₁ w₂) }

private theorem restrictWeylGroupHom_simpleReflectionMem (M : Submodule K H)
    (hc : R.corootSpan ≤ M) (hs : M ⊔ R.cartanCenter = ⊤) (hdiag : ∀ i, A i i = 2) (i : I) :
    R.restrictWeylGroupHom M hc hs hdiag (R.simpleReflectionMem hdiag i) =
      (R.restrict M hc hs).simpleReflectionMem hdiag i := by
  have hmem : (⟨R.restrictCorootAut hdiag M hc (R.simpleReflectionMem hdiag i),
      R.restrictCorootAut_mem hdiag M hc hs _⟩ :
      (R.restrict M hc hs).corootWeylGroup hdiag) =
      (R.restrict M hc hs).corootReflectionMem hdiag i :=
    Subtype.ext <| (R.restrictCorootAut_simpleReflectionMem hdiag M hc hs i).trans
      ((R.restrict M hc hs).coe_corootReflectionMem hdiag i).symm
  simp [restrictWeylGroupHom, hmem]

private theorem restrictWeylGroupHom_bijective (M : Submodule K H) (hc : R.corootSpan ≤ M)
    (hs : M ⊔ R.cartanCenter = ⊤) (hdiag : ∀ i, A i i = 2) :
    Function.Bijective (R.restrictWeylGroupHom M hc hs hdiag) := by
  refine ⟨(injective_iff_map_eq_one _).mpr fun w hw ↦ R.corootAut_injective hdiag ?_, fun w' ↦ ?_⟩
  · have hM : R.restrictCorootAut hdiag M hc w = 1 :=
      congrArg Subtype.val <|
        ((R.restrict M hc hs).corootWeylEquiv hdiag).injective (hw.trans (map_one _).symm)
    ext x
    obtain ⟨m, hm, z, hz, rfl⟩ := Submodule.mem_sup.mp (hs ▸ Submodule.mem_top : x ∈ _)
    have hm' : R.corootAut hdiag w m = m :=
      congrArg Subtype.val (congrArg (fun f : M ≃ₗ[K] M ↦ f ⟨m, hm⟩) hM)
    rw [map_add, hm', R.corootAut_eq_self_of_mem_cartanCenter hdiag w hz]
    simp
  · obtain ⟨l, rfl⟩ := (R.restrict M hc hs).exists_wordProd_eq hdiag w'
    refine ⟨R.wordProd hdiag l, ?_⟩
    induction l with
    | nil => simp
    | cons i l ih =>
      rw [wordProd_cons, wordProd_cons, map_mul, ih,
        R.restrictWeylGroupHom_simpleReflectionMem M hc hs hdiag i]

/-- **The Weyl group of a realization is canonically isomorphic to that of any sub-realization.**
In particular, adding central directions does not change the Weyl group. -/
noncomputable def restrictWeylGroupEquiv (M : Submodule K H) (hc : R.corootSpan ≤ M)
    (hs : M ⊔ R.cartanCenter = ⊤) (hdiag : ∀ i, A i i = 2) :
    R.weylGroup hdiag ≃* (R.restrict M hc hs).weylGroup hdiag :=
  MulEquiv.ofBijective (R.restrictWeylGroupHom M hc hs hdiag)
    (R.restrictWeylGroupHom_bijective M hc hs hdiag)

@[simp]
theorem restrictWeylGroupEquiv_simpleReflectionMem (M : Submodule K H) (hc : R.corootSpan ≤ M)
    (hs : M ⊔ R.cartanCenter = ⊤) (hdiag : ∀ i, A i i = 2) (i : I) :
    R.restrictWeylGroupEquiv M hc hs hdiag (R.simpleReflectionMem hdiag i) =
      (R.restrict M hc hs).simpleReflectionMem hdiag i :=
  R.restrictWeylGroupHom_simpleReflectionMem M hc hs hdiag i

theorem dualMap_subtype_smul (M : Submodule K H) (hc : R.corootSpan ≤ M)
    (hs : M ⊔ R.cartanCenter = ⊤) (hdiag : ∀ i, A i i = 2) (w : R.weylGroup hdiag)
    (φ : Dual K H) :
    M.subtype.dualMap (w • φ) =
      R.restrictWeylGroupEquiv M hc hs hdiag w • M.subtype.dualMap φ := by
  obtain ⟨l, rfl⟩ := R.exists_wordProd_eq hdiag w
  induction l generalizing φ with
  | nil => simp
  | cons i l ih =>
    rw [wordProd_cons, map_mul, restrictWeylGroupEquiv_simpleReflectionMem, mul_smul, mul_smul,
      ← ih]
    simp only [Subgroup.smul_def, coe_simpleReflectionMem, LinearEquiv.smul_def]
    exact R.dualMap_subtype_simpleReflection hdiag M hc hs i _

/-- Restriction to a sub-realization intertwines the Weyl-group action `rootLatticeAut` on `Q`. -/
@[simp]
theorem restrictRootLatticeEquiv_rootLatticeAut {I K H : Type*} [Field K] [AddCommGroup H]
    [Module K H] {A : Matrix I I ℤ} (R : CartanRealization (A.map (Int.cast : ℤ → K)) H)
    (M : Submodule K H) (hc : R.corootSpan ≤ M) (hs : M ⊔ R.cartanCenter = ⊤)
    (hdiag : ∀ i, A.map (Int.cast : ℤ → K) i i = 2) (w : R.weylGroup hdiag)
    (α : R.rootLattice) :
    R.restrictRootLatticeEquiv M hc hs (R.rootLatticeAut hdiag w α) =
      (R.restrict M hc hs).rootLatticeAut hdiag (R.restrictWeylGroupEquiv M hc hs hdiag w)
        (R.restrictRootLatticeEquiv M hc hs α) := by
  apply Subtype.ext
  simp [R.dualMap_subtype_smul M hc hs hdiag w α.1]

end Restriction

/-! ### Rank-two Chebyshev reflection formulas and braid relations -/

section BraidRelations

variable {I K H : Type*} [Field K] [AddCommGroup H] [Module K H] {A : Matrix I I ℤ}
  (R : CartanRealization (A.map (Int.cast : ℤ → K)) H)
  (hdiag : ∀ i, A.map (Int.cast : ℤ → K) i i = 2)

theorem simpleReflection_mul_pow_root (i j : I) (m : ℕ) :
    ((R.simpleReflection hdiag i * R.simpleReflection hdiag j) ^ m) (R.root i) =
      ((S ℤ m).eval (A i j * A j i - 2) +
          (S ℤ ((m : ℤ) - 1)).eval (A i j * A j i - 2)) • R.root i +
        ((S ℤ ((m : ℤ) - 1)).eval (A i j * A j i - 2) * -A j i) • R.root j := by
  rw [simpleReflection_eq_reflection, simpleReflection_eq_reflection,
    Module.reflection_mul_reflection_pow_apply_self]
  have ht : Dual.eval K H (R.coroot i) (R.root j) * Dual.eval K H (R.coroot j) (R.root i) - 2 =
      algebraMap ℤ K (A i j * A j i - 2) := by
    simp [R.root_coroot]
  rw [ht, ← algebraMap_eval_S, ← algebraMap_eval_S]
  simp only [eq_intCast, Dual.eval_apply, R.root_coroot, Matrix.map_apply]
  rw [← Int.cast_add, Int.cast_smul_eq_zsmul, ← Int.cast_neg, ← Int.cast_mul,
    Int.cast_smul_eq_zsmul]

theorem simpleReflection_mul_simpleReflection_mul_pow_root (i j : I) (m : ℕ) :
    (R.simpleReflection hdiag j *
        (R.simpleReflection hdiag i * R.simpleReflection hdiag j) ^ m) (R.root i) =
      ((S ℤ m).eval (A i j * A j i - 2) +
          (S ℤ ((m : ℤ) - 1)).eval (A i j * A j i - 2)) • R.root i +
        ((S ℤ m).eval (A i j * A j i - 2) * -A j i) • R.root j := by
  rw [simpleReflection_eq_reflection, simpleReflection_eq_reflection,
    Module.reflection_mul_reflection_mul_reflection_pow_apply_self]
  have ht : Dual.eval K H (R.coroot i) (R.root j) * Dual.eval K H (R.coroot j) (R.root i) - 2 =
      algebraMap ℤ K (A i j * A j i - 2) := by
    simp [R.root_coroot]
  rw [ht, ← algebraMap_eval_S, ← algebraMap_eval_S]
  simp only [eq_intCast, Dual.eval_apply, R.root_coroot, Matrix.map_apply]
  rw [← Int.cast_add, Int.cast_smul_eq_zsmul, ← Int.cast_neg, ← Int.cast_mul,
    Int.cast_smul_eq_zsmul]

private theorem simpleReflection_comm_of_apply_eq_zero {i j : I} (hij0 : A i j = 0)
    (hji0 : A j i = 0) :
    R.simpleReflection hdiag i * R.simpleReflection hdiag j =
      R.simpleReflection hdiag j * R.simpleReflection hdiag i := by
  ext φ h
  simp only [mul_apply_eq_comp, simpleReflection_apply, map_sub, map_smul, R.root_coroot,
    Matrix.map_apply, hij0, hji0, Int.cast_zero, zero_smul, sub_zero, LinearMap.sub_apply,
    LinearMap.smul_apply, smul_eq_mul]
  ring

private theorem simpleReflection_mul_pow_eq_one_of_mem {i j : I}
    (hmem : A i j * A j i ∈ ({1, 2, 3} : Set ℤ)) :
    (R.simpleReflection hdiag i * R.simpleReflection hdiag j) ^
        TauCeti.coxeterOrder (A i j * A j i) = 1 := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with hc | hc | hc
  · rw [hc, TauCeti.coxeterOrder_one]
    have hprod : (A i j : K) * (A j i : K) = 1 := by
      rw [← Int.cast_mul, hc]
      norm_num
    ext φ h
    rw [simpleReflection_eq_reflection, simpleReflection_eq_reflection,
      Module.reflection_mul_reflection_pow_apply]
    simp [R.root_coroot, hprod, S_zero, S_one]
    ring
  · rw [hc, TauCeti.coxeterOrder_two]
    have hprod : (A i j : K) * (A j i : K) = 2 := by
      rw [← Int.cast_mul, hc]
      norm_num
    ext φ h
    rw [simpleReflection_eq_reflection, simpleReflection_eq_reflection,
      Module.reflection_mul_reflection_pow_apply]
    simp [R.root_coroot, hprod, S_one]
  · rw [hc, TauCeti.coxeterOrder_three]
    have hprod : (A i j : K) * (A j i : K) = 3 := by
      rw [← Int.cast_mul, hc]
      norm_num
    ext φ h
    rw [simpleReflection_eq_reflection, simpleReflection_eq_reflection,
      Module.reflection_mul_reflection_pow_apply]
    simp [R.root_coroot, hprod, S_two]
    ring

/-- **Braid relation on `Dual K H`**: `(sᵢ sⱼ) ^ (A.cartanCoxeterMatrix i j) = 1` whenever `A` has
diagonal `2` in `K` and symmetric zero pattern. -/
theorem simpleReflection_mul_pow_cartanCoxeterMatrix
    (hzero : ∀ i j, A i j = 0 ↔ A j i = 0) (i j : I) :
    (R.simpleReflection hdiag i * R.simpleReflection hdiag j) ^ A.cartanCoxeterMatrix i j = 1 := by
  rcases eq_or_ne i j with rfl | hij
  · simp
  by_cases hmem : A i j * A j i ∈ ({0, 1, 2, 3} : Set ℤ)
  · have hle : A i j * A j i ≤ 3 := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
      omega
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
      rw [A.cartanCoxeterMatrix_of_ne hij]
      split_ifs with hle
      · rw [TauCeti.coxeterOrder_eq_zero_iff]
        intro hmem'
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem hmem'
        omega
      · rfl
    rw [hm0, pow_zero]

/-- **Braid relation in `R.weylGroup hdiag`.** -/
theorem simpleReflectionMem_mul_pow_cartanCoxeterMatrix
    (hzero : ∀ i j, A i j = 0 ↔ A j i = 0) (i j : I) :
    (R.simpleReflectionMem hdiag i * R.simpleReflectionMem hdiag j) ^
        A.cartanCoxeterMatrix i j = 1 := by
  apply Subtype.ext
  simpa using R.simpleReflection_mul_pow_cartanCoxeterMatrix hdiag hzero i j

private theorem linearIndependent_int_root_pair [CharZero K] {i j : I} (hij : i ≠ j) :
    LinearIndependent ℤ ![R.root i, R.root j] := by
  have hcomp : R.root ∘ ![i, j] = ![R.root i, R.root j] := by
    ext a
    fin_cases a <;> rfl
  rw [← hcomp]
  refine (R.root_linearIndependent.restrict_scalars' ℤ).comp ![i, j] fun a b hab ↦ ?_
  fin_cases a <;> fin_cases b <;> simp_all

private theorem false_of_chebyshev_dihedral_lt {a b : ℤ} {k : ℕ}
    (hmem : a * b ∈ ({0, 1, 2, 3} : Set ℤ)) (hlt : k + 1 < TauCeti.coxeterOrder (a * b))
    (hsum : (S ℤ ((k + 1 : ℕ) : ℤ)).eval (a * b - 2) + (S ℤ k).eval (a * b - 2) = 1)
    (hprod : (S ℤ k).eval (a * b - 2) * -b = 0) : False := by
  have hS3 := S_add_two ℤ 1
  have hS4 := S_add_two ℤ 2
  norm_num at hS3 hS4
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with hc | hc | hc | hc
  · rw [hc, TauCeti.coxeterOrder_zero] at hlt
    have hk0 : k = 0 := by omega
    subst hk0
    rw [hc] at hsum
    norm_num [S_zero, S_one] at hsum
  · have hb0 : b ≠ 0 := fun h0 ↦ by simp [h0] at hc
    rw [hc, TauCeti.coxeterOrder_one] at hlt
    have hk : k < 2 := by omega
    interval_cases k <;> rw [hc] at hprod <;> simp [hb0, S_zero, S_one] at hprod
  · have hb0 : b ≠ 0 := fun h0 ↦ by simp [h0] at hc
    rw [hc, TauCeti.coxeterOrder_two] at hlt
    have hk : k < 3 := by omega
    interval_cases k
    · rw [hc] at hprod; simp [hb0, S_zero] at hprod
    · rw [hc] at hsum; norm_num [S_one, S_two] at hsum
    · rw [hc] at hprod; simp [hb0, S_two] at hprod
  · have hb0 : b ≠ 0 := fun h0 ↦ by simp [h0] at hc
    rw [hc, TauCeti.coxeterOrder_three] at hlt
    have hk : k < 5 := by omega
    interval_cases k
    · rw [hc] at hprod; simp [hb0, S_zero] at hprod
    · rw [hc] at hprod; simp [hb0, S_one] at hprod
    · rw [hc] at hsum; norm_num [S_two, hS3] at hsum
    · rw [hc] at hprod; simp [hb0, S_two, hS3] at hprod
    · rw [hc] at hprod; simp [hb0, S_two, hS3, hS4] at hprod

private theorem simpleReflection_mul_pow_ne_one_of_lt [CharZero K] {i j : I} (hij : i ≠ j)
    {k : ℕ} (hk : A.cartanCoxeterMatrix i j = 0 ∨ k + 1 < A.cartanCoxeterMatrix i j) :
    (R.simpleReflection hdiag i * R.simpleReflection hdiag j) ^ (k + 1) ≠ 1 := by
  intro h1
  have hroot : ((R.simpleReflection hdiag i * R.simpleReflection hdiag j) ^ (k + 1)) (R.root i) =
      (1 : ℤ) • R.root i + (0 : ℤ) • R.root j := by
    simp [h1]
  rw [R.simpleReflection_mul_pow_root hdiag i j (k + 1)] at hroot
  have hidx : (((k + 1 : ℕ) : ℤ) - 1) = (k : ℤ) := by omega
  rw [hidx] at hroot
  obtain ⟨hsum, hprod⟩ := (R.linearIndependent_int_root_pair hij).eq_of_pair hroot
  by_cases hmem : A i j * A j i ∈ ({0, 1, 2, 3} : Set ℤ)
  · have hle : A i j * A j i ≤ 3 := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
      omega
    have hm := A.cartanCoxeterMatrix_of_ne_of_le hij hle
    have h2 : 2 ≤ A.cartanCoxeterMatrix i j := hm ▸ TauCeti.two_le_coxeterOrder hmem
    exact false_of_chebyshev_dihedral_lt hmem (hm ▸ hk.resolve_left (by omega)) hsum hprod
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hmem
    have haji : A j i ≠ 0 := fun h0 ↦ hmem.1 (by simp [h0])
    have habs : (2 : ℤ) ≤ |A i j * A j i - 2| := by
      rcases lt_or_gt_of_ne hmem.1 with hlt | hgt
      · rw [abs_of_neg (by omega)]; omega
      · rw [abs_of_nonneg (by omega)]; omega
    have hbound := natCast_add_one_le_abs_S_eval habs k
    have hSne : (S ℤ k).eval (A i j * A j i - 2) ≠ 0 := fun h0 ↦ by
      rw [h0, abs_zero] at hbound; omega
    exact mul_ne_zero hSne (neg_ne_zero.mpr haji) hprod

/-- **Exact pairwise orders of simple reflections.** Over a field of characteristic zero, the
product `sᵢ sⱼ` has order `A.cartanCoxeterMatrix i j` (`0` when `sᵢ sⱼ` has infinite order). -/
@[simp]
theorem orderOf_simpleReflectionMem_mul [CharZero K]
    (hzero : ∀ i j, A i j = 0 ↔ A j i = 0) (i j : I) :
    orderOf (R.simpleReflectionMem hdiag i * R.simpleReflectionMem hdiag j) =
      A.cartanCoxeterMatrix i j := by
  rcases eq_or_ne i j with rfl | hij
  · simp
  rcases Nat.eq_zero_or_pos (A.cartanCoxeterMatrix i j) with hm0 | hpos
  · rw [hm0, orderOf_eq_zero_iff']
    intro n hn hpow
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    have hpow' : (R.simpleReflection hdiag i * R.simpleReflection hdiag j) ^ (k + 1) = 1 := by
      simpa using congrArg Subtype.val hpow
    exact R.simpleReflection_mul_pow_ne_one_of_lt hdiag hij (Or.inl hm0) hpow'
  · rw [orderOf_eq_iff hpos]
    refine ⟨R.simpleReflectionMem_mul_pow_cartanCoxeterMatrix hdiag hzero i j, fun m hlt hm ↦ ?_⟩
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
    intro hpow
    have hpow' : (R.simpleReflection hdiag i * R.simpleReflection hdiag j) ^ (k + 1) = 1 := by
      simpa using congrArg Subtype.val hpow
    exact R.simpleReflection_mul_pow_ne_one_of_lt hdiag hij (Or.inr hlt) hpow'

/-- The canonical group homomorphism from `A.cartanCoxeterMatrix.Group` to `R.weylGroup hdiag`
sending each Coxeter generator `sᵢ` to `R.simpleReflectionMem hdiag i`. -/
noncomputable def coxeterHom (hzero : ∀ i j, A i j = 0 ↔ A j i = 0) :
    A.cartanCoxeterMatrix.Group →* R.weylGroup hdiag :=
  A.cartanCoxeterMatrix.toCoxeterSystem.lift
    ⟨R.simpleReflectionMem hdiag, R.simpleReflectionMem_mul_pow_cartanCoxeterMatrix hdiag hzero⟩

@[simp]
theorem coxeterHom_simple (hzero : ∀ i j, A i j = 0 ↔ A j i = 0) (i : I) :
    R.coxeterHom hdiag hzero (A.cartanCoxeterMatrix.simple i) = R.simpleReflectionMem hdiag i :=
  A.cartanCoxeterMatrix.toCoxeterSystem.lift_apply_simple _ i

@[simp]
theorem coxeterHom_wordProd (hzero : ∀ i j, A i j = 0 ↔ A j i = 0) (l : List I) :
    R.coxeterHom hdiag hzero (A.cartanCoxeterMatrix.toCoxeterSystem.wordProd l) =
      R.wordProd hdiag l := by
  induction l with
  | nil => simp
  | cons i l ih =>
    rw [CoxeterSystem.wordProd_cons, map_mul, ih, wordProd_cons]
    exact congrArg (· * R.wordProd hdiag l) (R.coxeterHom_simple hdiag hzero i)

theorem coxeterHom_surjective (hzero : ∀ i j, A i j = 0 ↔ A j i = 0) :
    Function.Surjective (R.coxeterHom hdiag hzero) := by
  intro w
  obtain ⟨l, rfl⟩ := R.exists_wordProd_eq hdiag w
  exact ⟨A.cartanCoxeterMatrix.toCoxeterSystem.wordProd l, R.coxeterHom_wordProd hdiag hzero l⟩

end BraidRelations

/-! ### Coxeter presentation, Kac's Lemma 3.11, and faithfulness on `Q` -/

section GeneralizedCartan

universe u

variable {I K H : Type*} [Field K] [AddCommGroup H] [Module K H] {A : Matrix I I ℤ}
  (R : CartanRealization (A.map (Int.cast : ℤ → K)) H)

private theorem alternatingWord_chebyshev_nonneg {c : ℤ} (hc0 : 0 ≤ c) {k : ℕ}
    (hk : 3 < c ∨ (c ≤ 3 ∧ k < TauCeti.coxeterOrder c)) :
    0 ≤ (S ℤ (k / 2)).eval (c - 2) + (S ℤ (((k / 2 : ℕ) : ℤ) - 1)).eval (c - 2) ∧
      0 ≤ (if Even k then (S ℤ (((k / 2 : ℕ) : ℤ) - 1)).eval (c - 2)
        else (S ℤ (k / 2)).eval (c - 2)) := by
  rcases hk with hgt | ⟨hle, hlt⟩
  · have ht : (2 : ℤ) ≤ c - 2 := by omega
    have h1 : 0 ≤ (S ℤ (k / 2)).eval (c - 2) := S_eval_nonneg ht (k / 2)
    have h2 : 0 ≤ (S ℤ (((k / 2 : ℕ) : ℤ) - 1)).eval (c - 2) := by
      rcases eq_or_ne (k / 2) 0 with h0 | hne
      · simp [h0, S_neg_one]
      · obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hne
        have hidx : (((m + 1 : ℕ) : ℤ) - 1) = (m : ℤ) := by omega
        rw [hm, Nat.succ_eq_add_one, hidx]
        exact S_eval_nonneg ht m
    refine ⟨add_nonneg h1 h2, ?_⟩
    split_ifs <;> assumption
  · rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3) with rfl | rfl | rfl | rfl
    · rw [TauCeti.coxeterOrder_zero] at hlt
      interval_cases k <;> norm_num [S_neg_one, S_zero]
    · rw [TauCeti.coxeterOrder_one] at hlt
      interval_cases k <;> norm_num [S_neg_one, S_zero, S_one]
    · rw [TauCeti.coxeterOrder_two] at hlt
      interval_cases k <;> norm_num [Nat.even_iff, S_neg_one, S_zero, S_one]
    · rw [TauCeti.coxeterOrder_three] at hlt
      interval_cases k <;> norm_num [Nat.even_iff, S_neg_one, S_zero, S_one, S_two]

private theorem exists_nsmul_alternatingWord_root (hA : A.IsGeneralizedCartan)
    {i j : I} (hij : i ≠ j) {k : ℕ}
    (hk : A.cartanCoxeterMatrix i j = 0 ∨ k < A.cartanCoxeterMatrix i j) :
    ∃ a b : ℕ,
      R.coxeterHom (hA.diag_map K) hA.zero_comm
          (A.cartanCoxeterMatrix.toCoxeterSystem.wordProd
            (CoxeterSystem.alternatingWord i j k)) • R.root i =
        a • R.root i + b • R.root j := by
  have hk' : 3 < A i j * A j i ∨
      (A i j * A j i ≤ 3 ∧ k < TauCeti.coxeterOrder (A i j * A j i)) := by
    rcases hk with h0 | hlt
    · exact Or.inl (((hA.cartanCoxeterMatrix_eq_zero_iff i j).mp h0).2)
    · by_cases hle : A i j * A j i ≤ 3
      · exact Or.inr ⟨hle, (A.cartanCoxeterMatrix_of_ne_of_le hij hle) ▸ hlt⟩
      · exact Or.inl (not_le.mp hle)
  obtain ⟨ha, hb⟩ := alternatingWord_chebyshev_nonneg (hA.mul_nonneg i j) hk'
  have hb' : 0 ≤ (if Even k then (S ℤ (((k / 2 : ℕ) : ℤ) - 1)).eval (A i j * A j i - 2)
      else (S ℤ (k / 2)).eval (A i j * A j i - 2)) * -A j i :=
    mul_nonneg hb (neg_nonneg.mpr (hA.offDiag_nonpos j i hij.symm))
  refine ⟨((S ℤ (k / 2)).eval (A i j * A j i - 2) +
      (S ℤ (((k / 2 : ℕ) : ℤ) - 1)).eval (A i j * A j i - 2)).toNat,
    ((if Even k then (S ℤ (((k / 2 : ℕ) : ℤ) - 1)).eval (A i j * A j i - 2)
      else (S ℤ (k / 2)).eval (A i j * A j i - 2)) * -A j i).toNat, ?_⟩
  rw [← natCast_zsmul, ← natCast_zsmul, Int.toNat_of_nonneg ha, Int.toNat_of_nonneg hb']
  rw [CoxeterSystem.prod_alternatingWord_eq_mul_pow]
  by_cases hev : Even k
  · simp only [hev, ↓reduceIte, one_mul, map_pow, map_mul,
      CoxeterMatrix.toCoxeterSystem_simple, coxeterHom_simple, Subgroup.smul_def,
      Subgroup.coe_pow, Subgroup.coe_mul, coe_simpleReflectionMem, LinearEquiv.smul_def]
    exact R.simpleReflection_mul_pow_root (hA.diag_map K) i j (k / 2)
  · simp only [hev, ↓reduceIte, map_mul, map_pow,
      CoxeterMatrix.toCoxeterSystem_simple, coxeterHom_simple, Subgroup.smul_def,
      Subgroup.coe_mul, Subgroup.coe_pow, coe_simpleReflectionMem, LinearEquiv.smul_def]
    exact R.simpleReflection_mul_simpleReflection_mul_pow_root (hA.diag_map K) i j (k / 2)

private theorem coxeterHom_smul_root_mem_posRootCone_of_not_isRightDescent
    (hA : A.IsGeneralizedCartan) :
    ∀ (n : ℕ) (w : A.cartanCoxeterMatrix.Group),
      A.cartanCoxeterMatrix.toCoxeterSystem.length w = n →
      ∀ i : I, ¬ A.cartanCoxeterMatrix.toCoxeterSystem.IsRightDescent w i →
        R.coxeterHom (hA.diag_map K) hA.zero_comm w • R.root i ∈ R.posRootCone := by
  let cs := A.cartanCoxeterMatrix.toCoxeterSystem
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro w hwn i hi
    rcases eq_or_ne w 1 with rfl | hw1
    · simpa using R.root_mem_posRootCone i
    obtain ⟨j, hj⟩ := cs.exists_rightDescent_of_ne_one hw1
    have hij : i ≠ j := fun h ↦ hi (h ▸ hj)
    obtain ⟨⟨u, v⟩, ⟨hu, hv, rfl⟩, -⟩ := cs.existsUnique_isMinimalCosetRep_mul {i, j} w
    have hlen : cs.length (u * v) = cs.length u + cs.length v :=
      cs.length_mul_of_isMinimalCosetRep hu hv
    have hui_nd : ¬ cs.IsRightDescent u i := cs.isMinimalCosetRep_iff.mp hu i (by simp)
    have huj_nd : ¬ cs.IsRightDescent u j := cs.isMinimalCosetRep_iff.mp hu j (by simp)
    have hv1 : v ≠ 1 := by
      rintro rfl
      exact huj_nd (by simpa using hj)
    have hvpos : 0 < cs.length v := Nat.pos_of_ne_zero fun h0 ↦ hv1 (cs.length_eq_zero_iff.mp h0)
    have hvi : ¬ cs.IsRightDescent v i := fun hdvi ↦ hi <| by
      have hvsi : v * cs.simple i ∈ cs.parabolic {i, j} :=
        mul_mem hv (cs.simple_mem_parabolic (by simp))
      rw [CoxeterSystem.IsRightDescent, mul_assoc, cs.length_mul_of_isMinimalCosetRep hu hvsi,
        hlen]
      exact Nat.add_lt_add_left hdvi _
    obtain ⟨hvw, hk⟩ := cs.wordProd_alternatingWord_eq_and_length_lt_of_mem_parabolic_pair hv hvi
    obtain ⟨a, b, hab⟩ := R.exists_nsmul_alternatingWord_root hA hij hk
    rw [hvw] at hab
    have hlt : cs.length u < n := (Nat.lt_add_of_pos_right hvpos).trans_eq (hlen.symm.trans hwn)
    have hui := ih (cs.length u) hlt u rfl i hui_nd
    have huj := ih (cs.length u) hlt u rfl j huj_nd
    rw [map_mul, mul_smul, hab, smul_add, smul_comm, smul_comm _ b]
    exact add_mem (Submodule.smul_mem _ a hui) (Submodule.smul_mem _ b huj)

variable [CharZero K]

private theorem isRightDescent_coxeterHom_iff (hA : A.IsGeneralizedCartan)
    (w : A.cartanCoxeterMatrix.Group) (i : I) :
    A.cartanCoxeterMatrix.toCoxeterSystem.IsRightDescent w i ↔
      -(R.coxeterHom (hA.diag_map K) hA.zero_comm w • R.root i) ∈ R.posRootCone := by
  let cs := A.cartanCoxeterMatrix.toCoxeterSystem
  have hnot_both : ¬ (R.coxeterHom (hA.diag_map K) hA.zero_comm w • R.root i ∈ R.posRootCone ∧
      -(R.coxeterHom (hA.diag_map K) hA.zero_comm w • R.root i) ∈ R.posRootCone) := by
    rintro ⟨hp, hn⟩
    have h0 := R.isPointed_posRootCone _ hp hn
    rw [Subgroup.smul_def, LinearEquiv.smul_def, LinearEquiv.map_eq_zero_iff] at h0
    exact R.root_linearIndependent.ne_zero i h0
  constructor
  · intro hd
    have hnd := cs.isRightDescent_iff_not_isRightDescent_mul.mp hd
    have hpos := R.coxeterHom_smul_root_mem_posRootCone_of_not_isRightDescent hA _ _ rfl i hnd
    have h1 : R.coxeterHom (hA.diag_map K) hA.zero_comm (cs.simple i) • R.root i = -R.root i := by
      simp [cs, Subgroup.smul_def, LinearEquiv.smul_def]
    rwa [map_mul, mul_smul, h1, smul_neg] at hpos
  · intro hneg
    by_contra hnd
    exact hnot_both ⟨R.coxeterHom_smul_root_mem_posRootCone_of_not_isRightDescent hA _ _ rfl i hnd,
      hneg⟩

private theorem eq_one_of_forall_coxeterHom_smul_root_eq (hA : A.IsGeneralizedCartan)
    {w : A.cartanCoxeterMatrix.Group}
    (hw : ∀ i, R.coxeterHom (hA.diag_map K) hA.zero_comm w • R.root i = R.root i) : w = 1 := by
  by_contra hw1
  obtain ⟨i, hi⟩ := A.cartanCoxeterMatrix.toCoxeterSystem.exists_rightDescent_of_ne_one hw1
  have hneg := (R.isRightDescent_coxeterHom_iff hA w i).mp hi
  rw [hw i] at hneg
  exact R.root_linearIndependent.ne_zero i
    (R.isPointed_posRootCone _ (R.root_mem_posRootCone i) hneg)

/-- **Injectivity of `coxeterHom` (Kac, Proposition 3.13).** -/
theorem coxeterHom_injective (hA : A.IsGeneralizedCartan) :
    Function.Injective (R.coxeterHom (hA.diag_map K) hA.zero_comm) := by
  refine (injective_iff_map_eq_one _).mpr fun w hw ↦
    R.eq_one_of_forall_coxeterHom_smul_root_eq hA fun i ↦ ?_
  rw [hw, one_smul]

/-- **Kac, Proposition 3.13.** The canonical isomorphism from `A.cartanCoxeterMatrix.Group` onto
the Weyl group `R.weylGroup (hA.diag_map K)` of a generalized Cartan matrix. -/
noncomputable def coxeterEquiv (hA : A.IsGeneralizedCartan) :
    A.cartanCoxeterMatrix.Group ≃* R.weylGroup (hA.diag_map K) :=
  MulEquiv.ofBijective (R.coxeterHom (hA.diag_map K) hA.zero_comm)
    ⟨R.coxeterHom_injective hA, R.coxeterHom_surjective (hA.diag_map K) hA.zero_comm⟩

@[simp]
theorem coxeterEquiv_simple (hA : A.IsGeneralizedCartan) (i : I) :
    R.coxeterEquiv hA (A.cartanCoxeterMatrix.simple i) =
      R.simpleReflectionMem (hA.diag_map K) i :=
  R.coxeterHom_simple (hA.diag_map K) hA.zero_comm i

/-- **The Weyl group as a Coxeter system** with Coxeter matrix `A.cartanCoxeterMatrix`. -/
noncomputable def weylCoxeterSystem (hA : A.IsGeneralizedCartan) :
    CoxeterSystem A.cartanCoxeterMatrix (R.weylGroup (hA.diag_map K)) :=
  A.cartanCoxeterMatrix.toCoxeterSystem.map (R.coxeterEquiv hA)

/-- When `I`, `K`, and `H` share a universe, `R.weylGroup (hA.diag_map K)` satisfies Mathlib's
`IsCoxeterGroup` predicate. -/
theorem isCoxeterGroup_weylGroup {I' K' H' : Type u} [Field K'] [CharZero K'] [AddCommGroup H']
    [Module K' H'] {A' : Matrix I' I' ℤ} (R' : CartanRealization (A'.map (Int.cast : ℤ → K')) H')
    (hA' : A'.IsGeneralizedCartan) :
    IsCoxeterGroup (R'.weylGroup (hA'.diag_map K')) :=
  ⟨⟨I', A'.cartanCoxeterMatrix, ⟨R'.weylCoxeterSystem hA'⟩⟩⟩

@[simp]
theorem weylCoxeterSystem_simple (hA : A.IsGeneralizedCartan) (i : I) :
    (R.weylCoxeterSystem hA).simple i = R.simpleReflectionMem (hA.diag_map K) i :=
  R.coxeterEquiv_simple hA i

@[simp]
theorem weylCoxeterSystem_wordProd (hA : A.IsGeneralizedCartan) (l : List I) :
    (R.weylCoxeterSystem hA).wordProd l = R.wordProd (hA.diag_map K) l := by
  rw [weylCoxeterSystem, CoxeterSystem.wordProd_map]
  exact R.coxeterHom_wordProd (hA.diag_map K) hA.zero_comm l

/-- The Coxeter length on `R.weylGroup (hA.diag_map K)` agrees with the generator-word length
`R.length`. -/
@[simp]
theorem weylCoxeterSystem_length (hA : A.IsGeneralizedCartan)
    (w : R.weylGroup (hA.diag_map K)) :
    (R.weylCoxeterSystem hA).length w = R.length (hA.diag_map K) w := by
  refine le_antisymm ?_ ?_
  · obtain ⟨l, hl, rfl⟩ := R.exists_wordProd_length_eq (hA.diag_map K) w
    rw [← hl, ← R.weylCoxeterSystem_wordProd hA l]
    exact (R.weylCoxeterSystem hA).length_wordProd_le l
  · obtain ⟨l, hl, rfl⟩ := (R.weylCoxeterSystem hA).exists_isReduced w
    rw [hl.eq, R.weylCoxeterSystem_wordProd hA l]
    exact R.length_wordProd_le (hA.diag_map K) l

/-- **Kac, Lemma 3.11 (descent form).** An index `i` is a right descent of `w` if and only if
`w • αᵢ` lies in `-Q₊`. -/
theorem isRightDescent_weylCoxeterSystem_iff (hA : A.IsGeneralizedCartan)
    (w : R.weylGroup (hA.diag_map K)) (i : I) :
    (R.weylCoxeterSystem hA).IsRightDescent w i ↔ -(w • R.root i) ∈ R.posRootCone := by
  let w₀ := (R.coxeterEquiv hA).symm w
  have hw : R.coxeterEquiv hA w₀ = w := (R.coxeterEquiv hA).apply_symm_apply w
  have hcox : R.coxeterHom (hA.diag_map K) hA.zero_comm w₀ = w := hw
  have hdesc : (R.weylCoxeterSystem hA).IsRightDescent w i ↔
      A.cartanCoxeterMatrix.toCoxeterSystem.IsRightDescent w₀ i := by
    rw [CoxeterSystem.IsRightDescent, CoxeterSystem.IsRightDescent, ← hw, weylCoxeterSystem,
      CoxeterSystem.map_simple, CoxeterMatrix.toCoxeterSystem_simple, ← map_mul,
      CoxeterSystem.length_map, CoxeterSystem.length_map]
  exact hdesc.trans ((R.isRightDescent_coxeterHom_iff hA w₀ i).trans (by rw [hcox]))

theorem not_isRightDescent_weylCoxeterSystem_iff (hA : A.IsGeneralizedCartan)
    (w : R.weylGroup (hA.diag_map K)) (i : I) :
    ¬ (R.weylCoxeterSystem hA).IsRightDescent w i ↔ w • R.root i ∈ R.posRootCone := by
  let w₀ := (R.coxeterEquiv hA).symm w
  have hcox : R.coxeterHom (hA.diag_map K) hA.zero_comm w₀ = w :=
    (R.coxeterEquiv hA).apply_symm_apply w
  rw [R.isRightDescent_weylCoxeterSystem_iff hA]
  refine ⟨fun hnot ↦ ?_, fun hpos hneg ↦
    R.root_linearIndependent.ne_zero i (by
      have h0 := R.isPointed_posRootCone _ hpos hneg
      rw [Subgroup.smul_def, LinearEquiv.smul_def, LinearEquiv.map_eq_zero_iff] at h0
      exact h0)⟩
  have hnd : ¬ A.cartanCoxeterMatrix.toCoxeterSystem.IsRightDescent w₀ i := by
    rw [R.isRightDescent_coxeterHom_iff hA, hcox]
    exact hnot
  have hpos := R.coxeterHom_smul_root_mem_posRootCone_of_not_isRightDescent hA _ _ rfl i hnd
  rwa [hcox] at hpos

/-- **Kac, Lemma 3.11 (length form).** `ℓ(w sᵢ) < ℓ(w)` if and only if `-(w • αᵢ) ∈ Q₊`. -/
theorem length_mul_simpleReflectionMem_lt_iff (hA : A.IsGeneralizedCartan)
    (w : R.weylGroup (hA.diag_map K)) (i : I) :
    R.length (hA.diag_map K) (w * R.simpleReflectionMem (hA.diag_map K) i) <
        R.length (hA.diag_map K) w ↔
      -(w • R.root i) ∈ R.posRootCone := by
  rw [← R.weylCoxeterSystem_length hA, ← R.weylCoxeterSystem_length hA,
    ← R.weylCoxeterSystem_simple hA]
  exact R.isRightDescent_weylCoxeterSystem_iff hA w i

/-- An element of the Weyl group fixing every simple root is the identity. -/
theorem eq_one_of_forall_smul_root_eq (hA : A.IsGeneralizedCartan)
    {w : R.weylGroup (hA.diag_map K)} (hw : ∀ i, w • R.root i = R.root i) : w = 1 := by
  have h0 : (R.coxeterEquiv hA).symm w = 1 :=
    R.eq_one_of_forall_coxeterHom_smul_root_eq hA fun i ↦ by
      have hcox : R.coxeterHom (hA.diag_map K) hA.zero_comm ((R.coxeterEquiv hA).symm w) = w :=
        (R.coxeterEquiv hA).apply_symm_apply w
      rw [hcox, hw i]
  exact (R.coxeterEquiv hA).symm.injective (h0.trans (map_one _).symm)

/-- **Faithfulness of the Weyl group on the root lattice `Q`.** -/
theorem rootLatticeAut_injective (hA : A.IsGeneralizedCartan) :
    Function.Injective (R.rootLatticeAut (hA.diag_map K)) := by
  refine (injective_iff_map_eq_one _).mpr fun w hw ↦
    R.eq_one_of_forall_smul_root_eq hA fun i ↦ ?_
  have hi := congrArg (fun f : R.rootLattice ≃ₗ[ℤ] R.rootLattice ↦
    (f ⟨R.root i, R.root_mem_rootLattice i⟩ : Dual K H)) hw
  simpa using hi

end GeneralizedCartan

/-! ### Low-rank and affine checks -/

section Checks

/-- With an empty index set, the Weyl group is trivial. -/
@[simp]
theorem weylGroup_eq_bot_of_isEmpty {I K H : Type*} [IsEmpty I] [Field K] [AddCommGroup H]
    [Module K H] {A : Matrix I I K} (R : CartanRealization A H) (hdiag : ∀ i, A i i = 2) :
    R.weylGroup hdiag = ⊥ := by
  simp [weylGroup_def, Set.range_eq_empty]

instance subsingleton_weylGroup_of_isEmpty {I K H : Type*} [IsEmpty I] [Field K] [AddCommGroup H]
    [Module K H] {A : Matrix I I K} (R : CartanRealization A H) (hdiag : ∀ i, A i i = 2) :
    Subsingleton (R.weylGroup hdiag) := by
  rw [R.weylGroup_eq_bot_of_isEmpty hdiag]
  infer_instance

/-- **Type `A₁`**: the Weyl group is isomorphic to `Multiplicative (ZMod 2)` via length parity and
has order `2`. -/
noncomputable def weylGroupAOneEquivZModTwo {K H : Type*} [Field K] [CharZero K] [AddCommGroup H]
    [Module K H] (R : CartanRealization ((CartanMatrix.A 1).map (Int.cast : ℤ → K)) H) :
    R.weylGroup ((CartanMatrix.isGeneralizedCartan_A 1).diag_map K) ≃* Multiplicative (ZMod 2) :=
  (R.weylCoxeterSystem (CartanMatrix.isGeneralizedCartan_A 1)).uniqueEquivZModTwo

@[simp]
theorem natCard_weylGroup_A_one {K H : Type*} [Field K] [CharZero K] [AddCommGroup H] [Module K H]
    (R : CartanRealization ((CartanMatrix.A 1).map (Int.cast : ℤ → K)) H) :
    Nat.card (R.weylGroup ((CartanMatrix.isGeneralizedCartan_A 1).diag_map K)) = 2 :=
  (R.weylCoxeterSystem (CartanMatrix.isGeneralizedCartan_A 1)).natCard_of_unique

theorem simpleReflection_eq_neg_of_corootSpan_eq_top_fin_one {K H : Type*} [Field K]
    [AddCommGroup H] [Module K H] {A : Matrix (Fin 1) (Fin 1) K} (R : CartanRealization A H)
    (hdiag : ∀ i, A i i = 2) (hmin : R.corootSpan = ⊤) (ω : Dual K H) :
    R.simpleReflection hdiag 0 ω = -ω := by
  ext h
  have hh : h ∈ R.corootSpan := hmin ▸ Submodule.mem_top
  rw [R.corootSpan_def] at hh
  induction hh using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    have hi : i = 0 := Subsingleton.elim i 0
    subst hi
    rw [simpleReflection_apply, LinearMap.sub_apply, LinearMap.smul_apply, R.root_coroot, hdiag 0,
      smul_eq_mul, LinearMap.neg_apply]
    ring
  | zero => simp
  | add x y _ _ ihx ihy => simp [ihx, ihy, add_comm]
  | smul c x _ ih => simp [ih]

/-- **Rank-two generalized Cartan matrices**: `R.weylGroup (hA.diag_map K)` is isomorphic to
`DihedralGroup (A.cartanCoxeterMatrix 0 1)` — finite dihedral when `A 0 1 * A 1 0 ≤ 3`, and the
infinite dihedral group `DihedralGroup 0` when `3 < A 0 1 * A 1 0`. -/
noncomputable def weylGroupFinTwoEquivDihedralGroup {K H : Type*} [Field K] [CharZero K]
    [AddCommGroup H] [Module K H] {A : Matrix (Fin 2) (Fin 2) ℤ} (hA : A.IsGeneralizedCartan)
    (R : CartanRealization (A.map (Int.cast : ℤ → K)) H) :
    R.weylGroup (hA.diag_map K) ≃* DihedralGroup (A.cartanCoxeterMatrix 0 1) :=
  (R.weylCoxeterSystem hA).finTwoEquivDihedralGroup

@[simp]
theorem natCard_weylGroup_fin_two {K H : Type*} [Field K] [CharZero K] [AddCommGroup H]
    [Module K H] {A : Matrix (Fin 2) (Fin 2) ℤ} (hA : A.IsGeneralizedCartan)
    (R : CartanRealization (A.map (Int.cast : ℤ → K)) H) :
    Nat.card (R.weylGroup (hA.diag_map K)) = 2 * A.cartanCoxeterMatrix 0 1 :=
  (R.weylCoxeterSystem hA).natCard_of_fin_two

/-- **Type `B₂`**: `(CartanMatrix.B 2).cartanCoxeterMatrix 0 1 = 4` and the Weyl group has order
`8`. -/
@[simp]
theorem cartanCoxeterMatrix_B_two_zero_one :
    (CartanMatrix.B 2).cartanCoxeterMatrix 0 1 = 4 := by
  have hprod : CartanMatrix.B 2 0 1 * CartanMatrix.B 2 1 0 = 2 := by decide
  rw [Matrix.cartanCoxeterMatrix_of_ne_of_le _ (by decide) (by omega), hprod,
    TauCeti.coxeterOrder_two]

@[simp]
theorem natCard_weylGroup_B_two {K H : Type*} [Field K] [CharZero K] [AddCommGroup H] [Module K H]
    (R : CartanRealization ((CartanMatrix.B 2).map (Int.cast : ℤ → K)) H) :
    Nat.card (R.weylGroup ((CartanMatrix.isGeneralizedCartan_B 2).diag_map K)) = 8 := by
  rw [R.natCard_weylGroup_fin_two (CartanMatrix.isGeneralizedCartan_B 2),
    cartanCoxeterMatrix_B_two_zero_one]

/-- **Type `G₂`**: the Weyl group has order `12`. -/
@[simp]
theorem natCard_weylGroup_G₂ {K H : Type*} [Field K] [CharZero K] [AddCommGroup H] [Module K H]
    (R : CartanRealization (CartanMatrix.G₂.map (Int.cast : ℤ → K)) H) :
    Nat.card (R.weylGroup (CartanMatrix.isGeneralizedCartan_G₂.diag_map K)) = 12 := by
  have hm : CartanMatrix.G₂.cartanCoxeterMatrix 0 1 = 6 := by
    rw [CartanMatrix.cartanCoxeterMatrix_G₂]
    rfl
  rw [R.natCard_weylGroup_fin_two CartanMatrix.isGeneralizedCartan_G₂, hm]

/-- The affine `A₁⁽¹⁾` Cartan matrix `!![2, -2; -2, 2]` is a generalized Cartan matrix. -/
theorem isGeneralizedCartan_two_neg_two :
    (!![2, -2; -2, 2] : Matrix (Fin 2) (Fin 2) ℤ).IsGeneralizedCartan where
  diag i := by fin_cases i <;> decide
  offDiag_nonpos i j hij := by fin_cases i <;> fin_cases j <;> simp_all
  zero_comm i j := by fin_cases i <;> fin_cases j <;> decide

@[simp]
theorem cartanCoxeterMatrix_two_neg_two_zero_one :
    (!![2, -2; -2, 2] : Matrix (Fin 2) (Fin 2) ℤ).cartanCoxeterMatrix 0 1 = 0 :=
  Matrix.cartanCoxeterMatrix_of_ne_of_lt _ (by decide) (by decide)

/-- **Affine `A₁⁽¹⁾`**: its Weyl group is isomorphic to the infinite dihedral group
`DihedralGroup 0`. -/
noncomputable def weylGroupTwoNegTwoEquivDihedralGroup {K H : Type*} [Field K] [CharZero K]
    [AddCommGroup H] [Module K H]
    (R : CartanRealization ((!![2, -2; -2, 2] : Matrix (Fin 2) (Fin 2) ℤ).map
      (Int.cast : ℤ → K)) H) :
    R.weylGroup (isGeneralizedCartan_two_neg_two.diag_map K) ≃* DihedralGroup 0 := by
  have h := R.weylGroupFinTwoEquivDihedralGroup isGeneralizedCartan_two_neg_two
  rwa [cartanCoxeterMatrix_two_neg_two_zero_one] at h

/-- **Affine `A₁⁽¹⁾`**: `s₀ s₁` has infinite order (`orderOf = 0`). -/
theorem orderOf_simpleReflectionMem_mul_two_neg_two {K H : Type*} [Field K] [CharZero K]
    [AddCommGroup H] [Module K H]
    (R : CartanRealization ((!![2, -2; -2, 2] : Matrix (Fin 2) (Fin 2) ℤ).map
      (Int.cast : ℤ → K)) H) :
    orderOf (R.simpleReflectionMem (isGeneralizedCartan_two_neg_two.diag_map K) 0 *
      R.simpleReflectionMem (isGeneralizedCartan_two_neg_two.diag_map K) 1) = 0 := by
  simp

/-- **Affine `A₁⁽¹⁾`**: `(s₀ s₁)(α₁) = -α₁ - 2 α₀ = α₁ - 2(α₀ + α₁)`. -/
theorem simpleReflection_mul_root_two_neg_two {K H : Type*} [Field K] [AddCommGroup H] [Module K H]
    (R : CartanRealization ((!![2, -2; -2, 2] : Matrix (Fin 2) (Fin 2) ℤ).map
      (Int.cast : ℤ → K)) H)
    (hdiag : ∀ i, (!![2, -2; -2, 2] : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → K) i i = 2) :
    (R.simpleReflection hdiag 0 * R.simpleReflection hdiag 1) (R.root 1) =
      -R.root 1 - (2 : ℤ) • R.root 0 := by
  rw [mul_apply_eq_comp, simpleReflection_root_self, map_neg, simpleReflection_root_int]
  have h01 : (!![2, -2; -2, 2] : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = -2 := rfl
  rw [h01, neg_zsmul, sub_neg_eq_add, neg_add, sub_eq_add_neg]

end Checks

end TauCeti.CartanRealization

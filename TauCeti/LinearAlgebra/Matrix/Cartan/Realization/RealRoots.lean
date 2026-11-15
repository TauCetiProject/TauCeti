/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Cartan.Realization.WeylGroup

/-!
# Real roots, real coroots, and real reflections of a Cartan realization

For a realization `R` of a generalized Cartan matrix `A` over a field `K` of characteristic zero,
the **real roots** `Φ^re` (`realRoots`) are the Weyl-group transforms `w • αᵢ` of the simple roots,
and the **positive real roots** `Φ₊^re` (`posRealRoots`) are `Φ^re ∩ Q₊`. Following Kac (§3.10,
§5.1), we prove sign dichotomy on `Φ^re`, reducedness (`eq_one_or_neg_one_of_smul_mem_realRoots`,
Kac Proposition 5.1(b)), stability of `Φ₊^re \ {αᵢ}` under `sᵢ`
(`bijOn_simpleReflection_posRealRoots_diff`, Kac Lemma 3.10), well-definedness and `W`-equivariance
of real coroots (`realCoroot`, `realCoroot_smul`), and that reflections in real roots
(`realReflection`, `weylRealReflection`) belong to `W` as Coxeter reflections
(`isReflection_weylRealReflection`).

## References

* V. G. Kac, *Infinite-dimensional Lie algebras*, third edition, Cambridge University Press, 1990,
  §3.10 and §5.1 (Proposition 5.1).
* S. Kumar, *Kac-Moody Groups, their Flag Varieties and Representation Theory*, Progress in
  Mathematics 204, Birkhäuser, 2002, §1.3.
-/

public section

open Module

namespace TauCeti.CartanRealization

/-! ### Real roots and positive real roots over an arbitrary field -/

section Field

variable {I K H : Type*} [Field K] [AddCommGroup H] [Module K H] {A : Matrix I I ℤ}
  (R : CartanRealization (A.map (Int.cast : ℤ → K)) H) (hA : A.IsGeneralizedCartan)

/-- The **real roots** `Φ^re` of a realization: the Weyl-group orbit of the simple roots in
`Dual K H`. -/
def realRoots : Set (Dual K H) :=
  {α | ∃ (w : R.weylGroup hA.cast_diag) (i : I), w • R.root i = α}

theorem realRoots_def :
    R.realRoots hA = {α | ∃ (w : R.weylGroup hA.cast_diag) (i : I), w • R.root i = α} := (rfl)

theorem mem_realRoots_iff {α : Dual K H} :
    α ∈ R.realRoots hA ↔ ∃ (w : R.weylGroup hA.cast_diag) (i : I), w • R.root i = α := (Iff.rfl)

/-- The **positive real roots** `Φ₊^re = Φ^re ∩ Q₊`. -/
def posRealRoots : Set (Dual K H) := R.realRoots hA ∩ R.posRootCone

theorem posRealRoots_def : R.posRealRoots hA = R.realRoots hA ∩ R.posRootCone := (rfl)

theorem mem_posRealRoots_iff {α : Dual K H} :
    α ∈ R.posRealRoots hA ↔ α ∈ R.realRoots hA ∧ α ∈ R.posRootCone := (Iff.rfl)

theorem root_mem_realRoots (i : I) : R.root i ∈ R.realRoots hA := ⟨1, i, one_smul _ _⟩

theorem root_mem_posRealRoots (i : I) : R.root i ∈ R.posRealRoots hA :=
  ⟨R.root_mem_realRoots hA i, R.root_mem_posRootCone i⟩

theorem realRoots_subset_rootLattice : R.realRoots hA ⊆ R.rootLattice := by
  rintro _ ⟨w, i, rfl⟩
  exact R.weylGroup_smul_mem_rootLattice hA.cast_diag w (R.root_mem_rootLattice i)

theorem ne_zero_of_mem_realRoots {α : Dual K H} (hα : α ∈ R.realRoots hA) : α ≠ 0 := by
  obtain ⟨w, i, rfl⟩ := hα
  exact fun h0 ↦ R.root_linearIndependent.ne_zero i (by simpa using congrArg (w⁻¹ • ·) h0)

@[simp] theorem smul_mem_realRoots_iff (w : R.weylGroup hA.cast_diag) {α : Dual K H} :
    w • α ∈ R.realRoots hA ↔ α ∈ R.realRoots hA :=
  ⟨fun ⟨u, i, hu⟩ ↦ ⟨w⁻¹ * u, i, by rw [mul_smul, hu, inv_smul_smul]⟩,
   fun ⟨u, i, hu⟩ ↦ ⟨w * u, i, by rw [mul_smul, hu]⟩⟩

@[simp] theorem neg_mem_realRoots_iff {α : Dual K H} :
    -α ∈ R.realRoots hA ↔ α ∈ R.realRoots hA := by
  suffices ∀ β ∈ R.realRoots hA, -β ∈ R.realRoots hA from ⟨fun h ↦ neg_neg α ▸ this _ h, this α⟩
  rintro _ ⟨w, i, rfl⟩
  exact ⟨w * R.weylSimple hA.cast_diag i, i, by simp [mul_smul]⟩

end Field

/-! ### Sign dichotomy, reducedness, real coroots, and real reflections in characteristic zero -/

section CharZero

variable {I K H : Type*} [Field K] [CharZero K] [AddCommGroup H] [Module K H]
  {A : Matrix I I ℤ} (R : CartanRealization (A.map (Int.cast : ℤ → K)) H)
  (hA : A.IsGeneralizedCartan)

/-- **Sign dichotomy for real roots**: every real root lies either in `Q₊` or in `-Q₊`. -/
theorem mem_posRootCone_or_neg_mem_posRootCone_of_mem_realRoots {α : Dual K H}
    (hα : α ∈ R.realRoots hA) : α ∈ R.posRootCone ∨ -α ∈ R.posRootCone := by
  obtain ⟨w, i, rfl⟩ := hα
  rcases lt_trichotomy (R.length hA.cast_diag w)
      (R.length hA.cast_diag (w * R.weylSimple hA.cast_diag i)) with hlt | heq | hgt
  · exact Or.inl ((R.smul_root_mem_posRootCone_iff hA w i).mpr hlt)
  · exact absurd heq.symm (by simpa using (R.weylCoxeterSystem hA).length_mul_simple_ne w i)
  · exact Or.inr ((R.length_mul_weylSimple_lt_iff hA w i).mp hgt)

theorem mem_posRealRoots_or_neg_mem_posRealRoots_of_mem_realRoots {α : Dual K H}
    (hα : α ∈ R.realRoots hA) : α ∈ R.posRealRoots hA ∨ -α ∈ R.posRealRoots hA :=
  (R.mem_posRootCone_or_neg_mem_posRootCone_of_mem_realRoots hA hα).imp
    (⟨hα, ·⟩) (⟨(R.neg_mem_realRoots_iff hA).mpr hα, ·⟩)

/-- **Kac, Proposition 5.1(b) (reducedness of real roots)**: the only scalar multiples of a real
root `α` that are real roots are `α` and `-α`. -/
theorem eq_one_or_neg_one_of_smul_mem_realRoots {α : Dual K H} (hα : α ∈ R.realRoots hA)
    {c : K} (hc : c • α ∈ R.realRoots hA) : c = 1 ∨ c = -1 := by
  have hc0 : c ≠ 0 := fun h0 ↦ R.ne_zero_of_mem_realRoots hA (by simpa [h0] using hc) rfl
  obtain ⟨w₁, i₁, rfl⟩ := hα
  obtain ⟨w₂, i₂, hw₂⟩ := hc
  have mem_int {u₁ u₂ : R.weylGroup hA.cast_diag} {j₁ j₂ : I} {d : K}
      (hd : d • (u₁ • R.root j₁) = u₂ • R.root j₂) : ∃ n : ℤ, (n : K) = d := by
    refine Submodule.mem_one.mp ((R.smul_root_mem_rootLattice_iff d j₁).mp ?_)
    have heq : d • R.root j₁ = (u₁⁻¹ * u₂) • R.root j₂ := by
      rw [mul_smul, ← hd, smul_comm, inv_smul_smul]
    exact heq ▸ R.realRoots_subset_rootLattice hA ⟨u₁⁻¹ * u₂, j₂, rfl⟩
  obtain ⟨n, hn⟩ := mem_int hw₂.symm
  obtain ⟨m, hm⟩ := mem_int (u₁ := w₂) (u₂ := w₁) (d := c⁻¹) (by rw [hw₂, inv_smul_smul₀ hc0])
  have hnm : n * m = 1 :=
    Int.cast_injective (α := K) (by push_cast; rw [hn, hm, mul_inv_cancel₀ hc0])
  exact (Int.eq_one_or_neg_one_of_mul_eq_one hnm).imp (by simp [← hn, ·]) (by simp [← hn, ·])

theorem eq_one_of_nsmul_mem_realRoots {α : Dual K H} (hα : α ∈ R.realRoots hA) {n : ℕ}
    (hn : (n • α : Dual K H) ∈ R.realRoots hA) : n = 1 := by
  rw [← Nat.cast_smul_eq_nsmul K] at hn
  rcases R.eq_one_or_neg_one_of_smul_mem_realRoots hA hα hn with h1 | hm1
  · exact_mod_cast h1
  · exfalso
    have : (n : ℤ) = -1 := Int.cast_injective (α := K) (by simpa using hm1)
    omega

/-- **Kac, Lemma 3.10 (real roots)**: `sᵢ` maps `Φ₊^re \ {αᵢ}` into `Φ₊^re \ {αᵢ}`. -/
theorem simpleReflection_mem_posRealRoots_of_ne (i : I) {α : Dual K H}
    (hα : α ∈ R.posRealRoots hA) (hne : α ≠ R.root i) :
    R.simpleReflection hA.cast_diag i α ∈ R.posRealRoots hA ∧
      R.simpleReflection hA.cast_diag i α ≠ R.root i := by
  have hs_real : R.simpleReflection hA.cast_diag i α ∈ R.realRoots hA := by
    simpa [← weylSimple_smul] using hα.1
  have hs_ne : R.simpleReflection hA.cast_diag i α ≠ R.root i := fun heq ↦ by
    have : α = -R.root i := by simpa using congrArg (R.simpleReflection hA.cast_diag i) heq
    exact R.root_linearIndependent.ne_zero i
      (R.isPointed_posRootCone _ (R.root_mem_posRootCone i) (this ▸ hα.2))
  refine ⟨⟨hs_real, ?_⟩, hs_ne⟩
  refine (R.mem_posRootCone_or_neg_mem_posRootCone_of_mem_realRoots hA hs_real).resolve_right
    fun hneg ↦ ?_
  obtain ⟨f, hf⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp (R.posRootCone_def ▸ hα.2)
  obtain ⟨g, hg⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp (R.posRootCone_def ▸ hneg)
  have hex : ∃ j ≠ i, f j ≠ 0 := by
    by_contra! hall
    have hsupp : f = Finsupp.single i (f i) :=
      Finsupp.ext fun j ↦ by obtain rfl | hji := eq_or_ne j i <;> simp [*]
    rw [hsupp, Finsupp.sum_single_index (zero_smul ℕ (R.root i))] at hf
    have hfi := R.eq_one_of_nsmul_mem_realRoots hA (R.root_mem_realRoots hA i) (hf.symm ▸ hα.1)
    exact hne (by rw [← hf, hfi, one_smul])
  obtain ⟨j₀, hj₀, hfj₀⟩ := hex
  have hlin : Finsupp.linearCombination K R.root
      (f.mapRange (Nat.cast : ℕ → K) Nat.cast_zero +
        g.mapRange (Nat.cast : ℕ → K) Nat.cast_zero -
        Finsupp.single i (α (R.coroot i))) = 0 := by
    rw [map_sub, map_add, Finsupp.linearCombination_single,
      Finsupp.linearCombination_apply, Finsupp.linearCombination_apply,
      Finsupp.sum_mapRange_index (fun j ↦ zero_smul K (R.root j)),
      Finsupp.sum_mapRange_index (fun j ↦ zero_smul K (R.root j))]
    simp only [Nat.cast_smul_eq_nsmul, hf, hg, simpleReflection_apply]
    abel
  have hcoeff := Finsupp.ext_iff.mp
    (linearIndependent_iff.mp R.root_linearIndependent _ hlin) j₀
  have hfg : f j₀ + g j₀ = 0 := Nat.cast_injective (R := K)
    (by simpa [Finsupp.single_apply, Ne.symm hj₀] using hcoeff)
  omega

/-- `sᵢ` restricts to a bijection on `Φ₊^re \ {αᵢ}`. -/
theorem bijOn_simpleReflection_posRealRoots_diff (i : I) :
    Set.BijOn (R.simpleReflection hA.cast_diag i)
      (R.posRealRoots hA \ {R.root i}) (R.posRealRoots hA \ {R.root i}) :=
  have hmaps : Set.MapsTo (R.simpleReflection hA.cast_diag i)
      (R.posRealRoots hA \ {R.root i}) (R.posRealRoots hA \ {R.root i}) :=
    fun _ ⟨hα, hne⟩ ↦ R.simpleReflection_mem_posRealRoots_of_ne hA i hα hne
  ⟨hmaps, (R.simpleReflection hA.cast_diag i).injective.injOn,
    fun α hα ↦ ⟨_, hmaps hα, R.involutive_simpleReflection hA.cast_diag i α⟩⟩

/-! ### Well-definedness of real coroots `(wα)^∨ = w(α^∨)` and real reflections -/

/-- If `u • αᵢ = αⱼ` in the Weyl group, then `u * sᵢ * u⁻¹ = sⱼ` in `R.weylGroup hA.cast_diag`. -/
theorem conj_weylSimple_eq_of_smul_root_eq {u : R.weylGroup hA.cast_diag} {i j : I}
    (hu : u • R.root i = R.root j) :
    u * R.weylSimple hA.cast_diag i * u⁻¹ = R.weylSimple hA.cast_diag j := by
  let cs := R.weylCoxeterSystem hA
  have hu_inv : u⁻¹ • R.root j = R.root i := by rw [← hu, inv_smul_smul]
  have hlen_ui : cs.length (u * cs.simple i) = cs.length u + 1 :=
    cs.not_isRightDescent_iff.mp <| (R.not_isRightDescent_weylCoxeterSystem_iff hA u i).mpr
      (hu ▸ R.root_mem_posRootCone j)
  have hlen_ju : cs.length (cs.simple j * u) = cs.length u + 1 :=
    cs.not_isLeftDescent_iff.mp <| by
      rw [← cs.isRightDescent_inv_iff, R.not_isRightDescent_weylCoxeterSystem_iff hA, hu_inv]
      exact R.root_mem_posRootCone i
  have hd_usi : cs.IsLeftDescent (u * cs.simple i) j := by
    rw [← cs.isRightDescent_inv_iff, mul_inv_rev, cs.inv_simple,
      R.isRightDescent_weylCoxeterSystem_iff hA, weylCoxeterSystem_simple, mul_smul, hu_inv,
      weylSimple_smul, simpleReflection_root_self, neg_neg]
    exact R.root_mem_posRootCone i
  have hlen_jui := cs.isLeftDescent_iff.mp hd_usi
  have hcomm : cs.simple j * u = u * cs.simple i :=
    cs.simple_mul_eq_mul_simple_of_length_eq (by rw [mul_assoc]; omega) (by omega)
  calc u * R.weylSimple hA.cast_diag i * u⁻¹
      = cs.simple j * u * u⁻¹ := by rw [← weylCoxeterSystem_simple R hA, hcomm]
    _ = R.weylSimple hA.cast_diag j := by simp [cs, mul_assoc]

omit [CharZero K] in
private theorem conj_weylSimple_smul (w : R.weylGroup hA.cast_diag) (i : I) (φ : Dual K H) :
    (w * R.weylSimple hA.cast_diag i * w⁻¹) • φ =
      φ - φ (R.corootEquiv hA.cast_diag w • R.coroot i) • (w • R.root i) := by
  rw [mul_smul, mul_smul, weylSimple_smul, simpleReflection_apply, smul_sub, smul_inv_smul,
    smul_comm w, R.weylGroup_smul_apply hA.cast_diag w⁻¹ φ (R.coroot i), map_inv, inv_inv]

/-- Transport of simple coroots along `W` depends only on the transported real root:
if `w₁ • α_{i₁} = w₂ • α_{i₂}`, then `w₁ • h_{i₁} = w₂ • h_{i₂}`. -/
theorem corootEquiv_smul_coroot_eq_of_smul_root_eq
    {w₁ w₂ : R.weylGroup hA.cast_diag} {i₁ i₂ : I}
    (h : w₁ • R.root i₁ = w₂ • R.root i₂) :
    R.corootEquiv hA.cast_diag w₁ • R.coroot i₁ =
      R.corootEquiv hA.cast_diag w₂ • R.coroot i₂ := by
  suffices key : ∀ u : R.weylGroup hA.cast_diag, u • R.root i₁ = R.root i₂ →
      R.corootEquiv hA.cast_diag u • R.coroot i₁ = R.coroot i₂ by
    have hcor := key (w₂⁻¹ * w₁) (by rw [mul_smul, h, inv_smul_smul])
    rwa [map_mul, map_inv, mul_smul, inv_smul_eq_iff] at hcor
  intro u hu
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff K]
  intro φ
  have hφ := congrArg (· • φ) (R.conj_weylSimple_eq_of_smul_root_eq hA hu)
  rw [R.conj_weylSimple_smul hA u i₁ φ, hu, weylSimple_smul, simpleReflection_apply,
    sub_right_inj] at hφ
  rw [map_sub, sub_eq_zero]
  exact smul_left_injective K (R.root_linearIndependent.ne_zero i₂) hφ

/-- The **real coroot** `α^∨ ∈ H` attached to a real root `α ∈ R.realRoots hA`. -/
noncomputable def realCoroot (α : R.realRoots hA) : H :=
  R.corootEquiv hA.cast_diag α.2.choose • R.coroot α.2.choose_spec.choose

theorem realCoroot_eq {α : R.realRoots hA} (w : R.weylGroup hA.cast_diag) (i : I)
    (hw : w • R.root i = α) :
    R.realCoroot hA α = R.corootEquiv hA.cast_diag w • R.coroot i :=
  R.corootEquiv_smul_coroot_eq_of_smul_root_eq hA (α.2.choose_spec.choose_spec.trans hw.symm)

@[simp] theorem realCoroot_root (i : I) :
    R.realCoroot hA ⟨R.root i, R.root_mem_realRoots hA i⟩ = R.coroot i := by
  simpa using R.realCoroot_eq hA (α := ⟨R.root i, R.root_mem_realRoots hA i⟩) 1 i (one_smul _ _)

/-- **Equivariance of real coroots**: `(w • α)^∨ = w • α^∨` for every `w ∈ W` and `α ∈ Φ^re`. -/
@[simp] theorem realCoroot_smul (w : R.weylGroup hA.cast_diag) (α : R.realRoots hA) :
    R.realCoroot hA ⟨w • α.1, (R.smul_mem_realRoots_iff hA w).mpr α.2⟩ =
      R.corootEquiv hA.cast_diag w • R.realCoroot hA α := by
  obtain ⟨u, i, hu⟩ := α.2
  rw [R.realCoroot_eq hA u i hu, R.realCoroot_eq hA (w * u) i (by rw [mul_smul, hu]),
    map_mul, mul_smul]

@[simp] theorem realCoroot_neg (α : R.realRoots hA) :
    R.realCoroot hA ⟨-α.1, (R.neg_mem_realRoots_iff hA).mpr α.2⟩ = -R.realCoroot hA α := by
  obtain ⟨w, i, hw⟩ := α.2
  rw [R.realCoroot_eq hA w i hw, R.realCoroot_eq hA (w * R.weylSimple hA.cast_diag i) i
    (by simp [mul_smul, hw]), map_mul, mul_smul, corootEquiv_weylSimple, corootWeylSimple_smul,
    simpleCoreflection_coroot_self, smul_neg]

@[simp] theorem apply_realCoroot_self (α : R.realRoots hA) :
    (α : Dual K H) (R.realCoroot hA α) = 2 := by
  obtain ⟨w, i, hw⟩ := α.2
  rw [R.realCoroot_eq hA w i hw, ← hw, weylGroup_smul_apply_corootEquiv_smul, R.root_coroot,
    hA.cast_diag i]

/-- The **reflection** `s_α : Dual K H ≃ₗ[K] Dual K H` in a real root `α ∈ Φ^re` (defined on
`R.realRoots hA` only): `λ ↦ λ - λ(α^∨) • α`. -/
noncomputable def realReflection (α : R.realRoots hA) : Dual K H ≃ₗ[K] Dual K H :=
  Module.reflection (x := (α : Dual K H)) (f := Dual.eval K H (R.realCoroot hA α))
    (R.apply_realCoroot_self hA α)

theorem realReflection_apply (α : R.realRoots hA) (φ : Dual K H) :
    R.realReflection hA α φ = φ - φ (R.realCoroot hA α) • (α : Dual K H) :=
  Module.reflection_apply φ _

@[simp] theorem realReflection_apply_self (α : R.realRoots hA) :
    R.realReflection hA α (α : Dual K H) = -(α : Dual K H) := Module.reflection_apply_self _

theorem involutive_realReflection (α : R.realRoots hA) :
    Function.Involutive (R.realReflection hA α) := Module.involutive_reflection _

@[simp] theorem realReflection_realReflection (α : R.realRoots hA) (φ : Dual K H) :
    R.realReflection hA α (R.realReflection hA α φ) = φ := R.involutive_realReflection hA α φ

@[simp] theorem realReflection_symm (α : R.realRoots hA) :
    (R.realReflection hA α).symm = R.realReflection hA α := Module.reflection_symm _

@[simp] theorem realReflection_inv (α : R.realRoots hA) :
    (R.realReflection hA α)⁻¹ = R.realReflection hA α := Module.reflection_inv _

@[simp] theorem realReflection_mul_self (α : R.realRoots hA) :
    R.realReflection hA α * R.realReflection hA α = 1 :=
  LinearEquiv.ext (R.realReflection_realReflection hA α)

@[simp] theorem realReflection_root (i : I) :
    R.realReflection hA ⟨R.root i, R.root_mem_realRoots hA i⟩ =
      R.simpleReflection hA.cast_diag i := by
  ext φ h
  simp [realReflection_apply, simpleReflection_apply]

@[simp] theorem realReflection_neg (α : R.realRoots hA) :
    R.realReflection hA ⟨-α.1, (R.neg_mem_realRoots_iff hA).mpr α.2⟩ = R.realReflection hA α := by
  ext φ h
  simp [realReflection_apply]

theorem realReflection_eq_conj {α : R.realRoots hA} (w : R.weylGroup hA.cast_diag) (i : I)
    (hw : w • R.root i = α) :
    R.realReflection hA α =
      (w : Dual K H ≃ₗ[K] Dual K H) * R.simpleReflection hA.cast_diag i *
        (w : Dual K H ≃ₗ[K] Dual K H)⁻¹ := by
  apply LinearEquiv.ext fun φ ↦ ?_
  have hcalc := R.conj_weylSimple_smul hA w i φ
  rw [realReflection_apply, R.realCoroot_eq hA w i hw, ← hw, ← hcalc, Subgroup.smul_def,
    Subgroup.coe_mul, Subgroup.coe_mul, coe_weylSimple, Subgroup.coe_inv, LinearEquiv.smul_def]

theorem realReflection_mem_weylGroup (α : R.realRoots hA) :
    R.realReflection hA α ∈ R.weylGroup hA.cast_diag := by
  obtain ⟨w, i, hw⟩ := α.2
  rw [R.realReflection_eq_conj hA w i hw]
  exact mul_mem (mul_mem w.2 (R.simpleReflection_mem_weylGroup hA.cast_diag i)) (inv_mem w.2)

/-- The reflection `s_α` in a real root `α ∈ Φ^re`, as an element of `R.weylGroup hA.cast_diag`. -/
noncomputable def weylRealReflection (α : R.realRoots hA) : R.weylGroup hA.cast_diag :=
  ⟨R.realReflection hA α, R.realReflection_mem_weylGroup hA α⟩

@[simp] theorem coe_weylRealReflection (α : R.realRoots hA) :
    (R.weylRealReflection hA α : Dual K H ≃ₗ[K] Dual K H) = R.realReflection hA α := (rfl)

@[simp] theorem weylRealReflection_smul (α : R.realRoots hA) (φ : Dual K H) :
    R.weylRealReflection hA α • φ = R.realReflection hA α φ := (rfl)

@[simp] theorem weylRealReflection_mul_self (α : R.realRoots hA) :
    R.weylRealReflection hA α * R.weylRealReflection hA α = 1 :=
  Subtype.ext (R.realReflection_mul_self hA α)

@[simp] theorem inv_weylRealReflection (α : R.realRoots hA) :
    (R.weylRealReflection hA α)⁻¹ = R.weylRealReflection hA α :=
  Subtype.ext (R.realReflection_inv hA α)

@[simp] theorem weylRealReflection_root (i : I) :
    R.weylRealReflection hA ⟨R.root i, R.root_mem_realRoots hA i⟩ =
      R.weylSimple hA.cast_diag i :=
  Subtype.ext (by simp [R.realReflection_root hA i])

@[simp] theorem weylRealReflection_neg (α : R.realRoots hA) :
    R.weylRealReflection hA ⟨-α.1, (R.neg_mem_realRoots_iff hA).mpr α.2⟩ =
      R.weylRealReflection hA α :=
  Subtype.ext (R.realReflection_neg hA α)

theorem weylRealReflection_eq_conj {α : R.realRoots hA} (w : R.weylGroup hA.cast_diag) (i : I)
    (hw : w • R.root i = α) :
    R.weylRealReflection hA α = w * R.weylSimple hA.cast_diag i * w⁻¹ :=
  Subtype.ext (by simp [R.realReflection_eq_conj hA w i hw])

/-- Every real reflection is a Coxeter reflection in `R.weylCoxeterSystem hA`. -/
theorem isReflection_weylRealReflection (α : R.realRoots hA) :
    (R.weylCoxeterSystem hA).IsReflection (R.weylRealReflection hA α) := by
  obtain ⟨w, i, hw⟩ := α.2
  exact ⟨w, i, by rw [weylCoxeterSystem_simple, R.weylRealReflection_eq_conj hA w i hw]⟩

end CharZero

end TauCeti.CartanRealization

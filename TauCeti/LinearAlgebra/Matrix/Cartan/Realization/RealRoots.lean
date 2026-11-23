/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Cartan.Realization.Weyl.Coxeter
import TauCeti.GroupTheory.Coxeter.StrongExchange

/-!
# Real roots, real coroots, and real reflections of a Cartan realization

For a `TauCeti.CartanRealization` `R` of a generalized Cartan matrix `A` over a characteristic-zero
field `K`, the **real roots** `Δ^re` (`realRoots`) are the Weyl-group translates `w(αᵢ)` of the
simple roots, and `Δ₊^re = Δ^re ∩ Q₊` (`posRealRoots`) are the positive real roots (Kac,
*Infinite-dimensional Lie algebras*, §5.1).

We prove:
* indivisibility of real roots in `Q` (`eq_one_or_neg_one_of_zsmul_mem_realRoots`, Kac
  Proposition 5.1(b));
* sign dichotomy (`mem_posRootCone_or_neg_mem_posRootCone_of_mem_realRoots`);
* stability of `Δ₊^re \ {αᵢ}` under `sᵢ` (`simpleReflection_mem_posRealRoots`);
* word-independent **real coroots** `α^∨ = w(hᵢ) ∈ H` (`realCoroot`) and **real reflections**
  `s_α = w sᵢ w⁻¹ ∈ R.weylGroup _` (`realReflection`), together with their equivariance, negation
  laws (`(-α)^∨ = -α^∨`, `s_{-α} = s_α`), evaluation `α(α^∨) = 2`, dual reflection formulas on
  `Dual K H` and `H`, and membership in `R.corootSpan` and admissible coweight lattices.

## References

* V. G. Kac, *Infinite-dimensional Lie algebras*, third edition, Cambridge University Press, 1990,
  §3.8, §5.1, and Proposition 5.1(b).
-/

public section

open Module

namespace TauCeti.CartanRealization

section Integral
variable {I K H : Type*} [Field K] [AddCommGroup H] [Module K H] {A : Matrix I I ℤ}
  (R : CartanRealization (A.map (Int.cast : ℤ → K)) H)
  (hdiag : ∀ i, (A.map (Int.cast : ℤ → K)) i i = 2)

/-- The **real roots** `Δ^re` of a Cartan realization: the Weyl-group orbit of the simple roots. -/
def realRoots : Set (Dual K H) :=
  {α | ∃ (w : R.weylGroup hdiag) (i : I), (w : Dual K H ≃ₗ[K] Dual K H) (R.root i) = α}

/-- The **positive real roots** `Δ₊^re = Δ^re ∩ Q₊`. -/
def posRealRoots : Set (Dual K H) := R.realRoots hdiag ∩ R.posRootCone

/-- Membership characterization for `R.realRoots hdiag`. -/
theorem mem_realRoots_iff {α : Dual K H} :
    α ∈ R.realRoots hdiag ↔
      ∃ (w : R.weylGroup hdiag) (i : I), (w : Dual K H ≃ₗ[K] Dual K H) (R.root i) = α :=
  Iff.rfl

/-- Membership characterization for `R.posRealRoots hdiag`. -/
theorem mem_posRealRoots_iff {α : Dual K H} :
    α ∈ R.posRealRoots hdiag ↔ α ∈ R.realRoots hdiag ∧ α ∈ R.posRootCone :=
  Iff.rfl

/-- Every simple root is a real root. -/
theorem root_mem_realRoots (i : I) : R.root i ∈ R.realRoots hdiag :=
  (R.mem_realRoots_iff hdiag).mpr ⟨1, i, rfl⟩

/-- Every Weyl-group translate of a simple root is a real root. -/
theorem apply_root_mem_realRoots (w : R.weylGroup hdiag) (i : I) :
    (w : Dual K H ≃ₗ[K] Dual K H) (R.root i) ∈ R.realRoots hdiag :=
  (R.mem_realRoots_iff hdiag).mpr ⟨w, i, rfl⟩

/-- The set of real roots is stable under the Weyl group. -/
theorem apply_mem_realRoots (w : R.weylGroup hdiag) {α : Dual K H}
    (hα : α ∈ R.realRoots hdiag) : (w : Dual K H ≃ₗ[K] Dual K H) α ∈ R.realRoots hdiag := by
  obtain ⟨u, i, rfl⟩ := (R.mem_realRoots_iff hdiag).mp hα
  exact (R.mem_realRoots_iff hdiag).mpr ⟨w * u, i, rfl⟩

@[simp]
theorem apply_mem_realRoots_iff (w : R.weylGroup hdiag) {α : Dual K H} :
    (w : Dual K H ≃ₗ[K] Dual K H) α ∈ R.realRoots hdiag ↔ α ∈ R.realRoots hdiag :=
  ⟨fun h ↦ by simpa [← mul_apply_eq_comp] using R.apply_mem_realRoots hdiag w⁻¹ h,
    R.apply_mem_realRoots hdiag w⟩

/-- Every simple reflection preserves `R.realRoots hdiag`. -/
theorem simpleReflection_mem_realRoots (i : I) {α : Dual K H} (hα : α ∈ R.realRoots hdiag) :
    R.simpleReflection hdiag i α ∈ R.realRoots hdiag := by
  simpa [coe_weylSimple] using R.apply_mem_realRoots hdiag (R.weylSimple hdiag i) hα

@[simp]
theorem simpleReflection_mem_realRoots_iff (i : I) {α : Dual K H} :
    R.simpleReflection hdiag i α ∈ R.realRoots hdiag ↔ α ∈ R.realRoots hdiag := by
  simpa [coe_weylSimple] using R.apply_mem_realRoots_iff hdiag (R.weylSimple hdiag i)

/-- The opposite of a real root is a real root. -/
theorem neg_mem_realRoots {α : Dual K H} (hα : α ∈ R.realRoots hdiag) :
    -α ∈ R.realRoots hdiag := by
  obtain ⟨w, i, rfl⟩ := (R.mem_realRoots_iff hdiag).mp hα
  refine (R.mem_realRoots_iff hdiag).mpr ⟨w * R.weylSimple hdiag i, i, ?_⟩
  simp [mul_apply_eq_comp]

@[simp]
theorem neg_mem_realRoots_iff {α : Dual K H} :
    -α ∈ R.realRoots hdiag ↔ α ∈ R.realRoots hdiag :=
  ⟨fun h ↦ neg_neg α ▸ R.neg_mem_realRoots hdiag h, R.neg_mem_realRoots hdiag⟩

/-- Zero is never a real root. -/
theorem zero_notMem_realRoots : (0 : Dual K H) ∉ R.realRoots hdiag := fun h0 ↦ by
  obtain ⟨w, i, hwi⟩ := (R.mem_realRoots_iff hdiag).mp h0
  exact R.root_linearIndependent.ne_zero i ((map_eq_zero_iff _ (LinearEquiv.injective _)).mp hwi)

/-- Every real root belongs to the root lattice `Q`. -/
theorem realRoots_subset_rootLattice : R.realRoots hdiag ⊆ R.rootLattice := fun _ hα ↦ by
  obtain ⟨w, i, rfl⟩ := (R.mem_realRoots_iff hdiag).mp hα
  exact (R.apply_mem_rootLattice_iff_of_mem_weylGroup hdiag w.property).mpr
    (R.root_mem_rootLattice i)

/-- Every simple root is a positive real root. -/
theorem root_mem_posRealRoots (i : I) : R.root i ∈ R.posRealRoots hdiag :=
  (R.mem_posRealRoots_iff hdiag).mpr ⟨R.root_mem_realRoots hdiag i, R.root_mem_posRootCone i⟩

end Integral

section CharZero
variable {I K H : Type*} [Field K] [CharZero K] [AddCommGroup H] [Module K H] {A : Matrix I I ℤ}
  (R : CartanRealization (A.map (Int.cast : ℤ → K)) H)

/-- **Real roots are indivisible in the root lattice** (Kac, Proposition 5.1(b)). -/
theorem eq_one_or_neg_one_of_zsmul_mem_realRoots
    (hdiag : ∀ i, (A.map (Int.cast : ℤ → K)) i i = 2)
    {n : ℤ} {β : Dual K H} (hβ : β ∈ R.rootLattice) (hn : n • β ∈ R.realRoots hdiag) :
    n = 1 ∨ n = -1 := by
  obtain ⟨w, i, hwi⟩ := (R.mem_realRoots_iff hdiag).mp hn
  have hγ : (w⁻¹ : R.weylGroup hdiag).val β ∈ R.rootLattice :=
    (R.apply_mem_rootLattice_iff_of_mem_weylGroup hdiag (w⁻¹).property).mpr hβ
  have hroot : R.root i = n • (w⁻¹ : R.weylGroup hdiag).val β := by
    have h1 := congrArg (w⁻¹ : R.weylGroup hdiag).val hwi
    simpa [← mul_apply_eq_comp] using h1
  let hli := R.root_linearIndependent.restrict_scalars' ℤ
  have hrepr : hli.repr ⟨R.root i, R.rootLattice_def ▸ R.root_mem_rootLattice i⟩ =
      n • hli.repr ⟨(w⁻¹ : R.weylGroup hdiag).val β, R.rootLattice_def ▸ hγ⟩ :=
    (congrArg hli.repr (Subtype.ext hroot)).trans (map_zsmul _ _ _)
  rw [hli.repr_eq_single i _ rfl] at hrepr
  exact Int.isUnit_iff.mp <| IsUnit.of_mul_eq_one _ <| by
    simpa using (congrArg (fun f : I →₀ ℤ ↦ f i) hrepr).symm

variable (hA : A.IsGeneralizedCartan)

/-- **Sign dichotomy for real roots** (Kac, §5.1): every real root lies in `Q₊` or `-Q₊`. -/
theorem mem_posRootCone_or_neg_mem_posRootCone_of_mem_realRoots
    {α : Dual K H} (hα : α ∈ R.realRoots (diag_map_intCast hA.diag)) :
    α ∈ R.posRootCone ∨ -α ∈ R.posRootCone := by
  obtain ⟨w, i, rfl⟩ := (R.mem_realRoots_iff (diag_map_intCast hA.diag)).mp hα
  exact R.apply_root_mem_posRootCone_or_neg_mem_posRootCone
    hA.diag hA.offDiag_nonpos hA.zero_comm w i

/-- **The simple reflection `sᵢ` stabilizes `Δ₊^re \ {αᵢ}`** (Kac, §5.1). -/
theorem simpleReflection_mem_posRealRoots (i : I) {α : Dual K H}
    (hα : α ∈ R.posRealRoots (diag_map_intCast hA.diag)) (hne : α ≠ R.root i) :
    R.simpleReflection (diag_map_intCast hA.diag) i α ∈
      R.posRealRoots (diag_map_intCast hA.diag) := by
  let hd := diag_map_intCast (K := K) hA.diag
  obtain ⟨hα_real, hα_pos⟩ := (R.mem_posRealRoots_iff hd).mp hα
  have hreal := R.simpleReflection_mem_realRoots hd i hα_real
  refine (R.mem_posRealRoots_iff hd).mpr
    ⟨hreal, (R.mem_posRootCone_or_neg_mem_posRootCone_of_mem_realRoots hA hreal).resolve_right
      fun hneg ↦ ?_⟩
  obtain ⟨m, hm⟩ := R.exists_apply_coroot_eq_intCast_of_mem_rootLattice
    (R.realRoots_subset_rootLattice hd hα_real) i
  have hsum : α + -(R.simpleReflection hd i α) = m • R.root i := by
    rw [simpleReflection_apply, hm, Int.cast_smul_eq_zsmul K m (R.root i)]; abel
  rcases le_or_gt m 0 with hm0 | hmpos
  · have hpt : α + -(R.simpleReflection hd i α) = 0 := by
      refine R.isPointed_posRootCone _ (add_mem hα_pos hneg) ?_
      rw [hsum, ← neg_zsmul, ← Int.toNat_of_nonneg (neg_nonneg.mpr hm0), natCast_zsmul]
      exact Submodule.smul_mem _ _ (R.root_mem_posRootCone i)
    exact R.zero_notMem_realRoots hd
      (R.isPointed_posRootCone _ hα_pos (by rwa [eq_neg_of_add_eq_zero_right hpt] at hneg) ▸
        hα_real)
  · obtain ⟨c, hc⟩ := R.exists_nsmul_root_of_add_eq_nsmul_root hα_pos hneg
      (by rwa [← natCast_zsmul, Int.toNat_of_nonneg hmpos.le])
    rw [← natCast_zsmul] at hc
    rcases R.eq_one_or_neg_one_of_zsmul_mem_realRoots hd
        (R.root_mem_rootLattice i) (hc ▸ hα_real) with h1 | hm1
    · exact hne (by rwa [h1, one_smul] at hc)
    · omega

/-- If `w₁(αᵢ) = w₂(αⱼ)`, then `w₁ sᵢ w₁⁻¹ = w₂ sⱼ w₂⁻¹`, showing that `R.realReflection` does
not depend on the chosen presentation `(w, i)` of a real root. -/
theorem conj_weylSimple_eq_of_apply_root_eq
    {w₁ w₂ : R.weylGroup (diag_map_intCast hA.diag)} {i j : I}
    (h : (w₁ : Dual K H ≃ₗ[K] Dual K H) (R.root i) = (w₂ : Dual K H ≃ₗ[K] Dual K H) (R.root j)) :
    w₁ * R.weylSimple (diag_map_intCast hA.diag) i * w₁⁻¹ =
      w₂ * R.weylSimple (diag_map_intCast hA.diag) j * w₂⁻¹ := by
  classical
  let cs := R.weylCoxeterSystem hA.diag hA.offDiag_nonpos hA.zero_comm
  let u := w₁⁻¹ * w₂
  have hu : (u : Dual K H ≃ₗ[K] Dual K H) (R.root j) = R.root i := by
    have h1 := congrArg (w₁⁻¹ : R.weylGroup (diag_map_intCast hA.diag)).val h.symm
    simpa [u, mul_apply_eq_comp, ← Subgroup.coe_mul] using h1
  have h_uj : cs.length (u * cs.simple j) = cs.length u + 1 := cs.not_isRightDescent_iff.mp <| by
    rw [R.not_isRightDescent_weylCoxeterSystem_iff hA.diag hA.offDiag_nonpos hA.zero_comm, hu]
    exact R.root_mem_posRootCone i
  have h_iu : cs.length (cs.simple i * u) = cs.length u + 1 := cs.not_isLeftDescent_iff.mp <| by
    rw [← cs.isRightDescent_inv_iff,
      R.not_isRightDescent_weylCoxeterSystem_iff hA.diag hA.offDiag_nonpos hA.zero_comm]
    have hu' : (u⁻¹ : R.weylGroup (diag_map_intCast hA.diag)).val (R.root i) = R.root j := by
      have h2 := congrArg (u⁻¹ : R.weylGroup (diag_map_intCast hA.diag)).val hu.symm
      simpa [← mul_apply_eq_comp, ← Subgroup.coe_mul] using h2
    rw [hu']
    exact R.root_mem_posRootCone j
  have h_iusj : cs.length (cs.simple i * u * cs.simple j) = cs.length u := by
    have hd : cs.IsRightDescent (cs.simple i * u) j := by
      rw [R.isRightDescent_weylCoxeterSystem_iff hA.diag hA.offDiag_nonpos hA.zero_comm,
        Subgroup.coe_mul, mul_apply_eq_comp, hu, R.weylCoxeterSystem_simple, coe_weylSimple,
        simpleReflection_root_self, neg_neg]
      exact R.root_mem_posRootCone i
    have hstep := cs.isRightDescent_iff.mp hd
    omega
  have hcomm := cs.simple_mul_eq_mul_simple_of_length_eq h_iusj (h_iu.trans h_uj.symm)
  rw [R.weylCoxeterSystem_simple, R.weylCoxeterSystem_simple] at hcomm
  calc w₁ * R.weylSimple (diag_map_intCast hA.diag) i * w₁⁻¹
    _ = w₁ * (R.weylSimple (diag_map_intCast hA.diag) i * u) * w₂⁻¹ := by simp [u, mul_assoc]
    _ = w₁ * (u * R.weylSimple (diag_map_intCast hA.diag) j) * w₂⁻¹ := by rw [hcomm]
    _ = w₂ * R.weylSimple (diag_map_intCast hA.diag) j * w₂⁻¹ := by simp [u, ← mul_assoc]

/-- If `u(αⱼ) = αᵢ`, then `R.ambientAction _ u` maps `hⱼ` to `hᵢ`. -/
theorem ambientAction_coroot_eq_coroot_of_apply_root_eq
    {u : R.weylGroup (diag_map_intCast hA.diag)} {i j : I}
    (hu : (u : Dual K H ≃ₗ[K] Dual K H) (R.root j) = R.root i) :
    R.ambientAction (diag_map_intCast hA.diag) u (R.coroot j) = R.coroot i := by
  let hd := diag_map_intCast (K := K) hA.diag
  have hconj : R.weylSimple hd i = u * R.weylSimple hd j * u⁻¹ := by
    have h1 : ((1 : R.weylGroup hd) : Dual K H ≃ₗ[K] Dual K H) (R.root i) =
        (u : Dual K H ≃ₗ[K] Dual K H) (R.root j) := hu.symm
    simpa using R.conj_weylSimple_eq_of_apply_root_eq hA h1
  have heval := congrArg (fun w ↦ R.ambientAction hd w (R.coroot i)) hconj
  have hpair : R.root j ((R.ambientAction hd u).symm (R.coroot i)) = 2 := by
    rw [← LinearEquiv.coe_inv, ← map_inv, ← R.weylGroup_apply_apply, hu, R.root_coroot, hd i]
  have htwo : (2 : K) • R.ambientAction hd u (R.coroot j) = (2 : K) • R.coroot i := by
    simpa [-simpleCoreflection_coroot_self, mul_apply_eq_comp, simpleCoreflection_apply,
      LinearEquiv.coe_inv, R.root_coroot, hA.diag i, hpair] using heval.symm
  exact smul_right_injective H (two_ne_zero : (2 : K) ≠ 0) htwo

/-- If `w₁(αᵢ) = w₂(αⱼ)`, then `ambientAction w₁ hᵢ = ambientAction w₂ hⱼ`, showing that
`R.realCoroot` does not depend on the chosen presentation `(w, i)` of a real root. -/
theorem ambientAction_coroot_eq_of_apply_root_eq
    {w₁ w₂ : R.weylGroup (diag_map_intCast hA.diag)} {i j : I}
    (h : (w₁ : Dual K H ≃ₗ[K] Dual K H) (R.root i) = (w₂ : Dual K H ≃ₗ[K] Dual K H) (R.root j)) :
    R.ambientAction (diag_map_intCast hA.diag) w₁ (R.coroot i) =
      R.ambientAction (diag_map_intCast hA.diag) w₂ (R.coroot j) := by
  have hu : ((w₁⁻¹ * w₂ : R.weylGroup (diag_map_intCast hA.diag)) :
      Dual K H ≃ₗ[K] Dual K H) (R.root j) = R.root i := by
    have h1 := congrArg (w₁⁻¹ : R.weylGroup (diag_map_intCast hA.diag)).val h.symm
    simpa [mul_apply_eq_comp, ← Subgroup.coe_mul] using h1
  have hcor := congrArg (R.ambientAction (diag_map_intCast hA.diag) w₁)
    (R.ambientAction_coroot_eq_coroot_of_apply_root_eq hA hu)
  simpa [← mul_apply_eq_comp, ← map_mul, ← mul_assoc] using hcor.symm

/-- The **real coroot** `α^∨ ∈ H` attached to a real root `α ∈ R.realRoots _`. -/
noncomputable def realCoroot {α : Dual K H}
    (hα : α ∈ R.realRoots (diag_map_intCast hA.diag)) : H :=
  let h := (R.mem_realRoots_iff (diag_map_intCast hA.diag)).mp hα
  R.ambientAction (diag_map_intCast hA.diag) h.choose (R.coroot h.choose_spec.choose)

/-- The **real reflection** `s_α ∈ R.weylGroup _` attached to a real root `α`. -/
noncomputable def realReflection {α : Dual K H}
    (hα : α ∈ R.realRoots (diag_map_intCast hA.diag)) :
    R.weylGroup (diag_map_intCast hA.diag) :=
  let h := (R.mem_realRoots_iff (diag_map_intCast hA.diag)).mp hα
  h.choose * R.weylSimple (diag_map_intCast hA.diag) h.choose_spec.choose * h.choose⁻¹

/-- Word independence of `R.realCoroot`: for any `(w, i)` with `w(αᵢ) = α`,
`R.realCoroot hA hα = R.ambientAction _ w (R.coroot i)`. -/
theorem realCoroot_eq_of_apply_root_eq {w : R.weylGroup (diag_map_intCast hA.diag)} {i : I}
    {α : Dual K H} (hα : α ∈ R.realRoots (diag_map_intCast hA.diag))
    (hw : (w : Dual K H ≃ₗ[K] Dual K H) (R.root i) = α) :
    R.realCoroot hA hα = R.ambientAction (diag_map_intCast hA.diag) w (R.coroot i) :=
  R.ambientAction_coroot_eq_of_apply_root_eq hA
    (((R.mem_realRoots_iff (diag_map_intCast hA.diag)).mp hα).choose_spec.choose_spec.trans hw.symm)

/-- Word independence of `R.realReflection`: for any `(w, i)` with `w(αᵢ) = α`,
`R.realReflection hA hα = w * sᵢ * w⁻¹`. -/
theorem realReflection_eq_of_apply_root_eq {w : R.weylGroup (diag_map_intCast hA.diag)} {i : I}
    {α : Dual K H} (hα : α ∈ R.realRoots (diag_map_intCast hA.diag))
    (hw : (w : Dual K H ≃ₗ[K] Dual K H) (R.root i) = α) :
    R.realReflection hA hα = w * R.weylSimple (diag_map_intCast hA.diag) i * w⁻¹ :=
  R.conj_weylSimple_eq_of_apply_root_eq hA
    (((R.mem_realRoots_iff (diag_map_intCast hA.diag)).mp hα).choose_spec.choose_spec.trans hw.symm)

/-- The real coroot of `w(αᵢ)` is `w(hᵢ)`. -/
@[simp]
theorem realCoroot_apply_root (w : R.weylGroup (diag_map_intCast hA.diag)) (i : I) :
    R.realCoroot hA (R.apply_root_mem_realRoots (diag_map_intCast hA.diag) w i) =
      R.ambientAction (diag_map_intCast hA.diag) w (R.coroot i) :=
  R.realCoroot_eq_of_apply_root_eq hA _ rfl

/-- The real coroot of a simple root `αᵢ` is `hᵢ`. -/
@[simp]
theorem realCoroot_root (i : I) :
    R.realCoroot hA (R.root_mem_realRoots (diag_map_intCast hA.diag) i) = R.coroot i := by
  simpa using R.realCoroot_eq_of_apply_root_eq hA (R.root_mem_realRoots _ i) (w := 1) rfl

/-- Equivariance of `R.realCoroot` under the Weyl group: `(w(α))^∨ = w(α^∨)`. -/
@[simp]
theorem realCoroot_apply (w : R.weylGroup (diag_map_intCast hA.diag)) {α : Dual K H}
    (hα : α ∈ R.realRoots (diag_map_intCast hA.diag)) :
    R.realCoroot hA (R.apply_mem_realRoots (diag_map_intCast hA.diag) w hα) =
      R.ambientAction (diag_map_intCast hA.diag) w (R.realCoroot hA hα) := by
  obtain ⟨u, i, hui⟩ := (R.mem_realRoots_iff (diag_map_intCast hA.diag)).mp hα
  have hwu : ((w * u : R.weylGroup (diag_map_intCast hA.diag)) :
      Dual K H ≃ₗ[K] Dual K H) (R.root i) = (w : Dual K H ≃ₗ[K] Dual K H) α := by
    simp [mul_apply_eq_comp, hui]
  rw [R.realCoroot_eq_of_apply_root_eq hA _ hwu, R.realCoroot_eq_of_apply_root_eq hA hα hui,
    map_mul, mul_apply_eq_comp]

/-- Negating a real root negates its real coroot: `(-α)^∨ = -α^∨`. -/
@[simp]
theorem realCoroot_neg {α : Dual K H} (hα : α ∈ R.realRoots (diag_map_intCast hA.diag)) :
    R.realCoroot hA (R.neg_mem_realRoots (diag_map_intCast hA.diag) hα) =
      -R.realCoroot hA hα := by
  obtain ⟨w, i, rfl⟩ := (R.mem_realRoots_iff (diag_map_intCast hA.diag)).mp hα
  have hneg : ((w * R.weylSimple (diag_map_intCast hA.diag) i :
      R.weylGroup (diag_map_intCast hA.diag)) : Dual K H ≃ₗ[K] Dual K H) (R.root i) =
      -((w : Dual K H ≃ₗ[K] Dual K H) (R.root i)) := by
    simp [mul_apply_eq_comp]
  rw [R.realCoroot_eq_of_apply_root_eq hA _ hneg, R.realCoroot_apply_root, map_mul]
  simp [mul_apply_eq_comp]

/-- Every real coroot lies in `R.corootSpan`. -/
theorem realCoroot_mem_corootSpan {α : Dual K H}
    (hα : α ∈ R.realRoots (diag_map_intCast hA.diag)) :
    R.realCoroot hA hα ∈ R.corootSpan := by
  obtain ⟨w, i, hwi⟩ := (R.mem_realRoots_iff (diag_map_intCast hA.diag)).mp hα
  rw [R.realCoroot_eq_of_apply_root_eq hA hα hwi]
  exact R.ambientAction_mem_corootSpan (diag_map_intCast hA.diag) w (R.coroot_mem_corootSpan i)

/-- Every real root pairs to `2` with its real coroot: `α(α^∨) = 2`. -/
@[simp]
theorem apply_realCoroot_self {α : Dual K H} (hα : α ∈ R.realRoots (diag_map_intCast hA.diag)) :
    α (R.realCoroot hA hα) = 2 := by
  obtain ⟨w, i, hwi⟩ := (R.mem_realRoots_iff (diag_map_intCast hA.diag)).mp hα
  rw [R.realCoroot_eq_of_apply_root_eq hA hα hwi, ← hwi, R.apply_ambientAction, R.root_coroot,
    diag_map_intCast hA.diag i]

/-- The real reflection in `w(αᵢ)` is `w * sᵢ * w⁻¹`. -/
@[simp]
theorem realReflection_apply_root (w : R.weylGroup (diag_map_intCast hA.diag)) (i : I) :
    R.realReflection hA (R.apply_root_mem_realRoots (diag_map_intCast hA.diag) w i) =
      w * R.weylSimple (diag_map_intCast hA.diag) i * w⁻¹ :=
  R.realReflection_eq_of_apply_root_eq hA _ rfl

/-- The real reflection in a simple root `αᵢ` is `sᵢ`. -/
@[simp]
theorem realReflection_root (i : I) :
    R.realReflection hA (R.root_mem_realRoots (diag_map_intCast hA.diag) i) =
      R.weylSimple (diag_map_intCast hA.diag) i := by
  simpa using R.realReflection_eq_of_apply_root_eq hA (R.root_mem_realRoots _ i) (w := 1) rfl

/-- Conjugation equivariance of `R.realReflection`: `s_{w(α)} = w * s_α * w⁻¹`. -/
@[simp]
theorem realReflection_apply (w : R.weylGroup (diag_map_intCast hA.diag)) {α : Dual K H}
    (hα : α ∈ R.realRoots (diag_map_intCast hA.diag)) :
    R.realReflection hA (R.apply_mem_realRoots (diag_map_intCast hA.diag) w hα) =
      w * R.realReflection hA hα * w⁻¹ := by
  obtain ⟨u, i, hui⟩ := (R.mem_realRoots_iff (diag_map_intCast hA.diag)).mp hα
  have hwu : ((w * u : R.weylGroup (diag_map_intCast hA.diag)) :
      Dual K H ≃ₗ[K] Dual K H) (R.root i) = (w : Dual K H ≃ₗ[K] Dual K H) α := by
    simp [mul_apply_eq_comp, hui]
  rw [R.realReflection_eq_of_apply_root_eq hA _ hwu, R.realReflection_eq_of_apply_root_eq hA hα hui]
  simp [mul_assoc]

/-- Opposite real roots determine the same reflection: `s_{-α} = s_α`. -/
@[simp]
theorem realReflection_neg {α : Dual K H} (hα : α ∈ R.realRoots (diag_map_intCast hA.diag)) :
    R.realReflection hA (R.neg_mem_realRoots (diag_map_intCast hA.diag) hα) =
      R.realReflection hA hα := by
  obtain ⟨w, i, rfl⟩ := (R.mem_realRoots_iff (diag_map_intCast hA.diag)).mp hα
  have hneg : ((w * R.weylSimple (diag_map_intCast hA.diag) i :
      R.weylGroup (diag_map_intCast hA.diag)) : Dual K H ≃ₗ[K] Dual K H) (R.root i) =
      -((w : Dual K H ≃ₗ[K] Dual K H) (R.root i)) := by
    simp [mul_apply_eq_comp]
  rw [R.realReflection_eq_of_apply_root_eq hA _ hneg, R.realReflection_apply_root, mul_assoc w]
  simp [← mul_assoc]

/-- Reflection formula on `Dual K H` for `R.realReflection`: `s_α(φ) = φ - φ(α^∨) • α`. -/
theorem coe_realReflection_apply {α : Dual K H} (hα : α ∈ R.realRoots (diag_map_intCast hA.diag))
    (φ : Dual K H) :
    (R.realReflection hA hα : Dual K H ≃ₗ[K] Dual K H) φ = φ - φ (R.realCoroot hA hα) • α := by
  let hd := diag_map_intCast (K := K) hA.diag
  obtain ⟨w, i, hwi⟩ := (R.mem_realRoots_iff hd).mp hα
  have hpair : (w : Dual K H ≃ₗ[K] Dual K H).symm φ (R.coroot i) =
      φ (R.ambientAction hd w (R.coroot i)) := by
    simpa [LinearEquiv.coe_inv] using R.weylGroup_apply_apply hd w⁻¹ φ (R.coroot i)
  rw [R.realReflection_eq_of_apply_root_eq hA hα hwi, R.realCoroot_eq_of_apply_root_eq hA hα hwi,
    ← hwi]
  simp [mul_apply_eq_comp, simpleReflection_apply, LinearEquiv.coe_inv, hpair]

/-- Dual reflection formula on `H` for `R.realReflection`: `s_α(x) = x - α(x) • α^∨`. -/
theorem ambientAction_realReflection_apply {α : Dual K H}
    (hα : α ∈ R.realRoots (diag_map_intCast hA.diag)) (x : H) :
    R.ambientAction (diag_map_intCast hA.diag) (R.realReflection hA hα) x =
      x - α x • R.realCoroot hA hα := by
  let hd := diag_map_intCast (K := K) hA.diag
  obtain ⟨w, i, hwi⟩ := (R.mem_realRoots_iff hd).mp hα
  have hpair : R.root i ((R.ambientAction hd w).symm x) =
      (w : Dual K H ≃ₗ[K] Dual K H) (R.root i) x := by
    rw [R.weylGroup_apply_apply, map_inv, LinearEquiv.coe_inv]
  rw [R.realReflection_eq_of_apply_root_eq hA hα hwi, R.realCoroot_eq_of_apply_root_eq hA hα hwi,
    ← hwi]
  simp [mul_apply_eq_comp, simpleCoreflection_apply, LinearEquiv.coe_inv, hpair]

/-- Every real reflection negates its own real root: `s_α(α) = -α`. -/
@[simp]
theorem coe_realReflection_apply_self {α : Dual K H}
    (hα : α ∈ R.realRoots (diag_map_intCast hA.diag)) :
    (R.realReflection hA hα : Dual K H ≃ₗ[K] Dual K H) α = -α := by
  rw [R.coe_realReflection_apply hA hα α, R.apply_realCoroot_self hA hα, two_smul]
  abel

/-- Every real reflection negates its own real coroot on `H`: `s_α(α^∨) = -α^∨`. -/
@[simp]
theorem ambientAction_realReflection_apply_self {α : Dual K H}
    (hα : α ∈ R.realRoots (diag_map_intCast hA.diag)) :
    R.ambientAction (diag_map_intCast hA.diag) (R.realReflection hA hα) (R.realCoroot hA hα) =
      -R.realCoroot hA hα := by
  rw [R.ambientAction_realReflection_apply hA hα, R.apply_realCoroot_self hA hα, two_smul]
  abel

/-- Every real reflection is an involution in `R.weylGroup _`. -/
@[simp]
theorem realReflection_mul_self {α : Dual K H}
    (hα : α ∈ R.realRoots (diag_map_intCast hA.diag)) :
    R.realReflection hA hα * R.realReflection hA hα = 1 := by
  obtain ⟨w, i, hwi⟩ := (R.mem_realRoots_iff (diag_map_intCast hA.diag)).mp hα
  rw [R.realReflection_eq_of_apply_root_eq hA hα hwi]
  simp only [mul_assoc, inv_mul_cancel_left]
  rw [← mul_assoc (R.weylSimple _ i), weylSimple_mul_self, one_mul, mul_inv_cancel]

/-- Every real reflection equals its own inverse in `R.weylGroup _`. -/
@[simp]
theorem realReflection_inv {α : Dual K H}
    (hα : α ∈ R.realRoots (diag_map_intCast hA.diag)) :
    (R.realReflection hA hα)⁻¹ = R.realReflection hA hα :=
  inv_eq_of_mul_eq_one_right (R.realReflection_mul_self hA hα)

end CharZero

namespace CoweightLattice
variable {I H : Type*} [AddCommGroup H] [Module ℚ H] {A : Matrix I I ℤ}
  {R : CartanRealization (A.map (Int.cast : ℤ → ℚ)) H}
  (L : R.CoweightLattice) (hA : A.IsGeneralizedCartan)

/-- Every real coroot of a rational realization belongs to any admissible coweight lattice. -/
theorem realCoroot_mem_lattice {α : Dual ℚ H}
    (hα : α ∈ R.realRoots (diag_map_intCast hA.diag)) :
    R.realCoroot hA hα ∈ L.lattice := by
  obtain ⟨w, i, hwi⟩ := (R.mem_realRoots_iff (diag_map_intCast hA.diag)).mp hα
  rw [R.realCoroot_eq_of_apply_root_eq hA hα hwi]
  exact L.ambientAction_mem_lattice (diag_map_intCast hA.diag) w (L.coroot_mem i)

end CoweightLattice

end TauCeti.CartanRealization

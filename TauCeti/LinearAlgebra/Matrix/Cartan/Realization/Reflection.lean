/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Reflection
public import TauCeti.LinearAlgebra.Matrix.Cartan.Realization.BaseChange
public import TauCeti.LinearAlgebra.Matrix.Cartan.Realization.RootLattice

/-!
# Simple reflections and coreflections of a Cartan realization

For a realization `R : TauCeti.CartanRealization A H` over a field `K` with `hA : ∀ i, A i i = 2`,
Mathlib's `Module.reflection` defines two involutive automorphisms at each `i : I`:
* `simpleCoreflection` (`sᵢ^∨ : H ≃ₗ[K] H`), `h ↦ h - αᵢ(h) • hᵢ`;
* `simpleReflection` (`sᵢ : Dual K H ≃ₗ[K] Dual K H`), `λ ↦ λ - λ(hᵢ) • αᵢ`.

We prove contragredient duality (`sᵢ = (sᵢ^∨).dualMap`) and pairing invariance, stability of
`R.cartanCenter` and `R.corootSpan`, compatibility with `map`, `restrict`, and `baseChange`, and
induced `ℤ`-linear reflections on `R.rootLattice`, any coweight lattice `Y`, and its dual weight
lattice `P`.

## References

* V. G. Kac, *Infinite-dimensional Lie algebras*, third edition, Cambridge University Press, 1990,
  §3.7.
-/

public section

open Module
open scoped TensorProduct

namespace TauCeti.CartanRealization

section Field

variable {I K H : Type*} [Field K] [AddCommGroup H] [Module K H] {A : Matrix I I K}
  (R : CartanRealization A H) (hA : ∀ i, A i i = 2)

/-! ### Definitions and basic involutive identities -/

/-- The **simple coreflection** `sᵢ^∨ : H ≃ₗ[K] H` sending `h ↦ h - αᵢ(h) • hᵢ`. -/
noncomputable def simpleCoreflection (i : I) : H ≃ₗ[K] H :=
  Module.reflection (x := R.coroot i) (f := R.root i) ((R.root_coroot i i).trans (hA i))

/-- The **simple reflection** `sᵢ : Dual K H ≃ₗ[K] Dual K H` sending `λ ↦ λ - λ(hᵢ) • αᵢ`. -/
noncomputable def simpleReflection (i : I) : Dual K H ≃ₗ[K] Dual K H :=
  Module.reflection (x := R.root i) (f := Dual.eval K H (R.coroot i)) (by simpa using hA i)

theorem simpleCoreflection_eq_reflection (i : I) :
    R.simpleCoreflection hA i = Module.reflection ((R.root_coroot i i).trans (hA i)) := (rfl)

theorem simpleReflection_eq_reflection (i : I) :
    R.simpleReflection hA i =
      Module.reflection (x := R.root i) (f := Dual.eval K H (R.coroot i)) (by simpa using hA i) :=
  (rfl)

theorem simpleCoreflection_apply (i : I) (h : H) :
    R.simpleCoreflection hA i h = h - R.root i h • R.coroot i := Module.reflection_apply h _

theorem simpleReflection_apply (i : I) (φ : Dual K H) :
    R.simpleReflection hA i φ = φ - φ (R.coroot i) • R.root i := Module.reflection_apply φ _

theorem simpleCoreflection_coroot (i j : I) :
    R.simpleCoreflection hA i (R.coroot j) = R.coroot j - A j i • R.coroot i := by
  rw [simpleCoreflection_apply, R.root_coroot]

theorem simpleReflection_root (i j : I) :
    R.simpleReflection hA i (R.root j) = R.root j - A i j • R.root i := by
  rw [simpleReflection_apply, R.root_coroot]

@[simp] theorem simpleCoreflection_coroot_self (i : I) :
    R.simpleCoreflection hA i (R.coroot i) = -R.coroot i := Module.reflection_apply_self _

@[simp] theorem simpleReflection_root_self (i : I) :
    R.simpleReflection hA i (R.root i) = -R.root i := Module.reflection_apply_self _

@[simp] theorem simpleCoreflection_simpleCoreflection (i : I) (h : H) :
    R.simpleCoreflection hA i (R.simpleCoreflection hA i h) = h := Module.involutive_reflection _ h

@[simp] theorem simpleReflection_simpleReflection (i : I) (φ : Dual K H) :
    R.simpleReflection hA i (R.simpleReflection hA i φ) = φ := Module.involutive_reflection _ φ

theorem involutive_simpleCoreflection (i : I) : Function.Involutive (R.simpleCoreflection hA i) :=
  Module.involutive_reflection _

theorem involutive_simpleReflection (i : I) : Function.Involutive (R.simpleReflection hA i) :=
  Module.involutive_reflection _

@[simp] theorem simpleCoreflection_symm (i : I) :
    (R.simpleCoreflection hA i).symm = R.simpleCoreflection hA i := Module.reflection_symm _

@[simp] theorem simpleReflection_symm (i : I) :
    (R.simpleReflection hA i).symm = R.simpleReflection hA i := Module.reflection_symm _

@[simp] theorem simpleCoreflection_inv (i : I) :
    (R.simpleCoreflection hA i)⁻¹ = R.simpleCoreflection hA i := Module.reflection_inv _

@[simp] theorem simpleReflection_inv (i : I) :
    (R.simpleReflection hA i)⁻¹ = R.simpleReflection hA i := Module.reflection_inv _

@[simp] theorem simpleCoreflection_mul_self (i : I) :
    R.simpleCoreflection hA i * R.simpleCoreflection hA i = 1 :=
  LinearEquiv.ext (R.simpleCoreflection_simpleCoreflection hA i)

@[simp] theorem simpleReflection_mul_self (i : I) :
    R.simpleReflection hA i * R.simpleReflection hA i = 1 :=
  LinearEquiv.ext (R.simpleReflection_simpleReflection hA i)

@[simp] theorem simpleCoreflection_sq (i : I) : R.simpleCoreflection hA i ^ 2 = 1 := by
  rw [sq, simpleCoreflection_mul_self]

@[simp] theorem simpleReflection_sq (i : I) : R.simpleReflection hA i ^ 2 = 1 := by
  rw [sq, simpleReflection_mul_self]

theorem simpleCoreflection_eq_self_of_apply_eq_zero {i : I} {h : H} (hh : R.root i h = 0) :
    R.simpleCoreflection hA i h = h := by rw [simpleCoreflection_apply, hh, zero_smul, sub_zero]

theorem simpleReflection_eq_self_of_apply_eq_zero {i : I} {φ : Dual K H}
    (hφ : φ (R.coroot i) = 0) : R.simpleReflection hA i φ = φ := by
  rw [simpleReflection_apply, hφ, zero_smul, sub_zero]

/-- `sᵢ^∨` fixes `h` if and only if `αᵢ(h) = 0`. -/
theorem simpleCoreflection_eq_self_iff {i : I} {h : H} :
    R.simpleCoreflection hA i h = h ↔ R.root i h = 0 := by
  rw [simpleCoreflection_apply, sub_eq_self, smul_eq_zero]
  exact or_iff_left (R.coroot_linearIndependent.ne_zero i)

/-- `sᵢ` fixes `φ` if and only if `φ(hᵢ) = 0`. -/
theorem simpleReflection_eq_self_iff {i : I} {φ : Dual K H} :
    R.simpleReflection hA i φ = φ ↔ φ (R.coroot i) = 0 := by
  rw [simpleReflection_apply, sub_eq_self, smul_eq_zero]
  exact or_iff_left (R.root_linearIndependent.ne_zero i)

/-! ### Contragredient duality and pairing invariance -/

/-- The simple reflection on `Dual K H` is the contragredient transpose of the simple coreflection
on `H`. -/
theorem simpleReflection_eq_dualMap (i : I) :
    R.simpleReflection hA i = (R.simpleCoreflection hA i).dualMap := by
  ext φ h
  simp only [simpleReflection_apply, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
    LinearEquiv.dualMap_apply, simpleCoreflection_apply, map_sub, map_smul]
  ring

theorem simpleReflection_apply_eq_apply_simpleCoreflection (i : I) (φ : Dual K H) (h : H) :
    R.simpleReflection hA i φ h = φ (R.simpleCoreflection hA i h) := by
  rw [simpleReflection_eq_dualMap, LinearEquiv.dualMap_apply]

/-- Simple reflections and coreflections preserve the evaluation pairing:
`(sᵢ φ)(sᵢ^∨ h) = φ(h)`. -/
@[simp] theorem simpleReflection_apply_simpleCoreflection (i : I) (φ : Dual K H) (h : H) :
    R.simpleReflection hA i φ (R.simpleCoreflection hA i h) = φ h := by
  rw [simpleReflection_apply_eq_apply_simpleCoreflection, simpleCoreflection_simpleCoreflection]

@[simp] theorem simpleReflection_apply_coroot_self (i : I) (φ : Dual K H) :
    R.simpleReflection hA i φ (R.coroot i) = -φ (R.coroot i) := by
  rw [simpleReflection_apply_eq_apply_simpleCoreflection, simpleCoreflection_coroot_self, map_neg]

@[simp] theorem root_simpleCoreflection_self (i : I) (h : H) :
    R.root i (R.simpleCoreflection hA i h) = -R.root i h := by
  rw [← simpleReflection_apply_eq_apply_simpleCoreflection R hA, simpleReflection_root_self,
    LinearMap.neg_apply]

/-! ### Stability of the Cartan center and the coroot span -/

/-- Every simple coreflection fixes the Cartan center pointwise. -/
theorem simpleCoreflection_eq_self_of_mem_cartanCenter (i : I) {h : H}
    (hh : h ∈ R.cartanCenter) : R.simpleCoreflection hA i h = h :=
  R.simpleCoreflection_eq_self_of_apply_eq_zero hA ((R.mem_cartanCenter_iff h).mp hh i)

theorem simpleCoreflection_mem_cartanCenter_iff (i : I) (h : H) :
    R.simpleCoreflection hA i h ∈ R.cartanCenter ↔ h ∈ R.cartanCenter :=
  ⟨fun hh ↦ R.simpleCoreflection_simpleCoreflection hA i h ▸
      (R.simpleCoreflection_eq_self_of_mem_cartanCenter hA i hh).symm ▸ hh,
    fun hh ↦ (R.simpleCoreflection_eq_self_of_mem_cartanCenter hA i hh).symm ▸ hh⟩

theorem simpleReflection_apply_of_mem_cartanCenter (i : I) (φ : Dual K H) {h : H}
    (hh : h ∈ R.cartanCenter) : R.simpleReflection hA i φ h = φ h := by
  rw [simpleReflection_apply_eq_apply_simpleCoreflection,
    R.simpleCoreflection_eq_self_of_mem_cartanCenter hA i hh]

/-- Every simple coreflection preserves the coroot span. -/
theorem simpleCoreflection_mem_corootSpan (i : I) {h : H} (hh : h ∈ R.corootSpan) :
    R.simpleCoreflection hA i h ∈ R.corootSpan :=
  (R.simpleCoreflection_apply hA i h).symm ▸
    sub_mem hh (Submodule.smul_mem _ _ (R.coroot_mem_corootSpan i))

@[simp] theorem simpleCoreflection_mem_corootSpan_iff (i : I) (h : H) :
    R.simpleCoreflection hA i h ∈ R.corootSpan ↔ h ∈ R.corootSpan :=
  ⟨fun hh ↦ R.simpleCoreflection_simpleCoreflection hA i h ▸
      R.simpleCoreflection_mem_corootSpan hA i hh,
    R.simpleCoreflection_mem_corootSpan hA i⟩

/-! ### Functoriality under transport, sub-realization restriction, and scalar extension -/

theorem map_simpleCoreflection {H' : Type*} [AddCommGroup H'] [Module K H']
    (e : H ≃ₗ[K] H') (i : I) :
    (R.map e).simpleCoreflection hA i = e.symm.trans ((R.simpleCoreflection hA i).trans e) := by
  ext h
  simp [simpleCoreflection_apply]

@[simp] theorem map_simpleCoreflection_apply {H' : Type*} [AddCommGroup H'] [Module K H']
    (e : H ≃ₗ[K] H') (i : I) (h : H) :
    (R.map e).simpleCoreflection hA i (e h) = e (R.simpleCoreflection hA i h) := by
  simp [map_simpleCoreflection]

theorem map_simpleReflection {H' : Type*} [AddCommGroup H'] [Module K H']
    (e : H ≃ₗ[K] H') (i : I) :
    (R.map e).simpleReflection hA i =
      e.dualMap.trans ((R.simpleReflection hA i).trans e.symm.dualMap) := by
  ext φ h
  simp [simpleReflection_apply]

@[simp] theorem map_simpleReflection_apply {H' : Type*} [AddCommGroup H'] [Module K H']
    (e : H ≃ₗ[K] H') (i : I) (φ : Dual K H) :
    (R.map e).simpleReflection hA i (e.symm.dualMap φ) =
      e.symm.dualMap (R.simpleReflection hA i φ) := by
  ext h
  simp [simpleReflection_apply]

@[simp] theorem coe_restrict_simpleCoreflection (M : Submodule K H) (hc : R.corootSpan ≤ M)
    (hs : M ⊔ R.cartanCenter = ⊤) (i : I) (m : M) :
    ((R.restrict M hc hs).simpleCoreflection hA i m : H) = R.simpleCoreflection hA i m := by
  simp [simpleCoreflection_apply]

@[simp] theorem restrict_simpleReflection_comp_subtype (M : Submodule K H) (hc : R.corootSpan ≤ M)
    (hs : M ⊔ R.cartanCenter = ⊤) (i : I) (φ : Dual K H) :
    (R.restrict M hc hs).simpleReflection hA i (φ.comp M.subtype) =
      (R.simpleReflection hA i φ).comp M.subtype := by
  ext m
  simp [simpleReflection_apply]

theorem baseChange_simpleCoreflection [FiniteDimensional K H] (L : Type*) [Field L] [Algebra K L]
    (i : I) :
    (R.baseChange L).simpleCoreflection (fun j ↦ by simp [hA j, map_ofNat]) i =
      (R.simpleCoreflection hA i).baseChange K L H H := by
  apply LinearEquiv.toLinearMap_injective
  ext h
  simp [simpleCoreflection_apply, TensorProduct.tmul_sub, Algebra.smul_def]

@[simp] theorem baseChange_simpleReflection_baseChange [FiniteDimensional K H] (L : Type*)
    [Field L] [Algebra K L] (i : I) (φ : Dual K H) :
    (R.baseChange L).simpleReflection (fun j ↦ by simp [hA j, map_ofNat]) i (φ.baseChange L) =
      (R.simpleReflection hA i φ).baseChange L := by
  ext h
  simp [simpleReflection_apply, Module.Dual.baseChange_apply_tmul, Algebra.smul_def]

end Field

/-! ### Stability of the root lattice `Q` -/

/-- A scalar multiple `c • αᵢ` of a simple root lies in the root lattice `Q` if and only if `c`
lies in the image of `ℤ` in `K`. -/
@[simp] theorem smul_root_mem_rootLattice_iff {I K H : Type*} [Field K] [AddCommGroup H]
    [Module K H] {A : Matrix I I K} (R : CartanRealization A H) (c : K) (i : I) :
    c • R.root i ∈ R.rootLattice ↔ c ∈ (1 : Submodule ℤ K) := by
  refine ⟨fun hc ↦ ?_, fun hc ↦ ?_⟩
  · obtain ⟨f, hf⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp (R.rootLattice_def ▸ hc)
    refine Submodule.mem_one.mpr ⟨f i, ?_⟩
    have hlin : Finsupp.linearCombination K R.root
        (f.mapRange (Int.cast : ℤ → K) Int.cast_zero - Finsupp.single i c) = 0 := by
      rw [map_sub, Finsupp.linearCombination_single, Finsupp.linearCombination_apply,
        Finsupp.sum_mapRange_index (fun j ↦ zero_smul K (R.root j))]
      simpa only [Int.cast_smul_eq_zsmul] using sub_eq_zero.mpr hf
    simpa [sub_eq_zero] using
      Finsupp.ext_iff.mp (linearIndependent_iff.mp R.root_linearIndependent _ hlin) i
  · obtain ⟨n, rfl⟩ := Submodule.mem_one.mp hc
    simpa only [algebraMap_smul] using R.rootLattice.smul_mem n (R.root_mem_rootLattice i)

section RootLattice

variable {I K H : Type*} [Field K] [AddCommGroup H] [Module K H] {A : Matrix I I ℤ}
  (R : CartanRealization (A.map (Int.cast : ℤ → K)) H)

/-- Every element of the root lattice takes values in the image of `ℤ` on each simple coroot. -/
theorem apply_coroot_mem_one_of_mem_rootLattice {φ : Dual K H} (hφ : φ ∈ R.rootLattice) (i : I) :
    φ (R.coroot i) ∈ (1 : Submodule ℤ K) := by
  rw [R.rootLattice_def] at hφ
  induction hφ using Submodule.span_induction with
  | mem _ hx => obtain ⟨j, rfl⟩ := hx; exact Submodule.mem_one.mpr ⟨A i j, by simp⟩
  | zero => simp
  | add _ _ _ _ hx hy => simpa only [LinearMap.add_apply] using add_mem hx hy
  | smul n _ _ hx => simpa only [LinearMap.smul_apply] using Submodule.smul_mem _ n hx

/-- Simple reflections preserve the root lattice `Q`. -/
theorem simpleReflection_mem_rootLattice (hA : ∀ i, A.map (Int.cast : ℤ → K) i i = 2) (i : I)
    {φ : Dual K H} (hφ : φ ∈ R.rootLattice) : R.simpleReflection hA i φ ∈ R.rootLattice := by
  obtain ⟨n, hn⟩ := Submodule.mem_one.mp (R.apply_coroot_mem_one_of_mem_rootLattice hφ i)
  rw [simpleReflection_apply, ← hn, algebraMap_smul]
  exact sub_mem hφ (Submodule.smul_mem _ n (R.root_mem_rootLattice i))

@[simp] theorem simpleReflection_mem_rootLattice_iff (hA : ∀ i, A.map (Int.cast : ℤ → K) i i = 2)
    (i : I) (φ : Dual K H) : R.simpleReflection hA i φ ∈ R.rootLattice ↔ φ ∈ R.rootLattice :=
  ⟨fun hφ ↦ R.simpleReflection_simpleReflection hA i φ ▸ R.simpleReflection_mem_rootLattice hA i hφ,
    R.simpleReflection_mem_rootLattice hA i⟩

/-- The `ℤ`-linear automorphism of the root lattice `Q` induced by the `i`-th simple reflection. -/
noncomputable def rootLatticeSimpleReflection (hA : ∀ i, A.map (Int.cast : ℤ → K) i i = 2)
    (i : I) : R.rootLattice ≃ₗ[ℤ] R.rootLattice :=
  LinearEquiv.ofInvolutive
    (((R.simpleReflection hA i).toLinearMap.restrictScalars ℤ).restrict
      fun _ ↦ R.simpleReflection_mem_rootLattice hA i)
    fun x ↦ Subtype.ext (R.simpleReflection_simpleReflection hA i x)

@[simp] theorem coe_rootLatticeSimpleReflection_apply (hA : ∀ i, A.map (Int.cast : ℤ → K) i i = 2)
    (i : I) (x : R.rootLattice) :
    (R.rootLatticeSimpleReflection hA i x : Dual K H) = R.simpleReflection hA i x := (rfl)

@[simp] theorem rootLatticeSimpleReflection_symm (hA : ∀ i, A.map (Int.cast : ℤ → K) i i = 2)
    (i : I) : (R.rootLatticeSimpleReflection hA i).symm = R.rootLatticeSimpleReflection hA i :=
  (rfl)

end RootLattice

/-! ### Stability of coweight and weight lattices `Y` and `P` -/

namespace CoweightLattice

variable {I H : Type*} [AddCommGroup H] [Module ℚ H] {A : Matrix I I ℤ}
  {R : CartanRealization (A.map (Int.cast : ℤ → ℚ)) H} (L : R.CoweightLattice)

/-- Simple coreflections preserve every coweight lattice `Y`. -/
theorem simpleCoreflection_mem_lattice (hA : ∀ i, A.map (Int.cast : ℤ → ℚ) i i = 2) (i : I)
    {y : H} (hy : y ∈ L.lattice) : R.simpleCoreflection hA i y ∈ L.lattice := by
  obtain ⟨n, hn⟩ := Submodule.mem_one.mp
    ((Submodule.mem_dualLattice L.lattice (R.root i)).mp (L.root_mem_dualLattice i) y hy)
  rw [simpleCoreflection_apply, ← hn, algebraMap_smul]
  exact sub_mem hy (Submodule.smul_mem _ n (L.coroot_mem i))

@[simp] theorem simpleCoreflection_mem_lattice_iff (hA : ∀ i, A.map (Int.cast : ℤ → ℚ) i i = 2)
    (i : I) (y : H) : R.simpleCoreflection hA i y ∈ L.lattice ↔ y ∈ L.lattice :=
  ⟨fun hy ↦ R.simpleCoreflection_simpleCoreflection hA i y ▸
      L.simpleCoreflection_mem_lattice hA i hy,
    L.simpleCoreflection_mem_lattice hA i⟩

/-- Simple reflections preserve the dual weight lattice `P`. -/
theorem simpleReflection_mem_weightLattice (hA : ∀ i, A.map (Int.cast : ℤ → ℚ) i i = 2) (i : I)
    {φ : Dual ℚ H} (hφ : φ ∈ L.weightLattice) : R.simpleReflection hA i φ ∈ L.weightLattice := by
  rw [L.weightLattice_def] at hφ ⊢
  rw [R.simpleReflection_eq_dualMap hA i]
  exact Submodule.dualMap_mem_dualLattice L.lattice L.lattice
    (R.simpleCoreflection hA i).toLinearMap (fun _ ↦ L.simpleCoreflection_mem_lattice hA i) hφ

@[simp] theorem simpleReflection_mem_weightLattice_iff (hA : ∀ i, A.map (Int.cast : ℤ → ℚ) i i = 2)
    (i : I) (φ : Dual ℚ H) : R.simpleReflection hA i φ ∈ L.weightLattice ↔ φ ∈ L.weightLattice :=
  ⟨fun hφ ↦ R.simpleReflection_simpleReflection hA i φ ▸
      L.simpleReflection_mem_weightLattice hA i hφ,
    L.simpleReflection_mem_weightLattice hA i⟩

/-- The `ℤ`-linear simple coreflection of the coweight lattice `Y`. -/
noncomputable def coreflection (hA : ∀ i, A.map (Int.cast : ℤ → ℚ) i i = 2) (i : I) :
    L.lattice ≃ₗ[ℤ] L.lattice :=
  LinearEquiv.ofInvolutive
    (((R.simpleCoreflection hA i).toLinearMap.restrictScalars ℤ).restrict
      fun _ ↦ L.simpleCoreflection_mem_lattice hA i)
    fun y ↦ Subtype.ext (R.simpleCoreflection_simpleCoreflection hA i y)

/-- The `ℤ`-linear simple reflection of the weight lattice `P`. -/
noncomputable def reflection (hA : ∀ i, A.map (Int.cast : ℤ → ℚ) i i = 2) (i : I) :
    L.weightLattice ≃ₗ[ℤ] L.weightLattice :=
  LinearEquiv.ofInvolutive
    (((R.simpleReflection hA i).toLinearMap.restrictScalars ℤ).restrict
      fun _ ↦ L.simpleReflection_mem_weightLattice hA i)
    fun φ ↦ Subtype.ext (R.simpleReflection_simpleReflection hA i φ)

@[simp] theorem coe_coreflection_apply (hA : ∀ i, A.map (Int.cast : ℤ → ℚ) i i = 2) (i : I)
    (y : L.lattice) : (L.coreflection hA i y : H) = R.simpleCoreflection hA i y := (rfl)

@[simp] theorem coe_reflection_apply (hA : ∀ i, A.map (Int.cast : ℤ → ℚ) i i = 2) (i : I)
    (φ : L.weightLattice) : (L.reflection hA i φ : Dual ℚ H) = R.simpleReflection hA i φ := (rfl)

@[simp] theorem coreflection_symm (hA : ∀ i, A.map (Int.cast : ℤ → ℚ) i i = 2) (i : I) :
    (L.coreflection hA i).symm = L.coreflection hA i := (rfl)

@[simp] theorem reflection_symm (hA : ∀ i, A.map (Int.cast : ℤ → ℚ) i i = 2) (i : I) :
    (L.reflection hA i).symm = L.reflection hA i := (rfl)

/-- The lattice reflections preserve the integral weight–coweight pairing `P × Y → ℤ`. -/
@[simp] theorem pairing_reflection_coreflection (hA : ∀ i, A.map (Int.cast : ℤ → ℚ) i i = 2) (i : I)
    (φ : L.weightLattice) (y : L.lattice) :
    L.pairing (L.reflection hA i φ) (L.coreflection hA i y) = L.pairing φ y := by
  apply Int.cast_injective (α := ℚ)
  simp

end CoweightLattice

end TauCeti.CartanRealization

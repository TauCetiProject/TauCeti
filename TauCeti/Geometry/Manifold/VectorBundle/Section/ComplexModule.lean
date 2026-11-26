/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Algebra.ComplexSmoothFunctions
public import TauCeti.Geometry.Manifold.VectorBundle.Complexification
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Module
public import TauCeti.LinearAlgebra.Complex.Module
public import TauCeti.RingTheory.Derivation.DifferentialOperator
import Mathlib.Geometry.Manifold.BumpFunction

/-!
# Sections of complex bundles as modules over complex-valued functions

Let `V` be a complex vector bundle over a real manifold `M`, and let
`A_ℂ = C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯` be the complex-valued `C^n` functions on `M`, where differentiability
is taken over `ℝ`, so they are not required to be holomorphic. Pointwise multiplication makes
the `C^n` sections of `V` an `A_ℂ`-module (`ContMDiffSection.instModuleContMDiffMapOfNormedAlgebra`,
for the extension `ℝ ⊆ ℂ`). This is the module on which complex differential operators between
complex bundles over a real base act, in the same way as `ContMDiffSection.instModuleContMDiffMap`
makes sections of a real bundle a module over the real functions. This file relates the
`A_ℂ`-action to the complex structure of the fibres and to complexification.

Complex scalars act through constant functions and real functions through their complex
inclusion. Writing `J s = I • s` for fibrewise multiplication by `i`, a function
`u + i v` acts by `(u + i v) • s = u • s + v • J s`
(`ContMDiffSection.smul_eq_re_smul_add_im_smul_I_smul`). On the complexification `ℂ ⊗[ℝ] E` of a
real bundle `E`, the real and imaginary parts of `(u + i v) • σ` are `u Re σ - v Im σ` and
`u Im σ + v Re σ`. On a real section `s`, this reads
`(u + i v) • (1 ⊗ s) = 1 ⊗ (u • s) + i ⊗ (v • s)`
(`ContMDiffSection.smul_function_oneTmulLinearMap_of_normedAlgebra`). The identification of
`ℂ ⊗[ℝ] Γ(E)` with the sections of `ℂ ⊗[ℝ] E` intertwines the real function actions.

A complex differential operator between sections of complex bundles, of finite order in
Grothendieck's sense for commutators with multiplication by elements of `A_ℂ`, is local: `P s`
vanishes near every point near which `s` vanishes
(`TauCeti.complexDifferentialOperators_section_apply_eq_zero_of_eventuallyEq`). In particular an
`A_ℂ`-linear operator is local (`TauCeti.apply_eq_zero_of_map_smul`).

## References

* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, Springer
  (1993), §10.
* D. Huybrechts, *Complex Geometry: An Introduction*, Springer (2005), §1.2.
-/

public section

noncomputable section

open Bundle TopologicalSpace
open scoped Manifold ContDiff TensorProduct

namespace ContMDiffSection

/-! ### Complex-valued functions on real manifolds -/

section Complex

open TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  {n : ℕ∞ω} {V : M → Type*} [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [∀ x, AddCommGroup (V x)] [∀ x, Module ℂ (V x)] [VectorBundle ℂ F V]

/-- Complex scalars, acting on complex-valued functions through constant functions, and these
functions form a tower on sections. -/
instance instIsScalarTowerComplexContMDiffMap :
    IsScalarTower ℂ C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ Cₛ^n⟮I; F, V⟯ where
  smul_assoc c f s := by ext x; simp [mul_smul]

/-- A constant complex function acts on sections by complex scalar multiplication. -/
@[simp]
theorem complexSmoothConstants_smul (z : ℂ) (s : Cₛ^n⟮I; F, V⟯) :
    (complexSmoothConstants z : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) • s = z • s :=
  ext fun x ↦ by simp

variable [∀ x, Module ℝ (V x)] [VectorBundle ℝ F V] [∀ x, IsScalarTower ℝ ℂ (V x)]

/-- A real function, viewed as a complex function, acts on sections by the real function
action. -/
@[simp]
theorem ofReal_smul (f : C^n⟮I, M; ℝ⟯) (s : Cₛ^n⟮I; F, V⟯) :
    ContMDiffMap.ofReal f • s = f • s :=
  ext fun x ↦ by simpa using algebraMap_smul ℂ (f x) (s x)

/-- A complex function `u + i v` acts on a section by `u • s + v • (i • s)`, where `u` and `v`
act through the real function action. -/
theorem smul_eq_re_smul_add_im_smul_I_smul (f : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) (s : Cₛ^n⟮I; F, V⟯) :
    f • s = f.re • s + f.im • (Complex.I • s) := by
  ext x
  simp [ContMDiffMap.re_apply, ContMDiffMap.im_apply]

end Complex

/-! ### Sections of a complexified real bundle -/

section Complexification

open TauCeti

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners ℝ EB HB} {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ∞ω}
  {E : B → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℝ (E x)]
  [TopologicalSpace (TotalSpace F E)] [∀ x, TopologicalSpace (E x)] [FiberBundle F E]
  [VectorBundle ℝ F E] [∀ x, TopologicalSpace (ℂ ⊗[ℝ] E x)] [∀ x, IsComplexificationTopology (E x)]

/-- The real part of `(u + i v) • σ` is `u • Re σ - v • Im σ`. -/
@[simp]
theorem realPartLinearMap_smul_function_of_normedAlgebra (f : C^n⟮IB, B; 𝓘(ℝ, ℂ), ℂ⟯)
    (σ : Cₛ^n⟮IB; Complexification F, fun x ↦ ℂ ⊗[ℝ] E x⟯) :
    realPartLinearMap IB F n E (f • σ) =
      f.re • realPartLinearMap IB F n E σ - f.im • imaginaryPartLinearMap IB F n E σ :=
  ext fun x ↦ by simp [ContMDiffMap.re_apply, ContMDiffMap.im_apply]

/-- The imaginary part of `(u + i v) • σ` is `u • Im σ + v • Re σ`. -/
@[simp]
theorem imaginaryPartLinearMap_smul_function_of_normedAlgebra (f : C^n⟮IB, B; 𝓘(ℝ, ℂ), ℂ⟯)
    (σ : Cₛ^n⟮IB; Complexification F, fun x ↦ ℂ ⊗[ℝ] E x⟯) :
    imaginaryPartLinearMap IB F n E (f • σ) =
      f.re • imaginaryPartLinearMap IB F n E σ + f.im • realPartLinearMap IB F n E σ :=
  ext fun x ↦ by simp [ContMDiffMap.re_apply, ContMDiffMap.im_apply]

/-- Taking real parts commutes with the real function action. -/
@[simp]
theorem realPartLinearMap_smul_function (f : C^n⟮IB, B; ℝ⟯)
    (σ : Cₛ^n⟮IB; Complexification F, fun x ↦ ℂ ⊗[ℝ] E x⟯) :
    realPartLinearMap IB F n E (f • σ) = f • realPartLinearMap IB F n E σ :=
  ext fun x ↦ by simp

/-- Taking imaginary parts commutes with the real function action. -/
@[simp]
theorem imaginaryPartLinearMap_smul_function (f : C^n⟮IB, B; ℝ⟯)
    (σ : Cₛ^n⟮IB; Complexification F, fun x ↦ ℂ ⊗[ℝ] E x⟯) :
    imaginaryPartLinearMap IB F n E (f • σ) = f • imaginaryPartLinearMap IB F n E σ :=
  ext fun x ↦ by simp

/-- The real inclusion `s ↦ 1 ⊗ s` commutes with the real function action. -/
@[simp]
theorem oneTmulLinearMap_smul_function (f : C^n⟮IB, B; ℝ⟯) (s : Cₛ^n⟮IB; F, E⟯) :
    oneTmulLinearMap IB F n E (f • s) = f • oneTmulLinearMap IB F n E s :=
  ext fun x ↦ by simp [TensorProduct.tmul_smul]

/-- The imaginary inclusion `s ↦ i ⊗ s` commutes with the real function action. -/
@[simp]
theorem ITmulLinearMap_smul_function (f : C^n⟮IB, B; ℝ⟯) (s : Cₛ^n⟮IB; F, E⟯) :
    ITmulLinearMap IB F n E (f • s) = f • ITmulLinearMap IB F n E s :=
  ext fun x ↦ by simp [TensorProduct.tmul_smul]

/-- Multiplying the complexification `1 ⊗ s` of a real section by `u + i v` gives
`1 ⊗ (u • s) + i ⊗ (v • s)`. -/
theorem smul_function_oneTmulLinearMap_of_normedAlgebra (f : C^n⟮IB, B; 𝓘(ℝ, ℂ), ℂ⟯)
    (s : Cₛ^n⟮IB; F, E⟯) :
    f • oneTmulLinearMap IB F n E s =
      oneTmulLinearMap IB F n E (f.re • s) + ITmulLinearMap IB F n E (f.im • s) := by
  rw [smul_eq_re_smul_add_im_smul_I_smul, I_smul_oneTmulLinearMap, oneTmulLinearMap_smul_function,
    ITmulLinearMap_smul_function]

/-- The identification of `ℂ ⊗[ℝ] Γ(E)` with the sections of `ℂ ⊗[ℝ] E` carries the real
function action on the second tensor factor to the real function action on sections of
`ℂ ⊗[ℝ] E`. -/
theorem complexificationEquiv_tmul_smul_function (z : ℂ) (f : C^n⟮IB, B; ℝ⟯)
    (s : Cₛ^n⟮IB; F, E⟯) :
    complexificationEquiv IB F n E (z ⊗ₜ[ℝ] (f • s)) =
      f • complexificationEquiv IB F n E (z ⊗ₜ[ℝ] s) := by
  rw [complexificationEquiv_tmul_eq_smul, complexificationEquiv_tmul_eq_smul,
    oneTmulLinearMap_smul_function, ← ofReal_smul, ← ofReal_smul, smul_comm]

end Complexification

end ContMDiffSection

/-! ### Operators linear over complex-valued functions are local -/

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] {V : M → Type*}
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)] [FiberBundle F V]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)] [VectorBundle ℝ F V]
  [VectorBundle ℂ F V]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℂ F'] {W : M → Type*}
  [∀ x, TopologicalSpace (W x)] [TopologicalSpace (TotalSpace F' W)] [FiberBundle F' W]
  [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)] [∀ x, Module ℂ (W x)] [VectorBundle ℝ F' W]
  [VectorBundle ℂ F' W]

open scoped Topology

/-- **Complex differential operators between sections are local.** A complex-linear operator
`P : Γ(V) → Γ(W)` between sections of complex bundles which is a differential operator of order at
most `m` in Grothendieck's sense, for commutators with multiplication by complex-valued smooth
functions, is local: `P s` vanishes at every point near which `s` vanishes. -/
theorem complexDifferentialOperators_section_apply_eq_zero_of_eventuallyEq {m : ℕ}
    {P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℂ] Cₛ^∞⟮I; F', W⟯}
    (hP : P ∈ differentialOperators ℂ C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ m)
    {s : Cₛ^∞⟮I; F, V⟯} {x : M} (hs : ∀ᶠ y in 𝓝 x, s y = 0) :
    P s x = 0 := by
  -- A bump function `ρ` at `x` supported where `s = 0` has `ρ s = 0` and `ρ(x) = 1`.
  obtain ⟨ρ, -, hρ⟩ := (SmoothBumpFunction.nhds_basis_support (I := I) hs).mem_iff.mp hs
  set g : C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ := ContMDiffMap.ofReal ⟨ρ, ρ.contMDiff⟩
  -- `ofReal_apply`, up to the coercion of the bundled bump function `⟨ρ, _⟩`, which is `ρ`.
  have hg (y : M) : g y = ρ y := ContMDiffMap.ofReal_apply _ y
  have hgs : g • s = 0 := by
    ext y
    by_cases hy : ρ y = 0
    · simp [hg, hy]
    · simp [show s y = 0 from hρ hy]
  -- `0 = P (g s) = [P, g] s + g P s`, and the commutator `[P, g]` has lower order, so it vanishes
  -- at `x` by induction, while `g x = 1`.
  induction m generalizing P with
  | zero =>
    have hx := congrArg (· x) (mem_differentialOperators_zero_iff.1 hP g s)
    simpa [hgs, hg, ρ.eq_one] using hx.symm
  | succ m ih =>
    have hx := congrArg (· x) (apply_smul_eq_smulCommutator_add g P s)
    simp only [hgs, map_zero, ContMDiffSection.coe_add, Pi.add_apply,
      ContMDiffSection.smul_apply_of_normedAlgebra, hg, ρ.eq_one,
      ih (smulCommutator_mem_differentialOperators hP g)] at hx
    simpa using hx.symm

/-- An operator between sections of complex bundles which is linear over the complex-valued smooth
functions is local: `P s` vanishes at every point near which `s` vanishes. -/
theorem apply_eq_zero_of_map_smul {P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℂ] Cₛ^∞⟮I; F', W⟯}
    (hP : ∀ (f : C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) s, P (f • s) = f • P s)
    {s : Cₛ^∞⟮I; F, V⟯} {x : M} (hs : ∀ᶠ y in 𝓝 x, s y = 0) :
    P s x = 0 :=
  complexDifferentialOperators_section_apply_eq_zero_of_eventuallyEq (m := 0)
    (mem_differentialOperators_zero_iff.2 hP) hs

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Determinant.ComplexOrientation
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import TauCeti.LinearAlgebra.Complex.Finrank
import TauCeti.LinearAlgebra.Complex.Module

/-!
# Complex orientations of determinant lines of complex-linear maps

The real determinant line `det E` of a finite-dimensional complex vector space carries the complex
orientation `TauCeti.IsComplexPositive`, preserved by complex-linear isomorphisms
(`TauCeti.isComplexPositive_detLineCongr_iff`). This file computes the effect of isomorphisms
anticommuting with `I`, that is, conjugate-linear ones, and transfers the complex orientation to
the determinant line of a complex-linear map.

A conjugate-linear isomorphism `g` sends the pair `bᵢ, I • bᵢ` of a complex basis `b` to
`g bᵢ, -(I • g bᵢ)`, so it multiplies the complex orientation of `det E` by `(-1) ^ n`,
`n = finrank ℂ E` (`TauCeti.IsComplexPositive.neg_one_pow_smul_detLineCongr`); likewise for
`(det E)^*` and `det E ⊗ (det F)^*`.

The determinant line `det (ker f) ⊗ (det (coker f))^*` (`LinearMap.detLine`) of a complex-linear
map `f` is formed from the kernel and cokernel of the underlying real-linear map. These are the
complex kernel and cokernel with their real structures, and `LinearMap.detLineRestrictScalarsEquiv`
identifies the two forms. An element of the determinant line is complex positive
(`LinearMap.IsComplexPositiveDetLine`) if it corresponds to a complex positive element
(`TauCeti.IsComplexPositiveTMulDual`). Transport along a commuting square of real isomorphisms
(`LinearMap.detLineCongr`) preserves complex positivity when the isomorphisms commute with `I`
(`LinearMap.IsComplexPositiveDetLine.detLineCongr`), and multiplies it by `(-1) ^ (k + c)` when
they anticommute with `I`, where `k` and `c` are the complex dimensions of the kernel and the
cokernel (`LinearMap.IsComplexPositiveDetLine.neg_one_pow_smul_detLineCongr`). The sign is `(-1)`
to the complex index `k - c`.

In Seiberg–Witten theory this is the complex factor of the determinant sign of charge
conjugation: the quaternionic structure of the spinors is a conjugate-linear intertwiner of the
Dirac operators of a `Spinᶜ` structure and of its conjugate, so it contributes `(-1)` to the
complex index of the Dirac operator. Charge conjugation negates both the domain and the target of
the real deformation operator on imaginary forms; that contributes `(-1)` to the sum of the
dimensions of its kernel and cokernel (`LinearMap.detLineCongr_neg_apply`).

## Main definitions

* `LinearMap.kerRestrictScalarsEquiv`, `LinearMap.cokerRestrictScalarsEquiv`: the kernel and
  cokernel of a complex-linear map are those of the underlying real-linear map.
* `LinearMap.detLineRestrictScalarsEquiv`: the corresponding isomorphism of real determinant
  lines.
* `LinearMap.IsComplexPositiveDetLine`: the complex orientation of the determinant line of a
  complex-linear map.

## Main results

* `TauCeti.IsComplexPositive.neg_one_pow_smul_detLineCongr`,
  `TauCeti.IsComplexPositiveDual.neg_one_pow_smul_comp_detLineCongr`,
  `TauCeti.IsComplexPositiveTMulDual.neg_one_pow_smul_congr_detLineCongr`: conjugate-linear
  isomorphisms multiply complex orientations by `(-1)` to the complex dimension.
* `LinearMap.IsComplexPositiveDetLine.detLineCongr`: complex-linear transport preserves the
  complex orientation of the determinant line of a complex-linear map.
* `LinearMap.IsComplexPositiveDetLine.neg_one_pow_smul_detLineCongr`: conjugate-linear transport
  multiplies it by `(-1) ^ (k + c)`.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  AMS Colloquium Publications 52, 2012, Section A.2 (determinant line bundles).
* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds*, Mathematical Notes 44, Princeton University Press, 1996.
-/

public section

noncomputable section

open Module TensorProduct Complex

namespace TauCeti

variable {E F : Type*} [AddCommGroup E] [Module ℂ E] [Module ℝ E] [IsScalarTower ℝ ℂ E]
  [AddCommGroup F] [Module ℂ F] [Module ℝ F] [IsScalarTower ℝ ℂ F]

/-! ### Conjugate-linear isomorphisms -/

omit [IsScalarTower ℝ ℂ E] [IsScalarTower ℝ ℂ F] in
/-- A real-linear map anticommuting with `I` maps the real family `(v₀, I • v₀, v₁, …)` underlying
`v` to that underlying `g ∘ v` with every second vector negated, so their exterior products differ
by `(-1) ^ n`. -/
private theorem ιMulti_comp_complexToRealFamily_of_map_I_smul {n : ℕ} (g : E →ₗ[ℝ] F)
    (hg : ∀ x, g (I • x) = -(I • g x)) (v : Fin n → E) :
    ExteriorAlgebra.ιMulti ℝ (2 * n) (g ∘ complexToRealFamily v) =
      (-1 : ℝ) ^ n • ExteriorAlgebra.ιMulti ℝ (2 * n) (complexToRealFamily (g ∘ v)) := by
  set s : Fin (2 * n) → ℝ := fun j ↦ if ((complexRealIndexEquiv n).symm j).2 = 0 then 1 else -1
  have hv : g ∘ complexToRealFamily v = fun j ↦ s j • complexToRealFamily (g ∘ v) j := by
    funext j
    obtain ⟨⟨i, k⟩, rfl⟩ := (complexRealIndexEquiv n).surjective j
    fin_cases k <;> simp [s, hg]
  have hs : ∏ j, s j = (-1) ^ n := by
    rw [← (complexRealIndexEquiv n).prod_comp, Fintype.prod_prod_type]
    simp [s, Fin.prod_univ_two]
  rw [hv, AlternatingMap.map_smul_univ, hs]

/-- A real-linear isomorphism anticommuting with `I`, that is, a conjugate-linear isomorphism,
maps a complex basis to a complex basis. -/
private theorem exists_basis_coe_eq_comp_of_map_I_smul [FiniteDimensional ℂ F] {n : ℕ}
    (g : E ≃ₗ[ℝ] F) (hg : ∀ x, g (I • x) = -(I • g x)) (b : Basis (Fin n) ℂ E) :
    ∃ b' : Basis (Fin n) ℂ F, ⇑b' = g ∘ b := by
  have hconj := g.toLinearMap.map_smul_eq_conj_smul_of_map_I_smul hg
  have hli : LinearIndependent ℂ (g ∘ b) :=
    b.linearIndependent.map_of_injective_injectiveₛ (starRingEnd ℂ) g.toAddEquiv.toAddMonoidHom
      (RingHom.injective _) g.injective fun r m ↦ by simpa using hconj (starRingEnd ℂ r) m
  have hn : Fintype.card (Fin n) = finrank ℂ F := by
    rw [← g.finrank_complex_eq, finrank_eq_card_basis b]
  exact ⟨basisOfLinearIndependentOfCardEqFinrank' _ hli hn, by simp⟩

/-- **A conjugate-linear isomorphism reverses the complex orientation `(-1) ^ n` times**: the
isomorphism of real determinant lines induced by a real-linear isomorphism `g` anticommuting with
`I` maps a complex positive element to `(-1) ^ n` times a complex positive element,
`n = finrank ℂ E`. -/
theorem IsComplexPositive.neg_one_pow_smul_detLineCongr [FiniteDimensional ℂ E]
    [FiniteDimensional ℂ F] {x : detLine ℝ E} (hx : IsComplexPositive x) (g : E ≃ₗ[ℝ] F)
    (hg : ∀ x, g (I • x) = -(I • g x)) :
    IsComplexPositive ((-1 : ℝ) ^ finrank ℂ E • LinearEquiv.detLineCongr g x) := by
  set b := finBasis ℂ E
  obtain ⟨c, hc, hx⟩ := (isComplexPositive_iff b).1 hx
  obtain ⟨b', hb'⟩ := exists_basis_coe_eq_comp_of_map_I_smul g hg b
  refine (isComplexPositive_iff b').2 ⟨c, hc, ?_⟩
  rw [Submodule.coe_smul, LinearEquiv.coe_detLineCongr, hx, map_smul,
    ExteriorAlgebra.map_apply_ιMulti, ιMulti_comp_complexToRealFamily_of_map_I_smul _ hg,
    smul_comm, smul_smul, smul_smul, mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq,
    one_pow, mul_one, hb']
  rfl

/-- Pulling a complex positive functional back along the isomorphism of real determinant lines
induced by a conjugate-linear isomorphism `g` gives `(-1) ^ n` times a complex positive functional,
`n = finrank ℂ F`. -/
theorem IsComplexPositiveDual.neg_one_pow_smul_comp_detLineCongr [FiniteDimensional ℂ E]
    [FiniteDimensional ℂ F] {φ : Dual ℝ (detLine ℝ E)} (hφ : IsComplexPositiveDual φ)
    (g : F ≃ₗ[ℝ] E) (hg : ∀ x, g (I • x) = -(I • g x)) :
    IsComplexPositiveDual
      ((-1 : ℝ) ^ finrank ℂ F • φ ∘ₗ (LinearEquiv.detLineCongr g).toLinearMap) := by
  obtain ⟨y, hy⟩ := exists_isComplexPositive (E := F)
  rw [hy.isComplexPositiveDual_iff, LinearMap.smul_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe, ← map_smul]
  exact (hy.neg_one_pow_smul_detLineCongr g hg).isComplexPositiveDual_iff.1 hφ

/-- The isomorphism `det E ⊗ (det F)^* ≃ det E' ⊗ (det F')^*` induced by conjugate-linear
isomorphisms `e₁ : E ≃ E'` and `e₂ : F ≃ F'`, the shape of `LinearMap.detLineCongr`, maps a
complex positive element to `(-1) ^ (m + n)` times a complex positive element, where `m` and `n`
are the complex dimensions of `E` and `F`. -/
theorem IsComplexPositiveTMulDual.neg_one_pow_smul_congr_detLineCongr {E' F' : Type*}
    [AddCommGroup E'] [Module ℂ E'] [Module ℝ E'] [IsScalarTower ℝ ℂ E']
    [AddCommGroup F'] [Module ℂ F'] [Module ℝ F'] [IsScalarTower ℝ ℂ F']
    [FiniteDimensional ℂ E] [FiniteDimensional ℂ F] [FiniteDimensional ℂ E']
    [FiniteDimensional ℂ F'] {t : detLine ℝ E ⊗[ℝ] Dual ℝ (detLine ℝ F)}
    (ht : IsComplexPositiveTMulDual t)
    (e₁ : E ≃ₗ[ℝ] E') (e₂ : F ≃ₗ[ℝ] F') (he₁ : ∀ x, e₁ (I • x) = -(I • e₁ x))
    (he₂ : ∀ y, e₂ (I • y) = -(I • e₂ y)) :
    IsComplexPositiveTMulDual ((-1 : ℝ) ^ (finrank ℂ E + finrank ℂ F) •
      TensorProduct.congr (LinearEquiv.detLineCongr e₁)
        (LinearEquiv.detLineCongr e₂).symm.dualMap t) := by
  obtain ⟨x, hx⟩ := exists_isComplexPositive (E := E)
  obtain ⟨φ, hφ⟩ := exists_isComplexPositiveDual (E := F)
  obtain ⟨c, hc, rfl⟩ := (hx.isComplexPositiveTMulDual_tmul hφ).exists_pos_smul_eq ht
  have he₂' (y : F') : e₂.symm (I • y) = -(I • e₂.symm y) := by
    rw [LinearEquiv.symm_apply_eq, map_neg, he₂, LinearEquiv.apply_symm_apply, neg_neg]
  have hφ' := hφ.neg_one_pow_smul_comp_detLineCongr e₂.symm he₂'
  rw [e₂.symm.finrank_complex_eq, ← LinearEquiv.detLineCongr_symm] at hφ'
  rw [map_smul, smul_comm, TensorProduct.congr_tmul, pow_add, ← smul_tmul_smul]
  exact ((hx.neg_one_pow_smul_detLineCongr e₁ he₁).isComplexPositiveTMulDual_tmul hφ').smul hc

end TauCeti

namespace LinearMap

open TauCeti

variable {M N : Type*} [AddCommGroup M] [Module ℂ M] [Module ℝ M] [IsScalarTower ℝ ℂ M]
  [AddCommGroup N] [Module ℂ N] [Module ℝ N] [IsScalarTower ℝ ℂ N] (f : M →ₗ[ℂ] N)

/-! ### The complex orientation of the determinant line of a complex-linear map -/

/-- The kernel of a complex-linear map, with its real structure, is the kernel of the underlying
real-linear map. -/
def kerRestrictScalarsEquiv : ker f ≃ₗ[ℝ] ker (f.restrictScalars ℝ) :=
  ((ker f).restrictScalarsEquiv ℝ).symm.restrictScalars ℝ

/-- The cokernel of a complex-linear map, with its real structure, is the cokernel of the
underlying real-linear map. -/
def cokerRestrictScalarsEquiv : (N ⧸ range (f.restrictScalars ℝ)) ≃ₗ[ℝ] N ⧸ range f :=
  (Submodule.quotEquivOfEq _ _ (range_restrictScalars f)).trans
    (Submodule.Quotient.restrictScalarsEquiv ℝ (range f))

@[simp]
theorem cokerRestrictScalarsEquiv_mk (y : N) :
    f.cokerRestrictScalarsEquiv (Submodule.Quotient.mk y) = Submodule.Quotient.mk y :=
  (rfl)

@[simp]
theorem cokerRestrictScalarsEquiv_symm_mk (y : N) :
    f.cokerRestrictScalarsEquiv.symm (Submodule.Quotient.mk y) = Submodule.Quotient.mk y :=
  (rfl)

/-- The real determinant line `det (ker f) ⊗ (det (coker f))^*` of a complex-linear map, formed
from the kernel and cokernel of the underlying real-linear map (`LinearMap.detLine`), is the one
formed from the complex kernel and cokernel with their real structures. -/
def detLineRestrictScalarsEquiv :
    (f.restrictScalars ℝ).detLine ≃ₗ[ℝ]
      TauCeti.detLine ℝ (ker f) ⊗[ℝ] Dual ℝ (TauCeti.detLine ℝ (N ⧸ range f)) :=
  TensorProduct.congr (LinearEquiv.detLineCongr f.kerRestrictScalarsEquiv.symm)
    (LinearEquiv.detLineCongr f.cokerRestrictScalarsEquiv.symm).dualMap

/-- An element of the real determinant line of a complex-linear map `f` is **complex positive** if
it corresponds to a complex positive element of `det (ker f) ⊗ (det (coker f))^*`, that is, to
`(b₀ ∧ I • b₀ ∧ ⋯) ⊗ φ` for a complex basis `b` of the kernel and a functional `φ` positive on
`c₀ ∧ I • c₀ ∧ ⋯` for complex bases `c` of the cokernel. These are the complex orientations of
the determinant lines of complex-linear Fredholm operators, such as complex Dirac and
Cauchy–Riemann operators. -/
def IsComplexPositiveDetLine (z : (f.restrictScalars ℝ).detLine) : Prop :=
  IsComplexPositiveTMulDual (f.detLineRestrictScalarsEquiv z)

/-- The determinant line of a complex-linear map with finite-dimensional kernel and cokernel has
a complex positive element. -/
theorem exists_isComplexPositiveDetLine [FiniteDimensional ℂ (ker f)]
    [FiniteDimensional ℂ (N ⧸ range f)] :
    ∃ z : (f.restrictScalars ℝ).detLine, f.IsComplexPositiveDetLine z := by
  obtain ⟨t, ht⟩ := exists_isComplexPositiveTMulDual (E := ker f) (F := N ⧸ range f)
  exact ⟨f.detLineRestrictScalarsEquiv.symm t, by simpa [IsComplexPositiveDetLine] using ht⟩

variable {f} in
/-- The negative of a complex positive element of the determinant line of a complex-linear map is
not complex positive. -/
theorem IsComplexPositiveDetLine.not_neg [FiniteDimensional ℂ (N ⧸ range f)]
    {z : (f.restrictScalars ℝ).detLine} (hz : f.IsComplexPositiveDetLine z) :
    ¬ f.IsComplexPositiveDetLine (-z) := by
  rw [IsComplexPositiveDetLine, map_neg f.detLineRestrictScalarsEquiv z]
  exact IsComplexPositiveTMulDual.not_neg hz

/-! ### Transport along commuting squares -/

section Transport

variable {M' N' : Type*} [AddCommGroup M'] [Module ℂ M'] [Module ℝ M'] [IsScalarTower ℝ ℂ M']
  [AddCommGroup N'] [Module ℂ N'] [Module ℝ N'] [IsScalarTower ℝ ℂ N'] {f' : M' →ₗ[ℂ] N'}
  (e₁ : M ≃ₗ[ℝ] M') (e₂ : N ≃ₗ[ℝ] N')
  (h : f'.restrictScalars ℝ ∘ₗ e₁.toLinearMap = e₂.toLinearMap ∘ₗ f.restrictScalars ℝ)

/-- The isomorphism of complex kernels induced by a commuting square of real isomorphisms. -/
private def kerCongrOfComp : ker f ≃ₗ[ℝ] ker f' :=
  f.kerRestrictScalarsEquiv.trans ((e₁.ofSubmodules _ _
    ((f.restrictScalars ℝ).map_ker_eq_ker_of_comp_eq e₁.surjective e₂.injective h)).trans
      f'.kerRestrictScalarsEquiv.symm)

private theorem coe_kerCongrOfComp_apply (x : ker f) :
    (kerCongrOfComp f e₁ e₂ h x : M') = e₁ x :=
  rfl

private theorem kerCongrOfComp_I_smul {s : ℂ} (he₁ : ∀ x, e₁ (I • x) = s • e₁ x) (x : ker f) :
    kerCongrOfComp f e₁ e₂ h (I • x) = s • kerCongrOfComp f e₁ e₂ h x :=
  Subtype.ext (by simp [coe_kerCongrOfComp_apply, he₁])

/-- The isomorphism of complex cokernels induced by a commuting square of real isomorphisms. -/
private def cokerCongrOfComp : (N ⧸ range f) ≃ₗ[ℝ] N' ⧸ range f' :=
  f.cokerRestrictScalarsEquiv.symm.trans ((Submodule.Quotient.equiv _ _ e₂
    ((f.restrictScalars ℝ).map_range_eq_range_of_comp_eq e₁.surjective h)).trans
      f'.cokerRestrictScalarsEquiv)

private theorem cokerCongrOfComp_mk (y : N) :
    cokerCongrOfComp f e₁ e₂ h (Submodule.Quotient.mk y) = Submodule.Quotient.mk (e₂ y) :=
  rfl

private theorem cokerCongrOfComp_I_smul {s : ℂ} (he₂ : ∀ y, e₂ (I • y) = s • e₂ y)
    (y : N ⧸ range f) :
    cokerCongrOfComp f e₁ e₂ h (I • y) = s • cokerCongrOfComp f e₁ e₂ h y := by
  induction y using Submodule.Quotient.induction_on with
  | H y => rw [← Submodule.Quotient.mk_smul, cokerCongrOfComp_mk, cokerCongrOfComp_mk, he₂,
      Submodule.Quotient.mk_smul]

/-- Under `LinearMap.detLineRestrictScalarsEquiv`, transport along a commuting square of real
isomorphisms is the isomorphism of determinant lines induced by the isomorphisms of complex
kernels and cokernels. -/
private theorem detLineRestrictScalarsEquiv_detLineCongr (z : (f.restrictScalars ℝ).detLine) :
    f'.detLineRestrictScalarsEquiv ((f.restrictScalars ℝ).detLineCongr e₁ e₂ h z) =
      TensorProduct.congr (LinearEquiv.detLineCongr (kerCongrOfComp f e₁ e₂ h))
        (LinearEquiv.detLineCongr (cokerCongrOfComp f e₁ e₂ h)).symm.dualMap
        (f.detLineRestrictScalarsEquiv z) := by
  induction z using TensorProduct.inductionOn with
  | add a b ha hb => simp only [LinearEquiv.map_add, ha, hb]
  | tmul x φ =>
    simp only [detLineCongr_tmul, detLineRestrictScalarsEquiv, TensorProduct.congr_tmul]
    congr 1
    · rw [← LinearEquiv.trans_apply, ← LinearEquiv.detLineCongr_trans, ← LinearEquiv.trans_apply,
        ← LinearEquiv.detLineCongr_trans]
      congr 2
    · refine LinearMap.ext fun w ↦ ?_
      rw [LinearEquiv.dualMap_apply, LinearEquiv.dualMap_apply, LinearEquiv.dualMap_apply,
        LinearMap.comp_apply, LinearEquiv.coe_coe, ← LinearEquiv.trans_apply,
        ← LinearEquiv.trans_apply, LinearEquiv.detLineCongr_symm, LinearEquiv.detLineCongr_symm,
        ← LinearEquiv.detLineCongr_trans, ← LinearEquiv.detLineCongr_trans]
      congr 3
      refine LinearEquiv.ext fun y ↦ ?_
      induction y using Submodule.Quotient.induction_on with
      | H y =>
        obtain ⟨y, rfl⟩ := e₂.surjective y
        simp [cokerCongrOfComp]

variable {f}

/-- Transport along a commuting square of real isomorphisms commuting with `I`, that is, of
complex-linear isomorphisms, preserves the complex orientation of the determinant line of a
complex-linear map. -/
theorem IsComplexPositiveDetLine.detLineCongr {z : (f.restrictScalars ℝ).detLine}
    (hz : f.IsComplexPositiveDetLine z) (he₁ : ∀ x, e₁ (I • x) = I • e₁ x)
    (he₂ : ∀ y, e₂ (I • y) = I • e₂ y) :
    f'.IsComplexPositiveDetLine ((f.restrictScalars ℝ).detLineCongr e₁ e₂ h z) := by
  set g₁ := kerCongrOfComp f e₁ e₂ h
  set g₂ := cokerCongrOfComp f e₁ e₂ h
  let G₁ : ker f ≃ₗ[ℂ] ker f' := .ofBijective
    (g₁.toLinearMap.complexOfMapISmul (kerCongrOfComp_I_smul f e₁ e₂ h he₁))
    (by simpa using g₁.bijective)
  let G₂ : (N ⧸ range f) ≃ₗ[ℂ] N' ⧸ range f' := .ofBijective
    (g₂.toLinearMap.complexOfMapISmul (cokerCongrOfComp_I_smul f e₁ e₂ h he₂))
    (by simpa using g₂.bijective)
  have hG₁ : G₁.restrictScalars ℝ = g₁ := LinearEquiv.ext fun _ ↦ by simp [G₁]
  have hG₂ : G₂.restrictScalars ℝ = g₂ := LinearEquiv.ext fun _ ↦ by simp [G₂]
  have := IsComplexPositiveTMulDual.congr_detLineCongr hz G₁ G₂
  rw [hG₁, hG₂] at this
  rw [IsComplexPositiveDetLine, detLineRestrictScalarsEquiv_detLineCongr]
  exact this

/-- **The determinant sign of a conjugate-linear transport.** Transport along a commuting square
of real isomorphisms anticommuting with `I`, that is, of conjugate-linear isomorphisms, maps a
complex positive element of the determinant line of `f` to `(-1) ^ (k + c)` times a complex
positive element of the determinant line of `f'`, where `k` and `c` are the complex dimensions of
the kernel and the cokernel of `f`. The sign is `(-1)` to the complex index `k - c`. -/
theorem IsComplexPositiveDetLine.neg_one_pow_smul_detLineCongr [FiniteDimensional ℂ (ker f)]
    [FiniteDimensional ℂ (N ⧸ range f)] [FiniteDimensional ℂ (ker f')]
    [FiniteDimensional ℂ (N' ⧸ range f')] {z : (f.restrictScalars ℝ).detLine}
    (hz : f.IsComplexPositiveDetLine z) (he₁ : ∀ x, e₁ (I • x) = -(I • e₁ x))
    (he₂ : ∀ y, e₂ (I • y) = -(I • e₂ y)) :
    f'.IsComplexPositiveDetLine ((-1 : ℝ) ^ (finrank ℂ (ker f) + finrank ℂ (N ⧸ range f)) •
      (f.restrictScalars ℝ).detLineCongr e₁ e₂ h z) := by
  have he₁' (x : M) : e₁ (I • x) = (-I) • e₁ x := by rw [he₁, neg_smul]
  have he₂' (y : N) : e₂ (I • y) = (-I) • e₂ y := by rw [he₂, neg_smul]
  rw [IsComplexPositiveDetLine, map_smul, detLineRestrictScalarsEquiv_detLineCongr]
  exact IsComplexPositiveTMulDual.neg_one_pow_smul_congr_detLineCongr hz _ _
    (fun x ↦ by rw [kerCongrOfComp_I_smul f e₁ e₂ h he₁' x, neg_smul])
    (fun y ↦ by rw [cokerCongrOfComp_I_smul f e₁ e₂ h he₂' y, neg_smul])

end Transport

end LinearMap

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.BilinearForm.DualLattice
public import Mathlib.NumberTheory.Real.Irrational
public import TauCeti.Algebra.Module.ZLattice.Basic
public import TauCeti.Analysis.InnerProductSpace.Nondegenerate

/-!
# The dual lattice in a real inner product space

For a `ℤ`-submodule `L` of a real inner product space `E`, the *dual lattice*

`L^∨ = {x ∈ E | ⟪x, y⟫ ∈ ℤ for all y ∈ L}`

is Mathlib's `BilinForm.dualSubmodule` of the inner product `innerₗ E`, with `ℤ` as
the ring of coefficients. This file names that submodule `ZLattice.dual` and develops the part of
its theory that holds for a full lattice in a finite-dimensional space: the dual of a full lattice
is again a full lattice (`ZLattice.dual` carries `DiscreteTopology` and `IsZLattice` instances),
and taking the dual twice gives the lattice back (`ZLattice.dual_dual`).

Both facts come from the dual-basis description of Mathlib: the dual of the `ℤ`-span of an
`ℝ`-basis `b` is the `ℤ`-span of the basis dual to `b` for the inner product
(`ZLattice.dual_span_basis`), and a full lattice is the `ℤ`-span of an `ℝ`-basis. In particular the
`ℤ`-span of an orthonormal basis is its own dual (`ZLattice.dual_span_orthonormalBasis`), the
self-duality of `ℤⁿ ⊆ ℝⁿ`.

The dual is antitone, and it commutes with pulling a lattice back along a linear isometry
equivalence (`ZLattice.dual_comap`), so every notion defined from it is an isometry invariant.
Along a general continuous linear equivalence `e` of complete spaces the dual is pulled back along
the adjoint of `e⁻¹` instead (`ZLattice.dual_comap_continuousLinearEquiv`): the dual of `A L` is
`(A⁻¹)ᵀ L^∨`, the transport of dual lattices under a linear change of variables.

This is the dual lattice entering Poisson summation over a lattice, and the integrality,
evenness and unimodularity of a lattice in `TauCeti/Algebra/Module/ZLattice/Integral.lean` are
defined from it.

## Main definitions

* `ZLattice.dual L`: the dual of `L : Submodule ℤ E` with respect to the inner product.
* `ZLattice.basisSpanOrthonormalBasis b`: an orthonormal basis `b` as a `ℤ`-basis of its
  `ℤ`-span.
* `ZLattice.dualComapEquiv L e`: the `ℤ`-linear equivalence `(e⁻¹ L)^∨ ≃ₗ[ℤ] L^∨` induced by a
  linear isometry equivalence `e`.

## Notation

* `L^∨`: the dual lattice `ZLattice.dual L`, scoped in `ZLattice`.

## Main statements

* `ZLattice.mem_dual`: `x ∈ dual L` if and only if `⟪x, y⟫` is an integer for every `y ∈ L`.
* `ZLattice.dual_span_basis`: the dual of the `ℤ`-span of an `ℝ`-basis is the `ℤ`-span of its
  dual basis.
* `ZLattice.dual_span_orthonormalBasis`: the `ℤ`-span of an orthonormal basis is self-dual.
* `ZLattice.dual_span_singleton`, `ZLattice.dual_span_inv`: the dual of `c ℤ ⊆ ℝ` (`c ≠ 0`) is
  `c⁻¹ ℤ`, and the dual of `c⁻¹ ℤ` is `c ℤ`.
* `ZLattice.span_natCast_lt_span_inv_natCast`, `ZLattice.dual_span_inv_natCast_lt`: for a natural
  number `n > 1`, `n ℤ < n⁻¹ ℤ` in `ℝ`, so `(n⁻¹ ℤ)^∨ = n ℤ` is strictly contained in `n⁻¹ ℤ`.
* `ZLattice.inf_dual_span_singleton_eq_bot_of_irrational_sq`: when `c²` is irrational, `c ℤ ⊆ ℝ`
  meets its dual `c⁻¹ ℤ` only at `0`.
* `ZLattice.dual_dual`: the dual of the dual of a full lattice is the lattice itself.
* `ZLattice.dual_comap`: the dual commutes with pulling back along a linear isometry equivalence.
* `ZLattice.dual_comap_continuousLinearEquiv`: the dual of the pullback along a continuous linear
  equivalence `e` is the pullback of the dual along the adjoint of `e⁻¹`.
-/

public section

open Module Submodule
open LinearMap (BilinForm)
open scoped RealInnerProductSpace

universe u

namespace ZLattice

variable {E : Type u} {F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The dual lattice of `L : Submodule ℤ E`: the vectors whose inner product with every vector of
`L` is an integer. It is Mathlib's `BilinForm.dualSubmodule` of the inner product. -/
noncomputable def dual (L : Submodule ℤ E) : Submodule ℤ E :=
  BilinForm.dualSubmodule (innerₗ E) L

@[inherit_doc] scoped notation:max L "^∨" => ZLattice.dual L

theorem dual_def (L : Submodule ℤ E) : dual L = BilinForm.dualSubmodule (innerₗ E) L :=
  (rfl)

/-- A vector lies in the dual lattice exactly when its inner product with every vector of `L` is
an integer. -/
@[simp]
theorem mem_dual {L : Submodule ℤ E} {x : E} : x ∈ dual L ↔ ∀ y ∈ L, ∃ m : ℤ, ⟪x, y⟫ = m := by
  simp only [dual_def, BilinForm.mem_dualSubmodule, Submodule.mem_one, innerₗ_apply_apply,
    algebraMap_int_eq, eq_intCast, eq_comm]

/-- Taking duals reverses inclusions. -/
theorem dual_anti {L M : Submodule ℤ E} (h : L ≤ M) : dual M ≤ dual L :=
  fun _ hx y hy ↦ hx y (h hy)

/-- `L` lies in the dual of `M` if and only if `M` lies in the dual of `L`: both say that `L` and
`M` pair integrally. -/
theorem le_dual_comm {L M : Submodule ℤ E} : L ≤ dual M ↔ M ≤ dual L := by
  have h : BilinForm.flip (innerₗ E) = innerₗ E := flip_innerₗ E
  rw [dual_def, dual_def, ← BilinForm.le_flip_dualSubmodule, h]

/-- Every lattice is contained in the dual of its dual. Equality holds for a full lattice in a
finite-dimensional space, `dual_dual`. -/
theorem le_dual_dual (L : Submodule ℤ E) : L ≤ dual (dual L) :=
  le_dual_comm.mpr le_rfl

/-- The dual of the `ℤ`-span of an `ℝ`-basis is the `ℤ`-span of the dual basis for the inner
product. -/
theorem dual_span_basis {ι : Type*} [Finite ι] [DecidableEq ι] (b : Basis ι ℝ E) :
    dual (span ℤ (Set.range b)) =
      span ℤ (Set.range (BilinForm.dualBasis (innerₗ E) TauCeti.nondegenerate_inner b)) :=
  BilinForm.dualSubmodule_span_of_basis (innerₗ E) TauCeti.nondegenerate_inner b

/-- The `ℤ`-span of an orthonormal basis is discrete, as the `ℤ`-span of the underlying basis
`b.toBasis` is. -/
instance instDiscreteTopologySpanOrthonormalBasis {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) : DiscreteTopology (span ℤ (Set.range b)) := by
  rw [← b.coe_toBasis]
  infer_instance

/-- The `ℤ`-span of an orthonormal basis is a full lattice, a copy of `ℤⁿ ⊆ ℝⁿ`. -/
instance instIsZLatticeSpanOrthonormalBasis {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) : IsZLattice ℝ (span ℤ (Set.range b)) where
  span_top := by
    rw [← b.coe_toBasis]
    exact IsZLattice.span_top

/-- An orthonormal basis `b` is a `ℤ`-basis of its `ℤ`-span `ℤ b`. -/
noncomputable def basisSpanOrthonormalBasis {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) : Basis ι ℤ (span ℤ (Set.range b)) :=
  (b.toBasis.restrictScalars ℤ).map (LinearEquiv.ofEq _ _ (by rw [b.coe_toBasis]))

/-- The `i`-th vector of the `ℤ`-basis `basisSpanOrthonormalBasis b` of `ℤ b` is `b i`. -/
@[simp]
theorem coe_basisSpanOrthonormalBasis_apply {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) (i : ι) : (basisSpanOrthonormalBasis b i : E) = b i := by
  simp only [basisSpanOrthonormalBasis, Basis.map_apply, LinearEquiv.coe_ofEq_apply,
    Basis.restrictScalars_apply]
  exact congrFun b.coe_toBasis i

/-- The `ℤ`-span of an orthonormal basis is its own dual. -/
@[simp]
theorem dual_span_orthonormalBasis {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) :
    dual (span ℤ (Set.range b)) = span ℤ (Set.range b) := by
  classical
  have hb :
      BilinForm.dualBasis (innerₗ E) TauCeti.nondegenerate_inner b.toBasis = ⇑b := by
    rw [BilinForm.dualBasis_eq_iff]
    intro i j
    rw [innerₗ_apply_apply, OrthonormalBasis.coe_toBasis, b.inner_eq_ite]
    simp only [eq_comm]
  rw [← b.coe_toBasis, dual_span_basis, hb, b.coe_toBasis]

/-- The dual of the rank-one lattice `c ℤ ⊆ ℝ` (`c ≠ 0`) is `c⁻¹ ℤ`. -/
theorem dual_span_singleton {c : ℝ} (hc : c ≠ 0) :
    dual (span ℤ {c} : Submodule ℤ ℝ) = span ℤ {c⁻¹} := by
  ext x
  refine ⟨fun hx ↦ ?_, fun hx ↦ mem_dual.mpr fun y hy ↦ ?_⟩
  · obtain ⟨m, hm⟩ := mem_dual.mp hx c (Submodule.mem_span_singleton_self c)
    rw [RCLike.inner_apply, conj_trivial] at hm
    refine Submodule.mem_span_singleton.mpr ⟨m, ?_⟩
    rw [zsmul_eq_mul, ← hm, mul_comm c x, mul_inv_cancel_right₀ hc]
  · obtain ⟨m, rfl⟩ := Submodule.mem_span_singleton.mp hx
    obtain ⟨n, rfl⟩ := Submodule.mem_span_singleton.mp hy
    refine ⟨m * n, ?_⟩
    rw [RCLike.inner_apply, conj_trivial, zsmul_eq_mul, zsmul_eq_mul, Int.cast_mul]
    calc (n : ℝ) * c * ((m : ℝ) * c⁻¹)
        = (m : ℝ) * (n : ℝ) * (c * c⁻¹) := by ring
      _ = (m : ℝ) * (n : ℝ) := by rw [mul_inv_cancel₀ hc, mul_one]

/-- The dual of the rank-one lattice `c⁻¹ ℤ ⊆ ℝ` (`c ≠ 0`) is `c ℤ`. -/
theorem dual_span_inv {c : ℝ} (hc : c ≠ 0) :
    dual (span ℤ {c⁻¹} : Submodule ℤ ℝ) = span ℤ {c} := by
  rw [dual_span_singleton (inv_ne_zero hc), inv_inv]

/-- For every natural number `n`, `n ℤ` is contained in `n⁻¹ ℤ` inside `ℝ`. -/
theorem span_natCast_le_span_inv_natCast (n : ℕ) :
    (span ℤ {(n : ℝ)} : Submodule ℤ ℝ) ≤ span ℤ {(n : ℝ)⁻¹} := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_span_singleton]
    refine ⟨n ^ 2, ?_⟩
    have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    rw [zsmul_eq_mul]
    push_cast
    rw [sq, mul_inv_cancel_right₀ hn']

/-- For a natural number `n > 1`, `n ℤ` is strictly contained in `n⁻¹ ℤ` inside `ℝ`. -/
theorem span_natCast_lt_span_inv_natCast {n : ℕ} (hn : 1 < n) :
    (span ℤ {(n : ℝ)} : Submodule ℤ ℝ) < span ℤ {(n : ℝ)⁻¹} := by
  refine lt_of_le_not_ge (span_natCast_le_span_inv_natCast n) fun h ↦ ?_
  obtain ⟨m, hm⟩ := Submodule.mem_span_singleton.mp (h (Submodule.mem_span_singleton_self _))
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have h1 : (m : ℝ) * (n : ℝ) ^ 2 = 1 := by
    rw [zsmul_eq_mul] at hm
    calc (m : ℝ) * (n : ℝ) ^ 2 = (m : ℝ) * (n : ℝ) * (n : ℝ) := by ring
      _ = (n : ℝ)⁻¹ * (n : ℝ) := by rw [hm]
      _ = 1 := inv_mul_cancel₀ hn0
  have h2 : m * (n : ℤ) ^ 2 = 1 := by exact_mod_cast h1
  have hn2 : (4 : ℤ) ≤ (n : ℤ) ^ 2 := by
    have : (2 : ℤ) ≤ n := by exact_mod_cast hn
    nlinarith
  rcases le_or_gt m 0 with hm0 | hm0 <;> nlinarith

/-- For a nonzero natural number `n`, the dual `n ℤ` of `n⁻¹ ℤ ⊆ ℝ` is contained in `n⁻¹ ℤ`. -/
theorem dual_span_inv_natCast_le {n : ℕ} (hn : n ≠ 0) :
    dual (span ℤ {(n : ℝ)⁻¹} : Submodule ℤ ℝ) ≤ span ℤ {(n : ℝ)⁻¹} := by
  rw [dual_span_inv (Nat.cast_ne_zero.mpr hn)]
  exact span_natCast_le_span_inv_natCast n

/-- For a natural number `n > 1`, the dual `n ℤ` of `n⁻¹ ℤ ⊆ ℝ` is strictly contained in
`n⁻¹ ℤ`. -/
theorem dual_span_inv_natCast_lt {n : ℕ} (hn : 1 < n) :
    dual (span ℤ {(n : ℝ)⁻¹} : Submodule ℤ ℝ) < span ℤ {(n : ℝ)⁻¹} := by
  rw [dual_span_inv (Nat.cast_ne_zero.mpr (by omega))]
  exact span_natCast_lt_span_inv_natCast hn

/-- When `c²` is irrational, the rank-one lattice `c ℤ ⊆ ℝ` meets its dual `c⁻¹ ℤ` only at `0`. -/
theorem inf_dual_span_singleton_eq_bot_of_irrational_sq {c : ℝ} (hc : Irrational (c ^ 2)) :
    (span ℤ {c} : Submodule ℤ ℝ) ⊓ dual (span ℤ {c}) = ⊥ := by
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hc ⟨0, by norm_num⟩
  rw [dual_span_singleton hc0, eq_bot_iff]
  intro x hx
  rw [Submodule.mem_inf, Submodule.mem_span_singleton, Submodule.mem_span_singleton] at hx
  obtain ⟨⟨m, rfl⟩, ⟨n, hn⟩⟩ := hx
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  exfalso
  refine hc ⟨(n : ℚ) / (m : ℚ), ?_⟩
  have hm' : (m : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hm
  have hmc : (m : ℝ) * c = (n : ℝ) * c⁻¹ := by simpa [zsmul_eq_mul] using hn.symm
  have hmc2 : (n : ℝ) = c ^ 2 * m := by
    calc
      (n : ℝ) = (n : ℝ) * c⁻¹ * c := (inv_mul_cancel_right₀ hc0 (n : ℝ)).symm
      _ = (m : ℝ) * c * c := by rw [← hmc]
      _ = c ^ 2 * m := by ring
  push_cast
  exact (div_eq_iff hm').mpr hmc2

/-- The dual commutes with pulling a lattice back along a linear isometry equivalence. -/
@[simp]
theorem dual_comap (L : Submodule ℤ E) (e : F ≃ₗᵢ[ℝ] E) :
    dual (ZLattice.comap ℝ L e.toLinearEquiv.toLinearMap) =
      ZLattice.comap ℝ (dual L) e.toLinearEquiv.toLinearMap := by
  ext x
  simp only [mem_comap, mem_dual, LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv]
  refine ⟨fun h z hz ↦ ?_, fun h y hy ↦ e.inner_map_map x y ▸ h _ hy⟩
  obtain ⟨m, hm⟩ := h (e.symm z) (by rwa [e.apply_symm_apply])
  exact ⟨m, by rwa [← e.inner_map_map, e.apply_symm_apply] at hm⟩

/-- A linear isometry equivalence `e : F ≃ₗᵢ[ℝ] E` identifies the dual of the pullback of `L` with
the dual of `L`. -/
noncomputable def dualComapEquiv (L : Submodule ℤ E) (e : F ≃ₗᵢ[ℝ] E) :
    dual (ZLattice.comap ℝ L e.toLinearEquiv.toLinearMap) ≃ₗ[ℤ] dual L :=
  (LinearEquiv.ofEq _ _ (dual_comap L e)).trans
    ((e.toLinearEquiv.restrictScalars ℤ).ofSubmodule' (dual L))

/-- Applying `dualComapEquiv L e` applies `e` to the underlying vector. -/
@[simp]
theorem coe_dualComapEquiv_apply (L : Submodule ℤ E) (e : F ≃ₗᵢ[ℝ] E)
    (x : dual (ZLattice.comap ℝ L e.toLinearEquiv.toLinearMap)) :
    (dualComapEquiv L e x : E) = e x :=
  (rfl)

/-- Applying `(dualComapEquiv L e).symm` applies `e.symm` to the underlying vector. -/
@[simp]
theorem coe_dualComapEquiv_symm_apply (L : Submodule ℤ E) (e : F ≃ₗᵢ[ℝ] E) (y : dual L) :
    ((dualComapEquiv L e).symm y : F) = e.symm y :=
  (rfl)

/-- The dual of the pullback of a lattice along a continuous linear equivalence `e` is the
pullback of the dual along the adjoint of `e⁻¹`. Read through images, the dual of `A L` is
`(A⁻¹)ᵀ L^∨` for a linear automorphism `A`. -/
@[simp]
theorem dual_comap_continuousLinearEquiv [CompleteSpace E] [CompleteSpace F] (L : Submodule ℤ E)
    (e : F ≃L[ℝ] E) :
    dual (ZLattice.comap ℝ L e.toLinearMap) =
      ZLattice.comap ℝ (dual L) (ContinuousLinearMap.adjoint (e.symm : E →L[ℝ] F)).toLinearMap := by
  ext x
  simp only [mem_comap, mem_dual, LinearEquiv.coe_coe, ContinuousLinearEquiv.coe_toLinearEquiv,
    ContinuousLinearMap.coe_coe]
  refine ⟨fun h y hy ↦ ?_, fun h z hz ↦ ?_⟩
  · obtain ⟨m, hm⟩ := h (e.symm y) (by simpa using hy)
    exact ⟨m, by rwa [ContinuousLinearMap.adjoint_inner_left]⟩
  · obtain ⟨m, hm⟩ := h (e z) hz
    exact ⟨m, by simpa [ContinuousLinearMap.adjoint_inner_left] using hm⟩

section FiniteDimensional

variable [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]

instance : DiscreteTopology (dual L) := by
  obtain ⟨ι, _, _, b, rfl⟩ := exists_basis_span_eq ℝ L
  rw [dual_span_basis]
  infer_instance

instance : IsZLattice ℝ (dual L) where
  span_top := by
    obtain ⟨ι, _, _, b, rfl⟩ := exists_basis_span_eq ℝ L
    rw [dual_span_basis]
    exact ZSpan.span_top _

/-- The dual of the dual of a full lattice in a finite-dimensional space is the lattice. -/
@[simp]
theorem dual_dual : dual (dual L) = L := by
  obtain ⟨ι, _, _, b, rfl⟩ := exists_basis_span_eq ℝ L
  exact BilinForm.dualSubmodule_dualSubmodule_of_basis (innerₗ E)
    TauCeti.nondegenerate_inner (BilinForm.isSymm_iff.mpr isSymm_inner) b

end FiniteDimensional

end ZLattice

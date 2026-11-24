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
its theory that holds in a finite-dimensional space: the dual of a full lattice is again a full
lattice (`ZLattice.dual` carries `DiscreteTopology` and `IsZLattice` instances), and taking the
dual twice gives back every discrete lattice, full or not (`ZLattice.dual_dual`).

Both facts come from the dual-basis description of Mathlib: the dual of the `ℤ`-span of an
`ℝ`-basis `b` is the `ℤ`-span of the basis dual to `b` for the inner product
(`ZLattice.dual_span_basis`), and a full lattice is the `ℤ`-span of an `ℝ`-basis. In particular the
`ℤ`-span of an orthonormal basis is its own dual (`ZLattice.dual_span_orthonormalBasis`), the
self-duality of `ℤⁿ ⊆ ℝⁿ`. A discrete lattice that does not span is full in its real span `K`, and
every vector orthogonal to `K` lies in `L^∨` (`ZLattice.mem_dual_of_mem_orthogonal_span`) together
with all its real multiples, so no vector outside `K` lies in the dual of `L^∨`.

The dual is antitone, and it commutes with pulling a lattice back along a linear isometry
equivalence (`ZLattice.dual_comap`), so every notion defined from it is an isometry invariant.
Along a general continuous linear equivalence `e` of complete spaces the dual is pulled back along
the adjoint of `e⁻¹` instead (`ZLattice.dual_comap_continuousLinearEquiv`): the dual of `A L` is
`(A⁻¹)ᵀ L^∨`, the transport of dual lattices under a linear change of variables.

Duals taken inside a subspace `K` are slices of the ambient dual. The dual of the orthogonal
projection `π(L)` of any lattice to `K`, taken inside `K`, is `L^∨ ∩ K`
(`ZLattice.dual_map_orthogonalProjectionOnto`), and so is the dual of `L` inside `K` when `L ⊆ K`
(`ZLattice.dual_comap_subtype_of_le`). In particular a discrete lattice `L` is full in its real span
`W`, and `L^∨ ∩ W` is its dual there, again a full lattice in `W`, although `L^∨` itself contains
`Wᗮ` and need not be discrete.

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
* `ZLattice.dual_span_singleton`: the dual of `c ℤ ⊆ ℝ` (`c ≠ 0`) is `c⁻¹ ℤ`.
* `ZLattice.dual_span_one_half`, `ZLattice.span_two_lt_span_one_half`,
  `ZLattice.dual_span_one_half_lt`: the dual of `½ ℤ ⊆ ℝ` is `2 ℤ`, strictly contained in `½ ℤ`.
* `ZLattice.dual_span_singleton_le_self_iff`, `ZLattice.dual_span_singleton_lt_self_iff`:
  criteria on `c : ℝ` for `(c ℤ)^∨ ≤ c ℤ` and `(c ℤ)^∨ < c ℤ`.
* `ZLattice.inf_dual_span_singleton_eq_bot_of_irrational_sq`: when `c²` is irrational, `c ℤ ⊆ ℝ`
  meets its dual `c⁻¹ ℤ` only at `0`.
* `ZLattice.mem_dual_of_mem_orthogonal_span`: a vector orthogonal to `L` lies in `L^∨`.
* `ZLattice.dual_dual`: the dual of the dual of a discrete lattice in a finite-dimensional space is
  the lattice itself.
* `ZLattice.span_eq_top_of_finite_quotient_smul_submoduleOf_dual`,
  `ZLattice.span_eq_top_of_dual_le`: a lattice in a finite-dimensional space with finite quotient
  `L^∨ ⧸ (cL ∩ L^∨)` for some real `c` (in particular any lattice with `L^∨ ≤ L`) spans the space.
* `ZLattice.dual_comap`: the dual commutes with pulling back along a linear isometry equivalence.
* `ZLattice.dual_comap_continuousLinearEquiv`: the dual of the pullback along a continuous linear
  equivalence `e` is the pullback of the dual along the adjoint of `e⁻¹`.
* `ZLattice.dual_map_orthogonalProjectionOnto`: the dual of the orthogonal projection of `L` to a
  subspace `K`, taken inside `K`, is `L^∨ ∩ K`.
* `ZLattice.dual_comap_subtype_of_le`: for `L ⊆ K`, the dual of `L` taken inside `K` is
  `L^∨ ∩ K`.
* `ZLattice.instDiscreteTopologyComapDualSpanSubtype`,
  `ZLattice.instIsZLatticeComapDualSpanSubtype`: for a discrete lattice `L` in a
  finite-dimensional space, `L^∨ ∩ span ℝ L` is a full lattice in `span ℝ L`.

## References

* T. Horesh and Y. Karasik, *Equidistribution of primitive lattices in `ℝⁿ`*, Quart. J. Math. 74
  (2023), 1253–1294, DOI 10.1093/qmath/haad008, Proposition B.5, p.1291, with its pairing proof.
  This is the source of `ZLattice.dual_map_orthogonalProjectionOnto`.
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

/-- Every lattice is contained in the dual of its dual. Equality holds for a discrete lattice in a
finite-dimensional space, `dual_dual`. -/
theorem le_dual_dual (L : Submodule ℤ E) : L ≤ dual (dual L) :=
  le_dual_comm.mpr le_rfl

/-- The dual of the zero lattice is the whole space. -/
@[simp]
theorem dual_bot : dual (⊥ : Submodule ℤ E) = ⊤ :=
  eq_top_iff.mpr fun _ _ ↦ mem_dual.mpr fun y hy ↦ ⟨0, by simp [(mem_bot ℤ).mp hy]⟩

/-- A vector orthogonal to a lattice lies in its dual lattice, its inner products with the lattice
being `0`. -/
theorem mem_dual_of_mem_orthogonal_span {L : Submodule ℤ E} {x : E}
    (hx : x ∈ (span ℝ (L : Set E))ᗮ) : x ∈ dual L :=
  mem_dual.mpr fun _ hy ↦ ⟨0, by
    rw [Submodule.inner_left_of_mem_orthogonal (subset_span hy) hx, Int.cast_zero]⟩

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

/-- The dual of `c ℤ ⊆ ℝ` is contained in `c ℤ` if and only if `(m : ℝ) * c ^ 2 = 1` for some
`m : ℤ` (equivalently, `c ≠ 0` and `c⁻² ∈ ℤ`). -/
theorem dual_span_singleton_le_self_iff {c : ℝ} :
    dual (span ℤ {c} : Submodule ℤ ℝ) ≤ span ℤ {c} ↔
      ∃ m : ℤ, (m : ℝ) * c ^ 2 = 1 := by
  rcases eq_or_ne c 0 with rfl | hc
  · refine ⟨fun h ↦ ?_, fun ⟨m, hm⟩ ↦ by norm_num at hm⟩
    have h1 : (1 : ℝ) ∈ span ℤ {(0 : ℝ)} := h (by simp)
    rw [span_singleton_eq_bot.mpr rfl, mem_bot] at h1
    exact (one_ne_zero h1).elim
  · rw [dual_span_singleton hc, span_singleton_le_iff_mem, Submodule.mem_span_singleton]
    refine exists_congr fun m ↦ ?_
    rw [zsmul_eq_mul]
    exact ⟨fun h ↦ by linear_combination c * h + mul_inv_cancel₀ hc,
      fun h ↦ mul_right_cancel₀ hc (by linear_combination h - inv_mul_cancel₀ hc)⟩

/-- The dual of `c ℤ ⊆ ℝ` is strictly contained in `c ℤ` if and only if `(m : ℝ) * c ^ 2 = 1` for
some `m : ℤ` and `|c| ≠ 1`. -/
theorem dual_span_singleton_lt_self_iff {c : ℝ} :
    dual (span ℤ {c} : Submodule ℤ ℝ) < span ℤ {c} ↔
      (∃ m : ℤ, (m : ℝ) * c ^ 2 = 1) ∧ |c| ≠ 1 := by
  rw [lt_iff_le_not_ge, dual_span_singleton_le_self_iff]
  refine and_congr_right fun ⟨m, hm⟩ ↦ ?_
  have hc : c ≠ 0 := fun h0 ↦ by simp [h0] at hm
  refine not_congr ?_
  rw [dual_span_singleton hc, span_singleton_le_iff_mem, Submodule.mem_span_singleton,
    abs_eq zero_le_one, ← sq_eq_one_iff]
  refine ⟨fun ⟨k, hk⟩ ↦ ?_, fun hc2 ↦ ⟨1, ?_⟩⟩
  · have hkc : (k : ℝ) = c ^ 2 := by
      rw [zsmul_eq_mul] at hk
      calc (k : ℝ) = (k : ℝ) * c⁻¹ * c := (inv_mul_cancel_right₀ hc k).symm
        _ = c * c := by rw [hk]
        _ = c ^ 2 := (sq c).symm
    have hmk_real : (m : ℝ) * k = 1 := by rw [hkc, hm]
    have hmk : m * k = 1 := by exact_mod_cast hmk_real
    have hk0 : (0 : ℤ) < k := by exact_mod_cast (hkc ▸ sq_pos_of_ne_zero hc : (0 : ℝ) < k)
    have hk1 : k = 1 := Int.eq_one_of_mul_eq_one_left hk0.le hmk
    simpa [hk1] using hkc.symm
  · rw [one_smul]
    exact mul_left_cancel₀ hc (by rw [mul_inv_cancel₀ hc, ← sq, hc2])

/-- The dual of the rank-one lattice `½ ℤ ⊆ ℝ` is `2 ℤ`. -/
theorem dual_span_one_half :
    dual (span ℤ {1 / 2} : Submodule ℤ ℝ) = span ℤ {2} := by
  rw [dual_span_singleton (by norm_num)]
  norm_num

/-- In `ℝ`, `2 ℤ` is a proper sublattice of `½ ℤ`. -/
theorem span_two_lt_span_one_half :
    (span ℤ {2} : Submodule ℤ ℝ) < span ℤ {1 / 2} := by
  refine lt_of_le_not_ge
    (span_le.mpr (Set.singleton_subset_iff.mpr (mem_span_singleton.mpr ⟨4, ?_⟩))) fun h ↦ ?_
  · rw [zsmul_eq_mul]
    norm_num
  · obtain ⟨n, hn⟩ := mem_span_singleton.mp (h (mem_span_singleton_self (1 / 2)))
    rw [zsmul_eq_mul] at hn
    have h4 : (4 : ℝ) * n = 1 := by linarith
    have h4' : 4 * n = 1 := by exact_mod_cast h4
    omega

/-- The dual `2 ℤ` of `½ ℤ ⊆ ℝ` is strictly contained in `½ ℤ`. -/
theorem dual_span_one_half_lt :
    dual (span ℤ {1 / 2} : Submodule ℤ ℝ) < span ℤ {1 / 2} :=
  dual_span_one_half ▸ span_two_lt_span_one_half

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

section Subspace

variable (K : Submodule ℝ E)

/-- For a lattice `L` contained in a subspace `K`, the dual of `L` taken inside `K` is the
ambient dual `L^∨` intersected with `K`. -/
theorem dual_comap_subtype_of_le {L : Submodule ℤ E} (h : L ≤ K.restrictScalars ℤ) :
    dual (ZLattice.comap ℝ L K.subtype) = ZLattice.comap ℝ (dual L) K.subtype := by
  ext x
  simp only [mem_comap, mem_dual, Submodule.coe_subtype, Submodule.coe_inner]
  exact ⟨fun hx y hy ↦ hx ⟨y, h hy⟩ hy, fun hx y hy ↦ hx y hy⟩

/-- **The dual of a projected lattice.** For any `ℤ`-submodule `L` and the orthogonal projection
`π` onto a subspace `K`, the dual of `π(L)` taken inside `K` is the ambient dual `L^∨`
intersected with `K`: for `x ∈ K` and `y ∈ E`, `⟪x, π y⟫ = ⟪x, y⟫`. No discreteness or fullness
of `L` is needed. -/
@[simp]
theorem dual_map_orthogonalProjectionOnto (L : Submodule ℤ E) [K.HasOrthogonalProjection] :
    dual (L.map ((K.orthogonalProjectionOnto : E →ₗ[ℝ] K).restrictScalars ℤ)) =
      ZLattice.comap ℝ (dual L) K.subtype := by
  ext x
  simp only [mem_comap, mem_dual, Submodule.mem_map, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, LinearMap.coe_restrictScalars, ContinuousLinearMap.coe_coe,
    inner_orthogonalProjectionOnto_eq_of_mem_left, Submodule.coe_subtype]

end Subspace

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

omit [IsZLattice ℝ L] in
/-- The dual of the dual of a discrete lattice in a finite-dimensional space is the lattice. -/
@[simp]
theorem dual_dual : dual (dual L) = L := by
  -- The lattice is full in its real span `K`, where the dual-basis description applies.
  set K := span ℝ (L : Set E)
  let L' : Submodule ℤ K := ZLattice.comap ℝ L K.subtype
  have key : dual (dual L') = L' := by
    obtain ⟨ι, _, _, b, hb⟩ := exists_basis_span_eq ℝ L'
    rw [← hb]
    exact BilinForm.dualSubmodule_dualSubmodule_of_basis (innerₗ K)
      TauCeti.nondegenerate_inner (BilinForm.isSymm_iff.mpr isSymm_inner) b
  refine le_antisymm (fun y hy ↦ ?_) (le_dual_dual L)
  replace hy := mem_dual.mp hy
  -- `y` lies in `K`: a vector `u` orthogonal to `K` lies in `L^∨` with all its real multiples.
  have hyK : y ∈ K := by
    rw [← Submodule.orthogonal_orthogonal K, Submodule.mem_orthogonal]
    intro u hu
    by_contra h0
    obtain ⟨m, hm⟩ := hy ((2 * inner ℝ u y)⁻¹ • u)
      (mem_dual_of_mem_orthogonal_span (Submodule.smul_mem _ _ hu))
    rw [real_inner_smul_right, real_inner_comm u y] at hm
    have : (m : ℝ) * 2 = 1 := by
      rw [← hm]
      field_simp
    have : m * 2 = 1 := by exact_mod_cast this
    omega
  -- Then `y` lies in `dual (dual L') = L'`, since `L'^∨ = L^∨ ∩ K`.
  have hyL : (⟨y, hyK⟩ : K) ∈ L' := by
    rw [← key, mem_dual]
    intro z hz
    rw [dual_comap_subtype_of_le K subset_span] at hz
    obtain ⟨m, hm⟩ := hy z hz
    exact ⟨m, by simpa using hm⟩
  simpa using (ZLattice.mem_comap ℝ L K.subtype).mp hyL

end FiniteDimensional

section RealSpan

variable [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L]

/-- The ambient dual of a discrete subgroup `L`, intersected with the real span of `L`, is
discrete: it is the dual of `L` taken inside its span. The ambient dual itself need not be
discrete, as it contains the orthogonal complement of the span. -/
instance instDiscreteTopologyComapDualSpanSubtype :
    DiscreteTopology (ZLattice.comap ℝ (dual L) (span ℝ (L : Set E)).subtype) := by
  rw [← dual_comap_subtype_of_le _ subset_span]
  infer_instance

/-- The ambient dual of a discrete subgroup `L`, intersected with the real span of `L`, is a full
lattice in that span. -/
instance instIsZLatticeComapDualSpanSubtype :
    IsZLattice ℝ (ZLattice.comap ℝ (dual L) (span ℝ (L : Set E)).subtype) where
  span_top := by
    rw [← dual_comap_subtype_of_le _ subset_span]
    exact IsZLattice.span_top

end RealSpan

section Span

open scoped Pointwise

variable {L : Submodule ℤ E}

/-- A lattice in a finite-dimensional space with finite quotient `L^∨ ⧸ (cL ∩ L^∨)` (the quotient
by `cL` is taken through `submoduleOf`), for some real `c`, spans: the orthogonal complement of its
span lies in `L^∨` and meets `cL` only in `0`, so it would inject into the quotient. For `c = 1` the
quotient is the discriminant group `L^∨ ⧸ (L ∩ L^∨)`. -/
theorem span_eq_top_of_finite_quotient_smul_submoduleOf_dual [FiniteDimensional ℝ E] (c : ℝ)
    [Finite (dual L ⧸ (c • L).submoduleOf (dual L))] : span ℝ (L : Set E) = ⊤ := by
  by_contra h
  set K := span ℝ (L : Set E)
  have : Nontrivial Kᗮ :=
    Submodule.nontrivial_iff_ne_bot.mpr (by rwa [Ne, Submodule.orthogonal_eq_bot_iff])
  have : Infinite Kᗮ := Module.Free.infinite ℝ _
  have : Infinite (dual L ⧸ (c • L).submoduleOf (dual L)) := Infinite.of_injective
    (fun w : Kᗮ ↦ Submodule.Quotient.mk ⟨w, mem_dual_of_mem_orthogonal_span w.property⟩) fun a b hab
        ↦ by
    rw [Submodule.Quotient.eq, submoduleOf, Submodule.mem_comap, subtype_apply,
      mem_smul_pointwise_iff_exists] at hab
    obtain ⟨l, hl, hlab⟩ := hab
    -- `a - b = c • l` lies both in `K` and in `Kᗮ`, so it vanishes.
    have hK : (a : E) - b ∈ K := by
      simpa [hlab] using K.smul_mem c (subset_span hl : l ∈ K)
    have h0 := Submodule.inner_right_of_mem_orthogonal hK (sub_mem a.property b.property)
    rw [inner_self_eq_zero, sub_eq_zero] at h0
    exact Subtype.ext h0
  exact not_finite (dual L ⧸ (c • L).submoduleOf (dual L))

/-- If `L^∨ ≤ L` in a finite-dimensional space, then `L` spans the space over `ℝ`. -/
theorem span_eq_top_of_dual_le [FiniteDimensional ℝ E] (h : dual L ≤ L) :
    span ℝ (L : Set E) = ⊤ := by
  have : Subsingleton (dual L ⧸ ((1 : ℝ) • L).submoduleOf (dual L)) := by
    rw [one_smul, Submodule.Quotient.subsingleton_iff, submoduleOf_eq_top]
    exact h
  exact span_eq_top_of_finite_quotient_smul_submoduleOf_dual 1

end Span

end ZLattice

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Algebra.Module.ZLattice.Covolume
public import TauCeti.LinearAlgebra.IntegralLattice.Gram
public import TauCeti.LinearAlgebra.IntegralLattice.Signature

/-!
# The covolume of an integral lattice realized in Euclidean space

A *realization* of an integral lattice `L` in a real inner product space `E` is a `ℤ`-linear map
`φ : L → E` carrying the integral form to the inner product,
`⟪φ x, φ y⟫ = β(x, y)`, whose image spans `E` over `ℝ`. When `L` is nondegenerate, this file
proves that the image `φ(L)` is a `ℤ`-lattice in `E` (discrete and of full rank) and that its
covolume, for the volume measure of the inner product, satisfies

`covolume(φ(L))² = det L`, equivalently `covolume(φ(L)) = √(disc L)`.

This reconciles the analytic covolume of Mathlib's `ZLattice` with the algebraic determinant of
the lattice. The form of a realized lattice is the pullback of an inner product, so only positive
semidefinite lattices have realizations, and nondegeneracy is the hypothesis that rules out a
collapsing `φ`: the zero form on `ℤ`, realized by the zero map into the zero space, has
determinant `0` but covolume `1`.

Conversely every positive semidefinite lattice of rank `n` has a map to Euclidean space
`ℝⁿ` carrying its form to the inner product: diagonalize the rational form in an orthogonal
basis and rescale the coordinates by the square roots of its nonnegative diagonal values. For a
positive definite lattice the image spans, so every positive definite lattice has a realization;
this is what lets geometry-of-numbers arguments in `ℝⁿ` be applied to an abstract positive
definite lattice. In particular the determinant of a positive definite lattice is the square of a
covolume, hence positive.

## Main results

* `TauCeti.IntegralLattice.gram_comp_eq_map_gramMatrix`: the Gram matrix of the image of a carrier
  basis is the integral Gram matrix of the lattice.
* `TauCeti.IntegralLattice.injective_of_inner_eq`: a realization of a nondegenerate lattice is
  injective.
* `TauCeti.IntegralLattice.linearIndependent_comp_basis`: it carries carrier bases to
  `ℝ`-linearly independent families.
* `TauCeti.IntegralLattice.discreteTopology_range`: the image of a map carrying the integral form
  to the inner product is discrete; for a full realization it is a `ℤ`-lattice in `E`.
* `TauCeti.IntegralLattice.covolume_range_sq_eq_determinant`: `covolume(φ(L))² = det L`.
* `TauCeti.IntegralLattice.covolume_range_eq_sqrt_discriminant`: `covolume(φ(L)) = √(disc L)`.
* `TauCeti.IntegralLattice.IsPosSemidef.exists_inner_eq`: a positive semidefinite lattice maps to
  `ℝⁿ` with its form carried to the inner product.
* `TauCeti.IntegralLattice.IsPosDef.exists_realization`: a positive definite lattice has a
  realization in `ℝⁿ`.
* `TauCeti.IntegralLattice.IsPosDef.determinant_pos`: a positive definite lattice has positive
  determinant.

## References

* J. W. S. Cassels, *An Introduction to the Geometry of Numbers*, Chapter I, §2.
* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 1, §1.
-/

public section

open Module MeasureTheory
open scoped InnerProductSpace

namespace TauCeti.IntegralLattice

universe u

variable {V : Type u} [AddCommGroup V] [Module ℚ V] {L : IntegralLattice V}
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {φ : L →ₗ[ℤ] E}

section Gram

variable (hφ : ∀ x y : L, ⟪φ x, φ y⟫_ℝ = L.integralForm x y)
include hφ

/-- A map carrying the integral form to the inner product carries the integral Gram matrix of a
carrier basis to the real Gram matrix of its image. -/
theorem gram_comp_eq_map_gramMatrix {ι : Type*} (e : Basis ι ℤ L) :
    Matrix.gram ℝ (fun i ↦ φ (e i)) = (L.gramMatrix e).map ((↑) : ℤ → ℝ) := by
  ext i j
  simp [Matrix.gram_apply, hφ]

/-- A map carrying the integral form to the inner product carries every carrier basis to a family
whose Gram determinant is the determinant of the lattice. -/
theorem det_gram_comp_eq_determinant {ι : Type*} [Fintype ι] [DecidableEq ι] (e : Basis ι ℤ L) :
    (Matrix.gram ℝ (fun i ↦ φ (e i))).det = L.determinant := by
  rw [gram_comp_eq_map_gramMatrix hφ, ← Int.cast_det, ← gramDet_def, L.determinant_eq_gramDet e]

/-- The image of a map carrying the integral form to the inner product is discrete: its nonzero
vectors have integral squared norm, hence norm at least `1`. -/
theorem discreteTopology_range : DiscreteTopology (LinearMap.range φ) := by
  refine discreteTopology_of_isOpen_singleton_zero <| Metric.isOpen_singleton_iff.mpr
    ⟨1, one_pos, fun ⟨_, x, rfl⟩ hx ↦ Subtype.ext ?_⟩
  have hlt : (L.integralForm x x : ℝ) < 1 := by
    rw [← hφ, real_inner_self_eq_norm_sq]
    have h1 : ‖φ x‖ < 1 := by simpa using hx
    nlinarith [norm_nonneg (φ x)]
  have h0 : (0 : ℝ) ≤ L.integralForm x x := hφ x x ▸ real_inner_self_nonneg
  have hx0 : L.integralForm x x = 0 := by
    have : L.integralForm x x < 1 := by exact_mod_cast hlt
    have : 0 ≤ L.integralForm x x := by exact_mod_cast h0
    omega
  rw [ZeroMemClass.coe_zero, ← inner_self_eq_zero (𝕜 := ℝ), hφ, hx0, Int.cast_zero]

variable [L.IsNondegenerate]

/-- A map carrying the form of a nondegenerate lattice to the inner product is injective. -/
theorem injective_of_inner_eq : Function.Injective φ := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  refine ((nondegenerate_integralForm_iff L).mpr L.form_nondegenerate).1 x fun y ↦ ?_
  have h := hφ x y
  rw [hx, inner_zero_left] at h
  exact_mod_cast h.symm

/-- A map carrying the form of a nondegenerate lattice to the inner product carries every carrier
basis to an `ℝ`-linearly independent family. -/
theorem linearIndependent_comp_basis {ι : Type*} [Finite ι] (e : Basis ι ℤ L) :
    LinearIndependent ℝ (fun i ↦ φ (e i)) := by
  classical
  have := Fintype.ofFinite ι
  rw [← Matrix.det_gram_ne_zero_iff_linearIndependent, det_gram_comp_eq_determinant hφ]
  exact_mod_cast (determinant_ne_zero_iff L).mpr L.form_nondegenerate

variable (hspan : Submodule.span ℝ (Set.range φ) = ⊤)
include hspan

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- **The covolume identity.** The square of the covolume of a nondegenerate integral lattice,
realized in a real inner product space, is its determinant. -/
theorem covolume_range_sq_eq_determinant :
    ZLattice.covolume (LinearMap.range φ) ^ 2 = L.determinant := by
  classical
  have := discreteTopology_range hφ
  have : IsZLattice ℝ (LinearMap.range φ) := ⟨by rw [LinearMap.coe_range, hspan]⟩
  let e := Free.chooseBasis ℤ L
  rw [ZLattice.covolume_sq_eq_det_gram _ (e.map (LinearEquiv.ofInjective φ
    (injective_of_inner_eq hφ))), ← det_gram_comp_eq_determinant hφ e]
  simp

/-- The covolume of a nondegenerate integral lattice, realized in a real inner product space, is
the square root of its discriminant. -/
theorem covolume_range_eq_sqrt_discriminant :
    ZLattice.covolume (LinearMap.range φ) = √(L.discriminant : ℝ) := by
  have := discreteTopology_range hφ
  have : IsZLattice ℝ (LinearMap.range φ) := ⟨by rw [LinearMap.coe_range, hspan]⟩
  rw [discriminant_def, Nat.cast_natAbs, Int.cast_abs,
    ← covolume_range_sq_eq_determinant hφ hspan, abs_sq,
    Real.sqrt_sq (ZLattice.covolume_pos _ _).le]

end Gram

/-! ### Existence of realizations -/

/-- **A positive semidefinite lattice maps to Euclidean space by its form.** A positive
semidefinite integral lattice of rank `n` has a `ℤ`-linear map to `ℝⁿ` carrying its integral form
to the inner product. In an orthogonal basis of the rational form the map sends a vector to its
coordinates, rescaled by the square roots of the nonnegative diagonal values. -/
theorem IsPosSemidef.exists_inner_eq (hL : L.IsPosSemidef) :
    ∃ φ : L →ₗ[ℤ] EuclideanSpace ℝ (Fin (finrank ℤ L)),
      ∀ x y : L, ⟪φ x, φ y⟫_ℝ = L.integralForm x y := by
  classical
  have := L.finiteDimensional
  obtain ⟨v, hv⟩ := LinearMap.BilinForm.exists_orthogonal_basis
    (LinearMap.BilinForm.isSymm_iff.mp L.isSymm)
  set w := v.reindex (finCongr L.finrank_carrier.symm)
  have hw : ∀ i j, i ≠ j → L.form (w i) (w j) = 0 := fun i j hij ↦ by
    simpa [w] using hv (i := Fin.cast L.finrank_carrier i) (j := Fin.cast L.finrank_carrier j)
      (by simpa using hij)
  set d : Fin (finrank ℤ L) → ℝ := fun i ↦ √(L.form (w i) (w i) : ℝ)
  let φ : L →ₗ[ℤ] EuclideanSpace ℝ (Fin (finrank ℤ L)) :=
    { toFun x := WithLp.toLp 2 fun i ↦ d i * (w.repr x i : ℝ)
      map_add' x y := by ext i; simp [mul_add]
      map_smul' c x := by ext i; simp; ring }
  refine ⟨φ, fun x y ↦ ?_⟩
  -- In the orthogonal basis `w` the rational form is diagonal.
  have hexp : L.form x y = ∑ i, w.repr x i * w.repr y i * L.form (w i) (w i) := by
    conv_lhs => rw [← w.sum_repr (x : V), ← w.sum_repr (y : V)]
    simp only [LinearMap.BilinForm.sum_left, LinearMap.BilinForm.sum_right,
      LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Finset.sum_eq_single i (fun j _ hji ↦ by simp [hw _ _ hji]) (by simp)]
    ring
  have hd : ∀ i, d i * d i = L.form (w i) (w i) := fun i ↦
    Real.mul_self_sqrt (by exact_mod_cast L.isPosSemidef_iff.mp hL (w i))
  rw [← Rat.cast_intCast, L.integralForm_cast, hexp]
  simp only [φ, LinearMap.coe_mk, AddHom.coe_mk, PiLp.inner_apply, RCLike.inner_apply,
    conj_trivial, Rat.cast_sum, Rat.cast_mul]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← hd i]
  ring

/-- **A positive definite lattice has a realization.** A positive definite integral lattice of
rank `n` has a `ℤ`-linear map to `ℝⁿ` carrying its integral form to the inner product, whose
image spans `ℝⁿ`. -/
theorem IsPosDef.exists_realization (hL : L.IsPosDef) :
    ∃ φ : L →ₗ[ℤ] EuclideanSpace ℝ (Fin (finrank ℤ L)),
      (∀ x y : L, ⟪φ x, φ y⟫_ℝ = L.integralForm x y) ∧
        Submodule.span ℝ (Set.range φ) = ⊤ := by
  have : L.IsNondegenerate := ⟨(L.isPosDef_iff_isPosSemidef_and_nondegenerate.mp hL).2⟩
  obtain ⟨φ, hφ⟩ := hL.isPosSemidef.exists_inner_eq
  refine ⟨φ, hφ, eq_top_iff.mpr ?_⟩
  rw [← (linearIndependent_comp_basis hφ (finBasis ℤ L)).span_eq_top_of_card_eq_finrank'
    (by simp)]
  exact Submodule.span_mono (Set.range_comp_subset_range _ _)

/-- **A positive definite lattice has positive determinant**, the square of the covolume of any
of its realizations. -/
theorem IsPosDef.determinant_pos (hL : L.IsPosDef) : 0 < L.determinant := by
  have : L.IsNondegenerate := ⟨(L.isPosDef_iff_isPosSemidef_and_nondegenerate.mp hL).2⟩
  obtain ⟨φ, hφ, hspan⟩ := hL.exists_realization
  have := discreteTopology_range hφ
  have : IsZLattice ℝ (LinearMap.range φ) := ⟨by rw [LinearMap.coe_range, hspan]⟩
  have h := covolume_range_sq_eq_determinant hφ hspan
  exact_mod_cast h ▸ pow_pos (ZLattice.covolume_pos _ _) 2

end TauCeti.IntegralLattice

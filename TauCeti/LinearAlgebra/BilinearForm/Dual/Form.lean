/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.Dual.BaseChange
public import Mathlib.LinearAlgebra.PerfectPairing.Basic
public import TauCeti.LinearAlgebra.BilinearForm.BaseChange

/-!
# The dual of a bilinear form

A nondegenerate bilinear form `Q` on a finite-dimensional vector space `V` identifies `V` with its
dual by `Q♭ : x ↦ Q(x, ·)` (Mathlib's `LinearMap.BilinForm.toDual`). Transporting `Q` along `Q♭`
gives the **dual form** `Q^∨(ξ, η) = Q(Q♭⁻¹ ξ, Q♭⁻¹ η)` on `Module.Dual K V`
(`LinearMap.BilinForm.dualForm`). It is nondegenerate, alternating when `Q` is, and
`(c Q)^∨ = c⁻¹ Q^∨`.

For a lattice the dual form need not be integral. Let `Q` be a bilinear form on an `R`-module `Λ`
whose map `Q♭ : Λ → Hom(Λ, R)` is injective, and let `a ∈ R` kill the cokernel of `Q♭`, so that
`a η = Q♭ y_η` for a unique `y_η`. Then `(ξ, η) ↦ ξ(y_η)` is an integral form on `Hom(Λ, R)`
(`LinearMap.BilinForm.scaledDualForm`). For a base change `j : Λ → V` to a field `K`, it is
`a Q^∨` on the image of `Hom(Λ, R)` in `Module.Dual K V`
(`LinearMap.BilinForm.algebraMap_scaledDualForm`). For `R = ℤ` one may take for `a` the exponent
`e` of the finite group `Hom(Λ, ℤ)/Q♭(Λ)`, so `e Q^∨` is integral on `Hom(Λ, ℤ)`. When `Q` is
principal (a perfect pairing) one may take `a = 1`: `Q^∨` itself is integral, and it is perfect
(`LinearMap.BilinForm.isPerfPair_scaledDualForm_one`).

For `E = 2 E₀` with `E₀` the standard principal alternating form on `ℤ²`, the dual form takes the
value `1/2`, so it is not integral; here `e = 2`, and `2 E^∨ = E₀^∨` is principal
(`TauCeti.DualFormExamples.dualForm_E_eq_half`, `TauCeti.DualFormExamples.scaledDualForm_E_eq`).

## Main definitions

* `LinearMap.BilinForm.dualForm`: the dual form `Q^∨` of a nondegenerate form on a vector space.
* `LinearMap.BilinForm.scaledDualForm`: the integral form `a Q^∨` on `Hom(Λ, R)`, for `a` killing
  the cokernel of `Q♭`.

## Main results

* `LinearMap.BilinForm.dualForm_toDual_toDual`: `Q^∨(Q♭ x, Q♭ y) = Q(x, y)`.
* `LinearMap.BilinForm.comp_scaledDualPreimage`: `Q` pulls back along `η ↦ y_η` to `a` times
  the integral form `a Q^∨`.
* `LinearMap.BilinForm.algebraMap_scaledDualForm`: `a Q^∨` restricts to the integral form.
* `LinearMap.BilinForm.isPerfPair_scaledDualForm_one`: the dual form of a principal form is
  integral and principal.

## References

* Stanford VIGRE notes, *Complex theory of abelian varieties* (2004), Definitions 1.13–1.14 and
  Lemma 1.16, pp. 5–6, <https://math.stanford.edu/~conrad/vigregroup/vigre04/abvaran.pdf>: the
  dual form `Q^∨` and the integral rescaling `e Q^∨`.
-/

public section

namespace LinearMap.BilinForm

open Module

/-! ### The dual form over a field -/

section Field

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- The **dual form** `Q^∨(ξ, η) = Q(Q♭⁻¹ ξ, Q♭⁻¹ η)` of a nondegenerate bilinear form `Q` on a
finite-dimensional vector space `V`: the transport of `Q` to `Module.Dual K V` along
`Q♭ : x ↦ Q(x, ·)`. -/
noncomputable def dualForm (Q : LinearMap.BilinForm K V) (hQ : Q.Nondegenerate) :
    LinearMap.BilinForm K (Dual K V) :=
  congr (Q.toDual hQ) Q

variable {Q : LinearMap.BilinForm K V} (hQ : Q.Nondegenerate)

/-- The dual form evaluated through `Q♭⁻¹`. -/
theorem dualForm_apply (ξ η : Dual K V) :
    Q.dualForm hQ ξ η = Q ((Q.toDual hQ).symm ξ) ((Q.toDual hQ).symm η) :=
  (rfl)

/-- `Q^∨(Q♭ x, Q♭ y) = Q(x, y)`: the dual form is the transport of `Q` along `Q♭`. -/
@[simp]
theorem dualForm_toDual_toDual (x y : V) :
    Q.dualForm hQ (Q.toDual hQ x) (Q.toDual hQ y) = Q x y := by
  simp [dualForm_apply]

/-- `Q^∨(ξ, η) = ξ(Q♭⁻¹ η)`. -/
theorem dualForm_apply_eq (ξ η : Dual K V) :
    Q.dualForm hQ ξ η = ξ ((Q.toDual hQ).symm η) := by
  rw [dualForm_apply]
  exact apply_toDual_symm_apply ξ _

/-- `Q^∨(ξ, Q♭ y) = ξ(y)`. -/
theorem dualForm_apply_toDual_right (ξ : Dual K V) (y : V) :
    Q.dualForm hQ ξ (Q.toDual hQ y) = ξ y := by
  rw [dualForm_apply_eq, LinearEquiv.symm_apply_apply]

/-- The dual form of a nondegenerate form is nondegenerate. -/
theorem nondegenerate_dualForm : (Q.dualForm hQ).Nondegenerate :=
  hQ.congr (Q.toDual hQ)

/-- The dual form of an alternating form is alternating. -/
theorem IsAlt.dualForm (hQa : Q.IsAlt) : (Q.dualForm hQ).IsAlt :=
  fun ξ ↦ by rw [dualForm_apply]; exact hQa _

/-- The dual form of a symmetric form is symmetric. -/
theorem IsSymm.dualForm (hQs : Q.IsSymm) : (Q.dualForm hQ).IsSymm :=
  ⟨fun ξ η ↦ by rw [dualForm_apply, dualForm_apply, hQs.eq]⟩

/-- `(c Q)^∨ = c⁻¹ Q^∨`. -/
theorem dualForm_smul {c : K} (hc : c ≠ 0) (hcQ : (c • Q).Nondegenerate) :
    (c • Q).dualForm hcQ = c⁻¹ • Q.dualForm hQ := by
  have h (y : V) : (c • Q).toDual hcQ (c⁻¹ • y) = Q.toDual hQ y := by
    ext z
    simp [toDual_def, hc]
  refine LinearMap.ext₂ fun ξ η ↦ ?_
  obtain ⟨y, rfl⟩ := (Q.toDual hQ).surjective η
  rw [LinearMap.smul_apply, LinearMap.smul_apply, dualForm_apply_toDual_right, ← h,
    dualForm_apply_toDual_right, map_smul]

end Field

/-! ### The integral dual form of a lattice -/

section Lattice

variable {R Λ : Type*} [CommRing R] [AddCommGroup Λ] [Module R Λ]

variable (Q : LinearMap.BilinForm R Λ) (hQ : Function.Injective Q) (a : R)
  (ha : ∀ η : Dual R Λ, a • η ∈ LinearMap.range Q)

/-- For `a` killing the cokernel of the injective map `Q♭ : Λ → Hom(Λ, R)`, the map
`η ↦ y_η` with `Q♭ y_η = a η`. -/
noncomputable def scaledDualPreimage : Dual R Λ →ₗ[R] Λ :=
  (LinearEquiv.ofInjective Q hQ).symm.toLinearMap ∘ₗ
    (a • LinearMap.id : Dual R Λ →ₗ[R] Dual R Λ).codRestrict (LinearMap.range Q) ha

/-- `Q♭ y_η = a η`. -/
@[simp]
theorem apply_scaledDualPreimage (η : Dual R Λ) : Q (Q.scaledDualPreimage hQ a ha η) = a • η := by
  simp [scaledDualPreimage]

/-- The **integral form `a Q^∨`** on `Hom(Λ, R)`: for `a` killing the cokernel of the injective
map `Q♭ : Λ → Hom(Λ, R)`, it sends `(ξ, η)` to `ξ(y_η)`, where `Q♭ y_η = a η`. For `R = ℤ` and
`a` the exponent of the cokernel this is the integral polarizing form `e Q^∨` of the Stanford VIGRE
notes, Lemma 1.16 (see the module docstring); for `Q` principal and `a = 1` it is the dual form
itself. -/
noncomputable def scaledDualForm : LinearMap.BilinForm R (Dual R Λ) :=
  (LinearMap.applyₗ (R := R) (M := Λ) (M₂ := R)).flip.compl₂ (Q.scaledDualPreimage hQ a ha)

/-- `a Q^∨(ξ, η) = ξ(y_η)`. -/
theorem scaledDualForm_apply (ξ η : Dual R Λ) :
    Q.scaledDualForm hQ a ha ξ η = ξ (Q.scaledDualPreimage hQ a ha η) :=
  (rfl)

/-- `y_η` is characterized by `Q♭ y_η = a η`. -/
theorem scaledDualPreimage_eq_iff (η : Dual R Λ) (y : Λ) :
    Q.scaledDualPreimage hQ a ha η = y ↔ Q y = a • η :=
  ⟨fun h ↦ h ▸ Q.apply_scaledDualPreimage hQ a ha η,
    fun h ↦ hQ (by rw [apply_scaledDualPreimage, h])⟩

/-- On `Hom(Λ, R)`, the integral form `a Q^∨` is `(ξ, Q♭ y) ↦ a ξ(y)`. -/
@[simp]
theorem scaledDualForm_apply_right (ξ : Dual R Λ) (y : Λ) :
    Q.scaledDualForm hQ a ha ξ (Q y) = a * ξ y := by
  have hpre : Q.scaledDualPreimage hQ a ha (Q y) = a • y :=
    (Q.scaledDualPreimage_eq_iff hQ a ha _ _).mpr (by rw [map_smul])
  rw [scaledDualForm_apply, hpre, map_smul, smul_eq_mul]

/-- `Q` pulled back along `η ↦ y_η` is `a` times the integral form `a Q^∨`:
`Q(y_ξ, y_η) = a ξ(y_η)`. -/
theorem comp_scaledDualPreimage :
    Q.comp (Q.scaledDualPreimage hQ a ha) (Q.scaledDualPreimage hQ a ha) =
      a • Q.scaledDualForm hQ a ha := by
  ext ξ η
  simp [scaledDualForm_apply]

/-- When `Q♭ : Λ → Hom(Λ, R)` is a perfect pairing, `1` kills its cokernel. -/
theorem one_smul_mem_range_of_isPerfPair [Q.IsPerfPair] (η : Dual R Λ) :
    (1 : R) • η ∈ LinearMap.range Q :=
  LinearMap.mem_range.mpr ⟨Q.toPerfPair.symm ((1 : R) • η), by simp⟩

include ha in
/-- If `a` kills the cokernel of `Q♭`, it kills the cokernel of `(-Q)♭`. -/
theorem smul_mem_range_neg (η : Dual R Λ) : a • η ∈ LinearMap.range (-Q) := by
  simpa [LinearMap.range_neg] using ha η

/-- When `Q♭ : Λ → Hom(Λ, R)` is a perfect pairing, `1` kills the cokernel of `(-Q)♭`. -/
theorem one_smul_mem_range_neg_of_isPerfPair [Q.IsPerfPair] (η : Dual R Λ) :
    (1 : R) • η ∈ LinearMap.range (-Q) :=
  Q.smul_mem_range_neg 1 Q.one_smul_mem_range_of_isPerfPair η

/-- **The dual of a principal form is principal.** If `Q♭ : Λ → Hom(Λ, R)` is bijective, the
integral dual form `Q^∨` (the case `a = 1`) is the transport of `Q` along `Q♭`, hence a perfect
pairing on `Hom(Λ, R)`. -/
theorem isPerfPair_scaledDualForm_one [Q.IsPerfPair] :
    (Q.scaledDualForm (IsPerfPair.bijective_left Q).injective 1
      Q.one_smul_mem_range_of_isPerfPair).IsPerfPair := by
  refine IsPerfPair.congr (p := Q) Q.toPerfPair.symm Q.toPerfPair.symm _
    (LinearMap.ext₂ fun x y ↦ ?_)
  simp only [compl₁₂_apply, LinearEquiv.coe_coe, LinearEquiv.symm_symm, toLinearMap_toPerfPair]
  rw [scaledDualForm_apply_right, one_mul]

/-! ### Comparison with the dual form over a field -/

variable {K V : Type*} [Field K] [Algebra R K] [AddCommGroup V] [Module K V] [Module R V]
  [IsScalarTower R K V] [FiniteDimensional K V] {j : Λ →ₗ[R] V} (hj : IsBaseChange K j)
  (hQK : (hj.bilinForm Q).Nondegenerate)

/-- `Q♭` of the base change, on the image of `Λ`, is the base change of `Q♭`. -/
@[simp]
theorem toDual_isBaseChange_bilinForm_apply (y : Λ) :
    (hj.bilinForm Q).toDual hQK (j y) = hj.toDual (Q y) := by
  refine hj.algHom_ext _ _ fun z ↦ ?_
  rw [toDual_def, IsBaseChange.bilinForm_apply, IsBaseChange.toDual_comp_apply]

/-- **`a Q^∨` is integral.** On the image of `Hom(Λ, R)` in `Module.Dual K V`, the dual form of the
base change of `Q`, multiplied by `a`, is the integral form `scaledDualForm`. -/
theorem algebraMap_scaledDualForm (ξ η : Dual R Λ) :
    algebraMap R K (Q.scaledDualForm hQ a ha ξ η) =
      algebraMap R K a * (hj.bilinForm Q).dualForm hQK (hj.toDual ξ) (hj.toDual η) := by
  set y := Q.scaledDualPreimage hQ a ha η
  have hy : (hj.bilinForm Q).toDual hQK (j y) = algebraMap R K a • hj.toDual η := by
    rw [toDual_isBaseChange_bilinForm_apply, apply_scaledDualPreimage, map_smul, algebraMap_smul]
  rw [scaledDualForm_apply, ← hj.toDual_comp_apply]
  by_cases ha0 : algebraMap R K a = 0
  · rw [ha0, zero_smul, ← map_zero ((hj.bilinForm Q).toDual hQK)] at hy
    rw [(hj.bilinForm Q).toDual hQK |>.injective hy, map_zero, ha0, zero_mul]
  · have : hj.toDual η = (hj.bilinForm Q).toDual hQK ((algebraMap R K a)⁻¹ • j y) := by
      rw [map_smul, hy, smul_smul, inv_mul_cancel₀ ha0, one_smul]
    rw [this, dualForm_apply_toDual_right, map_smul, smul_eq_mul, mul_inv_cancel_left₀ ha0]

end Lattice

end LinearMap.BilinForm

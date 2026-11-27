/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Bott.Complex
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.Algebra.Module.BigOperators
import TauCeti.Algebra.Ring.NegOnePow

/-!
# The Bott complex of a Morse function and of its product with a manifold

Let `f` be a Morse function on `M` with finitely many critical points `ι`, of indices `λ_C`, and
let `c C D` be the signed count of its trajectories from `C` to `D`, nonzero only when
`λ_C = λ_D + 1` and satisfying `∑_E c_CE c_ED = 0`. This file specializes the algebraic Bott complex
`TauCeti.BottChainData` to two Morse–Bott functions built from `f`.

**Products.** For an `n`-dimensional manifold `N` whose chains form a module, also written `N`,
with boundary `∂_N`, the function `f ∘ pr₁` on `M × N` is Morse–Bott with critical components
`{C} × N` of negative-normal rank `λ_C` and dimension `n`. The trajectories from `{C} × N` to
`{D} × N` are the products of those from `C` to `D` with `N`, so the endpoint pushforward multiplies
a chain by `c C D` (`TauCeti.BottChainData.morseProd`). All its correspondences join components of
the same dimension whose ranks differ by one, where the chain-degree shift vanishes
(`TauCeti.bottDegreeShift_eq_zero_of_eq_add_one`) and the broken face through `E` has the sign
`(-1)^(n λ_C)` whatever `E` is (`TauCeti.negOnePow_bottBrokenFaceExponent_of_eq_add_one`), so the
face relation reduces to `∂_Morse² = 0`. The correspondences are the Morse coefficients with the
sign `(-1)^((λ_D + 1) n)` (`TauCeti.BottChainData.correspondence_morseProd`).

The Bott complex of the product is the tensor product of the Morse complex with the chains of `N`.
The signs `ε_C = (-1)^(n λ_C (λ_C + 1) / 2)` (`TauCeti.morseProdTwistSign`) satisfy
`ε_C ε_D = (-1)^((λ_D + 1) n)` when `λ_C = λ_D + 1`, since consecutive triangular numbers add up
to the square `(λ_D + 1)²`.
Reversing the negative-normal orientations of the components with `ε_C = -1`
(`TauCeti.BottChainData.reorient`) therefore removes the signs from the correspondences, and the
Bott differential becomes

`d_Morse ⊗ 1 + (-1)^λ 1 ⊗ ∂_N`

(`TauCeti.BottChainData.differential_reorient_morseProd`). Here this differential is written on
`ι → N`, whose component in `D` is `∑_C c_CD x_C + (-1)^λ_D ∂_N x_D`
(`TauCeti.morseTensorDifferential`), and it is the tensor product differential under the
identification of `(ι → R) ⊗ N` with `ι → N` (`TauCeti.morseTensorDifferential_comp_tensor`). The
Bott chain complexes before and after the reversal are isomorphic
(`TauCeti.BottChainData.chainComplexReorientIso`).

**The ordinary Morse complex.** Taking `N` to be a point, with chains `R` in degree `0`, gives the
Bott data of `f` itself (`TauCeti.BottChainData.ofMorse`): its critical components are the critical
points, and its Bott differential is the Morse differential `x ↦ x ᵥ* c`, which sends `C` to
`∑_D c_CD D` (`TauCeti.BottChainData.differential_ofMorse`). Its piece of total degree `k` consists
of the chains on the critical points of index `k`
(`TauCeti.BottChainData.mem_totalDegree_ofMorse_iff`). Together with
`TauCeti.BottChainData.ofBoundary` for a constant function, these are the basic specializations of
the Bott complex.

## Main definitions

* `TauCeti.BottChainData.morseProd`: the Bott data of a Morse function times a manifold.
* `TauCeti.morseTensorDifferential`: the differential `d_Morse ⊗ 1 + (-1)^λ 1 ⊗ ∂_N` on `ι → N`.
* `TauCeti.morseProdTwistSign`: the orientation signs that turn the one into the other.
* `TauCeti.BottChainData.ofMorse`: the Bott data of a Morse function.

## Main results

* `TauCeti.BottChainData.correspondence_morseProd`,
  `TauCeti.BottChainData.differential_morseProd_apply`: the correspondences and the Bott
  differential of the product.
* `TauCeti.BottChainData.differential_reorient_morseProd`: after the change of orientations, the
  Bott differential of the product is `d_Morse ⊗ 1 + (-1)^λ 1 ⊗ ∂_N`.
* `TauCeti.morseTensorDifferential_comp_tensor`: that differential is the tensor product
  differential.
* `TauCeti.BottChainData.differential_ofMorse`: the Bott differential of a Morse function is its
  Morse differential.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §6.2.4 (the Morse–Bott complex of geometric chains).
-/

public section

namespace TauCeti

variable {ι : Type*}

/-! ### Morse data times a chain module -/

namespace BottChainData

variable [Fintype ι] {R : Type*} [CommRing R] {N : Type*} [AddCommGroup N] [Module R N]
  (rank : ι → ℕ) (c : ι → ι → R) (hc : ∀ C D, c C D ≠ 0 → rank C = rank D + 1)
  (hcc : ∀ C D, ∑ E, c C E * c E D = 0) (n : ℕ) (boundary : N →ₗ[R] N)
  (hboundary : boundary ∘ₗ boundary = 0)

omit [Fintype ι] in
include hc in
/-- The composites `c_CE c_ED` of Morse coefficients, with the sign of the broken face through `E`
of the product with an `n`-dimensional factor, all carry the same sign `(-1)^(n λ_C)`. -/
private theorem negOnePow_smul_mul_eq (C E D : ι) :
    (bottBrokenFaceExponent rank (fun _ ↦ n) C E D).negOnePow • (c C E * c E D) =
      ((n : ℤ) * rank C).negOnePow • (c C E * c E D) := by
  by_cases h : c C E = 0
  · simp [h]
  · rw [negOnePow_bottBrokenFaceExponent_of_eq_add_one rank _ (hc C E h) rfl]

/-- **The Bott data of a Morse function times an auxiliary chain module.** For a Morse function
on `M` with critical points `ι` of indices `rank` and trajectory counts `c C D`, and an
`n`-dimensional manifold whose chains form the module `N` with boundary `∂_N`, the function
`f ∘ pr₁` on `M × N` is Morse–Bott with critical components `{C} × N`, all of dimension `n`. The
trajectory space from `{C} × N` to `{D} × N` is the product of the trajectory space from `C` to
`D` with `N`, so its endpoint pushforward multiplies a chain by `c C D`. -/
def morseProd : BottChainData R ι fun _ ↦ N where
  rank := rank
  dim _ := n
  boundary _ := boundary
  boundary_comp_boundary _ := hboundary
  pushforward C D := c C D • LinearMap.id
  boundary_comp_pushforward C D := by
    ext x
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply, LinearMap.add_apply,
      LinearMap.sum_apply, map_smul]
    have hshift :
        (bottDegreeShift rank C D).negOnePow • c C D • boundary x = c C D • boundary x := by
      by_cases h : c C D = 0
      · simp [h]
      · rw [bottDegreeShift_eq_zero_of_eq_add_one rank (hc C D h), Int.negOnePow_zero, one_smul]
    have hterm : ∀ E, (bottBrokenFaceExponent rank (fun _ ↦ n) C E D).negOnePow •
        c C E • c E D • x = (((n : ℤ) * rank C).negOnePow • (c C E * c E D)) • x := fun E ↦ by
      rw [← negOnePow_smul_mul_eq rank c hc n C E D, Units.smul_def, Units.smul_def, smul_assoc,
        mul_smul]
    -- the broken faces cancel by `∂_Morse² = 0`
    rw [hshift, Finset.sum_congr rfl fun E _ ↦ hterm E, ← Finset.sum_smul, ← Finset.smul_sum, hcc,
      smul_zero, zero_smul, add_zero]

section morseProd

@[simp]
theorem morseProd_rank : (morseProd rank c hc hcc n boundary hboundary).rank = rank :=
  (rfl)

@[simp]
theorem morseProd_dim : (morseProd rank c hc hcc n boundary hboundary).dim = fun _ ↦ n :=
  (rfl)

@[simp]
theorem morseProd_boundary (C : ι) :
    (morseProd rank c hc hcc n boundary hboundary).boundary C = boundary :=
  (rfl)

@[simp]
theorem morseProd_pushforward (C D : ι) :
    (morseProd rank c hc hcc n boundary hboundary).pushforward C D = c C D • LinearMap.id :=
  (rfl)

/-- **The signed correspondences of the product** are the Morse coefficients with the sign
`(-1)^((λ_D + 1) n)`. -/
@[simp]
theorem correspondence_morseProd (C D : ι) :
    (morseProd rank c hc hcc n boundary hboundary).correspondence C D =
      ((rank D + 1 : ℤ) * n).negOnePow • c C D • LinearMap.id := by
  ext x
  rw [correspondence_apply, morseProd_pushforward]
  by_cases h : c C D = 0
  · simp [h]
  · rw [morseProd_rank, morseProd_dim,
      bottCorrespondenceExponent_of_eq_add_one rank (fun _ ↦ n) (hc C D h)]
    simp

/-- **The Bott differential of the product**: its component in `D` is
`(-1)^λ_D ∂_N x_D + ∑_C (-1)^((λ_D + 1) n) c_CD x_C`. -/
theorem differential_morseProd_apply (x : ι → N) (D : ι) :
    (morseProd rank c hc hcc n boundary hboundary).differential x D =
      (rank D : ℤ).negOnePow • boundary (x D) +
        ((rank D + 1 : ℤ) * n).negOnePow • ∑ C, c C D • x C := by
  simp [differential_apply, correspondence_morseProd, Finset.smul_sum]

/-- **The pushforwards of the product respect a grading of `N`**: they shift the chain degree by
`d_CD`, which vanishes wherever the Morse coefficient `c C D` is nonzero. This is the grading
hypothesis of `TauCeti.BottChainData.chainComplex`. -/
theorem pushforward_morseProd_mem {T : ℤ → Submodule R N} (C D : ι) {j : ℤ} {x : N}
    (hx : x ∈ T j) :
    (morseProd rank c hc hcc n boundary hboundary).pushforward C D x ∈
      T (j + bottDegreeShift (morseProd rank c hc hcc n boundary hboundary).rank C D) := by
  rw [morseProd_pushforward, morseProd_rank, LinearMap.smul_apply, LinearMap.id_apply]
  by_cases h : c C D = 0
  · simp [h]
  · rw [bottDegreeShift_eq_zero_of_eq_add_one rank (hc C D h), add_zero]
    exact (T j).smul_mem _ hx

end morseProd

end BottChainData

/-! ### The tensor product differential -/

section Tensor

variable {R : Type*} [CommRing R] {N : Type*} [AddCommGroup N] [Module R N]
  (rank : ι → ℕ) (c : ι → ι → R) (n : ℕ) (boundary : N →ₗ[R] N)

/-- **The sign `(-1)^(n λ_C (λ_C + 1) / 2)`** of a component `C` of negative-normal rank `λ_C` in
the product of a Morse function with an `n`-dimensional manifold. Over two components whose ranks
differ by one these signs multiply to `(-1)^((λ_D + 1) n)`, the sign of the correspondences of the
product, so reversing the negative-normal orientations of the components where it is `-1` removes
the signs from the correspondences. -/
def morseProdTwistSign (C : ι) : ℤˣ := ((n : ℤ) * ((rank C : ℤ) * (rank C + 1) / 2)).negOnePow

theorem morseProdTwistSign_def (C : ι) :
    morseProdTwistSign rank n C = ((n : ℤ) * ((rank C : ℤ) * (rank C + 1) / 2)).negOnePow :=
  (rfl)

/-- Over components whose ranks differ by one, the twist signs multiply to the sign
`(-1)^((λ_D + 1) n)` of the correspondences of the product. -/
theorem morseProdTwistSign_mul_morseProdTwistSign {C D : ι} (h : rank C = rank D + 1) :
    morseProdTwistSign rank n C * morseProdTwistSign rank n D =
      ((rank D + 1 : ℤ) * n).negOnePow := by
  -- the triangular numbers satisfy `(-1)^((k + 1)(k + 2) / 2) = (-1)^(k + 1) (-1)^(k (k + 1) / 2)`
  have hk := Int.negOnePow_mul_succ_div_two_succ (rank D)
  rw [← Int.negOnePow_add, Int.negOnePow_eq_iff] at hk
  rw [morseProdTwistSign_def, morseProdTwistSign_def, ← Int.negOnePow_add, Int.negOnePow_eq_iff, h]
  push_cast
  convert (hk.mul_left (n : ℤ)).add (even_two_mul ((n : ℤ) * ((rank D : ℤ) * (rank D + 1) / 2)))
    using 1
  ring

variable [Fintype ι]

/-- **The differential `d_Morse ⊗ 1 + (-1)^λ 1 ⊗ ∂_N`** of the tensor product of the Morse complex,
free on the critical points `ι` with coefficients `c` and gradings `rank`, with a chain module
`N`, written on `ι → N`: its component in `D` is `∑_C c_CD x_C + (-1)^λ_D ∂_N x_D`. -/
def morseTensorDifferential : (ι → N) →ₗ[R] (ι → N) :=
  LinearMap.pi fun D ↦ ∑ C, c C D • LinearMap.proj C +
    (rank D : ℤ).negOnePow • (boundary ∘ₗ LinearMap.proj D)

@[simp]
theorem morseTensorDifferential_apply (x : ι → N) (D : ι) :
    morseTensorDifferential rank c boundary x D =
      ∑ C, c C D • x C + (rank D : ℤ).negOnePow • boundary (x D) := by
  simp [morseTensorDifferential, LinearMap.sum_apply]

/-- **The Bott complex of a Morse function times an auxiliary manifold** is the tensor product of
the Morse complex with the chains of the auxiliary manifold: after reversing the orientations of
the negative-normal lines of the components `C` with `n λ_C (λ_C + 1) / 2` odd, the Bott
differential of `morseProd` is `d_Morse ⊗ 1 + (-1)^λ 1 ⊗ ∂_N`. The Bott chain complexes before
and after the reversal are isomorphic by `TauCeti.BottChainData.chainComplexReorientIso`. -/
theorem BottChainData.differential_reorient_morseProd
    (hc : ∀ C D, c C D ≠ 0 → rank C = rank D + 1) (hcc : ∀ C D, ∑ E, c C E * c E D = 0)
    (hboundary : boundary ∘ₗ boundary = 0) :
    ((morseProd rank c hc hcc n boundary hboundary).reorient
        (morseProdTwistSign rank n)).differential =
      morseTensorDifferential rank c boundary := by
  ext x : 1
  funext D
  have hterm : ∀ C, (morseProdTwistSign rank n C * morseProdTwistSign rank n D) •
      ((rank D + 1 : ℤ) * n).negOnePow • c C D • x C = c C D • x C := by
    intro C
    by_cases h : c C D = 0
    · simp [h]
    · rw [morseProdTwistSign_mul_morseProdTwistSign rank n (hc C D h), smul_smul,
        ← Int.negOnePow_add, ← two_mul, Int.negOnePow_two_mul, one_smul]
  simp only [differential_apply, correspondence_reorient, correspondence_morseProd, reorient_rank,
    reorient_boundary, morseProd_rank, morseProd_boundary, LinearMap.smul_apply,
    LinearMap.id_apply, hterm, morseTensorDifferential_apply, add_comm]

/-- The differential `d_Morse ⊗ 1 + (-1)^λ 1 ⊗ ∂_N` squares to zero. -/
theorem morseTensorDifferential_comp_morseTensorDifferential
    (hc : ∀ C D, c C D ≠ 0 → rank C = rank D + 1) (hcc : ∀ C D, ∑ E, c C E * c E D = 0)
    (hboundary : boundary ∘ₗ boundary = 0) :
    morseTensorDifferential rank c boundary ∘ₗ morseTensorDifferential rank c boundary = 0 := by
  rw [← BottChainData.differential_reorient_morseProd rank c 0 boundary hc hcc hboundary]
  exact BottChainData.differential_comp_differential _

/-- **`morseTensorDifferential` is `d_Morse ⊗ 1 + (-1)^λ 1 ⊗ ∂_N`.** Under the identification of
`(ι → R) ⊗ N` with `ι → N`, `φ ⊗ x ↦ (C ↦ φ C • x)`, it is the tensor product differential of the
Morse differential `φ ↦ φ ᵥ* c` on `ι → R`, which sends the generator `C` to `∑_D c_CD D`, with
`∂_N`, with the Koszul sign `(-1)^λ_C` on the generator `C`. -/
theorem morseTensorDifferential_comp_tensor [DecidableEq ι] :
    morseTensorDifferential rank c boundary ∘ₗ
        (TensorProduct.comm R (ι → R) N ≪≫ₗ TensorProduct.piScalarRight R R N ι).toLinearMap =
      (TensorProduct.comm R (ι → R) N ≪≫ₗ TensorProduct.piScalarRight R R N ι).toLinearMap ∘ₗ
        (TensorProduct.map (Matrix.vecMulLinear (Matrix.of c)) LinearMap.id +
          TensorProduct.map (LinearMap.pi fun C ↦ (rank C : ℤ).negOnePow • LinearMap.proj C)
            boundary) := by
  refine TensorProduct.ext' fun φ x ↦ ?_
  funext D
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.trans_apply,
    TensorProduct.comm_tmul, LinearMap.add_apply, TensorProduct.map_tmul, map_add,
    TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul,
    morseTensorDifferential_apply, Pi.add_apply, LinearMap.id_apply, LinearMap.pi_apply,
    LinearMap.smul_apply, LinearMap.proj_apply, map_smul, smul_assoc]
  congr 1
  simp [Matrix.vecMul_eq_sum, Finset.sum_smul, mul_smul, smul_comm (c _ D)]

end Tensor

/-! ### The ordinary Morse complex -/

namespace BottChainData

variable [Fintype ι] {R : Type*} [CommRing R]
  (rank : ι → ℕ) (c : ι → ι → R) (hc : ∀ C D, c C D ≠ 0 → rank C = rank D + 1)
  (hcc : ∀ C D, ∑ E, c C E * c E D = 0)

/-- **The Bott data of a Morse function**: its critical points are critical components of
dimension `0` with chains `R` and no boundary, and the pushforward from `C` to `D` multiplies by
the trajectory count `c C D`. It is the product `morseProd` with a point. -/
def ofMorse : BottChainData R ι fun _ ↦ R :=
  morseProd rank c hc hcc 0 0 (LinearMap.zero_comp 0)

theorem ofMorse_def :
    ofMorse rank c hc hcc = morseProd rank c hc hcc 0 0 (LinearMap.zero_comp 0) :=
  (rfl)

@[simp]
theorem ofMorse_rank : (ofMorse rank c hc hcc).rank = rank :=
  (rfl)

@[simp]
theorem ofMorse_dim : (ofMorse rank c hc hcc).dim = fun _ ↦ 0 :=
  (rfl)

@[simp]
theorem ofMorse_boundary (C : ι) : (ofMorse rank c hc hcc).boundary C = 0 :=
  (rfl)

@[simp]
theorem ofMorse_pushforward (C D : ι) :
    (ofMorse rank c hc hcc).pushforward C D = c C D • LinearMap.id :=
  (rfl)

@[simp]
theorem correspondence_ofMorse (C D : ι) :
    (ofMorse rank c hc hcc).correspondence C D = c C D • LinearMap.id := by
  simp [ofMorse_def]

/-- **The Bott differential of a Morse function is its Morse differential** `x ↦ x ᵥ* c`, which
sends the critical point `C` to `∑_D c_CD D`. -/
theorem differential_ofMorse :
    (ofMorse rank c hc hcc).differential = Matrix.vecMulLinear (Matrix.of c) := by
  ext x : 1
  funext D
  simp [differential_apply, Matrix.vecMul_eq_sum, mul_comm]

/-- **The total-degree pieces of the Morse complex.** When the chains `R` on each critical point
sit in degree `0`, the piece of total degree `k` of the Bott complex of a Morse function consists
of the chains supported on the critical points of index `k`. -/
theorem mem_totalDegree_ofMorse_iff {k : ℤ} {x : ι → R} :
    x ∈ (ofMorse rank c hc hcc).totalDegree (fun _ j ↦ if j = 0 then ⊤ else ⊥) k ↔
      ∀ C, (rank C : ℤ) ≠ k → x C = 0 := by
  simp only [mem_totalDegree_iff, ofMorse, morseProd_rank]
  refine forall_congr' fun C ↦ ?_
  split_ifs with h <;> simp [Submodule.mem_bot] <;> omega

end BottChainData

end TauCeti

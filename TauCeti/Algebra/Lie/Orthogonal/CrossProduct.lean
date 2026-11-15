/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Classical
public import Mathlib.LinearAlgebra.CrossProduct
public import Mathlib.LinearAlgebra.Matrix.Dual
public import TauCeti.Algebra.Lie.Coadjoint
public import TauCeti.LinearAlgebra.CrossProduct
public import TauCeti.LinearAlgebra.Matrix.CrossProduct
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

/-!
# The orthogonal Lie algebra `so(3)` and the cross product

The skew-symmetric `3 × 3` matrices are the matrices of the maps `v ↦ u ⨯₃ v`. The **hat map**
`u ↦ û` (`TauCeti.crossProductMatrix`, in `TauCeti.LinearAlgebra.Matrix.CrossProduct`) sends `u`
to the matrix of this map; `û` is skew-symmetric, and the commutator of two such matrices is the
matrix of the cross product of their vectors:

`[û, v̂] = (u ⨯₃ v)^`.

When `R` has no zero divisors and `2 ≠ 0` in `R`, the hat map is a linear isomorphism
`TauCeti.soThreeEquiv` from `R³`, with the cross product as its bracket, onto the orthogonal Lie
algebra `so(3) = LieAlgebra.Orthogonal.so (Fin 3) R`. (In characteristic `2` a skew-symmetric
matrix need not have zero diagonal.) Composing the dot product `n ↦ n ⬝ᵥ ·` with this isomorphism
identifies `R³` with the dual `so(3)*` (`TauCeti.soThreeDualEquiv`): a linear functional on `so(3)`
is `ν_n : û ↦ n ⬝ᵥ u` for a unique vector `n`.

## Coadjoint orbits

Through these identifications the coadjoint action of `so(3)` on its dual is the infinitesimal
rotation of `R³`:

`⁅ξ̂, ν_n⁆ = ν_(ξ ⨯₃ n)`

(`TauCeti.lie_soThreeEquiv_soThreeDualEquiv`). Hence `ξ̂` stabilizes `ν_n` exactly when
`ξ ⨯₃ n = 0`. Over a field and for `n ≠ 0` the stabilizer is the line spanned by `n̂`
(`TauCeti.lieAnnihilator_soThreeDualEquiv_toSubmodule_eq_span_soThreeEquiv`), so the algebraic
tangent model `so(3) ⧸ so(3)_ν` of the coadjoint orbit through `ν_n` has dimension `2`, and the
orbit derivative `[ξ̂] ↦ ν_(ξ ⨯₃ n)` maps it onto the plane `n^⊥`
(`TauCeti.soThreeDualEquiv_mem_range_coadjointTangentMap_iff`). Over `ℝ`, `n^⊥` is the tangent
plane at `n` of the sphere of radius `r = ‖n‖` about the origin; this sphere is the coadjoint orbit
of the rotation group `SO(3)` through `ν_n`, a fact about the group action not treated here.

The Kirillov–Kostant–Souriau form of `ν_n` is the triple product

`ω_n([ξ̂], [η̂]) = n ⬝ᵥ (ξ ⨯₃ η)`

(`TauCeti.kksForm_soThreeDualEquiv_mk`). Its value on the tangent vectors `a = ξ ⨯₃ n` and
`b = η ⨯₃ n` compares with the area form `(n / r) ⬝ᵥ (a ⨯₃ b)` of that sphere, with its outward
normal, by

`(n ⬝ᵥ n) ω_n([ξ̂], [η̂]) = n ⬝ᵥ (a ⨯₃ b)`

(`TauCeti.dotProduct_self_mul_kksForm_soThreeDualEquiv_mk`). So on the sphere of radius `r > 0`
the KKS form is `1 / r` times the area form, and its total KKS area is `4πr² / r = 4πr`; that
integral is not formalized here.

## Main definitions

* `TauCeti.soThreeEquiv R`: the isomorphism `u ↦ û` from `R³` onto `so(3)`.
* `TauCeti.soThreeDualEquiv R`: the identification of `R³` with `so(3)*` by the dot product.

## Main results

* `TauCeti.lie_soThreeEquiv`: `⁅û, v̂⁆ = (u ⨯₃ v)^` in `so(3)`.
* `TauCeti.finrank_so_three`: `so(3)` has dimension `3`.
* `TauCeti.lie_soThreeEquiv_soThreeDualEquiv`: the coadjoint action is the rotation `n ↦ ξ ⨯₃ n`.
* `TauCeti.lieAnnihilator_soThreeDualEquiv_toSubmodule_eq_span_soThreeEquiv`,
  `TauCeti.lieAnnihilator_soThreeDualEquiv_eq_top_iff`: the coadjoint stabilizers.
* `TauCeti.finrank_quotient_lieAnnihilator_soThreeDualEquiv`: nonzero coadjoint orbits are
  two-dimensional.
* `TauCeti.soThreeDualEquiv_mem_range_coadjointTangentMap_iff`: the orbit tangent plane at `ν_n`
  is `n^⊥`.
* `TauCeti.kksForm_soThreeDualEquiv_mk`, `TauCeti.dotProduct_self_mul_kksForm_soThreeDualEquiv_mk`:
  the KKS form is the triple product, and it is `1 / ‖n‖` times the area form of the sphere.

## References

* J. E. Marsden and T. S. Ratiu, *Introduction to Mechanics and Symmetry*, second edition, Texts
  in Applied Mathematics 17, Springer, 1999, Chapters 9 and 14 (the hat map and the coadjoint
  orbits of `SO(3)`).
* A. A. Kirillov, *Lectures on the Orbit Method*, Graduate Studies in Mathematics 64, AMS, 2004,
  Section 1.2.
-/

public section

open Matrix Module LieAlgebra.Orthogonal

attribute [local instance 100] LieRing.ofAssociativeRing

namespace TauCeti

/-! ### The hat map onto `so(3)` -/

section CommRing

variable {R : Type*} [CommRing R]

/-- The matrix `û` lies in the orthogonal Lie algebra `so(3)`. -/
theorem crossProductMatrix_mem_so (u : Fin 3 → R) : crossProductMatrix R u ∈ so (Fin 3) R :=
  (mem_so _ _ _).mpr (transpose_crossProductMatrix u)

end CommRing

section CharNeTwo

variable (R : Type*) [CommRing R] [NoZeroDivisors R] [NeZero (2 : R)]

/-- The hat map `u ↦ û` as a linear isomorphism from `R³` onto the orthogonal Lie algebra `so(3)`.
It carries the cross product to the bracket (`TauCeti.lie_soThreeEquiv`). Since `2 ≠ 0` and `R`
has no zero divisors, skew-symmetric matrices have zero diagonal, so every element of `so(3)` is
some `û`. -/
def soThreeEquiv : (Fin 3 → R) ≃ₗ[R] so (Fin 3) R where
  toFun u := ⟨crossProductMatrix R u, crossProductMatrix_mem_so u⟩
  map_add' u v := Subtype.ext (map_add _ u v)
  map_smul' c u := Subtype.ext (map_smul _ c u)
  invFun A := ![(A : Matrix (Fin 3) (Fin 3) R) 2 1, (A : Matrix (Fin 3) (Fin 3) R) 0 2,
    (A : Matrix (Fin 3) (Fin 3) R) 1 0]
  left_inv u := by
    ext i
    fin_cases i <;> simp [crossProductMatrix_apply]
  right_inv A := by
    obtain ⟨A, hA⟩ := A
    have h : ∀ i j, A j i = -A i j := fun i j ↦ by
      simpa using congrFun (congrFun ((mem_so _ _ _).mp hA) i) j
    have hd : ∀ i, A i i = 0 := fun i ↦ by
      have h2 : 2 * A i i = 0 := by linear_combination h i i
      exact (mul_eq_zero.mp h2).resolve_left two_ne_zero
    ext i j
    fin_cases i <;> fin_cases j <;> simp [crossProductMatrix_apply, hd, h 0 1, h 0 2, h 1 2]

variable {R}

@[simp]
theorem coe_soThreeEquiv (u : Fin 3 → R) :
    (soThreeEquiv R u : Matrix (Fin 3) (Fin 3) R) = crossProductMatrix R u :=
  (rfl)

/-- The inverse of the hat map reads `u` off the off-diagonal entries of `A = û`:
`u = (A₂₁, A₀₂, A₁₀)`. -/
theorem soThreeEquiv_symm_apply (A : so (Fin 3) R) :
    (soThreeEquiv R).symm A = ![(A : Matrix (Fin 3) (Fin 3) R) 2 1,
      (A : Matrix (Fin 3) (Fin 3) R) 0 2, (A : Matrix (Fin 3) (Fin 3) R) 1 0] :=
  (rfl)

/-- The bracket of `so(3)` is the cross product: `⁅û, v̂⁆ = (u ⨯₃ v)^`. -/
@[simp]
theorem lie_soThreeEquiv (u v : Fin 3 → R) :
    ⁅soThreeEquiv R u, soThreeEquiv R v⁆ = soThreeEquiv R (u ⨯₃ v) :=
  Subtype.ext (crossProductMatrix_cross u v).symm

/-- The orthogonal Lie algebra `so(3)` has dimension `3`. -/
theorem finrank_so_three : finrank R (so (Fin 3) R) = 3 := by
  have : Nontrivial R := nontrivial_of_ne 2 0 two_ne_zero
  rw [← (soThreeEquiv R).finrank_eq, finrank_fin_fun]

variable (R) in
/-- The dot product identifies `R³` with the dual of `so(3)`: the vector `n` gives the functional
`ν_n : û ↦ n ⬝ᵥ u` (`TauCeti.soThreeDualEquiv_apply_soThreeEquiv`). -/
def soThreeDualEquiv : (Fin 3 → R) ≃ₗ[R] Dual R (so (Fin 3) R) :=
  (dotProductEquiv R (Fin 3)).trans (soThreeEquiv R).symm.dualMap

/-- The functional `ν_n` pairs `A ∈ so(3)` with `n ⬝ᵥ u`, where `A = û`. -/
theorem soThreeDualEquiv_apply (n : Fin 3 → R) (A : so (Fin 3) R) :
    soThreeDualEquiv R n A = n ⬝ᵥ (soThreeEquiv R).symm A :=
  (rfl)

/-- The functional `ν_n` pairs `û` with `n ⬝ᵥ u`. -/
@[simp]
theorem soThreeDualEquiv_apply_soThreeEquiv (n u : Fin 3 → R) :
    soThreeDualEquiv R n (soThreeEquiv R u) = n ⬝ᵥ u := by
  simp [soThreeDualEquiv_apply]

/-- The inverse of `soThreeDualEquiv` reads off the vector of a functional `f` on `so(3)` from
its values `f(êᵢ)` on the hat matrices of the standard basis vectors `eᵢ`. -/
theorem soThreeDualEquiv_symm_apply (f : Dual R (so (Fin 3) R)) :
    (soThreeDualEquiv R).symm f = fun i ↦ f (soThreeEquiv R (Pi.single i 1)) := by
  rw [LinearEquiv.symm_apply_eq]
  refine LinearMap.ext fun A ↦ ?_
  obtain ⟨u, rfl⟩ := (soThreeEquiv R).surjective A
  rw [soThreeDualEquiv_apply_soThreeEquiv]
  conv_lhs => rw [pi_eq_sum_univ' u]
  simp [dotProduct, mul_comm]

end CharNeTwo

/-! ### Coadjoint orbits -/

section Coadjoint

variable {R : Type*} [CommRing R] [NoZeroDivisors R] [NeZero (2 : R)]

/-- **The coadjoint action of `so(3)` is the infinitesimal rotation of `R³`**:
`⁅ξ̂, ν_n⁆ = ν_(ξ ⨯₃ n)`. -/
@[simp]
theorem lie_soThreeEquiv_soThreeDualEquiv (ξ n : Fin 3 → R) :
    ⁅soThreeEquiv R ξ, soThreeDualEquiv R n⁆ = soThreeDualEquiv R (ξ ⨯₃ n) := by
  refine LinearMap.ext fun A ↦ ?_
  obtain ⟨η, rfl⟩ := (soThreeEquiv R).surjective A
  rw [Dual.lie_apply, lie_soThreeEquiv, soThreeDualEquiv_apply_soThreeEquiv,
    soThreeDualEquiv_apply_soThreeEquiv, ← cross_anticomm n ξ, neg_dotProduct,
    dotProduct_comm (n ⨯₃ ξ), triple_product_permutation η n ξ]

/-- The element `ξ̂` stabilizes `ν_n` exactly when `ξ ⨯₃ n = 0`. -/
theorem soThreeEquiv_mem_lieAnnihilator_iff (ξ n : Fin 3 → R) :
    soThreeEquiv R ξ ∈ lieAnnihilator R (so (Fin 3) R) (soThreeDualEquiv R n) ↔ ξ ⨯₃ n = 0 := by
  rw [mem_lieAnnihilator, lie_soThreeEquiv_soThreeDualEquiv, LinearEquiv.map_eq_zero_iff]

/-- The zero functional is the only one stabilized by all of `so(3)`. -/
theorem lieAnnihilator_soThreeDualEquiv_eq_top_iff (n : Fin 3 → R) :
    lieAnnihilator R (so (Fin 3) R) (soThreeDualEquiv R n) = ⊤ ↔ n = 0 := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · -- The basis vectors `eᵢ` all stabilize, and `eᵢ ⨯₃ n = 0` for every `i` forces `n = 0`.
    have hmem : ∀ ξ, ξ ⨯₃ n = 0 := fun ξ ↦
      (soThreeEquiv_mem_lieAnnihilator_iff ξ n).mp (h ▸ LieSubalgebra.mem_top _)
    have h0 := hmem ![1, 0, 0]
    have h1 := hmem ![0, 1, 0]
    simp only [cross_apply] at h0 h1
    ext i
    fin_cases i
    · simpa using congrFun h1 2
    · simpa using congrFun h0 2
    · simpa using congrFun h0 1
  · rintro rfl
    refine eq_top_iff.mpr fun A _ ↦ ?_
    obtain ⟨ξ, rfl⟩ := (soThreeEquiv R).surjective A
    exact (soThreeEquiv_mem_lieAnnihilator_iff ξ 0).mpr (map_zero _)

variable {K : Type*} [Field K] [NeZero (2 : K)]

/-- **The coadjoint stabilizer of a nonzero `ν_n` is the line spanned by `n̂`**, the infinitesimal
rotations about the axis `n`. -/
theorem lieAnnihilator_soThreeDualEquiv_toSubmodule_eq_span_soThreeEquiv {n : Fin 3 → K}
    (hn : n ≠ 0) :
    (lieAnnihilator K (so (Fin 3) K) (soThreeDualEquiv K n)).toSubmodule =
      K ∙ soThreeEquiv K n := by
  ext A
  obtain ⟨ξ, rfl⟩ := (soThreeEquiv K).surjective A
  -- `ξ ⨯₃ n = 0` exactly when `n, ξ` are linearly dependent, that is, `ξ` is a multiple of `n`.
  rw [LieSubalgebra.mem_toSubmodule, soThreeEquiv_mem_lieAnnihilator_iff, ← cross_anticomm,
    neg_eq_zero, ← not_ne_iff, crossProduct_ne_zero_iff_linearIndependent,
    LinearIndependent.pair_iff' hn, Submodule.mem_span_singleton]
  simp only [ne_eq, not_forall, not_not, ← map_smul, (soThreeEquiv K).injective.eq_iff]

/-- **The coadjoint orbits of `so(3)` through nonzero functionals are two-dimensional**: the
algebraic tangent model `so(3) ⧸ so(3)_ν` at a nonzero `ν_n` has dimension `2`. -/
theorem finrank_quotient_lieAnnihilator_soThreeDualEquiv {n : Fin 3 → K} (hn : n ≠ 0) :
    finrank K
      (so (Fin 3) K ⧸ (lieAnnihilator K (so (Fin 3) K) (soThreeDualEquiv K n)).toSubmodule) =
        2 := by
  have h := Submodule.finrank_quotient_add_finrank
    (lieAnnihilator K (so (Fin 3) K) (soThreeDualEquiv K n)).toSubmodule
  rw [lieAnnihilator_soThreeDualEquiv_toSubmodule_eq_span_soThreeEquiv hn,
    finrank_span_singleton ((soThreeEquiv K).map_ne_zero_iff.mpr hn), finrank_so_three] at h
  rw [lieAnnihilator_soThreeDualEquiv_toSubmodule_eq_span_soThreeEquiv hn]
  omega

/-- **The tangent plane of the coadjoint orbit through `ν_n` is `n^⊥`.** For `n ≠ 0`, the image of
the algebraic orbit derivative `[ξ̂] ↦ ν_(ξ ⨯₃ n)` consists of the `ν_m` with `n ⬝ᵥ m = 0`. -/
theorem soThreeDualEquiv_mem_range_coadjointTangentMap_iff {n : Fin 3 → K} (hn : n ≠ 0)
    (m : Fin 3 → K) :
    soThreeDualEquiv K m ∈ LinearMap.range (soThreeDualEquiv K n).coadjointTangentMap ↔
      n ⬝ᵥ m = 0 := by
  -- The pullback `T` of the image lies in the plane `n^⊥ = ker (n ⬝ᵥ ·)`, and both are
  -- two-dimensional.
  set T : Submodule K (Fin 3 → K) :=
    (LinearMap.range (soThreeDualEquiv K n).coadjointTangentMap).comap
      (soThreeDualEquiv K).toLinearMap with hT_def
  have hle : T ≤ LinearMap.ker (dotProductEquiv K (Fin 3) n) := by
    rintro m ⟨y, hy⟩
    induction y using Submodule.Quotient.induction_on with
    | H A =>
      obtain ⟨ξ, rfl⟩ := (soThreeEquiv K).surjective A
      rw [Dual.coadjointTangentMap_mk, lie_soThreeEquiv_soThreeDualEquiv] at hy
      rw [LinearMap.mem_ker, dotProductEquiv_apply_apply, ← (soThreeDualEquiv K).injective hy,
        dot_cross_self]
  have hT : finrank K T = 2 := by
    rw [← finrank_quotient_lieAnnihilator_soThreeDualEquiv hn,
      ← LinearMap.finrank_range_of_inj (soThreeDualEquiv K n).coadjointTangentMap_injective]
    exact (Submodule.equivMapOfInjective _ (soThreeDualEquiv K).injective T).finrank_eq.trans
      (by rw [hT_def, Submodule.map_comap_eq_of_surjective (soThreeDualEquiv K).surjective])
  have hP : finrank K (LinearMap.ker (dotProductEquiv K (Fin 3) n)) = 2 := by
    have h := Dual.finrank_ker_add_one_of_ne_zero
      ((dotProductEquiv K (Fin 3)).map_ne_zero_iff.mpr hn)
    rw [finrank_fin_fun] at h
    omega
  have hm := SetLike.ext_iff.mp (Submodule.eq_of_le_of_finrank_eq hle (hT.trans hP.symm)) m
  rwa [hT_def, Submodule.mem_comap, LinearEquiv.coe_coe, LinearMap.mem_ker,
    dotProductEquiv_apply_apply] at hm

end Coadjoint

/-! ### The Kirillov–Kostant–Souriau form -/

section KKS

variable {R : Type*} [CommRing R] [NoZeroDivisors R] [NeZero (2 : R)]

/-- **The KKS form of `so(3)` is the triple product**: `ω_n([ξ̂], [η̂]) = n ⬝ᵥ (ξ ⨯₃ η)`. -/
theorem kksForm_soThreeDualEquiv_mk (n ξ η : Fin 3 → R) :
    (soThreeDualEquiv R n).kksForm (Submodule.Quotient.mk (soThreeEquiv R ξ))
      (Submodule.Quotient.mk (soThreeEquiv R η)) = n ⬝ᵥ ξ ⨯₃ η := by
  rw [Dual.kksForm_mk, lie_soThreeEquiv, soThreeDualEquiv_apply_soThreeEquiv]

/-- **The KKS form compared with the area form of the sphere.** For the orbit tangent vectors
`a = ξ ⨯₃ n` and `b = η ⨯₃ n` at `n`, `(n ⬝ᵥ n) ω_n([ξ̂], [η̂]) = n ⬝ᵥ (a ⨯₃ b)`. Over `ℝ` and
for `r = ‖n‖ > 0` the area form of the sphere of radius `r` is `(a, b) ↦ (n / r) ⬝ᵥ (a ⨯₃ b)`, so
this says that the KKS form is `1 / r` times the area form. -/
theorem dotProduct_self_mul_kksForm_soThreeDualEquiv_mk (n ξ η : Fin 3 → R) :
    (n ⬝ᵥ n) * (soThreeDualEquiv R n).kksForm (Submodule.Quotient.mk (soThreeEquiv R ξ))
      (Submodule.Quotient.mk (soThreeEquiv R η)) = n ⬝ᵥ (ξ ⨯₃ n) ⨯₃ (η ⨯₃ n) := by
  -- `(ξ ⨯₃ n) ⨯₃ (η ⨯₃ n) = (ξ ⬝ᵥ η ⨯₃ n) • n`, and `ξ ⬝ᵥ η ⨯₃ n = n ⬝ᵥ ξ ⨯₃ η`.
  rw [kksForm_soThreeDualEquiv_mk, cross_cross_cross_eq_smul, dotProduct_smul, smul_eq_mul,
    triple_product_permutation n ξ η, mul_comm]

end KKS

end TauCeti

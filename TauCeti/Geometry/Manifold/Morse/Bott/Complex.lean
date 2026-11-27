/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Module.Basic
public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Ring

/-!
# The signs of the Bott complex and its total differential

Let `f` be a Morse–Bott function whose critical components `C` have negative-normal ranks `λ_C`
and dimensions `dim C`. The Bott complex has, for each component, a chain complex of geometric
chains on `C` with coefficients in the orientation line of the negative normal bundle, placed in
total degree `chain degree + λ_C`. Its differential has two kinds of terms: the internal boundary
`(-1)^λ_C ∂` of each component, and, for each ordered pair `(C, D)`, the trajectory
correspondence `F_CD`, which sends a chain `σ` on `C` to the endpoint pushforward of the fibre
product `𝓜(C, D) ×_C σ` with the space of Bott trajectories from `C` to `D`. This file isolates
the sign calculation behind `D² = 0`, which Hutchings's account suppresses, and proves the
resulting algebraic statement.

**Dimensions.** The trajectory space `𝓜(C, D)` has dimension
`m_CD = λ_C - λ_D + dim C - 1` (`TauCeti.bottTrajectoryDim`). A broken stratum through `E` has
dimension `m_CE + m_ED - dim E = m_CD - 1`, so it is a codimension-one face
(`TauCeti.bottTrajectoryDim_add_bottTrajectoryDim_sub`). The correspondence changes the chain
degree by `d_CD = m_CD - dim C = λ_C - λ_D - 1` (`TauCeti.bottDegreeShift`,
`TauCeti.bottDegreeShift_eq_bottTrajectoryDim_sub`), hence the total degree by `-1`.

**Signs.** The correspondence is the endpoint pushforward `P_CD` twisted by the sign
`(-1)^g_CD`, with `g_CD = (λ_D + 1) m_CD` (`TauCeti.bottCorrespondenceExponent`). The boundary of
`P_CD σ` has two kinds of faces. The input-boundary face is `(-1)^d_CD P_CD (∂σ)`, and the internal
cross-terms of `D²` cancel because `(-1)^λ_D (-1)^d_CD + (-1)^λ_C = 0`
(`TauCeti.negOnePow_rank_mul_negOnePow_bottDegreeShift`), including when `λ_C = λ_D`. The broken
face through `E` carries the outward-first sign `(-1)^(a + e λ_E)` of the compactified trajectory
space, where `a = m_CE`, `b = m_ED` and `e = dim E`. Comparing `𝓜(C, E) ×_E 𝓜(E, D)` with the
trajectory-first composite `𝓜(E, D) ×_E (𝓜(C, E) ×_C σ)` exchanges two fibre product factors,
which costs the sign `(-1)^(a b + e (a + b) + e)` of exchanging the factors of a fibre product
(`Orientation.map_fiberProduct_comm`). The total broken-face exponent is
`TauCeti.bottBrokenFaceExponent`, and the parity identity

`g_CD + λ_D + a + e λ_E ≡ g_CE + g_ED + a b + e (a + b) + e + 1 (mod 2)`

(`TauCeti.bottCorrespondenceExponent_add_modEq`) says exactly that the broken terms of `D²`
cancel the composites `F_ED F_CE` (`TauCeti.negOnePow_bottCorrespondenceExponent_mul`). Both
identities hold for all integer ranks and dimensions.

**The total differential.** `TauCeti.BottChainData` records the algebraic output of the geometry:
a module `M C` with a square-zero boundary for each component of a finite set, and maps
`P_CD : M C → M D` satisfying the face relation
`∂ P_CD = (-1)^d_CD P_CD ∂ + ∑_E (-1)^s_CED P_ED P_CE`, with `s_CED` the broken-face exponent.
Its total differential `D` on `∏_C M C` has component `(-1)^λ_D ∂ + ∑_C F_CD` in `D`, so its
diagonal entry is `(-1)^λ_D ∂ + F_DD` (with `F_DD = 0` for geometric data, since `𝓜(D, D)` is
empty) and `F_CD` off it (`TauCeti.BottChainData.differential`), and `D² = 0`
(`TauCeti.BottChainData.differential_comp_differential`). If each `M C` is graded so that `∂`
lowers degree by one and `P_CD` shifts it by `d_CD`, then `D` lowers the total degree
`chain degree + λ_C` by one (`TauCeti.BottChainData.differential_mem_totalDegree`), and the
total-degree pieces form a chain complex (`TauCeti.BottChainData.chainComplex`).

**Orientations.** The chains on `C` have coefficients in the orientation line of its negative
normal bundle, so reversing that orientation negates them. Reversing the orientations of the
components with `ε C = -1`, for signs `ε : ι → ℤˣ`, keeps the boundaries and multiplies `P_CD` by
`ε C ε D` (`TauCeti.BottChainData.reorient`). Negating the chains on those components intertwines
the two Bott differentials (`TauCeti.BottChainData.differential_reorient_apply`) and is an
isomorphism of Bott chain complexes (`TauCeti.BottChainData.chainComplexReorientIso`).

## Main definitions

* `TauCeti.bottTrajectoryDim`, `TauCeti.bottDegreeShift`: the dimension `m_CD` of the trajectory
  space and the chain-degree shift `d_CD` of the correspondence.
* `TauCeti.bottCorrespondenceExponent`, `TauCeti.bottBrokenFaceExponent`: the exponents `g_CD` and
  `s_CED` of the correspondence sign and of the broken-face sign.
* `TauCeti.BottChainData`: components with square-zero boundaries and pushforwards satisfying the
  face relation.
* `TauCeti.BottChainData.correspondence`, `TauCeti.BottChainData.differential`: the signed
  correspondences and the total differential.
* `TauCeti.BottChainData.totalDegree`, `TauCeti.BottChainData.chainComplex`: the total-degree
  pieces and the Bott chain complex.
* `TauCeti.BottChainData.ofBoundary`: components without trajectories between them, as for a
  constant function, whose Bott differential is the internal boundary
  (`TauCeti.BottChainData.differential_ofBoundary_apply`).
* `TauCeti.BottChainData.reorient`: the Bott data after reversing some negative-normal
  orientations.

## Main results

* `TauCeti.negOnePow_rank_mul_negOnePow_bottDegreeShift`: the cross-term coefficient vanishes.
* `TauCeti.bottCorrespondenceExponent_add_modEq`: the broken-face parity identity.
* `TauCeti.BottChainData.boundary_comp_correspondence_add_eq_zero`: the component identity of
  `D² = 0`.
* `TauCeti.BottChainData.differential_comp_differential`: `D² = 0`.
* `TauCeti.BottChainData.differential_mem_totalDegree`: `D` has total degree `-1`.
* `TauCeti.BottChainData.differential_reorient_apply`,
  `TauCeti.BottChainData.chainComplexReorientIso`: the Bott complex does not depend on the
  negative-normal orientations.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §6.2.4, Lemma 6.2 (the Morse–Bott complex of geometric
  chains), and §6.2.5, Theorem 6.5 (its homology).
-/

public section

open CategoryTheory

namespace TauCeti

variable {ι : Type*}

/-! ### Dimensions and signs -/

section Signs

variable (rank dim : ι → ℕ)

/-- **The dimension of the space of Bott trajectories** from the critical component `C` to the
critical component `D`, `m_CD = λ_C - λ_D + dim C - 1`, for negative-normal ranks `λ = rank`
and component dimensions `dim`. -/
def bottTrajectoryDim (C D : ι) : ℤ := rank C - rank D + dim C - 1

theorem bottTrajectoryDim_def (C D : ι) :
    bottTrajectoryDim rank dim C D = rank C - rank D + dim C - 1 :=
  (rfl)

/-- **The chain-degree shift of the Bott correspondence** from `C` to `D`,
`d_CD = λ_C - λ_D - 1`: the fibre product `𝓜(C, D) ×_C σ` of a chain `σ` on `C` has dimension
`dim σ + d_CD`. -/
def bottDegreeShift (C D : ι) : ℤ := rank C - rank D - 1

theorem bottDegreeShift_def (C D : ι) : bottDegreeShift rank C D = rank C - rank D - 1 :=
  (rfl)

/-- **The exponent of the sign of the Bott correspondence** from `C` to `D`,
`g_CD = (λ_D + 1) m_CD`: the signed correspondence is `(-1)^g_CD` times the endpoint pushforward
of the trajectory-first fibre product. -/
def bottCorrespondenceExponent (C D : ι) : ℤ := (rank D + 1) * bottTrajectoryDim rank dim C D

theorem bottCorrespondenceExponent_def (C D : ι) :
    bottCorrespondenceExponent rank dim C D = (rank D + 1) * bottTrajectoryDim rank dim C D :=
  (rfl)

/-- **The exponent of the sign of the broken face** through `E` of the correspondence from `C` to
`D`, `a + e λ_E + a b + e (a + b) + e`, with `a = m_CE`, `b = m_ED` and `e = dim E`. It is the
outward-first sign `a + e λ_E` of the face `𝓜(C, E) ×_E 𝓜(E, D)` of the compactified trajectory
space, plus the sign `a b + e (a + b) + e` of exchanging the two trajectory factors. -/
def bottBrokenFaceExponent (C E D : ι) : ℤ :=
  bottTrajectoryDim rank dim C E + dim E * rank E +
    bottTrajectoryDim rank dim C E * bottTrajectoryDim rank dim E D +
    dim E * (bottTrajectoryDim rank dim C E + bottTrajectoryDim rank dim E D) + dim E

theorem bottBrokenFaceExponent_def (C E D : ι) :
    bottBrokenFaceExponent rank dim C E D =
      bottTrajectoryDim rank dim C E + dim E * rank E +
        bottTrajectoryDim rank dim C E * bottTrajectoryDim rank dim E D +
        dim E * (bottTrajectoryDim rank dim C E + bottTrajectoryDim rank dim E D) + dim E :=
  (rfl)

/-- A broken stratum through `E` of the Bott trajectories from `C` to `D` has codimension one:
`m_CE + m_ED - dim E = m_CD - 1`. -/
theorem bottTrajectoryDim_add_bottTrajectoryDim_sub (C E D : ι) :
    bottTrajectoryDim rank dim C E + bottTrajectoryDim rank dim E D - dim E =
      bottTrajectoryDim rank dim C D - 1 := by
  simp only [bottTrajectoryDim]
  ring

/-- The chain-degree shift of the correspondence is the dimension of the trajectory space minus
that of its source component, `d_CD = m_CD - dim C`. -/
theorem bottDegreeShift_eq_bottTrajectoryDim_sub (C D : ι) :
    bottDegreeShift rank C D = bottTrajectoryDim rank dim C D - dim C := by
  simp only [bottDegreeShift, bottTrajectoryDim]
  ring

/-- The chain-degree shifts of two consecutive correspondences add up to that of the direct one,
less the codimension of the broken face: `d_CE + d_ED + 1 = d_CD`. -/
theorem bottDegreeShift_add_bottDegreeShift (C E D : ι) :
    bottDegreeShift rank C E + bottDegreeShift rank E D + 1 = bottDegreeShift rank C D := by
  simp only [bottDegreeShift]
  ring

/-- **The cross-term coefficient of the Bott differential vanishes**:
`(-1)^λ_D (-1)^d_CD + (-1)^λ_C = 0`, including when `λ_C = λ_D`. -/
theorem negOnePow_rank_mul_negOnePow_bottDegreeShift (C D : ι) :
    (rank D : ℤ).negOnePow * (bottDegreeShift rank C D).negOnePow = -(rank C : ℤ).negOnePow := by
  rw [← Int.negOnePow_add,
    show (rank D : ℤ) + bottDegreeShift rank C D = rank C - 1 by rw [bottDegreeShift]; ring,
    Int.negOnePow_sub, Int.negOnePow_one, mul_neg, mul_one]

/-- The polynomial identity behind the broken-face parity, on `ZMod 2`. -/
private theorem broken_face_parity :
    ∀ lC lE lD c e : ZMod 2,
      (lD + 1) * (lC - lD + c - 1) + lD + (lC - lE + c - 1) + e * lE =
        (lE + 1) * (lC - lE + c - 1) + (lD + 1) * (lE - lD + e - 1) +
          (lC - lE + c - 1) * (lE - lD + e - 1) +
          e * ((lC - lE + c - 1) + (lE - lD + e - 1)) + e + 1 := by
  decide

/-- **The broken-face parity identity of the Bott complex**: with `a = m_CE`, `b = m_ED` and
`e = dim E`,
`g_CD + λ_D + a + e λ_E ≡ g_CE + g_ED + a b + e (a + b) + e + 1 (mod 2)`.
It compares the outward-first sign of the broken face through `E` with the exchange of the two
trajectory factors, and makes the broken terms of `D²` cancel the composites `F_ED F_CE`. -/
theorem bottCorrespondenceExponent_add_modEq (C E D : ι) :
    bottCorrespondenceExponent rank dim C D + rank D + bottTrajectoryDim rank dim C E +
        dim E * rank E ≡
      bottCorrespondenceExponent rank dim C E + bottCorrespondenceExponent rank dim E D +
          bottTrajectoryDim rank dim C E * bottTrajectoryDim rank dim E D +
          dim E * (bottTrajectoryDim rank dim C E + bottTrajectoryDim rank dim E D) + dim E + 1
        [ZMOD 2] := by
  refine (ZMod.intCast_eq_intCast_iff _ _ 2).1 ?_
  simp only [bottCorrespondenceExponent, bottTrajectoryDim]
  push_cast
  exact broken_face_parity _ _ _ _ _

/-- **The broken terms of `D²` cancel**, in the form of signs:
`(-1)^g_CD (-1)^λ_D (-1)^s_CED = -(-1)^g_CE (-1)^g_ED`. -/
theorem negOnePow_bottCorrespondenceExponent_mul (C E D : ι) :
    (bottCorrespondenceExponent rank dim C D).negOnePow * (rank D : ℤ).negOnePow *
        (bottBrokenFaceExponent rank dim C E D).negOnePow =
      -((bottCorrespondenceExponent rank dim C E).negOnePow *
        (bottCorrespondenceExponent rank dim E D).negOnePow) := by
  rw [← Int.negOnePow_add, ← Int.negOnePow_add, ← Int.negOnePow_add, ← Int.negOnePow_succ,
    Int.negOnePow_eq_iff]
  -- the exponents differ from the two sides of the parity identity by an even number
  set a := bottTrajectoryDim rank dim C E
  set b := bottTrajectoryDim rank dim E D
  have h := (even_iff_two_dvd.2 (bottCorrespondenceExponent_add_modEq rank dim C E D).symm.dvd).add
    (even_two_mul (a * b + dim E * (a + b) + dim E))
  convert h using 1
  simp only [bottBrokenFaceExponent]
  ring

/-- The chain-degree shift of a correspondence between components whose negative-normal ranks
differ by one vanishes. -/
theorem bottDegreeShift_eq_zero_of_eq_add_one {C D : ι} (h : rank C = rank D + 1) :
    bottDegreeShift rank C D = 0 := by
  rw [bottDegreeShift_def, h]
  push_cast
  ring

/-- Between components whose negative-normal ranks differ by one, the trajectory space has the
dimension of its source component, so the correspondence exponent is `g_CD = (λ_D + 1) dim C`. -/
theorem bottCorrespondenceExponent_of_eq_add_one {C D : ι} (h : rank C = rank D + 1) :
    bottCorrespondenceExponent rank dim C D = (rank D + 1) * dim C := by
  rw [bottCorrespondenceExponent_def, bottTrajectoryDim_def, h]
  push_cast
  ring

/-- **The broken-face sign at a single rank drop.** If the negative-normal rank drops by one from
`C` to `E` and the two components have the same dimension `e`, the sign of the broken face
through `E` is `(-1)^(e λ_C)`, whatever the target `D`. -/
theorem negOnePow_bottBrokenFaceExponent_of_eq_add_one {C E D : ι} (hrank : rank C = rank E + 1)
    (hdim : dim C = dim E) :
    (bottBrokenFaceExponent rank dim C E D).negOnePow = ((dim E : ℤ) * rank C).negOnePow := by
  have ha : bottTrajectoryDim rank dim C E = dim E := by
    rw [bottTrajectoryDim_def, hrank, hdim]
    push_cast
    ring
  rw [Int.negOnePow_eq_iff, bottBrokenFaceExponent_def, ha, hrank]
  -- the difference is `e (e + 1) + 2 e b`, with `b = m_ED`
  convert (Int.even_mul_succ_self (dim E : ℤ)).add
    (even_two_mul ((dim E : ℤ) * bottTrajectoryDim rank dim E D)) using 1
  push_cast
  ring

end Signs

/-! ### The total differential -/

/-- **The algebraic data of a Bott complex** over the finite set `ι` of critical components. Each
component `C` has a negative-normal rank `rank C`, a dimension `dim C` and a module `M C` of chains
with a square-zero boundary. For each ordered pair `(C, D)` the pushforward `P_CD` along the
Bott trajectories from `C` to `D` satisfies the face relation of the compactified trajectory
spaces: the boundary of `P_CD σ` consists of the input-boundary face `(-1)^d_CD P_CD (∂σ)` and the
broken faces `(-1)^s_CED P_ED P_CE σ` through the components `E`. The sum runs over all
components, including `E = C` and `E = D`; for geometric data the self-pushforwards `P_CC` vanish,
so only the intermediate components contribute. -/
structure BottChainData (R : Type*) [Semiring R] (ι : Type*) [Fintype ι] (M : ι → Type*)
    [∀ C, AddCommGroup (M C)] [∀ C, Module R (M C)] where
  /-- The negative-normal rank `λ_C` of each critical component. -/
  rank : ι → ℕ
  /-- The dimension of each critical component. -/
  dim : ι → ℕ
  /-- The boundary of the chains on each critical component. -/
  boundary : ∀ C, M C →ₗ[R] M C
  boundary_comp_boundary : ∀ C, boundary C ∘ₗ boundary C = 0
  /-- The endpoint pushforward along the Bott trajectories from `C` to `D`. -/
  pushforward : ∀ C D, M C →ₗ[R] M D
  boundary_comp_pushforward : ∀ C D, boundary D ∘ₗ pushforward C D =
    (bottDegreeShift rank C D).negOnePow • (pushforward C D ∘ₗ boundary C) +
      ∑ E, (bottBrokenFaceExponent rank dim C E D).negOnePow •
        (pushforward E D ∘ₗ pushforward C E)

namespace BottChainData

variable {R : Type*} [Semiring R] [Fintype ι] {M : ι → Type*} [∀ C, AddCommGroup (M C)]
  [∀ C, Module R (M C)] (B : BottChainData R ι M)

/-- **The signed Bott correspondence** `F_CD = (-1)^g_CD P_CD` from `C` to `D`. -/
def correspondence (C D : ι) : M C →ₗ[R] M D :=
  (bottCorrespondenceExponent B.rank B.dim C D).negOnePow • B.pushforward C D

theorem correspondence_apply (C D : ι) (x : M C) :
    B.correspondence C D x =
      (bottCorrespondenceExponent B.rank B.dim C D).negOnePow • B.pushforward C D x := by
  rw [correspondence, LinearMap.smul_apply]

/-- **The total differential of the Bott complex** on `∏_C M C`: its component in `D` is
`(-1)^λ_D ∂` applied to the `D`-component plus the correspondences `F_CD` applied to the
`C`-components. -/
def differential : (∀ C, M C) →ₗ[R] (∀ C, M C) :=
  LinearMap.pi fun D ↦ (B.rank D : ℤ).negOnePow • (B.boundary D ∘ₗ LinearMap.proj D) +
    ∑ C, B.correspondence C D ∘ₗ LinearMap.proj C

@[simp]
theorem differential_apply (x : ∀ C, M C) (D : ι) :
    B.differential x D =
      (B.rank D : ℤ).negOnePow • B.boundary D (x D) + ∑ C, B.correspondence C D (x C) := by
  simp [differential, LinearMap.sum_apply]

/-- **The component identity of `D² = 0`**: for every ordered pair of components,
`(-1)^λ_D ∂ F_CD + (-1)^λ_C F_CD ∂ + ∑_E F_ED F_CE = 0`. -/
theorem boundary_comp_correspondence_add_eq_zero (C D : ι) :
    (B.rank D : ℤ).negOnePow • (B.boundary D ∘ₗ B.correspondence C D) +
        (B.rank C : ℤ).negOnePow • (B.correspondence C D ∘ₗ B.boundary C) +
      ∑ E, B.correspondence E D ∘ₗ B.correspondence C E = 0 := by
  simp only [correspondence, LinearMap.comp_smul, LinearMap.smul_comp, B.boundary_comp_pushforward,
    smul_add, Finset.smul_sum, smul_smul]
  have hX : (B.rank D : ℤ).negOnePow * ((bottCorrespondenceExponent B.rank B.dim C D).negOnePow *
      (bottDegreeShift B.rank C D).negOnePow) =
        -((B.rank C : ℤ).negOnePow * (bottCorrespondenceExponent B.rank B.dim C D).negOnePow) := by
    rw [← mul_assoc, mul_right_comm, negOnePow_rank_mul_negOnePow_bottDegreeShift, neg_mul]
  have hY : ∀ E, (B.rank D : ℤ).negOnePow *
      ((bottCorrespondenceExponent B.rank B.dim C D).negOnePow *
        (bottBrokenFaceExponent B.rank B.dim C E D).negOnePow) =
      -((bottCorrespondenceExponent B.rank B.dim C E).negOnePow *
        (bottCorrespondenceExponent B.rank B.dim E D).negOnePow) := fun E ↦ by
    rw [← mul_assoc, mul_comm (B.rank D : ℤ).negOnePow, negOnePow_bottCorrespondenceExponent_mul]
  simp only [hX, hY, Units.neg_smul, Finset.sum_neg_distrib]
  abel

/-- The component identity of `D² = 0`, applied to a chain `x` on `C`. -/
theorem boundary_comp_correspondence_add_eq_zero_apply (C D : ι) (x : M C) :
    (B.rank D : ℤ).negOnePow • B.boundary D (B.correspondence C D x) +
        (B.rank C : ℤ).negOnePow • B.correspondence C D (B.boundary C x) +
      ∑ E, B.correspondence E D (B.correspondence C E x) = 0 := by
  simpa [LinearMap.sum_apply] using
    LinearMap.congr_fun (B.boundary_comp_correspondence_add_eq_zero C D) x

/-- **The Bott differential squares to zero.** -/
theorem differential_comp_differential : B.differential ∘ₗ B.differential = 0 := by
  ext x : 1
  funext D
  have hsq : B.boundary D (B.boundary D (x D)) = 0 :=
    LinearMap.congr_fun (B.boundary_comp_boundary D) (x D)
  -- sum the component identity over the components `C` carrying the chains `x C`
  have h := Finset.sum_eq_zero (s := Finset.univ) fun C _ ↦
    B.boundary_comp_correspondence_add_eq_zero_apply C D (x C)
  -- exchange the double sum to `∑_E ∑_C F_ED F_CE x_C`, the order in which `D (D x)` produces it
  simp only [Finset.sum_add_distrib] at h
  rw [Finset.sum_comm (f := fun C E ↦ B.correspondence E D (B.correspondence C E (x C)))] at h
  simp only [Units.smul_def] at h
  simp only [LinearMap.comp_apply, differential_apply, Units.smul_def, map_add, map_zsmul, map_sum,
    hsq, smul_zero, zero_add, Finset.smul_sum, Finset.sum_add_distrib, LinearMap.zero_apply,
    Pi.zero_apply]
  rw [← h]
  abel

/-- The differential applied twice vanishes. -/
@[simp]
theorem differential_differential (x : ∀ C, M C) : B.differential (B.differential x) = 0 :=
  LinearMap.congr_fun B.differential_comp_differential x


/-! ### The total degree -/

section Grading

variable {R : Type*} [Ring R] {M : ι → Type*} [∀ C, AddCommGroup (M C)] [∀ C, Module R (M C)]
  (B : BottChainData R ι M) (S : ∀ C, ℤ → Submodule R (M C))

/-- **The total-degree pieces of the Bott complex**: the elements of `∏_C M C` whose `C`-component
has chain degree `k - λ_C` for the gradings `S C` of the chains on the components. -/
def totalDegree (k : ℤ) : Submodule R (∀ C, M C) :=
  Submodule.pi Set.univ fun C ↦ S C (k - B.rank C)

@[simp]
theorem mem_totalDegree_iff {k : ℤ} {x : ∀ C, M C} :
    x ∈ B.totalDegree S k ↔ ∀ C, x C ∈ S C (k - B.rank C) := by
  simp [totalDegree]

variable {S}

/-- **The Bott differential has total degree `-1`**: if the boundary of each component lowers the
chain degree by one and the pushforward from `C` to `D` shifts it by `d_CD = λ_C - λ_D - 1`,
then the differential lowers the total degree `chain degree + λ_C` by one. -/
theorem differential_mem_totalDegree
    (hboundary : ∀ C j, ∀ x ∈ S C j, B.boundary C x ∈ S C (j - 1))
    (hpushforward : ∀ C D j, ∀ x ∈ S C j,
      B.pushforward C D x ∈ S D (j + bottDegreeShift B.rank C D))
    {k : ℤ} {x : ∀ C, M C} (hx : x ∈ B.totalDegree S k) :
    B.differential x ∈ B.totalDegree S (k - 1) := by
  rw [mem_totalDegree_iff] at hx ⊢
  intro D
  rw [differential_apply, Units.smul_def]
  refine add_mem (zsmul_mem ?_ _) (sum_mem fun C _ ↦ ?_)
  · convert hboundary D _ _ (hx D) using 2
    ring
  · rw [correspondence_apply, Units.smul_def]
    refine zsmul_mem ?_ _
    convert hpushforward C D _ _ (hx C) using 2
    simp only [bottDegreeShift]
    ring

/-- **The Bott chain complex**: the total-degree pieces of `∏_C M C` with the restrictions of the
Bott differential, for gradings of the components in which the boundary lowers the chain degree
by one and the pushforward from `C` to `D` shifts it by `d_CD`. -/
@[expose] noncomputable def chainComplex
    (hboundary : ∀ C j, ∀ x ∈ S C j, B.boundary C x ∈ S C (j - 1))
    (hpushforward : ∀ C D j, ∀ x ∈ S C j,
      B.pushforward C D x ∈ S D (j + bottDegreeShift B.rank C D)) :
    ChainComplex (ModuleCat R) ℤ :=
  ChainComplex.of (fun k ↦ ModuleCat.of R (B.totalDegree S k))
    (fun k ↦ ModuleCat.ofHom (B.differential.restrict fun _ hx ↦ by
      simpa using B.differential_mem_totalDegree hboundary hpushforward hx))
    (fun k ↦ by
      ext x : 2
      simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply, ModuleCat.hom_zero,
        LinearMap.zero_apply]
      refine Subtype.ext ?_
      rw [LinearMap.coe_restrict_apply, LinearMap.coe_restrict_apply, B.differential_differential,
        Submodule.coe_zero])

/-- The differential of the Bott chain complex from total degree `k + 1` to total degree `k` is
the Bott differential. -/
@[simp]
theorem chainComplex_d_apply
    (hboundary : ∀ C j, ∀ x ∈ S C j, B.boundary C x ∈ S C (j - 1))
    (hpushforward : ∀ C D j, ∀ x ∈ S C j,
      B.pushforward C D x ∈ S D (j + bottDegreeShift B.rank C D))
    (k : ℤ) (x : B.totalDegree S (k + 1)) :
    (((B.chainComplex hboundary hpushforward).d (k + 1) k).hom x : B.totalDegree S k).val =
      B.differential x.val := by
  simp only [chainComplex, ChainComplex.of_d, ModuleCat.hom_ofHom]
  exact LinearMap.coe_restrict_apply _ _

/-- The object of the Bott chain complex in total degree `k` is the total-degree piece. -/
@[simp]
theorem chainComplex_X
    (hboundary : ∀ C j, ∀ x ∈ S C j, B.boundary C x ∈ S C (j - 1))
    (hpushforward : ∀ C D j, ∀ x ∈ S C j,
      B.pushforward C D x ∈ S D (j + bottDegreeShift B.rank C D))
    (k : ℤ) :
    (B.chainComplex hboundary hpushforward).X k = ModuleCat.of R (B.totalDegree S k) :=
  (rfl)

end Grading

/-! ### Reversing the orientations of the negative-normal lines -/

section Reorient

variable (ε : ι → ℤˣ)

/-- **Bott data with reversed negative-normal orientations.** The chains on a component `C` have
coefficients in the orientation line of its negative normal bundle, so reversing that orientation
negates them. For signs `ε C = ±1`, reversing the orientations of the components with `ε C = -1`
keeps the boundaries and multiplies the pushforward from `C` to `D` by `ε C ε D`. -/
def reorient : BottChainData R ι M where
  rank := B.rank
  dim := B.dim
  boundary := B.boundary
  boundary_comp_boundary := B.boundary_comp_boundary
  pushforward C D := (ε C * ε D) • B.pushforward C D
  boundary_comp_pushforward C D := by
    simp only [LinearMap.comp_smul, LinearMap.smul_comp, B.boundary_comp_pushforward, smul_add,
      Finset.smul_sum, smul_smul]
    -- the sign `ε E` of the intermediate component appears twice in each broken term
    refine congrArg₂ (· + ·) (by rw [mul_comm]) (Finset.sum_congr rfl fun E _ ↦ ?_)
    rw [show ε C * ε E * (ε E * ε D) = ε C * ε D by
      rw [mul_assoc, ← mul_assoc (ε E), Int.units_mul_self, one_mul], mul_comm]

@[simp]
theorem reorient_rank : (B.reorient ε).rank = B.rank :=
  (rfl)

@[simp]
theorem reorient_dim : (B.reorient ε).dim = B.dim :=
  (rfl)

@[simp]
theorem reorient_boundary : (B.reorient ε).boundary = B.boundary :=
  (rfl)

@[simp]
theorem reorient_pushforward (C D : ι) :
    (B.reorient ε).pushforward C D = (ε C * ε D) • B.pushforward C D :=
  (rfl)

/-- The signed correspondences of the reoriented data are multiplied by `ε C ε D`. -/
@[simp]
theorem correspondence_reorient (C D : ι) :
    (B.reorient ε).correspondence C D = (ε C * ε D) • B.correspondence C D := by
  ext x
  simp only [correspondence_apply, reorient_pushforward, reorient_rank, reorient_dim,
    LinearMap.smul_apply, smul_comm (ε C * ε D)]

/-- Reversing the orientations twice restores the Bott data. -/
@[simp]
theorem reorient_reorient : (B.reorient ε).reorient ε = B := by
  cases B
  simp only [reorient, mk.injEq, true_and]
  funext C D
  rw [smul_smul, Int.units_mul_self, one_smul]

/-- **The Bott differential under a change of orientations**: negating the chains on the
components with `ε C = -1` intertwines the Bott differentials of `B` and of `B.reorient ε`. -/
theorem differential_reorient_apply (x : ∀ C, M C) (D : ι) :
    (B.reorient ε).differential (fun C ↦ ε C • x C) D = ε D • B.differential x D := by
  simp [differential_apply, smul_add, Finset.smul_sum, smul_smul, ← mul_assoc, mul_comm (ε D)]

end Reorient

section ReorientGrading

variable {R : Type*} [Ring R] {M : ι → Type*} [∀ C, AddCommGroup (M C)] [∀ C, Module R (M C)]
  (B : BottChainData R ι M) (ε : ι → ℤˣ) {S : ∀ C, ℤ → Submodule R (M C)}

@[simp]
theorem totalDegree_reorient : (B.reorient ε).totalDegree S = B.totalDegree S :=
  (rfl)

variable {B} in
/-- The reoriented pushforwards still shift the chain degree by `d_CD`, as `chainComplex`
requires. -/
theorem reorient_pushforward_mem
    (hpushforward : ∀ C D j, ∀ x ∈ S C j,
      B.pushforward C D x ∈ S D (j + bottDegreeShift B.rank C D))
    (C D : ι) (j : ℤ) (x : M C) (hx : x ∈ S C j) :
    (B.reorient ε).pushforward C D x ∈ S D (j + bottDegreeShift (B.reorient ε).rank C D) := by
  rw [reorient_pushforward, LinearMap.smul_apply, reorient_rank]
  exact (S D _).smul_of_tower_mem _ (hpushforward C D j x hx)

/-- The negation of the chains on the components with `ε C = -1`, on the total-degree piece `k`. -/
private noncomputable def reorientTotalDegreeEquiv (k : ℤ) :
    B.totalDegree S k ≃ₗ[R] (B.reorient ε).totalDegree S k :=
  (LinearEquiv.piCongrRight fun C ↦ DistribMulAction.toLinearEquiv R (M C) (ε C)).ofSubmodules _ _
    (by
      ext x
      rw [Submodule.map_equiv_eq_comap_symm, Submodule.mem_comap, totalDegree_reorient]
      simp [mem_totalDegree_iff, Submodule.smul_mem_iff'])

private theorem coe_reorientTotalDegreeEquiv_apply {k : ℤ} (x : B.totalDegree S k) :
    (B.reorientTotalDegreeEquiv ε k x : ∀ C, M C) = fun C ↦ ε C • (x : ∀ C, M C) C :=
  funext fun C ↦ by simp [reorientTotalDegreeEquiv]

private theorem coe_reorientTotalDegreeEquiv_symm_apply {k : ℤ}
    (x : (B.reorient ε).totalDegree S k) :
    ((B.reorientTotalDegreeEquiv ε k).symm x : ∀ C, M C) = fun C ↦ ε C • (x : ∀ C, M C) C :=
  funext fun C ↦ by
    simp [reorientTotalDegreeEquiv, LinearEquiv.ofSubmodules_symm_apply,
      LinearEquiv.piCongrRight_symm, Int.units_inv_eq_self]

variable (hboundary : ∀ C j, ∀ x ∈ S C j, B.boundary C x ∈ S C (j - 1))
  (hpushforward : ∀ C D j, ∀ x ∈ S C j,
    B.pushforward C D x ∈ S D (j + bottDegreeShift B.rank C D))

/-- **The Bott chain complex does not depend on the orientations of the negative-normal lines**:
negating the chains on the components with `ε C = -1` is an isomorphism from the Bott chain
complex of `B` to that of `B.reorient ε`. -/
noncomputable def chainComplexReorientIso :
    B.chainComplex hboundary hpushforward ≅
      (B.reorient ε).chainComplex (by simpa only [reorient_boundary] using hboundary)
        (reorient_pushforward_mem ε hpushforward) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun k ↦ ((B.reorientTotalDegreeEquiv ε k).toModuleIso :
      (B.chainComplex hboundary hpushforward).X k ≅ _)) <| by
    rintro _ k rfl
    ext x : 2
    refine Subtype.ext (funext fun D ↦ ?_)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
    -- The terms of `chainComplex` are the total-degree pieces only by definition, so the
    -- differentials are evaluated through `chainComplex_d_apply` on the underlying chains.
    have hd := congrFun (B.chainComplex_d_apply hboundary hpushforward k x) D
    refine (congrFun ((B.reorient ε).chainComplex_d_apply _ _ k
      (B.reorientTotalDegreeEquiv ε (k + 1) x)) D).trans ?_
    refine (congrArg (fun y ↦ (B.reorient ε).differential y D)
      (B.coe_reorientTotalDegreeEquiv_apply ε x)).trans ?_
    rw [differential_reorient_apply, ← hd]
    exact (congrFun (B.coe_reorientTotalDegreeEquiv_apply ε _) D).symm

/-- The orientation-change isomorphism negates the chains on the components with `ε C = -1`. -/
@[simp]
theorem chainComplexReorientIso_hom_f_apply (k : ℤ) (x : B.totalDegree S k) :
    (((B.chainComplexReorientIso ε hboundary hpushforward).hom.f k).hom x :
        (B.reorient ε).totalDegree S k).val = fun C ↦ ε C • x.val C :=
  B.coe_reorientTotalDegreeEquiv_apply ε x

/-- The inverse of the orientation-change isomorphism also negates the chains on the components
with `ε C = -1`. -/
@[simp]
theorem chainComplexReorientIso_inv_f_apply (k : ℤ) (x : (B.reorient ε).totalDegree S k) :
    (((B.chainComplexReorientIso ε hboundary hpushforward).inv.f k).hom x :
        B.totalDegree S k).val = fun C ↦ ε C • x.val C :=
  B.coe_reorientTotalDegreeEquiv_symm_apply ε x

end ReorientGrading

/-! ### Components without trajectories -/

/-- **Bott data without trajectories**: components with square-zero boundaries and no
trajectories between them, as for a constant function, whose only critical component is the
whole manifold. -/
def ofBoundary (rank dim : ι → ℕ) (boundary : ∀ C, M C →ₗ[R] M C)
    (hboundary : ∀ C, boundary C ∘ₗ boundary C = 0) : BottChainData R ι M where
  rank := rank
  dim := dim
  boundary := boundary
  boundary_comp_boundary := hboundary
  pushforward _ _ := 0
  boundary_comp_pushforward _ _ := by simp

section ofBoundary

variable (rank dim : ι → ℕ) (boundary : ∀ C, M C →ₗ[R] M C)
  (hboundary : ∀ C, boundary C ∘ₗ boundary C = 0)

@[simp]
theorem ofBoundary_rank : (ofBoundary rank dim boundary hboundary).rank = rank :=
  (rfl)

@[simp]
theorem ofBoundary_dim : (ofBoundary rank dim boundary hboundary).dim = dim :=
  (rfl)

@[simp]
theorem ofBoundary_boundary : (ofBoundary rank dim boundary hboundary).boundary = boundary :=
  (rfl)

@[simp]
theorem ofBoundary_pushforward (C D : ι) :
    (ofBoundary rank dim boundary hboundary).pushforward C D = 0 :=
  (rfl)

@[simp]
theorem correspondence_ofBoundary (C D : ι) :
    (ofBoundary rank dim boundary hboundary).correspondence C D = 0 := by
  simp [correspondence]

end ofBoundary

/-- Without trajectories, the Bott differential is the internal boundary `(-1)^λ_C ∂` of each
component. -/
theorem differential_ofBoundary_apply (rank dim : ι → ℕ) (boundary : ∀ C, M C →ₗ[R] M C)
    (hboundary : ∀ C, boundary C ∘ₗ boundary C = 0) (x : ∀ C, M C) (D : ι) :
    (ofBoundary rank dim boundary hboundary).differential x D =
      (rank D : ℤ).negOnePow • boundary D (x D) := by
  simp

end BottChainData

end TauCeti

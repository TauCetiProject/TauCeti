/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Bott.Complex
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Tactic.DeriveFintype
public import TauCeti.Algebra.Homology.ModuleCat.Basic

/-!
# The finite Bott models of the two-cap and four-component spheres

The Bott complex of a Morse–Bott function (`TauCeti.BottChainData`) has, on each critical
component `C`, chains placed in total degree `chain degree + λ_C`, where `λ_C` is the rank of the
negative normal bundle, and the differential `(-1)^λ_C ∂ + ∑_D F_CD` built from the trajectory
correspondences `F_CD`. This file works out the finite models of this complex for two Morse–Bott
functions on the round sphere `S² ⊂ ℝ³`, in which the chains on each component are replaced by its
homology, with zero internal boundary. A point has homology `R` in degree `0` and a circle has
homology `R` in degrees `0` and `1`, so the chains on a component of dimension `d ≤ 1` are
`Fin (d + 1) → R`, with the coordinate `i` in degree `i` (`TauCeti.coordinateGrading`).

* **Two caps.** For `f = z²` the critical components are the equator `C`, of negative-normal rank
  `0`, and the two poles, of Morse index `2`
  (`TauCeti.exists_isMorseBottFamily_sq_comp_sphereHeight`).
  The unstable orientations of the poles are chosen so that both correspondences send the generator
  of a pole to the fundamental class `[C]`
  (`TauCeti.BottChainData.correspondence_twoCapSphere_northPole_equator`). The Bott differential
  then sends the chain `a N + b S` on the poles to `(a + b) [C]`
  (`TauCeti.BottChainData.differential_twoCapSphere_equator`), so the cycles of total degree `2`
  are the multiples of `N - S`. The homology of the Bott complex
  `TauCeti.BottChainData.twoCapSphereComplex` is `R` in degrees `0` and `2` and vanishes in every
  other degree (`TauCeti.BottChainData.twoCapSphereHomologyTwoEquiv`,
  `TauCeti.BottChainData.twoCapSphereHomologyZeroEquiv`,
  `TauCeti.BottChainData.isZero_homology_twoCapSphereComplex`): the relation between the two caps
  kills `H₁(C)`. The classes of `N - S` and of the point class of the equator generate `H₂` and `H₀`
  (`TauCeti.BottChainData.twoCapSphereHomologyTwoEquiv_twoCapSphereCycleTwo`,
  `TauCeti.BottChainData.twoCapSphereHomologyZeroEquiv_twoCapSphereCycleZero`).
* **Four components.** For `f = 5z/4 - z³` and `a = √(5/12)`, the critical components in
  increasing order of value are the circle `C₀` at `z = -a`, the south pole `S`, the north pole `N`
  and the circle `C₃` at `z = a`, of negative-normal ranks `0, 2, 0, 1`
  (`TauCeti.exists_isMorseBottFamily_mul_sub_pow_three_comp_sphereHeight` for `b = 5/4`). With both
  circles oriented by increasing longitude, `ν⁻_(C₃)` by `+∂_z` and `ν⁻_S` by `dx ∧ dy`, the
  correspondences are `-φ_*` from `C₃` to `C₀`, for the identification `φ` of the circles by
  longitude, the augmentation from `C₃` to `N`, and `1 ↦ [C₀]` from `S` to `C₀`
  (`TauCeti.BottChainData.correspondence_fourComponentSphere_highCircle_lowCircle` and the next
  two lemmas). In the bases `([C₃], S)`, `(pt_(C₃), [C₀])` and `(pt_(C₀), N)` of total degrees `2`,
  `1` and `0` the Bott differential is `D₂ (a, b) = (0, b - a)` and `D₁ (c, d) = (-c, c)`
  (`TauCeti.BottChainData.differential_fourComponentSphere_lowCircle`,
  `TauCeti.BottChainData.differential_fourComponentSphere_northPole`). The homology of the Bott
  complex `TauCeti.BottChainData.fourComponentSphereComplex` is `R` in degrees `0` and `2` and
  vanishes in every other degree (`TauCeti.BottChainData.fourComponentSphereHomologyTwoEquiv`,
  `TauCeti.BottChainData.fourComponentSphereHomologyZeroEquiv`,
  `TauCeti.BottChainData.isZero_homology_fourComponentSphereComplex`); the cycles of total degree
  `2` are the multiples of `[C₃] + S`, whose class generates `H₂`, and the point class of `C₀`
  generates `H₀`
  (`TauCeti.BottChainData.fourComponentSphereHomologyTwoEquiv_fourComponentSphereCycleTwo`,
  `TauCeti.BottChainData.fourComponentSphereHomologyZeroEquiv_fourComponentSphereCycleZero`).

In total degrees `0` and `2` the homology is identified with `R` by a surjective linear form on
the cycles, built from their coefficients, that vanishes exactly on the boundaries
(`HomologicalComplex.homologyLinearEquivOfSurjective`), which sends the class of a cycle to the
value of that form on it. The computations hold over
every ring `R`. The data record the endpoint pushforwards `P_CD`, and the correspondences are
`F_CD = (-1)^g_CD P_CD` (`TauCeti.BottChainData.correspondence`); every nonzero correspondence here
has `g_CD = 1`, so `P_CD = -F_CD`. Only the models are constructed
here: identifying them with the Bott complexes of geometric chains of the two functions needs the
trajectory spaces of a rotation- and reflection-invariant metric, which this file does not use.

## Main definitions

* `TauCeti.BottChainData.twoCapSphere`, `TauCeti.BottChainData.twoCapSphereComplex`: the finite
  model of the two-cap sphere and its Bott complex.
* `TauCeti.BottChainData.fourComponentSphere`, `TauCeti.BottChainData.fourComponentSphereComplex`:
  the finite model of the four-component sphere and its Bott complex.
* `TauCeti.BottChainData.twoCapSphereHomologyTwoEquiv`,
  `TauCeti.BottChainData.twoCapSphereHomologyZeroEquiv`,
  `TauCeti.BottChainData.fourComponentSphereHomologyTwoEquiv`,
  `TauCeti.BottChainData.fourComponentSphereHomologyZeroEquiv`: the identifications of `H₂` and
  `H₀` of the two models with `R`, by coefficients of cycles.
* `TauCeti.BottChainData.twoCapSphereCycleTwo`, `TauCeti.BottChainData.twoCapSphereCycleZero`,
  `TauCeti.BottChainData.fourComponentSphereCycleTwo`,
  `TauCeti.BottChainData.fourComponentSphereCycleZero`: the generating cycles `N - S`, the point
  class of the equator, `[C₃] + S` and the point class of `C₀`.

## Main results

* `TauCeti.BottChainData.twoCapSphereHomologyTwoEquiv_twoCapSphereCycleTwo`,
  `TauCeti.BottChainData.twoCapSphereHomologyZeroEquiv_twoCapSphereCycleZero`,
  `TauCeti.BottChainData.isZero_homology_twoCapSphereComplex`: the homology of the two-cap model.
* `TauCeti.BottChainData.fourComponentSphereHomologyTwoEquiv_fourComponentSphereCycleTwo`,
  `TauCeti.BottChainData.fourComponentSphereHomologyZeroEquiv_fourComponentSphereCycleZero`,
  `TauCeti.BottChainData.isZero_homology_fourComponentSphereComplex`: the homology of the
  four-component model.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §6.2.4 (the Morse–Bott complex) and §6.2.5 (its homology).
-/

public section

open CategoryTheory CategoryTheory.Limits

namespace TauCeti

variable {R : Type*} [Ring R]

/-- **The critical components of the two-cap function** `z²` on the round sphere `S² ⊂ ℝ³`: the
equator, of negative-normal rank `0`, and the two poles, of Morse index `2`. -/
inductive TwoCapSphereComponent
  | equator
  | northPole
  | southPole
  deriving DecidableEq, Fintype

namespace TwoCapSphereComponent

/-- The negative-normal ranks `λ_C` of the critical components of `z²`: `0` for the equator and
`2` for the poles. -/
abbrev rank : TwoCapSphereComponent → ℕ
  | equator => 0
  | northPole => 2
  | southPole => 2

/-- The dimensions of the critical components of `z²`: `1` for the equator and `0` for the poles.
-/
abbrev dim : TwoCapSphereComponent → ℕ
  | equator => 1
  | northPole => 0
  | southPole => 0

private theorem univ_eq :
    (Finset.univ : Finset TwoCapSphereComponent) = {equator, northPole, southPole} := by
  decide

/-- A sum over the critical components of `z²`. -/
theorem sum_univ {M : Type*} [AddCommMonoid M] (f : TwoCapSphereComponent → M) :
    ∑ C, f C = f equator + f northPole + f southPole := by
  simp [univ_eq, add_assoc]

end TwoCapSphereComponent

namespace BottChainData

open TwoCapSphereComponent

variable (R) in
/-- **The finite Bott model of the two-cap sphere**, for `z²` on the round sphere: the chains on
each critical component are its homology, with zero boundary, and the endpoint pushforward from
each pole to the equator is `a ↦ -a [C]`, so that the correspondence sends the generator of the
pole to the fundamental class `[C]` of the equator. -/
def twoCapSphere :
    BottChainData R TwoCapSphereComponent fun C ↦ Fin (TwoCapSphereComponent.dim C + 1) → R where
  rank := TwoCapSphereComponent.rank
  dim := TwoCapSphereComponent.dim
  boundary _ := 0
  boundary_comp_boundary _ := LinearMap.zero_comp 0
  pushforward
    | northPole, equator => -(LinearMap.single R (fun _ ↦ R) 1 ∘ₗ LinearMap.proj 0)
    | southPole, equator => -(LinearMap.single R (fun _ ↦ R) 1 ∘ₗ LinearMap.proj 0)
    | _, _ => 0
  boundary_comp_pushforward C D := by
    simp only [LinearMap.zero_comp, LinearMap.comp_zero, smul_zero, zero_add]
    refine (Finset.sum_eq_zero fun E _ ↦ ?_).symm
    cases C <;> cases E <;> cases D <;> simp

@[simp]
theorem twoCapSphere_rank : (twoCapSphere R).rank = TwoCapSphereComponent.rank :=
  (rfl)

@[simp]
theorem twoCapSphere_dim : (twoCapSphere R).dim = TwoCapSphereComponent.dim :=
  (rfl)

@[simp]
theorem twoCapSphere_boundary (C : TwoCapSphereComponent) : (twoCapSphere R).boundary C = 0 :=
  (rfl)

/-- The pushforward from the north pole to the equator is `a ↦ -a [C]`. -/
@[simp]
theorem twoCapSphere_pushforward_northPole_equator :
    (twoCapSphere R).pushforward northPole equator =
      -(LinearMap.single R (fun _ ↦ R) 1 ∘ₗ LinearMap.proj 0) :=
  (rfl)

/-- The pushforward from the south pole to the equator is `a ↦ -a [C]`. -/
@[simp]
theorem twoCapSphere_pushforward_southPole_equator :
    (twoCapSphere R).pushforward southPole equator =
      -(LinearMap.single R (fun _ ↦ R) 1 ∘ₗ LinearMap.proj 0) :=
  (rfl)

/-- The pushforwards of the two-cap model out of the equator vanish: no trajectory leaves it. -/
@[simp]
theorem twoCapSphere_pushforward_equator (D : TwoCapSphereComponent) :
    (twoCapSphere R).pushforward equator D = 0 := by
  cases D <;> rfl

/-- The pushforwards of the two-cap model into a pole vanish: no trajectory ends there. -/
@[simp]
theorem twoCapSphere_pushforward_of_ne_equator (C : TwoCapSphereComponent)
    {D : TwoCapSphereComponent} (hD : D ≠ equator) : (twoCapSphere R).pushforward C D = 0 := by
  cases C <;> cases D <;> first | rfl | exact absurd rfl hD

/-- Every correspondence of the two-cap model is the negative of its pushforward. -/
theorem correspondence_twoCapSphere_eq_neg (C D : TwoCapSphereComponent) :
    (twoCapSphere R).correspondence C D = -(twoCapSphere R).pushforward C D := by
  have h (C : TwoCapSphereComponent) (hC : C ≠ equator) :
      (bottCorrespondenceExponent TwoCapSphereComponent.rank TwoCapSphereComponent.dim
        C equator).negOnePow = -1 := by
    rw [bottCorrespondenceExponent_def, bottTrajectoryDim_def]
    cases C <;> simp_all [TwoCapSphereComponent.rank, TwoCapSphereComponent.dim]
  refine LinearMap.ext fun x ↦ ?_
  rw [correspondence_apply]
  cases C <;> cases D <;> simp only [twoCapSphere, LinearMap.zero_apply, smul_zero, neg_zero,
    LinearMap.neg_apply]
  all_goals rw [h _ (by decide), Units.neg_smul, one_smul]

/-- The correspondence from the north pole to the equator sends the generator to the fundamental
class `[C]`. -/
@[simp]
theorem correspondence_twoCapSphere_northPole_equator :
    (twoCapSphere R).correspondence northPole equator =
      LinearMap.single R (fun _ ↦ R) 1 ∘ₗ LinearMap.proj 0 := by
  rw [correspondence_twoCapSphere_eq_neg]
  simp

/-- The correspondence from the south pole to the equator sends the generator to the fundamental
class `[C]`. -/
@[simp]
theorem correspondence_twoCapSphere_southPole_equator :
    (twoCapSphere R).correspondence southPole equator =
      LinearMap.single R (fun _ ↦ R) 1 ∘ₗ LinearMap.proj 0 := by
  rw [correspondence_twoCapSphere_eq_neg]
  simp

/-- **The Bott differential of the two-cap model at the equator**: the chain `a N + b S` on the
poles goes to `(a + b) [C]`.

This and the next two evaluation lemmas have high `simp` priority, so that they apply before the
general expansion `TauCeti.BottChainData.differential_apply` into a sum over the components. -/
@[simp high]
theorem differential_twoCapSphere_equator (x : ∀ C, Fin (TwoCapSphereComponent.dim C + 1) → R) :
    (twoCapSphere R).differential x equator =
      Pi.single 1 (x northPole 0 + x southPole 0) := by
  rw [differential_apply, TwoCapSphereComponent.sum_univ]
  simp only [correspondence_twoCapSphere_eq_neg]
  simp [Pi.single_add]

/-- The Bott differential of the two-cap model vanishes at the north pole: no trajectory ends
there. -/
@[simp high]
theorem differential_twoCapSphere_northPole
    (x : ∀ C, Fin (TwoCapSphereComponent.dim C + 1) → R) :
    (twoCapSphere R).differential x northPole = 0 := by
  rw [differential_apply, TwoCapSphereComponent.sum_univ]
  simp [correspondence_twoCapSphere_eq_neg]

/-- The Bott differential of the two-cap model vanishes at the south pole: no trajectory ends
there. -/
@[simp high]
theorem differential_twoCapSphere_southPole
    (x : ∀ C, Fin (TwoCapSphereComponent.dim C + 1) → R) :
    (twoCapSphere R).differential x southPole = 0 := by
  rw [differential_apply, TwoCapSphereComponent.sum_univ]
  simp [correspondence_twoCapSphere_eq_neg]

/-- The pushforwards of the two-cap model shift the coordinate grading by the chain-degree shift
`d_CD = λ_C - λ_D - 1`: from a pole to the equator, a point goes to a multiple of `[C]`. -/
theorem twoCapSphere_pushforward_mem (C D : TwoCapSphereComponent) (j : ℤ)
    (x : Fin (TwoCapSphereComponent.dim C + 1) → R)
    (hx : x ∈ coordinateGrading R (TwoCapSphereComponent.dim C) j) :
    (twoCapSphere R).pushforward C D x ∈ coordinateGrading R (TwoCapSphereComponent.dim D)
      (j + bottDegreeShift (twoCapSphere R).rank C D) := by
  cases C <;> cases D <;> simp only [twoCapSphere_pushforward_equator,
    twoCapSphere_pushforward_of_ne_equator, twoCapSphere_pushforward_northPole_equator,
    twoCapSphere_pushforward_southPole_equator, ne_eq, reduceCtorEq, not_false_eq_true,
    LinearMap.zero_apply, LinearMap.neg_apply, zero_mem]
  -- From a pole to the equator, the coordinate `0` moves to the coordinate `1`.
  all_goals
    refine neg_mem ?_
    convert single_comp_proj_mem_coordinateGrading 0 1 hx using 2
    simp [bottDegreeShift_def]

variable (R) in
/-- **The Bott complex of the two-cap model**: `R²` on the poles in total degree `2`, `H₁(C)` and
`H₀(C)` in total degrees `1` and `0`. It is exposed so that statements about its cycles can name
their coefficients. -/
@[expose] noncomputable def twoCapSphereComplex : ChainComplex (ModuleCat R) ℤ :=
  (twoCapSphere R).chainComplex (S := fun C ↦ coordinateGrading R (TwoCapSphereComponent.dim C))
    (fun C _ _ _ ↦ by simp) twoCapSphere_pushforward_mem

/-- The Bott complex of the two-cap model is the Bott chain complex of the two-cap model, graded
by coordinates. -/
theorem twoCapSphereComplex_def :
    twoCapSphereComplex R = (twoCapSphere R).chainComplex
      (S := fun C ↦ coordinateGrading R (TwoCapSphereComponent.dim C))
      (fun C _ _ _ ↦ by simp) twoCapSphere_pushforward_mem :=
  (rfl)

/-- The object of the Bott complex of the two-cap model in total degree `k` is the total-degree
piece. -/
@[simp]
theorem twoCapSphereComplex_X (k : ℤ) :
    (twoCapSphereComplex R).X k = ModuleCat.of R ((twoCapSphere R).totalDegree
      (fun C ↦ coordinateGrading R (TwoCapSphereComponent.dim C)) k) :=
  (rfl)

variable (R) in
/-- **The cycle `N - S`** of total degree `2` of the two-cap model, whose class generates `H₂`
(`TauCeti.BottChainData.twoCapSphereHomologyTwoEquiv_twoCapSphereCycleTwo`). -/
noncomputable def twoCapSphereCycleTwo : LinearMap.ker ((twoCapSphereComplex R).d 2 1).hom :=
  ⟨⟨Pi.single northPole (fun _ ↦ 1) - Pi.single southPole (fun _ ↦ 1),
    mem_totalDegree_coordinateGrading_iff.2 fun C i hi ↦ by cases C <;> fin_cases i <;> simp_all⟩,
    ((twoCapSphere R).mem_ker_chainComplex_d_iff _ _ (by norm_num) _).2
      (funext fun C ↦ by cases C <;> simp)⟩

variable (R) in
/-- The coefficient of `N` of a cycle of total degree `2` of the two-cap model. -/
private noncomputable def twoCapSphereCoeffTwo :
    LinearMap.ker ((twoCapSphereComplex R).d 2 1).hom →ₗ[R] R :=
  LinearMap.proj 0 ∘ₗ LinearMap.proj northPole ∘ₗ ((twoCapSphere R).totalDegree
    (fun C ↦ coordinateGrading R (TwoCapSphereComponent.dim C)) 2).subtype ∘ₗ
      (LinearMap.ker ((twoCapSphereComplex R).d 2 1).hom).subtype

private theorem twoCapSphereCoeffTwo_apply (z : LinearMap.ker ((twoCapSphereComplex R).d 2 1).hom) :
    twoCapSphereCoeffTwo R z = (z : (twoCapSphereComplex R).X 2).val northPole 0 :=
  (rfl)

/-- A cycle of total degree `2` of the two-cap model is a boundary exactly when its coefficient
of `N` vanishes: then the differential forces its coefficient of `S` to vanish, and nothing has
total degree `3`. -/
private theorem twoCapSphereCoeffTwo_eq_zero_iff
    (z : LinearMap.ker ((twoCapSphereComplex R).d 2 1).hom) :
    twoCapSphereCoeffTwo R z = 0 ↔
      (z : (twoCapSphereComplex R).X 2) ∈ LinearMap.range ((twoCapSphereComplex R).d 3 2).hom := by
  rw [twoCapSphereCoeffTwo_apply, (twoCapSphereComplex R).range_d_eq_bot_of_forall_eq_zero (n := 2)
      fun y ↦ Subtype.ext (eq_zero_of_mem_totalDegree_coordinateGrading y.property fun C i ↦ by
        cases C <;> fin_cases i <;> simp),
    Submodule.mem_bot]
  refine ⟨fun hN ↦ ?_, fun h ↦ by rw [h]; rfl⟩
  have hx := (z : (twoCapSphereComplex R).X 2).property
  have hS : (z : (twoCapSphereComplex R).X 2).val southPole 0 = 0 := by
    have h := congrFun (congrFun (((twoCapSphere R).mem_ker_chainComplex_d_iff _ _ (j := 1)
      (by norm_num) _).1 z.property) equator) 1
    rw [differential_twoCapSphere_equator] at h
    simpa [hN] using h
  exact Subtype.ext (funext fun C ↦ funext fun i ↦ by
    cases C <;> fin_cases i <;> simp [mem_totalDegree_coordinateGrading_iff.1 hx, hN, hS] <;> rfl)

variable (R) in
/-- **`H₂ = R` for the two-cap model**: the class of a cycle of total degree `2` goes to its
coefficient of `N`. The cycles are the multiples of `N - S`, and nothing has total degree `3`. -/
noncomputable def twoCapSphereHomologyTwoEquiv : (twoCapSphereComplex R).homology 2 ≃ₗ[R] R :=
  (twoCapSphereComplex R).homologyLinearEquivOfSurjective (m := 1) (by simp) (p := 3) (by simp)
    (twoCapSphereCoeffTwo R)
    (fun r ↦ ⟨r • twoCapSphereCycleTwo R, by
      rw [map_smul, twoCapSphereCoeffTwo_apply]
      simp [twoCapSphereCycleTwo]⟩)
    twoCapSphereCoeffTwo_eq_zero_iff

/-- The identification of `H₂` of the two-cap model with `R` sends the class of a cycle to its
coefficient of `N`. -/
@[simp]
theorem twoCapSphereHomologyTwoEquiv_moduleCatKerHomologyClass
    (z : LinearMap.ker ((twoCapSphereComplex R).d 2 1).hom) :
    twoCapSphereHomologyTwoEquiv R ((twoCapSphereComplex R).moduleCatKerHomologyClass (by simp) z) =
      (z : (twoCapSphereComplex R).X 2).val northPole 0 :=
  HomologicalComplex.homologyLinearEquivOfSurjective_moduleCatKerHomologyClass _ _ _ _ _ _ z

/-- **The class of `N - S` generates `H₂`** of the two-cap model. -/
theorem twoCapSphereHomologyTwoEquiv_twoCapSphereCycleTwo :
    twoCapSphereHomologyTwoEquiv R ((twoCapSphereComplex R).moduleCatKerHomologyClass (by simp)
      (twoCapSphereCycleTwo R)) = 1 := by
  simp [twoCapSphereCycleTwo]

variable (R) in
/-- **The point class of the equator**, a cycle of total degree `0` of the two-cap model, whose
class generates `H₀` (`TauCeti.BottChainData.twoCapSphereHomologyZeroEquiv_twoCapSphereCycleZero`).
-/
noncomputable def twoCapSphereCycleZero : LinearMap.ker ((twoCapSphereComplex R).d 0 (-1)).hom :=
  ⟨⟨Pi.single equator (Pi.single 0 1),
    mem_totalDegree_coordinateGrading_iff.2 fun C i hi ↦ by cases C <;> fin_cases i <;> simp_all⟩,
    Subtype.ext (eq_zero_of_mem_totalDegree_coordinateGrading_of_neg (Subtype.property _)
      (by norm_num))⟩

variable (R) in
/-- The coefficient of the point class of the equator of a chain of total degree `0` of the
two-cap model. -/
private noncomputable def twoCapSphereCoeffZero :
    LinearMap.ker ((twoCapSphereComplex R).d 0 (-1)).hom →ₗ[R] R :=
  LinearMap.proj 0 ∘ₗ LinearMap.proj equator ∘ₗ ((twoCapSphere R).totalDegree
    (fun C ↦ coordinateGrading R (TwoCapSphereComponent.dim C)) 0).subtype ∘ₗ
      (LinearMap.ker ((twoCapSphereComplex R).d 0 (-1)).hom).subtype

private theorem twoCapSphereCoeffZero_apply
    (z : LinearMap.ker ((twoCapSphereComplex R).d 0 (-1)).hom) :
    twoCapSphereCoeffZero R z = (z : (twoCapSphereComplex R).X 0).val equator 0 :=
  (rfl)

/-- A chain of total degree `0` of the two-cap model is a boundary exactly when its coefficient of
the point class of the equator vanishes: the Bott differential lands in multiples of `[C]`. -/
private theorem twoCapSphereCoeffZero_eq_zero_iff
    (z : LinearMap.ker ((twoCapSphereComplex R).d 0 (-1)).hom) :
    twoCapSphereCoeffZero R z = 0 ↔
      (z : (twoCapSphereComplex R).X 0) ∈ LinearMap.range ((twoCapSphereComplex R).d 1 0).hom := by
  rw [twoCapSphereCoeffZero_apply]
  have hx := (z : (twoCapSphereComplex R).X 0).property
  refine ⟨fun hE ↦ ?_, fun ⟨y, hy⟩ ↦ ?_⟩
  · obtain h : (z : (twoCapSphereComplex R).X 0) = 0 := Subtype.ext (funext fun C ↦ funext fun i ↦
      by cases C <;> fin_cases i <;> simp [mem_totalDegree_coordinateGrading_iff.1 hx, hE] <;> rfl)
    rw [h]
    exact zero_mem _
  · have hd : (((twoCapSphereComplex R).d 1 0).hom y).val = (twoCapSphere R).differential y.val :=
      chainComplex_d_apply_of_eq_add_one _ _ _ (by norm_num) y
    rw [← hy, hd]
    simp

variable (R) in
/-- **`H₀ = R` for the two-cap model**: the class of a chain of total degree `0` goes to its
coefficient of the point class of the equator. -/
noncomputable def twoCapSphereHomologyZeroEquiv : (twoCapSphereComplex R).homology 0 ≃ₗ[R] R :=
  (twoCapSphereComplex R).homologyLinearEquivOfSurjective (m := -1) (by simp) (p := 1) (by simp)
    (twoCapSphereCoeffZero R)
    (fun r ↦ ⟨r • twoCapSphereCycleZero R, by
      rw [map_smul, twoCapSphereCoeffZero_apply]
      simp [twoCapSphereCycleZero]⟩)
    twoCapSphereCoeffZero_eq_zero_iff

/-- The identification of `H₀` of the two-cap model with `R` sends the class of a chain to its
coefficient of the point class of the equator. -/
@[simp]
theorem twoCapSphereHomologyZeroEquiv_moduleCatKerHomologyClass
    (z : LinearMap.ker ((twoCapSphereComplex R).d 0 (-1)).hom) :
    twoCapSphereHomologyZeroEquiv R ((twoCapSphereComplex R).moduleCatKerHomologyClass (by simp)
      z) = (z : (twoCapSphereComplex R).X 0).val equator 0 :=
  HomologicalComplex.homologyLinearEquivOfSurjective_moduleCatKerHomologyClass _ _ _ _ _ _ z

/-- **The point class of the equator generates `H₀`** of the two-cap model. -/
theorem twoCapSphereHomologyZeroEquiv_twoCapSphereCycleZero :
    twoCapSphereHomologyZeroEquiv R ((twoCapSphereComplex R).moduleCatKerHomologyClass (by simp)
      (twoCapSphereCycleZero R)) = 1 := by
  simp [twoCapSphereCycleZero]

/-- **The other homology groups of the two-cap model vanish.** In total degree `1` the class
`[C]` is the boundary of the north pole; no other degree carries chains. -/
theorem isZero_homology_twoCapSphereComplex {k : ℤ} (h0 : k ≠ 0) (h2 : k ≠ 2) :
    IsZero ((twoCapSphereComplex R).homology k) := by
  set K := twoCapSphereComplex R
  refine HomologicalComplex.ExactAt.isZero_homology ?_
  rw [K.exactAt_iff' (k + 1) k (k - 1) (by simp) (by simp), ShortComplex.moduleCat_exact_iff]
  rintro ⟨x, hx⟩ -
  by_cases h1 : k = 1
  · -- In total degree `1` the cycle `a [equator]` bounds `a • northPole`.
    subst h1
    let y : ∀ C, Fin (TwoCapSphereComponent.dim C + 1) → R :=
      Pi.single northPole (fun _ ↦ x equator 1)
    have hy : y ∈ (twoCapSphere R).totalDegree
        (fun C ↦ coordinateGrading R (TwoCapSphereComponent.dim C)) (1 + 1) := by
      refine mem_totalDegree_coordinateGrading_iff.2 fun C i hi ↦ ?_
      cases C <;> fin_cases i <;> simp_all [y]
    have hd : ((K.d (1 + 1) 1).hom ⟨y, hy⟩).val = (twoCapSphere R).differential y :=
      chainComplex_d_apply_of_eq_add_one _ _ _ rfl _
    refine ⟨⟨y, hy⟩, Subtype.ext (hd.trans ?_)⟩
    funext C i
    cases C <;> fin_cases i <;> simp [y, mem_totalDegree_coordinateGrading_iff.1 hx]
  · -- Otherwise there are no chains of total degree `k`.
    refine ⟨0, Subtype.ext ?_⟩
    rw [map_zero]
    exact (eq_zero_of_mem_totalDegree_coordinateGrading hx fun C i ↦ by
      cases C <;> fin_cases i <;> simp <;> omega).symm

end BottChainData

/-- **The critical components of the four-component function** `5z/4 - z³` on the round sphere
`S² ⊂ ℝ³`, in increasing order of critical value: the circle `C₀` at `z = -a`, the south pole `S`,
the north pole `N` and the circle `C₃` at `z = a`, for `a = √(5/12)`. -/
inductive FourComponentSphereComponent
  | lowCircle
  | southPole
  | northPole
  | highCircle
  deriving DecidableEq, Fintype

namespace FourComponentSphereComponent

/-- The negative-normal ranks `λ_C` of the critical components of `5z/4 - z³`: `0, 2, 0, 1` for
`C₀, S, N, C₃`. -/
abbrev rank : FourComponentSphereComponent → ℕ
  | lowCircle => 0
  | southPole => 2
  | northPole => 0
  | highCircle => 1

/-- The dimensions of the critical components of `5z/4 - z³`: `1` for the circles and `0` for the
poles. -/
abbrev dim : FourComponentSphereComponent → ℕ
  | lowCircle => 1
  | southPole => 0
  | northPole => 0
  | highCircle => 1

private theorem univ_eq : (Finset.univ : Finset FourComponentSphereComponent) =
    {lowCircle, southPole, northPole, highCircle} := by
  decide

/-- A sum over the critical components of `5z/4 - z³`. -/
theorem sum_univ {M : Type*} [AddCommMonoid M] (f : FourComponentSphereComponent → M) :
    ∑ C, f C = f lowCircle + f southPole + f northPole + f highCircle := by
  simp [univ_eq, add_assoc]

end FourComponentSphereComponent

namespace BottChainData

open FourComponentSphereComponent

variable (R) in
/-- **The finite Bott model of the four-component sphere**, for `5z/4 - z³` on the round sphere:
the chains on each critical component are its homology, with zero boundary, and the endpoint
pushforwards are the identification `φ_*` of the circles from `C₃` to `C₀`, minus the
augmentation from `C₃` to `N`, and `a ↦ -a [C₀]` from `S` to `C₀`. -/
def fourComponentSphere : BottChainData R FourComponentSphereComponent
    fun C ↦ Fin (FourComponentSphereComponent.dim C + 1) → R where
  rank := FourComponentSphereComponent.rank
  dim := FourComponentSphereComponent.dim
  boundary _ := 0
  boundary_comp_boundary _ := LinearMap.zero_comp 0
  pushforward
    | highCircle, lowCircle => LinearMap.id
    | highCircle, northPole => -LinearMap.pi fun _ ↦ LinearMap.proj 0
    | southPole, lowCircle => -(LinearMap.single R (fun _ ↦ R) 1 ∘ₗ LinearMap.proj 0)
    | _, _ => 0
  boundary_comp_pushforward C D := by
    simp only [LinearMap.zero_comp, LinearMap.comp_zero, smul_zero, zero_add]
    refine (Finset.sum_eq_zero fun E _ ↦ ?_).symm
    cases C <;> cases E <;> cases D <;> simp

@[simp]
theorem fourComponentSphere_rank :
    (fourComponentSphere R).rank = FourComponentSphereComponent.rank :=
  (rfl)

@[simp]
theorem fourComponentSphere_dim : (fourComponentSphere R).dim = FourComponentSphereComponent.dim :=
  (rfl)

@[simp]
theorem fourComponentSphere_boundary (C : FourComponentSphereComponent) :
    (fourComponentSphere R).boundary C = 0 :=
  (rfl)

/-- The pushforward from `C₃` to `C₀` is the identification `φ_*` of the circles by longitude. -/
@[simp]
theorem fourComponentSphere_pushforward_highCircle_lowCircle :
    (fourComponentSphere R).pushforward highCircle lowCircle = LinearMap.id :=
  (rfl)

/-- The pushforward from `C₃` to `N` is minus the augmentation. -/
@[simp]
theorem fourComponentSphere_pushforward_highCircle_northPole :
    (fourComponentSphere R).pushforward highCircle northPole =
      -LinearMap.pi fun _ ↦ LinearMap.proj 0 :=
  (rfl)

/-- The pushforward from `S` to `C₀` is `a ↦ -a [C₀]`. -/
@[simp]
theorem fourComponentSphere_pushforward_southPole_lowCircle :
    (fourComponentSphere R).pushforward southPole lowCircle =
      -(LinearMap.single R (fun _ ↦ R) 1 ∘ₗ LinearMap.proj 0) :=
  (rfl)

/-- The pushforwards of the four-component model out of `C₀` vanish: no trajectory leaves it. -/
@[simp]
theorem fourComponentSphere_pushforward_lowCircle (D : FourComponentSphereComponent) :
    (fourComponentSphere R).pushforward lowCircle D = 0 := by
  cases D <;> rfl

/-- The pushforwards of the four-component model out of `N` vanish: no trajectory leaves it. -/
@[simp]
theorem fourComponentSphere_pushforward_northPole (D : FourComponentSphereComponent) :
    (fourComponentSphere R).pushforward northPole D = 0 := by
  cases D <;> rfl

/-- The pushforwards of the four-component model from `S` vanish except into `C₀`. -/
@[simp]
theorem fourComponentSphere_pushforward_southPole_of_ne_lowCircle
    {D : FourComponentSphereComponent} (hD : D ≠ lowCircle) :
    (fourComponentSphere R).pushforward southPole D = 0 := by
  cases D <;> first | rfl | exact absurd rfl hD

/-- The pushforward of the four-component model from `C₃` to `S` vanishes. -/
@[simp]
theorem fourComponentSphere_pushforward_highCircle_southPole :
    (fourComponentSphere R).pushforward highCircle southPole = 0 :=
  (rfl)

/-- The pushforward of the four-component model from `C₃` to itself vanishes. -/
@[simp]
theorem fourComponentSphere_pushforward_highCircle_highCircle :
    (fourComponentSphere R).pushforward highCircle highCircle = 0 :=
  (rfl)

/-- Every correspondence of the four-component model is the negative of its pushforward. -/
theorem correspondence_fourComponentSphere_eq_neg (C D : FourComponentSphereComponent) :
    (fourComponentSphere R).correspondence C D = -(fourComponentSphere R).pushforward C D := by
  have h (C D : FourComponentSphereComponent) (hCD : bottCorrespondenceExponent
      FourComponentSphereComponent.rank FourComponentSphereComponent.dim C D = 1) :
      (bottCorrespondenceExponent FourComponentSphereComponent.rank
        FourComponentSphereComponent.dim C D).negOnePow = -1 := by
    rw [hCD, Int.negOnePow_one]
  refine LinearMap.ext fun x ↦ ?_
  rw [correspondence_apply]
  cases C <;> cases D <;> simp only [fourComponentSphere, LinearMap.zero_apply, smul_zero,
    neg_zero, LinearMap.neg_apply]
  all_goals rw [h _ _ (by rw [bottCorrespondenceExponent_def, bottTrajectoryDim_def]; norm_num),
    Units.neg_smul, one_smul]

/-- The correspondence from `C₃` to `C₀` is `-φ_*`. -/
@[simp]
theorem correspondence_fourComponentSphere_highCircle_lowCircle :
    (fourComponentSphere R).correspondence highCircle lowCircle = -LinearMap.id := by
  rw [correspondence_fourComponentSphere_eq_neg]
  simp

/-- The correspondence from `C₃` to `N` is the augmentation, which keeps the coefficient of the
point class. -/
@[simp]
theorem correspondence_fourComponentSphere_highCircle_northPole :
    (fourComponentSphere R).correspondence highCircle northPole =
      LinearMap.pi fun _ ↦ LinearMap.proj 0 := by
  rw [correspondence_fourComponentSphere_eq_neg]
  simp

/-- The correspondence from `S` to `C₀` sends the generator to the fundamental class `[C₀]`. -/
@[simp]
theorem correspondence_fourComponentSphere_southPole_lowCircle :
    (fourComponentSphere R).correspondence southPole lowCircle =
      LinearMap.single R (fun _ ↦ R) 1 ∘ₗ LinearMap.proj 0 := by
  rw [correspondence_fourComponentSphere_eq_neg]
  simp

/-- **The Bott differential of the four-component model at `C₀`**: `b S` and `x` on `C₃` go to
`b [C₀] - φ_* x`.

This and the next three evaluation lemmas have high `simp` priority, so that they apply before the
general expansion `TauCeti.BottChainData.differential_apply` into a sum over the components. -/
@[simp high]
theorem differential_fourComponentSphere_lowCircle
    (x : ∀ C, Fin (FourComponentSphereComponent.dim C + 1) → R) :
    (fourComponentSphere R).differential x lowCircle =
      Pi.single 1 (x southPole 0) - x highCircle := by
  rw [differential_apply, FourComponentSphereComponent.sum_univ]
  simp only [correspondence_fourComponentSphere_eq_neg]
  simp [sub_eq_add_neg]

/-- **The Bott differential of the four-component model at `N`**: the coefficient of the point
class of `C₃`. -/
@[simp high]
theorem differential_fourComponentSphere_northPole
    (x : ∀ C, Fin (FourComponentSphereComponent.dim C + 1) → R) :
    (fourComponentSphere R).differential x northPole = fun _ ↦ x highCircle 0 := by
  rw [differential_apply, FourComponentSphereComponent.sum_univ]
  simp only [correspondence_fourComponentSphere_eq_neg]
  funext i
  simp

/-- The Bott differential of the four-component model vanishes at `S`: no trajectory ends there.
-/
@[simp high]
theorem differential_fourComponentSphere_southPole
    (x : ∀ C, Fin (FourComponentSphereComponent.dim C + 1) → R) :
    (fourComponentSphere R).differential x southPole = 0 := by
  rw [differential_apply, FourComponentSphereComponent.sum_univ]
  simp [correspondence_fourComponentSphere_eq_neg]

/-- The Bott differential of the four-component model vanishes at `C₃`: no trajectory ends there.
-/
@[simp high]
theorem differential_fourComponentSphere_highCircle
    (x : ∀ C, Fin (FourComponentSphereComponent.dim C + 1) → R) :
    (fourComponentSphere R).differential x highCircle = 0 := by
  rw [differential_apply, FourComponentSphereComponent.sum_univ]
  simp [correspondence_fourComponentSphere_eq_neg]

/-- The pushforwards of the four-component model shift the coordinate grading by the chain-degree
shift `d_CD = λ_C - λ_D - 1`. -/
theorem fourComponentSphere_pushforward_mem (C D : FourComponentSphereComponent) (j : ℤ)
    (x : Fin (FourComponentSphereComponent.dim C + 1) → R)
    (hx : x ∈ coordinateGrading R (FourComponentSphereComponent.dim C) j) :
    (fourComponentSphere R).pushforward C D x ∈
      coordinateGrading R (FourComponentSphereComponent.dim D)
        (j + bottDegreeShift (fourComponentSphere R).rank C D) := by
  cases C <;> cases D <;> simp only [fourComponentSphere_pushforward_lowCircle,
    fourComponentSphere_pushforward_northPole,
    fourComponentSphere_pushforward_southPole_of_ne_lowCircle,
    fourComponentSphere_pushforward_highCircle_southPole,
    fourComponentSphere_pushforward_highCircle_highCircle,
    fourComponentSphere_pushforward_southPole_lowCircle,
    fourComponentSphere_pushforward_highCircle_lowCircle,
    fourComponentSphere_pushforward_highCircle_northPole, ne_eq, reduceCtorEq, not_false_eq_true,
    LinearMap.zero_apply, LinearMap.neg_apply, LinearMap.id_apply, zero_mem]
  · -- From the south pole to the low circle, the coordinate `0` moves to the coordinate `1`.
    refine neg_mem ?_
    convert single_comp_proj_mem_coordinateGrading 0 1 hx using 2
    simp [bottDegreeShift_def]
  · simpa [bottDegreeShift_def] using hx
  · refine neg_mem ?_
    rw [mem_coordinateGrading_iff] at hx ⊢
    intro i hi
    fin_cases i
    simpa using hx 0 (by simpa [bottDegreeShift_def] using hi)

variable (R) in
/-- **The Bott complex of the four-component model**: `([C₃], S)`, `(pt_(C₃), [C₀])` and
`(pt_(C₀), N)` in total degrees `2`, `1` and `0`. It is exposed so that statements about its cycles
can name their coefficients. -/
@[expose] noncomputable def fourComponentSphereComplex : ChainComplex (ModuleCat R) ℤ :=
  (fourComponentSphere R).chainComplex
    (S := fun C ↦ coordinateGrading R (FourComponentSphereComponent.dim C))
    (fun C _ _ _ ↦ by simp) fourComponentSphere_pushforward_mem

/-- The Bott complex of the four-component model is the Bott chain complex of the four-component
model, graded by coordinates. -/
theorem fourComponentSphereComplex_def :
    fourComponentSphereComplex R = (fourComponentSphere R).chainComplex
      (S := fun C ↦ coordinateGrading R (FourComponentSphereComponent.dim C))
      (fun C _ _ _ ↦ by simp) fourComponentSphere_pushforward_mem :=
  (rfl)

/-- The object of the Bott complex of the four-component model in total degree `k` is the
total-degree piece. -/
@[simp]
theorem fourComponentSphereComplex_X (k : ℤ) :
    (fourComponentSphereComplex R).X k = ModuleCat.of R ((fourComponentSphere R).totalDegree
      (fun C ↦ coordinateGrading R (FourComponentSphereComponent.dim C)) k) :=
  (rfl)

variable (R) in
/-- **The cycle `[C₃] + S`** of total degree `2` of the four-component model, whose class generates
`H₂` (`TauCeti.BottChainData.fourComponentSphereHomologyTwoEquiv_fourComponentSphereCycleTwo`). -/
noncomputable def fourComponentSphereCycleTwo :
    LinearMap.ker ((fourComponentSphereComplex R).d 2 1).hom :=
  ⟨⟨Pi.single highCircle (Pi.single 1 1) + Pi.single southPole (fun _ ↦ 1),
    mem_totalDegree_coordinateGrading_iff.2 fun C i hi ↦ by cases C <;> fin_cases i <;> simp_all⟩,
    ((fourComponentSphere R).mem_ker_chainComplex_d_iff _ _ (by norm_num) _).2
      (funext fun C ↦ by cases C <;> simp [funext_iff])⟩

variable (R) in
/-- The coefficient of `[C₃]` of a cycle of total degree `2` of the four-component model. -/
private noncomputable def fourComponentSphereCoeffTwo :
    LinearMap.ker ((fourComponentSphereComplex R).d 2 1).hom →ₗ[R] R :=
  LinearMap.proj 1 ∘ₗ LinearMap.proj highCircle ∘ₗ ((fourComponentSphere R).totalDegree
    (fun C ↦ coordinateGrading R (FourComponentSphereComponent.dim C)) 2).subtype ∘ₗ
      (LinearMap.ker ((fourComponentSphereComplex R).d 2 1).hom).subtype

private theorem fourComponentSphereCoeffTwo_apply
    (z : LinearMap.ker ((fourComponentSphereComplex R).d 2 1).hom) :
    fourComponentSphereCoeffTwo R z = (z : (fourComponentSphereComplex R).X 2).val highCircle 1 :=
  (rfl)

/-- A cycle of total degree `2` of the four-component model is a boundary exactly when its
coefficient of `[C₃]` vanishes: then the differential forces its coefficient of `S` to vanish, and
nothing has total degree `3`. -/
private theorem fourComponentSphereCoeffTwo_eq_zero_iff
    (z : LinearMap.ker ((fourComponentSphereComplex R).d 2 1).hom) :
    fourComponentSphereCoeffTwo R z = 0 ↔ (z : (fourComponentSphereComplex R).X 2) ∈
      LinearMap.range ((fourComponentSphereComplex R).d 3 2).hom := by
  rw [fourComponentSphereCoeffTwo_apply,
    (fourComponentSphereComplex R).range_d_eq_bot_of_forall_eq_zero (n := 2) fun y ↦ Subtype.ext
      (eq_zero_of_mem_totalDegree_coordinateGrading y.property fun C i ↦ by
        cases C <;> fin_cases i <;> simp),
    Submodule.mem_bot]
  refine ⟨fun hC ↦ ?_, fun h ↦ by rw [h]; rfl⟩
  have hx := (z : (fourComponentSphereComplex R).X 2).property
  have hS : (z : (fourComponentSphereComplex R).X 2).val southPole 0 = 0 := by
    have h := congrFun (congrFun (((fourComponentSphere R).mem_ker_chainComplex_d_iff _ _ (j := 1)
      (by norm_num) _).1 z.property) lowCircle) 1
    rw [differential_fourComponentSphere_lowCircle] at h
    simpa [hC] using h
  exact Subtype.ext (funext fun C ↦ funext fun i ↦ by
    cases C <;> fin_cases i <;> simp [mem_totalDegree_coordinateGrading_iff.1 hx, hS, hC] <;> rfl)

variable (R) in
/-- **`H₂ = R` for the four-component model**: the class of a cycle of total degree `2` goes to its
coefficient of `[C₃]`. The cycles are the multiples of `[C₃] + S`, and nothing has total
degree `3`. -/
noncomputable def fourComponentSphereHomologyTwoEquiv :
    (fourComponentSphereComplex R).homology 2 ≃ₗ[R] R :=
  (fourComponentSphereComplex R).homologyLinearEquivOfSurjective (m := 1) (by simp) (p := 3)
    (by simp) (fourComponentSphereCoeffTwo R)
    (fun r ↦ ⟨r • fourComponentSphereCycleTwo R, by
      rw [map_smul, fourComponentSphereCoeffTwo_apply]
      simp [fourComponentSphereCycleTwo]⟩)
    fourComponentSphereCoeffTwo_eq_zero_iff

/-- The identification of `H₂` of the four-component model with `R` sends the class of a cycle to
its coefficient of `[C₃]`. -/
@[simp]
theorem fourComponentSphereHomologyTwoEquiv_moduleCatKerHomologyClass
    (z : LinearMap.ker ((fourComponentSphereComplex R).d 2 1).hom) :
    fourComponentSphereHomologyTwoEquiv R
        ((fourComponentSphereComplex R).moduleCatKerHomologyClass (by simp) z) =
      (z : (fourComponentSphereComplex R).X 2).val highCircle 1 :=
  HomologicalComplex.homologyLinearEquivOfSurjective_moduleCatKerHomologyClass _ _ _ _ _ _ z

/-- **The class of `[C₃] + S` generates `H₂`** of the four-component model. -/
theorem fourComponentSphereHomologyTwoEquiv_fourComponentSphereCycleTwo :
    fourComponentSphereHomologyTwoEquiv R ((fourComponentSphereComplex R).moduleCatKerHomologyClass
      (by simp) (fourComponentSphereCycleTwo R)) = 1 := by
  simp [fourComponentSphereCycleTwo]

variable (R) in
/-- **The point class of `C₀`**, a cycle of total degree `0` of the four-component model, whose
class generates `H₀`
(`TauCeti.BottChainData.fourComponentSphereHomologyZeroEquiv_fourComponentSphereCycleZero`). -/
noncomputable def fourComponentSphereCycleZero :
    LinearMap.ker ((fourComponentSphereComplex R).d 0 (-1)).hom :=
  ⟨⟨Pi.single lowCircle (Pi.single 0 1),
    mem_totalDegree_coordinateGrading_iff.2 fun C i hi ↦ by cases C <;> fin_cases i <;> simp_all⟩,
    Subtype.ext (eq_zero_of_mem_totalDegree_coordinateGrading_of_neg (Subtype.property _)
      (by norm_num))⟩

variable (R) in
/-- The sum of the coefficients of the point classes of `C₀` and of `N` of a chain of total degree
`0` of the four-component model. -/
private noncomputable def fourComponentSphereCoeffZero :
    LinearMap.ker ((fourComponentSphereComplex R).d 0 (-1)).hom →ₗ[R] R :=
  LinearMap.proj 0 ∘ₗ LinearMap.proj lowCircle ∘ₗ ((fourComponentSphere R).totalDegree
      (fun C ↦ coordinateGrading R (FourComponentSphereComponent.dim C)) 0).subtype ∘ₗ
        (LinearMap.ker ((fourComponentSphereComplex R).d 0 (-1)).hom).subtype +
    LinearMap.proj 0 ∘ₗ LinearMap.proj northPole ∘ₗ ((fourComponentSphere R).totalDegree
      (fun C ↦ coordinateGrading R (FourComponentSphereComponent.dim C)) 0).subtype ∘ₗ
        (LinearMap.ker ((fourComponentSphereComplex R).d 0 (-1)).hom).subtype

private theorem fourComponentSphereCoeffZero_apply
    (z : LinearMap.ker ((fourComponentSphereComplex R).d 0 (-1)).hom) :
    fourComponentSphereCoeffZero R z = (z : (fourComponentSphereComplex R).X 0).val lowCircle 0 +
      (z : (fourComponentSphereComplex R).X 0).val northPole 0 :=
  (rfl)

/-- A chain of total degree `0` of the four-component model whose coefficients at the point classes
of `C₀` and `N` add up to zero is the boundary of a chain of total degree `1`, a multiple of the
point class of `C₃`. -/
private theorem fourComponentSphere_exists_differential_eq
    {x : ∀ C, Fin (FourComponentSphereComponent.dim C + 1) → R}
    (hx : x ∈ (fourComponentSphere R).totalDegree
      (fun C ↦ coordinateGrading R (FourComponentSphereComponent.dim C)) 0)
    (hz : x lowCircle 0 + x northPole 0 = 0) :
    ∃ y ∈ (fourComponentSphere R).totalDegree
      (fun C ↦ coordinateGrading R (FourComponentSphereComponent.dim C)) 1,
      (fourComponentSphere R).differential y = x := by
  refine ⟨Pi.single highCircle (Pi.single 0 (x northPole 0)),
    mem_totalDegree_coordinateGrading_iff.2 fun C i hi ↦ ?_, funext fun C ↦ funext fun i ↦ ?_⟩
  · cases C <;> fin_cases i <;> simp_all
  · cases C <;> fin_cases i <;>
      simp [mem_totalDegree_coordinateGrading_iff.1 hx, eq_neg_of_add_eq_zero_left hz]

/-- A chain of total degree `0` of the four-component model is a boundary exactly when its
coefficients at the point classes of `C₀` and `N` add up to zero: the boundaries are the multiples
of `N - pt_(C₀)`. -/
private theorem fourComponentSphereCoeffZero_eq_zero_iff
    (z : LinearMap.ker ((fourComponentSphereComplex R).d 0 (-1)).hom) :
    fourComponentSphereCoeffZero R z = 0 ↔ (z : (fourComponentSphereComplex R).X 0) ∈
      LinearMap.range ((fourComponentSphereComplex R).d 1 0).hom := by
  have hd (y : (fourComponentSphereComplex R).X 1) :
      (((fourComponentSphereComplex R).d 1 0).hom y).val =
        (fourComponentSphere R).differential y.val :=
    chainComplex_d_apply_of_eq_add_one _ _ _ (by norm_num) y
  rw [fourComponentSphereCoeffZero_apply]
  refine ⟨fun hz ↦ ?_, fun ⟨y, hy⟩ ↦ ?_⟩
  · obtain ⟨y, hy, hdy⟩ := fourComponentSphere_exists_differential_eq
      (z : (fourComponentSphereComplex R).X 0).property hz
    exact ⟨⟨y, hy⟩, Subtype.ext ((hd ⟨y, hy⟩).trans hdy)⟩
  · -- The boundary of `c` times the point class of `C₃` is `c (N - pt_(C₀))`.
    rw [← hy, hd]
    simp

variable (R) in
/-- **`H₀ = R` for the four-component model**: the class of a chain of total degree `0` goes to the
sum of its coefficients at the point classes of `C₀` and `N`, since the boundaries are the
multiples of `N - pt_(C₀)`. -/
noncomputable def fourComponentSphereHomologyZeroEquiv :
    (fourComponentSphereComplex R).homology 0 ≃ₗ[R] R :=
  (fourComponentSphereComplex R).homologyLinearEquivOfSurjective (m := -1) (by simp) (p := 1)
    (by simp) (fourComponentSphereCoeffZero R)
    (fun r ↦ ⟨r • fourComponentSphereCycleZero R, by
      rw [map_smul, fourComponentSphereCoeffZero_apply]
      simp [fourComponentSphereCycleZero]⟩)
    fourComponentSphereCoeffZero_eq_zero_iff

/-- The identification of `H₀` of the four-component model with `R` sends the class of a chain to
the sum of its coefficients at the point classes of `C₀` and `N`. -/
@[simp]
theorem fourComponentSphereHomologyZeroEquiv_moduleCatKerHomologyClass
    (z : LinearMap.ker ((fourComponentSphereComplex R).d 0 (-1)).hom) :
    fourComponentSphereHomologyZeroEquiv R
        ((fourComponentSphereComplex R).moduleCatKerHomologyClass (by simp) z) =
      (z : (fourComponentSphereComplex R).X 0).val lowCircle 0 +
        (z : (fourComponentSphereComplex R).X 0).val northPole 0 :=
  HomologicalComplex.homologyLinearEquivOfSurjective_moduleCatKerHomologyClass _ _ _ _ _ _ z

/-- **The point class of `C₀` generates `H₀`** of the four-component model. -/
theorem fourComponentSphereHomologyZeroEquiv_fourComponentSphereCycleZero :
    fourComponentSphereHomologyZeroEquiv R
      ((fourComponentSphereComplex R).moduleCatKerHomologyClass (by simp)
        (fourComponentSphereCycleZero R)) = 1 := by
  simp [fourComponentSphereCycleZero]

/-- **The other homology groups of the four-component model vanish.** In total degree `1` a cycle
is a multiple of `[C₀]`, the boundary of a multiple of `S`; no other degree carries chains. -/
theorem isZero_homology_fourComponentSphereComplex {k : ℤ} (h0 : k ≠ 0) (h2 : k ≠ 2) :
    IsZero ((fourComponentSphereComplex R).homology k) := by
  set K := fourComponentSphereComplex R
  refine HomologicalComplex.ExactAt.isZero_homology ?_
  rw [K.exactAt_iff' (k + 1) k (k - 1) (by simp) (by simp), ShortComplex.moduleCat_exact_iff]
  rintro ⟨x, hx⟩ hdx
  by_cases h1 : k = 1
  · -- A cycle of total degree `1` is `d [C₀]`, the boundary of `d S`.
    subst h1
    have hdx' : (fourComponentSphere R).differential x = 0 :=
      ((fourComponentSphere R).mem_ker_chainComplex_d_iff (fun C _ _ _ ↦ by simp)
        fourComponentSphere_pushforward_mem (j := 1 - 1) (by norm_num) ⟨x, hx⟩).1 hdx
    have hC : x highCircle 0 = 0 := by
      have h := congrFun (congrFun hdx' northPole) 0
      rw [differential_fourComponentSphere_northPole] at h
      exact h
    let y : ∀ C, Fin (FourComponentSphereComponent.dim C + 1) → R :=
      Pi.single southPole (fun _ ↦ x lowCircle 1)
    have hy : y ∈ (fourComponentSphere R).totalDegree
        (fun C ↦ coordinateGrading R (FourComponentSphereComponent.dim C)) (1 + 1) := by
      refine mem_totalDegree_coordinateGrading_iff.2 fun C i hi ↦ ?_
      cases C <;> fin_cases i <;> simp_all [y]
    have hd : ((K.d (1 + 1) 1).hom ⟨y, hy⟩).val = (fourComponentSphere R).differential y :=
      chainComplex_d_apply_of_eq_add_one _ _ _ rfl _
    refine ⟨⟨y, hy⟩, Subtype.ext (hd.trans ?_)⟩
    funext C i
    cases C <;> fin_cases i <;> simp [y, mem_totalDegree_coordinateGrading_iff.1 hx, hC]
  · -- Otherwise there are no chains of total degree `k`.
    refine ⟨0, Subtype.ext ?_⟩
    rw [map_zero]
    exact (eq_zero_of_mem_totalDegree_coordinateGrading hx fun C i ↦ by
      cases C <;> fin_cases i <;> simp <;> omega).symm

end BottChainData

end TauCeti

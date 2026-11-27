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
  other degree (`TauCeti.BottChainData.nonempty_linearEquiv_homology_two_twoCapSphereComplex`,
  `TauCeti.BottChainData.nonempty_linearEquiv_homology_zero_twoCapSphereComplex`,
  `TauCeti.BottChainData.isZero_homology_twoCapSphereComplex`): the relation between the two caps
  kills `H₁(C)`.
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
  vanishes in every other degree; the cycles of total degree `2` are the multiples of
  `[C₃] + S`.

The computations hold over every ring `R`. The data record the endpoint pushforwards `P_CD`, and
the correspondences are `F_CD = (-1)^g_CD P_CD` (`TauCeti.BottChainData.correspondence`); every
nonzero correspondence here has `g_CD = 1`, so `P_CD = -F_CD`. Only the models are constructed
here: identifying them with the Bott complexes of geometric chains of the two functions needs the
trajectory spaces of a rotation- and reflection-invariant metric, which this file does not use.

## Main definitions

* `TauCeti.coordinateGrading`: the grading of `Fin (d + 1) → R` by coordinates.
* `TauCeti.BottChainData.twoCapSphere`, `TauCeti.BottChainData.twoCapSphereComplex`: the finite
  model of the two-cap sphere and its Bott complex.
* `TauCeti.BottChainData.fourComponentSphere`, `TauCeti.BottChainData.fourComponentSphereComplex`:
  the finite model of the four-component sphere and its Bott complex.

## Main results

* `TauCeti.BottChainData.nonempty_linearEquiv_homology_two_twoCapSphereComplex`,
  `TauCeti.BottChainData.nonempty_linearEquiv_homology_zero_twoCapSphereComplex`,
  `TauCeti.BottChainData.isZero_homology_twoCapSphereComplex`: the homology of the two-cap model.
* `TauCeti.BottChainData.nonempty_linearEquiv_homology_two_fourComponentSphereComplex`,
  `TauCeti.BottChainData.nonempty_linearEquiv_homology_zero_fourComponentSphereComplex`,
  `TauCeti.BottChainData.isZero_homology_fourComponentSphereComplex`: the homology of the
  four-component model.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §6.2.4 (the Morse–Bott complex) and §6.2.5 (its homology).
-/

public section

open CategoryTheory CategoryTheory.Limits

namespace TauCeti

section CoordinateGrading

variable (R : Type*) [Semiring R]

/-- **The grading of `Fin (d + 1) → R` by coordinates**: the elements of degree `j` are those
supported on the coordinate `j`. -/
def coordinateGrading (d : ℕ) (j : ℤ) : Submodule R (Fin (d + 1) → R) :=
  Submodule.pi {i | (i : ℤ) ≠ j} fun _ ↦ ⊥

variable {R}

/-- An element of `Fin (d + 1) → R` has degree `j` exactly when it vanishes off the coordinate
`j`. -/
theorem mem_coordinateGrading_iff {d : ℕ} {j : ℤ} {x : Fin (d + 1) → R} :
    x ∈ coordinateGrading R d j ↔ ∀ i : Fin (d + 1), (i : ℤ) ≠ j → x i = 0 := by
  simp [coordinateGrading]

end CoordinateGrading

variable {R : Type*} [Ring R]

namespace BottChainData

variable {ι : Type*} [Fintype ι] {d : ι → ℕ}

/-- For Bott data whose chains on `C` are `Fin (d C + 1) → R`, graded by coordinates, a chain has
total degree `k` exactly when its coordinate `i` on `C` vanishes unless `i = k - λ_C`. -/
theorem mem_totalDegree_coordinateGrading_iff
    {B : BottChainData R ι fun C ↦ Fin (d C + 1) → R} {k : ℤ} {x : ∀ C, Fin (d C + 1) → R} :
    x ∈ B.totalDegree (fun C ↦ coordinateGrading R (d C)) k ↔
      ∀ C (i : Fin (d C + 1)), (i : ℤ) ≠ k - B.rank C → x C i = 0 := by
  simp only [mem_totalDegree_iff, mem_coordinateGrading_iff]

end BottChainData

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

/-- Every correspondence of the two-cap model is the negative of its pushforward. -/
private theorem correspondence_twoCapSphere_eq_neg (C D : TwoCapSphereComponent) :
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
  simp [twoCapSphere]

/-- The correspondence from the south pole to the equator sends the generator to the fundamental
class `[C]`. -/
@[simp]
theorem correspondence_twoCapSphere_southPole_equator :
    (twoCapSphere R).correspondence southPole equator =
      LinearMap.single R (fun _ ↦ R) 1 ∘ₗ LinearMap.proj 0 := by
  rw [correspondence_twoCapSphere_eq_neg]
  simp [twoCapSphere]

/-- **The Bott differential of the two-cap model at the equator**: the chain `a N + b S` on the
poles goes to `(a + b) [C]`. -/
theorem differential_twoCapSphere_equator (x : ∀ C, Fin (TwoCapSphereComponent.dim C + 1) → R) :
    (twoCapSphere R).differential x equator =
      Pi.single 1 (x northPole 0 + x southPole 0) := by
  rw [differential_apply, TwoCapSphereComponent.sum_univ]
  simp only [correspondence_twoCapSphere_eq_neg]
  simp [twoCapSphere, Pi.single_add]

/-- The Bott differential of the two-cap model vanishes at the north pole: no trajectory ends
there. -/
theorem differential_twoCapSphere_northPole
    (x : ∀ C, Fin (TwoCapSphereComponent.dim C + 1) → R) :
    (twoCapSphere R).differential x northPole = 0 := by
  rw [differential_apply, TwoCapSphereComponent.sum_univ]
  simp only [correspondence_twoCapSphere_eq_neg]
  simp [twoCapSphere]

/-- The Bott differential of the two-cap model vanishes at the south pole: no trajectory ends
there. -/
theorem differential_twoCapSphere_southPole
    (x : ∀ C, Fin (TwoCapSphereComponent.dim C + 1) → R) :
    (twoCapSphere R).differential x southPole = 0 := by
  rw [differential_apply, TwoCapSphereComponent.sum_univ]
  simp only [correspondence_twoCapSphere_eq_neg]
  simp [twoCapSphere]

/-- The pushforwards of the two-cap model shift the coordinate grading by the chain-degree shift
`d_CD = λ_C - λ_D - 1`: from a pole to the equator, a point goes to a multiple of `[C]`. -/
theorem twoCapSphere_pushforward_mem (C D : TwoCapSphereComponent) (j : ℤ)
    (x : Fin (TwoCapSphereComponent.dim C + 1) → R)
    (hx : x ∈ coordinateGrading R (TwoCapSphereComponent.dim C) j) :
    (twoCapSphere R).pushforward C D x ∈ coordinateGrading R (TwoCapSphereComponent.dim D)
      (j + bottDegreeShift (twoCapSphere R).rank C D) := by
  rw [mem_coordinateGrading_iff] at hx ⊢
  intro i hi
  cases C <;> cases D <;> simp only [twoCapSphere, LinearMap.zero_apply, Pi.zero_apply] at hi ⊢
  -- The two correspondences from a pole to the equator: `x` has degree `0` unless it vanishes.
  all_goals
    have : x 0 = 0 ∨ (i : ℤ) = 0 := by
      rw [bottDegreeShift_def] at hi
      by_cases hj : j = 0
      · fin_cases i <;> simp_all
      · exact .inl (hx 0 (by simpa [eq_comm] using hj))
    fin_cases i <;> rcases this with h | h <;> simp_all

variable (R) in
/-- **The Bott complex of the two-cap model**: `R²` on the poles in total degree `2`, `H₁(C)` and
`H₀(C)` in total degrees `1` and `0`. -/
@[expose] noncomputable def twoCapSphereComplex : ChainComplex (ModuleCat R) ℤ :=
  (twoCapSphere R).chainComplex (S := fun C ↦ coordinateGrading R (TwoCapSphereComponent.dim C))
    (fun C _ _ _ ↦ by simp) twoCapSphere_pushforward_mem

/-- The differential of the Bott complex of the two-cap model is the Bott differential. -/
theorem twoCapSphereComplex_d_apply {i j : ℤ} (hij : i = j + 1)
    (x : (twoCapSphere R).totalDegree
      (fun C ↦ coordinateGrading R (TwoCapSphereComponent.dim C)) i) :
    (((twoCapSphereComplex R).d i j).hom x : (twoCapSphere R).totalDegree
      (fun C ↦ coordinateGrading R (TwoCapSphereComponent.dim C)) j).val =
      (twoCapSphere R).differential x.val := by
  subst hij
  exact chainComplex_d_apply _ _ _ _ x

/-- **`H₂ = R` for the two-cap model**: the cycles of total degree `2` are the multiples of
`N - S`, and nothing has total degree `3`. -/
theorem nonempty_linearEquiv_homology_two_twoCapSphereComplex :
    Nonempty ((twoCapSphereComplex R).homology 2 ≃ₗ[R] R) := by
  set K := twoCapSphereComplex R
  set S : ∀ C : TwoCapSphereComponent,
    ℤ → Submodule R (Fin (TwoCapSphereComponent.dim C + 1) → R) :=
    fun C ↦ coordinateGrading R (TwoCapSphereComponent.dim C)
  let ψ : LinearMap.ker (K.d 2 1).hom →ₗ[R] R :=
    LinearMap.proj 0 ∘ₗ LinearMap.proj northPole ∘ₗ ((twoCapSphere R).totalDegree S 2).subtype ∘ₗ
      (LinearMap.ker (K.d 2 1).hom).subtype
  have hψ : Function.Surjective ψ := by
    intro r
    let y : ∀ C, Fin (TwoCapSphereComponent.dim C + 1) → R :=
      Pi.single northPole (fun _ ↦ r) - Pi.single southPole (fun _ ↦ r)
    have hy : y ∈ (twoCapSphere R).totalDegree S 2 := by
      refine mem_totalDegree_coordinateGrading_iff.2 fun C i hi ↦ ?_
      cases C <;> fin_cases i <;> simp_all [y]
    have hdy : (twoCapSphere R).differential y = 0 := by
      funext C
      cases C <;> simp only [differential_twoCapSphere_equator, differential_twoCapSphere_northPole,
        differential_twoCapSphere_southPole] <;> simp [y]
    exact ⟨⟨⟨y, hy⟩, LinearMap.mem_ker.2 (Subtype.ext
      ((twoCapSphereComplex_d_apply (by norm_num) ⟨y, hy⟩).trans hdy))⟩,
      (by simp [y] : y northPole 0 = r)⟩
  have hker : LinearMap.range (K.sc' 3 2 1).moduleCatToCycles = LinearMap.ker ψ := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨y, rfl⟩
      have : y = 0 := Subtype.ext (funext fun C ↦ funext fun i ↦
        mem_totalDegree_coordinateGrading_iff.1 y.property C i
          (by cases C <;> fin_cases i <;> simp))
      simp [this]
    · rintro ⟨⟨x, hx⟩, hdx⟩ hz
      have hdx' : (twoCapSphere R).differential x = 0 :=
        (twoCapSphereComplex_d_apply (by norm_num) ⟨x, hx⟩).symm.trans
          (congrArg Subtype.val (hdx : (K.d 2 1).hom ⟨x, hx⟩ = 0))
      have hN : x northPole 0 = 0 := hz
      have hS : x southPole 0 = 0 := by
        have h := congrFun (congrFun hdx' equator) 1
        rw [differential_twoCapSphere_equator] at h
        simpa [hN] using h
      obtain rfl : x = 0 := funext fun C ↦ funext fun i ↦ by
        cases C <;> fin_cases i <;>
          simp [mem_totalDegree_coordinateGrading_iff.1 hx, hN, hS]
      exact zero_mem _
  exact ⟨(K.homologyIsoSc' 3 2 1 (by simp) (by simp) ≪≫
    (K.sc' 3 2 1).moduleCatHomologyIso).toLinearEquiv ≪≫ₗ Submodule.quotEquivOfEq _ _ hker ≪≫ₗ
      ψ.quotKerEquivOfSurjective hψ⟩

/-- **`H₀ = R` for the two-cap model**, spanned by the point class of the equator. -/
theorem nonempty_linearEquiv_homology_zero_twoCapSphereComplex :
    Nonempty ((twoCapSphereComplex R).homology 0 ≃ₗ[R] R) := by
  set K := twoCapSphereComplex R
  set S : ∀ C : TwoCapSphereComponent,
    ℤ → Submodule R (Fin (TwoCapSphereComponent.dim C + 1) → R) :=
    fun C ↦ coordinateGrading R (TwoCapSphereComponent.dim C)
  -- Every chain of total degree `-1` vanishes.
  have hX : ∀ y : K.X (-1), y = 0 := fun ⟨y, hy⟩ ↦ Subtype.ext (funext fun C ↦ funext fun i ↦
    mem_totalDegree_coordinateGrading_iff.1 hy C i (by cases C <;> fin_cases i <;> simp))
  let ψ : LinearMap.ker (K.d 0 (-1)).hom →ₗ[R] R :=
    LinearMap.proj 0 ∘ₗ LinearMap.proj equator ∘ₗ ((twoCapSphere R).totalDegree S 0).subtype ∘ₗ
      (LinearMap.ker (K.d 0 (-1)).hom).subtype
  have hψ : Function.Surjective ψ := by
    intro r
    let y : ∀ C, Fin (TwoCapSphereComponent.dim C + 1) → R :=
      Pi.single equator (Pi.single 0 r)
    have hy : y ∈ (twoCapSphere R).totalDegree S 0 := by
      refine mem_totalDegree_coordinateGrading_iff.2 fun C i hi ↦ ?_
      cases C <;> fin_cases i <;> simp_all [y]
    exact ⟨⟨⟨y, hy⟩, hX _⟩, (by simp [y] : y equator 0 = r)⟩
  have hker : LinearMap.range (K.sc' 1 0 (-1)).moduleCatToCycles = LinearMap.ker ψ := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨⟨y, hy⟩, rfl⟩
      -- The differential vanishes in total degree `1`: the poles carry no chains there.
      have hdy : (twoCapSphere R).differential y = 0 := by
        have hN : y northPole 0 = 0 := mem_totalDegree_coordinateGrading_iff.1 hy _ _ (by simp)
        have hS : y southPole 0 = 0 := mem_totalDegree_coordinateGrading_iff.1 hy _ _ (by simp)
        funext C
        cases C <;> simp only [differential_twoCapSphere_equator,
          differential_twoCapSphere_northPole, differential_twoCapSphere_southPole] <;>
          simp [hN, hS]
      have : (K.sc' 1 0 (-1)).moduleCatToCycles ⟨y, hy⟩ = 0 := Subtype.ext (Subtype.ext
        ((twoCapSphereComplex_d_apply (by norm_num) ⟨y, hy⟩).trans hdy))
      rw [this]
      exact zero_mem _
    · rintro ⟨⟨x, hx⟩, hdx⟩ hz
      have hE : x equator 0 = 0 := hz
      obtain rfl : x = 0 := funext fun C ↦ funext fun i ↦ by
        cases C <;> fin_cases i <;>
          simp [mem_totalDegree_coordinateGrading_iff.1 hx, hE]
      exact zero_mem _
  exact ⟨(K.homologyIsoSc' 1 0 (-1) (by simp) (by simp) ≪≫
    (K.sc' 1 0 (-1)).moduleCatHomologyIso).toLinearEquiv ≪≫ₗ Submodule.quotEquivOfEq _ _ hker ≪≫ₗ
      ψ.quotKerEquivOfSurjective hψ⟩

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
    refine ⟨⟨y, hy⟩, Subtype.ext ((twoCapSphereComplex_d_apply rfl ⟨y, hy⟩).trans ?_)⟩
    funext C i
    cases C <;> simp only [differential_twoCapSphere_equator,
      differential_twoCapSphere_northPole, differential_twoCapSphere_southPole] <;> fin_cases i
    all_goals simp [y, mem_totalDegree_coordinateGrading_iff.1 hx]
  · -- Otherwise there are no chains of total degree `k`.
    refine ⟨0, Subtype.ext ?_⟩
    rw [map_zero]
    funext C i
    refine (mem_totalDegree_coordinateGrading_iff.1 hx C i ?_).symm
    cases C <;> fin_cases i <;> simp <;> omega

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

/-- Every correspondence of the four-component model is the negative of its pushforward. -/
private theorem correspondence_fourComponentSphere_eq_neg (C D : FourComponentSphereComponent) :
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
  simp [fourComponentSphere]

/-- The correspondence from `C₃` to `N` is the augmentation, which keeps the coefficient of the
point class. -/
@[simp]
theorem correspondence_fourComponentSphere_highCircle_northPole :
    (fourComponentSphere R).correspondence highCircle northPole =
      LinearMap.pi fun _ ↦ LinearMap.proj 0 := by
  rw [correspondence_fourComponentSphere_eq_neg]
  simp [fourComponentSphere]

/-- The correspondence from `S` to `C₀` sends the generator to the fundamental class `[C₀]`. -/
@[simp]
theorem correspondence_fourComponentSphere_southPole_lowCircle :
    (fourComponentSphere R).correspondence southPole lowCircle =
      LinearMap.single R (fun _ ↦ R) 1 ∘ₗ LinearMap.proj 0 := by
  rw [correspondence_fourComponentSphere_eq_neg]
  simp [fourComponentSphere]

/-- **The Bott differential of the four-component model at `C₀`**: `b S` and `x` on `C₃` go to
`b [C₀] - φ_* x`. -/
theorem differential_fourComponentSphere_lowCircle
    (x : ∀ C, Fin (FourComponentSphereComponent.dim C + 1) → R) :
    (fourComponentSphere R).differential x lowCircle =
      Pi.single 1 (x southPole 0) - x highCircle := by
  rw [differential_apply, FourComponentSphereComponent.sum_univ]
  simp only [correspondence_fourComponentSphere_eq_neg]
  simp [fourComponentSphere, sub_eq_add_neg]

/-- **The Bott differential of the four-component model at `N`**: the coefficient of the point
class of `C₃`. -/
theorem differential_fourComponentSphere_northPole
    (x : ∀ C, Fin (FourComponentSphereComponent.dim C + 1) → R) :
    (fourComponentSphere R).differential x northPole = fun _ ↦ x highCircle 0 := by
  rw [differential_apply, FourComponentSphereComponent.sum_univ]
  simp only [correspondence_fourComponentSphere_eq_neg]
  funext i
  simp [fourComponentSphere]

/-- The Bott differential of the four-component model vanishes at `S`: no trajectory ends there.
-/
theorem differential_fourComponentSphere_southPole
    (x : ∀ C, Fin (FourComponentSphereComponent.dim C + 1) → R) :
    (fourComponentSphere R).differential x southPole = 0 := by
  rw [differential_apply, FourComponentSphereComponent.sum_univ]
  simp only [correspondence_fourComponentSphere_eq_neg]
  simp [fourComponentSphere]

/-- The Bott differential of the four-component model vanishes at `C₃`: no trajectory ends there.
-/
theorem differential_fourComponentSphere_highCircle
    (x : ∀ C, Fin (FourComponentSphereComponent.dim C + 1) → R) :
    (fourComponentSphere R).differential x highCircle = 0 := by
  rw [differential_apply, FourComponentSphereComponent.sum_univ]
  simp only [correspondence_fourComponentSphere_eq_neg]
  simp [fourComponentSphere]

/-- The pushforwards of the four-component model shift the coordinate grading by the chain-degree
shift `d_CD = λ_C - λ_D - 1`. -/
theorem fourComponentSphere_pushforward_mem (C D : FourComponentSphereComponent) (j : ℤ)
    (x : Fin (FourComponentSphereComponent.dim C + 1) → R)
    (hx : x ∈ coordinateGrading R (FourComponentSphereComponent.dim C) j) :
    (fourComponentSphere R).pushforward C D x ∈
      coordinateGrading R (FourComponentSphereComponent.dim D)
        (j + bottDegreeShift (fourComponentSphere R).rank C D) := by
  rw [mem_coordinateGrading_iff] at hx ⊢
  intro i hi
  cases C <;> cases D <;> simp only [fourComponentSphere, LinearMap.zero_apply, Pi.zero_apply]
    at hi ⊢
  all_goals rw [bottDegreeShift_def] at hi
  · -- From the south pole to the low circle: `x` has degree `0` unless it vanishes.
    have : x 0 = 0 ∨ (i : ℤ) = 0 := by
      by_cases hj : j = 0
      · fin_cases i <;> simp_all
      · exact .inl (hx 0 (by simpa [eq_comm] using hj))
    fin_cases i <;> rcases this with h | h <;> simp_all
  · simpa using hx i (by simpa using hi)
  · fin_cases i
    simpa using hx 0 (by simpa using hi)

variable (R) in
/-- **The Bott complex of the four-component model**: `([C₃], S)`, `(pt_(C₃), [C₀])` and
`(pt_(C₀), N)` in total degrees `2`, `1` and `0`. -/
@[expose] noncomputable def fourComponentSphereComplex : ChainComplex (ModuleCat R) ℤ :=
  (fourComponentSphere R).chainComplex
    (S := fun C ↦ coordinateGrading R (FourComponentSphereComponent.dim C))
    (fun C _ _ _ ↦ by simp) fourComponentSphere_pushforward_mem

/-- The differential of the Bott complex of the four-component model is the Bott differential. -/
theorem fourComponentSphereComplex_d_apply {i j : ℤ} (hij : i = j + 1)
    (x : (fourComponentSphere R).totalDegree
      (fun C ↦ coordinateGrading R (FourComponentSphereComponent.dim C)) i) :
    (((fourComponentSphereComplex R).d i j).hom x : (fourComponentSphere R).totalDegree
      (fun C ↦ coordinateGrading R (FourComponentSphereComponent.dim C)) j).val =
      (fourComponentSphere R).differential x.val := by
  subst hij
  exact chainComplex_d_apply _ _ _ _ x

/-- The chain `r ([C₃] + S)` is a cycle of total degree `2` of the four-component model. -/
private theorem fourComponentSphere_isCycle_two (r : R) :
    (Pi.single highCircle (Pi.single 1 r) + Pi.single southPole (fun _ ↦ r) :
        ∀ C, Fin (FourComponentSphereComponent.dim C + 1) → R) ∈
      (fourComponentSphere R).totalDegree
        (fun C ↦ coordinateGrading R (FourComponentSphereComponent.dim C)) 2 ∧
    (fourComponentSphere R).differential
      (Pi.single highCircle (Pi.single 1 r) + Pi.single southPole (fun _ ↦ r)) = 0 := by
  refine ⟨mem_totalDegree_coordinateGrading_iff.2 fun C i hi ↦ ?_, funext fun C ↦ ?_⟩
  · cases C <;> fin_cases i <;> simp_all
  · cases C <;> simp only [differential_fourComponentSphere_lowCircle,
      differential_fourComponentSphere_northPole, differential_fourComponentSphere_southPole,
      differential_fourComponentSphere_highCircle] <;> simp [funext_iff]

/-- A chain of total degree `0` of the four-component model whose coefficients at the point classes
of `C₀` and `N` add up to zero is the boundary of a chain of total degree `1`, a multiple of the
point class of `C₃`. -/
private theorem fourComponentSphere_exists_differential_eq
    {x : ∀ C, Fin (FourComponentSphereComponent.dim C + 1) → R}
    (hx : x ∈ (fourComponentSphere R).totalDegree
      (fun C ↦ coordinateGrading R (FourComponentSphereComponent.dim C)) 0)
    (hz : x lowCircle 0 + x northPole 0 = 0) :
    ∃ y ∈ (fourComponentSphere R).totalDegree
      (fun C ↦ coordinateGrading R (FourComponentSphereComponent.dim C)) (0 + 1),
      (fourComponentSphere R).differential y = x := by
  refine ⟨Pi.single highCircle (Pi.single 0 (x northPole 0)),
    mem_totalDegree_coordinateGrading_iff.2 fun C i hi ↦ ?_, funext fun C ↦ funext fun i ↦ ?_⟩
  · cases C <;> fin_cases i <;> simp_all
  · cases C <;> simp only [differential_fourComponentSphere_lowCircle,
      differential_fourComponentSphere_northPole, differential_fourComponentSphere_southPole,
      differential_fourComponentSphere_highCircle] <;> fin_cases i
    all_goals simp [mem_totalDegree_coordinateGrading_iff.1 hx, eq_neg_of_add_eq_zero_left hz]

/-- **`H₂ = R` for the four-component model**: the cycles of total degree `2` are the multiples of
`[C₃] + S`, and nothing has total degree `3`. -/
theorem nonempty_linearEquiv_homology_two_fourComponentSphereComplex :
    Nonempty ((fourComponentSphereComplex R).homology 2 ≃ₗ[R] R) := by
  set K := fourComponentSphereComplex R
  set S : ∀ C : FourComponentSphereComponent,
    ℤ → Submodule R (Fin (FourComponentSphereComponent.dim C + 1) → R) :=
    fun C ↦ coordinateGrading R (FourComponentSphereComponent.dim C)
  -- The coefficient of `[C₃]`, on the cycles of total degree `2`.
  let ψ : LinearMap.ker (K.d 2 1).hom →ₗ[R] R :=
    LinearMap.proj 1 ∘ₗ LinearMap.proj highCircle ∘ₗ
      ((fourComponentSphere R).totalDegree S 2).subtype ∘ₗ (LinearMap.ker (K.d 2 1).hom).subtype
  have hψ : Function.Surjective ψ := fun r ↦
    have ⟨hy, hdy⟩ := fourComponentSphere_isCycle_two (R := R) r
    ⟨⟨⟨_, hy⟩, LinearMap.mem_ker.2 (Subtype.ext
      ((fourComponentSphereComplex_d_apply (by norm_num) ⟨_, hy⟩).trans hdy))⟩,
      (by simp : (Pi.single highCircle (Pi.single 1 r) +
        Pi.single southPole (fun _ ↦ r) : ∀ C, Fin (FourComponentSphereComponent.dim C + 1) → R)
          highCircle 1 = r)⟩
  have hker : LinearMap.range (K.sc' 3 2 1).moduleCatToCycles = LinearMap.ker ψ := by
    refine le_antisymm ?_ ?_
    · -- There are no chains of total degree `3`.
      rintro _ ⟨y, rfl⟩
      have : y = 0 := Subtype.ext (funext fun C ↦ funext fun i ↦
        mem_totalDegree_coordinateGrading_iff.1 y.property C i
          (by cases C <;> fin_cases i <;> simp))
      simp [this]
    · rintro ⟨⟨x, hx⟩, hdx⟩ hz
      have hdx' : (fourComponentSphere R).differential x = 0 :=
        (fourComponentSphereComplex_d_apply (by norm_num) ⟨x, hx⟩).symm.trans
          (congrArg Subtype.val (hdx : (K.d 2 1).hom ⟨x, hx⟩ = 0))
      have hC : x highCircle 1 = 0 := hz
      have hS : x southPole 0 = 0 := by
        have h := congrFun (congrFun hdx' lowCircle) 1
        rw [differential_fourComponentSphere_lowCircle] at h
        simpa [hC] using h
      obtain rfl : x = 0 := funext fun C ↦ funext fun i ↦ by
        cases C <;> fin_cases i <;>
          simp [mem_totalDegree_coordinateGrading_iff.1 hx, hS, hC]
      exact zero_mem _
  exact ⟨(K.homologyIsoSc' 3 2 1 (by simp) (by simp) ≪≫
    (K.sc' 3 2 1).moduleCatHomologyIso).toLinearEquiv ≪≫ₗ Submodule.quotEquivOfEq _ _ hker ≪≫ₗ
      ψ.quotKerEquivOfSurjective hψ⟩

/-- **`H₀ = R` for the four-component model**: the boundaries of total degree `0` are the
multiples of `N - pt_(C₀)`, so the sum of the two coefficients identifies `H₀` with `R`. -/
theorem nonempty_linearEquiv_homology_zero_fourComponentSphereComplex :
    Nonempty ((fourComponentSphereComplex R).homology 0 ≃ₗ[R] R) := by
  set K := fourComponentSphereComplex R
  set S : ∀ C : FourComponentSphereComponent,
    ℤ → Submodule R (Fin (FourComponentSphereComponent.dim C + 1) → R) :=
    fun C ↦ coordinateGrading R (FourComponentSphereComponent.dim C)
  -- Every chain of total degree `-1` vanishes.
  have hX : ∀ y : K.X (-1), y = 0 := fun ⟨y, hy⟩ ↦ Subtype.ext (funext fun C ↦ funext fun i ↦
    mem_totalDegree_coordinateGrading_iff.1 hy C i (by cases C <;> fin_cases i <;> simp))
  -- The sum of the coefficients of the point classes of `C₀` and of `N`.
  let ψ : LinearMap.ker (K.d 0 (-1)).hom →ₗ[R] R :=
    LinearMap.proj 0 ∘ₗ LinearMap.proj lowCircle ∘ₗ
        ((fourComponentSphere R).totalDegree S 0).subtype ∘ₗ
          (LinearMap.ker (K.d 0 (-1)).hom).subtype +
      LinearMap.proj 0 ∘ₗ LinearMap.proj northPole ∘ₗ
        ((fourComponentSphere R).totalDegree S 0).subtype ∘ₗ
          (LinearMap.ker (K.d 0 (-1)).hom).subtype
  have hψ : Function.Surjective ψ := by
    intro r
    let y : ∀ C, Fin (FourComponentSphereComponent.dim C + 1) → R :=
      Pi.single lowCircle (Pi.single 0 r)
    have hy : y ∈ (fourComponentSphere R).totalDegree S 0 := by
      refine mem_totalDegree_coordinateGrading_iff.2 fun C i hi ↦ ?_
      cases C <;> fin_cases i <;> simp_all [y]
    exact ⟨⟨⟨y, hy⟩, hX _⟩, (by simp [y] : y lowCircle 0 + y northPole 0 = r)⟩
  have hker : LinearMap.range (K.sc' 1 0 (-1)).moduleCatToCycles = LinearMap.ker ψ := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨⟨y, hy⟩, rfl⟩
      -- The boundary of `c` times the point class of `C₃` is `c (N - pt_{C₀})`.
      have hψy : (fourComponentSphere R).differential y lowCircle 0 +
          (fourComponentSphere R).differential y northPole 0 = 0 := by
        rw [differential_fourComponentSphere_lowCircle, differential_fourComponentSphere_northPole]
        simp
      exact hψy
    · rintro ⟨⟨x, hx⟩, hdx⟩ hz
      obtain ⟨y, hy, hdy⟩ := fourComponentSphere_exists_differential_eq hx hz
      exact ⟨⟨y, hy⟩, Subtype.ext (Subtype.ext
        ((fourComponentSphereComplex_d_apply rfl ⟨y, hy⟩).trans hdy))⟩
  exact ⟨(K.homologyIsoSc' 1 0 (-1) (by simp) (by simp) ≪≫
    (K.sc' 1 0 (-1)).moduleCatHomologyIso).toLinearEquiv ≪≫ₗ Submodule.quotEquivOfEq _ _ hker ≪≫ₗ
      ψ.quotKerEquivOfSurjective hψ⟩

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
      (fourComponentSphereComplex_d_apply (by norm_num) ⟨x, hx⟩).symm.trans
        (congrArg Subtype.val (hdx : (K.d 1 (1 - 1)).hom ⟨x, hx⟩ = 0))
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
    refine ⟨⟨y, hy⟩, Subtype.ext ((fourComponentSphereComplex_d_apply rfl ⟨y, hy⟩).trans ?_)⟩
    funext C i
    cases C <;> simp only [differential_fourComponentSphere_lowCircle,
      differential_fourComponentSphere_northPole, differential_fourComponentSphere_southPole,
      differential_fourComponentSphere_highCircle] <;> fin_cases i
    all_goals simp [y, mem_totalDegree_coordinateGrading_iff.1 hx, hC]
  · -- Otherwise there are no chains of total degree `k`.
    refine ⟨0, Subtype.ext ?_⟩
    rw [map_zero]
    funext C i
    refine (mem_totalDegree_coordinateGrading_iff.1 hx C i ?_).symm
    cases C <;> fin_cases i <;> simp <;> omega

end BottChainData

end TauCeti

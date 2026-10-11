/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Spectrum.Basic
public import Mathlib.LinearAlgebra.LinearPMap
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic

/-!
# Continuous inverses of shifts of partial linear maps

For a partial linear map `A` on a module over a ring, `LinearPMap.IsResolventAt`
says that a continuous linear map inverts `lambda • I - A` on the domain of `A`. The inverse
is unique, and its existence defines `LinearPMap.resolventSet` and the chosen map
`LinearPMap.resolvent`. These notions require only a topology on the module, with no norm or
continuity assumptions on addition or scalar multiplication.

Over a noncommutative ring, the scalar expression `x ↦ lambda • x - A x` need not be linear.
The predicate still requires its inverse to be linear over the full scalar ring; a parameter
whose shift is not linear therefore does not belong to the resolvent set.

This file gives the graph characterization, the two inverse identities, and the fact that an
operator has no proper extension sharing a resolvent point. The pointwise resolvent identity
holds over rings, and resolvents commute over division rings. For topological additive groups, an
invertible continuous linear perturbation gives another resolvent. Over commutative rings
with continuous scalar multiplication by constants, the resolvent of an everywhere defined
continuous linear operator agrees with Mathlib's algebraic resolvent.

On normed spaces over nontrivially normed fields the continuous linear inverse is bounded;
Neumann perturbations and openness of the resolvent set are developed in
`TauCeti.Analysis.Normed.Operator.Resolvent.Unbounded`.

## References

Engel--Nagel, *One-Parameter Semigroups for Linear Evolution Equations*, Section IV.1;
Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*,
Chapter 1.
-/

public section

noncomputable section

namespace LinearPMap

section Basic

variable {𝕜 X : Type*} [Ring 𝕜] [AddCommGroup X] [TopologicalSpace X] [Module 𝕜 X]
variable {A : X →ₗ.[𝕜] X} {lambda : 𝕜} {R : X →L[𝕜] X}

/-! ## Inverting `lambda • I - A` -/

/-- `IsResolventAt A lambda R` says that the **continuous** operator `R : X →L[𝕜] X` inverts
`lambda • I - A : D(A) → X`: it takes its values in `D(A)`, is a right inverse of
`lambda • I - A` on all of `X`, and is a left inverse of it on `D(A)`.

For an unbounded `A` this replaces the algebraic condition
`IsUnit (algebraMap 𝕜 (X →L[𝕜] X) lambda - A)` behind Mathlib's `resolventSet`, which cannot be
formed because `A` is not an element of `X →L[𝕜] X`. The two conditions agree when `A` is a
continuous linear operator read as an everywhere defined `LinearPMap`; see
`ContinuousLinearMap.mem_resolventSet_toPMap_top_iff`. -/
structure IsResolventAt (A : X →ₗ.[𝕜] X) (lambda : 𝕜) (R : X →L[𝕜] X) : Prop where
  /-- The inverse takes its values in the domain of `A`. -/
  mem_domain (y : X) : R y ∈ A.domain
  /-- `R` is a right inverse: `(lambda • I - A) (R y) = y` for every `y : X`. -/
  smul_sub_apply (y : X) : lambda • R y - A ⟨R y, mem_domain y⟩ = y
  /-- `R` is a left inverse: `R ((lambda • I - A) x) = x` for every `x ∈ D(A)`. -/
  apply_smul_sub (x : A.domain) : R (lambda • (x : X) - A x) = (x : X)

/-- An inverse of `lambda • I - A` is unique: a left inverse and a right inverse of the same
map agree. -/
theorem IsResolventAt.unique (h : IsResolventAt A lambda R) {R' : X →L[𝕜] X}
    (h' : IsResolventAt A lambda R') : R = R' := by
  ext y
  have hy : R (lambda • R' y - A ⟨R' y, h'.mem_domain y⟩) = R' y :=
    h.apply_smul_sub ⟨R' y, h'.mem_domain y⟩
  rwa [h'.smul_sub_apply y] at hy

/-- `lambda • I - A` is injective on `D(A)` whenever it has a left inverse. -/
theorem IsResolventAt.smul_sub_injective (h : IsResolventAt A lambda R) :
    Function.Injective fun x : A.domain => lambda • (x : X) - A x := by
  intro x y hxy
  dsimp only at hxy
  exact Subtype.ext (by rw [← h.apply_smul_sub x, ← h.apply_smul_sub y, hxy])

/-- `lambda • I - A` maps `D(A)` onto `X` whenever it has a right inverse. -/
theorem IsResolventAt.smul_sub_surjective (h : IsResolventAt A lambda R) :
    Function.Surjective fun x : A.domain => lambda • (x : X) - A x :=
  fun y => ⟨⟨R y, h.mem_domain y⟩, h.smul_sub_apply y⟩

/-- `lambda • I - A : D(A) → X` is a bijection at a point of the resolvent set. -/
theorem IsResolventAt.smul_sub_bijective (h : IsResolventAt A lambda R) :
    Function.Bijective fun x : A.domain => lambda • (x : X) - A x :=
  ⟨h.smul_sub_injective, h.smul_sub_surjective⟩

/-- The graph form of `IsResolventAt`: `R` inverts `lambda • I - A` exactly when every
`(R y, lambda • R y - y)` lies on the graph of `A`, and `R (lambda • x - w) = x` for every point
`(x, w)` of that graph. This form transfers along any construction described by its graph. -/
theorem isResolventAt_iff_forall_mem_graph :
    IsResolventAt A lambda R ↔
      (∀ y : X, (R y, lambda • R y - y) ∈ A.graph) ∧
        ∀ p ∈ A.graph, R (lambda • p.1 - p.2) = p.1 := by
  constructor
  · intro h
    refine ⟨fun y => (A.mem_graph_iff).mpr ⟨⟨R y, h.mem_domain y⟩, rfl, ?_⟩, fun p hp => ?_⟩
    · exact eq_sub_of_add_eq (sub_eq_iff_eq_add'.mp (h.smul_sub_apply y)).symm
    · obtain ⟨u, hu, hAu⟩ := (A.mem_graph_iff).mp hp
      rw [← hu, ← hAu]
      exact h.apply_smul_sub u
  · rintro ⟨hgraph, hleft⟩
    have hmem (y : X) : R y ∈ A.domain := by
      obtain ⟨⟨v, hv⟩, hu, -⟩ := (A.mem_graph_iff).mp (hgraph y)
      simp only at hu
      exact hu ▸ hv
    refine ⟨hmem, fun y => ?_, fun x => hleft _ (A.mem_graph x)⟩
    obtain ⟨u, hu, hAu⟩ := (A.mem_graph_iff).mp (hgraph y)
    have huR : u = ⟨R y, hmem y⟩ := Subtype.ext hu
    subst huR
    simp only at hAu
    rw [hAu, sub_sub_cancel]

/-! ## The resolvent set and the resolvent -/

/-- The **resolvent set** of an unbounded operator `A : X →ₗ.[𝕜] X`: those `lambda : 𝕜` for which
`lambda • I - A : D(A) → X` is a bijection with continuous linear inverse. -/
def resolventSet (A : X →ₗ.[𝕜] X) : Set 𝕜 :=
  {lambda | ∃ R : X →L[𝕜] X, IsResolventAt A lambda R}

/-- Membership in the resolvent set unfolds to the existence of a continuous linear inverse of
`lambda • I - A`. -/
theorem mem_resolventSet_iff :
    lambda ∈ resolventSet A ↔ ∃ R : X →L[𝕜] X, IsResolventAt A lambda R :=
  Iff.rfl

/-- Exhibiting an inverse puts `lambda` in the resolvent set. -/
theorem IsResolventAt.mem_resolventSet (h : IsResolventAt A lambda R) :
    lambda ∈ resolventSet A :=
  ⟨R, h⟩

/-- An inverse of `lambda • I - A` exists conditionally on `lambda` lying in the resolvent set;
this is what lets `LinearPMap.resolvent` be defined by `Classical.choose`
without a decidability side-condition. -/
private theorem exists_isResolventAt_of_mem (A : X →ₗ.[𝕜] X) (lambda : 𝕜) :
    ∃ R : X →L[𝕜] X, lambda ∈ resolventSet A → IsResolventAt A lambda R := by
  by_cases h : lambda ∈ resolventSet A
  · exact ⟨h.choose, fun _ => h.choose_spec⟩
  · exact ⟨0, fun h' => absurd h' h⟩

/-- The **resolvent** `R(lambda, A) = (lambda • I - A)⁻¹` of an unbounded operator, as a
continuous linear operator on `X`.

Off the resolvent set the value is an unspecified junk value; every lemma below carries the
hypothesis `lambda ∈ resolventSet A`. Uniqueness of the inverse
(`LinearPMap.IsResolventAt.unique`) makes the choice immaterial on the
resolvent set: `LinearPMap.resolvent_eq_of_isResolventAt` identifies it with
any inverse one can exhibit. -/
noncomputable def resolvent (A : X →ₗ.[𝕜] X) (lambda : 𝕜) : X →L[𝕜] X :=
  (exists_isResolventAt_of_mem A lambda).choose

/-- On the resolvent set, `resolvent A lambda` really does invert `lambda • I - A`. -/
theorem isResolventAt_resolvent (h : lambda ∈ resolventSet A) :
    IsResolventAt A lambda (resolvent A lambda) :=
  (exists_isResolventAt_of_mem A lambda).choose_spec h

/-- Any exhibited inverse of `lambda • I - A` *is* the resolvent. -/
theorem resolvent_eq_of_isResolventAt (h : IsResolventAt A lambda R) :
    resolvent A lambda = R :=
  (isResolventAt_resolvent h.mem_resolventSet).unique h

/-- The resolvent takes its values in `D(A)`. -/
theorem resolvent_mem_domain (h : lambda ∈ resolventSet A) (y : X) :
    resolvent A lambda y ∈ A.domain :=
  (isResolventAt_resolvent h).mem_domain y

/-- The right-inverse identity `(lambda • I - A) R(lambda) y = y`. -/
theorem smul_sub_apply_resolvent (h : lambda ∈ resolventSet A) (y : X) :
    lambda • resolvent A lambda y - A ⟨resolvent A lambda y, resolvent_mem_domain h y⟩ = y :=
  (isResolventAt_resolvent h).smul_sub_apply y

/-- The left-inverse identity `R(lambda) (lambda • x - A x) = x` on `D(A)`. -/
@[simp] theorem resolvent_smul_sub_apply (h : lambda ∈ resolventSet A) (x : A.domain) :
    resolvent A lambda (lambda • (x : X) - A x) = (x : X) :=
  (isResolventAt_resolvent h).apply_smul_sub x

/-- The right-inverse identity solved for `A`: `A R(lambda) y = lambda • R(lambda) y - y`. -/
@[simp] theorem apply_resolvent (h : lambda ∈ resolventSet A) (y : X) :
    A ⟨resolvent A lambda y, resolvent_mem_domain h y⟩ = lambda • resolvent A lambda y - y := by
  exact eq_sub_of_add_eq (sub_eq_iff_eq_add'.mp (smul_sub_apply_resolvent h y)).symm

/-- At a point of the resolvent set, `lambda • I - A : D(A) → X` is a bijection. -/
theorem smul_sub_bijective (h : lambda ∈ resolventSet A) :
    Function.Bijective fun x : A.domain => lambda • (x : X) - A x :=
  (isResolventAt_resolvent h).smul_sub_bijective

/-- **An operator has no proper extension sharing a resolvent point.** If `A ≤ B` and some
`lambda` lies in the resolvent set of both, then `A = B`.

A vector `y ∈ D(B)` has `lambda • y - B y = lambda • x - A x` for a unique `x ∈ D(A)`, by
surjectivity for `A`; injectivity for `B` then forces `y = x`, so `D(B) ⊆ D(A)`.

This is the step that upgrades "`A` is a restriction of the generator" to "`A` *is* the
generator" in the generation theorems. -/
theorem eq_of_le_of_mem_resolventSet {A B : X →ₗ.[𝕜] X} (hAB : A ≤ B)
    (hA : lambda ∈ resolventSet A) (hB : lambda ∈ resolventSet B) : A = B := by
  refine LinearPMap.eq_of_le_of_domain_eq hAB (le_antisymm hAB.1 fun y hy => ?_)
  obtain ⟨x, hx⟩ := (smul_sub_bijective hA).surjective (lambda • y - B ⟨y, hy⟩)
  obtain ⟨x', hx'coe, hx'val⟩ := LinearPMap.exists_of_le hAB x
  have hxy : x' = (⟨y, hy⟩ : B.domain) := by
    refine (smul_sub_bijective hB).injective ?_
    simp only [← hx'coe, ← hx'val]
    exact hx
  have hcoe : (x : X) = y := by rw [hx'coe, hxy]
  rw [← hcoe]
  exact x.property

/-- The resolvent commutes with `A` on `D(A)`: `R(lambda) (A x) = A (R(lambda) x)`. -/
theorem resolvent_apply_comm (h : lambda ∈ resolventSet A) (x : A.domain) :
    resolvent A lambda (A x) =
      A ⟨resolvent A lambda (x : X), resolvent_mem_domain h (x : X)⟩ := by
  rw [apply_resolvent h (x : X)]
  have hx := resolvent_smul_sub_apply h x
  rw [ContinuousLinearMap.map_sub, ContinuousLinearMap.map_smul] at hx
  exact eq_sub_of_add_eq (sub_eq_iff_eq_add'.mp hx).symm

end Basic

/-! ## The resolvent identity -/

section Ring

variable {𝕜 X : Type*} [Ring 𝕜] [AddCommGroup X] [TopologicalSpace X] [Module 𝕜 X]
variable {A : X →ₗ.[𝕜] X} {lambda mu : 𝕜}

/-- Pointwise form of the **resolvent identity**
`R(lambda) - R(mu) = (mu - lambda) R(lambda) R(mu)`. -/
theorem resolvent_sub_resolvent_apply (hl : lambda ∈ A.resolventSet)
    (hm : mu ∈ A.resolventSet) (y : X) :
    A.resolvent lambda y - A.resolvent mu y
      = (mu - lambda) • A.resolvent lambda (A.resolvent mu y) := by
  have hmem := resolvent_mem_domain hm y
  have hy : mu • A.resolvent mu y - A ⟨A.resolvent mu y, hmem⟩ = y :=
    smul_sub_apply_resolvent hm y
  have hleft : A.resolvent lambda
      (lambda • A.resolvent mu y - A ⟨A.resolvent mu y, hmem⟩) = A.resolvent mu y :=
    resolvent_smul_sub_apply hl ⟨A.resolvent mu y, hmem⟩
  have hkey : A.resolvent lambda (mu • A.resolvent mu y - A ⟨A.resolvent mu y, hmem⟩)
      = A.resolvent mu y + (mu - lambda) • A.resolvent lambda (A.resolvent mu y) := by
    have hsplit : mu • A.resolvent mu y - A ⟨A.resolvent mu y, hmem⟩
        = (lambda • A.resolvent mu y - A ⟨A.resolvent mu y, hmem⟩)
          + (mu - lambda) • A.resolvent mu y := by
            rw [sub_smul]
            abel
    rw [hsplit, ContinuousLinearMap.map_add, ContinuousLinearMap.map_smul, hleft]
  rw [hy] at hkey
  rw [hkey]
  abel

end Ring

section CommRing

variable {𝕜 X : Type*} [CommRing 𝕜] [AddCommGroup X] [TopologicalSpace X] [Module 𝕜 X]
  [IsTopologicalAddGroup X] [ContinuousConstSMul 𝕜 X]
variable {A : X →ₗ.[𝕜] X} {lambda mu : 𝕜}

/-- The **resolvent identity** `R(lambda) - R(mu) = (mu - lambda) R(lambda) R(mu)`, as an
equality of continuous linear maps. -/
theorem resolvent_sub_resolvent (hl : lambda ∈ A.resolventSet) (hm : mu ∈ A.resolventSet) :
    A.resolvent lambda - A.resolvent mu
      = (mu - lambda) • (A.resolvent lambda ∘L A.resolvent mu) := by
  ext y
  simpa using resolvent_sub_resolvent_apply hl hm y

end CommRing

section DivisionRing

variable {𝕜 X : Type*} [DivisionRing 𝕜] [AddCommGroup X] [TopologicalSpace X] [Module 𝕜 X]
variable {A : X →ₗ.[𝕜] X} {lambda mu : 𝕜}

/-- Resolvents at two points of the resolvent set commute. -/
theorem resolvent_comm (hl : lambda ∈ A.resolventSet) (hm : mu ∈ A.resolventSet) :
    A.resolvent lambda ∘L A.resolvent mu = A.resolvent mu ∘L A.resolvent lambda := by
  ext y
  rcases eq_or_ne lambda mu with rfl | hne
  · rfl
  · have hsub : (mu - lambda) ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
    have h1 := resolvent_sub_resolvent_apply hl hm y
    have h2 := resolvent_sub_resolvent_apply hm hl y
    have h3 : (mu - lambda) • A.resolvent lambda (A.resolvent mu y)
        = (mu - lambda) • A.resolvent mu (A.resolvent lambda y) := by
      rw [← h1, ← neg_sub lambda mu, neg_smul, ← h2]
      abel
    have h4 := congrArg (fun x : X => (mu - lambda)⁻¹ • x) h3
    simpa only [ContinuousLinearMap.comp_apply, smul_smul, inv_mul_cancel₀ hsub, one_smul]
      using h4

end DivisionRing

/-! ## Invertible perturbations -/

section Perturbation

variable {𝕜 X : Type*} [Ring 𝕜] [AddCommGroup X] [TopologicalSpace X] [Module 𝕜 X]
  [IsTopologicalAddGroup X]
variable {A : X →ₗ.[𝕜] X} {lambda : 𝕜}

/-- **The common invertible perturbation witness.** If `lambda` lies in the resolvent set of `A`
and `I - B R(lambda, A)` is invertible, then
`R(lambda, A) (I - B R(lambda, A))⁻¹` inverts `lambda • I - (B + A)`.

This is the lower-level construction shared by bounded perturbations and perturbations of the
spectral parameter. -/
theorem _root_.ContinuousLinearMap.isResolventAt_vadd_of_isUnit_one_sub_mul_resolvent
    (B : X →L[𝕜] X)
    (h : lambda ∈ A.resolventSet) (hB : IsUnit (1 - B * A.resolvent lambda)) :
    IsResolventAt ((B : X →ₗ[𝕜] X) +ᵥ A) lambda
      (A.resolvent lambda * Ring.inverse (1 - B * A.resolvent lambda)) := by
  set R := A.resolvent lambda with hRdef
  have hunit : IsUnit (1 - B * R) := by simpa only [hRdef] using hB
  rw [ContinuousLinearMap.mul_def]
  set U : X →L[𝕜] X := Ring.inverse (1 - B * R) with hUdef
  have hcancel : ∀ y : X, U y - B (R (U y)) = y := by
    intro y
    have h1 : (1 - B * R) * U = 1 := by
      rw [hUdef, Ring.mul_inverse_cancel _ hunit]
    simpa using congrArg (fun S : X →L[𝕜] X => S y) h1
  have hsolve : ∀ y : X, U (y - B (R y)) = y := by
    intro y
    have h1 : U * (1 - B * R) = 1 := by
      rw [hUdef, Ring.inverse_mul_cancel _ hunit]
    simpa using congrArg (fun S : X →L[𝕜] X => S y) h1
  refine ⟨fun y => resolvent_mem_domain h (U y), fun y => ?_, fun x => ?_⟩
  · have hstep : lambda • (R ∘L U) y -
        ((B : X →ₗ[𝕜] X) +ᵥ A) ⟨(R ∘L U) y, resolvent_mem_domain h (U y)⟩
        = (lambda • R (U y) - A ⟨R (U y), resolvent_mem_domain h (U y)⟩) - B (R (U y)) := by
      rw [LinearPMap.vadd_apply]
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_coe]
      abel
    rw [hstep, smul_sub_apply_resolvent h (U y), hcancel y]
  · have hx : R (lambda • (x : X) - A x) = (x : X) :=
      resolvent_smul_sub_apply h ⟨(x : X), x.2⟩
    have hstep : lambda • (x : X) - ((B : X →ₗ[𝕜] X) +ᵥ A) x
        = (lambda • (x : X) - A x) - B (R (lambda • (x : X) - A x)) := by
      rw [LinearPMap.vadd_apply, hx]
      simp only [ContinuousLinearMap.coe_coe]
      abel
    rw [ContinuousLinearMap.comp_apply, hstep, hsolve, hx]

end Perturbation

/-! ## The bridge to Mathlib's algebraic resolvent

A continuous linear operator `T : X →L[𝕜] X` becomes an everywhere defined partial linear map
`(T : X →ₗ[𝕜] X).toPMap ⊤`. Its resolvent set and resolvent agree with Mathlib's
`resolventSet 𝕜 T` and `resolvent T`, computed in the algebra `X →L[𝕜] X`. -/

section ContinuousOperator

variable {𝕜 X : Type*} [CommRing 𝕜] [AddCommGroup X] [TopologicalSpace X] [Module 𝕜 X]
  [IsTopologicalAddGroup X] [ContinuousConstSMul 𝕜 X]
variable {T R : X →L[𝕜] X} {lambda : 𝕜}

/-- An inverse of `lambda • I - T` in the partial-map sense is a two-sided inverse in the algebra
`X →L[𝕜] X`, so `lambda • I - T` is a unit there. -/
theorem IsResolventAt.isUnit_toPMap_top
    (h : IsResolventAt ((T : X →ₗ[𝕜] X).toPMap ⊤) lambda R) :
    IsUnit (algebraMap 𝕜 (X →L[𝕜] X) lambda - T) := by
  have hright : (algebraMap 𝕜 (X →L[𝕜] X) lambda - T) * R = 1 := by
    ext y
    have h1 : lambda • R y - T (R y) = y := h.smul_sub_apply y
    simpa using h1
  have hleft : R * (algebraMap 𝕜 (X →L[𝕜] X) lambda - T) = 1 := by
    ext y
    have h1 : R (lambda • y - T y) = y := h.apply_smul_sub ⟨y, Submodule.mem_top⟩
    simpa using h1
  exact spectrum.mem_resolventSet_of_left_right_inverse hright hleft

/-- A unit `lambda • I - T` of the algebra `X →L[𝕜] X` inverts `lambda • I - T` in the
partial-map sense, with the algebra inverse as the resolvent. -/
theorem _root_.IsUnit.isResolventAt_toPMap_top
    (h : IsUnit (algebraMap 𝕜 (X →L[𝕜] X) lambda - T)) :
    IsResolventAt ((T : X →ₗ[𝕜] X).toPMap ⊤) lambda
      ((h.unit⁻¹ : (X →L[𝕜] X)ˣ) : X →L[𝕜] X) where
  mem_domain _ := Submodule.mem_top
  smul_sub_apply y := by
    have h1 : (algebraMap 𝕜 (X →L[𝕜] X) lambda - T)
        (((h.unit⁻¹ : (X →L[𝕜] X)ˣ) : X →L[𝕜] X) y) = y := by
      rw [← mul_apply_eq_comp, h.mul_val_inv, one_apply_eq_self]
    rwa [_root_.sub_apply, ContinuousLinearMap.algebraMap_apply] at h1
  apply_smul_sub x := by
    have h1 : ((h.unit⁻¹ : (X →L[𝕜] X)ˣ) : X →L[𝕜] X)
        ((algebraMap 𝕜 (X →L[𝕜] X) lambda - T) (x : X)) = (x : X) := by
      rw [← mul_apply_eq_comp, h.val_inv_mul, one_apply_eq_self]
    rwa [_root_.sub_apply, ContinuousLinearMap.algebraMap_apply] at h1

/-- **The continuous-operator bridge, membership half.** For a continuous linear operator `T`,
the partial-map resolvent set and Mathlib's algebraic resolvent set agree. -/
@[simp]
theorem _root_.ContinuousLinearMap.mem_resolventSet_toPMap_top_iff
    (T : X →L[𝕜] X) (lambda : 𝕜) :
    lambda ∈ ((T : X →ₗ[𝕜] X).toPMap ⊤).resolventSet ↔ lambda ∈ _root_.resolventSet 𝕜 T :=
  (_root_.LinearPMap.mem_resolventSet_iff).trans
    ⟨fun ⟨_, hR⟩ => hR.isUnit_toPMap_top,
      fun h => ⟨_, h.isResolventAt_toPMap_top⟩⟩

/-- **The continuous-operator bridge, value half.** For a continuous linear operator, the
partial-map resolvent is Mathlib's algebraic resolvent. -/
@[simp]
theorem _root_.ContinuousLinearMap.resolvent_toPMap_top
    (T : X →L[𝕜] X) {lambda : 𝕜}
    (h : lambda ∈ _root_.resolventSet 𝕜 T) :
    ((T : X →ₗ[𝕜] X).toPMap ⊤).resolvent lambda = _root_.resolvent T lambda := by
  rw [resolvent_eq_of_isResolventAt (h.isResolventAt_toPMap_top),
    spectrum.resolvent_eq h]

end ContinuousOperator

end LinearPMap

end

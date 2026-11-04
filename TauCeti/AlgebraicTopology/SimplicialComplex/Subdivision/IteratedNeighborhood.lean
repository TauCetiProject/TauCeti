/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Finite
public import TauCeti.AlgebraicTopology.SimplicialComplex.Subdivision.NDRPair
public import TauCeti.Topology.Homotopy.DeformationRetract

import Mathlib.Data.Nat.Cast.Order.Field
import TauCeti.Algebra.BigOperators.Finprod

/-!
# Open simplicial neighbourhoods in iterated barycentric subdivisions

Let `P` be a subcomplex of an abstract simplicial complex `K`. Its open simplicial neighbourhood
`openSimplicialNeighborhood K P` is an open neighbourhood of the polyhedron of `P` that strong
deformation retracts onto it. Repeating the construction after further barycentric subdivisions
gives smaller such neighbourhoods. This file shows that, when `K` is finite, they are cofinal
among all neighbourhoods of the polyhedron of `P`: every open set containing the polyhedron
contains one of them. A finite triangulated pair `(|K|, |P|)` therefore has arbitrarily small
open neighbourhoods of `|P|` that strong deformation retract onto it, each of which is a
simplicial neighbourhood of a subdivision of `K`.

Under the canonical homeomorphism `barycentricSubdivisionRealizationHomeomorph K`, the
polyhedron of `P` is the polyhedron of `subdivisionSubcomplex K P`, the chains of faces of `P`
regarded as a subcomplex of the barycentric subdivision of `K`. The neighbourhood after `n`
further subdivisions, `iteratedOpenSimplicialNeighborhood K P n`, is defined by recursion on `n`:
it is the image under that homeomorphism of the neighbourhood of `subdivisionSubcomplex K P`
after `n - 1` subdivisions of the subdivided complex.

The size of a neighbourhood is measured by the control function
`openSimplicialNeighborhoodControl K P`, which vanishes exactly on the polyhedron of `P`. One
subdivision step multiplies it by at most `1 - 1 / D` on the next neighbourhood, when every face
of `K` has at most `D` vertices. In barycentric terms: a point of the next neighbourhood is a
convex combination of barycenters of chains of faces of `K`, each of which contains a face of
`P`, and the barycenter of a chain with at most `D` members, at least one of them in `P`, has
mass at least `1 / D` on the faces of `P`. So the control function is at most `(1 - 1 / D) ^ n`
on the neighbourhood after `n` subdivisions, and a compactness argument gives cofinality.

## Main definitions

* `AbstractSimplicialComplex.iteratedOpenSimplicialNeighborhood`: the open simplicial
  neighbourhood of `P` after `n` further barycentric subdivisions.

## Main results

* `AbstractSimplicialComplex.exists_deformation_iteratedOpenSimplicialNeighborhood`: each of
  these neighbourhoods strong deformation retracts onto the polyhedron of `P`.
* `AbstractSimplicialComplex.antitone_iteratedOpenSimplicialNeighborhood`: the neighbourhoods
  decrease.
* `AbstractSimplicialComplex.coe_openSimplicialNeighborhoodControl_le_pow`: the control
  function of `P` is at most `(1 - 1 / D) ^ n` on the neighbourhood after `n` subdivisions.
* `AbstractSimplicialComplex.exists_iteratedOpenSimplicialNeighborhood_subset`: **cofinality.**
  For a finite complex, every open set containing the polyhedron of `P` contains one of the
  iterated neighbourhoods.

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer (1972),
  Chapter 3 (derived neighbourhoods).
-/

public section

noncomputable section

open Set Topology TauCeti.SetLike

namespace AbstractSimplicialComplex

universe u

variable {ι : Type u} (K : AbstractSimplicialComplex ι) (P : PreAbstractSimplicialComplex ι)

/-- The open simplicial neighbourhood of `P` after `n` further barycentric subdivisions of `K`.
For `n = 0` it is `openSimplicialNeighborhood K P`; for `n + 1` it is the image, under the
subdivision homeomorphism, of the neighbourhood of `subdivisionSubcomplex K P` after `n`
subdivisions of the barycentric subdivision of `K`. -/
def iteratedOpenSimplicialNeighborhood {ι : Type u} (K : AbstractSimplicialComplex ι)
    (P : PreAbstractSimplicialComplex ι) : ℕ → Set (Realization K)
  | 0 => K.openSimplicialNeighborhood P
  | n + 1 => barycentricSubdivisionRealizationHomeomorph K ''
      (TauCeti.PreAbstractSimplicialComplex.barycentricSubdivision
        K.toPreAbstractSimplicialComplex).iteratedOpenSimplicialNeighborhood
          (K.subdivisionSubcomplex P) n

@[simp]
theorem iteratedOpenSimplicialNeighborhood_zero :
    K.iteratedOpenSimplicialNeighborhood P 0 = K.openSimplicialNeighborhood P :=
  (rfl)

theorem iteratedOpenSimplicialNeighborhood_succ (n : ℕ) :
    K.iteratedOpenSimplicialNeighborhood P (n + 1) =
      barycentricSubdivisionRealizationHomeomorph K ''
        (TauCeti.PreAbstractSimplicialComplex.barycentricSubdivision
          K.toPreAbstractSimplicialComplex).iteratedOpenSimplicialNeighborhood
            (K.subdivisionSubcomplex P) n :=
  (rfl)

/-- The iterated open simplicial neighbourhoods are open. -/
theorem isOpen_iteratedOpenSimplicialNeighborhood (n : ℕ) :
    IsOpen (K.iteratedOpenSimplicialNeighborhood P n) := by
  induction n generalizing ι with
  | zero => exact K.isOpen_openSimplicialNeighborhood P
  | succ n ih =>
    rw [iteratedOpenSimplicialNeighborhood_succ]
    exact (barycentricSubdivisionRealizationHomeomorph K).isOpenMap _ (ih _ _)

/-- The polyhedron of `P` lies in each iterated open simplicial neighbourhood. -/
theorem setOf_support_mem_subset_iteratedOpenSimplicialNeighborhood (n : ℕ) :
    {y : Realization K | y.1.support ∈ P} ⊆ K.iteratedOpenSimplicialNeighborhood P n := by
  induction n generalizing ι with
  | zero => exact K.setOf_support_mem_subset_openSimplicialNeighborhood P
  | succ n ih =>
    rw [iteratedOpenSimplicialNeighborhood_succ,
      ← image_barycentricSubdivisionRealizationHomeomorph_setOf_support_mem]
    exact image_mono (ih _ _)

/-- **Each iterated open simplicial neighbourhood strong deformation retracts onto the
polyhedron of `P`.** The deformation is the straight-line open star deformation of the
`(n + 1)`-st barycentric subdivision, transported to the realization of `K`. -/
theorem exists_deformation_iteratedOpenSimplicialNeighborhood (n : ℕ) :
    ∃ r : C(K.iteratedOpenSimplicialNeighborhood P n, {y : Realization K | y.1.support ∈ P}),
      (∀ y, r (ContinuousMap.inclusion
        (K.setOf_support_mem_subset_iteratedOpenSimplicialNeighborhood P n) y) = y) ∧
      Nonempty (((ContinuousMap.inclusion
        (K.setOf_support_mem_subset_iteratedOpenSimplicialNeighborhood P n)).comp r).HomotopyRel
          (.id _) {y | (y : Realization K).1.support ∈ P}) := by
  induction n generalizing ι with
  | zero =>
    exact ⟨K.openSimplicialNeighborhoodRetraction P,
      K.openSimplicialNeighborhoodRetraction_inclusion P,
      ⟨(K.openSimplicialNeighborhoodDeformation P).symm⟩⟩
  | succ n ih =>
    exact (barycentricSubdivisionRealizationHomeomorph K).exists_deformation_of_image_eq _ _
      (iteratedOpenSimplicialNeighborhood_succ K P n).symm
      (image_barycentricSubdivisionRealizationHomeomorph_setOf_support_mem K P) (ih _ _)

/-! ### The control function under one subdivision -/

section Control

attribute [local instance] Classical.propDecidable

/-- In the coordinates `z` of the second subdivision, one minus the control function of `P` is
the average, weighted by the coordinates, of the proportion of faces of `P` in each chain. -/
private theorem one_sub_coe_openSimplicialNeighborhoodControl
    (z : Realization (TauCeti.PreAbstractSimplicialComplex.barycentricSubdivision
      (TauCeti.PreAbstractSimplicialComplex.barycentricSubdivision
        K.toPreAbstractSimplicialComplex).toPreAbstractSimplicialComplex)) :
    1 - (K.openSimplicialNeighborhoodControl P (barycentricSubdivisionRealizationHomeomorph K
        (barycentricSubdivisionRealizationHomeomorph _ z)) : ℝ) =
      ∑ ρ ∈ z.1.support,
        z.1 ρ * (((ρ.1.filter fun σ : Face K => σ.1 ∈ P).card : ℝ) * (ρ.1.card : ℝ)⁻¹) := by
  have hcoord (σ : Face K) : (barycentricSubdivisionRealizationHomeomorph _ z).1 σ =
      ∑ ρ ∈ z.1.support, z.1 ρ * if σ ∈ ρ.1 then (ρ.1.card : ℝ)⁻¹ else 0 := by
    rw [barycentricSubdivisionRealizationHomeomorph_apply, barycentricSubdivisionRealizationMap_val,
      barycentricSubdivisionLinearMap_apply]
    -- The two sides differ only in the decidability instance of the membership test.
    refine Finset.sum_congr rfl fun ρ _ => ?_
    congr
  -- Every face with a nonzero coordinate lies in some chain of the support.
  have hsupp : Function.support (fun σ => (barycentricSubdivisionRealizationHomeomorph _ z).1 σ) ⊆
      ↑(z.1.support.biUnion Subtype.val) := by
    intro σ hσ
    by_contra hU
    refine hσ ((hcoord σ).trans (Finset.sum_eq_zero fun ρ hρ => ?_))
    rw [ite_eq_right_of_eq_false _ _ (eq_false fun h => hU (Finset.mem_coe.2
      (Finset.mem_biUnion.2 ⟨ρ, hρ, h⟩))), mul_zero]
  rw [openSimplicialNeighborhoodControl_apply, Homeomorph.symm_apply_apply,
    coe_openStarControl_apply, sub_sub_cancel,
    TauCeti.finsum_mem_eq_sum_filter_of_support_subset _ _ hsupp]
  simp_rw [hcoord]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ρ hρ => ?_
  rw [← Finset.mul_sum, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
    nsmul_eq_mul]
  -- The faces of `P` in the chain `ρ` are the faces of `P` in the union of the chains of the
  -- support that lie in `ρ`.
  refine congrArg (fun s : Finset (Face K) => z.1 ρ * ((s.card : ℝ) * (ρ.1.card : ℝ)⁻¹)) ?_
  ext σ
  simp only [Finset.mem_filter, Finset.mem_biUnion]
  exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨⟨ρ, hρ, h.1⟩, h.2⟩, h.1⟩⟩

/-- In the coordinates `z` of the second subdivision, the control function of the subdivided
subcomplex is the total coordinate of the chains that are not faces of it. -/
private theorem coe_openSimplicialNeighborhoodControl_subdivisionSubcomplex
    (z : Realization (TauCeti.PreAbstractSimplicialComplex.barycentricSubdivision
      (TauCeti.PreAbstractSimplicialComplex.barycentricSubdivision
        K.toPreAbstractSimplicialComplex).toPreAbstractSimplicialComplex)) :
    ((TauCeti.PreAbstractSimplicialComplex.barycentricSubdivision
        K.toPreAbstractSimplicialComplex).openSimplicialNeighborhoodControl
          (K.subdivisionSubcomplex P) (barycentricSubdivisionRealizationHomeomorph _ z) : ℝ) =
      ∑ ρ ∈ z.1.support, z.1 ρ * if ρ.1 ∈ K.subdivisionSubcomplex P then 0 else 1 := by
  have hsum := Realization.sum_eq_one _ z
  rw [Finsupp.sum] at hsum
  rw [openSimplicialNeighborhoodControl_apply, Homeomorph.symm_apply_apply,
    coe_openStarControl_apply,
    TauCeti.finsum_mem_eq_sum_filter_of_support_subset _ _ (Finsupp.fun_support_eq _).subset,
    Finset.sum_filter]
  conv_lhs => rw [← hsum]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  split_ifs with h₁ h₂ h₂
  · ring
  · exact absurd h₁ h₂
  · exact absurd h₂ h₁
  · ring

/-- A weighted comparison of the control functions across one subdivision: if, on every chain
in the support of the second-subdivision coordinates `z`, one minus the proportion of faces of
`P` is at most `θ` times the indicator of not being a face of the subdivided subcomplex, then
the control function of `P` is at most `θ` times that of the subdivided subcomplex. -/
private theorem coe_openSimplicialNeighborhoodControl_le_mul_of_forall
    (z : Realization (TauCeti.PreAbstractSimplicialComplex.barycentricSubdivision
      (TauCeti.PreAbstractSimplicialComplex.barycentricSubdivision
        K.toPreAbstractSimplicialComplex).toPreAbstractSimplicialComplex)) (θ : ℝ)
    (h : ∀ ρ ∈ z.1.support,
      1 - ((ρ.1.filter fun σ : Face K => σ.1 ∈ P).card : ℝ) * (ρ.1.card : ℝ)⁻¹ ≤
        θ * if ρ.1 ∈ K.subdivisionSubcomplex P then 0 else 1) :
    (K.openSimplicialNeighborhoodControl P (barycentricSubdivisionRealizationHomeomorph K
        (barycentricSubdivisionRealizationHomeomorph _ z)) : ℝ) ≤
      θ * ((TauCeti.PreAbstractSimplicialComplex.barycentricSubdivision
        K.toPreAbstractSimplicialComplex).openSimplicialNeighborhoodControl
          (K.subdivisionSubcomplex P) (barycentricSubdivisionRealizationHomeomorph _ z) : ℝ) := by
  have hsum := Realization.sum_eq_one _ z
  rw [Finsupp.sum] at hsum
  have hc := one_sub_coe_openSimplicialNeighborhoodControl K P z
  rw [coe_openSimplicialNeighborhoodControl_subdivisionSubcomplex, Finset.mul_sum]
  calc (K.openSimplicialNeighborhoodControl P (barycentricSubdivisionRealizationHomeomorph K
        (barycentricSubdivisionRealizationHomeomorph _ z)) : ℝ)
      = ∑ ρ ∈ z.1.support,
          z.1 ρ * (1 - ((ρ.1.filter fun σ : Face K => σ.1 ∈ P).card : ℝ) * (ρ.1.card : ℝ)⁻¹) := by
        simp only [mul_sub, mul_one, Finset.sum_sub_distrib, hsum]
        linarith
    _ ≤ ∑ ρ ∈ z.1.support, θ * (z.1 ρ * if ρ.1 ∈ K.subdivisionSubcomplex P then 0 else 1) :=
        Finset.sum_le_sum fun ρ hρ => by
          rw [mul_left_comm]
          exact mul_le_mul_of_nonneg_left (h ρ hρ) (Realization.nonneg _ z ρ)

/-- One minus the proportion of faces of `P` in a chain is zero on chains of faces of `P`. -/
private theorem one_sub_card_filter_mul_inv_eq_zero {ρ : Finset (Face K)} (hρ : ρ.Nonempty)
    (hP : ∀ σ ∈ ρ, σ.1 ∈ P) :
    1 - ((ρ.filter fun σ : Face K => σ.1 ∈ P).card : ℝ) * (ρ.card : ℝ)⁻¹ = 0 := by
  rw [Finset.filter_true_of_mem hP,
    mul_inv_cancel₀ (Nat.cast_ne_zero.2 (Finset.card_pos.2 hρ).ne'), sub_self]

/-- **The control function does not increase under subdivision**: the control function of `P`
at the image of a point of the subdivision is at most the control function of the subdivided
subcomplex at that point. -/
theorem openSimplicialNeighborhoodControl_barycentricSubdivisionRealizationHomeomorph_le
    (y : Realization (TauCeti.PreAbstractSimplicialComplex.barycentricSubdivision
      K.toPreAbstractSimplicialComplex)) :
    K.openSimplicialNeighborhoodControl P (barycentricSubdivisionRealizationHomeomorph K y) ≤
      (TauCeti.PreAbstractSimplicialComplex.barycentricSubdivision
        K.toPreAbstractSimplicialComplex).openSimplicialNeighborhoodControl
          (K.subdivisionSubcomplex P) y := by
  obtain ⟨z, rfl⟩ := (barycentricSubdivisionRealizationHomeomorph _).surjective y
  have h := coe_openSimplicialNeighborhoodControl_le_mul_of_forall K P z 1 fun ρ _ => by
    have hne := (TauCeti.PreAbstractSimplicialComplex.barycentricSubdivision
      K.toPreAbstractSimplicialComplex).isRelLowerSet_faces.prop_of_mem ρ.2
    split_ifs with hρP <;> rw [mem_subdivisionSubcomplex_iff] at hρP
    · rw [mul_zero]
      exact (one_sub_card_filter_mul_inv_eq_zero K P hne hρP.2).le
    · rw [mul_one, sub_le_self_iff]
      positivity
  rw [one_mul] at h
  exact h

/-- **One subdivision contracts the control function on the next neighbourhood.** If every face
of `K` has at most `D` vertices, then on the open simplicial neighbourhood of the subdivided
subcomplex, the control function of `P` is at most `1 - 1 / D` times the control function of the
subdivided subcomplex. -/
theorem coe_openSimplicialNeighborhoodControl_barycentricSubdivisionRealizationHomeomorph_le_mul
    {D : ℕ} (hD : ∀ σ ∈ K, σ.card ≤ D)
    {y : Realization (TauCeti.PreAbstractSimplicialComplex.barycentricSubdivision
      K.toPreAbstractSimplicialComplex)}
    (hy : y ∈ (TauCeti.PreAbstractSimplicialComplex.barycentricSubdivision
      K.toPreAbstractSimplicialComplex).openSimplicialNeighborhood (K.subdivisionSubcomplex P)) :
    (K.openSimplicialNeighborhoodControl P (barycentricSubdivisionRealizationHomeomorph K y) :
        ℝ) ≤
      (1 - (D : ℝ)⁻¹) * ((TauCeti.PreAbstractSimplicialComplex.barycentricSubdivision
        K.toPreAbstractSimplicialComplex).openSimplicialNeighborhoodControl
          (K.subdivisionSubcomplex P) y : ℝ) := by
  obtain ⟨z, rfl⟩ := (barycentricSubdivisionRealizationHomeomorph _).surjective y
  -- Some chain `ρ₀` in the support of `z` consists of faces of `P`.
  rw [← mem_preimage,
    preimage_barycentricSubdivisionRealizationHomeomorph_openSimplicialNeighborhood,
    mem_openStarRealizationSet] at hy
  obtain ⟨ρ₀, hρ₀P, hρ₀⟩ := hy
  replace hρ₀P := (K.mem_subdivisionSubcomplex_iff P).1 hρ₀P
  have hρ₀T : ρ₀ ∈ z.1.support := Finsupp.mem_support_iff.2 hρ₀.ne'
  refine coe_openSimplicialNeighborhoodControl_le_mul_of_forall K P z _ fun ρ hρ => ?_
  have hne := (TauCeti.PreAbstractSimplicialComplex.barycentricSubdivision
    K.toPreAbstractSimplicialComplex).isRelLowerSet_faces.prop_of_mem ρ.2
  split_ifs with hρP <;> rw [mem_subdivisionSubcomplex_iff] at hρP
  · rw [mul_zero]
    exact (one_sub_card_filter_mul_inv_eq_zero K P hne hρP.2).le
  rw [mul_one]
  -- The support of `z` is a chain of chains, so `ρ` contains `ρ₀` or consists of faces of `P`.
  rcases TauCeti.PreAbstractSimplicialComplex.subset_or_subset_of_mem_barycentricSubdivision
    (support_mem _ z) hρ hρ₀T with hle | hle
  · exact absurd ⟨ρ.2, fun σ hσ => hρ₀P.2 σ (hle hσ)⟩ hρP
  -- So some member of `ρ` is a face of `P`, and `ρ` has at most `D` members.
  obtain ⟨σ₀, hσ₀⟩ := (TauCeti.PreAbstractSimplicialComplex.barycentricSubdivision
    K.toPreAbstractSimplicialComplex).isRelLowerSet_faces.prop_of_mem ρ₀.2
  have hpos : (0 : ℝ) < ρ.1.card := Nat.cast_pos.2 (Finset.card_pos.2 hne)
  have hcard : (1 : ℝ) ≤ (ρ.1.filter fun σ : Face K => σ.1 ∈ P).card :=
    Nat.one_le_cast.2 (Finset.card_pos.2 ⟨σ₀, Finset.mem_filter.2 ⟨hle hσ₀, hρ₀P.2 σ₀ hσ₀⟩⟩)
  have hρD : (ρ.1.card : ℝ) ≤ D := Nat.cast_le.2
    (TauCeti.PreAbstractSimplicialComplex.card_le_of_mem_barycentricSubdivision hD ρ.2)
  have hinv : (D : ℝ)⁻¹ ≤ (ρ.1.card : ℝ)⁻¹ := inv_anti₀ hpos hρD
  have := mul_le_mul_of_nonneg_right hcard (inv_nonneg.2 hpos.le)
  linarith

end Control

/-! ### Decay and cofinality -/

/-- The neighbourhood after one more subdivision lies in the previous one. -/
theorem iteratedOpenSimplicialNeighborhood_succ_subset (n : ℕ) :
    K.iteratedOpenSimplicialNeighborhood P (n + 1) ⊆ K.iteratedOpenSimplicialNeighborhood P n := by
  induction n generalizing ι with
  | zero =>
    rintro _ ⟨y, hy, rfl⟩
    rw [iteratedOpenSimplicialNeighborhood_zero, ← openSimplicialNeighborhoodControl_lt_one_iff]
      at hy ⊢
    exact (openSimplicialNeighborhoodControl_barycentricSubdivisionRealizationHomeomorph_le
      K P y).trans_lt hy
  | succ n ih =>
    rw [iteratedOpenSimplicialNeighborhood_succ K P (n + 1),
      iteratedOpenSimplicialNeighborhood_succ K P n]
    exact image_mono (ih _ _)

/-- The iterated open simplicial neighbourhoods decrease. -/
theorem antitone_iteratedOpenSimplicialNeighborhood :
    Antitone (K.iteratedOpenSimplicialNeighborhood P) :=
  antitone_nat_of_succ_le (K.iteratedOpenSimplicialNeighborhood_succ_subset P)

/-- **Decay of the control function.** If every face of `K` has at most `D` vertices, then the
control function of `P` is at most `(1 - 1 / D) ^ n` on the open simplicial neighbourhood of `P`
after `n` further subdivisions. -/
theorem coe_openSimplicialNeighborhoodControl_le_pow {D : ℕ} (hD : ∀ σ ∈ K, σ.card ≤ D)
    {n : ℕ} {y : Realization K} (hy : y ∈ K.iteratedOpenSimplicialNeighborhood P n) :
    (K.openSimplicialNeighborhoodControl P y : ℝ) ≤ (1 - (D : ℝ)⁻¹) ^ n := by
  induction n generalizing ι with
  | zero => simpa using (K.openSimplicialNeighborhoodControl P y).2.2
  | succ n ih =>
    obtain ⟨x, hx, rfl⟩ := hy
    have hθ : 0 ≤ 1 - (D : ℝ)⁻¹ := sub_nonneg.2 (Nat.cast_inv_le_one D)
    have hx₀ : x ∈ (TauCeti.PreAbstractSimplicialComplex.barycentricSubdivision
        K.toPreAbstractSimplicialComplex).openSimplicialNeighborhood (K.subdivisionSubcomplex P) :=
      antitone_iteratedOpenSimplicialNeighborhood _ _ (Nat.zero_le n) hx
    have hD' : ∀ ρ ∈ TauCeti.PreAbstractSimplicialComplex.barycentricSubdivision
        K.toPreAbstractSimplicialComplex, ρ.card ≤ D := fun ρ hρ =>
      TauCeti.PreAbstractSimplicialComplex.card_le_of_mem_barycentricSubdivision hD hρ
    calc _ ≤ (1 - (D : ℝ)⁻¹) * ((TauCeti.PreAbstractSimplicialComplex.barycentricSubdivision
          K.toPreAbstractSimplicialComplex).openSimplicialNeighborhoodControl
            (K.subdivisionSubcomplex P) x : ℝ) :=
          coe_openSimplicialNeighborhoodControl_barycentricSubdivisionRealizationHomeomorph_le_mul
            K P hD hx₀
      _ ≤ (1 - (D : ℝ)⁻¹) * (1 - (D : ℝ)⁻¹) ^ n := mul_le_mul_of_nonneg_left (ih _ _ hD' hx) hθ
      _ = (1 - (D : ℝ)⁻¹) ^ (n + 1) := (pow_succ' _ _).symm

/-- **The iterated neighbourhoods eventually avoid every compact set disjoint from `P`.** If the
faces of `K` have boundedly many vertices and `C` is a compact subset of the realization of `K`
disjoint from the polyhedron of `P`, then some iterated open simplicial neighbourhood of `P` is
disjoint from `C`. -/
theorem exists_disjoint_iteratedOpenSimplicialNeighborhood {D : ℕ}
    (hD : ∀ σ ∈ K, σ.card ≤ D) {C : Set (Realization K)} (hC : IsCompact C)
    (hCP : Disjoint C {y | y.1.support ∈ P}) :
    ∃ n, Disjoint (K.iteratedOpenSimplicialNeighborhood P n) C := by
  rcases C.eq_empty_or_nonempty with rfl | hne
  · exact ⟨0, disjoint_empty _⟩
  -- The control function has a positive minimum `μ` on `C`.
  obtain ⟨x, hxC, hmin⟩ :=
    hC.exists_isMinOn hne (K.openSimplicialNeighborhoodControl P).continuous.continuousOn
  have hμ : (0 : ℝ) < K.openSimplicialNeighborhoodControl P x := by
    refine lt_of_le_of_ne (K.openSimplicialNeighborhoodControl P x).2.1 fun h => ?_
    exact hCP.notMem_of_mem_left hxC
      ((K.openSimplicialNeighborhoodControl_eq_zero_iff P).1 (Subtype.ext h.symm))
  -- With the bound `D + 1 ≥ 1`, the decay factor is less than one.
  have hD' : ∀ σ ∈ K, σ.card ≤ D + 1 := fun σ hσ => (hD σ hσ).trans (Nat.le_succ D)
  have hθ : 1 - ((D + 1 : ℕ) : ℝ)⁻¹ < 1 :=
    sub_lt_self _ (inv_pos.2 (Nat.cast_pos.2 (Nat.succ_pos D)))
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hμ hθ
  refine ⟨n, Set.disjoint_left.2 fun y hy hyC => ?_⟩
  have h₁ := coe_openSimplicialNeighborhoodControl_le_pow K P hD' hy
  have h₂ : (K.openSimplicialNeighborhoodControl P x : ℝ) ≤
      K.openSimplicialNeighborhoodControl P y := hmin hyC
  linarith

/-- **Cofinality of the iterated open simplicial neighbourhoods.** If `K` has finitely many faces,
every open subset of its realization containing the polyhedron of `P` contains the open
simplicial neighbourhood of `P` after some number of further barycentric subdivisions. -/
theorem exists_iteratedOpenSimplicialNeighborhood_subset (hfin : K.faces.Finite)
    {W : Set (Realization K)} (hW : IsOpen W) (hPW : {y : Realization K | y.1.support ∈ P} ⊆ W) :
    ∃ n, K.iteratedOpenSimplicialNeighborhood P n ⊆ W := by
  have := compactSpace_realization_of_finite_faces K hfin
  obtain ⟨D, hD⟩ := (hfin.image Finset.card).bddAbove
  obtain ⟨n, hn⟩ := K.exists_disjoint_iteratedOpenSimplicialNeighborhood P
    (fun σ hσ => hD (mem_image_of_mem _ hσ)) hW.isClosed_compl.isCompact
    (disjoint_compl_left_iff_subset.2 hPW)
  exact ⟨n, fun y hy => by_contra fun hyW => hn.notMem_of_mem_left hy hyW⟩

end AbstractSimplicialComplex

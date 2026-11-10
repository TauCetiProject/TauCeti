/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Cylinder
public import Mathlib.Topology.Homotopy.HomotopyGroup
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import TauCeti.Geometry.Manifold.SmoothApprox

/-!
# Periods of closed two-forms on the second homotopy group

Let `φ` be a closed `C¹` two-form on a compact manifold `M`, for instance the symplectic form of a
closed symplectic manifold. Its integral over a sphere only depends on the homotopy class of the
sphere, and it is additive under the group law of `π₂(M, x)`. This file constructs the resulting
**period homomorphism** `TauCeti.spherePeriodHom` from `π₂(M, x)`, written additively, to the
coefficients. For a symplectic form it is the symplectic area of spheres, the homomorphism `ω` on
spherical classes through which capped Hamiltonian Floer theory defines its period group and the
recapping law of the action.

An element of `π₂(M, x)` is a homotopy class, relative to the boundary, of maps of the square
`[0, 1]²` sending the boundary to `x` (Mathlib's `GenLoop`). A map `u : ℝ × ℝ → M` of the plane
which sends the boundary of the unit square to `x` restricts to such a map
(`TauCeti.squareGenLoop`). When `u` is `C²`, the integral of `φ` over the sphere is the integral
`TauCeti.rectangleIntegral φ u (0, 0) (1, 1)` of the pullback of `φ` over the square.

* Every class has a smooth representative: a continuous map of the square constant near its
  boundary is homotopic, relative to that neighbourhood, to a smooth map by the Whitney
  approximation theorem (`ContinuousMap.exists_contMDiff_homotopicRel`), which needs `M` compact.
* Two `C²` representatives of the same class have the same integral
  (`TauCeti.rectangleIntegral_eq_of_squareGenLoop_eq`). A continuous homotopy between them is made
  smooth by Whitney approximation relative to the boundary and to the two ends, and the integral of
  a closed form is invariant under smooth homotopies through spheres
  (`TauCeti.rectangleIntegral_eq_of_homotopy`).
* Hence the integral over any `C²` representative computes the period
  (`TauCeti.spherePeriod_mk`). The product in `π₂(M, x)` concatenates representatives along the
  first coordinate, so the period is additive (`TauCeti.spherePeriod_mul`).

The period vanishes for forms vanishing on spheres
(`TauCeti.VanishesOnSpheres.spherePeriod_eq_zero`), hence for exact forms
(`TauCeti.spherePeriod_mextDeriv`), and it is linear in the form. It is the two-dimensional
analogue of the period homomorphism `TauCeti.periodHom` of a closed one-form on the fundamental
group.

## Main definitions

* `TauCeti.squareGenLoop`: the element of `π₂(M, x)` represented by a map of the plane sending the
  boundary of the unit square to `x`.
* `TauCeti.spherePeriod φ x`: the integral of a two-form over the classes of `π₂(M, x)`.
* `TauCeti.spherePeriodHom`: for a closed `C¹` form on a compact manifold, the period as a
  homomorphism from `π₂(M, x)` to the coefficients.

## Main results

* `TauCeti.rectangleIntegral_eq_of_squareGenLoop_eq`: homotopic `C²` spheres have the same integral.
* `TauCeti.spherePeriod_mk`: the period of the class of a `C²` sphere is its integral.
* `TauCeti.spherePeriod_mul`: the period is additive on `π₂(M, x)`.

## References

* R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*, GTM 82, Springer, 1982, §4
  (homotopy invariance of integrals of closed forms).
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., GTM 218, Springer, 2013, Theorems 6.26
  and 6.29 (Whitney approximation).
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS, 2012,
  Section 11.1 (the symplectic area of spherical classes and the Novikov ring).
-/

public section

noncomputable section

open Set Function Topology
open scoped Manifold ContDiff Topology.Homotopy

namespace TauCeti

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {x : M}

/-! ### Spheres as maps of the plane -/

/-- A point of the boundary of the cube `I²`, read as a point of the unit square of the plane, has a
coordinate equal to `0` or `1`. -/
private theorem coe_eq_zero_or_eq_one_of_mem_boundary {y : Fin 2 → unitInterval}
    (hy : y ∈ Cube.boundary (Fin 2)) :
    (y 0 : ℝ) = 0 ∨ (y 0 : ℝ) = 1 ∨ (y 1 : ℝ) = 0 ∨ (y 1 : ℝ) = 1 := by
  obtain ⟨i, hi⟩ := hy
  fin_cases i <;> rcases hi with h | h <;> simp_all

/-- The generalized loop `I² → M` at `x` given by a continuous map `u` of the plane sending the
boundary of the unit square to `x`, restricted to the square. Its class is an element of
`π₂(M, x)`. -/
def squareGenLoop (u : ℝ × ℝ → M) (hu : Continuous u)
    (hx : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, (s = 0 ∨ s = 1 ∨ t = 0 ∨ t = 1) →
      u (s, t) = x) : Ω^ (Fin 2) M x :=
  ⟨⟨fun y ↦ u ((y 0 : ℝ), (y 1 : ℝ)), by fun_prop⟩, fun _ hy ↦
    hx _ (Subtype.prop _) _ (Subtype.prop _) (coe_eq_zero_or_eq_one_of_mem_boundary hy)⟩

@[simp]
theorem squareGenLoop_apply (u : ℝ × ℝ → M) (hu : Continuous u)
    (hx : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, (s = 0 ∨ s = 1 ∨ t = 0 ∨ t = 1) →
      u (s, t) = x) (y : Fin 2 → unitInterval) :
    squareGenLoop u hu hx y = u ((y 0 : ℝ), (y 1 : ℝ)) :=
  (rfl)

/-- Two maps of the plane sending the boundary of the unit square to `x` are homotopic as
generalized loops when they are joined by a homotopy which sends the boundary of the square to `x`
at all times. -/
theorem squareGenLoop_homotopic {u₀ u₁ : ℝ × ℝ → M} {hu₀ : Continuous u₀} {hu₁ : Continuous u₁}
    {hx₀ : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, (s = 0 ∨ s = 1 ∨ t = 0 ∨ t = 1) →
      u₀ (s, t) = x}
    {hx₁ : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, (s = 0 ∨ s = 1 ∨ t = 0 ∨ t = 1) →
      u₁ (s, t) = x}
    {Φ : unitInterval × (ℝ × ℝ) → M} (hΦ : Continuous Φ) (h₀ : ∀ z, Φ (0, z) = u₀ z)
    (h₁ : ∀ z, Φ (1, z) = u₁ z)
    (hΦx : ∀ c, ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, (s = 0 ∨ s = 1 ∨ t = 0 ∨ t = 1) →
      Φ (c, (s, t)) = x) :
    GenLoop.Homotopic (squareGenLoop u₀ hu₀ hx₀) (squareGenLoop u₁ hu₁ hx₁) :=
  Nonempty.intro
    { toFun := fun p ↦ Φ (p.1, ((p.2 0 : ℝ), (p.2 1 : ℝ)))
      continuous_toFun := by fun_prop
      map_zero_left := fun _ ↦ h₀ _
      map_one_left := fun _ ↦ h₁ _
      prop' := fun c y hy ↦ by
        have h := coe_eq_zero_or_eq_one_of_mem_boundary hy
        exact (hΦx c _ (Subtype.prop _) _ (Subtype.prop _) h).trans
          (hx₀ _ (Subtype.prop _) _ (Subtype.prop _) h).symm }

/-! ### The period of a two-form on `π₂` -/

/-- The **period** of a two-form `φ` on `π₂(M, x)`: the integral of `φ` over the unit square along a
smooth map of the plane which sends the boundary of the square to `x` and represents the given
class. It does not depend on the representative when `φ` is closed and `C¹` and `M` is compact
(`TauCeti.spherePeriod_mk`), and it is `0` on classes without a smooth representative. -/
def spherePeriod (φ : RoughForm I M F 2) (x : M) (a : π_ 2 M x) : F := by
  classical
  exact if h : ∃ (u : ℝ × ℝ → M) (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I ∞ u)
      (hx : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, (s = 0 ∨ s = 1 ∨ t = 0 ∨ t = 1) →
        u (s, t) = x),
      (⟦squareGenLoop u hu.continuous hx⟧ : π_ 2 M x) = a then
    rectangleIntegral φ h.choose (0, 0) (1, 1)
  else 0

/-- The period of a form vanishing on spheres vanishes. -/
theorem VanishesOnSpheres.spherePeriod_eq_zero {φ : RoughForm I M F 2}
    (hφ : VanishesOnSpheres φ) (a : π_ 2 M x) : spherePeriod φ x a = 0 := by
  rw [spherePeriod]
  split_ifs with h
  · obtain ⟨hu, hx, -⟩ := h.choose_spec
    have hI0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := left_mem_Icc.2 zero_le_one
    have hI1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := right_mem_Icc.2 zero_le_one
    exact (vanishesOnSpheres_iff φ).1 hφ _ hu
      (fun t ht ↦ (hx 0 hI0 t ht (Or.inl rfl)).trans (hx 0 hI0 0 hI0 (Or.inl rfl)).symm)
      (fun t ht ↦ (hx 1 hI1 t ht (Or.inr (Or.inl rfl))).trans
        (hx 1 hI1 0 hI0 (Or.inr (Or.inl rfl))).symm)
      (fun s hs ↦ (hx s hs 1 hI1 (Or.inr (Or.inr (Or.inr rfl)))).trans
        (hx s hs 0 hI0 (Or.inr (Or.inr (Or.inl rfl)))).symm)
  · rfl

/-- The periods of exact two-forms vanish. -/
theorem spherePeriod_mextDeriv [IsManifold I 2 M] {α : RoughForm I M F 1}
    (hα : IsSmoothForm I 1 α) (a : π_ 2 M x) : spherePeriod (mextDeriv α) x a = 0 :=
  (vanishesOnSpheres_mextDeriv hα).spherePeriod_eq_zero a

/-- The period is linear in the form: scalar multiples. -/
theorem spherePeriod_smul (c : ℝ) (φ : RoughForm I M F 2) (a : π_ 2 M x) :
    spherePeriod (c • φ) x a = c • spherePeriod φ x a := by
  simp only [spherePeriod]
  split_ifs
  · exact rectangleIntegral_smul c φ _ _ _
  · exact (smul_zero c).symm

/-- The period is linear in the form: sums of continuous forms. -/
theorem spherePeriod_add [IsManifold I 1 M] {φ ψ : RoughForm I M F 2} (hφ : IsSmoothForm I 0 φ)
    (hψ : IsSmoothForm I 0 ψ) (a : π_ 2 M x) :
    spherePeriod (φ + ψ) x a = spherePeriod φ x a + spherePeriod ψ x a := by
  simp only [spherePeriod]
  split_ifs with h
  · obtain ⟨hu, -, -⟩ := h.choose_spec
    have hu1 : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 h.choose := hu.of_le (by simp)
    have hint {θ : RoughForm I M F 2} (hθ : IsSmoothForm I 0 θ) (s : ℝ) :
        IntervalIntegrable (fun t ↦ mpullback 𝓘(ℝ, ℝ × ℝ) I h.choose θ (s, t) ![(1, 0), (0, 1)])
          MeasureTheory.volume 0 1 :=
      ((hθ.continuous_mpullback_apply hu1 ![(1, 0), (0, 1)]).comp
        (Continuous.prodMk_right s)).intervalIntegrable 0 1
    exact rectangleIntegral_add (a := (0, 0)) (b := (1, 1)) (fun s _ ↦ hint hφ s)
      (fun s _ ↦ hint hψ s) ((continuous_integral_mpullback hφ hu1 0 1).intervalIntegrable 0 1)
      ((continuous_integral_mpullback hψ hu1 0 1).intervalIntegrable 0 1)
  · exact (add_zero 0).symm

/-! ### Squeezing spheres away from the boundary of the square -/

/-- The smooth squeeze `s ↦ β (3 s - 1)` of the line onto `[0, 1]`, for the smooth transition
function `β`: it vanishes for `s ≤ 1/3` and equals `1` for `s ≥ 2/3`. Precomposing a sphere with
it in both coordinates gives a homotopic sphere which is constant near the boundary of the
square. -/
private def squeeze (s : ℝ) : ℝ :=
  Real.smoothTransition (3 * s - 1)

private theorem squeeze_mem_Icc (s : ℝ) : squeeze s ∈ Icc (0 : ℝ) 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

private theorem squeeze_of_le {s : ℝ} (hs : s ≤ 1 / 3) : squeeze s = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

private theorem squeeze_of_ge {s : ℝ} (hs : 2 / 3 ≤ s) : squeeze s = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

private theorem contDiff_squeeze {n : ℕ∞} : ContDiff ℝ n squeeze :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)

/-- The segment from `s` to `squeeze s` stays in `[0, 1]` for `s ∈ [0, 1]`. -/
private theorem add_mul_squeeze_sub_mem_Icc {s c : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (hc : c ∈ Icc (0 : ℝ) 1) : s + c * (squeeze s - s) ∈ Icc (0 : ℝ) 1 := by
  have hq := squeeze_mem_Icc s
  constructor <;> nlinarith [hs.1, hs.2, hc.1, hc.2, hq.1, hq.2, mul_nonneg hc.1 hq.1,
    mul_nonneg (sub_nonneg.2 hc.2) hs.1, mul_nonneg hc.1 (sub_nonneg.2 hq.2),
    mul_nonneg (sub_nonneg.2 hc.2) (sub_nonneg.2 hs.2)]

/-- The segment from `s` to `squeeze s` fixes the endpoints `0` and `1` of `[0, 1]`. -/
private theorem add_mul_squeeze_sub_eq {s c : ℝ} (hs : s = 0 ∨ s = 1) :
    s + c * (squeeze s - s) = s := by
  rcases hs with rfl | rfl
  · simp [squeeze_of_le (by norm_num : (0 : ℝ) ≤ 1 / 3)]
  · simp [squeeze_of_ge (by norm_num : (2 / 3 : ℝ) ≤ 1)]

omit [TopologicalSpace M] in
/-- A map sending the boundary of the unit square to `x`, precomposed with the squeeze in both
coordinates, equals `x` off the open square `(1/3, 2/3)²`. -/
private theorem comp_squeeze_eq {u : ℝ × ℝ → M}
    (hx : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, (s = 0 ∨ s = 1 ∨ t = 0 ∨ t = 1) →
      u (s, t) = x)
    {z : ℝ × ℝ} (hz : z.1 ≤ 1 / 3 ∨ 2 / 3 ≤ z.1 ∨ z.2 ≤ 1 / 3 ∨ 2 / 3 ≤ z.2) :
    (u ∘ Prod.map squeeze squeeze) z = x := by
  refine hx _ (squeeze_mem_Icc _) _ (squeeze_mem_Icc _) ?_
  rcases hz with h | h | h | h
  · exact Or.inl (squeeze_of_le h)
  · exact Or.inr (Or.inl (squeeze_of_ge h))
  · exact Or.inr (Or.inr (Or.inl (squeeze_of_le h)))
  · exact Or.inr (Or.inr (Or.inr (squeeze_of_ge h)))

/-- Squeezing a map in both coordinates by the segment from the identity to `squeeze` gives a
smooth homotopy through maps sending the boundary of the unit square to `x`. -/
private theorem contDiff_squeezeHomotopy {n : ℕ∞} :
    ContDiff ℝ n fun p : (ℝ × ℝ) × ℝ ↦
      (p.1.1 + p.2 * (squeeze p.1.1 - p.1.1), p.1.2 + p.2 * (squeeze p.1.2 - p.1.2)) := by
  have h := contDiff_squeeze (n := n)
  fun_prop

/-- The squeeze does not change the class of a sphere. -/
private theorem squareGenLoop_comp_squeeze {u : ℝ × ℝ → M} (hu : Continuous u)
    (hx : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, (s = 0 ∨ s = 1 ∨ t = 0 ∨ t = 1) →
      u (s, t) = x) :
    (⟦squareGenLoop (u ∘ Prod.map squeeze squeeze)
        (hu.comp ((contDiff_squeeze (n := 0)).continuous.prodMap
          (contDiff_squeeze (n := 0)).continuous))
        fun s _ t _ h ↦ comp_squeeze_eq hx (by
          rcases h with rfl | rfl | rfl | rfl <;> norm_num)⟧ : π_ 2 M x) =
      ⟦squareGenLoop u hu hx⟧ := by
  refine Quotient.sound (squareGenLoop_homotopic (Φ := fun p ↦ u
    (p.2.1 + (1 - (p.1 : ℝ)) * (squeeze p.2.1 - p.2.1),
      p.2.2 + (1 - (p.1 : ℝ)) * (squeeze p.2.2 - p.2.2))) ?_ ?_ ?_ ?_)
  · have h := (contDiff_squeeze (n := 0)).continuous
    fun_prop
  · intro z
    simp [Prod.map]
  · intro z
    simp
  · intro c s hs t ht h
    have hc : 1 - (c : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨sub_nonneg.2 c.2.2, by linarith [c.2.1]⟩
    refine hx _ (add_mul_squeeze_sub_mem_Icc hs hc) _ (add_mul_squeeze_sub_mem_Icc ht hc) ?_
    rcases h with h | h | h | h
    · exact Or.inl ((add_mul_squeeze_sub_eq (Or.inl h)).trans h)
    · exact Or.inr (Or.inl ((add_mul_squeeze_sub_eq (Or.inr h)).trans h))
    · exact Or.inr (Or.inr (Or.inl ((add_mul_squeeze_sub_eq (Or.inl h)).trans h)))
    · exact Or.inr (Or.inr (Or.inr ((add_mul_squeeze_sub_eq (Or.inr h)).trans h)))

/-- Squeezing a `C²` sphere does not change the integral of a closed `C¹` form over it: the segment
from the identity to `squeeze` is a smooth homotopy through spheres. -/
private theorem rectangleIntegral_comp_squeeze [CompleteSpace F] [IsManifold I 2 M]
    {φ : RoughForm I M F 2} (hφ : IsSmoothForm I 1 φ) (hdφ : mextDeriv φ = 0) {u : ℝ × ℝ → M}
    (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 2 u)
    (hx : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, (s = 0 ∨ s = 1 ∨ t = 0 ∨ t = 1) →
      u (s, t) = x) :
    rectangleIntegral φ (u ∘ Prod.map squeeze squeeze) (0, 0) (1, 1) =
      rectangleIntegral φ u (0, 0) (1, 1) := by
  set Φ : (ℝ × ℝ) × ℝ → M := fun p ↦
    u (p.1.1 + p.2 * (squeeze p.1.1 - p.1.1), p.1.2 + p.2 * (squeeze p.1.2 - p.1.2))
  have hΦ : ContMDiff 𝓘(ℝ, (ℝ × ℝ) × ℝ) I 2 Φ :=
    hu.comp (contMDiff_iff_contDiff.2 contDiff_squeezeHomotopy)
  -- Every edge of the square stays at `x` during the homotopy.
  have hedge {s t c : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) (hc : c ∈ Icc (0 : ℝ) 1)
      (h : s = 0 ∨ s = 1 ∨ t = 0 ∨ t = 1) : Φ ((s, t), c) = x := by
    refine hx _ (add_mul_squeeze_sub_mem_Icc hs hc) _ (add_mul_squeeze_sub_mem_Icc ht hc) ?_
    rcases h with h | h | h | h
    · exact Or.inl ((add_mul_squeeze_sub_eq (Or.inl h)).trans h)
    · exact Or.inr (Or.inl ((add_mul_squeeze_sub_eq (Or.inr h)).trans h))
    · exact Or.inr (Or.inr (Or.inl ((add_mul_squeeze_sub_eq (Or.inl h)).trans h)))
    · exact Or.inr (Or.inr (Or.inr ((add_mul_squeeze_sub_eq (Or.inr h)).trans h)))
  have h01 : uIcc (0 : ℝ) 1 = Icc 0 1 := uIcc_of_le zero_le_one
  have hI0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := left_mem_Icc.2 zero_le_one
  have hI1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := right_mem_Icc.2 zero_le_one
  have h := rectangleIntegral_eq_of_homotopy hφ hdφ hΦ (a := (0, 0)) (b := (1, 1))
    (Or.inr fun t ht c hc ↦ by
      rw [hedge hI0 (h01 ▸ ht) hc (Or.inl rfl), hedge hI0 hI0 hc (Or.inl rfl)])
    (Or.inr fun t ht c hc ↦ by
      rw [hedge hI1 (h01 ▸ ht) hc (Or.inr (Or.inl rfl)),
        hedge hI1 hI1 hc (Or.inr (Or.inl rfl))])
    (fun s hs c hc ↦ by
      rw [hedge (h01 ▸ hs) hI1 hc (Or.inr (Or.inr (Or.inr rfl))),
        hedge (h01 ▸ hs) hI0 hc (Or.inr (Or.inr (Or.inl rfl)))])
  convert h using 2 <;> funext z <;> simp [Φ, Prod.map]

/-! ### Concatenation of spheres -/

/-- The concatenation of two maps of the plane along the first coordinate, compressed into the two
halves of the unit square: `v (2 s, t)` for `s ≤ 1/2` and `u (2 s - 1, t)` for `s > 1/2`. On maps
which equal `x` off `(1/3, 2/3)²` it represents the product in `π₂(M, x)`: on the square it is
Mathlib's `GenLoop.transAt 0`, and it is smooth because both pieces are constant near the seam.
The smooth concatenation `TauCeti.rectangleTrans` glues arbitrary smooth maps instead, at the cost
of a reparametrization which is not `GenLoop.transAt`. -/
private def squareConcat (v u : ℝ × ℝ → M) (z : ℝ × ℝ) : M :=
  if z.1 ≤ 1 / 2 then v (2 * z.1, z.2) else u (2 * z.1 - 1, z.2)

omit [TopologicalSpace M] in
private theorem squareConcat_of_le {v u : ℝ × ℝ → M} {s t : ℝ} (hs : s ≤ 1 / 2) :
    squareConcat v u (s, t) = v (2 * s, t) := by
  simp only [squareConcat, hs, ↓reduceIte]

omit [TopologicalSpace M] in
private theorem squareConcat_of_lt {v u : ℝ × ℝ → M} {s t : ℝ} (hs : 1 / 2 < s) :
    squareConcat v u (s, t) = u (2 * s - 1, t) := by
  simp only [squareConcat, not_le.2 hs, ↓reduceIte]

omit [TopologicalSpace M] in
/-- The concatenation sends the boundary of the unit square to `x`. -/
private theorem squareConcat_eq {v u : ℝ × ℝ → M}
    (hv : ∀ z : ℝ × ℝ, (z.1 ≤ 1 / 3 ∨ 2 / 3 ≤ z.1 ∨ z.2 ≤ 1 / 3 ∨ 2 / 3 ≤ z.2) → v z = x)
    (hu : ∀ z : ℝ × ℝ, (z.1 ≤ 1 / 3 ∨ 2 / 3 ≤ z.1 ∨ z.2 ≤ 1 / 3 ∨ 2 / 3 ≤ z.2) → u z = x) :
    ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, (s = 0 ∨ s = 1 ∨ t = 0 ∨ t = 1) →
      squareConcat v u (s, t) = x := by
  intro s _ t _ h
  simp only [squareConcat]
  split_ifs
  · exact hv _ (by rcases h with rfl | rfl | rfl | rfl <;> norm_num)
  · exact hu _ (by rcases h with rfl | rfl | rfl | rfl <;> norm_num)

/-- The concatenation of two `C²` maps equal to `x` off `(1/3, 2/3)²` is `C²`: near the seam
`s = 1/2` both pieces equal `x`. -/
private theorem contMDiff_squareConcat {v u : ℝ × ℝ → M} (hv : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 2 v)
    (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 2 u)
    (hvx : ∀ z : ℝ × ℝ, (z.1 ≤ 1 / 3 ∨ 2 / 3 ≤ z.1 ∨ z.2 ≤ 1 / 3 ∨ 2 / 3 ≤ z.2) → v z = x)
    (hux : ∀ z : ℝ × ℝ, (z.1 ≤ 1 / 3 ∨ 2 / 3 ≤ z.1 ∨ z.2 ≤ 1 / 3 ∨ 2 / 3 ≤ z.2) → u z = x) :
    ContMDiff 𝓘(ℝ, ℝ × ℝ) I 2 (squareConcat v u) := by
  have hL {c : ℝ} : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) 2 fun z : ℝ × ℝ ↦ (2 * z.1 - c, z.2) :=
    contMDiff_iff_contDiff.2 (by fun_prop)
  intro z
  rcases lt_trichotomy z.1 (1 / 2) with h | h | h
  · refine ((hv.comp (hL (c := 0))) z).congr_of_eventuallyEq ?_
    filter_upwards [(isOpen_lt continuous_fst continuous_const).mem_nhds h] with z' hz'
    simp only [squareConcat, Function.comp_apply, sub_zero, hz'.le, ↓reduceIte]
  · refine (contMDiffAt_const (c := x)).congr_of_eventuallyEq ?_
    have hV : IsOpen {z' : ℝ × ℝ | 1 / 3 < z'.1 ∧ z'.1 < 2 / 3} :=
      (isOpen_lt continuous_const continuous_fst).inter (isOpen_lt continuous_fst continuous_const)
    filter_upwards [hV.mem_nhds (show 1 / 3 < z.1 ∧ z.1 < 2 / 3 by constructor <;> linarith)]
      with z' hz'
    simp only [squareConcat]
    split_ifs
    · exact hvx _ (Or.inr (Or.inl (by linarith [hz'.1])))
    · exact hux _ (Or.inl (by linarith [hz'.2]))
  · refine ((hu.comp (hL (c := 1))) z).congr_of_eventuallyEq ?_
    filter_upwards [(isOpen_lt continuous_const continuous_fst).mem_nhds h] with z' hz'
    simp only [squareConcat, Function.comp_apply, not_le.2 hz', ↓reduceIte]

omit [TopologicalSpace M] in
/-- On the unit square the concatenation is Mathlib's concatenation `GenLoop.transAt 0` of
generalized loops along the first coordinate. -/
private theorem squareConcat_apply_eq_transAt {v u : ℝ × ℝ → M} (y : Fin 2 → unitInterval) :
    squareConcat v u ((y 0 : ℝ), (y 1 : ℝ)) =
      if (y 0 : ℝ) ≤ 1 / 2 then v ((projIcc (0 : ℝ) 1 zero_le_one (2 * (y 0 : ℝ)) : ℝ), (y 1 : ℝ))
      else u ((projIcc (0 : ℝ) 1 zero_le_one (2 * (y 0 : ℝ) - 1) : ℝ), (y 1 : ℝ)) := by
  simp only [squareConcat]
  split_ifs with h
  · rw [projIcc_of_mem _ ⟨by linarith [(y 0).2.1], by linarith⟩]
  · rw [projIcc_of_mem _ ⟨by linarith, by linarith [(y 0).2.2]⟩]

/-- The integral over the concatenation is the sum of the integrals over its two pieces. -/
private theorem rectangleIntegral_squareConcat [IsManifold I 1 M] {φ : RoughForm I M F 2}
    (hφ : IsSmoothForm I 0 φ) {v u : ℝ × ℝ → M} (hw : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 (squareConcat v u))
    (hvx : ∀ z : ℝ × ℝ, (z.1 ≤ 1 / 3 ∨ 2 / 3 ≤ z.1 ∨ z.2 ≤ 1 / 3 ∨ 2 / 3 ≤ z.2) → v z = x)
    (hux : ∀ z : ℝ × ℝ, (z.1 ≤ 1 / 3 ∨ 2 / 3 ≤ z.1 ∨ z.2 ≤ 1 / 3 ∨ 2 / 3 ≤ z.2) → u z = x) :
    rectangleIntegral φ (squareConcat v u) (0, 0) (1, 1) =
      rectangleIntegral φ v (0, 0) (1, 1) + rectangleIntegral φ u (0, 0) (1, 1) := by
  -- Split at `s = 1/2` and rescale each half affinely to the unit square.
  rw [← rectangleIntegral_add_adjacent_fst hφ hw (0, 0) (1, 1) (1 / 2),
    ← rectangleIntegral_comp_prodMap_affine hφ hw 0 (1 / 2) 0 1,
    ← rectangleIntegral_comp_prodMap_affine hφ hw (1 / 2) 1 0 1]
  congr 1
  · refine rectangleIntegral_congr fun z hz ↦ ?_
    obtain ⟨s, t⟩ := z
    rw [uIcc_of_le zero_le_one] at hz
    simp only [Function.comp_apply, Prod.map_apply, id_eq]
    rw [squareConcat_of_le (by linarith [hz.1.2])]
    congr 2
    ring
  · refine rectangleIntegral_congr fun z hz ↦ ?_
    obtain ⟨s, t⟩ := z
    rw [uIcc_of_le zero_le_one] at hz
    simp only [Function.comp_apply, Prod.map_apply, id_eq]
    rcases hz.1.1.eq_or_lt with hs | hs
    · -- At the seam both pieces equal `x`.
      subst hs
      rw [squareConcat_of_le (by norm_num), hvx _ (Or.inr (Or.inl (by norm_num))),
        hux _ (Or.inl (by norm_num))]
    · rw [squareConcat_of_lt (by linarith)]
      congr 2
      ring

variable [CompactSpace M] [T2Space M] [I.Boundaryless] [IsManifold I ∞ M] [FiniteDimensional ℝ E]

/-- The point `(squeeze s, squeeze t)` of the cube `I²`. -/
private def squeezeCube (z : ℝ × ℝ) : Fin 2 → unitInterval :=
  ![⟨squeeze z.1, squeeze_mem_Icc _⟩, ⟨squeeze z.2, squeeze_mem_Icc _⟩]

private theorem continuous_squeezeCube : Continuous squeezeCube := by
  have h := (contDiff_squeeze (n := 0)).continuous
  refine continuous_pi fun i ↦ ?_
  fin_cases i
  · exact (h.comp continuous_fst).subtype_mk _
  · exact (h.comp continuous_snd).subtype_mk _

/-- Off the open square `(1/3, 2/3)²`, the squeezed point lies on the boundary of the cube. -/
private theorem squeezeCube_mem_boundary {z : ℝ × ℝ}
    (hz : z.1 ≤ 1 / 3 ∨ 2 / 3 ≤ z.1 ∨ z.2 ≤ 1 / 3 ∨ 2 / 3 ≤ z.2) :
    squeezeCube z ∈ Cube.boundary (Fin 2) := by
  rcases hz with h | h | h | h
  · exact ⟨0, Or.inl (Subtype.ext (squeeze_of_le h))⟩
  · exact ⟨0, Or.inr (Subtype.ext (squeeze_of_ge h))⟩
  · exact ⟨1, Or.inl (Subtype.ext (squeeze_of_le h))⟩
  · exact ⟨1, Or.inr (Subtype.ext (squeeze_of_ge h))⟩

omit [CompactSpace M] [T2Space M] [I.Boundaryless] [IsManifold I ∞ M] [FiniteDimensional ℝ E] in
/-- Evaluating a sphere at the squeezed point is the squeezed sphere. -/
private theorem squareGenLoop_squeezeCube {u : ℝ × ℝ → M} (hu : Continuous u)
    (hx : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, (s = 0 ∨ s = 1 ∨ t = 0 ∨ t = 1) →
      u (s, t) = x) (z : ℝ × ℝ) :
    squareGenLoop u hu hx (squeezeCube z) = (u ∘ Prod.map squeeze squeeze) z :=
  (rfl)

variable (I) in
/-- **Smooth representatives.** On a compact manifold every element of `π₂(M, x)` is the class of
a smooth map of the plane sending the boundary of the unit square to `x`. -/
theorem exists_contMDiff_squareGenLoop (a : π_ 2 M x) :
    ∃ (u : ℝ × ℝ → M) (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I ∞ u)
      (hx : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, (s = 0 ∨ s = 1 ∨ t = 0 ∨ t = 1) →
        u (s, t) = x),
      (⟦squareGenLoop u hu.continuous hx⟧ : π_ 2 M x) = a := by
  obtain ⟨p, rfl⟩ := Quotient.exists_rep a
  -- The map `p ∘ squeezeCube` of the plane is continuous and equals `x` off `(1/3, 2/3)²`.
  let f : C(ℝ × ℝ, M) := ⟨fun z ↦ p (squeezeCube z), by
    have := continuous_squeezeCube; fun_prop⟩
  have hf {z : ℝ × ℝ} (hz : z.1 ≤ 1 / 3 ∨ 2 / 3 ≤ z.1 ∨ z.2 ≤ 1 / 3 ∨ 2 / 3 ≤ z.2) : f z = x :=
    p.2 _ (squeezeCube_mem_boundary hz)
  set S : Set (ℝ × ℝ) := {z | z.1 ≤ 1 / 4 ∨ 3 / 4 ≤ z.1 ∨ z.2 ≤ 1 / 4 ∨ 3 / 4 ≤ z.2}
  set U : Set (ℝ × ℝ) := {z | z.1 < 1 / 3 ∨ 2 / 3 < z.1 ∨ z.2 < 1 / 3 ∨ 2 / 3 < z.2}
  have hS : IsClosed S :=
    (isClosed_le continuous_fst continuous_const).union ((isClosed_le continuous_const
      continuous_fst).union ((isClosed_le continuous_snd continuous_const).union
        (isClosed_le continuous_const continuous_snd)))
  have hU : IsOpen U :=
    (isOpen_lt continuous_fst continuous_const).union ((isOpen_lt continuous_const
      continuous_fst).union ((isOpen_lt continuous_snd continuous_const).union
        (isOpen_lt continuous_const continuous_snd)))
  have hSU : S ⊆ U := by
    rintro z (h | h | h | h)
    · exact Or.inl (by linarith)
    · exact Or.inr (Or.inl (by linarith))
    · exact Or.inr (Or.inr (Or.inl (by linarith)))
    · exact Or.inr (Or.inr (Or.inr (by linarith)))
  have hfU : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞ f U := by
    refine (contMDiffOn_const (c := x)).congr fun z hz ↦ hf ?_
    rcases hz with h | h | h | h
    · exact Or.inl h.le
    · exact Or.inr (Or.inl h.le)
    · exact Or.inr (Or.inr (Or.inl h.le))
    · exact Or.inr (Or.inr (Or.inr h.le))
  obtain ⟨g, hg, ⟨R⟩⟩ := f.exists_contMDiff_homotopicRel (⊤ : ℕ∞) hS (hU.mem_nhdsSet.2 hSU) hfU
  -- The boundary of the square lies in `S`, where `g = f = x`.
  have hRS {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1)
      (h : s = 0 ∨ s = 1 ∨ t = 0 ∨ t = 1) : (s, t) ∈ S := by
    rcases h with rfl | rfl | rfl | rfl
    · exact Or.inl (by norm_num)
    · exact Or.inr (Or.inl (by norm_num))
    · exact Or.inr (Or.inr (Or.inl (by norm_num)))
    · exact Or.inr (Or.inr (Or.inr (by norm_num)))
  have hfx : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, (s = 0 ∨ s = 1 ∨ t = 0 ∨ t = 1) →
      f (s, t) = x := fun s hs t ht h ↦ hf (by
    rcases h with rfl | rfl | rfl | rfl <;> norm_num)
  have hgx : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, (s = 0 ∨ s = 1 ∨ t = 0 ∨ t = 1) →
      g (s, t) = x := fun s hs t ht h ↦ (R.fst_eq_snd (hRS hs ht h)).symm.trans (hfx s hs t ht h)
  refine ⟨g, hg, hgx, ?_⟩
  -- `g` is homotopic to `f` relative to `S`, and `f` is the reparametrization of `p` by the
  -- squeeze, which is homotopic to the identity of the cube relative to its boundary.
  have hgf : (⟦squareGenLoop g hg.continuous hgx⟧ : π_ 2 M x) =
      ⟦squareGenLoop f f.continuous hfx⟧ :=
    (Quotient.sound (squareGenLoop_homotopic (Φ := fun q ↦ R q) R.continuous
      (fun z ↦ R.apply_zero z) (fun z ↦ R.apply_one z) fun c s hs t ht h ↦
        (R.eq_fst c (hRS hs ht h)).trans (hfx s hs t ht h))).symm
  rw [hgf]
  refine Quotient.sound <| Nonempty.intro
    { toFun := fun q ↦ p fun i ↦ ⟨(q.2 i : ℝ) + (1 - (q.1 : ℝ)) * (squeeze (q.2 i) - q.2 i),
        add_mul_squeeze_sub_mem_Icc (q.2 i).2 ⟨sub_nonneg.2 q.1.2.2, by linarith [q.1.2.1]⟩⟩
      continuous_toFun := by
        have h := (contDiff_squeeze (n := 0)).continuous
        refine p.1.continuous.comp (continuous_pi fun i ↦ Continuous.subtype_mk ?_ _)
        fun_prop
      map_zero_left := fun y ↦ by
        simp only [Set.Icc.coe_zero, sub_zero, one_mul, add_sub_cancel]
        exact congrArg (fun y' ↦ p y') (funext fun i ↦ by fin_cases i <;> rfl)
      map_one_left := fun y ↦ by
        simp only [Set.Icc.coe_one, sub_self, zero_mul, add_zero]
        rfl
      prop' := fun c y ⟨i, hi⟩ ↦ by
        have hy : y ∈ Cube.boundary (Fin 2) := ⟨i, hi⟩
        refine (GenLoop.boundary p _ ⟨i, ?_⟩).trans
          (GenLoop.boundary (squareGenLoop f f.continuous hfx) y hy).symm
        rcases hi with h | h
        · have h' : ((y i : ℝ)) = 0 := congrArg Subtype.val h
          exact Or.inl (Subtype.ext ((add_mul_squeeze_sub_eq (Or.inl h')).trans h'))
        · have h' : ((y i : ℝ)) = 1 := congrArg Subtype.val h
          exact Or.inr (Subtype.ext ((add_mul_squeeze_sub_eq (Or.inr h')).trans h')) }

/-- The squeeze `ρ c = squeeze c` of the homotopy parameter, as a point of the unit interval. -/
private def squeezeInterval (c : ℝ) : unitInterval :=
  ⟨squeeze c, squeeze_mem_Icc c⟩

/-- **Smoothing a homotopy of spheres.** On a compact manifold, two `C²` maps of the plane sending
the boundary of the unit square to `x` which represent the same element of `π₂(M, x)` have squeezes
joined by a `C²` homotopy keeping the boundary of the square at `x`. A continuous homotopy between
the representatives, reparametrized by the squeeze in all three variables, is smooth near the ends
and near the boundary; Whitney approximation relative to these sets makes it smooth everywhere. -/
private theorem exists_contMDiff_homotopy_comp_squeeze {u₀ u₁ : ℝ × ℝ → M}
    (hu₀ : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 2 u₀) (hu₁ : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 2 u₁)
    {hx₀ : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, (s = 0 ∨ s = 1 ∨ t = 0 ∨ t = 1) →
      u₀ (s, t) = x}
    {hx₁ : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, (s = 0 ∨ s = 1 ∨ t = 0 ∨ t = 1) →
      u₁ (s, t) = x}
    (h : (⟦squareGenLoop u₀ hu₀.continuous hx₀⟧ : π_ 2 M x) =
      ⟦squareGenLoop u₁ hu₁.continuous hx₁⟧) :
    ∃ Φ : (ℝ × ℝ) × ℝ → M, ContMDiff 𝓘(ℝ, (ℝ × ℝ) × ℝ) I 2 Φ ∧
      (∀ z, Φ (z, 0) = (u₀ ∘ Prod.map squeeze squeeze) z) ∧
      (∀ z, Φ (z, 1) = (u₁ ∘ Prod.map squeeze squeeze) z) ∧
      ∀ s t c : ℝ, (s = 0 ∨ s = 1 ∨ t = 0 ∨ t = 1) → Φ ((s, t), c) = x := by
  obtain ⟨K⟩ := Quotient.exact h
  -- The homotopy `K`, reparametrized by the squeeze in all three variables, is a continuous map
  -- of `(ℝ × ℝ) × ℝ` which is smooth near the two ends and near the boundary of the square.
  let G : C((ℝ × ℝ) × ℝ, M) := ⟨fun w ↦ K (squeezeInterval w.2, squeezeCube w.1), by
    have h₁ := continuous_squeezeCube
    have h₂ : Continuous squeezeInterval :=
      ((contDiff_squeeze (n := 0)).continuous).subtype_mk _
    fun_prop⟩
  have hKx {c : unitInterval} {y : Fin 2 → unitInterval} (hy : y ∈ Cube.boundary (Fin 2)) :
      K (c, y) = x :=
    (K.eq_fst c hy).trans (GenLoop.boundary _ y hy)
  have hG₀ {w : (ℝ × ℝ) × ℝ} (hw : w.2 ≤ 1 / 3) :
      G w = (u₀ ∘ Prod.map squeeze squeeze) w.1 := by
    have hc : squeezeInterval w.2 = 0 := Subtype.ext (squeeze_of_le hw)
    simp only [G, ContinuousMap.coe_mk, hc, ContinuousMap.HomotopyWith.apply_zero]
    rfl
  have hG₁ {w : (ℝ × ℝ) × ℝ} (hw : 2 / 3 ≤ w.2) :
      G w = (u₁ ∘ Prod.map squeeze squeeze) w.1 := by
    have hc : squeezeInterval w.2 = 1 := Subtype.ext (squeeze_of_ge hw)
    simp only [G, ContinuousMap.coe_mk, hc, ContinuousMap.HomotopyWith.apply_one]
    rfl
  have hGx {w : (ℝ × ℝ) × ℝ}
      (hw : w.1.1 ≤ 1 / 3 ∨ 2 / 3 ≤ w.1.1 ∨ w.1.2 ≤ 1 / 3 ∨ 2 / 3 ≤ w.1.2) : G w = x :=
    hKx (squeezeCube_mem_boundary hw)
  set S : Set ((ℝ × ℝ) × ℝ) := {w | w.2 ≤ 1 / 4 ∨ 3 / 4 ≤ w.2 ∨
    (w.1.1 ≤ 1 / 4 ∨ 3 / 4 ≤ w.1.1 ∨ w.1.2 ≤ 1 / 4 ∨ 3 / 4 ≤ w.1.2)}
  set U : Set ((ℝ × ℝ) × ℝ) := {w | w.2 < 1 / 3 ∨ 2 / 3 < w.2 ∨
    (w.1.1 < 1 / 3 ∨ 2 / 3 < w.1.1 ∨ w.1.2 < 1 / 3 ∨ 2 / 3 < w.1.2)}
  have h₁ : Continuous fun w : (ℝ × ℝ) × ℝ ↦ w.1.1 := continuous_fst.fst
  have h₂ : Continuous fun w : (ℝ × ℝ) × ℝ ↦ w.1.2 := continuous_fst.snd
  have hS : IsClosed S :=
    (isClosed_le continuous_snd continuous_const).union ((isClosed_le continuous_const
      continuous_snd).union ((isClosed_le h₁ continuous_const).union ((isClosed_le continuous_const
        h₁).union ((isClosed_le h₂ continuous_const).union (isClosed_le continuous_const h₂)))))
  have hV : IsOpen {w : (ℝ × ℝ) × ℝ | w.1.1 < 1 / 3 ∨ 2 / 3 < w.1.1 ∨ w.1.2 < 1 / 3 ∨
      2 / 3 < w.1.2} :=
    (isOpen_lt h₁ continuous_const).union ((isOpen_lt continuous_const h₁).union
      ((isOpen_lt h₂ continuous_const).union (isOpen_lt continuous_const h₂)))
  have hU : IsOpen U :=
    (isOpen_lt continuous_snd continuous_const).union ((isOpen_lt continuous_const
      continuous_snd).union hV)
  have hSU : S ⊆ U := by
    rintro w (h | h | h | h | h | h)
    · exact Or.inl (by linarith)
    · exact Or.inr (Or.inl (by linarith))
    · exact Or.inr (Or.inr (Or.inl (by linarith)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (by linarith))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by linarith)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by linarith)))))
  have hsq : ContMDiff 𝓘(ℝ, (ℝ × ℝ) × ℝ) 𝓘(ℝ, ℝ × ℝ) 2
      (fun w : (ℝ × ℝ) × ℝ ↦ Prod.map squeeze squeeze w.1) := by
    have h := contDiff_squeeze (n := 2)
    exact contMDiff_iff_contDiff.2 (by fun_prop)
  -- Near every point of `U`, `G` agrees with one of three smooth maps.
  have hGU : ContMDiffOn 𝓘(ℝ, (ℝ × ℝ) × ℝ) I 2 G U := by
    intro w hw
    refine ContMDiffAt.contMDiffWithinAt ?_
    rcases hw with h | h | h
    · refine (hu₀.comp hsq w).congr_of_eventuallyEq ?_
      filter_upwards [(isOpen_lt continuous_snd continuous_const).mem_nhds h] with w' hw'
      exact hG₀ (le_of_lt hw')
    · refine (hu₁.comp hsq w).congr_of_eventuallyEq ?_
      filter_upwards [(isOpen_lt continuous_const continuous_snd).mem_nhds h] with w' hw'
      exact hG₁ (le_of_lt hw')
    · refine (contMDiffAt_const (c := x)).congr_of_eventuallyEq ?_
      filter_upwards [hV.mem_nhds h] with w' hw'
      refine hGx ?_
      rcases hw' with h' | h' | h' | h'
      · exact Or.inl h'.le
      · exact Or.inr (Or.inl h'.le)
      · exact Or.inr (Or.inr (Or.inl h'.le))
      · exact Or.inr (Or.inr (Or.inr h'.le))
  obtain ⟨Φ, hΦ, ⟨R⟩⟩ := G.exists_contMDiff_homotopicRel (2 : ℕ∞) hS (hU.mem_nhdsSet.2 hSU) hGU
  have hΦG {w : (ℝ × ℝ) × ℝ} (hw : w ∈ S) : Φ w = G w := (R.fst_eq_snd hw).symm
  refine ⟨Φ, hΦ, fun z ↦ (hΦG (Or.inl (by norm_num))).trans (hG₀ (by norm_num)),
    fun z ↦ (hΦG (Or.inr (Or.inl (by norm_num)))).trans (hG₁ (by norm_num)), fun s t c h ↦ ?_⟩
  -- The smooth homotopy `Φ` keeps every edge of the square at `x`.
  have hw : ((s, t), c) ∈ S ∧ (s ≤ 1 / 3 ∨ 2 / 3 ≤ s ∨ t ≤ 1 / 3 ∨ 2 / 3 ≤ t) := by
    rcases h with rfl | rfl | rfl | rfl <;> norm_num [S]
  exact (hΦG hw.1).trans (hGx hw.2)
/-- **Homotopy invariance of the integral over a sphere.** On a compact manifold, two `C²` maps of
the plane sending the boundary of the unit square to `x` which represent the same element of
`π₂(M, x)` have the same integral of a closed `C¹` two-form over the square. -/
theorem rectangleIntegral_eq_of_squareGenLoop_eq [CompleteSpace F] {φ : RoughForm I M F 2}
    (hφ : IsSmoothForm I 1 φ) (hdφ : mextDeriv φ = 0) {u₀ u₁ : ℝ × ℝ → M}
    (hu₀ : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 2 u₀) (hu₁ : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 2 u₁)
    {hx₀ : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, (s = 0 ∨ s = 1 ∨ t = 0 ∨ t = 1) →
      u₀ (s, t) = x}
    {hx₁ : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, (s = 0 ∨ s = 1 ∨ t = 0 ∨ t = 1) →
      u₁ (s, t) = x}
    (h : (⟦squareGenLoop u₀ hu₀.continuous hx₀⟧ : π_ 2 M x) =
      ⟦squareGenLoop u₁ hu₁.continuous hx₁⟧) :
    rectangleIntegral φ u₀ (0, 0) (1, 1) = rectangleIntegral φ u₁ (0, 0) (1, 1) := by
  obtain ⟨Φ, hΦ, hΦ₀, hΦ₁, hedge⟩ := exists_contMDiff_homotopy_comp_squeeze hu₀ hu₁ h
  have hint := rectangleIntegral_eq_of_homotopy hφ hdφ hΦ (a := (0, 0)) (b := (1, 1))
    (Or.inr fun t _ c _ ↦ by rw [hedge _ _ _ (Or.inl rfl), hedge _ _ _ (Or.inl rfl)])
    (Or.inr fun t _ c _ ↦ by
      rw [hedge _ _ _ (Or.inr (Or.inl rfl)), hedge _ _ _ (Or.inr (Or.inl rfl))])
    (fun s _ c _ ↦ by rw [hedge _ _ _ (Or.inr (Or.inr (Or.inr rfl))),
      hedge _ _ _ (Or.inr (Or.inr (Or.inl rfl)))])
  rw [funext hΦ₀, funext hΦ₁, rectangleIntegral_comp_squeeze hφ hdφ hu₀ hx₀,
    rectangleIntegral_comp_squeeze hφ hdφ hu₁ hx₁] at hint
  exact hint.symm

/-- **The period of a sphere is its integral.** For a closed `C¹` two-form on a compact manifold and
a `C²` map of the plane sending the boundary of the unit square to `x`, the period of its class in
`π₂(M, x)` is the integral of the form over the square. -/
theorem spherePeriod_mk [CompleteSpace F] {φ : RoughForm I M F 2} (hφ : IsSmoothForm I 1 φ)
    (hdφ : mextDeriv φ = 0) {u : ℝ × ℝ → M} (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 2 u)
    (hx : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, (s = 0 ∨ s = 1 ∨ t = 0 ∨ t = 1) →
      u (s, t) = x) :
    spherePeriod φ x ⟦squareGenLoop u hu.continuous hx⟧ = rectangleIntegral φ u (0, 0) (1, 1) := by
  have h := exists_contMDiff_squareGenLoop I (⟦squareGenLoop u hu.continuous hx⟧ : π_ 2 M x)
  unfold spherePeriod
  split_ifs with h'
  · obtain ⟨hv, hvx, hva⟩ := h'.choose_spec
    exact rectangleIntegral_eq_of_squareGenLoop_eq hφ hdφ (hv.of_le (by simp)) hu hva
  · exact absurd h h'

/-- **Additivity of the period.** For a closed `C¹` two-form on a compact manifold, the period of a
product in `π₂(M, x)` is the sum of the periods. -/
theorem spherePeriod_mul [CompleteSpace F] {φ : RoughForm I M F 2} (hφ : IsSmoothForm I 1 φ)
    (hdφ : mextDeriv φ = 0) (a b : π_ 2 M x) :
    spherePeriod φ x (a * b) = spherePeriod φ x a + spherePeriod φ x b := by
  obtain ⟨u, hu, hux, rfl⟩ := exists_contMDiff_squareGenLoop I a
  obtain ⟨v, hv, hvx, rfl⟩ := exists_contMDiff_squareGenLoop I b
  have hsq : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) 2 (Prod.map squeeze squeeze) :=
    contMDiff_iff_contDiff.2 (contDiff_squeeze.prodMap contDiff_squeeze)
  -- Replace both representatives by their squeezes, which equal `x` off `(1/3, 2/3)²`.
  have hu' : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 2 (u ∘ Prod.map squeeze squeeze) :=
    (hu.of_le (by simp)).comp hsq
  have hv' : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 2 (v ∘ Prod.map squeeze squeeze) :=
    (hv.of_le (by simp)).comp hsq
  have hu'x (z : ℝ × ℝ) (hz : z.1 ≤ 1 / 3 ∨ 2 / 3 ≤ z.1 ∨ z.2 ≤ 1 / 3 ∨ 2 / 3 ≤ z.2) :
      (u ∘ Prod.map squeeze squeeze) z = x :=
    comp_squeeze_eq hux hz
  have hv'x (z : ℝ × ℝ) (hz : z.1 ≤ 1 / 3 ∨ 2 / 3 ≤ z.1 ∨ z.2 ≤ 1 / 3 ∨ 2 / 3 ≤ z.2) :
      (v ∘ Prod.map squeeze squeeze) z = x :=
    comp_squeeze_eq hvx hz
  have hw := contMDiff_squareConcat hv' hu' hv'x hu'x
  rw [← squareGenLoop_comp_squeeze hu.continuous hux,
    ← squareGenLoop_comp_squeeze hv.continuous hvx, spherePeriod_mk hφ hdφ hu',
    spherePeriod_mk hφ hdφ hv']
  -- The product is the concatenation of the second factor followed by the first.
  have hmul := HomotopyGroup.mul_spec (X := M) (x := x) (i := (0 : Fin 2))
    (p := squareGenLoop (u ∘ Prod.map squeeze squeeze) hu'.continuous
      fun s _ t _ h ↦ hu'x _ (by rcases h with rfl | rfl | rfl | rfl <;> norm_num))
    (q := squareGenLoop (v ∘ Prod.map squeeze squeeze) hv'.continuous
      fun s _ t _ h ↦ hv'x _ (by rcases h with rfl | rfl | rfl | rfl <;> norm_num))
  -- `HomotopyGroup.mul_spec` is stated for the multiplication written as a lambda.
  beta_reduce at hmul
  have hgen : GenLoop.transAt 0
      (squareGenLoop (v ∘ Prod.map squeeze squeeze) hv'.continuous
        fun s _ t _ h ↦ hv'x _ (by rcases h with rfl | rfl | rfl | rfl <;> norm_num))
      (squareGenLoop (u ∘ Prod.map squeeze squeeze) hu'.continuous
        fun s _ t _ h ↦ hu'x _ (by rcases h with rfl | rfl | rfl | rfl <;> norm_num)) =
      squareGenLoop _ hw.continuous (squareConcat_eq hv'x hu'x) := by
    ext y
    simp only [GenLoop.transAt, GenLoop.coe_copy, squareGenLoop_apply,
      squareConcat_apply_eq_transAt, Function.update_self,
      Function.update_of_ne (show (1 : Fin 2) ≠ 0 by decide)]
  rw [hmul, hgen, spherePeriod_mk hφ hdφ hw,
    rectangleIntegral_squareConcat (hφ.of_le (by simp)) (hw.of_le (by simp)) hv'x hu'x, add_comm]

/-- The period of the identity of `π₂(M, x)`, the class of the constant sphere, vanishes. -/
theorem spherePeriod_one [CompleteSpace F] {φ : RoughForm I M F 2} (hφ : IsSmoothForm I 1 φ)
    (hdφ : mextDeriv φ = 0) : spherePeriod φ x 1 = 0 := by
  have h : (1 : π_ 2 M x) = ⟦squareGenLoop (fun _ ↦ x) continuous_const fun _ _ _ _ _ ↦ rfl⟧ :=
    HomotopyGroup.one_def.trans (congrArg _ (GenLoop.ext _ _ fun _ ↦ rfl))
  rw [h, spherePeriod_mk hφ hdφ contMDiff_const, rectangleIntegral_const]

variable (x) in
/-- The **period homomorphism** of a closed `C¹` two-form `φ` on a compact manifold: the integral
of `φ` over spheres, as a homomorphism from `π₂(M, x)` to the coefficients. For a symplectic form
it is the symplectic area of spheres. -/
def spherePeriodHom [CompleteSpace F] {φ : RoughForm I M F 2} (hφ : IsSmoothForm I 1 φ)
    (hdφ : mextDeriv φ = 0) : Additive (π_ 2 M x) →+ F where
  toFun a := spherePeriod φ x a.toMul
  map_zero' := spherePeriod_one hφ hdφ
  map_add' a b := spherePeriod_mul hφ hdφ a.toMul b.toMul

@[simp]
theorem spherePeriodHom_apply [CompleteSpace F] {φ : RoughForm I M F 2} (hφ : IsSmoothForm I 1 φ)
    (hdφ : mextDeriv φ = 0) (a : Additive (π_ 2 M x)) :
    spherePeriodHom x hφ hdφ a = spherePeriod φ x a.toMul :=
  (rfl)

end TauCeti

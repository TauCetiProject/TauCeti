/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Cylinder
public import TauCeti.Topology.Homotopy.GenLoop.Square
import TauCeti.Analysis.SpecialFunctions.SmoothTransition
import TauCeti.Geometry.Manifold.SmoothApprox
import TauCeti.Topology.Homotopy.Cube.Basic
import TauCeti.Topology.Homotopy.HomotopyGroup.TransAt

/-!
# Periods of closed two-forms on the second homotopy group

Let `φ` be a closed `C¹` two-form on a closed manifold `M` (compact, Hausdorff, boundaryless and
finite-dimensional), for instance the symplectic form of a closed symplectic manifold. Its integral
over a sphere only depends on the homotopy class of the sphere, and it is additive under the group
law of `π₂(M, x)`. This file constructs the resulting **period homomorphism**
`TauCeti.spherePeriodHom` from `π₂(M, x)`, written additively, to the coefficients. For a
symplectic form it is the symplectic area of spheres, the homomorphism `ω` on spherical classes
through which capped Hamiltonian Floer theory defines its period group and the recapping law of
the action.

An element of `π₂(M, x)` is a homotopy class, relative to the boundary, of maps of the square
`[0, 1]²` sending the boundary to `x` (Mathlib's `GenLoop`). A map `u : ℝ × ℝ → M` of the
plane which sends the boundary of the unit square to `x` (`TauCeti.MapsSquareBoundaryTo`)
restricts to such a generalized loop (`TauCeti.squareGenLoop`), whose class lies in `π₂(M, x)`.
When `u` is `C²`, the integral of `φ` over the sphere is the integral
`TauCeti.rectangleIntegral φ u (0, 0) (1, 1)` of the pullback of `φ` over the square.

* Every class has a smooth representative: a continuous map of the square constant near its
  boundary is homotopic, relative to that neighbourhood, to a smooth map by the Whitney
  approximation theorem (`ContinuousMap.exists_contMDiff_homotopicRel_compl`), which needs `M`
  to be a compact, Hausdorff, boundaryless, finite-dimensional manifold.
* Two homotopic `C²` representatives have the same integral
  (`TauCeti.rectangleIntegral_eq_of_homotopic`). A continuous homotopy between them is made
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

* `TauCeti.spherePeriod φ x`: the integral of a two-form over the classes of `π₂(M, x)`.
* `TauCeti.spherePeriodHom`: for a closed `C¹` form on a closed manifold, the period as a
  homomorphism from `π₂(M, x)` to the coefficients.

## Main results

* `TauCeti.exists_contMDiff_squareGenLoop`: on a closed manifold every class of `π₂(M, x)` has a
  smooth representative.
* `TauCeti.rectangleIntegral_eq_of_homotopic`: homotopic `C²` spheres have the same integral.
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

/-! ### The period of a two-form on `π₂` -/

/-- The **period** of a two-form `φ` on `π₂(M, x)`: the integral of `φ` over the unit square along a
smooth map of the plane which sends the boundary of the square to `x` and represents the given
class. It does not depend on the representative when `φ` is closed and `C¹` and `M` is a closed
manifold: compact, Hausdorff, boundaryless and finite-dimensional (`TauCeti.spherePeriod_mk`). It
is `0` on classes without a smooth representative. -/
def spherePeriod (φ : RoughForm I M F 2) (x : M) (a : π_ 2 M x) : F := by
  classical
  exact if h : ∃ (u : ℝ × ℝ → M) (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I ∞ u)
      (hx : MapsSquareBoundaryTo u x), (⟦squareGenLoop u hu.continuous hx⟧ : π_ 2 M x) = a then
    rectangleIntegral φ h.choose (0, 0) (1, 1)
  else 0

/-- The period of a form vanishing on spheres vanishes. -/
@[simp]
theorem VanishesOnSpheres.spherePeriod_eq_zero {φ : RoughForm I M F 2}
    (hφ : VanishesOnSpheres φ) (a : π_ 2 M x) : spherePeriod φ x a = 0 := by
  rw [spherePeriod]
  split_ifs with h
  · obtain ⟨hu, hx, -⟩ := h.choose_spec
    obtain ⟨h₀, h₁, h₂⟩ := hx.edges
    exact (vanishesOnSpheres_iff φ).1 hφ _ hu h₀ h₁ h₂
  · rfl

/-- The periods of exact two-forms vanish. -/
@[simp]
theorem spherePeriod_mextDeriv [IsManifold I 2 M] {α : RoughForm I M F 1}
    (hα : IsSmoothForm I 1 α) (a : π_ 2 M x) : spherePeriod (mextDeriv α) x a = 0 :=
  (vanishesOnSpheres_mextDeriv hα).spherePeriod_eq_zero a

/-- The period is linear in the form: scalar multiples. -/
@[simp]
theorem spherePeriod_smul (c : ℝ) (φ : RoughForm I M F 2) (a : π_ 2 M x) :
    spherePeriod (c • φ) x a = c • spherePeriod φ x a := by
  simp only [spherePeriod]
  split_ifs
  · exact rectangleIntegral_smul c φ _ _ _
  · exact (smul_zero c).symm

/-- The period of the zero form vanishes. -/
@[simp]
theorem spherePeriod_zero (a : π_ 2 M x) : spherePeriod (0 : RoughForm I M F 2) x a = 0 := by
  simpa using spherePeriod_smul 0 (0 : RoughForm I M F 2) a

/-- The period is linear in the form: sums of continuous forms. -/
@[simp]
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
  Real.smoothTransition (3 * s + -1)

private theorem squeeze_mem_Icc (s : ℝ) : squeeze s ∈ Icc (0 : ℝ) 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

private theorem squeeze_of_le {s : ℝ} (hs : s ≤ 1 / 3) : squeeze s = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

private theorem squeeze_of_ge {s : ℝ} (hs : 2 / 3 ≤ s) : squeeze s = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

private theorem contDiff_squeeze {n : ℕ∞} : ContDiff ℝ n squeeze :=
  Real.smoothTransition.contDiff_comp_mul_add 3 (-1)

private theorem continuous_squeeze : Continuous squeeze :=
  (contDiff_squeeze (n := 0)).continuous

/-- The segment from `s` to `squeeze s` stays in `[0, 1]` for `s ∈ [0, 1]`. -/
private theorem add_mul_squeeze_sub_mem_Icc {s c : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (hc : c ∈ Icc (0 : ℝ) 1) : s + c * (squeeze s - s) ∈ Icc (0 : ℝ) 1 := by
  simpa only [smul_eq_mul] using (convex_Icc (0 : ℝ) 1).add_smul_sub_mem hs (squeeze_mem_Icc s) hc

/-- The segment from `s` to `squeeze s` fixes the endpoints `0` and `1` of `[0, 1]`. -/
private theorem add_mul_squeeze_sub_eq {s c : ℝ} (hs : s = 0 ∨ s = 1) :
    s + c * (squeeze s - s) = s := by
  rcases hs with rfl | rfl
  · simp [squeeze_of_le (by norm_num : (0 : ℝ) ≤ 1 / 3)]
  · simp [squeeze_of_ge (by norm_num : (2 / 3 : ℝ) ≤ 1)]

omit [TopologicalSpace M] in
/-- Along the segment from the identity to `squeeze` in both coordinates, a map sending the
boundary of the unit square to `x` keeps sending it to `x` at every time `c ∈ [0, 1]`. -/
private theorem MapsSquareBoundaryTo.squeezeHomotopy {u : ℝ × ℝ → M}
    (hx : MapsSquareBoundaryTo u x) {c : ℝ} (hc : c ∈ Icc (0 : ℝ) 1) :
    MapsSquareBoundaryTo
      (fun z : ℝ × ℝ ↦ u (z.1 + c * (squeeze z.1 - z.1), z.2 + c * (squeeze z.2 - z.2))) x := by
  refine mapsSquareBoundaryTo_iff.2 fun s hs t ht h ↦
    hx.apply_eq (add_mul_squeeze_sub_mem_Icc hs hc) (add_mul_squeeze_sub_mem_Icc ht hc) ?_
  rcases h with h | h | h | h
  · exact Or.inl ((add_mul_squeeze_sub_eq (Or.inl h)).trans h)
  · exact Or.inr (Or.inl ((add_mul_squeeze_sub_eq (Or.inr h)).trans h))
  · exact Or.inr (Or.inr (Or.inl ((add_mul_squeeze_sub_eq (Or.inl h)).trans h)))
  · exact Or.inr (Or.inr (Or.inr ((add_mul_squeeze_sub_eq (Or.inr h)).trans h)))

/-- The open middle square `(1/3, 2/3)²` of the plane, off which maps precomposed with the squeeze
in both coordinates are constant. -/
private def middleSquare : Set (ℝ × ℝ) :=
  Ioo (1 / 3) (2 / 3) ×ˢ Ioo (1 / 3) (2 / 3)

private theorem notMem_middleSquare_iff {z : ℝ × ℝ} :
    z ∉ middleSquare ↔ z.1 ≤ 1 / 3 ∨ 2 / 3 ≤ z.1 ∨ z.2 ≤ 1 / 3 ∨ 2 / 3 ≤ z.2 := by
  simp only [middleSquare, mem_prod, mem_Ioo, not_and_or, not_lt, or_assoc]

omit [TopologicalSpace M] in
/-- A map equal to `x` off the middle square sends the boundary of the unit square to `x`. -/
private theorem MapsSquareBoundaryTo.of_notMem_middleSquare {u : ℝ × ℝ → M}
    (hu : ∀ z ∉ middleSquare, u z = x) : MapsSquareBoundaryTo u x :=
  .of_forall_notMem (by norm_num) (by norm_num) hu

/-- The closed square `[1/3, 2/3]²` lies in the open square `(1/4, 3/4)²`: the closed set off the
latter, on which Whitney approximation keeps a squeezed map fixed, lies in the open set off the
former, where the squeezed map is constant. -/
private theorem Icc_subset_Ioo_quarters : Icc (1 / 3 : ℝ) (2 / 3) ⊆ Ioo (1 / 4) (3 / 4) :=
  Icc_subset_Ioo (by norm_num) (by norm_num)

omit [TopologicalSpace M] in
/-- A map sending the boundary of the unit square to `x`, precomposed with the squeeze in both
coordinates, equals `x` off the middle square. -/
private theorem comp_squeeze_eq {u : ℝ × ℝ → M} (hx : MapsSquareBoundaryTo u x) {z : ℝ × ℝ}
    (hz : z ∉ middleSquare) : (u ∘ Prod.map squeeze squeeze) z = x := by
  refine hx.apply_eq (squeeze_mem_Icc _) (squeeze_mem_Icc _) ?_
  rcases notMem_middleSquare_iff.1 hz with h | h | h | h
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
    (hx : MapsSquareBoundaryTo u x) :
    (⟦squareGenLoop (u ∘ Prod.map squeeze squeeze)
        (hu.comp (continuous_squeeze.prodMap continuous_squeeze))
        (.of_notMem_middleSquare fun _ ↦ comp_squeeze_eq hx)⟧ : π_ 2 M x) =
      ⟦squareGenLoop u hu hx⟧ := by
  refine Quotient.sound (squareGenLoop_homotopic (Φ := fun p ↦ u
    (p.2.1 + (1 - (p.1 : ℝ)) * (squeeze p.2.1 - p.2.1),
      p.2.2 + (1 - (p.1 : ℝ)) * (squeeze p.2.2 - p.2.2))) ?_ ?_ ?_ ?_)
  · have h := continuous_squeeze
    fun_prop
  · intro z
    simp [Prod.map]
  · intro z
    simp
  · exact fun c ↦ hx.squeezeHomotopy (c := 1 - c) ⟨sub_nonneg.2 c.2.2, by linarith [c.2.1]⟩

/-- The integral of a closed `C¹` two-form over the unit square does not change along a `C²`
homotopy which keeps the boundary of the square at `x`: this is
`TauCeti.rectangleIntegral_eq_of_homotopy` on the unit square, with all its edges fixed. -/
private theorem rectangleIntegral_eq_of_homotopy_unitSquare [IsManifold I 2 M]
    {φ : RoughForm I M F 2} (hφ : IsSmoothForm I 1 φ) (hdφ : mextDeriv φ = 0)
    {Φ : (ℝ × ℝ) × ℝ → M} (hΦ : ContMDiff 𝓘(ℝ, (ℝ × ℝ) × ℝ) I 2 Φ)
    (hx : ∀ c ∈ Icc (0 : ℝ) 1, MapsSquareBoundaryTo (fun z ↦ Φ (z, c)) x) :
    rectangleIntegral φ (fun z ↦ Φ (z, 1)) (0, 0) (1, 1) =
      rectangleIntegral φ (fun z ↦ Φ (z, 0)) (0, 0) (1, 1) := by
  have h01 : uIcc (0 : ℝ) 1 = Icc 0 1 := uIcc_of_le zero_le_one
  have hI1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := right_mem_Icc.2 zero_le_one
  exact rectangleIntegral_eq_of_homotopy hφ hdφ hΦ
    (Or.inr fun t ht c hc ↦ (hx c hc).edges.1 t (h01 ▸ ht))
    (Or.inr fun t ht c hc ↦
      ((hx c hc).edges.2.1 t (h01 ▸ ht)).trans ((hx c hc).edges.2.1 1 hI1).symm)
    fun s hs c hc ↦ (hx c hc).edges.2.2 s (h01 ▸ hs)

/-- Squeezing a `C²` sphere does not change the integral of a closed `C¹` form over it: the segment
from the identity to `squeeze` is a smooth homotopy through spheres. -/
private theorem rectangleIntegral_comp_squeeze [IsManifold I 2 M]
    {φ : RoughForm I M F 2} (hφ : IsSmoothForm I 1 φ) (hdφ : mextDeriv φ = 0) {u : ℝ × ℝ → M}
    (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 2 u) (hx : MapsSquareBoundaryTo u x) :
    rectangleIntegral φ (u ∘ Prod.map squeeze squeeze) (0, 0) (1, 1) =
      rectangleIntegral φ u (0, 0) (1, 1) := by
  have h := rectangleIntegral_eq_of_homotopy_unitSquare hφ hdφ
    (hu.comp (contMDiff_iff_contDiff.2 contDiff_squeezeHomotopy))
    fun _ hc ↦ hx.squeezeHomotopy hc
  convert h using 2 <;> funext z <;> simp [Prod.map]

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
private theorem mapsSquareBoundaryTo_squareConcat {v u : ℝ × ℝ → M}
    (hv : ∀ z ∉ middleSquare, v z = x) (hu : ∀ z ∉ middleSquare, u z = x) :
    MapsSquareBoundaryTo (squareConcat v u) x := by
  refine mapsSquareBoundaryTo_iff.2 fun s _ t _ h ↦ ?_
  simp only [squareConcat]
  split_ifs
  · exact hv _ (notMem_middleSquare_iff.2 (by rcases h with rfl | rfl | rfl | rfl <;> norm_num))
  · exact hu _ (notMem_middleSquare_iff.2 (by rcases h with rfl | rfl | rfl | rfl <;> norm_num))

/-- The concatenation of two `C²` maps equal to `x` off `(1/3, 2/3)²` is `C²`: near the seam
`s = 1/2` both pieces equal `x`. -/
private theorem contMDiff_squareConcat {v u : ℝ × ℝ → M} (hv : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 2 v)
    (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 2 u) (hvx : ∀ z ∉ middleSquare, v z = x)
    (hux : ∀ z ∉ middleSquare, u z = x) :
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
    · exact hvx _ (notMem_middleSquare_iff.2 (Or.inr (Or.inl (by linarith [hz'.1]))))
    · exact hux _ (notMem_middleSquare_iff.2 (Or.inl (by linarith [hz'.2])))
  · refine ((hu.comp (hL (c := 1))) z).congr_of_eventuallyEq ?_
    filter_upwards [(isOpen_lt continuous_const continuous_fst).mem_nhds h] with z' hz'
    simp only [squareConcat, Function.comp_apply, not_le.2 hz', ↓reduceIte]

/-- The integral over the concatenation is the sum of the integrals over its two pieces. -/
private theorem rectangleIntegral_squareConcat [IsManifold I 1 M] {φ : RoughForm I M F 2}
    (hφ : IsSmoothForm I 0 φ) {v u : ℝ × ℝ → M} (hw : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 (squareConcat v u))
    (hvx : ∀ z ∉ middleSquare, v z = x) (hux : ∀ z ∉ middleSquare, u z = x) :
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
      rw [squareConcat_of_le (by norm_num),
        hvx _ (notMem_middleSquare_iff.2 (Or.inr (Or.inl (by norm_num)))),
        hux _ (notMem_middleSquare_iff.2 (Or.inl (by norm_num)))]
    · rw [squareConcat_of_lt (by linarith)]
      congr 2
      ring

variable [CompactSpace M] [T2Space M] [I.Boundaryless] [IsManifold I ∞ M] [FiniteDimensional ℝ E]

/-- The point `(squeeze s, squeeze t)` of the cube `I²`. -/
private def squeezeCube (z : ℝ × ℝ) : Fin 2 → unitInterval :=
  ![⟨squeeze z.1, squeeze_mem_Icc _⟩, ⟨squeeze z.2, squeeze_mem_Icc _⟩]

private theorem continuous_squeezeCube : Continuous squeezeCube := by
  refine continuous_pi fun i ↦ ?_
  fin_cases i
  · exact (continuous_squeeze.comp continuous_fst).subtype_mk _
  · exact (continuous_squeeze.comp continuous_snd).subtype_mk _

/-- Off the middle square, the squeezed point lies on the boundary of the cube. -/
private theorem squeezeCube_mem_boundary {z : ℝ × ℝ} (hz : z ∉ middleSquare) :
    squeezeCube z ∈ Cube.boundary (Fin 2) := by
  rcases notMem_middleSquare_iff.1 hz with h | h | h | h
  · exact ⟨0, Or.inl (Subtype.ext (squeeze_of_le h))⟩
  · exact ⟨0, Or.inr (Subtype.ext (squeeze_of_ge h))⟩
  · exact ⟨1, Or.inl (Subtype.ext (squeeze_of_le h))⟩
  · exact ⟨1, Or.inr (Subtype.ext (squeeze_of_ge h))⟩

variable (I) in
/-- **Smooth representatives.** On a closed manifold (compact, Hausdorff, boundaryless and
finite-dimensional) every element of `π₂(M, x)` is the class of a smooth map of the plane sending
the boundary of the unit square to `x`. -/
theorem exists_contMDiff_squareGenLoop (a : π_ 2 M x) :
    ∃ (u : ℝ × ℝ → M) (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I ∞ u) (hx : MapsSquareBoundaryTo u x),
      (⟦squareGenLoop u hu.continuous hx⟧ : π_ 2 M x) = a := by
  obtain ⟨p, rfl⟩ := Quotient.exists_rep a
  obtain ⟨P, hPc, hPx, rfl⟩ := exists_squareGenLoop_eq p
  -- The squeeze `f` of `P` is continuous and equals `x` off the middle square.
  let f : C(ℝ × ℝ, M) := ⟨P ∘ Prod.map squeeze squeeze,
    hPc.comp (continuous_squeeze.prodMap continuous_squeeze)⟩
  have hf : ∀ z ∉ middleSquare, f z = x := fun _ ↦ comp_squeeze_eq hPx
  obtain ⟨g, hg, hgf, ⟨R⟩⟩ := f.exists_contMDiff_homotopicRel_compl (I := 𝓘(ℝ, ℝ × ℝ))
    (J := I) ⊤ (isClosed_Icc.prod isClosed_Icc) (isOpen_Ioo.prod isOpen_Ioo)
    (prod_mono Icc_subset_Ioo_quarters Icc_subset_Ioo_quarters)
    ((contMDiffOn_const (c := x)).congr fun z hz ↦
      hf z fun hm ↦ hz (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self hm))
  -- Off `(1/4, 3/4)²`, which contains the middle square, `g = f = x`.
  have hfO : ∀ z ∉ Ioo (1 / 4 : ℝ) (3 / 4) ×ˢ Ioo (1 / 4 : ℝ) (3 / 4), f z = x :=
    fun z hz ↦ hf z fun hm ↦ hz (prod_mono (Ioo_subset_Ioo (by norm_num) (by norm_num))
      (Ioo_subset_Ioo (by norm_num) (by norm_num)) hm)
  have hfx := MapsSquareBoundaryTo.of_notMem_middleSquare hf
  refine ⟨g, hg, .of_forall_notMem (by norm_num) (by norm_num) fun z hz ↦
    (hgf z hz).trans (hfO z hz), ?_⟩
  -- `g` is homotopic to `f` relative to the boundary, and `f` is the squeeze of `P`.
  refine (Quotient.sound (squareGenLoop_homotopic (hu₀ := f.continuous) (hx₀ := hfx)
    (Φ := fun q ↦ R q) R.continuous (fun z ↦ R.apply_zero z) (fun z ↦ R.apply_one z)
    fun c ↦ .of_forall_notMem (by norm_num) (by norm_num) fun z hz ↦
      (R.eq_fst c hz).trans (hfO z hz))).symm.trans ?_
  exact squareGenLoop_comp_squeeze hPc hPx

/-- The squeeze `ρ c = squeeze c` of the homotopy parameter, as a point of the unit interval. -/
private def squeezeInterval (c : ℝ) : unitInterval :=
  ⟨squeeze c, squeeze_mem_Icc c⟩

/-- **Smoothing a homotopy of spheres.** On a closed manifold, two homotopic `C²` maps of the plane
sending the boundary of the unit square to `x` have squeezes joined by a `C²` homotopy keeping the
boundary of the square at `x`. A continuous homotopy between the representatives, reparametrized by
the squeeze in all three variables, is smooth near the ends and near the boundary; Whitney
approximation relative to these sets makes it smooth everywhere. -/
private theorem exists_contMDiff_homotopy_comp_squeeze {u₀ u₁ : ℝ × ℝ → M}
    (hu₀ : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 2 u₀) (hu₁ : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 2 u₁)
    {hx₀ : MapsSquareBoundaryTo u₀ x} {hx₁ : MapsSquareBoundaryTo u₁ x}
    (h : GenLoop.Homotopic (squareGenLoop u₀ hu₀.continuous hx₀)
      (squareGenLoop u₁ hu₁.continuous hx₁)) :
    ∃ Φ : (ℝ × ℝ) × ℝ → M, ContMDiff 𝓘(ℝ, (ℝ × ℝ) × ℝ) I 2 Φ ∧
      (∀ z, Φ (z, 0) = (u₀ ∘ Prod.map squeeze squeeze) z) ∧
      (∀ z, Φ (z, 1) = (u₁ ∘ Prod.map squeeze squeeze) z) ∧
      ∀ c, MapsSquareBoundaryTo (fun z ↦ Φ (z, c)) x := by
  obtain ⟨K⟩ := h
  -- The homotopy `K`, reparametrized by the squeeze in all three variables, is a continuous map
  -- of `(ℝ × ℝ) × ℝ` which is smooth near the two ends and near the boundary of the square.
  let G : C((ℝ × ℝ) × ℝ, M) := ⟨fun w ↦ K (squeezeInterval w.2, squeezeCube w.1), by
    have h₁ := continuous_squeezeCube
    have h₂ : Continuous squeezeInterval := continuous_squeeze.subtype_mk _
    fun_prop⟩
  have hG₀ {w : (ℝ × ℝ) × ℝ} (hw : w.2 ≤ 1 / 3) :
      G w = (u₀ ∘ Prod.map squeeze squeeze) w.1 := by
    have hc : squeezeInterval w.2 = 0 := Subtype.ext (squeeze_of_le hw)
    simp only [G, ContinuousMap.coe_mk, hc, ContinuousMap.HomotopyWith.apply_zero]
    exact squareGenLoop_apply _ _ _ _
  have hG₁ {w : (ℝ × ℝ) × ℝ} (hw : 2 / 3 ≤ w.2) :
      G w = (u₁ ∘ Prod.map squeeze squeeze) w.1 := by
    have hc : squeezeInterval w.2 = 1 := Subtype.ext (squeeze_of_ge hw)
    simp only [G, ContinuousMap.coe_mk, hc, ContinuousMap.HomotopyWith.apply_one]
    exact squareGenLoop_apply _ _ _ _
  have hGx {w : (ℝ × ℝ) × ℝ} (hw : w.1 ∉ middleSquare) : G w = x :=
    (K.eq_fst _ (squeezeCube_mem_boundary hw)).trans
      (GenLoop.boundary _ _ (squeezeCube_mem_boundary hw))
  -- Whitney approximation keeps `G` fixed off `(1/4, 3/4)³`, inside the open set off
  -- `[1/3, 2/3]³` where `G` is smooth.
  set U : Set ((ℝ × ℝ) × ℝ) :=
    ((Icc (1 / 3 : ℝ) (2 / 3) ×ˢ Icc (1 / 3 : ℝ) (2 / 3)) ×ˢ Icc (1 / 3 : ℝ) (2 / 3))ᶜ
  have hsq : ContMDiff 𝓘(ℝ, (ℝ × ℝ) × ℝ) 𝓘(ℝ, ℝ × ℝ) 2
      (fun w : (ℝ × ℝ) × ℝ ↦ Prod.map squeeze squeeze w.1) := by
    have h := contDiff_squeeze (n := 2)
    exact contMDiff_iff_contDiff.2 (by fun_prop)
  -- Near every point off `[1/3, 2/3]³`, `G` agrees with one of three smooth maps.
  have hGU : ContMDiffOn 𝓘(ℝ, (ℝ × ℝ) × ℝ) I 2 G U := by
    intro w hw
    refine ContMDiffAt.contMDiffWithinAt ?_
    rcases not_and_or.1 hw with h | h
    · refine (contMDiffAt_const (c := x)).congr_of_eventuallyEq ?_
      filter_upwards [((isClosed_Icc.prod isClosed_Icc).isOpen_compl.preimage
        continuous_fst).mem_nhds h] with w' hw'
      exact hGx fun hm ↦ hw' (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self hm)
    · rcases not_and_or.1 h with h | h <;> rw [not_le] at h
      · refine (hu₀.comp hsq w).congr_of_eventuallyEq ?_
        filter_upwards [(isOpen_lt continuous_snd continuous_const).mem_nhds h] with w' hw'
        exact hG₀ hw'.le
      · refine (hu₁.comp hsq w).congr_of_eventuallyEq ?_
        filter_upwards [(isOpen_lt continuous_const continuous_snd).mem_nhds h] with w' hw'
        exact hG₁ hw'.le
  obtain ⟨Φ, hΦ, hΦG, -⟩ := G.exists_contMDiff_homotopicRel_compl (J := I) 2
    ((isClosed_Icc.prod isClosed_Icc).prod isClosed_Icc)
    ((isOpen_Ioo.prod isOpen_Ioo).prod isOpen_Ioo)
    (prod_mono (prod_mono Icc_subset_Ioo_quarters Icc_subset_Ioo_quarters)
      Icc_subset_Ioo_quarters) hGU
  refine ⟨Φ, hΦ, fun z ↦ (hΦG _ fun hm ↦ absurd hm.2.1 (by norm_num)).trans (hG₀ (by norm_num)),
    fun z ↦ (hΦG _ fun hm ↦ absurd hm.2.2 (by norm_num)).trans (hG₁ (by norm_num)),
    fun c ↦ .of_forall_notMem (a := 1 / 4) (b := 3 / 4) (by norm_num) (by norm_num)
      fun z hz ↦ ?_⟩
  -- The smooth homotopy `Φ` keeps every edge of the square, off `(1/4, 3/4)²`, at `x`.
  exact (hΦG _ fun hm ↦ hz hm.1).trans (hGx fun hm ↦ hz (prod_mono
    (Ioo_subset_Ioo (by norm_num) (by norm_num)) (Ioo_subset_Ioo (by norm_num) (by norm_num)) hm))

/-- **Homotopy invariance of the integral over a sphere.** On a closed manifold, two `C²` maps of
the plane sending the boundary of the unit square to `x` which are homotopic as generalized loops
have the same integral of a closed `C¹` two-form over the square. -/
theorem rectangleIntegral_eq_of_homotopic {φ : RoughForm I M F 2}
    (hφ : IsSmoothForm I 1 φ) (hdφ : mextDeriv φ = 0) {u₀ u₁ : ℝ × ℝ → M}
    (hu₀ : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 2 u₀) (hu₁ : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 2 u₁)
    {hx₀ : MapsSquareBoundaryTo u₀ x} {hx₁ : MapsSquareBoundaryTo u₁ x}
    (h : GenLoop.Homotopic (squareGenLoop u₀ hu₀.continuous hx₀)
      (squareGenLoop u₁ hu₁.continuous hx₁)) :
    rectangleIntegral φ u₀ (0, 0) (1, 1) = rectangleIntegral φ u₁ (0, 0) (1, 1) := by
  obtain ⟨Φ, hΦ, hΦ₀, hΦ₁, hedge⟩ := exists_contMDiff_homotopy_comp_squeeze hu₀ hu₁ h
  have hint := rectangleIntegral_eq_of_homotopy_unitSquare hφ hdφ hΦ fun c _ ↦ hedge c
  rw [funext hΦ₀, funext hΦ₁, rectangleIntegral_comp_squeeze hφ hdφ hu₀ hx₀,
    rectangleIntegral_comp_squeeze hφ hdφ hu₁ hx₁] at hint
  exact hint.symm

/-- **The period of a sphere is its integral.** For a closed `C¹` two-form on a closed manifold and
a `C²` map of the plane sending the boundary of the unit square to `x`, the period of its class in
`π₂(M, x)` is the integral of the form over the square. -/
theorem spherePeriod_mk {φ : RoughForm I M F 2} (hφ : IsSmoothForm I 1 φ)
    (hdφ : mextDeriv φ = 0) {u : ℝ × ℝ → M} (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 2 u)
    (hx : MapsSquareBoundaryTo u x) :
    spherePeriod φ x ⟦squareGenLoop u hu.continuous hx⟧ = rectangleIntegral φ u (0, 0) (1, 1) := by
  have h := exists_contMDiff_squareGenLoop I (⟦squareGenLoop u hu.continuous hx⟧ : π_ 2 M x)
  unfold spherePeriod
  split_ifs with h'
  · obtain ⟨hv, hvx, hva⟩ := h'.choose_spec
    exact rectangleIntegral_eq_of_homotopic hφ hdφ (hv.of_le (by simp)) hu (Quotient.exact hva)
  · exact absurd h h'

/-- **Additivity of the period.** For a closed `C¹` two-form on a closed manifold, the period of a
product in `π₂(M, x)` is the sum of the periods. -/
theorem spherePeriod_mul {φ : RoughForm I M F 2} (hφ : IsSmoothForm I 1 φ)
    (hdφ : mextDeriv φ = 0) (a b : π_ 2 M x) :
    spherePeriod φ x (a * b) = spherePeriod φ x a + spherePeriod φ x b := by
  obtain ⟨u, hu, hux, rfl⟩ := exists_contMDiff_squareGenLoop I a
  obtain ⟨v, hv, hvx, rfl⟩ := exists_contMDiff_squareGenLoop I b
  have hsq : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) 2 (Prod.map squeeze squeeze) :=
    contMDiff_iff_contDiff.2 (contDiff_squeeze.prodMap contDiff_squeeze)
  -- Replace both representatives by their squeezes, which equal `x` off the middle square.
  have hu' : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 2 (u ∘ Prod.map squeeze squeeze) :=
    (hu.of_le (by simp)).comp hsq
  have hv' : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 2 (v ∘ Prod.map squeeze squeeze) :=
    (hv.of_le (by simp)).comp hsq
  have hu'x : ∀ z ∉ middleSquare, (u ∘ Prod.map squeeze squeeze) z = x :=
    fun _ ↦ comp_squeeze_eq hux
  have hv'x : ∀ z ∉ middleSquare, (v ∘ Prod.map squeeze squeeze) z = x :=
    fun _ ↦ comp_squeeze_eq hvx
  have hw := contMDiff_squareConcat hv' hu' hv'x hu'x
  rw [← squareGenLoop_comp_squeeze hu.continuous hux,
    ← squareGenLoop_comp_squeeze hv.continuous hvx, spherePeriod_mk hφ hdφ hu',
    spherePeriod_mk hφ hdφ hv']
  -- The product is the concatenation of the second factor followed by the first.
  have hgen : GenLoop.transAt 0
      (squareGenLoop _ hv'.continuous (MapsSquareBoundaryTo.of_notMem_middleSquare hv'x))
      (squareGenLoop _ hu'.continuous (MapsSquareBoundaryTo.of_notMem_middleSquare hu'x)) =
      squareGenLoop _ hw.continuous (mapsSquareBoundaryTo_squareConcat hv'x hu'x) := by
    ext y
    have h10 : (1 : Fin 2) ≠ 0 := by decide
    rcases le_or_gt (y 0 : ℝ) (1 / 2) with h | h
    · rw [GenLoop.transAt_apply_of_le 0 _ _ h
        (a := ⟨2 * y 0, by linarith [(y 0).2.1], by linarith⟩) rfl]
      simp only [squareGenLoop_apply, update_self, update_of_ne h10, squareConcat_of_le h]
    · rw [GenLoop.transAt_apply_of_lt 0 _ _ h
        (a := ⟨2 * y 0 - 1, by linarith, by linarith [(y 0).2.2]⟩) rfl]
      simp only [squareGenLoop_apply, update_self, update_of_ne h10, squareConcat_of_lt h]
  refine (congrArg (spherePeriod φ x) ((congrArg Additive.toMul
    (HomotopyGroup.ofMul_transAt 0 _ _)).symm.trans
      (congrArg (fun l ↦ (⟦l⟧ : π_ 2 M x)) hgen))).trans ?_
  rw [spherePeriod_mk hφ hdφ hw,
    rectangleIntegral_squareConcat (hφ.of_le (by simp)) (hw.of_le (by simp)) hv'x hu'x, add_comm]

/-- The period of the identity of `π₂(M, x)`, the class of the constant sphere, vanishes. -/
@[simp]
theorem spherePeriod_one {φ : RoughForm I M F 2} (hφ : IsSmoothForm I 1 φ)
    (hdφ : mextDeriv φ = 0) : spherePeriod φ x 1 = 0 := by
  have hx : MapsSquareBoundaryTo (fun _ : ℝ × ℝ ↦ x) x :=
    mapsSquareBoundaryTo_iff.2 fun _ _ _ _ _ ↦ rfl
  have h : (1 : π_ 2 M x) = ⟦squareGenLoop (fun _ ↦ x) continuous_const hx⟧ :=
    (congrArg Additive.toMul HomotopyGroup.ofMul_const).symm.trans
      (congrArg (fun l ↦ (⟦l⟧ : π_ 2 M x)) (GenLoop.ext _ _ fun _ ↦ by simp))
  rw [h, spherePeriod_mk hφ hdφ contMDiff_const, rectangleIntegral_const]

variable (x) in
/-- The **period homomorphism** of a closed `C¹` two-form `φ` on a closed manifold (compact,
Hausdorff, boundaryless and finite-dimensional): the integral of `φ` over spheres, as a
homomorphism from `π₂(M, x)` to the coefficients. For a symplectic form it is the symplectic area
of spheres. -/
def spherePeriodHom {φ : RoughForm I M F 2} (hφ : IsSmoothForm I 1 φ)
    (hdφ : mextDeriv φ = 0) : Additive (π_ 2 M x) →+ F where
  toFun a := spherePeriod φ x a.toMul
  map_zero' := spherePeriod_one hφ hdφ
  map_add' a b := spherePeriod_mul hφ hdφ a.toMul b.toMul

@[simp]
theorem spherePeriodHom_apply {φ : RoughForm I M F 2} (hφ : IsSmoothForm I 1 φ)
    (hdφ : mextDeriv φ = 0) (a : Additive (π_ 2 M x)) :
    spherePeriodHom x hφ hdφ a = spherePeriod φ x a.toMul :=
  (rfl)

end TauCeti

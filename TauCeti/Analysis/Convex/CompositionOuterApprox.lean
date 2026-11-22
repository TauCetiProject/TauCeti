/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Affine
public import Mathlib.Analysis.Convex.Function
public import TauCeti.Order.CompositionLift
import Mathlib.Algebra.Order.Hom.Monoid
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Prod
import TauCeti.Analysis.Calculus.FDeriv.Monotone
import TauCeti.Analysis.Convex.Strong

/-!
# Matched outer approximations of convex compositions

Let `D` be a set in a real normed space `X`, `g : X → ι → ℝ` an inner map with finitely many
coordinates, `h : (ι → ℝ) → ℝ` an outer function, `E` a set of admissible heights and `b` a budget.
The constraint `h (g x) ≤ b` on `D` cuts out `TauCeti.CompositionLift.originalSet D g h b`.
Given anchors `a i ∈ D` and derivatives `Dg i` of `g` at `a i` and `Dh i` of `h` at `g (a i)`,
there are three affine rows at each anchor:

    G_i(x) = g(a_i) + Dg_i (x - a_i)                 (component row)
    H_i(y) = h(g(a_i)) + Dh_i (y - g(a_i))           (outer row)
    C_i(x) = h(g(a_i)) + (Dh_i ∘ Dg_i) (x - a_i)     (direct row)

with `H_i (G_i x) = C_i x`. The *direct* outer approximation keeps `x ∈ D` and every `C_i x ≤ b`.
The *shared* outer approximation keeps `x ∈ D`, a single height vector `y ∈ E` and every
`G_i x ≤ y` and `H_i y ≤ b`: all anchors share the same `y`. Its variant on a set `J` of
coordinates also imposes the exact rows `y j = G_i x j` for `j ∈ J`.

When the coordinates of `g` outside `J` are convex on `D`, its coordinates in `J` are reproduced
exactly by their component rows, `h` is convex on `E` and `g` maps `D` into `E`, the tangent
support inequality of a convex function shows that the graph point `(x, g x)` of a point of the
original set satisfies every shared row. If every outer derivative `Dh i` is nonnegative on the
nonnegative directions vanishing on `J`, comparing affine rows shows that the projection of the
shared approximation lies in the direct one. Hence

    originalSet D g h b ⊆ Prod.fst '' sharedOuterApproxOn J D E g h a Dg Dh b
                       ⊆ directOuterApprox D g h a Dg Dh b,

so the shared rows are valid and at least as tight as the direct ones with the same anchors. For
`J = ∅` the sign condition says that each `Dh i` is monotone; when `h` is monotone on the whole
height space this follows from differentiability. On coordinates in `J` the outer derivatives may
have either sign. No monotonicity of `h` itself enters the first inclusion.

The inner map `g` is differentiated within `D` and the outer function `h` within `E`, so anchors
and heights may lie on the boundary of the domains. Only the full-space comparison for a monotone
`h` takes derivatives of `h` on the whole height space.

## Main definitions

* `TauCeti.CompositionLift.componentRow`, `TauCeti.CompositionLift.outerRow`,
  `TauCeti.CompositionLift.directRow`: the rows `G_i`, `H_i` and `C_i`.
* `TauCeti.CompositionLift.directOuterApprox`: the direct outer approximation.
* `TauCeti.CompositionLift.sharedOuterApprox`: the shared-height outer approximation.
* `TauCeti.CompositionLift.sharedOuterApproxOn`: the shared approximation with exact rows on `J`.

## Main results

* `TauCeti.CompositionLift.componentRow_apply_le`, `TauCeti.CompositionLift.outerRow_le`,
  `TauCeti.CompositionLift.directRow_le`: tangent support of the three rows.
* `TauCeti.CompositionLift.componentRow_apply_eq_of_eq_continuousAffineMap`: the component row
  of an affine coordinate is exact.
* `TauCeti.CompositionLift.originalSet_subset_fst_image_sharedOuterApproxOn` and
  `TauCeti.CompositionLift.fst_image_sharedOuterApproxOn_subset_directOuterApprox`: the
  comparison with exact rows on `J`.
* `TauCeti.CompositionLift.originalSet_subset_fst_image_sharedOuterApprox` and
  `TauCeti.CompositionLift.fst_image_sharedOuterApprox_subset_directOuterApprox`: the comparison
  with inequality heights only, under monotone outer derivatives.
* `TauCeti.CompositionLift.fst_image_sharedOuterApprox_subset_directOuterApprox_of_monotone`:
  the same comparison when `h` is monotone on the whole height space.
* `TauCeti.CompositionLift.sharedOuterApprox_empty_heights`,
  `TauCeti.CompositionLift.sharedOuterApproxOn_empty_heights`,
  `TauCeti.CompositionLift.directOuterApprox_of_isEmpty`,
  `TauCeti.CompositionLift.sharedOuterApproxOn_of_isEmpty` and
  `TauCeti.CompositionLift.fst_image_sharedOuterApprox_of_isEmpty`: the degenerate cases of no
  admissible heights and no anchors.

## References

* M. Tawarmalani and N. V. Sahinidis, *A polyhedral branch-and-cut approach to global
  optimization*, Math. Program. 103 (2005), 225–249, §2, Theorem 1. The source compares epigraph
  pairs, keeps affine inner coordinates as equalities and assumes monotonicity of the outer
  function in the other coordinates; here the budget is a fixed scalar and the sign condition is
  stated for the outer derivatives at the anchors.
-/

public section

open Set

namespace TauCeti.CompositionLift

variable {X ι κ : Type*}

/-! ### Rows -/

section OuterRow

variable {g : X → ι → ℝ} {h : (ι → ℝ) → ℝ} {a : X} {y : ι → ℝ} {Dh : (ι → ℝ) →L[ℝ] ℝ}

/-- The outer row `y ↦ h (g a) + Dh (y - g a)`: the affine approximation of the outer function `h`
at the image `g a` of the anchor, with derivative `Dh`. -/
def outerRow (g : X → ι → ℝ) (h : (ι → ℝ) → ℝ) (a : X) (Dh : (ι → ℝ) →L[ℝ] ℝ) (y : ι → ℝ) : ℝ :=
  h (g a) + Dh (y - g a)

theorem outerRow_def : outerRow g h a Dh y = h (g a) + Dh (y - g a) :=
  (rfl)

/-- A continuous linear outer function is its own outer row at any anchor. -/
@[simp]
theorem outerRow_continuousLinearMap (L : (ι → ℝ) →L[ℝ] ℝ) : outerRow g L a L y = L y := by
  simp [outerRow_def]

/-- For the outer sum, the outer row at any anchor is the sum of the heights. -/
@[simp]
theorem outerRow_sum_coord [Fintype ι] :
    outerRow g (fun y ↦ ∑ j, y j) a (∑ j, ContinuousLinearMap.proj j) y = ∑ j, y j := by
  convert outerRow_continuousLinearMap (g := g) (a := a) (y := y)
    (∑ j, ContinuousLinearMap.proj (R := ℝ) j) using 2
  · ext
    simp
  · simp

@[simp]
theorem outerRow_self : outerRow g h a Dh (g a) = h (g a) := by
  simp [outerRow_def]

/-- The outer row is affine with linear part `Dh`. -/
theorem outerRow_sub_outerRow (y y' : ι → ℝ) :
    outerRow g h a Dh y - outerRow g h a Dh y' = Dh (y - y') := by
  simp only [outerRow_def, map_sub]
  ring

/-- **Outer support.** If `h` is convex on `E` and has derivative `Dh` within `E` at `g a ∈ E`,
then the outer row lies below `h` on `E`. -/
theorem outerRow_le [Finite ι] {E : Set (ι → ℝ)} (hh : ConvexOn ℝ E h) (ha : g a ∈ E)
    (hy : y ∈ E) (hd : HasFDerivWithinAt h Dh E (g a)) : outerRow g h a Dh y ≤ h y :=
  have := Fintype.ofFinite ι
  hh.add_le_of_hasFDerivWithinAt ha hy hd

end OuterRow

variable [NormedAddCommGroup X] [NormedSpace ℝ X]

section Rows

variable {g : X → ι → ℝ} {h : (ι → ℝ) → ℝ} {a x : X} {Dg : X →L[ℝ] ι → ℝ}
  {Dh : (ι → ℝ) →L[ℝ] ℝ}

/-- The component row `x ↦ g a + Dg (x - a)`: the affine approximation of the inner map `g` at
the anchor `a` with derivative `Dg`. -/
def componentRow (g : X → ι → ℝ) (a : X) (Dg : X →L[ℝ] ι → ℝ) (x : X) : ι → ℝ :=
  g a + Dg (x - a)

/-- The direct row `x ↦ h (g a) + (Dh ∘ Dg) (x - a)`: the affine approximation of the composition
`h ∘ g` at the anchor `a` with the chain-rule derivative `Dh ∘ Dg`. -/
def directRow (g : X → ι → ℝ) (h : (ι → ℝ) → ℝ) (a : X) (Dg : X →L[ℝ] ι → ℝ)
    (Dh : (ι → ℝ) →L[ℝ] ℝ) (x : X) : ℝ :=
  h (g a) + (Dh.comp Dg) (x - a)

theorem componentRow_def : componentRow g a Dg x = g a + Dg (x - a) :=
  (rfl)

/-- A continuous linear inner map is its own component row at any anchor. -/
@[simp]
theorem componentRow_continuousLinearMap (L : X →L[ℝ] ι → ℝ) : componentRow L a L x = L x := by
  simp [componentRow_def]

/-- The component row of the identity inner map is the identity at every anchor. -/
@[simp]
theorem componentRow_id [Fintype ι] (a x : ι → ℝ) :
    componentRow id a (ContinuousLinearMap.id ℝ _) x = x := by
  simpa using componentRow_continuousLinearMap (a := a) (x := x) (ContinuousLinearMap.id ℝ _)

theorem directRow_def : directRow g h a Dg Dh x = h (g a) + Dh (Dg (x - a)) :=
  (rfl)

@[simp]
theorem componentRow_self : componentRow g a Dg a = g a := by
  simp [componentRow_def]

@[simp]
theorem directRow_self : directRow g h a Dg Dh a = h (g a) := by
  simp [directRow_def]

/-- The outer row evaluated at the component row is the direct row. -/
@[simp]
theorem outerRow_componentRow :
    outerRow g h a Dh (componentRow g a Dg x) = directRow g h a Dg Dh x := by
  simp [outerRow_def, componentRow_def, directRow_def]

variable [Finite ι] {D : Set X}

/-- **Component support.** If the coordinate `j` of `g` is convex on `D` and `g` has derivative
`Dg` within `D` at the anchor `a ∈ D`, then the component row lies below `g` in that coordinate
at every `x ∈ D`. -/
theorem componentRow_apply_le {j : ι} (hc : ConvexOn ℝ D fun x ↦ g x j) (ha : a ∈ D) (hx : x ∈ D)
    (hg : HasFDerivWithinAt g Dg D a) : componentRow g a Dg x j ≤ g x j := by
  have := Fintype.ofFinite ι
  simpa [componentRow_def] using hc.add_le_of_hasFDerivWithinAt ha hx (hasFDerivWithinAt_pi'.1 hg j)

/-- **Component support.** If every coordinate of `g` is convex on `D` and `g` has derivative `Dg`
within `D` at the anchor `a ∈ D`, then the component row lies below `g` on `D`. -/
theorem componentRow_le (hc : ∀ j, ConvexOn ℝ D fun x ↦ g x j) (ha : a ∈ D) (hx : x ∈ D)
    (hg : HasFDerivWithinAt g Dg D a) : componentRow g a Dg x ≤ g x :=
  fun j ↦ componentRow_apply_le (hc j) ha hx hg

/-- **Exact component rows.** If the coordinate `j` of `g` is a continuous affine map, `D` is
convex and `g` has derivative `Dg` within `D` at the anchor `a ∈ D`, then the component row
reproduces that coordinate at every `x ∈ D`. -/
theorem componentRow_apply_eq_of_eq_continuousAffineMap {j : ι} (φ : X →ᴬ[ℝ] ℝ)
    (hφ : (fun x ↦ g x j) = φ) (hD : Convex ℝ D) (ha : a ∈ D) (hx : x ∈ D)
    (hg : HasFDerivWithinAt g Dg D a) : componentRow g a Dg x j = g x j := by
  have := Fintype.ofFinite ι
  -- Along the segment `[a, x] ⊆ D`, both `Dg (x - a) j` and `φ.contLinear (x - a)` are the
  -- derivative of `t ↦ φ (a + t • (x - a))` within `[0, 1]` at `0`.
  have hseg : Icc (0 : ℝ) 1 ⊆ (fun t : ℝ ↦ a + t • (x - a)) ⁻¹' D :=
    fun _ ht ↦ hD.add_smul_sub_mem ha hx ht
  have h₁ : HasLineDerivWithinAt ℝ φ (Dg (x - a) j) D a (x - a) := by
    simpa [← hφ] using (hasFDerivWithinAt_pi'.1 hg j).hasLineDerivWithinAt (x - a)
  have hj : Dg (x - a) j = φ.contLinear (x - a) :=
    (uniqueDiffOn_Icc_zero_one 0 (left_mem_Icc.2 zero_le_one)).eq_deriv _
      (HasDerivWithinAt.mono h₁ hseg)
      (HasDerivWithinAt.mono (φ.hasFDerivAt.hasFDerivWithinAt.hasLineDerivWithinAt (x - a)) hseg)
  have hφx : φ x = φ.contLinear (x - a) + φ a := by
    simpa using φ.map_vadd a (x - a)
  rw [componentRow_def, Pi.add_apply, hj, congr_fun hφ a, congr_fun hφ x, hφx, add_comm]

/-- **Direct support.** If the composition `h ∘ g` is convex on `D`, `g` maps `D` into `E`, `h` has
derivative `Dh` within `E` at `g a` and `g` has derivative `Dg` within `D` at the anchor `a ∈ D`,
then the direct row lies below `h ∘ g` on `D`. -/
theorem directRow_le {E : Set (ι → ℝ)} (hc : ConvexOn ℝ D (h ∘ g)) (hgE : MapsTo g D E)
    (ha : a ∈ D) (hx : x ∈ D) (hh : HasFDerivWithinAt h Dh E (g a))
    (hg : HasFDerivWithinAt g Dg D a) : directRow g h a Dg Dh x ≤ h (g x) :=
  have := Fintype.ofFinite ι
  hc.add_le_of_hasFDerivWithinAt ha hx (hh.comp a hg hgE)

end Rows

/-! ### Outer approximations -/

section Sets

variable {J J' : Set ι} {D : Set X} {E : Set (ι → ℝ)} {g : X → ι → ℝ} {h : (ι → ℝ) → ℝ}
  {a : κ → X} {Dg : κ → X →L[ℝ] ι → ℝ} {Dh : κ → (ι → ℝ) →L[ℝ] ℝ} {b : ℝ}

/-- The direct outer approximation: the points of `D` satisfying every direct row at the anchors
`a i` within the budget `b`. -/
def directOuterApprox (D : Set X) (g : X → ι → ℝ) (h : (ι → ℝ) → ℝ) (a : κ → X)
    (Dg : κ → X →L[ℝ] ι → ℝ) (Dh : κ → (ι → ℝ) →L[ℝ] ℝ) (b : ℝ) : Set X :=
  {x | x ∈ D ∧ ∀ i, directRow g h (a i) (Dg i) (Dh i) x ≤ b}

/-- The shared outer approximation: the pairs `(x, y)` with `x ∈ D` and a single height vector
`y ∈ E` that dominates every component row and satisfies every outer row within the budget `b`. -/
def sharedOuterApprox (D : Set X) (E : Set (ι → ℝ)) (g : X → ι → ℝ) (h : (ι → ℝ) → ℝ)
    (a : κ → X) (Dg : κ → X →L[ℝ] ι → ℝ) (Dh : κ → (ι → ℝ) →L[ℝ] ℝ) (b : ℝ) :
    Set (X × (ι → ℝ)) :=
  {z | z.1 ∈ D ∧ z.2 ∈ E ∧
    ∀ i, componentRow g (a i) (Dg i) z.1 ≤ z.2 ∧ outerRow g h (a i) (Dh i) z.2 ≤ b}

/-- The shared outer approximation with exact rows on the coordinates in `J`: the points of the
shared approximation whose heights in `J` equal every component row there. -/
def sharedOuterApproxOn (J : Set ι) (D : Set X) (E : Set (ι → ℝ)) (g : X → ι → ℝ)
    (h : (ι → ℝ) → ℝ) (a : κ → X) (Dg : κ → X →L[ℝ] ι → ℝ) (Dh : κ → (ι → ℝ) →L[ℝ] ℝ) (b : ℝ) :
    Set (X × (ι → ℝ)) :=
  {z | z ∈ sharedOuterApprox D E g h a Dg Dh b ∧
    ∀ i, ∀ j ∈ J, z.2 j = componentRow g (a i) (Dg i) z.1 j}

@[simp]
theorem mem_directOuterApprox {x : X} :
    x ∈ directOuterApprox D g h a Dg Dh b ↔
      x ∈ D ∧ ∀ i, directRow g h (a i) (Dg i) (Dh i) x ≤ b :=
  Iff.rfl

@[simp]
theorem mem_sharedOuterApprox {z : X × (ι → ℝ)} :
    z ∈ sharedOuterApprox D E g h a Dg Dh b ↔ z.1 ∈ D ∧ z.2 ∈ E ∧
      ∀ i, componentRow g (a i) (Dg i) z.1 ≤ z.2 ∧ outerRow g h (a i) (Dh i) z.2 ≤ b :=
  Iff.rfl

@[simp]
theorem mem_sharedOuterApproxOn {z : X × (ι → ℝ)} :
    z ∈ sharedOuterApproxOn J D E g h a Dg Dh b ↔ z ∈ sharedOuterApprox D E g h a Dg Dh b ∧
      ∀ i, ∀ j ∈ J, z.2 j = componentRow g (a i) (Dg i) z.1 j :=
  Iff.rfl

theorem directOuterApprox_subset : directOuterApprox D g h a Dg Dh b ⊆ D :=
  fun _ hx ↦ hx.1

theorem fst_image_sharedOuterApprox_subset :
    Prod.fst '' sharedOuterApprox D E g h a Dg Dh b ⊆ D := by
  rintro _ ⟨z, hz, rfl⟩
  exact hz.1

/-- Forgetting the exact rows gives a point of the shared approximation. -/
theorem sharedOuterApproxOn_subset :
    sharedOuterApproxOn J D E g h a Dg Dh b ⊆ sharedOuterApprox D E g h a Dg Dh b :=
  fun _ hz ↦ hz.1

@[simp]
theorem sharedOuterApproxOn_empty :
    sharedOuterApproxOn ∅ D E g h a Dg Dh b = sharedOuterApprox D E g h a Dg Dh b := by
  ext z
  simp

/-- Exact rows on more coordinates give a smaller approximation. -/
theorem sharedOuterApproxOn_anti (hJ : J' ⊆ J) :
    sharedOuterApproxOn J D E g h a Dg Dh b ⊆ sharedOuterApproxOn J' D E g h a Dg Dh b :=
  fun _ hz ↦ ⟨hz.1, fun i j hj ↦ hz.2 i j (hJ hj)⟩

/-! ### Degenerate cases -/

/-- The shared approximation lies in the product of the domain and the admissible heights. -/
theorem sharedOuterApprox_subset_prod : sharedOuterApprox D E g h a Dg Dh b ⊆ D ×ˢ E :=
  fun _ hz ↦ ⟨hz.1, hz.2.1⟩

/-- With no admissible heights the shared approximation is empty, whatever the anchors, rows and
budget. -/
@[simp]
theorem sharedOuterApprox_empty_heights : sharedOuterApprox D ∅ g h a Dg Dh b = ∅ :=
  subset_empty_iff.1 <| sharedOuterApprox_subset_prod.trans (prod_empty (s := D)).subset

/-- With no admissible heights the shared approximation with exact rows on `J` is empty, whatever
the anchors, rows and budget. -/
@[simp]
theorem sharedOuterApproxOn_empty_heights : sharedOuterApproxOn J D ∅ g h a Dg Dh b = ∅ :=
  subset_empty_iff.1 <| sharedOuterApproxOn_subset.trans sharedOuterApprox_empty_heights.subset

/-- Without anchors the direct approximation is the domain. -/
@[simp]
theorem directOuterApprox_of_isEmpty [IsEmpty κ] : directOuterApprox D g h a Dg Dh b = D := by
  ext x
  simp

/-- Without anchors the shared approximation is the product of the domain and the heights. -/
@[simp]
theorem sharedOuterApprox_of_isEmpty [IsEmpty κ] :
    sharedOuterApprox D E g h a Dg Dh b = D ×ˢ E := by
  ext z
  simp

/-- Without anchors the shared approximation with exact rows on `J` is the product of the domain
and the heights. -/
@[simp]
theorem sharedOuterApproxOn_of_isEmpty [IsEmpty κ] :
    sharedOuterApproxOn J D E g h a Dg Dh b = D ×ˢ E := by
  ext z
  simp

/-- Without anchors and with some admissible height, the projected shared approximation is the
domain. -/
theorem fst_image_sharedOuterApprox_of_isEmpty [IsEmpty κ] (hE : E.Nonempty) :
    Prod.fst '' sharedOuterApprox D E g h a Dg Dh b = D := by
  rw [sharedOuterApprox_of_isEmpty, fst_image_prod _ hE]

/-! ### The comparison theorems -/

/-- **Shared rows contain the original set.** Assume that `g` maps `D` into `E`, that the
component rows are exact at `x` on the coordinates in `J`, that the coordinates of `g` outside `J`
are convex on `D`, that `h` is convex on `E`, and that `g` and `h` have derivatives `Dg i` within
`D` at `a i ∈ D` and `Dh i` within `E` at `g (a i)`. Then the graph point `(x, g x)` of a point `x`
of the original set lies in the shared approximation with exact rows on `J`. -/
theorem mk_mem_sharedOuterApproxOn_of_mem_originalSet [Finite ι] (hgE : MapsTo g D E)
    (hc : ∀ j ∉ J, ConvexOn ℝ D fun x ↦ g x j) (hh : ConvexOn ℝ E h) (ha : ∀ i, a i ∈ D)
    (hg : ∀ i, HasFDerivWithinAt g (Dg i) D (a i))
    (hdh : ∀ i, HasFDerivWithinAt h (Dh i) E (g (a i))) {x : X}
    (hexact : ∀ i, ∀ j ∈ J, componentRow g (a i) (Dg i) x j = g x j)
    (hx : x ∈ originalSet D g h b) :
    (x, g x) ∈ sharedOuterApproxOn J D E g h a Dg Dh b := by
  obtain ⟨hxD, hxb⟩ := mem_originalSet.1 hx
  refine ⟨⟨hxD, hgE hxD, fun i ↦ ⟨fun j ↦ ?_, ?_⟩⟩, fun i j hj ↦ (hexact i j hj).symm⟩
  · by_cases hj : j ∈ J
    · exact (hexact i j hj).le
    · exact componentRow_apply_le (hc j hj) (ha i) hxD (hg i)
  · exact (outerRow_le hh (hgE (ha i)) (hgE hxD) (hdh i)).trans hxb

/-- **The original set lies in the shared approximation with exact rows on `J`.** Under the
hypotheses of `mk_mem_sharedOuterApproxOn_of_mem_originalSet`, with the component rows exact on
the coordinates in `J` at every point of `D`, every point of the original set lifts to the shared
approximation. -/
theorem originalSet_subset_fst_image_sharedOuterApproxOn [Finite ι] (hgE : MapsTo g D E)
    (hexact : ∀ i, ∀ x ∈ D, ∀ j ∈ J, componentRow g (a i) (Dg i) x j = g x j)
    (hc : ∀ j ∉ J, ConvexOn ℝ D fun x ↦ g x j) (hh : ConvexOn ℝ E h) (ha : ∀ i, a i ∈ D)
    (hg : ∀ i, HasFDerivWithinAt g (Dg i) D (a i))
    (hdh : ∀ i, HasFDerivWithinAt h (Dh i) E (g (a i))) :
    originalSet D g h b ⊆ Prod.fst '' sharedOuterApproxOn J D E g h a Dg Dh b :=
  fun x hx ↦ ⟨(x, g x), mk_mem_sharedOuterApproxOn_of_mem_originalSet hgE hc hh ha hg hdh
    (fun i ↦ hexact i x (mem_originalSet.1 hx).1) hx, rfl⟩

/-- **The shared approximation with exact rows on `J` lies in the direct one.** If every outer
derivative `Dh i` is nonnegative on the nonnegative directions vanishing on `J`, then the
projection of the shared approximation with exact rows on `J` lies in the direct approximation
with the same anchors. Neither convexity nor membership of the component rows in `E` is needed. -/
theorem fst_image_sharedOuterApproxOn_subset_directOuterApprox
    (hD : ∀ i, ∀ v : ι → ℝ, 0 ≤ v → (∀ j ∈ J, v j = 0) → 0 ≤ Dh i v) :
    Prod.fst '' sharedOuterApproxOn J D E g h a Dg Dh b ⊆ directOuterApprox D g h a Dg Dh b := by
  rintro _ ⟨z, ⟨⟨hzD, -, hz⟩, hzJ⟩, rfl⟩
  refine ⟨hzD, fun i ↦ ?_⟩
  -- The direction `z.2 - G_i (z.1)` is nonnegative and vanishes on `J`.
  have hv := hD i (z.2 - componentRow g (a i) (Dg i) z.1) (sub_nonneg.2 (hz i).1)
    fun j hj ↦ by simp [hzJ i j hj]
  have hsub := outerRow_sub_outerRow (g := g) (h := h) (a := a i) (Dh := Dh i) z.2
    (componentRow g (a i) (Dg i) z.1)
  rw [outerRow_componentRow] at hsub
  linarith [(hz i).2]

/-- **Shared rows contain the original set.** If `g` maps `D` into `E`, every coordinate of `g` is
convex on `D`, `h` is convex on `E`, and `g` and `h` have derivatives `Dg i` within `D` at
`a i ∈ D` and `Dh i` within `E` at `g (a i)`, then the graph point `(x, g x)` of a point `x` of the
original set lies in the shared approximation. -/
theorem mk_mem_sharedOuterApprox_of_mem_originalSet [Finite ι] (hgE : MapsTo g D E)
    (hc : ∀ j, ConvexOn ℝ D fun x ↦ g x j) (hh : ConvexOn ℝ E h) (ha : ∀ i, a i ∈ D)
    (hg : ∀ i, HasFDerivWithinAt g (Dg i) D (a i))
    (hdh : ∀ i, HasFDerivWithinAt h (Dh i) E (g (a i))) {x : X} (hx : x ∈ originalSet D g h b) :
    (x, g x) ∈ sharedOuterApprox D E g h a Dg Dh b :=
  sharedOuterApproxOn_subset <| mk_mem_sharedOuterApproxOn_of_mem_originalSet (J := ∅) hgE
    (fun j _ ↦ hc j) hh ha hg hdh (by simp) hx

/-- **The original set lies in the shared approximation.** If `g` maps `D` into `E`, every
coordinate of `g` is convex on `D`, `h` is convex on `E`, and `g` and `h` have derivatives `Dg i`
within `D` at `a i ∈ D` and `Dh i` within `E` at `g (a i)`, then every point of the original set
lifts to the shared approximation. Monotonicity of `h` is not needed. -/
theorem originalSet_subset_fst_image_sharedOuterApprox [Finite ι] (hgE : MapsTo g D E)
    (hc : ∀ j, ConvexOn ℝ D fun x ↦ g x j) (hh : ConvexOn ℝ E h) (ha : ∀ i, a i ∈ D)
    (hg : ∀ i, HasFDerivWithinAt g (Dg i) D (a i))
    (hdh : ∀ i, HasFDerivWithinAt h (Dh i) E (g (a i))) :
    originalSet D g h b ⊆ Prod.fst '' sharedOuterApprox D E g h a Dg Dh b :=
  fun x hx ↦ ⟨(x, g x), mk_mem_sharedOuterApprox_of_mem_originalSet hgE hc hh ha hg hdh hx, rfl⟩

/-- **The shared approximation lies in the direct one.** If every outer derivative `Dh i` is
monotone, then the projection of the shared approximation lies in the direct approximation with
the same anchors. -/
theorem fst_image_sharedOuterApprox_subset_directOuterApprox (hD : ∀ i, Monotone (Dh i)) :
    Prod.fst '' sharedOuterApprox D E g h a Dg Dh b ⊆ directOuterApprox D g h a Dg Dh b := by
  simpa using fst_image_sharedOuterApproxOn_subset_directOuterApprox (J := ∅) (D := D) (E := E)
    (g := g) (h := h) (a := a) (Dg := Dg) (b := b)
    fun i v hv _ ↦ (monotone_iff_map_nonneg (Dh i)).1 (hD i) v hv

/-- **The shared approximation lies in the direct one for a monotone outer function.** If `h` is
monotone on the whole height space and has derivative `Dh i` at every `g (a i)`, then the
projection of the shared approximation lies in the direct approximation with the same anchors. -/
theorem fst_image_sharedOuterApprox_subset_directOuterApprox_of_monotone [Finite ι]
    (hm : Monotone h) (hdh : ∀ i, HasFDerivAt h (Dh i) (g (a i))) :
    Prod.fst '' sharedOuterApprox D E g h a Dg Dh b ⊆ directOuterApprox D g h a Dg Dh b :=
  have := Fintype.ofFinite ι
  fst_image_sharedOuterApprox_subset_directOuterApprox fun i ↦ (hdh i).monotone_of_monotone hm

/-- **The original set lies in the direct approximation.** If the composition `h ∘ g` is convex on
`D`, `g` maps `D` into `E`, `h` has derivative `Dh i` within `E` at `g (a i)` and `g` has
derivative `Dg i` within `D` at `a i ∈ D`, then every point of the original set satisfies the
direct rows. -/
theorem originalSet_subset_directOuterApprox [Finite ι] (hc : ConvexOn ℝ D (h ∘ g))
    (hgE : MapsTo g D E) (ha : ∀ i, a i ∈ D) (hdh : ∀ i, HasFDerivWithinAt h (Dh i) E (g (a i)))
    (hg : ∀ i, HasFDerivWithinAt g (Dg i) D (a i)) :
    originalSet D g h b ⊆ directOuterApprox D g h a Dg Dh b :=
  fun _ hx ↦ ⟨(mem_originalSet.1 hx).1, fun i ↦
    (directRow_le hc hgE (ha i) (mem_originalSet.1 hx).1 (hdh i) (hg i)).trans
      (mem_originalSet.1 hx).2⟩

end Sets

end TauCeti.CompositionLift

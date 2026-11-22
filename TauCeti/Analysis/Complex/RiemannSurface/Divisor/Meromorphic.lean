/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.Divisor.Sheaf
public import TauCeti.Analysis.Complex.RiemannSurface.FunctionField.Order
public import TauCeti.Analysis.Complex.RiemannSurface.Degree
import Mathlib.LinearAlgebra.Dimension.Constructions
import TauCeti.Analysis.Complex.RiemannSurface.FunctionField.Divisor

/-!
# Divisor sections as meromorphic functions

Global sections of `𝒪_D` use representatives which are zero wherever `D` permits a pole.
Consequently even a constant meromorphic function need not have a constant representative.
This file embeds these sections linearly into the field of meromorphic functions using
`MeromorphicFunction.ofMeromorphic`, which fills removable singularities and poles on the
native Riemann sphere. The embedding preserves the order bound and is injective despite the
normalization of representatives.

If the space of sections has dimension greater than one, its image cannot consist only of
constants. On a compact connected Riemann surface this produces a finite holomorphic map to
the sphere, with the prescribed pole bound. This is the linear-algebra step converting a
lower bound on the dimension of a divisor's section space into an actual finite map. When the
divisor `D` bounding the poles is effective, the degree of this map is at most `deg D`, so a
second section of the divisor of a single point gives a map of degree one.

If adding a point `x` to `D` enlarges the space of sections, a new section is a meromorphic
function whose order at `x` is exactly the newly allowed `-(D(x) + 1)`.

Since principal divisors have degree zero, the same embedding shows that a divisor of negative
degree on a compact connected Riemann surface has no nonzero global sections.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  §16, for divisor sections and the construction of meromorphic functions from a dimension bound.
-/

public noncomputable section

open CategoryTheory Filter OnePoint Opposite Set TopologicalSpace Topology
open scoped Manifold ContDiff

namespace TauCeti.RiemannSurface

open TauCeti.AlgebraicGeometry (WeilDivisor)

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [ConnectedSpace X]

namespace divisorSections

variable {D : WeilDivisor X}

/-- Embed global sections of `𝒪_D` into meromorphic functions, filling in their normalized
values at the points where poles are allowed. -/
def toMeromorphic (D : WeilDivisor X) :
    divisorSections D ⊤ →ₗ[ℂ] MeromorphicFunction X where
  toFun f := MeromorphicFunction.ofMeromorphic fun x ↦ (isDivisorSectionAt f x).meromorphicAt
  map_add' f g := MeromorphicFunction.ofMeromorphic_add _ _
  map_smul' c f := by
    simpa only [Algebra.smul_def, RingHom.id_apply, MeromorphicFunction.ofMeromorphic_const] using
      (MeromorphicFunction.ofMeromorphic_mul
        (fun x ↦ meromorphicAt_const c x) (fun x ↦ (isDivisorSectionAt f x).meromorphicAt))

/-- The finite part of the meromorphic image agrees with the section on punctured
neighbourhoods, including at points where a pole is allowed but removable. -/
theorem finitePart_toMeromorphic_eventuallyEq (f : divisorSections D ⊤) (x : X) :
    (toMeromorphic D f).finitePart =ᶠ[𝓝[≠] x] fun y ↦ f.val ⟨y, trivial⟩ :=
  MeromorphicFunction.finitePart_ofMeromorphic_eventuallyEq
    (fun y ↦ (isDivisorSectionAt f y).meromorphicAt) x

/-- Where the divisor allows no pole, the meromorphic image takes the section's actual value. -/
@[simp]
theorem toMeromorphic_apply_of_nonpos (f : divisorSections D ⊤) {x : X} (hx : D x ≤ 0) :
    toMeromorphic D f x = (f.val ⟨x, trivial⟩ : OnePoint ℂ) :=
  MeromorphicFunction.ofMeromorphic_apply_of_continuousAt
    (fun y ↦ (isDivisorSectionAt f y).meromorphicAt)
    ((isDivisorSectionAt f x).contMDiffAt hx).continuousAt

/-- Filling the normalized values loses no information: the map to meromorphic functions
is injective. -/
theorem toMeromorphic_injective (D : WeilDivisor X) :
    Function.Injective (toMeromorphic D) := by
  intro f g h
  apply Subtype.ext
  funext x
  by_cases hx : 0 < D x
  · rw [apply_eq_zero_of_mem_divisorSections f.property hx,
      apply_eq_zero_of_mem_divisorSections g.property hx]
  · exact OnePoint.coe_injective <| by
      simpa only [toMeromorphic_apply_of_nonpos f (le_of_not_gt hx),
        toMeromorphic_apply_of_nonpos g (le_of_not_gt hx)] using
        congrArg (fun k : MeromorphicFunction X ↦ k x) h

/-- The order of the meromorphic image is the order of the section's representative. -/
theorem order_toMeromorphic (f : divisorSections D ⊤) (x : X) :
    MeromorphicFunction.order x (toMeromorphic D f) =
      meromorphicOrderAt (fun y ↦ f.val ⟨y, trivial⟩) x := by
  rw [MeromorphicFunction.order_apply,
    meromorphicOrderAt_congr (finitePart_toMeromorphic_eventuallyEq f x)]

/-- The embedding preserves the defining pole and zero bound of `𝒪_D`. -/
theorem neg_le_order_toMeromorphic (f : divisorSections D ⊤) (x : X) :
    ((-D x : ℤ) : WithTop ℤ) ≤ MeromorphicFunction.order x (toMeromorphic D f) := by
  rw [order_toMeromorphic]
  exact (isDivisorSectionAt f x).neg_le_meromorphicOrderAt

/-- The image consists exactly of the meromorphic functions satisfying the divisor bound.
This also accounts for allowed poles which happen to be removable: their section
representatives must still be normalized to zero. -/
theorem mem_range_toMeromorphic_iff (f : MeromorphicFunction X) :
    f ∈ (toMeromorphic D).range ↔
      ∀ x, ((-D x : ℤ) : WithTop ℤ) ≤ MeromorphicFunction.order x f := by
  classical
  have := ChartedSpace.t1Space ℂ X
  refine ⟨fun ⟨s, hs⟩ ↦ hs ▸ neg_le_order_toMeromorphic s, fun hf ↦ ?_⟩
  let g : X → ℂ := {x | D x ≤ 0}.indicator f.finitePart
  have hEq (x : X) : g =ᶠ[𝓝[≠] x] f.finitePart := by
    filter_upwards [D.eventually_eq_zero_nhdsNE x] with y hy
    exact Set.indicator_of_mem (s := {x | D x ≤ 0}) hy.le _
  have hg (x : X) : IsDivisorSectionAt D g x := by
    refine ⟨(f.meromorphicAt_finitePart x).congr (hEq x).symm, ?_, ?_, ?_⟩
    · rw [meromorphicOrderAt_congr (hEq x)]
      simpa only [MeromorphicFunction.order_apply] using hf x
    · intro hx
      have hnonneg : (0 : WithTop ℤ) ≤ ((-D x : ℤ) : WithTop ℤ) := by
        exact_mod_cast neg_nonneg.mpr hx
      have hfinite : f x ≠ (∞ : OnePoint ℂ) :=
        MeromorphicFunction.order_nonneg_iff.mp (hnonneg.trans (hf x))
      exact (f.contMDiffAt_finitePart hfinite).congr_of_eventuallyEq <|
        eventuallyEq_nhds_of_eventuallyEq_nhdsNE (hEq x)
          (Set.indicator_of_mem (s := {x | D x ≤ 0}) hx f.finitePart)
    · intro hx
      exact Set.indicator_of_notMem (s := {x | D x ≤ 0}) (not_le.mpr hx) _
  let s : divisorSections D ⊤ :=
    ⟨g ∘ Subtype.val, comp_val_mem_divisorSections (fun x _ ↦ hg x)⟩
  refine ⟨s, ?_⟩
  exact (MeromorphicFunction.ofMeromorphic_congr
    (fun x ↦ (isDivisorSectionAt s x).meromorphicAt) f.meromorphicAt_finitePart hEq).trans
      (MeromorphicFunction.ofMeromorphic_finitePart f)

/-- The images of the section spaces grow with the divisor: if `D ≤ E`, every meromorphic
function satisfying the bound of `𝒪(D)` satisfies that of `𝒪(E)`. -/
theorem range_toMeromorphic_mono {D E : WeilDivisor X} (h : D ≤ E) :
    (toMeromorphic D).range ≤ (toMeromorphic E).range := fun f hf ↦ by
  rw [mem_range_toMeromorphic_iff] at hf ⊢
  exact fun y ↦ le_trans (WithTop.coe_le_coe.2 (neg_le_neg (Finsupp.le_def.1 h y))) (hf y)

/-- **A jump in the section spaces gives a function of exact pole order.** If adding a point `x`
to a divisor `D` raises the dimension of the global sections, then some meromorphic function
satisfies the bound of `𝒪(D + [x])` and has order exactly `-(D(x) + 1)` at `x`. -/
theorem _root_.TauCeti.RiemannSurface.MeromorphicFunction.exists_order_eq_neg_of_finrank_lt
    {D : WeilDivisor X} {x : X}
    (h : Module.finrank ℂ (divisorSections D ⊤) <
      Module.finrank ℂ (divisorSections (D + WeilDivisor.ofPoint x) ⊤)) :
    ∃ f : MeromorphicFunction X,
      MeromorphicFunction.order x f = ((-(D x + 1) : ℤ) : WithTop ℤ) ∧
      ∀ y, ((-(D + WeilDivisor.ofPoint x) y : ℤ) : WithTop ℤ) ≤ MeromorphicFunction.order y f := by
  set E := D + WeilDivisor.ofPoint x
  -- The image of `L(D)` lies in that of `L(D + [x])`, which is finite-dimensional, and does not
  -- contain it, since it has smaller dimension.
  have hDE : (toMeromorphic D).range ≤ (toMeromorphic E).range :=
    range_toMeromorphic_mono (le_add_of_nonneg_right (WeilDivisor.ofPoint_nonneg x))
  have : Module.Finite ℂ (divisorSections E ⊤) := Module.finite_of_finrank_pos (by omega)
  have := Submodule.finiteDimensional_of_le hDE
  have hlt : ¬(toMeromorphic E).range ≤ (toMeromorphic D).range := fun hle ↦ by
    have := Submodule.finrank_mono hle
    rw [LinearMap.finrank_range_of_inj (toMeromorphic_injective D),
      LinearMap.finrank_range_of_inj (toMeromorphic_injective E)] at this
    omega
  obtain ⟨f, hfE, hfD⟩ := IsConcreteLE.not_le_iff_exists.mp hlt
  rw [mem_range_toMeromorphic_iff] at hfE hfD
  push Not at hfD
  obtain ⟨y, hy⟩ := hfD
  refine ⟨f, ?_, hfE⟩
  -- The bounds of `L(D)` and `L(D + [x])` differ only at `x`, so `f` violates the first there,
  -- which pins its order at `x` to `-(D(x) + 1)`.
  have hyE := hfE y
  simp only [E, Finsupp.add_apply] at hyE
  rcases eq_or_ne y x with rfl | hyx
  · have hp : WeilDivisor.ofPoint y y = 1 := WeilDivisor.coeff_ofPoint_self y
    rw [hp] at hyE
    induction h : MeromorphicFunction.order y f using WithTop.recTopCoe with
    | top => rw [h] at hy; exact absurd hy not_top_lt
    | coe n =>
      rw [h] at hy hyE
      norm_cast at hy hyE ⊢
      omega
  · have hp : WeilDivisor.ofPoint x y = 0 := WeilDivisor.coeff_ofPoint_of_ne hyx
    exact absurd hy (not_lt.mpr (by simpa [hp] using hyE))

/-- A section space of dimension greater than one contains a section whose meromorphic
image is not constant. No effectiveness assumption on the divisor is needed. -/
theorem exists_toMeromorphic_notMem_range_algebraMap (D : WeilDivisor X)
    (hD : 1 < Module.finrank ℂ (divisorSections D ⊤)) :
    ∃ f : divisorSections D ⊤,
      toMeromorphic D f ∉ Set.range (algebraMap ℂ (MeromorphicFunction X)) := by
  by_contra! h
  have hle : (toMeromorphic D).range ≤
      (Algebra.linearMap ℂ (MeromorphicFunction X)).range := by
    rintro _ ⟨f, rfl⟩
    simpa only [LinearMap.mem_range, Algebra.linearMap_apply, Set.mem_range] using h f
  have hdim := Submodule.finrank_mono hle
  rw [LinearMap.finrank_range_of_inj (toMeromorphic_injective D),
    LinearMap.finrank_range_of_inj (FaithfulSMul.algebraMap_injective ℂ (MeromorphicFunction X)),
    Module.finrank_self] at hdim
  omega

/-- On a compact connected Riemann surface a divisor of negative degree has no nonzero global
sections: the divisor of the meromorphic image of a nonzero section is bounded below by `-D` and
has degree zero. -/
theorem eq_zero_of_degree_neg [CompactSpace X] [T2Space X] (hD : WeilDivisor.degree D < 0)
    (f : divisorSections D ⊤) : f = 0 := by
  by_contra hf
  have hne : toMeromorphic D f ≠ 0 := (map_ne_zero_iff _ (toMeromorphic_injective D)).2 hf
  let u : Additive (MeromorphicFunction X)ˣ := Additive.ofMul (Units.mk0 _ hne)
  have hle : -D ≤ (MeromorphicFunction.orderSystem X).principalDivisor u := fun x ↦ by
    rw [Finsupp.neg_apply, ← WithTop.coe_le_coe]
    exact (neg_le_order_toMeromorphic f x).trans_eq
      (MeromorphicFunction.coe_coeff_principalDivisor_orderSystem u x).symm
  have h := WeilDivisor.degree_nonneg (sub_nonneg.2 hle)
  rw [map_sub, MeromorphicFunction.degree_principalDivisor, map_neg] at h
  omega

end divisorSections

section DegreeNeg

variable [CompactSpace X] [T2Space X] {D : WeilDivisor X}

/-- On a compact connected Riemann surface, `H⁰(𝒪(D))` vanishes when `deg D < 0`. -/
theorem isZero_divisorSheaf_globalSections_of_degree_neg (hD : WeilDivisor.degree D < 0) :
    Limits.IsZero ((divisorSheaf D).obj.obj (op ⊤)) :=
  ModuleCat.isZero_iff_subsingleton.2 ⟨fun f g ↦ (divisorSheafSectionsEquiv D ⊤).injective <| by
    rw [divisorSections.eq_zero_of_degree_neg hD (divisorSheafSectionsEquiv D ⊤ f),
      divisorSections.eq_zero_of_degree_neg hD (divisorSheafSectionsEquiv D ⊤ g)]⟩

end DegreeNeg

/-- A dimension bound on global divisor sections produces an actual finite holomorphic map
from a compact connected Riemann surface to the sphere. The order of its affine part is bounded
below by `-D`, so all poles lie among the points where `D` is positive. -/
theorem exists_finiteHolomorphicMap_of_one_lt_finrank_divisorSections [CompactSpace X]
    (D : WeilDivisor X) (hD : 1 < Module.finrank ℂ (divisorSections D ⊤)) :
    ∃ F : FiniteHolomorphicMap X (OnePoint ℂ),
      ∀ x, ((-D x : ℤ) : WithTop ℤ) ≤
        meromorphicOrderAt (fun y ↦ OnePoint.affineChart (F y)) x := by
  obtain ⟨s, hs⟩ := divisorSections.exists_toMeromorphic_notMem_range_algebraMap D hD
  let f := divisorSections.toMeromorphic D s
  have hne := f.exists_apply_ne_of_notMem_range_algebraMap hs
  refine ⟨FiniteHolomorphicMap.ofMDifferentiable f.mdifferentiable hne, ?_⟩
  simpa only [FiniteHolomorphicMap.coe_ofMDifferentiable,
    ← MeromorphicFunction.finitePart_def, MeromorphicFunction.order_apply] using
    divisorSections.neg_le_order_toMeromorphic s

/-- A divisor of negative degree has no nonzero global sections: a nonzero section is a meromorphic
function whose principal divisor is at least `-D`, and principal divisors have degree zero. -/
theorem finrank_divisorSheaf_eq_zero_of_degree_neg [CompactSpace X] [T2Space X]
    {D : WeilDivisor X} (hD : WeilDivisor.degree D < 0) :
    Module.finrank ℂ ((divisorSheaf D).obj.obj (Opposite.op ⊤)) = 0 :=
  have := ModuleCat.isZero_iff_subsingleton.1 (isZero_divisorSheaf_globalSections_of_degree_neg hD)
  Module.finrank_zero_of_subsingleton

/-- **A second section of `𝒪(x)` gives a degree-one map to `ℙ¹`.** If the global sections of the
divisor of a point `x` on a compact connected Riemann surface have dimension greater than one,
there is a finite holomorphic map `X → ℙ¹` of degree one. -/
theorem exists_finiteHolomorphicMap_degree_eq_one_of_one_lt_finrank_divisorSections_ofPoint
    [CompactSpace X] [T2Space X] {x : X}
    (hx : 1 < Module.finrank ℂ (divisorSections (WeilDivisor.ofPoint x) ⊤)) :
    ∃ F : FiniteHolomorphicMap X (OnePoint ℂ), degree F = 1 := by
  obtain ⟨F, hF⟩ := exists_finiteHolomorphicMap_of_one_lt_finrank_divisorSections _ hx
  refine ⟨F, ?_⟩
  have hle := F.degree_le_degree_of_neg_le_meromorphicOrderAt (WeilDivisor.ofPoint_nonneg x) hF
  rw [WeilDivisor.degree_ofPoint] at hle
  have := degree_pos F
  omega

end TauCeti.RiemannSurface

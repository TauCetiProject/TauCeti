/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.JHolomorphic.CanonicalCycle
public import TauCeti.Geometry.Symplectic.JHolomorphic.PointConfigurationCount
public import TauCeti.Geometry.Symplectic.Manifold.EmbeddedCurve

/-!
# Exceptional spheres and good classes of an almost complex structure

Let `X` be a closed symplectic four-manifold with canonical class `κ`, intersection form `B` on
`H₂(X; ℤ)` and a compatible almost complex structure `J`. Taubes's count of embedded
`J`-holomorphic curves treats the embedded `J`-holomorphic spheres of square `-1` separately: as
ordinary components of configurations they are counted with multiplicity one only, so the count
in a class `A` with `A · [S] < -1` for such a sphere `S` vanishes. Taubes calls `A` *good* for `J`
when `A · [S] ≥ -1` for every such sphere; for `A` Poincaré dual to a class `e ∈ H²(X; ℤ)`, this
is `⟨e, [S]⟩ ≥ -1`. Both notions refer to the same `J` as the count.

This file defines them on the embedded pseudoholomorphic images of
`TauCeti.Geometry.Symplectic.Manifold.EmbeddedCurve`, for an intersection form
`B : TauCeti.IntersectionForm X`.

* `TauCeti.IntersectionForm X`, the `ℤ`-bilinear forms on `H₂(X; ℤ)` for the `ℤ`-module structure
  `AddCommGroup.toIntModule`, as in the abstract counts and cycles over an additive group which
  this file specializes.
* `TauCeti.exceptionalImages J B κ`, the set `Exc_J`: the embedded `J`-holomorphic images `S`
  whose class is exceptional, `[S] · [S] = κ · [S] = -1`. An embedded curve of genus `g` satisfies
  the adjunction formula `[S] · [S] + κ · [S] = 2 g - 2`, and under it these images are exactly the
  embedded spheres of square `-1`
  (`TauCeti.EmbeddedPseudoholomorphicCurve.range_mem_exceptionalImages_iff`). For a generic `J`,
  every embedded image of negative square is one of them
  (`TauCeti.mem_exceptionalImages_of_apply_self_neg`).
* `TauCeti.IsGoodClass J B κ A`, the predicate `good_J(A)`: `A · [S] ≥ -1` for every
  `S ∈ exceptionalImages J B κ`.

Three consequences follow from the intersection algebra of the configuration counts and of
canonical cycles.

* **Bad classes have zero count.** If `A` is not good, the weighted count of configurations in
  class `A`, with or without point constraints, vanishes, provided the other candidates meet
  every exceptional image nonnegatively (positivity of intersections) and exceptional images are
  weighted with multiplicity one only (`TauCeti.configurationCount_eq_zero_of_not_isGoodClass`,
  `TauCeti.pointConfigurationCount_eq_zero_of_not_isGoodClass`).
* **Canonical cycles contain every exceptional image.** Let `D = ∑ m_i C_i` be a canonical cycle
  of images (`TauCeti.IsCanonicalCycle`), such as the cycle Taubes assembles from the
  Seiberg–Witten solutions of a class `e` and of its conjugate `κ - e`, and suppose its
  components meet every exceptional image other than themselves nonnegatively. Since
  `κ · [S] = -1 < 0`, every exceptional image is a component of `D`
  (`TauCeti.IsCanonicalCycle.exists_eq_of_mem_exceptionalImages`), occurring with multiplicity
  one (`TauCeti.IsCanonicalCycle.mult_eq_one_of_mem_exceptionalImages`). Hence `Exc_J` is finite
  (`TauCeti.IsCanonicalCycle.finite_exceptionalImages`), and every subcycle of `D`, in particular
  the cycle of `e`, is a good class (`TauCeti.IsCanonicalCycle.isGoodClass_sum`).
* **Good classes satisfy the exceptional-sphere condition of good cycles.** If `A` is good and
  every candidate image of negative square is exceptional, the components of a point
  configuration in class `A` through `d(A) / 2` generic points form a good cycle
  (`TauCeti.isGoodCycle_of_mem_pointConfigurations_of_isGoodClass`), so the structure theorem
  for `TauCeti.IsGoodCycle` applies to them.

As in the abstract counts, the intersection form, the canonical class, adjunction, regularity and
positivity of intersections are inputs here; the geometric theorems supplying them are separate.

## Main definitions

* `TauCeti.IntersectionForm`: the type of intersection forms on `H₂(X; ℤ)`.
* `TauCeti.IntersectionForm.IsSymm`: symmetry of an intersection form.
* `TauCeti.exceptionalImages`: the embedded images in exceptional classes.
* `TauCeti.IsGoodClass`: the classes at least `-1` on every exceptional image.

## References

* C. H. Taubes, *Counting pseudo-holomorphic submanifolds in dimension 4*, J. Differential Geom.
  44 (1996), 818–893.
* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
* D. McDuff, *Lectures on Gromov invariants for symplectic 4-manifolds*, arXiv:dg-ga/9606005.
-/

public section

open LinearMap (BilinForm)
open Set
open scoped Manifold ContDiff

namespace TauCeti

/-- The `ℤ`-bilinear forms on `H₂(X; ℤ)`, such as the intersection form of a closed oriented
four-manifold `X`. They are bilinear for the `ℤ`-module structure `AddCommGroup.toIntModule`, the
one the abstract counts and cycles over an additive group use, rather than for the `ModuleCat ℤ`
structure of `secondHomology X`, which agrees with it only propositionally. -/
abbrev IntersectionForm (X : Type) [TopologicalSpace X] : Type :=
  @BilinForm ℤ _ (secondHomology X) _ (AddCommGroup.toIntModule _)

/-- An intersection form `B : TauCeti.IntersectionForm X` is **symmetric**,
`LinearMap.BilinForm.IsSymm` for the `ℤ`-module structure `AddCommGroup.toIntModule`. -/
abbrev IntersectionForm.IsSymm {X : Type} [TopologicalSpace X] (B : IntersectionForm X) : Prop :=
  @LinearMap.BilinForm.IsSymm ℤ (secondHomology X) _ _ (AddCommGroup.toIntModule _) B

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {X : Type} [TopologicalSpace X] [ChartedSpace H X]
  [IsManifold I ∞ X]

section Defs

variable (J : SmoothAlmostComplexStructure I X) (B : IntersectionForm X)
  (κ : secondHomology X)

/-- The **exceptional images** `Exc_J` of an almost complex structure `J`, for the intersection
form `B` and canonical class `κ`: the embedded `J`-holomorphic images `S` whose class is
exceptional, `[S] · [S] = -1` and `κ · [S] = -1`. Given the adjunction formula for embedded
curves, these are exactly the embedded `J`-holomorphic spheres of square `-1`
(`TauCeti.EmbeddedPseudoholomorphicCurve.range_mem_exceptionalImages_iff`). -/
def exceptionalImages : Set (Set X) :=
  {S | IsEmbeddedPseudoholomorphicImage J S ∧
    B (embeddedCurveClass J S) (embeddedCurveClass J S) = -1 ∧
      B κ (embeddedCurveClass J S) = -1}

/-- A class `A ∈ H₂(X; ℤ)` is **good** for `J` when it is at least `-1` on every exceptional
image: `A · [S] ≥ -1` for every `S ∈ exceptionalImages J B κ`. -/
def IsGoodClass (A : secondHomology X) : Prop :=
  ∀ S ∈ exceptionalImages J B κ, -1 ≤ B A (embeddedCurveClass J S)

end Defs

variable {J : SmoothAlmostComplexStructure I X} {B : IntersectionForm X}
  {κ A : secondHomology X} {S : Set X}

@[simp]
theorem mem_exceptionalImages :
    S ∈ exceptionalImages J B κ ↔ IsEmbeddedPseudoholomorphicImage J S ∧
      B (embeddedCurveClass J S) (embeddedCurveClass J S) = -1 ∧
        B κ (embeddedCurveClass J S) = -1 :=
  Iff.rfl

/-- An exceptional image is an embedded pseudoholomorphic image. -/
theorem isEmbeddedPseudoholomorphicImage_of_mem_exceptionalImages
    (hS : S ∈ exceptionalImages J B κ) : IsEmbeddedPseudoholomorphicImage J S :=
  hS.1

/-- An exceptional image has square `-1`. -/
theorem apply_self_eq_neg_one_of_mem_exceptionalImages (hS : S ∈ exceptionalImages J B κ) :
    B (embeddedCurveClass J S) (embeddedCurveClass J S) = -1 :=
  hS.2.1

/-- An exceptional image pairs with the canonical class to `-1`. -/
theorem apply_canonical_eq_neg_one_of_mem_exceptionalImages (hS : S ∈ exceptionalImages J B κ) :
    B κ (embeddedCurveClass J S) = -1 :=
  hS.2.2

theorem isGoodClass_iff :
    IsGoodClass J B κ A ↔ ∀ S ∈ exceptionalImages J B κ, -1 ≤ B A (embeddedCurveClass J S) :=
  Iff.rfl

/-- A class is bad exactly when it pairs below `-1` with some exceptional image. -/
theorem not_isGoodClass_iff :
    ¬IsGoodClass J B κ A ↔ ∃ S ∈ exceptionalImages J B κ, B A (embeddedCurveClass J S) < -1 := by
  simp only [isGoodClass_iff, not_forall, not_le, exists_prop]

/-- The class of the empty configuration is good. -/
@[simp]
theorem isGoodClass_zero : IsGoodClass J B κ 0 := fun _ _ ↦ by simp

/-! ### Exceptional images as spheres -/

/-- **Exceptional images are the embedded spheres of square `-1`.** If an embedded
pseudoholomorphic curve `C` of genus `g` satisfies the adjunction formula
`[C] · [C] + κ · [C] = 2 g - 2`, its image is exceptional exactly when `g = 0` and
`[C] · [C] = -1`. -/
theorem EmbeddedPseudoholomorphicCurve.range_mem_exceptionalImages_iff [T2Space X]
    (C : EmbeddedPseudoholomorphicCurve J) {g : ℕ}
    (hadj : B C.homologyClass C.homologyClass + B κ C.homologyClass = 2 * g - 2) :
    range C.toFun ∈ exceptionalImages J B κ ↔ g = 0 ∧ B C.homologyClass C.homologyClass = -1 := by
  simp only [mem_exceptionalImages, embeddedCurveClass_range,
    C.isEmbeddedPseudoholomorphicImage, true_and]
  omega

/-- **Embedded images of negative square are exceptional.** An embedded image whose class
satisfies adjunction and the index bound of a regular almost complex structure, and has negative
square, is exceptional. -/
theorem mem_exceptionalImages_of_apply_self_neg (hS : IsEmbeddedPseudoholomorphicImage J S)
    {g δ : ℕ} (hreg : IsRegularSimpleCurve B κ (embeddedCurveClass J S) g δ)
    (hneg : B (embeddedCurveClass J S) (embeddedCurveClass J S) < 0) :
    S ∈ exceptionalImages J B κ :=
  ⟨hS, hreg.apply_self_eq_neg_one_of_apply_self_neg hneg,
    hreg.apply_canonical_eq_neg_one_of_apply_self_neg hneg⟩

/-! ### Vanishing of the count in a bad class -/

section BadClass

variable {R : Type*} [CommSemiring R] {r : Set X → Set X → Prop} {w : Set X → ℕ → R}
  {s : Set (Set X)}

/-- **The count vanishes in a bad class.** Suppose that the candidate images meet every
exceptional image other than themselves nonnegatively, as positivity of intersections gives, and
that an exceptional image is counted with multiplicity one only, `w S k = 0` for `k ≥ 2`. If `A`
is not good, the weighted count of configurations in class `A` vanishes. -/
theorem configurationCount_eq_zero_of_not_isGoodClass
    (hpos : ∀ S ∈ exceptionalImages J B κ, ∀ c ∈ s, c ≠ S →
      0 ≤ B (embeddedCurveClass J c) (embeddedCurveClass J S))
    (hw : ∀ S ∈ exceptionalImages J B κ, ∀ k, 2 ≤ k → w S k = 0)
    (hA : ¬IsGoodClass J B κ A) :
    configurationCount r (embeddedCurveClass J) w s A = 0 := by
  obtain ⟨S, hS, hlt⟩ := not_isGoodClass_iff.1 hA
  exact configurationCount_eq_zero_of_apply_lt_neg_one (hpos S hS)
    (apply_self_eq_neg_one_of_mem_exceptionalImages hS).ge (hw S hS) hlt

/-- **The count through points vanishes in a bad class**, under the hypotheses of
`TauCeti.configurationCount_eq_zero_of_not_isGoodClass`. -/
theorem pointConfigurationCount_eq_zero_of_not_isGoodClass {P : Type*} {pts : Set X → Finset P}
    (hpos : ∀ S ∈ exceptionalImages J B κ, ∀ c ∈ s, c ≠ S →
      0 ≤ B (embeddedCurveClass J c) (embeddedCurveClass J S))
    (hw : ∀ S ∈ exceptionalImages J B κ, ∀ k, 2 ≤ k → w S k = 0)
    (hA : ¬IsGoodClass J B κ A) :
    pointConfigurationCount r (embeddedCurveClass J) pts w s A = 0 := by
  obtain ⟨S, hS, hlt⟩ := not_isGoodClass_iff.1 hA
  exact pointConfigurationCount_eq_zero_of_apply_lt_neg_one (hpos S hS)
    (apply_self_eq_neg_one_of_mem_exceptionalImages hS).ge (hw S hS) hlt

end BadClass

/-! ### Good classes and good cycles -/

/-- **Point configurations in a good class are good cycles.** Let `s` be a set of candidate
images such that compatible images meet nonnegatively, the generic points on each image `c` cut
its virtual dimension down to a nonnegative dimension, `2 |pts c| ≤ d(c)`, and every image of
negative square is exceptional, as `TauCeti.mem_exceptionalImages_of_apply_self_neg` gives for a
generic `J`. If `A` is good and the number of points is `d(A) / 2`, the components of a point
configuration in class `A` form a good cycle. The structure theorem for good cycles then makes
them homologically disjoint and assigns each point to exactly one of them. -/
theorem isGoodCycle_of_mem_pointConfigurations_of_isGoodClass {P : Type*} [Fintype P]
    {pts : Set X → Finset P} {r : Set X → Set X → Prop} {s : Set (Set X)} {l : Set X →₀ ℕ}
    (hint : ∀ c ∈ s, ∀ d ∈ s, r c d →
      0 ≤ B (embeddedCurveClass J c) (embeddedCurveClass J d))
    (hind : ∀ c ∈ s, 2 * ((pts c).card : ℤ) ≤
      B (embeddedCurveClass J c) (embeddedCurveClass J c) - B κ (embeddedCurveClass J c))
    (hexc : ∀ c ∈ s, B (embeddedCurveClass J c) (embeddedCurveClass J c) < 0 →
      c ∈ exceptionalImages J B κ)
    (hA : IsGoodClass J B κ A) (hl : l ∈ pointConfigurations r (embeddedCurveClass J) pts s A)
    (hdim : B A A - B κ A = 2 * Fintype.card P) :
    IsGoodCycle B κ A (fun c : l.support ↦ embeddedCurveClass J c) (fun c ↦ l c) 0
      (fun c ↦ pts c) :=
  isGoodCycle_of_mem_pointConfigurations hint hind (fun c hc hneg ↦ hA c (hexc c hc hneg)) hl
    hdim

/-! ### Canonical cycles -/

section CanonicalCycle

variable {ι : Type*} [Fintype ι] {C : ι → Set X} {m : ι → ℕ}

/-- **Every exceptional image is a component of a canonical cycle.** Let `∑ m i • [C i]` be a
canonical cycle of images whose components other than the exceptional image `S` meet it
nonnegatively. Since `S` pairs negatively with the canonical class, it is one of the
components. -/
theorem IsCanonicalCycle.exists_eq_of_mem_exceptionalImages
    (h : IsCanonicalCycle B κ (embeddedCurveClass J ∘ C) m)
    (hpos : ∀ i, C i ≠ S → 0 ≤ B (embeddedCurveClass J (C i)) (embeddedCurveClass J S))
    (hS : S ∈ exceptionalImages J B κ) : ∃ i, C i = S := by
  by_contra hne
  push Not at hne
  have hκ : B κ (embeddedCurveClass J S) < 0 := by
    rw [apply_canonical_eq_neg_one_of_mem_exceptionalImages hS]
    norm_num
  -- The canonical cycle has a component of the same class as `S`, which is not `S` itself.
  obtain ⟨i, hi⟩ := h.exists_eq_of_apply_canonical_neg hκ fun i ↦ .inr (hpos i (hne i))
  have := hpos i (hne i)
  rw [Function.comp_apply] at hi
  rw [hi, apply_self_eq_neg_one_of_mem_exceptionalImages hS] at this
  omega

/-- An exceptional image occurs with multiplicity one in a canonical cycle. -/
theorem IsCanonicalCycle.mult_eq_one_of_mem_exceptionalImages (hB : B.IsSymm)
    (h : IsCanonicalCycle B κ (embeddedCurveClass J ∘ C) m) {i : ι}
    (hi : C i ∈ exceptionalImages J B κ) : m i = 1 :=
  h.mult_eq_one_of_apply_self_neg hB <| by
    rw [Function.comp_apply, apply_self_eq_neg_one_of_mem_exceptionalImages hi]
    norm_num

/-- **Finiteness of the exceptional images.** If the images of a canonical cycle meet every
exceptional image other than themselves nonnegatively, there are finitely many exceptional
images. -/
theorem IsCanonicalCycle.finite_exceptionalImages
    (h : IsCanonicalCycle B κ (embeddedCurveClass J ∘ C) m)
    (hpos : ∀ S ∈ exceptionalImages J B κ, ∀ i, C i ≠ S →
      0 ≤ B (embeddedCurveClass J (C i)) (embeddedCurveClass J S)) :
    (exceptionalImages J B κ).Finite :=
  (finite_range C).subset fun _ hS ↦ h.exists_eq_of_mem_exceptionalImages (hpos _ hS) hS

/-- **Subcycles of a canonical cycle are good.** If the images of a canonical cycle
`∑ m i • [C i]` meet every exceptional image other than themselves nonnegatively, then every
subcycle `∑ a i • [C i]` with `a ≤ m` is a good class: it pairs with each exceptional image to
at least `-1`. -/
theorem IsCanonicalCycle.isGoodClass_sum (hB : B.IsSymm)
    (h : IsCanonicalCycle B κ (embeddedCurveClass J ∘ C) m)
    (hpos : ∀ S ∈ exceptionalImages J B κ, ∀ i, C i ≠ S →
      0 ≤ B (embeddedCurveClass J (C i)) (embeddedCurveClass J S))
    {a : ι → ℕ} (ha : ∀ i, a i ≤ m i) :
    IsGoodClass J B κ (∑ i, a i • embeddedCurveClass J (C i)) := by
  intro S hS
  have hκ : B κ (embeddedCurveClass J S) < 0 := by
    rw [apply_canonical_eq_neg_one_of_mem_exceptionalImages hS]
    norm_num
  rcases h.apply_sum_eq_zero_or_eq_neg_one hB ha hκ
    (fun i ↦ (eq_or_ne (C i) S).imp (congrArg (embeddedCurveClass J)) (hpos S hS i)) with
    h0 | h1
  · simp only [Function.comp_apply] at h0
    omega
  · simp only [Function.comp_apply] at h1
    omega

end CanonicalCycle

end TauCeti

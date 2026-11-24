/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.FiberProduct.Associativity
public import TauCeti.Geometry.Manifold.Groupoid.Basic
import TauCeti.Geometry.Manifold.SmoothEmbedding.LeftInverse
import TauCeti.Geometry.Manifold.Submersion.LocalDiffeomorph

/-!
# Unit degeneracies, composable-pair inversion, and composable triples of a Lie groupoid

For a Lie groupoid `C` modelled on `I` (objects) and `J` (total arrows), this file develops the
smooth geometry of the degree-2 and degree-3 levels of its simplicial nerve:

* **Unit degeneracies and pair inversion on composable pairs**: the left, right, and diagonal unit
  sections `leftUnitPair` (`b ↦ (1_{s(b)}, b)`), `rightUnitPair` (`a ↦ (a, 1_{t(a)})`), and
  `unitPair` (`x ↦ (1_x, 1_x)`) are smooth embeddings into `ComposablePairs C`, and reversing and
  inverting a composable pair `(a, b) ↦ (b⁻¹, a⁻¹)` is an involutive `C^∞` diffeomorphism
  (`inverseComposablePairsDiffeomorph`) compatible with groupoid composition.
* **Iterated transverse pullbacks of composable triples and smooth associativity**: both
  parenthesizations `ComposableTriplesLeft C` (`((a, b), c)`) and `ComposableTriplesRight C`
  (`(a, (b, c))`) carry canonical transverse fibre-product smooth atlases with universal properties
  and submersive factor projections, and regrouping is a `C^∞` diffeomorphism
  (`composableTriplesAssocDiffeomorph`).
* **Simplicial face maps**: all four simplicial face maps `triplesFace₀`..`triplesFace₃` from
  composable triples to composable pairs are smooth, with the outer faces `triplesFace₀` and
  `triplesFace₃` smooth submersions and the inner faces satisfying `comp ∘ d₁ = comp ∘ d₂`
  (`comp_triplesFace₁_eq_comp_triplesFace₂`).

## Main definitions

* `TauCeti.IsLieGroupoid.ComposablePairs`, `TauCeti.IsLieGroupoid.leftUnitPair`,
  `TauCeti.IsLieGroupoid.rightUnitPair`, `TauCeti.IsLieGroupoid.unitPair`.
* `TauCeti.IsLieGroupoid.inverseComposablePairsDiffeomorph`: involutive diffeomorphism
  `(a, b) ↦ (b⁻¹, a⁻¹)` of composable pairs.
* `TauCeti.IsLieGroupoid.ComposableTriplesLeft`, `TauCeti.IsLieGroupoid.ComposableTriplesRight`,
  `TauCeti.IsLieGroupoid.composableTriplesLeftChartedSpace`,
  `TauCeti.IsLieGroupoid.composableTriplesRightChartedSpace`,
  `TauCeti.IsLieGroupoid.composableTriplesAssocDiffeomorph`.
* `TauCeti.IsLieGroupoid.triplesFace₀`, `TauCeti.IsLieGroupoid.triplesFace₁`,
  `TauCeti.IsLieGroupoid.triplesFace₂`, `TauCeti.IsLieGroupoid.triplesFace₃`.

## References

* K. C. H. Mackenzie, *General Theory of Lie Groupoids and Lie Algebroids*, London Math. Soc.
  Lecture Note Ser. 213, Cambridge University Press (2005), Section 1.1.
* I. Moerdijk and J. Mrčun, *Introduction to Foliations and Lie Groupoids*, Cambridge Stud. Adv.
  Math. 91, Cambridge University Press (2003), Section 5.1.
-/

public section

noncomputable section

open CategoryTheory Function Module
open scoped Manifold ContDiff

namespace TauCeti.IsLieGroupoid

/-- Composable pairs of total arrows in categorical order: the target of the first arrow equals the
source of the second. -/
abbrev ComposablePairs (C : Type*) [Quiver C] : Type _ :=
  {p : Quiver.Total C × Quiver.Total C // p.1.right = p.2.left}

/-- Left unit degeneracy `b ↦ (1_{s(b)}, b)` into composable pairs. -/
abbrev leftUnitPair {C : Type*} [Category C] (b : Quiver.Total C) : ComposablePairs C :=
  ⟨(⟨b.left, b.left, 𝟙 b.left⟩, b), rfl⟩

/-- Right unit degeneracy `a ↦ (a, 1_{t(a)})` into composable pairs. -/
abbrev rightUnitPair {C : Type*} [Category C] (a : Quiver.Total C) : ComposablePairs C :=
  ⟨(a, ⟨a.right, a.right, 𝟙 a.right⟩), rfl⟩

/-- Diagonal unit degeneracy `x ↦ (1_x, 1_x)` from objects into composable pairs. -/
abbrev unitPair {C : Type*} [Category C] (x : C) : ComposablePairs C :=
  ⟨(⟨x, x, 𝟙 x⟩, ⟨x, x, 𝟙 x⟩), rfl⟩

@[simp]
theorem leftUnitPair_fst {C : Type*} [Category C] (b : Quiver.Total C) :
    (leftUnitPair b).val.1 = ⟨b.left, b.left, 𝟙 b.left⟩ :=
  (rfl)

@[simp]
theorem leftUnitPair_snd {C : Type*} [Category C] (b : Quiver.Total C) :
    (leftUnitPair b).val.2 = b :=
  (rfl)

@[simp]
theorem rightUnitPair_fst {C : Type*} [Category C] (a : Quiver.Total C) :
    (rightUnitPair a).val.1 = a :=
  (rfl)

@[simp]
theorem rightUnitPair_snd {C : Type*} [Category C] (a : Quiver.Total C) :
    (rightUnitPair a).val.2 = ⟨a.right, a.right, 𝟙 a.right⟩ :=
  (rfl)

@[simp]
theorem unitPair_fst {C : Type*} [Category C] (x : C) :
    (unitPair x).val.1 = ⟨x, x, 𝟙 x⟩ :=
  (rfl)

@[simp]
theorem unitPair_snd {C : Type*} [Category C] (x : C) :
    (unitPair x).val.2 = ⟨x, x, 𝟙 x⟩ :=
  (rfl)

/-- Composing the arrows of `leftUnitPair b` recovers `b`. -/
theorem comp_leftUnitPair {C : Type*} [Category C] (b : Quiver.Total C) :
    (leftUnitPair b).val.1.comp (leftUnitPair b).val.2 (leftUnitPair b).property = b :=
  b.unit_comp

/-- Composing the arrows of `rightUnitPair a` recovers `a`. -/
theorem comp_rightUnitPair {C : Type*} [Category C] (a : Quiver.Total C) :
    (rightUnitPair a).val.1.comp (rightUnitPair a).val.2 (rightUnitPair a).property = a :=
  a.comp_unit

/-- Composing the arrows of `unitPair x` recovers the identity arrow `1_x`. -/
theorem comp_unitPair {C : Type*} [Category C] (x : C) :
    (unitPair x).val.1.comp (unitPair x).val.2 (unitPair x).property = ⟨x, x, 𝟙 x⟩ :=
  (⟨x, x, 𝟙 x⟩ : Quiver.Total C).unit_comp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] (J : ModelWithCorners ℝ E' H') [J.Boundaryless]
  (C : Type*) [Category C] [IsGroupoid C]
  [TopologicalSpace C] [ChartedSpace H C] [IsManifold I ∞ C]
  [TopologicalSpace (Quiver.Total C)] [ChartedSpace H' (Quiver.Total C)]
  [IsManifold J ∞ (Quiver.Total C)] [IsLieGroupoid I J C]

/-! ### Smooth unit degeneracies and inversion on composable pairs -/

/-- The left unit degeneracy `b ↦ (1_{s(b)}, b)` into composable pairs is smooth. -/
theorem contMDiff_leftUnitPair :
    letI := composablePairsChartedSpace I J C
    ContMDiff J 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) ∞
      (leftUnitPair : Quiver.Total C → ComposablePairs C) :=
  (contMDiff_composablePairs_iff I J C le_rfl).mpr
    ⟨(contMDiff_unit (I := I) (J := J) (C := C)).comp (contMDiff_source I J C), contMDiff_id⟩

/-- The right unit degeneracy `a ↦ (a, 1_{t(a)})` into composable pairs is smooth. -/
theorem contMDiff_rightUnitPair :
    letI := composablePairsChartedSpace I J C
    ContMDiff J 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) ∞
      (rightUnitPair : Quiver.Total C → ComposablePairs C) :=
  (contMDiff_composablePairs_iff I J C le_rfl).mpr
    ⟨contMDiff_id, (contMDiff_unit (I := I) (J := J) (C := C)).comp (contMDiff_target I J C)⟩

/-- The diagonal unit degeneracy `x ↦ (1_x, 1_x)` into composable pairs is smooth. -/
theorem contMDiff_unitPair :
    letI := composablePairsChartedSpace I J C
    ContMDiff I 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) ∞
      (unitPair : C → ComposablePairs C) :=
  letI := composablePairsChartedSpace I J C
  (contMDiff_leftUnitPair I J C).comp (contMDiff_unit (I := I) (J := J) (C := C))

/-- The left unit degeneracy `b ↦ (1_{s(b)}, b)` is a smooth embedding into composable pairs. -/
theorem isSmoothEmbedding_leftUnitPair :
    letI := composablePairsChartedSpace I J C
    Manifold.IsSmoothEmbedding J
      𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) ∞
      (leftUnitPair : Quiver.Total C → ComposablePairs C) := by
  let := composablePairsChartedSpace I J C
  have := isManifold_composablePairs I J C
  exact (contMDiff_leftUnitPair I J C).isSmoothEmbedding_of_leftInverse (by simp)
    ((isSubmersion_snd_composablePairs I J C).contMDiff.of_le (by simp)) fun _ ↦ rfl

/-- The right unit degeneracy `a ↦ (a, 1_{t(a)})` is a smooth embedding into composable pairs. -/
theorem isSmoothEmbedding_rightUnitPair :
    letI := composablePairsChartedSpace I J C
    Manifold.IsSmoothEmbedding J
      𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) ∞
      (rightUnitPair : Quiver.Total C → ComposablePairs C) := by
  let := composablePairsChartedSpace I J C
  have := isManifold_composablePairs I J C
  exact (contMDiff_rightUnitPair I J C).isSmoothEmbedding_of_leftInverse (by simp)
    ((isSubmersion_fst_composablePairs I J C).contMDiff.of_le (by simp)) fun _ ↦ rfl

/-- The diagonal unit degeneracy `x ↦ (1_x, 1_x)` is a smooth embedding of the object manifold into
composable pairs. -/
theorem isSmoothEmbedding_unitPair :
    letI := composablePairsChartedSpace I J C
    Manifold.IsSmoothEmbedding I
      𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) ∞
      (unitPair : C → ComposablePairs C) := by
  let := composablePairsChartedSpace I J C
  have := isManifold_composablePairs I J C
  exact (contMDiff_unitPair I J C).isSmoothEmbedding_of_leftInverse (by simp)
    (((contMDiff_source I J C).comp
      (isSubmersion_fst_composablePairs I J C).contMDiff).of_le (by simp)) fun _ ↦ rfl

/-- Reversing and inverting a composable pair `(a, b) ↦ (b⁻¹, a⁻¹)` is an involutive `C^∞`
diffeomorphism of `ComposablePairs C`. -/
def inverseComposablePairsDiffeomorph :
    letI := composablePairsChartedSpace I J C
    ComposablePairs C ≃ₘ^∞⟮𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ),
      𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ)⟯ ComposablePairs C :=
  letI := composablePairsChartedSpace I J C
  let f : ComposablePairs C → ComposablePairs C := fun p ↦
    ⟨(inverseDiffeomorph I J C p.val.2, inverseDiffeomorph I J C p.val.1),
      (inverseDiffeomorph_right I J C p.val.2).trans
        (p.property.symm.trans (inverseDiffeomorph_left I J C p.val.1).symm)⟩
  have hinv : LeftInverse f f := fun p ↦
    Subtype.ext (by obtain ⟨⟨⟨_, _, _⟩, ⟨_, _, _⟩⟩, _⟩ := p; simp [f])
  have hf : ContMDiff 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ)
      𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) ∞ f :=
    (contMDiff_composablePairs_iff I J C le_rfl).mpr
      ⟨(inverseDiffeomorph I J C).contMDiff.comp
        (isSubmersion_snd_composablePairs I J C).contMDiff,
       (inverseDiffeomorph I J C).contMDiff.comp
        (isSubmersion_fst_composablePairs I J C).contMDiff⟩
  { toFun := f, invFun := f, left_inv := hinv, right_inv := hinv
    contMDiff_toFun := hf, contMDiff_invFun := hf }

@[simp]
theorem inverseComposablePairsDiffeomorph_fst (p : ComposablePairs C) :
    letI := composablePairsChartedSpace I J C
    (inverseComposablePairsDiffeomorph I J C p).val.1 = inverseDiffeomorph I J C p.val.2 :=
  (rfl)

@[simp]
theorem inverseComposablePairsDiffeomorph_snd (p : ComposablePairs C) :
    letI := composablePairsChartedSpace I J C
    (inverseComposablePairsDiffeomorph I J C p).val.2 = inverseDiffeomorph I J C p.val.1 :=
  (rfl)

@[simp]
theorem inverseComposablePairsDiffeomorph_symm :
    letI := composablePairsChartedSpace I J C
    (inverseComposablePairsDiffeomorph I J C).symm = inverseComposablePairsDiffeomorph I J C :=
  (rfl)

/-- Composing the arrows of `inverseComposablePairsDiffeomorph I J C p` gives the inverse of the
composite of `p`. -/
theorem comp_inverseComposablePairsDiffeomorph (p : ComposablePairs C) :
    letI := composablePairsChartedSpace I J C
    (inverseComposablePairsDiffeomorph I J C p).val.1.comp
      (inverseComposablePairsDiffeomorph I J C p).val.2
      (inverseComposablePairsDiffeomorph I J C p).property =
      inverseDiffeomorph I J C (p.val.1.comp p.val.2 p.property) := by
  let := composablePairsChartedSpace I J C
  exact ((Quiver.Total.comp_congr (inverseDiffeomorph_apply I J C p.val.2)
    (inverseDiffeomorph_apply I J C p.val.1) _ p.property.symm).trans
    (p.val.1.inv_comp p.val.2 p.property).symm).trans
    (inverseDiffeomorph_apply I J C (p.val.1.comp p.val.2 p.property)).symm

/-! ### Composable triples and smooth associativity -/

/-- Left-parenthesized composable triples `((a, b), c)` with `a.right = b.left` and
`b.right = c.left`. -/
abbrev ComposableTriplesLeft (C : Type*) [Quiver C] : Type _ :=
  {p : ComposablePairs C × Quiver.Total C // p.1.val.2.right = p.2.left}

/-- Right-parenthesized composable triples `(a, (b, c))` with `b.right = c.left` and
`a.right = b.left`. -/
abbrev ComposableTriplesRight (C : Type*) [Quiver C] : Type _ :=
  {p : Quiver.Total C × ComposablePairs C // p.1.right = p.2.val.1.left}

/-- Euclidean model space for left-parenthesized composable triples. -/
abbrev ComposableTriplesLeftModel (E E' : Type*) [AddCommGroup E] [Module ℝ E]
    [AddCommGroup E'] [Module ℝ E'] : Type :=
  Fin (finrank ℝ (Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) +
    finrank ℝ E' - finrank ℝ E) → ℝ

/-- Euclidean model space for right-parenthesized composable triples. -/
abbrev ComposableTriplesRightModel (E E' : Type*) [AddCommGroup E] [Module ℝ E]
    [AddCommGroup E'] [Module ℝ E'] : Type :=
  Fin (finrank ℝ E' +
    finrank ℝ (Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) - finrank ℝ E) → ℝ

/-- Transverse fibre-product smooth atlas on left-parenthesized composable triples. -/
@[expose, instance_reducible]
def composableTriplesLeftChartedSpace :
    ChartedSpace (ComposableTriplesLeftModel E E') (ComposableTriplesLeft C) :=
  letI := composablePairsChartedSpace I J C
  haveI := isManifold_composablePairs I J C
  transverseFiberProductChartedSpace (n := ∞) (by simp)
    ((contMDiff_target I J C).comp (isSubmersion_snd_composablePairs I J C).contMDiff)
    (contMDiff_source I J C)
    (fun p _ ↦ transverse_of_isSubmersion_right (by simp)
      (isSubmersion_source (I := I) (J := J) (C := C)) p)

/-- Left-parenthesized composable triples form a smooth manifold. -/
theorem isManifold_composableTriplesLeft :
    letI := composableTriplesLeftChartedSpace I J C
    IsManifold 𝓘(ℝ, ComposableTriplesLeftModel E E') ∞ (ComposableTriplesLeft C) :=
  letI := composablePairsChartedSpace I J C
  haveI := isManifold_composablePairs I J C
  isManifold_transverseFiberProduct (n := ∞) (by simp)
    ((contMDiff_target I J C).comp (isSubmersion_snd_composablePairs I J C).contMDiff)
    (contMDiff_source I J C)
    (fun p _ ↦ transverse_of_isSubmersion_right (by simp)
      (isSubmersion_source (I := I) (J := J) (C := C)) p)

/-- Inclusion of left-parenthesized composable triples into `ComposablePairs C × Quiver.Total C` is
a smooth embedding. -/
theorem isSmoothEmbedding_coe_composableTriplesLeft :
    letI := composablePairsChartedSpace I J C
    letI := composableTriplesLeftChartedSpace I J C
    Manifold.IsSmoothEmbedding 𝓘(ℝ, ComposableTriplesLeftModel E E')
      (𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ).prod J) ∞
      (Subtype.val : ComposableTriplesLeft C → ComposablePairs C × Quiver.Total C) :=
  letI := composablePairsChartedSpace I J C
  haveI := isManifold_composablePairs I J C
  isSmoothEmbedding_coe_transverseFiberProduct (n := ∞) (by simp)
    ((contMDiff_target I J C).comp (isSubmersion_snd_composablePairs I J C).contMDiff)
    (contMDiff_source I J C)
    (fun p _ ↦ transverse_of_isSubmersion_right (by simp)
      (isSubmersion_source (I := I) (J := J) (C := C)) p)

/-- The first factor projection `((a, b), c) ↦ (a, b)` on left-parenthesized composable triples is a
smooth submersion. -/
theorem isSubmersion_fst_composableTriplesLeft :
    letI := composablePairsChartedSpace I J C
    letI := composableTriplesLeftChartedSpace I J C
    Manifold.IsSubmersion 𝓘(ℝ, ComposableTriplesLeftModel E E')
      𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) ∞
      (fun p : ComposableTriplesLeft C ↦ p.val.1) :=
  letI := composablePairsChartedSpace I J C
  haveI := isManifold_composablePairs I J C
  isSubmersion_fst_transverseFiberProduct (n := ∞) (by simp)
    ((contMDiff_target I J C).comp (isSubmersion_snd_composablePairs I J C).contMDiff)
    (contMDiff_source I J C)
    (fun p _ ↦ transverse_of_isSubmersion_right (by simp)
      (isSubmersion_source (I := I) (J := J) (C := C)) p)
    (isSubmersion_source (I := I) (J := J) (C := C))

/-- The last-arrow projection `((a, b), c) ↦ c` on left-parenthesized composable triples is a smooth
submersion. -/
theorem isSubmersion_snd_composableTriplesLeft :
    letI := composableTriplesLeftChartedSpace I J C
    Manifold.IsSubmersion 𝓘(ℝ, ComposableTriplesLeftModel E E') J ∞
      (fun p : ComposableTriplesLeft C ↦ p.val.2) := by
  let := composablePairsChartedSpace I J C
  have := isManifold_composablePairs I J C
  have hsnd := isSubmersion_snd_composablePairs I J C
  refine isSubmersion_snd_transverseFiberProduct (n := ∞) (by simp)
    ((contMDiff_target I J C).comp hsnd.contMDiff) (contMDiff_source I J C)
    (fun p _ ↦ transverse_of_isSubmersion_right (by simp)
      (isSubmersion_source (I := I) (J := J) (C := C)) p) ?_
  refine (((contMDiff_target I J C).comp hsnd.contMDiff)
    |>.isSubmersionOfComplement_of_surjective_mfderiv (by simp) fun q ↦ ?_).isSubmersion
  rw [mfderiv_comp q ((contMDiff_target I J C _).mdifferentiableAt (by simp))
    ((hsnd.contMDiff q).mdifferentiableAt (by simp))]
  exact (surjective_mfderiv_target I J C q.val.2).comp (hsnd.surjective_mfderiv (by simp) q)

/-- **Universal property of `ComposableTriplesLeft C`.** A map into left-parenthesized composable
triples is `C^n` (`n ≤ ∞`) if and only if all three component arrow maps are `C^n`. -/
theorem contMDiff_composableTriplesLeft_iff {F G X : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [TopologicalSpace G] {K : ModelWithCorners ℝ F G} [TopologicalSpace X]
    [ChartedSpace G X] {n : ℕ∞ω} (hn : n ≤ ∞) {f : X → ComposableTriplesLeft C} :
    letI := composableTriplesLeftChartedSpace I J C
    ContMDiff K 𝓘(ℝ, ComposableTriplesLeftModel E E') n f ↔
      (ContMDiff K J n fun x ↦ (f x).val.1.val.1) ∧
        (ContMDiff K J n fun x ↦ (f x).val.1.val.2) ∧
        ContMDiff K J n fun x ↦ (f x).val.2 := by
  let := composablePairsChartedSpace I J C
  let := composableTriplesLeftChartedSpace I J C
  have := isManifold_composablePairs I J C
  have := isManifold_composableTriplesLeft I J C
  rw [((isSmoothEmbedding_coe_composableTriplesLeft I J C).of_le hn).contMDiff_iff_comp,
    contMDiff_prod_iff]
  change (ContMDiff K _ n fun x ↦ (f x).val.1) ∧ (ContMDiff K J n fun x ↦ (f x).val.2) ↔ _
  rw [contMDiff_composablePairs_iff I J C hn, and_assoc]

/-- Transverse fibre-product smooth atlas on right-parenthesized composable triples. -/
@[expose, instance_reducible]
def composableTriplesRightChartedSpace :
    ChartedSpace (ComposableTriplesRightModel E E') (ComposableTriplesRight C) :=
  letI := composablePairsChartedSpace I J C
  haveI := isManifold_composablePairs I J C
  transverseFiberProductChartedSpace (n := ∞) (by simp)
    (contMDiff_target I J C)
    ((contMDiff_source I J C).comp (isSubmersion_fst_composablePairs I J C).contMDiff)
    (fun p _ ↦ transverse_of_isSubmersion_left (by simp) (isSubmersion_target I J C) p)

/-- Right-parenthesized composable triples form a smooth manifold. -/
theorem isManifold_composableTriplesRight :
    letI := composableTriplesRightChartedSpace I J C
    IsManifold 𝓘(ℝ, ComposableTriplesRightModel E E') ∞ (ComposableTriplesRight C) :=
  letI := composablePairsChartedSpace I J C
  haveI := isManifold_composablePairs I J C
  isManifold_transverseFiberProduct (n := ∞) (by simp)
    (contMDiff_target I J C)
    ((contMDiff_source I J C).comp (isSubmersion_fst_composablePairs I J C).contMDiff)
    (fun p _ ↦ transverse_of_isSubmersion_left (by simp) (isSubmersion_target I J C) p)

/-- Inclusion of right-parenthesized composable triples into `Quiver.Total C × ComposablePairs C` is
a smooth embedding. -/
theorem isSmoothEmbedding_coe_composableTriplesRight :
    letI := composablePairsChartedSpace I J C
    letI := composableTriplesRightChartedSpace I J C
    Manifold.IsSmoothEmbedding 𝓘(ℝ, ComposableTriplesRightModel E E')
      (J.prod 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ)) ∞
      (Subtype.val : ComposableTriplesRight C → Quiver.Total C × ComposablePairs C) :=
  letI := composablePairsChartedSpace I J C
  haveI := isManifold_composablePairs I J C
  isSmoothEmbedding_coe_transverseFiberProduct (n := ∞) (by simp)
    (contMDiff_target I J C)
    ((contMDiff_source I J C).comp (isSubmersion_fst_composablePairs I J C).contMDiff)
    (fun p _ ↦ transverse_of_isSubmersion_left (by simp) (isSubmersion_target I J C) p)

/-- The second factor projection `(a, (b, c)) ↦ (b, c)` on right-parenthesized composable triples is
a smooth submersion. -/
theorem isSubmersion_snd_composableTriplesRight :
    letI := composablePairsChartedSpace I J C
    letI := composableTriplesRightChartedSpace I J C
    Manifold.IsSubmersion 𝓘(ℝ, ComposableTriplesRightModel E E')
      𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) ∞
      (fun p : ComposableTriplesRight C ↦ p.val.2) :=
  letI := composablePairsChartedSpace I J C
  haveI := isManifold_composablePairs I J C
  isSubmersion_snd_transverseFiberProduct (n := ∞) (by simp)
    (contMDiff_target I J C)
    ((contMDiff_source I J C).comp (isSubmersion_fst_composablePairs I J C).contMDiff)
    (fun p _ ↦ transverse_of_isSubmersion_left (by simp) (isSubmersion_target I J C) p)
    (isSubmersion_target I J C)

/-- **Universal property of `ComposableTriplesRight C`.** A map into right-parenthesized composable
triples is `C^n` (`n ≤ ∞`) if and only if all three component arrow maps are `C^n`. -/
theorem contMDiff_composableTriplesRight_iff {F G X : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [TopologicalSpace G] {K : ModelWithCorners ℝ F G} [TopologicalSpace X]
    [ChartedSpace G X] {n : ℕ∞ω} (hn : n ≤ ∞) {f : X → ComposableTriplesRight C} :
    letI := composableTriplesRightChartedSpace I J C
    ContMDiff K 𝓘(ℝ, ComposableTriplesRightModel E E') n f ↔
      (ContMDiff K J n fun x ↦ (f x).val.1) ∧
        (ContMDiff K J n fun x ↦ (f x).val.2.val.1) ∧
        ContMDiff K J n fun x ↦ (f x).val.2.val.2 := by
  let := composablePairsChartedSpace I J C
  let := composableTriplesRightChartedSpace I J C
  have := isManifold_composablePairs I J C
  have := isManifold_composableTriplesRight I J C
  rw [((isSmoothEmbedding_coe_composableTriplesRight I J C).of_le hn).contMDiff_iff_comp,
    contMDiff_prod_iff]
  change (ContMDiff K J n fun x ↦ (f x).val.1) ∧ (ContMDiff K _ n fun x ↦ (f x).val.2) ↔ _
  rw [contMDiff_composablePairs_iff I J C hn]

/-- **Smooth associativity of composable triples.** Regrouping `((a, b), c) ↦ (a, (b, c))` is a
`C^∞` diffeomorphism between the two iterated transverse fibre products of composable triples. -/
def composableTriplesAssocDiffeomorph :
    letI := composableTriplesLeftChartedSpace I J C
    letI := composableTriplesRightChartedSpace I J C
    ComposableTriplesLeft C ≃ₘ^∞⟮𝓘(ℝ, ComposableTriplesLeftModel E E'),
      𝓘(ℝ, ComposableTriplesRightModel E E')⟯ ComposableTriplesRight C :=
  letI := composablePairsChartedSpace I J C
  letI := composableTriplesLeftChartedSpace I J C
  letI := composableTriplesRightChartedSpace I J C
  fiberProductAssocDiffeomorph (isSmoothEmbedding_coe_composablePairs I J C)
    (isSmoothEmbedding_coe_composablePairs I J C)
    (isSmoothEmbedding_coe_composableTriplesLeft I J C)
    (isSmoothEmbedding_coe_composableTriplesRight I J C)

@[simp]
theorem composableTriplesAssocDiffeomorph_apply (p : ComposableTriplesLeft C) :
    letI := composableTriplesLeftChartedSpace I J C
    letI := composableTriplesRightChartedSpace I J C
    composableTriplesAssocDiffeomorph I J C p =
      ⟨(p.val.1.val.1, ⟨(p.val.1.val.2, p.val.2), p.property⟩), p.val.1.property⟩ := by
  let := composablePairsChartedSpace I J C
  let := composableTriplesLeftChartedSpace I J C
  let := composableTriplesRightChartedSpace I J C
  exact fiberProductAssocDiffeomorph_apply (isSmoothEmbedding_coe_composablePairs I J C)
    (isSmoothEmbedding_coe_composablePairs I J C)
    (isSmoothEmbedding_coe_composableTriplesLeft I J C)
    (isSmoothEmbedding_coe_composableTriplesRight I J C) p

@[simp]
theorem composableTriplesAssocDiffeomorph_symm_apply (p : ComposableTriplesRight C) :
    letI := composableTriplesLeftChartedSpace I J C
    letI := composableTriplesRightChartedSpace I J C
    (composableTriplesAssocDiffeomorph I J C).symm p =
      ⟨(⟨(p.val.1, p.val.2.val.1), p.property⟩, p.val.2.val.2), p.val.2.property⟩ := by
  let := composablePairsChartedSpace I J C
  let := composableTriplesLeftChartedSpace I J C
  let := composableTriplesRightChartedSpace I J C
  exact fiberProductAssocDiffeomorph_symm_apply (isSmoothEmbedding_coe_composablePairs I J C)
    (isSmoothEmbedding_coe_composablePairs I J C)
    (isSmoothEmbedding_coe_composableTriplesLeft I J C)
    (isSmoothEmbedding_coe_composableTriplesRight I J C) p

/-! ### Simplicial face maps on composable triples -/

/-- Zeroth face map `((a, b), c) ↦ (b, c)` dropping the first arrow. -/
def triplesFace₀ {C : Type*} [Quiver C] (t : ComposableTriplesLeft C) : ComposablePairs C :=
  ⟨(t.val.1.val.2, t.val.2), t.property⟩

/-- First face map `((a, b), c) ↦ (a ≫ b, c)` composing the first two arrows. -/
def triplesFace₁ {C : Type*} [Category C] (t : ComposableTriplesLeft C) : ComposablePairs C :=
  ⟨(t.val.1.val.1.comp t.val.1.val.2 t.val.1.property, t.val.2),
    (t.val.1.val.1.comp_right t.val.1.val.2 t.val.1.property).trans t.property⟩

/-- Second face map `((a, b), c) ↦ (a, b ≫ c)` composing the last two arrows. -/
def triplesFace₂ {C : Type*} [Category C] (t : ComposableTriplesLeft C) : ComposablePairs C :=
  ⟨(t.val.1.val.1, t.val.1.val.2.comp t.val.2 t.property),
    t.val.1.property.trans (t.val.1.val.2.comp_left t.val.2 t.property).symm⟩

/-- Third face map `((a, b), c) ↦ (a, b)` dropping the last arrow. -/
def triplesFace₃ {C : Type*} [Quiver C] (t : ComposableTriplesLeft C) : ComposablePairs C :=
  t.val.1

@[simp]
theorem triplesFace₀_fst {C : Type*} [Quiver C] (t : ComposableTriplesLeft C) :
    (triplesFace₀ t).val.1 = t.val.1.val.2 :=
  (rfl)

@[simp]
theorem triplesFace₀_snd {C : Type*} [Quiver C] (t : ComposableTriplesLeft C) :
    (triplesFace₀ t).val.2 = t.val.2 :=
  (rfl)

@[simp]
theorem triplesFace₁_fst {C : Type*} [Category C] (t : ComposableTriplesLeft C) :
    (triplesFace₁ t).val.1 = t.val.1.val.1.comp t.val.1.val.2 t.val.1.property :=
  (rfl)

@[simp]
theorem triplesFace₁_snd {C : Type*} [Category C] (t : ComposableTriplesLeft C) :
    (triplesFace₁ t).val.2 = t.val.2 :=
  (rfl)

@[simp]
theorem triplesFace₂_fst {C : Type*} [Category C] (t : ComposableTriplesLeft C) :
    (triplesFace₂ t).val.1 = t.val.1.val.1 :=
  (rfl)

@[simp]
theorem triplesFace₂_snd {C : Type*} [Category C] (t : ComposableTriplesLeft C) :
    (triplesFace₂ t).val.2 = t.val.1.val.2.comp t.val.2 t.property :=
  (rfl)

@[simp]
theorem triplesFace₃_eq {C : Type*} [Quiver C] (t : ComposableTriplesLeft C) :
    triplesFace₃ t = t.val.1 :=
  (rfl)

/-- Simplicial associativity identity `comp ∘ d₁ = comp ∘ d₂` on composable triples. -/
theorem comp_triplesFace₁_eq_comp_triplesFace₂ {C : Type*} [Category C]
    (t : ComposableTriplesLeft C) :
    (triplesFace₁ t).val.1.comp (triplesFace₁ t).val.2 (triplesFace₁ t).property =
      (triplesFace₂ t).val.1.comp (triplesFace₂ t).val.2 (triplesFace₂ t).property :=
  Quiver.Total.comp_assoc t.val.1.val.1 t.val.1.val.2 t.val.2 t.val.1.property t.property _ _

/-- The zeroth simplicial face map `((a, b), c) ↦ (b, c)` is smooth. -/
theorem contMDiff_triplesFace₀ :
    letI := composablePairsChartedSpace I J C
    letI := composableTriplesLeftChartedSpace I J C
    ContMDiff 𝓘(ℝ, ComposableTriplesLeftModel E E')
      𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) ∞
      (triplesFace₀ : ComposableTriplesLeft C → ComposablePairs C) := by
  let := composablePairsChartedSpace I J C
  let := composableTriplesLeftChartedSpace I J C
  obtain ⟨_, hb, hc⟩ :=
    (contMDiff_composableTriplesLeft_iff I J C le_rfl (f := id)).mp contMDiff_id
  exact (contMDiff_composablePairs_iff I J C le_rfl).mpr ⟨hb, hc⟩

/-- The zeroth simplicial face map `((a, b), c) ↦ (b, c)` is a smooth submersion: under
`composableTriplesAssocDiffeomorph` it is the second projection of `ComposableTriplesRight C`. -/
theorem isSubmersion_triplesFace₀ :
    letI := composablePairsChartedSpace I J C
    letI := composableTriplesLeftChartedSpace I J C
    Manifold.IsSubmersion 𝓘(ℝ, ComposableTriplesLeftModel E E')
      𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) ∞
      (triplesFace₀ : ComposableTriplesLeft C → ComposablePairs C) := by
  let := composablePairsChartedSpace I J C
  let := composableTriplesLeftChartedSpace I J C
  let := composableTriplesRightChartedSpace I J C
  have := isManifold_composablePairs I J C
  have := isManifold_composableTriplesLeft I J C
  have := isManifold_composableTriplesRight I J C
  let e := composableTriplesAssocDiffeomorph I J C
  have hsnd := isSubmersion_snd_composableTriplesRight I J C
  refine ((contMDiff_triplesFace₀ I J C).isSubmersionOfComplement_of_surjective_mfderiv
    (by simp) fun t ↦ ?_).isSubmersion
  have heq : (triplesFace₀ : ComposableTriplesLeft C → ComposablePairs C) =
      (fun q : ComposableTriplesRight C ↦ q.val.2) ∘ e := funext fun p ↦ by simp [e, triplesFace₀]
  rw [heq, mfderiv_comp t ((hsnd.contMDiff (e t)).mdifferentiableAt (by simp))
    ((e.contMDiff t).mdifferentiableAt (by simp)), ContinuousLinearMap.coe_comp]
  exact (hsnd.surjective_mfderiv (by simp) (e t)).comp
    ((e.isLocalDiffeomorph t).mfderivToContinuousLinearEquiv (by simp)).surjective

/-- The third simplicial face map `((a, b), c) ↦ (a, b)` is a smooth submersion. -/
theorem isSubmersion_triplesFace₃ :
    letI := composablePairsChartedSpace I J C
    letI := composableTriplesLeftChartedSpace I J C
    Manifold.IsSubmersion 𝓘(ℝ, ComposableTriplesLeftModel E E')
      𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) ∞
      (triplesFace₃ : ComposableTriplesLeft C → ComposablePairs C) :=
  isSubmersion_fst_composableTriplesLeft I J C

/-- The third simplicial face map `((a, b), c) ↦ (a, b)` is smooth. -/
theorem contMDiff_triplesFace₃ :
    letI := composablePairsChartedSpace I J C
    letI := composableTriplesLeftChartedSpace I J C
    ContMDiff 𝓘(ℝ, ComposableTriplesLeftModel E E')
      𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) ∞
      (triplesFace₃ : ComposableTriplesLeft C → ComposablePairs C) :=
  letI := composablePairsChartedSpace I J C
  letI := composableTriplesLeftChartedSpace I J C
  (isSubmersion_triplesFace₃ I J C).contMDiff

/-- The first simplicial face map `((a, b), c) ↦ (a ≫ b, c)` is smooth. -/
theorem contMDiff_triplesFace₁ :
    letI := composablePairsChartedSpace I J C
    letI := composableTriplesLeftChartedSpace I J C
    ContMDiff 𝓘(ℝ, ComposableTriplesLeftModel E E')
      𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) ∞
      (triplesFace₁ : ComposableTriplesLeft C → ComposablePairs C) := by
  let := composablePairsChartedSpace I J C
  let := composableTriplesLeftChartedSpace I J C
  obtain ⟨ha, hb, hc⟩ :=
    (contMDiff_composableTriplesLeft_iff I J C le_rfl (f := id)).mp contMDiff_id
  exact (contMDiff_composablePairs_iff I J C le_rfl).mpr
    ⟨ha.totalComp I J C le_rfl hb fun t ↦ t.val.1.property, hc⟩

/-- The second simplicial face map `((a, b), c) ↦ (a, b ≫ c)` is smooth. -/
theorem contMDiff_triplesFace₂ :
    letI := composablePairsChartedSpace I J C
    letI := composableTriplesLeftChartedSpace I J C
    ContMDiff 𝓘(ℝ, ComposableTriplesLeftModel E E')
      𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) ∞
      (triplesFace₂ : ComposableTriplesLeft C → ComposablePairs C) := by
  let := composablePairsChartedSpace I J C
  let := composableTriplesLeftChartedSpace I J C
  obtain ⟨ha, hb, hc⟩ :=
    (contMDiff_composableTriplesLeft_iff I J C le_rfl (f := id)).mp contMDiff_id
  exact (contMDiff_composablePairs_iff I J C le_rfl).mpr
    ⟨ha, hb.totalComp I J C le_rfl hc fun t ↦ t.property⟩

end TauCeti.IsLieGroupoid

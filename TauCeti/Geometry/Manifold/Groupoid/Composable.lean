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
  sections `Quiver.Total.leftUnitPair` (`b ↦ (1_{s(b)}, b)`), `Quiver.Total.rightUnitPair`
  (`a ↦ (a, 1_{t(a)})`), and `Quiver.Total.unitPair` (`x ↦ (1_x, 1_x)`) are smooth embeddings into
  `Quiver.Total.ComposablePairs C`, and reversing and inverting a composable pair
  `(a, b) ↦ (b⁻¹, a⁻¹)` is an involutive `C^∞` diffeomorphism
  (`inverseComposablePairsDiffeomorph`) compatible with groupoid composition.
* **Iterated transverse pullbacks of composable triples and smooth associativity**: both
  parenthesizations `Quiver.Total.ComposableTriplesLeft C` (`((a, b), c)`) and
  `Quiver.Total.ComposableTriplesRight C` (`(a, (b, c))`) carry canonical transverse fibre-product
  smooth atlases with universal properties, both factor projections of `ComposableTriplesLeft C` and
  the `(b, c)` factor projection of `ComposableTriplesRight C` are smooth submersions, and
  regrouping is a `C^∞` diffeomorphism (`composableTriplesAssocDiffeomorph`).
* **Simplicial face maps**: all four simplicial face maps `Quiver.Total.triplesFace₀`..
  `Quiver.Total.triplesFace₃` from composable triples to composable pairs are smooth, with the outer
  faces `triplesFace₀` and `triplesFace₃` smooth submersions.

## Main declarations

* `TauCeti.IsLieGroupoid.isSmoothEmbedding_leftUnitPair`,
  `TauCeti.IsLieGroupoid.isSmoothEmbedding_rightUnitPair`,
  `TauCeti.IsLieGroupoid.isSmoothEmbedding_unitPair`: smooth unit-pair embeddings into
  `Quiver.Total.ComposablePairs`.
* `TauCeti.IsLieGroupoid.inverseComposablePairsDiffeomorph`: involutive diffeomorphism
  `(a, b) ↦ (b⁻¹, a⁻¹)` of composable pairs.
* `TauCeti.IsLieGroupoid.ComposableTriplesLeftModel`,
  `TauCeti.IsLieGroupoid.ComposableTriplesRightModel`,
  `TauCeti.IsLieGroupoid.composableTriplesLeftChartedSpace`,
  `TauCeti.IsLieGroupoid.composableTriplesRightChartedSpace`,
  `TauCeti.IsLieGroupoid.composableTriplesAssocDiffeomorph`: transverse fibre-product smooth atlases
  on `Quiver.Total.ComposableTriplesLeft` and `Quiver.Total.ComposableTriplesRight`, and the
  regrouping diffeomorphism.
* `TauCeti.IsLieGroupoid.isSubmersion_triplesFace₀`,
  `TauCeti.IsLieGroupoid.contMDiff_triplesFace₁`, `TauCeti.IsLieGroupoid.contMDiff_triplesFace₂`,
  `TauCeti.IsLieGroupoid.isSubmersion_triplesFace₃`: smoothness and outer-face submersion properties
  of the simplicial face maps on composable triples.

## References

* K. C. H. Mackenzie, *General Theory of Lie Groupoids and Lie Algebroids*, London Math. Soc.
  Lecture Note Ser. 213, Cambridge University Press (2005), Section 1.1.
* I. Moerdijk and J. Mrčun, *Introduction to Foliations and Lie Groupoids*, Cambridge Stud. Adv.
  Math. 91, Cambridge University Press (2003), Section 5.1.
-/

public section

noncomputable section

open CategoryTheory Function Module
open Quiver.Total (ComposablePairs ComposableTriplesLeft ComposableTriplesRight leftUnitPair
  rightUnitPair unitPair triplesFace₀ triplesFace₁ triplesFace₂ triplesFace₃)
open scoped Manifold ContDiff

namespace TauCeti.IsLieGroupoid

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

-- `composableTriplesLeftChartedSpace` carries `@[expose]`, so Lean's `module` visibility rules
-- forbid referencing `private` declarations in its body; all four smooth properties below share
-- the smoothness and transversality data bound once in this `private` bundle.
private theorem composableTriplesLeft_bundle :
    letI := composablePairsChartedSpace I J C
    letI := composableTriplesLeftChartedSpace I J C
    IsManifold 𝓘(ℝ, ComposableTriplesLeftModel E E') ∞ (ComposableTriplesLeft C) ∧
      Manifold.IsSmoothEmbedding 𝓘(ℝ, ComposableTriplesLeftModel E E')
        (𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ).prod J) ∞
        (Subtype.val : ComposableTriplesLeft C → ComposablePairs C × Quiver.Total C) ∧
      Manifold.IsSubmersion 𝓘(ℝ, ComposableTriplesLeftModel E E')
        𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) ∞
        (fun p : ComposableTriplesLeft C ↦ p.val.1) ∧
      Manifold.IsSubmersion 𝓘(ℝ, ComposableTriplesLeftModel E E') J ∞
        (fun p : ComposableTriplesLeft C ↦ p.val.2) := by
  let := composablePairsChartedSpace I J C
  have := isManifold_composablePairs I J C
  let K := 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ)
  have hsnd := isSubmersion_snd_composablePairs I J C
  have hf : ContMDiff K I ∞ (fun q : ComposablePairs C ↦ q.val.2.right) :=
    (contMDiff_target I J C).comp hsnd.contMDiff
  have hg := contMDiff_source I J C
  have htrans := fun (p : ComposablePairs C × Quiver.Total C) (_ : p.1.val.2.right = p.2.left) ↦
    transverse_of_isSubmersion_right (IX := K)
      (f := fun q : ComposablePairs C ↦ q.val.2.right) (n := ∞) (by simp)
      (isSubmersion_source (I := I) (J := J) (C := C)) p
  refine ⟨isManifold_transverseFiberProduct (n := ∞) (by simp) hf hg htrans,
    isSmoothEmbedding_coe_transverseFiberProduct (n := ∞) (by simp) hf hg htrans,
    isSubmersion_fst_transverseFiberProduct (n := ∞) (by simp) hf hg htrans
      (isSubmersion_source (I := I) (J := J) (C := C)),
    isSubmersion_snd_transverseFiberProduct (n := ∞) (by simp) hf hg htrans ?_⟩
  refine (hf.isSubmersionOfComplement_of_surjective_mfderiv (by simp) fun q ↦ ?_).isSubmersion
  rw [show (fun q : ComposablePairs C ↦ q.val.2.right) =
      Quiver.Total.right ∘ (fun q : ComposablePairs C ↦ q.val.2) from rfl,
    mfderiv_comp q ((contMDiff_target I J C _).mdifferentiableAt (by simp))
      ((hsnd.contMDiff q).mdifferentiableAt (by simp))]
  exact (surjective_mfderiv_target I J C q.val.2).comp (hsnd.surjective_mfderiv (by simp) q)

/-- Left-parenthesized composable triples form a smooth manifold. -/
theorem isManifold_composableTriplesLeft :
    letI := composableTriplesLeftChartedSpace I J C
    IsManifold 𝓘(ℝ, ComposableTriplesLeftModel E E') ∞ (ComposableTriplesLeft C) :=
  (composableTriplesLeft_bundle I J C).1

/-- Inclusion of left-parenthesized composable triples into `ComposablePairs C × Quiver.Total C` is
a smooth embedding. -/
theorem isSmoothEmbedding_coe_composableTriplesLeft :
    letI := composablePairsChartedSpace I J C
    letI := composableTriplesLeftChartedSpace I J C
    Manifold.IsSmoothEmbedding 𝓘(ℝ, ComposableTriplesLeftModel E E')
      (𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ).prod J) ∞
      (Subtype.val : ComposableTriplesLeft C → ComposablePairs C × Quiver.Total C) :=
  (composableTriplesLeft_bundle I J C).2.1

/-- The first factor projection `((a, b), c) ↦ (a, b)` on left-parenthesized composable triples is a
smooth submersion. -/
theorem isSubmersion_fst_composableTriplesLeft :
    letI := composablePairsChartedSpace I J C
    letI := composableTriplesLeftChartedSpace I J C
    Manifold.IsSubmersion 𝓘(ℝ, ComposableTriplesLeftModel E E')
      𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) ∞
      (fun p : ComposableTriplesLeft C ↦ p.val.1) :=
  (composableTriplesLeft_bundle I J C).2.2.1

/-- The last-arrow projection `((a, b), c) ↦ c` on left-parenthesized composable triples is a smooth
submersion. -/
theorem isSubmersion_snd_composableTriplesLeft :
    letI := composableTriplesLeftChartedSpace I J C
    Manifold.IsSubmersion 𝓘(ℝ, ComposableTriplesLeftModel E E') J ∞
      (fun p : ComposableTriplesLeft C ↦ p.val.2) :=
  (composableTriplesLeft_bundle I J C).2.2.2

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
  simp only [Function.comp_def, contMDiff_composablePairs_iff I J C hn, and_assoc]

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

-- As on the left, `composableTriplesRightChartedSpace` carries `@[expose]`, while the three smooth
-- properties below share the smoothness and transversality data bound once in this `private`
-- bundle.
private theorem composableTriplesRight_bundle :
    letI := composablePairsChartedSpace I J C
    letI := composableTriplesRightChartedSpace I J C
    IsManifold 𝓘(ℝ, ComposableTriplesRightModel E E') ∞ (ComposableTriplesRight C) ∧
      Manifold.IsSmoothEmbedding 𝓘(ℝ, ComposableTriplesRightModel E E')
        (J.prod 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ)) ∞
        (Subtype.val : ComposableTriplesRight C → Quiver.Total C × ComposablePairs C) ∧
      Manifold.IsSubmersion 𝓘(ℝ, ComposableTriplesRightModel E E')
        𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) ∞
        (fun p : ComposableTriplesRight C ↦ p.val.2) := by
  let := composablePairsChartedSpace I J C
  have := isManifold_composablePairs I J C
  let K := 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ)
  have hf := contMDiff_target I J C
  have hg : ContMDiff K I ∞ (fun q : ComposablePairs C ↦ q.val.1.left) :=
    (contMDiff_source I J C).comp (isSubmersion_fst_composablePairs I J C).contMDiff
  have htrans := fun (p : Quiver.Total C × ComposablePairs C) (_ : p.1.right = p.2.val.1.left) ↦
    transverse_of_isSubmersion_left (IY := K)
      (g := fun q : ComposablePairs C ↦ q.val.1.left) (n := ∞) (by simp)
      (isSubmersion_target I J C) p
  exact ⟨isManifold_transverseFiberProduct (n := ∞) (by simp) hf hg htrans,
    isSmoothEmbedding_coe_transverseFiberProduct (n := ∞) (by simp) hf hg htrans,
    isSubmersion_snd_transverseFiberProduct (n := ∞) (by simp) hf hg htrans
      (isSubmersion_target I J C)⟩

/-- Right-parenthesized composable triples form a smooth manifold. -/
theorem isManifold_composableTriplesRight :
    letI := composableTriplesRightChartedSpace I J C
    IsManifold 𝓘(ℝ, ComposableTriplesRightModel E E') ∞ (ComposableTriplesRight C) :=
  (composableTriplesRight_bundle I J C).1

/-- Inclusion of right-parenthesized composable triples into `Quiver.Total C × ComposablePairs C` is
a smooth embedding. -/
theorem isSmoothEmbedding_coe_composableTriplesRight :
    letI := composablePairsChartedSpace I J C
    letI := composableTriplesRightChartedSpace I J C
    Manifold.IsSmoothEmbedding 𝓘(ℝ, ComposableTriplesRightModel E E')
      (J.prod 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ)) ∞
      (Subtype.val : ComposableTriplesRight C → Quiver.Total C × ComposablePairs C) :=
  (composableTriplesRight_bundle I J C).2.1

/-- The second factor projection `(a, (b, c)) ↦ (b, c)` on right-parenthesized composable triples is
a smooth submersion. -/
theorem isSubmersion_snd_composableTriplesRight :
    letI := composablePairsChartedSpace I J C
    letI := composableTriplesRightChartedSpace I J C
    Manifold.IsSubmersion 𝓘(ℝ, ComposableTriplesRightModel E E')
      𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) ∞
      (fun p : ComposableTriplesRight C ↦ p.val.2) :=
  (composableTriplesRight_bundle I J C).2.2

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
  simp only [Function.comp_def, contMDiff_composablePairs_iff I J C hn]

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

/-! ### Smoothness and submersions of simplicial face maps on composable triples -/

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
  rw [contMDiff_composablePairs_iff I J C le_rfl]
  simpa only [Quiver.Total.triplesFace₀_fst, Quiver.Total.triplesFace₀_snd] using ⟨hb, hc⟩

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
      (fun q : ComposableTriplesRight C ↦ q.val.2) ∘ e :=
    funext fun p ↦ Subtype.ext (Prod.ext (by simp [e]) (by simp [e]))
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
      (triplesFace₃ : ComposableTriplesLeft C → ComposablePairs C) := by
  rw [funext Quiver.Total.triplesFace₃_eq]
  exact isSubmersion_fst_composableTriplesLeft I J C

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
  rw [contMDiff_composablePairs_iff I J C le_rfl]
  simpa only [Quiver.Total.triplesFace₁_fst, Quiver.Total.triplesFace₁_snd] using
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
  rw [contMDiff_composablePairs_iff I J C le_rfl]
  simpa only [Quiver.Total.triplesFace₂_fst, Quiver.Total.triplesFace₂_snd] using
    ⟨ha, hb.totalComp I J C le_rfl hc fun t ↦ t.property⟩

end TauCeti.IsLieGroupoid

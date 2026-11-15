/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.FiberProduct.Associativity
public import TauCeti.Geometry.Manifold.Groupoid.Basic
import TauCeti.Geometry.Manifold.SmoothEmbedding.LeftInverse

/-!
# Composable pairs, shear diffeomorphism, and composable triples of a Lie groupoid

For a Lie groupoid `C`, this file develops the smooth geometry of the low-degree spaces of its
simplicial nerve:

* The two unit degeneracy maps `leftUnitPair` and `rightUnitPair` into `ComposablePairs C` are
  smooth embeddings, and pair-inversion `(a, b) ↦ (inv b, inv a)` is an involutive smooth
  diffeomorphism (`inverseComposablePairsDiffeomorph`).
* The shear map `(a, b) ↦ (a, a.comp b h)` is a smooth diffeomorphism from `ComposablePairs C` onto
  `SameSourcePairs C = {p : Quiver.Total C × Quiver.Total C // p.1.left = p.2.left}`. Composing its
  inverse with the second projection shows without coordinate calculations that groupoid composition
  `ComposablePairs C → Quiver.Total C` is itself a smooth submersion (`isSubmersion_comp`).
* The two parenthesizations `ComposableTriplesLeft C` and `ComposableTriplesRight C` of composable
  triples carry transverse fibre-product smooth atlases and are canonically diffeomorphic via
  `composableTriplesAssocDiffeomorph`, and all four simplicial face maps from composable triples to
  composable pairs are smooth.

## References

* K. C. H. Mackenzie, *General Theory of Lie Groupoids and Lie Algebroids*, London Math. Soc.
  Lecture Note Ser. 213, Cambridge University Press (2005), Section 1.1.
* I. Moerdijk and J. Mrčun, *Introduction to Foliations and Lie Groupoids*, Cambridge Stud. Adv.
  Math. 91, Cambridge University Press (2003), Section 5.1.
-/

public section

noncomputable section

open CategoryTheory Function Module Set
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

/-! ### Projections, degeneracies, and inversion on composable pairs -/

/-- Left unit degeneracy `b ↦ (1_{s(b)}, b)` into composable pairs. -/
def leftUnitPair {C : Type*} [Category C] (b : Quiver.Total C) : ComposablePairs C :=
  ⟨(⟨b.left, b.left, 𝟙 b.left⟩, b), rfl⟩

/-- Right unit degeneracy `a ↦ (a, 1_{t(a)})` into composable pairs. -/
def rightUnitPair {C : Type*} [Category C] (a : Quiver.Total C) : ComposablePairs C :=
  ⟨(a, ⟨a.right, a.right, 𝟙 a.right⟩), rfl⟩

@[simp]
theorem leftUnitPair_fst {C : Type*} [Category C] (b : Quiver.Total C) :
    (leftUnitPair b).1.1 = ⟨b.left, b.left, 𝟙 b.left⟩ := (rfl)

@[simp]
theorem leftUnitPair_snd {C : Type*} [Category C] (b : Quiver.Total C) :
    (leftUnitPair b).1.2 = b := (rfl)

@[simp]
theorem rightUnitPair_fst {C : Type*} [Category C] (a : Quiver.Total C) :
    (rightUnitPair a).1.1 = a := (rfl)

@[simp]
theorem rightUnitPair_snd {C : Type*} [Category C] (a : Quiver.Total C) :
    (rightUnitPair a).1.2 = ⟨a.right, a.right, 𝟙 a.right⟩ := (rfl)

/-- The left unit degeneracy `b ↦ (1_{s(b)}, b)` is a smooth embedding into composable pairs. -/
theorem isSmoothEmbedding_leftUnitPair :
    letI := composablePairsChartedSpace I J C
    Manifold.IsSmoothEmbedding J
      𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) ∞
      (leftUnitPair : Quiver.Total C → ComposablePairs C) := by
  let := composablePairsChartedSpace I J C
  have := isManifold_composablePairs I J C
  have hι := isSmoothEmbedding_coe_composablePairs I J C
  have hsmooth : ContMDiff J 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) ∞
      (leftUnitPair : Quiver.Total C → ComposablePairs C) :=
    hι.contMDiff_iff_comp.mpr
      (((contMDiff_unit (I := I) (J := J) (C := C)).comp (contMDiff_source I J C)).prodMk
        contMDiff_id)
  exact hsmooth.isSmoothEmbedding_of_leftInverse (by simp)
    (hι.contMDiff.snd.of_le (by simp)) fun _ ↦ rfl

/-- The right unit degeneracy `a ↦ (a, 1_{t(a)})` is a smooth embedding into composable pairs. -/
theorem isSmoothEmbedding_rightUnitPair :
    letI := composablePairsChartedSpace I J C
    Manifold.IsSmoothEmbedding J
      𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) ∞
      (rightUnitPair : Quiver.Total C → ComposablePairs C) := by
  let := composablePairsChartedSpace I J C
  have := isManifold_composablePairs I J C
  have hι := isSmoothEmbedding_coe_composablePairs I J C
  have hsmooth : ContMDiff J 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) ∞
      (rightUnitPair : Quiver.Total C → ComposablePairs C) :=
    hι.contMDiff_iff_comp.mpr
      (contMDiff_id.prodMk
        ((contMDiff_unit (I := I) (J := J) (C := C)).comp (contMDiff_target I J C)))
  exact hsmooth.isSmoothEmbedding_of_leftInverse (by simp)
    (hι.contMDiff.fst.of_le (by simp)) fun _ ↦ rfl

/-- Reversing and inverting a composable pair `(a, b) ↦ (inv b, inv a)` is an involutive smooth
diffeomorphism of `ComposablePairs C`. -/
def inverseComposablePairsDiffeomorph :
    letI := composablePairsChartedSpace I J C
    ComposablePairs C ≃ₘ^∞⟮𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ),
      𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ)⟯ ComposablePairs C :=
  letI := composablePairsChartedSpace I J C
  { toFun := fun p ↦
      ⟨(inverseDiffeomorph I J C p.1.2, inverseDiffeomorph I J C p.1.1),
        (inverseDiffeomorph_right I J C p.1.2).trans
          (p.2.symm.trans (inverseDiffeomorph_left I J C p.1.1).symm)⟩
    invFun := fun p ↦
      ⟨(inverseDiffeomorph I J C p.1.2, inverseDiffeomorph I J C p.1.1),
        (inverseDiffeomorph_right I J C p.1.2).trans
          (p.2.symm.trans (inverseDiffeomorph_left I J C p.1.1).symm)⟩
    left_inv := fun p ↦ Subtype.ext (by obtain ⟨⟨⟨_, _, _⟩, ⟨_, _, _⟩⟩, _⟩ := p; simp)
    right_inv := fun p ↦ Subtype.ext (by obtain ⟨⟨⟨_, _, _⟩, ⟨_, _, _⟩⟩, _⟩ := p; simp)
    contMDiff_toFun := by
      have := isManifold_composablePairs I J C
      have hι := isSmoothEmbedding_coe_composablePairs I J C
      exact hι.contMDiff_iff_comp.mpr
        (((inverseDiffeomorph I J C).contMDiff.comp hι.contMDiff.snd).prodMk
          ((inverseDiffeomorph I J C).contMDiff.comp hι.contMDiff.fst))
    contMDiff_invFun := by
      have := isManifold_composablePairs I J C
      have hι := isSmoothEmbedding_coe_composablePairs I J C
      exact hι.contMDiff_iff_comp.mpr
        (((inverseDiffeomorph I J C).contMDiff.comp hι.contMDiff.snd).prodMk
          ((inverseDiffeomorph I J C).contMDiff.comp hι.contMDiff.fst)) }

@[simp]
theorem inverseComposablePairsDiffeomorph_fst (p : ComposablePairs C) :
    letI := composablePairsChartedSpace I J C
    (inverseComposablePairsDiffeomorph I J C p).1.1 = inverseDiffeomorph I J C p.1.2 :=
  (rfl)

@[simp]
theorem inverseComposablePairsDiffeomorph_snd (p : ComposablePairs C) :
    letI := composablePairsChartedSpace I J C
    (inverseComposablePairsDiffeomorph I J C p).1.2 = inverseDiffeomorph I J C p.1.1 :=
  (rfl)

@[simp]
theorem inverseComposablePairsDiffeomorph_symm :
    letI := composablePairsChartedSpace I J C
    (inverseComposablePairsDiffeomorph I J C).symm = inverseComposablePairsDiffeomorph I J C :=
  (rfl)

/-! ### Same-source pairs, the shear diffeomorphism, and submersiveness of composition -/

/-- Pairs of total arrows sharing the same source. -/
abbrev SameSourcePairs (C : Type*) [Quiver C] : Type _ :=
  {p : Quiver.Total C × Quiver.Total C // p.1.left = p.2.left}

/-- The transverse fibre-product smooth atlas on pairs of total arrows with the same source. -/
@[instance_reducible]
def sameSourcePairsChartedSpace :
    ChartedSpace (Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) (SameSourcePairs C) :=
  transverseFiberProductChartedSpace (by simp : (1 : ℕ∞ω) ≤ ∞)
    (contMDiff_source I J C) (contMDiff_source I J C)
    (fun p _ ↦ (isSubmersion_source (I := I) (J := J) (C := C)).transverse_left (by simp) _ p)

/-- Same-source arrow pairs form a smooth manifold with their transverse fibre-product atlas. -/
theorem isManifold_sameSourcePairs :
    letI := sameSourcePairsChartedSpace I J C
    IsManifold 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) ∞ (SameSourcePairs C) :=
  isManifold_transverseFiberProduct (by simp : (1 : ℕ∞ω) ≤ ∞)
    (contMDiff_source I J C) (contMDiff_source I J C)
    (fun p _ ↦ (isSubmersion_source (I := I) (J := J) (C := C)).transverse_left (by simp) _ p)

/-- The inclusion of same-source arrow pairs into the product of arrow spaces is a smooth
embedding. -/
theorem isSmoothEmbedding_coe_sameSourcePairs :
    letI := sameSourcePairsChartedSpace I J C
    Manifold.IsSmoothEmbedding
      𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) (J.prod J) ∞
      (Subtype.val : SameSourcePairs C → Quiver.Total C × Quiver.Total C) :=
  isSmoothEmbedding_coe_transverseFiberProduct (by simp : (1 : ℕ∞ω) ≤ ∞)
    (contMDiff_source I J C) (contMDiff_source I J C)
    (fun p _ ↦ (isSubmersion_source (I := I) (J := J) (C := C)).transverse_left (by simp) _ p)

/-- The first projection on same-source arrow pairs is a smooth submersion. -/
theorem isSubmersion_fst_sameSourcePairs :
    letI := sameSourcePairsChartedSpace I J C
    Manifold.IsSubmersion
      𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) J ∞
      (fun q : SameSourcePairs C ↦ q.1.1) :=
  isSubmersion_fst_transverseFiberProduct (by simp : (1 : ℕ∞ω) ≤ ∞)
    (contMDiff_source I J C) (contMDiff_source I J C)
    (fun p _ ↦ (isSubmersion_source (I := I) (J := J) (C := C)).transverse_left (by simp) _ p)
    (isSubmersion_source (I := I) (J := J) (C := C))

/-- The second projection on same-source arrow pairs is a smooth submersion. -/
theorem isSubmersion_snd_sameSourcePairs :
    letI := sameSourcePairsChartedSpace I J C
    Manifold.IsSubmersion
      𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) J ∞
      (fun q : SameSourcePairs C ↦ q.1.2) :=
  isSubmersion_snd_transverseFiberProduct (by simp : (1 : ℕ∞ω) ≤ ∞)
    (contMDiff_source I J C) (contMDiff_source I J C)
    (fun p _ ↦ (isSubmersion_source (I := I) (J := J) (C := C)).transverse_left (by simp) _ p)
    (isSubmersion_source (I := I) (J := J) (C := C))

/-- **The groupoid shear diffeomorphism.** Sending a composable pair `(a, b)` to `(a, a.comp b h)`
is a smooth diffeomorphism from `ComposablePairs C` onto `SameSourcePairs C`, with smooth inverse
`(a, c) ↦ (a, (inv a).comp c h)`. -/
def shearDiffeomorph :
    letI := composablePairsChartedSpace I J C
    letI := sameSourcePairsChartedSpace I J C
    ComposablePairs C ≃ₘ^∞⟮𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ),
      𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ)⟯ SameSourcePairs C :=
  letI := composablePairsChartedSpace I J C
  letI := sameSourcePairsChartedSpace I J C
  { toFun := fun p ↦ ⟨(p.1.1, p.1.1.comp p.1.2 p.2), (p.1.1.comp_left p.1.2 p.2).symm⟩
    invFun := fun q ↦
      ⟨(q.1.1, (inverseDiffeomorph I J C q.1.1).comp q.1.2
          ((inverseDiffeomorph_right I J C q.1.1).trans q.2)),
        (inverseDiffeomorph_left I J C q.1.1).symm.trans
          ((inverseDiffeomorph I J C q.1.1).comp_left q.1.2 _).symm⟩
    left_inv := fun p ↦
      Subtype.ext (Prod.ext rfl
        ((Quiver.Total.comp_congr (inverseDiffeomorph_apply I J C p.1.1) rfl _
          (p.1.1.comp_left p.1.2 p.2).symm).trans
          (Quiver.Total.inv_comp_comp p.1.1 p.1.2 p.2 _)))
    right_inv := fun q ↦
      Subtype.ext (Prod.ext rfl
        ((Quiver.Total.comp_congr rfl
          (Quiver.Total.comp_congr (inverseDiffeomorph_apply I J C q.1.1) rfl _ q.2) _
          (Quiver.Total.comp_left ⟨q.1.1.right, q.1.1.left, inv q.1.1.hom⟩ q.1.2 q.2).symm).trans
          (Quiver.Total.comp_inv_comp q.1.1 q.1.2 q.2 _)))
    contMDiff_toFun := by
      have := isManifold_composablePairs I J C
      have := isManifold_sameSourcePairs I J C
      have hι := isSmoothEmbedding_coe_composablePairs I J C
      have hιS := isSmoothEmbedding_coe_sameSourcePairs I J C
      exact hιS.contMDiff_iff_comp.mpr
        (hι.contMDiff.fst.prodMk (contMDiff_composablePairs_comp I J C))
    contMDiff_invFun := by
      have := isManifold_composablePairs I J C
      have := isManifold_sameSourcePairs I J C
      have hι := isSmoothEmbedding_coe_composablePairs I J C
      have hιS := isSmoothEmbedding_coe_sameSourcePairs I J C
      have hinvPair : ContMDiff
          𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ)
          𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) ∞
          (fun q : SameSourcePairs C ↦
            (⟨(inverseDiffeomorph I J C q.1.1, q.1.2),
              (inverseDiffeomorph_right I J C q.1.1).trans q.2⟩ : ComposablePairs C)) :=
        hι.contMDiff_iff_comp.mpr
          (((inverseDiffeomorph I J C).contMDiff.comp hιS.contMDiff.fst).prodMk
            hιS.contMDiff.snd)
      exact hι.contMDiff_iff_comp.mpr
        (hιS.contMDiff.fst.prodMk
          ((contMDiff_composablePairs_comp I J C).comp hinvPair)) }

@[simp]
theorem shearDiffeomorph_fst (p : ComposablePairs C) :
    letI := composablePairsChartedSpace I J C
    letI := sameSourcePairsChartedSpace I J C
    (shearDiffeomorph I J C p).1.1 = p.1.1 :=
  (rfl)

@[simp]
theorem shearDiffeomorph_snd (p : ComposablePairs C) :
    letI := composablePairsChartedSpace I J C
    letI := sameSourcePairsChartedSpace I J C
    (shearDiffeomorph I J C p).1.2 = p.1.1.comp p.1.2 p.2 :=
  (rfl)

@[simp]
theorem shearDiffeomorph_symm_fst (q : SameSourcePairs C) :
    letI := composablePairsChartedSpace I J C
    letI := sameSourcePairsChartedSpace I J C
    ((shearDiffeomorph I J C).symm q).1.1 = q.1.1 :=
  (rfl)

@[simp]
theorem shearDiffeomorph_symm_snd (q : SameSourcePairs C) :
    letI := composablePairsChartedSpace I J C
    letI := sameSourcePairsChartedSpace I J C
    ((shearDiffeomorph I J C).symm q).1.2 =
      (inverseDiffeomorph I J C q.1.1).comp q.1.2
        ((inverseDiffeomorph_right I J C q.1.1).trans q.2) :=
  (rfl)

/-- **Composition in a Lie groupoid is a smooth submersion.** Composing the second projection of
`SameSourcePairs C` (a submersion) with `shearDiffeomorph` recovers categorical composition. -/
theorem isSubmersion_comp :
    letI := composablePairsChartedSpace I J C
    Manifold.IsSubmersion
      𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) J ∞
      (fun p : ComposablePairs C ↦ p.1.1.comp p.1.2 p.2) := by
  let := composablePairsChartedSpace I J C
  let := sameSourcePairsChartedSpace I J C
  have := isManifold_composablePairs I J C
  have := isManifold_sameSourcePairs I J C
  let e := shearDiffeomorph I J C
  have hπ₂ := isSubmersion_snd_sameSourcePairs I J C
  refine ((hπ₂.contMDiff.comp e.contMDiff).isSubmersionOfComplement_of_surjective_mfderiv
    (by simp) fun p ↦ ?_).isSubmersion
  have hc := mfderiv_comp p ((hπ₂.contMDiff (e p)).mdifferentiableAt (by simp))
    ((e.contMDiff p).mdifferentiableAt (by simp))
  rw [hc]
  exact (hπ₂.surjective_mfderiv (by simp) (e p)).comp
    ((e.isLocalDiffeomorph p).mfderivToContinuousLinearEquiv (by simp)).surjective

/-! ### Composable triples and smooth associativity -/

/-- Left-parenthesized composable triples `((a, b), c)` with `a.right = b.left` and
`b.right = c.left`. -/
abbrev ComposableTriplesLeft (C : Type*) [Quiver C] : Type _ :=
  {p : ComposablePairs C × Quiver.Total C // p.1.1.2.right = p.2.left}

/-- Right-parenthesized composable triples `(a, (b, c))` with `b.right = c.left` and
`a.right = b.left`. -/
abbrev ComposableTriplesRight (C : Type*) [Quiver C] : Type _ :=
  {p : Quiver.Total C × ComposablePairs C // p.1.right = p.2.1.1.left}

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
@[instance_reducible]
def composableTriplesLeftChartedSpace :
    ChartedSpace (ComposableTriplesLeftModel E E') (ComposableTriplesLeft C) :=
  letI := composablePairsChartedSpace I J C
  haveI := isManifold_composablePairs I J C
  transverseFiberProductChartedSpace (by simp : (1 : ℕ∞ω) ≤ ∞)
    ((contMDiff_target I J C).comp
      (contMDiff_snd.comp (isSmoothEmbedding_coe_composablePairs I J C).contMDiff))
    (contMDiff_source I J C)
    (fun p _ ↦ (isSubmersion_source (I := I) (J := J) (C := C)).transverse_right (by simp) _ p)

/-- Left-parenthesized composable triples form a smooth manifold. -/
theorem isManifold_composableTriplesLeft :
    letI := composableTriplesLeftChartedSpace I J C
    IsManifold 𝓘(ℝ, ComposableTriplesLeftModel E E') ∞ (ComposableTriplesLeft C) :=
  letI := composablePairsChartedSpace I J C
  haveI := isManifold_composablePairs I J C
  isManifold_transverseFiberProduct (by simp : (1 : ℕ∞ω) ≤ ∞)
    ((contMDiff_target I J C).comp
      (contMDiff_snd.comp (isSmoothEmbedding_coe_composablePairs I J C).contMDiff))
    (contMDiff_source I J C)
    (fun p _ ↦ (isSubmersion_source (I := I) (J := J) (C := C)).transverse_right (by simp) _ p)

/-- Inclusion of left-parenthesized composable triples into `ComposablePairs C × Quiver.Total C` is
a smooth embedding. -/
theorem isSmoothEmbedding_coe_composableTriplesLeft :
    letI := composablePairsChartedSpace I J C
    letI := composableTriplesLeftChartedSpace I J C
    Manifold.IsSmoothEmbedding
      𝓘(ℝ, ComposableTriplesLeftModel E E')
      (𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ).prod J) ∞
      (Subtype.val : ComposableTriplesLeft C → ComposablePairs C × Quiver.Total C) :=
  letI := composablePairsChartedSpace I J C
  haveI := isManifold_composablePairs I J C
  isSmoothEmbedding_coe_transverseFiberProduct (by simp : (1 : ℕ∞ω) ≤ ∞)
    ((contMDiff_target I J C).comp
      (contMDiff_snd.comp (isSmoothEmbedding_coe_composablePairs I J C).contMDiff))
    (contMDiff_source I J C)
    (fun p _ ↦ (isSubmersion_source (I := I) (J := J) (C := C)).transverse_right (by simp) _ p)

/-- Transverse fibre-product smooth atlas on right-parenthesized composable triples. -/
@[instance_reducible]
def composableTriplesRightChartedSpace :
    ChartedSpace (ComposableTriplesRightModel E E') (ComposableTriplesRight C) :=
  letI := composablePairsChartedSpace I J C
  haveI := isManifold_composablePairs I J C
  transverseFiberProductChartedSpace (by simp : (1 : ℕ∞ω) ≤ ∞)
    (contMDiff_target I J C)
    ((contMDiff_source I J C).comp
      (contMDiff_fst.comp (isSmoothEmbedding_coe_composablePairs I J C).contMDiff))
    (fun p _ ↦ (isSubmersion_target (I := I) (J := J) (C := C)).transverse_left (by simp) _ p)

/-- Right-parenthesized composable triples form a smooth manifold. -/
theorem isManifold_composableTriplesRight :
    letI := composableTriplesRightChartedSpace I J C
    IsManifold 𝓘(ℝ, ComposableTriplesRightModel E E') ∞ (ComposableTriplesRight C) :=
  letI := composablePairsChartedSpace I J C
  haveI := isManifold_composablePairs I J C
  isManifold_transverseFiberProduct (by simp : (1 : ℕ∞ω) ≤ ∞)
    (contMDiff_target I J C)
    ((contMDiff_source I J C).comp
      (contMDiff_fst.comp (isSmoothEmbedding_coe_composablePairs I J C).contMDiff))
    (fun p _ ↦ (isSubmersion_target (I := I) (J := J) (C := C)).transverse_left (by simp) _ p)

/-- Inclusion of right-parenthesized composable triples into `Quiver.Total C × ComposablePairs C` is
a smooth embedding. -/
theorem isSmoothEmbedding_coe_composableTriplesRight :
    letI := composablePairsChartedSpace I J C
    letI := composableTriplesRightChartedSpace I J C
    Manifold.IsSmoothEmbedding
      𝓘(ℝ, ComposableTriplesRightModel E E')
      (J.prod 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ)) ∞
      (Subtype.val : ComposableTriplesRight C → Quiver.Total C × ComposablePairs C) :=
  letI := composablePairsChartedSpace I J C
  haveI := isManifold_composablePairs I J C
  isSmoothEmbedding_coe_transverseFiberProduct (by simp : (1 : ℕ∞ω) ≤ ∞)
    (contMDiff_target I J C)
    ((contMDiff_source I J C).comp
      (contMDiff_fst.comp (isSmoothEmbedding_coe_composablePairs I J C).contMDiff))
    (fun p _ ↦ (isSubmersion_target (I := I) (J := J) (C := C)).transverse_left (by simp) _ p)

/-- **Smooth associativity of composable triples.** Regrouping `((a, b), c) ↦ (a, (b, c))` is a
smooth diffeomorphism between the two iterated transverse fibre products of composable triples. -/
def composableTriplesAssocDiffeomorph :
    letI := composableTriplesLeftChartedSpace I J C
    letI := composableTriplesRightChartedSpace I J C
    ComposableTriplesLeft C ≃ₘ^∞⟮
      𝓘(ℝ, ComposableTriplesLeftModel E E'),
      𝓘(ℝ, ComposableTriplesRightModel E E')⟯
      ComposableTriplesRight C :=
  letI := composablePairsChartedSpace I J C
  letI := composableTriplesLeftChartedSpace I J C
  letI := composableTriplesRightChartedSpace I J C
  fiberProductAssocDiffeomorph
    (isSmoothEmbedding_coe_composablePairs I J C)
    (isSmoothEmbedding_coe_composablePairs I J C)
    (isSmoothEmbedding_coe_composableTriplesLeft I J C)
    (isSmoothEmbedding_coe_composableTriplesRight I J C)

@[simp]
theorem composableTriplesAssocDiffeomorph_apply (p : ComposableTriplesLeft C) :
    letI := composableTriplesLeftChartedSpace I J C
    letI := composableTriplesRightChartedSpace I J C
    composableTriplesAssocDiffeomorph I J C p =
      ⟨(p.1.1.1.1, ⟨(p.1.1.1.2, p.1.2), p.2⟩), p.1.1.2⟩ := by
  let := composablePairsChartedSpace I J C
  let := composableTriplesLeftChartedSpace I J C
  let := composableTriplesRightChartedSpace I J C
  exact fiberProductAssocDiffeomorph_apply
    (isSmoothEmbedding_coe_composablePairs I J C)
    (isSmoothEmbedding_coe_composablePairs I J C)
    (isSmoothEmbedding_coe_composableTriplesLeft I J C)
    (isSmoothEmbedding_coe_composableTriplesRight I J C) p

@[simp]
theorem composableTriplesAssocDiffeomorph_symm_apply (p : ComposableTriplesRight C) :
    letI := composableTriplesLeftChartedSpace I J C
    letI := composableTriplesRightChartedSpace I J C
    (composableTriplesAssocDiffeomorph I J C).symm p =
      ⟨(⟨(p.1.1, p.1.2.1.1), p.2⟩, p.1.2.1.2), p.1.2.2⟩ := by
  let := composablePairsChartedSpace I J C
  let := composableTriplesLeftChartedSpace I J C
  let := composableTriplesRightChartedSpace I J C
  exact fiberProductAssocDiffeomorph_symm_apply
    (isSmoothEmbedding_coe_composablePairs I J C)
    (isSmoothEmbedding_coe_composablePairs I J C)
    (isSmoothEmbedding_coe_composableTriplesLeft I J C)
    (isSmoothEmbedding_coe_composableTriplesRight I J C) p

/-! ### Simplicial face maps on composable triples -/

/-- Zeroth face map `((a, b), c) ↦ (b, c)` dropping the first arrow. -/
def triplesFace₀ {C : Type*} [Quiver C] (t : ComposableTriplesLeft C) : ComposablePairs C :=
  ⟨(t.1.1.1.2, t.1.2), t.2⟩

/-- First face map `((a, b), c) ↦ (a.comp b, c)` composing the first two arrows. -/
def triplesFace₁ {C : Type*} [Category C] (t : ComposableTriplesLeft C) : ComposablePairs C :=
  ⟨(t.1.1.1.1.comp t.1.1.1.2 t.1.1.2, t.1.2),
    (t.1.1.1.1.comp_right t.1.1.1.2 t.1.1.2).trans t.2⟩

/-- Second face map `((a, b), c) ↦ (a, b.comp c)` composing the last two arrows. -/
def triplesFace₂ {C : Type*} [Category C] (t : ComposableTriplesLeft C) : ComposablePairs C :=
  ⟨(t.1.1.1.1, t.1.1.1.2.comp t.1.2 t.2),
    t.1.1.2.trans (t.1.1.1.2.comp_left t.1.2 t.2).symm⟩

/-- Third face map `((a, b), c) ↦ (a, b)` dropping the last arrow. -/
def triplesFace₃ {C : Type*} [Quiver C] (t : ComposableTriplesLeft C) : ComposablePairs C :=
  t.1.1

@[simp]
theorem triplesFace₀_fst {C : Type*} [Quiver C] (t : ComposableTriplesLeft C) :
    (triplesFace₀ t).1.1 = t.1.1.1.2 := (rfl)

@[simp]
theorem triplesFace₀_snd {C : Type*} [Quiver C] (t : ComposableTriplesLeft C) :
    (triplesFace₀ t).1.2 = t.1.2 := (rfl)

@[simp]
theorem triplesFace₁_fst {C : Type*} [Category C] (t : ComposableTriplesLeft C) :
    (triplesFace₁ t).1.1 = t.1.1.1.1.comp t.1.1.1.2 t.1.1.2 := (rfl)

@[simp]
theorem triplesFace₁_snd {C : Type*} [Category C] (t : ComposableTriplesLeft C) :
    (triplesFace₁ t).1.2 = t.1.2 := (rfl)

@[simp]
theorem triplesFace₂_fst {C : Type*} [Category C] (t : ComposableTriplesLeft C) :
    (triplesFace₂ t).1.1 = t.1.1.1.1 := (rfl)

@[simp]
theorem triplesFace₂_snd {C : Type*} [Category C] (t : ComposableTriplesLeft C) :
    (triplesFace₂ t).1.2 = t.1.1.1.2.comp t.1.2 t.2 := (rfl)

@[simp]
theorem triplesFace₃_eq {C : Type*} [Quiver C] (t : ComposableTriplesLeft C) :
    triplesFace₃ t = t.1.1 := (rfl)

/-- Simplicial associativity identity `comp ∘ d₁ = comp ∘ d₂` on composable triples. -/
theorem comp_triplesFace₁_eq_comp_triplesFace₂ {C : Type*} [Category C]
    (t : ComposableTriplesLeft C) :
    (triplesFace₁ t).1.1.comp (triplesFace₁ t).1.2 (triplesFace₁ t).2 =
      (triplesFace₂ t).1.1.comp (triplesFace₂ t).1.2 (triplesFace₂ t).2 :=
  Quiver.Total.comp_assoc t.1.1.1.1 t.1.1.1.2 t.1.2 t.1.1.2 t.2 _ _

/-- The zeroth simplicial face map `((a, b), c) ↦ (b, c)` is smooth. -/
theorem contMDiff_triplesFace₀ :
    letI := composablePairsChartedSpace I J C
    letI := composableTriplesLeftChartedSpace I J C
    ContMDiff
      𝓘(ℝ, ComposableTriplesLeftModel E E')
      𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) ∞
      (triplesFace₀ : ComposableTriplesLeft C → ComposablePairs C) := by
  let := composablePairsChartedSpace I J C
  let := composableTriplesLeftChartedSpace I J C
  have := isManifold_composablePairs I J C
  have := isManifold_composableTriplesLeft I J C
  have hι := isSmoothEmbedding_coe_composablePairs I J C
  have hL := isSmoothEmbedding_coe_composableTriplesLeft I J C
  exact hι.contMDiff_iff_comp.mpr
    (((contMDiff_snd.comp hι.contMDiff).comp (contMDiff_fst.comp hL.contMDiff)).prodMk
      (contMDiff_snd.comp hL.contMDiff))

/-- The first simplicial face map `((a, b), c) ↦ (a.comp b, c)` is smooth. -/
theorem contMDiff_triplesFace₁ :
    letI := composablePairsChartedSpace I J C
    letI := composableTriplesLeftChartedSpace I J C
    ContMDiff
      𝓘(ℝ, ComposableTriplesLeftModel E E')
      𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) ∞
      (triplesFace₁ : ComposableTriplesLeft C → ComposablePairs C) := by
  let := composablePairsChartedSpace I J C
  let := composableTriplesLeftChartedSpace I J C
  have := isManifold_composablePairs I J C
  have := isManifold_composableTriplesLeft I J C
  have hι := isSmoothEmbedding_coe_composablePairs I J C
  have hL := isSmoothEmbedding_coe_composableTriplesLeft I J C
  exact hι.contMDiff_iff_comp.mpr
    (((contMDiff_composablePairs_comp I J C).comp (contMDiff_fst.comp hL.contMDiff)).prodMk
      (contMDiff_snd.comp hL.contMDiff))

/-- The second simplicial face map `((a, b), c) ↦ (a, b.comp c)` is smooth. -/
theorem contMDiff_triplesFace₂ :
    letI := composablePairsChartedSpace I J C
    letI := composableTriplesLeftChartedSpace I J C
    ContMDiff
      𝓘(ℝ, ComposableTriplesLeftModel E E')
      𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) ∞
      (triplesFace₂ : ComposableTriplesLeft C → ComposablePairs C) := by
  let := composablePairsChartedSpace I J C
  let := composableTriplesLeftChartedSpace I J C
  have := isManifold_composablePairs I J C
  have := isManifold_composableTriplesLeft I J C
  have hι := isSmoothEmbedding_coe_composablePairs I J C
  have hL := isSmoothEmbedding_coe_composableTriplesLeft I J C
  exact hι.contMDiff_iff_comp.mpr
    (((contMDiff_fst.comp hι.contMDiff).comp (contMDiff_fst.comp hL.contMDiff)).prodMk
      ((contMDiff_composablePairs_comp I J C).comp (contMDiff_triplesFace₀ I J C)))

/-- The third simplicial face map `((a, b), c) ↦ (a, b)` is smooth. -/
theorem contMDiff_triplesFace₃ :
    letI := composablePairsChartedSpace I J C
    letI := composableTriplesLeftChartedSpace I J C
    ContMDiff
      𝓘(ℝ, ComposableTriplesLeftModel E E')
      𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) ∞
      (triplesFace₃ : ComposableTriplesLeft C → ComposablePairs C) := by
  let := composablePairsChartedSpace I J C
  let := composableTriplesLeftChartedSpace I J C
  have := isManifold_composablePairs I J C
  have := isManifold_composableTriplesLeft I J C
  exact contMDiff_fst.comp (isSmoothEmbedding_coe_composableTriplesLeft I J C).contMDiff

end TauCeti.IsLieGroupoid

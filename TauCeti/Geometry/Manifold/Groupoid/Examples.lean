/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Basic
public import TauCeti.Geometry.Manifold.Groupoid.Composable
public import TauCeti.Geometry.Manifold.PullbackGroupoid
public import TauCeti.Topology.CategoryTheory.Groupoid.Examples
import TauCeti.Geometry.Manifold.Submersion.Basic
import TauCeti.Geometry.Manifold.Submersion.LocalDiffeomorph

/-!
# Unit, pair, and one-object Lie groupoids

Equipping the topological groupoids `Discrete M`, `Codiscrete M`, and `SingleObj G` with smooth
atlases pulled back along their canonical object and arrow homeomorphisms yields the three
fundamental examples of Lie groupoids:

* **Unit Lie groupoid (`TauCeti.UnitGroupoid.isLieGroupoid`).** For any boundaryless finite-
  dimensional smooth manifold `M` (not necessarily Hausdorff), `Discrete M` has object and arrow
  manifolds diffeomorphic to `M`. Source and target are diffeomorphisms, so `Discrete M` is an
  étale Lie groupoid; each source fibre is a singleton and hence Hausdorff without assuming
  `T2Space M`.
* **Pair Lie groupoid (`TauCeti.PairGroupoid.isLieGroupoid`).** For a Hausdorff boundaryless
  finite-dimensional smooth manifold `M`, `Codiscrete M` has object manifold diffeomorphic to `M`
  and total-arrow manifold diffeomorphic to `M × M` in `(target, source)` coordinates. Its source
  and target fibres are diffeomorphic to `M`, its composable pairs are diffeomorphic to
  `M × M × M`, and left and right translations act in coordinates by `(y, x) ↦ (z, x)` and
  `(z, y) ↦ (z, x)`.
* **One-object Lie groupoid (`TauCeti.OneObjectGroupoid.isLieGroupoid`).** For a finite-dimensional
  boundaryless Lie group `G`, `SingleObj G` is a Lie groupoid over `Unit` whose arrow manifold is
  diffeomorphic to `G` and whose geometric groupoid product recovers group multiplication `g * h`.
  Hausdorffness of its unique source fibre follows from `ModelWithCorners.t2Space_of_lieGroup`.

## Main definitions

* `TauCeti.UnitGroupoid.objectDiffeomorph`, `TauCeti.UnitGroupoid.arrowDiffeomorph`,
  `TauCeti.UnitGroupoid.isSubmersion_source`, `TauCeti.UnitGroupoid.isSubmersion_target`,
  `TauCeti.UnitGroupoid.isLieGroupoid`.
* `TauCeti.PairGroupoid.objectDiffeomorph`, `TauCeti.PairGroupoid.arrowDiffeomorph`,
  `TauCeti.PairGroupoid.isSubmersion_source`, `TauCeti.PairGroupoid.isSubmersion_target`,
  `TauCeti.PairGroupoid.isLieGroupoid`, `TauCeti.PairGroupoid.sourceFiberDiffeomorph`,
  `TauCeti.PairGroupoid.targetFiberDiffeomorph`, `TauCeti.PairGroupoid.composablePairsDiffeomorph`.
* `TauCeti.OneObjectGroupoid.objectHomeomorph`, `TauCeti.OneObjectGroupoid.arrowDiffeomorph`,
  `TauCeti.OneObjectGroupoid.isLieGroupoid`,
  `TauCeti.OneObjectGroupoid.composablePairsDiffeomorph`.

## References

* I. Moerdijk and J. Mrčun, *Introduction to Foliations and Lie Groupoids*, Cambridge Studies in
  Advanced Mathematics 91, Cambridge University Press (2003), Section 5.1, Examples 5.1(1)–(3).
* K. C. H. Mackenzie, *General Theory of Lie Groupoids and Lie Algebroids*, London Math. Soc.
  Lecture Note Ser. 213, Cambridge University Press (2005), Examples 1.1.9–1.1.11.
-/

public section

open CategoryTheory Module
open scoped Manifold ContDiff

namespace TauCeti

namespace UnitGroupoid

section Atlas

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M] [ChartedSpace H M]

/-- Objects of the unit groupoid inherit the smooth atlas of `M` via `objectHomeomorph`. -/
instance instChartedSpaceObjects : ChartedSpace H (Discrete M) :=
  (objectHomeomorph M).pullbackChartedSpace

/-- Objects of the unit groupoid form a smooth manifold modeled on `I`. -/
instance instIsManifoldObjects [IsManifold I ∞ M] : IsManifold I ∞ (Discrete M) :=
  (objectHomeomorph M).pullback_isManifold I ∞

/-- Unwrapping `Discrete M` is a smooth diffeomorphism onto `M`. -/
noncomputable def objectDiffeomorph : Discrete M ≃ₘ^∞⟮I, I⟯ M :=
  (objectHomeomorph M).pullbackDiffeomorph I ∞

/-- Total arrows of the unit groupoid inherit the smooth atlas of `M` via `arrowHomeomorph`. -/
instance instChartedSpaceArrows : ChartedSpace H (Quiver.Total (Discrete M)) :=
  (arrowHomeomorph M).pullbackChartedSpace

/-- Total arrows of the unit groupoid form a smooth manifold modeled on `I`. -/
instance instIsManifoldArrows [IsManifold I ∞ M] : IsManifold I ∞ (Quiver.Total (Discrete M)) :=
  (arrowHomeomorph M).pullback_isManifold I ∞

/-- Sending each unit arrow to its basepoint in `M` is a smooth diffeomorphism. -/
noncomputable def arrowDiffeomorph : Quiver.Total (Discrete M) ≃ₘ^∞⟮I, I⟯ M :=
  (arrowHomeomorph M).pullbackDiffeomorph I ∞

@[simp]
theorem objectDiffeomorph_apply (x : Discrete M) : objectDiffeomorph I M x = x.as := by
  simp [objectDiffeomorph]

@[simp]
theorem objectDiffeomorph_symm_apply (x : M) :
    (objectDiffeomorph I M).symm x = Discrete.mk x := by
  simp [objectDiffeomorph]

@[simp]
theorem arrowDiffeomorph_apply (a : Quiver.Total (Discrete M)) :
    arrowDiffeomorph I M a = a.left.as := by
  simp [arrowDiffeomorph]

@[simp]
theorem arrowDiffeomorph_symm_apply (x : M) :
    (arrowDiffeomorph I M).symm x = ⟨⟨x⟩, ⟨x⟩, 𝟙 _⟩ := by
  simp [arrowDiffeomorph]

/-- Source on the unit groupoid is a smooth submersion for any smooth manifold `M` (including
infinite-dimensional or with boundary). -/
theorem isSubmersion_source [IsManifold I ∞ M] :
    Manifold.IsSubmersion I I ∞
      (Quiver.Total.left : Quiver.Total (Discrete M) → Discrete M) := by
  have heq : (Quiver.Total.left : Quiver.Total (Discrete M) → Discrete M) =
      ((arrowDiffeomorph I M).trans (objectDiffeomorph I M).symm) := by
    funext a; simp
  rw [heq]
  exact ((arrowDiffeomorph I M).trans
    (objectDiffeomorph I M).symm).isLocalDiffeomorph.isSubmersion_sameModel

/-- Target on the unit groupoid is a smooth submersion for any smooth manifold `M` (including
infinite-dimensional or with boundary). -/
theorem isSubmersion_target [IsManifold I ∞ M] :
    Manifold.IsSubmersion I I ∞
      (Quiver.Total.right : Quiver.Total (Discrete M) → Discrete M) := by
  have heq : (Quiver.Total.right : Quiver.Total (Discrete M) → Discrete M) =
      Quiver.Total.left := by
    funext a
    exact (Discrete.ext (Discrete.eq_of_hom a.hom)).symm
  rw [heq]
  exact isSubmersion_source I M

end Atlas

section LieGroupoid

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The unit groupoid on any boundaryless finite-dimensional smooth manifold is an étale Lie
groupoid; its source fibres are singletons and hence Hausdorff even without `T2Space M`. -/
instance isLieGroupoid : IsLieGroupoid I I (Discrete M) where
  isSubmersion_source := isSubmersion_source I M
  isSubmersion_target := isSubmersion_target I M
  contMDiff_unit :=
    (((objectDiffeomorph I M).trans (arrowDiffeomorph I M).symm).contMDiff).congr fun x ↦ by simp
  contMDiff_inverse := contMDiff_id.congr fun ⟨⟨x⟩, ⟨y⟩, f⟩ ↦ by
    obtain rfl := Discrete.eq_of_hom f
    simp [Subsingleton.elim (inv f) f]
  contMDiff_mul := by
    let hsrc := isSubmersion_source I M
    let htgt := isSubmersion_target I M
    let _ := transverseFiberProductChartedSpace (by simp : (1 : ℕ∞ω) ≤ ∞)
      hsrc.contMDiff htgt.contMDiff (transverse_of_isSubmersion_left hsrc (by simp))
    have hcoe := (isSmoothEmbedding_coe_transverseFiberProduct (by simp : (1 : ℕ∞ω) ≤ ∞)
      hsrc.contMDiff htgt.contMDiff (transverse_of_isSubmersion_left hsrc (by simp))).contMDiff
    refine (contMDiff_fst.comp hcoe).congr ?_
    rintro ⟨⟨⟨⟨x⟩, ⟨y⟩, f⟩, ⟨⟨z⟩, ⟨w⟩, g⟩⟩, h⟩
    obtain rfl := Discrete.eq_of_hom f
    obtain rfl := Discrete.eq_of_hom g
    dsimp only at h
    cases h
    simp [Quiver.Total.comp_def, Subsingleton.elim (g ≫ f) f]
  t2Space_sourceFiber x := by
    have : Subsingleton {a : Quiver.Total (Discrete M) // a.left = x} := ⟨by
      rintro ⟨⟨⟨u⟩, ⟨v⟩, f⟩, hu⟩ ⟨⟨⟨u'⟩, ⟨v'⟩, g⟩, hu'⟩
      obtain rfl := Discrete.eq_of_hom f
      obtain rfl := Discrete.eq_of_hom g
      dsimp only at hu hu'
      cases hu
      cases hu'
      exact Subtype.ext (by simp [Subsingleton.elim f g])⟩
    infer_instance

end LieGroupoid

end UnitGroupoid

namespace PairGroupoid

section Atlas

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M] [ChartedSpace H M]

/-- Objects of the pair groupoid inherit the smooth atlas of `M` via `objectHomeomorph`. -/
instance instChartedSpaceObjects : ChartedSpace H (Codiscrete M) :=
  (objectHomeomorph M).pullbackChartedSpace

/-- Objects of the pair groupoid form a smooth manifold modeled on `I`. -/
instance instIsManifoldObjects [IsManifold I ∞ M] : IsManifold I ∞ (Codiscrete M) :=
  (objectHomeomorph M).pullback_isManifold I ∞

/-- Unwrapping `Codiscrete M` is a smooth diffeomorphism onto `M`. -/
noncomputable def objectDiffeomorph : Codiscrete M ≃ₘ^∞⟮I, I⟯ M :=
  (objectHomeomorph M).pullbackDiffeomorph I ∞

/-- Total arrows of the pair groupoid carry the product smooth atlas via `arrowHomeomorph` in
`(target, source)` coordinates. -/
instance instChartedSpaceArrows : ChartedSpace (ModelProd H H) (Quiver.Total (Codiscrete M)) :=
  (arrowHomeomorph M).pullbackChartedSpace

/-- Total arrows of the pair groupoid form a smooth manifold modeled on `I.prod I`. -/
instance instIsManifoldArrows [IsManifold I ∞ M] :
    IsManifold (I.prod I) ∞ (Quiver.Total (Codiscrete M)) :=
  (arrowHomeomorph M).pullback_isManifold (I.prod I) ∞

/-- Sending the unique arrow `x ⟶ y` of `Codiscrete M` to `(y, x)` is a smooth diffeomorphism onto
`M × M`. -/
noncomputable def arrowDiffeomorph : Quiver.Total (Codiscrete M) ≃ₘ^∞⟮I.prod I, I.prod I⟯ M × M :=
  (arrowHomeomorph M).pullbackDiffeomorph (I.prod I) ∞

@[simp]
theorem objectDiffeomorph_apply (x : Codiscrete M) : objectDiffeomorph I M x = x.as := by
  simp [objectDiffeomorph]

@[simp]
theorem objectDiffeomorph_symm_apply (x : M) :
    (objectDiffeomorph I M).symm x = Codiscrete.mk x := by
  simp [objectDiffeomorph]

@[simp]
theorem arrowDiffeomorph_apply (a : Quiver.Total (Codiscrete M)) :
    arrowDiffeomorph I M a = (a.right.as, a.left.as) := by
  simp [arrowDiffeomorph]

@[simp]
theorem arrowDiffeomorph_symm_apply (p : M × M) :
    (arrowDiffeomorph I M).symm p = ⟨⟨p.2⟩, ⟨p.1⟩, default⟩ := by
  simp [arrowDiffeomorph]

/-- Source on the pair groupoid is a smooth submersion for any smooth manifold `M` (including
infinite-dimensional or with boundary). -/
theorem isSubmersion_source [IsManifold I ∞ M] :
    Manifold.IsSubmersion (I.prod I) I ∞
      (Quiver.Total.left : Quiver.Total (Codiscrete M) → Codiscrete M) := by
  let Φ := (arrowDiffeomorph I M).trans (Diffeomorph.prodComm I I M M ∞)
  let Ψ := (objectDiffeomorph I M).symm
  have heq : (Quiver.Total.left : Quiver.Total (Codiscrete M) → Codiscrete M) =
      (Ψ ∘ Prod.fst) ∘ Φ := by
    funext a; simp [Φ, Ψ]
  rw [heq]
  refine (Manifold.isSubmersionOfComplement_iff (F := E).mpr fun a ↦ ?_).isSubmersion
  have h₁ := Manifold.isSubmersionOfComplement_iff.mp
    (Manifold.isSubmersionOfComplement_fst (I := I) (J := I) (M := M) (N := M) (n := ∞)) (Φ a)
  have h₂ : Manifold.IsSubmersionAtOfComplement E (I.prod I) I ∞ (Ψ ∘ Prod.fst) (Φ a) :=
    (Ψ.isLocalDiffeomorph (Φ a).1).comp_isSubmersionAtOfComplement h₁
  exact (Φ.isLocalDiffeomorph a).isSubmersionAtOfComplement_comp h₂

/-- Target on the pair groupoid is a smooth submersion for any smooth manifold `M` (including
infinite-dimensional or with boundary). -/
theorem isSubmersion_target [IsManifold I ∞ M] :
    Manifold.IsSubmersion (I.prod I) I ∞
      (Quiver.Total.right : Quiver.Total (Codiscrete M) → Codiscrete M) := by
  let Φ := arrowDiffeomorph I M
  let Ψ := (objectDiffeomorph I M).symm
  have heq : (Quiver.Total.right : Quiver.Total (Codiscrete M) → Codiscrete M) =
      (Ψ ∘ Prod.fst) ∘ Φ := by
    funext a; simp [Φ, Ψ]
  rw [heq]
  refine (Manifold.isSubmersionOfComplement_iff (F := E).mpr fun a ↦ ?_).isSubmersion
  have h₁ := Manifold.isSubmersionOfComplement_iff.mp
    (Manifold.isSubmersionOfComplement_fst (I := I) (J := I) (M := M) (N := M) (n := ∞)) (Φ a)
  have h₂ : Manifold.IsSubmersionAtOfComplement E (I.prod I) I ∞ (Ψ ∘ Prod.fst) (Φ a) :=
    (Ψ.isLocalDiffeomorph (Φ a).1).comp_isSubmersionAtOfComplement h₁
  exact (Φ.isLocalDiffeomorph a).isSubmersionAtOfComplement_comp h₂

end Atlas

section LieGroupoid

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The pair groupoid on a Hausdorff boundaryless finite-dimensional smooth manifold `M` is a Lie
groupoid with arrow manifold `M × M`. -/
instance isLieGroupoid [T2Space M] : IsLieGroupoid I (I.prod I) (Codiscrete M) where
  isSubmersion_source := isSubmersion_source I M
  isSubmersion_target := isSubmersion_target I M
  contMDiff_unit := ((arrowDiffeomorph I M).symm.contMDiff.comp <|
    (objectDiffeomorph I M).contMDiff.prodMk (objectDiffeomorph I M).contMDiff).congr fun x ↦ by
      simp [Subsingleton.elim default (𝟙 x)]
  contMDiff_inverse := ((arrowDiffeomorph I M).symm.contMDiff.comp <|
    (Diffeomorph.prodComm I I M M ∞).contMDiff.comp (arrowDiffeomorph I M).contMDiff).congr
      fun a ↦ by simp [Subsingleton.elim default (inv a.hom)]
  contMDiff_mul := by
    let hsrc := isSubmersion_source I M
    let htgt := isSubmersion_target I M
    let _ := transverseFiberProductChartedSpace (by simp : (1 : ℕ∞ω) ≤ ∞)
      hsrc.contMDiff htgt.contMDiff (transverse_of_isSubmersion_left hsrc (by simp))
    have hcoe := (isSmoothEmbedding_coe_transverseFiberProduct (by simp : (1 : ℕ∞ω) ≤ ∞)
      hsrc.contMDiff htgt.contMDiff (transverse_of_isSubmersion_left hsrc (by simp))).contMDiff
    have h₁ := contMDiff_fst.comp ((arrowDiffeomorph I M).contMDiff.comp (contMDiff_fst.comp hcoe))
    have h₂ := contMDiff_snd.comp ((arrowDiffeomorph I M).contMDiff.comp (contMDiff_snd.comp hcoe))
    refine ((arrowDiffeomorph I M).symm.contMDiff.comp (h₁.prodMk h₂)).congr fun p ↦ ?_
    obtain ⟨⟨⟨⟨y⟩, ⟨z⟩, f⟩, ⟨⟨x⟩, ⟨y'⟩, g⟩⟩, h⟩ := p
    dsimp only at h
    cases h
    simp [Quiver.Total.comp_def, Subsingleton.elim default (g ≫ f)]
  t2Space_sourceFiber _ := by
    have : T2Space (Quiver.Total (Codiscrete M)) := (arrowHomeomorph M).isEmbedding.t2Space
    infer_instance

section Coordinates

variable [T2Space M]

/-- Each source fibre `s⁻¹(x)` of `Codiscrete M` is smoothly diffeomorphic to `M` via the target
coordinate `(y, x) ↦ y`. -/
noncomputable def sourceFiberDiffeomorph (x : Codiscrete M) :
    letI := IsLieGroupoid.sourceFiberChartedSpace I (I.prod I) (Codiscrete M) x
    {a : Quiver.Total (Codiscrete M) // a.left = x} ≃ₘ^∞⟮
      𝓘(ℝ, Fin (finrank ℝ (E × E) - finrank ℝ E) → ℝ), I⟯ M :=
  letI := IsLieGroupoid.sourceFiberChartedSpace I (I.prod I) (Codiscrete M) x
  { toFun := fun a ↦ a.1.right.as
    invFun := fun y ↦ ⟨⟨x, ⟨y⟩, default⟩, rfl⟩
    left_inv := fun ⟨⟨x', ⟨y⟩, f⟩, hx⟩ ↦ by
      dsimp only at hx
      subst hx
      exact Subtype.ext (by simp [Subsingleton.elim default f])
    right_inv := fun _ ↦ rfl
    contMDiff_toFun := (contMDiff_fst.comp <| (arrowDiffeomorph I M).contMDiff.comp
      (IsLieGroupoid.isSmoothEmbedding_coe_sourceFiber I (I.prod I) (Codiscrete M)
        x).contMDiff).congr fun _ ↦ by simp
    contMDiff_invFun :=
      (IsLieGroupoid.isSmoothEmbedding_coe_sourceFiber I (I.prod I) (Codiscrete M)
        x).contMDiff_iff_comp.mpr <|
        ((arrowDiffeomorph I M).symm.contMDiff.comp
          (contMDiff_id.prodMk (contMDiff_const (c := x.as)))).congr
          fun y ↦ by obtain ⟨x⟩ := x; simp }

@[simp]
theorem sourceFiberDiffeomorph_apply (x : Codiscrete M)
    (a : {a : Quiver.Total (Codiscrete M) // a.left = x}) :
    letI := IsLieGroupoid.sourceFiberChartedSpace I (I.prod I) (Codiscrete M) x
    sourceFiberDiffeomorph I M x a = a.1.right.as := (rfl)

@[simp]
theorem coe_sourceFiberDiffeomorph_symm (x : Codiscrete M) (y : M) :
    letI := IsLieGroupoid.sourceFiberChartedSpace I (I.prod I) (Codiscrete M) x
    ((sourceFiberDiffeomorph I M x).symm y : Quiver.Total (Codiscrete M)) =
      ⟨x, ⟨y⟩, default⟩ := (rfl)

/-- Each target fibre `t⁻¹(y)` of `Codiscrete M` is smoothly diffeomorphic to `M` via the source
coordinate `(y, x) ↦ x`. -/
noncomputable def targetFiberDiffeomorph (y : Codiscrete M) :
    letI := IsLieGroupoid.targetFiberChartedSpace I (I.prod I) (Codiscrete M) y
    {a : Quiver.Total (Codiscrete M) // a.right = y} ≃ₘ^∞⟮
      𝓘(ℝ, Fin (finrank ℝ (E × E) - finrank ℝ E) → ℝ), I⟯ M :=
  letI := IsLieGroupoid.targetFiberChartedSpace I (I.prod I) (Codiscrete M) y
  { toFun := fun a ↦ a.1.left.as
    invFun := fun x ↦ ⟨⟨⟨x⟩, y, default⟩, rfl⟩
    left_inv := fun ⟨⟨⟨x⟩, y', f⟩, hy⟩ ↦ by
      dsimp only at hy
      subst hy
      exact Subtype.ext (by simp [Subsingleton.elim default f])
    right_inv := fun _ ↦ rfl
    contMDiff_toFun := (contMDiff_snd.comp <| (arrowDiffeomorph I M).contMDiff.comp
      (IsLieGroupoid.isSmoothEmbedding_coe_targetFiber I (I.prod I) (Codiscrete M)
        y).contMDiff).congr fun _ ↦ by simp
    contMDiff_invFun :=
      (IsLieGroupoid.isSmoothEmbedding_coe_targetFiber I (I.prod I) (Codiscrete M)
        y).contMDiff_iff_comp.mpr <|
        ((arrowDiffeomorph I M).symm.contMDiff.comp
          ((contMDiff_const (c := y.as)).prodMk contMDiff_id)).congr
          fun x ↦ by obtain ⟨y⟩ := y; simp }

@[simp]
theorem targetFiberDiffeomorph_apply (y : Codiscrete M)
    (a : {a : Quiver.Total (Codiscrete M) // a.right = y}) :
    letI := IsLieGroupoid.targetFiberChartedSpace I (I.prod I) (Codiscrete M) y
    targetFiberDiffeomorph I M y a = a.1.left.as := (rfl)

@[simp]
theorem coe_targetFiberDiffeomorph_symm (y : Codiscrete M) (x : M) :
    letI := IsLieGroupoid.targetFiberChartedSpace I (I.prod I) (Codiscrete M) y
    ((targetFiberDiffeomorph I M y).symm x : Quiver.Total (Codiscrete M)) =
      ⟨⟨x⟩, y, default⟩ := (rfl)

/-- Composable pairs `((z, y), (y, x))` in `Codiscrete M` (in geometric order `s(g) = t(h)`) are
smoothly diffeomorphic to `M × M × M` via `((z, y), (y, x)) ↦ (z, y, x)`. -/
noncomputable def composablePairsDiffeomorph :
    letI := IsLieGroupoid.composablePairsChartedSpace I (I.prod I) (Codiscrete M)
    {p : Quiver.Total (Codiscrete M) × Quiver.Total (Codiscrete M) // p.1.left = p.2.right} ≃ₘ^∞⟮
      𝓘(ℝ, Fin (finrank ℝ (E × E) + finrank ℝ (E × E) - finrank ℝ E) → ℝ),
      I.prod (I.prod I)⟯ M × M × M :=
  letI := IsLieGroupoid.composablePairsChartedSpace I (I.prod I) (Codiscrete M)
  have hcoe :=
    (IsLieGroupoid.isSmoothEmbedding_coe_composablePairs I (I.prod I) (Codiscrete M)).contMDiff
  { toFun := fun p ↦ (p.1.1.right.as, p.1.1.left.as, p.1.2.left.as)
    invFun := fun t ↦ ⟨(⟨⟨t.2.1⟩, ⟨t.1⟩, default⟩, ⟨⟨t.2.2⟩, ⟨t.2.1⟩, default⟩), rfl⟩
    left_inv := fun ⟨⟨⟨⟨y⟩, ⟨z⟩, f⟩, ⟨⟨x⟩, ⟨y'⟩, g⟩⟩, h⟩ ↦ by
      dsimp only at h
      cases h
      exact Subtype.ext (Prod.ext (by simp [Subsingleton.elim default f])
        (by simp [Subsingleton.elim default g]))
    right_inv := fun _ ↦ rfl
    contMDiff_toFun :=
      ((contMDiff_fst.comp ((arrowDiffeomorph I M).contMDiff.comp (contMDiff_fst.comp hcoe))).prodMk
        ((contMDiff_snd.comp ((arrowDiffeomorph I M).contMDiff.comp
          (contMDiff_fst.comp hcoe))).prodMk
          (contMDiff_snd.comp ((arrowDiffeomorph I M).contMDiff.comp
            (contMDiff_snd.comp hcoe))))).congr fun _ ↦ by simp
    contMDiff_invFun :=
      (IsLieGroupoid.isSmoothEmbedding_coe_composablePairs I (I.prod I)
        (Codiscrete M)).contMDiff_iff_comp.mpr <|
        (((arrowDiffeomorph I M).symm.contMDiff.comp
          (contMDiff_fst.prodMk (contMDiff_fst.comp contMDiff_snd))).prodMk
          ((arrowDiffeomorph I M).symm.contMDiff.comp
            ((contMDiff_fst.comp contMDiff_snd).prodMk
              (contMDiff_snd.comp contMDiff_snd)))).congr fun _ ↦ by simp }

@[simp]
theorem composablePairsDiffeomorph_apply
    (p : {p : Quiver.Total (Codiscrete M) × Quiver.Total (Codiscrete M) // p.1.left = p.2.right}) :
    letI := IsLieGroupoid.composablePairsChartedSpace I (I.prod I) (Codiscrete M)
    composablePairsDiffeomorph I M p = (p.1.1.right.as, p.1.1.left.as, p.1.2.left.as) := (rfl)

@[simp]
theorem composablePairsDiffeomorph_symm_apply (t : M × M × M) :
    letI := IsLieGroupoid.composablePairsChartedSpace I (I.prod I) (Codiscrete M)
    (composablePairsDiffeomorph I M).symm t =
      ⟨(⟨⟨t.2.1⟩, ⟨t.1⟩, default⟩, ⟨⟨t.2.2⟩, ⟨t.2.1⟩, default⟩), rfl⟩ := (rfl)

/-- In `(target, source)` coordinates, pair-groupoid multiplication discards the middle point:
`(z, y) · (y, x) = (z, x)`. -/
theorem arrowDiffeomorph_mul_composablePairsDiffeomorph_symm (t : M × M × M) :
    letI := IsLieGroupoid.composablePairsChartedSpace I (I.prod I) (Codiscrete M)
    let p := (composablePairsDiffeomorph I M).symm t
    arrowDiffeomorph I M (p.1.2.comp p.1.1 p.2.symm) = (t.1, t.2.2) := by
  let _ := IsLieGroupoid.composablePairsChartedSpace I (I.prod I) (Codiscrete M)
  simp

/-- Left translation in `Codiscrete M` by `(z, y)` sends `(y, x)` to `(z, x)`. -/
theorem arrowDiffeomorph_leftTranslate (x y z : M) :
    let g : Quiver.Total (Codiscrete M) := ⟨⟨y⟩, ⟨z⟩, default⟩
    letI := IsLieGroupoid.targetFiberChartedSpace I (I.prod I) (Codiscrete M) g.left
    letI := IsLieGroupoid.targetFiberChartedSpace I (I.prod I) (Codiscrete M) g.right
    arrowDiffeomorph I M
      (IsLieGroupoid.leftTranslateDiffeomorph I (I.prod I) (Codiscrete M) g
        ⟨⟨⟨x⟩, ⟨y⟩, default⟩, rfl⟩) = (z, x) := by
  simp

/-- Right translation in `Codiscrete M` by `(y, x)` sends `(z, y)` to `(z, x)`. -/
theorem arrowDiffeomorph_rightTranslate (x y z : M) :
    let g : Quiver.Total (Codiscrete M) := ⟨⟨x⟩, ⟨y⟩, default⟩
    letI := IsLieGroupoid.sourceFiberChartedSpace I (I.prod I) (Codiscrete M) g.right
    letI := IsLieGroupoid.sourceFiberChartedSpace I (I.prod I) (Codiscrete M) g.left
    arrowDiffeomorph I M
      (IsLieGroupoid.rightTranslateDiffeomorph I (I.prod I) (Codiscrete M) g
        ⟨⟨⟨y⟩, ⟨z⟩, default⟩, rfl⟩) = (z, x) := by
  simp

end Coordinates

end LieGroupoid

end PairGroupoid

namespace OneObjectGroupoid

section ObjectAtlas

variable (G : Type*)

/-- Identifying the unique object of `SingleObj G` with `Unit` is a homeomorphism. -/
def objectHomeomorph : SingleObj G ≃ₜ Unit where
  toFun _ := ()
  invFun _ := SingleObj.star G
  left_inv x := by cases x; rfl
  right_inv u := by cases u; rfl
  continuous_toFun := continuous_const
  continuous_invFun := continuous_const

@[simp]
theorem objectHomeomorph_apply (x : SingleObj G) : objectHomeomorph G x = () := (rfl)

@[simp]
theorem objectHomeomorph_symm_apply (u : Unit) :
    (objectHomeomorph G).symm u = SingleObj.star G := (rfl)

/-- The singleton object space of `SingleObj G` carries the zero-dimensional `Unit` atlas. -/
instance instChartedSpaceObjects : ChartedSpace Unit (SingleObj G) :=
  (objectHomeomorph G).pullbackChartedSpace

/-- The singleton object space of `SingleObj G` is a zero-dimensional smooth manifold. -/
instance instIsManifoldObjects : IsManifold 𝓘(ℝ, Unit) ∞ (SingleObj G) :=
  (objectHomeomorph G).pullback_isManifold 𝓘(ℝ, Unit) ∞

end ObjectAtlas

section ArrowAtlas

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) (G : Type*) [TopologicalSpace G] [ChartedSpace H G]

/-- Total arrows of `SingleObj G` inherit the smooth atlas of `G` via `arrowHomeomorph`. -/
instance instChartedSpaceArrows : ChartedSpace H (Quiver.Total (SingleObj G)) :=
  (arrowHomeomorph G).pullbackChartedSpace

/-- Total arrows of `SingleObj G` form a smooth manifold modeled on `I`. -/
instance instIsManifoldArrows [IsManifold I ∞ G] : IsManifold I ∞ (Quiver.Total (SingleObj G)) :=
  (arrowHomeomorph G).pullback_isManifold I ∞

/-- Extracting the group label of a total arrow in `SingleObj G` is a smooth diffeomorphism onto
`G`. -/
noncomputable def arrowDiffeomorph : Quiver.Total (SingleObj G) ≃ₘ^∞⟮I, I⟯ G :=
  (arrowHomeomorph G).pullbackDiffeomorph I ∞

@[simp]
theorem arrowDiffeomorph_apply (a : Quiver.Total (SingleObj G)) :
    arrowDiffeomorph I G a = a.hom := by
  simp [arrowDiffeomorph]

@[simp]
theorem arrowDiffeomorph_symm_apply (g : G) :
    (arrowDiffeomorph I G).symm g = ⟨SingleObj.star G, SingleObj.star G, g⟩ := by
  simp [arrowDiffeomorph]

end ArrowAtlas

section LieGroupoid

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
  (G : Type*) [Group G] [TopologicalSpace G] [ChartedSpace H G] [LieGroup I ∞ G]

private theorem isSubmersion_toSingleObj
    (f : Quiver.Total (SingleObj G) → SingleObj G) :
    Manifold.IsSubmersion I 𝓘(ℝ, Unit) ∞ f := by
  have hf : ContMDiff I 𝓘(ℝ, Unit) ∞ f :=
    contMDiff_const.congr fun a ↦ Subsingleton.elim (f a) (SingleObj.star G)
  refine (hf.isSubmersionOfComplement_of_surjective_mfderiv (by simp) fun a _ ↦ ?_).isSubmersion
  have : Subsingleton (TangentSpace 𝓘(ℝ, Unit) (f a)) := inferInstanceAs (Subsingleton Unit)
  exact ⟨0, Subsingleton.elim _ _⟩

/-- A finite-dimensional boundaryless Lie group `G` defines a Lie groupoid `SingleObj G` over one
object, with arrow manifold `G` and geometric multiplication `(g, h) ↦ g * h`. -/
instance isLieGroupoid : IsLieGroupoid 𝓘(ℝ, Unit) I (SingleObj G) where
  isSubmersion_source := isSubmersion_toSingleObj I G Quiver.Total.left
  isSubmersion_target := isSubmersion_toSingleObj I G Quiver.Total.right
  contMDiff_unit := contMDiff_const.congr fun x ↦ by cases x; rfl
  contMDiff_inverse :=
    ((arrowDiffeomorph I G).symm.contMDiff.comp (arrowDiffeomorph I G).contMDiff.inv).congr
      fun ⟨x, y, g⟩ ↦ by
        simp [Subsingleton.elim x (SingleObj.star G), Subsingleton.elim y (SingleObj.star G),
          SingleObj.inv_as_inv]
  contMDiff_mul := by
    let hsrc := isSubmersion_toSingleObj I G Quiver.Total.left
    let htgt := isSubmersion_toSingleObj I G Quiver.Total.right
    let _ := transverseFiberProductChartedSpace (by simp : (1 : ℕ∞ω) ≤ ∞)
      hsrc.contMDiff htgt.contMDiff (transverse_of_isSubmersion_left hsrc (by simp))
    have hcoe := (isSmoothEmbedding_coe_transverseFiberProduct (by simp : (1 : ℕ∞ω) ≤ ∞)
      hsrc.contMDiff htgt.contMDiff (transverse_of_isSubmersion_left hsrc (by simp))).contMDiff
    have h₁ := (arrowDiffeomorph I G).contMDiff.comp (contMDiff_fst.comp hcoe)
    have h₂ := (arrowDiffeomorph I G).contMDiff.comp (contMDiff_snd.comp hcoe)
    refine ((arrowDiffeomorph I G).symm.contMDiff.comp (h₁.mul h₂)).congr fun p ↦ ?_
    apply (arrowHomeomorph G).injective
    simp [arrowDiffeomorph_symm_apply]
  t2Space_sourceFiber _ := by
    have : T2Space G := I.t2Space_of_lieGroup ∞
    have : T2Space (Quiver.Total (SingleObj G)) := (arrowHomeomorph G).isEmbedding.t2Space
    infer_instance

/-- Composable pairs of `SingleObj G` are smoothly diffeomorphic to `G × G`, with geometric
multiplication reading directly as `(g, h) ↦ g * h`. -/
noncomputable def composablePairsDiffeomorph :
    letI := IsLieGroupoid.composablePairsChartedSpace 𝓘(ℝ, Unit) I (SingleObj G)
    {p : Quiver.Total (SingleObj G) × Quiver.Total (SingleObj G) // p.1.left = p.2.right} ≃ₘ^∞⟮
      𝓘(ℝ, Fin (finrank ℝ E + finrank ℝ E - finrank ℝ Unit) → ℝ), I.prod I⟯ G × G :=
  letI := IsLieGroupoid.composablePairsChartedSpace 𝓘(ℝ, Unit) I (SingleObj G)
  have hcoe :=
    (IsLieGroupoid.isSmoothEmbedding_coe_composablePairs 𝓘(ℝ, Unit) I (SingleObj G)).contMDiff
  { toFun := fun p ↦ (p.1.1.hom, p.1.2.hom)
    invFun := fun q ↦ ⟨(⟨SingleObj.star G, SingleObj.star G, q.1⟩,
      ⟨SingleObj.star G, SingleObj.star G, q.2⟩), rfl⟩
    left_inv := fun ⟨⟨⟨x, y, _⟩, ⟨z, w, _⟩⟩, _⟩ ↦ by cases x; cases y; cases z; cases w; rfl
    right_inv := fun _ ↦ rfl
    contMDiff_toFun :=
      (((arrowDiffeomorph I G).contMDiff.comp (contMDiff_fst.comp hcoe)).prodMk
        ((arrowDiffeomorph I G).contMDiff.comp (contMDiff_snd.comp hcoe))).congr fun _ ↦ by simp
    contMDiff_invFun :=
      (IsLieGroupoid.isSmoothEmbedding_coe_composablePairs 𝓘(ℝ, Unit) I
        (SingleObj G)).contMDiff_iff_comp.mpr <|
        (((arrowDiffeomorph I G).symm.contMDiff.comp contMDiff_fst).prodMk
          ((arrowDiffeomorph I G).symm.contMDiff.comp contMDiff_snd)).congr fun _ ↦ by simp }

@[simp]
theorem composablePairsDiffeomorph_apply
    (p : {p : Quiver.Total (SingleObj G) × Quiver.Total (SingleObj G) // p.1.left = p.2.right}) :
    letI := IsLieGroupoid.composablePairsChartedSpace 𝓘(ℝ, Unit) I (SingleObj G)
    composablePairsDiffeomorph I G p = (p.1.1.hom, p.1.2.hom) := (rfl)

@[simp]
theorem composablePairsDiffeomorph_symm_apply (q : G × G) :
    letI := IsLieGroupoid.composablePairsChartedSpace 𝓘(ℝ, Unit) I (SingleObj G)
    (composablePairsDiffeomorph I G).symm q =
      ⟨(⟨SingleObj.star G, SingleObj.star G, q.1⟩,
        ⟨SingleObj.star G, SingleObj.star G, q.2⟩), rfl⟩ := (rfl)

/-- Under `composablePairsDiffeomorph` and `arrowDiffeomorph`, geometric multiplication in
`SingleObj G` is the group product `g * h`. -/
theorem arrowDiffeomorph_mul_composablePairsDiffeomorph_symm (q : G × G) :
    letI := IsLieGroupoid.composablePairsChartedSpace 𝓘(ℝ, Unit) I (SingleObj G)
    let p := (composablePairsDiffeomorph I G).symm q
    arrowDiffeomorph I G (p.1.2.comp p.1.1 p.2.symm) = q.1 * q.2 := by
  let _ := IsLieGroupoid.composablePairsChartedSpace 𝓘(ℝ, Unit) I (SingleObj G)
  dsimp only
  rw [composablePairsDiffeomorph_symm_apply, arrowDiffeomorph_apply, ← arrowHomeomorph_apply]
  exact (arrowHomeomorph_comp G ⟨SingleObj.star G, SingleObj.star G, q.2⟩
    ⟨SingleObj.star G, SingleObj.star G, q.1⟩ rfl).trans (by simp)

end LieGroupoid

end OneObjectGroupoid

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import TauCeti.Geometry.Manifold.Groupoid.Basic
public import TauCeti.Geometry.Manifold.PullbackGroupoid
public import TauCeti.Topology.CategoryTheory.Groupoid.Examples

/-!
# Unit, pair, and one-object Lie groupoids

The native topological groupoids `Discrete M`, `Codiscrete M`, and `SingleObj G` from
`TauCeti.Topology.CategoryTheory.Groupoid.Examples` carry canonical smooth structures pulled back
along their object and arrow homeomorphisms via `Homeomorph.pullbackChartedSpace`, making each into
a `TauCeti.IsLieGroupoid`:

* the **unit Lie groupoid** `Discrete M` of a Hausdorff second-countable smooth manifold `M` has
  both object and arrow manifolds diffeomorphic to `M` (`TauCeti.UnitGroupoid.isLieGroupoid`), and
  its source projection is a local diffeomorphism (`TauCeti.UnitGroupoid.isLocalDiffeomorph_source`,
  so `Discrete M` is étale);
* the **pair Lie groupoid** `Codiscrete M` of a Hausdorff second-countable smooth manifold `M` has
  object manifold diffeomorphic to `M` and arrow manifold diffeomorphic to `M × M` in `(target,
  source)` coordinates (`TauCeti.PairGroupoid.isLieGroupoid`);
* the **one-object Lie groupoid** `SingleObj G` of a second-countable Lie group `G` has singleton
  object manifold modelled on `𝓘(ℝ, Unit)` and arrow manifold diffeomorphic to `G`
  (`TauCeti.OneObjectGroupoid.isLieGroupoid`). No separate Hausdorffness hypothesis on `G` is
  needed, as every real Lie group is Hausdorff.

## Main definitions and instances

* `TauCeti.UnitGroupoid.instChartedSpaceObjects`, `TauCeti.UnitGroupoid.instChartedSpaceArrows`,
  `TauCeti.UnitGroupoid.isLieGroupoid`: smooth structure and Lie groupoid instance on `Discrete M`.
* `TauCeti.PairGroupoid.instChartedSpaceObjects`, `TauCeti.PairGroupoid.instChartedSpaceArrows`,
  `TauCeti.PairGroupoid.isLieGroupoid`: smooth structure and Lie groupoid instance on
  `Codiscrete M`.
* `TauCeti.OneObjectGroupoid.instChartedSpaceObjects`,
  `TauCeti.OneObjectGroupoid.instChartedSpaceArrows`,
  `TauCeti.OneObjectGroupoid.isLieGroupoid`: smooth structure and Lie groupoid instance on
  `SingleObj G`.

## References

* K. C. H. Mackenzie, *General Theory of Lie Groupoids and Lie Algebroids*, London Math. Soc.
  Lecture Note Ser. 213, Cambridge University Press (2005), Examples 1.1.9–1.1.11.
* I. Moerdijk and J. Mrčun, *Introduction to Foliations and Lie Groupoids*, Cambridge Stud. Adv.
  Math. 91, Cambridge University Press (2003), Examples 5.1(1)–(3).
-/

public noncomputable section

open CategoryTheory Topology
open scoped Manifold ContDiff

namespace TauCeti

/-! ### The unit Lie groupoid `Discrete M` -/

namespace UnitGroupoid

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M] [ChartedSpace H M]

/-- The object manifold of the unit groupoid pulls back the charts of `M` along
`UnitGroupoid.objectHomeomorph`. -/
instance instChartedSpaceObjects : ChartedSpace H (Discrete M) :=
  (objectHomeomorph M).pullbackChartedSpace

instance instIsManifoldObjects {n : ℕ∞ω} [IsManifold I n M] : IsManifold I n (Discrete M) :=
  Homeomorph.pullback_isManifold I n (objectHomeomorph M)

/-- The objects of `Discrete M` are diffeomorphic to `M`. -/
def objectDiffeomorph (n : ℕ∞ω) : Discrete M ≃ₘ^n⟮I, I⟯ M :=
  (objectHomeomorph M).pullbackDiffeomorph I n

@[simp]
theorem objectDiffeomorph_apply (n : ℕ∞ω) (x : Discrete M) :
    objectDiffeomorph I M n x = x.as := by
  simp [objectDiffeomorph]

@[simp]
theorem objectDiffeomorph_symm_apply (n : ℕ∞ω) (x : M) :
    (objectDiffeomorph I M n).symm x = Discrete.mk x := by
  simp [objectDiffeomorph]

/-- The arrow manifold of the unit groupoid pulls back the charts of `M` along
`UnitGroupoid.arrowHomeomorph`. -/
instance instChartedSpaceArrows : ChartedSpace H (Quiver.Total (Discrete M)) :=
  (arrowHomeomorph M).pullbackChartedSpace

instance instIsManifoldArrows {n : ℕ∞ω} [IsManifold I n M] :
    IsManifold I n (Quiver.Total (Discrete M)) :=
  Homeomorph.pullback_isManifold I n (arrowHomeomorph M)

/-- The total arrows of `Discrete M` are diffeomorphic to `M`. -/
def arrowDiffeomorph (n : ℕ∞ω) : Quiver.Total (Discrete M) ≃ₘ^n⟮I, I⟯ M :=
  (arrowHomeomorph M).pullbackDiffeomorph I n

@[simp]
theorem arrowDiffeomorph_apply (n : ℕ∞ω) (a : Quiver.Total (Discrete M)) :
    arrowDiffeomorph I M n a = a.left.as := by
  simp [arrowDiffeomorph]

@[simp]
theorem arrowDiffeomorph_symm_apply (n : ℕ∞ω) (x : M) :
    (arrowDiffeomorph I M n).symm x = ⟨⟨x⟩, ⟨x⟩, 𝟙 _⟩ := by
  simp [arrowDiffeomorph]

/-- The source projection of `Discrete M` is a `C^n` diffeomorphism, hence a `C^n` local
diffeomorphism, with no finite-dimensionality, boundarylessness, or separation hypotheses. -/
theorem isLocalDiffeomorph_source (n : ℕ∞ω) :
    IsLocalDiffeomorph I I n (Quiver.Total.left : Quiver.Total (Discrete M) → Discrete M) := by
  convert ((arrowDiffeomorph I M n).trans (objectDiffeomorph I M n).symm).isLocalDiffeomorph
  ext a
  simp

private theorem contMDiff_inverse_aux :
    ContMDiff I I ∞ (fun a : Quiver.Total (Discrete M) ↦
      (⟨a.right, a.left, inv a.hom⟩ : Quiver.Total (Discrete M))) := by
  rw [← (arrowDiffeomorph I M ∞).contMDiff_diffeomorph_comp_iff le_rfl]
  refine (arrowDiffeomorph I M ∞).contMDiff.congr fun a ↦ ?_
  simpa using (Discrete.eq_of_hom a.hom).symm

section LieGroupoid

variable [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M]

private theorem isSubmersion_source_aux :
    Manifold.IsSubmersion I I ∞ (Quiver.Total.left : Quiver.Total (Discrete M) → Discrete M) := by
  let e : Quiver.Total (Discrete M) ≃ₘ^∞⟮I, I⟯ Discrete M :=
    (arrowDiffeomorph I M ∞).trans (objectDiffeomorph I M ∞).symm
  have he : (Quiver.Total.left : Quiver.Total (Discrete M) → Discrete M) = ⇑e := by
    ext a
    simp [e]
  rw [he]
  refine (e.contMDiff.isSubmersionOfComplement_of_surjective_mfderiv (by simp)
    fun a ↦ ?_).isSubmersion
  rw [← e.mfderivToContinuousLinearEquiv_coe (by simp)]
  exact (e.mfderivToContinuousLinearEquiv (by simp) a).surjective

variable [T2Space M] [SecondCountableTopology M]

/-- The unit groupoid on a Hausdorff second-countable smooth manifold is a Lie groupoid. -/
instance isLieGroupoid : IsLieGroupoid I I (Discrete M) where
  t2Space_objects :=
    T2Space.of_injective_continuous (objectHomeomorph M).injective (objectHomeomorph M).continuous
  secondCountableTopology_arrows := (arrowHomeomorph M).isEmbedding.secondCountableTopology
  isSubmersion_source := isSubmersion_source_aux I M
  contMDiff_unit :=
    ((arrowDiffeomorph I M ∞).symm.contMDiff.comp
      (objectDiffeomorph I M ∞).contMDiff).congr fun x ↦ by simp
  contMDiff_inverse := contMDiff_inverse_aux I M
  contMDiff_comp := by
    let := transverseFiberProductChartedSpace
      (f := (Quiver.Total.right : Quiver.Total (Discrete M) → Discrete M))
      (g := (Quiver.Total.left : Quiver.Total (Discrete M) → Discrete M)) (n := ∞) (by simp)
      ((isSubmersion_source_aux I M).contMDiff.comp (contMDiff_inverse_aux I M))
      (isSubmersion_source_aux I M).contMDiff
      (fun p _ ↦ transverse_of_isSubmersion_right _ (isSubmersion_source_aux I M) (by simp) p)
    have hemb := isSmoothEmbedding_coe_transverseFiberProduct
      (f := (Quiver.Total.right : Quiver.Total (Discrete M) → Discrete M))
      (g := (Quiver.Total.left : Quiver.Total (Discrete M) → Discrete M)) (n := ∞) (by simp)
      ((isSubmersion_source_aux I M).contMDiff.comp (contMDiff_inverse_aux I M))
      (isSubmersion_source_aux I M).contMDiff
      (fun p _ ↦ transverse_of_isSubmersion_right _ (isSubmersion_source_aux I M) (by simp) p)
    rw [← (arrowDiffeomorph I M ∞).contMDiff_diffeomorph_comp_iff le_rfl]
    exact ((arrowDiffeomorph I M ∞).contMDiff.comp (contMDiff_fst.comp hemb.contMDiff)).congr
      fun p ↦ by simp
  t2Space_sourceFiber _ :=
    have : T2Space (Quiver.Total (Discrete M)) :=
      T2Space.of_injective_continuous (arrowHomeomorph M).injective (arrowHomeomorph M).continuous
    inferInstance

end LieGroupoid

end UnitGroupoid

/-! ### The pair Lie groupoid `Codiscrete M` -/

namespace PairGroupoid

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M] [ChartedSpace H M]

/-- The object manifold of the pair groupoid pulls back the charts of `M` along
`PairGroupoid.objectHomeomorph`. -/
instance instChartedSpaceObjects : ChartedSpace H (Codiscrete M) :=
  (objectHomeomorph M).pullbackChartedSpace

instance instIsManifoldObjects {n : ℕ∞ω} [IsManifold I n M] : IsManifold I n (Codiscrete M) :=
  Homeomorph.pullback_isManifold I n (objectHomeomorph M)

/-- The objects of `Codiscrete M` are diffeomorphic to `M`. -/
def objectDiffeomorph (n : ℕ∞ω) : Codiscrete M ≃ₘ^n⟮I, I⟯ M :=
  (objectHomeomorph M).pullbackDiffeomorph I n

@[simp]
theorem objectDiffeomorph_apply (n : ℕ∞ω) (x : Codiscrete M) :
    objectDiffeomorph I M n x = x.as := by
  simp [objectDiffeomorph]

@[simp]
theorem objectDiffeomorph_symm_apply (n : ℕ∞ω) (x : M) :
    (objectDiffeomorph I M n).symm x = Codiscrete.mk x := by
  simp [objectDiffeomorph]

/-- The arrow manifold of the pair groupoid pulls back the product charts of `M × M` in
`(target, source)` coordinates along `PairGroupoid.arrowHomeomorph`. -/
instance instChartedSpaceArrows : ChartedSpace (ModelProd H H) (Quiver.Total (Codiscrete M)) :=
  (arrowHomeomorph M).pullbackChartedSpace

instance instIsManifoldArrows {n : ℕ∞ω} [IsManifold I n M] :
    IsManifold (I.prod I) n (Quiver.Total (Codiscrete M)) :=
  Homeomorph.pullback_isManifold (I.prod I) n (arrowHomeomorph M)

/-- The total arrows of `Codiscrete M` are diffeomorphic to `M × M` in `(target, source)`
coordinates. -/
def arrowDiffeomorph (n : ℕ∞ω) :
    Quiver.Total (Codiscrete M) ≃ₘ^n⟮I.prod I, I.prod I⟯ (M × M) :=
  (arrowHomeomorph M).pullbackDiffeomorph (I.prod I) n

@[simp]
theorem arrowDiffeomorph_apply (n : ℕ∞ω) (a : Quiver.Total (Codiscrete M)) :
    arrowDiffeomorph I M n a = (a.right.as, a.left.as) := by
  simp [arrowDiffeomorph]

@[simp]
theorem arrowDiffeomorph_symm_apply (n : ℕ∞ω) (p : M × M) :
    (arrowDiffeomorph I M n).symm p = ⟨⟨p.2⟩, ⟨p.1⟩, default⟩ := by
  simp [arrowDiffeomorph]

private theorem contMDiff_inverse_aux :
    ContMDiff (I.prod I) (I.prod I) ∞ (fun a : Quiver.Total (Codiscrete M) ↦
      (⟨a.right, a.left, inv a.hom⟩ : Quiver.Total (Codiscrete M))) := by
  rw [← (arrowDiffeomorph I M ∞).contMDiff_diffeomorph_comp_iff le_rfl]
  exact ((contMDiff_snd.comp (arrowDiffeomorph I M ∞).contMDiff).prodMk
    (contMDiff_fst.comp (arrowDiffeomorph I M ∞).contMDiff)).congr fun a ↦ by simp

section LieGroupoid

variable [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M]

private theorem isSubmersion_source_aux :
    Manifold.IsSubmersion (I.prod I) I ∞
      (Quiver.Total.left : Quiver.Total (Codiscrete M) → Codiscrete M) := by
  have hs : ContMDiff (I.prod I) I ∞
      (Quiver.Total.left : Quiver.Total (Codiscrete M) → Codiscrete M) :=
    ((objectDiffeomorph I M ∞).symm.contMDiff.comp
      (contMDiff_snd.comp (arrowDiffeomorph I M ∞).contMDiff)).congr fun a ↦ by simp
  refine (hs.isSubmersionOfComplement_of_surjective_mfderiv (by simp) fun a v ↦ ?_).isSubmersion
  let σ : Codiscrete M → Quiver.Total (Codiscrete M) :=
    fun x ↦ (arrowDiffeomorph I M ∞).symm (a.right.as, objectDiffeomorph I M ∞ x)
  have hσ : ContMDiff I (I.prod I) ∞ σ :=
    (arrowDiffeomorph I M ∞).symm.contMDiff.comp
      (contMDiff_const.prodMk (objectDiffeomorph I M ∞).contMDiff)
  have hσa : σ a.left = a := by
    refine Quiver.Total.ext (by simp [σ]) (by simp [σ]) ?_
    exact heq_of_eq (Subsingleton.elim _ _)
  have hlσ : (Quiver.Total.left : Quiver.Total (Codiscrete M) → Codiscrete M) ∘ σ = id := by
    ext x
    simp [σ]
  refine ⟨mfderiv I (I.prod I) σ a.left v, ?_⟩
  have hcomp := mfderiv_comp a.left (by rw [hσa]; exact hs.mdifferentiableAt (by simp))
    (hσ.mdifferentiableAt (by simp))
  rw [hσa, hlσ, mfderiv_id] at hcomp
  exact DFunLike.congr_fun hcomp.symm v

variable [T2Space M] [SecondCountableTopology M]

/-- The pair groupoid on a Hausdorff second-countable smooth manifold is a Lie groupoid. -/
instance isLieGroupoid : IsLieGroupoid I (I.prod I) (Codiscrete M) where
  t2Space_objects :=
    T2Space.of_injective_continuous (objectHomeomorph M).injective (objectHomeomorph M).continuous
  secondCountableTopology_arrows := (arrowHomeomorph M).isEmbedding.secondCountableTopology
  isSubmersion_source := isSubmersion_source_aux I M
  contMDiff_unit := by
    rw [← (arrowDiffeomorph I M ∞).contMDiff_diffeomorph_comp_iff le_rfl]
    exact ((objectDiffeomorph I M ∞).contMDiff.prodMk
      (objectDiffeomorph I M ∞).contMDiff).congr fun x ↦ by simp
  contMDiff_inverse := contMDiff_inverse_aux I M
  contMDiff_comp := by
    let := transverseFiberProductChartedSpace
      (f := (Quiver.Total.right : Quiver.Total (Codiscrete M) → Codiscrete M))
      (g := (Quiver.Total.left : Quiver.Total (Codiscrete M) → Codiscrete M)) (n := ∞) (by simp)
      ((isSubmersion_source_aux I M).contMDiff.comp (contMDiff_inverse_aux I M))
      (isSubmersion_source_aux I M).contMDiff
      (fun p _ ↦ transverse_of_isSubmersion_right _ (isSubmersion_source_aux I M) (by simp) p)
    have hemb := isSmoothEmbedding_coe_transverseFiberProduct
      (f := (Quiver.Total.right : Quiver.Total (Codiscrete M) → Codiscrete M))
      (g := (Quiver.Total.left : Quiver.Total (Codiscrete M) → Codiscrete M)) (n := ∞) (by simp)
      ((isSubmersion_source_aux I M).contMDiff.comp (contMDiff_inverse_aux I M))
      (isSubmersion_source_aux I M).contMDiff
      (fun p _ ↦ transverse_of_isSubmersion_right _ (isSubmersion_source_aux I M) (by simp) p)
    rw [← (arrowDiffeomorph I M ∞).contMDiff_diffeomorph_comp_iff le_rfl]
    exact (((contMDiff_fst.comp (arrowDiffeomorph I M ∞).contMDiff).comp
      (contMDiff_snd.comp hemb.contMDiff)).prodMk
      ((contMDiff_snd.comp (arrowDiffeomorph I M ∞).contMDiff).comp
        (contMDiff_fst.comp hemb.contMDiff))).congr fun p ↦ by simp
  t2Space_sourceFiber _ :=
    have : T2Space (Quiver.Total (Codiscrete M)) :=
      T2Space.of_injective_continuous (arrowHomeomorph M).injective (arrowHomeomorph M).continuous
    inferInstance

end LieGroupoid

end PairGroupoid

/-! ### The one-object Lie groupoid `SingleObj G` of a Lie group -/

namespace OneObjectGroupoid

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) (G : Type*) [TopologicalSpace G] [ChartedSpace H G]

/-- The singleton object space `SingleObj G` carries the canonical zero-dimensional charted-space
structure of `Unit`. -/
instance instChartedSpaceObjects : ChartedSpace Unit (SingleObj G) :=
  inferInstanceAs (ChartedSpace Unit Unit)

instance instIsManifoldObjects {n : ℕ∞ω} : IsManifold 𝓘(ℝ, Unit) n (SingleObj G) :=
  inferInstanceAs (IsManifold 𝓘(ℝ, Unit) n Unit)

/-- The arrow manifold of `SingleObj G` pulls back the charts of `G` along
`OneObjectGroupoid.arrowHomeomorph`. -/
instance instChartedSpaceArrows : ChartedSpace H (Quiver.Total (SingleObj G)) :=
  (arrowHomeomorph G).pullbackChartedSpace

instance instIsManifoldArrows {n : ℕ∞ω} [IsManifold I n G] :
    IsManifold I n (Quiver.Total (SingleObj G)) :=
  Homeomorph.pullback_isManifold I n (arrowHomeomorph G)

/-- The total arrows of `SingleObj G` are diffeomorphic to `G`. -/
def arrowDiffeomorph (n : ℕ∞ω) : Quiver.Total (SingleObj G) ≃ₘ^n⟮I, I⟯ G :=
  (arrowHomeomorph G).pullbackDiffeomorph I n

@[simp]
theorem arrowDiffeomorph_apply (n : ℕ∞ω) (a : Quiver.Total (SingleObj G)) :
    arrowDiffeomorph I G n a = a.hom := by
  simp [arrowDiffeomorph]

@[simp]
theorem arrowDiffeomorph_symm_apply (n : ℕ∞ω) (g : G) :
    (arrowDiffeomorph I G n).symm g = ⟨SingleObj.star G, SingleObj.star G, g⟩ := by
  simp [arrowDiffeomorph]

private theorem isSubmersion_source_aux [FiniteDimensional ℝ E] [I.Boundaryless]
    [IsManifold I ∞ G] :
    Manifold.IsSubmersion I 𝓘(ℝ, Unit) ∞
      (Quiver.Total.left : Quiver.Total (SingleObj G) → SingleObj G) := by
  have hs : ContMDiff I 𝓘(ℝ, Unit) ∞
      (Quiver.Total.left : Quiver.Total (SingleObj G) → SingleObj G) :=
    contMDiff_const.congr fun _ ↦ Subsingleton.elim _ (SingleObj.star G)
  exact (hs.isSubmersionOfComplement_of_surjective_mfderiv (by simp) fun _ v ↦
    ⟨0, Subsingleton.elim (α := Unit) _ v⟩).isSubmersion

section LieGroupoid

variable [Group G] [FiniteDimensional ℝ E] [I.Boundaryless] [LieGroup I ∞ G]

omit [FiniteDimensional ℝ E] [I.Boundaryless] in
private theorem contMDiff_inverse_aux :
    ContMDiff I I ∞ (fun a : Quiver.Total (SingleObj G) ↦
      (⟨a.right, a.left, inv a.hom⟩ : Quiver.Total (SingleObj G))) := by
  rw [← (arrowDiffeomorph I G ∞).contMDiff_diffeomorph_comp_iff le_rfl]
  exact (arrowDiffeomorph I G ∞).contMDiff.inv.congr fun a ↦ by simp [SingleObj.inv_as_inv]

variable [SecondCountableTopology G]

/-- Every second-countable real Lie group `G` defines a one-object Lie groupoid `SingleObj G`. -/
instance isLieGroupoid : IsLieGroupoid 𝓘(ℝ, Unit) I (SingleObj G) where
  t2Space_objects := inferInstanceAs (T2Space Unit)
  secondCountableTopology_arrows := (arrowHomeomorph G).isEmbedding.secondCountableTopology
  isSubmersion_source := isSubmersion_source_aux I G
  contMDiff_unit :=
    contMDiff_const.congr fun x ↦ by
      cases Subsingleton.elim x (SingleObj.star G)
      rfl
  contMDiff_inverse := contMDiff_inverse_aux I G
  contMDiff_comp := by
    let := transverseFiberProductChartedSpace
      (f := (Quiver.Total.right : Quiver.Total (SingleObj G) → SingleObj G))
      (g := (Quiver.Total.left : Quiver.Total (SingleObj G) → SingleObj G)) (n := ∞) (by simp)
      ((isSubmersion_source_aux I G).contMDiff.comp (contMDiff_inverse_aux I G))
      (isSubmersion_source_aux I G).contMDiff
      (fun p _ ↦ transverse_of_isSubmersion_right _ (isSubmersion_source_aux I G) (by simp) p)
    have hemb := isSmoothEmbedding_coe_transverseFiberProduct
      (f := (Quiver.Total.right : Quiver.Total (SingleObj G) → SingleObj G))
      (g := (Quiver.Total.left : Quiver.Total (SingleObj G) → SingleObj G)) (n := ∞) (by simp)
      ((isSubmersion_source_aux I G).contMDiff.comp (contMDiff_inverse_aux I G))
      (isSubmersion_source_aux I G).contMDiff
      (fun p _ ↦ transverse_of_isSubmersion_right _ (isSubmersion_source_aux I G) (by simp) p)
    rw [← (arrowDiffeomorph I G ∞).contMDiff_diffeomorph_comp_iff le_rfl]
    refine (((arrowDiffeomorph I G ∞).contMDiff.comp (contMDiff_snd.comp hemb.contMDiff)).mul
      ((arrowDiffeomorph I G ∞).contMDiff.comp (contMDiff_fst.comp hemb.contMDiff))).congr
      fun p ↦ ?_
    simpa only [Function.comp_apply, Pi.mul_apply, arrowDiffeomorph_apply,
      arrowHomeomorph_apply] using arrowHomeomorph_comp G p.1.1 p.1.2 p.2
  t2Space_sourceFiber _ := by
    have := topologicalGroup_of_lieGroup I ∞ (G := G)
    have := I.t1Space G
    have : T2Space (Quiver.Total (SingleObj G)) :=
      T2Space.of_injective_continuous (arrowHomeomorph G).injective (arrowHomeomorph G).continuous
    exact inferInstance

end LieGroupoid

end OneObjectGroupoid

end TauCeti

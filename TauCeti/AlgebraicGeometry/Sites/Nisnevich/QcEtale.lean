/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import TauCeti.AlgebraicGeometry.Sites.Nisnevich.Affine

/-!
# The quasi-compact small Nisnevich site

Let `X` be a scheme. The category `X.QcEtale` is the full subcategory of the category `X.Etale` of
étale `X`-schemes on the objects whose structure morphism is quasi-compact. It is the basis on
which the Nisnevich sheaf condition is tested by elementary distinguished squares
(Morel–Voevodsky, §3.1, Proposition 1.4); it contains the identity of `X` and the empty étale
`X`-scheme, but not, for example, an infinite coproduct of points over a point.

When `X` is quasi-separated, every affine scheme étale over `X` is quasi-compact over `X`, so every
étale `X`-scheme is Zariski-covered by objects of `X.QcEtale`: the inclusion `X.QcEtale ⥤ X.Etale`
is cover-dense for the small Nisnevich topology, and `X.QcEtale` carries the induced topology
`X.qcNisnevichTopology`, whose covering families are again those whose underlying morphisms of
schemes form a Nisnevich covering, and `X.QcEtale` is a dense subsite of the small Nisnevich site.

## Main declarations

* `AlgebraicGeometry.Scheme.QcEtale X`: the full subcategory of `X.Etale` on quasi-compact
  structure morphisms, with the inclusion `AlgebraicGeometry.Scheme.QcEtale.ι X`.
* `AlgebraicGeometry.Scheme.QcEtale.isCoverDense_smallNisnevichTopology`: for quasi-separated `X`,
  the inclusion is cover-dense for the small Nisnevich topology.
* `AlgebraicGeometry.Scheme.qcNisnevichTopology X`: the topology on `X.QcEtale` induced from the
  small Nisnevich topology, with `mem_qcNisnevichTopology_iff` and
  `ofArrows_mem_qcNisnevichTopology_iff`.

## References

* F. Morel and V. Voevodsky, *𝔸¹-homotopy theory of schemes*, Publ. Math. IHÉS 90 (1999),
  §3.1, Proposition 1.4.
-/

public noncomputable section

universe u

open CategoryTheory Limits MorphismProperty TauCeti.AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})

/-- The property of an étale `X`-scheme that its structure morphism is quasi-compact. -/
@[expose] def isQuasiCompactEtale : ObjectProperty X.Etale :=
  fun U ↦ QuasiCompact U.hom

/-- The **quasi-compact small étale site** of `X`: the full subcategory of the category `X.Etale`
of étale `X`-schemes on the objects whose structure morphism is quasi-compact. -/
@[expose] def QcEtale : Type (u + 1) :=
  (isQuasiCompactEtale X).FullSubcategory

instance : Category X.QcEtale :=
  inferInstanceAs (Category (isQuasiCompactEtale X).FullSubcategory)

namespace QcEtale

/-- The inclusion of the quasi-compact small étale site into the small étale site. -/
@[expose] def ι : X.QcEtale ⥤ X.Etale :=
  (isQuasiCompactEtale X).ι

instance : (ι X).Full :=
  inferInstanceAs (isQuasiCompactEtale X).ι.Full

instance : (ι X).Faithful :=
  inferInstanceAs (isQuasiCompactEtale X).ι.Faithful

variable {X}

/-- An étale `X`-scheme with quasi-compact structure morphism, as an object of `X.QcEtale`. -/
@[expose]
def mk (U : X.Etale) [QuasiCompact U.hom] : X.QcEtale :=
  ⟨U, ‹_›⟩

@[simp]
lemma ι_obj_mk (U : X.Etale) [QuasiCompact U.hom] : (ι X).obj (mk U) = U :=
  rfl

instance quasiCompact_ι_obj_hom (U : X.QcEtale) : QuasiCompact ((ι X).obj U).hom :=
  U.property

/-- A morphism of étale `X`-schemes between objects of `X.QcEtale` is a morphism of `X.QcEtale`. -/
@[expose]
def homMk {U V : X.QcEtale} (f : (ι X).obj U ⟶ (ι X).obj V) : U ⟶ V :=
  ObjectProperty.homMk f

@[simp]
lemma ι_map_homMk {U V : X.QcEtale} (f : (ι X).obj U ⟶ (ι X).obj V) : (ι X).map (homMk f) = f :=
  rfl

/-- Over a quasi-separated scheme, every étale `X`-scheme has a Nisnevich covering by objects of
`X.QcEtale`: the members of an affine open cover, which are quasi-compact over `X` because their
sources are affine. -/
theorem exists_mem_smallNisnevichTopology [QuasiSeparatedSpace X] (V : X.Etale) :
    ∃ (ι' : Type u) (U : ι' → X.QcEtale) (f : ∀ i, (ι X).obj (U i) ⟶ V),
      Sieve.ofArrows _ f ∈ X.smallNisnevichTopology V := by
  let 𝒰 := V.left.affineOpenCover
  refine ⟨𝒰.I₀, fun i ↦ @mk _ (MorphismProperty.Over.mk ⊤ (𝒰.f i ≫ V.hom) inferInstance)
      (quasiCompact_of_compactSpace (Y := X) (𝒰.f i ≫ V.hom)),
    fun i ↦ Over.homMk (𝒰.f i) rfl trivial, ?_⟩
  exact (ofArrows_mem_smallNisnevichTopology_iff _).mpr
    (isNisnevichCovering_of_zariski 𝒰.openCover.mem₀)

instance isCoverDense_smallNisnevichTopology [QuasiSeparatedSpace X] :
    (ι X).IsCoverDense X.smallNisnevichTopology where
  is_cover V := by
    obtain ⟨ι', U, f, hf⟩ := exists_mem_smallNisnevichTopology V
    refine GrothendieckTopology.superset_covering _ ?_ hf
    rw [Sieve.ofArrows, Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
    exact fun i ↦ Presieve.in_coverByImage _ (f i)

end QcEtale

/-- The **quasi-compact small Nisnevich site** of `X`: the topology on `X.QcEtale` induced by the
inclusion from the small Nisnevich topology. Its covering sieves are described by
`mem_qcNisnevichTopology_iff` when `X` is quasi-separated, where the inclusion is cover-dense. -/
def qcNisnevichTopology : GrothendieckTopology X.QcEtale :=
  (QcEtale.ι X).inducedTopology X.smallNisnevichTopology

variable {X} [QuasiSeparatedSpace X]

/-- A sieve is a covering sieve for the quasi-compact Nisnevich topology if and only if its image
in `X.Etale` is a covering sieve for the small Nisnevich topology. -/
theorem mem_qcNisnevichTopology_iff {U : X.QcEtale} (R : Sieve U) :
    R ∈ X.qcNisnevichTopology U ↔
      R.functorPushforward (QcEtale.ι X) ∈ X.smallNisnevichTopology ((QcEtale.ι X).obj U) :=
  Functor.mem_inducedTopology_iff_of_isCoverDense _ _ R

/-- The sieve generated by a family of morphisms of `X.QcEtale` is a covering sieve for the
quasi-compact Nisnevich topology if and only if the underlying morphisms of schemes form a
Nisnevich covering. -/
@[simp]
theorem ofArrows_mem_qcNisnevichTopology_iff {U : X.QcEtale} {ι' : Type*}
    {V : ι' → X.QcEtale} (f : ∀ i, V i ⟶ U) :
    Sieve.ofArrows V f ∈ X.qcNisnevichTopology U ↔
      IsNisnevichCovering (fun i ↦ ((QcEtale.ι X).map (f i)).left) := by
  rw [mem_qcNisnevichTopology_iff, Sieve.functorPushforward_ofArrows,
    ofArrows_mem_smallNisnevichTopology_iff]

instance QcEtale.isDenseSubsite_qcNisnevichTopology :
    Functor.IsDenseSubsite X.qcNisnevichTopology X.smallNisnevichTopology (QcEtale.ι X) := by
  dsimp [qcNisnevichTopology]
  infer_instance

end AlgebraicGeometry.Scheme

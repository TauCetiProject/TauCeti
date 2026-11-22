/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import TauCeti.AlgebraicGeometry.GroupAction.Orbit.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import TauCeti.AlgebraicGeometry.Morphisms.FiniteType
import TauCeti.AlgebraicGeometry.Morphisms.UniversallyOpen
import TauCeti.AlgebraicGeometry.Pullback.Over
import TauCeti.AlgebraicGeometry.RationalPoint.Basic
import TauCeti.AlgebraicGeometry.RationalPoint.Image
import TauCeti.AlgebraicGeometry.Scheme.KrullDimension
import TauCeti.Topology.Algebra.MulAction.Orbit
import TauCeti.Topology.Maps.OpenQuotient

/-!
# Orbits of algebraic group actions are locally closed

Let a group scheme `G` act on a scheme `X` over `S`. Global points of `G` act on the underlying
space of `X` by the translation homeomorphisms, and they preserve every geometric orbit
`TauCeti.SchemeAction.orbit G x`.

When `G` is of finite type and `X` is quasi-compact and locally Noetherian, the geometric orbit
is constructible, by Chevalley's theorem. Over an arbitrary field `k`, when `G` and `X` are
locally of finite type with quasi-compact underlying spaces and `x` is a `k`-rational point of
`X`, the geometric orbit `orbit G x` is locally closed (`isLocallyClosed_orbit`): it is open in
its closure, and its boundary is closed and of strictly smaller dimension. When `X` is locally of
finite type over `k`, the orbit of `x` covers all of `X` (including nonclosed points) if and only
if it contains every closed point of `X` (`orbit_eq_univ_iff_closedPoints_subset`); over an
algebraically closed field, this holds if and only if every rational point of `X` is a translate
`g • x` (`orbit_eq_univ_iff_forall_exists_smul`, `surjective_orbitMap_iff_forall_exists_smul`).

No algebraic closedness of `k`, smoothness, reducedness, affineness, separatedness or
connectedness hypothesis is needed, and `X` need not be irreducible. The orbit is the full
topological image of the orbit morphism, including its nonclosed points; it is not replaced by
the set of rational points. No subscheme structure on the orbit is constructed here.

Over an algebraically closed field, a closed point of the orbit lifts to a closed point of the
Jacobson scheme `G` (`Continuous.exists_isClosed_singleton_of_mem_range`), which is a rational
point of `G`; thus the rational points of `G` act transitively on the closed points of the orbit,
and local closedness follows from
`TauCeti.isLocallyClosed_of_isConstructible_of_closedPoints_transitive`. Over a general field `k`,
base change to `AlgebraicClosure k` pulls the orbit back along the projection
`X ×_k Spec (AlgebraicClosure k) ⟶ X` (`orbit_pullback`). Because every morphism to `Spec k` is
universally open and `Spec (AlgebraicClosure k) ⟶ Spec k` is surjective, this projection is an
open quotient map on underlying topological spaces, so local closedness descends by
`IsOpenQuotientMap.isLocallyClosed_preimage_iff`.

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 1.65(b), pp. 26–27, and §7.c.
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
  Topology
open scoped CategoryTheory.Obj

namespace TauCeti.SchemeAction

universe u

/-- The geometric orbit of a section is constructible when the group is of finite type and the
acted-on scheme is quasi-compact and locally Noetherian. -/
theorem isConstructible_orbit {S : Scheme.{u}} (G : Over S) {X : Over S} [MonObj G] [ModObj G X]
    [LocallyOfFiniteType G.hom] [CompactSpace G.left] [IsLocallyNoetherian X.left]
    [CompactSpace X.left] (x : 𝟙_ (Over S) ⟶ X) :
    IsConstructible (orbit G x) := by
  have : LocallyOfFiniteType (orbitMap G x).left := locallyOfFiniteType_orbitMap G x
  have h : orbit G x = Set.range (orbitMap G x).left := Set.ext (mem_orbit G x)
  simpa [h] using (orbitMap G x).left.isConstructible_image IsConstructible.univ

section AlgClosed

variable {k : Type u} [Field k] [IsAlgClosed k] (G : Over (Spec (.of k)))
  {X : Over (Spec (.of k))}

section RationalPoints

variable [MonObj G] [ModObj G X] [LocallyOfFiniteType G.hom]

/-- Over an algebraically closed field, with `G` locally of finite type, the orbit morphism sends
every closed point of `G` to a translate of `x` by a rational point of `G`. -/
theorem exists_orbitMap_left_apply_eq_smul_left_apply (x : 𝟙_ (Over (Spec (.of k))) ⟶ X)
    {c : G.left} (hc : IsClosed {c}) (a : (𝟙_ (Over (Spec (.of k)))).left) :
    ∃ g : 𝟙_ (Over (Spec (.of k))) ⟶ G, (orbitMap G x).left c = (g • x).left a := by
  let g : 𝟙_ (Over (Spec (.of k))) ⟶ G :=
    Over.homMk (U := 𝟙_ _) (V := G) (pointOfClosedPoint G.hom c hc)
      (pointOfClosedPoint_comp G.hom c _)
  refine ⟨g, ?_⟩
  rw [← left_comp_orbitMap_left, Scheme.Hom.comp_apply]
  exact congrArg _ (pointOfClosedPoint_apply G.hom c hc a).symm

/-- Over an algebraically closed field, with `G` locally of finite type, the closed points of the
geometric orbit of `x` are exactly the points underlying its translates by rational points of
`G`. -/
theorem orbit_inter_closedPoints (x : 𝟙_ (Over (Spec (.of k))) ⟶ X) :
    orbit G x ∩ closedPoints X.left =
      ⋃ g : 𝟙_ (Over (Spec (.of k))) ⟶ G, Set.range (g • x).left := by
  refine Set.Subset.antisymm (fun p ⟨hpo, hpc⟩ ↦ ?_) ?_
  · -- A closed point of the orbit is the image of a closed point of the Jacobson scheme `G`,
    -- which is a rational point of `G`.
    have : JacobsonSpace G.left := LocallyOfFiniteType.jacobsonSpace G.hom
    obtain ⟨c, hc, hfc⟩ := (orbitMap G x).left.continuous.exists_isClosed_singleton_of_mem_range
      (mem_closedPoints_iff.mp hpc).isLocallyClosed ((mem_orbit G x p).mp hpo)
    obtain ⟨g, hg⟩ :=
      exists_orbitMap_left_apply_eq_smul_left_apply G x hc (IsLocalRing.closedPoint k)
    exact Set.mem_iUnion.mpr ⟨g, _, hg.symm.trans hfc⟩
  simp only [Set.iUnion_subset_iff]
  rintro g _ ⟨a, rfl⟩
  refine ⟨smul_left_apply_mem_orbit G x g a, ?_⟩
  obtain rfl : a = IsLocalRing.closedPoint k := Subsingleton.elim (α := Spec (.of k)) _ _
  exact mem_closedPoints_iff.mpr
    (TauCeti.AlgebraicGeometry.isClosed_singleton_of_section (Over.w (g • x)))

/-- Over an algebraically closed field, with `G` locally of finite type, a rational point of `X`
lies in the geometric orbit of `x` exactly when it is a translate of `x` by a rational point of
`G`. -/
theorem left_apply_mem_orbit_iff (x y : 𝟙_ (Over (Spec (.of k))) ⟶ X)
    (a : (𝟙_ (Over (Spec (.of k)))).left) :
    y.left a ∈ orbit G x ↔ ∃ g : 𝟙_ (Over (Spec (.of k))) ⟶ G, g • x = y := by
  refine ⟨fun h ↦ ?_, fun ⟨g, hg⟩ ↦ hg ▸ smul_left_apply_mem_orbit G x g a⟩
  -- The rational point `y` is a closed point of the orbit, hence a translate `g • x` at the
  -- underlying point; two sections agreeing at a point of `Spec k` are equal.
  obtain rfl : a = IsLocalRing.closedPoint k := Subsingleton.elim (α := Spec (.of k)) _ _
  have hy : y.left (IsLocalRing.closedPoint k) ∈ orbit G x ∩ closedPoints X.left :=
    ⟨h, mem_closedPoints_iff.mpr
      (TauCeti.AlgebraicGeometry.isClosed_singleton_of_section (Over.w y))⟩
  rw [orbit_inter_closedPoints] at hy
  obtain ⟨g, b, hb⟩ := Set.mem_iUnion.mp hy
  obtain rfl : b = IsLocalRing.closedPoint k := Subsingleton.elim (α := Spec (.of k)) _ _
  refine ⟨g, Over.OverMorphism.ext ?_⟩
  simpa only [Category.id_comp] using
    (TauCeti.AlgebraicGeometry.comp_eq_comp_iff_of_section (Over.w (g • x)) (Over.w y) (𝟙 _)
      (IsLocalRing.closedPoint k)).mpr hb

end RationalPoints

section Transitivity

variable [GrpObj G] [ModObj G X] [LocallyOfFiniteType G.hom]
  [LocallyOfFiniteType X.hom]

omit [LocallyOfFiniteType X.hom] in
/-- Over an algebraically closed field, with `G` locally of finite type, any two closed
points of the geometric orbit of `x` are related by translation by a rational point of `G`. -/
theorem exists_translation_eq_of_mem_orbit_inter_closedPoints
    (x : 𝟙_ (Over (Spec (.of k))) ⟶ X) {p q : X.left}
    (hp : p ∈ orbit G x ∩ closedPoints X.left)
    (hq : q ∈ orbit G x ∩ closedPoints X.left) :
    ∃ g : 𝟙_ (Over (Spec (.of k))) ⟶ G, (translation X g).hom.left p = q := by
  let := translationMulAction G X
  rw [orbit_inter_closedPoints] at hp hq
  obtain ⟨g, a, rfl⟩ := Set.mem_iUnion.mp hp
  obtain ⟨h, b, rfl⟩ := Set.mem_iUnion.mp hq
  obtain rfl : b = a := Subsingleton.elim (α := Spec (.of k)) _ _
  refine ⟨h * g⁻¹, ?_⟩
  rw [← translationMulAction_smul, translationMulAction_smul_apply,
    mul_smul, inv_smul_smul]

/-- Over an algebraically closed field, with `G` and `X` locally of finite type, an immersed
scheme lying in the geometric orbit of `x` inherits transitivity on closed points from any family
of automorphisms intertwining the ambient translations by rational points of `G`. -/
theorem exists_eq_of_equivariant_of_range_subset_orbit
    (x : 𝟙_ (Over (Spec (.of k))) ⟶ X) {Y : Scheme.{u}} (i : Y ⟶ X.left)
    [IsImmersion i] (hrange : Set.range i ⊆ orbit G x)
    (e : (𝟙_ (Over (Spec (.of k))) ⟶ G) → (Y ≅ Y))
    (he : ∀ g, (e g).hom ≫ i = i ≫ (translation X g).hom.left)
    {y z : Y} (hy : y ∈ closedPoints Y) (hz : z ∈ closedPoints Y) :
    ∃ g, (e g).hom y = z := by
  have : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  have hp (p : Y) (hp : p ∈ closedPoints Y) :
      i p ∈ orbit G x ∩ closedPoints X.left := by
    have h : i p ∈ i '' closedPoints Y := ⟨p, hp, rfl⟩
    rw [Scheme.Hom.image_closedPoints_eq_range_inter_closedPoints] at h
    exact ⟨hrange h.1, h.2⟩
  obtain ⟨g, hg⟩ := exists_translation_eq_of_mem_orbit_inter_closedPoints G x
    (hp y hy) (hp z hz)
  refine ⟨g, i.isEmbedding.injective ?_⟩
  rw [← Scheme.Hom.comp_apply, he, Scheme.Hom.comp_apply, hg]

end Transitivity

private theorem isLocallyClosed_orbit_of_isAlgClosed [GrpObj G] [ModObj G X]
    [LocallyOfFiniteType G.hom] [CompactSpace G.left] [LocallyOfFiniteType X.hom]
    [CompactSpace X.left] (x : 𝟙_ (Over (Spec (.of k))) ⟶ X) :
    IsLocallyClosed (orbit G x) := by
  have : IsNoetherian X.left := { __ := LocallyOfFiniteType.isLocallyNoetherian X.hom }
  have : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  let := translationMulAction G X
  have := continuousConstSMul_translationMulAction (G := G) (X := X)
  refine isLocallyClosed_of_isConstructible_of_closedPoints_transitive
    (isConstructible_orbit G x) (preimage_smul_orbit · x) ?_
  intro p hp q hq
  simpa only [translationMulAction_smul] using
    exists_translation_eq_of_mem_orbit_inter_closedPoints G x hp hq

/-- Over an algebraically closed field, the geometric orbit of `x` covers all of `X` (including
nonclosed points) if and only if every rational point of `X` is a translate of `x` by a rational
point of `G`. -/
theorem orbit_eq_univ_iff_forall_exists_smul [MonObj G] [ModObj G X] [LocallyOfFiniteType G.hom]
    [LocallyOfFiniteType X.hom] (x : 𝟙_ (Over (Spec (.of k))) ⟶ X)
    [QuasiCompact (orbitMap G x).left] :
    orbit G x = Set.univ ↔
      ∀ y : 𝟙_ (Over (Spec (.of k))) ⟶ X,
        ∃ g : 𝟙_ (Over (Spec (.of k))) ⟶ G, g • x = y := by
  have : LocallyOfFiniteType ((orbitMap G x).left ≫ X.hom) := by
    rw [Over.w]; infer_instance
  rw [← surjective_orbitMap_iff_orbit_eq_univ, surjective_iff,
    (orbitMap G x).left.surjective_iff_forall_rationalPoint X.hom]
  refine ⟨fun h y ↦ ?_, fun h p hp ↦ ?_⟩
  · obtain ⟨q, hq⟩ := h y.left (by simp)
    let g : 𝟙_ (Over (Spec (.of k))) ⟶ G := Over.homMk q (by
      rw [← Over.w (orbitMap G x), ← Category.assoc, hq]
      exact Over.w y)
    refine ⟨g, Over.OverMorphism.ext ?_⟩
    exact (left_comp_orbitMap_left G x g).symm.trans hq
  · obtain ⟨g, hg⟩ := h (Over.homMk (U := 𝟙_ _) p hp)
    refine ⟨g.left, ?_⟩
    exact (left_comp_orbitMap_left G x g).trans (congrArg Over.Hom.left hg)

/-- Over an algebraically closed field, the orbit morphism is surjective on all scheme points if
and only if every rational point of `X` is a translate of `x` by a rational point of `G`. -/
theorem surjective_orbitMap_iff_forall_exists_smul [MonObj G] [ModObj G X]
    [LocallyOfFiniteType G.hom] [LocallyOfFiniteType X.hom]
    (x : 𝟙_ (Over (Spec (.of k))) ⟶ X) [QuasiCompact (orbitMap G x).left] :
    Surjective (orbitMap G x).left ↔
      ∀ y : 𝟙_ (Over (Spec (.of k))) ⟶ X,
        ∃ g : 𝟙_ (Over (Spec (.of k))) ⟶ G, g • x = y :=
  (surjective_orbitMap_iff_orbit_eq_univ G x).trans (orbit_eq_univ_iff_forall_exists_smul G x)

end AlgClosed

section Field

/-- Over a field, the geometric orbit of a rational point covers a locally finite-type scheme `X`
if and only if it contains every closed point of `X`. -/
theorem orbit_eq_univ_iff_closedPoints_subset {k : Type u} [Field k] (G : Over (Spec (.of k)))
    {X : Over (Spec (.of k))} [MonObj G] [ModObj G X] [LocallyOfFiniteType G.hom]
    [LocallyOfFiniteType X.hom] (x : 𝟙_ (Over (Spec (.of k))) ⟶ X)
    [QuasiCompact (orbitMap G x).left] :
    orbit G x = Set.univ ↔ closedPoints X.left ⊆ orbit G x := by
  refine ⟨fun h ↦ h ▸ Set.subset_univ _, fun h ↦ Set.eq_univ_iff_forall.mpr fun p ↦ ?_⟩
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  have : LocallyOfFinitePresentation (orbitMap G x).left :=
    locallyOfFinitePresentation_orbitMap G x
  have hloc : IsLocallyConstructible (orbit G x) := by
    simpa [orbit_def] using (orbitMap G x).left.isLocallyConstructible_image
      IsLocallyConstructible.univ
  obtain ⟨V, hV, hpV, -⟩ :=
    exists_isAffineOpen_mem_and_subset (TopologicalSpace.Opens.mem_top p)
  exact ((hV.isCompact.isConstructible V.isOpen).subset_iff_inter_closedPoints_subset
    (hloc.inter_of_isOpen_isCompact V.isOpen hV.isCompact)).mpr
      (fun q ⟨hqV, hqc⟩ ↦ ⟨⟨h hqc, hqV⟩, hqc⟩) hpV |>.1

variable {k : Type u} [Field k] (G : Over (Spec (.of k))) {X : Over (Spec (.of k))}
  [GrpObj G] [ModObj G X] [LocallyOfFiniteType G.hom] [CompactSpace G.left]
  [LocallyOfFiniteType X.hom] [CompactSpace X.left]

/-- Over any field, the geometric orbit of a rational point under a finite-type group scheme
acting on a finite-type scheme is locally closed. Neither algebraic closedness of the ground
field nor smoothness, reducedness, affineness or separatedness is required. -/
theorem isLocallyClosed_orbit (x : 𝟙_ (Over (Spec (.of k))) ⟶ X) :
    IsLocallyClosed (orbit G x) := by
  let f := Spec.algebraMap k (AlgebraicClosure k)
  let := (Over.pullback f).modObjObj G X
  rw [← (pullback.fst X.hom f).isOpenQuotientMap.isLocallyClosed_preimage_iff,
    ← orbit_pullback G f x]
  exact isLocallyClosed_orbit_of_isAlgClosed ((Over.pullback f).obj G) _

/-- Over any field, the geometric orbit of a rational point is open in its closure. -/
theorem isOpen_orbitClosure_preimage_orbit (x : 𝟙_ (Over (Spec (.of k))) ⟶ X) :
    IsOpen ((Subtype.val : orbitClosure G x → X.left) ⁻¹' orbit G x) := by
  rw [orbitClosure_def]
  exact (isLocallyClosed_orbit G x).isOpen_preimage_val_closure

/-- Over any field, the boundary of the geometric orbit of a rational point is closed. -/
theorem isClosed_orbitBoundary (x : 𝟙_ (Over (Spec (.of k))) ⟶ X) :
    IsClosed (orbitBoundary G x) := by
  rw [orbitBoundary_def, orbitClosure_def]
  exact isOpen_compl_iff.mp (isLocallyClosed_orbit G x).isOpen_coborder

/-- Over any field, the closure of the geometric orbit of a rational point has the same dimension
as the orbit. -/
theorem topologicalKrullDim_orbitClosure (x : 𝟙_ (Over (Spec (.of k))) ⟶ X) :
    topologicalKrullDim (orbitClosure G x) = topologicalKrullDim (orbit G x) := by
  rw [orbitClosure_def]
  exact AlgebraicGeometry.topologicalKrullDim_closure_of_isLocallyClosed X.hom
    (isLocallyClosed_orbit G x)

/-- Over any field, the boundary of the geometric orbit of a rational point has strictly smaller
dimension than the orbit, even when the group is disconnected or the orbit closure is
reducible. -/
theorem topologicalKrullDim_orbitBoundary_lt (x : 𝟙_ (Over (Spec (.of k))) ⟶ X) :
    topologicalKrullDim (orbitBoundary G x) < topologicalKrullDim (orbit G x) := by
  rw [orbitBoundary_def, orbitClosure_def]
  exact AlgebraicGeometry.topologicalKrullDim_closure_sdiff_lt_of_isLocallyClosed X.hom
    (isLocallyClosed_orbit G x)
    ⟨x.left (IsLocalRing.closedPoint k), left_apply_mem_orbit G x _⟩

end Field

end TauCeti.SchemeAction

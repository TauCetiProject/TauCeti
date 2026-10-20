/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.GroupAction.Orbit
public import TauCeti.AlgebraicGeometry.RationalPoint.Image
public import TauCeti.AlgebraicGeometry.Scheme.KrullDimension
public import TauCeti.Topology.Algebra.MulAction.Orbit

/-!
# Orbits of algebraic group actions are locally closed

Let a group scheme `G` act on a scheme `X` over `S`. Global points of `G` act on the underlying
space of `X` by the translation homeomorphisms, and they preserve every geometric orbit
`TauCeti.SchemeAction.orbit G x`.

When `G` is of finite type and `X` is quasi-compact and locally Noetherian, the geometric orbit
is constructible, by Chevalley's theorem. Over an algebraically closed field `k`, with `G` and `X`
of finite type, the rational points of the orbit are exactly the translates `g • x` of `x` by
the rational points `g` of `G`, and the closed points of the orbit are the corresponding points
of the underlying space. Hence the rational points of `G` act transitively on the closed points
of the orbit, and the orbit is locally closed: it is open in its closure, and its boundary is
closed and of strictly smaller dimension.

No smoothness, reducedness, separatedness or connectedness hypothesis is needed, and `X` need
not be irreducible. The orbit is the full topological image of the orbit morphism, including its
nonclosed points; it is not replaced by the set of rational points. No subscheme structure on
the orbit is constructed here.

The argument combines `AlgebraicGeometry.Scheme.Hom.exists_comp_eq_iff_mem_range`, which lifts
rational points along morphisms, with
`TauCeti.isLocallyClosed_of_isConstructible_of_closedPoints_transitive`, which only needs
transitivity on closed points.

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 1.65 and §7.c.
-/

public section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
  Topology

namespace TauCeti.SchemeAction

universe u

section Translation

variable {S : Scheme.{u}} (G X : Over S) [GrpObj G] [ModObj G X]

/-- The global points of a group scheme act on the underlying space of a scheme it acts on, each
acting through its translation automorphism. Install it locally to select this action. -/
@[instance_reducible]
noncomputable def translationMulAction : MulAction (𝟙_ (Over S) ⟶ G) X.left where
  smul g p := (translation X g).hom.left p
  one_smul p := by simp [HSMul.hSMul]
  mul_smul g h p := by
    simp only [HSMul.hSMul, SMul.smul, translation_mul, Iso.trans_hom, Over.comp_left,
      Scheme.Hom.comp_apply]

variable {G X}

/-- A global point acts through its translation automorphism. -/
theorem translationMulAction_smul (g : 𝟙_ (Over S) ⟶ G) (p : X.left) :
    letI := translationMulAction G X
    g • p = (translation X g).hom.left p :=
  (rfl)

/-- On the point underlying a section, the translation action is the action on sections. -/
theorem translationMulAction_smul_apply (g : 𝟙_ (Over S) ⟶ G) (y : 𝟙_ (Over S) ⟶ X)
    (a : (𝟙_ (Over S)).left) :
    letI := translationMulAction G X
    g • y.left a = (g • y).left a := by
  rw [translationMulAction_smul, ← Scheme.Hom.comp_apply, ← Over.comp_left, comp_translation_hom,
    toUnit_unit, Category.id_comp]

/-- Every global point acts by a homeomorphism. -/
theorem continuousConstSMul_translationMulAction :
    letI := translationMulAction G X
    ContinuousConstSMul (𝟙_ (Over S) ⟶ G) X.left :=
  letI := translationMulAction G X
  ⟨fun g ↦ (translation X g).hom.left.continuous⟩

/-- Translation by a global point preserves the orbit, so the orbit is invariant under the
translation action. -/
theorem preimage_smul_orbit (g : 𝟙_ (Over S) ⟶ G) (x : 𝟙_ (Over S) ⟶ X) :
    letI := translationMulAction G X
    (fun p : X.left ↦ g • p) ⁻¹' orbit G x = orbit G x := by
  let := translationMulAction G X
  rw [Set.preimage_smul, ← Set.image_smul]
  exact image_translation_orbit G g⁻¹ x

end Translation

/-- The geometric orbit of a section is constructible when the group is of finite type and the
acted-on scheme is quasi-compact and locally Noetherian. -/
theorem isConstructible_orbit {S : Scheme.{u}} (G : Over S) {X : Over S} [MonObj G] [ModObj G X]
    [LocallyOfFiniteType G.hom] [CompactSpace G.left] [IsLocallyNoetherian X.left]
    [CompactSpace X.left] (x : 𝟙_ (Over S) ⟶ X) :
    IsConstructible (orbit G x) := by
  have : LocallyOfFiniteType ((orbitMap G x).left ≫ X.hom) := by
    rw [Over.w]
    infer_instance
  have : LocallyOfFiniteType (orbitMap G x).left :=
    locallyOfFiniteType_of_comp (orbitMap G x).left X.hom
  have h : orbit G x = Set.range (orbitMap G x).left := Set.ext (mem_orbit G x)
  simpa [h] using (orbitMap G x).left.isConstructible_image IsConstructible.univ

section AlgClosed

variable {k : Type u} [Field k] [IsAlgClosed k] (G : Over (Spec (.of k)))
  {X : Over (Spec (.of k))} [GrpObj G] [ModObj G X]

section RationalPoints

variable [LocallyOfFiniteType G.hom] [LocallyOfFiniteType X.hom]

/-- Over an algebraically closed field, a rational point of `X` lies in the geometric orbit of
`x` exactly when it is a translate of `x` by a rational point of `G`. -/
theorem left_apply_mem_orbit_iff (x y : 𝟙_ (Over (Spec (.of k))) ⟶ X)
    (a : (𝟙_ (Over (Spec (.of k)))).left) :
    y.left a ∈ orbit G x ↔ ∃ g : 𝟙_ (Over (Spec (.of k))) ⟶ G, g • x = y := by
  have hw : (orbitMap G x).left ≫ X.hom = G.hom := Over.w (orbitMap G x)
  have : LocallyOfFiniteType ((orbitMap G x).left ≫ X.hom) := by
    rw [hw]
    infer_instance
  obtain rfl : a = IsLocalRing.closedPoint k := Subsingleton.elim (α := Spec (.of k)) _ _
  rw [mem_orbit]
  refine Iff.trans
    ((orbitMap G x).left.exists_comp_eq_iff_mem_range X.hom y.left (Over.w y)).symm ?_
  symm
  constructor
  · rintro ⟨g, rfl⟩
    refine ⟨g.left, ?_⟩
    have h := congrArg (fun f ↦ f.left) (comp_orbitMap G g x)
    simp only [toUnit_unit, Category.id_comp, Over.comp_left] at h
    exact h
  · rintro ⟨q, hq⟩
    have hqG : q ≫ G.hom = (𝟙_ (Over (Spec (.of k)))).hom := by
      rw [← hw, ← Category.assoc, hq, Over.w y]
    let g : 𝟙_ (Over (Spec (.of k))) ⟶ G := Over.homMk (U := 𝟙_ _) (V := G) q hqG
    refine ⟨g, ?_⟩
    ext1
    have h := congrArg (fun f ↦ f.left) (comp_orbitMap G g x)
    simp only [toUnit_unit, Category.id_comp, Over.comp_left, g, Over.homMk_left, hq] at h
    exact h.symm

/-- Over an algebraically closed field, the closed points of the geometric orbit of `x` are
exactly the points underlying its translates by rational points of `G`. -/
theorem orbit_inter_closedPoints (x : 𝟙_ (Over (Spec (.of k))) ⟶ X) :
    orbit G x ∩ closedPoints X.left =
      ⋃ g : 𝟙_ (Over (Spec (.of k))) ⟶ G, Set.range (g • x).left := by
  ext p
  simp only [Set.mem_iUnion, Set.mem_range]
  constructor
  · rintro ⟨hp, hpc⟩
    let y : 𝟙_ (Over (Spec (.of k))) ⟶ X :=
      Over.homMk (pointOfClosedPoint X.hom p (mem_closedPoints_iff.mp hpc))
        (pointOfClosedPoint_comp X.hom p _)
    have hy (a) : y.left a = p := pointOfClosedPoint_apply X.hom p _ a
    obtain ⟨g, hg⟩ := (left_apply_mem_orbit_iff G x y (IsLocalRing.closedPoint k)).mp
      ((hy _).symm ▸ hp)
    exact ⟨g, IsLocalRing.closedPoint k, hg ▸ hy _⟩
  · rintro ⟨g, a, rfl⟩
    refine ⟨(left_apply_mem_orbit_iff G x (g • x) a).mpr ⟨g, rfl⟩, ?_⟩
    obtain rfl : a = IsLocalRing.closedPoint k := Subsingleton.elim (α := Spec (.of k)) _ _
    exact ((pointEquivClosedPoint X.hom) ⟨(g • x).left, Over.w (g • x)⟩).property

end RationalPoints

variable [LocallyOfFiniteType G.hom] [CompactSpace G.left] [LocallyOfFiniteType X.hom]
  [CompactSpace X.left]

/-- Over an algebraically closed field, the geometric orbit of a rational point under a
finite-type group scheme acting on a finite-type scheme is locally closed. -/
theorem isLocallyClosed_orbit (x : 𝟙_ (Over (Spec (.of k))) ⟶ X) :
    IsLocallyClosed (orbit G x) := by
  have : IsNoetherian X.left := { __ := LocallyOfFiniteType.isLocallyNoetherian X.hom }
  have : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  let := translationMulAction G X
  have := continuousConstSMul_translationMulAction (G := G) (X := X)
  refine isLocallyClosed_of_isConstructible_of_closedPoints_transitive
    (isConstructible_orbit G x) (preimage_smul_orbit · x) ?_
  rw [orbit_inter_closedPoints]
  simp only [Set.mem_iUnion, Set.mem_range]
  rintro _ ⟨g, a, rfl⟩ _ ⟨h, b, rfl⟩
  obtain rfl : b = a := Subsingleton.elim (α := Spec (.of k)) _ _
  exact ⟨h * g⁻¹, by rw [translationMulAction_smul_apply, mul_smul, inv_smul_smul]⟩

/-- Over an algebraically closed field, the geometric orbit of a rational point is open in its
closure. -/
theorem isOpen_orbitClosure_preimage_orbit (x : 𝟙_ (Over (Spec (.of k))) ⟶ X) :
    IsOpen ((Subtype.val : orbitClosure G x → X.left) ⁻¹' orbit G x) := by
  rw [orbitClosure_def]
  exact (isLocallyClosed_orbit G x).isOpen_preimage_val_closure

/-- Over an algebraically closed field, the boundary of the geometric orbit of a rational point
is closed. -/
theorem isClosed_orbitBoundary (x : 𝟙_ (Over (Spec (.of k))) ⟶ X) :
    IsClosed (orbitBoundary G x) := by
  rw [orbitBoundary_def, orbitClosure_def]
  exact isOpen_compl_iff.mp (isLocallyClosed_orbit G x).isOpen_coborder

/-- Over an algebraically closed field, the closure of the geometric orbit of a rational point
has the same dimension as the orbit. -/
theorem topologicalKrullDim_orbitClosure (x : 𝟙_ (Over (Spec (.of k))) ⟶ X) :
    topologicalKrullDim (orbitClosure G x) = topologicalKrullDim (orbit G x) := by
  rw [orbitClosure_def]
  exact AlgebraicGeometry.topologicalKrullDim_closure_of_isLocallyClosed X.hom
    (isLocallyClosed_orbit G x)

/-- Over an algebraically closed field, the boundary of the geometric orbit of a rational point
has strictly smaller dimension than the orbit, even when the orbit closure is reducible. -/
theorem topologicalKrullDim_orbitBoundary_lt (x : 𝟙_ (Over (Spec (.of k))) ⟶ X) :
    topologicalKrullDim (orbitBoundary G x) < topologicalKrullDim (orbit G x) := by
  rw [orbitBoundary_def, orbitClosure_def]
  exact AlgebraicGeometry.topologicalKrullDim_closure_sdiff_lt_of_isLocallyClosed X.hom
    (isLocallyClosed_orbit G x) ⟨x.left (IsLocalRing.closedPoint k),
      (left_apply_mem_orbit_iff G x x _).mpr ⟨1, one_smul _ _⟩⟩

end AlgClosed

end TauCeti.SchemeAction

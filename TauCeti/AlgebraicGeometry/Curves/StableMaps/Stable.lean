/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.Node.DualGraph.Iso
public import TauCeti.AlgebraicGeometry.Curves.StableMaps.Category
public import TauCeti.AlgebraicGeometry.Curves.StableMaps.Contracted.Vertex

/-!
# Stable maps

Let `F : C ⟶ V` be a prestable map to a target `q : V ⟶ S`. Stability of `F` is a condition on
its geometric fibres: on every geometric fibre, every irreducible component on which `F` is
constant must have positive **log-canonical degree** `2g(E^ν) - 2 + #(special flags on E^ν)`,
where `E^ν` is the normalization of the component and its special flags are the markings on `E^ν`
together with the points of `E^ν` above nodes of the curve, a self-node contributing two flags.
Components on which `F` is not constant impose no condition, so the pointed source curve of a
stable map need not be stable.

Over a separably closed field `K`, these numbers are read off the dual graph of the pointed source
curve (`TauCeti.AlgebraicGeometry.PointedPrestableFamily.dualGraph`, built from
`AlgebraicGeometry.Scheme.dualGraph`). Its vertices are the irreducible components of the blowup
`ν : C^ν ⟶ C` of `C` along its singular subscheme, which separates the branches at every node; the
genus of a vertex is the genus of its component, the valence counts the points of the component
over nodes, and the markings sit on the components carrying the points over them. Its
log-canonical degree `TauCeti.DualGraph.logCanonicalDegree` is the degree above. A vertex `v` is
**contracted** by `F` when `ν ≫ F` is constant on `v`, that is, when `F` is constant on the
component `ν(v)` of `C` (`TauCeti.AlgebraicGeometry.PrestableMap.IsContractedVertex`). The map
is a **stable fibre** when every contracted vertex has positive log-canonical degree
(`TauCeti.AlgebraicGeometry.PrestableMap.IsStableFiber`).

Over an arbitrary base, `F` is **stable** (`TauCeti.AlgebraicGeometry.PrestableMap.IsStableMap`)
when its base change `F.pullback x` to every geometric point `x : Spec Ω ⟶ S`, with `Ω`
algebraically closed, is a stable fibre.

A constant map contracts every component of a curve over a field, so it is stable exactly when
the dual graphs of the geometric fibres of its pointed source are stable. Postcomposition with a
morphism of targets can only contract more components, so it can only make stability harder, and
it does not change stability when the morphism of targets has discrete fibres after every base
change, for instance when it is locally quasi-finite (finite morphisms, immersions) or
universally injective.

## Main definitions

* `TauCeti.AlgebraicGeometry.PrestableMap.IsStableFiber`: over a separably closed field, every
  contracted vertex has positive log-canonical degree.
* `TauCeti.AlgebraicGeometry.PrestableMap.IsStableMap`: every geometric fibre is stable.
* `TauCeti.AlgebraicGeometry.PrestableMap.dualGraphIsoOfIso`: the isomorphism of dual graphs of
  the source curves induced by an isomorphism of prestable maps over a separably closed field.

## Main results

In the namespace `TauCeti.AlgebraicGeometry.PrestableMap`:

* `isStableFiber_const_iff` and `isStableMap_const_iff`: a constant map is stable exactly when the
  dual graphs of the geometric fibres of its pointed source are stable.
* `IsStableFiber.of_postcomp` and `IsStableMap.of_postcomp`: if the postcomposition of a map with
  a morphism of targets is stable, so is the map.
* `isStableFiber_postcomp_iff_of_isDiscrete`: over a separably closed field, postcomposition with
  a morphism of targets with discrete fibres does not change being a stable fibre;
  `isStableFiber_postcomp_iff_of_injective`, `isStableFiber_postcomp_iff_of_locallyQuasiFinite`
  and `isStableFiber_postcomp_iff` are the injective, locally quasi-finite and universally
  injective cases.
* `isStableMap_postcomp_iff_of_isDiscrete`: postcomposition with a morphism of targets whose base
  changes to the geometric points have discrete fibres does not change stability;
  `isStableMap_postcomp_iff_of_locallyQuasiFinite` and `isStableMap_postcomp_iff` are the locally
  quasi-finite and universally injective cases.
* `isStableFiber_iff_of_iso` and `isStableMap_iff_of_iso`: being a stable fibre and being stable
  are invariant under isomorphism of prestable maps; over a field, an isomorphism induces an
  isomorphism of dual graphs (`dualGraphIsoOfIso`) matching the contracted vertices
  (`isContractedVertex_dualGraphIsoOfIso_vertexEquiv_iff`) and their log-canonical degrees.
* `IsStableMap.pullback`: the base change of a stable map along any morphism of bases is stable.

## References

* M. Kontsevich, *Enumeration of rational curves via torus actions*, in *The moduli space of
  curves*, Progr. Math. 129 (1995), 335–368, where stable maps were introduced.
* K. Behrend and Yu. Manin, *Stacks of stable maps and Gromov–Witten invariants*,
  Duke Math. J. 85 (1996), 1–60, Definition 2.1.
* W. Fulton and R. Pandharipande, *Notes on stable maps and quantum cohomology*,
  Proc. Sympos. Pure Math. 62 (1997), Part 2, 45–96, Section 1.
-/

public section

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

namespace PrestableMap

variable {V W S : Scheme.{u}} {n : ℕ}

section Fiber

variable {K : Type u} [Field K] [IsSepClosed K] {q : V ⟶ Spec (.of K)} (F : PrestableMap q n)

/-- A prestable map over a separably closed field is a **stable fibre** when every vertex of the
dual graph of its source curve that it contracts has positive log-canonical degree. -/
def IsStableFiber : Prop :=
  ∀ v, F.IsContractedVertex v → 0 < F.curve.dualGraph.logCanonicalDegree v

/-- Restatement of the definition of a stable fibre. -/
theorem isStableFiber_iff :
    F.IsStableFiber ↔ ∀ v, F.IsContractedVertex v → 0 < F.curve.dualGraph.logCanonicalDegree v :=
  Iff.rfl

/-- Over a separably closed field, a constant map is a stable fibre exactly when the dual graph of
its pointed source curve is stable. -/
@[simp]
theorem isStableFiber_const_iff (P : PointedPrestableFamily (Spec (.of K)) n)
    (σ : Spec (.of K) ⟶ V) (hσ : σ ≫ q = 𝟙 _) :
    (const P σ hσ).IsStableFiber ↔ P.dualGraph.IsStable := by
  rw [DualGraph.isStable_iff]
  exact forall_congr' fun v ↦ imp_iff_right (isContractedVertex_const P σ hσ v)

variable {F} in
/-- If the postcomposition of a map over a separably closed field with a morphism of targets is
a stable fibre, so is the map: the postcomposition contracts more vertices. -/
theorem IsStableFiber.of_postcomp {r : W ⟶ Spec (.of K)} (h : V ⟶ W) (hh : h ≫ r = q)
    (hF : (F.postcomp h hh).IsStableFiber) : F.IsStableFiber :=
  fun v hv ↦ hF v (hv.postcomp h hh)

/-- Postcomposition with a morphism of targets whose fibres are discrete does not change being a
stable fibre. -/
theorem isStableFiber_postcomp_iff_of_isDiscrete {r : W ⟶ Spec (.of K)} (h : V ⟶ W)
    (hdisc : ∀ w : W, _root_.IsDiscrete (h ⁻¹' {w})) (hh : h ≫ r = q) :
    (F.postcomp h hh).IsStableFiber ↔ F.IsStableFiber :=
  forall_congr' fun _ ↦ imp_congr_left (F.isContractedVertex_postcomp_iff_of_isDiscrete h hdisc hh)

/-- Postcomposition with a morphism of targets that is injective on points does not change being
a stable fibre. -/
theorem isStableFiber_postcomp_iff_of_injective {r : W ⟶ Spec (.of K)} (h : V ⟶ W)
    (hinj : Function.Injective h) (hh : h ≫ r = q) :
    (F.postcomp h hh).IsStableFiber ↔ F.IsStableFiber :=
  F.isStableFiber_postcomp_iff_of_isDiscrete h
    (fun _ ↦ (Set.subsingleton_singleton.preimage hinj).isDiscrete) hh

/-- Postcomposition with a locally quasi-finite morphism of targets, for instance a finite
morphism or an immersion, does not change being a stable fibre. -/
@[simp]
theorem isStableFiber_postcomp_iff_of_locallyQuasiFinite {r : W ⟶ Spec (.of K)} (h : V ⟶ W)
    [LocallyQuasiFinite h] (hh : h ≫ r = q) :
    (F.postcomp h hh).IsStableFiber ↔ F.IsStableFiber :=
  F.isStableFiber_postcomp_iff_of_isDiscrete h h.isDiscrete_preimage_singleton hh

/-- Postcomposition with a universally injective morphism of targets does not change being a
stable fibre. -/
@[simp]
theorem isStableFiber_postcomp_iff {r : W ⟶ Spec (.of K)} (h : V ⟶ W) [UniversallyInjective h]
    (hh : h ≫ r = q) : (F.postcomp h hh).IsStableFiber ↔ F.IsStableFiber :=
  F.isStableFiber_postcomp_iff_of_injective h h.injective hh

variable {F} {G : PrestableMap q n}

/-- The isomorphism of total spaces of the source curves induced by an isomorphism of prestable
maps. -/
@[expose, simps]
def totalIso (e : F ≅ G) : F.curve.total ≅ G.curve.total where
  hom := e.hom.curve.hom
  inv := e.inv.curve.hom
  hom_inv_id := by
    rw [← PointedPrestableFamily.comp_hom, ← comp_curve, e.hom_inv_id, id_curve,
      PointedPrestableFamily.id_hom]
  inv_hom_id := by
    rw [← PointedPrestableFamily.comp_hom, ← comp_curve, e.inv_hom_id, id_curve,
      PointedPrestableFamily.id_hom]

omit [IsSepClosed K] in
/-- The isomorphism of total spaces induced by an isomorphism of prestable maps carries each
marked point to the corresponding marked point. -/
theorem totalIso_hom_markingPoint (e : F ≅ G) (i : Fin n) :
    (totalIso e).hom (F.curve.markingPoint i : F.curve.total) = G.curve.markingPoint i := by
  rw [totalIso_hom, PointedPrestableFamily.coe_markingPoint,
    PointedPrestableFamily.coe_markingPoint, ← Scheme.Hom.comp_apply,
    PointedPrestableFamily.Hom.marking_comp_hom]

/-- An isomorphism of prestable maps over a separably closed field induces an isomorphism of the
dual graphs of their source curves: the isomorphism `Scheme.dualGraphIsoOfIso` induced by the
isomorphism of total spaces, which lies over `Spec K` and matches the markings. -/
def dualGraphIsoOfIso (e : F ≅ G) : F.curve.dualGraph.Iso G.curve.dualGraph :=
  Scheme.dualGraphIsoOfIso (K := K) (totalIso e) e.hom.curve.hom_comp_toBase _ _
    (totalIso_hom_markingPoint e)

/-- An isomorphism of prestable maps over a separably closed field matches the contracted
vertices: the map `G` is constant on the image of the component corresponding to `v` exactly when
`F` is constant on the image of `v`. -/
@[simp]
theorem isContractedVertex_dualGraphIsoOfIso_vertexEquiv_iff (e : F ≅ G)
    (v : F.curve.dualGraph.Vertex) :
    G.IsContractedVertex ((dualGraphIsoOfIso e).vertexEquiv v) ↔ F.IsContractedVertex v := by
  have h := Scheme.image_blowupToBase_comp_dualGraphIsoOfIso_vertexEquiv (K := K) (totalIso e)
    e.hom.curve.hom_comp_toBase _ _ (totalIso_hom_markingPoint e) G.map v
  rw [totalIso_hom, Hom.hom_comp_map] at h
  rw [isContractedVertex_iff, isContractedVertex_iff, ← h]
  rfl

/-- Being a stable fibre is invariant under isomorphism of prestable maps. -/
theorem IsStableFiber.of_iso (e : F ≅ G) (hF : F.IsStableFiber) : G.IsStableFiber := by
  intro w hw
  obtain ⟨v, rfl⟩ := (dualGraphIsoOfIso e).vertexEquiv.surjective w
  rw [DualGraph.Iso.logCanonicalDegree_vertexEquiv]
  exact hF v ((isContractedVertex_dualGraphIsoOfIso_vertexEquiv_iff e v).mp hw)

/-- Isomorphic prestable maps over a separably closed field are stable fibres simultaneously. -/
theorem isStableFiber_iff_of_iso (e : F ≅ G) : F.IsStableFiber ↔ G.IsStableFiber :=
  ⟨.of_iso e, .of_iso e.symm⟩

end Fiber

variable {q : V ⟶ S}

/-- A prestable map is **stable** when each of its geometric fibres is: for every algebraically
closed field `Ω` and every geometric point `x : Spec Ω ⟶ S`, the base change of the map to `x` is a
stable fibre, that is, every component of the geometric fibre on which the map is constant has
positive log-canonical degree. -/
def IsStableMap (F : PrestableMap q n) : Prop :=
  ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ S), (F.pullback x).IsStableFiber

/-- Restatement of the definition of a stable map. -/
theorem isStableMap_iff (F : PrestableMap q n) :
    F.IsStableMap ↔
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ S),
        (F.pullback x).IsStableFiber :=
  Iff.rfl

/-- A constant map is stable exactly when the dual graphs of the geometric fibres of its pointed
source curve are stable. -/
@[simp]
theorem isStableMap_const_iff (P : PointedPrestableFamily S n) (σ : S ⟶ V) (hσ : σ ≫ q = 𝟙 S) :
    (const P σ hσ).IsStableMap ↔
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ S),
        (P.pullback x).dualGraph.IsStable := by
  simp only [isStableMap_iff, pullback_const, isStableFiber_const_iff]

/-- If the postcomposition of a map with a morphism of targets is stable, so is the map. -/
theorem IsStableMap.of_postcomp {F : PrestableMap q n} {r : W ⟶ S} (h : V ⟶ W) (hh : h ≫ r = q)
    (hF : (F.postcomp h hh).IsStableMap) : F.IsStableMap := by
  intro Ω _ _ x
  have := hF Ω x
  rw [pullback_postcomp] at this
  exact this.of_postcomp _ _

/-- Postcomposition with a morphism of targets does not change stability when the base change
`V ×_S Spec Ω ⟶ W ×_S Spec Ω` of the morphism of targets to every geometric point has discrete
fibres. -/
theorem isStableMap_postcomp_iff_of_isDiscrete (F : PrestableMap q n) {r : W ⟶ S}
    (h : V ⟶ W) (hh : h ≫ r = q)
    (hdisc : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ S) w,
      _root_.IsDiscrete
        (Limits.pullback.map q x r x h (𝟙 _) (𝟙 S) (by simp [hh]) (by simp) ⁻¹' {w})) :
    (F.postcomp h hh).IsStableMap ↔ F.IsStableMap := by
  refine ⟨IsStableMap.of_postcomp h hh, fun hF Ω _ _ x ↦ ?_⟩
  rw [pullback_postcomp, isStableFiber_postcomp_iff_of_isDiscrete _ _ (hdisc Ω x)]
  exact hF Ω x

/-- Postcomposition with a locally quasi-finite morphism of targets, for instance a finite
morphism or an immersion, does not change stability. -/
@[simp]
theorem isStableMap_postcomp_iff_of_locallyQuasiFinite (F : PrestableMap q n) {r : W ⟶ S}
    (h : V ⟶ W) [LocallyQuasiFinite h] (hh : h ≫ r = q) :
    (F.postcomp h hh).IsStableMap ↔ F.IsStableMap :=
  F.isStableMap_postcomp_iff_of_isDiscrete h hh fun _ _ _ x ↦
    have : LocallyQuasiFinite
        (Limits.pullback.map q x r x h (𝟙 _) (𝟙 S) (by simp [hh]) (by simp)) :=
      MorphismProperty.pullbackMap (P := @LocallyQuasiFinite) ‹_› inferInstance hh.symm
        (Category.id_comp x).symm
    Scheme.Hom.isDiscrete_preimage_singleton _

/-- Postcomposition with a universally injective morphism of targets does not change
stability. -/
@[simp]
theorem isStableMap_postcomp_iff (F : PrestableMap q n) {r : W ⟶ S} (h : V ⟶ W)
    [UniversallyInjective h] (hh : h ≫ r = q) :
    (F.postcomp h hh).IsStableMap ↔ F.IsStableMap :=
  F.isStableMap_postcomp_iff_of_isDiscrete h hh fun _ _ _ x _ ↦
    have : UniversallyInjective
        (Limits.pullback.map q x r x h (𝟙 _) (𝟙 S) (by simp [hh]) (by simp)) :=
      MorphismProperty.pullbackMap (P := @UniversallyInjective) ‹_› inferInstance hh.symm
        (Category.id_comp x).symm
    (Set.subsingleton_singleton.preimage (Scheme.Hom.injective _)).isDiscrete

section Invariance

variable {T : Scheme.{u}}

/-- **Stability is invariant under isomorphism.** Isomorphic prestable maps have isomorphic base
changes to every geometric point, so they are stable simultaneously. -/
theorem isStableMap_iff_of_iso {F G : PrestableMap q n} (e : F ≅ G) :
    F.IsStableMap ↔ G.IsStableMap :=
  forall₄_congr fun _ _ _ x ↦ isStableFiber_iff_of_iso ((pullbackFunctor x).mapIso e)

/-- If two prestable maps are isomorphic and one is stable, so is the other. -/
theorem IsStableMap.of_iso {F G : PrestableMap q n} (e : F ≅ G) (hF : F.IsStableMap) :
    G.IsStableMap :=
  (isStableMap_iff_of_iso e).mp hF

/-- **Stability is stable under base change.** If a prestable map is stable, so is its base
change along any morphism `g : T ⟶ S`: a geometric point `x` of `T` gives the geometric point
`x ≫ g` of `S`, and the base change of `F.pullback g` to `x` is canonically isomorphic, after
postcomposition with the canonical isomorphism of targets, to the base change of `F` to
`x ≫ g`. -/
theorem IsStableMap.pullback {F : PrestableMap q n} (hF : F.IsStableMap) (g : T ⟶ S) :
    (F.pullback g).IsStableMap := by
  intro Ω _ _ x
  rw [← isStableFiber_postcomp_iff _ (Limits.pullbackLeftPullbackSndIso q g x).hom
    (Limits.pullbackLeftPullbackSndIso_hom_snd q g x)]
  exact (hF Ω (x ≫ g)).of_iso (pullbackCompIso F g x).symm

end Invariance

end PrestableMap

end TauCeti.AlgebraicGeometry

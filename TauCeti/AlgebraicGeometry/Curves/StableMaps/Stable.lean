/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

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

end PrestableMap

end TauCeti.AlgebraicGeometry

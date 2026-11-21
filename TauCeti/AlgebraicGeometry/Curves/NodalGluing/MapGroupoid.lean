/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.NodalGluing.FiniteAutomorphisms
public import TauCeti.AlgebraicGeometry.Curves.NodalGluing.UnstableComponent
public import Mathlib.CategoryTheory.Elements

/-!
# Maps out of marked nodal curves: isotropy groups and the map groupoid

A map from a marked nodal curve to a set `Y` is presented on its normalization, as a map
`u : (Σ i, X i) → Y`; it descends to the glued curve when it takes the same value at the two
points of every flag pair (`NodalGluing.GluedCurve.lift`). An arrow `e` between two such maps
`u` and `u'` is an isomorphism of the marked curves (an `AuxiliaryIso`, which fixes the ordered
marks and permutes the auxiliary ones) intertwining them exactly: `u' ∘ e = u`. Every arrow is
retained, including those acting trivially on the curve away from finitely many points.

The **isotropy group** of `u` is the subgroup `AuxiliaryAut.isotropy I n m u` of automorphisms
`e` of the marked curve with `u ∘ e = u`: the stabilizer of `u` for the action of the
automorphisms by precomposition. For pseudoholomorphic maps from nodal Riemann surfaces these are
the automorphism groups of prestable maps, whose finiteness is the stability condition of
Gromov–Witten theory.

That condition is a condition on the constant components only. One half of it holds for maps
into any set: if `u` is constant on a component `i`, then every diffeomorphism of `X i` fixing
its special points, extended by the identity, lies in the isotropy group
(`AuxiliaryAut.ofComponent_mem_isotropy`), injectively. So finitely many isotropy elements force
finitely many such diffeomorphisms of every constant component
(`AuxiliaryAut.finite_fixingSubgroup_of_finite_isotropy`), and a constant rational component with
at most two special points, or a constant elliptic component with none, has infinitely many
(`AuxiliaryAut.infinite_isotropy_of_encard_specialPoints_le_two`,
`AuxiliaryAut.infinite_isotropy_of_specialPoints_eq_empty`). Conversely, for finitely many
connected components, flag pairs and auxiliary labels, and for every map, if every component has
finitely many diffeomorphisms fixing its special points then the whole automorphism group of the
marked curve is finite, and so is the isotropy group
(`AuxiliaryAut.finite_isotropy_of_forall_finite_fixingSubgroup`). Under the same finiteness and
connectedness hypotheses, when `u` is constant on every component, the two halves combine: the
isotropy group is finite exactly when every component has finitely many diffeomorphisms fixing
its special points (`AuxiliaryAut.finite_isotropy_iff_of_forall_apply_eq`). The sharper
converse, which asks nothing of the nonconstant pseudoholomorphic components, needs auxiliary
marks through injective points and is not treated here.

The maps out of curves with `N` ordered and `R` auxiliary marks form the **map groupoid**
`(AuxiliaryMarkedCurve.mapFunctor I n N R Y).Elements`: the category of elements of the functor
`AuxiliaryMarkedCurve.mapFunctor`, which sends a curve to the maps out of its normalization and an
arrow `e` to `g ↦ g ∘ e⁻¹`, on the groupoid `unorderedAuxiliaryIsomorphismGroupoid` of marked
curves. Its composition and inverses are those of the groupoid of curves, its forgetful functor
to curves is faithful (Mathlib's `CategoryTheory.Functor.Elements.π`), and its automorphism groups
are the isotropy groups (`AuxiliaryMarkedCurve.autMulEquivIsotropy`).

## Main definitions

* `NodalGluing.AuxiliaryAut.isotropy`: the automorphisms of a marked nodal curve intertwining a
  map out of its normalization.
* `NodalGluing.AuxiliaryMarkedCurve.mapFunctor`: maps out of normalizations, transported along
  arrows of marked curves.
* `NodalGluing.AuxiliaryMarkedCurve.mapHomMk`: arrows of the map groupoid
  `(mapFunctor I n N R Y).Elements` from arrows of marked curves intertwining the maps.
* `NodalGluing.AuxiliaryMarkedCurve.autMulEquivIsotropy`: the automorphism groups of the map
  groupoid are the isotropy groups.

## Main results

* `NodalGluing.AuxiliaryAut.finite_fixingSubgroup_of_finite_isotropy`: a map with finite isotropy
  group has, on each component where it is constant, finitely many diffeomorphisms fixing the
  special points.
* `NodalGluing.AuxiliaryAut.finite_isotropy_of_forall_finite_fixingSubgroup`: for finitely many
  connected components, flag pairs and auxiliary labels, if every component has finitely many
  diffeomorphisms fixing the special points, every isotropy group is finite.
* `NodalGluing.AuxiliaryAut.finite_isotropy_iff_of_forall_apply_eq`: for finitely many connected
  components, flag pairs and auxiliary labels, and a map constant on every component, the
  isotropy group is finite exactly when every component is pointed stable in this sense.

## References

* John Pardon, *An algebraic approach to virtual fundamental cycles on moduli spaces of
  pseudo-holomorphic curves*, Geom. Topol. 20 (2016), 779–1034, §9.2, for stable maps on nodal
  curves, their automorphisms and the stability criterion.
* Dusa McDuff and Dietmar Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  AMS Colloquium Publications 52 (2012), §5.1, for stable maps and their automorphism groups.
-/

public noncomputable section

open Set CategoryTheory
open scoped Manifold ContDiff

namespace TauCeti

namespace NodalGluing

universe u v w y

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {n : ℕ∞ω}
  {ι Flag : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)] [∀ i, ChartedSpace H (X i)]
  {d : FlagPairData ι Flag X} {N R : Type*} {m : Marking d (N ⊕ R)}

namespace AuxiliaryAut

variable {Y : Type*}

/-! ### The isotropy group of a map -/

variable (I n m) in
/-- **The isotropy group of a map.** The automorphisms `e` of the marked nodal curve (fixing the
ordered marks and permuting the auxiliary ones) that intertwine a map `u` out of its
normalization exactly, `u ∘ e = u`: the stabilizer of `u` for the action of the automorphisms by
precomposition. -/
def isotropy (u : (Σ i, X i) → Y) : Subgroup (AuxiliaryAut I n m) where
  carrier := {e | u ∘ e = u}
  mul_mem' {e e'} he he' := funext fun x ↦ by
    rw [Function.comp_apply, mul_apply]
    exact (congrFun he (e' x)).trans (congrFun he' x)
  one_mem' := funext fun x ↦ by rw [Function.comp_apply, one_apply]
  inv_mem' {e} he := funext fun x ↦ by
    simpa only [Function.comp_apply, inv_apply, AuxiliaryIso.apply_symm_apply] using
      (congrFun he (e⁻¹ x)).symm

variable {u : (Σ i, X i) → Y} {e : AuxiliaryAut I n m}

/-- An automorphism lies in the isotropy group of `u` exactly when it intertwines `u`. -/
@[simp]
theorem mem_isotropy_iff : e ∈ isotropy I n m u ↔ u ∘ e = u :=
  Iff.rfl

/-- An automorphism lies in the isotropy group of `u` exactly when `u` takes the same value at
every point and at its image. -/
theorem mem_isotropy_iff_forall : e ∈ isotropy I n m u ↔ ∀ x, u (e x) = u x :=
  funext_iff

/-- **Constant maps.** A constant map is intertwined by every automorphism of the marked curve. -/
theorem isotropy_eq_top_of_forall_apply_eq (hu : ∀ x y, u x = u y) : isotropy I n m u = ⊤ :=
  eq_top_iff.mpr fun _ _ ↦ mem_isotropy_iff_forall.mpr fun _ ↦ hu _ _

/-! ### Components on which the map is constant -/

/-- **Automorphisms supported on a constant component.** If `u` is constant on the component `i`,
every diffeomorphism of `X i` fixing the special points of `i`, extended by the identity on the
other components, intertwines `u`. -/
theorem ofComponent_mem_isotropy {i : ι} (hu : ∀ x y : X i, u ⟨i, x⟩ = u ⟨i, y⟩)
    (φ : Diffeomorph.fixingSubgroup (I := I) (n := n) (m.specialPoints i)) :
    (ofComponent i φ : AuxiliaryAut I n m) ∈ isotropy I n m u := by
  refine mem_isotropy_iff_forall.mpr ?_
  rintro ⟨j, x⟩
  by_cases hj : j = i
  · subst hj
    rw [ofComponent_apply_mk_self]
    exact hu _ _
  · rw [ofComponent_apply_mk_of_ne hj]

/-- The diffeomorphisms of a constant component fixing its special points embed in the isotropy
group. -/
private theorem injective_ofComponent_isotropy {i : ι} (hu : ∀ x y : X i, u ⟨i, x⟩ = u ⟨i, y⟩) :
    Function.Injective fun φ : Diffeomorph.fixingSubgroup (I := I) (n := n) (m.specialPoints i) ↦
      (⟨ofComponent i φ, ofComponent_mem_isotropy hu φ⟩ : isotropy I n m u) :=
  fun _ _ h ↦ ofComponent_injective i <| Subtype.ext <| Subtype.mk.inj h

/-- **Infinitely many automorphisms of a constant component.** If `u` is constant on a component
with infinitely many diffeomorphisms fixing its special points, the isotropy group of `u` is
infinite. -/
theorem infinite_isotropy_of_infinite_fixingSubgroup {i : ι}
    (hu : ∀ x y : X i, u ⟨i, x⟩ = u ⟨i, y⟩)
    [Infinite (Diffeomorph.fixingSubgroup (I := I) (n := n) (m.specialPoints i))] :
    Infinite (isotropy I n m u) :=
  Infinite.of_injective _ (injective_ofComponent_isotropy hu)

/-- **Constant components of a map with finite isotropy are pointed stable.** If the isotropy
group of `u` is finite, then every component on which `u` is constant has finitely many
diffeomorphisms fixing its special points. -/
theorem finite_fixingSubgroup_of_finite_isotropy [Finite (isotropy I n m u)] {i : ι}
    (hu : ∀ x y : X i, u ⟨i, x⟩ = u ⟨i, y⟩) :
    Finite (Diffeomorph.fixingSubgroup (I := I) (n := n) (m.specialPoints i)) :=
  Finite.of_injective _ (injective_ofComponent_isotropy hu)

/-- **An unstable constant rational component.** If `u` is constant on a component diffeomorphic
to the projective line `OnePoint 𝕜` carrying at most two special points, the isotropy group of `u`
is infinite: Möbius transformations fixing those points act on the component. -/
theorem infinite_isotropy_of_encard_specialPoints_le_two [ProperSpace 𝕜] {i : ι}
    (hu : ∀ x y : X i, u ⟨i, x⟩ = u ⟨i, y⟩) (e : X i ≃ₘ^n⟮I, 𝓘(𝕜)⟯ OnePoint 𝕜)
    (h : (m.specialPoints i).encard ≤ 2) : Infinite (isotropy I n m u) :=
  have := e.infinite_fixingSubgroup_of_encard_le_two h
  infinite_isotropy_of_infinite_fixingSubgroup hu

/-- **An unstable constant elliptic component.** If `u` is constant on a component without
special points diffeomorphic to an infinite additive group `G` whose translations are `C^n`, such
as a complex torus, the isotropy group of `u` is infinite: the translations of `G` act on the
component. -/
theorem infinite_isotropy_of_specialPoints_eq_empty {E' : Type*} [NormedAddCommGroup E']
    [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
    {G : Type*} [AddGroup G] [TopologicalSpace G] [ChartedSpace H' G]
    [ContMDiffConstVAdd I' n G G] [Infinite G] {i : ι} (hu : ∀ x y : X i, u ⟨i, x⟩ = u ⟨i, y⟩)
    (e : X i ≃ₘ^n⟮I, I'⟯ G) (h : m.specialPoints i = ∅) : Infinite (isotropy I n m u) := by
  have : Infinite (Diffeomorph.fixingSubgroup (I := I) (n := n) (m.specialPoints i)) :=
    h ▸ e.infinite_fixingSubgroup_empty
  exact infinite_isotropy_of_infinite_fixingSubgroup hu

/-- **Pointed stable components give finite isotropy.** For finitely many connected components,
flag pairs and auxiliary labels, if every component has finitely many diffeomorphisms fixing its
special points, the isotropy group of every map `u` is finite: it is a subgroup of the
automorphism group of the marked curve, which is then finite. -/
theorem finite_isotropy_of_forall_finite_fixingSubgroup [Finite ι] [Finite Flag] [Finite R]
    [∀ i, ConnectedSpace (X i)]
    (h : ∀ i, Finite (Diffeomorph.fixingSubgroup (I := I) (n := n) (m.specialPoints i))) :
    Finite (isotropy I n m u) :=
  have := finite_iff.mpr h
  inferInstance

/-- **Stability of maps constant on every component.** For finitely many connected components,
flag pairs and auxiliary labels, if `u` is constant on every component, its isotropy group is
finite exactly when every component has finitely many diffeomorphisms fixing its special points.
Only the forward direction (`finite_fixingSubgroup_of_finite_isotropy`) uses that `u` is constant
on every component; the converse `finite_isotropy_of_forall_finite_fixingSubgroup` holds for every
map. -/
theorem finite_isotropy_iff_of_forall_apply_eq [Finite ι] [Finite Flag] [Finite R]
    [∀ i, ConnectedSpace (X i)] (hu : ∀ i (x y : X i), u ⟨i, x⟩ = u ⟨i, y⟩) :
    Finite (isotropy I n m u) ↔
      ∀ i, Finite (Diffeomorph.fixingSubgroup (I := I) (n := n) (m.specialPoints i)) :=
  ⟨fun _ i ↦ finite_fixingSubgroup_of_finite_isotropy (hu i),
    finite_isotropy_of_forall_finite_fixingSubgroup⟩

end AuxiliaryAut

/-! ### The map groupoid -/

namespace AuxiliaryMarkedCurve

variable (I n N R) in
/-- **Maps out of marked nodal curves, transported along arrows.** The functor sending a curve
with `N` ordered and `R` auxiliary marks to the type of maps from its normalization to `Y`, and an
arrow `e : C ⟶ C'` to the transport `g ↦ g ∘ e⁻¹` of maps on `C` to maps on `C'`. -/
@[expose] def mapFunctor (Y : Type y) :
    AuxiliaryMarkedCurve.{u, v, w} I n N R ⥤ Type (max u w y) where
  obj C := (Σ i, C.X i) → Y
  map {C C'} e := TypeCat.ofHom fun g ↦ g ∘ AuxiliaryIso.symm (m := C.marking) (m' := C'.marking) e
  map_id C := by
    ext g x
    simp [id_def]
  map_comp e e' := by
    ext g x
    simp [comp_def]

variable {Y : Type y}

/-- The transport of a map along an arrow `e` is the composite with `e⁻¹`. -/
@[simp]
theorem mapFunctor_map_apply {C C' : AuxiliaryMarkedCurve.{u, v, w} I n N R} (e : C ⟶ C')
    (g : (Σ i, C.X i) → Y) :
    (mapFunctor I n N R Y).map e g =
      g ∘ AuxiliaryIso.symm (m := C.marking) (m' := C'.marking) e :=
  (rfl)

variable {p q : (mapFunctor.{u, v, w, y} I n N R Y).Elements}

/-! An object `p` of the category of elements `(mapFunctor I n N R Y).Elements` is a curve
`p.obj` with `N` ordered and `R` auxiliary marks together with a map `p.val` from its
normalization to `Y`; an arrow `p ⟶ q` is an arrow `e : p.obj ⟶ q.obj` of marked curves with
`q.val ∘ e = p.val`. Since the curves form a groupoid, so does this category of elements
(`CategoryTheory.Functor.Elements.groupoid`): it is the groupoid of maps out of marked nodal
curves, with the composition and inverses of marked curves. -/

/-- **An arrow of maps intertwines them.** The underlying arrow `e` of marked curves of an arrow
`p ⟶ q` in the groupoid of maps satisfies `q.val (e x) = p.val x`. -/
@[simp]
theorem val_hom_apply (f : p ⟶ q) (x : Σ i, p.obj.X i) :
    q.val (DFunLike.coe (F := AuxiliaryIso I n p.obj.marking q.obj.marking) f.hom x) = p.val x := by
  have h : p.val ∘ AuxiliaryIso.symm (m := p.obj.marking) (m' := q.obj.marking) f.hom = q.val :=
    (mapFunctor_map_apply f.hom p.val).symm.trans f.map_val
  rw [← h]
  exact congrArg p.val (AuxiliaryIso.symm_apply_apply _ x)

/-- **An arrow of maps intertwines them**, as an equality of maps: `q.val ∘ e = p.val`. -/
theorem val_comp_hom (f : p ⟶ q) :
    q.val ∘ DFunLike.coe (F := AuxiliaryIso I n p.obj.marking q.obj.marking) f.hom = p.val :=
  funext (val_hom_apply f)

/-- **Arrows of maps from intertwining arrows of curves.** An arrow `e` of marked curves with
`q.val ∘ e = p.val` is an arrow `p ⟶ q` in the groupoid of maps. -/
def mapHomMk (e : AuxiliaryIso I n p.obj.marking q.obj.marking) (he : q.val ∘ e = p.val) :
    p ⟶ q :=
  Functor.Elements.homMk e <| (mapFunctor_map_apply e p.val).trans <| by
    rw [← he]
    funext x
    exact congrArg q.val (AuxiliaryIso.apply_symm_apply _ x)

/-- The underlying arrow of curves of `mapHomMk e he` is `e`. -/
@[simp]
theorem mapHomMk_hom (e : AuxiliaryIso I n p.obj.marking q.obj.marking) (he : q.val ∘ e = p.val) :
    (mapHomMk e he).hom = e :=
  (rfl)

variable (p) in
/-- **Automorphisms of a map are its isotropy group.** The automorphism group of `p` in the
groupoid of maps is the isotropy group of the map `p.val` in the automorphisms of the marked
curve `p.obj`. -/
def autMulEquivIsotropy :
    CategoryTheory.Aut p ≃* AuxiliaryAut.isotropy I n p.obj.marking p.val where
  toFun g := ⟨g.asIso.hom.hom, val_comp_hom g.asIso.hom⟩
  invFun e := .of <| (Groupoid.isoEquivHom p p).symm (mapHomMk e.val e.property)
  left_inv _ := Aut.ext <| CategoryTheory.Iso.ext <| Functor.Elements.hom_ext rfl
  right_inv _ := rfl
  map_mul' g g' := Subtype.ext <| by
    simp only [Aut.mul_asIso, Iso.trans_hom, Functor.Elements.comp_hom, comp_def,
      Subgroup.coe_mul, AuxiliaryAut.mul_def]

/-- The isotropy element of an automorphism of a map is its underlying automorphism of the
marked curve. -/
@[simp]
theorem coe_autMulEquivIsotropy_apply (g : CategoryTheory.Aut p) :
    (autMulEquivIsotropy p g : AuxiliaryAut I n p.obj.marking) = g.asIso.hom.hom :=
  (rfl)

/-- The automorphism of a map given by an isotropy element has that element as its underlying
automorphism of the marked curve. -/
@[simp]
theorem autMulEquivIsotropy_symm_apply_hom (e : AuxiliaryAut.isotropy I n p.obj.marking p.val) :
    ((autMulEquivIsotropy p).symm e).asIso.hom.hom = e :=
  (rfl)

end AuxiliaryMarkedCurve

end NodalGluing

end TauCeti

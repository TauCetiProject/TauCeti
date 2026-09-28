/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.CompactOpen
public import Mathlib.Topology.Homotopy.Equiv

/-!
# The mapping cylinder of a continuous map

The mapping cylinder of `f : C(X, Y)` is the cylinder `I × X` glued to `Y` by identifying the
top face `{1} × X` with its image under `f`.  It contains `X` as the bottom face `{0} × X` and
`Y` as the glued base, it retracts onto `Y` by collapsing the cylinder along `f`, and the
composite `X → Mf → Y` of the two structure maps is `f` itself.

Sliding every point of the cylinder to the top face deforms the mapping cylinder onto its base
without moving the base, so the base inclusion is a homotopy equivalence.  Together with the
factorization this replaces an arbitrary continuous map, up to homotopy equivalence of its
target, by the inclusion of a closed subspace; that inclusion is moreover a cofibration, which
is proved in `TauCeti.Topology.Homotopy.Extension.MappingCylinder`.

The quotient is presented here as the quotient by the kernel of the normalization which replaces
a point `(1, x)` of the top face by `f x`.  That makes two points of `I × X ⊕ Y` identified
exactly when the gluing forces it, which is what `TauCeti.MappingCylinder.mkCyl_eq_mkCyl_iff`
and its companions record.

## Main declarations

* `TauCeti.MappingCylinder`: the mapping cylinder, with its two structure maps
  `TauCeti.MappingCylinder.mkCyl` and `TauCeti.MappingCylinder.mkBase` and the presentation
  `TauCeti.MappingCylinder.isQuotientMap_sumElim_mkCyl_mkBase` of the underlying set as a quotient.
* `TauCeti.MappingCylinder.lift`: the universal property, together with
  `TauCeti.MappingCylinder.ind` and `TauCeti.MappingCylinder.continuous_prod_iff`, the
  continuity criterion for homotopies out of the mapping cylinder.
* `TauCeti.MappingCylinder.incl` and `TauCeti.MappingCylinder.proj`: the inclusion of the source
  and the projection onto the target, with `TauCeti.MappingCylinder.proj_comp_incl` the
  factorization of `f` and `TauCeti.MappingCylinder.isClosedEmbedding_incl`,
  `TauCeti.MappingCylinder.isClosedEmbedding_mkBase` the closedness of the two subspaces.
* `TauCeti.MappingCylinder.deformation`: **the mapping cylinder deformation retracts onto its
  base**, with `TauCeti.MappingCylinder.homotopyEquiv` the resulting homotopy equivalence with
  the target.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Chapter 0, the section "Mapping cylinders".
* G. W. Whitehead, *Elements of Homotopy Theory*, Chapter I.
-/

public section

noncomputable section

namespace TauCeti

open Set Topology unitInterval

universe u v w

variable {X : Type u} [TopologicalSpace X] {Y : Type v} [TopologicalSpace Y]

/-- The normal form of a point of `I × X ⊕ Y` for the mapping cylinder of `f`: a point of the
top face `{1} × X` of the cylinder is replaced by its image in `Y`, and every other point is
left alone.  Two points of `I × X ⊕ Y` have the same normal form exactly when the gluing of the
mapping cylinder identifies them, which is how the mapping cylinder is defined below. -/
private def cylinderNormalize (f : C(X, Y)) (a : I × X ⊕ Y) : I × X ⊕ Y :=
  a.elim (fun p => if p.1 = 1 then .inr (f p.2) else .inl p) .inr

/-- The **mapping cylinder** of `f : C(X, Y)`: the cylinder `I × X` glued to `Y` along the map
sending `(1, x)` to `f x`.

The presentation as a quotient is private to this file and is not part of the public interface:
points of the mapping cylinder come from `TauCeti.MappingCylinder.mkCyl` and
`TauCeti.MappingCylinder.mkBase`, which points they identify from
`TauCeti.MappingCylinder.mkCyl_eq_mkCyl_iff` and its companions, maps out of it from
`TauCeti.MappingCylinder.lift`, equalities of such maps from `TauCeti.MappingCylinder.hom_ext`,
and statements about all of its points from `TauCeti.MappingCylinder.ind`. -/
def MappingCylinder (f : C(X, Y)) : Type max u v :=
  Quotient (Setoid.ker (cylinderNormalize f))

namespace MappingCylinder

variable {f : C(X, Y)}

/-! The topology is transported from the private quotient; the instance is `@[no_expose]`, which
is what lets its body name the private constant. -/

@[no_expose] instance : TopologicalSpace (MappingCylinder f) :=
  inferInstanceAs (TopologicalSpace (Quotient (Setoid.ker (cylinderNormalize f))))

/-- The point of the mapping cylinder of `f` represented by a point of the cylinder `I × X`. -/
def mkCyl (f : C(X, Y)) : C(I × X, MappingCylinder f) :=
  ⟨fun p => Quotient.mk _ (.inl p), continuous_quot_mk.comp continuous_inl⟩

/-- The point of the mapping cylinder of `f` represented by a point of the target `Y`. -/
def mkBase (f : C(X, Y)) : C(Y, MappingCylinder f) :=
  ⟨fun y => Quotient.mk _ (.inr y), continuous_quot_mk.comp continuous_inr⟩

private lemma mkCyl_eq_mkCyl_iff' {p q : I × X} :
    mkCyl f p = mkCyl f q ↔ cylinderNormalize f (.inl p) = cylinderNormalize f (.inl q) :=
  Quotient.eq (r := Setoid.ker (cylinderNormalize f))

private lemma mkCyl_eq_mkBase_iff' {p : I × X} {y : Y} :
    mkCyl f p = mkBase f y ↔ cylinderNormalize f (.inl p) = cylinderNormalize f (.inr y) :=
  Quotient.eq (r := Setoid.ker (cylinderNormalize f))

private lemma mkBase_eq_mkBase_iff' {y z : Y} :
    mkBase f y = mkBase f z ↔ cylinderNormalize f (.inr y) = cylinderNormalize f (.inr z) :=
  Quotient.eq (r := Setoid.ker (cylinderNormalize f))

/-- The top face of the cylinder is glued to the base along `f`. -/
@[simp]
lemma mkCyl_one (x : X) : mkCyl f (1, x) = mkBase f (f x) :=
  mkCyl_eq_mkBase_iff'.2 (by simp [cylinderNormalize])

/-- Two points of the cylinder have the same image in the mapping cylinder exactly when they are
equal, or both lie in the top face and have the same image under `f`. -/
@[simp]
lemma mkCyl_eq_mkCyl_iff {s t : I} {x y : X} :
    mkCyl f (s, x) = mkCyl f (t, y) ↔ (s = t ∧ x = y) ∨ (s = 1 ∧ t = 1 ∧ f x = f y) := by
  rw [mkCyl_eq_mkCyl_iff']
  simp only [cylinderNormalize, Sum.elim_inl]
  split_ifs with hs ht ht <;> simp_all [Prod.ext_iff, eq_comm]

/-- A point of the cylinder and a point of the target have the same image in the mapping cylinder
exactly when the former lies in the top face and the gluing sends it to the latter. -/
@[simp]
lemma mkCyl_eq_mkBase_iff {s : I} {x : X} {y : Y} :
    mkCyl f (s, x) = mkBase f y ↔ s = 1 ∧ f x = y := by
  rw [mkCyl_eq_mkBase_iff']
  simp only [cylinderNormalize, Sum.elim_inl, Sum.elim_inr]
  split_ifs with hs <;> simp [hs]

@[simp]
lemma mkBase_inj {y z : Y} : mkBase f y = mkBase f z ↔ y = z := by
  rw [mkBase_eq_mkBase_iff']
  simp [cylinderNormalize]

lemma mkBase_injective : Function.Injective (mkBase f) := fun _ _ h => mkBase_inj.1 h

/-- Every point of the mapping cylinder comes from the cylinder or from the base. -/
@[elab_as_elim]
lemma ind {p : MappingCylinder f → Prop} (cyl : ∀ q : I × X, p (mkCyl f q))
    (base : ∀ y : Y, p (mkBase f y)) (m : MappingCylinder f) : p m := by
  induction m using Quotient.ind with
  | _ a => cases a with
    | inl q => exact cyl q
    | inr y => exact base y

/-- **The mapping cylinder is a quotient of `I × X ⊕ Y`.** -/
theorem isQuotientMap_sumElim_mkCyl_mkBase :
    IsQuotientMap (Sum.elim (⇑(mkCyl f)) (⇑(mkBase f))) := by
  have h : (Sum.elim (⇑(mkCyl f)) (⇑(mkBase f))) =
      Quotient.mk (Setoid.ker (cylinderNormalize f)) := by
    funext a
    cases a <;> rfl
  rw [h]
  exact isQuotientMap_quot_mk

/-- A subset of the mapping cylinder is closed as soon as its preimages in the cylinder and in
the base are. -/
theorem isClosed_of_preimages {S : Set (MappingCylinder f)}
    (hcyl : IsClosed (mkCyl f ⁻¹' S)) (hbase : IsClosed (mkBase f ⁻¹' S)) : IsClosed S := by
  rw [← isQuotientMap_sumElim_mkCyl_mkBase.isClosed_preimage, isClosed_sum_iff]
  exact ⟨hcyl, hbase⟩

section Lift

variable {W : Type w} [TopologicalSpace W] {g : C(I × X, W)} {h : C(Y, W)}

private lemma sumElim_cylinderNormalize (hgh : ∀ x, g (1, x) = h (f x)) (a : I × X ⊕ Y) :
    Sum.elim (⇑g) (⇑h) (cylinderNormalize f a) = Sum.elim (⇑g) (⇑h) a := by
  cases a with
  | inl p =>
    simp only [cylinderNormalize, Sum.elim_inl]
    split_ifs with hp
    · rw [Sum.elim_inr, ← hgh p.2, ← hp]
    · rfl
  | inr y => rfl

/-- **The universal property of the mapping cylinder.**  A map on the cylinder and a map on the
base which agree on the glued top face assemble into a map out of the mapping cylinder. -/
def lift (g : C(I × X, W)) (h : C(Y, W)) (hgh : ∀ x, g (1, x) = h (f x)) :
    C(MappingCylinder f, W) :=
  ⟨Quotient.lift (Sum.elim (⇑g) (⇑h)) fun a b hab => by
      rw [← sumElim_cylinderNormalize hgh a, ← sumElim_cylinderNormalize hgh b, hab],
    Continuous.quotient_lift (g.continuous.sumElim h.continuous) _⟩

@[simp]
lemma lift_mkCyl (hgh : ∀ x, g (1, x) = h (f x)) (p : I × X) :
    lift g h hgh (mkCyl f p) = g p := (rfl)

@[simp]
lemma lift_mkBase (hgh : ∀ x, g (1, x) = h (f x)) (y : Y) :
    lift g h hgh (mkBase f y) = h y := (rfl)

/-- **Extensionality for maps out of the mapping cylinder.**  Two continuous maps out of the
mapping cylinder which agree on the cylinder and on the base are equal. -/
@[ext]
theorem hom_ext {F G : C(MappingCylinder f, W)} (cyl : ∀ p : I × X, F (mkCyl f p) = G (mkCyl f p))
    (base : ∀ y : Y, F (mkBase f y) = G (mkBase f y)) : F = G := by
  refine ContinuousMap.ext fun m => ?_
  induction m using ind with
  | cyl q => exact cyl q
  | base y => exact base y

/-- **Uniqueness in the universal property of the mapping cylinder.**  A map out of the mapping
cylinder is determined by its restrictions to the cylinder and to the base. -/
theorem lift_unique (hgh : ∀ x, g (1, x) = h (f x)) {F : C(MappingCylinder f, W)}
    (hcyl : ∀ p : I × X, F (mkCyl f p) = g p) (hbase : ∀ y : Y, F (mkBase f y) = h y) :
    F = lift g h hgh :=
  hom_ext (fun p => by rw [hcyl, lift_mkCyl]) fun y => by rw [hbase, lift_mkBase]

end Lift

/-- **Continuity criterion for maps out of `Z × Mf`.**  For a locally compact space `Z`, a map
out of the product of `Z` with the mapping cylinder is continuous exactly when it is continuous
on `Z × (I × X)` and on `Z × Y`.  For `Z = I` this builds homotopies out of the mapping
cylinder. -/
theorem continuous_prod_iff {Z W : Type*} [TopologicalSpace Z] [LocallyCompactSpace Z]
    [TopologicalSpace W] {g : Z × MappingCylinder f → W} :
    Continuous g ↔ (Continuous fun q : Z × (I × X) => g (q.1, mkCyl f q.2)) ∧
      Continuous fun q : Z × Y => g (q.1, mkBase f q.2) := by
  refine ⟨fun hg => ⟨hg.comp (by fun_prop), hg.comp (by fun_prop)⟩,
    fun ⟨hcyl, hbase⟩ => isQuotientMap_sumElim_mkCyl_mkBase.continuous_lift_prod_right ?_⟩
  -- Split the product of `Z` with `I × X ⊕ Y` into the products of `Z` with the two summands.
  rw [← Homeomorph.prodSumDistrib.symm.comp_continuous_iff', continuous_sum_dom]
  exact ⟨hcyl, hbase⟩

/-- The inclusion of the source of `f` into its mapping cylinder as the bottom face of the
cylinder. -/
def incl (f : C(X, Y)) : C(X, MappingCylinder f) := (mkCyl f).comp ⟨fun x => (0, x), by fun_prop⟩

/-- The projection of the mapping cylinder of `f` onto its target: the cylinder is collapsed
along `f`. -/
def proj (f : C(X, Y)) : C(MappingCylinder f, Y) :=
  lift (f.comp (⟨Prod.snd, continuous_snd⟩ : C(I × X, X))) (ContinuousMap.id Y) fun _ => rfl

@[simp]
lemma incl_apply (x : X) : incl f x = mkCyl f (0, x) := (rfl)

@[simp]
lemma proj_mkCyl (p : I × X) : proj f (mkCyl f p) = f p.2 := (rfl)

@[simp]
lemma proj_mkBase (y : Y) : proj f (mkBase f y) = y := (rfl)

@[simp]
lemma proj_comp_mkBase : (proj f).comp (mkBase f) = ContinuousMap.id Y := by
  ext y
  rw [ContinuousMap.comp_apply, proj_mkBase, ContinuousMap.id_apply]

/-- **The mapping cylinder factors `f`** as its inclusion into the cylinder followed by the
projection onto the target. -/
@[simp]
lemma proj_comp_incl : (proj f).comp (incl f) = f := by
  ext x
  rw [ContinuousMap.comp_apply, incl_apply, proj_mkCyl]

/-- A point of the cylinder lies in the bottom face exactly when its image in the mapping
cylinder lies in the image of the source. -/
lemma mkCyl_mem_range_incl_iff {s : I} {x : X} :
    mkCyl f (s, x) ∈ Set.range (incl f) ↔ s = 0 := by
  constructor
  · rintro ⟨z, hz⟩
    rw [incl_apply, mkCyl_eq_mkCyl_iff] at hz
    obtain ⟨h, -⟩ | ⟨h, -⟩ := hz
    · exact h.symm
    · exact absurd h (zero_ne_one : (0 : I) ≠ 1)
  · rintro rfl
    exact ⟨x, incl_apply x⟩

/-- No point of the base of the mapping cylinder comes from the source. -/
lemma mkBase_notMem_range_incl (y : Y) : mkBase f y ∉ Set.range (incl f) := by
  rintro ⟨x, hx⟩
  rw [incl_apply, mkCyl_eq_mkBase_iff] at hx
  exact (zero_ne_one : (0 : I) ≠ 1) hx.1

/-- The preimage of the image of the source under the cylinder map is the bottom face. -/
private lemma preimage_mkCyl_range_incl :
    mkCyl f ⁻¹' Set.range (incl f) = (fun p : I × X => p.1) ⁻¹' {0} := by
  ext ⟨s, x⟩
  simp only [Set.mem_preimage, Set.mem_singleton_iff, mkCyl_mem_range_incl_iff]

/-- The image of the source of `f` in the mapping cylinder is closed. -/
theorem isClosed_range_incl : IsClosed (Set.range (incl f)) := by
  refine isClosed_of_preimages ?_ ?_
  · rw [preimage_mkCyl_range_incl]
    exact isClosed_singleton.preimage continuous_fst
  · convert isClosed_empty using 1
    ext y
    simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
    exact mkBase_notMem_range_incl y

/-- **The source of `f` is a closed subspace of its mapping cylinder.** -/
theorem isClosedEmbedding_incl : IsClosedEmbedding (incl f) := by
  refine .of_continuous_injective_isClosedMap (incl f).continuous (fun x x' hx => ?_)
    fun K hK => isClosed_of_preimages ?_ ?_
  · rw [incl_apply, incl_apply, mkCyl_eq_mkCyl_iff] at hx
    obtain ⟨-, h⟩ | ⟨h, -⟩ := hx
    · exact h
    · exact absurd h (zero_ne_one : (0 : I) ≠ 1)
  · have hpre : mkCyl f ⁻¹' (incl f '' K) =
        (fun p : I × X => p.1) ⁻¹' {0} ∩ (fun p : I × X => p.2) ⁻¹' K := by
      ext ⟨s, x⟩
      constructor
      · rintro ⟨z, hz, hzx⟩
        rw [incl_apply, mkCyl_eq_mkCyl_iff] at hzx
        obtain ⟨h, rfl⟩ | ⟨h, -⟩ := hzx
        · exact ⟨h.symm, hz⟩
        · exact absurd h (zero_ne_one : (0 : I) ≠ 1)
      · rintro ⟨rfl, hx⟩
        exact ⟨x, hx, incl_apply x⟩
    rw [hpre]
    exact (isClosed_singleton.preimage continuous_fst).inter (hK.preimage continuous_snd)
  · convert isClosed_empty using 1
    ext y
    simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
    rintro ⟨x, -, hx⟩
    exact mkBase_notMem_range_incl (f := f) y ⟨x, hx⟩

/-- **The target of `f` is a closed subspace of its mapping cylinder.** -/
theorem isClosedEmbedding_mkBase : IsClosedEmbedding (mkBase f) := by
  refine .of_continuous_injective_isClosedMap (mkBase f).continuous mkBase_injective
    fun K hK => isClosed_of_preimages ?_ ?_
  · have hpre : mkCyl f ⁻¹' (mkBase f '' K) =
        (fun p : I × X => p.1) ⁻¹' {1} ∩ (fun p : I × X => f p.2) ⁻¹' K := by
      ext ⟨s, x⟩
      constructor
      · rintro ⟨y, hy, hyx⟩
        obtain ⟨h1, rfl⟩ := mkCyl_eq_mkBase_iff.1 hyx.symm
        exact ⟨h1, hy⟩
      · rintro ⟨rfl, hx⟩
        exact ⟨f x, hx, (mkCyl_eq_mkBase_iff.2 ⟨rfl, rfl⟩).symm⟩
    rw [hpre]
    exact (isClosed_singleton.preimage continuous_fst).inter
      (hK.preimage (f.continuous.comp continuous_snd))
  · convert hK using 1
    ext y
    simp

section Deformation

/-- The map deforming the mapping cylinder at time `t`: a point of the cylinder slides towards
the top face, and the base stays where it is. -/
private def deformationMap (f : C(X, Y)) (t : I) :
    C(MappingCylinder f, MappingCylinder f) :=
  lift ⟨fun q => mkCyl f (Set.Icc.convexComb q.1 1 t, q.2), (mkCyl f).continuous.comp
      (((Set.Icc.continuous_convexComb_prod).comp
        (continuous_fst.prodMk (continuous_const.prodMk continuous_const))).prodMk
          continuous_snd)⟩
    (mkBase f) fun x => by
      rw [ContinuousMap.coe_mk, Set.Icc.convexComb_eq, mkCyl_one]

private lemma deformationMap_mkCyl (t : I) (q : I × X) :
    deformationMap f t (mkCyl f q) = mkCyl f (Set.Icc.convexComb q.1 1 t, q.2) := (rfl)

private lemma deformationMap_mkBase (t : I) (y : Y) :
    deformationMap f t (mkBase f y) = mkBase f y := (rfl)

private lemma continuous_deformationMap :
    Continuous fun p : I × MappingCylinder f => deformationMap f p.1 p.2 := by
  rw [continuous_prod_iff]
  refine ⟨?_, ?_⟩
  · simp only [deformationMap_mkCyl]
    exact (mkCyl f).continuous.comp
      ((Set.Icc.continuous_convexComb_prod.comp ((continuous_fst.comp continuous_snd).prodMk
        (continuous_const.prodMk continuous_fst))).prodMk (continuous_snd.comp continuous_snd))
  · simp only [deformationMap_mkBase]
    exact (mkBase f).continuous.comp continuous_snd

/-- **The mapping cylinder deformation retracts onto its base.**  Sliding every point of the
cylinder to the top face is a homotopy from the identity of the mapping cylinder to the
projection followed by the base inclusion, and it does not move the base. -/
def deformation (f : C(X, Y)) :
    (ContinuousMap.id (MappingCylinder f)).HomotopyRel ((mkBase f).comp (proj f))
      (Set.range (mkBase f)) where
  toFun p := deformationMap f p.1 p.2
  continuous_toFun := continuous_deformationMap
  map_zero_left m := by
    induction m using ind with
    | cyl q => rw [deformationMap_mkCyl, Set.Icc.convexComb_zero, ContinuousMap.id_apply]
    | base y => rw [deformationMap_mkBase, ContinuousMap.id_apply]
  map_one_left m := by
    induction m using ind with
    | cyl q =>
      rw [deformationMap_mkCyl, Set.Icc.convexComb_one, mkCyl_one, ContinuousMap.comp_apply,
        proj_mkCyl]
    | base y => rw [deformationMap_mkBase, ContinuousMap.comp_apply, proj_mkBase]
  prop' t := by
    rintro m ⟨y, rfl⟩
    rw [ContinuousMap.coe_mk, deformationMap_mkBase, ContinuousMap.id_apply]

/-- **The mapping cylinder of `f` is homotopy equivalent to the target of `f`**, by the
projection and the base inclusion. -/
def homotopyEquiv (f : C(X, Y)) : ContinuousMap.HomotopyEquiv (MappingCylinder f) Y where
  toFun := proj f
  invFun := mkBase f
  left_inv := ⟨(deformation f).toHomotopy.symm⟩
  right_inv := by rw [proj_comp_mkBase]

/-- The homotopy equivalence with the target is the projection. -/
@[simp]
lemma homotopyEquiv_apply (m : MappingCylinder f) : homotopyEquiv f m = proj f m := (rfl)

/-- The homotopy inverse of the projection is the base inclusion. -/
@[simp]
lemma homotopyEquiv_symm_apply (y : Y) : (homotopyEquiv f).symm y = mkBase f y := (rfl)

end Deformation

end MappingCylinder

end TauCeti

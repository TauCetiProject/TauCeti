/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cylinder
public import TauCeti.Topology.MappingTorus.LocalProduct
import Mathlib.Algebra.Order.Round
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Topology.Algebra.Order.Floor

/-!
# The relative homology of a mapping torus modulo a fibre

Let `T` be the mapping torus of a homeomorphism `φ : F ≃ₜ F`, and regard `F` as the fibre of `T`
over `0` in the circle (`TauCeti.MappingTorus.fiber`).  The cylinder `F × I` maps onto `T` by
`(x, t) ↦ [φ x, t]`; this is the monodromy homotopy `TauCeti.MappingTorus.monodromyHomotopy` read
as a map out of the cylinder.  It sends the ends `F × ∂I` into the fibre, so it is a map of pairs
`(F × I, F × ∂I) ⟶ (T, F)` (`TauCeti.MappingTorus.cylinderPairMap`).  On the bottom end it is the
fibre inclusion after `φ`, and on the top end it is the fibre inclusion.

This map induces isomorphisms on relative singular homology in every degree
(`TauCeti.MappingTorus.isIso_singularHomologyMap_cylinderPairMap`), with coefficients in an object
of an abelian category with coproducts.  Combined with the homology of the cylinder modulo its
ends, this gives `Hₙ₊₁(T, F) ≅ Hₙ(F)` (`TauCeti.MappingTorus.singularHomologyFiberPairIso`) and
`H₀(T, F) = 0`.  Under this isomorphism the connecting morphism `Hₙ₊₁(T, F) ⟶ Hₙ(F)` of the pair
is `id - φ_*` followed by the map induced by the fibre inclusion
(`TauCeti.MappingTorus.singularHomologyδ_fiberPair`).  This is the form in which the endomorphism
`id - φ_*` of the Wang sequence of the mapping torus enters the long exact sequence of the pair
`(T, F)`.

The proof is the argument showing that the quotient map of a good pair induces isomorphisms on
relative homology.  Both pairs are first thickened.  In `T`, the heights within `1/3` of an
integer form an open neighbourhood of the fibre; in the cylinder, the heights within `1/3` of `0`
or `1` form an open neighbourhood of the ends.  Collapsing these heights onto the nearest integer is
a deformation of each space, so thickening does not change relative homology
(`TopPair.isIso_singularHomologyMap_ofSubsetMap_id_of_homotopy`).  The open cylinder `F × (0, 1)`
embeds openly in `T`, with image the complement of the fibre
(`TauCeti.MappingTorus.isOpenEmbedding_mk_Ioo` and `TauCeti.MappingTorus.range_mk_Ioo`).  So
excision identifies both thickened pairs with the same pair on the open cylinder
(`TopPair.isIso_singularHomologyMap_excisionMap` and
`TopPair.isIso_singularHomologyMap_of_open_cover`).

## Main declarations

* `TauCeti.MappingTorus.fiberPair φ`: the pair `(T, F)`.
* `TauCeti.MappingTorus.fiberPairIncl φ`: the fibre inclusion `F ⟶ fiber φ`, an isomorphism
  (`TauCeti.MappingTorus.isIso_fiberPairIncl`).
* `TauCeti.MappingTorus.cylinderPairMap φ`: the map of pairs `(F × I, F × ∂I) ⟶ (T, F)`.
* `TauCeti.MappingTorus.isIso_singularHomologyMap_cylinderPairMap`: it induces isomorphisms on
  relative singular homology.
* `TauCeti.MappingTorus.singularHomologyFiberPairIso`: `Hₙ₊₁(T, F) ≅ Hₙ(F)`.
* `TauCeti.MappingTorus.singularHomologyδ_fiberPair`: the connecting morphism of `(T, F)` is
  `id - φ_*` followed by the fibre inclusion.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.1, Proposition 2.22 and its proof (good pairs), and
  Section 2.2 (the homology of a mapping torus).
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology Topology unitInterval Set

universe w v u

namespace TauCeti.MappingTorus

variable {F : Type w} [TopologicalSpace F] (φ : F ≃ₜ F)

/-- The pair `(T, F)` formed by the mapping torus `T` of `φ` and its fibre over `0`. -/
abbrev fiberPair : TopPair.{w} := TopPair.ofSubset (X := TopCat.of (MappingTorus φ)) (fiber φ)

/-- The fibre inclusion `MappingTorus.incl`, as a map into the subspace of `fiberPair φ`. -/
def fiberPairIncl : TopCat.of F ⟶ (fiberPair φ).snd :=
  TopCat.ofHom ⟨fun x ↦ ⟨incl φ x, incl_mem_fiber φ x⟩, (incl φ).continuous.subtype_mk _⟩

@[simp]
lemma fiberPairIncl_apply (x : F) : (fiberPairIncl φ x).1 = incl φ x := (rfl)

/-- The fibre inclusion into the subspace, followed by its inclusion into the mapping torus, is
the usual fibre inclusion. -/
@[simp]
lemma fiberPairIncl_comp_map :
    fiberPairIncl φ ≫ TopCat.ofHom (ContinuousMap.subtypeVal (fiber φ)) =
      TopCat.ofHom (incl φ) :=
  TopCat.ext fun x ↦ fiberPairIncl_apply φ x

/-- The fibre inclusion is an isomorphism onto the fibre: it is `MappingTorus.fiberHomeomorph`. -/
instance isIso_fiberPairIncl : IsIso (fiberPairIncl φ) := by
  have h : fiberPairIncl φ =
      (TopCat.isoOfHomeo (X := TopCat.of F) (Y := (fiberPair φ).snd) (fiberHomeomorph φ)).hom :=
    TopCat.ext fun x ↦ Subtype.ext (coe_fiberHomeomorph_apply φ x).symm
  rw [h]
  infer_instance

/-- The map `(x, t) ↦ [φ x, t]` from the cylinder onto the mapping torus.  It is the monodromy
homotopy `MappingTorus.monodromyHomotopy`, read as a map out of the cylinder `F × I`. -/
def cylinderMap : C(F × I, MappingTorus φ) :=
  (monodromyHomotopy φ).toContinuousMap.comp ContinuousMap.prodSwap

@[simp]
lemma cylinderMap_apply (p : F × I) : cylinderMap φ p = mk φ (φ p.1) p.2 :=
  monodromyHomotopy_apply φ p.2 p.1

private lemma cylinderMap_mem_fiber {p : F × I} (hp : p.2 = 0 ∨ p.2 = 1) :
    cylinderMap φ p ∈ fiber φ := by
  rcases hp with hp | hp <;> simp [hp]

/-- The map of pairs `(F × I, F × ∂I) ⟶ (T, F)` induced by `MappingTorus.cylinderMap`. -/
def cylinderPairMap : cylinderBoundaryPair (TopCat.of F) ⟶ fiberPair φ :=
  TopPair.ofSubsetMap (TopCat.ofHom (cylinderMap φ)) fun _ hp ↦
    cylinderMap_mem_fiber φ ((mem_cylinderBoundary _).1 hp)

lemma cylinderPairMap_fst : TopPair.Hom.fst (cylinderPairMap φ) = TopCat.ofHom (cylinderMap φ) :=
  TopPair.ofSubsetMap_fst _ _

@[simp]
lemma cylinderPairMap_fst_apply (p : F × I) :
    TopPair.Hom.fst (cylinderPairMap φ) p = mk φ (φ p.1) p.2 := by
  rw [cylinderPairMap_fst]
  exact cylinderMap_apply φ p

@[simp]
lemma cylinderPairMap_snd_apply (p : (cylinderBoundaryPair (TopCat.of F)).snd) :
    (TopPair.Hom.snd (cylinderPairMap φ) p).1 = mk φ (φ p.1.1) p.1.2 :=
  (TopPair.ofSubsetMap_snd_apply _ _ _).trans (cylinderMap_apply φ _)

/-- On the bottom end of the cylinder, the cylinder map is the fibre inclusion after `φ`. -/
@[reassoc (attr := simp)]
lemma cylinderBoundaryι₀_comp_cylinderPairMap :
    cylinderBoundaryι₀ (TopCat.of F) ≫ TopPair.Hom.snd (cylinderPairMap φ) =
      TopCat.ofHom (⟨φ, φ.continuous⟩ : C(F, F)) ≫ fiberPairIncl φ := by
  refine TopCat.ext fun x ↦ Subtype.ext ?_
  refine ((cylinderPairMap_snd_apply φ _).trans
    (congrArg (fun q : F × I ↦ mk φ (φ q.1) q.2) (cylinderBoundaryι₀_apply _ x))).trans ?_
  exact ((fiberPairIncl_apply φ (φ x)).trans (incl_apply φ (φ x))).symm

/-- On the top end of the cylinder, the cylinder map is the fibre inclusion. -/
@[reassoc (attr := simp)]
lemma cylinderBoundaryι₁_comp_cylinderPairMap :
    cylinderBoundaryι₁ (TopCat.of F) ≫ TopPair.Hom.snd (cylinderPairMap φ) = fiberPairIncl φ := by
  refine TopCat.ext fun x ↦ Subtype.ext ?_
  refine ((cylinderPairMap_snd_apply φ _).trans
    (congrArg (fun q : F × I ↦ mk φ (φ q.1) q.2) (cylinderBoundaryι₁_apply _ x))).trans ?_
  refine Eq.trans ?_ ((fiberPairIncl_apply φ x).trans (incl_apply φ x)).symm
  simpa using mk_vadd φ 1 x 0

section Thickening

/-! ### Thickening the fibre and the ends of the cylinder -/

/-- The reparametrisation `u ↦ projIcc 0 1 (3u - 1)` of `ℝ` onto `I`, which is `0` up to `1/3`
and `1` from `2/3` on. -/
private def collapse : C(ℝ, I) :=
  ⟨fun u ↦ projIcc 0 1 zero_le_one (3 * u - 1), continuous_projIcc.comp (by fun_prop)⟩

private lemma collapse_of_le {u : ℝ} (hu : u ≤ 1 / 3) : collapse u = 0 :=
  projIcc_of_le_left zero_le_one (by linarith)

private lemma collapse_of_ge {u : ℝ} (hu : 2 / 3 ≤ u) : collapse u = 1 :=
  projIcc_of_right_le zero_le_one (by linarith)

/-- A real number lies within `1/3` of an integer exactly when its fractional part lies within
`1/3` of `0` or of `1`. -/
private lemma norm_coe_lt_iff (t : ℝ) :
    ‖(t : UnitAddCircle)‖ < 1 / 3 ↔ Int.fract t < 1 / 3 ∨ 2 / 3 < Int.fract t := by
  rw [UnitAddCircle.norm_eq, abs_sub_round_eq_min, min_lt_iff]
  exact or_congr Iff.rfl ⟨fun h ↦ by linarith, fun h ↦ by linarith⟩

private lemma norm_coe_intCast_add_lt (m : ℤ) {v : ℝ} (hv : |v| < 1 / 3) :
    ‖(((m : ℝ) + v : ℝ) : UnitAddCircle)‖ < 1 / 3 := by
  have hm : ((m : ℝ) : UnitAddCircle) = 0 := (AddCircle.coe_eq_zero_iff 1).2 ⟨m, by simp⟩
  obtain ⟨hv₁, hv₂⟩ := abs_lt.1 hv
  rw [AddCircle.coe_add, hm, zero_add, UnitAddCircle.norm_eq,
    round_eq_zero_iff.2 ⟨by linarith, by linarith⟩, Int.cast_zero, sub_zero]
  exact hv

variable (X : TopCat.{w})

/-- The heights within `1/3` of the ends of the cylinder: an open neighbourhood of `X × ∂I`. -/
private def cylinderEnds : Set (X × I) := {p | (p.2 : ℝ) < 1 / 3 ∨ 2 / 3 < (p.2 : ℝ)}

/-- The open cylinder `X × (0, 1)`. -/
private def openCylinder : Set (X × I) := {p | 0 < (p.2 : ℝ) ∧ (p.2 : ℝ) < 1}

private lemma isOpen_cylinderEnds : IsOpen (cylinderEnds X) := by
  have h₁ : IsOpen {p : X × I | (p.2 : ℝ) < 1 / 3} := isOpen_lt (by fun_prop) continuous_const
  have h₂ : IsOpen {p : X × I | 2 / 3 < (p.2 : ℝ)} := isOpen_lt continuous_const (by fun_prop)
  exact h₁.union h₂

private lemma isOpen_openCylinder : IsOpen (openCylinder X) := by
  have h₁ : IsOpen {p : X × I | 0 < (p.2 : ℝ)} := isOpen_lt continuous_const (by fun_prop)
  have h₂ : IsOpen {p : X × I | (p.2 : ℝ) < 1} := isOpen_lt (by fun_prop) continuous_const
  exact h₁.inter h₂

private lemma mapsTo_cylinderBoundary_cylinderEnds :
    MapsTo (𝟙 (TopCat.of (X × I))) (cylinderBoundary X) (cylinderEnds X) := by
  intro p hp
  rcases (mem_cylinderBoundary X).1 hp with h | h
  · exact Or.inl (by norm_num [h])
  · exact Or.inr (by norm_num [h])

/-- The retraction of the cylinder collapsing the heights within `1/3` of the ends onto the
ends. -/
private def cylinderRetract : TopCat.of (X × I) ⟶ TopCat.of (X × I) :=
  TopCat.ofHom ((ContinuousMap.id X).prodMap (collapse.comp (ContinuousMap.subtypeVal _)))

/-- The straight-line homotopy from the identity of the cylinder to `cylinderRetract`. -/
private def cylinderHomotopy :
    (TopCat.Hom.hom (𝟙 (TopCat.of (X × I)))).Homotopy (cylinderRetract X).hom where
  toFun q := (q.2.1, Icc.convexComb q.2.2 (collapse q.2.2) q.1)
  continuous_toFun := by
    have := collapse.continuous
    fun_prop
  map_zero_left p := Prod.ext (rfl) (Icc.convexComb_zero _ _)
  map_one_left p := Prod.ext (rfl) (Icc.convexComb_one _ _)

private lemma cylinderHomotopy_apply_snd (τ : I) (p : TopCat.of (X × I)) :
    (cylinderHomotopy X (τ, p)).2 = Icc.convexComb p.2 (collapse p.2) τ := (rfl)

private lemma cylinderHomotopy_mem_cylinderBoundary (τ : I) (p : TopCat.of (X × I))
    (hp : p ∈ cylinderBoundary X) : cylinderHomotopy X (τ, p) ∈ cylinderBoundary X := by
  rcases (mem_cylinderBoundary X).1 hp with h | h
  · refine (mem_cylinderBoundary X).2 (Or.inl ?_)
    rw [cylinderHomotopy_apply_snd, h, collapse_of_le (by norm_num), Icc.convexComb_eq]
  · refine (mem_cylinderBoundary X).2 (Or.inr ?_)
    rw [cylinderHomotopy_apply_snd, h, collapse_of_ge (by norm_num), Icc.convexComb_eq]

private lemma cylinderHomotopy_mem_cylinderEnds (τ : I) (p : TopCat.of (X × I))
    (hp : p ∈ cylinderEnds X) : cylinderHomotopy X (τ, p) ∈ cylinderEnds X := by
  have hτ₀ := τ.2.1
  have hτ₁ := τ.2.2
  have ht₀ := p.2.2.1
  have ht₁ := p.2.2.2
  have hval : ((cylinderHomotopy X (τ, p)).2 : ℝ) = (1 - τ) * p.2 + τ * collapse p.2 := by
    rw [cylinderHomotopy_apply_snd, Icc.coe_convexComb]
  rcases hp with h | h
  · refine Or.inl ?_
    rw [hval, collapse_of_le h.le, Icc.coe_zero]
    nlinarith
  · refine Or.inr ?_
    rw [hval, collapse_of_ge h.le, Icc.coe_one]
    nlinarith

private lemma mapsTo_cylinderRetract :
    MapsTo (cylinderRetract X) (cylinderEnds X) (cylinderBoundary X) := by
  intro p hp
  rcases hp with h | h
  · exact (mem_cylinderBoundary X).2 (Or.inl (collapse_of_le h.le))
  · exact (mem_cylinderBoundary X).2 (Or.inr (collapse_of_ge h.le))

variable {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A] (R : A)

/-- Thickening the ends of the cylinder does not change relative homology. -/
private lemma isIso_singularHomologyMap_cylinderBoundary_cylinderEnds (n : ℕ) :
    IsIso (TopPair.singularHomologyMap
      (TopPair.ofSubsetMap _ (mapsTo_cylinderBoundary_cylinderEnds X)) R n) :=
  TopPair.isIso_singularHomologyMap_ofSubsetMap_id_of_homotopy _ (cylinderHomotopy X)
    (cylinderHomotopy_mem_cylinderBoundary X) (cylinderHomotopy_mem_cylinderEnds X)
    (mapsTo_cylinderRetract X) R n

/-- Excising the open cylinder: `(X × (0, 1), X × ((0, 1/3) ∪ (2/3, 1))) ⟶ (X × I, ends)` induces
isomorphisms on relative homology. -/
private lemma isIso_singularHomologyMap_excisionMap_openCylinder (n : ℕ) :
    IsIso (TopPair.singularHomologyMap (TopPair.excisionMap (X := TopCat.of (X × I))
      (openCylinder X) (cylinderEnds X)) R n) := by
  refine TopPair.isIso_singularHomologyMap_excisionMap R _ _ ?_ n
  rw [(isOpen_openCylinder X).interior_eq, (isOpen_cylinderEnds X).interior_eq]
  refine eq_univ_of_forall fun p ↦ ?_
  rcases lt_or_ge (p.2 : ℝ) (1 / 3) with h₁ | h₁
  · exact Or.inr (Or.inl h₁)
  rcases lt_or_ge (2 / 3) (p.2 : ℝ) with h₂ | h₂
  · exact Or.inr (Or.inr h₂)
  exact Or.inl ⟨by linarith, by linarith⟩

variable {X}

/-- The height shift `t ↦ fract t - collapse (fract t)`.  Subtracting it from `t` collapses the
heights within `1/3` of an integer onto that integer. -/
private def heightShift (t : ℝ) : ℝ := Int.fract t - collapse (Int.fract t)

private lemma continuous_heightShift : Continuous heightShift :=
  ContinuousOn.comp_fract'' (f := fun u ↦ u - collapse u)
    (by fun_prop : Continuous fun u ↦ u - (collapse u : ℝ)).continuousOn
    (by rw [collapse_of_le (by norm_num), collapse_of_ge (by norm_num)]; norm_num)

private lemma heightShift_add_intCast (t : ℝ) (n : ℤ) :
    heightShift (t + n) = heightShift t := by
  simp only [heightShift, Int.fract_add_intCast]

private lemma heightShift_of_coe_eq_zero {t : ℝ} (ht : (t : UnitAddCircle) = 0) :
    heightShift t = 0 := by
  obtain ⟨n, rfl⟩ := (AddCircle.coe_eq_zero_iff 1).1 ht
  simp [heightShift, collapse_of_le]

/-- Near an integer, removing the height shift lands on an integer. -/
private lemma coe_sub_heightShift {t : ℝ} (ht : ‖(t : UnitAddCircle)‖ < 1 / 3) :
    ((t - heightShift t : ℝ) : UnitAddCircle) = 0 := by
  have hft := Int.floor_add_fract t
  obtain ⟨m, hm⟩ : ∃ m : ℤ, t - heightShift t = m := by
    rcases (norm_coe_lt_iff t).1 ht with h | h
    · exact ⟨⌊t⌋, by rw [heightShift, collapse_of_le h.le, Icc.coe_zero]; linarith⟩
    · exact ⟨⌊t⌋ + 1, by rw [heightShift, collapse_of_ge h.le, Icc.coe_one]; push_cast; linarith⟩
  rw [hm]
  exact (AddCircle.coe_eq_zero_iff 1).2 ⟨m, by simp⟩

/-- Near an integer, the straight line from `t` to `t - heightShift t` stays near that integer. -/
private lemma norm_coe_sub_mul_heightShift_lt (s : I) {t : ℝ}
    (ht : ‖(t : UnitAddCircle)‖ < 1 / 3) :
    ‖((t - s * heightShift t : ℝ) : UnitAddCircle)‖ < 1 / 3 := by
  have hft := Int.floor_add_fract t
  have hs₀ := s.2.1
  have hs₁ := s.2.2
  have hf₀ := Int.fract_nonneg t
  have hf₁ := Int.fract_lt_one t
  rcases (norm_coe_lt_iff t).1 ht with h | h
  · have heq : t - s * heightShift t = (⌊t⌋ : ℝ) + (1 - s) * Int.fract t := by
      rw [heightShift, collapse_of_le h.le, Icc.coe_zero]
      linarith
    rw [heq]
    exact norm_coe_intCast_add_lt _ (abs_lt.2 ⟨by nlinarith, by nlinarith⟩)
  · have heq : t - s * heightShift t = ((⌊t⌋ + 1 : ℤ) : ℝ) + (1 - s) * (Int.fract t - 1) := by
      rw [heightShift, collapse_of_ge h.le, Icc.coe_one]
      push_cast
      linarith
    rw [heq]
    exact norm_coe_intCast_add_lt _ (abs_lt.2 ⟨by nlinarith, by nlinarith⟩)

/-- The straight-line deformation `(s, [x, t]) ↦ [x, t - s · heightShift t]` of the mapping
torus. -/
private def torusDeform (p : I × MappingTorus φ) : MappingTorus φ :=
  lift φ (fun q : F × ℝ ↦ mk φ q.1 (q.2 - p.1 * heightShift q.2)) (fun n x t ↦ by
    rw [heightShift_add_intCast, ← mk_vadd φ n x (t - p.1 * heightShift t)]
    ring_nf) p.2

private lemma torusDeform_mk (s : I) (x : F) (t : ℝ) :
    torusDeform φ (s, mk φ x t) = mk φ x (t - s * heightShift t) :=
  lift_mk ..

private lemma continuous_torusDeform : Continuous (torusDeform φ) := by
  have hq : IsQuotientMap
      (Prod.map id fun q : F × ℝ ↦ mk φ q.1 q.2 : I × (F × ℝ) → I × MappingTorus φ) :=
    (IsOpenMap.id.prodMap (isOpenMap_mk φ)).isQuotientMap
      (continuous_id.prodMap (continuous_mk φ)) (Function.surjective_id.prodMap (mk_surjective φ))
  refine hq.continuous_iff.2 ?_
  have := continuous_heightShift
  -- On representatives, the deformation is `(s, (x, t)) ↦ [x, t - s · heightShift t]`.
  exact ((continuous_mk φ).comp
    (f := fun p : I × (F × ℝ) ↦ (p.2.1, p.2.2 - p.1 * heightShift p.2.2)) (by fun_prop)).congr
      fun p ↦ (torusDeform_mk φ p.1 p.2.1 p.2.2).symm

/-- The retraction of the mapping torus collapsing the heights within `1/3` of an integer onto
the fibre. -/
private def torusRetract : TopCat.of (MappingTorus φ) ⟶ TopCat.of (MappingTorus φ) :=
  TopCat.ofHom ⟨fun z ↦ torusDeform φ (1, z),
    (continuous_torusDeform φ).comp (continuous_const.prodMk continuous_id)⟩

/-- The straight-line homotopy from the identity of the mapping torus to `torusRetract`. -/
private def torusHomotopy :
    (TopCat.Hom.hom (𝟙 (TopCat.of (MappingTorus φ)))).Homotopy (torusRetract φ).hom where
  toFun := torusDeform φ
  continuous_toFun := continuous_torusDeform φ
  map_zero_left z := by
    obtain ⟨⟨x, t⟩, rfl⟩ := mk_surjective φ z
    simp [torusDeform_mk]
  map_one_left _ := rfl

private lemma torusHomotopy_apply_mk (s : I) (x : F) (t : ℝ) :
    torusHomotopy φ (s, mk φ x t) = mk φ x (t - s * heightShift t) :=
  torusDeform_mk φ s x t

private lemma torusRetract_apply_mk (x : F) (t : ℝ) :
    torusRetract φ (mk φ x t) = mk φ x (t - heightShift t) :=
  (torusDeform_mk φ 1 x t).trans (by rw [Icc.coe_one, one_mul])

/-- The heights within `1/3` of an integer: an open neighbourhood of the fibre over `0`. -/
private def fiberNbhd : Set (MappingTorus φ) := proj φ ⁻¹' {θ | ‖θ‖ < 1 / 3}

private lemma mk_mem_fiberNbhd_iff {x : F} {t : ℝ} :
    mk φ x t ∈ fiberNbhd φ ↔ ‖(t : UnitAddCircle)‖ < 1 / 3 := by
  simp [fiberNbhd]

private lemma isOpen_fiberNbhd : IsOpen (fiberNbhd φ) :=
  isOpen_lt (continuous_norm.comp (continuous_proj φ)) continuous_const

private lemma mapsTo_fiber_fiberNbhd :
    MapsTo (𝟙 (TopCat.of (MappingTorus φ))) (fiber φ) (fiberNbhd φ) := by
  intro z hz
  simp only [fiberNbhd, mem_preimage, mem_ofPred_eq]
  calc ‖proj φ z‖ = 0 := by rw [(mem_fiber_iff φ).1 hz, norm_zero]
    _ < 1 / 3 := by norm_num

private lemma torusHomotopy_mem_fiber (τ : I) (z : TopCat.of (MappingTorus φ))
    (hz : z ∈ fiber φ) : torusHomotopy φ (τ, z) ∈ fiber φ := by
  obtain ⟨⟨x, t⟩, rfl⟩ := mk_surjective φ z
  dsimp only at hz ⊢
  have ht : (t : UnitAddCircle) = 0 := (proj_mk φ x t).symm.trans ((mem_fiber_iff φ).1 hz)
  rw [torusHomotopy_apply_mk, heightShift_of_coe_eq_zero ht, mul_zero, sub_zero]
  exact hz

private lemma torusHomotopy_mem_fiberNbhd (τ : I) (z : TopCat.of (MappingTorus φ))
    (hz : z ∈ fiberNbhd φ) : torusHomotopy φ (τ, z) ∈ fiberNbhd φ := by
  obtain ⟨⟨x, t⟩, rfl⟩ := mk_surjective φ z
  dsimp only at hz ⊢
  rw [torusHomotopy_apply_mk]
  exact (mk_mem_fiberNbhd_iff φ).2
    (norm_coe_sub_mul_heightShift_lt τ ((mk_mem_fiberNbhd_iff φ).1 hz))

private lemma mapsTo_torusRetract : MapsTo (torusRetract φ) (fiberNbhd φ) (fiber φ) := by
  intro z hz
  obtain ⟨⟨x, t⟩, rfl⟩ := mk_surjective φ z
  dsimp only at hz ⊢
  rw [torusRetract_apply_mk]
  exact (mem_fiber_iff φ).2 ((proj_mk φ x _).trans
    (coe_sub_heightShift ((mk_mem_fiberNbhd_iff φ).1 hz)))

/-- Thickening the fibre of the mapping torus does not change relative homology. -/
private lemma isIso_singularHomologyMap_fiber_fiberNbhd (n : ℕ) :
    IsIso (TopPair.singularHomologyMap (TopPair.ofSubsetMap _ (mapsTo_fiber_fiberNbhd φ)) R n) :=
  TopPair.isIso_singularHomologyMap_ofSubsetMap_id_of_homotopy _ (torusHomotopy φ)
    (torusHomotopy_mem_fiber φ) (torusHomotopy_mem_fiberNbhd φ) (mapsTo_torusRetract φ) R n

/-- The cylinder map carries the heights within `1/3` of the ends into the heights within `1/3` of
an integer. -/
private lemma mapsTo_cylinderEnds :
    MapsTo (TopCat.ofHom (cylinderMap φ)) (cylinderEnds (TopCat.of F)) (fiberNbhd φ) := by
  intro p hp
  have ht₀ := p.2.2.1
  have ht₁ := p.2.2.2
  rw [TopCat.ofHom_apply, cylinderMap_apply]
  refine (mk_mem_fiberNbhd_iff φ).2 ?_
  rcases hp with h | h
  · simpa using norm_coe_intCast_add_lt 0 (v := p.2) (abs_lt.2 ⟨by linarith, h⟩)
  · simpa using norm_coe_intCast_add_lt 1 (v := p.2 - 1) (abs_lt.2 ⟨by linarith, by linarith⟩)

/-- The thickened cylinder map, restricted to the open cylinder. -/
private abbrev openCylinderMap :
    TopPair.interPair (X := TopCat.of (TopCat.of F × I)) (openCylinder (TopCat.of F))
        (cylinderEnds (TopCat.of F)) ⟶
      TopPair.ofSubset (X := TopCat.of (MappingTorus φ)) (fiberNbhd φ) :=
  TopPair.excisionMap (X := TopCat.of (TopCat.of F × I)) _ _ ≫
    TopPair.ofSubsetMap _ (mapsTo_cylinderEnds φ)

private lemma openCylinderMap_fst_apply (p : openCylinder (TopCat.of F)) :
    TopPair.Hom.fst (openCylinderMap φ) p = mk φ (φ p.1.1) p.1.2 := by
  -- The ambient map of a composite of pairs is the composite of the ambient maps.
  exact (congrArg (TopPair.Hom.fst (TopPair.ofSubsetMap _ (mapsTo_cylinderEnds φ)))
    (TopPair.excisionMap_fst_apply (X := TopCat.of (TopCat.of F × I)) _ _ p)).trans
      ((TopPair.ofSubsetMap_fst_apply _ _ _).trans (cylinderMap_apply φ p.1))

private lemma isEmbedding_openCylinderMap :
    IsEmbedding (TopPair.Hom.fst (openCylinderMap φ)) := by
  let e : openCylinder (TopCat.of F) → F × Ioo (0 : ℝ) (0 + 1) :=
    fun p ↦ (φ p.1.1, ⟨p.1.2, p.2.1, by simpa using p.2.2⟩)
  have he : IsEmbedding e :=
    (IsEmbedding.of_comp_iff (IsEmbedding.id.prodMap IsEmbedding.subtypeVal)).1
      ((φ.isEmbedding.prodMap IsEmbedding.subtypeVal).comp IsEmbedding.subtypeVal)
  -- On the open cylinder, the cylinder map is the open cylinder chart `isOpenEmbedding_mk_Ioo`
  -- after `e`.
  have h : ⇑(TopPair.Hom.fst (openCylinderMap φ)) =
      (fun p : F × Ioo (0 : ℝ) (0 + 1) ↦ mk φ p.1 p.2) ∘ e :=
    funext (openCylinderMap_fst_apply φ)
  rw [h]
  exact (isOpenEmbedding_mk_Ioo φ 0).isEmbedding.comp he

/-- Excising the open cylinder from the mapping torus: the open cylinder modulo the heights within
`1/3` of `0` or `1` maps isomorphically onto the mapping torus modulo the heights within `1/3` of
an integer. -/
private lemma isIso_singularHomologyMap_openCylinderMap (n : ℕ) :
    IsIso (TopPair.singularHomologyMap (openCylinderMap φ) R n) := by
  refine TopPair.isIso_singularHomologyMap_of_open_cover R (openCylinderMap φ)
    (isEmbedding_openCylinderMap φ) ?_ (fun b : Bool ↦ bif b then fiberNbhd φ else (fiber φ)ᶜ)
    (fun b ↦ by cases b; exacts [(isClosed_fiber φ).isOpen_compl, isOpen_fiberNbhd φ]) ?_ ?_ n
  · rintro p ⟨y, hy⟩
    have hp : mk φ (φ p.1.1) p.1.2 ∈ fiberNbhd φ := by
      have hy' : y.1 = mk φ (φ p.1.1) p.1.2 :=
        hy.trans (openCylinderMap_fst_apply φ p)
      exact hy' ▸ y.2
    have hfract : Int.fract (p.1.2 : ℝ) = p.1.2 := Int.fract_eq_self.2 ⟨p.2.1.le, p.2.2⟩
    have h := (norm_coe_lt_iff _).1 ((mk_mem_fiberNbhd_iff φ).1 hp)
    rw [hfract] at h
    exact ⟨⟨p, h⟩, rfl⟩
  · refine eq_univ_of_forall fun z ↦ mem_iUnion.2 ?_
    by_cases hz : z ∈ fiber φ
    · exact ⟨true, mapsTo_fiber_fiberNbhd φ hz⟩
    · exact ⟨false, hz⟩
  · intro b
    cases b
    · refine Or.inr fun z hz ↦ ?_
      have hz₀ : z ∉ fiber φ := hz
      have hz' : z ∈ range fun p : F × Ioo (0 : ℝ) (0 + 1) ↦ mk φ p.1 p.2 := by
        rw [range_mk_Ioo]
        exact fun h ↦ hz₀ ((mem_fiber_iff φ).2 ((mem_singleton_iff.1 (mem_preimage.1 h)).trans
          (AddCircle.coe_zero (p := (1 : ℝ)))))
      obtain ⟨⟨y, t⟩, rfl⟩ := hz'
      refine ⟨⟨(φ.symm y, ⟨t, t.2.1.le, by linarith [t.2.2]⟩), t.2.1, by linarith [t.2.2]⟩, ?_⟩
      exact (openCylinderMap_fst_apply φ _).trans
        (congrArg (fun a ↦ mk φ a (t : ℝ)) (φ.apply_symm_apply y))
    · exact Or.inl fun z hz ↦ ⟨⟨z, hz⟩, rfl⟩

end Thickening

variable {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A] (R : A)

/-- **The cylinder map induces isomorphisms on relative homology**: the map of pairs
`(F × I, F × ∂I) ⟶ (T, F)` given by `(x, t) ↦ [φ x, t]` induces isomorphisms
`Hₙ(F × I, F × ∂I) ≅ Hₙ(T, F)` in every degree. -/
theorem isIso_singularHomologyMap_cylinderPairMap (n : ℕ) :
    IsIso (TopPair.singularHomologyMap (cylinderPairMap φ) R n) := by
  have h₁ := isIso_singularHomologyMap_cylinderBoundary_cylinderEnds (TopCat.of F) R n
  have h₂ := isIso_singularHomologyMap_fiber_fiberNbhd φ R n
  have h₃ : IsIso (TopPair.singularHomologyMap
      (TopPair.ofSubsetMap _ (mapsTo_cylinderEnds φ)) R n) := by
    have := isIso_singularHomologyMap_excisionMap_openCylinder (TopCat.of F) R n
    have h := isIso_singularHomologyMap_openCylinderMap φ R n
    rw [TopPair.singularHomologyMap_comp] at h
    exact IsIso.of_isIso_comp_left (TopPair.singularHomologyMap
      (TopPair.excisionMap (X := TopCat.of (TopCat.of F × I)) (openCylinder (TopCat.of F))
        (cylinderEnds (TopCat.of F))) R n) _
  -- Both thickenings of the cylinder map are the cylinder map into the thickened fibre.
  have hsq : cylinderPairMap φ ≫ TopPair.ofSubsetMap _ (mapsTo_fiber_fiberNbhd φ) =
      TopPair.ofSubsetMap _ (mapsTo_cylinderBoundary_cylinderEnds (TopCat.of F)) ≫
        TopPair.ofSubsetMap _ (mapsTo_cylinderEnds φ) :=
    TopPair.hom_ext_of_fst _ (by
      simp only [TopPair.Hom.fst_comp, cylinderPairMap_fst, TopPair.ofSubsetMap_fst]
      exact (Category.comp_id _).trans (Category.id_comp _).symm)
  have : IsIso (TopPair.singularHomologyMap (cylinderPairMap φ) R n ≫
      TopPair.singularHomologyMap (TopPair.ofSubsetMap _ (mapsTo_fiber_fiberNbhd φ)) R n) := by
    rw [← TopPair.singularHomologyMap_comp, hsq, TopPair.singularHomologyMap_comp]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    (TopPair.singularHomologyMap (TopPair.ofSubsetMap _ (mapsTo_fiber_fiberNbhd φ)) R n)

/-- **The relative homology `H₀(T, F)` vanishes**, like that of the cylinder modulo its ends. -/
theorem isZero_singularHomology_fiberPair_zero : IsZero ((fiberPair φ).singularHomology R 0) :=
  have := isIso_singularHomologyMap_cylinderPairMap φ R 0
  (isZero_singularHomology_cylinderBoundaryPair_zero (TopCat.of F) R).of_iso
    (asIso (TopPair.singularHomologyMap (cylinderPairMap φ) R 0)).symm

/-- **The homology of a mapping torus modulo a fibre**: `Hₙ₊₁(T, F) ≅ Hₙ(F)`.  It is the inverse
of the isomorphism induced by the cylinder map, followed by the homology of the cylinder modulo
its ends, `singularHomologyCylinderBoundaryPairIso`. -/
def singularHomologyFiberPairIso (n : ℕ) :
    (fiberPair φ).singularHomology R (n + 1) ≅
      ((singularHomologyFunctor A n).obj R).obj (TopCat.of F) :=
  have := isIso_singularHomologyMap_cylinderPairMap φ R (n + 1)
  (asIso (TopPair.singularHomologyMap (cylinderPairMap φ) R (n + 1))).symm ≪≫
    singularHomologyCylinderBoundaryPairIso (TopCat.of F) R n

/-- The isomorphism `Hₙ₊₁(T, F) ≅ Hₙ(F)` after the map induced by the cylinder map is the
homology of the cylinder modulo its ends. -/
@[reassoc (attr := simp)]
lemma singularHomologyMap_cylinderPairMap_comp_singularHomologyFiberPairIso_hom (n : ℕ) :
    TopPair.singularHomologyMap (cylinderPairMap φ) R (n + 1) ≫
        (singularHomologyFiberPairIso φ R n).hom =
      (singularHomologyCylinderBoundaryPairIso (TopCat.of F) R n).hom := by
  simp [singularHomologyFiberPairIso]

/-- **The connecting morphism of a mapping torus modulo a fibre.**  Under `Hₙ₊₁(T, F) ≅ Hₙ(F)`,
the connecting morphism `Hₙ₊₁(T, F) ⟶ Hₙ(F)` of the pair is `id - φ_*` followed by the map induced
by the fibre inclusion. -/
theorem singularHomologyδ_fiberPair (n : ℕ) :
    (fiberPair φ).singularHomologyδ R (n + 1) n =
      (singularHomologyFiberPairIso φ R n).hom ≫
        (𝟙 _ - ((singularHomologyFunctor A n).obj R).map
          (TopCat.ofHom (⟨φ, φ.continuous⟩ : C(F, F)))) ≫
          ((singularHomologyFunctor A n).obj R).map (fiberPairIncl φ) := by
  let H := (singularHomologyFunctor A n).obj R
  let q := TopPair.singularHomologyMap (cylinderPairMap φ) R (n + 1)
  have : IsIso q := isIso_singularHomologyMap_cylinderPairMap φ R (n + 1)
  -- State both connecting morphisms with target `H.obj _`, so that rewriting stays well-typed.
  let δ : (fiberPair φ).singularHomology R (n + 1) ⟶ H.obj (fiberPair φ).snd :=
    (fiberPair φ).singularHomologyδ R (n + 1) n
  let δc : (cylinderBoundaryPair (TopCat.of F)).singularHomology R (n + 1) ⟶
      H.obj (cylinderBoundaryPair (TopCat.of F)).snd :=
    (cylinderBoundaryPair (TopCat.of F)).singularHomologyδ R (n + 1) n
  have hδ : δc ≫ H.map (TopPair.Hom.snd (cylinderPairMap φ)) = q ≫ δ :=
    TopPair.singularHomologyδ_naturality R (cylinderPairMap φ) (n + 1) n
  have hc : δc = (singularHomologyCylinderBoundaryPairIso (TopCat.of F) R n).hom ≫
      (H.map (cylinderBoundaryι₁ (TopCat.of F)) - H.map (cylinderBoundaryι₀ (TopCat.of F))) :=
    singularHomologyδ_cylinderBoundaryPair (TopCat.of F) R n
  have key : δ = (singularHomologyFiberPairIso φ R n).hom ≫
      (𝟙 _ - H.map (TopCat.ofHom (⟨φ, φ.continuous⟩ : C(F, F)))) ≫ H.map (fiberPairIncl φ) := by
    rw [← cancel_epi q, ← hδ, hc,
      singularHomologyMap_cylinderPairMap_comp_singularHomologyFiberPairIso_hom_assoc]
    simp only [H, Category.assoc, Preadditive.sub_comp, Category.id_comp, ← Functor.map_comp,
      cylinderBoundaryι₀_comp_cylinderPairMap, cylinderBoundaryι₁_comp_cylinderPairMap]
  exact key

end TauCeti.MappingTorus

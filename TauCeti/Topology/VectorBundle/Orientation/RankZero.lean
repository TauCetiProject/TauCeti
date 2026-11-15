/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Equiv.SpanSingleton
public import TauCeti.AlgebraicTopology.Cohomology.DegreeZero
public import TauCeti.Topology.VectorBundle.EulerClass
public import TauCeti.Topology.VectorBundle.Orientation.Basic

/-!
# Thom and Euler classes in rank zero

Let `E → B` be a real vector bundle whose model fibre `F` is zero, so that every fibre is zero.
Its Thom pair `(E, E₀)` has empty second member (`TauCeti.zeroSectionCompl_eq_empty`), and the
zero section is a homeomorphism `B ≅ E`, inverse to the projection
(`TauCeti.thomPairProj_comp_zeroSectionHom`). So the Euler class map
`Hⁿ(E, E₀) ⟶ Hⁿ(B)`, restriction to `Hⁿ(E)` followed by pull-back along the zero section, is an
isomorphism in every degree and for all coefficients (`TauCeti.isIso_eulerClass`): in rank zero a
relative class is the same thing as its Euler class. With coefficients in a commutative ring `K`,
a degree-zero class restricts to a generator of `H⁰(E_b, E_b ∖ {0}; K) ≅ K` on the fibre over `b`
exactly when its Euler class takes a unit value at `b`
(`TauCeti.span_singularCohomologyMap_fiberThomPairMap_eq_top_iff`). Hence the Thom classes of a
rank-zero bundle are the classes whose Euler classes are units of `H⁰(B; K)`, the functions on
path components with values in `Kˣ` (`TauCeti.isThomClass_iff_forall_isUnit`).

An orientation of a rank-zero bundle is indexed by an empty type `ι`. A zero-dimensional vector
space has two orientations, the positive orientation `positiveOrientation` (that of its empty
basis) and its opposite, so an orientation of the bundle is a choice of sign over each point, and
the sign is locally constant: the points where an orientation `o` is positive form a clopen set
(`TauCeti.VectorBundleOrientation.isClopen_setOf_eq_positiveOrientation`). Every rank-zero bundle
carries the positive orientation `TauCeti.VectorBundleOrientation.positive`.

This sign is the degree-zero Thom and Euler generator of the oriented bundle. The *Euler class*
`e(E, o) ∈ H⁰(B; K)` (`TauCeti.VectorBundleOrientation.rankZeroEulerClass`) is the degree-zero
class with value `1` at the points where `o` is positive and `-1` at the others, and the *Thom
class* `U ∈ H⁰(E, E₀; K)` (`TauCeti.VectorBundleOrientation.rankZeroThomClass`) is the class with
this Euler class. It is a Thom class
(`TauCeti.VectorBundleOrientation.isThomClass_rankZeroThomClass`). The positive orientation has
the unit class as Euler class, and its Thom class restricts to the unit class of `H⁰(E; K)`;
reversing the orientation negates both classes, and both are natural under pull-back of bundles.
The Euler class squares to the unit for the cup product.

## Main definitions

* `TauCeti.VectorBundleOrientation.positive`: the positive orientation of a rank-zero bundle.
* `TauCeti.VectorBundleOrientation.rankZeroThomClass`: the Thom class `U ∈ H⁰(E, E₀; K)` of an
  oriented rank-zero bundle.
* `TauCeti.VectorBundleOrientation.rankZeroEulerClass`: its Euler class `e(E, o) ∈ H⁰(B; K)`, the
  sign of the orientation.

## Main results

* `TauCeti.isIso_eulerClass`: in rank zero the Euler class map is an isomorphism.
* `TauCeti.isThomClass_iff_forall_isUnit`: in rank zero a class is a Thom class exactly when its
  Euler class takes unit values.
* `TauCeti.VectorBundleOrientation.singularCohomologyZeroEval_rankZeroEulerClass_of_eq` and
  `TauCeti.VectorBundleOrientation.singularCohomologyZeroEval_rankZeroEulerClass_of_eq_neg`: the
  values `±1` of the Euler class.
* `TauCeti.VectorBundleOrientation.eq_rankZeroThomClass_iff`: the Thom class is the class with
  that Euler class.
* `TauCeti.VectorBundleOrientation.isThomClass_rankZeroThomClass`: it is a Thom class.
* `TauCeti.VectorBundleOrientation.rankZeroEulerClass_pullback` and
  `TauCeti.VectorBundleOrientation.singularCohomologyMap_pullbackThomPairMap_rankZeroThomClass`:
  naturality under pull-back of bundles.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §9 (the Thom class and the Euler class of an oriented bundle).
-/

public section

noncomputable section

open Bundle CategoryTheory Limits MonoidalCategory Module Set

universe w v u

namespace TauCeti

section Subsingleton

variable {B : Type w} [TopologicalSpace B] (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
  (E : B → Type w) [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E]
  [Subsingleton F]

include F in
/-- The fibres of a real vector bundle with zero model fibre are zero. -/
theorem subsingleton_fiber (b : B) : Subsingleton (E b) :=
  ((trivializationAt F E b).linearEquivAt ℝ b
    (FiberBundle.mem_baseSet_trivializationAt' b)).toEquiv.subsingleton

/-- A real vector bundle with zero model fibre has no nonzero vectors: `E₀` is empty. -/
theorem zeroSectionCompl_eq_empty : zeroSectionCompl F E = ∅ :=
  eq_empty_iff_forall_notMem.2 fun v hv ↦
    mem_zeroSectionCompl.1 hv ((subsingleton_fiber F E v.proj).elim _ _)

/-- In a real vector bundle with zero model fibre, every vector is the zero vector of its fibre:
the projection followed by the zero section is the identity of the total space. -/
theorem thomPairProj_comp_zeroSectionHom :
    thomPairProj F E ≫ zeroSectionHom F E = 𝟙 _ := by
  have h (v : TotalSpace F E) : zeroSection F E v.proj = v := by
    obtain ⟨b, x⟩ := v
    obtain rfl : x = 0 := (subsingleton_fiber F E b).elim _ _
    rfl
  exact TopCat.ext fun v ↦ (ConcreteCategory.comp_apply _ _ v).trans <|
    (zeroSectionHom_apply F E _).trans <|
      (congrArg (zeroSection F E) (thomPairProj_apply F E v)).trans <|
        (h v).trans (ConcreteCategory.id_apply v).symm

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)
  (k : Type*) [Ring k] [Linear k C] (M : C)

/-- **In rank zero the Euler class map is an isomorphism** `Hⁿ(E, E₀) ≅ Hⁿ(B)` in every degree:
`E₀` is empty, so restriction `Hⁿ(E, E₀) ⟶ Hⁿ(E)` is an isomorphism, and the zero section is a
homeomorphism `B ≅ E`. -/
instance isIso_eulerClass (n : ℕ) : IsIso (eulerClass R k M F E n) := by
  have : IsEmpty (thomPair F E).snd := isEmpty_coe_sort.2 (zeroSectionCompl_eq_empty F E)
  have hzero : zeroSectionHom F E ≫ thomPairProj F E = 𝟙 _ := TopCat.ext fun b ↦ by
    rw [ConcreteCategory.comp_apply, zeroSectionHom_apply, thomPairProj_apply,
      ConcreteCategory.id_apply]
    rfl
  have : IsIso (TopCat.singularCohomologyMap (R := R) (k := k) (M := M) (zeroSectionHom F E) n) :=
    ⟨TopCat.singularCohomologyMap (thomPairProj F E) n,
      by rw [← TopCat.singularCohomologyMap_comp, thomPairProj_comp_zeroSectionHom,
        TopCat.singularCohomologyMap_id],
      by rw [← TopCat.singularCohomologyMap_comp, hzero,
        TopCat.singularCohomologyMap_id]⟩
  rw [eulerClass_def]
  infer_instance

/-- In rank zero, pulling the Euler class of a relative class `u ∈ Hⁿ(E, E₀)` back along the
projection gives the image of `u` in `Hⁿ(E)`. -/
theorem singularCohomologyMap_thomPairProj_eulerClass (n : ℕ)
    (u : (thomPair F E).singularCohomology R k M n) :
    TopCat.singularCohomologyMap (thomPairProj F E) n (eulerClass R k M F E n u) =
      (thomPair F E).singularCohomologyπ R k M n u := by
  rw [eulerClass_def, ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply
    (TopCat.singularCohomologyMap (zeroSectionHom F E) n), ← TopCat.singularCohomologyMap_comp,
    thomPairProj_comp_zeroSectionHom, TopCat.singularCohomologyMap_id, ConcreteCategory.id_apply]

variable {F E} {K : Type w} [CommRing K]

/-- **The fibre generators in rank zero.** A degree-zero relative class `u ∈ H⁰(E, E₀; K)`
restricts to a generator of `H⁰(E_b, E_b ∖ {0}; K) ≅ K` on the fibre over `b` exactly when its
Euler class takes a unit value at `b`. -/
theorem span_singularCohomologyMap_fiberThomPairMap_eq_top_iff
    (u : (thomPair F E).singularCohomology (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K)) 0)
    (b : B) :
    Submodule.span K {TopPair.singularCohomologyMap (fiberThomPairMap F E b) 0 u} = ⊤ ↔
      IsUnit (singularCohomologyZeroEval b
        (eulerClass (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K)) F E 0 u)) := by
  have := subsingleton_fiber F E b
  have : IsEmpty (TopPair.ofSubset (X := TopCat.of (E b)) ({0}ᶜ : Set (E b))).snd :=
    isEmpty_coe_sort.2 (by simp [Set.eq_empty_iff_forall_notMem, Subsingleton.elim _ (0 : E b)])
  -- The fibre is the single point `0`, so the value at `0` identifies its `H⁰` with `K`.
  have hinj : Function.Injective (singularCohomologyZeroEval (k := K) (X := TopCat.of (E b)) 0) :=
    fun x y h ↦ singularCohomologyZero_ext fun z ↦ by rwa [Subsingleton.elim z 0]
  have hsurj : Function.Surjective
      (singularCohomologyZeroEval (k := K) (X := TopCat.of (E b)) 0) := fun c ↦
    ⟨c • (TopCat.of (E b)).singularCohomologyZeroOne, by simp⟩
  rw [← ((asIso ((TopPair.ofSubset (X := TopCat.of (E b)) ({0}ᶜ : Set (E b))).singularCohomologyπ
      (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K)) 0)).toLinearEquiv.trans
      (LinearEquiv.ofBijective _ ⟨hinj, hsurj⟩)).span_singleton_apply_eq_top_iff,
    Ideal.span_singleton_eq_top]
  -- Both sides read the value at the zero vector over `b` of the image of `u` in `H⁰(E; K)`.
  have key : singularCohomologyZeroEval (0 : E b)
      ((TopPair.ofSubset (X := TopCat.of (E b)) ({0}ᶜ : Set (E b))).singularCohomologyπ
        (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K)) 0
        (TopPair.singularCohomologyMap (fiberThomPairMap F E b) 0 u)) =
      singularCohomologyZeroEval b
        (eulerClass (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K)) F E 0 u) := by
    calc _ = singularCohomologyZeroEval (0 : E b)
          (TopCat.singularCohomologyMap (TopPair.Hom.fst (fiberThomPairMap F E b)) 0
            ((thomPair F E).singularCohomologyπ (𝟙_ (ModuleCat.{w} K)) K
              (𝟙_ (ModuleCat.{w} K)) 0 u)) :=
          congrArg _ (ConcreteCategory.congr_hom
            (TopPair.singularCohomologyπ_naturality (fiberThomPairMap F E b) 0) u).symm
      _ = singularCohomologyZeroEval (zeroSectionHom F E b)
          ((thomPair F E).singularCohomologyπ (𝟙_ (ModuleCat.{w} K)) K
            (𝟙_ (ModuleCat.{w} K)) 0 u) :=
          (singularCohomologyZeroEval_naturality _ _ _).trans <|
            congrArg (singularCohomologyZeroEval · _)
              ((fiberThomPairMap_fst_apply F E b 0).trans (zeroSectionHom_apply F E b).symm)
      _ = _ := by rw [eulerClass_def, ConcreteCategory.comp_apply,
          singularCohomologyZeroEval_naturality]
  exact iff_of_eq (congrArg IsUnit key)

/-- **The Thom classes in rank zero.** A degree-zero relative class `u ∈ H⁰(E, E₀; K)` of a bundle
with zero model fibre, read in the degree `finrank ℝ F = 0`, is a Thom class exactly when its
Euler class takes unit values at every point. -/
theorem isThomClass_iff_forall_isUnit
    (u : (thomPair F E).singularCohomology (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K)) 0) :
    IsThomClass F E ((finrank_zero_of_subsingleton (R := ℝ) (M := F)).symm ▸ u :
      (thomPair F E).singularCohomology (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K))
        (finrank ℝ F)) ↔
      ∀ b, IsUnit (singularCohomologyZeroEval b
        (eulerClass (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K)) F E 0 u)) := by
  -- Transport along `0 = finrank ℝ F` commutes with the fibre restrictions.
  suffices h : ∀ {d : ℕ} (hd : 0 = d) (b : B),
      Submodule.span K {TopPair.singularCohomologyMap (fiberThomPairMap F E b) d (hd ▸ u)} = ⊤ ↔
        Submodule.span K {TopPair.singularCohomologyMap (fiberThomPairMap F E b) 0 u} = ⊤ by
    rw [isThomClass_iff, and_iff_right (inferInstance : FiniteDimensional ℝ F)]
    exact forall_congr' fun b ↦ (h (finrank_zero_of_subsingleton (R := ℝ) (M := F)).symm b).trans
      (span_singularCohomologyMap_fiberThomPairMap_eq_top_iff u b)
  intro d hd b
  subst hd
  rfl

end Subsingleton

namespace VectorBundleOrientation

section Positive

variable {B : Type w} [TopologicalSpace B] (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
  (E : B → Type w) [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E]
  (ι : Type*) [IsEmpty ι]

/-- **The positive orientation** of a bundle oriented by an empty index type: every fibre carries
its positive orientation `positiveOrientation`, the orientation of its empty basis. For a bundle of
rank zero this is the canonical orientation. -/
def positive : VectorBundleOrientation F E ι where
  toFun _ := positiveOrientation
  eventually_mapOrientation_eq' _ := Filter.Eventually.of_forall fun _ _ ↦ by
    rw [Trivialization.mapOrientation_apply, Trivialization.mapOrientation_apply,
      Orientation.map_positiveOrientation_of_isEmpty,
      Orientation.map_positiveOrientation_of_isEmpty]

@[simp]
theorem positive_apply (b : B) : positive F E ι b = positiveOrientation :=
  (rfl)

variable {F E ι}

/-- At every point, an orientation indexed by an empty type is the positive orientation of the
fibre or its opposite. -/
theorem eq_positiveOrientation_or_eq_neg (o : VectorBundleOrientation F E ι) (b : B) :
    o b = positiveOrientation ∨ o b = -positiveOrientation := by
  -- Read the orientation in a trivialization, where the model fibre is an additive group.
  have hb := FiberBundle.mem_baseSet_trivializationAt' (F := F) (E := E) b
  have hpos := Orientation.map_positiveOrientation_of_isEmpty (R := ℝ) (ι := ι)
    ((trivializationAt F E b).linearEquivAt ℝ b hb)
  refine (Orientation.eq_or_eq_neg_of_isEmpty
    ((trivializationAt F E b).mapOrientation ι hb (o b))).imp (fun h ↦ ?_) fun h ↦ ?_ <;>
    refine ((trivializationAt F E b).mapOrientation ι hb).injective ?_
  · rw [h, Trivialization.mapOrientation_apply, hpos]
  · rw [h, Trivialization.mapOrientation_neg, Trivialization.mapOrientation_apply, hpos]

/-- An orientation indexed by an empty type is positive on a clopen set of the base, and negative,
`-positiveOrientation`, on its complement. -/
theorem isClopen_setOf_eq_positiveOrientation (o : VectorBundleOrientation F E ι) :
    IsClopen {b | o b = positiveOrientation} := by
  refine ⟨?_, o.isOpen_setOf_eq (positive F E ι)⟩
  have h : {b | o b = positiveOrientation}ᶜ = {b | o b = (-positive F E ι) b} := by
    ext b
    rcases o.eq_positiveOrientation_or_eq_neg b with hb | hb <;>
      simp [hb, Module.Ray.ne_neg_self, (Module.Ray.ne_neg_self _).symm]
  exact isOpen_compl_iff.1 (h ▸ o.isOpen_setOf_eq _)

end Positive

section ThomClass

variable {B : Type w} [TopologicalSpace B] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type w} [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E]
  {ι : Type*} [IsEmpty ι] (o : VectorBundleOrientation F E ι) (K : Type w) [CommRing K]

open scoped Classical in
/-- The sign of an orientation indexed by an empty type is a degree-zero class: it is locally
constant, hence constant on path components. -/
private theorem exists_singularCohomologyZeroEval_eq_sign :
    ∃ e : (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K)) 0,
      ∀ b, singularCohomologyZeroEval b e = if o b = positiveOrientation then 1 else -1 := by
  refine exists_singularCohomologyZeroEval_eq (X := TopCat.of B) _ fun x y h ↦ ?_
  -- A path from `x` to `y` stays in the clopen set where `o` is positive, or outside it.
  have hmem {x y : B} (h : Joined x y) (hx : o x = positiveOrientation) :
      o y = positiveOrientation :=
    (isPreconnected_range h.somePath.continuous).subset_isClopen
      o.isClopen_setOf_eq_positiveOrientation ⟨x, ⟨0, by simp⟩, hx⟩ ⟨1, by simp⟩
  by_cases hx : o x = positiveOrientation
  · simp [hx, hmem h hx]
  · have hy : ¬o y = positiveOrientation := fun hy ↦ hx (hmem h.symm hy)
    simp [hx, hy]

variable [Subsingleton F]

/-- **The Thom class of an oriented rank-zero bundle**, `U ∈ H⁰(E, E₀; K)` for a bundle with zero
model fibre oriented by an empty index type: the class whose Euler class
(`TauCeti.VectorBundleOrientation.rankZeroEulerClass`) has the value `1` at the points where the
orientation is positive and `-1` at the others. It is determined by its Euler class
(`TauCeti.VectorBundleOrientation.eq_rankZeroThomClass_iff`), and it is a Thom class
(`TauCeti.VectorBundleOrientation.isThomClass_rankZeroThomClass`). -/
def rankZeroThomClass :
    (thomPair F E).singularCohomology (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K)) 0 :=
  inv (eulerClass (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K)) F E 0)
    (exists_singularCohomologyZeroEval_eq_sign o K).choose

/-- **The Euler class of an oriented rank-zero bundle**, `e(E, o) ∈ H⁰(B; K)`: the Euler class of
its Thom class, the sign of the orientation. It has the value `1` at the points where the
orientation is positive
(`TauCeti.VectorBundleOrientation.singularCohomologyZeroEval_rankZeroEulerClass_of_eq`) and `-1`
at the others
(`TauCeti.VectorBundleOrientation.singularCohomologyZeroEval_rankZeroEulerClass_of_eq_neg`). -/
def rankZeroEulerClass :
    (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K)) 0 :=
  eulerClass (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K)) F E 0 (o.rankZeroThomClass K)

theorem rankZeroEulerClass_def :
    o.rankZeroEulerClass K =
      eulerClass (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K)) F E 0 (o.rankZeroThomClass K) :=
  (rfl)

open scoped Classical in
private theorem singularCohomologyZeroEval_rankZeroEulerClass (b : B) :
    singularCohomologyZeroEval b (o.rankZeroEulerClass K) =
      if o b = positiveOrientation then 1 else -1 := by
  rw [rankZeroEulerClass_def, rankZeroThomClass, ← ConcreteCategory.comp_apply, IsIso.inv_hom_id,
    ConcreteCategory.id_apply]
  exact (exists_singularCohomologyZeroEval_eq_sign o K).choose_spec b

/-- The Euler class of an oriented rank-zero bundle has the value `1` at a point where the
orientation is positive. -/
theorem singularCohomologyZeroEval_rankZeroEulerClass_of_eq {b : B}
    (h : o b = positiveOrientation) :
    singularCohomologyZeroEval b (o.rankZeroEulerClass K) = 1 := by
  simp [singularCohomologyZeroEval_rankZeroEulerClass, h]

/-- The Euler class of an oriented rank-zero bundle has the value `-1` at a point where the
orientation is negative. -/
theorem singularCohomologyZeroEval_rankZeroEulerClass_of_eq_neg {b : B}
    (h : o b = -positiveOrientation) :
    singularCohomologyZeroEval b (o.rankZeroEulerClass K) = -1 := by
  simp [singularCohomologyZeroEval_rankZeroEulerClass, h, (Module.Ray.ne_neg_self _).symm]

/-- **The Thom class is determined by its Euler class**: in rank zero the Euler class map is an
isomorphism (`TauCeti.isIso_eulerClass`). -/
theorem eq_rankZeroThomClass_iff
    (u : (thomPair F E).singularCohomology (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K)) 0) :
    u = o.rankZeroThomClass K ↔
      eulerClass (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K)) F E 0 u =
        o.rankZeroEulerClass K :=
  ⟨fun h ↦ h ▸ rfl, fun h ↦ (asIso (eulerClass (𝟙_ (ModuleCat.{w} K)) K
    (𝟙_ (ModuleCat.{w} K)) F E 0)).toLinearEquiv.injective h⟩

/-- **The Thom class of an oriented rank-zero bundle is a Thom class**: read in the degree
`finrank ℝ F = 0`, it restricts to a generator of `H⁰(E_b, E_b ∖ {0}; K) ≅ K` on every fibre. -/
theorem isThomClass_rankZeroThomClass :
    IsThomClass F E ((finrank_zero_of_subsingleton (R := ℝ) (M := F)).symm ▸
      o.rankZeroThomClass K :
      (thomPair F E).singularCohomology (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K))
        (finrank ℝ F)) := by
  refine (isThomClass_iff_forall_isUnit _).2 fun b ↦ ?_
  rw [← rankZeroEulerClass_def]
  rcases o.eq_positiveOrientation_or_eq_neg b with h | h
  · rw [o.singularCohomologyZeroEval_rankZeroEulerClass_of_eq K h]
    exact isUnit_one
  · rw [o.singularCohomologyZeroEval_rankZeroEulerClass_of_eq_neg K h]
    exact isUnit_one.neg

/-- The positive orientation of a rank-zero bundle has the unit class as Euler class. -/
@[simp]
theorem rankZeroEulerClass_positive :
    (positive F E ι).rankZeroEulerClass K = (TopCat.of B).singularCohomologyZeroOne :=
  singularCohomologyZero_ext fun b ↦ by
    rw [singularCohomologyZeroEval_rankZeroEulerClass_of_eq _ K (positive_apply F E ι b),
      singularCohomologyZeroEval_singularCohomologyZeroOne]

/-- The Thom class of the positive orientation of a rank-zero bundle restricts to the unit class
of the total space. -/
theorem singularCohomologyπ_rankZeroThomClass_positive :
    (thomPair F E).singularCohomologyπ (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K)) 0
        ((positive F E ι).rankZeroThomClass K) =
      (TopCat.of (TotalSpace F E)).singularCohomologyZeroOne := by
  rw [← singularCohomologyMap_thomPairProj_eulerClass, ← rankZeroEulerClass_def,
    rankZeroEulerClass_positive, singularCohomologyMap_singularCohomologyZeroOne]
  rfl

/-- Reversing the orientation negates the Euler class. -/
@[simp]
theorem rankZeroEulerClass_neg : (-o).rankZeroEulerClass K = -o.rankZeroEulerClass K :=
  singularCohomologyZero_ext fun b ↦ by
    rw [map_neg]
    rcases o.eq_positiveOrientation_or_eq_neg b with h | h
    · rw [singularCohomologyZeroEval_rankZeroEulerClass_of_eq_neg _ K (by rw [neg_apply, h]),
        o.singularCohomologyZeroEval_rankZeroEulerClass_of_eq K h]
    · -- `rw [neg_neg]` does not find the pattern, as in `TauCeti.VectorBundleOrientation.neg_neg`.
      have h' : (-o) b = positiveOrientation := by
        rw [neg_apply, h]
        exact _root_.neg_neg (positiveOrientation : Orientation ℝ (E b) ι)
      rw [singularCohomologyZeroEval_rankZeroEulerClass_of_eq _ K h',
        o.singularCohomologyZeroEval_rankZeroEulerClass_of_eq_neg K h, neg_neg]

/-- Reversing the orientation negates the Thom class. -/
@[simp]
theorem rankZeroThomClass_neg : (-o).rankZeroThomClass K = -o.rankZeroThomClass K := by
  symm
  rw [eq_rankZeroThomClass_iff, map_neg, ← rankZeroEulerClass_def, rankZeroEulerClass_neg]

/-- **The Euler class is a unit**: it squares to the unit class for the cup product, since its
values are `±1`. -/
@[simp]
theorem singularCup_rankZeroEulerClass_self :
    (TopCat.of B).singularCup K (λ_ _).inv (λ_ _).hom 0 0 0 rfl (o.rankZeroEulerClass K)
      (o.rankZeroEulerClass K) = (TopCat.of B).singularCohomologyZeroOne :=
  singularCohomologyZero_ext fun b ↦ by
    rw [singularCohomologyZeroEval_singularCup,
      singularCohomologyZeroEval_singularCohomologyZeroOne]
    rcases o.eq_positiveOrientation_or_eq_neg b with h | h
    · rw [o.singularCohomologyZeroEval_rankZeroEulerClass_of_eq K h, one_mul]
    · rw [o.singularCohomologyZeroEval_rankZeroEulerClass_of_eq_neg K h, neg_one_mul, neg_neg]

/-- **Naturality of the Euler class**: the Euler class of the pulled-back orientation of `f*E` is
the pull-back along `f` of the Euler class of `E`. -/
theorem rankZeroEulerClass_pullback {B' : Type w} [TopologicalSpace B'] (f : C(B', B)) :
    (o.pullback f).rankZeroEulerClass K =
      TopCat.singularCohomologyMap (TopCat.ofHom f) 0 (o.rankZeroEulerClass K) :=
  singularCohomologyZero_ext fun b' ↦ by
    rw [singularCohomologyZeroEval_naturality]
    rcases o.eq_positiveOrientation_or_eq_neg (f b') with h | h
    -- The point `TopCat.ofHom f b'` is `f b'`.
    · exact (singularCohomologyZeroEval_rankZeroEulerClass_of_eq _ K
        (by rw [pullback_apply]; exact h)).trans
        (o.singularCohomologyZeroEval_rankZeroEulerClass_of_eq K h).symm
    · exact (singularCohomologyZeroEval_rankZeroEulerClass_of_eq_neg _ K
        (by rw [pullback_apply]; exact h)).trans
        (o.singularCohomologyZeroEval_rankZeroEulerClass_of_eq_neg K h).symm

/-- **Naturality of the Thom class**: pulling the Thom class of `E` back along the map of Thom
pairs `(f*E, (f*E)₀) ⟶ (E, E₀)` covering `f` gives the Thom class of the pulled-back orientation of
`f*E`. -/
theorem singularCohomologyMap_pullbackThomPairMap_rankZeroThomClass {B' : Type w}
    [TopologicalSpace B'] (f : C(B', B)) :
    TopPair.singularCohomologyMap (pullbackThomPairMap F E f) 0 (o.rankZeroThomClass K) =
      (o.pullback f).rankZeroThomClass K :=
  -- Term-mode steps: the zero of the fibres of `f*E` enters the Thom pair of `f*E` through
  -- `pullbackThomPairMap` and through the vector bundle structure of `f*E` as two instances that
  -- agree only up to unfolding, so `rw` cannot match the composite.
  (eq_rankZeroThomClass_iff (o.pullback f) K _).2 <|
    (ConcreteCategory.comp_apply _ _ _).symm.trans <|
      (ConcreteCategory.congr_hom (eulerClass_pullback F E f 0) _).trans <|
        (ConcreteCategory.comp_apply _ _ _).trans (rankZeroEulerClass_pullback o K f).symm

end ThomClass

end VectorBundleOrientation

end TauCeti

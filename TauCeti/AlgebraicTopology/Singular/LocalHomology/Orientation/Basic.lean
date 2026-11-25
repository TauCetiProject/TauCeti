/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.System
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
import TauCeti.Algebra.Group.ZMultiples

/-!
# Local orientations from chart homology

A local orientation at a point of an `n`-dimensional manifold is a generator of the integral
local homology group in degree `n`. This file defines that generator condition and proves that
every point in a finite-dimensional charted space has local orientations. Integral coefficients
are represented by the universe-lifted module `ULift ℤ`. The construction is the inverse image of
`1` under the chart computation of local homology. The two generators of a fibre isomorphic to
`ℤ` differ by sign, and each of them identifies `ℤ` with the fibre
(`TauCeti.IsLocalOrientation.linearEquiv`); reversal and preservation by local homology
isomorphisms are also proved, and isomorphisms of pairs `(M, M ∖ {x}) ≅ (N, N ∖ {y})` transport
local orientations (`TauCeti.LocalOrientation.map`), compatibly with reversal, identities and
composites. In the dimension of a manifold, every point has exactly two local orientations, which
are reversals of each other (`TauCeti.LocalOrientation.nat_card_eq_two`,
`TauCeti.LocalOrientation.eq_or_eq_neg_of_finrank_eq`, `TauCeti.LocalOrientation.neg_ne`).

The local orientation is the generator of `Hₙ(M, M ∖ {x}; ℤ)` described in Hatcher's
*Algebraic Topology*, Section 3.3.
-/

public section

noncomputable section

open CategoryTheory Module

universe w

namespace TauCeti

/-- An element of the integral local homology group is a local orientation when it generates the
whole group as a `ℤ`-module. -/
def IsLocalOrientation {M : Type w} [TopologicalSpace M] (x : M) (d : ℕ)
    (z : localHomology (A := ModuleCat.{w} ℤ) (ModuleCat.of ℤ (ULift.{w} ℤ))
      ({x} : Set M) d) : Prop :=
  ∀ y, ∃ c : ℤ, c • z = y

/-- An element of local homology is a local orientation exactly when every class is an integral
multiple of it. -/
theorem isLocalOrientation_iff {M : Type w} [TopologicalSpace M] (x : M) (d : ℕ)
    (z : localHomology (A := ModuleCat.{w} ℤ) (ModuleCat.of ℤ (ULift.{w} ℤ))
      ({x} : Set M) d) :
    IsLocalOrientation x d z ↔ ∀ y, ∃ c : ℤ, c • z = y := Iff.rfl

/-- An element of local homology is a local orientation exactly when its `ℤ`-multiples are the
whole group. -/
theorem isLocalOrientation_iff_zmultiples_eq_top {M : Type w} [TopologicalSpace M] (x : M)
    (d : ℕ) (z : localHomology (A := ModuleCat.{w} ℤ) (ModuleCat.of ℤ (ULift.{w} ℤ))
      ({x} : Set M) d) :
    IsLocalOrientation x d z ↔ AddSubgroup.zmultiples z = ⊤ := by
  rw [AddSubgroup.eq_top_iff']
  exact forall_congr' fun _ ↦ AddSubgroup.mem_zmultiples_iff.symm

/-- An element of local homology is a local orientation exactly when it spans the whole group as a
`ℤ`-module. -/
theorem isLocalOrientation_iff_span_eq_top {M : Type w} [TopologicalSpace M] (x : M) (d : ℕ)
    (z : localHomology (A := ModuleCat.{w} ℤ) (ModuleCat.of ℤ (ULift.{w} ℤ))
      ({x} : Set M) d) :
    IsLocalOrientation x d z ↔ Submodule.span ℤ {z} = ⊤ := by
  rw [Submodule.span_singleton_eq_top_iff, isLocalOrientation_iff]
  exact forall_congr' fun _ ↦ exists_congr fun c ↦
    iff_of_eq (congrArg (· = _) (int_smul_eq_zsmul _ c _)).symm

/-- The integral local homology group at `x` in degree `d`, with its local orientations. -/
abbrev LocalOrientation (M : Type w) [TopologicalSpace M] (x : M) (d : ℕ) :=
  {z : localHomology (A := ModuleCat.{w} ℤ) (ModuleCat.of ℤ (ULift.{w} ℤ))
      ({x} : Set M) d //
    IsLocalOrientation x d z}

/-- The inverse image of `1` under an isomorphism from integral local homology to `ℤ` is a local
orientation. -/
theorem isLocalOrientation_inv_one {M : Type w} [TopologicalSpace M] {x : M} {d : ℕ}
    (e : localHomology (A := ModuleCat.{w} ℤ) (ModuleCat.of ℤ (ULift.{w} ℤ))
      ({x} : Set M) d ≅
      ModuleCat.of ℤ (ULift.{w} ℤ)) :
    IsLocalOrientation x d (e.inv 1) := by
  intro y
  refine ⟨(e.hom y).down, ?_⟩
  have h : (e.hom y).down • (1 : ULift.{w} ℤ) = e.hom y := by
    apply ULift.ext
    simp
  calc
    (e.hom y).down • e.inv 1 = e.inv ((e.hom y).down • (1 : ULift.{w} ℤ)) :=
      (e.inv.hom.toAddMonoidHom.map_zsmul ((e.hom y).down) (1 : ULift.{w} ℤ)).symm
    _ = e.inv (e.hom y) := congrArg e.inv h
    _ = y := e.hom_inv_id_apply y

/-- Reversing a local orientation gives a local orientation. -/
theorem IsLocalOrientation.neg {M : Type w} [TopologicalSpace M] {x : M} {d : ℕ}
    {z : localHomology (A := ModuleCat.{w} ℤ) (ModuleCat.of ℤ (ULift.{w} ℤ)) ({x} : Set M) d}
    (hz : IsLocalOrientation x d z) : IsLocalOrientation x d (-z) := by
  intro y
  obtain ⟨c, rfl⟩ := hz y
  exact ⟨-c, by simp⟩

/-- Reversal of local orientations is involutive. -/
instance {M : Type w} [TopologicalSpace M] {x : M} {d : ℕ} :
    InvolutiveNeg (LocalOrientation M x d) where
  neg z := ⟨-z.val, z.property.neg⟩
  neg_neg z := Subtype.ext (neg_neg z.val)

@[simp]
lemma LocalOrientation.coe_neg {M : Type w} [TopologicalSpace M] {x : M} {d : ℕ}
    (z : LocalOrientation M x d) : (↑(-z) : localHomology (A := ModuleCat.{w} ℤ)
      (ModuleCat.of ℤ (ULift.{w} ℤ)) ({x} : Set M) d) = -z.val :=
  (rfl)

/-- An isomorphism of integral local homology groups preserves the generator condition. The two
groups may sit in different degrees. -/
theorem IsLocalOrientation.map {M N : Type w} [TopologicalSpace M] [TopologicalSpace N]
    {x : M} {y : N} {d d' : ℕ}
    {z : localHomology (A := ModuleCat.{w} ℤ) (ModuleCat.of ℤ (ULift.{w} ℤ)) ({x} : Set M) d}
    (hz : IsLocalOrientation x d z)
    (e : localHomology (A := ModuleCat.{w} ℤ) (ModuleCat.of ℤ (ULift.{w} ℤ)) ({x} : Set M) d ≅
      localHomology (A := ModuleCat.{w} ℤ) (ModuleCat.of ℤ (ULift.{w} ℤ)) ({y} : Set N) d') :
    IsLocalOrientation y d' (e.hom z) :=
  (isLocalOrientation_iff_zmultiples_eq_top _ _ _).2 <|
    zmultiples_apply_eq_top_of_surjective (ConcreteCategory.bijective_of_isIso e.hom).2
      ((isLocalOrientation_iff_zmultiples_eq_top _ _ _).1 hz)

/-- An isomorphism of pairs `(M, M ∖ {x}) ≅ (N, N ∖ {y})` carries local orientations at `x` to
local orientations at `y`, through the isomorphism it induces on integral local homology. -/
def LocalOrientation.map {M N : Type w} [TopologicalSpace M] [TopologicalSpace N]
    {x : M} {y : N} {d : ℕ} (z : LocalOrientation M x d)
    (e : TopPair.ofSubset ({x}ᶜ : Set (TopCat.of M)) ≅
      TopPair.ofSubset ({y}ᶜ : Set (TopCat.of N))) :
    LocalOrientation N y d :=
  ⟨(TopPair.singularHomologyMap e.hom (ModuleCat.of ℤ (ULift.{w} ℤ)) d).hom z.val,
    z.property.map
      { hom := TopPair.singularHomologyMap e.hom (ModuleCat.of ℤ (ULift.{w} ℤ)) d
        inv := TopPair.singularHomologyMap e.inv (ModuleCat.of ℤ (ULift.{w} ℤ)) d
        hom_inv_id := by
          rw [← TopPair.singularHomologyMap_comp, Iso.hom_inv_id, TopPair.singularHomologyMap_id]
        inv_hom_id := by
          rw [← TopPair.singularHomologyMap_comp, Iso.inv_hom_id,
            TopPair.singularHomologyMap_id] }⟩

@[simp]
lemma LocalOrientation.coe_map {M N : Type w} [TopologicalSpace M] [TopologicalSpace N]
    {x : M} {y : N} {d : ℕ} (z : LocalOrientation M x d)
    (e : TopPair.ofSubset ({x}ᶜ : Set (TopCat.of M)) ≅
      TopPair.ofSubset ({y}ᶜ : Set (TopCat.of N))) :
    ((z.map e : LocalOrientation N y d) : localHomology (A := ModuleCat.{w} ℤ)
      (ModuleCat.of ℤ (ULift.{w} ℤ)) ({y} : Set N) d) =
      (TopPair.singularHomologyMap e.hom (ModuleCat.of ℤ (ULift.{w} ℤ)) d).hom z.val :=
  (rfl)

/-- Transport along an isomorphism of pairs commutes with reversal of local orientations. -/
@[simp]
lemma LocalOrientation.map_neg {M N : Type w} [TopologicalSpace M] [TopologicalSpace N]
    {x : M} {y : N} {d : ℕ} (z : LocalOrientation M x d)
    (e : TopPair.ofSubset ({x}ᶜ : Set (TopCat.of M)) ≅
      TopPair.ofSubset ({y}ᶜ : Set (TopCat.of N))) :
    (-z).map e = -z.map e :=
  Subtype.ext (_root_.map_neg _ z.val)

/-- Transport along the identity isomorphism of pairs is the identity. -/
@[simp]
lemma LocalOrientation.map_refl {M : Type w} [TopologicalSpace M] {x : M} {d : ℕ}
    (z : LocalOrientation M x d) : z.map (Iso.refl _) = z :=
  Subtype.ext (by rw [coe_map, Iso.refl_hom, TopPair.singularHomologyMap_id, ModuleCat.id_apply])

/-- Transport along a composite isomorphism of pairs is the composite of the transports. -/
lemma LocalOrientation.map_trans {M N P : Type w} [TopologicalSpace M] [TopologicalSpace N]
    [TopologicalSpace P] {x : M} {y : N} {p : P} {d : ℕ} (z : LocalOrientation M x d)
    (e : TopPair.ofSubset ({x}ᶜ : Set (TopCat.of M)) ≅
      TopPair.ofSubset ({y}ᶜ : Set (TopCat.of N)))
    (e' : TopPair.ofSubset ({y}ᶜ : Set (TopCat.of N)) ≅
      TopPair.ofSubset ({p}ᶜ : Set (TopCat.of P))) :
    z.map (e ≪≫ e') = (z.map e).map e' :=
  Subtype.ext (by
    rw [coe_map, coe_map, coe_map, Iso.trans_hom, TopPair.singularHomologyMap_comp,
      ModuleCat.comp_apply])

/-- If integral local homology is isomorphic to `ℤ`, its generators are precisely the inverse
images of `1` and `-1`. In particular a top-degree local homology fibre has two orientations. -/
theorem isLocalOrientation_iff_eq_or_eq_neg_inv_one {M : Type w} [TopologicalSpace M]
    {x : M} {d : ℕ}
    (e : localHomology (A := ModuleCat.{w} ℤ) (ModuleCat.of ℤ (ULift.{w} ℤ)) ({x} : Set M) d ≅
      ModuleCat.of ℤ (ULift.{w} ℤ))
    (z : localHomology (A := ModuleCat.{w} ℤ) (ModuleCat.of ℤ (ULift.{w} ℤ)) ({x} : Set M) d) :
    IsLocalOrientation x d z ↔ z = e.inv 1 ∨ z = -e.inv 1 := by
  constructor
  · intro hz
    obtain ⟨c, hc⟩ := hz (e.inv 1)
    have he : c * (e.hom z).down = 1 := by
      have h := congrArg (fun a ↦ (e.hom a).down) hc
      simpa using h
    rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp he with ⟨_, h⟩ | ⟨_, h⟩
    · left
      calc
        z = e.inv (e.hom z) := (e.hom_inv_id_apply z).symm
        _ = e.inv 1 := congrArg e.inv (ULift.ext h)
    · right
      calc
        z = e.inv (e.hom z) := (e.hom_inv_id_apply z).symm
        _ = e.inv (-1) := congrArg e.inv (ULift.ext h)
        _ = -e.inv 1 := e.inv.hom.map_neg 1
  · rintro (rfl | rfl)
    · exact isLocalOrientation_inv_one e
    · exact (isLocalOrientation_inv_one e).neg

/-- A local homology fibre isomorphic to `ℤ` has exactly two local orientations. -/
theorem nat_card_localOrientation {M : Type w} [TopologicalSpace M] {x : M} {d : ℕ}
    (e : localHomology (A := ModuleCat.{w} ℤ) (ModuleCat.of ℤ (ULift.{w} ℤ)) ({x} : Set M) d ≅
      ModuleCat.of ℤ (ULift.{w} ℤ)) :
    Nat.card (LocalOrientation M x d) = 2 := by
  let z : LocalOrientation M x d := ⟨e.inv 1, isLocalOrientation_inv_one e⟩
  refine Nat.card_eq_two_iff.mpr ⟨z, -z, ?_, ?_⟩
  · intro h
    have h' := congrArg (fun a : LocalOrientation M x d ↦ (e.hom a.val).down) h
    simp [z] at h'
  · apply Set.eq_univ_of_forall
    intro a
    rcases (isLocalOrientation_iff_eq_or_eq_neg_inv_one e a.val).mp a.property with h | h
    · exact Set.mem_insert_iff.mpr (Or.inl (Subtype.ext h))
    · exact Set.mem_insert_of_mem _ (Set.mem_singleton_iff.mpr (Subtype.ext h))

/-- In a local homology fibre isomorphic to `ℤ`, two local orientations agree up to sign. -/
theorem IsLocalOrientation.eq_or_eq_neg {M : Type w} [TopologicalSpace M] {x : M} {d : ℕ}
    (e : localHomology (A := ModuleCat.{w} ℤ) (ModuleCat.of ℤ (ULift.{w} ℤ)) ({x} : Set M) d ≅
      ModuleCat.of ℤ (ULift.{w} ℤ))
    {z z' : localHomology (A := ModuleCat.{w} ℤ) (ModuleCat.of ℤ (ULift.{w} ℤ)) ({x} : Set M) d}
    (hz : IsLocalOrientation x d z) (hz' : IsLocalOrientation x d z') : z' = z ∨ z' = -z := by
  rcases (isLocalOrientation_iff_eq_or_eq_neg_inv_one e z).1 hz with rfl | rfl <;>
    rcases (isLocalOrientation_iff_eq_or_eq_neg_inv_one e z').1 hz' with rfl | rfl <;> simp

/-- In a local homology fibre isomorphic to `ℤ`, a local orientation has infinite order. -/
theorem IsLocalOrientation.zsmul_eq_zero_iff {M : Type w} [TopologicalSpace M] {x : M} {d : ℕ}
    (e : localHomology (A := ModuleCat.{w} ℤ) (ModuleCat.of ℤ (ULift.{w} ℤ)) ({x} : Set M) d ≅
      ModuleCat.of ℤ (ULift.{w} ℤ))
    {z : localHomology (A := ModuleCat.{w} ℤ) (ModuleCat.of ℤ (ULift.{w} ℤ)) ({x} : Set M) d}
    (hz : IsLocalOrientation x d z) {c : ℤ} : c • z = 0 ↔ c = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
  have h' := congrArg (fun a ↦ (e.hom a).down) h
  rcases (isLocalOrientation_iff_eq_or_eq_neg_inv_one e z).1 hz with rfl | rfl <;> simpa using h'

/-- In a local homology fibre isomorphic to `ℤ`, a local orientation differs from its reversal. -/
theorem IsLocalOrientation.neg_ne {M : Type w} [TopologicalSpace M] {x : M} {d : ℕ}
    (e : localHomology (A := ModuleCat.{w} ℤ) (ModuleCat.of ℤ (ULift.{w} ℤ)) ({x} : Set M) d ≅
      ModuleCat.of ℤ (ULift.{w} ℤ))
    {z : localHomology (A := ModuleCat.{w} ℤ) (ModuleCat.of ℤ (ULift.{w} ℤ)) ({x} : Set M) d}
    (hz : IsLocalOrientation x d z) : -z ≠ z := by
  intro h
  have h2 : (2 : ℤ) • z = 0 := by
    rw [two_zsmul]
    nth_rw 1 [← h]
    exact neg_add_cancel z
  exact two_ne_zero ((hz.zsmul_eq_zero_iff e).1 h2)

/-- In a local homology fibre isomorphic to `ℤ`, two local orientations agree up to sign. -/
theorem LocalOrientation.eq_or_eq_neg {M : Type w} [TopologicalSpace M] {x : M} {d : ℕ}
    (e : localHomology (A := ModuleCat.{w} ℤ) (ModuleCat.of ℤ (ULift.{w} ℤ)) ({x} : Set M) d ≅
      ModuleCat.of ℤ (ULift.{w} ℤ))
    (z z₀ : LocalOrientation M x d) : z = z₀ ∨ z = -z₀ :=
  (z₀.property.eq_or_eq_neg e z.property).imp Subtype.ext Subtype.ext

/-- In a local homology fibre isomorphic to `ℤ`, a local orientation `z` identifies `ℤ` with the
fibre: every class is a unique integral multiple `c • z` of `z`. -/
def IsLocalOrientation.linearEquiv {M : Type w} [TopologicalSpace M] {x : M} {d : ℕ}
    (e : localHomology (A := ModuleCat.{w} ℤ) (ModuleCat.of ℤ (ULift.{w} ℤ)) ({x} : Set M) d ≅
      ModuleCat.of ℤ (ULift.{w} ℤ))
    {z : localHomology (A := ModuleCat.{w} ℤ) (ModuleCat.of ℤ (ULift.{w} ℤ)) ({x} : Set M) d}
    (hz : IsLocalOrientation x d z) :
    ℤ ≃ₗ[ℤ] localHomology (A := ModuleCat.{w} ℤ) (ModuleCat.of ℤ (ULift.{w} ℤ)) ({x} : Set M) d :=
  LinearEquiv.ofBijective (LinearMap.toSpanSingleton ℤ _ z)
    ⟨(injective_iff_map_eq_zero _).2 fun c hc ↦
        (hz.zsmul_eq_zero_iff e).1 ((int_smul_eq_zsmul _ c z).symm.trans hc),
      fun y ↦ let ⟨c, hc⟩ := hz y; ⟨c, (int_smul_eq_zsmul _ c z).trans hc⟩⟩

/-- The identification of `ℤ` with the fibre given by a local orientation `z` sends `c` to
`c • z`. -/
@[simp]
theorem IsLocalOrientation.linearEquiv_apply {M : Type w} [TopologicalSpace M] {x : M} {d : ℕ}
    (e : localHomology (A := ModuleCat.{w} ℤ) (ModuleCat.of ℤ (ULift.{w} ℤ)) ({x} : Set M) d ≅
      ModuleCat.of ℤ (ULift.{w} ℤ))
    {z : localHomology (A := ModuleCat.{w} ℤ) (ModuleCat.of ℤ (ULift.{w} ℤ)) ({x} : Set M) d}
    (hz : IsLocalOrientation x d z) (c : ℤ) : hz.linearEquiv e c = c • z :=
  (LinearMap.toSpanSingleton_apply ℤ _ z c).trans (int_smul_eq_zsmul _ c z)

/-- The identification of `ℤ` with the fibre given by a local orientation `z` sends `1` to `z`. -/
theorem IsLocalOrientation.linearEquiv_apply_one {M : Type w} [TopologicalSpace M] {x : M} {d : ℕ}
    (e : localHomology (A := ModuleCat.{w} ℤ) (ModuleCat.of ℤ (ULift.{w} ℤ)) ({x} : Set M) d ≅
      ModuleCat.of ℤ (ULift.{w} ℤ))
    {z : localHomology (A := ModuleCat.{w} ℤ) (ModuleCat.of ℤ (ULift.{w} ℤ)) ({x} : Set M) d}
    (hz : IsLocalOrientation x d z) : hz.linearEquiv e 1 = z :=
  (hz.linearEquiv_apply e 1).trans (one_smul ℤ z)

/-- The identification of `ℤ` with the fibre given by a local orientation `z` sends `z` back
to `1`. -/
@[simp]
theorem IsLocalOrientation.linearEquiv_symm_self {M : Type w} [TopologicalSpace M] {x : M}
    {d : ℕ}
    (e : localHomology (A := ModuleCat.{w} ℤ) (ModuleCat.of ℤ (ULift.{w} ℤ)) ({x} : Set M) d ≅
      ModuleCat.of ℤ (ULift.{w} ℤ))
    {z : localHomology (A := ModuleCat.{w} ℤ) (ModuleCat.of ℤ (ULift.{w} ℤ)) ({x} : Set M) d}
    (hz : IsLocalOrientation x d z) : (hz.linearEquiv e).symm z = 1 :=
  (hz.linearEquiv e).symm_apply_eq.2 (hz.linearEquiv_apply_one e).symm

/-- The local orientation at `x` selected by a chart and its chart-induced local homology
isomorphism. -/
def localOrientationOfChart {M E : Type w} [TopologicalSpace M] [T2Space M]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ : OpenPartialHomeomorph M E) {x : M} (hx : x ∈ φ.source) {n : ℕ}
    (hn : finrank ℝ E = n + 1) : LocalOrientation M x (n + 1) :=
  ⟨(singularHomologyComplSingletonIsoOfFinrankEq (A := ModuleCat.{w} ℤ)
      (ModuleCat.of ℤ (ULift.{w} ℤ)) φ hx hn).inv 1,
    isLocalOrientation_inv_one _⟩

/-- A point in a positive-dimensional finite-dimensional charted space has a local orientation.
The chart computation identifies its local homology group with `ℤ`, and the inverse image of `1`
is a generator. -/
theorem exists_localOrientation_of_chart {M E : Type w} [TopologicalSpace M] [T2Space M]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ChartedSpace E M]
    (x : M) {n : ℕ} (hn : finrank ℝ E = n + 1) :
    Nonempty (LocalOrientation M x (n + 1)) :=
  ⟨localOrientationOfChart (chartAt E x) (mem_chart_source E x) hn⟩

/-- A point with a zero-dimensional chart also has a local orientation, represented by the class
of the point in degree-zero local homology. -/
def localOrientationOfZeroDimChart {M E : Type w} [TopologicalSpace M] [T2Space M]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (φ : OpenPartialHomeomorph M E) {x : M} (hx : x ∈ φ.source)
    (hn : finrank ℝ E = 0) : LocalOrientation M x 0 :=
  ⟨(singularHomologyComplSingletonIsoOfFinrankEqZero (A := ModuleCat.{w} ℤ)
      (ModuleCat.of ℤ (ULift.{w} ℤ)) φ hx hn).inv 1,
    isLocalOrientation_inv_one _⟩

/-- The positive local orientation of a zero-dimensional chart is the actual relative point
class of the original point. In particular the chart contributes no additional sign. -/
@[simp]
theorem localOrientationOfZeroDimChart_coe
    {M E : Type w} [TopologicalSpace M] [T2Space M]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (φ : OpenPartialHomeomorph M E) {x : M} (hx : x ∈ φ.source) (hE : finrank ℝ E = 0) :
    (localOrientationOfZeroDimChart φ hx hE).val =
      localHomologyPointClass (ModuleCat.of ℤ (ULift.{w} ℤ)) {x} x 1 := by
  exact singularHomologyComplSingletonIsoOfFinrankEqZero_inv_eq_localHomologyPointClass_apply
    (ModuleCat.of ℤ (ULift.{w} ℤ)) φ hx hE 1

/-- Zero-dimensional charts, even in different real normed models, select the same positive
local point class. -/
theorem localOrientationOfZeroDimChart_eq
    {M E F : Type w} [TopologicalSpace M] [T2Space M]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (φ : OpenPartialHomeomorph M E) (ψ : OpenPartialHomeomorph M F) {x : M}
    (hx : x ∈ φ.source) (hx' : x ∈ ψ.source) (hE : finrank ℝ E = 0) (hF : finrank ℝ F = 0) :
    localOrientationOfZeroDimChart φ hx hE = localOrientationOfZeroDimChart ψ hx' hF := by
  apply Subtype.ext
  rw [localOrientationOfZeroDimChart_coe,
    localOrientationOfZeroDimChart_coe]

/-- Every point of a zero-dimensional finite-dimensional charted space has a local orientation. -/
theorem exists_localOrientation_of_zero_dim_chart {M E : Type w} [TopologicalSpace M]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [ChartedSpace E M] (x : M) (hn : finrank ℝ E = 0) : Nonempty (LocalOrientation M x 0) :=
  haveI : Subsingleton E := Module.finrank_zero_iff.1 hn
  haveI : DiscreteTopology M := ChartedSpace.discreteTopology (H := E) M
  ⟨localOrientationOfZeroDimChart (chartAt E x) (mem_chart_source E x) hn⟩

/-! ### Local orientations of a manifold -/

section Manifold

variable {M E : Type w} [TopologicalSpace M] [T2Space M] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [ChartedSpace E M] {d : ℕ}

namespace LocalOrientation

/-- In the dimension of the manifold, every point has a local orientation. -/
theorem nonempty (hd : finrank ℝ E = d) (x : M) : Nonempty (LocalOrientation M x d) := by
  cases d with
  | zero => exact exists_localOrientation_of_zero_dim_chart x hd
  | succ d => exact exists_localOrientation_of_chart x hd

/-- In the dimension of the manifold, every point has exactly two local orientations. -/
theorem nat_card_eq_two (hd : finrank ℝ E = d) (x : M) : Nat.card (LocalOrientation M x d) = 2 := by
  subst hd
  exact nat_card_localOrientation
    (singularHomologyComplSingletonFinrankIso _ (chartAt E x) (mem_chart_source E x))

/-- In the dimension of the manifold, the local orientations at a point form a finite set. -/
theorem finite (hd : finrank ℝ E = d) (x : M) : Finite (LocalOrientation M x d) :=
  Nat.finite_of_card_ne_zero (by simp [nat_card_eq_two hd x])

/-- In the dimension of the manifold, two local orientations at a point agree up to reversal. -/
theorem eq_or_eq_neg_of_finrank_eq (hd : finrank ℝ E = d) {x : M}
    (z z' : LocalOrientation M x d) : z' = z ∨ z' = -z := by
  subst hd
  exact LocalOrientation.eq_or_eq_neg
    (singularHomologyComplSingletonFinrankIso _ (chartAt E x) (mem_chart_source E x)) z' z

/-- In the dimension of the manifold, a local orientation differs from its reversal. -/
theorem neg_ne (hd : finrank ℝ E = d) {x : M} (z : LocalOrientation M x d) : -z ≠ z := by
  subst hd
  exact fun h ↦ IsLocalOrientation.neg_ne
    (singularHomologyComplSingletonFinrankIso _ (chartAt E x) (mem_chart_source E x))
    z.property (congrArg Subtype.val h)

end LocalOrientation

end Manifold

end TauCeti

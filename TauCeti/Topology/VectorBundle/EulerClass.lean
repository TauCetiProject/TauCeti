/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Topology.VectorBundle.Constructions
public import TauCeti.AlgebraicTopology.Cohomology.HomotopyInvariance
public import TauCeti.Topology.Category.TopPair
import TauCeti.Topology.VectorBundle.Smul

/-!
# Thom classes and Euler classes of vector bundles

Let `E → B` be a real vector bundle with finite-dimensional model fibre `F` of rank `r`, and let
`E₀ ⊆ E` be the complement of the zero section (`TauCeti.zeroSectionCompl`). The *Thom pair* of
the bundle is the topological pair `(E, E₀)` (`TauCeti.thomPair`). A *Thom class* is a relative
class `u ∈ Hʳ(E, E₀)` whose restriction to every fibre pair `(E_b, E_b ∖ {0})` generates the
cohomology of that pair (`TauCeti.IsThomClass`). With ordinary integral coefficients (specified
below) this is a cohomological orientation of the bundle; by the Thom isomorphism theorem, which
is not formalized here, every orientation determines a unique Thom class, and `-u` belongs to the
opposite orientation.

The *Euler class* of a relative class `u ∈ Hⁿ(E, E₀)` is its image in `Hⁿ(B)` under the
restriction `Hⁿ(E, E₀) ⟶ Hⁿ(E)` followed by pullback along the zero section
(`TauCeti.eulerClass`). With ordinary integral coefficients, for a Thom class this is the Euler
class of the oriented bundle, the characteristic class whose evaluation on surfaces appears in
the Euler class inequalities for foliations.

The Euler class is natural under maps of Thom pairs covering a map of bases
(`TauCeti.eulerClass_naturality`), in particular under pullback of bundles
(`TauCeti.eulerClass_pullback`), and pullback carries Thom classes to Thom classes
(`TauCeti.IsThomClass.pullback`). A bundle with a nowhere-vanishing continuous section has zero
Euler class (`TauCeti.eulerClass_eq_zero_of_forall_ne_zero`): the zero section is homotopic,
through `t • s`, to a section with values in `E₀`, and every relative class restricts to zero on
`E₀`. So a trivial bundle of positive rank has zero Euler class
(`TauCeti.eulerClass_trivial_eq_zero`).

Cohomology is the singular cohomology of `TauCeti/AlgebraicTopology/Cohomology/`, with the same
general coefficients: `Hom(C(X; R), M)` in a `k`-linear abelian category `C`. Integral cohomology
uses `C := ModuleCat ℤ`, `k := ℤ`, and `R = M = ModuleCat.of ℤ ℤ`.

## Main definitions

* `TauCeti.zeroSectionCompl`: the nonzero vectors `E₀` of a bundle.
* `TauCeti.thomPair`: the Thom pair `(E, E₀)`.
* `TauCeti.fiberThomPairMap`: the inclusion of the fibre pair `(E_b, E_b ∖ {0})` into the Thom
  pair.
* `TauCeti.IsThomClass`: a relative class restricting to a generator on every fibre.
* `TauCeti.eulerClass`: the Euler class `Hⁿ(E, E₀) ⟶ Hⁿ(B)`.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §9 (the fundamental class `u ∈ Hⁿ(E, E₀; ℤ)` of an oriented bundle, the Euler
  class, its naturality and its vanishing for a bundle with a nowhere-zero section) and §10 (the
  Thom isomorphism).
* A. Hatcher, *Vector Bundles and K-Theory*, §4.D (Thom classes).
-/

public section

noncomputable section

open Bundle CategoryTheory Limits Set Module

universe w v u

namespace TauCeti

section Pair

variable {B : Type w} (F : Type*) (E : B → Type w) [∀ b, Zero (E b)]

/-- The complement `E₀` of the zero section in the total space of a bundle: its nonzero
vectors. -/
def zeroSectionCompl : Set (TotalSpace F E) :=
  {v | v.2 ≠ 0}

variable {F E} in
@[simp]
theorem mem_zeroSectionCompl {v : TotalSpace F E} : v ∈ zeroSectionCompl F E ↔ v.2 ≠ 0 :=
  Iff.rfl

/-- The nonzero vectors are the complement of the range of the zero section. -/
theorem zeroSectionCompl_eq_compl_range :
    zeroSectionCompl F E = (range (zeroSection F E))ᶜ := by
  ext ⟨b, x⟩
  simp only [mem_zeroSectionCompl, mem_compl_iff, mem_range, not_exists]
  constructor
  · rintro hx b' h
    cases h
    exact hx rfl
  · intro h hx
    exact h b (by rw [hx]; rfl)

variable [TopologicalSpace (TotalSpace F E)]

/-- The Thom pair `(E, E₀)` of a bundle: its total space relative to the complement of the zero
section. -/
abbrev thomPair : TopPair.{w} :=
  TopPair.ofSubset (X := TopCat.of (TotalSpace F E)) (zeroSectionCompl F E)

end Pair

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] {R : C}
  {k : Type*} [Ring k] [Linear k C] {M : C}

section ThomClass

variable {B : Type w} [TopologicalSpace B] (F : Type*) [TopologicalSpace F] (E : B → Type w)
  [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
  [∀ b, Zero (E b)]

/-- The inclusion `(E_b, E_b ∖ {0}) ⟶ (E, E₀)` of the fibre over `b` into the Thom pair. -/
def fiberThomPairMap (b : B) :
    TopPair.ofSubset (X := TopCat.of (E b)) ({0}ᶜ : Set (E b)) ⟶ thomPair F E :=
  TopPair.ofSubsetMap (TopCat.ofHom ⟨TotalSpace.mk b, FiberBundle.continuous_totalSpaceMk F E b⟩)
    fun _ hx ↦ hx

@[simp]
theorem fiberThomPairMap_fst_apply (b : B) (x : E b) :
    TopPair.Hom.fst (fiberThomPairMap F E b) x = TotalSpace.mk b x := by
  unfold fiberThomPairMap
  exact TopPair.ofSubsetMap_fst_apply _ _ _

variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A Thom class of a real vector bundle with finite-dimensional model fibre `F` of rank
`r = finrank ℝ F`: a relative class `u ∈ Hʳ(E, E₀)` whose restriction to the fibre pair
`(E_b, E_b ∖ {0})` over every point `b` generates the `k`-module `Hʳ(E_b, E_b ∖ {0})`. With ordinary
integral coefficients (`C := ModuleCat ℤ`, `k := ℤ`, `R = M = ModuleCat.of ℤ ℤ`) this is the notion
of a cohomological orientation of the bundle.

Finite-dimensionality of `F` is part of the predicate: otherwise `finrank ℝ F = 0` and the
degree-zero condition would hold vacuously, so a bundle with infinite-dimensional fibres has no
Thom class. -/
def IsThomClass (u : (thomPair F E).singularCohomology R k M (finrank ℝ F)) : Prop :=
  FiniteDimensional ℝ F ∧
    ∀ b, Submodule.span k {TopPair.singularCohomologyMap (fiberThomPairMap F E b) _ u} = ⊤

variable {F E} in
theorem isThomClass_iff {u : (thomPair F E).singularCohomology R k M (finrank ℝ F)} :
    IsThomClass F E u ↔ FiniteDimensional ℝ F ∧
      ∀ b, Submodule.span k {TopPair.singularCohomologyMap (fiberThomPairMap F E b) _ u} = ⊤ :=
  Iff.rfl

variable {F E} in
/-- Negation preserves the fibrewise generator condition, so the negative of a Thom class is a
Thom class. -/
theorem IsThomClass.neg {u : (thomPair F E).singularCohomology R k M (finrank ℝ F)}
    (hu : IsThomClass F E u) : IsThomClass F E (-u) := by
  refine ⟨hu.1, fun b ↦ ?_⟩
  rw [map_neg, ← Set.neg_singleton, Submodule.span_neg]
  exact hu.2 b

end ThomClass

section Pullback

variable {B : Type w} [TopologicalSpace B] (F : Type*) (E : B → Type w)
  [TopologicalSpace (TotalSpace F E)] [∀ b, Zero (E b)] {B' : Type w}
  [TopologicalSpace B'] (f : C(B', B))

local instance (b' : B') : Zero (((⇑f) *ᵖ E) b') :=
  inferInstanceAs (Zero (E (f b')))

/-- The map `(f*E, (f*E)₀) ⟶ (E, E₀)` of Thom pairs covering a continuous map `f : B' → B`. -/
def pullbackThomPairMap : thomPair F ((⇑f) *ᵖ E) ⟶ thomPair F E :=
  TopPair.ofSubsetMap (TopCat.ofHom ⟨Pullback.lift f, Pullback.continuous_lift F E f⟩)
    fun _ hv ↦ hv

@[simp]
theorem pullbackThomPairMap_fst_apply (v : TotalSpace F ((⇑f) *ᵖ E)) :
    TopPair.Hom.fst (pullbackThomPairMap F E f) v = Pullback.lift f v := by
  unfold pullbackThomPairMap
  exact TopPair.ofSubsetMap_fst_apply _ _ _

variable [TopologicalSpace F] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]

/-- The fibre of the Thom pair of `f*E` over `b'` is included in the Thom pair of `E` as the fibre
over `f b'`. -/
theorem fiberThomPairMap_comp_pullbackThomPairMap (b' : B') :
    fiberThomPairMap F ((⇑f) *ᵖ E) b' ≫ pullbackThomPairMap F E f = fiberThomPairMap F E (f b') :=
  TopPair.ofSubsetMap_comp_ofSubsetMap_of_comp_eq _ _ _ (TopCat.ext fun _ ↦ rfl)

variable [NormedAddCommGroup F] [NormedSpace ℝ F]

variable {F E} in
/-- The pullback of a Thom class of `E` along a continuous map `f` is a Thom class of `f*E`. -/
theorem IsThomClass.pullback {u : (thomPair F E).singularCohomology R k M (finrank ℝ F)}
    (hu : IsThomClass F E u) :
    IsThomClass F ((⇑f) *ᵖ E) (TopPair.singularCohomologyMap (pullbackThomPairMap F E f) _ u) := by
  refine ⟨hu.1, fun b' ↦ ?_⟩
  rw [← ConcreteCategory.comp_apply, ← TopPair.singularCohomologyMap_comp,
    fiberThomPairMap_comp_pullbackThomPairMap]
  exact hu.2 (f b')

end Pullback

section EulerClass

variable {B : Type w} [TopologicalSpace B] (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
  (E : B → Type w) [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E]

/-- The zero section `B ⟶ E` of a real vector bundle, as a morphism of topological spaces into
the ambient space of the Thom pair. -/
def zeroSectionHom : TopCat.of B ⟶ (thomPair F E).fst :=
  TopCat.ofHom ⟨zeroSection F E, Trivialization.continuous_zeroSection ℝ⟩

@[simp]
theorem zeroSectionHom_apply (b : B) : zeroSectionHom F E b = zeroSection F E b :=
  (rfl)

variable (R k M) in
/-- The Euler class `e(u) ∈ Hⁿ(B)` of a relative class `u ∈ Hⁿ(E, E₀)` of a real vector bundle, as
a morphism `Hⁿ(E, E₀) ⟶ Hⁿ(B)`: restriction from the Thom pair to the total space, followed by
pullback along the zero section. With ordinary integral coefficients (`C := ModuleCat ℤ`,
`k := ℤ`, `R = M = ModuleCat.of ℤ ℤ`), the Euler class of an oriented bundle is the image of its
Thom class (`TauCeti.IsThomClass`). -/
def eulerClass (n : ℕ) :
    (thomPair F E).singularCohomology R k M n ⟶ (TopCat.of B).singularCohomology R k M n :=
  (thomPair F E).singularCohomologyπ R k M n ≫ TopCat.singularCohomologyMap (zeroSectionHom F E) n

theorem eulerClass_def (n : ℕ) :
    eulerClass R k M F E n = (thomPair F E).singularCohomologyπ R k M n ≫
      TopCat.singularCohomologyMap (zeroSectionHom F E) n :=
  (rfl)

/-- **Naturality of the Euler class.** A map of Thom pairs `φ : (E', E'₀) ⟶ (E, E₀)` which carries
the zero section over a map of bases `f : B' ⟶ B` to the zero section intertwines the Euler
classes. -/
theorem eulerClass_naturality {B' : Type w} [TopologicalSpace B'] {F' : Type*}
    [NormedAddCommGroup F'] [NormedSpace ℝ F'] {E' : B' → Type w}
    [TopologicalSpace (TotalSpace F' E')] [∀ b, AddCommMonoid (E' b)] [∀ b, Module ℝ (E' b)]
    [∀ b, TopologicalSpace (E' b)] [FiberBundle F' E'] [VectorBundle ℝ F' E']
    (φ : thomPair F' E' ⟶ thomPair F E) (f : TopCat.of B' ⟶ TopCat.of B)
    (h : zeroSectionHom F' E' ≫ TopPair.Hom.fst φ = f ≫ zeroSectionHom F E) (n : ℕ) :
    TopPair.singularCohomologyMap φ n ≫ eulerClass R k M F' E' n =
      eulerClass R k M F E n ≫ TopCat.singularCohomologyMap f n := by
  rw [eulerClass_def, eulerClass_def, Category.assoc, ← TopCat.singularCohomologyMap_comp, ← h,
    TopCat.singularCohomologyMap_comp, TopPair.singularCohomologyπ_naturality_assoc]

/-- **A nowhere-vanishing section kills the Euler class.** If a real vector bundle has a continuous
section `s` with `s b ≠ 0` for every `b`, then its Euler class vanishes in every degree: the zero
section is homotopic through `t • s` to `s`, which takes values in `E₀`, and every relative class
restricts to zero on `E₀`. -/
theorem eulerClass_eq_zero_of_forall_ne_zero {s : ∀ b, E b}
    (hs : Continuous fun b ↦ TotalSpace.mk' F b (s b)) (hs₀ : ∀ b, s b ≠ 0) (n : ℕ) :
    eulerClass R k M F E n = 0 := by
  -- The section `s`, corestricted to the nonzero vectors.
  let s₀ : TopCat.of B ⟶ (thomPair F E).snd :=
    TopCat.ofHom ⟨fun b ↦ ⟨TotalSpace.mk' F b (s b), hs₀ b⟩, hs.subtype_mk _⟩
  -- The straight-line homotopy `t • s` from the zero section to `s`.
  let H : TopCat.Homotopy (zeroSectionHom F E) (s₀ ≫ (thomPair F E).map) :=
    { toFun := fun p ↦ TotalSpace.mk' F p.2 ((p.1 : ℝ) • s p.2)
      continuous_toFun :=
        (continuous_subtype_val.comp continuous_fst).smul_totalSpace (hs.comp continuous_snd)
      map_zero_left := fun b ↦ by simp; rfl
      map_one_left := fun b ↦ by simp; rfl }
  rw [eulerClass_def, H.congr_singularCohomologyMap, TopCat.singularCohomologyMap_comp,
    TopPair.singularCohomologyπ_comp_singularCohomologyMap_assoc, zero_comp]

variable {B' : Type w} [TopologicalSpace B'] (f : C(B', B)) in
/-- The Euler class of a pullback bundle `f*E` is the pullback along `f` of the Euler class of
`E`. -/
theorem eulerClass_pullback (n : ℕ) :
    TopPair.singularCohomologyMap (pullbackThomPairMap F E f) n ≫
        eulerClass R k M F ((⇑f) *ᵖ E) n =
      eulerClass R k M F E n ≫ TopCat.singularCohomologyMap (TopCat.ofHom f) n :=
  eulerClass_naturality F E _ _
    (TopCat.ext fun _ ↦ (pullbackThomPairMap_fst_apply F E f _).trans rfl) n

end EulerClass

/-- A trivial real vector bundle `B × V` of positive rank has zero Euler class in every degree. -/
theorem eulerClass_trivial_eq_zero (B : Type w) [TopologicalSpace B] (V : Type w)
    [NormedAddCommGroup V] [NormedSpace ℝ V] [Nontrivial V] (n : ℕ) :
    eulerClass R k M V (Trivial B V) n = 0 := by
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  exact eulerClass_eq_zero_of_forall_ne_zero (s := fun _ ↦ x) V (Trivial B V)
    ((Trivial.homeomorphProd B V).symm.continuous.comp (continuous_id.prodMk continuous_const))
    (fun _ ↦ hx) n

end TauCeti

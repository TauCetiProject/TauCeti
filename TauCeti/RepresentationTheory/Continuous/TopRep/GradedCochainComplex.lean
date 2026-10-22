/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplex
public import TauCeti.LinearAlgebra.Graded.LinearMap
public import TauCeti.RepresentationTheory.Continuous.TopRep.Subquotients

/-!
# The cochain complex of a graded topological representation

Let `M` be a topological representation of `G` whose underlying module carries a `ℤ`-indexed
family `ℳ` of submodules, each stable under the action, and let `d : M ⟶ M` be an equivariant
endomorphism of degree one with `d ≫ d = 0`. Then the subrepresentations on the pieces `ℳ n` for
`n : ℕ`, with the restrictions of `d`, form a cochain complex of topological representations. This
file performs that assembly.

Constructions such as tensor products and tensor induction are easier to write on a single carrier
than on a family of summands: the total module of a resolution carries one action and one
differential, and a tensor product of such modules again does. Continuous cohomology, on the other
hand, is computed from complexes in `TopRep k G` indexed by `ℕ` (`TopRep.resolution'`), and the
comparison of `TopRep.ResolutionContraction` takes such a complex as input. This construction
passes from the first description to the second. No decomposition hypothesis on `ℳ` is needed, and
the pieces in negative degrees are ignored.

This is the counterpart for topological representations of `TauCeti.gradedCochainComplex`, which
assembles a `ℤ`-indexed complex of modules from the same kind of data.

## Main definitions

* `TopRep.gradedCochainComplex`: the cochain complex whose degree-`n` term is the subrepresentation
  on `ℳ n` and whose differential is the restriction of `d`.
* `TopRep.gradedCochainComplexι`: the inclusion of each term into `M`.
* `TopRep.gradedCochainComplexRestrict`: the linear maps between terms induced by a homogeneous
  linear endomorphism of `M`.
* `TopRep.gradedCochainComplexInvariant`: a fixed homogeneous vector of `M` as an invariant
  element of a term.
* `TopRep.gradedCochainComplexLift`: the factorization through a term of a morphism into `M`
  with values in one piece of the grading.

## Main results

* `TopRep.gradedCochainComplex_d_comp_ι`: the inclusions intertwine the differential of the
  complex with `d`.
* `TopRep.gradedCochainComplex_d_apply`: the same statement on an element.
* `TopRep.gradedCochainComplexLift_comp_ι`, `TopRep.gradedCochainComplexLift_unique`: the
  factorization through a term is characterized by its composite with the inclusion.
* `TopRep.gradedCochainComplex_d_invariant`: a fixed homogeneous vector killed by `d` is an
  invariant cocycle of the complex.
-/

public section

open CategoryTheory

namespace TopRep

universe u v w

variable {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Monoid G]
  (M : TopRep.{w} k G) (ℳ : ℤ → Submodule k M.V)
  (hρ : ∀ n g x, x ∈ ℳ n → M.ρ g x ∈ ℳ n)
  (d : M ⟶ M) (hd : TauCeti.LinearMap.IsHomogeneous d.hom.toLinearMap ℳ ℳ 1) (hdd : d ≫ d = 0)

include hd in
/-- An endomorphism of degree one carries the degree-`n` piece into the degree-`n + 1` piece, with
the degree written as the cast of a natural number. -/
private theorem mem_succ_of_isHomogeneous (n : ℕ) (x : M.V) (hx : x ∈ ℳ n) :
    d.hom x ∈ ℳ ((n + 1 : ℕ) : ℤ) := by
  rw [Nat.cast_succ]
  exact hd.map_mem hx

/-- The **cochain complex of a graded topological representation**: its degree-`n` term is the
subrepresentation on the piece `ℳ n`, with the induced topology, and its differential is the
restriction of the degree-one endomorphism `d`, which squares to zero. -/
-- The body is exposed so that an element of `ℳ n` is an element of the degree-`n` term: this is
-- how a homogeneous vector of `M`, such as a cocycle written on the total module, is fed to the
-- complex.
@[expose] noncomputable def gradedCochainComplex : CochainComplex (TopRep.{w} k G) ℕ :=
  CochainComplex.of
    (fun n ↦ M.subrepresentation (ℳ n) (hρ n))
    (fun n ↦ subrepresentationLift M (ℳ ((n + 1 : ℕ) : ℤ))
      (hρ _)
      (subrepresentationι M (ℳ n) (hρ n) ≫ d)
      (fun y ↦ by
        rw [comp_apply, subrepresentationι_apply]
        exact mem_succ_of_isHomogeneous M ℳ d hd n y.1 y.2))
    (fun n ↦ by
      -- Both sides lift the zero morphism into `M` through the inclusion of `ℳ (n + 2)`.
      have hlift := subrepresentationLift_unique M (ℳ ((n + 1 + 1 : ℕ) : ℤ)) (hρ _)
        (0 : M.subrepresentation (ℳ n) (hρ n) ⟶ M) (fun _ ↦ zero_mem _)
      refine (hlift _ ?_).trans (hlift 0 Limits.zero_comp).symm
      rw [Category.assoc, subrepresentationLift_comp_ι, subrepresentationLift_comp_ι_assoc,
        Category.assoc, hdd, Limits.comp_zero])

/-- The degree-`n` term of `gradedCochainComplex` is the subrepresentation on `ℳ n`. -/
theorem gradedCochainComplex_X (n : ℕ) :
    (M.gradedCochainComplex ℳ hρ d hd hdd).X n =
      M.subrepresentation (ℳ n) (hρ n) :=
  (rfl)

/-- The action on a term of `gradedCochainComplex` is the action of `M`. -/
@[simp]
theorem gradedCochainComplex_ρ_apply (n : ℕ) (g : G)
    (v : ((M.gradedCochainComplex ℳ hρ d hd hdd).X n).V) :
    (((M.gradedCochainComplex ℳ hρ d hd hdd).X n).ρ g v).1 = M.ρ g v.1 :=
  congrArg Subtype.val (subrepresentation_ρ_apply M (ℳ n) (hρ n) g v)

/-- A map into a term of `gradedCochainComplex` is continuous exactly when it is continuous as a
map into `M`, since the term carries the topology induced from `M`. -/
theorem continuous_gradedCochainComplex_X_iff {Z : Type*} [TopologicalSpace Z] (n : ℕ)
    (f : Z → ((M.gradedCochainComplex ℳ hρ d hd hdd).X n).V) :
    Continuous f ↔ Continuous fun z ↦ (f z).1 :=
  Topology.IsInducing.subtypeVal.continuous_iff

/-- A morphism into `M` with values in `ℳ n` factors through the degree-`n` term of
`gradedCochainComplex`. -/
noncomputable def gradedCochainComplexLift {Y : TopRep.{w} k G} (n : ℕ) (f : Y ⟶ M)
    (hf : ∀ y, f.hom y ∈ ℳ n) : Y ⟶ (M.gradedCochainComplex ℳ hρ d hd hdd).X n :=
  subrepresentationLift M (ℳ n) (hρ n) f hf

/-- The factorization through a term of `gradedCochainComplex` evaluates by the original
morphism. -/
@[simp]
theorem gradedCochainComplexLift_apply {Y : TopRep.{w} k G} (n : ℕ) (f : Y ⟶ M)
    (hf : ∀ y, f.hom y ∈ ℳ n) (y : Y.V) :
    ((M.gradedCochainComplexLift ℳ hρ d hd hdd n f hf).hom y).1 = f.hom y :=
  congrArg Subtype.val (subrepresentationLift_apply M (ℳ n) (hρ n) f hf y)

/-- A linear endomorphism `f` of `M` of degree `q` restricts to a linear map from the degree-`m`
term of `gradedCochainComplex` to the degree-`n` term whenever `m + q = n`. Such maps need not be
equivariant: the contracting homotopies of `TopRep.ResolutionContraction` are of this form. -/
noncomputable def gradedCochainComplexRestrict (f : M.V →ₗ[k] M.V) {q : ℤ}
    (hf : TauCeti.LinearMap.IsHomogeneous f ℳ ℳ q) {m n : ℕ} (hmn : (m : ℤ) + q = n) :
    ((M.gradedCochainComplex ℳ hρ d hd hdd).X m).V →ₗ[k]
      ((M.gradedCochainComplex ℳ hρ d hd hdd).X n).V :=
  f.restrict (p := ℳ m) (q := ℳ n) fun _ hv ↦ hmn ▸ hf.map_mem hv

/-- The restriction of a homogeneous linear endomorphism to the terms of `gradedCochainComplex`
evaluates by the endomorphism. -/
@[simp]
theorem gradedCochainComplexRestrict_apply (f : M.V →ₗ[k] M.V) {q : ℤ}
    (hf : TauCeti.LinearMap.IsHomogeneous f ℳ ℳ q) {m n : ℕ} (hmn : (m : ℤ) + q = n)
    (v : ((M.gradedCochainComplex ℳ hρ d hd hdd).X m).V) :
    (M.gradedCochainComplexRestrict ℳ hρ d hd hdd f hf hmn v).1 = f v.1 :=
  (rfl)

/-- The inclusion of the degree-`n` term of `gradedCochainComplex` into the graded
representation. -/
noncomputable def gradedCochainComplexι (n : ℕ) :
    (M.gradedCochainComplex ℳ hρ d hd hdd).X n ⟶ M :=
  subrepresentationι M (ℳ n) (hρ n)

/-- The inclusion of a term of `gradedCochainComplex` is the inclusion of the submodule. -/
@[simp]
theorem gradedCochainComplexι_apply (n : ℕ) (v : ((M.gradedCochainComplex ℳ hρ d hd hdd).X n).V) :
    (M.gradedCochainComplexι ℳ hρ d hd hdd n).hom v = v.1 :=
  subrepresentationι_apply M (ℳ n) _ v

/-- The inclusions of the terms of `gradedCochainComplex` are injective. -/
theorem gradedCochainComplexι_injective (n : ℕ) :
    Function.Injective (M.gradedCochainComplexι ℳ hρ d hd hdd n).hom :=
  subrepresentationι_injective M (ℳ n) _

/-- The factorization through a term of `gradedCochainComplex`, followed by the inclusion, is the
original morphism. -/
@[reassoc (attr := simp)]
theorem gradedCochainComplexLift_comp_ι {Y : TopRep.{w} k G} (n : ℕ) (f : Y ⟶ M)
    (hf : ∀ y, f.hom y ∈ ℳ n) :
    M.gradedCochainComplexLift ℳ hρ d hd hdd n f hf ≫ M.gradedCochainComplexι ℳ hρ d hd hdd n =
      f :=
  subrepresentationLift_comp_ι M (ℳ n) (hρ n) f hf

/-- A morphism into a term of `gradedCochainComplex` is the factorization of its composite with
the inclusion. -/
theorem gradedCochainComplexLift_unique {Y : TopRep.{w} k G} (n : ℕ) (f : Y ⟶ M)
    (hf : ∀ y, f.hom y ∈ ℳ n) (g : Y ⟶ (M.gradedCochainComplex ℳ hρ d hd hdd).X n)
    (hg : g ≫ M.gradedCochainComplexι ℳ hρ d hd hdd n = f) :
    g = M.gradedCochainComplexLift ℳ hρ d hd hdd n f hf :=
  subrepresentationLift_unique M (ℳ n) (hρ n) f hf g hg

/-- **The inclusions intertwine the differentials**: the differential of `gradedCochainComplex`
followed by the inclusion is the inclusion followed by `d`. -/
@[reassoc]
theorem gradedCochainComplex_d_comp_ι (n : ℕ) :
    (M.gradedCochainComplex ℳ hρ d hd hdd).d n (n + 1) ≫
        M.gradedCochainComplexι ℳ hρ d hd hdd (n + 1) =
      M.gradedCochainComplexι ℳ hρ d hd hdd n ≫ d := by
  dsimp only [gradedCochainComplex]
  rw [CochainComplex.of_d]
  exact subrepresentationLift_comp_ι _ _ _ _ _

/-- The differential of `gradedCochainComplex` on an element is `d` applied to it in `M`. -/
@[simp]
theorem gradedCochainComplex_d_apply (n : ℕ)
    (v : ((M.gradedCochainComplex ℳ hρ d hd hdd).X n).V) :
    (((M.gradedCochainComplex ℳ hρ d hd hdd).d n (n + 1)).hom v).1 = d.hom v.1 := by
  rw [← gradedCochainComplexι_apply, ← gradedCochainComplexι_apply, ← comp_apply,
    gradedCochainComplex_d_comp_ι, comp_apply]

/-- A vector of `ℳ n` fixed by `G` is an invariant element of the degree-`n` term of
`gradedCochainComplex`. -/
def gradedCochainComplexInvariant (n : ℕ) (z : M.V) (hz : z ∈ ℳ n) (hinv : ∀ g, M.ρ g z = z) :
    ((M.gradedCochainComplex ℳ hρ d hd hdd).X n).ρ.invariants :=
  ⟨⟨z, hz⟩, fun g ↦ Subtype.ext ((gradedCochainComplex_ρ_apply M ℳ hρ d hd hdd n g _).trans
    (hinv g))⟩

/-- The invariant element of a term of `gradedCochainComplex` given by a fixed vector of `ℳ n` is
that vector. -/
@[simp]
theorem gradedCochainComplexInvariant_val (n : ℕ) (z : M.V) (hz : z ∈ ℳ n)
    (hinv : ∀ g, M.ρ g z = z) :
    ((M.gradedCochainComplexInvariant ℳ hρ d hd hdd n z hz hinv :
      ((M.gradedCochainComplex ℳ hρ d hd hdd).X n).V)).1 = z :=
  (rfl)

/-- A fixed vector of `ℳ n` killed by `d` is a cocycle of `gradedCochainComplex`. -/
theorem gradedCochainComplex_d_invariant {n : ℕ} {z : M.V} (hz : z ∈ ℳ n)
    (hinv : ∀ g, M.ρ g z = z) (hdz : d.hom z = 0) :
    ((M.gradedCochainComplex ℳ hρ d hd hdd).d n (n + 1)).hom
      (M.gradedCochainComplexInvariant ℳ hρ d hd hdd n z hz hinv :
        ((M.gradedCochainComplex ℳ hρ d hd hdd).X n).V) = 0 :=
  Subtype.ext ((gradedCochainComplex_d_apply M ℳ hρ d hd hdd n _).trans hdz)

end TopRep

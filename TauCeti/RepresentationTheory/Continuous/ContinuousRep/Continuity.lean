/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import TauCeti.RepresentationTheory.Continuous.ContinuousRep.Basic

/-!
# Continuity criteria, trivial representations, and forgetful comparison

Mathlib's `ContRepresentation R Γ V` asks each operator `ρ g` to be continuous on `V`, whereas
`TauCeti.ContinuousRep Γ A M` asks the action map `Γ × M → M` to be jointly continuous. Over a
discrete carrier `M`, every linear endomorphism is continuous, yet an action of a topological group
`Γ` is jointly continuous if and only if every point stabilizer `{g : Γ | ρ g x = x}` is open
(`Representation.continuous_iff_isOpen_stabilizer_of_discrete`). Thus `TauCeti.ContinuousRep` embeds
injectively into `ContRepresentation` with image precisely the jointly continuous representations
(`TauCeti.ContinuousRep.toContRepresentation_injective`,
`TauCeti.ContinuousRep.range_toContRepresentation`).

When `M` is a finite module over a topological ring `A` and carries its `A`-module topology
(`IsModuleTopology A M`), joint continuity reduces to simpler pointwise conditions because any
finite generating family `v : ι → M` presents `M` as an open quotient of `ι → A`:

* **Orbit continuity** (`Representation.continuous_iff_orbit`,
  `Representation.continuous_iff_orbit_of_span_eq_top`): over a topological ring `A`, `Γ × M → M` is
  continuous if and only if every orbit map `g ↦ ρ g x` (or every orbit map on a finite generating
  family) is continuous.
* **Matrix-coefficient continuity** (`Representation.continuous_iff_matrixCoeff`,
  `Representation.continuous_iff_basis_repr`, `Representation.continuous_iff_toMatrix_apply`): over
  a topological semiring `A`, when `M` is finite projective (in particular finite free), `Γ × M → M`
  is continuous if and only if every matrix coefficient `g ↦ φ (ρ g x)` (`φ : M →ₗ[A] A`, `x : M`)
  is continuous, or in a finite basis `b`, every coordinate entry
  `g ↦ LinearMap.toMatrix b b (ρ g) i j` is continuous.

This file also defines the trivial continuous representation `TauCeti.ContinuousRep.trivial` and its
compatibility with `ofCharacter 1` and scalar extension.

## Main definitions

* `TauCeti.ContinuousRep.ofContRepresentation`: upgrades a jointly continuous `ContRepresentation`
  to a `ContinuousRep`.
* `TauCeti.ContinuousRep.ofOrbit`, `TauCeti.ContinuousRep.ofOrbitOfSpanEqTop`,
  `TauCeti.ContinuousRep.ofMatrixCoeff`, `TauCeti.ContinuousRep.ofToMatrix`,
  `TauCeti.ContinuousRep.ofIsOpenStabilizer`: constructors for `ContinuousRep` on modules carrying
  their module or discrete topology.
* `TauCeti.ContinuousRep.trivial`: the trivial jointly continuous representation on any topological
  module.

## Main results

* `TauCeti.ContinuousRep.toContRepresentation_injective` and
  `TauCeti.ContinuousRep.range_toContRepresentation`: `toContRepresentation` is injective with range
  the jointly continuous `ContRepresentation`s.
* `Representation.continuous_iff_orbit_of_span_eq_top` and `Representation.continuous_iff_orbit`:
  joint continuity on a module with the module topology over a topological ring is equivalent to
  orbit continuity on a finite generating family (hence on all vectors when `M` is finitely
  generated).
* `Representation.continuous_iff_matrixCoeff` and `Representation.continuous_iff_toMatrix_apply`:
  joint continuity on a finite projective (or finite free) module over a topological semiring is
  equivalent to continuity of matrix coefficients or basis matrix entries.
* `Representation.continuous_iff_isOpen_stabilizer_of_discrete`: on a discrete carrier, joint
  continuity of a group action is equivalent to openness of every stabilizer.

## References

* H. Darmon, F. Diamond and R. Taylor, *Fermat's Last Theorem*, §2.1, p. 52.
* J. Newton and J. A. Thorne, *Symmetric power functoriality for holomorphic modular forms*, §1.2.
* G. Böckle, M. Harris, C. Khare and J. A. Thorne, *Potential automorphy of `G`-local systems*, §2.
-/

public section

open scoped TensorProduct

namespace Representation

section OrbitModuleTopology

variable {Γ A M : Type*} [Monoid Γ] [TopologicalSpace Γ] [Ring A] [TopologicalSpace A]
  [IsTopologicalSemiring A] [AddCommGroup M] [Module A M] [TopologicalSpace M]
  [IsModuleTopology A M]

/-- **Continuity on a finite generating family.** Over a topological ring `A`, a linear action of
`Γ` on a module `M` carrying its module topology is jointly continuous if and only if the orbit map
`g ↦ ρ g (v i)` is continuous for each member of a finite spanning family `v : ι → M`. -/
theorem continuous_iff_orbit_of_span_eq_top {ι : Type*} [Finite ι] (ρ : Representation A Γ M)
    {v : ι → M} (hv : Submodule.span A (Set.range v) = ⊤) :
    Continuous (fun p : Γ × M => ρ p.1 p.2) ↔ ∀ i, Continuous fun g => ρ g (v i) := by
  refine ⟨fun h i => h.comp (continuous_id.prodMk continuous_const), fun horb => ?_⟩
  cases nonempty_fintype ι
  have := IsModuleTopology.toContinuousAdd A M
  -- The linear combination map `(ι → A) → M` is an open quotient map for the module topologies.
  let q : (ι → A) →ₗ[A] M := Fintype.linearCombination A v
  have hq : IsOpenQuotientMap q :=
    IsModuleTopology.isOpenQuotientMap_of_surjective
      (LinearMap.range_eq_top.mp (by rw [Fintype.range_linearCombination, hv]))
  refine ((IsOpenQuotientMap.id.prodMap hq).continuous_comp_iff).mp ?_
  have hF : Continuous fun p : Γ × (ι → A) => ∑ i, p.2 i • ρ p.1 (v i) := by
    fun_prop
  refine hF.congr fun p => ?_
  simp [q, Fintype.linearCombination_apply, map_sum, map_smul]

/-- Set-indexed form of `Representation.continuous_iff_orbit_of_span_eq_top`: joint continuity is
detected on any finite spanning subset `s ⊆ M`. -/
theorem continuous_iff_orbit_of_span_eq_top_set (ρ : Representation A Γ M) {s : Set M}
    (hs : s.Finite) (hspan : Submodule.span A s = ⊤) :
    Continuous (fun p : Γ × M => ρ p.1 p.2) ↔ ∀ x ∈ s, Continuous fun g => ρ g x := by
  have : Finite s := hs.to_subtype
  rw [ρ.continuous_iff_orbit_of_span_eq_top (v := Subtype.val)
    (by simpa [Subtype.range_coe] using hspan)]
  exact Subtype.forall

/-- **Joint continuity from orbit continuity.** On a finitely generated module carrying its module
topology over a topological ring, a linear representation is jointly continuous if and only if
every orbit map `g ↦ ρ g x` is continuous. -/
theorem continuous_iff_orbit [Module.Finite A M] (ρ : Representation A Γ M) :
    Continuous (fun p : Γ × M => ρ p.1 p.2) ↔ ∀ x, Continuous fun g => ρ g x := by
  obtain ⟨n, v, hv⟩ := Module.Finite.exists_fin (R := A) (M := M)
  exact ⟨fun h x => h.comp (continuous_id.prodMk continuous_const),
    fun h => (ρ.continuous_iff_orbit_of_span_eq_top hv).mpr fun i => h (v i)⟩

end OrbitModuleTopology

section ProjectiveModuleTopology

variable {Γ A M : Type*} [Monoid Γ] [TopologicalSpace Γ] [Semiring A] [TopologicalSpace A]
  [IsTopologicalSemiring A] [AddCommMonoid M] [Module A M] [TopologicalSpace M]
  [IsModuleTopology A M]

/-- **Joint continuity from matrix coefficients.** On a finite projective (in particular, finite
free) module carrying its module topology over a topological semiring `A`, a representation `ρ` is
jointly continuous if and only if every matrix coefficient `g ↦ φ (ρ g x)` (`φ : M →ₗ[A] A`,
`x : M`) is continuous. -/
theorem continuous_iff_matrixCoeff [Module.Projective A M] [Module.Finite A M]
    (ρ : Representation A Γ M) :
    Continuous (fun p : Γ × M => ρ p.1 p.2) ↔
      ∀ (φ : M →ₗ[A] A) (x : M), Continuous fun g => φ (ρ g x) := by
  refine ⟨fun h φ x => (IsModuleTopology.continuous_of_linearMap φ).comp
    (h.comp (continuous_id.prodMk continuous_const)), fun h => ?_⟩
  obtain ⟨n, v, hv⟩ := Module.Finite.exists_fin (R := A) (M := M)
  have := IsModuleTopology.toContinuousAdd A M
  let q : (Fin n → A) →ₗ[A] M := Fintype.linearCombination A v
  obtain ⟨e, he⟩ := q.exists_rightInverse_of_surjective (by rwa [Fintype.range_linearCombination])
  have he_coord : ∀ j : Fin n, Continuous fun x : M => e x j :=
    fun j => IsModuleTopology.continuous_of_linearMap ((LinearMap.proj j).comp e)
  let c : Fin n → Fin n → Γ → A := fun i j g => ((LinearMap.proj i).comp e) (ρ g (v j))
  have hc : ∀ i j : Fin n, Continuous (c i j) :=
    fun i j => h ((LinearMap.proj i).comp e) (v j)
  let d : Fin n → M → A := fun j x => e x j
  have hd : ∀ j : Fin n, Continuous (d j) := he_coord
  have hF : Continuous fun p : Γ × M =>
      ∑ j : Fin n, d j p.2 • ∑ i : Fin n, c i j p.1 • v i := by
    fun_prop
  have hex : ∀ y : M, ∑ i : Fin n, e y i • v i = y := fun y => congr($he y)
  refine hF.congr fun p => ?_
  calc ∑ j : Fin n, d j p.2 • ∑ i : Fin n, c i j p.1 • v i
      = ∑ j : Fin n, e p.2 j • ρ p.1 (v j) := by
        simp_rw [c, d, LinearMap.comp_apply, LinearMap.proj_apply, hex]
    _ = ρ p.1 (∑ j : Fin n, e p.2 j • v j) := by simp only [map_sum, map_smul]
    _ = ρ p.1 p.2 := by rw [hex]

/-- **Joint continuity in basis coordinates.** For a finite basis `b` of `M` over a topological
semiring `A`, a representation `ρ` is jointly continuous for the module topology if and only if
every coordinate function `g ↦ b.repr (ρ g (b j)) i` is continuous. -/
theorem continuous_iff_basis_repr {ι : Type*} [Finite ι] (ρ : Representation A Γ M)
    (b : Module.Basis ι A M) :
    Continuous (fun p : Γ × M => ρ p.1 p.2) ↔
      ∀ i j, Continuous fun g => b.repr (ρ g (b j)) i := by
  refine ⟨fun h i j => (IsModuleTopology.continuous_of_linearMap (b.coord i)).comp
    (h.comp (continuous_id.prodMk continuous_const)), fun h => ?_⟩
  cases nonempty_fintype ι
  have := IsModuleTopology.toContinuousAdd A M
  let c : ι → ι → Γ → A := fun i j g => b.repr (ρ g (b j)) i
  have hc : ∀ i j : ι, Continuous (c i j) := h
  let d : ι → M → A := fun j x => b.repr x j
  have hd : ∀ j : ι, Continuous (d j) :=
    fun j => IsModuleTopology.continuous_of_linearMap (b.coord j)
  have hF : Continuous fun p : Γ × M =>
      ∑ j : ι, d j p.2 • ∑ i : ι, c i j p.1 • b i := by
    fun_prop
  refine hF.congr fun p => ?_
  calc ∑ j : ι, d j p.2 • ∑ i : ι, c i j p.1 • b i
      = ∑ j : ι, b.repr p.2 j • ρ p.1 (b j) := by simp_rw [c, d, b.sum_repr]
    _ = ρ p.1 (∑ j : ι, b.repr p.2 j • b j) := by simp only [map_sum, map_smul]
    _ = ρ p.1 p.2 := by rw [b.sum_repr]

end ProjectiveModuleTopology

section CommSemiringBasis

variable {Γ A M : Type*} [Monoid Γ] [TopologicalSpace Γ] [CommSemiring A] [TopologicalSpace A]
  [IsTopologicalSemiring A] [AddCommMonoid M] [Module A M] [TopologicalSpace M]
  [IsModuleTopology A M]

/-- **Joint continuity from matrix entries.** Over a commutative topological semiring `A`, in a
finite basis `b` of `M`, `ρ` is jointly continuous for the module topology if and only if each
matrix entry `g ↦ LinearMap.toMatrix b b (ρ g) i j` is continuous. -/
theorem continuous_iff_toMatrix_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : Representation A Γ M) (b : Module.Basis ι A M) :
    Continuous (fun p : Γ × M => ρ p.1 p.2) ↔
      ∀ i j, Continuous fun g => LinearMap.toMatrix b b (ρ g) i j := by
  simp_rw [LinearMap.toMatrix_apply, ρ.continuous_iff_basis_repr b]

end CommSemiringBasis

section Discrete

variable {Γ A M : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Semiring A]
  [AddCommMonoid M] [Module A M] [TopologicalSpace M] [DiscreteTopology M]

/-- **Discrete-carrier continuity criterion.** When `M` has the discrete topology and `Γ` is a
topological group, a representation `ρ : Representation A Γ M` is jointly continuous if and only if
the stabilizer `{g : Γ | ρ g x = x}` of every `x : M` is open in `Γ`. -/
theorem continuous_iff_isOpen_stabilizer_of_discrete (ρ : Representation A Γ M) :
    Continuous (fun p : Γ × M => ρ p.1 p.2) ↔ ∀ x : M, IsOpen {g : Γ | ρ g x = x} :=
  letI : MulAction Γ M := MulAction.compHom M (ρ : Γ →* Module.End A M)
  ⟨fun h => continuousSMul_iff_stabilizer_isOpen.mp ⟨h⟩,
    fun h => (continuousSMul_iff_stabilizer_isOpen.mpr h).continuous_smul⟩

end Discrete

end Representation

namespace TauCeti.ContinuousRep

/-! ### Forgetful map to `ContRepresentation` -/

section ContRepresentation

variable {Γ R V : Type*} [Monoid Γ] [TopologicalSpace Γ] [Ring R]
  [AddCommGroup V] [Module R V] [TopologicalSpace V] [IsTopologicalAddGroup V]

/-- **The forgetful map to `ContRepresentation` is injective.** -/
theorem toContRepresentation_injective :
    Function.Injective (toContRepresentation : ContinuousRep Γ R V → ContRepresentation R Γ V) :=
  fun _ _ h => ext fun g x => by simpa using congr($h g x)

/-- Two continuous representations have equal underlying `ContRepresentation`s if and only if they
are equal. -/
@[simp]
theorem toContRepresentation_inj {ρ σ : ContinuousRep Γ R V} :
    ρ.toContRepresentation = σ.toContRepresentation ↔ ρ = σ :=
  toContRepresentation_injective.eq_iff

/-- Forgetting from `ContinuousRep` to `ContRepresentation` and then to `Representation` gives the
underlying algebraic representation. -/
@[simp]
theorem toRepresentation_toContRepresentation (ρ : ContinuousRep Γ R V) :
    ρ.toContRepresentation.toRepresentation = ρ.toRepresentation := by
  ext g x
  exact ρ.toContRepresentation_apply g x

/-- Builds a `ContinuousRep` from a `ContRepresentation` whose action map `Γ × V → V` is jointly
continuous. -/
def ofContRepresentation (π : ContRepresentation R Γ V)
    (hπ : Continuous fun p : Γ × V => π p.1 p.2) : ContinuousRep Γ R V where
  toRepresentation := π.toRepresentation
  continuous_action := hπ

@[simp]
theorem ofContRepresentation_apply (π : ContRepresentation R Γ V)
    (hπ : Continuous fun p : Γ × V => π p.1 p.2) (g : Γ) (x : V) :
    ofContRepresentation π hπ g x = π g x :=
  (rfl)

@[simp]
theorem toRepresentation_ofContRepresentation (π : ContRepresentation R Γ V)
    (hπ : Continuous fun p : Γ × V => π p.1 p.2) :
    (ofContRepresentation π hπ).toRepresentation = π.toRepresentation :=
  (rfl)

@[simp]
theorem toContRepresentation_ofContRepresentation (π : ContRepresentation R Γ V)
    (hπ : Continuous fun p : Γ × V => π p.1 p.2) :
    (ofContRepresentation π hπ).toContRepresentation = π :=
  DFunLike.ext _ _ fun _ => ContinuousLinearMap.ext fun _ => by simp

@[simp]
theorem ofContRepresentation_toContRepresentation (ρ : ContinuousRep Γ R V)
    (h : Continuous fun p : Γ × V => ρ.toContRepresentation p.1 p.2) :
    ofContRepresentation ρ.toContRepresentation h = ρ := by
  ext g x
  simp

/-- A `ContRepresentation` lies in the image of `toContRepresentation` if and only if its action
`Γ × V → V` is jointly continuous. -/
theorem mem_range_toContRepresentation_iff {π : ContRepresentation R Γ V} :
    π ∈ Set.range (toContRepresentation : ContinuousRep Γ R V → ContRepresentation R Γ V) ↔
      Continuous fun p : Γ × V => π p.1 p.2 :=
  ⟨fun ⟨ρ, hρ⟩ =>
      hρ ▸ ρ.continuous_action.congr fun p => (ρ.toContRepresentation_apply p.1 p.2).symm,
    fun hπ => ⟨ofContRepresentation π hπ, toContRepresentation_ofContRepresentation π hπ⟩⟩

/-- **Range of `toContRepresentation`.** The image of `toContRepresentation` in
`ContRepresentation R Γ V` is the set of jointly continuous actions. -/
@[simp]
theorem range_toContRepresentation :
    Set.range (toContRepresentation : ContinuousRep Γ R V → ContRepresentation R Γ V) =
      {π : ContRepresentation R Γ V | Continuous fun p : Γ × V => π p.1 p.2} :=
  Set.ext fun _ => mem_range_toContRepresentation_iff

/-- On a finite module with its module topology over a topological ring, a `ContRepresentation`
lies in the image of `toContRepresentation` if and only if every orbit map is continuous. -/
theorem mem_range_toContRepresentation_iff_orbit [TopologicalSpace R] [IsTopologicalSemiring R]
    [IsModuleTopology R V] [Module.Finite R V] {π : ContRepresentation R Γ V} :
    π ∈ Set.range (toContRepresentation : ContinuousRep Γ R V → ContRepresentation R Γ V) ↔
      ∀ x, Continuous fun g => π g x := by
  rw [mem_range_toContRepresentation_iff]
  exact π.toRepresentation.continuous_iff_orbit

end ContRepresentation

/-! ### Constructors from orbit and matrix-coefficient continuity -/

section OrbitConstructors

variable {Γ A M : Type*} [Monoid Γ] [TopologicalSpace Γ] [Ring A] [TopologicalSpace A]
  [IsTopologicalSemiring A] [AddCommGroup M] [Module A M] [TopologicalSpace M]
  [IsModuleTopology A M]

/-- Constructs a `ContinuousRep` on a module carrying its module topology from orbit continuity on a
finite spanning family. -/
def ofOrbitOfSpanEqTop {ι : Type*} [Finite ι] (ρ : Representation A Γ M) {v : ι → M}
    (hv : Submodule.span A (Set.range v) = ⊤) (horb : ∀ i, Continuous fun g => ρ g (v i)) :
    ContinuousRep Γ A M where
  toRepresentation := ρ
  continuous_action := (ρ.continuous_iff_orbit_of_span_eq_top hv).mpr horb

@[simp]
theorem coe_ofOrbitOfSpanEqTop {ι : Type*} [Finite ι] (ρ : Representation A Γ M) {v : ι → M}
    (hv : Submodule.span A (Set.range v) = ⊤) (horb : ∀ i, Continuous fun g => ρ g (v i)) :
    ⇑(ofOrbitOfSpanEqTop ρ hv horb) = ρ :=
  (rfl)

@[simp]
theorem toRepresentation_ofOrbitOfSpanEqTop {ι : Type*} [Finite ι] (ρ : Representation A Γ M)
    {v : ι → M} (hv : Submodule.span A (Set.range v) = ⊤)
    (horb : ∀ i, Continuous fun g => ρ g (v i)) :
    (ofOrbitOfSpanEqTop ρ hv horb).toRepresentation = ρ :=
  (rfl)

/-- Constructs a `ContinuousRep` on a finite module carrying its module topology from continuity of
every orbit map `g ↦ ρ g x`. -/
def ofOrbit [Module.Finite A M] (ρ : Representation A Γ M)
    (horb : ∀ x, Continuous fun g => ρ g x) : ContinuousRep Γ A M where
  toRepresentation := ρ
  continuous_action := ρ.continuous_iff_orbit.mpr horb

@[simp]
theorem coe_ofOrbit [Module.Finite A M] (ρ : Representation A Γ M)
    (horb : ∀ x, Continuous fun g => ρ g x) :
    ⇑(ofOrbit ρ horb) = ρ :=
  (rfl)

@[simp]
theorem toRepresentation_ofOrbit [Module.Finite A M] (ρ : Representation A Γ M)
    (horb : ∀ x, Continuous fun g => ρ g x) :
    (ofOrbit ρ horb).toRepresentation = ρ :=
  (rfl)

end OrbitConstructors

section MatrixCoeffConstructors

variable {Γ A M : Type*} [Monoid Γ] [TopologicalSpace Γ] [Semiring A] [TopologicalSpace A]
  [IsTopologicalSemiring A] [AddCommMonoid M] [Module A M] [TopologicalSpace M]
  [IsModuleTopology A M]

/-- Constructs a `ContinuousRep` on a finite projective module carrying its module topology from
continuity of every matrix coefficient `g ↦ φ (ρ g x)`. -/
def ofMatrixCoeff [Module.Projective A M] [Module.Finite A M] (ρ : Representation A Γ M)
    (hcoeff : ∀ (φ : M →ₗ[A] A) (x : M), Continuous fun g => φ (ρ g x)) :
    ContinuousRep Γ A M where
  toRepresentation := ρ
  continuous_action := ρ.continuous_iff_matrixCoeff.mpr hcoeff

@[simp]
theorem coe_ofMatrixCoeff [Module.Projective A M] [Module.Finite A M] (ρ : Representation A Γ M)
    (hcoeff : ∀ (φ : M →ₗ[A] A) (x : M), Continuous fun g => φ (ρ g x)) :
    ⇑(ofMatrixCoeff ρ hcoeff) = ρ :=
  (rfl)

@[simp]
theorem toRepresentation_ofMatrixCoeff [Module.Projective A M] [Module.Finite A M]
    (ρ : Representation A Γ M)
    (hcoeff : ∀ (φ : M →ₗ[A] A) (x : M), Continuous fun g => φ (ρ g x)) :
    (ofMatrixCoeff ρ hcoeff).toRepresentation = ρ :=
  (rfl)

end MatrixCoeffConstructors

section OfToMatrix

variable {Γ A M : Type*} [Monoid Γ] [TopologicalSpace Γ] [CommSemiring A] [TopologicalSpace A]
  [IsTopologicalSemiring A] [AddCommMonoid M] [Module A M] [TopologicalSpace M]
  [IsModuleTopology A M]

/-- Constructs a `ContinuousRep` on a module with finite basis `b` and module topology from
continuity of the matrix entries `g ↦ LinearMap.toMatrix b b (ρ g) i j`. -/
def ofToMatrix {ι : Type*} [Fintype ι] [DecidableEq ι] (ρ : Representation A Γ M)
    (b : Module.Basis ι A M)
    (hmat : ∀ i j, Continuous fun g => LinearMap.toMatrix b b (ρ g) i j) :
    ContinuousRep Γ A M where
  toRepresentation := ρ
  continuous_action := (ρ.continuous_iff_toMatrix_apply b).mpr hmat

@[simp]
theorem coe_ofToMatrix {ι : Type*} [Fintype ι] [DecidableEq ι] (ρ : Representation A Γ M)
    (b : Module.Basis ι A M)
    (hmat : ∀ i j, Continuous fun g => LinearMap.toMatrix b b (ρ g) i j) :
    ⇑(ofToMatrix ρ b hmat) = ρ :=
  (rfl)

@[simp]
theorem toRepresentation_ofToMatrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : Representation A Γ M) (b : Module.Basis ι A M)
    (hmat : ∀ i j, Continuous fun g => LinearMap.toMatrix b b (ρ g) i j) :
    (ofToMatrix ρ b hmat).toRepresentation = ρ :=
  (rfl)

end OfToMatrix

/-! ### Discrete stabilizers -/

section Discrete

variable {Γ A M : Type*} [Monoid Γ] [TopologicalSpace Γ] [Semiring A]
  [AddCommMonoid M] [Module A M] [TopologicalSpace M] [DiscreteTopology M]

/-- On a discrete carrier, every point stabilizer of a `ContinuousRep` is open. -/
theorem isOpen_stabilizer_of_discrete (ρ : ContinuousRep Γ A M) (x : M) :
    IsOpen {g : Γ | ρ g x = x} :=
  (isOpen_discrete {x}).preimage (ρ.continuous_orbit x)

/-- Constructs a `ContinuousRep` of a topological group on a discrete module from openness of every
point stabilizer. -/
def ofIsOpenStabilizer {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (ρ : Representation A G M) (hstab : ∀ x : M, IsOpen {g : G | ρ g x = x}) :
    ContinuousRep G A M where
  toRepresentation := ρ
  continuous_action := ρ.continuous_iff_isOpen_stabilizer_of_discrete.mpr hstab

@[simp]
theorem coe_ofIsOpenStabilizer {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (ρ : Representation A G M) (hstab : ∀ x : M, IsOpen {g : G | ρ g x = x}) :
    ⇑(ofIsOpenStabilizer ρ hstab) = ρ :=
  (rfl)

@[simp]
theorem toRepresentation_ofIsOpenStabilizer {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (ρ : Representation A G M)
    (hstab : ∀ x : M, IsOpen {g : G | ρ g x = x}) :
    (ofIsOpenStabilizer ρ hstab).toRepresentation = ρ :=
  (rfl)

end Discrete

/-! ### The trivial representation -/

section Trivial

variable (Γ A M : Type*) [Monoid Γ] [TopologicalSpace Γ] [Semiring A]
  [AddCommMonoid M] [Module A M] [TopologicalSpace M]

/-- **The trivial jointly continuous representation** of `Γ` on `M`: every element of `Γ` acts as
the identity linear map, and `Γ × M → M` is the continuous second projection. -/
def trivial : ContinuousRep Γ A M where
  toRepresentation := Representation.trivial A Γ M
  continuous_action := continuous_snd

instance : Inhabited (ContinuousRep Γ A M) := ⟨trivial Γ A M⟩

variable {Γ A M}

/-- The trivial representation fixes every vector. -/
@[simp]
theorem trivial_apply (g : Γ) (x : M) : trivial Γ A M g x = x :=
  (rfl)

/-- Every operator of the trivial representation is `LinearMap.id`. -/
theorem trivial_apply_eq_id (g : Γ) : trivial Γ A M g = LinearMap.id :=
  (rfl)

/-- The algebraic representation underlying `ContinuousRep.trivial` is `Representation.trivial`. -/
@[simp]
theorem toRepresentation_trivial :
    (trivial Γ A M).toRepresentation = Representation.trivial A Γ M :=
  (rfl)

/-- Forgetting to `ContRepresentation` sends `ContinuousRep.trivial` to
`ContRepresentation.trivial`. -/
@[simp]
theorem toContRepresentation_trivial {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]
    [TopologicalSpace V] [IsTopologicalAddGroup V] :
    (trivial Γ R V).toContRepresentation = ContRepresentation.trivial R Γ V :=
  DFunLike.ext _ _ fun _ => ContinuousLinearMap.ext fun _ => by simp

/-- The rank-one representation attached to the trivial character `1 : Γ →ₜ* Aˣ` is `trivial`. -/
@[simp]
theorem ofCharacter_one {R : Type*} [CommSemiring R] [TopologicalSpace R] [ContinuousMul R] :
    ofCharacter (1 : Γ →ₜ* Rˣ) = trivial Γ R R := by
  ext
  simp

/-- Scalar extension of the trivial representation is the trivial representation on `B ⊗[A] M`. -/
@[simp]
theorem baseChange_trivial {R : Type*} [CommSemiring R] [TopologicalSpace R]
    {N : Type*} [AddCommMonoid N] [Module R N] [TopologicalSpace N] [IsModuleTopology R N]
    [Module.Finite R N] (B : Type*) [Ring B] [TopologicalSpace B] [IsTopologicalSemiring B]
    [Algebra R B] [ContinuousSMul R B] [TopologicalSpace (B ⊗[R] N)]
    [IsModuleTopology B (B ⊗[R] N)] :
    (trivial Γ R N).baseChange B = trivial Γ B (B ⊗[R] N) := by
  ext g x
  induction x using TensorProduct.inductionOn with
  | tmul b n => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy]

end Trivial

end TauCeti.ContinuousRep

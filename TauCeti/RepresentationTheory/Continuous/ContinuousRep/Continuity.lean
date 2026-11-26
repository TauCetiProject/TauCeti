/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Continuous.ContinuousRep.Basic
public import TauCeti.RepresentationTheory.Smooth.Basic

/-!
# Continuity constructors and discrete comparison for continuous representations

For a finite module `M` carrying its `A`-module topology (`IsModuleTopology A M`), the general
linear-map-family criteria in `TauCeti.Topology.Algebra.Module.ModuleTopology` reduce joint
continuity of an action `Γ × M → M` to pointwise conditions on `Γ`:

* **Orbit continuity** (`IsModuleTopology.continuous_linearMap_apply_iff`,
  `IsModuleTopology.continuous_linearMap_apply_iff_of_span_eq_top`, promoted by
  `TauCeti.ContinuousRep.ofOrbit` and `TauCeti.ContinuousRep.ofOrbitOfSpanEqTop`): over a
  topological ring `A`, continuity of every orbit map `g ↦ ρ g x` (or on a finite spanning family)
  is equivalent to joint continuity, promotes a `Representation` to a `ContinuousRep`, and
  characterizes the image of `toContRepresentation`
  (`TauCeti.ContinuousRep.mem_range_toContRepresentation_iff_orbit`).
* **Matrix-coefficient continuity**
  (`IsModuleTopology.continuous_linearMap_apply_iff_forall_dual_of_projective`,
  `TauCeti.ModuleTopology.continuous_linearMap_apply_iff_continuous_toMatrix`,
  `TauCeti.ContinuousRep.continuous_matrixCoeff`, `TauCeti.ContinuousRep.ofMatrixCoeff`,
  `TauCeti.ContinuousRep.ofToMatrix`): over a topological semiring `A`, on a finite projective
  module `M`, joint continuity is equivalent to continuity of every matrix coefficient
  `g ↦ φ (ρ g x)` (`φ : Module.Dual A M`, `x : M`), or in a finite basis `b` over a commutative
  topological semiring, continuity of every matrix entry `g ↦ LinearMap.toMatrix b b (ρ g) i j`.

On a discrete carrier `M`, every continuous representation of a group `G` has open point stabilizers
and hence a smooth underlying representation (`TauCeti.ContinuousRep.isOpen_stabilizer_of_discrete`,
`TauCeti.ContinuousRep.isSmooth_toRepresentation_of_discrete`). When right translations on `G` are
continuous (`ContinuousConstSMul Gᵐᵒᵖ G`), smoothness conversely promotes an algebraic
representation on a discrete module to a `ContinuousRep` (`TauCeti.ContinuousRep.ofIsSmooth`).

## Main definitions

* `TauCeti.ContinuousRep.ofOrbitOfSpanEqTop`, `TauCeti.ContinuousRep.ofOrbit`,
  `TauCeti.ContinuousRep.ofMatrixCoeff`, `TauCeti.ContinuousRep.ofToMatrix`: constructors for
  `ContinuousRep` on modules carrying their module topology.
* `TauCeti.ContinuousRep.ofIsSmooth`: constructor for `ContinuousRep` on a discrete carrier from a
  smooth representation of a group with continuous right translations.

## Main results

* `TauCeti.ContinuousRep.mem_range_toContRepresentation_iff_orbit`: on a finite module with its
  module topology over a topological ring, a `ContRepresentation` comes from a `ContinuousRep` if
  and only if every orbit map is continuous.
* `TauCeti.ContinuousRep.continuous_matrixCoeff`: every matrix coefficient `g ↦ φ (ρ g x)` is
  continuous when `M` carries its module topology.
* `TauCeti.ContinuousRep.isSmooth_toRepresentation_of_discrete`: on a discrete carrier, the
  underlying algebraic representation of a `ContinuousRep` of a group is smooth.

## References

* H. Darmon, F. Diamond and R. Taylor, *Fermat's Last Theorem*, §2.1, pp. 52–53.
* J. Newton and J. A. Thorne, *Symmetric power functoriality for holomorphic modular forms*, §1.2.
* G. Böckle, M. Harris, C. Khare and J. A. Thorne, *Potential automorphy of `G`-local systems*, §2.
-/

public section

namespace TauCeti.ContinuousRep

/-! ### Orbit characterization of the image of `toContRepresentation` -/

section ContRepresentation

variable {Γ R V : Type*} [Monoid Γ] [TopologicalSpace Γ] [Ring R] [TopologicalSpace R]
  [IsTopologicalSemiring R] [AddCommGroup V] [Module R V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [IsModuleTopology R V] [Module.Finite R V]

/-- On a finite module with its module topology over a topological ring, a `ContRepresentation`
lies in the image of `toContRepresentation` if and only if every orbit map is continuous. -/
theorem mem_range_toContRepresentation_iff_orbit {π : ContRepresentation R Γ V} :
    π ∈ Set.range (toContRepresentation : ContinuousRep Γ R V → ContRepresentation R Γ V) ↔
      ∀ x, Continuous fun g => π g x := by
  rw [mem_range_toContRepresentation_iff]
  exact IsModuleTopology.continuous_linearMap_apply_iff π.toRepresentation

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
  continuous_action := by
    have := IsModuleTopology.toContinuousAdd A M
    exact (IsModuleTopology.continuous_linearMap_apply_iff_of_span_eq_top ρ hv).mpr horb

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
  continuous_action := by
    have := IsModuleTopology.toContinuousAdd A M
    exact (IsModuleTopology.continuous_linearMap_apply_iff ρ).mpr horb

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

/-- Every matrix coefficient `g ↦ φ (ρ g x)` of a continuous representation on a module carrying
its module topology is continuous. -/
@[fun_prop]
theorem continuous_matrixCoeff (ρ : ContinuousRep Γ A M) (φ : Module.Dual A M) (x : M) :
    Continuous fun g => φ (ρ g x) :=
  (IsModuleTopology.continuous_of_linearMap φ).comp (ρ.continuous_orbit x)

/-- Constructs a `ContinuousRep` on a finite projective module carrying its module topology from
continuity of every matrix coefficient `g ↦ φ (ρ g x)`. -/
def ofMatrixCoeff [Module.Projective A M] [Module.Finite A M] (ρ : Representation A Γ M)
    (hcoeff : ∀ (φ : Module.Dual A M) (x : M), Continuous fun g => φ (ρ g x)) :
    ContinuousRep Γ A M where
  toRepresentation := ρ
  continuous_action :=
    (IsModuleTopology.continuous_linearMap_apply_iff_forall_dual_of_projective ρ).mpr hcoeff

@[simp]
theorem coe_ofMatrixCoeff [Module.Projective A M] [Module.Finite A M] (ρ : Representation A Γ M)
    (hcoeff : ∀ (φ : Module.Dual A M) (x : M), Continuous fun g => φ (ρ g x)) :
    ⇑(ofMatrixCoeff ρ hcoeff) = ρ :=
  (rfl)

@[simp]
theorem toRepresentation_ofMatrixCoeff [Module.Projective A M] [Module.Finite A M]
    (ρ : Representation A Γ M)
    (hcoeff : ∀ (φ : Module.Dual A M) (x : M), Continuous fun g => φ (ρ g x)) :
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
  continuous_action :=
    (ModuleTopology.continuous_linearMap_apply_iff_continuous_toMatrix b b ρ).mpr
      (continuous_matrix hmat)

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

/-! ### Discrete stabilizers and smooth representations -/

section Discrete

variable {Γ G A M : Type*} [Monoid Γ] [TopologicalSpace Γ]
  [Group G] [TopologicalSpace G] [Semiring A]
  [AddCommMonoid M] [Module A M] [TopologicalSpace M] [DiscreteTopology M]

/-- On a discrete carrier, every point stabilizer of a `ContinuousRep` is open. -/
theorem isOpen_stabilizer_of_discrete (ρ : ContinuousRep Γ A M) (x : M) :
    IsOpen {g : Γ | ρ g x = x} :=
  (isOpen_discrete {x}).preimage (ρ.continuous_orbit x)

/-- On a discrete carrier, the algebraic representation underlying a `ContinuousRep` of a group is
smooth. -/
instance isSmooth_toRepresentation_of_discrete (ρ : ContinuousRep G A M) :
    ρ.toRepresentation.IsSmooth :=
  ⟨fun x => ρ.isOpen_stabilizer_of_discrete x⟩

/-- Constructs a `ContinuousRep` on a discrete module from a smooth representation of a group with
continuous right translations. -/
def ofIsSmooth [ContinuousConstSMul Gᵐᵒᵖ G] (ρ : Representation A G M) [ρ.IsSmooth] :
    ContinuousRep G A M where
  toRepresentation := ρ
  continuous_action := ρ.continuous_iff_isSmooth.mpr inferInstance

@[simp]
theorem coe_ofIsSmooth [ContinuousConstSMul Gᵐᵒᵖ G] (ρ : Representation A G M) [ρ.IsSmooth] :
    ⇑(ofIsSmooth ρ) = ρ :=
  (rfl)

@[simp]
theorem toRepresentation_ofIsSmooth [ContinuousConstSMul Gᵐᵒᵖ G] (ρ : Representation A G M)
    [ρ.IsSmooth] :
    (ofIsSmooth ρ).toRepresentation = ρ :=
  (rfl)

end Discrete

end TauCeti.ContinuousRep

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.RepresentationTheory.Continuous.Basic
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Continuous representations acting by scalars

A representation acts *by scalars* when every operator `π g` is the homothety `v ↦ c g • v`. This
file collects what that shape is worth: two representations with the same scalars are equivalent
along any equivalence of their carriers, and, over an algebraically closed field, every irreducible
finite-dimensional continuous representation of a commutative group is of this shape, its scalars
forming a linear character `G →* 𝕜ˣ`.

The second half is the continuous form of Mathlib's
`Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative`, which says that such a
representation is one-dimensional: on a line every operator is a homothety, and the scalars multiply
because the operators compose. What is added on top of Mathlib is the passage from the dimension
count to the character, and the continuity of that character, which the purely algebraic statement
cannot see.

Together the two halves classify: an irreducible finite-dimensional continuous representation of a
commutative group is equivalent to any representation carried by `𝕜` with the same linear
character, so the linear characters of `G` list the irreducibles. That is how
`TauCeti/RepresentationTheory/Compact/Circle.lean` promotes its classification of the
representations *carried by* `ℂ` to all finite-dimensional irreducibles of the circle group.

## Main definitions

* `ContRepresentation.equivOfSmul`: two representations acting by the same scalars are equivalent
  along any continuous linear equivalence of their carriers.

## Main statements

* `ContRepresentation.exists_monoidHom_smul_eq`: **an irreducible continuous representation of a
  commutative monoid over an algebraically closed field acts by scalars**, and the scalars form a
  monoid homomorphism `G →* 𝕜`.
* `ContRepresentation.exists_linearCharacter_smul_eq`: for a commutative *group* the scalars are
  units, so they form a linear character `G →* 𝕜ˣ`.
* `ContRepresentation.continuous_of_smul_eq`: the scalars of a continuous representation on a line
  depend continuously on the group element.
* `ContRepresentation.exists_continuousLinearEquiv_of_isIrreducible`: the carrier of such an
  irreducible representation is continuously linearly isomorphic to `𝕜`, which is what
  `ContRepresentation.equivOfSmul` consumes.

## Implementation notes

Everything here is stated for a representation on a normed space, matching the rest of
`TauCeti/RepresentationTheory/Continuous/`. The finite-dimensional topology facts used
(`ContinuousLinearEquiv.ofFinrankEq`, `ContinuousLinearMap.apply`) are why the scalars form a
nontrivially normed field rather than a bare topological one, and why
`ContRepresentation.exists_continuousLinearEquiv_of_isIrreducible` asks for completeness; the
results that do not need completeness do not carry it.

The declarations live in the root `ContRepresentation` namespace, as in
`TauCeti/RepresentationTheory/Compact/Circle.lean`, so that dot notation on Mathlib's
`ContRepresentation` reaches them.
-/

public section

open Module

namespace ContRepresentation

section Smul

variable {𝕜 G V W : Type*} [NormedField 𝕜] [Monoid G]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedAddCommGroup W] [NormedSpace 𝕜 W]
  {π : ContRepresentation 𝕜 G V} {σ : ContRepresentation 𝕜 G W} {c : G → 𝕜}

/-- **Representations acting by the same scalars are equivalent along any equivalence of their
carriers.** A homothety commutes with every linear map, so the intertwining condition that would
otherwise constrain `e` is automatic here. -/
def equivOfSmul (hπ : ∀ g v, π g v = c g • v) (hσ : ∀ g w, σ g w = c g • w) (e : V ≃L[𝕜] W) :
    π.Equiv σ :=
  .mk e fun g => ContinuousLinearMap.ext fun v => by
    simp [hπ, hσ, map_smul]

@[simp]
theorem equivOfSmul_apply (hπ : ∀ g v, π g v = c g • v) (hσ : ∀ g w, σ g w = c g • w)
    (e : V ≃L[𝕜] W) (v : V) : equivOfSmul hπ hσ e v = e v := (rfl)

end Smul

section IsAlgClosed

variable {𝕜 G V : Type*} [NontriviallyNormedField 𝕜] [IsAlgClosed 𝕜]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [FiniteDimensional 𝕜 V]

section CommMonoid

variable [CommMonoid G]

/-- **An irreducible continuous representation of a commutative monoid over an algebraically closed
field acts by scalars.** The carrier is a line by
`Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative`, every operator on a line is a
homothety, and the scalar of a composite is the product of the scalars, so the scalars assemble
into a monoid homomorphism. -/
theorem exists_monoidHom_smul_eq (π : ContRepresentation 𝕜 G V)
    (hπ : π.toRepresentation.IsIrreducible) : ∃ c : G →* 𝕜, ∀ g v, π g v = c g • v := by
  -- Both `have`s are anonymous because they are consumed by instance search, not by name.
  have := hπ
  have : IsMulCommutative G := .of_comm mul_comm
  have h1 : finrank 𝕜 V = 1 :=
    Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative π.toRepresentation
  -- `c f` is the scalar of the endomorphism `f` of the line, and `huniq` pins it down.
  choose c hc huniq using fun f : V →ₗ[𝕜] V =>
    LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one h1 f
  have hcv : ∀ (g : G) (v : V), π g v = c (π g).toLinearMap • v := fun g v => by
    conv_lhs => rw [show π g v = (π g).toLinearMap v from rfl, hc (π g).toLinearMap]
    simp
  -- `π 1` is the identity, whose scalar is `1`; `π (g * h)` is the composite of `π g` and `π h`,
  -- whose scalar is therefore the product of theirs.
  refine ⟨{ toFun g := c (π g).toLinearMap
            map_one' := (huniq _ 1 (by ext v; simp)).symm
            map_mul' g h := (huniq _ _ (LinearMap.ext fun v => ?_)).symm }, hcv⟩
  have hgh : π (g * h) v = π g (π h v) := by rw [map_mul]; rfl
  simpa [hgh, mul_smul] using (hcv g (π h v)).trans (congrArg _ (hcv h v))

end CommMonoid

section CommGroup

variable [CommGroup G]

/-- **An irreducible continuous representation of a commutative group over an algebraically closed
field acts by a linear character.** Over a group the scalars are invertible, so
`ContRepresentation.exists_monoidHom_smul_eq` upgrades to a homomorphism into the units. -/
theorem exists_linearCharacter_smul_eq (π : ContRepresentation 𝕜 G V)
    (hπ : π.toRepresentation.IsIrreducible) :
    ∃ χ : G →* 𝕜ˣ, ∀ g v, π g v = (χ g : 𝕜) • v := by
  obtain ⟨c, hc⟩ := exists_monoidHom_smul_eq π hπ
  exact ⟨c.toHomUnits, fun g v => by rw [MonoidHom.coe_toHomUnits]; exact hc g v⟩

end CommGroup

/-- **An irreducible continuous representation of a commutative monoid over an algebraically closed
field is one-dimensional**, hence continuously linearly isomorphic to the scalars: the dimension
count of `Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative` followed by the
finite-dimensional comparison of topological vector spaces. This produces the equivalence that
`ContRepresentation.equivOfSmul` consumes. -/
theorem exists_continuousLinearEquiv_of_isIrreducible [CommMonoid G] [CompleteSpace 𝕜]
    (π : ContRepresentation 𝕜 G V) (hπ : π.toRepresentation.IsIrreducible) :
    Nonempty (V ≃L[𝕜] 𝕜) := by
  have := hπ
  have : IsMulCommutative G := .of_comm mul_comm
  have h1 : finrank 𝕜 V = 1 :=
    Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative π.toRepresentation
  exact ⟨ContinuousLinearEquiv.ofFinrankEq (by simp [h1])⟩

end IsAlgClosed

section Line

variable {𝕜 G V : Type*} [NontriviallyNormedField 𝕜] [Monoid G] [TopologicalSpace G]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V]

/-- **The scalars of a continuous representation on a line are continuous.** Reading them off as
`c g = e (π g (e⁻¹ 1))` along a continuous linear isomorphism `e : V ≃L[𝕜] 𝕜` exhibits `c` as a
composite of continuous maps. -/
theorem continuous_of_smul_eq (π : ContRepresentation 𝕜 G V) (hπ : Continuous π) (e : V ≃L[𝕜] 𝕜)
    {c : G → 𝕜} (hc : ∀ g v, π g v = c g • v) : Continuous c := by
  have hcg : c = fun g => e (π g (e.symm 1)) := by
    funext g
    rw [hc, map_smul, e.apply_symm_apply, smul_eq_mul, mul_one]
  rw [hcg]
  exact e.continuous.comp ((ContinuousLinearMap.apply 𝕜 V (e.symm 1)).continuous.comp hπ)

end Line

end ContRepresentation

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import TauCeti.RepresentationTheory.Subrepresentation

/-!
# Representations in which a scalar is a product of commutators

Let `ρ` be a representation of a group `G` on a vector space `V` over a field `k`, and suppose
that some element `z` of the commutator subgroup of `G` acts by a scalar `ζ`. The determinant of
the action on a subrepresentation `σ` is a homomorphism from `G` to the abelian group `kˣ`, so it
is trivial on `z`; on the other hand `z` acts on `σ` by `ζ`, whose determinant is
`ζ ^ dim σ`. Hence `ζ ^ dim σ = 1` for every subrepresentation `σ`.

If moreover `ζ` is a primitive `n`-th root of unity with `n = dim V`, then every nonzero
subrepresentation has dimension divisible by `n`, hence equal to `n`, so `ρ` is irreducible.
This is the linear-algebra core of the fact that the twisted relation
`[A₁,B₁]⋯[A_g,B_g] = ζ • 1` in `SU(r)`, with `ζ` a primitive `r`-th root of unity, admits no
proper invariant subspaces: in the language of gauge theory, a projectively flat connection of
coprime rank and degree has no parallel subbundles (Wehrheim–Woodward, *Floer field theory for
coprime rank and degree*, proof of Theorem 3.3.3).

## Main results

* `Subrepresentation.pow_finrank_eq_one_of_mem_commutator`: if an element of the commutator
  subgroup acts by `ζ`, then `ζ ^ dim σ = 1` for every subrepresentation `σ`.
* `Representation.isIrreducible_of_mem_commutator`: if moreover `ζ` is a primitive
  `(dim V)`-th root of unity and `V ≠ 0`, the representation is irreducible.
-/

public section

open Module

variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
  {ρ : Representation k G V}

namespace Subrepresentation

/-- **A scalar in the commutator subgroup is a root of unity of order dividing the dimension of
every subrepresentation.** If `z` lies in the commutator subgroup of `G` and acts by the scalar
`ζ`, then `ζ ^ dim σ = 1` for every subrepresentation `σ`: the determinant of the action on `σ`
is a homomorphism to the abelian group `kˣ`, so it is `1` on `z`, while `z` acts on `σ` by `ζ`. -/
theorem pow_finrank_eq_one_of_mem_commutator (σ : Subrepresentation ρ) {z : G}
    (hz : z ∈ commutator G) {ζ : k} (hzζ : ρ z = ζ • 1) :
    ζ ^ finrank k σ.toSubmodule = 1 := by
  have hdet := Group.Abelianization.commutator_le_ker
    (LinearMap.det.comp σ.toRepresentation).toHomUnits hz
  rw [MonoidHom.mem_ker, Units.ext_iff] at hdet
  have hσ : σ.toRepresentation z = ζ • 1 := by
    ext v
    simp [toRepresentation_apply, hzζ]
  simpa [hσ] using hdet

end Subrepresentation

namespace Representation

/-- **Irreducibility from a primitive root of unity in the commutator subgroup.** Let `V` be a
nonzero finite-dimensional representation of `G`, and suppose an element of the commutator
subgroup of `G` acts by a primitive `(dim V)`-th root of unity `ζ`. Then `V` is irreducible: by
`Subrepresentation.pow_finrank_eq_one_of_mem_commutator` every nonzero subrepresentation has
dimension divisible by `dim V`, so it is all of `V`. No hypothesis on the field is needed. -/
theorem isIrreducible_of_mem_commutator [FiniteDimensional k V] [Nontrivial V] {z : G}
    (hz : z ∈ commutator G) {ζ : k} (hζ : IsPrimitiveRoot ζ (finrank k V))
    (hzζ : ρ z = ζ • 1) : ρ.IsIrreducible where
  toNontrivial := inferInstance
  eq_bot_or_eq_top σ := by
    refine or_iff_not_imp_left.2 fun hσ ↦ Subrepresentation.toSubmodule_injective ?_
    have hpos : 0 < finrank k σ.toSubmodule := by
      refine Nat.pos_of_ne_zero fun h ↦ hσ (Subrepresentation.toSubmodule_injective ?_)
      rwa [Submodule.finrank_eq_zero] at h
    have hdvd := (hζ.pow_eq_one_iff_dvd _).1 (σ.pow_finrank_eq_one_of_mem_commutator hz hzζ)
    exact Submodule.eq_top_of_finrank_eq
      (le_antisymm (Submodule.finrank_le _) (Nat.le_of_dvd hpos hdvd))

end Representation

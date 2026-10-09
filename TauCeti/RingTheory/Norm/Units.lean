/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Norm.Defs
public import Mathlib.RingTheory.Norm.Transitivity
public import Mathlib.Algebra.Group.Subgroup.Defs

/-!
# The norm on unit groups

The norm `Algebra.norm R : S →* R` of an `R`-algebra is multiplicative, so it sends units to
units. `TauCeti.Algebra.normUnits` packages that as a homomorphism `Sˣ →* Rˣ`. This is the form a
statement about the norm of an invertible element wants: the value is a unit by construction, so
no choice of proof that it is nonzero has to be carried alongside it.

No finiteness hypothesis is needed here, because `Algebra.norm` itself has none: it is the
determinant of multiplication, which is `1` when `S` is not module-finite over `R`
(`Algebra.norm_eq_one_of_not_module_finite`). A consumer that cares about the value — for instance
the non-split torus of `GL₂` in
`TauCeti/LinearAlgebra/Matrix/GeneralLinearGroup/NonSplitTorus.lean` — supplies its own
finiteness where the value is computed.

## Main definitions

* `TauCeti.Algebra.normUnits`: the algebra norm read as a homomorphism `Sˣ →* Rˣ`.
* `TauCeti.normGroup`: the image of the norm on units in a finite field extension.

## Main results

* `AlgHom.normGroup_le_normGroup`: a larger extension has a smaller norm group.
* `TauCeti.pow_finrank_mem_normGroup`: the `[L : K]`-th power of an element of `Kˣ` is a norm.
-/

public section

namespace TauCeti

variable (R : Type*) [CommRing R] {S : Type*} [Ring S] [Algebra R S]

/-- **The norm as a homomorphism of unit groups.** The norm of a unit is a unit, because the norm
is multiplicative; this is `Algebra.norm R` read as a map `Sˣ →* Rˣ`. -/
noncomputable def Algebra.normUnits : Sˣ →* Rˣ :=
  Units.map (Algebra.norm R : S →* R)

/-- The value underlying `TauCeti.Algebra.normUnits` is the ordinary norm. -/
@[simp]
theorem Algebra.coe_normUnits (x : Sˣ) : (Algebra.normUnits R x : R) = Algebra.norm R (x : S) := by
  simp [Algebra.normUnits]

section NormGroup

variable (K L : Type*) [Field K] [Field L] [Algebra K L]

/-- The norm group `N_{L/K}(Lˣ)` of a finite field extension `L/K`: the image in `Kˣ` of the field
norm on units, `Algebra.normUnits K : Lˣ →* Kˣ`. Finiteness is required because `Algebra.norm K`
is identically `1` on an infinite extension. -/
noncomputable def normGroup [_hfin : Module.Finite K L] : Subgroup Kˣ :=
  (Algebra.normUnits K : Lˣ →* Kˣ).range

variable {K L} in
/-- An element of `Kˣ` lies in the norm group exactly when it is the norm of a unit of `L`. -/
@[simp]
theorem mem_normGroup_iff [Module.Finite K L] {x : Kˣ} :
    x ∈ normGroup K L ↔ ∃ y : Lˣ, Algebra.norm K (y : L) = x := by
  simp [normGroup, Units.ext_iff]

variable {K L} in
/-- **A larger extension has a smaller norm group.** A `K`-algebra map `f : M →ₐ[K] L` of finite
extensions makes `L` an extension of `M`, and by transitivity of the norm every norm from `L` is
a norm from `M`. -/
theorem _root_.AlgHom.normGroup_le_normGroup {M : Type*} [Field M] [Algebra K M] [Module.Finite K L]
    [Module.Finite K M] (f : M →ₐ[K] L) : normGroup K L ≤ normGroup K M := by
  let _ : Algebra M L := f.toRingHom.toAlgebra
  have : IsScalarTower K M L := .of_algebraMap_eq fun x ↦ (f.commutes x).symm
  have : Module.Finite M L := .of_restrictScalars_finite K M L
  rintro _ ⟨y, rfl⟩
  exact ⟨Algebra.normUnits M y, Units.ext (by simp [Algebra.norm_norm])⟩

variable {K} in
/-- **Powers to the degree are norms.** The norm of `a ∈ K` from `L` is `a ^ [L : K]`, so
`a ^ [L : K]` lies in the norm group `N_{L/K}(Lˣ)`. -/
theorem pow_finrank_mem_normGroup [Module.Finite K L] (a : Kˣ) :
    a ^ Module.finrank K L ∈ normGroup K L :=
  mem_normGroup_iff.2 ⟨Units.map (algebraMap K L).toMonoidHom a, by simp [Algebra.norm_algebraMap]⟩

end NormGroup

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Invariants
public import TauCeti.RepresentationTheory.SymmetricAlgebra.Basic

/-!
# The Reynolds operator on a symmetric algebra

Let a finite group `G` act linearly on a module `M` over a commutative ring `R` in which `#G` is
invertible. Averaging the induced action on the symmetric algebra,
`p ↦ #G⁻¹ • ∑ g, g • p`, is the *Reynolds operator* `Sym M → Sym(M)^G`. It is a retraction of
the inclusion of the invariant subalgebra, it preserves homogeneous degrees, and it is linear
over the invariant subalgebra: it sends `a * p` to `a` times the image of `p` for every
invariant `a`. It is generally not
multiplicative; the inclusion of the invariants, not the Reynolds operator, is the algebra map.

The Reynolds operator is the averaging projection `Representation.averageMap` of the induced
representation `Representation.symmetricAlgebra`; this file records the additional structure that
the multiplication and the grading of `Sym M` give it. It is the basic tool of the nonmodular
invariant theory of finite groups (Hilbert's finite generation argument, Molien's formula); its
definition requires `#G` to be invertible in `R`.

## Main definitions

* `Representation.symmetricAlgebraReynolds`: the Reynolds operator, as a linear map over the
  invariant subalgebra from `Sym M` onto the invariant subalgebra.

## Main results

* `Representation.coe_symmetricAlgebraReynolds_eq_sum`: it is the normalized group sum.
* `Representation.symmetricAlgebraReynolds_coe`: it restricts to the identity on invariants.
* `Representation.symmetricAlgebraReynolds_coe_mul`: it is linear over the invariants.
* `Representation.coe_symmetricAlgebraReynolds_mem_homogeneousSubmodule`: it preserves
  homogeneous degrees.
* `Representation.symmetricAlgebraReynolds_map`: it is constant on orbits.
* `Representation.coe_averageMap_symmetricAlgebraHomogeneous`: on each homogeneous component it is
  the averaging projection of the representation on that component.

## References

* L. Smith, *Polynomial Invariants of Finite Groups*, A K Peters (1995), Chapter 2.
* R. P. Stanley, *Invariants of finite groups and their applications to combinatorics*,
  Bull. Amer. Math. Soc. (N.S.) **1** (1979), 475–511.
-/

public section

open TauCeti.SymmetricAlgebra

namespace Representation

variable {R G M : Type*} [CommRing R] [Group G] [AddCommMonoid M] [Module R M]
variable (ρ : Representation R G M) [Fintype G] [Invertible (Fintype.card G : R)]

/-- The **Reynolds operator** `p ↦ #G⁻¹ • ∑ g, g • p`, from `Sym M` onto the invariant subalgebra.
It is linear over the invariant subalgebra and restricts to the identity on it, but it is
generally not multiplicative. -/
noncomputable def symmetricAlgebraReynolds :
    SymmetricAlgebra R M →ₗ[ρ.symmetricAlgebraInvariants] ρ.symmetricAlgebraInvariants where
  toFun p := ⟨ρ.symmetricAlgebra.averageMap p,
    (ρ.mem_symmetricAlgebraInvariants _).2 (ρ.symmetricAlgebra.averageMap_invariant p)⟩
  map_add' p q := Subtype.ext (map_add _ p q)
  map_smul' a p := Subtype.ext <| by
    -- Every `g` fixes the invariant factor `a`, so `a` passes through the group sum.
    have ha := (ρ.mem_symmetricAlgebraInvariants a).1 a.2
    simp only [symmetricAlgebra_apply] at ha
    simp only [averageMap_apply, symmetricAlgebra_apply, Subalgebra.smul_def,
      map_mul, ha, RingHom.id_apply, smul_eq_mul, Subalgebra.coe_mul, Finset.mul_sum,
      mul_smul_comm]

/-- The Reynolds operator is the averaging projection of the induced representation. -/
theorem coe_symmetricAlgebraReynolds (p : SymmetricAlgebra R M) :
    (ρ.symmetricAlgebraReynolds p : SymmetricAlgebra R M) = ρ.symmetricAlgebra.averageMap p :=
  (rfl)

/-- The Reynolds operator is the normalized sum `#G⁻¹ • ∑ g, g • p` over the group. -/
theorem coe_symmetricAlgebraReynolds_eq_sum (p : SymmetricAlgebra R M) :
    (ρ.symmetricAlgebraReynolds p : SymmetricAlgebra R M) =
      ⅟(Fintype.card G : R) • ∑ g : G, ρ.symmetricAlgebra g p :=
  ρ.symmetricAlgebra.averageMap_apply p

/-- The Reynolds operator restricts to the identity on the invariant subalgebra. -/
@[simp]
theorem symmetricAlgebraReynolds_coe (a : ρ.symmetricAlgebraInvariants) :
    ρ.symmetricAlgebraReynolds a = a :=
  Subtype.ext (ρ.symmetricAlgebra.averageMap_id a ((ρ.mem_symmetricAlgebraInvariants _).1 a.2))

/-- The Reynolds operator maps onto the invariant subalgebra. -/
theorem symmetricAlgebraReynolds_surjective :
    Function.Surjective ρ.symmetricAlgebraReynolds :=
  fun a ↦ ⟨a, ρ.symmetricAlgebraReynolds_coe a⟩

/-- The Reynolds operator is linear over the invariant subalgebra. -/
@[simp]
theorem symmetricAlgebraReynolds_coe_mul (a : ρ.symmetricAlgebraInvariants)
    (p : SymmetricAlgebra R M) :
    ρ.symmetricAlgebraReynolds (a * p) = a * ρ.symmetricAlgebraReynolds p :=
  ρ.symmetricAlgebraReynolds.map_smul a p

/-- The Reynolds operator preserves homogeneous degrees. -/
theorem coe_symmetricAlgebraReynolds_mem_homogeneousSubmodule {n : ℕ}
    {p : SymmetricAlgebra R M} (hp : p ∈ homogeneousSubmodule R M n) :
    (ρ.symmetricAlgebraReynolds p : SymmetricAlgebra R M) ∈ homogeneousSubmodule R M n := by
  rw [coe_symmetricAlgebraReynolds_eq_sum]
  exact Submodule.smul_mem _ _ <| Submodule.sum_mem _ fun g _ ↦
    ρ.symmetricAlgebra_mem_homogeneousSubmodule g hp

/-- The Reynolds operator is constant on the orbits of the induced action. -/
@[simp]
theorem symmetricAlgebraReynolds_map (g : G) (p : SymmetricAlgebra R M) :
    ρ.symmetricAlgebraReynolds (SymmetricAlgebra.map R (ρ g) p) = ρ.symmetricAlgebraReynolds p := by
  ext
  rw [coe_symmetricAlgebraReynolds, coe_symmetricAlgebraReynolds, ← symmetricAlgebra_apply,
    ← LinearMap.comp_apply, averageMap_comp_ρ]

/-- On the degree-`n` component, the Reynolds operator is the averaging projection of the
degree-`n` representation `Representation.symmetricAlgebraHomogeneous`. -/
theorem coe_averageMap_symmetricAlgebraHomogeneous (n : ℕ) (p : homogeneousSubmodule R M n) :
    ((ρ.symmetricAlgebraHomogeneous n).averageMap p : SymmetricAlgebra R M) =
      ρ.symmetricAlgebraReynolds p := by
  simp only [averageMap_apply, coe_symmetricAlgebraReynolds_eq_sum, Submodule.coe_smul,
    Submodule.coe_sum, coe_symmetricAlgebraHomogeneous_apply]

end Representation

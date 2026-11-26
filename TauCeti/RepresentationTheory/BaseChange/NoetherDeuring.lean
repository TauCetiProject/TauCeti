/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.BaseChange.Intertwiner
public import TauCeti.RepresentationTheory.Semisimple

/-!
# Descent of isomorphisms of semisimple representations

Over a field `K`, the dimension of every intertwiner space whose source is finite-dimensional is
unchanged by any nonzero commutative `K`-algebra `L`
(`Representation.finrank_intertwiningMap_baseChange`). Since
semisimple representations are determined by such dimensions
(`Representation.nonempty_equiv_of_finrank_intertwiningMap_eq`), two finite-dimensional
semisimple representations over `K` that become equivalent over `L` are already equivalent over
`K` (`Representation.nonempty_equiv_of_nonempty_equiv_baseChange`). This is the
Noether–Deuring theorem for semisimple representations; for instance `V ≅ W` over `K` if and
only if `AlgebraicClosure K ⊗ V ≅ AlgebraicClosure K ⊗ W`. The version for continuous
representations is `TauCeti.ContinuousRep.nonempty_iso_of_nonempty_equiv_baseChange`, in
`TauCeti.RepresentationTheory.Continuous.NoetherDeuring`.

## Main results

* `Representation.nonempty_equiv_of_nonempty_equiv_baseChange`: **Noether–Deuring for semisimple
  representations.** Semisimple representations that are equivalent after scalar extension are
  equivalent.
* `Representation.nonempty_equiv_baseChange_iff`: the same as an equivalence of statements.

## References

* C. W. Curtis and I. Reiner, *Representation theory of finite groups and associative algebras*,
  Theorem 29.7 (Noether–Deuring).
* H. Darmon, F. Diamond and R. Taylor, *Fermat's Last Theorem*, proof of Proposition 2.6.
-/

public section

namespace Representation

section Field

variable {K L G V W : Type*} [Field K] [CommRing L] [Nontrivial L] [Algebra K L] [Monoid G]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V] [AddCommGroup W] [Module K W]

omit [FiniteDimensional K V] in
/-- An equivalence after scalar extension preserves the dimensions of intertwiner spaces from any
finite-dimensional representation. -/
private theorem finrank_intertwiningMap_eq_of_equiv_baseChange {U : Type*} [AddCommGroup U]
    [Module K U] [FiniteDimensional K U] (τ : Representation K G U) {ρ : Representation K G V}
    {σ : Representation K G W} (e : (baseChange L ρ).Equiv (baseChange L σ)) :
    Module.finrank K (IntertwiningMap τ ρ) = Module.finrank K (IntertwiningMap τ σ) := by
  rw [← finrank_intertwiningMap_baseChange (L := L),
    ← finrank_intertwiningMap_baseChange (L := L)]
  exact (Equiv.intertwiningMapCongr (Equiv.refl _) e).finrank_eq

variable [FiniteDimensional K W]

/-- **Noether–Deuring for semisimple representations.** Two finite-dimensional semisimple
representations of a monoid over a field `K` that become equivalent after extending scalars to a
nonzero commutative `K`-algebra `L` (for instance an algebraic closure of `K`) are already
equivalent over `K`. -/
theorem nonempty_equiv_of_nonempty_equiv_baseChange (ρ : Representation K G V)
    (σ : Representation K G W) [ρ.IsSemisimpleRepresentation] [σ.IsSemisimpleRepresentation]
    (h : Nonempty ((baseChange L ρ).Equiv (baseChange L σ))) : Nonempty (ρ.Equiv σ) :=
  have ⟨e⟩ := h
  nonempty_equiv_of_finrank_intertwiningMap_eq ρ σ
    (fun _ _ => finrank_intertwiningMap_eq_of_equiv_baseChange _ e)
    (fun _ _ => finrank_intertwiningMap_eq_of_equiv_baseChange _ e)

/-- Two finite-dimensional semisimple representations over a field `K` are equivalent if and only
if they are equivalent after extending scalars to a nonzero commutative `K`-algebra. -/
theorem nonempty_equiv_baseChange_iff (ρ : Representation K G V) (σ : Representation K G W)
    [ρ.IsSemisimpleRepresentation] [σ.IsSemisimpleRepresentation] :
    Nonempty ((baseChange L ρ).Equiv (baseChange L σ)) ↔ Nonempty (ρ.Equiv σ) :=
  ⟨nonempty_equiv_of_nonempty_equiv_baseChange ρ σ, fun ⟨e⟩ => ⟨e.baseChange L⟩⟩

end Field

end Representation

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Eigenspace.JointEigenvector.Kolchin
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UpperUnitriangular.Nilpotent
import Mathlib.RingTheory.Nilpotent.Lemmas
import TauCeti.LinearAlgebra.ExtensionBasis

/-!
# Solvability of faithful unipotent representations

Kolchin's common fixed-vector theorem constructs a complete invariant flag for a
finite-dimensional representation whose every operator is unipotent. Relative to a basis adapted
to this flag, every representing matrix is upper unitriangular. Consequently a group admitting a
faithful representation of this kind embeds in an upper-unitriangular matrix group and is
solvable.

The block-triangularity of the matrix of an endomorphism in a basis adapted to an invariant
submodule is `TauCeti.toMatrixAlgEquiv_extensionBasis_isUpperUnitriangular`, in
`TauCeti.LinearAlgebra.ExtensionBasis`.

## Main declarations

* `Representation.isNilpotent_quotient_sub_one`: unipotent operators stay unipotent on the
  quotient by an invariant submodule.
* `Representation.exists_basis_isUpperUnitriangular_of_isUnipotent`: simultaneous
  upper-unitriangularization of a unipotent monoid representation.
* `Representation.isSolvable_of_injective_of_isUnipotent`: a group with a faithful
  finite-dimensional unipotent representation is solvable.

## References

* A. Borel, *Linear Algebraic Groups*, Proposition 4.8.
* T. A. Springer, *Linear Algebraic Groups*, Section 2.4.

This supplies the Lie--Kolchin solvability step in Layer 5 of the ReductiveGroups roadmap.
-/

public section

open Module

namespace TauCeti

section Quotient

variable {R G V : Type*} [Ring R] [Monoid G] [AddCommGroup V] [Module R V]

/-- If `rho g - 1` is nilpotent, then so is the operator `rho.quotient p hp g - 1` induced on the
quotient of the representation `rho` by an invariant submodule `p`. -/
theorem _root_.Representation.isNilpotent_quotient_sub_one (rho : Representation R G V)
    (p : Submodule R V) (hp : ∀ g, p ≤ p.comap (rho g)) {g : G}
    (hg : IsNilpotent (rho g - 1)) : IsNilpotent (rho.quotient p hp g - 1) := by
  have hsub : p ≤ p.comap (rho g - 1) := fun x hx ↦ by
    rw [Submodule.mem_comap, LinearMap.sub_apply, Module.End.one_apply]
    exact p.sub_mem (Submodule.mem_comap.mp (hp g hx)) hx
  have heq : rho.quotient p hp g - 1 = p.mapQ p (rho g - 1) hsub := by
    ext x
    simp [Representation.quotient_apply, Submodule.mapQ_apply]
  rw [heq]
  exact Module.End.IsNilpotent.mapQ hsub hg

end Quotient

end TauCeti

namespace TauCeti.Representation

universe u v w

noncomputable section

variable {K : Type u} {G : Type w} {V : Type v}
variable [Field K] [AddCommGroup V] [Module K V]

section Monoid

variable [Monoid G]

/-- A finite-dimensional monoid representation by unipotent operators has a basis in which all
representing matrices are upper unitriangular. -/
theorem _root_.Representation.exists_basis_isUpperUnitriangular_of_isUnipotent
    [FiniteDimensional K V]
    (rho : Representation K G V) (hunipotent : ∀ g, IsNilpotent (rho g - 1)) :
    ∃ (n : ℕ) (b : Basis (Fin n) K V),
      ∀ g, (LinearMap.toMatrixAlgEquiv b (rho g)).IsUpperUnitriangular := by
  generalize hdim : finrank K V = d
  induction d using Nat.strong_induction_on generalizing V with
  | h d ih =>
      rcases subsingleton_or_nontrivial V with _ | _
      · exact ⟨0, finBasisOfFinrankEq K V finrank_zero_of_subsingleton, fun _ ↦
          (Matrix.isUpperUnitriangular_def _).mpr ⟨fun i ↦ i.elim0, fun i ↦ i.elim0⟩⟩
      obtain ⟨p, hpdim, hfixed⟩ :=
        rho.exists_fixed_submodule_finrank_eq_one_of_isUnipotent hunipotent
      have hp (g : G) : p ≤ p.comap (rho g) := fun x hx ↦
        Submodule.mem_comap.mpr ((hfixed g x hx).symm ▸ hx)
      have hqdim : finrank K (V ⧸ p) < d := by
        have := p.finrank_quotient_add_finrank
        omega
      obtain ⟨n, bq, hbq⟩ := ih (finrank K (V ⧸ p)) hqdim (rho.quotient p hp)
        (fun g ↦ rho.isNilpotent_quotient_sub_one p hp (hunipotent g)) rfl
      let bp : Basis (Fin 1) K p := finBasisOfFinrankEq K p hpdim
      refine ⟨1 + n, extensionBasis p bp bq, fun g ↦ ?_⟩
      -- The operator `rho g` fixes the line `p` pointwise, so its block there is the identity;
      -- its block on `V ⧸ p` is upper unitriangular by the induction hypothesis.
      refine toMatrixAlgEquiv_extensionBasis_isUpperUnitriangular p bp bq (hp g) ?_ ?_
      · have hone : (rho g).restrict (fun _ hx ↦ Submodule.mem_comap.mp (hp g hx)) = 1 := by
          ext x
          simp [hfixed g x x.2]
        rw [hone, map_one]
        exact Matrix.isUpperUnitriangular_one
      · simpa only [Representation.quotient_apply] using hbq g

end Monoid

variable [Group G]

/-- Embed a representation into an upper-unitriangular group using a basis in which all of its
operators are upper unitriangular. -/
private def _root_.Representation.toUpperUnitriangularGroup {n : ℕ}
    (rho : Representation K G V)
    (b : Basis (Fin n) K V)
    (h : ∀ g, (LinearMap.toMatrixAlgEquiv b (rho g)).IsUpperUnitriangular) :
    G →* TauCeti.upperUnitriangularGroup (Fin n) K := by
  let f : G →* Matrix.GeneralLinearGroup (Fin n) K :=
    (Units.map (LinearMap.toMatrixAlgEquiv b).toMonoidHom).comp rho.asGroupHom
  exact
    { toFun := fun g ↦ ⟨f g, by
        apply TauCeti.UpperUnitriangularGroup.mem_iff.mpr
        simp only [f, MonoidHom.comp_apply, Units.coe_map,
          Representation.asGroupHom_apply]
        rw [Matrix.isUpperUnitriangular_def]
        refine ⟨?_, h g |>.apply_diag⟩
        intro i j hji
        apply (h g).isUpperTriangular
        -- The inherited order on `Fin n` is definitionally the order on its values.
        change j.val < i.val at hji ⊢
        exact hji⟩
      map_one' := Subtype.ext (map_one f)
      map_mul' := fun g h ↦ Subtype.ext (map_mul f g h) }

/-- A group admitting a faithful finite-dimensional representation by unipotent operators is
solvable. -/
theorem _root_.Representation.isSolvable_of_injective_of_isUnipotent
    [FiniteDimensional K V]
    (rho : Representation K G V) (hinjective : Function.Injective rho.asGroupHom)
    (hunipotent : ∀ g, IsNilpotent (rho g - 1)) : Group.IsSolvable G := by
  obtain ⟨n, b, hb⟩ :=
    _root_.Representation.exists_basis_isUpperUnitriangular_of_isUnipotent rho hunipotent
  apply Group.isSolvable_of_isSolvable_injective
    (f := _root_.Representation.toUpperUnitriangularGroup rho b hb)
  intro g h hgh
  apply hinjective
  apply Units.ext
  apply (LinearMap.toMatrixAlgEquiv b).injective
  exact congrArg (fun x : TauCeti.upperUnitriangularGroup (Fin n) K ↦
    ((x : Matrix.GeneralLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K)) hgh

end

end TauCeti.Representation

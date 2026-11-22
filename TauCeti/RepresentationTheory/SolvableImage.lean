/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.GroupTheory.Solvable
import TauCeti.GroupTheory.Solvable
import TauCeti.LinearAlgebra.ExtensionBasis
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UpperTriangular.Solvable
import TauCeti.RepresentationTheory.Subrepresentation

/-!
# Representations with solvable image and rank-two irreducibility

The image of a representation `ρ : Representation k G V` is the subgroup `ρ.asGroupHom.range` of
the automorphism group of `V`. If all the operators `ρ g` are upper triangular in one basis, this
image embeds in the upper-triangular subgroup of `GL_n(k)`, so it is solvable.

On a two-dimensional vector space a proper nonzero subrepresentation is a line, and in a basis
starting with a vector of that line every `ρ g` is upper triangular. Hence a two-dimensional
representation whose image is not solvable is irreducible. The converse fails: an irreducible
dihedral representation has solvable image.

Nonsolvability of the image also passes to a normal subgroup `N` of `G` with solvable quotient:
the image of `N` is normal in the image of `G`, with quotient a quotient of `G ⧸ N`. So a
two-dimensional representation with nonsolvable image stays irreducible on such a subgroup, for
instance on the absolute Galois group of a solvable extension. This is how the hypothesis of
nonsolvable residual image is used in the modularity lifting theorems for two-dimensional
residual Galois representations, where it survives the solvable base changes of the proofs.

## Main results

* `Representation.isSolvable_range_asGroupHom_of_isUpperTriangular`: a representation that is
  upper triangular in some basis has solvable image.
* `Subrepresentation.isSolvable_range_asGroupHom_of_finrank_eq_two`: a two-dimensional
  representation with a proper nonzero subrepresentation has solvable image.
* `Representation.isIrreducible_of_not_isSolvable_range_asGroupHom`: a two-dimensional
  representation with nonsolvable image is irreducible.
* `Representation.not_isSolvable_range_asGroupHom_comp_subtype`: restriction to a normal subgroup
  with solvable quotient keeps the image nonsolvable.
* `Representation.isIrreducible_comp_subtype_of_not_isSolvable_range_asGroupHom`: a
  two-dimensional representation with nonsolvable image stays irreducible on a normal subgroup
  with solvable quotient.

## References

* L. Dieulefait, A. Pacetti, *Modularity of compatible systems of Galois representations*,
  proof of Theorem 1.5.
-/

public section

open Module

namespace Representation

variable {k G V : Type*} [Group G] [AddCommGroup V]

section CommRing

variable [CommRing k] [Module k V]

/-- A representation whose operators all have upper-triangular matrices in one basis has
solvable image: the image embeds in the upper-triangular subgroup of `GL_n(k)`. -/
theorem isSolvable_range_asGroupHom_of_isUpperTriangular (ρ : Representation k G V)
    {ι : Type*} [Fintype ι] [LinearOrder ι] (b : Basis ι k V)
    (h : ∀ g, (LinearMap.toMatrixAlgEquiv b (ρ g)).IsUpperTriangular) :
    Group.IsSolvable ρ.asGroupHom.range := by
  let e : (Module.End k V)ˣ ≃* GL ι k := Units.mapEquiv (LinearMap.toMatrixAlgEquiv b).toMulEquiv
  let φ : ρ.asGroupHom.range →* TauCeti.upperTriangularGroup ι k :=
    (e.toMonoidHom.comp ρ.asGroupHom.range.subtype).codRestrict
      (TauCeti.upperTriangularGroup ι k) <| by
        rintro ⟨_, g, rfl⟩
        simpa [e, asGroupHom_apply] using h g
  refine Group.isSolvable_of_isSolvable_injective (f := φ) fun x y hxy ↦ ?_
  exact Subtype.ext (e.injective (congrArg Subtype.val hxy))

end CommRing

section Field

variable [Field k] [Module k V]

/-- A two-dimensional representation with a proper nonzero subrepresentation has solvable image:
in a basis whose first vector spans the subrepresentation, every operator is upper triangular. -/
theorem _root_.Subrepresentation.isSolvable_range_asGroupHom_of_finrank_eq_two
    {ρ : Representation k G V} (W : Subrepresentation ρ) (hV : finrank k V = 2) (hW₀ : W ≠ ⊥)
    (hW₁ : W ≠ ⊤) :
    Group.IsSolvable ρ.asGroupHom.range := by
  have : FiniteDimensional k V := Module.finite_of_finrank_eq_succ hV
  have hpos : 0 < finrank k W.toSubmodule := Nat.pos_of_ne_zero fun h ↦
    hW₀ (Subrepresentation.toSubmodule_injective (Submodule.finrank_eq_zero.mp h))
  have hlt : finrank k W.toSubmodule < 2 := hV ▸ Submodule.finrank_lt
    fun h ↦ hW₁ (Subrepresentation.toSubmodule_injective h)
  have h₁ : finrank k W.toSubmodule = 1 := by omega
  have h₂ : finrank k (V ⧸ W.toSubmodule) = 1 := by
    have := W.toSubmodule.finrank_quotient_add_finrank
    omega
  have hsub (M : Matrix (Fin 1) (Fin 1) k) : M.IsUpperTriangular := fun i j hij ↦
    (hij.ne (Subsingleton.elim j i)).elim
  exact ρ.isSolvable_range_asGroupHom_of_isUpperTriangular
    (TauCeti.extensionBasis W.toSubmodule (finBasisOfFinrankEq k _ h₁)
      (finBasisOfFinrankEq k _ h₂)) fun g ↦
    TauCeti.toMatrixAlgEquiv_extensionBasis_isUpperTriangular _ _ _
      (fun _ hv ↦ W.apply_mem_toSubmodule g hv) (hsub _) (hsub _)

/-- A two-dimensional representation whose image is not solvable is irreducible. -/
theorem isIrreducible_of_not_isSolvable_range_asGroupHom {ρ : Representation k G V}
    (hV : finrank k V = 2) (h : ¬ Group.IsSolvable ρ.asGroupHom.range) : ρ.IsIrreducible := by
  have : Nontrivial V := Module.nontrivial_of_finrank_eq_succ hV
  refine { eq_bot_or_eq_top := fun W ↦ ?_ }
  by_contra! hW
  exact h (W.isSolvable_range_asGroupHom_of_finrank_eq_two hV hW.1 hW.2)

end Field

section Restriction

variable [CommSemiring k] [Module k V]

/-- Restricting a representation with nonsolvable image to a normal subgroup with solvable
quotient keeps the image nonsolvable. -/
theorem not_isSolvable_range_asGroupHom_comp_subtype {ρ : Representation k G V}
    (N : Subgroup G) [N.Normal] [Group.IsSolvable (G ⧸ N)]
    (h : ¬ Group.IsSolvable ρ.asGroupHom.range) :
    ¬ Group.IsSolvable (asGroupHom (ρ.comp N.subtype)).range := by
  intro hN
  have hcomp : (asGroupHom (ρ.comp N.subtype)) = ρ.asGroupHom.comp N.subtype := by
    ext g : 2
    simp [asGroupHom_apply]
  rw [hcomp, MonoidHom.range_comp, Subgroup.range_subtype] at hN
  exact h (ρ.asGroupHom.isSolvable_range_of_isSolvable_map N)

end Restriction

/-- A two-dimensional representation with nonsolvable image stays irreducible on every normal
subgroup with solvable quotient. -/
theorem isIrreducible_comp_subtype_of_not_isSolvable_range_asGroupHom [Field k] [Module k V]
    {ρ : Representation k G V} (hV : finrank k V = 2) (N : Subgroup G) [N.Normal]
    [Group.IsSolvable (G ⧸ N)] (h : ¬ Group.IsSolvable ρ.asGroupHom.range) :
    IsIrreducible (ρ.comp N.subtype) :=
  isIrreducible_of_not_isSolvable_range_asGroupHom hV
    (not_isSolvable_range_asGroupHom_comp_subtype N h)

end Representation

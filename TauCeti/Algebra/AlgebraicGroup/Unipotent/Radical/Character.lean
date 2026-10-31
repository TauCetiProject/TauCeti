/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.CharacterKernel
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.Construction
import TauCeti.Algebra.AlgebraicGroup.Representation.UnipotentPoint.NoCharacters
import TauCeti.Algebra.AlgebraicGroup.Unipotent.Reduced
import TauCeti.RingTheory.Smooth.GeometricallyReduced

/-!
# Points and characters of the unipotent radical

Let `G` be an affine group of finite type over a field `k`. Its unipotent radical `R_u(G)` is a
smooth unipotent closed subgroup, so its rational points are unipotent and it has no nontrivial
characters. This file records both facts as statements about `G`:

* every rational point of `R_u(G)` is a unipotent point of `G`;
* the characters of `G` are trivial on `R_u(G)`, scheme-theoretically: the common kernel of the
  characters of `G` contains `R_u(G)`.

For a connected solvable `G` over an algebraically closed field both inclusions are equalities;
see `TauCeti.FiniteTypeCommHopfAlgCat.mem_quotientPointsSubgroup_unipotentRadical_iff` and
`TauCeti.FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal_eq_characterKernelIdeal`.

## Main declarations

* `FiniteTypeCommHopfAlgCat.isUnipotentPoint_of_mem_quotientPointsSubgroup_unipotentRadical`:
  rational points of `R_u(G)` are unipotent.
* `FiniteTypeCommHopfAlgCat.characterKernelIdeal_le_unipotentRadicalDefiningIdeal`: the
  characters of `G` are trivial on `R_u(G)`.
-/

public section

open CategoryTheory WithConv

namespace TauCeti.FiniteTypeCommHopfAlgCat

universe u

variable {k : Type u} [Field k]
variable (G : FiniteTypeCommHopfAlgCat.{u, u} k)

/-- Every rational point of the unipotent radical `R_u(G)` is unipotent. -/
theorem isUnipotentPoint_of_mem_quotientPointsSubgroup_unipotentRadical
    {g : WithConv (G →ₐ[k] k)}
    (hg : g ∈ CommHopfAlgCat.quotientPointsSubgroup G.obj (unipotentRadicalDefiningIdeal G)
      (CommAlgCat.of k k)) :
    HopfAlgebra.IsUnipotentPoint g := by
  obtain ⟨q, rfl⟩ := hg
  exact ((isUnipotentRadicalCandidate_unipotentRadicalDefiningIdeal G).smoothUnipotent
    |>.isUnipotentPoint q).mapDomain
    (CommHopfAlgCat.mkQuotient G.obj (unipotentRadicalDefiningIdeal G)).hom

/-- The characters of `G` are trivial on its unipotent radical, scheme-theoretically. -/
theorem characterKernelIdeal_le_unipotentRadicalDefiningIdeal :
    _root_.CommHopfAlgCat.characterKernelIdeal G.obj ≤ unipotentRadicalDefiningIdeal G := by
  -- The smooth unipotent group `R_u(G)` has no nontrivial characters.
  let J := unipotentRadicalDefiningIdeal G
  have hJ := (smoothUnipotentCommHopfAlgProperty_iff k _).mp
    (isUnipotentRadicalCandidate_unipotentRadicalDefiningIdeal G).smoothUnipotent
  let _ : Algebra.Smooth k (FiniteTypeCommHopfAlgCat.quotient G J) := hJ.1
  let _ : IsReduced (CommHopfAlgCat.quotient G.obj J) := isReduced_of_smooth k _
  let φ := (CommHopfAlgCat.mkQuotient G.obj J).hom.toAlgHom
  have hφ : ∀ x : GroupLike k G, φ x = 1 := fun x ↦
    congrArg GroupLike.val (groupLike_eq_one_of_forall_isUnipotentPoint hJ.2
      ⟨φ x, x.isGroupLikeElem_val.map (CommHopfAlgCat.mkQuotient G.obj J).hom⟩)
  rw [← HopfIdeal.toIdeal_le_toIdeal, ← CommHopfAlgCat.mkQuotient_ker G.obj J]
  exact (_root_.CommHopfAlgCat.characterKernelIdeal_toIdeal_le_ker_iff G.obj φ).mpr hφ

end TauCeti.FiniteTypeCommHopfAlgCat

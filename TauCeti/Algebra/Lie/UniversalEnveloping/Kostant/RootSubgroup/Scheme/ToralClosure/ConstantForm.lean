/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.ConstantForm.Basic
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.Basic

/-!
# The toral Kostant carrier inside a constant-form subgroup scheme

Fix an integral form matrix `C`. If every represented root subgroup and the represented weight
torus preserve `C` by congruence, their coordinate maps kill the constant-form defining ideal.
The largest Hopf ideal killed by those maps is the toral carrier's defining ideal, so it contains
the form ideal. Equivalently, the carrier is a closed subgroup scheme of the form-preserving
subgroup scheme.

## Main result

* `TauCeti.UniversalEnvelopingAlgebra.constantFormDefiningHopfIdeal_le_kostantToralDefiningIdeal`:
  containment of defining Hopf ideals from the generic matrices of the generating coordinate maps.

Only this containment is proved; no equality of subgroup schemes is asserted.
-/

public section

open CategoryTheory Matrix

namespace TauCeti.UniversalEnvelopingAlgebra

universe u w

-- Match tensor products to the `ℤ`-algebra structure used by scalar extension.
attribute [local instance high] Algebra.toModule

variable {L : Type u} [LieRing L] [LieAlgebra ℚ L]
variable {I : Type w} {κ : Type} [Finite κ]
variable {V : Type} [AddCommGroup V] [Module ℚ V]

variable (e : I → L) (h : κ → L)
variable (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V)
variable (M : AddSubgroup V)
variable (hM : ∀ u ∈ kostantForm e h, ∀ m ∈ M, ρ u m ∈ M)
variable (hnil : ∀ i, IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
variable {n : ℕ} (b : Module.Basis (Fin n) ℤ M)
variable (wt : Fin n → κ → ℤ)

/-- **The generators of the toral Kostant carrier cut out a form they preserve.** If the generic
matrix of every represented root-subgroup coordinate map and of the represented weight-torus
coordinate map preserves the constant form `C` by congruence, then the Hopf ideal cutting out the
subgroup scheme preserving `C` is contained in the toral defining ideal. Equivalently, the toral
carrier is a closed subgroup scheme of the group scheme preserving the form. -/
theorem constantFormDefiningHopfIdeal_le_kostantToralDefiningIdeal
    (C : Matrix (Fin n) (Fin n) ℤ)
    (hroot : ∀ i, (GeneralLinear.genericMatrix ℤ n).map
          (kostantRootSubgroupCoordinateMap e h ρ M hM i (hnil i) b).hom.toAlgHom *
        C.map (algebraMap ℤ (AdditiveGroup.coordinateHopfAlgebra ℤ)) *
        ((GeneralLinear.genericMatrix ℤ n).map
          (kostantRootSubgroupCoordinateMap e h ρ M hM i (hnil i) b).hom.toAlgHom)ᵀ =
        C.map (algebraMap ℤ (AdditiveGroup.coordinateHopfAlgebra ℤ)))
    (htorus : (GeneralLinear.genericMatrix ℤ n).map
          (GeneralLinear.weightTorusCoordinateMap (R := ℤ) wt).hom.toAlgHom *
        C.map (algebraMap ℤ
          (DiagonalizableGroup.coordinateRing ℤ (SplitTorus.characterGroup κ)).obj) *
        ((GeneralLinear.genericMatrix ℤ n).map
          (GeneralLinear.weightTorusCoordinateMap (R := ℤ) wt).hom.toAlgHom)ᵀ =
        C.map (algebraMap ℤ
          (DiagonalizableGroup.coordinateRing ℤ (SplitTorus.characterGroup κ)).obj)) :
    ConstantForm.definingHopfIdeal ℤ n C ≤ kostantToralDefiningIdeal e h ρ M hM hnil b wt := by
  rw [le_kostantToralDefiningIdeal_iff]
  exact ⟨fun i ↦ (ConstantForm.definingHopfIdeal_toIdeal_le_ker_iff ℤ n C _).2 (hroot i),
    (ConstantForm.definingHopfIdeal_toIdeal_le_ker_iff ℤ n C _).2 htorus⟩

end TauCeti.UniversalEnvelopingAlgebra

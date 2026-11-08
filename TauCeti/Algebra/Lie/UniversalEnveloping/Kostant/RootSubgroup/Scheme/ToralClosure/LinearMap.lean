/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Weight.LinearMap
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.Points

/-!
# Kostant toral closures along injective maps of character lattices

The Kostant toral closure of a finite free Kostant-stable lattice is the smallest closed subgroup
scheme of `GLₙ` containing the represented root subgroups and the represented weight torus of a
weight family `wt : Fin n → κ → ℤ`. Pushing the weights forward along an injective endomorphism `f`
of the character lattice `κ → ℤ` changes the parametrization of the torus, by the split-torus
morphism dual to `f`, but not the closed subgroup scheme it generates: the two weight-torus
coordinate maps have the same kernel
(`TauCeti.GeneralLinear.ker_weightTorusCoordinateMap_linearMap`). So the defining ideals, the group
schemes and their points agree, and the weight torus of `f ∘ wt` factors through the weight torus
of `wt`.

For Chevalley data this is the comparison between the torus whose character lattice is the lattice
`Λ` spanned by the weights and the parametrization of that torus by the full weight lattice `P ⊇ Λ`.
The second parametrization has kernel the diagonalizable group with character group `P / Λ`, but
it generates the same group scheme together with the root subgroups.

## Main results

* `TauCeti.UniversalEnvelopingAlgebra.kostantToralDefiningIdeal_linearMap`: the defining ideals
  agree.
* `TauCeti.UniversalEnvelopingAlgebra.kostantToralGroupScheme_linearMap` and
  `TauCeti.UniversalEnvelopingAlgebra.kostantToralPointsSubgroup_linearMap`: the group schemes and
  their points agree.
* `TauCeti.UniversalEnvelopingAlgebra.kostantWeightTorusToToral_linearMap`: the weight torus of
  `f ∘ wt` is the split-torus morphism dual to `f` followed by the weight torus of `wt`;
  `TauCeti.UniversalEnvelopingAlgebra.kostantWeightTorusToToral_linearMap_of_eq` allows any weight
  family equal to `f ∘ wt`.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3.
-/

public section

open AlgebraicGeometry CategoryTheory

namespace TauCeti.UniversalEnvelopingAlgebra

universe u w v

variable {L : Type u} [LieRing L] [LieAlgebra ℚ L]
variable {I : Type w} {κ : Type} [Finite κ]
variable {V : Type} [AddCommGroup V] [Module ℚ V]

variable (e : I → L) (h : κ → L)
variable (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V)
variable (M : AddSubgroup V)
variable (hM : ∀ u ∈ kostantForm e h, ∀ m ∈ M, ρ u m ∈ M)
variable (hnil : ∀ i, IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
variable {n : ℕ} (b : Module.Basis (Fin n) ℤ M)
variable (wt : Fin n → κ → ℤ) {f : (κ → ℤ) →ₗ[ℤ] (κ → ℤ)}

/-- **Pushing the weights forward along an injective map of character lattices does not change the
defining ideal of the Kostant toral closure.** -/
theorem kostantToralDefiningIdeal_linearMap (hf : Function.Injective f) :
    kostantToralDefiningIdeal e h ρ M hM hnil b (fun j => f (wt j)) =
      kostantToralDefiningIdeal e h ρ M hM hnil b wt := by
  have hker := GeneralLinear.ker_weightTorusCoordinateMap_linearMap (R := ℤ) hf wt
  apply le_antisymm <;> rw [le_kostantToralDefiningIdeal_iff]
  · refine ⟨kostantToralDefiningIdeal_toIdeal_le_root_ker e h ρ M hM hnil b _, ?_⟩
    rw [← hker]
    exact kostantToralDefiningIdeal_toIdeal_le_torus_ker e h ρ M hM hnil b _
  · refine ⟨kostantToralDefiningIdeal_toIdeal_le_root_ker e h ρ M hM hnil b wt, ?_⟩
    rw [hker]
    exact kostantToralDefiningIdeal_toIdeal_le_torus_ker e h ρ M hM hnil b wt

/-- **Pushing the weights forward along an injective map of character lattices does not change the
Kostant toral closure.** -/
theorem kostantToralGroupScheme_linearMap (hf : Function.Injective f) :
    kostantToralGroupScheme e h ρ M hM hnil b (fun j => f (wt j)) =
      kostantToralGroupScheme e h ρ M hM hnil b wt :=
  congrArg (CommHopfAlgCat.quotientSpec (GeneralLinear.coordinateHopfAlgebra ℤ n))
    (kostantToralDefiningIdeal_linearMap e h ρ M hM hnil b wt hf)

/-- **Pushing the weights forward along an injective map of character lattices does not change the
points of the Kostant toral closure.** -/
theorem kostantToralPointsSubgroup_linearMap (hf : Function.Injective f) (A : Type v)
    [CommRing A] :
    kostantToralPointsSubgroup e h ρ M hM hnil b (fun j => f (wt j)) A =
      kostantToralPointsSubgroup e h ρ M hM hnil b wt A := by
  rw [kostantToralPointsSubgroup_def, kostantToralPointsSubgroup_def,
    kostantToralDefiningIdeal_linearMap e h ρ M hM hnil b wt hf]

/-- The identification of the two toral closures is compatible with their inclusions into
`GLₙ`. -/
theorem eqToHom_comp_kostantToralGroupSchemeι_linearMap (hf : Function.Injective f) :
    eqToHom (kostantToralGroupScheme_linearMap e h ρ M hM hnil b wt hf) ≫
        kostantToralGroupSchemeι e h ρ M hM hnil b wt =
      kostantToralGroupSchemeι e h ρ M hM hnil b (fun j => f (wt j)) := by
  rw [kostantToralGroupSchemeι_def, kostantToralGroupSchemeι_def, ← Category.assoc,
    CommHopfAlgCat.eqToHom_comp_quotientSpecι _
      (kostantToralDefiningIdeal_linearMap e h ρ M hM hnil b wt hf)]

/-- **The weight torus of the pushed-forward weights factors through the weight torus of the
original weights**, by the split-torus morphism dual to `f`, after the identification of the two
toral closures. -/
theorem kostantWeightTorusToToral_linearMap (hf : Function.Injective f) :
    kostantWeightTorusToToral e h ρ M hM hnil b (fun j => f (wt j)) ≫
        eqToHom (kostantToralGroupScheme_linearMap e h ρ M hM hnil b wt hf) =
      SplitTorus.ofLinearMap ℤ f ≫ kostantWeightTorusToToral e h ρ M hM hnil b wt := by
  apply (cancel_mono (kostantToralGroupSchemeι e h ρ M hM hnil b wt)).1
  rw [Category.assoc, eqToHom_comp_kostantToralGroupSchemeι_linearMap e h ρ M hM hnil b wt hf,
    kostantWeightTorusToToral_comp_ι, Category.assoc, kostantWeightTorusToToral_comp_ι,
    GeneralLinear.weightTorus_linearMap]

/-- A variant of `kostantWeightTorusToToral_linearMap` for any weight family `wt'` equal to the
pushed-forward weights and any identification of the two toral closures. -/
theorem kostantWeightTorusToToral_linearMap_of_eq (hf : Function.Injective f)
    {wt' : Fin n → κ → ℤ} (hw : (fun j => f (wt j)) = wt')
    (hG : kostantToralGroupScheme e h ρ M hM hnil b wt' =
      kostantToralGroupScheme e h ρ M hM hnil b wt) :
    kostantWeightTorusToToral e h ρ M hM hnil b wt' ≫ eqToHom hG =
      SplitTorus.ofLinearMap ℤ f ≫ kostantWeightTorusToToral e h ρ M hM hnil b wt := by
  subst hw
  exact kostantWeightTorusToToral_linearMap e h ρ M hM hnil b wt hf

end TauCeti.UniversalEnvelopingAlgebra

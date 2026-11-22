/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.RationalSubset.Basis
public import TauCeti.CategoryTheory.Sites.TopologicalBasis
public import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology
public import Mathlib.Topology.Sheaves.SheafCondition.Sites

import TauCeti.CategoryTheory.Sites.IsSheafFor

/-!
# Sheaves on `Spa(A,A⁺)` are detected on rational covers

Rational subsets form a basis of `Spa(A,A⁺)` (`isTopologicalBasis_spaRationalFamily`), and a
presheaf on a space is a sheaf exactly when it is a sheaf for covers by basis elements
(`isSheaf_iff_isSheafFor_basisCoverage_comp`). Putting the two together, sheafhood on the adic
spectrum is decided by the rational covers alone.

The criterion is stated for an arbitrary presheaf, so it does not mention the structure presheaf;
applying it to `𝒪_X` is what turns the definition of sheafiness into Wedhorn's rational-cover
condition.

The rational opens also form a dense subsite of the opens of `Spa(A,A⁺)`, so a sheaf on the
rational opens for the restricted topology extends to a sheaf on `Spa(A,A⁺)` by right Kan
extension along their inclusion.

## Main definitions

* `TauCeti.ValuationSpectrum.rationalOpensFunctor` : the inclusion of the rational opens of
  `Spa(A,A⁺)` into all of its opens.

## Main results

* `TauCeti.ValuationSpectrum.isSheaf_iff_isSheafFor_rationalCover` : the criterion.
* `(TauCeti.ValuationSpectrum.rationalOpensFunctor Aplus).IsCoverDense` : the rational opens are
  cover-dense, for a Huber ring `A`.
* `TauCeti.ValuationSpectrum.isSheafFor_spaRationalOpens_of_finite` : quasi-compactness of
  rational opens reduces the set-level sheaf condition for arbitrary rational covers of rational
  opens to finite rational covers of rational opens.
* `TauCeti.ValuationSpectrum.isSheaf_restrictedTopology_rationalOpens_of_isSheafFor_ofArrows` :
  gluing along rational covers of rational opens gives the sheaf condition for the restricted
  topology on the rational basis.

The rational basis itself, in the `Opens` form this consumes, is
`TauCeti.ValuationSpectrum.isBasis_spaRationalOpens` in
`TauCeti.AlgebraicGeometry.AdicSpace.Spa.RationalSubset.Basis`.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), §7.3 for rational subsets and
  §8.1–§8.2 for the sheaf condition on them.
-/

namespace TauCeti.ValuationSpectrum

open CategoryTheory Opposite _root_.TopologicalSpace TauCeti.Huber TauCeti.TopologicalSpace.Opens

public section

universe v w u₁ u₂

variable {A : Type v} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- **Sheafhood on `Spa(A,A⁺)` is decided by rational covers.** A presheaf valued in any category
is a sheaf for the topology of the adic spectrum exactly when it satisfies the sheaf condition for
every cover of an open by rational subsets.

Nothing here is specific to the structure presheaf: the statement quantifies over presheaves, and
`𝒪_X` is one instance. -/
theorem isSheaf_iff_isSheafFor_rationalCover [IsHuberRing A] (Aplus : Subring A) {C : Type*}
    [Category C] (P : (Opens ↥(spa Aplus))ᵒᵖ ⥤ C) :
    Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa Aplus)) P ↔
      ∀ (E : C) ⦃U : Opens ↥(spa Aplus)⦄ (R : Presieve U),
        IsBasisCover (spaRationalOpens Aplus) R →
        Presieve.IsSheafFor (P ⋙ coyoneda.obj (Opposite.op E)) R :=
  isSheaf_iff_isSheafFor_basisCoverage_comp (isBasis_spaRationalOpens Aplus) P

variable (Aplus : Subring A)

/-- The inclusion of the rational opens of `Spa(A, A⁺)` into all of its opens, as a functor out of
the full subcategory they span. As an abbreviation for `inducedFunctor`, it is full and faithful
(`InducedCategory.full`, `InducedCategory.faithful`; bundled as `fullyFaithfulInducedFunctor _`). -/
abbrev rationalOpensFunctor : InducedCategory (Opens ↥(spa Aplus))
    (Subtype.val : spaRationalOpens Aplus → _) ⥤ Opens ↥(spa Aplus) :=
  inducedFunctor _

/-- The rational opens are cover-dense in `Spa(A, A⁺)`: every open is covered by the rational opens
it contains. Mathlib's instances then make `rationalOpensFunctor Aplus` cocontinuous
(`Functor.IsCocontinuous`) and a dense subsite (`Functor.IsDenseSubsite`) for the restricted
topology `Functor.restrictedTopology` on the rational opens. -/
instance [IsHuberRing A] : (rationalOpensFunctor Aplus).IsCoverDense
    (Opens.grothendieckTopology ↥(spa Aplus)) :=
  -- the rational opens form a basis of the topology of `Spa(A, A⁺)`
  coverDense_inducedFunctor_subtypeVal (isBasis_spaRationalOpens Aplus)

/-- Compactness of rational opens upgrades set-level gluing from finite rational covers of rational
opens to arbitrary rational covers of rational opens, for any presheaf of types on
`Spa(A, A⁺)`. -/
theorem isSheafFor_spaRationalOpens_of_finite [IsHuberRing A]
    {F : (Opens ↥(spa Aplus))ᵒᵖ ⥤ Type w}
    (hfin : ∀ {W : Opens ↥(spa Aplus)} {κ : Type u₁} [Finite κ] {V : κ → Opens ↥(spa Aplus)},
      W ∈ spaRationalOpens Aplus → (∀ k, V k ∈ spaRationalOpens Aplus) →
      ∀ hcov : ⨆ k, V k = W,
      (Presieve.ofArrows V fun k ↦ homOfLE ((le_iSup V k).trans_eq hcov)).IsSheafFor F)
    {W : Opens ↥(spa Aplus)} (hW : W ∈ spaRationalOpens Aplus) {ι : Type u₂}
    {U : ι → Opens ↥(spa Aplus)} (hU : ∀ i, U i ∈ spaRationalOpens Aplus)
    (hcov : ⨆ i, U i = W) :
    (Presieve.ofArrows U fun i ↦ homOfLE ((le_iSup U i).trans_eq hcov)).IsSheafFor F := by
  classical
  obtain ⟨I, hcovI⟩ := exists_finite_subcover_spaRationalOpens hW hcov
  let e := Equiv.ulift.{u₁}.trans (Finite.equivFin ↥I).symm
  let κ' := ULift.{u₁} (Fin (Nat.card ↥I))
  let U' : κ' → Opens ↥(spa Aplus) := fun k ↦ U (e k).val
  have hcovI' : (⨆ k : κ', U' k) = W := by
    rw [← hcovI]
    exact le_antisymm (iSup_le fun k ↦ le_iSup (fun k : ↥I ↦ U k.val) (e k))
      (iSup_le fun k ↦ le_iSup_of_le (e.symm k) (by simp [U']))
  have hcovUi (i : ι) : (⨆ k : κ', U i ⊓ U' k) = U i := by
    refine le_antisymm (iSup_le fun _ ↦ inf_le_left) fun x hx ↦ ?_
    obtain ⟨k, hxk⟩ := Opens.mem_iSup.mp (hcovI' ▸ ((le_iSup U i).trans_eq hcov) hx)
    exact Opens.mem_iSup.mpr ⟨k, hx, hxk⟩
  refine Presieve.isSheafFor_ofArrows_of_factorsThru _
    (fun i ↦ Presieve.ofArrows (fun k : κ' ↦ U i ⊓ U' k)
      fun k ↦ homOfLE ((le_iSup (fun k : κ' ↦ U i ⊓ U' k) k).trans_eq (hcovUi i)))
    (fun i ↦ (hfin (V := fun k : κ' ↦ U i ⊓ U' k) (hU i)
      (fun k ↦ inf_mem_spaRationalOpens (hU i) (hU (e k).val)) (hcovUi i)).isSeparatedFor)
    (S := Presieve.ofArrows U'
      fun k ↦ homOfLE ((le_iSup U' k).trans_eq hcovI'))
    (hfin (V := U') hW (fun k ↦ hU (e k).val) hcovI')
    (fun V g ⟨k⟩ ↦ ⟨U (e k).val, 𝟙 _, homOfLE ((le_iSup U (e k).val).trans_eq hcov),
      Presieve.ofArrows.mk (e k).val, Category.id_comp _⟩)
    (fun i Z g ⟨k⟩ ↦ ⟨U' k, homOfLE inf_le_right,
      homOfLE ((le_iSup U' k).trans_eq hcovI'), Presieve.ofArrows.mk k,
      Subsingleton.elim _ _⟩)

/-- **The sheaf condition on the rational basis.** For any presheaf of types `F` on `Spa(A, A⁺)`,
if `F` satisfies the sheaf condition for every cover of a rational open by rational opens, then its
restriction to the rational opens is a sheaf for the topology restricted from `Spa(A, A⁺)`.
Intersections of rational opens are rational, which is what lets compatibility on the basis stand
in for compatibility on pairwise intersections. -/
theorem isSheaf_restrictedTopology_rationalOpens_of_isSheafFor_ofArrows [IsHuberRing A]
    (F : (Opens ↥(spa Aplus))ᵒᵖ ⥤ Type w)
    (hrat : ∀ {W : Opens ↥(spa Aplus)} {ι : Type v} {U : ι → Opens ↥(spa Aplus)},
      W ∈ spaRationalOpens Aplus → (∀ i, U i ∈ spaRationalOpens Aplus) → ∀ hcov : ⨆ i, U i = W,
      (Presieve.ofArrows U fun i ↦ homOfLE ((le_iSup U i).trans_eq hcov)).IsSheafFor F) :
    Presieve.IsSheaf
      ((rationalOpensFunctor Aplus).restrictedTopology (Opens.grothendieckTopology ↥(spa Aplus)))
      ((rationalOpensFunctor Aplus).op ⋙ F) := by
  intro W S hS
  obtain ⟨ι, U, π, rfl⟩ := S.exists_eq_ofArrows
  rw [Functor.mem_restrictedTopology_iff, Sieve.functorPushforward_ofArrows] at hS
  have hcov : ⨆ i, (U i).val = W.val := by
    apply le_antisymm (iSup_le fun i ↦ (π i).hom.le)
    intro x hx
    obtain ⟨V, f, hf, hxV⟩ := hS x hx
    obtain ⟨V', g, f', hf', rfl⟩ := hf
    obtain ⟨i⟩ := hf'
    exact Opens.mem_iSup.mpr ⟨i, g.le hxV⟩
  have hrat := hrat W.property (fun i ↦ (U i).property) hcov
  have hπ (i : ι) : (rationalOpensFunctor Aplus).map (π i) =
      homOfLE ((le_iSup (fun i ↦ (U i).val) i).trans_eq hcov) := Subsingleton.elim _ _
  rw [← Presieve.isSheafFor_iff_generate, Presieve.isSheafFor_arrows_iff]
  rw [Presieve.isSheafFor_arrows_iff] at hrat
  intro x hx
  -- Intersections of rational opens are rational, so compatibility on the basis supplies the
  -- pairwise-intersection compatibility required in the ambient category of opens.
  have hcompat : Presieve.Arrows.Compatible F
      (fun i ↦ homOfLE ((le_iSup (fun i ↦ (U i).val) i).trans_eq hcov)) x := by
    apply (Presieve.Arrows.compatible_homOfLE_iff _ _).mpr
    intro i j
    let V : spaRationalOpens Aplus :=
      ⟨(U i).val ⊓ (U j).val, inf_mem_spaRationalOpens (U i).property (U j).property⟩
    exact hx i j V (InducedCategory.homMk (homOfLE inf_le_left))
      (InducedCategory.homMk (homOfLE inf_le_right))
      (InducedCategory.hom_ext (Subsingleton.elim _ _))
  obtain ⟨a, ha, hu⟩ := hrat x hcompat
  refine ⟨a, ?_, ?_⟩
  · intro i
    simpa only [Functor.comp_map, Functor.op_map, Quiver.Hom.unop_op, hπ] using ha i
  · intro b hb
    exact hu b fun i ↦ by
      simpa only [Functor.comp_map, Functor.op_map, Quiver.Hom.unop_op, hπ] using hb i

end

end TauCeti.ValuationSpectrum

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.GorensteinProjective.CompleteResolution
public import TauCeti.Algebra.Homology.TotallyAcyclic.Stable.Cycles

/-!
# The stable category of Gorenstein-projective modules as a homotopy category

The stable cycle functor from the homotopy category of totally acyclic complexes of finitely
generated projective modules to the stable category of finitely generated Gorenstein-projective
modules is an equivalence, in every degree. It is faithful because a map of totally acyclic
complexes inducing a stably zero map on cycles is null-homotopic, and full because every map of
cycles lifts to a map of complexes; both are the comparison theorem for complete resolutions in the
Frobenius category of Gorenstein-projective modules. Other degrees reduce to degree zero through
the shift of totally acyclic complexes (`TauCeti.TotallyAcyclicComplex.shiftCyclesIso`). The
inverse sends a module to a complete resolution of it.

No noetherian hypothesis is needed. The triangulated structure of this homotopy category and the
triangle equivalence are not treated here; for a general Frobenius exact category they are
`TauCeti.ExactStructure.IsFrobenius.stableToCompleteResolutionHomotopyCategory_isTriangulated`.

## Main definitions

* `TauCeti.TotallyAcyclicComplex.stableCyclesEquivalence`: the equivalence given by the stable
  cycles in degree zero.

## Main results

* `TauCeti.TotallyAcyclicComplex.ker_stableCycles_le_homotopyIdeal`: a map whose stable cycle map
  in some degree vanishes is null-homotopic.
* `TauCeti.TotallyAcyclicComplex.stableCyclesFunctor` is full, faithful and an equivalence in
  every degree.

## References

* Ragnar-Olaf Buchweitz, *Maximal Cohen–Macaulay Modules and Tate Cohomology*, Section 4.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe v u

namespace TauCeti

namespace TotallyAcyclicComplex

variable (A : Type u) [Ring A] [Small.{v} A]

/-- A map of totally acyclic complexes whose stable map on cycles in degree zero vanishes is
null-homotopic. -/
private theorem ker_stableCycles_zero_le_homotopyIdeal :
    (cyclesFunctor A 0 ⋙
      (GorensteinProjectiveModuleCat.exactStructure.{v} A).projectiveStableFunctor).kerIdeal ≤
      homotopyIdeal A := by
  intro P Q f hf
  have hE := GorensteinProjectiveModuleCat.exactStructure_isFrobenius (A := A)
  rw [Functor.mem_kerIdeal_hom, Functor.comp_map,
    ExactStructure.projectiveStableFunctor_map_eq_zero_iff,
    ← hE.projectiveInjective_eq_isProjective] at hf
  exact (mem_homotopyIdeal_iff A f).2
    ⟨CochainComplex.IsTotallyAcyclic.homotopyZero P.property Q.property f.hom hf⟩

/-- A map of totally acyclic complexes whose stable map on cycles in some degree vanishes is
null-homotopic: its shift has vanishing stable cycles in degree zero. -/
theorem ker_stableCycles_le_homotopyIdeal (n : ℤ) :
    (cyclesFunctor A n ⋙
      (GorensteinProjectiveModuleCat.exactStructure.{v} A).projectiveStableFunctor).kerIdeal ≤
      homotopyIdeal A := by
  intro P Q f hf
  let S := (GorensteinProjectiveModuleCat.exactStructure.{v} A).projectiveStableFunctor
  rw [← shift_map_mem_homotopyIdeal_iff A f n]
  apply ker_stableCycles_zero_le_homotopyIdeal
  rw [Functor.mem_kerIdeal_hom, Functor.comp_map] at hf ⊢
  rw [← cancel_mono (S.map ((shiftCyclesIso A n).hom.app Q)), ← S.map_comp,
    ← Functor.comp_map, (shiftCyclesIso A n).hom.naturality, S.map_comp, hf]
  simp

/-- Stable cycles in any degree are faithful on chain-homotopy classes. -/
instance (n : ℤ) : (stableCyclesFunctor.{v} A n).Faithful :=
  (MorphismIdeal.faithful_lift_iff _ _ _).2 (ker_stableCycles_le_homotopyIdeal A n)

/-- The cycles in degree zero of the lift of a map of cycles give back that map. -/
@[simp]
theorem cyclesFunctor_map_lift {P Q : TotallyAcyclicComplex.{v} A}
    (g : (cyclesFunctor A 0).obj P ⟶ (cyclesFunctor A 0).obj Q) :
    (cyclesFunctor A 0).map (ObjectProperty.homMk
      (CochainComplex.IsTotallyAcyclic.lift P.property Q.property g.hom)) = g := by
  ext : 1
  exact CochainComplex.IsTotallyAcyclic.cyclesMap_lift _ _ _

/-- Every stable map of cycles in degree `n` comes from a chain map: lift it on the shift by `n`,
where it becomes a map of cycles in degree zero, and shift back. -/
instance (n : ℤ) : (stableCyclesFunctor.{v} A n).Full where
  map_surjective {P Q} g := by
    obtain ⟨g₀, rfl⟩ :=
      (GorensteinProjectiveModuleCat.exactStructure.{v} A).projectiveStableFunctor.map_surjective g
    let e := shiftCyclesIso A n
    let sh := shiftFunctor (TotallyAcyclicComplex.{v} A) n
    let g₁ : (cyclesFunctor A 0).obj (sh.obj P.as) ⟶ (cyclesFunctor A 0).obj (sh.obj Q.as) :=
      e.hom.app P.as ≫ g₀ ≫ e.inv.app Q.as
    let ψ : sh.obj P.as ⟶ sh.obj Q.as := ObjectProperty.homMk
      (CochainComplex.IsTotallyAcyclic.lift (sh.obj P.as).property (sh.obj Q.as).property g₁.hom)
    refine ⟨(quotient A).map (sh.preimage ψ), ?_⟩
    rw [stableCyclesFunctor_map_quotient_map]
    congr 1
    rw [← cancel_epi (e.hom.app P.as), ← e.hom.naturality, Functor.comp_map, Functor.map_preimage,
      cyclesFunctor_map_lift]
    simp [g₁]

/-- Stable cycles in any degree are an equivalence; essential surjectivity is
`TauCeti.TotallyAcyclicComplex.cyclesFunctor_essSurj`. -/
instance (n : ℤ) : (stableCyclesFunctor.{v} A n).IsEquivalence where

/-- **The stable category of finitely generated Gorenstein-projective modules is equivalent to
the homotopy category of totally acyclic complexes of finitely generated projective modules**, by
cycles in degree zero. The inverse sends a module to a complete resolution of it, chosen through
`TauCeti.TotallyAcyclicComplex.cyclesFunctor_essSurj`. -/
abbrev stableCyclesEquivalence : HomotopyCategory.{v} A ≌
    (GorensteinProjectiveModuleCat.exactStructure.{v} A).ProjectiveStableCategory :=
  (stableCyclesFunctor.{v} A 0).asEquivalence

end TotallyAcyclicComplex

end TauCeti

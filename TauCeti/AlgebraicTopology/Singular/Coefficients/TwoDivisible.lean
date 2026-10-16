/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialSet.Homology.Coefficients
public import TauCeti.AlgebraicTopology.Singular.Basic
public import TauCeti.Algebra.Module.LocalizedModule.TwoDivisible
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Mod-two vanishing and integral homology

If the mod-two homology of a space vanishes in degrees n and n + 1, multiplication by two on
its integral homology in degree n is bijective. This is the algebraic step used with the Hurewicz
isomorphism to deduce unique two-divisibility of a first nonzero homotopy group.

The proof uses the coefficient sequence ℤ → ℤ → ℤ/2 and Mathlib's homology long exact
sequence, specifically `CategoryTheory.ShortComplex.ShortExact.homology_exact₁` and
`CategoryTheory.ShortComplex.ShortExact.homology_exact₂`. It requires no connectivity or
finite-generation assumptions. The coefficients are universe-lifted so that the space can live
in any universe.

## References

* A. Hatcher, *Algebraic Topology*, Section 3.A, change of coefficients.
* J.-P. Serre, *Groupes d'homotopie et classes de groupes abéliens*, Ann. of Math. 58 (1953).
-/

public noncomputable section

open CategoryTheory Limits HomologicalComplex

universe u

namespace TopCat

/-- Vanishing of mod-two singular homology in two adjacent degrees makes integral singular
homology in the lower degree uniquely two-divisible. -/
theorem isUniquelyTwoDivisible_singularHomology_of_isZero_mod_two (X : TopCat.{u}) (n : ℕ)
    (hn : IsZero (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj
      (ModuleCat.of ℤ (ULift.{u} (ZMod 2)))).obj X))
    (hn' : IsZero (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} ℤ) (n + 1)).obj
      (ModuleCat.of ℤ (ULift.{u} (ZMod 2)))).obj X)) :
    TauCeti.IsUniquelyTwoDivisible
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj
        (ModuleCat.of ℤ (ULift.{u} ℤ))).obj X) := by
  -- Mathlib's module AB4 instance fixes the ring and module universes to be equal.
  -- Here the ring ℤ is small while the modules and simplex sets can live in any universe.
  let : AB4OfSize.{u} (ModuleCat.{u} ℤ) := ⟨fun I ↦
    HasExactColimitsOfShape.domain_of_functor (Discrete I)
      (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u})⟩
  -- The coefficient sequence is exact before taking singular chains.
  let Z := ModuleCat.of ℤ (ULift.{u} ℤ)
  let q : Z ⟶ ModuleCat.of ℤ (ULift.{u} (ZMod 2)) := ModuleCat.ofHom
    ((AddEquiv.ulift.symm.toAddMonoidHom.comp (Int.castAddHom (ZMod 2))).comp
      AddEquiv.ulift.toAddMonoidHom).toIntLinearMap
  let S : ShortComplex (ModuleCat.{u} ℤ) := ShortComplex.mk ((2 : ℤ) • 𝟙 Z) q (by
    ext a
    simp [q, Z, AddEquiv.ulift, Equiv.ulift, show (2 : ZMod 2) = 0 by decide])
  have hS : S.ShortExact := by
    apply ModuleCat.shortComplex_shortExact
    · intro a
      constructor
      · intro ha
        have ha' : (a.down : ZMod 2) = 0 := congrArg ULift.down ha
        obtain ⟨b, hb⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd a.down 2).mp ha'
        exact ⟨ULift.up b, ULift.down_injective (by simpa [S, Z, mul_comm] using hb.symm)⟩
      · rintro ⟨b, rfl⟩
        apply ULift.down_injective
        simp [S, q, Z, AddEquiv.ulift, Equiv.ulift, show (2 : ZMod 2) = 0 by decide]
    · intro a b hab
      apply ULift.down_injective
      have hab' := congrArg ULift.down hab
      simpa [S, Z] using hab'
    · intro a
      obtain ⟨b, hb⟩ := ZMod.intCast_surjective a.down
      exact ⟨ULift.up b, ULift.down_injective hb⟩
  let T := S.map (AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} ℤ) ⋙
    (evaluation _ _).obj X)
  have hT : T.ShortExact := by
    convert hS.map_simplicialChains (TopCat.toSSet.obj X) using 1
    rfl
  -- Vanishing in the two adjacent degrees gives injectivity and surjectivity.
  have hmono : Mono (homologyMap T.f n) :=
    (hT.homology_exact₁ (n + 1) n (by simp)).mono_g (hn'.eq_of_src _ _)
  have hepi : Epi (homologyMap T.f n) :=
    (hT.homology_exact₂ n).epi_f (hn.eq_of_tgt _ _)
  -- Additivity identifies the induced coefficient map with multiplication by two.
  have hmap : homologyMap T.f n = (2 : ℤ) • 𝟙 (T.X₁.homology n) := by
    have hf : T.f = 𝟙 T.X₁ + 𝟙 T.X₁ := by simp [T, S, two_smul]
    rw [hf, homologyMap_add, homologyMap_id]
    exact (two_smul ℤ _).symm
  -- Transport the bundled module, including its group instance, to the chain-homology carrier.
  have hcarrier : (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj
      (ModuleCat.of ℤ (ULift.{u} ℤ))).obj X) = T.X₁.homology n := by rfl
  apply (congrArg (fun M : ModuleCat.{u} ℤ ↦ TauCeti.IsUniquelyTwoDivisible M) hcarrier).mpr
  rw [TauCeti.isUniquelyTwoDivisible_iff]
  simp only [two_zsmul]
  constructor
  · have h := (ModuleCat.mono_iff_injective (homologyMap T.f n)).mp hmono
    rw [hmap] at h
    simpa [two_mul, two_smul, Pi.add_def, Function.id_def] using h
  · have h := (ModuleCat.epi_iff_surjective (homologyMap T.f n)).mp hepi
    rw [hmap] at h
    simpa [two_mul, two_smul, Pi.add_def, Function.id_def] using h

end TopCat

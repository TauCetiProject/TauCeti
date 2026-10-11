/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.GorensteinProjective.Presentation
public import TauCeti.Algebra.Homology.TotallyAcyclic.Projective

/-!
# Projective kernels of extensions of Gorenstein-projective modules

Every short exact sequence with a finitely generated projective kernel and a
Gorenstein-projective quotient splits. This is the vanishing of degree-one extensions of a
Gorenstein-projective module by a finite projective module, and is the input for identifying
finite projectives as relative injectives in the Gorenstein-projective exact category.

No noetherian or self-injectivity hypothesis is required, and the ring and module universes are
independent. Taking the ring to be `Rᵐᵒᵖ` gives the result for right `R`-modules.

## References

* Ragnar-Olaf Buchweitz, *Maximal Cohen–Macaulay Modules and Tate Cohomology*, Section 4.
* Edgar E. Enochs and Overtoun M. G. Jenda, *Relative Homological Algebra*, Section 10.2.
-/

public section

open CategoryTheory Limits Preadditive

universe v u

namespace TauCeti

variable {A : Type u} [Ring A]

/-- A short exact sequence with finite projective kernel and Gorenstein-projective quotient
admits a splitting. The middle term need not be assumed Gorenstein-projective. -/
theorem IsGorensteinProjective.nonempty_splitting_of_projective
    {S : ShortComplex (ModuleCat.{v} A)} (hN : IsGorensteinProjective A S.X₃)
    (hS : S.ShortExact) [Module.Finite A S.X₁] [Module.Projective A S.X₁] :
    Nonempty S.Splitting := by
  obtain ⟨P, hP, ⟨e⟩⟩ := (isGorensteinProjective_iff S.X₃).mp hN
  let T := ShortComplex.mk (P.iCycles (-1)) (P.toCycles (-1) 0) (by
    rw [← cancel_mono (P.iCycles 0)]
    simp)
  have hT : T.ShortExact := by
    -- Transport the existing cycle presentation along its public carrier equations.
    let E : P.cyclesShortComplex (-1) ≅ T := ShortComplex.isoMk
      (eqToIso (by simp [T])) (eqToIso (by simp [T])) (eqToIso (by simp [T]))
      (by simp [T]) (by simp [T])
    exact ShortComplex.shortExact_of_iso E
      (HomologicalComplex.cyclesShortComplex_shortExact (-1) (hP.acyclic 0))
  have := hS.mono_f
  have := hS.epi_g
  have := hT.epi_g
  have := hP.projective (-1)
  let l := Projective.factorThru (T.g ≫ e.hom) S.g
  have hl : l ≫ S.g = T.g ≫ e.hom := Projective.factorThru_comp _ _
  have hz : T.f ≫ l ≫ S.g = 0 := by rw [hl, ← Category.assoc, T.zero, zero_comp]
  let k := hS.exact.lift (T.f ≫ l) hz
  obtain ⟨q, hq⟩ := hP.exists_extend_iCycles (-1) k.hom
  have hq' : T.f ≫ ModuleCat.ofHom q = k := ModuleCat.hom_ext hq
  -- Correct the lifted map by an extension of its restriction to the cycles.
  have hc : T.f ≫ (l - ModuleCat.ofHom q ≫ S.f) = 0 := by
    rw [comp_sub, ← Category.assoc, hq', hS.exact.lift_f, sub_self]
  let s := hT.exact.desc (l - ModuleCat.ofHom q ≫ S.f) hc
  have hs : s ≫ S.g = e.hom := by
    apply (cancel_epi T.g).mp
    rw [← Category.assoc, hT.exact.g_desc, sub_comp, hl, Category.assoc,
      S.zero, comp_zero, sub_zero]
  refine ⟨ShortComplex.Splitting.ofExactOfSection S hS.exact (e.inv ≫ s) ?_ hS.mono_f⟩
  rw [Category.assoc, hs, e.inv_hom_id]

end TauCeti

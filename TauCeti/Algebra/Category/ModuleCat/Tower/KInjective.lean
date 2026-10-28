/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Tower.Milnor
public import TauCeti.Algebra.Homology.HomotopyCategory.KInjective

/-!
# Limits of towers of complexes of modules as K-injective replacements

Let `C₀ ← C₁ ← C₂ ← ⋯` be a tower of cochain complexes of `R`-modules indexed by `ℤ`. If every
`Cₙ` is K-injective and every transition chain map `Cₙ₊₁ → Cₙ` is a split epimorphism in each
degree, then the limit complex `lim C` is K-injective
(`TauCeti.ComplexTower.isKInjective_limComplex`). The proof uses the sequence
`0 → lim C → ∏ₙ Cₙ → ∏ₙ Cₙ → 0` formed by the inclusion and the shift `δ(x)ₙ = xₙ - φₙ(xₙ₊₁)`
(`TauCeti.ComplexTower.shortComplex`). The product complex is K-injective as a product of
K-injective complexes, and when the transitions are split in each degree, so is the shift, so this
sequence is split short exact in every degree. The first term of such a sequence with K-injective
second and third terms is K-injective.

On the homology side, the matching statement that a cone whose legs are eventually isomorphisms on
homology in each degree induces a quasi-isomorphism into the limit complex is
`TauCeti.ComplexTower.quasiIso_isLimitLimComplexCone_lift`, next to the Milnor sequence.

Together these are the limit step of Spaltenstein's construction of K-injective replacements of
unbounded complexes of modules: a replacement of a complex `K` is the limit of a tower of
K-injective replacements of the truncations `τ^{≥ -n} K`, chosen with degreewise split surjective
transitions. In degree `j`, the truncation map `K → τ^{≥ -n} K` induces an isomorphism on
homology as soon as `-n ≤ j`.

## Main declarations

* `TauCeti.ComplexTower.isKInjective_productComplex`: the product complex of a tower of
  K-injective complexes is K-injective.
* `TauCeti.ComplexTower.isKInjective_limComplex`: the limit complex of a tower of K-injective
  complexes with degreewise split epimorphic transitions is K-injective.

## References

* N. Spaltenstein, *Resolutions of unbounded complexes*, Compositio Math. 65 (1988), 121–154.
* Stacks Project, *Derived Categories*, the section on K-injective complexes.
-/

public section

namespace TauCeti

namespace ComplexTower

open CategoryTheory Limits Opposite

universe v u

variable {R : Type u} [Ring R] (C : ComplexTower.{v} R (ComplexShape.up ℤ))

/-- The product complex of a tower of K-injective cochain complexes of modules is K-injective. -/
theorem isKInjective_productComplex [∀ n, CochainComplex.IsKInjective (C.obj (op n))] :
    CochainComplex.IsKInjective C.productComplex :=
  CochainComplex.isKInjective_of_isLimit_fan C.isLimitProductComplexFan

/-- **Limits of towers of K-injective complexes.** If every complex of a tower of cochain
complexes of modules is K-injective, and every transition chain map `Cₙ₊₁ → Cₙ` is a split
epimorphism in each degree, then the limit complex of the tower is K-injective. -/
theorem isKInjective_limComplex [∀ n, CochainComplex.IsKInjective (C.obj (op n))]
    (hC : ∀ (n : ℕ) (p : ℤ), IsSplitEpi ((C.map (homOfLE (Nat.le_succ n)).op).f p)) :
    CochainComplex.IsKInjective C.limComplex := by
  have : CochainComplex.IsKInjective C.shortComplex.X₂ := C.isKInjective_productComplex
  have : CochainComplex.IsKInjective C.shortComplex.X₃ := C.isKInjective_productComplex
  -- In each degree, the sequence `lim → ∏ → ∏` is exact with injective first map, and the shift
  -- has a section, so it splits.
  let S (p : ℤ) := C.shortComplex.map (HomologicalComplex.eval _ _ p)
  have hf (p : ℤ) : (S p).f = ModuleCat.ofHom (C.term p).lim.subtype :=
    ModuleCat.hom_ext (C.limComplexι_f_hom p)
  have hg (p : ℤ) : (S p).g = ModuleCat.ofHom (C.term p).shift :=
    ModuleCat.hom_ext (C.productComplexShift_f_hom p)
  have hexact (p : ℤ) : (S p).Exact := by
    rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact, hf, hg]
    exact ModuleTower.exact_lim_subtype_shift (C.term p)
  have hmono (p : ℤ) : Mono (S p).f :=
    (ModuleCat.mono_iff_injective _).2 (by rw [hf]; exact (C.term p).lim.injective_subtype)
  have hδ (p : ℤ) : IsSplitEpi (ModuleCat.ofHom (C.term p).shift) :=
    (C.term p).isSplitEpi_shift fun n ↦ hC n p
  exact CochainComplex.isKInjective_X₁_of_degreewiseSplit C.shortComplex fun p ↦
    ShortComplex.Splitting.ofExactOfSection (S p) (hexact p) (hδ p).exists_splitEpi.some.section_
      (by rw [hg]; exact (hδ p).exists_splitEpi.some.id) (hmono p)

end ComplexTower

end TauCeti

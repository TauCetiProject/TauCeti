/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Thom.Connectivity
public import TauCeti.Topology.VectorBundle.Thom.TwistedRankDegreeHomology

/-!
# The Thom class with coefficients in the orientation system

Let `E → B` be a real vector bundle of rank `r` over a compact base, with Thom pair `(E, E₀)`, `E₀`
the complement of the zero section, and let `R` be a commutative ring. An integral Thom class of
`E`, a class of `Hʳ(E, E₀; ℤ)` restricting to a generator on every fibre pair, exists only when `E`
is orientable. Twisting the coefficients by the orientation local system `o(E)` of `E`
(`TauCeti.VectorBundleOrientationCover.signLocalSystem`), pulled back to the total space
(`TauCeti.thomPairSignLocalSystem`), removes this restriction: every bundle has a **twisted Thom
class**

`U_E ∈ Hʳ(E, E₀; π^*o(E), R)`,

the relative cohomology with local coefficients, read by the Kronecker pairing against
`Hᵣ(E, E₀; π^*o(E))`, which takes the value `1` on every fibre class
(`TauCeti.twistedThomClass`, `TauCeti.twistedKronecker_twistedThomClass_thomPairSignFiberClass`).

The fibre class over `b` (`TauCeti.thomPairSignFiberClass`) is the class of the fibre pair
`(E_b, E_b ∖ {0})` read through a linear trivialization, tensored with the orientation of `E_b`
read by the same trivialization; it depends only on an orientation `ω` of the model fibre. The
construction uses two facts:

* the relative homology `Hₘ(E, E₀; π^*o(E))` vanishes below the rank, so by the universal
  coefficient theorem with local coefficients the Kronecker map identifies
  `Hʳ(E, E₀; π^*o(E), M)` with `Hom(Hᵣ(E, E₀; π^*o(E)), M)`
  (`TauCeti.thomPairTwistedCohomologyFinrankEquiv`);
* over a compact base, `Hᵣ(E, E₀; π^*o(E)) ≅ H₀(B; R)`, carrying the fibre class over `b` to the
  class of the point `b` (`TauCeti.thomPairTwistedHomologyFinrankIso`).

So `U_E` is the class whose Kronecker map is this isomorphism followed by the augmentation
`H₀(B; R) ⟶ R` (`TauCeti.twistedKronecker_twistedThomClass`). Since the fibre classes determine
morphisms out of `Hᵣ(E, E₀; π^*o(E))` (`TauCeti.thomPairTwistedHomology_hom_ext`), a class of
`Hʳ(E, E₀; π^*o(E), M)` is determined by its values on the fibre classes
(`TauCeti.twistedCohomology_thomPair_ext`), and `U_E` is the unique class taking the value `1` on
all of them (`TauCeti.eq_twistedThomClass_iff`). Reversing `ω` negates it
(`TauCeti.twistedThomClass_neg`).

The twisted Thom class is the input of the Thom isomorphism with orientation-twisted coefficients:
capping with it (`TopPair.twistedCap`) and pairing the two copies of `o(E)`
(`TauCeti.VectorBundleOrientationCover.signLocalSystemTensorIso`) sends `Hₙ₊ᵣ(E, E₀; R)` to the
homology `Hₙ(B; o(E))` of the base twisted by the orientation system, which is the relative homology
across the level of a Morse–Bott critical submanifold whose negative normal bundle is `E`.

## Main definitions and results

* `TauCeti.twistedThomClass`: the twisted Thom class `U_E`.
* `TauCeti.twistedKronecker_twistedThomClass`: its Kronecker map is
  `Hᵣ(E, E₀; π^*o(E)) ≅ H₀(B; R) ⟶ R`.
* `TauCeti.twistedKronecker_twistedThomClass_thomPairSignFiberClass`: it takes the value `1` on
  every fibre class.
* `TauCeti.twistedCohomology_thomPair_ext`: classes of `Hʳ(E, E₀; π^*o(E), M)` agreeing on the
  fibre classes are equal.
* `TauCeti.eq_twistedThomClass_iff`: `U_E` is the only class taking the value `1` on every fibre
  class.
* `TauCeti.twistedThomClass_neg`: reversing the model orientation negates `U_E`.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10 (Thom classes) and §12 (the orientation double cover and twisted
  coefficients).
* A. Hatcher, *Algebraic Topology*, Section 3.H (local coefficients and the orientation system)
  and Section 4.D (Thom classes).
-/

public section

noncomputable section

open CategoryTheory Bundle Module

universe w

namespace TauCeti

variable {B : Type w} [TopologicalSpace B] [CompactSpace B] {F : Type w}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {E : B → Type w}
  [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)] [∀ b, Module ℝ (E b)]
  [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E] {ι : Type w} [Fintype ι]
  {R : Type w} [CommRing R] (hι : Fintype.card ι = finrank ℝ F) (ω : Orientation ℝ F ι)

/-- **Classes of the Thom pair in the rank degree are determined by the fibre classes.** Over a
compact base, two classes of `Hʳ(E, E₀; π^*o(E), M)` whose Kronecker maps agree on the fibre class
over every point are equal. -/
theorem twistedCohomology_thomPair_ext {M : ModuleCat.{w} R}
    {α β : (thomPair F E).twistedCohomology (thomPairSignLocalSystem F E R hι) R M (finrank ℝ F)}
    (h : ∀ b, ((thomPair F E).twistedKronecker _ R (finrank ℝ F) α).hom
        (thomPairSignFiberClass F E R hι ω b) =
      ((thomPair F E).twistedKronecker _ R (finrank ℝ F) β).hom
        (thomPairSignFiberClass F E R hι ω b)) :
    α = β :=
  (twistedKronecker_bijective_thomPair F E _ R M).injective
    (thomPairTwistedHomology_hom_ext hι ω h)

variable (F E R) in
/-- **The Thom class with coefficients in the orientation system** of a real vector bundle `E` of
rank `r` over a compact base: the class `U_E ∈ Hʳ(E, E₀; π^*o(E), R)` taking the value `1` on the
fibre class over every point (`TauCeti.thomPairSignFiberClass`), for the orientation `ω` of the
model fibre. It exists without any orientation of `E`. -/
def twistedThomClass :
    (thomPair F E).twistedCohomology (thomPairSignLocalSystem F E R hι) R (ModuleCat.of R R)
      (finrank ℝ F) :=
  (thomPairTwistedCohomologyFinrankEquiv F E _ R (ModuleCat.of R R)).symm
    ((thomPairTwistedHomologyFinrankIso F E R hι ω).hom ≫
      (TopCat.of B).singularHomology₀ε (ModuleCat.of R R))

/-- The Kronecker map of the twisted Thom class is the isomorphism
`Hᵣ(E, E₀; π^*o(E)) ≅ H₀(B; R)` followed by the augmentation `H₀(B; R) ⟶ R`. -/
theorem twistedKronecker_twistedThomClass :
    (thomPair F E).twistedKronecker _ R (finrank ℝ F) (twistedThomClass F E R hι ω) =
      (thomPairTwistedHomologyFinrankIso F E R hι ω).hom ≫
        (TopCat.of B).singularHomology₀ε (ModuleCat.of R R) := by
  rw [twistedThomClass]
  exact (thomPairTwistedCohomologyFinrankEquiv_apply ..).symm.trans
    (LinearEquiv.apply_symm_apply _ _)

/-- **The twisted Thom class takes the value `1` on every fibre class.** -/
@[simp]
theorem twistedKronecker_twistedThomClass_thomPairSignFiberClass (b : B) :
    ((thomPair F E).twistedKronecker _ R (finrank ℝ F) (twistedThomClass F E R hι ω)).hom
      (thomPairSignFiberClass F E R hι ω b) = 1 := by
  rw [twistedKronecker_twistedThomClass, ConcreteCategory.comp_apply,
    thomPairTwistedHomologyFinrankIso_hom_thomPairSignFiberClass,
    singularHomology₀Section_singularHomology₀ε_apply]

/-- **Uniqueness of the twisted Thom class**: a class of `Hʳ(E, E₀; π^*o(E), R)` is the twisted Thom
class exactly when it takes the value `1` on the fibre class over every point. -/
theorem eq_twistedThomClass_iff
    {α : (thomPair F E).twistedCohomology (thomPairSignLocalSystem F E R hι) R (ModuleCat.of R R)
      (finrank ℝ F)} :
    α = twistedThomClass F E R hι ω ↔
      ∀ b, ((thomPair F E).twistedKronecker _ R (finrank ℝ F) α).hom
        (thomPairSignFiberClass F E R hι ω b) = 1 :=
  ⟨by rintro rfl b; exact twistedKronecker_twistedThomClass_thomPairSignFiberClass hι ω b,
    fun h ↦ twistedCohomology_thomPair_ext hι ω fun b ↦ by
      rw [h b, twistedKronecker_twistedThomClass_thomPairSignFiberClass]⟩

/-- Reversing the orientation `ω` of the model fibre negates the twisted Thom class. -/
theorem twistedThomClass_neg :
    twistedThomClass F E R hι (-ω) = -twistedThomClass F E R hι ω :=
  ((eq_twistedThomClass_iff hι (-ω)).2 fun b ↦ by
    simp [thomPairSignFiberClass_neg hι,
      twistedKronecker_twistedThomClass_thomPairSignFiberClass hι]).symm

end TauCeti

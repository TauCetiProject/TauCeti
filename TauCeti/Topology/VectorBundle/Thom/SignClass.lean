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

Let `E → B` be a real vector bundle of rank `r` over a compact base, with Thom pair `(E, E₀)`,
`E₀` the complement of the zero section, and let `R` be a commutative ring. Let `π^*o(E)` be the
orientation local system of `E` pulled back to the total space
(`TauCeti.thomPairSignLocalSystem`). Every bundle, orientable or not, has a **Thom class with
coefficients in its orientation system**,

`U ∈ Hʳ(E, E₀; π^*o(E), R)`,

a relative twisted cohomology class: a cocycle reads a coefficient of `π^*o(E)` at the initial
vertex of a simplex and returns an element of `R` (`TauCeti.twistedThomClass`). It is
characterized by taking the value `1` on the fibre class over every point `b`
(`TauCeti.twistedKronecker_twistedThomClass_thomPairSignFiberClass`,
`TauCeti.eq_twistedThomClass_iff`). The fibre class over `b`
(`TauCeti.thomPairSignFiberClass`) is the generator of `Hᵣ(E_b, E_b ∖ {0})` read through a
trivialization, with its coefficient the orientation of `E_b` read the same way. Reversing both
readings changes neither, so on each fibre `U` pairs the local orientation of `E_b` determined by
a generator with the orientation of `E_b` that the generator determines. An orientation of `E`
trivializes `o(E)`, and the condition becomes that of an ordinary Thom class
(`TauCeti.IsThomClass`); a non-orientable bundle has no ordinary Thom class with coefficients in
`ℤ`, and the twisted class takes its place.

The construction is the universal coefficient theorem in the bottom degree. The twisted homology
of the Thom pair vanishes below the rank (`TauCeti.isZero_twistedHomology_thomPair`), so evaluation
on homology identifies `Hʳ(E, E₀; π^*o(E), M)` with `Hom(Hᵣ(E, E₀; π^*o(E)), M)` for every module of
values `M` (`TauCeti.thomPairTwistedCohomologyFinrankEquiv`); the fibres of `π^*o(E)` are free of
rank one, hence projective. Over a compact base `Hᵣ(E, E₀; π^*o(E)) ≅ H₀(B; R)`, sending fibre
classes to classes of points (`TauCeti.thomPairTwistedHomologyFinrankIso`), so morphisms out of
it are determined by the fibre classes (`TauCeti.thomPairTwistedHomology_hom_ext`). So a class of
`Hʳ(E, E₀; π^*o(E), M)` is determined by its values on the fibre classes
(`TauCeti.twistedCohomology_thomPair_ext`), and `U` is the class whose evaluation is this
isomorphism followed by the augmentation `H₀(B; R) ⟶ R`.

The fibre classes, and with them `U`, are normalized by an orientation `ω` of the model fibre:
replacing `ω` by `-ω` negates them (`TauCeti.twistedThomClass_neg`).

Capping with `U` (`TopPair.twistedCap`) sends the relative homology of the Thom pair with
constant coefficients to the homology of `B` twisted by `o(E)`, since `o(E) ⊗ o(E)` is the
constant system (`TauCeti.VectorBundleOrientationCover.signLocalSystemTensorIso`). That is the map
of the Thom isomorphism `Hₚ₊ᵣ(E, E₀; R) ≅ Hₚ(B; o(E) ⊗ R)` with orientation-twisted coefficients,
which this file does not construct.

## Main definitions and results

* `TauCeti.twistedThomClass`: the Thom class with coefficients in the orientation system.
* `TauCeti.twistedKronecker_twistedThomClass`: its evaluation on `Hᵣ(E, E₀; π^*o(E))` is the
  identification with `H₀(B; R)` followed by the augmentation.
* `TauCeti.twistedKronecker_twistedThomClass_thomPairSignFiberClass`: it takes the value `1` on
  every fibre class.
* `TauCeti.twistedCohomology_thomPair_ext`: classes in the rank degree are determined by their
  values on the fibre classes.
* `TauCeti.eq_twistedThomClass_iff`: the Thom class is the only class taking the value `1` on every
  fibre class.
* `TauCeti.twistedThomClass_neg`: reversing the model orientation negates it.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10 (the Thom class and Lemma 10.3) and §12 (the orientation double cover).
* A. Hatcher, *Algebraic Topology*, Section 3.H (local coefficients and the universal coefficient
  theorem) and Section 4.D, Theorem 4D.10 (the Thom class).
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
  {R : Type w} (hι : Fintype.card ι = finrank ℝ F) (ω : Orientation ℝ F ι)

section Ext

variable [Ring R] {k : Type*} [Ring k] [Linear k (ModuleCat.{w} R)]

/-- **Classes of the Thom pair in the rank degree are determined on fibre classes.** Over a compact
base, two classes of `Hʳ(E, E₀; π^*o(E), M)` with the same value on the fibre class over every
point are equal: evaluation on homology is injective in the rank degree, and the fibre classes
generate `Hᵣ(E, E₀; π^*o(E)) ≅ H₀(B; R)`. -/
theorem twistedCohomology_thomPair_ext {M : ModuleCat.{w} R}
    {u v : (thomPair F E).twistedCohomology (thomPairSignLocalSystem F E R hι) k M (finrank ℝ F)}
    (h : ∀ b : B,
      ((thomPair F E).twistedKronecker (thomPairSignLocalSystem F E R hι) k (finrank ℝ F) u).hom
          (thomPairSignFiberClass F E R hι ω b) =
        ((thomPair F E).twistedKronecker (thomPairSignLocalSystem F E R hι) k (finrank ℝ F) v).hom
          (thomPairSignFiberClass F E R hι ω b)) :
    u = v :=
  (twistedKronecker_bijective_thomPair F E (thomPairSignLocalSystem F E R hι) k M).injective
    (thomPairTwistedHomology_hom_ext hι ω h)

end Ext

section ThomClass

variable [CommRing R]

variable (F E R) in
/-- **The Thom class with coefficients in the orientation system** of a real vector bundle `E` of
rank `r` over a compact base: the class `U ∈ Hʳ(E, E₀; π^*o(E), R)` taking the value `1` on the
fibre class over every point (`TauCeti.twistedKronecker_twistedThomClass_thomPairSignFiberClass`),
the only such class (`TauCeti.eq_twistedThomClass_iff`). It exists for every bundle, orientable or
not, and is normalized by the orientation `ω` of the model fibre that normalizes the fibre classes.
-/
def twistedThomClass :
    (thomPair F E).twistedCohomology (thomPairSignLocalSystem F E R hι) R (ModuleCat.of R R)
      (finrank ℝ F) :=
  (thomPairTwistedCohomologyFinrankEquiv F E (thomPairSignLocalSystem F E R hι) R
    (ModuleCat.of R R)).symm
      ((thomPairTwistedHomologyFinrankIso F E R hι ω).hom ≫
        (TopCat.of B).singularHomology₀ε (ModuleCat.of R R))

/-- The evaluation of the Thom class with coefficients in the orientation system on
`Hᵣ(E, E₀; π^*o(E))` is the identification `Hᵣ(E, E₀; π^*o(E)) ≅ H₀(B; R)` followed by the
augmentation `H₀(B; R) ⟶ R`. -/
theorem twistedKronecker_twistedThomClass :
    (thomPair F E).twistedKronecker (thomPairSignLocalSystem F E R hι) R (finrank ℝ F)
        (twistedThomClass F E R hι ω) =
      (thomPairTwistedHomologyFinrankIso F E R hι ω).hom ≫
        (TopCat.of B).singularHomology₀ε (ModuleCat.of R R) := by
  rw [twistedThomClass, ← thomPairTwistedCohomologyFinrankEquiv_apply (F := F) (E := E)
    (thomPairSignLocalSystem F E R hι) R (ModuleCat.of R R), LinearEquiv.apply_symm_apply]

/-- **The Thom class with coefficients in the orientation system takes the value `1` on every
fibre class.** -/
@[simp]
theorem twistedKronecker_twistedThomClass_thomPairSignFiberClass (b : B) :
    ((thomPair F E).twistedKronecker (thomPairSignLocalSystem F E R hι) R (finrank ℝ F)
        (twistedThomClass F E R hι ω)).hom (thomPairSignFiberClass F E R hι ω b) = 1 := by
  rw [twistedKronecker_twistedThomClass, ModuleCat.hom_comp, LinearMap.comp_apply,
    thomPairTwistedHomologyFinrankIso_hom_thomPairSignFiberClass,
    singularHomology₀Section_singularHomology₀ε_apply]

/-- **Characterization of the Thom class with coefficients in the orientation system**: a class of
`Hʳ(E, E₀; π^*o(E), R)` is the Thom class exactly when it takes the value `1` on the fibre class
over every point. -/
theorem eq_twistedThomClass_iff
    {u : (thomPair F E).twistedCohomology (thomPairSignLocalSystem F E R hι) R (ModuleCat.of R R)
      (finrank ℝ F)} :
    u = twistedThomClass F E R hι ω ↔ ∀ b : B,
      ((thomPair F E).twistedKronecker (thomPairSignLocalSystem F E R hι) R (finrank ℝ F) u).hom
        (thomPairSignFiberClass F E R hι ω b) = 1 := by
  refine ⟨?_, fun h ↦ twistedCohomology_thomPair_ext hι ω fun b ↦ ?_⟩
  · rintro rfl b
    exact twistedKronecker_twistedThomClass_thomPairSignFiberClass hι ω b
  · rw [h, twistedKronecker_twistedThomClass_thomPairSignFiberClass]

/-- **Reversing the model orientation negates the Thom class with coefficients in the orientation
system**: the fibre classes normalized by `-ω` are the negatives of those normalized by `ω`. -/
@[simp]
theorem twistedThomClass_neg : twistedThomClass F E R hι (-ω) = -twistedThomClass F E R hι ω := by
  refine ((eq_twistedThomClass_iff hι (-ω)).2 fun b ↦ ?_).symm
  rw [map_neg, thomPairSignFiberClass_neg, ModuleCat.hom_neg, LinearMap.neg_apply, map_neg,
    twistedKronecker_twistedThomClass_thomPairSignFiberClass, neg_neg]

end ThomClass

end TauCeti

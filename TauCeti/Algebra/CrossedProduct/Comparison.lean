/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.CrossedProduct.GaloisCocycle.BrauerClass
public import TauCeti.Algebra.CrossedProduct.Inflation
import TauCeti.Algebra.CrossedProduct.Comap
import TauCeti.Algebra.CrossedProduct.Injectivity

/-!
# The Brauer group as continuous `H²` of the absolute Galois group

For a field `K` with separable closure `Kˢ`, this file constructs the comparison isomorphism

```text
brauerExplicitH2Equiv K : Additive (Br K) ≃+ H²(G_K, (Kˢ)ˣ)
```

with the explicit continuous cohomology group `H²` of continuous cocycles modulo continuous
coboundaries, for a field `K` in any universe. It is characterized by its value on the Brauer
class of the crossed product of a cocycle `z` of a finite Galois subextension `L ⊆ Kˢ`, which is
`z.inflateH2 L`, the class of the inflation of `z` (`brauerExplicitH2Equiv_crossedProductClass`).
Every Brauer class is such a crossed-product class, so this equation determines the comparison
(`brauerExplicitH2Equiv_unique`). For `K : Type`, composing with the comparison of the explicit
`H²` with Mathlib's `continuousCohomology` gives `brauerCohomologyEquiv K`, which sends the same
class to `z.inflateClass L` (`brauerCohomologyEquiv_crossedProductClass`).

The equation is consistent because both sides only depend on the Brauer class. Two bundled Galois
cocycles can be compared over the compositum of their splitting fields, where neither side changes
(`crossedProductClass_comap`, `TwoCocycle.inflateH2_comap`). Over a single finite Galois
`L ⊆ Kˢ` the two sides are then equal together
(`BrauerGroup.crossedProductClass_eq_iff_inflateH2_eq`): cohomologous cocycles inflate to the
same class, and conversely a cocycle whose inflation is a continuous coboundary `d b` presents the
trivial Brauer class. For the converse, such a cocycle becomes a coboundary after refinement to a
finite Galois `M ⊇ L` (`TwoCocycle.inflateH2_eq_zero_iff`), and refinement does not change the
Brauer class.
Multiplicativity of crossed-product classes (`crossedProductClass_mul`) and additivity of inflation
(`TwoCocycle.inflateH2_mul`) make the comparison a homomorphism, and the two exhaustion theorems
`BrauerGroup.exists_galoisCocycle_brauerClass_eq` and `exists_galoisCocycle_inflateH2` make it
bijective.

## Main definitions

* `TauCeti.brauerExplicitH2Equiv K`: the comparison `Additive (Br K) ≃+ H²(G_K, (Kˢ)ˣ)` with the
  explicit continuous `H²`, for `K` in any universe.
* `TauCeti.brauerCohomologyEquiv K`: for `K : Type`, the comparison
  `Additive (Br K) ≃+ H²_cont(G_K, (Kˢ)ˣ)` with Mathlib's continuous cohomology.

## Main results

* `TauCeti.BrauerGroup.crossedProductClass_eq_iff_inflateH2_eq`: two cocycles of a finite
  Galois `L ⊆ Kˢ` have the same Brauer class exactly when they inflate to the same class.
* `TauCeti.BrauerGroup.crossedProductClass_eq_one_iff_inflateH2_eq_zero`: a crossed product is
  split exactly when the inflation of its cocycle is a continuous coboundary.
* `TauCeti.GaloisCocycle.brauerClass_eq_iff_inflateH2_eq`: the same for bundled Galois cocycles
  over possibly different splitting fields.
* `TauCeti.brauerExplicitH2Equiv_crossedProductClass`,
  `TauCeti.brauerExplicitH2Equiv_symm_inflateH2`: the comparison and its inverse on crossed
  products and inflated cocycles; `TauCeti.brauerExplicitH2Equiv_unique`: these values determine
  the comparison.
* `TauCeti.brauerCohomologyEquiv_crossedProductClass`, `TauCeti.brauerCohomologyEquiv_unique`:
  for `K : Type`, the value of `brauerCohomologyEquiv K` on crossed products, which determines it.

## References

* P. Gille and T. Szamuely, *Central Simple Algebras and Galois Cohomology* (2006), §4.4.
* J.-P. Serre, *Local Fields*, GTM 67 (1979), Chapter X, §5.
-/

public section

noncomputable section

namespace TauCeti

open ContCohomology IntermediateField

universe u

section Explicit

variable {K : Type u} [Field K]

namespace BrauerGroup

/-- Refining a cocycle to a larger finite Galois subextension does not change its Brauer class. -/
@[simp]
theorem crossedProductClass_refine {L M : IntermediateField K (SeparableClosure K)}
    [FiniteDimensional K L] [IsGalois K L] [FiniteDimensional K M] [IsGalois K M] (hLM : L ≤ M)
    (c : TwoCocycle K L) : crossedProductClass (c.refine hLM) = crossedProductClass c := by
  rw [TwoCocycle.refine_def]
  exact crossedProductClass_comap _ _ _ c

variable {L : IntermediateField K (SeparableClosure K)} [FiniteDimensional K L] [IsGalois K L]

/-- A cocycle whose inflation has trivial class presents the trivial Brauer class. -/
private theorem crossedProductClass_eq_one_of_inflateH2_eq_zero {c : TwoCocycle K L}
    (h : c.inflateH2 L = 0) : crossedProductClass c = 1 := by
  -- the cocycle becomes a coboundary over a finite Galois `M ⊇ L`
  obtain ⟨M, _, _, hLM, hcoh⟩ := (TwoCocycle.inflateH2_eq_zero_iff L).1 h
  exact (crossedProductClass_refine hLM c).symm.trans
    ((crossedProductClass_eq_of_cohomologous hcoh).symm.trans crossedProductClass_one)

/-- **Over a fixed finite Galois `L ⊆ Kˢ`, the Brauer class and the inflated class determine each
other**: two cocycles of `Gal(L/K)` have the same crossed-product class exactly when their
inflations to the absolute Galois group have the same class in `H²(G_K, (Kˢ)ˣ)`. -/
theorem crossedProductClass_eq_iff_inflateH2_eq {z w : TwoCocycle K L} :
    crossedProductClass z = crossedProductClass w ↔ z.inflateH2 L = w.inflateH2 L := by
  refine ⟨fun h ↦ TwoCocycle.inflateH2_eq_of_cohomologous L
    (cohomologous_of_crossedProductClass_eq h), fun h ↦ ?_⟩
  have h1 : crossedProductClass (z / w) = 1 :=
    crossedProductClass_eq_one_of_inflateH2_eq_zero
      (by rw [TwoCocycle.inflateH2_div, h, sub_self])
  rw [← div_mul_cancel z w, crossedProductClass_mul, h1, one_mul]

/-- **A crossed product over a finite Galois `L ⊆ Kˢ` is split exactly when the inflation of its
cocycle is a continuous coboundary.** -/
theorem crossedProductClass_eq_one_iff_inflateH2_eq_zero {c : TwoCocycle K L} :
    crossedProductClass c = 1 ↔ c.inflateH2 L = 0 := by
  rw [← crossedProductClass_one (L := L), crossedProductClass_eq_iff_inflateH2_eq,
    TwoCocycle.inflateH2_one]

end BrauerGroup

namespace GaloisCocycle

/-- The refinements of two Galois cocycles to the compositum of their splitting fields. -/
private theorem exists_refine (g₁ g₂ : GaloisCocycle K) :
    ∃ (M : IntermediateField K (SeparableClosure K)) (_ : FiniteDimensional K M)
      (_ : IsGalois K M) (z₁ z₂ : TwoCocycle K M),
      BrauerGroup.crossedProductClass z₁ = BrauerGroup.crossedProductClass g₁.cocycle ∧
        z₁.inflateH2 M = g₁.cocycle.inflateH2 g₁.extension ∧
        BrauerGroup.crossedProductClass z₂ = BrauerGroup.crossedProductClass g₂.cocycle ∧
        z₂.inflateH2 M = g₂.cocycle.inflateH2 g₂.extension :=
  -- the compositum is finite and normal, and separable as a subextension of `Kˢ`
  have : IsGalois K ↥(g₁.extension ⊔ g₂.extension) := IsGalois.mk
  ⟨_, inferInstance, inferInstance, g₁.cocycle.refine le_sup_left, g₂.cocycle.refine le_sup_right,
    BrauerGroup.crossedProductClass_refine _ _, TwoCocycle.inflateH2_refine _ _,
    BrauerGroup.crossedProductClass_refine _ _, TwoCocycle.inflateH2_refine _ _⟩

/-- **Two Galois cocycles have the same Brauer class exactly when they inflate to the same
class**, possibly over different finite Galois subextensions of `Kˢ/K`. -/
theorem brauerClass_eq_iff_inflateH2_eq {g₁ g₂ : GaloisCocycle K} :
    g₁.brauerClass = g₂.brauerClass ↔ g₁.inflateH2 = g₂.inflateH2 := by
  obtain ⟨M, _, _, z₁, z₂, hb₁, hi₁, hb₂, hi₂⟩ := exists_refine g₁ g₂
  rw [brauerClass_def, brauerClass_def, inflateH2_def, inflateH2_def, ← hb₁, ← hi₁, ← hb₂, ← hi₂]
  exact BrauerGroup.crossedProductClass_eq_iff_inflateH2_eq

/-- The product of the Brauer classes of two Galois cocycles is the Brauer class of a Galois
cocycle whose inflated class is the sum of theirs. -/
private theorem exists_brauerClass_mul (g₁ g₂ : GaloisCocycle K) :
    ∃ g : GaloisCocycle K, g.brauerClass = g₁.brauerClass * g₂.brauerClass ∧
      g.inflateH2 = g₁.inflateH2 + g₂.inflateH2 := by
  obtain ⟨M, _, _, z₁, z₂, hb₁, hi₁, hb₂, hi₂⟩ := exists_refine g₁ g₂
  refine ⟨⟨M, z₁ * z₂⟩, ?_, ?_⟩
  · simp only [brauerClass_def, BrauerGroup.crossedProductClass_mul, hb₁, hb₂]
  · simp only [inflateH2_def, TwoCocycle.inflateH2_mul, hi₁, hi₂]

end GaloisCocycle

/-! ### The comparison isomorphism -/

/-- The explicit class of a Brauer class: the inflated class of any Galois cocycle presenting it,
which does not depend on the choice by `GaloisCocycle.brauerClass_eq_iff_inflateH2_eq`. -/
private def brauerClassToH2 (x : BrauerGroup.{u, u} K) :
    H2 (AbsoluteGaloisGroup K) (UnitsCoeff K) :=
  (BrauerGroup.exists_galoisCocycle_brauerClass_eq x).choose.inflateH2

/-- On the Brauer class of a Galois cocycle, `brauerClassToH2` is its inflated class. -/
private theorem brauerClassToH2_brauerClass (g : GaloisCocycle K) :
    brauerClassToH2 g.brauerClass = g.inflateH2 :=
  GaloisCocycle.brauerClass_eq_iff_inflateH2_eq.1
    (BrauerGroup.exists_galoisCocycle_brauerClass_eq _).choose_spec

/-- `brauerClassToH2` turns products of Brauer classes into sums. -/
private theorem brauerClassToH2_mul (x y : BrauerGroup.{u, u} K) :
    brauerClassToH2 (x * y) = brauerClassToH2 x + brauerClassToH2 y := by
  obtain ⟨g₁, rfl⟩ := BrauerGroup.exists_galoisCocycle_brauerClass_eq x
  obtain ⟨g₂, rfl⟩ := BrauerGroup.exists_galoisCocycle_brauerClass_eq y
  obtain ⟨g, hb, hi⟩ := g₁.exists_brauerClass_mul g₂
  rw [← hb, brauerClassToH2_brauerClass, brauerClassToH2_brauerClass,
    brauerClassToH2_brauerClass, hi]

variable (K) in
/-- **The comparison isomorphism** `Br(K) ≃ H²(G_K, (Kˢ)ˣ)` with the explicit continuous `H²`, for
a field in any universe, with multiplication of Brauer classes going to addition of cohomology
classes. It is characterized by `brauerExplicitH2Equiv_crossedProductClass`: the class of the
crossed product of a cocycle of a finite Galois `L ⊆ Kˢ` goes to the class of the inflation of
that cocycle; see `brauerExplicitH2Equiv_unique`. -/
def brauerExplicitH2Equiv :
    Additive (BrauerGroup.{u, u} K) ≃+ H2 (AbsoluteGaloisGroup K) (UnitsCoeff K) :=
  AddEquiv.ofBijective
    (AddMonoidHom.mk' (fun x : Additive (BrauerGroup.{u, u} K) ↦ brauerClassToH2 x.toMul)
      fun x y ↦
      brauerClassToH2_mul x.toMul y.toMul)
    ⟨fun x y h ↦ by
      obtain ⟨g₁, hg₁⟩ := BrauerGroup.exists_galoisCocycle_brauerClass_eq x.toMul
      obtain ⟨g₂, hg₂⟩ := BrauerGroup.exists_galoisCocycle_brauerClass_eq y.toMul
      have h' : brauerClassToH2 x.toMul = brauerClassToH2 y.toMul := h
      rw [← hg₁, ← hg₂, brauerClassToH2_brauerClass, brauerClassToH2_brauerClass] at h'
      exact Additive.toMul.injective (hg₁.symm.trans
        ((GaloisCocycle.brauerClass_eq_iff_inflateH2_eq.2 h').trans hg₂)),
    fun z ↦
      let ⟨g, hg⟩ := exists_galoisCocycle_inflateH2 z
      ⟨Additive.ofMul g.brauerClass, (brauerClassToH2_brauerClass g).trans hg⟩⟩

/-- **The comparison on a bundled Galois cocycle**: the Brauer class of a Galois cocycle goes to its
inflated class. -/
theorem brauerExplicitH2Equiv_galoisCocycle_brauerClass (g : GaloisCocycle K) :
    brauerExplicitH2Equiv K (Additive.ofMul g.brauerClass) = g.inflateH2 :=
  brauerClassToH2_brauerClass g

/-- **The equation that determines the comparison.** On the class of the crossed product of a
cocycle `z` of a finite Galois `L ⊆ Kˢ`, the comparison is the class of the inflation of `z` to the
absolute Galois group. -/
@[simp]
theorem brauerExplicitH2Equiv_crossedProductClass (L : IntermediateField K (SeparableClosure K))
    [FiniteDimensional K L] [IsGalois K L] (z : TwoCocycle K L) :
    brauerExplicitH2Equiv K (Additive.ofMul (BrauerGroup.crossedProductClass z)) =
      z.inflateH2 L := by
  have h := brauerExplicitH2Equiv_galoisCocycle_brauerClass ⟨L, z⟩
  rwa [GaloisCocycle.brauerClass_def, GaloisCocycle.inflateH2_def] at h

/-- The inverse comparison sends the inflated class of a cocycle of a finite Galois `L ⊆ Kˢ` to the
Brauer class of its crossed product. -/
@[simp]
theorem brauerExplicitH2Equiv_symm_inflateH2 (L : IntermediateField K (SeparableClosure K))
    [FiniteDimensional K L] [IsGalois K L] (z : TwoCocycle K L) :
    (brauerExplicitH2Equiv K).symm (z.inflateH2 L) =
      Additive.ofMul (BrauerGroup.crossedProductClass z) :=
  (AddEquiv.symm_apply_eq _).2 (brauerExplicitH2Equiv_crossedProductClass L z).symm

/-- **There is only one such comparison.** Any additive equivalence sending the Brauer class of each
Galois cocycle to its inflated class is `brauerExplicitH2Equiv K`, because every Brauer class is
the class of a Galois cocycle. -/
theorem brauerExplicitH2Equiv_unique
    (e : Additive (BrauerGroup.{u, u} K) ≃+ H2 (AbsoluteGaloisGroup K) (UnitsCoeff K))
    (h : ∀ g : GaloisCocycle K, e (Additive.ofMul g.brauerClass) = g.inflateH2) :
    e = brauerExplicitH2Equiv K := by
  refine AddEquiv.ext fun x ↦ ?_
  obtain ⟨g, hg⟩ := BrauerGroup.exists_galoisCocycle_brauerClass_eq x.toMul
  rw [← ofMul_toMul x, ← hg, h, brauerExplicitH2Equiv_galoisCocycle_brauerClass]

end Explicit

/-! ### The comparison with Mathlib's continuous cohomology -/

section Continuous

variable {K : Type} [Field K]

/-- The absolute Galois group is locally compact, being compact and Hausdorff. Instance search
does not find this within its default budget under the imports of this file, so it is assembled
here from the Krull topology being Hausdorff. It is named so that it does not clash with the
anonymous local instance of `TauCeti.FieldTheory.GaloisCohomology.BrauerTorsion` in modules
importing both. -/
local instance locallyCompactSpace_absoluteGaloisGroup :
    LocallyCompactSpace (AbsoluteGaloisGroup K) :=
  have : R1Space (AbsoluteGaloisGroup K) := @T2Space.r1Space _ _ krullTopology_t2
  have : WeaklyLocallyCompactSpace (AbsoluteGaloisGroup K) :=
    ⟨fun _ ↦ ⟨Set.univ, isCompact_univ, Filter.univ_mem⟩⟩
  WeaklyLocallyCompactSpace.locallyCompactSpace

variable (K) in
/-- **The comparison isomorphism** `Br(K) ≃ H²_cont(G_K, (Kˢ)ˣ)` with Mathlib's continuous
cohomology, for `K : Type`: the explicit comparison `brauerExplicitH2Equiv K` followed by
`explicitH2AddEquivContinuousCohomology`. It is characterized by
`brauerCohomologyEquiv_crossedProductClass`: the class of the crossed product of a cocycle of a
finite Galois `L ⊆ Kˢ` goes to the continuous class of the inflation of that cocycle; see
`brauerCohomologyEquiv_unique`. -/
def brauerCohomologyEquiv :
    Additive (BrauerGroup K) ≃+
      continuousCohomology 2 (ofDiscreteModule ℤ (AbsoluteGaloisGroup K) (UnitsCoeff K)) :=
  (brauerExplicitH2Equiv K).trans
    (explicitH2AddEquivContinuousCohomology (AbsoluteGaloisGroup K) (UnitsCoeff K))

/-- For `K : Type`, the continuous comparison is the explicit one read in Mathlib's continuous
cohomology. -/
theorem brauerCohomologyEquiv_apply (x : Additive (BrauerGroup K)) :
    brauerCohomologyEquiv K x =
      explicitH2AddEquivContinuousCohomology (AbsoluteGaloisGroup K) (UnitsCoeff K)
        (brauerExplicitH2Equiv K x) :=
  (rfl)

/-- **The comparison on a bundled Galois cocycle**: the Brauer class of a Galois cocycle goes to its
inflated continuous class. -/
theorem brauerCohomologyEquiv_galoisCocycle_brauerClass (g : GaloisCocycle K) :
    brauerCohomologyEquiv K (Additive.ofMul g.brauerClass) = g.inflateClass := by
  rw [brauerCohomologyEquiv_apply, brauerExplicitH2Equiv_galoisCocycle_brauerClass,
    GaloisCocycle.inflateClass_def, TwoCocycle.inflateClass_def, GaloisCocycle.inflateH2_def]

/-- **The equation that determines the comparison.** On the class of the crossed product of a
cocycle `z` of a finite Galois `L ⊆ Kˢ`, the comparison is the continuous class of the inflation of
`z` to the absolute Galois group. -/
@[simp]
theorem brauerCohomologyEquiv_crossedProductClass (L : IntermediateField K (SeparableClosure K))
    [FiniteDimensional K L] [IsGalois K L] (z : TwoCocycle K L) :
    brauerCohomologyEquiv K (Additive.ofMul (BrauerGroup.crossedProductClass z)) =
      z.inflateClass L := by
  rw [brauerCohomologyEquiv_apply, brauerExplicitH2Equiv_crossedProductClass,
    TwoCocycle.inflateClass_def]

/-- The inverse comparison sends the inflated class of a cocycle of a finite Galois `L ⊆ Kˢ` to the
Brauer class of its crossed product. -/
@[simp]
theorem brauerCohomologyEquiv_symm_inflateClass (L : IntermediateField K (SeparableClosure K))
    [FiniteDimensional K L] [IsGalois K L] (z : TwoCocycle K L) :
    (brauerCohomologyEquiv K).symm (z.inflateClass L) =
      Additive.ofMul (BrauerGroup.crossedProductClass z) :=
  (AddEquiv.symm_apply_eq _).2 (brauerCohomologyEquiv_crossedProductClass L z).symm

/-- **There is only one such comparison.** Any additive equivalence sending the Brauer class of each
Galois cocycle to its inflated continuous class is `brauerCohomologyEquiv K`, because every Brauer
class is the class of a Galois cocycle. -/
theorem brauerCohomologyEquiv_unique
    (e : Additive (BrauerGroup K) ≃+
      continuousCohomology 2 (ofDiscreteModule ℤ (AbsoluteGaloisGroup K) (UnitsCoeff K)))
    (h : ∀ g : GaloisCocycle K, e (Additive.ofMul g.brauerClass) = g.inflateClass) :
    e = brauerCohomologyEquiv K := by
  refine AddEquiv.ext fun x ↦ ?_
  obtain ⟨g, hg⟩ := BrauerGroup.exists_galoisCocycle_brauerClass_eq x.toMul
  rw [← ofMul_toMul x, ← hg, h, brauerCohomologyEquiv_galoisCocycle_brauerClass]

end Continuous

end TauCeti

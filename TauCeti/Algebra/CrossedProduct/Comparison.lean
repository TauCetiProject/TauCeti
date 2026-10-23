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
brauerCohomologyEquiv K : Additive (Br K) ≃+ H²_cont(G_K, (Kˢ)ˣ)
```

and characterizes it: on the Brauer class of the crossed product of a cocycle `z` of a finite
Galois subextension `L ⊆ Kˢ`, it takes the value `z.inflateClass L`, the continuous class of the
inflation of `z` (`brauerCohomologyEquiv_crossedProductClass`). Every Brauer class is such a
crossed-product class, so this equation determines the comparison
(`brauerCohomologyEquiv_unique`).

The equation is consistent because both sides only depend on the Brauer class. Two bundled Galois
cocycles can be compared over the compositum of their splitting fields, where neither side changes
(`crossedProductClass_comap`, `TwoCocycle.inflateClass_comap`). Over a single finite Galois
`L ⊆ Kˢ` the two sides are then equal together
(`BrauerGroup.crossedProductClass_eq_iff_inflateClass_eq`): cohomologous cocycles inflate to the
same class, and conversely a cocycle whose inflation is a continuous coboundary `d b` presents the
trivial Brauer class. For the converse, such a cocycle becomes a coboundary after refinement to a
finite Galois `M ⊇ L` (`TwoCocycle.inflateZ2_mem_B2_iff`), and refinement does not change the
Brauer class.
Multiplicativity of crossed-product classes (`crossedProductClass_mul`) and additivity of inflation
(`TwoCocycle.inflateClass_mul`) make the comparison a homomorphism, and the two exhaustion theorems
`BrauerGroup.exists_galoisCocycle_brauerClass_eq` and `exists_galoisCocycle_inflateClass` make it
bijective.

## Main definitions

* `TauCeti.brauerCohomologyEquiv K`: the comparison `Additive (Br K) ≃+ H²_cont(G_K, (Kˢ)ˣ)`.

## Main results

* `TauCeti.BrauerGroup.crossedProductClass_eq_iff_inflateClass_eq`: two cocycles of a finite
  Galois `L ⊆ Kˢ` have the same Brauer class exactly when they inflate to the same continuous
  class.
* `TauCeti.BrauerGroup.crossedProductClass_eq_one_iff_inflateClass_eq_zero`: a crossed product is
  split exactly when the inflation of its cocycle is a continuous coboundary.
* `TauCeti.GaloisCocycle.brauerClass_eq_iff_inflateClass_eq`: the same for bundled Galois cocycles
  over possibly different splitting fields.
* `TauCeti.brauerCohomologyEquiv_crossedProductClass`,
  `TauCeti.brauerCohomologyEquiv_galoisCocycle_brauerClass`: the comparison sends the class of a
  crossed product to the inflation of its cocycle.
* `TauCeti.brauerCohomologyEquiv_unique`: this equation determines the comparison.

## References

* P. Gille and T. Szamuely, *Central Simple Algebras and Galois Cohomology* (2006), §4.4.
* J.-P. Serre, *Local Fields*, GTM 67 (1979), Chapter X, §5.
-/

public section

noncomputable section

namespace TauCeti

open ContCohomology IntermediateField

variable {K : Type} [Field K]

namespace BrauerGroup

/-- Refining a cocycle to a larger finite Galois subextension does not change its Brauer class. -/
@[simp]
theorem crossedProductClass_refine {L M : IntermediateField K (SeparableClosure K)}
    [FiniteDimensional K L] [IsGalois K L] [FiniteDimensional K M] [IsGalois K M] (hLM : L ≤ M)
    (c : TwoCocycle K L) : crossedProductClass (c.refine hLM) = crossedProductClass c := by
  rw [TwoCocycle.refine_def]
  exact crossedProductClass_comap _ _ _ c

variable {L : IntermediateField K (SeparableClosure K)} [FiniteDimensional K L] [IsGalois K L]

/-- A cocycle whose inflation has trivial continuous class presents the trivial Brauer class. -/
private theorem crossedProductClass_eq_one_of_inflateClass_eq_zero {c : TwoCocycle K L}
    (h : c.inflateClass L = 0) : crossedProductClass c = 1 := by
  rw [TwoCocycle.inflateClass_def, map_eq_zero_iff _ (AddEquiv.injective _),
    QuotientAddGroup.mk'_apply, H2pi_eq_zero_iff] at h
  -- the cocycle becomes a coboundary over a finite Galois `M ⊇ L`
  obtain ⟨M, _, _, hLM, hcoh⟩ := (TwoCocycle.inflateZ2_mem_B2_iff L).1 h
  exact (crossedProductClass_refine hLM c).symm.trans
    ((crossedProductClass_eq_of_cohomologous hcoh).symm.trans crossedProductClass_one)

/-- **Over a fixed finite Galois `L ⊆ Kˢ`, the Brauer class and the inflated continuous class
determine each other**: two cocycles of `Gal(L/K)` have the same crossed-product class exactly when
their inflations to the absolute Galois group have the same class in `H²_cont(G_K, (Kˢ)ˣ)`. -/
theorem crossedProductClass_eq_iff_inflateClass_eq {z w : TwoCocycle K L} :
    crossedProductClass z = crossedProductClass w ↔ z.inflateClass L = w.inflateClass L := by
  refine ⟨fun h ↦ TwoCocycle.inflateClass_eq_of_cohomologous L
    (cohomologous_of_crossedProductClass_eq h), fun h ↦ ?_⟩
  have h1 : crossedProductClass (z / w) = 1 :=
    crossedProductClass_eq_one_of_inflateClass_eq_zero
      (by rw [TwoCocycle.inflateClass_div, h, sub_self])
  rw [← div_mul_cancel z w, crossedProductClass_mul, h1, one_mul]

/-- **A crossed product over a finite Galois `L ⊆ Kˢ` is split exactly when the inflation of its
cocycle is a continuous coboundary.** -/
theorem crossedProductClass_eq_one_iff_inflateClass_eq_zero {c : TwoCocycle K L} :
    crossedProductClass c = 1 ↔ c.inflateClass L = 0 := by
  rw [← crossedProductClass_one (L := L), crossedProductClass_eq_iff_inflateClass_eq,
    TwoCocycle.inflateClass_one]

end BrauerGroup

namespace GaloisCocycle

/-- The refinements of two Galois cocycles to the compositum of their splitting fields. -/
private theorem exists_refine (g₁ g₂ : GaloisCocycle K) :
    ∃ (M : IntermediateField K (SeparableClosure K)) (_ : FiniteDimensional K M)
      (_ : IsGalois K M) (z₁ z₂ : TwoCocycle K M),
      BrauerGroup.crossedProductClass z₁ = BrauerGroup.crossedProductClass g₁.cocycle ∧
        z₁.inflateClass M = g₁.cocycle.inflateClass g₁.extension ∧
        BrauerGroup.crossedProductClass z₂ = BrauerGroup.crossedProductClass g₂.cocycle ∧
        z₂.inflateClass M = g₂.cocycle.inflateClass g₂.extension :=
  -- the compositum is finite and normal, and separable as a subextension of `Kˢ`
  have : IsGalois K ↥(g₁.extension ⊔ g₂.extension) := IsGalois.mk
  ⟨_, inferInstance, inferInstance, g₁.cocycle.refine le_sup_left, g₂.cocycle.refine le_sup_right,
    BrauerGroup.crossedProductClass_refine _ _, TwoCocycle.inflateClass_refine _ _,
    BrauerGroup.crossedProductClass_refine _ _, TwoCocycle.inflateClass_refine _ _⟩

/-- **Two Galois cocycles have the same Brauer class exactly when they inflate to the same
continuous class**, possibly over different finite Galois subextensions of `Kˢ/K`. -/
theorem brauerClass_eq_iff_inflateClass_eq {g₁ g₂ : GaloisCocycle K} :
    g₁.brauerClass = g₂.brauerClass ↔ g₁.inflateClass = g₂.inflateClass := by
  obtain ⟨M, _, _, z₁, z₂, hb₁, hi₁, hb₂, hi₂⟩ := exists_refine g₁ g₂
  rw [brauerClass_def, brauerClass_def, inflateClass_def, inflateClass_def, ← hb₁, ← hi₁, ← hb₂,
    ← hi₂]
  exact BrauerGroup.crossedProductClass_eq_iff_inflateClass_eq

/-- The product of the Brauer classes of two Galois cocycles is the Brauer class of a Galois
cocycle whose inflated class is the sum of theirs. -/
private theorem exists_brauerClass_mul (g₁ g₂ : GaloisCocycle K) :
    ∃ g : GaloisCocycle K, g.brauerClass = g₁.brauerClass * g₂.brauerClass ∧
      g.inflateClass = g₁.inflateClass + g₂.inflateClass := by
  obtain ⟨M, _, _, z₁, z₂, hb₁, hi₁, hb₂, hi₂⟩ := exists_refine g₁ g₂
  refine ⟨⟨M, z₁ * z₂⟩, ?_, ?_⟩
  · simp only [brauerClass_def, BrauerGroup.crossedProductClass_mul, hb₁, hb₂]
  · simp only [inflateClass_def, TwoCocycle.inflateClass_mul, hi₁, hi₂]

end GaloisCocycle

/-! ### The comparison isomorphism -/

/-- The continuous class of a Brauer class: the inflated class of any Galois cocycle presenting
it, which does not depend on the choice by `GaloisCocycle.brauerClass_eq_iff_inflateClass_eq`. -/
private def brauerClassToCohomology (x : BrauerGroup K) :
    continuousCohomology 2 (ofDiscreteModule ℤ (AbsoluteGaloisGroup K) (UnitsCoeff K)) :=
  (BrauerGroup.exists_galoisCocycle_brauerClass_eq x).choose.inflateClass

/-- On the Brauer class of a Galois cocycle, `brauerClassToCohomology` is its inflated class. -/
private theorem brauerClassToCohomology_brauerClass (g : GaloisCocycle K) :
    brauerClassToCohomology g.brauerClass = g.inflateClass :=
  GaloisCocycle.brauerClass_eq_iff_inflateClass_eq.1
    (BrauerGroup.exists_galoisCocycle_brauerClass_eq _).choose_spec

/-- `brauerClassToCohomology` turns products of Brauer classes into sums. -/
private theorem brauerClassToCohomology_mul (x y : BrauerGroup K) :
    brauerClassToCohomology (x * y) = brauerClassToCohomology x + brauerClassToCohomology y := by
  obtain ⟨g₁, rfl⟩ := BrauerGroup.exists_galoisCocycle_brauerClass_eq x
  obtain ⟨g₂, rfl⟩ := BrauerGroup.exists_galoisCocycle_brauerClass_eq y
  obtain ⟨g, hb, hi⟩ := g₁.exists_brauerClass_mul g₂
  rw [← hb, brauerClassToCohomology_brauerClass, brauerClassToCohomology_brauerClass,
    brauerClassToCohomology_brauerClass, hi]

variable (K) in
/-- **The comparison isomorphism** `Br(K) ≃ H²_cont(G_K, (Kˢ)ˣ)`, with multiplication of Brauer
classes going to addition of cohomology classes. It is characterized by
`brauerCohomologyEquiv_crossedProductClass`: the class of the crossed product of a cocycle of a
finite Galois `L ⊆ Kˢ` goes to the continuous class of the inflation of that cocycle; see
`brauerCohomologyEquiv_unique`. -/
def brauerCohomologyEquiv :
    Additive (BrauerGroup K) ≃+
      continuousCohomology 2 (ofDiscreteModule ℤ (AbsoluteGaloisGroup K) (UnitsCoeff K)) :=
  AddEquiv.ofBijective
    (AddMonoidHom.mk' (fun x ↦ brauerClassToCohomology x.toMul) fun x y ↦
      brauerClassToCohomology_mul x.toMul y.toMul)
    ⟨fun x y h ↦ by
      obtain ⟨g₁, hg₁⟩ := BrauerGroup.exists_galoisCocycle_brauerClass_eq x.toMul
      obtain ⟨g₂, hg₂⟩ := BrauerGroup.exists_galoisCocycle_brauerClass_eq y.toMul
      have h' : brauerClassToCohomology x.toMul = brauerClassToCohomology y.toMul := h
      rw [← hg₁, ← hg₂, brauerClassToCohomology_brauerClass,
        brauerClassToCohomology_brauerClass] at h'
      exact Additive.toMul.injective (hg₁.symm.trans
        ((GaloisCocycle.brauerClass_eq_iff_inflateClass_eq.2 h').trans hg₂)),
    fun z ↦
      let ⟨g, hg⟩ := exists_galoisCocycle_inflateClass z
      ⟨Additive.ofMul g.brauerClass, (brauerClassToCohomology_brauerClass g).trans hg⟩⟩

/-- **The comparison on a bundled Galois cocycle**: the Brauer class of a Galois cocycle goes to its
inflated continuous class. -/
theorem brauerCohomologyEquiv_galoisCocycle_brauerClass (g : GaloisCocycle K) :
    brauerCohomologyEquiv K (Additive.ofMul g.brauerClass) = g.inflateClass :=
  brauerClassToCohomology_brauerClass g

/-- **The equation that determines the comparison.** On the class of the crossed product of a
cocycle `z` of a finite Galois `L ⊆ Kˢ`, the comparison is the continuous class of the inflation of
`z` to the absolute Galois group. -/
@[simp]
theorem brauerCohomologyEquiv_crossedProductClass (L : IntermediateField K (SeparableClosure K))
    [FiniteDimensional K L] [IsGalois K L] (z : TwoCocycle K L) :
    brauerCohomologyEquiv K (Additive.ofMul (BrauerGroup.crossedProductClass z)) =
      z.inflateClass L := by
  have h := brauerCohomologyEquiv_galoisCocycle_brauerClass ⟨L, z⟩
  rwa [GaloisCocycle.brauerClass_def, GaloisCocycle.inflateClass_def] at h

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

end TauCeti

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
import TauCeti.RepresentationTheory.Homological.ContCohomology.FiniteQuotient.Descent

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
trivial Brauer class. For the converse, the continuous cochain `b` descends to a finite Galois
`M ⊇ L` with values in `Mˣ` (`ContCohomology.exists_openNormalSubgroup_descendContinuous` and the
fixed-field theorem for units), so that the cocycle refined to `M` is a coboundary there.
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

/-! ### Refining a cocycle to a larger subextension -/

namespace TwoCocycle

variable {L M : IntermediateField K (SeparableClosure K)} [Normal K L] [Normal K M]

/-- The refinement of a cocycle of `Gal(L/K)` to `Gal(M/K)` for `L ≤ M` inside `Kˢ`: the
inflation along restriction `Gal(M/K) → Gal(L/K)` and the inclusion `L ⊆ M`. -/
private def refine (hLM : L ≤ M) (c : TwoCocycle K L) : TwoCocycle K M :=
  c.comap (inclusion hLM).restrictNormalHom (inclusion hLM)
    (inclusion hLM).restrictNormalHom_commutes

/-- On restrictions of automorphisms of `Kˢ`, the refinement of `c` takes the values of `c`. -/
private theorem val_refine_toFun (hLM : L ≤ M) (c : TwoCocycle K L)
    (g k : Gal(SeparableClosure K/K)) :
    M.val ((c.refine hLM).toFun (AlgEquiv.restrictNormalHom M g)
        (AlgEquiv.restrictNormalHom M k)) =
      L.val (c.toFun (AlgEquiv.restrictNormalHom L g) (AlgEquiv.restrictNormalHom L k)) := by
  rw [refine, comap_toFun,
    restrictNormalHom_of_compatible _ _ (inclusion hLM).restrictNormalHom_commutes (fun _ ↦ rfl),
    restrictNormalHom_of_compatible _ _ (inclusion hLM).restrictNormalHom_commutes (fun _ ↦ rfl)]
  rfl

/-- If, on restrictions of automorphisms of `Kˢ`, the values of `c` are the coboundary of a
cochain `B : Gal(M/K) → Mˣ`, then the refinement of `c` to `M` is a coboundary. -/
private theorem one_cohomologous_refine (hLM : L ≤ M) (c : TwoCocycle K L) (B : Gal(M/K) → Mˣ)
    (hB : ∀ g k : Gal(SeparableClosure K/K),
      L.val (c.toFun (AlgEquiv.restrictNormalHom L g) (AlgEquiv.restrictNormalHom L k)) =
        g (M.val (B (AlgEquiv.restrictNormalHom M k))) *
          (M.val (B (AlgEquiv.restrictNormalHom M g * AlgEquiv.restrictNormalHom M k)))⁻¹ *
            M.val (B (AlgEquiv.restrictNormalHom M g))) :
    (1 : TwoCocycle K M).Cohomologous (c.refine hLM) := by
  have hsurj := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := M) (SeparableClosure K)
  refine cohomologous_iff.2 ⟨B, fun σ τ ↦ ?_⟩
  obtain ⟨g, rfl⟩ := hsurj σ
  obtain ⟨k, rfl⟩ := hsurj τ
  apply M.val.injective
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  have hr (x : M) : M.val (AlgEquiv.restrictNormalHom M g x) = g (M.val x) :=
    AlgEquiv.restrictNormal_commutes g M x
  rw [val_refine_toFun, hB, toFun_one, Units.val_one, one_mul, map_mul, map_mul, hr,
    Units.val_inv_eq_inv_val, map_inv₀]

/-- Refining a cocycle to a larger finite normal subextension does not change its inflated
continuous class. -/
private theorem inflateClass_refine [FiniteDimensional K L] [FiniteDimensional K M] (hLM : L ≤ M)
    (c : TwoCocycle K L) : (c.refine hLM).inflateClass M = c.inflateClass L :=
  c.inflateClass_comap _ _ _ fun _ ↦ rfl

end TwoCocycle

namespace BrauerGroup

/-- Refining a cocycle to a larger finite Galois subextension does not change its Brauer class. -/
private theorem crossedProductClass_refine {L M : IntermediateField K (SeparableClosure K)}
    [FiniteDimensional K L] [IsGalois K L] [FiniteDimensional K M] [IsGalois K M] (hLM : L ≤ M)
    (c : TwoCocycle K L) : crossedProductClass (c.refine hLM) = crossedProductClass c :=
  crossedProductClass_comap _ _ _ c

variable {L : IntermediateField K (SeparableClosure K)} [FiniteDimensional K L] [IsGalois K L]

/-- A cocycle whose inflation has trivial continuous class presents the trivial Brauer class. -/
private theorem crossedProductClass_eq_one_of_inflateClass_eq_zero {c : TwoCocycle K L}
    (h : c.inflateClass L = 0) : crossedProductClass c = 1 := by
  rw [TwoCocycle.inflateClass_def, map_eq_zero_iff _ (AddEquiv.injective _),
    QuotientAddGroup.mk'_apply, H2pi_eq_zero_iff] at h
  obtain ⟨b, hb, hd⟩ := mem_B2_iff.1 h
  -- the continuous primitive `b` descends to a finite Galois level `M ⊇ L`
  obtain ⟨V, hVU, bV, -, hbV⟩ :=
    exists_openNormalSubgroup_descendContinuous (galoisOpenNormalSubgroup K L L.val) b hb
  obtain ⟨M, _, _, rfl⟩ := exists_galoisOpenNormalSubgroup_eq V
  have hLM : L ≤ M := by
    have h : (galoisOpenNormalSubgroup K M M.val).toSubgroup ≤
        (galoisOpenNormalSubgroup K L L.val).toSubgroup := hVU
    rw [galoisOpenNormalSubgroup_toSubgroup, galoisOpenNormalSubgroup_toSubgroup,
      fieldRange_val, fieldRange_val] at h
    rw [← InfiniteGalois.fixedField_fixingSubgroup M, le_iff_le]
    exact h
  -- `b` only depends on the restriction to `M`, and takes values in `Mˣ`
  have hconst : ∀ g g' : Gal(SeparableClosure K/K),
      AlgEquiv.restrictNormalHom M g = AlgEquiv.restrictNormalHom M g' → b g = b g' := by
    intro g g' hgg'
    have hker : g⁻¹ * g' ∈ M.val.restrictNormalHom.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, restrictNormalHom_val, hgg', inv_mul_cancel]
    rw [AlgHom.ker_restrictNormalHom] at hker
    rw [← hbV, ← hbV]
    exact congrArg (fun q ↦ (bV q : UnitsCoeff K)) (QuotientGroup.eq.2 hker)
  choose b' hb' using fun g ↦ mem_H0_fixingSubgroup_unitsCoeff_iff.1 (hbV g ▸ (bV g).2)
  have hsurj := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := M) (SeparableClosure K)
  let B : Gal(M/K) → Mˣ := fun σ ↦ b' (Function.surjInv hsurj σ)
  have hB (g : Gal(SeparableClosure K/K)) :
      M.val (B (AlgEquiv.restrictNormalHom M g) : M) = ((b g).toMul : SeparableClosure K) :=
    congrArg Units.val ((hb' _).trans (congrArg _ (hconst _ _ (Function.surjInv_eq hsurj _))))
  -- so `B` exhibits the refinement of `c` to `M` as a coboundary
  have hcoh : (1 : TwoCocycle K M).Cohomologous (c.refine hLM) := by
    refine c.one_cohomologous_refine hLM B fun g k ↦ ?_
    rw [← map_mul, hB, hB, hB]
    simpa [AlgEquiv.smul_units_def, div_eq_mul_inv] using (congrArg
      (fun x : UnitsCoeff K ↦ ((x.toMul : (SeparableClosure K)ˣ) : SeparableClosure K))
        (congrFun hd (g, k))).symm
  rw [← crossedProductClass_refine hLM, ← crossedProductClass_eq_of_cohomologous hcoh,
    crossedProductClass_one]

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

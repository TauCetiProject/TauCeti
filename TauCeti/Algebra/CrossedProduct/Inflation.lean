/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.CrossedProduct.Cohomology
public import TauCeti.Algebra.CrossedProduct.GaloisCocycle.Basic
public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.FiniteExtension
public import TauCeti.FieldTheory.GaloisCohomology.Coefficients
public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologyComparison
public import TauCeti.RepresentationTheory.Homological.ContCohomology.FiniteQuotient.Colimit
import TauCeti.RepresentationTheory.Homological.ContCohomology.FiniteQuotient.DegreeTwoDescent
import TauCeti.RepresentationTheory.Homological.ContCohomology.FiniteQuotient.Descent

/-!
# Inflation of crossed-product cocycles

A `TwoCocycle K L` for a finite Galois subextension `L` of the separable closure of `K` inflates
along restriction `G_K → Gal(L/K)` to a continuous cocycle of the absolute Galois group with
values in `Additive (Kˢ)ˣ`. This file constructs its class `TwoCocycle.inflateH2` in the explicit
continuous `H²`, reads it as `TwoCocycle.inflateClass` in Mathlib's continuous cohomology, and
identifies the latter with the corresponding leg of the finite-quotient description of continuous
cohomology.

The multiplicative-to-additive conversion is `Additive.ofMul`. Continuity follows because
restriction has finite discrete target. Inflation turns products of cocycles into sums of
classes, cohomologous finite cocycles determine the same continuous class, and passing to a larger
finite Galois subextension, along any compatible pair agreeing with the inclusions into `Kˢ`, does
not change the class. `TwoCocycle.refine` is the refinement along the inclusion `L ⊆ M`.

Conversely, strict finite-quotient descent of continuous `2`-cocycles, followed by the infinite
Galois correspondence, realizes every continuous cocycle as the inflation of a cocycle on a finite
Galois subextension. Consequently every explicit and every continuous cohomology class is the
inflated class of a bundled `GaloisCocycle`. Coboundaries descend in the same way: the inflation
of a cocycle of `Gal(L/K)` is a continuous coboundary exactly when the cocycle becomes a coboundary
over some finite Galois `M ⊇ L`, after refinement (`TwoCocycle.inflateZ2_mem_B2_iff`). The
continuous primitive takes only finitely many values, which lie in `Mˣ` for the fixed field `M` of
an open normal subgroup on whose cosets it is constant.

Every statement holds for a field `K` in an arbitrary universe, both those about the explicit
cocycle groups `Z²` and `B²` and the explicit `H²` and those about Mathlib's `continuousCohomology`.

The conventions follow Gille--Szamuely, *Central Simple Algebras and Galois Cohomology*, §4.4,
and Serre, *Local Fields*, Chapter X.
-/

public section

noncomputable section

open groupCohomology

namespace TauCeti

open ContCohomology IntermediateField

universe u

namespace TwoCocycle

/-! ### Inflated cocycles -/

section Cocycle

variable {K : Type u} [Field K] (L : IntermediateField K (SeparableClosure K))

section Normal

variable [Normal K L]

/-- Inflation of a cocycle on `Gal(L/K)` to the absolute Galois group, along restriction and the
inclusion `L ⊆ Kˢ`. -/
def inflate (c : TwoCocycle K L) : TwoCocycle K (SeparableClosure K) :=
  c.comap (AlgEquiv.restrictNormalHom L) L.val fun g x ↦
    AlgEquiv.restrictNormal_commutes g L x

/-- Inflating a cocycle and evaluating it amounts to restricting both automorphisms and including
its value in the separable closure. -/
@[simp]
theorem inflate_toFun (c : TwoCocycle K L) (g h : AbsoluteGaloisGroup K) :
    (c.inflate L).toFun g h =
      Units.map L.val.toRingHom.toMonoidHom
        (c.toFun (AlgEquiv.restrictNormalHom L g) (AlgEquiv.restrictNormalHom L h)) :=
  TwoCocycle.comap_toFun c _ _ _ g h

end Normal

section Finite

variable [FiniteDimensional K L] [Normal K L]

/-- The additive cochain `(g, h) ↦ c(g|_L, h|_L)` of the inflation of a cocycle of a finite normal
subextension is continuous. -/
theorem continuous_ofMul_inflate_toFun (c : TwoCocycle K L) :
    Continuous fun p : AbsoluteGaloisGroup K × AbsoluteGaloisGroup K ↦
      (Additive.ofMul ((c.inflate L).toFun p.1 p.2) : UnitsCoeff K) := by
  have hfactor : (fun p : AbsoluteGaloisGroup K × AbsoluteGaloisGroup K ↦
      (Additive.ofMul ((c.inflate L).toFun p.1 p.2) : UnitsCoeff K)) =
      (fun q : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) ↦
        Additive.ofMul (Units.map L.val.toRingHom.toMonoidHom (c.toFun q.1 q.2))) ∘
        Prod.map (AlgEquiv.restrictNormalHom L) (AlgEquiv.restrictNormalHom L) := by
    ext p
    simp only [inflate_toFun, Function.comp_apply, Prod.map_fst, Prod.map_snd]
  rw [hfactor]
  exact continuous_of_discreteTopology.comp
    ((InfiniteGalois.restrictNormalHom_continuous L).prodMap
      (InfiniteGalois.restrictNormalHom_continuous L))

/-- The inflated cocycle as an element of the explicit continuous cocycle group `Z²`. -/
def inflateZ2 (c : TwoCocycle K L) :
    Z2 (AbsoluteGaloisGroup K) (UnitsCoeff K) :=
  -- `IsCocycle₂` of a cochain `Additive.ofMul ∘ f` unfolds to `IsMulCocycle₂ f`.
  ⟨fun p ↦ Additive.ofMul ((c.inflate L).toFun p.1 p.2),
    mem_Z2_iff.2 ⟨c.continuous_ofMul_inflate_toFun L, (c.inflate L).isMulCocycle₂⟩⟩

/-- The cocycle underlying `inflateZ2` is the additive cocycle of the inflated cocycle. -/
@[simp]
theorem coe_inflateZ2 (c : TwoCocycle K L) :
    (c.inflateZ2 L : AbsoluteGaloisGroup K × AbsoluteGaloisGroup K → UnitsCoeff K) =
      fun p ↦ Additive.ofMul ((c.inflate L).toFun p.1 p.2) :=
  (rfl)

/-- Inflation turns the pointwise product of cocycles into the sum of continuous cocycles. -/
@[simp]
theorem inflateZ2_mul (z w : TwoCocycle K L) :
    (z * w).inflateZ2 L = z.inflateZ2 L + w.inflateZ2 L :=
  Subtype.ext <| funext fun p ↦ by
    simp only [coe_inflateZ2, inflate_toFun, toFun_mul, map_mul, ofMul_mul,
      AddSubgroup.coe_add, Pi.add_apply]

/-- The trivial cocycle inflates to the zero continuous cocycle. -/
@[simp]
theorem inflateZ2_one : (1 : TwoCocycle K L).inflateZ2 L = 0 :=
  left_eq_add.1 <| by rw [← inflateZ2_mul, one_mul]

/-- The difference of inflated cohomologous cocycles is the inflation of their finite
coboundary, hence is a continuous coboundary. -/
theorem inflateZ2_sub_mem_B2 {z w : TwoCocycle K L} (h : z.Cohomologous w) :
    ((z.inflateZ2 L : AbsoluteGaloisGroup K × AbsoluteGaloisGroup K → UnitsCoeff K) -
      w.inflateZ2 L) ∈ B2 (AbsoluteGaloisGroup K) (UnitsCoeff K) := by
  obtain ⟨b, hb⟩ := cohomologous_def.1 h.symm
  refine mem_B2_iff'.2 ⟨(fun σ : L ≃ₐ[K] L ↦
    Additive.ofMul (Units.map L.val.toRingHom.toMonoidHom (b σ))) ∘
      AlgEquiv.restrictNormalHom L,
    continuous_of_discreteTopology.comp (InfiniteGalois.restrictNormalHom_continuous L),
    fun g k ↦ Additive.toMul.injective ?_⟩
  -- The inflated coboundary of `b` is the image of the finite coboundary `hb` under `Kˢ ⊇ L`.
  simp only [Function.comp_apply, toMul_add, toMul_sub, toMul_ofMul, Additive.toMul_smul,
    Pi.sub_apply, coe_inflateZ2, inflate_toFun]
  rw [← IntermediateField.units_map_val_restrictNormalHom, ← AlgEquiv.smul_units_def, map_mul,
    ← map_div, ← map_mul, hb, map_div]

end Finite

section Refinement

variable {L} {M : IntermediateField K (SeparableClosure K)} [Normal K L] [Normal K M]
  (π : (M ≃ₐ[K] M) →* (L ≃ₐ[K] L)) (ι : L →ₐ[K] M) (hπι : ∀ g x, ι (π g x) = g (ι x))
  (hι : ∀ x, M.val (ι x) = L.val x)
include hπι hι

/-- Refining a normal subextension along a compatible pair `(π, ι)`, with `ι` compatible with the
inclusions into `Kˢ`, before inflation does not change the cocycle on the absolute Galois
group. -/
theorem inflate_comap (c : TwoCocycle K L) : (c.comap π ι hπι).inflate M = c.inflate L := by
  ext g k
  rw [inflate_toFun, comap_toFun, inflate_toFun, restrictNormalHom_of_compatible π ι hπι hι,
    restrictNormalHom_of_compatible π ι hπι hι]
  simpa using hι (c.toFun (AlgEquiv.restrictNormalHom L g) (AlgEquiv.restrictNormalHom L k))

variable [FiniteDimensional K L] [FiniteDimensional K M]

/-- Refining the finite normal subextension along a compatible pair does not change the inflated
continuous cocycle. -/
theorem inflateZ2_comap (c : TwoCocycle K L) :
    (c.comap π ι hπι).inflateZ2 M = c.inflateZ2 L :=
  Subtype.ext (by rw [coe_inflateZ2, coe_inflateZ2, inflate_comap π ι hπι hι])

end Refinement

section Inclusion

variable {L} {M : IntermediateField K (SeparableClosure K)} [Normal K L]

/-- The refinement of a cocycle of `Gal(L/K)` to `Gal(M/K)` for `L ≤ M` inside `Kˢ`: its
`comap` along restriction `Gal(M/K) → Gal(L/K)` and the inclusion `L ⊆ M`. -/
def refine (hLM : L ≤ M) (c : TwoCocycle K L) : TwoCocycle K M :=
  c.comap (inclusion hLM).restrictNormalHom (inclusion hLM)
    (inclusion hLM).restrictNormalHom_commutes

/-- `refine` is `comap` along restriction and the inclusion. -/
theorem refine_def (hLM : L ≤ M) (c : TwoCocycle K L) :
    c.refine hLM = c.comap (inclusion hLM).restrictNormalHom (inclusion hLM)
      (inclusion hLM).restrictNormalHom_commutes :=
  (rfl)

/-- On restrictions of automorphisms of `Kˢ`, the refinement of `c` to `M ⊇ L` takes the values
of `c`, read in `Kˢ`. -/
theorem val_refine_toFun_restrictNormalHom [Normal K M] (hLM : L ≤ M) (c : TwoCocycle K L)
    (g k : Gal(SeparableClosure K/K)) :
    M.val ((c.refine hLM).toFun (AlgEquiv.restrictNormalHom M g)
        (AlgEquiv.restrictNormalHom M k)) =
      L.val (c.toFun (AlgEquiv.restrictNormalHom L g) (AlgEquiv.restrictNormalHom L k)) := by
  rw [refine_def, comap_toFun,
    restrictNormalHom_of_compatible _ _ (inclusion hLM).restrictNormalHom_commutes
      (coe_inclusion hLM),
    restrictNormalHom_of_compatible _ _ (inclusion hLM).restrictNormalHom_commutes
      (coe_inclusion hLM),
    Units.coe_map, MonoidHom.coe_ofClass, coe_val, coe_val, coe_inclusion]

/-- Refining a cocycle to a larger finite normal subextension does not change its inflated
continuous cocycle. -/
@[simp]
theorem inflateZ2_refine [Normal K M] [FiniteDimensional K L] [FiniteDimensional K M] (hLM : L ≤ M)
    (c : TwoCocycle K L) : (c.refine hLM).inflateZ2 M = c.inflateZ2 L :=
  inflateZ2_comap _ _ _ (coe_inclusion hLM) c

end Inclusion

section Coboundary

variable [Normal K L]

/-- If, on restrictions of automorphisms of `Kˢ`, the values of `c` are the coboundary of a
cochain `B : Gal(M/K) → Mˣ`, then the refinement of `c` to `M ⊇ L` along the inclusion is a
coboundary. -/
private theorem one_cohomologous_refine {M : IntermediateField K (SeparableClosure K)}
    [Normal K M] (hLM : L ≤ M) (c : TwoCocycle K L) (B : Gal(M/K) → Mˣ)
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
  rw [val_refine_toFun_restrictNormalHom, hB, toFun_one, Units.val_one, one_mul, map_mul,
    map_mul, hr, Units.val_inv_eq_inv_val, map_inv₀]

variable [FiniteDimensional K L]

/-- A cocycle whose inflation is a continuous coboundary becomes a coboundary over a finite Galois
`M ⊇ L`: the continuous primitive descends to `M`, with values in `Mˣ`. -/
private theorem exists_one_cohomologous_refine_of_inflateZ2_mem_B2 {c : TwoCocycle K L}
    (h : (c.inflateZ2 L : AbsoluteGaloisGroup K × AbsoluteGaloisGroup K → UnitsCoeff K) ∈
      B2 (AbsoluteGaloisGroup K) (UnitsCoeff K)) :
    ∃ (M : IntermediateField K (SeparableClosure K)) (_ : FiniteDimensional K M)
      (_ : IsGalois K M) (hLM : L ≤ M),
      (1 : TwoCocycle K M).Cohomologous (c.refine hLM) := by
  obtain ⟨b, hb, hd⟩ := mem_B2_iff.1 h
  -- the continuous primitive `b` descends to a finite Galois level `M ⊇ L`
  obtain ⟨V, hVU, bV, -, hbV⟩ :=
    exists_openNormalSubgroup_descendContinuous (galoisOpenNormalSubgroup K L L.val) b hb
  obtain ⟨M, _, _, rfl⟩ := exists_galoisOpenNormalSubgroup_eq V
  have hLM : L ≤ M := by
    have h := OpenNormalSubgroup.toSubgroup_le.2 hVU
    rw [galoisOpenNormalSubgroup_toSubgroup, galoisOpenNormalSubgroup_toSubgroup,
      fieldRange_val, fieldRange_val] at h
    rw [← InfiniteGalois.fixedField_fixingSubgroup M, le_fixedField_iff_le_fixingSubgroup]
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
  refine ⟨M, inferInstance, inferInstance, hLM, ?_⟩
  refine one_cohomologous_refine L hLM c B fun g k ↦ ?_
  rw [← map_mul, hB, hB, hB]
  simpa [AlgEquiv.smul_units_def, div_eq_mul_inv] using (congrArg
    (fun x : UnitsCoeff K ↦ ((x.toMul : (SeparableClosure K)ˣ) : SeparableClosure K))
      (congrFun hd (g, k))).symm

/-- **Continuous coboundaries descend to a finite level.** The inflation of a cocycle `c` of a
finite normal `L ⊆ Kˢ` is a continuous coboundary exactly when `c` becomes a coboundary after
refinement, along the inclusion, to some finite Galois `M ⊇ L` inside `Kˢ`. -/
theorem inflateZ2_mem_B2_iff {c : TwoCocycle K L} :
    (c.inflateZ2 L : AbsoluteGaloisGroup K × AbsoluteGaloisGroup K → UnitsCoeff K) ∈
        B2 (AbsoluteGaloisGroup K) (UnitsCoeff K) ↔
      ∃ (M : IntermediateField K (SeparableClosure K)) (_ : FiniteDimensional K M)
        (_ : IsGalois K M) (hLM : L ≤ M),
        (1 : TwoCocycle K M).Cohomologous (c.refine hLM) := by
  refine ⟨exists_one_cohomologous_refine_of_inflateZ2_mem_B2 L, ?_⟩
  rintro ⟨M, _, _, hLM, hc⟩
  have h := inflateZ2_sub_mem_B2 M hc
  rw [inflateZ2_one, inflateZ2_refine] at h
  simpa using neg_mem h

end Coboundary

section ExplicitClass

variable [FiniteDimensional K L] [Normal K L]

/-- The class in the explicit continuous cohomology group `H²(G_K, (Kˢ)ˣ)` of the inflation of
`c`. Unlike `inflateClass`, which lives in Mathlib's `continuousCohomology`, it is defined for a
field `K` in any universe. -/
def inflateH2 (c : TwoCocycle K L) : H2 (AbsoluteGaloisGroup K) (UnitsCoeff K) :=
  H2pi _ _ (c.inflateZ2 L)

/-- The representative of the explicit class `inflateH2`. -/
theorem inflateH2_def (c : TwoCocycle K L) : c.inflateH2 L = H2pi _ _ (c.inflateZ2 L) :=
  (rfl)

/-- **Inflation is additive**: the pointwise product of cocycles inflates to the sum of their
explicit classes. -/
@[simp]
theorem inflateH2_mul (z w : TwoCocycle K L) :
    (z * w).inflateH2 L = z.inflateH2 L + w.inflateH2 L := by
  rw [inflateH2, inflateH2, inflateH2, inflateZ2_mul, map_add]

/-- The trivial cocycle inflates to the zero class. -/
@[simp]
theorem inflateH2_one : (1 : TwoCocycle K L).inflateH2 L = 0 := by
  rw [inflateH2, inflateZ2_one, map_zero]

/-- Inflation turns the pointwise quotient of cocycles into the difference of their classes. -/
@[simp]
theorem inflateH2_div (z w : TwoCocycle K L) :
    (z / w).inflateH2 L = z.inflateH2 L - w.inflateH2 L :=
  eq_sub_of_add_eq <| by rw [← inflateH2_mul, div_mul_cancel]

/-- Cohomologous crossed-product cocycles have the same explicit class after inflation. -/
theorem inflateH2_eq_of_cohomologous {z w : TwoCocycle K L} (h : z.Cohomologous w) :
    z.inflateH2 L = w.inflateH2 L :=
  H2pi_eq_iff.2 (inflateZ2_sub_mem_B2 L h)

/-- **The inflated class vanishes exactly when the cocycle splits at a finite level**: after
refinement, along the inclusion, to some finite Galois `M ⊇ L` inside `Kˢ`, the cocycle becomes
cohomologous to the trivial one. -/
theorem inflateH2_eq_zero_iff {c : TwoCocycle K L} :
    c.inflateH2 L = 0 ↔
      ∃ (M : IntermediateField K (SeparableClosure K)) (_ : FiniteDimensional K M)
        (_ : IsGalois K M) (hLM : L ≤ M),
        (1 : TwoCocycle K M).Cohomologous (c.refine hLM) := by
  rw [inflateH2, QuotientAddGroup.mk'_apply, H2pi_eq_zero_iff, inflateZ2_mem_B2_iff]

variable {L} in
/-- Refining the finite normal subextension on which a cocycle is defined, along a compatible pair
`(π, ι)` with `ι` compatible with the inclusions into `Kˢ`, does not change its inflated class. -/
theorem inflateH2_comap {M : IntermediateField K (SeparableClosure K)} [FiniteDimensional K M]
    [Normal K M] (π : (M ≃ₐ[K] M) →* (L ≃ₐ[K] L)) (ι : L →ₐ[K] M)
    (hπι : ∀ g x, ι (π g x) = g (ι x)) (hι : ∀ x, M.val (ι x) = L.val x) (c : TwoCocycle K L) :
    (c.comap π ι hπι).inflateH2 M = c.inflateH2 L := by
  rw [inflateH2, inflateH2, inflateZ2_comap π ι hπι hι]

variable {L} in
/-- Refining a cocycle to a larger finite normal subextension does not change its inflated
class. -/
@[simp]
theorem inflateH2_refine {M : IntermediateField K (SeparableClosure K)} [FiniteDimensional K M]
    [Normal K M] (hLM : L ≤ M) (c : TwoCocycle K L) :
    (c.refine hLM).inflateH2 M = c.inflateH2 L :=
  inflateH2_comap _ _ _ (coe_inclusion hLM) c

end ExplicitClass

section FiniteLevel

variable [FiniteDimensional K L] [Normal K L]

/-- The quotient identification, bundled as a continuous homomorphism. -/
private def galoisQuotientHom :
    AbsoluteGaloisGroup K ⧸ (galoisOpenNormalSubgroup K L L.val).toSubgroup →ₜ* (L ≃ₐ[K] L) :=
  { (quotientFixingSubgroupFieldRangeEquiv K L L.val).toMonoidHom with
    continuous_toFun := continuous_of_discreteTopology }

/-- `galoisQuotientHom` is the quotient identification `quotientFixingSubgroupFieldRangeEquiv`. -/
private theorem galoisQuotientHom_apply
    (q : AbsoluteGaloisGroup K ⧸ (galoisOpenNormalSubgroup K L L.val).toSubgroup) :
    galoisQuotientHom L q = quotientFixingSubgroupFieldRangeEquiv K L L.val q :=
  (rfl)

/-- On the class of `g`, `galoisQuotientHom` is restriction of `g` to `L`. -/
private theorem galoisQuotientHom_mk (g : AbsoluteGaloisGroup K) :
    galoisQuotientHom L g = AlgEquiv.restrictNormalHom L g :=
  ((galoisQuotientHom_apply L g).trans (quotientFixingSubgroupFieldRangeEquiv_mk K L L.val g)).trans
    (DFunLike.congr_fun (IntermediateField.restrictNormalHom_val L) g)

/-- Inclusion of `Lˣ` in `(Kˢ)ˣ`, as an equivalence with the units fixed by
`Gal(Kˢ/L)`. -/
private def finiteLevelCoeffEquiv :
    Additive Lˣ ≃+
      FixedPoints.addSubgroup (galoisOpenNormalSubgroup K L L.val).toSubgroup (UnitsCoeff K) :=
  embeddedUnitsEquivInvariants K L L.val

/-- Inclusion of `Lˣ` in `(Kˢ)ˣ`, viewed as an additive map into the invariants fixed by
`Gal(Kˢ/L)`. -/
private def finiteLevelCoeffHom :
    Additive Lˣ →+
      FixedPoints.addSubgroup (galoisOpenNormalSubgroup K L L.val).toSubgroup (UnitsCoeff K) :=
  (finiteLevelCoeffEquiv L).toAddMonoidHom

/-- `finiteLevelCoeffHom` is the underlying map of `finiteLevelCoeffEquiv`. -/
private theorem finiteLevelCoeffHom_apply (b : Additive Lˣ) :
    finiteLevelCoeffHom L b = finiteLevelCoeffEquiv L b :=
  (rfl)

/-- `finiteLevelCoeffHom` embeds a unit of `L` into `(Kˢ)ˣ`. -/
private theorem coe_finiteLevelCoeffHom (b : Additive Lˣ) :
    (finiteLevelCoeffHom L b : UnitsCoeff K) =
      Additive.ofMul (Units.map L.val.toRingHom.toMonoidHom b.toMul) :=
  Additive.toMul.injective <| by
    have h := toMul_coe_embeddedUnitsInvariants K L L.val b.toMul
    rw [← embeddedUnitsEquivInvariants_apply] at h
    exact h

/-- The quotient action and the inclusion of invariant units form a compatible pair. -/
private theorem finiteLevelCoeffHom_smul
    (q : AbsoluteGaloisGroup K ⧸ (galoisOpenNormalSubgroup K L L.val).toSubgroup)
    (b : Additive Lˣ) :
    finiteLevelCoeffHom L (galoisQuotientHom L q • b) = q • finiteLevelCoeffHom L b := by
  induction q using QuotientGroup.induction_on with
  | _ g =>
      rw [galoisQuotientHom_mk, ← IntermediateField.restrictNormalHom_val]
      apply Subtype.ext
      rw [coe_quotient_smul_fixedPoints_addSubgroup]
      exact embeddedUnitsEquivInvariants_restrictNormalHom_smul K L L.val g b

/-- The inverse quotient identification, bundled as a continuous homomorphism. -/
private def galoisQuotientHomInv :
    (L ≃ₐ[K] L) →ₜ* AbsoluteGaloisGroup K ⧸
      (galoisOpenNormalSubgroup K L L.val).toSubgroup :=
  { (quotientFixingSubgroupFieldRangeEquiv K L L.val).symm.toMonoidHom with
    continuous_toFun := continuous_of_discreteTopology }

/-- `galoisQuotientHomInv` is the inverse quotient identification. -/
private theorem galoisQuotientHomInv_apply (g : L ≃ₐ[K] L) :
    galoisQuotientHomInv L g = (quotientFixingSubgroupFieldRangeEquiv K L L.val).symm g :=
  (rfl)

/-- The inverse quotient identification cancels the forward identification. -/
private theorem galoisQuotientHomInv_apply_quotientEquiv
    (q : AbsoluteGaloisGroup K ⧸ (galoisOpenNormalSubgroup K L L.val).toSubgroup) :
    galoisQuotientHomInv L (quotientFixingSubgroupFieldRangeEquiv K L L.val q) = q := by
  rw [galoisQuotientHomInv_apply]
  exact (quotientFixingSubgroupFieldRangeEquiv K L L.val).symm_apply_apply q

/-- The inverse coefficient identification is equivariant along the inverse quotient
identification. -/
private theorem finiteLevelCoeffEquiv_symm_smul
    (g : L ≃ₐ[K] L)
    (b : FixedPoints.addSubgroup
      (galoisOpenNormalSubgroup K L L.val).toSubgroup (UnitsCoeff K)) :
    (finiteLevelCoeffEquiv L).symm
        (galoisQuotientHomInv L g • b) =
      g • (finiteLevelCoeffEquiv L).symm b := by
  let φ : AbsoluteGaloisGroup K ⧸ (galoisOpenNormalSubgroup K L L.val).toSubgroup ≃*
      (L ≃ₐ[K] L) :=
    quotientFixingSubgroupFieldRangeEquiv K L L.val
  rw [galoisQuotientHomInv_apply]
  refine AddEquiv.symm_map_smul_of_map_mulEquiv_smul (finiteLevelCoeffEquiv L) φ
    (fun q m ↦ ?_) g b
  have hφ : φ q = galoisQuotientHom L q := (galoisQuotientHom_apply L q).symm
  rw [hφ, ← finiteLevelCoeffHom_apply, ← finiteLevelCoeffHom_apply]
  exact finiteLevelCoeffHom_smul L q m

/-- The inverse coefficient identification, followed by inclusion in the separable closure,
recovers the underlying invariant unit. -/
private theorem ofMul_unitsMap_finiteLevelCoeffEquiv_symm
    (b : FixedPoints.addSubgroup
      (galoisOpenNormalSubgroup K L L.val).toSubgroup (UnitsCoeff K)) :
    Additive.ofMul (Units.map L.val.toRingHom.toMonoidHom
        ((finiteLevelCoeffEquiv L).symm b).toMul) = (b : UnitsCoeff K) :=
  (coe_finiteLevelCoeffHom L _).symm.trans <| by
    rw [finiteLevelCoeffHom_apply, AddEquiv.apply_symm_apply]

/-- A cocycle at the finite quotient associated to `L` as a crossed-product cocycle of
`Gal(L/K)`. -/
private def ofFiniteLevelZ2
    (z : Z2 (AbsoluteGaloisGroup K ⧸
      (galoisOpenNormalSubgroup K L L.val).toSubgroup)
      (FixedPoints.addSubgroup (galoisOpenNormalSubgroup K L L.val).toSubgroup
        (UnitsCoeff K))) : TwoCocycle K L :=
  letI : TopologicalSpace (Additive Lˣ) := ⊥
  letI : DiscreteTopology (Additive Lˣ) := ⟨rfl⟩
  let z' := cocyclesMap2 _ _ _ _ (galoisQuotientHomInv L)
    (finiteLevelCoeffEquiv L).symm.toAddMonoidHom
    continuous_of_discreteTopology (finiteLevelCoeffEquiv_symm_smul L) z
  { toFun := fun g h ↦ Additive.toMul ((z' : _ → Additive Lˣ) (g, h))
    isMulCocycle₂ := fun g h j ↦ by
      apply Additive.ofMul.injective
      simpa only [ofMul_mul, ofMul_toMul, Additive.ofMul_smul] using
        (mem_Z2_iff.1 z'.2).2 g h j }

/-- The crossed-product cocycle obtained from a finite-level cocycle evaluates by pulling the
automorphisms back through the quotient identification and the coefficient through the invariant
unit identification. -/
private theorem ofFiniteLevelZ2_toFun
    (z : Z2 (AbsoluteGaloisGroup K ⧸
      (galoisOpenNormalSubgroup K L L.val).toSubgroup)
      (FixedPoints.addSubgroup (galoisOpenNormalSubgroup K L L.val).toSubgroup
        (UnitsCoeff K))) (g h : L ≃ₐ[K] L) :
    (ofFiniteLevelZ2 L z).toFun g h =
      Additive.toMul ((finiteLevelCoeffEquiv L).symm
        ((z : _ → _) (galoisQuotientHomInv L g, galoisQuotientHomInv L h))) :=
  letI : TopologicalSpace (Additive Lˣ) := ⊥
  haveI : DiscreteTopology (Additive Lˣ) := ⟨rfl⟩
  congrArg Additive.toMul <|
    cocyclesMap2_apply _ _ _ _ _ _ continuous_of_discreteTopology
      (finiteLevelCoeffEquiv_symm_smul L) z g h

/-- The cocycle at the finite quotient `G_K/G_L`, with values in the units fixed by `G_L`: the
pullback, along the compatible pair given by the quotient identification `G_K/G_L ≃ Gal(L/K)` and
the inclusion of `Lˣ` as the invariants, of `c` viewed as a cocycle of the discrete group
`Gal(L/K)` with discrete coefficients. -/
def finiteLevelZ2 (c : TwoCocycle K L) :
    Z2 (AbsoluteGaloisGroup K ⧸ (galoisOpenNormalSubgroup K L L.val).toSubgroup)
      (FixedPoints.addSubgroup (galoisOpenNormalSubgroup K L L.val).toSubgroup
        (UnitsCoeff K)) :=
  letI : TopologicalSpace (Additive Lˣ) := ⊥
  haveI : DiscreteTopology (Additive Lˣ) := ⟨rfl⟩
  cocyclesMap2 (L ≃ₐ[K] L) (Additive Lˣ) _ _ (galoisQuotientHom L) (finiteLevelCoeffHom L)
    continuous_of_discreteTopology (finiteLevelCoeffHom_smul L)
    -- as in `inflateZ2`, `IsCocycle₂ (Additive.ofMul ∘ f)` unfolds to `IsMulCocycle₂ f`
    ⟨fun p ↦ Additive.ofMul (c.toFun p.1 p.2),
      mem_Z2_iff.2 ⟨continuous_of_discreteTopology, c.isMulCocycle₂⟩⟩

/-- The finite-level cocycle evaluates by restricting the two quotient classes and embedding the
value of the original cocycle into the separable closure. -/
@[simp]
theorem finiteLevelZ2_apply (c : TwoCocycle K L)
    (q r : AbsoluteGaloisGroup K ⧸ (galoisOpenNormalSubgroup K L L.val).toSubgroup) :
    ((c.finiteLevelZ2 L).1 (q, r) : UnitsCoeff K) =
      Additive.ofMul (Units.map L.val.toRingHom.toMonoidHom
        (c.toFun (quotientFixingSubgroupFieldRangeEquiv K L L.val q)
          (quotientFixingSubgroupFieldRangeEquiv K L L.val r))) := by
  rw [finiteLevelZ2, cocyclesMap2_apply, coe_finiteLevelCoeffHom, galoisQuotientHom_apply,
    galoisQuotientHom_apply]
  simp only [toMul_ofMul]

/-- Converting a finite-level cocycle to a crossed-product cocycle and back recovers the
original finite-level cocycle. -/
private theorem finiteLevelZ2_ofFiniteLevelZ2
    (z : Z2 (AbsoluteGaloisGroup K ⧸
      (galoisOpenNormalSubgroup K L L.val).toSubgroup)
      (FixedPoints.addSubgroup (galoisOpenNormalSubgroup K L L.val).toSubgroup
        (UnitsCoeff K))) :
    (ofFiniteLevelZ2 L z).finiteLevelZ2 L = z := by
  apply Subtype.ext
  funext p
  obtain ⟨q, r⟩ := p
  apply Subtype.ext
  rw [finiteLevelZ2_apply, ofFiniteLevelZ2_toFun]
  rw [galoisQuotientHomInv_apply_quotientEquiv, galoisQuotientHomInv_apply_quotientEquiv]
  exact ofMul_unitsMap_finiteLevelCoeffEquiv_symm L ((z : _ → _) (q, r))

/-- The class of a crossed-product cocycle at the finite quotient `G_K/G_L`. -/
def finiteLevelClass (c : TwoCocycle K L) :
    H2 (AbsoluteGaloisGroup K ⧸ (galoisOpenNormalSubgroup K L L.val).toSubgroup)
      (FixedPoints.addSubgroup (galoisOpenNormalSubgroup K L L.val).toSubgroup
        (UnitsCoeff K)) :=
  H2pi _ _ (c.finiteLevelZ2 L)

/-- The representative of the finite-level cohomology class `finiteLevelClass`. -/
theorem finiteLevelClass_def (c : TwoCocycle K L) :
    c.finiteLevelClass L = H2pi _ _ (c.finiteLevelZ2 L) :=
  (rfl)

/-- Pointwise, inflating the finite-level cocycle along the quotient map recovers the directly
inflated cocycle. -/
private theorem cocyclesMap2_finiteLevelZ2_apply (c : TwoCocycle K L)
    (g h : AbsoluteGaloisGroup K) :
    (cocyclesMap2 _ _ _ _
      (Subgroup.quotientMkContinuousMonoidHom
        (galoisOpenNormalSubgroup K L L.val).toSubgroup)
      (FixedPoints.addSubgroup
        (galoisOpenNormalSubgroup K L L.val).toSubgroup (UnitsCoeff K)).subtype
      (continuous_fixedPoints_addSubgroup_subtype _ _ _)
      (galoisOpenNormalSubgroup K L L.val).toSubgroup.fixedPoints_subtype_quotientMk_smul
      (c.finiteLevelZ2 L) :
        AbsoluteGaloisGroup K × AbsoluteGaloisGroup K → UnitsCoeff K) (g, h) =
      (c.inflateZ2 L : AbsoluteGaloisGroup K × AbsoluteGaloisGroup K → UnitsCoeff K)
        (g, h) := by
  rw [cocyclesMap2_apply, AddSubgroup.subtype_apply, Subgroup.quotientMkContinuousMonoidHom_apply,
    Subgroup.quotientMkContinuousMonoidHom_apply, finiteLevelZ2_apply, ← galoisQuotientHom_apply,
    ← galoisQuotientHom_apply, galoisQuotientHom_mk, galoisQuotientHom_mk, coe_inflateZ2]
  simp only [inflate_toFun]

/-- Inflating the finite-level representative gives the cocycle obtained directly by restricting
absolute Galois automorphisms to `L`. -/
private theorem explicitInfl2_finiteLevelClass (c : TwoCocycle K L) :
    explicitInfl2 (AbsoluteGaloisGroup K) (UnitsCoeff K)
        (galoisOpenNormalSubgroup K L L.val).toSubgroup (c.finiteLevelClass L) =
      H2pi (AbsoluteGaloisGroup K) (UnitsCoeff K) (c.inflateZ2 L) := by
  rw [finiteLevelClass, QuotientAddGroup.mk'_apply, explicitInfl2_mk]
  apply congrArg (H2pi (AbsoluteGaloisGroup K) (UnitsCoeff K))
  apply Subtype.ext
  funext p
  obtain ⟨g, h⟩ := p
  exact cocyclesMap2_finiteLevelZ2_apply L c g h

end FiniteLevel

end Cocycle

/-! ### Continuous cohomology classes -/

section ContinuousClass

variable {K : Type u} [Field K]

section Finite

variable (L : IntermediateField K (SeparableClosure K)) [FiniteDimensional K L] [Normal K L]

/-- The continuous cohomology class represented by the inflation of `c`: the explicit class
`inflateH2`, read in Mathlib's `continuousCohomology`. -/
def inflateClass (c : TwoCocycle K L) :
    continuousCohomology 2
      (ofDiscreteModule ℤ (AbsoluteGaloisGroup K) (UnitsCoeff K)) :=
  explicitH2AddEquivContinuousCohomology (AbsoluteGaloisGroup K) (UnitsCoeff K) (c.inflateH2 L)

/-- The continuous class `inflateClass` is the image of the explicit class `inflateH2`. -/
theorem inflateClass_def (c : TwoCocycle K L) :
    c.inflateClass L =
      explicitH2AddEquivContinuousCohomology (AbsoluteGaloisGroup K) (UnitsCoeff K)
        (c.inflateH2 L) :=
  (rfl)

/-- **Inflation is additive**: the pointwise product of cocycles inflates to the sum of their
continuous classes. -/
@[simp]
theorem inflateClass_mul (z w : TwoCocycle K L) :
    (z * w).inflateClass L = z.inflateClass L + w.inflateClass L := by
  rw [inflateClass, inflateClass, inflateClass, inflateH2_mul, map_add]

/-- The trivial cocycle inflates to the zero class. -/
@[simp]
theorem inflateClass_one : (1 : TwoCocycle K L).inflateClass L = 0 := by
  rw [inflateClass, inflateH2_one, map_zero]

/-- Inflation turns the pointwise quotient of cocycles into the difference of their classes. -/
@[simp]
theorem inflateClass_div (z w : TwoCocycle K L) :
    (z / w).inflateClass L = z.inflateClass L - w.inflateClass L := by
  rw [inflateClass, inflateClass, inflateClass, inflateH2_div, map_sub]

/-- Cohomologous crossed-product cocycles have the same class after inflation to continuous
cohomology. -/
theorem inflateClass_eq_of_cohomologous {z w : TwoCocycle K L} (h : z.Cohomologous w) :
    z.inflateClass L = w.inflateClass L := by
  rw [inflateClass, inflateClass, inflateH2_eq_of_cohomologous L h]

/-- **The inflated crossed-product class is the finite-quotient comparison class.** More
precisely, its explicit `H²` representative is the image of the class at the quotient
`G_K/G_L` under the `L`-leg of `explicitFiniteQuotientComparison2`. -/
theorem inflateClass_eq_finiteQuotientComparison (c : TwoCocycle K L) :
    c.inflateClass L =
      explicitH2AddEquivContinuousCohomology (AbsoluteGaloisGroup K) (UnitsCoeff K)
        ((explicitFiniteQuotientComparison2 (AbsoluteGaloisGroup K) (UnitsCoeff K)).app
          (Opposite.op (galoisOpenNormalSubgroup K L L.val)) (c.finiteLevelClass L)) := by
  rw [inflateClass, inflateH2, explicitFiniteQuotientComparison2_app]
  exact congrArg (explicitH2AddEquivContinuousCohomology (AbsoluteGaloisGroup K) (UnitsCoeff K))
    (explicitInfl2_finiteLevelClass L c).symm

end Finite

section Refinement

variable {L M : IntermediateField K (SeparableClosure K)} [Normal K L] [Normal K M]
  [FiniteDimensional K L] [FiniteDimensional K M]
  (π : (M ≃ₐ[K] M) →* (L ≃ₐ[K] L)) (ι : L →ₐ[K] M) (hπι : ∀ g x, ι (π g x) = g (ι x))
  (hι : ∀ x, M.val (ι x) = L.val x)
include hι

/-- Refining the finite normal subextension on which a cocycle is defined, along a compatible pair
`(π, ι)` with `ι` compatible with the inclusions into `Kˢ`, does not change its inflated
continuous cohomology class. -/
theorem inflateClass_comap (c : TwoCocycle K L) :
    (c.comap π ι hπι).inflateClass M = c.inflateClass L := by
  rw [inflateClass, inflateClass, inflateH2_comap π ι hπι hι]

end Refinement

/-- Refining a cocycle to a larger finite normal subextension does not change its inflated
continuous class. -/
@[simp]
theorem inflateClass_refine {L M : IntermediateField K (SeparableClosure K)} [Normal K L]
    [Normal K M] [FiniteDimensional K L] [FiniteDimensional K M] (hLM : L ≤ M)
    (c : TwoCocycle K L) : (c.refine hLM).inflateClass M = c.inflateClass L :=
  inflateClass_comap _ _ _ (coe_inclusion hLM) c

end ContinuousClass

end TwoCocycle

namespace GaloisCocycle

section ExplicitClass

variable {K : Type u} [Field K]

/-- The explicit class in `H²(G_K, (Kˢ)ˣ)` obtained by inflating a bundled finite Galois
cocycle. -/
def inflateH2 (c : GaloisCocycle K) : H2 (AbsoluteGaloisGroup K) (UnitsCoeff K) :=
  c.cocycle.inflateH2 c.extension

/-- The explicit class of a bundled finite Galois cocycle is the inflated class of its cocycle. -/
@[simp]
theorem inflateH2_def (c : GaloisCocycle K) : c.inflateH2 = c.cocycle.inflateH2 c.extension :=
  (rfl)

end ExplicitClass

variable {K : Type u} [Field K]

/-- The continuous cohomology class obtained by inflating a bundled finite Galois cocycle. -/
def inflateClass (c : GaloisCocycle K) :
    continuousCohomology 2
      (ofDiscreteModule ℤ (AbsoluteGaloisGroup K) (UnitsCoeff K)) :=
  c.cocycle.inflateClass c.extension

/-- The class of a bundled finite Galois cocycle is the inflated class of its cocycle. -/
@[simp]
theorem inflateClass_def (c : GaloisCocycle K) :
    c.inflateClass = c.cocycle.inflateClass c.extension :=
  (rfl)

end GaloisCocycle


/-! ### Exhaustion by finite Galois cocycles -/

section Exhaustion

variable {K : Type u} [Field K]

/-- **Every continuous `2`-cocycle of the absolute Galois group is inflated from a finite Galois
subextension.** The equality is on cocycle representatives: no coboundary is subtracted.

The finite subextension is the fixed field of the open normal subgroup supplied by strict
finite-quotient descent. -/
theorem exists_galoisCocycle_inflateZ2
    (z : Z2 (AbsoluteGaloisGroup K) (UnitsCoeff K)) :
    ∃ c : GaloisCocycle K, c.cocycle.inflateZ2 c.extension = z := by
  obtain ⟨U, y, hy⟩ := exists_openNormalSubgroup_descendZ2 z
  obtain ⟨L, _, _, rfl⟩ := exists_galoisOpenNormalSubgroup_eq U
  let c : GaloisCocycle K :=
    { extension := L
      cocycle := TwoCocycle.ofFiniteLevelZ2 L y }
  refine ⟨c, ?_⟩
  apply Subtype.ext
  funext p
  obtain ⟨g, h⟩ := p
  have hinfl := TwoCocycle.cocyclesMap2_finiteLevelZ2_apply L c.cocycle g h
  rw [TwoCocycle.finiteLevelZ2_ofFiniteLevelZ2] at hinfl
  rw [← hinfl, cocyclesMap2_apply]
  simpa only [Subgroup.quotientMkContinuousMonoidHom_apply, AddSubgroup.coe_subtype]
    using hy g h

/-- **Every explicit degree-two class of the absolute Galois group is inflated from a finite
Galois cocycle.** -/
theorem exists_galoisCocycle_inflateH2 (x : H2 (AbsoluteGaloisGroup K) (UnitsCoeff K)) :
    ∃ c : GaloisCocycle K, c.inflateH2 = x := by
  induction x using QuotientAddGroup.induction_on with
  | _ z =>
      obtain ⟨c, hc⟩ := exists_galoisCocycle_inflateZ2 z
      exact ⟨c, by rw [GaloisCocycle.inflateH2_def, TwoCocycle.inflateH2_def, hc,
        QuotientAddGroup.mk'_apply]⟩

end Exhaustion

variable {K : Type u} [Field K]

/-- **Every continuous degree-two class of the absolute Galois group is inflated from a finite
Galois cocycle.** -/
theorem exists_galoisCocycle_inflateClass
    (x : continuousCohomology 2
      (ofDiscreteModule ℤ (AbsoluteGaloisGroup K) (UnitsCoeff K))) :
    ∃ c : GaloisCocycle K, c.inflateClass = x := by
  obtain ⟨y, rfl⟩ :=
    (explicitH2AddEquivContinuousCohomology (AbsoluteGaloisGroup K) (UnitsCoeff K)).surjective x
  obtain ⟨c, rfl⟩ := exists_galoisCocycle_inflateH2 y
  exact ⟨c, by rw [GaloisCocycle.inflateClass_def, TwoCocycle.inflateClass_def,
    GaloisCocycle.inflateH2_def]⟩

end TauCeti

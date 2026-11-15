/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.FiniteExtension
public import TauCeti.NumberTheory.ClassFieldTheory.FiniteQuotient
public import TauCeti.NumberTheory.ClassFieldTheory.Local.EulerCharacteristic.Basic
public import TauCeti.NumberTheory.ClassFieldTheory.Local.EulerCharacteristic.Shapiro
public import TauCeti.NumberTheory.LocalField.FiniteExtension.IntermediateField
public import TauCeti.RepresentationTheory.Homological.ContCohomology.ContinuousMulEquiv
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Shapiro.FiniteQuotient
public import TauCeti.RepresentationTheory.Induction.FiniteDimensional.Basic

/-!
# The local Euler characteristic of an induced module

Let `V` be an open normal subgroup of `G_K`, `C` a subgroup of the finite quotient `G_K ⧸ V`, and
`L/K` a finite extension embedded by `σ : L →ₐ[K] Kˢ` whose absolute Galois group is the preimage
of `C` in `G_K`, so that `L` is the fixed field `K_C` of `C`. For a finite `ℤ/n`-representation `B`
of `C`, read as the Galois representation `shapiroGalRep` of `L`, this file proves the Shapiro step
of the dévissage of the local Euler-characteristic formula:

```text
χ_K(Ind_C^{G_K ⧸ V} B) = χ_L(B),        φ_K(Ind_C^{G_K ⧸ V} B) = φ_L(B).
```

The first is Shapiro's lemma for inflated induced representations
(`ContinuousCohomology.indInflationShapiroIso`), read on `G_L` through the isomorphism of `G_L`
with the preimage of `C`. The second is the cardinality formula `#Ind B = #B ^ [L : K]` together
with the tower formula `[L : ℚ_p] = [L : K] [K : ℚ_p]`.

The hypothesis on `L` is met by the fixed field `shapiroField K V C` itself, embedded by
`shapiroFieldEmbedding` (`range_absoluteGaloisGroupExtend_shapiroFieldEmbedding`); the statements
are made for an abstract `L` because the local-field structure of a finite extension is data that
`L` carries.

## Main definitions

* `TauCeti.ClassFieldTheory.shapiroGalRep`: a representation of `C` read as a Galois
  representation of `L`.

## Main results

* `TauCeti.ClassFieldTheory.localEulerCharacteristic_galRepOfQuotient_ind`:
  `χ_K(Ind_C^{G_K ⧸ V} B) = χ_L(B)`.
* `TauCeti.ClassFieldTheory.localCardNorm_galRepOfQuotient_ind`:
  `φ_K(Ind_C^{G_K ⧸ V} B) = φ_L(B)`.
* `localEulerCharacteristic_eq_localCardNorm_fdGalRepOfQuotient_indFDRep_iff`:
  `χ_K = φ_K` holds for the inflation of Tau Ceti's finite-dimensional induction model
  `indFDRep B` exactly when `χ_L = φ_L` holds for `B`.
* `localEulerCharacteristic_eq_localCardNorm_fdGalRepOfQuotient_indFDRep_of_shapiroField`:
  the transport at the fixed field `shapiroField K V C`, with its finite-extension local-field
  structure. This is the form consumed by the modular-Artin reduction of `χ_K = φ_K` to
  representations induced from cyclic subgroups.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., proof of (7.3.1).
* J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., I, proof of Theorem 2.8.
-/

public noncomputable section

namespace TauCeti.ClassFieldTheory

open CategoryTheory ContCohomology

variable {K : Type} [Field K] {L : Type} [Field L] [Algebra K L] [FiniteDimensional K L]
  (σ : L →ₐ[K] SeparableClosure K)

/-! ### A representation of `C` as a Galois representation of `L` -/

variable (n : ℕ) {V : OpenNormalSubgroup (Field.absoluteGaloisGroup K)}
  {C : Subgroup (Field.absoluteGaloisGroup K ⧸ V.toSubgroup)}
  (hσ : (absoluteGaloisGroupExtend K L σ).range = C.comap (QuotientGroup.mk' V.toSubgroup))

/-- **A representation `B` of `C ≤ G_K ⧸ V` as a Galois representation of the fixed field `L` of
`C`**, when `G_L` is the preimage of `C`: `G_L` acts through `G_L ≅ π⁻¹(C) → C`, with the discrete
topology. It is the inflation `ContinuousCohomology.comapInflation` of `B` to the preimage of `C`,
read on `G_L` along `absoluteGaloisGroupExtendEquiv`. Its underlying module is identified with
that of `B` by `shapiroGalRepLinearEquiv`. -/
def shapiroGalRep (B : Rep (ZMod n) C) : GalRep n L :=
  TopRep.res ((absoluteGaloisGroupExtendEquiv K L σ hσ :
      Field.absoluteGaloisGroup L →ₜ* C.comap (QuotientGroup.mk' V.toSubgroup)) :
      Field.absoluteGaloisGroup L →* C.comap (QuotientGroup.mk' V.toSubgroup))
    (ContinuousCohomology.comapInflation V C B).obj

variable (B : Rep (ZMod n) C)

/-- The identification of the underlying module of `shapiroGalRep` with that of `B`. -/
def shapiroGalRepLinearEquiv : (shapiroGalRep σ n hσ B).V ≃ₗ[ZMod n] B.V :=
  ContinuousCohomology.comapInflationLinearEquiv B

/-- An element of `G_L` acts on `shapiroGalRep` through the class in `C` of its image in `G_K`
(`coe_absoluteGaloisGroupExtendEquiv_apply`). -/
@[simp]
theorem shapiroGalRepLinearEquiv_ρ_apply (g : Field.absoluteGaloisGroup L)
    (b : (shapiroGalRep σ n hσ B).V) :
    shapiroGalRepLinearEquiv σ n hσ B ((shapiroGalRep σ n hσ B).ρ g b) =
      B.ρ ((QuotientGroup.mk' V.toSubgroup).subgroupComap C
        (absoluteGaloisGroupExtendEquiv K L σ hσ g)) (shapiroGalRepLinearEquiv σ n hσ B b) :=
  ContinuousCohomology.comapInflationLinearEquiv_ρ_apply B _ b

/-- `shapiroGalRep` carries the discrete topology. -/
instance : DiscreteTopology (shapiroGalRep σ n hσ B).V :=
  (ContinuousCohomology.comapInflation V C B).2.discreteTopology

/-- `shapiroGalRep` of a finite representation is finite. -/
instance [Finite B] : Finite (shapiroGalRep σ n hσ B).V :=
  .of_equiv _ (shapiroGalRepLinearEquiv σ n hσ B).symm.toEquiv

/-- `shapiroGalRep` is smooth: it is the restriction of a smooth representation along a continuous
homomorphism. -/
instance : Fact (IsSmoothDiscrete (ZMod n) (shapiroGalRep σ n hσ B)) :=
  ⟨(ContinuousCohomology.comapInflation V C B).2.res
    (absoluteGaloisGroupExtendEquiv K L σ hσ).continuous_toFun⟩

/-! ### Shapiro's lemma for the two invariants -/

/-- **Shapiro's lemma for the local Euler characteristic.** For `L` the fixed field of
`C ≤ G_K ⧸ V`, the Euler characteristic over `K` of the inflation of `Ind_C^{G_K ⧸ V} B` is the
Euler characteristic over `L` of `B`: `χ_K(Ind B) = χ_L(B)`. -/
theorem localEulerCharacteristic_galRepOfQuotient_ind
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    (hn : (n : K) ≠ 0) [Finite B] :
    localEulerCharacteristic hn ((galRepOfQuotient n K V).obj (Rep.ind C.subtype B)) =
      localEulerCharacteristic
        (map_natCast (algebraMap K L) n ▸ (map_ne_zero (algebraMap K L)).2 hn)
        (shapiroGalRep σ n hσ B) := by
  have hcard (i : ℕ) :
      Nat.card (continuousCohomology i ((galRepOfQuotient n K V).obj (Rep.ind C.subtype B))) =
        Nat.card (continuousCohomology i (shapiroGalRep σ n hσ B)) :=
    (ContinuousCohomology.natCard_continuousCohomology_ind_inflation B i).trans
      (ContinuousMulEquiv.natCard_continuousCohomology_res
        (absoluteGaloisGroupExtendEquiv K L σ hσ) _ i).symm
  apply Subtype.ext
  apply Units.ext
  simp only [localEulerCharacteristic_coe, hcard]

/-- **Shapiro's lemma for the normalized order.** For `L` the fixed field of `C ≤ G_K ⧸ V`, the
invariant `φ_K(A) = ‖#A‖_K = |#A|_p ^ [K : ℚ_p]` of the inflation of `Ind_C^{G_K ⧸ V} B` is that of
`B` over `L`: `#Ind B = #B ^ [L : K]` and `[L : ℚ_p] = [K : ℚ_p] [L : K]`. -/
theorem localCardNorm_galRepOfQuotient_ind (p : ℕ) [Fact p.Prime]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [FinitePadicExtension K p]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [FinitePadicExtension L p]
    [IsScalarTower ℚ_[p] K L] [Finite B] :
    localCardNorm p ((galRepOfQuotient n K V).obj (Rep.ind C.subtype B)) =
      localCardNorm p (shapiroGalRep σ n hσ B) := by
  have hcard : Nat.card ((galRepOfQuotient n K V).obj (Rep.ind C.subtype B)).V =
      Nat.card B.V ^ Module.finrank K L := by
    rw [galRepOfQuotient_obj_V, Rep.natCard_ind,
      index_eq_finrank_of_range_absoluteGaloisGroupExtend_eq_comap hσ]
  have hcard' : Nat.card (shapiroGalRep σ n hσ B).V = Nat.card B.V :=
    Nat.card_congr (shapiroGalRepLinearEquiv σ n hσ B).toEquiv
  -- The tower formula, stated over an arbitrary base field: elaborating it at `ℚ_[p]` directly
  -- spends the instance budget on `StrongRankCondition ℚ_[p]`.
  have htower (k : Type) [Field k] [Algebra k K] [Algebra k L] [IsScalarTower k K L] :
      Module.finrank K L * Module.finrank k K = Module.finrank k L :=
    (mul_comm _ _).trans (Module.finrank_mul_finrank k K L)
  apply Subtype.ext
  apply Units.ext
  rw [localCardNorm_coe, localCardNorm_coe, hcard, hcard', Nat.cast_pow,
    IsAbsoluteValue.abv_pow (padicNorm p), ← pow_mul, htower]

/-! ### Transport of `χ = φ` across Shapiro's lemma -/

/-- **Shapiro transport of `χ = φ` for finite-dimensional induction.** For `L` the fixed field of
`C ≤ G_K ⧸ V` and a finite-dimensional `ZMod ℓ`-representation `B` of `C`, the identity
`χ_K = φ_K` holds for the inflation of `indFDRep B` exactly when `χ_L = φ_L` holds for `B`. -/
theorem localEulerCharacteristic_eq_localCardNorm_fdGalRepOfQuotient_indFDRep_iff
    (p : ℕ) [Fact p.Prime]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [FinitePadicExtension K p]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [FinitePadicExtension L p]
    [IsScalarTower ℚ_[p] K L] (ℓ : ℕ) [Fact ℓ.Prime]
    (hσ : (absoluteGaloisGroupExtend K L σ).range = C.comap (QuotientGroup.mk' V.toSubgroup))
    (B : FDRep (ZMod ℓ) C) :
    localEulerCharacteristic
        (map_natCast (algebraMap ℚ_[p] K) ℓ ▸
          (map_ne_zero (algebraMap ℚ_[p] K)).2 (Nat.cast_ne_zero.2 (NeZero.ne ℓ)))
        ((fdGalRepOfQuotient ℓ K V).obj (indFDRep B)) =
        localCardNorm p ((fdGalRepOfQuotient ℓ K V).obj (indFDRep B)) ↔
      let _ : Finite ((forget₂ (FDRep (ZMod ℓ) C) (Rep (ZMod ℓ) C)).obj B) :=
        Module.finite_of_finite (ZMod ℓ) (M := B)
      localEulerCharacteristic
          (map_natCast (algebraMap ℚ_[p] L) ℓ ▸
            (map_ne_zero (algebraMap ℚ_[p] L)).2 (Nat.cast_ne_zero.2 (NeZero.ne ℓ)))
          (shapiroGalRep σ ℓ hσ ((forget₂ (FDRep (ZMod ℓ) C) (Rep (ZMod ℓ) C)).obj B)) =
        localCardNorm p
          (shapiroGalRep σ ℓ hσ ((forget₂ (FDRep (ZMod ℓ) C) (Rep (ZMod ℓ) C)).obj B)) := by
  let _ : Finite ((forget₂ (FDRep (ZMod ℓ) C) (Rep (ZMod ℓ) C)).obj B) :=
    Module.finite_of_finite (ZMod ℓ) (M := B)
  have hℓ : (ℓ : K) ≠ 0 :=
    map_natCast (algebraMap ℚ_[p] K) ℓ ▸
      (map_ne_zero (algebraMap ℚ_[p] K)).2 (Nat.cast_ne_zero.2 (NeZero.ne ℓ))
  -- The inflation of `indFDRep B` is that of `Ind_C B` on the forgotten representation.
  let e : (fdGalRepOfQuotient ℓ K V).obj (indFDRep B) ≅
      (galRepOfQuotient ℓ K V).obj
        (Rep.ind C.subtype ((forget₂ (FDRep (ZMod ℓ) C) (Rep (ZMod ℓ) C)).obj B)) :=
    eqToIso (fdGalRepOfQuotient_obj ℓ K V _) ≪≫
      (galRepOfQuotient ℓ K V).mapIso (indFDRepForgetIso B)
  rw [localEulerCharacteristic_congr hℓ e, localCardNorm_congr p e,
    localEulerCharacteristic_galRepOfQuotient_ind σ ℓ hσ _ hℓ,
    localCardNorm_galRepOfQuotient_ind σ ℓ hσ _ p]

/-- **Shapiro transport of `χ = φ` at the canonical fixed field.** For `K/ℚ_p` finite, if
`χ = φ` holds for a finite-dimensional `ZMod ℓ`-representation `B` of `C ≤ G_K ⧸ V` read over the
fixed field `shapiroField K V C`, then it holds over `K` for the inflation of `indFDRep B`.

The fixed field carries its finite-extension valuation and topology
(`finiteIntermediateFieldValuativeRel`, `finiteIntermediateFieldTopology`) as local instances
in the hypothesis; they are not global instances, to avoid diamonds with other realizations of
the same finite extension. -/
theorem localEulerCharacteristic_eq_localCardNorm_fdGalRepOfQuotient_indFDRep_of_shapiroField
    (p : ℕ) [Fact p.Prime] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [FinitePadicExtension K p] (ℓ : ℕ) [Fact ℓ.Prime]
    (V : OpenNormalSubgroup (Field.absoluteGaloisGroup K))
    (C : Subgroup (Field.absoluteGaloisGroup K ⧸ V.toSubgroup)) (B : FDRep (ZMod ℓ) C)
    (hB :
      let _ : CharZero K := FinitePadicExtension.charZero K p
      let _ : ValuativeRel (shapiroField K V C) :=
        finiteIntermediateFieldValuativeRel K (AlgebraicClosure K) (shapiroField K V C)
      let _ : TopologicalSpace (shapiroField K V C) :=
        finiteIntermediateFieldTopology K (AlgebraicClosure K) (shapiroField K V C)
      let _ : IsNonarchimedeanLocalField (shapiroField K V C) :=
        finiteIntermediateField_isNonarchimedeanLocalField K (AlgebraicClosure K)
          (shapiroField K V C)
      let _ : ValuativeExtension K (shapiroField K V C) :=
        finiteIntermediateField_valuativeExtension K (AlgebraicClosure K) (shapiroField K V C)
      let _ : Module.Finite ℚ_[p] (shapiroField K V C) :=
        Module.Finite.trans K (shapiroField K V C)
      let _ : ValuativeExtension ℚ_[p] (shapiroField K V C) :=
        ValuativeExtension.trans ℚ_[p] K (shapiroField K V C)
      let _ : Finite ((forget₂ (FDRep (ZMod ℓ) C) (Rep (ZMod ℓ) C)).obj B) :=
        Module.finite_of_finite (ZMod ℓ) (M := B)
      localEulerCharacteristic
          (map_natCast (algebraMap ℚ_[p] (shapiroField K V C)) ℓ ▸
            (map_ne_zero (algebraMap ℚ_[p] (shapiroField K V C))).2
              (Nat.cast_ne_zero.2 (NeZero.ne ℓ)))
          (shapiroGalRep (shapiroFieldEmbedding K V C) ℓ
            (range_absoluteGaloisGroupExtend_shapiroFieldEmbedding K V C)
            ((forget₂ (FDRep (ZMod ℓ) C) (Rep (ZMod ℓ) C)).obj B)) =
        localCardNorm p
          (shapiroGalRep (shapiroFieldEmbedding K V C) ℓ
            (range_absoluteGaloisGroupExtend_shapiroFieldEmbedding K V C)
            ((forget₂ (FDRep (ZMod ℓ) C) (Rep (ZMod ℓ) C)).obj B))) :
    localEulerCharacteristic
        (map_natCast (algebraMap ℚ_[p] K) ℓ ▸
          (map_ne_zero (algebraMap ℚ_[p] K)).2 (Nat.cast_ne_zero.2 (NeZero.ne ℓ)))
        ((fdGalRepOfQuotient ℓ K V).obj (indFDRep B)) =
      localCardNorm p ((fdGalRepOfQuotient ℓ K V).obj (indFDRep B)) := by
  let _ : CharZero K := FinitePadicExtension.charZero K p
  let _ : ValuativeRel (shapiroField K V C) :=
    finiteIntermediateFieldValuativeRel K (AlgebraicClosure K) (shapiroField K V C)
  let _ : TopologicalSpace (shapiroField K V C) :=
    finiteIntermediateFieldTopology K (AlgebraicClosure K) (shapiroField K V C)
  let _ : IsNonarchimedeanLocalField (shapiroField K V C) :=
    finiteIntermediateField_isNonarchimedeanLocalField K (AlgebraicClosure K) (shapiroField K V C)
  let _ : ValuativeExtension K (shapiroField K V C) :=
    finiteIntermediateField_valuativeExtension K (AlgebraicClosure K) (shapiroField K V C)
  let _ : Module.Finite ℚ_[p] (shapiroField K V C) := Module.Finite.trans K (shapiroField K V C)
  let _ : ValuativeExtension ℚ_[p] (shapiroField K V C) :=
    ValuativeExtension.trans ℚ_[p] K (shapiroField K V C)
  exact (localEulerCharacteristic_eq_localCardNorm_fdGalRepOfQuotient_indFDRep_iff
    (shapiroFieldEmbedding K V C) p ℓ (range_absoluteGaloisGroupExtend_shapiroFieldEmbedding K V C)
    B).2 hB

end TauCeti.ClassFieldTheory

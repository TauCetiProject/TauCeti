/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import TauCeti.AlgebraicGeometry.FormalScheme.Morphism
public import TauCeti.RingTheory.Huber.Padic.Basic

/-!
# Examples and counterexamples for morphisms into `Spf A`

We exercise `TauCeti.FormalScheme.homSpfEquiv`, `TauCeti.FormalScheme.ContinuousOnAffines`,
`TauCeti.FormalScheme.sectionsTopology`, and `TauCeti.FormalScheme.Spf.homEquiv_pow` on five
concrete regimes:

1. **Ordinary schemes (`ofScheme.obj X`):** every affine open of a scheme `X` is an affine formal
   open of `ofScheme.obj X` with discrete `sectionsTopology`, and every ring homomorphism from a
   discrete ring `A` to `Γ(X, ⊤)` satisfies `ContinuousOnAffines`.
2. **Empty formal schemes (`IsEmpty X` / `ofSpf (ZMod 1)`):** when `X` is empty, every ring
   homomorphism `A →+* Γ(X, ⊤)` is vacuously continuous on affine opens and `X ⟶ ofSpf A` has a
   unique element.
3. **Evaluation and non-exponent-1 ideals of definition (`homEquiv_pow`):** on `ℤ_[p]` with
   `I = (p)` and `J = (p)²`, the identity morphism of `Spf ℤ_[p]` satisfies `(I ^ n).map id ≤ J`
   only for `n ≥ 2`, witnessing why `Spf.homEquiv_pow` requires a positive power `I ^ n` rather
   than `I.map φ ≤ J`.
4. **Singleton carrier with nondiscrete global sections (`ofSpf ℤ_[p]`):** `ofSpf ℤ_[p]` has at
   most one point, yet `(ofSpf ℤ_[p]).sectionsTopology ⊤ _` is homeomorphic to `ℤ_[p]` and hence
   not discrete.
5. **Non-continuity and absence of morphisms `Spec ℚ_[p] ⟶ Spf ℤ_[p]`:** the canonical inclusion
   `ℤ_[p] →+* Γ(Spec ℚ_[p], ⊤)` sends `p ∈ (p)` to a unit of `ℚ_[p]`, violating the residue-field
   criterion `continuousOnAffines_iff_residue`; in fact no morphism
   `ofScheme.obj (Spec (CommRingCat.of ℚ_[p])) ⟶ ofSpf ℤ_[p]` exists.
-/

public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry
open TauCeti TauCeti.FormalScheme

universe u

noncomputable section

namespace TauCeti.Examples.FormalScheme.Morphism

/-! ### 1. Ordinary schemes and discrete target rings -/

/-- Every affine open of an ordinary scheme `X` has discrete `sectionsTopology` on
`ofScheme.obj X`. -/
example (X : Scheme.{u}) (U : Opens X) (hU : IsAffineOpen U) :
    (ofScheme.obj X).sectionsTopology U (isAffineOpen_ofScheme hU) = ⊥ :=
  sectionsTopology_ofScheme hU

/-- Every ring homomorphism from a discrete ring `A` to the global sections of a formal scheme `X`
is continuous on affine opens and hence corresponds to a unique morphism `X ⟶ ofSpf A`. -/
example (X : FormalScheme.{u}) (A : Type u) [CommRing A] [TopologicalSpace A]
    [DiscreteTopology A] (φ : A →+* X.presheaf.obj (op ⊤)) :
    ∃! f : X ⟶ ofSpf A, sectionsHom f = φ := by
  have hφ : ContinuousOnAffines X A φ :=
    (continuousOnAffines_iff X A φ).mpr fun U hU ↦ by
      let _ := X.sectionsTopology U hU
      exact continuous_of_discreteTopology
  refine ⟨homOfContinuousOnAffines φ hφ, sectionsHom_homOfContinuousOnAffines φ hφ, fun f hf ↦ ?_⟩
  exact sectionsHom_injective (hf.trans (sectionsHom_homOfContinuousOnAffines φ hφ).symm)

/-! ### 2. Empty formal schemes -/

/-- Out of any empty formal scheme `X`, there is a unique morphism `X ⟶ ofSpf A` for every adic
ring `A`. -/
theorem nonempty_unique_hom_of_isEmpty (X : FormalScheme.{u}) (hX : IsEmpty X) (A : Type u)
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsAdicRing A] :
    Nonempty (Unique (X ⟶ ofSpf A)) := by
  have hsub : Subsingleton (X.presheaf.obj (op ⊤)) :=
    ⟨fun s t ↦ X.toLocallyRingedSpace.IsSheaf.section_ext fun x ↦ False.elim (hX.false x)⟩
  let φ0 : A →+* X.presheaf.obj (op ⊤) :=
    { toFun := fun _ ↦ 0
      map_one' := hsub.elim _ _
      map_mul' := fun _ _ ↦ hsub.elim _ _
      map_zero' := rfl
      map_add' := fun _ _ ↦ hsub.elim _ _ }
  obtain ⟨-, hI, -⟩ := IsAdicRing.ideal_spec A
  have h0 : ContinuousOnAffines X A φ0 :=
    (continuousOnAffines_iff_residue hI φ0).mpr fun _ _ x ↦ False.elim (hX.false x)
  exact ⟨{
    default := homOfContinuousOnAffines φ0 h0
    uniq f := sectionsHom_injective (RingHom.ext fun _ ↦ hsub.elim _ _) }⟩

section ZeroRing

/-- The discrete topology on the zero ring `ZMod 1`. -/
local instance zmodOneTopology : TopologicalSpace (ZMod 1) := ⊥
/-- Discreteness of `ZMod 1`. -/
local instance zmodOneDiscreteTopology : DiscreteTopology (ZMod 1) := ⟨rfl⟩

/-- `ofSpf (ZMod 1)` is empty and admits a unique morphism into any `ofSpf A`. -/
example (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsAdicRing A] :
    Nonempty (Unique (ofSpf (ZMod 1) ⟶ ofSpf A)) := by
  have hEmpty : IsEmpty (ofSpf (ZMod 1)) := ⟨fun x ↦ x.1.isPrime.ne_top (Subsingleton.elim _ _)⟩
  exact nonempty_unique_hom_of_isEmpty (ofSpf (ZMod 1)) hEmpty A

end ZeroRing

/-! ### 3–5. `p`-adic checks (`ℤ_[p]` and `ℚ_[p]`) -/

section Padic

variable (p : ℕ) [Fact p.Prime]

/-- `ℤ_[p]` is a complete separated adic ring of finite ideal type with ideal `(p)`. -/
local instance padicIntIsAdicRing : IsAdicRing ℤ_[p] :=
  ⟨IsLocalRing.maximalIdeal ℤ_[p],
    by rw [PadicInt.maximalIdeal_eq_span_p]; exact Submodule.fg_span_singleton _,
    Huber.PadicInt.isAdic_maximalIdeal, inferInstance⟩

/-- `sectionsHom` recovers the identity on `ofSpf ℤ_[p]`. -/
example (a : ℤ_[p]) :
    (Spf.topSectionsIso ℤ_[p]).hom (sectionsHom (𝟙 (ofSpf ℤ_[p])) a) = a :=
  topSectionsIso_hom_sectionsHom_id ℤ_[p] a

/-- On `ℤ_[p]` with ideals of definition `I = (p)` and `J = (p)²`, the identity morphism of
`Spf ℤ_[p]` satisfies `(I ^ n).map id ≤ J` for some `n > 0` (`Spf.homEquiv_pow`), while
`¬ I.map id ≤ J` because `p ∉ (p)²`. -/
theorem padicInt_homEquiv_pow_witness :
    (∃ n > 0,
        (IsLocalRing.maximalIdeal ℤ_[p] ^ n).map (Spf.homEquiv (𝟙 (Spf ℤ_[p])) : ℤ_[p] →+* ℤ_[p]) ≤
          IsLocalRing.maximalIdeal ℤ_[p] ^ 2) ∧
      ¬ (IsLocalRing.maximalIdeal ℤ_[p]).map (Spf.homEquiv (𝟙 (Spf ℤ_[p])) : ℤ_[p] →+* ℤ_[p]) ≤
          IsLocalRing.maximalIdeal ℤ_[p] ^ 2 := by
  have hI : IsAdic (IsLocalRing.maximalIdeal ℤ_[p]) := Huber.PadicInt.isAdic_maximalIdeal
  have hIfg : (IsLocalRing.maximalIdeal ℤ_[p]).FG := by
    rw [PadicInt.maximalIdeal_eq_span_p]
    exact Submodule.fg_span_singleton _
  have hJ : IsAdic (IsLocalRing.maximalIdeal ℤ_[p] ^ 2) := is_ideal_adic_pow hI two_pos
  have hpow := Spf.homEquiv_pow hI hIfg hJ (Spf.homEquiv (𝟙 (Spf ℤ_[p])) : ℤ_[p] →+* ℤ_[p])
  refine ⟨hpow.2.mp (hpow.1.mp (Spf.homEquiv (𝟙 (Spf ℤ_[p]))).2), ?_⟩
  rw [Spf.homEquiv_apply_coe, Spf.sectionsHom_id, Ideal.map_id]
  intro hle
  have hpI : (p : ℤ_[p]) ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
    rw [PadicInt.maximalIdeal_eq_span_p]
    exact Ideal.subset_span rfl
  have hpJ : (p : ℤ_[p]) ∈ Ideal.span {(p : ℤ_[p]) ^ 2} := by
    have hmem := hle hpI
    rwa [PadicInt.maximalIdeal_eq_span_p, Ideal.span_singleton_pow] at hmem
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hpJ
  have hp_ne : (p : ℤ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hone : (p : ℤ_[p]) * c = 1 := mul_left_cancel₀ hp_ne (by linear_combination -hc)
  have h1mem : (1 : ℤ_[p]) ∈ IsLocalRing.maximalIdeal ℤ_[p] :=
    hone ▸ (IsLocalRing.maximalIdeal ℤ_[p]).mul_mem_right c hpI
  exact (IsLocalRing.maximalIdeal ℤ_[p]).ne_top_iff_one.mp
    (IsLocalRing.maximalIdeal.isMaximal ℤ_[p]).ne_top h1mem

/-- `ofSpf ℤ_[p]` has at most one point, yet the intrinsic topology on its global sections is
nondiscrete. -/
theorem subsingleton_and_not_discrete_sectionsTopology_padicInt :
    Subsingleton (ofSpf ℤ_[p]) ∧
      ¬ @DiscreteTopology _
        ((ofSpf ℤ_[p]).sectionsTopology ⊤ (isAffineOpen_top_ofSpf ℤ_[p])) := by
  refine ⟨⟨fun x y ↦ Subtype.ext (PrimeSpectrum.ext ?_)⟩, ?_⟩
  · have hmax : ∀ z : ofSpf ℤ_[p], z.1.asIdeal = IsLocalRing.maximalIdeal ℤ_[p] := fun z ↦
      le_antisymm (IsLocalRing.le_maximalIdeal z.1.isPrime.ne_top)
        ((Spf.mem_carrier_iff_le (Huber.PadicInt.isAdic_maximalIdeal (p := p))).mp z.2)
    exact (hmax x).trans (hmax y).symm
  · let _ := (ofSpf ℤ_[p]).sectionsTopology ⊤ (isAffineOpen_top_ofSpf ℤ_[p])
    intro hdisc
    have hdiscZ : DiscreteTopology ℤ_[p] :=
      (isHomeomorph_topSectionsIso ℤ_[p]).homeomorph.discreteTopology_iff.mp hdisc
    have hnil : Filter.Tendsto (fun n : ℕ ↦ (p : ℤ_[p]) ^ n) Filter.atTop (nhds 0) :=
      (Huber.PadicInt.isTopologicallyNilpotent_iff_dvd (c := (p : ℤ_[p]))).mpr dvd_rfl
    rw [nhds_discrete, Filter.tendsto_pure] at hnil
    obtain ⟨n, hn⟩ := hnil.exists
    exact pow_ne_zero n (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) hn

/-- No ring homomorphism `ℤ_[p] →+* Γ(Spec ℚ_[p], ⊤)` satisfies `ContinuousOnAffines`, because
`p ∈ (p)` maps to the invertible natural cast `(p : ℚ_[p])`. -/
theorem not_continuousOnAffines_spec_padic
    (φ : ℤ_[p] →+*
      (ofScheme.obj (Spec (CommRingCat.of ℚ_[p]))).presheaf.obj (op ⊤)) :
    ¬ ContinuousOnAffines (ofScheme.obj (Spec (CommRingCat.of ℚ_[p]))) ℤ_[p] φ := by
  let S := Spec (CommRingCat.of ℚ_[p])
  let X := ofScheme.obj S
  let x : X := ⟨(⊥ : Ideal ℚ_[p]), inferInstance⟩
  let toRes : ℚ_[p] →+* X.toLocallyRingedSpace.residueField x :=
    ((Scheme.ΓSpecIso (CommRingCat.of ℚ_[p])).inv ≫ X.toLocallyRingedSpace.Γevaluation x).hom
  intro hφ
  have hp_mem : (p : ℤ_[p]) ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
    rw [PadicInt.maximalIdeal_eq_span_p]
    exact Ideal.subset_span rfl
  have hzero :=
    (continuousOnAffines_iff_residue (Huber.PadicInt.isAdic_maximalIdeal (p := p)) φ).mp
      hφ (p : ℤ_[p]) hp_mem x
  have hp_unit_Q : IsUnit (p : ℚ_[p]) :=
    isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
  have hcast : X.toLocallyRingedSpace.Γevaluation x (φ (p : ℤ_[p])) = toRes (p : ℚ_[p]) := by
    rw [map_natCast, map_natCast, map_natCast]
  rw [hcast] at hzero
  exact (hp_unit_Q.map toRes).ne_zero hzero

/-- In particular, the canonical inclusion `ℤ_[p] →+* Γ(Spec ℚ_[p], ⊤)` is not continuous on
affine formal opens. -/
example :
    ¬ ContinuousOnAffines (ofScheme.obj (Spec (CommRingCat.of ℚ_[p]))) ℤ_[p]
      ((Scheme.ΓSpecIso (CommRingCat.of ℚ_[p])).inv.hom.comp (algebraMap ℤ_[p] ℚ_[p])) :=
  not_continuousOnAffines_spec_padic p _

/-- There is no morphism of formal schemes `Spec ℚ_[p] ⟶ Spf ℤ_[p]`. -/
theorem isEmpty_hom_spec_padic_to_ofSpf_padicInt :
    IsEmpty (ofScheme.obj (Spec (CommRingCat.of ℚ_[p])) ⟶ ofSpf ℤ_[p]) :=
  ⟨fun f ↦ not_continuousOnAffines_spec_padic p (sectionsHom f) (continuousOnAffines_sectionsHom f)⟩

end Padic

end TauCeti.Examples.FormalScheme.Morphism

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.WeightSpace.CompletedGroupAlgebra
public import TauCeti.NumberTheory.Padics.WeightSpace.GeneratorChange
import TauCeti.Algebra.MonoidAlgebra.Basic
import TauCeti.Analysis.Normed.Ring.Basic
import TauCeti.RingTheory.PowerSeries.Binomial
import TauCeti.Topology.Algebra.MonoidAlgebra.PowerSeries

/-!
# Universal characters and specialisation of `ℤ_p[[ℤ_pˣ]]`

Let `p` be a prime, `q = p ^ TauCeti.padicUnitsDepth p`, `Δ = (ℤ/qℤ)ˣ`, `ω = padicUnitsSection p`,
and `γ = padicUnitsGenerator p = exp q`. The group embedding `x ↦ [x]` defines the universal weight
`TauCeti.WeightSpace.universal p`. Continuous ring homomorphisms out of `ℤ_p[[ℤ_pˣ]]` restrict to
weights (`TauCeti.WeightSpace.ofContinuousRingHom`) and are uniquely determined on group elements.

Conversely, weights integrate to continuous homomorphisms out of `ℤ_p[[ℤ_pˣ]]`:
* **Adic (`adicSpecialize`, `adicSpecializeEquiv`, `hasSum_adicSpecialize_padicUnitsCoordinate`)**
  into any complete separated linearly topologised commutative `ℤ_p`-algebra `S`.
* **Normed (`normedSpecialize`, `normedSpecializeEquiv`,
  `hasSum_normedSpecialize_padicUnitsCoordinate`)** into any complete ultrametric normed
  commutative `ℤ_p`-algebra `R` with contractive `ℤ_p`-action, via `TauCeti.padicPowerSeriesEval`.
* **Normed `ℚ_p`-algebras (`specializeRingHom`, `specializeRingHomEquiv`,
  `existsUnique_continuous_ringHom_of_norm_lt_one`,
  `hasSum_specializeRingHom_padicUnitsCoordinate`)**, avoiding `ℤ_p`-algebra diamonds, and
  adic/normed agreement (`adicSpecialize_eq_normedSpecialize`).

## References

* P. Colmez, *Fonctions d'une variable p-adique*, Astérisque 330 (2010), §I.3.
* J. Rodrigues Jacinto and C. Williams, *An introduction to p-adic L-functions*, §§3.6 and 4.
-/

public section

open Filter Topology
open scoped PowerSeries.WithPiTopology

namespace TauCeti

section LiftHelper

variable {p : ℕ} [Fact p.Prime] {B : Type*} [CommRing B] [Algebra ℤ_[p] B]
  (ε : PowerSeries ℤ_[p] →ₐ[ℤ_[p]] B) (η : (ZMod (p ^ padicUnitsDepth p))ˣ →* Bˣ)

private noncomputable def liftPS : completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ →ₐ[ℤ_[p]] B :=
  ((MonoidAlgebra.liftNCAlgHom ε ((Units.coeHom B).comp η) fun _ _ ↦ Commute.all _ _).comp
    (MonoidAlgebra.powerSeriesAlgEquiv ℤ_[p] ℤ_[p] _).symm.toAlgHom).comp
    (padicUnitsCoordinate p).symm.toAlgHom

private theorem liftPS_apply (x : completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ) :
    liftPS ε η x = MonoidAlgebra.liftNCAlgHom ε ((Units.coeHom B).comp η)
      (fun _ _ ↦ Commute.all _ _)
      ((MonoidAlgebra.powerSeriesAlgEquiv ℤ_[p] ℤ_[p] _).symm ((padicUnitsCoordinate p).symm x)) :=
  rfl

private theorem liftPS_C_single (δ : (ZMod (p ^ padicUnitsDepth p))ˣ) (a : ℤ_[p]) :
    liftPS ε η (padicUnitsCoordinate p (PowerSeries.C (MonoidAlgebra.single δ a))) =
      algebraMap ℤ_[p] B a * η δ := by
  rw [liftPS_apply, AlgEquiv.symm_apply_apply, MonoidAlgebra.powerSeriesAlgEquiv_symm_C_single]
  simp [PowerSeries.C_eq_algebraMap]

private theorem liftPS_map_singleOne (φ : PowerSeries ℤ_[p]) :
    liftPS ε η (padicUnitsCoordinate p (PowerSeries.map MonoidAlgebra.singleOneRingHom φ)) =
      ε φ := by
  simp [liftPS]

private theorem liftPS_of (x : ℤ_[p]ˣ) :
    liftPS ε η (completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ x) =
      η (padicIntUnitsEquivZModUnitsProd p x).1 *
        ε (PowerSeries.binomialSeries ℤ_[p] (padicIntUnitsEquivZModUnitsProd p x).2.toAdd) := by
  rw [← (padicUnitsCoordinate p).apply_symm_apply (completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ x),
    padicUnitsCoordinate_symm_of, ← PowerSeries.map_algHom_binomialSeries
      (MonoidAlgebra.singleOneAlgHom (R := ℤ_[p]) (A := ℤ_[p]) (M := _)),
    MonoidAlgebra.toRingHom_singleOneAlgHom, map_mul, map_mul, liftPS_C_single,
    liftPS_map_singleOne, map_one, one_mul]

variable {ε}

open scoped PadicUnitsModuleTopology in
private theorem continuous_liftPS [TopologicalSpace B] [IsTopologicalRing B] (hε : Continuous ε) :
    Continuous (liftPS ε η) :=
  (continuous_liftNCAlgHom_powerSeriesAlgEquiv_symm hε
    ((Units.coeHom B).comp η) (fun _ _ ↦ Commute.all _ _)).comp
    (continuous_padicUnitsCoordinate_symm p)
end LiftHelper

namespace WeightSpace
variable {p : ℕ} [Fact p.Prime]

section Universal

variable (p) in
/-- **The universal weight of `ℤ_pˣ`.** It sends `x ∈ ℤ_pˣ` to `[x]` in `ℤ_p[[ℤ_pˣ]]`. -/
noncomputable def universal : WeightSpace p (completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ) where
  toMonoidHom := (completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ).toHomUnits
  continuous_toFun :=
    have hf := completedGroupAlgebra.continuous_of ℤ_[p] ℤ_[p]ˣ
    Units.continuous_iff.mpr ⟨hf, (hf.comp continuous_inv).congr fun x ↦
      congrArg Units.val (map_inv (completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ).toHomUnits x)⟩

@[simp] theorem coe_universal_apply (x : ℤ_[p]ˣ) :
    (universal p x : completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ) =
      completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ x := (rfl)
theorem coe_finiteChar_universal_apply (δ : (ZMod (p ^ padicUnitsDepth p))ˣ) :
    ((universal p).finiteChar δ : completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ) =
      completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ (padicUnitsSection p δ) := by
  rw [finiteChar_apply, coe_universal_apply]
@[simp] theorem coord_universal : (universal p).coord =
    completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ (padicUnitsGenerator p) - 1 := by
  rw [coord_def, coe_universal_apply]
@[simp] theorem coordAt_universal (u : ℤ_[p]ˣ) :
    (universal p).coordAt u = completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ
      ((unitsPrincipalLogEquiv p).symm (.ofAdd (u : ℤ_[p]))) - 1 := by
  rw [coordAt_eq_principalChar_sub_one, principalChar_apply, coe_universal_apply]

section OfContinuousRingHom
variable {R : Type*} [Ring R] [TopologicalSpace R]
  (φ : completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ →+* R) (hφ : Continuous φ)

/-- Every continuous ring homomorphism out of `ℤ_p[[ℤ_pˣ]]` restricts along `universal p` to a
weight in the target ring. -/
noncomputable def ofContinuousRingHom : WeightSpace p R where
  toMonoidHom := (Units.map φ.toMonoidHom).comp (universal p).toMonoidHom
  continuous_toFun := (Continuous.units_map _ hφ).comp (universal p).continuous

@[simp] theorem coe_ofContinuousRingHom_apply (x : ℤ_[p]ˣ) :
    (ofContinuousRingHom φ hφ x : R) = φ (completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ x) := (rfl)
theorem coe_finiteChar_ofContinuousRingHom_apply (δ : (ZMod (p ^ padicUnitsDepth p))ˣ) :
    ((ofContinuousRingHom φ hφ).finiteChar δ : R) =
      φ (completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ (padicUnitsSection p δ)) := by
  rw [finiteChar_apply, coe_ofContinuousRingHom_apply]
@[simp] theorem coord_ofContinuousRingHom :
    (ofContinuousRingHom φ hφ).coord =
      φ (completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ (padicUnitsGenerator p) - 1) := by
  rw [coord_def, coe_ofContinuousRingHom_apply, map_sub, map_one]
end OfContinuousRingHom

private noncomputable def mkSpecializeEquiv {R H : Type*} [Ring R] [TopologicalSpace R]
    [FunLike H (completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ) R] [RingHomClass H _ R]
    (spec : WeightSpace p R → H) (hcont : ∀ κ, Continuous (spec κ))
    (hof : ∀ κ x, spec κ (completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ x) = κ x)
    (heq : ∀ {φ : H}, Continuous φ → ∀ κ,
      (∀ x, φ (completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ x) = κ x) → φ = spec κ) :
    WeightSpace p R ≃ {φ : H // Continuous φ} where
  toFun κ := ⟨spec κ, hcont κ⟩
  invFun φ := ofContinuousRingHom (RingHomClass.toRingHom φ.val) φ.property
  left_inv κ := by ext x; exact hof κ x
  right_inv φ := Subtype.ext <| (heq φ.property _ fun _ ↦ rfl).symm

private theorem existsUnique_of_specializeEquiv {R H : Type*} [CommRing R] [TopologicalSpace R]
    [FunLike H (completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ) R] [RingHomClass H _ R]
    (e : WeightSpace p R ≃ {φ : H // Continuous φ})
    (h_apply : ∀ (κ : WeightSpace p R) (x : ℤ_[p]ˣ),
      (e κ).val (completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ x) = κ x)
    (h_symm : ∀ (φ : {φ : H // Continuous φ}) (x : ℤ_[p]ˣ),
      ((e.symm φ) x : R) = φ.val (completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ x))
    {η : (ZMod (p ^ padicUnitsDepth p))ˣ →* Rˣ} {t : R}
    (huniq : ∃! κ : WeightSpace p R, κ.finiteChar = η ∧ κ.coord = t) :
    ∃! φ : H, Continuous φ ∧
      (∀ δ, φ (completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ (padicUnitsSection p δ)) = η δ) ∧
      φ (completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ (padicUnitsGenerator p) - 1) = t := by
  obtain ⟨κ₀, ⟨hη₀, ht₀⟩, hκ_uniq⟩ := huniq
  refine ⟨(e κ₀).val, ⟨(e κ₀).property,
    fun δ ↦ by rw [h_apply, ← finiteChar_apply, hη₀],
    by rw [map_sub, map_one, h_apply, ← coord_def, ht₀]⟩,
    fun φ ⟨hφ, hη, ht'⟩ ↦ ?_⟩
  have hκ : e.symm ⟨φ, hφ⟩ = κ₀ := hκ_uniq _
    ⟨by ext δ; simp only [finiteChar_apply, h_symm]; exact hη δ,
     by rw [coord_def, h_symm, ← map_one φ, ← map_sub φ, ht']⟩
  exact congrArg Subtype.val (e.symm_apply_eq.mp hκ)

open scoped PadicUnitsModuleTopology in
/-- No continuous ring homomorphism out of `ℤ_p[[ℤ_pˣ]]` into a semiring with a topology sends
`[γ] - 1` to an element whose powers do not tend to `0`. -/
theorem not_exists_continuous_ringHom_of_not_tendsto_pow {R : Type*} [Semiring R]
    [TopologicalSpace R] {z : R} (hz : ¬Tendsto (z ^ ·) atTop (𝓝 0)) :
    ¬∃ φ : completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ →+* R,
      Continuous φ ∧ φ (completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ (padicUnitsGenerator p) - 1) = z := by
  rintro ⟨φ, hφ, rfl⟩
  have hX : Tendsto (fun n : ℕ ↦
      (completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ (padicUnitsGenerator p) - 1) ^ n) atTop (𝓝 0) := by
    have h0 : Tendsto (fun n : ℕ ↦
        (PowerSeries.X : PowerSeries (MonoidAlgebra ℤ_[p] (ZMod (p ^ padicUnitsDepth p))ˣ)) ^ n)
        atTop (𝓝 0) :=
      PowerSeries.WithPiTopology.isTopologicallyNilpotent_of_constantCoeff_zero
        PowerSeries.constantCoeff_X
    simpa only [Function.comp_def, map_pow, padicUnitsCoordinate_X] using
      ((continuous_padicUnitsCoordinate p).tendsto' 0 0 (map_zero _)).comp h0
  exact hz <| by
    simpa only [Function.comp_def, map_pow] using (hφ.tendsto' 0 0 (map_zero φ)).comp hX

/-- No continuous ring homomorphism out of `ℤ_p[[ℤ_pˣ]]` into a seminormed ring with
multiplicative norm sends `[γ] - 1` to an element of norm at least `1`. -/
theorem not_exists_continuous_ringHom_of_one_le_norm {K : Type*} [SeminormedRing K]
    [NormMulClass K] {z : K} (hz : 1 ≤ ‖z‖) :
    ¬∃ φ : completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ →+* K,
      Continuous φ ∧ φ (completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ (padicUnitsGenerator p) - 1) = z :=
  not_exists_continuous_ringHom_of_not_tendsto_pow fun h ↦
    hz.not_gt (tendsto_pow_atTop_nhds_zero_iff_norm_lt_one.mp h)
end Universal

/-! ### Adic specialisation into complete linearly topologised `ℤ_p`-algebras -/

section Adic
variable {S : Type*} [CommRing S] [UniformSpace S] [IsUniformAddGroup S] [IsTopologicalRing S]
  [IsLinearTopology S S] [CompleteSpace S] [T2Space S] [Algebra ℤ_[p] S] [ContinuousSMul ℤ_[p] S]

/-- **Adic specialisation of `ℤ_p[[ℤ_pˣ]]` at a weight** in a complete separated linearly
topologised commutative `ℤ_p`-algebra `S`. -/
noncomputable def adicSpecialize (κ : WeightSpace p S) :
    completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ →ₐ[ℤ_[p]] S :=
  liftPS (PowerSeries.aeval κ.hasEval_coord) κ.finiteChar

theorem continuous_adicSpecialize (κ : WeightSpace p S) : Continuous κ.adicSpecialize :=
  continuous_liftPS κ.finiteChar (PowerSeries.continuous_aeval κ.hasEval_coord)
@[simp] theorem adicSpecialize_of (κ : WeightSpace p S) (x : ℤ_[p]ˣ) :
    κ.adicSpecialize (completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ x) = κ x := by
  rw [adicSpecialize, liftPS_of, ← κ.apply_eq_finiteChar_mul_aeval_binomialSeries]
@[simp] theorem adicSpecialize_coord (κ : WeightSpace p S) :
    κ.adicSpecialize (completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ (padicUnitsGenerator p) - 1) =
      κ.coord := by rw [map_sub, map_one, adicSpecialize_of, coord_def]
@[simp] theorem adicSpecialize_padicUnitsCoordinate_map_singleOneRingHom (κ : WeightSpace p S)
    (φ : PowerSeries ℤ_[p]) :
    κ.adicSpecialize (padicUnitsCoordinate p (PowerSeries.map MonoidAlgebra.singleOneRingHom φ)) =
      PowerSeries.aeval κ.hasEval_coord φ := liftPS_map_singleOne _ _ φ

/-- **Power-series expansion of adic specialisation.** Specialising `F = ∑ n, c_n X^n` at `κ` is
the convergent series `∑ n, κ_Δ(c_n) · T_κ ^ n`. -/
theorem hasSum_adicSpecialize_padicUnitsCoordinate (κ : WeightSpace p S)
    (F : PowerSeries (MonoidAlgebra ℤ_[p] (ZMod (p ^ padicUnitsDepth p))ˣ)) :
    HasSum (fun n : ℕ ↦ MonoidAlgebra.lift ℤ_[p] S (ZMod (p ^ padicUnitsDepth p))ˣ
        ((Units.coeHom S).comp κ.finiteChar) (F.coeff n) * κ.coord ^ n)
      (κ.adicSpecialize (padicUnitsCoordinate p F)) := by
  simpa only [adicSpecialize, liftPS, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    AlgEquiv.symm_apply_apply] using
    hasSum_liftNCAlgHom_powerSeriesAlgEquiv_symm (PowerSeries.hasSum_aeval κ.hasEval_coord)
      ((Units.coeHom S).comp κ.finiteChar) (fun _ _ ↦ Commute.all _ _) (fun _ ↦ Commute.all _ _) F
theorem adicSpecialize_padicUnitsCoordinate_eq_tsum (κ : WeightSpace p S)
    (F : PowerSeries (MonoidAlgebra ℤ_[p] (ZMod (p ^ padicUnitsDepth p))ˣ)) :
    κ.adicSpecialize (padicUnitsCoordinate p F) = ∑' n : ℕ,
      MonoidAlgebra.lift ℤ_[p] S (ZMod (p ^ padicUnitsDepth p))ˣ
        ((Units.coeHom S).comp κ.finiteChar) (F.coeff n) * κ.coord ^ n :=
  (κ.hasSum_adicSpecialize_padicUnitsCoordinate F).tsum_eq.symm
@[simp] theorem ofContinuousRingHom_adicSpecialize (κ : WeightSpace p S) :
    ofContinuousRingHom (κ.adicSpecialize : completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ →+* S)
      κ.continuous_adicSpecialize = κ := by ext x; exact κ.adicSpecialize_of x

/-- Any continuous `ℤ_p`-algebra homomorphism agreeing with `κ` on `ℤ_pˣ` is `κ.adicSpecialize`. -/
theorem eq_adicSpecialize_of_continuous {φ : completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ →ₐ[ℤ_[p]] S}
    (hφ : Continuous φ) (κ : WeightSpace p S)
    (h : ∀ x : ℤ_[p]ˣ, φ (completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ x) = κ x) :
    φ = κ.adicSpecialize :=
  completedGroupAlgebra.algHom_ext_of_continuous hφ κ.continuous_adicSpecialize fun x ↦
    (h x).trans (κ.adicSpecialize_of x).symm

/-- **The adic universal property of `ℤ_p[[ℤ_pˣ]]`.** Weights in `S` correspond bijectively to
continuous `ℤ_p`-algebra homomorphisms `ℤ_p[[ℤ_pˣ]] →ₐ[ℤ_p] S`. -/
noncomputable def adicSpecializeEquiv :
    WeightSpace p S ≃ {φ : completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ →ₐ[ℤ_[p]] S // Continuous φ} :=
  mkSpecializeEquiv adicSpecialize continuous_adicSpecialize adicSpecialize_of
    eq_adicSpecialize_of_continuous

@[simp] theorem adicSpecializeEquiv_apply (κ : WeightSpace p S) :
    (adicSpecializeEquiv κ : completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ →ₐ[ℤ_[p]] S) =
      κ.adicSpecialize := (rfl)
@[simp] theorem adicSpecializeEquiv_symm_apply
    (φ : {φ : completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ →ₐ[ℤ_[p]] S // Continuous φ}) :
    adicSpecializeEquiv.symm φ =
      ofContinuousRingHom (φ.val : completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ →+* S) φ.property := (rfl)

/-- Every `η : Δ →* Sˣ` and evaluable `z ∈ S` determine a unique continuous `ℤ_p`-algebra
homomorphism `ℤ_p[[ℤ_pˣ]] →ₐ[ℤ_p] S` sending `[ω(δ)] ↦ η(δ)` and `[γ] - 1 ↦ z`. -/
theorem existsUnique_continuous_algHom_of_hasEval (η : (ZMod (p ^ padicUnitsDepth p))ˣ →* Sˣ)
    {z : S} (hz : PowerSeries.HasEval z) :
    ∃! φ : completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ →ₐ[ℤ_[p]] S, Continuous φ ∧
      (∀ δ, φ (completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ (padicUnitsSection p δ)) = η δ) ∧
      φ (completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ (padicUnitsGenerator p) - 1) = z :=
  existsUnique_of_specializeEquiv adicSpecializeEquiv (fun κ x ↦ κ.adicSpecialize_of x)
    (fun _ _ ↦ rfl) (existsUnique_character_of_hasEval η hz)

@[simp] theorem adicSpecialize_universal :
    (universal p).adicSpecialize = AlgHom.id ℤ_[p] (completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ) :=
  (eq_adicSpecialize_of_continuous (φ := AlgHom.id ℤ_[p] _) continuous_id (universal p)
    fun x ↦ (coe_universal_apply x).symm).symm
end Adic

/-! ### Normed specialisation into complete ultrametric normed `ℤ_p`-algebras -/

section Normed
variable {R : Type*} [NormedCommRing R] [Algebra ℤ_[p] R] [IsBoundedSMul ℤ_[p] R]
  [IsUltrametricDist R] [CompleteSpace R]

/-- **Normed specialisation of `ℤ_p[[ℤ_pˣ]]` at a weight** in a complete ultrametric normed
commutative `ℤ_p`-algebra `R` with contractive scalar action. -/
noncomputable def normedSpecialize (κ : WeightSpace p R) :
    completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ →ₐ[ℤ_[p]] R :=
  liftPS (padicPowerSeriesEval p κ.tendsto_coord_pow) κ.finiteChar

theorem continuous_normedSpecialize (κ : WeightSpace p R) : Continuous κ.normedSpecialize :=
  continuous_liftPS κ.finiteChar (continuous_padicPowerSeriesEval p κ.tendsto_coord_pow)
@[simp] theorem normedSpecialize_of (κ : WeightSpace p R) (x : ℤ_[p]ˣ) :
    κ.normedSpecialize (completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ x) = κ x := by
  rw [normedSpecialize, liftPS_of, padicPowerSeriesEval_binomialSeries,
    ← κ.principalChar_eq_addChar_of_value_at_one, ← κ.apply_eq_finiteChar_mul_principalChar]
@[simp] theorem normedSpecialize_coord (κ : WeightSpace p R) :
    κ.normedSpecialize (completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ (padicUnitsGenerator p) - 1) =
      κ.coord := by rw [map_sub, map_one, normedSpecialize_of, coord_def]
@[simp] theorem normedSpecialize_padicUnitsCoordinate_map_singleOneRingHom (κ : WeightSpace p R)
    (φ : PowerSeries ℤ_[p]) :
    κ.normedSpecialize (padicUnitsCoordinate p (PowerSeries.map MonoidAlgebra.singleOneRingHom φ)) =
      padicPowerSeriesEval p κ.tendsto_coord_pow φ := liftPS_map_singleOne _ _ φ

/-- `κ.normedSpecialize` sends `[γ⁻¹]` to a multiplicative inverse of `1 + κ.coord` in `R`. -/
theorem normedSpecialize_of_padicUnitsGenerator_inv_mul_one_add_coord (κ : WeightSpace p R) :
    κ.normedSpecialize (completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ (padicUnitsGenerator p)⁻¹) *
        (1 + κ.coord) = 1 := by
  rw [normedSpecialize_of, coord_def, add_sub_cancel, ← Units.val_mul, ← map_mul,
    inv_mul_cancel, map_one, Units.val_one]

/-- **Power-series expansion of normed specialisation.** Specialising `F = ∑ n, c_n X^n` at `κ` is
the convergent series `∑ n, κ_Δ(c_n) · T_κ ^ n`. -/
theorem hasSum_normedSpecialize_padicUnitsCoordinate (κ : WeightSpace p R)
    (F : PowerSeries (MonoidAlgebra ℤ_[p] (ZMod (p ^ padicUnitsDepth p))ˣ)) :
    HasSum (fun n : ℕ ↦ MonoidAlgebra.lift ℤ_[p] R (ZMod (p ^ padicUnitsDepth p))ˣ
        ((Units.coeHom R).comp κ.finiteChar) (F.coeff n) * κ.coord ^ n)
      (κ.normedSpecialize (padicUnitsCoordinate p F)) := by
  simpa only [normedSpecialize, liftPS, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    AlgEquiv.symm_apply_apply] using
    hasSum_liftNCAlgHom_powerSeriesAlgEquiv_symm (hasSum_padicPowerSeriesEval p κ.tendsto_coord_pow)
      ((Units.coeHom R).comp κ.finiteChar) (fun _ _ ↦ Commute.all _ _) (fun _ ↦ Commute.all _ _) F
theorem normedSpecialize_padicUnitsCoordinate_eq_tsum (κ : WeightSpace p R)
    (F : PowerSeries (MonoidAlgebra ℤ_[p] (ZMod (p ^ padicUnitsDepth p))ˣ)) :
    κ.normedSpecialize (padicUnitsCoordinate p F) = ∑' n : ℕ,
      MonoidAlgebra.lift ℤ_[p] R (ZMod (p ^ padicUnitsDepth p))ˣ
        ((Units.coeHom R).comp κ.finiteChar) (F.coeff n) * κ.coord ^ n :=
  (κ.hasSum_normedSpecialize_padicUnitsCoordinate F).tsum_eq.symm
@[simp] theorem ofContinuousRingHom_normedSpecialize (κ : WeightSpace p R) :
    ofContinuousRingHom (κ.normedSpecialize : completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ →+* R)
      κ.continuous_normedSpecialize = κ := by ext x; exact κ.normedSpecialize_of x

/-- Any continuous `ℤ_p`-algebra homomorphism agreeing with `κ` on `ℤ_pˣ` is
`κ.normedSpecialize`. -/
theorem eq_normedSpecialize_of_continuous {φ : completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ →ₐ[ℤ_[p]] R}
    (hφ : Continuous φ) (κ : WeightSpace p R)
    (h : ∀ x : ℤ_[p]ˣ, φ (completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ x) = κ x) :
    φ = κ.normedSpecialize :=
  completedGroupAlgebra.algHom_ext_of_continuous hφ κ.continuous_normedSpecialize fun x ↦
    (h x).trans (κ.normedSpecialize_of x).symm

/-- **The normed universal property of `ℤ_p[[ℤ_pˣ]]`.** Weights in `R` correspond bijectively to
continuous `ℤ_p`-algebra homomorphisms `ℤ_p[[ℤ_pˣ]] →ₐ[ℤ_p] R`. -/
noncomputable def normedSpecializeEquiv :
    WeightSpace p R ≃ {φ : completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ →ₐ[ℤ_[p]] R // Continuous φ} :=
  mkSpecializeEquiv normedSpecialize continuous_normedSpecialize normedSpecialize_of
    eq_normedSpecialize_of_continuous

@[simp] theorem normedSpecializeEquiv_apply (κ : WeightSpace p R) :
    (normedSpecializeEquiv κ : completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ →ₐ[ℤ_[p]] R) =
      κ.normedSpecialize := (rfl)
@[simp] theorem normedSpecializeEquiv_symm_apply
    (φ : {φ : completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ →ₐ[ℤ_[p]] R // Continuous φ}) :
    normedSpecializeEquiv.symm φ =
      ofContinuousRingHom (φ.val : completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ →+* R) φ.property := (rfl)

/-- Every `η : Δ →* Rˣ` and topologically nilpotent `t ∈ R` determine a unique continuous
`ℤ_p`-algebra homomorphism `ℤ_p[[ℤ_pˣ]] →ₐ[ℤ_p] R` sending `[ω(δ)] ↦ η(δ)` and `[γ] - 1 ↦ t`. -/
theorem existsUnique_continuous_algHom_of_tendsto_pow
    (η : (ZMod (p ^ padicUnitsDepth p))ˣ →* Rˣ) {t : R} (ht : Tendsto (t ^ ·) atTop (𝓝 0)) :
    ∃! φ : completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ →ₐ[ℤ_[p]] R, Continuous φ ∧
      (∀ δ, φ (completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ (padicUnitsSection p δ)) = η δ) ∧
      φ (completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ (padicUnitsGenerator p) - 1) = t :=
  existsUnique_of_specializeEquiv normedSpecializeEquiv (fun κ x ↦ κ.normedSpecialize_of x)
    (fun _ _ ↦ rfl) (existsUnique_character_of_tendsto_pow η ht)

/-- When `‖t‖ < 1`, `η` and `t` determine a unique continuous `ℤ_p`-algebra homomorphism out of
`ℤ_p[[ℤ_pˣ]]`. -/
theorem existsUnique_continuous_algHom_of_norm_lt_one
    (η : (ZMod (p ^ padicUnitsDepth p))ˣ →* Rˣ) {t : R} (ht : ‖t‖ < 1) :
    ∃! φ : completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ →ₐ[ℤ_[p]] R, Continuous φ ∧
      (∀ δ, φ (completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ (padicUnitsSection p δ)) = η δ) ∧
      φ (completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ (padicUnitsGenerator p) - 1) = t :=
  existsUnique_continuous_algHom_of_tendsto_pow η (tendsto_pow_atTop_nhds_zero_of_norm_lt_one ht)

theorem normedSpecialize_padicUnitsCoordinateAt_X (κ : WeightSpace p R) (u : ℤ_[p]ˣ) :
    κ.normedSpecialize (padicUnitsCoordinateAt p u PowerSeries.X) = κ.coordAt u := by
  rw [padicUnitsCoordinateAt_X, map_sub, map_one, normedSpecialize_of,
    κ.coordAt_eq_principalChar_sub_one, principalChar_apply]

open scoped PadicUnitsModuleTopology in
/-- Specialising along the generator-change coordinate `padicUnitsCoordinateAt p u` factors
through `padicPowerSeriesEval` at `κ.coordAt u` and `κ.finiteChar`. -/
theorem normedSpecialize_comp_padicUnitsCoordinateAt (κ : WeightSpace p R) (u : ℤ_[p]ˣ) :
    κ.normedSpecialize.comp (padicUnitsCoordinateAt p u).toAlgHom =
      (MonoidAlgebra.liftNCAlgHom (padicPowerSeriesEval p (κ.tendsto_coordAt_pow u))
        ((Units.coeHom R).comp κ.finiteChar) fun _ _ ↦ Commute.all _ _).comp
        (MonoidAlgebra.powerSeriesAlgEquiv ℤ_[p] ℤ_[p]
          (ZMod (p ^ padicUnitsDepth p))ˣ).symm.toAlgHom := by
  let Δ := (ZMod (p ^ padicUnitsDepth p))ˣ
  let L₁ := κ.normedSpecialize.comp (padicUnitsCoordinateAt p u).toAlgHom
  let L₂ := (MonoidAlgebra.liftNCAlgHom (padicPowerSeriesEval p (κ.tendsto_coordAt_pow u))
    ((Units.coeHom R).comp κ.finiteChar) fun _ _ ↦ Commute.all _ _).comp
    (MonoidAlgebra.powerSeriesAlgEquiv ℤ_[p] ℤ_[p] Δ).symm.toAlgHom
  have hpoly : L₁.toRingHom.comp Polynomial.coeToPowerSeries.ringHom =
      L₂.toRingHom.comp Polynomial.coeToPowerSeries.ringHom := by
    refine Polynomial.ringHom_ext' ?_ ?_
    · refine MonoidAlgebra.ringHom_ext (fun a ↦ ?_) (fun δ ↦ ?_)
      · simp [L₁, L₂, Δ, AlgHom.commutes]
      · simp [L₁, L₂, Δ, ← finiteChar_apply]
    · simp [L₁, L₂, Δ, coordAt_eq_principalChar_sub_one, principalChar_apply]
  exact AlgHom.coe_fn_injective <|
    (PowerSeries.WithPiTopology.denseRange_toPowerSeries (MonoidAlgebra ℤ_[p] Δ)).equalizer
      (κ.continuous_normedSpecialize.comp (continuous_padicUnitsCoordinateAt p u))
      (continuous_liftNCAlgHom_powerSeriesAlgEquiv_symm
        (continuous_padicPowerSeriesEval p (κ.tendsto_coordAt_pow u))
        ((Units.coeHom R).comp κ.finiteChar) (fun _ _ ↦ Commute.all _ _))
      (funext fun P ↦ RingHom.congr_fun hpoly P)

/-- **Generator-change series expansion.** Specialising `padicUnitsCoordinateAt p u F` at `κ`
evaluates the finite-part coefficients against powers of `κ.coordAt u`. -/
theorem hasSum_normedSpecialize_padicUnitsCoordinateAt (κ : WeightSpace p R) (u : ℤ_[p]ˣ)
    (F : PowerSeries (MonoidAlgebra ℤ_[p] (ZMod (p ^ padicUnitsDepth p))ˣ)) :
    HasSum (fun n : ℕ ↦ MonoidAlgebra.lift ℤ_[p] R (ZMod (p ^ padicUnitsDepth p))ˣ
        ((Units.coeHom R).comp κ.finiteChar) (F.coeff n) * κ.coordAt u ^ n)
      (κ.normedSpecialize (padicUnitsCoordinateAt p u F)) := by
  rw [← AlgEquiv.coe_toAlgHom (padicUnitsCoordinateAt p u), ← AlgHom.comp_apply,
    normedSpecialize_comp_padicUnitsCoordinateAt, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom]
  exact hasSum_liftNCAlgHom_powerSeriesAlgEquiv_symm
    (hasSum_padicPowerSeriesEval p (κ.tendsto_coordAt_pow u))
    ((Units.coeHom R).comp κ.finiteChar) (fun _ _ ↦ Commute.all _ _) (fun _ ↦ Commute.all _ _) F

/-- Specialising at the trivial weight `1` augments the constant term of `F` and kills `X`. -/
theorem normedSpecialize_one_padicUnitsCoordinate
    (F : PowerSeries (MonoidAlgebra ℤ_[p] (ZMod (p ^ padicUnitsDepth p))ˣ)) :
    (1 : WeightSpace p R).normedSpecialize (padicUnitsCoordinate p F) =
      MonoidAlgebra.lift ℤ_[p] R (ZMod (p ^ padicUnitsDepth p))ˣ 1
        (PowerSeries.constantCoeff F) := by
  rw [normedSpecialize_padicUnitsCoordinate_eq_tsum, coord_one,
    tsum_eq_single 0 fun n hn ↦ by simp [zero_pow hn]]
  have h1 : ((Units.coeHom R).comp (1 : WeightSpace p R).finiteChar) = 1 := by ext; simp
  rw [h1, pow_zero, mul_one, PowerSeries.coeff_zero_eq_constantCoeff]

end Normed

/-! ### Adic and normed agreement -/

section AdicNormed
variable {S : Type*} [NormedCommRing S] [IsUltrametricDist S] [CompleteSpace S]
  [IsLinearTopology S S] [Algebra ℤ_[p] S] [IsBoundedSMul ℤ_[p] S]

/-- **Agreement of adic and normed specialisations** when `S` carries both structures. -/
theorem adicSpecialize_eq_normedSpecialize (κ : WeightSpace p S) :
    κ.adicSpecialize = κ.normedSpecialize :=
  completedGroupAlgebra.algHom_ext_of_continuous κ.continuous_adicSpecialize
    κ.continuous_normedSpecialize
    fun x ↦ (κ.adicSpecialize_of x).trans (κ.normedSpecialize_of x).symm
end AdicNormed

/-! ### Specialisation for ultrametric normed `ℚ_p`-algebras -/

section NormedPadicAlgebra
variable {K : Type*} [NormedCommRing K] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K]
  [CompleteSpace K]

/-- **Specialisation of `ℤ_p[[ℤ_pˣ]]` at a weight in a complete ultrametric normed commutative
`ℚ_p`-algebra `K`**, bundled as a ring homomorphism without requiring `Algebra ℤ_[p] K`. -/
noncomputable def specializeRingHom (κ : WeightSpace p K) :
    completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ →+* K :=
  letI := padicIntAlgebra p K; haveI := isBoundedSMul_padicIntAlgebra p K
  κ.normedSpecialize.toRingHom

theorem continuous_specializeRingHom (κ : WeightSpace p K) : Continuous κ.specializeRingHom :=
  letI := padicIntAlgebra p K; haveI := isBoundedSMul_padicIntAlgebra p K
  κ.continuous_normedSpecialize
@[simp] theorem specializeRingHom_of (κ : WeightSpace p K) (x : ℤ_[p]ˣ) :
    κ.specializeRingHom (completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ x) = κ x :=
  letI := padicIntAlgebra p K; haveI := isBoundedSMul_padicIntAlgebra p K; κ.normedSpecialize_of x
@[simp] theorem specializeRingHom_algebraMap (κ : WeightSpace p K) (a : ℤ_[p]) :
    κ.specializeRingHom (algebraMap ℤ_[p] (completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ) a) =
      padicIntAlgebraMap p K a := by
  let _ := padicIntAlgebra p K; have _ := isBoundedSMul_padicIntAlgebra p K
  simp [specializeRingHom, AlgHom.commutes, algebraMap_padicIntAlgebra_apply,
    padicIntAlgebraMap_apply]
@[simp] theorem specializeRingHom_coord (κ : WeightSpace p K) :
    κ.specializeRingHom (completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ (padicUnitsGenerator p) - 1) =
      κ.coord := by rw [map_sub, map_one, specializeRingHom_of, coord_def]

/-- **Power-series expansion of `specializeRingHom`.** Specialising `F = ∑ n, c_n X^n` at `κ` is
the convergent series evaluating `c_n` via `padicIntAlgebraMap p K` and `κ.finiteChar` times
`κ.coord ^ n`. -/
theorem hasSum_specializeRingHom_padicUnitsCoordinate (κ : WeightSpace p K)
    (F : PowerSeries (MonoidAlgebra ℤ_[p] (ZMod (p ^ padicUnitsDepth p))ˣ)) :
    HasSum (fun n : ℕ ↦ MonoidAlgebra.liftNCRingHom (padicIntAlgebraMap p K)
        ((Units.coeHom K).comp κ.finiteChar) (fun _ _ ↦ Commute.all _ _) (F.coeff n) * κ.coord ^ n)
      (κ.specializeRingHom (padicUnitsCoordinate p F)) := by
  let _ := padicIntAlgebra p K; have _ := isBoundedSMul_padicIntAlgebra p K
  refine (κ.hasSum_normedSpecialize_padicUnitsCoordinate F).congr_fun fun n ↦ congrArg (· * _) ?_
  induction F.coeff n using MonoidAlgebra.induction_linear with
  | zero => simp
  | add _ _ hx hy => simp [map_add, hx, hy]
  | single _ _ =>
    simp [Algebra.smul_def, algebraMap_padicIntAlgebra_apply, padicIntAlgebraMap_apply]
@[simp] theorem ofContinuousRingHom_specializeRingHom (κ : WeightSpace p K) :
    ofContinuousRingHom κ.specializeRingHom κ.continuous_specializeRingHom = κ := by
  ext x; exact κ.specializeRingHom_of x

/-- Any continuous ring homomorphism agreeing with `κ` on `ℤ_pˣ` equals `κ.specializeRingHom`. -/
theorem eq_specializeRingHom_of_continuous {φ : completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ →+* K}
    (hφ : Continuous φ) (κ : WeightSpace p K)
    (h : ∀ x : ℤ_[p]ˣ, φ (completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ x) = κ x) :
    φ = κ.specializeRingHom :=
  completedGroupAlgebra.ringHom_ext_of_continuous_padicInt hφ κ.continuous_specializeRingHom
    fun x ↦ (h x).trans (κ.specializeRingHom_of x).symm

/-- **The normed `ℚ_p`-algebra universal property of `ℤ_p[[ℤ_pˣ]]`.** Weights in `K` correspond
bijectively to continuous ring homomorphisms `ℤ_p[[ℤ_pˣ]] →+* K`. -/
noncomputable def specializeRingHomEquiv :
    WeightSpace p K ≃ {φ : completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ →+* K // Continuous φ} :=
  mkSpecializeEquiv specializeRingHom continuous_specializeRingHom specializeRingHom_of
    eq_specializeRingHom_of_continuous

@[simp] theorem specializeRingHomEquiv_apply (κ : WeightSpace p K) :
    (specializeRingHomEquiv κ : completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ →+* K) =
      κ.specializeRingHom := (rfl)
@[simp] theorem specializeRingHomEquiv_symm_apply
    (φ : {φ : completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ →+* K // Continuous φ}) :
    specializeRingHomEquiv.symm φ = ofContinuousRingHom φ.val φ.property := (rfl)

/-- Every `η : Δ →* Kˣ` and topologically nilpotent `t ∈ K` determine a unique continuous ring
homomorphism `ℤ_p[[ℤ_pˣ]] →+* K` sending `[ω(δ)] ↦ η(δ)` and `[γ] - 1 ↦ t`. -/
theorem existsUnique_continuous_ringHom_of_tendsto_pow
    (η : (ZMod (p ^ padicUnitsDepth p))ˣ →* Kˣ) {t : K} (ht : Tendsto (t ^ ·) atTop (𝓝 0)) :
    ∃! φ : completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ →+* K, Continuous φ ∧
      (∀ δ, φ (completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ (padicUnitsSection p δ)) = η δ) ∧
      φ (completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ (padicUnitsGenerator p) - 1) = t :=
  existsUnique_of_specializeEquiv specializeRingHomEquiv (fun κ x ↦ κ.specializeRingHom_of x)
    (fun φ x ↦ by simp) (existsUnique_character_of_tendsto_pow_of_normedAlgebra η ht)

/-- When `‖t‖ < 1`, `η` and `t` determine a unique continuous ring homomorphism out of
`ℤ_p[[ℤ_pˣ]]` into a complete ultrametric normed `ℚ_p`-algebra `K`. -/
theorem existsUnique_continuous_ringHom_of_norm_lt_one
    (η : (ZMod (p ^ padicUnitsDepth p))ˣ →* Kˣ) {t : K} (ht : ‖t‖ < 1) :
    ∃! φ : completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ →+* K, Continuous φ ∧
      (∀ δ, φ (completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ (padicUnitsSection p δ)) = η δ) ∧
      φ (completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ (padicUnitsGenerator p) - 1) = t :=
  existsUnique_continuous_ringHom_of_tendsto_pow η (tendsto_pow_atTop_nhds_zero_of_norm_lt_one ht)

/-- When `K` also carries a contractive `ℤ_p`-algebra structure, `normedSpecialize` and
`specializeRingHom` agree as ring homomorphisms on all of `ℤ_p[[ℤ_pˣ]]`. -/
theorem toRingHom_normedSpecialize_eq_specializeRingHom [Algebra ℤ_[p] K] [IsBoundedSMul ℤ_[p] K]
    (κ : WeightSpace p K) : κ.normedSpecialize.toRingHom = κ.specializeRingHom :=
  eq_specializeRingHom_of_continuous κ.continuous_normedSpecialize κ κ.normedSpecialize_of

/-- Specialising `[x]` at the algebraic weight `inclusion K ^ k` gives `x ^ k` in `K`. -/
theorem specializeRingHom_inclusion_pow_of (k : ℕ) (x : ℤ_[p]ˣ) :
    ((inclusion (p := p) K ^ k).specializeRingHom)
      (completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ x) = padicIntAlgebraMap p K x ^ k := by
  simp [ContinuousMonoidHom.pow_apply]

end NormedPadicAlgebra
end WeightSpace
end TauCeti

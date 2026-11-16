/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.WeightSpace.CompletedGroupAlgebra
public import TauCeti.NumberTheory.Padics.WeightSpace.GeneratorChange

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

private theorem liftPS_C_single (δ : (ZMod (p ^ padicUnitsDepth p))ˣ) (a : ℤ_[p]) :
    liftPS ε η (padicUnitsCoordinate p (PowerSeries.C (MonoidAlgebra.single δ a))) =
      algebraMap ℤ_[p] B a * η δ := by
  rw [liftPS, AlgHom.comp_apply, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.coe_toAlgHom,
    (padicUnitsCoordinate p).symm_apply_apply, MonoidAlgebra.powerSeriesAlgEquiv_symm_C_single]
  simp [PowerSeries.C_eq_algebraMap]

private theorem liftPS_map_singleOne (φ : PowerSeries ℤ_[p]) :
    liftPS ε η (padicUnitsCoordinate p (PowerSeries.map MonoidAlgebra.singleOneRingHom φ)) =
      ε φ := by
  rw [liftPS, AlgHom.comp_apply, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.coe_toAlgHom,
    (padicUnitsCoordinate p).symm_apply_apply, ← MonoidAlgebra.toPowerSeries_single_one ℤ_[p] ℤ_[p],
    ← MonoidAlgebra.coe_powerSeriesAlgEquiv, AlgEquiv.symm_apply_apply]; simp

private theorem liftPS_of (x : ℤ_[p]ˣ) :
    liftPS ε η (completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ x) =
      η (padicIntUnitsEquivZModUnitsProd p x).1 *
        ε (PowerSeries.binomialSeries ℤ_[p] (padicIntUnitsEquivZModUnitsProd p x).2.toAdd) := by
  have hmap (s : ℤ_[p]) :
      PowerSeries.binomialSeries (MonoidAlgebra ℤ_[p] (ZMod (p ^ padicUnitsDepth p))ˣ) s =
        PowerSeries.map MonoidAlgebra.singleOneRingHom (PowerSeries.binomialSeries ℤ_[p] s) := by
    ext n; simp [PowerSeries.binomialSeries_coeff, MonoidAlgebra.one_def]
  rw [← (padicUnitsCoordinate p).apply_symm_apply (completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ x),
    padicUnitsCoordinate_symm_of, hmap, map_mul, map_mul, liftPS_C_single, liftPS_map_singleOne,
    map_one, one_mul]

variable {ε}

private theorem continuous_liftPS [TopologicalSpace B] [IsTopologicalRing B] (hε : Continuous ε) :
    Continuous (liftPS ε η) := by
  let : TopologicalSpace (MonoidAlgebra ℤ_[p] (ZMod (p ^ padicUnitsDepth p))ˣ) :=
    moduleTopology ℤ_[p] _
  have : IsModuleTopology ℤ_[p] (MonoidAlgebra ℤ_[p] (ZMod (p ^ padicUnitsDepth p))ˣ) := ⟨rfl⟩
  exact (completedGroupAlgebra.continuous_liftNCAlgHom_powerSeriesAlgEquiv_symm hε
    ((Units.coeHom B).comp η) (fun _ _ ↦ Commute.all _ _)).comp
    (continuous_padicUnitsCoordinate_symm p)

private theorem hasSum_liftNCAlgHom [TopologicalSpace B] [IsTopologicalRing B] {t : B}
    (hε : ∀ φ : PowerSeries ℤ_[p], HasSum (fun n : ℕ ↦ φ.coeff n • t ^ n) (ε φ))
    (F : PowerSeries (MonoidAlgebra ℤ_[p] (ZMod (p ^ padicUnitsDepth p))ˣ)) :
    HasSum (fun n : ℕ ↦ MonoidAlgebra.lift ℤ_[p] B (ZMod (p ^ padicUnitsDepth p))ˣ
        ((Units.coeHom B).comp η) (F.coeff n) * t ^ n)
      (MonoidAlgebra.liftNCAlgHom ε ((Units.coeHom B).comp η) (fun _ _ ↦ Commute.all _ _)
        ((MonoidAlgebra.powerSeriesAlgEquiv ℤ_[p] ℤ_[p] _).symm F)) := by
  rw [MonoidAlgebra.liftNCAlgHom_powerSeriesAlgEquiv_symm_apply]
  refine (hasSum_sum fun δ _ ↦ (hε _).mul_right (η δ : B)).congr_fun fun n ↦ ?_
  rw [MonoidAlgebra.lift_apply,
    Finsupp.sum_fintype _ _ (fun δ ↦ zero_smul ℤ_[p] (((Units.coeHom B).comp η) δ)), Finset.sum_mul]
  exact Finset.sum_congr rfl fun δ _ ↦ by
    rw [MonoidAlgebra.coeff_coeff_powerSeriesAlgEquiv_symm, MonoidHom.comp_apply,
      Units.coeHom_apply, Algebra.smul_def, Algebra.smul_def, mul_right_comm]
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

/-- No continuous ring homomorphism out of `ℤ_p[[ℤ_pˣ]]` into an ultrametric normed `ℤ_p`-algebra
sends `[γ] - 1` to an element whose powers do not tend to `0`. -/
theorem not_exists_continuous_ringHom_of_not_tendsto_pow {R : Type*} [NormedRing R]
    [Algebra ℤ_[p] R] [IsBoundedSMul ℤ_[p] R] [IsUltrametricDist R] {z : R}
    (hz : ¬Tendsto (z ^ ·) atTop (𝓝 0)) :
    ¬∃ φ : completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ →+* R,
      Continuous φ ∧ φ (completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ (padicUnitsGenerator p) - 1) = z := by
  rintro ⟨φ, hφ, rfl⟩
  exact hz <| coord_ofContinuousRingHom φ hφ ▸ (ofContinuousRingHom φ hφ).tendsto_coord_pow

/-- No continuous ring homomorphism out of `ℤ_p[[ℤ_pˣ]]` into a normed division `ℚ_p`-algebra `K`
sends `[γ] - 1` to an element of norm at least `1`. -/
theorem not_exists_continuous_ringHom_of_one_le_norm {K : Type*} [NormedDivisionRing K]
    [NormedAlgebra ℚ_[p] K] {z : K} (hz : 1 ≤ ‖z‖) :
    ¬∃ φ : completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ →+* K,
      Continuous φ ∧ φ (completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ (padicUnitsGenerator p) - 1) = z := by
  rintro ⟨φ, hφ, rfl⟩
  exact not_lt_of_ge hz <| coord_ofContinuousRingHom φ hφ ▸
    norm_coord_lt_one_of_normedAlgebra (ofContinuousRingHom φ hφ)
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
    hasSum_liftNCAlgHom κ.finiteChar (PowerSeries.hasSum_aeval κ.hasEval_coord) F
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
    WeightSpace p S ≃ {φ : completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ →ₐ[ℤ_[p]] S // Continuous φ} where
  toFun κ := ⟨κ.adicSpecialize, κ.continuous_adicSpecialize⟩
  invFun φ := ofContinuousRingHom (φ.1 : completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ →+* S) φ.2
  left_inv κ := κ.ofContinuousRingHom_adicSpecialize
  right_inv φ := Subtype.ext <| (eq_adicSpecialize_of_continuous φ.2 _ fun _ ↦ rfl).symm

@[simp] theorem adicSpecializeEquiv_apply (κ : WeightSpace p S) :
    (adicSpecializeEquiv κ : completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ →ₐ[ℤ_[p]] S) =
      κ.adicSpecialize := (rfl)
@[simp] theorem adicSpecializeEquiv_symm_apply
    (φ : {φ : completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ →ₐ[ℤ_[p]] S // Continuous φ}) :
    adicSpecializeEquiv.symm φ =
      ofContinuousRingHom (φ.1 : completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ →+* S) φ.2 := (rfl)

/-- Every `η : Δ →* Sˣ` and evaluable `z ∈ S` determine a unique continuous `ℤ_p`-algebra
homomorphism `ℤ_p[[ℤ_pˣ]] →ₐ[ℤ_p] S` sending `[ω(δ)] ↦ η(δ)` and `[γ] - 1 ↦ z`. -/
theorem existsUnique_continuous_algHom_of_hasEval (η : (ZMod (p ^ padicUnitsDepth p))ˣ →* Sˣ)
    {z : S} (hz : PowerSeries.HasEval z) :
    ∃! φ : completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ →ₐ[ℤ_[p]] S, Continuous φ ∧
      (∀ δ, φ (completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ (padicUnitsSection p δ)) = η δ) ∧
      φ (completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ (padicUnitsGenerator p) - 1) = z := by
  refine ⟨(ofHasEval η hz).adicSpecialize, ⟨(ofHasEval η hz).continuous_adicSpecialize,
    fun δ ↦ by rw [adicSpecialize_of, ← finiteChar_apply, finiteChar_ofHasEval],
    by rw [adicSpecialize_coord, coord_ofHasEval]⟩, fun φ ⟨hφ, hη, hz'⟩ ↦ ?_⟩
  have hκ : ofContinuousRingHom φ.toRingHom hφ = ofHasEval η hz :=
    ext_finiteChar_coord (by ext δ; simpa using hη δ) (by simpa using hz')
  exact eq_adicSpecialize_of_continuous hφ (ofHasEval η hz) fun x ↦ by rw [← hκ]; rfl

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
theorem normedSpecialize_of_padicUnitsGenerator_inv (κ : WeightSpace p R) :
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
    hasSum_liftNCAlgHom κ.finiteChar (hasSum_padicPowerSeriesEval p κ.tendsto_coord_pow) F
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
    WeightSpace p R ≃ {φ : completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ →ₐ[ℤ_[p]] R // Continuous φ} where
  toFun κ := ⟨κ.normedSpecialize, κ.continuous_normedSpecialize⟩
  invFun φ := ofContinuousRingHom (φ.1 : completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ →+* R) φ.2
  left_inv κ := κ.ofContinuousRingHom_normedSpecialize
  right_inv φ := Subtype.ext <| (eq_normedSpecialize_of_continuous φ.2 _ fun _ ↦ rfl).symm

@[simp] theorem normedSpecializeEquiv_apply (κ : WeightSpace p R) :
    (normedSpecializeEquiv κ : completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ →ₐ[ℤ_[p]] R) =
      κ.normedSpecialize := (rfl)
@[simp] theorem normedSpecializeEquiv_symm_apply
    (φ : {φ : completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ →ₐ[ℤ_[p]] R // Continuous φ}) :
    normedSpecializeEquiv.symm φ =
      ofContinuousRingHom (φ.1 : completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ →+* R) φ.2 := (rfl)

/-- Every `η : Δ →* Rˣ` and topologically nilpotent `t ∈ R` determine a unique continuous
`ℤ_p`-algebra homomorphism `ℤ_p[[ℤ_pˣ]] →ₐ[ℤ_p] R` sending `[ω(δ)] ↦ η(δ)` and `[γ] - 1 ↦ t`. -/
theorem existsUnique_continuous_algHom_of_tendsto_pow
    (η : (ZMod (p ^ padicUnitsDepth p))ˣ →* Rˣ) {t : R} (ht : Tendsto (t ^ ·) atTop (𝓝 0)) :
    ∃! φ : completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ →ₐ[ℤ_[p]] R, Continuous φ ∧
      (∀ δ, φ (completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ (padicUnitsSection p δ)) = η δ) ∧
      φ (completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ (padicUnitsGenerator p) - 1) = t := by
  refine ⟨(ofCoord η t ht).normedSpecialize, ⟨(ofCoord η t ht).continuous_normedSpecialize,
    fun δ ↦ by rw [normedSpecialize_of, ← finiteChar_apply, finiteChar_ofCoord],
    by rw [normedSpecialize_coord, coord_ofCoord]⟩, fun φ ⟨hφ, hη, ht'⟩ ↦ ?_⟩
  have hκ : ofContinuousRingHom φ.toRingHom hφ = ofCoord η t ht :=
    ext_finiteChar_coord (by ext δ; simpa using hη δ) (by simpa using ht')
  exact eq_normedSpecialize_of_continuous hφ (ofCoord η t ht) fun x ↦ by rw [← hκ]; rfl

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

/-- **Generator-change series expansion.** Specialising `padicUnitsCoordinateAt p u F` at `κ`
evaluates the finite-part coefficients against powers of `κ.coordAt u`. -/
theorem hasSum_normedSpecialize_padicUnitsCoordinateAt (κ : WeightSpace p R) (u : ℤ_[p]ˣ)
    (F : PowerSeries (MonoidAlgebra ℤ_[p] (ZMod (p ^ padicUnitsDepth p))ˣ)) :
    HasSum (fun n : ℕ ↦ MonoidAlgebra.lift ℤ_[p] R (ZMod (p ^ padicUnitsDepth p))ˣ
        ((Units.coeHom R).comp κ.finiteChar) (F.coeff n) * κ.coordAt u ^ n)
      (κ.normedSpecialize (padicUnitsCoordinateAt p u F)) := by
  let Δ := (ZMod (p ^ padicUnitsDepth p))ˣ
  let : TopologicalSpace (MonoidAlgebra ℤ_[p] Δ) := moduleTopology ℤ_[p] _
  have : IsModuleTopology ℤ_[p] (MonoidAlgebra ℤ_[p] Δ) := ⟨rfl⟩
  let s := (MonoidAlgebra.powerSeriesAlgEquiv ℤ_[p] ℤ_[p] Δ).symm
  let L₁ := κ.normedSpecialize.comp (padicUnitsCoordinateAt p u).toAlgHom
  let L₂ := (MonoidAlgebra.liftNCAlgHom (padicPowerSeriesEval p (κ.tendsto_coordAt_pow u))
    ((Units.coeHom R).comp κ.finiteChar) fun _ _ ↦ Commute.all _ _).comp s.toAlgHom
  have hL_eq : ⇑L₁ = ⇑L₂ :=
    (PowerSeries.WithPiTopology.denseRange_toPowerSeries (MonoidAlgebra ℤ_[p] Δ)).equalizer
      (κ.continuous_normedSpecialize.comp (continuous_padicUnitsCoordinateAt p u))
      (completedGroupAlgebra.continuous_liftNCAlgHom_powerSeriesAlgEquiv_symm
        (continuous_padicPowerSeriesEval p (κ.tendsto_coordAt_pow u))
        ((Units.coeHom R).comp κ.finiteChar) (fun _ _ ↦ Commute.all _ _))
      (funext fun P ↦ by
        simp only [Function.comp_apply]
        induction P using Polynomial.induction_on' with
        | add _ _ hf hg => simp [Polynomial.coe_add, map_add, hf, hg]
        | monomial n r =>
          rw [Polynomial.coe_monomial, PowerSeries.monomial_eq_C_mul_X_pow, map_mul, map_mul,
            map_pow, map_pow]
          refine congrArg₂ (· * ·) ?_ (by simp [L₁, L₂, s, Δ, coordAt_eq_principalChar_sub_one,
            principalChar_apply, MonoidAlgebra.powerSeriesAlgEquiv_symm_X])
          induction r using MonoidAlgebra.induction_linear with
          | zero => simp
          | add _ _ hx hy => simp [map_add, hx, hy]
          | single δ a =>
            dsimp only [L₁, L₂, s, Δ]
            rw [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, padicUnitsCoordinateAt_C_single,
              map_mul, AlgHom.commutes, normedSpecialize_of, ← finiteChar_apply, AlgHom.comp_apply,
              AlgEquiv.coe_toAlgHom, MonoidAlgebra.powerSeriesAlgEquiv_symm_C_single]
            simp [PowerSeries.C_eq_algebraMap])
  rw [← AlgEquiv.coe_toAlgHom (padicUnitsCoordinateAt p u), ← AlgHom.comp_apply,
    congrFun hL_eq F]
  exact hasSum_liftNCAlgHom κ.finiteChar (hasSum_padicPowerSeriesEval p (κ.tendsto_coordAt_pow u)) F

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
variable {K : Type*} [NormedCommRing K] [NormedAlgebra ℚ_[p] K]

variable (p K) in
@[instance_reducible] private noncomputable def padicAlg : Algebra ℤ_[p] K :=
  Algebra.compHom K (algebraMap ℤ_[p] ℚ_[p])
variable (p K) in
private theorem padicBoundedSMul : letI := padicAlg p K; IsBoundedSMul ℤ_[p] K :=
  letI := padicAlg p K; .of_norm_smul_le fun r x ↦ norm_smul_le (r : ℚ_[p]) x

variable [IsUltrametricDist K] [CompleteSpace K]

/-- **Specialisation of `ℤ_p[[ℤ_pˣ]]` at a weight in a complete ultrametric normed commutative
`ℚ_p`-algebra `K`**, bundled as a ring homomorphism without requiring `Algebra ℤ_[p] K`. -/
noncomputable def specializeRingHom (κ : WeightSpace p K) :
    completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ →+* K :=
  letI := padicAlg p K; haveI := padicBoundedSMul p K; κ.normedSpecialize.toRingHom

theorem continuous_specializeRingHom (κ : WeightSpace p K) : Continuous κ.specializeRingHom :=
  letI := padicAlg p K; haveI := padicBoundedSMul p K; κ.continuous_normedSpecialize
@[simp] theorem specializeRingHom_of (κ : WeightSpace p K) (x : ℤ_[p]ˣ) :
    κ.specializeRingHom (completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ x) = κ x :=
  letI := padicAlg p K; haveI := padicBoundedSMul p K; κ.normedSpecialize_of x
@[simp] theorem specializeRingHom_algebraMap (κ : WeightSpace p K) (a : ℤ_[p]) :
    κ.specializeRingHom (algebraMap ℤ_[p] (completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ) a) =
      padicIntAlgebraMap p K a := by
  let _ := padicAlg p K; have _ := padicBoundedSMul p K
  simp [specializeRingHom, padicAlg, AlgHom.commutes, Algebra.compHom_algebraMap_apply,
    padicIntAlgebraMap_apply, PadicInt.algebraMap_eq_coe_ringHom]
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
  let _ := padicAlg p K; have _ := padicBoundedSMul p K
  refine (κ.hasSum_normedSpecialize_padicUnitsCoordinate F).congr_fun fun n ↦ congrArg (· * _) ?_
  induction F.coeff n using MonoidAlgebra.induction_linear with
  | zero => simp
  | add _ _ hx hy => simp [map_add, hx, hy]
  | single _ _ =>
    simp [Algebra.smul_def, Algebra.compHom_algebraMap_apply, padicIntAlgebraMap_apply,
      PadicInt.algebraMap_eq_coe_ringHom]
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
    WeightSpace p K ≃ {φ : completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ →+* K // Continuous φ} where
  toFun κ := ⟨κ.specializeRingHom, κ.continuous_specializeRingHom⟩
  invFun φ := ofContinuousRingHom φ.1 φ.2
  left_inv κ := κ.ofContinuousRingHom_specializeRingHom
  right_inv φ := Subtype.ext <| (eq_specializeRingHom_of_continuous φ.2 _ fun _ ↦ rfl).symm

@[simp] theorem specializeRingHomEquiv_apply (κ : WeightSpace p K) :
    (specializeRingHomEquiv κ : completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ →+* K) =
      κ.specializeRingHom := (rfl)
@[simp] theorem specializeRingHomEquiv_symm_apply
    (φ : {φ : completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ →+* K // Continuous φ}) :
    specializeRingHomEquiv.symm φ = ofContinuousRingHom φ.1 φ.2 := (rfl)

/-- Every `η : Δ →* Kˣ` and topologically nilpotent `t ∈ K` determine a unique continuous ring
homomorphism `ℤ_p[[ℤ_pˣ]] →+* K` sending `[ω(δ)] ↦ η(δ)` and `[γ] - 1 ↦ t`. -/
theorem existsUnique_continuous_ringHom_of_tendsto_pow
    (η : (ZMod (p ^ padicUnitsDepth p))ˣ →* Kˣ) {t : K} (ht : Tendsto (t ^ ·) atTop (𝓝 0)) :
    ∃! φ : completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ →+* K, Continuous φ ∧
      (∀ δ, φ (completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ (padicUnitsSection p δ)) = η δ) ∧
      φ (completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ (padicUnitsGenerator p) - 1) = t := by
  refine ⟨(ofCoordOfNormedAlgebra η t ht).specializeRingHom,
    ⟨(ofCoordOfNormedAlgebra η t ht).continuous_specializeRingHom,
      fun δ ↦ by rw [specializeRingHom_of, ← finiteChar_apply, finiteChar_ofCoordOfNormedAlgebra],
      by rw [specializeRingHom_coord, coord_ofCoordOfNormedAlgebra]⟩,
    fun φ ⟨hφ, hη, ht'⟩ ↦ ?_⟩
  have hκ : ofContinuousRingHom φ hφ = ofCoordOfNormedAlgebra η t ht :=
    ext_finiteChar_coord (by ext δ; simpa [coe_finiteChar_ofContinuousRingHom_apply] using hη δ)
      (by simpa using ht')
  exact eq_specializeRingHom_of_continuous hφ _ fun x ↦ by rw [← hκ]; rfl

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

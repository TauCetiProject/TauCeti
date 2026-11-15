/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Tower.Summation
public import TauCeti.Algebra.Lie.Current.CompletedDerivation
public import TauCeti.Algebra.Lie.Current.ExtendedAffine.LeftIdeal

/-!
# The completed enveloping algebra of the extended affine algebra at a fixed level

For `U = U(ĝ) / (ι K - a)`, `U' = U(ĝ') / (ι K - a)`, and `I'_n = U' · ι(a_n)`, this file builds
the **completed extended enveloping algebra** `Û' = lim_n U' / I'_n`
(`TauCeti.CurrentAlgebra.ExtendedCompletedEnveloping`), the closed uniform embedding `Û →ₐ[R] Û'`
(`TauCeti.CurrentAlgebra.completedToExtended`), the completed degree element `d̂ ∈ Û'` and its
coordinates `completedDegreeCoeff`, functoriality, and `extendedLevelCompletedEnvelopingEquiv`.

## References

* E. Frenkel, *Langlands Correspondence for Loop Groups*, §4.3.2.
-/

public section

noncomputable section

open Filter Topology TauCeti.UniversalEnvelopingAlgebra
open scoped LaurentSeries
open LieAlgebra.ofTwoCocycle (centralElement envelopingι)

namespace TauCeti.CurrentAlgebra

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

section Completion

variable (Φ : LinearMap.BilinForm R L) (hΦ : Φ.lieInvariant L) (hΦs : Φ.IsSymm) (a : R)

local notation "c" => twoCocycleOfBilinear R L Φ hΦ hΦs
local notation "UK" => CentralQuotient R (centralElement c) a
local notation "UK'" =>
  CentralQuotient R (toExtendedResidueExtension Φ hΦ hΦs (centralElement c)) a
local notation "oAnti" => orderLeftIdeal_natCast_antitone Φ hΦ hΦs a
local notation "eAnti" => extendedOrderLeftIdeal_natCast_antitone Φ hΦ hΦs a
local notation "oTower" => orderQuotientTower Φ hΦ hΦs a

/-- The tower `U' / I'_0 ← U' / I'_1 ← ⋯` of quotients of `U(ĝ') / (ι K - a)`. -/
abbrev extendedOrderQuotientTower : ModuleTower UK' := ModuleTower.quotients _ eAnti

local notation "eTower" => extendedOrderQuotientTower Φ hΦ hΦs a

/-- **The completed extended enveloping algebra** `Û' = lim_n U' / I'_n` at level `a`. -/
abbrev ExtendedCompletedEnveloping : Type _ := (eTower).lim

local notation "Û" => CompletedEnveloping Φ hΦ hΦs a
local notation "Û'" => ExtendedCompletedEnveloping Φ hΦ hΦs a

theorem ker_toLimQuotients_extendedOrderLeftIdeal :
    LinearMap.ker (ModuleTower.toLimQuotients _ eAnti) =
      ⨅ N : ℤ, extendedOrderLeftIdeal Φ hΦ hΦs a N := by
  rw [ModuleTower.ker_toLimQuotients, iInf_extendedOrderLeftIdeal_natCast]

instance : Ring Û' :=
  ModuleTower.limRing (exists_forall_mul_mem_extendedOrderLeftIdeal_natCast Φ hΦ hΦs a)

instance : Algebra R Û' where
  smul r x := algebraMap R UK' r • x
  algebraMap :=
    { toFun r := ModuleTower.toLimQuotients _ _ (algebraMap R UK' r)
      map_one' := congrArg (ModuleTower.toLimQuotients _ _) (map_one _)
      map_mul' r s := (congrArg (ModuleTower.toLimQuotients _ _) (map_mul _ r s)).trans
        (ModuleTower.toLimQuotients_mul
          (exists_forall_mul_mem_extendedOrderLeftIdeal_natCast Φ hΦ hΦs a) _ _)
      map_zero' := by rw [map_zero, map_zero]
      map_add' r s := by rw [map_add, map_add] }
  commutes' r x := (ModuleTower.smul_eq_limMul _ _ x).symm.trans
    (ModuleTower.limMul_toLimQuotients_of_commute _ (fun b ↦ Algebra.commute_algebraMap_right r b)
      x).symm
  smul_def' _ x := ModuleTower.smul_eq_limMul _ _ x

instance : IsScalarTower R UK' Û' := .of_algebraMap_smul fun _ _ ↦ rfl

/-- **The canonical algebra map** `U' →ₐ[R] Û'` into the completed extended enveloping algebra. -/
def toExtendedCompletedEnveloping : UK' →ₐ[R] Û' :=
  { ModuleTower.toLimRingHom
      (exists_forall_mul_mem_extendedOrderLeftIdeal_natCast Φ hΦ hΦs a) with
    commutes' r := congrFun (ModuleTower.coe_toLimRingHom _) (algebraMap R UK' r) }

local notation "ι'" => toExtendedCompletedEnveloping Φ hΦ hΦs a

@[simp]
theorem coe_toExtendedCompletedEnveloping : ⇑ι' = ModuleTower.toLimQuotients _ eAnti :=
  ModuleTower.coe_toLimRingHom _

theorem denseRange_toExtendedCompletedEnveloping : DenseRange ι' := by
  simpa only [coe_toExtendedCompletedEnveloping] using ModuleTower.denseRange_toLimQuotients _ eAnti

variable {Φ hΦ hΦs a} in
theorem limπ_toExtendedCompletedEnveloping (n : ℕ) (b : UK') :
    (eTower).limπ n (ι' b) = ModuleTower.quotientsπ _ eAnti n b := by
  rw [coe_toExtendedCompletedEnveloping, ← LinearMap.comp_apply,
    ModuleTower.limπ_comp_toLimQuotients]

/-- **The kernel of the stage projection** `Û' → U' / I'_n`, an open and closed left ideal. -/
def completedExtendedOrderLeftIdeal (n : ℕ) : Submodule Û' Û' where
  carrier := LinearMap.ker ((eTower).limπ n)
  add_mem' := add_mem
  zero_mem' := zero_mem _
  smul_mem' x _ hy := ModuleTower.limπ_limMul_eq_zero _ x hy

local notation "Î'" => completedExtendedOrderLeftIdeal Φ hΦ hΦs a

variable {Φ hΦ hΦs a}

@[simp]
theorem mem_completedExtendedOrderLeftIdeal {n : ℕ} {x : Û'} :
    x ∈ Î' n ↔ (eTower).limπ n x = 0 := Iff.rfl

theorem toExtendedCompletedEnveloping_mem_completedExtendedOrderLeftIdeal_iff {n : ℕ} {b : UK'} :
    ι' b ∈ Î' n ↔ b ∈ extendedOrderLeftIdeal Φ hΦ hΦs a n := by
  simp only [coe_toExtendedCompletedEnveloping, mem_completedExtendedOrderLeftIdeal,
    ModuleTower.limπ_apply, ModuleTower.coe_toLimQuotients_apply,
    ModuleTower.quotientsπ_eq_zero_iff]

theorem exists_forall_mul_mem_completedExtendedOrderLeftIdeal (y : Û') (n : ℕ) :
    ∃ m, ∀ x ∈ Î' m, x * y ∈ Î' n :=
  ModuleTower.exists_forall_limπ_limMul_eq_zero _ y n

variable (Φ hΦ hΦs a)

theorem hasBasis_nhds_zero_completedExtendedOrderLeftIdeal :
    (𝓝 (0 : Û')).HasBasis (fun _ : ℕ ↦ True) fun n ↦ (Î' n : Set Û') :=
  (eTower).hasBasis_nhds_zero

instance : IsLinearTopology Û' Û' :=
  .mk_of_hasBasis _ (hasBasis_nhds_zero_completedExtendedOrderLeftIdeal Φ hΦ hΦs a)

instance : IsTopologicalRing Û' where
  continuous_mul := ModuleTower.continuous_limMul _

theorem isClosed_completedExtendedOrderLeftIdeal (n : ℕ) : IsClosed (Î' n : Set Û') :=
  (eTower).isClosed_ker_limπ n

theorem isOpen_completedExtendedOrderLeftIdeal (n : ℕ) : IsOpen (Î' n : Set Û') :=
  (eTower).isOpen_ker_limπ n

private theorem orderLeftIdeal_le_comap_toExtendedEnveloping (n : ℕ) :
    orderLeftIdeal Φ hΦ hΦs a n ≤
      (extendedOrderLeftIdeal Φ hΦ hΦs a n).comap
        (toExtendedEnveloping Φ hΦ hΦs a).toRingHom.toSemilinearMap :=
  fun _ hx ↦ toExtendedEnveloping_mem_extendedOrderLeftIdeal hx

private def completedToExtendedFun : Û → Û' :=
  ModuleTower.limQuotientsMap oAnti eAnti
    (toExtendedEnveloping Φ hΦ hΦs a).toRingHom.toSemilinearMap
    (fun n ↦ ⟨n, orderLeftIdeal_le_comap_toExtendedEnveloping Φ hΦ hΦs a n⟩)

private theorem completedToExtendedFun_toCompletedEnveloping (x : UK) :
    completedToExtendedFun Φ hΦ hΦs a (toCompletedEnveloping Φ hΦ hΦs a x) =
      ι' (toExtendedEnveloping Φ hΦ hΦs a x) := by
  rw [completedToExtendedFun, coe_toCompletedEnveloping, coe_toExtendedCompletedEnveloping,
    ModuleTower.limQuotientsMap_toLimQuotients]; rfl

/-- **The canonical continuous algebra map** `Û →ₐ[R] Û'` extending `U → U'`. -/
def completedToExtended : Û →ₐ[R] Û' where
  toFun := completedToExtendedFun Φ hΦ hΦs a
  map_one' := by
    rw [← map_one (toCompletedEnveloping Φ hΦ hΦs a),
      completedToExtendedFun_toCompletedEnveloping, map_one, map_one]
  map_mul' x y := by
    rw [completedToExtendedFun]; exact ModuleTower.limQuotientsMap_limMul _ _ _ _ _ x y
  map_zero' := by rw [completedToExtendedFun]; exact map_zero _
  map_add' x y := by rw [completedToExtendedFun]; exact map_add _ x y
  commutes' r := by
    rw [← (toCompletedEnveloping Φ hΦ hΦs a).commutes r,
      completedToExtendedFun_toCompletedEnveloping, (toExtendedEnveloping Φ hΦ hΦs a).commutes r,
      (ι').commutes r]

local notation "ι̂" => completedToExtended Φ hΦ hΦs a

@[simp]
theorem completedToExtended_toLimQuotients (x : UK) :
    ι̂ (ModuleTower.toLimQuotients _ oAnti x) =
      ModuleTower.toLimQuotients _ eAnti (toExtendedEnveloping Φ hΦ hΦs a x) :=
  ModuleTower.limQuotientsMap_toLimQuotients _ _ _ _ x

theorem completedToExtended_toCompletedEnveloping (x : UK) :
    ι̂ (toCompletedEnveloping Φ hΦ hΦs a x) = ι' (toExtendedEnveloping Φ hΦ hΦs a x) := by
  rw [coe_toCompletedEnveloping, coe_toExtendedCompletedEnveloping,
    completedToExtended_toLimQuotients]

theorem continuous_completedToExtended : Continuous ι̂ :=
  ModuleTower.continuous_limQuotientsMap _ _ _ _

variable {Φ hΦ hΦs a} in
theorem completedToExtended_mem_completedExtendedOrderLeftIdeal_iff {n : ℕ} {x : Û} :
    ι̂ x ∈ Î' n ↔ x ∈ completedOrderLeftIdeal Φ hΦ hΦs a n := by
  obtain ⟨b, hb⟩ := ModuleTower.quotientsπ_surjective _ _ n ((oTower).limπ n x)
  have hπ : (eTower).limπ n (ι̂ x) =
      ModuleTower.quotientsπ _ eAnti n (toExtendedEnveloping Φ hΦ hΦs a b) :=
    ModuleTower.limπ_limQuotientsMap _ _ _ _
      (orderLeftIdeal_le_comap_toExtendedEnveloping Φ hΦ hΦs a n) hb
  rw [mem_completedExtendedOrderLeftIdeal, mem_completedOrderLeftIdeal, hπ, ← hb,
    ModuleTower.quotientsπ_eq_zero_iff, ModuleTower.quotientsπ_eq_zero_iff,
    toExtendedEnveloping_mem_extendedOrderLeftIdeal_iff]

/-- **The completed degree element** `d̂ ∈ Û'`, image of `d = t d/dt`. -/
def completedDegreeElement : Û' := ι' (CentralQuotient.ι _ a (degreeElement Φ hΦ hΦs))

local notation "d̂" => completedDegreeElement Φ hΦ hΦs a

variable {Φ hΦ hΦs a} in
theorem mul_completedDegreeElement_mem_completedExtendedOrderLeftIdeal {n : ℕ} {w : Û'}
    (hw : w ∈ Î' n) : w * d̂ ∈ Î' n := by
  rw [mem_completedExtendedOrderLeftIdeal] at hw ⊢
  change (eTower).limπ n
    (ModuleTower.limMul (exists_forall_mul_mem_extendedOrderLeftIdeal_natCast Φ hΦ hΦs a) w d̂) = 0
  rw [completedDegreeElement, ModuleTower.limπ_limMul, limπ_toExtendedCompletedEnveloping,
    ModuleTower.limSmul_quotientsπ
      (exists_forall_mul_mem_extendedOrderLeftIdeal_natCast Φ hΦ hΦs a) (m := n)
      (fun _ hc' ↦ mul_ι_degreeElement_mem_extendedOrderLeftIdeal hc') (b := 0)
      (by rw [map_zero, hw]), zero_mul, map_zero]

variable {Φ hΦ hΦs a} in
theorem mul_completedDegreeElement_pow_mem_completedExtendedOrderLeftIdeal {n : ℕ} {w : Û'}
    (hw : w ∈ Î' n) (m : ℕ) : w * d̂ ^ m ∈ Î' n := by
  induction m with
  | zero => simpa using hw
  | succ m ih =>
    rw [pow_succ, ← mul_assoc]
    exact mul_completedDegreeElement_mem_completedExtendedOrderLeftIdeal ih

/-- **Inner derivation by `d̂` restricts on `Û` to the completed degree derivation.** -/
theorem completedDegreeElement_mul_completedToExtended_sub_mul (x : Û) :
    d̂ * ι̂ x - ι̂ x * d̂ =
      ι̂ ((vectorFieldCompletedEnvelopingDerivation Φ hΦ hΦs a (HahnSeries.single 1 1) :
        Module.End R Û) x) := by
  have hi := continuous_completedToExtended Φ hΦ hΦs a
  have hδ := continuous_vectorFieldCompletedEnvelopingDerivation Φ hΦ hΦs a (HahnSeries.single 1 1)
  induction x using (denseRange_toCompletedEnveloping Φ hΦ hΦs a).induction_on with
  | hp => exact isClosed_eq ((continuous_const.mul hi).sub (hi.mul continuous_const)) (hi.comp hδ)
  | ih b =>
    rw [completedToExtended_toCompletedEnveloping, completedDegreeElement, ← map_mul, ← map_mul,
      ← map_sub, ι_degreeElement_mul_sub_mul, coe_toCompletedEnveloping,
      vectorFieldCompletedEnvelopingDerivation_toLimQuotients,
      completedToExtended_toCompletedEnveloping]

local notation "eOre" => extendedEnvelopingOreEquiv Φ hΦ hΦs a

theorem adjoin_insert_ι_degreeElement_range_toExtendedEnveloping :
    Algebra.adjoin R (insert (CentralQuotient.ι _ a (degreeElement Φ hΦ hΦs))
      (Set.range (toExtendedEnveloping Φ hΦ hΦs a))) = ⊤ := by
  rw [eq_top_iff]; intro x _
  rw [← (eOre).symm_apply_apply x, ← OreExtension.sum_monomial_eq (eOre x), map_sum]
  refine sum_mem fun n _ ↦ extendedEnvelopingOreEquiv_symm_monomial Φ hΦ hΦs a _ _ ▸
    mul_mem (Algebra.subset_adjoin (Set.mem_insert_of_mem _ ⟨_, rfl⟩))
      (pow_mem (Algebra.subset_adjoin (Set.mem_insert _ _)) n)

/-- **Topological generation of `Û'`** by `d̂` and the image of `Û`. -/
theorem topologicalClosure_adjoin_insert_completedDegreeElement_range_completedToExtended :
    (Algebra.adjoin R (insert d̂ (Set.range ι̂))).topologicalClosure = ⊤ := by
  have hle : (ι').range ≤ Algebra.adjoin R (insert d̂ (Set.range ι̂)) := by
    rw [← Algebra.map_top, ← adjoin_insert_ι_degreeElement_range_toExtendedEnveloping Φ hΦ hΦs a,
      AlgHom.map_adjoin]
    refine Algebra.adjoin_mono ?_
    rintro _ ⟨_, rfl | ⟨b, rfl⟩, rfl⟩
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ ⟨_, completedToExtended_toCompletedEnveloping Φ hΦ hΦs a b⟩
  have htop : (ι').range.topologicalClosure = ⊤ := SetLike.ext' <| by
    simpa using (denseRange_toExtendedCompletedEnveloping Φ hΦ hΦs a).closure_range
  exact eq_top_iff.2 (htop ▸ Subalgebra.topologicalClosure_mono hle)

private def stageDegreeCoeff (j n : ℕ) (q : (eTower).obj (Opposite.op n)) :
    (oTower).obj (Opposite.op n) :=
  ModuleTower.quotientsπ _ oAnti n
    ((eOre (ModuleTower.quotientsπ_surjective _ _ n q).choose).coeff j)

private theorem stageDegreeCoeff_quotientsπ (j n : ℕ) (x : UK') :
    stageDegreeCoeff Φ hΦ hΦs a j n (ModuleTower.quotientsπ _ eAnti n x) =
      ModuleTower.quotientsπ _ oAnti n ((eOre x).coeff j) := by
  let q := ModuleTower.quotientsπ _ eAnti n x
  have hy := (ModuleTower.quotientsπ_surjective _ _ n q).choose_spec
  rw [ModuleTower.quotientsπ_eq_quotientsπ_iff, mem_extendedOrderLeftIdeal_iff_coeff] at hy
  rw [stageDegreeCoeff, ModuleTower.quotientsπ_eq_quotientsπ_iff, ← OreExtension.coeff_sub,
    ← map_sub]; exact hy j

private theorem stageDegreeCoeff_add (j n : ℕ) (q₁ q₂ : (eTower).obj (Opposite.op n)) :
    stageDegreeCoeff Φ hΦ hΦs a j n (q₁ + q₂) =
      stageDegreeCoeff Φ hΦ hΦs a j n q₁ + stageDegreeCoeff Φ hΦ hΦs a j n q₂ := by
  obtain ⟨x₁, rfl⟩ := ModuleTower.quotientsπ_surjective _ _ n q₁
  obtain ⟨x₂, rfl⟩ := ModuleTower.quotientsπ_surjective _ _ n q₂
  rw [← map_add, stageDegreeCoeff_quotientsπ, stageDegreeCoeff_quotientsπ,
    stageDegreeCoeff_quotientsπ, map_add, OreExtension.coeff_add, map_add]

private theorem stageDegreeCoeff_algebraMap_smul (j n : ℕ) (r : R)
    (q : (eTower).obj (Opposite.op n)) :
    stageDegreeCoeff Φ hΦ hΦs a j n (algebraMap R UK' r • q) =
      algebraMap R UK r • stageDegreeCoeff Φ hΦ hΦs a j n q := by
  obtain ⟨x, rfl⟩ := ModuleTower.quotientsπ_surjective _ _ n q
  rw [← map_smul, smul_eq_mul, ← (toExtendedEnveloping Φ hΦ hΦs a).commutes r,
    stageDegreeCoeff_quotientsπ, stageDegreeCoeff_quotientsπ, map_mul,
    extendedEnvelopingOreEquiv_toExtendedEnveloping, OreExtension.coeff_C_mul, ← smul_eq_mul,
    map_smul]

private theorem eq_zero_iff_forall_stageDegreeCoeff (n : ℕ) (q : (eTower).obj (Opposite.op n)) :
    q = 0 ↔ ∀ j, stageDegreeCoeff Φ hΦ hΦs a j n q = 0 := by
  obtain ⟨x, rfl⟩ := ModuleTower.quotientsπ_surjective _ _ n q
  simp only [stageDegreeCoeff_quotientsπ, ModuleTower.quotientsπ_eq_zero_iff,
    mem_extendedOrderLeftIdeal_iff_coeff]

private theorem transition_stageDegreeCoeff (j n : ℕ) (q : (eTower).obj (Opposite.op (n + 1))) :
    (oTower).transition n (stageDegreeCoeff Φ hΦ hΦs a j (n + 1) q) =
      stageDegreeCoeff Φ hΦ hΦs a j n ((eTower).transition n q) := by
  obtain ⟨x, rfl⟩ := ModuleTower.quotientsπ_surjective _ _ (n + 1) q
  rw [stageDegreeCoeff_quotientsπ, ModuleTower.transition_quotientsπ,
    ModuleTower.transition_quotientsπ, stageDegreeCoeff_quotientsπ]

private def completedDegreeCoeffAux (j : ℕ) (w : Û') : Û :=
  ⟨fun n ↦ stageDegreeCoeff Φ hΦ hΦs a j n ((eTower).limπ n w), (oTower).mem_lim.2 fun n ↦ by
    rw [transition_stageDegreeCoeff, ← LinearMap.comp_apply, ModuleTower.transition_comp_limπ]⟩

/-- **The `j`-th completed `d̂`-coefficient** `Û' →ₗ[R] Û`. -/
def completedDegreeCoeff (j : ℕ) : Û' →ₗ[R] Û where
  toFun := completedDegreeCoeffAux Φ hΦ hΦs a j
  map_add' _ _ := ModuleTower.lim_ext _ fun n ↦ by
    simp only [map_add, completedDegreeCoeffAux, ModuleTower.limπ_apply, stageDegreeCoeff_add]
  map_smul' r w := ModuleTower.lim_ext _ fun n ↦ by
    rw [RingHom.id_apply, ← algebraMap_smul UK' r w,
      ← algebraMap_smul UK r (completedDegreeCoeffAux Φ hΦ hΦs a j w)]
    simp only [map_smul, completedDegreeCoeffAux, ModuleTower.limπ_apply,
      stageDegreeCoeff_algebraMap_smul]

private theorem limπ_completedDegreeCoeff (j n : ℕ) (w : Û') :
    (oTower).limπ n (completedDegreeCoeff Φ hΦ hΦs a j w) =
      stageDegreeCoeff Φ hΦ hΦs a j n ((eTower).limπ n w) :=
  (oTower).limπ_apply n _

local notation "coeff̂" => completedDegreeCoeff Φ hΦ hΦs a

@[simp]
theorem completedDegreeCoeff_toLimQuotients (j : ℕ) (x : UK') :
    coeff̂ j (ModuleTower.toLimQuotients _ eAnti x) =
      ModuleTower.toLimQuotients _ oAnti ((eOre x).coeff j) :=
  ModuleTower.lim_ext _ fun n ↦ by
    rw [limπ_completedDegreeCoeff, ← coe_toExtendedCompletedEnveloping,
      limπ_toExtendedCompletedEnveloping, stageDegreeCoeff_quotientsπ,
      ← coe_toCompletedEnveloping, limπ_toCompletedEnveloping]

theorem completedDegreeCoeff_toExtendedCompletedEnveloping (j : ℕ) (x : UK') :
    coeff̂ j (ι' x) = toCompletedEnveloping Φ hΦ hΦs a ((eOre x).coeff j) := by
  rw [coe_toExtendedCompletedEnveloping, coe_toCompletedEnveloping,
    completedDegreeCoeff_toLimQuotients]

variable {Φ hΦ hΦs a} in
theorem mem_completedExtendedOrderLeftIdeal_iff_forall_completedDegreeCoeff {n : ℕ} {w : Û'} :
    w ∈ Î' n ↔ ∀ j, coeff̂ j w ∈ completedOrderLeftIdeal Φ hΦ hΦs a n := by
  simp only [mem_completedExtendedOrderLeftIdeal, eq_zero_iff_forall_stageDegreeCoeff,
    mem_completedOrderLeftIdeal, limπ_completedDegreeCoeff]

theorem ext_completedDegreeCoeff {w₁ w₂ : Û'} (h : ∀ j, coeff̂ j w₁ = coeff̂ j w₂) : w₁ = w₂ := by
  rw [← sub_eq_zero]; refine ModuleTower.lim_ext _ fun n ↦ ?_
  rw [map_zero, ← mem_completedExtendedOrderLeftIdeal,
    mem_completedExtendedOrderLeftIdeal_iff_forall_completedDegreeCoeff]
  intro j; rw [map_sub, h j, sub_self]; exact zero_mem _

theorem continuous_completedDegreeCoeff (j : ℕ) : Continuous (coeff̂ j) :=
  continuous_of_tendsto_nhds_zero (coeff̂ j) <|
    ((hasBasis_nhds_zero_completedExtendedOrderLeftIdeal Φ hΦ hΦs a).tendsto_iff
      (hasBasis_nhds_zero_completedOrderLeftIdeal Φ hΦ hΦs a)).2 fun n _ ↦
        ⟨n, trivial, fun _ hw ↦
          (mem_completedExtendedOrderLeftIdeal_iff_forall_completedDegreeCoeff.1 hw) j⟩

@[simp]
theorem completedDegreeCoeff_completedToExtended_mul_pow (j k : ℕ) (u : Û) :
    coeff̂ j (ι̂ u * d̂ ^ k) = if k = j then u else 0 := by
  have hc := continuous_completedDegreeCoeff Φ hΦ hΦs a j
  have hi := continuous_completedToExtended Φ hΦ hΦs a
  have hrhs : Continuous fun u : Û ↦ if k = j then u else 0 := by
    by_cases hkj : k = j <;> simp [hkj, continuous_id', continuous_const]
  induction u using (denseRange_toCompletedEnveloping Φ hΦ hΦs a).induction_on with
  | hp => exact isClosed_eq (hc.comp (hi.mul continuous_const)) hrhs
  | ih b =>
    rw [completedToExtended_toCompletedEnveloping, completedDegreeElement, ← map_pow, ← map_mul,
      ← extendedEnvelopingOreEquiv_symm_monomial,
      completedDegreeCoeff_toExtendedCompletedEnveloping, AlgEquiv.apply_symm_apply,
      OreExtension.coeff_monomial]
    by_cases hkj : k = j <;> simp [hkj]

@[simp]
theorem completedDegreeCoeff_zero_completedToExtended (u : Û) : coeff̂ 0 (ι̂ u) = u := by
  simpa using completedDegreeCoeff_completedToExtended_mul_pow Φ hΦ hΦs a 0 0 u

theorem leftInverse_completedDegreeCoeff_zero_completedToExtended :
    Function.LeftInverse (coeff̂ 0) ι̂ :=
  completedDegreeCoeff_zero_completedToExtended Φ hΦ hΦs a

/-- **`Û` embeds injectively into `Û'`** over every commutative ring and at every level `a`. -/
theorem completedToExtended_injective : Function.Injective ι̂ :=
  (leftInverse_completedDegreeCoeff_zero_completedToExtended Φ hΦ hΦs a).injective

/-- **`completedToExtended : Û → Û'` is a closed embedding.** -/
theorem isClosedEmbedding_completedToExtended : IsClosedEmbedding ι̂ :=
  (leftInverse_completedDegreeCoeff_zero_completedToExtended Φ hΦ hΦs a).isClosedEmbedding
    (continuous_completedDegreeCoeff Φ hΦ hΦs a 0) (continuous_completedToExtended Φ hΦ hΦs a)

/-- **`completedToExtended : Û → Û'` is a uniform embedding.** -/
theorem isUniformEmbedding_completedToExtended : IsUniformEmbedding ι̂ :=
  AddMonoidHom.isUniformEmbedding_of_isEmbedding (f := (ι̂).toAddMonoidHom)
    (isClosedEmbedding_completedToExtended Φ hΦ hΦs a).isEmbedding

/-- **The completed `d̂`-coefficients of every element of `Û'` tend to `0`.** -/
theorem tendsto_completedDegreeCoeff_atTop (w : Û') : Tendsto (fun j ↦ coeff̂ j w) atTop (𝓝 0) := by
  rw [ModuleTower.tendsto_nhds_iff]; intro n
  obtain ⟨x, hx⟩ := ModuleTower.quotientsπ_surjective _ _ n ((eTower).limπ n w)
  let s := (eOre x).toFinsupp.support
  refine eventually_atTop.2 ⟨s.sup id + 1, fun j hj ↦ ?_⟩
  have hjs : j ∉ s := fun hmem ↦ by have : j ≤ s.sup id := Finset.le_sup (f := id) hmem; omega
  have h0 : (eOre x).coeff j = 0 := by
    rw [OreExtension.coeff_def]; exact Classical.not_not.1 (mt Finsupp.mem_support_iff.2 hjs)
  rw [map_zero, limπ_completedDegreeCoeff, ← hx, stageDegreeCoeff_quotientsπ, h0, map_zero]

theorem summable_completedToExtended_mul_completedDegreeElement_pow
    {u : ℕ → Û} (hu : Tendsto u atTop (𝓝 0)) : Summable fun j ↦ ι̂ (u j) * d̂ ^ j := by
  rw [ModuleTower.summable_iff_forall_eventually_limπ_eq_zero]; intro n; rw [Nat.cofinite_eq_atTop]
  filter_upwards [((hasBasis_nhds_zero_completedOrderLeftIdeal Φ hΦ hΦs a).tendsto_right_iff.1 hu)
    n trivial] with j hj
  rw [← mem_completedExtendedOrderLeftIdeal]
  exact mul_completedDegreeElement_pow_mem_completedExtendedOrderLeftIdeal
    (completedToExtended_mem_completedExtendedOrderLeftIdeal_iff.2 hj) j

@[simp]
theorem completedDegreeCoeff_tsum_completedToExtended_mul_completedDegreeElement_pow
    {u : ℕ → Û} (hu : Tendsto u atTop (𝓝 0)) (j : ℕ) :
    coeff̂ j (∑' k, ι̂ (u k) * d̂ ^ k) = u j := by
  have hs := summable_completedToExtended_mul_completedDegreeElement_pow Φ hΦ hΦs a hu
  have hmap := (hs.hasSum.map (coeff̂ j).toAddMonoidHom
    (continuous_completedDegreeCoeff Φ hΦ hΦs a j)).tsum_eq
  simpa only [LinearMap.toAddMonoidHom_coe, Function.comp_apply,
    completedDegreeCoeff_completedToExtended_mul_pow, tsum_ite_eq] using hmap.symm

/-- **Every element of `Û'` is the sum of its `d̂`-power series.** -/
@[simp]
theorem tsum_completedDegreeCoeff_mul_completedDegreeElement_pow (w : Û') :
    (∑' j, ι̂ (coeff̂ j w) * d̂ ^ j) = w :=
  ext_completedDegreeCoeff Φ hΦ hΦs a fun j ↦
    completedDegreeCoeff_tsum_completedToExtended_mul_completedDegreeElement_pow Φ hΦ hΦs a
      (tendsto_completedDegreeCoeff_atTop Φ hΦ hΦs a w) j

end Completion

section Field

variable {K : Type*} [Field K] [LieAlgebra K L]
  (Φ : LinearMap.BilinForm K L) (hΦ : Φ.lieInvariant L) (hΦs : Φ.IsSymm) (a : K)

/-- Over a field, `U(ĝ') / (ι K - a) → Û'` is injective at every level `a`. -/
theorem toExtendedCompletedEnveloping_injective :
    Function.Injective (toExtendedCompletedEnveloping Φ hΦ hΦs a) := by
  rw [coe_toExtendedCompletedEnveloping, ModuleTower.toLimQuotients_injective_iff,
    iInf_extendedOrderLeftIdeal_natCast, iInf_extendedOrderLeftIdeal]

end Field

section Map

variable {Φ Ψ : LinearMap.BilinForm R L} {hΦ : Φ.lieInvariant L} {hΦs : Φ.IsSymm}
  {hΨ : Ψ.lieInvariant L} {hΨs : Ψ.IsSymm} {a b : R}

local notation "cΦ" => twoCocycleOfBilinear R L Φ hΦ hΦs
local notation "cΨ" => twoCocycleOfBilinear R L Ψ hΨ hΨs
local notation "UK'Ψ" =>
  CentralQuotient R (toExtendedResidueExtension Ψ hΨ hΨs (centralElement cΨ)) b
local notation "UK'Φ" =>
  CentralQuotient R (toExtendedResidueExtension Φ hΦ hΦs (centralElement cΦ)) a
local notation "Û'Ψ" => ExtendedCompletedEnveloping Ψ hΨ hΨs b
local notation "Û'Φ" => ExtendedCompletedEnveloping Φ hΦ hΦs a
local notation "I'Ψ" => extendedOrderLeftIdeal Ψ hΨ hΨs b
local notation "I'Φ" => extendedOrderLeftIdeal Φ hΦ hΦs a
local notation "antiΨ" => extendedOrderLeftIdeal_natCast_antitone Ψ hΨ hΨs b
local notation "antiΦ" => extendedOrderLeftIdeal_natCast_antitone Φ hΦ hΦs a

private def extendedCompletedEnvelopingMapFun (g : UK'Ψ →ₐ[R] UK'Φ)
    (hg : ∀ n : ℕ, ∃ m : ℕ, I'Ψ m ≤ (I'Φ n).comap g.toRingHom.toSemilinearMap) : Û'Ψ → Û'Φ :=
  ModuleTower.limQuotientsMap antiΨ antiΦ g.toRingHom.toSemilinearMap hg

private theorem extendedCompletedEnvelopingMapFun_toExtendedCompletedEnveloping
    (g : UK'Ψ →ₐ[R] UK'Φ)
    (hg : ∀ n : ℕ, ∃ m : ℕ, I'Ψ m ≤ (I'Φ n).comap g.toRingHom.toSemilinearMap) (x : UK'Ψ) :
    extendedCompletedEnvelopingMapFun g hg (toExtendedCompletedEnveloping Ψ hΨ hΨs b x) =
      toExtendedCompletedEnveloping Φ hΦ hΦs a (g x) := by
  rw [extendedCompletedEnvelopingMapFun, coe_toExtendedCompletedEnveloping,
    coe_toExtendedCompletedEnveloping, ModuleTower.limQuotientsMap_toLimQuotients]; rfl

/-- **Functoriality of the completed extended enveloping algebra.** -/
def extendedCompletedEnvelopingMap (g : UK'Ψ →ₐ[R] UK'Φ)
    (hg : ∀ n : ℕ, ∃ m : ℕ, I'Ψ m ≤ (I'Φ n).comap g.toRingHom.toSemilinearMap) : Û'Ψ →ₐ[R] Û'Φ where
  toFun := extendedCompletedEnvelopingMapFun g hg
  map_one' := by
    rw [← map_one (toExtendedCompletedEnveloping Ψ hΨ hΨs b),
      extendedCompletedEnvelopingMapFun_toExtendedCompletedEnveloping, map_one, map_one]
  map_mul' x y := by
    rw [extendedCompletedEnvelopingMapFun]; exact ModuleTower.limQuotientsMap_limMul _ _ _ _ _ x y
  map_zero' := by rw [extendedCompletedEnvelopingMapFun]; exact map_zero _
  map_add' x y := by rw [extendedCompletedEnvelopingMapFun]; exact map_add _ x y
  commutes' r := by
    rw [← (toExtendedCompletedEnveloping Ψ hΨ hΨs b).commutes r,
      extendedCompletedEnvelopingMapFun_toExtendedCompletedEnveloping, g.commutes r,
      (toExtendedCompletedEnveloping Φ hΦ hΦs a).commutes r]

@[simp]
theorem extendedCompletedEnvelopingMap_toLimQuotients (g : UK'Ψ →ₐ[R] UK'Φ)
    (hg : ∀ n : ℕ, ∃ m : ℕ, I'Ψ m ≤ (I'Φ n).comap g.toRingHom.toSemilinearMap) (x : UK'Ψ) :
    extendedCompletedEnvelopingMap g hg (ModuleTower.toLimQuotients _ antiΨ x) =
      ModuleTower.toLimQuotients _ antiΦ (g x) :=
  ModuleTower.limQuotientsMap_toLimQuotients _ _ _ _ x

theorem continuous_extendedCompletedEnvelopingMap (g : UK'Ψ →ₐ[R] UK'Φ)
    (hg : ∀ n : ℕ, ∃ m : ℕ, I'Ψ m ≤ (I'Φ n).comap g.toRingHom.toSemilinearMap) :
    Continuous (extendedCompletedEnvelopingMap g hg) :=
  ModuleTower.continuous_limQuotientsMap _ _ _ _

theorem eq_extendedCompletedEnvelopingMap (g : UK'Ψ →ₐ[R] UK'Φ)
    (hg : ∀ n : ℕ, ∃ m : ℕ, I'Ψ m ≤ (I'Φ n).comap g.toRingHom.toSemilinearMap)
    {φ : Û'Ψ →ₐ[R] Û'Φ} (hφ : Continuous φ)
    (h : ∀ x, φ (toExtendedCompletedEnveloping Ψ hΨ hΨs b x) =
      toExtendedCompletedEnveloping Φ hΦ hΦs a (g x)) :
    φ = extendedCompletedEnvelopingMap g hg :=
  DFunLike.coe_injective <| ModuleTower.eq_limQuotientsMap antiΨ antiΦ
    g.toRingHom.toSemilinearMap hg hφ fun x ↦ by
      have hx := h x
      rw [coe_toExtendedCompletedEnveloping, coe_toExtendedCompletedEnveloping] at hx; exact hx

theorem extendedCompletedEnvelopingMap_mem_completedExtendedOrderLeftIdeal (g : UK'Ψ →ₐ[R] UK'Φ)
    (hg : ∀ n : ℕ, ∃ m : ℕ, I'Ψ m ≤ (I'Φ n).comap g.toRingHom.toSemilinearMap) {n m : ℕ}
    (hm : I'Ψ m ≤ (I'Φ n).comap g.toRingHom.toSemilinearMap) {w : Û'Ψ}
    (hw : w ∈ completedExtendedOrderLeftIdeal Ψ hΨ hΨs b m) :
    extendedCompletedEnvelopingMap g hg w ∈ completedExtendedOrderLeftIdeal Φ hΦ hΦs a n := by
  rw [mem_completedExtendedOrderLeftIdeal] at hw ⊢
  change (extendedOrderQuotientTower Φ hΦ hΦs a).limπ n
    (ModuleTower.limQuotientsMap _ _ g.toRingHom.toSemilinearMap hg w) = 0
  rw [ModuleTower.limπ_limQuotientsMap _ _ _ _ hm (b := 0) (by rw [map_zero, hw]),
    map_zero, map_zero]

private theorem map_comp_eq_id (g : UK'Ψ →ₐ[R] UK'Φ) (g' : UK'Φ →ₐ[R] UK'Ψ)
    (hg : ∀ n : ℕ, ∃ m : ℕ, I'Ψ m ≤ (I'Φ n).comap g.toRingHom.toSemilinearMap)
    (hg' : ∀ n : ℕ, ∃ m : ℕ, I'Φ m ≤ (I'Ψ n).comap g'.toRingHom.toSemilinearMap)
    (h : ∀ x, g (g' x) = x) :
    (extendedCompletedEnvelopingMap g hg).comp (extendedCompletedEnvelopingMap g' hg') =
      AlgHom.id R Û'Φ := by
  have hid : ∀ n : ℕ, ∃ m : ℕ,
      I'Φ m ≤ (I'Φ n).comap (AlgHom.id R UK'Φ).toRingHom.toSemilinearMap :=
    fun n ↦ ⟨n, fun _ hx ↦ by rw [Submodule.mem_comap]; exact hx⟩
  refine (eq_extendedCompletedEnvelopingMap (AlgHom.id R UK'Φ) hid
    ((continuous_extendedCompletedEnvelopingMap g hg).comp
      (continuous_extendedCompletedEnvelopingMap g' hg')) fun x ↦ ?_).trans
    (eq_extendedCompletedEnvelopingMap (AlgHom.id R UK'Φ) hid continuous_id fun _ ↦ rfl).symm
  rw [AlgHom.comp_apply, coe_toExtendedCompletedEnveloping,
    extendedCompletedEnvelopingMap_toLimQuotients,
    extendedCompletedEnvelopingMap_toLimQuotients, h, AlgHom.id_apply]

/-- **Isomorphisms of completed extended enveloping algebras.** -/
def extendedCompletedEnvelopingEquiv (e : UK'Ψ ≃ₐ[R] UK'Φ)
    (he : ∀ n : ℕ, ∃ m : ℕ, I'Ψ m ≤ (I'Φ n).comap e.toAlgHom.toRingHom.toSemilinearMap)
    (he' : ∀ n : ℕ, ∃ m : ℕ, I'Φ m ≤ (I'Ψ n).comap e.symm.toAlgHom.toRingHom.toSemilinearMap) :
    Û'Ψ ≃ₐ[R] Û'Φ :=
  AlgEquiv.ofAlgHom (extendedCompletedEnvelopingMap e.toAlgHom he)
    (extendedCompletedEnvelopingMap e.symm.toAlgHom he')
    (map_comp_eq_id _ _ he he' e.apply_symm_apply) (map_comp_eq_id _ _ he' he e.symm_apply_apply)

@[simp]
theorem extendedCompletedEnvelopingEquiv_toLimQuotients (e : UK'Ψ ≃ₐ[R] UK'Φ)
    (he : ∀ n : ℕ, ∃ m : ℕ, I'Ψ m ≤ (I'Φ n).comap e.toAlgHom.toRingHom.toSemilinearMap)
    (he' : ∀ n : ℕ, ∃ m : ℕ, I'Φ m ≤ (I'Ψ n).comap e.symm.toAlgHom.toRingHom.toSemilinearMap)
    (x : UK'Ψ) :
    extendedCompletedEnvelopingEquiv e he he' (ModuleTower.toLimQuotients _ antiΨ x) =
      ModuleTower.toLimQuotients _ antiΦ (e x) :=
  extendedCompletedEnvelopingMap_toLimQuotients e.toAlgHom he x

@[simp]
theorem extendedCompletedEnvelopingEquiv_symm_toLimQuotients (e : UK'Ψ ≃ₐ[R] UK'Φ)
    (he : ∀ n : ℕ, ∃ m : ℕ, I'Ψ m ≤ (I'Φ n).comap e.toAlgHom.toRingHom.toSemilinearMap)
    (he' : ∀ n : ℕ, ∃ m : ℕ, I'Φ m ≤ (I'Ψ n).comap e.symm.toAlgHom.toRingHom.toSemilinearMap)
    (x : UK'Φ) :
    (extendedCompletedEnvelopingEquiv e he he').symm (ModuleTower.toLimQuotients _ antiΦ x) =
      ModuleTower.toLimQuotients _ antiΨ (e.symm x) :=
  extendedCompletedEnvelopingMap_toLimQuotients e.symm.toAlgHom he' x

theorem continuous_extendedCompletedEnvelopingEquiv (e : UK'Ψ ≃ₐ[R] UK'Φ)
    (he : ∀ n : ℕ, ∃ m : ℕ, I'Ψ m ≤ (I'Φ n).comap e.toAlgHom.toRingHom.toSemilinearMap)
    (he' : ∀ n : ℕ, ∃ m : ℕ, I'Φ m ≤ (I'Ψ n).comap e.symm.toAlgHom.toRingHom.toSemilinearMap) :
    Continuous (extendedCompletedEnvelopingEquiv e he he') :=
  continuous_extendedCompletedEnvelopingMap e.toAlgHom he

theorem continuous_extendedCompletedEnvelopingEquiv_symm (e : UK'Ψ ≃ₐ[R] UK'Φ)
    (he : ∀ n : ℕ, ∃ m : ℕ, I'Ψ m ≤ (I'Φ n).comap e.toAlgHom.toRingHom.toSemilinearMap)
    (he' : ∀ n : ℕ, ∃ m : ℕ, I'Φ m ≤ (I'Ψ n).comap e.symm.toAlgHom.toRingHom.toSemilinearMap) :
    Continuous (extendedCompletedEnvelopingEquiv e he he').symm :=
  continuous_extendedCompletedEnvelopingMap e.symm.toAlgHom he'

end Map

section Level

variable {Φ Ψ : LinearMap.BilinForm R L} (hΦ : Φ.lieInvariant L) (hΦs : Φ.IsSymm)
  (hΨ : Ψ.lieInvariant L) (hΨs : Ψ.IsSymm) {k : R}

local notation "cΦ" => twoCocycleOfBilinear R L Φ hΦ hΦs
local notation "cΨ" => twoCocycleOfBilinear R L Ψ hΨ hΨs
local notation "UK'Ψ" =>
  CentralQuotient R (toExtendedResidueExtension Ψ hΨ hΨs (centralElement cΨ)) 1
local notation "UK'Φ" =>
  CentralQuotient R (toExtendedResidueExtension Φ hΦ hΦs (centralElement cΦ)) k
local notation "eL" => extendedLevelEnvelopingEquiv hΦ hΦs hΨ hΨs
local notation "anti1" => extendedOrderLeftIdeal_natCast_antitone Ψ hΨ hΨs 1
local notation "antik" => extendedOrderLeftIdeal_natCast_antitone Φ hΦ hΦs k

private theorem le_comap_eL (h : Ψ = k • Φ) (n : ℕ) : extendedOrderLeftIdeal Ψ hΨ hΨs 1 n ≤
    (extendedOrderLeftIdeal Φ hΦ hΦs k n).comap (eL h).toAlgHom.toRingHom.toSemilinearMap := by
  intro x hx; rw [Submodule.mem_comap]; change eL h x ∈ _
  exact (extendedLevelEnvelopingEquiv_mem_extendedOrderLeftIdeal_iff h).2 hx

private theorem le_comap_eL_symm (h : Ψ = k • Φ) (n : ℕ) : extendedOrderLeftIdeal Φ hΦ hΦs k n ≤
    (extendedOrderLeftIdeal Ψ hΨ hΨs 1 n).comap (eL h).symm.toAlgHom.toRingHom.toSemilinearMap :=
  fun x hx ↦ by
    rw [Submodule.mem_comap]; change (eL h).symm x ∈ _
    rwa [← extendedLevelEnvelopingEquiv_mem_extendedOrderLeftIdeal_iff h, AlgEquiv.apply_symm_apply]

/-- **The completed level comparison for the extended affine algebra** at `(Ψ, 1)` and `(Φ, k)`. -/
def extendedLevelCompletedEnvelopingEquiv (h : Ψ = k • Φ) :
    ExtendedCompletedEnveloping Ψ hΨ hΨs 1 ≃ₐ[R] ExtendedCompletedEnveloping Φ hΦ hΦs k :=
  extendedCompletedEnvelopingEquiv (eL h) (fun n ↦ ⟨n, le_comap_eL hΦ hΦs hΨ hΨs h n⟩)
    (fun n ↦ ⟨n, le_comap_eL_symm hΦ hΦs hΨ hΨs h n⟩)

local notation "eLC" => extendedLevelCompletedEnvelopingEquiv hΦ hΦs hΨ hΨs

@[simp]
theorem extendedLevelCompletedEnvelopingEquiv_toLimQuotients (h : Ψ = k • Φ) (x : UK'Ψ) :
    eLC h (ModuleTower.toLimQuotients _ anti1 x) = ModuleTower.toLimQuotients _ antik (eL h x) :=
  extendedCompletedEnvelopingEquiv_toLimQuotients _ _ _ x

@[simp]
theorem extendedLevelCompletedEnvelopingEquiv_symm_toLimQuotients (h : Ψ = k • Φ) (x : UK'Φ) :
    (eLC h).symm (ModuleTower.toLimQuotients _ antik x) =
      ModuleTower.toLimQuotients _ anti1 ((eL h).symm x) :=
  extendedCompletedEnvelopingEquiv_symm_toLimQuotients _ _ _ x

theorem continuous_extendedLevelCompletedEnvelopingEquiv (h : Ψ = k • Φ) : Continuous (eLC h) :=
  continuous_extendedCompletedEnvelopingEquiv _ _ _

theorem continuous_extendedLevelCompletedEnvelopingEquiv_symm (h : Ψ = k • Φ) :
    Continuous (eLC h).symm :=
  continuous_extendedCompletedEnvelopingEquiv_symm _ _ _

@[simp]
theorem extendedLevelCompletedEnvelopingEquiv_completedToExtended (h : Ψ = k • Φ)
    (x : CompletedEnveloping Ψ hΨ hΨs 1) :
    eLC h (completedToExtended Ψ hΨ hΨs 1 x) =
      completedToExtended Φ hΦ hΦs k (levelCompletedEnvelopingEquiv hΦ hΦs hΨ hΨs h x) := by
  have hc := continuous_extendedLevelCompletedEnvelopingEquiv hΦ hΦs hΨ hΨs h
  induction x using (denseRange_toCompletedEnveloping Ψ hΨ hΨs 1).induction_on with
  | hp =>
    exact isClosed_eq (hc.comp (continuous_completedToExtended Ψ hΨ hΨs 1))
      ((continuous_completedToExtended Φ hΦ hΦs k).comp
        (continuous_levelCompletedEnvelopingEquiv hΦ hΦs hΨ hΨs h))
  | ih b =>
    rw [completedToExtended_toCompletedEnveloping, coe_toCompletedEnveloping,
      coe_toExtendedCompletedEnveloping, extendedLevelCompletedEnvelopingEquiv_toLimQuotients,
      levelCompletedEnvelopingEquiv_toLimQuotients, completedToExtended_toLimQuotients,
      extendedLevelEnvelopingEquiv_toExtendedEnveloping]

@[simp]
theorem extendedLevelCompletedEnvelopingEquiv_completedDegreeElement (h : Ψ = k • Φ) :
    eLC h (completedDegreeElement Ψ hΨ hΨs 1) = completedDegreeElement Φ hΦ hΦs k := by
  simp [completedDegreeElement]

variable {hΨ hΨs} in
theorem extendedLevelCompletedEnvelopingEquiv_mem_completedExtendedOrderLeftIdeal_iff
    (h : Ψ = k • Φ) {n : ℕ} {w : ExtendedCompletedEnveloping Ψ hΨ hΨs 1} :
    eLC h w ∈ completedExtendedOrderLeftIdeal Φ hΦ hΦs k n ↔
      w ∈ completedExtendedOrderLeftIdeal Ψ hΨ hΨs 1 n := by
  refine ⟨fun hw ↦ ?_, extendedCompletedEnvelopingMap_mem_completedExtendedOrderLeftIdeal _ _
    (le_comap_eL hΦ hΦs hΨ hΨs h n)⟩
  rw [← (eLC h).symm_apply_apply w]
  exact extendedCompletedEnvelopingMap_mem_completedExtendedOrderLeftIdeal _ _
    (le_comap_eL_symm hΦ hΦs hΨ hΨs h n) hw

end Level

end TauCeti.CurrentAlgebra

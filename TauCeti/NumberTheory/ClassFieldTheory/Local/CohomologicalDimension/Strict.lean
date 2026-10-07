/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Local.CohomologicalDimension.AbsoluteGaloisGroup
public import TauCeti.NumberTheory.ClassFieldTheory.Local.Duality.FiniteModule
public import TauCeti.NumberTheory.LocalField.RootsOfUnity.Basic
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Bockstein.Integral
public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologicalDimension.IntegralCriterion
public import TauCeti.Topology.Algebra.Group.ClosedSubgroup

/-!
# The strict cohomological dimension of the absolute Galois group of a local field

For a nonarchimedean local field `K` and a prime `ℓ` invertible in `K`, this file proves

```text
scd_ℓ G_K = 2
```

(`strictCohomologicalDimensionAt_absoluteGaloisGroup_eq_two_of_isUnit`), and in particular
`scd_ℓ G_K = 2` for every prime `ℓ` when `K` has characteristic zero
(`strictCohomologicalDimensionAt_absoluteGaloisGroup_eq_two`).

The lower bound is `cd_ℓ G_K ≤ scd_ℓ G_K` with `cd_ℓ G_K = 2`. For the upper bound, the criterion
`TauCeti.strictCohomologicalDimensionAt_le_iff_forall_openSubgroup` (NSW (3.3.4)) asks, besides
`cd_ℓ G_K ≤ 2`, that the `ℓ`-primary component of `H³(U, ℤ)` vanish for every open subgroup `U`
of `G_K` (`primaryComponent_h3_int_eq_bot_of_isOpen`). The subgroup `U` is the absolute Galois
group of a finite extension `E` of `K`, again a local field, and:

* **`H²(G_E, ℤ/n)` is killed by the exponent of `μₙ(E)`** (`nsmul_H2_zmod_eq_zero`). By local Tate
  duality, `H²(G_E, ℤ/n)` embeds into the dual of `H⁰(G_E, Hom(ℤ/n, μₙ)) = Hom(ℤ/n, μₙ(E))`
  (`TauCeti.ClassFieldTheory.dualityMap2_kummerCoeff_bijective`). Since the `ℓ`-power roots of
  unity of `E` form a finite group of some order `ℓᵐ`
  (`TauCeti.finite_pPowerRootsOfUnity`), `ℓᵐ` kills `H²(G_E, ℤ/ℓᵏ)` for every `k`.
* **`H³(U, ℤ/ℓᵐ) = 0`**, because `cd_ℓ U ≤ cd_ℓ G_K = 2`.

These two facts give the vanishing of the `ℓ`-primary part of `H³(U, ℤ)` through the integral
Bockstein sequences `0 → ℤ → ℤ → ℤ/ℓᵏ → 0`
(`TauCeti.primaryComponent_continuousCohomology_int_eq_bot`). This is the argument of NSW, which
identifies `H³(U, ℤ)(ℓ)` with `H²(U, ℚ_ℓ/ℤ_ℓ)`, the dual of the inverse limit of the `μ_{ℓᵏ}(E)`
under `ℓ`-th powers, which vanishes because `μ_{ℓ^∞}(E)` is finite.

## Main results

* `TauCeti.ClassFieldTheory.nsmul_H2_zmod_eq_zero`: `e • H²(G_K, ℤ/n) = 0` whenever `e` kills
  `μₙ(K)`, for `n` invertible in `K`.
* `TauCeti.ClassFieldTheory.primaryComponent_h3_int_eq_bot_of_isOpen`: the `ℓ`-primary component
  of `H³(U, ℤ)` vanishes for every open subgroup `U` of `G_K`.
* `TauCeti.ClassFieldTheory.strictCohomologicalDimensionAt_absoluteGaloisGroup_eq_two_of_isUnit`:
  `scd_ℓ G_K = 2` for `ℓ` invertible in `K`.
* `TauCeti.ClassFieldTheory.strictCohomologicalDimensionAt_absoluteGaloisGroup_eq_two`:
  **`scd_ℓ G_K = 2`** for a local field `K` of characteristic zero and every prime `ℓ`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (3.3.4) and
  (7.2.5).
* J.-P. Serre, *Galois Cohomology*, Ch. II, §5.3.
-/

public section

namespace TauCeti.ClassFieldTheory

open ContCohomology

attribute [local instance] trivialZModAction integralAction cyclicContinuousSMul

variable {K : Type} [Field K]

/-! ### `H²` with trivial cyclic coefficients -/

section TrivialZMod

variable {n : ℕ} {e : ℕ} [DistribMulAction (AbsoluteGaloisGroup K) (ZMod n)]
  (htriv : ∀ (g : AbsoluteGaloisGroup K) (m : ZMod n), g • m = m)
include htriv

/-- The invariants of `Hom(ℤ/n, μₙ)` are killed by every `e` killing `μₙ(K)`: an invariant
homomorphism is determined by its value at `1`, a root of unity fixed by `G_K`, hence one of `K`. -/
private theorem nsmul_H0_internalHom_eq_zero [NeZero n] (he : ∀ ζ : Kˣ, ζ ^ n = 1 → ζ ^ e = 1)
    (φ : H0 (AbsoluteGaloisGroup K)
      (InternalHom (AbsoluteGaloisGroup K) (ZMod n) (KummerCoeff K n))) :
    e • φ = 0 := by
  -- the value `z = φ 1` is fixed by `G_K`, so its image in `(Kˢ)ˣ` comes from a unit `a` of `K`
  set z := φ.1.toAddMonoidHom 1
  have hz : kummerCoeffIncl K n z ∈ H0 (AbsoluteGaloisGroup K) (UnitsCoeff K) :=
    (FixedPoints.mem_addSubgroup _ _ _).2 fun g ↦ by
      rw [← kummerCoeffIncl_equivariant, ← InternalHom.smul_eq_self_iff.1
        ((FixedPoints.mem_addSubgroup _ _ _).1 φ.2 g) 1, htriv]
  obtain ⟨a, ha⟩ := mem_H0_unitsCoeff_iff.1 hz
  have hzn : ((z.toMul : rootsOfUnity n (SeparableClosure K)) : (SeparableClosure K)ˣ) ^ n = 1 :=
    (mem_rootsOfUnity _ _).1 z.toMul.2
  have han : a ^ n = 1 := by
    refine Units.map_injective (algebraMap K (SeparableClosure K)).injective ?_
    rw [map_pow, map_one, ha, toMul_kummerCoeffIncl, hzn]
  have hze : e • z = 0 := by
    refine Additive.toMul.injective (Subtype.ext ?_)
    rw [toMul_nsmul, SubmonoidClass.coe_pow, toMul_zero, OneMemClass.coe_one,
      ← toMul_kummerCoeffIncl, ← ha, ← map_pow, he a han, map_one]
  -- an additive map out of `ℤ/n` killing `e • 1` is killed by `e`
  refine Subtype.ext (InternalHom.ext (AddMonoidHom.ext fun m ↦ ?_))
  obtain ⟨k, rfl⟩ := ZMod.natCast_zmod_surjective m
  simp only [AddSubgroup.coe_nsmul, InternalHom.toAddMonoidHom_nsmul, AddMonoidHom.nsmul_apply,
    ZeroMemClass.coe_zero, InternalHom.toAddMonoidHom_zero, AddMonoidHom.zero_apply]
  rw [← nsmul_one, map_nsmul, smul_comm, hze, smul_zero]

variable [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ContinuousSMul (AbsoluteGaloisGroup K) (ZMod n)]

/-- **`H²(G_K, ℤ/n)` is killed by the exponent of `μₙ(K)`.** For `n` invertible in the local field
`K` and `G_K` acting trivially on `ℤ/n`, if `e` kills every `n`th root of unity of `K`, then `e`
kills `H²(G_K, ℤ/n)`. -/
theorem nsmul_H2_zmod_eq_zero (hn : IsUnit (n : K)) (he : ∀ ζ : Kˣ, ζ ^ n = 1 → ζ ^ e = 1)
    (y : H2 (AbsoluteGaloisGroup K) (ZMod n)) : e • y = 0 := by
  have : NeZero n := NeZero.of_neZero_natCast K (h := ⟨hn.ne_zero⟩)
  refine (dualityMap2_kummerCoeff_bijective hn (ZMod n) fun a ↦ ?_).1 ?_
  · rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  · ext φ
    rw [map_nsmul, AddMonoidHom.nsmul_apply, ← map_nsmul, nsmul_H0_internalHom_eq_zero htriv he,
      _root_.map_zero, _root_.map_zero, AddMonoidHom.zero_apply]

end TrivialZMod

/-! ### Open subgroups -/

section OpenSubgroup

variable [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] {ℓ : ℕ} [Fact ℓ.Prime]

/-- For an open subgroup `V` of `G_K` and a prime `ℓ` invertible in `K`, a single power `ℓᵐ` kills
`H²(V, ℤ/ℓᵏ)` for every `k`: `V` is the absolute Galois group of a finite extension `E` of `K`,
whose `ℓ`-power roots of unity form a finite group of order `ℓᵐ`. -/
private theorem exists_pow_nsmul_H2_eq_zero (hℓ : IsUnit (ℓ : K))
    (V : Subgroup (AbsoluteGaloisGroup K)) (hV : IsOpen (V : Set (AbsoluteGaloisGroup K))) :
    ∃ m : ℕ, ∀ (k : ℕ) (y : H2 V (ULift (ZMod (ℓ ^ k)))), ℓ ^ m • y = 0 := by
  -- `V` is the subgroup fixing its fixed field `E`, which is finite over `K`.
  obtain ⟨E, _, rfl⟩ : ∃ E : IntermediateField K (SeparableClosure K),
      FiniteDimensional K E ∧ E.val.fieldRange.fixingSubgroup = V := by
    obtain ⟨E, hE⟩ : ∃ E : IntermediateField K (SeparableClosure K), E.fixingSubgroup = V :=
      ⟨_, InfiniteGalois.fixingSubgroup_fixedField ⟨V, Subgroup.isClosed_of_isOpen V hV⟩⟩
    refine ⟨E, ?_, by rw [IntermediateField.fieldRange_val, hE]⟩
    rw [← InfiniteGalois.isOpen_iff_finite, hE]
    exact hV
  -- The canonical structure of nonarchimedean local field on `E`.
  let _ := finiteExtensionValuativeRel K E
  let _ := finiteExtensionNormedFieldTopology K E
  have := finiteExtension_isNonarchimedeanLocalField K E
  have hℓE : IsUnit (ℓ : E) := map_natCast (algebraMap K E) ℓ ▸ hℓ.map (algebraMap K E)
  have hfin := finite_pPowerRootsOfUnity (p := ℓ) hℓE.ne_zero
  obtain ⟨m, hm⟩ := localRootOfUnityOrder_isPow ℓ E hfin
  refine ⟨m, fun k y ↦ ?_⟩
  have : ContinuousSMul (AbsoluteGaloisGroup E) (ZMod (ℓ ^ k)) := ⟨continuous_snd⟩
  -- Transport along `G_E ≃ₜ* V` and apply the bound over `E`.
  have χ : H2 E.val.fieldRange.fixingSubgroup (ULift (ZMod (ℓ ^ k))) ≃+
      H2 (AbsoluteGaloisGroup E) (ZMod (ℓ ^ k)) :=
    explicitMap2Equiv _ (ULift (ZMod (ℓ ^ k))) (AbsoluteGaloisGroup E) (ZMod (ℓ ^ k))
      (absoluteGaloisGroupEquivFixingSubgroup K E E.val) AddEquiv.ulift
      continuous_of_discreteTopology continuous_of_discreteTopology fun _ _ ↦ rfl
  have hn : IsUnit ((ℓ ^ k : ℕ) : E) := Nat.cast_pow (α := E) ℓ k ▸ hℓE.pow k
  -- an `ℓᵏ`-th root of unity of `E` lies in the group of `ℓ`-power roots of unity, of order `ℓᵐ`
  have he (ζ : Eˣ) (hζ : ζ ^ (ℓ ^ k) = 1) : ζ ^ (ℓ ^ m) = 1 := by
    have hmem : ζ ∈ pPowerRootsOfUnity ℓ E := (mem_pPowerRootsOfUnity_iff ℓ E ζ).2 ⟨k, hζ⟩
    have h := pow_card_eq_one' (G := pPowerRootsOfUnity ℓ E) (x := ⟨ζ, hmem⟩)
    rw [← localRootOfUnityOrder_def ℓ E hfin, hm] at h
    exact congrArg Subtype.val h
  exact χ.injective ((map_nsmul χ (ℓ ^ m) y).trans
    ((nsmul_H2_zmod_eq_zero (K := E) (fun _ _ ↦ rfl) hn he (χ y)).trans (map_zero χ).symm))

/-- **The `ℓ`-primary part of `H³(U, ℤ)` vanishes** for every open subgroup `U` of `G_K`, the
integers carrying the trivial action, for a prime `ℓ` invertible in the local field `K`. -/
theorem primaryComponent_h3_int_eq_bot_of_isOpen (hℓ : IsUnit (ℓ : K))
    (U : Subgroup (Field.absoluteGaloisGroup K))
    (hU : IsOpen (U : Set (Field.absoluteGaloisGroup K))) :
    AddCommGroup.primaryComponent (continuousCohomology 3
      (TopRep.of (ContRepresentation.trivial ℤ U (ULift.{0} ℤ)))) ℓ = ⊥ := by
  have : CompactSpace U := isCompact_iff_compactSpace.1 (U.isClosed_of_isOpen hU).isCompact
  have : LocallyCompactSpace U := (U.isClosed_of_isOpen hU).locallyCompactSpace
  -- some `ℓᵐ` kills `H²(U, ℤ/ℓᵏ)` for every `k`, and `H³(U, ℤ/ℓᵐ) = 0`
  -- the image `V` of `U` in Tau Ceti's model of `G_K`, and the bound on `H²(V, ℤ/ℓᵏ)`
  obtain ⟨V, hV, ⟨φ⟩⟩ : ∃ V : Subgroup (AbsoluteGaloisGroup K),
      IsOpen (V : Set (AbsoluteGaloisGroup K)) ∧ Nonempty (U ≃ₜ* V) :=
    ⟨_, by rw [Subgroup.coe_map]; exact (absoluteGaloisGroupRestrictEquiv K).isOpenMap _ hU,
      ⟨(absoluteGaloisGroupRestrictEquiv K).subgroupMap U⟩⟩
  obtain ⟨m, hm⟩ := exists_pow_nsmul_H2_eq_zero hℓ _ hV
  -- `H³(U, ℤ/ℓᵐ) = 0`, since `cd_ℓ U ≤ 2`
  have hcd : CohomologicalDimensionLE.{0} ℓ U 2 :=
    ((cohomologicalDimensionAt_le_iff ℓ _ 2).1
      (cohomologicalDimensionAt_absoluteGaloisGroup_eq_two_of_isUnit hℓ).le).of_isClosed
        (U.isClosed_of_isOpen hU)
  have : Subsingleton (continuousCohomology 3 (ofDiscreteModule ℤ U (ULift (ZMod (ℓ ^ m))))) :=
    cohomologicalDimensionLE_iff.1 hcd _
      (isPPrimaryTorsion_of_natCard_eq_pow (by rw [Nat.card_ulift, Nat.card_zmod])) 3 (by norm_num)
  have h := primaryComponent_continuousCohomology_int_eq_bot U ℓ m 2 fun k y ↦ ?_
  · have hZ : ofDiscreteModule ℤ U (ULift.{0} ℤ) =
        TopRep.of (ContRepresentation.trivial ℤ U (ULift.{0} ℤ)) :=
      -- `ofDiscreteModule` is `TopRep.of` of the representation `g ↦ (g • ·)`, and the action of
      -- `integralAction` is trivial by definition
      congrArg TopRep.of (DFunLike.ext _ _ fun g ↦ ContinuousLinearMap.ext fun x ↦
        (ofDiscreteModule_ρ_apply_apply g x).trans (ContRepresentation.trivial_apply g x).symm)
    rw [← hZ]
    exact h
  · -- transport the bound along `U ≃ₜ* V`
    have χ : H2 V (ULift (ZMod (ℓ ^ k))) ≃+
        continuousCohomology 2 (ofDiscreteModule ℤ U (ULift (ZMod (ℓ ^ k)))) :=
      (explicitMap2Equiv _ _ U _ φ (AddEquiv.refl _) continuous_id continuous_id
        fun _ _ ↦ rfl).trans (explicitH2AddEquivContinuousCohomology U _)
    obtain ⟨z, rfl⟩ := χ.surjective y
    exact (map_nsmul χ _ z).symm.trans ((congrArg χ (hm k z)).trans (map_zero χ))

end OpenSubgroup

/-! ### The strict cohomological dimension -/

variable [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- **`scd_ℓ G_K = 2`** for a nonarchimedean local field `K` and a prime `ℓ` invertible in `K`
(NSW (7.2.5)). -/
theorem strictCohomologicalDimensionAt_absoluteGaloisGroup_eq_two_of_isUnit {ℓ : ℕ}
    [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : K)) :
    strictCohomologicalDimensionAt.{0} ℓ (Field.absoluteGaloisGroup K) = 2 := by
  have hcd := cohomologicalDimensionAt_absoluteGaloisGroup_eq_two_of_isUnit hℓ
  refine le_antisymm ((strictCohomologicalDimensionAt_le_iff_forall_openSubgroup Fact.out 2).2
    ⟨hcd.le, fun U ↦ primaryComponent_h3_int_eq_bot_of_isOpen hℓ U U.isOpen⟩) ?_
  rw [← hcd]
  exact cohomologicalDimensionAt_le_strictCohomologicalDimensionAt _ _

/-- **`scd_ℓ G_K = 2`** for every prime `ℓ` and every nonarchimedean local field `K` of
characteristic zero, that is every finite extension of some `ℚ_p` (NSW (7.2.5)): every prime is
invertible in `K`. -/
theorem strictCohomologicalDimensionAt_absoluteGaloisGroup_eq_two [CharZero K] (ℓ : ℕ)
    [Fact ℓ.Prime] : strictCohomologicalDimensionAt.{0} ℓ (Field.absoluteGaloisGroup K) = 2 :=
  strictCohomologicalDimensionAt_absoluteGaloisGroup_eq_two_of_isUnit
    (Nat.cast_ne_zero.2 (Fact.out : ℓ.Prime).ne_zero).isUnit

end TauCeti.ClassFieldTheory

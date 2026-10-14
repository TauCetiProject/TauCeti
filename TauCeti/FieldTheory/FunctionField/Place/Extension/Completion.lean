/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Place.Completion.Congr
public import TauCeti.FieldTheory.FunctionField.Place.Extension.LocalRamificationGroup

/-!
# The decomposition group acts on the completion

Let `F' / F` be an extension of fields, `k` a subfield of `F`, and `P` a place of `F' / k`. An
element `σ` of the decomposition group of `P` preserves the valuation of `P`, so it extends by
continuity to an automorphism of the completion `F'_P` preserving the completed valuation ring
`𝒪̂_P`. This gives a homomorphism

`Place.completionDecompositionHom F P : G_Z(P) →* G_Z(P̂)`

from the decomposition group of `P` to the decomposition group of the completed valuation ring
in `Aut_k(F'_P)`. It is injective, since `F'` is dense in `F'_P`.

The lower ramification groups do not change under completion: `σ` lies in `G_i(P)` exactly when
its extension acts trivially on `𝒪̂_P ⧸ 𝔪̂ ^ (i + 1)`, that is, when the extension lies in the
`i`-th ramification group of the action on the complete discrete valuation ring `𝒪̂_P`. Indeed,
`𝒪_P → 𝒪̂_P` induces isomorphisms `𝒪_P ⧸ 𝔪 ^ n ≃ 𝒪̂_P ⧸ 𝔪̂ ^ n`, so the two congruence
conditions agree.

## Main definitions

* `TauCeti.Place.completionDecompositionHom`: the action of the decomposition group of `P` on the
  completion at `P`, as a homomorphism into the decomposition group of the completed valuation
  ring.

## Main results

* `TauCeti.Place.completionDecompositionHom_completionEmbedding`: the action extends that of the
  decomposition group on `F'`.
* `TauCeti.Place.completionDecompositionHom_injective`: the action is faithful.
* `TauCeti.Place.ramificationGroup_eq_comap_completionDecompositionHom`: **the ramification groups
  of `P` are those of the complete discrete valuation ring `𝒪̂_P`**, pulled back along
  `completionDecompositionHom`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Definition 3.8.4.
* J.-P. Serre, *Local Fields*, Chapter II, Section 3 and Chapter IV, Section 1.
-/

public section

namespace TauCeti

namespace Place

variable {k F F' : Type*} [Field k] [Field F] [Field F']
variable [Algebra k F] [Algebra k F'] [Algebra F F'] [IsScalarTower k F F']
variable (F) (P : Place k F')

/-- An element of the decomposition group of `P`, viewed as a `k`-automorphism, preserves the
valuation of `P`. -/
private theorem valuation_restrictScalars_apply (g : P.integers.decompositionSubgroup F) (x : F') :
    P.valuation (((g : F' ≃ₐ[F] F').restrictScalars k) x) = P.valuation x :=
  valuation_decompositionSubgroup_apply F P g x

/-- **The action of the decomposition group on the completion**: an element of the decomposition
group of `P` extends by continuity to an automorphism of the completion at `P` that preserves the
completed valuation ring. -/
noncomputable def completionDecompositionHom :
    P.integers.decompositionSubgroup F →* P.completionPlace.integers.decompositionSubgroup k where
  toFun g := ⟨completionCongr P P _ (valuation_restrictScalars_apply F P g),
    completionCongr_mem_decompositionSubgroup _ _⟩
  map_one' := Subtype.ext <| AlgEquiv.ext fun x ↦ DFunLike.congr_fun (completionCongr_refl P) x
  map_mul' g h := Subtype.ext <| AlgEquiv.ext fun x ↦ (DFunLike.congr_fun
    (completionCongr_trans (valuation_restrictScalars_apply F P h)
      (valuation_restrictScalars_apply F P g)) x).symm

variable {F P}

/-- An element of the decomposition group acts on the completion by `completionCongr`. -/
theorem coe_completionDecompositionHom (g : P.integers.decompositionSubgroup F) :
    (completionDecompositionHom F P g : P.Completion ≃ₐ[k] P.Completion) =
      completionCongr P P ((g : F' ≃ₐ[F] F').restrictScalars k) (fun x ↦ by
        rw [AlgEquiv.restrictScalars_apply, valuation_decompositionSubgroup_apply]) :=
  (rfl)

/-- The action of the decomposition group on the completion extends its action on `F'`. -/
@[simp]
theorem completionDecompositionHom_completionEmbedding (g : P.integers.decompositionSubgroup F)
    (x : F') :
    (completionDecompositionHom F P g : P.Completion ≃ₐ[k] P.Completion)
        (P.completionEmbedding x) =
      P.completionEmbedding ((g : F' ≃ₐ[F] F') x) := by
  rw [coe_completionDecompositionHom, completionCongr_completionEmbedding,
    AlgEquiv.restrictScalars_apply]

/-- The action of the decomposition group on the completion is continuous. -/
theorem continuous_completionDecompositionHom (g : P.integers.decompositionSubgroup F) :
    Continuous (completionDecompositionHom F P g : P.Completion ≃ₐ[k] P.Completion) := by
  rw [coe_completionDecompositionHom]
  exact continuous_completionCongr _

/-- On the completed valuation ring, the action of the decomposition group extends its action on
the valuation ring of `P`. -/
theorem completionDecompositionHom_smul_completionIntegersEmbedding
    (g : P.integers.decompositionSubgroup F) (x : P.integers) :
    completionDecompositionHom F P g • P.completionIntegersEmbedding x =
      P.completionIntegersEmbedding (g • x) := by
  ext
  rw [ValuationSubring.coe_decompositionSubgroup_smul, completionIntegersEmbedding_apply,
    completionIntegersEmbedding_apply, completionDecompositionHom_completionEmbedding,
    ValuationSubring.coe_decompositionSubgroup_smul]

variable (F P) in
/-- The decomposition group of `P` acts faithfully on the completion at `P`. -/
theorem completionDecompositionHom_injective :
    Function.Injective (completionDecompositionHom F P) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  ext x
  have h := congrArg (fun τ : P.completionPlace.integers.decompositionSubgroup k ↦
    (τ : P.Completion ≃ₐ[k] P.Completion) (P.completionEmbedding x)) hg
  simp only [completionDecompositionHom_completionEmbedding, OneMemClass.coe_one,
    AlgEquiv.one_apply] at h
  exact P.completionEmbedding.injective h

variable (F P) in
/-- **The ramification groups do not change under completion.** The `i`-th ramification group of
`P` is the preimage, under the action on the completion, of the `i`-th ramification group of the
action on the complete discrete valuation ring `𝒪̂_P`. -/
theorem ramificationGroup_eq_comap_completionDecompositionHom (i : ℕ) :
    ramificationGroup F P i =
      (IsLocalRing.ramificationGroup (P.completionPlace.integers.decompositionSubgroup k)
        P.completionPlace.integers i).comap (completionDecompositionHom F P) := by
  rw [ramificationGroup_eq_isLocalRing_ramificationGroup]
  refine IsLocalRing.ramificationGroup_eq_comap_of_comap_maximalIdeal_pow _
    P.completionIntegersEmbedding.toRingHom
    (fun g x ↦ (completionDecompositionHom_smul_completionIntegersEmbedding g x).symm)
    (fun n ↦ ?_) (fun n y ↦ ?_) i
  · ext x
    rw [Ideal.mem_comap, mem_maximalIdeal_pow_iff_coe_mem_filtration,
      mem_maximalIdeal_pow_iff_coe_mem_filtration, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      completionIntegersEmbedding_apply, completionEmbedding_mem_filtration_iff]
  · -- approximate `y` to order `n` by a function in the valuation ring of `P`
    obtain ⟨x, hx⟩ := P.exists_filtration_sub_completionEmbedding_mem (Nat.cast_nonneg n)
      ⟨y, P.completionPlace.mem_filtration_zero_iff.mpr y.2⟩
    refine ⟨⟨x, P.mem_filtration_zero_iff.mp x.2⟩, ?_⟩
    rw [mem_maximalIdeal_pow_iff_coe_mem_filtration, AddSubgroupClass.coe_sub,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, completionIntegersEmbedding_apply]
    exact hx

end Place

end TauCeti

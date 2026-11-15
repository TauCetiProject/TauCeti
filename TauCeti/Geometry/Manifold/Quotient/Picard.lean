/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Quotient.AssociatedBundle
public import TauCeti.Geometry.Manifold.VectorBundle.FiniteRank.Picard
public import TauCeti.Topology.Covering.Proper
public import TauCeti.Topology.Covering.Quotient
public import Mathlib.GroupTheory.OrderOfElement

/-!
# The character homomorphism into the `C^n` and holomorphic Picard group

Let `p : E → X` be a quotient covering map for a group `G` (`IsQuotientCoveringMap p G`). For a
character `χ : G →* 𝕜ˣ` of the deck group, the point-indexed core
`IsQuotientCoveringMap.characterFiniteRankCore χ` has locally constant transitions, so for every
model `IB` on `X` and every regularity `n` it defines an object
`IsQuotientCoveringMap.characterContMDiffCore IB n χ` of `ContMDiffFiniteRankBundleCore IB n X`
whose total space is `C^n`-diffeomorphic over `X` to `(hp.characterCore χ).TotalSpace`
(`IsQuotientCoveringMap.characterFiniteRankCoreDiffeomorph`).

In `ContMDiffFiniteRankBundleCore IB n X`, character line bundles satisfy canonical `C^n`
isomorphisms

* `L_1 ≅ 𝟙_` (`characterContMDiffCoreOneIso`),
* `L_χ ⊗ L_ψ ≅ L_{χ * ψ}` (`characterContMDiffCoreMulIso`),
* `L_χ^{\otimes m} ≅ L_{χ ^ m}` (`characterContMDiffCoreTensorPowerIso`),
* `L_χ^{\otimes \operatorname{orderOf} χ} ≅ 𝟙_` (`characterContMDiffCoreTensorPowerOrderOfIsoUnit`).

Consequently `χ ↦ [L_χ]` is a group homomorphism
`IsQuotientCoveringMap.characterPicardHom IB n : (G →* 𝕜ˣ) →* ContMDiffPicardGroup IB n X`, and
the order of `[L_χ]` in `ContMDiffPicardGroup IB n X` divides `orderOf χ` (and `Nat.card G`).

When `𝕜` is complete and `p` is a `C^n` local diffeomorphism, global `C^n` triviality of `L_χ` is
decided by equivariant functions on `E`:

* `characterPicardHom_eq_one_iff`: `[L_χ] = 1` if and only if there is a nowhere-vanishing `C^n`
  function `f : E → 𝕜` with `f (g • y) = χ g * f y`.
* `orderOf_characterPicardHom_eq_iff`, `orderOf_characterPicardHom_eq_iff_forall_lt`: exact-order
  characterization of `[L_χ]` in `ContMDiffPicardGroup IB n X` in terms of non-existence of
  nowhere-vanishing `χ ^ m`-equivariant `C^n` functions on `E` for `0 < m < orderOf χ`.

Over `ℂ` at positive regularity `n ≠ 0` (in particular `n = ∞` or `n = ω`), if `p` is
differentiable and the total space `E` is a compact connected boundaryless complex manifold — for
instance whenever `X` is compact, `E` is connected, and `G` is finite — every holomorphic function
on `E` is constant, so no nontrivial character admits a globally trivial line bundle:

* `characterPicardHom_injective`: `(G →* ℂˣ) →* ContMDiffPicardGroup IB n X` is injective;
* `orderOf_characterPicardHom_eq`: the order of `[L_χ]` in the holomorphic Picard group equals
  `orderOf χ`.

## References

* Daniel Huybrechts, *Complex Geometry: An Introduction*, Springer, 2005, Section 2.2.
* Otto Forster, *Lectures on Riemann Surfaces*, Springer, 1981, §§4–5.
-/

public section

open Bundle CategoryTheory Filter Module MonoidalCategory Set Topology
open TauCeti (ContMDiffFiniteRankBundleCore ContMDiffPicardGroup FiniteRankBundleCore)
open scoped Manifold ContDiff

namespace IsQuotientCoveringMap

section Topology

/-- The total space of a quotient covering map of a compact space by a finite group is compact. -/
theorem compactSpace {E X G : Type*} [TopologicalSpace E] [TopologicalSpace X]
    [Group G] [MulAction G E] {p : E → X} (hp : IsQuotientCoveringMap p G)
    [CompactSpace X] [Finite G] : CompactSpace E :=
  isCompact_univ_iff.mp <| by
    simpa using (hp.isCoveringMap.isProperMap hp.finite_fiber).isCompact_preimage
      (isCompact_univ (X := X))

end Topology

section General

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*} [TopologicalSpace HB]
  (IB : ModelWithCorners 𝕜 EB HB) (n : ℕ∞ω)
  {E X G : Type*} [TopologicalSpace E] [TopologicalSpace X] [ChartedSpace HB X]
  [Group G] [MulAction G E] {p : E → X} (hp : IsQuotientCoveringMap p G)

/-- The point-indexed finite-rank core of a character has locally constant transitions, so it is a
`C^n` vector bundle for every model of the base and every regularity. -/
instance isContMDiff_characterFiniteRankCore (χ : G →* 𝕜ˣ) :
    (hp.characterFiniteRankCore χ).core.IsContMDiff IB n where
  contMDiffOn_coordChange _ _ _ hx :=
    (contMDiffAt_const.congr_of_eventuallyEq
      (hp.eventually_characterFiniteRankCore_coordChange_eq χ hx)).contMDiffWithinAt

/-- Total-space `C^n` diffeomorphism identifying `(hp.characterFiniteRankCore χ).core.TotalSpace`
with `(hp.characterCore χ).TotalSpace` over `X`. -/
noncomputable def characterFiniteRankCoreDiffeomorph (χ : G →* 𝕜ˣ) :
    (hp.characterFiniteRankCore χ).core.TotalSpace ≃ₘ^n⟮IB.prod
      𝓘(𝕜, Fin (hp.characterFiniteRankCore χ).rank → 𝕜), IB.prod 𝓘(𝕜)⟯
      (hp.characterCore χ).TotalSpace where
  toFun p₀ := ⟨p₀.1, (p₀.2 : Fin (hp.characterFiniteRankCore χ).rank → 𝕜) ⟨0, by simp⟩⟩
  invFun q := ⟨q.1, (fun _ ↦ (q.2 : 𝕜) : Fin (hp.characterFiniteRankCore χ).rank → 𝕜)⟩
  left_inv p₀ := by
    simpa only [characterFiniteRankCoreHomeomorph_apply,
      characterFiniteRankCoreHomeomorph_symm_apply] using
      (hp.characterFiniteRankCoreHomeomorph χ).symm_apply_apply p₀
  right_inv := fun ⟨_, _⟩ ↦ rfl
  contMDiff_toFun p₀ := by
    let P : (Fin (hp.characterFiniteRankCore χ).rank → 𝕜) →L[𝕜] 𝕜 :=
      ContinuousLinearMap.proj ⟨0, by simp⟩
    obtain ⟨hb, hp₀'⟩ := Bundle.contMDiffAt_totalSpace_iff.mp
      (contMDiffAt_id (I := IB.prod 𝓘(𝕜, Fin (hp.characterFiniteRankCore χ).rank → 𝕜)) (x := p₀))
    refine Bundle.contMDiffAt_totalSpace_iff.mpr ⟨hb, ?_⟩
    exact (funext fun z ↦ hp.trivializationAt_characterCore_snd χ p₀.1 z) ▸
      P.contMDiff.contMDiffAt.comp p₀ hp₀'
  contMDiff_invFun q := by
    let L : 𝕜 →L[𝕜] (Fin (hp.characterFiniteRankCore χ).rank → 𝕜) :=
      ContinuousLinearMap.pi fun _ ↦ ContinuousLinearMap.id 𝕜 𝕜
    obtain ⟨hb, hq'⟩ := Bundle.contMDiffAt_totalSpace_iff.mp
      (contMDiffAt_id (I := IB.prod 𝓘(𝕜)) (x := q))
    refine Bundle.contMDiffAt_totalSpace_iff.mpr ⟨hb, ?_⟩
    exact (funext fun z ↦ funext fun k ↦
        hp.trivializationAt_characterFiniteRankCore_snd χ q.1 z k) ▸
      L.contMDiff.contMDiffAt.comp q hq'

@[simp] theorem characterFiniteRankCoreDiffeomorph_apply (χ : G →* 𝕜ˣ)
    (p₀ : (hp.characterFiniteRankCore χ).core.TotalSpace) :
    hp.characterFiniteRankCoreDiffeomorph IB n χ p₀ =
      ⟨p₀.1, (p₀.2 : Fin (hp.characterFiniteRankCore χ).rank → 𝕜) ⟨0, by simp⟩⟩ := (rfl)

@[simp] theorem characterFiniteRankCoreDiffeomorph_symm_apply (χ : G →* 𝕜ˣ)
    (q : (hp.characterCore χ).TotalSpace) :
    (hp.characterFiniteRankCoreDiffeomorph IB n χ).symm q =
      ⟨q.1, (fun _ ↦ (q.2 : 𝕜) : Fin (hp.characterFiniteRankCore χ).rank → 𝕜)⟩ := (rfl)

/-- Nowhere-vanishing `C^n` sections of `hp.characterFiniteRankCore χ` correspond to
nowhere-vanishing `C^n` sections of `hp.characterCore χ`. -/
theorem exists_section_ne_zero_characterFiniteRankCore_iff (χ : G →* 𝕜ˣ) :
    (∃ σ : ∀ x, (hp.characterFiniteRankCore χ).core.Fiber x,
      ContMDiff IB (IB.prod 𝓘(𝕜, Fin (hp.characterFiniteRankCore χ).rank → 𝕜)) n
        (fun x ↦ TotalSpace.mk' (Fin (hp.characterFiniteRankCore χ).rank → 𝕜) x (σ x)) ∧
      ∀ x, σ x ≠ 0) ↔
    ∃ τ : ∀ x, (hp.characterCore χ).Fiber x,
      ContMDiff IB (IB.prod 𝓘(𝕜)) n (fun x ↦ TotalSpace.mk' 𝕜 x (τ x)) ∧
      ∀ x, τ x ≠ 0 := by
  let k₀ : Fin (hp.characterFiniteRankCore χ).rank := ⟨0, by simp⟩
  constructor
  · rintro ⟨σ, hσ, hσ₀⟩
    refine ⟨fun x ↦ (σ x : Fin (hp.characterFiniteRankCore χ).rank → 𝕜) k₀,
      ((hp.characterFiniteRankCoreDiffeomorph IB n χ).contMDiff.comp hσ).congr fun _ ↦ rfl,
      fun x h0 ↦ hσ₀ x ?_⟩
    let v : Fin (hp.characterFiniteRankCore χ).rank → 𝕜 := σ x
    change v = 0
    ext k; rw [show k = k₀ from Fin.ext (Nat.lt_one_iff.mp k.2)]; exact h0
  · rintro ⟨τ, hτ, hτ₀⟩
    exact ⟨fun x _ ↦ (τ x : 𝕜),
      ((hp.characterFiniteRankCoreDiffeomorph IB n χ).symm.contMDiff.comp hτ).congr fun _ ↦ rfl,
      fun x h0 ↦ hτ₀ x (congrFun h0 k₀)⟩

/-- The `C^n` line-bundle core over `X` attached to a character `χ : G →* 𝕜ˣ` of the deck group. -/
noncomputable def characterContMDiffCore (χ : G →* 𝕜ˣ) :
    ContMDiffFiniteRankBundleCore IB n X :=
  ⟨hp.characterFiniteRankCore χ, inferInstance⟩

@[simp] theorem toCore_characterContMDiffCore (χ : G →* 𝕜ˣ) :
    (hp.characterContMDiffCore IB n χ).toCore = hp.characterFiniteRankCore χ := (rfl)

theorem rank_characterContMDiffCore (χ : G →* 𝕜ˣ) :
    (hp.characterContMDiffCore IB n χ).toCore.rank = 1 :=
  hp.rank_characterFiniteRankCore χ

/-- Equality of characters induces a canonical `C^n` isomorphism of their cores. -/
noncomputable def characterContMDiffCoreCongr {χ ψ : G →* 𝕜ˣ} (h : χ = ψ) :
    hp.characterContMDiffCore IB n χ ≅ hp.characterContMDiffCore IB n ψ :=
  eqToIso (congrArg (hp.characterContMDiffCore IB n) h)

/-- The `C^n` core of the trivial character is canonically isomorphic in
`ContMDiffFiniteRankBundleCore IB n X` to the monoidal unit. -/
noncomputable def characterContMDiffCoreOneIso :
    hp.characterContMDiffCore IB n (1 : G →* 𝕜ˣ) ≅ 𝟙_ (ContMDiffFiniteRankBundleCore IB n X) :=
  ContMDiffFiniteRankBundleCore.isoTensorUnitOfCoordChangeEqId
    (hp.characterContMDiffCore IB n 1)
    (ContinuousLinearEquiv.piCongrLeft 𝕜
      (fun _ : Fin (𝟙_ (FiniteRankBundleCore 𝕜 X)).rank ↦ 𝕜) (finCongr (by simp)))
    fun i j x _ _ ↦ by
      rw [toCore_characterContMDiffCore, characterFiniteRankCore_coordChange,
        MonoidHom.one_apply, Units.val_one, one_smul]

/-- **Tensor multiplicativity of `C^n` and holomorphic character line bundles.** For characters
`χ, ψ : G →* 𝕜ˣ` of the deck group, `L_χ ⊗ L_ψ ≅ L_{χ * ψ}` in
`ContMDiffFiniteRankBundleCore IB n X`. -/
noncomputable def characterContMDiffCoreMulIso (χ ψ : G →* 𝕜ˣ) :
    hp.characterContMDiffCore IB n χ ⊗ hp.characterContMDiffCore IB n ψ ≅
      hp.characterContMDiffCore IB n (χ * ψ) :=
  ContMDiffFiniteRankBundleCore.constIso
    (fun i ↦ by
      change (hp.characterFiniteRankCore χ).core.baseSet i ∩
          (hp.characterFiniteRankCore ψ).core.baseSet i =
        (hp.characterFiniteRankCore (χ * ψ)).core.baseSet i
      simp only [characterFiniteRankCore_baseSet, Set.inter_self])
    (hp.characterMulFibreEquiv χ ψ)
    fun i j x _ _ ↦ hp.characterFiniteRankCore_mul_intertwine χ ψ i j x

/-- **Tensor powers of a `C^n` character line bundle.** For every `m : ℕ`, the `m`-th tensor power
of `hp.characterContMDiffCore IB n χ` is canonically isomorphic to
`hp.characterContMDiffCore IB n (χ ^ m)`. -/
noncomputable def characterContMDiffCoreTensorPowerIso (χ : G →* 𝕜ˣ) :
    ∀ m : ℕ, (hp.characterContMDiffCore IB n χ).tensorPower m ≅
      hp.characterContMDiffCore IB n (χ ^ m)
  | 0 => (hp.characterContMDiffCoreOneIso IB n).symm ≪≫
      hp.characterContMDiffCoreCongr IB n (pow_zero χ).symm
  | m + 1 => (characterContMDiffCoreTensorPowerIso χ m ⊗ᵢ
        Iso.refl (hp.characterContMDiffCore IB n χ)) ≪≫
      hp.characterContMDiffCoreMulIso IB n (χ ^ m) χ ≪≫
      hp.characterContMDiffCoreCongr IB n (pow_succ χ m).symm

/-- For every character `χ : G →* 𝕜ˣ`, the `orderOf χ`-th tensor power of `L_χ` is canonically
isomorphic in `ContMDiffFiniteRankBundleCore IB n X` to the trivial line bundle `𝟙_`. -/
noncomputable def characterContMDiffCoreTensorPowerOrderOfIsoUnit (χ : G →* 𝕜ˣ) :
    (hp.characterContMDiffCore IB n χ).tensorPower (orderOf χ) ≅
      𝟙_ (ContMDiffFiniteRankBundleCore IB n X) :=
  hp.characterContMDiffCoreTensorPowerIso IB n χ (orderOf χ) ≪≫
    hp.characterContMDiffCoreCongr IB n (pow_orderOf_eq_one χ) ≪≫
    hp.characterContMDiffCoreOneIso IB n

/-- For every character `χ : G →* 𝕜ˣ`, `χ ^ Nat.card G = 1`. -/
private theorem pow_natCard_eq_one (χ : G →* 𝕜ˣ) : χ ^ Nat.card G = 1 := by
  ext g; simp [← map_pow]

/-- The `Nat.card G`-th tensor power of `L_χ` is canonically isomorphic in
`ContMDiffFiniteRankBundleCore IB n X` to the trivial line bundle `𝟙_`. -/
noncomputable def characterContMDiffCoreTensorPowerNatCardIsoUnit (χ : G →* 𝕜ˣ) :
    (hp.characterContMDiffCore IB n χ).tensorPower (Nat.card G) ≅
      𝟙_ (ContMDiffFiniteRankBundleCore IB n X) :=
  hp.characterContMDiffCoreTensorPowerIso IB n χ (Nat.card G) ≪≫
    hp.characterContMDiffCoreCongr IB n (pow_natCard_eq_one χ) ≪≫
    hp.characterContMDiffCoreOneIso IB n

/-- **The character homomorphism into the `C^n` Picard group.** Sends a character `χ : G →* 𝕜ˣ` of
the deck group to the isomorphism class of `hp.characterContMDiffCore IB n χ` in
`ContMDiffPicardGroup IB n X`. Over `𝓘(ℂ, EB)` with `n = ∞`, this lands in the holomorphic Picard
group of `X`. -/
noncomputable def characterPicardHom : (G →* 𝕜ˣ) →* ContMDiffPicardGroup IB n X where
  toFun χ := ContMDiffPicardGroup.mkOfTensorIsoUnit
    (hp.characterContMDiffCoreMulIso IB n χ χ⁻¹ ≪≫
      hp.characterContMDiffCoreCongr IB n (mul_inv_cancel χ) ≪≫
      hp.characterContMDiffCoreOneIso IB n)
  map_one' := Units.ext <| by
    rw [ContMDiffPicardGroup.val_mkOfTensorIsoUnit, Units.val_one, Skeleton.one_eq]
    exact Quotient.sound ⟨hp.characterContMDiffCoreOneIso IB n⟩
  map_mul' χ ψ := Units.ext <| by
    rw [Units.val_mul, ContMDiffPicardGroup.val_mkOfTensorIsoUnit,
      ContMDiffPicardGroup.val_mkOfTensorIsoUnit, ContMDiffPicardGroup.val_mkOfTensorIsoUnit,
      ← Skeleton.toSkeleton_tensorObj]
    exact Quotient.sound ⟨(hp.characterContMDiffCoreMulIso IB n χ ψ).symm⟩

@[simp] theorem val_characterPicardHom_apply (χ : G →* 𝕜ˣ) :
    (hp.characterPicardHom IB n χ : Skeleton (ContMDiffFiniteRankBundleCore IB n X)) =
      toSkeleton (hp.characterContMDiffCore IB n χ) :=
  ContMDiffPicardGroup.val_mkOfTensorIsoUnit _

theorem characterPicardHom_eq_one_iff_nonempty_iso (χ : G →* 𝕜ˣ) :
    hp.characterPicardHom IB n χ = 1 ↔
      Nonempty (hp.characterContMDiffCore IB n χ ≅ 𝟙_ (ContMDiffFiniteRankBundleCore IB n X)) :=
  ContMDiffPicardGroup.mkOfTensorIsoUnit_eq_one_iff _

theorem characterPicardHom_pow_eq_one_iff_nonempty_iso (χ : G →* 𝕜ˣ) (m : ℕ) :
    hp.characterPicardHom IB n χ ^ m = 1 ↔
      Nonempty ((hp.characterContMDiffCore IB n χ).tensorPower m ≅
        𝟙_ (ContMDiffFiniteRankBundleCore IB n X)) :=
  ContMDiffPicardGroup.pow_mkOfTensorIsoUnit_eq_one_iff _ m

/-- **Tensor-order divisibility.** The order of `[L_χ]` in `ContMDiffPicardGroup IB n X` divides the
order of the character `χ`. -/
theorem orderOf_characterPicardHom_dvd (χ : G →* 𝕜ˣ) :
    orderOf (hp.characterPicardHom IB n χ) ∣ orderOf χ :=
  orderOf_map_dvd (hp.characterPicardHom IB n) χ

/-- The order of `[L_χ]` in `ContMDiffPicardGroup IB n X` divides `Nat.card G`. -/
theorem orderOf_characterPicardHom_dvd_natCard (χ : G →* 𝕜ˣ) :
    orderOf (hp.characterPicardHom IB n χ) ∣ Nat.card G :=
  orderOf_dvd_of_pow_eq_one <| by rw [← map_pow, pow_natCard_eq_one, map_one]

/-- If `characterPicardHom IB n` is injective, `[L_χ]` has the exact order of `χ` in
`ContMDiffPicardGroup IB n X`. -/
theorem orderOf_characterPicardHom_eq_of_injective
    (hinj : Function.Injective (hp.characterPicardHom IB n)) (χ : G →* 𝕜ˣ) :
    orderOf (hp.characterPicardHom IB n χ) = orderOf χ :=
  orderOf_injective (hp.characterPicardHom IB n) hinj χ

end General

/-! ### Triviality and exact order via equivariant functions upstairs -/

section Complete

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM] {HM : Type*} [TopologicalSpace HM]
  {I : ModelWithCorners 𝕜 EM HM}
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} {n : ℕ∞ω}
  {E X G : Type*} [TopologicalSpace E] [ChartedSpace HM E] [TopologicalSpace X]
  [ChartedSpace HB X] [Group G] [MulAction G E] {p : E → X} (hp : IsQuotientCoveringMap p G)

@[simp] theorem ofRankOne_characterContMDiffCore (χ : G →* 𝕜ˣ) :
    ContMDiffPicardGroup.ofRankOne (hp.characterContMDiffCore IB n χ)
      (hp.rank_characterContMDiffCore IB n χ) = hp.characterPicardHom IB n χ :=
  Units.ext <| by rw [ContMDiffPicardGroup.val_ofRankOne, val_characterPicardHom_apply]

/-- Over a complete scalar field, `[L_χ] = 1` in `ContMDiffPicardGroup IB n X` if and only if
`hp.characterCore χ` admits a global linear trivialization in its maximal `C^n` atlas. -/
theorem characterPicardHom_eq_one_iff_exists_trivialization_baseSet_eq_univ (χ : G →* 𝕜ˣ) :
    hp.characterPicardHom IB n χ = 1 ↔
      ∃ (e : Trivialization 𝕜 (π 𝕜 (hp.characterCore χ).Fiber)) (_ : e.IsLinear 𝕜),
        e.toOpenPartialHomeomorph ∈ (contMDiffFiberwiseLinear X 𝕜 IB n).maximalAtlas
          (TotalSpace 𝕜 (hp.characterCore χ).Fiber) ∧ e.baseSet = univ := by
  rw [hp.characterPicardHom_eq_one_iff_nonempty_iso,
    (hp.characterContMDiffCore IB n χ).nonempty_iso_tensorUnit_iff_exists_section_ne_zero
      (hp.rank_characterContMDiffCore IB n χ),
    toCore_characterContMDiffCore, hp.exists_section_ne_zero_characterFiniteRankCore_iff IB n χ,
    ContMDiffVectorBundle.exists_trivialization_baseSet_eq_univ_iff_exists_ne_zero
      (finrank_self 𝕜)]

variable (hpd : IsLocalDiffeomorph I IB n p)
include hpd

/-- If `p` is a `C^n` local diffeomorphism, `[L_χ] = 1` in `ContMDiffPicardGroup IB n X` if and
only if there is a nowhere-vanishing `C^n` function `f : E → 𝕜` with `f (g • y) = χ g * f y`. -/
theorem characterPicardHom_eq_one_iff (χ : G →* 𝕜ˣ) :
    hp.characterPicardHom IB n χ = 1 ↔
      ∃ f : E → 𝕜, ContMDiff I 𝓘(𝕜) n f ∧ (∀ y, f y ≠ 0) ∧
        ∀ (g : G) (y : E), f (g • y) = χ g * f y :=
  (hp.characterPicardHom_eq_one_iff_exists_trivialization_baseSet_eq_univ χ).trans
    (hp.exists_trivialization_baseSet_eq_univ_characterCore_iff hpd χ)

/-- If `p` is a `C^n` local diffeomorphism, `[L_χ] ^ m = 1` in `ContMDiffPicardGroup IB n X` if and
only if there is a nowhere-vanishing `C^n` function `f : E → 𝕜` with
`f (g • y) = (χ ^ m) g * f y`. -/
theorem characterPicardHom_pow_eq_one_iff (χ : G →* 𝕜ˣ) (m : ℕ) :
    hp.characterPicardHom IB n χ ^ m = 1 ↔
      ∃ f : E → 𝕜, ContMDiff I 𝓘(𝕜) n f ∧ (∀ y, f y ≠ 0) ∧
        ∀ (g : G) (y : E), f (g • y) = (χ ^ m) g * f y := by
  rw [← map_pow, hp.characterPicardHom_eq_one_iff hpd (χ ^ m)]

/-- If `p` is a `C^n` local diffeomorphism, `L_χ^{\otimes m} ≅ 𝟙_` in
`ContMDiffFiniteRankBundleCore IB n X` if and only if there is a nowhere-vanishing `C^n` function
`f : E → 𝕜` with `f (g • y) = (χ ^ m) g * f y`. -/
theorem nonempty_characterContMDiffCore_tensorPower_iso_unit_iff (χ : G →* 𝕜ˣ) (m : ℕ) :
    Nonempty ((hp.characterContMDiffCore IB n χ).tensorPower m ≅
        𝟙_ (ContMDiffFiniteRankBundleCore IB n X)) ↔
      ∃ f : E → 𝕜, ContMDiff I 𝓘(𝕜) n f ∧ (∀ y, f y ≠ 0) ∧
        ∀ (g : G) (y : E), f (g • y) = (χ ^ m) g * f y :=
  (hp.characterPicardHom_pow_eq_one_iff_nonempty_iso IB n χ m).symm.trans
    (hp.characterPicardHom_pow_eq_one_iff hpd χ m)

/-- Characterization of injectivity of `characterPicardHom IB n` via equivariant `C^n` functions on
the covering space `E`. -/
theorem characterPicardHom_injective_iff :
    Function.Injective (hp.characterPicardHom IB n) ↔
      ∀ χ : G →* 𝕜ˣ,
        (∃ f : E → 𝕜, ContMDiff I 𝓘(𝕜) n f ∧ (∀ y, f y ≠ 0) ∧
          ∀ (g : G) (y : E), f (g • y) = χ g * f y) → χ = 1 := by
  rw [injective_iff_map_eq_one]
  exact forall_congr' fun χ ↦ imp_congr_left (hp.characterPicardHom_eq_one_iff hpd χ)

/-- **Exact-order characterization in the `C^n` and holomorphic Picard group.** For any character
`χ : G →* 𝕜ˣ` (torsion or infinite-order), `[L_χ]` has the exact order of `χ` in
`ContMDiffPicardGroup IB n X` if and only if every `m : ℕ` admitting a nowhere-vanishing
`χ ^ m`-equivariant `C^n` function on `E` satisfies `χ ^ m = 1`. -/
theorem orderOf_characterPicardHom_eq_iff (χ : G →* 𝕜ˣ) :
    orderOf (hp.characterPicardHom IB n χ) = orderOf χ ↔
      ∀ m : ℕ,
        (∃ f : E → 𝕜, ContMDiff I 𝓘(𝕜) n f ∧ (∀ y, f y ≠ 0) ∧
          ∀ (g : G) (y : E), f (g • y) = (χ ^ m) g * f y) → χ ^ m = 1 := by
  rw [orderOf_eq_orderOf_iff]
  refine forall_congr' fun m ↦ ?_
  rw [← hp.characterPicardHom_pow_eq_one_iff hpd χ m]
  exact ⟨Iff.mp, fun h ↦ ⟨h, fun hm ↦ by rw [← map_pow, hm, map_one]⟩⟩

/-- **Exact-order characterization for torsion characters.** For a finite-order character
`χ : G →* 𝕜ˣ`, `[L_χ]` has exact order `orderOf χ` in `ContMDiffPicardGroup IB n X` if and only if
no positive `m < orderOf χ` admits a nowhere-vanishing `χ ^ m`-equivariant `C^n` function on `E`. -/
theorem orderOf_characterPicardHom_eq_iff_forall_lt (χ : G →* 𝕜ˣ) (hχ : IsOfFinOrder χ) :
    orderOf (hp.characterPicardHom IB n χ) = orderOf χ ↔
      ∀ m : ℕ, 0 < m → m < orderOf χ →
        ¬∃ f : E → 𝕜, ContMDiff I 𝓘(𝕜) n f ∧ (∀ y, f y ≠ 0) ∧
          ∀ (g : G) (y : E), f (g • y) = (χ ^ m) g * f y := by
  rw [orderOf_eq_iff (orderOf_pos_iff.mpr hχ)]
  have hpow : hp.characterPicardHom IB n χ ^ orderOf χ = 1 := by
    rw [← map_pow, pow_orderOf_eq_one, map_one]
  refine ⟨fun h m hm0 hmlt ↦ ?_, fun h ↦ ⟨hpow, fun m hmlt hm0 ↦ ?_⟩⟩
  · rw [← hp.characterPicardHom_pow_eq_one_iff hpd χ m]; exact h.2 m hmlt hm0
  · rw [ne_eq, hp.characterPicardHom_pow_eq_one_iff hpd χ m]; exact h m hm0 hmlt

end Complete

/-! ### Compact connected complex coverings -/

section ComplexCompact

variable {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℂ EM] {HM : Type*} [TopologicalSpace HM]
  {I : ModelWithCorners ℂ EM HM} [I.Boundaryless]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℂ EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners ℂ EB HB} {n : ℕ∞ω}
  {E X G : Type*} [TopologicalSpace E] [ChartedSpace HM E] [IsManifold I 1 E]
  [TopologicalSpace X] [ChartedSpace HB X]
  [Group G] [MulAction G E] {p : E → X} (hp : IsQuotientCoveringMap p G)

/-- On a compact connected complex manifold `E`, any character admitting a nowhere-vanishing
equivariant holomorphic function is trivial: by the maximum modulus principle the function is a
nonzero constant, forcing `χ g = 1`. -/
theorem eq_one_of_contMDiff_equivariant_ne_zero [CompactSpace E] [ConnectedSpace E]
    (hn : n ≠ 0) {χ : G →* ℂˣ} {f : E → ℂ} (hf : ContMDiff I 𝓘(ℂ) n f) (hf₀ : ∀ y, f y ≠ 0)
    (hfG : ∀ (g : G) (y : E), f (g • y) = χ g * f y) : χ = 1 := by
  let y₀ : E := Classical.arbitrary E
  ext g
  have hconst : f (g • y₀) = f y₀ :=
    (hf.mdifferentiable hn).apply_eq_of_compactSpace (g • y₀) y₀
  exact mul_right_cancel₀ (hf₀ y₀)
    (by rw [← hfG g y₀, MonoidHom.one_apply, Units.val_one, one_mul, hconst])

section WithMDifferentiable

variable (hpd : MDifferentiable I IB p) (hn : n ≠ 0)
include hpd hn

/-- **Injectivity of the character homomorphism on compact connected complex coverings.** When `p`
is differentiable, the covering manifold `E` is compact and connected, and `n ≠ 0` (in particular
`n = ∞`, the holomorphic Picard group), `(G →* ℂˣ) →* ContMDiffPicardGroup IB n X` is injective. -/
theorem characterPicardHom_injective [CompactSpace E] [ConnectedSpace E] :
    Function.Injective (hp.characterPicardHom IB n) :=
  (injective_iff_map_eq_one _).mpr fun χ hχ ↦
    (hp.exists_trivialization_baseSet_eq_univ_characterCore_iff_eq_one hpd hn χ).mp
      ((hp.characterPicardHom_eq_one_iff_exists_trivialization_baseSet_eq_univ χ).mp hχ)

/-- **Exact Picard order on compact connected complex coverings.** When `p` is differentiable, `E`
is compact and connected, and `n ≠ 0` (in particular `n = ∞`), `[L_χ]` has exact order `orderOf χ`
in `ContMDiffPicardGroup IB n X`. -/
theorem orderOf_characterPicardHom_eq [CompactSpace E] [ConnectedSpace E] (χ : G →* ℂˣ) :
    orderOf (hp.characterPicardHom IB n χ) = orderOf χ :=
  hp.orderOf_characterPicardHom_eq_of_injective IB n (hp.characterPicardHom_injective hpd hn) χ

/-- **Injectivity of the character homomorphism for finite coverings of compact bases.** If `p` is
differentiable, `X` is compact, `G` is finite, `E` is connected, and `n ≠ 0`, then
`hp.characterPicardHom IB n : (G →* ℂˣ) →* ContMDiffPicardGroup IB n X` is injective. -/
theorem characterPicardHom_injective_of_compactSpace_base [CompactSpace X] [ConnectedSpace E]
    [Finite G] : Function.Injective (hp.characterPicardHom IB n) :=
  have := hp.compactSpace
  hp.characterPicardHom_injective hpd hn

/-- **Exact Picard order for finite coverings of compact bases.** If `p` is differentiable, `X` is
compact, `G` is finite, `E` is connected, and `n ≠ 0`, then `[L_χ]` has exact order `orderOf χ` in
`ContMDiffPicardGroup IB n X`. -/
theorem orderOf_characterPicardHom_eq_of_compactSpace_base [CompactSpace X] [ConnectedSpace E]
    [Finite G] (χ : G →* ℂˣ) :
    orderOf (hp.characterPicardHom IB n χ) = orderOf χ :=
  have := hp.compactSpace
  hp.orderOf_characterPicardHom_eq hpd hn χ

end WithMDifferentiable

end ComplexCompact

end IsQuotientCoveringMap

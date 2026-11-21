/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Quotient.AssociatedBundle
public import TauCeti.Geometry.Manifold.VectorBundle.FiniteRank.Picard
public import TauCeti.GroupTheory.OrderOfElement.Basic
public import TauCeti.Topology.Covering.Quotient
public import Mathlib.GroupTheory.OrderOfElement

/-!
# The character homomorphism into the `C^n` and holomorphic Picard group

Let `p : E → X` be a quotient covering map for a group `G` (`IsQuotientCoveringMap p G`). For a
finite-rank representation `ρ : G →* ((Fin r → 𝕜) →L[𝕜] (Fin r → 𝕜))ˣ` of the deck group, the
point-indexed core `IsQuotientCoveringMap.associatedFiniteRankCore ρ` has locally constant
transitions, so for every model `IB` on `X` and every regularity `n` it defines an object
`IsQuotientCoveringMap.associatedContMDiffCore IB n ρ` of `ContMDiffFiniteRankBundleCore IB n X`.
For a character `χ : G →* 𝕜ˣ`, its rank-one specialization
`IsQuotientCoveringMap.characterContMDiffCore IB n χ` has total space `C^n`-diffeomorphic over `X`
to `(hp.characterCore χ).TotalSpace` via `IsQuotientCoveringMap.characterFiniteRankCoreDiffeomorph`
(defined in `TauCeti.Geometry.Manifold.Quotient.AssociatedBundle`).

In `ContMDiffFiniteRankBundleCore IB n X`, character line bundles satisfy canonical `C^n`
isomorphisms (using the categorical tensor power `TauCeti.tensorPow`):

* `L_1 ≅ 𝟙_` (`characterContMDiffCoreOneIso`),
* `L_χ ⊗ L_ψ ≅ L_{χ * ψ}` (`characterContMDiffCoreMulIso`),
* `L_χ^{\otimes m} ≅ L_{χ ^ m}` (`characterContMDiffCoreTensorPowerIso`),
* `L_χ^{\otimes \operatorname{orderOf} χ} ≅ 𝟙_` (`characterContMDiffCoreTensorPowerOrderOfIsoUnit`),
* `L_χ^{\otimes \operatorname{Nat.card} G} ≅ 𝟙_`
  (`characterContMDiffCoreTensorPowerNatCardIsoUnit`).

Consequently `χ ↦ [L_χ]` is a group homomorphism
`IsQuotientCoveringMap.characterPicardHom IB n : (G →* 𝕜ˣ) →* ContMDiffPicardGroup IB n X`, and
the order of `[L_χ]` in `ContMDiffPicardGroup IB n X` divides `orderOf χ` (and `Nat.card G`).

When `p` is a `C^n` local diffeomorphism (without assuming completeness of `𝕜`), global `C^n`
triviality of `L_χ` is decided by equivariant functions on `E`:

* `characterPicardHom_eq_one_iff`: `[L_χ] = 1` if and only if there is a nowhere-vanishing `C^n`
  function `f : E → 𝕜` with `f (g • y) = χ g * f y`.
* `orderOf_characterPicardHom_eq_iff`: for arbitrary `χ`, `orderOf [L_χ] = orderOf χ` if and only
  if every `m : ℕ` admitting a nowhere-vanishing `χ ^ m`-equivariant `C^n` function on `E`
  satisfies `χ ^ m = 1`.
* `orderOf_characterPicardHom_eq_iff_forall_lt`: for a finite-order character (`IsOfFinOrder χ`),
  `orderOf [L_χ] = orderOf χ` if and only if no `0 < m < orderOf χ` admits a nowhere-vanishing
  `χ ^ m`-equivariant `C^n` function on `E`.

Over `ℂ` at positive regularity `n ≠ 0` (in particular `n = ∞` or `n = ω`), if `p` is
differentiable and the total space `E` is a compact connected boundaryless complex manifold — for
instance whenever `X` is compact, `E` is connected, and `G` is finite — every holomorphic function
on `E` is constant, so no nontrivial character admits a globally trivial line bundle:

* `characterPicardHom_injective`: `(G →* ℂˣ) →* ContMDiffPicardGroup IB n X` is injective;
* `orderOf_characterPicardHom_eq`: the order of `[L_χ]` in the holomorphic Picard group equals
  `orderOf χ`;
* `exists_bundleDiffeomorph_characterCore_iff_eq`,
  `exists_trivialization_baseSet_eq_univ_tensorPow_characterFiniteRankCore_iff_orderOf_dvd`, and
  `isLeast_pos_trivialization_tensorPow_characterFiniteRankCore`: global-trivialization and
  bundle-equivalence criteria for character line bundles and their tensor powers.

## References

* Daniel Huybrechts, *Complex Geometry: An Introduction*, Springer, 2005, Section 2.2.
* Otto Forster, *Lectures on Riemann Surfaces*, Springer, 1981, §§4–5.
-/

public section

open Bundle CategoryTheory Filter Module MonoidalCategory Set Topology
open TauCeti (ContMDiffFiniteRankBundleCore ContMDiffPicardGroup FiniteRankBundleCore tensorPow)
open scoped Manifold ContDiff

namespace IsQuotientCoveringMap

section General

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*} [TopologicalSpace HB]
  (IB : ModelWithCorners 𝕜 EB HB) (n : ℕ∞ω)
  {E X G : Type*} [TopologicalSpace E] [TopologicalSpace X] [ChartedSpace HB X]
  [Group G] [MulAction G E] {p : E → X} (hp : IsQuotientCoveringMap p G)

/-- The `C^n` finite-rank core over `X` attached to a representation
`ρ : G →* ((Fin r → 𝕜) →L[𝕜] (Fin r → 𝕜))ˣ` of the deck group. -/
-- Exposed so `.toCore` and `.toCore.rank` reduce definitionally in dependent morphism and fibre
-- statements.
@[expose]
noncomputable def associatedContMDiffCore {r : ℕ}
    (ρ : G →* ((Fin r → 𝕜) →L[𝕜] (Fin r → 𝕜))ˣ) :
    ContMDiffFiniteRankBundleCore IB n X :=
  ⟨hp.associatedFiniteRankCore ρ, inferInstance⟩

@[simp] theorem toCore_associatedContMDiffCore {r : ℕ}
    (ρ : G →* ((Fin r → 𝕜) →L[𝕜] (Fin r → 𝕜))ˣ) :
    (hp.associatedContMDiffCore IB n ρ).toCore = hp.associatedFiniteRankCore ρ := (rfl)

@[simp] theorem associatedContMDiffCore_localTriv_baseSet {r : ℕ}
    (ρ : G →* ((Fin r → 𝕜) →L[𝕜] (Fin r → 𝕜))ˣ) (x : X) :
    ((hp.associatedContMDiffCore IB n ρ).toCore.core.localTriv x).baseSet =
      (hp.isLocalHomeomorph.localInverseAt (Function.surjInv hp.surjective x)).source := (rfl)

theorem rank_associatedContMDiffCore {r : ℕ}
    (ρ : G →* ((Fin r → 𝕜) →L[𝕜] (Fin r → 𝕜))ˣ) :
    (hp.associatedContMDiffCore IB n ρ).toCore.rank = r :=
  hp.rank_associatedFiniteRankCore ρ

/-- The `C^n` line-bundle core over `X` attached to a character `χ : G →* 𝕜ˣ` of the deck group. -/
-- Exposed so `.toCore` and `.toCore.rank` reduce definitionally in dependent morphism and fibre
-- statements.
@[expose]
noncomputable def characterContMDiffCore (χ : G →* 𝕜ˣ) :
    ContMDiffFiniteRankBundleCore IB n X :=
  hp.associatedContMDiffCore IB n
    ((Units.map (algebraMap 𝕜 ((Fin 1 → 𝕜) →L[𝕜] (Fin 1 → 𝕜))).toMonoidHom).comp χ)

/-- The `C^n` core of a character is the `C^n` associated core for scalar multiplication on
`Fin 1 → 𝕜`. -/
theorem characterContMDiffCore_def (χ : G →* 𝕜ˣ) :
    hp.characterContMDiffCore IB n χ =
      hp.associatedContMDiffCore IB n
        ((Units.map (algebraMap 𝕜 ((Fin 1 → 𝕜) →L[𝕜] (Fin 1 → 𝕜))).toMonoidHom).comp χ) :=
  (rfl)

@[simp] theorem toCore_characterContMDiffCore (χ : G →* 𝕜ˣ) :
    (hp.characterContMDiffCore IB n χ).toCore = hp.characterFiniteRankCore χ := (rfl)

@[simp] theorem characterContMDiffCore_localTriv_baseSet (χ : G →* 𝕜ˣ) (x : X) :
    ((hp.characterContMDiffCore IB n χ).toCore.core.localTriv x).baseSet =
      (hp.isLocalHomeomorph.localInverseAt (Function.surjInv hp.surjective x)).source := (rfl)

theorem rank_characterContMDiffCore (χ : G →* 𝕜ˣ) :
    (hp.characterContMDiffCore IB n χ).toCore.rank = 1 :=
  hp.rank_characterFiniteRankCore χ

/-- Equality of characters induces a canonical `C^n` isomorphism of their cores. -/
noncomputable def characterContMDiffCoreCongr {χ ψ : G →* 𝕜ˣ} (h : χ = ψ) :
    hp.characterContMDiffCore IB n χ ≅ hp.characterContMDiffCore IB n ψ :=
  eqToIso (congrArg (hp.characterContMDiffCore IB n) h)

theorem characterContMDiffCoreCongr_def {χ ψ : G →* 𝕜ˣ} (h : χ = ψ) :
    hp.characterContMDiffCoreCongr IB n h =
      eqToIso (congrArg (hp.characterContMDiffCore IB n) h) := (rfl)

@[simp] theorem characterContMDiffCoreCongr_refl (χ : G →* 𝕜ˣ) :
    hp.characterContMDiffCoreCongr IB n (rfl : χ = χ) = Iso.refl _ := (rfl)

/-- The `C^n` core of the trivial character is canonically isomorphic in
`ContMDiffFiniteRankBundleCore IB n X` to the monoidal unit. -/
noncomputable def characterContMDiffCoreOneIso :
    hp.characterContMDiffCore IB n (1 : G →* 𝕜ˣ) ≅ 𝟙_ (ContMDiffFiniteRankBundleCore IB n X) :=
  ContMDiffFiniteRankBundleCore.isoTrivialOfCoordChangeEqId
    (hp.characterContMDiffCore IB n 1)
    (ContinuousLinearEquiv.refl 𝕜 (Fin 1 → 𝕜))
    fun i j x _ _ ↦ by
      rw [toCore_characterContMDiffCore, characterFiniteRankCore_coordChange,
        MonoidHom.one_apply, Units.val_one, one_smul]

@[simp] theorem characterContMDiffCoreOneIso_hom_toHom :
    (hp.characterContMDiffCoreOneIso IB n).hom.toHom =
      hp.characterFiniteRankCoreOneIso.hom :=
  (ContMDiffFiniteRankBundleCore.isoTrivialOfCoordChangeEqId_hom_toHom _ _ _).trans <|
    FiniteRankBundleCore.hom_ext fun x ↦
      (FiniteRankBundleCore.fiberMap_isoTrivialOfCoordChangeEqId_hom _ _ _ x).trans
        (hp.fiberMap_characterFiniteRankCoreOneIso_hom x).symm

@[simp] theorem characterContMDiffCoreOneIso_inv_toHom :
    (hp.characterContMDiffCoreOneIso IB n).inv.toHom =
      hp.characterFiniteRankCoreOneIso.inv :=
  (ContMDiffFiniteRankBundleCore.isoTrivialOfCoordChangeEqId_inv_toHom _ _ _).trans <|
    FiniteRankBundleCore.hom_ext fun x ↦
      (FiniteRankBundleCore.fiberMap_isoTrivialOfCoordChangeEqId_inv _ _ _ x).trans
        (hp.fiberMap_characterFiniteRankCoreOneIso_inv x).symm

/-- **Tensor multiplicativity of `C^n` and holomorphic character line bundles.** For characters
`χ, ψ : G →* 𝕜ˣ` of the deck group, `L_χ ⊗ L_ψ ≅ L_{χ * ψ}` in
`ContMDiffFiniteRankBundleCore IB n X`. -/
noncomputable def characterContMDiffCoreMulIso (χ ψ : G →* 𝕜ˣ) :
    hp.characterContMDiffCore IB n χ ⊗ hp.characterContMDiffCore IB n ψ ≅
      hp.characterContMDiffCore IB n (χ * ψ) :=
  ContMDiffFiniteRankBundleCore.constIso
    (fun _ ↦ by simp)
    (hp.characterMulFiberEquiv χ ψ)
    fun i j x _ _ ↦ hp.characterFiniteRankCore_mul_intertwine χ ψ i j x

@[simp] theorem characterContMDiffCoreMulIso_hom_toHom (χ ψ : G →* 𝕜ˣ) :
    (hp.characterContMDiffCoreMulIso IB n χ ψ).hom.toHom =
      (hp.characterFiniteRankCoreMulIso χ ψ).hom :=
  (ContMDiffFiniteRankBundleCore.constIso_hom_toHom _ _ _).trans <|
    FiniteRankBundleCore.hom_ext fun x ↦
      (FiniteRankBundleCore.fiberMap_constIso_hom _ _ _ x).trans
        (hp.fiberMap_characterFiniteRankCoreMulIso_hom χ ψ x).symm

@[simp] theorem characterContMDiffCoreMulIso_inv_toHom (χ ψ : G →* 𝕜ˣ) :
    (hp.characterContMDiffCoreMulIso IB n χ ψ).inv.toHom =
      (hp.characterFiniteRankCoreMulIso χ ψ).inv :=
  (ContMDiffFiniteRankBundleCore.constIso_inv_toHom _ _ _).trans <|
    FiniteRankBundleCore.hom_ext fun x ↦
      (FiniteRankBundleCore.fiberMap_constIso_inv _ _ _ x).trans
        (hp.fiberMap_characterFiniteRankCoreMulIso_inv χ ψ x).symm

/-- **Tensor powers of a `C^n` character line bundle.** For every `m : ℕ`, the `m`-th tensor power
of `hp.characterContMDiffCore IB n χ` is canonically isomorphic to
`hp.characterContMDiffCore IB n (χ ^ m)`. -/
noncomputable def characterContMDiffCoreTensorPowerIso (χ : G →* 𝕜ˣ) :
    ∀ m : ℕ, tensorPow (hp.characterContMDiffCore IB n χ) m ≅
      hp.characterContMDiffCore IB n (χ ^ m)
  | 0 => (hp.characterContMDiffCoreOneIso IB n).symm ≪≫
      hp.characterContMDiffCoreCongr IB n (pow_zero χ).symm
  | m + 1 => (Iso.refl (hp.characterContMDiffCore IB n χ) ⊗ᵢ
        characterContMDiffCoreTensorPowerIso χ m) ≪≫
      hp.characterContMDiffCoreMulIso IB n χ (χ ^ m) ≪≫
      hp.characterContMDiffCoreCongr IB n (pow_succ' χ m).symm

@[simp] theorem characterContMDiffCoreTensorPowerIso_zero (χ : G →* 𝕜ˣ) :
    hp.characterContMDiffCoreTensorPowerIso IB n χ 0 =
      (hp.characterContMDiffCoreOneIso IB n).symm ≪≫
        hp.characterContMDiffCoreCongr IB n (pow_zero χ).symm := (rfl)

theorem characterContMDiffCoreTensorPowerIso_succ (χ : G →* 𝕜ˣ) (m : ℕ) :
    hp.characterContMDiffCoreTensorPowerIso IB n χ (m + 1) =
      (Iso.refl (hp.characterContMDiffCore IB n χ) ⊗ᵢ
        hp.characterContMDiffCoreTensorPowerIso IB n χ m) ≪≫
        hp.characterContMDiffCoreMulIso IB n χ (χ ^ m) ≪≫
        hp.characterContMDiffCoreCongr IB n (pow_succ' χ m).symm := (rfl)

/-- For every character `χ : G →* 𝕜ˣ`, the `orderOf χ`-th tensor power of `L_χ` is canonically
isomorphic in `ContMDiffFiniteRankBundleCore IB n X` to the trivial line bundle `𝟙_`. -/
noncomputable def characterContMDiffCoreTensorPowerOrderOfIsoUnit (χ : G →* 𝕜ˣ) :
    tensorPow (hp.characterContMDiffCore IB n χ) (orderOf χ) ≅
      𝟙_ (ContMDiffFiniteRankBundleCore IB n X) :=
  hp.characterContMDiffCoreTensorPowerIso IB n χ (orderOf χ) ≪≫
    hp.characterContMDiffCoreCongr IB n (pow_orderOf_eq_one χ) ≪≫
    hp.characterContMDiffCoreOneIso IB n

theorem characterContMDiffCoreTensorPowerOrderOfIsoUnit_def (χ : G →* 𝕜ˣ) :
    hp.characterContMDiffCoreTensorPowerOrderOfIsoUnit IB n χ =
      hp.characterContMDiffCoreTensorPowerIso IB n χ (orderOf χ) ≪≫
        hp.characterContMDiffCoreCongr IB n (pow_orderOf_eq_one χ) ≪≫
        hp.characterContMDiffCoreOneIso IB n := (rfl)

/-- The `Nat.card G`-th tensor power of `L_χ` is canonically isomorphic in
`ContMDiffFiniteRankBundleCore IB n X` to the trivial line bundle `𝟙_`. -/
noncomputable def characterContMDiffCoreTensorPowerNatCardIsoUnit (χ : G →* 𝕜ˣ) :
    tensorPow (hp.characterContMDiffCore IB n χ) (Nat.card G) ≅
      𝟙_ (ContMDiffFiniteRankBundleCore IB n X) :=
  hp.characterContMDiffCoreTensorPowerIso IB n χ (Nat.card G) ≪≫
    hp.characterContMDiffCoreCongr IB n χ.pow_natCard_eq_one ≪≫
    hp.characterContMDiffCoreOneIso IB n

theorem characterContMDiffCoreTensorPowerNatCardIsoUnit_def (χ : G →* 𝕜ˣ) :
    hp.characterContMDiffCoreTensorPowerNatCardIsoUnit IB n χ =
      hp.characterContMDiffCoreTensorPowerIso IB n χ (Nat.card G) ≪≫
        hp.characterContMDiffCoreCongr IB n χ.pow_natCard_eq_one ≪≫
        hp.characterContMDiffCoreOneIso IB n := (rfl)

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

/-- The character class `[L_χ]` is trivial in `ContMDiffPicardGroup IB n X` if and only if
`hp.characterContMDiffCore IB n χ` is isomorphic to `𝟙_` in
`ContMDiffFiniteRankBundleCore IB n X`. -/
theorem characterPicardHom_eq_one_iff_nonempty_iso (χ : G →* 𝕜ˣ) :
    hp.characterPicardHom IB n χ = 1 ↔
      Nonempty (hp.characterContMDiffCore IB n χ ≅ 𝟙_ (ContMDiffFiniteRankBundleCore IB n X)) :=
  ContMDiffPicardGroup.mkOfTensorIsoUnit_eq_one_iff _

/-- The `m`-th power `[L_χ] ^ m` is trivial in `ContMDiffPicardGroup IB n X` if and only if the
`m`-th tensor power `tensorPow (hp.characterContMDiffCore IB n χ) m` is isomorphic to `𝟙_` in
`ContMDiffFiniteRankBundleCore IB n X`. -/
theorem characterPicardHom_pow_eq_one_iff_nonempty_iso (χ : G →* 𝕜ˣ) (m : ℕ) :
    hp.characterPicardHom IB n χ ^ m = 1 ↔
      Nonempty (tensorPow (hp.characterContMDiffCore IB n χ) m ≅
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
  orderOf_dvd_of_pow_eq_one <| by rw [← map_pow, MonoidHom.pow_natCard_eq_one, map_one]

/-- If `characterPicardHom IB n` is injective, `[L_χ]` has the exact order of `χ` in
`ContMDiffPicardGroup IB n X`. -/
theorem orderOf_characterPicardHom_eq_of_injective
    (hinj : Function.Injective (hp.characterPicardHom IB n)) (χ : G →* 𝕜ˣ) :
    orderOf (hp.characterPicardHom IB n χ) = orderOf χ :=
  orderOf_injective (hp.characterPicardHom IB n) hinj χ

end General

/-! ### Triviality and exact order via equivariant functions upstairs -/

section Equivariant

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM] {HM : Type*} [TopologicalSpace HM]
  {I : ModelWithCorners 𝕜 EM HM}
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} {n : ℕ∞ω}
  {E X G : Type*} [TopologicalSpace E] [ChartedSpace HM E] [TopologicalSpace X]
  [ChartedSpace HB X] [Group G] [MulAction G E] {p : E → X} (hp : IsQuotientCoveringMap p G)
  (hpd : IsLocalDiffeomorph I IB n p)
include hpd

/-- If `p` is a `C^n` local diffeomorphism, `[L_χ] = 1` in `ContMDiffPicardGroup IB n X` if and
only if there is a nowhere-vanishing `C^n` function `f : E → 𝕜` with `f (g • y) = χ g * f y`. -/
theorem characterPicardHom_eq_one_iff (χ : G →* 𝕜ˣ) :
    hp.characterPicardHom IB n χ = 1 ↔
      ∃ f : E → 𝕜, ContMDiff I 𝓘(𝕜) n f ∧ (∀ y, f y ≠ 0) ∧
        ∀ (g : G) (y : E), f (g • y) = χ g * f y := by
  rw [hp.characterPicardHom_eq_one_iff_nonempty_iso,
    (hp.characterContMDiffCore IB n χ).nonempty_iso_tensorUnit_iff_exists_section_ne_zero
      (hp.rank_characterContMDiffCore IB n χ),
    toCore_characterContMDiffCore, hp.exists_section_ne_zero_characterFiniteRankCore_iff IB n χ,
    characterCore_def]
  set ρ := (Units.map (algebraMap 𝕜 (𝕜 →L[𝕜] 𝕜)).toMonoidHom).comp χ
  constructor
  · rintro ⟨σ, hσ, hσ₀⟩
    refine ⟨hp.associatedSectionEquiv ρ σ,
      (hp.contMDiff_section_associatedCore_iff ρ hpd le_rfl).1 hσ, fun y ↦ ?_, fun g y ↦ ?_⟩
    · rw [Ne, associatedSectionEquiv_apply_eq_zero_iff]
      exact hσ₀ _
    · simpa [ρ, ContinuousLinearMap.algebraMap_apply, smul_eq_mul] using
        (hp.associatedSectionEquiv ρ σ).property g y
  · rintro ⟨f, hf, hf₀, hfG⟩
    have hfG' : ∀ (g : G) (y : E), f (g • y) = (ρ g : 𝕜 →L[𝕜] 𝕜) (f y) := fun g y ↦ by
      simpa [ρ, ContinuousLinearMap.algebraMap_apply, smul_eq_mul] using hfG g y
    set σ := (hp.associatedSectionEquiv ρ).symm ⟨f, hfG'⟩
    have hσ : (hp.associatedSectionEquiv ρ σ : E → 𝕜) = f := by
      simp only [σ, Equiv.apply_symm_apply]
    refine ⟨σ, (hp.contMDiff_section_associatedCore_iff ρ hpd le_rfl).2 (hσ ▸ hf), fun x ↦ ?_⟩
    obtain ⟨y, rfl⟩ := hp.surjective x
    rw [Ne, ← associatedSectionEquiv_apply_eq_zero_iff, hσ]
    exact hf₀ y

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
    Nonempty (tensorPow (hp.characterContMDiffCore IB n χ) m ≅
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

end Equivariant

/-! ### Global trivialization characterization over a complete scalar field -/

section Complete

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} {n : ℕ∞ω}
  {E X G : Type*} [TopologicalSpace E] [TopologicalSpace X] [ChartedSpace HB X]
  [Group G] [MulAction G E] {p : E → X} (hp : IsQuotientCoveringMap p G)

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

/-- The `m`-th tensor power `tensorPow (hp.characterFiniteRankCore χ) m` admits a global compatible
`C^n` trivialization if and only if `hp.characterCore (χ ^ m)` does. -/
theorem exists_trivialization_baseSet_eq_univ_tensorPow_characterFiniteRankCore_iff
    (χ : G →* 𝕜ˣ) (m : ℕ) :
    (∃ (e : Trivialization (Fin (tensorPow (hp.characterFiniteRankCore χ) m).rank → 𝕜)
        (π _ (tensorPow (hp.characterFiniteRankCore χ) m).core.Fiber)) (_ : e.IsLinear 𝕜),
        e.toOpenPartialHomeomorph ∈
          (contMDiffFiberwiseLinear X (Fin (tensorPow (hp.characterFiniteRankCore χ) m).rank → 𝕜)
            IB n).maximalAtlas
            (TotalSpace _ (tensorPow (hp.characterFiniteRankCore χ) m).core.Fiber) ∧
          e.baseSet = univ) ↔
      ∃ (e : Trivialization 𝕜 (π 𝕜 (hp.characterCore (χ ^ m)).Fiber)) (_ : e.IsLinear 𝕜),
        e.toOpenPartialHomeomorph ∈
          (contMDiffFiberwiseLinear X 𝕜 IB n).maximalAtlas
            (TotalSpace 𝕜 (hp.characterCore (χ ^ m)).Fiber) ∧
          e.baseSet = univ := by
  have h1 : (tensorPow (hp.characterContMDiffCore IB n χ) m).toCore =
      tensorPow (hp.characterFiniteRankCore χ) m :=
    ContMDiffFiniteRankBundleCore.toCore_tensorPow _ m
  have hleft := ContMDiffPicardGroup.ofRankOne_eq_one_iff_exists_trivialization_baseSet_eq_univ
    (tensorPow (hp.characterContMDiffCore IB n χ) m) (by simp)
  rw [ContMDiffPicardGroup.ofRankOne_tensorPow _ (hp.rank_characterContMDiffCore IB n χ),
    hp.ofRankOne_characterContMDiffCore, ← map_pow,
    hp.characterPicardHom_eq_one_iff_exists_trivialization_baseSet_eq_univ] at hleft
  exact h1 ▸ hleft.symm

/-- Whenever `orderOf χ ∣ m`, the `m`-th tensor power `tensorPow (hp.characterFiniteRankCore χ) m`
admits a global compatible `C^n` trivialization over `X`. -/
theorem exists_trivialization_baseSet_eq_univ_tensorPow_characterFiniteRankCore_of_orderOf_dvd
    {χ : G →* 𝕜ˣ} {m : ℕ} (hdvd : orderOf χ ∣ m) :
    ∃ (e : Trivialization (Fin (tensorPow (hp.characterFiniteRankCore χ) m).rank → 𝕜)
      (π _ (tensorPow (hp.characterFiniteRankCore χ) m).core.Fiber)) (_ : e.IsLinear 𝕜),
      e.toOpenPartialHomeomorph ∈
        (contMDiffFiberwiseLinear X (Fin (tensorPow (hp.characterFiniteRankCore χ) m).rank → 𝕜)
          IB n).maximalAtlas
          (TotalSpace _ (tensorPow (hp.characterFiniteRankCore χ) m).core.Fiber) ∧
        e.baseSet = univ := by
  rw [hp.exists_trivialization_baseSet_eq_univ_tensorPow_characterFiniteRankCore_iff,
    orderOf_dvd_iff_pow_eq_one.1 hdvd]
  exact hp.exists_trivialization_baseSet_eq_univ_characterCore_one

/-- For every character `χ`, the `orderOf χ`-th tensor power
`tensorPow (hp.characterFiniteRankCore χ) (orderOf χ)` admits a global compatible `C^n`
trivialization. -/
theorem exists_trivialization_baseSet_eq_univ_tensorPow_characterFiniteRankCore_orderOf
    (χ : G →* 𝕜ˣ) :
    ∃ (e : Trivialization (Fin (tensorPow (hp.characterFiniteRankCore χ) (orderOf χ)).rank → 𝕜)
      (π _ (tensorPow (hp.characterFiniteRankCore χ) (orderOf χ)).core.Fiber)) (_ : e.IsLinear 𝕜),
      e.toOpenPartialHomeomorph ∈
        (contMDiffFiberwiseLinear X
          (Fin (tensorPow (hp.characterFiniteRankCore χ) (orderOf χ)).rank → 𝕜)
          IB n).maximalAtlas
          (TotalSpace _ (tensorPow (hp.characterFiniteRankCore χ) (orderOf χ)).core.Fiber) ∧
        e.baseSet = univ :=
  hp.exists_trivialization_baseSet_eq_univ_tensorPow_characterFiniteRankCore_of_orderOf_dvd dvd_rfl

/-- For every character `χ : G →* 𝕜ˣ`, the `Nat.card G`-th tensor power
`tensorPow (hp.characterFiniteRankCore χ) (Nat.card G)` admits a global compatible `C^n`
trivialization; for a finite deck group `G` of order `N = Nat.card G`, every character line bundle
has `N`-torsion tensor power. -/
theorem exists_trivialization_baseSet_eq_univ_tensorPow_characterFiniteRankCore_natCard
    (χ : G →* 𝕜ˣ) :
    ∃ (e : Trivialization (Fin (tensorPow (hp.characterFiniteRankCore χ) (Nat.card G)).rank → 𝕜)
      (π _ (tensorPow (hp.characterFiniteRankCore χ) (Nat.card G)).core.Fiber)) (_ : e.IsLinear 𝕜),
      e.toOpenPartialHomeomorph ∈
        (contMDiffFiberwiseLinear X
          (Fin (tensorPow (hp.characterFiniteRankCore χ) (Nat.card G)).rank → 𝕜)
          IB n).maximalAtlas
          (TotalSpace _ (tensorPow (hp.characterFiniteRankCore χ) (Nat.card G)).core.Fiber) ∧
        e.baseSet = univ := by
  refine hp.exists_trivialization_baseSet_eq_univ_tensorPow_characterFiniteRankCore_of_orderOf_dvd
    (orderOf_dvd_iff_pow_eq_one.2 ?_)
  ext g
  simp [← map_pow, pow_card_eq_one']

/-- When `hp.characterPicardHom IB n` is injective, two character line bundles
`hp.characterCore χ₁` and `hp.characterCore χ₂` are `C^n` bundle-equivalent if and only if
`χ₁ = χ₂`. -/
theorem exists_bundleDiffeomorph_characterCore_iff_eq_of_injective
    (hinj : Function.Injective (hp.characterPicardHom IB n)) (χ₁ χ₂ : G →* 𝕜ˣ) :
    (∃ e : ∀ x, (hp.characterCore χ₁).Fiber x ≃L[𝕜] (hp.characterCore χ₂).Fiber x,
        ContMDiff (IB.prod 𝓘(𝕜)) (IB.prod 𝓘(𝕜)) n
          (fun p : (hp.characterCore χ₁).TotalSpace ↦ TotalSpace.mk' 𝕜 p.proj (e p.proj p.snd))) ↔
      χ₁ = χ₂ := by
  refine ⟨fun h ↦ inv_mul_eq_one.1 <| hinj ?_, ?_⟩
  · rw [map_one, hp.characterPicardHom_eq_one_iff_exists_trivialization_baseSet_eq_univ]
    exact (hp.exists_bundleDiffeomorph_characterCore_iff_exists_trivialization χ₁ χ₂).1 h
  · rintro rfl
    exact ⟨fun x ↦ ContinuousLinearEquiv.refl 𝕜 ((hp.characterCore χ₁).Fiber x), contMDiff_id⟩

/-- When `hp.characterPicardHom IB n` is injective, the `m`-th tensor power
`tensorPow (hp.characterFiniteRankCore χ) m` is globally `C^n`-trivial if and only if
`orderOf χ ∣ m`. -/
theorem exists_trivialization_tensorPow_characterFiniteRankCore_iff_orderOf_dvd_of_injective
    (hinj : Function.Injective (hp.characterPicardHom IB n)) (χ : G →* 𝕜ˣ) (m : ℕ) :
    (∃ (e : Trivialization (Fin (tensorPow (hp.characterFiniteRankCore χ) m).rank → 𝕜)
        (π _ (tensorPow (hp.characterFiniteRankCore χ) m).core.Fiber)) (_ : e.IsLinear 𝕜),
        e.toOpenPartialHomeomorph ∈
          (contMDiffFiberwiseLinear X (Fin (tensorPow (hp.characterFiniteRankCore χ) m).rank → 𝕜)
            IB n).maximalAtlas
            (TotalSpace _ (tensorPow (hp.characterFiniteRankCore χ) m).core.Fiber) ∧
          e.baseSet = univ) ↔
      orderOf χ ∣ m := by
  refine ⟨fun h ↦ orderOf_dvd_iff_pow_eq_one.2 <| hinj ?_,
    hp.exists_trivialization_baseSet_eq_univ_tensorPow_characterFiniteRankCore_of_orderOf_dvd⟩
  rw [map_one, hp.characterPicardHom_eq_one_iff_exists_trivialization_baseSet_eq_univ]
  exact (hp.exists_trivialization_baseSet_eq_univ_tensorPow_characterFiniteRankCore_iff χ m).1 h

/-- When `hp.characterPicardHom IB n` is injective, the least positive exponent `m` for which
`tensorPow (hp.characterFiniteRankCore χ) m` is globally `C^n`-trivial is `orderOf χ` whenever `χ`
has finite order. -/
theorem isLeast_pos_trivialization_tensorPow_characterFiniteRankCore_of_injective
    (hinj : Function.Injective (hp.characterPicardHom IB n))
    {χ : G →* 𝕜ˣ} (hχ : IsOfFinOrder χ) :
    IsLeast {m : ℕ | 0 < m ∧
      ∃ (e : Trivialization (Fin (tensorPow (hp.characterFiniteRankCore χ) m).rank → 𝕜)
        (π _ (tensorPow (hp.characterFiniteRankCore χ) m).core.Fiber)) (_ : e.IsLinear 𝕜),
        e.toOpenPartialHomeomorph ∈
          (contMDiffFiberwiseLinear X (Fin (tensorPow (hp.characterFiniteRankCore χ) m).rank → 𝕜)
            IB n).maximalAtlas
            (TotalSpace _ (tensorPow (hp.characterFiniteRankCore χ) m).core.Fiber) ∧
          e.baseSet = univ} (orderOf χ) :=
  ⟨⟨hχ.orderOf_pos,
    hp.exists_trivialization_baseSet_eq_univ_tensorPow_characterFiniteRankCore_orderOf χ⟩,
    fun _ hm ↦ Nat.le_of_dvd hm.1 <|
      (hp.exists_trivialization_tensorPow_characterFiniteRankCore_iff_orderOf_dvd_of_injective
        hinj χ _).1 hm.2⟩

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
  (hpd : MDifferentiable I IB p) (hn : n ≠ 0)
include hpd hn

/-- **Injectivity of the character homomorphism on compact connected complex coverings.** When `E`
is a compact connected boundaryless complex manifold (`[I.Boundaryless] [IsManifold I 1 E]`), `p`
is differentiable, and `n ≠ 0` (in particular `n = ∞`, the holomorphic Picard group),
`(G →* ℂˣ) →* ContMDiffPicardGroup IB n X` is injective. -/
theorem characterPicardHom_injective [CompactSpace E] [ConnectedSpace E] :
    Function.Injective (hp.characterPicardHom IB n) :=
  (injective_iff_map_eq_one _).mpr fun χ hχ ↦
    (hp.exists_trivialization_baseSet_eq_univ_characterCore_iff_eq_one hpd hn χ).mp
      ((hp.characterPicardHom_eq_one_iff_exists_trivialization_baseSet_eq_univ χ).mp hχ)

/-- **Exact Picard order on compact connected complex coverings.** When `E` is a compact connected
boundaryless complex manifold (`[I.Boundaryless] [IsManifold I 1 E]`), `p` is differentiable, and
`n ≠ 0` (in particular `n = ∞`), `[L_χ]` has exact order `orderOf χ` in
`ContMDiffPicardGroup IB n X`. -/
theorem orderOf_characterPicardHom_eq [CompactSpace E] [ConnectedSpace E] (χ : G →* ℂˣ) :
    orderOf (hp.characterPicardHom IB n χ) = orderOf χ :=
  hp.orderOf_characterPicardHom_eq_of_injective IB n (hp.characterPicardHom_injective hpd hn) χ

/-- **Injectivity of the character homomorphism for finite coverings of compact bases.** If `E` is
a connected boundaryless complex manifold (`[I.Boundaryless] [IsManifold I 1 E]`), `p` is
differentiable, `X` is compact, `G` is finite, and `n ≠ 0`, then
`hp.characterPicardHom IB n : (G →* ℂˣ) →* ContMDiffPicardGroup IB n X` is injective. -/
theorem characterPicardHom_injective_of_compactSpace_base [CompactSpace X] [ConnectedSpace E]
    [Finite G] : Function.Injective (hp.characterPicardHom IB n) :=
  have := hp.compactSpace
  hp.characterPicardHom_injective hpd hn

/-- **Exact Picard order for finite coverings of compact bases.** If `E` is a connected boundaryless
complex manifold (`[I.Boundaryless] [IsManifold I 1 E]`), `p` is differentiable, `X` is compact,
`G` is finite, and `n ≠ 0`, then `[L_χ]` has exact order `orderOf χ` in
`ContMDiffPicardGroup IB n X`. -/
theorem orderOf_characterPicardHom_eq_of_compactSpace_base [CompactSpace X] [ConnectedSpace E]
    [Finite G] (χ : G →* ℂˣ) :
    orderOf (hp.characterPicardHom IB n χ) = orderOf χ :=
  have := hp.compactSpace
  hp.orderOf_characterPicardHom_eq hpd hn χ

/-- When `E` is a compact connected complex manifold and `p : E → X` is differentiable (`n ≠ 0`),
two character line bundles `hp.characterCore χ₁` and `hp.characterCore χ₂` are `C^n`
bundle-equivalent (in particular holomorphically isomorphic at `n = ∞`) if and only if
`χ₁ = χ₂`. -/
theorem exists_bundleDiffeomorph_characterCore_iff_eq [CompactSpace E] [ConnectedSpace E]
    (χ₁ χ₂ : G →* ℂˣ) :
    (∃ e : ∀ x, (hp.characterCore χ₁).Fiber x ≃L[ℂ] (hp.characterCore χ₂).Fiber x,
        ContMDiff (IB.prod 𝓘(ℂ)) (IB.prod 𝓘(ℂ)) n
          (fun p : (hp.characterCore χ₁).TotalSpace ↦ TotalSpace.mk' ℂ p.proj (e p.proj p.snd))) ↔
      χ₁ = χ₂ :=
  hp.exists_bundleDiffeomorph_characterCore_iff_eq_of_injective
    (hp.characterPicardHom_injective hpd hn) χ₁ χ₂

/-- When `E` is a compact connected complex manifold and `p : E → X` is differentiable (`n ≠ 0`),
the `m`-th tensor power `tensorPow (hp.characterFiniteRankCore χ) m` admits a global compatible
`C^n` trivialization if and only if `orderOf χ ∣ m`. -/
theorem exists_trivialization_baseSet_eq_univ_tensorPow_characterFiniteRankCore_iff_orderOf_dvd
    [CompactSpace E] [ConnectedSpace E] (χ : G →* ℂˣ) (m : ℕ) :
    (∃ (e : Trivialization (Fin (tensorPow (hp.characterFiniteRankCore χ) m).rank → ℂ)
        (π _ (tensorPow (hp.characterFiniteRankCore χ) m).core.Fiber)) (_ : e.IsLinear ℂ),
        e.toOpenPartialHomeomorph ∈
          (contMDiffFiberwiseLinear X (Fin (tensorPow (hp.characterFiniteRankCore χ) m).rank → ℂ)
            IB n).maximalAtlas
            (TotalSpace _ (tensorPow (hp.characterFiniteRankCore χ) m).core.Fiber) ∧
          e.baseSet = univ) ↔
      orderOf χ ∣ m :=
  hp.exists_trivialization_tensorPow_characterFiniteRankCore_iff_orderOf_dvd_of_injective
    (hp.characterPicardHom_injective hpd hn) χ m

/-- When `E` is a compact connected complex manifold, `p : E → X` is differentiable (`n ≠ 0`), and
`χ : G →* ℂˣ` has finite order, the exact order of `hp.characterFiniteRankCore χ` under `tensorPow`
is `orderOf χ`. -/
theorem isLeast_pos_trivialization_tensorPow_characterFiniteRankCore
    [CompactSpace E] [ConnectedSpace E] {χ : G →* ℂˣ} (hχ : IsOfFinOrder χ) :
    IsLeast {m : ℕ | 0 < m ∧
      ∃ (e : Trivialization (Fin (tensorPow (hp.characterFiniteRankCore χ) m).rank → ℂ)
        (π _ (tensorPow (hp.characterFiniteRankCore χ) m).core.Fiber)) (_ : e.IsLinear ℂ),
        e.toOpenPartialHomeomorph ∈
          (contMDiffFiberwiseLinear X (Fin (tensorPow (hp.characterFiniteRankCore χ) m).rank → ℂ)
            IB n).maximalAtlas
            (TotalSpace _ (tensorPow (hp.characterFiniteRankCore χ) m).core.Fiber) ∧
          e.baseSet = univ} (orderOf χ) :=
  hp.isLeast_pos_trivialization_tensorPow_characterFiniteRankCore_of_injective
    (hp.characterPicardHom_injective hpd hn) hχ

end ComplexCompact

end IsQuotientCoveringMap

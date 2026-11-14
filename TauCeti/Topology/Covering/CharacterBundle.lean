/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Covering.AssociatedBundle
public import TauCeti.Topology.VectorBundle.FiniteRank.Monoidal
public import TauCeti.Topology.VectorBundle.FiniteRank.Dual
public import TauCeti.Topology.VectorBundle.FiniteRank.Scalar

/-!
# Algebra of line bundles associated with characters of a deck group

Let `p : E → X` present `X` as the quotient of `E` by a group `G` (`IsQuotientCoveringMap p G`).
For each character `χ : G →* 𝕜ˣ`, `IsQuotientCoveringMap.characterCore χ` is the scalar line-bundle
core over `X` with transitions multiplying by `χ (deckChange e e' x)`. Restricting along the
preferred local sections and identifying `𝕜` with `Fin 1 → 𝕜` produces the point-indexed rank-one
core `IsQuotientCoveringMap.characterFiniteRankCore χ : FiniteRankBundleCore 𝕜 X`, whose total space
is canonically homeomorphic to `(hp.characterCore χ).TotalSpace` over `X`.

Because the chart domains of `associatedCore` depend only on `p` and not on the character, the
monoidal and dual operations on `FiniteRankBundleCore 𝕜 X` match the group operations on
characters `G →* 𝕜ˣ`:

* `IsQuotientCoveringMap.characterFiniteRankCoreOneIso`: the bundle of the trivial character is
  canonically isomorphic to the monoidal unit `𝟙_ (FiniteRankBundleCore 𝕜 X)`;
* `IsQuotientCoveringMap.characterFiniteRankCoreMulIso`: the tensor product of the bundles of `χ₁`
  and `χ₂` is canonically isomorphic to the bundle of `χ₁ * χ₂`;
* `IsQuotientCoveringMap.characterFiniteRankCoreInvIso`: over a complete field, the dual of the
  bundle of `χ` is canonically isomorphic to the bundle of `χ⁻¹`;
* `IsQuotientCoveringMap.characterFiniteRankCorePowIso`: the `m`-th tensor power
  `TauCeti.tensorPow (hp.characterFiniteRankCore χ) m` is canonically isomorphic to the bundle of
  `χ ^ m`.

On scalar cores, twisting chart operators by `χ₁⁻¹ (deckChange e e' x)` identifies cocycle
morphisms from `hp.characterCore χ₁` to `hp.characterCore χ₂` with cocycle morphisms from
`hp.characterCore 1` to `hp.characterCore (χ₁⁻¹ * χ₂)` while preserving all fibre maps
(`IsQuotientCoveringMap.characterCoreHomEquiv`).

## References

* Norman Steenrod, *The Topology of Fibre Bundles*, Princeton University Press, 1951, §§2–3, §8.
* Daniel Huybrechts, *Complex Geometry: An Introduction*, Springer, 2005, Section 2.2.
-/

public section

open Bundle CategoryTheory MonoidalCategory ContinuousLinearEquiv ContinuousLinearMap Set
open TauCeti TauCeti.FiniteRankBundleCore VectorBundleCore

namespace IsQuotientCoveringMap

variable {E X G : Type*} [TopologicalSpace E] [TopologicalSpace X] [Group G] [MulAction G E]
  {p : E → X} (hp : IsQuotientCoveringMap p G)

/-! ### Symmetry of deck transformations and character-core charts -/

/-- Reversing the order of two local sections over a common point of their domains inverts the deck
transformation between them. -/
theorem deckChange_inv {e e' : E} {x : X}
    (h : x ∈ (hp.isLocalHomeomorph.localInverseAt e).source ∩
      (hp.isLocalHomeomorph.localInverseAt e').source) :
    hp.deckChange e' e x = (hp.deckChange e e' x)⁻¹ :=
  mul_eq_one_iff_eq_inv.1 <| by
    rw [hp.deckChange_mul_deckChange ⟨h, h.1⟩, hp.deckChange_self h.1]

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-- The chart domain of `hp.characterCore χ` through `e` is the domain of the local section of `p`
through `e`, independently of `χ`. -/
theorem characterCore_baseSet (χ : G →* 𝕜ˣ) (e : E) :
    (hp.characterCore χ).baseSet e = (hp.isLocalHomeomorph.localInverseAt e).source := by
  rw [characterCore_def, associatedCore_baseSet]

@[simp]
theorem characterCore_localTriv_baseSet (χ : G →* 𝕜ˣ) (e : E) :
    ((hp.characterCore χ).localTriv e).baseSet =
      (hp.isLocalHomeomorph.localInverseAt e).source := by
  rw [characterCore_def, associatedCore_localTriv_baseSet]

/-- The preferred chart index of `hp.characterCore χ` at `x` is `Function.surjInv hp.surjective x`,
independently of `χ`. -/
@[simp]
theorem characterCore_indexAt (χ : G →* 𝕜ˣ) (x : X) :
    (hp.characterCore χ).indexAt x = Function.surjInv hp.surjective x := by
  rw [characterCore_def, associatedCore_indexAt]

/-! ### Point-indexed rank-one character cores -/

/-- The point-indexed rank-one vector-bundle core over `X` associated with a character
`χ : G →* 𝕜ˣ`, obtained from `hp.characterCore χ` via `FiniteRankBundleCore.ofScalarCore`. -/
@[expose]
noncomputable def characterFiniteRankCore (χ : G →* 𝕜ˣ) : FiniteRankBundleCore 𝕜 X :=
  ofScalarCore (hp.characterCore χ)

@[simp]
theorem rank_characterFiniteRankCore (χ : G →* 𝕜ˣ) :
    (hp.characterFiniteRankCore χ).rank = 1 :=
  (rfl)

/-- The chart domain of `hp.characterFiniteRankCore χ` at `x` depends only on `p`, namely it is the
source of the local section of `p` through `Function.surjInv hp.surjective x`. -/
theorem baseSet_characterFiniteRankCore (χ : G →* 𝕜ˣ) (x : X) :
    (hp.characterFiniteRankCore χ).core.baseSet x =
      (hp.isLocalHomeomorph.localInverseAt (Function.surjInv hp.surjective x)).source := by
  simp [characterFiniteRankCore]

@[simp]
theorem localTriv_baseSet_characterFiniteRankCore (χ : G →* 𝕜ˣ) (x : X) :
    ((hp.characterFiniteRankCore χ).core.localTriv x).baseSet =
      (hp.isLocalHomeomorph.localInverseAt (Function.surjInv hp.surjective x)).source := by
  rw [characterFiniteRankCore, localTriv_baseSet_ofScalarCore, characterCore_baseSet,
    characterCore_indexAt]

/-- The transition map of `hp.characterFiniteRankCore χ` from chart `i` to chart `j` at `x` scales
by `χ (hp.deckChange (Function.surjInv hp.surjective i) (Function.surjInv hp.surjective j) x)`. -/
theorem coordChange_characterFiniteRankCore_eq_smul (χ : G →* 𝕜ˣ) (i j x : X) :
    (hp.characterFiniteRankCore χ).core.coordChange i j x =
      (χ (hp.deckChange (Function.surjInv hp.surjective i)
        (Function.surjInv hp.surjective j) x) : 𝕜) •
        ContinuousLinearMap.id 𝕜 (Fin (hp.characterFiniteRankCore χ).rank → 𝕜) := by
  dsimp +instances only [characterFiniteRankCore]
  rw [coordChange_ofScalarCore_eq_smul, characterCore_coordChange_apply, mul_one,
    characterCore_indexAt, characterCore_indexAt]

/-- The trivial character gives identity transition maps on `hp.characterFiniteRankCore 1`. -/
@[simp]
theorem coordChange_characterFiniteRankCore_one (i j x : X) :
    (hp.characterFiniteRankCore (1 : G →* 𝕜ˣ)).core.coordChange i j x =
      ContinuousLinearMap.id 𝕜 (Fin (hp.characterFiniteRankCore (1 : G →* 𝕜ˣ)).rank → 𝕜) := by
  rw [hp.coordChange_characterFiniteRankCore_eq_smul, MonoidHom.one_apply, Units.val_one, one_smul]

/-- The total space of `hp.characterFiniteRankCore χ` is canonically homeomorphic to the total space
of `hp.characterCore χ` over the identity of `X`. -/
noncomputable def characterFiniteRankCoreHomeomorph (χ : G →* 𝕜ˣ) :
    (hp.characterFiniteRankCore χ).core.TotalSpace ≃ₜ (hp.characterCore χ).TotalSpace :=
  ofScalarCoreHomeomorph (hp.characterCore χ)

@[simp]
theorem coe_characterFiniteRankCoreHomeomorph (χ : G →* 𝕜ˣ) :
    ⇑(hp.characterFiniteRankCoreHomeomorph χ) = (toScalarCore (hp.characterCore χ)).totalSpaceMap :=
  coe_ofScalarCoreHomeomorph (hp.characterCore χ)

@[simp]
theorem coe_characterFiniteRankCoreHomeomorph_symm (χ : G →* 𝕜ˣ) :
    ⇑(hp.characterFiniteRankCoreHomeomorph χ).symm =
      (fromScalarCore (hp.characterCore χ)).totalSpaceMap :=
  coe_ofScalarCoreHomeomorph_symm (hp.characterCore χ)

/-! ### Multiplicativity, inversion, and tensor powers of character cores -/

variable (𝕜) in
/-- The rank-one core of the trivial character is canonically isomorphic to the monoidal unit
`𝟙_ (FiniteRankBundleCore 𝕜 X)`. -/
noncomputable def characterFiniteRankCoreOneIso :
    hp.characterFiniteRankCore (1 : G →* 𝕜ˣ) ≅ 𝟙_ (FiniteRankBundleCore 𝕜 X) :=
  isoTrivialOfCoordChangeEqId (hp.characterFiniteRankCore (1 : G →* 𝕜ˣ))
    fun i j x _ _ ↦ hp.coordChange_characterFiniteRankCore_one i j x

@[simp]
theorem fiberMap_characterFiniteRankCoreOneIso_hom (x : X) :
    (hp.characterFiniteRankCoreOneIso 𝕜).hom.fiberMap x =
      ContinuousLinearMap.id 𝕜 (Fin 1 → 𝕜) :=
  fiberMap_isoTrivialOfCoordChangeEqId_hom _ _ x

@[simp]
theorem fiberMap_characterFiniteRankCoreOneIso_inv (x : X) :
    (hp.characterFiniteRankCoreOneIso 𝕜).inv.fiberMap x =
      ContinuousLinearMap.id 𝕜 (Fin 1 → 𝕜) :=
  fiberMap_isoTrivialOfCoordChangeEqId_inv _ _ x

/-- `kroneckerLid 𝕜 1` intertwines the Kronecker product of the transition maps for `χ₁` and `χ₂`
with the transition map for `χ₁ * χ₂`. -/
theorem coordChange_characterFiniteRankCore_mul_intertwines (χ₁ χ₂ : G →* 𝕜ˣ) (i j x : X) :
    (kroneckerLid 𝕜 1 : (Fin (1 * 1) → 𝕜) →L[𝕜] (Fin 1 → 𝕜)).comp
        ((tensor (hp.characterFiniteRankCore χ₁)
          (hp.characterFiniteRankCore χ₂)).core.coordChange i j x) =
      ((hp.characterFiniteRankCore (χ₁ * χ₂)).core.coordChange i j x).comp
        (kroneckerLid 𝕜 1 : (Fin (1 * 1) → 𝕜) →L[𝕜] (Fin 1 → 𝕜)) := by
  rw [coordChange_tensor, hp.coordChange_characterFiniteRankCore_eq_smul χ₁,
    hp.coordChange_characterFiniteRankCore_eq_smul χ₂,
    hp.coordChange_characterFiniteRankCore_eq_smul (χ₁ * χ₂)]
  dsimp +instances only [characterFiniteRankCore, ofScalarCore]
  rw [smul_kronecker, kronecker_smul, id_kronecker_id, smul_smul, MonoidHom.mul_apply,
    Units.val_mul]
  set c : 𝕜 := (χ₁ (hp.deckChange (Function.surjInv hp.surjective i)
      (Function.surjInv hp.surjective j) x) : 𝕜) *
    (χ₂ (hp.deckChange (Function.surjInv hp.surjective i)
      (Function.surjInv hp.surjective j) x) : 𝕜)
  refine ContinuousLinearMap.ext fun v ↦ ?_
  change kroneckerLid 𝕜 1 (c • v) = c • kroneckerLid 𝕜 1 v
  exact ContinuousLinearEquiv.map_smul (kroneckerLid 𝕜 1) c v

/-- Chart domains of `hp.characterFiniteRankCore χ₁ ⊗ hp.characterFiniteRankCore χ₂` coincide with
those of `hp.characterFiniteRankCore (χ₁ * χ₂)`. -/
theorem baseSet_tensor_characterFiniteRankCore (χ₁ χ₂ : G →* 𝕜ˣ) (x : X) :
    (tensor (hp.characterFiniteRankCore χ₁) (hp.characterFiniteRankCore χ₂)).core.baseSet x =
      (hp.characterFiniteRankCore (χ₁ * χ₂)).core.baseSet x := by
  simp [VectorBundleCore.baseSet_at]

/-- The tensor product of the rank-one cores for `χ₁` and `χ₂` is canonically isomorphic to the
rank-one core for `χ₁ * χ₂`, acting fibrewise by `kroneckerLid 𝕜 1`. -/
noncomputable def characterFiniteRankCoreMulIso (χ₁ χ₂ : G →* 𝕜ˣ) :
    hp.characterFiniteRankCore χ₁ ⊗ hp.characterFiniteRankCore χ₂ ≅
      hp.characterFiniteRankCore (χ₁ * χ₂) :=
  constIso (A := tensor (hp.characterFiniteRankCore χ₁) (hp.characterFiniteRankCore χ₂))
    (D := hp.characterFiniteRankCore (χ₁ * χ₂))
    (hp.baseSet_tensor_characterFiniteRankCore χ₁ χ₂) (kroneckerLid 𝕜 1)
    fun i j x _ _ ↦ hp.coordChange_characterFiniteRankCore_mul_intertwines χ₁ χ₂ i j x

@[simp]
theorem fiberMap_characterFiniteRankCoreMulIso_hom (χ₁ χ₂ : G →* 𝕜ˣ) (x : X) :
    (hp.characterFiniteRankCoreMulIso χ₁ χ₂).hom.fiberMap x =
      (kroneckerLid 𝕜 1).toContinuousLinearMap := by
  unfold characterFiniteRankCoreMulIso
  exact fiberMap_constIso_hom _ _ _ x

@[simp]
theorem fiberMap_characterFiniteRankCoreMulIso_inv (χ₁ χ₂ : G →* 𝕜ˣ) (x : X) :
    (hp.characterFiniteRankCoreMulIso χ₁ χ₂).inv.fiberMap x =
      (kroneckerLid 𝕜 1).symm.toContinuousLinearMap := by
  unfold characterFiniteRankCoreMulIso
  exact fiberMap_constIso_inv _ _ _ x

/-- Chart domains of `(hp.characterFiniteRankCore χ).dual` coincide with those of
`hp.characterFiniteRankCore χ⁻¹`. -/
theorem baseSet_dual_characterFiniteRankCore [CompleteSpace 𝕜] (χ : G →* 𝕜ˣ) (x : X) :
    (hp.characterFiniteRankCore χ).dual.core.baseSet x =
      (hp.characterFiniteRankCore χ⁻¹).core.baseSet x := by
  simp [VectorBundleCore.baseSet_at]

/-- On chart overlaps, the dual transition map of `hp.characterFiniteRankCore χ` coincides with the
transition map of `hp.characterFiniteRankCore χ⁻¹`. -/
theorem coordChange_characterFiniteRankCore_inv_intertwines [CompleteSpace 𝕜] (χ : G →* 𝕜ˣ)
    (i j x : X) (hi : x ∈ (hp.characterFiniteRankCore χ).dual.core.baseSet i)
    (hj : x ∈ (hp.characterFiniteRankCore χ).dual.core.baseSet j) :
    (ContinuousLinearEquiv.refl 𝕜 (Fin 1 → 𝕜) : (Fin 1 → 𝕜) →L[𝕜] (Fin 1 → 𝕜)).comp
        ((hp.characterFiniteRankCore χ).dual.core.coordChange i j x) =
      ((hp.characterFiniteRankCore χ⁻¹).core.coordChange i j x).comp
        (ContinuousLinearEquiv.refl 𝕜 (Fin 1 → 𝕜) : (Fin 1 → 𝕜) →L[𝕜] (Fin 1 → 𝕜)) := by
  have hi' : x ∈ (hp.isLocalHomeomorph.localInverseAt (Function.surjInv hp.surjective i)).source :=
    by simpa [VectorBundleCore.baseSet_at] using hi
  have hj' : x ∈ (hp.isLocalHomeomorph.localInverseAt (Function.surjInv hp.surjective j)).source :=
    by simpa [VectorBundleCore.baseSet_at] using hj
  rw [coordChange_dual, hp.coordChange_characterFiniteRankCore_eq_smul χ j i x,
    hp.coordChange_characterFiniteRankCore_eq_smul χ⁻¹ i j x]
  dsimp +instances only [characterFiniteRankCore, ofScalarCore]
  rw [piTranspose_smul, piTranspose_id, hp.deckChange_inv ⟨hi', hj'⟩, map_inv,
    MonoidHom.inv_apply, ContinuousLinearEquiv.coe_refl]
  exact ContinuousLinearMap.ext fun _ ↦ rfl

/-- Over a complete scalar field, the dual of `hp.characterFiniteRankCore χ` is canonically
isomorphic to `hp.characterFiniteRankCore χ⁻¹`, acting as the identity on every coordinate fibre. -/
noncomputable def characterFiniteRankCoreInvIso [CompleteSpace 𝕜] (χ : G →* 𝕜ˣ) :
    (hp.characterFiniteRankCore χ).dual ≅ hp.characterFiniteRankCore χ⁻¹ :=
  constIso (A := (hp.characterFiniteRankCore χ).dual) (D := hp.characterFiniteRankCore χ⁻¹)
    (hp.baseSet_dual_characterFiniteRankCore χ) (ContinuousLinearEquiv.refl 𝕜 (Fin 1 → 𝕜))
    (hp.coordChange_characterFiniteRankCore_inv_intertwines χ)

@[simp]
theorem fiberMap_characterFiniteRankCoreInvIso_hom [CompleteSpace 𝕜] (χ : G →* 𝕜ˣ) (x : X) :
    (hp.characterFiniteRankCoreInvIso χ).hom.fiberMap x =
      ContinuousLinearMap.id 𝕜 (Fin 1 → 𝕜) := by
  unfold characterFiniteRankCoreInvIso
  exact fiberMap_constIso_hom _ _ _ x

@[simp]
theorem fiberMap_characterFiniteRankCoreInvIso_inv [CompleteSpace 𝕜] (χ : G →* 𝕜ˣ) (x : X) :
    (hp.characterFiniteRankCoreInvIso χ).inv.fiberMap x =
      ContinuousLinearMap.id 𝕜 (Fin 1 → 𝕜) := by
  unfold characterFiniteRankCoreInvIso
  exact fiberMap_constIso_inv _ _ _ x

/-- The `m`-th tensor power of `hp.characterFiniteRankCore χ` is canonically isomorphic to
`hp.characterFiniteRankCore (χ ^ m)`. -/
noncomputable def characterFiniteRankCorePowIso (χ : G →* 𝕜ˣ) :
    (m : ℕ) → tensorPow (hp.characterFiniteRankCore χ) m ≅ hp.characterFiniteRankCore (χ ^ m)
  | 0 =>
    (hp.characterFiniteRankCoreOneIso 𝕜).symm ≪≫
      eqToIso (congrArg hp.characterFiniteRankCore (pow_zero χ).symm)
  | m + 1 =>
    whiskerLeftIso (hp.characterFiniteRankCore χ) (characterFiniteRankCorePowIso χ m) ≪≫
      hp.characterFiniteRankCoreMulIso χ (χ ^ m) ≪≫
      eqToIso (congrArg hp.characterFiniteRankCore (pow_succ' χ m).symm)

@[simp]
theorem characterFiniteRankCorePowIso_zero (χ : G →* 𝕜ˣ) :
    hp.characterFiniteRankCorePowIso χ 0 =
      (hp.characterFiniteRankCoreOneIso 𝕜).symm ≪≫
        eqToIso (congrArg hp.characterFiniteRankCore (pow_zero χ).symm) := by
  rw [characterFiniteRankCorePowIso]

/-- Recursive step of the character tensor-power isomorphism. -/
theorem characterFiniteRankCorePowIso_succ (χ : G →* 𝕜ˣ) (m : ℕ) :
    hp.characterFiniteRankCorePowIso χ (m + 1) =
      whiskerLeftIso (hp.characterFiniteRankCore χ) (hp.characterFiniteRankCorePowIso χ m) ≪≫
        hp.characterFiniteRankCoreMulIso χ (χ ^ m) ≪≫
        eqToIso (congrArg hp.characterFiniteRankCore (pow_succ' χ m).symm) := by
  rw [characterFiniteRankCorePowIso]

/-! ### Twisting cocycle morphisms between scalar character cores -/

/-- On the common domain of charts `e` and `e'`, reading a family of fibre maps `ϕ` between
`hp.characterCore χ₁` and `hp.characterCore χ₂` differs from reading `ϕ` between
`hp.characterCore 1` and `hp.characterCore (χ₁⁻¹ * χ₂)` by the locally constant scalar
`χ₁ (hp.deckChange e e' x)`. -/
theorem inChartCoordinates_characterCore_eq_smul (χ₁ χ₂ : G →* 𝕜ˣ) (ϕ : X → 𝕜 →L[𝕜] 𝕜)
    (e e' : E) {x : X}
    (hx : x ∈ (hp.isLocalHomeomorph.localInverseAt e).source ∩
      (hp.isLocalHomeomorph.localInverseAt e').source) :
    (hp.characterCore χ₁).inChartCoordinates (hp.characterCore χ₂) e e' x (ϕ x) =
      (χ₁ (hp.deckChange e e' x) : 𝕜) •
        (hp.characterCore 1).inChartCoordinates (hp.characterCore (χ₁⁻¹ * χ₂)) e e' x (ϕ x) := by
  set i₀ := Function.surjInv hp.surjective x
  have hi₀ : x ∈ (hp.isLocalHomeomorph.localInverseAt i₀).source := by
    simpa only [i₀, Function.surjInv_eq hp.surjective x] using
      hp.isLocalHomeomorph.apply_self_mem_localInverseAt_source (x := i₀)
  have hmul : χ₁ (hp.deckChange e e' x) * (χ₁ (hp.deckChange i₀ e' x))⁻¹ =
      χ₁ (hp.deckChange e i₀ x) := by
    rw [← hp.deckChange_mul_deckChange ⟨⟨hx.1, hi₀⟩, hx.2⟩, map_mul, mul_comm, inv_mul_cancel_left]
  refine ContinuousLinearMap.ext fun v ↦ ?_
  have hrhs :
      ((χ₁ (hp.deckChange e e' x) : 𝕜) •
          (hp.characterCore 1).inChartCoordinates (hp.characterCore (χ₁⁻¹ * χ₂)) e e' x (ϕ x)) v =
        (χ₁ (hp.deckChange e e' x) : 𝕜) *
          ((hp.characterCore 1).inChartCoordinates (hp.characterCore (χ₁⁻¹ * χ₂)) e e' x
            (ϕ x) v) := rfl
  rw [hrhs, inChartCoordinates_apply, inChartCoordinates_apply]
  simp only [characterCore_indexAt]
  rw [hp.characterCore_coordChange_apply, hp.characterCore_coordChange_apply,
    hp.characterCore_coordChange_apply, hp.characterCore_one_coordChange,
    ContinuousLinearMap.id_apply]
  have hlin : ϕ x ((χ₁ (hp.deckChange e i₀ x) : 𝕜) * v) =
      (χ₁ (hp.deckChange e i₀ x) : 𝕜) * ϕ x v := by
    rw [← smul_eq_mul, _root_.map_smul, smul_eq_mul]
  rw [hlin, MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, ← hmul, Units.val_mul]
  ring

private def reindexCharacterOverlap {χ₁ χ₂ χ₁' χ₂' : G →* 𝕜ˣ} {e e' : E}
    (x : ↥((hp.characterCore χ₁).baseSet e ∩ (hp.characterCore χ₂).baseSet e')) :
    ↥((hp.characterCore χ₁').baseSet e ∩ (hp.characterCore χ₂').baseSet e') :=
  ⟨x.1, by simpa using x.2.1, by simpa using x.2.2⟩

private noncomputable def twistCharacterCoreOperator {χ₁ χ₂ : G →* 𝕜ˣ} (χ : G →* 𝕜ˣ)
    (a : CoordinateHom (hp.characterCore χ₁) (hp.characterCore χ₂)) (e e' : E) :
    C(↥((hp.characterCore (χ * χ₁)).baseSet e ∩ (hp.characterCore (χ * χ₂)).baseSet e'),
      𝕜 →L[𝕜] 𝕜) :=
  ⟨fun x ↦ (χ (hp.deckChange e e' x.1) : 𝕜) • a.operator e e' (hp.reindexCharacterOverlap x), by
    refine continuous_iff_continuousAt.2 fun x ↦ ?_
    have hx : x.1 ∈ (hp.isLocalHomeomorph.localInverseAt e).source ∩
        (hp.isLocalHomeomorph.localInverseAt e').source := by
      simpa using x.2
    have hconst : ContinuousAt (fun y : ↥((hp.characterCore (χ * χ₁)).baseSet e ∩
        (hp.characterCore (χ * χ₂)).baseSet e') ↦ (χ (hp.deckChange e e' y.1) : 𝕜)) x :=
      continuousAt_const.congr <|
        Filter.Eventually.mono
          (continuous_subtype_val.continuousAt.eventually (hp.eventually_deckChange_eq hx))
          fun y hy ↦ congrArg (fun g ↦ (χ g : 𝕜)) hy.symm
    have hre : Continuous (hp.reindexCharacterOverlap
        (χ₁ := χ * χ₁) (χ₂ := χ * χ₂) (χ₁' := χ₁) (χ₂' := χ₂) (e := e) (e' := e')) :=
      continuous_subtype_val.subtype_mk _
    exact hconst.smul ((a.operator e e').continuous.comp hre).continuousAt⟩

/-- Twisting a cocycle morphism `a : CoordinateHom (hp.characterCore χ₁) (hp.characterCore χ₂)` by
`χ`-multiplying its chart operators yields a cocycle morphism from `hp.characterCore (χ * χ₁)` to
`hp.characterCore (χ * χ₂)` with the exact same fibre maps. -/
private noncomputable def twistCharacterCoreHom {χ₁ χ₂ : G →* 𝕜ˣ} (χ : G →* 𝕜ˣ)
    (a : CoordinateHom (hp.characterCore χ₁) (hp.characterCore χ₂)) :
    CoordinateHom (hp.characterCore (χ * χ₁)) (hp.characterCore (χ * χ₂)) where
  operator := hp.twistCharacterCoreOperator χ a
  compatible e₁ e₂ e₁' e₂' x he₁ he₂ he₁' he₂' v := by
    have hs₁ : x ∈ (hp.isLocalHomeomorph.localInverseAt e₁).source := by simpa using he₁
    have hs₂ : x ∈ (hp.isLocalHomeomorph.localInverseAt e₂).source := by simpa using he₂
    have hs₁' : x ∈ (hp.isLocalHomeomorph.localInverseAt e₁').source := by simpa using he₁'
    have hs₂' : x ∈ (hp.isLocalHomeomorph.localInverseAt e₂').source := by simpa using he₂'
    have ha₁ : x ∈ (hp.characterCore χ₁).baseSet e₁ := by simpa using hs₁
    have ha₂ : x ∈ (hp.characterCore χ₁).baseSet e₂ := by simpa using hs₂
    have ha₁' : x ∈ (hp.characterCore χ₂).baseSet e₁' := by simpa using hs₁'
    have ha₂' : x ∈ (hp.characterCore χ₂).baseSet e₂' := by simpa using hs₂'
    have hcompat := a.compatible e₁ e₂ e₁' e₂' x ha₁ ha₂ ha₁' ha₂'
      ((χ (hp.deckChange e₁ e₂ x) : 𝕜) * v)
    have hlin : a.operator e₁ e₁' ⟨x, ha₁, ha₁'⟩ ((χ (hp.deckChange e₁ e₂ x) : 𝕜) * v) =
        (χ (hp.deckChange e₁ e₂ x) : 𝕜) * a.operator e₁ e₁' ⟨x, ha₁, ha₁'⟩ v := by
      rw [← smul_eq_mul, _root_.map_smul, smul_eq_mul]
    rw [hlin, hp.characterCore_coordChange_apply, hp.characterCore_coordChange_apply] at hcompat
    have hc₁ : (χ (hp.deckChange e₁' e₂' x) : 𝕜) * (χ (hp.deckChange e₁ e₁' x) : 𝕜) =
        (χ (hp.deckChange e₂ e₂' x) : 𝕜) * (χ (hp.deckChange e₁ e₂ x) : 𝕜) := by
      exact_mod_cast (by
        rw [← map_mul, ← map_mul, hp.deckChange_mul_deckChange ⟨⟨hs₁, hs₁'⟩, hs₂'⟩,
          hp.deckChange_mul_deckChange ⟨⟨hs₁, hs₂⟩, hs₂'⟩])
    change (hp.characterCore (χ * χ₂)).coordChange e₁' e₂' x
        ((χ (hp.deckChange e₁ e₁' x) : 𝕜) * a.operator e₁ e₁' ⟨x, ha₁, ha₁'⟩ v) =
      (χ (hp.deckChange e₂ e₂' x) : 𝕜) *
        a.operator e₂ e₂' ⟨x, ha₂, ha₂'⟩ ((hp.characterCore (χ * χ₁)).coordChange e₁ e₂ x v)
    rw [hp.characterCore_coordChange_apply, hp.characterCore_coordChange_apply,
      MonoidHom.mul_apply, MonoidHom.mul_apply, Units.val_mul, Units.val_mul]
    calc ((χ (hp.deckChange e₁' e₂' x) : 𝕜) * (χ₂ (hp.deckChange e₁' e₂' x) : 𝕜)) *
          ((χ (hp.deckChange e₁ e₁' x) : 𝕜) * a.operator e₁ e₁' ⟨x, ha₁, ha₁'⟩ v)
        = (χ (hp.deckChange e₁' e₂' x) : 𝕜) * (χ (hp.deckChange e₁ e₁' x) : 𝕜) *
            ((χ₂ (hp.deckChange e₁' e₂' x) : 𝕜) * a.operator e₁ e₁' ⟨x, ha₁, ha₁'⟩ v) := by ring
      _ = (χ (hp.deckChange e₂ e₂' x) : 𝕜) *
            ((χ₂ (hp.deckChange e₁' e₂' x) : 𝕜) *
              ((χ (hp.deckChange e₁ e₂ x) : 𝕜) * a.operator e₁ e₁' ⟨x, ha₁, ha₁'⟩ v)) := by
          rw [hc₁]; ring
      _ = (χ (hp.deckChange e₂ e₂' x) : 𝕜) *
            a.operator e₂ e₂' ⟨x, ha₂, ha₂'⟩
              (((χ (hp.deckChange e₁ e₂ x) : 𝕜) * (χ₁ (hp.deckChange e₁ e₂ x) : 𝕜)) * v) := by
          rw [hcompat]; congr 2; ring

private theorem fiberMap_twistCharacterCoreHom {χ₁ χ₂ : G →* 𝕜ˣ} (χ : G →* 𝕜ˣ)
    (a : CoordinateHom (hp.characterCore χ₁) (hp.characterCore χ₂)) (x : X) :
    (hp.twistCharacterCoreHom χ a).fiberMap x = a.fiberMap x := by
  rw [CoordinateHom.fiberMap_def, CoordinateHom.fiberMap_def]
  set i₀ := Function.surjInv hp.surjective x
  have hs : x ∈ (hp.isLocalHomeomorph.localInverseAt i₀).source := by
    simpa only [i₀, Function.surjInv_eq hp.surjective x] using
      hp.isLocalHomeomorph.apply_self_mem_localInverseAt_source (x := i₀)
  have h1 : (hp.characterCore (χ * χ₁)).indexAt x = i₀ := hp.characterCore_indexAt _ x
  have h2 : (hp.characterCore (χ * χ₂)).indexAt x = i₀ := hp.characterCore_indexAt _ x
  have h3 : (hp.characterCore χ₁).indexAt x = i₀ := hp.characterCore_indexAt _ x
  have h4 : (hp.characterCore χ₂).indexAt x = i₀ := hp.characterCore_indexAt _ x
  conv_lhs =>
    change (χ (hp.deckChange ((hp.characterCore (χ * χ₁)).indexAt x)
        ((hp.characterCore (χ * χ₂)).indexAt x) x) : 𝕜) •
      a.operator ((hp.characterCore (χ * χ₁)).indexAt x) ((hp.characterCore (χ * χ₂)).indexAt x)
        (hp.reindexCharacterOverlap ⟨x, (hp.characterCore (χ * χ₁)).mem_baseSet_at x,
          (hp.characterCore (χ * χ₂)).mem_baseSet_at x⟩)
  have hcast :
      a.operator ((hp.characterCore (χ * χ₁)).indexAt x) ((hp.characterCore (χ * χ₂)).indexAt x)
          (hp.reindexCharacterOverlap ⟨x, (hp.characterCore (χ * χ₁)).mem_baseSet_at x,
            (hp.characterCore (χ * χ₂)).mem_baseSet_at x⟩) =
        a.operator ((hp.characterCore χ₁).indexAt x) ((hp.characterCore χ₂).indexAt x)
          ⟨x, (hp.characterCore χ₁).mem_baseSet_at x,
            (hp.characterCore χ₂).mem_baseSet_at x⟩ := by
    rw [CoordinateHom.operator_eq, CoordinateHom.operator_eq]
    dsimp only [reindexCharacterOverlap]
    rw [h1, h2, h3, h4]
  rw [hcast, h1, h2, hp.deckChange_self hs, map_one, Units.val_one, one_smul]

/-- Transporting along equalities of characters preserves cocycle morphisms and fibre maps. -/
private def castCharacterCoreHom {χ₁ χ₁' χ₂ χ₂' : G →* 𝕜ˣ} (h₁ : χ₁ = χ₁') (h₂ : χ₂ = χ₂')
    (a : CoordinateHom (hp.characterCore χ₁) (hp.characterCore χ₂)) :
    CoordinateHom (hp.characterCore χ₁') (hp.characterCore χ₂') :=
  h₁ ▸ h₂ ▸ a

private theorem fiberMap_castCharacterCoreHom {χ₁ χ₁' χ₂ χ₂' : G →* 𝕜ˣ}
    (h₁ : χ₁ = χ₁') (h₂ : χ₂ = χ₂')
    (a : CoordinateHom (hp.characterCore χ₁) (hp.characterCore χ₂)) (x : X) :
    (hp.castCharacterCoreHom h₁ h₂ a).fiberMap x = a.fiberMap x := by
  subst h₁; subst h₂; rfl

/-- Cocycle morphisms between `hp.characterCore χ₁` and `hp.characterCore χ₂` correspond
additively to cocycle morphisms between `hp.characterCore 1` and `hp.characterCore (χ₁⁻¹ * χ₂)`
with the exact same fibre maps, without completeness assumptions on `𝕜`. -/
noncomputable def characterCoreHomEquiv (χ₁ χ₂ : G →* 𝕜ˣ) :
    CoordinateHom (hp.characterCore χ₁) (hp.characterCore χ₂) ≃+
      CoordinateHom (hp.characterCore 1) (hp.characterCore (χ₁⁻¹ * χ₂)) where
  toFun a := hp.castCharacterCoreHom (inv_mul_cancel χ₁) rfl (hp.twistCharacterCoreHom χ₁⁻¹ a)
  invFun b := hp.castCharacterCoreHom (mul_one χ₁) (mul_inv_cancel_left χ₁ χ₂)
    (hp.twistCharacterCoreHom χ₁ b)
  left_inv a := CoordinateHom.fiberMap_injective <| funext fun x ↦ by
    rw [fiberMap_castCharacterCoreHom, fiberMap_twistCharacterCoreHom,
      fiberMap_castCharacterCoreHom, fiberMap_twistCharacterCoreHom]
  right_inv b := CoordinateHom.fiberMap_injective <| funext fun x ↦ by
    rw [fiberMap_castCharacterCoreHom, fiberMap_twistCharacterCoreHom,
      fiberMap_castCharacterCoreHom, fiberMap_twistCharacterCoreHom]
  map_add' a₁ a₂ := CoordinateHom.fiberMap_injective <| funext fun x ↦ by
    rw [CoordinateHom.fiberMap_add, fiberMap_castCharacterCoreHom, fiberMap_twistCharacterCoreHom,
      fiberMap_castCharacterCoreHom, fiberMap_twistCharacterCoreHom,
      fiberMap_castCharacterCoreHom, fiberMap_twistCharacterCoreHom, CoordinateHom.fiberMap_add]

@[simp]
theorem fiberMap_characterCoreHomEquiv (χ₁ χ₂ : G →* 𝕜ˣ)
    (a : CoordinateHom (hp.characterCore χ₁) (hp.characterCore χ₂)) (x : X) :
    (hp.characterCoreHomEquiv χ₁ χ₂ a).fiberMap x = a.fiberMap x := by
  dsimp only [characterCoreHomEquiv, AddEquiv.coe_mk, Equiv.coe_fn_mk]
  rw [fiberMap_castCharacterCoreHom, fiberMap_twistCharacterCoreHom]

@[simp]
theorem fiberMap_characterCoreHomEquiv_symm (χ₁ χ₂ : G →* 𝕜ˣ)
    (b : CoordinateHom (hp.characterCore 1) (hp.characterCore (χ₁⁻¹ * χ₂))) (x : X) :
    ((hp.characterCoreHomEquiv χ₁ χ₂).symm b).fiberMap x = b.fiberMap x := by
  dsimp only [characterCoreHomEquiv, AddEquiv.symm_mk, AddEquiv.coe_mk, Equiv.coe_fn_symm_mk]
  rw [fiberMap_castCharacterCoreHom, fiberMap_twistCharacterCoreHom]

/-- Reading a fibrewise scalar-multiplication map `v ↦ v • s x` from `hp.characterCore 1` to
`hp.characterCore χ` in charts `(e, e')` gives scalar multiplication by the local coordinate of `s`
in the chart `e'`. -/
theorem inChartCoordinates_characterCore_one_smulRight (χ : G →* 𝕜ˣ)
    (s : X → 𝕜) (e e' : E) (x : X) :
    (hp.characterCore 1).inChartCoordinates (hp.characterCore χ) e e' x
        ((ContinuousLinearMap.id 𝕜 𝕜).smulRight (s x)) =
      (ContinuousLinearMap.id 𝕜 𝕜).smulRight
        (((hp.characterCore χ).localTriv e' ⟨x, s x⟩).2) := by
  refine ContinuousLinearMap.ext fun v ↦ ?_
  rw [inChartCoordinates_apply, hp.characterCore_one_coordChange, ContinuousLinearMap.id_apply,
    smulRight_apply, ContinuousLinearMap.id_apply, _root_.map_smul, localTriv_apply,
    smulRight_apply, ContinuousLinearMap.id_apply]

end IsQuotientCoveringMap

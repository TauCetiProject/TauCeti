/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Boundary.Augmentation
public import TauCeti.Geometry.Manifold.Morse.Boundary.Integral

/-!
# The augmentation of the integral Morse complex

Let `f` be a Morse function on a compact boundaryless manifold `M`, `X` a Morse–Smale
pseudo-gradient adapted to `f`, and `𝔬` orientation data for the integral Morse boundary
(`TauCeti.MorseOrientation`). At a critical point `q` of index `0` the unstable manifold is the
point `q` itself, and `𝔬` orients it by one of the two orientations of the zero space: the
positive one, that of the empty basis, or its opposite. Its **augmentation sign**
(`TauCeti.MorseOrientation.augmentationSign`) is `1` or `-1` accordingly, and `0` at the critical
points of positive index. The **augmentation** of the integral Morse chains
(`TauCeti.MorseOrientation.signedMorseAugmentation`) adds up the coefficients of the critical
points of index `0`, weighted by these signs.

The main theorem is that the augmentation vanishes on boundaries: `ε ∘ ∂ = 0` over every ring of
coefficients. Only the boundaries of critical points `p` of index `1` matter. The unstable manifold
of such a `p` is a line through `p`, made of two trajectories leaving `p` in opposite directions
(`TauCeti.IsAdaptedPseudoGradient.exists_unstableSet_eq_insert_union_orbit`), and under the
Morse–Smale condition each of them ends at a critical point of index `0`. The two trajectories
count with opposite signs
(`TauCeti.IsAdaptedPseudoGradient.trajectorySign_eq_neg_of_notMem_orbit`): along a trajectory
from `p` to a critical point of index `0`, the sign of the trajectory, corrected by the
augmentation sign of its end, compares the orientation of `W^u(p)` with the direction of `-X`,
opposite to the direction in which the trajectory leaves `p`. So the two trajectories cancel in
the augmentation of the boundary of `p`.

In particular, if `f` has a single critical point `m` of index `0`, the two trajectories from
every critical point of index `1` both end at `m` and carry opposite signs, so the integral
boundary never reaches `m` (`IsMorseSmale.signedMorseBoundaryCoeff_eq_zero_of_unique_index_zero`).
This is the integral form of
`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.morseBoundaryCoeff_eq_zero_of_unique_index_zero`:
for the sphere with one minimum, the torus with its standard height function, or the real
projective plane with its moment function, the integral boundary vanishes in degree `1`.

Over `ZMod 2` the augmentation is the mod-two augmentation `TauCeti.morseAugmentation`, whatever
the orientations, and reversing orientations composes it with the corresponding sign reversal of
the chains, as for the boundary.

## Main definitions

* `TauCeti.MorseOrientation.augmentationSign`: the sign of the orientation at a critical point of
  index `0`, and `0` at the other critical points.
* `TauCeti.MorseOrientation.signedMorseAugmentation`: the augmentation of the Morse chains with
  coefficients in a ring `R`.

## Main results

* `TauCeti.MorseChart.exists_basis_fst_eq_one_orientation_eq`: at a critical point of index `0`,
  the orientation of `ℝ × V` against which trajectory signs are measured is that of a basis whose
  vectors all have first coordinate `1`.

In the namespace `TauCeti.IsAdaptedPseudoGradient`:

* `trajectorySign_eq_neg_of_notMem_orbit`: two different trajectories leaving a critical point of
  index `1` carry opposite signs, measured against the orientations of the empty basis at their
  ends.
* `IsMorseSmale.finsum_augmentationSign_mul_signedMorseBoundaryCoeff`: the boundary coefficients of
  a critical point, weighted by the augmentation signs, add up to zero.
* `IsMorseSmale.signedMorseAugmentation_comp_signedMorseBoundary`: `ε ∘ ∂ = 0`.
* `IsMorseSmale.signedMorseBoundaryCoeff_eq_zero_of_unique_index_zero`: the integral boundary does
  not reach a unique critical point of index `0`.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §2.3 (orientations and the Morse complex over `ℤ`).
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 4 (the Morse complex with integer coefficients, and its homology in degree `0`).
-/

public section

open Function Module Set
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}

namespace MorseOrientation

variable (𝔬 : MorseOrientation f X)

/-- The **augmentation sign** at a critical point `q`. When `q` has index `0`, the space of
coordinates of negative weight of the chart at `q` is zero, and the orientation chosen there is
either its positive orientation, that of the empty basis, or the opposite one; the sign is `1` in
the first case and `-1` in the second. At the critical points of positive index the sign is `0`. -/
noncomputable def augmentationSign (q : criticalPoints 𝓘(ℝ, E) f) : ℤ :=
  if manifoldMorseIndex 𝓘(ℝ, E) f q = 0 then
    ((𝔬.orientation q).signBasis
      (Module.finBasisOfFinrankEq ℝ _ (𝔬.chart q).finrank_negativeWeight_fun) : ℤ)
  else 0

/-- At a critical point of index `0`, the augmentation sign is the sign of the orientation relative
to the empty basis. -/
theorem augmentationSign_of_morseIndex_eq_zero {q : criticalPoints 𝓘(ℝ, E) f}
    (hq : manifoldMorseIndex 𝓘(ℝ, E) f q = 0) :
    𝔬.augmentationSign q = ((𝔬.orientation q).signBasis
      (Module.finBasisOfFinrankEq ℝ _ (𝔬.chart q).finrank_negativeWeight_fun) : ℤ) :=
  ite_eq_left hq

/-- The augmentation sign vanishes at the critical points of positive index. -/
@[simp]
theorem augmentationSign_of_morseIndex_ne_zero {q : criticalPoints 𝓘(ℝ, E) f}
    (hq : manifoldMorseIndex 𝓘(ℝ, E) f q ≠ 0) : 𝔬.augmentationSign q = 0 :=
  ite_eq_right hq

/-- At a critical point of index `0`, the augmentation sign is `±1`. -/
theorem augmentationSign_eq_one_or_eq_neg_one {q : criticalPoints 𝓘(ℝ, E) f}
    (hq : manifoldMorseIndex 𝓘(ℝ, E) f q = 0) :
    𝔬.augmentationSign q = 1 ∨ 𝔬.augmentationSign q = -1 := by
  rw [augmentationSign_of_morseIndex_eq_zero 𝔬 hq]
  rcases Int.units_eq_one_or ((𝔬.orientation q).signBasis
    (Module.finBasisOfFinrankEq ℝ _ (𝔬.chart q).finrank_negativeWeight_fun)) with h | h <;> simp [h]

/-- Modulo two, the augmentation sign is `1` at the critical points of index `0` and `0`
elsewhere, whatever the orientations. -/
theorem intCast_augmentationSign (q : criticalPoints 𝓘(ℝ, E) f) :
    (𝔬.augmentationSign q : ZMod 2) = if manifoldMorseIndex 𝓘(ℝ, E) f q = 0 then 1 else 0 := by
  by_cases hq : manifoldMorseIndex 𝓘(ℝ, E) f q = 0
  · rw [ite_eq_left hq]
    rcases 𝔬.augmentationSign_eq_one_or_eq_neg_one hq with h | h <;> rw [h] <;> decide
  · rw [ite_eq_right hq, 𝔬.augmentationSign_of_morseIndex_ne_zero hq, Int.cast_zero]

/-- **Reversing orientations changes the augmentation signs** at the critical points of the
reversed set. -/
theorem augmentationSign_reverse (S : Set (criticalPoints 𝓘(ℝ, E) f)) [DecidablePred (· ∈ S)]
    (q : criticalPoints 𝓘(ℝ, E) f) :
    (𝔬.reverse S).augmentationSign q = (if q ∈ S then -1 else 1) * 𝔬.augmentationSign q := by
  by_cases hq : manifoldMorseIndex 𝓘(ℝ, E) f q = 0
  · -- The reversed data has the same charts, so the two signs are taken in the same basis.
    -- `simp` cannot rewrite `(𝔬.reverse S).chart` to `𝔬.chart` (`reverse_chart`) inside the
    -- dependent type of the basis, so each branch closes up to that definitional equality.
    by_cases hS : q ∈ S
    · simp only [augmentationSign, hq, hS, ↓reduceIte, reverse_orientation, neg_one_mul]
      exact congrArg Units.val (Orientation.signBasis_neg _ _)
    · simp only [augmentationSign, hq, hS, ↓reduceIte, reverse_orientation, one_mul]
      rfl
  · simp [hq]

/-- The **augmentation** of the Morse chains with coefficients in a ring `R`: the sum of the
coefficients at the critical points of index `0`, each weighted by its augmentation sign. -/
noncomputable def signedMorseAugmentation (R : Type*) [Ring R] :
    (criticalPoints 𝓘(ℝ, E) f →₀ R) →ₗ[R] R :=
  Finsupp.linearCombination R fun q ↦ (𝔬.augmentationSign q : R)

variable {R : Type*} [Ring R]

/-- The augmentation of a chain `c` is the sum of its coefficients weighted by the augmentation
signs. -/
theorem signedMorseAugmentation_apply (c : criticalPoints 𝓘(ℝ, E) f →₀ R) :
    𝔬.signedMorseAugmentation R c = c.sum fun q a ↦ a * (𝔬.augmentationSign q : R) := by
  simp [signedMorseAugmentation, Finsupp.linearCombination_apply, smul_eq_mul]

/-- The augmentation of `a • q` is `a` times the augmentation sign of `q`. -/
@[simp]
theorem signedMorseAugmentation_single (q : criticalPoints 𝓘(ℝ, E) f) (a : R) :
    𝔬.signedMorseAugmentation R (Finsupp.single q a) = a * (𝔬.augmentationSign q : R) := by
  simp [signedMorseAugmentation, smul_eq_mul]

/-- **Change of coefficients.** An additive map `g : R → R'` commutes with the augmentations with
coefficients in `R` and in `R'`, since the augmentation signs are integers. -/
theorem map_signedMorseAugmentation {R' F : Type*} [Ring R'] [FunLike F R R']
    [AddMonoidHomClass F R R'] (g : F) (c : criticalPoints 𝓘(ℝ, E) f →₀ R) :
    g (𝔬.signedMorseAugmentation R c) =
      𝔬.signedMorseAugmentation R' (Finsupp.mapRange g (map_zero g) c) := by
  rw [signedMorseAugmentation_apply, signedMorseAugmentation_apply,
    Finsupp.sum_mapRange_index (fun _ ↦ zero_mul _), map_finsuppSum]
  simp only [← zsmul_eq_mul', map_zsmul]

/-- **With coefficients in `ZMod 2`, the augmentation is the mod-two augmentation**, whatever the
orientations. -/
theorem signedMorseAugmentation_eq_morseAugmentation :
    𝔬.signedMorseAugmentation (ZMod 2) = morseAugmentation f :=
  Finsupp.lhom_ext fun q a ↦ by
    rw [signedMorseAugmentation_single, morseAugmentation_single, intCast_augmentationSign]
    split_ifs <;> simp

/-- **Reversing orientations composes the augmentation with the sign reversal** of the chains on
the reversed set. -/
theorem signedMorseAugmentation_reverse (S : Set (criticalPoints 𝓘(ℝ, E) f))
    [DecidablePred (· ∈ S)] :
    (𝔬.reverse S).signedMorseAugmentation R =
      𝔬.signedMorseAugmentation R ∘ₗ (Finsupp.signReversal R S).toLinearMap := by
  refine Finsupp.lhom_ext fun q a ↦ ?_
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [signedMorseAugmentation_single, Finsupp.signReversal_single, signedMorseAugmentation_single,
    augmentationSign_reverse]
  by_cases hS : q ∈ S <;> simp [hS]

end MorseOrientation

namespace MorseChart

/-- **The target orientation at a critical point of index `0`.** When `q` has index `0`, the
orientation of `ℝ × V`, for `V = 0` the space of coordinates of negative weight at `q`, made of the
standard orientation of `ℝ` followed by the positive orientation of `V`, is that of a basis whose
vectors all have first coordinate `1`. -/
theorem exists_basis_fst_eq_one_orientation_eq {q : M} (φq : MorseChart E f q)
    (hq : manifoldMorseIndex 𝓘(ℝ, E) f q = 0) {n : ℕ}
    (hn : 1 + manifoldMorseIndex 𝓘(ℝ, E) f q = n) :
    ∃ B₀ : Module.Basis (Fin n) ℝ (ℝ × ({i // φq.weight i < 0} → ℝ)), (∀ j, (B₀ j).1 = 1) ∧
      ((Module.Basis.singleton (Fin 1) ℝ).orientation.prod
          (Module.finBasisOfFinrankEq ℝ _ φq.finrank_negativeWeight_fun).orientation
          (Module.finrank_self ℝ) φq.finrank_negativeWeight_fun).reindex ℝ _ (finCongr hn) =
        B₀.orientation := by
  refine ⟨(((Module.Basis.singleton (Fin 1) ℝ).prod
    (Module.finBasisOfFinrankEq ℝ _ φq.finrank_negativeWeight_fun)).reindex finSumFinEquiv).reindex
      (finCongr hn), fun j ↦ ?_, ?_⟩
  · rw [Module.Basis.reindex_apply, Module.Basis.reindex_apply]
    rcases finSumFinEquiv.symm ((finCongr hn).symm j) with k | k
    · rw [Module.Basis.prod_apply_inl_fst, Module.Basis.singleton_apply]
    · exact absurd k.isLt (by omega)
  · rw [Orientation.prod_basis_orientation]
    simp only [Module.Basis.orientation_reindex]

end MorseChart

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [T2Space M]

namespace IsAdaptedPseudoGradient

variable {hX : IsAdaptedPseudoGradient f X}

/-! ### Signs of the trajectories into a critical point of index `0` -/

/-- **The sign of a trajectory into a critical point of index `0`.** Let `q` have index `0` and `p`
index `1`, and let `C` be a basis of the coordinates of negative weight at `p` whose vectors are
sent by the unstable frame at `y` to vectors along which `f` increases. Then the comparison map at
`y` is an isomorphism, and the sign at `y`, measured against the positive orientation at `q`, is
the sign of `op` relative to `C`. -/
private theorem trajectorySign_eq_signBasis {p q : M} {φp : MorseChart E f p}
    {φq : MorseChart E f q} (hq : manifoldMorseIndex 𝓘(ℝ, E) f q = 0)
    (hpq : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1) {y : M}
    (op : Orientation ℝ ({i // φp.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f p)))
    (C : Module.Basis (Fin (manifoldMorseIndex 𝓘(ℝ, E) f p)) ℝ ({i // φp.weight i < 0} → ℝ))
    (hC : ∀ j, 0 < mvfderiv 𝓘(ℝ, E) f y (hX.unstableFrame φp y (C j))) :
    hX.trajectorySign φp φq op
        (Module.finBasisOfFinrankEq ℝ _ φq.finrank_negativeWeight_fun).orientation hpq y =
      (op.signBasis C : ℤ) := by
  classical
  set b := Module.finBasisOfFinrankEq ℝ _ φq.finrank_negativeWeight_fun
  have hsub : Subsingleton ({i // φq.weight i < 0} → ℝ) :=
    Module.finrank_zero_iff.1 (φq.finrank_negativeWeight_fun.trans hq)
  -- The comparison map is onto, since `f` increases along `C j`, and both sides are lines.
  have hy : Bijective (hX.trajectoryComparison φp φq y) := by
    have hsurj : Surjective (hX.trajectoryComparison φp φq y) := fun w ↦ by
      let j : Fin (manifoldMorseIndex 𝓘(ℝ, E) f p) := ⟨0, by omega⟩
      refine ⟨(w.1 / mvfderiv 𝓘(ℝ, E) f y (hX.unstableFrame φp y (C j))) • C j,
        Prod.ext ?_ (Subsingleton.elim _ _)⟩
      simp only [map_smul, Prod.smul_fst, trajectoryComparison_apply, smul_eq_mul]
      exact div_mul_cancel₀ _ (hC j).ne'
    refine ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).2 hsurj, hsurj⟩
    rw [Module.finrank_prod, Module.finrank_self, φp.finrank_negativeWeight_fun,
      φq.finrank_negativeWeight_fun]
    omega
  set e := LinearEquiv.ofBijective (hX.trajectoryComparison φp φq y).toLinearMap hy
  have he (v : {i // φp.weight i < 0} → ℝ) : e v = hX.trajectoryComparison φp φq y v :=
    LinearEquiv.ofBijective_apply _ v
  -- The target orientation is that of a basis whose vectors are all `(1, 0)`.
  obtain ⟨B₀, hB₀, hT'⟩ := φq.exists_basis_fst_eq_one_orientation_eq hq
    (by omega : 1 + manifoldMorseIndex 𝓘(ℝ, E) f q = manifoldMorseIndex 𝓘(ℝ, E) f p)
  have hT : φq.trajectoryTargetOrientation b.orientation hpq = B₀.orientation := by
    rw [MorseChart.trajectoryTargetOrientation_def]
    exact hT'
  -- The comparison map carries `C` to positive multiples of the vectors of `B₀`.
  have hCe : C.map e = B₀.unitsSMul fun j ↦ Units.mk0 _ (hC j).ne' := by
    refine Module.Basis.eq_of_apply_eq fun j ↦ Prod.ext ?_ (Subsingleton.elim _ _)
    rw [Module.Basis.map_apply, he, trajectoryComparison_apply, Module.Basis.unitsSMul_apply,
      Prod.smul_fst, hB₀, Units.smul_def, Units.val_mk0, smul_eq_mul, mul_one]
  have hpos : 0 < (((∏ j, Units.mk0 _ (hC j).ne')⁻¹ : ℝˣ) : ℝ) := by
    rw [Units.val_inv_eq_inv_val, Units.coe_prod]
    exact inv_pos.2 (Finset.prod_pos fun j _ ↦ hC j)
  have hTe :
      φq.trajectoryTargetOrientation b.orientation hpq = Orientation.map _ e C.orientation := by
    rw [hT, ← Module.Basis.orientation_map, hCe, Module.Basis.orientation_unitsSMul,
      Module.Ray.units_smul_of_pos _ hpos]
  rw [trajectorySign_of_bijective hy, hTe]
  split_ifs with hc
  · rw [(Orientation.map _ e).injective hc, Orientation.signBasis_orientation, Units.val_one]
  · have h : op ≠ C.orientation := fun h ↦ hc (h ▸ rfl)
    rw [(C.orientation_eq_or_eq_neg op).resolve_left h, Orientation.signBasis_neg,
      Orientation.signBasis_orientation, Units.val_neg, Units.val_one]

/-- **Different trajectories leave a critical point of index `1` in opposite directions.** If
`y₁` and `y₂` are points of `W^u(p)` on different orbits, away from the critical points, the
unstable frames at
`y₁` and `y₂` send to their velocities two vectors `a₁ ≠ 0` and `a₂ = κ a₁` with `κ < 0`. -/
private theorem exists_unstableFrame_eq_of_morseIndex_eq_one (hf : IsMorse 𝓘(ℝ, E) f) {p : M}
    {φp : MorseChart E f p}
    (hφp : ∀ y ∈ φp.toChart.source,
      φp.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φp.toChart y (X y)) =
        fun i ↦ -(φp.weight i * φp.coord (φp.toChart y) i))
    (hp : manifoldMorseIndex 𝓘(ℝ, E) f p = 1) {y₁ y₂ : M} (hy₁ : y₁ ∈ hX.flow.unstableSet p)
    (hy₂ : y₂ ∈ hX.flow.unstableSet p) (hX₁ : X y₁ ≠ 0) (hX₂ : X y₂ ≠ 0)
    (hne : y₂ ∉ hX.flow.orbit y₁) :
    ∃ a₁ a₂ : {i // φp.weight i < 0} → ℝ, ∃ κ : ℝ, κ < 0 ∧ a₁ ≠ 0 ∧ κ • a₁ = a₂ ∧
      hX.unstableFrame φp y₁ a₁ = X y₁ ∧ hX.unstableFrame φp y₂ a₂ = X y₂ := by
  obtain ⟨T₁, hT₁⟩ := (hX.eventually_mem_linearBackwardTimes hφp hf hy₁).exists
  obtain ⟨T₂, hT₂⟩ := (hX.eventually_mem_linearBackwardTimes hφp hf hy₂).exists
  have ha₁ := unstableFrame_exp_smul_negativeCoord hφp hf hy₁ hT₁
  have ha₂ := unstableFrame_exp_smul_negativeCoord hφp hf hy₂ hT₂
  set a₁ := Real.exp T₁ • φp.negativeCoord (φp.toChart (hX.flow (-T₁) y₁))
  set a₂ := Real.exp T₂ • φp.negativeCoord (φp.toChart (hX.flow (-T₂) y₂))
  have ha₁0 : a₁ ≠ 0 := fun h ↦ hX₁ (by rw [← ha₁, h, map_zero])
  -- The line `W^u(p)` is one-dimensional, so `a₂ = κ a₁`; a positive `κ` would put `y₂` on the
  -- orbit of `y₁`, and `κ = 0` would make `X y₂` vanish.
  obtain ⟨κ, hκ⟩ := exists_smul_eq_of_finrank_eq_one (φp.finrank_negativeWeight_fun.trans hp)
    ha₁0 a₂
  refine ⟨a₁, a₂, κ, ?_, ha₁0, hκ, ha₁, ha₂⟩
  rcases lt_trichotomy κ 0 with h | rfl | h
  · exact h
  · exact absurd (ha₂.symm.trans (by rw [← hκ, zero_smul, map_zero])) hX₂
  · exact (hne (hX.flow.mem_orbit_iff.2
      ⟨_, flow_log_eq_of_exp_smul_negativeCoord_eq hφp hf hy₁ hy₂ hT₁ hT₂ h hκ.symm⟩)).elim

/-- **Two trajectories leaving a critical point of index `1` carry opposite signs.** Let `p` be a
critical point of index `1` and `y₁`, `y₂` points of `W^u(p)` on different orbits, other than `p`.
Measured as trajectories into critical points `q₁` and `q₂` of index `0`, against the positive
orientations there, those of the empty basis, the two have opposite signs: they leave `p` in the
two opposite directions of the line `W^u(p)`. -/
theorem trajectorySign_eq_neg_of_notMem_orbit (hf : IsMorse 𝓘(ℝ, E) f)
    {p q₁ q₂ : M} {φp : MorseChart E f p} {φq₁ : MorseChart E f q₁} {φq₂ : MorseChart E f q₂}
    (hφp : ∀ y ∈ φp.toChart.source,
      φp.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φp.toChart y (X y)) =
        fun i ↦ -(φp.weight i * φp.coord (φp.toChart y) i))
    (op : Orientation ℝ ({i // φp.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f p)))
    (hp : manifoldMorseIndex 𝓘(ℝ, E) f p = 1)
    (hpq₁ : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q₁ + 1)
    (hpq₂ : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q₂ + 1) {y₁ y₂ : M}
    (hy₁ : y₁ ∈ hX.flow.unstableSet p) (hy₂ : y₂ ∈ hX.flow.unstableSet p)
    (hy₁₀ : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y₁ ≠ 0) (hy₂₀ : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y₂ ≠ 0)
    (hne : y₂ ∉ hX.flow.orbit y₁) :
    hX.trajectorySign φp φq₂ op
        (Module.finBasisOfFinrankEq ℝ _ φq₂.finrank_negativeWeight_fun).orientation hpq₂ y₂ =
      -hX.trajectorySign φp φq₁ op
        (Module.finBasisOfFinrankEq ℝ _ φq₁.finrank_negativeWeight_fun).orientation hpq₁ y₁ := by
  have hrank : finrank ℝ ({i // φp.weight i < 0} → ℝ) = 1 := φp.finrank_negativeWeight_fun.trans hp
  -- Along each trajectory, `f` decreases in the direction `X`.
  have hdf₁ := hX.mvfderiv_apply_lt_zero y₁ hy₁₀
  have hdf₂ := hX.mvfderiv_apply_lt_zero y₂ hy₂₀
  -- The directions `aᵢ` in which the trajectories leave `p` are opposite, and the frame sends
  -- them to `X yᵢ`.
  obtain ⟨a₁, a₂, κ, hκ0, ha₁0, hκ, ha₁, ha₂⟩ := exists_unstableFrame_eq_of_morseIndex_eq_one hf hφp
    hp hy₁ hy₂ (hX.ne_zero_of_mfderiv_ne_zero hy₁₀) (hX.ne_zero_of_mfderiv_ne_zero hy₂₀) hne
  -- Bases of the line of coordinates of negative weight at `p`, along `-a₁` and `-a₂`.
  have : Unique (Fin (manifoldMorseIndex 𝓘(ℝ, E) f p)) := by rw [hp]; infer_instance
  set C₁ := FiniteDimensional.basisSingleton (Fin (manifoldMorseIndex 𝓘(ℝ, E) f p)) hrank (-a₁)
    (neg_ne_zero.2 ha₁0)
  have hC₁ (j) : C₁ j = -a₁ := FiniteDimensional.basisSingleton_apply _ _ _ _ j
  set C₂ := C₁.unitsSMul fun _ ↦ Units.mk0 κ hκ0.ne with hC₂def
  have hC₂ (j) : C₂ j = -a₂ := by
    rw [hC₂def, Module.Basis.unitsSMul_apply, hC₁, Units.smul_def, Units.val_mk0, smul_neg, hκ]
  have hor : C₂.orientation = -C₁.orientation := by
    rw [hC₂def, Module.Basis.orientation_unitsSMul]
    refine Module.Ray.units_smul_of_neg _ ?_ _
    rw [Units.val_inv_eq_inv_val, Units.coe_prod, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, hp, pow_one, Units.val_mk0]
    exact inv_lt_zero.2 hκ0
  -- Each sign compares `op` with the basis along `-aᵢ`, along which `f` increases.
  rw [trajectorySign_eq_signBasis (by omega) hpq₂ op C₂
      fun j ↦ by rw [hC₂, map_neg, ha₂, map_neg]; linarith,
    trajectorySign_eq_signBasis (by omega) hpq₁ op C₁
      fun j ↦ by rw [hC₁, map_neg, ha₁, map_neg]; linarith,
    Orientation.signBasis_eq_neg_of_orientation_eq_neg op C₁ C₂ hor, Units.val_neg]

/-! ### The augmentation vanishes on boundaries -/

namespace IsMorseSmale

variable (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f) (𝔬 : MorseOrientation f X)
include h hf

/-- **The augmentation of the boundary of a critical point vanishes.** For every critical point
`p`, the coefficients of the integral boundary of `p`, weighted by the augmentation signs, add up
to zero. Only a critical point `p` of index `1` has nonzero coefficients at critical points of
index `0`; its two trajectories leave `p` in opposite directions and cancel. -/
theorem finsum_augmentationSign_mul_signedMorseBoundaryCoeff (p : criticalPoints 𝓘(ℝ, E) f) :
    ∑ᶠ q, 𝔬.augmentationSign q * hX.signedMorseBoundaryCoeff 𝔬 p q = 0 := by
  classical
  have := hf.finite_criticalPoints.fintype
  rw [finsum_eq_sum_of_fintype]
  by_cases hp : manifoldMorseIndex 𝓘(ℝ, E) f p = 1
  swap
  · -- Away from index `1`, no critical point of index `0` appears in the boundary.
    refine Finset.sum_eq_zero fun q _ ↦ ?_
    by_cases hq : manifoldMorseIndex 𝓘(ℝ, E) f q = 0
    · rw [signedMorseBoundaryCoeff_eq_zero_of_morseIndex_ne_add_one (by omega), mul_zero]
    · rw [𝔬.augmentationSign_of_morseIndex_ne_zero hq, zero_mul]
  -- The two trajectories leaving `p` cross the middle levels at `w i` and end at `bc i`.
  obtain ⟨w, b, hb, hwmem, hw1, hwinj, hslice⟩ :=
    h.exists_morseTrajectorySlice_eq_image_of_morseIndex_eq_one hf
      (mem_criticalPoints_iff_mfderiv_eq_zero.1 p.property) hp
  set bc : Fin 2 → criticalPoints 𝓘(ℝ, E) f :=
    fun i ↦ ⟨b i, mem_criticalPoints_iff_mfderiv_eq_zero.2 (hb i).1⟩
  have hpbc (i : Fin 2) : manifoldMorseIndex 𝓘(ℝ, E) f p =
      manifoldMorseIndex 𝓘(ℝ, E) f (bc i) + 1 := hp.trans (congrArg (· + 1) (hb i).2).symm
  have hcrit (i : Fin 2) : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f (w i) ≠ 0 :=
    hX.mfderiv_ne_zero_of_mem_unstableSet_inter_stableSet
      (fun he ↦ by have := (hb i).2; rw [← he] at this; omega) (hwmem i)
  -- The signs of the two trajectories, measured against the positive orientations at their ends.
  set s : Fin 2 → ℤ := fun i ↦ hX.trajectorySign (𝔬.chart p) (𝔬.chart (bc i)) (𝔬.orientation p)
    (Module.finBasisOfFinrankEq ℝ _ (𝔬.chart (bc i)).finrank_negativeWeight_fun).orientation
    (hpbc i) (w i)
  have hs : s 1 = -s 0 :=
    trajectorySign_eq_neg_of_notMem_orbit hf (𝔬.coord_mfderiv_chart p) (𝔬.orientation p) hp
      (hpbc 0) (hpbc 1) (hwmem 0).1 (hwmem 1).1 (hcrit 0) (hcrit 1) hw1
  -- The weighted coefficient at `q` is the sum of the signs of the trajectories ending at `q`.
  have hq (q : criticalPoints 𝓘(ℝ, E) f) :
      𝔬.augmentationSign q * hX.signedMorseBoundaryCoeff 𝔬 p q =
        ∑ i ∈ Finset.univ.filter (fun i ↦ bc i = q), s i := by
    by_cases hq0 : manifoldMorseIndex 𝓘(ℝ, E) f q = 0
    swap
    · rw [𝔬.augmentationSign_of_morseIndex_ne_zero hq0, zero_mul, eq_comm]
      exact Finset.sum_eq_zero fun i hi ↦ absurd ((Finset.mem_filter.1 hi).2 ▸ (hb i).2) hq0
    have hpq : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1 := by omega
    rw [𝔬.augmentationSign_of_morseIndex_eq_zero hq0,
      signedMorseBoundaryCoeff_of_morseIndex_eq_add_one hpq, signedTrajectoryCount_def,
      hslice q fun he ↦ by rw [he] at hpq; omega,
      finsum_mem_image hwinj.injOn, finsum_mem_eq_finite_toFinset_sum _ (toFinite _),
      Finset.mul_sum]
    refine Finset.sum_congr (by ext; simp [bc, Subtype.ext_iff]) fun i hi ↦ ?_
    obtain rfl : bc i = q := by simpa using hi
    exact signBasis_mul_trajectorySign _ _
  rw [Finset.sum_congr rfl fun q _ ↦ hq q, Finset.sum_fiberwise, Fin.sum_univ_two, hs,
    add_neg_cancel]

/-- **The augmentation vanishes on boundaries.** With coefficients in any ring `R`, the
augmentation of the integral Morse boundary of every chain is zero: `ε ∘ ∂ = 0`. -/
theorem signedMorseAugmentation_comp_signedMorseBoundary (R : Type*) [Ring R] :
    𝔬.signedMorseAugmentation R ∘ₗ hX.signedMorseBoundary 𝔬 hf R = 0 := by
  classical
  have := hf.finite_criticalPoints.fintype
  refine Finsupp.lhom_ext fun p a ↦ ?_
  have hsum := h.finsum_augmentationSign_mul_signedMorseBoundaryCoeff hf 𝔬 p
  rw [finsum_eq_sum_of_fintype] at hsum
  rw [LinearMap.comp_apply, LinearMap.zero_apply, MorseOrientation.signedMorseAugmentation_apply,
    Finsupp.sum_fintype _ _ (by simp)]
  simp only [signedMorseBoundary_single_apply, mul_assoc, ← Finset.mul_sum]
  have hR : ∑ q, (hX.signedMorseBoundaryCoeff 𝔬 p q : R) * (𝔬.augmentationSign q : R) = 0 := by
    rw [← Int.cast_zero, ← hsum]
    push_cast
    exact Finset.sum_congr rfl fun q _ ↦ Int.cast_comm _ _
  rw [hR, mul_zero]

/-- **The augmentation of a boundary is zero.** The applied form of `ε ∘ ∂ = 0`. -/
@[simp]
theorem signedMorseAugmentation_signedMorseBoundary {R : Type*} [Ring R]
    (c : criticalPoints 𝓘(ℝ, E) f →₀ R) :
    𝔬.signedMorseAugmentation R (hX.signedMorseBoundary 𝔬 hf R c) = 0 := by
  rw [← LinearMap.comp_apply, h.signedMorseAugmentation_comp_signedMorseBoundary hf 𝔬 R,
    LinearMap.zero_apply]

/-- **The integral boundary does not reach a unique critical point of index zero.** If `m` is the
only critical point of index `0`, then its coefficient in the integral Morse boundary of every
critical point vanishes: the two trajectories from a critical point of index `1` to `m` carry
opposite signs. -/
theorem signedMorseBoundaryCoeff_eq_zero_of_unique_index_zero {m : criticalPoints 𝓘(ℝ, E) f}
    (huniq : ∀ y, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y = 0 → manifoldMorseIndex 𝓘(ℝ, E) f y = 0 → y = m)
    (p : criticalPoints 𝓘(ℝ, E) f) : hX.signedMorseBoundaryCoeff 𝔬 p m = 0 := by
  -- Some critical point has index `0`, and it must be `m`.
  have : Nonempty M := ⟨m⟩
  have h0 := criticalCount_zero_ne_zero (I := 𝓘(ℝ, E)) (hf.contMDiff.of_le (by simp))
  rw [criticalCount_def] at h0
  obtain ⟨x, hxc, hx0⟩ := nonempty_of_encard_ne_zero h0
  have hm : manifoldMorseIndex 𝓘(ℝ, E) f m = 0 := by
    rwa [← huniq x (mem_criticalPoints_iff_mfderiv_eq_zero.1 hxc) hx0]
  have hsum := h.finsum_augmentationSign_mul_signedMorseBoundaryCoeff hf 𝔬 p
  rw [finsum_eq_single _ m fun q hqm ↦ by
    rw [𝔬.augmentationSign_of_morseIndex_ne_zero fun hq ↦ hqm (Subtype.ext
      (huniq q (mem_criticalPoints_iff_mfderiv_eq_zero.1 q.property) hq)), zero_mul]] at hsum
  rcases 𝔬.augmentationSign_eq_one_or_eq_neg_one hm with he | he <;> rw [he] at hsum <;> omega

/-- **A unique critical point of index zero is not hit by the integral boundary.** If `m` is the
only critical point of index `0`, then the coefficient of `m` in `∂ c` vanishes for every chain
`c`, with coefficients in any ring. -/
theorem signedMorseBoundary_apply_eq_zero_of_unique_index_zero {R : Type*} [Ring R]
    {m : criticalPoints 𝓘(ℝ, E) f}
    (huniq : ∀ y, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y = 0 → manifoldMorseIndex 𝓘(ℝ, E) f y = 0 → y = m)
    (c : criticalPoints 𝓘(ℝ, E) f →₀ R) : hX.signedMorseBoundary 𝔬 hf R c m = 0 := by
  simp [signedMorseBoundary_apply, h.signedMorseBoundaryCoeff_eq_zero_of_unique_index_zero hf 𝔬
    huniq]

end IsMorseSmale

end IsAdaptedPseudoGradient

end TauCeti

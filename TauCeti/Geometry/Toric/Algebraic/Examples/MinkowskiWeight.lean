/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Algebraic.Examples.ProjectiveLine
public import TauCeti.Geometry.Toric.Algebraic.Fan.MinkowskiWeight

/-!
# Minkowski weights of the projective-line fan

The projective-line fan has the two standard rays as its cones of codimension zero and the zero
cone as its only cone of codimension one. The lattice normals of the two rays along the zero cone
are `1` and `-1`, so the balancing condition at the zero cone reads `c(+) u(1) + c(-) u(-1) = 0`
for every character `u`: its relation matrix is `[1, -1]`. Hence the Minkowski weights of
codimension zero are exactly the weights taking the same value on the two rays, matching the
operational Chow group `A⁰(ℙ¹) = ℤ`.

## Main declarations

* `TauCeti.Toric.projectiveLinePositiveCone` and
  `TauCeti.Toric.projectiveLineNegativeCone`: the two rays as cones of codimension
  zero.
* `TauCeti.Toric.isLatticeNormal_bot_affineRayCone` and
  `TauCeti.Toric.isLatticeNormal_bot_negativeRayCone`: their lattice normals along the zero cone.
* `TauCeti.Toric.balancing_projectiveLineFan_apply`: the balancing functional at the zero cone is
  `c ↦ (c(+) - c(-)) u(1)`.
* `TauCeti.Toric.mem_minkowskiWeights_projectiveLineFan_zero`: a weight of codimension zero
  is balanced exactly when it takes the same value on the two rays.

## References

* W. Fulton and B. Sturmfels, *Intersection theory on toric varieties*, Topology 36 (1997), §2.
-/

public section

open Module

namespace TauCeti.Toric

private theorem finrank_span_affineRayCone :
    finrank ℝ (Submodule.span ℝ (affineRayCone : Set (Fin 1 → ℝ))) = 1 := by
  rw [affineRayCone_def, PointedCone.hull, Submodule.span_span_of_tower,
    finrank_span_singleton one_ne_zero]

private theorem finrank_span_negativeRayCone :
    finrank ℝ (Submodule.span ℝ (negativeRayCone : Set (Fin 1 → ℝ))) = 1 := by
  rw [negativeRayCone_def, PointedCone.hull, Submodule.span_span_of_tower,
    finrank_span_singleton (neg_ne_zero.2 one_ne_zero)]

private theorem finrank_span_bot :
    finrank ℝ (Submodule.span ℝ ((⊥ : PointedCone ℝ (Fin 1 → ℝ)) : Set (Fin 1 → ℝ))) =
      0 := by
  simp

/-- The positive ray, as a cone of codimension zero of the projective-line fan. -/
def projectiveLinePositiveCone : projectiveLineFan.ConeOfCodim 0 :=
  ⟨⟨affineRayCone, affineRayCone_mem_projectiveLineFan⟩, by
    simp [finrank_span_affineRayCone]⟩

/-- The negative ray, as a cone of codimension zero of the projective-line fan. -/
def projectiveLineNegativeCone : projectiveLineFan.ConeOfCodim 0 :=
  ⟨⟨negativeRayCone, negativeRayCone_mem_projectiveLineFan⟩, by
    simp [finrank_span_negativeRayCone]⟩

@[simp]
theorem coe_projectiveLinePositiveCone :
    projectiveLinePositiveCone.val.val = affineRayCone := (rfl)

@[simp]
theorem coe_projectiveLineNegativeCone :
    projectiveLineNegativeCone.val.val = negativeRayCone := (rfl)

/-- The two rays are the only cones of codimension zero of the projective-line fan. -/
theorem eq_projectiveLinePositiveCone_or_eq_projectiveLineNegativeCone
    (σ : projectiveLineFan.ConeOfCodim 0) :
    σ = projectiveLinePositiveCone ∨ σ = projectiveLineNegativeCone := by
  obtain ⟨⟨σ, hσ⟩, hdim⟩ := σ
  rcases (mem_projectiveLineFan_cones σ).1 hσ with rfl | rfl | rfl
  · simp only [finrank_span_bot, finrank_fin_fun] at hdim
    exact absurd hdim zero_ne_one
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- The zero cone is the only cone of codimension one of the projective-line fan. -/
theorem projectiveLineFan_coneOfCodim_one_eq_bot (τ : projectiveLineFan.ConeOfCodim 1) :
    τ.val.val = ⊥ := by
  obtain ⟨⟨τ, hτ⟩, hdim⟩ := τ
  rcases (mem_projectiveLineFan_cones τ).1 hτ with rfl | rfl | rfl
  · rfl
  · simp [finrank_span_affineRayCone] at hdim
  · simp [finrank_span_negativeRayCone] at hdim

/-- The lattice normal of the positive ray along the zero cone is `1`. -/
theorem isLatticeNormal_bot_affineRayCone :
    IsLatticeNormal ((Int.castAddHom ℝ).compLeft (Fin 1)) ⊥ affineRayCone 1 := by
  have hbot := coneSublattice_bot (isIntegralLattice_intCast 1)
  refine ⟨mem_coneSublattice.2 (Submodule.subset_span ?_), fun m _ ↦ ⟨m 0, ?_⟩, 1, ?_, 1,
    one_pos, ?_⟩
  · simp [intCast_finOne_one]
  · rw [hbot, AddSubgroup.mem_bot, sub_eq_zero]
    ext j
    simp [Subsingleton.elim j 0]
  · simp [intCast_finOne_one]
  · simp [hbot]

/-- The lattice normal of the negative ray along the zero cone is `-1`. -/
theorem isLatticeNormal_bot_negativeRayCone :
    IsLatticeNormal ((Int.castAddHom ℝ).compLeft (Fin 1)) ⊥ negativeRayCone (-1) := by
  have hbot := coneSublattice_bot (isIntegralLattice_intCast 1)
  refine ⟨mem_coneSublattice.2 (Submodule.subset_span ?_), fun m _ ↦ ⟨-m 0, ?_⟩, -1, ?_, 1,
    one_pos, ?_⟩
  · simp [intCast_finOne_one]
  · rw [hbot, AddSubgroup.mem_bot, sub_eq_zero]
    ext j
    simp [Subsingleton.elim j 0]
  · simp [intCast_finOne_one]
  · simp [hbot]

/-- The two rays are distinct cones of codimension zero. -/
theorem projectiveLinePositiveCone_ne_projectiveLineNegativeCone :
    projectiveLinePositiveCone ≠ projectiveLineNegativeCone := by
  intro h
  have h1 := congrArg (fun σ : projectiveLineFan.ConeOfCodim 0 ↦ σ.val.val) h
  have h2 : (-1 : Fin 1 → ℝ) ∉ affineRayCone := by simp
  simp only [coe_projectiveLinePositiveCone,
    coe_projectiveLineNegativeCone] at h1
  exact h2 (h1 ▸ negativeRayCone_def ▸ PointedCone.subset_hull rfl)

/-- The balancing functional of the projective-line fan at its cone of codimension one is
`c ↦ (c(+) - c(-)) u(1)`: its relation matrix is `[1, -1]`. -/
theorem balancing_projectiveLineFan_apply (τ : projectiveLineFan.ConeOfCodim 1)
    (u : (Fin 1 → ℤ) →+ ℤ) (c : projectiveLineFan.ConeOfCodim 0 → ℤ) :
    projectiveLineFan.balancing 0 τ.val.val u c =
      (c projectiveLinePositiveCone - c projectiveLineNegativeCone) *
        u 1 := by
  classical
  let _ := Fintype.ofFinite (projectiveLineFan.ConeOfCodim 0)
  have hpn := projectiveLinePositiveCone_ne_projectiveLineNegativeCone
  have hτ := projectiveLineFan_coneOfCodim_one_eq_bot τ
  let n : projectiveLineFan.ConeOfCodim 0 → Fin 1 → ℤ := fun σ ↦
    if σ = projectiveLinePositiveCone then 1 else -1
  have hn (σ : projectiveLineFan.ConeOfCodim 0) (_ : τ.val.val ≤ σ.val.val) :
      IsLatticeNormal ((Int.castAddHom ℝ).compLeft (Fin 1)) τ.val.val σ.val.val (n σ) := by
    rw [hτ]
    rcases eq_projectiveLinePositiveCone_or_eq_projectiveLineNegativeCone σ with rfl | rfl
    · simpa [n] using isLatticeNormal_bot_affineRayCone
    · simpa [n, hpn.symm] using isLatticeNormal_bot_negativeRayCone
  have hu : coneSublattice ((Int.castAddHom ℝ).compLeft (Fin 1)) τ.val.val ≤ u.ker := by
    simp [hτ, coneSublattice_bot (isIntegralLattice_intCast 1)]
  rw [projectiveLineFan.balancing_apply_of_isLatticeNormal τ hu n hn, hτ,
    Finset.filter_true_of_mem fun σ _ ↦ bot_le, Fintype.sum_eq_add _ _ hpn fun σ hσ ↦ ?_]
  · simp only [n, ite_true, hpn.symm, ite_false, map_neg]
    ring
  · rcases eq_projectiveLinePositiveCone_or_eq_projectiveLineNegativeCone σ with h | h
    · exact absurd h hσ.1
    · exact absurd h hσ.2

/-- A weight on the two rays of the projective-line fan is a Minkowski weight of codimension zero
exactly when it takes the same value on both rays. -/
theorem mem_minkowskiWeights_projectiveLineFan_zero
    {c : projectiveLineFan.ConeOfCodim 0 → ℤ} :
    c ∈ projectiveLineFan.minkowskiWeights 0 ↔
      c projectiveLinePositiveCone = c projectiveLineNegativeCone := by
  rw [Fan.mem_minkowskiWeights]
  refine ⟨fun h ↦ ?_, fun h τ u _ ↦ by
    rw [balancing_projectiveLineFan_apply, h, sub_self, zero_mul]⟩
  -- Test the balancing condition at the zero cone against the coordinate character.
  let τ : projectiveLineFan.ConeOfCodim 1 :=
    ⟨⟨⊥, projectiveLineFan.bot_mem affineRayCone_mem_projectiveLineFan⟩, by simp⟩
  have := h τ (Pi.evalAddMonoidHom (fun _ ↦ ℤ) 0)
    (by simp [τ, coneSublattice_bot (isIntegralLattice_intCast 1)])
  rw [balancing_projectiveLineFan_apply] at this
  simpa [sub_eq_zero] using this

end TauCeti.Toric

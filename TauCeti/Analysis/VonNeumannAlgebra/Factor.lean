/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.VonNeumannAlgebra.Lattice

/-!
# Factors of von Neumann algebras

Factors—von Neumann algebras with trivial center—are the indecomposable building blocks of von
Neumann algebra classification and the target of the Murray–von Neumann ICC factor theorem
(`TauCeti.isFactor_groupVonNeumannAlgebra_iff`). `VonNeumannAlgebra.IsFactor` holds when
`(1 : H →L[ℂ] H) ≠ 0` and every central element `x ∈ M ∩ M'` is a scalar multiple of `1`,
equivalently `Nontrivial H` and `M ⊓ M.commutant = ⊥`
(`VonNeumannAlgebra.isFactor_iff_inf_commutant_eq_bot`). Factorhood is preserved under commutants
(`VonNeumannAlgebra.isFactor_commutant_iff`) and holds for `⊤` and `⊥` on any nontrivial Hilbert
space. When `M ⊓ M.commutant = ⊥`, a product `a * b` with `a ∈ M` and `b ∈ M.commutant` vanishes
only when `a = 0` or `b = 0`
(`VonNeumannAlgebra.eq_zero_or_eq_zero_of_mul_eq_zero_of_mem_commutant`), since the projection onto
the closed `M`-orbit of `range a` belongs to `M ⊓ M.commutant = ⊥`.

## References

* J. Peterson, *Notes on von Neumann Algebras* (2013), Proposition 2.1.3.
* C. Anantharaman and S. Popa, *An Introduction to II₁ Factors*, §2.1.
-/

public section

namespace VonNeumannAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A concrete von Neumann algebra `M` on `H` is a **factor** when `(1 : H →L[ℂ] H) ≠ 0` and every
element of the center `M ∩ M'` is a scalar multiple of the identity. -/
def IsFactor (M : VonNeumannAlgebra H) : Prop :=
  (1 : H →L[ℂ] H) ≠ 0 ∧
    ∀ x : H →L[ℂ] H, x ∈ M → x ∈ M.commutant → ∃ c : ℂ, x = c • (1 : H →L[ℂ] H)

theorem isFactor_def (M : VonNeumannAlgebra H) :
    M.IsFactor ↔
      (1 : H →L[ℂ] H) ≠ 0 ∧
        ∀ x : H →L[ℂ] H, x ∈ M → x ∈ M.commutant → ∃ c : ℂ, x = c • (1 : H →L[ℂ] H) :=
  Iff.rfl

/-- In a factor on `H`, the identity operator on `H` is nonzero. -/
theorem IsFactor.one_ne_zero {M : VonNeumannAlgebra H} (hM : M.IsFactor) :
    (1 : H →L[ℂ] H) ≠ 0 :=
  hM.1

/-- The underlying Hilbert space of a factor is nontrivial. -/
theorem IsFactor.nontrivial {M : VonNeumannAlgebra H} (hM : M.IsFactor) : Nontrivial H := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  exact hM.1 (Subsingleton.elim _ _)

/-- Every element in both a factor `M` and its commutant `M'` is a scalar multiple of `1`. -/
theorem IsFactor.exists_eq_smul_one {M : VonNeumannAlgebra H} (hM : M.IsFactor) {x : H →L[ℂ] H}
    (hx : x ∈ M) (hx' : x ∈ M.commutant) : ∃ c : ℂ, x = c • (1 : H →L[ℂ] H) :=
  hM.2 x hx hx'

/-- No von Neumann algebra on a subsingleton Hilbert space is a factor. -/
@[simp]
theorem not_isFactor_of_subsingleton [Subsingleton H] (M : VonNeumannAlgebra H) : ¬ M.IsFactor :=
  fun hM => hM.1 (Subsingleton.elim _ _)

/-- `M` is a factor if and only if `H` is nontrivial and the center `M ⊓ M'` is the scalar algebra
`⊥`. -/
theorem isFactor_iff_inf_commutant_eq_bot (M : VonNeumannAlgebra H) :
    M.IsFactor ↔ Nontrivial H ∧ M ⊓ M.commutant = ⊥ := by
  refine ⟨fun hM => ⟨hM.nontrivial, le_antisymm (fun x hx => ?_) bot_le⟩, fun ⟨_, hbot⟩ => ?_⟩
  · obtain ⟨c, rfl⟩ := hM.2 x (mem_inf.1 hx).1 (mem_inf.1 hx).2
    exact mem_bot.2 ⟨c, Algebra.algebraMap_eq_smul_one c⟩
  · refine ⟨one_ne_zero, fun x hx hx' => ?_⟩
    obtain ⟨c, rfl⟩ := mem_bot.1 (hbot ▸ mem_inf.2 ⟨hx, hx'⟩)
    exact ⟨c, (Algebra.algebraMap_eq_smul_one c).symm⟩

/-- The commutant of a factor is a factor. -/
theorem IsFactor.commutant {M : VonNeumannAlgebra H} (hM : M.IsFactor) : M.commutant.IsFactor :=
  ⟨hM.1, fun x hx hx' => hM.2 x (by simpa using hx') hx⟩

/-- A von Neumann algebra's commutant is a factor if and only if the algebra itself is a factor. -/
@[simp]
theorem isFactor_commutant_iff (M : VonNeumannAlgebra H) : M.commutant.IsFactor ↔ M.IsFactor :=
  ⟨fun h => by simpa using h.commutant, IsFactor.commutant⟩

/-- On a nontrivial Hilbert space, `⊤ = B(H)` is a factor. -/
@[simp]
theorem isFactor_top [Nontrivial H] : (⊤ : VonNeumannAlgebra H).IsFactor := by
  rw [isFactor_iff_inf_commutant_eq_bot, commutant_top, top_inf_eq]
  exact ⟨inferInstance, rfl⟩

/-- On a nontrivial Hilbert space, the scalar algebra `⊥ = ℂ • 1` is a factor. -/
@[simp]
theorem isFactor_bot [Nontrivial H] : (⊥ : VonNeumannAlgebra H).IsFactor := by
  rw [← commutant_top, isFactor_commutant_iff]; exact isFactor_top

/-! ### Nonzero products between `M` and `M.commutant` -/

/-- **Nonzero product theorem.** If `M` has scalar center (`M ⊓ M.commutant = ⊥`), `a ∈ M`, and
`b ∈ M.commutant` satisfy `a * b = 0`, then `a = 0` or `b = 0`. -/
theorem eq_zero_or_eq_zero_of_mul_eq_zero_of_mem_commutant {M : VonNeumannAlgebra H}
    (hM : M ⊓ M.commutant = ⊥) {a b : H →L[ℂ] H} (ha : a ∈ M) (hb : b ∈ M.commutant)
    (hab : a * b = 0) :
    a = 0 ∨ b = 0 := by
  -- The closed span `L` of `{x v | x ∈ M, v ∈ range a}` reduces both `M` and `M.commutant`.
  set L₀ : Submodule ℂ H := Submodule.span ℂ {w : H | ∃ x ∈ M, ∃ v ∈ Set.range a, x v = w}
  set L : Submodule ℂ H := L₀.topologicalClosure
  have hrange : ∀ w ∈ M.commutant, Set.MapsTo w (Set.range a) (Set.range a) := by
    rintro w hw _ ⟨ξ, rfl⟩
    exact ⟨w ξ, by
      simpa [mul_apply_eq_comp] using DFunLike.congr_fun (mem_commutant_iff.mp hw a ha) ξ⟩
  have hp_bot : L.starProjection ∈ (⊥ : VonNeumannAlgebra H) :=
    hM ▸ mem_inf.mpr
      ⟨M.starProjection_topologicalClosure_span_mem hrange,
        M.starProjection_topologicalClosure_span_mem_commutant (Set.range a)⟩
  -- Since `L.starProjection` is an idempotent in `⊥`, it is `0` or `1`.
  rcases eq_zero_or_eq_one_of_isIdempotentElem_of_mem_bot L.isIdempotentElem_starProjection
      hp_bot with hp0 | hp1
  · left
    ext ξ
    have hξ : a ξ ∈ L := Submodule.le_topologicalClosure _
      (Submodule.subset_span ⟨1, M.one_mem, a ξ, ⟨ξ, rfl⟩, one_apply_eq_self _⟩)
    rw [← L.starProjection_eq_self_iff.mpr hξ, hp0, zero_apply, zero_apply]
  · right
    have hker : L ≤ LinearMap.ker b.toLinearMap := by
      refine Submodule.topologicalClosure_minimal _ (Submodule.span_le.mpr ?_)
        (isClosed_singleton.preimage b.continuous)
      rintro _ ⟨x, hx, _, ⟨ξ, rfl⟩, rfl⟩
      have hab' : b * a = 0 := (mem_commutant_iff.mp hb a ha).symm.trans hab
      simpa [SetLike.mem_coe, LinearMap.mem_ker, mul_apply_eq_comp, mul_assoc, hab'] using
        DFunLike.congr_fun (congrArg (· * a) (mem_commutant_iff.mp hb x hx).symm) ξ
    ext v
    exact hker (L.starProjection_eq_self_iff.mp (by rw [hp1, one_apply_eq_self]))

/-- In a von Neumann algebra with scalar center, a product `a * b` with `a ∈ M` and
`b ∈ M.commutant` vanishes if and only if `a = 0` or `b = 0`. -/
theorem mul_eq_zero_iff_of_mem_commutant {M : VonNeumannAlgebra H} (hM : M ⊓ M.commutant = ⊥)
    {a b : H →L[ℂ] H} (ha : a ∈ M) (hb : b ∈ M.commutant) :
    a * b = 0 ↔ a = 0 ∨ b = 0 :=
  ⟨eq_zero_or_eq_zero_of_mul_eq_zero_of_mem_commutant hM ha hb, by rintro (rfl | rfl) <;> simp⟩

/-- In a von Neumann algebra with scalar center, the product of nonzero `a ∈ M` and
`b ∈ M.commutant` is nonzero. -/
theorem mul_ne_zero_of_mem_commutant {M : VonNeumannAlgebra H} (hM : M ⊓ M.commutant = ⊥)
    {a b : H →L[ℂ] H} (ha : a ∈ M) (hb : b ∈ M.commutant) (ha0 : a ≠ 0) (hb0 : b ≠ 0) :
    a * b ≠ 0 :=
  fun hab => (eq_zero_or_eq_zero_of_mul_eq_zero_of_mem_commutant hM ha hb hab).elim ha0 hb0

end VonNeumannAlgebra

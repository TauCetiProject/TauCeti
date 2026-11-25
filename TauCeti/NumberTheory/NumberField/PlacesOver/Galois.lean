/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.AbsoluteValue.Action
public import TauCeti.NumberTheory.NumberField.PlacesOver.Basic
public import TauCeti.NumberTheory.NumberField.PlacesOver.Relative

import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Mathlib.NumberTheory.RamificationInertia.Galois
import TauCeti.NumberTheory.NumberField.AutomorphismAction
import TauCeti.NumberTheory.NumberField.InfinitePlace.Action

/-!
# Conjugate absolute values over a place

Let `F / K` be a Galois extension and `v` a place of `K`. The Galois group `F ≃ₐ[K] F` acts on the
absolute values of `F` by `σ • w = w ∘ σ⁻¹` (`AbsoluteValue.instMulActionAlgEquiv`), preserving
those that lie over `v`. This file proves that it permutes them transitively:

* Above an infinite place `v` (for any Galois field extension `F / K`), any two absolute values of
  `F` lying over `v` are infinite places of `F` with the same restriction to `K`, hence conjugate
  under `F ≃ₐ[K] F` (`NumberField.exists_smul_eq_of_liesOver_infinitePlace`,
  `NumberField.setOf_liesOver_infinitePlace_eq_orbit`).
* Above a finite place `v` of a number field `K`, any two absolute values of `F` lying over `v`
  are conjugate (`NumberField.exists_smul_eq_of_liesOver_finitePlace`,
  `NumberField.setOf_liesOver_finitePlace_eq_orbit`), even though they are in general real powers
  of finite places of `F` rather than finite places themselves.
* Together these give `NumberField.exists_smul_eq_of_liesOver` and
  `NumberField.setOf_liesOver_eq_orbit` for any base place satisfying
  `IsInfinitePlace v ∨ IsFinitePlace v`.
* Given an absolute value `w' v` of `F` over each place `v` of `K`, `NumberField.conjPair w' u`
  chooses, as a function of an absolute value `u` of `F` alone, a place `v` of `K` below it and an
  automorphism of `F / K` carrying `w' v` to the absolute value that `u` induces over `v`. When
  `w' v` lies over `v`, at an infinite place `W` of `F` above `v` this place is `v` and the
  automorphism carries `w' v` to `W` itself (`NumberField.conjPair_infinitePlace`); at a finite
  place `W` above `v` the place is again `v` but the target is the local-degree root
  `W.relativeAbsValue K`, which in general differs from `W` (`NumberField.conjPair_finitePlace`).

## Implementation notes

At a finite place `v = FinitePlace.mk 𝔭`, an absolute value `w` lying over `v` is determined by
its prime `{y ∈ 𝓞 F | w y < 1}` (`NumberField.eq_of_liesOver_of_forall_apply_lt_one_iff`), and the
prime of `σ • w` is the image under `σ` of the prime of `w`, reducing transitivity to
`Ideal.exists_smul_eq_of_isGaloisGroup`. The finite-place transitivity statement along this route
follows Ralf Stephan's `rwst/Subspace-Theorems` at `09835cb23557ae5ae0cf55a9c4ab9055f5d60338`,
file `DiophantineApproximation/ConjugatePlaces.lean` (Apache 2.0). At an infinite place,
`NumberField.existsUnique_infinitePlace_of_liesOver` reduces directly to Mathlib's
`NumberField.InfinitePlace.exists_smul_eq_of_comap_eq` via `NumberField.InfinitePlace.coe_smul`.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press, 2006,
  §1.3, Corollaries 1.3.2 and 1.3.5.
-/

public section

open AbsoluteValue IsDedekindDomain Pointwise

namespace NumberField

section Field

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [IsGalois K F]

/-- **Conjugate absolute values over an infinite place.** Let `F / K` be a Galois field extension
and `v` an infinite place of `K`. Any two absolute values of `F` lying over `v` are conjugate
under `F ≃ₐ[K] F`. -/
theorem exists_smul_eq_of_liesOver_infinitePlace (v : InfinitePlace K)
    (w₁ w₂ : AbsoluteValue F ℝ) [w₁.LiesOver v.val] [w₂.LiesOver v.val] :
    ∃ σ : F ≃ₐ[K] F, σ • w₁ = w₂ := by
  obtain ⟨u₁, _, rfl⟩ := (existsUnique_infinitePlace_of_liesOver v w₁).exists
  obtain ⟨u₂, _, rfl⟩ := (existsUnique_infinitePlace_of_liesOver v w₂).exists
  obtain ⟨σ, rfl⟩ := InfinitePlace.exists_smul_eq_of_comap_eq
    ((InfinitePlace.LiesOver.comap_eq u₁ v).trans (InfinitePlace.LiesOver.comap_eq u₂ v).symm)
  exact ⟨σ, (InfinitePlace.coe_smul σ u₁).symm⟩

/-- Let `F / K` be a Galois field extension and `v` an infinite place of `K`. The absolute values
of `F` lying over `v` form a single orbit of `F ≃ₐ[K] F`. -/
theorem setOf_liesOver_infinitePlace_eq_orbit (v : InfinitePlace K)
    (w : AbsoluteValue F ℝ) [w.LiesOver v.val] :
    {w' : AbsoluteValue F ℝ | w'.LiesOver v.val} = MulAction.orbit (F ≃ₐ[K] F) w := by
  ext w'
  simp only [Set.mem_ofPred_eq, MulAction.mem_orbit_iff]
  refine ⟨fun _ ↦ exists_smul_eq_of_liesOver_infinitePlace v w w', ?_⟩
  rintro ⟨σ, rfl⟩
  infer_instance

end Field

section NumberField

variable {K F : Type*} [Field K] [Field F] [NumberField K] [NumberField F] [Algebra K F]

/-- **Conjugate absolute values over a finite place.** Let `F / K` be a Galois extension of number
fields and `v` a finite place of `K`. Any two absolute values of `F` lying over `v` are conjugate
under `F ≃ₐ[K] F`. -/
theorem exists_smul_eq_of_liesOver_finitePlace [IsGalois K F] (v : FinitePlace K)
    (w₁ w₂ : AbsoluteValue F ℝ) [w₁.LiesOver v.val] [w₂.LiesOver v.val] :
    ∃ σ : F ≃ₐ[K] F, σ • w₁ = w₂ := by
  obtain ⟨𝔭, rfl⟩ : ∃ 𝔭, FinitePlace.mk 𝔭 = v := ⟨_, v.mk_maximalIdeal⟩
  obtain ⟨𝔓₁, h𝔓₁, hw₁⟩ := exists_liesOver_forall_mem_iff_apply_lt_one (𝔭 := 𝔭) (w := w₁)
  obtain ⟨𝔓₂, h𝔓₂, hw₂⟩ := exists_liesOver_forall_mem_iff_apply_lt_one (𝔭 := 𝔭) (w := w₂)
  obtain ⟨σ, hσ⟩ :=
    Ideal.exists_smul_eq_of_isGaloisGroup 𝔭.asIdeal 𝔓₁.asIdeal 𝔓₂.asIdeal (F ≃ₐ[K] F)
  refine ⟨σ, eq_of_liesOver_of_forall_apply_lt_one_iff (𝔭 := 𝔭) fun y ↦ ?_⟩
  -- Transport the prime of `w₁` to the prime of `w₂` along `σ`.
  rw [← hw₂, ← hσ, Ideal.mem_pointwise_smul_iff_inv_smul_mem, hw₁]
  -- The action of `σ⁻¹` on `𝓞 F` is the restriction of its action on `F`.
  simp only [AbsoluteValue.smul_apply, AlgEquiv.aut_inv, algebraMap_smul_eq_apply]

/-- Let `F / K` be a Galois extension of number fields and `v` a finite place of `K`. The absolute
values of `F` lying over `v` form a single orbit of `F ≃ₐ[K] F`. -/
theorem setOf_liesOver_finitePlace_eq_orbit [IsGalois K F] (v : FinitePlace K)
    (w : AbsoluteValue F ℝ) [w.LiesOver v.val] :
    {w' : AbsoluteValue F ℝ | w'.LiesOver v.val} = MulAction.orbit (F ≃ₐ[K] F) w := by
  ext w'
  simp only [Set.mem_ofPred_eq, MulAction.mem_orbit_iff]
  refine ⟨fun _ ↦ exists_smul_eq_of_liesOver_finitePlace v w w', ?_⟩
  rintro ⟨σ, rfl⟩
  infer_instance

/-- **Conjugate absolute values over a place.** In a Galois extension `F / K` of number fields, any
two absolute values of `F` lying over the same infinite or finite place of `K` are conjugate under
`F ≃ₐ[K] F`. -/
theorem exists_smul_eq_of_liesOver [IsGalois K F] {v : AbsoluteValue K ℝ}
    (hv : IsInfinitePlace v ∨ IsFinitePlace v)
    (w₁ w₂ : AbsoluteValue F ℝ) [w₁.LiesOver v] [w₂.LiesOver v] :
    ∃ σ : F ≃ₐ[K] F, σ • w₁ = w₂ := by
  rcases hv with hinf | hfin
  · obtain ⟨v', rfl⟩ := (isInfinitePlace_iff v).mp hinf
    exact exists_smul_eq_of_liesOver_infinitePlace v' w₁ w₂
  · obtain ⟨v', rfl⟩ := (isFinitePlace_iff v).mp hfin
    exact exists_smul_eq_of_liesOver_finitePlace v' w₁ w₂

/-- In a Galois extension `F / K` of number fields, the absolute values of `F` lying over a given
infinite or finite place of `K` form a single orbit of `F ≃ₐ[K] F`. -/
theorem setOf_liesOver_eq_orbit [IsGalois K F] {v : AbsoluteValue K ℝ}
    (hv : IsInfinitePlace v ∨ IsFinitePlace v)
    (w : AbsoluteValue F ℝ) [w.LiesOver v] :
    {w' : AbsoluteValue F ℝ | w'.LiesOver v} = MulAction.orbit (F ≃ₐ[K] F) w := by
  ext w'
  simp only [Set.mem_ofPred_eq, MulAction.mem_orbit_iff]
  refine ⟨fun _ ↦ exists_smul_eq_of_liesOver hv w w', ?_⟩
  rintro ⟨σ, rfl⟩
  infer_instance

/-! ### Conjugating automorphisms chosen place by place -/

section conjPair

variable [IsGalois K F]

open Classical in
/-- For an absolute value `u` of `F`, a place `v` of `K` below it together with an automorphism
`σ` of `F / K` carrying `w' v` to the absolute value that `u` induces over `v`: `u` itself when
`u` is an infinite place of `F`, and the local-degree root of `u` when `u` is a finite place.
When `u` is a place of `F` above a place `v` at which `w' v` lies over `v`, the pair has first
component `v` (`NumberField.conjPair_infinitePlace`, `NumberField.conjPair_finitePlace`); when no
such pair exists, `(u.under K, 1)` is returned. -/
noncomputable def conjPair (w' : AbsoluteValue K ℝ → AbsoluteValue F ℝ) (u : AbsoluteValue F ℝ) :
    AbsoluteValue K ℝ × (F ≃ₐ[K] F) :=
  if h : ∃ p : AbsoluteValue K ℝ × (F ≃ₐ[K] F),
      (∃ (W : InfinitePlace F) (v : InfinitePlace K), W.val = u ∧ v.val = p.1 ∧ W.LiesOver v ∧
        p.2 • w' v.val = W.val) ∨
      (∃ (W : FinitePlace F) (v : FinitePlace K), W.val = u ∧ v.val = p.1 ∧ W.LiesOver v ∧
        p.2 • w' v.val = W.relativeAbsValue K)
  then h.choose else (u.under K, 1)

variable {w' : AbsoluteValue K ℝ → AbsoluteValue F ℝ}

/-- The defining property of `conjPair` at an absolute value for which some pair exists. -/
private theorem conjPair_spec {u : AbsoluteValue F ℝ}
    (h : ∃ p : AbsoluteValue K ℝ × (F ≃ₐ[K] F),
      (∃ (W : InfinitePlace F) (v : InfinitePlace K), W.val = u ∧ v.val = p.1 ∧ W.LiesOver v ∧
        p.2 • w' v.val = W.val) ∨
      (∃ (W : FinitePlace F) (v : FinitePlace K), W.val = u ∧ v.val = p.1 ∧ W.LiesOver v ∧
        p.2 • w' v.val = W.relativeAbsValue K)) :
    (∃ (W : InfinitePlace F) (v : InfinitePlace K), W.val = u ∧ v.val = (conjPair w' u).1 ∧
        W.LiesOver v ∧ (conjPair w' u).2 • w' v.val = W.val) ∨
      (∃ (W : FinitePlace F) (v : FinitePlace K), W.val = u ∧ v.val = (conjPair w' u).1 ∧
        W.LiesOver v ∧ (conjPair w' u).2 • w' v.val = W.relativeAbsValue K) := by
  unfold conjPair
  split_ifs
  exact h.choose_spec

/-- At an infinite place `W` of `F` above `v`, with `w' v` lying over `v`, the place of `K` chosen
by `conjPair` is `v`, and its automorphism carries `w' v` to `W`. -/
theorem conjPair_infinitePlace (W : InfinitePlace F) (v : InfinitePlace K) [W.LiesOver v]
    (hw : (w' v.val).LiesOver v.val) :
    (conjPair w' W.val).1 = v.val ∧ (conjPair w' W.val).2 • w' v.val = W.val := by
  obtain ⟨σ, hσ⟩ := exists_smul_eq_of_liesOver_infinitePlace v (w' v.val) W.val
  rcases conjPair_spec (w' := w') ⟨(v.val, σ), .inl ⟨W, v, rfl, rfl, inferInstance, hσ⟩⟩ with
    ⟨W₀, v₀, hW, hv, hWv, hσ₀⟩ | ⟨W₀, v₀, hW, -, -, -⟩
  · obtain rfl : W₀ = W := Subtype.ext hW
    obtain rfl : v₀ = v :=
      (InfinitePlace.LiesOver.comap_eq W₀ v₀).symm.trans (InfinitePlace.LiesOver.comap_eq W₀ v)
    exact ⟨hv.symm, hσ₀⟩
  · exact absurd hW (FinitePlace.val_ne_infinitePlace_val W₀ W)

/-- At a finite place `W` of `F` above `v`, with `w' v` lying over `v`, the place of `K` chosen by
`conjPair` is `v`, and its automorphism carries `w' v` to the local-degree root of `W`. -/
theorem conjPair_finitePlace (W : FinitePlace F) (v : FinitePlace K) [W.LiesOver v]
    (hw : (w' v.val).LiesOver v.val) :
    (conjPair w' W.val).1 = v.val ∧ (conjPair w' W.val).2 • w' v.val = W.relativeAbsValue K := by
  obtain ⟨σ, hσ⟩ := exists_smul_eq_of_liesOver_finitePlace v (w' v.val) (W.relativeAbsValue K)
  rcases conjPair_spec (w' := w') ⟨(v.val, σ), .inr ⟨W, v, rfl, rfl, inferInstance, hσ⟩⟩ with
    ⟨W₀, v₀, hW, -, -, -⟩ | ⟨W₀, v₀, hW, hv, hWv, hσ₀⟩
  · exact absurd hW.symm (FinitePlace.val_ne_infinitePlace_val W W₀)
  · obtain rfl : W₀ = W := Subtype.ext hW
    obtain rfl : v₀ = v := FinitePlace.eq_of_liesOver (w := W₀)
    exact ⟨hv.symm, hσ₀⟩

end conjPair

end NumberField

end NumberField

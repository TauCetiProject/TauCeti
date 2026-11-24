/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.FullFockSpace.Wick
public import TauCeti.Probability.FreeProbability.Circular
public import TauCeti.Probability.FreeProbability.StarIndependence
public import TauCeti.Probability.FreeProbability.WeakClosure

/-!
# Free probability on full Fock space

Combining the Fock-space vacuum Wick formula
(`TauCeti.FullFockSpace.vacuumState_prod_ofFn_creation_add_annihilation`) with the algebraic Wick
characterization of semicircular systems (`TauCeti.isSemicircularSystem_iff_apply_prod_ofFn`)
identifies the joint free cumulants of left creation and left annihilation operators on
`FullFockSpace 𝕜 H` under `(vacuumState 𝕜 H).toLinearMap`:

* For any families `f, g : ι → H`, the operators `creation 𝕜 (f i) + annihilation 𝕜 (g i)` form an
  algebraic semicircular system with covariance `Matrix.of fun i j => ⟪g i, f j⟫_𝕜`. Consequently,
  along any nonempty finite ordered index set `s`, all free cumulants of order `#s ≠ 2` vanish and
  `κ₂(ℓ(f i) + ℓ(g i)*, ℓ(f j) + ℓ(g j)*) = ⟪g i, f j⟫_𝕜`.
* Specializing to `g = f`, the self-adjoint field operators `field 𝕜 (f i)` form a semicircular
  system with Gram covariance `⟪f i, f j⟫_𝕜`, each `field 𝕜 h` is semicircular of variance
  `‖h‖ ^ 2`, and `field 𝕜 ∘ f` is freely independent if and only if the vectors `f i` are pairwise
  orthogonal.
* Over `ℂ`, for orthogonal unit vectors `e₁, e₂ : H`, both Voiculescu's operator
  `creation ℂ e₁ + annihilation ℂ e₂` and `(√2)⁻¹ • (field ℂ e₁ + I • field ℂ e₂)` are standard
  circular elements.
* For any family of pairwise orthogonal subsets `S : ι → Set H`, the generated unital
  `⋆`-subalgebras `StarAlgebra.adjoin 𝕜 (creation 𝕜 '' S i)`—and hence their norm closures, weak
  operator closures, and generated field subalgebras—are freely independent for the vacuum
  functional. In particular, `creation 𝕜 ∘ v` is `⋆`-freely independent if and only if the vectors
  `v i` are pairwise orthogonal.

No completeness assumption on `H` is needed anywhere in this file.

## Main results

* `TauCeti.FullFockSpace.isSemicircularSystem_creation_add_annihilation` and
  `TauCeti.FullFockSpace.freeCumulant_vacuumState_creation_add_annihilation`: semicircular-system
  structure and joint free cumulants of `creation 𝕜 (f i) + annihilation 𝕜 (g i)`.
* `TauCeti.FullFockSpace.isSemicircularSystem_field`, `TauCeti.FullFockSpace.isSemicircular_field`,
  and `TauCeti.FullFockSpace.isFreelyIndependentElements_field_iff`: semicircular systems of field
  operators and equivalence of freeness with orthogonality.
* `TauCeti.FullFockSpace.isCircular_creation_add_annihilation` and
  `TauCeti.FullFockSpace.isCircular_field_add_I_smul_field`: Fock-space circular operators.
* `TauCeti.FullFockSpace.isFreelyIndependent_starAlgebra_adjoin_creation`,
  `TauCeti.FullFockSpace.isFreelyIndependent_topologicalClosure_starAlgebra_adjoin_creation`,
  `TauCeti.FullFockSpace.isFreelyIndependent_weakOperatorClosure_starAlgebra_adjoin_creation`, and
  `TauCeti.FullFockSpace.isStarFreelyIndependentElements_creation_iff`: `⋆`-freeness from
  orthogonality on full Fock space.

## References

* D. V. Voiculescu, K. J. Dykema, A. Nica, *Free Random Variables*, CRM Monograph Series, Vol. 1,
  American Mathematical Society, 1992, §2.6.
* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, London Mathematical
  Society Lecture Note Series, Vol. 335, Cambridge University Press, 2006, Lectures 7, 8, and 15.
-/

public section

noncomputable section

open Finset Matrix
open scoped ComplexOrder InnerProductSpace Pointwise

namespace TauCeti

universe u v

namespace FullFockSpace

section Cumulants

variable {𝕜 : Type u} {H : Type v} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  {ι α : Type*} [LinearOrder α]

/-- For any two families `f, g : ι → H`, the operators `creation 𝕜 (f i) + annihilation 𝕜 (g i)`
form an algebraic semicircular system for `(vacuumState 𝕜 H).toLinearMap` with covariance
`Matrix.of fun i j => ⟪g i, f j⟫_𝕜`. -/
theorem isSemicircularSystem_creation_add_annihilation (f g : ι → H) :
    IsSemicircularSystem (vacuumState 𝕜 H).toLinearMap
      (fun i => creation 𝕜 (f i) + annihilation 𝕜 (g i))
      (Matrix.of fun i j => ⟪g i, f j⟫_𝕜) :=
  isSemicircularSystem_iff_apply_prod_ofFn.2 fun w =>
    vacuumState_prod_ofFn_creation_add_annihilation (f ∘ w) (g ∘ w)

/-- Joint free cumulant of `creation 𝕜 (f i) + annihilation 𝕜 (g i)` along a nonempty finite
ordered set `s`: only order-two cumulants can be nonzero, given by `⟪g (min s), f (max s)⟫_𝕜`. -/
theorem freeCumulant_vacuumState_creation_add_annihilation {s : Finset α} (hs : s.Nonempty)
    (f g : α → H) :
    freeCumulant (vacuumState 𝕜 H).toLinearMap
        (fun i => creation 𝕜 (f i) + annihilation 𝕜 (g i)) s =
      if #s = 2 then ⟪g (s.min' hs), f (s.max' hs)⟫_𝕜 else 0 := by
  simpa using (isSemicircularSystem_creation_add_annihilation f g).freeCumulant_comp id hs

/-- Second free cumulant of `creation 𝕜 (f x) + annihilation 𝕜 (g x)` on `{i, j}` with `i < j`. -/
theorem freeCumulant_vacuumState_creation_add_annihilation_pair {i j : α} (hij : i < j)
    (f g : α → H) :
    freeCumulant (vacuumState 𝕜 H).toLinearMap
        (fun x => creation 𝕜 (f x) + annihilation 𝕜 (g x)) {i, j} =
      ⟪g i, f j⟫_𝕜 := by
  rw [freeCumulant_vacuumState_creation_add_annihilation ⟨i, mem_insert_self i _⟩]
  simp [card_pair hij.ne, min_eq_left hij.le, max_eq_right hij.le]

/-- Every joint free cumulant of `creation 𝕜 (f i) + annihilation 𝕜 (g i)` of positive order
`#s ≠ 2` vanishes. -/
theorem freeCumulant_vacuumState_creation_add_annihilation_eq_zero {s : Finset α} (hs : s.Nonempty)
    (hcard : #s ≠ 2) (f g : α → H) :
    freeCumulant (vacuumState 𝕜 H).toLinearMap
        (fun i => creation 𝕜 (f i) + annihilation 𝕜 (g i)) s = 0 := by
  rw [freeCumulant_vacuumState_creation_add_annihilation hs]
  simp [hcard]

/-- Self-adjoint field operators `field 𝕜 (f i)` form a semicircular system for
`(vacuumState 𝕜 H).toLinearMap` with Gram covariance `Matrix.of fun i j => ⟪f i, f j⟫_𝕜`. -/
theorem isSemicircularSystem_field (f : ι → H) :
    IsSemicircularSystem (vacuumState 𝕜 H).toLinearMap
      (fun i => field 𝕜 (f i)) (Matrix.of fun i j => ⟪f i, f j⟫_𝕜) := by
  simp_rw [field_def]
  exact isSemicircularSystem_creation_add_annihilation f f

/-- Joint free cumulant of self-adjoint field operators `field 𝕜 (f i)` along a nonempty finite
ordered set `s`. -/
theorem freeCumulant_vacuumState_field {s : Finset α} (hs : s.Nonempty) (f : α → H) :
    freeCumulant (vacuumState 𝕜 H).toLinearMap (fun i => field 𝕜 (f i)) s =
      if #s = 2 then ⟪f (s.min' hs), f (s.max' hs)⟫_𝕜 else 0 := by
  simp_rw [field_def]
  exact freeCumulant_vacuumState_creation_add_annihilation hs f f

/-- Every field operator `field 𝕜 h` is semicircular of variance `(‖h‖ ^ 2 : 𝕜)` for
`(vacuumState 𝕜 H).toLinearMap`. -/
theorem isSemicircular_field (h : H) :
    IsSemicircular (vacuumState 𝕜 H).toLinearMap (field 𝕜 h) (‖h‖ ^ 2 : 𝕜) := by
  simpa [inner_self_eq_norm_sq_to_K] using
    (isSemicircularSystem_field fun _ : Unit => h).isSemicircular ()

/-- A family of field operators `field 𝕜 (f i)` is freely independent for the vacuum functional if
and only if the vectors `f i` are pairwise orthogonal. -/
theorem isFreelyIndependentElements_field_iff {f : ι → H} :
    IsFreelyIndependentElements (vacuumState 𝕜 H).toLinearMap (fun i => field 𝕜 (f i)) ↔
      ∀ i j, i ≠ j → ⟪f i, f j⟫_𝕜 = 0 := by
  simpa using (isSemicircularSystem_field f).isFreelyIndependentElements_iff

/-- Because field operators are self-adjoint, their `⋆`-free independence is likewise equivalent to
pairwise orthogonality of the underlying vectors. -/
theorem isStarFreelyIndependentElements_field_iff {f : ι → H} :
    IsStarFreelyIndependentElements (vacuumState 𝕜 H).toLinearMap (fun i => field 𝕜 (f i)) ↔
      ∀ i j, i ≠ j → ⟪f i, f j⟫_𝕜 = 0 := by
  rw [isStarFreelyIndependentElements_iff_of_isSelfAdjoint (R := 𝕜)
      (A := FullFockSpace 𝕜 H →L[𝕜] FullFockSpace 𝕜 H) (fun i => isSelfAdjoint_field (f i)),
    isFreelyIndependentElements_field_iff]

end Cumulants

section Circular

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- **Voiculescu's circular operator** on complex full Fock space: for orthogonal unit vectors
`e₁, e₂ : H`, `creation ℂ e₁ + annihilation ℂ e₂` (`ℓ(e₁) + ℓ(e₂)*`) is a standard circular element
for `(vacuumState ℂ H).toLinearMap`. -/
theorem isCircular_creation_add_annihilation {e₁ e₂ : H} (he₁ : ‖e₁‖ = 1) (he₂ : ‖e₂‖ = 1)
    (horth : ⟪e₁, e₂⟫_ℂ = 0) :
    IsCircular (vacuumState ℂ H).toLinearMap (creation ℂ e₁ + annihilation ℂ e₂) := by
  have hsys := isSemicircularSystem_creation_add_annihilation (𝕜 := ℂ) ![e₁, e₂] ![e₂, e₁]
  have hop : (fun i : Fin 2 => creation ℂ (![e₁, e₂] i) + annihilation ℂ (![e₂, e₁] i)) =
      ![creation ℂ e₁ + annihilation ℂ e₂, star (creation ℂ e₁ + annihilation ℂ e₂)] := by
    funext i
    fin_cases i
    · rfl
    · dsimp
      rw [ContinuousLinearMap.star_eq_adjoint, map_add, adjoint_creation, adjoint_annihilation,
        add_comm]
  have hcov : (Matrix.of fun i j : Fin 2 => ⟪![e₂, e₁] i, ![e₁, e₂] j⟫_ℂ) = !![0, 1; 1, 0] := by
    have h21 : ⟪e₂, e₁⟫_ℂ = 0 := by rw [← inner_conj_symm, horth, map_zero]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [horth, h21, inner_self_eq_norm_sq_to_K, he₁, he₂]
  rwa [hop, hcov] at hsys

/-- For orthogonal unit vectors `e₁, e₂ : H` in a complex inner product space, the normalized
combination `(√2)⁻¹ • (field ℂ e₁ + I • field ℂ e₂)` is a standard circular element for
`(vacuumState ℂ H).toLinearMap`. -/
theorem isCircular_field_add_I_smul_field {e₁ e₂ : H} (he₁ : ‖e₁‖ = 1) (he₂ : ‖e₂‖ = 1)
    (horth : ⟪e₁, e₂⟫_ℂ = 0) :
    IsCircular (vacuumState ℂ H).toLinearMap
      ((Real.sqrt 2 : ℂ)⁻¹ • (field ℂ e₁ + Complex.I • field ℂ e₂)) := by
  have hsys := isSemicircularSystem_field (𝕜 := ℂ) ![e₁, e₂]
  have hcov : (Matrix.of fun i j : Fin 2 => ⟪![e₁, e₂] i, ![e₁, e₂] j⟫_ℂ) = 1 := by
    have h21 : ⟪e₂, e₁⟫_ℂ = 0 := by rw [← inner_conj_symm, horth, map_zero]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [horth, h21, inner_self_eq_norm_sq_to_K, he₁, he₂]
  rw [hcov] at hsys
  exact hsys.isCircular fun i => isSelfAdjoint_field (![e₁, e₂] i)

end Circular

section OrthogonalIndependence

variable {𝕜 : Type u} {H : Type v} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  {ι : Type*}

/-- Every generator in `creation 𝕜 '' S ∪ star (creation 𝕜 '' S)` is of the form
`creation 𝕜 f + annihilation 𝕜 g` with each of `f`, `g` either `0` or in `S`. -/
private theorem exists_creation_add_annihilation_of_mem_union {S : Set H}
    {T : FullFockSpace 𝕜 H →L[𝕜] FullFockSpace 𝕜 H}
    (hT : T ∈ creation 𝕜 '' S ∪ star (creation 𝕜 '' S)) :
    ∃ f g : H, T = creation 𝕜 f + annihilation 𝕜 g ∧ (f = 0 ∨ f ∈ S) ∧ (g = 0 ∨ g ∈ S) := by
  rcases hT with ⟨x, hx, rfl⟩ | hstar
  · exact ⟨x, 0, by simp, Or.inr hx, Or.inl rfl⟩
  · obtain ⟨y, hy, hTy⟩ := (Set.mem_star.1 hstar : star T ∈ creation 𝕜 '' S)
    refine ⟨0, y, ?_, Or.inl rfl, Or.inr hy⟩
    have h := congrArg star hTy
    simpa using h.symm

/-- **Orthogonality implies `⋆`-freeness on full Fock space**: if `S : ι → Set H` is a family of
pairwise orthogonal subsets of `H`, then the unital `⋆`-subalgebras generated by the creation
operators `creation 𝕜 '' S i` are freely independent for `(vacuumState 𝕜 H).toLinearMap`. -/
theorem isFreelyIndependent_starAlgebra_adjoin_creation {S : ι → Set H}
    (horth : ∀ ⦃i j⦄, i ≠ j → ∀ x ∈ S i, ∀ y ∈ S j, ⟪x, y⟫_𝕜 = 0) :
    IsFreelyIndependent (vacuumState 𝕜 H).toLinearMap
      fun i => (StarAlgebra.adjoin 𝕜 (creation 𝕜 '' S i)).toSubalgebra := by
  simp_rw [StarAlgebra.adjoin_toSubalgebra]
  have h1 : (vacuumState 𝕜 H).toLinearMap 1 = 1 := vacuumState_one
  refine isFreelyIndependent_adjoin_of_freeCumulant_eq_zero h1 fun n a ℓ ha k k' hkk' => ?_
  choose f g ha_eq hf hg using fun m => exists_creation_add_annihilation_of_mem_union (ha m)
  have hfun : a = fun m => creation 𝕜 (f m) + annihilation 𝕜 (g m) := funext ha_eq
  have : Nonempty (Fin n) := ⟨k⟩
  rw [hfun, freeCumulant_vacuumState_creation_add_annihilation univ_nonempty f g]
  split_ifs with hcard
  · obtain rfl : n = 2 := by simpa using hcard
    have hmin : (univ : Finset (Fin 2)).min' univ_nonempty = 0 :=
      le_antisymm (min'_le _ 0 (mem_univ 0)) (Fin.zero_le _)
    have hmax : (univ : Finset (Fin 2)).max' univ_nonempty = 1 :=
      le_antisymm (Fin.le_last _) (le_max' _ 1 (mem_univ 1))
    have h01 : ℓ 0 ≠ ℓ 1 := by
      intro h01
      apply hkk'
      fin_cases k <;> fin_cases k' <;> simp [h01]
    rw [hmin, hmax]
    rcases hg 0 with hg0 | hg0
    · simp [hg0]
    rcases hf 1 with hf1 | hf1
    · simp [hf1]
    exact horth h01 _ hg0 _ hf1
  · rfl

/-- Norm closures of the unital `⋆`-subalgebras generated by creation operators on pairwise
orthogonal sets `S i` are freely independent for `(vacuumState 𝕜 H).toLinearMap`. -/
theorem isFreelyIndependent_topologicalClosure_starAlgebra_adjoin_creation {S : ι → Set H}
    (horth : ∀ ⦃i j⦄, i ≠ j → ∀ x ∈ S i, ∀ y ∈ S j, ⟪x, y⟫_𝕜 = 0) :
    IsFreelyIndependent (vacuumState 𝕜 H).toLinearMap
      fun i => (StarAlgebra.adjoin 𝕜 (creation 𝕜 '' S i)).toSubalgebra.topologicalClosure :=
  (isFreelyIndependent_starAlgebra_adjoin_creation horth).topologicalClosure
    vacuumState_one continuous_vacuumState

/-- Weak operator closures of the unital `⋆`-subalgebras generated by creation operators on
pairwise orthogonal sets `S i` are freely independent for the vacuum vector functional. -/
theorem isFreelyIndependent_weakOperatorClosure_starAlgebra_adjoin_creation {S : ι → Set H}
    (horth : ∀ ⦃i j⦄, i ≠ j → ∀ x ∈ S i, ∀ y ∈ S j, ⟪x, y⟫_𝕜 = 0) :
    IsFreelyIndependent
      ((vacuumState 𝕜 H).toLinearMap.comp (ContinuousLinearMapWOT.algEquiv 𝕜).toLinearMap)
      fun i => (((StarAlgebra.adjoin 𝕜 (creation 𝕜 '' S i)).toSubalgebra.map
        (ContinuousLinearMapWOT.algEquiv 𝕜).symm.toAlgHom).topologicalClosure) :=
  (isFreelyIndependent_weakOperatorClosure_iff_of_vectorState
    vacuumState_one (vacuum : FullFockSpace 𝕜 H) vacuumState_apply).2
    (isFreelyIndependent_starAlgebra_adjoin_creation horth)

/-- Unital subalgebras generated by field operators on pairwise orthogonal sets `S i` are freely
independent for `(vacuumState 𝕜 H).toLinearMap`. -/
theorem isFreelyIndependent_adjoin_field {S : ι → Set H}
    (horth : ∀ ⦃i j⦄, i ≠ j → ∀ x ∈ S i, ∀ y ∈ S j, ⟪x, y⟫_𝕜 = 0) :
    IsFreelyIndependent (vacuumState 𝕜 H).toLinearMap
      fun i => Algebra.adjoin 𝕜 (field 𝕜 '' S i) := by
  refine (isFreelyIndependent_starAlgebra_adjoin_creation horth).mono fun i =>
    Algebra.adjoin_le ?_
  rintro _ ⟨x, hx, rfl⟩
  have hmem : creation 𝕜 x ∈ StarAlgebra.adjoin 𝕜 (creation 𝕜 '' S i) :=
    StarAlgebra.subset_adjoin 𝕜 _ ⟨x, hx, rfl⟩
  have hadd : creation 𝕜 x + star (creation 𝕜 x) ∈ StarAlgebra.adjoin 𝕜 (creation 𝕜 '' S i) :=
    add_mem hmem (star_mem hmem)
  rwa [star_creation, ← field_def] at hadd

/-- A family of left creation operators `creation 𝕜 (v i)` is `⋆`-freely independent for the vacuum
functional if and only if the vectors `v i` are pairwise orthogonal. -/
theorem isStarFreelyIndependentElements_creation_iff {v : ι → H} :
    IsStarFreelyIndependentElements (vacuumState 𝕜 H).toLinearMap (fun i => creation 𝕜 (v i)) ↔
      ∀ i j, i ≠ j → ⟪v i, v j⟫_𝕜 = 0 := by
  rw [isStarFreelyIndependentElements_iff]
  refine ⟨fun hfree i j hij => ?_, fun horth => ?_⟩
  · have hmem_i : annihilation 𝕜 (v i) ∈ StarAlgebra.adjoin 𝕜 {creation 𝕜 (v i)} := by
      rw [← star_creation]
      exact star_mem (StarAlgebra.subset_adjoin 𝕜 _ (Set.mem_singleton _))
    have hmem_j : creation 𝕜 (v j) ∈ StarAlgebra.adjoin 𝕜 {creation 𝕜 (v j)} :=
      StarAlgebra.subset_adjoin 𝕜 _ (Set.mem_singleton _)
    have hzero := isFreelyIndependent_iff.1 hfree
      [(i, annihilation 𝕜 (v i)), (j, creation 𝕜 (v j))] (by simp) (by simp [hij])
      (by simp [hmem_i, hmem_j]) (by simp)
    have hmul : (vacuumState 𝕜 H).toLinearMap (annihilation 𝕜 (v i) * creation 𝕜 (v j)) =
        ⟪v i, v j⟫_𝕜 := vacuumState_annihilation_mul_creation (v i) (v j)
    simpa [mul_one, hmul] using hzero
  · have hS := isFreelyIndependent_starAlgebra_adjoin_creation (S := fun i => {v i})
      fun i j hij x hx y hy => by
        rw [Set.mem_singleton_iff.1 hx, Set.mem_singleton_iff.1 hy]
        exact horth i j hij
    simpa using hS

end OrthogonalIndependence

end FullFockSpace

end TauCeti

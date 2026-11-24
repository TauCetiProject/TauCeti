/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.BottSamelson.Moment

/-!
# The torus-fixed flags of the word `121` Bott–Samelson variety

Let `X = {(L₁, P, L) | L₁ ⊆ P₀, L₁ ⊆ P, L ⊆ P}` be the Bott–Samelson variety of the word `121`,
with `L₁, L` lines and `P` a plane in `ℂ³` and `P₀ = span(e₀, e₁)`
(`TauCeti.BottSamelson.initialPlane`). The torus `T = U(1)³` of diagonal unitaries acts on `ℂ³`;
its elements are the linear isometries `LinearIsometryEquiv.piLpCongrRight 2 e` for
`e : Fin 3 → ℂ ≃ₗᵢ[ℂ] ℂ`, which multiply each coordinate by a complex number of norm one. It
preserves `P₀`, so it acts on `X` by moving each of the three subspaces.

This file determines the fixed points and the kernel of this action. A subspace of `ℂ³` is fixed
by `T` exactly when it is a coordinate subspace (`Submodule.forall_map_piLpCongrRight_eq_iff`), and
coordinate subspaces are ordered by inclusion of their coordinate sets. So a fixed point of `X` is a
triple of coordinate sets `(s₁, t, u)` of sizes `1, 2, 1` with `s₁ ⊆ {0, 1}`, `s₁ ⊆ t` and `u ⊆ t`.
Writing `ij` for the plane `span(eᵢ, eⱼ)` and `eᵢ` for the line spanned by `eᵢ`, there are exactly
eight of them (`TauCeti.BottSamelson.fixedFlag`):

`(e₀, 01, e₀)`, `(e₀, 01, e₁)`, `(e₀, 02, e₀)`, `(e₀, 02, e₂)`,
`(e₁, 01, e₀)`, `(e₁, 01, e₁)`, `(e₁, 12, e₁)`, `(e₁, 12, e₂)`

(`TauCeti.BottSamelson.forall_map_eq_iff_exists_fixedFlag`). They are pairwise distinct, and their
moment values are, in this order, the eight rows of `TauCeti.BottSamelson.fixedMoment`
(`TauCeti.BottSamelson.moment_fixedFlag`). So the fixed points keep their labels even for the
weights `a = c`, where the moment values of `fixedFlag 1` and `fixedFlag 4` coincide (rows `2`
and `5` of the table in `TauCeti.Geometry.Symplectic.BottSamelson.FixedMoment`, which numbers its
rows from `1`, so that row `k + 1` is `fixedMoment a b c k`).

The kernel of the action is the diagonal circle: a diagonal unitary fixes every point of `X` exactly
when its three entries agree (`TauCeti.BottSamelson.forall_map_eq_iff_forall_eq`). Scalars fix every
subspace. Conversely, `X` contains the points `(e₀, 0j, span(e₀ + eⱼ))` for `j = 1, 2`, and a
diagonal unitary fixing the line `span(e₀ + eⱼ)` has equal `0`-th and `j`-th entries. Thus the
effective torus `T / U(1)` has dimension two, matching the affine trace plane
`x + y + z = a + 2b + c` in which the moment map takes its values
(`TauCeti.BottSamelson.sum_moment`).

## Main definitions

* `TauCeti.BottSamelson.fixedFlagCoords`: the coordinate sets of the eight fixed flags.
* `TauCeti.BottSamelson.fixedFlag`: the eight fixed flags, as triples of coordinate subspaces.

## Main results

* `TauCeti.BottSamelson.fixedFlag_mem`: each fixed flag satisfies the rank and incidence conditions
  of `X`.
* `TauCeti.BottSamelson.map_fixedFlag`: each fixed flag is fixed by the torus.
* `TauCeti.BottSamelson.forall_map_eq_iff_exists_fixedFlag`: a point of `X` is fixed by the torus
  exactly when it is one of the eight fixed flags.
* `TauCeti.BottSamelson.fixedFlag_injective`: the eight fixed flags are distinct.
* `TauCeti.BottSamelson.moment_fixedFlag`: the moment value of `fixedFlag k` is
  `fixedMoment a b c k`.
* `TauCeti.BottSamelson.forall_map_eq_iff_forall_eq`: the kernel of the torus action on `X` is the
  diagonal circle.

## References

* L. Escobar, *Brick manifolds and toric varieties of brick polytopes*, Electron. J. Combin. 23
  (2016), §3.2 and §4.1 (Bott–Samelson varieties inside products of Grassmannians, and their torus
  fixed points).
-/

public section

noncomputable section

namespace TauCeti.BottSamelson

open Module Set Submodule

/-- The coordinate sets `(s₁, t, u)` of the eight torus-fixed flags of the Bott–Samelson variety of
the word `121`: `fixedFlag k` is the triple of coordinate subspaces spanned by the `eᵢ` with
`i` in `s₁`, `t` and `u` respectively. They are ordered as the rows of `fixedMoment`. -/
def fixedFlagCoords : Fin 8 → Finset (Fin 3) × Finset (Fin 3) × Finset (Fin 3) :=
  ![({0}, {0, 1}, {0}), ({0}, {0, 1}, {1}), ({0}, {0, 2}, {0}), ({0}, {0, 2}, {2}),
    ({1}, {0, 1}, {0}), ({1}, {0, 1}, {1}), ({1}, {1, 2}, {1}), ({1}, {1, 2}, {2})]

/-- The coordinate sets of the eight fixed flags, listed in the order of `fixedMoment`. -/
theorem fixedFlagCoords_def :
    fixedFlagCoords =
      ![({0}, {0, 1}, {0}), ({0}, {0, 1}, {1}), ({0}, {0, 2}, {0}), ({0}, {0, 2}, {2}),
        ({1}, {0, 1}, {0}), ({1}, {0, 1}, {1}), ({1}, {1, 2}, {1}), ({1}, {1, 2}, {2})] :=
  (rfl)

/-- The eight torus-fixed flags `(L₁, P, L)` of the Bott–Samelson variety of the word `121`: the
triples of coordinate subspaces with coordinate sets `fixedFlagCoords k`. -/
def fixedFlag (k : Fin 8) :
    Submodule ℂ (EuclideanSpace ℂ (Fin 3)) × Submodule ℂ (EuclideanSpace ℂ (Fin 3)) ×
      Submodule ℂ (EuclideanSpace ℂ (Fin 3)) :=
  (span ℂ ((fun i ↦ EuclideanSpace.single i (1 : ℂ)) '' ((fixedFlagCoords k).1 : Set (Fin 3))),
    span ℂ ((fun i ↦ EuclideanSpace.single i (1 : ℂ)) '' ((fixedFlagCoords k).2.1 : Set (Fin 3))),
    span ℂ ((fun i ↦ EuclideanSpace.single i (1 : ℂ)) '' ((fixedFlagCoords k).2.2 : Set (Fin 3))))

/-- The fixed flag `fixedFlag k` is the triple of coordinate subspaces of `fixedFlagCoords k`. -/
theorem fixedFlag_def (k : Fin 8) :
    fixedFlag k =
      (span ℂ ((fun i ↦ EuclideanSpace.single i (1 : ℂ)) '' ((fixedFlagCoords k).1 : Set (Fin 3))),
        span ℂ ((fun i ↦ EuclideanSpace.single i (1 : ℂ)) ''
          ((fixedFlagCoords k).2.1 : Set (Fin 3))),
        span ℂ ((fun i ↦ EuclideanSpace.single i (1 : ℂ)) ''
          ((fixedFlagCoords k).2.2 : Set (Fin 3)))) :=
  (rfl)

/-- The triples of coordinate sets of sizes `1, 2, 1` satisfying the incidences `s₁ ⊆ {0, 1}`,
`s₁ ⊆ t` and `u ⊆ t` are exactly the coordinate sets of the fixed flags. -/
theorem exists_fixedFlagCoords_eq_iff (s₁ t u : Finset (Fin 3)) :
    (∃ k, fixedFlagCoords k = (s₁, t, u)) ↔
      s₁.card = 1 ∧ t.card = 2 ∧ u.card = 1 ∧ s₁ ⊆ {0, 1} ∧ s₁ ⊆ t ∧ u ⊆ t := by
  revert s₁ t u
  decide

/-- The coordinate sets of the fixed flags are pairwise distinct. -/
theorem fixedFlagCoords_injective : Function.Injective fixedFlagCoords := by
  decide

/-- The fixed flags are pairwise distinct, even when their moment values coincide. -/
theorem fixedFlag_injective : Function.Injective fixedFlag := by
  intro k l h
  simp only [fixedFlag, Prod.mk.injEq] at h
  have hinj := (span_image_single_injective (𝕜 := ℂ) (ι := Fin 3)).comp Finset.coe_injective
  exact fixedFlagCoords_injective (Prod.ext (hinj h.1) (Prod.ext (hinj h.2.1) (hinj h.2.2)))

/-- The rank and incidence conditions of the coordinate subspaces with coordinate sets `s₁, t, u`
are those of the sets. -/
private theorem span_image_single_mem_iff (s₁ t u : Finset (Fin 3)) :
    (finrank ℂ (span ℂ ((fun i ↦ EuclideanSpace.single i (1 : ℂ)) '' (s₁ : Set (Fin 3)))) = 1 ∧
      finrank ℂ (span ℂ ((fun i ↦ EuclideanSpace.single i (1 : ℂ)) '' (t : Set (Fin 3)))) = 2 ∧
      finrank ℂ (span ℂ ((fun i ↦ EuclideanSpace.single i (1 : ℂ)) '' (u : Set (Fin 3)))) = 1 ∧
      span ℂ ((fun i ↦ EuclideanSpace.single i (1 : ℂ)) '' (s₁ : Set (Fin 3))) ≤ initialPlane ∧
      span ℂ ((fun i ↦ EuclideanSpace.single i (1 : ℂ)) '' (s₁ : Set (Fin 3))) ≤
        span ℂ ((fun i ↦ EuclideanSpace.single i (1 : ℂ)) '' (t : Set (Fin 3))) ∧
      span ℂ ((fun i ↦ EuclideanSpace.single i (1 : ℂ)) '' (u : Set (Fin 3))) ≤
        span ℂ ((fun i ↦ EuclideanSpace.single i (1 : ℂ)) '' (t : Set (Fin 3)))) ↔
      s₁.card = 1 ∧ t.card = 2 ∧ u.card = 1 ∧ s₁ ⊆ {0, 1} ∧ s₁ ⊆ t ∧ u ⊆ t := by
  rw [initialPlane_eq_span_image, ← Finset.coe_pair]
  simp only [finrank_span_image_single, span_image_single_le_span_image_single_iff,
    Finset.coe_subset]

/-- Each fixed flag `(L₁, P, L)` is a point of the Bott–Samelson variety of the word `121`: a line
`L₁ ⊆ P₀`, a plane `P ⊇ L₁` and a line `L ⊆ P`. -/
theorem fixedFlag_mem (k : Fin 8) :
    finrank ℂ (fixedFlag k).1 = 1 ∧ finrank ℂ (fixedFlag k).2.1 = 2 ∧
      finrank ℂ (fixedFlag k).2.2 = 1 ∧ (fixedFlag k).1 ≤ initialPlane ∧
        (fixedFlag k).1 ≤ (fixedFlag k).2.1 ∧ (fixedFlag k).2.2 ≤ (fixedFlag k).2.1 :=
  (span_image_single_mem_iff _ _ _).2 ((exists_fixedFlagCoords_eq_iff _ _ _).1 ⟨k, rfl⟩)

/-- Each fixed flag is fixed by the diagonal unitary group. -/
theorem map_fixedFlag (k : Fin 8) (e : Fin 3 → ℂ ≃ₗᵢ[ℂ] ℂ) :
    (fixedFlag k).1.map ((LinearIsometryEquiv.piLpCongrRight 2 e :
        EuclideanSpace ℂ (Fin 3) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin 3)).toLinearEquiv :
          EuclideanSpace ℂ (Fin 3) →ₗ[ℂ] EuclideanSpace ℂ (Fin 3)) = (fixedFlag k).1 ∧
      (fixedFlag k).2.1.map ((LinearIsometryEquiv.piLpCongrRight 2 e :
        EuclideanSpace ℂ (Fin 3) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin 3)).toLinearEquiv :
          EuclideanSpace ℂ (Fin 3) →ₗ[ℂ] EuclideanSpace ℂ (Fin 3)) = (fixedFlag k).2.1 ∧
      (fixedFlag k).2.2.map ((LinearIsometryEquiv.piLpCongrRight 2 e :
        EuclideanSpace ℂ (Fin 3) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin 3)).toLinearEquiv :
          EuclideanSpace ℂ (Fin 3) →ₗ[ℂ] EuclideanSpace ℂ (Fin 3)) = (fixedFlag k).2.2 :=
  ⟨map_piLpCongrRight_span_image_single e _, map_piLpCongrRight_span_image_single e _,
    map_piLpCongrRight_span_image_single e _⟩

/-- **The torus-fixed points of the word `121` Bott–Samelson variety.** A point `(L₁, P, L)` of the
variety, a line `L₁ ⊆ P₀`, a plane `P ⊇ L₁` and a line `L ⊆ P`, is fixed by the diagonal unitary
group exactly when it is one of the eight flags `fixedFlag k`. -/
theorem forall_map_eq_iff_exists_fixedFlag {L₁ P L : Submodule ℂ (EuclideanSpace ℂ (Fin 3))}
    (hL₁ : finrank ℂ L₁ = 1) (hP : finrank ℂ P = 2) (hL : finrank ℂ L = 1)
    (h₁ : L₁ ≤ initialPlane) (hL₁P : L₁ ≤ P) (hLP : L ≤ P) :
    (∀ e : Fin 3 → ℂ ≃ₗᵢ[ℂ] ℂ,
      L₁.map ((LinearIsometryEquiv.piLpCongrRight 2 e :
        EuclideanSpace ℂ (Fin 3) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin 3)).toLinearEquiv :
          EuclideanSpace ℂ (Fin 3) →ₗ[ℂ] EuclideanSpace ℂ (Fin 3)) = L₁ ∧
      P.map ((LinearIsometryEquiv.piLpCongrRight 2 e :
        EuclideanSpace ℂ (Fin 3) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin 3)).toLinearEquiv :
          EuclideanSpace ℂ (Fin 3) →ₗ[ℂ] EuclideanSpace ℂ (Fin 3)) = P ∧
      L.map ((LinearIsometryEquiv.piLpCongrRight 2 e :
        EuclideanSpace ℂ (Fin 3) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin 3)).toLinearEquiv :
          EuclideanSpace ℂ (Fin 3) →ₗ[ℂ] EuclideanSpace ℂ (Fin 3)) = L) ↔
      ∃ k, fixedFlag k = (L₁, P, L) := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · classical
    -- each of the three subspaces is the coordinate subspace of the basis vectors it contains
    have key (U : Submodule ℂ (EuclideanSpace ℂ (Fin 3)))
        (hU : ∀ e : Fin 3 → ℂ ≃ₗᵢ[ℂ] ℂ, U.map ((LinearIsometryEquiv.piLpCongrRight 2 e :
          EuclideanSpace ℂ (Fin 3) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin 3)).toLinearEquiv :
            EuclideanSpace ℂ (Fin 3) →ₗ[ℂ] EuclideanSpace ℂ (Fin 3)) = U) :
        U = span ℂ ((fun i ↦ EuclideanSpace.single i (1 : ℂ)) ''
          ((Finset.univ.filter fun i ↦ EuclideanSpace.single i (1 : ℂ) ∈ U :
            Finset (Fin 3)) : Set (Fin 3))) := by
      rw [Finset.coe_filter_univ]
      exact eq_span_image_single_of_forall_map_piLpCongrRight_le U fun e ↦ (hU e).le
    obtain ⟨s₁, e₁⟩ : ∃ s : Finset (Fin 3),
        L₁ = span ℂ ((fun i ↦ EuclideanSpace.single i (1 : ℂ)) '' (s : Set (Fin 3))) :=
      ⟨_, key L₁ fun e ↦ (h e).1⟩
    obtain ⟨t, e₂⟩ : ∃ s : Finset (Fin 3),
        P = span ℂ ((fun i ↦ EuclideanSpace.single i (1 : ℂ)) '' (s : Set (Fin 3))) :=
      ⟨_, key P fun e ↦ (h e).2.1⟩
    obtain ⟨u, e₃⟩ : ∃ s : Finset (Fin 3),
        L = span ℂ ((fun i ↦ EuclideanSpace.single i (1 : ℂ)) '' (s : Set (Fin 3))) :=
      ⟨_, key L fun e ↦ (h e).2.2⟩
    subst e₁ e₂ e₃
    obtain ⟨k, hk⟩ := (exists_fixedFlagCoords_eq_iff s₁ t u).2
      ((span_image_single_mem_iff s₁ t u).1 ⟨hL₁, hP, hL, h₁, hL₁P, hLP⟩)
    exact ⟨k, by rw [fixedFlag_def, hk]⟩
  · rintro ⟨k, hk⟩ e
    have hmap := map_fixedFlag k e
    rwa [hk] at hmap

/-- The moment value of `fixedFlag k` is `fixedMoment a b c k`. -/
@[simp]
theorem moment_fixedFlag (a b c : ℝ) (k : Fin 8) :
    moment a b c (fixedFlag k).1 (fixedFlag k).2.1 (fixedFlag k).2.2 = fixedMoment a b c k := by
  ext i
  simp only [fixedFlag, moment_apply, projectorDiagonal_span_single]
  fin_cases k <;> fin_cases i <;> simp [fixedFlagCoords_def, fixedMoment_def]

/-- **The kernel of the torus action on the word `121` Bott–Samelson variety is the diagonal
circle.** A diagonal unitary fixes every point `(L₁, P, L)` of the variety exactly when its three
entries agree. -/
theorem forall_map_eq_iff_forall_eq (e : Fin 3 → ℂ ≃ₗᵢ[ℂ] ℂ) :
    (∀ L₁ P L : Submodule ℂ (EuclideanSpace ℂ (Fin 3)), finrank ℂ L₁ = 1 → finrank ℂ P = 2 →
      finrank ℂ L = 1 → L₁ ≤ initialPlane → L₁ ≤ P → L ≤ P →
        L₁.map ((LinearIsometryEquiv.piLpCongrRight 2 e :
          EuclideanSpace ℂ (Fin 3) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin 3)).toLinearEquiv :
            EuclideanSpace ℂ (Fin 3) →ₗ[ℂ] EuclideanSpace ℂ (Fin 3)) = L₁ ∧
        P.map ((LinearIsometryEquiv.piLpCongrRight 2 e :
          EuclideanSpace ℂ (Fin 3) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin 3)).toLinearEquiv :
            EuclideanSpace ℂ (Fin 3) →ₗ[ℂ] EuclideanSpace ℂ (Fin 3)) = P ∧
        L.map ((LinearIsometryEquiv.piLpCongrRight 2 e :
          EuclideanSpace ℂ (Fin 3) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin 3)).toLinearEquiv :
            EuclideanSpace ℂ (Fin 3) →ₗ[ℂ] EuclideanSpace ℂ (Fin 3)) = L) ↔
      ∀ i j, e i = e j := by
  refine ⟨fun h ↦ ?_, fun he _ _ _ _ _ _ _ _ _ ↦ ⟨map_piLpCongrRight_of_forall_eq _ he,
    map_piLpCongrRight_of_forall_eq _ he, map_piLpCongrRight_of_forall_eq _ he⟩⟩
  -- the point `(e₀, span(e₀, eⱼ), span(e₀ + eⱼ))` forces `e 0 = e j`
  have h0 (j : Fin 3) (hj : j ≠ 0) : e 0 = e j := by
    have hv : EuclideanSpace.single 0 (1 : ℂ) + EuclideanSpace.single j 1 ≠ 0 := fun hv ↦ by
      simpa [hj.symm] using congr($hv 0)
    obtain ⟨hr₁, hr₂, -, hle₀, hle₁, -⟩ := (span_image_single_mem_iff {0} {0, j} {0}).2
      (by simp [Finset.card_pair hj.symm])
    refine eq_of_map_piLpCongrRight_span_singleton_le hj.symm
      (h _ _ _ hr₁ hr₂ (finrank_span_singleton hv) hle₀ hle₁ ?_).2.2.le
    rw [span_le, singleton_subset_iff]
    exact add_mem (subset_span ⟨0, by simp, rfl⟩) (subset_span ⟨j, by simp, rfl⟩)
  have h0' (i : Fin 3) : e 0 = e i := by
    fin_cases i
    exacts [rfl, h0 _ (by decide), h0 _ (by decide)]
  intro i j
  rw [← h0' i, ← h0' j]

end TauCeti.BottSamelson

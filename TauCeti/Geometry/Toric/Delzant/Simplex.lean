/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Delzant.Basic

/-!
# The standard simplex as a Delzant polytope

The moment polytope of the standard torus action on complex projective space `ℂPⁿ`, with the
Fubini–Study form scaled to size `a`, is the standard simplex

`Δ = {x ∈ (ℝⁿ)* | 0 ≤ x(e_k) for every k, x(e_1) + ⋯ + x(e_n) ≤ a}`.

In the standard lattice `ℤⁿ ⊂ ℝⁿ` (`(Int.castAddHom ℝ).compLeft (Fin n)`) it has `n + 1` facets,
indexed by `Option (Fin n)`: the coordinate facet `{x(e_k) = 0}` has inward normal `e_k`
and support constant `0`, and the facet `{x(e_1) + ⋯ + x(e_n) = a}` has inward normal
`-(e_1 + ⋯ + e_n)` and support constant `-a` (`TauCeti.Toric.simplexNormal`,
`TauCeti.Toric.simplexSupport`).

For `n ≠ 0` and `a > 0` this presentation is Delzant (`TauCeti.Toric.isDelzant_simplex`). The
`n + 1` constraints are never all active at once, since adding the `n + 1` active equations would
give `0 = a`. At a vertex the active normals span, which forces exactly one constraint to be
inactive. The `n + 1` normals sum to zero, so any `n` of them generate `ℤⁿ`, and hence form a
lattice basis (`TauCeti.Toric.isSmoothVertex_iff_span_eq_top`). The vertices are `0` and the points
`a e_k*` (`TauCeti.Toric.mem_extremePoints_facetPolyhedron_simplex_iff`).

## Main definitions

* `TauCeti.Toric.simplexNormal n`: the inward facet normals `e_1, …, e_n, -(e_1 + ⋯ + e_n)`.
* `TauCeti.Toric.simplexSupport n a`: the support constants `0, …, 0, -a`.

## Main results

* `TauCeti.Toric.mem_facetPolyhedron_simplex_iff`: the polyhedron is the standard simplex of
  size `a`.
* `TauCeti.Toric.mem_extremePoints_facetPolyhedron_simplex_iff`: its vertices are `0` and the
  points `a e_k*`.
* `TauCeti.Toric.isDelzant_simplex`: for `n ≠ 0` and `a > 0` it is a Delzant polytope.

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 28.
* V. Guillemin, *Moment Maps and Combinatorial Invariants of Hamiltonian `T^n`-spaces*,
  Birkhäuser, 1994, Chapter 1.
-/

public section

noncomputable section

open Set

namespace TauCeti.Toric

variable (n : ℕ) (a : ℝ)

/-- The inward facet normals of the standard `n`-simplex in the lattice `ℤⁿ`: the standard basis
vector `e_k` for the coordinate facet `{x(e_k) = 0}`, and `-(e_1 + ⋯ + e_n)` for the facet
`{x(e_1) + ⋯ + x(e_n) = a}`. -/
def simplexNormal (j : Option (Fin n)) : Fin n → ℤ :=
  j.elim (-1) fun k ↦ Pi.single k 1

/-- The support constants of the standard simplex of size `a`: `0` for the coordinate facets and
`-a` for the facet `{x(e_1) + ⋯ + x(e_n) = a}`. -/
def simplexSupport (j : Option (Fin n)) : ℝ :=
  j.elim (-a) fun _ ↦ 0

variable {n a}

@[simp]
theorem simplexNormal_none : simplexNormal n none = -1 := (rfl)

@[simp]
theorem simplexNormal_some (k : Fin n) : simplexNormal n (some k) = Pi.single k 1 := (rfl)

@[simp]
theorem simplexSupport_none : simplexSupport n a none = -a := (rfl)

@[simp]
theorem simplexSupport_some (k : Fin n) : simplexSupport n a (some k) = 0 := (rfl)

/-- The pairing of a functional with the coordinate normal `e_k` is its value on `e_k`. -/
private theorem facetPairing_simplexNormal_some (x : StrongDual ℝ (Fin n → ℝ)) (k : Fin n) :
    facetPairing ((Int.castAddHom ℝ).compLeft (Fin n)) (simplexNormal n) (some k) x =
      x (Pi.single k 1) := by
  rw [facetPairing_apply, simplexNormal_some]
  congr 1
  ext l
  simp [Pi.single_apply, apply_ite]

/-- The pairing of a functional with the normal `-(e_1 + ⋯ + e_n)` is minus the sum of its values
on the `e_k`. -/
private theorem facetPairing_simplexNormal_none (x : StrongDual ℝ (Fin n → ℝ)) :
    facetPairing ((Int.castAddHom ℝ).compLeft (Fin n)) (simplexNormal n) none x =
      -∑ k, x (Pi.single k 1) := by
  have h : (Int.castAddHom ℝ).compLeft (Fin n) (simplexNormal n none) =
      -∑ k, Pi.single k (1 : ℝ) := by
    rw [Finset.univ_sum_single (fun _ ↦ (1 : ℝ))]
    ext l
    simp
  rw [facetPairing_apply, h, map_neg, map_sum]

/-- **The standard simplex.** The polyhedron of the simplex presentation consists of the
functionals with nonnegative values `x(e_k)` summing to at most `a`. -/
theorem mem_facetPolyhedron_simplex_iff {x : StrongDual ℝ (Fin n → ℝ)} :
    x ∈ facetPolyhedron ((Int.castAddHom ℝ).compLeft (Fin n)) (simplexNormal n)
        (simplexSupport n a) ↔
      (∀ k, 0 ≤ x (Pi.single k 1)) ∧ ∑ k, x (Pi.single k 1) ≤ a := by
  simp only [mem_facetPolyhedron, ← facetPairing_apply, Option.forall,
    facetPairing_simplexNormal_none, facetPairing_simplexNormal_some, simplexSupport_none,
    simplexSupport_some, neg_le_neg_iff]
  exact and_comm

/-- The coordinate facet `{x(e_k) = 0}` is active at `x` exactly when `x(e_k) = 0`. -/
theorem some_mem_activeSet_simplex_iff {x : StrongDual ℝ (Fin n → ℝ)} {k : Fin n} :
    some k ∈ activeSet (facetPairing ((Int.castAddHom ℝ).compLeft (Fin n)) (simplexNormal n))
        (simplexSupport n a) x ↔ x (Pi.single k 1) = 0 := by
  rw [mem_activeSet, facetPairing_simplexNormal_some, simplexSupport_some]

/-- The facet `{x(e_1) + ⋯ + x(e_n) = a}` is active at `x` exactly when the values `x(e_k)` sum
to `a`. -/
theorem none_mem_activeSet_simplex_iff {x : StrongDual ℝ (Fin n → ℝ)} :
    none ∈ activeSet (facetPairing ((Int.castAddHom ℝ).compLeft (Fin n)) (simplexNormal n))
        (simplexSupport n a) x ↔ ∑ k, x (Pi.single k 1) = a := by
  rw [mem_activeSet, facetPairing_simplexNormal_none, simplexSupport_none, neg_inj]

/-- For distinct facets `j` and `m`, some nonzero functional vanishes on every normal other than
those of `j` and `m`. -/
private theorem exists_ne_zero_facetPairing_simplex_eq_zero {j m : Option (Fin n)} (hjm : j ≠ m) :
    ∃ w : StrongDual ℝ (Fin n → ℝ), w ≠ 0 ∧ ∀ l, l ≠ j → l ≠ m →
      facetPairing ((Int.castAddHom ℝ).compLeft (Fin n)) (simplexNormal n) l w = 0 := by
  -- With `j = some p` and `m = some q`, take `x ↦ x_p - x_q`; if one of them is `none`, take the
  -- coordinate of the other.
  have hproj (q : Fin n) : ∃ w : StrongDual ℝ (Fin n → ℝ), w ≠ 0 ∧ ∀ l, l ≠ some q → l ≠ none →
      facetPairing ((Int.castAddHom ℝ).compLeft (Fin n)) (simplexNormal n) l w = 0 := by
    refine ⟨ContinuousLinearMap.proj q, fun h ↦ ?_, fun l hlq hl ↦ ?_⟩
    · simpa using congr($h (Pi.single q 1))
    · obtain ⟨l, rfl⟩ := Option.ne_none_iff_exists'.1 hl
      have hlq' : q ≠ l := fun h ↦ hlq (congrArg some h.symm)
      simp [hlq']
  rcases j with _ | p <;> rcases m with _ | q
  · exact absurd rfl hjm
  · obtain ⟨w, hw, h⟩ := hproj q
    exact ⟨w, hw, fun l hl hl' ↦ h l hl' hl⟩
  · exact hproj p
  · have hpq : p ≠ q := fun h ↦ hjm (h ▸ rfl)
    refine ⟨ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n ↦ ℝ) p -
      ContinuousLinearMap.proj q, fun h ↦ ?_, fun l hl hl' ↦ ?_⟩
    · simpa [hpq] using congr($h (Pi.single p 1))
    rcases l with _ | l
    · simp
    · have hlp : p ≠ l := fun h ↦ hl (congrArg some h.symm)
      have hlq : q ≠ l := fun h ↦ hl' (congrArg some h.symm)
      simp [hlp, hlq]

/-- At a vertex of the standard simplex, all constraints but exactly one are active. -/
private theorem exists_activeSet_simplex_eq_compl_singleton (ha : 0 < a)
    {x : StrongDual ℝ (Fin n → ℝ)} (hx : x ∈ (facetPolyhedron ((Int.castAddHom ℝ).compLeft (Fin n))
      (simplexNormal n) (simplexSupport n a)).extremePoints ℝ) :
    ∃ j, activeSet (facetPairing ((Int.castAddHom ℝ).compLeft (Fin n)) (simplexNormal n))
      (simplexSupport n a) x = {j}ᶜ := by
  obtain ⟨-, hker⟩ := mem_extremePoints_facetPolyhedron_iff.1 hx
  -- Not every constraint is active: adding all the active equations would give `0 = a`.
  obtain ⟨j, hj⟩ : ∃ j, j ∉ activeSet (facetPairing ((Int.castAddHom ℝ).compLeft (Fin n))
      (simplexNormal n)) (simplexSupport n a) x := by
    by_contra! h
    have hsum := none_mem_activeSet_simplex_iff.1 (h none)
    simp only [some_mem_activeSet_simplex_iff.1 (h (some _)), Finset.sum_const_zero] at hsum
    exact ha.ne hsum
  -- Every other constraint is active, since otherwise a nonzero functional kills the active
  -- normals.
  refine ⟨j, Set.ext fun m ↦ ⟨fun hm hmj ↦ hj (hmj ▸ hm), fun hmj ↦ ?_⟩⟩
  by_contra hm
  obtain ⟨w, hw, hwl⟩ := exists_ne_zero_facetPairing_simplex_eq_zero (Ne.symm hmj)
  refine hw (hker w fun l hl ↦ ?_)
  rw [← facetPairing_apply]
  exact hwl l (fun h ↦ hj (h ▸ hl)) fun h ↦ hm (h ▸ hl)

/-- Any `n` of the `n + 1` simplex normals generate the lattice `ℤⁿ`. -/
private theorem span_image_simplexNormal_compl_singleton (j : Option (Fin n)) :
    Submodule.span ℤ (simplexNormal n '' {j}ᶜ) = ⊤ := by
  set S := Submodule.span ℤ (simplexNormal n '' {j}ᶜ)
  have hmem {l} (hl : l ≠ j) : simplexNormal n l ∈ S :=
    Submodule.subset_span ⟨l, hl, rfl⟩
  -- Each `e_k` lies in `S`; when `j = some k`, it is the negative of the sum of the other normals.
  have he (k : Fin n) : Pi.single k (1 : ℤ) ∈ S := by
    by_cases hk : some k = j
    · subst hk
      have hsum : Pi.single k (1 : ℤ) =
          -simplexNormal n none - ∑ l ∈ Finset.univ.erase k, simplexNormal n (some l) := by
        rw [simplexNormal_none, neg_neg, eq_sub_iff_add_eq]
        simp only [simplexNormal_some]
        rw [Finset.add_sum_erase _ (fun l ↦ Pi.single l (1 : ℤ)) (Finset.mem_univ k),
          Finset.univ_sum_single (fun _ ↦ (1 : ℤ)), Pi.one_def]
      rw [hsum]
      exact S.sub_mem (S.neg_mem (hmem (by simp))) (S.sum_mem fun l hl ↦
        hmem fun h ↦ (Finset.ne_of_mem_erase hl) (Option.some_injective _ h))
    · exact hmem hk
  rw [eq_top_iff, ← (Pi.basisFun ℤ (Fin n)).span_eq, Submodule.span_le]
  rintro _ ⟨k, rfl⟩
  simpa using he k

/-- At a vertex of the standard simplex the inactive constraint determines the vertex: it is `0`
when the slanted facet is inactive and `a e_p*` when the facet `{x(e_p) = 0}` is. -/
private theorem eq_zero_or_eq_smul_proj_of_mem_extremePoints (ha : 0 < a)
    {x : StrongDual ℝ (Fin n → ℝ)} (hx : x ∈ (facetPolyhedron ((Int.castAddHom ℝ).compLeft (Fin n))
      (simplexNormal n) (simplexSupport n a)).extremePoints ℝ) :
    x = 0 ∨ ∃ k, x = a • ContinuousLinearMap.proj k := by
  obtain ⟨j, hj⟩ := exists_activeSet_simplex_eq_compl_singleton ha hx
  have hzero {k : Fin n} (hk : some k ≠ j) : x (Pi.single k 1) = 0 :=
    some_mem_activeSet_simplex_iff.1 (by rw [hj]; exact hk)
  rcases j with _ | p
  · exact Or.inl (ContinuousLinearMap.coe_injective <| (Pi.basisFun ℝ (Fin n)).ext
      fun k ↦ by simpa using hzero (Option.some_ne_none k))
  · -- All values but the `p`-th vanish, and the values sum to `a`.
    have hsum := none_mem_activeSet_simplex_iff.1 (by rw [hj]; simp)
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ p), Finset.sum_eq_zero fun k hk ↦
      hzero fun h ↦ (Finset.ne_of_mem_erase hk) (Option.some_injective _ h), add_zero] at hsum
    refine Or.inr ⟨p, ContinuousLinearMap.coe_injective <| (Pi.basisFun ℝ (Fin n)).ext fun k ↦ ?_⟩
    by_cases hk : k = p
    · subst hk
      simpa using hsum
    · simpa [Pi.single_apply, hk] using hzero fun h ↦ hk (Option.some_injective _ h)

/-- **The vertices of the standard simplex.** For `a > 0`, the vertices are `0` and the points
`a e_k*`, where `e_k*` is the `k`-th coordinate functional. -/
theorem mem_extremePoints_facetPolyhedron_simplex_iff (ha : 0 < a)
    {x : StrongDual ℝ (Fin n → ℝ)} :
    x ∈ (facetPolyhedron ((Int.castAddHom ℝ).compLeft (Fin n)) (simplexNormal n)
        (simplexSupport n a)).extremePoints ℝ ↔
      x = 0 ∨ ∃ k, x = a • ContinuousLinearMap.proj k := by
  refine ⟨eq_zero_or_eq_smul_proj_of_mem_extremePoints ha, fun hx ↦ ?_⟩
  have hmem : x ∈ facetPolyhedron ((Int.castAddHom ℝ).compLeft (Fin n)) (simplexNormal n)
      (simplexSupport n a) := by
    rw [mem_facetPolyhedron_simplex_iff]
    rcases hx with rfl | ⟨p, rfl⟩
    · simp [ha.le]
    · refine ⟨fun k ↦ ?_, by simp [Pi.single_apply]⟩
      simp only [Pi.single_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
      split_ifs <;> simp [ha.le]
  -- The active normals span: a functional vanishing on them vanishes on every `e_k`.
  refine mem_extremePoints_facetPolyhedron_iff.2 ⟨hmem, fun w hw ↦ ?_⟩
  have hw' (j) (hj : j ∈ activeSet (facetPairing ((Int.castAddHom ℝ).compLeft (Fin n))
      (simplexNormal n)) (simplexSupport n a) x) :
      facetPairing ((Int.castAddHom ℝ).compLeft (Fin n)) (simplexNormal n) j w = 0 := by
    rw [facetPairing_apply]
    exact hw j hj
  rcases hx with rfl | ⟨p, rfl⟩
  · refine ContinuousLinearMap.coe_injective <| (Pi.basisFun ℝ (Fin n)).ext fun k ↦ ?_
    have h := hw' (some k) (some_mem_activeSet_simplex_iff.2 (by simp))
    rw [facetPairing_simplexNormal_some] at h
    simpa using h
  · -- The active normals are the `e_k` with `k ≠ p` and `-(e_1 + ⋯ + e_n)`.
    have hk (k : Fin n) (hk : k ≠ p) : w (Pi.single k 1) = 0 := by
      have h := hw' (some k) (some_mem_activeSet_simplex_iff.2 (by simp [hk]))
      rwa [facetPairing_simplexNormal_some] at h
    have hp : w (Pi.single p 1) = 0 := by
      have hsum := hw' none (none_mem_activeSet_simplex_iff.2 (by simp [Pi.single_apply]))
      rw [facetPairing_simplexNormal_none, neg_eq_zero,
        ← Finset.add_sum_erase _ _ (Finset.mem_univ p),
        Finset.sum_eq_zero fun k hk' ↦ hk k (Finset.ne_of_mem_erase hk'), add_zero] at hsum
      exact hsum
    refine ContinuousLinearMap.coe_injective <| (Pi.basisFun ℝ (Fin n)).ext fun k ↦ ?_
    by_cases hkp : k = p
    · simpa [hkp] using hp
    · simpa using hk k hkp

/-- Every facet of the standard simplex has a point lying on no other facet: the point with all
values `a / n` for the slanted facet, and for the facet `{x(e_p) = 0}` the point with value `0` on
`e_p` and `a / (2n)` on the other `e_k`. -/
private theorem exists_activeSet_simplex_eq_singleton (hn : n ≠ 0) (ha : 0 < a)
    (j : Option (Fin n)) :
    ∃ x ∈ facetPolyhedron ((Int.castAddHom ℝ).compLeft (Fin n)) (simplexNormal n)
      (simplexSupport n a), activeSet (facetPairing ((Int.castAddHom ℝ).compLeft (Fin n))
        (simplexNormal n)) (simplexSupport n a) x = {j} := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
  have hy (y : Fin n → ℝ) (l : Fin n) :
      (∑ k, y k • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n ↦ ℝ) k) (Pi.single l 1) =
        y l := by
    simp [Pi.single_apply]
  rcases j with _ | p
  · refine ⟨∑ k, (a / n) • ContinuousLinearMap.proj k, ?_, ?_⟩
    · rw [mem_facetPolyhedron_simplex_iff]
      simp only [hy (fun _ ↦ a / n), Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      exact ⟨fun _ ↦ by positivity, by field_simp; rfl⟩
    · ext m
      rcases m with _ | k
      · simp only [none_mem_activeSet_simplex_iff, hy (fun _ ↦ a / n), Finset.sum_const,
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp
        simp
      · simp only [some_mem_activeSet_simplex_iff, hy (fun _ ↦ a / n)]
        simp [ha.ne', hn]
  · let y : Fin n → ℝ := fun k ↦ if k = p then 0 else a / (2 * n)
    have hyk (k : Fin n) : y k ≤ a / (2 * n) := by
      simp only [y]
      split_ifs
      · positivity
      · exact le_rfl
    have hsum : ∑ k, y k < a := by
      calc ∑ k, y k ≤ ∑ _k : Fin n, a / (2 * n) := Finset.sum_le_sum fun k _ ↦ hyk k
        _ = a / 2 := by simp; field_simp
        _ < a := by linarith
    refine ⟨∑ k, y k • ContinuousLinearMap.proj k, ?_, ?_⟩
    · rw [mem_facetPolyhedron_simplex_iff]
      simp only [hy y]
      exact ⟨fun k ↦ by simp only [y]; split_ifs <;> positivity, hsum.le⟩
    · ext m
      rcases m with _ | k
      · simp only [none_mem_activeSet_simplex_iff, hy y]
        simpa using hsum.ne
      · simp only [some_mem_activeSet_simplex_iff, hy y]
        by_cases hk : k = p
        · simp [y, hk]
        · simp [y, hk, ha.ne', hn]

/-- **The standard simplex is a Delzant polytope.** For `n ≠ 0` and `a > 0`, the standard simplex
of size `a` in the lattice `ℤⁿ`, with facet normals `e_1, …, e_n, -(e_1 + ⋯ + e_n)`, is a Delzant
polytope. -/
theorem isDelzant_simplex (hn : n ≠ 0) (ha : 0 < a) :
    IsDelzant ((Int.castAddHom ℝ).compLeft (Fin n)) (simplexNormal n) (simplexSupport n a) := by
  refine ⟨?_, fun x hx ↦ ?_, exists_activeSet_simplex_eq_singleton hn ha⟩
  · -- Every value `x(e_k)` at a point of the simplex lies in `[0, a]`.
    obtain ⟨C, -, hC⟩ := (Pi.basisFun ℝ (Fin n)).exists_opNorm_le (F := ℝ)
    refine (Metric.isBounded_iff_subset_closedBall 0).2 ⟨C * a, fun x hx ↦ ?_⟩
    obtain ⟨h0, hsum⟩ := mem_facetPolyhedron_simplex_iff.1 hx
    rw [Metric.mem_closedBall, dist_zero_right]
    refine hC ha.le fun k ↦ ?_
    rw [Pi.basisFun_apply, Real.norm_of_nonneg (h0 k)]
    exact (Finset.single_le_sum (fun l _ ↦ h0 l) (Finset.mem_univ k)).trans hsum
  · -- All but one of the `n + 1` constraints are active, and those normals form a basis.
    obtain ⟨j, hj⟩ := exists_activeSet_simplex_eq_compl_singleton ha hx
    rw [isSmoothVertex_iff_span_eq_top, hj, Module.finrank_fin_fun]
    refine ⟨span_image_simplexNormal_compl_singleton j, ?_⟩
    have hcard := Set.ncard_add_ncard_compl {j}
    rw [ncard_singleton, Nat.card_eq_fintype_card, Fintype.card_option, Fintype.card_fin] at hcard
    omega

end TauCeti.Toric

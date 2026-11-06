/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.OrthogonalGroup.Basic
public import TauCeti.LinearAlgebra.Matrix.SpecialOrthogonalGroup.Reflection
public import TauCeti.RepresentationTheory.ClassicalGroups.BrauerGenerators.Orthogonal.Equivariance

/-!
# The commutant of the orthogonal group on the tensor square

Let `K` be a field and `V = Kⁿ` with its standard symmetric bilinear form. The Brauer algebra
`B₂(n)` on two strands has three diagrams: the identity, the crossing `σ` and the cap-cup `e`. Its
action `TauCeti.brauerActionOrth` on `V ⊗ V` sends them to the identity, the flip of the two tensor
factors, and the map `x ⊗ y ↦ ⟨x, y⟩ ∑ⱼ eⱼ ⊗ eⱼ`. These operators commute with the diagonal action
`g ↦ g ⊗ g` of the orthogonal group `O(n, K)` (`TauCeti.range_brauerActionOrth_le_centralizer`).
This file proves the converse on two strands when `2 ≠ 0` in `K` and the unit circle of `K` has a
point `(c, s)` with `c s ≠ 0`, in particular in characteristic zero: every operator on `V ⊗ V`
commuting with every `g ⊗ g` is a combination of the identity, `σ` and `e`, so the image of `B₂(n)`
is exactly the commutant of `O(n, K)`
(`TauCeti.range_brauerActionOrth_two_eq_centralizer_of_sq_add_sq_eq_one`, and
`TauCeti.range_brauerActionOrth_two_eq_centralizer` in characteristic zero). This is the
two-strand case of Brauer's description of the commutant of the orthogonal group on
`V^{⊗k}`, the first fundamental theorem of invariant theory for `O(n)`.

The proof is a computation with the matrix `M` of such an operator in the monomial basis
`eₐ ⊗ e_b`, using three kinds of orthogonal matrices.

* The diagonal reflections `diag(±1, …, ±1)` force `M` to vanish at every entry whose four indices
  do not pair off. An entry `M_{(a,b),(c,d)}` can only be nonzero when `a = b` and `c = d`, when
  `(a, b) = (c, d)`, or when `(a, b) = (d, c)`.
* The permutation matrices make `M` invariant under renaming the indices, so on each of these
  three patterns with two distinct indices `M` is constant. So `M = q • 1 + r • σ + p • e + y • Δ`,
  where `Δ` is the diagonal projection onto the span of the `eₐ ⊗ eₐ`.
* A reflection `g` with `g₀₀ g₀₁ ≠ 0` does not commute with `Δ`, so `y = 0`.

The last step needs such a reflection. Its entries come from a point `(c, s)` of the unit circle
with `c s ≠ 0`, which exists over every field of characteristic zero, for instance `(3/5, 4/5)`;
the diagonal reflections need `2 ≠ 0`. The unit-circle condition cannot be dropped: over `𝔽₃`
with `n = 2` the orthogonal group consists of the signed permutation matrices, and `Δ` commutes
with all of them without lying in the image of `B₂(2)`.

## Main results

* `TauCeti.eq_and_eq_or_eq_or_eq_and_eq_of_forall_update_mul_eq`: when `2 ≠ 0`, if every sign
  vector `Function.update 1 a (-1)` gives the same product of signs on two pairs of indices, the
  four indices pair off.
* `TauCeti.range_brauerActionOrth_two_eq_centralizer_of_sq_add_sq_eq_one`: over a field with
  `2 ≠ 0` and a point `(c, s)` of the unit circle with `c ≠ 0` and `s ≠ 0`, the image of the Brauer
  algebra `B₂(n)` is the commutant of the orthogonal group on `(Kⁿ)^{⊗2}`.
* `TauCeti.range_brauerActionOrth_two_eq_centralizer`: the same over every field of
  characteristic zero.

## References

* [R. Brauer, *On algebras which are connected with the semisimple continuous groups*][brauer1937],
  Annals of Mathematics 38 (1937), 857-872.
* R. Goodman and N. R. Wallach, *Symmetry, Representations, and Invariants*, Springer GTM 255
  (2009), Chapter 5 (the first fundamental theorem for the orthogonal group) and §10.1.
-/

public section

open Matrix

namespace TauCeti

/-- Let `2 ≠ 0` in `R`. If, for every `a`, the sign vector `Function.update 1 a (-1)` (the diagonal
of `TauCeti.orthogonalDiagonalReflection R a`) gives the same product of signs on the two pairs of
indices `(v 0, v 1)` and `(u 0, u 1)`, then the four indices pair off: the two pairs are both
constant, or equal, or swapped. -/
theorem eq_and_eq_or_eq_or_eq_and_eq_of_forall_update_mul_eq {R ι : Type*} [CommRing R]
    [DecidableEq ι] (h2 : (2 : R) ≠ 0) {v u : Fin 2 → ι}
    (h : ∀ a, Function.update (1 : ι → R) a (-1) (v 0) *
        Function.update (1 : ι → R) a (-1) (v 1) =
      Function.update (1 : ι → R) a (-1) (u 0) * Function.update (1 : ι → R) a (-1) (u 1)) :
    (v 0 = v 1 ∧ u 0 = u 1) ∨ v = u ∨ (u 0 = v 1 ∧ u 1 = v 0) := by
  have hne : (-1 : R) ≠ 1 := fun h ↦ h2 (by linear_combination -h)
  -- A product of two signs is `-1` exactly when one of the two labels is `a`.
  have key : ∀ a x y : ι, Function.update (1 : ι → R) a (-1) x *
      Function.update (1 : ι → R) a (-1) y = -1 ↔ (x = a ↔ y ≠ a) := fun a x y ↦ by
    simp only [Function.update_apply, Pi.one_apply]
    split_ifs <;> simp_all [hne.symm]
  rw [funext_iff, Fin.forall_fin_two]
  by_cases hv : v 0 = v 1
  · -- both signs of `v` agree, so those of `u` agree too: `u` is constant.
    refine .inl ⟨hv, by_contra fun hu ↦ ?_⟩
    have h' := h (u 0)
    rw [hv, ((key _ _ _).mpr ⟨fun _ ↦ Ne.symm hu, fun _ ↦ rfl⟩)] at h'
    have := (key (u 0) (v 1) (v 1)).mp h'
    tauto
  · -- each of `v 0` and `v 1` occurs exactly once in `u`.
    have h₀ := (key _ _ _).mp ((h (v 0)).symm.trans ((key _ _ _).mpr ⟨fun _ ↦ Ne.symm hv,
      fun _ ↦ rfl⟩))
    have h₁ := (key _ _ _).mp ((h (v 1)).symm.trans ((key _ _ _).mpr ⟨fun h ↦ absurd h hv,
      fun h ↦ absurd rfl h⟩))
    by_cases hu : u 0 = v 0
    · have hu1 : u 1 = v 1 := by_contra fun h ↦ hv (hu.symm.trans (h₁.mpr h))
      exact .inr (.inl ⟨hu.symm, hu1.symm⟩)
    · have hu1 : u 1 = v 0 := by_contra fun h ↦ hu (h₀.mpr h)
      exact .inr (.inr ⟨h₁.mpr fun h ↦ hv (hu1.symm.trans h), hu1⟩)

variable {K : Type*} [Field K]

variable {n : ℕ} {M : Matrix (Fin 2 → Fin n) (Fin 2 → Fin n) K}

/-- **Sign constraints.** A matrix commuting with the Kronecker squares of the diagonal reflections
vanishes at every entry whose indices do not pair off. -/
private theorem eq_and_eq_or_eq_or_eq_and_eq_of_apply_ne_zero (h2 : (2 : K) ≠ 0)
    (hM : ∀ g : Matrix.orthogonalGroup (Fin n) K,
      M * (g : Matrix (Fin n) (Fin n) K).kroneckerPower (Fin 2) =
        (g : Matrix (Fin n) (Fin n) K).kroneckerPower (Fin 2) * M)
    {v u : Fin 2 → Fin n} (hvu : M v u ≠ 0) :
    (v 0 = v 1 ∧ u 0 = u 1) ∨ v = u ∨ (u 0 = v 1 ∧ u 1 = v 0) := by
  refine eq_and_eq_or_eq_or_eq_and_eq_of_forall_update_mul_eq h2 fun a ↦ ?_
  have h := congrFun (congrFun (hM (orthogonalDiagonalReflection K a)) v) u
  simp only [coe_orthogonalDiagonalReflection, kroneckerPower_diagonal, mul_diagonal,
    diagonal_mul, Fin.prod_univ_two] at h
  exact (mul_left_cancel₀ hvu (h.trans (mul_comm _ _))).symm

/-- **Permutation invariance.** A matrix commuting with the Kronecker squares of the permutation
matrices is invariant under renaming the indices. -/
private theorem apply_comp_perm_eq
    (hM : ∀ g : Matrix.orthogonalGroup (Fin n) K,
      M * (g : Matrix (Fin n) (Fin n) K).kroneckerPower (Fin 2) =
        (g : Matrix (Fin n) (Fin n) K).kroneckerPower (Fin 2) * M)
    (σ : Equiv.Perm (Fin n)) (v u : Fin 2 → Fin n) :
    M (fun i ↦ σ (v i)) (fun i ↦ σ (u i)) = M v u := by
  have h := hM ⟨_, permMatrix_mem_orthogonalGroup K σ⟩
  simp only [kroneckerPower_toMatrix_toPEquiv, PEquiv.mul_toMatrix_toPEquiv,
    PEquiv.toMatrix_toPEquiv_mul] at h
  have h' := (congrFun (congrFun h v) (Equiv.piCongrRight (fun _ ↦ σ) u)).symm
  have hpi (w : Fin 2 → Fin n) : Equiv.piCongrRight (fun _ ↦ σ) w = fun i ↦ σ (w i) :=
    funext (Equiv.piCongrRight_apply _ w)
  simp only [submatrix_apply, Equiv.symm_apply_apply, id_eq] at h'
  simpa only [hpi] using h'

/-- Any two ordered pairs of distinct indices are related by a permutation. -/
private theorem exists_perm_apply_eq_of_ne {a b : Fin n} (hab : a ≠ b) (c d : Fin n)
    (hcd : c ≠ d) : ∃ σ : Equiv.Perm (Fin n), σ a = c ∧ σ b = d :=
  (exists_pair_perm_fixed (s := ∅) hab hcd (by simp) (by simp) (by simp) (by simp)).imp
    fun _ h ↦ h.2

/-- A matrix commuting with the Kronecker squares of the permutation matrices takes the same value
at two pairs of index patterns related by a common renaming of the indices. -/
private theorem apply_eq_apply_of_perm_apply
    (hM : ∀ g : Matrix.orthogonalGroup (Fin n) K,
      M * (g : Matrix (Fin n) (Fin n) K).kroneckerPower (Fin 2) =
        (g : Matrix (Fin n) (Fin n) K).kroneckerPower (Fin 2) * M)
    (σ : Equiv.Perm (Fin n)) {v u w z : Fin 2 → Fin n} (hv : ∀ i, σ (w i) = v i)
    (hu : ∀ i, σ (z i) = u i) : M v u = M w z := by
  rw [← apply_comp_perm_eq hM σ w z, funext hv, funext hu]

/-- The diagonal projection of `(Kⁿ)^{⊗2}` onto the span of the basis tensors `eₐ ⊗ eₐ`. -/
private abbrev diagProj (K : Type*) [Field K] (n : ℕ) : Matrix (Fin 2 → Fin n) (Fin 2 → Fin n) K :=
  diagonal fun v ↦ if v 0 = v 1 then 1 else 0

/-- **Sign and permutation constraints.** With two distinct coordinates `a₀ ≠ a₁`, a matrix
commuting with the Kronecker squares of all orthogonal matrices is a combination of the matrices of
the three Brauer diagrams on two strands and of the diagonal projection onto the span of the
`eₐ ⊗ eₐ`. -/
private theorem exists_eq_add_smul_diagProj (h2 : (2 : K) ≠ 0) {a₀ a₁ : Fin n} (ha : a₀ ≠ a₁)
    (hM : ∀ g : Matrix.orthogonalGroup (Fin n) K,
      M * (g : Matrix (Fin n) (Fin n) K).kroneckerPower (Fin 2) =
        (g : Matrix (Fin n) (Fin n) K).kroneckerPower (Fin 2) * M) :
    ∃ q r p y : K, M = q • (permToBrauer 1).orthogonalActionMatrix K (Fin n) +
      r • (permToBrauer (Equiv.swap (0 : Fin 2) 1)).orthogonalActionMatrix K (Fin n) +
      p • (capCup (0 : Fin 2) 1).orthogonalActionMatrix K (Fin n) + y • diagProj K n := by
  have htrans := exists_perm_apply_eq_of_ne ha
  have hmove := @apply_eq_apply_of_perm_apply _ _ _ _ hM
  -- The value of `M` on each pattern of indices is its value at a pattern built from `a₀, a₁`.
  set x := M ![a₀, a₀] ![a₀, a₀]
  set p := M ![a₀, a₀] ![a₁, a₁]
  set q := M ![a₀, a₁] ![a₀, a₁]
  set r := M ![a₀, a₁] ![a₁, a₀]
  refine ⟨q, r, p, x - p - q - r, ?_⟩
  ext v u
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, diagonal_apply,
    BrauerDiagram.orthogonalActionMatrix_permToBrauer_one, Matrix.one_apply,
    BrauerDiagram.orthogonalActionMatrix_apply, BrauerDiagram.isConstantOnArcs_permToBrauer_iff,
    BrauerDiagram.isConstantOnArcs_capCup_iff Fin.zero_ne_one, Fin.forall_fin_two, funext_iff]
  simp only [Equiv.swap_apply_left, Equiv.swap_apply_right, ne_eq]
  have hzero (h : ¬((v 0 = v 1 ∧ u 0 = u 1) ∨ v = u ∨ (u 0 = v 1 ∧ u 1 = v 0))) :
      M v u = 0 := by_contra fun h' ↦ h (eq_and_eq_or_eq_or_eq_and_eq_of_apply_ne_zero h2 hM h')
  rw [funext_iff, Fin.forall_fin_two] at hzero
  by_cases hv : v 0 = v 1
  · by_cases hu : u 0 = u 1
    · by_cases hvu : v 0 = u 0
      · -- all four indices agree
        have hval : M v u = x := hmove (Equiv.swap a₀ (v 0))
          (by simp [Fin.forall_fin_two, hv]) (by simp [Fin.forall_fin_two, ← hvu, ← hu])
        rw [hval]
        grind
      · -- `v` and `u` are constant with distinct values
        obtain ⟨σ, hσ₀, hσ₁⟩ := htrans _ _ hvu
        have hval : M v u = p := hmove σ (by simp [Fin.forall_fin_two, hσ₀, hv])
          (by simp [Fin.forall_fin_two, hσ₁, hu])
        rw [hval]
        grind
    · -- `v` is constant and `u` is not: the entry vanishes
      rw [hzero (by grind)]
      grind
  · by_cases hvu : v 0 = u 0 ∧ v 1 = u 1
    · -- `v = u` with distinct indices
      obtain ⟨σ, hσ₀, hσ₁⟩ := htrans _ _ hv
      have hval : M v u = q := hmove σ (by simp [Fin.forall_fin_two, hσ₀, hσ₁])
        (by simp [Fin.forall_fin_two, ← hvu.1, ← hvu.2, hσ₀, hσ₁])
      rw [hval]
      grind
    · by_cases hsw : v 1 = u 0 ∧ v 0 = u 1
      · -- `u` is `v` with its indices swapped
        obtain ⟨σ, hσ₀, hσ₁⟩ := htrans _ _ hv
        have hval : M v u = r := hmove σ (by simp [Fin.forall_fin_two, hσ₀, hσ₁])
          (by simp [Fin.forall_fin_two, hσ₀, hσ₁, hsw])
        rw [hval]
        grind
      · -- the indices do not pair off: the entry vanishes
        rw [hzero (by grind)]
        grind

/-- **A reflection separates the diagonal projection.** If `M = N + y • Δ`, where `M` and `N` both
commute with the Kronecker squares of all orthogonal matrices, then `y = 0`: a reflection `g` with
`g₀₀ = c` and `g₀₁ = s` has `(Δ (g ⊗ g) - (g ⊗ g) Δ)_{(0,0),(0,1)} = c s ≠ 0`. -/
private theorem eq_zero_of_eq_add_smul_diagProj {c s : K} (hcs : c ^ 2 + s ^ 2 = 1)
    (hc : c ≠ 0) (hs : s ≠ 0) (hn : 2 ≤ n)
    (hM : ∀ g : Matrix.orthogonalGroup (Fin n) K,
      M * (g : Matrix (Fin n) (Fin n) K).kroneckerPower (Fin 2) =
        (g : Matrix (Fin n) (Fin n) K).kroneckerPower (Fin 2) * M)
    {N : Matrix (Fin 2 → Fin n) (Fin 2 → Fin n) K}
    (hN : ∀ g : Matrix.orthogonalGroup (Fin n) K,
      Commute N ((g : Matrix (Fin n) (Fin n) K).kroneckerPower (Fin 2)))
    {y : K} (hy : M = N + y • diagProj K n) : y = 0 := by
  set a₀ : Fin n := ⟨0, by omega⟩
  set a₁ : Fin n := ⟨1, by omega⟩
  have ha : a₀ ≠ a₁ := by simp [a₀, a₁, Fin.ext_iff]
  -- The reflection in `w = (1 - c) e₀ - s e₁` has `g₀₀ = c` and `g₀₁ = s`.
  have h1c : 1 - c ≠ 0 := fun h ↦ hs <| pow_eq_zero_iff two_ne_zero |>.mp <| by
    linear_combination hcs + (1 + c) * h
  set w : Fin n → K := Pi.single a₀ (1 - c) - Pi.single a₁ s
  have hw : (1 - c)⁻¹ * (w ⬝ᵥ w) = 2 := by
    have : w ⬝ᵥ w = (1 - c) ^ 2 + s ^ 2 := by
      simp [w, dotProduct_sub, ha, Ne.symm ha]
      ring
    rw [this]
    field_simp
    linear_combination hcs
  set g : Matrix.orthogonalGroup (Fin n) K :=
    ⟨reflectionMatrix w (1 - c)⁻¹, reflectionMatrix_mem_orthogonalGroup hw⟩
  have hg₀₀ : (g : Matrix (Fin n) (Fin n) K) a₀ a₀ = c := by
    simp [g, w, ha]
    field_simp
    ring
  have hg₀₁ : (g : Matrix (Fin n) (Fin n) K) a₀ a₁ = s := by
    simp [g, w, ha, Ne.symm ha]
    field_simp
  -- So `y • Δ` commutes with `g ⊗ g`, and comparing one entry gives `y * (c * s) = 0`.
  have h := hM g
  rw [hy, add_mul, mul_add, (hN g).eq, smul_mul_assoc, mul_smul_comm] at h
  have h' := congrFun (congrFun
    (add_left_cancel (G := Matrix (Fin 2 → Fin n) (Fin 2 → Fin n) K) h) ![a₀, a₀]) ![a₀, a₁]
  simp only [Matrix.smul_apply, smul_eq_mul, diagonal_mul, mul_diagonal, kroneckerPower_apply,
    Fin.prod_univ_two] at h'
  simpa [hg₀₀, hg₀₁, ha, hc, hs] using h'

/-- **The commutant on two strands, at the level of matrices.** Over a field with `2 ≠ 0` and a
point `(c, s)` of the unit circle with `c ≠ 0` and `s ≠ 0`, a matrix commuting with the Kronecker
squares of all orthogonal matrices is a combination of the matrices of the three Brauer diagrams on
two strands. -/
private theorem exists_eq_smul_add_smul_add_smul (h2 : (2 : K) ≠ 0) {c s : K}
    (hcs : c ^ 2 + s ^ 2 = 1) (hc : c ≠ 0) (hs : s ≠ 0)
    (hM : ∀ g : Matrix.orthogonalGroup (Fin n) K,
      M * (g : Matrix (Fin n) (Fin n) K).kroneckerPower (Fin 2) =
        (g : Matrix (Fin n) (Fin n) K).kroneckerPower (Fin 2) * M) :
    ∃ q r p : K, M = q • (permToBrauer 1).orthogonalActionMatrix K (Fin n) +
      r • (permToBrauer (Equiv.swap (0 : Fin 2) 1)).orthogonalActionMatrix K (Fin n) +
      p • (capCup (0 : Fin 2) 1).orthogonalActionMatrix K (Fin n) := by
  rcases lt_or_ge n 2 with hn | hn
  · -- With at most one coordinate there is at most one index, and `M` is a scalar.
    have : Subsingleton (Fin 2 → Fin n) := by
      have : Subsingleton (Fin n) := Fin.subsingleton_iff_le_one.mpr (by omega)
      infer_instance
    refine ⟨M.trace, 0, 0, ?_⟩
    ext v u
    obtain rfl := Subsingleton.elim v u
    simp [trace, Fintype.sum_subsingleton _ v]
  obtain ⟨q, r, p, y, hy⟩ := exists_eq_add_smul_diagProj h2
    (a₀ := ⟨0, by omega⟩) (a₁ := ⟨1, by omega⟩) (by simp [Fin.ext_iff]) hM
  refine ⟨q, r, p, ?_⟩
  -- The three diagram matrices commute with every `g ⊗ g`, so the coefficient of `Δ` vanishes.
  have hN (g : Matrix.orthogonalGroup (Fin n) K) := fun D ↦
    BrauerDiagram.commute_orthogonalActionMatrix_kroneckerPower (R := K) (ι := Fin n) (k := 2) D
      ((mem_orthogonalGroup_iff' (Fin n) K).mp g.2)
  rw [hy, eq_zero_of_eq_add_smul_diagProj hcs hc hs hn hM
    (fun g ↦ (((hN g _).smul_left q).add_left ((hN g _).smul_left r)).add_left
      ((hN g _).smul_left p)) hy, zero_smul, add_zero]

variable (K) in
/-- **Brauer duality on the tensor square.** Over a field `K` with `2 ≠ 0` that has a point
`(c, s)` of the unit circle with `c ≠ 0` and `s ≠ 0`, the image of the Brauer algebra `B₂(n)` in
the endomorphisms of `(Kⁿ)^{⊗2}` is the commutant of the diagonal action of the orthogonal group:
an operator commuting with every `g ⊗ g` is a combination of the identity, the flip of the two
tensor factors and the cup-cap generator. -/
theorem range_brauerActionOrth_two_eq_centralizer_of_sq_add_sq_eq_one (n : ℕ) (h2 : (2 : K) ≠ 0)
    {c s : K} (hcs : c ^ 2 + s ^ 2 = 1) (hc : c ≠ 0) (hs : s ≠ 0) :
    (brauerActionOrth K n 2).range =
      Subalgebra.centralizer K (Set.range ((stdOrthogonalRep K n).tensorPower 2)) := by
  refine le_antisymm (range_brauerActionOrth_le_centralizer K n 2) fun T hT ↦ ?_
  set b := tensorPowerBasis K n 2
  -- The matrix of `T` commutes with the Kronecker square of every orthogonal matrix.
  have hM (g : Matrix.orthogonalGroup (Fin n) K) :
      LinearMap.toMatrix b b T * (g : Matrix (Fin n) (Fin n) K).kroneckerPower (Fin 2) =
        (g : Matrix (Fin n) (Fin n) K).kroneckerPower (Fin 2) * LinearMap.toMatrix b b T := by
    rw [Subalgebra.mem_centralizer_iff] at hT
    have h := congrArg (LinearMap.toMatrix b b) (hT _ ⟨g, rfl⟩)
    rw [Representation.tensorPower_apply] at h
    simp only [stdOrthogonalRep_apply, LinearMap.toMatrix_mul, b,
      Matrix.toMatrix_piTensorProductMap_tensorPowerBasis] at h
    exact h.symm
  obtain ⟨q, r, p, hqrp⟩ := exists_eq_smul_add_smul_add_smul h2 hcs hc hs hM
  refine ⟨q • BrauerAlgebra.of (permToBrauer 1) +
    r • BrauerAlgebra.of (permToBrauer (Equiv.swap (0 : Fin 2) 1)) +
      p • BrauerAlgebra.of (capCup (0 : Fin 2) 1), ?_⟩
  rw [← Matrix.toLin_toMatrix b b T, hqrp]
  simp [b, brauerActionOrth_of]

variable (K) in
/-- **Brauer duality on the tensor square in characteristic zero.** Over a field of
characteristic zero, the image of the Brauer algebra `B₂(n)` in the endomorphisms of `(Kⁿ)^{⊗2}`
is the commutant of the diagonal action of the orthogonal group. -/
theorem range_brauerActionOrth_two_eq_centralizer [CharZero K] (n : ℕ) :
    (brauerActionOrth K n 2).range =
      Subalgebra.centralizer K (Set.range ((stdOrthogonalRep K n).tensorPower 2)) :=
  range_brauerActionOrth_two_eq_centralizer_of_sq_add_sq_eq_one K n two_ne_zero
    (c := 3 / 5) (s := 4 / 5) (by norm_num) (by norm_num) (by norm_num)

end TauCeti

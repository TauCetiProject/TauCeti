/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Pi
public import TauCeti.Algebra.TypeAHeckeAlgebra.JucysMurphy.Content
public import TauCeti.Algebra.TypeAHeckeAlgebra.JucysMurphy.Finite
public import TauCeti.Combinatorics.Young.StandardTableau.Content

/-!
# Seminormal representations of the type-A Hecke algebra

Let `K` be a field, `q : Kˣ`, `Q = q ^ 2` and `g_i = q T_i`, so that `(g_i - Q) (g_i + 1) = 0`. For
a Young diagram `μ` with `n` cells, this file constructs Hoefsmit's seminormal representation
`TauCeti.TypeAHeckeAlgebra.seminormalRep` of `H_n(q) = TypeAHeckeAlgebra K q n` on the functions
on the standard Young tableaux of shape `μ`, with basis the vectors `v_U = Pi.single U 1`. Labels
start at `0`, and `T q i` exchanges the labels `i` and `i + 1`. For a standard tableau `U` let
`d = content (i + 1) - content i` be the *axial distance* of these labels and `s_i U` the tableau
with them exchanged (`TauCeti.StandardYoungTableau.swap`). Then

* `g_i v_U = Q v_U` if `d = 1`, that is, `i + 1` lies immediately right of `i`;
* `g_i v_U = -v_U` if `d = -1`, that is, `i + 1` lies immediately below `i`;
* `g_i v_U = A(d) v_U + v_(s_i U)` if `d > 1`;
* `g_i v_U = A(d) v_U + (Q + A(d) A(-d)) v_(s_i U)` if `d < -1`,

where `A(d) = Q ^ d / [d]_Q` is `TauCeti.TypeAHeckeAlgebra.seminormalDiag`, with `[d]_Q` the
additive content, and `Q + A(d) A(-d) = Q [d + 1]_Q [d - 1]_Q / [d]_Q ^ 2`. The off-diagonal
coefficients are packaged as `TauCeti.TypeAHeckeAlgebra.seminormalOffDiag`. At `Q = 1` this is
Young's seminormal form of the symmetric group, with coefficients `1 / d` and `1 - 1 / d ^ 2`. The
construction needs the additive contents `[d]_Q`, `0 < d < n`, to be nonzero; this is implied by
the split-semisimplicity criterion and includes `Q = 1` in characteristic zero.

The vectors `v_U` diagonalize the Jucys–Murphy elements: `J_i v_U = Q ^ content i * v_U`, where
`content i` is the column minus the row of the label `i` in `U`. Irreducibility of these modules
and their comparison with other constructions of the Specht modules are not treated here.

## Main definitions

* `TauCeti.TypeAHeckeAlgebra.seminormalDiag`, `TauCeti.TypeAHeckeAlgebra.seminormalOffDiag`: the
  coefficients of the seminormal form as functions of the axial distance.
* `TauCeti.TypeAHeckeAlgebra.seminormalRep`: the seminormal representation.

## Main results

* `TauCeti.TypeAHeckeAlgebra.seminormalRep_T_apply`: the action of a generator.
* `TauCeti.TypeAHeckeAlgebra.seminormalRep_T_single_of_abs_ne_one` and
  `TauCeti.TypeAHeckeAlgebra.seminormalRep_T_single_of_abs_eq_one`: the action of a generator on
  a basis vector.
* `TauCeti.TypeAHeckeAlgebra.seminormalRep_jucysMurphy_single`: the basis vectors are
  eigenvectors of the Jucys–Murphy elements, with eigenvalues `Q ^ content`.

## Implementation notes

The operators are first defined, in the pull form `(g_i φ) t = A(d) φ t + E(d) φ (s_i t)`, on the
functions on *all* tableaux of shape `μ`, where exchanging two labels is always defined. Extension
by zero from the standard tableaux intertwines them with the operators on standard tableaux,
because the off-diagonal coefficient vanishes when `|d| = 1`, which is exactly when exchanging the
labels of a standard tableau does not give a standard tableau. The relations are then checked at
each standard tableau, where the contents of nearby labels are distinct: the braid relation
reduces to identities among the coefficients at the three contents of the labels `i`, `i + 1`,
`i + 2`, which follow from the cocycle identity `[a + b]_Q = [a]_Q + Q ^ a [b]_Q`.

## References

* P. N. Hoefsmit, *Representations of Hecke algebras of finite groups with BN-pairs of classical
  type*, PhD thesis, University of British Columbia (1974).
* A. Ram, *Seminormal representations of Weyl groups and Iwahori-Hecke algebras*, Proc. London
  Math. Soc. 75 (1997), 99–133.
* H. Wenzl, *Hecke algebras of type A_n and subfactors*, Invent. Math. 92 (1988), 349–383,
  for the tableau representations.
-/

public section

namespace TauCeti.TypeAHeckeAlgebra

open YoungTableau

variable {K : Type*} [Field K]

/-! ### The seminormal coefficients -/

section Coefficients

/-- The diagonal coefficient `Q ^ d / [d]_Q` of the seminormal form at axial distance `d`, with
`[d]_Q` the additive content: the coefficient of a tableau vector in its image under `g = q T`.
At `Q = 1` it is Young's coefficient `1 / d`. -/
def seminormalDiag (Q : K) (d : ℤ) : K :=
  Q ^ d / additiveContent Q d

theorem seminormalDiag_def (Q : K) (d : ℤ) : seminormalDiag Q d = Q ^ d / additiveContent Q d :=
  (rfl)

/-- The off-diagonal coefficient of the seminormal form: `g = q T` sends the vector of a tableau
of axial distance `-d` to `seminormalDiag Q (-d)` times itself plus `seminormalOffDiag Q d` times
the vector of the exchanged tableau, whose axial distance is `d`. It is `1` for `d < -1`,
`Q + seminormalDiag Q d * seminormalDiag Q (-d)` for `1 < d`, and `0` for `|d| ≤ 1`, where the
exchanged tableau is not standard. -/
def seminormalOffDiag (Q : K) (d : ℤ) : K :=
  if d < -1 then 1 else if 1 < d then Q + seminormalDiag Q d * seminormalDiag Q (-d) else 0

variable {Q : K}

/-- At axial distance `1`, the label `k + 1` immediately to the right of `k`, the diagonal
coefficient is `Q`. -/
@[simp]
theorem seminormalDiag_one : seminormalDiag Q 1 = Q := by
  rw [seminormalDiag, additiveContent_one_right, zpow_one, div_one]

/-- At axial distance `-1`, the label `k + 1` immediately below `k`, the diagonal coefficient
is `-1`. -/
@[simp]
theorem seminormalDiag_neg_one (hQ : Q ≠ 0) : seminormalDiag Q (-1) = -1 := by
  rw [seminormalDiag, additiveContent_neg hQ, additiveContent_one_right, mul_one, div_neg,
    div_self (zpow_ne_zero _ hQ)]

/-- The diagonal coefficient at a negative axial distance is `-[d]_Q⁻¹`. -/
theorem seminormalDiag_neg (hQ : Q ≠ 0) (d : ℤ) :
    seminormalDiag Q (-d) = -(additiveContent Q d)⁻¹ := by
  have h := zpow_ne_zero (-d) hQ
  rw [seminormalDiag, additiveContent_neg hQ]
  by_cases hd : additiveContent Q d = 0
  · simp [hd]
  · field_simp

/-- The two diagonal coefficients at opposite axial distances add up to the trace `Q - 1` of
`g` on a two-dimensional block. -/
theorem seminormalDiag_add_seminormalDiag_neg (hQ : Q ≠ 0) {d : ℤ}
    (hd : additiveContent Q d ≠ 0) : seminormalDiag Q d + seminormalDiag Q (-d) = Q - 1 := by
  have h := sub_one_mul_additiveContent hQ d
  rw [seminormalDiag_neg hQ, seminormalDiag]
  field_simp
  linear_combination -h

/-- The diagonal coefficients at opposite axial distances are related by
`seminormalDiag Q d + seminormalDiag Q (-d) * Q ^ d = 0`; this makes the vector of a tableau an
eigenvector of the Jucys–Murphy elements. -/
private theorem seminormalDiag_add_seminormalDiag_neg_mul_zpow (hQ : Q ≠ 0) (d : ℤ) :
    seminormalDiag Q d + seminormalDiag Q (-d) * Q ^ d = 0 := by
  rw [seminormalDiag_neg hQ, seminormalDiag]
  ring

/-- The off-diagonal coefficient vanishes when the axial distance is at most `1` in absolute
value. -/
theorem seminormalOffDiag_of_abs_le_one {d : ℤ} (hd : |d| ≤ 1) : seminormalOffDiag Q d = 0 := by
  rw [abs_le] at hd
  simp only [seminormalOffDiag]
  split_ifs <;> first | rfl | omega

/-- The off-diagonal coefficient is `1` at axial distances below `-1`. -/
theorem seminormalOffDiag_of_lt_neg_one {d : ℤ} (hd : d < -1) : seminormalOffDiag Q d = 1 := by
  rw [seminormalOffDiag, ite_eq_left hd]

/-- The off-diagonal coefficient at axial distances above `1`. -/
theorem seminormalOffDiag_of_one_lt {d : ℤ} (hd : 1 < d) :
    seminormalOffDiag Q d = Q + seminormalDiag Q d * seminormalDiag Q (-d) := by
  rw [seminormalOffDiag, ite_eq_right (by omega), ite_eq_left hd]

/-- The product of the off-diagonal coefficients at opposite axial distances is
`Q + seminormalDiag Q d * seminormalDiag Q (-d)`, the value forced by the determinant `-Q` of
`g` on a two-dimensional block. At `d = ±1` both sides vanish. -/
theorem seminormalOffDiag_mul_seminormalOffDiag_neg {d : ℤ} (hd : d ≠ 0) :
    seminormalOffDiag Q d * seminormalOffDiag Q (-d) =
      Q + seminormalDiag Q d * seminormalDiag Q (-d) := by
  -- at `d = ±1` both sides vanish: `Q + Q * (-1) = 0`, and at `Q = 0` every term is `0`
  have h₀ : Q + seminormalDiag Q 1 * seminormalDiag Q (-1) = 0 := by
    rcases eq_or_ne Q 0 with rfl | hQ
    · simp [seminormalDiag]
    · rw [seminormalDiag_one, seminormalDiag_neg_one hQ]
      ring
  rcases eq_or_ne d 1 with rfl | h₁
  · rw [seminormalOffDiag_of_abs_le_one (by norm_num), zero_mul, h₀]
  rcases eq_or_ne d (-1) with rfl | h₂
  · rw [seminormalOffDiag_of_abs_le_one (by norm_num), zero_mul, neg_neg, mul_comm, h₀]
  simp only [seminormalOffDiag, neg_neg]
  split_ifs <;> first | omega | ring

/-- The identity among diagonal coefficients behind the braid relation: for axial distances
`u`, `v` and `v + u`, it reduces to the cocycle identity `[v + u]_Q = [v]_Q + Q ^ v * [u]_Q`. -/
private theorem diag_braid_core (hQ : Q ≠ 0) {u v : ℤ} (hu : additiveContent Q u ≠ 0)
    (hv : additiveContent Q v ≠ 0) (huv : additiveContent Q (v + u) ≠ 0) :
    seminormalDiag Q u * seminormalDiag Q v + seminormalDiag Q (v + u) * seminormalDiag Q (-u) =
      seminormalDiag Q v * seminormalDiag Q (v + u) := by
  rw [seminormalDiag_neg hQ]
  simp only [seminormalDiag]
  rw [additiveContent_add hQ v u] at huv ⊢
  rw [zpow_add₀ hQ]
  have hu' : Q ^ u ≠ 0 := zpow_ne_zero _ hQ
  have hv' : Q ^ v ≠ 0 := zpow_ne_zero _ hQ
  have huv' : additiveContent Q v + additiveContent Q u * Q ^ v ≠ 0 := by rwa [mul_comm] at huv
  field_simp
  ring

/-- Two-point form of `TauCeti.TypeAHeckeAlgebra.diag_braid_core`, for contents `x`, `y`, `z`. -/
private theorem diag_braid_left (hQ : Q ≠ 0) {x y z : ℤ} (hxy : additiveContent Q (y - x) ≠ 0)
    (hyz : additiveContent Q (z - y) ≠ 0) (hxz : additiveContent Q (z - x) ≠ 0) :
    seminormalDiag Q (y - x) * seminormalDiag Q (z - y) +
        seminormalDiag Q (z - x) * seminormalDiag Q (x - y) =
      seminormalDiag Q (z - y) * seminormalDiag Q (z - x) := by
  have h := diag_braid_core hQ (u := y - x) (v := z - y) hxy hyz (by rwa [sub_add_sub_cancel])
  rwa [sub_add_sub_cancel, neg_sub] at h

/-- The mirror image of `TauCeti.TypeAHeckeAlgebra.diag_braid_left`. -/
private theorem diag_braid_right (hQ : Q ≠ 0) {x y z : ℤ} (hxy : additiveContent Q (y - x) ≠ 0)
    (hyz : additiveContent Q (z - y) ≠ 0) (hxz : additiveContent Q (z - x) ≠ 0) :
    seminormalDiag Q (z - y) * seminormalDiag Q (y - x) +
        seminormalDiag Q (z - x) * seminormalDiag Q (y - z) =
      seminormalDiag Q (y - x) * seminormalDiag Q (z - x) := by
  have h := diag_braid_core hQ (u := z - y) (v := y - x) hyz hxy
    (by rwa [add_comm, sub_add_sub_cancel])
  rwa [add_comm (y - x), sub_add_sub_cancel, neg_sub] at h

end Coefficients

/-! ### The seminormal operators on all tableaux -/

section Operators

variable {μ : YoungDiagram}

/-- The transposition of the labels `k` and `k + 1`. -/
private abbrev labelSwap (k : ℕ) (hk : k + 1 < μ.card) : Equiv.Perm (Fin μ.card) :=
  Equiv.swap ⟨k, by omega⟩ ⟨k + 1, hk⟩

/-- The seminormal operator of `g = q T_k` on functions on *all* tableaux, in pull form: the
value at `t` combines the values at `t` and at `t` with `k` and `k + 1` exchanged. -/
private def seminormalAux (Q : K) (k : ℕ) (hk : k + 1 < μ.card) :
    Module.End K (YoungTableau μ → K) :=
  LinearMap.mulLeft K (fun t => seminormalDiag Q (axialDistance t k hk)) +
    LinearMap.mulLeft K (fun t => seminormalOffDiag Q (axialDistance t k hk)) ∘ₗ
      LinearMap.funLeft K K (relabel (labelSwap k hk))

private theorem seminormalAux_apply (Q : K) (k : ℕ) (hk : k + 1 < μ.card)
    (φ : YoungTableau μ → K) (t : YoungTableau μ) :
    seminormalAux Q k hk φ t = seminormalDiag Q (axialDistance t k hk) * φ t +
      seminormalOffDiag Q (axialDistance t k hk) * φ (relabel (labelSwap k hk) t) := by
  rw [seminormalAux, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply,
    LinearMap.mulLeft_apply, Pi.add_apply, Pi.mul_apply, Pi.mul_apply, LinearMap.funLeft_apply]

variable (K) in
/-- Extension by zero from the standard tableaux to all tableaux. -/
private noncomputable abbrev extendSYT : (StandardYoungTableau μ → K) →ₗ[K] YoungTableau μ → K :=
  Function.ExtendByZero.linearMap K K StandardYoungTableau.toTableau

private theorem extendSYT_apply_toTableau (ψ : StandardYoungTableau μ → K)
    (T : StandardYoungTableau μ) : extendSYT K ψ T.toTableau = ψ T := by
  rw [Function.ExtendByZero.linearMap_apply,
    StandardYoungTableau.toTableau_injective.extend_apply]

private theorem extendSYT_apply_of_not_exists (ψ : StandardYoungTableau μ → K)
    {u : YoungTableau μ} (hu : ¬∃ T : StandardYoungTableau μ, T.toTableau = u) :
    extendSYT K ψ u = 0 := by
  rw [Function.ExtendByZero.linearMap_apply, Function.extend_apply' _ _ _ hu, Pi.zero_apply]

/-- The seminormal operator of `g = q T_k` on functions on the standard tableaux. -/
private noncomputable def seminormalGen (Q : K) (k : ℕ) (hk : k + 1 < μ.card) :
    Module.End K (StandardYoungTableau μ → K) :=
  LinearMap.funLeft K K StandardYoungTableau.toTableau ∘ₗ seminormalAux Q k hk ∘ₗ extendSYT K

private theorem seminormalGen_apply (Q : K) (k : ℕ) (hk : k + 1 < μ.card)
    (ψ : StandardYoungTableau μ → K) (T : StandardYoungTableau μ) :
    seminormalGen Q k hk ψ T = seminormalAux Q k hk (extendSYT K ψ) T.toTableau :=
  (rfl)

/-- Extension by zero intertwines the seminormal operators on standard tableaux and on all
tableaux. At a nonstandard tableau `u` whose exchange is the standard tableau `T`, the labels
`k` and `k + 1` lie next to each other in `T`, so the off-diagonal coefficient vanishes. -/
private theorem extendSYT_seminormalGen (Q : K) (k : ℕ) (hk : k + 1 < μ.card)
    (ψ : StandardYoungTableau μ → K) :
    extendSYT K (seminormalGen Q k hk ψ) = seminormalAux Q k hk (extendSYT K ψ) := by
  funext u
  by_cases hu : ∃ T : StandardYoungTableau μ, T.toTableau = u
  · obtain ⟨T, rfl⟩ := hu
    rw [extendSYT_apply_toTableau, seminormalGen_apply]
  rw [extendSYT_apply_of_not_exists _ hu, seminormalAux_apply, extendSYT_apply_of_not_exists _ hu,
    mul_zero, zero_add]
  by_cases hsu : ∃ T : StandardYoungTableau μ, T.toTableau = relabel (labelSwap k hk) u
  · obtain ⟨T, hT⟩ := hsu
    have hu' : u = relabel (labelSwap k hk) T.toTableau := by
      rw [hT, relabel_relabel, Equiv.swap_mul_self, relabel_one]
    have habs : |axialDistance T.toTableau k hk| = 1 := by
      by_contra h
      exact hu ⟨T.swap k hk h, (T.toTableau_swap k hk h).trans hu'.symm⟩
    rw [hu', axialDistance_relabel_swap, seminormalOffDiag_of_abs_le_one (by rw [abs_neg, habs]),
      zero_mul]
  · rw [extendSYT_apply_of_not_exists _ hsu, mul_zero]

variable {Q : K}

/-- The quadratic relation `g² = (Q - 1) g + Q` at a tableau of nonzero axial distance. -/
private theorem seminormalAux_sq_apply (hQ : Q ≠ 0) (k : ℕ) (hk : k + 1 < μ.card)
    (φ : YoungTableau μ → K) {t : YoungTableau μ}
    (hd : additiveContent Q (axialDistance t k hk) ≠ 0) :
    seminormalAux Q k hk (seminormalAux Q k hk φ) t =
      (Q - 1) * seminormalAux Q k hk φ t + Q * φ t := by
  have hd0 := ne_zero_of_additiveContent_ne_zero hd
  have h₁ := seminormalDiag_add_seminormalDiag_neg hQ hd
  have h₂ := seminormalOffDiag_mul_seminormalOffDiag_neg (Q := Q) hd0
  simp only [seminormalAux_apply, relabel_relabel, Equiv.swap_mul_self, relabel_one,
    axialDistance_relabel_swap]
  linear_combination (seminormalDiag Q (axialDistance t k hk) * φ t +
    seminormalOffDiag Q (axialDistance t k hk) * φ (relabel (labelSwap k hk) t)) * h₁ + φ t * h₂

private theorem labelSwap_apply_of_ne {k : ℕ} (hk : k + 1 < μ.card) {j : ℕ} (hj : j < μ.card)
    (h₁ : j ≠ k) (h₂ : j ≠ k + 1) : labelSwap k hk ⟨j, hj⟩ = ⟨j, hj⟩ :=
  Equiv.swap_apply_of_ne_of_ne (by rw [ne_eq, Fin.mk.injEq]; exact h₁)
    (by rw [ne_eq, Fin.mk.injEq]; exact h₂)

private theorem labelContent_relabel_labelSwap (t : YoungTableau μ) {k : ℕ} (hk : k + 1 < μ.card)
    (j : Fin μ.card) :
    labelContent (relabel (labelSwap k hk) t) j = labelContent t (labelSwap k hk j) := by
  rw [labelContent_relabel, Equiv.swap_inv]

/-- Exchanges of labels at distance at least two commute. -/
private theorem labelSwap_mul_comm {k l : ℕ} (hk : k + 1 < μ.card) (hl : l + 1 < μ.card)
    (hkl : k + 2 ≤ l) : labelSwap k hk * labelSwap l hl = labelSwap l hl * labelSwap k hk := by
  rw [Equiv.mul_swap_eq_swap_mul, labelSwap_apply_of_ne hk _ (by omega) (by omega),
    labelSwap_apply_of_ne hk _ (by omega) (by omega)]

/-- The braid relation among adjacent exchanges of labels: both sides exchange `k` and
`k + 2`. -/
private theorem labelSwap_braid {k : ℕ} (hk : k + 1 + 1 < μ.card) :
    labelSwap k (by omega) * (labelSwap (k + 1) hk * labelSwap k (by omega)) =
      labelSwap (k + 1) hk * (labelSwap k (by omega) * labelSwap (k + 1) hk) := by
  have hk₁ : k + 1 < μ.card := by omega
  have h₁ : labelSwap k hk₁ * labelSwap (k + 1) hk =
      Equiv.swap ⟨k, by omega⟩ ⟨k + 1 + 1, hk⟩ * labelSwap k hk₁ := by
    rw [Equiv.mul_swap_eq_swap_mul, Equiv.swap_apply_right,
      labelSwap_apply_of_ne hk₁ hk (by omega) (by omega)]
  have h₂ : labelSwap (k + 1) hk * labelSwap k hk₁ =
      Equiv.swap ⟨k, by omega⟩ ⟨k + 1 + 1, hk⟩ * labelSwap (k + 1) hk := by
    rw [Equiv.mul_swap_eq_swap_mul, Equiv.swap_apply_left,
      labelSwap_apply_of_ne hk (by omega) (by omega) (by omega)]
  rw [← mul_assoc, ← mul_assoc, h₁, h₂, mul_assoc, mul_assoc, Equiv.swap_mul_self,
    Equiv.swap_mul_self]

/-- Distant seminormal operators commute. -/
private theorem seminormalAux_comm_apply (Q : K) {k l : ℕ} (hk : k + 1 < μ.card)
    (hl : l + 1 < μ.card) (hkl : k + 2 ≤ l) (φ : YoungTableau μ → K) (t : YoungTableau μ) :
    seminormalAux Q k hk (seminormalAux Q l hl φ) t =
      seminormalAux Q l hl (seminormalAux Q k hk φ) t := by
  have h₁ : axialDistance (relabel (labelSwap l hl) t) k hk = axialDistance t k hk := by
    rw [axialDistance_def, labelContent_relabel_labelSwap, labelContent_relabel_labelSwap,
      labelSwap_apply_of_ne hl _ (by omega) (by omega),
      labelSwap_apply_of_ne hl _ (by omega) (by omega), axialDistance_def]
  have h₂ : axialDistance (relabel (labelSwap k hk) t) l hl = axialDistance t l hl := by
    rw [axialDistance_def, labelContent_relabel_labelSwap, labelContent_relabel_labelSwap,
      labelSwap_apply_of_ne hk _ (by omega) (by omega),
      labelSwap_apply_of_ne hk _ (by omega) (by omega), axialDistance_def]
  simp only [seminormalAux_apply, relabel_relabel, h₁, h₂, labelSwap_mul_comm hk hl hkl]
  ring

/-- The braid relation `g_k g_(k+1) g_k = g_(k+1) g_k g_(k+1)` at a tableau whose labels `k`,
`k + 1` and `k + 2` have contents with nonzero additive differences. -/
private theorem seminormalAux_braid_apply (hQ : Q ≠ 0) {k : ℕ} (hk : k + 1 + 1 < μ.card)
    (φ : YoungTableau μ → K) {t : YoungTableau μ}
    (hxy : additiveContent Q (labelContent t ⟨k + 1, by omega⟩ - labelContent t ⟨k, by omega⟩) ≠ 0)
    (hyz : additiveContent Q
      (labelContent t ⟨k + 1 + 1, hk⟩ - labelContent t ⟨k + 1, by omega⟩) ≠ 0)
    (hxz : additiveContent Q (labelContent t ⟨k + 1 + 1, hk⟩ - labelContent t ⟨k, by omega⟩) ≠ 0) :
    seminormalAux Q k (by omega)
        (seminormalAux Q (k + 1) hk (seminormalAux Q k (by omega) φ)) t =
      seminormalAux Q (k + 1) hk
        (seminormalAux Q k (by omega) (seminormalAux Q (k + 1) hk φ)) t := by
  have hk₁ : k + 1 < μ.card := by omega
  set x := labelContent t ⟨k, by omega⟩ with hx
  set y := labelContent t ⟨k + 1, hk₁⟩ with hy
  set z := labelContent t ⟨k + 1 + 1, hk⟩ with hz
  have hs : labelSwap k hk₁ ⟨k + 1 + 1, hk⟩ = ⟨k + 1 + 1, hk⟩ :=
    labelSwap_apply_of_ne hk₁ hk (by omega) (by omega)
  have hr : labelSwap (k + 1) hk ⟨k, by omega⟩ = ⟨k, by omega⟩ :=
    labelSwap_apply_of_ne hk (by omega) (by omega) (by omega)
  -- the axial distances at the tableaux met in both products, in terms of `x`, `y` and `z`
  have a₀ : axialDistance t k hk₁ = y - x := axialDistance_def t k hk₁
  have b₀ : axialDistance t (k + 1) hk = z - y := axialDistance_def t (k + 1) hk
  have a₁ : axialDistance (relabel (labelSwap k hk₁) t) k hk₁ = x - y := by
    rw [axialDistance_relabel_swap, a₀, neg_sub]
  have a₂ : axialDistance (relabel (labelSwap (k + 1) hk) t) k hk₁ = z - x := by
    simp only [axialDistance_def, labelContent_relabel_labelSwap, Equiv.swap_apply_left, hr, ← hx,
      ← hz]
  have a₃ : axialDistance (relabel (labelSwap (k + 1) hk * labelSwap k hk₁) t) k hk₁ = z - y := by
    simp only [axialDistance_def, labelContent_relabel, mul_inv_rev, Equiv.swap_inv,
      Equiv.Perm.mul_apply, Equiv.swap_apply_left, hs, hr, ← hy, ← hz]
  have b₁ : axialDistance (relabel (labelSwap k hk₁) t) (k + 1) hk = z - x := by
    simp only [axialDistance_def, labelContent_relabel_labelSwap, Equiv.swap_apply_right, hs, ← hx,
      ← hz]
  have b₂ : axialDistance (relabel (labelSwap (k + 1) hk) t) (k + 1) hk = y - z := by
    rw [axialDistance_relabel_swap, b₀, neg_sub]
  have b₃ : axialDistance (relabel (labelSwap k hk₁ * labelSwap (k + 1) hk) t) (k + 1) hk =
      y - x := by
    simp only [axialDistance_def, labelContent_relabel, mul_inv_rev, Equiv.swap_inv,
      Equiv.Perm.mul_apply, Equiv.swap_apply_right, hs, hr, ← hx, ← hy]
  have hB₁ := diag_braid_left hQ hxy hyz hxz
  have hB₂ := diag_braid_right hQ hxy hyz hxz
  have hE₁ := seminormalOffDiag_mul_seminormalOffDiag_neg (Q := Q)
    (ne_zero_of_additiveContent_ne_zero hxy)
  have hE₂ := seminormalOffDiag_mul_seminormalOffDiag_neg (Q := Q)
    (ne_zero_of_additiveContent_ne_zero hyz)
  rw [neg_sub] at hE₁ hE₂
  simp only [seminormalAux_apply, relabel_relabel, Equiv.swap_mul_self, relabel_one,
    a₀, a₁, a₂, a₃, b₀, b₁, b₂, b₃, labelSwap_braid hk]
  linear_combination φ t * (seminormalDiag Q (z - x) * hE₁ - seminormalDiag Q (z - x) * hE₂ +
      seminormalDiag Q (y - x) * hB₁ - seminormalDiag Q (z - y) * hB₂) +
    φ (relabel (labelSwap k hk₁) t) * seminormalOffDiag Q (y - x) * hB₁ -
    φ (relabel (labelSwap (k + 1) hk) t) * seminormalOffDiag Q (z - y) * hB₂

/-- Multiplication by `Q ^ labelContent t i` at the tableau `t`, the expected action of the
Jucys–Murphy element of strand `i`. -/
private def contentMul (Q : K) (i : Fin μ.card) : Module.End K (YoungTableau μ → K) :=
  LinearMap.mulLeft K (fun t => Q ^ labelContent t i)

private theorem contentMul_apply (Q : K) (i : Fin μ.card) (φ : YoungTableau μ → K)
    (t : YoungTableau μ) : contentMul Q i φ t = Q ^ labelContent t i * φ t := by
  rw [contentMul, LinearMap.mulLeft_apply, Pi.mul_apply]

/-- The Jucys–Murphy recursion `J_(k+1) = Q⁻¹ g_k J_k g_k` on a tableau vector: conjugating
multiplication by `Q ^ content k` with the seminormal operator of `g_k` gives `Q` times the
multiplication by `Q ^ content (k + 1)`. -/
private theorem seminormalAux_contentMul_seminormalAux_apply (hQ : Q ≠ 0) (k : ℕ)
    (hk : k + 1 < μ.card) (φ : YoungTableau μ → K) {t : YoungTableau μ}
    (hd : additiveContent Q (axialDistance t k hk) ≠ 0) :
    seminormalAux Q k hk (contentMul Q ⟨k, by omega⟩ (seminormalAux Q k hk φ)) t =
      Q * (Q ^ labelContent t ⟨k + 1, hk⟩ * φ t) := by
  have hd0 := ne_zero_of_additiveContent_ne_zero hd
  have hE := seminormalOffDiag_mul_seminormalOffDiag_neg (Q := Q) hd0
  have hA := seminormalDiag_add_seminormalDiag_neg_mul_zpow hQ (axialDistance t k hk)
  have hpow : Q ^ labelContent t ⟨k + 1, hk⟩ =
      Q ^ labelContent t ⟨k, by omega⟩ * Q ^ axialDistance t k hk := by
    rw [← zpow_add₀ hQ, axialDistance_def, add_sub_cancel]
  have hc :
      labelContent (relabel (labelSwap k hk) t) ⟨k, by omega⟩ = labelContent t ⟨k + 1, hk⟩ := by
    rw [labelContent_relabel_labelSwap, Equiv.swap_apply_left]
  simp only [seminormalAux_apply, contentMul_apply, relabel_relabel, Equiv.swap_mul_self,
    relabel_one, axialDistance_relabel_swap, hc, hpow]
  linear_combination Q ^ labelContent t ⟨k, by omega⟩ *
      (seminormalDiag Q (axialDistance t k hk) * φ t +
        seminormalOffDiag Q (axialDistance t k hk) * φ (relabel (labelSwap k hk) t)) * hA +
    Q ^ labelContent t ⟨k, by omega⟩ * Q ^ axialDistance t k hk * φ t * hE

end Operators

/-! ### The seminormal representation -/

section Representation

variable {μ : YoungDiagram} {Q : K}

/-- Under the hypothesis on `Q`, the additive content of the difference of the contents of two
labels of a standard tableau that differ by at most two is nonzero. -/
private theorem additiveContent_labelContent_sub_ne_zero (hQ : Q ≠ 0)
    (hμ : ∀ d : ℕ, 0 < d → d < μ.card → additiveContent Q d ≠ 0) (T : StandardYoungTableau μ)
    {a b : Fin μ.card} (hab : a < b) (hba : (b : ℕ) ≤ a + 2) :
    additiveContent Q (labelContent T.toTableau b - labelContent T.toTableau a) ≠ 0 := by
  have hne : labelContent T.toTableau b - labelContent T.toTableau a ≠ 0 :=
    sub_ne_zero.mpr (T.labelContent_ne_of_lt_of_le_add_two hab hba).symm
  have hlt : |labelContent T.toTableau b - labelContent T.toTableau a| < μ.card := by
    rw [labelContent_def, labelContent_def]
    exact YoungDiagram.abs_cellContent_sub_lt_card ((YoungDiagram.mem_cells _).mp
      (T.toTableau.symm b).2) ((YoungDiagram.mem_cells _).mp (T.toTableau.symm a).2)
  rw [abs_lt] at hlt
  rcases lt_or_gt_of_ne hne with h | h
  · obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (neg_nonneg.mpr h.le)
    rw [← neg_neg (labelContent T.toTableau b - labelContent T.toTableau a), hm, ne_eq,
      additiveContent_neg_eq_zero_iff hQ]
    exact hμ m (by omega) (by omega)
  · obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le h.le
    rw [hm]
    exact hμ m (by omega) (by omega)

private theorem additiveContent_axialDistance_ne_zero (hQ : Q ≠ 0)
    (hμ : ∀ d : ℕ, 0 < d → d < μ.card → additiveContent Q d ≠ 0) (T : StandardYoungTableau μ)
    (k : ℕ) (hk : k + 1 < μ.card) : additiveContent Q (axialDistance T.toTableau k hk) ≠ 0 := by
  rw [axialDistance_def]
  exact additiveContent_labelContent_sub_ne_zero hQ hμ T (Fin.mk_lt_mk.mpr (Nat.lt_add_one k))
    (by simp only; omega)

private theorem seminormalGen_sq (hQ : Q ≠ 0)
    (hμ : ∀ d : ℕ, 0 < d → d < μ.card → additiveContent Q d ≠ 0) (k : ℕ) (hk : k + 1 < μ.card)
    (ψ : StandardYoungTableau μ → K) :
    seminormalGen Q k hk (seminormalGen Q k hk ψ) = (Q - 1) • seminormalGen Q k hk ψ + Q • ψ := by
  funext T
  rw [seminormalGen_apply, extendSYT_seminormalGen,
    seminormalAux_sq_apply hQ k hk _ (additiveContent_axialDistance_ne_zero hQ hμ T k hk),
    Pi.add_apply, Pi.smul_apply, Pi.smul_apply, seminormalGen_apply, extendSYT_apply_toTableau,
    smul_eq_mul, smul_eq_mul]

private theorem seminormalGen_braid (hQ : Q ≠ 0)
    (hμ : ∀ d : ℕ, 0 < d → d < μ.card → additiveContent Q d ≠ 0) {k : ℕ}
    (hk : k + 1 + 1 < μ.card) (ψ : StandardYoungTableau μ → K) :
    seminormalGen Q k (by omega) (seminormalGen Q (k + 1) hk (seminormalGen Q k (by omega) ψ)) =
      seminormalGen Q (k + 1) hk (seminormalGen Q k (by omega) (seminormalGen Q (k + 1) hk ψ)) := by
  funext T
  rw [seminormalGen_apply, extendSYT_seminormalGen, extendSYT_seminormalGen, seminormalGen_apply,
    extendSYT_seminormalGen, extendSYT_seminormalGen]
  exact seminormalAux_braid_apply hQ hk _
    (additiveContent_labelContent_sub_ne_zero hQ hμ T (Fin.mk_lt_mk.mpr (by omega)) (by simp))
    (additiveContent_labelContent_sub_ne_zero hQ hμ T (Fin.mk_lt_mk.mpr (by omega)) (by simp))
    (additiveContent_labelContent_sub_ne_zero hQ hμ T (Fin.mk_lt_mk.mpr (by omega)) (by simp))

private theorem seminormalGen_comm (Q : K) {k l : ℕ} (hk : k + 1 < μ.card) (hl : l + 1 < μ.card)
    (hkl : k + 2 ≤ l) (ψ : StandardYoungTableau μ → K) :
    seminormalGen Q k hk (seminormalGen Q l hl ψ) =
      seminormalGen Q l hl (seminormalGen Q k hk ψ) := by
  funext T
  rw [seminormalGen_apply, extendSYT_seminormalGen, seminormalGen_apply, extendSYT_seminormalGen]
  exact seminormalAux_comm_apply Q hk hl hkl _ _

/-- **Hoefsmit's seminormal representation** of the Hecke algebra `H_n(q)`, `n = μ.card`, on the
functions on the standard Young tableaux of shape `μ`. With `Q = q ^ 2` and `g_i = q T_i`, the
generator `g_i` acts on a tableau vector through the axial distance `d` of the labels `i` and
`i + 1`, by the coefficients `seminormalDiag Q d` and `seminormalOffDiag Q d`
(`TauCeti.TypeAHeckeAlgebra.seminormalRep_T_apply`). The hypothesis that the additive contents
`[d]_Q` with `0 < d < n` are nonzero makes every coefficient well defined. At `Q = 1` it says
that the characteristic of `K` is zero or at least `n`; for `Q ≠ 1` it says that `Q` is not a
root of unity of order less than `n`. It follows from the split-semisimplicity criterion
`∏_(d=1)^n [d]_Q ≠ 0`. -/
noncomputable def seminormalRep (q : Kˣ) (μ : YoungDiagram)
    (hμ : ∀ d : ℕ, 0 < d → d < μ.card → additiveContent ((q : K) ^ 2) d ≠ 0) :
    TypeAHeckeAlgebra K q μ.card →ₐ[K] Module.End K (StandardYoungTableau μ → K) :=
  lift (fun i => (↑q⁻¹ : K) • seminormalGen ((q : K) ^ 2) i (by omega))
    (fun i => by
      have hq := q.ne_zero
      refine LinearMap.ext fun ψ => ?_
      simp only [mul_apply_eq_comp, LinearMap.smul_apply, LinearMap.add_apply,
        one_apply_eq_self, map_smul, seminormalGen_sq (pow_ne_zero 2 hq) hμ, smul_add,
        smul_smul, Units.val_inv_eq_inv_val]
      field_simp
      module)
    (fun {i j} h => by
      obtain ⟨j, hj⟩ := j
      simp only at h
      subst h
      refine LinearMap.ext fun ψ => ?_
      simp only [mul_apply_eq_comp, LinearMap.smul_apply, map_smul]
      rw [seminormalGen_braid (pow_ne_zero 2 q.ne_zero) hμ (k := i) (by omega)])
    (fun {i j} h => by
      refine LinearMap.ext fun ψ => ?_
      simp only [mul_apply_eq_comp, LinearMap.smul_apply, map_smul]
      rw [seminormalGen_comm _ _ _ h])

variable {q : Kˣ} {hμ : ∀ d : ℕ, 0 < d → d < μ.card → additiveContent ((q : K) ^ 2) d ≠ 0}

private theorem seminormalRep_T (i : Fin (μ.card - 1)) :
    seminormalRep q μ hμ (T q i) = (↑q⁻¹ : K) • seminormalGen ((q : K) ^ 2) i (by omega) :=
  lift_T _ _ _ _ i

/-- **The seminormal action of a generator.** With `Q = q ^ 2` and `d` the axial distance of the
labels `i` and `i + 1` in the standard tableau `U`, the value of `T_i ψ` at `U` combines the
values of `ψ` at `U` and, when `|d| ≠ 1`, at the tableau `U.swap i _ h` with `i` and `i + 1`
exchanged. -/
theorem seminormalRep_T_apply (i : Fin (μ.card - 1)) (ψ : StandardYoungTableau μ → K)
    (U : StandardYoungTableau μ) :
    seminormalRep q μ hμ (T q i) ψ U = (↑q⁻¹ : K) *
      (seminormalDiag ((q : K) ^ 2) (axialDistance U.toTableau i (by omega)) * ψ U +
        if h : |axialDistance U.toTableau i (by omega)| = 1 then 0
        else seminormalOffDiag ((q : K) ^ 2) (axialDistance U.toTableau i (by omega)) *
          ψ (U.swap i (by omega) h)) := by
  rw [seminormalRep_T, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, seminormalGen_apply,
    seminormalAux_apply, extendSYT_apply_toTableau]
  split_ifs with h
  · rw [seminormalOffDiag_of_abs_le_one h.le, zero_mul]
  · rw [← StandardYoungTableau.toTableau_swap U i (by omega) h, extendSYT_apply_toTableau]

/-- **The seminormal form on a basis vector**, when the labels `i` and `i + 1` of `U` do not lie
next to each other in a row or a column: `T_i` sends the vector of `U` to a combination of the
vectors of `U` and of `U` with `i` and `i + 1` exchanged. -/
theorem seminormalRep_T_single_of_abs_ne_one (i : Fin (μ.card - 1)) (U : StandardYoungTableau μ)
    (h : |axialDistance U.toTableau i (by omega)| ≠ 1) :
    seminormalRep q μ hμ (T q i) (Pi.single U 1) =
      ((↑q⁻¹ : K) * seminormalDiag ((q : K) ^ 2) (axialDistance U.toTableau i (by omega))) •
          Pi.single U 1 +
        ((↑q⁻¹ : K) * seminormalOffDiag ((q : K) ^ 2) (-axialDistance U.toTableau i (by omega))) •
          Pi.single (U.swap i (by omega) h) 1 := by
  funext V
  rw [seminormalRep_T_apply, Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
  by_cases hV : V = U
  · subst hV
    rw [dite_eq_right h, Pi.single_eq_same, Pi.single_eq_of_ne (V.swap_ne_self i (by omega) h),
      Pi.single_eq_of_ne (V.swap_ne_self i (by omega) h).symm]
    ring
  by_cases hV' : V = U.swap i (by omega) h
  · subst hV'
    have h' : ¬|axialDistance (U.swap i (by omega) h).toTableau i (by omega)| = 1 := by
      rwa [StandardYoungTableau.toTableau_swap, axialDistance_relabel_swap, abs_neg]
    rw [dite_eq_right h', StandardYoungTableau.swap_swap, Pi.single_eq_same, Pi.single_eq_of_ne hV,
      Pi.single_eq_same, StandardYoungTableau.toTableau_swap, axialDistance_relabel_swap]
    ring
  rw [Pi.single_eq_of_ne hV, Pi.single_eq_of_ne hV']
  split_ifs with h'
  · ring
  · rw [Pi.single_eq_of_ne]
    · ring
    · intro hVU
      subst hVU
      exact hV' (StandardYoungTableau.swap_swap _ _ _ _ _).symm

/-- **The seminormal form on a basis vector**, when the labels `i` and `i + 1` of `U` lie next to
each other in a row (axial distance `1`, where `T_i` acts by `q`) or in a column (axial distance
`-1`, where `T_i` acts by `-q⁻¹`). -/
theorem seminormalRep_T_single_of_abs_eq_one (i : Fin (μ.card - 1)) (U : StandardYoungTableau μ)
    (h : |axialDistance U.toTableau i (by omega)| = 1) :
    seminormalRep q μ hμ (T q i) (Pi.single U 1) =
      ((↑q⁻¹ : K) * seminormalDiag ((q : K) ^ 2) (axialDistance U.toTableau i (by omega))) •
          Pi.single U 1 := by
  funext V
  rw [seminormalRep_T_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hV : V = U
  · subst hV
    rw [dite_eq_left h, Pi.single_eq_same]
    ring
  rw [Pi.single_eq_of_ne hV]
  split_ifs with h'
  · ring
  · rw [Pi.single_eq_of_ne]
    · ring
    · intro hVU
      subst hVU
      rw [StandardYoungTableau.toTableau_swap, axialDistance_relabel_swap, abs_neg] at h
      exact h' h

/-- The Jucys–Murphy elements act on extensions by zero of tableau functions by the content
multiplications; the induction behind `seminormalRep_jucysMurphy_apply`. -/
private theorem extendSYT_seminormalRep_jucysMurphy (k : ℕ) (hk : k < μ.card)
    (ψ : StandardYoungTableau μ → K) :
    extendSYT K (seminormalRep q μ hμ (jucysMurphy q ⟨k, hk⟩) ψ) =
      contentMul ((q : K) ^ 2) ⟨k, hk⟩ (extendSYT K ψ) := by
  have hq := q.ne_zero
  have hQ : (q : K) ^ 2 ≠ 0 := pow_ne_zero 2 hq
  induction k generalizing ψ with
  | zero =>
    have : NeZero μ.card := ⟨by omega⟩
    have h0 : (⟨0, hk⟩ : Fin μ.card) = 0 := Fin.ext (Fin.val_zero _).symm
    rw [h0, jucysMurphy_zero, map_one, one_apply_eq_self]
    funext u
    by_cases hu : ∃ T : StandardYoungTableau μ, T.toTableau = u
    · obtain ⟨T, rfl⟩ := hu
      rw [contentMul_apply, ← h0, T.labelContent_zero hk, zpow_zero, one_mul]
    · rw [contentMul_apply, extendSYT_apply_of_not_exists _ hu, mul_zero]
  | succ k ih =>
    funext u
    by_cases hu : ∃ T : StandardYoungTableau μ, T.toTableau = u
    · obtain ⟨T, rfl⟩ := hu
      rw [jucysMurphy_succ k hk, map_mul, map_mul, mul_apply_eq_comp, mul_apply_eq_comp,
        extendSYT_apply_toTableau, seminormalRep_T]
      simp only [LinearMap.smul_apply, map_smul, Pi.smul_apply, smul_eq_mul, seminormalGen_apply,
        ih, extendSYT_seminormalGen]
      rw [seminormalAux_contentMul_seminormalAux_apply hQ k hk _
        (additiveContent_axialDistance_ne_zero hQ hμ T k hk), contentMul_apply,
        Units.val_inv_eq_inv_val]
      field_simp
    · rw [contentMul_apply, extendSYT_apply_of_not_exists _ hu, extendSYT_apply_of_not_exists _ hu,
        mul_zero]

/-- **The Jucys–Murphy eigenvalues of the seminormal basis.** The normalized Jucys–Murphy
element `J_i` acts on a function on the standard tableaux by multiplying its value at `U` by
`Q ^ content i`, with `Q = q ^ 2` and `content i = column - row` of the cell carrying the label
`i` in `U`. -/
theorem seminormalRep_jucysMurphy_apply (i : Fin μ.card) (ψ : StandardYoungTableau μ → K)
    (U : StandardYoungTableau μ) :
    seminormalRep q μ hμ (jucysMurphy q i) ψ U =
      ((q : K) ^ 2) ^ labelContent U.toTableau i * ψ U := by
  obtain ⟨k, hk⟩ := i
  have h := congrFun (extendSYT_seminormalRep_jucysMurphy (hμ := hμ) k hk ψ) U.toTableau
  rwa [extendSYT_apply_toTableau, contentMul_apply, extendSYT_apply_toTableau] at h

/-- The vector of a standard tableau `U` is an eigenvector of the Jucys–Murphy element `J_i`,
of eigenvalue `Q ^ content i`. -/
theorem seminormalRep_jucysMurphy_single (i : Fin μ.card) (U : StandardYoungTableau μ) :
    seminormalRep q μ hμ (jucysMurphy q i) (Pi.single U 1) =
      (((q : K) ^ 2) ^ labelContent U.toTableau i) • Pi.single U 1 := by
  funext V
  rw [seminormalRep_jucysMurphy_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hV : V = U
  · subst hV
    rfl
  · rw [Pi.single_eq_of_ne hV, mul_zero, mul_zero]

end Representation

end TauCeti.TypeAHeckeAlgebra

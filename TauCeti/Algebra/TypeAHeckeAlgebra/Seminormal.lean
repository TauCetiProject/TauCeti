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
import TauCeti.LinearAlgebra.ExtendByZero

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

The vectors `v_U` diagonalize the Jucys–Murphy elements: the additive element `L_i` acts by
`L_i v_U = [content i]_Q * v_U`, and the normalized element `J_i = 1 + (Q - 1) L_i` by
`J_i v_U = Q ^ content i * v_U`, where `content i` is the column minus the row of the label `i`
in `U`. The additive eigenvalues remain informative at `Q = 1`, where `J_i = 1`. Irreducibility
of these modules is proved in `TauCeti.Algebra.TypeAHeckeAlgebra.Seminormal.Irreducible`; their
comparison with other constructions of the Specht modules is not treated.

## Main definitions

* `TauCeti.TypeAHeckeAlgebra.seminormalDiag`, `TauCeti.TypeAHeckeAlgebra.seminormalOffDiag`: the
  coefficients of the seminormal form as functions of the axial distance.
* `TauCeti.TypeAHeckeAlgebra.seminormalRep`: the seminormal representation.

## Main results

* `TauCeti.TypeAHeckeAlgebra.seminormalRep_T_apply`: the action of a generator.
* `TauCeti.TypeAHeckeAlgebra.seminormalRep_T_single_of_abs_ne_one` and
  `TauCeti.TypeAHeckeAlgebra.seminormalRep_T_single_of_abs_eq_one`: the action of a generator on
  a basis vector.
* `TauCeti.TypeAHeckeAlgebra.seminormalRep_additiveJucysMurphy_single`: the basis vectors are
  eigenvectors of the additive Jucys–Murphy elements, with eigenvalues `[content]_Q`.
* `TauCeti.TypeAHeckeAlgebra.seminormalRep_jucysMurphy_single`: the basis vectors are
  eigenvectors of the normalized Jucys–Murphy elements, with eigenvalues `Q ^ content`.

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

theorem seminormalOffDiag_def (Q : K) (d : ℤ) : seminormalOffDiag Q d =
    if d < -1 then 1 else if 1 < d then Q + seminormalDiag Q d * seminormalDiag Q (-d) else 0 :=
  (rfl)

variable {Q : K}

/-- At axial distance `0` the diagonal coefficient is the junk value `0`, since `[0]_Q = 0`. -/
@[simp]
theorem seminormalDiag_zero : seminormalDiag Q 0 = 0 := by
  simp [seminormalDiag]

/-- At `Q = 1` the diagonal coefficient is Young's coefficient `1 / d`. -/
@[simp]
theorem seminormalDiag_one_left (d : ℤ) : seminormalDiag (1 : K) d = (d : K)⁻¹ := by
  simp [seminormalDiag]

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

/-- The identity behind the additive Jucys–Murphy recursion, for a label of content `x` and an
axial distance `d`; it reduces to the cocycle identity `[x + d]_Q = [x]_Q + Q ^ x [d]_Q`. This
makes the vector of a tableau an eigenvector of the additive Jucys–Murphy elements. -/
private theorem additiveContent_mul_seminormalDiag_add (hQ : Q ≠ 0) (x : ℤ) {d : ℤ}
    (hd : additiveContent Q d ≠ 0) :
    additiveContent Q x * seminormalDiag Q d + seminormalDiag Q (-d) * additiveContent Q (x + d) +
      1 = 0 := by
  have hx := sub_one_mul_additiveContent hQ x
  have hd' := sub_one_mul_additiveContent hQ d
  rw [seminormalDiag_neg hQ, seminormalDiag, additiveContent_add hQ x d]
  field_simp
  linear_combination -additiveContent Q x * hd' + additiveContent Q d * hx

/-- The off-diagonal coefficient vanishes when the axial distance is at most `1` in absolute
value. -/
theorem seminormalOffDiag_of_abs_le_one {d : ℤ} (hd : |d| ≤ 1) : seminormalOffDiag Q d = 0 := by
  rw [abs_le] at hd
  simp only [seminormalOffDiag]
  split_ifs <;> first | rfl | omega

@[simp]
theorem seminormalOffDiag_zero : seminormalOffDiag Q 0 = 0 :=
  seminormalOffDiag_of_abs_le_one (by simp)

@[simp]
theorem seminormalOffDiag_one : seminormalOffDiag Q 1 = 0 :=
  seminormalOffDiag_of_abs_le_one (by simp)

@[simp]
theorem seminormalOffDiag_neg_one : seminormalOffDiag Q (-1) = 0 :=
  seminormalOffDiag_of_abs_le_one (by simp)

/-- The off-diagonal coefficient is `1` at axial distances below `-1`. -/
theorem seminormalOffDiag_of_lt_neg_one {d : ℤ} (hd : d < -1) : seminormalOffDiag Q d = 1 := by
  rw [seminormalOffDiag, ite_eq_left hd]

/-- The off-diagonal coefficient at axial distances above `1`. -/
theorem seminormalOffDiag_of_one_lt {d : ℤ} (hd : 1 < d) :
    seminormalOffDiag Q d = Q + seminormalDiag Q d * seminormalDiag Q (-d) := by
  rw [seminormalOffDiag, ite_eq_right (by omega), ite_eq_left hd]

/-- The factored form `Q [d + 1]_Q [d - 1]_Q / [d]_Q ^ 2` of the product of the off-diagonal
coefficients at opposite axial distances. At `Q = 1` it is `1 - 1 / d ^ 2`. -/
theorem add_seminormalDiag_mul_seminormalDiag_neg {d : ℤ} (hd : additiveContent Q d ≠ 0) :
    Q + seminormalDiag Q d * seminormalDiag Q (-d) =
      Q * additiveContent Q (d + 1) * additiveContent Q (d - 1) / additiveContent Q d ^ 2 := by
  rcases eq_or_ne Q 0 with rfl | hQ
  · -- at `Q = 0` both sides vanish, since `0 ^ d = 0` for `d ≠ 0`
    simp [seminormalDiag, zero_zpow _ (ne_zero_of_additiveContent_ne_zero hd)]
  have h₁ := additiveContent_add_one Q d
  have h₂ := additiveContent_add_one Q (d - 1)
  rw [sub_add_cancel] at h₂
  have h₃ := sub_one_mul_additiveContent hQ d
  have h₄ : Q ^ d = Q ^ (d - 1) * Q := by rw [← zpow_add_one₀ hQ, sub_add_cancel]
  rw [seminormalDiag_neg hQ, seminormalDiag, h₁, eq_div_iff (pow_ne_zero 2 hd)]
  field_simp
  linear_combination Q * (additiveContent Q d + Q ^ d) * h₂ - Q ^ d * h₃ -
    (additiveContent Q d + Q ^ d) * h₄

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

open Function.ExtendByZero

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
  simp [seminormalAux]

variable (K) in
/-- Extension by zero from the standard tableaux to all tableaux. -/
private noncomputable abbrev extendSYT : (StandardYoungTableau μ → K) →ₗ[K] YoungTableau μ → K :=
  Function.ExtendByZero.linearMap K K StandardYoungTableau.toTableau

/-- The seminormal operator of `g = q T_k` on functions on the standard tableaux. -/
private noncomputable def seminormalGen (Q : K) (k : ℕ) (hk : k + 1 < μ.card) :
    Module.End K (StandardYoungTableau μ → K) :=
  LinearMap.funLeft K K StandardYoungTableau.toTableau ∘ₗ seminormalAux Q k hk ∘ₗ extendSYT K

private theorem seminormalGen_apply (Q : K) (k : ℕ) (hk : k + 1 < μ.card)
    (ψ : StandardYoungTableau μ → K) (T : StandardYoungTableau μ) :
    seminormalGen Q k hk ψ T = seminormalAux Q k hk (extendSYT K ψ) T.toTableau := by
  rw [seminormalGen, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.funLeft_apply]

/-- Extension by zero intertwines the seminormal operators on standard tableaux and on all
tableaux. At a nonstandard tableau `u` whose exchange is the standard tableau `T`, the labels
`k` and `k + 1` lie next to each other in `T`, so the off-diagonal coefficient vanishes. -/
private theorem extendSYT_seminormalGen (Q : K) (k : ℕ) (hk : k + 1 < μ.card)
    (ψ : StandardYoungTableau μ → K) :
    extendSYT K (seminormalGen Q k hk ψ) = seminormalAux Q k hk (extendSYT K ψ) := by
  funext u
  by_cases hu : ∃ T : StandardYoungTableau μ, T.toTableau = u
  · obtain ⟨T, rfl⟩ := hu
    rw [linearMap_apply_of_injective K StandardYoungTableau.toTableau_injective,
      seminormalGen_apply]
  rw [linearMap_apply_of_notMem_range K _ hu, seminormalAux_apply,
    linearMap_apply_of_notMem_range K _ hu, mul_zero, zero_add]
  by_cases hsu : ∃ T : StandardYoungTableau μ, T.toTableau = relabel (labelSwap k hk) u
  · obtain ⟨T, hT⟩ := hsu
    have hu' : u = relabel (labelSwap k hk) T.toTableau := by
      rw [hT, relabel_relabel, Equiv.swap_mul_self, relabel_one]
    have habs : |axialDistance T.toTableau k hk| = 1 := by
      by_contra h
      exact hu ⟨T.swap k hk h, (T.toTableau_swap k hk h).trans hu'.symm⟩
    rw [hu', axialDistance_relabel_swap, seminormalOffDiag_of_abs_le_one (by rw [abs_neg, habs]),
      zero_mul]
  · rw [linearMap_apply_of_notMem_range K _ hsu, mul_zero]

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
  simp only [← mul_assoc]
  exact swap_braid (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])

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

/-- Multiplication by the additive content `[labelContent t i]_Q` at the tableau `t`, the
expected action of the additive Jucys–Murphy element of strand `i`. -/
private def contentMul (Q : K) (i : Fin μ.card) : Module.End K (YoungTableau μ → K) :=
  LinearMap.mulLeft K (fun t => additiveContent Q (labelContent t i))

private theorem contentMul_apply (Q : K) (i : Fin μ.card) (φ : YoungTableau μ → K)
    (t : YoungTableau μ) : contentMul Q i φ t = additiveContent Q (labelContent t i) * φ t := by
  simp [contentMul]

/-- The additive Jucys–Murphy recursion `Q L_(k+1) = g_k L_k g_k + g_k` on a tableau vector:
conjugating multiplication by `[content k]_Q` with the seminormal operator of `g_k` and adding
that operator gives `Q` times the multiplication by `[content (k + 1)]_Q`. -/
private theorem seminormalAux_contentMul_seminormalAux_apply (hQ : Q ≠ 0) (k : ℕ)
    (hk : k + 1 < μ.card) (φ : YoungTableau μ → K) {t : YoungTableau μ}
    (hd : additiveContent Q (axialDistance t k hk) ≠ 0) :
    seminormalAux Q k hk (contentMul Q ⟨k, by omega⟩ (seminormalAux Q k hk φ)) t +
        seminormalAux Q k hk φ t =
      Q * (additiveContent Q (labelContent t ⟨k + 1, hk⟩) * φ t) := by
  have hE := seminormalOffDiag_mul_seminormalOffDiag_neg (Q := Q)
    (ne_zero_of_additiveContent_ne_zero hd)
  have hA := additiveContent_mul_seminormalDiag_add hQ (labelContent t ⟨k, by omega⟩) hd
  have hy : labelContent t ⟨k + 1, hk⟩ = labelContent t ⟨k, by omega⟩ + axialDistance t k hk := by
    rw [axialDistance_def, add_sub_cancel]
  have hc :
      labelContent (relabel (labelSwap k hk) t) ⟨k, by omega⟩ = labelContent t ⟨k + 1, hk⟩ := by
    rw [labelContent_relabel_labelSwap, Equiv.swap_apply_left]
  simp only [seminormalAux_apply, contentMul_apply, relabel_relabel, Equiv.swap_mul_self,
    relabel_one, axialDistance_relabel_swap, hc, hy]
  linear_combination (seminormalDiag Q (axialDistance t k hk) * φ t +
      seminormalOffDiag Q (axialDistance t k hk) * φ (relabel (labelSwap k hk) t)) * hA +
    additiveContent Q (labelContent t ⟨k, by omega⟩ + axialDistance t k hk) * φ t * hE

end Operators

/-! ### The seminormal representation -/

section Representation

open Function.ExtendByZero

variable {μ : YoungDiagram} {Q : K}

/-- Under the hypothesis of `TauCeti.TypeAHeckeAlgebra.seminormalRep` on `Q`, the additive
content of the difference of the contents of two labels of a standard tableau that differ by at
most two is nonzero. -/
theorem additiveContent_labelContent_sub_ne_zero (hQ : Q ≠ 0)
    (hμ : ∀ d : ℕ, 0 < d → d < μ.card → additiveContent Q d ≠ 0) (T : StandardYoungTableau μ)
    {a b : Fin μ.card} (hab : a < b) (hba : (b : ℕ) ≤ a + 2) :
    additiveContent Q (labelContent T.toTableau b - labelContent T.toTableau a) ≠ 0 := by
  have hne : labelContent T.toTableau b - labelContent T.toTableau a ≠ 0 :=
    sub_ne_zero.mpr (T.labelContent_ne_of_lt_of_le_add_two hab hba).symm
  have hlt : |labelContent T.toTableau b - labelContent T.toTableau a - 0| < μ.card := by
    rw [sub_zero]
    exact abs_labelContent_sub_lt_card T.toTableau b a
  rw [ne_eq, ← additiveContent_zero Q, additiveContent_inj hQ hμ hlt]
  exact hne

/-- Under the hypothesis of `TauCeti.TypeAHeckeAlgebra.seminormalRep` on `Q`, the additive
content of an axial distance of a standard tableau is nonzero. -/
theorem additiveContent_axialDistance_ne_zero (hQ : Q ≠ 0)
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
    seminormalAux_sq_apply hQ k hk _ (additiveContent_axialDistance_ne_zero hQ hμ T k hk)]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, seminormalGen_apply,
    linearMap_apply_of_injective K StandardYoungTableau.toTableau_injective]

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
functions on the standard Young tableaux of shape `μ`. Let `Q = q ^ 2`, `g_i = q T_i`, and let
`d` be the axial distance of the labels `i` and `i + 1` in a standard tableau `U`. The value of
`g_i ψ` at `U` combines the values of `ψ` at `U` and at `U` with `i` and `i + 1` exchanged, by the
coefficients `seminormalDiag Q d` and `seminormalOffDiag Q d`
(`TauCeti.TypeAHeckeAlgebra.seminormalRep_T_apply`). Dually, `g_i` sends the vector of `U` to
`seminormalDiag Q d` times itself plus `seminormalOffDiag Q (-d)` times the vector of the
exchanged tableau (`TauCeti.TypeAHeckeAlgebra.seminormalRep_T_single_of_abs_ne_one`). The
hypothesis that the additive contents `[d]_Q` with `0 < d < n` are nonzero makes every coefficient
well defined. At `Q = 1` it says
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
    seminormalAux_apply, linearMap_apply_of_injective K StandardYoungTableau.toTableau_injective]
  split_ifs with h
  · rw [seminormalOffDiag_of_abs_le_one h.le, zero_mul]
  · rw [← StandardYoungTableau.toTableau_swap U i (by omega) h,
      linearMap_apply_of_injective K StandardYoungTableau.toTableau_injective]

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

/-- The additive Jucys–Murphy elements act on extensions by zero of tableau functions by the
content multiplications; the induction behind `seminormalRep_additiveJucysMurphy_apply`. -/
private theorem extendSYT_seminormalRep_additiveJucysMurphy (k : ℕ) (hk : k < μ.card)
    (ψ : StandardYoungTableau μ → K) :
    extendSYT K (seminormalRep q μ hμ (additiveJucysMurphy q ⟨k, hk⟩) ψ) =
      contentMul ((q : K) ^ 2) ⟨k, hk⟩ (extendSYT K ψ) := by
  have hq := q.ne_zero
  have hQ : (q : K) ^ 2 ≠ 0 := pow_ne_zero 2 hq
  induction k generalizing ψ with
  | zero =>
    have : NeZero μ.card := ⟨by omega⟩
    have h0 : (⟨0, hk⟩ : Fin μ.card) = 0 := Fin.ext (Fin.val_zero _).symm
    rw [h0, additiveJucysMurphy_zero, map_zero, LinearMap.zero_apply, map_zero]
    funext u
    by_cases hu : ∃ T : StandardYoungTableau μ, T.toTableau = u
    · obtain ⟨T, rfl⟩ := hu
      rw [contentMul_apply, T.labelContent_zero, additiveContent_zero, zero_mul, Pi.zero_apply]
    · rw [contentMul_apply, linearMap_apply_of_notMem_range K _ hu, mul_zero, Pi.zero_apply]
  | succ k ih =>
    funext u
    by_cases hu : ∃ T : StandardYoungTableau μ, T.toTableau = u
    · obtain ⟨T, rfl⟩ := hu
      have key := seminormalAux_contentMul_seminormalAux_apply hQ k hk (extendSYT K ψ)
        (additiveContent_axialDistance_ne_zero hQ hμ T k hk)
      rw [additiveJucysMurphy_succ k hk, map_add, map_mul, map_mul, map_smul, LinearMap.add_apply,
        mul_apply_eq_comp, mul_apply_eq_comp,
        linearMap_apply_of_injective K StandardYoungTableau.toTableau_injective, seminormalRep_T]
      simp only [LinearMap.smul_apply, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        seminormalGen_apply, ih, extendSYT_seminormalGen]
      rw [contentMul_apply, Units.val_inv_eq_inv_val]
      field_simp
      linear_combination key
    · rw [contentMul_apply, linearMap_apply_of_notMem_range K _ hu,
        linearMap_apply_of_notMem_range K _ hu, mul_zero]

/-- **The additive Jucys–Murphy eigenvalues of the seminormal basis.** The additive Jucys–Murphy
element `L_i` acts on a function on the standard tableaux by multiplying its value at `U` by the
additive content `[content i]_Q`, with `Q = q ^ 2` and `content i = column - row` of the cell
carrying the label `i` in `U`. Unlike the normalized eigenvalues, these distinguish the tableaux
also at `Q = 1`. -/
theorem seminormalRep_additiveJucysMurphy_apply (i : Fin μ.card)
    (ψ : StandardYoungTableau μ → K) (U : StandardYoungTableau μ) :
    seminormalRep q μ hμ (additiveJucysMurphy q i) ψ U =
      additiveContent ((q : K) ^ 2) (labelContent U.toTableau i) * ψ U := by
  obtain ⟨k, hk⟩ := i
  have h := congrFun (extendSYT_seminormalRep_additiveJucysMurphy (hμ := hμ) k hk ψ) U.toTableau
  rwa [linearMap_apply_of_injective K StandardYoungTableau.toTableau_injective, contentMul_apply,
    linearMap_apply_of_injective K StandardYoungTableau.toTableau_injective] at h

/-- The vector of a standard tableau `U` is an eigenvector of the additive Jucys–Murphy element
`L_i`, of eigenvalue `[content i]_Q`. -/
theorem seminormalRep_additiveJucysMurphy_single (i : Fin μ.card) (U : StandardYoungTableau μ) :
    seminormalRep q μ hμ (additiveJucysMurphy q i) (Pi.single U 1) =
      additiveContent ((q : K) ^ 2) (labelContent U.toTableau i) • Pi.single U 1 := by
  funext V
  rw [seminormalRep_additiveJucysMurphy_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hV : V = U
  · subst hV
    rfl
  · rw [Pi.single_eq_of_ne hV, mul_zero, mul_zero]

/-- **The Jucys–Murphy eigenvalues of the seminormal basis.** The normalized Jucys–Murphy
element `J_i = 1 + (Q - 1) L_i` acts on a function on the standard tableaux by multiplying its
value at `U` by `Q ^ content i`, with `Q = q ^ 2` and `content i = column - row` of the cell
carrying the label `i` in `U`. -/
theorem seminormalRep_jucysMurphy_apply (i : Fin μ.card) (ψ : StandardYoungTableau μ → K)
    (U : StandardYoungTableau μ) :
    seminormalRep q μ hμ (jucysMurphy q i) ψ U =
      ((q : K) ^ 2) ^ labelContent U.toTableau i * ψ U := by
  have h := sub_one_mul_additiveContent (pow_ne_zero 2 q.ne_zero) (labelContent U.toTableau i)
  rw [jucysMurphy_eq_one_add_smul_additiveJucysMurphy, map_add, map_one, map_smul,
    LinearMap.add_apply, LinearMap.smul_apply, one_apply_eq_self, Pi.add_apply, Pi.smul_apply,
    seminormalRep_additiveJucysMurphy_apply, smul_eq_mul]
  linear_combination ψ U * h

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

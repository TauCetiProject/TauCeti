/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.LowerCentralSeries.Graded.Basic

/-!
# The graded deviation of an endomorphism congruent to the identity

Let `G` be a topological group with lower `p`-series `λ_k = TauCeti.pLowerCentralSeries p G k`,
and let `θ : G →* G` be a continuous endomorphism that is *congruent to the identity modulo
`λ_m`*: `g⁻¹ * θ g ∈ λ_m` for every `g`. Then `g⁻¹ * θ g ∈ λ_{m+k}` for `g ∈ λ_k`, and the
assignment `g ↦ g⁻¹ * θ g` induces additive maps

  `D_k : gr_k(G) →+ gr_{m+k}(G)`

on the graded pieces `gr_k(G) = λ_k ⧸ λ_{k+1}`, the **graded deviation** of `θ`. The map
`g ↦ g⁻¹ * θ g` is a crossed homomorphism,
`(g * h)⁻¹ * θ (g * h) = (h⁻¹ * (g⁻¹ * θ g) * h) * (h⁻¹ * θ h)`, and the conjugation acts
trivially on the relevant graded piece; this is what makes `D_k` well defined and additive.

For `m ≥ 1` the deviation is a derivation of the graded structure: it satisfies the Leibniz rule
`D [x, y] = [D x, y] + [x, D y]` against the bracket, and it commutes with the `p`-power operator
`π` in every degree `k ≥ 1`. In degree zero the exact relation is
`D (π x) = π (D x) + (p choose 2) • [D x, x]`, the binomial formula of nilpotency class two, so
`D` commutes with `π` in degree zero for odd `p`, while for `p = 2` the defect is the bracket
`[D x, x]`. This dyadic defect is not a degree-zero accident of the operator `π` alone: the
deviation carries it into the degree `m + 1` for every `m`, and it is the reason the
basis-modification maps of the theory of Demushkin groups acquire an extra bracket term at
`p = 2`.

The motivating case is a free pro-`p` group `F` on generators `x_i` and the endomorphism
`x_i ↦ x_i * w_i` with `w_i ∈ λ_m(F)`, which moves a relator `r ∈ λ_1(F)` inside its coset by an
element of `λ_{m+1}(F)` whose class is `D_1 ρ`, for `ρ ∈ gr_1(F)` the class of `r`. That case is
developed in
`TauCeti.Topology.Algebra.Group.Profinite.Free.BasisModification`.

## Main definitions

* `TauCeti.gradedDeviation`: the additive map `D_k : gr_k(G) →+ gr_{m+k}(G)` induced by
  `g ↦ g⁻¹ * θ g`.

## Main results

* `TauCeti.inv_mul_apply_mem_pLowerCentralSeries`: `g⁻¹ * θ g ∈ λ_{m+k}` for `g ∈ λ_k`.
* `TauCeti.gradedMap_eq_id_of_one_le`: for `m ≥ 1`, `θ` induces the identity on every graded piece.
* `TauCeti.gradedDeviation_gradedBracket`, `TauCeti.gradedDeviation_gradedBracket_zero`: the
  Leibniz rule, for `m ≥ 1`.
* `TauCeti.gradedDeviation_gradedPow_of_one_le`, `TauCeti.gradedDeviation_gradedPow_zero`,
  `TauCeti.gradedDeviation_gradedPow_zero_of_odd`, `TauCeti.gradedDeviation_gradedPow_zero_of_two`:
  compatibility with `π`, exact in every degree.

## References

* J. Labute, *Classification of Demushkin groups*, Canadian J. Math. 19 (1967), §1 and
  Proposition 5.
-/

public section

open Subgroup
open scoped commutatorElement

namespace TauCeti

universe u

variable {p : ℕ} {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-! ### The deviation of an endomorphism congruent to the identity -/

section Deviation

variable (θ : G →* G) (hθc : Continuous θ) {m : ℕ}
  (hθ : ∀ g, g⁻¹ * θ g ∈ pLowerCentralSeries p G m)

include hθc hθ in
/-- **An endomorphism congruent to the identity modulo `λ_m` is congruent to the identity modulo
`λ_{m+k}` on `λ_k`.** -/
theorem inv_mul_apply_mem_pLowerCentralSeries {k : ℕ} {g : G} (hg : g ∈ pLowerCentralSeries p G k) :
    g⁻¹ * θ g ∈ pLowerCentralSeries p G (m + k) := by
  induction k generalizing g with
  | zero => exact hθ g
  | succ k ih =>
    -- The elements on which `θ` agrees with the identity modulo `N = λ_{m+k+1}` form a closed
    -- subgroup `K`, which contains the `p`-th powers and the commutators generating `λ_{k+1}` by
    -- the induction hypothesis on `λ_k`.
    set N := pLowerCentralSeries p G (m + k + 1)
    have : IsClosed (N : Set G) := isClosed_pLowerCentralSeries _
    set K : Subgroup G := (QuotientGroup.mk' N).eqLocus ((QuotientGroup.mk' N).comp θ)
    have hmem : ∀ x, x ∈ K ↔ ((x : G) : G ⧸ N) = θ x := fun x ↦ Iff.rfl
    have hKc : IsClosed (K : Set G) :=
      isClosed_eq QuotientGroup.continuous_mk (QuotientGroup.continuous_mk.comp hθc)
    suffices h : pLowerCentralSeries p G (k + 1) ≤ K from
      QuotientGroup.eq.mp ((hmem g).mp (h hg))
    rw [pLowerCentralSeries_succ, pLowerCentralStep_le_iff hKc]
    refine ⟨fun x hx ↦ ?_, Subgroup.commutator_le.mpr fun x hx y _ ↦ ?_⟩
    · -- `θ (x ^ p) = (x * u) ^ p` with `u ∈ λ_{m+k}` central modulo `N`, and `u ^ p ∈ N`.
      have hu := ih hx
      set u := x⁻¹ * θ x
      have hθx : θ x = x * u := (mul_inv_cancel_left x (θ x)).symm
      rw [hmem, map_pow, hθx, QuotientGroup.mk_pow, QuotientGroup.mk_pow, QuotientGroup.mk_mul,
        (commute_mk_of_mem_pLowerCentralSeries hu x).mul_pow, ← QuotientGroup.mk_pow _ u,
        mk_eq_one_of_mem_pLowerCentralSeries_of_le (m + k + 1) (pow_mem_pLowerCentralSeries hu)
          le_rfl, mul_one]
    · -- `θ ⁅x, y⁆ = ⁅x * u, y * v⁆` with `⁅u, y * v⁆ ∈ N` and `⁅x, v⁆ ∈ N`.
      have hu := ih hx
      have hv := hθ y
      set u := x⁻¹ * θ x
      set v := y⁻¹ * θ y
      have hθx : θ x = x * u := (mul_inv_cancel_left x (θ x)).symm
      have hθy : θ y = y * v := (mul_inv_cancel_left y (θ y)).symm
      rw [hmem, map_commutatorElement, hθx, hθy,
        mk_eq_mk_mul_mk_of_le (m + k + 1) (by omega) (mk_commutatorElement_mul_left hu
          (mem_pLowerCentralSeries_zero p (y * v)) x),
        mk_eq_one_of_mem_pLowerCentralSeries_of_le (m + k + 1)
          (commutator_mem_pLowerCentralSeries_succ hu (y * v)) le_rfl, mul_one,
        mk_eq_mk_mul_mk_of_le (m + k + 1) (by omega) (mk_commutatorElement_mul_right hx hv y),
        mk_eq_one_of_mem_pLowerCentralSeries_of_le (m + k + 1)
          (commutator_mem_pLowerCentralSeries hx hv) (by omega), mul_one]

/-- The deviation `x ↦ x⁻¹ * θ x` on `λ_k`, with values in `λ_{m+k} ⧸ λ_{m+k+1}`, before passing
to the quotient by `λ_{k+1}`. -/
private def deviationAux (k : ℕ) :
    pLowerCentralSeries p G k →*
      (pLowerCentralSeries p G (m + k) ⧸
        (pLowerCentralSeries p G (m + k + 1)).subgroupOf (pLowerCentralSeries p G (m + k))) where
  toFun x := QuotientGroup.mk ⟨(x : G)⁻¹ * θ x, inv_mul_apply_mem_pLowerCentralSeries θ hθc hθ x.2⟩
  map_one' := by
    rw [← QuotientGroup.mk_one]
    congr 1
    ext
    simp
  map_mul' x y := by
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq_subgroupOf]
    simp only [coe_mul]
    have hu : (x : G)⁻¹ * θ x ∈ pLowerCentralSeries p G (m + k) :=
      inv_mul_apply_mem_pLowerCentralSeries θ hθc hθ x.2
    have h : ((x : G) * y)⁻¹ * θ ((x : G) * y) =
        ((y : G)⁻¹ * ((x : G)⁻¹ * θ x) * (y : G)⁻¹⁻¹) * ((y : G)⁻¹ * θ y) := by
      rw [map_mul]; group
    rw [h, QuotientGroup.mk_mul _ ((y : G)⁻¹ * ((x : G)⁻¹ * θ x) * (y : G)⁻¹⁻¹),
      QuotientGroup.mk_mul _ ((x : G)⁻¹ * θ x), mk_conj_of_mem_pLowerCentralSeries hu]

private theorem deviationAux_apply (k : ℕ) (x : pLowerCentralSeries p G k) :
    deviationAux θ hθc hθ k x = QuotientGroup.mk ⟨(x : G)⁻¹ * θ x,
      inv_mul_apply_mem_pLowerCentralSeries θ hθc hθ x.2⟩ :=
  rfl

private theorem subgroupOf_le_ker_deviationAux (k : ℕ) :
    (pLowerCentralSeries p G (k + 1)).subgroupOf (pLowerCentralSeries p G k) ≤
      (deviationAux θ hθc hθ k).ker := by
  intro x hx
  rw [MonoidHom.mem_ker, deviationAux_apply, QuotientGroup.eq_one_iff, mem_subgroupOf, coe_mk]
  exact inv_mul_apply_mem_pLowerCentralSeries θ hθc hθ (mem_subgroupOf.mp hx)

/-- **The graded deviation** `D_k : gr_k(G) →+ gr_{m+k}(G)` of an endomorphism `θ` congruent to
the identity modulo `λ_m`: the map induced by `g ↦ g⁻¹ * θ g`. Its defining equation is
`TauCeti.gradedDeviation_gradedMk`. For `m ≥ 1` it is a derivation of the graded structure
(`TauCeti.gradedDeviation_gradedBracket`), compatible with `π` away from degree zero
(`TauCeti.gradedDeviation_gradedPow_of_one_le`) and with the binomial defect
`(p choose 2) • [D x, x]` in degree zero (`TauCeti.gradedDeviation_gradedPow_zero`). -/
def gradedDeviation (k : ℕ) : gradedPiece p G k →+ gradedPiece p G (m + k) :=
  MonoidHom.toAdditive
    (QuotientGroup.lift _ (deviationAux θ hθc hθ k) (subgroupOf_le_ker_deviationAux θ hθc hθ k))

/-- **The graded deviation on classes**: the defining equation of `TauCeti.gradedDeviation`. -/
@[simp]
theorem gradedDeviation_gradedMk {k : ℕ} (x : pLowerCentralSeries p G k) :
    gradedDeviation θ hθc hθ k (gradedMk p G k x) =
      gradedMk p G (m + k)
        ⟨(x : G)⁻¹ * θ x, inv_mul_apply_mem_pLowerCentralSeries θ hθc hθ x.2⟩ := by
  rw [gradedDeviation, gradedMk_def k x, MonoidHom.toAdditive_apply_apply, toMul_ofMul,
    QuotientGroup.lift_mk, deviationAux_apply, gradedMk_def (m + k)]

/-- **The graded deviation in degree zero**: the class of `g` goes to the class of `g⁻¹ * θ g` in
`gr_m(G)`. -/
@[simp]
theorem gradedDeviation_gradedMkZero (g : G) :
    gradedDeviation θ hθc hθ 0 (gradedMkZero p G g) = gradedMk p G m ⟨g⁻¹ * θ g, hθ g⟩ := by
  rw [← gradedMk_zero ⟨g, mem_pLowerCentralSeries_zero p g⟩]
  exact gradedDeviation_gradedMk θ hθc hθ _

include hθc hθ in
/-- **An endomorphism congruent to the identity modulo `λ_m` with `m ≥ 1` induces the identity on
every graded piece**: its deviation on `λ_k` lies in `λ_{m+k} ≤ λ_{k+1}`. -/
theorem gradedMap_eq_id_of_one_le (hm : 1 ≤ m) (k : ℕ) :
    gradedMap p θ hθc k = AddMonoidHom.id (gradedPiece p G k) := by
  refine AddMonoidHom.ext fun x ↦ ?_
  obtain ⟨x, rfl⟩ := gradedMk_surjective k x
  rw [gradedMap_gradedMk, AddMonoidHom.id_apply, gradedMk_eq_gradedMk_iff, coe_mk, eq_comm,
    QuotientGroup.eq]
  exact pLowerCentralSeries_antitone (by omega)
    (inv_mul_apply_mem_pLowerCentralSeries θ hθc hθ x.2)

/-- **The Leibniz rule.** For `m ≥ 1` the graded deviation is a derivation of the bracket:
`D [x, y] = [D x, y] + [x, D y]`, with the two terms transported to the degree `m + (j + k + 1)`.
The cross term `⁅x⁻¹ * θ x, y⁻¹ * θ y⁆` has degree `2m + j + k + 1`, which is above
`m + j + k + 1` exactly when `m ≥ 1`. -/
theorem gradedDeviation_gradedBracket (hm : 1 ≤ m) {j k : ℕ} (x : gradedPiece p G j)
    (y : gradedPiece p G k) :
    gradedDeviation θ hθc hθ (j + k + 1) (gradedBracket p G j k x y) =
      gradedCast p G (by omega)
          (gradedBracket p G (m + j) k (gradedDeviation θ hθc hθ j x) y) +
        gradedCast p G (by omega)
          (gradedBracket p G j (m + k) x (gradedDeviation θ hθc hθ k y)) := by
  obtain ⟨x, rfl⟩ := gradedMk_surjective j x
  obtain ⟨y, rfl⟩ := gradedMk_surjective k y
  have hu : (x : G)⁻¹ * θ x ∈ pLowerCentralSeries p G (m + j) :=
    inv_mul_apply_mem_pLowerCentralSeries θ hθc hθ x.2
  have hv : (y : G)⁻¹ * θ y ∈ pLowerCentralSeries p G (m + k) :=
    inv_mul_apply_mem_pLowerCentralSeries θ hθc hθ y.2
  rw [gradedBracket_gradedMk, gradedDeviation_gradedMk, gradedDeviation_gradedMk,
    gradedDeviation_gradedMk, gradedBracket_gradedMk, gradedBracket_gradedMk, gradedCast_gradedMk,
    gradedCast_gradedMk, ← gradedMk_mul, gradedMk_eq_gradedMk_iff]
  simp only [coe_mul]
  set u := (x : G)⁻¹ * θ x
  set v := (y : G)⁻¹ * θ y
  have hθx : θ x = x * u := (mul_inv_cancel_left (x : G) (θ x)).symm
  have hθy : θ y = y * v := (mul_inv_cancel_left (y : G) (θ y)).symm
  -- `⁅x * u, y * v⁆ ≡ ⁅x, y⁆ * ⁅x, v⁆ * ⁅u, y⁆` modulo `λ_{m+j+k+2}`, by bimultiplicativity of the
  -- commutator, since `⁅u, v⁆ ∈ λ_{2m+j+k+1}`.
  have h : ((⁅(x : G) * u, (y : G) * v⁆ : G) : G ⧸ pLowerCentralSeries p G (m + (j + k + 1) + 1)) =
      ((⁅(x : G), (y : G)⁆ : G) : G ⧸ _) * ((⁅(x : G), v⁆ : G) : G ⧸ _) *
        ((⁅u, (y : G)⁆ : G) : G ⧸ _) := by
    rw [mk_eq_mk_mul_mk_of_le _ (by omega) (mk_commutatorElement_mul_left hu
        (mul_mem y.2 (pLowerCentralSeries_antitone (Nat.le_add_left k m) hv)) x),
      mk_eq_mk_mul_mk_of_le _ (by omega) (mk_commutatorElement_mul_right x.2 hv y),
      mk_eq_mk_mul_mk_of_le _ (by omega) (mk_commutatorElement_mul_right hu hv y),
      mk_eq_one_of_mem_pLowerCentralSeries_of_le _ (commutator_mem_pLowerCentralSeries hu hv)
        (by omega), mul_one]
  rw [map_commutatorElement, hθx, hθy, QuotientGroup.mk_mul, QuotientGroup.mk_inv, h,
    QuotientGroup.mk_mul, mul_assoc, inv_mul_cancel_left,
    (commute_mk_of_mem_pLowerCentralSeries_of_le _ (commutator_mem_pLowerCentralSeries x.2 hv)
      (by omega) _).eq]

/-- **The Leibniz rule in degree zero**, in the cast-free form
`D [x, y] = [D x, y] - [D y, x]` for `x, y ∈ gr_0(G)` and `m ≥ 1`, using skew-symmetry of the
bracket to put both terms in `gr_{m+1}(G)`. -/
@[simp]
theorem gradedDeviation_gradedBracket_zero (hm : 1 ≤ m) (x y : gradedPiece p G 0) :
    gradedDeviation θ hθc hθ 1 (gradedBracket p G 0 0 x y) =
      gradedBracket p G m 0 (gradedDeviation θ hθc hθ 0 x) y -
        gradedBracket p G m 0 (gradedDeviation θ hθc hθ 0 y) x := by
  obtain ⟨x, rfl⟩ := gradedMk_surjective 0 x
  obtain ⟨y, rfl⟩ := gradedMk_surjective 0 y
  have hu : (x : G)⁻¹ * θ x ∈ pLowerCentralSeries p G m := hθ x
  have hv : (y : G)⁻¹ * θ y ∈ pLowerCentralSeries p G m := hθ y
  -- The general Leibniz rule at `j = k = 0`, with the casts pushed through the classes and the
  -- degrees `m + (0 + 0 + 1)`, `m + 0 + 0 + 1` and `0 + (m + 0) + 1` all read as `m + 1`.
  have h : gradedMk p G (m + 1) ⟨⁅(x : G), (y : G)⁆⁻¹ * θ ⁅(x : G), (y : G)⁆,
        inv_mul_apply_mem_pLowerCentralSeries θ hθc hθ
          (commutator_mem_pLowerCentralSeries x.2 y.2)⟩ =
      gradedMk p G (m + 1) ⟨⁅(x : G)⁻¹ * θ x, (y : G)⁆,
          commutator_mem_pLowerCentralSeries_succ hu y⟩ +
        gradedMk p G (m + 1) ⟨⁅(x : G), (y : G)⁻¹ * θ y⁆,
          commutatorElement_inv ((y : G)⁻¹ * θ y) x ▸
            inv_mem (commutator_mem_pLowerCentralSeries_succ hv x)⟩ := by
    simpa only [gradedDeviation_gradedMk, gradedBracket_gradedMk, gradedCast_gradedMk] using
      gradedDeviation_gradedBracket θ hθc hθ hm (gradedMk p G 0 x) (gradedMk p G 0 y)
  -- The degree-zero deviations live in `gr_{m+0} = gr_m`, the brackets in `gr_{m+0+1} = gr_{m+1}`.
  have ex : gradedDeviation θ hθc hθ 0 (gradedMk p G 0 x) = gradedMk p G m ⟨(x : G)⁻¹ * θ x, hu⟩ :=
    gradedDeviation_gradedMk θ hθc hθ x
  have ey : gradedDeviation θ hθc hθ 0 (gradedMk p G 0 y) = gradedMk p G m ⟨(y : G)⁻¹ * θ y, hv⟩ :=
    gradedDeviation_gradedMk θ hθc hθ y
  have hbx : gradedBracket p G m 0 (gradedMk p G m ⟨(x : G)⁻¹ * θ x, hu⟩) (gradedMk p G 0 y) =
      gradedMk p G (m + 1) ⟨⁅(x : G)⁻¹ * θ x, (y : G)⁆,
        commutator_mem_pLowerCentralSeries_succ hu y⟩ :=
    gradedBracket_gradedMk _ _
  have hby : gradedBracket p G m 0 (gradedMk p G m ⟨(y : G)⁻¹ * θ y, hv⟩) (gradedMk p G 0 x) =
      gradedMk p G (m + 1) ⟨⁅(y : G)⁻¹ * θ y, (x : G)⁆,
        commutator_mem_pLowerCentralSeries_succ hv x⟩ :=
    gradedBracket_gradedMk _ _
  rw [gradedBracket_gradedMk, gradedDeviation_gradedMk, h, ex, ey, hbx, hby, sub_eq_add_neg,
    ← gradedMk_inv, add_right_inj, gradedMk_eq_gradedMk_iff, coe_inv, coe_mk, coe_mk,
    commutatorElement_inv]

/-- **The graded deviation commutes with `π` above degree zero**, for every `m`: for `k ≥ 1`,
`D (π x) = π (D x)`, because `⁅x, x⁻¹ * θ x⁆` has degree `m + 2k + 1 ≥ m + k + 2`. -/
@[simp]
theorem gradedDeviation_gradedPow_of_one_le {k : ℕ} (hk : 1 ≤ k) (x : gradedPiece p G k) :
    gradedDeviation θ hθc hθ (k + 1) (gradedPow p G k x) =
      gradedPow p G (m + k) (gradedDeviation θ hθc hθ k x) := by
  obtain ⟨x, rfl⟩ := gradedMk_surjective k x
  have hu : (x : G)⁻¹ * θ x ∈ pLowerCentralSeries p G (m + k) :=
    inv_mul_apply_mem_pLowerCentralSeries θ hθc hθ x.2
  -- The two sides live in `gr_{m+(k+1)}` and `gr_{m+k+1}`, which agree definitionally.
  have e : gradedDeviation θ hθc hθ (k + 1)
      (gradedMk p G (k + 1) ⟨(x : G) ^ p, pow_mem_pLowerCentralSeries x.2⟩) =
        gradedMk p G (m + k + 1) ⟨((x : G) ^ p)⁻¹ * θ ((x : G) ^ p),
          inv_mul_apply_mem_pLowerCentralSeries θ hθc hθ (pow_mem_pLowerCentralSeries x.2)⟩ :=
    gradedDeviation_gradedMk θ hθc hθ _
  rw [gradedPow_gradedMk, e, gradedDeviation_gradedMk, gradedPow_gradedMk, gradedMk_eq_gradedMk_iff]
  dsimp only
  set u := (x : G)⁻¹ * θ x
  have hθx : θ x = x * u := (mul_inv_cancel_left (x : G) (θ x)).symm
  rw [map_pow, hθx, QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_pow,
    QuotientGroup.mk_pow, QuotientGroup.mk_mul _ (x : G) u,
    (QuotientGroup.commute_mk_iff.mpr (pLowerCentralSeries_antitone (by omega)
      (commutator_mem_pLowerCentralSeries x.2 hu))).mul_pow, inv_mul_cancel_left,
    QuotientGroup.mk_pow]

/-- **The graded deviation against `π` in degree zero**:
`D (π x) = π (D x) + (p choose 2) • [D x, x]` in `gr_{m+1}(G)`. This is the binomial formula
`(x * u) ^ p = x ^ p * u ^ p * ⁅u, x⁆ ^ (p choose 2)` of nilpotency class two, read modulo
`λ_{m+2}`, where the class of `⁅u, x⁆ ∈ λ_{m+1}` is central. -/
theorem gradedDeviation_gradedPow_zero (x : gradedPiece p G 0) :
    gradedDeviation θ hθc hθ 1 (gradedPow p G 0 x) =
      gradedPow p G m (gradedDeviation θ hθc hθ 0 x) +
        p.choose 2 • gradedBracket p G m 0 (gradedDeviation θ hθc hθ 0 x) x := by
  obtain ⟨x, rfl⟩ := gradedMk_surjective 0 x
  have hu : (x : G)⁻¹ * θ x ∈ pLowerCentralSeries p G m := hθ x
  -- The degree-zero deviation lives in `gr_{m+0} = gr_m`, the bracket in `gr_{m+0+1} = gr_{m+1}`.
  have e : gradedDeviation θ hθc hθ 0 (gradedMk p G 0 x) = gradedMk p G m ⟨(x : G)⁻¹ * θ x, hu⟩ :=
    gradedDeviation_gradedMk θ hθc hθ x
  have hb : gradedBracket p G m 0 (gradedMk p G m ⟨(x : G)⁻¹ * θ x, hu⟩) (gradedMk p G 0 x) =
      gradedMk p G (m + 1) ⟨⁅(x : G)⁻¹ * θ x, (x : G)⁆,
        commutator_mem_pLowerCentralSeries_succ hu x⟩ :=
    gradedBracket_gradedMk _ _
  rw [gradedPow_gradedMk, gradedDeviation_gradedMk, e, gradedPow_gradedMk, hb, ← gradedMk_pow,
    ← gradedMk_mul, gradedMk_eq_gradedMk_iff]
  simp only [coe_mul, coe_pow]
  set u := (x : G)⁻¹ * θ x
  have hθx : θ x = x * u := (mul_inv_cancel_left (x : G) (θ x)).symm
  set N := pLowerCentralSeries p G (m + 1 + 1)
  have hcomm : (⁅(u : G ⧸ N), ((x : G) : G ⧸ N)⁆ : G ⧸ N) = ((⁅u, (x : G)⁆ : G) : G ⧸ N) :=
    (map_commutatorElement (QuotientGroup.mk' N) u x).symm
  have hc := commute_mk_of_mem_pLowerCentralSeries_of_le (m + 1 + 1)
    (commutator_mem_pLowerCentralSeries_succ hu x) le_rfl
  rw [map_pow, hθx, QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_pow,
    QuotientGroup.mk_pow, QuotientGroup.mk_mul _ (x : G) u,
    Commute.mul_pow_eq_pow_mul_pow_mul_commutatorElement_pow_choose_two
      (by rw [hcomm]; exact hc x) (by rw [hcomm]; exact hc u),
    mul_assoc, inv_mul_cancel_left, hcomm, QuotientGroup.mk_mul _ (u ^ p),
    QuotientGroup.mk_pow _ u, QuotientGroup.mk_pow _ ⁅u, (x : G)⁆]

/-- **The graded deviation commutes with `π` in degree zero for odd `p`**: the defect
`(p choose 2) • [D x, x]` is a multiple of `p • [D x, x] = 0`. -/
@[simp]
theorem gradedDeviation_gradedPow_zero_of_odd (hp : Odd p) (x : gradedPiece p G 0) :
    gradedDeviation θ hθc hθ 1 (gradedPow p G 0 x) =
      gradedPow p G m (gradedDeviation θ hθc hθ 0 x) := by
  rw [gradedDeviation_gradedPow_zero, choose_two_nsmul_gradedPiece_eq_zero_of_odd hp, add_zero]

/-- **The dyadic defect of the graded deviation against `π` in degree zero.** For `p = 2`,
`D (π x) = π (D x) + [D x, x]` in `gr_{m+1}(G)`: the square of `x * u` is `x ^ 2 * u ^ 2 * ⁅u, x⁆`
up to `λ_{m+2}`, and the commutator does not vanish in `gr_{m+1}(G)` in general. -/
@[simp]
theorem gradedDeviation_gradedPow_zero_of_two (hp : p = 2) (x : gradedPiece p G 0) :
    gradedDeviation θ hθc hθ 1 (gradedPow p G 0 x) =
      gradedPow p G m (gradedDeviation θ hθc hθ 0 x) +
        gradedBracket p G m 0 (gradedDeviation θ hθc hθ 0 x) x := by
  subst hp
  rw [gradedDeviation_gradedPow_zero, Nat.choose_self, one_nsmul]

end Deviation

end TauCeti

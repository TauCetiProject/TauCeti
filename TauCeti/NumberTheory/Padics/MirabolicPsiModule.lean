/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Basic
public import TauCeti.GroupTheory.SpecificGroups.Affine.Padic

/-!
# `(P(ℤ_p), ψ)`-modules and the `P(ℚ_p)`-module `M ⊠ ℚ_p`

Write `P(R) = {(a b; 0 1)}` for the mirabolic group over a ring `R`, realised as the affine group
`TauCeti.AffineGroup R`: the element `(b, a)` is the matrix `(a b; 0 1)`, acting on `R` by
`x ↦ b + a x`. Put `φ = diag(p, 1)`, the dilation `x ↦ p x` of `ℚ_p`
(`TauCeti.AffineGroup.padicPhi`).

Following Colmez, a `(P(ℤ_p), ψ)`-module is an `R`-module `M` with an action of `P(ℤ_p)` and an
operator `ψ` satisfying `ψ ∘ (p b, a) = (b, a) ∘ ψ`: `ψ` commutes with the diagonal units and
`ψ (u(p b) z) = u(b) ψ(z)` for the unipotent `u(b) = (1 b; 0 1)`. The relation says that
`ψ` intertwines the action of `h ∈ P(ℤ_p)` with that of `φ h φ⁻¹`, and is the abstract form of
the operator `ψ` on measures on `ℤ_p` (restriction to `pℤ_p` followed by `p x ↦ x`), and on
étale `(φ, Γ)`-modules.

The module `M ⊠ ℚ_p` consists of the `ψ`-compatible sequences `(x_n)_{n ≥ 0}`, those with
`ψ (x_{n + 1}) = x_n`. For measures, `x_n` is the restriction of a measure on `ℚ_p` to
`p^{-n} ℤ_p`, transported to `ℤ_p` by `x ↦ p^n x`. This module carries an action of `P(ℚ_p)` in
which the diagonal units act coordinatewise, `diag(p^k, 1)` acts by the shift `x_n ↦ x_{n + k}`
and `u(b)` by `x_n ↦ u(p^n b) x_n` once `p^n b ∈ ℤ_p`. In general,
if `φ^m g φ^{-l} = h` lies in `P(ℤ_p)`, then the `m`-th coordinate of `g x` is `h x_l`, and the
coordinates of index `n ≤ m` are recovered by applying `ψ^(m - n)`
(`TauCeti.MirabolicPsiModule.boxtimesRep_apply_coe`).

We work with an arbitrary commutative semiring of coefficients and do not impose Colmez's
topological hypotheses or the surjectivity of `ψ` in the definition; they are hypotheses of the
statements that use them.

## Main definitions

* `TauCeti.MirabolicPsiModule`: a `P(ℤ_p)`-representation with an operator `ψ` satisfying
  `ψ ∘ (p b, a) = (b, a) ∘ ψ`.
* `TauCeti.MirabolicPsiModule.boxtimesQp`: the module `M ⊠ ℚ_p` of `ψ`-compatible sequences.
* `TauCeti.MirabolicPsiModule.boxtimesRep`: the representation of `P(ℚ_p)` on `M ⊠ ℚ_p`.

## Main results

* `TauCeti.MirabolicPsiModule.boxtimesRep_apply_coe`: the coordinates of `g x`.
* `TauCeti.MirabolicPsiModule.boxtimesRep_padicPhi_pow_apply_coe`: `diag(p^k, 1)` is the shift.
* `TauCeti.MirabolicPsiModule.boxtimesRep_padicPhi_inv_apply_coe_zero`: the zeroth coordinate
  of `diag(p⁻¹, 1) x` is `ψ (x_0)`.
* `TauCeti.MirabolicPsiModule.boxtimesRep_map_apply_coe`: `h ∈ P(ℤ_p)` acts on `x_n` through
  `φ^n h φ^{-n}`; in particular the zeroth coordinate is `P(ℤ_p)`-equivariant.
* `TauCeti.MirabolicPsiModule.boxtimesQp_coe_zero_surjective`: if `ψ` is surjective, every
  element of `M` is the zeroth coordinate of an element of `M ⊠ ℚ_p`.
* `TauCeti.MirabolicPsiModule.continuous_boxtimesRep`: for continuous `ψ` and a continuous
  `P(ℤ_p)`-action, each element of `P(ℚ_p)` acts continuously on `M ⊠ ℚ_p` with the inverse-limit
  topology.

## References

* P. Colmez, *Représentations de `GL₂(ℚ_p)` et `(φ, Γ)`-modules*, Astérisque 330 (2010),
  Introduction §5 (Proposition 0.5) and §I.3.3.
-/

public noncomputable section

namespace TauCeti

open AffineGroup

variable (p : ℕ) [Fact p.Prime]

/-- A `(P(ℤ_p), ψ)`-module in the sense of Colmez, without topology: a representation `ρ` of
`P(ℤ_p)` on an `R`-module `M` and an `R`-linear operator `ψ` on `M` with
`ψ ∘ (p b, a) = (b, a) ∘ ψ`, i.e. `ψ` commutes with the diagonal units and
`ψ (u(p b) z) = u(b) ψ(z)`. -/
@[ext]
structure MirabolicPsiModule (R M : Type*) [CommSemiring R] [AddCommMonoid M] [Module R M] where
  /-- The action of `P(ℤ_p)`. -/
  ρ : Representation R (AffineGroup ℤ_[p]) M
  /-- The operator `ψ`. -/
  ψ : M →ₗ[R] M
  /-- `ψ ∘ (p b, a) = (b, a) ∘ ψ`. -/
  ψ_comp_ρ (b : ℤ_[p]) (a : ℤ_[p]ˣ) :
    ψ ∘ₗ ρ ⟨.ofAdd ((p : ℤ_[p]) * b), a⟩ = ρ ⟨.ofAdd b, a⟩ ∘ₗ ψ

namespace MirabolicPsiModule

variable {p} {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
variable (D : MirabolicPsiModule p R M)

/-- `ψ (ρ(p b, a) z) = ρ(b, a) (ψ z)`. -/
theorem ψ_ρ_apply (b : ℤ_[p]) (a : ℤ_[p]ˣ) (z : M) :
    D.ψ (D.ρ ⟨.ofAdd ((p : ℤ_[p]) * b), a⟩ z) = D.ρ ⟨.ofAdd b, a⟩ (D.ψ z) :=
  LinearMap.congr_fun (D.ψ_comp_ρ b a) z

/-- The module `M ⊠ ℚ_p` of `ψ`-compatible sequences `(x_n)_{n ≥ 0}`, those with
`ψ (x_{n + 1}) = x_n`. -/
def boxtimesQp : Submodule R (ℕ → M) where
  carrier := {x | ∀ n, D.ψ (x (n + 1)) = x n}
  add_mem' hx hy n := by simp [hx n, hy n]
  zero_mem' n := by simp
  smul_mem' c x hx n := by simp [hx n]

@[simp]
theorem mem_boxtimesQp {x : ℕ → M} : x ∈ D.boxtimesQp ↔ ∀ n, D.ψ (x (n + 1)) = x n :=
  Iff.rfl

variable {D}

/-- The coordinates of an element of `M ⊠ ℚ_p` are `ψ`-compatible. -/
@[simp]
theorem ψ_boxtimesQp_coe_succ (x : D.boxtimesQp) (n : ℕ) :
    D.ψ ((x : ℕ → M) (n + 1)) = (x : ℕ → M) n :=
  x.property n

/-- `ψ^k (x_{n + k}) = x_n` for `x ∈ M ⊠ ℚ_p`. -/
theorem ψ_pow_boxtimesQp_coe_add (x : D.boxtimesQp) (n k : ℕ) :
    (D.ψ ^ k) ((x : ℕ → M) (n + k)) = (x : ℕ → M) n := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, mul_apply_eq_comp, ← add_assoc, ψ_boxtimesQp_coe_succ, ih]

/-- `ψ^(m - n) (x_m) = x_n` for `n ≤ m`. -/
theorem ψ_pow_sub_boxtimesQp_coe (x : D.boxtimesQp) {n m : ℕ} (hnm : n ≤ m) :
    (D.ψ ^ (m - n)) ((x : ℕ → M) m) = (x : ℕ → M) n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
  simpa using ψ_pow_boxtimesQp_coe_add x n k

/-- An element of `M ⊠ ℚ_p` is determined by its coordinates of large index. -/
theorem boxtimesQp_ext {x y : D.boxtimesQp} (N : ℕ)
    (h : ∀ n, N ≤ n → (x : ℕ → M) n = (y : ℕ → M) n) : x = y := by
  refine Subtype.ext (funext fun n ↦ ?_)
  rw [← ψ_pow_boxtimesQp_coe_add x n N, ← ψ_pow_boxtimesQp_coe_add y n N, h _ (by omega)]

/-- If `ψ` is surjective, every element of `M` is the zeroth coordinate of an element of
`M ⊠ ℚ_p`. -/
theorem boxtimesQp_coe_zero_surjective (hψ : Function.Surjective D.ψ) :
    Function.Surjective fun x : D.boxtimesQp ↦ (x : ℕ → M) 0 := by
  intro z
  refine ⟨⟨fun n ↦ (Function.surjInv hψ)^[n] z, fun n ↦ ?_⟩, rfl⟩
  simp only [Function.iterate_succ_apply', Function.surjInv_eq hψ]

/-! ### The action of `P(ℚ_p)` -/

/-- Raising the level: if `φ^m g φ^{-l}` is `h = (b, a)`, then `φ^(m + 1) g φ^(-(l + 1))` is
`(p b, a)`. -/
private def raise (h : AffineGroup ℤ_[p]) : AffineGroup ℤ_[p] :=
  ⟨.ofAdd ((p : ℤ_[p]) * h.left.toAdd), h.right⟩

/-- Raising the level is conjugation by `φ`. -/
private theorem map_raise (h : AffineGroup ℤ_[p]) :
    map PadicInt.Coe.ringHom (raise h) =
      padicPhi p * map PadicInt.Coe.ringHom h * (padicPhi p)⁻¹ := by
  ext <;> simp [raise]

private theorem map_raise_iterate (h : AffineGroup ℤ_[p]) (k : ℕ) :
    map PadicInt.Coe.ringHom ((raise^[k]) h) =
      padicPhi p ^ k * map PadicInt.Coe.ringHom h * (padicPhi p ^ k)⁻¹ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', map_raise, ih]
    group

/-- Raising the level `k` times turns `φ^m g φ^{-l} = h` into
`φ^(m + k) g φ^(-(l + k)) = raise^[k] h`. -/
private theorem map_raise_iterate_of_eq {g : AffineGroup ℚ_[p]} {m l : ℕ}
    {h : AffineGroup ℤ_[p]}
    (hh : map PadicInt.Coe.ringHom h = padicPhi p ^ m * g * (padicPhi p ^ l)⁻¹) (k : ℕ) :
    map PadicInt.Coe.ringHom ((raise^[k]) h) =
      padicPhi p ^ (m + k) * g * (padicPhi p ^ (l + k))⁻¹ := by
  rw [map_raise_iterate, hh]
  group

private theorem ψ_ρ_raise_apply (h : AffineGroup ℤ_[p]) (z : M) :
    D.ψ (D.ρ (raise h) z) = D.ρ h (D.ψ z) :=
  D.ψ_ρ_apply h.left.toAdd h.right z

/-- The candidate `n`-th coordinate of `g x` computed at the level `(m, l)` with
`φ^m g φ^{-l} = h`. -/
private def coordAt (x : ℕ → M) (n m l : ℕ) (h : AffineGroup ℤ_[p]) : M :=
  (D.ψ ^ (m - n)) (D.ρ h (x l))

private theorem coordAt_raise_iterate (x : D.boxtimesQp) {n m : ℕ} (hnm : n ≤ m) (l : ℕ)
    (h : AffineGroup ℤ_[p]) (k : ℕ) :
    coordAt (D := D) x n (m + k) (l + k) ((raise^[k]) h) = coordAt (D := D) x n m l h := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [← ih, coordAt, coordAt, show m + (k + 1) - n = (m + k - n) + 1 by omega, pow_succ,
      mul_apply_eq_comp, Function.iterate_succ_apply', ψ_ρ_raise_apply, ← add_assoc,
      ψ_boxtimesQp_coe_succ]

/-- The level `l` and the integral element at a given level `m` are unique. -/
private theorem eq_of_map_eq {g : AffineGroup ℚ_[p]} {m l l' : ℕ} {h h' : AffineGroup ℤ_[p]}
    (hh : map PadicInt.Coe.ringHom h = padicPhi p ^ m * g * (padicPhi p ^ l)⁻¹)
    (hh' : map PadicInt.Coe.ringHom h' = padicPhi p ^ m * g * (padicPhi p ^ l')⁻¹) :
    l = l' ∧ h = h' := by
  have hl : l = l' := by
    refine eq_of_map_eq_padicPhi_pow_mul_inv_pow (h := h⁻¹ * h') ?_
    rw [map_mul, map_inv, hh, hh']
    group
  subst hl
  exact ⟨rfl, map_injective (fun _ _ ↦ PadicInt.ext) (hh.trans hh'.symm)⟩

/-- The candidate coordinates agree at all admissible levels. -/
private theorem coordAt_eq (x : D.boxtimesQp) {g : AffineGroup ℚ_[p]} {n m l m' l' : ℕ}
    {h h' : AffineGroup ℤ_[p]} (hnm : n ≤ m) (hnm' : n ≤ m')
    (hh : map PadicInt.Coe.ringHom h = padicPhi p ^ m * g * (padicPhi p ^ l)⁻¹)
    (hh' : map PadicInt.Coe.ringHom h' = padicPhi p ^ m' * g * (padicPhi p ^ l')⁻¹) :
    coordAt (D := D) x n m l h = coordAt (D := D) x n m' l' h' := by
  rw [← coordAt_raise_iterate x hnm l h m', ← coordAt_raise_iterate x hnm' l' h' m]
  have h₂ := map_raise_iterate_of_eq hh' m
  rw [add_comm m' m] at h₂
  obtain ⟨hl, hh⟩ := eq_of_map_eq (map_raise_iterate_of_eq hh m') h₂
  rw [hl, hh, add_comm m m']

/-- A choice of admissible level for `g` at least `n`. -/
private def level (g : AffineGroup ℚ_[p]) (n : ℕ) : ℕ × ℕ × AffineGroup ℤ_[p] :=
  let e := exists_map_eq_padicPhi_pow_mul_mul_inv_pow g n
  (e.choose, e.choose_spec.choose, e.choose_spec.choose_spec.choose)

private theorem level_spec (g : AffineGroup ℚ_[p]) (n : ℕ) :
    n ≤ (level g n).1 ∧ map PadicInt.Coe.ringHom (level g n).2.2 =
      padicPhi p ^ (level g n).1 * g * (padicPhi p ^ (level g n).2.1)⁻¹ :=
  (exists_map_eq_padicPhi_pow_mul_mul_inv_pow g n).choose_spec.choose_spec.choose_spec

/-- The sequence `g x`, computed at the chosen levels. -/
private def actSeq (g : AffineGroup ℚ_[p]) (x : D.boxtimesQp) (n : ℕ) : M :=
  coordAt (D := D) x n (level g n).1 (level g n).2.1 (level g n).2.2

private theorem actSeq_eq (g : AffineGroup ℚ_[p]) (x : D.boxtimesQp) {n m l : ℕ}
    {h : AffineGroup ℤ_[p]} (hnm : n ≤ m)
    (hh : map PadicInt.Coe.ringHom h = padicPhi p ^ m * g * (padicPhi p ^ l)⁻¹) :
    actSeq g x n = (D.ψ ^ (m - n)) (D.ρ h ((x : ℕ → M) l)) :=
  coordAt_eq x (level_spec g n).1 hnm (level_spec g n).2 hh

private theorem actSeq_eq_of_eq (g : AffineGroup ℚ_[p]) (x : D.boxtimesQp) {n l : ℕ}
    {h : AffineGroup ℤ_[p]}
    (hh : map PadicInt.Coe.ringHom h = padicPhi p ^ n * g * (padicPhi p ^ l)⁻¹) :
    actSeq g x n = D.ρ h ((x : ℕ → M) l) := by
  rw [actSeq_eq g x le_rfl hh, Nat.sub_self, pow_zero, one_apply_eq_self]

private theorem actSeq_mem (g : AffineGroup ℚ_[p]) (x : D.boxtimesQp) :
    actSeq g x ∈ D.boxtimesQp := by
  intro n
  obtain ⟨m, l, h, hnm, hh⟩ := exists_map_eq_padicPhi_pow_mul_mul_inv_pow g (n + 1)
  rw [actSeq_eq g x hnm hh, actSeq_eq g x (by omega : n ≤ m) hh, ← mul_apply_eq_comp,
    ← pow_succ', show m - (n + 1) + 1 = m - n by omega]

/-- The action of `g ∈ P(ℚ_p)` on `M ⊠ ℚ_p` as a linear map. -/
private def actLinear (g : AffineGroup ℚ_[p]) : D.boxtimesQp →ₗ[R] D.boxtimesQp where
  toFun x := ⟨actSeq g x, actSeq_mem g x⟩
  map_add' x y := Subtype.ext <| funext fun n ↦ by
    simp [actSeq, coordAt]
  map_smul' c x := Subtype.ext <| funext fun n ↦ by
    simp [actSeq, coordAt]

private theorem coe_actLinear (g : AffineGroup ℚ_[p]) (x : D.boxtimesQp) :
    (actLinear g x : ℕ → M) = actSeq g x :=
  rfl

private theorem actLinear_one : actLinear (D := D) 1 = 1 := by
  ext x n : 3
  have h1 : map PadicInt.Coe.ringHom (1 : AffineGroup ℤ_[p]) =
      padicPhi p ^ n * 1 * (padicPhi p ^ n)⁻¹ := by group; simp
  rw [one_apply_eq_self, coe_actLinear, actSeq_eq_of_eq 1 x h1, map_one, one_apply_eq_self]

private theorem actLinear_mul (g g' : AffineGroup ℚ_[p]) :
    actLinear (D := D) (g * g') = actLinear g * actLinear g' := by
  ext x n : 3
  obtain ⟨m, l, h, hnm, hh⟩ := exists_map_eq_padicPhi_pow_mul_mul_inv_pow g n
  obtain ⟨m', l', h', -, hh'⟩ := exists_map_eq_padicPhi_pow_mul_mul_inv_pow g' 0
  have hg := map_raise_iterate_of_eq hh m'
  have hg' := map_raise_iterate_of_eq hh' l
  rw [add_comm m' l] at hg'
  have hgg' : map PadicInt.Coe.ringHom ((raise^[m']) h * (raise^[l]) h') =
      padicPhi p ^ (m + m') * (g * g') * (padicPhi p ^ (l' + l))⁻¹ := by
    rw [map_mul, hg, hg']
    group
  rw [mul_apply_eq_comp, coe_actLinear, coe_actLinear,
    actSeq_eq _ x (by omega : n ≤ m + m') hgg', actSeq_eq g _ (by omega : n ≤ m + m') hg,
    coe_actLinear, actSeq_eq_of_eq g' x hg', map_mul, mul_apply_eq_comp]

variable (D) in
/-- The representation of `P(ℚ_p)` on `M ⊠ ℚ_p`: if `φ^m g φ^{-l} = h` lies in `P(ℤ_p)`, the
`m`-th coordinate of `g x` is `h x_l` (`TauCeti.MirabolicPsiModule.boxtimesRep_apply_coe`). -/
def boxtimesRep : Representation R (AffineGroup ℚ_[p]) D.boxtimesQp where
  toFun := actLinear
  map_one' := actLinear_one
  map_mul' := actLinear_mul

/-- **The coordinates of `g x`**: if `φ^m g φ^{-l} = h` for some `h ∈ P(ℤ_p)`, then the `n`-th
coordinate of `g x`, for `n ≤ m`, is `ψ^(m - n) (h x_l)`. -/
theorem boxtimesRep_apply_coe (g : AffineGroup ℚ_[p]) (x : D.boxtimesQp) {n m l : ℕ}
    {h : AffineGroup ℤ_[p]} (hnm : n ≤ m)
    (hh : map PadicInt.Coe.ringHom h = padicPhi p ^ m * g * (padicPhi p ^ l)⁻¹) :
    (D.boxtimesRep g x : ℕ → M) n = (D.ψ ^ (m - n)) (D.ρ h ((x : ℕ → M) l)) :=
  actSeq_eq g x hnm hh

/-- If `φ^n g φ^{-l} = h` for some `h ∈ P(ℤ_p)`, then the `n`-th coordinate of `g x` is
`h x_l`. -/
theorem boxtimesRep_apply_coe_of_eq (g : AffineGroup ℚ_[p]) (x : D.boxtimesQp) {n l : ℕ}
    {h : AffineGroup ℤ_[p]}
    (hh : map PadicInt.Coe.ringHom h = padicPhi p ^ n * g * (padicPhi p ^ l)⁻¹) :
    (D.boxtimesRep g x : ℕ → M) n = D.ρ h ((x : ℕ → M) l) :=
  actSeq_eq_of_eq g x hh

/-- **`diag(p^k, 1)` acts by the shift** `x_n ↦ x_{n + k}`. -/
@[simp]
theorem boxtimesRep_padicPhi_pow_apply_coe (k : ℕ) (x : D.boxtimesQp) (n : ℕ) :
    ((D.boxtimesRep (padicPhi p) ^ k) x : ℕ → M) n = (x : ℕ → M) (n + k) := by
  rw [← map_pow,
    boxtimesRep_apply_coe_of_eq _ x (h := 1) (l := n + k) (by rw [pow_add]; group; simp), map_one,
    one_apply_eq_self]

/-- `diag(p, 1)` acts by the shift `x_n ↦ x_{n + 1}`. -/
@[simp]
theorem boxtimesRep_padicPhi_apply_coe (x : D.boxtimesQp) (n : ℕ) :
    (D.boxtimesRep (padicPhi p) x : ℕ → M) n = (x : ℕ → M) (n + 1) := by
  simpa using boxtimesRep_padicPhi_pow_apply_coe 1 x n

/-- `diag(p⁻¹, 1)` shifts the coordinates of positive index: the `(n + 1)`-st coordinate of
`φ⁻¹ x` is `x_n`. -/
@[simp]
theorem boxtimesRep_padicPhi_inv_apply_coe_succ (x : D.boxtimesQp) (n : ℕ) :
    (D.boxtimesRep (padicPhi p)⁻¹ x : ℕ → M) (n + 1) = (x : ℕ → M) n := by
  rw [boxtimesRep_apply_coe_of_eq _ x (h := 1) (l := n) (by rw [pow_succ]; group; simp), map_one,
    one_apply_eq_self]

/-- The zeroth coordinate of `diag(p⁻¹, 1) x` is `ψ (x_0)`. -/
@[simp]
theorem boxtimesRep_padicPhi_inv_apply_coe_zero (x : D.boxtimesQp) :
    (D.boxtimesRep (padicPhi p)⁻¹ x : ℕ → M) 0 = D.ψ ((x : ℕ → M) 0) := by
  rw [boxtimesRep_apply_coe _ x (Nat.zero_le 1) (h := 1) (l := 0) (by group; simp), map_one]
  simp

/-- **`h ∈ P(ℤ_p)` acts on `x_n` through `φ^n h φ^{-n}`**: for `h = (b, a)`, the `n`-th
coordinate of `h x` is `(p^n b, a) x_n`. -/
theorem boxtimesRep_map_apply_coe (b : ℤ_[p]) (a : ℤ_[p]ˣ) (x : D.boxtimesQp) (n : ℕ) :
    (D.boxtimesRep (map PadicInt.Coe.ringHom ⟨.ofAdd b, a⟩) x : ℕ → M) n =
      D.ρ ⟨.ofAdd ((p : ℤ_[p]) ^ n * b), a⟩ ((x : ℕ → M) n) := by
  have hraise : ((raise^[n]) ⟨.ofAdd b, a⟩ : AffineGroup ℤ_[p]) =
      ⟨.ofAdd ((p : ℤ_[p]) ^ n * b), a⟩ := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply', ih, raise]
      simp [pow_succ', mul_assoc]
  rw [boxtimesRep_apply_coe_of_eq _ x (map_raise_iterate _ n), hraise]

/-- The zeroth coordinate `M ⊠ ℚ_p → M` is `P(ℤ_p)`-equivariant. -/
@[simp]
theorem boxtimesRep_map_apply_coe_zero (h : AffineGroup ℤ_[p]) (x : D.boxtimesQp) :
    (D.boxtimesRep (map PadicInt.Coe.ringHom h) x : ℕ → M) 0 = D.ρ h ((x : ℕ → M) 0) := by
  simpa using boxtimesRep_map_apply_coe (D := D) h.left.toAdd h.right x 0

/-- The translation `u(b) = (1 b; 0 1)` with `p^n b ∈ ℤ_p` acts on `x_n` through
`u(p^n b)`. -/
theorem boxtimesRep_inl_apply_coe (b : ℚ_[p]) (x : D.boxtimesQp) (n : ℕ) (c : ℤ_[p])
    (hc : (c : ℚ_[p]) = (p : ℚ_[p]) ^ n * b) :
    (D.boxtimesRep (SemidirectProduct.inl (.ofAdd b)) x : ℕ → M) n =
      D.ρ (SemidirectProduct.inl (.ofAdd c)) ((x : ℕ → M) n) := by
  have hh : map PadicInt.Coe.ringHom (SemidirectProduct.inl (.ofAdd c) : AffineGroup ℤ_[p]) =
      padicPhi p ^ n * SemidirectProduct.inl (.ofAdd b) * (padicPhi p ^ n)⁻¹ := by
    ext
    · rw [toAdd_padicPhi_pow_mul_mul_inv_pow_left]
      simpa using hc
    · rw [coe_padicPhi_pow_mul_mul_inv_pow_right]
      simp [(Fact.out : p.Prime).ne_zero]
  exact boxtimesRep_apply_coe_of_eq _ x hh

/-- If `ψ` and the action of `P(ℤ_p)` are continuous, every element of `P(ℚ_p)` acts continuously
on `M ⊠ ℚ_p`, with the topology induced from the product topology on sequences. -/
theorem continuous_boxtimesRep [TopologicalSpace M] (hψ : Continuous D.ψ)
    (hρ : ∀ h, Continuous (D.ρ h)) (g : AffineGroup ℚ_[p]) :
    Continuous (D.boxtimesRep g) := by
  refine continuous_induced_rng.mpr (continuous_pi fun n ↦ ?_)
  obtain ⟨m, l, h, hnm, hh⟩ := exists_map_eq_padicPhi_pow_mul_mul_inv_pow g n
  have hcont : Continuous fun x : D.boxtimesQp ↦ (D.ψ ^ (m - n)) (D.ρ h ((x : ℕ → M) l)) := by
    simp only [pow_apply_eq_iterate]
    exact (hψ.iterate _).comp ((hρ h).comp ((continuous_apply l).comp continuous_subtypeVal))
  exact hcont.congr fun x ↦ (boxtimesRep_apply_coe g x hnm hh).symm

end MirabolicPsiModule

end TauCeti

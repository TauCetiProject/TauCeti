/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Logic.Equiv.Prod

/-!
# The closing defect of broken orbits of a chain of strip maps

Let `F_0, F_1, …, F_(n-1)` be maps of the plane, with components `F_k = (X_k, Y_k)`, for instance
the twist factors of a lift of an area-preserving diffeomorphism of the annulus
`(ℝ / ℤ) × [0, 1]` to the strip `ℝ × [0, 1]`. A **broken orbit** of the chain starts at a
position `x_0` and is driven by freely chosen incoming momenta `y_0, …, y_(n-1)`: its successive
positions are

`x_(k+1) = X_k(x_k, y_k)`

(`TauCeti.stripBrokenOrbitEnd F n x y` is the last position `x_n`). The momenta need not match the
outgoing momenta `Y_k(x_k, y_k)` of the previous factor, so the broken orbit is not an orbit of the
chain in general. When they do match, it is one, and its last position is that of the orbit
(`TauCeti.stripBrokenOrbitEnd_eq_of_orbit`). The **closing defect**

`G(x_0, y) = x_n - x_0`

(`TauCeti.stripClosingDefect F n x y`) measures how far the broken orbit is from returning to its
starting position. Its zero set is the set of broken orbits closing up, which is the configuration
space of the finite-action proof of the Poincaré–Birkhoff theorem in the coordinates
`(x_0, y_0, …, y_(n-1))`.

Suppose that on a set `J` of heights every `X_k` is increasing in `x`, and increasing in `y` for
the factors `k` in a set `P` of *positive* indices, decreasing for the others. Then the end of a
broken orbit is monotone in its starting position and in its inputs with these signs, and so is
the defect in its inputs: if `y ≤ y'` in the coordinates of `P` and `y' ≤ y` in the others, then
`G(x, y) ≤ G(x, y')` (`TauCeti.stripClosingDefect_le_stripClosingDefect`). When the monotonicity of
the factors is strict, so is that of the defect unless `y = y'`
(`TauCeti.stripClosingDefect_lt_stripClosingDefect`). In particular, with the momenta of the
negative factors held fixed, it is strictly increasing in the momenta of the positive ones
(`TauCeti.strictMonoOn_stripClosingDefect`).

If every factor maps a line `y = c` into itself, the broken orbit with all inputs `c` is the orbit
of `(x, c)` under the chain (`TauCeti.stripBrokenOrbitEnd_const_eq_of_orbit`), so its defect is the
displacement `F^x(x, c) - x` of the composite `F = F_(n-1) ∘ ⋯ ∘ F_0` along that line. For a lift
with strictly negative displacement on the lower boundary line and strictly positive displacement
on the upper one, the signs of the defect therefore propagate to the faces of the cube of inputs:
`G < 0` where the positive inputs take the lower value and `G > 0` where they take the upper
value, whatever the negative inputs are (`TauCeti.stripClosingDefect_neg`,
`TauCeti.stripClosingDefect_pos`). So for fixed `x` and fixed negative inputs, the defect is
strictly increasing along the diagonal of the cube of positive inputs, negative at its lower
vertex and positive at its upper one.

The defect is invariant under translating the starting position by a deck translation commuting
with every factor (`TauCeti.stripClosingDefect_add`), and it is jointly `C^m` in the starting
position and the inputs when every `X_k` is (`TauCeti.contDiffOn_stripClosingDefect`). None of the
statements needs the factors to preserve area.

## Main definitions

* `TauCeti.stripBrokenOrbitEnd F n x y`: the last position of the broken orbit.
* `TauCeti.stripClosingDefect F n x y`: the closing defect `x_n - x_0`.

## Main results

* `TauCeti.stripBrokenOrbitEnd_eq_of_orbit`: an unbroken orbit ends where the orbit does.
* `TauCeti.stripBrokenOrbitEnd_le_stripBrokenOrbitEnd`,
  `TauCeti.stripBrokenOrbitEnd_lt_stripBrokenOrbitEnd`: signed monotonicity of the end of a broken
  orbit in its starting position and its inputs.
* `TauCeti.stripClosingDefect_le_stripClosingDefect`,
  `TauCeti.stripClosingDefect_lt_stripClosingDefect`: signed monotonicity of the defect in the
  inputs.
* `TauCeti.strictMonoOn_stripClosingDefect`: strict monotonicity in the positive inputs.
* `TauCeti.stripClosingDefect_neg`, `TauCeti.stripClosingDefect_pos`: the signs on the lower and
  upper faces of the cube of positive inputs.
* `TauCeti.stripClosingDefect_add`: invariance under deck translations.
* `TauCeti.contDiffOn_stripClosingDefect`: joint smoothness.
* `TauCeti.stripClosingDefect_affineShear_shear`: the defect `u - (6 v + 1) / 8` of the chain of
  the affine shear `(x, y) ↦ (x - (6 y + 1) / 8, y)` followed by the shear `(x, y) ↦ (x + y, y)`,
  whose composite is `(x, y) ↦ (x + (2 y - 1) / 8, y)`.

## References

* C. Conley and E. Zehnder, *The Birkhoff–Lewis fixed point theorem and a conjecture of
  V. I. Arnold*, Invent. Math. 73 (1983), 33–49.
-/

public section

open Set

namespace TauCeti

/-- The last position of a **broken orbit** of the chain of maps `F 0, F 1, …, F (n - 1)` of the
plane. Starting from the position `x`, the incoming momentum `y k` at step `k` is chosen freely,
and the next position is the first component of `F k (x_k, y k)`; the result is the position `x_n`
after `n` steps. -/
def stripBrokenOrbitEnd (F : ℕ → ℝ × ℝ → ℝ × ℝ) : (n : ℕ) → ℝ → (Fin n → ℝ) → ℝ
  | 0, x, _ => x
  | n + 1, x, y => (F n (stripBrokenOrbitEnd F n x (Fin.init y), y (Fin.last n))).1

/-- The **closing defect** `x_n - x_0` of the broken orbit of the chain `F 0, …, F (n - 1)` which
starts at the position `x` and has incoming momenta `y`. It vanishes exactly when the broken orbit
returns to its starting position. -/
def stripClosingDefect (F : ℕ → ℝ × ℝ → ℝ × ℝ) (n : ℕ) (x : ℝ) (y : Fin n → ℝ) : ℝ :=
  stripBrokenOrbitEnd F n x y - x

variable {F : ℕ → ℝ × ℝ → ℝ × ℝ} {n : ℕ} {x : ℝ} {J : Set ℝ} {P : Set ℕ}

@[simp]
theorem stripBrokenOrbitEnd_zero (F : ℕ → ℝ × ℝ → ℝ × ℝ) (x : ℝ) (y : Fin 0 → ℝ) :
    stripBrokenOrbitEnd F 0 x y = x :=
  (rfl)

@[simp]
theorem stripBrokenOrbitEnd_succ (F : ℕ → ℝ × ℝ → ℝ × ℝ) (n : ℕ) (x : ℝ) (y : Fin (n + 1) → ℝ) :
    stripBrokenOrbitEnd F (n + 1) x y =
      (F n (stripBrokenOrbitEnd F n x (Fin.init y), y (Fin.last n))).1 :=
  (rfl)

theorem stripClosingDefect_def (F : ℕ → ℝ × ℝ → ℝ × ℝ) (n : ℕ) (x : ℝ) (y : Fin n → ℝ) :
    stripClosingDefect F n x y = stripBrokenOrbitEnd F n x y - x :=
  (rfl)

@[simp]
theorem stripClosingDefect_zero (F : ℕ → ℝ × ℝ → ℝ × ℝ) (x : ℝ) (y : Fin 0 → ℝ) :
    stripClosingDefect F 0 x y = 0 := by
  rw [stripClosingDefect_def, stripBrokenOrbitEnd_zero, sub_self]

/-- The broken orbit closes up exactly when its closing defect vanishes. -/
theorem stripClosingDefect_eq_zero_iff {y : Fin n → ℝ} :
    stripClosingDefect F n x y = 0 ↔ stripBrokenOrbitEnd F n x y = x :=
  sub_eq_zero

/-! ### Unbroken orbits -/

/-- **An unbroken orbit ends where the orbit does.** If `z` is an orbit of the chain,
`z (k + 1) = F k (z k)` for `k < n`, then the broken orbit starting at the position of `z 0` with
the momenta of `z` as inputs ends at the position of `z n`. -/
theorem stripBrokenOrbitEnd_eq_of_orbit {z : ℕ → ℝ × ℝ}
    (hz : ∀ k < n, z (k + 1) = F k (z k)) :
    stripBrokenOrbitEnd F n (z 0).1 (fun i ↦ (z i).2) = (z n).1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hinit : (Fin.init fun i : Fin (n + 1) ↦ (z i).2) = fun i : Fin n ↦ (z i).2 := by
      ext i
      simp [Fin.init]
    rw [stripBrokenOrbitEnd_succ, hinit, ih fun k hk ↦ hz k (by omega), Fin.val_last,
      hz n n.lt_succ_self]

/-- If every factor maps the line `y = c` into itself, the broken orbit with all inputs `c` is the
orbit of `(x, c)`: it ends at the position of the image of `(x, c)` under the chain. -/
theorem stripBrokenOrbitEnd_const_eq_of_orbit {c : ℝ} (hc : ∀ k < n, ∀ x, (F k (x, c)).2 = c)
    {z : ℕ → ℝ × ℝ} (hz : ∀ k < n, z (k + 1) = F k (z k)) (hz0 : z 0 = (x, c)) :
    stripBrokenOrbitEnd F n x (fun _ ↦ c) = (z n).1 := by
  have hline : ∀ k ≤ n, (z k).2 = c := by
    intro k hk
    induction k with
    | zero => rw [hz0]
    | succ k ih =>
      rw [hz k (by omega), ← Prod.mk.eta (p := z k), ih (by omega)]
      exact hc k (by omega) _
  have h := stripBrokenOrbitEnd_eq_of_orbit hz
  rw [hz0] at h
  rw [← h]
  congr 1
  funext i
  exact (hline i i.is_lt.le).symm

/-! ### Monotonicity -/

/-- **Signed monotonicity of the end of a broken orbit.** Suppose that on the set `J` of heights
every factor is increasing in the position, and increasing in the momentum for the factors in `P`,
decreasing for the others. If the starting position `x'` dominates `x`, and the inputs `y'`
dominate `y` in the coordinates of `P` and are dominated by `y` in the others, then the broken
orbit from `x` with inputs `y` ends at most where the one from `x'` with inputs `y'` does. -/
theorem stripBrokenOrbitEnd_le_stripBrokenOrbitEnd
    (hx : ∀ k < n, ∀ t ∈ J, Monotone fun x ↦ (F k (x, t)).1)
    (hP : ∀ k < n, k ∈ P → ∀ x, MonotoneOn (fun t ↦ (F k (x, t)).1) J)
    (hN : ∀ k < n, k ∉ P → ∀ x, AntitoneOn (fun t ↦ (F k (x, t)).1) J)
    {x x' : ℝ} (hxx' : x ≤ x') {y y' : Fin n → ℝ} (hy : ∀ i, y i ∈ J) (hy' : ∀ i, y' i ∈ J)
    (hyy' : ∀ i : Fin n, ((i : ℕ) ∈ P → y i ≤ y' i) ∧ ((i : ℕ) ∉ P → y' i ≤ y i)) :
    stripBrokenOrbitEnd F n x y ≤ stripBrokenOrbitEnd F n x' y' := by
  induction n with
  | zero => exact hxx'
  | succ n ih =>
    have hle := ih (y := Fin.init y) (y' := Fin.init y') (fun k hk ↦ hx k (by omega))
      (fun k hk ↦ hP k (by omega)) (fun k hk ↦ hN k (by omega)) (fun i ↦ hy i.castSucc)
      (fun i ↦ hy' i.castSucc) (fun i ↦ by simpa [Fin.init] using hyy' i.castSucc)
    have hlast := hyy' (Fin.last n)
    simp only [Fin.val_last] at hlast
    rw [stripBrokenOrbitEnd_succ, stripBrokenOrbitEnd_succ]
    refine (hx n n.lt_succ_self _ (hy _) hle).trans ?_
    -- The last momentum step, with the sign of the last factor.
    by_cases hn : n ∈ P
    · exact hP n n.lt_succ_self hn _ (hy _) (hy' _) (hlast.1 hn)
    · exact hN n n.lt_succ_self hn _ (hy' _) (hy _) (hlast.2 hn)

/-- **Strict signed monotonicity of the end of a broken orbit.** Under the hypotheses of
`TauCeti.stripBrokenOrbitEnd_le_stripBrokenOrbitEnd` with strict monotonicity of the factors, the
inequality is strict as soon as the starting positions or the families of inputs differ. -/
theorem stripBrokenOrbitEnd_lt_stripBrokenOrbitEnd
    (hx : ∀ k < n, ∀ t ∈ J, StrictMono fun x ↦ (F k (x, t)).1)
    (hP : ∀ k < n, k ∈ P → ∀ x, StrictMonoOn (fun t ↦ (F k (x, t)).1) J)
    (hN : ∀ k < n, k ∉ P → ∀ x, StrictAntiOn (fun t ↦ (F k (x, t)).1) J)
    {x x' : ℝ} (hxx' : x ≤ x') {y y' : Fin n → ℝ} (hy : ∀ i, y i ∈ J) (hy' : ∀ i, y' i ∈ J)
    (hyy' : ∀ i : Fin n, ((i : ℕ) ∈ P → y i ≤ y' i) ∧ ((i : ℕ) ∉ P → y' i ≤ y i))
    (hne : x < x' ∨ y ≠ y') :
    stripBrokenOrbitEnd F n x y < stripBrokenOrbitEnd F n x' y' := by
  induction n with
  | zero => exact hne.resolve_right fun h ↦ h (Subsingleton.elim y y')
  | succ n ih =>
    have hinit (i : Fin n) : ((i : ℕ) ∈ P → Fin.init y i ≤ Fin.init y' i) ∧
        ((i : ℕ) ∉ P → Fin.init y' i ≤ Fin.init y i) := by
      simpa [Fin.init] using hyy' i.castSucc
    have hle := stripBrokenOrbitEnd_le_stripBrokenOrbitEnd
      (fun k hk t ht ↦ (hx k (by omega) t ht).monotone)
      (fun k hk hkP x ↦ (hP k (by omega) hkP x).monotoneOn)
      (fun k hk hkP x ↦ (hN k (by omega) hkP x).antitoneOn) hxx'
      (fun i ↦ hy i.castSucc) (fun i ↦ hy' i.castSucc) hinit
    have hmono := hx n n.lt_succ_self _ (hy (Fin.last n))
    have hlast := hyy' (Fin.last n)
    simp only [Fin.val_last] at hlast
    rw [stripBrokenOrbitEnd_succ, stripBrokenOrbitEnd_succ]
    by_cases heq : y (Fin.last n) = y' (Fin.last n)
    · -- The last inputs agree, so the strict inequality comes from the earlier positions.
      have hne' : x < x' ∨ Fin.init y ≠ Fin.init y' := by
        refine hne.imp_right fun hne hinit ↦ hne ?_
        rw [← Fin.snoc_init_self y, ← Fin.snoc_init_self y', hinit, heq]
      rw [← heq]
      exact hmono (ih (fun k hk ↦ hx k (by omega)) (fun k hk ↦ hP k (by omega))
        (fun k hk ↦ hN k (by omega)) (fun i ↦ hy i.castSucc) (fun i ↦ hy' i.castSucc) hinit hne')
    · -- The last inputs differ, so the strict inequality comes from the last momentum step.
      refine (hmono.monotone hle).trans_lt ?_
      by_cases hn : n ∈ P
      · exact hP n n.lt_succ_self hn _ (hy _) (hy' _) ((hlast.1 hn).lt_of_ne heq)
      · exact hN n n.lt_succ_self hn _ (hy' _) (hy _) ((hlast.2 hn).lt_of_ne (Ne.symm heq))

/-- **Signed monotonicity of the closing defect.** Suppose that on the set `J` of heights every
factor is increasing in the position, and increasing in the momentum for the factors in `P`,
decreasing for the others. If the inputs `y'` dominate `y` in the coordinates of `P` and are
dominated by `y` in the others, then the closing defect at `y` is at most that at `y'`. -/
theorem stripClosingDefect_le_stripClosingDefect
    (hx : ∀ k < n, ∀ t ∈ J, Monotone fun x ↦ (F k (x, t)).1)
    (hP : ∀ k < n, k ∈ P → ∀ x, MonotoneOn (fun t ↦ (F k (x, t)).1) J)
    (hN : ∀ k < n, k ∉ P → ∀ x, AntitoneOn (fun t ↦ (F k (x, t)).1) J)
    {y y' : Fin n → ℝ} (hy : ∀ i, y i ∈ J) (hy' : ∀ i, y' i ∈ J)
    (hyy' : ∀ i : Fin n, ((i : ℕ) ∈ P → y i ≤ y' i) ∧ ((i : ℕ) ∉ P → y' i ≤ y i)) :
    stripClosingDefect F n x y ≤ stripClosingDefect F n x y' :=
  sub_le_sub_right (stripBrokenOrbitEnd_le_stripBrokenOrbitEnd hx hP hN le_rfl hy hy' hyy') x

/-- **Strict signed monotonicity of the closing defect.** Under the hypotheses of
`TauCeti.stripClosingDefect_le_stripClosingDefect` with strict monotonicity of the factors, the
inequality is strict as soon as the two families of inputs differ. -/
theorem stripClosingDefect_lt_stripClosingDefect
    (hx : ∀ k < n, ∀ t ∈ J, StrictMono fun x ↦ (F k (x, t)).1)
    (hP : ∀ k < n, k ∈ P → ∀ x, StrictMonoOn (fun t ↦ (F k (x, t)).1) J)
    (hN : ∀ k < n, k ∉ P → ∀ x, StrictAntiOn (fun t ↦ (F k (x, t)).1) J)
    {y y' : Fin n → ℝ} (hy : ∀ i, y i ∈ J) (hy' : ∀ i, y' i ∈ J)
    (hyy' : ∀ i : Fin n, ((i : ℕ) ∈ P → y i ≤ y' i) ∧ ((i : ℕ) ∉ P → y' i ≤ y i))
    (hne : y ≠ y') :
    stripClosingDefect F n x y < stripClosingDefect F n x y' :=
  sub_lt_sub_right (stripBrokenOrbitEnd_lt_stripBrokenOrbitEnd hx hP hN le_rfl hy hy' hyy'
    (.inr hne)) x

/-- **The closing defect is strictly increasing in the positive inputs.** Split the inputs into
those `u` of the factors in `P` and those `v` of the others, and hold `v` fixed in `J`. Then the
closing defect is strictly increasing in `u` on the inputs with values in `J`. -/
theorem strictMonoOn_stripClosingDefect [DecidablePred (· ∈ P)]
    (hx : ∀ k < n, ∀ t ∈ J, StrictMono fun x ↦ (F k (x, t)).1)
    (hP : ∀ k < n, k ∈ P → ∀ x, StrictMonoOn (fun t ↦ (F k (x, t)).1) J)
    (hN : ∀ k < n, k ∉ P → ∀ x, StrictAntiOn (fun t ↦ (F k (x, t)).1) J)
    {v : {i : Fin n // (i : ℕ) ∉ P} → ℝ} (hv : ∀ i, v i ∈ J) :
    StrictMonoOn (fun u ↦ stripClosingDefect F n x
      ((Equiv.piEquivPiSubtypeProd (fun i : Fin n ↦ (i : ℕ) ∈ P) fun _ ↦ ℝ).symm (u, v)))
      {u | ∀ i, u i ∈ J} := by
  intro u hu u' hu' huu'
  set e := Equiv.piEquivPiSubtypeProd (fun i : Fin n ↦ (i : ℕ) ∈ P) fun _ ↦ ℝ
  have he (w : {i : Fin n // (i : ℕ) ∈ P} → ℝ) (i : Fin n) :
      e.symm (w, v) i = if hi : (i : ℕ) ∈ P then w ⟨i, hi⟩ else v ⟨i, hi⟩ :=
    Equiv.piEquivPiSubtypeProd_symm_apply _ _ _ _
  have hmem {w : {i : Fin n // (i : ℕ) ∈ P} → ℝ} (hw : ∀ i, w i ∈ J) (i : Fin n) :
      e.symm (w, v) i ∈ J := by
    by_cases hi : (i : ℕ) ∈ P
    · rw [he, dite_eq_left_of_eq_true (eq_true hi)]
      exact hw ⟨i, hi⟩
    · rw [he, dite_eq_right_of_eq_false (eq_false hi)]
      exact hv ⟨i, hi⟩
  refine stripClosingDefect_lt_stripClosingDefect hx hP hN (hmem hu) (hmem hu') (fun i ↦ ?_) ?_
  · by_cases hi : (i : ℕ) ∈ P
    · rw [he, he, dite_eq_left_of_eq_true (eq_true hi), dite_eq_left_of_eq_true (eq_true hi)]
      exact ⟨fun _ ↦ huu'.le ⟨i, hi⟩, fun h ↦ (h hi).elim⟩
    · rw [he, he, dite_eq_right_of_eq_false (eq_false hi), dite_eq_right_of_eq_false (eq_false hi)]
      exact ⟨fun h ↦ (hi h).elim, fun _ ↦ le_rfl⟩
  · intro h
    exact huu'.ne (congrArg Prod.fst (e.symm.injective h))

/-! ### The signs on the faces of the cube of inputs -/

/-- **The closing defect is negative on the lower face.** Suppose every factor maps the line
`y = c` into itself, and the chain displaces `(x, c)` strictly to the left. Then the closing
defect is negative at every family of inputs in `J` whose positive inputs are at most `c` and
whose negative inputs are at least `c`, for instance with `c` the lower boundary height, positive
inputs `c` and arbitrary negative inputs. -/
theorem stripClosingDefect_neg
    (hx : ∀ k < n, ∀ t ∈ J, Monotone fun x ↦ (F k (x, t)).1)
    (hP : ∀ k < n, k ∈ P → ∀ x, MonotoneOn (fun t ↦ (F k (x, t)).1) J)
    (hN : ∀ k < n, k ∉ P → ∀ x, AntitoneOn (fun t ↦ (F k (x, t)).1) J)
    {c : ℝ} (hcJ : c ∈ J) (hc : ∀ k < n, ∀ x, (F k (x, c)).2 = c)
    {z : ℕ → ℝ × ℝ} (hz : ∀ k < n, z (k + 1) = F k (z k)) (hz0 : z 0 = (x, c))
    (hzn : (z n).1 < x) {y : Fin n → ℝ} (hy : ∀ i, y i ∈ J)
    (hyc : ∀ i : Fin n, ((i : ℕ) ∈ P → y i ≤ c) ∧ ((i : ℕ) ∉ P → c ≤ y i)) :
    stripClosingDefect F n x y < 0 := by
  refine (stripClosingDefect_le_stripClosingDefect hx hP hN hy (fun _ ↦ hcJ) hyc).trans_lt ?_
  rw [stripClosingDefect_def, stripBrokenOrbitEnd_const_eq_of_orbit hc hz hz0, sub_neg]
  exact hzn

/-- **The closing defect is positive on the upper face.** Suppose every factor maps the line
`y = c` into itself, and the chain displaces `(x, c)` strictly to the right. Then the closing
defect is positive at every family of inputs in `J` whose positive inputs are at least `c` and
whose negative inputs are at most `c`, for instance with `c` the upper boundary height, positive
inputs `c` and arbitrary negative inputs. -/
theorem stripClosingDefect_pos
    (hx : ∀ k < n, ∀ t ∈ J, Monotone fun x ↦ (F k (x, t)).1)
    (hP : ∀ k < n, k ∈ P → ∀ x, MonotoneOn (fun t ↦ (F k (x, t)).1) J)
    (hN : ∀ k < n, k ∉ P → ∀ x, AntitoneOn (fun t ↦ (F k (x, t)).1) J)
    {c : ℝ} (hcJ : c ∈ J) (hc : ∀ k < n, ∀ x, (F k (x, c)).2 = c)
    {z : ℕ → ℝ × ℝ} (hz : ∀ k < n, z (k + 1) = F k (z k)) (hz0 : z 0 = (x, c))
    (hzn : x < (z n).1) {y : Fin n → ℝ} (hy : ∀ i, y i ∈ J)
    (hyc : ∀ i : Fin n, ((i : ℕ) ∈ P → c ≤ y i) ∧ ((i : ℕ) ∉ P → y i ≤ c)) :
    0 < stripClosingDefect F n x y := by
  refine lt_of_lt_of_le ?_
    (stripClosingDefect_le_stripClosingDefect hx hP hN (fun _ ↦ hcJ) hy hyc)
  rw [stripClosingDefect_def, stripBrokenOrbitEnd_const_eq_of_orbit hc hz hz0, sub_pos]
  exact hzn

/-! ### Deck translations and smoothness -/

/-- If every factor commutes with the translation by `a` in the position, at the heights in `J`,
then translating the starting position of a broken orbit with inputs in `J` translates its last
position. -/
theorem stripBrokenOrbitEnd_add {a : ℝ}
    (hF : ∀ k < n, ∀ x, ∀ t ∈ J, (F k (x + a, t)).1 = (F k (x, t)).1 + a)
    {y : Fin n → ℝ} (hy : ∀ i, y i ∈ J) :
    stripBrokenOrbitEnd F n (x + a) y = stripBrokenOrbitEnd F n x y + a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [stripBrokenOrbitEnd_succ, stripBrokenOrbitEnd_succ,
      ih (y := Fin.init y) (fun k hk ↦ hF k (by omega)) (fun i ↦ hy i.castSucc)]
    exact hF n n.lt_succ_self _ _ (hy _)

/-- **The closing defect is invariant under deck translations.** If every factor commutes with
the translation by `a` in the position, at the heights in `J`, as the lifts of maps of the annulus
do for `a = 1`, then the closing defect at inputs in `J` is invariant under translating the
starting position by `a`. -/
theorem stripClosingDefect_add {a : ℝ}
    (hF : ∀ k < n, ∀ x, ∀ t ∈ J, (F k (x + a, t)).1 = (F k (x, t)).1 + a)
    {y : Fin n → ℝ} (hy : ∀ i, y i ∈ J) :
    stripClosingDefect F n (x + a) y = stripClosingDefect F n x y := by
  rw [stripClosingDefect_def, stripClosingDefect_def, stripBrokenOrbitEnd_add hF hy]
  ring

/-- The last position of a broken orbit is jointly `C^m` in the starting position and the inputs
in `J`, when the first component of every factor is `C^m` on the strip `ℝ × J`. -/
theorem contDiffOn_stripBrokenOrbitEnd {m : WithTop ℕ∞}
    (hF : ∀ k < n, ContDiffOn ℝ m (fun q ↦ (F k q).1) (univ ×ˢ J)) :
    ContDiffOn ℝ m (fun p : ℝ × (Fin n → ℝ) ↦ stripBrokenOrbitEnd F n p.1 p.2)
      (univ ×ˢ univ.pi fun _ ↦ J) := by
  induction n with
  | zero => exact contDiffOn_fst
  | succ n ih =>
    have hinit : ContDiff ℝ m fun y : Fin (n + 1) → ℝ ↦ Fin.init y :=
      contDiff_pi.2 fun i ↦ by
        simp only [Fin.init]
        exact contDiff_apply ℝ (fun _ ↦ ℝ) i.castSucc
    have hpre : ContDiffOn ℝ m (fun p : ℝ × (Fin (n + 1) → ℝ) ↦ (p.1, Fin.init p.2))
        (univ ×ˢ univ.pi fun _ ↦ J) :=
      contDiffOn_fst.prodMk (hinit.comp_contDiffOn contDiffOn_snd)
    have hmaps : MapsTo (fun p : ℝ × (Fin (n + 1) → ℝ) ↦ (p.1, Fin.init p.2))
        (univ ×ˢ univ.pi fun _ ↦ J) (univ ×ˢ univ.pi fun _ ↦ J) :=
      fun p hp ↦ ⟨trivial, fun i _ ↦ hp.2 i.castSucc trivial⟩
    have hend := (ih fun k hk ↦ hF k (by omega)).comp hpre hmaps
    have hlast : ContDiffOn ℝ m (fun p : ℝ × (Fin (n + 1) → ℝ) ↦ p.2 (Fin.last n))
        (univ ×ˢ univ.pi fun _ ↦ J) :=
      (contDiff_apply ℝ (fun _ ↦ ℝ) (Fin.last n)).comp_contDiffOn contDiffOn_snd
    exact (hF n n.lt_succ_self).comp (hend.prodMk hlast)
      fun p hp ↦ ⟨trivial, hp.2 (Fin.last n) trivial⟩

/-- **The closing defect is jointly smooth.** It is `C^m` in the starting position and the inputs
in `J`, when the first component of every factor is `C^m` on the strip `ℝ × J`. -/
theorem contDiffOn_stripClosingDefect {m : WithTop ℕ∞}
    (hF : ∀ k < n, ContDiffOn ℝ m (fun q ↦ (F k q).1) (univ ×ˢ J)) :
    ContDiffOn ℝ m (fun p : ℝ × (Fin n → ℝ) ↦ stripClosingDefect F n p.1 p.2)
      (univ ×ˢ univ.pi fun _ ↦ J) :=
  (contDiffOn_stripBrokenOrbitEnd hF).sub contDiffOn_fst

/-! ### A chain of two shears -/

/-- **The closing defect of a chain of two shears.** For the chain of the affine shear
`(x, y) ↦ (x - (6 y + 1) / 8, y)`, with negative twist `-3/4`, followed by the shear
`(x, y) ↦ (x + y, y)`, with positive twist `1`, the closing defect with incoming momenta `v` and
`u` is `u - (6 v + 1) / 8`. The composite of the chain is `(x, y) ↦ (x + (2 y - 1) / 8, y)`. -/
theorem stripClosingDefect_affineShear_shear (x u v : ℝ) :
    stripClosingDefect
      (fun k q ↦ if k = 0 then (q.1 - (6 * q.2 + 1) / 8, q.2) else (q.1 + q.2, q.2))
      2 x ![v, u] = u - (6 * v + 1) / 8 := by
  simp only [stripClosingDefect_def, stripBrokenOrbitEnd_succ, stripBrokenOrbitEnd_zero, Fin.init,
    Fin.last_zero, Fin.castSucc_zero, Fin.reduceLast, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, one_ne_zero, ↓reduceIte, Nat.reduceAdd]
  ring

/-- The two shears satisfy the hypotheses of the sign theorems on `J = [0, 1]`, with the second
factor positive and the first negative, and the chain preserves both boundary lines. Its composite
`(x, y) ↦ (x + (2 y - 1) / 8, y)` displaces the lower boundary line by `-1/8` and the upper one by
`1/8`, so the closing defect is negative on the lower face `u = 0` and positive on the upper face
`u = 1` of the square of inputs. -/
example (x v : ℝ) (hv : v ∈ Icc (0 : ℝ) 1) :
    let F : ℕ → ℝ × ℝ → ℝ × ℝ :=
      fun k q ↦ if k = 0 then (q.1 - (6 * q.2 + 1) / 8, q.2) else (q.1 + q.2, q.2)
    stripClosingDefect F 2 x ![v, 0] < 0 ∧ 0 < stripClosingDefect F 2 x ![v, 1] := by
  intro F
  have hx : ∀ k < 2, ∀ t ∈ Icc (0 : ℝ) 1, Monotone fun x ↦ (F k (x, t)).1 := by
    intro k _ t _ a b hab
    simp only [F]
    split_ifs <;> linarith
  have hP : ∀ k < 2, k ∈ ({1} : Set ℕ) → ∀ x, MonotoneOn (fun t ↦ (F k (x, t)).1) (Icc 0 1) := by
    rintro k _ rfl x a _ b _ hab
    simp only [F, one_ne_zero, ite_false]
    linarith
  have hN : ∀ k < 2, k ∉ ({1} : Set ℕ) → ∀ x, AntitoneOn (fun t ↦ (F k (x, t)).1) (Icc 0 1) := by
    intro k hk hkP x a _ b _ hab
    obtain rfl : k = 0 := by
      rw [Set.mem_singleton_iff] at hkP
      omega
    simp only [F, ite_true]
    linarith
  have hy (w : ℝ) (hw : w ∈ Icc (0 : ℝ) 1) : ∀ i : Fin 2, ![v, w] i ∈ Icc (0 : ℝ) 1 :=
    Fin.forall_fin_two.2 ⟨hv, hw⟩
  have hline (c : ℝ) : ∀ k < 2, ∀ x, (F k (x, c)).2 = c := by
    intro k _ x
    simp only [F]
    split_ifs <;> rfl
  constructor
  · refine stripClosingDefect_neg (J := Icc 0 1) (P := {1}) hx hP hN ⟨le_rfl, zero_le_one⟩
      (hline 0) (z := fun k ↦ if k = 0 then (x, 0) else (x - 1 / 8, 0)) (fun k hk ↦ ?_) rfl
      (by norm_num) (hy 0 ⟨le_rfl, zero_le_one⟩) (Fin.forall_fin_two.2 ⟨by simp [hv.1], by simp⟩)
    obtain _ | _ | k := k
    · norm_num [F]
    · norm_num [F]
    · omega
  · refine stripClosingDefect_pos (J := Icc 0 1) (P := {1}) hx hP hN ⟨zero_le_one, le_rfl⟩
      (hline 1)
      (z := fun k ↦ if k = 0 then (x, 1) else if k = 1 then (x - 7 / 8, 1) else (x - 7 / 8 + 1, 1))
      (fun k hk ↦ ?_) rfl (by norm_num [sub_add]) (hy 1 ⟨zero_le_one, le_rfl⟩)
      (Fin.forall_fin_two.2 ⟨by simp [hv.2], by simp⟩)
    obtain _ | _ | k := k
    · norm_num [F]
    · norm_num [F]
    · omega

end TauCeti

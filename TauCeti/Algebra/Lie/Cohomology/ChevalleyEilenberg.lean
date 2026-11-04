/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Lie.Cochain
public import TauCeti.Algebra.Lie.Cohomology.LowDegree
public import TauCeti.Algebra.Lie.AlternatingMap
public import TauCeti.Data.Fin.Tuple.Basic
public import TauCeti.LinearAlgebra.Alternating.Curry

/-!
# The Chevalley–Eilenberg complex of a Lie algebra

Let `L` be a Lie algebra over a commutative ring `R` and `M` an `L`-module. The
Chevalley–Eilenberg cochains of degree `n` are the alternating maps `L [⋀^Fin n]→ₗ[R] M`, and the
differential `d R L M n` sends an `n`-cochain `ω` to the `(n + 1)`-cochain
`(d ω)(x₀, …, xₙ) = ∑ i, (-1)^i ⁅xᵢ, ω(x₀, …, x̂ᵢ, …, xₙ)⁆`
`  + ∑_{i < j} (-1)^(i + j) ω(⁅xᵢ, xⱼ⁆, x₀, …, x̂ᵢ, …, x̂ⱼ, …, xₙ)`
(`d_zero_apply`, `d_succ_apply`). This file constructs the differential in every degree and
proves `d ∘ d = 0` (`d_d`).

The differential is constructed one degree at a time from the interior products
`ω.curryLeft x` and the Lie derivatives `⁅x, ω⁆` of `AlternatingMap.instLieRingModule`, through
Cartan's formula `ι_x d ω = ⁅x, ω⁆ - d ι_x ω` (`curryLeft_d_zero`, `curryLeft_d_succ`). This
formula, together with `[L_x, ι_y] = ι_{[x, y]}`, shows that the differential commutes with the
Lie derivatives (`lie_d`), and then that it squares to zero, both by induction on the degree.
The explicit formula is then deduced from Cartan's formula.

The differentials assemble into a cochain complex of `R`-modules, whose cohomology is the Lie
algebra cohomology of `L` with coefficients in `M` in every degree. In degrees one and two, the
cochains are identified with Mathlib's low-degree cochains `oneCochain` and `twoCochain`, and
the differential with `d₀₁`, Mathlib's `d₁₂` and, after forgetting alternation, `d₂₃`.

## Main definitions

* `TauCeti.LieModule.Cohomology.d`: the Chevalley–Eilenberg differential in degree `n`.
* `TauCeti.LieModule.Cohomology.cochainComplex`: the Chevalley–Eilenberg cochain complex.
* `TauCeti.LieModule.Cohomology.cohomology`: Lie algebra cohomology in degree `n`.
* `TauCeti.LieModule.Cohomology.oneCochainEquiv`, `TauCeti.LieModule.Cohomology.twoCochainEquiv`:
  the comparison with the low-degree cochains.

## Main results

* `TauCeti.LieModule.Cohomology.d_succ_apply`: the explicit formula for the differential.
* `TauCeti.LieModule.Cohomology.curryLeft_d_succ`: Cartan's formula.
* `TauCeti.LieModule.Cohomology.lie_d`: the differential is a map of `L`-modules.
* `TauCeti.LieModule.Cohomology.d_d`: the differential squares to zero.
* `TauCeti.LieModule.Cohomology.twoCochainEquiv_d_one`,
  `TauCeti.LieModule.Cohomology.d₂₃_twoCochainEquiv`: the comparison with `d₁₂` and `d₂₃`.

## References

* C. Chevalley and S. Eilenberg, *Cohomology theory of Lie groups and Lie algebras*,
  Trans. Amer. Math. Soc. 63 (1948), 85–124.
* C. A. Weibel, *An Introduction to Homological Algebra*, Cambridge University Press, 1994,
  §7.7.
-/

public section

open Fin AlternatingMap _root_.LieModule.Cohomology

namespace TauCeti.LieModule.Cohomology

variable (R : Type*) [CommRing R]
variable (L : Type*) [LieRing L] [LieAlgebra R L]
variable (M : Type*) [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

/-- The Lie derivatives `x ↦ ⁅x, ω⁆` of a cochain, as a linear map. -/
private def lieFamily {n : ℕ} (ω : L [⋀^Fin n]→ₗ[R] M) : L →ₗ[R] L [⋀^Fin n]→ₗ[R] M :=
  (LieModule.toEnd R L (L [⋀^Fin n]→ₗ[R] M) : L →ₗ[R] Module.End R _).flip ω

private theorem lieFamily_apply {n : ℕ} (ω : L [⋀^Fin n]→ₗ[R] M) (x : L) :
    lieFamily R L M ω x = ⁅x, ω⁆ := (rfl)

/-- The differential with values in multilinear maps, defined by Cartan's formula
`ι_x d ω = ⁅x, ω⁆ - d ι_x ω` before alternation is known. -/
private def dAux :
    (n : ℕ) → (L [⋀^Fin n]→ₗ[R] M) →ₗ[R] MultilinearMap R (fun _ : Fin (n + 1) ↦ L) M
  | 0 =>
    { toFun ω := (toMultilinearMapLM ∘ₗ lieFamily R L M ω).uncurryLeft
      map_add' ω ω' := by ext v; simp [lieFamily_apply]
      map_smul' c ω := by ext v; simp [lieFamily_apply] }
  | n + 1 =>
    { toFun ω := (toMultilinearMapLM ∘ₗ lieFamily R L M ω - dAux n ∘ₗ ω.curryLeft).uncurryLeft
      map_add' ω ω' := by ext v; simp [lieFamily_apply]; abel
      map_smul' c ω := by ext v; simp [lieFamily_apply, smul_sub] }

variable {R L M}

private theorem dAux_zero_apply (ω : L [⋀^Fin 0]→ₗ[R] M) (v : Fin 1 → L) :
    dAux R L M 0 ω v = ⁅v 0, ω⁆ (tail v) := by
  simp [dAux, lieFamily_apply]

private theorem dAux_succ_apply {n : ℕ} (ω : L [⋀^Fin (n + 1)]→ₗ[R] M) (v : Fin (n + 2) → L) :
    dAux R L M (n + 1) ω v = ⁅v 0, ω⁆ (tail v) - dAux R L M n (ω.curryLeft (v 0)) (tail v) := by
  simp [dAux, lieFamily_apply]

/-- The multilinear differential vanishes on tuples with two equal entries. -/
private theorem dAux_map_eq_zero_of_eq :
    ∀ (n : ℕ) (ω : L [⋀^Fin n]→ₗ[R] M) (v : Fin (n + 1) → L) (i j : Fin (n + 1)),
      v i = v j → i ≠ j → dAux R L M n ω v = 0 := by
  intro n
  induction n with
  | zero => exact fun _ _ i j _ hij ↦ absurd (Fin.ext (by omega)) hij
  | succ n ih =>
    intro ω v i j hv hij
    -- By induction, `dAux R L M n` is alternating; assemble it into the alternating map `D`.
    let D : (L [⋀^Fin n]→ₗ[R] M) →ₗ[R] L [⋀^Fin (n + 1)]→ₗ[R] M :=
      { toFun η := ⟨dAux R L M n η, ih η⟩
        map_add' η η' := by ext; simp
        map_smul' c η := by ext; simp }
    let g : L →ₗ[R] L [⋀^Fin (n + 1)]→ₗ[R] M := lieFamily R L M ω - D ∘ₗ ω.curryLeft
    -- Cartan's formula for `D` at `x`, with `ι_x ι_x ω = 0`, shows that `g x` vanishes when its
    -- first argument is `x`.
    have hg : ∀ x, (g x).curryLeft x = 0 := by
      intro x
      ext w
      have hL : ⁅x, ω⁆ (Matrix.vecCons x w) = ⁅x, ω.curryLeft x⁆ w := by
        rw [← curryLeft_apply_apply, curryLeft_lie, lie_self, _root_.map_zero, sub_zero]
      have hD : D (ω.curryLeft x) (Matrix.vecCons x w) = ⁅x, ω.curryLeft x⁆ w := by
        cases n with
        | zero => exact dAux_zero_apply _ _
        | succ m =>
          -- `D` is `dAux R L M (m + 1)` with its alternation attached.
          change dAux R L M (m + 1) _ _ = _
          simp [dAux_succ_apply, Fin.tail_def]
      simp only [g, curryLeft_apply_apply, LinearMap.sub_apply, LinearMap.comp_apply,
        lieFamily_apply, sub_apply, hL, hD, sub_self, zero_apply]
    have h := (uncurryLeft g hg).map_eq_zero_of_eq v hv hij
    rwa [uncurryLeft_apply] at h

variable (R L M)

/-- The Chevalley–Eilenberg differential from `n`-cochains to `(n + 1)`-cochains of `L` with
coefficients in `M`. -/
def d (n : ℕ) : (L [⋀^Fin n]→ₗ[R] M) →ₗ[R] L [⋀^Fin (n + 1)]→ₗ[R] M where
  toFun ω := ⟨dAux R L M n ω, dAux_map_eq_zero_of_eq n ω⟩
  map_add' ω ω' := by ext; simp
  map_smul' c ω := by ext; simp

variable {R L M}

private theorem d_apply_eq_dAux {n : ℕ} (ω : L [⋀^Fin n]→ₗ[R] M) (v : Fin (n + 1) → L) :
    d R L M n ω v = dAux R L M n ω v := (rfl)

/-- Cartan's formula in degree zero: the interior product of `d ω` is the Lie derivative. -/
@[simp]
theorem curryLeft_d_zero (ω : L [⋀^Fin 0]→ₗ[R] M) (x : L) :
    (d R L M 0 ω).curryLeft x = ⁅x, ω⁆ := by
  ext w
  simp [d_apply_eq_dAux, dAux_zero_apply]

/-- **Cartan's formula** `ι_x d ω = L_x ω - d ι_x ω`. -/
@[simp]
theorem curryLeft_d_succ {n : ℕ} (ω : L [⋀^Fin (n + 1)]→ₗ[R] M) (x : L) :
    (d R L M (n + 1) ω).curryLeft x = ⁅x, ω⁆ - d R L M n (ω.curryLeft x) := by
  ext w
  simp [d_apply_eq_dAux, dAux_succ_apply]

/-- The differential of a `0`-cochain, that is of an element `ω ![]` of `M`. -/
@[simp]
theorem d_zero_apply (ω : L [⋀^Fin 0]→ₗ[R] M) (v : Fin 1 → L) :
    d R L M 0 ω v = ⁅v 0, ω ![]⁆ := by
  simp [d_apply_eq_dAux, dAux_zero_apply, Subsingleton.elim (tail v) ![]]

/-- The differential commutes with the action of `L`: it is a map of `L`-modules. -/
theorem lie_d (n : ℕ) (x : L) (ω : L [⋀^Fin n]→ₗ[R] M) :
    ⁅x, d R L M n ω⁆ = d R L M n ⁅x, ω⁆ := by
  induction n with
  | zero =>
    refine curryLeft_injective (LinearMap.ext fun y ↦ ?_)
    rw [curryLeft_lie, curryLeft_d_zero, curryLeft_d_zero, curryLeft_d_zero, leibniz_lie]
    abel
  | succ n ih =>
    refine curryLeft_injective (LinearMap.ext fun y ↦ ?_)
    simp only [curryLeft_lie, curryLeft_d_succ, lie_sub, ih, map_sub, leibniz_lie x y ω]
    abel

/-- The Chevalley–Eilenberg differential squares to zero. -/
@[simp]
theorem d_d (n : ℕ) (ω : L [⋀^Fin n]→ₗ[R] M) : d R L M (n + 1) (d R L M n ω) = 0 := by
  induction n with
  | zero =>
    refine curryLeft_injective (LinearMap.ext fun x ↦ ?_)
    simp [lie_d]
  | succ n ih =>
    refine curryLeft_injective (LinearMap.ext fun x ↦ ?_)
    simp [lie_d, ih]

/-- The Chevalley–Eilenberg differential squares to zero, as a composite of linear maps. -/
theorem d_comp_d (n : ℕ) : d R L M (n + 1) ∘ₗ d R L M n = 0 :=
  LinearMap.ext (d_d n)

/-! ### The explicit formula -/

omit [LieModule R L M] in
/-- Splitting off the first argument in the sum of Lie actions of the Chevalley–Eilenberg
formula. -/
private theorem sum_lie_vecCons {n : ℕ} (ω : L [⋀^Fin (n + 1)]→ₗ[R] M) (x : L)
    (w : Fin (n + 1) → L) :
    ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        ⁅Matrix.vecCons x w i, ω (i.removeNth (Matrix.vecCons x w))⁆ =
      ⁅x, ω w⁆ - ∑ i : Fin (n + 1), (-1 : ℤ) ^ (i : ℕ) • ⁅w i, ω.curryLeft x (i.removeNth w)⁆ := by
  rw [Fin.sum_univ_succ]
  simp [Matrix.vecCons, removeNth_succ_cons, pow_succ, curryLeft_apply_apply, sub_eq_add_neg]

omit [LieRingModule L M] [LieModule R L M] in
/-- The pairs of the Chevalley–Eilenberg formula containing the first argument `x` give the
action of `x` on the remaining arguments. -/
private theorem sum_pair_vecCons_zero {n : ℕ} (ω : L [⋀^Fin (n + 1)]→ₗ[R] M) (x : L)
    (w : Fin (n + 1) → L) :
    ∑ j ≥ (0 : Fin (n + 1)), (-1 : ℤ) ^ ((0 : Fin (n + 1)) + j + 1 : ℕ) •
        ω (Matrix.vecCons ⁅Matrix.vecCons x w (0 : Fin (n + 1)).castSucc, Matrix.vecCons x w j.succ⁆
          (j.removeNth ((0 : Fin (n + 1)).castSucc.removeNth (Matrix.vecCons x w)))) =
      -∑ k, ω (Function.update w k ⁅x, w k⁆) := by
  simp only [← insertNth_removeNth, map_insertNth]
  simp [Matrix.vecCons, pow_succ, Finset.sum_neg_distrib]

omit [LieRingModule L M] [LieModule R L M] in
/-- Splitting off the first argument in the sum over pairs of the Chevalley–Eilenberg formula:
the pairs containing it give the action of `x` on the remaining arguments, and the others the
corresponding sum for the interior product `ω.curryLeft x`. -/
private theorem sum_pair_vecCons {n : ℕ} (ω : L [⋀^Fin (n + 2)]→ₗ[R] M) (x : L)
    (w : Fin (n + 2) → L) :
    ∑ i : Fin (n + 2), ∑ j ≥ i, (-1 : ℤ) ^ (i + j + 1 : ℕ) •
        ω (Matrix.vecCons ⁅Matrix.vecCons x w i.castSucc, Matrix.vecCons x w j.succ⁆
          (j.removeNth (i.castSucc.removeNth (Matrix.vecCons x w)))) =
      -∑ k, ω (Function.update w k ⁅x, w k⁆) -
        ∑ i : Fin (n + 1), ∑ j ≥ i, (-1 : ℤ) ^ (i + j + 1 : ℕ) •
          ω.curryLeft x (Matrix.vecCons ⁅w i.castSucc, w j.succ⁆
            (j.removeNth (i.castSucc.removeNth w))) := by
  have hsign (a b : ℕ) : (-1 : ℤ) ^ (a + 1 + (b + 1) + 1) = (-1) ^ (a + b + 1) := by ring
  conv_lhs => rw [Fin.sum_univ_succ, sum_pair_vecCons_zero]
  rw [sub_eq_add_neg]
  congr 1
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Fin.sum_Ici_succ, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have hω (a : L) (r : Fin n → L) :
      ω (cons a (cons x r)) = -ω.curryLeft x (cons a r) := by
    have h := congr($(curryLeft_curryLeft_eq_neg ω a x) r)
    simpa [curryLeft_apply_apply, Matrix.vecCons] using h
  simp only [← succ_castSucc, Matrix.vecCons, cons_succ, removeNth_succ_cons, val_succ, hsign,
    hω, smul_neg]

/-- **The Chevalley–Eilenberg formula** for the differential of a cochain of positive degree:
`(d ω)(x₀, …, xₙ₊₁) = ∑ i, (-1)^i ⁅xᵢ, ω(…, x̂ᵢ, …)⁆ + ∑_{i < j} (-1)^(i + j) ω(⁅xᵢ, xⱼ⁆, …)`,
where the pairs `i < j` are written as `(i.castSucc, j.succ)` with `i ≤ j`. -/
theorem d_succ_apply {n : ℕ} (ω : L [⋀^Fin (n + 1)]→ₗ[R] M) (v : Fin (n + 2) → L) :
    d R L M (n + 1) ω v =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • ⁅v i, ω (i.removeNth v)⁆ +
        ∑ i : Fin (n + 1), ∑ j ≥ i, (-1 : ℤ) ^ (i + j + 1 : ℕ) •
          ω (Matrix.vecCons ⁅v i.castSucc, v j.succ⁆ (j.removeNth (i.castSucc.removeNth v))) := by
  -- Split off the first argument `x` and compare with Cartan's formula `ι_x d = L_x - d ι_x`.
  induction n with
  | zero =>
    obtain ⟨x, a, rfl⟩ : ∃ x a, v = ![x, a] := ⟨v 0, v 1, by ext i; fin_cases i <;> rfl⟩
    rw [← curryLeft_apply_apply, curryLeft_d_succ, sub_apply, d_zero_apply]
    have h₁ : Function.update ![a] 0 ⁅x, a⁆ = ![⁅x, a⁆] := by ext i; fin_cases i; rfl
    have h₂ : removeNth 1 ![x, a] = ![x] := by ext i; fin_cases i; rfl
    simp [Fin.sum_univ_succ, Subsingleton.elim (removeNth 0 ![a]) ![], h₁, h₂]
    abel
  | succ n ih =>
    obtain ⟨x, w, rfl⟩ : ∃ x w, v = Matrix.vecCons x w := ⟨v 0, tail v, (cons_self_tail v).symm⟩
    rw [← curryLeft_apply_apply, curryLeft_d_succ, sub_apply, lie_apply, sum_lie_vecCons, ih,
      sum_pair_vecCons]
    abel

/-! ### The complex and its cohomology -/

variable (R L M)

/-- The Chevalley–Eilenberg cochain complex of `L` with coefficients in `M`, whose degree `n`
term is the module of alternating maps `L [⋀^Fin n]→ₗ[R] M`. -/
noncomputable abbrev cochainComplex : CochainComplex (ModuleCat R) ℕ :=
  CochainComplex.of (fun n ↦ ModuleCat.of R (L [⋀^Fin n]→ₗ[R] M))
    (fun n ↦ ModuleCat.ofHom (d R L M n)) fun n ↦ by
      rw [← ModuleCat.ofHom_comp, d_comp_d, ModuleCat.ofHom_zero]

/-- The `n`-th Lie algebra cohomology of `L` with coefficients in `M`. -/
noncomputable def cohomology (n : ℕ) : ModuleCat R :=
  (cochainComplex R L M).homology n

/-! ### Comparison with the low-degree cochains -/

omit [LieRingModule L M] [LieModule R L M] in
/-- One-cochains are linear maps. -/
def oneCochainEquiv : (L [⋀^Fin 1]→ₗ[R] M) ≃ₗ[R] oneCochain R L M where
  toFun ω :=
    { toFun x := ω ![x]
      map_add' x y := ω.map_vecCons_add _ x y
      map_smul' c x := ω.map_vecCons_smul _ c x }
  invFun := ofSubsingleton R L M 0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv ω := by
    ext v
    simpa using congrArg ω (funext fun i ↦ by fin_cases i; rfl)
  right_inv f := by
    ext x
    simp

variable {R L M}

omit [LieRingModule L M] [LieModule R L M] in
/-- The linear map attached to a one-cochain is its value on one-element tuples. -/
@[simp]
theorem oneCochainEquiv_apply (ω : L [⋀^Fin 1]→ₗ[R] M) (x : L) :
    oneCochainEquiv R L M ω x = ω ![x] := (rfl)

omit [LieRingModule L M] [LieModule R L M] in
/-- The one-cochain attached to a linear map evaluates it on the unique entry. -/
@[simp]
theorem oneCochainEquiv_symm_apply (f : oneCochain R L M) (v : Fin 1 → L) :
    (oneCochainEquiv R L M).symm f v = f (v 0) := (rfl)

variable (R L M)

omit [LieRingModule L M] [LieModule R L M] in
/-- Two-cochains are alternating bilinear maps. -/
def twoCochainEquiv : (L [⋀^Fin 2]→ₗ[R] M) ≃ₗ[R] twoCochain R L M where
  toFun ω := ⟨(oneCochainEquiv R L M).toLinearMap ∘ₗ ω.curryLeft, fun x ↦ by
    simpa using ω.map_eq_zero_of_eq ![x, x] (i := 0) (j := 1) rfl (by decide)⟩
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp
  invFun c := uncurryLeft ((oneCochainEquiv R L M).symm.toLinearMap ∘ₗ c.1) fun x ↦ by
    ext r
    simp
  left_inv ω := by
    ext v
    rw [uncurryLeft_apply]
    simp [Matrix.vecCons]
  right_inv c := by
    ext x y
    simp

variable {R L M}

omit [LieRingModule L M] [LieModule R L M] in
/-- The bilinear map attached to a two-cochain is its value on pairs. -/
@[simp]
theorem twoCochainEquiv_apply (ω : L [⋀^Fin 2]→ₗ[R] M) (x y : L) :
    twoCochainEquiv R L M ω x y = ω ![x, y] :=
  (oneCochainEquiv_apply (ω.curryLeft x) y).trans (curryLeft_apply_apply ω x ![y])

omit [LieRingModule L M] [LieModule R L M] in
/-- The two-cochain attached to an alternating bilinear map evaluates it on the two entries. -/
@[simp]
theorem twoCochainEquiv_symm_apply (c : twoCochain R L M) (v : Fin 2 → L) :
    (twoCochainEquiv R L M).symm c v = c (v 0) (v 1) := by
  simp [twoCochainEquiv, tail]

/-- In degree zero, the differential is the differential `d₀₁` from the module to
one-cochains. -/
theorem oneCochainEquiv_d_zero (ω : L [⋀^Fin 0]→ₗ[R] M) :
    oneCochainEquiv R L M (d R L M 0 ω) = d₀₁ R L M (ω ![]) := by
  ext x
  simp [d_zero_apply]

/-- In degree one, the differential is Mathlib's `d₁₂`. -/
theorem twoCochainEquiv_d_one (ω : L [⋀^Fin 1]→ₗ[R] M) :
    twoCochainEquiv R L M (d R L M 1 ω) = d₁₂ R L M (oneCochainEquiv R L M ω) := by
  ext x y
  have h : removeNth 1 ![x, y] = ![x] := by ext i; fin_cases i; rfl
  simp [d_succ_apply, Fin.sum_univ_succ, h]
  abel

/-- In degree two, the differential is Mathlib's `d₂₃`, which takes values in all trilinear
maps. -/
theorem d₂₃_twoCochainEquiv (ω : L [⋀^Fin 2]→ₗ[R] M) (x y z : L) :
    d₂₃ R L M (twoCochainEquiv R L M ω) x y z = d R L M 2 ω ![x, y, z] := by
  have h₁ : removeNth 1 ![x, y, z] = ![x, z] := by ext i; fin_cases i <;> rfl
  have h₂ : removeNth 2 ![x, y, z] = ![x, y] := by ext i; fin_cases i <;> rfl
  have h₃ : removeNth 1 ![y, z] = ![y] := by ext i; fin_cases i; rfl
  have h₄ : removeNth 1 ![x, z] = ![x] := by ext i; fin_cases i; rfl
  have h₅ : Finset.Ici (1 : Fin 2) = {1} := by decide
  simp [d_succ_apply, Fin.sum_univ_succ, h₁, h₂, h₃, h₄, h₅]
  abel

end TauCeti.LieModule.Cohomology

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.Distribution.AnalyticStage
public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Product
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.RingTheory.Regular.IsSMulRegular

/-!
# Two-variable stage evaluation and additive comultiplication

For analytic levels `h` and `k` and a complete ultrametric normed `ℤ_p`-module `E`, the model space
`C₀((ZMod (pʰ) × ℕ) × (ZMod (pᵏ) × ℕ), E)` represents families of two-variable power series
`∑_{i, j} uⁱ vʲ • F((a, i), (b, j))` on the product discs `(a + pʰℤ_p) × (b + pᵏℤ_p)`. Under
`ZeroAtInftyContinuousMap.curryEquiv` it is isometric to `LA_h(LA_k(E))`, so two-variable
evaluation `TauCeti.AnalyticStage.eval₂` is obtained by evaluating the second index into
`C(ℤ_p, E)`, evaluating the first index into `C(ℤ_p, C(ℤ_p, E))`, and uncurrying to
`C(ℤ_p × ℤ_p, E)`. When multiplication by `p` on `E` is injective, `eval₂` is injective.

Addition `(x, y) ↦ x + y` on `ℤ_p` sends `(a + pʰ u) + (b + pʰ v)` into the disc of `a + b` in
`ZMod (pʰ)` with normalized coordinate `q + u + v`, where `q = ⌊(a.val + b.val) / pʰ⌋ ∈ {0, 1}` is
the carry digit. Re-expanding `(q + u + v)ᵏ` in powers of `u` and `v` defines the additive
comultiplication

`addComul S : LA_h(E) →L[S] C₀((ZMod (pʰ) × ℕ) × (ZMod (pʰ) × ℕ), E)`,

sending `c` at `((a, i), (b, j))` to
`∑_{k ≥ i + j} (k choose (i + j)) ((i + j) choose i) q^(k - i - j) • c(a + b, k)`.

Vanishing at infinity holds because `ZMod (pʰ)` is finite, so outside finitely many pairs of indices
the total degree `i + j` is large and only tail coefficients `c(a + b, k)` with `k ≥ i + j` can
contribute. Every stage comultiplication is an isometry (`norm_addComul`), satisfies the counit
identities at `(0, 0)`, is cocommutative under swapping the two factors, intertwines stage
transitions (`prodMapCLM_transition_addComul`), and is coassociative (`coassoc_addComul`). No
`p`-regularity assumption on `E` is needed for these identities: compatibility with transitions and
coassociativity are proved first over `ℤ_p` by injectivity of multivariable evaluation, then
transferred to arbitrary coefficient modules along coordinate vectors.

## Main definitions

* `TauCeti.AnalyticStage.eval₂ S`: two-variable evaluation
  `C₀((ZMod (pʰ) × ℕ) × (ZMod (pᵏ) × ℕ), E) →L[S] C(ℤ_p × ℤ_p, E)`.
* `TauCeti.AnalyticStage.addComul S`: additive comultiplication on `LA_h(E)`.

## Main results

* `TauCeti.AnalyticStage.eval₂_natCast_val_add_mul`: explicit double power-series formula on a
  product of discs.
* `TauCeti.AnalyticStage.eval₂_prodSMul`: `eval₂` sends elementary tensors to pointwise scalar
  products of one-variable evaluations.
* `TauCeti.AnalyticStage.eval₂_injective`: `eval₂` is injective when `p` is regular on `E`.
* `TauCeti.AnalyticStage.norm_addComul`: `addComul` preserves the Gauss norm.
* `TauCeti.AnalyticStage.eval₂_addComul`: `(eval₂ S (addComul S c)) (x, y) = eval S c (x + y)`.
* `TauCeti.AnalyticStage.congrLeft_prodComm_addComul`: cocommutativity of `addComul`.
* `TauCeti.AnalyticStage.prodMapCLM_transition_addComul`: `addComul` commutes with raising the
  analytic level.
* `TauCeti.AnalyticStage.coassoc_addComul`: coassociativity of `addComul`.

## References

* P. Colmez, *Fonctions d'une variable p-adique*, Astérisque 330 (2010), §I.4 and §II.2.
* Y. Amice, *Interpolation p-adique*, Bull. Soc. Math. France 92 (1964), 117–180.
-/

public section

open Filter Topology ZeroAtInftyContinuousMap
open scoped ZeroAtInfty

variable {p : ℕ} [hp : Fact p.Prime]

namespace TauCeti

namespace AnalyticStage

section Coe

variable {h : ℕ} {E F : Type*}
  [NormedAddCommGroup E] [Module ℤ_[p] E] [IsBoundedSMul ℤ_[p] E]
  [IsUltrametricDist E] [CompleteSpace E]
  [NormedAddCommGroup F] [Module ℤ_[p] F] [IsBoundedSMul ℤ_[p] F]
  [IsUltrametricDist F] [CompleteSpace F]

/-- Evaluating an analytic-stage expansion at `0 ∈ ℤ_p` returns its `(0, 0)`-coefficient. -/
@[simp]
theorem eval_apply_zero (S : Type*) [Semiring S] [Module S E] [ContinuousConstSMul S E]
    [SMulCommClass ℤ_[p] S E] (c : AnalyticStage p h E) :
    eval S c 0 = c (0, 0) := by
  have : NeZero (p ^ h) := ⟨pow_ne_zero h hp.out.ne_zero⟩
  have h0 : (0 : ℤ_[p]) = ((0 : ZMod (p ^ h)).val : ℤ_[p]) + (p : ℤ_[p]) ^ h * 0 := by simp
  rw [h0, eval_natCast_val_add_mul, tsum_eq_single 0]
  · simp
  · intro n hn
    simp [zero_pow hn]

/-- `transition S c` does not depend on the choice of scalar ring `S`. -/
theorem transition_eq_of_scalars (S₁ S₂ : Type*)
    [Semiring S₁] [Module S₁ E] [ContinuousConstSMul S₁ E] [SMulCommClass ℤ_[p] S₁ E]
    [Semiring S₂] [Module S₂ E] [ContinuousConstSMul S₂ E] [SMulCommClass ℤ_[p] S₂ E]
    (c : AnalyticStage p h E) :
    transition S₁ c = transition S₂ c := by
  ext ⟨a', j⟩
  rw [transition_apply, transition_apply]

/-- `transition` commutes with bounded `ℤ_p`-compatible coefficient maps. -/
theorem compLeft_transition (S : Type*) [Semiring S]
    [Module S E] [ContinuousConstSMul S E] [SMulCommClass ℤ_[p] S E]
    [Module S F] [ContinuousConstSMul S F] [SMulCommClass ℤ_[p] S F]
    [LinearMap.CompatibleSMul E F ℤ_[p] S]
    (w : E →L[S] F) (hw : ∃ C, ∀ x, ‖w x‖ ≤ C * ‖x‖) :
    compLeft w hw ∘L transition (p := p) (h := h) (E := E) S =
      transition (p := p) (h := h) (E := F) S ∘L compLeft w hw := by
  ext c ⟨a', j⟩
  simp only [ContinuousLinearMap.comp_apply, compLeft_apply, transition_apply]
  have hs : Summable fun k ↦ ((k.choose j : ℤ_[p]) *
      ((a'.val / p ^ h : ℕ) : ℤ_[p]) ^ (k - j) * (p : ℤ_[p]) ^ j) •
        c ((a'.val : ZMod (p ^ h)), k) :=
    NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero <| by
      rw [Nat.cofinite_eq_atTop]
      refine squeeze_zero_norm (fun _ ↦ (norm_smul_le _ _).trans
        (mul_le_of_le_one_left (norm_nonneg _) (PadicInt.norm_le_one _))) ?_
      have hinj : Function.Injective fun k : ℕ ↦ ((a'.val : ZMod (p ^ h)), k) :=
        fun _ _ hk ↦ (Prod.ext_iff.1 hk).2
      rw [← Nat.cofinite_eq_atTop]
      exact tendsto_zero_iff_norm_tendsto_zero.mp (c.tendsto_cofinite.comp hinj.tendsto_cofinite)
  simpa only [w.map_smul_of_tower] using (hs.hasSum.mapL w).tsum_eq.symm

end Coe

/-! ### Two-variable stage evaluation -/

section Eval₂

variable {h k : ℕ} {E : Type*}
  [NormedAddCommGroup E] [Module ℤ_[p] E] [IsBoundedSMul ℤ_[p] E]
  [IsUltrametricDist E] [CompleteSpace E]
  (S : Type*) [Semiring S] [Module S E] [ContinuousConstSMul S E] [SMulCommClass ℤ_[p] S E]

private noncomputable def uncurryCLM {X Y : Type*}
    [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] :
    C(X, C(Y, E)) →L[S] C(X × Y, E) where
  toFun := ContinuousMap.uncurry
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := ContinuousMap.continuous_uncurry

omit [CompleteSpace E] in
private theorem norm_uncurryCLM_le {X Y : Type*}
    [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
    (f : C(X, C(Y, E))) :
    ‖uncurryCLM S f‖ ≤ ‖f‖ :=
  (ContinuousMap.norm_le _ (norm_nonneg f)).mpr fun xy ↦
    ((f xy.1).norm_coe_le_norm xy.2).trans (f.norm_coe_le_norm xy.1)

/-- **Two-variable analytic-stage evaluation.** Sends a coefficient family
`F ∈ C₀((ZMod (pʰ) × ℕ) × (ZMod (pᵏ) × ℕ), E)` to the continuous function on `ℤ_p × ℤ_p` obtained
by evaluating the second index in `C(ℤ_p, E)`, then the first index in `C(ℤ_p, C(ℤ_p, E))`, and
uncurrying. -/
noncomputable def eval₂ :
    C₀((ZMod (p ^ h) × ℕ) × (ZMod (p ^ k) × ℕ), E) →L[S] C(ℤ_[p] × ℤ_[p], E) :=
  uncurryCLM S ∘L eval (p := p) (h := h) (E := C(ℤ_[p], E)) S ∘L
    compLeft (eval (p := p) (h := k) (E := E) S)
      ⟨1, fun c ↦ by simpa using norm_eval_le S c⟩ ∘L
      (curryEquiv (I := ZMod (p ^ h) × ℕ) (J := ZMod (p ^ k) × ℕ) S E
        ).toLinearIsometry.toContinuousLinearMap

private theorem eval₂_eq_eval_curry (F : C₀((ZMod (p ^ h) × ℕ) × (ZMod (p ^ k) × ℕ), E))
    (x y : ℤ_[p]) :
    eval₂ S F (x, y) =
      eval (p := p) (h := h) (E := C(ℤ_[p], E)) S
        (compLeft (eval (p := p) (h := k) (E := E) S)
          ⟨1, fun c ↦ by simpa using norm_eval_le S c⟩
            (curryEquiv (I := ZMod (p ^ h) × ℕ) (J := ZMod (p ^ k) × ℕ) S E F)) x y :=
  (rfl)

/-- Two-variable evaluation does not increase norms. -/
theorem norm_eval₂_le (F : C₀((ZMod (p ^ h) × ℕ) × (ZMod (p ^ k) × ℕ), E)) :
    ‖eval₂ S F‖ ≤ ‖F‖ := by
  refine (norm_uncurryCLM_le S _).trans ((norm_eval_le S _).trans ?_)
  exact (norm_compLeft_apply_le (C := 1) (eval (p := p) (h := k) (E := E) S)
    (fun c ↦ by simpa using norm_eval_le S c) _).trans_eq
      (by simp [one_mul])

/-- On the product disc `(a + pʰℤ_p) × (b + pᵏℤ_p)`, `eval₂ S F` is the iterated power series
`∑' i, ∑' j, (uⁱ * vʲ) • F((a, i), (b, j))`. -/
theorem eval₂_natCast_val_add_mul (F : C₀((ZMod (p ^ h) × ℕ) × (ZMod (p ^ k) × ℕ), E))
    (a : ZMod (p ^ h)) (u : ℤ_[p]) (b : ZMod (p ^ k)) (v : ℤ_[p]) :
    eval₂ S F ((a.val : ℤ_[p]) + (p : ℤ_[p]) ^ h * u,
        (b.val : ℤ_[p]) + (p : ℤ_[p]) ^ k * v) =
      ∑' i, ∑' j, (u ^ i * v ^ j) • F ((a, i), (b, j)) := by
  rw [eval₂_eq_eval_curry]
  set y : ℤ_[p] := (b.val : ℤ_[p]) + (p : ℤ_[p]) ^ k * v
  have houter := (hasSum_eval_natCast_val_add_mul S
    (compLeft (eval (p := p) (h := k) (E := E) S)
      ⟨1, fun c ↦ by simpa using norm_eval_le S c⟩
        (curryEquiv (I := ZMod (p ^ h) × ℕ) (J := ZMod (p ^ k) × ℕ) S E F)) a u).mapL
    (ContinuousMap.evalCLM ℤ_[p] y)
  change ContinuousMap.evalCLM ℤ_[p] y _ = _
  rw [← houter.tsum_eq]
  refine tsum_congr fun i ↦ ?_
  simp only [ContinuousMap.evalCLM_apply, ContinuousMap.smul_apply, compLeft_apply]
  rw [eval_natCast_val_add_mul]
  have hinner := (hasSum_eval_natCast_val_add_mul ℤ_[p]
    (curryEquiv (I := ZMod (p ^ h) × ℕ) (J := ZMod (p ^ k) × ℕ) S E F (a, i)) b v).summable
  simpa only [curryEquiv_apply_apply, mul_smul] using (hinner.tsum_const_smul (u ^ i)).symm

/-- `eval₂` sends an elementary tensor `prodSMul f g` to `(x, y) ↦ eval ℤ_p f x • eval S g y`. -/
@[simp]
theorem eval₂_prodSMul (f : AnalyticStage p h ℤ_[p]) (g : AnalyticStage p k E)
    (x y : ℤ_[p]) :
    eval₂ S (prodSMul f g) (x, y) = eval ℤ_[p] f x • eval S g y := by
  obtain ⟨⟨a, u⟩, rfl⟩ := (PadicInt.discHomeomorph p h).surjective x
  obtain ⟨⟨b, v⟩, rfl⟩ := (PadicInt.discHomeomorph p k).surjective y
  simp only [PadicInt.discHomeomorph_apply]
  rw [eval₂_natCast_val_add_mul, eval_natCast_val_add_mul, eval_natCast_val_add_mul]
  have hf := (hasSum_eval_natCast_val_add_mul ℤ_[p] f a u).summable
  have hg := (hasSum_eval_natCast_val_add_mul S g b v).summable
  have hterm : ∀ i j, (u ^ i * v ^ j) • (f (a, i) • g (b, j)) =
      (u ^ i * f (a, i)) • (v ^ j • g (b, j)) := fun i j ↦ by
    rw [smul_smul, smul_smul]
    congr 1
    ring
  have hfg : ∀ i, ∑' j, (u ^ i * v ^ j) • (f (a, i) • g (b, j)) =
      (u ^ i * f (a, i)) • ∑' j, v ^ j • g (b, j) := fun i ↦ by
    simp_rw [hterm i]
    exact hg.tsum_const_smul (u ^ i * f (a, i))
  simp_rw [prodSMul_apply, hfg]
  set val_g : E := ∑' j, v ^ j • g (b, j)
  let smulG : ℤ_[p] →L[ℤ_[p]] E := ContinuousLinearMap.smulRight (1 : ℤ_[p] →L[ℤ_[p]] ℤ_[p]) val_g
  simpa [smulG, smul_eq_mul] using (hf.hasSum.mapL smulG).tsum_eq

/-- Two-variable evaluation is compatible with transition in the second factor. -/
@[simp]
theorem eval₂_sndMapCLM_transition
    (hT : ∃ C, ∀ g : AnalyticStage p k E, ‖transition (p := p) (h := k) (E := E) S g‖ ≤ C * ‖g‖)
    (F : C₀((ZMod (p ^ h) × ℕ) × (ZMod (p ^ k) × ℕ), E)) :
    eval₂ S (sndMapCLM (ZMod (p ^ h) × ℕ)
      (transition (p := p) (h := k) (E := E) S) hT F) = eval₂ S F := by
  have hrow :
      compLeft (eval (p := p) (h := k + 1) (E := E) S)
          ⟨1, fun c ↦ by simpa using norm_eval_le S c⟩
          (curryEquiv (I := ZMod (p ^ h) × ℕ) (J := ZMod (p ^ (k + 1)) × ℕ) S E
            (sndMapCLM (ZMod (p ^ h) × ℕ)
              (transition (p := p) (h := k) (E := E) S) hT F)) =
        compLeft (eval (p := p) (h := k) (E := E) S)
          ⟨1, fun c ↦ by simpa using norm_eval_le S c⟩
          (curryEquiv (I := ZMod (p ^ h) × ℕ) (J := ZMod (p ^ k) × ℕ) S E F) := by
    refine ZeroAtInftyContinuousMap.ext fun i ↦ ?_
    simp
  ext ⟨x, y⟩
  simp only [eval₂_eq_eval_curry, hrow]

/-- Two-variable evaluation is compatible with transition in the first factor. -/
@[simp]
theorem eval₂_fstMapCLM_transition
    (hT : ∃ C, ∀ f : AnalyticStage p h E, ‖transition (p := p) (h := h) (E := E) S f‖ ≤ C * ‖f‖)
    (F : C₀((ZMod (p ^ h) × ℕ) × (ZMod (p ^ k) × ℕ), E)) :
    eval₂ S (fstMapCLM (ZMod (p ^ k) × ℕ)
      (transition (p := p) (h := h) (E := E) S) hT F) = eval₂ S F := by
  classical
  have hmap : eval₂ S ∘L fstMapCLM (ZMod (p ^ k) × ℕ)
      (transition (p := p) (h := h) (E := E) S) hT = eval₂ S := by
    refine ZeroAtInftyContinuousMap.continuousLinearMap_ext fun idx e ↦ ?_
    rcases idx with ⟨i, j⟩
    have h1 : single (i, j) e = prodSMul (single i (1 : ℤ_[p])) (single j e) := by simp
    have h2 : fstMapCLM (ZMod (p ^ k) × ℕ)
        (transition (p := p) (h := h) (E := E) S) hT (single (i, j) e) =
        prodSMul (transition (p := p) (h := h) (E := ℤ_[p]) ℤ_[p]
          (single i (1 : ℤ_[p]))) (single j e) := by
      refine ZeroAtInftyContinuousMap.ext fun ⟨i', j'⟩ ↦ ?_
      have hcol : curryEquiv S E
          (congrLeft S E (Homeomorph.prodComm _ _) (single (i, j) e)) j' =
          if j' = j then single i e else 0 := by
        refine ZeroAtInftyContinuousMap.ext fun a ↦ ?_
        by_cases hj : j' = j <;> by_cases ha : a = i <;> simp [hj, ha]
      simp only [fstMapCLM_apply, hcol, prodSMul_apply, single_apply]
      split_ifs with hj
      · rw [transition_eq_of_scalars S ℤ_[p]]
        let w : ℤ_[p] →L[ℤ_[p]] E := ContinuousLinearMap.smulRight (1 : ℤ_[p] →L[ℤ_[p]] ℤ_[p]) e
        have hw : ∃ C, ∀ r : ℤ_[p], ‖w r‖ ≤ C * ‖r‖ :=
          ⟨‖e‖, fun r ↦ by simpa [w, mul_comm] using norm_smul_le r e⟩
        have hwe := congr($(compLeft_transition (p := p) (h := h) ℤ_[p] w hw)
          (single i (1 : ℤ_[p])) i')
        simpa [w] using hwe.symm
      · simp
    ext ⟨x, y⟩
    rw [ContinuousLinearMap.comp_apply, h2, eval₂_prodSMul, h1, eval₂_prodSMul, eval_transition]
  exact congr($hmap F)

/-- Two-variable evaluation is compatible with simultaneous transitions in both factors. -/
@[simp]
theorem eval₂_prodMapCLM_transition
    (hT₁ : ∃ C, ∀ f : AnalyticStage p h E, ‖transition (p := p) (h := h) (E := E) S f‖ ≤ C * ‖f‖)
    (hT₂ : ∃ C, ∀ g : AnalyticStage p k E, ‖transition (p := p) (h := k) (E := E) S g‖ ≤ C * ‖g‖)
    (F : C₀((ZMod (p ^ h) × ℕ) × (ZMod (p ^ k) × ℕ), E)) :
    eval₂ S (prodMapCLM (transition (p := p) (h := h) (E := E) S) hT₁
      (transition (p := p) (h := k) (E := E) S) hT₂ F) = eval₂ S F := by
  rw [prodMapCLM_def, ContinuousLinearMap.comp_apply, eval₂_sndMapCLM_transition,
    eval₂_fstMapCLM_transition]

omit [IsUltrametricDist E] [CompleteSpace E] in
private theorem isSMulRegular_continuousMap {X : Type*} [TopologicalSpace X]
    (hpE : IsSMulRegular E (p : ℤ_[p])) :
    IsSMulRegular C(X, E) (p : ℤ_[p]) :=
  fun _ _ hfg ↦ ContinuousMap.ext fun x ↦ hpE (DFunLike.congr_fun hfg x)

/-- Two-variable evaluation is injective when multiplication by `p` on `E` is injective. -/
theorem eval₂_injective (hpE : IsSMulRegular E (p : ℤ_[p])) :
    Function.Injective (eval₂ (p := p) (h := h) (k := k) (E := E) S) := by
  intro F G hFG
  have h1 : eval (p := p) (h := h) (E := C(ℤ_[p], E)) S
      (compLeft (eval (p := p) (h := k) (E := E) S) ⟨1, fun c ↦ by simpa using norm_eval_le S c⟩
        (curryEquiv S E F)) =
      eval (p := p) (h := h) (E := C(ℤ_[p], E)) S
      (compLeft (eval (p := p) (h := k) (E := E) S) ⟨1, fun c ↦ by simpa using norm_eval_le S c⟩
        (curryEquiv S E G)) := by
    ext x y
    exact DFunLike.congr_fun hFG (x, y)
  have h2 := eval_injective S (isSMulRegular_continuousMap hpE) h1
  apply (curryEquiv S E).injective
  refine ZeroAtInftyContinuousMap.ext fun i ↦ ?_
  exact eval_injective S hpE (by simpa using DFunLike.congr_fun h2 i)

end Eval₂

/-! ### Additive comultiplication on analytic stages -/

section AddComul

variable {h : ℕ} {E : Type*}
  [NormedAddCommGroup E] [Module ℤ_[p] E] [IsBoundedSMul ℤ_[p] E]
  [IsUltrametricDist E] [CompleteSpace E]

/-- Coefficient of `uⁱ vʲ` in `(q + u + v)ᵏ`. -/
private noncomputable def addComulScalar (q : ℤ_[p]) (i j k : ℕ) : ℤ_[p] :=
  (k.choose (i + j) : ℤ_[p]) * ((i + j).choose i : ℤ_[p]) * q ^ (k - (i + j))

private theorem addComulScalar_eq_zero_of_lt (q : ℤ_[p]) {i j k : ℕ} (hk : k < i + j) :
    addComulScalar q i j k = 0 := by
  simp [addComulScalar, Nat.choose_eq_zero_of_lt hk]

private theorem addComulScalar_comm (q : ℤ_[p]) (i j k : ℕ) :
    addComulScalar q j i k = addComulScalar q i j k := by
  have hchoose : (j + i).choose j = (i + j).choose i := by
    rw [Nat.add_comm j i, Nat.choose_symm_add]
  rw [addComulScalar, addComulScalar, hchoose, Nat.add_comm j i]

private theorem add_pow_eq_sum_addComulScalar (q u v : ℤ_[p]) (k : ℕ) :
    (q + u + v) ^ k =
      ∑ ij ∈ (Finset.range (k + 1)).biUnion Finset.antidiagonal,
        u ^ ij.1 * v ^ ij.2 * addComulScalar q ij.1 ij.2 k := by
  have hdisj : ((Finset.range (k + 1) : Set ℕ)).PairwiseDisjoint Finset.antidiagonal :=
    fun m₁ _ m₂ _ hne ↦ Finset.disjoint_left.mpr fun ij h₁ h₂ ↦
      hne ((Finset.mem_antidiagonal.mp h₁).symm.trans (Finset.mem_antidiagonal.mp h₂))
  rw [Finset.sum_biUnion hdisj]
  have houter : (q + u + v) ^ k =
      ∑ m ∈ Finset.range (k + 1), (u + v) ^ m * q ^ (k - m) * (k.choose m : ℤ_[p]) := by
    rw [show q + u + v = (u + v) + q by ring, add_pow]
  rw [houter]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  rw [add_pow u v m, Finset.sum_mul, Finset.sum_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have him : i + (m - i) = m := Nat.add_sub_of_le (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
  simp only [addComulScalar, him]
  ring

private noncomputable def addComulCoeff (c : AnalyticStage p h E)
    (idx : (ZMod (p ^ h) × ℕ) × (ZMod (p ^ h) × ℕ)) : E :=
  ∑' k, addComulScalar (((idx.1.1.val + idx.2.1.val) / p ^ h : ℕ) : ℤ_[p])
    idx.1.2 idx.2.2 k • c (idx.1.1 + idx.2.1, k)

private theorem summable_addComulScalar_smul (c : AnalyticStage p h E) (a : ZMod (p ^ h))
    (q : ℤ_[p]) (i j : ℕ) :
    Summable fun k ↦ addComulScalar q i j k • c (a, k) :=
  NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero <| by
    rw [Nat.cofinite_eq_atTop]
    refine squeeze_zero_norm (fun _ ↦ (norm_smul_le _ _).trans
      (mul_le_of_le_one_left (norm_nonneg _) (PadicInt.norm_le_one _))) ?_
    have hinj : Function.Injective fun k : ℕ ↦ (a, k) := fun _ _ hk ↦ (Prod.ext_iff.1 hk).2
    rw [← Nat.cofinite_eq_atTop]
    exact tendsto_zero_iff_norm_tendsto_zero.mp (c.tendsto_cofinite.comp hinj.tendsto_cofinite)

omit [CompleteSpace E] in
private theorem norm_addComulCoeff_le (c : AnalyticStage p h E)
    (idx : (ZMod (p ^ h) × ℕ) × (ZMod (p ^ h) × ℕ)) :
    ‖addComulCoeff c idx‖ ≤ ‖c‖ :=
  IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (norm_nonneg c) fun _ ↦
    (norm_smul_le _ _).trans <|
      (mul_le_of_le_one_left (norm_nonneg _) (PadicInt.norm_le_one _)).trans
        (c.norm_coe_le_norm _)

omit [CompleteSpace E] in
private theorem tendsto_addComulCoeff (c : AnalyticStage p h E) :
    Tendsto (addComulCoeff c) cofinite (𝓝 0) := by
  have : NeZero (p ^ h) := ⟨pow_ne_zero h hp.out.ne_zero⟩
  refine NormedAddGroup.tendsto_nhds_zero.2 fun ε hε ↦ eventually_cofinite.2 ?_
  have hS : {x : ZMod (p ^ h) × ℕ | ¬‖c x‖ < ε / 2}.Finite :=
    eventually_cofinite.1 (NormedAddGroup.tendsto_nhds_zero.1 c.tendsto_cofinite _ (half_pos hε))
  let N : ℕ := hS.toFinset.sup Prod.snd + 1
  let box : Finset ((ZMod (p ^ h) × ℕ) × (ZMod (p ^ h) × ℕ)) :=
    (Finset.univ ×ˢ Finset.range N) ×ˢ (Finset.univ ×ˢ Finset.range N)
  refine box.finite_toSet.subset fun idx hidx ↦ ?_
  by_contra hnotmem
  have hij : N ≤ idx.1.2 + idx.2.2 := by
    simp only [box, Finset.mem_coe, Finset.mem_product, Finset.mem_univ, Finset.mem_range,
      true_and, not_and_or, not_lt] at hnotmem
    omega
  refine hidx (lt_of_le_of_lt ?_ (half_lt_self hε))
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (half_pos hε).le fun k ↦ ?_
  by_cases hk : k < idx.1.2 + idx.2.2
  · simp [addComulScalar_eq_zero_of_lt _ hk, (half_pos hε).le]
  · have hkN : hS.toFinset.sup Prod.snd < k := by omega
    have hck : ‖c (idx.1.1 + idx.2.1, k)‖ < ε / 2 := by
      by_contra hbad
      have hmem : (idx.1.1 + idx.2.1, k) ∈ hS.toFinset := hS.mem_toFinset.mpr hbad
      exact hkN.not_ge (Finset.le_sup (f := Prod.snd) hmem)
    exact ((norm_smul_le _ _).trans
      (mul_le_of_le_one_left (norm_nonneg _) (PadicInt.norm_le_one _))).trans hck.le

variable (S : Type*) [Semiring S] [Module S E] [ContinuousConstSMul S E] [SMulCommClass ℤ_[p] S E]

/-- **Additive comultiplication on `LA_h(E)`.** Re-expands `x + y` on the product discs
`(a + pʰℤ_p) × (b + pʰℤ_p)` inside the disc of `a + b` with carry digit
`q = ⌊(a.val + b.val) / pʰ⌋`. -/
noncomputable def addComul :
    AnalyticStage p h E →L[S] C₀((ZMod (p ^ h) × ℕ) × (ZMod (p ^ h) × ℕ), E) :=
  let L : AnalyticStage p h E →ₗ[S] C₀((ZMod (p ^ h) × ℕ) × (ZMod (p ^ h) × ℕ), E) :=
    { toFun c := mkOfDiscrete (addComulCoeff c) (tendsto_addComulCoeff c)
      map_add' c d := by
        ext idx
        simp only [coe_mkOfDiscrete, addComulCoeff, FunLike.coe_add, Pi.add_apply, smul_add]
        exact (summable_addComulScalar_smul c _ _ _ _).tsum_add
          (summable_addComulScalar_smul d _ _ _ _)
      map_smul' s c := by
        ext idx
        simp only [coe_mkOfDiscrete, addComulCoeff, FunLike.coe_smul, Pi.smul_apply,
          RingHom.id_apply, smul_comm _ s]
        exact (summable_addComulScalar_smul c _ _ _ _).tsum_const_smul s }
  { L with
    cont := AddMonoidHomClass.continuous_of_bound L 1 fun c ↦ by
      rw [one_mul]
      refine (ZeroAtInftyContinuousMap.norm_le (norm_nonneg c)).mpr fun idx ↦ ?_
      simp only [L, LinearMap.coe_mk, AddHom.coe_mk, coe_mkOfDiscrete]
      exact norm_addComulCoeff_le c idx }

private theorem coe_addComul (c : AnalyticStage p h E) :
    ⇑(addComul S c) = addComulCoeff c :=
  coe_mkOfDiscrete _ _

/-- Explicit coefficient formula for `addComul S c` at `((a, i), (b, j))`. -/
theorem addComul_apply (c : AnalyticStage p h E) (a b : ZMod (p ^ h)) (i j : ℕ) :
    addComul S c ((a, i), (b, j)) =
      ∑' k, ((k.choose (i + j) : ℤ_[p]) * ((i + j).choose i : ℤ_[p]) *
        (((a.val + b.val) / p ^ h : ℕ) : ℤ_[p]) ^ (k - (i + j))) • c (a + b, k) := by
  rw [coe_addComul]
  rfl

/-- `addComul S c` does not depend on the choice of scalar ring `S`. -/
theorem addComul_eq_of_scalars (S₂ : Type*) [Semiring S₂] [Module S₂ E]
    [ContinuousConstSMul S₂ E] [SMulCommClass ℤ_[p] S₂ E] (c : AnalyticStage p h E) :
    addComul S c = addComul S₂ c := by
  ext ⟨⟨a, i⟩, ⟨b, j⟩⟩
  rw [addComul_apply, addComul_apply]

/-- **Right counit law**: evaluating the second factor at `(0, 0)` recovers `c`. -/
@[simp]
theorem addComul_apply_zero_right (c : AnalyticStage p h E) (a : ZMod (p ^ h)) (i : ℕ) :
    addComul S c ((a, i), (0, 0)) = c (a, i) := by
  have : NeZero (p ^ h) := ⟨pow_ne_zero h hp.out.ne_zero⟩
  rw [addComul_apply, ZMod.val_zero, add_zero, add_zero, Nat.div_eq_of_lt (ZMod.val_lt a),
    Nat.choose_self, tsum_eq_single i]
  · simp
  · intro k hki
    by_cases hlt : k < i
    · simp [Nat.choose_eq_zero_of_lt hlt]
    · have hsub : k - i ≠ 0 := by omega
      simp [hsub]

/-- **Cocommutativity of `addComul`**: swapping the two stage factors fixes `addComul S c`. -/
@[simp]
theorem congrLeft_prodComm_addComul (c : AnalyticStage p h E) :
    congrLeft S E (Homeomorph.prodComm _ _) (addComul S c) = addComul S c := by
  ext ⟨⟨a, i⟩, ⟨b, j⟩⟩
  simp only [congrLeft_apply, Homeomorph.prodComm_symm, Homeomorph.coe_prodComm, Prod.swap_prod_mk,
    coe_addComul, addComulCoeff, Nat.add_comm b.val a.val, add_comm b a, addComulScalar_comm]

/-- **Left counit law**: evaluating the first factor at `(0, 0)` recovers `c`. -/
@[simp]
theorem addComul_apply_zero_left (c : AnalyticStage p h E) (b : ZMod (p ^ h)) (j : ℕ) :
    addComul S c ((0, 0), (b, j)) = c (b, j) := by
  rw [← addComul_apply_zero_right S c b j]
  simpa only [congrLeft_apply, Homeomorph.prodComm_symm, Homeomorph.coe_prodComm,
    Prod.swap_prod_mk] using congr($(congrLeft_prodComm_addComul S c) ((b, j), (0, 0)))

/-- `addComul` preserves the Gauss norm on every analytic stage. -/
@[simp]
theorem norm_addComul (c : AnalyticStage p h E) : ‖addComul S c‖ = ‖c‖ := by
  refine le_antisymm ((ZeroAtInftyContinuousMap.norm_le (norm_nonneg c)).mpr fun idx ↦ ?_) ?_
  · rw [coe_addComul]
    exact norm_addComulCoeff_le c idx
  · refine (ZeroAtInftyContinuousMap.norm_le (norm_nonneg _)).mpr fun ⟨a, i⟩ ↦ ?_
    simpa only [addComul_apply_zero_right] using (addComul S c).norm_coe_le_norm ((a, i), (0, 0))

/-- `addComul` commutes with bounded `ℤ_p`-compatible coefficient maps. -/
theorem compLeft_addComul {F : Type*}
    [NormedAddCommGroup F] [Module ℤ_[p] F] [IsBoundedSMul ℤ_[p] F]
    [IsUltrametricDist F] [CompleteSpace F]
    [Module S F] [ContinuousConstSMul S F] [SMulCommClass ℤ_[p] S F]
    [LinearMap.CompatibleSMul E F ℤ_[p] S]
    (w : E →L[S] F) (hw : ∃ C, ∀ x, ‖w x‖ ≤ C * ‖x‖) :
    compLeft w hw ∘L addComul (p := p) (h := h) (E := E) S =
      addComul (p := p) (h := h) (E := F) S ∘L compLeft w hw := by
  ext c ⟨⟨a, i⟩, ⟨b, j⟩⟩
  simp only [ContinuousLinearMap.comp_apply, compLeft_apply, coe_addComul, addComulCoeff]
  simpa only [w.map_smul_of_tower] using
    ((summable_addComulScalar_smul c (a + b) _ i j).hasSum.mapL w).tsum_eq.symm

private theorem summable_eval₂_addComul (c : AnalyticStage p h E) (a : ZMod (p ^ h))
    (q u v : ℤ_[p]) :
    Summable (fun p_idx : (ℕ × ℕ) × ℕ ↦
      (u ^ p_idx.1.1 * v ^ p_idx.1.2 * addComulScalar q p_idx.1.1 p_idx.1.2 p_idx.2) •
        c (a, p_idx.2)) := by
  refine NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ?_
  refine NormedAddGroup.tendsto_nhds_zero.2 fun ε hε ↦ eventually_cofinite.2 ?_
  have hinj : Function.Injective fun k : ℕ ↦ (a, k) := fun _ _ hk ↦ (Prod.ext_iff.1 hk).2
  have hc : Tendsto (fun k ↦ c (a, k)) atTop (𝓝 0) := by
    rw [← Nat.cofinite_eq_atTop]
    exact c.tendsto_cofinite.comp hinj.tendsto_cofinite
  obtain ⟨N, hN⟩ := eventually_atTop.1 (NormedAddGroup.tendsto_nhds_zero.1 hc ε hε)
  refine (((Finset.range N ×ˢ Finset.range N) ×ˢ Finset.range N : Finset _).finite_toSet).subset
    fun ⟨⟨i, j⟩, k⟩ hbad ↦ ?_
  have hle : i + j ≤ k := by
    by_contra hlt
    exact hbad (by simp [addComulScalar_eq_zero_of_lt q (Nat.lt_of_not_ge hlt), hε])
  have hkN : k < N := by
    by_contra hge
    refine hbad (lt_of_le_of_lt ?_ (hN k (Nat.le_of_not_lt hge)))
    exact (norm_smul_le _ _).trans (mul_le_of_le_one_left (norm_nonneg _) (PadicInt.norm_le_one _))
  simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_range]
  omega

/-- **Evaluation of `addComul`**: two-variable evaluation of `addComul S c` is `c` evaluated along
addition `(x, y) ↦ x + y`. -/
@[simp]
theorem eval₂_addComul (c : AnalyticStage p h E) (x y : ℤ_[p]) :
    eval₂ S (addComul S c) (x, y) = eval S c (x + y) := by
  have : NeZero (p ^ h) := ⟨pow_ne_zero h hp.out.ne_zero⟩
  obtain ⟨⟨a, u⟩, rfl⟩ := (PadicInt.discHomeomorph p h).surjective x
  obtain ⟨⟨b, v⟩, rfl⟩ := (PadicInt.discHomeomorph p h).surjective y
  simp only [PadicInt.discHomeomorph_apply]
  set q : ℤ_[p] := (((a.val + b.val) / p ^ h : ℕ) : ℤ_[p])
  have hxy : ((a.val : ℤ_[p]) + (p : ℤ_[p]) ^ h * u) + ((b.val : ℤ_[p]) + (p : ℤ_[p]) ^ h * v) =
      ((a + b).val : ℤ_[p]) + (p : ℤ_[p]) ^ h * (q + u + v) := by
    have hval : a.val + b.val = (a + b).val + p ^ h * ((a.val + b.val) / p ^ h) := by
      rw [ZMod.val_add, Nat.mod_add_div]
    have hcast : (a.val : ℤ_[p]) + (b.val : ℤ_[p]) =
        ((a + b).val : ℤ_[p]) + (p : ℤ_[p]) ^ h * q := by
      calc (a.val : ℤ_[p]) + (b.val : ℤ_[p])
        _ = ((a.val + b.val : ℕ) : ℤ_[p]) := (Nat.cast_add _ _).symm
        _ = (((a + b).val + p ^ h * ((a.val + b.val) / p ^ h) : ℕ) : ℤ_[p]) :=
          congrArg (Nat.cast : ℕ → ℤ_[p]) hval
        _ = ((a + b).val : ℤ_[p]) + (p : ℤ_[p]) ^ h * q := by
          simp only [q, Nat.cast_add, Nat.cast_mul, Nat.cast_pow]
    linear_combination hcast
  rw [eval₂_natCast_val_add_mul, hxy, eval_natCast_val_add_mul]
  have hΦ := summable_eval₂_addComul c (a + b) q u v
  have hrow : ∀ i j, (u ^ i * v ^ j) • addComul S c ((a, i), (b, j)) =
      ∑' k, (u ^ i * v ^ j * addComulScalar q i j k) • c (a + b, k) := fun i j ↦ by
    rw [coe_addComul]
    simpa only [addComulCoeff, mul_smul] using
      ((summable_addComulScalar_smul c (a + b) q i j).tsum_const_smul (u ^ i * v ^ j)).symm
  simp_rw [hrow]
  rw [← hΦ.prod.tsum_prod, ← hΦ.tsum_comm]
  refine tsum_congr fun k ↦ ?_
  rw [add_pow_eq_sum_addComulScalar q u v k, Finset.sum_smul]
  refine tsum_eq_sum fun ij hij ↦ ?_
  have hk : k < ij.1 + ij.2 := by
    by_contra hle
    exact hij (Finset.mem_biUnion.mpr ⟨ij.1 + ij.2,
      Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_of_not_lt hle)),
      Finset.mem_antidiagonal.mpr rfl⟩)
  simp [addComulScalar_eq_zero_of_lt q hk]

private theorem prodMapCLM_transition_addComul_Zp_scalars (c : AnalyticStage p h E) :
    let tE := transition (p := p) (h := h) (E := E) ℤ_[p]
    let bE : ∃ C, ∀ f : AnalyticStage p h E, ‖tE f‖ ≤ C * ‖f‖ :=
      ⟨1, fun f ↦ by simpa [tE] using norm_transition_le ℤ_[p] f⟩
    prodMapCLM tE bE tE bE (addComul ℤ_[p] c) = addComul ℤ_[p] (tE c) := by
  classical
  let tZp := transition (p := p) (h := h) (E := ℤ_[p]) ℤ_[p]
  let bZp : ∃ C, ∀ f : AnalyticStage p h ℤ_[p], ‖tZp f‖ ≤ C * ‖f‖ :=
    ⟨1, fun f ↦ by simpa [tZp] using norm_transition_le ℤ_[p] f⟩
  have hZp : ∀ d : AnalyticStage p h ℤ_[p],
      prodMapCLM tZp bZp tZp bZp (addComul ℤ_[p] d) = addComul ℤ_[p] (tZp d) := fun d ↦ by
    apply eval₂_injective ℤ_[p] (IsSMulRegular.of_ne_zero (Nat.cast_ne_zero.mpr hp.out.ne_zero))
    ext ⟨x, y⟩
    rw [eval₂_prodMapCLM_transition, eval₂_addComul, eval₂_addComul, eval_transition]
  let tE := transition (p := p) (h := h) (E := E) ℤ_[p]
  let bE : ∃ C, ∀ f : AnalyticStage p h E, ‖tE f‖ ≤ C * ‖f‖ :=
    ⟨1, fun f ↦ by simpa [tE] using norm_transition_le ℤ_[p] f⟩
  have hE_Zp : prodMapCLM tE bE tE bE ∘L addComul (p := p) (h := h) (E := E) ℤ_[p] =
      addComul (p := p) (h := h + 1) (E := E) ℤ_[p] ∘L tE := by
    refine ZeroAtInftyContinuousMap.continuousLinearMap_ext fun idx e ↦ ?_
    let w : ℤ_[p] →L[ℤ_[p]] E := ContinuousLinearMap.smulRight (1 : ℤ_[p] →L[ℤ_[p]] ℤ_[p]) e
    have hw : ∃ C, ∀ r : ℤ_[p], ‖w r‖ ≤ C * ‖r‖ :=
      ⟨‖e‖, fun r ↦ by simpa [w, mul_comm] using norm_smul_le r e⟩
    rw [show single idx e = compLeft w hw (single idx (1 : ℤ_[p])) by simp [w]]
    simp only [ContinuousLinearMap.comp_apply]
    have h1 := congr($(compLeft_addComul (p := p) (h := h) ℤ_[p] w hw) (single idx (1 : ℤ_[p])))
    have h2 := congr($(compLeft_transition (p := p) (h := h) ℤ_[p] w hw) (single idx (1 : ℤ_[p])))
    have h3 := congr($(compLeft_addComul (p := p) (h := h + 1) ℤ_[p] w hw)
      (tZp (single idx (1 : ℤ_[p]))))
    simp only [ContinuousLinearMap.comp_apply] at h1 h2 h3
    calc prodMapCLM tE bE tE bE (addComul ℤ_[p] (compLeft w hw (single idx 1)))
        = sndMapCLM _ tE bE (fstMapCLM _ tE bE (compLeft w hw (addComul ℤ_[p] (single idx 1)))) :=
          by rw [prodMapCLM_def, ContinuousLinearMap.comp_apply, h1]
      _ = compLeft w hw
            (sndMapCLM _ tZp bZp (fstMapCLM _ tZp bZp (addComul ℤ_[p] (single idx 1)))) := by
          rw [← compLeft_fstMapCLM w hw w hw tZp bZp tE bE
              (compLeft_transition (p := p) (h := h) ℤ_[p] w hw),
            ← compLeft_sndMapCLM w hw w hw tZp bZp tE bE
              (compLeft_transition (p := p) (h := h) ℤ_[p] w hw)]
      _ = compLeft w hw (prodMapCLM tZp bZp tZp bZp (addComul ℤ_[p] (single idx 1))) := by
          rw [prodMapCLM_def, ContinuousLinearMap.comp_apply]
      _ = addComul ℤ_[p] (tE (compLeft w hw (single idx 1))) := by rw [hZp, h3, h2]
  exact congr($hE_Zp c)

/-- **Compatibility of `addComul` with stage transitions** in both factors. Holds for arbitrary
complete ultrametric `ℤ_p`-modules `E`, without any `p`-regularity hypothesis. -/
theorem prodMapCLM_transition_addComul
    (hT₁ : ∃ C, ∀ f : AnalyticStage p h E, ‖transition (p := p) (h := h) (E := E) S f‖ ≤ C * ‖f‖)
    (hT₂ : ∃ C, ∀ g : AnalyticStage p h E, ‖transition (p := p) (h := h) (E := E) S g‖ ≤ C * ‖g‖)
    (c : AnalyticStage p h E) :
    prodMapCLM (transition (p := p) (h := h) (E := E) S) hT₁
      (transition (p := p) (h := h) (E := E) S) hT₂ (addComul S c) =
      addComul S (transition S c) := by
  let tE := transition (p := p) (h := h) (E := E) ℤ_[p]
  let bE : ∃ C, ∀ f : AnalyticStage p h E, ‖tE f‖ ≤ C * ‖f‖ :=
    ⟨1, fun f ↦ by simpa [tE] using norm_transition_le ℤ_[p] f⟩
  calc prodMapCLM (transition (p := p) (h := h) (E := E) S) hT₁
        (transition (p := p) (h := h) (E := E) S) hT₂ (addComul S c)
      = prodMapCLM tE bE tE bE (addComul ℤ_[p] c) := by
        refine ZeroAtInftyContinuousMap.ext fun ⟨i', j'⟩ ↦ ?_
        simp only [prodMapCLM_def, ContinuousLinearMap.comp_apply, sndMapCLM_apply, tE]
        rw [transition_eq_of_scalars S ℤ_[p]]
        refine congrArg (fun g ↦ transition ℤ_[p] g j') (ZeroAtInftyContinuousMap.ext fun a ↦ ?_)
        simp only [curryEquiv_apply_apply, fstMapCLM_apply]
        rw [transition_eq_of_scalars S ℤ_[p]]
        refine congrArg (fun g ↦ transition ℤ_[p] g i') (ZeroAtInftyContinuousMap.ext fun b ↦ ?_)
        rw [addComul_eq_of_scalars S ℤ_[p]]
        simp only [curryEquiv_apply_apply, congrLeft_apply, Homeomorph.prodComm_symm,
          Homeomorph.coe_prodComm, Prod.swap_prod_mk]
    _ = addComul ℤ_[p] (tE c) := prodMapCLM_transition_addComul_Zp_scalars c
    _ = addComul S (transition S c) := by
        simp only [tE]
        rw [← transition_eq_of_scalars S ℤ_[p], ← addComul_eq_of_scalars S ℤ_[p]]

/-- Three-variable auxiliary evaluation `C₀(I × (I × I), E) →L[S] C(ℤ_p, C(ℤ_p × ℤ_p, E))`. -/
private noncomputable def eval₃Aux :
    C₀((ZMod (p ^ h) × ℕ) × ((ZMod (p ^ h) × ℕ) × (ZMod (p ^ h) × ℕ)), E) →L[S]
      C(ℤ_[p], C(ℤ_[p] × ℤ_[p], E)) :=
  eval (p := p) (h := h) (E := C(ℤ_[p] × ℤ_[p], E)) S ∘L
    compLeft (eval₂ (p := p) (h := h) (k := h) (E := E) S)
      ⟨1, fun F ↦ by simpa using norm_eval₂_le S F⟩ ∘L
    (curryEquiv (I := ZMod (p ^ h) × ℕ)
      (J := (ZMod (p ^ h) × ℕ) × (ZMod (p ^ h) × ℕ)) S E).toLinearIsometry.toContinuousLinearMap

private theorem eval₃Aux_injective (hpE : IsSMulRegular E (p : ℤ_[p])) :
    Function.Injective (eval₃Aux (p := p) (h := h) (E := E) S) := by
  intro A B hAB
  have h1 := eval_injective S (isSMulRegular_continuousMap hpE) hAB
  apply (curryEquiv S E).injective
  refine ZeroAtInftyContinuousMap.ext fun i ↦ ?_
  exact eval₂_injective S hpE (by simpa using DFunLike.congr_fun h1 i)

private theorem eval_single_apply {F : Type*} [NormedAddCommGroup F] [Module ℤ_[p] F]
    [IsBoundedSMul ℤ_[p] F] [IsUltrametricDist F] [CompleteSpace F]
    (i₁ : ZMod (p ^ h)) (i₂ : ℕ) (v : F) (x : ℤ_[p]) :
    eval ℤ_[p] (single (i₁, i₂) v) x = eval ℤ_[p] (single (i₁, i₂) (1 : ℤ_[p])) x • v := by
  obtain ⟨⟨a, u⟩, rfl⟩ := (PadicInt.discHomeomorph p h).surjective x
  simp only [PadicInt.discHomeomorph_apply, eval_natCast_val_add_mul]
  by_cases ha : a = i₁
  · subst ha
    rw [tsum_eq_single i₂ (fun n hn ↦ by simp [single_apply, hn]),
      tsum_eq_single i₂ (fun n hn ↦ by simp [single_apply, hn])]
    simp [smul_eq_mul]
  · simp [single_apply, ha]

private theorem eval₃Aux_prodSMul_apply (f : AnalyticStage p h ℤ_[p])
    (G : C₀((ZMod (p ^ h) × ℕ) × (ZMod (p ^ h) × ℕ), ℤ_[p])) (x y z : ℤ_[p]) :
    eval₃Aux ℤ_[p] (prodSMul f G) x (y, z) = eval ℤ_[p] f x * eval₂ ℤ_[p] G (y, z) := by
  classical
  let evYZ : C(ℤ_[p] × ℤ_[p], ℤ_[p]) →L[ℤ_[p]] ℤ_[p] := ContinuousMap.evalCLM ℤ_[p] (y, z)
  let evX : C(ℤ_[p], C(ℤ_[p] × ℤ_[p], ℤ_[p])) →L[ℤ_[p]] C(ℤ_[p] × ℤ_[p], ℤ_[p]) :=
    ContinuousMap.evalCLM ℤ_[p] x
  let pLin : AnalyticStage p h ℤ_[p] →ₗ[ℤ_[p]]
      C₀((ZMod (p ^ h) × ℕ) × ((ZMod (p ^ h) × ℕ) × (ZMod (p ^ h) × ℕ)), ℤ_[p]) :=
    { toFun := fun f' ↦ prodSMul f' G
      map_add' := fun f₁ f₂ ↦ add_prodSMul f₁ f₂ G
      map_smul' := fun r f' ↦ smul_prodSMul r f' G }
  let pCLM : AnalyticStage p h ℤ_[p] →L[ℤ_[p]]
      C₀((ZMod (p ^ h) × ℕ) × ((ZMod (p ^ h) × ℕ) × (ZMod (p ^ h) × ℕ)), ℤ_[p]) :=
    { pLin with
      cont := AddMonoidHomClass.continuous_of_bound pLin ‖G‖ fun f' ↦
        (norm_prodSMul_le f' G).trans_eq (mul_comm _ _) }
  have hL : evYZ ∘L evX ∘L eval₃Aux ℤ_[p] ∘L pCLM =
      ContinuousLinearMap.smulRight (ContinuousMap.evalCLM ℤ_[p] x ∘L eval ℤ_[p])
        (eval₂ ℤ_[p] G (y, z)) := by
    refine ZeroAtInftyContinuousMap.continuousLinearMap_ext_single_one fun ⟨i₁, i₂⟩ ↦ ?_
    have hcur : compLeft (eval₂ (p := p) (h := h) (k := h) (E := ℤ_[p]) ℤ_[p])
        ⟨1, fun F ↦ by simpa using norm_eval₂_le ℤ_[p] F⟩
        (curryEquiv ℤ_[p] ℤ_[p] (prodSMul (single (i₁, i₂) (1 : ℤ_[p])) G)) =
        single (i₁, i₂) (eval₂ ℤ_[p] G) := by
      refine ZeroAtInftyContinuousMap.ext fun i' ↦ ?_
      by_cases hi : i' = (i₁, i₂) <;> simp [hi]
    simp only [pCLM, pLin, evX, evYZ, eval₃Aux, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk,
      LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry,
      ContinuousMap.evalCLM_apply, ContinuousLinearMap.smulRight_apply, hcur]
    rw [eval_single_apply i₁ i₂ (eval₂ ℤ_[p] G) x]
    simp [smul_eq_mul]
  simpa only [pCLM, pLin, evX, evYZ, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_mk',
    LinearMap.coe_mk, AddHom.coe_mk, ContinuousMap.evalCLM_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul] using congr($hL f)

private theorem eval₃Aux_sndMapCLM_addComul_Zp
    (bZp : ∃ C, ∀ g : AnalyticStage p h ℤ_[p],
      ‖addComul (p := p) (h := h) (E := ℤ_[p]) ℤ_[p] g‖ ≤ C * ‖g‖)
    (F : C₀((ZMod (p ^ h) × ℕ) × (ZMod (p ^ h) × ℕ), ℤ_[p])) (x y z : ℤ_[p]) :
    eval₃Aux ℤ_[p]
      (sndMapCLM (ZMod (p ^ h) × ℕ)
        (addComul (p := p) (h := h) (E := ℤ_[p]) ℤ_[p]) bZp F) x (y, z) =
      eval₂ ℤ_[p] F (x, y + z) := by
  classical
  let evYZ : C(ℤ_[p] × ℤ_[p], ℤ_[p]) →L[ℤ_[p]] ℤ_[p] := ContinuousMap.evalCLM ℤ_[p] (y, z)
  let evX : C(ℤ_[p], C(ℤ_[p] × ℤ_[p], ℤ_[p])) →L[ℤ_[p]] C(ℤ_[p] × ℤ_[p], ℤ_[p]) :=
    ContinuousMap.evalCLM ℤ_[p] x
  have hmap : evYZ ∘L evX ∘L eval₃Aux ℤ_[p] ∘L
      sndMapCLM (ZMod (p ^ h) × ℕ)
        (addComul (p := p) (h := h) (E := ℤ_[p]) ℤ_[p]) bZp =
      ContinuousMap.evalCLM ℤ_[p] (x, y + z) ∘L eval₂ (p := p) (h := h) (k := h) ℤ_[p] := by
    refine ZeroAtInftyContinuousMap.continuousLinearMap_ext_single_one fun ⟨i, j⟩ ↦ ?_
    have h1 : single (i, j) (1 : ℤ_[p]) =
        prodSMul (single i (1 : ℤ_[p])) (single j (1 : ℤ_[p])) := by simp
    simp only [h1, ContinuousLinearMap.comp_apply, sndMapCLM_prodSMul, evX, evYZ,
      ContinuousMap.evalCLM_apply, eval₃Aux_prodSMul_apply, eval₂_addComul, eval₂_prodSMul,
      smul_eq_mul]
  exact congr($hmap F)

private theorem eval₃Aux_prodAssoc_prodSMul_apply
    (H : C₀((ZMod (p ^ h) × ℕ) × (ZMod (p ^ h) × ℕ), ℤ_[p]))
    (g : AnalyticStage p h ℤ_[p]) (x y z : ℤ_[p]) :
    eval₃Aux ℤ_[p] (congrLeft ℤ_[p] ℤ_[p] (Homeomorph.prodAssoc _ _ _) (prodSMul H g)) x (y, z) =
      eval₂ ℤ_[p] H (x, y) * eval ℤ_[p] g z := by
  classical
  let evYZ : C(ℤ_[p] × ℤ_[p], ℤ_[p]) →L[ℤ_[p]] ℤ_[p] := ContinuousMap.evalCLM ℤ_[p] (y, z)
  let evX : C(ℤ_[p], C(ℤ_[p] × ℤ_[p], ℤ_[p])) →L[ℤ_[p]] C(ℤ_[p] × ℤ_[p], ℤ_[p]) :=
    ContinuousMap.evalCLM ℤ_[p] x
  let pLin : C₀((ZMod (p ^ h) × ℕ) × (ZMod (p ^ h) × ℕ), ℤ_[p]) →ₗ[ℤ_[p]]
      C₀(((ZMod (p ^ h) × ℕ) × (ZMod (p ^ h) × ℕ)) × (ZMod (p ^ h) × ℕ), ℤ_[p]) :=
    { toFun := fun H' ↦ prodSMul H' g
      map_add' := fun H₁ H₂ ↦ add_prodSMul H₁ H₂ g
      map_smul' := fun r H' ↦ smul_prodSMul r H' g }
  let pG : C₀((ZMod (p ^ h) × ℕ) × (ZMod (p ^ h) × ℕ), ℤ_[p]) →L[ℤ_[p]]
      C₀(((ZMod (p ^ h) × ℕ) × (ZMod (p ^ h) × ℕ)) × (ZMod (p ^ h) × ℕ), ℤ_[p]) :=
    { pLin with
      cont := AddMonoidHomClass.continuous_of_bound pLin ‖g‖ fun H' ↦
        (norm_prodSMul_le H' g).trans_eq (mul_comm _ _) }
  have hH : evYZ ∘L evX ∘L eval₃Aux ℤ_[p] ∘L
      (congrLeft ℤ_[p] ℤ_[p]
        (Homeomorph.prodAssoc (ZMod (p ^ h) × ℕ) (ZMod (p ^ h) × ℕ) (ZMod (p ^ h) × ℕ))
        ).toLinearIsometry.toContinuousLinearMap ∘L pG =
      ContinuousLinearMap.smulRight
        (ContinuousMap.evalCLM ℤ_[p] (x, y) ∘L eval₂ (p := p) (h := h) (k := h) ℤ_[p])
        (eval ℤ_[p] g z) := by
    refine ZeroAtInftyContinuousMap.continuousLinearMap_ext_single_one fun ⟨a, b⟩ ↦ ?_
    have hab : single (a, b) (1 : ℤ_[p]) =
        prodSMul (single a (1 : ℤ_[p])) (single b (1 : ℤ_[p])) := by simp
    simp only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
      LinearIsometryEquiv.coe_toLinearIsometry, pG, pLin, ContinuousLinearMap.coe_mk',
      LinearMap.coe_mk, AddHom.coe_mk, hab, congrLeft_prodAssoc_prodSMul, evX, evYZ,
      ContinuousMap.evalCLM_apply, eval₃Aux_prodSMul_apply, eval₂_prodSMul,
      ContinuousLinearMap.smulRight_apply, smul_eq_mul, mul_assoc]
  simpa only [evX, evYZ, pG, pLin, ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry,
    ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk, ContinuousMap.evalCLM_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul] using congr($hH H)

private theorem eval₃Aux_prodAssoc_fstMapCLM_addComul_Zp
    (bZp : ∃ C, ∀ f : AnalyticStage p h ℤ_[p],
      ‖addComul (p := p) (h := h) (E := ℤ_[p]) ℤ_[p] f‖ ≤ C * ‖f‖)
    (F : C₀((ZMod (p ^ h) × ℕ) × (ZMod (p ^ h) × ℕ), ℤ_[p])) (x y z : ℤ_[p]) :
    eval₃Aux ℤ_[p] (congrLeft ℤ_[p] ℤ_[p] (Homeomorph.prodAssoc _ _ _)
      (fstMapCLM (ZMod (p ^ h) × ℕ)
        (addComul (p := p) (h := h) (E := ℤ_[p]) ℤ_[p]) bZp F)) x (y, z) =
      eval₂ ℤ_[p] F (x + y, z) := by
  classical
  let evYZ : C(ℤ_[p] × ℤ_[p], ℤ_[p]) →L[ℤ_[p]] ℤ_[p] := ContinuousMap.evalCLM ℤ_[p] (y, z)
  let evX : C(ℤ_[p], C(ℤ_[p] × ℤ_[p], ℤ_[p])) →L[ℤ_[p]] C(ℤ_[p] × ℤ_[p], ℤ_[p]) :=
    ContinuousMap.evalCLM ℤ_[p] x
  have hmap : evYZ ∘L evX ∘L eval₃Aux ℤ_[p] ∘L
      (congrLeft ℤ_[p] ℤ_[p]
        (Homeomorph.prodAssoc (ZMod (p ^ h) × ℕ) (ZMod (p ^ h) × ℕ) (ZMod (p ^ h) × ℕ))
        ).toLinearIsometry.toContinuousLinearMap ∘L
      fstMapCLM (ZMod (p ^ h) × ℕ)
        (addComul (p := p) (h := h) (E := ℤ_[p]) ℤ_[p]) bZp =
      ContinuousMap.evalCLM ℤ_[p] (x + y, z) ∘L eval₂ (p := p) (h := h) (k := h) ℤ_[p] := by
    refine ZeroAtInftyContinuousMap.continuousLinearMap_ext_single_one fun ⟨i, j⟩ ↦ ?_
    have h1 : single (i, j) (1 : ℤ_[p]) =
        prodSMul (single i (1 : ℤ_[p])) (single j (1 : ℤ_[p])) := by simp
    simp only [h1, ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
      LinearIsometryEquiv.coe_toLinearIsometry, fstMapCLM_prodSMul, evX, evYZ,
      ContinuousMap.evalCLM_apply, eval₃Aux_prodAssoc_prodSMul_apply, eval₂_addComul,
      eval₂_prodSMul, smul_eq_mul]
  exact congr($hmap F)

private theorem coassoc_addComul_Zp_scalars (c : AnalyticStage p h E) :
    let cE := addComul (p := p) (h := h) (E := E) ℤ_[p]
    let bE : ∃ C, ∀ f : AnalyticStage p h E, ‖cE f‖ ≤ C * ‖f‖ :=
      ⟨1, fun f ↦ by simp [cE]⟩
    congrLeft ℤ_[p] E (Homeomorph.prodAssoc _ _ _)
      (fstMapCLM (ZMod (p ^ h) × ℕ) cE bE (cE c)) =
      sndMapCLM (ZMod (p ^ h) × ℕ) cE bE (cE c) := by
  classical
  let cZp := addComul (p := p) (h := h) (E := ℤ_[p]) ℤ_[p]
  let bZp : ∃ C, ∀ f : AnalyticStage p h ℤ_[p], ‖cZp f‖ ≤ C * ‖f‖ :=
    ⟨1, fun f ↦ by simp [cZp]⟩
  have hZp : ∀ d : AnalyticStage p h ℤ_[p],
      congrLeft ℤ_[p] ℤ_[p] (Homeomorph.prodAssoc _ _ _)
        (fstMapCLM (ZMod (p ^ h) × ℕ) cZp bZp (cZp d)) =
        sndMapCLM (ZMod (p ^ h) × ℕ) cZp bZp (cZp d) := fun d ↦ by
    apply eval₃Aux_injective ℤ_[p] (IsSMulRegular.of_ne_zero (Nat.cast_ne_zero.mpr hp.out.ne_zero))
    ext x ⟨y, z⟩
    rw [eval₃Aux_prodAssoc_fstMapCLM_addComul_Zp, eval₃Aux_sndMapCLM_addComul_Zp,
      eval₂_addComul, eval₂_addComul, add_assoc]
  let cE := addComul (p := p) (h := h) (E := E) ℤ_[p]
  let bE : ∃ C, ∀ f : AnalyticStage p h E, ‖cE f‖ ≤ C * ‖f‖ :=
    ⟨1, fun f ↦ by simp [cE]⟩
  have hE_Zp :
      (congrLeft ℤ_[p] E
        (Homeomorph.prodAssoc (ZMod (p ^ h) × ℕ) (ZMod (p ^ h) × ℕ) (ZMod (p ^ h) × ℕ))
        ).toLinearIsometry.toContinuousLinearMap ∘L
        fstMapCLM (ZMod (p ^ h) × ℕ) cE bE ∘L cE =
      sndMapCLM (ZMod (p ^ h) × ℕ) cE bE ∘L cE := by
    refine ZeroAtInftyContinuousMap.continuousLinearMap_ext fun idx e ↦ ?_
    let w : ℤ_[p] →L[ℤ_[p]] E := ContinuousLinearMap.smulRight (1 : ℤ_[p] →L[ℤ_[p]] ℤ_[p]) e
    have hw : ∃ C, ∀ r : ℤ_[p], ‖w r‖ ≤ C * ‖r‖ :=
      ⟨‖e‖, fun r ↦ by simpa [w, mul_comm] using norm_smul_le r e⟩
    rw [show single idx e = compLeft w hw (single idx (1 : ℤ_[p])) by simp [w]]
    simp only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
      LinearIsometryEquiv.coe_toLinearIsometry]
    have h1 := congr($(compLeft_addComul (p := p) (h := h) ℤ_[p] w hw) (single idx (1 : ℤ_[p])))
    simp only [ContinuousLinearMap.comp_apply] at h1
    rw [← h1, ← compLeft_fstMapCLM w hw w hw cZp bZp cE bE
        (compLeft_addComul (p := p) (h := h) ℤ_[p] w hw),
      congrLeft_compLeft, hZp,
      compLeft_sndMapCLM w hw w hw cZp bZp cE bE
        (compLeft_addComul (p := p) (h := h) ℤ_[p] w hw)]
  simpa only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
    LinearIsometryEquiv.coe_toLinearIsometry] using congr($hE_Zp c)

/-- **Coassociativity of `addComul`.** Re-expanding `(x + y) + z` via the first factor agrees with
re-expanding `x + (y + z)` via the second factor, for every complete ultrametric `ℤ_p`-module `E`.
-/
theorem coassoc_addComul
    (hC₁ : ∃ C, ∀ f : AnalyticStage p h E, ‖addComul (p := p) (h := h) (E := E) S f‖ ≤ C * ‖f‖)
    (hC₂ : ∃ C, ∀ g : AnalyticStage p h E, ‖addComul (p := p) (h := h) (E := E) S g‖ ≤ C * ‖g‖)
    (c : AnalyticStage p h E) :
    congrLeft S E (Homeomorph.prodAssoc _ _ _)
      (fstMapCLM (ZMod (p ^ h) × ℕ) (addComul (p := p) (h := h) (E := E) S) hC₁ (addComul S c)) =
      sndMapCLM (ZMod (p ^ h) × ℕ) (addComul (p := p) (h := h) (E := E) S) hC₂ (addComul S c) := by
  let cE := addComul (p := p) (h := h) (E := E) ℤ_[p]
  let bE : ∃ C, ∀ f : AnalyticStage p h E, ‖cE f‖ ≤ C * ‖f‖ :=
    ⟨1, fun f ↦ by simp [cE]⟩
  refine ZeroAtInftyContinuousMap.ext fun ⟨i, j, l⟩ ↦ ?_
  have hlhs : congrLeft S E (Homeomorph.prodAssoc _ _ _)
      (fstMapCLM (ZMod (p ^ h) × ℕ)
        (addComul (p := p) (h := h) (E := E) S) hC₁ (addComul S c)) (i, j, l) =
      congrLeft ℤ_[p] E (Homeomorph.prodAssoc _ _ _)
        (fstMapCLM (ZMod (p ^ h) × ℕ) cE bE (cE c)) (i, j, l) := by
    rw [congrLeft_apply, congrLeft_apply]
    rcases (Homeomorph.prodAssoc _ _ _).symm (i, j, l) with ⟨ij, l₀⟩
    simp only [fstMapCLM_apply, cE]
    rw [addComul_eq_of_scalars S ℤ_[p]]
    refine congrArg (fun g ↦ addComul ℤ_[p] g ij) (ZeroAtInftyContinuousMap.ext fun a ↦ ?_)
    rw [addComul_eq_of_scalars S ℤ_[p]]
    simp only [curryEquiv_apply_apply, congrLeft_apply, Homeomorph.prodComm_symm,
      Homeomorph.coe_prodComm, Prod.swap_prod_mk]
  have hrhs : sndMapCLM (ZMod (p ^ h) × ℕ)
      (addComul (p := p) (h := h) (E := E) S) hC₂ (addComul S c) (i, j, l) =
      sndMapCLM (ZMod (p ^ h) × ℕ) cE bE (cE c) (i, j, l) := by
    simp only [sndMapCLM_apply, cE]
    rw [addComul_eq_of_scalars S ℤ_[p]]
    refine congrArg (fun g ↦ addComul ℤ_[p] g (j, l)) (ZeroAtInftyContinuousMap.ext fun a ↦ ?_)
    simp [addComul_eq_of_scalars S ℤ_[p]]
  rw [hlhs, hrhs, coassoc_addComul_Zp_scalars c]

end AddComul

end AnalyticStage

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.IteratedFDeriv.LeibnizJet
public import TauCeti.Analysis.PDE.Parabolic.Holder.Iterated.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import TauCeti.Analysis.Normed.Operator.Holder
import TauCeti.Analysis.PDE.Parabolic.Holder.Iterated.FieldHolder
import TauCeti.Data.Nat.Choose.Basic
import TauCeti.Topology.MetricSpace.Holder

/-!
# Products in the parabolic Hölder spaces of every order

Let `B : F →L[ℝ] G →L[ℝ] H` be a continuous bilinear map and `α ≤ 1`. This file proves that `B`
acts pointwise on the bounded parabolic Hölder spaces `C_{par,b}^{k+α}` of every order `k` on a
slab `E × [a, b]`: for `u ∈ C_{par,b}^{k+α}(F)` and `v ∈ C_{par,b}^{k+α}(G)` the map
`(x, t) ↦ B (u (x, t)) (v (x, t))` lies in `C_{par,b}^{k+α}(H)`, and

`‖B u v‖ ≤ 21 (k + 1)² 2ᵏ ‖B‖ ‖u‖ ‖v‖`

(`ContinuousLinearMap.norm_compParabolicCkHolder₂_le`). With `B` the multiplication of `ℝ`, the
scalar multiplication `ℝ × F → F` or the application of operator-valued coefficients, this is the
product and bounded multiplication estimate of these spaces: it bounds the terms `aⁱʲ ∂ᵢ∂ⱼu`,
`bⁱ ∂ᵢu` and `c u` of a parabolic operator with coefficients in `C_{par,b}^{k+α}` acting on
`C_{par,b}^{k+2+α}`, and the localization of a solution by a smooth space-time cutoff.

The fields of `B u v` are given by the Leibniz rule in time and in space,

`D_t^r D_x^m (B u v) = ∑_{r₁ + r₂ = r} (r choose r₁) Λₘ (J^{r₁} u, J^{r₂} v)`, where
`J^{r'} u = (D_t^{r'} D_x^i u)_{i ≤ m}`

(`ContinuousLinearMap.mixedDerivL_compParabolicCkHolder₂`), where
`Λₘ = ContinuousLinearMap.leibnizJet B E m` is the continuous bilinear map computing the `m`-th
spatial derivative of a product from the jets of its factors. Because `Λₘ` is bilinear and
continuous, the time derivatives of the jets pass through it by the product rule, and the binomial
recursion of `Finset.sum_antidiagonal_choose_succ_nsmul` reassembles them.

The Hölder conditions of `B u v` come from those of the fields of `u` and `v` of every order, not
only the top one. For `α ≤ 1`, every field `D_t^r D_x^m u` of order `2 r + m ≤ k` is parabolically
`α`-Hölder with constant `6 ‖u‖`
(`TauCeti.ParabolicCkHolderSpace.holderWith_mixedDerivL_of_le`): at the top order by definition,
and below it because the field is Lipschitz in space, with the next spatial field as derivative,
and Lipschitz or `(1 + α) / 2`-Hölder in time. Likewise every field of order `2 r + m ≤ k - 1` has
`(1 + α) / 2`-Hölder time slices with constant `3 ‖u‖`
(`TauCeti.ParabolicCkHolderSpace.holderWith_mixedDerivL_slabMk_of_add_one_le`). Products of
bounded Hölder maps through a bilinear map are Hölder, which gives the Hölder field and the Hölder
time slices of `B u v` at the top two orders.

## Main declarations

* `ContinuousLinearMap.compParabolicCkHolder₂`: pointwise application of `B` as a continuous
  bilinear map of the parabolic Hölder spaces of order `k`.
* `ContinuousLinearMap.compParabolicCkHolder₂_apply` and
  `ContinuousLinearMap.mixedDerivL_compParabolicCkHolder₂`: its values and its fields.
* `ContinuousLinearMap.norm_compParabolicCkHolder₂_le`: the operator-norm bound
  `21 (k + 1)² 2ᵏ ‖B‖`.
* `ContinuousLinearMap.norm_compParabolicCkHolder₂_le_card`: the sharper bound `21 N 2ᵏ ‖B‖`, where
  `N ≤ (k + 1)²` is the number of fields `(r, m)` with `2 r + m ≤ k`.

## References

* A. Lunardi, *Linear and nonlinear diffusion problems*, lecture notes, Cortona, 2004, Chapter 3
  (the parabolic Hölder spaces `C^{k+α,(k+α)/2}`).
* N. V. Krylov, *Lectures on elliptic and parabolic equations in Hölder spaces*, AMS, 1996,
  Chapter 8.
-/

public section

noncomputable section

namespace TauCeti

open Set Filter Topology ParabolicSpaceTime
open scoped NNReal ENNReal BoundedContinuousFunction TauCeti.Jet

variable {k : ℕ} {α : ℝ≥0} {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H] {a b : ℝ} {hab : a < b}

namespace ParabolicCkHolderSpace

/-! ### Jets of the fields -/

/-- The spatial jet `(D_t^r D_x^i u (p))_{i ≤ m}` of the `r`-th time derivative at `p`. -/
private def jet (u : ParabolicCkHolderSpace k α E F hab) (r m : ℕ) (p : slab (E := E) a b) :
    (i : Fin (m + 1)) → E [×i]→L[ℝ] F :=
  fun i ↦ mixedDerivL r i u p

private theorem jetInit_jet (u : ParabolicCkHolderSpace k α E F hab) (r m : ℕ)
    (p : slab (E := E) a b) : jetInit ℝ E F m (jet u r (m + 1) p) = jet u r m p := by
  unfold jet
  exact jetInit_fun_coe m fun i ↦ mixedDerivL r i u p

private theorem norm_jet_le (u : ParabolicCkHolderSpace k α E F hab) (r m : ℕ)
    (p : slab (E := E) a b) : ‖jet u r m p‖ ≤ ‖u‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg u)).2 fun i ↦
    ((mixedDerivL r i u).norm_coe_le_norm p).trans (norm_mixedDerivL_le u r i)

private theorem continuous_jet (u : ParabolicCkHolderSpace k α E F hab) (r m : ℕ) :
    Continuous (jet u r m) :=
  continuous_pi fun i ↦ (mixedDerivL r i u).continuous

private theorem holderWith_jet (hα : α ≤ 1) (u : ParabolicCkHolderSpace k α E F hab) {r m : ℕ}
    (h : 2 * r + m ≤ k) : HolderWith (6 * ‖u‖₊) α (jet u r m) := fun p q ↦
  edist_pi_le_iff.2 fun i ↦ holderWith_mixedDerivL_of_le hα u (by omega) p q

private theorem holderWith_jet_slabMk (hα : α ≤ 1) (u : ParabolicCkHolderSpace k α E F hab)
    {r m : ℕ} (h : 2 * r + m + 1 ≤ k) (x : E) :
    HolderWith (3 * ‖u‖₊) ((1 + α) / 2) fun t : Icc a b ↦ jet u r m (slabMk x t) := fun t s ↦
  edist_pi_le_iff.2 fun i ↦ holderWith_mixedDerivL_slabMk_of_add_one_le hα u (by omega) x t s

/-- The jet of the `r`-th time derivative is differentiable in time within `[a, b]`, with the jet
of the `(r + 1)`-th time derivative as derivative. -/
private theorem hasDerivWithinAt_jet (u : ParabolicCkHolderSpace k α E F hab) {r m : ℕ}
    (h : 2 * r + m + 2 ≤ k) (x : E) (t : Icc a b) :
    HasDerivWithinAt (fun s ↦ jet u r m (slabMk x (projIcc a b hab.le s)))
      (jet u (r + 1) m (slabMk x t)) (Icc a b) t :=
  hasDerivWithinAt_pi.2 fun i ↦ by
    have hi := hasDerivWithinAt_mixedDerivL u (r := r) (m := i) (by omega) x t
    rwa [ParabolicC2HolderSpace.timeExtension_def] at hi

/-! ### The fields of the product -/

variable (B : F →L[ℝ] G →L[ℝ] H)

/-- The field `D_t^r D_x^m (B u v)` given by the Leibniz rule. -/
private def productField (u : ParabolicCkHolderSpace k α E F hab)
    (v : ParabolicCkHolderSpace k α E G hab) (r m : ℕ) (p : slab (E := E) a b) : E [×m]→L[ℝ] H :=
  ∑ ij ∈ Finset.antidiagonal r, r.choose ij.1 • B.leibnizJet E m (jet u ij.1 m p) (jet v ij.2 m p)

/-- The product field, with the jets written out. -/
private theorem productField_eq (u : ParabolicCkHolderSpace k α E F hab)
    (v : ParabolicCkHolderSpace k α E G hab) (r m : ℕ) (p : slab (E := E) a b) :
    productField B u v r m p = ∑ ij ∈ Finset.antidiagonal r, r.choose ij.1 •
      B.leibnizJet E m (fun i ↦ mixedDerivL ij.1 i u p) (fun i ↦ mixedDerivL ij.2 i v p) := by
  rw [productField]
  unfold jet
  rfl

private theorem continuous_productField (u : ParabolicCkHolderSpace k α E F hab)
    (v : ParabolicCkHolderSpace k α E G hab) (r m : ℕ) : Continuous (productField B u v r m) :=
  continuous_finsetSum _ fun ij _ ↦
    (((B.leibnizJet E m).continuous₂.comp
      ((continuous_jet u ij.1 m).prodMk (continuous_jet v ij.2 m)))).const_smul _

/-- The Leibniz map of order `m` applied to two jets, bounded by `2ᵐ ‖B‖ ‖u‖ ‖v‖`. -/
private theorem norm_leibnizJet_jet_le (u : ParabolicCkHolderSpace k α E F hab)
    (v : ParabolicCkHolderSpace k α E G hab) (r₁ r₂ m : ℕ) (p : slab (E := E) a b) :
    ‖B.leibnizJet E m (jet u r₁ m p) (jet v r₂ m p)‖ ≤ 2 ^ m * ‖B‖ * ‖u‖ * ‖v‖ :=
  ((B.leibnizJet E m).le_opNorm₂ _ _).trans (mul_le_mul (mul_le_mul (B.norm_leibnizJet_le m)
    (norm_jet_le u r₁ m p) (norm_nonneg _) (by positivity)) (norm_jet_le v r₂ m p)
    (norm_nonneg _) (by positivity))

private theorem norm_productField_le (u : ParabolicCkHolderSpace k α E F hab)
    (v : ParabolicCkHolderSpace k α E G hab) (r m : ℕ) (p : slab (E := E) a b) :
    ‖productField B u v r m p‖ ≤ 2 ^ (r + m) * ‖B‖ * ‖u‖ * ‖v‖ := by
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum fun ij _ ↦ norm_nsmul_le.trans
    (mul_le_mul_of_nonneg_left (norm_leibnizJet_jet_le B u v ij.1 ij.2 m p)
      (Nat.cast_nonneg _))).trans (le_of_eq ?_)
  rw [← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_antidiagonal_choose, pow_add]
  push_cast
  ring

/-- The field `D_t^r D_x^m (B u v)` as a bounded continuous map. -/
private def productFieldBCF (u : ParabolicCkHolderSpace k α E F hab)
    (v : ParabolicCkHolderSpace k α E G hab) (r m : ℕ) : slab (E := E) a b →ᵇ (E [×m]→L[ℝ] H) :=
  BoundedContinuousFunction.ofNormedAddCommGroup (productField B u v r m)
    (continuous_productField B u v r m) (2 ^ (r + m) * ‖B‖ * ‖u‖ * ‖v‖)
    (norm_productField_le B u v r m)

private theorem productFieldBCF_apply (u : ParabolicCkHolderSpace k α E F hab)
    (v : ParabolicCkHolderSpace k α E G hab) (r m : ℕ) (p : slab (E := E) a b) :
    productFieldBCF B u v r m p = productField B u v r m p := by
  simp [productFieldBCF]

/-- **The spatial Leibniz rule for the product fields.** -/
private theorem hasFDerivAt_productField (u : ParabolicCkHolderSpace k α E F hab)
    (v : ParabolicCkHolderSpace k α E G hab) {r m : ℕ} (h : 2 * r + m + 1 ≤ k) (t : Icc a b)
    (x : E) :
    HasFDerivAt (fun y ↦ productField B u v r m (slabMk y t))
      (productField B u v r (m + 1) (slabMk x t)).curryLeft x := by
  have hterm : ∀ ij ∈ Finset.antidiagonal r, HasFDerivAt
      (fun y ↦ r.choose ij.1 • B.leibnizJet E m (jet u ij.1 m (slabMk y t))
        (jet v ij.2 m (slabMk y t)))
      (r.choose ij.1 • (B.leibnizJet E (m + 1) (jet u ij.1 (m + 1) (slabMk x t))
        (jet v ij.2 (m + 1) (slabMk x t))).curryLeft) x := fun ij hij ↦ by
    have hr := Finset.mem_antidiagonal.1 hij
    have hD := B.hasFDerivAt_leibnizJet (n := m) (x := x)
      (f := fun y ↦ jet u ij.1 (m + 1) (slabMk y t))
      (g := fun y ↦ jet v ij.2 (m + 1) (slabMk y t))
      (fun i ↦ hasFDerivAt_mixedDerivL u (r := ij.1) (m := i) (by omega) t x)
      (fun i ↦ hasFDerivAt_mixedDerivL v (r := ij.2) (m := i) (by omega) t x)
    simp only [jetInit_jet] at hD
    exact hD.const_smul _
  have hsum := HasFDerivAt.fun_sum hterm
  refine hsum.congr_fderiv ?_
  ext h v
  simp [productField, -ContinuousLinearMap.curryLeft_leibnizJet_succ]

/-- **The time Leibniz rule for the product fields.** -/
private theorem hasDerivWithinAt_productField (u : ParabolicCkHolderSpace k α E F hab)
    (v : ParabolicCkHolderSpace k α E G hab) {r m : ℕ} (h : 2 * r + m + 2 ≤ k) (x : E)
    (t : Icc a b) :
    HasDerivWithinAt (ParabolicC2HolderSpace.timeExtension hab.le (productFieldBCF B u v r m) x)
      (productField B u v (r + 1) m (slabMk x t)) (Icc a b) t := by
  have hterm : ∀ ij ∈ Finset.antidiagonal r, HasDerivWithinAt
      (fun s ↦ r.choose ij.1 • B.leibnizJet E m (jet u ij.1 m (slabMk x (projIcc a b hab.le s)))
        (jet v ij.2 m (slabMk x (projIcc a b hab.le s))))
      (r.choose ij.1 • (B.leibnizJet E m (jet u ij.1 m (slabMk x t))
        (jet v (ij.2 + 1) m (slabMk x t)) + B.leibnizJet E m (jet u (ij.1 + 1) m (slabMk x t))
          (jet v ij.2 m (slabMk x t)))) (Icc a b) t := fun ij hij ↦ by
    have hr := Finset.mem_antidiagonal.1 hij
    have hu := hasDerivWithinAt_jet u (r := ij.1) (m := m) (by omega) x t
    have hv := hasDerivWithinAt_jet v (r := ij.2) (m := m) (by omega) x t
    have hB := (B.leibnizJet E m).hasDerivWithinAt_of_bilinear hu hv
    rw [projIcc_val] at hB
    exact hB.const_smul _
  have hsum := HasDerivWithinAt.fun_sum hterm
  have hfun : ParabolicC2HolderSpace.timeExtension hab.le (productFieldBCF B u v r m) x =
      fun s ↦ ∑ ij ∈ Finset.antidiagonal r, r.choose ij.1 • B.leibnizJet E m
        (jet u ij.1 m (slabMk x (projIcc a b hab.le s)))
        (jet v ij.2 m (slabMk x (projIcc a b hab.le s))) := by
    funext s
    simp only [ParabolicC2HolderSpace.timeExtension_def, productFieldBCF_apply, productField]
  rw [hfun]
  refine hsum.congr_deriv ?_
  unfold productField
  rw [Finset.sum_antidiagonal_choose_succ_nsmul
    (fun i j ↦ B.leibnizJet E m (jet u i m (slabMk x t)) (jet v j m (slabMk x t))) r]
  simp only [smul_add, Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun ij hij ↦ ?_
  rw [Nat.choose_symm_of_eq_add (Finset.mem_antidiagonal.1 hij).symm]

/-- A binomially weighted sum of Leibniz maps of jets is Hölder: if the jets `f i` and `g j` are
`γ`-Hölder with constants `Cf` and `Cg` and bounded by `Mf` and `Mg`, then
`x ↦ ∑_{i + j = r} (r choose i) Λₘ (f i x, g j x)` is `γ`-Hölder with constant
`2ʳ 2ᵐ ‖B‖ (Mf Cg + Mg Cf)`. -/
private theorem holderWith_sum_leibnizJet {X : Type*} [PseudoMetricSpace X] {γ Cf Cg Mf Mg : ℝ≥0}
    (r m : ℕ) (f : ℕ → X → (i : Fin (m + 1)) → E [×i]→L[ℝ] F)
    (g : ℕ → X → (i : Fin (m + 1)) → E [×i]→L[ℝ] G) (hf : ∀ i ≤ r, HolderWith Cf γ (f i))
    (hg : ∀ j ≤ r, HolderWith Cg γ (g j)) (hfM : ∀ i x, ‖f i x‖ ≤ Mf)
    (hgM : ∀ j x, ‖g j x‖ ≤ Mg) :
    HolderWith (2 ^ r * (2 ^ m * ‖B‖₊ * (Mf * Cg + Mg * Cf))) γ
      fun x ↦ ∑ ij ∈ Finset.antidiagonal r,
        r.choose ij.1 • B.leibnizJet E m (f ij.1 x) (g ij.2 x) := by
  have hK : ∀ ij ∈ Finset.antidiagonal r, HolderWith (2 ^ m * ‖B‖₊ * (Mf * Cg + Mg * Cf)) γ
      fun x ↦ B.leibnizJet E m (f ij.1 x) (g ij.2 x) := fun ij hij ↦ by
    have hr := Finset.mem_antidiagonal.1 hij
    have hP := (B.leibnizJet E m).holderWith_comp₂ (hf ij.1 (by omega)) (hg ij.2 (by omega))
      (hfM ij.1) (hgM ij.2)
    refine fun x y ↦ (hP x y).trans ?_
    gcongr
    rw [← NNReal.coe_le_coe]
    push_cast
    exact B.norm_leibnizJet_le m
  have hsum := HolderWith.sum_nsmul (Finset.antidiagonal r) (fun ij ↦ r.choose ij.1) hK
  rwa [← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_antidiagonal_choose, Nat.cast_pow,
    Nat.cast_ofNat] at hsum

/-- The Hölder constant of the product fields of top order. -/
private theorem holderWith_productField (hα : α ≤ 1) (u : ParabolicCkHolderSpace k α E F hab)
    (v : ParabolicCkHolderSpace k α E G hab) {r m : ℕ} (h : 2 * r + m ≤ k) :
    HolderWith (2 ^ r * (2 ^ m * ‖B‖₊ * (‖u‖₊ * (6 * ‖v‖₊) + ‖v‖₊ * (6 * ‖u‖₊)))) α
      (productField B u v r m) := by
  unfold productField
  exact holderWith_sum_leibnizJet B r m (fun i ↦ jet u i m) (fun j ↦ jet v j m)
    (fun i _ ↦ holderWith_jet hα u (by omega)) (fun j _ ↦ holderWith_jet hα v (by omega))
    (fun i ↦ norm_jet_le u i m) (fun j ↦ norm_jet_le v j m)

/-- The Hölder constant of the time slices of the product fields one order below the top. -/
private theorem holderWith_productField_slabMk (hα : α ≤ 1)
    (u : ParabolicCkHolderSpace k α E F hab) (v : ParabolicCkHolderSpace k α E G hab)
    {r m : ℕ} (h : 2 * r + m + 1 ≤ k) (x : E) :
    HolderWith (2 ^ r * (2 ^ m * ‖B‖₊ * (‖u‖₊ * (3 * ‖v‖₊) + ‖v‖₊ * (3 * ‖u‖₊)))) ((1 + α) / 2)
      fun t : Icc a b ↦ productField B u v r m (slabMk x t) := by
  unfold productField
  exact holderWith_sum_leibnizJet B r m (fun i t ↦ jet u i m (slabMk x t))
    (fun j t ↦ jet v j m (slabMk x t)) (fun i _ ↦ holderWith_jet_slabMk hα u (by omega) x)
    (fun j _ ↦ holderWith_jet_slabMk hα v (by omega) x) (fun i _ ↦ norm_jet_le u i m _)
    (fun j _ ↦ norm_jet_le v j m _)

private theorem coe_productFieldBCF (u : ParabolicCkHolderSpace k α E F hab)
    (v : ParabolicCkHolderSpace k α E G hab) (r m : ℕ) :
    ⇑(productFieldBCF B u v r m) = productField B u v r m :=
  funext (productFieldBCF_apply B u v r m)

/-- The norm of a product field is at most `2ᵏ ‖B‖ ‖u‖ ‖v‖` at every order `2 r + m ≤ k`. -/
private theorem norm_productFieldBCF_le (u : ParabolicCkHolderSpace k α E F hab)
    (v : ParabolicCkHolderSpace k α E G hab) {r m : ℕ} (h : 2 * r + m ≤ k) :
    ‖productFieldBCF B u v r m‖ ≤ 2 ^ k * ‖B‖ * ‖u‖ * ‖v‖ :=
  (BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ (by positivity) _).trans (by
    gcongr
    · norm_num
    · omega)

/-- The pointwise product `B u v`, before bundling. -/
private def compAux (hα : α ≤ 1) (u : ParabolicCkHolderSpace k α E F hab)
    (v : ParabolicCkHolderSpace k α E G hab) : ParabolicCkHolderSpace k α E H hab :=
  mk (productFieldBCF B u v)
    (fun _ _ h t x ↦ by
      simpa only [productFieldBCF_apply] using hasFDerivAt_productField B u v h t x)
    (fun _ _ h x t ↦ by
      rw [productFieldBCF_apply]
      exact hasDerivWithinAt_productField B u v h x t)
    (fun _ _ h ↦ ⟨_, fun x ↦ by
      simpa only [productFieldBCF_apply] using holderWith_productField_slabMk B hα u v h.le x⟩)
    (fun _ _ h ↦ by
      rw [coe_productFieldBCF]
      exact (holderWith_productField B hα u v h.le).memHolder)

private theorem mixedDerivL_compAux (hα : α ≤ 1) (u : ParabolicCkHolderSpace k α E F hab)
    (v : ParabolicCkHolderSpace k α E G hab) {r m : ℕ} (h : 2 * r + m ≤ k) :
    mixedDerivL r m (compAux B hα u v) = productFieldBCF B u v r m :=
  mixedDerivL_mk _ _ _ _ h

private theorem compAux_apply (hα : α ≤ 1) (u : ParabolicCkHolderSpace k α E F hab)
    (v : ParabolicCkHolderSpace k α E G hab) (p : slab (E := E) a b) :
    compAux B hα u v p = B (u p) (v p) := by
  rw [compAux, mk_apply, productFieldBCF_apply, productField]
  simp [jet]

/-- The real value of the Hölder constants of the product fields at order `2 r + m ≤ k` is at most
`2 c 2ᵏ ‖B‖ ‖u‖ ‖v‖`. -/
private theorem coe_two_pow_mul_le (u : ParabolicCkHolderSpace k α E F hab)
    (v : ParabolicCkHolderSpace k α E G hab) {r m : ℕ} (h : 2 * r + m ≤ k) (c : ℝ≥0) :
    ((2 ^ r * (2 ^ m * ‖B‖₊ * (‖u‖₊ * (c * ‖v‖₊) + ‖v‖₊ * (c * ‖u‖₊))) : ℝ≥0) : ℝ) ≤
      2 * c * (2 ^ k * ‖B‖ * ‖u‖ * ‖v‖) := by
  have h2 : (2 : ℝ) ^ r * 2 ^ m ≤ 2 ^ k := by
    rw [← pow_add]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have := mul_le_mul_of_nonneg_right h2 (by positivity : (0 : ℝ) ≤ 2 * c * ‖B‖ * ‖u‖ * ‖v‖)
  push_cast
  nlinarith

/-- The time slices of the product one order below the top have norm at most
`7 · 2ᵏ ‖B‖ ‖u‖ ‖v‖`. -/
private theorem norm_timeSliceL_compAux_le (hα : α ≤ 1) (u : ParabolicCkHolderSpace k α E F hab)
    (v : ParabolicCkHolderSpace k α E G hab) {r m : ℕ} (h : 2 * r + m ≤ k) :
    ‖timeSliceL r m (compAux B hα u v)‖ ≤ 7 * (2 ^ k * ‖B‖ * ‖u‖ * ‖v‖) := by
  by_cases h1 : 2 * r + m + 1 = k
  · refine (norm_timeSliceL_le_of_holderWith _ h1
      (C := 2 ^ r * (2 ^ m * ‖B‖₊ * (‖u‖₊ * (3 * ‖v‖₊) + ‖v‖₊ * (3 * ‖u‖₊)))) fun x ↦ ?_).trans ?_
    · rw [mixedDerivL_compAux B hα u v h]
      simpa only [productFieldBCF_apply] using holderWith_productField_slabMk B hα u v h1.le x
    · have h6 := coe_two_pow_mul_le B u v h 3
      rw [mixedDerivL_compAux B hα u v h]
      push_cast at h6 ⊢
      linarith [norm_productFieldBCF_le B u v h]
  · rw [timeSliceL_of_ne h1, zero_apply, norm_zero]
    positivity

/-- The Hölder field of the product at the top order has norm at most
`13 · 2ᵏ ‖B‖ ‖u‖ ‖v‖`. -/
private theorem norm_mixedDerivHolderL_compAux_le (hα : α ≤ 1)
    (u : ParabolicCkHolderSpace k α E F hab) (v : ParabolicCkHolderSpace k α E G hab) {r m : ℕ}
    (h : 2 * r + m ≤ k) :
    ‖mixedDerivHolderL r m (compAux B hα u v)‖ ≤ 13 * (2 ^ k * ‖B‖ * ‖u‖ * ‖v‖) := by
  by_cases h0 : 2 * r + m = k
  · have hcoe : ⇑(mixedDerivHolderL r m (compAux B hα u v)) = productField B u v r m := by
      funext q
      rw [mixedDerivHolderL_apply _ h0, mixedDerivL_compAux B hα u v h, productFieldBCF_apply]
    refine (HolderSpace.norm_le_of_norm_le_of_holderWith (M := 2 ^ k * ‖B‖ * ‖u‖ * ‖v‖)
      (by positivity) (fun q ↦ ?_)
      (hcoe ▸ holderWith_productField B hα u v h)).trans ?_
    · rw [hcoe, ← productFieldBCF_apply]
      exact ((productFieldBCF B u v r m).norm_coe_le_norm q).trans
        (norm_productFieldBCF_le B u v h)
    · have h12 := coe_two_pow_mul_le B u v h 6
      push_cast at h12 ⊢
      linarith
  · rw [mixedDerivHolderL_of_ne h0, zero_apply, norm_zero]
    positivity

private theorem norm_compAux_le_card (hα : α ≤ 1) (u : ParabolicCkHolderSpace k α E F hab)
    (v : ParabolicCkHolderSpace k α E G hab) :
    ‖compAux B hα u v‖ ≤ 21 * (parabolicDerivPairs k).card * 2 ^ k * ‖B‖ * ‖u‖ * ‖v‖ := by
  set M := 2 ^ k * ‖B‖ * ‖u‖ * ‖v‖ with hM
  -- Each pair `(r, m)` contributes at most `M + 7 M + 13 M`.
  have hterm : ∀ q ∈ parabolicDerivPairs k, ‖mixedDerivL q.1 q.2 (compAux B hα u v)‖ +
      (‖timeSliceL q.1 q.2 (compAux B hα u v)‖ + ‖mixedDerivHolderL q.1 q.2 (compAux B hα u v)‖) ≤
        21 * M := by
    rintro ⟨r, m⟩ hq
    have hq : 2 * r + m ≤ k := mem_parabolicDerivPairs.1 hq
    have hfield := norm_productFieldBCF_le B u v hq
    rw [← mixedDerivL_compAux B hα u v hq] at hfield
    linarith [norm_timeSliceL_compAux_le B hα u v hq, norm_mixedDerivHolderL_compAux_le B hα u v hq]
  rw [norm_eq]
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul, hM]
  exact le_of_eq (by ring)

private theorem norm_compAux_le (hα : α ≤ 1) (u : ParabolicCkHolderSpace k α E F hab)
    (v : ParabolicCkHolderSpace k α E G hab) :
    ‖compAux B hα u v‖ ≤ 21 * (k + 1) ^ 2 * 2 ^ k * ‖B‖ * ‖u‖ * ‖v‖ := by
  refine (norm_compAux_le_card B hα u v).trans ?_
  gcongr
  exact_mod_cast card_parabolicDerivPairs_le k

end ParabolicCkHolderSpace

end TauCeti

namespace ContinuousLinearMap

open TauCeti TauCeti.ParabolicCkHolderSpace TauCeti.ParabolicSpaceTime
open scoped NNReal

variable {k : ℕ} {α : ℝ≥0} {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H] {a b : ℝ} {hab : a < b}
  (B : F →L[ℝ] G →L[ℝ] H) (hα : α ≤ 1)

/-- For `α ≤ 1`, pointwise application `(u, v) ↦ B u v` of a continuous bilinear map, as a
continuous bilinear map of the bounded parabolic Hölder spaces `C_{par,b}^{k+α}` of order `k` on a
slab. -/
def compParabolicCkHolder₂ :
    ParabolicCkHolderSpace k α E F hab →L[ℝ] ParabolicCkHolderSpace k α E G hab →L[ℝ]
      ParabolicCkHolderSpace k α E H hab :=
  (LinearMap.mk₂ ℝ (compAux B hα)
    (fun _ _ _ ↦ ParabolicCkHolderSpace.ext fun _ ↦ by simp [compAux_apply])
    (fun _ _ _ ↦ ParabolicCkHolderSpace.ext fun _ ↦ by simp [compAux_apply])
    (fun _ _ _ ↦ ParabolicCkHolderSpace.ext fun _ ↦ by simp [compAux_apply])
    (fun _ _ _ ↦ ParabolicCkHolderSpace.ext fun _ ↦ by simp [compAux_apply])).mkContinuous₂
    (21 * (k + 1) ^ 2 * 2 ^ k * ‖B‖) (norm_compAux_le B hα)

/- `LinearMap.mkContinuous₂_apply` and `LinearMap.mk₂_apply` do not fire here, as for the order-two
space `TauCeti.ParabolicC2HolderSpace`, whose definition as a submodule is not exposed either; the
equation is closed by `rfl` directly. -/
private theorem compParabolicCkHolder₂_eq (u : ParabolicCkHolderSpace k α E F hab)
    (v : ParabolicCkHolderSpace k α E G hab) :
    B.compParabolicCkHolder₂ hα u v = compAux B hα u v := (rfl)

@[simp]
theorem compParabolicCkHolder₂_apply (u : ParabolicCkHolderSpace k α E F hab)
    (v : ParabolicCkHolderSpace k α E G hab) (p : slab (E := E) a b) :
    B.compParabolicCkHolder₂ hα u v p = B (u p) (v p) := by
  rw [compParabolicCkHolder₂_eq, compAux_apply]

/-- **The Leibniz rule for the fields.** For `2 r + m ≤ k`, the field `D_t^r D_x^m (B u v)` is
`∑_{r₁ + r₂ = r} (r choose r₁) Λₘ (J^{r₁} u, J^{r₂} v)`, where `Λₘ = B.leibnizJet E m` and
`J^{r'} u = (D_t^{r'} D_x^i u)_{i ≤ m}` is the spatial jet of the `r'`-th time derivative. -/
theorem mixedDerivL_compParabolicCkHolder₂ (u : ParabolicCkHolderSpace k α E F hab)
    (v : ParabolicCkHolderSpace k α E G hab) {r m : ℕ} (h : 2 * r + m ≤ k)
    (p : slab (E := E) a b) :
    mixedDerivL r m (B.compParabolicCkHolder₂ hα u v) p =
      ∑ ij ∈ Finset.antidiagonal r, r.choose ij.1 • B.leibnizJet E m
        (fun i ↦ mixedDerivL ij.1 i u p) (fun i ↦ mixedDerivL ij.2 i v p) := by
  rw [compParabolicCkHolder₂_eq, mixedDerivL_compAux B hα u v h, productFieldBCF_apply,
    productField_eq]

/-- **The product estimate.** Pointwise application of `B` to parabolic Hölder maps of order `k`
has operator norm at most `21 (k + 1)² 2ᵏ ‖B‖`, uniformly over the exponent, the spaces and the
slab. -/
theorem norm_compParabolicCkHolder₂_le :
    ‖B.compParabolicCkHolder₂ (k := k) (E := E) (hab := hab) hα‖ ≤
      21 * (k + 1) ^ 2 * 2 ^ k * ‖B‖ :=
  opNorm_le_bound₂ _ (by positivity) fun u v ↦ by
    rw [compParabolicCkHolder₂_eq]
    exact norm_compAux_le B hα u v

/-- **The product estimate, counting the fields.** Pointwise application of `B` to parabolic
Hölder maps of order `k` has operator norm at most `21 N 2ᵏ ‖B‖`, where `N` is the number of pairs
`(r, m)` with `2 r + m ≤ k`; since `N ≤ (k + 1)²`, this sharpens
`ContinuousLinearMap.norm_compParabolicCkHolder₂_le`. -/
theorem norm_compParabolicCkHolder₂_le_card :
    ‖B.compParabolicCkHolder₂ (k := k) (E := E) (hab := hab) hα‖ ≤
      21 * (parabolicDerivPairs k).card * 2 ^ k * ‖B‖ :=
  opNorm_le_bound₂ _ (by positivity) fun u v ↦ by
    rw [compParabolicCkHolder₂_eq]
    exact norm_compAux_le_card B hα u v

/-- The norm of `B u v` is at most `21 (k + 1)² 2ᵏ ‖B‖ ‖u‖ ‖v‖`. -/
theorem norm_compParabolicCkHolder₂_apply_le (u : ParabolicCkHolderSpace k α E F hab)
    (v : ParabolicCkHolderSpace k α E G hab) :
    ‖B.compParabolicCkHolder₂ hα u v‖ ≤ 21 * (k + 1) ^ 2 * 2 ^ k * ‖B‖ * ‖u‖ * ‖v‖ := by
  rw [compParabolicCkHolder₂_eq]
  exact norm_compAux_le B hα u v

/-- The pointwise product of two scalar parabolic Hölder maps of order `k` has norm at most
`21 (k + 1)² 2ᵏ ‖u‖ ‖v‖`: `ContinuousLinearMap.norm_compParabolicCkHolder₂_apply_le` for the
multiplication of `ℝ`, whose operator norm is at most `1`. -/
theorem norm_mul_compParabolicCkHolder₂_apply_le (u v : ParabolicCkHolderSpace k α E ℝ hab) :
    ‖(ContinuousLinearMap.mul ℝ ℝ).compParabolicCkHolder₂ hα u v‖ ≤
      21 * (k + 1) ^ 2 * 2 ^ k * (‖u‖ * ‖v‖) := by
  refine (norm_compParabolicCkHolder₂_apply_le _ hα u v).trans ?_
  have h1 : ‖ContinuousLinearMap.mul ℝ ℝ‖ ≤ 1 := opNorm_mul_le ℝ ℝ
  calc _ ≤ 21 * (k + 1) ^ 2 * 2 ^ k * 1 * ‖u‖ * ‖v‖ := by gcongr
    _ = _ := by ring

end ContinuousLinearMap

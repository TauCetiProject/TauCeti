/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Holder.Iterated
public import TauCeti.Analysis.Holder.OpenSet
import TauCeti.Analysis.Holder.Leibniz
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-!
# Products in higher-order Hölder spaces

A continuous bilinear map acts pointwise on `CkHolderSpace`. For `α ≤ 1`, the lifted map
`ContinuousLinearMap.compCkHolder₂` is continuous bilinear, with operator norm at most
`(k + 7) * 2^k * ‖B‖`. In particular this supplies bounded multiplication by coefficients,
scalar multiplication, and application of operator-valued coefficient fields in every order.
The constant is not sharp; it is independent of the exponent, spaces and functions.

On the spaces `CkHolderSpaceOn k α Ω` of an open set `Ω`, the same construction needs the
derivative fields below the top order to be `α`-Hölder on `Ω`, and this depends on the geometry of
`Ω`: on a slit annulus in the plane the angle function `θ` lies in `C^{1,α}`, since its gradient
is the restriction of a smooth field on the full annulus, but `θ²` does not, since the derivative
`2 θ ∇θ` jumps across the slit. Given constants `C` and `D` such that every derivative field
through order `k` of every `f ∈ C^{k,α}(Ω, E)` is `α`-Hölder with constant `C ‖f‖`, and of every
`g ∈ C^{k,α}(Ω, F)` with constant `D ‖g‖`, the lifted map
`ContinuousLinearMap.compCkHolderOn₂OfHolderOnWith` is continuous bilinear with operator norm at
most `(k + 1 + C + D) 2^k ‖B‖`. On a convex open set the mean value inequality gives `C = D = 3`,
hence the order-`k` Leibniz estimate
`‖B (f, g)‖_{C^{k,α}(Ω)} ≤ (k + 7) 2^k ‖B‖ ‖f‖_{C^{k,α}(Ω)} ‖g‖_{C^{k,α}(Ω)}`
(`ContinuousLinearMap.compCkHolderOn₂`), which gives bounded multiplication by coefficients in
`C^{k,α}(Ω)`. The case of a bounded Lipschitz domain is
`ContinuousLinearMap.compCkHolderOn₂OfIsLipschitzDomain`.

The norm is the existing sum of the supremum norms of all derivative fields and the Hölder
seminorm of the top field. We use Mathlib's bilinear Leibniz bound for the supremum terms and
`ContinuousLinearMap.holderWith_iteratedFDeriv_of_tsupport_subset_right`, respectively
`ContinuousLinearMap.holderOnWith_iteratedFDeriv_comp₂`, for the top seminorm.

## References

D. Gilbarg and N. Trudinger, *Elliptic Partial Differential Equations of Second Order*, §4.1.
-/

public section
noncomputable section

open scoped NNReal BoundedContinuousFunction
open TauCeti TopologicalSpace

namespace ContinuousLinearMap

variable {X E F G : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] {k : ℕ} {α : ℝ≥0}

/-- The binomial sum in the bilinear Leibniz bound at an order `j ≤ k` is at most
`2 ^ k * ‖B‖ * M * N` when the derivative norms of the two factors are bounded by `M` and `N`
through order `k`. -/
private theorem norm_mul_sum_choose_le (B : E →L[ℝ] F →L[ℝ] G) {j : ℕ} (hj : j ≤ k)
    {a b : ℕ → ℝ} {M N : ℝ} (ha0 : ∀ i, 0 ≤ a i) (hb0 : ∀ i, 0 ≤ b i)
    (ha : ∀ i ≤ k, a i ≤ M) (hb : ∀ i ≤ k, b i ≤ N) :
    ‖B‖ * ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * a i * b (j - i) ≤
      2 ^ k * ‖B‖ * M * N := by
  have hM : 0 ≤ M := (ha0 0).trans (ha 0 k.zero_le)
  have hN : 0 ≤ N := (hb0 0).trans (hb 0 k.zero_le)
  calc
    _ ≤ ‖B‖ * ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * M * N := by
      gcongr with i hi
      · exact hb0 _
      · exact ha i (by have := Finset.mem_range.mp hi; omega)
      · exact hb _ ((Nat.sub_le j i).trans hj)
    _ = 2 ^ j * ‖B‖ * M * N := by
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      have hsum : (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ)) = 2 ^ j := by
        exact_mod_cast Nat.sum_range_choose j
      rw [hsum]
      ring
    _ ≤ _ := by gcongr; norm_num

private theorem norm_iteratedFDeriv_ckHolderBilinear_le (B : E →L[ℝ] F →L[ℝ] G)
    (f : CkHolderSpace k α X E) (g : CkHolderSpace k α X F) {j : ℕ} (hj : j ≤ k)
    (x : X) :
    ‖iteratedFDeriv ℝ j (fun y ↦ B (f y) (g y)) x‖ ≤ 2 ^ k * ‖B‖ * ‖f‖ * ‖g‖ := by
  refine (B.norm_iteratedFDeriv_le_of_bilinear f.contDiff g.contDiff x
    (by exact_mod_cast hj)).trans ?_
  exact norm_mul_sum_choose_le B hj (a := fun i ↦ ‖iteratedFDeriv ℝ i f x‖)
    (b := fun i ↦ ‖iteratedFDeriv ℝ i g x‖) (fun _ ↦ norm_nonneg _) (fun _ ↦ norm_nonneg _)
    (fun i hi ↦ f.norm_iteratedFDeriv_apply_le hi x)
    (fun i hi ↦ g.norm_iteratedFDeriv_apply_le hi x)

private theorem holderWith_iteratedFDeriv_ckHolderBilinear (B : E →L[ℝ] F →L[ℝ] G)
    (hα : α ≤ 1) (f : CkHolderSpace k α X E) (g : CkHolderSpace k α X F) :
    HolderWith (6 * 2 ^ k * ‖B‖₊ * ‖f‖₊ * ‖g‖₊) α
      (iteratedFDeriv ℝ k (fun x ↦ B (f x) (g x))) := by
  have h := B.holderWith_iteratedFDeriv_of_tsupport_subset_right f.contDiff.contDiffOn
    g.contDiff isOpen_univ (Set.subset_univ _)
    (M := ‖f‖₊) (N := ‖g‖₊) (H := 3 * ‖f‖₊) (K := 3 * ‖g‖₊)
    (fun j hj x _ ↦ f.norm_iteratedFDeriv_apply_le hj x)
    (fun j hj x ↦ g.norm_iteratedFDeriv_apply_le hj x)
    (fun j hj ↦ (f.holderWith_iteratedFDeriv_of_le hα hj).holderOnWith Set.univ)
    (fun j hj ↦ g.holderWith_iteratedFDeriv_of_le hα hj)
  convert h using 1; ring

private def ckHolderBilinear (B : E →L[ℝ] F →L[ℝ] G) (hα : α ≤ 1)
    (f : CkHolderSpace k α X E) (g : CkHolderSpace k α X F) : CkHolderSpace k α X G :=
  CkHolderSpace.ofContDiff (fun x ↦ B (f x) (g x))
    (B.isBoundedBilinearMap.contDiff.comp (f.contDiff.prodMk g.contDiff))
    (fun _ hj ↦ ⟨2 ^ k * ‖B‖ * ‖f‖ * ‖g‖,
      norm_iteratedFDeriv_ckHolderBilinear_le B f g hj⟩)
    (holderWith_iteratedFDeriv_ckHolderBilinear B hα f g).memHolder

@[simp]
private theorem coe_ckHolderBilinear (B : E →L[ℝ] F →L[ℝ] G) (hα : α ≤ 1)
    (f : CkHolderSpace k α X E) (g : CkHolderSpace k α X F) :
    ⇑(ckHolderBilinear B hα f g) = fun x ↦ B (f x) (g x) := by
  simp [ckHolderBilinear]

private theorem norm_ckHolderBilinear_le (B : E →L[ℝ] F →L[ℝ] G) (hα : α ≤ 1)
    (f : CkHolderSpace k α X E) (g : CkHolderSpace k α X F) :
    ‖ckHolderBilinear B hα f g‖ ≤ (k + 7) * 2 ^ k * ‖B‖ * ‖f‖ * ‖g‖ := by
  have hfield (i : Fin (k + 1)) : ‖(ckHolderBilinear B hα f g).iteratedFDeriv i‖ ≤
      2 ^ k * ‖B‖ * ‖f‖ * ‖g‖ := by
    refine (BoundedContinuousFunction.norm_le (by positivity)).2 fun x ↦ ?_
    rw [← CkHolderSpace.iteratedFDeriv_eq, coe_ckHolderBilinear]
    exact norm_iteratedFDeriv_ckHolderBilinear_le B f g (by omega) x
  have htop : (nnHolderNorm α (iteratedFDeriv ℝ k (ckHolderBilinear B hα f g)) : ℝ) ≤
      6 * 2 ^ k * ‖B‖ * ‖f‖ * ‖g‖ := by
    rw [coe_ckHolderBilinear]
    exact_mod_cast (holderWith_iteratedFDeriv_ckHolderBilinear B hα f g).nnholderNorm_le
  rw [CkHolderSpace.norm_eq]
  calc
    _ ≤ (∑ _ : Fin (k + 1), 2 ^ k * ‖B‖ * ‖f‖ * ‖g‖) +
        6 * 2 ^ k * ‖B‖ * ‖f‖ * ‖g‖ :=
      add_le_add (Finset.sum_le_sum fun i _ ↦ hfield i) htop
    _ = _ := by simp; ring

private def ckHolderBilinearLinear (B : E →L[ℝ] F →L[ℝ] G) (hα : α ≤ 1) :
    CkHolderSpace k α X E →ₗ[ℝ] CkHolderSpace k α X F →ₗ[ℝ] CkHolderSpace k α X G :=
  LinearMap.mk₂ ℝ (ckHolderBilinear B hα)
    (fun f₁ f₂ g ↦ CkHolderSpace.ext fun x ↦ by simp)
    (fun c f g ↦ CkHolderSpace.ext fun x ↦ by simp)
    (fun f g₁ g₂ ↦ CkHolderSpace.ext fun x ↦ by simp)
    (fun c f g ↦ CkHolderSpace.ext fun x ↦ by simp)

/-- Pointwise application of a continuous bilinear map to bounded `C^{k,α}` functions.
Fixing the first argument gives bounded multiplication by a coefficient field. -/
def compCkHolder₂ (B : E →L[ℝ] F →L[ℝ] G) (hα : α ≤ 1) :
    CkHolderSpace k α X E →L[ℝ] CkHolderSpace k α X F →L[ℝ] CkHolderSpace k α X G :=
  (ckHolderBilinearLinear B hα).mkContinuous₂ ((k + 7) * 2 ^ k * ‖B‖)
    (norm_ckHolderBilinear_le B hα)

/-- The lifted bilinear operation is pointwise the original one. -/
@[simp]
theorem compCkHolder₂_apply (B : E →L[ℝ] F →L[ℝ] G) (hα : α ≤ 1)
    (f : CkHolderSpace k α X E) (g : CkHolderSpace k α X F) (x : X) :
    B.compCkHolder₂ hα f g x = B (f x) (g x) := by
  simp [compCkHolder₂, ckHolderBilinearLinear]

/-- The lifted bilinear map has an operator norm bound depending only on the order and `‖B‖`.
This estimate uses the supremum-plus-Hölder sum norm, not an equivalent renorming. -/
theorem norm_compCkHolder₂_le (B : E →L[ℝ] F →L[ℝ] G) (hα : α ≤ 1) :
    ‖B.compCkHolder₂ (k := k) (X := X) hα‖ ≤ (k + 7) * 2 ^ k * ‖B‖ :=
  LinearMap.mkContinuous₂_norm_le _ (by positivity) _

/-- The order-`k` Hölder product estimate, with an explicit order-dependent constant. -/
theorem norm_compCkHolder₂_apply_le (B : E →L[ℝ] F →L[ℝ] G) (hα : α ≤ 1)
    (f : CkHolderSpace k α X E) (g : CkHolderSpace k α X F) :
    ‖B.compCkHolder₂ hα f g‖ ≤ (k + 7) * 2 ^ k * ‖B‖ * ‖f‖ * ‖g‖ :=
  (B.compCkHolder₂ hα |>.le_opNorm₂ f g).trans (by
    gcongr
    exact B.norm_compCkHolder₂_le hα)

section OpenSet

variable {Ω : Opens X}

/-- The bilinear Leibniz bound for the derivative fields on `Ω` of the pointwise product of two
maps agreeing on `Ω` with elements of `C^{k,α}(Ω)`. -/
private theorem norm_iteratedFDeriv_comp₂_le_of_ckHolderSpaceOn (B : E →L[ℝ] F →L[ℝ] G)
    (f : CkHolderSpaceOn k α Ω E) (g : CkHolderSpaceOn k α Ω F) {f' : X → E} {g' : X → F}
    (hf : ∀ x : Ω, f' x = f x) (hg : ∀ x : Ω, g' x = g x) {j : ℕ} (hj : j ≤ k) (x : Ω) :
    ‖iteratedFDeriv ℝ j (fun y ↦ B (f' y) (g' y)) x‖ ≤ 2 ^ k * ‖B‖ * ‖f‖ * ‖g‖ := by
  have hΩ := Ω.isOpen
  rw [← iteratedFDerivWithin_of_isOpen j hΩ x.property]
  refine (B.norm_iteratedFDerivWithin_le_of_bilinear (f.contDiffOn hf) (g.contDiffOn hg)
    hΩ.uniqueDiffOn x.property (by exact_mod_cast hj)).trans ?_
  exact norm_mul_sum_choose_le B hj (a := fun i ↦ ‖iteratedFDerivWithin ℝ i f' Ω x‖)
    (b := fun i ↦ ‖iteratedFDerivWithin ℝ i g' Ω x‖) (fun _ ↦ norm_nonneg _) (fun _ ↦ norm_nonneg _)
    (fun i hi ↦ by
      rw [iteratedFDerivWithin_of_isOpen i hΩ x.property]
      exact f.norm_iteratedFDeriv_apply_le hf hi x)
    (fun i hi ↦ by
      rw [iteratedFDerivWithin_of_isOpen i hΩ x.property]
      exact g.norm_iteratedFDeriv_apply_le hg hi x)

variable {C D : ℝ≥0}

/-- The Hölder bound on `Ω` for the top derivative of the pointwise product of the extensions by
zero of `f ∈ C^{k,α}(Ω)` and `g ∈ C^{k,α}(Ω)`, when their derivative fields through order `k` are
`α`-Hölder on `Ω` with constants `C ‖f‖` and `D ‖g‖`. -/
private theorem holderOnWith_iteratedFDeriv_comp₂_extend (B : E →L[ℝ] F →L[ℝ] G)
    (f : CkHolderSpaceOn k α Ω E) (g : CkHolderSpaceOn k α Ω F)
    (hf : ∀ j ≤ k, HolderOnWith (C * ‖f‖₊) α (iteratedFDeriv ℝ j f.extend) Ω)
    (hg : ∀ j ≤ k, HolderOnWith (D * ‖g‖₊) α (iteratedFDeriv ℝ j g.extend) Ω) :
    HolderOnWith ((C + D) * 2 ^ k * ‖B‖₊ * ‖f‖₊ * ‖g‖₊) α
      (iteratedFDeriv ℝ k (fun x ↦ B (f.extend x) (g.extend x))) Ω := by
  have h := B.holderOnWith_iteratedFDeriv_comp₂ f.contDiffOn_extend g.contDiffOn_extend Ω.isOpen
    (M := ‖f‖₊) (N := ‖g‖₊)
    (fun j hj x hx ↦ f.norm_iteratedFDeriv_apply_le f.extend_apply hj ⟨x, hx⟩)
    (fun j hj x hx ↦ g.norm_iteratedFDeriv_apply_le g.extend_apply hj ⟨x, hx⟩) hf hg
  convert h using 1; ring

/-- The pointwise product of two elements of `C^{k,α}(Ω)`, as an element of `C^{k,α}(Ω)`, computed
from their extensions by zero, which agree with them on `Ω`. -/
private def ckHolderOnBilinear (B : E →L[ℝ] F →L[ℝ] G)
    (hC : ∀ (f : CkHolderSpaceOn k α Ω E) {j : ℕ}, j ≤ k →
      HolderOnWith (C * ‖f‖₊) α (iteratedFDeriv ℝ j f.extend) Ω)
    (hD : ∀ (g : CkHolderSpaceOn k α Ω F) {j : ℕ}, j ≤ k →
      HolderOnWith (D * ‖g‖₊) α (iteratedFDeriv ℝ j g.extend) Ω)
    (f : CkHolderSpaceOn k α Ω E) (g : CkHolderSpaceOn k α Ω F) : CkHolderSpaceOn k α Ω G :=
  CkHolderSpaceOn.ofContDiffOn (fun x ↦ B (f.extend x) (g.extend x))
    (B.isBoundedBilinearMap.contDiff.comp_contDiffOn
      (f.contDiffOn_extend.prodMk g.contDiffOn_extend))
    (fun _ hj ↦ ⟨2 ^ k * ‖B‖ * ‖f‖ * ‖g‖, norm_iteratedFDeriv_comp₂_le_of_ckHolderSpaceOn B f g
      f.extend_apply g.extend_apply hj⟩)
    (HolderWith.memHolder fun x y ↦ holderOnWith_iteratedFDeriv_comp₂_extend B f g
      (fun _ hj ↦ hC f hj) (fun _ hj ↦ hD g hj) x x.property y y.property)

@[simp]
private theorem ckHolderOnBilinear_apply (B : E →L[ℝ] F →L[ℝ] G)
    (hC : ∀ (f : CkHolderSpaceOn k α Ω E) {j : ℕ}, j ≤ k →
      HolderOnWith (C * ‖f‖₊) α (iteratedFDeriv ℝ j f.extend) Ω)
    (hD : ∀ (g : CkHolderSpaceOn k α Ω F) {j : ℕ}, j ≤ k →
      HolderOnWith (D * ‖g‖₊) α (iteratedFDeriv ℝ j g.extend) Ω)
    (f : CkHolderSpaceOn k α Ω E) (g : CkHolderSpaceOn k α Ω F) (x : Ω) :
    ckHolderOnBilinear B hC hD f g x = B (f x) (g x) := by
  rw [ckHolderOnBilinear, CkHolderSpaceOn.ofContDiffOn_apply, f.extend_apply, g.extend_apply]

private theorem norm_ckHolderOnBilinear_le (B : E →L[ℝ] F →L[ℝ] G)
    (hC : ∀ (f : CkHolderSpaceOn k α Ω E) {j : ℕ}, j ≤ k →
      HolderOnWith (C * ‖f‖₊) α (iteratedFDeriv ℝ j f.extend) Ω)
    (hD : ∀ (g : CkHolderSpaceOn k α Ω F) {j : ℕ}, j ≤ k →
      HolderOnWith (D * ‖g‖₊) α (iteratedFDeriv ℝ j g.extend) Ω)
    (f : CkHolderSpaceOn k α Ω E) (g : CkHolderSpaceOn k α Ω F) :
    ‖ckHolderOnBilinear B hC hD f g‖ ≤ (k + 1 + C + D) * 2 ^ k * ‖B‖ * ‖f‖ * ‖g‖ := by
  refine (CkHolderSpaceOn.norm_le_sum_add_of_norm_iteratedFDeriv_le_of_holderWith
    (M := fun _ ↦ 2 ^ k * ‖B‖ * ‖f‖ * ‖g‖) (fun _ ↦ by positivity) (fun i x ↦ ?_)
    (K := (C + D) * 2 ^ k * ‖B‖₊ * ‖f‖₊ * ‖g‖₊) (fun x y ↦ ?_)).trans_eq ?_
  · rw [ckHolderOnBilinear, CkHolderSpaceOn.iteratedFDeriv_ofContDiffOn]
    exact norm_iteratedFDeriv_comp₂_le_of_ckHolderSpaceOn B f g f.extend_apply g.extend_apply
      (by omega) x
  · rw [ckHolderOnBilinear, CkHolderSpaceOn.iteratedFDeriv_ofContDiffOn,
      CkHolderSpaceOn.iteratedFDeriv_ofContDiffOn, Fin.val_last]
    exact holderOnWith_iteratedFDeriv_comp₂_extend B f g (fun _ hj ↦ hC f hj)
      (fun _ hj ↦ hD g hj) x x.property y y.property
  · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring

private def ckHolderOnBilinearLinear (B : E →L[ℝ] F →L[ℝ] G)
    (hC : ∀ (f : CkHolderSpaceOn k α Ω E) {j : ℕ}, j ≤ k →
      HolderOnWith (C * ‖f‖₊) α (iteratedFDeriv ℝ j f.extend) Ω)
    (hD : ∀ (g : CkHolderSpaceOn k α Ω F) {j : ℕ}, j ≤ k →
      HolderOnWith (D * ‖g‖₊) α (iteratedFDeriv ℝ j g.extend) Ω) :
    CkHolderSpaceOn k α Ω E →ₗ[ℝ] CkHolderSpaceOn k α Ω F →ₗ[ℝ] CkHolderSpaceOn k α Ω G :=
  LinearMap.mk₂ ℝ (ckHolderOnBilinear B hC hD)
    (fun f₁ f₂ g ↦ CkHolderSpaceOn.ext fun x ↦ by simp)
    (fun c f g ↦ CkHolderSpaceOn.ext fun x ↦ by simp)
    (fun f g₁ g₂ ↦ CkHolderSpaceOn.ext fun x ↦ by simp)
    (fun c f g ↦ CkHolderSpaceOn.ext fun x ↦ by simp)

/-- Pointwise application of a continuous bilinear map to `C^{k,α}` functions on an open set `Ω`,
given constants `C` and `D` such that every derivative field through order `k` of (the extension
by zero of) every `f ∈ C^{k,α}(Ω, E)` is `α`-Hölder on `Ω` with constant `C ‖f‖`, and of every
`g ∈ C^{k,α}(Ω, F)` with constant `D ‖g‖`. Such bounds depend on the geometry of `Ω`:
`ContinuousLinearMap.compCkHolderOn₂` supplies them on convex open sets. -/
def compCkHolderOn₂OfHolderOnWith (B : E →L[ℝ] F →L[ℝ] G) (C D : ℝ≥0)
    (hC : ∀ (f : CkHolderSpaceOn k α Ω E) {j : ℕ}, j ≤ k →
      HolderOnWith (C * ‖f‖₊) α (iteratedFDeriv ℝ j f.extend) Ω)
    (hD : ∀ (g : CkHolderSpaceOn k α Ω F) {j : ℕ}, j ≤ k →
      HolderOnWith (D * ‖g‖₊) α (iteratedFDeriv ℝ j g.extend) Ω) :
    CkHolderSpaceOn k α Ω E →L[ℝ] CkHolderSpaceOn k α Ω F →L[ℝ] CkHolderSpaceOn k α Ω G :=
  (ckHolderOnBilinearLinear B hC hD).mkContinuous₂ ((k + 1 + C + D) * 2 ^ k * ‖B‖)
    (norm_ckHolderOnBilinear_le B hC hD)

/-- The lifted bilinear operation built from Hölder bounds is pointwise the original one. -/
@[simp]
theorem compCkHolderOn₂OfHolderOnWith_apply (B : E →L[ℝ] F →L[ℝ] G) (C D : ℝ≥0)
    (hC : ∀ (f : CkHolderSpaceOn k α Ω E) {j : ℕ}, j ≤ k →
      HolderOnWith (C * ‖f‖₊) α (iteratedFDeriv ℝ j f.extend) Ω)
    (hD : ∀ (g : CkHolderSpaceOn k α Ω F) {j : ℕ}, j ≤ k →
      HolderOnWith (D * ‖g‖₊) α (iteratedFDeriv ℝ j g.extend) Ω)
    (f : CkHolderSpaceOn k α Ω E) (g : CkHolderSpaceOn k α Ω F) (x : Ω) :
    B.compCkHolderOn₂OfHolderOnWith C D hC hD f g x = B (f x) (g x) := by
  simp [compCkHolderOn₂OfHolderOnWith, ckHolderOnBilinearLinear]

/-- The lifted bilinear map built from Hölder bounds with constants `C ‖f‖` and `D ‖g‖` has
operator norm at most `(k + 1 + C + D) 2^k ‖B‖`. -/
theorem norm_compCkHolderOn₂OfHolderOnWith_le (B : E →L[ℝ] F →L[ℝ] G) (C D : ℝ≥0)
    (hC : ∀ (f : CkHolderSpaceOn k α Ω E) {j : ℕ}, j ≤ k →
      HolderOnWith (C * ‖f‖₊) α (iteratedFDeriv ℝ j f.extend) Ω)
    (hD : ∀ (g : CkHolderSpaceOn k α Ω F) {j : ℕ}, j ≤ k →
      HolderOnWith (D * ‖g‖₊) α (iteratedFDeriv ℝ j g.extend) Ω) :
    ‖B.compCkHolderOn₂OfHolderOnWith C D hC hD‖ ≤ (k + 1 + C + D) * 2 ^ k * ‖B‖ :=
  LinearMap.mkContinuous₂_norm_le _ (by positivity) _

/-- Pointwise application of a continuous bilinear map to `C^{k,α}` functions on a convex open
set `Ω`. Fixing the first argument gives bounded multiplication by a coefficient field in
`C^{k,α}(Ω)`. -/
def compCkHolderOn₂ (B : E →L[ℝ] F →L[ℝ] G) (hΩ : Convex ℝ (Ω : Set X)) (hα : α ≤ 1) :
    CkHolderSpaceOn k α Ω E →L[ℝ] CkHolderSpaceOn k α Ω F →L[ℝ] CkHolderSpaceOn k α Ω G :=
  B.compCkHolderOn₂OfHolderOnWith 3 3
    (fun f _ hj ↦ f.holderOnWith_iteratedFDeriv_of_le f.extend_apply hΩ hα hj)
    (fun g _ hj ↦ g.holderOnWith_iteratedFDeriv_of_le g.extend_apply hΩ hα hj)

/-- The lifted bilinear operation on `C^{k,α}(Ω)` is pointwise the original one. -/
@[simp]
theorem compCkHolderOn₂_apply (B : E →L[ℝ] F →L[ℝ] G) (hΩ : Convex ℝ (Ω : Set X))
    (hα : α ≤ 1) (f : CkHolderSpaceOn k α Ω E) (g : CkHolderSpaceOn k α Ω F) (x : Ω) :
    B.compCkHolderOn₂ hΩ hα f g x = B (f x) (g x) :=
  compCkHolderOn₂OfHolderOnWith_apply _ _ _ _ _ f g x

/-- The lifted bilinear map on `C^{k,α}(Ω)` has an operator norm bound depending only on the order
and `‖B‖`. -/
theorem norm_compCkHolderOn₂_le (B : E →L[ℝ] F →L[ℝ] G) (hΩ : Convex ℝ (Ω : Set X))
    (hα : α ≤ 1) : ‖B.compCkHolderOn₂ (k := k) hΩ hα‖ ≤ (k + 7) * 2 ^ k * ‖B‖ :=
  (norm_compCkHolderOn₂OfHolderOnWith_le _ _ _ _ _).trans_eq (by push_cast; ring)

/-- The order-`k` Leibniz estimate in `C^{k,α}(Ω)` for a convex open set `Ω`, with an explicit
order-dependent constant. -/
theorem norm_compCkHolderOn₂_apply_le (B : E →L[ℝ] F →L[ℝ] G) (hΩ : Convex ℝ (Ω : Set X))
    (hα : α ≤ 1) (f : CkHolderSpaceOn k α Ω E) (g : CkHolderSpaceOn k α Ω F) :
    ‖B.compCkHolderOn₂ hΩ hα f g‖ ≤ (k + 7) * 2 ^ k * ‖B‖ * ‖f‖ * ‖g‖ :=
  (B.compCkHolderOn₂ hΩ hα |>.le_opNorm₂ f g).trans (by
    gcongr
    exact B.norm_compCkHolderOn₂_le hΩ hα)

end OpenSet

end ContinuousLinearMap

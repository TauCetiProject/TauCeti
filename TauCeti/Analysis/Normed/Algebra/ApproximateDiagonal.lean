/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ApproximateUnit
public import TauCeti.Analysis.Normed.Module.CohenFactorization.Basic
public import TauCeti.Analysis.Normed.Module.TensorProduct.Completion

/-!
# Approximate diagonals of Banach algebras

Let `A` be a possibly nonunital normed algebra over `𝕜`. The completed projective tensor product
`A ⊗̂π A` is a Banach `A`-bimodule for the *outer* actions `c · (x ⊗ y) = (c * x) ⊗ y` and
`(x ⊗ y) · c = x ⊗ (y * c)`, written `mulLeft 𝕜 A c` and `mulRight 𝕜 A c`. They are bounded
bilinear maps `A →L[𝕜] A ⊗̂π A →L[𝕜] A ⊗̂π A`, the interface used for Banach bimodules in
`TauCeti.Analysis.Normed.Algebra.HochschildCohomology.Coboundary`. When `A` is complete,
multiplication induces the bounded bimodule map `Δ : A ⊗̂π A →L[𝕜] A`, `x ⊗ y ↦ x * y`, here
`CompletedProjectiveTensor.mul' 𝕜 A` after its algebraic counterpart `LinearMap.mul'`. It is a
contraction, and by Cohen's factorization theorem it is surjective as soon as `A` has a bounded
left approximate identity.

An *approximate diagonal* of `A` is a proper filter `l` on `A ⊗̂π A` along which
`a · m - m · a → 0` and `a * Δ m → a` for every `a`; it is *bounded by `C`* when `‖m‖ ≤ C`
eventually along `l`. This is B. E. Johnson's notion: a Banach algebra is amenable exactly when it
has a bounded approximate diagonal. Recording approximate diagonals as filters, rather than nets,
follows the convention for approximate identities in
`TauCeti.Analysis.Normed.Ring.ApproximateUnit`.

The image of an approximate diagonal under `Δ` is a two-sided approximate identity, bounded by
`C` when the diagonal is: `a * Δ m → a` is assumed, and
`Δ m * a = Δ (m · a) = a * Δ m - Δ (a · m - m · a) → a`. In particular, a Banach algebra with a
bounded approximate diagonal has a bounded approximate identity.

## Main definitions

* `TauCeti.CompletedProjectiveTensor.mulLeft` and `TauCeti.CompletedProjectiveTensor.mulRight`:
  the outer bimodule actions of `A` on `A ⊗̂π A`.
* `TauCeti.CompletedProjectiveTensor.mul'`: the multiplication map `Δ : A ⊗̂π A →L[𝕜] A`.
* `TauCeti.IsApproximateDiagonal`: approximate diagonals.

## Main results

* `TauCeti.CompletedProjectiveTensor.mulLeft_mul_apply`,
  `TauCeti.CompletedProjectiveTensor.mulRight_mul_apply` and
  `TauCeti.CompletedProjectiveTensor.mulLeft_mulRight_apply_comm`: the bimodule laws.
* `TauCeti.CompletedProjectiveTensor.mul'_mulLeft_apply` and
  `TauCeti.CompletedProjectiveTensor.mul'_mulRight_apply`: `Δ` is a bimodule map.
* `TauCeti.CompletedProjectiveTensor.mul'_surjective`: `Δ` is surjective when `A` has a bounded
  left approximate identity.
* `TauCeti.IsApproximateDiagonal.isApproximateUnit_map`: `Δ` maps an approximate diagonal to an
  approximate identity.
* `TauCeti.IsApproximateDiagonal.exists_isApproximateUnit`: a Banach algebra with an approximate
  diagonal bounded by `C` has a two-sided approximate identity bounded by `C`.

## References

* B. E. Johnson, *Approximate diagonals and cohomology of certain annihilator Banach algebras*,
  Amer. J. Math. 94 (1972), 685–698.
* V. Runde, *Lectures on Amenability*, Springer, 2002, §2.2.
* H. G. Dales, *Banach Algebras and Automatic Continuity*, §2.9.
-/

public section

open Filter Topology UniformSpace

open scoped TensorProduct

namespace TauCeti

namespace CompletedProjectiveTensor

section Actions

variable (𝕜 A : Type*) [NontriviallyNormedField 𝕜] [NonUnitalSeminormedRing A] [NormedSpace 𝕜 A]
  [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A]

/-- The outer left action of `A` on `A ⊗̂π A`, `c · (x ⊗ y) = (c * x) ⊗ y`, as a bounded bilinear
map. -/
noncomputable def mulLeft : A →L[𝕜] CompletedProjectiveTensor 𝕜 A A →L[𝕜]
    CompletedProjectiveTensor 𝕜 A A :=
  LinearMap.mkContinuous
    { toFun c := mapL (ContinuousLinearMap.mul 𝕜 A c) (.id 𝕜 A)
      map_add' c c' := by rw [map_add, mapL_add_left]
      map_smul' k c := by rw [map_smul, mapL_smul_left, RingHom.id_apply] }
    1 fun c ↦ (norm_mapL_le _ _).trans <| by
      simpa using mul_le_mul (ContinuousLinearMap.opNorm_mul_apply_le 𝕜 A c)
        ContinuousLinearMap.norm_id_le (norm_nonneg _) (norm_nonneg c)

/-- The outer right action of `A` on `A ⊗̂π A`, `(x ⊗ y) · c = x ⊗ (y * c)`, as a bounded bilinear
map. -/
noncomputable def mulRight : A →L[𝕜] CompletedProjectiveTensor 𝕜 A A →L[𝕜]
    CompletedProjectiveTensor 𝕜 A A :=
  LinearMap.mkContinuous
    { toFun c := mapL (.id 𝕜 A) ((ContinuousLinearMap.mul 𝕜 A).flip c)
      map_add' c c' := by rw [map_add, mapL_add_right]
      map_smul' k c := by rw [map_smul, mapL_smul_right, RingHom.id_apply] }
    1 fun c ↦ (norm_mapL_le _ _).trans <| by
      have : ‖(ContinuousLinearMap.mul 𝕜 A).flip c‖ ≤ ‖c‖ := by
        simpa using (ContinuousLinearMap.mul 𝕜 A).flip.le_of_opNorm_le
          ((ContinuousLinearMap.opNorm_flip _).trans_le (ContinuousLinearMap.opNorm_mul_le 𝕜 A)) c
      simpa using mul_le_mul ContinuousLinearMap.norm_id_le this (norm_nonneg _) zero_le_one

variable {𝕜 A}

/-- The outer left action of `c` is the operator induced by left multiplication by `c` on the
first factor. -/
theorem mulLeft_apply (c : A) :
    mulLeft 𝕜 A c = mapL (ContinuousLinearMap.mul 𝕜 A c) (.id 𝕜 A) :=
  (rfl)

/-- The outer right action of `c` is the operator induced by right multiplication by `c` on the
second factor. -/
theorem mulRight_apply (c : A) :
    mulRight 𝕜 A c = mapL (.id 𝕜 A) ((ContinuousLinearMap.mul 𝕜 A).flip c) :=
  (rfl)

/-- The outer left action on pure tensors: `c · (x ⊗ y) = (c * x) ⊗ y`. -/
@[simp]
theorem mulLeft_apply_coe_tmul (c x y : A) :
    mulLeft 𝕜 A c (⟨x ⊗ₜ y⟩ : ProjectiveTensor 𝕜 A A) =
      ((⟨(c * x) ⊗ₜ y⟩ : ProjectiveTensor 𝕜 A A) : CompletedProjectiveTensor 𝕜 A A) := by
  simp [mulLeft_apply]

/-- The outer right action on pure tensors: `(x ⊗ y) · c = x ⊗ (y * c)`. -/
@[simp]
theorem mulRight_apply_coe_tmul (c x y : A) :
    mulRight 𝕜 A c (⟨x ⊗ₜ y⟩ : ProjectiveTensor 𝕜 A A) =
      ((⟨x ⊗ₜ (y * c)⟩ : ProjectiveTensor 𝕜 A A) : CompletedProjectiveTensor 𝕜 A A) := by
  simp [mulRight_apply]

/-- The outer left action is a left action: `(a * b) · m = a · (b · m)`. -/
theorem mulLeft_mul_apply (a b : A) (m : CompletedProjectiveTensor 𝕜 A A) :
    mulLeft 𝕜 A (a * b) m = mulLeft 𝕜 A a (mulLeft 𝕜 A b m) := by
  have : mulLeft 𝕜 A (a * b) = mulLeft 𝕜 A a ∘L mulLeft 𝕜 A b := by
    ext; simp [mul_assoc]
  exact congr($this m)

/-- The outer right action is a right action: `m · (a * b) = (m · a) · b`. -/
theorem mulRight_mul_apply (a b : A) (m : CompletedProjectiveTensor 𝕜 A A) :
    mulRight 𝕜 A (a * b) m = mulRight 𝕜 A b (mulRight 𝕜 A a m) := by
  have : mulRight 𝕜 A (a * b) = mulRight 𝕜 A b ∘L mulRight 𝕜 A a := by
    ext; simp [mul_assoc]
  exact congr($this m)

/-- The outer left and right actions commute: `a · (m · b) = (a · m) · b`. -/
theorem mulLeft_mulRight_apply_comm (a b : A) (m : CompletedProjectiveTensor 𝕜 A A) :
    mulLeft 𝕜 A a (mulRight 𝕜 A b m) = mulRight 𝕜 A b (mulLeft 𝕜 A a m) := by
  have : mulLeft 𝕜 A a ∘L mulRight 𝕜 A b = mulRight 𝕜 A b ∘L mulLeft 𝕜 A a := by
    ext; simp
  exact congr($this m)

end Actions

section Multiplication

variable (𝕜 A : Type*) [NontriviallyNormedField 𝕜] [NonUnitalNormedRing A] [NormedSpace 𝕜 A]
  [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] [CompleteSpace A]

/-- The multiplication map `Δ : A ⊗̂π A →L[𝕜] A`, `x ⊗ y ↦ x * y`, of a Banach algebra: the
bounded counterpart of `LinearMap.mul'`. -/
noncomputable def mul' : CompletedProjectiveTensor 𝕜 A A →L[𝕜] A :=
  liftIsometry 𝕜 A A A (ContinuousLinearMap.mul 𝕜 A)

variable {𝕜 A}

/-- The multiplication map on pure tensors: `Δ (x ⊗ y) = x * y`. -/
@[simp]
theorem mul'_coe_tmul (x y : A) : mul' 𝕜 A (⟨x ⊗ₜ y⟩ : ProjectiveTensor 𝕜 A A) = x * y := by
  simp [mul', ProjectiveTensor.liftIsometry_apply_tmul]

/-- The multiplication map is a contraction. -/
theorem norm_mul'_le : ‖mul' 𝕜 A‖ ≤ 1 := by
  rw [mul', LinearIsometryEquiv.norm_map]
  exact ContinuousLinearMap.opNorm_mul_le 𝕜 A

/-- The multiplication map does not increase norms: `‖Δ m‖ ≤ ‖m‖`. -/
theorem norm_mul'_apply_le (m : CompletedProjectiveTensor 𝕜 A A) : ‖mul' 𝕜 A m‖ ≤ ‖m‖ := by
  simpa using (mul' 𝕜 A).le_of_opNorm_le norm_mul'_le m

/-- The multiplication map intertwines the outer left action with left multiplication:
`Δ (c · m) = c * Δ m`. -/
@[simp]
theorem mul'_mulLeft_apply (c : A) (m : CompletedProjectiveTensor 𝕜 A A) :
    mul' 𝕜 A (mulLeft 𝕜 A c m) = c * mul' 𝕜 A m := by
  have : mul' 𝕜 A ∘L mulLeft 𝕜 A c = ContinuousLinearMap.mul 𝕜 A c ∘L mul' 𝕜 A := by
    ext; simp [mul_assoc]
  exact congr($this m)

/-- The multiplication map intertwines the outer right action with right multiplication:
`Δ (m · c) = Δ m * c`. -/
@[simp]
theorem mul'_mulRight_apply (c : A) (m : CompletedProjectiveTensor 𝕜 A A) :
    mul' 𝕜 A (mulRight 𝕜 A c m) = mul' 𝕜 A m * c := by
  have : mul' 𝕜 A ∘L mulRight 𝕜 A c = (ContinuousLinearMap.mul 𝕜 A).flip c ∘L mul' 𝕜 A := by
    ext; simp [mul_assoc]
  exact congr($this m)

end Multiplication

/-- By Cohen's factorization theorem, the multiplication map `Δ : A ⊗̂π A → A` of a Banach algebra
with a bounded left approximate identity is surjective: every element is even the image of a pure
tensor. -/
theorem mul'_surjective {𝕜 A : Type*} [RCLike 𝕜] [NonUnitalNormedRing A] [NormedSpace 𝕜 A]
    [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] [CompleteSpace A] {l : Filter A} [l.NeBot]
    {C : ℝ} (hC : ∀ᶠ e in l, ‖e‖ ≤ C) (hl : ∀ a, Tendsto (· * a) l (𝓝 a)) :
    Function.Surjective (mul' 𝕜 A) := fun x ↦
  let ⟨a, y, _, h⟩ := exists_mul_eq_of_tendsto_mul_right 𝕜 hC hl x
  ⟨(⟨a ⊗ₜ y⟩ : ProjectiveTensor 𝕜 A A), by simpa using h⟩

end CompletedProjectiveTensor

open CompletedProjectiveTensor

section ApproximateDiagonal

variable (𝕜 : Type*) {A : Type*} [NontriviallyNormedField 𝕜] [NonUnitalNormedRing A]
  [NormedSpace 𝕜 A] [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] [CompleteSpace A]

/-- A filter `l` on `A ⊗̂π A` is an *approximate diagonal* of the Banach algebra `A` if it is
proper and, along `l`, `a · m - m · a → 0` and `a * Δ m → a` for every `a`, where `Δ` is the
multiplication map. It is *bounded by `C`* when `‖m‖ ≤ C` eventually along `l`. -/
structure IsApproximateDiagonal (l : Filter (CompletedProjectiveTensor 𝕜 A A)) : Prop where
  /-- The outer actions of every `a` asymptotically agree along `l`. -/
  tendsto_mulLeft_sub_mulRight (a : A) :
    Tendsto (fun m ↦ mulLeft 𝕜 A a m - mulRight 𝕜 A a m) l (𝓝 0)
  /-- The image of `l` under the multiplication map is a right approximate identity. -/
  tendsto_mul_mul' (a : A) : Tendsto (fun m ↦ a * mul' 𝕜 A m) l (𝓝 a)
  /-- The filter is not `⊥`. -/
  protected [neBot : l.NeBot]

variable {𝕜} {l : Filter (CompletedProjectiveTensor 𝕜 A A)}

namespace IsApproximateDiagonal

/-- If `l` is an approximate diagonal and `⊥ < l' ≤ l`, then `l'` is also an approximate
diagonal. -/
theorem mono (h : IsApproximateDiagonal 𝕜 l) {l' : Filter (CompletedProjectiveTensor 𝕜 A A)}
    (hle : l' ≤ l) [l'.NeBot] : IsApproximateDiagonal 𝕜 l' where
  tendsto_mulLeft_sub_mulRight a := (h.tendsto_mulLeft_sub_mulRight a).mono_left hle
  tendsto_mul_mul' a := (h.tendsto_mul_mul' a).mono_left hle

/-- The multiplication map sends an approximate diagonal to a two-sided approximate identity. -/
theorem isApproximateUnit_map (h : IsApproximateDiagonal 𝕜 l) :
    (l.map (mul' 𝕜 A)).IsApproximateUnit where
  tendsto_mul_left a := tendsto_map'_iff.2 (h.tendsto_mul_mul' a)
  tendsto_mul_right a := by
    have hΔ := ((mul' 𝕜 A).continuous.tendsto 0).comp (h.tendsto_mulLeft_sub_mulRight a)
    rw [map_zero] at hΔ
    refine tendsto_map'_iff.2 ?_
    simpa [Function.comp_def] using (h.tendsto_mul_mul' a).sub hΔ
  neBot := have := h.neBot; inferInstance

/-- A Banach algebra with an approximate diagonal bounded by `C` has a two-sided approximate
identity bounded by `C`: the image of the approximate diagonal under the multiplication map. -/
theorem exists_isApproximateUnit (h : IsApproximateDiagonal 𝕜 l) {C : ℝ}
    (hC : ∀ᶠ m in l, ‖m‖ ≤ C) :
    ∃ l' : Filter A, l'.IsApproximateUnit ∧ ∀ᶠ e in l', ‖e‖ ≤ C :=
  ⟨_, h.isApproximateUnit_map, eventually_map.2 <| hC.mono fun m hm ↦
    (norm_mul'_apply_le m).trans hm⟩

end IsApproximateDiagonal

end ApproximateDiagonal

section Unital

variable {𝕜 A : Type*} [NontriviallyNormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A]
  [CompleteSpace A]

/-- In a unital Banach algebra, a *diagonal*, that is an element `m` of `A ⊗̂π A` commuting with
`A` for the outer actions and with `Δ m = 1`, is a constant approximate diagonal. -/
theorem isApproximateDiagonal_pure {m : CompletedProjectiveTensor 𝕜 A A}
    (hm : ∀ a, mulLeft 𝕜 A a m = mulRight 𝕜 A a m) (h1 : mul' 𝕜 A m = 1) :
    IsApproximateDiagonal 𝕜 (pure m) where
  tendsto_mulLeft_sub_mulRight a := by
    simpa [hm] using tendsto_pure_nhds (fun m ↦ mulLeft 𝕜 A a m - mulRight 𝕜 A a m) m
  tendsto_mul_mul' a := by simpa [h1] using tendsto_pure_nhds (fun m ↦ a * mul' 𝕜 A m) m

variable (𝕜) in
/-- The base field, as a Banach algebra over itself, has the diagonal `1 ⊗ 1`. -/
theorem isApproximateDiagonal_pure_one_tmul_one [CompleteSpace 𝕜] :
    IsApproximateDiagonal 𝕜
      (pure ((⟨1 ⊗ₜ 1⟩ : ProjectiveTensor 𝕜 𝕜 𝕜) : CompletedProjectiveTensor 𝕜 𝕜 𝕜)) :=
  isApproximateDiagonal_pure (fun a ↦ by
    rw [mulLeft_apply_coe_tmul, mulRight_apply_coe_tmul, ← smul_eq_mul a 1,
      TensorProduct.smul_tmul, smul_eq_mul, mul_one, one_mul]) (by simp)

end Unital

end TauCeti

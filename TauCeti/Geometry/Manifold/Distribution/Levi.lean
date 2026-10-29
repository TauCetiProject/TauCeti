/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Distribution.VectorBundle
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import TauCeti.Geometry.Manifold.VectorField.LieBracket
import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# The Levi form of a distribution

Let `D` be a `C¹` distribution on a manifold `M`. Its **Levi form** at a point `x` is the bilinear
map

`L_D x : D x × D x → T_x M ⧸ D x`, `L_D x (V x, W x) = -[V, W] x mod D x`,

where `V` and `W` are any vector fields that are differentiable at `x` and tangent to `D` near `x`.
The class of `[V, W] x` modulo `D x` depends only on the values `V x` and `W x`: in a local frame
of `D`, a vector field tangent to `D` and vanishing at `x` has coefficients vanishing at `x`, and
the product rule for the Lie bracket then puts its bracket with any vector field in `D x`. The
Levi form is antisymmetric, and it vanishes identically exactly when `D` is involutive. A
hyperplane field is a contact structure when its Levi form is nondegenerate. The sign is the one
for which, when `D = ker α`, the isomorphism `T_x M ⧸ D x ≃ 𝕜` induced by `α` carries the Levi form
to the restriction of `dα` to `D`.

## Main definitions

* `TauCeti.distributionLeviForm D x`: the Levi form of `D` at `x`, computed from a `C¹` local frame
  near `x`, and zero when there is none.

## Main results

* `TauCeti.IsDistributionFrameOn.mlieBracket_mem_of_apply_eq_zero`: the Lie bracket at `x` of a
  vector field tangent to `D` near `x` and vanishing at `x` with any vector field lies in `D x`.
* `TauCeti.IsDistributionFrameOn.mlieBracket_sub_mlieBracket_mem`: modulo `D x`, the Lie bracket at
  `x` of two vector fields tangent to `D` depends only on their values at `x`.
* `TauCeti.IsDistributionFrameOn.distributionLeviForm_apply` and
  `TauCeti.distributionLeviForm_apply`: the Levi form is the negated Lie bracket modulo `D`, for
  any extensions, given a `C¹` local frame near `x` or a global `C¹` distribution structure.
* `TauCeti.IsDistributionFrameOn.distributionLeviForm_apply_eq_zero_iff` and
  `TauCeti.distributionLeviForm_apply_eq_zero_iff`: the Levi form vanishes on two values exactly
  when the Lie bracket of their extensions is tangent to `D`.
* `TauCeti.distributionLeviForm_swap`: the Levi form is antisymmetric.
* `TauCeti.isInvolutiveDistribution_iff_distributionLeviForm_eq_zero`: a `C¹` distribution is
  involutive exactly when its Levi form vanishes at every point.
* `TauCeti.distributionLeviForm_standardContactDistribution_ne_zero`: the Levi form of the standard
  contact distribution on `ℝ³` is nonzero at every point.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge Studies in Advanced Mathematics 109
  (2008), Chapter 1 (contact structures as maximally non-integrable hyperplane fields).
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Chapter 19
  (local frames of distributions and involutivity).
-/

public section

noncomputable section

open Set Filter Function Module VectorField
open scoped Manifold ContDiff Topology

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  {n : ℕ∞ω} {k : ℕ} {D : Π x : M, Submodule 𝕜 (TangentSpace I x)} {x : M}

namespace IsDistributionFrameOn

variable {ι : Type*} [Fintype ι] {X : ι → Π y : M, TangentSpace I y} {U : Set M}
  {V V' W W' : Π y : M, TangentSpace I y}

private theorem mdifferentiableAt_extend (hX : IsDistributionFrameOn I n D X U) (hn : 1 ≤ n)
    (hU : U ∈ 𝓝 x) (u : D x) : MDiffAt (T% (hX.extend (mem_of_mem_nhds hU) u)) x :=
  ((hX.contMDiffOn_extend _ u).contMDiffAt hU).mdifferentiableAt (zero_lt_one.trans_le hn).ne'

variable [CompleteSpace E]

/-- The Levi form at `x` computed from a `C¹` frame on a neighbourhood of `x`, using the
constant-coefficient extensions of vectors of `D x`. -/
private def leviForm (hX : IsDistributionFrameOn I 1 D X U) (hU : U ∈ 𝓝 x) :
    D x →ₗ[𝕜] D x →ₗ[𝕜] TangentSpace I x ⧸ D x :=
  have hd := hX.mdifferentiableAt_extend le_rfl hU
  LinearMap.mk₂ 𝕜
    (fun u v ↦ -(D x).mkQ (mlieBracket I (hX.extend (mem_of_mem_nhds hU) u)
      (hX.extend (mem_of_mem_nhds hU) v) x))
    (fun u u' v ↦ by rw [extend_add, mlieBracket_add_left (hd u) (hd u'), map_add, neg_add])
    (fun c u v ↦ by rw [extend_smul, mlieBracket_const_smul_left (hd u), map_smul, smul_neg])
    (fun u v v' ↦ by rw [extend_add, mlieBracket_add_right (hd v) (hd v'), map_add, neg_add])
    (fun c u v ↦ by rw [extend_smul, mlieBracket_const_smul_right (hd v), map_smul, smul_neg])

variable [IsRCLikeNormedField 𝕜]

omit [Fintype ι] in
/-- The Lie bracket at `x` of a vector field `V` with any vector field `W` lies in `D x` when `V`
is differentiable at `x`, tangent to `D` near `x` and zero at `x`, provided `D` has a `C^n` local
frame near `x` with `1 ≤ n`. -/
theorem mlieBracket_mem_of_apply_eq_zero [Finite ι] (hX : IsDistributionFrameOn I n D X U)
    (hn : 1 ≤ n) (hU : U ∈ 𝓝 x) (hV : MDiffAt (T% V) x) (hVD : ∀ᶠ y in 𝓝 x, V y ∈ D y)
    (hVx : V x = 0) (W : Π y : M, TangentSpace I y) : mlieBracket I V W x ∈ D x := by
  classical
  let := Fintype.ofFinite ι
  obtain ⟨c, hc, hVc⟩ := hX.exists_mdifferentiableAt_coeff hn hU hV hVD
  have hXd (i : ι) : MDiffAt (T% (X i)) x :=
    ((hX.contMDiffOn i).contMDiffAt hU).mdifferentiableAt (zero_lt_one.trans_le hn).ne'
  -- The coefficients vanish at `x`, since the frame is linearly independent there.
  have hc0 : ∀ i, c i x = 0 :=
    Fintype.linearIndependent_iff.mp (hX.linearIndependent (mem_of_mem_nhds hU)) _
      (hVc.self_of_nhds ▸ hVx)
  have hsum (s : Finset ι) : MDiffAt (T% (∑ i ∈ s, c i • X i)) x := by
    rw [Finset.sum_fn]
    exact MDifferentiableAt.sum_section fun i _ ↦ (hc i).smul_section (hXd i)
  -- By the product rule, each term `c i • X i` contributes `-(dc i (W x)) • X i x ∈ D x`.
  have key (s : Finset ι) : mlieBracket I (∑ i ∈ s, c i • X i) W x ∈ D x := by
    induction s using Finset.induction_on with
    | empty => simp [mlieBracket_zero_left]
    | insert a s has ih =>
      rw [Finset.sum_insert has, mlieBracket_add_left ((hc a).smul_section (hXd a)) (hsum s),
        mlieBracket_smul_left (hc a) (hXd a), hc0 a, zero_smul, add_zero]
      exact (D x).add_mem ((D x).smul_mem _ (hX.apply_mem a (mem_of_mem_nhds hU))) ih
  have hVc' : V =ᶠ[𝓝 x] ∑ i, c i • X i := hVc.mono fun y hy ↦
    hy.trans (Finset.sum_apply y Finset.univ fun i ↦ c i • X i).symm
  rw [hVc'.mlieBracket_vectorField_eq (EventuallyEq.refl _ W)]
  exact key Finset.univ

omit [Fintype ι] in
/-- **Tensoriality of the Lie bracket modulo a distribution.** If `D` has a `C^n` local frame near
`x` with `1 ≤ n`, and the vector fields `V, V', W, W'` are differentiable at `x` and tangent to `D`
near `x`, with `V x = V' x` and `W x = W' x`, then `[V, W] x - [V', W'] x ∈ D x`. -/
theorem mlieBracket_sub_mlieBracket_mem [Finite ι] (hX : IsDistributionFrameOn I n D X U)
    (hn : 1 ≤ n)
    (hU : U ∈ 𝓝 x) (hV : MDiffAt (T% V) x) (hV' : MDiffAt (T% V') x) (hW : MDiffAt (T% W) x)
    (hW' : MDiffAt (T% W') x) (hVD : ∀ᶠ y in 𝓝 x, V y ∈ D y) (hV'D : ∀ᶠ y in 𝓝 x, V' y ∈ D y)
    (hWD : ∀ᶠ y in 𝓝 x, W y ∈ D y) (hW'D : ∀ᶠ y in 𝓝 x, W' y ∈ D y) (hVx : V x = V' x)
    (hWx : W x = W' x) : mlieBracket I V W x - mlieBracket I V' W' x ∈ D x := by
  have hVV' := mdifferentiableAt_sub_section hV hV'
  have hWW' := mdifferentiableAt_sub_section hW hW'
  have h₁ := hX.mlieBracket_mem_of_apply_eq_zero hn hU hVV'
    (by filter_upwards [hVD, hV'D] with y h h' using (D y).sub_mem h h') (sub_eq_zero.mpr hVx) W
  have h₂ := hX.mlieBracket_mem_of_apply_eq_zero hn hU hWW'
    (by filter_upwards [hWD, hW'D] with y h h' using (D y).sub_mem h h') (sub_eq_zero.mpr hWx) V'
  have e₁ : mlieBracket I V W x = mlieBracket I V' W x + mlieBracket I (V - V') W x := by
    rw [← mlieBracket_add_left hV' hVV', add_sub_cancel]
  have e₂ : mlieBracket I V' W x = mlieBracket I V' W' x - mlieBracket I (W - W') V' x := by
    rw [mlieBracket_swap_apply (V := W - W'), sub_neg_eq_add,
      ← mlieBracket_add_right hW' hWW', add_sub_cancel]
  rw [e₁, e₂]
  convert (D x).sub_mem h₁ h₂ using 1
  abel

private theorem leviForm_apply (hX : IsDistributionFrameOn I 1 D X U) (hU : U ∈ 𝓝 x)
    {V W : Π y : M, TangentSpace I y} (hV : MDiffAt (T% V) x) (hW : MDiffAt (T% W) x)
    (hVD : ∀ᶠ y in 𝓝 x, V y ∈ D y) (hWD : ∀ᶠ y in 𝓝 x, W y ∈ D y) :
    hX.leviForm hU ⟨V x, hVD.self_of_nhds⟩ ⟨W x, hWD.self_of_nhds⟩ =
      -(D x).mkQ (mlieBracket I V W x) := by
  have hx := mem_of_mem_nhds hU
  have hext (u : D x) : ∀ᶠ y in 𝓝 x, hX.extend hx u y ∈ D y :=
    eventually_of_mem hU fun _ hy ↦ hX.extend_mem hx u hy
  let u : D x := ⟨V x, hVD.self_of_nhds⟩
  let v : D x := ⟨W x, hWD.self_of_nhds⟩
  have h := hX.mlieBracket_sub_mlieBracket_mem le_rfl hU (hX.mdifferentiableAt_extend le_rfl hU u)
    hV (hX.mdifferentiableAt_extend le_rfl hU v) hW (hext u) hVD (hext v) hWD
    (hX.extend_apply_self hx u) (hX.extend_apply_self hx v)
  simp only [leviForm, LinearMap.mk₂_apply, neg_inj]
  exact (Submodule.Quotient.eq (D x)).mpr h

end IsDistributionFrameOn

variable [CompleteSpace E]

open scoped Classical in
variable (D x) in
/-- The **Levi form** of a distribution `D` at `x`: the bilinear map
`D x × D x → T_x M ⧸ D x` sending `(V x, W x)` to the class of `-[V, W] x`, for vector fields `V`
and `W` differentiable at `x` and tangent to `D` near `x` (`TauCeti.distributionLeviForm_apply`).
It is computed from a `C¹` local frame of `D` on a neighbourhood of `x`, and is defined to be zero
when there is no such frame. -/
def distributionLeviForm : D x →ₗ[𝕜] D x →ₗ[𝕜] TangentSpace I x ⧸ D x :=
  if h : ∃ (m : ℕ) (X : Fin m → Π y : M, TangentSpace I y) (U : Set M),
      U ∈ 𝓝 x ∧ IsDistributionFrameOn I 1 D X U then
    h.choose_spec.choose_spec.choose_spec.2.leviForm h.choose_spec.choose_spec.choose_spec.1
  else 0

/-- The Levi form of a distribution is antisymmetric. -/
theorem distributionLeviForm_swap (u v : D x) :
    distributionLeviForm D x v u = -distributionLeviForm D x u v := by
  unfold distributionLeviForm
  split_ifs with h
  · simp only [IsDistributionFrameOn.leviForm, LinearMap.mk₂_apply, neg_neg]
    rw [mlieBracket_swap_apply, map_neg, neg_neg]
  · simp

variable [IsRCLikeNormedField 𝕜]

/-- **The Levi form is the Lie bracket modulo the distribution.** If `D` has a `C^n` local frame
on a neighbourhood of `x`, with `1 ≤ n`, and the vector fields `V` and `W` are differentiable at
`x` and tangent to `D` near `x`, then the Levi form of `D` at `x` sends `(V x, W x)` to the class
of `-[V, W] x` modulo `D x`. -/
theorem IsDistributionFrameOn.distributionLeviForm_apply {ι : Type*} [Finite ι]
    {X : ι → Π y : M, TangentSpace I y} {U : Set M} (hX : IsDistributionFrameOn I n D X U)
    (hn : 1 ≤ n) (hU : U ∈ 𝓝 x) {V W : Π y : M, TangentSpace I y} (hV : MDiffAt (T% V) x)
    (hW : MDiffAt (T% W) x) (hVD : ∀ᶠ y in 𝓝 x, V y ∈ D y) (hWD : ∀ᶠ y in 𝓝 x, W y ∈ D y) :
    distributionLeviForm D x ⟨V x, hVD.self_of_nhds⟩ ⟨W x, hWD.self_of_nhds⟩ =
      -(D x).mkQ (mlieBracket I V W x) := by
  -- Reindex the frame by `Fin m` to witness the existence of a frame in the definition.
  have h : ∃ (m : ℕ) (X : Fin m → Π y : M, TangentSpace I y) (U : Set M),
      U ∈ 𝓝 x ∧ IsDistributionFrameOn I 1 D X U := by
    obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
    refine ⟨m, fun j ↦ X (e.symm j), U, hU, fun j ↦ (hX.of_le hn).contMDiffOn _,
      fun hy ↦ (hX.linearIndependent hy).comp _ e.symm.injective, fun hy ↦ ?_⟩
    rw [← hX.span_eq hy, ← e.symm.surjective.range_comp (X · _)]
    rfl
  rw [distributionLeviForm, dite_eq_left h]
  exact IsDistributionFrameOn.leviForm_apply _ _ hV hW hVD hWD

/-- The Levi form of `D` vanishes on `(V x, W x)` exactly when the Lie bracket `[V, W] x` is
tangent to `D`, for vector fields `V` and `W` differentiable at `x` and tangent to `D` near `x`,
provided `D` has a `C^n` local frame on a neighbourhood of `x`, with `1 ≤ n`. -/
theorem IsDistributionFrameOn.distributionLeviForm_apply_eq_zero_iff {ι : Type*} [Finite ι]
    {X : ι → Π y : M, TangentSpace I y} {U : Set M} (hX : IsDistributionFrameOn I n D X U)
    (hn : 1 ≤ n) (hU : U ∈ 𝓝 x) {V W : Π y : M, TangentSpace I y} (hV : MDiffAt (T% V) x)
    (hW : MDiffAt (T% W) x) (hVD : ∀ᶠ y in 𝓝 x, V y ∈ D y) (hWD : ∀ᶠ y in 𝓝 x, W y ∈ D y) :
    distributionLeviForm D x ⟨V x, hVD.self_of_nhds⟩ ⟨W x, hWD.self_of_nhds⟩ = 0 ↔
      mlieBracket I V W x ∈ D x := by
  rw [hX.distributionLeviForm_apply hn hU hV hW hVD hWD, neg_eq_zero, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero]

/-- **The Levi form is the Lie bracket modulo the distribution.** For a `C^n` distribution `D` with
`1 ≤ n`, and vector fields `V` and `W` differentiable at `x` and tangent to `D` near `x`, the Levi
form of `D` at `x` sends `(V x, W x)` to the class of `-[V, W] x` modulo `D x`. -/
theorem distributionLeviForm_apply (hD : IsContMDiffDistribution I n k D) (hn : 1 ≤ n)
    {V W : Π y : M, TangentSpace I y} (hV : MDiffAt (T% V) x) (hW : MDiffAt (T% W) x)
    (hVD : ∀ᶠ y in 𝓝 x, V y ∈ D y) (hWD : ∀ᶠ y in 𝓝 x, W y ∈ D y) :
    distributionLeviForm D x ⟨V x, hVD.self_of_nhds⟩ ⟨W x, hWD.self_of_nhds⟩ =
      -(D x).mkQ (mlieBracket I V W x) := by
  obtain ⟨U, hU, hxU, X, hX⟩ := isContMDiffDistribution_iff.mp hD x
  exact hX.distributionLeviForm_apply hn (hU.mem_nhds hxU) hV hW hVD hWD

/-- The Levi form of `D` vanishes on `(V x, W x)` exactly when the Lie bracket `[V, W] x` is
tangent to `D`, for vector fields `V` and `W` differentiable at `x` and tangent to `D` near `x`. -/
theorem distributionLeviForm_apply_eq_zero_iff (hD : IsContMDiffDistribution I n k D) (hn : 1 ≤ n)
    {V W : Π y : M, TangentSpace I y} (hV : MDiffAt (T% V) x) (hW : MDiffAt (T% W) x)
    (hVD : ∀ᶠ y in 𝓝 x, V y ∈ D y) (hWD : ∀ᶠ y in 𝓝 x, W y ∈ D y) :
    distributionLeviForm D x ⟨V x, hVD.self_of_nhds⟩ ⟨W x, hWD.self_of_nhds⟩ = 0 ↔
      mlieBracket I V W x ∈ D x := by
  obtain ⟨U, hU, hxU, X, hX⟩ := isContMDiffDistribution_iff.mp hD x
  exact hX.distributionLeviForm_apply_eq_zero_iff hn (hU.mem_nhds hxU) hV hW hVD hWD

/-- **A `C¹` distribution is involutive exactly when its Levi form vanishes.** -/
theorem isInvolutiveDistribution_iff_distributionLeviForm_eq_zero
    (hD : IsContMDiffDistribution I n k D) (hn : 1 ≤ n) :
    IsInvolutiveDistribution I D ↔ ∀ x, distributionLeviForm D x = 0 := by
  have hn0 : n ≠ 0 := (zero_lt_one.trans_le hn).ne'
  refine ⟨fun hinv x ↦ ?_, fun h ↦ isInvolutiveDistribution_iff.mpr
    fun U hU V W hV hW hVD hWD x hx ↦ ?_⟩
  · ext u v
    obtain ⟨U, hU, hxU, V, hV, hVD, hVx⟩ := hD.exists_contMDiffOn_apply_eq u
    obtain ⟨U', hU', hxU', W, hW, hWD, hWx⟩ := hD.exists_contMDiffOn_apply_eq v
    have hUU' := (hU.inter hU').mem_nhds ⟨hxU, hxU'⟩
    have hmem := hinv.mlieBracket_mem (hU.inter hU')
      ((hV.mono inter_subset_left).mdifferentiableOn hn0)
      ((hW.mono inter_subset_right).mdifferentiableOn hn0) (fun y hy ↦ hVD y hy.1)
      (fun y hy ↦ hWD y hy.2) ⟨hxU, hxU'⟩
    rw [show u = ⟨V x, hVD x hxU⟩ from Subtype.ext hVx.symm,
      show v = ⟨W x, hWD x hxU'⟩ from Subtype.ext hWx.symm, LinearMap.zero_apply,
      LinearMap.zero_apply]
    exact (distributionLeviForm_apply_eq_zero_iff hD hn
      (((hV.mono inter_subset_left).contMDiffAt hUU').mdifferentiableAt hn0)
      (((hW.mono inter_subset_right).contMDiffAt hUU').mdifferentiableAt hn0)
      (eventually_of_mem (hU.mem_nhds hxU) hVD)
      (eventually_of_mem (hU'.mem_nhds hxU') hWD)).mpr hmem
  · have hUx := hU.mem_nhds hx
    refine (distributionLeviForm_apply_eq_zero_iff hD hn (hV.mdifferentiableAt hUx)
      (hW.mdifferentiableAt hUx) (eventually_of_mem hUx hVD) (eventually_of_mem hUx hWD)).mp ?_
    rw [h x, LinearMap.zero_apply, LinearMap.zero_apply]

/-- The Levi form of the standard contact distribution `ker (dz - x dy)` on `ℝ³` is nonzero at
every point: it sends the values of the tangent fields `(1, 0, 0)` and `(0, 1, x)` to the class of
`-(0, 0, 1)`, which is not tangent to the distribution. -/
theorem distributionLeviForm_standardContactDistribution_ne_zero (p : ℝ × ℝ × ℝ) :
    distributionLeviForm (I := 𝓘(ℝ, ℝ × ℝ × ℝ)) (standardContactDistribution ℝ) p ≠ 0 := by
  have hW : HasFDerivAt (fun q : ℝ × ℝ × ℝ ↦ ((0, 1, q.1) : ℝ × ℝ × ℝ))
      ((0 : ℝ × ℝ × ℝ →L[ℝ] ℝ).prod ((0 : ℝ × ℝ × ℝ →L[ℝ] ℝ).prod
        (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)))) p :=
    (hasFDerivAt_const _ _).prodMk ((hasFDerivAt_const _ _).prodMk hasFDerivAt_fst)
  let V : Π q : ℝ × ℝ × ℝ, TangentSpace 𝓘(ℝ, ℝ × ℝ × ℝ) q := fun _ ↦ ((1, 0, 0) : ℝ × ℝ × ℝ)
  let W : Π q : ℝ × ℝ × ℝ, TangentSpace 𝓘(ℝ, ℝ × ℝ × ℝ) q := fun q ↦ ((0, 1, q.1) : ℝ × ℝ × ℝ)
  have hbracket : mlieBracket 𝓘(ℝ, ℝ × ℝ × ℝ) V W p = ((0, 0, 1) : ℝ × ℝ × ℝ) := by
    rw [mlieBracket_eq_lieBracket]
    simp [V, W, lieBracket_eq, hW.fderiv]
    -- The two sides are `(0, 0, 1)`, typed as a tangent vector and as a point of `ℝ³`.
    rfl
  intro h
  have hmem := (distributionLeviForm_apply_eq_zero_iff
    (isContMDiffDistribution_standardContactDistribution 1) le_rfl (V := V) (W := W)
    (mdifferentiableAt_vectorSpace_iff_differentiableAt (V := V).mpr (differentiableAt_const _))
    (mdifferentiableAt_vectorSpace_iff_differentiableAt (V := W).mpr hW.differentiableAt)
    (Eventually.of_forall fun q ↦ mem_standardContactDistribution.mpr (by simp [V]))
    (Eventually.of_forall fun q ↦ mem_standardContactDistribution.mpr (by simp [W]))).mp
    -- Both sides are zero, the zero bilinear map being evaluated pointwise.
    (by rw [h]; rfl)
  rw [hbracket] at hmem
  -- The tangent spaces of `ℝ³` are `ℝ³` itself, by definition.
  have h01 : ((0, 0, 1) : ℝ × ℝ × ℝ).2.2 = p.1 * ((0, 0, 1) : ℝ × ℝ × ℝ).2.1 :=
    mem_standardContactDistribution.mp hmem
  simp at h01

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Banach
public import TauCeti.Analysis.Normed.Algebra.Multiplier.Basic
public import TauCeti.Topology.ApproximateUnit
import TauCeti.Analysis.Normed.Operator.Dense

/-!
# Double centralizers of nondegenerate Banach algebras

Mathlib's multiplier algebra `𝓜(𝕜, A)` of a normed algebra `A` consists of pairs `(S, T)` of
bounded linear maps on `A` satisfying the centrality condition `T x * y = x * S y`. Building on the
basic API in `TauCeti.Analysis.Normed.Algebra.Multiplier.Basic`, this file shows that, for a
Banach algebra `A` with zero left and right annihilators, neither linearity nor boundedness needs
to be assumed: every pair of functions `S T : A → A` with `T x * y = x * S y` is a double
centralizer, `DoubleCentralizer.ofCentral`. Linearity follows by testing against all of `A`.
Boundedness follows from the closed graph theorem: if `x n → 0` and `S (x n) → y`, then
`c * y = lim T c * x n = 0` for every `c`, so `y = 0`, and symmetrically for `T`. Hence the pairs
of centralizers of elements of `𝓜(𝕜, A)` are exactly the pairs of functions satisfying the
centrality condition, `DoubleCentralizer.range_coeFn_fst_snd`, and so exactly those satisfying
the three laws of the classical definition.

The annihilator conditions are the instances `FaithfulSMul Aᵐᵒᵖ A` and `FaithfulSMul A A`; an
approximate unit supplies both (`TauCeti.faithfulSMul_of_tendsto_mul_left` and
`TauCeti.faithfulSMul_mulOpposite_of_tendsto_mul_right`), as does a proper involution. A
bounded approximate unit moreover controls norms: if a left approximate unit of `A` is bounded
by `C`, then `‖S‖ ≤ C * ‖T‖` and `‖a‖ ≤ C * ‖(a : 𝓜(𝕜, A))‖`, while a right one
gives `‖T‖ ≤ C * ‖S‖`. For a two-sided approximate unit of norm at most `1` this gives
`‖S‖ = ‖T‖`. A left approximate unit of norm at most `1` makes `A → 𝓜(𝕜, A)` isometric and
gives `‖R_a‖ = ‖a‖` for the right multiplication `R_a`, while a right one gives `‖L_a‖ = ‖a‖`
for the left multiplication `L_a`; for a general bound `C` the map is only bounded below.
Consequently the canonical image of a Banach algebra with a bounded left approximate unit is closed
in its multiplier algebra.

## Main definitions

* `DoubleCentralizer.ofCentral`: the double centralizer built from a pair of functions satisfying
  the centrality condition, for a complete algebra with zero annihilators.

## Main results

* `DoubleCentralizer.range_coeFn_fst_snd`: the pairs of underlying functions of double
  centralizers are exactly the pairs of functions satisfying the centrality condition.
* `DoubleCentralizer.norm_fst_le_mul_norm_snd`, `DoubleCentralizer.norm_snd_le_mul_norm_fst`:
  comparison of the two centralizer norms under a bounded approximate unit.
* `DoubleCentralizer.norm_le_mul_norm_coe`, `DoubleCentralizer.isClosed_range_coe`: lower norm
  bound and closedness of the canonical image `A → 𝓜(𝕜, A)` under a bounded left approximate
  unit.
* `DoubleCentralizer.norm_fst_eq_snd_of_isApproximateUnit`,
  `DoubleCentralizer.isometry_coe_of_tendsto_mul_right`,
  `DoubleCentralizer.norm_coe_fst_of_tendsto_mul_left`,
  `DoubleCentralizer.norm_coe_snd_of_tendsto_mul_right`: the contractive case.
* `DoubleCentralizer.exists_clm_tendsto_fst`: along a bounded left approximate unit, a norm-bounded
  multiplicative action of `A` on a Banach space with dense essential subspace converges at
  `m.fst e` to a bounded operator extending `m`.

## References

* M. A. Rieffel, *C⋆-algebras*, Math 208 lectures, UC Berkeley, Spring 2008, notes by
  T. Johnson-Freyd, p. 38: double centralizers and the multiplier algebra of an algebra with an
  approximate identity.
* B. E. Johnson, *An introduction to the theory of centralizers*, Proc. London Math. Soc. (3) 14
  (1964), 299–320.
-/

public section

noncomputable section

open Filter Topology
open scoped MultiplierAlgebra

namespace DoubleCentralizer

variable {𝕜 A : Type*} [NontriviallyNormedField 𝕜] [NonUnitalNormedRing A] [NormedSpace 𝕜 A]
  [SMulCommClass 𝕜 A A] [IsScalarTower 𝕜 A A]

/-! ### Double centralizers from pairs of functions -/

section OfCentral

variable [FaithfulSMul Aᵐᵒᵖ A] [FaithfulSMul A A] {S T : A → A}

/-- The left map of a central pair, as a linear map: linearity follows from centrality. -/
private def fstₗ (h : ∀ x y, T x * y = x * S y) : A →ₗ[𝕜] A where
  toFun := S
  map_add' x y := MulOpposite.op_injective <| FaithfulSMul.eq_of_smul_eq_smul fun c => by
    rw [op_smul_eq_mul, op_smul_eq_mul, ← h, mul_add, mul_add, ← h, ← h]
  map_smul' k x := MulOpposite.op_injective <| FaithfulSMul.eq_of_smul_eq_smul fun c => by
    rw [op_smul_eq_mul, op_smul_eq_mul, ← h, RingHom.id_apply, mul_smul_comm, mul_smul_comm, ← h]

/-- The right map of a central pair, as a linear map: linearity follows from centrality. -/
private def sndₗ (h : ∀ x y, T x * y = x * S y) : A →ₗ[𝕜] A where
  toFun := T
  map_add' x y := FaithfulSMul.eq_of_smul_eq_smul fun c => by
    rw [smul_eq_mul, smul_eq_mul, h, add_mul, add_mul, h, h]
  map_smul' k x := FaithfulSMul.eq_of_smul_eq_smul fun c => by
    rw [smul_eq_mul, smul_eq_mul, h, RingHom.id_apply, smul_mul_assoc, smul_mul_assoc, h]

variable [CompleteSpace A]

omit [IsScalarTower 𝕜 A A] [FaithfulSMul A A] in
/-- The left map of a central pair is continuous, by the closed graph theorem. -/
private theorem continuous_fstₗ (h : ∀ x y, T x * y = x * S y) :
    Continuous (fstₗ (𝕜 := 𝕜) h) :=
  (fstₗ h).continuous_of_seq_closed_graph fun u x y hu hy =>
    MulOpposite.op_injective <| FaithfulSMul.eq_of_smul_eq_smul fun c => by
      have hc : (fun n => c * (fstₗ (𝕜 := 𝕜) h ∘ u) n) = fun n => T c * u n :=
        funext fun n => (h c (u n)).symm
      rw [op_smul_eq_mul, op_smul_eq_mul]
      exact tendsto_nhds_unique (hy.const_mul c) (hc ▸ hu.const_mul (T c)) |>.trans (h c x)

omit [SMulCommClass 𝕜 A A] [FaithfulSMul Aᵐᵒᵖ A] in
/-- The right map of a central pair is continuous, by the closed graph theorem. -/
private theorem continuous_sndₗ (h : ∀ x y, T x * y = x * S y) :
    Continuous (sndₗ (𝕜 := 𝕜) h) :=
  (sndₗ h).continuous_of_seq_closed_graph fun u x y hu hy =>
    FaithfulSMul.eq_of_smul_eq_smul fun c => by
      have hc : (fun n => (sndₗ (𝕜 := 𝕜) h ∘ u) n * c) = fun n => u n * S c :=
        funext fun n => h (u n) c
      rw [smul_eq_mul, smul_eq_mul]
      exact tendsto_nhds_unique (hy.mul_const c) (hc ▸ hu.mul_const (S c)) |>.trans (h x c).symm

variable (𝕜) in
/-- The double centralizer of a complete normed algebra with zero left and right annihilators
determined by a pair of functions `S T : A → A` with `T x * y = x * S y`. Its left and right
centralizers are `S` and `T`; no linearity or continuity of `S` and `T` is assumed. -/
def ofCentral (S T : A → A) (h : ∀ x y, T x * y = x * S y) : 𝓜(𝕜, A) where
  fst := ⟨fstₗ h, continuous_fstₗ h⟩
  snd := ⟨sndₗ h, continuous_sndₗ h⟩
  central := h

/-- The left centralizer of `ofCentral 𝕜 S T h` is `S`. -/
@[simp]
theorem coe_ofCentral_fst (h : ∀ x y, T x * y = x * S y) : ⇑(ofCentral 𝕜 S T h).fst = S :=
  (rfl)

/-- The right centralizer of `ofCentral 𝕜 S T h` is `T`. -/
@[simp]
theorem coe_ofCentral_snd (h : ∀ x y, T x * y = x * S y) : ⇑(ofCentral 𝕜 S T h).snd = T :=
  (rfl)

/-- A double centralizer is recovered from its pair of centralizers by `ofCentral`. -/
@[simp]
theorem ofCentral_fst_snd (m : 𝓜(𝕜, A)) : ofCentral 𝕜 m.fst m.snd m.central = m :=
  ext_fst_snd (fun _ => rfl) (fun _ => rfl)

/-- For a complete normed algebra with zero left and right annihilators, the pairs of underlying
functions of double centralizers are exactly the pairs of functions `(S, T)` with
`T x * y = x * S y`. Such pairs are automatically linear and bounded, and satisfy the module laws
`S (x * y) = S x * y` and `T (x * y) = x * T y` (`DoubleCentralizer.fst_mul`,
`DoubleCentralizer.snd_mul`). -/
theorem range_coeFn_fst_snd :
    Set.range (fun m : 𝓜(𝕜, A) => ((m.fst : A → A), (m.snd : A → A))) =
      {p : (A → A) × (A → A) | ∀ x y, p.2 x * y = x * p.1 y} :=
  Set.ext fun p => ⟨by rintro ⟨m, rfl⟩; exact m.central,
    fun h => ⟨ofCentral 𝕜 p.1 p.2 h, by simp⟩⟩

end OfCentral

/-! ### Norm estimates from bounded approximate units -/

section Norm

variable {l : Filter A} {C : ℝ}

/-- If `A` has a left approximate unit bounded by `C`, the left centralizer of a multiplier is
bounded by `C` times its right centralizer. -/
theorem norm_fst_le_mul_norm_snd [l.NeBot] (hC : ∀ᶠ e in l, ‖e‖ ≤ C)
    (hl : ∀ a, Tendsto (· * a) l (𝓝 a)) (m : 𝓜(𝕜, A)) : ‖m.fst‖ ≤ C * ‖m.snd‖ := by
  have hC0 : 0 ≤ C := let ⟨e, he⟩ := hC.exists; (norm_nonneg e).trans he
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x =>
    le_of_tendsto (hl (m.fst x)).norm <| hC.mono fun e he => ?_
  rw [← m.central]
  calc ‖m.snd e * x‖ ≤ ‖m.snd‖ * ‖e‖ * ‖x‖ :=
        (norm_mul_le _ _).trans (by gcongr; exact m.snd.le_opNorm e)
    _ ≤ C * ‖m.snd‖ * ‖x‖ := by
        rw [mul_comm C]
        gcongr

/-- If `A` has a right approximate unit bounded by `C`, the right centralizer of a multiplier is
bounded by `C` times its left centralizer. -/
theorem norm_snd_le_mul_norm_fst [l.NeBot] (hC : ∀ᶠ e in l, ‖e‖ ≤ C)
    (hl : ∀ a, Tendsto (a * ·) l (𝓝 a)) (m : 𝓜(𝕜, A)) : ‖m.snd‖ ≤ C * ‖m.fst‖ := by
  have hC0 : 0 ≤ C := let ⟨e, he⟩ := hC.exists; (norm_nonneg e).trans he
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x =>
    le_of_tendsto (hl (m.snd x)).norm <| hC.mono fun e he => ?_
  rw [m.central]
  calc ‖x * m.fst e‖ ≤ ‖x‖ * (‖m.fst‖ * ‖e‖) :=
        (norm_mul_le _ _).trans (by gcongr; exact m.fst.le_opNorm e)
    _ ≤ C * ‖m.fst‖ * ‖x‖ := by
        rw [mul_comm, mul_comm C]
        gcongr

/-- If `A` has a left approximate unit bounded by `C`, the canonical map of `A` into its
multiplier algebra is bounded below: `‖a‖ ≤ C * ‖(a : 𝓜(𝕜, A))‖`. -/
theorem norm_le_mul_norm_coe [l.NeBot] (hC : ∀ᶠ e in l, ‖e‖ ≤ C) (hl : ∀ a, Tendsto (· * a) l (𝓝 a))
    (a : A) : ‖a‖ ≤ C * ‖(a : 𝓜(𝕜, A))‖ :=
  le_of_tendsto (hl a).norm <| hC.mono fun e he =>
    calc ‖e * a‖ = ‖(a : 𝓜(𝕜, A)).snd e‖ := by simp
      _ ≤ ‖(a : 𝓜(𝕜, A))‖ * ‖e‖ :=
          ((a : 𝓜(𝕜, A)).snd.le_opNorm e).trans (by gcongr; exact norm_snd_le _)
      _ ≤ C * ‖(a : 𝓜(𝕜, A))‖ := by
          rw [mul_comm C]
          gcongr

/-- If a Banach algebra `A` has a bounded left approximate unit, the image of the canonical map
`A → 𝓜(𝕜, A)` is closed. -/
theorem isClosed_range_coe [CompleteSpace A] [l.NeBot] (hC : ∀ᶠ e in l, ‖e‖ ≤ C)
    (hl : ∀ a, Tendsto (· * a) l (𝓝 a)) :
    IsClosed (Set.range (DoubleCentralizer.coe 𝕜 : A → 𝓜(𝕜, A))) :=
  (AntilipschitzWith.of_le_mul_dist (K := C.toNNReal) fun a b => by
      rw [dist_eq_norm, dist_eq_norm, ← coe_sub]
      exact (norm_le_mul_norm_coe hC hl _).trans <|
        mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal C) (norm_nonneg _)).isClosed_range
    (LipschitzWith.of_dist_le_mul (K := 1) fun a b => by
      rw [dist_eq_norm, dist_eq_norm, ← coe_sub, NNReal.coe_one, one_mul]
      exact norm_coe_le _).uniformContinuous

/-! ### Contractive approximate units -/

/-- If `A` has an approximate unit of norm at most `1`, the left and right centralizers of a
multiplier have equal norms. -/
theorem norm_fst_eq_snd_of_isApproximateUnit (hl : l.IsApproximateUnit)
    (h1 : ∀ᶠ e in l, ‖e‖ ≤ 1) (m : 𝓜(𝕜, A)) : ‖m.fst‖ = ‖m.snd‖ := by
  have := hl.neBot
  exact le_antisymm (by simpa using norm_fst_le_mul_norm_snd h1 hl.tendsto_mul_right m)
    (by simpa using norm_snd_le_mul_norm_fst h1 hl.tendsto_mul_left m)

/-- If `A` has a left approximate unit of norm at most `1`, the canonical map of `A` into its
multiplier algebra preserves the norm. -/
theorem norm_coe_of_tendsto_mul_right [l.NeBot] (h1 : ∀ᶠ e in l, ‖e‖ ≤ 1)
    (hl : ∀ a, Tendsto (· * a) l (𝓝 a)) (a : A) : ‖(a : 𝓜(𝕜, A))‖ = ‖a‖ :=
  le_antisymm (norm_coe_le a) (by simpa using norm_le_mul_norm_coe h1 hl a)

/-- If `A` has a left approximate unit of norm at most `1`, the canonical map of `A` into its
multiplier algebra is an isometry. -/
theorem isometry_coe_of_tendsto_mul_right [l.NeBot] (h1 : ∀ᶠ e in l, ‖e‖ ≤ 1)
    (hl : ∀ a, Tendsto (· * a) l (𝓝 a)) : Isometry (DoubleCentralizer.coe 𝕜 : A → 𝓜(𝕜, A)) := by
  intro a b
  simp only [edist_dist, dist_eq_norm, ← coe_sub, norm_coe_of_tendsto_mul_right h1 hl]

/-- If `A` has a right approximate unit of norm at most `1`, left multiplication by `a`, the left
centralizer of `(a : 𝓜(𝕜, A))`, has norm `‖a‖`. -/
theorem norm_coe_fst_of_tendsto_mul_left [l.NeBot] (h1 : ∀ᶠ e in l, ‖e‖ ≤ 1)
    (hl : ∀ a, Tendsto (a * ·) l (𝓝 a)) (a : A) : ‖(a : 𝓜(𝕜, A)).fst‖ = ‖a‖ :=
  le_antisymm ((norm_fst_le _).trans (norm_coe_le a)) <|
    le_of_tendsto (hl a).norm <| h1.mono fun e he =>
      calc ‖a * e‖ = ‖(a : 𝓜(𝕜, A)).fst e‖ := by simp
        _ ≤ ‖(a : 𝓜(𝕜, A)).fst‖ * ‖e‖ := (a : 𝓜(𝕜, A)).fst.le_opNorm e
        _ ≤ ‖(a : 𝓜(𝕜, A)).fst‖ := mul_le_of_le_one_right (norm_nonneg _) he

/-- If `A` has a left approximate unit of norm at most `1`, right multiplication by `a`, the right
centralizer of `(a : 𝓜(𝕜, A))`, has norm `‖a‖`. -/
theorem norm_coe_snd_of_tendsto_mul_right [l.NeBot] (h1 : ∀ᶠ e in l, ‖e‖ ≤ 1)
    (hl : ∀ a, Tendsto (· * a) l (𝓝 a)) (a : A) : ‖(a : 𝓜(𝕜, A)).snd‖ = ‖a‖ :=
  le_antisymm ((norm_snd_le _).trans (norm_coe_le a)) <|
    le_of_tendsto (hl a).norm <| h1.mono fun e he =>
      calc ‖e * a‖ = ‖(a : 𝓜(𝕜, A)).snd e‖ := by simp
        _ ≤ ‖(a : 𝓜(𝕜, A)).snd‖ * ‖e‖ := (a : 𝓜(𝕜, A)).snd.le_opNorm e
        _ ≤ ‖(a : 𝓜(𝕜, A)).snd‖ := mul_le_of_le_one_right (norm_nonneg _) he

/-- If `A` has a left approximate unit bounded by `C` and `L : A → E →L[𝕜] E` is a norm-bounded
multiplicative map with point-continuous orbits and dense essential subspace in a complete normed
space `E`, then for every multiplier `m : 𝓜(𝕜, A)` the operators `L (m.fst e)` converge strongly
along `l` to a bounded operator `T` satisfying `T * L a = L (m.fst a)` for all `a : A`. -/
theorem exists_clm_tendsto_fst {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [CompleteSpace E] [l.NeBot] {K : ℝ} (hC : ∀ᶠ e in l, ‖e‖ ≤ C)
    (hl : ∀ a, Tendsto (· * a) l (𝓝 a)) {L : A → E →L[𝕜] E}
    (hL_cont : ∀ x, Continuous fun a => L a x) (hL_mul : ∀ a b, L (a * b) = L a * L b)
    (hL_norm : ∀ a, ‖L a‖ ≤ K * ‖a‖)
    (hL_dense : Dense (Submodule.span 𝕜 (⋃ a, Set.range (L a)) : Set E)) (m : 𝓜(𝕜, A)) :
    ∃ T : E →L[𝕜] E, (∀ a, T * L a = L (m.fst a)) ∧
      ∀ x, Tendsto (fun e => L (m.fst e) x) l (𝓝 (T x)) := by
  have := TauCeti.faithfulSMul_mulOpposite_of_tendsto_mul_right hl
  have happ (a : A) (x : E) :
      Tendsto (fun e => L (m.fst e) (L a x)) l (𝓝 (L (m.fst a) x)) :=
    (((hL_cont x).comp m.fst.continuous).tendsto a |>.comp (hl a)).congr fun e => by
      simp [Function.comp_apply, fst_mul, hL_mul, mul_apply_eq_comp]
  have hbound : ∀ᶠ e in l, ‖L (m.fst e)‖ ≤ max K 0 * (‖m‖ * C) :=
    hC.mono fun e he => (hL_norm _).trans <| (mul_le_mul_of_nonneg_right (le_max_left K 0)
      (norm_nonneg _)).trans <| mul_le_mul_of_nonneg_left
        ((m.fst.le_opNorm e).trans (mul_le_mul (norm_fst_le m) he (norm_nonneg e) (norm_nonneg m)))
        (le_max_right K 0)
  obtain ⟨T, hT⟩ := ContinuousLinearMap.exists_tendsto_apply_of_dense_span hL_dense hbound
    fun _ hx => let ⟨a, x, hax⟩ := Set.mem_iUnion.1 hx
      hax ▸ ⟨L (m.fst a) x, happ a x⟩
  exact ⟨T, fun a => ContinuousLinearMap.ext fun x =>
    tendsto_nhds_unique (hT (L a x)) (happ a x), hT⟩

end Norm

end DoubleCentralizer

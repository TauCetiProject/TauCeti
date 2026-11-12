/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Analysis.CStarAlgebra.Multiplier
public import TauCeti.Topology.ApproximateUnit

/-!
# Double centralizers of nondegenerate Banach algebras

Mathlib's multiplier algebra `𝓜(𝕜, A)` of a normed algebra `A` consists of pairs `(S, T)` of
bounded linear maps on `A` satisfying the centrality condition `T x * y = x * S y`. This file
shows that, for a Banach algebra `A` with zero left and right annihilators, neither linearity
nor boundedness needs to be assumed: every pair of functions `S T : A → A` with
`T x * y = x * S y` is a double centralizer, `DoubleCentralizer.ofCentral`. Linearity follows
by testing against all of `A`. Boundedness follows from the closed graph theorem: if `x n → 0`
and `S (x n) → y`, then `c * y = lim T c * x n = 0` for every `c`, so `y = 0`, and symmetrically
for `T`. The module laws `S (a * b) = S a * b` and `T (a * b) = a * T b` also follow from
centrality (`DoubleCentralizer.fst_mul`, `DoubleCentralizer.snd_mul`). Hence the pairs of
centralizers of elements of `𝓜(𝕜, A)` are exactly the pairs of functions satisfying the
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
Consequently
the canonical image of a Banach algebra with a bounded left approximate unit is closed in its
multiplier algebra; it is a two-sided ideal by `DoubleCentralizer.mul_coe_eq_coe_fst` and
`DoubleCentralizer.coe_mul_eq_coe_snd`. The image is essential: a multiplier annihilating `A` on
either side vanishes.

## Main definitions

* `DoubleCentralizer.ofCentral`: the double centralizer built from a pair of functions satisfying
  the centrality condition, for a complete algebra with zero annihilators.

## Main results

* `DoubleCentralizer.fst_mul`, `DoubleCentralizer.snd_mul`: with zero annihilators, the
  centralizers are module maps for right and left multiplication.
* `DoubleCentralizer.coe_injective`, `DoubleCentralizer.ext_fst`: with zero annihilators, the
  canonical map `A → 𝓜(𝕜, A)` is injective and a multiplier is determined by its left
  centralizer.
* `DoubleCentralizer.range_coeFn_fst_snd`: the pairs of underlying functions of double
  centralizers are exactly the pairs of functions satisfying the centrality condition.
* `DoubleCentralizer.norm_fst_le_mul_norm_snd`, `DoubleCentralizer.norm_snd_le_mul_norm_fst`:
  comparison of the two centralizer norms under a bounded approximate unit.
* `DoubleCentralizer.norm_le_mul_norm_coe`, `DoubleCentralizer.norm_coe_le`: the canonical map
  `A → 𝓜(𝕜, A)` is bounded above and below.
* `DoubleCentralizer.isClosed_range_coe`: its range is closed.
* `DoubleCentralizer.norm_fst_eq_snd_of_isApproximateUnit`,
  `DoubleCentralizer.isometry_coe_of_tendsto_mul_right`,
  `DoubleCentralizer.norm_coe_fst_of_tendsto_mul_left`,
  `DoubleCentralizer.norm_coe_snd_of_tendsto_mul_right`: the contractive case.
* `DoubleCentralizer.eq_zero_of_forall_mul_coe_eq_zero`,
  `DoubleCentralizer.eq_zero_of_forall_coe_mul_eq_zero`: the image of `A` is an essential ideal.

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

/-! ### Basic API of the canonical inclusion and of nondegenerate double centralizers -/

section NontriviallyNormed

variable {𝕜 A : Type*} [NontriviallyNormedField 𝕜] [NonUnitalNormedRing A] [NormedSpace 𝕜 A]
  [SMulCommClass 𝕜 A A] [IsScalarTower 𝕜 A A]

/-- Two multipliers are equal if their left and right centralizers agree pointwise. -/
theorem ext_fst_snd {m n : 𝓜(𝕜, A)} (h₁ : ∀ a, m.fst a = n.fst a)
    (h₂ : ∀ a, m.snd a = n.snd a) : m = n :=
  DoubleCentralizer.ext _ _ _ _ <|
    Prod.ext (ContinuousLinearMap.ext h₁) (ContinuousLinearMap.ext h₂)

/-- The inclusion of `A` into its multiplier algebra sends `0` to `0`. -/
@[simp, norm_cast]
theorem coe_zero : ((0 : A) : 𝓜(𝕜, A)) = 0 :=
  ext_fst_snd (fun _ => by simp) (fun _ => by simp)

/-- The inclusion of `A` into its multiplier algebra commutes with addition. -/
@[simp, norm_cast]
theorem coe_add (a b : A) : ((a + b : A) : 𝓜(𝕜, A)) = (a : 𝓜(𝕜, A)) + b :=
  ext_fst_snd (fun _ => by simp) (fun _ => by simp)

/-- The inclusion of `A` into its multiplier algebra commutes with multiplication. -/
@[simp, norm_cast]
theorem coe_mul (a b : A) : ((a * b : A) : 𝓜(𝕜, A)) = (a : 𝓜(𝕜, A)) * b :=
  ext_fst_snd (fun _ => by simp [mul_assoc]) (fun _ => by simp [mul_assoc])

/-- The inclusion of `A` into its multiplier algebra commutes with negation. -/
@[simp, norm_cast]
theorem coe_neg (a : A) : ((-a : A) : 𝓜(𝕜, A)) = -(a : 𝓜(𝕜, A)) :=
  ext_fst_snd (fun _ => by simp) (fun _ => by simp)

/-- The inclusion of `A` into its multiplier algebra commutes with subtraction. -/
@[simp, norm_cast]
theorem coe_sub (a b : A) : ((a - b : A) : 𝓜(𝕜, A)) = (a : 𝓜(𝕜, A)) - b :=
  ext_fst_snd (fun _ => by simp) (fun _ => by simp)

/-- The inclusion of `A` into its multiplier algebra commutes with scalar multiplication. -/
@[simp, norm_cast]
theorem coe_smul (c : 𝕜) (a : A) : ((c • a : A) : 𝓜(𝕜, A)) = c • (a : 𝓜(𝕜, A)) :=
  ext_fst_snd (fun _ => by simp) (fun _ => by simp)

/-- The inclusion of `A` into its multiplier algebra commutes with the star operation. -/
@[simp, norm_cast]
theorem coe_star [StarRing 𝕜] [StarRing A] [StarModule 𝕜 A] [NormedStarGroup A] (a : A) :
    ((star a : A) : 𝓜(𝕜, A)) = star (a : 𝓜(𝕜, A)) :=
  map_star (coeHom (𝕜 := 𝕜)) a

end NontriviallyNormed

section Unital

variable {𝕜 A : Type*} [NontriviallyNormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A]

/-- The inclusion of a unital algebra into its multiplier algebra sends `1` to `1`. -/
@[simp, norm_cast]
theorem coe_one : ((1 : A) : 𝓜(𝕜, A)) = 1 :=
  ext_fst_snd (fun _ => by simp) (fun _ => by simp)

end Unital

section FaithfulMulOpposite

variable {𝕜 A : Type*} [NontriviallyNormedField 𝕜] [NonUnitalNormedRing A] [NormedSpace 𝕜 A]
  [SMulCommClass 𝕜 A A] [IsScalarTower 𝕜 A A] [FaithfulSMul Aᵐᵒᵖ A]

/-- The left centralizer of a multiplier commutes with right multiplication. -/
theorem fst_mul (m : 𝓜(𝕜, A)) (a b : A) : m.fst (a * b) = m.fst a * b :=
  MulOpposite.op_injective <| FaithfulSMul.eq_of_smul_eq_smul fun y => by
    rw [op_smul_eq_mul, op_smul_eq_mul, ← mul_assoc, ← m.central, ← m.central, mul_assoc]

/-- A multiplier times an element of `A` is the element obtained from the left centralizer. -/
@[simp]
theorem mul_coe_eq_coe_fst (m : 𝓜(𝕜, A)) (a : A) : m * (a : 𝓜(𝕜, A)) = (m.fst a : 𝓜(𝕜, A)) :=
  ext_fst_snd (fun _ => by simp [fst_mul]) (fun _ => by simp [m.central])

/-- The canonical map of `A` into its multiplier algebra is injective. -/
theorem coe_injective : Function.Injective (DoubleCentralizer.coe 𝕜 : A → 𝓜(𝕜, A)) :=
  fun a b h => MulOpposite.op_injective <| FaithfulSMul.eq_of_smul_eq_smul fun y => by
    rw [op_smul_eq_mul, op_smul_eq_mul]
    simpa using congrArg (fun m : 𝓜(𝕜, A) => m.snd y) h

@[simp, norm_cast]
theorem coe_inj {a b : A} : (a : 𝓜(𝕜, A)) = b ↔ a = b :=
  coe_injective.eq_iff

end FaithfulMulOpposite

section Faithful

variable {𝕜 A : Type*} [NontriviallyNormedField 𝕜] [NonUnitalNormedRing A] [NormedSpace 𝕜 A]
  [SMulCommClass 𝕜 A A] [IsScalarTower 𝕜 A A] [FaithfulSMul A A]

/-- The right centralizer of a multiplier commutes with left multiplication. -/
theorem snd_mul (m : 𝓜(𝕜, A)) (a b : A) : m.snd (a * b) = a * m.snd b :=
  FaithfulSMul.eq_of_smul_eq_smul fun y => by
    rw [smul_eq_mul, smul_eq_mul, m.central, mul_assoc, mul_assoc, m.central]

/-- An element of `A` times a multiplier is the element obtained from the right centralizer. -/
@[simp]
theorem coe_mul_eq_coe_snd (a : A) (m : 𝓜(𝕜, A)) : (a : 𝓜(𝕜, A)) * m = (m.snd a : 𝓜(𝕜, A)) :=
  ext_fst_snd (fun _ => by simp [m.central]) (fun _ => by simp [snd_mul])

/-- A multiplier is determined by its left centralizer. -/
theorem ext_fst {m n : 𝓜(𝕜, A)} (h : ∀ a, m.fst a = n.fst a) : m = n :=
  ext_fst_snd h fun a => FaithfulSMul.eq_of_smul_eq_smul fun y => by
    rw [smul_eq_mul, smul_eq_mul, m.central, n.central, h]

end Faithful

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

/-- The norm of a multiplier dominates the norm of its right centralizer. -/
theorem norm_snd_le (m : 𝓜(𝕜, A)) : ‖m.snd‖ ≤ ‖m‖ :=
  (norm_def m).symm ▸ _root_.norm_snd_le (toProdHom m)

/-- The norm of a multiplier dominates the norm of its left centralizer. -/
theorem norm_fst_le (m : 𝓜(𝕜, A)) : ‖m.fst‖ ≤ ‖m‖ :=
  (norm_def m).symm ▸ _root_.norm_fst_le (toProdHom m)

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

/-- The canonical map of `A` into its multiplier algebra is contractive. -/
theorem norm_coe_le (a : A) : ‖(a : 𝓜(𝕜, A))‖ ≤ ‖a‖ := by
  simp only [norm_def, toProdHom_apply, Prod.norm_def, coe_fst, coe_snd, max_le_iff]
  exact ⟨ContinuousLinearMap.opNorm_mul_apply_le 𝕜 A a,
    ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg a) fun x => by
      simpa [mul_comm ‖a‖] using norm_mul_le x a⟩

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

end Norm

/-! ### Essentiality of the canonical ideal -/

section Essential

variable [FaithfulSMul Aᵐᵒᵖ A] [FaithfulSMul A A]

/-- A multiplier whose products with every element of `A` on the right vanish is zero. -/
theorem eq_zero_of_forall_mul_coe_eq_zero {m : 𝓜(𝕜, A)} (h : ∀ a : A, m * (a : 𝓜(𝕜, A)) = 0) :
    m = 0 :=
  ext_fst fun a => coe_injective (𝕜 := 𝕜) <| by
    simp [← mul_coe_eq_coe_fst, h]

/-- A multiplier whose products with every element of `A` on the left vanish is zero. -/
theorem eq_zero_of_forall_coe_mul_eq_zero {m : 𝓜(𝕜, A)} (h : ∀ a : A, (a : 𝓜(𝕜, A)) * m = 0) :
    m = 0 := by
  have hsnd (a : A) : m.snd a = 0 := coe_injective (𝕜 := 𝕜) <| by
    rw [← coe_mul_eq_coe_snd, h, coe_zero]
  refine ext_fst_snd (fun a => MulOpposite.op_injective <|
    FaithfulSMul.eq_of_smul_eq_smul (α := A) fun c => ?_) fun a => by simp [hsnd]
  rw [op_smul_eq_mul, op_smul_eq_mul]
  simp [← m.central, hsnd]

end Essential

end DoubleCentralizer

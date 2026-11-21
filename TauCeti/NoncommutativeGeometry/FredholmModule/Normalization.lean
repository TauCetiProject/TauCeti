/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import TauCeti.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Contraction
public import TauCeti.Analysis.InnerProductSpace.ProdL2
public import TauCeti.Analysis.InnerProductSpace.Spectral.BlockSum
public import TauCeti.Analysis.Normed.Operator.Compact.EssentialCommutant
public import TauCeti.NoncommutativeGeometry.FredholmModule.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import TauCeti.Analysis.Normed.Operator.Compact.Interpolation
import TauCeti.Analysis.SpecialFunctions.Trigonometric.Sinc

/-!
# Normalization of Fredholm modules

The operator `F` of a Fredholm module `(H, π, F)` only satisfies `F² = 1` modulo operators that
become compact after multiplication by `π(a)`. The index pairing and the Chern character are
built from modules with `F² = 1` exactly, and every Fredholm module can be brought to that form
in two steps.

1. **The sine replacement.** For a self-adjoint `F` the operator `sin (π F / 2)`, defined by the
   continuous functional calculus, is a self-adjoint contraction. It still has compact commutators
   with the representation, because the essential commutant of `π(A)` is closed under the
   functional calculus, and its defect `sin (π F / 2)² - 1 = -cos (π F / 2)²` is a continuous
   function of `F` times `F² - 1`, since `cos (π x / 2)` vanishes at `x = ±1`. The function
   `sin (π x / 2)` fixes the essential values `±1`: a merely rescaled contraction such as `F / ‖F‖`
   would in general not have a compact defect.
2. **The doubling.** For a self-adjoint contraction `F`, put `S = √(1 - F²)`. On `H ⊕ H` the
   operator
   `F' = [[F, S], [S, -F]]`
   is a self-adjoint involution, `F'² = 1`, because `S` commutes with `F` and `F² + S² = 1`. With
   the representation `π ⊕ 0` the pair is again a Fredholm module: the commutator of `F'` with
   `π(a) ⊕ 0` has the blocks `[F, π(a)]`, `-π(a) S` and `S π(a)`, and `S π(a)` is compact because
   `(S π(a))* (S π(a)) = π(a*) (1 - F²) π(a)` is. In the even case the grading is `γ ⊕ -γ`.

Composing the two gives `FredholmModule.normalize` and `EvenFredholmModule.normalize`, Fredholm
modules over the same algebra on `H ⊕ H` whose operator squares to `1`.

## Main definitions

* `TauCeti.doublingOperator F`: the operator `[[F, √(1 - F²)], [√(1 - F²), -F]]` on `H ⊕ H`, a
  self-adjoint involution when `F` is a self-adjoint contraction.
* `TauCeti.FredholmModule.sineReplacement`: the module with operator `sin (π F / 2)`.
* `TauCeti.FredholmModule.double`: the doubled module on `H ⊕ H` of a module whose operator is a
  contraction.
* `TauCeti.FredholmModule.normalize`: the doubled sine replacement, with `F² = 1`.
* `TauCeti.EvenFredholmModule.sineReplacement`, `TauCeti.EvenFredholmModule.double`,
  `TauCeti.EvenFredholmModule.normalize`: the even versions, with grading `γ ⊕ -γ` on `H ⊕ H`.

## Main results

* `TauCeti.FredholmModule.isCompactOperator_cfc_commutator`: `[f(F), π(a)]` is compact for every
  real function `f`.
* `TauCeti.FredholmModule.isCompactOperator_sqrt_mul_rep`: `√(1 - F²) π(a)` is compact.
* `TauCeti.doublingOperator_mul_self`: `F'² = 1`.
* `TauCeti.FredholmModule.normalize_operator_mul_self`: the normalized module has `F² = 1`.

## References

* A. Connes, *Noncommutative Geometry*, Academic Press (1994), Chapter IV, §1.
* N. Higson, J. Roe, *Analytic K-Homology*, Oxford Mathematical Monographs (2000), §8.3
  (Lemma 8.3.8 for the doubling).
-/

public section

noncomputable section

open ContinuousLinearMap Real

namespace TauCeti

variable {A : Type*} [NonUnitalNonAssocSemiring A] [Module ℂ A] [Star A]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### The doubling operator -/

/-- The **doubling operator** of `F`: the operator `[[F, √(1 - F²)], [√(1 - F²), -F]]` on the
Hilbert direct sum `H ⊕ H`. For a self-adjoint contraction `F` it is a self-adjoint involution
(`TauCeti.isSelfAdjoint_doublingOperator`, `TauCeti.doublingOperator_mul_self`) whose upper left
corner is `F`. -/
def doublingOperator (F : H →L[ℂ] H) : WithLp 2 (H × H) →L[ℂ] WithLp 2 (H × H) :=
  WithLp.blockL2 F (CFC.sqrt (1 - F * F)) (CFC.sqrt (1 - F * F)) (-F)

/-- The block form of the doubling operator. -/
theorem doublingOperator_def (F : H →L[ℂ] H) :
    doublingOperator F =
      WithLp.blockL2 F (CFC.sqrt (1 - F * F)) (CFC.sqrt (1 - F * F)) (-F) :=
  (rfl)

/-- The doubling operator of a self-adjoint operator is self-adjoint. -/
theorem isSelfAdjoint_doublingOperator {F : H →L[ℂ] H} (hF : IsSelfAdjoint F) :
    IsSelfAdjoint (doublingOperator F) := by
  have hS : IsSelfAdjoint (CFC.sqrt (1 - F * F)) := (CFC.sqrt_nonneg _).isSelfAdjoint
  rw [IsSelfAdjoint, doublingOperator, WithLp.star_blockL2, ← star_eq_adjoint, hS.star_eq,
    star_neg, hF.star_eq]

/-- **The doubling operator is an involution.** For a self-adjoint contraction `F`,
`[[F, √(1 - F²)], [√(1 - F²), -F]]² = 1`. -/
theorem doublingOperator_mul_self {F : H →L[ℂ] H} (hF : IsSelfAdjoint F) (hF₁ : ‖F‖ ≤ 1) :
    doublingOperator F * doublingOperator F = 1 := by
  rw [doublingOperator, WithLp.blockL2_mul_blockL2, ← withLpProdMap_one (p := 2),
    ← WithLp.blockL2_zero_zero]
  set S := CFC.sqrt (1 - F * F)
  have hSS : S * S = 1 - F * F := CFC.sqrt_mul_sqrt_self _ (hF.one_sub_mul_self_nonneg hF₁)
  have hFS : F * S = S * F :=
    (hF.commute_sqrt_one_sub_mul_self hF₁ ((Commute.refl F).mul_left (Commute.refl F))).eq.symm
  simp only [← mul_def, mul_neg, neg_mul, neg_neg, hSS, hFS, WithLp.blockL2_inj]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> abel

/-! ### Odd Fredholm modules -/

namespace FredholmModule

variable (M : FredholmModule A H)

/-- The operator of a Fredholm module lies in the essential commutant of its representation. -/
theorem operator_mem_essentialCommutant :
    M.operator ∈ essentialCommutant (Set.range M.rep) :=
  mem_essentialCommutant.2 <| by
    rintro _ ⟨a, rfl⟩
    exact M.isCompactOperator_commutator a

/-- **Functions of `F` have compact commutators.** For every real function `f`, the commutator
`[f(F), π(a)]` of the continuous functional calculus of `F` with the representation is
compact. -/
theorem isCompactOperator_cfc_commutator (f : ℝ → ℝ) (a : A) :
    IsCompactOperator ⇑(cfc f M.operator * M.rep a - M.rep a * cfc f M.operator) :=
  mem_essentialCommutant.1 (cfc_mem_essentialCommutant
    (by rintro _ ⟨b, rfl⟩; exact ⟨star b, map_star M.rep b⟩) f M.operator_mem_essentialCommutant)
    _ ⟨a, rfl⟩

/-- `sin (π x / 2) ^ 2 - 1 = g x * (x ^ 2 - 1)` for the continuous function
`g x = (π / 2) ^ 2 * sinc (π (1 - x) / 2) * sinc (π (1 + x) / 2)`, because `cos (π x / 2)` is
both `sin (π (1 - x) / 2)` and `sin (π (1 + x) / 2)`. -/
private theorem sin_mul_sin_sub_one (x : ℝ) :
    sin (π * x / 2) * sin (π * x / 2) - 1 =
      (π / 2) ^ 2 * sinc (π * (1 - x) / 2) * sinc (π * (1 + x) / 2) * (x * x - 1) := by
  have h₁ : π * (1 - x) / 2 * sinc (π * (1 - x) / 2) = cos (π * x / 2) := by
    rw [mul_sinc, ← sin_pi_div_two_sub]; ring_nf
  have h₂ : π * (1 + x) / 2 * sinc (π * (1 + x) / 2) = cos (π * x / 2) := by
    rw [mul_sinc, ← sin_add_pi_div_two]; ring_nf
  have h : sin (π * x / 2) * sin (π * x / 2) - 1 = -(cos (π * x / 2) * cos (π * x / 2)) := by
    nlinarith [sin_sq_add_cos_sq (π * x / 2)]
  rw [h]
  nth_rw 1 [← h₁]
  rw [← h₂]
  ring

/-- The defect of the sine replacement: `sin (π F / 2)² - 1 = g(F) (F² - 1)` for a continuous
function `g`. -/
private theorem cfc_sin_mul_cfc_sin_sub_one :
    ∃ G : H →L[ℂ] H, cfc (fun x : ℝ => sin (π * x / 2)) M.operator *
      cfc (fun x : ℝ => sin (π * x / 2)) M.operator - 1 = G * (M.operator * M.operator - 1) := by
  have hF := M.isSelfAdjoint_operator
  set g : ℝ → ℝ := fun x => (π / 2) ^ 2 * sinc (π * (1 - x) / 2) * sinc (π * (1 + x) / 2)
  have hg : Continuous g := by
    have := continuous_sinc
    fun_prop
  have hs : Continuous fun x : ℝ => sin (π * x / 2) := by fun_prop
  refine ⟨cfc g M.operator, ?_⟩
  have e₁ : cfc (fun x : ℝ => sin (π * x / 2) * sin (π * x / 2) - 1) M.operator =
      cfc (fun x : ℝ => sin (π * x / 2)) M.operator *
        cfc (fun x : ℝ => sin (π * x / 2)) M.operator - 1 := by
    rw [cfc_sub (fun x : ℝ => sin (π * x / 2) * sin (π * x / 2)) (fun _ => 1) M.operator,
      cfc_mul _ _ M.operator hs.continuousOn hs.continuousOn, cfc_const_one ℝ M.operator]
  have e₂ : cfc (fun x => g x * (x * x - 1)) M.operator = cfc g M.operator *
      (M.operator * M.operator - 1) := by
    rw [cfc_mul g (fun x : ℝ => x * x - 1) M.operator hg.continuousOn,
      cfc_sub (fun x : ℝ => x * x) (fun _ => 1) M.operator,
      cfc_mul (fun x : ℝ => x) (fun x : ℝ => x) M.operator, cfc_id' ℝ M.operator,
      cfc_const_one ℝ M.operator]
  rw [← e₁, ← e₂]
  exact cfc_congr fun x _ => sin_mul_sin_sub_one x

/-- **The sine replacement** of a Fredholm module: the operator `F` is replaced by the
self-adjoint contraction `sin (π F / 2)` (`norm_sineReplacement_operator_le_one`), with the same
representation. -/
def sineReplacement : FredholmModule A H where
  rep := M.rep
  operator := cfc (fun x : ℝ => sin (π * x / 2)) M.operator
  isSelfAdjoint_operator := cfc_predicate _ _
  isCompactOperator_commutator := M.isCompactOperator_cfc_commutator _
  isCompactOperator_mul_self_sub_one_mul a := by
    obtain ⟨G, hG⟩ := M.cfc_sin_mul_cfc_sin_sub_one
    rw [hG, mul_assoc]
    exact (M.isCompactOperator_mul_self_sub_one_mul a).mul_left G

@[simp]
theorem sineReplacement_rep : M.sineReplacement.rep = M.rep :=
  (rfl)

@[simp]
theorem sineReplacement_operator :
    M.sineReplacement.operator = cfc (fun x : ℝ => sin (π * x / 2)) M.operator :=
  (rfl)

/-- The operator of the sine replacement is a contraction. -/
theorem norm_sineReplacement_operator_le_one : ‖M.sineReplacement.operator‖ ≤ 1 :=
  norm_cfc_le zero_le_one fun x _ => by simpa using abs_sin_le_one (π * x / 2)

/-- **The off-diagonal blocks of the doubling are compact.** `√(1 - F²) π(a)` is compact. When
`1 - F²` is not positive, `CFC.sqrt` gives `0` and the statement is trivial; for a contraction
`F` it holds because `(√(1 - F²) π(a))* √(1 - F²) π(a) = π(a*) (1 - F²) π(a)` is compact. -/
theorem isCompactOperator_sqrt_mul_rep (a : A) :
    IsCompactOperator ⇑(CFC.sqrt (1 - M.operator * M.operator) * M.rep a) := by
  by_cases hnn : 0 ≤ 1 - M.operator * M.operator
  swap
  · rw [CFC.sqrt_of_not_nonneg hnn, zero_mul]
    exact isCompactOperator_zero
  set S := CFC.sqrt (1 - M.operator * M.operator)
  have hS : IsSelfAdjoint S := (CFC.sqrt_nonneg _).isSelfAdjoint
  have hSS : S * S = 1 - M.operator * M.operator := CFC.sqrt_mul_sqrt_self _ hnn
  refine IsCompactOperator.of_adjoint_comp_self ?_
  rw [← star_eq_adjoint, ← mul_def]
  have h : star (S * M.rep a) * (S * M.rep a) =
      -(M.rep (star a) * ((M.operator * M.operator - 1) * M.rep a)) := by
    rw [star_mul, hS.star_eq, ← map_star, mul_assoc, ← mul_assoc S, hSS, ← neg_sub, neg_mul,
      mul_neg]
  rw [h, FunLike.coe_neg]
  exact ((M.isCompactOperator_mul_self_sub_one_mul a).mul_left _).neg

/-- Mirror image of `isCompactOperator_sqrt_mul_rep`: `π(a) √(1 - F²)` is compact. -/
theorem isCompactOperator_rep_mul_sqrt (a : A) :
    IsCompactOperator ⇑(M.rep a * CFC.sqrt (1 - M.operator * M.operator)) := by
  have hS : IsSelfAdjoint (CFC.sqrt (1 - M.operator * M.operator)) :=
    (CFC.sqrt_nonneg _).isSelfAdjoint
  simpa only [star_mul, hS.star_eq, map_star, star_star] using
    (M.isCompactOperator_sqrt_mul_rep (star a)).star

/-- The commutator of the doubling operator with `π(a) ⊕ 0` is compact: it is the block operator
`[[[F, π(a)], -π(a) S], [S π(a), 0]]` with `S = √(1 - F²)`. -/
private theorem isCompactOperator_doublingOperator_commutator (a : A) :
    IsCompactOperator ⇑(doublingOperator M.operator * (M.rep a).withLpProdMap 2 (0 : H →L[ℂ] H) -
      (M.rep a).withLpProdMap 2 (0 : H →L[ℂ] H) * doublingOperator M.operator) := by
  have h : doublingOperator M.operator * (M.rep a).withLpProdMap 2 0 -
      (M.rep a).withLpProdMap 2 0 * doublingOperator M.operator =
        WithLp.blockL2 (M.operator * M.rep a - M.rep a * M.operator)
          (-(M.rep a * CFC.sqrt (1 - M.operator * M.operator)))
          (CFC.sqrt (1 - M.operator * M.operator) * M.rep a) 0 := by
    rw [doublingOperator, ← WithLp.blockL2_zero_zero, WithLp.blockL2_mul_blockL2,
      WithLp.blockL2_mul_blockL2, WithLp.blockL2_sub_blockL2]
    simp [← mul_def]
  rw [h]
  exact WithLp.isCompactOperator_blockL2 (M.isCompactOperator_commutator a)
    (M.isCompactOperator_rep_mul_sqrt a).neg (M.isCompactOperator_sqrt_mul_rep a)
    isCompactOperator_zero

section Double

variable {M}

/-- **The doubling** of a Fredholm module whose operator `F` is a contraction: the Fredholm module
on `H ⊕ H` with representation `π ⊕ 0` and operator
`[[F, √(1 - F²)], [√(1 - F²), -F]]`, which squares to `1`
(`TauCeti.doublingOperator_mul_self`). -/
def double (M : FredholmModule A H) (hF₁ : ‖M.operator‖ ≤ 1) :
    FredholmModule A (WithLp 2 (H × H)) where
  rep := (withLpProdMapStarAlgHom.toNonUnitalStarAlgHom.comp
    ((NonUnitalStarAlgHom.id ℂ (H →L[ℂ] H)).prod 0)).comp M.rep
  operator := doublingOperator M.operator
  isSelfAdjoint_operator := isSelfAdjoint_doublingOperator M.isSelfAdjoint_operator
  isCompactOperator_commutator a := by
    simpa using M.isCompactOperator_doublingOperator_commutator a
  isCompactOperator_mul_self_sub_one_mul a := by
    rw [doublingOperator_mul_self M.isSelfAdjoint_operator hF₁, sub_self, zero_mul]
    exact isCompactOperator_zero

@[simp]
theorem double_rep_apply (hF₁ : ‖M.operator‖ ≤ 1) (a : A) :
    (M.double hF₁).rep a = (M.rep a).withLpProdMap 2 0 := by
  simp [double]

@[simp]
theorem double_operator (hF₁ : ‖M.operator‖ ≤ 1) :
    (M.double hF₁).operator = doublingOperator M.operator :=
  (rfl)

end Double

/-- **The normalization** of a Fredholm module: the doubling of its sine replacement, a Fredholm
module on `H ⊕ H` with representation `π ⊕ 0` whose operator squares to `1`
(`normalize_operator_mul_self`). -/
def normalize : FredholmModule A (WithLp 2 (H × H)) :=
  M.sineReplacement.double M.norm_sineReplacement_operator_le_one

theorem normalize_def :
    M.normalize = M.sineReplacement.double M.norm_sineReplacement_operator_le_one :=
  (rfl)

@[simp]
theorem normalize_rep_apply (a : A) : M.normalize.rep a = (M.rep a).withLpProdMap 2 0 :=
  M.sineReplacement.double_rep_apply _ a

@[simp]
theorem normalize_operator :
    M.normalize.operator = doublingOperator (cfc (fun x : ℝ => sin (π * x / 2)) M.operator) :=
  (rfl)

/-- The operator of the normalized module is an involution: `F² = 1`. -/
theorem normalize_operator_mul_self : M.normalize.operator * M.normalize.operator = 1 :=
  doublingOperator_mul_self M.sineReplacement.isSelfAdjoint_operator
    M.norm_sineReplacement_operator_le_one

end FredholmModule

/-! ### Even Fredholm modules -/

namespace EvenFredholmModule

variable (M : EvenFredholmModule A H)

/-- **The sine replacement**, even version: the grading anticommutes with `sin (π F / 2)`, since
the sine is odd. -/
def sineReplacement : EvenFredholmModule A H where
  toFredholmModule := M.toFredholmModule.sineReplacement
  grading := M.grading
  isSelfAdjoint_grading := M.isSelfAdjoint_grading
  grading_mul_grading := M.grading_mul_grading
  commute_grading_rep := M.commute_grading_rep
  grading_mul_operator := mul_cfc_eq_neg_cfc_mul M.isSelfAdjoint_grading M.grading_mul_grading
    M.isSelfAdjoint_operator M.grading_mul_operator fun x => by rw [mul_neg, neg_div, sin_neg]

@[simp]
theorem sineReplacement_toFredholmModule :
    M.sineReplacement.toFredholmModule = M.toFredholmModule.sineReplacement :=
  (rfl)

@[simp]
theorem sineReplacement_grading : M.sineReplacement.grading = M.grading :=
  (rfl)

/-- **The doubling**, even version: the grading of the doubled module is `γ ⊕ -γ`, which
anticommutes with `[[F, √(1 - F²)], [√(1 - F²), -F]]` because `γ` anticommutes with `F` and
commutes with `F²`. -/
def double (hF₁ : ‖M.operator‖ ≤ 1) : EvenFredholmModule A (WithLp 2 (H × H)) where
  toFredholmModule := M.toFredholmModule.double hF₁
  grading := M.grading.withLpProdMap 2 (-M.grading)
  isSelfAdjoint_grading := (isSelfAdjoint_withLpProdMap_iff _ _).2
    ⟨M.isSelfAdjoint_grading, M.isSelfAdjoint_grading.neg⟩
  grading_mul_grading := by
    rw [← withLpProdMap_mul, neg_mul_neg, M.grading_mul_grading, withLpProdMap_one]
  commute_grading_rep a := by
    rw [Commute, SemiconjBy, FredholmModule.double_rep_apply, ← withLpProdMap_mul,
      ← withLpProdMap_mul, (M.commute_grading_rep a).eq, mul_zero, zero_mul]
  grading_mul_operator := by
    have hFγ : M.operator * M.grading = -(M.grading * M.operator) := by
      rw [M.grading_mul_operator, neg_neg]
    have hγS : M.grading * CFC.sqrt (1 - M.operator * M.operator) =
        CFC.sqrt (1 - M.operator * M.operator) * M.grading :=
      (M.isSelfAdjoint_operator.commute_sqrt_one_sub_mul_self hF₁
        (by rw [Commute, SemiconjBy, mul_assoc, hFγ, mul_neg, ← mul_assoc, hFγ, neg_mul,
          neg_neg, mul_assoc])).eq.symm
    rw [FredholmModule.double_operator, doublingOperator, ← WithLp.blockL2_zero_zero,
      WithLp.blockL2_mul_blockL2, WithLp.blockL2_mul_blockL2, WithLp.neg_blockL2]
    simp [← mul_def, M.grading_mul_operator, hγS]

@[simp]
theorem double_toFredholmModule (hF₁ : ‖M.operator‖ ≤ 1) :
    (M.double hF₁).toFredholmModule = M.toFredholmModule.double hF₁ :=
  (rfl)

@[simp]
theorem double_grading (hF₁ : ‖M.operator‖ ≤ 1) :
    (M.double hF₁).grading = M.grading.withLpProdMap 2 (-M.grading) :=
  (rfl)

/-- **The normalization**, even version: the doubling of the sine replacement, with grading
`γ ⊕ -γ` and an operator that squares to `1`. -/
def normalize : EvenFredholmModule A (WithLp 2 (H × H)) :=
  M.sineReplacement.double M.toFredholmModule.norm_sineReplacement_operator_le_one

@[simp]
theorem normalize_toFredholmModule :
    M.normalize.toFredholmModule = M.toFredholmModule.normalize :=
  (rfl)

@[simp]
theorem normalize_grading :
    M.normalize.grading = M.grading.withLpProdMap 2 (-M.grading) :=
  (rfl)

end EvenFredholmModule

end TauCeti

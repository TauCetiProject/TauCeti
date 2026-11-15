/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
public import TauCeti.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Polar
public import TauCeti.Geometry.Lie.Exponential.Units.Basic
import Mathlib.Analysis.Normed.Ring.Units

/-!
# The Cartan decomposition of the group of units

Let `A` be a complete normed real algebra with a star-ordered involution and an isometric real
continuous functional calculus, for instance a unital C⋆-algebra or the algebra `Matrix n n 𝕜` of
square matrices over `ℝ` or `ℂ` with the `ℓ²` operator norm. The exponential of a self-adjoint
element is strictly positive, and the functional-calculus logarithm `CFC.log` inverts it.
Combined with the right polar decomposition `a = u √(a⋆ a)` of a unit
(`Units.polarUnitary_mul_sqrt_star_mul`), this shows that every unit factors uniquely as

`a = u * exp x`, with `u` unitary and `x` self-adjoint,

namely `u = a.polarUnitary` and `x = log √(a⋆ a)`. Both factors depend continuously on `a`, so the
map `(u, x) ↦ u * exp x` is a homeomorphism `unitary A × selfAdjoint A ≃ₜ Aˣ`.

For `A = Matrix n n ℝ` this is the global Cartan decomposition `GL(n, ℝ) = O(n) · exp 𝔭` of the
general linear group, where `𝔭` is the space of symmetric matrices, the `-1` eigenspace of the
Cartan involution `X ↦ -Xᵀ` of `𝔤𝔩(n, ℝ)`; over `ℂ` it is `GL(n, ℂ) = U(n) · exp 𝔭` with `𝔭` the
Hermitian matrices. The matrix statement is `Matrix.GeneralLinearGroup.cartanHomeomorph`, in
`TauCeti/Analysis/Matrix/Cartan.lean`. Topologically, the homeomorphism identifies `Aˣ` with the
product of the unitary group and the real vector space `selfAdjoint A`.

The decomposition restricts to a subgroup `G` of `Aˣ` that is closed under `a ↦ a⋆` and such that,
for self-adjoint `x`, the line `t ↦ exp (t x)` lies in `G` as soon as `exp x` does. For `a ∈ G`,
the element `a⋆ a = exp (2 x)` lies in `G`, hence so does the line through `x`, and then so does
the unitary factor `a exp (-x)`. Thus `G` is homeomorphic to the product of its unitary elements
and of the self-adjoint elements of its Lie algebra `{x | ∀ t, exp (t x) ∈ G}`. For a subgroup of
`GL(n, ℝ)` or `GL(n, ℂ)` this is the global Cartan decomposition `G = K exp 𝔭`, with `K = G ∩ U(n)`
and `𝔭` the Hermitian part of the Lie algebra of `G`. The hypotheses hold for the special linear
groups (`Matrix.SpecialLinearGroup.cartanHomeomorph`) and, more generally, for real algebraic groups
stable under conjugate transpose; they fail for a discrete subgroup such as the powers of a
positive diagonal matrix, which is not a product of this form.

## Main declarations

* `IsSelfAdjoint.isStrictlyPositive_exp`: the exponential of a self-adjoint element is strictly
  positive.
* `Units.polarUnitary_mul_exp_log_sqrt_star_mul`: the Cartan factorization
  `a = a.polarUnitary * exp (log √(a⋆ a))` of a unit.
* `Units.mul_exp_eq_iff_polarUnitary_eq_and_log_sqrt_star_mul_eq`: its uniqueness.
* `Units.coe_polarUnitary_eq_mul_exp_neg_log_sqrt_star_mul`: the unitary factor is
  `a * exp (-log √(a⋆ a))`.
* `Units.continuous_polarUnitary`, `Units.continuous_log_sqrt_star_mul`: both factors depend
  continuously on the unit.
* `TauCeti.cartanHomeomorph`: the homeomorphism `unitary A × selfAdjoint A ≃ₜ Aˣ`,
  `(u, x) ↦ u * exp x`, with `TauCeti.val_cartanHomeomorph_apply`,
  `TauCeti.cartanHomeomorph_symm_apply_fst` and `TauCeti.coe_cartanHomeomorph_symm_apply_snd`
  computing it and its inverse.
* `TauCeti.cartanHomeomorph_mem_iff`: for a subgroup `G` as above, `u * exp x` lies in `G` exactly
  when `u` does and the whole line `exp (t x)` does.
* `Subgroup.cartanHomeomorph`: the Cartan decomposition of such a subgroup, the
  homeomorphism `{u ∈ unitary A | u ∈ G} × {x ∈ selfAdjoint A | ∀ t, exp (t x) ∈ G} ≃ₜ G`, with
  `Subgroup.val_cartanHomeomorph_apply`, `Subgroup.coe_cartanHomeomorph_symm_apply_fst` and
  `Subgroup.coe_cartanHomeomorph_symm_apply_snd` computing it and its inverse.

## References

* Anthony W. Knapp, *Lie Groups Beyond an Introduction*, second edition, Progress in Mathematics
  140, Birkhäuser, 2002, Chapter VI, Section 1 (the global Cartan decomposition).
* Brian C. Hall, *Lie Groups, Lie Algebras, and Representations*, second edition, Graduate Texts
  in Mathematics 222, Springer, 2015, Section 2.5 (the polar decomposition `A = U e^X` of
  `GL(n, ℂ)` with `U` unitary and `X` self-adjoint).
* G. D. Mostow, *Self-adjoint groups*, Annals of Mathematics (2) 62 (1955), 44–55 (the Cartan
  decomposition of an algebraic group of matrices closed under conjugate transpose).
-/

public section

noncomputable section

open NormedSpace

section Factorization

variable {A : Type*} [NormedRing A] [StarRing A] [NormedAlgebra ℝ A] [PartialOrder A]
  [StarOrderedRing A] [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint] [NonnegSpectrumClass ℝ A]

/-- The exponential of a self-adjoint element is strictly positive. -/
@[aesop safe apply (rule_sets := [CStarAlgebra])]
theorem IsSelfAdjoint.isStrictlyPositive_exp {x : A} (hx : IsSelfAdjoint x) :
    IsStrictlyPositive (NormedSpace.exp x) := by
  rw [← CFC.real_exp_eq_normedSpace_exp]
  exact (cfc_isStrictlyPositive_iff Real.exp x).2 fun t _ ↦ Real.exp_pos t

namespace Units

variable (a : Aˣ)

/-- **The Cartan factorization** `a = u * exp x` of a unit, with `u = a.polarUnitary` unitary and
`x = log √(a⋆ a)` self-adjoint. -/
@[simp]
theorem polarUnitary_mul_exp_log_sqrt_star_mul :
    a.polarUnitary * exp (CFC.log (CFC.sqrt (star (a : A) * a))) = a := by
  rw [CFC.exp_log _ (isStrictlyPositive_sqrt_star_mul a), polarUnitary_mul_sqrt_star_mul]

/-- **Uniqueness of the Cartan factorization.** A unit `a` is `u * exp x`, with `u` unitary and `x`
self-adjoint, exactly when `u = a.polarUnitary` and `x = log √(a⋆ a)`. -/
theorem mul_exp_eq_iff_polarUnitary_eq_and_log_sqrt_star_mul_eq {u : unitary A} {x : A}
    (hx : IsSelfAdjoint x) :
    u * exp x = a ↔ a.polarUnitary = u ∧ CFC.log (CFC.sqrt (star (a : A) * a)) = x := by
  rw [mul_eq_iff_polarUnitary_eq_and_sqrt_star_mul_eq a hx.exp_nonneg]
  refine and_congr_right fun _ ↦ ⟨fun h ↦ by rw [h, CFC.log_exp x hx], fun h ↦ ?_⟩
  rw [← h, CFC.exp_log _ (isStrictlyPositive_sqrt_star_mul a)]

variable [CompleteSpace A] in
/-- The unitary Cartan factor of a unit `a = u * exp x` is `u = a * exp (-x)`. -/
theorem coe_polarUnitary_eq_mul_exp_neg_log_sqrt_star_mul :
    (a.polarUnitary : A) = a * exp (-CFC.log (CFC.sqrt (star (a : A) * a))) := by
  -- Mathlib's lemmas on `exp` in a Banach algebra are stated for normed `ℚ`-algebras.
  let : NormedAlgebra ℚ A := .restrictScalars ℚ ℝ A
  calc (a.polarUnitary : A)
      = a.polarUnitary * exp (CFC.log (CFC.sqrt (star (a : A) * a))) *
          exp (-CFC.log (CFC.sqrt (star (a : A) * a))) := by
        rw [mul_assoc, ← exp_add_of_commute (Commute.refl _).neg_right, add_neg_cancel, exp_zero,
          mul_one]
    _ = a * exp (-CFC.log (CFC.sqrt (star (a : A) * a))) := by
      rw [polarUnitary_mul_exp_log_sqrt_star_mul]

end Units

end Factorization

section Continuity

variable {A : Type*} [NormedRing A] [StarRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
  [PartialOrder A] [StarOrderedRing A] [IsometricContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
  [NonnegSpectrumClass ℝ A] [ContinuousStar A]

namespace Units

/-- The self-adjoint Cartan factor `log √(a⋆ a)` of a unit depends continuously on the unit. -/
theorem continuous_log_sqrt_star_mul :
    Continuous fun a : Aˣ ↦ CFC.log (CFC.sqrt (star (a : A) * a)) := by
  have hval : Continuous fun a : Aˣ ↦ star (a : A) * a :=
    (continuous_val.star).mul continuous_val
  refine CFC.continuousOn_log.comp_continuous
    (CFC.continuousOn_sqrt.comp_continuous hval fun a ↦ star_mul_self_nonneg (a : A)) fun a ↦ ?_
  have ha := a.isStrictlyPositive_sqrt_star_mul
  exact ⟨ha.isSelfAdjoint, ha.isUnit⟩

/-- The polar unitary factor `a.polarUnitary` of a unit depends continuously on the unit. -/
theorem continuous_polarUnitary : Continuous fun a : Aˣ ↦ a.polarUnitary := by
  -- Mathlib's lemmas on `exp` in a Banach algebra are stated for normed `ℚ`-algebras.
  let : NormedAlgebra ℚ A := .restrictScalars ℚ ℝ A
  refine Continuous.subtype_mk ?_ _
  simp_rw [coe_polarUnitary_eq_mul_exp_neg_log_sqrt_star_mul]
  exact continuous_val.mul (exp_continuous.comp continuous_log_sqrt_star_mul.neg)

end Units

end Continuity

namespace TauCeti

variable {A : Type*} [NormedRing A] [StarRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
  [PartialOrder A] [StarOrderedRing A] [IsometricContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
  [NonnegSpectrumClass ℝ A] [ContinuousStar A]

variable (A) in
/-- **The Cartan decomposition** of the group of units: the map `(u, x) ↦ u * exp x` is a
homeomorphism from the product of the unitary group and the self-adjoint elements onto the group of
units. Its inverse sends a unit `a` to its polar unitary factor `a.polarUnitary` and the logarithm
`log √(a⋆ a)` of its positive factor.

For matrices, see `Matrix.GeneralLinearGroup.cartanHomeomorph`, which specializes over `ℝ` to
`O(n) × Sym(n) ≃ₜ GL(n, ℝ)` using the default entrywise topology. -/
def cartanHomeomorph : unitary A × selfAdjoint A ≃ₜ Aˣ where
  toFun p := Unitary.toUnits p.1 * (p.2.prop.isStrictlyPositive_exp).isUnit.unit
  invFun a := (a.polarUnitary, ⟨CFC.log (CFC.sqrt (star (a : A) * a)), IsSelfAdjoint.log⟩)
  left_inv p := by
    obtain ⟨hu, hx⟩ := (Units.mul_exp_eq_iff_polarUnitary_eq_and_log_sqrt_star_mul_eq
      (Unitary.toUnits p.1 * (p.2.prop.isStrictlyPositive_exp).isUnit.unit) (u := p.1)
      p.2.prop).1 (by simp)
    exact Prod.ext hu (Subtype.ext hx)
  right_inv a := Units.ext (by simp)
  continuous_toFun := by
    -- Mathlib's lemmas on `exp` in a Banach algebra are stated for normed `ℚ`-algebras.
    let : NormedAlgebra ℚ A := .restrictScalars ℚ ℝ A
    refine (Units.isOpenEmbedding_val (R := A)).isEmbedding.continuous_iff.2 ?_
    simp only [Function.comp_def, Units.val_mul, Unitary.val_toUnits_apply, IsUnit.unit_spec]
    exact (continuous_subtype_val.comp continuous_fst).mul
      (exp_continuous.comp (continuous_subtype_val.comp continuous_snd))
  continuous_invFun :=
    Units.continuous_polarUnitary.prodMk (Units.continuous_log_sqrt_star_mul.subtype_mk _)

/-- The Cartan decomposition map sends `(u, x)` to `u * exp x`. -/
@[simp]
theorem val_cartanHomeomorph_apply (p : unitary A × selfAdjoint A) :
    (cartanHomeomorph A p : A) = p.1 * exp (p.2 : A) := by
  simp [cartanHomeomorph]

/-- The unitary factor of the Cartan decomposition of `a` is its polar unitary factor. -/
@[simp]
theorem cartanHomeomorph_symm_apply_fst (a : Aˣ) :
    ((cartanHomeomorph A).symm a).1 = a.polarUnitary :=
  (rfl)

/-- The self-adjoint factor of the Cartan decomposition of `a` is `log √(a⋆ a)`. -/
@[simp]
theorem coe_cartanHomeomorph_symm_apply_snd (a : Aˣ) :
    (((cartanHomeomorph A).symm a).2 : A) = CFC.log (CFC.sqrt (star (a : A) * a)) :=
  (rfl)

section Subgroup

/-! ### The Cartan decomposition of a subgroup closed under the involution -/

attribute [local instance] TauCeti.normedAlgebraRatOfReal

/-- The Cartan decomposition map sends `(u, x)` to the product of the units `u` and `exp x`. -/
theorem cartanHomeomorph_apply (p : unitary A × selfAdjoint A) :
    cartanHomeomorph A p = Unitary.toUnits p.1 * expUnit (p.2 : A) :=
  Units.ext (by simp)

variable {G : Subgroup Aˣ}

/-- Let `G` be a subgroup of the units closed under the involution, such that the exponential
line `t ↦ exp (t x)` stays in `G` as soon as `exp x` does, for self-adjoint `x`. Then for `u`
unitary and `x` self-adjoint, `u * exp x` lies in `G` exactly when `u` lies in `G` and `x` lies in
the Lie algebra `{x | ∀ t, exp (t x) ∈ G}` of `G`. -/
theorem cartanHomeomorph_mem_iff (hstar : ∀ a ∈ G, star a ∈ G)
    (hexp : ∀ x : A, IsSelfAdjoint x → expUnit x ∈ G → ∀ t : ℝ, expUnit (t • x) ∈ G)
    (p : unitary A × selfAdjoint A) :
    cartanHomeomorph A p ∈ G ↔
      Unitary.toUnits p.1 ∈ G ∧ ∀ t : ℝ, expUnit (t • (p.2 : A)) ∈ G := by
  obtain ⟨u, x, hx⟩ := p
  refine ⟨fun h ↦ ?_, fun ⟨hu, hx'⟩ ↦ ?_⟩
  · -- `a⋆ a = exp x⋆ u⋆ u exp x = exp (2 x)`, so the line through `2 x` lies in `G`.
    have h2 : expUnit ((2 : ℝ) • x) = star (cartanHomeomorph A (u, ⟨x, hx⟩)) *
        cartanHomeomorph A (u, ⟨x, hx⟩) := by
      refine Units.ext ?_
      simp only [expUnit_coe, Units.val_mul, Units.coe_star, val_cartanHomeomorph_apply, star_mul,
        (hx.exp).star_eq, mul_assoc, ← mul_assoc (star (u : A)), Unitary.coe_star_mul_self,
        one_mul]
      rw [← exp_add_of_commute (Commute.refl x), two_smul]
    have hline (t : ℝ) : expUnit (t • x) ∈ G := by
      have h2x : IsSelfAdjoint ((2 : ℝ) • x) := by
        rw [two_smul]
        exact hx.add hx
      have := hexp _ h2x (h2 ▸ G.mul_mem (hstar _ h) h) (t / 2)
      rwa [smul_smul, div_mul_cancel₀ t two_ne_zero] at this
    refine ⟨?_, hline⟩
    -- The unitary factor is `a * (exp x)⁻¹`.
    have hu : Unitary.toUnits u = cartanHomeomorph A (u, ⟨x, hx⟩) * (expUnit x)⁻¹ := by
      rw [cartanHomeomorph_apply, mul_inv_cancel_right]
    rw [hu]
    exact G.mul_mem h (G.inv_mem (by simpa using hline 1))
  · rw [cartanHomeomorph_apply]
    exact G.mul_mem hu (by simpa using hx' 1)

variable (G) in
/-- **The Cartan decomposition of a subgroup closed under the involution.** Let `G` be a subgroup
of the units closed under `a ↦ a⋆`, such that for self-adjoint `x` with `exp x ∈ G` the whole line
`exp (t x)` lies in `G`. Then `(u, x) ↦ u * exp x` is a homeomorphism from the product of the
unitary elements of `G` and the self-adjoint elements `x` of the Lie algebra of `G`, those with
`exp (t x) ∈ G` for every real `t`, onto `G`.

For a subgroup of `GL(n, ℝ)` or `GL(n, ℂ)` satisfying these hypotheses, such as `SL(n, ℝ)` or
`SL(n, ℂ)`, this is the global Cartan decomposition `G = K exp 𝔭`, with `K = G ∩ U(n)` and `𝔭` the
Hermitian part of the Lie algebra of `G`. -/
def _root_.Subgroup.cartanHomeomorph (hstar : ∀ a ∈ G, star a ∈ G)
    (hexp : ∀ x : A, IsSelfAdjoint x → expUnit x ∈ G → ∀ t : ℝ, expUnit (t • x) ∈ G) :
    {u : unitary A // Unitary.toUnits u ∈ G} ×
        {x : selfAdjoint A // ∀ t : ℝ, expUnit (t • (x : A)) ∈ G} ≃ₜ G :=
  (Homeomorph.Set.prod {u : unitary A | Unitary.toUnits u ∈ G}
      {x : selfAdjoint A | ∀ t : ℝ, expUnit (t • (x : A)) ∈ G}).symm.trans <|
    (TauCeti.cartanHomeomorph A).subtype fun p ↦ (cartanHomeomorph_mem_iff hstar hexp p).symm

/-- The Cartan decomposition of a subgroup sends `(u, x)` to `u * exp x`. -/
@[simp]
theorem _root_.Subgroup.val_cartanHomeomorph_apply (hstar : ∀ a ∈ G, star a ∈ G)
    (hexp : ∀ x : A, IsSelfAdjoint x → expUnit x ∈ G → ∀ t : ℝ, expUnit (t • x) ∈ G)
    (p : {u : unitary A // Unitary.toUnits u ∈ G} ×
      {x : selfAdjoint A // ∀ t : ℝ, expUnit (t • (x : A)) ∈ G}) :
    ((G.cartanHomeomorph hstar hexp p : Aˣ) : A) =
      (p.1 : A) * exp ((p.2 : selfAdjoint A) : A) :=
  TauCeti.val_cartanHomeomorph_apply _

/-- The unitary factor of the Cartan decomposition of an element `a` of a subgroup is its polar
unitary factor. -/
@[simp]
theorem _root_.Subgroup.coe_cartanHomeomorph_symm_apply_fst (hstar : ∀ a ∈ G, star a ∈ G)
    (hexp : ∀ x : A, IsSelfAdjoint x → expUnit x ∈ G → ∀ t : ℝ, expUnit (t • x) ∈ G) (a : G) :
    (((G.cartanHomeomorph hstar hexp).symm a).1 : unitary A) = (a : Aˣ).polarUnitary :=
  (rfl)

/-- The self-adjoint factor of the Cartan decomposition of an element `a` of a subgroup is
`log √(a⋆ a)`. -/
@[simp]
theorem _root_.Subgroup.coe_cartanHomeomorph_symm_apply_snd (hstar : ∀ a ∈ G, star a ∈ G)
    (hexp : ∀ x : A, IsSelfAdjoint x → expUnit x ∈ G → ∀ t : ℝ, expUnit (t • x) ∈ G) (a : G) :
    ((((G.cartanHomeomorph hstar hexp).symm a).2 : selfAdjoint A) : A) =
      CFC.log (CFC.sqrt (star ((a : Aˣ) : A) * (a : Aˣ))) :=
  (rfl)

end Subgroup

end TauCeti

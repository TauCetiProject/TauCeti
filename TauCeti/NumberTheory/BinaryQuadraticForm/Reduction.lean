/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.NumberTheory.Modular
public import TauCeti.GroupTheory.GroupAction.Stabilizer
public import TauCeti.NumberTheory.BinaryQuadraticForm.Root
public import TauCeti.NumberTheory.HurwitzClassNumber
import TauCeti.Algebra.QuadraticDiscriminant
import TauCeti.Analysis.Complex.UpperHalfPlane.MoebiusAction
import TauCeti.Analysis.Complex.UpperHalfPlane.Rho
import TauCeti.NumberTheory.Modular.Stabilizer

/-!
# The Hurwitz class number counts classes of forms

For `D ≠ 0` the Hurwitz class number `TauCeti.hurwitzClassNumber D` is *defined* as a weighted
count of the reduced forms of discriminant `-D`. This file proves that it is the weighted count of
the `SL(2, ℤ)`-classes of positive definite integral binary quadratic forms of discriminant `-D`,
each class weighted by `2 / |Stab|`, where `Stab` is the stabiliser in `SL(2, ℤ)` of any form in
the class: `-1` acts trivially on forms, so `|Stab| / 2` is the order of the stabiliser in
`PSL(2, ℤ)`, and the weight is `1/2` on the classes of multiples of `x² + y²`, `1/3` on those of
multiples of `x² + x y + y²`, and `1` on all others.

The reduction theory is transported to the upper half-plane by the root map
`TauCeti.BinaryQuadraticForm.root`, which sends `f = a x² + b x y + c y²` to the root
`τ = (-b + i √D) / (2 a)` of `a τ² + b τ + c`, and which is injective and `SL(2, ℤ)`-equivariant.
Since `re τ = -b / (2 a)` and `|τ|² = c / a`, the conditions defining a reduced form say exactly
that `τ` lies in the part of the fundamental domain `𝒟` left of its boundary identifications: the
points of `𝒟` with `re τ < 1/2` which, on the unit circle, have `re τ ≤ 0`. Every orbit of
`SL(2, ℤ)` on `ℍ` meets that region in exactly one point
(`TauCeti.ModularGroup.exists_smul_mem_fd_left` and
`TauCeti.ModularGroup.orbit_mk_injOn_fd_left`), so every class of forms contains exactly one
reduced form. The stabiliser of a form is that of its root, and for a reduced form `f` the root `τ`
lies in `𝒟`: the stabiliser has order `4` when `τ = i`, that is for the forms `⟨a, 0, a⟩`, order
`6` when `τ = ρ`, that is for the forms `⟨a, a, a⟩`, and order `2` otherwise, the corner `ρ + 1`
of `𝒟` having real part `1/2`. So `2 / |Stab|` is the weight `TauCeti.reducedFormWeight` of the
reduced form in the class.

## Main results

* `TauCeti.BinaryQuadraticForm.isReducedForm_iff_root_mem`: a positive definite form is reduced
  exactly when its root lies in `𝒟`, has real part `< 1/2`, and has real part `≤ 0` if it lies on
  the unit circle.
* `TauCeti.BinaryQuadraticForm.root_eq_I_iff` and `TauCeti.BinaryQuadraticForm.root_eq_ρ_iff`: the
  forms with root `i` are the `⟨a, 0, a⟩`, those with root `ρ` the `⟨a, a, a⟩`.
* `TauCeti.BinaryQuadraticForm.reducedFormWeight_eq_two_div_card_stabilizer`: the weight of a
  reduced form is `2 / |Stab|`.
* `TauCeti.BinaryQuadraticForm.exists_smul_isReducedForm` and
  `TauCeti.BinaryQuadraticForm.orbit_mk_injOn_isReducedForm`: every class of positive definite
  forms of discriminant `-D` contains exactly one reduced form (Cohen, §5.3).
* `TauCeti.BinaryQuadraticForm.orbit_mk_reducedForms_bijective`: so the reduced forms of
  discriminant `-D` are in bijection with the classes, and there are finitely many classes
  (`TauCeti.BinaryQuadraticForm.finite_orbitRel_quotient_posDef`).
* `TauCeti.hurwitzClassNumber_eq_finsum`: for `D ≠ 0`, `H D` is the sum over the classes of
  `2 / |Stab|`.

## References

* H. Cohen, *A Course in Computational Algebraic Number Theory*, Graduate Texts in Mathematics
  138, Springer, 1993, §5.3.
* D. Zagier, *Zetafunktionen und quadratische Körper*, Springer, 1981, §8.
* A. Popa and D. Zagier, *An elementary proof of the Eichler–Selberg trace formula*,
  J. Reine Angew. Math. **762** (2020), 105–122, arXiv:1711.00327.
-/

public section

open MulAction UpperHalfPlane
open scoped MatrixGroups Modular

namespace TauCeti

namespace BinaryQuadraticForm

variable {D : ℕ} [NeZero D]

/-- The root `τ` of a positive definite form `a x² + b x y + c y²` has `|re τ| ≤ 1/2` exactly when
`|b| ≤ a`, as `re τ = -b / (2 a)`. -/
theorem abs_re_root_le_half_iff (f : posDef D) : |(root f).re| ≤ 1 / 2 ↔ |f.1.b| ≤ f.1.a := by
  have ha : (0 : ℝ) < 2 * f.1.a := by have := (mem_posDef.1 f.2).2; positivity
  rw [re_root, abs_div, abs_neg, abs_of_pos ha, div_le_iff₀ ha, one_div_mul_eq_div,
    mul_div_cancel_left₀ _ two_ne_zero]
  norm_cast

/-- The root `τ` of a positive definite form `a x² + b x y + c y²` has `re τ < 1/2` exactly when
`-a < b`. -/
theorem re_root_lt_half_iff (f : posDef D) : (root f).re < 1 / 2 ↔ -f.1.a < f.1.b := by
  have ha : (0 : ℝ) < 2 * f.1.a := by have := (mem_posDef.1 f.2).2; positivity
  rw [re_root, div_lt_iff₀ ha, one_div_mul_eq_div, mul_div_cancel_left₀ _ two_ne_zero, neg_lt]
  norm_cast

/-- The root `τ` of a positive definite form `a x² + b x y + c y²` has `re τ ≤ 0` exactly when
`0 ≤ b`. -/
theorem re_root_nonpos_iff (f : posDef D) : (root f).re ≤ 0 ↔ 0 ≤ f.1.b := by
  have ha : (0 : ℝ) < 2 * f.1.a := by have := (mem_posDef.1 f.2).2; positivity
  rw [re_root, div_le_iff₀ ha, zero_mul, neg_nonpos]
  norm_cast

/-- The root `τ` of a positive definite form `a x² + b x y + c y²` has `|τ|² ≥ 1` exactly when
`a ≤ c`, as `|τ|² = c / a`. -/
theorem one_le_normSq_root_iff (f : posDef D) : 1 ≤ Complex.normSq (root f) ↔ f.1.a ≤ f.1.c := by
  have ha : (0 : ℝ) < f.1.a := mod_cast (mem_posDef.1 f.2).2
  rw [normSq_root, one_le_div ha]
  norm_cast

/-- The root `τ` of a positive definite form `a x² + b x y + c y²` lies on the unit circle exactly
when `a = c`. -/
theorem norm_root_eq_one_iff (f : posDef D) : ‖(root f : ℂ)‖ = 1 ↔ f.1.a = f.1.c := by
  have ha : (0 : ℝ) < f.1.a := mod_cast (mem_posDef.1 f.2).2
  rw [Complex.norm_def, Real.sqrt_eq_one, normSq_root, div_eq_one_iff_eq ha.ne', eq_comm]
  norm_cast

/-- **A form is reduced exactly when its root is in the left part of `𝒟`**: the root
`τ = (-b + i √D) / (2 a)` of a positive definite form `a x² + b x y + c y²` lies in `𝒟`, has
`re τ < 1/2`, and has `re τ ≤ 0` if `|τ| = 1`. This is the region of
`TauCeti.ModularGroup.orbit_mk_injOn_fd_left` and `TauCeti.ModularGroup.exists_smul_mem_fd_left`:
`|b| ≤ a` is `|re τ| ≤ 1/2`, `a ≤ c` is `|τ| ≥ 1`, and the sign conditions of a reduced form rule
out the right vertical edge and the part of the unit arc right of `i`. -/
theorem isReducedForm_iff_root_mem (f : posDef D) :
    IsReducedForm f.1 ↔
      root f ∈ 𝒟 ∧ (root f).re < 1 / 2 ∧ (‖(root f : ℂ)‖ = 1 → (root f).re ≤ 0) := by
  simp only [isReducedForm_iff, ModularGroup.fd, Set.mem_ofPred_eq, one_le_normSq_root_iff,
    abs_re_root_le_half_iff, re_root_lt_half_iff, norm_root_eq_one_iff, re_root_nonpos_iff]
  grind [(mem_posDef.1 f.2).2]

/-- The root of a positive definite form is `i` exactly for the multiples `⟨a, 0, a⟩` of
`x² + y²`. -/
@[simp]
theorem root_eq_I_iff (f : posDef D) : root f = I ↔ f.1.b = 0 ∧ f.1.a = f.1.c := by
  -- `a i² + b i + c = b i + (c - a)`
  rw [eq_comm, eq_root_iff]
  convert ofReal_mul_add_eq_zero_iff I (m := f.1.b) (n := f.1.c - f.1.a) using 1
  · push_cast [coe_I, Complex.I_sq]
    ring_nf
  · norm_cast
    omega

/-- The root of a positive definite form is `ρ = (-1 + i √3) / 2` exactly for the multiples
`⟨a, a, a⟩` of `x² + x y + y²`. -/
@[simp]
theorem root_eq_ρ_iff (f : posDef D) : root f = ρ ↔ f.1.a = f.1.b ∧ f.1.b = f.1.c := by
  -- `a ρ² + b ρ + c = (b - a) (ρ + 1) + (c - b)`, as `ρ² = -ρ - 1`
  rw [eq_comm, eq_root_iff]
  convert ofReal_mul_add_eq_zero_iff ((1 : ℝ) +ᵥ ρ) (m := f.1.b - f.1.a) (n := f.1.c - f.1.b)
    using 1
  · push_cast [coe_vadd_one_ρ, ρ_sq]
    ring_nf
  · norm_cast
    omega

/-- **The weight of a reduced form is `2 / |Stab|`**, for its stabiliser in `SL(2, ℤ)`: `1/2` for
the forms `⟨a, 0, a⟩`, whose root is `i` and whose stabiliser has order `4`, `1/3` for the forms
`⟨a, a, a⟩`, whose root is `ρ` and whose stabiliser has order `6`, and `1` for every other reduced
form, whose stabiliser is `±1`. -/
theorem reducedFormWeight_eq_two_div_card_stabilizer (f : posDef D) (hf : IsReducedForm f.1) :
    reducedFormWeight f.1 = 2 / Nat.card (stabilizer SL(2, ℤ) f) := by
  obtain ⟨hfd, hre, -⟩ := (isReducedForm_iff_root_mem f).1 hf
  rw [← stabilizer_root, reducedFormWeight]
  split_ifs with hI hρ
  · rw [(root_eq_I_iff f).2 hI, ModularGroup.card_stabilizer_I]
    norm_num
  · rw [(root_eq_ρ_iff f).2 hρ, ModularGroup.card_stabilizer_ρ]
    norm_num
  · rw [ModularGroup.card_stabilizer_eq_two_of_orbit_ne_I_of_orbit_ne_ρ _ ?_ ?_]
    · norm_num
    · rwa [Ne, ModularGroup.orbit_mk_eq_I_iff hfd, root_eq_I_iff]
    · rw [Ne, ModularGroup.orbit_mk_eq_ρ_iff hfd, root_eq_ρ_iff, not_or]
      -- the corner `ρ + 1` has real part `1/2`
      exact ⟨hρ, fun h ↦ by norm_num [h] at hre⟩

/-- A reduced form of discriminant `-D` is positive definite. -/
theorem mem_posDef_of_mem_reducedForms {f : BinaryQuadraticForm ℤ} (hf : f ∈ reducedForms D) :
    f ∈ posDef D := by
  obtain ⟨hd, hr⟩ := (mem_reducedForms (NeZero.ne D)).1 hf
  exact mem_posDef.2 ⟨hd, pos_of_nonneg_of_discrim_lt_zero ((abs_nonneg _).trans hr.1) <|
    (discrim_def f).symm.trans_lt <| by simp [hd, NeZero.pos]⟩

/-- **Every class contains a reduced form**: for each positive definite form `f` there is
`γ ∈ SL(2, ℤ)` with `γ • f` reduced. -/
theorem exists_smul_isReducedForm (f : posDef D) : ∃ γ : SL(2, ℤ), IsReducedForm (γ • f).1 :=
  -- move the root of `f` into the left part of `𝒟`, and use that `root` is equivariant
  (ModularGroup.exists_smul_mem_fd_left (root f)).imp fun γ hγ ↦
    (isReducedForm_iff_root_mem _).2 <| by rwa [root_smul]

/-- **Every class contains at most one reduced form**: two reduced forms in the same
`SL(2, ℤ)`-class are equal. -/
theorem orbit_mk_injOn_isReducedForm :
    Set.InjOn (fun f : posDef D ↦ (Quotient.mk'' f : orbitRel.Quotient SL(2, ℤ) (posDef D)))
      {f | IsReducedForm f.1} := by
  intro f hf g hg h
  obtain ⟨γ, rfl⟩ := Quotient.exact' h
  -- the roots lie in the left part of `𝒟` and, as `root` is equivariant, in one orbit
  exact root_injective <| ModularGroup.orbit_mk_injOn_fd_left ((isReducedForm_iff_root_mem _).1 hf)
    ((isReducedForm_iff_root_mem _).1 hg) <| Quotient.sound' ⟨γ, (root_smul γ g).symm⟩

/-- **The reduced forms of discriminant `-D` represent the classes**: sending a reduced form to its
`SL(2, ℤ)`-class is a bijection from `reducedForms D` onto the classes of positive definite forms
of discriminant `-D` (Cohen, §5.3). -/
theorem orbit_mk_reducedForms_bijective :
    Function.Bijective fun f : reducedForms D ↦
      (Quotient.mk'' ⟨f, mem_posDef_of_mem_reducedForms f.2⟩ :
        orbitRel.Quotient SL(2, ℤ) (posDef D)) := by
  have hr (f : reducedForms D) : IsReducedForm f.1 := ((mem_reducedForms (NeZero.ne D)).1 f.2).2
  -- `by exact` defers the two memberships until `h` has fixed the forms: checked first, they make
  -- the unifier solve for the forms inside `IsReducedForm`, which is slow
  refine ⟨fun f g h ↦ Subtype.ext <| Subtype.mk.inj <|
    orbit_mk_injOn_isReducedForm (by exact hr f) (by exact hr g) h, Quotient.ind' fun f ↦ ?_⟩
  obtain ⟨γ, hγ⟩ := exists_smul_isReducedForm f
  exact ⟨⟨(γ • f).1, (mem_reducedForms (NeZero.ne D)).2 ⟨(mem_posDef.1 (γ • f).2).1, hγ⟩⟩,
    Quotient.sound' ⟨γ, rfl⟩⟩

/-- There are finitely many `SL(2, ℤ)`-classes of positive definite forms of discriminant `-D`. -/
instance finite_orbitRel_quotient_posDef : Finite (orbitRel.Quotient SL(2, ℤ) (posDef D)) :=
  -- the finitely many reduced forms represent them all
  .of_surjective _ orbit_mk_reducedForms_bijective.2

end BinaryQuadraticForm

open BinaryQuadraticForm

/-- **The Hurwitz class number counts classes of forms**: for `D ≠ 0`, `H D` is the number of
`SL(2, ℤ)`-classes of positive definite integral binary quadratic forms of discriminant `-D`, each
class counted with weight `2 / |Stab|` for the stabiliser in `SL(2, ℤ)` of any of its forms. That
weight is `1/2` on the classes of multiples of `x² + y²`, `1/3` on those of multiples of
`x² + x y + y²`, and `1` on all others. The sum is finite
(`TauCeti.BinaryQuadraticForm.finite_orbitRel_quotient_posDef`). -/
theorem hurwitzClassNumber_eq_finsum (D : ℕ) [NeZero D] :
    hurwitzClassNumber D =
      ∑ᶠ q : orbitRel.Quotient SL(2, ℤ) (posDef D), 2 / (cardStabilizerOnOrbit q : ℚ) := by
  rw [hurwitzClassNumber_of_ne_zero (NeZero.ne D), ← Finset.sum_coe_sort,
    ← finsum_eq_sum_of_fintype]
  refine finsum_eq_of_bijective _ orbit_mk_reducedForms_bijective fun f ↦ ?_
  rw [cardStabilizerOnOrbit_mk]
  exact reducedFormWeight_eq_two_div_card_stabilizer ⟨f, mem_posDef_of_mem_reducedForms f.2⟩
    ((mem_reducedForms (NeZero.ne D)).1 f.2).2

end TauCeti

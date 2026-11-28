/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.PeriodPair
public import TauCeti.Algebra.QuadraticAlgebra.UnitMatrix
import TauCeti.NumberTheory.BinaryQuadraticForm.Root

/-!
# Multipliers of a principal quadratic period lattice

If `τ ∈ ℍ` satisfies `τ² + Bτ + C = 0` with integral coefficients, the lattice
`ℤ τ + ℤ` is a subalgebra of `ℂ`. It is exactly the ring of complex scalars preserving that
lattice, and evaluation at `τ` identifies it with `QuadraticAlgebra ℤ (-C) (-B)`.
More generally, for any `τ ∈ ℍ` the left order of `ℤ τ + ℤ` is strictly larger than `ℤ` (`⊥`) if
and only if `τ` satisfies an integral quadratic equation `a τ² + b τ + c = 0` with `a > 0`
(`UpperHalfPlane.leftOrder_lattice_periodPair_ne_bot_iff`); when `(a, b, c)` generate the unit
ideal of `ℤ`, the left order is `ℤ + ℤ(a τ) = ℤ[a τ]`.
The Möbius transformations of `SL(2, ℤ)` fixing such a monic quadratic point are exactly the
multiplication matrices of the units of `QuadraticAlgebra ℤ (-C) (-B)`
(`UpperHalfPlane.stabilizer_eq_range_periodUnitSLMatrix`), so the stabilizer of `τ` is isomorphic
to that unit group (`UpperHalfPlane.unitsMulEquivStabilizer`).
These are scalar endomorphisms of the lattice; no algebraic elliptic-curve comparison is asserted.

The multiplication matrix uses row coordinates in the ordered periods `(τ, 1)`, as for division
points of a complex torus. Thus multiplication by `t + sτ` sends a row `r` to
`r * !![t - B*s, -C*s; s, t]`. The construction reuses the native regular representation of
`QuadraticAlgebra`, reversing its basis `(1, ω)` and transposing to the row convention.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, Chapter 11, for the lattice description of complex
  multiplication.
* J. H. Silverman, *The Arithmetic of Elliptic Curves*, 2nd ed., Graduate Texts in Mathematics
  106, Springer, 2009, Theorem VI.6.1.
* D. H. Shin, *Generation of class fields by Siegel-Ramachandra invariants*, §2, for the
  multiplication matrices in the row-coordinate convention.
-/

public section

noncomputable section

open Complex Matrix
open scoped MatrixGroups

namespace UpperHalfPlane

variable (τ : ℍ) {B C : ℤ}

/-- The lattice of a monic integral quadratic point is closed under multiplication. -/
theorem mul_mem_lattice_periodPair_of_quadratic
    (hτ : (τ : ℂ) ^ 2 + B * τ + C = 0) {x y : ℂ}
    (hx : x ∈ τ.periodPair.lattice) (hy : y ∈ τ.periodPair.lattice) :
    x * y ∈ τ.periodPair.lattice := by
  obtain ⟨m, n, rfl⟩ := PeriodPair.mem_lattice.mp hx
  obtain ⟨p, q, rfl⟩ := PeriodPair.mem_lattice.mp hy
  refine PeriodPair.mem_lattice.mpr ⟨m * q + n * p - B * m * p, n * q - C * m * p, ?_⟩
  simp only [periodPair_ω₁, periodPair_ω₂, mul_one]
  push_cast
  linear_combination -(m : ℂ) * p * hτ

/-- The integral quadratic order carried by the principal lattice `ℤ τ + ℤ`. -/
def quadraticOrder (hτ : (τ : ℂ) ^ 2 + B * τ + C = 0) : Subalgebra ℤ ℂ :=
  τ.periodPair.lattice.toSubalgebra (by simpa using τ.periodPair.ω₂_mem_lattice)
    (fun _ _ hx hy ↦ τ.mul_mem_lattice_periodPair_of_quadratic hτ hx hy)

/-- Membership in the quadratic order is membership in the original period lattice. -/
@[simp]
theorem mem_quadraticOrder (hτ : (τ : ℂ) ^ 2 + B * τ + C = 0) (x : ℂ) :
    x ∈ τ.quadraticOrder hτ ↔ x ∈ τ.periodPair.lattice := Iff.rfl

/-- The quadratic order is precisely the complex scalars preserving the period lattice. -/
theorem mem_quadraticOrder_iff_mul_mem (hτ : (τ : ℂ) ^ 2 + B * τ + C = 0) (x : ℂ) :
    x ∈ τ.quadraticOrder hτ ↔ ∀ y ∈ τ.periodPair.lattice, x * y ∈ τ.periodPair.lattice := by
  constructor
  · intro hx y hy
    exact τ.mul_mem_lattice_periodPair_of_quadratic hτ hx hy
  · intro hx
    simpa using hx 1 (by simpa using τ.periodPair.ω₂_mem_lattice)

/-- Evaluation at `τ` identifies its quadratic algebra with its integral period order. -/
def quadraticOrderEquiv (hτ : (τ : ℂ) ^ 2 + B * τ + C = 0) :
    QuadraticAlgebra ℤ (-C) (-B) ≃ₐ[ℤ] τ.quadraticOrder hτ := by
  let u : τ.quadraticOrder hτ := ⟨τ, by simpa using τ.periodPair.ω₁_mem_lattice⟩
  let f : QuadraticAlgebra ℤ (-C) (-B) →ₐ[ℤ] τ.quadraticOrder hτ :=
    QuadraticAlgebra.lift ⟨u, by
      apply Subtype.ext
      simp [u, zsmul_eq_mul]
      linear_combination hτ⟩
  refine AlgEquiv.ofBijective f ⟨?_, ?_⟩
  · apply (QuadraticAlgebra.lift_injective_iff _).mpr
    apply LinearIndependent.of_comp (τ.quadraticOrder hτ).val.toLinearMap
    have hi := (LinearIndependent.pair_symm_iff).mpr (τ.periodPair.indep.restrict_scalars' ℤ)
    convert hi using 1
    ext i
    fin_cases i <;> simp [u]
  · intro x
    obtain ⟨s, t, hst⟩ := PeriodPair.mem_lattice.mp x.property
    refine ⟨⟨t, s⟩, Subtype.ext ?_⟩
    simpa [f, u, QuadraticAlgebra.lift_apply_apply, add_comm] using hst

/-- Evaluation is `t + sτ` in the native coordinates `(t,s)` of the quadratic algebra. -/
@[simp↓]
theorem coe_quadraticOrderEquiv (hτ : (τ : ℂ) ^ 2 + B * τ + C = 0)
    (z : QuadraticAlgebra ℤ (-C) (-B)) :
    (τ.quadraticOrderEquiv hτ z : ℂ) = z.re + z.im * τ := by
  dsimp only [quadraticOrderEquiv, AlgEquiv.ofBijective, RingEquiv.ofBijective]
  simp [QuadraticAlgebra.lift_apply_apply]

/-- The inverse coordinates recover the unique expression `t + sτ`. -/
theorem quadraticOrderEquiv_symm_apply_eq_iff (hτ : (τ : ℂ) ^ 2 + B * τ + C = 0)
    (x : τ.quadraticOrder hτ) (z : QuadraticAlgebra ℤ (-C) (-B)) :
    (τ.quadraticOrderEquiv hτ).symm x = z ↔ (x : ℂ) = z.re + z.im * τ := by
  rw [AlgEquiv.symm_apply_eq]
  exact Subtype.ext_iff.trans (by rw [coe_quadraticOrderEquiv])

/-- Multiplication acts on row coordinates of division points on the right by the period matrix.
The identity is valid for every complex denominator, including its totalized zero value. -/
theorem quadraticOrderEquiv_mul_divisionPoint
    (hτ : (τ : ℂ) ^ 2 + B * τ + C = 0) (z : QuadraticAlgebra ℤ (-C) (-B))
    (r : Fin 2 → ℤ) (N : ℂ) :
    (τ.quadraticOrderEquiv hτ z : ℂ) * (((r 0 : ℂ) * τ + r 1) / N) =
      ((((r ᵥ* z.periodMulMatrix) 0 : ℂ) * τ + (r ᵥ* z.periodMulMatrix) 1) / N) := by
  rw [coe_quadraticOrderEquiv, QuadraticAlgebra.periodMulMatrix_eq, ← mul_div_assoc]
  congr 1
  simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  linear_combination (z.im : ℂ) * r 0 * hτ

section Stabilizer

/-- A monic integral quadratic point of `ℍ` has negative discriminant `B² - 4C`, the
discriminant of `QuadraticAlgebra ℤ (-C) (-B)`; this is the monic case of
`TauCeti.BinaryQuadraticForm.discrim_neg_of_quadratic_upperHalfPlane`. -/
theorem discr_lt_zero_of_quadratic (hτ : (τ : ℂ) ^ 2 + B * τ + C = 0) :
    QuadraticAlgebra.discr (-C) (-B) < 0 := by
  have h := TauCeti.BinaryQuadraticForm.discrim_neg_of_quadratic_upperHalfPlane one_ne_zero
    (by simpa using hτ)
  rw [QuadraticAlgebra.discr_def]
  simp only [TauCeti.BinaryQuadraticForm.discrim, discrim] at h
  linarith

/-- The multiplication matrix of a unit of `ℤ[τ]` fixes `τ`. -/
theorem periodUnitSLMatrix_smul (hτ : (τ : ℂ) ^ 2 + B * τ + C = 0)
    (u : (QuadraticAlgebra ℤ (-C) (-B))ˣ) :
    QuadraticAlgebra.periodUnitSLMatrix (τ.discr_lt_zero_of_quadratic hτ).le u • τ = τ := by
  ext1
  rw [coe_specialLinearGroup_apply]
  have hden := denom_ne_zero (QuadraticAlgebra.periodUnitSLMatrix
    (τ.discr_lt_zero_of_quadratic hτ).le u) τ
  rw [div_eq_iff (by simpa [denom] using hden)]
  simp [QuadraticAlgebra.periodMulMatrix_eq]
  linear_combination -((u : QuadraticAlgebra ℤ (-C) (-B)).im : ℂ) * hτ

/-- **The stabilizer of a monic quadratic point**: `γ ∈ SL(2, ℤ)` fixes `τ` if and only if it is
the multiplication matrix of a unit of `ℤ[τ] ≅ QuadraticAlgebra ℤ (-C) (-B)`. -/
theorem mem_stabilizer_iff_exists_periodUnitSLMatrix_eq (hτ : (τ : ℂ) ^ 2 + B * τ + C = 0)
    {γ : SL(2, ℤ)} :
    γ ∈ MulAction.stabilizer SL(2, ℤ) τ ↔
      ∃ u, QuadraticAlgebra.periodUnitSLMatrix (τ.discr_lt_zero_of_quadratic hτ).le u = γ := by
  refine ⟨fun hγ ↦ ?_, ?_⟩
  · have h := congrArg (fun z : ℍ ↦ (z : ℂ)) (MulAction.mem_stabilizer_iff.mp hγ)
    simp only [coe_specialLinearGroup_apply] at h
    rw [div_eq_iff (by simpa [denom] using denom_ne_zero γ τ)] at h
    -- `γ = !![p, q; r, s]` fixes `τ` iff `rτ² + (s - p)τ - q = 0`; reducing with the monic
    -- relation of `τ` and comparing coefficients of `τ` and `1` gives `p = s - Br`, `q = -Cr`.
    have hlin : ((γ 1 1 - γ 0 0 - B * γ 1 0 : ℤ) : ℂ) * τ + ((-γ 0 1 - C * γ 1 0 : ℤ) : ℂ) = 0 := by
      push_cast
      linear_combination -h - (γ 1 0 : ℂ) * hτ
    obtain ⟨h₁, h₂⟩ := intCast_mul_add_intCast_eq_zero_iff.mp hlin
    let z : QuadraticAlgebra ℤ (-C) (-B) := ⟨γ 1 1, γ 1 0⟩
    have hz : z.periodMulMatrix = (γ : Matrix (Fin 2) (Fin 2) ℤ) := by
      rw [QuadraticAlgebra.periodMulMatrix_eq]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [z] <;> linarith
    have hu : IsUnit z := (QuadraticAlgebra.isUnit_periodMulMatrix_iff z).mp
      (Matrix.isUnit_iff_isUnit_det _ |>.mpr (by rw [hz, γ.det_coe]; exact isUnit_one))
    exact ⟨hu.unit,
      Subtype.ext (by rw [QuadraticAlgebra.coe_periodUnitSLMatrix, IsUnit.unit_spec, hz])⟩
  · rintro ⟨u, rfl⟩
    exact τ.periodUnitSLMatrix_smul hτ u

/-- The stabilizer of a monic quadratic point in `SL(2, ℤ)` is the image of the units of
`QuadraticAlgebra ℤ (-C) (-B)` under their multiplication matrices. -/
theorem stabilizer_eq_range_periodUnitSLMatrix (hτ : (τ : ℂ) ^ 2 + B * τ + C = 0) :
    MulAction.stabilizer SL(2, ℤ) τ =
      (QuadraticAlgebra.periodUnitSLMatrix (τ.discr_lt_zero_of_quadratic hτ).le).range :=
  Subgroup.ext fun _ ↦ τ.mem_stabilizer_iff_exists_periodUnitSLMatrix_eq hτ

/-- The units of `QuadraticAlgebra ℤ (-C) (-B)` are isomorphic to the stabilizer of `τ` in
`SL(2, ℤ)`, a unit going to its multiplication matrix. -/
def unitsMulEquivStabilizer (hτ : (τ : ℂ) ^ 2 + B * τ + C = 0) :
    (QuadraticAlgebra ℤ (-C) (-B))ˣ ≃* MulAction.stabilizer SL(2, ℤ) τ :=
  (MonoidHom.ofInjective (QuadraticAlgebra.periodUnitSLMatrix_injective _)).trans
    (MulEquiv.subgroupCongr (τ.stabilizer_eq_range_periodUnitSLMatrix hτ).symm)

/-- `unitsMulEquivStabilizer` sends a unit to its multiplication matrix. -/
@[simp]
theorem coe_unitsMulEquivStabilizer (hτ : (τ : ℂ) ^ 2 + B * τ + C = 0)
    (u : (QuadraticAlgebra ℤ (-C) (-B))ˣ) :
    (τ.unitsMulEquivStabilizer hτ u : SL(2, ℤ)) =
      QuadraticAlgebra.periodUnitSLMatrix (τ.discr_lt_zero_of_quadratic hτ).le u :=
  (rfl)

/-- The stabilizer of a monic quadratic point in `SL(2, ℤ)` has as many elements as the unit
group of `QuadraticAlgebra ℤ (-C) (-B)`. -/
theorem natCard_stabilizer_eq_natCard_units (hτ : (τ : ℂ) ^ 2 + B * τ + C = 0) :
    Nat.card (MulAction.stabilizer SL(2, ℤ) τ) = Nat.card (QuadraticAlgebra ℤ (-C) (-B))ˣ :=
  (Nat.card_congr (τ.unitsMulEquivStabilizer hτ).toEquiv).symm

end Stabilizer

section LeftOrder

/-- If `(a : ℂ) * τ² + b * τ + c = 0` for integers `a, b, c`, then `(a : ℂ) * τ` preserves the
lattice `ℤ τ + ℤ`. -/
theorem intCast_mul_mem_leftOrder_lattice_periodPair_of_quadratic {τ : ℍ} {a b c : ℤ}
    (hrel : (a : ℂ) * (τ : ℂ) ^ 2 + b * (τ : ℂ) + c = 0) :
    (a : ℂ) * (τ : ℂ) ∈ τ.periodPair.lattice.leftOrder := by
  rw [mem_leftOrder_lattice_periodPair_iff]
  refine ⟨by simpa using intCast_mul_add_intCast_mem_lattice_periodPair τ a 0, ?_⟩
  have hmul : (a : ℂ) * (τ : ℂ) * (τ : ℂ) = ((-b : ℤ) : ℂ) * (τ : ℂ) + (-c : ℤ) := by
    push_cast; linear_combination hrel
  exact hmul ▸ intCast_mul_add_intCast_mem_lattice_periodPair τ (-b) (-c)

/-- **Complex multiplication dichotomy for `ℤ τ + ℤ`** (Silverman, *AEC*, Theorem VI.6.1):
the multiplier order of `ℤ τ + ℤ` is strictly larger than `ℤ` if and only if `τ` satisfies an
integral quadratic equation `a τ² + b τ + c = 0` with `a > 0`. -/
theorem leftOrder_lattice_periodPair_ne_bot_iff {τ : ℍ} :
    τ.periodPair.lattice.leftOrder ≠ ⊥ ↔
      ∃ a b c : ℤ, 0 < a ∧ (a : ℂ) * (τ : ℂ) ^ 2 + b * (τ : ℂ) + c = 0 := by
  constructor
  · intro hne
    obtain ⟨x, hx, hxbot⟩ := IsConcreteLE.not_le_iff_exists.mp fun hle ↦
      hne (le_antisymm hle bot_le)
    obtain ⟨hx₁, hxτ⟩ := mem_leftOrder_lattice_periodPair_iff.mp hx
    obtain ⟨s, t, rfl⟩ := PeriodPair.mem_lattice.mp hx₁
    obtain ⟨p, q, hpq⟩ := PeriodPair.mem_lattice.mp hxτ
    simp only [periodPair_ω₁, periodPair_ω₂, mul_one] at hpq hxbot ⊢
    have hs : s ≠ 0 := fun hs0 ↦ hxbot (Algebra.mem_bot.mpr ⟨t, by simp [hs0]⟩)
    rcases lt_or_gt_of_ne hs with hneg | hpos
    · exact ⟨-s, p - t, q, neg_pos.mpr hneg, by push_cast; linear_combination hpq⟩
    · exact ⟨s, t - p, -q, hpos, by push_cast; linear_combination -hpq⟩
  · rintro ⟨a, b, c, ha, hrel⟩ hbot
    obtain ⟨m, hm⟩ := Algebra.mem_bot.mp
      (hbot ▸ intCast_mul_mem_leftOrder_lattice_periodPair_of_quadratic hrel)
    have him := congrArg Complex.im hm
    simp only [Algebra.algebraMap_eq_smul_one, zsmul_one, intCast_im, mul_im, intCast_re,
      zero_mul, add_zero, coe_im] at him
    exact (mul_pos (Int.cast_pos.mpr ha) τ.im_pos).ne him

/-- The multiplier order of `ℤ τ + ℤ` is `ℤ` (`⊥`) if and only if `τ` satisfies no nontrivial
integral quadratic equation. -/
theorem leftOrder_lattice_periodPair_eq_bot_iff {τ : ℍ} :
    τ.periodPair.lattice.leftOrder = ⊥ ↔
      ∀ a b c : ℤ, 0 < a → (a : ℂ) * (τ : ℂ) ^ 2 + b * (τ : ℂ) + c ≠ 0 := by
  rw [← not_iff_not, ← ne_eq, leftOrder_lattice_periodPair_ne_bot_iff]; push Not; rfl

/-- **Exact multiplier order of an imaginary quadratic lattice**: if `τ ∈ ℍ` satisfies an integral
quadratic relation `a τ² + b τ + c = 0` whose coefficients `(a, b, c)` generate the unit ideal of
`ℤ`, then the multipliers of `ℤ τ + ℤ` are precisely the integral combinations `m + k (a τ)`. -/
theorem mem_leftOrder_lattice_periodPair_iff_of_quadratic_of_linearCombination_eq_one
    {τ : ℍ} {a b c : ℤ} (hrel : (a : ℂ) * (τ : ℂ) ^ 2 + b * (τ : ℂ) + c = 0)
    (hprim : ∃ u v w : ℤ, u * a + v * b + w * c = 1) {x : ℂ} :
    x ∈ τ.periodPair.lattice.leftOrder ↔ ∃ m k : ℤ, x = m + k * ((a : ℂ) * (τ : ℂ)) := by
  constructor
  · intro hx
    obtain ⟨u, v, w, huvw⟩ := hprim
    obtain ⟨hx₁, hxτ⟩ := mem_leftOrder_lattice_periodPair_iff.mp hx
    obtain ⟨s, t, rfl⟩ := PeriodPair.mem_lattice.mp hx₁
    obtain ⟨p, q, hpq⟩ := PeriodPair.mem_lattice.mp hxτ
    simp only [periodPair_ω₁, periodPair_ω₂, mul_one] at hpq ⊢
    -- Comparing coefficients of `τ` and `1` in `a (x τ - (s τ + t) τ) + s (a τ² + b τ + c) = 0`.
    have hlin : ((a * p - a * t + s * b : ℤ) : ℂ) * (τ : ℂ) + ((a * q + s * c : ℤ) : ℂ) = 0 := by
      push_cast; linear_combination (a : ℂ) * hpq + s * hrel
    obtain ⟨h₁, h₂⟩ := intCast_mul_add_intCast_eq_zero_iff.mp hlin
    set k : ℤ := u * s + v * (t - p) - w * q
    have hs : (s : ℂ) = (k : ℂ) * a := by
      have hsz : s = k * a := by linear_combination -s * huvw + v * h₁ + w * h₂
      exact_mod_cast hsz
    exact ⟨t, k, by rw [hs]; ring⟩
  · rintro ⟨m, k, rfl⟩
    have hθ := intCast_mul_mem_leftOrder_lattice_periodPair_of_quadratic hrel
    simpa [zsmul_eq_mul] using add_mem (τ.periodPair.lattice.leftOrder.algebraMap_mem m)
      (τ.periodPair.lattice.leftOrder.smul_mem hθ k)

/-- If `τ ∈ ℍ` satisfies a primitive integral quadratic relation `a τ² + b τ + c = 0`, then the
left order of `ℤ τ + ℤ` is `ℤ[a τ]`. -/
theorem leftOrder_lattice_periodPair_eq_adjoin_of_quadratic_of_linearCombination_eq_one
    {τ : ℍ} {a b c : ℤ} (hrel : (a : ℂ) * (τ : ℂ) ^ 2 + b * (τ : ℂ) + c = 0)
    (hprim : ∃ u v w : ℤ, u * a + v * b + w * c = 1) :
    τ.periodPair.lattice.leftOrder = Algebra.adjoin ℤ {(a : ℂ) * (τ : ℂ)} := by
  refine le_antisymm (fun x hx ↦ ?_) (Algebra.adjoin_le (Set.singleton_subset_iff.mpr
    (intCast_mul_mem_leftOrder_lattice_periodPair_of_quadratic hrel)))
  obtain ⟨m, k, rfl⟩ :=
    (mem_leftOrder_lattice_periodPair_iff_of_quadratic_of_linearCombination_eq_one
      hrel hprim).mp hx
  set S := Algebra.adjoin ℤ {(a : ℂ) * (τ : ℂ)}
  simpa [zsmul_eq_mul] using add_mem (S.algebraMap_mem m)
    (S.smul_mem (Algebra.subset_adjoin (Set.mem_singleton _)) k)

/-- For a monic quadratic point `τ² + B τ + C = 0`, the left order of `ℤ τ + ℤ` agrees with
`UpperHalfPlane.quadraticOrder`. -/
theorem leftOrder_lattice_periodPair_eq_quadraticOrder {τ : ℍ} {B C : ℤ}
    (hτ : (τ : ℂ) ^ 2 + B * τ + C = 0) : τ.periodPair.lattice.leftOrder = τ.quadraticOrder hτ :=
  Subalgebra.ext fun x ↦ Submodule.mem_leftOrder_iff.trans
    (τ.mem_quadraticOrder_iff_mul_mem hτ x).symm

end LeftOrder

end UpperHalfPlane

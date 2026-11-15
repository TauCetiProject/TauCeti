/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.IntermediateField.LinearDisjoint
public import TauCeti.NumberTheory.ModularForms.QExpansion.FunctionField

/-!
# Descent of linear relations to the coefficient field

Let `X` be the compactified quotient of a discrete subgroup of `PSL(2, ℝ)`, let `D` be a cusp
datum and let `K` be a subfield of `ℂ`. The meromorphic functions on `X` whose Laurent
`q`-expansion at `D` has all its coefficients in `K` form the subfield
`Subgroup.CompactifiedQuotient.coeffSubfield D K` of the function field `M(X)`. This file proves
the rationality comparison between this subfield and the complex constants: **`coeffSubfield D K`
and `ℂ` are linearly disjoint over `K`** inside `M(X)`. Equivalently, functions with coefficients
in `K` that are linearly independent over `K` stay linearly independent over `ℂ`, so that
`ℂ ⊗[K] coeffSubfield D K → M(X)` is injective.

The proof descends linear relations coefficientwise. If `∑ cᵢ Fᵢ = 0` with `cᵢ ∈ ℂ` and every `Fᵢ`
has its coefficients in `K`, then applying a `K`-linear functional `φ : ℂ → K` to every coefficient
of the expansion of `∑ cᵢ Fᵢ` gives the expansion of `∑ φ(cᵢ) Fᵢ`, since
`φ (cᵢ aᵢ) = aᵢ φ (cᵢ)` for `aᵢ ∈ K`. By the `q`-expansion principle `∑ φ(cᵢ) Fᵢ = 0`, and since
the functionals `φ` separate the points of `ℂ`, a relation over `ℂ` among functions linearly
independent over `K` is trivial.

For the principal congruence subgroup `Γ(N)`, its cusp `∞` and `K = ℚ(ζ_N)`, this compares the
field `F_N` of modular functions of level `N` with coefficients in `ℚ(ζ_N)` with the full function
field of `X(N)`. Together with
`IntermediateField.LinearDisjoint.lift_rank_le_lift_rank_adjoin_algebraMap`, applied to the field
`C = ℚ(ζ_N)(j)`, it bounds the degree of `F_N` over `ℚ(ζ_N)(j)` by the degree of the function field
of `X(N)` over `ℂ(j)`. This is the degree comparison by which `F_N` is identified with the field
generated over `ℚ(ζ_N)(j)` by explicit modular functions.

## Main declarations

* `Subgroup.CompactifiedQuotient.coeffIntermediateField`: the subfield `coeffSubfield D K` as an
  intermediate field of `M(X) / K`.
* `Subgroup.CompactifiedQuotient.sum_apply_smul_eq_zero_of_mem_coeffSubfield`: a linear relation
  over `ℂ` among functions with coefficients in `K` descends along every `K`-linear functional
  `ℂ → K`.
* `Subgroup.CompactifiedQuotient.linearDisjoint_coeffIntermediateField`: `coeffSubfield D K` and
  `ℂ` are linearly disjoint over `K`.
* `Subgroup.CompactifiedQuotient.linearDisjoint_fieldRange_coeffIntermediateField`: the same, in
  the form taken by the lemmas on linearly disjoint extensions of constants.
* `Subgroup.CompactifiedQuotient.linearIndependent_of_mem_coeffSubfield`: functions with
  coefficients in `K` that are linearly independent over `K` are linearly independent over `ℂ`.

## References

* Goro Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, Princeton
  University Press, 1971, §6.1 (the linear disjointness of the field of modular functions with
  coefficients in a subfield of `ℂ` from `ℂ`).
-/

public noncomputable section

open TauCeti.RiemannSurface
open scoped MatrixGroups

namespace Subgroup.CompactifiedQuotient

variable {Γ : Subgroup PSL(2, ℝ)} [DiscreteTopology Γ] (D : Γ.CuspDatum) (K : Subfield ℂ)

/-- The meromorphic functions on the compactified quotient whose Laurent `q`-expansion at `D` has
all its coefficients in the subfield `K` of `ℂ`, as an intermediate field of the function field
over `K`. Its underlying subfield is `Subgroup.CompactifiedQuotient.coeffSubfield D K`. -/
def coeffIntermediateField : IntermediateField K (MeromorphicFunction Γ.CompactifiedQuotient) :=
  (coeffSubfield D K).toIntermediateField fun c ↦ (algebraMap_mem_coeffSubfield D).mpr c.2

variable {D K}

/-- A meromorphic function lies in `coeffIntermediateField D K` exactly when it lies in
`coeffSubfield D K`. -/
@[simp]
theorem mem_coeffIntermediateField {F : MeromorphicFunction Γ.CompactifiedQuotient} :
    F ∈ coeffIntermediateField D K ↔ F ∈ coeffSubfield D K :=
  Iff.rfl

variable (D K) in
/-- The underlying subfield of `coeffIntermediateField D K` is `coeffSubfield D K`. -/
@[simp]
theorem toSubfield_coeffIntermediateField :
    (coeffIntermediateField D K).toSubfield = coeffSubfield D K :=
  Subfield.ext fun _ ↦ mem_coeffIntermediateField

/-- **Descent of linear relations along functionals.** Let `F` be a family of meromorphic
functions whose Laurent `q`-expansions at `D` have their coefficients in `K`. If `∑ cᵢ Fᵢ = 0`
with complex coefficients `cᵢ`, then `∑ φ(cᵢ) Fᵢ = 0` for every `K`-linear map `φ : ℂ → K`. -/
theorem sum_apply_smul_eq_zero_of_mem_coeffSubfield {ι : Type*} (s : Finset ι)
    {F : ι → MeromorphicFunction Γ.CompactifiedQuotient} (hF : ∀ i, F i ∈ coeffSubfield D K)
    {c : ι → ℂ} (hc : ∑ i ∈ s, c i • F i = 0) (φ : ℂ →ₗ[K] K) :
    ∑ i ∈ s, φ (c i) • F i = 0 := by
  -- the coefficients of the expansions of the `Fᵢ`, as elements of `K`
  let a (i : ι) (n : ℤ) : K :=
    ⟨(laurentQExpansion D (F i)).coeff n, (mem_coeffSubfield D).mp (hF i) n⟩
  have hexp (x : ι → ℂ) (n : ℤ) :
      (laurentQExpansion D (∑ i ∈ s, x i • F i)).coeff n = ∑ i ∈ s, x i * a i n := by
    simp only [map_sum, HahnSeries.coeff_sum, a, Algebra.smul_def, map_mul, AlgHom.commutes,
      LaurentSeries.algebraMap_apply, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul,
      Algebra.algebraMap_self, RingHom.id_apply]
  -- `φ (cᵢ) aᵢ = φ (cᵢ aᵢ)`, since `φ` is `K`-linear
  have hφ (n : ℤ) : ∑ i ∈ s, φ (c i) * a i n = φ (∑ i ∈ s, c i * a i n) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [mul_comm (c i), ← smul_eq_mul (a i n : ℂ), ← Subfield.smul_def, φ.map_smul, smul_eq_mul,
      mul_comm]
  refine laurentQExpansion_injective D ?_
  ext n
  have h := congrArg (fun G ↦ (laurentQExpansion D G).coeff n) hc
  simp only [hexp, map_zero, HahnSeries.coeff_zero] at h
  rw [Finset.sum_congr rfl fun i _ ↦ Subfield.smul_def (φ (c i)) (F i), hexp, map_zero,
    HahnSeries.coeff_zero]
  exact_mod_cast (hφ n).trans (by rw [h, map_zero])

/-- **Linear disjointness from the constants.** The meromorphic functions whose Laurent
`q`-expansions at `D` have their coefficients in `K` and the complex constants are linearly
disjoint over `K` inside the function field of the compactified quotient. -/
theorem linearDisjoint_coeffIntermediateField : (coeffIntermediateField D K).LinearDisjoint ℂ := by
  let a := Module.Basis.ofVectorSpace K (coeffIntermediateField D K)
  refine .of_basis_left a (linearIndependent_iff'.mpr fun s c hc i hi ↦ ?_)
  refine (Module.forall_dual_apply_eq_zero_iff K (c i)).mp fun φ ↦ ?_
  have h := sum_apply_smul_eq_zero_of_mem_coeffSubfield s (fun j ↦ (a j).2) hc φ
  exact linearIndependent_iff'.mp a.linearIndependent s (φ ∘ c)
    (Subtype.ext (by simpa using h)) i hi

/-- **Linear disjointness from the constants**, in the form taken by the lemmas on linearly
disjoint extensions of constants: the image of `ℂ` in the function field and the functions whose
Laurent `q`-expansions at `D` have their coefficients in `K` are linearly disjoint over `K`. With
`IntermediateField.LinearDisjoint.lift_rank_le_lift_rank_adjoin_algebraMap` this bounds the degree
of these functions over a field `C` between `K` and them by the degree of the function field over
the field generated by `ℂ` and `C`. -/
theorem linearDisjoint_fieldRange_coeffIntermediateField :
    IntermediateField.LinearDisjoint
      (IsScalarTower.toAlgHom K ℂ (MeromorphicFunction Γ.CompactifiedQuotient)).fieldRange
      (coeffIntermediateField D K) := by
  refine .symm' ?_
  have h : (IsScalarTower.toAlgHom K (coeffIntermediateField D K) _).fieldRange =
      coeffIntermediateField D K := by
    ext F
    simp [AlgHom.mem_fieldRange]
  rw [h]
  exact linearDisjoint_coeffIntermediateField

/-- **Linear independence over `ℂ`.** Meromorphic functions whose Laurent `q`-expansions at `D`
have their coefficients in `K` and that are linearly independent over `K` are linearly independent
over `ℂ`. -/
theorem linearIndependent_of_mem_coeffSubfield {ι : Type*}
    {F : ι → MeromorphicFunction Γ.CompactifiedQuotient} (hF : ∀ i, F i ∈ coeffSubfield D K)
    (hli : LinearIndependent K F) : LinearIndependent ℂ F :=
  linearDisjoint_coeffIntermediateField.linearIndependent_left
    (a := fun i ↦ (⟨F i, hF i⟩ : coeffIntermediateField D K))
    (.of_comp (coeffIntermediateField D K).val.toLinearMap hli)

end Subgroup.CompactifiedQuotient

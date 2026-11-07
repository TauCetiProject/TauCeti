/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.QuadraticForm.OrthogonalGroup.Integral.Basic
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.OrthogonalBasis
import Mathlib.Topology.Order.Compact

/-!
# Compact orthogonal subgroups containing coordinate reflections

At an odd prime, a compact orthogonal subgroup containing the reflections in an orthogonal
basis of unit quadratic values is integral in that basis. Compactness bounds the orbits of
the basis vectors. Coordinate reflections extract each coordinate without enlarging these
bounds; applying the same estimate to the inverse and using the weighted transpose identity
forces every matrix entry to have norm at most one.

This criterion permits integrality of compact reference subgroups to be deduced from membership
of finitely many reflections, rather than imposed as an additional hypothesis.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms* (1963), §43 and §101.
-/

public section

namespace QuadraticMap

open Module TauCeti TauCeti.QuadraticMap

noncomputable section

variable {p : ℕ} [Fact p.Prime] {V ι : Type*}
  [AddCommGroup V] [Module ℚ_[p] V] [Fintype ι] [DecidableEq ι]
  (Q : QuadraticForm ℚ_[p] V) (b : Basis ι ℚ_[p] V)

omit [Fintype ι] [DecidableEq ι] in
/-- The coordinates of the image of a basis vector under an orthogonal transformation depend
continuously on the transformation. -/
theorem continuous_equivFun_orthogonalGroup_apply_basis [Finite ι]
    (i : ι) :
    Continuous (fun g : orthogonalGroup Q ↦ b.equivFun ((g : V ≃ₗ[ℚ_[p]] V) (b i))) := by
  classical
  have := Fintype.ofFinite ι
  have hM : Continuous (fun g : orthogonalGroup Q ↦
      LinearMap.toMatrix b b (g : V ≃ₗ[ℚ_[p]] V).toLinearMap) :=
    (IsModuleTopology.continuous_of_linearMap
      (LinearMap.toMatrixAlgEquiv b).toLinearMap).comp
      (continuous_linearEquiv_toLinearMap.comp continuous_subtype_val)
  exact (continuous_pi fun k ↦ ((continuous_apply i).comp
    ((continuous_apply k).comp hM))).congr fun g ↦ by
      ext k
      exact LinearMap.toMatrix_apply b b (g : V ≃ₗ[ℚ_[p]] V).toLinearMap k i

omit [DecidableEq ι] in
/-- If the coordinates of the images of the basis vectors under the elements of a subgroup `H`
containing the coordinate reflections are bounded by `C`, with `C i` attained at `a i`, then
the `(i, j)` matrix entries of any `g ∈ H` satisfy `‖g_{ij}‖ * C i ≤ C j`. -/
private theorem norm_repr_apply_mul_le
    [∀ i, Invertible (Q (b i))] (hb : ∀ i j, i ≠ j → Q.IsOrtho (b i) (b j))
    (htwo : ‖(2 : ℚ_[p])‖ = 1) (H : Subgroup (orthogonalGroup Q))
    (hrefl : ∀ i, reflectionOrthogonal Q (b i) ∈ H) {a : ι → orthogonalGroup Q}
    (ha : ∀ i, a i ∈ H) {C : ι → ℝ} (hpos : ∀ i, 0 < C i)
    (hbound : ∀ g ∈ H, ∀ i, ‖b.equivFun ((g : V ≃ₗ[ℚ_[p]] V) (b i))‖ ≤ C i)
    (hC : ∀ i, ‖b.equivFun ((a i : V ≃ₗ[ℚ_[p]] V) (b i))‖ = C i)
    {g : orthogonalGroup Q} (hg : g ∈ H) (i j : ι) :
    ‖b.repr ((g : V ≃ₗ[ℚ_[p]] V) (b j)) i‖ * C i ≤ C j := by
  let F (g : orthogonalGroup Q) (i : ι) := b.equivFun ((g : V ≃ₗ[ℚ_[p]] V) (b i))
  let r := reflectionOrthogonal Q (b i)
  have hr : r ∈ H := hrefl i
  have hproj : F (a i * g) j - F (a i * r * g) j =
      (2 * b.repr ((g : V ≃ₗ[ℚ_[p]] V) (b j)) i) • F (a i) i := by
    simp only [F, Subgroup.coe_mul, mul_apply_eq_comp, r, coe_reflectionOrthogonal,
      reflection_basis_apply Q b hb, map_sub, map_smul]
    module
  have hle : ‖F (a i * g) j - F (a i * r * g) j‖ ≤ C j := by
    apply (pi_norm_le_iff_of_nonneg (hpos j).le).mpr
    intro k
    have h₁ := (norm_le_pi_norm (F (a i * g) j) k).trans
      (hbound _ (H.mul_mem (ha i) hg) j)
    have h₂ := (norm_le_pi_norm (F (a i * r * g) j) k).trans
      (hbound _ (H.mul_mem (H.mul_mem (ha i) hr) hg) j)
    have hk : ‖(F (a i * g) j - F (a i * r * g) j) k‖ ≤
        max ‖F (a i * g) j k‖ ‖F (a i * r * g) j k‖ := by
      simpa [sub_eq_add_neg] using
        Padic.nonarchimedean (F (a i * g) j k) (-(F (a i * r * g) j k))
    exact hk.trans (max_le h₁ h₂)
  simpa only [hproj, norm_smul, norm_mul, htwo, one_mul, F, hC] using hle

/-- If the matrix entries of every element of a subgroup `H` satisfy `‖g_{ij}‖ * C i ≤ C j` for
positive `C`, and orthogonality gives `‖g_{ij}‖ = ‖(g⁻¹)_{ji}‖`, then all entries of elements of
`H` have norm at most `1`. -/
private theorem norm_toMatrix_le_one
    (hb : ∀ i j, i ≠ j → Q.IsOrtho (b i) (b j)) (hunit : ∀ i, ‖Q (b i)‖ = 1)
    (htwo : ‖(2 : ℚ_[p])‖ = 1) (H : Subgroup (orthogonalGroup Q)) {C : ι → ℝ}
    (hpos : ∀ i, 0 < C i)
    (hentry : ∀ g ∈ H, ∀ i j, ‖b.repr ((g : V ≃ₗ[ℚ_[p]] V) (b j)) i‖ * C i ≤ C j)
    {g : orthogonalGroup Q} (hg : g ∈ H) (i j : ι) :
    ‖LinearMap.toMatrix b b (g : V ≃ₗ[ℚ_[p]] V).toLinearMap i j‖ ≤ 1 := by
  have hnorm (g : orthogonalGroup Q) (i j : ι) :
      ‖b.repr ((g : V ≃ₗ[ℚ_[p]] V) (b j)) i‖ =
        ‖b.repr (((g⁻¹ : orthogonalGroup Q) : V ≃ₗ[ℚ_[p]] V) (b i)) j‖ := by
    have h := congrArg norm
      (basis_value_mul_repr_orthogonal_eq_basis_value_mul_repr_inv Q b hb g i j)
    simpa only [norm_mul, htwo, hunit, one_mul] using h
  rw [LinearMap.toMatrix_apply]
  simp only [LinearEquiv.coe_coe]
  have h₁ := hentry g hg i j
  have h₂ := hentry g⁻¹ (H.inv_mem hg) j i
  rw [← hnorm g i j] at h₂
  have hCi := hpos i
  have hCj := hpos j
  nlinarith [norm_nonneg (b.repr ((g : V ≃ₗ[ℚ_[p]] V) (b j)) i)]

/-- At an odd prime, a compact orthogonal subgroup containing all coordinate reflections of an
orthogonal basis of unit quadratic values is contained in its integral orthogonal subgroup. -/
theorem le_integralOrthogonalSubgroup_of_isCompact_of_reflection_mem
    (hp : p ≠ 2) (hb : ∀ i j, i ≠ j → Q.IsOrtho (b i) (b j))
    (hunit : ∀ i, ‖Q (b i)‖ = 1) (H : Subgroup (orthogonalGroup Q))
    (hH : IsCompact (H : Set (orthogonalGroup Q)))
    (hrefl : ∀ i, ∀ hi : Invertible (Q (b i)),
      @reflectionOrthogonal _ _ _ _ _ Q (b i) hi ∈ H) :
    H ≤ integralOrthogonalSubgroup Q b := by
  classical
  let (i : ι) : Invertible (Q (b i)) := invertibleOfNonzero (by
    intro hzero
    simpa [hzero] using hunit i)
  have htwo : ‖(2 : ℚ_[p])‖ = 1 := by
    exact_mod_cast (Padic.norm_natCast_eq_one_iff (p := p) (n := 2)).mpr
      ((Nat.coprime_primes Fact.out Nat.prime_two).mpr hp)
  let F (g : orthogonalGroup Q) (i : ι) := b.equivFun ((g : V ≃ₗ[ℚ_[p]] V) (b i))
  -- Choose the largest orbit norm of each basis vector on the compact subgroup.
  choose a ha hmax using fun i : ι ↦
    hH.exists_isMaxOn ⟨1, H.one_mem⟩
      (continuous_equivFun_orthogonalGroup_apply_basis Q b i).norm.continuousOn
  let C (i : ι) := ‖F (a i) i‖
  have hbound (g : orthogonalGroup Q) (hg : g ∈ H) (i : ι) : ‖F g i‖ ≤ C i :=
    hmax i hg
  have hpos (i : ι) : 0 < C i := by
    have hone : 1 ≤ ‖F (1 : orthogonalGroup Q) i‖ := by
      simpa [F, Basis.equivFun_apply] using
        norm_le_pi_norm (b.equivFun (b i)) i
    exact lt_of_lt_of_le zero_lt_one (hone.trans (hbound 1 H.one_mem i))
  have hentry (g : orthogonalGroup Q) (hg : g ∈ H) (i j : ι) :
      ‖b.repr ((g : V ≃ₗ[ℚ_[p]] V) (b j)) i‖ * C i ≤ C j :=
    norm_repr_apply_mul_le Q b hb htwo H (fun i ↦ hrefl i inferInstance) ha hpos hbound
      (fun _ ↦ rfl) hg i j
  have hintegral (g : orthogonalGroup Q) (hg : g ∈ H) (i j : ι) :
      ‖LinearMap.toMatrix b b (g : V ≃ₗ[ℚ_[p]] V).toLinearMap i j‖ ≤ 1 :=
    norm_toMatrix_le_one Q b hb hunit htwo H (C := C) hpos hentry hg i j
  intro g hg
  exact (mem_integralOrthogonalSubgroup_iff_norm Q b g).mpr
    ⟨hintegral g hg, hintegral g⁻¹ (H.inv_mem hg)⟩

end

end QuadraticMap

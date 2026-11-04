/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Groebner
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Sum
import TauCeti.Analysis.Normed.Module.StrictGenerators

/-!
# Strict generators of submodules of finite free modules over Tate algebras

Let `T = K⟨X₁/c₁, …, Xₙ/cₙ⟩` be a Tate algebra over a complete nonarchimedean field `K`, at
arbitrary positive radii, and give the finite free module `T^ι` the maximum of the Gauss norms of
the coordinates. Every submodule `N ≤ T^ι` has a finite set `F` of nonzero elements generating it
*strictly*: each `y ∈ N` is a combination `∑ x ∈ F, a x • x` with `‖a x‖ * ‖x‖ ≤ ‖y‖`
(`Submodule.exists_finset_eq_sum_smul_isRestricted_subring`). At unit polyradius the generators
can be taken of norm one, with coefficients of norm at most `‖y‖`
(`Submodule.exists_finset_norm_eq_one_isRestricted_subring`). These are the module forms of
`Ideal.exists_finset_eq_sum_mul_isRestricted_subring` and
`Ideal.exists_finset_norm_eq_one_isRestricted_subring`. As for ideals, the general statement
(`TauCeti.MvPowerSeries.exists_finset_eq_sum_smul_isRestricted_subring_of_division`) holds over a
complete commutative ring with a multiplicative ultrametric norm and a compatible Euclidean
degree.

## Proof

The submodule is reduced to an ideal in more variables. In the restricted series over `T` in new
variables `Y_i`, `i ∈ ι`, at radius one, consider the ideal `J` of series `z` without constant
term whose linear part `∑ᵢ zᵢ Yᵢ` has coefficient vector `(zᵢ)ᵢ ∈ N`. Since `z` has no constant
term, the linear part of `a * z` is the constant term of `a` times that of `z`, so `J` is an
ideal. Identifying series over `T` in `Y` with restricted series in the variables `X` and `Y`
(`TauCeti.MvPowerSeries.restrictedSumEquiv`), the ideal `J` has strict generators `g`. For
`y ∈ N`, write `∑ᵢ yᵢ Yᵢ = ∑ a g * g` strictly and compare linear parts:
`y = ∑ (a g)(0) • lin(g)`. Taking coefficients does not increase Gauss norms, and the Gauss norm of
`∑ᵢ yᵢ Yᵢ` is at most `‖y‖`, so the linear parts of the `g` generate `N` strictly.

## References

* S. Bosch, *Lectures on Formal and Rigid Geometry*, §1.3, for strict generating systems of
  submodules of `T^m`.
-/

public section

namespace TauCeti.MvPowerSeries

open _root_.MvPowerSeries

variable {σ ι R : Type*} [NormedCommRing R] [IsUltrametricDist R] {c : σ → ℝ}
  [∀ i, Fact (0 < c i)]

local notation "T" => IsRestricted.subring (R := R) c
local notation "TY" => IsRestricted.subring (R := T) (fun _ : ι ↦ (1 : ℝ))

/-- The coefficients of the variables `Yᵢ` in a restricted series over `T` in the variables `Y`. -/
private noncomputable def linearCoeff : TY →+ (ι → T) :=
  AddMonoidHom.pi fun i ↦ (coeff (Finsupp.single i 1)).toAddMonoidHom.comp
    (IsRestricted.subring (R := T) (fun _ : ι ↦ (1 : ℝ))).subtype.toAddMonoidHom

private theorem linearCoeff_apply (z : TY) (i : ι) :
    linearCoeff z i = coeff (Finsupp.single i 1) (z : MvPowerSeries ι T) := (rfl)

private theorem linearCoeff_mul (a z : TY) (hz : constantCoeff (z : MvPowerSeries ι T) = 0) :
    linearCoeff (a * z) = constantCoeff (a : MvPowerSeries ι T) • linearCoeff z := by
  classical
  funext i
  simp [linearCoeff_apply, coeff_mul, Finsupp.antidiagonal_single, Finset.Nat.antidiagonal_succ,
    hz]

private theorem norm_linearCoeff_le [Fintype ι] (z : TY) : ‖linearCoeff z‖ ≤ ‖z‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg z)).mpr fun _ ↦ norm_coeff_le_norm z _

/-- The series over `T` in the variables `Y` without constant term whose linear part
`∑ᵢ xᵢ Yᵢ` has `x ∈ N`. -/
private noncomputable def linearIdeal (N : Submodule T (ι → T)) : Ideal TY where
  carrier := {z | constantCoeff (z : MvPowerSeries ι T) = 0 ∧ linearCoeff z ∈ N}
  add_mem' {z w} hz hw := by
    refine ⟨?_, ?_⟩
    · simp [hz.1, hw.1]
    · rw [map_add]
      exact N.add_mem hz.2 hw.2
  zero_mem' := ⟨by simp, by simp⟩
  smul_mem' a z hz := by
    refine ⟨?_, ?_⟩
    · simp [hz.1]
    · rw [smul_eq_mul, linearCoeff_mul _ _ hz.1]
      exact N.smul_mem _ hz.2

variable [Fintype ι]

/-- The series `∑ᵢ xᵢ Yᵢ` over `T`, linear in the variables `Y`. -/
private noncomputable def linearForm (x : ι → T) : TY :=
  ∑ i, ⟨monomial (Finsupp.single i 1) (x i), isRestricted_monomial _ _ _⟩

private theorem linearCoeff_linearForm (x : ι → T) : linearCoeff (linearForm x) = x := by
  classical
  funext j
  simp [linearCoeff_apply, linearForm, coeff_monomial, Finsupp.single_left_inj]

private theorem constantCoeff_linearForm (x : ι → T) :
    constantCoeff (linearForm x : MvPowerSeries ι T) = 0 := by
  classical
  have h (i : ι) : (0 : ι →₀ ℕ) ≠ Finsupp.single i 1 :=
    (Finsupp.single_ne_zero.mpr one_ne_zero).symm
  simp [linearForm, ← coeff_zero_eq_constantCoeff_apply, coeff_monomial, h]

private theorem norm_linearForm_le (x : ι → T) : ‖linearForm x‖ ≤ ‖x‖ :=
  IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg x) fun i _ ↦ by
    simpa using norm_le_pi_norm x i

private theorem linearForm_mem_linearIdeal {N : Submodule T (ι → T)} {x : ι → T} (hx : x ∈ N) :
    linearForm x ∈ linearIdeal N :=
  ⟨constantCoeff_linearForm x, (linearCoeff_linearForm x).symm ▸ hx⟩

/-- **Strict generators of submodules of finite free modules over restricted power series.**
Let `R` be a complete commutative ring with a multiplicative ultrametric norm, and `deg : R → ℕ`
a degree such that `deg y = deg x` whenever `‖x - y‖ < ‖x‖`, and such that for `x ≠ 0` every `y`
can be divided as `y = z * x + w` with `‖w‖ ≤ ‖y‖` and either `w = 0` or `deg w < deg x`. Let `T`
be the ring of restricted power series over `R` in finitely many variables at positive radii `c`.
Then every submodule `N` of the finite free module `ι → T`, with the maximum norm, has a finite set
`F` of nonzero elements such that every `y ∈ N` is a combination `∑ x ∈ F, a x • x` with
`‖a x‖ * ‖x‖ ≤ ‖y‖`. In particular `F` generates `N`, and `F` is empty when `N = ⊥`. -/
theorem exists_finset_eq_sum_smul_isRestricted_subring_of_division [NormMulClass R]
    [CompleteSpace R] [Finite σ] (deg : R → ℕ)
    (hdeg : ∀ x y : R, ‖x - y‖ < ‖x‖ → deg y = deg x)
    (hdiv : ∀ x y : R, x ≠ 0 → ∃ z w, y = z * x + w ∧ ‖w‖ ≤ ‖y‖ ∧ (w = 0 ∨ deg w < deg x))
    (N : Submodule T (ι → T)) :
    ∃ F : Finset (ι → T), (∀ x ∈ F, x ∈ N ∧ x ≠ 0) ∧
      ∀ y ∈ N, ∃ a : (ι → T) → T, y = ∑ x ∈ F, a x • x ∧ ∀ x ∈ F, ‖a x‖ * ‖x‖ ≤ ‖y‖ := by
  classical
  -- `e` identifies restricted series in the variables `ι ⊕ σ` with restricted series in the
  -- variables `Y = ι` over `T`. Strict generators of the ideal of series in `Y` whose linear part
  -- comes from `N` and whose constant term vanishes give strict generators of `N`, by taking
  -- linear parts.
  let e := restrictedSumEquiv (R := R) (c := fun _ : ι ↦ (1 : ℝ)) (d := c)
  obtain ⟨G, hGN, hG⟩ := exists_finset_eq_sum_mul_isRestricted_subring_of_division deg hdeg hdiv
    ((linearIdeal N).comap e)
  let s g := linearCoeff (e g)
  have hsN (g) (hg : g ∈ G) : constantCoeff (e g : MvPowerSeries ι T) = 0 ∧ s g ∈ N :=
    (hGN g hg).1
  refine ⟨(G.image s).filter (· ≠ 0), ?_, fun y hy ↦ ?_⟩
  · simp only [Finset.mem_filter, Finset.mem_image, and_imp, forall_exists_index]
    rintro _ g hg rfl hne
    exact ⟨(hsN g hg).2, hne⟩
  obtain ⟨a, ha, hale⟩ := hG (e.symm (linearForm y)) (by
    rw [Ideal.mem_comap, RingEquiv.apply_symm_apply]
    exact linearForm_mem_linearIdeal hy)
  let b g := constantCoeff (e (a g) : MvPowerSeries ι T)
  have hy' : y = ∑ g ∈ G, b g • s g := by
    have := congrArg (fun z ↦ linearCoeff (e z)) ha
    simp only [RingEquiv.apply_symm_apply, linearCoeff_linearForm, map_sum, map_mul] at this
    rw [this]
    exact Finset.sum_congr rfl fun g hg ↦ linearCoeff_mul _ _ (hsN g hg).1
  refine ⟨fun x ↦ ∑ g ∈ G with s g = x, b g, ?_, fun x hx ↦ ?_⟩
  · rw [Finset.sum_filter_of_ne fun x _ h ↦ by rintro rfl; simp at h, hy']
    simp only [Finset.sum_smul]
    calc ∑ g ∈ G, b g • s g = ∑ x ∈ G.image s, ∑ g ∈ G with s g = x, b g • s g :=
          (Finset.sum_fiberwise_of_maps_to (fun g hg ↦ Finset.mem_image_of_mem s hg) _).symm
      _ = ∑ x ∈ G.image s, ∑ g ∈ G with s g = x, b g • x :=
          Finset.sum_congr rfl fun x _ ↦ Finset.sum_congr rfl fun g hg ↦ by
            rw [(Finset.mem_filter.mp hg).2]
  · have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr (Finset.mem_filter.mp hx).2
    have hey : ‖e.symm (linearForm y)‖ ≤ ‖y‖ := by
      rw [← norm_restrictedSumEquiv, RingEquiv.apply_symm_apply]
      exact norm_linearForm_le y
    rw [← le_div_iff₀ hxpos]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
      (div_nonneg (norm_nonneg _) hxpos.le) fun g hg ↦ ?_
    obtain ⟨hgG, rfl⟩ := Finset.mem_filter.mp hg
    rw [le_div_iff₀ hxpos]
    calc ‖b g‖ * ‖s g‖ ≤ ‖a g‖ * ‖g‖ :=
          mul_le_mul ((norm_constantCoeff_le _).trans_eq (norm_restrictedSumEquiv _))
            ((norm_linearCoeff_le _).trans_eq (norm_restrictedSumEquiv _)) (norm_nonneg _)
            (norm_nonneg _)
      _ ≤ ‖y‖ := (hale g hgG).trans hey

section Field

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Finite σ]

/-- **Strict generators of submodules of finite free modules over Tate algebras.** Over a
complete nonarchimedean field `K`, in finitely many variables and at arbitrary positive radii `c`,
every submodule `N` of the finite free module `ι → K⟨X/c⟩`, with the maximum norm, has a finite set
`F` of nonzero elements such that every `y ∈ N` is a combination `∑ x ∈ F, a x • x` with
`‖a x‖ * ‖x‖ ≤ ‖y‖`. -/
theorem _root_.Submodule.exists_finset_eq_sum_smul_isRestricted_subring
    (N : Submodule (IsRestricted.subring (R := K) c) (ι → IsRestricted.subring (R := K) c)) :
    ∃ F : Finset (ι → IsRestricted.subring (R := K) c), (∀ x ∈ F, x ∈ N ∧ x ≠ 0) ∧
      ∀ y ∈ N, ∃ a : (ι → IsRestricted.subring (R := K) c) → IsRestricted.subring (R := K) c,
        y = ∑ x ∈ F, a x • x ∧ ∀ x ∈ F, ‖a x‖ * ‖x‖ ≤ ‖y‖ :=
  exists_finset_eq_sum_smul_isRestricted_subring_of_division (fun _ ↦ 0) (fun _ _ _ ↦ rfl)
    (fun x y hx ↦ ⟨y * x⁻¹, 0, by rw [add_zero, inv_mul_cancel_right₀ hx], by simp, Or.inl rfl⟩)
    N

/-- **Strict generators of norm one.** Over a complete nonarchimedean field `K`, every submodule
`N` of the finite free module `ι → K⟨X⟩` over the Tate algebra at unit polyradius in finitely many
variables, with the maximum norm, has a finite set `F` of generators of norm one such that every
`y ∈ N` is a combination `∑ x ∈ F, a x • x` with `‖a x‖ ≤ ‖y‖`. The set `F` is empty when
`N = ⊥`. -/
theorem _root_.Submodule.exists_finset_norm_eq_one_isRestricted_subring
    (N : Submodule (IsRestricted.subring (R := K) (fun _ : σ ↦ 1))
      (ι → IsRestricted.subring (R := K) (fun _ : σ ↦ 1))) :
    ∃ F : Finset (ι → IsRestricted.subring (R := K) (fun _ : σ ↦ 1)),
      (∀ x ∈ F, x ∈ N ∧ ‖x‖ = 1) ∧
      ∀ y ∈ N, ∃ a : (ι → IsRestricted.subring (R := K) (fun _ : σ ↦ 1)) →
          IsRestricted.subring (R := K) (fun _ : σ ↦ 1),
        y = ∑ x ∈ F, a x • x ∧ ∀ x ∈ F, ‖a x‖ ≤ ‖y‖ := by
  refine N.exists_finset_norm_eq_one_of_exists_finset_eq_sum_smul (fun x _ hx ↦ ?_)
    N.exists_finset_eq_sum_smul_isRestricted_subring
  -- The norm of `x` is the norm of one of its coordinates, which is the norm of a unit.
  have : Nonempty ι := not_isEmpty_iff.mp fun _ ↦ hx (Subsingleton.elim x 0)
  obtain ⟨i, hi : ‖x i‖ = ‖x‖⟩ := (IsGreatest.pi_norm x).1
  obtain ⟨u, hu, hux⟩ := exists_isUnit_and_norm_eq (f := x i) (by
    rw [← norm_pos_iff, hi]
    exact norm_pos_iff.mpr hx)
  exact ⟨u, hu, hux.trans hi⟩

end Field

end TauCeti.MvPowerSeries

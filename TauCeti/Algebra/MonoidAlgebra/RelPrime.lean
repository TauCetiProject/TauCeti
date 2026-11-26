/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.Ring.Divisibility.Lemmas
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import TauCeti.Algebra.Group.UniqueProds.TorsionFree
import TauCeti.Algebra.MonoidAlgebra.Basic
import TauCeti.Algebra.MonoidAlgebra.ComapDomain
import TauCeti.Algebra.MonoidAlgebra.Grading
import TauCeti.Algebra.MonoidAlgebra.Units

/-!
# Relative primality along independent cyclic directions in lattice Laurent rings

Let `R` be a commutative semiring without zero divisors and `L` a torsion-free abelian group
(`[AddCommGroup L] [HasUniqueDiv L]`). Suppose nonzero elements `P, Q : AddMonoidAlgebra R L` have
exponent supports contained in `AddSubgroup.zmultiples a` and `AddSubgroup.zmultiples b` for a
`ℤ`-linearly independent pair `![a, b]`.

For every integer weight `w : L →+ ℤ` vanishing on `a`, `P` has width `0` in the `w`-grading
`AddMonoidAlgebra.gradeBy R w`
(`AddMonoidAlgebra.width_gradeBy_eq_zero_of_support_subset_zmultiples`). Additivity of
`TauCeti.GradedAlgebra.width` forces every divisor `D ∣ P` to have `w`-width `0` as well, so `w` is
constant on `D.coeff.support`. Applying this to all weights `w₂ a • w₁ - w₁ a • w₂` (for `P`) and
`w₂ b • w₁ - w₁ b • w₂` (for `Q`) on a finitely generated free `ℤ`-submodule of `L` containing the
supports forces every common divisor `D` of `P` and `Q` to have at most one supported exponent, i.e.
to be a single monomial. If in addition `P` has at least one unit coefficient, the single
coefficient of `D` divides that unit coefficient and is therefore a unit, making `D` a unit of
`AddMonoidAlgebra R L`.

Consequently `P` and `Q` are relatively prime (`IsRelPrime P Q`) without any factoriality
assumption on `R` or finite-rank assumption on `L`. In particular, binomials `1 + single a c` and
`1 + single b d`, as well as finite products `∏ r ∈ s, (1 + single a (c r))` and
`∏ r ∈ t, (1 + single b (d r))`, are relatively prime whenever `LinearIndependent ℤ ![a, b]`.

## Main results

* `AddMonoidAlgebra.weight_sub_eq_of_dvd_of_support_subset_zmultiples`: weight-determinant identity
  `w₂ a * w₁ (x - y) = w₁ a * w₂ (x - y)` on supported exponents `x, y` of any divisor `D ∣ P` when
  `P ≠ 0` is supported on `ℤ ∙ a`.
* `AddMonoidAlgebra.subsingleton_support_of_dvd_of_linearIndependent`: every common divisor of
  nonzero `P, Q` supported on `ℤ ∙ a` and `ℤ ∙ b` (`LinearIndependent ℤ ![a, b]`) has subsingleton
  exponent support.
* `AddMonoidAlgebra.isRelPrime_of_support_subset_zmultiples`: if moreover `P` has a unit
  coefficient, then `IsRelPrime P Q`.
* `AddMonoidAlgebra.isRelPrime_one_add_single`, `AddMonoidAlgebra.isRelPrime_prod_one_add_single`:
  relative primality of binomials and finite products of binomials along independent directions.

## References

* S. Fomin and A. Zelevinsky, *Cluster algebras I: Foundations*, J. Amer. Math. Soc. 15 (2002),
  §3.
* A. Berenstein and A. Zelevinsky, *Quantum cluster algebras*, Adv. Math. 195 (2005), §5.
-/

public section

namespace AddMonoidAlgebra

open TauCeti.GradedAlgebra

section TorsionFree

variable {R L : Type*} [CommSemiring R] [NoZeroDivisors R] [AddCommGroup L] [HasUniqueDiv L]

/-- Weight-determinant identity for divisors of an element supported on `ℤ ∙ a`: for any two
integer weights `w₁, w₂ : L →+ ℤ` and any two exponents `x, y` in the support of a divisor `D ∣ P`
(`P ≠ 0`), `w₂ a * w₁ (x - y) = w₁ a * w₂ (x - y)`. -/
theorem weight_sub_eq_of_dvd_of_support_subset_zmultiples {a : L} {P D : R[L]}
    (hP : P ≠ 0) (hsupp : (P.coeff.support : Set L) ⊆ AddSubgroup.zmultiples a)
    (hDP : D ∣ P) (w₁ w₂ : L →+ ℤ) {x y : L}
    (hx : x ∈ D.coeff.support) (hy : y ∈ D.coeff.support) :
    w₂ a * w₁ (x - y) = w₁ a * w₂ (x - y) := by
  let w : L →+ ℤ := w₂ a • w₁ - w₁ a • w₂
  have hwa : w a = 0 := by
    simp only [w, AddMonoidHom.sub_apply, AddMonoidHom.smul_apply, zsmul_eq_mul, Int.cast_id]
    ring
  have hwP : width (gradeBy R w) P = 0 :=
    width_gradeBy_eq_zero_of_support_subset_zmultiples hsupp hwa
  have hwD : width (gradeBy R w) D = 0 :=
    le_antisymm ((width_le_of_dvd (gradeBy R w) hP hDP).trans_eq hwP)
      (width_nonneg (gradeBy R w) D)
  have hxy : w x = w y := (width_gradeBy_eq_zero_iff w D).mp hwD x hx y hy
  have hsub : w (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  simp only [w, AddMonoidHom.sub_apply, AddMonoidHom.smul_apply, zsmul_eq_mul, Int.cast_id] at hsub
  exact sub_eq_zero.mp hsub

private theorem repr_sub_smul_eq_of_dvd_of_support_subset_zmultiples {ι : Type*}
    (B : Module.Basis ι ℤ L) (j : ι) {a : L} {P D : R[L]}
    (hP : P ≠ 0) (hsupp : (P.coeff.support : Set L) ⊆ AddSubgroup.zmultiples a)
    (hDP : D ∣ P) {x y : L} (hx : x ∈ D.coeff.support) (hy : y ∈ D.coeff.support) :
    B.repr (x - y) j • a = B.repr a j • (x - y) := by
  apply B.repr.injective
  ext i
  have hid := weight_sub_eq_of_dvd_of_support_subset_zmultiples hP hsupp hDP
    (B.coord i).toAddMonoidHom (B.coord j).toAddMonoidHom hx hy
  simp only [LinearMap.toAddMonoidHom_coe, Module.Basis.coord_apply] at hid
  simp only [map_zsmul, Finsupp.smul_apply, zsmul_eq_mul, Int.cast_id]
  linarith

private theorem subsingleton_support_of_dvd_of_linearIndependent_free [Module.Free ℤ L]
    {a b : L} (hab : LinearIndependent ℤ ![a, b]) {P Q D : R[L]}
    (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hPa : (P.coeff.support : Set L) ⊆ AddSubgroup.zmultiples a)
    (hQb : (Q.coeff.support : Set L) ⊆ AddSubgroup.zmultiples b)
    (hDP : D ∣ P) (hDQ : D ∣ Q) :
    (D.coeff.support : Set L).Subsingleton := by
  intro x hx y hy
  by_contra hxy
  let B := Module.Free.chooseBasis ℤ L
  have hne : B.repr (x - y) ≠ 0 :=
    B.repr.map_eq_zero_iff.not.mpr (sub_ne_zero.mpr hxy)
  obtain ⟨j₀, hj₀⟩ := Finsupp.support_nonempty_iff.mpr hne
  set c : ℤ := B.repr (x - y) j₀
  have hc : c ≠ 0 := Finsupp.mem_support_iff.mp hj₀
  have ha_eq : c • a = B.repr a j₀ • (x - y) :=
    repr_sub_smul_eq_of_dvd_of_support_subset_zmultiples B j₀ hP hPa hDP hx hy
  have hb_eq : c • b = B.repr b j₀ • (x - y) :=
    repr_sub_smul_eq_of_dvd_of_support_subset_zmultiples B j₀ hQ hQb hDQ hx hy
  have hrel : (c * B.repr b j₀) • a + (-(c * B.repr a j₀)) • b = 0 := by
    linear_combination (norm := module) (B.repr b j₀) • ha_eq - (B.repr a j₀) • hb_eq
  have haj₀ : B.repr a j₀ = 0 := by
    have h2 := (LinearIndependent.pair_iff.mp hab _ _ hrel).2
    rcases mul_eq_zero.mp (neg_eq_zero.mp h2) with hc0 | ha0
    · exact absurd hc0 hc
    · exact ha0
  have hca : c • a + (0 : ℤ) • b = 0 := by simp [ha_eq, haj₀]
  exact hc (LinearIndependent.pair_iff.mp hab c 0 hca).1

/-- **Common divisors along independent cyclic directions are monomials.** If `P, Q : R[L]` are
nonzero with supports in `ℤ ∙ a` and `ℤ ∙ b` for `LinearIndependent ℤ ![a, b]`, every common
divisor `D` of `P` and `Q` has at most one exponent in its support. -/
theorem subsingleton_support_of_dvd_of_linearIndependent {a b : L}
    (hab : LinearIndependent ℤ ![a, b]) {P Q D : R[L]}
    (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hPa : (P.coeff.support : Set L) ⊆ AddSubgroup.zmultiples a)
    (hQb : (Q.coeff.support : Set L) ⊆ AddSubgroup.zmultiples b)
    (hDP : D ∣ P) (hDQ : D ∣ Q) :
    (D.coeff.support : Set L).Subsingleton := by
  classical
  -- Step 1: Span a finitely generated (hence free) ℤ-submodule M containing all exponents and a, b.
  obtain ⟨U, hPU⟩ := hDP
  obtain ⟨V, hQV⟩ := hDQ
  let S : Finset L := P.coeff.support ∪ Q.coeff.support ∪ D.coeff.support ∪
    U.coeff.support ∪ V.coeff.support ∪ {a, b}
  let M : Submodule ℤ L := Submodule.span ℤ (S : Set L)
  have : Module.Finite ℤ M := Module.Finite.span_of_finite ℤ S.finite_toSet
  have : HasUniqueDiv M := .of_isTorsionFree ℤ M
  let φ : M →+ L := M.toAddSubgroup.subtype
  have hφ : Function.Injective φ := Subtype.val_injective
  have hsub (T : Finset L) (hT : T ⊆ S) : (T : Set L) ⊆ Set.range φ := by
    rw [AddSubgroup.coe_subtype, Subtype.range_val]
    exact (Finset.coe_subset.mpr hT).trans Submodule.subset_span
  have hPM := hsub P.coeff.support (by grind)
  have hQM := hsub Q.coeff.support (by grind)
  have hDM := hsub D.coeff.support (by grind)
  -- Step 2: Pull P, Q, D, a, b and their support/divisibility hypotheses back along φ : M →+ L.
  let a₀ : M := ⟨a, Submodule.subset_span (by simp [S])⟩
  let b₀ : M := ⟨b, Submodule.subset_span (by simp [S])⟩
  have hab₀ : LinearIndependent ℤ ![a₀, b₀] := by
    rw [LinearIndependent.pair_iff] at hab ⊢
    exact fun s t hst ↦ hab s t (by simpa [a₀, b₀] using congrArg Subtype.val hst)
  have hne {X : R[L]} (hX : X ≠ 0) (hXM : (X.coeff.support : Set L) ⊆ Set.range φ) :
      comapDomain φ hφ X ≠ 0 := fun h0 ↦
    hX (by simpa [h0] using (mapDomain_comapDomain hXM hφ).symm)
  have hzmult {X : R[L]} {c₀ : M}
      (hXc : (X.coeff.support : Set L) ⊆ AddSubgroup.zmultiples (φ c₀)) :
      ((comapDomain φ hφ X).coeff.support : Set M) ⊆ AddSubgroup.zmultiples c₀ :=
    support_coeff_comapDomain_subset hφ <| by
      rwa [← AddSubgroup.coe_map, AddMonoidHom.map_zmultiples]
  -- Step 3: Apply the free-module theorem on M and push subsingleton support forward along φ.
  have hsub₀ := subsingleton_support_of_dvd_of_linearIndependent_free hab₀
    (hne hP hPM) (hne hQ hQM) (hzmult hPa) (hzmult hQb)
    (comapDomain_dvd_comapDomain hφ hPU hDM (hsub U.coeff.support (by grind)))
    (comapDomain_dvd_comapDomain hφ hQV hDM (hsub V.coeff.support (by grind)))
  have hD_img : φ '' ((comapDomain φ hφ D).coeff.support : Set M) = (D.coeff.support : Set L) := by
    rw [coeff_comapDomain, Finsupp.comapDomain_support, Finset.coe_preimage,
      Set.image_preimage_eq_iff.mpr hDM]
  exact hD_img ▸ hsub₀.image φ

/-- **Relative primality along independent cyclic directions.** Let `P, Q : R[L]` be nonzero with
supports in `ℤ ∙ a` and `ℤ ∙ b` for `LinearIndependent ℤ ![a, b]`. If `P` has a unit coefficient,
then `IsRelPrime P Q`. -/
theorem isRelPrime_of_support_subset_zmultiples {a b : L}
    (hab : LinearIndependent ℤ ![a, b]) {P Q : R[L]}
    (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hPa : (P.coeff.support : Set L) ⊆ AddSubgroup.zmultiples a)
    (hQb : (Q.coeff.support : Set L) ⊆ AddSubgroup.zmultiples b)
    (hunit : ∃ m : L, IsUnit (P.coeff m)) :
    IsRelPrime P Q := by
  intro D hDP hDQ
  have hsub := subsingleton_support_of_dvd_of_linearIndependent hab hP hQ hPa hQb hDP hDQ
  obtain ⟨U, hPU⟩ := hDP
  have hD0 : D ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hPU
    exact hP hPU
  obtain ⟨x₀, hx₀⟩ := Finsupp.support_nonempty_iff.mpr (mt coeff_eq_zero.mp hD0)
  set r : R := D.coeff x₀
  have hD_eq : D = single x₀ r := by
    classical
    exact coeff_inj.mp (Finsupp.support_subset_singleton.mp fun y hy ↦
      Finset.mem_singleton.mpr (hsub hy hx₀))
  obtain ⟨m, hm⟩ := hunit
  have hcoeff : P.coeff m = r * U.coeff (-x₀ + m) := by
    rw [hPU, hD_eq]
    exact coeff_single_mul_eq_mul_coeff (-x₀ + m) (fun y _ ↦ eq_neg_add_iff_add_eq.symm)
  have huD : IsUnit r := isUnit_of_dvd_unit ⟨U.coeff (-x₀ + m), hcoeff⟩ hm
  have : Nontrivial R := ⟨⟨r, 0, Finsupp.mem_support_iff.mp hx₀⟩⟩
  rw [hD_eq]
  exact (isUnit_single_iff x₀ r).mpr ⟨AddGroup.isAddUnit x₀, huD⟩

/-- **Finite products of binomials along independent directions are relatively prime**, for
arbitrary coefficients `c r, d t : R`. -/
theorem isRelPrime_prod_one_add_single {ι κ : Type*} {a b : L}
    (hab : LinearIndependent ℤ ![a, b]) (s : Finset ι) (t : Finset κ)
    (c : ι → R) (d : κ → R) :
    IsRelPrime (∏ r ∈ s, (1 + single a (c r))) (∏ r ∈ t, (1 + single b (d r))) := by
  cases subsingleton_or_nontrivial R
  · exact fun _ _ _ ↦ isUnit_of_subsingleton _
  have ha : ¬ IsOfFinAddOrder a :=
    not_isOfFinAddOrder_of_isAddTorsionFree (by simpa using hab.ne_zero 0)
  have hb : ¬ IsOfFinAddOrder b :=
    not_isOfFinAddOrder_of_isAddTorsionFree (by simpa using hab.ne_zero 1)
  have hP0 : (∏ r ∈ s, (1 + single a (c r))).coeff 0 = 1 :=
    coeff_zero_prod_one_add_single s ha c
  have hQ0 : (∏ r ∈ t, (1 + single b (d r))).coeff 0 = 1 :=
    coeff_zero_prod_one_add_single t hb d
  have hP : (∏ r ∈ s, (1 + single a (c r))) ≠ 0 := fun h ↦ by simp [h] at hP0
  have hQ : (∏ r ∈ t, (1 + single b (d r))) ≠ 0 := fun h ↦ by simp [h] at hQ0
  have hmul_sub (v : L) : (AddSubmonoid.multiples v : Set L) ⊆ AddSubgroup.zmultiples v := by
    intro x hx
    obtain ⟨n, rfl⟩ := (AddSubmonoid.mem_multiples_iff x v).mp hx
    exact AddSubgroup.mem_zmultiples_iff.mpr ⟨n, natCast_zsmul v n⟩
  exact isRelPrime_of_support_subset_zmultiples hab hP hQ
    ((support_coeff_prod_one_add_single_subset s a c).trans (hmul_sub a))
    ((support_coeff_prod_one_add_single_subset t b d).trans (hmul_sub b))
    ⟨0, hP0.symm ▸ isUnit_one⟩

/-- Binomials `1 + single a c` and `1 + single b d` along `ℤ`-linearly independent directions
`a, b` are relatively prime. -/
theorem isRelPrime_one_add_single {a b : L} (hab : LinearIndependent ℤ ![a, b]) (c d : R) :
    IsRelPrime (1 + single a c) (1 + single b d) := by
  simpa using isRelPrime_prod_one_add_single hab {()} {()} (fun _ ↦ c) (fun _ ↦ d)

end TorsionFree

end AddMonoidAlgebra

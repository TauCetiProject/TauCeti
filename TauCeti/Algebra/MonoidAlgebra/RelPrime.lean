/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Grading
public import Mathlib.Algebra.Ring.Divisibility.Lemmas
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import TauCeti.RingTheory.GradedAlgebra.Degree.Width
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
import Mathlib.Algebra.MonoidAlgebra.Support
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import TauCeti.Algebra.Group.UniqueProds.TorsionFree
import TauCeti.Algebra.MonoidAlgebra.Units

/-!
# Relative primality along independent cyclic directions in lattice Laurent rings

Let `R` be a commutative semiring without zero divisors and `L` a torsion-free abelian group
(`[AddCommGroup L] [HasUniqueDiv L]`). Suppose nonzero elements `P, Q : AddMonoidAlgebra R L` have
exponent supports contained in `AddSubgroup.zmultiples a` and `AddSubgroup.zmultiples b` for a
`ℤ`-linearly independent pair `![a, b]`.

For every integer weight `w : L →+ ℤ` vanishing on `a`, `P` has width `0` in the `w`-grading
`AddMonoidAlgebra.gradeBy R w`. Additivity of `TauCeti.GradedAlgebra.width` forces every divisor
`D ∣ P` to have `w`-width `0` as well, so `w` is constant on `D.coeff.support`. Applying this to
all weights `w₂ a • w₁ - w₁ a • w₂` (for `P`) and `w₂ b • w₁ - w₁ b • w₂` (for `Q`) on a finitely
generated free `ℤ`-submodule of `L` containing the supports forces every common divisor `D` of `P`
and `Q` to have at most one supported exponent, i.e. to be a single monomial. If in addition `P`
has at least one unit coefficient, the single coefficient of `D` divides that unit coefficient and
is therefore a unit, making `D` a unit of `AddMonoidAlgebra R L`.

Consequently `P` and `Q` are relatively prime (`IsRelPrime P Q`) without any factoriality
assumption on `R` or finite-rank assumption on `L`. In particular, binomials `1 + single a c` and
`1 + single b d`, as well as finite products `∏ r ∈ s, (1 + single a (c r))` and
`∏ r ∈ t, (1 + single b (d r))`, are relatively prime whenever `LinearIndependent ℤ ![a, b]`.

## Main results

* `AddMonoidAlgebra.width_gradeBy_eq_zero_iff`: `width (gradeBy R w) f = 0` iff `w` is constant on
  `f.coeff.support`.
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

section Width

variable {R L : Type*} [CommSemiring R]

/-- An element of `AddMonoidAlgebra R L` has width `0` for `gradeBy R w` if and only if `w` takes
the same value on all exponents in its support. -/
theorem width_gradeBy_eq_zero_iff [AddMonoid L] (w : L →+ ℤ) (f : R[L]) :
    width (gradeBy R w) f = 0 ↔
      ∀ x ∈ f.coeff.support, ∀ y ∈ f.coeff.support, w x = w y := by
  rw [width_eq_zero_iff]
  refine ⟨fun ⟨d, hd⟩ x hx y hy ↦ (hd x hx).trans (hd y hy).symm, fun h ↦ ?_⟩
  rcases f.coeff.support.eq_empty_or_nonempty with hemp | ⟨x₀, hx₀⟩
  · refine ⟨0, fun x hx ↦ ?_⟩
    rw [hemp] at hx
    cases hx
  · exact ⟨w x₀, fun x hx ↦ h x hx x₀ hx₀⟩

/-- An element supported in `AddSubgroup.zmultiples a` has width `0` under any weight `w : L →+ ℤ`
with `w a = 0`. -/
theorem width_gradeBy_eq_zero_of_support_subset_zmultiples [AddGroup L] {a : L} {f : R[L]}
    (hf : (f.coeff.support : Set L) ⊆ AddSubgroup.zmultiples a) {w : L →+ ℤ} (hw : w a = 0) :
    width (gradeBy R w) f = 0 := by
  rw [width_gradeBy_eq_zero_iff]
  intro x hx y hy
  obtain ⟨m, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp (hf hx)
  obtain ⟨n, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp (hf hy)
  simp [hw]

end Width

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

omit [NoZeroDivisors R] [HasUniqueDiv L] in
private theorem support_subset_zmultiples_comapDomain {M : Submodule ℤ L} {a₀ : M}
    {P : R[L]} (hPa : (P.coeff.support : Set L) ⊆ AddSubgroup.zmultiples a₀.1) :
    ((comapDomain (Subtype.val : M → L) Subtype.val_injective P).coeff.support : Set M) ⊆
      AddSubgroup.zmultiples a₀ := fun x hx ↦ by
  have hxP : x.1 ∈ P.coeff.support := by
    simpa [Finsupp.mem_support_iff] using hx
  obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp (hPa hxP)
  exact AddSubgroup.mem_zmultiples_iff.mpr ⟨n, Subtype.ext hn⟩

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
  obtain ⟨U, hPU⟩ := hDP
  obtain ⟨V, hQV⟩ := hDQ
  let S : Finset L := P.coeff.support ∪ Q.coeff.support ∪ D.coeff.support ∪
    U.coeff.support ∪ V.coeff.support ∪ {a, b}
  let M : Submodule ℤ L := Submodule.span ℤ (S : Set L)
  have : Module.Finite ℤ M := Module.Finite.span_of_finite ℤ S.finite_toSet
  have : HasUniqueDiv M := .of_isTorsionFree ℤ M
  have hsub (T : Finset L) (hT : T ⊆ S) : (T : Set L) ⊆ M :=
    (Finset.coe_subset.mpr hT).trans Submodule.subset_span
  have hDM : (D.coeff.support : Set L) ⊆ M := hsub D.coeff.support (by grind)
  have hmap_comap {f : R[L]} (hf : (f.coeff.support : Set L) ⊆ M) :
      mapDomain M.subtype.toAddMonoidHom
        (comapDomain (Subtype.val : M → L) Subtype.val_injective f) = f :=
    mapDomain_comapDomain (fun x hx ↦ ⟨⟨x, hf hx⟩, rfl⟩) Subtype.val_injective
  let P₀ : R[M] := comapDomain (Subtype.val : M → L) Subtype.val_injective P
  let Q₀ : R[M] := comapDomain (Subtype.val : M → L) Subtype.val_injective Q
  let D₀ : R[M] := comapDomain (Subtype.val : M → L) Subtype.val_injective D
  let U₀ : R[M] := comapDomain (Subtype.val : M → L) Subtype.val_injective U
  let V₀ : R[M] := comapDomain (Subtype.val : M → L) Subtype.val_injective V
  have hP₀_map : mapDomain M.subtype.toAddMonoidHom P₀ = P :=
    hmap_comap (hsub P.coeff.support (by grind))
  have hQ₀_map : mapDomain M.subtype.toAddMonoidHom Q₀ = Q :=
    hmap_comap (hsub Q.coeff.support (by grind))
  have hD₀_map : mapDomain M.subtype.toAddMonoidHom D₀ = D := hmap_comap hDM
  have hU₀_map : mapDomain M.subtype.toAddMonoidHom U₀ = U :=
    hmap_comap (hsub U.coeff.support (by grind))
  have hV₀_map : mapDomain M.subtype.toAddMonoidHom V₀ = V :=
    hmap_comap (hsub V.coeff.support (by grind))
  let a₀ : M := ⟨a, Submodule.subset_span (by simp [S])⟩
  let b₀ : M := ⟨b, Submodule.subset_span (by simp [S])⟩
  have hab₀ : LinearIndependent ℤ ![a₀, b₀] := by
    rw [LinearIndependent.pair_iff] at hab ⊢
    exact fun s t hst ↦ hab s t (by simpa [a₀, b₀] using congrArg Subtype.val hst)
  have hP₀ : P₀ ≠ 0 := fun h0 ↦ hP (by simpa [h0] using hP₀_map.symm)
  have hQ₀ : Q₀ ≠ 0 := fun h0 ↦ hQ (by simpa [h0] using hQ₀_map.symm)
  have hDP₀ : D₀ ∣ P₀ := ⟨U₀, mapDomain_injective Subtype.val_injective
    (by simpa only [LinearMap.toAddMonoidHom_coe, Submodule.coe_subtype] using
      (hP₀_map.trans hPU).trans ((mapDomain_mul M.subtype.toAddMonoidHom D₀ U₀).trans
        (congrArg₂ (· * ·) hD₀_map hU₀_map)).symm)⟩
  have hDQ₀ : D₀ ∣ Q₀ := ⟨V₀, mapDomain_injective Subtype.val_injective
    (by simpa only [LinearMap.toAddMonoidHom_coe, Submodule.coe_subtype] using
      (hQ₀_map.trans hQV).trans ((mapDomain_mul M.subtype.toAddMonoidHom D₀ V₀).trans
        (congrArg₂ (· * ·) hD₀_map hV₀_map)).symm)⟩
  have hsub₀ := subsingleton_support_of_dvd_of_linearIndependent_free hab₀ hP₀ hQ₀
    (support_subset_zmultiples_comapDomain hPa)
    (support_subset_zmultiples_comapDomain hQb) hDP₀ hDQ₀
  intro x hx y hy
  have hx₀ : (⟨x, hDM hx⟩ : M) ∈ (D₀.coeff.support : Set M) := by
    simpa [D₀, Finsupp.mem_support_iff] using hx
  have hy₀ : (⟨y, hDM hy⟩ : M) ∈ (D₀.coeff.support : Set M) := by
    simpa [D₀, Finsupp.mem_support_iff] using hy
  exact congrArg Subtype.val (hsub₀ hx₀ hy₀)

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
    ext y
    classical
    rw [coeff_single, Finsupp.single_apply]
    split_ifs with hxy
    · subst hxy
      rfl
    · by_contra hy0
      exact hxy (hsub (Finsupp.mem_support_iff.mpr hy0) hx₀).symm
  obtain ⟨m, hm⟩ := hunit
  have hcoeff : P.coeff m = r * U.coeff (-x₀ + m) := by
    rw [hPU, hD_eq]
    exact coeff_single_mul_eq_mul_coeff (-x₀ + m) (fun y _ ↦ eq_neg_add_iff_add_eq.symm)
  have huD : IsUnit r := isUnit_of_dvd_unit ⟨U.coeff (-x₀ + m), hcoeff⟩ hm
  have : Nontrivial R := ⟨⟨r, 0, Finsupp.mem_support_iff.mp hx₀⟩⟩
  rw [hD_eq]
  exact (isUnit_single_iff x₀ r).mpr ⟨AddGroup.isAddUnit x₀, huD⟩

omit [NoZeroDivisors R] in
private theorem prod_one_add_single_support_and_coeff_zero {ι : Type*} (s : Finset ι)
    {a : L} (ha : a ≠ 0) (c : ι → R) :
    ((∏ r ∈ s, (1 + single a (c r))).coeff.support : Set L) ⊆
      {x : L | ∃ n : ℕ, n • a = x} ∧
      (∏ r ∈ s, (1 + single a (c r))).coeff 0 = 1 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨?_, by simp [one_def]⟩
    intro x hx
    rw [Finset.prod_empty, one_def] at hx
    obtain rfl : x = 0 := Finset.mem_singleton.mp (Finsupp.support_single_subset hx)
    exact ⟨0, zero_nsmul a⟩
  | insert r s hrs ih =>
    obtain ⟨hsupp, h0⟩ := ih
    set f : R[L] := 1 + single a (c r)
    set g : R[L] := ∏ i ∈ s, (1 + single a (c i))
    have hf_supp : (f.coeff.support : Set L) ⊆ {x : L | ∃ n : ℕ, n • a = x} := by
      intro x hx
      rw [coeff_add] at hx
      rcases Finset.mem_union.mp (Finsupp.support_add hx) with hx1 | hxa
      · rw [one_def] at hx1
        obtain rfl : x = 0 := Finset.mem_singleton.mp (Finsupp.support_single_subset hx1)
        exact ⟨0, zero_nsmul a⟩
      · rw [coeff_single] at hxa
        have hxa' : x = a := Finset.mem_singleton.mp (Finsupp.support_single_subset hxa)
        exact ⟨1, hxa'.symm ▸ one_nsmul a⟩
    have hf0 : f.coeff 0 = 1 := by
      simp [f, one_def, ha.symm]
    rw [Finset.prod_insert hrs]
    refine ⟨?_, ?_⟩
    · intro x hx
      obtain ⟨y, hy, z, hz, rfl⟩ := Finset.mem_add.mp (support_coeff_mul_subset f g hx)
      obtain ⟨m, rfl⟩ := hf_supp hy
      obtain ⟨n, rfl⟩ := hsupp hz
      exact ⟨m + n, add_nsmul a m n⟩
    · have huniq : UniqueAdd f.coeff.support g.coeff.support 0 0 := by
        intro y z hy hz hyz
        obtain ⟨m, rfl⟩ := hf_supp hy
        obtain ⟨n, rfl⟩ := hsupp hz
        rw [← add_nsmul, add_zero] at hyz
        have hmn : m + n = 0 := (smul_eq_zero_iff_left ha).mp hyz
        obtain ⟨rfl, rfl⟩ : m = 0 ∧ n = 0 := Nat.add_eq_zero_iff.mp hmn
        simp
      have hmul := coeff_mul_add_of_uniqueAdd huniq
      simpa [hf0, h0] using hmul

/-- **Finite products of binomials along independent directions are relatively prime**, for
arbitrary coefficients `c r, d t : R`. -/
theorem isRelPrime_prod_one_add_single {ι κ : Type*} {a b : L}
    (hab : LinearIndependent ℤ ![a, b]) (s : Finset ι) (t : Finset κ)
    (c : ι → R) (d : κ → R) :
    IsRelPrime (∏ r ∈ s, (1 + single a (c r))) (∏ r ∈ t, (1 + single b (d r))) := by
  cases subsingleton_or_nontrivial R
  · exact fun _ _ _ ↦ isUnit_of_subsingleton _
  have ha : a ≠ 0 := by
    rintro rfl
    exact one_ne_zero (LinearIndependent.pair_iff.mp hab 1 0 (by simp)).1
  have hb : b ≠ 0 := by
    rintro rfl
    exact one_ne_zero (LinearIndependent.pair_iff.mp hab 0 1 (by simp)).2
  obtain ⟨hPsupp, hP0⟩ := prod_one_add_single_support_and_coeff_zero s ha c
  obtain ⟨hQsupp, hQ0⟩ := prod_one_add_single_support_and_coeff_zero t hb d
  have hP : (∏ r ∈ s, (1 + single a (c r))) ≠ 0 := by
    intro h
    rw [h, coeff_zero] at hP0
    exact zero_ne_one hP0
  have hQ : (∏ r ∈ t, (1 + single b (d r))) ≠ 0 := by
    intro h
    rw [h, coeff_zero] at hQ0
    exact zero_ne_one hQ0
  refine isRelPrime_of_support_subset_zmultiples hab hP hQ ?_ ?_ ⟨0, hP0.symm ▸ isUnit_one⟩
  · intro x hx
    obtain ⟨n, rfl⟩ := hPsupp hx
    exact AddSubgroup.mem_zmultiples_iff.mpr ⟨n, natCast_zsmul a n⟩
  · intro x hx
    obtain ⟨n, rfl⟩ := hQsupp hx
    exact AddSubgroup.mem_zmultiples_iff.mpr ⟨n, natCast_zsmul b n⟩

/-- Binomials `1 + single a c` and `1 + single b d` along `ℤ`-linearly independent directions
`a, b` are relatively prime. -/
theorem isRelPrime_one_add_single {a b : L} (hab : LinearIndependent ℤ ![a, b]) (c d : R) :
    IsRelPrime (1 + single a c) (1 + single b d) := by
  simpa using isRelPrime_prod_one_add_single hab {()} {()} (fun _ ↦ c) (fun _ ↦ d)

end TorsionFree

end AddMonoidAlgebra

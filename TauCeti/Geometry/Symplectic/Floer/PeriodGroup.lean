/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Algebra.Ring.NegOnePow
public import TauCeti.GroupTheory.SpecificGroups.Cyclic.Int

/-!
# The period group of spherical classes

Let `(X, ω)` be a closed symplectic manifold and let `S` be its group of spherical classes, the
image of the Hurewicz map `π₂(X) → H₂(X; ℤ)`. Integrating `ω` and evaluating the first Chern
class give homomorphisms `ω : S →+ ℝ` and `c : S →+ ℤ`. Two caps of a contractible loop differ
by a spherical class `B`, and replacing one cap by the other shifts the action by `ω B` and the
Conley–Zehnder grading by `2 * c B`. Capped Hamiltonian Floer theory therefore takes its
coefficients over the *period group*
`Γ = S ⧸ (ker ω ⊓ ker c)`,
on which area and first Chern number descend. Quotienting by the joint kernel, rather than by
`ker ω` alone, keeps apart classes of equal area and different Chern number, hence different
degree.

This file develops `Γ` for an arbitrary additive group `S` with two such homomorphisms. We write
`Γ` as the quotient by the kernel of `s ↦ (ω s, c s)`, which is `ker ω ⊓ ker c` by
`AddMonoidHom.ker_prod`.

## Main definitions

* `TauCeti.Floer.PeriodGroup ω c`: the period group `Γ`.
* `TauCeti.Floer.PeriodGroup.periods`: the injective homomorphism `Γ →+ ℝ × ℤ` recording area
  and first Chern number, with components `PeriodGroup.area` and `PeriodGroup.chern`.
* `TauCeti.Floer.PeriodGroup.degree`: the degree `γ ↦ 2 c(γ)`, the grading shift of a recapping
  by `γ`.
* `TauCeti.Floer.PeriodGroup.chernEquivInt`: integer coordinates with positive Chern generator
  when the Chern map is injective and nonzero; `laurentExponent` reverses these coordinates
  to make the Floer Laurent variable have positive valuation in the positive monotone case.
* `TauCeti.Floer.PeriodGroup.map`: the homomorphism of period groups induced by a homomorphism of
  class groups preserving area and Chern number.

## Main results

* `PeriodGroup.ext_iff`: a class in `Γ` is determined by its area and first Chern number;
  equivalently the kernels of area and Chern number are disjoint
  (`PeriodGroup.disjoint_ker_area_ker_chern`).
* `PeriodGroup.subsingleton_iff`: `Γ` is trivial exactly when area and Chern number vanish on
  `S`, as for symplectically aspherical manifolds.
* `PeriodGroup.chern_injective_iff`, `PeriodGroup.area_injective_iff`: the Chern number (resp.
  the area) embeds `Γ` into `ℤ` (resp. `ℝ`) exactly when its kernel on `S` lies in the kernel of
  the area (resp. the Chern number).
* `PeriodGroup.chern_injective_of_area_eq_mul_chern`,
  `PeriodGroup.isAddCyclic_of_area_eq_mul_chern`: if the area is a fixed multiple of the Chern
  number (spherical monotonicity), then the Chern number embeds `Γ` into `ℤ`, so `Γ` is cyclic.
* `PeriodGroup.area_injective_of_chern_eq_zero`: if the Chern number vanishes, then the area
  embeds `Γ` into `ℝ`.
* `PeriodGroup.negOnePow_eq_negOnePow_of_quotientMk_eq`: degrees are even, so the residue of an
  integer modulo the degrees of `Γ` determines its parity.
* `PeriodGroup.map_injective`: induced maps of period groups are injective, and they are
  bijective when the map of class groups is surjective. They are functorial (`PeriodGroup.map_id`,
  `PeriodGroup.map_comp`).

## References

* H. Hofer and D. A. Salamon, *Floer homology and Novikov rings*, in *The Floer memorial
  volume*, Progr. Math. 133 (1995), 483–524.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, the construction of
  the Novikov ring in the chapter on quantum cohomology.
-/

public section

namespace TauCeti.Floer

variable {S S' : Type*} [AddGroup S] [AddGroup S']

/-- The period group `Γ = S ⧸ (ker ω ⊓ ker c)` of a group of spherical classes `S` with symplectic
area `ω` and first Chern number `c`, written as the quotient by the kernel of `s ↦ (ω s, c s)`.

It is an abbreviation so that the quotient group API of Mathlib applies to it directly. -/
abbrev PeriodGroup (ω : S →+ ℝ) (c : S →+ ℤ) : Type _ :=
  S ⧸ (ω.prod c).ker

namespace PeriodGroup

variable (ω : S →+ ℝ) (c : S →+ ℤ)

/-- The joint period map `Γ →+ ℝ × ℤ`, recording the area and the first Chern number of a
class. It is injective (`PeriodGroup.periods_injective`). -/
def periods : PeriodGroup ω c →+ ℝ × ℤ :=
  QuotientAddGroup.kerLift (ω.prod c)

/-- The symplectic area on the period group. -/
def area : PeriodGroup ω c →+ ℝ :=
  (AddMonoidHom.fst ℝ ℤ).comp (periods ω c)

/-- The first Chern number on the period group. -/
def chern : PeriodGroup ω c →+ ℤ :=
  (AddMonoidHom.snd ℝ ℤ).comp (periods ω c)

/-- The degree `2 c(γ)` of a class `γ`: recapping an orbit by `γ` shifts its Conley–Zehnder
grading by `2 c(γ)`. It is the degree of the monomial `e^γ` of the Floer Novikov ring. -/
def degree : PeriodGroup ω c →+ ℤ :=
  2 • chern ω c

/-- The degree of a class is twice its first Chern number. -/
@[simp]
theorem degree_apply (γ : PeriodGroup ω c) : degree ω c γ = 2 * chern ω c γ := by
  simp [degree]

/-- Degrees in the period group are even. -/
theorem even_degree (γ : PeriodGroup ω c) : Even (degree ω c γ) :=
  ⟨chern ω c γ, by rw [degree_apply, two_mul]⟩

variable {ω c} in
/-- Two integers with the same residue modulo the degrees of the period group have the same
parity, since all these degrees are even. Hence the sign `(-1)^k` is a function of the residue
of `k`. -/
theorem negOnePow_eq_negOnePow_of_quotientMk_eq {k l : ℤ}
    (h : (k : ℤ ⧸ (degree ω c).range) = l) : k.negOnePow = l.negOnePow := by
  obtain ⟨γ, hγ⟩ := AddMonoidHom.mem_range.1 (QuotientAddGroup.eq.1 h)
  rw [Int.negOnePow_eq_iff, ← even_neg, neg_sub, sub_eq_neg_add, ← hγ]
  exact even_degree ω c γ

/-- The joint period map sends the class of `s` to its area and first Chern number. -/
theorem periods_mk (s : S) : periods ω c (s : PeriodGroup ω c) = (ω s, c s) := by
  rw [periods, QuotientAddGroup.kerLift_mk, AddMonoidHom.prod_apply]

/-- The area of the class of a spherical class `s` is `ω s`. -/
@[simp]
theorem area_mk (s : S) : area ω c (s : PeriodGroup ω c) = ω s := by
  rw [area, AddMonoidHom.comp_apply, periods_mk, AddMonoidHom.coe_fst]

/-- The first Chern number of the class of a spherical class `s` is `c s`. -/
@[simp]
theorem chern_mk (s : S) : chern ω c (s : PeriodGroup ω c) = c s := by
  rw [chern, AddMonoidHom.comp_apply, periods_mk, AddMonoidHom.coe_snd]

/-- The joint period map has components `PeriodGroup.area` and `PeriodGroup.chern`. -/
@[simp]
theorem periods_apply (γ : PeriodGroup ω c) : periods ω c γ = (area ω c γ, chern ω c γ) := by
  induction γ using QuotientAddGroup.induction_on with
  | H s => simp [periods_mk]

/-- The joint period map is injective. -/
theorem periods_injective : Function.Injective (periods ω c) :=
  QuotientAddGroup.kerLift_injective _

variable {ω c} in
/-- A class in the period group is determined by its area and its first Chern number. -/
@[ext (iff := false)]
theorem ext {γ γ' : PeriodGroup ω c} (harea : area ω c γ = area ω c γ')
    (hchern : chern ω c γ = chern ω c γ') : γ = γ' :=
  periods_injective ω c <| by rw [periods_apply, periods_apply, harea, hchern]

variable {ω c} in
/-- Two classes in the period group are equal exactly when they have the same area and the same
first Chern number. -/
theorem ext_iff {γ γ' : PeriodGroup ω c} :
    γ = γ' ↔ area ω c γ = area ω c γ' ∧ chern ω c γ = chern ω c γ' :=
  ⟨fun h => h ▸ ⟨rfl, rfl⟩, fun h => ext h.1 h.2⟩

variable {ω c} in
/-- Two spherical classes have the same image in the period group exactly when they have the
same area and the same first Chern number. -/
theorem mk_eq_mk_iff {s t : S} :
    (s : PeriodGroup ω c) = t ↔ ω s = ω t ∧ c s = c t := by
  rw [PeriodGroup.ext_iff, area_mk, area_mk, chern_mk, chern_mk]

/-- The areas of classes in the period group are the areas of spherical classes. -/
@[simp]
theorem range_area : (area ω c).range = ω.range := by
  ext x
  simp [QuotientAddGroup.mk_surjective.exists]

/-- The first Chern numbers of classes in the period group are those of spherical classes. -/
@[simp]
theorem range_chern : (chern ω c).range = c.range := by
  ext x
  simp [QuotientAddGroup.mk_surjective.exists]

/-- The period group is torsion-free: it embeds into `ℝ × ℤ`. -/
instance : HasUniqueDiv (PeriodGroup ω c) :=
  (periods_injective ω c).hasUniqueDiv (periods ω c)

variable {ω c} in
/-- The period group is trivial exactly when area and first Chern number vanish on every spherical
class, as they do on a symplectically aspherical manifold. -/
theorem subsingleton_iff :
    Subsingleton (PeriodGroup ω c) ↔ ∀ s, ω s = 0 ∧ c s = 0 := by
  constructor
  · intro _ s
    simpa using (mk_eq_mk_iff (ω := ω) (c := c) (s := s) (t := 0)).1 (Subsingleton.elim _ _)
  · intro h
    refine ⟨fun γ γ' => ?_⟩
    induction γ using QuotientAddGroup.induction_on with
    | H s =>
    induction γ' using QuotientAddGroup.induction_on with
    | H t => exact mk_eq_mk_iff.2 ⟨by rw [(h s).1, (h t).1], by rw [(h s).2, (h t).2]⟩

section Injective

variable {ω c}

/-- The first Chern number embeds the period group into `ℤ` exactly when every spherical class
with vanishing first Chern number has vanishing area. -/
theorem chern_injective_iff : Function.Injective (chern ω c) ↔ c.ker ≤ ω.ker := by
  rw [injective_iff_map_eq_zero]
  constructor
  · intro h s hs
    have hs' := (mk_eq_mk_iff (s := s) (t := 0)).1 (h s (by simpa using hs))
    simpa using hs'.1
  · intro h γ hγ
    induction γ using QuotientAddGroup.induction_on with
    | H s =>
      refine ext ?_ (by rw [hγ, map_zero])
      simpa using h (by simpa using hγ)

/-- The area embeds the period group into `ℝ` exactly when every spherical class with vanishing
area has vanishing first Chern number. -/
theorem area_injective_iff : Function.Injective (area ω c) ↔ ω.ker ≤ c.ker := by
  rw [injective_iff_map_eq_zero]
  constructor
  · intro h s hs
    have hs' := (mk_eq_mk_iff (s := s) (t := 0)).1 (h s (by simpa using hs))
    simpa using hs'.2
  · intro h γ hγ
    induction γ using QuotientAddGroup.induction_on with
    | H s =>
      refine ext (by rw [hγ, map_zero]) ?_
      simpa using h (by simpa using hγ)

/-- The degree is injective exactly when the first Chern number is. -/
theorem degree_injective_iff :
    Function.Injective (degree ω c) ↔ Function.Injective (chern ω c) := by
  refine ⟨fun h γ γ' hγ => h ?_, fun h γ γ' hγ => h ?_⟩
  · rw [degree_apply, degree_apply, hγ]
  · simpa using hγ

variable (ω c) in
/-- A class has degree zero exactly when its first Chern number vanishes. -/
@[simp]
theorem ker_degree : (degree ω c).ker = (chern ω c).ker := by
  ext γ
  simp [AddMonoidHom.mem_ker]

variable (ω c) in
/-- Area and first Chern number are jointly injective on the period group: the only class with
vanishing area and vanishing first Chern number is zero. -/
theorem disjoint_ker_area_ker_chern : Disjoint (area ω c).ker (chern ω c).ker :=
  disjoint_iff_inf_le.2 fun γ hγ => AddSubgroup.mem_bot.2 <|
    ext (by rw [AddMonoidHom.mem_ker.1 hγ.1, map_zero])
      (by rw [AddMonoidHom.mem_ker.1 hγ.2, map_zero])

/-- If every spherical class with vanishing first Chern number has vanishing area, the period
group is cyclic. -/
theorem isAddCyclic_of_ker_le (h : c.ker ≤ ω.ker) : IsAddCyclic (PeriodGroup ω c) :=
  isAddCyclic_of_injective (chern ω c) (chern_injective_iff.2 h)

end Injective

section Monotone

variable {ω c} {τ : ℝ}

/-- If the area of every spherical class is `τ` times its first Chern number, the same holds on
the period group. -/
theorem area_eq_mul_chern (h : ∀ s, ω s = τ * c s) (γ : PeriodGroup ω c) :
    area ω c γ = τ * chern ω c γ := by
  induction γ using QuotientAddGroup.induction_on with
  | H s => simpa using h s

/-- For a spherically monotone pair, where the area is a fixed multiple of the first Chern number,
every spherical class with vanishing first Chern number has vanishing area. -/
theorem ker_le_ker_of_area_eq_mul_chern (h : ∀ s, ω s = τ * c s) : c.ker ≤ ω.ker := fun s hs => by
  rw [AddMonoidHom.mem_ker] at hs ⊢
  simp [h s, hs]

/-- For a spherically monotone pair, where the area is a fixed multiple of the first Chern number,
the first Chern number embeds the period group into `ℤ`. -/
theorem chern_injective_of_area_eq_mul_chern (h : ∀ s, ω s = τ * c s) :
    Function.Injective (chern ω c) :=
  chern_injective_iff.2 (ker_le_ker_of_area_eq_mul_chern h)

/-- For a spherically monotone pair, the degree embeds the period group into `ℤ`. -/
theorem degree_injective_of_area_eq_mul_chern (h : ∀ s, ω s = τ * c s) :
    Function.Injective (degree ω c) :=
  degree_injective_iff.2 (chern_injective_of_area_eq_mul_chern h)

/-- For a spherically monotone pair the period group is cyclic. -/
theorem isAddCyclic_of_area_eq_mul_chern (h : ∀ s, ω s = τ * c s) :
    IsAddCyclic (PeriodGroup ω c) :=
  isAddCyclic_of_ker_le (ker_le_ker_of_area_eq_mul_chern h)

end Monotone

section ChernZero

variable {ω c}

/-- If the first Chern number vanishes on spherical classes, it vanishes on the period group. -/
theorem chern_eq_zero (h : ∀ s, c s = 0) (γ : PeriodGroup ω c) : chern ω c γ = 0 := by
  induction γ using QuotientAddGroup.induction_on with
  | H s => simpa using h s

/-- If the first Chern number vanishes on spherical classes, the area embeds the period group
into `ℝ`. -/
theorem area_injective_of_chern_eq_zero (h : ∀ s, c s = 0) :
    Function.Injective (area ω c) :=
  area_injective_iff.2 fun s _ => h s

end ChernZero

section Laurent

variable {ω c}

/-- Integer coordinates on a period group whose Chern map is injective and nonzero.
The inverse image of one is the generator with positive Chern number. -/
noncomputable def chernEquivInt (hker : c.ker ≤ ω.ker) (hc : c ≠ 0) : PeriodGroup ω c ≃+ ℤ :=
  ((AddMonoidHom.ofInjective (chern_injective_iff.mpr hker)).trans
    (AddEquiv.addSubgroupCongr (range_chern ω c))).trans (c.rangeOrderAddEquivInt hc).toAddEquiv

/-- The positive generator has strictly positive Chern number, the minimal Chern number. -/
theorem chern_chernEquivInt_symm_pos (hker : c.ker ≤ ω.ker) (hc : c ≠ 0) :
    0 < chern ω c ((chernEquivInt hker hc).symm 1) := by
  have h := c.rangeOrderAddEquivInt_symm_one_pos hc
  -- The underlying additive equivalence and the ordered equivalence have the same inverse.
  have he : (c.rangeOrderAddEquivInt hc).toAddEquiv.symm 1 =
      (c.rangeOrderAddEquivInt hc).symm 1 := rfl
  simpa only [chernEquivInt, AddEquiv.symm_trans_apply, he,
    AddEquiv.addSubgroupCongr_symm_apply,
    AddMonoidHom.apply_ofInjective_symm] using h

/-- The Chern number in integer coordinates is the exponent times the minimal Chern number. -/
theorem chern_chernEquivInt_symm (hker : c.ker ≤ ω.ker) (hc : c ≠ 0) (k : ℤ) :
    chern ω c ((chernEquivInt hker hc).symm k) =
      k * chern ω c ((chernEquivInt hker hc).symm 1) := by
  have hk : k = k • (1 : ℤ) := by simp
  conv_lhs => rw [hk]
  rw [map_zsmul, map_zsmul, zsmul_eq_mul, Int.cast_id]

/-- The Chern number of a period class determines its integer exponent by multiplication by
the minimal Chern number. -/
theorem chern_eq_mul_chernEquivInt (hker : c.ker ≤ ω.ker) (hc : c ≠ 0)
    (γ : PeriodGroup ω c) :
    chern ω c γ = chernEquivInt hker hc γ *
      chern ω c ((chernEquivInt hker hc).symm 1) := by
  simpa only [AddEquiv.symm_apply_apply] using
    chern_chernEquivInt_symm hker hc (chernEquivInt hker hc γ)

/-- Laurent exponents for Floer coefficients. The variable corresponds to the negative of the
positive Chern generator, so its valuation is positive on positively monotone targets. -/
noncomputable def laurentExponent (hker : c.ker ≤ ω.ker) (hc : c ≠ 0) :
    PeriodGroup ω c ≃+ ℤ :=
  (chernEquivInt hker hc).trans (AddEquiv.neg ℤ)

/-- A Floer Laurent exponent is the negative of the positive-Chern integer coordinate. -/
@[simp]
theorem laurentExponent_apply (hker : c.ker ≤ ω.ker) (hc : c ≠ 0)
    (γ : PeriodGroup ω c) :
    laurentExponent hker hc γ = -chernEquivInt hker hc γ :=
  (rfl)

/-- The class of the Laurent monomial of exponent `k` has Chern number `-k N`,
where `N` is the positive minimal Chern number. -/
@[simp]
theorem chern_laurentExponent_symm (hker : c.ker ≤ ω.ker) (hc : c ≠ 0) (k : ℤ) :
    chern ω c ((laurentExponent hker hc).symm k) =
      -k * chern ω c ((chernEquivInt hker hc).symm 1) := by
  simpa only [laurentExponent, AddEquiv.symm_trans_apply, AddEquiv.neg_symm,
    AddEquiv.neg_apply] using
    chern_chernEquivInt_symm hker hc (-k)

/-- In the monotone case the area of a Laurent monomial is minus its exponent times the area
of the positive Chern generator. When `0 < τ`, positive exponents have positive Floer valuation. -/
theorem area_laurentExponent_symm {τ : ℝ} (h : ∀ s, ω s = τ * c s) (hc : c ≠ 0)
    (k : ℤ) :
    area ω c ((laurentExponent (ker_le_ker_of_area_eq_mul_chern h) hc).symm k) =
      -(τ * chern ω c ((chernEquivInt (ker_le_ker_of_area_eq_mul_chern h) hc).symm 1)) * k := by
  rw [area_eq_mul_chern h, chern_laurentExponent_symm]
  push_cast
  ring

end Laurent

section Map

variable {ω c} {ω' : S' →+ ℝ} {c' : S' →+ ℤ}

/-- A homomorphism of class groups preserving area and first Chern number induces a homomorphism
of period groups. -/
def map (f : S →+ S') (hω : ω'.comp f = ω) (hc : c'.comp f = c) :
    PeriodGroup ω c →+ PeriodGroup ω' c' :=
  QuotientAddGroup.map _ _ f fun s hs => by
    subst hω hc
    simpa using hs

variable (f : S →+ S') (hω : ω'.comp f = ω) (hc : c'.comp f = c)

/-- The induced map sends the class of `s` to the class of `f s`. -/
@[simp]
theorem map_mk (s : S) : map f hω hc (s : PeriodGroup ω c) = (f s : PeriodGroup ω' c') :=
  QuotientAddGroup.map_mk _ _ _ _ s

/-- The induced map of period groups preserves area. -/
@[simp]
theorem area_map (γ : PeriodGroup ω c) : area ω' c' (map f hω hc γ) = area ω c γ := by
  induction γ using QuotientAddGroup.induction_on with
  | H s => simp [← hω]

/-- The induced map of period groups preserves the first Chern number. -/
@[simp]
theorem chern_map (γ : PeriodGroup ω c) : chern ω' c' (map f hω hc γ) = chern ω c γ := by
  induction γ using QuotientAddGroup.induction_on with
  | H s => simp [← hc]

/-- Induced maps of period groups are injective: classes are separated by area and first Chern
number, which the map preserves. -/
theorem map_injective : Function.Injective (map f hω hc) := fun γ γ' hγ =>
  ext (by rw [← area_map f hω hc, hγ, area_map]) (by rw [← chern_map f hω hc, hγ, chern_map])

/-- The map of period groups induced by a surjective map of class groups is surjective. -/
theorem map_surjective (hf : Function.Surjective f) : Function.Surjective (map f hω hc) :=
  QuotientAddGroup.map_surjective_of_surjective _ _ f (QuotientAddGroup.mk_surjective.comp hf) _

variable (ω c) in
/-- The map of period groups induced by the identity is the identity. -/
@[simp]
theorem map_id : map (AddMonoidHom.id S) ω.comp_id c.comp_id = AddMonoidHom.id (PeriodGroup ω c) :=
  AddMonoidHom.ext fun _ => ext (by simp) (by simp)

/-- Maps of period groups induced by composable maps of class groups compose. -/
@[simp]
theorem map_comp {S'' : Type*} [AddGroup S''] {ω'' : S'' →+ ℝ} {c'' : S'' →+ ℤ} (g : S' →+ S'')
    (hω' : ω''.comp g = ω') (hc' : c''.comp g = c') :
    (map g hω' hc').comp (map f hω hc) =
      map (g.comp f) (by rw [← AddMonoidHom.comp_assoc, hω', hω])
        (by rw [← AddMonoidHom.comp_assoc, hc', hc]) :=
  AddMonoidHom.ext fun _ => ext (by simp) (by simp)

end Map

end PeriodGroup

end TauCeti.Floer

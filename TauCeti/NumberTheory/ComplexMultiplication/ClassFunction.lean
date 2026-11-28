/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.FieldTheory.Galois.Infinite
import TauCeti.FieldTheory.Galois.FixedField
public import TauCeti.RepresentationTheory.CharacterTable.ClassFunction.Periods

/-!
# CM class functions and their finite quotients

For the absolute Galois group of the rationals with a complex conjugation `c`,
`CMClassFunction ℚ c` is Colmez's space CM⁰. Its elements are locally constant class functions
for which `f(x) + f(cx)` is constant. The same definition on a finite Galois quotient lets one
pull its class functions back and compare them on common refinements.

The finite quotient can always be chosen with central image of `c`. In fact the quotient by all
right periods of `f` has this property. This makes it possible to expand `f` in ordinary
characters of a finite group with central complex conjugation.

## References

* F. Andreatta, E. Z. Goren, B. Howard and K. Madapusi Pera, *Faltings heights of abelian
  varieties with complex multiplication*, Ann. of Math. 187 (2018), §9.1.
* P. Colmez, *Périodes des variétés abéliennes à multiplication complexe*, Ann. of Math.
  138 (1993), §0.
-/

public section

namespace TauCeti

variable (k : Type*) [Semiring k] {G : Type*} [Group G] [TopologicalSpace G]

/-- Locally constant class functions whose sum with their left translate by `c` is constant.
The CM class functions take rational values and use a complex conjugation as `c`. -/
def CMClassFunction (c : G) : Submodule k (ClassFunction k G) where
  carrier := {f | IsLocallyConstant f.val ∧ ∀ x, f.val x + f.val (c * x) = f.val 1 + f.val c}
  zero_mem' := ⟨IsLocallyConstant.zero, fun _ ↦ rfl⟩
  add_mem' {f g} hf hg := ⟨hf.1.add hg.1, fun x ↦ by
    simpa only [Submodule.coe_add, Pi.add_apply, add_add_add_comm] using
      congrArg₂ (· + ·) (hf.2 x) (hg.2 x)⟩
  smul_mem' r f hf := ⟨hf.1.comp (r • ·), fun x ↦ by
    simpa only [Submodule.coe_smul, Pi.smul_apply, smul_add] using congrArg (r • ·) (hf.2 x)⟩

namespace CMClassFunction

variable {k} {c : G} {f : ClassFunction k G}

/-- Membership is local constancy and the complement identity, with the constant evaluated
at the identity element. -/
theorem mem_iff : f ∈ CMClassFunction k c ↔
    IsLocallyConstant f.val ∧ ∀ x, f.val x + f.val (c * x) = f.val 1 + f.val c :=
  Iff.rfl

/-- Constant class functions satisfy the CM condition for every distinguished element. -/
@[simp]
theorem ofConjClasses_const_mem (r : k) :
    ClassFunction.ofConjClasses (Function.const (ConjClasses G) r) ∈ CMClassFunction k c := by
  refine mem_iff.mpr ⟨?_, fun x ↦ by simp⟩
  simpa only [funext (ClassFunction.ofConjClasses_apply _), Function.const_apply,
    Function.const_def] using IsLocallyConstant.const (X := G) r

/-- The constant function with value one belongs to CM⁰. -/
@[simp]
theorem ofConjClasses_one_mem : ClassFunction.ofConjClasses 1 ∈ CMClassFunction k c := by
  simpa only [Function.const_one] using ofConjClasses_const_mem (c := c) (1 : k)

/-- Changing the distinguished element by conjugacy preserves the space of CM class functions. -/
theorem eq_of_isConj {d : G} (h : IsConj c d) : CMClassFunction k c = CMClassFunction k d := by
  suffices ∀ {a b : G}, IsConj a b → CMClassFunction k a ≤ CMClassFunction k b from
    le_antisymm (this h) (this h.symm)
  intro a b hab f hf
  obtain ⟨g, rfl⟩ := isConj_iff.mp hab
  refine mem_iff.mpr ⟨(mem_iff.mp hf).1, fun x ↦ ?_⟩
  have hinv (y : G) : f.val (g⁻¹ * y * g) = f.val y := by
    simpa only [inv_inv] using ClassFunction.apply_conj f g⁻¹ y
  have hmul : g⁻¹ * ((g * a * g⁻¹) * x) * g = a * (g⁻¹ * x * g) := by group
  simpa only [← hmul, hinv, ClassFunction.apply_conj] using (mem_iff.mp hf).2 (g⁻¹ * x * g)

variable {H : Type*} [Group H] [TopologicalSpace H]

/-- Continuous pullback preserves the CM complement condition. Iterated pullbacks are given by
`ClassFunction.comap_comp`. -/
theorem comap_mem (π : G →* H) (hπ : Continuous π) {a : ClassFunction k H}
    (ha : a ∈ CMClassFunction k (π c)) : ClassFunction.comap π a ∈ CMClassFunction k c := by
  obtain ⟨hloc, h⟩ := mem_iff.mp ha
  refine mem_iff.mpr ⟨?_, fun x ↦ by simpa using h (π x)⟩
  rw [funext (ClassFunction.comap_apply π a)]
  exact hloc.comp_continuous hπ

/-- A quotient map detects the CM condition as well as preserving it. -/
theorem comap_mem_iff (π : G →* H) (hπ : Topology.IsQuotientMap π) {a : ClassFunction k H} :
    ClassFunction.comap π a ∈ CMClassFunction k c ↔ a ∈ CMClassFunction k (π c) := by
  refine ⟨fun ha ↦ ?_, comap_mem π hπ.continuous⟩
  obtain ⟨hloc, h⟩ := mem_iff.mp ha
  refine mem_iff.mpr ⟨fun s ↦ hπ.isOpen_preimage.mp ?_, hπ.surjective.forall.mpr fun x ↦ ?_⟩
  · simpa only [Set.preimage_preimage, Function.comp_def, ← ClassFunction.comap_apply] using hloc s
  · simpa using h x

/-- Every CM class function on a compact group is the pullback of a unique CM class function
on a finite quotient with central image of `c`, once that quotient is fixed. -/
theorem exists_openNormalSubgroup_comap_eq [IsLeftCancelAdd k] [ContinuousMul G]
    [CompactSpace G] (hf : f ∈ CMClassFunction k c) :
    ∃ U : OpenNormalSubgroup G, (c : G ⧸ U.toSubgroup) ∈ Subgroup.center _ ∧
      ∃! a : CMClassFunction k (c : G ⧸ U.toSubgroup),
        ClassFunction.comap (QuotientGroup.mk' U.toSubgroup) a.val = f := by
  let U : OpenNormalSubgroup G :=
    { rightTranslationStabilizer f.val with
      isOpen' := isOpen_rightTranslationStabilizer (mem_iff.mp hf).1
      isNormal' := inferInstance }
  let π := QuotientGroup.mk' U.toSubgroup
  have hπ := QuotientGroup.mk'_surjective U.toSubgroup
  have hker : π.ker ≤ rightTranslationStabilizer f.val := by simp [π, U]
  obtain ⟨a, ha⟩ := (ClassFunction.mem_range_comap_iff f hπ).mpr hker
  have hamem := (comap_mem_iff π (QuotientGroup.isQuotientMap_mk _) (c := c)).mp (ha ▸ hf)
  have hc := ClassFunction.mk_mem_center_quotient_rightTranslationStabilizer f (mem_iff.mp hf).2
  exact ⟨U, hc, ⟨a, hamem⟩, ha,
    fun _ hb ↦ Subtype.ext (ClassFunction.comap_injective hπ (hb.trans ha.symm))⟩

/-- A class function on a Galois group satisfies the CM condition exactly when it comes from
a finite Galois subextension on which the restriction of `c` is central. In particular this
applies with the Krull topology on the absolute Galois group of the rationals. -/
theorem mem_iff_exists_finiteGaloisIntermediateField [IsLeftCancelAdd k]
    {F L : Type*} [Field F] [Field L] [Algebra F L] [IsGalois F L]
    {c : Gal(L/F)} {f : ClassFunction k Gal(L/F)} :
    f ∈ CMClassFunction k c ↔ ∃ K : FiniteGaloisIntermediateField F L,
      AlgEquiv.restrictNormalHom K c ∈ Subgroup.center Gal(K/F) ∧
      ∃ a : CMClassFunction k (AlgEquiv.restrictNormalHom K c),
        ClassFunction.comap (AlgEquiv.restrictNormalHom K) a.val = f := by
  constructor
  · intro hf
    obtain ⟨U, hc, a, ha, -⟩ := exists_openNormalSubgroup_comap_eq hf
    let H : ClosedSubgroup Gal(L/F) := ⟨U.toSubgroup, U.toOpenSubgroup.isClosed⟩
    let K : FiniteGaloisIntermediateField F L :=
      { toIntermediateField := IntermediateField.fixedField U.toSubgroup
        finiteDimensional := IntermediateField.finiteDimensional_fixedField_of_isOpen U.isOpen }
    have : FiniteDimensional F K := K.finiteDimensional
    let e : Gal(L/F) ⧸ U.toSubgroup ≃* Gal(K/F) := InfiniteGalois.normalAutEquivQuotient H
    have he (x : Gal(L/F)) : e x = AlgEquiv.restrictNormalHom K x :=
      InfiniteGalois.normalAutEquivQuotient_apply H x
    have he' (x : Gal(L/F)) : e.symm (AlgEquiv.restrictNormalHom K x) = ↑x := by
      rw [← he, e.symm_apply_apply]
    refine ⟨K, ?_,
      ⟨ClassFunction.comap e.symm.toMonoidHom a.val, ?_⟩, ?_⟩
    · rw [← he c]
      exact MulEquivClass.apply_mem_center e hc
    · apply comap_mem _ continuous_of_discreteTopology
      rw [MulEquiv.coe_toMonoidHom, he']
      exact a.property
    · refine Subtype.ext (funext fun x ↦ ?_)
      simpa only [ClassFunction.comap_apply, QuotientGroup.mk'_apply,
        MulEquiv.coe_toMonoidHom, he'] using
        congrArg (fun b : ClassFunction k Gal(L/F) ↦ b.val x) ha
  · rintro ⟨K, -, a, rfl⟩
    exact comap_mem _ (InfiniteGalois.restrictNormalHom_continuous K.toIntermediateField) a.property

end CMClassFunction

end TauCeti

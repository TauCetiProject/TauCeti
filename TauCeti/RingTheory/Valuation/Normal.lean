/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Fixed
public import Mathlib.FieldTheory.Normal.Basic
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import TauCeti.FieldTheory.Normal.FixedField
import TauCeti.RingTheory.Valuation.AlgebraicExtension
import TauCeti.RingTheory.Valuation.ValuationSubring

/-!
# Extensions of valuation subrings along purely inseparable and normal extensions

Let `L / K` be a field extension. A valuation subring of `K` always extends to `L`
(`ValuationSubring.comap_surjective`). This file proves two structural theorems about the fibre of
extensions:

* Along a **purely inseparable** extension `L / K`, every element has a `qⁿ`-th power in `K`, and
  membership in a valuation subring is detected by positive powers. Thus restriction of valuation
  subrings is injective (`ValuationSubring.comap_injective_of_isPurelyInseparable`), hence
  bijective (`ValuationSubring.comap_bijective_of_isPurelyInseparable`).
* Along the fixed field of a **finite group** `G` acting on `L`, any two valuation subrings of `L`
  with the same restriction to `Lᴳ` are `G`-conjugate
  (`ValuationSubring.exists_smul_comap_eq_of_comap_eq`). If their orbits were disjoint, the
  approximation theorem for algebraic extensions
  (`ValuationSubring.exists_valuation_eq_one_and_lt_one`) produces an element `x ∈ L` with
  `v₁(g • x) < 1` and `v₂(g • x) = 1` for every `g ∈ G`, whose orbit product `∏ g, g • x ∈ Lᴳ`
  then has valuation `1` under `v₂` (hence under `v₁`) and valuation `< 1` under `v₁`.
* Combining the two via the splitting `K ⊆ L^{Aut(L/K)} ⊆ L` of a **normal** extension with finite
  automorphism group (`TauCeti.IntermediateField.isPurelyInseparable_fixedField_top`), any two
  valuation subrings of `L` with the same restriction to `K` are `Aut(L/K)`-conjugate
  (`ValuationSubring.exists_algEquiv_comap_eq_of_comap_eq`).

## Main results

* `ValuationSubring.comap_injective_of_isPurelyInseparable`,
  `ValuationSubring.comap_bijective_of_isPurelyInseparable`: a valuation subring has a unique
  extension along a purely inseparable field extension.
* `ValuationSubring.exists_smul_comap_eq_of_comap_eq`: two valuation subrings of `L` with the same
  restriction to `FixedPoints.subfield G L` are conjugate under a finite group `G`.
* `ValuationSubring.exists_algEquiv_comap_eq_of_comap_eq`: two valuation subrings of a normal
  extension `L / K` with finite `Aut(L/K)` having the same restriction to `K` are conjugate by an
  element of `L ≃ₐ[K] L`.

## References

* A. J. Engler and A. Prestel, *Valued Fields*, Springer, 2005, Theorem 3.2.15.
* N. Bourbaki, *Commutative Algebra*, Ch. VI, §8.6, Proposition 6 and Corollary 1.
-/

public section

namespace ValuationSubring

section PurelyInseparable

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- **Uniqueness of valuation extensions along a purely inseparable extension.** If `L / K` is
purely inseparable, then every valuation subring of `L` is determined by its restriction to `K`:
for each `x ∈ L`, some positive power `x ^ (q ^ n)` lies in `K`, and a valuation subring contains
`x` iff it contains `x ^ (q ^ n)`. -/
theorem comap_injective_of_isPurelyInseparable [IsPurelyInseparable K L] :
    Function.Injective (fun W : ValuationSubring L ↦ W.comap (algebraMap K L)) := by
  intro W₁ W₂ h
  dsimp only at h
  obtain ⟨q, hq⟩ := ExpChar.exists K
  have hq0 : q ≠ 0 := by
    rcases hq with _ | hp
    · exact one_ne_zero
    · exact hp.ne_zero
  ext x
  obtain ⟨n, a, ha⟩ := IsPurelyInseparable.pow_mem K q x
  have hm : q ^ n ≠ 0 := pow_ne_zero n hq0
  have hmem (W : ValuationSubring L) : x ∈ W ↔ a ∈ W.comap (algebraMap K L) := by
    rw [mem_comap, ha, ← W.valuation_le_one_iff, ← W.valuation_le_one_iff, map_pow]
    exact ⟨fun hx ↦ pow_le_one' hx _,
      fun hpow ↦ le_of_pow_le_pow_left₀ hm zero_le (by simpa using hpow)⟩
  rw [hmem W₁, h, ← hmem W₂]

/-- Restriction of valuation subrings along a purely inseparable field extension is bijective. -/
theorem comap_bijective_of_isPurelyInseparable [IsPurelyInseparable K L] :
    Function.Bijective (fun W : ValuationSubring L ↦ W.comap (algebraMap K L)) :=
  ⟨comap_injective_of_isPurelyInseparable, comap_surjective (algebraMap K L)⟩

end PurelyInseparable

section FiniteGroup

/-- `V.valuation x = 1` iff `x` belongs to `V` and is not a nonunit of `V`. -/
private theorem valuation_eq_one_iff_mem_and_notMem_nonunits {L : Type*} [Field L]
    (V : ValuationSubring L) {x : L} :
    V.valuation x = 1 ↔ x ∈ V ∧ x ∉ V.nonunits := by
  rw [← V.valuation_le_one_iff, V.mem_nonunits_iff, not_lt]
  exact ⟨fun h ↦ ⟨h.le, h.ge⟩, fun ⟨h₁, h₂⟩ ↦ le_antisymm h₁ h₂⟩

/-- Given two disjoint finite sets `S₁`, `S₂` of extensions of `O` to an algebraic extension `L/K`,
there is `x ∈ L` with `A.valuation x < 1` for all `A ∈ S₁` and `B.valuation x = 1` for all
`B ∈ S₂`. -/
private theorem exists_valuation_lt_one_and_eq_one {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L] (O : ValuationSubring K) {S₁ S₂ : Finset (ValuationSubring L)}
    (hdisj : Disjoint S₁ S₂)
    (hS₁ : ∀ A ∈ S₁, A.comap (algebraMap K L) = O)
    (hS₂ : ∀ B ∈ S₂, B.comap (algebraMap K L) = O) :
    ∃ x : L, (∀ A ∈ S₁, A.valuation x < 1) ∧ (∀ B ∈ S₂, B.valuation x = 1) := by
  classical
  have hS : ∀ A ∈ S₁ ∪ S₂, A.comap (algebraMap K L) = O := fun A hA ↦
    (Finset.mem_union.mp hA).elim (hS₁ A) (hS₂ A)
  obtain ⟨e, he⟩ := exists_valuation_eq_one_and_lt_one O (S₁ ∪ S₂) hS
  refine ⟨∑ B ∈ S₂, e B, fun A hA ↦ ?_, fun B hB ↦ ?_⟩
  · exact Valuation.map_sum_lt _ one_ne_zero fun B hB ↦
      (he B (Finset.mem_union_right _ hB)).2 A (Finset.mem_union_left _ hA)
        fun hAB ↦ Finset.disjoint_left.mp hdisj hA (hAB ▸ hB)
  · have hrest : B.valuation (∑ C ∈ S₂.erase B, e C) < 1 :=
      Valuation.map_sum_lt _ one_ne_zero fun C hC ↦
        (he C (Finset.mem_union_right _ (Finset.mem_of_mem_erase hC))).2 B
          (Finset.mem_union_right _ hB) (Finset.ne_of_mem_erase hC).symm
    rw [← Finset.add_sum_erase _ _ hB,
      B.valuation.map_add_eq_of_lt_left
        (hrest.trans_eq (he B (Finset.mem_union_right _ hB)).1.symm),
      (he B (Finset.mem_union_right _ hB)).1]

/-- Non-conjugate valuation subrings have disjoint `G`-orbits under `comap`. -/
private theorem disjoint_image_comap_smul (G : Type*) [Group G] [Fintype G] {L : Type*} [Field L]
    [MulSemiringAction G L] {V₁ V₂ : ValuationSubring L}
    (hconj : ¬ ∃ g : G, V₁.comap (MulSemiringAction.toRingHom G L g) = V₂) :
    letI := Classical.decEq (ValuationSubring L)
    Disjoint (Finset.univ.image fun g : G ↦ V₁.comap (MulSemiringAction.toRingHom G L g))
      (Finset.univ.image fun g : G ↦ V₂.comap (MulSemiringAction.toRingHom G L g)) := by
  classical
  refine Finset.disjoint_left.mpr fun W hW₁ hW₂ ↦ ?_
  obtain ⟨g₁, -, rfl⟩ := Finset.mem_image.mp hW₁
  obtain ⟨g₂, -, hW⟩ := Finset.mem_image.mp hW₂
  refine hconj ⟨g₁ * g₂⁻¹, ?_⟩
  have hpull := congrArg (fun U : ValuationSubring L ↦
    U.comap (MulSemiringAction.toRingHom G L g₂⁻¹)) hW.symm
  ext z
  simpa only [mem_comap, MulSemiringAction.toRingHom_apply, mul_smul, smul_inv_smul] using
    congr(z ∈ $hpull).to_iff

variable (G : Type*) [Group G] [Finite G] {L : Type*} [Field L] [MulSemiringAction G L]

/-- **Conjugacy of valuation subrings over a finite-group fixed field.** Let a finite group `G`
act by field automorphisms on `L`. Two valuation subrings of `L` with the same restriction to
`FixedPoints.subfield G L` are conjugate by an element of `G`. -/
theorem exists_smul_comap_eq_of_comap_eq {V₁ V₂ : ValuationSubring L}
    (h : V₁.comap (FixedPoints.subfield G L).subtype =
      V₂.comap (FixedPoints.subfield G L).subtype) :
    ∃ g : G, V₁.comap (MulSemiringAction.toRingHom G L g) = V₂ := by
  classical
  cases nonempty_fintype G
  let F := FixedPoints.subfield G L
  have : Algebra.IsAlgebraic F L := ⟨fun x ↦ (FixedPoints.isIntegral G L x).isAlgebraic⟩
  by_contra hconj
  have hcomap_smul (V : ValuationSubring L) (g : G) :
      (V.comap (MulSemiringAction.toRingHom G L g)).comap (algebraMap F L) = V.comap F.subtype := by
    rw [comap_comap]
    exact congrArg V.comap (RingHom.ext fun a ↦ a.2 g)
  obtain ⟨x, hx₁', hx₂'⟩ := exists_valuation_lt_one_and_eq_one (V₁.comap F.subtype)
    (disjoint_image_comap_smul G hconj)
    (fun A hA ↦ by obtain ⟨g, -, rfl⟩ := Finset.mem_image.mp hA; exact hcomap_smul V₁ g)
    (fun B hB ↦ by
      obtain ⟨g, -, rfl⟩ := Finset.mem_image.mp hB
      exact (hcomap_smul V₂ g).trans h.symm)
  have hx₁ (g : G) : V₁.valuation (g • x) < 1 := by
    have hlt := hx₁' _ (Finset.mem_image_of_mem _ (Finset.mem_univ g))
    exact V₁.mem_nonunits_iff.mp
      (mem_nonunits_comap.mp ((_ : ValuationSubring L).mem_nonunits_iff.mpr hlt))
  have hx₂ (g : G) : V₂.valuation (g • x) = 1 := by
    have heq := hx₂' _ (Finset.mem_image_of_mem _ (Finset.mem_univ g))
    have ⟨hm, hn⟩ := (valuation_eq_one_iff_mem_and_notMem_nonunits _).mp heq
    exact (valuation_eq_one_iff_mem_and_notMem_nonunits V₂).mpr
      ⟨mem_comap.mp hm, fun hnon ↦ hn (mem_nonunits_comap.mpr hnon)⟩
  -- The orbit product `a = ∏ g, g • x ∈ F` has `v₂(a) = 1`, hence `v₁(a) = 1`,
  -- contradicting `v₁(a) < 1`.
  let a : F := ⟨∏ g : G, g • x, Finset.smul_prod_perm x⟩
  have ha₂ : V₂.valuation (a : L) = 1 := by
    change V₂.valuation (∏ g : G, g • x) = 1
    rw [map_prod]
    exact Finset.prod_eq_one fun g _ ↦ hx₂ g
  have ha₁_eq : V₁.valuation (a : L) = 1 := by
    have ⟨hm, hn⟩ := (valuation_eq_one_iff_mem_and_notMem_nonunits V₂).mp ha₂
    have hm₁ : a ∈ V₁.comap F.subtype := h ▸ hm
    have hn₁ : a ∉ (V₁.comap F.subtype).nonunits := fun hnon ↦ hn (mem_nonunits_comap.mp (h ▸ hnon))
    exact (valuation_eq_one_iff_mem_and_notMem_nonunits V₁).mpr
      ⟨mem_comap.mp hm₁, fun hnon ↦ hn₁ (mem_nonunits_comap.mpr hnon)⟩
  have ha₁_lt : V₁.valuation (a : L) < 1 := by
    change V₁.valuation (∏ g : G, g • x) < 1
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ (1 : G)), map_mul, map_prod]
    exact mul_lt_one_of_lt_of_le (hx₁ 1) (Finset.prod_le_one fun g _ ↦ (hx₁ g).le)
  exact ha₁_lt.ne ha₁_eq

end FiniteGroup

section Normal

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [Normal K L] [Finite (L ≃ₐ[K] L)]

/-- **Conjugacy of valuation subrings in a normal extension with finite automorphism group.**
If `L / K` is normal with `Aut(L/K)` finite, any two valuation subrings of `L` with the same
restriction to `K` differ by an element of `L ≃ₐ[K] L`. -/
theorem exists_algEquiv_comap_eq_of_comap_eq {V₁ V₂ : ValuationSubring L}
    (h : V₁.comap (algebraMap K L) = V₂.comap (algebraMap K L)) :
    ∃ σ : L ≃ₐ[K] L, V₁.comap (σ : L →+* L) = V₂ := by
  set F := IntermediateField.fixedField (⊤ : Subgroup (L ≃ₐ[K] L))
  have : IsPurelyInseparable K F :=
    TauCeti.IntermediateField.isPurelyInseparable_fixedField_top K L
  have hF : V₁.comap F.val.toRingHom = V₂.comap F.val.toRingHom := by
    refine comap_injective_of_isPurelyInseparable (K := K) (L := F) ?_
    have hcomp : F.val.toRingHom.comp (algebraMap K F) = algebraMap K L :=
      RingHom.ext fun _ ↦ rfl
    simpa only [comap_comap, hcomp] using h
  have hfixed : V₁.comap (FixedPoints.subfield (L ≃ₐ[K] L) L).subtype =
      V₂.comap (FixedPoints.subfield (L ≃ₐ[K] L) L).subtype := by
    ext x
    have hx : (x : L) ∈ F := fun ⟨σ, _⟩ ↦ x.2 σ
    simpa [mem_comap] using congr((⟨x.1, hx⟩ : F) ∈ $hF)
  obtain ⟨σ, hσ⟩ := exists_smul_comap_eq_of_comap_eq (L ≃ₐ[K] L) hfixed
  exact ⟨σ, hσ⟩

end Normal

end ValuationSubring

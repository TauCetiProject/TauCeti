/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.GlobalExistence.UpwardClosure
public import TauCeti.NumberTheory.ClassFieldTheory.Global.Kummer.Index
public import TauCeti.NumberTheory.ClassFieldTheory.Global.Kummer.Layer
public import TauCeti.NumberTheory.ClassFieldTheory.Global.Kummer.Norm
import TauCeti.NumberTheory.ClassFieldTheory.Global.Reciprocity
import TauCeti.NumberTheory.NumberField.Global.Ideles.Ray.OpenSubgroup
import TauCeti.NumberTheory.NumberField.Kummer.Unramified
import TauCeti.RingTheory.ClassGroup.HeightOneSpectrum

/-!
# The Kummer case of global existence

Let `K` be a number field containing the `p`-th roots of unity for a prime `p`. This file proves
the **Kummer case** of the global existence theorem (Milne, *Class Field Theory*, VII, Lemma 9.3):
every open subgroup `N` of the idele class group `C_K` containing the `p`-th powers is the norm
subgroup of a finite abelian extension of `K`
(`exists_abelianLayer_globalNormSubgroup_eq_of_pow_mem`).

The proof uses an auxiliary Kummer extension: the Kummer field `M = K(U_S^{1/p})` of the
`S`-units, cut out by the Kummer layer `kummerLayer p (S.unit K)`, for a finite set `S` of finite
places containing the places above `p` and generating the ideal class group. Its norm subgroup is
contained in `N` but need not equal it. Write `E_S` for the Kummer idele subgroup
`auxiliaryKummerIdeleSubgroup S ∅ p` of ideles that are `p`-th powers at `S` and at every infinite
place and units elsewhere. Then:

* the norm subgroup of `M/K` is the image of `E_S` in `C_K`
  (`globalNormSubgroup_kummerLayer_sUnits`). The image of `E_S` consists of norms, since `M/K` has
  exponent `p` and is unramified outside `S`, and both subgroups have index `p ^ (#S + r₁ + r₂)`:
  the image of `E_S` by the product formula and the `S`-unit theorem, and the norm subgroup by the
  norm index theorem `[C_K : N_{M/K}(C_M)] = [M : K]` together with the Kummer degree of `M`;
* an open subgroup `N` contains a ray subgroup, so once `S` also contains the finite part of its
  modulus, every element of `E_S` is a `p`-th power times an idele of that ray subgroup, and
  `N ⊇ C_Kᵖ` contains the image of `E_S`
  (`auxiliaryKummerIdeleClassSubgroup_le_of_raySubgroup_le`).

Hence `N` contains the norm subgroup of `M/K`, and upward closure of global norm subgroups
(`exists_abelianLayer_globalNormSubgroup_eq_of_le`) realizes `N` itself as a norm subgroup.

Together with descent along `K(ζ_p)/K` and the induction on the index of
`ClassFormation.exists_abelianLayer_normSubgroup_eq_of_forall_prime`, this is the arithmetic input
of the global existence theorem.

## Main results

* `TauCeti.ClassFieldTheory.globalNormSubgroup_kummerLayer_sUnits`: the norm subgroup of
  `K(U_S^{1/p})/K` is the image of `E_S`.
* `TauCeti.ClassFieldTheory.exists_abelianLayer_globalNormSubgroup_eq_of_pow_mem`: the Kummer case
  of global existence.
* `TauCeti.ClassFieldTheory.exists_intermediateField_range_ideleClassNormMap_eq_of_pow_mem`: the
  realization of an open subgroup containing the `p`-th powers as the idele-class norm range
  of a finite subextension of a separably closed field over `K`.

## References

* J. S. Milne, *Class Field Theory*, v4.03, Chapter VII, §9, Lemma 9.3.
* E. Artin and J. Tate, *Class Field Theory*, Chapter XIV, §6.
-/

public noncomputable section

open IsDedekindDomain NumberField

namespace TauCeti.ClassFieldTheory

open GlobalNumberFields

variable {K : Type} [Field K] [NumberField K]

variable {p : ℕ} [Fact p.Prime] [HasEnoughRootsOfUnity K p]

/-- **The norm subgroup of the Kummer field of the `S`-units** (Milne VII, Lemma 9.3). Let `K`
contain the `p`-th roots of unity, and let `S` be a finite set of finite places containing the
places above `p` and generating the ideal class group. Then the idele-class norm group of
`K(U_S^{1/p})/K` is the image in `C_K` of the Kummer idele subgroup `E_S` of ideles that are
`p`-th powers at `S` and at every infinite place and units elsewhere. -/
theorem globalNormSubgroup_kummerLayer_sUnits {S : Finset (HeightOneSpectrum (𝓞 K))}
    (hcl : Subgroup.closure
      (HeightOneSpectrum.classGroupMk '' (S : Set (HeightOneSpectrum (𝓞 K)))) = ⊤)
    (hpS : ∀ v : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ v.asIdeal → v ∈ S) :
    globalNormSubgroup K (kummerLayer p ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)) =
      auxiliaryKummerIdeleClassSubgroup S ∅ p := by
  set V := kummerLayer p ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)
  -- Work with the Kummer field `M = K(U_S^{1/p})` cut out by `V`.
  let M := kummerField (SeparableClosure K) p ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)
  have : NumberField M := .of_module_finite K M
  have hVM : globalNormSubgroup K V =
      (ideleClassNormMap K M : IdeleClassGroup (𝓞 M) M →* IdeleClassGroup (𝓞 K) K).range := by
    rw [globalNormSubgroup_eq_range_classField]
    exact range_ideleClassNormMap_eq_of_algEquiv
      (IntermediateField.equivOfEq (classField_kummerLayer _ _))
  -- The Kummer idele classes are norms from `M`, which has exponent `p` and is unramified
  -- outside `S`.
  have hle : auxiliaryKummerIdeleClassSubgroup S ∅ p ≤ globalNormSubgroup K V := by
    rw [hVM]
    exact auxiliaryKummerIdeleClassSubgroup_le_range_ideleClassNormMap_of_ramifiedSupport K M
      exponent_algEquiv_kummerField_dvd S ∅ (by simp)
      (TauCeti.NumberField.ramifiedSupport_kummerField_sUnits_subset S hpS)
  -- Both subgroups have index `p ^ (#S + r₁ + r₂)`: the image of `E_S` by the product formula
  -- and the `S`-unit theorem, and the norm subgroup by the norm index theorem and the Kummer
  -- degree of `M`.
  have haux : (auxiliaryKummerIdeleClassSubgroup S ∅ p).index =
      p ^ (S.card + Fintype.card (InfinitePlace K)) := by
    simpa using index_auxiliaryKummerIdeleClassSubgroup_mul_pow_card (T := ∅) Fact.out
      (by simp) hcl hpS fun b ↦ ⟨1, funext fun v ↦ absurd v.2 (by simp)⟩
  have hnorm : (globalNormSubgroup K V).index = Module.finrank K M := by
    rw [hVM, Subgroup.index_eq_card, card_ideleClassNormQuotient]
  have hdeg : Module.finrank K M = p ^ (S.card + Fintype.card (InfinitePlace K)) := by
    rw [finrank_kummerField fun a _ ↦ IsSepClosed.exists_pow_nat_eq _ p,
      relIndex_range_powMonoidHom_sUnits_numberField]
    simp [add_comm]
  have hindex : (globalNormSubgroup K V).index =
      (auxiliaryKummerIdeleClassSubgroup S ∅ p).index := by
    rw [hnorm, hdeg, haux]
  have : (globalNormSubgroup K V).FiniteIndex := finiteIndex_globalNormSubgroup K V
  exact (Subgroup.eq_of_index_dvd_index hle (hindex ▸ dvd_rfl)).symm

/-- **The Kummer case of global existence** (Milne VII, Lemma 9.3). Let `K` be a number field
containing the `p`-th roots of unity for a prime `p`. Every open subgroup of the idele class group
`C_K` containing the `p`-th powers is the norm subgroup of a finite abelian extension of `K`. -/
theorem exists_abelianLayer_globalNormSubgroup_eq_of_pow_mem
    {N : Subgroup (IdeleClassGroup (𝓞 K) K)} (hN : IsOpen (N : Set (IdeleClassGroup (𝓞 K) K)))
    (hpow : ∀ c, c ^ p ∈ N) :
    ∃ V : OpenNormalSubgroup (AbsoluteGaloisGroup K),
      V.IsAbelianClassFieldLayer ∧ globalNormSubgroup K V = N := by
  classical
  -- `N` contains a ray subgroup. Choose `S` containing the finite part of its modulus and the
  -- places above `p`, and generating the class group.
  obtain ⟨𝔪, h𝔪⟩ := exists_raySubgroup_le_of_isOpen N hN
  obtain ⟨S, hS₀S, hcl, hpS⟩ := ClassGroup.exists_finset_superset_closure_classGroupMk_image_eq_top
    𝔪.support (a := (p : 𝓞 K)) (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  -- `N` contains the norm subgroup of `K(U_S^{1/p})/K`, so upward closure applies.
  refine exists_abelianLayer_globalNormSubgroup_eq_of_le
    (V := kummerLayer p ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)) ?_
  rw [globalNormSubgroup_kummerLayer_sUnits hcl hpS]
  exact auxiliaryKummerIdeleClassSubgroup_le_of_raySubgroup_le hpow h𝔪 hS₀S

/-- **The Kummer case of global existence in a separably closed field.** Let `E` be a number field
containing the `p`-th roots of unity for a prime `p`, and `Ω` a separably closed field over `E`.
Every open subgroup of `C_E` containing the `p`-th powers is the idele-class norm group of a
finite subextension of `Ω/E`: the image of an `E`-embedding into `Ω` of the class field given by
`exists_abelianLayer_globalNormSubgroup_eq_of_pow_mem`. -/
theorem exists_intermediateField_range_ideleClassNormMap_eq_of_pow_mem {E Ω : Type} [Field E]
    [NumberField E] [Field Ω] [Algebra E Ω] [IsSepClosed Ω] [HasEnoughRootsOfUnity E p]
    {N : Subgroup (IdeleClassGroup (𝓞 E) E)} (hN : IsOpen (N : Set (IdeleClassGroup (𝓞 E) E)))
    (hpow : ∀ c, c ^ p ∈ N) :
    ∃ (L : IntermediateField E Ω) (_ : NumberField L),
      (ideleClassNormMap E L : IdeleClassGroup (𝓞 L) L →* IdeleClassGroup (𝓞 E) E).range = N := by
  obtain ⟨V, -, rfl⟩ := exists_abelianLayer_globalNormSubgroup_eq_of_pow_mem hN hpow
  let τ : classField E V →ₐ[E] Ω := IsSepClosed.lift
  have : FiniteDimensional E τ.fieldRange := τ.toLinearMap.finiteDimensional_range
  have : NumberField τ.fieldRange := .of_module_finite E _
  refine ⟨τ.fieldRange, inferInstance, ?_⟩
  rw [globalNormSubgroup_eq_range_classField]
  exact (range_ideleClassNormMap_eq_of_algEquiv τ.equivFieldRange).symm

end TauCeti.ClassFieldTheory

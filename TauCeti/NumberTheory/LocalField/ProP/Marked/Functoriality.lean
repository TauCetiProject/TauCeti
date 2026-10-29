/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.ProP.Marked.Basic
import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Cyclotomic.Map
import TauCeti.NumberTheory.LocalField.RootsOfUnity.Tower

/-!
# Functoriality of the marked presentations of `G_K(p)`

The marked theorems of `TauCeti.NumberTheory.LocalField.ProP.Marked.Basic` present `G_K(p)`, for
`K` a finite extension of `ℚ_p` containing a primitive `p`th root of unity, by a single relator on
`[K : ℚ_p] + 2` generators, and record the values of the cyclotomic orientation on those
generators. This file proves that this marked data is carried along an isomorphism of fields
`e : K ≃+* K'`: the induced isomorphism `absoluteGaloisGroupProPCongr e` of maximal pro-`p` Galois
groups carries the presentation of `G_K(p)` to a presentation of `G_{K'}(p)`, and the values of the
cyclotomic orientation of `G_{K'}(p)` on the transported generators are the values that
`Marked/Basic.lean` records for `K`.

Three ingredients make the marking functorial.

* The cyclotomic character does not see the choice of embedding of algebraic closures
  (`TauCeti.localCyclotomicCharacter_map`), so the image of the cyclotomic character is an invariant
  of the field (`TauCeti.range_localCyclotomicCharacter_eq_of_ringEquiv`). The image separates the
  two even dyadic branches, so together with the degree over `ℚ_p` the arithmetic branch predicates
  that select the relator word are invariant as well (`TauCeti.isQNeTwoCase_iff_of_algEquiv` and the
  three dyadic variants).
* The cyclotomic orientation is natural
  (`TauCeti.cyclotomicOrientation_maximalProPQuotient_congr_symm`), which makes the recorded values
  of a marked presentation transport
  (`TauCeti.cyclotomicOrientation_trans_absoluteGaloisGroupProPCongr`).
* The degree `[K : ℚ_p]` and the number `q(K)` of `p`-power roots of unity are preserved by an
  isomorphism of local fields over `ℚ_p` (`LinearEquiv.finrank_eq`,
  `TauCeti.localRootOfUnityOrder_eq_of_ringEquiv`), so the abstract group that the marked theorems
  present for `K` also presents `G_{K'}(p)`.

The isomorphism `e` of the three transport theorems is an isomorphism of *fields*, not an
isomorphism of local fields over `ℚ_p`. The conclusions of those theorems only concern the
transport of the recorded values, and the naturality of the cyclotomic orientation gives that for
any isomorphism of fields, so the `ℚ_p`-structure plays no role in them. The `ℚ_p`-structure is
what makes the *arithmetic data* that the marked presentation of `K` records — the degree
`[K : ℚ_p]`, the number `q(K)` of `p`-power roots of unity and the dyadic branch — agree with the
data of `K'`, and that agreement is what makes the transported presentation the marked presentation
of `G_{K'}(p)` in the sense of `TauCeti.NumberTheory.LocalField.ProP.Marked.Basic`. The four branch
lemmas below establish the agreement for isomorphisms of local fields over `ℚ_p`; for an arbitrary
isomorphism of fields it has to be assumed.

The transports are stated at the parameters of `K`: the relator word, the number of generators and
the recorded values are those of the marked theorem for `K`, and the invariants above are what allow
reading them as data of `K'` as well. Keeping the invariants as equalities rather than transporting
the presentation along them keeps the transported isomorphism on the same generating set
`Fin (N + 2)`, where `N = [K : ℚ_p]`. The transport is group-theoretic: no valuation is used, and
the field side enters only through the cyclotomic character. No composition law is claimed for
`absoluteGaloisGroupProPCongr`, since `Field.absoluteGaloisGroup.map` depends on a non-canonical
choice (`IsAlgClosed.lift`) of embedding of algebraic closures.

## Main results

* `TauCeti.absoluteGaloisGroupProPCongr`: the isomorphism `G_{K'}(p) ≃ₜ* G_K(p)` induced by an
  isomorphism of fields `K ≃+* K'`.
* `TauCeti.range_localCyclotomicCharacter_eq_of_ringEquiv`: the image of the cyclotomic character is
  an invariant of the field.
* `TauCeti.cyclotomicOrientation_trans_absoluteGaloisGroupProPCongr`: the marking transports.
* `TauCeti.isQNeTwoCase_iff_of_algEquiv`, `TauCeti.isDyadicOddCase_iff_of_algEquiv`,
  `TauCeti.isDyadicEvenPlusMinusCase_iff_of_algEquiv`,
  `TauCeti.isDyadicEvenPrincipalCase_iff_of_algEquiv`: the arithmetic branch predicates of the
  marked classification are invariants of the field.
* `TauCeti.absoluteGaloisGroupProP_marked_of_q_ne_two_congr`,
  `TauCeti.absoluteGaloisGroupProP_two_marked_of_degree_odd_congr`,
  `TauCeti.absoluteGaloisGroupProP_two_marked_of_degree_even_congr`: functoriality of the marked
  results, one statement per relator family. The last covers both even dyadic branches, which share
  the relator word `demushkinWordTwoEven` and the recorded values and differ only in the hypotheses
  that select the parameters.

## References

* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), 106-132,
  Theorems 7-9.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (7.5.11) and
  (7.5.12).
-/

public section

namespace TauCeti

variable (p : ℕ) [Fact p.Prime]

/-- The isomorphism of maximal pro-`p` Galois groups induced by an isomorphism of fields
`e : K ≃+* K'`: the form in which an isomorphism of fields acts on the marked presentations. It is
contravariant, going from `G_{K'}(p)` to `G_K(p)`. -/
noncomputable abbrev absoluteGaloisGroupProPCongr (K K' : Type*) [Field K] [Field K']
    (e : K ≃+* K') : absoluteGaloisGroupProP p K' ≃ₜ* absoluteGaloisGroupProP p K :=
  maximalProPQuotient.congr (absoluteGaloisGroupMapEquiv e)

section Isomorphism

variable {K : Type*} [Field K] {K' : Type*} [Field K']

/-- **The image of the cyclotomic character is an invariant of the field.** An isomorphism of fields
induces an isomorphism of absolute Galois groups, and the cyclotomic character of the target is the
character of the source read through it (`TauCeti.localCyclotomicCharacter_map`); hence the two
characters have the same image in `ℤ_pˣ`. -/
theorem range_localCyclotomicCharacter_eq_of_ringEquiv (e : K ≃+* K') :
    (localCyclotomicCharacter p K).range = (localCyclotomicCharacter p K').range := by
  have key : ∀ g : Field.absoluteGaloisGroup K',
      localCyclotomicCharacter p K (absoluteGaloisGroupMapEquiv e g) =
        localCyclotomicCharacter p K' g := fun g ↦ by
    rw [absoluteGaloisGroupMapEquiv_apply]
    exact localCyclotomicCharacter_map p e.toRingHom g
  refine le_antisymm ?_ ?_
  · rintro u ⟨g, rfl⟩
    obtain ⟨g', hg'⟩ := (absoluteGaloisGroupMapEquiv e).surjective g
    exact ⟨g', (key g').symm.trans (congrArg (localCyclotomicCharacter p K) hg')⟩
  · rintro u ⟨g, rfl⟩
    exact ⟨absoluteGaloisGroupMapEquiv e g, key g⟩

variable {P : Type*} [Group P] [TopologicalSpace P]

/-- **Naturality of the marked orientation.** An isomorphism of fields carries a presentation of
`G_K(p)` to a presentation of `G_{K'}(p)`, and the value of the cyclotomic orientation of
`G_{K'}(p)` on a transported generator is the value recorded for `K` on that generator. Applied to
the marked presentations of `Marked/Basic.lean`, this says that
`(absoluteGaloisGroupProPCongr e).trans m` is a marked presentation of `G_{K'}(p)` with the same
relator word and the same values. -/
theorem cyclotomicOrientation_trans_absoluteGaloisGroupProPCongr (e : K ≃+* K')
    (hmu : ∃ ζ : K, IsPrimitiveRoot ζ p) (hmu' : ∃ ζ : K', IsPrimitiveRoot ζ p)
    (m : absoluteGaloisGroupProP p K ≃ₜ* P) (y : P) :
    cyclotomicOrientation p K' hmu'
        (((absoluteGaloisGroupProPCongr p K K' e).trans m).symm y) =
      cyclotomicOrientation p K hmu (m.symm y) := by
  rw [ContinuousMulEquiv.symm_trans_apply,
    cyclotomicOrientation_maximalProPQuotient_congr_symm p e hmu' (m.symm y)]

end Isomorphism

section Branches

variable {K K' : Type*} [Field K] [Algebra ℚ_[p] K]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field K'] [Algebra ℚ_[p] K'] [ValuativeRel K'] [TopologicalSpace K']
  [IsNonarchimedeanLocalField K']

/-- **The nonexceptional Demushkin branch is an invariant of the field.** An isomorphism of local
fields over `ℚ_p` preserves the existence of a primitive `p`th root of unity and the number of
`p`-power roots of unity (`TauCeti.localRootOfUnityOrder_eq_of_ringEquiv`). -/
theorem isQNeTwoCase_iff_of_algEquiv (e : K ≃ₐ[ℚ_[p]] K') :
    IsQNeTwoCase p K ↔ IsQNeTwoCase p K' := by
  let _ : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[p] K).injective
  let _ : CharZero K' := charZero_of_injective_algebraMap (algebraMap ℚ_[p] K').injective
  have hq : localRootOfUnityOrder p K
        (finite_pPowerRootsOfUnity (p := p) (K := K)
          (by exact_mod_cast (Fact.out : p.Prime).ne_zero)) =
      localRootOfUnityOrder p K'
        (finite_pPowerRootsOfUnity (p := p) (K := K')
          (by exact_mod_cast (Fact.out : p.Prime).ne_zero)) :=
    localRootOfUnityOrder_eq_of_ringEquiv p e.toRingEquiv _ _
  constructor
  · intro h
    have hne := ((isQNeTwoCase_iff (p := p) (K := K)).mp h).2
    have hmu := ((isQNeTwoCase_iff (p := p) (K := K)).mp h).1
    exact (isQNeTwoCase_iff (p := p) (K := K')).mpr
      ⟨hmu.elim fun ζ hζ ↦
        ⟨e ζ, hζ.map_of_injective (f := e.toRingEquiv) e.toRingEquiv.injective⟩, hq ▸ hne⟩
  · intro h
    have hne := ((isQNeTwoCase_iff (p := p) (K := K')).mp h).2
    have hmu := ((isQNeTwoCase_iff (p := p) (K := K')).mp h).1
    exact (isQNeTwoCase_iff (p := p) (K := K)).mpr
      ⟨hmu.elim fun ζ hζ ↦
        ⟨e.symm ζ, hζ.map_of_injective (f := e.symm.toRingEquiv) e.symm.toRingEquiv.injective⟩,
        hq.symm ▸ hne⟩

end Branches

section DyadicOdd

variable {K K' : Type*} [Field K] [Algebra ℚ_[2] K] [FiniteDimensional ℚ_[2] K]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field K'] [Algebra ℚ_[2] K'] [FiniteDimensional ℚ_[2] K'] [ValuativeRel K']
  [TopologicalSpace K'] [IsNonarchimedeanLocalField K']

omit [FiniteDimensional ℚ_[2] K] [FiniteDimensional ℚ_[2] K'] in
/-- **The odd dyadic branch is an invariant of the field.** An isomorphism of local fields over
`ℚ₂` preserves the number of `2`-power roots of unity and the parity of the degree over `ℚ₂`
(`LinearEquiv.finrank_eq`). -/
theorem isDyadicOddCase_iff_of_algEquiv (e : K ≃ₐ[ℚ_[2]] K') :
    IsDyadicOddCase K ↔ IsDyadicOddCase K' := by
  let _ : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[2] K).injective
  let _ : CharZero K' := charZero_of_injective_algebraMap (algebraMap ℚ_[2] K').injective
  have hq : localRootOfUnityOrder 2 K
        (finite_pPowerRootsOfUnity (p := 2) (K := K) (by norm_num)) =
      localRootOfUnityOrder 2 K'
        (finite_pPowerRootsOfUnity (p := 2) (K := K') (by norm_num)) :=
    localRootOfUnityOrder_eq_of_ringEquiv 2 e.toRingEquiv _ _
  have hf : Module.finrank ℚ_[2] K = Module.finrank ℚ_[2] K' := e.toLinearEquiv.finrank_eq
  constructor
  · intro h
    have hodd := ((isDyadicOddCase_iff (K := K)).mp h).2
    have hroot := ((isDyadicOddCase_iff (K := K)).mp h).1
    exact (isDyadicOddCase_iff (K := K')).mpr ⟨hq ▸ hroot, hf ▸ hodd⟩
  · intro h
    have hodd := ((isDyadicOddCase_iff (K := K')).mp h).2
    have hroot := ((isDyadicOddCase_iff (K := K')).mp h).1
    exact (isDyadicOddCase_iff (K := K)).mpr ⟨hq.symm ▸ hroot, hf.symm ▸ hodd⟩

end DyadicOdd

section DyadicEven

variable {K K' : Type*} [Field K] [Algebra ℚ_[2] K]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field K'] [Algebra ℚ_[2] K'] [ValuativeRel K'] [TopologicalSpace K']
  [IsNonarchimedeanLocalField K']

/-- **The even dyadic branch whose cyclotomic image contains `-1` is an invariant of the field.**
Besides the number of `2`-power roots of unity and the parity of the degree over `ℚ₂`, the branch
records the image of the cyclotomic character, which is an invariant of the field
(`TauCeti.range_localCyclotomicCharacter_eq_of_ringEquiv`). -/
theorem isDyadicEvenPlusMinusCase_iff_of_algEquiv (e : K ≃ₐ[ℚ_[2]] K') :
    IsDyadicEvenPlusMinusCase K ↔ IsDyadicEvenPlusMinusCase K' := by
  let _ : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[2] K).injective
  let _ : CharZero K' := charZero_of_injective_algebraMap (algebraMap ℚ_[2] K').injective
  have hq : localRootOfUnityOrder 2 K
        (finite_pPowerRootsOfUnity (p := 2) (K := K) (by norm_num)) =
      localRootOfUnityOrder 2 K'
        (finite_pPowerRootsOfUnity (p := 2) (K := K') (by norm_num)) :=
    localRootOfUnityOrder_eq_of_ringEquiv 2 e.toRingEquiv _ _
  have hf : Module.finrank ℚ_[2] K = Module.finrank ℚ_[2] K' := e.toLinearEquiv.finrank_eq
  have hr : (localCyclotomicCharacter 2 K).range = (localCyclotomicCharacter 2 K').range :=
    range_localCyclotomicCharacter_eq_of_ringEquiv 2 e.toRingEquiv
  constructor
  · intro h
    have hneg := ((isDyadicEvenPlusMinusCase_iff (K := K)).mp h).2.2
    have heven := ((isDyadicEvenPlusMinusCase_iff (K := K)).mp h).2.1
    have hroot := ((isDyadicEvenPlusMinusCase_iff (K := K)).mp h).1
    exact (isDyadicEvenPlusMinusCase_iff (K := K')).mpr
      ⟨hq ▸ hroot, hf ▸ heven, hr ▸ hneg⟩
  · intro h
    have hneg := ((isDyadicEvenPlusMinusCase_iff (K := K')).mp h).2.2
    have heven := ((isDyadicEvenPlusMinusCase_iff (K := K')).mp h).2.1
    have hroot := ((isDyadicEvenPlusMinusCase_iff (K := K')).mp h).1
    exact (isDyadicEvenPlusMinusCase_iff (K := K)).mpr
      ⟨hq.symm ▸ hroot, hf.symm ▸ heven, hr.symm ▸ hneg⟩

/-- **The even dyadic branch whose cyclotomic image does not contain `-1` is an invariant of the
field**, by the same three invariants as the other even branch. -/
theorem isDyadicEvenPrincipalCase_iff_of_algEquiv (e : K ≃ₐ[ℚ_[2]] K') :
    IsDyadicEvenPrincipalCase K ↔ IsDyadicEvenPrincipalCase K' := by
  let _ : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[2] K).injective
  let _ : CharZero K' := charZero_of_injective_algebraMap (algebraMap ℚ_[2] K').injective
  have hq : localRootOfUnityOrder 2 K
        (finite_pPowerRootsOfUnity (p := 2) (K := K) (by norm_num)) =
      localRootOfUnityOrder 2 K'
        (finite_pPowerRootsOfUnity (p := 2) (K := K') (by norm_num)) :=
    localRootOfUnityOrder_eq_of_ringEquiv 2 e.toRingEquiv _ _
  have hf : Module.finrank ℚ_[2] K = Module.finrank ℚ_[2] K' := e.toLinearEquiv.finrank_eq
  have hr : (localCyclotomicCharacter 2 K).range = (localCyclotomicCharacter 2 K').range :=
    range_localCyclotomicCharacter_eq_of_ringEquiv 2 e.toRingEquiv
  constructor
  · intro h
    have hneg := ((isDyadicEvenPrincipalCase_iff (K := K)).mp h).2.2
    have heven := ((isDyadicEvenPrincipalCase_iff (K := K)).mp h).2.1
    have hroot := ((isDyadicEvenPrincipalCase_iff (K := K)).mp h).1
    exact (isDyadicEvenPrincipalCase_iff (K := K')).mpr
      ⟨hq ▸ hroot, hf ▸ heven, hr ▸ hneg⟩
  · intro h
    have hneg := ((isDyadicEvenPrincipalCase_iff (K := K')).mp h).2.2
    have heven := ((isDyadicEvenPrincipalCase_iff (K := K')).mp h).2.1
    have hroot := ((isDyadicEvenPrincipalCase_iff (K := K')).mp h).1
    exact (isDyadicEvenPrincipalCase_iff (K := K)).mpr
      ⟨hq.symm ▸ hroot, hf.symm ▸ heven, hr.symm ▸ hneg⟩

end DyadicEven

section MarkedQNeTwo

variable {K K' : Type*} [Field K] [Algebra ℚ_[p] K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field K']

/-- **Functoriality of the marked presentation when `q(K) ≠ 2`.** Let `e : K ≃+* K'` be an
isomorphism of fields, and let `m` be a marked presentation of `G_K(p)` with the relator word and
the values that `TauCeti.absoluteGaloisGroupProP_marked_of_q_ne_two` records for `K`. Then
`(absoluteGaloisGroupProPCongr e).trans m` presents `G_{K'}(p)` by the same relator word and takes
the same values of the cyclotomic orientation on the generators.

Only the transport of the recorded values is claimed, and it uses no property of `e` beyond being an
isomorphism of fields: it is the naturality of the cyclotomic orientation along the induced
isomorphism of the absolute Galois groups
(`TauCeti.cyclotomicOrientation_trans_absoluteGaloisGroupProPCongr`). For the transported
presentation to be *the* marked presentation of `G_{K'}(p)` in the sense of
`TauCeti.absoluteGaloisGroupProP_marked_of_q_ne_two`, the target must have the same degree over
`ℚ_p` and the same number of `p`-power roots of unity as the source; an isomorphism of local fields
over `ℚ_p` provides that (`TauCeti.isQNeTwoCase_iff_of_algEquiv`). -/
theorem absoluteGaloisGroupProP_marked_of_q_ne_two_congr (e : K ≃+* K')
    (hmu : ∃ ζ : K, IsPrimitiveRoot ζ p) (hmu' : ∃ ζ : K', IsPrimitiveRoot ζ p)
    (m : absoluteGaloisGroupProP p K ≃ₜ*
      presentedProP p (Fin (Module.finrank ℚ_[p] K + 2))
        {demushkinWordNeTwo
          (localRootOfUnityOrder p K
            (finite_pPowerRootsOfUnity (hmu.elim fun _ hζ ↦ hζ.neZero'.out)))
          (Module.finrank ℚ_[p] K + 2)
          (freeProPGen p (Module.finrank ℚ_[p] K + 2))})
    (hm₁ : ((cyclotomicOrientation p K hmu
          (m.symm (presentedProPGen p (Module.finrank ℚ_[p] K + 2) _ 1)) : ℤ_[p]) *
        (1 - (localRootOfUnityOrder p K
          (finite_pPowerRootsOfUnity (hmu.elim fun _ hζ ↦ hζ.neZero'.out)) : ℤ_[p])) = 1))
    (hm₂ : ∀ i : ℕ, i ≠ 1 → i < Module.finrank ℚ_[p] K + 2 →
      cyclotomicOrientation p K hmu
        (m.symm (presentedProPGen p (Module.finrank ℚ_[p] K + 2) _ i)) = 1) :
    ((cyclotomicOrientation p K' hmu'
          (((absoluteGaloisGroupProPCongr p K K' e).trans m).symm
            (presentedProPGen p (Module.finrank ℚ_[p] K + 2) _ 1)) : ℤ_[p]) *
        (1 - (localRootOfUnityOrder p K
          (finite_pPowerRootsOfUnity (hmu.elim fun _ hζ ↦ hζ.neZero'.out)) : ℤ_[p])) = 1) ∧
      ∀ i : ℕ, i ≠ 1 → i < Module.finrank ℚ_[p] K + 2 →
        cyclotomicOrientation p K' hmu'
          (((absoluteGaloisGroupProPCongr p K K' e).trans m).symm
            (presentedProPGen p (Module.finrank ℚ_[p] K + 2) _ i)) = 1 := by
  have htrans : ∀ i : ℕ,
      cyclotomicOrientation p K' hmu'
          (((absoluteGaloisGroupProPCongr p K K' e).trans m).symm
            (presentedProPGen p (Module.finrank ℚ_[p] K + 2) _ i)) =
        cyclotomicOrientation p K hmu
          (m.symm (presentedProPGen p (Module.finrank ℚ_[p] K + 2) _ i)) :=
    fun i ↦ cyclotomicOrientation_trans_absoluteGaloisGroupProPCongr (p := p) (K := K)
      (K' := K') e hmu hmu' m _
  refine ⟨?_, ?_⟩
  · rw [htrans 1]
    exact hm₁
  · intro i hi₁ hi₂
    rw [htrans i]
    exact hm₂ i hi₁ hi₂

end MarkedQNeTwo

section MarkedDyadic

variable {K K' : Type*} [Field K] [Algebra ℚ_[2] K] [Field K']

/-- **Functoriality of the marked presentation in odd degree.** Let `e : K ≃+* K'` be an isomorphism
of fields, and let `m` be a marked presentation of `G_K(2)` with the relator word and the values
that `TauCeti.absoluteGaloisGroupProP_two_marked_of_degree_odd` records for `K`. Then
`(absoluteGaloisGroupProPCongr e).trans m` presents `G_{K'}(2)` by the same relator word
`demushkinWordTwoOdd` and takes the same values on the generators `0`, `2` and the remaining ones.

Only the transport of the recorded values is claimed, and it uses no property of `e` beyond being an
isomorphism of fields; the transport is the naturality of the cyclotomic orientation along the
induced isomorphism of the absolute Galois groups
(`TauCeti.cyclotomicOrientation_trans_absoluteGaloisGroupProPCongr`). For the transported
presentation to be *the* marked presentation of `G_{K'}(2)` in the sense of
`TauCeti.absoluteGaloisGroupProP_two_marked_of_degree_odd`, the target must have the same odd degree
over `ℚ₂` as the source; an isomorphism of local fields over `ℚ₂` provides that
(`TauCeti.isDyadicOddCase_iff_of_algEquiv`). -/
theorem absoluteGaloisGroupProP_two_marked_of_degree_odd_congr (e : K ≃+* K')
    (hmu : ∃ ζ : K, IsPrimitiveRoot ζ 2) (hmu' : ∃ ζ : K', IsPrimitiveRoot ζ 2)
    (m : absoluteGaloisGroupProP 2 K ≃ₜ*
      presentedProP 2 (Fin (Module.finrank ℚ_[2] K + 2))
        {demushkinWordTwoOdd 2 (Module.finrank ℚ_[2] K + 2)
          (freeProPGen 2 (Module.finrank ℚ_[2] K + 2))})
    (hm₀ : cyclotomicOrientation 2 K hmu
        (m.symm (presentedProPGen 2 (Module.finrank ℚ_[2] K + 2) _ 0)) = -1)
    (hm₂ : ((cyclotomicOrientation 2 K hmu
          (m.symm (presentedProPGen 2 (Module.finrank ℚ_[2] K + 2) _ 2)) : ℤ_[2]) *
        (1 - 2 ^ 2) = 1))
    (hm : ∀ i : ℕ, i ≠ 0 → i ≠ 2 → i < Module.finrank ℚ_[2] K + 2 →
      cyclotomicOrientation 2 K hmu
        (m.symm (presentedProPGen 2 (Module.finrank ℚ_[2] K + 2) _ i)) = 1) :
    cyclotomicOrientation 2 K' hmu'
          (((absoluteGaloisGroupProPCongr 2 K K' e).trans m).symm
            (presentedProPGen 2 (Module.finrank ℚ_[2] K + 2) _ 0)) = -1 ∧
      ((cyclotomicOrientation 2 K' hmu'
          (((absoluteGaloisGroupProPCongr 2 K K' e).trans m).symm
            (presentedProPGen 2 (Module.finrank ℚ_[2] K + 2) _ 2)) : ℤ_[2]) *
        (1 - 2 ^ 2) = 1) ∧
      ∀ i : ℕ, i ≠ 0 → i ≠ 2 → i < Module.finrank ℚ_[2] K + 2 →
        cyclotomicOrientation 2 K' hmu'
          (((absoluteGaloisGroupProPCongr 2 K K' e).trans m).symm
            (presentedProPGen 2 (Module.finrank ℚ_[2] K + 2) _ i)) = 1 := by
  have htrans : ∀ i : ℕ,
      cyclotomicOrientation 2 K' hmu'
          (((absoluteGaloisGroupProPCongr 2 K K' e).trans m).symm
            (presentedProPGen 2 (Module.finrank ℚ_[2] K + 2) _ i)) =
        cyclotomicOrientation 2 K hmu
          (m.symm (presentedProPGen 2 (Module.finrank ℚ_[2] K + 2) _ i)) :=
    fun i ↦ cyclotomicOrientation_trans_absoluteGaloisGroupProPCongr (p := 2) (K := K)
      (K' := K') e hmu hmu' m _
  refine ⟨?_, ?_, ?_⟩
  · rw [htrans 0]
    exact hm₀
  · rw [htrans 2]
    exact hm₂
  · intro i hi₀ hi₂ hi
    rw [htrans i]
    exact hm i hi₀ hi₂ hi

/-- **Functoriality of the marked presentation in even degree.** The two even dyadic marked
theorems `TauCeti.absoluteGaloisGroupProP_two_marked_of_degree_even_plusMinus` and
`TauCeti.absoluteGaloisGroupProP_two_marked_of_degree_even_principal` present `G_K(2)` by the same
word `demushkinWordTwoEven a f (N + 2)` on `N + 2` generators and record the same values on the
second and fourth marked generators, the value `-(1 + a)⁻¹` and the value `(1 - 2^f)⁻¹`; they differ
only in the hypotheses that select the parameters `a` and `f`. Hence the transport of their marking
is a single statement. For `e : K ≃+* K'` an isomorphism of fields, the transported isomorphism
`(absoluteGaloisGroupProPCongr e).trans m` of a marked presentation of `G_K(2)` of the even form
presents `G_{K'}(2)` by the same relator word and takes the same values.

Only the transport of the recorded values is claimed, and it uses no property of `e` beyond being an
isomorphism of fields; the transport is the naturality of the cyclotomic orientation along the
induced isomorphism of the absolute Galois groups
(`TauCeti.cyclotomicOrientation_trans_absoluteGaloisGroupProPCongr`). For the transported
presentation to be *the* marked presentation of `G_{K'}(2)` in the sense of
`TauCeti.absoluteGaloisGroupProP_two_marked_of_degree_even_plusMinus` or
`TauCeti.absoluteGaloisGroupProP_two_marked_of_degree_even_principal`, the target must have the
same even degree over `ℚ₂` and the same cyclotomic image as the source; an isomorphism of local
fields over `ℚ₂` provides that (`TauCeti.isDyadicEvenPlusMinusCase_iff_of_algEquiv` and
`TauCeti.isDyadicEvenPrincipalCase_iff_of_algEquiv`). -/
theorem absoluteGaloisGroupProP_two_marked_of_degree_even_congr (e : K ≃+* K')
    (hmu : ∃ ζ : K, IsPrimitiveRoot ζ 2) (hmu' : ∃ ζ : K', IsPrimitiveRoot ζ 2) {a f : ℕ}
    (m : absoluteGaloisGroupProP 2 K ≃ₜ*
      presentedProP 2 (Fin (Module.finrank ℚ_[2] K + 2))
        {demushkinWordTwoEven a f (Module.finrank ℚ_[2] K + 2)
          (freeProPGen 2 (Module.finrank ℚ_[2] K + 2))})
    (hm₁ : ((cyclotomicOrientation 2 K hmu
          (m.symm (presentedProPGen 2 (Module.finrank ℚ_[2] K + 2) _ 1)) : ℤ_[2]) *
        (1 + (a : ℤ_[2])) = -1))
    (hm₃ : ((cyclotomicOrientation 2 K hmu
          (m.symm (presentedProPGen 2 (Module.finrank ℚ_[2] K + 2) _ 3)) : ℤ_[2]) *
        (1 - 2 ^ f) = 1))
    (hm : ∀ i : ℕ, i ≠ 1 → i ≠ 3 → i < Module.finrank ℚ_[2] K + 2 →
      cyclotomicOrientation 2 K hmu
        (m.symm (presentedProPGen 2 (Module.finrank ℚ_[2] K + 2) _ i)) = 1) :
    ((cyclotomicOrientation 2 K' hmu'
          (((absoluteGaloisGroupProPCongr 2 K K' e).trans m).symm
            (presentedProPGen 2 (Module.finrank ℚ_[2] K + 2) _ 1)) : ℤ_[2]) *
        (1 + (a : ℤ_[2])) = -1) ∧
      ((cyclotomicOrientation 2 K' hmu'
          (((absoluteGaloisGroupProPCongr 2 K K' e).trans m).symm
            (presentedProPGen 2 (Module.finrank ℚ_[2] K + 2) _ 3)) : ℤ_[2]) *
        (1 - 2 ^ f) = 1) ∧
      ∀ i : ℕ, i ≠ 1 → i ≠ 3 → i < Module.finrank ℚ_[2] K + 2 →
        cyclotomicOrientation 2 K' hmu'
          (((absoluteGaloisGroupProPCongr 2 K K' e).trans m).symm
            (presentedProPGen 2 (Module.finrank ℚ_[2] K + 2) _ i)) = 1 := by
  have htrans : ∀ i : ℕ,
      cyclotomicOrientation 2 K' hmu'
          (((absoluteGaloisGroupProPCongr 2 K K' e).trans m).symm
            (presentedProPGen 2 (Module.finrank ℚ_[2] K + 2) _ i)) =
        cyclotomicOrientation 2 K hmu
          (m.symm (presentedProPGen 2 (Module.finrank ℚ_[2] K + 2) _ i)) :=
    fun i ↦ cyclotomicOrientation_trans_absoluteGaloisGroupProPCongr (p := 2) (K := K)
      (K' := K') e hmu hmu' m _
  refine ⟨?_, ?_, ?_⟩
  · rw [htrans 1]
    exact hm₁
  · rw [htrans 3]
    exact hm₃
  · intro i hi₁ hi₃ hi
    rw [htrans i]
    exact hm i hi₁ hi₃ hi

end MarkedDyadic

end TauCeti

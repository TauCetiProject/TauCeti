/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LocalProperties.Exactness
public import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
public import TauCeti.Algebra.Module.LocalizedModule.Map

import Mathlib.Algebra.Module.LocalizedModule.Away
import TauCeti.Algebra.Algebra.IsUnit
import TauCeti.Algebra.BigOperators.Finset.OffDiagonal

/-!
# The Čech complex of localizations

Let `R` be a commutative ring, `M` an `R`-module and `f : ι → R` a family indexed by a linearly
ordered type. For a finite set `S ⊆ ι` write `f_S = ∏_{i ∈ S} f i` and `M_{f_S}` for the
localization of `M` away from `f_S`. The (alternating, extended) Čech complex of localizations is
`0 → M → ∏_{|S| = 1} M_{f_S} → ∏_{|S| = 2} M_{f_S} → ⋯`.
Its augmentation sends `m` to `m / 1` in every factor. Its differential sends `x` to the family
whose `S`-component is `∑_{a ∈ S} (-1)^k x_{S ∖ {a}}`, where `k` is the number of elements of `S`
below `a` and `x_{S ∖ {a}}` is restricted along `M_{f_{S ∖ {a}}} → M_{f_S}`. Listing `S` as
`i₀ < ⋯ < i_{p+1}`, this is the usual formula `∑_k (-1)^k x_{i₀ ⋯ î_k ⋯ i_{p+1}}`.

When `ι` is finite and the `f i` generate the unit ideal, the complex is exact. This is the
module-level form of the vanishing of the higher Čech cohomology of the quasi-coherent sheaf
associated to `M` on the cover of `Spec R` by the basic opens `D(f i)`. It is the algebraic input
to Huber's proof of sheafiness for Huber rings with a noetherian ring of definition, where this
complex of localizations is topologized and completed.

## Main definitions

* `TauCeti.cechLocalizationTerm M f p`: the degree `p` term `∏_{|S| = p + 1} M_{f_S}`.
* `TauCeti.cechLocalizationRestriction M f h`: the restriction `M_{f_T} → M_{f_S}` for `T ⊆ S`.
* `TauCeti.cechLocalizationAugmentation M f`: the augmentation `M → ∏_{|S| = 1} M_{f_S}`.
* `TauCeti.cechLocalizationDifferential M f p`: the differential in degree `p`.

## Main results

* `TauCeti.cechLocalizationDifferential_comp_augmentation` and
  `TauCeti.cechLocalizationDifferential_comp_differential`: the maps form a complex.
* `TauCeti.injective_cechLocalizationAugmentation`,
  `TauCeti.exact_cechLocalizationAugmentation_differential` and
  `TauCeti.cechComplexLocalization_exact`: the complex is exact if `ι` is finite and the `f i`
  generate the unit ideal.

## Implementation notes

Indexing by finite subsets rather than by increasing tuples turns deletion of a vertex into
`Finset.erase`, and lets the contracting homotopy insert a vertex with `insert`. Exactness is
local on `Spec R` (`exact_of_isLocalized_span`): after inverting `f j`, the localized complex is
the Čech complex of `M_{f j}`, on which `f j` acts invertibly, and inserting `j` into each subset
gives a contracting homotopy.

## References

* The Stacks Project, [Tag 01X9](https://stacks.math.columbia.edu/tag/01X9) (Lemma 30.2.1,
  Čech cohomology of quasi-coherent sheaves on affine schemes).
* R. Huber, *A generalization of formal schemes and rigid analytic varieties*, Math. Z. 217
  (1994), §2, proof of (1.3).
-/

public section

open LocalizedModule

namespace TauCeti

variable {R : Type*} [CommRing R]

section Restriction

variable {M : Type*} [AddCommGroup M] [Module R M]

/-- The canonical map `M_a → M_c`, defined when `a` acts invertibly on `M_c`. -/
private noncomputable def restr {a c : R}
    (h : IsUnit (algebraMap R (Module.End R (LocalizedModule (.powers c) M)) a)) :
    LocalizedModule (.powers a) M →ₗ[R] LocalizedModule (.powers c) M :=
  LocalizedModule.lift _ (mkLinearMap _ M) h.algebraMap_powers

private theorem restr_comp_mkLinearMap {a c : R}
    (h : IsUnit (algebraMap R (Module.End R (LocalizedModule (.powers c) M)) a)) :
    restr h ∘ₗ mkLinearMap _ M = mkLinearMap _ M :=
  LocalizedModule.lift_comp _ _ _

private theorem restr_ext {a c : R}
    (h : IsUnit (algebraMap R (Module.End R (LocalizedModule (.powers c) M)) a))
    {g g' : LocalizedModule (.powers a) M →ₗ[R] LocalizedModule (.powers c) M}
    (e : g ∘ₗ mkLinearMap _ M = g' ∘ₗ mkLinearMap _ M) : g = g' :=
  IsLocalizedModule.ext _ (mkLinearMap _ M) h.algebraMap_powers e

private theorem restr_restr {a b c : R}
    (h₁ : IsUnit (algebraMap R (Module.End R (LocalizedModule (.powers b) M)) a))
    (h₂ : IsUnit (algebraMap R (Module.End R (LocalizedModule (.powers c) M)) b))
    (h₃ : IsUnit (algebraMap R (Module.End R (LocalizedModule (.powers c) M)) a))
    (x : LocalizedModule (.powers a) M) : restr h₂ (restr h₁ x) = restr h₃ x := by
  refine LinearMap.congr_fun (restr_ext h₃ (g := restr h₂ ∘ₗ restr h₁) ?_) x
  rw [LinearMap.comp_assoc, restr_comp_mkLinearMap, restr_comp_mkLinearMap,
    restr_comp_mkLinearMap]

private theorem restr_self {a : R}
    (h : IsUnit (algebraMap R (Module.End R (LocalizedModule (.powers a) M)) a))
    (x : LocalizedModule (.powers a) M) : restr h x = x := by
  refine LinearMap.congr_fun (restr_ext h (g := restr h) (g' := LinearMap.id) ?_) x
  rw [restr_comp_mkLinearMap, LinearMap.id_comp]

/-- Restriction maps are natural in the module. -/
private theorem restr_map {N : Type*} [AddCommGroup N] [Module R N] (g : M →ₗ[R] N) {a c : R}
    (hM : IsUnit (algebraMap R (Module.End R (LocalizedModule (.powers c) M)) a))
    (hN : IsUnit (algebraMap R (Module.End R (LocalizedModule (.powers c) N)) a))
    (x : LocalizedModule (.powers a) M) :
    IsLocalizedModule.map (.powers c) (mkLinearMap _ M) (mkLinearMap _ N) g (restr hM x) =
      restr hN (IsLocalizedModule.map (.powers a) (mkLinearMap _ M) (mkLinearMap _ N) g x) := by
  refine LinearMap.congr_fun (IsLocalizedModule.ext _ (mkLinearMap _ M) hN.algebraMap_powers
    (j := IsLocalizedModule.map (.powers c) (mkLinearMap _ M) (mkLinearMap _ N) g ∘ₗ restr hM)
    (k := restr hN ∘ₗ
      IsLocalizedModule.map (.powers a) (mkLinearMap _ M) (mkLinearMap _ N) g) ?_) x
  rw [LinearMap.comp_assoc, restr_comp_mkLinearMap, IsLocalizedModule.map_comp,
    LinearMap.comp_assoc, IsLocalizedModule.map_comp, ← LinearMap.comp_assoc,
    restr_comp_mkLinearMap]

end Restriction

section Signs

variable {ι : Type*} [LinearOrder ι]

/-- The sign `(-1)^k` attached to deleting `a` from `S`, where `k` counts the elements of `S`
below `a`. -/
private def sgn (R : Type*) [CommRing R] (S : Finset ι) (a : ι) : R :=
  (-1) ^ (S.filter (· < a)).card

private theorem sgn_mul_self (S : Finset ι) (a : ι) : sgn R S a * sgn R S a = 1 := by
  rw [sgn, ← mul_pow]
  simp

/-- Deleting `a` from `S` changes the sign of a vertex `b` exactly when `a < b`. -/
private theorem sgn_erase {S : Finset ι} {a : ι} (ha : a ∈ S) (b : ι) :
    sgn R (S.erase a) b = if a < b then -sgn R S b else sgn R S b := by
  rw [sgn, sgn, Finset.filter_erase]
  split_ifs with hab
  · have hmem : a ∈ S.filter (· < b) := Finset.mem_filter.mpr ⟨ha, hab⟩
    rw [Finset.card_erase_of_mem hmem]
    obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_lt (Finset.card_pos.mpr ⟨a, hmem⟩)
    rw [hn]
    simp [pow_succ]
  · have hmem : a ∉ S.filter (· < b) := fun h ↦ hab (Finset.mem_filter.mp h).2
    rw [Finset.erase_eq_of_notMem hmem]

/-- The two ways of deleting two distinct vertices carry opposite signs. -/
private theorem sgn_erase_add {S : Finset ι} {a b : ι} (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b) :
    sgn R S a * sgn R (S.erase a) b + sgn R S b * sgn R (S.erase b) a = 0 := by
  rw [sgn_erase ha, sgn_erase hb]
  rcases hab.lt_or_gt with h | h
  · simp [h, h.not_gt]; ring
  · simp [h, h.not_gt]; ring

/-- The sign identity behind the contracting homotopy that inserts a vertex `j ∉ S`. -/
private theorem sgn_insert_add {S : Finset ι} {a j : ι} (ha : a ∈ S) (hj : j ∉ S) :
    sgn R S a * sgn R (insert j (S.erase a)) j + sgn R (insert j S) j * sgn R (insert j S) a =
      0 := by
  have haj : a ≠ j := fun h ↦ hj (h ▸ ha)
  have h₁ : sgn R S a = sgn R ((insert j S).erase j) a := by rw [Finset.erase_insert hj]
  have h₂ : sgn R (insert j (S.erase a)) j = sgn R ((insert j S).erase a) j := by
    rw [Finset.erase_insert_of_ne haj.symm]
  rw [h₁, h₂, sgn_erase (Finset.mem_insert_self j S), sgn_erase (Finset.mem_insert_of_mem ha)]
  rcases haj.lt_or_gt with h | h
  · simp [h, h.not_gt]; ring
  · simp [h, h.not_gt]; ring

end Signs

variable (M : Type*) [AddCommGroup M] [Module R M] {ι : Type*} (f : ι → R)

/-! ### The complex -/

/-- The degree `p` term of the Čech complex of localizations: the product of the localizations
`M_{f_S}`, `f_S = ∏_{i ∈ S} f i`, over the subsets `S` with `p + 1` elements. -/
abbrev cechLocalizationTerm (p : ℕ) : Type _ :=
  (S : {S : Finset ι // S.card = p + 1}) → LocalizedModule (.powers (∏ i ∈ S.1, f i)) M

/-- The restriction `M_{f_T} → M_{f_S}` for `T ⊆ S`: the map out of `M_{f_T}` extending the
canonical map `M → M_{f_S}`, which exists since `f_T` divides `f_S`. -/
noncomputable def cechLocalizationRestriction {T S : Finset ι} (h : T ⊆ S) :
    LocalizedModule (.powers (∏ i ∈ T, f i)) M →ₗ[R]
      LocalizedModule (.powers (∏ i ∈ S, f i)) M :=
  restr <| (IsLocalizedModule.Away.isUnit_algebraMap (mkLinearMap _ M) _).algebraMap_of_dvd
    (Finset.prod_dvd_prod_of_subset T S f h)

/-- The restriction maps extend the canonical maps from `M`. -/
@[simp]
theorem cechLocalizationRestriction_mk {T S : Finset ι} (h : T ⊆ S) (m : M) :
    cechLocalizationRestriction M f h (mk m 1) = mk m 1 := by
  simp [cechLocalizationRestriction, restr]

/-- The restriction maps are compatible with composition. -/
theorem cechLocalizationRestriction_restriction {T S U : Finset ι} (hTS : T ⊆ S) (hSU : S ⊆ U)
    (x : LocalizedModule (.powers (∏ i ∈ T, f i)) M) :
    cechLocalizationRestriction M f hSU (cechLocalizationRestriction M f hTS x) =
      cechLocalizationRestriction M f (hTS.trans hSU) x :=
  restr_restr _ _ _ x

/-- The restriction maps are compatible with the canonical maps from `M`. -/
@[simp]
theorem cechLocalizationRestriction_comp_mkLinearMap {T S : Finset ι} (h : T ⊆ S) :
    cechLocalizationRestriction M f h ∘ₗ mkLinearMap _ M = mkLinearMap _ M :=
  restr_comp_mkLinearMap _

/-- The restriction `M_{f_T} → M_{f_S}` is the unique linear map extending the canonical map
`M → M_{f_S}`. -/
theorem eq_cechLocalizationRestriction {T S : Finset ι} (h : T ⊆ S)
    {g : LocalizedModule (.powers (∏ i ∈ T, f i)) M →ₗ[R]
      LocalizedModule (.powers (∏ i ∈ S, f i)) M}
    (hg : g ∘ₗ mkLinearMap _ M = mkLinearMap _ M) : g = cechLocalizationRestriction M f h :=
  restr_ext ((IsLocalizedModule.Away.isUnit_algebraMap (mkLinearMap _ M) _).algebraMap_of_dvd
    (Finset.prod_dvd_prod_of_subset T S f h))
    (hg.trans (cechLocalizationRestriction_comp_mkLinearMap M f h).symm)

/-- Restriction along `S ⊆ S` is the identity. -/
@[simp]
theorem cechLocalizationRestriction_self {S : Finset ι} (h : S ⊆ S)
    (x : LocalizedModule (.powers (∏ i ∈ S, f i)) M) :
    cechLocalizationRestriction M f h x = x :=
  restr_self _ x

/-- The augmentation `M → ∏_{|S| = 1} M_{f_S}`, sending `m` to `m / 1` in every factor. -/
noncomputable def cechLocalizationAugmentation : M →ₗ[R] cechLocalizationTerm M f 0 :=
  LinearMap.pi fun _ ↦ mkLinearMap _ M

@[simp]
theorem cechLocalizationAugmentation_apply (m : M) (S : {S : Finset ι // S.card = 0 + 1}) :
    cechLocalizationAugmentation M f m S = mk m 1 := by
  simp [cechLocalizationAugmentation]

/-! The differential is defined uniformly on the products `∏_{|S| = q} M_{f_S}` for all `q`,
including `q = 0`, where the only factor is `M_{f_∅} = M_1`. -/

/-- The product of the localizations over the subsets with `q` elements. -/
private abbrev Term (q : ℕ) : Type _ :=
  (S : {S : Finset ι // S.card = q}) → LocalizedModule (.powers (∏ i ∈ S.1, f i)) M

/-- The `T`-component of an element of `Term M f q`, which is zero unless `T` has `q`
elements. -/
private noncomputable def proj (q : ℕ) (T : Finset ι) :
    Term M f q →ₗ[R] LocalizedModule (.powers (∏ i ∈ T, f i)) M :=
  if h : T.card = q then
    LinearMap.proj (R := R) (φ := fun S : {S : Finset ι // S.card = q} ↦
      LocalizedModule (.powers (∏ i ∈ S.1, f i)) M) ⟨T, h⟩
  else 0

private theorem proj_of_card {q : ℕ} {T : Finset ι} (h : T.card = q) (x : Term M f q) :
    proj M f q T x = x ⟨T, h⟩ := by
  simp [proj, h]

private theorem proj_of_card_ne {q : ℕ} {T : Finset ι} (h : T.card ≠ q) (x : Term M f q) :
    proj M f q T x = 0 := by
  simp [proj, h]

open scoped Classical in
/-- The `T`-component of an element of `Term M f q`, restricted to `M_{f_S}`; it is zero when
`f_T` does not act invertibly on `M_{f_S}`. -/
private noncomputable def rc (q : ℕ) (S T : Finset ι) :
    Term M f q →ₗ[R] LocalizedModule (.powers (∏ i ∈ S, f i)) M :=
  if h : IsUnit (algebraMap R (Module.End R (LocalizedModule (.powers (∏ i ∈ S, f i)) M))
      (∏ i ∈ T, f i)) then restr h ∘ₗ proj M f q T else 0

private theorem rc_eq {q : ℕ} {S T : Finset ι}
    (h : IsUnit (algebraMap R (Module.End R (LocalizedModule (.powers (∏ i ∈ S, f i)) M))
      (∏ i ∈ T, f i))) (x : Term M f q) :
    rc M f q S T x = restr h (proj M f q T x) := by
  simp [rc, h]

private theorem rc_of_card_ne {q : ℕ} {S T : Finset ι} (hT : T.card ≠ q) (x : Term M f q) :
    rc M f q S T x = 0 := by
  unfold rc
  split_ifs <;> simp [proj_of_card_ne M f hT]

private theorem rc_self {q : ℕ} (S : {S : Finset ι // S.card = q}) (x : Term M f q) :
    rc M f q S.1 S.1 x = x S := by
  rw [rc_eq M f (IsLocalizedModule.Away.isUnit_algebraMap (mkLinearMap _ M) _), restr_self,
    proj_of_card M f S.2]

private theorem restr_rc {q : ℕ} {S T U : Finset ι}
    (h₁ : IsUnit (algebraMap R (Module.End R (LocalizedModule (.powers (∏ i ∈ T, f i)) M))
      (∏ i ∈ U, f i)))
    (h₂ : IsUnit (algebraMap R (Module.End R (LocalizedModule (.powers (∏ i ∈ S, f i)) M))
      (∏ i ∈ T, f i)))
    (h₃ : IsUnit (algebraMap R (Module.End R (LocalizedModule (.powers (∏ i ∈ S, f i)) M))
      (∏ i ∈ U, f i))) (x : Term M f q) :
    restr h₂ (rc M f q T U x) = rc M f q S U x := by
  rw [rc_eq M f h₁, rc_eq M f h₃, restr_restr]

/-- If `T ⊆ S` then `f_T` acts invertibly on `M_{f_S}`. -/
private theorem isUnit_of_subset {T S : Finset ι} (h : T ⊆ S) :
    IsUnit (algebraMap R (Module.End R (LocalizedModule (.powers (∏ i ∈ S, f i)) M))
      (∏ i ∈ T, f i)) :=
  (IsLocalizedModule.Away.isUnit_algebraMap (mkLinearMap _ M) _).algebraMap_of_dvd
    (Finset.prod_dvd_prod_of_subset T S f h)

variable {M f} in
/-- The map induced on the products of localizations by a linear map `g : M → N`. -/
private noncomputable def termMap {N : Type*} [AddCommGroup N] [Module R N] (g : M →ₗ[R] N)
    (q : ℕ) : Term M f q →ₗ[R] Term N f q :=
  LinearMap.pi fun S ↦ IsLocalizedModule.map (.powers (∏ i ∈ S.1, f i)) (mkLinearMap _ M)
    (mkLinearMap _ N) g ∘ₗ LinearMap.proj S

private theorem termMap_apply {N : Type*} [AddCommGroup N] [Module R N] (g : M →ₗ[R] N)
    {q : ℕ} (x : Term M f q) (S : {S : Finset ι // S.card = q}) :
    termMap g q x S = IsLocalizedModule.map (.powers (∏ i ∈ S.1, f i)) (mkLinearMap _ M)
      (mkLinearMap _ N) g (x S) :=
  rfl

private theorem proj_termMap {N : Type*} [AddCommGroup N] [Module R N] (g : M →ₗ[R] N)
    (q : ℕ) (T : Finset ι) (x : Term M f q) :
    proj N f q T (termMap g q x) = IsLocalizedModule.map (.powers (∏ i ∈ T, f i))
      (mkLinearMap _ M) (mkLinearMap _ N) g (proj M f q T x) := by
  by_cases h : T.card = q
  · rw [proj_of_card N f h, proj_of_card M f h, termMap_apply]
  · rw [proj_of_card_ne N f h, proj_of_card_ne M f h, map_zero]

/-- The inclusion of `M` as the factor `M_{f_∅} = M_1`. -/
private noncomputable def incl : M →ₗ[R] Term M f 0 :=
  LinearMap.pi fun _ ↦ mkLinearMap _ M

private theorem coe_eq_one_of_mem_powers_prod_empty
    (c : Submonoid.powers (∏ i ∈ (∅ : Finset ι), f i)) : (c : R) = 1 := by
  obtain ⟨k, hk⟩ := c.2
  simp [← hk]

private theorem incl_injective : Function.Injective (incl M f) := by
  rw [injective_iff_map_eq_zero]
  intro m hm
  have h : mkLinearMap (.powers (∏ i ∈ (∅ : Finset ι), f i)) M m = mkLinearMap _ M 0 := by
    rw [map_zero]
    exact congrFun hm ⟨∅, Finset.card_empty⟩
  obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := .powers (∏ i ∈ (∅ : Finset ι), f i)) h
  rwa [Submonoid.smul_def, Submonoid.smul_def, coe_eq_one_of_mem_powers_prod_empty, one_smul,
    one_smul] at hc

private theorem incl_surjective : Function.Surjective (incl M f) := by
  intro x
  obtain ⟨⟨m, c⟩, hm⟩ := IsLocalizedModule.surj
    (.powers (∏ i ∈ (∅ : Finset ι), f i)) (mkLinearMap _ M) (x ⟨∅, Finset.card_empty⟩)
  rw [Submonoid.smul_def, coe_eq_one_of_mem_powers_prod_empty, one_smul] at hm
  refine ⟨m, funext fun S ↦ ?_⟩
  obtain ⟨S, hS⟩ := S
  obtain rfl := Finset.card_eq_zero.mp hS
  exact hm.symm

variable [LinearOrder ι]

/-- The differential `∏_{|T| = q} M_{f_T} → ∏_{|S| = q + 1} M_{f_S}`. -/
private noncomputable def D (q : ℕ) : Term M f q →ₗ[R] Term M f (q + 1) :=
  LinearMap.pi fun S ↦ ∑ a ∈ S.1, sgn R S.1 a • rc M f q S.1 (S.1.erase a)

private theorem D_apply (q : ℕ) (x : Term M f q) (S : {S : Finset ι // S.card = q + 1}) :
    D M f q x S = ∑ a ∈ S.1, sgn R S.1 a • rc M f q S.1 (S.1.erase a) x := by
  simp [D]

/-- Restricting a component of `D x` to `M_{f_S}`. -/
private theorem rc_D {q : ℕ} {S T : Finset ι}
    (hTS : IsUnit (algebraMap R (Module.End R (LocalizedModule (.powers (∏ i ∈ S, f i)) M))
      (∏ i ∈ T, f i))) (hT : T.card = q + 1) (x : Term M f q) :
    rc M f (q + 1) S T (D M f q x) = ∑ a ∈ T, sgn R T a • rc M f q S (T.erase a) x := by
  rw [rc_eq M f hTS, proj_of_card M f hT, D_apply, map_sum]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [map_smul, restr_rc M f (isUnit_of_subset M f (T.erase_subset a)) hTS
    (hTS.algebraMap_of_dvd (Finset.prod_dvd_prod_of_subset _ _ f (T.erase_subset a)))]

private theorem D_D (q : ℕ) (x : Term M f q) : D M f (q + 1) (D M f q x) = 0 := by
  funext S
  rw [D_apply]
  have key : ∀ a ∈ S.1, sgn R S.1 a • rc M f (q + 1) S.1 (S.1.erase a) (D M f q x) =
      ∑ b ∈ S.1.erase a, (sgn R S.1 a * sgn R (S.1.erase a) b) •
        rc M f q S.1 ((S.1.erase a).erase b) x := by
    intro a ha
    rw [rc_D M f (isUnit_of_subset M f (S.1.erase_subset a))
      (by rw [Finset.card_erase_of_mem ha, S.2]; rfl), Finset.smul_sum]
    simp only [mul_smul]
  rw [Finset.sum_congr rfl key]
  refine Finset.sum_sum_erase_eq_zero _ fun a ha b hb hab ↦ ?_
  rw [Finset.erase_right_comm (a := b), ← add_smul, sgn_erase_add ha hb hab, zero_smul]

/-! ### The contracting homotopy after inverting `f j` -/

/-- Inserting the vertex `j`: the candidate contracting homotopy, which is one when `f j` acts
invertibly on `M`. -/
private noncomputable def H (j : ι) (q : ℕ) : Term M f (q + 1) →ₗ[R] Term M f q :=
  LinearMap.pi fun T ↦ sgn R (insert j T.1) j • rc M f (q + 1) T.1 (insert j T.1)

private theorem H_apply (j : ι) (q : ℕ) (y : Term M f (q + 1))
    (T : {T : Finset ι // T.card = q}) :
    H M f j q y T = sgn R (insert j T.1) j • rc M f (q + 1) T.1 (insert j T.1) y := by
  simp [H]

variable {M f}

private theorem prod_insert_dvd (j : ι) (S : Finset ι) :
    ∏ i ∈ insert j S, f i ∣ f j * ∏ i ∈ S, f i := by
  by_cases h : j ∈ S
  · rw [Finset.insert_eq_of_mem h]
    exact dvd_mul_left _ _
  · rw [Finset.prod_insert h]

section Homotopy

variable {j : ι} (hj : IsUnit (algebraMap R (Module.End R M) (f j)))
include hj

omit [LinearOrder ι] in
/-- If `f j` acts invertibly on `M`, then `f_T` acts invertibly on `M_{f_S}` whenever `f_T`
divides `f j * f_S`. -/
private theorem isUnit_of_dvd_mul {S T : Finset ι} (h : ∏ i ∈ T, f i ∣ f j * ∏ i ∈ S, f i) :
    IsUnit (algebraMap R (Module.End R (LocalizedModule (.powers (∏ i ∈ S, f i)) M))
      (∏ i ∈ T, f i)) := by
  refine IsUnit.algebraMap_of_dvd ?_ h
  rw [map_mul]
  exact (IsLocalizedModule.isUnit_algebraMap_of_isUnit (.powers (∏ i ∈ S, f i))
    (mkLinearMap _ M) hj).mul
    (IsLocalizedModule.Away.isUnit_algebraMap (mkLinearMap _ M) _)

private theorem rc_H {q : ℕ} {S T : Finset ι}
    (hTS : IsUnit (algebraMap R (Module.End R (LocalizedModule (.powers (∏ i ∈ S, f i)) M))
      (∏ i ∈ T, f i))) (hT : T.card = q) (y : Term M f (q + 1)) :
    rc M f q S T (H M f j q y) = sgn R (insert j T) j • rc M f (q + 1) S (insert j T) y := by
  rw [rc_eq M f hTS, proj_of_card M f hT, H_apply, map_smul]
  congr 1
  refine restr_rc M f (isUnit_of_dvd_mul hj (prod_insert_dvd j T)) hTS
    (IsUnit.algebraMap_of_dvd ?_ (prod_insert_dvd j T)) y
  rw [map_mul]
  exact (IsLocalizedModule.isUnit_algebraMap_of_isUnit (.powers (∏ i ∈ S, f i))
    (mkLinearMap _ M) hj).mul hTS

private theorem D_H_of_mem {q : ℕ} (y : Term M f (q + 1)) (S : {S : Finset ι // S.card = q + 1})
    (h : j ∈ S.1) : D M f q (H M f j q y) S = y S := by
  rw [D_apply, Finset.sum_eq_single j]
  · rw [rc_H hj (isUnit_of_subset M f (S.1.erase_subset j))
      (by rw [Finset.card_erase_of_mem h, S.2]; rfl), smul_smul]
    have hS : insert j (S.1.erase j) = S.1 := Finset.insert_erase h
    have hsgn : sgn R (insert j (S.1.erase j)) j = sgn R S.1 j := by rw [hS]
    have hrc : rc M f (q + 1) S.1 (insert j (S.1.erase j)) y = rc M f (q + 1) S.1 S.1 y := by
      rw [hS]
    rw [hsgn, hrc, sgn_mul_self, one_smul, rc_self]
  · intro a ha haj
    have hT : insert j (S.1.erase a) = S.1.erase a :=
      Finset.insert_eq_of_mem (Finset.mem_erase.mpr ⟨Ne.symm haj, h⟩)
    rw [rc_H hj (isUnit_of_subset M f (S.1.erase_subset a))
      (by rw [Finset.card_erase_of_mem ha, S.2]; rfl), rc_of_card_ne M f (by
        rw [hT, Finset.card_erase_of_mem ha, S.2]; simp), smul_zero, smul_zero]
  · exact fun h' ↦ (h' h).elim

private theorem D_H_apply {q : ℕ} (y : Term M f (q + 1))
    (S : {S : Finset ι // S.card = q + 1}) :
    D M f q (H M f j q y) S = ∑ a ∈ S.1, (sgn R S.1 a * sgn R (insert j (S.1.erase a)) j) •
      rc M f (q + 1) S.1 (insert j (S.1.erase a)) y := by
  rw [D_apply]
  refine Finset.sum_congr rfl fun a ha ↦ ?_
  rw [rc_H hj (isUnit_of_subset M f (S.1.erase_subset a))
    (by rw [Finset.card_erase_of_mem ha, S.2]; rfl), smul_smul]

omit hj in
private theorem H_D_of_mem {q : ℕ} (y : Term M f q) (S : {S : Finset ι // S.card = q})
    (h : j ∈ S.1) : H M f j q (D M f q y) S = 0 := by
  rw [H_apply, rc_of_card_ne M f (by rw [Finset.insert_eq_of_mem h, S.2]; simp), smul_zero]

private theorem H_D_of_notMem {q : ℕ} (y : Term M f q) (S : {S : Finset ι // S.card = q})
    (h : j ∉ S.1) : H M f j q (D M f q y) S = y S + ∑ a ∈ S.1,
      (sgn R (insert j S.1) j * sgn R (insert j S.1) a) •
        rc M f q S.1 (insert j (S.1.erase a)) y := by
  rw [H_apply, rc_D M f (isUnit_of_dvd_mul hj (prod_insert_dvd j S.1))
    (by rw [Finset.card_insert_of_notMem h, S.2]), Finset.sum_insert h, smul_add,
    Finset.smul_sum, smul_smul, sgn_mul_self, one_smul]
  have hS : (insert j S.1).erase j = S.1 := Finset.erase_insert h
  have hrc : rc M f q S.1 ((insert j S.1).erase j) y = rc M f q S.1 S.1 y := by rw [hS]
  rw [hrc, rc_self]
  congr 1
  refine Finset.sum_congr rfl fun a ha ↦ ?_
  have haj : a ≠ j := fun e ↦ h (e ▸ ha)
  rw [smul_smul, Finset.erase_insert_of_ne (Ne.symm haj)]

/-- The homotopy identity `d h + h d = 1` in positive degrees. -/
private theorem D_H_add_H_D {q : ℕ} (y : Term M f (q + 1)) :
    D M f q (H M f j q y) + H M f j (q + 1) (D M f (q + 1) y) = y := by
  funext S
  rw [Pi.add_apply]
  by_cases h : j ∈ S.1
  · rw [D_H_of_mem hj y S h, H_D_of_mem y S h, add_zero]
  · rw [D_H_apply hj y S, H_D_of_notMem hj y S h, add_left_comm, ← Finset.sum_add_distrib]
    conv_rhs => rw [← add_zero (y S)]
    congr 1
    refine Finset.sum_eq_zero fun a ha ↦ ?_
    rw [← add_smul, sgn_insert_add ha h, zero_smul]

/-- The homotopy identity `h d = 1` in degree zero. -/
private theorem H_D_zero (y : Term M f 0) : H M f j 0 (D M f 0 y) = y := by
  funext S
  have hS : S.1 = ∅ := Finset.card_eq_zero.mp S.2
  rw [H_D_of_notMem hj y S (by simp [hS])]
  simp [hS]

private theorem injective_D_zero : Function.Injective (D M f 0) :=
  Function.LeftInverse.injective (g := H M f j 0) (H_D_zero hj)

private theorem exact_D_of_isUnit (q : ℕ) : Function.Exact (D M f q) (D M f (q + 1)) := by
  intro y
  constructor
  · intro hy
    refine ⟨H M f j q y, ?_⟩
    have := D_H_add_H_D hj y
    rwa [hy, map_zero, add_zero] at this
  · rintro ⟨x, rfl⟩
    exact D_D M f q x

end Homotopy

/-! ### Localizing the complex -/

private theorem termMap_D {N : Type*} [AddCommGroup N] [Module R N] (g : M →ₗ[R] N)
    (q : ℕ) (x : Term M f q) : termMap g (q + 1) (D M f q x) = D N f q (termMap g q x) := by
  funext S
  rw [termMap_apply, D_apply, D_apply, map_sum]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [map_smul, rc_eq M f (isUnit_of_subset M f (S.1.erase_subset a)),
    rc_eq N f (isUnit_of_subset N f (S.1.erase_subset a)),
    restr_map g _ (isUnit_of_subset N f (S.1.erase_subset a)), proj_termMap]

variable (M f)

omit [LinearOrder ι] in
private theorem isLocalizedModule_termMap [Finite ι] (r : R) (q : ℕ) :
    IsLocalizedModule (.powers r) (termMap (f := f) (mkLinearMap (.powers r) M) q) := by
  have (S : {S : Finset ι // S.card = q}) : IsLocalizedModule (.powers r)
      (IsLocalizedModule.map (.powers (∏ i ∈ S.1, f i))
        (mkLinearMap (.powers (∏ i ∈ S.1, f i)) M)
        (mkLinearMap (.powers (∏ i ∈ S.1, f i)) (LocalizedModule (.powers r) M))
        (mkLinearMap (.powers r) M)) :=
    IsLocalizedModule.isLocalizedModule_map _ _ _ _
  have : Finite (Finset ι) := Finite.of_injective _ Finset.coe_injective
  exact IsLocalizedModule.pi (.powers r) _

attribute [local instance] isLocalizedModule_termMap

/-- Localizing the complex away from `r` gives the complex of `M_r`. -/
private theorem map_D [Finite ι] (r : R) (q : ℕ) :
    IsLocalizedModule.map (.powers r) (termMap (f := f) (mkLinearMap (.powers r) M) q)
      (termMap (mkLinearMap (.powers r) M) (q + 1)) (D M f q) =
      D (LocalizedModule (.powers r) M) f q := by
  refine IsLocalizedModule.linearMap_ext (.powers r) (termMap (mkLinearMap (.powers r) M) q)
    (termMap (mkLinearMap (.powers r) M) (q + 1)) ?_
  rw [IsLocalizedModule.map_comp]
  exact LinearMap.ext fun x ↦ termMap_D _ q x

omit [LinearOrder ι] in
private theorem isUnit_of_mem_range {r : Set.range f} {j : ι} (hj : f j = r.1) :
    IsUnit (algebraMap R (Module.End R (LocalizedModule (.powers r.1) M)) (f j)) := by
  rw [hj]
  exact IsLocalizedModule.Away.isUnit_algebraMap (mkLinearMap _ M) _

private theorem injective_D_zero_of_span [Finite ι] (hf : Ideal.span (Set.range f) = ⊤) :
    Function.Injective (D M f 0) := by
  refine injective_of_isLocalized_span (Set.range f) hf
    (fun r ↦ Term (LocalizedModule (.powers r.1) M) f 0) (fun r ↦ termMap (mkLinearMap _ M) 0)
    (fun r ↦ Term (LocalizedModule (.powers r.1) M) f 1) (fun r ↦ termMap (mkLinearMap _ M) 1)
    (D M f 0) fun r ↦ ?_
  obtain ⟨j, hj⟩ := r.2
  rw [map_D]
  exact injective_D_zero (isUnit_of_mem_range M f hj)

private theorem exact_D [Finite ι] (hf : Ideal.span (Set.range f) = ⊤) (q : ℕ) :
    Function.Exact (D M f q) (D M f (q + 1)) := by
  refine exact_of_isLocalized_span (Set.range f) hf
    (fun r ↦ Term (LocalizedModule (.powers r.1) M) f q) (fun r ↦ termMap (mkLinearMap _ M) q)
    (fun r ↦ Term (LocalizedModule (.powers r.1) M) f (q + 1))
    (fun r ↦ termMap (mkLinearMap _ M) (q + 1))
    (fun r ↦ Term (LocalizedModule (.powers r.1) M) f (q + 2))
    (fun r ↦ termMap (mkLinearMap _ M) (q + 2)) (D M f q) (D M f (q + 1)) fun r ↦ ?_
  obtain ⟨j, hj⟩ := r.2
  rw [map_D, map_D]
  exact exact_D_of_isUnit (isUnit_of_mem_range M f hj) q

/-! ### The augmented complex -/

/-- The differential of the Čech complex of localizations in degree `p`. The component of
`cechLocalizationDifferential M f p x` at `S` is the alternating sum of the restrictions of the
components of `x` at the subsets `S ∖ {a}` (`cechLocalizationDifferential_apply`). -/
noncomputable def cechLocalizationDifferential (p : ℕ) :
    cechLocalizationTerm M f p →ₗ[R] cechLocalizationTerm M f (p + 1) :=
  D M f (p + 1)

/-- The differential of the Čech complex: the component at `S` is
`∑_{a ∈ S} (-1)^k x_{S ∖ {a}}`, where `k` is the number of elements of `S` below `a`. -/
theorem cechLocalizationDifferential_apply (p : ℕ) (x : cechLocalizationTerm M f p)
    (S : {S : Finset ι // S.card = p + 1 + 1}) :
    cechLocalizationDifferential M f p x S = ∑ a ∈ S.1.attach,
      ((-1) ^ (S.1.filter (· < a.1)).card : R) •
        cechLocalizationRestriction M f (S.1.erase_subset a.1)
          (x ⟨S.1.erase a.1, by rw [Finset.card_erase_of_mem a.2, S.2]; rfl⟩) := by
  rw [cechLocalizationDifferential, D_apply, ← Finset.sum_attach]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [rc_eq M f (isUnit_of_subset M f (S.1.erase_subset a.1)),
    proj_of_card M f (by rw [Finset.card_erase_of_mem a.2, S.2]; rfl)]
  simp only [sgn, cechLocalizationRestriction]

private theorem augmentation_eq : cechLocalizationAugmentation M f = D M f 0 ∘ₗ incl M f := by
  refine LinearMap.ext fun m ↦ funext fun S ↦ ?_
  obtain ⟨S, hS⟩ := S
  obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hS
  have hsgn : sgn R {a} a = 1 := by simp [sgn, Finset.filter_singleton]
  rw [cechLocalizationAugmentation_apply, LinearMap.comp_apply, D_apply, Finset.sum_singleton,
    Finset.erase_singleton, rc_eq M f (isUnit_of_subset M f (Finset.empty_subset _)),
    proj_of_card M f Finset.card_empty, hsgn, one_smul]
  exact (cechLocalizationRestriction_mk M f (Finset.empty_subset {a}) m).symm

/-- The augmentation followed by the first differential is zero. -/
theorem cechLocalizationDifferential_comp_augmentation :
    cechLocalizationDifferential M f 0 ∘ₗ cechLocalizationAugmentation M f = 0 := by
  rw [augmentation_eq, cechLocalizationDifferential, ← LinearMap.comp_assoc]
  exact LinearMap.ext fun m ↦ D_D M f 0 (incl M f m)

/-- Two consecutive differentials compose to zero. -/
theorem cechLocalizationDifferential_comp_differential (p : ℕ) :
    cechLocalizationDifferential M f (p + 1) ∘ₗ cechLocalizationDifferential M f p = 0 :=
  LinearMap.ext (D_D M f (p + 1))

/-- If the `f i` generate the unit ideal, the augmentation of the Čech complex is injective. -/
theorem injective_cechLocalizationAugmentation [Finite ι]
    (hf : Ideal.span (Set.range f) = ⊤) :
    Function.Injective (cechLocalizationAugmentation M f) := by
  rw [augmentation_eq, LinearMap.coe_comp]
  exact (injective_D_zero_of_span M f hf).comp (incl_injective M f)

/-- If the `f i` generate the unit ideal, the Čech complex is exact at its degree `0` term. -/
theorem exact_cechLocalizationAugmentation_differential [Finite ι]
    (hf : Ideal.span (Set.range f) = ⊤) :
    Function.Exact (cechLocalizationAugmentation M f) (cechLocalizationDifferential M f 0) := by
  intro y
  rw [augmentation_eq, cechLocalizationDifferential, exact_D M f hf 0 y, LinearMap.coe_comp,
    (incl_surjective M f).range_comp]

/-- **Exactness of the Čech complex of localizations.** If `ι` is finite and the `f i` generate
the unit ideal, the Čech complex of localizations of `M` is exact in every positive degree. -/
theorem cechComplexLocalization_exact [Finite ι] (hf : Ideal.span (Set.range f) = ⊤) (p : ℕ) :
    Function.Exact (cechLocalizationDifferential M f p)
      (cechLocalizationDifferential M f (p + 1)) :=
  exact_D M f hf (p + 1)

end TauCeti

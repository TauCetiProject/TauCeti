/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.LocalRing.Quotient
import Mathlib.Algebra.Field.Equiv

/-!
# The maximal ideal and the cotangent space of a quotient of a local ring

Let `π : Q → A` be a surjective homomorphism of local rings. Then `π` maps `𝔪_Q` onto `𝔪_A`, and
an element of `Q` maps into `𝔪_A²` exactly when it lies in `ker π + 𝔪_Q²`. Consequently
lifts to `Q` of a basis of the cotangent space `𝔪_A / 𝔪_A²` span `𝔪_Q` modulo `ker π + 𝔪_Q²`,
and they are linearly independent modulo it.

The quotient of a local ring by a proper ideal is again local. For a local homomorphism `R → S`
with `S` local and an ideal `J` of `R`, the induced map `R ⧸ J → S ⧸ J S` is again local.
Dividing both sides of a local homomorphism by an ideal of the base, as in inductions on the
dimension of the base, therefore stays among local homomorphisms.
When `J` is the maximal ideal of `R` and generates the maximal ideal of `S`, this map is the
residue field extension, whose degree is then the rank of a finite free `S`.

## Main results

* `TauCeti.IsLocalRing.apply_mem_maximalIdeal_sq_iff`: `π a ∈ 𝔪_A²` if and only if
  `a ∈ ker π + 𝔪_Q²`.
* `TauCeti.IsLocalRing.not_isPrincipal_maximalIdeal_of_ker_le_sq`: if `ker π ≤ 𝔪_Q²` and no
  single element spans `𝔪_Q` modulo `𝔪_Q²`, then `𝔪_A` is not principal.
* `TauCeti.IsLocalRing.maximalIdeal_quotient_eq_span_range`: if `𝔪_Q = J + (yⱼ)`, then the images
  of the `yⱼ` generate the maximal ideal of `Q ⧸ J`.
* `TauCeti.IsLocalRing.exists_lift_finBasis_cotangentSpace`: lifts to `Q` of a basis of the
  cotangent space of `A`.
* `TauCeti.isLocalRing_quotient`: the quotient of a local ring by a proper ideal is local.
* `Ideal.Quotient.isLocalHom_algebraMap_quotient_map_quotient`: `R ⧸ J → S ⧸ J S` is a local
  homomorphism when `R → S` is one and `S` is local.
* `TauCeti.IsLocalRing.finrank_residueField_eq_finrank`: if `S` is finite free over `R` and
  `𝔪_R S = 𝔪_S`, the residue field extension has degree `[S : R]`, by Mathlib's
  `IsLocalRing.finrank_quotient_map`.
* `TauCeti.IsLocalRing.map_maximalIdeal_of_bijective_quotientMap`,
  `TauCeti.IsLocalRing.isLocalHom_of_bijective_quotientMap`,
  `TauCeti.IsLocalRing.faithfullyFlat_of_bijective_quotientMap`,
  `TauCeti.IsLocalRing.radical_map_maximalIdeal_of_bijective_quotientMap`: if `f : R →+* S` between
  local rings induces a bijection `R ⧸ 𝔪_R → S ⧸ 𝔪_R S`, then `𝔪_R S = 𝔪_S` (so `f` is local,
  faithfully flat when flat, and `𝔪_R S` has radical `𝔪_S`), without assuming `f` is local.
* `TauCeti.IsLocalRing.bijective_quotientMap_iff_map_maximalIdeal_eq_and_bijective_residueFieldMap`:
  for a local homomorphism `f : R →+* S`, `R ⧸ 𝔪_R → S ⧸ 𝔪_R S` is bijective if and only if
  `𝔪_R S = 𝔪_S` and `ResidueField.map f` is bijective.
* `TauCeti.IsLocalRing.isLocalRing_quotient_maximalIdeal_pow`: the truncation `R ⧸ 𝔪_R ^ (n + 1)`
  of a local ring is a local ring.
* `TauCeti.IsLocalRing.exists_maximalIdeal_pow_le_ker`: a local homomorphism to an Artinian local
  ring kills a power of the maximal ideal of the source.
-/

public section

namespace TauCeti.IsLocalRing

open _root_.IsLocalRing Module

variable {Q A : Type*} [CommRing Q] [IsLocalRing Q] [CommRing A] [IsLocalRing A]

/-- Along a surjective homomorphism of local rings `π : Q → A`, an element `a` maps into `𝔪_A²`
if and only if it lies in `ker π + 𝔪_Q²`. -/
theorem apply_mem_maximalIdeal_sq_iff {π : Q →+* A} (hπ : Function.Surjective π) (a : Q) :
    π a ∈ maximalIdeal A ^ 2 ↔ a ∈ RingHom.ker π ⊔ maximalIdeal Q ^ 2 := by
  rw [← map_maximalIdeal_of_surjective π hπ, ← Ideal.map_pow, ← Ideal.mem_comap,
    Ideal.comap_map_of_surjective' _ hπ, sup_comm]

/-- Along a surjective homomorphism of local rings `π : Q → A` with `ker π ≤ 𝔪_Q²`, the maximal
ideal of `A` is not principal as soon as no single element of `𝔪_Q` spans `𝔪_Q` modulo `𝔪_Q²`:
a generator `π z` of `𝔪_A` would give `𝔪_Q ≤ (z) + ker π ≤ (z) + 𝔪_Q²`. -/
theorem not_isPrincipal_maximalIdeal_of_ker_le_sq {π : Q →+* A} (hπ : Function.Surjective π)
    (hker : RingHom.ker π ≤ maximalIdeal Q ^ 2)
    (h : ∀ z ∈ maximalIdeal Q, ¬ maximalIdeal Q ≤ Ideal.span {z} ⊔ maximalIdeal Q ^ 2) :
    ¬ (maximalIdeal A).IsPrincipal := by
  rintro ⟨z', hz'⟩
  obtain ⟨z, rfl⟩ := hπ z'
  rw [Ideal.submodule_span_eq] at hz'
  have : IsLocalHom π := .of_surjective π hπ
  have hzm : z ∈ maximalIdeal Q := by
    rw [← maximalIdeal_comap π, Ideal.mem_comap, hz']
    exact Ideal.mem_span_singleton_self _
  refine h z hzm ?_
  calc maximalIdeal Q ≤ (maximalIdeal A).comap π := (maximalIdeal_comap π).ge
    _ = Ideal.span {z} ⊔ RingHom.ker π := by
      rw [hz', ← Set.image_singleton, ← Ideal.map_span, Ideal.comap_map_of_surjective _ hπ,
        RingHom.ker_eq_comap_bot]
    _ ≤ Ideal.span {z} ⊔ maximalIdeal Q ^ 2 := sup_le_sup_left hker _

omit [IsLocalRing A] in
/-- If the maximal ideal of `Q` is `J + (yⱼ)`, then the images of the `yⱼ` generate the maximal
ideal of the local ring `Q ⧸ J`. -/
theorem maximalIdeal_quotient_eq_span_range {κ : Type*} {J : Ideal Q} [IsLocalRing (Q ⧸ J)]
    {y : κ → Q} (h : maximalIdeal Q = J ⊔ Ideal.span (Set.range y)) :
    maximalIdeal (Q ⧸ J) = Ideal.span (Set.range (Ideal.Quotient.mk J ∘ y)) := by
  rw [← map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective, h, Ideal.map_sup,
    Ideal.map_quotient_self, bot_sup_eq, Ideal.map_span, Set.range_comp]

/-- **Lifts of a basis of the cotangent space of a quotient.** Let `π : Q → A` be a surjective
homomorphism of local rings, where `𝔪_Q` is finitely generated. Then there are lifts
`y : Fin e → Q` of a basis of `𝔪_A / 𝔪_A²`, where `e` is its dimension. They lie in `𝔪_Q`, span
`𝔪_Q` modulo `ker π + 𝔪_Q²`, and are linearly independent modulo it: a combination `∑ cⱼ yⱼ` lies
in `ker π + 𝔪_Q²` only if every `cⱼ ∈ 𝔪_Q`. -/
theorem exists_lift_finBasis_cotangentSpace (hfg : (maximalIdeal Q).FG) {π : Q →+* A}
    (hπ : Function.Surjective π) :
    ∃ y : Fin (finrank (ResidueField A) (CotangentSpace A)) → Q,
      (∀ j, y j ∈ maximalIdeal Q) ∧
      maximalIdeal Q ≤ Ideal.span (Set.range y) ⊔ (RingHom.ker π ⊔ maximalIdeal Q ^ 2) ∧
      ∀ c : Fin (finrank (ResidueField A) (CotangentSpace A)) → Q,
        ∑ j, c j * y j ∈ RingHom.ker π ⊔ maximalIdeal Q ^ 2 → ∀ j, c j ∈ maximalIdeal Q := by
  set e := finrank (ResidueField A) (CotangentSpace A)
  have hπ𝔪 : (maximalIdeal Q).map π = maximalIdeal A := map_maximalIdeal_of_surjective π hπ
  have : IsLocalHom π := .of_surjective π hπ
  have : Module.Finite A (maximalIdeal A) := Module.Finite.iff_fg.2 (hπ𝔪 ▸ hfg.map π)
  have : Module.Finite A (CotangentSpace A) :=
    .of_surjective _ (maximalIdeal A).toCotangent_surjective
  have : Module.Finite (ResidueField A) (CotangentSpace A) :=
    .of_restrictScalars_finite A _ _
  let bA := Module.finBasisOfFinrankEq (ResidueField A) (CotangentSpace A) rfl
  choose m hm using fun j ↦ (maximalIdeal A).toCotangent_surjective (bA j)
  choose y hy using fun j ↦ hπ (m j : A)
  have hy𝔪 (j : Fin e) : y j ∈ maximalIdeal Q := by
    rw [← maximalIdeal_comap π, Ideal.mem_comap, hy]
    exact (m j).property
  have hsum𝔪 (c : Fin e → Q) : π (∑ j, c j * y j) ∈ maximalIdeal A :=
    hπ𝔪 ▸ Ideal.mem_map_of_mem π (Ideal.sum_mem _ fun j _ ↦ Ideal.mul_mem_left _ _ (hy𝔪 j))
  have hcot (c : Fin e → Q) : (maximalIdeal A).toCotangent ⟨_, hsum𝔪 c⟩ =
      ∑ j, residue A (π (c j)) • bA j := by
    have : (⟨_, hsum𝔪 c⟩ : maximalIdeal A) = ∑ j, π (c j) • m j := by
      ext
      simp [hy]
    rw [this, map_sum]
    simp [hm, ← ResidueField.algebraMap_eq, algebraMap_smul]
  -- The `yⱼ` together with `ker π` span `𝔪` modulo `𝔪²` ...
  have hcov (a : Q) (ha : a ∈ maximalIdeal Q) :
      a ∈ Ideal.span (Set.range y) ⊔ (RingHom.ker π ⊔ maximalIdeal Q ^ 2) := by
    have haA : π a ∈ maximalIdeal A := hπ𝔪 ▸ Ideal.mem_map_of_mem π ha
    choose c hc using fun j ↦ (residue_surjective.comp hπ) (bA.repr
      ((maximalIdeal A).toCotangent ⟨_, haA⟩) j)
    have hspan : ∑ j, c j * y j ∈ Ideal.span (Set.range y) :=
      Ideal.sum_mem _ fun j _ ↦ Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)
    have hrest : a - ∑ j, c j * y j ∈ RingHom.ker π ⊔ maximalIdeal Q ^ 2 := by
      have hmem : π (a - ∑ j, c j * y j) ∈ maximalIdeal A :=
        (map_sub π _ _) ▸ sub_mem haA (hsum𝔪 c)
      rw [← apply_mem_maximalIdeal_sq_iff hπ, ← Ideal.toCotangent_eq_zero _ ⟨_, hmem⟩]
      have : (⟨_, hmem⟩ : maximalIdeal A) = ⟨_, haA⟩ - ⟨_, hsum𝔪 c⟩ :=
        Subtype.ext (map_sub π _ _)
      rw [this, map_sub, hcot]
      simp only [Function.comp_apply] at hc
      simp [hc, Basis.sum_repr]
    simpa using Submodule.add_mem_sup hspan hrest
  -- ... and are linearly independent modulo `ker π + 𝔪²`.
  have hind (c : Fin e → Q) (hc : ∑ j, c j * y j ∈ RingHom.ker π ⊔ maximalIdeal Q ^ 2)
      (j : Fin e) : c j ∈ maximalIdeal Q := by
    rw [← apply_mem_maximalIdeal_sq_iff hπ, ← Ideal.toCotangent_eq_zero _ ⟨_, hsum𝔪 c⟩,
      hcot] at hc
    have := (Fintype.linearIndependent_iff.1 bA.linearIndependent _ hc) j
    rw [residue_eq_zero_iff, ← Ideal.mem_comap, maximalIdeal_comap] at this
    exact this
  exact ⟨y, hy𝔪, fun a ha ↦ hcov a ha, hind⟩

end TauCeti.IsLocalRing

namespace TauCeti

/-- The quotient of a commutative local ring by a proper ideal is a local ring. -/
theorem isLocalRing_quotient {A : Type*} [CommRing A] [IsLocalRing A] {I : Ideal A} (hI : I ≠ ⊤) :
    IsLocalRing (A ⧸ I) :=
  have : Nontrivial (A ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  .of_surjective' _ Ideal.Quotient.mk_surjective

end TauCeti

namespace Ideal.Quotient

open _root_.IsLocalRing

variable {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing S] [Algebra R S]
  [IsLocalHom (algebraMap R S)]

/-- For a local homomorphism `R → S` to a local ring and an ideal `J` of `R`, the induced
homomorphism `R ⧸ J → S ⧸ J S` is local. The ring `R` need not be local. -/
instance isLocalHom_algebraMap_quotient_map_quotient (J : Ideal R) :
    IsLocalHom (algebraMap (R ⧸ J) (S ⧸ J.map (algebraMap R S))) := by
  refine ⟨fun a ha ↦ ?_⟩
  obtain ⟨r, rfl⟩ := mk_surjective a
  rw [algebraMap_quotient_map_quotient] at ha
  by_cases hJ : J = ⊤
  · subst hJ
    exact isUnit_of_subsingleton _
  -- A proper `J` consists of nonunits, so `J S` lies in the maximal ideal of `S`.
  have hJS : J.map (algebraMap R S) ≤ maximalIdeal S := map_le_iff_le_comap.mpr fun j hj ↦
    (mem_maximalIdeal _).mpr fun h ↦ hJ (J.eq_top_of_isUnit_mem hj (isUnit_of_map_unit _ j h))
  have : Nontrivial (S ⧸ J.map (algebraMap R S)) :=
    Ideal.Quotient.nontrivial_iff.mpr (ne_top_of_le_ne_top IsPrime.ne_top' hJS)
  have := IsLocalHom.of_surjective (mk (J.map (algebraMap R S))) mk_surjective
  exact (isUnit_of_map_unit (algebraMap R S) r (isUnit_of_map_unit (mk _) _ ha)).map _

end Ideal.Quotient

namespace TauCeti.IsLocalRing

open _root_.IsLocalRing Module

variable {R S : Type*} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]

/-- **Residue degree of a finite free extension in which the maximal ideal stays maximal.** If
`S` is a finite free extension of the local ring `R` and the maximal ideal of `R` generates the
maximal ideal of `S`, then the residue field extension has degree `[S : R]`.

The proof is adapted from that of Mathlib's `IsLocalRing.finrank_eq_finrank_residueField`, the
étale special case, and goes through Mathlib's `IsLocalRing.finrank_quotient_map`. -/
theorem finrank_residueField_eq_finrank [Algebra R S] [IsLocalHom (algebraMap R S)]
    [Module.Free R S] [Module.Finite R S]
    (h : (maximalIdeal R).map (algebraMap R S) = maximalIdeal S) :
    finrank (ResidueField R) (ResidueField S) = finrank R S := by
  rw [← finrank_quotient_map (R := R) (S := S)]
  -- `ResidueField R` is `R ⧸ 𝔪_R` and `ResidueField S` is `S ⧸ 𝔪_S`, by definition.
  refine (AddEquiv.toLinearEquiv (R := R ⧸ maximalIdeal R) (Ideal.quotEquivOfEq h).toAddEquiv
    fun r x ↦ ?_).finrank_eq.symm
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

/-- If a homomorphism `f : R →+* S` of local rings induces a bijection `R ⧸ 𝔪_R → S ⧸ 𝔪_R S`, then
the maximal ideal of `R` generates the maximal ideal of `S`; in particular `f` is local. -/
theorem map_maximalIdeal_of_bijective_quotientMap {f : R →+* S}
    (h : Function.Bijective (Ideal.quotientMap ((maximalIdeal R).map f) f Ideal.le_comap_map)) :
    (maximalIdeal R).map f = maximalIdeal S := by
  let _ : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field (maximalIdeal R)
  have hmax : ((maximalIdeal R).map f).IsMaximal :=
    Ideal.Quotient.maximal_ideal_iff_isField_quotient _ |>.mpr <|
      (RingEquiv.ofBijective _ h).toMulEquiv.isField_congr.mp (Field.toIsField _)
  exact eq_maximalIdeal hmax

/-- A homomorphism `f : R →+* S` of local rings that induces a bijection `R ⧸ 𝔪_R → S ⧸ 𝔪_R S` is
a local homomorphism. -/
theorem isLocalHom_of_bijective_quotientMap {f : R →+* S}
    (h : Function.Bijective (Ideal.quotientMap ((maximalIdeal R).map f) f Ideal.le_comap_map)) :
    IsLocalHom f :=
  ((local_hom_tfae f).out 1 3).mpr (map_maximalIdeal_of_bijective_quotientMap h).le

/-- A flat homomorphism of local rings `R → S` that induces a bijection `R ⧸ 𝔪_R → S ⧸ 𝔪_R S` is
faithfully flat. -/
theorem faithfullyFlat_of_bijective_quotientMap [Algebra R S] [Module.Flat R S]
    (h : Function.Bijective (Ideal.quotientMap ((maximalIdeal R).map (algebraMap R S))
      (algebraMap R S) Ideal.le_comap_map)) :
    Module.FaithfullyFlat R S := by
  have := isLocalHom_of_bijective_quotientMap h
  exact .of_flat_of_isLocalHom

/-- If a homomorphism `f : R →+* S` of local rings induces a bijection `R ⧸ 𝔪_R → S ⧸ 𝔪_R S`, then
the closed point of `Spec S` is the only point over the closed point of `Spec R`. -/
theorem radical_map_maximalIdeal_of_bijective_quotientMap {f : R →+* S}
    (h : Function.Bijective (Ideal.quotientMap ((maximalIdeal R).map f) f Ideal.le_comap_map)) :
    ((maximalIdeal R).map f).radical = maximalIdeal S := by
  rw [map_maximalIdeal_of_bijective_quotientMap h]
  exact (maximalIdeal.isMaximal S).isPrime.radical

/-- For a local homomorphism `f : R →+* S` of local rings, the induced map `R ⧸ 𝔪_R → S ⧸ 𝔪_R S` is
bijective if and only if `𝔪_R` generates `𝔪_S` and the induced map on residue fields is
bijective. -/
theorem bijective_quotientMap_iff_map_maximalIdeal_eq_and_bijective_residueFieldMap
    (f : R →+* S) [IsLocalHom f] :
    Function.Bijective (Ideal.quotientMap ((maximalIdeal R).map f) f Ideal.le_comap_map) ↔
      (maximalIdeal R).map f = maximalIdeal S ∧
        Function.Bijective (ResidueField.map f) := by
  -- `ResidueField R` is `R ⧸ 𝔪_R` and `ResidueField S` is `S ⧸ 𝔪_S`, by definition.
  have heq (hmap : (maximalIdeal R).map f = maximalIdeal S) :
      ⇑(Ideal.quotEquivOfEq hmap) ∘
        ⇑(Ideal.quotientMap ((maximalIdeal R).map f) f Ideal.le_comap_map) =
        ⇑(ResidueField.map f) := by
    funext x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Function.comp_apply, Ideal.quotientMap_mk, Ideal.quotEquivOfEq_mk, ← residue_def,
      ← residue_def, ResidueField.map_residue]
  refine ⟨fun h ↦ ?_, fun ⟨hmap, hres⟩ ↦ ?_⟩
  · have hmap := map_maximalIdeal_of_bijective_quotientMap h
    exact ⟨hmap, heq hmap ▸ (Ideal.quotEquivOfEq hmap).bijective.comp h⟩
  · exact (Ideal.quotEquivOfEq hmap).toEquiv.comp_bijective _ |>.mp (heq hmap ▸ hres)

end TauCeti.IsLocalRing

namespace TauCeti.IsLocalRing

open _root_.IsLocalRing

variable {R : Type*} [CommRing R] [IsLocalRing R]

/-- A positive power of the maximal ideal of a local ring is a proper ideal, so the quotient by it
is a nontrivial ring. No Noetherian or completeness hypothesis is needed. -/
instance nontrivial_quotient_maximalIdeal_pow (n : ℕ) :
    Nontrivial (R ⧸ maximalIdeal R ^ (n + 1)) :=
  Ideal.Quotient.nontrivial_iff.mpr
    ((Ideal.pow_le_self n.succ_ne_zero).trans_lt (maximalIdeal.isMaximal R).ne_top.lt_top).ne

/-- The quotient of a local ring by a positive power of its maximal ideal is a local ring. No
Noetherian or completeness hypothesis is needed. -/
instance isLocalRing_quotient_maximalIdeal_pow (n : ℕ) :
    IsLocalRing (R ⧸ maximalIdeal R ^ (n + 1)) :=
  .of_surjective' _ Ideal.Quotient.mk_surjective

/-- A local homomorphism from a local ring `R` to an Artinian local ring kills a power of the
maximal ideal of `R`, as the maximal ideal of the target is nilpotent. So it factors through a
truncation `R ⧸ 𝔪_R ^ (n + 1)`. -/
theorem exists_maximalIdeal_pow_le_ker {S : Type*} [CommRing S] [IsLocalRing S] [IsArtinianRing S]
    (f : R →+* S) [IsLocalHom f] : ∃ n, maximalIdeal R ^ (n + 1) ≤ RingHom.ker f := by
  obtain ⟨n, hn⟩ : IsNilpotent (maximalIdeal S) := by
    rw [← ringJacobson_eq_maximalIdeal]
    exact IsArtinianRing.isNilpotent_jacobson _
  refine ⟨n, (Ideal.pow_le_pow_right n.le_succ).trans ?_⟩
  calc maximalIdeal R ^ n
      ≤ ((maximalIdeal S).comap f) ^ n := Ideal.pow_right_mono (maximalIdeal_comap f).ge n
    _ ≤ (maximalIdeal S ^ n).comap f := Ideal.le_comap_pow _ n
    _ = RingHom.ker f := by rw [hn, Ideal.zero_eq_bot, RingHom.ker_eq_comap_bot]

end TauCeti.IsLocalRing

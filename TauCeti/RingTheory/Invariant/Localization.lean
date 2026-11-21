/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Operations
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.Ideal.Operations

/-!
# Invariant rings and localization

Let a monoid `G` act on a commutative semiring `A` by ring endomorphisms (automorphisms if `G` is
a group), and write `Aᴳ` for the invariants, as the subsemiring `FixedPoints.subsemiring A G` or,
when `A` is a ring, the subring `FixedPoints.subring A G`. This file compares invariants with
localization.

For a submonoid `M` of invariant elements, the action extends to the localization `M⁻¹A`
(`Localization (Algebra.algebraMapSubmonoid A M)`), compatibly with `A → M⁻¹A`. Here `M` may be a
submonoid of any commutative semiring `R` such that `A` is an `R`-algebra on which `G` acts by
`R`-algebra endomorphisms (`SMulCommClass G R A`), such as `Aᴳ` itself. When `G` is finite, taking
invariants commutes with this localization: `(M⁻¹A)ᴳ` is the localization of `Aᴳ` at `M`. A
fraction `a / s` fixed by every `g` satisfies `t_g (g • a) = t_g a` for some `t_g ∈ M`, which can
be replaced by the product `t` of the `t_g` because `G` is finite, and then `a / s = t a / (s t)`
with `t a` invariant. Taking `M` to be the powers of an invariant `r` gives the localization
`A[1/r]` of `A` at `r`. The argument only uses finitely many ring endomorphisms compatible with the
localization map, and is stated in that form: an arbitrary localization `S` of `A`, whose fixed
elements are described by an arbitrary semiring `R'` mapping injectively to `S`
(`TauCeti.FixedPoints.isLocalization_of_mem_range_iff`).

Also for a finite group `G` acting on a commutative ring `A`, the local homomorphism
`(Aᴳ)_P → A_Q` induced by `Aᴳ ⊆ A` at a prime `Q` of `A` lying over a prime `P` of `Aᴳ` is
injective. If an invariant `a` is killed by some `t ∉ Q`, prime avoidance applied to the
annihilator of `a`, which is `G`-stable, and the finitely many primes `g⁻¹ • Q` gives such a `t`
outside every `g⁻¹ • Q`; then the invariant `∏ g, g • t` lies outside `P` and kills `a`.

These are the two local facts behind the categorical universal property of the affine invariant
quotient `Spec A ⟶ Spec Aᴳ` for arbitrary target schemes.

## Main definitions

* `TauCeti.FixedPoints.localizationRingEnd G A M`: the action of `G` on `M⁻¹A` for a submonoid
  `M` of `R`, by the ring endomorphisms `IsLocalization.map` induced by the action on `A`, which
  provides the instance `MulSemiringAction G (Localization (Algebra.algebraMapSubmonoid A M))`.
* The instances `Algebra (FixedPoints.subsemiring A G)
  (FixedPoints.subsemiring (Localization (Algebra.algebraMapSubmonoid A M)) G)` and, for a ring
  `A`, `Algebra (FixedPoints.subring A G)
  (FixedPoints.subring (Localization (Algebra.algebraMapSubmonoid A M)) G)`, given by `A → M⁻¹A`.

## Main results

* `TauCeti.FixedPoints.smul_algebraMap_localization`: `A → M⁻¹A` is `G`-equivariant.
* `TauCeti.FixedPoints.smul_mk'`: `G` acts on a fraction `a / s` through its numerator.
* `TauCeti.FixedPoints.isLocalization_of_mem_range_iff`: the elements of a localization fixed by
  finitely many compatible ring endomorphisms are the localization of the fixed elements.
* `TauCeti.FixedPoints.isLocalization_subsemiring` and, for a ring `A`,
  `TauCeti.FixedPoints.isLocalization`: for finite `G`, `(M⁻¹A)ᴳ` is the localization of `Aᴳ`
  at `M`.
* `Ideal.exists_mem_forall_smul_notMem`: for finite `G` acting on a ring, prime avoidance for the
  preimages `{a | g • a ∈ Q}` of a prime `Q`, which are the translates `g⁻¹ • Q` when `G` is a
  group.
* `Ideal.exists_notMem_dvd_of_forall_smul_notMem`: for a finite group `G`, an element outside every
  `g⁻¹ • Q` divides an invariant outside `Q`.
* `TauCeti.FixedPoints.localRingHom_injective`: for a finite group `G`, `(Aᴳ)_P → A_Q` is
  injective.

## References

* M. Demazure and A. Grothendieck, *Schémas en groupes (SGA 3)*, Exposé V, §1.
-/

public section

namespace TauCeti.FixedPoints

/-- **Fixed elements commute with localization.** Let `S` be a localization of `A` at the image of
a submonoid `M` of `R`, and let finitely many ring endomorphisms `σ i` of `A` and `τ i` of `S` be
compatible with `A → S`. If `R → A` and `R' → S` are injective with images the elements fixed by
every `σ i`, respectively every `τ i`, and `R → R'` is compatible with them, then `R'` is the
localization of `R` at `M`. A fraction `a / s` fixed by every `τ i` satisfies
`t_i σ i a = t_i a` for some `t_i ∈ M`, which can be replaced by the product `t` of the `t_i`
since there are finitely many `i`; then `a / s = t a / (s t)` with `t a` fixed. -/
theorem isLocalization_of_mem_range_iff {ι R A R' S : Type*} [Finite ι] [CommSemiring R]
    [CommSemiring A] [CommSemiring R'] [CommSemiring S] [Algebra R A] [Algebra A S] [Algebra R' S]
    [Algebra R R'] (M : Submonoid R) [IsLocalization (Algebra.algebraMapSubmonoid A M) S]
    (σ : ι → A →+* A) (τ : ι → S →+* S)
    (hστ : ∀ i a, τ i (algebraMap A S a) = algebraMap A S (σ i a))
    (hR : Function.Injective (algebraMap R A))
    (hσ : ∀ a, a ∈ Set.range (algebraMap R A) ↔ ∀ i, σ i a = a)
    (hR' : Function.Injective (algebraMap R' S))
    (hτ : ∀ s, s ∈ Set.range (algebraMap R' S) ↔ ∀ i, τ i s = s)
    (h : ∀ x, algebraMap R' S (algebraMap R R' x) = algebraMap A S (algebraMap R A x)) :
    IsLocalization M R' := by
  have hfix (x : R) (i : ι) :
      τ i (algebraMap A S (algebraMap R A x)) = algebraMap A S (algebraMap R A x) := by
    rw [hστ, (hσ _).mp ⟨x, rfl⟩ i]
  refine (_root_.isLocalization_iff _ _).mpr ⟨?_, ?_, ?_⟩
  · -- The image of `m ∈ M` is a unit of `S` whose inverse is again fixed.
    intro m
    have hu : IsUnit (algebraMap A S (algebraMap R A m)) :=
      IsLocalization.map_units S ⟨_, Algebra.mem_algebraMapSubmonoid_of_mem m⟩
    obtain ⟨v, hv⟩ := (hτ (hu.unit⁻¹ : Sˣ)).mpr fun i ↦ by
      refine Units.eq_inv_of_mul_eq_one_right ?_
      rw [← map_one (τ i), ← Units.inv_mul hu.unit, map_mul, IsUnit.unit_spec, hfix]
    refine isUnit_iff_exists_inv.mpr ⟨v, hR' ?_⟩
    rw [map_mul, h, hv, map_one]
    exact hu.mul_val_inv
  · -- A fixed fraction `a / s` equals `t a / (s t)` with `t ∈ M` and `t a` fixed.
    intro z
    obtain ⟨⟨a, _, ⟨s, hs, rfl⟩⟩, ha⟩ :=
      IsLocalization.surj (Algebra.algebraMapSubmonoid A M) (algebraMap R' S z)
    have hk (i : ι) : ∃ t ∈ M, algebraMap R A t * σ i a = algebraMap R A t * a := by
      have hi := congrArg (τ i) ha
      rw [map_mul, (hτ _).mp ⟨z, rfl⟩ i, hfix, hστ] at hi
      obtain ⟨⟨_, t, ht, rfl⟩, hti⟩ :=
        IsLocalization.exists_of_eq (M := Algebra.algebraMapSubmonoid A M) (hi.symm.trans ha)
      exact ⟨t, ht, hti⟩
    choose t ht hti using hk
    have := Fintype.ofFinite ι
    set T := ∏ i, t i
    have hT (i : ι) : algebraMap R A T * σ i a = algebraMap R A T * a := by
      obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem t (Finset.mem_univ i)
      rw [show T = t i * c from hc, map_mul, mul_comm (algebraMap R A (t i)), mul_assoc,
        mul_assoc, hti i]
    obtain ⟨b, hb⟩ := (hσ (algebraMap R A T * a)).mpr fun i ↦ by
      rw [map_mul, (hσ _).mp ⟨T, rfl⟩ i, hT i]
    refine ⟨(b, ⟨s * T, mul_mem hs (prod_mem fun i _ ↦ ht i)⟩), hR' ?_⟩
    simp only [map_mul, h, hb, ← ha]
    ring
  · -- Elements of `R` identified in `R'` are identified after multiplication by some `t ∈ M`.
    intro x y hxy
    have hxy' : algebraMap A S (algebraMap R A x) = algebraMap A S (algebraMap R A y) := by
      rw [← h, ← h, hxy]
    obtain ⟨⟨_, t, ht, rfl⟩, hty⟩ :=
      IsLocalization.exists_of_eq (M := Algebra.algebraMapSubmonoid A M) hxy'
    exact ⟨⟨t, ht⟩, hR (by simpa only [map_mul] using hty)⟩

section Semiring

variable {G A : Type*} [Monoid G] [CommSemiring A] [MulSemiringAction G A]

section Localization

variable {R : Type*} [CommSemiring R] [Algebra R A] [SMulCommClass G R A] (M : Submonoid R)

/-- An element of `G` maps the image in `A` of a submonoid of `R` into itself. -/
private theorem algebraMapSubmonoid_le_comap_toRingHom (g : G) :
    Algebra.algebraMapSubmonoid A M ≤
      (Algebra.algebraMapSubmonoid A M).comap (MulSemiringAction.toRingHom G A g) := by
  rintro _ ⟨m, hm, rfl⟩
  exact ⟨m, hm, (smul_algebraMap g m).symm⟩

variable (G A) in
/-- The action of `G` on the localization `M⁻¹A` at the image of a submonoid `M` of `R`, where
`G` acts on the `R`-algebra `A` by `R`-algebra endomorphisms, induced by its action on `A`: `g` acts
by the ring endomorphism `IsLocalization.map` of `g : A →+* A`, which is defined because `g` fixes
the denominators. -/
noncomputable def localizationRingEnd :
    G →* Localization (Algebra.algebraMapSubmonoid A M) →+*
      Localization (Algebra.algebraMapSubmonoid A M) where
  toFun g := IsLocalization.map _ (MulSemiringAction.toRingHom G A g)
    (algebraMapSubmonoid_le_comap_toRingHom M g)
  map_one' := IsLocalization.ringHom_ext (Algebra.algebraMapSubmonoid A M) <|
    RingHom.ext fun a ↦ by simp
  map_mul' g h := IsLocalization.ringHom_ext (Algebra.algebraMapSubmonoid A M) <|
    RingHom.ext fun a ↦ by simp [mul_smul]

/-- The action of `G` on `M⁻¹A` given by `localizationRingEnd`. -/
noncomputable instance instMulSemiringActionLocalization :
    MulSemiringAction G (Localization (Algebra.algebraMapSubmonoid A M)) :=
  MulSemiringAction.compHom _ (localizationRingEnd G A M)

/-- `localizationRingEnd G A M g` is the action of `g` on `M⁻¹A`. -/
theorem localizationRingEnd_apply (g : G) (x : Localization (Algebra.algebraMapSubmonoid A M)) :
    localizationRingEnd G A M g x = g • x :=
  rfl

/-- The action of `G` on `M⁻¹A` extends the action on `A`. -/
@[simp]
theorem smul_algebraMap_localization (g : G) (a : A) :
    g • algebraMap A (Localization (Algebra.algebraMapSubmonoid A M)) a =
      algebraMap A (Localization (Algebra.algebraMapSubmonoid A M)) (g • a) :=
  IsLocalization.map_eq (algebraMapSubmonoid_le_comap_toRingHom M g) a

/-- The action of `G` on `M⁻¹A` on fractions: `g • (a / s) = (g • a) / s`, since the
denominator `s` is invariant. -/
@[simp]
theorem smul_mk' (g : G) (a : A) (s : Algebra.algebraMapSubmonoid A M) :
    g • IsLocalization.mk' (Localization (Algebra.algebraMapSubmonoid A M)) a s =
      IsLocalization.mk' _ (g • a) s := by
  obtain ⟨m, -, hm⟩ := s.property
  have hs : g • (s : A) = s := hm ▸ smul_algebraMap g m
  rw [IsLocalization.eq_mk'_iff_mul_eq, ← hs, ← smul_algebraMap_localization,
    ← smul_algebraMap_localization, ← smul_mul', IsLocalization.mk'_spec]

/-- The localization map `A → M⁻¹A` sends invariants to invariants. -/
theorem algebraMap_mem_fixedPoints {a : A} (ha : a ∈ FixedPoints.submonoid G A) :
    algebraMap A (Localization (Algebra.algebraMapSubmonoid A M)) a ∈
      FixedPoints.submonoid G (Localization (Algebra.algebraMapSubmonoid A M)) := fun g ↦ by
  rw [smul_algebraMap_localization, ha g]

/-- The algebra structure of `(M⁻¹A)ᴳ` over `Aᴳ`, as invariant subsemirings, given by the
localization map `A → M⁻¹A`. -/
noncomputable instance instAlgebraLocalizationSubsemiring :
    Algebra (FixedPoints.subsemiring A G)
      (FixedPoints.subsemiring (Localization (Algebra.algebraMapSubmonoid A M)) G) :=
  (((algebraMap A (Localization (Algebra.algebraMapSubmonoid A M))).comp
    (FixedPoints.subsemiring A G).subtype).codRestrict (FixedPoints.subsemiring _ G)
      fun a ↦ algebraMap_mem_fixedPoints M a.property).toAlgebra

/-- The algebra map `Aᴳ → (M⁻¹A)ᴳ` of invariant subsemirings is the localization map
`A → M⁻¹A`. -/
@[simp]
theorem coe_algebraMap_localization_subsemiring (a : FixedPoints.subsemiring A G) :
    (algebraMap (FixedPoints.subsemiring A G)
        (FixedPoints.subsemiring (Localization (Algebra.algebraMapSubmonoid A M)) G) a :
      Localization (Algebra.algebraMapSubmonoid A M)) =
      algebraMap A (Localization (Algebra.algebraMapSubmonoid A M)) a :=
  rfl

end Localization

/-- **Invariants commute with localization at invariant elements.** For a finite monoid `G` and a
submonoid `M` of the invariant subsemiring `Aᴳ`, the invariants of `M⁻¹A` are the localization of
`Aᴳ` at `M`. -/
instance isLocalization_subsemiring [Finite G] (M : Submonoid (FixedPoints.subsemiring A G)) :
    IsLocalization M
      (FixedPoints.subsemiring (Localization (Algebra.algebraMapSubmonoid A M)) G) :=
  isLocalization_of_mem_range_iff M (MulSemiringAction.toRingHom G A)
    (MulSemiringAction.toRingHom G _) (smul_algebraMap_localization M) Subtype.val_injective
    (fun a ↦ ⟨fun ⟨b, hb⟩ ↦ hb ▸ b.property, fun ha ↦ ⟨⟨a, ha⟩, rfl⟩⟩) Subtype.val_injective
    (fun s ↦ ⟨fun ⟨b, hb⟩ ↦ hb ▸ b.property, fun hs ↦ ⟨⟨s, hs⟩, rfl⟩⟩) fun _ ↦ rfl

end Semiring

section Ring

variable {G A : Type*} [Monoid G] [CommRing A] [MulSemiringAction G A]

section Localization

variable {R : Type*} [CommSemiring R] [Algebra R A] [SMulCommClass G R A] (M : Submonoid R)

/-- The algebra structure of `(M⁻¹A)ᴳ` over `Aᴳ`, as invariant subrings, given by the localization
map `A → M⁻¹A`. -/
noncomputable instance instAlgebraLocalization :
    Algebra (FixedPoints.subring A G)
      (FixedPoints.subring (Localization (Algebra.algebraMapSubmonoid A M)) G) :=
  (((algebraMap A (Localization (Algebra.algebraMapSubmonoid A M))).comp
    (FixedPoints.subring A G).subtype).codRestrict (FixedPoints.subring _ G)
      fun a ↦ algebraMap_mem_fixedPoints M a.property).toAlgebra

/-- The algebra map `Aᴳ → (M⁻¹A)ᴳ` of invariant subrings is the localization map `A → M⁻¹A`. -/
@[simp]
theorem coe_algebraMap_localization (a : FixedPoints.subring A G) :
    (algebraMap (FixedPoints.subring A G)
        (FixedPoints.subring (Localization (Algebra.algebraMapSubmonoid A M)) G) a :
      Localization (Algebra.algebraMapSubmonoid A M)) =
      algebraMap A (Localization (Algebra.algebraMapSubmonoid A M)) a :=
  rfl

end Localization

/-- **Invariants commute with localization at invariant elements.** For a finite monoid `G` and a
submonoid `M` of the invariant subring `Aᴳ`, the invariants of `M⁻¹A` are the localization of `Aᴳ`
at `M`. -/
instance isLocalization [Finite G] (M : Submonoid (FixedPoints.subring A G)) :
    IsLocalization M (FixedPoints.subring (Localization (Algebra.algebraMapSubmonoid A M)) G) :=
  isLocalization_of_mem_range_iff M (MulSemiringAction.toRingHom G A)
    (MulSemiringAction.toRingHom G _) (smul_algebraMap_localization M) Subtype.val_injective
    (fun a ↦ ⟨fun ⟨b, hb⟩ ↦ hb ▸ b.property, fun ha ↦ ⟨⟨a, ha⟩, rfl⟩⟩) Subtype.val_injective
    (fun s ↦ ⟨fun ⟨b, hb⟩ ↦ hb ▸ b.property, fun hs ↦ ⟨⟨s, hs⟩, rfl⟩⟩) fun _ ↦ rfl

/-- **Prime avoidance for the preimages of a prime.** For a finite monoid `G`, if an ideal `I` of
`A` is contained in no preimage `{a | g • a ∈ Q}` of a prime `Q`, then some `u ∈ I` satisfies
`g • u ∉ Q` for every `g`. For a group `G` these preimages are the translates `g⁻¹ • Q`. -/
theorem _root_.Ideal.exists_mem_forall_smul_notMem [Finite G] (Q : Ideal A) [Q.IsPrime]
    {I : Ideal A} (hI : ∀ g : G, ¬ I ≤ Q.comap (MulSemiringAction.toRingHom G A g)) :
    ∃ u ∈ I, ∀ g : G, g • u ∉ Q := by
  by_contra! h
  obtain ⟨g, -, hg⟩ := (Ideal.subset_union_prime_finite Set.finite_univ 1 1
    fun g _ _ _ ↦ Ideal.comap_isPrime (MulSemiringAction.toRingHom G A g) Q).mp fun u hu ↦ by
      obtain ⟨g, hg⟩ := h u hu
      exact Set.mem_biUnion (Set.mem_univ g) hg
  exact hI g hg

end Ring

section LocalRingHom

variable {A G : Type*} [CommRing A] [Group G] [MulSemiringAction G A] [Finite G]

/-- **Norms of elements avoiding every translate of a prime.** For a finite group `G`, if
`g • u ∉ Q` for every `g`, then the invariant norm `∏ g, g • u` lies outside `Q` and is divisible
by `u`. -/
theorem _root_.Ideal.exists_notMem_dvd_of_forall_smul_notMem (Q : Ideal A) [Q.IsPrime] {u : A}
    (hu : ∀ g : G, g • u ∉ Q) : ∃ r : FixedPoints.subring A G, (r : A) ∉ Q ∧ u ∣ r := by
  have := Fintype.ofFinite G
  refine ⟨⟨∏ g : G, g • u, fun g ↦ Finset.smul_prod_perm u g⟩, fun hmem ↦ ?_, ?_⟩
  · obtain ⟨g, -, hg⟩ := (Ideal.IsPrime.prod_mem_iff (p := Q)).mp hmem
    exact hu g hg
  · simpa using Finset.dvd_prod_of_mem (fun g : G ↦ g • u) (Finset.mem_univ 1)

/-- If an invariant `x` is killed by an element outside a prime `Q`, it is killed by an invariant
element outside `Q`. This is prime avoidance for the `G`-stable annihilator of `x` and the
finitely many primes `g⁻¹ • Q`. -/
theorem exists_mul_eq_zero_of_mul_eq_zero (Q : Ideal A) [Q.IsPrime] (x : FixedPoints.subring A G)
    {t : A} (htQ : t ∉ Q) (htx : t * x = 0) :
    ∃ s ∈ FixedPoints.subring A G, s ∉ Q ∧ s * x = 0 := by
  set I : Ideal A := (Ideal.span {(x : A)}).annihilator
  have hI (u : A) : u ∈ I ↔ u * x = 0 := by
    rw [Submodule.mem_annihilator_span_singleton, smul_eq_mul]
  obtain ⟨u, huI, hu⟩ := Q.exists_mem_forall_smul_notMem (G := G) (I := I) fun g hg ↦ by
    -- The annihilator of `x` is `G`-stable, so it contains `g⁻¹ • t`, and then `t ∈ Q`.
    have hmem : g⁻¹ • t ∈ I := by
      rw [hI, ← x.property g⁻¹, ← smul_mul', htx, smul_zero]
    exact htQ (by simpa using hg hmem)
  obtain ⟨r, hrQ, c, hc⟩ := Q.exists_notMem_dvd_of_forall_smul_notMem hu
  exact ⟨r, r.property, hrQ, by rw [hc, mul_comm u, mul_assoc, (hI u).mp huI, mul_zero]⟩

/-- **Invariants inject into stalks.** For a finite group `G`, a prime `Q` of `A` and the prime
`P` of `Aᴳ` below it, the induced homomorphism of local rings `(Aᴳ)_P → A_Q` is injective. -/
theorem localRingHom_injective (P : Ideal (FixedPoints.subring A G)) (Q : Ideal A) [P.IsPrime]
    [Q.IsPrime] (hPQ : P = Q.comap (algebraMap (FixedPoints.subring A G) A)) :
    Function.Injective
      (Localization.localRingHom P Q (algebraMap (FixedPoints.subring A G) A) hPQ) := by
  refine IsLocalization.injective_of_map_algebraMap_zero (M := P.primeCompl) _ _ fun x hx ↦ ?_
  rw [Localization.localRingHom_to_map,
    IsLocalization.map_eq_zero_iff Q.primeCompl] at hx
  obtain ⟨⟨t, htQ⟩, htx⟩ := hx
  obtain ⟨s, hs, hsQ, hsx⟩ := exists_mul_eq_zero_of_mul_eq_zero Q x htQ htx
  refine (IsLocalization.map_eq_zero_iff P.primeCompl _ x).mpr
    ⟨⟨⟨s, hs⟩, fun h ↦ hsQ (by rwa [hPQ] at h)⟩, Subtype.ext hsx⟩

end LocalRingHom

end TauCeti.FixedPoints

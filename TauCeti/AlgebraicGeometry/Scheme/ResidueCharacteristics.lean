/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Invertible
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.RingTheory.Ideal.Int
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import TauCeti.AlgebraicGeometry.Scheme.Characteristic
public import TauCeti.AlgebraicGeometry.Scheme.CoefficientInvertibility
public import TauCeti.AlgebraicGeometry.Scheme.ZeroLocusComponents
public import TauCeti.Topology.Constructible.Basic
public import TauCeti.Topology.Sober

/-!
# Residue characteristics of a scheme

For a scheme `X`, the set `X.residueChars` of *residue characteristics* consists of the primes `p`
that are the characteristic of the residue field `κ(x)` at some point `x` of `X`. Residue
characteristic zero contributes nothing, so `X.residueChars` is empty exactly when every residue
field has characteristic zero, that is, when every prime is invertible on `X`. For example
`Spec ℚ` has no residue characteristics, `Spec ℤ` has every prime, `Spec ℤ_(2)` has only `2`, and
`Spec ℤ[1/6]` has the primes other than `2` and `3`.

These sets control the degrees allowed in desingularization by alterations: in Temkin's theorem a
scheme of finite type over a quasi-excellent base of dimension at most two is resolved by an
alteration whose generic degrees have all their prime factors in `X.residueChars`.

The characterizations below identify `p ∈ X.residueChars` with the failure of `p` to be invertible
on `X`, in the sense of `AlgebraicGeometry.Scheme.IsUnitNatCast`, and hence with `p` not being a
unit of `Γ(X, ⊤)`. From there the residue characteristics shrink along morphisms, are unchanged by
surjective morphisms, and are computed for affine schemes by the units of the ring.

Along a dominant morphism `f : X ⟶ S` of finite type to a Noetherian scheme only finitely many
residue characteristics are lost. By Chevalley's theorem the image of `f` contains a dense open
`U`. A residue characteristic `p` of `S` that is not one of `X` has its zero locus `V(p)` outside
`U`, and by Krull's principal ideal theorem a generic point of a component of `V(p)` is then a
generic point of a component of the closed complement of `U`. There are finitely many such points,
and each has a single residue characteristic.

## Main definitions

* `AlgebraicGeometry.Scheme.residueChars X`: the set of primes `p` for which some residue field of
  `X` has characteristic `p`.

## Main results

* `AlgebraicGeometry.Scheme.mem_residueChars_iff_not_isUnit`: for a prime `p`,
  `p ∈ X.residueChars` exactly when `p` is not a unit of `Γ(X, ⊤)`.
* `AlgebraicGeometry.Scheme.residueChars_eq_empty_iff_forall_charZero`: `X.residueChars` is empty
  exactly when every residue field of `X` has characteristic zero.
* `AlgebraicGeometry.Scheme.Hom.residueChars_subset`: a morphism `X ⟶ Y` gives
  `X.residueChars ⊆ Y.residueChars`, with equality for surjective morphisms
  (`AlgebraicGeometry.Scheme.residueChars_eq_of_surjective`).
* `TauCeti.AlgebraicGeometry.SchemeCharP.residueChars_eq`: a nonempty scheme of prime
  characteristic `p` has residue characteristics `{p}`.
* `AlgebraicGeometry.Scheme.Hom.finite_residueChars_diff`: for `f : X ⟶ S` dominant of finite type
  with `S` Noetherian, `S.residueChars \ X.residueChars` is finite.
* `AlgebraicGeometry.Scheme.mem_residueChars_Spec_iff`: for a commutative ring `R`,
  `p ∈ (Spec R).residueChars` exactly when `p` is a prime that is not a unit of `R`.
* `AlgebraicGeometry.Scheme.residueChars_Spec_of_charP` and
  `AlgebraicGeometry.Scheme.residueChars_Spec_of_algebraRat`: the spectrum of a nonzero ring of
  prime characteristic `p` has residue characteristics `{p}`, and that of a `ℚ`-algebra has none.
* `AlgebraicGeometry.Scheme.residueChars_Spec_int`,
  `AlgebraicGeometry.Scheme.residueChars_Spec_intLocalizationAtPrime` and
  `AlgebraicGeometry.Scheme.residueChars_Spec_intLocalizationAway`: the residue characteristics of
  `Spec ℤ`, `Spec ℤ_(ℓ)` and `Spec ℤ[1/n]`.

## References

* M. Temkin, *Tame distillation and desingularization by `p`-alterations*, Annals of Mathematics
  186 (2017), §1.2.1, §2.1.1 and §4.3.2.
-/

public section

open CategoryTheory Order Topology TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}} {p : ℕ}

/-- The only prime divisible by a prime `p` is `p` itself. -/
private theorem prime_and_dvd_iff_eq (hp : p.Prime) {q : ℕ} : q.Prime ∧ p ∣ q ↔ q = p :=
  ⟨fun ⟨hq, hpq⟩ ↦ ((Nat.prime_dvd_prime_iff_eq hp hq).mp hpq).symm,
    by rintro rfl; exact ⟨hp, dvd_rfl⟩⟩

/-- The residue characteristics of a scheme `X`: the primes `p` that are the characteristic of the
residue field `κ(x)` at some point `x` of `X`. Residue characteristic zero contributes nothing, and
the empty scheme has no residue characteristics. -/
def residueChars (X : Scheme.{u}) : Set ℕ :=
  {p | p.Prime ∧ ∃ x : X, ringChar (X.residueField x) = p}

theorem mem_residueChars :
    p ∈ X.residueChars ↔ p.Prime ∧ ∃ x : X, ringChar (X.residueField x) = p :=
  Iff.rfl

/-- Residue characteristics are primes. -/
theorem prime_of_mem_residueChars (hp : p ∈ X.residueChars) : p.Prime :=
  hp.1

/-- The characteristic of a residue field, when positive, is a residue characteristic. -/
theorem ringChar_residueField_mem_residueChars (x : X) (hx : ringChar (X.residueField x) ≠ 0) :
    ringChar (X.residueField x) ∈ X.residueChars :=
  ⟨(CharP.char_is_prime_or_zero (X.residueField x) _).resolve_right hx, x, rfl⟩

theorem mem_residueChars_iff_exists_charP :
    p ∈ X.residueChars ↔ p.Prime ∧ ∃ x : X, CharP (X.residueField x) p := by
  simp only [mem_residueChars, ringChar.eq_iff]

/-- A point `x ∈ U` lies in the zero locus of a section `a` over `U` exactly when `a` vanishes in
its residue field. -/
theorem mem_zeroLocus_singleton_iff {U : X.Opens} (a : Γ(X, U)) {x : X} (hx : x ∈ U) :
    x ∈ X.zeroLocus {a} ↔ X.evaluation U x hx a = 0 := by
  rw [zeroLocus_singleton, Set.mem_compl_iff, SetLike.mem_coe,
    ← X.evaluation_ne_zero_iff_mem_basicOpen x hx, not_not]

/-- A point `x ∈ U` lies in the zero locus of the function `n` on `U` exactly when `n` vanishes in
its residue field. -/
theorem mem_zeroLocus_natCast_iff {U : X.Opens} (n : ℕ) {x : X} (hx : x ∈ U) :
    x ∈ X.zeroLocus {(n : Γ(X, U))} ↔ (n : X.residueField x) = 0 := by
  rw [mem_zeroLocus_singleton_iff _ hx, map_natCast]

/-- A prime `p` is a residue characteristic exactly when it vanishes in some residue field. -/
theorem mem_residueChars_iff_exists_natCast_eq_zero :
    p ∈ X.residueChars ↔ p.Prime ∧ ∃ x : X, (p : X.residueField x) = 0 := by
  refine and_congr_right fun hp ↦ exists_congr fun x ↦ ?_
  rw [ringChar.eq_iff, CharP.charP_iff_prime_eq_zero hp]

/-- A prime `p` is a residue characteristic exactly when it is not invertible on `X`. -/
theorem mem_residueChars_iff_not_isUnitNatCast :
    p ∈ X.residueChars ↔ p.Prime ∧ ¬X.IsUnitNatCast p := by
  simp only [mem_residueChars_iff_exists_natCast_eq_zero,
    isUnitNatCast_iff_forall_residueField_ne_zero, ne_eq, not_forall, not_not]

/-- A prime `p` is a residue characteristic exactly when it is not a unit of `Γ(X, ⊤)`. -/
theorem mem_residueChars_iff_not_isUnit :
    p ∈ X.residueChars ↔ p.Prime ∧ ¬IsUnit (p : Γ(X, ⊤)) := by
  rw [mem_residueChars_iff_not_isUnitNatCast, isUnitNatCast_iff_isUnit]

/-- A scheme has no residue characteristics exactly when every prime is invertible on it. -/
theorem residueChars_eq_empty_iff_forall_isUnitNatCast :
    X.residueChars = ∅ ↔ ∀ p : ℕ, p.Prime → X.IsUnitNatCast p := by
  simp only [Set.eq_empty_iff_forall_notMem, mem_residueChars_iff_not_isUnitNatCast, not_and,
    not_not]

/-- A scheme has no residue characteristics exactly when every prime is a unit of `Γ(X, ⊤)`. -/
theorem residueChars_eq_empty_iff_forall_isUnit :
    X.residueChars = ∅ ↔ ∀ p : ℕ, p.Prime → IsUnit (p : Γ(X, ⊤)) := by
  simp only [residueChars_eq_empty_iff_forall_isUnitNatCast, isUnitNatCast_iff_isUnit]

/-- A scheme has no residue characteristics exactly when all its residue fields have
characteristic zero. -/
theorem residueChars_eq_empty_iff_forall_charZero :
    X.residueChars = ∅ ↔ ∀ x : X, CharZero (X.residueField x) := by
  simp only [← CharP.ringChar_zero_iff_CharZero, Set.eq_empty_iff_forall_notMem]
  refine ⟨fun h x ↦ ?_, fun h p ⟨hp, x, hx⟩ ↦ hp.ne_zero (hx ▸ h x)⟩
  by_contra hx
  exact h _ (ringChar_residueField_mem_residueChars x hx)

/-- The empty scheme has no residue characteristics. -/
@[simp]
theorem residueChars_eq_empty_of_isEmpty [IsEmpty X] : X.residueChars = ∅ :=
  residueChars_eq_empty_iff_forall_charZero.mpr isEmptyElim

/-- Residue characteristics shrink along morphisms: the residue field at a point is an extension of
the residue field at its image, so the two have the same characteristic. -/
theorem Hom.residueChars_subset (f : X ⟶ Y) : X.residueChars ⊆ Y.residueChars := by
  intro p hp
  rw [mem_residueChars_iff_not_isUnitNatCast] at hp ⊢
  exact ⟨hp.1, fun h ↦ hp.2 (h.comap f)⟩

/-- An open subscheme has at most the residue characteristics of the ambient scheme. -/
theorem Opens.residueChars_subset (U : X.Opens) : (U : Scheme.{u}).residueChars ⊆ X.residueChars :=
  U.ι.residueChars_subset

/-- A surjective morphism does not change residue characteristics. -/
theorem residueChars_eq_of_surjective (f : X ⟶ Y) [Surjective f] :
    X.residueChars = Y.residueChars := by
  ext p
  simp only [mem_residueChars_iff_not_isUnitNatCast,
    isUnitNatCast_iff_of_surjective f f.surjective]

/-- A nonempty scheme of prime characteristic `p` has `p` as its only residue characteristic. -/
theorem _root_.TauCeti.AlgebraicGeometry.SchemeCharP.residueChars_eq [hp : Fact p.Prime]
    [Nonempty X] (h : SchemeCharP X p) : X.residueChars = {p} := by
  have : Nonempty (⊤ : X.Opens) := ⟨⟨Classical.arbitrary X, trivial⟩⟩
  have := h.charP_sections ⊤
  ext q
  simp only [mem_residueChars_iff_not_isUnit, CharP.isUnit_natCast_iff hp.out, not_not,
    Set.mem_singleton_iff]
  exact prime_and_dvd_iff_eq hp.out

/-! ### Dominant morphisms of finite type -/

/-- **Residue characteristics lost along a dominant morphism of finite type.** If `f : X ⟶ S` is
dominant and of finite type, with `S` Noetherian, then all but finitely many residue
characteristics of `S` are residue characteristics of `X`. -/
theorem Hom.finite_residueChars_diff {S : Scheme.{u}} (f : X ⟶ S) [IsNoetherian S]
    [LocallyOfFiniteType f] [QuasiCompact f] [IsDominant f] :
    (S.residueChars \ X.residueChars).Finite := by
  -- By Chevalley's theorem the image of `f` is constructible; it is dense, so its interior `U`
  -- is a dense open subset of `S`.
  have hT : IsConstructible (Set.range f) := by
    simpa only [Set.image_univ] using f.isConstructible_image IsConstructible.univ
  have hU : Dense (interior (Set.range f)) := hT.dense_interior f.denseRange
  -- The closed complement `Z` of `U` has finitely many component-generic points, and each lost
  -- residue characteristic is the characteristic of the residue field at one of them.
  let Z : Set S := (interior (Set.range f))ᶜ
  have : QuasiSober Z := isOpen_interior.isClosed_compl.isClosedEmbedding_subtypeVal.quasiSober
  have hG : (genericPoints Z).Finite :=
    genericPoints.finite TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
  refine (hG.image fun z : Z ↦ ringChar (S.residueField z)).subset ?_
  rintro p ⟨⟨hp, s, hs⟩, hpX⟩
  -- Take a maximal point `w` of the zero locus `V(p)` of `p`, a generization of `s`.
  have hsV : s ∈ S.zeroLocus {(p : Γ(S, ⊤))} := by
    rw [mem_zeroLocus_natCast_iff _ trivial, ← hs, ringChar.Nat.cast_ringChar]
  obtain ⟨w, hw, -⟩ := TauCeti.AlgebraicGeometry.Scheme.exists_maximal_mem_zeroLocus_specializes hsV
  have hwp : (p : S.residueField w) = 0 := (mem_zeroLocus_natCast_iff p trivial).mp hw.prop
  -- The point `w` is not in the image of `f`, since `p` is not a residue characteristic of `X`.
  have hwZ : w ∈ Z := by
    rintro hwU
    obtain ⟨x, rfl⟩ := interior_subset hwU
    exact hpX (mem_residueChars_iff_exists_natCast_eq_zero.mpr
      ⟨hp, x, by rw [← map_natCast (f.residueFieldMap x).hom, hwp, map_zero]⟩)
  refine ⟨⟨w, hwZ⟩, ?_, CharP.ringChar_of_prime_eq_zero hp hwp⟩
  -- A proper generization `y` of `w` has coheight zero by Krull's principal ideal theorem, so it
  -- is the generic point of a component of `S`, which lies in `U`; hence `y ∉ Z`.
  rw [TauCeti.mem_genericPoints_iff]
  rintro ⟨y, hyZ⟩ hyw
  have hyw : y ⤳ w := subtype_specializes_iff _ _ |>.mp hyw
  ext
  by_contra hne
  have hlt : w < y := ⟨hyw, fun h ↦ hne (hyw.antisymm h).eq⟩
  have hy0 : coheight y = 0 := by
    have h := coheight_strictAnti hlt (TauCeti.AlgebraicGeometry.Scheme.coheight_lt_top y)
    have h1 := TauCeti.AlgebraicGeometry.Scheme.coheight_le_one_of_maximal_mem_zeroLocus hw
    exact Order.lt_one_iff.mp (h.trans_le h1)
  have hyG : y ∈ genericPoints S := by
    rw [TauCeti.mem_genericPoints_iff]
    exact fun z hzy ↦ (hzy.antisymm (coheight_eq_zero.mp hy0 hzy)).eq
  exact hyZ (hU.genericPoints_subset isOpen_interior hyG)

/-! ### Affine schemes -/

/-- The residue characteristics of `Spec R` are the primes that are not units of `R`. -/
@[simp]
theorem mem_residueChars_Spec_iff (R : CommRingCat.{u}) :
    p ∈ (Spec R).residueChars ↔ p.Prime ∧ ¬IsUnit (p : R) := by
  rw [mem_residueChars_iff_not_isUnitNatCast, isUnitNatCast_Spec_iff]

/-- The spectrum of a nonzero ring of prime characteristic `p` has `p` as its only residue
characteristic. -/
theorem residueChars_Spec_of_charP (R : CommRingCat.{u}) [Nontrivial R] (p : ℕ) [Fact p.Prime]
    [CharP R p] : (Spec R).residueChars = {p} :=
  ((SchemeCharP.spec_iff R).mpr ‹_›).residueChars_eq

/-- The spectrum of a `ℚ`-algebra, for instance of a field of characteristic zero, has no residue
characteristics. -/
theorem residueChars_Spec_of_algebraRat (R : CommRingCat.{u}) [Algebra ℚ R] :
    (Spec R).residueChars = ∅ := by
  ext p
  simp only [mem_residueChars_Spec_iff, Set.mem_empty_iff_false, iff_false, not_and, not_not]
  intro hp
  rw [← map_natCast (algebraMap ℚ R)]
  exact (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr hp.ne_zero)).map _

/-! ### Examples -/

/-- Every prime is a residue characteristic of `Spec ℤ`. -/
theorem residueChars_Spec_int : (Spec (.of ℤ)).residueChars = {p | p.Prime} := by
  ext p
  simp only [mem_residueChars_Spec_iff, Set.mem_ofPred_eq, and_iff_left_iff_imp]
  intro hp h
  exact hp.ne_one (by simpa [Int.isUnit_iff_natAbs_eq] using h)

/-- The localization `ℤ_(ℓ)` of the integers at a prime `ℓ` has `ℓ` as its only residue
characteristic, although its generic residue field `ℚ` has characteristic zero. -/
theorem residueChars_Spec_intLocalizationAtPrime (ℓ : ℕ) [hℓ : Fact ℓ.Prime] :
    (Spec (.of (Localization.AtPrime (Ideal.span {(ℓ : ℤ)})))).residueChars = {ℓ} := by
  ext p
  rw [mem_residueChars_Spec_iff,
    ← map_natCast (algebraMap ℤ (Localization.AtPrime (Ideal.span {(ℓ : ℤ)}))) p]
  rw [IsLocalization.AtPrime.isUnit_to_map_iff _ (Ideal.span {(ℓ : ℤ)})]
  simp only [Ideal.mem_primeCompl_iff, Ideal.mem_span_singleton, Int.natCast_dvd_natCast, not_not,
    Set.mem_singleton_iff]
  exact prime_and_dvd_iff_eq hℓ.out

/-- Inverting `n` in the integers removes exactly the prime divisors of `n` from the residue
characteristics; for instance `Spec ℤ[1/6]` has the primes other than `2` and `3`. -/
theorem residueChars_Spec_intLocalizationAway (n : ℕ) :
    (Spec (.of (Localization.Away (n : ℤ)))).residueChars = {p | p.Prime ∧ ¬p ∣ n} := by
  ext p
  rw [mem_residueChars_Spec_iff, ← map_natCast (algebraMap ℤ (Localization.Away (n : ℤ))) p]
  rw [IsLocalization.Away.algebraMap_isUnit_iff (n : ℤ), Set.mem_ofPred_eq]
  refine and_congr_right fun hp ↦ not_congr
    ⟨fun ⟨k, hk⟩ ↦ ?_, fun h ↦ ⟨1, by simpa using Int.natCast_dvd_natCast.mpr h⟩⟩
  exact Int.natCast_dvd_natCast.mp ((Nat.prime_iff_prime_int.mp hp).dvd_of_dvd_pow hk)

/-- `Spec ℚ` has no residue characteristics. -/
theorem residueChars_Spec_rat : (Spec (.of ℚ)).residueChars = ∅ :=
  residueChars_Spec_of_algebraRat _

end AlgebraicGeometry.Scheme

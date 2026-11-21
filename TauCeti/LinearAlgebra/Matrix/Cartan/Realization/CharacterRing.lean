/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Cartan.Realization.RootLattice
public import TauCeti.RingTheory.HahnSeries.Cone
public import TauCeti.RingTheory.HahnSeries.EmbDomain
public import TauCeti.RingTheory.HahnSeries.Geometric

/-!
# The character ring of a Cartan realization

Let `R` be a realization of a matrix over a field `K` of characteristic zero, with simple roots
`αᵢ ∈ H*` and positive root cone `Q₊ = ⊕ᵢ ℕ αᵢ`. The characters of highest-weight modules and of
the modules of category `O` are formal sums `∑_μ c_μ e^μ` over weights `μ ∈ H*` whose support lies
in finitely many translated cones `λ - Q₊`. This file constructs the ring they live in.

The ring `TauCeti.CartanRealization.CharacterRing R S` is the ring of Hahn series with
coefficients in `S` over the exponent type `TauCeti.CartanRealization.CharacterExponent R`, the
weights ordered by `μ ≤ ν ↔ μ - ν ∈ Q₊`. By the general theory of
`TauCeti/RingTheory/HahnSeries/Cone.lean`, a function on weights is a Hahn series exactly when its
support lies in finitely many cones `λ - Q₊` (`HahnSeries.ofConeBounded`,
`HahnSeries.exists_finset_sub_mem_of_coeff_ne_zero`), so this is the ring of cone-supported
characters, with Mathlib's convolution product. The independence of the simple roots in the full
dual, rather than after restriction to the coroot span, makes `Q₊` pointed even when the matrix is
singular, as in affine type.

The formal exponentials `e^μ` form a monoid homomorphism from the weights, with unit values. For
a nonzero `β ∈ Q₊` the element `1 - e^{-β}` is invertible, with inverse the geometric series
`∑_{n ≥ 0} e^{-nβ}`; for the simple roots these are the factors of the Weyl–Kac denominator.
With no simple roots the cone is zero and every character has finite support.

For a rational realization of an integral matrix with a coweight lattice, the characters with
exponents in the weight lattice `P` form a ring of the same kind over `P` and its own positive
root cone. Extension by zero is an injective ring homomorphism from it to the character ring of
the realization, whose image is the characters supported on `P`.

## Main definitions

* `TauCeti.CartanRealization.CharacterExponent R`: the weights of `R`, ordered by
  `μ ≤ ν ↔ μ - ν ∈ Q₊`.
* `TauCeti.CartanRealization.CharacterRing R S`: the ring of characters with coefficients in `S`.
* `TauCeti.CartanRealization.formalExp R S`: the formal exponentials `μ ↦ e^μ`.
* `TauCeti.CartanRealization.CoweightLattice.CharacterRing L S`: the characters with exponents in
  the weight lattice of a coweight lattice `L`.
* `TauCeti.CartanRealization.CoweightLattice.toCharacterRing L S`: extension by zero from the
  weight lattice to the full dual.

## Main results

* `TauCeti.CartanRealization.ringInverse_one_sub_formalExp_neg` and
  `TauCeti.CartanRealization.coeff_ringInverse_one_sub_formalExp_neg`: for a nonzero `β ∈ Q₊`,
  `(1 - e^{-β})⁻¹ = ∑_{n ≥ 0} e^{-nβ}`.
* `TauCeti.CartanRealization.finite_support_of_isEmpty`: with no simple roots, every character
  has finite support.
* `TauCeti.CartanRealization.CoweightLattice.toCharacterRing_injective` and
  `TauCeti.CartanRealization.CoweightLattice.mem_range_toCharacterRing_iff`: extension by zero is
  injective, and its image is the characters supported on the weight lattice.

## References

* V. G. Kac, *Infinite-dimensional Lie algebras*, third edition, §9.7 (the algebra `ℰ` of formal
  characters, its formal exponentials, and the invertibility of `1 - e^{-α}`).
-/

public section

open Module TauCeti.ConeExponent

namespace TauCeti

namespace CartanRealization

section CharZero

variable {I K H : Type*} [Field K] [CharZero K] [AddCommGroup H] [Module K H] {A : Matrix I I K}
  (R : CartanRealization A H)

/-- The exponents of the characters of a realization `R`: the weights `μ ∈ H*`, ordered by
`μ ≤ ν ↔ μ - ν ∈ Q₊`. This is the reverse of the order on weights
`TauCeti.CartanRealization.RootLE`, so that the cone `λ - Q₊` below a weight is the interval
`Set.Ici λ`. -/
abbrev CharacterExponent : Type _ :=
  ConeExponent R.isPointed_posRootCone

/-- The **character ring** of a realization `R` with coefficients in `S`: formal sums
`∑_μ c_μ e^μ` over weights `μ ∈ H*` whose support lies in finitely many cones `λ - Q₊`, realized as
the Hahn series over `TauCeti.CartanRealization.CharacterExponent R`. -/
abbrev CharacterRing (S : Type*) [Zero S] : Type _ :=
  HahnSeries R.CharacterExponent S

variable {R}

/-- The order on exponents of characters is the reverse of the order on weights. -/
theorem toConeExponent_le_toConeExponent_iff_rootLE {μ ν : Dual K H} :
    (toConeExponent μ : R.CharacterExponent) ≤ toConeExponent ν ↔ R.RootLE ν μ := by
  rw [toConeExponent_le_toConeExponent_iff, rootLE_iff, Submodule.mem_toAddSubmonoid]

variable (R)

/-- For a finite index set the positive root cone is finitely generated, so every function on
weights supported in finitely many cones `λ - Q₊` is a character (`HahnSeries.ofConeBounded`). -/
instance isAddFG_posRootCone [Finite I] : IsAddFG R.posRootCone.toAddSubmonoid := by
  rw [AddSubmonoid.isAddFG_iff_finite, posRootCone_def]
  exact ⟨Set.range R.root, Set.finite_range _, (Submodule.span_nat_eq_addSubmonoidClosure _).symm⟩

/-! ### Formal exponentials -/

section Semiring

variable (S : Type*) [Semiring S]

/-- The **formal exponentials** `μ ↦ e^μ`, the monomials of the character ring: a homomorphism
from the weights, written multiplicatively, so that `e^{μ + ν} = e^μ e^ν`. -/
noncomputable def formalExp : Multiplicative (Dual K H) →* R.CharacterRing S where
  toFun μ := HahnSeries.single (toConeExponent μ.toAdd) 1
  map_one' := (rfl)
  map_mul' μ ν := by
    rw [HahnSeries.single_mul_single, mul_one, toAdd_mul, toConeExponent_add]

theorem formalExp_ofAdd (μ : Dual K H) :
    R.formalExp S (.ofAdd μ) = HahnSeries.single (toConeExponent μ) 1 := (rfl)

open scoped Classical in
/-- The coefficients of `e^μ`. -/
@[simp]
theorem coeff_formalExp (μ ν : Dual K H) :
    (R.formalExp S (.ofAdd μ)).coeff (toConeExponent ν) = if ν = μ then 1 else 0 := by
  rw [formalExp_ofAdd]
  split_ifs with h
  · rw [h, HahnSeries.coeff_single_same]
  · exact HahnSeries.coeff_single_of_ne fun h' ↦ h (congrArg ofConeExponent h')

/-- `e^μ` is a unit, with inverse `e^{-μ}`. -/
theorem isUnit_formalExp (μ : Multiplicative (Dual K H)) : IsUnit (R.formalExp S μ) :=
  (Group.isUnit μ).map _

end Semiring

/-! ### The geometric series -/

section CommRing

variable {R} (S : Type*) [CommRing S] {β : Dual K H}

/-- A nonzero element `β` of the positive root cone gives a positive exponent `-β`. -/
theorem toConeExponent_neg_pos (hβ : β ∈ R.posRootCone) (hβ0 : β ≠ 0) :
    (0 : R.CharacterExponent) < toConeExponent (-β) := by
  refine lt_of_le_of_ne ?_ fun h ↦ hβ0 (neg_eq_zero.mp (congrArg ofConeExponent h).symm)
  rw [← toConeExponent_zero, toConeExponent_le_toConeExponent_iff, zero_sub, neg_neg]
  exact hβ

/-- **The geometric series in the character ring**: for a nonzero `β ∈ Q₊`, the inverse of
`1 - e^{-β}` is `∑_{n ≥ 0} e^{-nβ}`, the image of `∑ₙ Xⁿ` under `X ↦ e^{-β}`. -/
theorem ringInverse_one_sub_formalExp_neg (hβ : β ∈ R.posRootCone) (hβ0 : β ≠ 0) :
    Ring.inverse (1 - R.formalExp S (.ofAdd (-β))) =
      HahnSeries.ofPowerSeriesSingle S (toConeExponent_neg_pos hβ hβ0) (PowerSeries.mk 1) := by
  have h := HahnSeries.one_sub_single_mul_ofPowerSeriesSingle_mk_pow
    (toConeExponent_neg_pos hβ hβ0) (1 : S)
  simp only [one_pow, ← Pi.one_def] at h
  rw [formalExp_ofAdd, ← Ring.inverse_mul_cancel_left _ (HahnSeries.ofPowerSeriesSingle S _ _)
    (IsUnit.of_mul_eq_one _ h), h, mul_one]

/-- For a nonzero `β ∈ Q₊`, the series `1 - e^{-β}` is a unit of the character ring. -/
theorem isUnit_one_sub_formalExp_neg (hβ : β ∈ R.posRootCone) (hβ0 : β ≠ 0) :
    IsUnit (1 - R.formalExp S (.ofAdd (-β))) :=
  HahnSeries.isUnit_one_sub_single (toConeExponent_neg_pos hβ hβ0) 1

open scoped Classical in
/-- The coefficients of `(1 - e^{-β})⁻¹ = ∑_{n ≥ 0} e^{-nβ}`: `1` at the weights `-nβ` with
`n ≥ 0`, and `0` elsewhere. -/
theorem coeff_ringInverse_one_sub_formalExp_neg (hβ : β ∈ R.posRootCone) (hβ0 : β ≠ 0)
    (μ : Dual K H) :
    (Ring.inverse (1 - R.formalExp S (.ofAdd (-β)))).coeff (toConeExponent μ) =
      if ∃ n : ℕ, μ = -(n • β) then 1 else 0 := by
  rw [ringInverse_one_sub_formalExp_neg S hβ hβ0]
  split_ifs with h
  · obtain ⟨n, rfl⟩ := h
    rw [← neg_nsmul, toConeExponent_nsmul, HahnSeries.coeff_ofPowerSeriesSingle_nsmul,
      PowerSeries.coeff_mk, Pi.one_apply]
  · refine HahnSeries.coeff_ofPowerSeriesSingle_of_forall_ne _ _ fun n hn ↦ h ⟨n, ?_⟩
    rw [← neg_nsmul]
    exact (congrArg ofConeExponent hn).symm

end CommRing

/-! ### No simple roots -/

/-- With no simple roots the positive root cone is zero, so every character has finite support: the
character ring is the group ring of the weights. -/
theorem finite_support_of_isEmpty [IsEmpty I] {S : Type*} [Zero S] (f : R.CharacterRing S) :
    f.support.Finite := by
  classical
  obtain ⟨t, ht⟩ := HahnSeries.exists_finset_sub_mem_of_coeff_ne_zero f
  refine (t.finite_toSet.image toConeExponent).subset fun x hx ↦ ?_
  obtain ⟨b, hb, hbx⟩ := ht x.ofConeExponent hx
  refine ⟨b, hb, ConeExponent.ext ?_⟩
  have hbx' : b - x.ofConeExponent ∈ R.posRootCone := hbx
  generalize x.ofConeExponent = μ at hbx' ⊢
  rw [posRootCone_eq_bot, Submodule.mem_bot, sub_eq_zero] at hbx'
  simpa using hbx'

end CharZero

/-! ### Characters supported on the weight lattice -/

namespace CoweightLattice

variable {I H : Type*} [AddCommGroup H] [Module ℚ H] {A : Matrix I I ℤ}
  {R : CartanRealization (A.map (Int.cast : ℤ → ℚ)) H} (L : R.CoweightLattice)

/-- The positive root cone of the weight lattice: the natural span of the simple roots in `P`. -/
def posRootCone : Submodule ℕ L.weightLattice :=
  Submodule.span ℕ (Set.range L.root)

theorem posRootCone_def : L.posRootCone = Submodule.span ℕ (Set.range L.root) := (rfl)

/-- The positive root cone of the weight lattice is pointed. -/
theorem isPointed_posRootCone : L.posRootCone.toAddSubmonoid.IsPointed :=
  fun _ h h' ↦
    (L.linearIndependent_root.restrict_scalars' ℕ).eq_zero_of_mem_natSpan_of_neg_mem h h'

/-- A weight lies in the positive root cone of the weight lattice exactly when it lies in the
positive root cone of the realization. -/
theorem coe_mem_posRootCone_iff {φ : L.weightLattice} :
    (φ : Dual ℚ H) ∈ R.posRootCone ↔ φ ∈ L.posRootCone := by
  let ι : L.weightLattice →ₗ[ℕ] Dual ℚ H := L.weightLattice.subtype.restrictScalars ℕ
  have hι : Function.Injective ι := Subtype.val_injective
  have h : R.posRootCone = L.posRootCone.map ι := by
    rw [posRootCone_def, CartanRealization.posRootCone_def, ← Submodule.span_image,
      ← Set.range_comp]
    congr 2
    funext i
    exact (L.coe_root i).symm
  rw [h]
  exact ⟨fun ⟨ψ, hψ, he⟩ ↦ hι he ▸ hψ, fun hφ ↦ ⟨φ, hφ, rfl⟩⟩

/-- The exponents of characters supported on the weight lattice: the weights in `P`, ordered by
`μ ≤ ν ↔ μ - ν ∈ Q₊`. -/
abbrev CharacterExponent : Type _ :=
  ConeExponent L.isPointed_posRootCone

/-- The characters with coefficients in `S` and exponents in the weight lattice `P`: formal sums
`∑_μ c_μ e^μ` over `μ ∈ P` supported in finitely many cones `λ - Q₊`. -/
abbrev CharacterRing (S : Type*) [Zero S] : Type _ :=
  HahnSeries L.CharacterExponent S

/-- The inclusion of the weight lattice into the full dual, on exponents of characters. -/
def toCharacterExponent : L.CharacterExponent →+ R.CharacterExponent :=
  ConeExponent.map L.weightLattice.subtype.toAddMonoidHom

@[simp]
theorem ofConeExponent_toCharacterExponent (x : L.CharacterExponent) :
    (L.toCharacterExponent x).ofConeExponent = x.ofConeExponent :=
  ofConeExponent_map _ x

@[simp]
theorem toCharacterExponent_toConeExponent (φ : L.weightLattice) :
    L.toCharacterExponent (toConeExponent φ) = toConeExponent (φ : Dual ℚ H) :=
  map_toConeExponent _ φ

theorem toCharacterExponent_injective : Function.Injective L.toCharacterExponent :=
  map_injective Subtype.val_injective

theorem toCharacterExponent_le_toCharacterExponent_iff {x y : L.CharacterExponent} :
    L.toCharacterExponent x ≤ L.toCharacterExponent y ↔ x ≤ y :=
  map_le_map_iff fun _ ↦ L.coe_mem_posRootCone_iff

variable (S : Type*) [NonAssocSemiring S]

/-- Extension by zero from characters supported on the weight lattice to characters of the
realization: an injective ring homomorphism whose image is the characters supported on `P`. -/
noncomputable def toCharacterRing : L.CharacterRing S →+* R.CharacterRing S :=
  HahnSeries.embDomainRingHom L.toCharacterExponent L.toCharacterExponent_injective
    fun _ _ ↦ L.toCharacterExponent_le_toCharacterExponent_iff

/-- Extension by zero keeps the coefficients at the weights of `P`. -/
@[simp]
theorem coeff_toCharacterRing_coe (f : L.CharacterRing S) (φ : L.weightLattice) :
    (L.toCharacterRing S f).coeff (toConeExponent (φ : Dual ℚ H)) = f.coeff (toConeExponent φ) := by
  rw [← toCharacterExponent_toConeExponent]
  exact HahnSeries.embDomain_coeff

/-- Extension by zero vanishes at the weights outside `P`. -/
theorem coeff_toCharacterRing_of_notMem (f : L.CharacterRing S) {μ : Dual ℚ H}
    (hμ : μ ∉ L.weightLattice) : (L.toCharacterRing S f).coeff (toConeExponent μ) = 0 := by
  refine HahnSeries.embDomain_of_notMem_range ?_
  rintro ⟨x, hx⟩
  have hx' : (x.ofConeExponent : Dual ℚ H) = μ := by
    simpa using congrArg ofConeExponent hx
  exact hμ (hx' ▸ x.ofConeExponent.2)

/-- Extension by zero is injective. -/
theorem toCharacterRing_injective : Function.Injective (L.toCharacterRing S) :=
  HahnSeries.embDomain_injective

/-- A character of the realization is the extension by zero of a character supported on the
weight lattice exactly when its support lies in `P`. -/
theorem mem_range_toCharacterRing_iff (g : R.CharacterRing S) :
    g ∈ Set.range (L.toCharacterRing S) ↔
      ∀ μ : Dual ℚ H, g.coeff (toConeExponent μ) ≠ 0 → μ ∈ L.weightLattice := by
  refine HahnSeries.mem_range_embDomain_iff.trans ⟨fun h μ hμ ↦ ?_, fun h x hx ↦ ?_⟩
  · obtain ⟨y, hy⟩ := h hμ
    have hy' : (y.ofConeExponent : Dual ℚ H) = μ := by
      simpa using congrArg ofConeExponent hy
    exact hy' ▸ y.ofConeExponent.2
  · refine ⟨toConeExponent ⟨x.ofConeExponent, h _ hx⟩, ?_⟩
    exact (L.toCharacterExponent_toConeExponent _).trans (toConeExponent_ofConeExponent x)

/-- Extension by zero sends `e^φ` to `e^φ`. -/
@[simp]
theorem toCharacterRing_single (φ : L.weightLattice) (r : S) :
    L.toCharacterRing S (HahnSeries.single (toConeExponent φ) r) =
      HahnSeries.single (toConeExponent (φ : Dual ℚ H)) r := by
  rw [← toCharacterExponent_toConeExponent]
  exact HahnSeries.embDomain_single

end CoweightLattice

end CartanRealization

end TauCeti

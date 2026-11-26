/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Lifts
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import TauCeti.LinearAlgebra.Charpoly.Degree
public import TauCeti.NumberTheory.WeilNumber.Basic
public import TauCeti.NumberTheory.WeilNumber.IotaWeight
public import TauCeti.RepresentationTheory.Charpoly
public import TauCeti.RepresentationTheory.LinearCharacter.Basic

/-!
# Representations pure of a weight outside a set of places

Let `ρ` be a finite-dimensional representation of a group `G` over a field `E`. Suppose that for
each place `v` in an index type we are given an inertia subgroup `I v ≤ G`, an element `F v ∈ G`
playing the role of geometric Frobenius, and the size `q v` of the residue field. For a set `T`
of places and `w ∈ ℤ`:

* `ρ` is *unramified outside `T`* if each `I v`, `v ∉ T`, acts trivially;
* `ρ` is *pure of weight `w` outside `T`* if it is unramified outside `T` and, for every `v ∉ T`,
  every root of the characteristic polynomial `P_v = det (X - ρ (F v))` in an algebraic closure
  of `E` is a Weil `q v`-number of weight `w`: `1 < q v`, it is algebraic over `ℚ`, and all its
  complex conjugates have absolute value `q v ^ (w / 2)`. So a nonzero pure representation has
  residue sizes greater than `1` at all places outside `T`;
* for a field embedding `ι : E →+* ℂ` and a real number `r`, `ρ` is *`ι`-pure of weight `r`
  outside `T`* if it is unramified outside `T` and, for every `v ∉ T`, every complex root of
  `ι (P_v)` has absolute value `q v ^ (r / 2)`. This makes no algebraicity assertion;
* `ρ` has *integral characteristic polynomials outside `T`* if it is unramified outside `T` and
  each `P_v`, `v ∉ T`, is the image of a polynomial in `ℤ[X]`.

For a continuous `ℓ`-adic representation of the Galois group of a number field, with the inertia
groups and geometric Frobenius elements at a set of places, these are Deligne's notions of
purity of weight `w` and of `ι`-purity, and the integrality of Frobenius polynomials, all outside
`T`. Geometric Frobenius is the inverse of `x ↦ x ^ q`, so the Tate character, on which it acts by
`q⁻¹`, has weight `-2`. Here the data `I`, `F`, `q` are arbitrary: the predicates only express the
numerical conditions on them.

Purity of weight `w` implies `ι`-purity of weight `w` for every `ι`. Integral characteristic
polynomials, defined more generally for free modules of finite rank over a commutative ring, have
roots integral over `ℤ`; the converse would need the polynomials to be rational. Integrality is
independent of purity: the Tate character is pure of weight `-2`, but its characteristic
polynomial `X - q⁻¹` is not integral when `q > 1`. Every predicate survives enlarging `T`. The
weight of a nonzero representation is unique as soon as one place lies outside `T`, with residue
size greater than `1` for `ι`-purity. A representation of rank zero has characteristic polynomial
`1`, so it is pure of every weight; no unconditional uniqueness holds. The file closes with the
numerical Tate character over `ℂ`, pure of weight `-2` and not integral, and the sum of the trivial
and Tate lines, pure of no weight.

## Main definitions

* `Representation.IsUnramifiedOutside ρ I T`: each `I v` with `v ∉ T` acts trivially.
* `Representation.IsPureOutside ρ I F q T w`: `ρ` is pure of weight `w` outside `T`.
* `Representation.IsIotaPureOutside ι ρ I F q T r`: `ρ` is `ι`-pure of weight `r` outside `T`.
* `Representation.HasIntegralCharpolyOutside ρ I F T`: the characteristic polynomials of the
  `ρ (F v)`, `v ∉ T`, come from `ℤ[X]`.

## Main results

* `Representation.isPureOutside_iff_forall_mem_aroots`: purity may be tested on the roots in any
  algebraically closed field over `E`.
* `Representation.IsPureOutside.isIotaPureOutside`: purity of weight `w` implies `ι`-purity of
  weight `w` for every `ι : E →+* ℂ`.
* `Representation.isIotaPureOutside_iff_isIotaPure`: over an algebraically closed `E`, `ι`-purity
  is `ι`-purity of every eigenvalue in the sense of `TauCeti.IsIotaPure`.
* `Representation.HasIntegralCharpolyOutside.isIntegral_of_mem_aroots`: integral characteristic
  polynomials have roots integral over `ℤ`.
* `Representation.IsPureOutside.unique`, `Representation.IsIotaPureOutside.unique`: the weight of
  a nonzero representation is unique when one place lies outside `T`.
* `Representation.isPureOutside_ofLinearCharacter_iff` and its analogues: the predicates for the
  line on which `G` acts through a character `χ`.

## References

* P. Deligne, *La conjecture de Weil. II*, Publ. Math. IHÉS 52 (1980), §1.2, (1.2.2)–(1.2.6).
* B. Lawrence, A. Venkatesh, *Diophantine problems and p-adic period mappings*, Invent. Math.
  221 (2020), §2.3 and Lemma 2.3.
-/

public section

open Module Polynomial TauCeti

namespace Representation

/-! ### Unramified representations -/

section IsUnramifiedOutside

variable {k G V κ : Type*} [CommSemiring k] [Group G] [AddCommMonoid V] [Module k V]
  {ρ : Representation k G V} {I : κ → Subgroup G} {T T' : Set κ}

variable (ρ I T) in
/-- A representation is *unramified outside `T`* if, at every place `v ∉ T`, the inertia
subgroup `I v` acts trivially. -/
def IsUnramifiedOutside : Prop :=
  ∀ v ∉ T, ∀ g ∈ I v, ρ g = 1

theorem isUnramifiedOutside_iff : ρ.IsUnramifiedOutside I T ↔ ∀ v ∉ T, ∀ g ∈ I v, ρ g = 1 :=
  Iff.rfl

/-- Inertia at a place outside the exceptional set acts trivially on an unramified
representation. -/
theorem IsUnramifiedOutside.apply_eq_one (h : ρ.IsUnramifiedOutside I T) {v : κ} (hv : v ∉ T)
    {g : G} (hg : g ∈ I v) : ρ g = 1 :=
  h v hv g hg

/-- Unramifiedness survives enlarging the exceptional set. -/
theorem IsUnramifiedOutside.mono (h : ρ.IsUnramifiedOutside I T) (hT : T ⊆ T') :
    ρ.IsUnramifiedOutside I T' :=
  fun v hv ↦ h v fun hvT ↦ hv (hT hvT)

/-- A representation of rank zero is unramified everywhere. -/
theorem isUnramifiedOutside_of_subsingleton [Subsingleton V] : ρ.IsUnramifiedOutside I T :=
  fun _ _ _ _ ↦ Subsingleton.elim _ _

variable (V) in
/-- The trivial representation is unramified everywhere. -/
@[simp]
theorem isUnramifiedOutside_trivial : (trivial k G V).IsUnramifiedOutside I T :=
  fun _ _ _ _ ↦ rfl

/-- The line on which `G` acts through `χ` is unramified outside `T` exactly when `χ` is trivial
on every inertia subgroup outside `T`. -/
theorem isUnramifiedOutside_ofLinearCharacter_iff (χ : G →* kˣ) :
    (ofLinearCharacter χ).IsUnramifiedOutside I T ↔ ∀ v ∉ T, ∀ g ∈ I v, χ g = 1 := by
  simp [isUnramifiedOutside_iff]

end IsUnramifiedOutside

variable {E G V κ : Type*} [Field E] [Group G] [AddCommGroup V] [Module E V]
  [FiniteDimensional E V] {ρ : Representation E G V} {I : κ → Subgroup G} {F : κ → G}
  {q : κ → ℕ} {T T' : Set κ}

/-! ### Purity of an integer weight -/

section IsPureOutside

variable [Algebra ℚ E]

variable (ρ I F q T) in
/-- A representation is *pure of weight `w` outside `T`* if it is unramified outside `T` and, for
every place `v ∉ T`, every root of the characteristic polynomial of `ρ (F v)` in an algebraic
closure of `E` is a Weil `q v`-number of weight `w`. See
`Representation.isPureOutside_iff_forall_mem_aroots` for the independence of the algebraic
closure. -/
structure IsPureOutside (w : ℤ) : Prop where
  /-- A pure representation is unramified outside the exceptional set. -/
  isUnramifiedOutside : ρ.IsUnramifiedOutside I T
  /-- The characteristic roots of Frobenius outside the exceptional set are Weil numbers. -/
  isWeilNumber : ∀ v ∉ T, ∀ α ∈ (ρ (F v)).charpoly.aroots (AlgebraicClosure E),
    IsWeilNumber (q v : ℝ) w α

/-- Unbundled form of `Representation.IsPureOutside`. -/
theorem isPureOutside_iff {w : ℤ} : ρ.IsPureOutside I F q T w ↔ ρ.IsUnramifiedOutside I T ∧
    ∀ v ∉ T, ∀ α ∈ (ρ (F v)).charpoly.aroots (AlgebraicClosure E), IsWeilNumber (q v : ℝ) w α :=
  ⟨fun ⟨h₁, h₂⟩ ↦ ⟨h₁, h₂⟩, fun ⟨h₁, h₂⟩ ↦ ⟨h₁, h₂⟩⟩

/-- Purity may be tested on the characteristic roots in any algebraically closed field `Ω`
over `E`. Taking `Ω = E` gives the test on `charpoly.roots` when `E` is algebraically closed. -/
theorem isPureOutside_iff_forall_mem_aroots (Ω : Type*) [Field Ω] [IsAlgClosed Ω] [Algebra E Ω]
    [Algebra ℚ Ω] {w : ℤ} :
    ρ.IsPureOutside I F q T w ↔ ρ.IsUnramifiedOutside I T ∧
      ∀ v ∉ T, ∀ α ∈ (ρ (F v)).charpoly.aroots Ω, IsWeilNumber (q v : ℝ) w α := by
  let φ : AlgebraicClosure E →ₐ[E] Ω := IsAlgClosed.lift
  have hroots (p : E[X]) : p.aroots Ω = (p.aroots (AlgebraicClosure E)).map φ := by
    rw [aroots_def, aroots_def, ← φ.comp_algebraMap, ← map_map]
    exact (IsAlgClosed.splits _).roots_map_of_injective φ.injective
  refine ⟨fun h ↦ ⟨h.isUnramifiedOutside, fun v hv ↦ ?_⟩, fun h ↦ ⟨h.1, fun v hv ↦ ?_⟩⟩
  · rw [hroots, Multiset.forall_mem_map_iff]
    simpa only [isWeilNumber_map_iff] using h.isWeilNumber v hv
  · have := h.2 v hv
    rw [hroots, Multiset.forall_mem_map_iff] at this
    simpa only [isWeilNumber_map_iff] using this

namespace IsPureOutside

variable {w w' : ℤ}

/-- Every root, in any field `L` over `E`, of the characteristic polynomial of Frobenius at a
place outside `T` is a Weil number of the weight of a pure representation. -/
theorem isWeilNumber_of_mem_aroots (h : ρ.IsPureOutside I F q T w) {v : κ} (hv : v ∉ T)
    {L : Type*} [Field L] [Algebra E L] [Algebra ℚ L] {α : L}
    (hα : α ∈ (ρ (F v)).charpoly.aroots L) : IsWeilNumber (q v : ℝ) w α := by
  rw [← isWeilNumber_map_iff (algebraMap L (AlgebraicClosure L))]
  refine ((isPureOutside_iff_forall_mem_aroots (AlgebraicClosure L)).mp h).2 v hv _ ?_
  rw [mem_aroots'] at hα ⊢
  refine ⟨((ρ (F v)).charpoly_monic.map _).ne_zero, ?_⟩
  rw [aeval_algebraMap_apply, hα.2, map_zero]

/-- Purity survives enlarging the exceptional set. -/
theorem mono (h : ρ.IsPureOutside I F q T w) (hT : T ⊆ T') : ρ.IsPureOutside I F q T' w :=
  ⟨h.isUnramifiedOutside.mono hT, fun v hv ↦ h.isWeilNumber v fun hvT ↦ hv (hT hvT)⟩

/-- The weight of a pure representation of positive rank is unique, as soon as one place lies
outside the exceptional set. -/
theorem unique [Nontrivial V] (h : ρ.IsPureOutside I F q T w) (h' : ρ.IsPureOutside I F q T w')
    {v : κ} (hv : v ∉ T) : w = w' := by
  obtain ⟨α, hα⟩ :=
    LinearMap.exists_mem_roots_map_charpoly (algebraMap E (AlgebraicClosure E)) (ρ (F v))
  exact (h.isWeilNumber v hv α hα).unique (h'.isWeilNumber v hv α hα)

end IsPureOutside

/-- A representation of rank zero is pure of every weight: its characteristic polynomials are `1`
and have no roots. -/
theorem isPureOutside_of_subsingleton [Subsingleton V] {w : ℤ} : ρ.IsPureOutside I F q T w :=
  ⟨isUnramifiedOutside_of_subsingleton, fun v _ α hα ↦ by
    simp at hα⟩

variable (V) in
/-- The trivial representation is pure of weight `0` outside `T` when every residue field
outside `T` has more than one element. -/
theorem isPureOutside_trivial (hq : ∀ v ∉ T, 1 < q v) : (trivial E G V).IsPureOutside I F q T 0 :=
  ⟨isUnramifiedOutside_trivial V, fun v hv α hα ↦ by
    rw [eq_one_of_mem_roots_map_charpoly_trivial hα]
    exact isWeilNumber_one (by exact_mod_cast hq v hv)⟩

/-- The line on which `G` acts through a character `χ` is pure of weight `w` outside `T` exactly
when `χ` is trivial on inertia outside `T` and its values at the Frobenius elements outside `T` are
Weil numbers of weight `w`. -/
theorem isPureOutside_ofLinearCharacter_iff (χ : G →* Eˣ) {w : ℤ} :
    (ofLinearCharacter χ).IsPureOutside I F q T w ↔
      (∀ v ∉ T, ∀ g ∈ I v, χ g = 1) ∧ ∀ v ∉ T, IsWeilNumber (q v : ℝ) w (χ (F v) : E) := by
  rw [← isUnramifiedOutside_ofLinearCharacter_iff]
  refine ⟨fun h ↦ ⟨h.isUnramifiedOutside, fun v hv ↦ ?_⟩, fun h ↦ ⟨h.1, fun v hv α hα ↦ ?_⟩⟩
  · rw [← isWeilNumber_map_iff (algebraMap E (AlgebraicClosure E))]
    exact h.isWeilNumber v hv _ (by simp [charpoly_ofLinearCharacter_apply])
  · simp only [charpoly_ofLinearCharacter_apply, aroots_X_sub_C, Multiset.mem_singleton] at hα
    rw [hα, isWeilNumber_map_iff]
    exact h.2 v hv

end IsPureOutside

/-! ### `ι`-purity of a real weight -/

/-- For a field embedding `ι : E →+* ℂ`, a representation is *`ι`-pure of weight `r` outside `T`*
if it is unramified outside `T` and, for every place `v ∉ T`, every complex root of the image under
`ι` of the characteristic polynomial of `ρ (F v)` has absolute value `q v ^ (r / 2)`. Unlike
`Representation.IsPureOutside`, this makes no algebraicity assertion. -/
structure IsIotaPureOutside (ι : E →+* ℂ) (ρ : Representation E G V) (I : κ → Subgroup G)
    (F : κ → G) (q : κ → ℕ) (T : Set κ) (r : ℝ) : Prop where
  /-- An `ι`-pure representation is unramified outside the exceptional set. -/
  isUnramifiedOutside : ρ.IsUnramifiedOutside I T
  /-- The complex characteristic roots of Frobenius outside the exceptional set have absolute
  value `q v ^ (r / 2)`. -/
  norm_eq : ∀ v ∉ T, ∀ z ∈ ((ρ (F v)).charpoly.map ι).roots, ‖z‖ = (q v : ℝ) ^ (r / 2)

variable {ι : E →+* ℂ}

/-- Unbundled form of `Representation.IsIotaPureOutside`. -/
theorem isIotaPureOutside_iff {r : ℝ} : ρ.IsIotaPureOutside ι I F q T r ↔
    ρ.IsUnramifiedOutside I T ∧
      ∀ v ∉ T, ∀ z ∈ ((ρ (F v)).charpoly.map ι).roots, ‖z‖ = (q v : ℝ) ^ (r / 2) :=
  ⟨fun ⟨h₁, h₂⟩ ↦ ⟨h₁, h₂⟩, fun ⟨h₁, h₂⟩ ↦ ⟨h₁, h₂⟩⟩

/-- Over an algebraically closed field `E`, a representation is `ι`-pure of weight `r` outside `T`
exactly when it is unramified outside `T` and every eigenvalue of every `ρ (F v)`, `v ∉ T`, is
`ι`-pure of weight `r` relative to `q v`, provided these residue sizes exceed `1`. -/
theorem isIotaPureOutside_iff_isIotaPure [IsAlgClosed E] (hq : ∀ v ∉ T, 1 < q v) {r : ℝ} :
    ρ.IsIotaPureOutside ι I F q T r ↔ ρ.IsUnramifiedOutside I T ∧
      ∀ v ∉ T, ∀ α ∈ (ρ (F v)).charpoly.roots, IsIotaPure ι (q v : ℝ) r α := by
  rw [isIotaPureOutside_iff]
  refine and_congr Iff.rfl (forall₂_congr fun v hv ↦ ?_)
  have hq' : (1 : ℝ) < q v := by exact_mod_cast hq v hv
  rw [(IsAlgClosed.splits _).roots_map_of_injective ι.injective, Multiset.forall_mem_map_iff]
  exact forall₂_congr fun α _ ↦
    (isIotaPure_iff_norm_apply_eq (zero_lt_one.trans hq') hq'.ne').symm

namespace IsIotaPureOutside

variable {r r' : ℝ}

/-- `ι`-purity survives enlarging the exceptional set. -/
theorem mono (h : ρ.IsIotaPureOutside ι I F q T r) (hT : T ⊆ T') :
    ρ.IsIotaPureOutside ι I F q T' r :=
  ⟨h.isUnramifiedOutside.mono hT, fun v hv ↦ h.norm_eq v fun hvT ↦ hv (hT hvT)⟩

/-- The real weight of an `ι`-pure representation of positive rank is unique, as soon as one place
outside the exceptional set has residue size greater than `1`. -/
theorem unique [Nontrivial V] (h : ρ.IsIotaPureOutside ι I F q T r)
    (h' : ρ.IsIotaPureOutside ι I F q T r') {v : κ} (hv : v ∉ T) (hq : 1 < q v) : r = r' := by
  obtain ⟨z, hz⟩ := LinearMap.exists_mem_roots_map_charpoly ι (ρ (F v))
  have hq' : (1 : ℝ) < q v := by exact_mod_cast hq
  have := (h.norm_eq v hv z hz).symm.trans (h'.norm_eq v hv z hz)
  rwa [Real.rpow_right_inj (zero_lt_one.trans hq') hq'.ne', div_left_inj₀ two_ne_zero] at this

end IsIotaPureOutside

/-- A representation of rank zero is `ι`-pure of every real weight. -/
theorem isIotaPureOutside_of_subsingleton [Subsingleton V] {r : ℝ} :
    ρ.IsIotaPureOutside ι I F q T r :=
  ⟨isUnramifiedOutside_of_subsingleton, fun v _ z hz ↦ by
    simp at hz⟩

variable (V) in
/-- The trivial representation is `ι`-pure of weight `0`. -/
@[simp]
theorem isIotaPureOutside_trivial : (trivial E G V).IsIotaPureOutside ι I F q T 0 :=
  ⟨isUnramifiedOutside_trivial V, fun v _ z hz ↦ by
    simp [eq_one_of_mem_roots_map_charpoly_trivial hz]⟩

/-- The line on which `G` acts through a character `χ` is `ι`-pure of weight `r` outside `T`
exactly when `χ` is trivial on inertia outside `T` and its values at the Frobenius elements
outside `T` have absolute value `q v ^ (r / 2)` under `ι`. -/
theorem isIotaPureOutside_ofLinearCharacter_iff (χ : G →* Eˣ) {r : ℝ} :
    (ofLinearCharacter χ).IsIotaPureOutside ι I F q T r ↔
      (∀ v ∉ T, ∀ g ∈ I v, χ g = 1) ∧ ∀ v ∉ T, ‖ι (χ (F v))‖ = (q v : ℝ) ^ (r / 2) := by
  rw [isIotaPureOutside_iff, isUnramifiedOutside_ofLinearCharacter_iff]
  refine and_congr Iff.rfl (forall₂_congr fun v _ ↦ ?_)
  simp [charpoly_ofLinearCharacter_apply]

/-- Purity of weight `w` implies `ι`-purity of weight `w` for every field embedding
`ι : E →+* ℂ`. -/
theorem IsPureOutside.isIotaPureOutside [Algebra ℚ E] {w : ℤ} (h : ρ.IsPureOutside I F q T w)
    (ι : E →+* ℂ) : ρ.IsIotaPureOutside ι I F q T w := by
  let _ := ι.toAlgebra
  refine ⟨h.isUnramifiedOutside, fun v hv z hz ↦ ?_⟩
  have hz' : z ∈ (ρ (F v)).charpoly.aroots ℂ := by rwa [aroots_def, RingHom.algebraMap_toAlgebra]
  simpa using (h.isWeilNumber_of_mem_aroots hv hz').norm_apply_eq (RingHom.id ℂ)

/-! ### Integral characteristic polynomials -/

section HasIntegralCharpolyOutside

variable {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W] [Module.Free R W]
  [Module.Finite R W] {σ : Representation R G W}

variable (σ I F T) in
/-- A representation has *integral characteristic polynomials outside `T`* if it is unramified
outside `T` and, for every place `v ∉ T`, the characteristic polynomial of `σ (F v)` is the image
of a polynomial with integer coefficients. -/
structure HasIntegralCharpolyOutside : Prop where
  /-- A representation with integral characteristic polynomials is unramified outside the
  exceptional set. -/
  isUnramifiedOutside : σ.IsUnramifiedOutside I T
  /-- The characteristic polynomials of Frobenius outside the exceptional set come from
  `ℤ[X]`. -/
  charpoly_mem_lifts : ∀ v ∉ T, (σ (F v)).charpoly ∈ lifts (algebraMap ℤ R)

/-- Unbundled form of `Representation.HasIntegralCharpolyOutside`. -/
theorem hasIntegralCharpolyOutside_iff : σ.HasIntegralCharpolyOutside I F T ↔
    σ.IsUnramifiedOutside I T ∧ ∀ v ∉ T, (σ (F v)).charpoly ∈ lifts (algebraMap ℤ R) :=
  ⟨fun ⟨h₁, h₂⟩ ↦ ⟨h₁, h₂⟩, fun ⟨h₁, h₂⟩ ↦ ⟨h₁, h₂⟩⟩

namespace HasIntegralCharpolyOutside

/-- The characteristic polynomial of Frobenius at a place outside `T` is the image of a monic
polynomial with integer coefficients. -/
theorem exists_monic_map_eq (h : σ.HasIntegralCharpolyOutside I F T) {v : κ} (hv : v ∉ T) :
    ∃ P : ℤ[X], P.Monic ∧ P.map (algebraMap ℤ R) = (σ (F v)).charpoly := by
  obtain ⟨P, hP, -, hmonic⟩ :=
    lifts_and_natDegree_eq_and_monic (h.charpoly_mem_lifts v hv) (σ (F v)).charpoly_monic
  exact ⟨P, hmonic, hP⟩

/-- Every root, in any domain `L` over `R`, of an integral characteristic polynomial of Frobenius
is integral over `ℤ`. -/
theorem isIntegral_of_mem_aroots (h : σ.HasIntegralCharpolyOutside I F T) {v : κ} (hv : v ∉ T)
    {L : Type*} [CommRing L] [IsDomain L] [Algebra R L] {α : L}
    (hα : α ∈ (σ (F v)).charpoly.aroots L) : IsIntegral ℤ α := by
  obtain ⟨P, hmonic, hP⟩ := h.exists_monic_map_eq hv
  refine ⟨P, hmonic, ?_⟩
  have := (mem_aroots'.mp hα).2
  rwa [← hP, aeval_map_algebraMap, aeval_def] at this

/-- Integrality of the characteristic polynomials survives enlarging the exceptional set. -/
theorem mono (h : σ.HasIntegralCharpolyOutside I F T) (hT : T ⊆ T') :
    σ.HasIntegralCharpolyOutside I F T' :=
  ⟨h.isUnramifiedOutside.mono hT, fun v hv ↦ h.charpoly_mem_lifts v fun hvT ↦ hv (hT hvT)⟩

end HasIntegralCharpolyOutside

/-- A representation of rank zero has integral characteristic polynomials: they are `1`. -/
theorem hasIntegralCharpolyOutside_of_subsingleton [Subsingleton W] :
    σ.HasIntegralCharpolyOutside I F T :=
  ⟨isUnramifiedOutside_of_subsingleton, fun v _ ↦ by
    rw [LinearMap.charpoly_eq_one_of_subsingleton]
    exact one_mem _⟩

variable (W) in
/-- The trivial representation has integral characteristic polynomials `(X - 1) ^ dim W`. -/
@[simp]
theorem hasIntegralCharpolyOutside_trivial : (trivial R G W).HasIntegralCharpolyOutside I F T :=
  ⟨isUnramifiedOutside_trivial W, fun v _ ↦ by
    rw [charpoly_trivial_apply]
    exact ⟨(X - 1) ^ finrank R W, by simp⟩⟩

/-- The line on which `G` acts through a character `χ` has integral characteristic polynomials
outside `T` exactly when `χ` is trivial on inertia outside `T` and its values at the Frobenius
elements outside `T` are integers. -/
theorem hasIntegralCharpolyOutside_ofLinearCharacter_iff (χ : G →* Rˣ) :
    (ofLinearCharacter χ).HasIntegralCharpolyOutside I F T ↔
      (∀ v ∉ T, ∀ g ∈ I v, χ g = 1) ∧ ∀ v ∉ T, ∃ n : ℤ, (χ (F v) : R) = n := by
  rw [← isUnramifiedOutside_ofLinearCharacter_iff]
  refine ⟨fun h ↦ ⟨h.isUnramifiedOutside, fun v hv ↦ ?_⟩, fun h ↦ ⟨h.1, fun v hv ↦ ?_⟩⟩
  · obtain ⟨n, hn⟩ := (lifts_iff_coeff_lifts _).mp (h.charpoly_mem_lifts v hv) 0
    have hn' : (n : R) = -(χ (F v) : R) := by simpa [charpoly_ofLinearCharacter_apply] using hn
    exact ⟨-n, by simp [hn']⟩
  · obtain ⟨n, hn⟩ := h.2 v hv
    exact ⟨X - C n, by simp [charpoly_ofLinearCharacter_apply, hn]⟩

end HasIntegralCharpolyOutside

/-! ### Examples

Over `ℂ`, with places the primes `p`, trivial inertia, residue sizes `p`, and Frobenius at `p`
acting by `p⁻¹`, the line on which `ℂˣ` acts by multiplication is a numerical model of the Tate
character `ℚ_ℓ(1)`. -/

/-- The Frobenius elements of the numerical Tate character: `p⁻¹ ∈ ℂˣ` at the prime `p`. -/
private noncomputable abbrev tateFrob (p : Nat.Primes) : ℂˣ :=
  (Units.mk0 (p : ℂ) (Nat.cast_ne_zero.mpr p.prop.ne_zero))⁻¹

/-- At the prime `p`, the numerical Tate character has Frobenius eigenvalue `p⁻¹`, a Weil
`p`-number of weight `-2`. -/
private theorem isWeilNumber_tateFrob (p : Nat.Primes) :
    IsWeilNumber ((p : ℕ) : ℝ) (-2) ((tateFrob p : ℂˣ) : ℂ) := by
  simpa using (isWeilNumber_map_iff (K := ℚ) (L := ℂ) (Rat.castHom ℂ)).mpr
    (isWeilNumber_inv_natCast p.prop.two_le)

/-- The numerical Tate character is pure of weight `-2`. -/
private theorem isPureOutside_tate : (ofLinearCharacter (MonoidHom.id ℂˣ)).IsPureOutside
    (fun _ ↦ ⊥) tateFrob (fun p ↦ (p : ℕ)) ∅ (-2) :=
  (isPureOutside_ofLinearCharacter_iff _).mpr ⟨by simp, fun p _ ↦ isWeilNumber_tateFrob p⟩

/- The numerical Tate character is `ι`-pure of weight `-2` under every `ι`. -/
example (ι : ℂ →+* ℂ) : (ofLinearCharacter (MonoidHom.id ℂˣ)).IsIotaPureOutside ι (fun _ ↦ ⊥)
    tateFrob (fun p ↦ (p : ℕ)) ∅ (-2) := by
  exact_mod_cast isPureOutside_tate.isIotaPureOutside ι

/- The numerical Tate character does not have integral characteristic polynomials: `X - 2⁻¹` is
not in `ℤ[X]`. -/
example : ¬(ofLinearCharacter (MonoidHom.id ℂˣ)).HasIntegralCharpolyOutside (fun _ ↦ ⊥)
    tateFrob ∅ := by
  intro h
  obtain ⟨n, hn⟩ := ((hasIntegralCharpolyOutside_ofLinearCharacter_iff _).mp h).2
    ⟨2, Nat.prime_two⟩ (Set.notMem_empty _)
  have h2 : ((2⁻¹ : ℚ) : ℂ) = ((n : ℚ) : ℂ) := by simpa using hn
  have h3 : (2 : ℚ) * n = 1 := by
    rw [← Rat.cast_injective h2]
    norm_num
  have h4 : (2 * n : ℤ) = 1 := by exact_mod_cast h3
  omega

/- The sum of the trivial line and the numerical Tate character is pure of no weight: at `p = 2`
it has eigenvalues `1` and `2⁻¹`, of weights `0` and `-2`. -/
example (w : ℤ) : ¬((trivial ℂ ℂˣ ℂ).prod (ofLinearCharacter (MonoidHom.id ℂˣ))).IsPureOutside
    (fun _ ↦ ⊥) tateFrob (fun p ↦ (p : ℕ)) ∅ w := by
  intro h
  let p : Nat.Primes := ⟨2, Nat.prime_two⟩
  have hmem (z : ℂ) (hz : z = 1 ∨ z = ((tateFrob p : ℂˣ) : ℂ)) :
      z ∈ (((trivial ℂ ℂˣ ℂ).prod (ofLinearCharacter (MonoidHom.id ℂˣ))) (tateFrob p)
        ).charpoly.aroots ℂ := by
    refine mem_aroots.mpr ⟨(LinearMap.charpoly_monic _).ne_zero, ?_⟩
    simp only [charpoly_prod_apply, charpoly_trivial_apply, charpoly_ofLinearCharacter_apply]
    rcases hz with rfl | rfl <;> simp
  have h1 := (h.isWeilNumber_of_mem_aroots (Set.notMem_empty p) (hmem 1 (.inl rfl))).unique
    (isWeilNumber_one (K := ℂ) (by norm_num))
  have h2 := (h.isWeilNumber_of_mem_aroots (Set.notMem_empty p) (hmem _ (.inr rfl))).unique
    (isWeilNumber_tateFrob p)
  omega

/- A representation of rank zero is pure of every weight. -/
example (w : ℤ) : (trivial ℂ ℂˣ (Fin 0 → ℂ)).IsPureOutside (fun _ ↦ ⊥) tateFrob
    (fun p ↦ (p : ℕ)) ∅ w :=
  isPureOutside_of_subsingleton

/- The scalar `3` acting on `ℂ` is not `ι`-pure of weight `0` for the identity embedding, at a
place with residue size `3`. -/
example : ¬(ofLinearCharacter (MonoidHom.id ℂˣ)).IsIotaPureOutside (RingHom.id ℂ)
    (fun _ : Unit ↦ ⊥) (fun _ ↦ Units.mk0 3 three_ne_zero) (fun _ ↦ 3) ∅ 0 := by
  rw [isIotaPureOutside_ofLinearCharacter_iff]
  rintro ⟨-, h⟩
  have := h () (Set.notMem_empty _)
  norm_num at this

end Representation

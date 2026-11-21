/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Coxeter.Element.Eigen
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Classification
public import TauCeti.LinearAlgebra.RootSystem.Positive
-- `TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Coefficient` supplies the description
-- of the root columns of the pinned simply connected datum as the `columnReflectionGroup` orbits
-- of the coordinate columns, used only inside `HasCartanType.nonempty_equiv_fin_numRoots`.
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Coefficient

/-!
# Root counts, Coxeter numbers, and classification-free Coxeter invariants

For a finite reduced crystallographic root pairing `P` carrying a base `b` of valid Cartan type `t`,
the simple-root coefficient columns of the roots of `P` are the `columnReflectionGroup` orbits of
the coordinate columns (`RootPairing.Base.iUnion_orbit_single_eq_range_rootCoefficients`). Matching
those orbits along the Cartan-matrix relabelling to the orbits of the pinned simply connected root
datum of `t` (`TauCeti.DynkinType.iUnion_orbit_single_eq_range_simpleRootCoefficients`) identifies
the root count of `P` with `t.numRoots` without assuming that the roots of `P` span the ambient
module.

Combined with `TauCeti.DynkinType.numRoots_eq_rank_mul_coxeterNumber` (`t.numRoots = r * h`),
`TauCeti.Coxeter.orderOf_wordProd_of_hasCartanType` (`orderOf c = h`), and the Cartan-Killing
classification (`TauCeti.classifiedDynkinType`), this yields the classical root-count and
eigenvalue theorems both for bases of a prescribed valid Cartan type and unconditionally for any
finite irreducible reduced crystallographic root system:

* `|Φ| = r * h` and `h = |Φ| / r`, where `r = b.support.card` is the rank and
  `h = orderOf (wordProd P b l)` is the order of any Coxeter element;
* `2 * |Φ⁺| = r * h` and `|Φ⁺| = ∑ mᵢ`;
* all Coxeter elements across all bases and all orderings of the simple reflections have the same
  order `h ≥ 2`;
* every primitive `h`-th root of unity `exp (2πi e / h)` (`e < h`, `gcd(e, h) = 1`) — in particular
  `exp (2πi / h)` — is a complex eigenvalue of the matrix of every Coxeter element on the simple
  roots.

## Main results

* `TauCeti.HasCartanType.nonempty_equiv_fin_numRoots` and
  `TauCeti.HasCartanType.natCard_eq_numRoots`: a finite reduced crystallographic root pairing with a
  base of valid Cartan type `t` has `t.numRoots` roots (no spanning hypothesis needed).
* `TauCeti.HasCartanType.ncard_posRoots_eq_sum_exponents`,
  `TauCeti.HasCartanType.natCard_eq_card_support_mul_coxeterNumber`, and
  `TauCeti.HasCartanType.coxeterNumber_eq_natCard_div_card_support`: positive-root count `∑ mᵢ` and
  the identity `h = |Φ| / r` for any base of valid Cartan type `t`.
* `TauCeti.Coxeter.natCard_eq_card_support_mul_orderOf_wordProd` and
  `TauCeti.Coxeter.orderOf_wordProd_eq_natCard_div_card_support`: **`|Φ| = r * h` and
  `h = |Φ| / r`** for every finite irreducible reduced crystallographic root system.
* `TauCeti.Coxeter.orderOf_wordProd_eq_orderOf_wordProd`: any two Coxeter elements, relative to any
  two bases, have the same order.
* `TauCeti.Coxeter.roots_charpoly_of_actsBy` and
  `TauCeti.Coxeter.mem_roots_charpoly_of_actsBy_of_coprime`: the complex eigenvalue multiset of any
  Coxeter element on the simple roots, and containment of all primitive `h`-th roots of unity.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. V, §6, no. 2, and Ch. VI, §1.11.
* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, Cambridge University Press (1990),
  §§ 3.16--3.18.
-/

public section

open Function Matrix Set

namespace TauCeti

section HasCartanType

variable {ι R M N : Type*} [CommRing R] [CharZero R] [IsDomain R] [Finite ι]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [P.IsCrystallographic] [P.IsReduced]

/-- Relabelling simple-root coefficient columns along a Cartan-matrix equivalence matches the
`columnReflectionGroup` orbits of the coordinate columns to those of `t.cartanMatrix`. -/
private lemma image_comp_symm_range_rootCoefficients {b : P.Base} {t : DynkinType} (ht : t.Valid)
    (e : b.support ≃ Fin t.rank) (he : ∀ i j, b.cartanMatrix i j = t.cartanMatrix (e i) (e j)) :
    Set.range (fun x : ι ↦ b.rootCoefficients x ∘ e.symm) =
      Set.range (t.simpleRootCoefficients ht) := by
  classical
  have hrange : Set.range (fun x : ι ↦ b.rootCoefficients x ∘ e.symm) =
      (fun c : b.support → ℤ ↦ c ∘ e.symm) '' Set.range b.rootCoefficients :=
    Set.range_comp (fun c : b.support → ℤ ↦ c ∘ e.symm) b.rootCoefficients
  rw [hrange, ← b.iUnion_orbit_single_eq_range_rootCoefficients,
    ← t.iUnion_orbit_single_eq_range_simpleRootCoefficients ht]
  ext d
  simp only [mem_image, mem_iUnion]
  constructor
  · rintro ⟨c, ⟨k, hk⟩, rfl⟩
    refine ⟨e k, ?_⟩
    have horb := Matrix.comp_equiv_mem_orbit b.cartanMatrix b.cartanMatrix_apply_same
      t.cartanMatrix_apply_same e.symm
      (fun i j ↦ by simp [he (e.symm i) (e.symm j)]) hk
    have hs : (Pi.single k 1 : b.support → ℤ) ∘ e.symm = Pi.single (e k) 1 := by
      ext i; simp [Pi.single_apply, Equiv.symm_apply_eq]
    rwa [hs] at horb
  · rintro ⟨i, hi⟩
    refine ⟨d ∘ e, ⟨e.symm i, ?_⟩, by ext j; simp⟩
    have horb := Matrix.comp_equiv_mem_orbit t.cartanMatrix t.cartanMatrix_apply_same
      b.cartanMatrix_apply_same e he hi
    have hs : (Pi.single i 1 : Fin t.rank → ℤ) ∘ e = Pi.single (e.symm i) 1 := by
      ext k; simp [Pi.single_apply, Equiv.eq_symm_apply]
    rwa [hs] at horb

/-- **A finite reduced crystallographic root pairing carrying a base of valid Cartan type `t` has
root index type equivalent to `Fin t.numRoots`.** No spanning assumption on the roots is
required. -/
theorem HasCartanType.nonempty_equiv_fin_numRoots {b : P.Base} {t : DynkinType}
    (h : HasCartanType P b t) (ht : t.Valid) :
    Nonempty (ι ≃ Fin t.numRoots) := by
  obtain ⟨e, he⟩ := (hasCartanType_iff b t).mp h
  let f : ι → (Fin t.rank → ℤ) := fun x ↦ b.rootCoefficients x ∘ e.symm
  have hf : Injective f := fun x y hxy ↦ b.rootCoefficients_injective <| by
    ext k
    simpa [f] using congrFun hxy (e k)
  have hg : Injective (t.simpleRootCoefficients ht) := t.simpleRootCoefficients_injective ht
  have hrange := image_comp_symm_range_rootCoefficients ht e he
  have heq : Set.range f ≃ Set.range (t.simpleRootCoefficients ht) :=
    hrange ▸ Equiv.refl (Set.range f)
  exact ⟨(Equiv.ofInjective f hf).trans (heq.trans (Equiv.ofInjective _ hg).symm)⟩

/-- **A finite reduced crystallographic root pairing with a base of valid Cartan type `t` has
`t.numRoots` roots.** -/
theorem HasCartanType.natCard_eq_numRoots {b : P.Base} {t : DynkinType}
    (h : HasCartanType P b t) (ht : t.Valid) :
    Nat.card ι = t.numRoots := by
  obtain ⟨e⟩ := h.nonempty_equiv_fin_numRoots ht
  simpa using Nat.card_congr e

/-- Twice the number of positive roots of a base of valid Cartan type `t` is `t.numRoots`. -/
theorem HasCartanType.two_mul_ncard_posRoots_eq_numRoots {b : P.Base} {t : DynkinType}
    (h : HasCartanType P b t) (ht : t.Valid) :
    2 * (posRoots P b).ncard = t.numRoots :=
  (two_mul_ncard_posRoots P b).trans (h.natCard_eq_numRoots ht)

/-- **The number of positive roots of a base of valid Cartan type `t` equals the sum of the
exponents of `t`.** -/
theorem HasCartanType.ncard_posRoots_eq_sum_exponents {b : P.Base} {t : DynkinType}
    (h : HasCartanType P b t) (ht : t.Valid) :
    (posRoots P b).ncard = t.exponents.sum := by
  have h2 := h.two_mul_ncard_posRoots_eq_numRoots ht
  have hexp := t.two_mul_sum_exponents
  omega

/-- Finset version of `TauCeti.HasCartanType.ncard_posRoots_eq_sum_exponents`. -/
theorem HasCartanType.card_posRootsFinset_eq_sum_exponents {b : P.Base} {t : DynkinType}
    (h : HasCartanType P b t) (ht : t.Valid) :
    (posRootsFinset P b).card = t.exponents.sum :=
  (card_posRootsFinset P b).trans (h.ncard_posRoots_eq_sum_exponents ht)

/-- **The sum of the fundamental degrees of `t` equals `|Φ⁺| + r`** for any base `b` of valid
Cartan type `t`. -/
theorem HasCartanType.sum_degrees_eq_ncard_posRoots_add_card_support {b : P.Base}
    {t : DynkinType} (h : HasCartanType P b t) (ht : t.Valid) :
    t.degrees.sum = (posRoots P b).ncard + b.support.card := by
  rw [t.sum_degrees, ← t.sum_exponents, ← h.ncard_posRoots_eq_sum_exponents ht, h.card_support]

/-- **For a base `b` of valid Cartan type `t`, `|Φ| = r * h`**, where `r = b.support.card` is the
rank and `h = t.coxeterNumber` is the Coxeter number. -/
theorem HasCartanType.natCard_eq_card_support_mul_coxeterNumber {b : P.Base} {t : DynkinType}
    (h : HasCartanType P b t) (ht : t.Valid) :
    Nat.card ι = b.support.card * t.coxeterNumber := by
  rw [h.natCard_eq_numRoots ht, h.card_support, t.numRoots_eq_rank_mul_coxeterNumber]

/-- **For a base `b` of valid Cartan type `t`, `h = |Φ| / r`**, where `r = b.support.card`. -/
theorem HasCartanType.coxeterNumber_eq_natCard_div_card_support {b : P.Base} {t : DynkinType}
    (h : HasCartanType P b t) (ht : t.Valid) :
    t.coxeterNumber = Nat.card ι / b.support.card := by
  have hpos : 0 < b.support.card := h.card_support ▸ DynkinType.rank_pos ht
  rw [h.natCard_eq_card_support_mul_coxeterNumber ht, Nat.mul_div_right _ hpos]

end HasCartanType

/-! ### Invariants of classified finite irreducible root systems -/

section Classified

variable {ι R M N : Type*} [CommRing R] [CharZero R] [IsDomain R] [Finite ι]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [P.IsRootSystem] [P.IsCrystallographic] [P.IsReduced] [P.IsIrreducible]

/-- The number of roots of a finite irreducible reduced crystallographic root system is the
`numRoots` of its classified Dynkin type. -/
theorem natCard_eq_numRoots_classifiedDynkinType (b : P.Base) :
    Nat.card ι = (classifiedDynkinType b).numRoots :=
  (hasCartanType_classifiedDynkinType b).natCard_eq_numRoots (valid_classifiedDynkinType b)

/-- The number of positive roots of any base equals the sum of the exponents of its classified
Dynkin type. -/
theorem ncard_posRoots_eq_sum_exponents_classifiedDynkinType (b : P.Base) :
    (posRoots P b).ncard = (classifiedDynkinType b).exponents.sum :=
  (hasCartanType_classifiedDynkinType b).ncard_posRoots_eq_sum_exponents
    (valid_classifiedDynkinType b)

/-- Finset version of `TauCeti.ncard_posRoots_eq_sum_exponents_classifiedDynkinType`. -/
theorem card_posRootsFinset_eq_sum_exponents_classifiedDynkinType (b : P.Base) :
    (posRootsFinset P b).card = (classifiedDynkinType b).exponents.sum :=
  (hasCartanType_classifiedDynkinType b).card_posRootsFinset_eq_sum_exponents
    (valid_classifiedDynkinType b)

/-- The sum of the fundamental degrees of the classified Dynkin type equals `|Φ⁺| + r`. -/
theorem sum_degrees_classifiedDynkinType (b : P.Base) :
    (classifiedDynkinType b).degrees.sum = (posRoots P b).ncard + b.support.card :=
  (hasCartanType_classifiedDynkinType b).sum_degrees_eq_ncard_posRoots_add_card_support
    (valid_classifiedDynkinType b)

/-- The Coxeter number of the classified Dynkin type is `|Φ| / r`. -/
theorem coxeterNumber_classifiedDynkinType_eq_natCard_div_card_support (b : P.Base) :
    (classifiedDynkinType b).coxeterNumber = Nat.card ι / b.support.card :=
  (hasCartanType_classifiedDynkinType b).coxeterNumber_eq_natCard_div_card_support
    (valid_classifiedDynkinType b)

end Classified

namespace Coxeter

/-! ### Coxeter order and root counts for bases of valid Cartan type -/

section HasCartanType

variable {ι R M N : Type*} [CommRing R] [CharZero R] [IsDomain R] [Finite ι]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [P.IsCrystallographic] [P.IsReduced]

/-- **For any base `b` of valid Cartan type `t` and any Coxeter element `c`, `|Φ| = r * orderOf c`**
(no spanning assumption on the roots needed). -/
theorem natCard_eq_card_support_mul_orderOf_wordProd_of_hasCartanType {b : P.Base}
    {t : DynkinType} (ht : t.Valid) (h : HasCartanType P b t) {l : List b.support}
    (hnd : l.Nodup) (hall : ∀ i, i ∈ l) :
    Nat.card ι = b.support.card * orderOf (wordProd P b l) := by
  rw [orderOf_wordProd_of_hasCartanType ht h hnd hall]
  exact h.natCard_eq_card_support_mul_coxeterNumber ht

/-- **For any base `b` of valid Cartan type `t` and any Coxeter element `c`,
`orderOf c = |Φ| / r`.** -/
theorem orderOf_wordProd_eq_natCard_div_card_support_of_hasCartanType {b : P.Base}
    {t : DynkinType} (ht : t.Valid) (h : HasCartanType P b t) {l : List b.support}
    (hnd : l.Nodup) (hall : ∀ i, i ∈ l) :
    orderOf (wordProd P b l) = Nat.card ι / b.support.card := by
  rw [orderOf_wordProd_of_hasCartanType ht h hnd hall]
  exact h.coxeterNumber_eq_natCard_div_card_support ht

/-- Twice the number of positive roots of a base `b` of valid Cartan type `t` is
`b.support.card * orderOf (wordProd P b l)`. -/
theorem two_mul_ncard_posRoots_eq_card_support_mul_orderOf_wordProd_of_hasCartanType {b : P.Base}
    {t : DynkinType} (ht : t.Valid) (h : HasCartanType P b t) {l : List b.support}
    (hnd : l.Nodup) (hall : ∀ i, i ∈ l) :
    2 * (posRoots P b).ncard = b.support.card * orderOf (wordProd P b l) :=
  (two_mul_ncard_posRoots P b).trans
    (natCard_eq_card_support_mul_orderOf_wordProd_of_hasCartanType ht h hnd hall)

end HasCartanType

/-! ### Classification-free Coxeter theorems for irreducible root systems -/

section Irreducible

variable {ι R M N : Type*} [CommRing R] [CharZero R] [IsDomain R] [Finite ι]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [P.IsRootSystem] [P.IsCrystallographic] [P.IsReduced] [P.IsIrreducible]

/-- **Every Coxeter element of a base `b` of a finite irreducible reduced crystallographic root
system has order `(classifiedDynkinType b).coxeterNumber`.** -/
theorem orderOf_wordProd_eq_coxeterNumber_classifiedDynkinType {b : P.Base} {l : List b.support}
    (hnd : l.Nodup) (hall : ∀ i, i ∈ l) :
    orderOf (wordProd P b l) = (classifiedDynkinType b).coxeterNumber :=
  orderOf_wordProd_of_hasCartanType (valid_classifiedDynkinType b)
    (hasCartanType_classifiedDynkinType b) hnd hall

/-- **Every Coxeter element of a finite irreducible reduced crystallographic root system has order
at least `2`.** -/
theorem two_le_orderOf_wordProd {b : P.Base} {l : List b.support} (hnd : l.Nodup)
    (hall : ∀ i, i ∈ l) :
    2 ≤ orderOf (wordProd P b l) := by
  rw [orderOf_wordProd_eq_coxeterNumber_classifiedDynkinType hnd hall]
  exact (classifiedDynkinType b).two_le_coxeterNumber (valid_classifiedDynkinType b)

/-- **Any two Coxeter elements of a finite irreducible reduced crystallographic root system, across
any two bases and any two orderings of their simple reflections, have the same order.** -/
theorem orderOf_wordProd_eq_orderOf_wordProd {b b' : P.Base} {l : List b.support}
    {l' : List b'.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l) (hnd' : l'.Nodup)
    (hall' : ∀ i, i ∈ l') :
    orderOf (wordProd P b l) = orderOf (wordProd P b' l') := by
  rw [orderOf_wordProd_eq_coxeterNumber_classifiedDynkinType hnd hall,
    orderOf_wordProd_eq_coxeterNumber_classifiedDynkinType hnd' hall',
    b.classifiedDynkinType_eq_classifiedDynkinType b']

/-- **`|Φ| = r * h`**: in any finite irreducible reduced crystallographic root system, the number of
roots equals the rank `b.support.card` times the order of any Coxeter element. -/
theorem natCard_eq_card_support_mul_orderOf_wordProd {b : P.Base} {l : List b.support}
    (hnd : l.Nodup) (hall : ∀ i, i ∈ l) :
    Nat.card ι = b.support.card * orderOf (wordProd P b l) :=
  natCard_eq_card_support_mul_orderOf_wordProd_of_hasCartanType (valid_classifiedDynkinType b)
    (hasCartanType_classifiedDynkinType b) hnd hall

/-- **`h = |Φ| / r`**: in any finite irreducible reduced crystallographic root system, every Coxeter
element has order equal to the number of roots divided by the rank. -/
theorem orderOf_wordProd_eq_natCard_div_card_support {b : P.Base} {l : List b.support}
    (hnd : l.Nodup) (hall : ∀ i, i ∈ l) :
    orderOf (wordProd P b l) = Nat.card ι / b.support.card :=
  orderOf_wordProd_eq_natCard_div_card_support_of_hasCartanType (valid_classifiedDynkinType b)
    (hasCartanType_classifiedDynkinType b) hnd hall

/-- **`2 |Φ⁺| = r * h`**: twice the number of positive roots equals the rank times the order of any
Coxeter element. -/
theorem two_mul_ncard_posRoots_eq_card_support_mul_orderOf_wordProd {b : P.Base}
    {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l) :
    2 * (posRoots P b).ncard = b.support.card * orderOf (wordProd P b l) :=
  two_mul_ncard_posRoots_eq_card_support_mul_orderOf_wordProd_of_hasCartanType
    (valid_classifiedDynkinType b) (hasCartanType_classifiedDynkinType b) hnd hall

/-- Finset version of
`TauCeti.Coxeter.two_mul_ncard_posRoots_eq_card_support_mul_orderOf_wordProd`. -/
theorem two_mul_card_posRootsFinset_eq_card_support_mul_orderOf_wordProd {b : P.Base}
    {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l) :
    2 * (posRootsFinset P b).card = b.support.card * orderOf (wordProd P b l) := by
  rw [card_posRootsFinset,
    two_mul_ncard_posRoots_eq_card_support_mul_orderOf_wordProd hnd hall]

/-- **Complex eigenvalue multiset of any Coxeter element on the simple roots** of a finite
irreducible reduced crystallographic root system: `exp (2πi e / h)` as `e` runs over the exponents
of `classifiedDynkinType b`, where `h = orderOf (wordProd P b l)`. -/
theorem roots_charpoly_of_actsBy [DecidableEq ι] {b : P.Base} {l : List b.support}
    (hnd : l.Nodup) (hall : ∀ i, i ∈ l) {W : Matrix b.support b.support ℤ}
    (hW : b.ActsBy (wordProd P b l) W) :
    (W.map (Int.castRingHom ℂ)).charpoly.roots =
      (Multiset.ofList (classifiedDynkinType b).exponents).map fun e : ℕ =>
        Complex.exp (2 * Real.pi * Complex.I * (e / orderOf (wordProd P b l))) := by
  rw [orderOf_wordProd_eq_coxeterNumber_classifiedDynkinType hnd hall]
  exact roots_charpoly_of_hasCartanType_of_actsBy (valid_classifiedDynkinType b)
    (hasCartanType_classifiedDynkinType b) hnd hall hW

/-- **Every primitive `h`-th root of unity is an eigenvalue of every Coxeter element** of a finite
irreducible reduced crystallographic root system on the simple roots, where
`h = orderOf (wordProd P b l)`. -/
theorem mem_roots_charpoly_of_actsBy_of_coprime [DecidableEq ι] {b : P.Base} {l : List b.support}
    (hnd : l.Nodup) (hall : ∀ i, i ∈ l) {W : Matrix b.support b.support ℤ}
    (hW : b.ActsBy (wordProd P b l) W) {e : ℕ} (he : e < orderOf (wordProd P b l))
    (hcop : e.Coprime (orderOf (wordProd P b l))) :
    Complex.exp (2 * Real.pi * Complex.I * (e / orderOf (wordProd P b l))) ∈
      (W.map (Int.castRingHom ℂ)).charpoly.roots := by
  have hord := orderOf_wordProd_eq_coxeterNumber_classifiedDynkinType hnd hall
  rw [hord] at he hcop ⊢
  exact mem_roots_charpoly_of_hasCartanType_of_actsBy_of_coprime (valid_classifiedDynkinType b)
    (hasCartanType_classifiedDynkinType b) hnd hall hW he hcop

/-- **The primitive root `exp (2πi / h)` (`e = 1`) is an eigenvalue of every Coxeter element** of a
finite irreducible reduced crystallographic root system on the simple roots. -/
theorem exp_two_pi_I_div_orderOf_mem_roots_charpoly_of_actsBy [DecidableEq ι] {b : P.Base}
    {l : List b.support} (hnd : l.Nodup) (hall : ∀ i, i ∈ l) {W : Matrix b.support b.support ℤ}
    (hW : b.ActsBy (wordProd P b l) W) :
    Complex.exp (2 * Real.pi * Complex.I / orderOf (wordProd P b l)) ∈
      (W.map (Int.castRingHom ℂ)).charpoly.roots := by
  have hmem := mem_roots_charpoly_of_actsBy_of_coprime hnd hall hW (e := 1)
    (two_le_orderOf_wordProd hnd hall) (Nat.coprime_one_left _)
  rw [Nat.cast_one, mul_one_div] at hmem
  exact hmem

end Irreducible

end Coxeter

end TauCeti

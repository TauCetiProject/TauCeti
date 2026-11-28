/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.WittVector.Complete
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.FreeModule.PID
import TauCeti.NumberTheory.Padics.FreeModuleReduction
import TauCeti.NumberTheory.Padics.PadicIntegers
import TauCeti.RingTheory.AdicCompletion.Finite
import TauCeti.RingTheory.WittVector.Teichmuller.Coeff
import TauCeti.RingTheory.WittVector.Units

/-!
# Witt vectors of a finite field

Let `k` be a finite perfect ring of characteristic `p`, for instance a finite field `𝔽_q`. Then
`𝕎 k` is a free `ℤ_p`-module of finite rank, and `p ^ rank = #k`; for `k = 𝔽_{p^a}` the rank is
`a`. The proof only uses that `𝕎 k` is `p`-adically separated and `p`-torsion-free with
`𝕎 k ⧸ p ≃ k`: complete Nakayama (`Module.Finite.of_finite_quotient_smul_top`) gives finiteness,
`ℤ_p` is a principal ideal domain, and the rank is read off from the reduction modulo `p`
(`TauCeti.natCard_quotient_padicInt_smul_top`).

The `ℤ_p`-module structure is that of an arbitrary `ℤ_[p]`-algebra structure on `𝕎 k`, given as
an instance argument (as Mathlib states results about finite fields for an arbitrary
`Algebra (ZMod p) K`); no instance is declared here. The canonical one is
`(TauCeti.WittVector.padicIntHom p k).toAlgebra`.

For a finite field `k` with `q` elements, the Teichmüller representatives of the nonzero elements
of `k` are exactly the roots of `y ^ (q - 1) = 1`, under any ring homomorphism `φ` from `𝕎 k` to
a domain, for instance an embedding of `W(𝔽_q)` into an algebraic closure of `ℚ_p`: the map
`x ↦ φ [x]` is injective on `k` because `[x] - [y]` is a unit for `x ≠ y`, its values on `kˣ` are
roots, and there are at most `q - 1` roots.

## Main results

* `TauCeti.WittVector.instIsTorsionFreePadicInt`: `𝕎 k` is a torsion-free `ℤ_p`-module.
* `TauCeti.WittVector.instFinitePadicInt`: for finite `k`, `𝕎 k` is a finite `ℤ_p`-module, hence
  free by Mathlib's instance `Module.free_of_finite_type_torsion_free'`.
* `TauCeti.WittVector.natCard_eq_pow_finrank_padicInt`: `#k = p ^ rank_{ℤ_p} 𝕎 k`.
* `TauCeti.WittVector.finrank_padicInt_eq_of_natCard_eq`: if `#k = p ^ a`, the rank is `a`.
* `TauCeti.WittVector.injective_comp_teichmuller`: `x ↦ φ [x]` is injective for every ring
  homomorphism `φ` from the Witt vectors of a field of characteristic `p` to a nontrivial ring.
* `TauCeti.WittVector.pow_natCard_sub_one_eq_one_iff_exists_teichmuller`: for a finite field `k`
  and a ring homomorphism `φ` from `𝕎 k` to a domain, `y ^ (#k - 1) = 1` if and only if `y` is
  `φ [x]` for a unit `x` of `k`.

## References

* J.-P. Serre, *Local Fields*, Graduate Texts in Mathematics 67, Springer, 1979, Chapter II, §§4–6.
* The folder `grh` of https://github.com/lsernau/grh-lean at commit
  72fead102f663d5c7a407964a13dc0cf9d977207: `Lib/PadicHodge/Kisin/Modules.lean`
  (`New.Lift.KummerChart.JumpLattice.finrank_wittFq`) and
  `Lib/PadicHodge/Kisin/KummerChartExistence.lean` (`New.Lift.exists_flatFq_teichmuller_eq`).

The analogous description of the Teichmüller lift of a local field, as the `q`-th-power-fixed
lift of the residue field, is `TauCeti.eq_teichmullerLift_iff`
(`TauCeti.NumberTheory.LocalField.Teichmuller`).
-/

public section

namespace TauCeti.WittVector

open _root_.WittVector Module
open scoped Pointwise

variable (p : ℕ) [Fact p.Prime]

local notation "𝕎" => _root_.WittVector p

section Rank

variable (k : Type*) [CommRing k] [CharP k p] [PerfectRing k p]
  [Algebra ℤ_[p] (WittVector p k)]

/-- Over a perfect ring of characteristic `p`, the Witt vectors are a torsion-free module over
`ℤ_p`, for any `ℤ_p`-algebra structure: a nonzero `p`-adic integer is a unit times a power of `p`,
and `p` is a nonzerodivisor of `𝕎 k`. -/
instance instIsTorsionFreePadicInt : IsTorsionFree ℤ_[p] (𝕎 k) :=
  .of_smul_eq_zero fun a x h ↦ by
    refine or_iff_not_imp_left.2 fun ha ↦ ?_
    have hu : IsUnit (algebraMap ℤ_[p] (𝕎 k) (PadicInt.unitCoeff ha)) :=
      (PadicInt.unitCoeff ha).isUnit.map _
    -- `a • x = u * (p ^ v * x)` with `u` the image of a unit
    rw [Algebra.smul_def, PadicInt.unitCoeff_spec ha] at h
    simp only [map_mul, map_pow, map_natCast, mul_assoc, hu.mul_right_eq_zero] at h
    exact (pow_mem (p_mem_nonZeroDivisors (p := p) (R := k)) _).2 x (by rwa [mul_comm])

/-- The reduction of `𝕎 k` modulo `p`, as a `ℤ_p`-module, is in bijection with `k`: the submodule
`p • 𝕎 k` over `ℤ_p` is the ideal `(p)` of `𝕎 k`, and `𝕎 k ⧸ (p) ≃ k`. -/
private noncomputable def quotientPadicIntEquiv :
    (𝕎 k ⧸ ((p : ℤ_[p]) • ⊤ : Submodule ℤ_[p] (𝕎 k))) ≃ k :=
  ((Submodule.quotEquivOfEq _ ((Ideal.span {(p : 𝕎 k)}).restrictScalars ℤ_[p]) (by
      rw [← Submodule.ideal_span_singleton_smul, Ideal.smul_top_eq_map, Ideal.map_span,
        Set.image_singleton, map_natCast])).trans
    (Submodule.Quotient.restrictScalarsEquiv ℤ_[p] _)).toEquiv.trans quotientPEquiv.toEquiv

variable [Finite k]

/-- **The Witt vectors of a finite perfect ring are a finite `ℤ_p`-module**, by complete Nakayama:
`𝕎 k` is `p`-adically separated and its reduction modulo `p` is `k`, which is finite. -/
instance instFinitePadicInt : Module.Finite ℤ_[p] (𝕎 k) := by
  -- `p`-adic separatedness over `ℤ_p` is that over `𝕎 k`, as `(p)` extends to `(p)`
  have : IsHausdorff (Ideal.span {(p : ℤ_[p])}) (𝕎 k) := by
    rw [← IsHausdorff.map_algebraMap_iff (S := 𝕎 k), Ideal.map_span, Set.image_singleton,
      map_natCast]
    infer_instance
  have : Finite (𝕎 k ⧸ ((p : ℤ_[p]) • ⊤ : Submodule ℤ_[p] (𝕎 k))) :=
    .of_equiv _ (quotientPadicIntEquiv p k).symm
  have : Module.Finite ℤ_[p]
      (𝕎 k ⧸ (Ideal.span {(p : ℤ_[p])} • ⊤ : Submodule ℤ_[p] (𝕎 k))) := by
    rw [Submodule.ideal_span_singleton_smul]
    infer_instance
  exact .of_finite_quotient_smul_top (Ideal.span {(p : ℤ_[p])}) (𝕎 k)

/-- **The rank of `𝕎 k` over `ℤ_p`**: a finite perfect ring `k` of characteristic `p` has
`p ^ r` elements, where `r` is the rank of the free `ℤ_p`-module `𝕎 k`. -/
theorem natCard_eq_pow_finrank_padicInt : Nat.card k = p ^ finrank ℤ_[p] (𝕎 k) := by
  rw [← Nat.card_congr (quotientPadicIntEquiv p k), natCard_quotient_padicInt_smul_top]

omit [Finite k] in
/-- **`W(𝔽_{p^a})` is free of rank `a` over `ℤ_p`**: if `k` has `p ^ a` elements, the rank of
`𝕎 k` over `ℤ_p` is `a`. -/
theorem finrank_padicInt_eq_of_natCard_eq {a : ℕ} (h : Nat.card k = p ^ a) :
    finrank ℤ_[p] (𝕎 k) = a := by
  -- `k` is finite, as `p ^ a ≠ 0`
  have : Finite k := Nat.finite_of_card_ne_zero (h ▸ pow_ne_zero a (NeZero.ne p))
  exact Nat.pow_right_injective (Fact.out : p.Prime).two_le
    ((natCard_eq_pow_finrank_padicInt p k).symm.trans h)

end Rank

section Roots

variable {p} {k : Type*} [Field k] [CharP k p] {K : Type*}

/-- **Teichmüller representatives stay distinct under every ring homomorphism** from the Witt
vectors of a field of characteristic `p` to a nontrivial ring: for `x ≠ y` the difference
`[x] - [y]` has zeroth Witt coordinate `x - y ≠ 0`, so it is a unit. -/
theorem injective_comp_teichmuller [Ring K] [Nontrivial K] (φ : 𝕎 k →+* K) :
    Function.Injective (φ ∘ teichmuller p) := fun x y h ↦ by
  by_contra hxy
  have hu : IsUnit (teichmuller p x - teichmuller p y) :=
    isUnit_iff_isUnit_coeff_zero.mpr (by simpa [sub_coeff_zero, sub_eq_zero] using hxy)
  have h' : φ (teichmuller p x) = φ (teichmuller p y) := h
  simpa [sub_eq_zero.mpr h'] using hu.map φ

/-- **Roots of `y ^ (q - 1) = 1` are Teichmüller representatives.** Let `k` be a finite field with
`q` elements and `φ` a ring homomorphism from `𝕎 k` to a domain `K`, for instance an embedding of
`W(𝔽_q)` into an algebraic closure of `ℚ_p`. Then `y ∈ K` satisfies `y ^ (q - 1) = 1` exactly
when `y = φ [x]` for a unit `x` of `k`. -/
theorem pow_natCard_sub_one_eq_one_iff_exists_teichmuller [Finite k] [CommRing K] [IsDomain K]
    (φ : 𝕎 k →+* K) (y : K) :
    y ^ (Nat.card k - 1) = 1 ↔ ∃ x : kˣ, φ (teichmuller p (x : k)) = y := by
  have hroot (x : kˣ) : φ (teichmuller p (x : k)) ^ (Nat.card k - 1) = 1 := by
    -- `kˣ` has `q - 1` elements
    have hx : x ^ (Nat.card k - 1) = 1 := by rw [← Nat.card_units, pow_card_eq_one']
    rw [← map_pow, ← map_pow, ← Units.val_pow_eq_pow_val, hx]
    simp
  refine ⟨fun hy ↦ ?_, fun ⟨x, hx⟩ ↦ hx ▸ hroot x⟩
  have hn : 0 < Nat.card k - 1 := Nat.sub_pos_of_lt Finite.one_lt_card
  -- `x ↦ φ [x]` maps `kˣ` injectively into the `q - 1`-th roots of unity, of which there are at
  -- most `q - 1 = #kˣ`; so it is onto them.
  let f : kˣ → Polynomial.nthRootsFinset (Nat.card k - 1) (1 : K) := fun x ↦
    ⟨φ (teichmuller p (x : k)), (Polynomial.mem_nthRootsFinset hn 1).mpr (hroot x)⟩
  have hf : f.Injective := fun x x' h ↦
    Units.val_injective (injective_comp_teichmuller φ (congrArg Subtype.val h))
  have hcard : Nat.card (Polynomial.nthRootsFinset (Nat.card k - 1) (1 : K)) ≤ Nat.card kˣ := by
    classical
    rw [Nat.card_units, Nat.card_eq_fintype_card, Fintype.card_coe,
      Polynomial.nthRootsFinset_def]
    exact (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots _ _)
  obtain ⟨x, hx⟩ := (hf.bijective_of_nat_card_le hcard).2
    ⟨y, (Polynomial.mem_nthRootsFinset hn 1).mpr hy⟩
  exact ⟨x, congrArg Subtype.val hx⟩

end Roots

end TauCeti.WittVector

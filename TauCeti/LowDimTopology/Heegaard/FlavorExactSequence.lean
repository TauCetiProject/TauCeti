/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.SquareZero.ShortExact
public import TauCeti.Algebra.Polynomial.Laurent.Polynomial
public import TauCeti.LowDimTopology.Heegaard.MinusDifferential
import Mathlib.Tactic.LinearCombination
import TauCeti.Algebra.Polynomial.Laurent.Basic

/-!
# The short exact sequences relating the flavors of a Heegaard diagram

The combinatorial flavors of a Heegaard diagram
(`TauCeti.LowDimTopology.Heegaard.MinusDifferential`) are related by three short exact sequences
of chain modules, the sources of the long exact sequences relating `HF̂`, `HF⁻`, `HF^∞` and
`HF⁺`. With `U = X` acting on `CF⁻`, on `CF^∞` through
`U = T 1`, and on the quotient `CF⁺ = CF^∞ / CF⁻`, they are:

* `0 → CF⁻ → CF^∞ → CF⁺ → 0`, the inclusion of the chains with polynomial coefficients
  followed by the quotient map
  (`TauCeti.HeegaardRegionSystem.isShortExactDifferential_mapRange_toLaurent_mkQ`);
* `0 → CF⁻ --U--> CF⁻ → CF̂ → 0`, multiplication by `U` followed by setting `U = 0`
  (`TauCeti.HeegaardRegionSystem.isShortExactDifferential_X_smul_mapRange_constantCoeff`);
* `0 → CF̂ → CF⁺ --U--> CF⁺ → 0`, where a generator `x` of `CF̂` goes to the class of `U⁻¹ x`
  (`TauCeti.HeegaardRegionSystem.hatToPlus`), followed by multiplication by `U`
  (`TauCeti.HeegaardRegionSystem.isShortExactDifferential_hatToPlus_X_smul`).

So `CF̂` is both the cokernel of `U` on `CF⁻` and the kernel of `U` on `CF⁺`, on which `U` is onto
(`TauCeti.HeegaardRegionSystem.X_smul_plus_surjective`).

Each sequence is stated as an `AddMonoidHom.IsShortExactDifferential`, the form consumed by the
five lemma `AddMonoidHom.exists_mem_ker_sub_mem_range_of_exact`: the maps are injective, exact and
surjective, and they intertwine the differentials. The inclusion of `CF⁻` into `CF^∞` and the
reduction of `CF⁻` modulo `U` intertwine the differentials by
`TauCeti.HeegaardRegionSystem.infinityDifferential_mapRange_toLaurent` and
`TauCeti.HeegaardRegionSystem.mapRange_constantCoeff_minusDifferential`, and so does the inclusion
of `CF̂` into `CF⁺` (`TauCeti.HeegaardRegionSystem.plusDifferential_hatToPlus`): a term `U ^ k y`
of the infinity differential of `x` survives in `CF⁺` after multiplication by `U⁻¹` only for
`k = 0`, and the domains with `n_z(D) = 0` are those counted by the hat differential. Like the
reduction modulo `U`, this needs the counts to be finite.

The definition of a short exact sequence of differential groups includes that the middle
differential squares to zero. The combinatorial counts satisfy `∂ ∘ ∂ = 0` only for some diagrams,
for instance those in which they agree with the holomorphic counts, and it is not proved here. It is
enough to know it for `CF⁻`: then the infinity differential
(`TauCeti.HeegaardRegionSystem.infinityDifferential_comp_self_eq_zero_iff`), the plus differential
(`TauCeti.HeegaardRegionSystem.plusDifferential_comp_self_eq_zero`) and, for finite counts, the hat
differential (`TauCeti.HeegaardRegionSystem.hatDifferential_comp_self_eq_zero`) square to zero.

## Main definitions

* `TauCeti.HeegaardRegionSystem.hatToPlus`: the inclusion of `CF̂` into `CF⁺` as the kernel of
  `U`, sending `x` to the class of `U⁻¹ x`.

## Main results

* `TauCeti.HeegaardRegionSystem.infinityDifferential_comp_self_eq_zero_iff`,
  `TauCeti.HeegaardRegionSystem.plusDifferential_comp_self_eq_zero` and
  `TauCeti.HeegaardRegionSystem.hatDifferential_comp_self_eq_zero`: `∂ ∘ ∂ = 0` on `CF⁻` gives it on
  the other flavors.
* `TauCeti.HeegaardRegionSystem.plusDifferential_hatToPlus`: the inclusion of `CF̂` into `CF⁺`
  intertwines the differentials.
* `TauCeti.HeegaardRegionSystem.exact_hatToPlus_X_smul`: its image is the kernel of `U`.
* `TauCeti.HeegaardRegionSystem.isShortExactDifferential_mapRange_toLaurent_mkQ`,
  `TauCeti.HeegaardRegionSystem.isShortExactDifferential_X_smul_mapRange_constantCoeff` and
  `TauCeti.HeegaardRegionSystem.isShortExactDifferential_hatToPlus_X_smul`: the three short exact
  sequences.

## References

* P. Ozsváth and Z. Szabó, *Holomorphic disks and topological invariants for closed
  three-manifolds*, Ann. of Math. **159** (2004),
  [arXiv:math/0101206](https://arxiv.org/abs/math/0101206), §4.1 (the short exact sequences
  relating `CF̂`, `CF⁻`, `CF^∞` and `CF⁺`).
-/

public section

open Polynomial LaurentPolynomial

namespace TauCeti

namespace HeegaardRegionSystem

universe u v w

variable {n : ℕ} {Point : Type u} {Region : Type v} {Basepoint : Type w}
  {H : HeegaardRegionSystem n Point Region Basepoint}

section HatToPlus

variable (H) in
/-- The inclusion of `CF̂` into `CF⁺ = CF^∞ / CF⁻` as the kernel of `U`: a generator `x` goes to the
class of `U⁻¹ x`. -/
noncomputable def hatToPlus :
    (H.Generator →₀ ZMod 2) →ₗ[ZMod 2] (H.Generator →₀ (ZMod 2)[T;T⁻¹]) ⧸ H.minusLattice :=
  H.minusLattice.mkQ.restrictScalars (ZMod 2) ∘ₗ
    Finsupp.mapRange.linearMap (LinearMap.toSpanSingleton (ZMod 2) _ (T (-1)))

/-- `hatToPlus` sends a chain `∑ aₓ x` to the class of `∑ aₓ U⁻¹ x`. -/
theorem hatToPlus_apply (c : H.Generator →₀ ZMod 2) :
    H.hatToPlus c = Submodule.Quotient.mk (Finsupp.mapRange
      (fun a => LaurentPolynomial.C a * T (-1)) (by rw [map_zero, zero_mul]) c) := by
  simp only [hatToPlus, LinearMap.coe_comp, Function.comp_apply, Finsupp.mapRange.linearMap_apply,
    LinearMap.coe_restrictScalars, Submodule.mkQ_apply]
  congr 1
  ext x
  simp [LaurentPolynomial.smul_eq_C_mul]

/-- `hatToPlus` sends `a x` to the class of `a U⁻¹ x`. -/
@[simp]
theorem hatToPlus_single (x : H.Generator) (a : ZMod 2) :
    H.hatToPlus (Finsupp.single x a) =
      Submodule.Quotient.mk (Finsupp.single x (LaurentPolynomial.C a * T (-1))) := by
  rw [hatToPlus_apply, Finsupp.mapRange_single]

/-- The inclusion of `CF̂` into `CF⁺` is injective: no nonzero multiple of `U⁻¹ x` has polynomial
coefficients. -/
theorem hatToPlus_injective : Function.Injective H.hatToPlus := by
  refine (injective_iff_map_eq_zero _).mpr fun c hc => ?_
  rw [hatToPlus_apply, Submodule.Quotient.mk_eq_zero, mem_minusLattice_iff] at hc
  ext x
  obtain ⟨p, hp⟩ := hc x
  rw [Finsupp.mapRange_apply] at hp
  exact ((C_mul_T_eq_toLaurent_iff (by norm_num)).mp hp.symm).1

/-- `U` kills the image of `CF̂` in `CF⁺`: `U · U⁻¹ x = x` has polynomial coefficients. -/
@[simp]
theorem X_smul_hatToPlus (c : H.Generator →₀ ZMod 2) : (X : (ZMod 2)[X]) • H.hatToPlus c = 0 := by
  rw [hatToPlus_apply, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero,
    mem_minusLattice_iff]
  intro x
  rw [Finsupp.smul_apply, X_smul_eq_T_one_mul, Finsupp.mapRange_apply, ← mul_assoc,
    T_mul_mul_T_neg]
  exact ⟨Polynomial.C (c x), toLaurent_C _⟩

/-- **`CF̂` is the kernel of `U` on `CF⁺`.** A class in `CF⁺` is killed by `U` exactly when it lies
in the image of `hatToPlus`. -/
theorem exact_hatToPlus_X_smul :
    Function.Exact H.hatToPlus
      fun y : (H.Generator →₀ (ZMod 2)[T;T⁻¹]) ⧸ H.minusLattice => (X : (ZMod 2)[X]) • y := by
  intro y
  refine ⟨fun hy => ?_, fun ⟨c, hc⟩ => hc ▸ X_smul_hatToPlus c⟩
  obtain ⟨c, rfl⟩ := Submodule.mkQ_surjective _ y
  simp only [Submodule.mkQ_apply, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero,
    mem_minusLattice_iff, Finsupp.smul_apply, X_smul_eq_T_one_mul,
    T_one_mul_mem_range_toLaurent_iff] at hy
  refine ⟨Finsupp.mapRange (fun f => f.coeff (-1))
    (by rw [AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply]) c, ?_⟩
  rw [hatToPlus_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, mem_minusLattice_iff]
  intro x
  obtain ⟨p, hp⟩ := hy x
  refine ⟨-p, ?_⟩
  rw [Finsupp.sub_apply, Finsupp.mapRange_apply, Finsupp.mapRange_apply, map_neg]
  linear_combination -hp

/-- On `CF⁺`, `U` is onto: the class of `c` is `U` times the class of `U⁻¹ c`. -/
theorem X_smul_plus_surjective :
    Function.Surjective
      fun y : (H.Generator →₀ (ZMod 2)[T;T⁻¹]) ⧸ H.minusLattice => (X : (ZMod 2)[X]) • y := by
  intro y
  obtain ⟨c, rfl⟩ := Submodule.mkQ_surjective _ y
  refine ⟨Submodule.Quotient.mk ((T (-1) : (ZMod 2)[T;T⁻¹]) • c), ?_⟩
  dsimp only
  rw [← Submodule.Quotient.mk_smul, Submodule.mkQ_apply]
  congr 1
  ext x
  rw [Finsupp.smul_apply, X_smul_eq_T_one_mul, Finsupp.smul_apply, smul_eq_mul,
    ← mul_assoc, ← T_add]
  simp

end HatToPlus

variable [Fintype Point] [DecidableEq Region] [Fintype Region] [Fintype Basepoint]
  {χ : Region → ℤ}

section SquareZero

/-- The infinity differential squares to zero exactly when the minus differential does: `CF^∞` is
`CF⁻` with `U` inverted. -/
theorem infinityDifferential_comp_self_eq_zero_iff :
    H.infinityDifferential χ ∘ₗ H.infinityDifferential χ = 0 ↔
      H.minusDifferential χ ∘ₗ H.minusDifferential χ = 0 := by
  have key (c : H.Generator →₀ (ZMod 2)[X]) :
      H.infinityDifferential χ
          (H.infinityDifferential χ (Finsupp.mapRange toLaurent (map_zero _) c)) =
        Finsupp.mapRange toLaurent (map_zero _)
          (H.minusDifferential χ (H.minusDifferential χ c)) := by
    rw [infinityDifferential_mapRange_toLaurent, infinityDifferential_mapRange_toLaurent]
  constructor
  · intro h
    refine LinearMap.ext fun c => Finsupp.mapRange_injective _ (map_zero _) toLaurent_injective ?_
    simpa [← key] using LinearMap.congr_fun h (Finsupp.mapRange toLaurent (map_zero _) c)
  · intro h
    refine Finsupp.lhom_ext' fun x => LinearMap.ext_ring ?_
    have hx : Finsupp.single x (1 : (ZMod 2)[T;T⁻¹]) =
        Finsupp.mapRange toLaurent (map_zero _) (Finsupp.single x 1) := by
      rw [Finsupp.mapRange_single, map_one]
    simpa [hx, key, -Finsupp.mapRange_single] using
      congr_arg (Finsupp.mapRange toLaurent (map_zero _))
        (LinearMap.congr_fun h (Finsupp.single x 1))

/-- If the minus differential squares to zero, so does the plus differential. -/
theorem plusDifferential_comp_self_eq_zero
    (h : H.minusDifferential χ ∘ₗ H.minusDifferential χ = 0) :
    H.plusDifferential χ ∘ₗ H.plusDifferential χ = 0 := by
  refine LinearMap.ext fun y => ?_
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  simpa [plusDifferential_mk] using
    congr_arg Submodule.Quotient.mk
      (LinearMap.congr_fun (infinityDifferential_comp_self_eq_zero_iff.mpr h) c)

/-- If the minus differential squares to zero and the counts are finite, the hat differential
squares to zero: it is the reduction of the minus differential modulo `U`. -/
theorem hatDifferential_comp_self_eq_zero (hfin : ∀ x y, (H.minusDomains χ x y).Finite)
    (h : H.minusDifferential χ ∘ₗ H.minusDifferential χ = 0) :
    H.hatDifferential χ ∘ₗ H.hatDifferential χ = 0 := by
  refine LinearMap.ext fun c => ?_
  have hc : Finsupp.mapRange constantCoeff (map_zero _)
      (Finsupp.mapRange (Polynomial.C : ZMod 2 →+* (ZMod 2)[X]) (map_zero _) c) = c := by
    ext x
    simp
  rw [LinearMap.comp_apply, ← hc, ← mapRange_constantCoeff_minusDifferential hfin,
    ← mapRange_constantCoeff_minusDifferential hfin]
  simpa using congr_arg (Finsupp.mapRange constantCoeff (map_zero _)) (LinearMap.congr_fun h _)

end SquareZero

section Intertwining

/-- **The inclusion of `CF̂` into `CF⁺` intertwines the differentials.** When the counts are
finite, the plus differential of the class of `U⁻¹ x` is the class of `U⁻¹` times the hat
differential of `x`: a term `U ^ k y` of the infinity differential of `x` survives in `CF⁺` after
multiplication by `U⁻¹` only for `k = 0`, and the domains with `n_z(D) = 0` are those counted by
the hat differential. -/
theorem plusDifferential_hatToPlus (hfin : ∀ x y, (H.minusDomains χ x y).Finite)
    (c : H.Generator →₀ ZMod 2) :
    H.plusDifferential χ (H.hatToPlus c) = H.hatToPlus (H.hatDifferential χ c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single x a =>
    rw [hatToPlus_single, plusDifferential_mk, hatToPlus_apply, Submodule.Quotient.eq,
      mem_minusLattice_iff]
    intro y
    refine ⟨Polynomial.C a * (H.minusCoefficient χ x y).divX, ?_⟩
    simp only [Int.reduceNeg, Finsupp.coe_sub, Pi.sub_apply,
      infinityDifferential_single_apply, Finsupp.mapRange_apply, hatDifferential_single_apply,
      ← coeff_zero_minusCoefficient (hfin x y), map_mul, toLaurent_C]
    linear_combination (-LaurentPolynomial.C a) *
      toLaurent_mul_T_neg_one (H.minusCoefficient χ x y)

end Intertwining

section ShortExact

/-- **`0 → CF⁻ → CF^∞ → CF⁺ → 0`.** If the minus differential squares to zero, the inclusion of
the chains with polynomial coefficients and the quotient map form a short exact sequence of
differential groups. -/
theorem isShortExactDifferential_mapRange_toLaurent_mkQ
    (h : H.minusDifferential χ ∘ₗ H.minusDifferential χ = 0) :
    AddMonoidHom.IsShortExactDifferential
      (Finsupp.mapRange.addMonoidHom (toLaurent : (ZMod 2)[X] →+* (ZMod 2)[T;T⁻¹]).toAddMonoidHom)
      H.minusLattice.mkQ.toAddMonoidHom (H.minusDifferential χ).toAddMonoidHom
      (H.infinityDifferential χ).toAddMonoidHom (H.plusDifferential χ).toAddMonoidHom where
  square_zero c := LinearMap.congr_fun (infinityDifferential_comp_self_eq_zero_iff.mpr h) c
  injective := Finsupp.mapRange_injective _ (map_zero _) toLaurent_injective
  exact c := by
    simp only [LinearMap.toAddMonoidHom_coe, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      mem_minusLattice_iff_exists, Set.mem_range, Finsupp.mapRange.addMonoidHom_apply,
      RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_ofClass]
  surjective := Submodule.mkQ_surjective _
  comm_left c := infinityDifferential_mapRange_toLaurent c
  comm_right c := (plusDifferential_mk c).symm

/-- **`0 → CF⁻ --U--> CF⁻ → CF̂ → 0`.** If the minus differential squares to zero and the counts
are finite, multiplication by `U` and setting `U = 0` form a short exact sequence of differential
groups. -/
theorem isShortExactDifferential_X_smul_mapRange_constantCoeff
    (hfin : ∀ x y, (H.minusDomains χ x y).Finite)
    (h : H.minusDifferential χ ∘ₗ H.minusDifferential χ = 0) :
    AddMonoidHom.IsShortExactDifferential
      (DistribSMul.toAddMonoidHom _ (X : (ZMod 2)[X]))
      (Finsupp.mapRange.addMonoidHom (constantCoeff : (ZMod 2)[X] →+* ZMod 2).toAddMonoidHom)
      (H.minusDifferential χ).toAddMonoidHom (H.minusDifferential χ).toAddMonoidHom
      (H.hatDifferential χ).toAddMonoidHom where
  square_zero c := LinearMap.congr_fun h c
  injective := isRegular_X.left.isSMulRegular.finsupp
  exact c := by
    refine ⟨fun hc => ⟨Finsupp.mapRange divX divX_zero c, Finsupp.ext fun x => ?_⟩, ?_⟩
    · have hx := Finsupp.ext_iff.mp hc x
      simp only [Finsupp.mapRange.addMonoidHom_apply, Finsupp.mapRange_apply,
        RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_ofClass, Finsupp.coe_zero, Pi.zero_apply,
        constantCoeff_apply] at hx
      simpa [hx] using X_mul_divX_add (c x)
    · rintro ⟨d, rfl⟩
      ext x
      simp
  surjective a := ⟨Finsupp.mapRange Polynomial.C (map_zero _) a, by ext x; simp⟩
  comm_left c := map_smul (H.minusDifferential χ) _ c
  comm_right c := mapRange_constantCoeff_minusDifferential hfin c

/-- **`0 → CF̂ → CF⁺ --U--> CF⁺ → 0`.** If the minus differential squares to zero and the counts
are finite, the inclusion of `CF̂` into `CF⁺` as the kernel of `U` and multiplication by `U` form a
short exact sequence of differential groups. -/
theorem isShortExactDifferential_hatToPlus_X_smul
    (hfin : ∀ x y, (H.minusDomains χ x y).Finite)
    (h : H.minusDifferential χ ∘ₗ H.minusDifferential χ = 0) :
    AddMonoidHom.IsShortExactDifferential H.hatToPlus.toAddMonoidHom
      (DistribSMul.toAddMonoidHom _ (X : (ZMod 2)[X])) (H.hatDifferential χ).toAddMonoidHom
      (H.plusDifferential χ).toAddMonoidHom (H.plusDifferential χ).toAddMonoidHom where
  square_zero c := LinearMap.congr_fun (plusDifferential_comp_self_eq_zero h) c
  injective := hatToPlus_injective
  exact := exact_hatToPlus_X_smul
  surjective := X_smul_plus_surjective
  comm_left c := plusDifferential_hatToPlus hfin c
  comm_right c := (map_smul (H.plusDifferential χ) _ c).symm

end ShortExact

end HeegaardRegionSystem

end TauCeti

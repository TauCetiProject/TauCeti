/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.PBW.Injective
public import TauCeti.LinearAlgebra.SymmetricAlgebra.LieModule
public import TauCeti.LinearAlgebra.SymmetricPower.Algebra
import TauCeti.Algebra.BigOperators.Ring.List

/-!
# Degreewise PBW symmetrization

When `n!` is a unit in the commutative base ring, averaging the ordered products of Lie
generators defines a canonical linear map from the `n`th symmetric power to the enveloping
algebra. Its leading PBW symbol is the product of the symmetric generators. When `L` is free
as an `R`-module, this gives an injective map on every homogeneous symmetric-algebra component,
splitting its PBW symbol.

This is the degreewise filtered comparison used to lift invariant symmetric polynomials to
the enveloping algebra without changing their leading terms. Symmetrization intertwines the
adjoint action of `L` on `S(L)` with the commutator action `u ↦ ⁅ι x, u⁆` on `U(L)`: bracketing
a symmetrized word with `ι x` symmetrizes the sum of the words in which one letter `y` is replaced
by `⁅x, y⁆`. Hence the symmetrization of a homogeneous Lie invariant `p ∈ S(L)^L` is central in
`U(L)`, and for free `L` the converse holds as well. These are the central elements whose leading
symbols are the given invariants, in the proof of the Harish-Chandra isomorphism by Chevalley's
restriction theorem.

The scalar ring lies in `Type`, as required by Mathlib's `Fin n`-indexed symmetric power
`Sym[R]^n L`. The Lie algebra module has an independent universe.

## Main results

* `TauCeti.UniversalEnvelopingAlgebra.lie_ι_pbwSymmetrization_tprod`: the commutator of `ι x`
  with a symmetrized word.
* `TauCeti.UniversalEnvelopingAlgebra.lie_ι_pbwHomogeneousSymmetrization`: symmetrization is
  equivariant for the adjoint actions on `S(L)` and `U(L)`.
* `TauCeti.UniversalEnvelopingAlgebra.pbwHomogeneousSymmetrization_mem_center`: the
  symmetrization of a homogeneous Lie invariant is central.
* `TauCeti.UniversalEnvelopingAlgebra.pbwHomogeneousSymmetrization_mem_center_iff` and
  `TauCeti.UniversalEnvelopingAlgebra.pbwSymmetrization_mem_center_iff`: for free `L`, a
  symmetrization is central exactly when the symmetric polynomial is a Lie invariant.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §23.3.
* J. Dixmier, *Enveloping Algebras*, §2.4.

The Lean code is adapted from the closed Tau Ceti PR
https://github.com/TauCetiProject/TauCeti/pull/18162 (feat: construct degreewise PBW
symmetrization).
-/

public section

open scoped TensorProduct

namespace TauCeti.UniversalEnvelopingAlgebra

open TauCeti.SymmetricAlgebra

universe v

variable (R : Type) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L]

attribute [local instance 100] LieRing.ofAssociativeRing

local notation "U" => _root_.UniversalEnvelopingAlgebra R L
local notation "ι" => _root_.UniversalEnvelopingAlgebra.ι R (L := L)

private noncomputable def wordMultilinear (n : ℕ) :
    MultilinearMap R (fun _ : Fin n ↦ L) U :=
  (MultilinearMap.mkPiAlgebraFin R n U).compLinearMap (fun _ ↦ (ι).toLinearMap)

/-- The average of all ordered products of a symmetric tensor's Lie generators. -/
noncomputable def pbwSymmetrization (n : ℕ) (hn : IsUnit (n.factorial : R)) : Sym[R]^n L →ₗ[R] U :=
  (↑hn.unit⁻¹ : R) •
    ((PiTensorProduct.lift (wordMultilinear R L n)).comp
      (SymmetricPower.toTensorPower R (Fin n) L))

/-- On pure symmetric tensors, symmetrization averages the products over all permutations. -/
@[simp]
theorem pbwSymmetrization_tprod (n : ℕ) (hn : IsUnit (n.factorial : R)) (m : Fin n → L) :
    pbwSymmetrization R L n hn (⨂ₛ[R] i, m i) =
      (↑hn.unit⁻¹ : R) •
        ∑ σ : Equiv.Perm (Fin n), (List.ofFn fun i ↦ ι (m (σ i))).prod := by
  simp [pbwSymmetrization, wordMultilinear]

/-- Over a rational algebra, the unit-normalized average is the usual rational average. -/
theorem pbwSymmetrization_tprod_rat [Algebra ℚ R] (n : ℕ)
    (hn : IsUnit (n.factorial : R)) (m : Fin n → L) :
    pbwSymmetrization R L n hn (⨂ₛ[R] i, m i) =
      algebraMap ℚ R ((n.factorial : ℚ)⁻¹) •
        ∑ σ : Equiv.Perm (Fin n), (List.ofFn fun i ↦ ι (m (σ i))).prod := by
  rw [pbwSymmetrization_tprod]
  have hinv : (↑hn.unit⁻¹ : R) = algebraMap ℚ R ((n.factorial : ℚ)⁻¹) := by
    apply hn.unit.inv_eq_of_mul_eq_one_left
    rw [IsUnit.unit_spec, ← map_natCast (algebraMap ℚ R) n.factorial]
    simp only [← map_mul]
    simp [Nat.factorial_ne_zero]
  rw [hinv]

/-- Symmetrization sends a pure power to the corresponding power of a Lie generator. -/
@[simp high] -- Normalize pure powers before expanding the permutation sum.
theorem pbwSymmetrization_tprod_const (n : ℕ) (hn : IsUnit (n.factorial : R)) (x : L) :
    pbwSymmetrization R L n hn (⨂ₛ[R] _ : Fin n, x) = (ι x) ^ n := by
  rw [pbwSymmetrization_tprod]
  -- All `n!` ordered products of `n` copies of `x` are `x ^ n`.
  simp only [List.ofFn_const, List.prod_replicate, Finset.sum_const, Finset.card_univ,
    Fintype.card_perm, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul R, smul_smul, hn.val_inv_mul,
    one_smul]

/-- Symmetrization has PBW filtration degree at most its symmetric degree. -/
theorem pbwSymmetrization_mem_pbwFiltration (n : ℕ) (hn : IsUnit (n.factorial : R))
    (x : Sym[R]^n L) :
    pbwSymmetrization R L n hn x ∈ pbwFiltration R L n := by
  apply LinearMap.apply_mem_of_forall_symmetricPower_tprod
  intro m
  rw [pbwSymmetrization_tprod]
  apply Submodule.smul_mem
  apply Submodule.sum_mem
  intro σ _
  simpa only [List.map_ofFn, Function.comp_def] using
    prod_map_ι_mem_pbwFiltration R L (l := List.ofFn fun i ↦ m (σ i)) (by simp)

/-- Symmetrizing a word changes it only in strictly smaller PBW filtration degree. -/
theorem pbwSymmetrization_tprod_sub_mem_pbwFiltrationPrevious (n : ℕ)
    (hn : IsUnit (n.factorial : R)) (m : Fin n → L) :
    pbwSymmetrization R L n hn (⨂ₛ[R] i, m i) - (List.ofFn fun i ↦ ι (m i)).prod ∈
      pbwFiltrationPrevious R L n := by
  classical
  have h (σ : Equiv.Perm (Fin n)) :
      (List.ofFn fun i ↦ ι (m (σ i))).prod - (List.ofFn fun i ↦ ι (m i)).prod ∈
        pbwFiltrationPrevious R L n := by
    simpa only [List.map_ofFn, Function.comp_def, List.length_ofFn] using
      prod_map_ι_sub_prod_map_ι_mem_pbwFiltrationPrevious_of_perm R L
        (σ.ofFn_comp_perm m)
  have hsum := (pbwFiltrationPrevious R L n).smul_mem
    (↑hn.unit⁻¹ : R)
    ((pbwFiltrationPrevious R L n).sum_mem (t := Finset.univ) fun σ _ ↦ h σ)
  simpa only [Finset.sum_sub_distrib, smul_sub, Finset.sum_const, Finset.card_univ,
    Fintype.card_perm, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul R, smul_smul, hn.val_inv_mul,
    one_smul, pbwSymmetrization_tprod] using hsum

/-- The leading symbol of tensor symmetrization is its canonical PBW image, without any
freeness assumption on the Lie algebra module. -/
@[simp↓] -- Take the symbol before expanding tensor symmetrization.
theorem mk_pbwSymmetrization (n : ℕ) (hn : IsUnit (n.factorial : R))
    (x : Sym[R]^n L) :
    Submodule.Quotient.mk
      (⟨pbwSymmetrization R L n hn x,
        by simpa only [pbwFiltration_def] using
          pbwSymmetrization_mem_pbwFiltration R L n hn x⟩ :
        TauCeti.Algebra.wordFiltration (ι).toLinearMap n) =
      pbwHomogeneousComponentMap R L n (SymmetricPower.toHomogeneous R L n x) := by
  let lhs : Sym[R]^n L →ₗ[R] PBWGradedPiece R L n :=
    (Submodule.mkQ (TauCeti.Algebra.wordFiltration.previousRestricted (ι).toLinearMap n)).comp
      ((pbwSymmetrization R L n hn).codRestrict _ fun x ↦
        by simpa only [pbwFiltration_def] using
          pbwSymmetrization_mem_pbwFiltration R L n hn x)
  suffices hl : lhs = (pbwHomogeneousComponentMap R L n).comp
      (SymmetricPower.toHomogeneous R L n) from LinearMap.congr_fun hl x
  apply SymmetricPower.ext
  intro m
  have hprod : SymmetricPower.toHomogeneous R L n (⨂ₛ[R] i, m i) =
      ⟨((List.ofFn m).map (SymmetricAlgebra.ι R L)).prod,
        by simpa only [List.length_ofFn] using
          prod_map_ι_mem_homogeneousSubmodule R L (List.ofFn m)⟩ := by
    apply Subtype.ext
    simp [List.prod_ofFn]
  simp only [LinearMap.comp_apply, hprod,
    pbwHomogeneousComponentMap_prod_map_ι_of_length_eq R L (List.ofFn m) List.length_ofFn]
  apply (Submodule.Quotient.eq _).mpr
  rw [TauCeti.Algebra.wordFiltration.mem_previousRestricted_iff]
  simp only [LinearMap.codRestrict_apply, Submodule.coe_sub]
  simpa only [pbwFiltrationPrevious_def, List.map_ofFn, Function.comp_def] using
    pbwSymmetrization_tprod_sub_mem_pbwFiltrationPrevious R L n hn m

/-- Degreewise symmetrization, expressed on homogeneous symmetric polynomials. -/
noncomputable def pbwHomogeneousSymmetrization (n : ℕ) (hn : IsUnit (n.factorial : R)) :
    homogeneousSubmodule R L n →ₗ[R] U :=
  (pbwSymmetrization R L n hn).comp
    (SymmetricPower.equivHomogeneous (R := R) (M := L) n).symm.toLinearMap

/-- Homogeneous symmetrization is tensor symmetrization after the inverse comparison. -/
@[simp low] -- Prefer cancelling the homogeneous comparison before expanding.
theorem pbwHomogeneousSymmetrization_apply (n : ℕ) (hn : IsUnit (n.factorial : R))
    (p : homogeneousSubmodule R L n) :
    pbwHomogeneousSymmetrization R L n hn p =
      pbwSymmetrization R L n hn ((SymmetricPower.equivHomogeneous n).symm p) := by
  rfl

/-- The homogeneous map agrees with tensor symmetrization under the canonical comparison. -/
@[simp]
theorem pbwHomogeneousSymmetrization_equivHomogeneous (n : ℕ) (hn : IsUnit (n.factorial : R))
    (x : Sym[R]^n L) :
    pbwHomogeneousSymmetrization R L n hn (SymmetricPower.equivHomogeneous n x) =
      pbwSymmetrization R L n hn x := by
  simp [pbwHomogeneousSymmetrization]

/-- Homogeneous symmetrization lands in the corresponding PBW filtration step. -/
theorem pbwHomogeneousSymmetrization_mem_pbwFiltration (n : ℕ) (hn : IsUnit (n.factorial : R))
    (p : homogeneousSubmodule R L n) :
    pbwHomogeneousSymmetrization R L n hn p ∈ pbwFiltration R L n := by
  rw [pbwHomogeneousSymmetrization_apply]
  exact pbwSymmetrization_mem_pbwFiltration R L n hn _

/-- Homogeneous symmetrization lands in the word filtration used for the PBW graded piece. -/
theorem pbwHomogeneousSymmetrization_mem_wordFiltration (n : ℕ) (hn : IsUnit (n.factorial : R))
    (p : homogeneousSubmodule R L n) :
    pbwHomogeneousSymmetrization R L n hn p ∈ TauCeti.Algebra.wordFiltration (ι).toLinearMap n := by
  simpa only [pbwFiltration_def] using
    pbwHomogeneousSymmetrization_mem_pbwFiltration R L n hn p

/-- Taking the leading PBW symbol of symmetrization recovers the canonical PBW image. -/
@[simp↓] -- Take the symbol before expanding homogeneous symmetrization.
theorem mk_pbwHomogeneousSymmetrization (n : ℕ) (hn : IsUnit (n.factorial : R))
    (p : homogeneousSubmodule R L n) :
    Submodule.Quotient.mk
      (⟨pbwHomogeneousSymmetrization R L n hn p,
        pbwHomogeneousSymmetrization_mem_wordFiltration R L n hn p⟩ :
        TauCeti.Algebra.wordFiltration (ι).toLinearMap n) =
      pbwHomogeneousComponentMap R L n p := by
  simpa only [← SymmetricPower.toLinearMap_equivHomogeneous, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, pbwHomogeneousSymmetrization_apply] using
    mk_pbwSymmetrization R L n hn ((SymmetricPower.equivHomogeneous n).symm p)

/-! ### Equivariance and central elements -/

section Center

/-- **The commutator with a Lie generator, on a symmetrized word.** Bracketing the
symmetrization of `m 0, …, m (n - 1)` with `ι x` gives the sum of the symmetrizations of the
words in which one letter `m k` is replaced by `⁅x, m k⁆`. -/
theorem lie_ι_pbwSymmetrization_tprod (n : ℕ) (hn : IsUnit (n.factorial : R)) (x : L)
    (m : Fin n → L) :
    ⁅ι x, pbwSymmetrization R L n hn (⨂ₛ[R] i, m i)⁆ =
      ∑ k, pbwSymmetrization R L n hn (⨂ₛ[R] i, Function.update m k ⁅x, m k⁆ i) := by
  have hleib (a b : U) : ⁅ι x, a * b⁆ = ⁅ι x, a⁆ * b + a * ⁅ι x, b⁆ := by
    simp only [LieRing.of_associative_ring_bracket, mul_sub, sub_mul, mul_assoc]
    abel
  simp only [pbwSymmetrization_tprod, lie_smul, lie_sum, ← Finset.smul_sum]
  rw [Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun σ _ ↦ ?_
  have h := (LieAlgebra.ad R U (ι x)).toAddMonoidHom.map_prod_ofFn_of_leibniz
    (by simpa only [LinearMap.toAddMonoidHom_coe, LieAlgebra.ad_apply] using hleib)
    (fun i ↦ ι (m (σ i)))
  simp only [LinearMap.toAddMonoidHom_coe, LieAlgebra.ad_apply] at h
  rw [h]
  -- Reindex the replaced letter by its position `σ k` in the permuted word.
  conv_rhs => rw [← Equiv.sum_comp σ]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  congr 2
  funext i
  rw [← LieHom.map_lie]
  rcases eq_or_ne i k with rfl | hik
  · simp
  · simp [hik, σ.injective.ne hik]

/-- **Symmetrization is equivariant for the adjoint actions.** If `q` is the image of the
homogeneous symmetric polynomial `p` under the adjoint action of `x` on `S(L)`, then the
symmetrization of `q` is the commutator of `ι x` with the symmetrization of `p`. -/
theorem lie_ι_pbwHomogeneousSymmetrization (n : ℕ) (hn : IsUnit (n.factorial : R)) (x : L)
    {p q : homogeneousSubmodule R L n}
    (hpq : lieModuleDerivation R L L x (p : SymmetricAlgebra R L) = q) :
    ⁅ι x, pbwHomogeneousSymmetrization R L n hn p⁆ = pbwHomogeneousSymmetrization R L n hn q := by
  let e := SymmetricPower.equivHomogeneous (R := R) (M := L) n
  let D : homogeneousSubmodule R L n →ₗ[R] homogeneousSubmodule R L n :=
    (lieModuleDerivation R L L x).toLinearMap.restrict
      fun _ hp ↦ lieModuleDerivation_mem_homogeneousSubmodule R L L x hp
  have hD : (LieAlgebra.ad R U (ι x)) ∘ₗ pbwSymmetrization R L n hn =
      pbwSymmetrization R L n hn ∘ₗ e.symm.toLinearMap ∘ₗ D ∘ₗ e.toLinearMap := by
    refine SymmetricPower.ext fun m ↦ ?_
    have hleib (a b : SymmetricAlgebra R L) :
        lieModuleDerivation R L L x (a * b) =
          lieModuleDerivation R L L x a * b + a * lieModuleDerivation R L L x b := by
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, add_comm, mul_comm b]
    have hprod := (lieModuleDerivation R L L x).toLinearMap.toAddMonoidHom.map_prod_ofFn_of_leibniz
      (by simpa only [LinearMap.toAddMonoidHom_coe, Derivation.coeFn_coe] using hleib)
      (fun i ↦ _root_.SymmetricAlgebra.ι R L (m i))
    simp only [LinearMap.toAddMonoidHom_coe, Derivation.coeFn_coe, List.prod_ofFn] at hprod
    have hDm : D (e (⨂ₛ[R] i, m i)) = ∑ k, e (⨂ₛ[R] i, Function.update m k ⁅x, m k⁆ i) := by
      apply Subtype.ext
      simp only [D, e, LinearMap.restrict_apply, Submodule.coe_sum,
        SymmetricPower.coe_equivHomogeneous_apply, SymmetricPower.toSymmetricAlgebra_tprod,
        Derivation.coeFn_coe, hprod]
      refine Finset.sum_congr rfl fun k _ ↦ Finset.prod_congr rfl fun i _ ↦ ?_
      rcases eq_or_ne i k with rfl | hik
      · simp
      · simp [hik]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LieAlgebra.ad_apply, hDm, map_sum,
      LinearEquiv.symm_apply_apply, lie_ι_pbwSymmetrization_tprod]
  have hq : q = D p := Subtype.ext hpq.symm
  have h := LinearMap.congr_fun hD (e.symm p)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LieAlgebra.ad_apply,
    LinearEquiv.apply_symm_apply] at h
  rw [pbwHomogeneousSymmetrization_apply, pbwHomogeneousSymmetrization_apply, hq]
  exact h

/-- **Symmetrizing a Lie invariant gives a central element.** The symmetrization of a
homogeneous element of `S(L)^L` commutes with every element of `U(L)`. -/
theorem pbwHomogeneousSymmetrization_mem_center (n : ℕ) (hn : IsUnit (n.factorial : R))
    {p : homogeneousSubmodule R L n} (hp : (p : SymmetricAlgebra R L) ∈ lieInvariants R L L) :
    pbwHomogeneousSymmetrization R L n hn p ∈ Subalgebra.center R U := by
  refine (mem_center_iff_forall_lie_ι R L).mpr fun x ↦ ?_
  rw [← lie_skew, lie_ι_pbwHomogeneousSymmetrization R L n hn x (q := 0)
    (by rw [mem_lieInvariants.mp hp x, Submodule.coe_zero]), map_zero, neg_zero]

/-- **Symmetrizing a Lie-invariant symmetric tensor gives a central element.** -/
theorem pbwSymmetrization_mem_center (n : ℕ) (hn : IsUnit (n.factorial : R)) {t : Sym[R]^n L}
    (ht : SymmetricPower.toSymmetricAlgebra R L n t ∈ lieInvariants R L L) :
    pbwSymmetrization R L n hn t ∈ Subalgebra.center R U := by
  simpa only [pbwHomogeneousSymmetrization_equivHomogeneous] using
    pbwHomogeneousSymmetrization_mem_center R L n hn
      (p := SymmetricPower.equivHomogeneous n t)
      (by rwa [SymmetricPower.coe_equivHomogeneous_apply])

end Center

variable [Module.Free R L]

/-- Symmetrization of homogeneous symmetric polynomials is injective. -/
theorem pbwHomogeneousSymmetrization_injective (n : ℕ) (hn : IsUnit (n.factorial : R)) :
    Function.Injective (pbwHomogeneousSymmetrization R L n hn) := by
  intro p q hpq
  apply pbwHomogeneousComponentMap_injective R L n
  rw [← mk_pbwHomogeneousSymmetrization R L n hn,
    ← mk_pbwHomogeneousSymmetrization R L n hn]
  exact congrArg Submodule.Quotient.mk (Subtype.ext hpq)

/-- Degreewise tensor symmetrization is injective when the Lie algebra module is free. -/
theorem pbwSymmetrization_injective (n : ℕ) (hn : IsUnit (n.factorial : R)) :
    Function.Injective (pbwSymmetrization R L n hn) := by
  intro x y h
  apply (SymmetricPower.equivHomogeneous (R := R) (M := L) n).injective
  apply pbwHomogeneousSymmetrization_injective R L n hn
  simpa only [pbwHomogeneousSymmetrization_equivHomogeneous] using h

/-- **The symmetrization of a homogeneous polynomial is central exactly when the polynomial is a
Lie invariant**, for `L` free over `R`. Symmetrization intertwines the adjoint actions on `S(L)`
and on `U(L)`, and it is injective on each homogeneous component. -/
@[simp↓] -- Fire before `pbwHomogeneousSymmetrization_apply` unfolds the left-hand side.
theorem pbwHomogeneousSymmetrization_mem_center_iff (n : ℕ) (hn : IsUnit (n.factorial : R))
    {p : homogeneousSubmodule R L n} :
    pbwHomogeneousSymmetrization R L n hn p ∈ Subalgebra.center R U ↔
      (p : SymmetricAlgebra R L) ∈ lieInvariants R L L := by
  refine ⟨fun h ↦ mem_lieInvariants.mpr fun x ↦ ?_,
    pbwHomogeneousSymmetrization_mem_center R L n hn⟩
  let q : homogeneousSubmodule R L n :=
    ⟨lieModuleDerivation R L L x p, lieModuleDerivation_mem_homogeneousSubmodule R L L x p.2⟩
  have hq : pbwHomogeneousSymmetrization R L n hn q = pbwHomogeneousSymmetrization R L n hn 0 := by
    rw [← lie_ι_pbwHomogeneousSymmetrization R L n hn x rfl, ← lie_skew,
      (mem_center_iff_forall_lie_ι R L).mp h x, neg_zero, map_zero]
  exact congrArg Subtype.val (pbwHomogeneousSymmetrization_injective R L n hn hq)

/-- **The symmetrization of a symmetric tensor is central exactly when the tensor is a Lie
invariant**, read in `S(L)`, for `L` free over `R`. -/
@[simp]
theorem pbwSymmetrization_mem_center_iff (n : ℕ) (hn : IsUnit (n.factorial : R))
    {t : Sym[R]^n L} :
    pbwSymmetrization R L n hn t ∈ Subalgebra.center R U ↔
      SymmetricPower.toSymmetricAlgebra R L n t ∈ lieInvariants R L L := by
  simpa only [pbwHomogeneousSymmetrization_equivHomogeneous,
    SymmetricPower.coe_equivHomogeneous_apply] using
    pbwHomogeneousSymmetrization_mem_center_iff R L n hn (p := SymmetricPower.equivHomogeneous n t)

end TauCeti.UniversalEnvelopingAlgebra

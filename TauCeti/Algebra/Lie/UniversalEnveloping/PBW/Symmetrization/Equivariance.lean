/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.PBW.Symmetrization.Equiv
import TauCeti.Algebra.BigOperators.Ring.List
import TauCeti.LinearAlgebra.SymmetricAlgebra.Powers

/-!
# Adjoint equivariance and filtration of PBW symmetrization

Let `L` be a Lie algebra over a commutative `ℚ`-algebra `R`. A linear map
`e : Sym_R(L) → U_R(L)` is a *PBW symmetrization* (`IsPBWSymmetrization`) when it sends a product
of `d` generators to `1/d!` times the sum of their products in all `d!` orders. The formula
determines `e` (`IsPBWSymmetrization.unique`), since pure powers span the symmetric algebra, and the
canonical global symmetrization `pbwSymmetrizationMap` satisfies it when `R : Type`.

This file proves the two structural properties of such a map, working directly with the formula,
so that the scalar ring may lie in any universe:

* **adjoint equivariance**: `e ⁅x, p⁆ = ι x * e p - e p * ι x`, where `L` acts on `Sym(L)` by
  the derivations extending `ad x`;
* **filtration**: a symmetric tensor has degree at most `n` exactly when its image has PBW degree
  at most `n`. The forward inclusion needs nothing; the converse needs `L` free over `R`, and
  uses that the leading PBW symbol of the image of a homogeneous tensor is its canonical image
  in the associated graded algebra.

Consequently `e` is injective for free `L`, and an element of `Sym(L)` is a Lie invariant exactly
when its symmetrization is central in `U(L)`. For the canonical map the injectivity holds without
freeness, so its centre criterion holds for every Lie algebra over a commutative `ℚ`-algebra in
`Type`.

The word computation behind the equivariance is that of
`TauCeti.UniversalEnvelopingAlgebra.lie_ι_pbwSymmetrization_tprod`, carried out on the formula
because that lemma is stated on `Sym[R]^n L` and so needs `R : Type`.

## Main definitions and results

* `TauCeti.UniversalEnvelopingAlgebra.IsPBWSymmetrization`: the permutation-average formula.
* `TauCeti.UniversalEnvelopingAlgebra.IsPBWSymmetrization.map_lie`: adjoint equivariance.
* `TauCeti.UniversalEnvelopingAlgebra.IsPBWSymmetrization.mem_pbwFiltration_iff`: the two-sided
  filtration statement.
* `TauCeti.UniversalEnvelopingAlgebra.IsPBWSymmetrization.injective`: injectivity for free `L`.
* `TauCeti.UniversalEnvelopingAlgebra.IsPBWSymmetrization.mem_center_iff`: the centre criterion.
* `TauCeti.UniversalEnvelopingAlgebra.pbwSymmetrizationMap_lie` and
  `TauCeti.UniversalEnvelopingAlgebra.pbwSymmetrizationMap_mem_center_iff`: the canonical map.

## References

* J. Dixmier, *Enveloping Algebras*, §2.4.
* P. Etingof, *Representations of Lie groups*, proof of Theorem 13.5.
-/

public section

namespace TauCeti.UniversalEnvelopingAlgebra

open TauCeti.SymmetricAlgebra

universe u v

section General

variable (R : Type u) (L : Type v) [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]

attribute [local instance 100] LieRing.ofAssociativeRing

local notation "U" => _root_.UniversalEnvelopingAlgebra R L
local notation "ι" => _root_.UniversalEnvelopingAlgebra.ι R (L := L)
local notation "𝒮" => homogeneousSubmodule R L
local notation "F" => TauCeti.Algebra.wordFiltration (SymmetricAlgebra.ι R L)

/-- A linear map `Sym_R(L) → U_R(L)` is a **PBW symmetrization** when it sends a product of `d`
generators to `1/d!` times the sum of their products in all `d!` orders. The empty product is
sent to `1`. -/
structure IsPBWSymmetrization (e : SymmetricAlgebra R L →ₗ[R] U) : Prop where
  /-- The permutation-average formula on a product of generators. -/
  apply_prod_ι (d : ℕ) (x : Fin d → L) :
    e (∏ j, SymmetricAlgebra.ι R L (x j)) =
      algebraMap ℚ R (d.factorial : ℚ)⁻¹ • ∑ σ : Equiv.Perm (Fin d),
        (List.ofFn fun j ↦ ι (x (σ j))).prod

variable {R L}

namespace IsPBWSymmetrization

variable {e : SymmetricAlgebra R L →ₗ[R] _root_.UniversalEnvelopingAlgebra R L}
  (he : IsPBWSymmetrization R L e)
include he

/-- A PBW symmetrization fixes pure powers: `e (x ^ n) = ι x ^ n`. -/
theorem apply_ι_pow (x : L) (n : ℕ) : e (SymmetricAlgebra.ι R L x ^ n) = ι x ^ n := by
  have h := he.apply_prod_ι n fun _ ↦ x
  have hn : (n.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, List.ofFn_const,
    List.prod_replicate, Finset.sum_const, Fintype.card_perm] at h
  rw [h, ← Nat.cast_smul_eq_nsmul R, smul_smul, ← map_natCast (algebraMap ℚ R), ← map_mul,
    inv_mul_cancel₀ hn, map_one, one_smul]

/-- **The formula determines the map**: two PBW symmetrizations are equal. -/
theorem unique {e' : SymmetricAlgebra R L →ₗ[R] U} (he' : IsPBWSymmetrization R L e') : e = e' :=
  linearMap_ext_ι_pow R L fun x n ↦ by rw [he.apply_ι_pow, he'.apply_ι_pow]

/-- Equivariance on a product of generators, in bracket form. -/
private theorem lie_ι_apply_prod_ι (x : L) {n : ℕ} (m : Fin n → L) :
    ⁅ι x, e (∏ j, SymmetricAlgebra.ι R L (m j))⁆ =
      e (lieModuleDerivation R L L x (∏ j, SymmetricAlgebra.ι R L (m j))) := by
  -- Expand the derivation on `Sym(L)` by the Leibniz rule, one letter at a time.
  have hleibS (a b : SymmetricAlgebra R L) :
      lieModuleDerivation R L L x (a * b) =
        lieModuleDerivation R L L x a * b + a * lieModuleDerivation R L L x b := by
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, add_comm, mul_comm b]
  have hS := map_prod_ofFn_of_leibniz (lieModuleDerivation R L L x) hleibS
    fun i ↦ SymmetricAlgebra.ι R L (m i)
  simp only [List.prod_ofFn] at hS
  have hupd (k : Fin n) : (∏ i, Function.update (fun i ↦ SymmetricAlgebra.ι R L (m i)) k
      (lieModuleDerivation R L L x (SymmetricAlgebra.ι R L (m k))) i) =
        ∏ i, SymmetricAlgebra.ι R L (Function.update m k ⁅x, m k⁆ i) := by
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    rcases eq_or_ne i k with rfl | hik
    · simp
    · simp [hik]
  -- Expand the commutator with `ι x` on each ordered word, and reindex the replaced letter.
  have hleib (a b : U) : ⁅ι x, a * b⁆ = ⁅ι x, a⁆ * b + a * ⁅ι x, b⁆ := by
    simp only [LieRing.of_associative_ring_bracket, mul_sub, sub_mul, mul_assoc]
    abel
  simp only [hS, hupd, map_sum, he.apply_prod_ι, lie_smul, lie_sum, ← Finset.smul_sum]
  rw [Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun σ _ ↦ ?_
  rw [map_prod_ofFn_of_leibniz (⁅ι x, ·⁆) hleib]
  conv_rhs => rw [← Equiv.sum_comp σ]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  congr 2
  funext i
  rw [← LieHom.map_lie]
  rcases eq_or_ne i k with rfl | hik
  · simp
  · simp [hik, σ.injective.ne hik]

/-- **PBW symmetrization is equivariant for the adjoint actions**: for the action of `L` on
`Sym(L)` by the derivations extending `ad x`, `e ⁅x, p⁆ = ι x * e p - e p * ι x`. -/
theorem map_lie (x : L) (p : SymmetricAlgebra R L) :
    e ⁅x, p⁆ = ι x * e p - e p * ι x := by
  have h : e ∘ₗ (lieModuleDerivation R L L x).toLinearMap =
      LieAlgebra.ad R U (ι x) ∘ₗ e := by
    refine linearMap_ext_ι_pow R L fun y n ↦ ?_
    have hy : SymmetricAlgebra.ι R L y ^ n = ∏ _j : Fin n, SymmetricAlgebra.ι R L y := by
      simp
    simp only [LinearMap.comp_apply, Derivation.coeFn_coe, LieAlgebra.ad_apply, hy]
    exact (he.lie_ι_apply_prod_ι x fun _ ↦ y).symm
  simpa only [LinearMap.comp_apply, Derivation.coeFn_coe, LieAlgebra.ad_apply,
    LieRing.of_associative_ring_bracket, lie_eq_lieModuleDerivation] using
    LinearMap.congr_fun h p

/-- A PBW symmetrization does not increase degree: it sends the `k`-th degree step of `Sym(L)`
into the `k`-th PBW filtration step. -/
theorem mem_pbwFiltration {k : ℕ} {p : SymmetricAlgebra R L} (hp : p ∈ F k) :
    e p ∈ pbwFiltration R L k := by
  have hle : F k ≤ (pbwFiltration R L k).comap e := by
    rw [TauCeti.Algebra.wordFiltration_eq_iSup_pow]
    refine iSup_le fun i ↦ ?_
    rw [← homogeneousSubmodule,
      ← span_range_ι_pow R L i (IsUnit.natCast_factorial_of_algebra ℚ i), Submodule.span_le]
    rintro _ ⟨y, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, he.apply_ι_pow]
    exact pbwFiltration_mono R L i.property (ι_pow_mem_pbwFiltration R L y i)
  exact hle hp

/-- **The leading symbol of a symmetrized homogeneous tensor** is its canonical image in the
associated graded algebra of the PBW filtration. -/
private theorem mk_apply_eq_pbwHomogeneousComponentMap (n : ℕ) (p : 𝒮 n) :
    Submodule.Quotient.mk
      (⟨e p, by
        simpa only [pbwFiltration_def] using
          he.mem_pbwFiltration (TauCeti.Algebra.range_pow_le_wordFiltration _ n p.2)⟩ :
        TauCeti.Algebra.wordFiltration (ι).toLinearMap n) =
      pbwHomogeneousComponentMap R L n p := by
  let ψ : 𝒮 n →ₗ[R] PBWGradedPiece R L n :=
    (Submodule.mkQ (TauCeti.Algebra.wordFiltration.previousRestricted (ι).toLinearMap n)).comp
      ((e ∘ₗ (𝒮 n).subtype).codRestrict _ fun p ↦ by
        simpa only [pbwFiltration_def, LinearMap.comp_apply, Submodule.subtype_apply] using
          he.mem_pbwFiltration (TauCeti.Algebra.range_pow_le_wordFiltration _ n p.2))
  -- The pure powers span the homogeneous piece, and on them both maps give the class of `ι x ^ n`.
  let v : L → 𝒮 n := fun y ↦ ⟨SymmetricAlgebra.ι R L y ^ n, by
    simpa using prod_map_ι_mem_homogeneousSubmodule R L (List.replicate n y)⟩
  have hv : Submodule.span R (Set.range v) = ⊤ := by
    refine Submodule.map_injective_of_injective (𝒮 n).injective_subtype ?_
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp]
    exact span_range_ι_pow R L n (IsUnit.natCast_factorial_of_algebra ℚ n)
  suffices hψ : ψ = pbwHomogeneousComponentMap R L n from LinearMap.congr_fun hψ p
  refine LinearMap.ext_on_range hv fun y ↦ ?_
  have hw : v y = ⟨((List.replicate n y).map (SymmetricAlgebra.ι R L)).prod, by
      simpa only [List.length_replicate] using
        prod_map_ι_mem_homogeneousSubmodule R L (List.replicate n y)⟩ :=
    Subtype.ext (by simp [v])
  rw [hw, pbwHomogeneousComponentMap_prod_map_ι_of_length_eq R L _ (List.length_replicate ..)]
  refine congrArg Submodule.Quotient.mk (Subtype.ext ?_)
  simp [he.apply_ι_pow]

/-- For free `L`, a homogeneous tensor of degree `n` whose symmetrization has PBW degree below
`n` is zero. -/
private theorem eq_zero_of_mem_pbwFiltrationPrevious [Module.Free R L] {n : ℕ}
    {p : SymmetricAlgebra R L} (hp : p ∈ 𝒮 n) (h : e p ∈ pbwFiltrationPrevious R L n) :
    p = 0 := by
  have hsymb := he.mk_apply_eq_pbwHomogeneousComponentMap n ⟨p, hp⟩
  rw [(Submodule.Quotient.mk_eq_zero _).mpr (by
    simpa only [TauCeti.Algebra.wordFiltration.mem_previousRestricted_iff,
      pbwFiltrationPrevious_def] using h),
    ← map_zero (pbwHomogeneousComponentMap R L n)] at hsymb
  exact congrArg Subtype.val (pbwHomogeneousComponentMap_injective R L n hsymb).symm

/-- **Two-sided filtration of PBW symmetrization**: for `L` free over `R`, a symmetric tensor has
degree at most `k` exactly when its symmetrization has PBW degree at most `k`. -/
theorem mem_pbwFiltration_iff [Module.Free R L] {k : ℕ} {p : SymmetricAlgebra R L} :
    e p ∈ pbwFiltration R L k ↔ p ∈ F k := by
  refine ⟨fun h ↦ ?_, he.mem_pbwFiltration⟩
  have htop : ⨆ i, F i = ⊤ :=
    top_unique <| (iSup_homogeneousSubmodule_eq_top R L).symm.le.trans <|
      iSup_mono fun i ↦ TauCeti.Algebra.range_pow_le_wordFiltration _ i
  obtain ⟨N, hN⟩ := TauCeti.Algebra.exists_mem_wordFiltration_of_iSup_eq_top _ htop p
  -- Strip the homogeneous components of degree above `k`, from the top down.
  induction N generalizing p with
  | zero => exact TauCeti.Algebra.wordFiltration_mono _ (Nat.zero_le k) hN
  | succ N ih =>
    rcases le_or_gt (N + 1) k with hle | hlt
    · exact TauCeti.Algebra.wordFiltration_mono _ hle hN
    rw [TauCeti.Algebra.wordFiltration_succ_eq_sup, Submodule.mem_sup] at hN
    obtain ⟨q, hq, r, hr, rfl⟩ := hN
    have hr0 : r = 0 := by
      refine he.eq_zero_of_mem_pbwFiltrationPrevious hr ?_
      rw [pbwFiltrationPrevious_succ, show e r = e (q + r) - e q by simp]
      exact sub_mem (pbwFiltration_mono R L (by omega) h) (he.mem_pbwFiltration hq)
    subst hr0
    rw [add_zero] at h ⊢
    exact ih h hq

/-- **A PBW symmetrization is injective** when `L` is free over `R`. -/
theorem injective [Module.Free R L] : Function.Injective e := by
  refine (injective_iff_map_eq_zero e).mpr fun p hp ↦ ?_
  have h0 : p ∈ F 0 := he.mem_pbwFiltration_iff.mp (by rw [hp]; exact zero_mem _)
  rw [TauCeti.Algebra.wordFiltration_zero, ← pow_zero (LinearMap.range (SymmetricAlgebra.ι R L)),
    ← homogeneousSubmodule] at h0
  exact he.eq_zero_of_mem_pbwFiltrationPrevious h0 (by
    rw [hp, pbwFiltrationPrevious_zero]
    exact zero_mem _)

omit he in
/-- **The symmetrization of a Lie invariant is central, and conversely** for an injective PBW
symmetrization: `e p` commutes with `U(L)` exactly when `p ∈ Sym(L)^L`. Injectivity holds for free
`L` by `IsPBWSymmetrization.injective`. -/
theorem mem_center_iff (he : IsPBWSymmetrization R L e) (hinj : Function.Injective e)
    {p : SymmetricAlgebra R L} :
    e p ∈ Subalgebra.center R U ↔ p ∈ lieInvariants R L L := by
  rw [mem_center_iff_forall_lie_ι, mem_lieInvariants]
  refine forall_congr' fun x ↦ ?_
  rw [← lie_skew, neg_eq_zero, LieRing.of_associative_ring_bracket, ← he.map_lie,
    lie_eq_lieModuleDerivation, map_eq_zero_iff e hinj]

end IsPBWSymmetrization

end General

/-! ### The canonical symmetrization -/

section Canonical

variable (R : Type) (L : Type v) [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]

/-- The canonical global map `pbwSymmetrizationMap` is a PBW symmetrization. -/
theorem isPBWSymmetrization_pbwSymmetrizationMap :
    IsPBWSymmetrization R L (pbwSymmetrizationMap R L) :=
  ⟨pbwSymmetrizationMap_prod_ι R L⟩

variable {R L} in
/-- A linear map is a PBW symmetrization exactly when it is the canonical map. -/
theorem isPBWSymmetrization_iff_eq_pbwSymmetrizationMap
    {e : SymmetricAlgebra R L →ₗ[R] _root_.UniversalEnvelopingAlgebra R L} :
    IsPBWSymmetrization R L e ↔ e = pbwSymmetrizationMap R L :=
  ⟨fun he ↦ he.unique (isPBWSymmetrization_pbwSymmetrizationMap R L),
    fun he ↦ he ▸ isPBWSymmetrization_pbwSymmetrizationMap R L⟩

/-- **The canonical symmetrization is equivariant for the adjoint actions.** -/
theorem pbwSymmetrizationMap_lie (x : L) (p : SymmetricAlgebra R L) :
    pbwSymmetrizationMap R L ⁅x, p⁆ =
      _root_.UniversalEnvelopingAlgebra.ι R x * pbwSymmetrizationMap R L p -
        pbwSymmetrizationMap R L p * _root_.UniversalEnvelopingAlgebra.ι R x :=
  (isPBWSymmetrization_pbwSymmetrizationMap R L).map_lie x p

/-- **The symmetrization of an element of `Sym(L)` is central exactly when the element is a Lie
invariant**, for every Lie algebra over a commutative `ℚ`-algebra, free or not. -/
@[simp]
theorem pbwSymmetrizationMap_mem_center_iff {p : SymmetricAlgebra R L} :
    pbwSymmetrizationMap R L p ∈ Subalgebra.center R (_root_.UniversalEnvelopingAlgebra R L) ↔
      p ∈ lieInvariants R L L :=
  (isPBWSymmetrization_pbwSymmetrizationMap R L).mem_center_iff
    (pbwSymmetrizationMap_injective R L)

end Canonical

end TauCeti.UniversalEnvelopingAlgebra

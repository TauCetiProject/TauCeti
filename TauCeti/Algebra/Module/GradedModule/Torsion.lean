/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.RingTheory.Polynomial.Basic
public import TauCeti.Algebra.Module.GradedModule.HomogeneousPart
public import TauCeti.Algebra.Module.GradedModule.Polynomial
public import TauCeti.Algebra.Module.GradedModule.Quotient
import TauCeti.Algebra.Module.GradedModule.DirectSum

/-!
# Homogeneous torsion in graded polynomial modules

Suppose `M` is internally integer graded over a domain `k`, is torsion-free over `k`, and
multiplication by `X` strictly lowers degree. Then its `k[X]`-torsion submodule is precisely its
`X`-power torsion submodule, even for elements with several homogeneous components. This torsion
submodule is homogeneous, so it and its quotient inherit gradings through
`InternalGrading.submodule` and `InternalGrading.quotient`, after restricting scalars to `k`.
Over a field, finite generation gives a single power of `X` annihilating the entire torsion
submodule; the ambient module need not be torsion.

The primary-torsion equality supplies the hypothesis on the torsion submodule for Mathlib's
`Module.torsion_by_prime_power_decomposition`. The torsion submodule also admits a homogeneous
polynomial-linear complement. This file does not construct homogeneous cyclic generators or a
bigraded decomposition. Examples use the existing negative-degree polynomial grading and its
induced quotient grading on `k[X] / (X²)`.

## Main results

* `InternalGrading.torsion_eq_torsion'_powers_X`: polynomial torsion is `X`-power torsion.
* `InternalGrading.isHomogeneous_torsion`: every component of a torsion element is torsion.
* `InternalGrading.torsion_eq_torsionBy_X_pow`: for a finitely generated module over a field,
  its torsion submodule is the kernel of a single power of `X`.
* `InternalGrading.exists_isCompl_torsion_of_X_smul_mem_piece`: torsion has a homogeneous
  polynomial-linear complement.
-/

public section

noncomputable section

open Polynomial
open scoped DirectSum

namespace TauCeti.InternalGrading

variable {k M : Type*} [CommRing k] [IsDomain k] [AddCommGroup M]
  [Module k M] [Module k[X] M] [IsScalarTower k k[X] M] [Module.IsTorsionFree k M]
  {G : InternalGrading k M} {d : ℕ}

/-- If `X` strictly lowers degree in a module torsion-free over its coefficient domain, the
polynomial torsion submodule equals the submodule of elements killed by powers of `X`.
No homogeneity assumption on the elements is needed. -/
theorem torsion_eq_torsion'_powers_X (hd : d ≠ 0)
    (hX : ∀ ⦃p : ℤ⦄ ⦃x : M⦄, x ∈ G.piece p → (X : k[X]) • x ∈ G.piece (p - d)) :
    Submodule.torsion k[X] M = Submodule.torsion' k[X] M (Submonoid.powers (X : k[X])) := by
  ext x
  rw [Submodule.mem_torsion_iff, Submodule.mem_torsion'_iff]
  constructor
  · rintro ⟨⟨a, ha⟩, hax⟩
    obtain ⟨b, hab, hb⟩ := a.exists_eq_pow_rootMultiplicity_mul_and_not_dvd
      (nonZeroDivisors.ne_zero ha) 0
    simp only [C_0, sub_zero] at hab hb
    have hb0 : b.coeff 0 ≠ 0 := fun h ↦ hb (X_dvd_iff.mpr h)
    refine ⟨⟨X ^ a.rootMultiplicity 0, ⟨a.rootMultiplicity 0, rfl⟩⟩, ?_⟩
    apply smul_injective_of_coeff_zero_ne_zero hd hX hb0
    simp only [Submonoid.smul_def] at hax
    rw [hab, mul_smul, smul_comm] at hax
    simpa only [Submonoid.smul_def, smul_zero] using hax
  · rintro ⟨⟨_, n, rfl⟩, hx⟩
    exact ⟨⟨X ^ n, pow_mem X_mem_nonZeroDivisors n⟩, hx⟩

/-- The torsion submodule of a graded polynomial module is homogeneous if `X` strictly lowers
degree and the module is torsion-free over its coefficient domain. In particular its scalar
restriction is a valid input to the existing submodule and quotient grading constructors. -/
theorem isHomogeneous_torsion (hd : d ≠ 0)
    (hX : ∀ ⦃p : ℤ⦄ ⦃x : M⦄, x ∈ G.piece p → (X : k[X]) • x ∈ G.piece (p - d)) :
    DirectSum.SetLike.IsHomogeneous G.piece (Submodule.torsion k[X] M) := by
  intro p x hx
  rw [torsion_eq_torsion'_powers_X hd hX, Submodule.mem_torsion'_iff] at hx ⊢
  obtain ⟨⟨_, n, rfl⟩, hn⟩ := hx
  refine ⟨⟨X ^ n, ⟨n, rfl⟩⟩, ?_⟩
  have hf : LinearMap.IsHomogeneous (_root_.LinearMap.lsmul k[X] M (X ^ n))
      G.piece G.piece (-(n : ℤ) * d) := by
    apply LinearMap.isHomogeneous_def.mpr
    intro q y hy
    simpa only [neg_mul, sub_eq_add_neg, _root_.LinearMap.lsmul_apply] using
      X_pow_smul_mem_piece hX n hy
  rw [Submonoid.smul_def] at hn
  have key := hf.map_decompose p x
  simpa only [Submonoid.smul_def, _root_.LinearMap.lsmul_apply, hn,
    DirectSum.decompose_zero, DirectSum.zero_apply, ZeroMemClass.coe_zero] using key

end TauCeti.InternalGrading

namespace TauCeti.InternalGrading

variable {k M : Type*} [Field k] [AddCommGroup M]
  [Module k M] [Module k[X] M] [IsScalarTower k k[X] M] [Module.Finite k[X] M]
  {G : InternalGrading k M} {d : ℕ}

/-- Over a field, the torsion submodule of a finitely generated graded polynomial module is
annihilated by one power of `X`, and equals the kernel of that power. The module itself need not
be torsion. The exponent may be zero when the torsion submodule is zero. -/
theorem torsion_eq_torsionBy_X_pow (hd : d ≠ 0)
    (hX : ∀ ⦃p : ℤ⦄ ⦃x : M⦄, x ∈ G.piece p → (X : k[X]) • x ∈ G.piece (p - d)) :
    ∃ N : ℕ, Submodule.torsion k[X] M = Submodule.torsionBy k[X] M (X ^ N) := by
  classical
  let T := Submodule.torsion k[X] M
  have hT : Module.IsTorsion' T (Submonoid.powers (X : k[X])) := by
    intro x
    have hx : (x : M) ∈ Submodule.torsion k[X] M := x.2
    rw [torsion_eq_torsion'_powers_X hd hX, Submodule.mem_torsion'_iff] at hx
    obtain ⟨a, ha⟩ := hx
    exact ⟨a, Subtype.ext ha⟩
  -- Noetherianity of the polynomial ring makes the torsion submodule finitely generated.
  obtain ⟨r, s, hs⟩ := Module.Finite.exists_fin (R := k[X]) (M := T)
  obtain ⟨N, hN⟩ : ∃ N : ℕ, Module.IsTorsionBy k[X] T (X ^ N) := by
    by_cases hr : r = 0
    · subst r
      -- With no generators the torsion submodule is zero; exponent zero suffices.
      have hs0 : Submodule.span k[X] (Set.range s) = ⊥ := by simp
      have hbot : (⊥ : Submodule k[X] T) = ⊤ := hs0.symm.trans hs
      refine ⟨0, fun x ↦ ?_⟩
      have hx : x = 0 := (Submodule.mem_bot k[X]).mp (hbot.symm ▸ Submodule.mem_top)
      simp [hx]
    · obtain ⟨j, hj⟩ := Submodule.exists_isTorsionBy hT r hr s hs
      exact ⟨Submodule.pOrder hT (s j), hj⟩
  refine ⟨N, le_antisymm ?_ ?_⟩
  · intro x hx
    exact (Submodule.mem_torsionBy_iff _ x).mpr (congrArg Subtype.val (@hN ⟨x, hx⟩))
  · intro x hx
    exact (Submodule.mem_torsion_iff x).mpr
      ⟨⟨X ^ N, pow_mem X_mem_nonZeroDivisors N⟩, (Submodule.mem_torsionBy_iff _ x).mp hx⟩

/-- A finitely generated polynomial module over a field admits a homogeneous complement to
its torsion submodule when `X` strictly lowers degree. The complement is not canonical;
no homogeneous basis is assumed or asserted. -/
theorem exists_isCompl_torsion_of_X_smul_mem_piece (G : InternalGrading k M) (hd : d ≠ 0)
    (hX : ∀ ⦃p : ℤ⦄ ⦃x : M⦄, x ∈ G.piece p → (X : k[X]) • x ∈ G.piece (p - d)) :
    ∃ L : Submodule k[X] M, IsCompl (Submodule.torsion k[X] M) L ∧
      DirectSum.SetLike.IsHomogeneous G.piece L := by
  classical
  let T := Submodule.torsion k[X] M
  -- The same PID/projective lifting used in Mathlib's `Module.equiv_free_prod_directSum`
  -- supplies an ordinary section; taking a homogeneous part makes the retraction graded.
  obtain ⟨s, hs⟩ := Module.projective_lifting_property T.mkQ
    (_root_.LinearMap.id : (M ⧸ T) →ₗ[k[X]] (M ⧸ T)) T.mkQ_surjective
  let e : M →ₗ[k[X]] M := _root_.LinearMap.id - s.comp T.mkQ
  have heT (x : M) : e x ∈ T := by
    rw [← Submodule.Quotient.mk_eq_zero]
    have hsec := _root_.LinearMap.congr_fun hs (T.mkQ x)
    simpa [e, map_sub] using sub_eq_zero.mpr hsec.symm
  have hefix (x : T) : e x = x := by
    have hx0 : T.mkQ x = 0 := (Submodule.Quotient.mk_eq_zero T).mpr x.property
    simp [e, hx0]
  have hshift : ∀ ⦃p : ℤ⦄ ⦃x : M⦄,
      x ∈ G.piece p → (X : k[X]) • x ∈ G.piece (p + -(d : ℤ)) := by
    simpa only [sub_eq_add_neg] using hX
  let e₀ := G.homogeneousPart G hshift hshift e 0
  have hT := G.isHomogeneous_torsion hd hX
  have he₀T (x : M) : e₀ x ∈ T := by
    rw [← DirectSum.sum_support_decompose G.piece x, map_sum]
    apply T.sum_mem
    intro p hp
    rw [G.homogeneousPart_apply_of_mem G hshift hshift e 0
      (DirectSum.decompose G.piece x p).property, add_zero]
    exact hT p (heT _)
  let ρ := e₀.codRestrict T he₀T
  have hρ (x : T) : ρ x = x := by
    apply Subtype.ext
    -- Codomain restriction does not change the value; decompose the underlying element of T.
    dsimp only [ρ, _root_.LinearMap.codRestrict_apply]
    conv_lhs => rw [← DirectSum.sum_support_decompose G.piece (x : M)]
    rw [map_sum]
    conv_rhs => rw [← DirectSum.sum_support_decompose G.piece (x : M)]
    apply Finset.sum_congr rfl
    intro p hp
    rw [G.homogeneousPart_apply_of_mem G hshift hshift e 0
      (DirectSum.decompose G.piece (x : M) p).property, add_zero]
    rw [hefix ⟨_, hT p x.property⟩]
    exact DirectSum.decompose_of_mem_same G.piece
      (DirectSum.decompose G.piece (x : M) p).property
  refine ⟨_root_.LinearMap.ker e₀, ?_, G.isHomogeneous_homogeneousPart G
    hshift hshift e 0 |>.isHomogeneous_ker⟩
  rw [← e₀.ker_codRestrict T he₀T]
  exact _root_.LinearMap.isCompl_of_proj hρ

end TauCeti.InternalGrading

namespace TauCeti

section InducedGradings

variable {k M : Type*} [CommRing k] [IsDomain k] [AddCommGroup M]
  [Module k M] [Module k[X] M] [IsScalarTower k k[X] M] [Module.IsTorsionFree k M]
  (G : InternalGrading k M) {d : ℕ} (hd : d ≠ 0)
  (hX : ∀ ⦃p : ℤ⦄ ⦃x : M⦄, x ∈ G.piece p → (X : k[X]) • x ∈ G.piece (p - d))

-- Scalar restriction preserves membership, so the standard constructors suffice.
example : InternalGrading k ((Submodule.torsion k[X] M).restrictScalars k) :=
  G.submodule _ (G.isHomogeneous_torsion hd hX)

example : InternalGrading k (M ⧸ (Submodule.torsion k[X] M).restrictScalars k) :=
  G.quotient _ (G.isHomogeneous_torsion hd hX)

end InducedGradings

section Examples

variable (k : Type*) [Field k]

-- The free tower has zero torsion, and exponent zero is a valid uniform exponent.
example : Submodule.torsion k[X] k[X] = ⊥ ∧
    Submodule.torsion k[X] k[X] = Submodule.torsionBy k[X] k[X] (X ^ 0) := by
  constructor
  · exact Submodule.isTorsionFree_iff_torsion_eq_bot.mp inferInstance
  · simp [Submodule.isTorsionFree_iff_torsion_eq_bot.mp
      (inferInstance : Module.IsTorsionFree k[X] k[X])]

example : ∃ N : ℕ, Submodule.torsion k[X] k[X] =
    Submodule.torsionBy k[X] k[X] (X ^ N) :=
  (Polynomial.negDegreeGrading k).torsion_eq_torsionBy_X_pow one_ne_zero
    (fun _ _ hx ↦ Polynomial.X_smul_mem_negDegreeGrading_piece hx)

-- With zero torsion, the complement is the whole free tower.
example : ∃ L : Submodule k[X] k[X], IsCompl (Submodule.torsion k[X] k[X]) L ∧
    DirectSum.SetLike.IsHomogeneous (Polynomial.negDegreeGrading k).piece L :=
  (Polynomial.negDegreeGrading k).exists_isCompl_torsion_of_X_smul_mem_piece one_ne_zero
    (fun _ _ hx ↦ Polynomial.X_smul_mem_negDegreeGrading_piece hx)

local notation "Q" => k[X] ⧸ Submodule.span k[X] {(X ^ 2 : k[X])}

-- A positive-length torsion module with two distinct nonzero homogeneous classes.
-- Its grading is induced on the actual module quotient, not on an alternate representation.
private theorem quotient_X_sq_example : ∃ G : InternalGrading k Q,
    (∀ ⦃p : ℤ⦄ ⦃x⦄, x ∈ G.piece p → (X : k[X]) • x ∈ G.piece (p - 1)) ∧
    (Submodule.Quotient.mk (1 : k[X]) : Q) ∈ G.piece 0 ∧
    (Submodule.Quotient.mk (X : k[X]) : Q) ∈ G.piece (-1) ∧
    (Submodule.Quotient.mk (1 : k[X]) : Q) ≠ 0 ∧
    (Submodule.Quotient.mk (X : k[X]) : Q) ≠ 0 ∧
    (∀ x : Q, (X ^ 2 : k[X]) • x = 0) ∧
    (∃ N : ℕ, Submodule.torsion k[X] Q = Submodule.torsionBy k[X] Q (X ^ N)) := by
  let I : Submodule k[X] k[X] := Submodule.span k[X] {(X ^ 2 : k[X])}
  let H := Polynomial.negDegreeGrading k
  -- The ideal is the range of a homogeneous multiplication map.
  have hf : LinearMap.IsHomogeneous (_root_.LinearMap.toSpanSingleton k[X] k[X] (X ^ 2))
      H.piece H.piece (-2) := by
    apply LinearMap.isHomogeneous_def.mpr
    intro p x hx
    simpa only [_root_.LinearMap.toSpanSingleton_apply, smul_eq_mul, mul_comm,
      Nat.cast_ofNat, Nat.cast_one, one_mul, sub_eq_add_neg] using
      H.X_pow_smul_mem_piece (d := 1)
        (fun _ _ hx ↦ Polynomial.X_smul_mem_negDegreeGrading_piece hx) 2 hx
  have hI : DirectSum.SetLike.IsHomogeneous H.piece (I.restrictScalars k) := by
    intro p y hy
    rw [Submodule.restrictScalars_mem] at hy ⊢
    have hr := hf.isHomogeneous_range
    rw [_root_.LinearMap.range_toSpanSingleton] at hr
    exact hr p hy
  -- Transport the standard quotient grading along the scalar-restriction equivalence.
  let e := Submodule.Quotient.restrictScalarsEquiv k I
  let G := (H.quotient (I.restrictScalars k) hI).map e
  have hmem (p : ℤ) (x : k[X]) (hx : x ∈ H.piece p) :
      (Submodule.Quotient.mk x : k[X] ⧸ I) ∈ G.piece p := by
    rw [InternalGrading.mem_map_piece_iff, Submodule.Quotient.restrictScalarsEquiv_symm_mk]
    exact H.mk_mem_quotient_piece _ hI hx
  have hX : ∀ ⦃p : ℤ⦄ ⦃x : k[X] ⧸ I⦄,
      x ∈ G.piece p → (X : k[X]) • x ∈ G.piece (p - 1) := by
    intro p x hx
    rw [InternalGrading.mem_map_piece_iff, InternalGrading.mem_quotient_piece_iff] at hx
    obtain ⟨y, hy, hxy⟩ := hx
    have heq : (Submodule.Quotient.mk y : k[X] ⧸ I) = x := by
      simpa only [e, Submodule.Quotient.restrictScalarsEquiv_mk,
        LinearEquiv.apply_symm_apply] using congrArg e hxy
    rw [← heq, ← Submodule.Quotient.mk_smul]
    exact hmem _ _ (Polynomial.X_smul_mem_negDegreeGrading_piece hy)
  -- The two classes survive in distinct degrees, and multiplication by X² is zero.
  refine ⟨G, hX, hmem 0 1 ?_, hmem (-1) X ?_, ?_, ?_, ?_,
    G.torsion_eq_torsionBy_X_pow one_ne_zero hX⟩
  · simpa only [pow_zero, Nat.cast_zero, neg_zero] using
      Polynomial.X_pow_mem_negDegreeGrading_piece (k := k) 0
  · simpa only [pow_one, Nat.cast_one] using
      Polynomial.X_pow_mem_negDegreeGrading_piece (k := k) 1
  · intro h
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp ((Submodule.Quotient.mk_eq_zero I).mp h)
    have hc := congrArg (fun f : k[X] ↦ f.coeff 0) ha
    simp [smul_eq_mul] at hc
  · intro h
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp ((Submodule.Quotient.mk_eq_zero I).mp h)
    have hc := congrArg (fun f : k[X] ↦ f.coeff 1) ha
    simp [smul_eq_mul, coeff_mul_X_pow'] at hc
  · intro x
    induction x using Submodule.Quotient.induction_on with
    | _ y =>
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      simpa only [smul_eq_mul, mul_comm] using
        I.smul_mem y (Submodule.mem_span_singleton_self (X ^ 2 : k[X]))

-- Every element of k[X]/(X²) is torsion; the theorem still constructs the homogeneous splitting.
example : ∃ (G : InternalGrading k Q) (L : Submodule k[X] Q),
    Submodule.torsion k[X] Q = ⊤ ∧ IsCompl (Submodule.torsion k[X] Q) L ∧
      DirectSum.SetLike.IsHomogeneous G.piece L := by
  obtain ⟨G, hX, _, _, _, _, hann, _⟩ := quotient_X_sq_example k
  obtain ⟨L, hL, hhom⟩ := G.exists_isCompl_torsion_of_X_smul_mem_piece one_ne_zero hX
  refine ⟨G, L, eq_top_iff.mpr ?_, hL, hhom⟩
  intro x hx
  exact (Submodule.mem_torsion_iff x).mpr
    ⟨⟨X ^ 2, pow_mem X_mem_nonZeroDivisors 2⟩, hann x⟩

-- A two-term external direct sum is a free-plus-torsion module. Keep its bookkeeping local
-- to the examples rather than adding another public grading construction.
private abbrev mixedSummand (i : Bool) := if i then Q else k[X]

private instance (i : Bool) : AddCommGroup (mixedSummand k i) := by
  cases i <;> dsimp [mixedSummand] <;> infer_instance

private instance (i : Bool) : Module k (mixedSummand k i) := by
  cases i <;> dsimp [mixedSummand] <;> infer_instance

private instance (i : Bool) : Module k[X] (mixedSummand k i) := by
  cases i <;> dsimp [mixedSummand] <;> infer_instance

private instance (i : Bool) : IsScalarTower k k[X] (mixedSummand k i) := by
  cases i <;> dsimp [mixedSummand] <;> infer_instance

private instance (i : Bool) : Module.Finite k[X] (mixedSummand k i) := by
  cases i <;> dsimp [mixedSummand] <;> infer_instance

example : ∃ (G : InternalGrading k (⨁ i : Bool, mixedSummand k i))
    (L : Submodule k[X] (⨁ i : Bool, mixedSummand k i)),
    IsCompl (Submodule.torsion k[X] (⨁ i : Bool, mixedSummand k i)) L ∧
      DirectSum.SetLike.IsHomogeneous G.piece L ∧
      Submodule.torsion k[X] (⨁ i : Bool, mixedSummand k i) ≠ ⊥ ∧
      Submodule.torsion k[X] (⨁ i : Bool, mixedSummand k i) ≠ ⊤ := by
  classical
  obtain ⟨H, hHX, _, _, h1, _, hann, _⟩ := quotient_X_sq_example k
  let J : ∀ i : Bool, InternalGrading k (mixedSummand k i) := fun i ↦
    match i with
    | false => Polynomial.negDegreeGrading k
    | true => H
  let G := InternalGrading.directSum J
  have hX : ∀ ⦃p : ℤ⦄ ⦃x⦄, x ∈ G.piece p → (X : k[X]) • x ∈ G.piece (p - 1) := by
    intro p x hx
    rw [InternalGrading.directSum_piece, InternalGrading.mem_directSumPiece_iff] at hx ⊢
    intro i
    rw [DirectSum.smul_apply]
    cases i with
    | false => exact Polynomial.X_smul_mem_negDegreeGrading_piece (hx false)
    | true => exact hHX (hx true)
  let : Module.Finite k[X] (⨁ i : Bool, mixedSummand k i) :=
    Module.Finite.equiv (DirectSum.linearEquivFunOnFintype k[X] Bool (mixedSummand k)).symm
  obtain ⟨L, hL, hhom⟩ := G.exists_isCompl_torsion_of_X_smul_mem_piece one_ne_zero hX
  refine ⟨G, L, hL, hhom, ?_, ?_⟩
  · intro hbot
    let t := DirectSum.lof k[X] Bool (mixedSummand k) true
      (Submodule.Quotient.mk (1 : k[X]) : Q)
    have ht : t ∈ Submodule.torsion k[X] (⨁ i : Bool, mixedSummand k i) := by
      apply (Submodule.mem_torsion_iff t).mpr
      refine ⟨⟨X ^ 2, pow_mem X_mem_nonZeroDivisors 2⟩, ?_⟩
      rw [Submonoid.smul_def, ← map_smul, hann, map_zero]
    have ht0 := (Submodule.mem_bot k[X]).mp (hbot ▸ ht)
    have := congrArg (fun z ↦ z true) ht0
    exact h1 (by simpa [t, DirectSum.lof_apply] using this)
  · intro htop
    let f := DirectSum.lof k[X] Bool (mixedSummand k) false (1 : k[X])
    have hf : f ∈ Submodule.torsion k[X] (⨁ i : Bool, mixedSummand k i) :=
      htop.symm ▸ Submodule.mem_top
    obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff f).mp hf
    have ha0 := congrArg (fun z ↦ z false) ha
    have : (a : k[X]) = 0 := by
      simpa only [f, DirectSum.smul_apply, DirectSum.lof_apply, Submonoid.smul_def,
        smul_eq_mul, mul_one, DirectSum.zero_apply] using ha0
    exact nonZeroDivisors.ne_zero a.property this

end Examples

end TauCeti

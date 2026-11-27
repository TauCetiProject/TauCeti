/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.DoubleCoset
public import Mathlib.RingTheory.RamificationInertia.Ramification
public import TauCeti.Algebra.Module.Lattice.BaseChange
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Basic
import Mathlib.Data.Fin.Tuple.Sort
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Basis
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Cartan.DiscreteValuationRing
import TauCeti.RingTheory.RamificationInertia.DiscreteValuationRing

/-!
# Elementary divisors of two full lattices

Let `R` be a discrete valuation ring with fraction field `K`. Two full lattices `L` and `M`
in a `K`-vector space have a relative position given by a multiset of integers. For every
uniformizer `t`, there is a basis `b` of `L` and an integer vector `a` such that the vectors
`t ^ (a i) • b i` form a basis of `M`. A negative exponent allows `M` to extend outside `L`.

`Submodule.latticeElementaryDivisors` is the multiset of these exponents. It determines
the relative position without choosing a uniformizer or keeping particular bases. Swapping
the lattices negates the exponents. Scalar extension multiplies them by the ramification index.

The construction uses `TauCeti.existsUnique_monotone_mem_doubleCoset_diagGL_zpow`, the
Cartan decomposition for the change-of-basis matrix. The bilattice convention follows
S. Howe and C. Klevdal, *Admissible pairs and p-adic Hodge structures I*, §§3.1–3.2,
<https://arxiv.org/abs/2308.11065>.
-/

public section

open Matrix Module DoubleCoset TauCeti

namespace Module.Basis

variable {R K V ι : Type*} [CommRing R] [CommRing K] [Algebra R K]
  [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
  {L M : Submodule R V} [L.IsFullLattice K] [M.IsFullLattice K]

variable [Fintype ι] [DecidableEq ι]

/-- The transition matrix between full lattice bases lies in the integral double coset of
`diag(d)` precisely when independent integral basis changes make the second basis `d` times
the first, vector by vector. -/
theorem mem_doubleCoset_diagGL_iff (b : Basis ι R L) (c : Basis ι R M)
    {g : GL ι K} (hg : (g : Matrix ι ι K) =
      (b.extendOfIsFullLattice K).toMatrix (c.extendOfIsFullLattice K)) (d : ι → Kˣ) :
    g ∈ doubleCoset (diagGL d) (GeneralLinearGroup.map (n := ι) (algebraMap R K)).range
        (GeneralLinearGroup.map (n := ι) (algebraMap R K)).range ↔
      ∃ (b' : Basis ι R L) (c' : Basis ι R M), ∀ i, (c' i : V) = d i • (b' i : V) := by
  let φ := GeneralLinearGroup.map (n := ι) (algebraMap R K)
  constructor
  · intro h
    obtain ⟨_, ⟨p, rfl⟩, _, ⟨q, rfl⟩, h⟩ := mem_doubleCoset.mp h
    -- Realize the two integral factors as basis changes on their respective lattices.
    have lift (N : Submodule R V) [N.IsFullLattice K] (x : Basis ι R N) (u : GL ι R) :
        ∃ y : Basis ι R N, (x.extendOfIsFullLattice K).toMatrix (y.extendOfIsFullLattice K) =
          (φ u : Matrix ι ι K) := by
      obtain ⟨e, rfl⟩ := x.toGL.surjective u
      exact ⟨x.map e, by ext; simp [φ, Basis.toMatrix_apply, LinearMap.toMatrix_apply]⟩
    obtain ⟨b', hb'⟩ := lift L b p
    obtain ⟨c', hc'⟩ := lift M c q⁻¹
    have hmul : g * φ q⁻¹ = φ p * diagGL d := by simp [h, φ, mul_assoc]
    have heq : (c'.extendOfIsFullLattice K : ι → V) =
        (b'.extendOfIsFullLattice K).unitsSMul d := by
      apply (b.extendOfIsFullLattice K).toMatrixEquiv.injective
      calc
        (b.extendOfIsFullLattice K).toMatrix (c'.extendOfIsFullLattice K)
            = (g : Matrix ι ι K) * (φ q⁻¹ : GL ι K) := by
          rw [hg, ← hc', toMatrix_mul_toMatrix]
        _ = (φ p : GL ι K) * (diagGL d : Matrix ι ι K) := congrArg Units.val hmul
        _ = (b.extendOfIsFullLattice K).toMatrix ((b'.extendOfIsFullLattice K).unitsSMul d) := by
          rw [← hb', ← toMatrix_mul_toMatrix _ (b'.extendOfIsFullLattice K)
            ((b'.extendOfIsFullLattice K).unitsSMul d), toMatrix_unitsSMul, diagGL_coe,
            Function.comp_def]
    exact ⟨b', c', fun i ↦ by simpa [unitsSMul_apply] using congrFun heq i⟩
  · rintro ⟨b', c', hd⟩
    let := b.invertibleToMatrix b'
    let := c'.invertibleToMatrix c
    let p := unitOfInvertible (b.toMatrix b')
    let q := unitOfInvertible (c'.toMatrix c)
    refine mem_doubleCoset.mpr ⟨_, ⟨p, rfl⟩, _, ⟨q, rfl⟩, Units.ext ?_⟩
    have heq : (c'.extendOfIsFullLattice K : ι → V) =
        (b'.extendOfIsFullLattice K).unitsSMul d :=
      funext fun i ↦ by simpa [unitsSMul_apply] using hd i
    rw [hg, ← toMatrix_mul_toMatrix _ (c'.extendOfIsFullLattice K),
      ← toMatrix_mul_toMatrix _ (b'.extendOfIsFullLattice K) (c'.extendOfIsFullLattice K),
      toMatrix_extendOfIsFullLattice, toMatrix_extendOfIsFullLattice, heq, toMatrix_unitsSMul]
    simp only [Units.val_mul, GeneralLinearGroup.val_map_apply, diagGL_coe, Function.comp_def,
      p, q, unitOfInvertible]

end Module.Basis

namespace Submodule

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  {V : Type*} [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
  (L M : Submodule R V) [L.IsFullLattice K] [M.IsFullLattice K]

/-- For a fixed uniformizer, there is exactly one nondecreasing exponent vector relating
a basis of the first full lattice to a basis of the second. -/
theorem existsUnique_monotone_basis_zpow_smul {t : R} (ht : Irreducible t) :
    ∃! a : Fin (finrank K V) → ℤ, Monotone a ∧
      ∃ (b : Basis _ R L) (c : Basis _ R M),
        ∀ i, (c i : V) = algebraMap R K t ^ a i • (b i : V) := by
  let latticeBasis (N : Submodule R V) [N.IsFullLattice K] : Basis (Fin (finrank K V)) R N :=
    have := IsLattice.free K N
    have := IsLattice.finite K N
    finBasisOfFinrankEq R N (IsFullLattice.finrank_eq K N)
  let b := latticeBasis L
  let c := latticeBasis M
  let B := b.extendOfIsFullLattice K
  let C := c.extendOfIsFullLattice K
  let := B.invertibleToMatrix C
  let g := unitOfInvertible (B.toMatrix C)
  let π := Units.mk0 (algebraMap R K t)
    ((map_ne_zero_iff _ (IsFractionRing.injective R K)).2 ht.ne_zero)
  have h := existsUnique_monotone_mem_doubleCoset_diagGL_zpow ht (π := π) rfl g
  simpa only [b.mem_doubleCoset_diagGL_iff c (g := g) rfl, Units.smul_def,
    Units.val_zpow_eq_zpow_val, Units.val_mk0, π] using h

private theorem exists_monotone_basis_zpow_smul_forall_irreducible :
    ∃ a : Fin (finrank K V) → ℤ, Monotone a ∧ ∀ t : R, Irreducible t →
      ∃ (b : Basis _ R L) (c : Basis _ R M),
        ∀ i, (c i : V) = algebraMap R K t ^ a i • (b i : V) := by
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨a, ha, b, c, h⟩ := (existsUnique_monotone_basis_zpow_smul (K := K) L M ht).exists
  refine ⟨a, ha, fun s hs ↦ ?_⟩
  obtain ⟨u, hu⟩ := IsDiscreteValuationRing.associated_of_irreducible R ht hs
  have hsK : algebraMap R K s = algebraMap R K u * algebraMap R K t := by
    rw [mul_comm, ← map_mul, hu]
  -- A unit change in the uniformizer can be absorbed into the second integral basis.
  refine ⟨b, c.unitsSMul (fun i ↦ u ^ a i), fun i ↦ ?_⟩
  simp only [Basis.unitsSMul_apply, Units.smul_def, Submodule.coe_smul, h]
  rw [← algebraMap_smul K, hsK, ← MonoidHom.coe_ofClass (algebraMap R K), ← Units.coe_map]
  simp only [map_zpow, Units.val_zpow_eq_zpow_val, Units.coe_map, MonoidHom.coe_ofClass,
    mul_zpow, mul_smul]

variable (K) in
/-- The multiset of integers `aᵢ` for which the second lattice has basis `t ^ aᵢ • bᵢ`,
where `b` is a basis of the first lattice and `t` is any uniformizer. -/
noncomputable def latticeElementaryDivisors : Multiset ℤ :=
  Finset.univ.val.map (exists_monotone_basis_zpow_smul_forall_irreducible (K := K) L M).choose

/-- Every uniformizer realizes the elementary divisors on a pair of adapted bases,
with exponents in nondecreasing order. -/
theorem exists_basis_latticeElementaryDivisors {t : R} (ht : Irreducible t) :
    ∃ (a : Fin (finrank K V) → ℤ) (b : Basis _ R L) (c : Basis _ R M),
      Monotone a ∧ L.latticeElementaryDivisors K M = Finset.univ.val.map a ∧
        ∀ i, (c i : V) = algebraMap R K t ^ a i • (b i : V) := by
  obtain ⟨ha, h⟩ := (exists_monotone_basis_zpow_smul_forall_irreducible (K := K) L M).choose_spec
  obtain ⟨b, c, hbc⟩ := h t ht
  exact ⟨_, b, c, ha, rfl, hbc⟩

/-- Any pair of adapted bases computes the same elementary divisors, in any order. -/
theorem latticeElementaryDivisors_eq_of_basis {ι : Type*} [Fintype ι] {t : R}
    (ht : Irreducible t) (b : Basis ι R L) (c : Basis ι R M) (a : ι → ℤ)
    (h : ∀ i, (c i : V) = algebraMap R K t ^ a i • (b i : V)) :
    L.latticeElementaryDivisors K M = Finset.univ.val.map a := by
  classical
  let e : Fin (finrank K V) ≃ ι := Fintype.equivOfCardEq (by
    rw [Fintype.card_fin, ← Module.finrank_eq_card_basis (b.extendOfIsFullLattice K)])
  -- Sort the proposed exponents to invoke uniqueness, then forget the permutation.
  let σ := (Tuple.sort (a ∘ e)).trans e
  obtain ⟨a₀, b₀, c₀, ha₀, hD, h₀⟩ := L.exists_basis_latticeElementaryDivisors M ht (K := K)
  have heq : a₀ = a ∘ σ := (existsUnique_monotone_basis_zpow_smul (K := K) L M ht).unique
    ⟨ha₀, b₀, c₀, h₀⟩ ⟨Tuple.monotone_sort (a ∘ e),
      b.reindex σ.symm, c.reindex σ.symm, fun i ↦ by simpa using h (σ i)⟩
  rw [hD, heq, ← Multiset.map_map, Multiset.map_univ_val_equiv]

/-- Each basis vector contributes one elementary divisor, counted with multiplicity. -/
@[simp]
theorem card_latticeElementaryDivisors :
    (L.latticeElementaryDivisors K M).card = finrank K V := by
  simp [latticeElementaryDivisors]

/-- A lattice compared with itself has one zero exponent per dimension. -/
@[simp]
theorem latticeElementaryDivisors_self :
    L.latticeElementaryDivisors K L = Multiset.replicate (finrank K V) 0 := by
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨b, _⟩ := IsLattice.exists_basis_linearIndependent K L
  rw [L.latticeElementaryDivisors_eq_of_basis L ht b b (fun _ ↦ 0) (fun i ↦ by simp)]
  simp [IsFullLattice.finrank_eq K L]

/-- All elementary divisors are zero exactly when the two lattices coincide. -/
@[simp]
theorem latticeElementaryDivisors_eq_replicate_zero_iff :
    L.latticeElementaryDivisors K M = Multiset.replicate (finrank K V) 0 ↔ L = M := by
  refine ⟨fun he ↦ ?_, ?_⟩
  swap
  · rintro rfl
    exact L.latticeElementaryDivisors_self
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨a, b, c, _, hD, h⟩ := L.exists_basis_latticeElementaryDivisors M ht (K := K)
  have ha (i) : a i = 0 := by
    apply Multiset.eq_of_mem_replicate
    rw [← he, hD]
    exact Multiset.mem_map.mpr ⟨i, Finset.mem_univ_val _, rfl⟩
  have hbc : (c.extendOfIsFullLattice K : _ → V) = b.extendOfIsFullLattice K := by
    funext i
    simpa [ha] using h i
  simpa only [Basis.span_range_extendOfIsFullLattice] using
    congrArg (fun v ↦ span R (Set.range v)) hbc.symm

/-- Exchanging the lattices negates all elementary divisors. -/
theorem latticeElementaryDivisors_swap :
    M.latticeElementaryDivisors K L = (L.latticeElementaryDivisors K M).map Neg.neg := by
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨a, b, c, _, hD, h⟩ := L.exists_basis_latticeElementaryDivisors M ht (K := K)
  rw [M.latticeElementaryDivisors_eq_of_basis L ht c b (fun i ↦ -a i) ?_, hD, Multiset.map_map]
  · rfl
  · intro i
    rw [h, smul_smul, _root_.zpow_neg]
    rw [inv_mul_cancel₀ (zpow_ne_zero _ ((map_ne_zero_iff _ (IsFractionRing.injective R K)).2
      ht.ne_zero)), one_smul]

variable {W : Type*} [AddCommGroup W] [Module R W] [Module K W] [IsScalarTower R K W]

/-- Transporting both lattices by the same linear equivalence preserves their type. -/
@[simp]
theorem latticeElementaryDivisors_map (f : V ≃ₗ[K] W) :
    letI := isFullLattice_map L f.toLinearMap f.surjective
    letI := isFullLattice_map M f.toLinearMap f.surjective
    (L.map (f.toLinearMap.restrictScalars R)).latticeElementaryDivisors K
      (M.map (f.toLinearMap.restrictScalars R)) = L.latticeElementaryDivisors K M := by
  have := isFullLattice_map L f.toLinearMap f.surjective
  have := isFullLattice_map M f.toLinearMap f.surjective
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨a, b, c, _, hD, h⟩ := L.exists_basis_latticeElementaryDivisors M ht (K := K)
  rw [hD]
  apply latticeElementaryDivisors_eq_of_basis (L.map (f.toLinearMap.restrictScalars R))
    (M.map (f.toLinearMap.restrictScalars R)) ht
    (b.map ((f.restrictScalars R).submoduleMap L))
    (c.map ((f.restrictScalars R).submoduleMap M))
  intro i
  exact (congrArg f (h i)).trans (f.map_smul _ _)

end Submodule

namespace Submodule

variable {R S K F V W : Type*}
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Field K] [Field F] [Algebra R K] [IsFractionRing R K] [Algebra S F] [IsFractionRing S F]
  [Algebra R S] [IsLocalHom (algebraMap R S)] [Algebra K F] [Algebra R F]
  [IsScalarTower R K F] [IsScalarTower R S F]
  [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
  [AddCommGroup W] [Module R W] [Module K W] [Module S W] [Module F W]
  [IsScalarTower R K W] [IsScalarTower R S W] [IsScalarTower K F W] [IsScalarTower S F W]
  {f : V →ₗ[K] W}

/-- Under a local extension of DVRs of ramification index `e`, extending both lattices
multiplies each elementary divisor by `e`. -/
theorem latticeElementaryDivisors_span_image (L M : Submodule R V)
    [L.IsFullLattice K] [M.IsFullLattice K] (hf : IsBaseChange F f) :
    letI := hf.isFullLattice_span_image (S := S) L
    letI := hf.isFullLattice_span_image (S := S) M
    (span S (f '' (L : Set V))).latticeElementaryDivisors F (span S (f '' (M : Set V))) =
      (L.latticeElementaryDivisors K M).map
        (fun n ↦ ((IsLocalRing.maximalIdeal S).ramificationIdx R : ℤ) * n) := by
  have := hf.isFullLattice_span_image (S := S) L
  have := hf.isFullLattice_span_image (S := S) M
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨s, hs⟩ := IsDiscreteValuationRing.exists_irreducible S
  obtain ⟨a, b, c, _, hD, h⟩ := L.exists_basis_latticeElementaryDivisors M ht (K := K)
  let e := (IsLocalRing.maximalIdeal S).ramificationIdx R
  have ht' : algebraMap R S t ≠ 0 := by
    intro hz
    have htF := congrArg (algebraMap S F) hz
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R K F, map_zero,
      map_eq_zero] at htF
    exact ((map_ne_zero_iff _ (IsFractionRing.injective R K)).2 ht.ne_zero) htF
  obtain ⟨u, hu⟩ := TauCeti.IsDiscreteValuationRing.exists_unit_mul_pow_ramificationIdx ht ht' hs
  have hF : algebraMap K F (algebraMap R K t) =
      algebraMap S F (u : S) * algebraMap S F s ^ e := by
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R S F, hu,
      map_mul, map_pow]
  -- The unit in the image of the old uniformizer acts on the first extended lattice basis.
  have hpow (n : ℤ) : algebraMap K F (algebraMap R K t ^ n) =
      algebraMap S F s ^ ((e : ℤ) * n) * algebraMap S F ↑(u ^ n) := by
    rw [← MonoidHom.coe_ofClass (algebraMap S F), ← Units.coe_map]
    simp only [map_zpow₀, hF, mul_zpow, map_zpow, Units.val_zpow_eq_zpow_val, Units.coe_map,
      MonoidHom.coe_ofClass, _root_.zpow_mul, zpow_natCast]
    rw [mul_comm]
  rw [hD, Multiset.map_map]
  apply (span S (f '' (L : Set V))).latticeElementaryDivisors_eq_of_basis _ hs
    ((b.baseChangeOfIsFullLattice hf).unitsSMul (fun i ↦ u ^ a i))
    (c.baseChangeOfIsFullLattice hf)
  intro i
  simp only [Function.comp_apply, Basis.unitsSMul_apply, Units.smul_def, Submodule.coe_smul,
    Basis.baseChangeOfIsFullLattice_apply, h, map_smul]
  rw [← algebraMap_smul F (R := K), hpow, mul_smul, algebraMap_smul]

end Submodule

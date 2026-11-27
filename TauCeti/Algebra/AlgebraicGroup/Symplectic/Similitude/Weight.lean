/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralSpin.RootDatum
public import TauCeti.LinearAlgebra.RootSystem.Chamber
public import TauCeti.LinearAlgebra.RootSystem.Dominance

/-!
# The integral weight lattice of the symplectic similitude group

The diagonal torus of `GSp₂g` consists of the matrices `diag(z₁, …, z_g, t/z₁, …, t/z_g)`, whose
multiplier `t` is a coordinate independent of the `zᵢ`. Its character lattice is therefore
`X_g = ℤ × ℤ^g` (`TauCeti.SymplecticSimilitude.Weight`), where `(m, u)` stands for the monomial
`t^m z₁^u₁ ⋯ z_g^u_g`. This is the lattice in which characters of algebraic representations of
`GSp₂g` are written as Laurent polynomials.

This file records the arithmetic of this lattice:

* the multiplier weight `e_t = (1, 0)`, the standard weights `eᵢ = (0, δᵢ)` and their paired
  weights `e_t - eᵢ`, the torus weights of the two basis vectors of the `i`-th hyperbolic pair;
* the central degree `d(m, u) = 2m + ∑ uᵢ`: a scalar matrix `c • 1` has torus coordinates
  `zᵢ = c` and `t = c²`, so it acts on the weight `(m, u)` by `c ^ d(m, u)`. The exponent of the
  multiplier and the scalar degree must be distinguished;
* the dominant weights, `u₁ ≥ ⋯ ≥ u_g ≥ 0` with an unrestricted integer `m`;
* the pullback `(m, u) ↦ (u, 2m + ∑ uᵢ)` along the central cover `Sp₂g × 𝔾_m → GSp₂g`,
  `(a, c) ↦ c • a`, which is injective with image the pairs `(u, d)` with `d ≡ ∑ uᵢ` modulo `2`;
* the simple roots `eᵢ - eᵢ₊₁` and `2e_g - e_t`, the simple coroots and the root order.

The roots, coroots and root order are not built anew: they are those of the based root datum
`TauCeti.gspRootDatum`, `TauCeti.gspBase` of `GSp₂g`, which lives on the lattice
`(ULift (Fin g) →₀ ℤ) × ℤ` with the multiplier as last coordinate. The equivalence
`TauCeti.SymplecticSimilitude.toGspCharacterLattice` transports them to `X_g`.

## Main declarations

* `TauCeti.SymplecticSimilitude.Weight`: the lattice `X_g = ℤ × (Fin g → ℤ)`.
* `TauCeti.SymplecticSimilitude.multiplierWeight`, `TauCeti.SymplecticSimilitude.standardWeight`
  and `TauCeti.SymplecticSimilitude.pairedWeight`: the weights `e_t`, `eᵢ` and `e_t - eᵢ`.
* `TauCeti.SymplecticSimilitude.centralDegree`: the homomorphism `d(m, u) = 2m + ∑ uᵢ`.
* `TauCeti.SymplecticSimilitude.dominantWeights`: the monoid of dominant weights.
* `TauCeti.SymplecticSimilitude.coverPullback`: the pullback along the central cover, with
  `TauCeti.SymplecticSimilitude.coverPullback_eq_iff` describing its fibres: it is injective, its
  image is cut out by a parity condition, and its inverse recovers `m = (d - ∑ uᵢ) / 2`.
* `TauCeti.SymplecticSimilitude.toGspCharacterLattice`: the comparison with the lattice of
  `TauCeti.gspRootDatum`.
* `TauCeti.SymplecticSimilitude.simpleRoot`: the simple roots `eᵢ - eᵢ₊₁` and `2e_g - e_t`.
* `TauCeti.SymplecticSimilitude.mem_dominantWeights_iff_mem_dominantChamber`: the dominant
  weights are the dominant chamber of `TauCeti.gspBase`, cut out by the simple coroots
  `(m, u) ↦ uᵢ - uᵢ₊₁` and `(m, u) ↦ u_g`.
* `TauCeti.SymplecticSimilitude.rootLE`: the root order, with
  `TauCeti.SymplecticSimilitude.rootLE_iff_exists_nat` (a natural combination of simple roots),
  reflexivity, transitivity, antisymmetry and
  `TauCeti.SymplecticSimilitude.centralDegree_eq_of_rootLE`: comparable weights have the same
  central degree.

## References

* H. Yu, *Number of irreducible ℓ-adic local systems on a curve*, arXiv:1807.04659v5, §7.1,
  equation (7.1.1) and Remark 7.1.1.
* J. S. Milne, *Algebraic Groups* (2017), Chapter 21 §j (Summary 21.98, the type `C` root datum)
  and Chapter 22 §a (the root order, Theorem 22.2 and complements 22.3–22.6).
-/

public section

open Function

namespace TauCeti.SymplecticSimilitude

/-- **The weight lattice of the diagonal torus of `GSp₂g`**: `X_g = ℤ × ℤ^g`, where `(m, u)`
denotes the character `t^m z₁^u₁ ⋯ z_g^u_g` of `diag(z₁, …, z_g, t/z₁, …, t/z_g)`. -/
abbrev Weight (g : ℕ) := ℤ × (Fin g → ℤ)

variable {g : ℕ}

/-! ### Distinguished weights and the central degree -/

/-- The multiplier weight `e_t = (1, 0)`, the character `t`. -/
def multiplierWeight (g : ℕ) : Weight g := (1, 0)

/-- The standard weight `eᵢ = (0, δᵢ)`, the character `zᵢ`: the torus weight of the first basis
vector of the `i`-th hyperbolic pair of the standard representation. -/
def standardWeight (i : Fin g) : Weight g := (0, Pi.single i 1)

/-- The paired weight `e_t - eᵢ`, the character `t/zᵢ`: the torus weight of the second basis
vector of the `i`-th hyperbolic pair of the standard representation. -/
def pairedWeight (i : Fin g) : Weight g := multiplierWeight g - standardWeight i

@[simp]
theorem multiplierWeight_fst : (multiplierWeight g).1 = 1 := (rfl)

@[simp]
theorem multiplierWeight_snd : (multiplierWeight g).2 = 0 := (rfl)

@[simp]
theorem standardWeight_fst (i : Fin g) : (standardWeight i).1 = 0 := (rfl)

@[simp]
theorem standardWeight_snd (i : Fin g) : (standardWeight i).2 = Pi.single i 1 := (rfl)

@[simp]
theorem pairedWeight_fst (i : Fin g) : (pairedWeight i).1 = 1 := by
  simp [pairedWeight]

@[simp]
theorem pairedWeight_snd (i : Fin g) : (pairedWeight i).2 = -Pi.single i 1 := by
  simp [pairedWeight]

/-- The standard weight and its paired weight add up to the multiplier weight: `zᵢ · (t/zᵢ) = t`.
-/
@[simp]
theorem standardWeight_add_pairedWeight (i : Fin g) :
    standardWeight i + pairedWeight i = multiplierWeight g := by
  simp [pairedWeight]

/-- **The central degree** `d(m, u) = 2m + ∑ uᵢ`. The scalar matrix `c • 1` has torus coordinates
`t = c²` and `zᵢ = c`, so it acts on the weight `(m, u)` by `c ^ d(m, u)`. -/
def centralDegree (g : ℕ) : Weight g →+ ℤ where
  toFun wt := 2 * wt.1 + ∑ i, wt.2 i
  map_zero' := by simp
  map_add' a b := by
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, Finset.sum_add_distrib]
    ring

theorem centralDegree_apply (wt : Weight g) : centralDegree g wt = 2 * wt.1 + ∑ i, wt.2 i := (rfl)

/-- The multiplier `t` has central degree `2`. -/
@[simp]
theorem centralDegree_multiplierWeight : centralDegree g (multiplierWeight g) = 2 := by
  simp [centralDegree_apply]

/-- Each standard weight has central degree `1`. -/
@[simp]
theorem centralDegree_standardWeight (i : Fin g) : centralDegree g (standardWeight i) = 1 := by
  simp [centralDegree_apply]

/-- Each paired weight has central degree `1`. -/
@[simp]
theorem centralDegree_pairedWeight (i : Fin g) : centralDegree g (pairedWeight i) = 1 := by
  simp [pairedWeight]

/-! ### Dominant weights -/

/-- **The dominant weights** `Dom_g`: the weights `(m, u)` with `u₁ ≥ ⋯ ≥ u_g ≥ 0`. The multiplier
exponent `m` is an unrestricted integer, so `(-1, 0)`, the character of `ν⁻¹`, is dominant. The
dominant weights are closed under addition. -/
def dominantWeights (g : ℕ) : AddSubmonoid (Weight g) where
  carrier := {wt | Antitone wt.2 ∧ 0 ≤ wt.2}
  zero_mem' := ⟨antitone_const, le_rfl⟩
  add_mem' ha hb := ⟨ha.1.add hb.1, add_nonneg ha.2 hb.2⟩

@[simp]
theorem mem_dominantWeights {wt : Weight g} :
    wt ∈ dominantWeights g ↔ Antitone wt.2 ∧ 0 ≤ wt.2 :=
  Iff.rfl

/-! ### The pullback along the central cover -/

/-- **The pullback along the central cover** `Sp₂g × 𝔾_m → GSp₂g`, `(a, c) ↦ c • a`: it sends the
weight `(m, u)` to the `Sp₂g`-weight `u` together with the exponent `2m + ∑ uᵢ` of `c`. -/
def coverPullback (g : ℕ) : Weight g →+ (Fin g → ℤ) × ℤ :=
  (AddMonoidHom.snd ℤ (Fin g → ℤ)).prod (centralDegree g)

@[simp]
theorem coverPullback_apply (wt : Weight g) : coverPullback g wt = (wt.2, centralDegree g wt) :=
  (rfl)

/-- **The fibres of the central-cover pullback.** The weight `wt` pulls back to `(u, d)` exactly
when `d - ∑ uᵢ` is even and `wt = ((d - ∑ uᵢ) / 2, u)`. -/
theorem coverPullback_eq_iff {wt : Weight g} {u : Fin g → ℤ} {d : ℤ} :
    coverPullback g wt = (u, d) ↔ Even (d - ∑ i, u i) ∧ wt = ((d - ∑ i, u i) / 2, u) := by
  obtain ⟨m, v⟩ := wt
  simp only [coverPullback_apply, centralDegree_apply, Prod.mk.injEq]
  constructor
  · rintro ⟨rfl, rfl⟩
    refine ⟨⟨m, by ring⟩, ?_, rfl⟩
    rw [add_sub_cancel_right]
    omega
  · rintro ⟨⟨k, hk⟩, rfl, rfl⟩
    refine ⟨rfl, ?_⟩
    rw [hk]
    omega

/-- The central-cover pullback is injective. -/
theorem coverPullback_injective : Injective (coverPullback g) := by
  intro a b h
  simp only [coverPullback_apply, centralDegree_apply, Prod.mk.injEq] at h
  obtain ⟨h₂, h₁⟩ := h
  rw [h₂] at h₁
  exact Prod.ext (by omega) h₂

/-- **The image of the central-cover pullback** consists of the pairs `(u, d)` with
`d ≡ ∑ uᵢ` modulo `2`: the condition for the kernel `μ₂` of the cover to act trivially. -/
theorem mem_range_coverPullback {x : (Fin g → ℤ) × ℤ} :
    x ∈ (coverPullback g).range ↔ Even (x.2 - ∑ i, x.1 i) := by
  obtain ⟨u, d⟩ := x
  refine ⟨fun ⟨wt, h⟩ ↦ (coverPullback_eq_iff.mp h).1, fun h ↦ ?_⟩
  exact ⟨((d - ∑ i, u i) / 2, u), coverPullback_eq_iff.mpr ⟨h, rfl⟩⟩

/-! ### Comparison with the root datum of `GSp₂g` -/

/-- **The comparison with the lattice of the root datum** `TauCeti.gspRootDatum`: the weight
`(m, u)` corresponds to `(u, m)`, the multiplier coordinate written last. -/
noncomputable def toGspCharacterLattice (g : ℕ) : Weight g ≃+ (ULift.{0} (Fin g) →₀ ℤ) × ℤ where
  toFun wt := (Finsupp.equivFunOnFinite.symm fun i ↦ wt.2 i.down, wt.1)
  invFun x := (x.2, fun i ↦ x.1 (ULift.up i))
  left_inv wt := by simp
  right_inv x := by
    ext <;> simp
  map_add' a b := by
    ext <;> simp

@[simp]
theorem toGspCharacterLattice_apply_fst_apply (wt : Weight g) (i : ULift.{0} (Fin g)) :
    (toGspCharacterLattice g wt).1 i = wt.2 i.down :=
  (rfl)

@[simp]
theorem toGspCharacterLattice_apply_snd (wt : Weight g) : (toGspCharacterLattice g wt).2 = wt.1 :=
  (rfl)

@[simp]
theorem toGspCharacterLattice_symm_apply (x : (ULift.{0} (Fin g) →₀ ℤ) × ℤ) :
    (toGspCharacterLattice g).symm x = (x.2, fun i ↦ x.1 (ULift.up i)) :=
  (rfl)

/-- **The simple roots**: `eᵢ - eᵢ₊₁` at the nodes `i` with `i + 1 < g`, and `2eᵢ - e_t` at the
last node `i = g - 1` (nodes are numbered from `0`). They are the simple roots of the base
`TauCeti.gspBase`, transported to `X_g`. -/
noncomputable def simpleRoot (i : Fin g) : Weight g :=
  (toGspCharacterLattice g).symm
    ((gspRootDatum.{0} g).root (Symplectic.diagonalSimpleRootIndex g i))

@[simp]
theorem toGspCharacterLattice_simpleRoot (i : Fin g) :
    toGspCharacterLattice g (simpleRoot i) =
      (gspRootDatum.{0} g).root (Symplectic.diagonalSimpleRootIndex g i) :=
  (toGspCharacterLattice g).apply_symm_apply _

/-- Before the last node, the simple root is `eᵢ - eᵢ₊₁`. -/
theorem simpleRoot_of_lt (i : Fin g) (h : (i : ℕ) + 1 < g) :
    simpleRoot i = standardWeight i - standardWeight ⟨i + 1, h⟩ := by
  rw [simpleRoot, AddEquiv.symm_apply_eq, Symplectic.diagonalSimpleRootIndex_of_lt i h,
    gspRootDatum_root_difference]
  ext <;> simp [Finsupp.single_apply, Pi.single_apply, ULift.ext_iff, eq_comm]

/-- At the last node, the simple root is `2e_g - e_t`. -/
theorem simpleRoot_of_not_lt (i : Fin g) (h : ¬(i : ℕ) + 1 < g) :
    simpleRoot i = 2 • standardWeight i - multiplierWeight g := by
  rw [simpleRoot, AddEquiv.symm_apply_eq, Symplectic.diagonalSimpleRootIndex_of_not_lt i h,
    gspRootDatum_root_positiveLong]
  ext <;> simp [Finsupp.single_apply, Pi.single_apply, ULift.ext_iff, eq_comm]

/-- Every simple root has central degree `0`: the centre acts trivially on the adjoint
representation. -/
@[simp]
theorem centralDegree_simpleRoot (i : Fin g) : centralDegree g (simpleRoot i) = 0 := by
  by_cases h : (i : ℕ) + 1 < g
  · rw [simpleRoot_of_lt i h, map_sub, centralDegree_standardWeight,
      centralDegree_standardWeight, sub_self]
  · rw [simpleRoot_of_not_lt i h, map_sub, map_nsmul, centralDegree_standardWeight,
      centralDegree_multiplierWeight]
    norm_num

/-- Before the last node, the simple coroot of `TauCeti.gspBase` at node `i` pairs `(m, u)` to
`uᵢ - uᵢ₊₁`. -/
theorem coroot'_diagonalSimpleRootIndex_toGspCharacterLattice_of_lt (i : Fin g)
    (h : (i : ℕ) + 1 < g) (wt : Weight g) :
    (gspRootDatum.{0} g).coroot' (Symplectic.diagonalSimpleRootIndex g i)
        (toGspCharacterLattice g wt) =
      wt.2 i - wt.2 ⟨i + 1, h⟩ := by
  simp [Symplectic.diagonalSimpleRootIndex_of_lt i h,
    Symplectic.diagonalRootDatum_coroot_difference, SplitTorus.dotPairing_apply,
    Finsupp.sum_fintype, Pi.single_apply, mul_sub, Finset.sum_sub_distrib]

/-- At the last node, the simple coroot of `TauCeti.gspBase` pairs `(m, u)` to `u_g`. -/
theorem coroot'_diagonalSimpleRootIndex_toGspCharacterLattice_of_not_lt (i : Fin g)
    (h : ¬(i : ℕ) + 1 < g) (wt : Weight g) :
    (gspRootDatum.{0} g).coroot' (Symplectic.diagonalSimpleRootIndex g i)
        (toGspCharacterLattice g wt) =
      wt.2 i := by
  simp [Symplectic.diagonalSimpleRootIndex_of_not_lt i h,
    Symplectic.diagonalRootDatum_coroot_positiveLong, SplitTorus.dotPairing_apply,
    Finsupp.sum_fintype, Pi.single_apply]

/-- **The dominant weights form the dominant chamber** of the base `TauCeti.gspBase`: a weight is
dominant exactly when every simple coroot is nonnegative on it. -/
theorem mem_dominantWeights_iff_mem_dominantChamber {wt : Weight g} :
    wt ∈ dominantWeights g ↔
      toGspCharacterLattice g wt ∈ (gspRootDatum.{0} g).dominantChamber (gspBase.{0} g) := by
  rw [RootPairing.mem_dominantChamber, mem_dominantWeights]
  simp only [mem_gspBase_support, forall_exists_index, forall_apply_eq_imp_iff]
  cases g with
  | zero => exact ⟨fun _ i ↦ i.elim0, fun _ ↦ ⟨fun a ↦ a.elim0, fun i ↦ i.elim0⟩⟩
  | succ n =>
    have hlast : ¬((Fin.last n : ℕ) + 1 < n + 1) := by simp
    constructor
    · rintro ⟨hanti, hnonneg⟩ i
      by_cases h : (i : ℕ) + 1 < n + 1
      · rw [coroot'_diagonalSimpleRootIndex_toGspCharacterLattice_of_lt i h, sub_nonneg]
        exact hanti (Fin.mk_le_mk.mpr (Nat.le_succ i))
      · rw [coroot'_diagonalSimpleRootIndex_toGspCharacterLattice_of_not_lt i h]
        exact hnonneg i
    · intro hc
      have hanti : Antitone wt.2 := by
        refine Fin.antitone_iff_succ_le.mpr fun i ↦ ?_
        have := hc i.castSucc
        rw [coroot'_diagonalSimpleRootIndex_toGspCharacterLattice_of_lt _ (by simp)] at this
        exact sub_nonneg.mp this
      refine ⟨hanti, fun i ↦ ?_⟩
      have := hc (Fin.last n)
      rw [coroot'_diagonalSimpleRootIndex_toGspCharacterLattice_of_not_lt _ hlast] at this
      exact this.trans (hanti (Fin.le_last i))

/-! ### The root order -/

/-- **The root order** `μ ≤ λ` on `X_g`: `λ - μ` is a natural combination of the simple roots
(`TauCeti.SymplecticSimilitude.rootLE_iff_exists_nat`). It is the order `RootPairing.rootLE` of
the base `TauCeti.gspBase` of `TauCeti.gspRootDatum`, transported to `X_g`. -/
def rootLE (μ lam : Weight g) : Prop :=
  (gspRootDatum.{0} g).rootLE (gspBase.{0} g) (toGspCharacterLattice g μ)
    (toGspCharacterLattice g lam)

/-- The root order on `X_g` is `RootPairing.rootLE` of `TauCeti.gspBase` under
`toGspCharacterLattice`, so the general `RootPairing.rootLE` lemmas apply to it. -/
theorem rootLE_iff_rootLE_toGspCharacterLattice {μ lam : Weight g} :
    rootLE μ lam ↔ (gspRootDatum.{0} g).rootLE (gspBase.{0} g) (toGspCharacterLattice g μ)
      (toGspCharacterLattice g lam) :=
  Iff.rfl

/-- `μ ≤ λ` in the root order exactly when `λ - μ = ∑ nᵢ αᵢ` with natural coefficients `nᵢ`. -/
theorem rootLE_iff_exists_nat {μ lam : Weight g} :
    rootLE μ lam ↔ ∃ n : Fin g → ℕ, lam - μ = ∑ i, n i • simpleRoot i := by
  rw [rootLE, RootPairing.rootLE_iff_sub_mem_posRootCone,
    mem_posRootCone_iff_exists_nat_of_bijOn _ _ (bijOn_diagonalSimpleRootIndex_gspBase g)]
  refine exists_congr fun n ↦ ?_
  rw [← map_sub, ← (toGspCharacterLattice g).injective.eq_iff, map_sum]
  simp only [map_nsmul, toGspCharacterLattice_simpleRoot]

/-- The root order is reflexive. -/
@[simp]
theorem rootLE_refl (wt : Weight g) : rootLE wt wt :=
  RootPairing.rootLE_refl _ _ _

/-- The root order is transitive. -/
theorem rootLE_trans {μ ν lam : Weight g} (h₁ : rootLE μ ν) (h₂ : rootLE ν lam) :
    rootLE μ lam :=
  RootPairing.rootLE_trans _ _ h₁ h₂

/-- The root order is antisymmetric. -/
theorem rootLE_antisymm {μ lam : Weight g} (h₁ : rootLE μ lam) (h₂ : rootLE lam μ) :
    μ = lam :=
  (toGspCharacterLattice g).injective (RootPairing.rootLE_antisymm _ _ h₁ h₂)

/-- **Comparable weights have the same central degree**, since every simple root has central
degree `0`. For instance `0` and `e_t` are incomparable. -/
theorem centralDegree_eq_of_rootLE {μ lam : Weight g} (h : rootLE μ lam) :
    centralDegree g μ = centralDegree g lam := by
  obtain ⟨n, hn⟩ := rootLE_iff_exists_nat.mp h
  have : centralDegree g (lam - μ) = 0 := by
    rw [hn, map_sum]
    exact Finset.sum_eq_zero fun i _ ↦ by rw [map_nsmul, centralDegree_simpleRoot, smul_zero]
  rw [map_sub, sub_eq_zero] at this
  exact this.symm

end TauCeti.SymplecticSimilitude

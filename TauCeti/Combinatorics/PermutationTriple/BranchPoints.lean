/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PermutationTriple.EulerCharacteristic
public import TauCeti.Combinatorics.PermutationTriple.GeometryType

/-!
# Permuting the branch points of a permutation triple

A permutation triple `t = (a, b, c) = (σ0, σ1, σinf)`, with `c * b * a = 1`, records the monodromy
of a cover of the sphere branched over the three ordered points `0, 1, ∞`. Reordering the three
branch points gives a new triple, whose components are the old ones in a new order, each up to
conjugacy; the conjugators are exactly what is needed to keep the product relation. This file
defines the five nonidentity resulting operations:

| operation  | branch points exchanged | formula                          |
| ---------- | ----------------------- | -------------------------------- |
| `swap01`   | `0 ↔ 1`                 | `(b, a, b⁻¹ * c * b)`            |
| `swap1Inf` | `1 ↔ ∞`                 | `(a, b⁻¹ * c * b, b)`            |
| `swap0Inf` | `0 ↔ ∞`                 | `(c, b, b * a * b⁻¹)`            |
| `rot`      | `0 → 1 → ∞ → 0`         | `(b, c, a)`                      |
| `rotInv`   | `0 → ∞ → 1 → 0`         | `(b⁻¹ * c * b, a, a * b * a⁻¹)`  |

Geometrically they, together with the identity operation, are the pullbacks along the six Möbius
transformations permuting `0, 1, ∞`.

## Main results

* `TauCeti.PermutationTriple.rot_eq`, `TauCeti.PermutationTriple.rotInv_eq`,
  `TauCeti.PermutationTriple.swap0Inf_eq`: the last three operations are composites of `swap01`
  and `swap1Inf`.
* `TauCeti.PermutationTriple.swap01_swap01`, `TauCeti.PermutationTriple.rot_rot_rot` and
  `TauCeti.PermutationTriple.rotInv_rotInv_rotInv` hold on the nose, whereas
  `TauCeti.PermutationTriple.swap1Inf_swap1Inf`, `TauCeti.PermutationTriple.swap0Inf_swap0Inf`,
  `TauCeti.PermutationTriple.rotInv_rot` and `TauCeti.PermutationTriple.rot_rotInv` are
  relabelings by an explicit component. The relabeling cannot be dropped:
  `TauCeti.PermutationTriple.exists_swap1Inf_swap1Inf_ne` and
  `TauCeti.PermutationTriple.exists_rotInv_rot_ne`.
* `TauCeti.PermutationTriple.swap01_smul` and its siblings: each operation commutes with
  relabeling, hence preserves isomorphism of triples (`TauCeti.PermutationTriple.Equivalent.swap01`
  and its siblings). Up to isomorphism the two exchanges `swap01` and `swap1Inf` are involutions
  whose composite `rotInv` has order three, which are the Coxeter relations of the symmetric group
  on the three branch points.
* The monodromy group, connectedness, the Euler characteristic, the genus and the geometry type
  are unchanged by all five nonidentity operations, while the cycle data, the cycle counts and
  the order triple are permuted accordingly.

## Implementation notes

Reordering the branch points is contravariant: applying `swap01` and then `swap1Inf` gives `rot`,
whose branch-point permutation `0 → 1 → ∞ → 0` is the product `(0 1) * (1 ∞)` of their labels in
the order of application. The operations therefore induce a right action of the symmetric group,
and only on isomorphism classes, since `swap1Inf` is an involution only up to relabeling.

## References

* `TauCetiRoadmap/BelyiMaps/README.md`, Layer 2.6, and the
  `TauCetiRoadmap/BelyiMaps/Suggested.lean` prototype.
* S. K. Lando, A. K. Zvonkin, *Graphs on Surfaces and Their Applications*, Encyclopaedia of
  Mathematical Sciences 141, Springer 2004, §1.5.
* E. Girondo, G. González-Diez, *Introduction to Compact Riemann Surfaces and Dessins d'Enfants*,
  London Mathematical Society Student Texts 79, Cambridge University Press 2012, §4.
-/

public section

namespace TauCeti

open Equiv Equiv.Perm

namespace PermutationTriple

variable {n : ℕ}

/-! ### The five nonidentity operations -/

/-- Exchange the branch points `0` and `1`: `(a, b, c) ↦ (b, a, b⁻¹ * c * b)`. -/
def swap01 (t : PermutationTriple n) : PermutationTriple n where
  σ0 := t.σ1
  σ1 := t.σ0
  σinf := t.σ1⁻¹ * t.σinf * t.σ1
  product_eq_one := by rw [t.σinf_eq_inv]; group

/-- Exchange the branch points `1` and `∞`: `(a, b, c) ↦ (a, b⁻¹ * c * b, b)`. -/
def swap1Inf (t : PermutationTriple n) : PermutationTriple n where
  σ0 := t.σ0
  σ1 := t.σ1⁻¹ * t.σinf * t.σ1
  σinf := t.σ1
  product_eq_one := by rw [t.σinf_eq_inv]; group

/-- Exchange the branch points `0` and `∞`: `(a, b, c) ↦ (c, b, b * a * b⁻¹)`. -/
def swap0Inf (t : PermutationTriple n) : PermutationTriple n :=
  swap01 (swap1Inf (swap01 t))

/-- Rotate the branch points `0 → 1 → ∞ → 0`: `(a, b, c) ↦ (b, c, a)`, with no conjugation. -/
def rot (t : PermutationTriple n) : PermutationTriple n :=
  swap1Inf (swap01 t)

/-- Rotate the branch points `0 → ∞ → 1 → 0`: `(a, b, c) ↦ (b⁻¹ * c * b, a, a * b * a⁻¹)`. This
is not the inverse of `TauCeti.PermutationTriple.rot` on triples, only on isomorphism classes;
see `TauCeti.PermutationTriple.rotInv_rot`. -/
def rotInv (t : PermutationTriple n) : PermutationTriple n :=
  swap01 (swap1Inf t)

variable (t : PermutationTriple n)

@[simp] theorem swap01_σ0 : (swap01 t).σ0 = t.σ1 := (rfl)

@[simp] theorem swap01_σ1 : (swap01 t).σ1 = t.σ0 := (rfl)

@[simp] theorem swap01_σinf : (swap01 t).σinf = t.σ1⁻¹ * t.σinf * t.σ1 := (rfl)

@[simp] theorem swap1Inf_σ0 : (swap1Inf t).σ0 = t.σ0 := (rfl)

@[simp] theorem swap1Inf_σ1 : (swap1Inf t).σ1 = t.σ1⁻¹ * t.σinf * t.σ1 := (rfl)

@[simp] theorem swap1Inf_σinf : (swap1Inf t).σinf = t.σ1 := (rfl)

@[simp] theorem swap0Inf_σ0 : (swap0Inf t).σ0 = t.σinf := by
  simp only [swap0Inf, swap01_σ0, swap1Inf_σ1, swap01_σ1, swap01_σinf, t.σinf_eq_inv]
  group

@[simp] theorem swap0Inf_σ1 : (swap0Inf t).σ1 = t.σ1 := (rfl)

@[simp] theorem swap0Inf_σinf : (swap0Inf t).σinf = t.σ1 * t.σ0 * t.σ1⁻¹ := by
  simp only [swap0Inf, swap01_σinf, swap1Inf_σ1, swap1Inf_σinf, swap01_σ1,
    swap01_σinf, t.σinf_eq_inv]
  group

@[simp] theorem rot_σ0 : (rot t).σ0 = t.σ1 := (rfl)

@[simp] theorem rot_σ1 : (rot t).σ1 = t.σinf := by
  simp only [rot, swap1Inf_σ1, swap01_σ1, swap01_σinf, t.σinf_eq_inv]
  group

@[simp] theorem rot_σinf : (rot t).σinf = t.σ0 := (rfl)

@[simp] theorem rotInv_σ0 : (rotInv t).σ0 = t.σ1⁻¹ * t.σinf * t.σ1 := (rfl)

@[simp] theorem rotInv_σ1 : (rotInv t).σ1 = t.σ0 := (rfl)

@[simp] theorem rotInv_σinf : (rotInv t).σinf = t.σ0 * t.σ1 * t.σ0⁻¹ := by
  simp only [rotInv, swap01_σinf, swap1Inf_σ1, swap1Inf_σinf, t.σinf_eq_inv]
  group

/-! ### Composites and relations -/

/-- Rotating `0 → 1 → ∞` is exchanging `0, 1` and then `1, ∞`. -/
theorem rot_eq : rot t = swap1Inf (swap01 t) := by
  simp only [rot]

/-- Rotating `0 → ∞ → 1` is exchanging `1, ∞` and then `0, 1`. -/
theorem rotInv_eq : rotInv t = swap01 (swap1Inf t) := by
  simp only [rotInv]

/-- Exchanging `0, ∞` is exchanging `0, 1`, then `1, ∞`, then `0, 1`. -/
theorem swap0Inf_eq : swap0Inf t = swap01 (swap1Inf (swap01 t)) := by
  simp only [swap0Inf]

/-- Exchanging `0` and `1` twice is the identity on triples, on the nose. -/
@[simp] theorem swap01_swap01 : swap01 (swap01 t) = t := (ext_of_two rfl rfl)

/-- Exchanging `0` and `1` is an involution on triples. -/
theorem swap01_involutive : Function.Involutive (swap01 : PermutationTriple n → _) :=
  swap01_swap01

/-- Exchanging `1` and `∞` twice relabels the triple by its first component. -/
@[simp] theorem swap1Inf_swap1Inf : swap1Inf (swap1Inf t) = t.σ0 • t := by
  ext1
  · simp
  · simp only [swap1Inf_σ1, swap1Inf_σinf, smul_σ1, t.σinf_eq_inv]
    group

/-- Exchanging `0` and `∞` twice relabels the triple by its second component. -/
@[simp] theorem swap0Inf_swap0Inf : swap0Inf (swap0Inf t) = t.σ1 • t := by
  ext1
  · simp
  · simp

/-- The rotation `0 → 1 → ∞ → 0` has order three on triples. -/
@[simp] theorem rot_rot_rot : rot (rot (rot t)) = t := by
  ext1 <;> simp

/-- The rotation `0 → ∞ → 1 → 0` has order three on triples. -/
@[simp] theorem rotInv_rotInv_rotInv : rotInv (rotInv (rotInv t)) = t := by
  ext1
  · simp only [rotInv_σ0, rotInv_σ1, rotInv_σinf, t.σinf_eq_inv]
    group
  · simp only [rotInv_σ0, rotInv_σ1, rotInv_σinf]
    group

/-- The two rotations compose to the relabeling by the second component. -/
@[simp] theorem rotInv_rot : rotInv (rot t) = t.σ1 • t := by
  ext1
  · simp only [rotInv_σ0, rot_σ1, rot_σinf, smul_σ0, t.σinf_eq_inv]
    group
  · simp

/-- The two rotations, in the other order, compose to the relabeling by the first component. -/
@[simp] theorem rot_rotInv : rot (rotInv t) = t.σ0 • t := by
  ext1
  · simp
  · simp

/-- `TauCeti.PermutationTriple.swap1Inf` is not an involution on triples. -/
theorem exists_swap1Inf_swap1Inf_ne :
    ∃ t : PermutationTriple 3, swap1Inf (swap1Inf t) ≠ t := by
  refine ⟨ofTwo (swap 0 1) (swap 1 2), fun h => ?_⟩
  have h0 := congrArg (fun s : PermutationTriple 3 => s.σ1 0) h
  simp [swap1Inf_swap1Inf, swap_apply_of_ne_of_ne] at h0

/-- `TauCeti.PermutationTriple.rotInv` is not a left inverse of `TauCeti.PermutationTriple.rot`
on triples. -/
theorem exists_rotInv_rot_ne : ∃ t : PermutationTriple 3, rotInv (rot t) ≠ t := by
  refine ⟨ofTwo (swap 0 1) (swap 1 2), fun h => ?_⟩
  have h0 := congrArg (fun s : PermutationTriple 3 => s.σ0 0) h
  simp [rotInv_rot, swap_apply_of_ne_of_ne] at h0

/-! ### Relabeling and isomorphism classes -/

variable (τ : Perm (Fin n))

/-- Exchanging `0` and `1` commutes with relabeling the sheets. -/
@[simp] theorem swap01_smul : swap01 (τ • t) = τ • swap01 t := by
  ext1 <;> simp

/-- Exchanging `1` and `∞` commutes with relabeling the sheets. -/
@[simp] theorem swap1Inf_smul : swap1Inf (τ • t) = τ • swap1Inf t := by
  ext1
  · simp
  · simp only [swap1Inf_σ1, smul_σ1, smul_σinf]
    group

/-- Exchanging `0` and `∞` commutes with relabeling the sheets. -/
@[simp] theorem swap0Inf_smul : swap0Inf (τ • t) = τ • swap0Inf t := by
  rw [swap0Inf_eq, swap0Inf_eq, swap01_smul, swap1Inf_smul, swap01_smul]

/-- Rotating the branch points commutes with relabeling the sheets. -/
@[simp] theorem rot_smul : rot (τ • t) = τ • rot t := by
  rw [rot_eq, rot_eq, swap01_smul, swap1Inf_smul]

/-- Rotating the branch points backwards commutes with relabeling the sheets. -/
@[simp] theorem rotInv_smul : rotInv (τ • t) = τ • rotInv t := by
  rw [rotInv_eq, rotInv_eq, swap1Inf_smul, swap01_smul]

variable {t}

/-- Exchanging `0` and `1` preserves isomorphism of triples. -/
theorem Equivalent.swap01 {t' : PermutationTriple n} (h : Equivalent t t') :
    Equivalent (swap01 t) (swap01 t') := by
  obtain ⟨τ, rfl⟩ := equivalent_iff_exists_smul_eq.mp h
  exact equivalent_iff_exists_smul_eq.mpr ⟨τ, (swap01_smul t τ).symm⟩

/-- Exchanging `1` and `∞` preserves isomorphism of triples. -/
theorem Equivalent.swap1Inf {t' : PermutationTriple n} (h : Equivalent t t') :
    Equivalent (swap1Inf t) (swap1Inf t') := by
  obtain ⟨τ, rfl⟩ := equivalent_iff_exists_smul_eq.mp h
  exact equivalent_iff_exists_smul_eq.mpr ⟨τ, (swap1Inf_smul t τ).symm⟩

/-- Exchanging `0` and `∞` preserves isomorphism of triples. -/
theorem Equivalent.swap0Inf {t' : PermutationTriple n} (h : Equivalent t t') :
    Equivalent (swap0Inf t) (swap0Inf t') := by
  rw [swap0Inf_eq, swap0Inf_eq]
  exact h.swap01.swap1Inf.swap01

/-- Rotating the branch points preserves isomorphism of triples. -/
theorem Equivalent.rot {t' : PermutationTriple n} (h : Equivalent t t') :
    Equivalent (rot t) (rot t') := by
  rw [rot_eq, rot_eq]
  exact h.swap01.swap1Inf

/-- Rotating the branch points backwards preserves isomorphism of triples. -/
theorem Equivalent.rotInv {t' : PermutationTriple n} (h : Equivalent t t') :
    Equivalent (rotInv t) (rotInv t') := by
  rw [rotInv_eq, rotInv_eq]
  exact h.swap1Inf.swap01

variable (t)

/-- Up to isomorphism, exchanging `1` and `∞` is an involution. -/
theorem equivalent_swap1Inf_swap1Inf : Equivalent (swap1Inf (swap1Inf t)) t := by
  rw [swap1Inf_swap1Inf]
  exact equivalent_iff_exists_smul_eq.mpr ⟨_, inv_smul_smul _ t⟩

/-- Up to isomorphism, exchanging `0` and `∞` is an involution. -/
theorem equivalent_swap0Inf_swap0Inf : Equivalent (swap0Inf (swap0Inf t)) t := by
  rw [swap0Inf_swap0Inf]
  exact equivalent_iff_exists_smul_eq.mpr ⟨_, inv_smul_smul _ t⟩

/-- Up to isomorphism, `TauCeti.PermutationTriple.rotInv` is a left inverse of
`TauCeti.PermutationTriple.rot`. -/
theorem equivalent_rotInv_rot : Equivalent (rotInv (rot t)) t := by
  rw [rotInv_rot]
  exact equivalent_iff_exists_smul_eq.mpr ⟨_, inv_smul_smul _ t⟩

/-- Up to isomorphism, `TauCeti.PermutationTriple.rotInv` is a right inverse of
`TauCeti.PermutationTriple.rot`. -/
theorem equivalent_rot_rotInv : Equivalent (rot (rotInv t)) t := by
  rw [rot_rotInv]
  exact equivalent_iff_exists_smul_eq.mpr ⟨_, inv_smul_smul _ t⟩

/-! ### Invariants

The monodromy group, and with it connectedness, is the subgroup generated by all three
components, so it does not see their order; the Euler characteristic, the genus and the geometry
type are symmetric functions of the three components' conjugacy classes. -/

/-- Exchanging `0` and `1` does not change the monodromy group. -/
@[simp] theorem monodromyGroup_swap01 : (swap01 t).monodromyGroup = t.monodromyGroup := by
  rw [← closure_pair_eq_monodromyGroup, ← closure_pair_eq_monodromyGroup, swap01_σ0, swap01_σ1,
    Set.pair_comm]

/-- Exchanging `1` and `∞` does not change the monodromy group. -/
@[simp] theorem monodromyGroup_swap1Inf : (swap1Inf t).monodromyGroup = t.monodromyGroup := by
  apply le_antisymm
  · rw [← closure_pair_eq_monodromyGroup, Subgroup.closure_le]
    rintro x (rfl | rfl)
    · simp
    · exact mul_mem (mul_mem (inv_mem t.σ1_mem_monodromyGroup) t.σinf_mem_monodromyGroup)
        t.σ1_mem_monodromyGroup
  · rw [← closure_pair_eq_monodromyGroup, Subgroup.closure_le]
    rintro x (rfl | rfl)
    · simpa using (swap1Inf t).σ0_mem_monodromyGroup
    · simpa using (swap1Inf t).σinf_mem_monodromyGroup

/-- Exchanging `0` and `∞` does not change the monodromy group. -/
@[simp] theorem monodromyGroup_swap0Inf : (swap0Inf t).monodromyGroup = t.monodromyGroup := by
  rw [swap0Inf_eq, monodromyGroup_swap01, monodromyGroup_swap1Inf, monodromyGroup_swap01]

/-- Rotating `0 → 1 → ∞ → 0` does not change the monodromy group. -/
@[simp] theorem monodromyGroup_rot : (rot t).monodromyGroup = t.monodromyGroup := by
  rw [rot_eq, monodromyGroup_swap1Inf, monodromyGroup_swap01]

/-- Rotating `0 → ∞ → 1 → 0` does not change the monodromy group. -/
@[simp] theorem monodromyGroup_rotInv : (rotInv t).monodromyGroup = t.monodromyGroup := by
  rw [rotInv_eq, monodromyGroup_swap01, monodromyGroup_swap1Inf]

/-- Exchanging `0` and `1` does not change connectedness. -/
@[simp] theorem isConnected_swap01_iff : (swap01 t).IsConnected ↔ t.IsConnected := by
  rw [isConnected_iff, isConnected_iff, monodromyGroup_swap01]

/-- Exchanging `1` and `∞` does not change connectedness. -/
@[simp] theorem isConnected_swap1Inf_iff : (swap1Inf t).IsConnected ↔ t.IsConnected := by
  rw [isConnected_iff, isConnected_iff, monodromyGroup_swap1Inf]

/-- Exchanging `0` and `∞` does not change connectedness. -/
@[simp] theorem isConnected_swap0Inf_iff : (swap0Inf t).IsConnected ↔ t.IsConnected := by
  rw [isConnected_iff, isConnected_iff, monodromyGroup_swap0Inf]

/-- Rotating `0 → 1 → ∞ → 0` does not change connectedness. -/
@[simp] theorem isConnected_rot_iff : (rot t).IsConnected ↔ t.IsConnected := by
  rw [isConnected_iff, isConnected_iff, monodromyGroup_rot]

/-- Rotating `0 → ∞ → 1 → 0` does not change connectedness. -/
@[simp] theorem isConnected_rotInv_iff : (rotInv t).IsConnected ↔ t.IsConnected := by
  rw [isConnected_iff, isConnected_iff, monodromyGroup_rotInv]

/-- Exchanging `0` and `1` exchanges the cycle partitions at `0` and `1`. -/
@[simp] theorem cycleData_swap01 :
    (swap01 t).cycleData = (t.cycleData.2.1, t.cycleData.1, t.cycleData.2.2) := by
  have h : IsConj t.σinf (t.σ1⁻¹ * t.σinf * t.σ1) := isConj_iff.mpr ⟨t.σ1⁻¹, by group⟩
  rw [partition_eq_of_isConj] at h
  simp [Prod.ext_iff, ← h]

/-- Exchanging `1` and `∞` exchanges the cycle partitions at `1` and `∞`. -/
@[simp] theorem cycleData_swap1Inf :
    (swap1Inf t).cycleData = (t.cycleData.1, t.cycleData.2.2, t.cycleData.2.1) := by
  have h : IsConj t.σinf (t.σ1⁻¹ * t.σinf * t.σ1) := isConj_iff.mpr ⟨t.σ1⁻¹, by group⟩
  rw [partition_eq_of_isConj] at h
  simp [Prod.ext_iff, ← h]

/-- Exchanging `0` and `∞` exchanges their cycle partitions. -/
@[simp] theorem cycleData_swap0Inf :
    (swap0Inf t).cycleData = (t.cycleData.2.2, t.cycleData.2.1, t.cycleData.1) := by
  rw [swap0Inf_eq, cycleData_swap01, cycleData_swap1Inf, cycleData_swap01]

/-- Rotating the branch points rotates the cycle partitions. -/
@[simp] theorem cycleData_rot :
    (rot t).cycleData = (t.cycleData.2.1, t.cycleData.2.2, t.cycleData.1) := by
  rw [rot_eq, cycleData_swap1Inf, cycleData_swap01]

/-- Rotating the branch points backwards rotates the cycle partitions backwards. -/
@[simp] theorem cycleData_rotInv :
    (rotInv t).cycleData = (t.cycleData.2.2, t.cycleData.1, t.cycleData.2.1) := by
  rw [rotInv_eq, cycleData_swap01, cycleData_swap1Inf]

/-- Exchanging `0` and `1` exchanges their cycle counts. -/
@[simp] theorem cycleCounts_swap01 :
    (swap01 t).cycleCounts = (t.cycleCounts.2.1, t.cycleCounts.1, t.cycleCounts.2.2) := by
  rw [cycleCounts_eq_card_cycleData, cycleCounts_eq_card_cycleData, cycleData_swap01]

/-- Exchanging `1` and `∞` exchanges their cycle counts. -/
@[simp] theorem cycleCounts_swap1Inf :
    (swap1Inf t).cycleCounts = (t.cycleCounts.1, t.cycleCounts.2.2, t.cycleCounts.2.1) := by
  rw [cycleCounts_eq_card_cycleData, cycleCounts_eq_card_cycleData, cycleData_swap1Inf]

/-- Exchanging `0` and `∞` exchanges their cycle counts. -/
@[simp] theorem cycleCounts_swap0Inf :
    (swap0Inf t).cycleCounts = (t.cycleCounts.2.2, t.cycleCounts.2.1, t.cycleCounts.1) := by
  rw [swap0Inf_eq, cycleCounts_swap01, cycleCounts_swap1Inf, cycleCounts_swap01]

/-- Rotating the branch points rotates their cycle counts. -/
@[simp] theorem cycleCounts_rot :
    (rot t).cycleCounts = (t.cycleCounts.2.1, t.cycleCounts.2.2, t.cycleCounts.1) := by
  rw [rot_eq, cycleCounts_swap1Inf, cycleCounts_swap01]

/-- Rotating the branch points backwards rotates their cycle counts backwards. -/
@[simp] theorem cycleCounts_rotInv :
    (rotInv t).cycleCounts = (t.cycleCounts.2.2, t.cycleCounts.1, t.cycleCounts.2.1) := by
  rw [rotInv_eq, cycleCounts_swap01, cycleCounts_swap1Inf]

/-- Exchanging `0` and `1` exchanges their entries in the order triple. -/
@[simp] theorem orderTriple_swap01 :
    (swap01 t).orderTriple = (t.orderTriple.2.1, t.orderTriple.1, t.orderTriple.2.2) := by
  rw [orderTriple_eq_lcm_cycleData, orderTriple_eq_lcm_cycleData, cycleData_swap01]

/-- Exchanging `1` and `∞` exchanges their entries in the order triple. -/
@[simp] theorem orderTriple_swap1Inf :
    (swap1Inf t).orderTriple = (t.orderTriple.1, t.orderTriple.2.2, t.orderTriple.2.1) := by
  rw [orderTriple_eq_lcm_cycleData, orderTriple_eq_lcm_cycleData, cycleData_swap1Inf]

/-- Exchanging `0` and `∞` exchanges their entries in the order triple. -/
@[simp] theorem orderTriple_swap0Inf :
    (swap0Inf t).orderTriple = (t.orderTriple.2.2, t.orderTriple.2.1, t.orderTriple.1) := by
  rw [swap0Inf_eq, orderTriple_swap01, orderTriple_swap1Inf, orderTriple_swap01]

/-- Rotating the branch points rotates the order triple. -/
@[simp] theorem orderTriple_rot :
    (rot t).orderTriple = (t.orderTriple.2.1, t.orderTriple.2.2, t.orderTriple.1) := by
  rw [rot_eq, orderTriple_swap1Inf, orderTriple_swap01]

/-- Rotating the branch points backwards rotates the order triple backwards. -/
@[simp] theorem orderTriple_rotInv :
    (rotInv t).orderTriple = (t.orderTriple.2.2, t.orderTriple.1, t.orderTriple.2.1) := by
  rw [rotInv_eq, orderTriple_swap01, orderTriple_swap1Inf]

/-- Exchanging `0` and `1` does not change the Euler characteristic. -/
@[simp] theorem eulerChar_swap01 : (swap01 t).eulerChar = t.eulerChar := by
  rw [eulerChar_eq_cycleCounts, eulerChar_eq_cycleCounts, cycleCounts_swap01]
  ring

/-- Exchanging `1` and `∞` does not change the Euler characteristic. -/
@[simp] theorem eulerChar_swap1Inf : (swap1Inf t).eulerChar = t.eulerChar := by
  rw [eulerChar_eq_cycleCounts, eulerChar_eq_cycleCounts, cycleCounts_swap1Inf]
  ring

/-- Exchanging `0` and `∞` does not change the Euler characteristic. -/
@[simp] theorem eulerChar_swap0Inf : (swap0Inf t).eulerChar = t.eulerChar := by
  rw [swap0Inf_eq, eulerChar_swap01, eulerChar_swap1Inf, eulerChar_swap01]

/-- Rotating `0 → 1 → ∞ → 0` does not change the Euler characteristic. -/
@[simp] theorem eulerChar_rot : (rot t).eulerChar = t.eulerChar := by
  rw [rot_eq, eulerChar_swap1Inf, eulerChar_swap01]

/-- Rotating `0 → ∞ → 1 → 0` does not change the Euler characteristic. -/
@[simp] theorem eulerChar_rotInv : (rotInv t).eulerChar = t.eulerChar := by
  rw [rotInv_eq, eulerChar_swap01, eulerChar_swap1Inf]

/-- Exchanging `0` and `1` does not change the genus. -/
@[simp] theorem genus_swap01 : (swap01 t).genus = t.genus := by
  rw [genus_def, genus_def, eulerChar_swap01]

/-- Exchanging `1` and `∞` does not change the genus. -/
@[simp] theorem genus_swap1Inf : (swap1Inf t).genus = t.genus := by
  rw [genus_def, genus_def, eulerChar_swap1Inf]

/-- Exchanging `0` and `∞` does not change the genus. -/
@[simp] theorem genus_swap0Inf : (swap0Inf t).genus = t.genus := by
  rw [genus_def, genus_def, eulerChar_swap0Inf]

/-- Rotating `0 → 1 → ∞ → 0` does not change the genus. -/
@[simp] theorem genus_rot : (rot t).genus = t.genus := by
  rw [genus_def, genus_def, eulerChar_rot]

/-- Rotating `0 → ∞ → 1 → 0` does not change the genus. -/
@[simp] theorem genus_rotInv : (rotInv t).genus = t.genus := by
  rw [genus_def, genus_def, eulerChar_rotInv]

/-- Exchanging `0` and `1` does not change the geometry type. -/
@[simp] theorem geometryType_swap01 : (swap01 t).geometryType = t.geometryType := by
  refine geometryType_eq_of_sum_eq ?_
  simp only [orderTriple_swap01]
  ring

/-- Exchanging `1` and `∞` does not change the geometry type. -/
@[simp] theorem geometryType_swap1Inf : (swap1Inf t).geometryType = t.geometryType := by
  refine geometryType_eq_of_sum_eq ?_
  simp only [orderTriple_swap1Inf]
  ring

/-- Exchanging `0` and `∞` does not change the geometry type. -/
@[simp] theorem geometryType_swap0Inf : (swap0Inf t).geometryType = t.geometryType := by
  rw [swap0Inf_eq, geometryType_swap01, geometryType_swap1Inf, geometryType_swap01]

/-- Rotating `0 → 1 → ∞ → 0` does not change the geometry type. -/
@[simp] theorem geometryType_rot : (rot t).geometryType = t.geometryType := by
  rw [rot_eq, geometryType_swap1Inf, geometryType_swap01]

/-- Rotating `0 → ∞ → 1 → 0` does not change the geometry type. -/
@[simp] theorem geometryType_rotInv : (rotInv t).geometryType = t.geometryType := by
  rw [rotInv_eq, geometryType_swap01, geometryType_swap1Inf]

end PermutationTriple

end TauCeti

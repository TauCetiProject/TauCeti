/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Stable
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Stability.Injective
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Stability.Surjective

/-!
# General linear stability theorems and finite-rank descriptions of `K₁`

Over a possibly noncommutative ring `R` of Bass stable range at most `s`
(`TauCeti.HasStableRangeLE R s`), Bass's surjective stability
(`TauCeti.surjective_stability`) and Vaserstein's injective stability
(`TauCeti.injective_stability`) capture algebraic `K₁(R)` and the commutator subgroup
`⁅GLₙ(R), GLₙ(R)⁆` already in finite rank:

* **Surjective `K₁`-stability (`s ≤ n`).** The canonical homomorphism
  `AlgebraicK1.mk R n : GL (Fin n) R →* K₁(R)` is surjective, yielding
  `GL (Fin n) R ⧸ (AlgebraicK1.mk R n).ker ≃* K₁(R)` already at the boundary `n = s` where
  injective stability need not yet hold.
* **Injective `K₁`-stability (`s + 1 ≤ n`).** The kernel of `AlgebraicK1.mk R n` equals
  `elementarySubgroup (Fin n) R`, yielding
  `GL (Fin n) R ⧸ elementarySubgroup (Fin n) R ≃* K₁(R)` and
  `commutator (GL n R) ≤ elementarySubgroup n R`.
* **Commutator and abelianization identification (`max 3 (s + 1) ≤ n`).** Combining with
  `elementarySubgroup_le_commutator` gives `elementarySubgroup n R = commutator (GL n R)` and
  `Group.Abelianization (GL (Fin n) R) ≃* K₁(R)`.

## Main definitions

* `TauCeti.AlgebraicK1.quotientKerMkEquiv`: `GL (Fin n) R ⧸ (AlgebraicK1.mk R n).ker ≃* K₁(R)`
  for `s ≤ n`.
* `TauCeti.AlgebraicK1.quotientFinElementarySubgroupEquiv`:
  `GL (Fin n) R ⧸ elementarySubgroup (Fin n) R ≃* K₁(R)` for `s + 1 ≤ n`.
* `TauCeti.AlgebraicK1.abelianizationFinEquiv`:
  `Group.Abelianization (GL (Fin n) R) ≃* K₁(R)` for `max 3 (s + 1) ≤ n`.

## Main results

* `TauCeti.AlgebraicK1.mk_surjective`, `TauCeti.AlgebraicK1.ker_mk_eq_elementarySubgroup`:
  finite-rank surjectivity and kernel identification for `AlgebraicK1.mk` in the stable range.
* `TauCeti.commutator_le_elementarySubgroup_of_hasStableRangeLE`,
  `TauCeti.elementarySubgroup_eq_commutator_of_hasStableRangeLE`: finite-rank commutator
  descriptions in the stable range.

## References

* H. Bass, *Algebraic K-Theory*, W. A. Benjamin (1968), Chapter V, §3–§4.
* L. N. Vaserstein, *On the stabilization of the general linear group over a ring*, Mathematics of
  the USSR-Sbornik 8 (1969), 383–400.
* C. A. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, Graduate Studies in
  Mathematics 145 (2013), Chapter III, Remark 1.2.5 and Exercise 1.3.
-/

public section

noncomputable section

open Matrix

open scoped commutatorElement

namespace TauCeti

/-! ## Finite-rank descriptions of `K₁` and commutator subgroups -/

namespace AlgebraicK1

/-- **Surjective `K₁`-stability:** if `R` has Bass stable range at most `s` and `s ≤ n`, the
canonical homomorphism `AlgebraicK1.mk R n : GL (Fin n) R →* AlgebraicK1 R` is surjective. -/
theorem mk_surjective {R : Type*} [Ring R] {s n : ℕ} (hR : HasStableRangeLE R s) (hn : s ≤ n) :
    Function.Surjective (mk R n) := by
  intro x
  obtain ⟨m, u, rfl⟩ := exists_mk x
  rcases le_total m n with hmn | hnm
  · exact ⟨stabilizeGL R hmn u, mk_stabilizeGL hmn u⟩
  · let φ := finSumFinEquiv.trans (finCongr (Nat.add_sub_cancel' hnm))
    obtain ⟨h, e, he, hge⟩ := surjective_stability s hR (Fin n) (Fin (m - n)) (by simpa using hn)
      (φ.symm.reindexGL R u)
    have hge' : φ.symm.reindexGL R u = fromBlocksGL (h, (1 : GL (Fin (m - n)) R)) * e :=
      Units.ext (by simpa using hge)
    have hu : u = stabilizeGL R hnm h * φ.reindexGL R e := by
      calc u = φ.reindexGL R (φ.symm.reindexGL R u) := by simp
        _ = φ.reindexGL R (fromBlocksGL (h, 1)) * φ.reindexGL R e := by rw [hge', map_mul]
        _ = stabilizeGL R hnm h * φ.reindexGL R e := by rw [← stabilizeGL_apply]
    refine ⟨h, ?_⟩
    rw [hu, map_mul, mk_stabilizeGL hnm h,
      elementarySubgroup_le_ker_mk m ((φ.reindexGL_mem_elementarySubgroup_iff).mpr he), mul_one]

/-- When `R` has Bass stable range at most `s` and `s ≤ n` (including at the boundary `n = s` where
injective stability need not yet hold), `K₁(R)` is the quotient of `GL (Fin n) R` by the actual
kernel `(AlgebraicK1.mk R n).ker`. -/
def quotientKerMkEquiv {R : Type*} [Ring R] {s n : ℕ} (hR : HasStableRangeLE R s) (hn : s ≤ n) :
    GL (Fin n) R ⧸ (mk R n).ker ≃* AlgebraicK1 R :=
  QuotientGroup.quotientKerEquivOfSurjective (mk R n) (mk_surjective hR hn)

/-- `AlgebraicK1.quotientKerMkEquiv` sends the coset of `u` to `AlgebraicK1.mk R n u`. -/
@[simp]
theorem quotientKerMkEquiv_mk {R : Type*} [Ring R] {s n : ℕ} (hR : HasStableRangeLE R s)
    (hn : s ≤ n) (u : GL (Fin n) R) :
    quotientKerMkEquiv hR hn (QuotientGroup.mk u) = mk R n u :=
  (rfl)

/-- **Injective `K₁`-stability:** if `R` has Bass stable range at most `s` and `s + 1 ≤ n`, the
kernel of `AlgebraicK1.mk R n` equals `elementarySubgroup (Fin n) R`. -/
theorem ker_mk_eq_elementarySubgroup {R : Type*} [Ring R] {s n : ℕ} (hR : HasStableRangeLE R s)
    (hn : s + 1 ≤ n) :
    (mk R n).ker = TauCeti.elementarySubgroup (Fin n) R := by
  refine le_antisymm (fun u hu ↦ ?_) (elementarySubgroup_le_ker_mk n)
  rw [MonoidHom.mem_ker, mk_eq_one_iff] at hu
  obtain ⟨k, hnk, hu⟩ := hu
  let φ := finSumFinEquiv.trans (finCongr (Nat.add_sub_cancel' hnk))
  have hU : φ.symm.reindexGL R (stabilizeGL R hnk u) =
      fromBlocksGL (u, (1 : GL (Fin (k - n)) R)) := by
    rw [stabilizeGL_apply hnk u]
    exact Equiv.reindexGL_symm_apply_reindexGL φ R _
  exact injective_stability s hR (Fin n) (Fin (k - n)) (by simpa using hn) u
    (φ.symm.reindexGL R (stabilizeGL R hnk u)) (by simp [hU])
    ((φ.symm.reindexGL_mem_elementarySubgroup_iff).mpr hu)

/-- When `R` has Bass stable range at most `s` and `s + 1 ≤ n`, algebraic `K₁(R)` is canonically
isomorphic to `GL (Fin n) R ⧸ elementarySubgroup (Fin n) R` (with normality provided by
`TauCeti.elementarySubgroup_normal_of_hasStableRangeLE`). -/
def quotientFinElementarySubgroupEquiv {R : Type*} [Ring R] {s n : ℕ}
    [(TauCeti.elementarySubgroup (Fin n) R).Normal]
    (hR : HasStableRangeLE R s) (hn : s + 1 ≤ n) :
    GL (Fin n) R ⧸ TauCeti.elementarySubgroup (Fin n) R ≃* AlgebraicK1 R :=
  (QuotientGroup.quotientMulEquivOfEq (ker_mk_eq_elementarySubgroup hR hn).symm).trans
    (quotientKerMkEquiv hR (Nat.le_of_succ_le hn))

/-- `AlgebraicK1.quotientFinElementarySubgroupEquiv` sends the coset of `u` to
`AlgebraicK1.mk R n u`. -/
@[simp]
theorem quotientFinElementarySubgroupEquiv_mk {R : Type*} [Ring R] {s n : ℕ}
    [(TauCeti.elementarySubgroup (Fin n) R).Normal]
    (hR : HasStableRangeLE R s) (hn : s + 1 ≤ n) (u : GL (Fin n) R) :
    quotientFinElementarySubgroupEquiv hR hn (QuotientGroup.mk u) = mk R n u :=
  (rfl)

end AlgebraicK1

/-- When `R` has Bass stable range at most `s` and `s + 1 ≤ Fintype.card n`, the commutator
subgroup of `GL n R` is contained in `elementarySubgroup n R`. -/
theorem commutator_le_elementarySubgroup_of_hasStableRangeLE {R n : Type*} [Ring R] [Fintype n]
    [DecidableEq n] {s : ℕ} (hR : HasStableRangeLE R s) (hn : s + 1 ≤ Fintype.card n) :
    commutator (GL n R) ≤ elementarySubgroup n R :=
  Subgroup.commutator_le.mpr fun u _ v _ ↦
    injective_stability s hR n n hn ⁅u, v⁆ (fromBlocksGL (⁅u, v⁆, 1)) (by simp)
      (fromBlocksGL_commutatorElement_mem_elementarySubgroup u v)

/-- When `R` has Bass stable range at most `s` and `max 3 (s + 1) ≤ Fintype.card n`, the
elementary subgroup `elementarySubgroup n R` equals the commutator subgroup of `GL n R`. -/
theorem elementarySubgroup_eq_commutator_of_hasStableRangeLE {R n : Type*} [Ring R] [Fintype n]
    [DecidableEq n] {s : ℕ} (hR : HasStableRangeLE R s)
    (hn : max 3 (s + 1) ≤ Fintype.card n) :
    elementarySubgroup n R = commutator (GL n R) :=
  le_antisymm (elementarySubgroup_le_commutator (le_of_max_le_left hn))
    (commutator_le_elementarySubgroup_of_hasStableRangeLE hR (le_of_max_le_right hn))

namespace AlgebraicK1

/-- When `R` has Bass stable range at most `s` and `max 3 (s + 1) ≤ n`, algebraic `K₁(R)` is
canonically isomorphic to the abelianization of `GL (Fin n) R`. -/
def abelianizationFinEquiv {R : Type*} [Ring R] {s n : ℕ} (hR : HasStableRangeLE R s)
    (hn : max 3 (s + 1) ≤ n) :
    Group.Abelianization (GL (Fin n) R) ≃* AlgebraicK1 R :=
  have hker : commutator (GL (Fin n) R) = (mk R n).ker := by
    rw [ker_mk_eq_elementarySubgroup hR (le_of_max_le_right hn),
      elementarySubgroup_eq_commutator_of_hasStableRangeLE hR (by simpa using hn)]
  (QuotientGroup.quotientMulEquivOfEq hker).trans
    (quotientKerMkEquiv hR (Nat.le_of_succ_le (le_of_max_le_right hn)))

/-- `AlgebraicK1.abelianizationFinEquiv` sends the abelianization class of `u` to
`AlgebraicK1.mk R n u`. -/
@[simp]
theorem abelianizationFinEquiv_of {R : Type*} [Ring R] {s n : ℕ} (hR : HasStableRangeLE R s)
    (hn : max 3 (s + 1) ≤ n) (u : GL (Fin n) R) :
    abelianizationFinEquiv hR hn (Group.Abelianization.of u) = mk R n u :=
  (rfl)

end AlgebraicK1

end TauCeti

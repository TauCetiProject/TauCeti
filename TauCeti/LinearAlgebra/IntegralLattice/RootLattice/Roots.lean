/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.PosDef.RepresentationNumber
public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.Dynkin
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.SimplyLaced

/-!
# The norm-two vectors of a root lattice are its roots

Let `t` be a valid simply-laced Dynkin type, so `t.rootLattice ht` is the positive even lattice on
`Fin t.rank → ℚ` whose Gram matrix in the standard basis is the Cartan matrix of `t`.  This file
proves that the vectors of norm `2` in this lattice are exactly the roots of the pinned simply
connected root datum `t.simplyConnectedRootDatum hv` of the root-system development, written in
simple-root coordinates, and that there are exactly `t.numRoots` of them.

The pinned datum writes roots in fundamental-weight coordinates and coroots in simple-coroot
coordinates.  In a simply-laced type the coordinates of the coroot with index `k` are the
simple-root coordinates of the root with index `k`
(`TauCeti.DynkinType.root_eq_sum_coroot_smul_root_simpleIndex`), so the lattice root
`TauCeti.DynkinType.rootLatticeRoot` attached to `k` is the vector with these coordinates, and the
pairing of the datum becomes the lattice form (`TauCeti.DynkinType.form_rootLatticeRoot`).

The proof is uniform in the type and uses no enumeration of roots.  Every root has norm `2`
because the pairing of a root with its own coroot is `2`.  Conversely, the norm-`2` vectors are
reached from the simple roots by simple reflections: if `x = ∑ cᵢ αᵢ` has norm `2`, then
`2 = ∑ cᵢ (x, αᵢ)`, so some `cᵢ (x, αᵢ)` is positive.  Replacing `x` by `-x` if necessary,
`cᵢ > 0` and `(x, αᵢ) > 0`; positive definiteness forces `x = αᵢ` or `(x, αᵢ) = 1`, and in the
latter case `x - αᵢ` has norm `2`, smaller coordinates, and reflects to `x` in `αᵢ`.  Induction on
`∑ |cᵢ|` concludes.

## Main declarations

* `TauCeti.DynkinType.rootLatticeRoot`: the root with index `k`, as a vector of the root lattice.
* `TauCeti.DynkinType.form_rootLatticeRoot`: the lattice form of two roots is the pairing of the
  pinned datum.
* `TauCeti.DynkinType.rootLatticeRoot_reflectionPerm`: the Weyl reflections of the datum act on
  the lattice roots by the lattice reflections `x ↦ x - (x, α) α`.
* `TauCeti.DynkinType.norm_rootLattice_eq_two_iff`: **a lattice vector has norm `2` exactly when it
  is a root of the pinned datum.**
* `TauCeti.DynkinType.rootLatticeRootEquiv`: the root indices `Fin t.numRoots` enumerate the
  norm-`2` shell of the root lattice.
* `TauCeti.DynkinType.representationNumber_rootLattice_two`: the root lattice has exactly
  `t.numRoots` vectors of norm `2`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. VI, §1.5 and Plates I--VII.
* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 4, §§6--8,
  where the root lattices `Aₙ`, `Dₙ`, `E₆`, `E₇`, `E₈` are characterized by their norm-`2`
  vectors.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §10.3.
-/

public section

namespace TauCeti.DynkinType

open IntegralLattice _root_.Matrix

variable (t : DynkinType) (ht : t.IsSimplyLaced) (hv : t.Valid)

include ht in
/-- The integral Cartan form of a simply-laced type is positive definite. -/
private theorem cartanNorm_pos {w : Fin t.rank → ℤ} (hw : w ≠ 0) :
    0 < (w ᵥ* t.cartanMatrix) ⬝ᵥ w := by
  have h := (isPosDef_iff _).mp (t.isPosDef_rootLattice ht) (fun j ↦ (w j : ℚ)) fun h ↦
    hw (funext fun j ↦ by simpa using congrFun h j)
  rw [form_rootLattice_intCast] at h
  exact_mod_cast h

/-- **The root with index `k` as a vector of the root lattice**: the vector whose simple-root
coordinates are those of the coroot with index `k` in the simple-coroot basis, which by
`TauCeti.DynkinType.root_eq_sum_coroot_smul_root_simpleIndex` are the simple-root coordinates of the
root itself. -/
noncomputable def rootLatticeRoot (k : Fin t.numRoots) : t.rootLattice ht :=
  ⟨fun j ↦ ((t.simplyConnectedRootDatum hv).coroot k j : ℚ),
    (t.mem_rootLattice_carrier_iff ht _).mpr fun _ ↦ ⟨_, rfl⟩⟩

/-- The coordinates of a lattice root are those of the corresponding coroot. -/
@[simp]
theorem coe_rootLatticeRoot_apply (k : Fin t.numRoots) (j : Fin t.rank) :
    (t.rootLatticeRoot ht hv k : Fin t.rank → ℚ) j =
      ((t.simplyConnectedRootDatum hv).coroot k j : ℚ) :=
  (rfl)

/-- The lattice roots at the Bourbaki simple indices are the simple roots. -/
@[simp]
theorem rootLatticeRoot_simpleIndex (i : Fin t.rank) :
    t.rootLatticeRoot ht hv (t.simpleIndex hv i) = t.simpleRootBasis ht i := by
  ext j
  simp [Pi.single_apply]

/-- Distinct root indices give distinct lattice roots. -/
theorem rootLatticeRoot_injective : Function.Injective (t.rootLatticeRoot ht hv) := by
  intro k l h
  refine (t.simplyConnectedRootDatum hv).coroot.injective (funext fun j ↦ ?_)
  have h' := congrArg (fun x : t.rootLattice ht ↦ (x : Fin t.rank → ℚ) j) h
  simp only [coe_rootLatticeRoot_apply, Int.cast_inj] at h'
  exact h'

/-- **The lattice form of two roots is the pairing of the pinned datum.** -/
@[simp]
theorem form_rootLatticeRoot (k l : Fin t.numRoots) :
    (t.rootLattice ht).form (t.rootLatticeRoot ht hv k) (t.rootLatticeRoot ht hv l) =
      (t.simplyConnectedRootDatum hv).pairing k l := by
  rw [t.pairing_eq_coroot_vecMul_dotProduct hv ht]
  exact t.form_rootLattice_intCast ht _ _

/-- **Every root has norm `2`.** -/
@[simp]
theorem norm_rootLatticeRoot (k : Fin t.numRoots) :
    (t.rootLattice ht).norm (t.rootLatticeRoot ht hv k) = 2 := by
  rw [norm_apply, form_rootLatticeRoot, RootPairing.pairing_same]
  norm_num

/-- **The Weyl reflections of the pinned datum are the lattice reflections**: reflecting the root
with index `l` in the root with index `k` gives `x - (x, α) α`, where `x` and `α` are the lattice
roots of `l` and `k`. -/
theorem rootLatticeRoot_reflectionPerm (k l : Fin t.numRoots) :
    t.rootLatticeRoot ht hv ((t.simplyConnectedRootDatum hv).reflectionPerm k l) =
      t.rootLatticeRoot ht hv l -
        (t.simplyConnectedRootDatum hv).pairing k l • t.rootLatticeRoot ht hv k := by
  ext j
  simp [RootPairing.coreflection_apply_coroot]

include ht in
/-- The integral Cartan norm of `u - eᵢ` is `(u, u) - 2 (u, αᵢ) + 2`. -/
private theorem cartanNorm_sub_single (u : Fin t.rank → ℤ) (i : Fin t.rank) :
    ((u - Pi.single i 1) ᵥ* t.cartanMatrix) ⬝ᵥ (u - Pi.single i 1) =
      (u ᵥ* t.cartanMatrix) ⬝ᵥ u - 2 * (u ᵥ* t.cartanMatrix) i + 2 := by
  have h : (Pi.single i 1 ᵥ* t.cartanMatrix) ⬝ᵥ u = (u ᵥ* t.cartanMatrix) i := by
    rw [vecMul_dotProduct_comm ht.isSymm_cartanMatrix, dotProduct_single, mul_one]
  rw [sub_vecMul, sub_dotProduct, dotProduct_sub, dotProduct_sub, h, dotProduct_single,
    dotProduct_single, single_one_vecMul, row_apply, cartanMatrix_apply_same]
  ring

include ht in
/-- The integral form of the descent: a coordinate vector whose integral Cartan norm is `2` is the
coordinate vector of a coroot. The induction is on the sum `m` of the absolute values of the
coordinates. -/
private theorem exists_coroot_eq_of_cartanNorm_eq_two :
    ∀ (m : ℕ) (v : Fin t.rank → ℤ), ∑ i, (v i).natAbs = m →
      (v ᵥ* t.cartanMatrix) ⬝ᵥ v = 2 → ∃ k, (t.simplyConnectedRootDatum hv).coroot k = v := by
  set P := t.simplyConnectedRootDatum hv
  set C := t.cartanMatrix
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  -- The positive case `uᵢ > 0` and `(u, αᵢ) > 0`: either `u = eᵢ`, or `(u, αᵢ) = 1` and
  -- `u - eᵢ` is a coroot of smaller size whose simple reflection is `u`.
  have key (u : Fin t.rank → ℤ) (hum : ∑ i, (u i).natAbs = m) (hu : (u ᵥ* C) ⬝ᵥ u = 2)
      (i : Fin t.rank) (hui : 0 < u i) (hai : 0 < (u ᵥ* C) i) : ∃ k, P.coroot k = u := by
    set w := u - Pi.single i 1 with hw
    have hnorm : (w ᵥ* C) ⬝ᵥ w = 4 - 2 * (u ᵥ* C) i := by
      rw [hw, t.cartanNorm_sub_single ht, hu]
      ring
    by_cases hw0 : w = 0
    · exact ⟨t.simpleIndex hv i, by rw [coroot_simpleIndex]; exact (sub_eq_zero.mp hw0).symm⟩
    have hpos : 0 < (w ᵥ* C) ⬝ᵥ w := t.cartanNorm_pos ht hw0
    have ha : (u ᵥ* C) i = 1 := by omega
    have hlt : ∑ j, (w j).natAbs < m := by
      rw [← hum]
      refine Finset.sum_lt_sum (fun j _ ↦ ?_) ⟨i, Finset.mem_univ _, ?_⟩
      · by_cases hj : j = i
        · subst hj; simp [hw]; omega
        · simp [hw, hj]
      · simp [hw]; omega
    obtain ⟨k, hk⟩ := ih _ hlt w rfl (by rw [hnorm, ha]; norm_num)
    refine ⟨P.reflectionPerm (t.simpleIndex hv i) k, ?_⟩
    rw [t.coroot_reflectionPerm_simpleIndex hv ht, hk, hw, sub_vecMul, single_one_vecMul,
      Pi.sub_apply, row_apply, cartanMatrix_apply_same, ha]
    norm_num
  intro v hvm hv2
  -- Some coordinate `vᵢ` has the same sign as `(v, αᵢ)`, since `∑ vᵢ (v, αᵢ) = 2`.
  obtain ⟨i, -, hi⟩ : ∃ i ∈ Finset.univ, (0 : ℤ) < (v ᵥ* C) i * v i := by
    refine Finset.exists_lt_of_sum_lt ?_
    simp only [dotProduct] at hv2
    rw [Finset.sum_const_zero, hv2]
    norm_num
  rcases pos_and_pos_or_neg_and_neg_of_mul_pos hi with ⟨ha, hvi⟩ | ⟨ha, hvi⟩
  · exact key v hvm hv2 i hvi ha
  -- The negative case reduces to the positive one for `-v`, and `-(-v)` is the reflection of the
  -- coroot `-v` in itself.
  obtain ⟨k, hk⟩ := key (-v) (by simpa using hvm)
    (by rw [neg_vecMul, neg_dotProduct, dotProduct_neg, neg_neg, hv2]) i (by simpa using hvi)
    (by simpa [neg_vecMul] using ha)
  exact ⟨P.reflectionPerm k k, by
    rw [RootPairing.coroot_reflectionPerm, RootPairing.coreflection_apply_self, hk, neg_neg]⟩

/-- **A vector of the root lattice has norm `2` exactly when it is a root** of the pinned simply
connected root datum, written in simple-root coordinates. -/
theorem norm_rootLattice_eq_two_iff (x : t.rootLattice ht) :
    (t.rootLattice ht).norm x = 2 ↔ ∃ k, t.rootLatticeRoot ht hv k = x := by
  refine ⟨fun hx ↦ ?_, by rintro ⟨k, rfl⟩; exact t.norm_rootLatticeRoot ht hv k⟩
  choose v hv' using (t.mem_rootLattice_carrier_iff ht _).mp x.property
  have hcast : (fun j ↦ (v j : ℚ)) = (x : Fin t.rank → ℚ) := funext hv'
  have hnorm : (v ᵥ* t.cartanMatrix) ⬝ᵥ v = 2 := by
    have h := t.norm_rootLattice_intCast ht v
    rw [hcast, hx] at h
    exact_mod_cast h.symm
  obtain ⟨k, hk⟩ := t.exists_coroot_eq_of_cartanNorm_eq_two ht hv _ v rfl hnorm
  refine ⟨k, Subtype.ext (funext fun j ↦ ?_)⟩
  rw [coe_rootLatticeRoot_apply, hk, hv']

/-- **The root indices enumerate the norm-`2` shell of the root lattice.** -/
noncomputable def rootLatticeRootEquiv : Fin t.numRoots ≃ (t.rootLattice ht).vectorsOfNorm 2 :=
  Equiv.ofBijective
    (fun k ↦ ⟨t.rootLatticeRoot ht hv k, mem_vectorsOfNorm.mpr (t.norm_rootLatticeRoot ht hv k)⟩)
    ⟨fun _ _ h ↦ t.rootLatticeRoot_injective ht hv (congrArg Subtype.val h), fun x ↦ by
      obtain ⟨k, hk⟩ := (t.norm_rootLattice_eq_two_iff ht hv x.1).mp (mem_vectorsOfNorm.mp x.2)
      exact ⟨k, Subtype.ext hk⟩⟩

/-- The shell equivalence sends each index to its lattice root. -/
@[simp]
theorem coe_rootLatticeRootEquiv_apply (k : Fin t.numRoots) :
    (t.rootLatticeRootEquiv ht hv k : t.rootLattice ht) = t.rootLatticeRoot ht hv k :=
  (rfl)

include hv in
/-- **The root lattice of a valid simply-laced type has exactly `t.numRoots` vectors of norm
`2`**: `n(n+1)` for `Aₙ`, `2n(n-1)` for `Dₙ`, and `72`, `126`, `240` for `E₆`, `E₇`, `E₈`. -/
@[simp]
theorem representationNumber_rootLattice_two :
    (t.rootLattice ht).representationNumber 2 = t.numRoots := by
  rw [representationNumber_def, ← Nat.card_coe_set_eq,
    ← Nat.card_congr (t.rootLatticeRootEquiv ht hv), Nat.card_eq_fintype_card, Fintype.card_fin]

end TauCeti.DynkinType

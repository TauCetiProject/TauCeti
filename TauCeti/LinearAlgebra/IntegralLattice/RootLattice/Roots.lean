/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.PosDef.RepresentationNumber
public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.Dynkin
public import TauCeti.LinearAlgebra.Matrix.NormTwoShell
public import TauCeti.LinearAlgebra.Matrix.PosDef.Basic
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
because the pairing of a root with its own coroot is `2`.  Conversely, the coordinate vectors of
the norm-`2` vectors form the norm-two shell `Matrix.normTwoShell` of the Cartan matrix, whose
vectors have coordinates of one sign (`Matrix.PosDef.nonneg_or_nonpos_of_mem_normTwoShell`).  The
nonnegative ones are reached from the simple roots by adding simple roots
(`Matrix.PosDef.normTwoShell_nonneg_induction`), and when `x` and `x + αᵢ` both have norm `2`, the
pairing `(x, αᵢ)` is `-1`, so `x + αᵢ` is the reflection of `x` in `αᵢ`.  A nonpositive vector is
the reflection of its negative in itself.

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
/-- The integral form of the descent: every vector of the norm-two shell of the Cartan matrix is
the coordinate vector of a coroot. -/
private theorem exists_coroot_eq_of_mem_normTwoShell {v : Fin t.rank → ℤ}
    (hv2 : v ∈ t.cartanMatrix.normTwoShell) :
    ∃ k, (t.simplyConnectedRootDatum hv).coroot k = v := by
  set P := t.simplyConnectedRootDatum hv
  have hB : t.cartanMatrix.PosDef :=
    TauCeti.Matrix.posDef_map_intCast_iff.mp ht.posDef_map_intCast_cartanMatrix
  have hoff : ∀ i j, i ≠ j → t.cartanMatrix i j ≤ 0 := fun _ _ ↦ t.cartanMatrix_apply_le_zero_of_ne
  -- The nonnegative vectors of the shell, by height induction: adding `eᵢ` to a coroot `c` stays
  -- in the shell exactly when `(c, αᵢ) = -1`, and then `c + eᵢ` is the simple reflection of `c`.
  have hnonneg (a : Fin t.rank → ℤ) (ha : a ∈ t.cartanMatrix.normTwoShell) (ha0 : 0 ≤ a) :
      ∃ k, P.coroot k = a := by
    refine hB.normTwoShell_nonneg_induction (motive := fun a ↦ ∃ k, P.coroot k = a)
      t.cartanMatrix_apply_same hoff (fun i ↦ ⟨t.simpleIndex hv i, coroot_simpleIndex t hv i⟩)
      (fun a i ha _ hai ⟨k, hk⟩ ↦ ⟨P.reflectionPerm (t.simpleIndex hv i) k, ?_⟩) ha ha0
    have hpair := (hB.isHermitian.isSymm.add_mem_normTwoShell_iff ha
      (single_mem_normTwoShell (t.cartanMatrix_apply_same i))).mp hai
    rw [dotProduct_mulVec, dotProduct_single, mul_one] at hpair
    rw [t.coroot_reflectionPerm_simpleIndex hv ht, hk, hpair, neg_one_smul, sub_neg_eq_add]
  rcases hB.nonneg_or_nonpos_of_mem_normTwoShell
      (fun i ↦ ⟨1, by rw [t.cartanMatrix_apply_same]; rfl⟩) hoff hv2 with h | h
  · exact hnonneg v hv2 h
  -- A nonpositive vector is `-(-v)`, the reflection of the coroot `-v` in itself.
  obtain ⟨k, hk⟩ := hnonneg (-v) (neg_mem_normTwoShell.mpr hv2) (neg_nonneg.mpr h)
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
  obtain ⟨k, hk⟩ := t.exists_coroot_eq_of_mem_normTwoShell ht hv
    (mem_normTwoShell.mpr (by rw [dotProduct_mulVec]; exact hnorm))
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

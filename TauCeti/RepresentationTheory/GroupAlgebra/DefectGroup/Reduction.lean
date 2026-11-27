/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Nakayama
public import TauCeti.RepresentationTheory.GroupAlgebra.DefectGroup.Basic
public import TauCeti.RepresentationTheory.GroupAlgebra.OrbitSum

/-!
# Defect groups and reduction of coefficients

Let `π : R → S` be a surjective homomorphism of commutative rings whose kernel lies in the Jacobson
radical `Ring.jacobson R`, for instance the reduction `O → k` of a complete discrete valuation
ring onto its residue field. For a finite group `G`, an idempotent `b` of the centre `R[G]^G`
and a subgroup `P`, `b ∈ Tr_P^G(R[G]^P)` exactly when its reduction `π(b)` lies in `Tr_P^G(S[G]^P)`
(`TauCeti.mem_relTraceIdeal_iff_conjInvariantsMap_mem`).

The forward implication is that reduction commutes with relative traces. Conversely, if
`π(b) = Tr_P^G(a')`, lift `a'` to `a ∈ R[G]^P`; then `t = b Tr_P^G(a)` lies in the ideal
`T = Tr_P^G(R[G]^P)` and reduces to `π(b)`, so `b − t` has all coordinates in `ker π` in the
basis of class sums. Hence `Z b = T b + (ker π) Z b` for `Z = R[G]^G`, and Nakayama's lemma for
the finitely generated `R`-module `Z b` gives `Z b = T b`, so `b ∈ T`.

So the defect groups of the reduction of a block idempotent `b`, read through the minimal trace
subgroups of `π(b)` (`TauCeti.isDefectGroup_iff_minimal`), are exactly the subgroups `D` minimal
with `b ∈ Tr_D^G(R[G]^D)` (`TauCeti.isDefectGroup_conjInvariantsMap_iff_minimal`; Webb, §12.3,
p. 235, and Theorem 12.4.5, p. 241).

## Main results

* `TauCeti.mem_relTraceIdeal_iff_conjInvariantsMap_mem`: a central idempotent is a trace from `P`
  exactly when its reduction is.
* `TauCeti.isDefectGroup_conjInvariantsMap_iff_minimal`: the defect groups of the reduction of a
  central idempotent with primitive reduction are the minimal subgroups `D` with
  `b ∈ Tr_D^G(R[G]^D)`.

## References

* P. Webb, *A Course in Finite Group Representation Theory*, §12.3, p. 235, and Theorem 12.4.5,
  p. 241.
-/

public section

namespace TauCeti

open MonoidAlgebra

variable {R S G : Type*} [CommRing R] [CommRing S] [Group G] [Finite G] {π : R →+* S}

/-- **A central idempotent is a trace from `P` exactly when its reduction is.** Let
`π : R → S` be a surjective homomorphism of commutative rings whose kernel lies in the Jacobson
radical of `R`, and `b` an idempotent of `R[G]^G`, `G` finite. Then `b ∈ Tr_P^G(R[G]^P)` exactly
when its reduction lies in `Tr_P^G(S[G]^P)`. -/
theorem mem_relTraceIdeal_iff_conjInvariantsMap_mem (hπ : Function.Surjective π)
    (hker : RingHom.ker π ≤ Ring.jacobson R) {b : conjInvariants R (⊤ : Subgroup G)}
    (hb : IsIdempotentElem b) {P : Subgroup G} :
    b ∈ relTraceIdeal R (le_top : P ≤ ⊤) ↔
      conjInvariantsMap π ⊤ b ∈ relTraceIdeal S (le_top : P ≤ ⊤) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨a, ha⟩ := (mem_relTraceIdeal_iff le_top).1 h
    exact (mem_relTraceIdeal_iff le_top).2
      ⟨conjInvariantsMap π P a, by rw [← ha, conjInvariantsMap_relTrace]⟩
  obtain ⟨a', ha'⟩ := (mem_relTraceIdeal_iff le_top).1 h
  obtain ⟨a, rfl⟩ := conjInvariantsMap_surjective π hπ P a'
  set T := relTraceIdeal R (le_top : P ≤ ⊤)
  set t := b * relTrace R P ⊤ a
  have htT : t ∈ T := T.mul_mem_left b (relTrace_mem_relTraceIdeal _ a)
  have htb : t * b = t := by rw [mul_comm, ← mul_assoc, hb.eq]
  have hbt : b - t ∈ RingHom.ker π • (⊤ : Submodule R (conjInvariants R (⊤ : Subgroup G))) := by
    refine mem_smul_top_of_conjInvariantsMap_eq_zero π ?_
    rw [map_sub, map_mul, conjInvariantsMap_relTrace, ha',
      (hb.map (conjInvariantsMap π ⊤)).eq, sub_self]
  -- Nakayama's lemma for `M = Z b` and `N = T b` with `Z = R[G]^G`.
  let f := LinearMap.mulRight R b
  let M := Submodule.map f ⊤
  let N := Submodule.map f (T.restrictScalars R)
  have hM : M.FG := Submodule.FG.map f
    (Module.Finite.fg_top (R := R) (M := conjInvariants R (⊤ : Subgroup G)))
  have hMN : M ≤ N ⊔ RingHom.ker π • M := by
    rintro _ ⟨z, -, rfl⟩
    have hsplit : f z = f (z * t) + f (z * (b - t)) := by
      simp only [f, LinearMap.mulRight_apply, mul_sub, sub_mul, mul_assoc, htb, hb.eq]
      abel
    rw [hsplit]
    refine Submodule.add_mem_sup ⟨z * t, T.mul_mem_left z htT, rfl⟩ ?_
    have hz : z * (b - t) ∈ RingHom.ker π • (⊤ : Submodule R (conjInvariants R ⊤)) := by
      have := Submodule.mem_map_of_mem (f := LinearMap.mulLeft R z) hbt
      rw [Submodule.map_smul''] at this
      exact Submodule.smul_mono le_rfl le_top this
    have := Submodule.mem_map_of_mem (f := f) hz
    rwa [Submodule.map_smul''] at this
  obtain ⟨y, hy, hyb⟩ := Submodule.mem_map.1 (Submodule.le_of_le_smul_of_le_jacobson hM hker hMN
    (show b ∈ M from ⟨b, Submodule.mem_top, hb.eq⟩))
  rw [← hyb]
  exact T.mul_mem_right b ((Submodule.restrictScalars_mem R T y).1 hy)

/-- **Defect groups through a lift.** Let `π : R → S` be a surjective homomorphism of commutative
rings whose kernel lies in the Jacobson radical of `R`, with `S` Artinian of characteristic `p`,
and `b` an idempotent of `R[G]^G` whose reduction `π(b)` is primitive in `S[G]^G`, for instance a
block idempotent of `O[G]` for a complete discrete valuation ring `O` with residue field `k`. Then
the defect groups of `π(b)` are exactly the subgroups `D` minimal with `b ∈ Tr_D^G(R[G]^D)`. -/
theorem isDefectGroup_conjInvariantsMap_iff_minimal [IsArtinianRing S] {p : ℕ} [Fact p.Prime]
    [CharP S p] (hπ : Function.Surjective π) (hker : RingHom.ker π ≤ Ring.jacobson R)
    {b : conjInvariants R (⊤ : Subgroup G)} (hb : IsIdempotentElem b)
    (he : IsPrimitiveIdempotent (conjInvariantsMap π ⊤ b)) {D : Subgroup G} :
    IsDefectGroup S p (conjInvariantsMap π ⊤ b : MonoidAlgebra S G) D ↔
      Minimal (fun Q : Subgroup G => b ∈ relTraceIdeal R (le_top : Q ≤ ⊤)) D := by
  rw [isDefectGroup_iff_minimal he]
  simp only [mem_relTraceIdeal_iff_conjInvariantsMap_mem hπ hker hb]

end TauCeti

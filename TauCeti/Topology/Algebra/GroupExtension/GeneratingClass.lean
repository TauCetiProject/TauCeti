/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.GroupExtension.Cohomology
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.PadicPow
import TauCeti.Algebra.Group.Subgroup.ZPowers
import TauCeti.NumberTheory.Padics.PadicIntegers

/-!
# Lifting surjections after comparing generating extension classes

A continuous equivariant surjection between the kernels of two profinite extensions need
not carry the source extension class to the target class. If its image class and the target
class both generate the same finite cyclic `p`-group, a prime-to-`p` power of the coefficient
map does carry one class to the other. For a pro-`p` target kernel this power is an
automorphism, so the corrected coefficient map remains surjective and lifts to a continuous
surjection of extensions.

This turns the cohomological comparison of relation-module maps into a surjection of groups:
the correction changes the coefficient map, but not its image or its kernel.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed.,
  I §5 Exercise 4 and the proof of (7.4.1).
-/

public section

namespace TauCeti.ProfiniteGroupExtension

open ContCohomology

variable {p : ℕ} [Fact p.Prime]
  {G M N : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]
  [CommGroup M] [TopologicalSpace M]
  [MulDistribMulAction G M] [ContinuousSMul G M] [CompactSpace M]
  [CommGroup N] [TopologicalSpace N] [IsTopologicalGroup N]
  [MulDistribMulAction G N] [ContinuousSMul G N] [CompactSpace N]
  [TotallyDisconnectedSpace N]

/-- A continuous equivariant surjection to a pro-`p` kernel lifts to a continuous surjection
of extensions after a prime-to-`p` power correction, provided its image extension class and
the target class generate the same finite `p`-power-order cohomology group.

The lifted homomorphism covers the identity on the quotient and restricts to `m ↦ (f m)^n`
on the kernels. In particular, the correction retains the kernel of `f`. -/
theorem exists_surjective_continuousMonoidHom_of_generating_classes
    (X : ProfiniteGroupExtension G M) (Y : ProfiniteGroupExtension G N)
    (hN : IsProP p N) (f : M →*[G] N) (hf : Continuous f) (hs : Function.Surjective f)
    (hx : AddSubgroup.zmultiples (X.map f hf).contCohomologyClass = ⊤)
    (hy : AddSubgroup.zmultiples Y.contCohomologyClass = ⊤)
    (hcard : ∃ r : ℕ, Nat.card (H2 G (Additive N)) = p ^ r) :
    ∃ (n : ℕ) (φ : X.E →ₜ* Y.E), p.Coprime n ∧ Function.Surjective φ ∧
      (∀ m, φ (X.toGroupExtension.inl m) = Y.toGroupExtension.inl ((f m) ^ n)) ∧
      Y.toGroupExtension.rightHom.comp φ.toMonoidHom = X.toGroupExtension.rightHom := by
  obtain ⟨r, hr⟩ := hcard
  have : Finite (H2 G (Additive N)) := Nat.finite_of_card_ne_zero <| by
    rw [hr]
    exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero
  -- The trivial cohomology group needs no correction; taking exponent one also avoids
  -- inferring coprimality to `p` from coprimality to its zeroth power.
  obtain ⟨n, hn, hclass⟩ : ∃ n : ℕ, p.Coprime n ∧
      n • (X.map f hf).contCohomologyClass = Y.contCohomologyClass := by
    by_cases hzero : r = 0
    · have : Subsingleton (H2 G (Additive N)) := Nat.card_eq_one_iff_unique.mp
        (by simpa [hzero] using hr) |>.1
      exact ⟨1, Nat.coprime_one_right _, Subsingleton.elim _ _⟩
    · obtain ⟨k, hk, heq⟩ := AddSubgroup.exists_coprime_zsmul_of_generators
        (X.map f hf).contCohomologyClass Y.contCohomologyClass hx hy
      let n := (k % (Nat.card (H2 G (Additive N)) : ℤ)).natAbs
      have hn : (Nat.card (H2 G (Additive N))).Coprime n := by
        apply Nat.Coprime.symm
        simpa only [Int.gcd_def, Int.natAbs_natCast] using
          (Int.gcd_emod k (Nat.card (H2 G (Additive N)))).trans hk
      have heq' : n • (X.map f hf).contCohomologyClass = Y.contCohomologyClass := by
        rw [heq, ← natCast_zsmul, Int.natAbs_of_nonneg
          (Int.emod_nonneg _ (Int.natCast_ne_zero.mpr Nat.card_pos.ne')),
          mod_natCard_zsmul]
      rw [hr] at hn
      exact ⟨n, (Nat.coprime_pow_left_iff (Nat.pos_of_ne_zero hzero) p n).mp hn, heq'⟩
  let q : N →*[G] N :=
    { powMonoidHom n with map_smul' := fun g z ↦ (smul_pow' g z n).symm }
  have hq_apply (z : N) : q z = z ^ n := (rfl)
  have hq : Continuous q := (continuous_pow n).congr fun z ↦ (hq_apply z).symm
  -- A prime-to-`p` natural number is a p-adic unit, whose power map is a homeomorphism.
  have hqs : Function.Surjective q := by
    obtain ⟨u, hu⟩ := PadicInt.isUnit_natCast_of_coprime hn
    intro z
    obtain ⟨w, hw⟩ := (hN.padicPowHomeomorph u).surjective z
    exact ⟨w, (hq_apply w).trans <| by simpa [hu] using hw⟩
  have hqf : Continuous (q.comp f) := hq.comp hf
  -- The compact source kernel inherits continuous group operations from its inclusion.
  let : IsTopologicalGroup M :=
    Topology.IsInducing.isTopologicalGroup X.toGroupExtension.inl
      (X.continuous_inl.isClosedEmbedding X.toGroupExtension.inl_injective).isEmbedding.isInducing
  have hmap : (X.map (q.comp f) hqf).contCohomologyClass =
      Y.contCohomologyClass := by
    refine (X.contCohomologyClass_map (q.comp f) hqf).trans ?_
    simp only [MulDistribMulActionHom.toAdditive_comp]
    rw [explicitCoeff2_comp]
    exact (explicitCoeff2_eq_nsmul G (Additive N) q.toAdditive (k := n)
      (q.continuous_toAdditive hq) (fun z ↦ by simp [hq_apply]) _).trans <| by
        simpa only [contCohomologyClass_map] using hclass
  obtain ⟨φ, hφ, hinl, hright⟩ :=
    X.exists_continuous_monoidHom_of_contCohomologyClass_map_eq (q.comp f) hqf Y hmap
  refine ⟨n, ⟨φ, hφ⟩, hn,
    GroupExtension.surjective_of_comp_inl_eq
      (q.comp f).toMonoidHom (hqs.comp hs) φ hinl hright, ?_, hright⟩
  intro m
  simpa [hq_apply] using DFunLike.congr_fun hinl m

end TauCeti.ProfiniteGroupExtension

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupExtension.KernelMap
public import TauCeti.Topology.Algebra.GroupExtension.GeneratingClass

/-!
# From a weak comparison to a surjection of profinite extensions

Suppose two profinite extensions have second cohomology groups of the same finite order,
and the target extension class generates its group. Any continuous homomorphism between the
extensions over the identity of the quotient, even a nonsurjective one, shows that the source
extension class also generates. Its restriction to the kernels is a continuous equivariant
coefficient map carrying the source class to the target class.

Consequently, a different continuous equivariant surjection on kernels, inducing an
isomorphism on second cohomology, lifts after a prime-to-`p` power correction to a surjection
of extensions when the target kernel is pro-`p` and its second cohomology has `p`-power order.
This separates the weak comparison used to detect a generating class from the coefficient
surjection one needs to lift.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed.,
  I §5 Exercise 4 and the proof of (7.4.1).
-/

public section

namespace TauCeti.ProfiniteGroupExtension

open ContCohomology

variable {G M N : Type*} [Group G] [TopologicalSpace G]
  [CommGroup M] [TopologicalSpace M] [MulDistribMulAction G M]
  [CommGroup N] [TopologicalSpace N] [MulDistribMulAction G N]
  (X : ProfiniteGroupExtension G M) (Y : ProfiniteGroupExtension G N)
  (φ : X.E →ₜ* Y.E)
  (hright : Y.toGroupExtension.rightHom.comp φ.toMonoidHom = X.toGroupExtension.rightHom)

/-- Restrict a continuous homomorphism of profinite extensions over the identity of the quotient
to their kernels, with their prescribed quotient actions. -/
noncomputable def equivariantKernelMap : M →*[G] N where
  __ := X.toGroupExtension.kernelMap Y.toGroupExtension φ.toMonoidHom hright
  map_smul' g m := by
    apply Y.toGroupExtension.inl_injective
    -- The equivariant-hom constructor reads the monoid hom through its `MulHom` projection.
    change Y.toGroupExtension.inl
        (X.toGroupExtension.kernelMap Y.toGroupExtension φ.toMonoidHom hright (g • m)) =
      Y.toGroupExtension.inl
        (g • X.toGroupExtension.kernelMap Y.toGroupExtension φ.toMonoidHom hright m)
    let σ := X.toGroupExtension.surjInvRightHom
    rw [GroupExtension.inl_kernelMap,
      GroupExtension.inl_smul σ X.inducesAction,
      GroupExtension.inl_smul (σ.monoidHomComp φ.toMonoidHom hright) Y.inducesAction]
    simp

/-- The equivariant kernel restriction agrees with the original map after inclusion. -/
@[simp]
theorem inl_equivariantKernelMap (m : M) :
    Y.toGroupExtension.inl (X.equivariantKernelMap Y φ hright m) =
      φ (X.toGroupExtension.inl m) :=
  GroupExtension.inl_kernelMap _ _ _ _ m

/-- The restriction of a continuous homomorphism of profinite extensions to their kernels is
continuous when the target kernel is compact. -/
theorem continuous_equivariantKernelMap [CompactSpace N] :
    Continuous (X.equivariantKernelMap Y φ hright) := by
  let hinl := (Y.continuous_inl.isClosedEmbedding Y.toGroupExtension.inl_injective).isEmbedding
  apply hinl.continuous_iff.mpr
  exact (φ.continuous.comp X.continuous_inl).congr
    (fun m ↦ (X.inl_equivariantKernelMap Y φ hright m).symm)

-- Explicit H² and its coefficient maps require topological group structures on both kernels.
variable [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
  [IsTopologicalGroup M] [ContinuousSMul G M] [CompactSpace M]
  [IsTopologicalGroup N] [ContinuousSMul G N] [CompactSpace N]
  [TotallyDisconnectedSpace N]

omit [IsTopologicalGroup M] [ContinuousSMul G M] in
/-- The kernel restriction of a weak comparison carries the source extension class to the
target extension class. -/
@[simp]
theorem contCohomologyClass_map_equivariantKernelMap :
    (X.map (X.equivariantKernelMap Y φ hright)
      (X.continuous_equivariantKernelMap Y φ hright)).contCohomologyClass =
        Y.contCohomologyClass :=
  X.contCohomologyClass_map_eq_of_continuous_monoidHom _ _ Y φ.toMonoidHom φ.continuous
    (MonoidHom.ext fun m ↦ (X.inl_equivariantKernelMap Y φ hright m).symm) hright

include φ hright

/-- A weak comparison of extensions detects a generating source class when the two second
cohomology groups have the same finite order and the target class generates. No surjectivity
of the comparison or its restriction to the kernels is assumed. -/
theorem zmultiples_contCohomologyClass_eq_top_of_comparison
    [Finite (H2 G (Additive M))]
    (hcard : Nat.card (H2 G (Additive M)) = Nat.card (H2 G (Additive N)))
    (hy : AddSubgroup.zmultiples Y.contCohomologyClass = ⊤) :
    AddSubgroup.zmultiples X.contCohomologyClass = ⊤ := by
  let k := X.equivariantKernelMap Y φ hright
  let c := explicitCoeff2 G (Additive M) k.toAdditive
    (k.continuous_toAdditive (X.continuous_equivariantKernelMap Y φ hright))
  have hc : c X.contCohomologyClass = Y.contCohomologyClass := by
    rw [← X.contCohomologyClass_map k (X.continuous_equivariantKernelMap Y φ hright),
      X.contCohomologyClass_map_equivariantKernelMap Y φ hright]
  have hsurj : Function.Surjective c := by
    intro y
    obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp (hy.ge (AddSubgroup.mem_top y))
    exact ⟨n • X.contCohomologyClass, by simpa [hc] using hn⟩
  have hbij := hsurj.bijective_of_nat_card_le hcard.le
  apply AddSubgroup.map_injective hbij.injective
  rw [c.map_zmultiples, hc, hy, AddSubgroup.map_top_of_surjective _ hbij.surjective]

/-- A weak comparison and a cohomologically bijective surjection on kernels give a continuous
surjection of extensions after a prime-to-`p` power correction. The weak comparison need not
be surjective and need not restrict to the given coefficient map.

The corrected map covers the identity on the quotient and restricts to `m ↦ (f m)^n` on
kernels, with `n` coprime to `p`. -/
theorem exists_surjective_continuousMonoidHom_of_comparison
    {p : ℕ} [Fact p.Prime] (hN : IsProP p N)
    (f : M →*[G] N) (hf : Continuous f) (hs : Function.Surjective f)
    (hc : Function.Bijective
      (explicitCoeff2 G (Additive M) f.toAdditive (f.continuous_toAdditive hf)))
    (hy : AddSubgroup.zmultiples Y.contCohomologyClass = ⊤)
    (hcard : ∃ r : ℕ, Nat.card (H2 G (Additive N)) = p ^ r) :
    ∃ (n : ℕ) (ψ : X.E →ₜ* Y.E), p.Coprime n ∧ Function.Surjective ψ ∧
      (∀ m, ψ (X.toGroupExtension.inl m) = Y.toGroupExtension.inl ((f m) ^ n)) ∧
      Y.toGroupExtension.rightHom.comp ψ.toMonoidHom = X.toGroupExtension.rightHom := by
  let c := explicitCoeff2 G (Additive M) f.toAdditive (f.continuous_toAdditive hf)
  let e := AddEquiv.ofBijective c hc
  have horder : Nat.card (H2 G (Additive M)) = Nat.card (H2 G (Additive N)) :=
    Nat.card_congr e.toEquiv
  have : Finite (H2 G (Additive M)) := Nat.finite_of_card_ne_zero <| by
    obtain ⟨r, hr⟩ := hcard
    rw [horder, hr]
    exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero
  have hx := X.zmultiples_contCohomologyClass_eq_top_of_comparison Y φ hright horder hy
  have hfx : AddSubgroup.zmultiples (X.map f hf).contCohomologyClass = ⊤ := by
    rw [contCohomologyClass_map, ← c.map_zmultiples, hx, AddSubgroup.map_top]
    exact AddMonoidHom.range_eq_top.mpr hc.surjective
  exact X.exists_surjective_continuousMonoidHom_of_generating_classes Y hN f hf hs hfx hy hcard

end TauCeti.ProfiniteGroupExtension

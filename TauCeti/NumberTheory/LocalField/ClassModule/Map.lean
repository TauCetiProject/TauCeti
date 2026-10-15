/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.ClassModule.Basic
public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologicalDimension.ClassModule.Naturality
public import TauCeti.Topology.Algebra.Group.Profinite.Free.Basic
public import TauCeti.Topology.Algebra.ContinuousMonoidHom.QuotientKerEquiv
import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologicalDimension.ClassModule.ClassIdentification

/-!
# Second cohomology of maps to local Galois class modules

Let `W` be an open normal subgroup of a local absolute Galois group `G_K`. Any continuous
map `G → G_K` inducing an isomorphism `G/V ≃ G_K/W` is onto on second cohomology of the
pro-`p` class modules, for a prime `p` invertible in `K`. The arithmetic extension class
generates, and naturality supplies a preimage of that generator.

In particular, lifts of a generating family of `G_K/W` to `G_K` induce a surjection on
second cohomology from its pro-`p` relation group to the arithmetic class module.
Surjectivity of the lift to `G_K` is not needed. For a surjective free presentation this
is the input for proving projectivity of the kernel of the induced integral relation-module map.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed.,
  (3.6.4)(iii) and the proof of (7.4.2)(i).
-/

public section

namespace TauCeti

open ContCohomology

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [ValuativeRel K]
  [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (hp : IsUnit (p : K)) {W : Subgroup (Field.absoluteGaloisGroup K)} [W.Normal]
  (hW : IsOpen (W : Set (Field.absoluteGaloisGroup K)))

include hp hW

/-- A map inducing an isomorphism onto a finite local Galois quotient is surjective on
second cohomology of its pro-`p` class modules. Only the quotient map, not the ambient
homomorphism or its restriction to the kernels, must be an isomorphism. -/
theorem explicitCoeff2_abelianizationProPMapEquivariant_absoluteGaloisGroup_surjective
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G]
    {V : Subgroup G} [V.Normal] [IsClosed (V : Set G)]
    (f : G →* Field.absoluteGaloisGroup K) (hf : Continuous f) (hVW : V ≤ W.comap f)
    (e : G ⧸ V ≃ₜ* Field.absoluteGaloisGroup K ⧸ W)
    (he : ∀ g : G, e (QuotientGroup.mk g) = QuotientGroup.mk (f g)) :
    letI : IsClosed (W : Set (Field.absoluteGaloisGroup K)) := W.isClosed_of_isOpen hW
    letI := MulDistribMulAction.compHom (abelianizationProP p G V) e.symm.toMulEquiv.toMonoidHom
    letI := MulAction.continuousSMul_compHom (X := abelianizationProP p G V)
      (f := e.symm.toMulEquiv.toMonoidHom) e.symm.continuous
    Function.Surjective (explicitCoeff2 (Field.absoluteGaloisGroup K ⧸ W)
      (Additive (abelianizationProP p G V))
      (abelianizationProPMapEquivariant p f hf hVW e he).toAdditive
      ((abelianizationProPMapEquivariant p f hf hVW e he).continuous_toAdditive
        (continuous_abelianizationProPMapEquivariant p f hf hVW e he))) := by
  let : IsClosed (W : Set (Field.absoluteGaloisGroup K)) := W.isClosed_of_isOpen hW
  apply explicitCoeff2_abelianizationProPMapEquivariant_surjective
  rw [abelianizationProPProfiniteExtension_contCohomologyClass p _ W hW]
  exact (contCohomologyClass_absoluteGaloisGroup_generates hp hW).1

/-- Lifts of quotient generators to a local absolute Galois group induce a surjection
on second cohomology from the pro-`p` relation group to the arithmetic class module.
The lift itself need not be surjective onto the absolute Galois group. -/
theorem freeProfiniteGroup.explicitCoeff2_abelianizationProPMapEquivariant_surjective
    {ι : Type} :
    letI : IsClosed (W : Set (Field.absoluteGaloisGroup K)) := W.isClosed_of_isOpen hW
    ∀ (g : ι → Field.absoluteGaloisGroup K ⧸ W)
      (_ : Dense (Subgroup.closure (Set.range g) : Set (Field.absoluteGaloisGroup K ⧸ W)))
      (φ : freeProfiniteGroup ι →ₜ* Field.absoluteGaloisGroup K)
      (_ : ∀ x, (φ x : Field.absoluteGaloisGroup K ⧸ W) = freeProfiniteGroup.lift g x),
    let R := (freeProfiniteGroup.lift g : freeProfiniteGroup ι →*
      Field.absoluteGaloisGroup K ⧸ W).ker
    ∃ (hRW : R ≤ W.comap φ.toMonoidHom)
      (e : freeProfiniteGroup ι ⧸ R ≃ₜ* Field.absoluteGaloisGroup K ⧸ W)
      (he : ∀ x, e (QuotientGroup.mk x) = QuotientGroup.mk (φ x)),
      letI := MulDistribMulAction.compHom (abelianizationProP p (freeProfiniteGroup ι) R)
        e.symm.toMulEquiv.toMonoidHom
      letI := MulAction.continuousSMul_compHom
        (X := abelianizationProP p (freeProfiniteGroup ι) R)
        (f := e.symm.toMulEquiv.toMonoidHom) e.symm.continuous
      Function.Surjective (explicitCoeff2 (Field.absoluteGaloisGroup K ⧸ W)
        (Additive (abelianizationProP p (freeProfiniteGroup ι) R))
        (abelianizationProPMapEquivariant p φ.toMonoidHom φ.continuous hRW e he).toAdditive
        ((abelianizationProPMapEquivariant p φ.toMonoidHom φ.continuous
          hRW e he).continuous_toAdditive
          (continuous_abelianizationProPMapEquivariant p φ.toMonoidHom φ.continuous
            hRW e he))) := by
  let : IsClosed (W : Set (Field.absoluteGaloisGroup K)) := W.isClosed_of_isOpen hW
  intro g hg φ hφ
  let R := (freeProfiniteGroup.lift g : freeProfiniteGroup ι →*
    Field.absoluteGaloisGroup K ⧸ W).ker
  have hRW : R ≤ W.comap φ.toMonoidHom := by
    intro x hx
    rw [Subgroup.mem_comap, ← QuotientGroup.eq_one_iff]
    simpa using (hφ x).trans (MonoidHom.mem_ker.mp hx)
  let e := (freeProfiniteGroup.lift g).quotientKerEquivOfSurjective
    (freeProfiniteGroup.lift_surjective hg)
  have he (x) : e (QuotientGroup.mk x) = QuotientGroup.mk (φ x) :=
    ((freeProfiniteGroup.lift g).quotientKerEquivOfSurjective_apply_mk _ x).trans (hφ x).symm
  refine ⟨hRW, e, he, ?_⟩
  let : IsClosed (R : Set (freeProfiniteGroup ι)) := (freeProfiniteGroup.lift g).isClosed_ker
  exact explicitCoeff2_abelianizationProPMapEquivariant_absoluteGaloisGroup_surjective hp hW
    φ.toMonoidHom φ.continuous hRW e he

end TauCeti

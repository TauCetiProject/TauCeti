/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.MappingPath.Fiber
public import TauCeti.Topology.Homotopy.MappingPath.LiftingFunction
public import TauCeti.Topology.Homotopy.MappingPath.WeakHomotopyEquivalence
public import TauCeti.Topology.Homotopy.SerreFibration.WeakHomotopyEquivalence

/-!
# Strict fibres and mapping-path fibres of Serre fibrations

Every map `p : E → B` factors through its mapping-path replacement `MappingPathSpace p` as the
homotopy equivalence `MappingPathSpace.incl p` followed by the Hurewicz fibration
`MappingPathSpace.endpoint p`. When `p` is a Serre fibration in `TopCat`, this factorization is a
commutative square of Serre fibrations over the identity of `B` whose map of total spaces is a weak
homotopy equivalence. By `TauCeti.TopCat.isWeakHomotopyEquivalence_fiberMap`, the induced map on
every fibre is a weak homotopy equivalence; identifying the endpoint fibre with
`MappingPathFiber p b` shows that `MappingPathFiber.ofFiber p b : p⁻¹(b) → MappingPathFiber p b` is
a weak homotopy equivalence for every `b : B`, including when `p⁻¹(b)` is empty.

## Main results

* `TauCeti.TopCat.isWeakHomotopyEquivalence_ofFiber`: for a Serre fibration `p : E ⟶ B`, the
  constant-path inclusion `p⁻¹(b) → MappingPathFiber p.hom b` is a weak homotopy equivalence for
  every `b : B`.

## References

* A. Hatcher, *Algebraic Topology*, Proposition 4.65.
* G. W. Whitehead, *Elements of Homotopy Theory*, GTM 61, Springer, 1978, Chapters I.7 and IV.8.
-/

public section

open CategoryTheory

universe u

namespace TauCeti.TopCat

/-- **Strict-to-homotopy fibre comparison for Serre fibrations.** For a Serre fibration
`p : E ⟶ B` and any point `b : B` (including when the fibre over `b` is empty), the constant-path
inclusion `MappingPathFiber.ofFiber p.hom b` from the strict fibre `p ⁻¹' {b}` to the mapping-path
fibre `MappingPathFiber p.hom b` is a weak homotopy equivalence. -/
theorem isWeakHomotopyEquivalence_ofFiber {E B : _root_.TopCat.{u}} {p : E ⟶ B}
    (hp : serreFibrations p) (b : B) :
    (MappingPathFiber.ofFiber p.hom b).IsWeakHomotopyEquivalence := by
  let sq : CommSq (_root_.TopCat.ofHom (MappingPathSpace.incl p.hom)) p
      (_root_.TopCat.ofHom (MappingPathSpace.endpoint p.hom)) (𝟙 B) :=
    ⟨_root_.TopCat.ext fun x ↦
      ContinuousMap.congr_fun (MappingPathSpace.endpoint_comp_incl p.hom) x⟩
  have hp' : serreFibrations (_root_.TopCat.ofHom (MappingPathSpace.endpoint p.hom)) :=
    (MappingPathSpace.isHurewiczFibration_endpoint.{0} p.hom).mem_serreFibrations
  let eEnd : MappingPathFiber p.hom b ≃ₜ
      (_root_.TopCat.ofHom (MappingPathSpace.endpoint p.hom)).fiber ((𝟙 B) b) :=
    (MappingPathFiber.endpointHomeomorph p.hom b).trans ((Homeomorph.refl _).subtype (by simp))
  have hcomp :
      (eEnd : C(MappingPathFiber p.hom b,
        (_root_.TopCat.ofHom (MappingPathSpace.endpoint p.hom)).fiber ((𝟙 B) b))).comp
        (MappingPathFiber.ofFiber p.hom b) = (sq.fiberMap b).hom := by
    ext x : 1
    exact Subtype.ext ((MappingPathFiber.endpointHomeomorph_ofFiber_val p.hom b x).trans
      ((_root_.TopCat.ofHom_apply _ _).symm.trans (sq.fiberMap_apply_coe b x).symm))
  exact eEnd.isWeakHomotopyEquivalence.of_postcomp
    (hcomp ▸ isWeakHomotopyEquivalence_fiberMap hp hp' sq
      (MappingPathSpace.isWeakHomotopyEquivalence_incl p.hom) .id b)

end TauCeti.TopCat

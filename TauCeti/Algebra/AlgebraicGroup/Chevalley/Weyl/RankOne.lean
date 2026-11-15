/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Root.Subgroup
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.Coroot
import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Weyl.RankOne

/-!
# The rank-one Steinberg conjugation relation

For every numbered root of a Chevalley datum, Steinberg's word
`n_α(s) = x_α(s) x_{-α}(-s⁻¹) x_α(s)` conjugates `x_α(u)` to `x_{-α}(-s⁻²u)`.
This is the rank-one relation needed in the presentation by root elements, where there
are no independent pairs of roots to which a commutator relation could apply.
The equation holds over every commutative value ring, including nonreduced rings and
bad characteristic, and for the actual admissible lattice of any Chevalley datum.

The construction uses the native all-root Chevalley system and its coroot admissibility
from `DynkinType.kostantForm_chevalleySystem_coroot_apply_mem`. The integral rank-one
calculation is `UniversalEnvelopingAlgebra.kostantWeylParam_conj_kostantRootSubgroupParam_e`;
no comparison of carriers or point-generation assertion is used.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapters 3 and 6, Theorem 8.
-/

public section

namespace TauCeti.DynkinType.ChevalleyDatum

open LieAlgebra.IsKilling TauCeti.UniversalEnvelopingAlgebra

attribute [local instance high] Algebra.toModule
attribute [local instance 100] LieRing.ofAssociativeRing

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)

/-- Steinberg's rank-one relation at every root and every unit parameter. The negative root
is the native reflection of the source root in itself. -/
theorem weylElement_conj_rootSubgroupPoints_self (α : Fin t.numRoots)
    (A : Type*) [CommRing A] (s : Aˣ) (u : A) :
    D.weylElement α A s * D.rootSubgroupPoints α A (Multiplicative.ofAdd u) *
        (D.weylElement α A s)⁻¹ =
      D.rootSubgroupPoints ((t.simplyConnectedRootDatum ht).reflectionPerm α α) A
        (Multiplicative.ofAdd (-(((s⁻¹ : Aˣ) : A) ^ 2 * u))) := by
  have hT := (t.isSl2Triple_chevalleySystem ht α).map
    (D.representation.toLieHom.comp (_root_.UniversalEnvelopingAlgebra.ι ℚ)) (by
      intro hz
      apply (t.isSl2Triple_chevalleySystem ht α).h_ne_zero
      apply D.injective_representation_ι
      simpa only [LieHom.comp_apply, AlgHom.toLieHom_apply, map_zero] using hz)
  -- The shared coroot adapters supply admissibility and the restricted basis weights.
  have h := kostantWeylParam_conj_kostantRootSubgroupParam_e
    (t.chevalleySystem ht) _ D.representation D.lattice
    (fun _ hz _ hv => kostantForm_chevalleySystem_coroot_apply_mem
      D.representation D.lattice D.representation_mem_lattice
      D.isNilpotent_representation_rootGenerator α hz hv)
    (isNilpotent_apply_ι_chevalleySystem D.representation
      D.isNilpotent_representation_rootGenerator α)
    (isNilpotent_apply_ι_chevalleySystem D.representation
      D.isNilpotent_representation_rootGenerator _) D.basis _
    (fun j => isCartanWeightVector_coroot_rootEquiv D.representation
      (D.isCartanWeightVector_basis j) α) (c := ()) hT
    (fun _ => (t.isSl2Triple_chevalleySystem ht α).lie_h_e_smul ℚ)
    (fun _ => (t.isSl2Triple_chevalleySystem ht α).lie_lie_smul_f ℚ)
    (CommAlgCat.of ℤ A) s u
  simp only [kostantWeylParam_def, kostantRootSubgroupParam_coroot_eq D.representation
    D.lattice D.representation_mem_lattice D.isNilpotent_representation_rootGenerator α] at h
  -- Transport the lattice identity through the weight-basis matrix map into datum points.
  apply Subtype.ext
  simp only [weylElement_def, Subgroup.coe_mul, Subgroup.coe_inv, coe_rootSubgroupPoints,
    ← map_mul, ← map_inv]
  exact congrArg (Units.map (LinearMap.toMatrixAlgEquiv (D.basis.baseChange A)).toMonoidHom) h

end TauCeti.DynkinType.ChevalleyDatum

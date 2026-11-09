/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Topology.Category.TopCommRingCat
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers

/-!
# Products and equalizers of topological commutative rings

Mathlib's `TopCommRingCat` carries no limit constructions at all. This file provides the two
shapes the sheaf condition consumes — products and equalizers — by exhibiting the explicit
cones: the pointwise ring with the product topology, and the agreement subring with the
subspace topology.

The forgetful functor to `CommRingCat` does not *create* these limits in the technical sense:
it does not reflect them, since the topology on a cone apex is not determined by the
underlying ring — the same reason `TopCat`'s own forgetful functor does not create products
or arbitrary limits (it does create some shapes, such as terminal objects). What is true, and
what later files use, is that it preserves limits: the constructions below have the expected
underlying rings, and preservation of products and equalizers implies preservation of all
small limits. The forgetful functor to types consequently preserves these limits as well.

## Main definitions

* `TauCeti.TopCommRingCat.piFan` and `TauCeti.TopCommRingCat.piFanIsLimit` : the product of a
  family, as the pointwise ring under the product topology.
* `TauCeti.TopCommRingCat.equalizerFork` and `TauCeti.TopCommRingCat.equalizerForkIsLimit` :
  the equalizer of a parallel pair, as the agreement subring under the subspace topology.
* The resulting `HasProducts` and `HasEqualizers` instances.
* `PreservesLimitsOfSize` instances for the forgetful functors to `CommRingCat` and types.

The equalizer fork's inclusion is the inclusion of the agreement subring
(`TauCeti.TopCommRingCat.coe_equalizerFork_ι`). Over a Hausdorff codomain that subring is closed,
by Mathlib's `isClosed_eq` applied to the continuity of the two morphisms; this is what keeps
equalizers of complete separated rings complete.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1 — the sheaf condition of §8.2 is stated in
  complete Hausdorff topological rings, whose products and equalizers this file prepares.
* The constructions adapt Mathlib's to continuous ring homomorphisms: `piFan`/`piFanIsLimit`
  follow `TopCat.piFan`/`TopCat.piFanIsLimit`
  (`Mathlib/Topology/Category/TopCat/Limits/Products.lean`) on the topological side and
  `CommRingCat.piFan`/`CommRingCat.piFanIsLimit` on the algebraic side, and
  `equalizerFork`/`equalizerForkIsLimit` follow `CommRingCat.equalizerFork`/
  `CommRingCat.equalizerForkIsLimit` (`Mathlib/Algebra/Category/Ring/Constructions.lean`),
  with the topology carried through each construction.
-/

public section

namespace TauCeti.TopCommRingCat

open CategoryTheory Limits

universe v u

/-- The explicit product fan of a family of topological commutative rings: the pointwise ring
under the product topology, with the evaluation projections. -/
@[expose, simps! pt π_app]
def piFan {β : Type v} (f : β → TopCommRingCat.{max u v}) : Fan f :=
  Fan.mk (TopCommRingCat.of (∀ b, f b)) fun b => ⟨Pi.evalRingHom _ b, continuous_apply b⟩

/-- The pointwise ring under the product topology is the product in `TopCommRingCat`. -/
def piFanIsLimit {β : Type v} (f : β → TopCommRingCat.{max u v}) : IsLimit (piFan f) where
  lift s := ⟨RingHom.pi fun b => (s.π.app ⟨b⟩).val, continuous_pi fun b => (s.π.app ⟨b⟩).2⟩
  fac _ _ := rfl
  uniq _ _ h := Subtype.ext <| RingHom.ext fun x => funext fun b => congr($(h ⟨b⟩).val x)

instance {β : Type v} (f : β → TopCommRingCat.{max u v}) : HasProduct f :=
  HasLimit.mk ⟨piFan f, piFanIsLimit f⟩

instance : HasProducts.{v} TopCommRingCat.{max u v} := fun _ =>
  ⟨fun _ => hasLimit_of_iso Discrete.natIsoFunctor.symm⟩

variable {R S : TopCommRingCat.{u}} (f g : R ⟶ S)

/-- The explicit equalizer fork of a parallel pair: the agreement subring
`RingHom.eqLocus` under the subspace topology. -/
@[expose, simps! pt]
def equalizerFork : Fork f g :=
  Fork.ofι (P := TopCommRingCat.of (RingHom.eqLocus f.val g.val))
    ⟨(RingHom.eqLocus f.val g.val).subtype, continuous_subtype_val⟩
    (Subtype.ext (RingHom.ext fun x => x.2))

/-- The inclusion of the equalizer fork is, as a function, the subtype coercion of the
agreement subring. -/
@[simp]
theorem coe_equalizerFork_ι :
    ⇑(equalizerFork f g).ι = ((↑) : RingHom.eqLocus f.val g.val → R) :=
  (rfl)

/-- The agreement subring under the subspace topology is the equalizer in
`TopCommRingCat`. -/
def equalizerForkIsLimit : IsLimit (equalizerFork f g) :=
  Fork.IsLimit.mk _
    (fun s => ⟨s.ι.val.codRestrict _ fun x => congr($(s.condition).val x), s.ι.2.subtype_mk _⟩)
    (fun _ => rfl)
    (fun _ _ h => Subtype.ext <| RingHom.ext fun x => Subtype.ext congr($(h).val x))

instance : HasLimit (parallelPair f g) :=
  HasLimit.mk ⟨equalizerFork f g, equalizerForkIsLimit f g⟩

instance : HasEqualizers TopCommRingCat.{u} :=
  ⟨fun F => hasLimit_of_iso (diagramIsoParallelPair F).symm⟩

/-- Forgetting the topology preserves products of topological commutative rings. -/
noncomputable instance {β : Type u} (f : β → TopCommRingCat.{u}) :
    PreservesLimit (Discrete.functor f) (forget₂ TopCommRingCat CommRingCat) :=
  preservesLimit_of_preserves_limit_cone (piFanIsLimit f) <| (isLimitMapConeFanMkEquiv _ _ _).symm
    (CommRingCat.piFanIsLimit fun b => (forget₂ TopCommRingCat CommRingCat).obj (f b))

/-- Forgetting the topology preserves discrete limits. The index type may live in a smaller
universe than the rings: reindexing along `ULift` reduces this to products indexed in the
rings' own universe. -/
noncomputable instance {β : Type v} :
    PreservesLimitsOfShape (Discrete β) (forget₂ TopCommRingCat.{max u v} CommRingCat.{max u v}) :=
  have : PreservesLimitsOfShape (Discrete (ULift.{u} β))
      (forget₂ TopCommRingCat.{max u v} CommRingCat.{max u v}) :=
    preservesLimitsOfShape_of_discrete _
  preservesLimitsOfShape_of_equiv (Discrete.equivalence Equiv.ulift) _

/-- Forgetting the topology preserves equalizers of topological commutative rings. -/
noncomputable instance :
    PreservesLimit (parallelPair f g) (forget₂ TopCommRingCat CommRingCat) := by
  apply preservesLimit_of_preserves_limit_cone (equalizerForkIsLimit f g)
  exact (isLimitMapConeForkEquiv _ _).symm
    (CommRingCat.equalizerForkIsLimit
      ((forget₂ TopCommRingCat CommRingCat).map f) ((forget₂ TopCommRingCat CommRingCat).map g))

/-- Forgetting the topology preserves limits of parallel pairs. -/
noncomputable instance :
    PreservesLimitsOfShape WalkingParallelPair (forget₂ TopCommRingCat.{u} CommRingCat) where
  preservesLimit {F} :=
    preservesLimit_of_iso_diagram _ (diagramIsoParallelPair F).symm

/-- Forgetting the topology preserves all small limits. -/
noncomputable instance :
    PreservesLimitsOfSize.{v, v} (forget₂ TopCommRingCat.{max u v} CommRingCat.{max u v}) :=
  preservesLimits_of_preservesEqualizers_and_products _

/-- The underlying-set functor preserves all small limits. -/
noncomputable instance : PreservesLimitsOfSize.{v, v} (forget TopCommRingCat.{max u v}) :=
  comp_preservesLimits.{v, v} (forget₂ TopCommRingCat.{max u v} CommRingCat.{max u v})
    (forget CommRingCat.{max u v})

end TauCeti.TopCommRingCat

end

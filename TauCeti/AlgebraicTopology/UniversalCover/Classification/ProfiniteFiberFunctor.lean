/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.UniversalCover.Classification.GaloisCategory
public import TauCeti.CategoryTheory.Action.ProfiniteCompletion

/-!
# The profinite fundamental group of the finite-cover fibre functor

Let `X` be path connected, locally path connected and semilocally simply connected, and fix a
basepoint `x₀`. Finite covering spaces of `X` form a Galois category with fibre functor
`TauCeti.FiniteCoveringSpace.fiberFunctor x₀`. Its fundamental group is the profinite completion
of `π₁(X, x₀)`.

The result transports the corresponding statement for finite `π₁(X, x₀)`-sets along
`TauCeti.FiniteCoveringSpace.fiberActionFintypeCatEquivalence`. Thus the action on a finite
cover's fibre is the unique continuous extension of monodromy from the ordinary fundamental
group. Mathlib's Galois-category recognition theorem then identifies this profinite completion
with the natural automorphism group of the fibre functor, as both a group and a topological
space.

## Main declarations

* `TauCeti.FiniteCoveringSpace.instProfiniteCompletionIsFundamentalGroup`: the profinite
  completion of `π₁(X, x₀)` is a fundamental group of the finite-cover fibre functor.
* `TauCeti.FiniteCoveringSpace.profiniteCompletionAutFiberFunctorMulEquiv`: the resulting
  multiplicative equivalence with the automorphism group of the fibre functor.
* `TauCeti.FiniteCoveringSpace.existsUnique_profiniteCompletion_smul_eq`: every automorphism is
  induced on every fibre by a unique element of the profinite completion.
* `TauCeti.FiniteCoveringSpace.profiniteCompletion_etaFn_smul`: the extended action restricts
  along `π₁(X, x₀) → π̂₁(X, x₀)` to the classified monodromy action.
* `TauCeti.FiniteCoveringSpace.profiniteCompletionAutFiberFunctorMulEquiv_isHomeomorph`: this
  equivalence is a homeomorphism for Mathlib's canonical topology on fibre-functor
  automorphisms.

The profinite-completion action is constructed in
`TauCeti.CategoryTheory.Action.ProfiniteCompletion` from Mathlib's universal property.
-/

public section
noncomputable section

open CategoryTheory Topology
open scoped CategoryTheory.PreGaloisCategory

universe u

namespace TauCeti.FiniteCoveringSpace

variable {X : TopCat.{u}} (x₀ : X) [PathConnectedSpace X] [LocallyPathConnectedSpace X]
  [SemilocallySimplyConnectedSpace X]

/-- The profinite completion of `π₁(X, x₀)` acts on the fibre of every finite covering space.
This is the continuous extension of the monodromy action. -/
@[instance_reducible] instance instProfiniteCompletionMulAction (p : FiniteCoveringSpace X) :
    MulAction
      (ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of (FundamentalGroup X x₀)))
      ((fiberFunctor x₀).obj p) :=
  CategoryTheory.Functor.mulActionComp (fiberActionFintypeCatEquivalence x₀).functor
    (Action.forget FintypeCat (FundamentalGroup X x₀))
    (ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of (FundamentalGroup X x₀))) p

/-- **The profinite completion of `π₁(X, x₀)` is a fundamental group of the finite-cover fibre
functor.** -/
instance instProfiniteCompletionIsFundamentalGroup :
    PreGaloisCategory.IsFundamentalGroup (fiberFunctor x₀)
      (ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of (FundamentalGroup X x₀))) := by
  exact CategoryTheory.Functor.isFundamentalGroup_comp
    (fiberActionFintypeCatEquivalence x₀).functor
    (F := Action.forget FintypeCat (FundamentalGroup X x₀))
    (G := ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of (FundamentalGroup X x₀)))

variable {x₀}

/-- The profinite-completion action restricts along the canonical map from `π₁(X, x₀)` to the
classified finite action. Through `finiteFiberActionFunctor_obj_obj_ρ_apply`, the right-hand side
is monodromy on the fibre of `p`. -/
@[simp]
theorem profiniteCompletion_etaFn_smul (g : FundamentalGroup X x₀)
    (p : FiniteCoveringSpace X) (e : (fiberFunctor x₀).obj p) :
    ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of (FundamentalGroup X x₀)) g • e =
      ConcreteCategory.hom (((fiberActionFintypeCatEquivalence x₀).functor.obj p).ρ g) e :=
  TauCeti.ProfiniteCompletion.etaFn_smul (FundamentalGroup X x₀)
    ((fiberActionFintypeCatEquivalence x₀).functor.obj p) g e

variable (x₀)

/-- **The profinite completion of `π₁(X, x₀)` is the automorphism group of the finite-cover fibre
functor.** -/
def profiniteCompletionAutFiberFunctorMulEquiv :
    ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of (FundamentalGroup X x₀)) ≃*
      Aut (fiberFunctor x₀) :=
  PreGaloisCategory.toAutMulEquiv (fiberFunctor x₀)
    (ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of (FundamentalGroup X x₀)))

variable {x₀}

/-- The automorphism attached to an element of the profinite completion acts on every finite
fibre by the canonical extended action. -/
@[simp]
theorem profiniteCompletionAutFiberFunctorMulEquiv_hom_app_apply
    (g : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of (FundamentalGroup X x₀)))
    (p : FiniteCoveringSpace X) (e : (fiberFunctor x₀).obj p) :
    (profiniteCompletionAutFiberFunctorMulEquiv x₀ g).hom.app p e = g • e :=
  PreGaloisCategory.toAut_hom_app_apply
    (F := fiberFunctor x₀)
    (G := ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of (FundamentalGroup X x₀))) g e

/-- The inverse of the automorphism attached to an element of the profinite completion acts by
the inverse element on every finite fibre. -/
@[simp]
theorem profiniteCompletionAutFiberFunctorMulEquiv_inv_app_apply
    (g : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of (FundamentalGroup X x₀)))
    (p : FiniteCoveringSpace X) (e : (fiberFunctor x₀).obj p) :
    (profiniteCompletionAutFiberFunctorMulEquiv x₀ g).inv.app p e = g⁻¹ • e := by
  let η : fiberFunctor x₀ ≅ fiberFunctor x₀ :=
    profiniteCompletionAutFiberFunctorMulEquiv x₀ g
  have hg : η.hom.app p (η.inv.app p e) = g • η.inv.app p e := by
    simpa only [η] using profiniteCompletionAutFiberFunctorMulEquiv_hom_app_apply
      (x₀ := x₀) g p (η.inv.app p e)
  have hi : η.hom.app p (η.inv.app p e) = e :=
    FintypeCat.inv_hom_id_apply (η.app p) e
  change η.inv.app p e = g⁻¹ • e
  calc
    _ = g⁻¹ • (g • η.inv.app p e) := by simp
    _ = g⁻¹ • η.hom.app p (η.inv.app p e) := congrArg (g⁻¹ • ·) hg.symm
    _ = g⁻¹ • e := congrArg (g⁻¹ • ·) hi

/-- Every natural automorphism of the finite-cover fibre functor is induced on every fibre by a
unique element of the profinite completion of `π₁(X, x₀)`. -/
theorem existsUnique_profiniteCompletion_smul_eq (η : Aut (fiberFunctor x₀)) :
    ∃! g : ProfiniteGrp.ProfiniteCompletion.completion
        (GrpCat.of (FundamentalGroup X x₀)),
      ∀ (p : FiniteCoveringSpace X) (e : (fiberFunctor x₀).obj p),
        g • e = η.hom.app p e := by
  refine ⟨(profiniteCompletionAutFiberFunctorMulEquiv x₀).symm η, fun p e => ?_, fun g hg => ?_⟩
  · rw [← profiniteCompletionAutFiberFunctorMulEquiv_hom_app_apply, MulEquiv.apply_symm_apply]
  · refine (profiniteCompletionAutFiberFunctorMulEquiv x₀).injective
      (Aut.ext (NatTrans.ext (funext fun p => ?_)))
    ext e
    rw [MulEquiv.apply_symm_apply]
    exact (profiniteCompletionAutFiberFunctorMulEquiv_hom_app_apply
      (x₀ := x₀) g p e).trans (hg p e)

variable (x₀)

/-- The equivalence between the profinite completion and fibre-functor automorphisms is a
homeomorphism for their canonical topologies. -/
theorem profiniteCompletionAutFiberFunctorMulEquiv_isHomeomorph :
    IsHomeomorph (profiniteCompletionAutFiberFunctorMulEquiv x₀) :=
  PreGaloisCategory.toAutMulEquiv_isHomeomorph (fiberFunctor x₀)
    (ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of (FundamentalGroup X x₀)))

end TauCeti.FiniteCoveringSpace

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Fibration.LocalSystem
public import TauCeti.AlgebraicTopology.Singular.Fibration.Transport

import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance

/-!
# The local system of fibre homology of a Serre fibration

Let `p : E → B` be a Serre fibration (`TauCeti.TopCat.serreFibrations`). A Serre fibration need
not have a transport map between its fibres, but it has one on homology via path transport
(`TauCeti.TopCat.fiberSingularHomologyIsoOfPath`), specialized from the general transport
`TauCeti.TopCat.fiberIsoOfPath` / `TauCeti.TopCat.pullbackFiberIso` in
`TauCeti.Topology.Homotopy.SerreFibration.Transport`. Since path transport depends only on the
homotopy class of `γ` relative to its end points, sends constant paths to identities and
concatenations to composites, `b ↦ Hₙ(p⁻¹(b); M)` is a local coefficient system on `B`
(`TauCeti.TopCat.serreFiberLocalSystem`), the local system of fibre homology of `p`. With path
transport as its monodromy (`TauCeti.TopCat.serreFiberLocalSystem_map_mk`), it provides the
coefficient system for the classical second page `E²_{s,t} = H_s(B; H_t(F))` of the Serre
spectral sequence of `p` (in `TauCeti.TopCat.serreSpectralSequence`, `page 2` is the skeletal `E¹`
page while `page 3` corresponds to the classical `E²` page).

When `p` has a lifting function `Λ`, so that it is a Hurewicz fibration with a transport map
`Λ.transport γ` between its fibres, the transport on homology is the map induced by
`Λ.transport γ`
(`TauCeti.TopCat.fiberSingularHomologyIsoOfPath_hom_eq_singularHomologyMap_fiberTransport`): the
lifts of `γ` give a homotopy, in `γ*E`, from the inclusion of the fibre over `b₀` to the transport
followed by the inclusion of the fibre over `b₁`. So the local system of fibre homology agrees with
the one built from a lifting function
(`TauCeti.TopCat.serreFiberLocalSystemIsoFiberLocalSystem`, against `TauCeti.fiberLocalSystem`).

A map of Serre fibrations, that is, a commutative square from `p` to `p'` over `g : B → B'`, maps
the local system of fibre homology of `p` to the pullback along `g` of that of `p'`, acting on the
fibres by the maps it induces (`CategoryTheory.CommSq.serreFiberLocalSystemMap`). This is an
isomorphism when the maps of fibres are weak homotopy equivalences, as for the base change of a
Serre fibration.

## Main definitions

* `TauCeti.TopCat.serreFiberLocalSystem`: the local system `b ↦ Hₙ(p⁻¹(b); M)`.
* `TauCeti.TopCat.serreFiberLocalSystemObjIso`: the identification of the fibre of
  `serreFiberLocalSystem` at `b` with `Hₙ(p⁻¹(b); M)`.
* `CategoryTheory.CommSq.serreFiberLocalSystemMap`: the morphism of local systems induced by a map
  of Serre fibrations.

## Main results

* `TauCeti.TopCat.serreFiberLocalSystem_map_mk`: monodromy of `serreFiberLocalSystem` is given by
  `TauCeti.TopCat.fiberSingularHomologyIsoOfPath`.
* `TauCeti.TopCat.fiberSingularHomologyIsoOfPath_hom_eq_singularHomologyMap_fiberTransport`: for a
  fibration with a lifting function, path transport on homology is induced by the transport map.
* `TauCeti.TopCat.serreFiberLocalSystemIsoFiberLocalSystem`: identification with
  `TauCeti.fiberLocalSystem`.

## References

* J.-P. Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. 54 (1951),
  425–505, Chapter II.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.H (local coefficients) and Section 4.2 (fibrations).
* G. W. Whitehead, *Elements of Homotopy Theory*, GTM 61, Springer, 1978, Chapter VI.2.
-/

public section

noncomputable section

open CategoryTheory AlgebraicTopology

universe w u

namespace TauCeti.TopCat

variable {E B : TopCat.{u}} {p : E ⟶ B}

section LocalSystem

variable {b₀ b₁ : B}

variable (hp : serreFibrations p) {R : Type w} [Ring R] (M : ModuleCat.{u} R) (n : ℕ)
include hp

/-- **The local system of fibre homology of a Serre fibration** `b ↦ Hₙ(p⁻¹(b); M)`, with
singular homology with coefficients in a module `M`. The class of a path acts by path transport
along it (`TauCeti.TopCat.fiberSingularHomologyIsoOfPath`). -/
def serreFiberLocalSystem : LocalCoefficientSystem.{w, u, u} R B where
  obj b := ((singularHomologyFunctor (ModuleCat.{u} R) n).obj M).obj (p.fiber b.as)
  map {b₀ b₁} := Quotient.lift (fun γ ↦ (fiberSingularHomologyIsoOfPath hp M γ n).hom)
    (fun _ _ h ↦ congrArg Iso.hom (fiberSingularHomologyIsoOfPath_congr hp M h n))
  -- The identity of the fundamental groupoid is the class of the constant path
  -- (`FundamentalGroupoid.id_eq_path_refl`).
  map_id b := congrArg Iso.hom (fiberSingularHomologyIsoOfPath_refl hp M b.as n)
  -- Composition in the fundamental groupoid is the class of the concatenation
  -- (`FundamentalGroupoid.comp_eq`), on which `Quotient.lift` evaluates by definition.
  map_comp f g := by
    induction f using Path.Homotopic.Quotient.ind with | mk γ =>
    induction g using Path.Homotopic.Quotient.ind with | mk δ =>
    exact congrArg Iso.hom (fiberSingularHomologyIsoOfPath_trans hp M γ δ n)

/-- The value of the local system of fibre homology at a point is the homology of the fibre over
it. -/
def serreFiberLocalSystemObjIso (b : FundamentalGroupoid B) :
    (serreFiberLocalSystem hp M n).obj b ≅
      ((singularHomologyFunctor (ModuleCat.{u} R) n).obj M).obj (p.fiber b.as) :=
  Iso.refl _

/-- The local system of fibre homology sends the class of a path to path transport along it. -/
@[simp]
theorem serreFiberLocalSystem_map_mk {b₀ b₁ : FundamentalGroupoid B}
    (γ : Path b₀.as b₁.as) :
    (serreFiberLocalSystem hp M n).map (Path.Homotopic.Quotient.mk γ) =
      (serreFiberLocalSystemObjIso hp M n b₀).hom ≫
        (fiberSingularHomologyIsoOfPath hp M γ n).hom ≫
        (serreFiberLocalSystemObjIso hp M n b₁).inv := by
  simp only [serreFiberLocalSystemObjIso, Iso.refl_hom, Iso.refl_inv]
  -- `Quotient.lift` evaluates on the class of a path by definition.
  rfl

/-! ### Comparison with the transport of a lifting function -/

/-- **Transport on homology is induced by the transport of a lifting function.** If the Serre
fibration `p` has a lifting function `Λ`, path transport along `γ` on the homology of the fibres is
the map induced by the transport map `Λ.transport γ`: the lifts of `γ` from the points of the
fibre over `b₀` form a homotopy, in `γ*E`, from the inclusion of that fibre to the transport
followed by the inclusion of the fibre over `b₁`. -/
theorem fiberSingularHomologyIsoOfPath_hom_eq_singularHomologyMap_fiberTransport
    (Λ : LiftingFunction p.hom) (γ : Path b₀ b₁) :
    (fiberSingularHomologyIsoOfPath hp M γ n).hom =
      ((singularHomologyFunctor (ModuleCat.{u} R) n).obj M).map (fiberTransport Λ γ) := by
  refine ((eq_fiberSingularHomologyIsoOfPath_hom_iff hp M γ n _).2 ?_).symm
  let H : _root_.TopCat.Homotopy
      (p.pullbackFiberι (TopCat.pathEquiv.symm γ).hom (k := 0) (TopCat.pathEquiv.symm γ).hom₀)
      (fiberTransport Λ γ ≫
        p.pullbackFiberι (TopCat.pathEquiv.symm γ).hom (k := 1) (TopCat.pathEquiv.symm γ).hom₁) :=
    { toFun x := ⟨(TopCat.I.homeomorph.symm x.1, Λ.lift x.2.val γ.toContinuousMap
          (γ.source.trans (x.2.property : p x.2.val = b₀).symm) x.1),
        (Λ.apply_lift _ _ _ x.1).symm⟩
      continuous_toFun := by
        refine Continuous.subtype_mk (Continuous.prodMk (by fun_prop) ?_) _
        exact continuous_eval.comp
          ((Λ.continuous_lift (by fun_prop) continuous_const _).prodMk continuous_fst)
      map_zero_left x := Subtype.ext <| by
        rw [TopCat.Hom.coe_pullbackFiberι_apply]
        exact Prod.ext rfl (Λ.lift_zero _ _ _)
      map_one_left x := Subtype.ext <| by
        rw [ConcreteCategory.comp_apply, TopCat.Hom.coe_pullbackFiberι_apply]
        exact Prod.ext rfl ((Λ.transport_apply_coe γ x).symm.trans
          (congrArg Subtype.val (ContinuousMap.congr_fun (fiberTransport_hom Λ γ).symm x))) }
  rw [← Functor.map_comp]
  exact (H.congr_homologyMap_singularChainComplexFunctor M n).symm

/-- **The local system of fibre homology agrees with the one of a lifting function.** For a Serre
fibration with a lifting function `Λ`, the local system `b ↦ Hₙ(p⁻¹(b); k)` of simplicial singular
homology with coefficients in a ring `k` is isomorphic, through the comparison of simplicial and
cubical singular homology, to `TauCeti.fiberLocalSystem Λ k n`, built from the transport maps of
`Λ` on normalized cubical chains. -/
def serreFiberLocalSystemIsoFiberLocalSystem
    (Λ : LiftingFunction p.hom) (k : Type u) [Ring k] :
    serreFiberLocalSystem hp (ModuleCat.of k k) n ≅ fiberLocalSystem Λ k n :=
  NatIso.ofComponents
    (fun b ↦ serreFiberLocalSystemObjIso hp _ n b ≪≫ (fiberLocalSystemSingularObjIso Λ k n b).symm)
    fun {b₀ b₁} q ↦ by
      induction q using Path.Homotopic.Quotient.ind with | mk γ =>
      rw [serreFiberLocalSystem_map_mk, fiberLocalSystem_map_mk_singular,
        fiberSingularHomologyIsoOfPath_hom_eq_singularHomologyMap_fiberTransport hp _ n Λ]
      -- `serreFiberLocalSystemObjIso` is the identity, and the map induced on
      -- `singularHomologyFunctor` is by definition the map induced on the homology of
      -- `singularChains`; `rw` cannot see through either, so `change` states both sides on the
      -- homology of `singularChains`.
      change HomologicalComplex.homologyMap ((singularChains k).map (fiberTransport Λ γ)) n ≫
          (fiberLocalSystemSingularObjIso Λ k n b₁).inv =
        (fiberLocalSystemSingularObjIso Λ k n b₀).inv ≫
          (fiberLocalSystemSingularObjIso Λ k n b₀).hom ≫
          HomologicalComplex.homologyMap ((singularChains k).map (fiberTransport Λ γ)) n ≫
          (fiberLocalSystemSingularObjIso Λ k n b₁).inv
      rw [Iso.inv_hom_id_assoc]

/-- The components of `TauCeti.TopCat.serreFiberLocalSystemIsoFiberLocalSystem` are the
comparisons of simplicial and cubical singular homology of the fibres. -/
@[simp]
theorem serreFiberLocalSystemIsoFiberLocalSystem_hom_app
    (Λ : LiftingFunction p.hom) (k : Type u) [Ring k] (b : FundamentalGroupoid B) :
    (serreFiberLocalSystemIsoFiberLocalSystem hp n Λ k).hom.app b =
      (serreFiberLocalSystemObjIso hp _ n b).hom ≫ (fiberLocalSystemSingularObjIso Λ k n b).inv :=
  (rfl)

end LocalSystem

end TauCeti.TopCat

/-! ### Maps of Serre fibrations -/

namespace CategoryTheory.CommSq

open TauCeti TauCeti.TopCat

variable {E B E' B' : TopCat.{u}} {f : E ⟶ E'} {p : E ⟶ B} {p' : E' ⟶ B'} {g : B ⟶ B'}
  (sq : CommSq f p p' g) (hp : serreFibrations p) (hp' : serreFibrations p') {R : Type w} [Ring R]
  (M : ModuleCat.{u} R) (n : ℕ)

/-- **Functoriality of the local system of fibre homology in maps of Serre fibrations.** A
commutative square from `p` to `p'` over `g` maps the local system of fibre homology of `p` to the
pullback along `g` of that of `p'`, acting on the fibre over each point by the map induced by
`CommSq.fiberMap`. -/
def serreFiberLocalSystemMap :
    serreFiberLocalSystem hp M n ⟶
      (LocalCoefficientSystem.pullback g.hom).obj (serreFiberLocalSystem hp' M n) where
  app b :=
    (serreFiberLocalSystemObjIso hp M n b).hom ≫
      ((singularHomologyFunctor (ModuleCat.{u} R) n).obj M).map (sq.fiberMap b.as) ≫
      (serreFiberLocalSystemObjIso hp' M n (.mk (g b.as))).inv
  naturality {b₀ b₁} q := by
    induction q using Path.Homotopic.Quotient.ind with | mk γ =>
    -- The pulled-back functor agrees with `serreFiberLocalSystem hp' M n` on `.mk (g b.as)` only
    -- up to unfolding `FundamentalGroupoid.map`, so `change` aligns the endpoints before `rw`.
    change (serreFiberLocalSystem hp M n).map (Path.Homotopic.Quotient.mk γ) ≫
        ((serreFiberLocalSystemObjIso hp M n b₁).hom ≫
          ((singularHomologyFunctor (ModuleCat.{u} R) n).obj M).map (sq.fiberMap b₁.as) ≫
          (serreFiberLocalSystemObjIso hp' M n (.mk (g b₁.as))).inv) =
      ((serreFiberLocalSystemObjIso hp M n b₀).hom ≫
          ((singularHomologyFunctor (ModuleCat.{u} R) n).obj M).map (sq.fiberMap b₀.as) ≫
          (serreFiberLocalSystemObjIso hp' M n (.mk (g b₀.as))).inv) ≫
        (serreFiberLocalSystem hp' M n).map
          (Path.Homotopic.Quotient.mk (γ.map g.hom.continuous))
    rw [serreFiberLocalSystem_map_mk, serreFiberLocalSystem_map_mk]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    congr 1
    rw [← Category.assoc, ← Category.assoc]
    congr 1
    exact fiberSingularHomologyIsoOfPath_naturality hp M hp' sq γ n

/-- On the fibre over `b`, the map of local systems induced by a map of Serre fibrations is the map
induced on homology by the map of fibres. -/
@[simp]
theorem serreFiberLocalSystemMap_app (b : FundamentalGroupoid B) :
    (sq.serreFiberLocalSystemMap hp hp' M n).app b =
      (serreFiberLocalSystemObjIso hp M n b).hom ≫
        ((singularHomologyFunctor (ModuleCat.{u} R) n).obj M).map (sq.fiberMap b.as) ≫
        (serreFiberLocalSystemObjIso hp' M n (.mk (g b.as))).inv :=
  (rfl)

/-- When a map of Serre fibrations induces weak homotopy equivalences of all fibres, as for the
base change of a Serre fibration along any map, the induced map of local systems of fibre homology
is an isomorphism. -/
theorem isIso_serreFiberLocalSystemMap (h : ∀ b, (sq.fiberMap b).hom.IsWeakHomotopyEquivalence) :
    IsIso (sq.serreFiberLocalSystemMap hp hp' M n) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro b
  have := (h b.as).isIso_singularHomologyMap M n
  -- Unfold `app b` across the definitional equality `(FundamentalGroupoid.map g.hom).obj b =
  -- .mk (g b.as)` so each factor's domain and codomain match at reducible transparency.
  change IsIso ((serreFiberLocalSystemObjIso hp M n b).hom ≫
    ((singularHomologyFunctor (ModuleCat.{u} R) n).obj M).map (sq.fiberMap b.as) ≫
    (serreFiberLocalSystemObjIso hp' M n (.mk (g b.as))).inv)
  infer_instance

end CategoryTheory.CommSq

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.HomotopyGroup.GeneratedBy
public import TauCeti.Topology.Homotopy.HomotopyGroup.Product

/-!
# Homotopy groups of Kelley products

The Kelley product equips the ordinary product with its compactly generated topology.
Its based homotopy classes are determined by their two projections, even in degree zero.
The comparison `HomotopyGroup.compactlyGeneratedProdEquiv` composes the map induced by
`CompactlyGenerated.adjCounit` with `HomotopyGroup.prodEquiv`, using
`TopCat.isWeakHomotopyEquivalence_compactlyGeneratedAdjCounit`. In positive degrees,
`HomotopyGroup.compactlyGeneratedProdMulEquiv` uses `HomotopyGroup.prodMulEquiv` to give a group
isomorphism. The comparison is natural in both factors, and the inverse sends a pair of
classes induced from the same compactly generated source to the class induced by the pairing.

## References

* R. M. Vogt, *Convenient categories of topological spaces for homotopy theory* (1971),
  for the compactly generated product.
-/

public section

open CategoryTheory Topology
open scoped Topology Topology.Homotopy

universe u v w v' w'

namespace HomotopyGroup

variable {X : TopCat.{v}} {Y : TopCat.{w}}

/-- The homotopy classes of the Kelley product split into the classes of the two factors.
The comparison is induced by the counit and the ordinary product projections, with no
separation assumption on either factor. See Vogt (1971) for the product topology. -/
noncomputable def compactlyGeneratedProdEquiv (n : ℕ)
    (p : TopCat.toCompactlyGenerated.{u, max v w}.obj (TopCat.of (X × Y))) :
    HomotopyGroup (Fin n) _ p ≃ HomotopyGroup (Fin n) X p.1 × HomotopyGroup (Fin n) Y p.2 :=
  let P := TopCat.of (X × Y)
  let c : C(↑(TopCat.toCompactlyGenerated.{u, max v w}.obj P), X × Y) :=
    (CompactlyGenerated.adjCounit.{u}.app P).hom
  (Equiv.ofBijective (map c rfl)
    (P.isWeakHomotopyEquivalence_compactlyGeneratedAdjCounit.{_, u}.bijective n p)).trans
    (prodEquiv p.1 p.2)

/-- The two coordinates of the Kelley product comparison are induced by the projections. -/
@[simp]
theorem compactlyGeneratedProdEquiv_apply (n : ℕ)
    (p : TopCat.toCompactlyGenerated.{u, max v w}.obj (TopCat.of (X × Y)))
    (a : HomotopyGroup (Fin n) _ p) :
    compactlyGeneratedProdEquiv n p a =
      (map (ContinuousMap.fst.comp (CompactlyGenerated.adjCounit.{u}.app
        (TopCat.of (X × Y))).hom) rfl a,
       map (ContinuousMap.snd.comp (CompactlyGenerated.adjCounit.{u}.app
        (TopCat.of (X × Y))).hom) rfl a) := by
  let c : C(↑(TopCat.toCompactlyGenerated.{u, max v w}.obj (TopCat.of (X × Y))), X × Y) :=
    (CompactlyGenerated.adjCounit.{u}.app (TopCat.of (X × Y))).hom
  have h : compactlyGeneratedProdEquiv n p a = prodEquiv p.1 p.2 (map c rfl a) := rfl
  exact h.trans ((prodEquiv_apply p.1 p.2 (map c rfl a)).trans
    (Prod.ext (map_comp_apply ContinuousMap.fst rfl c rfl a)
      (map_comp_apply ContinuousMap.snd rfl c rfl a)))

/-- In positive degrees the Kelley product comparison is an isomorphism of groups. -/
noncomputable def compactlyGeneratedProdMulEquiv (n : ℕ)
    (p : TopCat.toCompactlyGenerated.{u, max v w}.obj (TopCat.of (X × Y))) :
    HomotopyGroup (Fin (n + 1)) _ p ≃*
      HomotopyGroup (Fin (n + 1)) X p.1 × HomotopyGroup (Fin (n + 1)) Y p.2 :=
  let P := TopCat.of (X × Y)
  let c : C(↑(TopCat.toCompactlyGenerated.{u, max v w}.obj P), X × Y) :=
    (CompactlyGenerated.adjCounit.{u}.app P).hom
  let m := mapHom (N := Fin (n + 1)) (x := p) (y := (p.1, p.2)) c rfl
  have hm : Function.Bijective m :=
    P.isWeakHomotopyEquivalence_compactlyGeneratedAdjCounit.{_, u}.bijective (n + 1) p
  (MulEquiv.ofBijective m hm).trans (prodMulEquiv p.1 p.2)

/-- The multiplicative comparison acts on classes by the same projection formula. -/
@[simp]
theorem compactlyGeneratedProdMulEquiv_apply (n : ℕ)
    (p : TopCat.toCompactlyGenerated.{u, max v w}.obj (TopCat.of (X × Y)))
    (a : HomotopyGroup (Fin (n + 1)) _ p) :
    compactlyGeneratedProdMulEquiv n p a = compactlyGeneratedProdEquiv (n + 1) p a := by
  let c : C(↑(TopCat.toCompactlyGenerated.{u, max v w}.obj (TopCat.of (X × Y))), X × Y) :=
    (CompactlyGenerated.adjCounit.{u}.app (TopCat.of (X × Y))).hom
  -- Both counit comparisons act on classes by the same map.
  exact prodMulEquiv_apply p.1 p.2 (map c rfl a)

/-- The underlying equivalence of the positive-degree comparison. -/
@[simp]
theorem compactlyGeneratedProdMulEquiv_toEquiv (n : ℕ)
    (p : TopCat.toCompactlyGenerated.{u, max v w}.obj (TopCat.of (X × Y))) :
    (compactlyGeneratedProdMulEquiv n p : HomotopyGroup (Fin (n + 1)) _ p ≃ _) =
      compactlyGeneratedProdEquiv (n + 1) p :=
  Equiv.ext (compactlyGeneratedProdMulEquiv_apply n p)

/-- The Kelley product comparison commutes with the maps induced by maps of both factors. -/
theorem compactlyGeneratedProdEquiv_natural {X' : TopCat.{v'}} {Y' : TopCat.{w'}}
    (f : C(X, X')) (g : C(Y, Y')) (n : ℕ)
    (p : TopCat.toCompactlyGenerated.{u, max v w}.obj (TopCat.of (X × Y)))
    (a : HomotopyGroup (Fin n) _ p) :
    compactlyGeneratedProdEquiv n ((f.prodMap g).toCompactlyGenerated.{u} p)
        (map (f.prodMap g).toCompactlyGenerated.{u} rfl a) =
      Prod.map (map f rfl) (map g rfl) (compactlyGeneratedProdEquiv n p a) := by
  let P := TopCat.of (X × Y)
  let Q := TopCat.of (X' × Y')
  let k := (f.prodMap g).toCompactlyGenerated.{u}
  let c : C(↑(TopCat.toCompactlyGenerated.{u, max v w}.obj P), X × Y) :=
    (CompactlyGenerated.adjCounit.{u}.app P).hom
  let d : C(↑(TopCat.toCompactlyGenerated.{u, max v' w'}.obj Q), X' × Y') :=
    (CompactlyGenerated.adjCounit.{u}.app Q).hom
  have hcomm : d.comp k = (f.prodMap g).comp c := by
    refine ContinuousMap.ext fun z ↦ ?_
    have hc : c z = z := CompactlyGenerated.adjCounit_app_apply.{u} P z
    have hd : d (k z) = k z := CompactlyGenerated.adjCounit_app_apply.{u} Q (k z)
    simp only [ContinuousMap.comp_apply, hc, hd]
    exact ContinuousMap.toCompactlyGenerated_apply.{u} (f.prodMap g) z
  have hf : ContinuousMap.fst.comp (f.prodMap g) = f.comp ContinuousMap.fst :=
    ContinuousMap.ext fun z ↦ congrArg Prod.fst (ContinuousMap.prodMap_apply f g z)
  have hg : ContinuousMap.snd.comp (f.prodMap g) = g.comp ContinuousMap.snd :=
    ContinuousMap.ext fun z ↦ congrArg Prod.snd (ContinuousMap.prodMap_apply f g z)
  have hf' : (ContinuousMap.fst.comp d).comp k = f.comp (ContinuousMap.fst.comp c) := by
    rw [ContinuousMap.comp_assoc, hcomm, ← ContinuousMap.comp_assoc, hf, ContinuousMap.comp_assoc]
  have hg' : (ContinuousMap.snd.comp d).comp k = g.comp (ContinuousMap.snd.comp c) := by
    rw [ContinuousMap.comp_assoc, hcomm, ← ContinuousMap.comp_assoc, hg, ContinuousMap.comp_assoc]
  refine (compactlyGeneratedProdEquiv_apply n (k p) (map k rfl a)).trans ?_
  refine (congrArg₂ Prod.mk ?_ ?_).trans
    (congrArg (Prod.map (map f rfl) (map g rfl)) (compactlyGeneratedProdEquiv_apply n p a).symm)
  · exact (map_comp_apply (ContinuousMap.fst.comp d) rfl k rfl a).trans
      ((map_congr hf' _ _ a).trans (map_comp_apply f rfl _ rfl a).symm)
  · exact (map_comp_apply (ContinuousMap.snd.comp d) rfl k rfl a).trans
      ((map_congr hg' _ _ a).trans (map_comp_apply g rfl _ rfl a).symm)

/-- A pair of maps from a compactly generated space induces the pair of the individual maps
on homotopy classes. Taking one component constant gives the formula for a slice inclusion. -/
theorem compactlyGeneratedProdEquiv_map_homEquiv_prodMk {A : TopCat.{v}} {B : TopCat.{w}}
    {W : CompactlyGenerated.{u, max v w}} (f : C(W, A)) (g : C(W, B)) (n : ℕ) (z : W)
    (a : HomotopyGroup (Fin n) W z) :
    compactlyGeneratedProdEquiv (X := A) (Y := B) n (f z, g z)
      (map (CompactlyGenerated.adj.{u, max v w}.homEquiv W (TopCat.of (A × B))
        (TopCat.ofHom (f.prodMk g))).hom.hom rfl a) =
      (map f rfl a, map g rfl a) := by
  let P := TopCat.of (A × B)
  let k := (CompactlyGenerated.adj.{u, max v w}.homEquiv W P
    (TopCat.ofHom (f.prodMk g))).hom.hom
  let c : C(↑(TopCat.toCompactlyGenerated.{u, max v w}.obj P), A × B) :=
    (CompactlyGenerated.adjCounit.{u}.app P).hom
  have hc (x : TopCat.toCompactlyGenerated.{u, max v w}.obj P) : c x = x :=
    CompactlyGenerated.adjCounit_app_apply.{u} P x
  have hk (x : W) : k x = (f.prodMk g) x :=
    CompactlyGenerated.adj_homEquiv_apply (TopCat.ofHom (f.prodMk g)) x
  have hf : (ContinuousMap.fst.comp c).comp k = f := by
    ext x
    simp only [ContinuousMap.comp_apply, hc]
    simp only [hk, ContinuousMap.prod_eval, ContinuousMap.fst_apply]
  have hg : (ContinuousMap.snd.comp c).comp k = g := by
    ext x
    simp only [ContinuousMap.comp_apply, hc]
    simp only [hk, ContinuousMap.prod_eval, ContinuousMap.snd_apply]
  refine (compactlyGeneratedProdEquiv_apply n (k z) (map k rfl a)).trans ?_
  exact congrArg₂ Prod.mk
    (congrFun (map_comp_map_of_comp_eq hf rfl rfl rfl) a)
    (congrFun (map_comp_map_of_comp_eq hg rfl rfl rfl) a)

/-- On two classes induced from the same compactly generated source, the inverse comparison
is the map induced by the pairing into the Kelley product. -/
theorem compactlyGeneratedProdEquiv_symm_apply {A : TopCat.{v}} {B : TopCat.{w}}
    {W : CompactlyGenerated.{u, max v w}} (f : C(W, A)) (g : C(W, B)) (n : ℕ) (z : W)
    (a : HomotopyGroup (Fin n) W z) :
    (compactlyGeneratedProdEquiv n (f z, g z)).symm (map f rfl a, map g rfl a) =
      map (CompactlyGenerated.adj.{u, max v w}.homEquiv W (TopCat.of (A × B))
        (TopCat.ofHom (f.prodMk g))).hom.hom rfl a :=
  (compactlyGeneratedProdEquiv n (f z, g z)).symm_apply_eq.mpr
    (compactlyGeneratedProdEquiv_map_homEquiv_prodMk f g n z a).symm

/-- The inverse group comparison acts on classes by the inverse of the underlying comparison. -/
@[simp]
theorem compactlyGeneratedProdMulEquiv_symm_apply (n : ℕ)
    (p : TopCat.toCompactlyGenerated.{u, max v w}.obj (TopCat.of (X × Y)))
    (a : HomotopyGroup (Fin (n + 1)) X p.1 × HomotopyGroup (Fin (n + 1)) Y p.2) :
    (compactlyGeneratedProdMulEquiv n p).symm a = (compactlyGeneratedProdEquiv (n + 1) p).symm a :=
  congrArg (fun e : _ ≃ _ ↦ e.symm a) (compactlyGeneratedProdMulEquiv_toEquiv n p)

end HomotopyGroup

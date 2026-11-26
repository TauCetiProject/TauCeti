/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Category.CompactlyGenerated.Coreflection
public import TauCeti.Topology.Homotopy.HomotopyGroup.GeneratedBy
public import TauCeti.Topology.Homotopy.HomotopyGroup.Product

/-!
# Homotopy groups of Kelley products

The Kelley product equips the ordinary product with its compactly generated topology.
Its based homotopy classes are determined by their two projections, even in degree zero.
The comparison uses `CompactlyGenerated.adjCounit`,
`TauCeti.isWeakHomotopyEquivalence_compactlyGeneratedCounit`, and `HomotopyGroup.prodEquiv`.
In positive degrees the comparison respects the homotopy group multiplication.

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
    HomotopyGroup (Fin n) _ p ≃ HomotopyGroup (Fin n) X p.1 × HomotopyGroup (Fin n) Y p.2 := by
  let P := TopCat.of (X × Y)
  let c := (CompactlyGenerated.adjCounit.{u}.app P).hom
  let e := CompactlyGenerated.toCompactlyGeneratedHomeomorphGeneratedBy.{u} P
  let d := WithGeneratedByTopology.counit (fun K : CompHaus.{u} ↦ K) P
  let f : C(↑(TopCat.toCompactlyGenerated.{u, max v w}.obj P), _) := ⟨e, e.continuous⟩
  have hc : c = d.comp f := by
    refine ContinuousMap.ext fun z ↦ (CompactlyGenerated.adjCounit_app_apply.{u} P z).trans ?_
    have h : d (f z) = z := by
      exact (WithGeneratedByTopology.counit_apply _ (e z)).trans
        ((congrArg (WithGeneratedByTopology.equiv (X := fun K : CompHaus.{u} ↦ K))
          (CompactlyGenerated.toCompactlyGeneratedHomeomorphGeneratedBy_apply P z)).trans
          (Equiv.apply_symm_apply _ z))
    exact h.symm
  have hweak : c.IsWeakHomotopyEquivalence := by
    have hd : d.IsWeakHomotopyEquivalence := by
      simpa only [GeneratedByTopCat.adjCounit_app_hom] using!
        TauCeti.isWeakHomotopyEquivalence_compactlyGeneratedCounit.{_, u} P
    rw [hc]
    exact hd.comp e.isWeakHomotopyEquivalence
  exact (Equiv.ofBijective (map (N := Fin n) c rfl) (hweak.bijective n p)).trans
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
  let c := (CompactlyGenerated.adjCounit.{u}.app (TopCat.of (X × Y))).hom
  have h : compactlyGeneratedProdEquiv n p a = prodEquiv p.1 p.2 (map c rfl a) := rfl
  rw [h]
  exact (prodEquiv_apply p.1 p.2 (map c rfl a)).trans
    (Prod.ext (map_comp_apply ContinuousMap.fst rfl c rfl a)
      (map_comp_apply ContinuousMap.snd rfl c rfl a))

/-- In positive degrees the Kelley product comparison is an isomorphism of groups. -/
noncomputable def compactlyGeneratedProdMulEquiv (n : ℕ)
    (p : TopCat.toCompactlyGenerated.{u, max v w}.obj (TopCat.of (X × Y))) :
    HomotopyGroup (Fin (n + 1)) _ p ≃*
      HomotopyGroup (Fin (n + 1)) X p.1 × HomotopyGroup (Fin (n + 1)) Y p.2 := by
  refine { compactlyGeneratedProdEquiv (n + 1) p with map_mul' := ?_ }
  intro a b
  refine (compactlyGeneratedProdEquiv_apply (n + 1) p (a * b)).trans ?_
  let c : C(↑(TopCat.toCompactlyGenerated.{u, max v w}.obj (TopCat.of (X × Y))), X × Y) :=
    (CompactlyGenerated.adjCounit.{u}.app (TopCat.of (X × Y))).hom
  refine (congrArg₂ Prod.mk (map_mul (x := p) (y := p.1) (ContinuousMap.fst.comp c) rfl a b)
    (map_mul (x := p) (y := p.2) (ContinuousMap.snd.comp c) rfl a b)).trans ?_
  exact congrArg₂ (· * ·) (compactlyGeneratedProdEquiv_apply (n + 1) p a).symm
    (compactlyGeneratedProdEquiv_apply (n + 1) p b).symm

/-- The multiplicative comparison acts on classes by the same projection formula. -/
@[simp]
theorem compactlyGeneratedProdMulEquiv_apply (n : ℕ)
    (p : TopCat.toCompactlyGenerated.{u, max v w}.obj (TopCat.of (X × Y)))
    (a : HomotopyGroup (Fin (n + 1)) _ p) :
    compactlyGeneratedProdMulEquiv n p a = compactlyGeneratedProdEquiv (n + 1) p a :=
  (rfl)

/-- The underlying equivalence of the positive-degree comparison. -/
@[simp]
theorem compactlyGeneratedProdMulEquiv_toEquiv (n : ℕ)
    (p : TopCat.toCompactlyGenerated.{u, max v w}.obj (TopCat.of (X × Y))) :
    (compactlyGeneratedProdMulEquiv n p : HomotopyGroup (Fin (n + 1)) _ p ≃ _) =
      compactlyGeneratedProdEquiv (n + 1) p :=
  (rfl)

/-- The Kelley product comparison commutes with the maps induced by maps of both factors. -/
theorem compactlyGeneratedProdEquiv_natural {X' : TopCat.{v'}} {Y' : TopCat.{w'}}
    (f : C(X, X')) (g : C(Y, Y')) (n : ℕ)
    (p : TopCat.toCompactlyGenerated.{u, max v w}.obj (TopCat.of (X × Y)))
    (a : HomotopyGroup (Fin n) _ p) :
    compactlyGeneratedProdEquiv n ((f.prodMap g).toCompactlyGenerated.{u} p)
        (map (f.prodMap g).toCompactlyGenerated.{u} rfl a) =
      Prod.map (map f rfl) (map g rfl) (compactlyGeneratedProdEquiv n p a) := by
  let k := (f.prodMap g).toCompactlyGenerated.{u}
  let c := (CompactlyGenerated.adjCounit.{u}.app (TopCat.of (X × Y))).hom
  let d := (CompactlyGenerated.adjCounit.{u}.app (TopCat.of (X' × Y'))).hom
  have hf : (ContinuousMap.fst.comp d).comp k = f.comp (ContinuousMap.fst.comp c) :=
    ContinuousMap.ext fun _ ↦ rfl
  have hg : (ContinuousMap.snd.comp d).comp k = g.comp (ContinuousMap.snd.comp c) :=
    ContinuousMap.ext fun _ ↦ rfl
  refine (compactlyGeneratedProdEquiv_apply n (k p) (map k rfl a)).trans ?_
  refine (congrArg₂ Prod.mk ?_ ?_).trans
    (congrArg (Prod.map (map f rfl) (map g rfl)) (compactlyGeneratedProdEquiv_apply n p a).symm)
  · exact (map_comp_apply _ rfl k rfl a).trans
      ((map_congr hf _ _ a).trans (map_comp_apply f rfl _ rfl a).symm)
  · exact (map_comp_apply _ rfl k rfl a).trans
      ((map_congr hg _ _ a).trans (map_comp_apply g rfl _ rfl a).symm)

/-- A pair of maps from a compactly generated space induces the pair of the individual maps
on homotopy classes. Taking one component constant gives the formula for a slice inclusion. -/
theorem compactlyGeneratedProdEquiv_map_lift {A B : TopCat.{w}}
    {W : CompactlyGenerated.{u, w}} (f : C(W, A)) (g : C(W, B)) (n : ℕ) (z : W)
    (a : HomotopyGroup (Fin n) W z) :
    compactlyGeneratedProdEquiv (X := A) (Y := B) n (f z, g z)
      (map (CompactlyGenerated.adj.{u, w}.homEquiv W (TopCat.of (A × B))
        (TopCat.ofHom (f.prodMk g))).hom.hom rfl a) =
      (map f rfl a, map g rfl a) := by
  let k := (CompactlyGenerated.adj.{u, w}.homEquiv W (TopCat.of (A × B))
    (TopCat.ofHom (f.prodMk g))).hom.hom
  let c := (CompactlyGenerated.adjCounit.{u}.app (TopCat.of (A × B))).hom
  have hf : (ContinuousMap.fst.comp c).comp k = f := ContinuousMap.ext fun _ ↦ rfl
  have hg : (ContinuousMap.snd.comp c).comp k = g := ContinuousMap.ext fun _ ↦ rfl
  refine (compactlyGeneratedProdEquiv_apply n (k z) (map k rfl a)).trans ?_
  exact congrArg₂ Prod.mk
    (congrFun (map_comp_map_of_comp_eq hf rfl rfl rfl) a)
    (congrFun (map_comp_map_of_comp_eq hg rfl rfl rfl) a)

end HomotopyGroup

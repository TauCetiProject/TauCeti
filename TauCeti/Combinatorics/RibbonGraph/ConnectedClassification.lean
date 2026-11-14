/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PermutationTriple.ClassInvariants
public import TauCeti.Combinatorics.RibbonGraph.CycleData
public import TauCeti.Combinatorics.RibbonGraph.Genus

/-!
# Connected ribbon graphs and connected permutation triples

Isomorphism classes of connected finite bipartite ribbon graphs with `n` edges are equivalent to
`TauCeti.ConnectedIsoClass n`. These graphs are the combinatorial dessins d'enfants, so counting
their isomorphism classes reduces to counting connected triples. The equivalence restricts
`TauCeti.BipartiteRibbonGraph.isoClassEquiv`, with the same comparison of automorphism groups
given by `TauCeti.BipartiteRibbonGraph.autEquivAutomorphismGroup`.

The equations `connectedIsoClassEquiv_mk` and `connectedIsoClassEquiv_symm_mk` describe the
classification on representatives. Edge numberings are arbitrary, and the inverse uses universe
lifting so that graphs in any universe are classified. In degree zero both carriers are empty,
since connectedness requires a nonempty edge set, and in degree one both have a unique class.

The restriction uses Mathlib's `Equiv.subtypeQuotientEquivQuotientSubtype` to commute invariant
subtypes with quotients. The degree partitions (`cycleData`), Euler characteristic, genus,
automorphism-group order, and regularity descend to `Quotient (connectedIsoSetoid n)` and match
those of `TauCeti.ConnectedIsoClass n` along `connectedIsoClassEquiv`.

## References

* S. K. Lando, A. K. Zvonkin, *Graphs on Surfaces and Their Applications*, Encyclopaedia of
  Mathematical Sciences 141, Springer 2004, §1.3 and §1.5.
* E. Girondo, G. González-Diez, *Introduction to Compact Riemann Surfaces and Dessins d'Enfants*,
  London Mathematical Society Student Texts 79, Cambridge University Press 2012, §4.2.
-/

open Equiv

public section

namespace TauCeti.BipartiteRibbonGraph

universe u v

variable {n : ℕ}

/-! ### Automorphisms and regularity of ribbon graphs -/

/-- Isomorphisms between finite bipartite ribbon graphs form a finite type. -/
instance {Γ : BipartiteRibbonGraph.{u}} {Δ : BipartiteRibbonGraph.{v}} : Finite (Γ.Iso Δ) :=
  Finite.of_injective Iso.edge fun _ _ => Iso.ext

/-- Conjugation by an isomorphism of ribbon graphs identifies their automorphism groups. -/
def Iso.autMulEquiv {Γ : BipartiteRibbonGraph.{u}} {Δ : BipartiteRibbonGraph.{v}} (φ : Γ.Iso Δ) :
    Γ.Aut ≃* Δ.Aut where
  toFun f := φ.symm.trans (f.trans φ)
  invFun g := φ.trans (g.trans φ.symm)
  left_inv f := by ext e; simp
  right_inv g := by ext e; simp
  map_mul' f₁ f₂ := by ext e; simp

/-- Isomorphic bipartite ribbon graphs have automorphism groups of the same cardinality. -/
theorem Iso.natCard_aut_eq {Γ : BipartiteRibbonGraph.{u}} {Δ : BipartiteRibbonGraph.{v}}
    (φ : Γ.Iso Δ) : Nat.card Γ.Aut = Nat.card Δ.Aut :=
  Nat.card_congr φ.autMulEquiv.toEquiv

/-- The automorphism-group order of a numbered ribbon graph equals that of its triple. -/
theorem natCard_aut_eq_natCard_automorphismGroup (Γ : BipartiteRibbonGraph.{u}) (ν : Γ.E ≃ Fin n) :
    Nat.card Γ.Aut = Nat.card (Γ.toPermutationTriple ν).automorphismGroup :=
  Nat.card_congr (Γ.autEquivAutomorphismGroup ν).toEquiv

/-- Numbering the edges of a ribbon graph preserves the cardinality of its automorphism group. -/
@[simp] theorem natCard_automorphismGroup_toPermutationTriple (Γ : BipartiteRibbonGraph.{u})
    (ν : Γ.E ≃ Fin n) : Nat.card (Γ.toPermutationTriple ν).automorphismGroup = Nat.card Γ.Aut :=
  (Γ.natCard_aut_eq_natCard_automorphismGroup ν).symm

/-- Canonical isomorphism between `t.automorphismGroup` and `t.ribbonGraph.Aut`. -/
noncomputable def _root_.TauCeti.PermutationTriple.automorphismGroupMulEquivRibbonGraphAut
    (t : PermutationTriple n) : t.automorphismGroup ≃* t.ribbonGraph.Aut :=
  (MulEquiv.subgroupCongr
      (congrArg PermutationTriple.automorphismGroup t.toPermutationTriple_ribbonGraph.symm)).trans
    (t.ribbonGraph.autEquivAutomorphismGroup (Equiv.refl (Fin n))).symm

/-- On edges (`Fin n`), `automorphismGroupMulEquivRibbonGraphAut` is the underlying permutation. -/
@[simp] theorem _root_.TauCeti.PermutationTriple.automorphismGroupMulEquivRibbonGraphAut_edge
    (t : PermutationTriple n) (τ : t.automorphismGroup) :
    (t.automorphismGroupMulEquivRibbonGraphAut τ).edge = (τ : Perm (Fin n)) :=
  (t.ribbonGraph.autEquivAutomorphismGroup_symm_apply_edge (Equiv.refl (Fin n)) _).trans
    (Equiv.ext fun _ ↦ rfl)

/-- Passing from a triple to its ribbon graph preserves the automorphism-group order. -/
@[simp] theorem _root_.TauCeti.PermutationTriple.natCard_aut_ribbonGraph (t : PermutationTriple n) :
    Nat.card t.ribbonGraph.Aut = Nat.card t.automorphismGroup :=
  (Nat.card_congr t.automorphismGroupMulEquivRibbonGraphAut.toEquiv).symm

/-- Automorphisms of a bipartite ribbon graph act on its edges by evaluation. -/
instance (Γ : BipartiteRibbonGraph.{u}) : SMul Γ.Aut Γ.E := ⟨fun f e ↦ f.edge e⟩

/-- An automorphism acts on an edge by applying its underlying edge bijection. -/
@[simp] theorem Aut.smul_def {Γ : BipartiteRibbonGraph.{u}} (f : Γ.Aut) (e : Γ.E) :
    f • e = f.edge e := (rfl)

/-- The action of `Γ.Aut` on `Γ.E` is a multiplicative group action. -/
instance (Γ : BipartiteRibbonGraph.{u}) : MulAction Γ.Aut Γ.E where
  one_smul _ := by rw [Aut.smul_def, Aut.one_edge]; rfl
  mul_smul _ _ _ := by rw [Aut.smul_def, Aut.smul_def, Aut.smul_def, Aut.mul_edge]; rfl

/-- A ribbon graph is *regular* when it is connected and `Γ.Aut` acts transitively on `Γ.E`. -/
def IsRegular (Γ : BipartiteRibbonGraph.{u}) : Prop :=
  Γ.IsConnected ∧ MulAction.IsPretransitive Γ.Aut Γ.E

/-- Unfold `BipartiteRibbonGraph.IsRegular` into connectedness and edge-transitivity. -/
theorem isRegular_iff {Γ : BipartiteRibbonGraph.{u}} :
    Γ.IsRegular ↔ Γ.IsConnected ∧ MulAction.IsPretransitive Γ.Aut Γ.E := Iff.rfl

/-- Every regular bipartite ribbon graph is connected. -/
theorem IsRegular.isConnected {Γ : BipartiteRibbonGraph.{u}} (hΓ : Γ.IsRegular) : Γ.IsConnected :=
  hΓ.1

/-- Numbering the edges of a bipartite ribbon graph preserves regularity. -/
@[simp] theorem isRegular_toPermutationTriple (Γ : BipartiteRibbonGraph.{u}) (ν : Γ.E ≃ Fin n) :
    (Γ.toPermutationTriple ν).IsRegular ↔ Γ.IsRegular := by
  let φ : Γ.E →ₑ[Γ.autEquivAutomorphismGroup ν] Fin n :=
    { toFun := ν, map_smul' := fun f e => by
        rw [Aut.smul_def, Subgroup.smul_def, Perm.smul_def, coe_autEquivAutomorphismGroup_apply,
          Equiv.permCongr_apply, ν.symm_apply_apply] }
  rw [PermutationTriple.isRegular_iff, isRegular_iff]
  exact and_congr (Γ.isConnected_toPermutationTriple ν)
    (MulAction.isPretransitive_congr (f := φ)
      (Γ.autEquivAutomorphismGroup ν).surjective ν.bijective).symm

/-- Passing from a permutation triple to its ribbon graph preserves regularity. -/
@[simp] theorem _root_.TauCeti.PermutationTriple.isRegular_ribbonGraph (t : PermutationTriple n) :
    t.ribbonGraph.IsRegular ↔ t.IsRegular := by
  rw [← t.ribbonGraph.isRegular_toPermutationTriple (Equiv.refl (Fin n)),
    t.toPermutationTriple_ribbonGraph]

/-- `Γ` is regular iff it is connected and `Nat.card Γ.Aut = Fintype.card Γ.E`. -/
theorem isRegular_iff_natCard_aut (Γ : BipartiteRibbonGraph.{u}) :
    Γ.IsRegular ↔ Γ.IsConnected ∧ Nat.card Γ.Aut = Fintype.card Γ.E := by
  let ν := Fintype.equivFin Γ.E
  rw [← Γ.isRegular_toPermutationTriple ν, PermutationTriple.isRegular_iff_card_automorphismGroup,
    Γ.isConnected_toPermutationTriple ν, Γ.natCard_automorphismGroup_toPermutationTriple ν]

/-- Regularity of bipartite ribbon graphs is invariant under isomorphism. -/
theorem Iso.isRegular_iff {Γ : BipartiteRibbonGraph.{u}} {Δ : BipartiteRibbonGraph.{v}}
    (φ : Γ.Iso Δ) : Γ.IsRegular ↔ Δ.IsRegular := by
  rw [isRegular_iff_natCard_aut, isRegular_iff_natCard_aut, φ.isConnected_iff, φ.natCard_aut_eq,
    Fintype.card_congr φ.edge]

/-! ### Classification of connected ribbon graphs -/

/-- Isomorphism of connected bipartite ribbon graphs with `n` edges. The inner subtype records
the edge count; the outer subtype records connectedness. -/
def connectedIsoSetoid (n : ℕ) :
    Setoid {Γ : {Γ : BipartiteRibbonGraph.{u} // Fintype.card Γ.E = n} // Γ.1.IsConnected} :=
  (isoSetoid n).comap Subtype.val

/-- Two connected ribbon graphs have the same quotient class exactly when they are isomorphic. -/
@[simp]
theorem connectedIsoSetoid_mk_eq_mk_iff
    {Γ Δ : {Γ : {Γ : BipartiteRibbonGraph.{u} // Fintype.card Γ.E = n} // Γ.1.IsConnected}} :
    Quotient.mk (connectedIsoSetoid n) Γ = Quotient.mk (connectedIsoSetoid n) Δ ↔
      Nonempty (Γ.1.1.Iso Δ.1.1) :=
  Quotient.eq.trans isoSetoid_r

/-- Isomorphism classes of connected ribbon graphs are the isomorphism classes of connected
permutation triples. -/
noncomputable def connectedIsoClassEquiv (n : ℕ) :
    Quotient (connectedIsoSetoid.{u} n) ≃ ConnectedIsoClass n :=
  ((Equiv.subtypeQuotientEquivQuotientSubtype
    (fun Γ : {Γ : BipartiteRibbonGraph.{u} // Fintype.card Γ.E = n} => Γ.1.IsConnected)
    (fun c => (isoClassEquiv n c).IsConnected)
    (fun Γ => by
      rw [isoClassEquiv_mk_equivFinOfCardEq, PermutationTriple.IsoClass.isConnected_mk,
        isConnected_toPermutationTriple])
    (fun _ _ => Iff.rfl)).symm.trans
      (isoClassEquiv n).subtypeEquivOfSubtype).trans (ConnectedIsoClass.equivSubtype n).symm

/-- A connected graph determines the connected triple class of any numbering of its edges. -/
theorem connectedIsoClassEquiv_mk
    (Γ : {Γ : {Γ : BipartiteRibbonGraph.{u} // Fintype.card Γ.E = n} // Γ.1.IsConnected})
    (ν : Γ.1.1.E ≃ Fin n) :
    connectedIsoClassEquiv n (Quotient.mk (connectedIsoSetoid n) Γ) =
      ConnectedIsoClass.mk ⟨Γ.1.1.toPermutationTriple ν,
        (Γ.1.1.isConnected_toPermutationTriple ν).2 Γ.2⟩ := by
  apply (ConnectedIsoClass.equivSubtype n).injective
  simp only [connectedIsoClassEquiv, Equiv.trans_apply, Equiv.apply_symm_apply,
    ConnectedIsoClass.equivSubtype_mk]
  exact Subtype.ext (isoClassEquiv_mk Γ.1 ν)

/-- The connected graph class evaluated using the canonical numbering of its edges. -/
@[simp]
theorem connectedIsoClassEquiv_mk_equivFinOfCardEq
    (Γ : {Γ : {Γ : BipartiteRibbonGraph.{u} // Fintype.card Γ.E = n} // Γ.1.IsConnected}) :
    connectedIsoClassEquiv n (Quotient.mk (connectedIsoSetoid n) Γ) =
      ConnectedIsoClass.mk ⟨Γ.1.1.toPermutationTriple (Fintype.equivFinOfCardEq Γ.1.2),
        (Γ.1.1.isConnected_toPermutationTriple _).2 Γ.2⟩ :=
  connectedIsoClassEquiv_mk Γ _

/-- Forgetting connectedness commutes with the classification of all ribbon graphs. -/
@[simp]
theorem forget_connectedIsoClassEquiv (c : Quotient (connectedIsoSetoid.{u} n)) :
    (connectedIsoClassEquiv n c).forget =
      isoClassEquiv n (Quotient.map (sa := connectedIsoSetoid n) (sb := isoSetoid n) Subtype.val
        (fun _ _ h => isoSetoid_r.mpr
          (connectedIsoSetoid_mk_eq_mk_iff.mp (Quotient.sound h))) c) := by
  induction c using Quotient.inductionOn with
  | _ Γ => simp

/-- The connected class of a triple determines the class of its universe-lifted ribbon graph. -/
@[simp]
theorem connectedIsoClassEquiv_symm_mk (t : ConnectedTriple n) :
    (connectedIsoClassEquiv.{u} n).symm (ConnectedIsoClass.mk t) =
      Quotient.mk (connectedIsoSetoid n)
        ⟨⟨t.1.ribbonGraph.ulift, t.1.ribbonGraph.card_E_ulift.trans t.1.card_E_ribbonGraph⟩,
          t.1.ribbonGraph.uliftIso.isConnected_iff.mpr
            (t.1.isConnected_ribbonGraph.mpr t.2)⟩ := by
  apply (connectedIsoClassEquiv n).injective
  rw [Equiv.apply_symm_apply, connectedIsoClassEquiv_mk _
    (t.1.ribbonGraph.uliftIso.edge.trans (Equiv.refl (Fin n)))]
  symm
  apply ConnectedIsoClass.mk_eq_mk_iff_equivalent.mpr
  simpa only [PermutationTriple.toPermutationTriple_ribbonGraph] using
    equivalent_toPermutationTriple_of_iso t.1.ribbonGraph.uliftIso
      (t.1.ribbonGraph.uliftIso.edge.trans (Equiv.refl (Fin n))) (Equiv.refl (Fin n))

/-- There are no connected bipartite ribbon graphs with zero edges. -/
instance : IsEmpty (Quotient (connectedIsoSetoid.{u} 0)) := (connectedIsoClassEquiv.{u} 0).isEmpty

/-- Up to isomorphism there is a unique connected bipartite ribbon graph with one edge. -/
noncomputable instance : Unique (Quotient (connectedIsoSetoid.{u} 1)) :=
  (connectedIsoClassEquiv.{u} 1).unique

/-! ### Invariants of connected ribbon-graph classes -/

/-- The degree-partition triple `(λ₀, λ₁, λ∞)` of a class of connected ribbon graphs. -/
def connectedCycleData (n : ℕ) :
    Quotient (connectedIsoSetoid.{u} n) → Multiset ℕ × Multiset ℕ × Multiset ℕ :=
  Quotient.lift (fun Γ => Γ.1.1.cycleData) fun _ _ h =>
    (connectedIsoSetoid_mk_eq_mk_iff.mp (Quotient.sound h)).elim Iso.cycleData_eq

/-- Evaluating `connectedCycleData` on the class of `Γ` gives `Γ.1.1.cycleData`. -/
@[simp] theorem connectedCycleData_mk
    (Γ : {Γ : {Γ : BipartiteRibbonGraph.{u} // Fintype.card Γ.E = n} // Γ.1.IsConnected}) :
    connectedCycleData n (Quotient.mk (connectedIsoSetoid n) Γ) = Γ.1.1.cycleData := (rfl)

/-- `connectedIsoClassEquiv` matches `connectedCycleData` with `ConnectedIsoClass.cycleData`. -/
@[simp] theorem cycleData_connectedIsoClassEquiv (c : Quotient (connectedIsoSetoid.{u} n)) :
    (connectedIsoClassEquiv n c).cycleData = connectedCycleData n c :=
  Quotient.inductionOn c fun _ => by simp

/-- The Euler characteristic `|B| + |W| + F - |E|` of a class of connected ribbon graphs. -/
def connectedEulerChar (n : ℕ) : Quotient (connectedIsoSetoid.{u} n) → ℤ :=
  Quotient.lift (fun Γ => Γ.1.1.eulerChar) fun _ _ h =>
    (connectedIsoSetoid_mk_eq_mk_iff.mp (Quotient.sound h)).elim Iso.eulerChar_eq

/-- Evaluating `connectedEulerChar` on the class of `Γ` gives `Γ.1.1.eulerChar`. -/
@[simp] theorem connectedEulerChar_mk
    (Γ : {Γ : {Γ : BipartiteRibbonGraph.{u} // Fintype.card Γ.E = n} // Γ.1.IsConnected}) :
    connectedEulerChar n (Quotient.mk (connectedIsoSetoid n) Γ) = Γ.1.1.eulerChar := (rfl)

/-- The classification `connectedIsoClassEquiv` preserves the Euler characteristic. -/
@[simp] theorem eulerChar_connectedIsoClassEquiv (c : Quotient (connectedIsoSetoid.{u} n)) :
    (connectedIsoClassEquiv n c).eulerChar = connectedEulerChar n c :=
  Quotient.inductionOn c fun _ => by simp

/-- The combinatorial genus `((2 - χ) / 2).toNat` of a class of connected ribbon graphs. -/
def connectedGenus (n : ℕ) : Quotient (connectedIsoSetoid.{u} n) → ℕ :=
  Quotient.lift (fun Γ => Γ.1.1.genus) fun _ _ h =>
    (connectedIsoSetoid_mk_eq_mk_iff.mp (Quotient.sound h)).elim fun φ => φ.genus_eq

/-- Evaluating `connectedGenus` on the class of `Γ` gives `Γ.1.1.genus`. -/
@[simp] theorem connectedGenus_mk
    (Γ : {Γ : {Γ : BipartiteRibbonGraph.{u} // Fintype.card Γ.E = n} // Γ.1.IsConnected}) :
    connectedGenus n (Quotient.mk (connectedIsoSetoid n) Γ) = Γ.1.1.genus := (rfl)

/-- The classification `connectedIsoClassEquiv` preserves the combinatorial genus. -/
@[simp] theorem genus_connectedIsoClassEquiv (c : Quotient (connectedIsoSetoid.{u} n)) :
    (connectedIsoClassEquiv n c).genus = connectedGenus n c :=
  Quotient.inductionOn c fun _ => by simp

/-- The cardinality of the automorphism group of a class of connected ribbon graphs. -/
noncomputable def connectedNatCardAut (n : ℕ) : Quotient (connectedIsoSetoid.{u} n) → ℕ :=
  Quotient.lift (fun Γ => Nat.card Γ.1.1.Aut) fun _ _ h =>
    (connectedIsoSetoid_mk_eq_mk_iff.mp (Quotient.sound h)).elim Iso.natCard_aut_eq

/-- Evaluating `connectedNatCardAut` on the class of `Γ` gives `Nat.card Γ.1.1.Aut`. -/
@[simp] theorem connectedNatCardAut_mk
    (Γ : {Γ : {Γ : BipartiteRibbonGraph.{u} // Fintype.card Γ.E = n} // Γ.1.IsConnected}) :
    connectedNatCardAut n (Quotient.mk (connectedIsoSetoid n) Γ) = Nat.card Γ.1.1.Aut := (rfl)

/-- The classification `connectedIsoClassEquiv` preserves the automorphism-group order. -/
@[simp] theorem natCardAutomorphismGroup_connectedIsoClassEquiv
    (c : Quotient (connectedIsoSetoid.{u} n)) :
    (connectedIsoClassEquiv n c).natCardAutomorphismGroup = connectedNatCardAut n c :=
  Quotient.inductionOn c fun _ => by simp

/-- Regularity on isomorphism classes of connected bipartite ribbon graphs. -/
def ConnectedIsRegular (n : ℕ) : Quotient (connectedIsoSetoid.{u} n) → Prop :=
  Quotient.lift (fun Γ => Γ.1.1.IsRegular) fun _ _ h =>
    (connectedIsoSetoid_mk_eq_mk_iff.mp (Quotient.sound h)).elim fun φ => propext φ.isRegular_iff

/-- Evaluating `ConnectedIsRegular` on the class of `Γ` recovers `Γ.1.1.IsRegular`. -/
@[simp] theorem connectedIsRegular_mk
    (Γ : {Γ : {Γ : BipartiteRibbonGraph.{u} // Fintype.card Γ.E = n} // Γ.1.IsConnected}) :
    ConnectedIsRegular n (Quotient.mk (connectedIsoSetoid n) Γ) ↔ Γ.1.1.IsRegular := Iff.rfl

/-- The classification `connectedIsoClassEquiv` preserves regularity. -/
@[simp] theorem isRegular_connectedIsoClassEquiv (c : Quotient (connectedIsoSetoid.{u} n)) :
    (connectedIsoClassEquiv n c).IsRegular ↔ ConnectedIsRegular n c :=
  Quotient.inductionOn c fun _ => by simp

end TauCeti.BipartiteRibbonGraph

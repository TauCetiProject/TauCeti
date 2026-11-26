/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.FiberBundle.Principal.Basic
public import TauCeti.Topology.FiberBundle.Principal.Equiv
public import Mathlib.Topology.FiberBundle.Constructions

/-!
# The fibre product of principal bundles

Given a principal `G`-bundle `P` and a principal `H`-bundle `Q` over the same base `B`, their
**fibre product** `TauCeti.PrincipalBundle.FiberProd P Q` has fibre `P b × Q b` over `b`, with the
componentwise right action of `G × H`: `(p, q) • (g, h) = (p • g, q • h)`. It is a principal
`(G × H)`-bundle (`TauCeti.PrincipalBundle.FiberProd.instPrincipalBundle`), whose division map is
the pair of division maps (`TauCeti.PrincipalBundle.FiberProd.division_mk`).

The total space carries the topology induced from the product of the two total spaces, and the
fibre bundle structure is Mathlib's fibrewise product `P ×ᵇ Q` (`FiberBundle.prod`): every
trivialization of its atlas is a product `e₁.prod e₂` of trivializations of the atlases of `P`
and `Q`. Mathlib asks for `Zero` on the fibres, used only for the values of the inverse of
`e₁.prod e₂` outside its base set; the fibres of a principal bundle have no zero, so the instance
here supplies the point with coordinate `1` in the preferred trivialization instead. The fibre
product is a separate type `FiberProd P Q b` rather than `P b × Q b`, so that its action of
`(G × H)ᵐᵒᵖ` does not compete with Mathlib's actions on products.

Fibre products are the first step of the constructions that combine two principal bundles: the
twist of a `Spinᶜ` structure by a principal `U(1)`-bundle is the extension of structure group of
the fibre product along the multiplication `Spinᶜ(n) × U(1) → Spinᶜ(n)`.

Equivalences `φ : P ≃ P'` and `ψ : Q ≃ Q'` of principal bundles (`TauCeti.PrincipalBundle.Equiv`)
induce an equivalence of fibre products `(p, q) ↦ (φ p, ψ q)`
(`TauCeti.PrincipalBundle.Equiv.fiberProd`), compatible with identities, inverses and composites.

## Main definitions

* `TauCeti.PrincipalBundle.FiberProd`: the fibre product of two bundles over the same base.
* `TauCeti.PrincipalBundle.FiberProd.mk`, `FiberProd.fst`, `FiberProd.snd`: its points and their
  components.
* `TauCeti.PrincipalBundle.Equiv.fiberProd`: the equivalence of fibre products induced by
  equivalences of the factors.

## Main results

* `TauCeti.PrincipalBundle.FiberProd.instPrincipalBundle`: the fibre product of a principal
  `G`-bundle and a principal `H`-bundle is a principal `(G × H)`-bundle.
* `TauCeti.PrincipalBundle.FiberProd.continuous_iff`: a map into the total space is continuous
  exactly when its two components are.
* `TauCeti.PrincipalBundle.FiberProd.division_mk`: the division map is componentwise.

## References

* D. Husemoller, *Fibre Bundles*, 3rd ed., Graduate Texts in Mathematics 20, Springer, 1994,
  Chapter 4, §4 (fibre products of principal bundles).
-/

public section

open Bundle MulOpposite Topology

namespace TauCeti.PrincipalBundle

variable {B : Type*}

/-- The **fibre product** of two bundles `P` and `Q` over the same base: its fibre over `b` is
`P b × Q b`. For a principal `G`-bundle `P` and a principal `H`-bundle `Q` it is a principal
`(G × H)`-bundle (`TauCeti.PrincipalBundle.FiberProd.instPrincipalBundle`). -/
@[expose]
def FiberProd (P Q : B → Type*) (b : B) : Type _ :=
  P b × Q b

namespace FiberProd

variable {P Q : B → Type*} {b : B}

/-- The point `(p, q)` of the fibre product. -/
@[expose]
def mk (p : P b) (q : Q b) : FiberProd P Q b :=
  (p, q)

/-- The first component of a point of the fibre product. -/
@[expose]
def fst (z : FiberProd P Q b) : P b :=
  Prod.fst (α := P b) (β := Q b) z

/-- The second component of a point of the fibre product. -/
@[expose]
def snd (z : FiberProd P Q b) : Q b :=
  Prod.snd (α := P b) (β := Q b) z

@[simp]
theorem fst_mk (p : P b) (q : Q b) : (mk p q).fst = p :=
  (rfl)

@[simp]
theorem snd_mk (p : P b) (q : Q b) : (mk p q).snd = q :=
  (rfl)

@[simp]
theorem mk_fst_snd (z : FiberProd P Q b) : mk z.fst z.snd = z :=
  (rfl)

@[ext]
theorem ext {z w : FiberProd P Q b} (h₁ : z.fst = w.fst) (h₂ : z.snd = w.snd) : z = w :=
  Prod.ext (α := P b) (β := Q b) h₁ h₂

/-- Two points `(p, q)` and `(p', q')` of the fibre product are equal exactly when `p = p'` and
`q = q'`. -/
@[simp]
theorem mk_inj {p p' : P b} {q q' : Q b} : mk p q = mk p' q' ↔ p = p' ∧ q = q' :=
  Prod.mk_inj (α := P b) (β := Q b)

/-- The fibres of the fibre product carry the product topology. -/
instance instTopologicalSpace [∀ b, TopologicalSpace (P b)] [∀ b, TopologicalSpace (Q b)]
    (b : B) : TopologicalSpace (FiberProd P Q b) :=
  inferInstanceAs (TopologicalSpace (P b × Q b))

variable (G H : Type*)

/-- The total space of the fibre product carries the topology induced from the product of the two
total spaces (`FiberBundle.Prod.topologicalSpace`). -/
instance instTopologicalSpaceTotalSpace [TopologicalSpace (TotalSpace G P)]
    [TopologicalSpace (TotalSpace H Q)] : TopologicalSpace (TotalSpace (G × H) (FiberProd P Q)) :=
  FiberBundle.Prod.topologicalSpace G P H Q

section Topology

variable {G H} [TopologicalSpace (TotalSpace G P)] [TopologicalSpace (TotalSpace H Q)]

/-- The map from the total space of the fibre product to the product of the two total spaces is
inducing. -/
theorem isInducing_diag :
    IsInducing fun z : TotalSpace (G × H) (FiberProd P Q) ↦
      ((⟨z.proj, z.snd.fst⟩ : TotalSpace G P), (⟨z.proj, z.snd.snd⟩ : TotalSpace H Q)) :=
  FiberBundle.Prod.isInducing_diag G P H Q

/-- **Continuity into the fibre product**: a map into the total space of the fibre product is
continuous exactly when its two components, read in the total spaces of `P` and `Q`, are. -/
theorem continuous_iff {Z : Type*} [TopologicalSpace Z]
    {f : Z → TotalSpace (G × H) (FiberProd P Q)} :
    Continuous f ↔ Continuous (fun z ↦ (⟨(f z).proj, (f z).snd.fst⟩ : TotalSpace G P)) ∧
      Continuous (fun z ↦ (⟨(f z).proj, (f z).snd.snd⟩ : TotalSpace H Q)) :=
  isInducing_diag.continuous_iff.trans continuous_prodMk

/-- The first component of a point of the fibre product, as a point of the total space of `P`,
depends continuously on the point. -/
@[fun_prop]
theorem continuous_totalSpaceMk_fst :
    Continuous fun z : TotalSpace (G × H) (FiberProd P Q) ↦
      (⟨z.proj, z.snd.fst⟩ : TotalSpace G P) :=
  (continuous_iff.1 continuous_id).1

/-- The second component of a point of the fibre product, as a point of the total space of `Q`,
depends continuously on the point. -/
@[fun_prop]
theorem continuous_totalSpaceMk_snd :
    Continuous fun z : TotalSpace (G × H) (FiberProd P Q) ↦
      (⟨z.proj, z.snd.snd⟩ : TotalSpace H Q) :=
  (continuous_iff.1 continuous_id).2

/-- A pair of continuous families of points of `P` and `Q` over the same varying base point is a
continuous family of points of the fibre product. -/
theorem _root_.Continuous.totalSpaceMk_fiberProdMk {Z : Type*} [TopologicalSpace Z] {f : Z → B}
    {p : ∀ z, P (f z)} {q : ∀ z, Q (f z)} (hp : Continuous fun z ↦ TotalSpace.mk' G (f z) (p z))
    (hq : Continuous fun z ↦ TotalSpace.mk' H (f z) (q z)) :
    Continuous fun z ↦ TotalSpace.mk' (G × H) (E := FiberProd P Q) (f z) (mk (p z) (q z)) :=
  continuous_iff.2 ⟨hp, hq⟩

end Topology

section Action

variable {G H} [Group G] [Group H] [∀ b, MulAction Gᵐᵒᵖ (P b)] [∀ b, MulAction Hᵐᵒᵖ (Q b)]

/-- The componentwise right action of `G × H` on the fibres of the fibre product:
`(p, q) • (g, h) = (p • g, q • h)`. -/
instance instMulAction (b : B) : MulAction (G × H)ᵐᵒᵖ (FiberProd P Q b) where
  smul g z := mk (op g.unop.1 • z.fst) (op g.unop.2 • z.snd)
  one_smul z := ext (one_smul Gᵐᵒᵖ z.fst) (one_smul Hᵐᵒᵖ z.snd)
  mul_smul g g' z := ext (mul_smul (op g.unop.1) (op g'.unop.1) z.fst)
    (mul_smul (op g.unop.2) (op g'.unop.2) z.snd)

@[simp]
theorem op_smul_mk (p : P b) (q : Q b) (g : G) (h : H) :
    op (g, h) • mk p q = mk (op g • p) (op h • q) :=
  (rfl)

@[simp]
theorem fst_smul (z : FiberProd P Q b) (g : (G × H)ᵐᵒᵖ) : (g • z).fst = op g.unop.1 • z.fst :=
  (rfl)

@[simp]
theorem snd_smul (z : FiberProd P Q b) (g : (G × H)ᵐᵒᵖ) : (g • z).snd = op g.unop.2 • z.snd :=
  (rfl)

end Action

section Bundle

variable [TopologicalSpace B] [TopologicalSpace G] [TopologicalSpace H]
  [TopologicalSpace (TotalSpace G P)] [∀ b, TopologicalSpace (P b)] [FiberBundle G P]
  [TopologicalSpace (TotalSpace H Q)] [∀ b, TopologicalSpace (Q b)] [FiberBundle H Q]

/-- The fibre product of two fibre bundles with model fibres `G` and `H` is a fibre bundle with
model fibre `G × H`: Mathlib's fibrewise product `FiberBundle.prod`, whose trivializations are
the products of trivializations of `P` and `Q`. The junk values of the inverse trivializations
outside their base sets are the points with coordinate `1` in the preferred trivializations. -/
noncomputable instance instFiberBundle [One G] [One H] : FiberBundle (G × H) (FiberProd P Q) :=
  letI : ∀ b, Zero (P b) := fun b ↦ ⟨(FiberBundle.homeomorphAt G P b).symm 1⟩
  letI : ∀ b, Zero (Q b) := fun b ↦ ⟨(FiberBundle.homeomorphAt H Q b).symm 1⟩
  FiberBundle.prod G P H Q

variable [Group G] [Group H] [∀ b, MulAction Gᵐᵒᵖ (P b)] [∀ b, MulAction Hᵐᵒᵖ (Q b)]

/-- **The fibre product of principal bundles is principal**: for a principal `G`-bundle `P` and a
principal `H`-bundle `Q` over the same base, the fibre product, with `G × H` acting
componentwise, is a principal `(G × H)`-bundle. Each trivialization of its atlas is a product
`e₁.prod e₂` of equivariant trivializations, so it is equivariant. -/
instance instPrincipalBundle [PrincipalBundle G P] [PrincipalBundle H Q] :
    PrincipalBundle (G × H) (FiberProd P Q) where
  isEquivariant_trivialization' e he := by
    obtain ⟨e₁, e₂, h₁, h₂, rfl⟩ := he.out
    exact ⟨fun b hb z g ↦ Prod.ext (e₁.snd_apply_smul hb.1 z.fst g.1)
      (e₂.snd_apply_smul hb.2 z.snd g.2)⟩

/-- **The division map of the fibre product is componentwise**: the element of `G × H` carrying
`(p, q)` to `(p', q')` is the pair of the element of `G` carrying `p` to `p'` and the element of
`H` carrying `q` to `q'`. -/
@[simp]
theorem division_mk [PrincipalBundle G P] [PrincipalBundle H Q] (p p' : P b) (q q' : Q b) :
    division (G × H) (mk p q) (mk p' q') = (division G p p', division H q q') :=
  division_eq_iff.2 (by rw [op_smul_mk, smul_division, smul_division])

end Bundle

end FiberProd

namespace Equiv

variable {G H : Type*} [Group G] [Group H] {P P' P'' Q Q' Q'' : B → Type*}
  [TopologicalSpace (TotalSpace G P)] [TopologicalSpace (TotalSpace G P')]
  [TopologicalSpace (TotalSpace G P'')] [TopologicalSpace (TotalSpace H Q)]
  [TopologicalSpace (TotalSpace H Q')] [TopologicalSpace (TotalSpace H Q'')]
  [∀ b, MulAction Gᵐᵒᵖ (P b)] [∀ b, MulAction Gᵐᵒᵖ (P' b)] [∀ b, MulAction Gᵐᵒᵖ (P'' b)]
  [∀ b, MulAction Hᵐᵒᵖ (Q b)] [∀ b, MulAction Hᵐᵒᵖ (Q' b)] [∀ b, MulAction Hᵐᵒᵖ (Q'' b)]

/-- **Equivalences of fibre products**: equivalences `φ : P ≃ P'` of principal `G`-bundles and
`ψ : Q ≃ Q'` of principal `H`-bundles induce the equivalence `(p, q) ↦ (φ p, ψ q)` of the fibre
products. -/
@[expose]
def fiberProd (φ : Equiv G P P') (ψ : Equiv H Q Q') :
    Equiv (G × H) (FiberProd P Q) (FiberProd P' Q') where
  toEquiv b :=
    { toFun z := FiberProd.mk (φ.toEquiv b z.fst) (ψ.toEquiv b z.snd)
      invFun z := FiberProd.mk ((φ.toEquiv b).symm z.fst) ((ψ.toEquiv b).symm z.snd)
      left_inv z := by simp
      right_inv z := by simp }
  continuous_toFun :=
    (φ.continuous_toFun.comp FiberProd.continuous_totalSpaceMk_fst).totalSpaceMk_fiberProdMk
      (ψ.continuous_toFun.comp FiberProd.continuous_totalSpaceMk_snd)
  continuous_invFun :=
    (φ.continuous_invFun.comp FiberProd.continuous_totalSpaceMk_fst).totalSpaceMk_fiberProdMk
      (ψ.continuous_invFun.comp FiberProd.continuous_totalSpaceMk_snd)
  map_smul b z g := congrArg₂ FiberProd.mk (φ.map_smul b z.fst g.1) (ψ.map_smul b z.snd g.2)

variable {b : B}

@[simp]
theorem fiberProd_toEquiv_mk (φ : Equiv G P P') (ψ : Equiv H Q Q') (p : P b) (q : Q b) :
    (φ.fiberProd ψ).toEquiv b (FiberProd.mk p q) = FiberProd.mk (φ.toEquiv b p) (ψ.toEquiv b q) :=
  (rfl)

@[simp]
theorem fiberProd_toEquiv_fst (φ : Equiv G P P') (ψ : Equiv H Q Q') (z : FiberProd P Q b) :
    ((φ.fiberProd ψ).toEquiv b z).fst = φ.toEquiv b z.fst :=
  (rfl)

@[simp]
theorem fiberProd_toEquiv_snd (φ : Equiv G P P') (ψ : Equiv H Q Q') (z : FiberProd P Q b) :
    ((φ.fiberProd ψ).toEquiv b z).snd = ψ.toEquiv b z.snd :=
  (rfl)

@[simp]
theorem fiberProd_toEquiv_symm_fst (φ : Equiv G P P') (ψ : Equiv H Q Q') (z : FiberProd P' Q' b) :
    (((φ.fiberProd ψ).toEquiv b).symm z).fst = (φ.toEquiv b).symm z.fst :=
  (rfl)

@[simp]
theorem fiberProd_toEquiv_symm_snd (φ : Equiv G P P') (ψ : Equiv H Q Q') (z : FiberProd P' Q' b) :
    (((φ.fiberProd ψ).toEquiv b).symm z).snd = (ψ.toEquiv b).symm z.snd :=
  (rfl)

/-- The identities of `P` and `Q` induce the identity of the fibre product. -/
@[simp]
theorem fiberProd_refl : (refl G P).fiberProd (refl H Q) = refl (G × H) (FiberProd P Q) :=
  (rfl)

/-- The inverse of the equivalence of fibre products induced by `φ` and `ψ` is induced by the
inverses of `φ` and `ψ`. -/
@[simp]
theorem fiberProd_symm (φ : Equiv G P P') (ψ : Equiv H Q Q') :
    (φ.fiberProd ψ).symm = φ.symm.fiberProd ψ.symm :=
  (rfl)

/-- The composite of the equivalences of fibre products induced by `φ, ψ` and by `φ', ψ'` is
induced by the composites `φ.trans φ'` and `ψ.trans ψ'`. -/
@[simp]
theorem fiberProd_trans (φ : Equiv G P P') (φ' : Equiv G P' P'') (ψ : Equiv H Q Q')
    (ψ' : Equiv H Q' Q'') : (φ.fiberProd ψ).trans (φ'.fiberProd ψ') =
      (φ.trans φ').fiberProd (ψ.trans ψ') :=
  (rfl)

end Equiv

end TauCeti.PrincipalBundle

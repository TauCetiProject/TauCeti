/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.Pi.Finset
public import TauCeti.Algebra.Group.Sum
public import TauCeti.Analysis.Normed.Module.Sum
public import TauCeti.Data.Sum.Basic
public import TauCeti.Topology.Homeomorph.Pi
public import TauCeti.Topology.ImplicitAtlas.Basic
public import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

/-!
# Products of implicit atlases

Let `𝒜₁` be an implicit atlas of virtual dimension `d₁` on `X₁`, indexed by `A₁`, and `𝒜₂` one of
virtual dimension `d₂` on `X₂`, indexed by `A₂`. Their *product* `𝒜₁.prod 𝒜₂` is an implicit atlas
of virtual dimension `d₁ + d₂` on `X₁ × X₂`, indexed by `A₁ ⊕ A₂` (Pardon, Definition 6.3.1). A
finite set `I ⊆ A₁ ⊕ A₂` is the pair of its left and right parts `I₁ = I.toLeft ⊆ A₁` and
`I₂ = I.toRight ⊆ A₂`, and at `I` the product atlas has:

* the groups `Γ_α` and obstruction representations `E_α` of the factor that `α` comes from
  (`Sum.elim Γ₁ Γ₂` and `Sum.elim E₁ E₂`, with representations `TauCeti.ImplicitAtlas.sumElimRep`),
  so that `Γ_I = Γ₁_(I₁) × Γ₂_(I₂)` as groups (`MulEquiv.piFinsetSum`) and
  `E_I = E₁_(I₁) × E₂_(I₂)` as topological spaces (`Homeomorph.piFinsetSum`, whose underlying
  equivalence is `Equiv.piFinsetSum`); these split groups and spaces, not representations or
  linear spaces;
* the thickening `X₁_(I₁) × X₂_(I₂)`, with `Γ_I` acting factorwise
  (`TauCeti.ImplicitAtlas.prodAct`);
* the Kuranishi map `s_α` of the factor of `α`, on the corresponding coordinate
  (`TauCeti.ImplicitAtlas.prodKuranishi`), so that the zero set `Z_IJ` is `Z₁_(I₁J₁) × Z₂_(I₂J₂)`
  (`TauCeti.ImplicitAtlas.kuranishiZeroSet_prodKuranishi`);
* the regular locus `X₁_(I₁)^reg × X₂_(I₂)^reg` and the footprint map `ψ₁_(I₁J₁) × ψ₂_(I₂J₂)`.

Every axiom of `TauCeti.ImplicitAtlas.Core` holds factorwise (`TauCeti.ImplicitAtlas.Core.prod`).
The quotient axiom is the one that needs an argument: a product of quotient maps need not be a
quotient map, but the footprint maps are open quotient maps onto their images
(`TauCeti.ImplicitAtlas.Core.isOpenQuotientMap_footprintMap`), and products of open quotient maps
are open quotient maps. The regular footprints are products,
`V_I = V₁_(I₁) × V₂_(I₂)` (`TauCeti.ImplicitAtlas.Core.footprint_prod`), so they cover
`X₁ × X₂`: a point `(y₁, y₂)` with `y₁ ∈ V₁_(I₁)` and `y₂ ∈ V₂_(I₂)` lies in the footprint of
`I₁ ⊔ I₂`. Finally, the local product models multiply (`TauCeti.ImplicitAtlas.prod`): models
`ℝ^(n₁) × E₁_(J₁ \ I₁)` and `ℝ^(n₂) × E₂_(J₂ \ I₂)` of the extra obstructions of the two factors,
with `n₁ = d₁ + m₁_(I₁)` and `n₂ = d₂ + m₂_(I₂)`, give the model
`ℝ^(n₁ + n₂) × E_(J \ I)` of the product, of dimension `n₁ + n₂ = (d₁ + d₂) + m_I`.

This is the boundaryless, unstratified product. The products of boundary atlases, their
cell-like corner stratifications and the product of virtual classes are not treated here.

## Main definitions

* `TauCeti.ImplicitAtlas.Core.prod`: the product of the data and axioms of two implicit atlases
  other than their local product models.
* `TauCeti.ImplicitAtlas.prod`: the product of two implicit atlases, of virtual dimension
  `d₁ + d₂`.

## Main results

* `TauCeti.ImplicitAtlas.Core.footprintMap_prod` and
  `TauCeti.ImplicitAtlas.Core.range_footprintMap_prod`: the footprint maps of the product and their
  images are the products of those of the factors.
* `TauCeti.ImplicitAtlas.Core.footprint_prod`: the regular footprints of the product are the
  products of the regular footprints of the factors.

## References

* J. Pardon, *An algebraic approach to virtual fundamental cycles on moduli spaces of
  pseudo-holomorphic curves*, Geom. Topol. 20 (2016), 779–1034, Definition 6.3.1 (product
  implicit atlases).
-/

public section

open Set Topology
open Finset hiding range

namespace TauCeti.ImplicitAtlas

universe u v

variable {A₁ A₂ : Type*}

section SumElim

variable {Γ₁ : A₁ → Type u} {Γ₂ : A₂ → Type u} {E₁ : A₁ → Type v} {E₂ : A₂ → Type v}
  [∀ a, Group (Γ₁ a)] [∀ b, Group (Γ₂ b)] [∀ a, NormedAddCommGroup (E₁ a)]
  [∀ b, NormedAddCommGroup (E₂ b)] [∀ a, NormedSpace ℝ (E₁ a)] [∀ b, NormedSpace ℝ (E₂ b)]
  (ρ₁ : ∀ a, Representation ℝ (Γ₁ a) (E₁ a)) (ρ₂ : ∀ b, Representation ℝ (Γ₂ b) (E₂ b))

/-- The obstruction representations of a product atlas: `Γ_α` acts on `E_α` as in the factor
that `α ∈ A₁ ⊕ A₂` comes from. -/
def sumElimRep : ∀ α : A₁ ⊕ A₂, Representation ℝ (Sum.elim Γ₁ Γ₂ α) (Sum.elim E₁ E₂ α)
  | .inl a => ρ₁ a
  | .inr b => ρ₂ b

/-- At a left index `a`, the representation `sumElimRep ρ₁ ρ₂` is `ρ₁ a`. -/
@[simp]
theorem sumElimRep_inl (a : A₁) : sumElimRep ρ₁ ρ₂ (.inl a) = ρ₁ a :=
  (rfl)

/-- At a right index `b`, the representation `sumElimRep ρ₁ ρ₂` is `ρ₂ b`. -/
@[simp]
theorem sumElimRep_inr (b : A₂) : sumElimRep ρ₁ ρ₂ (.inr b) = ρ₂ b :=
  (rfl)

end SumElim

/-! ### The data of a product atlas -/

section Data

variable {Γ₁ : A₁ → Type u} {Γ₂ : A₂ → Type u} [∀ a, Group (Γ₁ a)] [∀ b, Group (Γ₂ b)]
  {T₁ : Finset A₁ → Type*} {T₂ : Finset A₂ → Type*} [∀ I, TopologicalSpace (T₁ I)]
  [∀ I, TopologicalSpace (T₂ I)]

/-- The action of `Γ_I = Γ₁_(I.toLeft) × Γ₂_(I.toRight)` on the product thickening
`X₁_(I.toLeft) × X₂_(I.toRight)`, factor by factor. -/
def prodAct (act₁ : ∀ I : Finset A₁, ((a : I) → Γ₁ a) →* (T₁ I ≃ₜ T₁ I))
    (act₂ : ∀ I : Finset A₂, ((b : I) → Γ₂ b) →* (T₂ I ≃ₜ T₂ I)) (I : Finset (A₁ ⊕ A₂)) :
    ((α : I) → Sum.elim Γ₁ Γ₂ α) →* (T₁ I.toLeft × T₂ I.toRight ≃ₜ T₁ I.toLeft × T₂ I.toRight)
    where
  toFun g :=
    (act₁ I.toLeft ((Equiv.piFinsetSum (Sum.elim Γ₁ Γ₂) I I.toLeft I.toRight) g).1).prodCongr
      (act₂ I.toRight ((Equiv.piFinsetSum (Sum.elim Γ₁ Γ₂) I I.toLeft I.toRight) g).2)
  map_one' := Homeomorph.ext fun x ↦ Prod.ext (DFunLike.congr_fun (map_one (act₁ I.toLeft)) x.1)
    (DFunLike.congr_fun (map_one (act₂ I.toRight)) x.2)
  map_mul' g g' := by
    -- `Equiv.piFinsetSum` underlies the multiplicative equivalence `MulEquiv.piFinsetSum`.
    have h := map_mul (MulEquiv.piFinsetSum (Sum.elim Γ₁ Γ₂) I I.toLeft I.toRight) g g'
    rw [MulEquiv.coe_piFinsetSum] at h
    set e := Equiv.piFinsetSum (Sum.elim Γ₁ Γ₂) I I.toLeft I.toRight
    ext x
    · exact (congrArg (fun p ↦ act₁ I.toLeft p.1 x.1) h).trans
        (DFunLike.congr_fun (map_mul (act₁ I.toLeft) (e g).1 (e g').1) x.1)
    · exact (congrArg (fun p ↦ act₂ I.toRight p.2 x.2) h).trans
        (DFunLike.congr_fun (map_mul (act₂ I.toRight) (e g).2 (e g').2) x.2)

@[simp]
theorem prodAct_apply (act₁ : ∀ I : Finset A₁, ((a : I) → Γ₁ a) →* (T₁ I ≃ₜ T₁ I))
    (act₂ : ∀ I : Finset A₂, ((b : I) → Γ₂ b) →* (T₂ I ≃ₜ T₂ I)) (I : Finset (A₁ ⊕ A₂))
    (g : (α : I) → Sum.elim Γ₁ Γ₂ α) (x : T₁ I.toLeft × T₂ I.toRight) :
    prodAct act₁ act₂ I g x =
      (act₁ I.toLeft ((Equiv.piFinsetSum (Sum.elim Γ₁ Γ₂) I I.toLeft I.toRight) g).1 x.1,
        act₂ I.toRight ((Equiv.piFinsetSum (Sum.elim Γ₁ Γ₂) I I.toLeft I.toRight) g).2 x.2) :=
  (rfl)

end Data

section Kuranishi

variable {T₁ : Finset A₁ → Type*} {T₂ : Finset A₂ → Type*} {E₁ : A₁ → Type v} {E₂ : A₂ → Type v}

/-- The Kuranishi maps of a product atlas: for `α ∈ J`, the Kuranishi map `s_α` of the factor that
`α` comes from, on the corresponding coordinate of `X₁_(J.toLeft) × X₂_(J.toRight)`. -/
def prodKuranishi (s₁ : ∀ (J : Finset A₁) (a : J), T₁ J → E₁ a)
    (s₂ : ∀ (J : Finset A₂) (b : J), T₂ J → E₂ b) :
    ∀ (J : Finset (A₁ ⊕ A₂)) (α : J), T₁ J.toLeft × T₂ J.toRight → Sum.elim E₁ E₂ α
  | J, ⟨.inl a, h⟩, x => s₁ J.toLeft ⟨a, mem_toLeft.2 h⟩ x.1
  | J, ⟨.inr b, h⟩, x => s₂ J.toRight ⟨b, mem_toRight.2 h⟩ x.2

variable (s₁ : ∀ (J : Finset A₁) (a : J), T₁ J → E₁ a)
  (s₂ : ∀ (J : Finset A₂) (b : J), T₂ J → E₂ b)

@[simp]
theorem prodKuranishi_inl (J : Finset (A₁ ⊕ A₂)) (a : A₁) (h : .inl a ∈ J)
    (x : T₁ J.toLeft × T₂ J.toRight) :
    prodKuranishi s₁ s₂ J ⟨.inl a, h⟩ x = s₁ J.toLeft ⟨a, mem_toLeft.2 h⟩ x.1 :=
  (rfl)

@[simp]
theorem prodKuranishi_inr (J : Finset (A₁ ⊕ A₂)) (b : A₂) (h : .inr b ∈ J)
    (x : T₁ J.toLeft × T₂ J.toRight) :
    prodKuranishi s₁ s₂ J ⟨.inr b, h⟩ x = s₂ J.toRight ⟨b, mem_toRight.2 h⟩ x.2 :=
  (rfl)

variable [∀ a, NormedAddCommGroup (E₁ a)] [∀ b, NormedAddCommGroup (E₂ b)]

/-- The zero set `Z_IJ` of the product Kuranishi maps is the product `Z₁_(I₁J₁) × Z₂_(I₂J₂)` of the
zero sets of the left and right parts. -/
@[simp]
theorem kuranishiZeroSet_prodKuranishi (I J : Finset (A₁ ⊕ A₂)) :
    kuranishiZeroSet (prodKuranishi s₁ s₂) I J =
      kuranishiZeroSet s₁ I.toLeft J.toLeft ×ˢ kuranishiZeroSet s₂ I.toRight J.toRight := by
  ext x
  simp only [mem_kuranishiZeroSet, mem_prod]
  refine ⟨fun hx ↦ ⟨fun a ha ↦ hx ⟨.inl a, mem_toLeft.1 a.property⟩ (by simpa using ha),
    fun b hb ↦ hx ⟨.inr b, mem_toRight.1 b.property⟩ (by simpa using hb)⟩, ?_⟩
  rintro ⟨hx₁, hx₂⟩ ⟨α | α, hα⟩ hαI
  · exact hx₁ ⟨α, mem_toLeft.2 hα⟩ (by simpa using hαI)
  · exact hx₂ ⟨α, mem_toRight.2 hα⟩ (by simpa using hαI)

/-- The identification of the zero set `Z_IJ` of the product Kuranishi maps with
`Z₁_(I₁J₁) × Z₂_(I₂J₂)`. -/
private def zeroSetHomeomorph [∀ I, TopologicalSpace (T₁ I)] [∀ I, TopologicalSpace (T₂ I)]
    (I J : Finset (A₁ ⊕ A₂)) :
    kuranishiZeroSet (prodKuranishi s₁ s₂) I J ≃ₜ
      kuranishiZeroSet s₁ I.toLeft J.toLeft × kuranishiZeroSet s₂ I.toRight J.toRight :=
  (Homeomorph.setCongr (kuranishiZeroSet_prodKuranishi s₁ s₂ I J)).trans (Homeomorph.Set.prod _ _)

end Kuranishi

/-! ### The product of the core data -/

variable [DecidableEq A₁] [DecidableEq A₂]
  {Γ₁ : A₁ → Type u} [∀ a, Group (Γ₁ a)] [∀ a, Finite (Γ₁ a)]
  {E₁ : A₁ → Type v} [∀ a, NormedAddCommGroup (E₁ a)] [∀ a, NormedSpace ℝ (E₁ a)]
  [∀ a, FiniteDimensional ℝ (E₁ a)] {ρ₁ : ∀ a, Representation ℝ (Γ₁ a) (E₁ a)}
  {T₁ : Finset A₁ → Type*} [∀ I, TopologicalSpace (T₁ I)] [∀ I, T2Space (T₁ I)]
  {act₁ : ∀ I : Finset A₁, ((a : I) → Γ₁ a) →* (T₁ I ≃ₜ T₁ I)}
  {X₁ : Type*} [TopologicalSpace X₁]
  {Γ₂ : A₂ → Type u} [∀ b, Group (Γ₂ b)] [∀ b, Finite (Γ₂ b)]
  {E₂ : A₂ → Type v} [∀ b, NormedAddCommGroup (E₂ b)] [∀ b, NormedSpace ℝ (E₂ b)]
  [∀ b, FiniteDimensional ℝ (E₂ b)] {ρ₂ : ∀ b, Representation ℝ (Γ₂ b) (E₂ b)}
  {T₂ : Finset A₂ → Type*} [∀ I, TopologicalSpace (T₂ I)] [∀ I, T2Space (T₂ I)]
  {act₂ : ∀ I : Finset A₂, ((b : I) → Γ₂ b) →* (T₂ I ≃ₜ T₂ I)}
  {X₂ : Type*} [TopologicalSpace X₂]

namespace Core

variable (𝒜₁ : ImplicitAtlas.Core Γ₁ E₁ ρ₁ T₁ act₁ X₁) (𝒜₂ : ImplicitAtlas.Core Γ₂ E₂ ρ₂ T₂ act₂ X₂)

/-- The footprint map `ψ_IJ = ψ₁_(I₁J₁) × ψ₂_(I₂J₂)` of a product atlas. -/
private def prodFootprintMap {I J : Finset (A₁ ⊕ A₂)} (h : I ⊆ J) :
    kuranishiZeroSet (prodKuranishi 𝒜₁.kuranishi 𝒜₂.kuranishi) I J → T₁ I.toLeft × T₂ I.toRight :=
  Prod.map (𝒜₁.footprintMap (toLeft_subset_toLeft h))
      (𝒜₂.footprintMap (toRight_subset_toRight h)) ∘
    zeroSetHomeomorph 𝒜₁.kuranishi 𝒜₂.kuranishi I J

/-- The footprint map `ψ_IJ` of a product atlas evaluates factorwise, on the two coordinates of a
point of `Z_IJ = Z₁_(I₁J₁) × Z₂_(I₂J₂)`. -/
private theorem prodFootprintMap_apply {I J : Finset (A₁ ⊕ A₂)} (h : I ⊆ J)
    (x : kuranishiZeroSet (prodKuranishi 𝒜₁.kuranishi 𝒜₂.kuranishi) I J) :
    prodFootprintMap 𝒜₁ 𝒜₂ h x =
      (𝒜₁.footprintMap (toLeft_subset_toLeft h)
          ⟨x.val.1, ((kuranishiZeroSet_prodKuranishi _ _ I J).subset x.property).1⟩,
        𝒜₂.footprintMap (toRight_subset_toRight h)
          ⟨x.val.2, ((kuranishiZeroSet_prodKuranishi _ _ I J).subset x.property).2⟩) :=
  -- `zeroSetHomeomorph` is `Homeomorph.setCongr` followed by `Homeomorph.Set.prod`, which send
  -- `x` to the pair of its coordinates.
  (rfl)

private theorem range_prodFootprintMap {I J : Finset (A₁ ⊕ A₂)} (h : I ⊆ J) :
    range (prodFootprintMap 𝒜₁ 𝒜₂ h) =
      range (𝒜₁.footprintMap (toLeft_subset_toLeft h)) ×ˢ
        range (𝒜₂.footprintMap (toRight_subset_toRight h)) := by
  rw [prodFootprintMap, (zeroSetHomeomorph _ _ I J).surjective.range_comp, range_prodMap]

/-- The footprint map `ψ_IJ` of a product atlas, corestricted to its image, is a quotient map: up to
the identifications of the zero sets and of the images with products, it is the product of the
corestrictions of `ψ₁_(I₁J₁)` and `ψ₂_(I₂J₂)`, which are open quotient maps. -/
private theorem isQuotientMap_rangeFactorization_prodFootprintMap {I J : Finset (A₁ ⊕ A₂)}
    (h : I ⊆ J) : IsQuotientMap (rangeFactorization (prodFootprintMap 𝒜₁ 𝒜₂ h)) := by
  have key : rangeFactorization (prodFootprintMap 𝒜₁ 𝒜₂ h) =
      Homeomorph.setCongr (range_prodFootprintMap 𝒜₁ 𝒜₂ h).symm ∘
        (Homeomorph.Set.prod _ _).symm ∘
          Prod.map (rangeFactorization (𝒜₁.footprintMap (toLeft_subset_toLeft h)))
            (rangeFactorization (𝒜₂.footprintMap (toRight_subset_toRight h))) ∘
            zeroSetHomeomorph 𝒜₁.kuranishi 𝒜₂.kuranishi I J := by
    -- Both sides take `x` to the point `prodFootprintMap 𝒜₁ 𝒜₂ h x` of the image: on the right,
    -- `Homeomorph.setCongr` and `(Homeomorph.Set.prod _ _).symm` keep the underlying pair.
    funext x
    exact Subtype.ext (prodFootprintMap_apply 𝒜₁ 𝒜₂ h x)
  rw [key]
  exact (Homeomorph.setCongr _).isQuotientMap.comp <|
    (Homeomorph.Set.prod _ _).symm.isQuotientMap.comp <|
      ((𝒜₁.isOpenQuotientMap_footprintMap _).prodMap
        (𝒜₂.isOpenQuotientMap_footprintMap _)).isQuotientMap.comp
          (zeroSetHomeomorph _ _ _ _).isQuotientMap

/-- The fibres of the footprint map `ψ_IJ` of a product atlas are the orbits of `Γ_(J \ I)`: those
of `ψ₁_(I₁J₁)` and `ψ₂_(I₂J₂)` are the orbits of `Γ₁_(J₁ \ I₁)` and `Γ₂_(J₂ \ I₂)`. -/
private theorem prodFootprintMap_eq_prodFootprintMap_iff {I J : Finset (A₁ ⊕ A₂)} (h : I ⊆ J)
    (x y : kuranishiZeroSet (prodKuranishi 𝒜₁.kuranishi 𝒜₂.kuranishi) I J) :
    prodFootprintMap 𝒜₁ 𝒜₂ h x = prodFootprintMap 𝒜₁ 𝒜₂ h y ↔
      ∃ g : (α : J) → Sum.elim Γ₁ Γ₂ α,
        Finset.restrict₂ (π := Sum.elim Γ₁ Γ₂) h g = 1 ∧ prodAct act₁ act₂ J g x = y := by
  let e := Equiv.piFinsetSum (Sum.elim Γ₁ Γ₂) J J.toLeft J.toRight
  rw [prodFootprintMap_apply, prodFootprintMap_apply, Prod.mk.injEq,
    𝒜₁.footprintMap_eq_footprintMap_iff, 𝒜₂.footprintMap_eq_footprintMap_iff]
  constructor
  · rintro ⟨⟨g₁, hg₁, hx₁⟩, g₂, hg₂, hx₂⟩
    refine ⟨e.symm (g₁, g₂), (restrict₂_eq_one_iff_piFinsetSum h _).2 ?_, ?_⟩
    · rw [e.apply_symm_apply]
      exact ⟨hg₁, hg₂⟩
    · rw [prodAct_apply, e.apply_symm_apply]
      exact Prod.ext hx₁ hx₂
  · rintro ⟨g, hg, hgx⟩
    rw [prodAct_apply, Prod.ext_iff] at hgx
    obtain ⟨hg₁, hg₂⟩ := (restrict₂_eq_one_iff_piFinsetSum h g).1 hg
    exact ⟨⟨(e g).1, hg₁, hgx.1⟩, (e g).2, hg₂, hgx.2⟩

/-- The **product** of the data and axioms, other than the local product models, of implicit
atlases `𝒜₁` on `X₁` and `𝒜₂` on `X₂`, indexed by `A₁ ⊕ A₂`. At a finite `I ⊆ A₁ ⊕ A₂` its
thickening is `X₁_(I.toLeft) × X₂_(I.toRight)`, its regular locus is the product of the regular
loci and its footprint map is the product of the footprint maps. -/
def prod : ImplicitAtlas.Core (Sum.elim Γ₁ Γ₂) (Sum.elim E₁ E₂) (sumElimRep ρ₁ ρ₂)
    (fun I ↦ T₁ I.toLeft × T₂ I.toRight) (prodAct act₁ act₂) (X₁ × X₂) where
  -- `T₁ (∅.toLeft)` is `T₁ ∅` by definition, since `Finset.toLeft ∅` is `∅` by `rfl`.
  baseHomeomorph := 𝒜₁.baseHomeomorph.prodCongr 𝒜₂.baseHomeomorph
  kuranishi := prodKuranishi 𝒜₁.kuranishi 𝒜₂.kuranishi
  continuous_kuranishi
    | _, ⟨.inl _, _⟩ => (𝒜₁.continuous_kuranishi _ _).comp continuous_fst
    | _, ⟨.inr _, _⟩ => (𝒜₂.continuous_kuranishi _ _).comp continuous_snd
  kuranishi_act
    | _, ⟨.inl _, _⟩, _, _ => 𝒜₁.kuranishi_act _ _ _ _
    | _, ⟨.inr _, _⟩, _, _ => 𝒜₂.kuranishi_act _ _ _ _
  regLocus I := 𝒜₁.regLocus I.toLeft ×ˢ 𝒜₂.regLocus I.toRight
  isOpen_regLocus I := (𝒜₁.isOpen_regLocus _).prod (𝒜₂.isOpen_regLocus _)
  act_mem_regLocus I g x hx :=
    ⟨𝒜₁.act_mem_regLocus _ _ _ hx.1, 𝒜₂.act_mem_regLocus _ _ _ hx.2⟩
  footprintMap _ _ := prodFootprintMap 𝒜₁ 𝒜₂
  continuous_footprintMap _ _ h :=
    ((𝒜₁.continuous_footprintMap _).prodMap (𝒜₂.continuous_footprintMap _)).comp
      (zeroSetHomeomorph _ _ _ _).continuous
  footprintMap_act I J h g x hx := by
    simp only [prodFootprintMap_apply, prodAct_apply]
    exact Prod.ext (𝒜₁.footprintMap_act (toLeft_subset_toLeft h) _ ⟨x.val.1, _⟩ _)
      (𝒜₂.footprintMap_act (toRight_subset_toRight h) _ ⟨x.val.2, _⟩ _)
  footprintMap_self I x := Prod.ext (𝒜₁.footprintMap_self _ x.1) (𝒜₂.footprintMap_self _ x.2)
  footprintMap_footprintMap I J K hIJ hJK x hx hx' := by
    simp only [prodFootprintMap_apply]
    exact Prod.ext
      (𝒜₁.footprintMap_footprintMap (toLeft_subset_toLeft hIJ) (toLeft_subset_toLeft hJK)
        ⟨x.val.1, _⟩ _ _)
      (𝒜₂.footprintMap_footprintMap (toRight_subset_toRight hIJ) (toRight_subset_toRight hJK)
        ⟨x.val.2, _⟩ _ _)
  kuranishi_footprintMap
    | _, _, h, x, ⟨.inl a, _⟩ => by
      rw [prodFootprintMap_apply, prodKuranishi_inl, prodKuranishi_inl]
      exact 𝒜₁.kuranishi_footprintMap (toLeft_subset_toLeft h) ⟨x.val.1, _⟩ ⟨a, _⟩
    | _, _, h, x, ⟨.inr b, _⟩ => by
      rw [prodFootprintMap_apply, prodKuranishi_inr, prodKuranishi_inr]
      exact 𝒜₂.kuranishi_footprintMap (toRight_subset_toRight h) ⟨x.val.2, _⟩ ⟨b, _⟩
  isOpen_range_footprintMap I J h := by
    rw [range_prodFootprintMap]
    exact (𝒜₁.isOpen_range_footprintMap _).prod (𝒜₂.isOpen_range_footprintMap _)
  range_footprintMap_inter I J₁ J₂ h₁ h₂ := by
    simp only [range_prodFootprintMap]
    rw [prod_inter_prod, 𝒜₁.range_footprintMap_inter, 𝒜₂.range_footprintMap_inter,
      𝒜₁.range_footprintMap_eq_of_eq _ _ toLeft_union.symm,
      𝒜₂.range_footprintMap_eq_of_eq _ _ toRight_union.symm]
  footprintMap_mem_range_iff I J K hIJ hJK x := by
    simp only [range_prodFootprintMap, prodFootprintMap_apply, mem_prod]
    exact and_congr
      (𝒜₁.footprintMap_mem_range_iff (toLeft_subset_toLeft hIJ) (toLeft_subset_toLeft hJK)
        ⟨x.val.1, _⟩)
      (𝒜₂.footprintMap_mem_range_iff (toRight_subset_toRight hIJ) (toRight_subset_toRight hJK)
        ⟨x.val.2, _⟩)
  isQuotientMap_footprintMap _ _ := isQuotientMap_rangeFactorization_prodFootprintMap 𝒜₁ 𝒜₂
  footprintMap_eq_footprintMap_iff _ _ := prodFootprintMap_eq_prodFootprintMap_iff 𝒜₁ 𝒜₂
  mem_regLocus_of_footprintMap_mem I J h x hx := by
    rw [prodFootprintMap_apply] at hx
    exact ⟨𝒜₁.mem_regLocus_of_footprintMap_mem (toLeft_subset_toLeft h) ⟨x.val.1, _⟩ hx.1,
      𝒜₂.mem_regLocus_of_footprintMap_mem (toRight_subset_toRight h) ⟨x.val.2, _⟩ hx.2⟩
  eq_one_of_act_eq I J h x hx g hg hgx := by
    rw [prodFootprintMap_apply] at hx
    rw [prodAct_apply, Prod.ext_iff] at hgx
    obtain ⟨hg₁, hg₂⟩ := (restrict₂_eq_one_iff_piFinsetSum h g).1 hg
    refine (MulEquiv.piFinsetSum (Sum.elim Γ₁ Γ₂) J J.toLeft J.toRight).map_eq_one_iff.1 ?_
    rw [MulEquiv.coe_piFinsetSum]
    exact Prod.ext (𝒜₁.eq_one_of_act_eq (toLeft_subset_toLeft h) ⟨x.val.1, _⟩ hx.1 _ hg₁ hgx.1)
      (𝒜₂.eq_one_of_act_eq (toRight_subset_toRight h) ⟨x.val.2, _⟩ hx.2 _ hg₂ hgx.2)
  exists_footprintMap_eq y := by
    obtain ⟨I₁, x₁, hx₁, hy₁⟩ := 𝒜₁.exists_footprintMap_eq y.1
    obtain ⟨I₂, x₂, hx₂, hy₂⟩ := 𝒜₂.exists_footprintMap_eq y.2
    -- The left and right parts of `I₁ ⊔ I₂` are `I₁` and `I₂`.
    obtain ⟨x₁, hx₁, hy₁⟩ : ∃ x : kuranishiZeroSet 𝒜₁.kuranishi ∅ (I₁.disjSum I₂).toLeft,
        x.val ∈ 𝒜₁.regLocus _ ∧
          𝒜₁.baseHomeomorph (𝒜₁.footprintMap (Finset.empty_subset _) x) = y.1 := by
      rw [toLeft_disjSum]
      exact ⟨x₁, hx₁, hy₁⟩
    obtain ⟨x₂, hx₂, hy₂⟩ : ∃ x : kuranishiZeroSet 𝒜₂.kuranishi ∅ (I₁.disjSum I₂).toRight,
        x.val ∈ 𝒜₂.regLocus _ ∧
          𝒜₂.baseHomeomorph (𝒜₂.footprintMap (Finset.empty_subset _) x) = y.2 := by
      rw [toRight_disjSum]
      exact ⟨x₂, hx₂, hy₂⟩
    exact ⟨I₁.disjSum I₂, ⟨(x₁.val, x₂.val),
      (kuranishiZeroSet_prodKuranishi 𝒜₁.kuranishi 𝒜₂.kuranishi _ _).symm.subset
        ⟨x₁.property, x₂.property⟩⟩, ⟨hx₁, hx₂⟩, Prod.ext hy₁ hy₂⟩

@[simp]
theorem baseHomeomorph_prod :
    (𝒜₁.prod 𝒜₂).baseHomeomorph = 𝒜₁.baseHomeomorph.prodCongr 𝒜₂.baseHomeomorph :=
  (rfl)

@[simp]
theorem kuranishi_prod : (𝒜₁.prod 𝒜₂).kuranishi = prodKuranishi 𝒜₁.kuranishi 𝒜₂.kuranishi :=
  (rfl)

@[simp]
theorem regLocus_prod (I : Finset (A₁ ⊕ A₂)) :
    (𝒜₁.prod 𝒜₂).regLocus I = 𝒜₁.regLocus I.toLeft ×ˢ 𝒜₂.regLocus I.toRight :=
  (rfl)

/-- The zero set `Z_IJ` of the product atlas is `Z₁_(I₁J₁) × Z₂_(I₂J₂)`. -/
theorem kuranishiZeroSet_prod (I J : Finset (A₁ ⊕ A₂)) :
    kuranishiZeroSet (𝒜₁.prod 𝒜₂).kuranishi I J =
      kuranishiZeroSet 𝒜₁.kuranishi I.toLeft J.toLeft ×ˢ
        kuranishiZeroSet 𝒜₂.kuranishi I.toRight J.toRight := by
  rw [kuranishi_prod]
  exact kuranishiZeroSet_prodKuranishi _ _ I J

/-- The footprint map `ψ_IJ` of the product atlas is `ψ₁_(I₁J₁) × ψ₂_(I₂J₂)`. -/
@[simp]
theorem footprintMap_prod {I J : Finset (A₁ ⊕ A₂)} (h : I ⊆ J)
    (x : kuranishiZeroSet (𝒜₁.prod 𝒜₂).kuranishi I J) :
    (𝒜₁.prod 𝒜₂).footprintMap h x =
      (𝒜₁.footprintMap (toLeft_subset_toLeft h)
          ⟨x.val.1, ((𝒜₁.kuranishiZeroSet_prod 𝒜₂ I J).subset x.property).1⟩,
        𝒜₂.footprintMap (toRight_subset_toRight h)
          ⟨x.val.2, ((𝒜₁.kuranishiZeroSet_prod 𝒜₂ I J).subset x.property).2⟩) :=
  prodFootprintMap_apply 𝒜₁ 𝒜₂ h x

/-- The image `U_IJ` of the footprint map of the product atlas is `U₁_(I₁J₁) × U₂_(I₂J₂)`. -/
@[simp]
theorem range_footprintMap_prod {I J : Finset (A₁ ⊕ A₂)} (h : I ⊆ J) :
    range ((𝒜₁.prod 𝒜₂).footprintMap h) =
      range (𝒜₁.footprintMap (toLeft_subset_toLeft h)) ×ˢ
        range (𝒜₂.footprintMap (toRight_subset_toRight h)) :=
  range_prodFootprintMap 𝒜₁ 𝒜₂ h

/-- The regular footprints of the product atlas are the products of those of the factors:
`V_I = V₁_(I.toLeft) × V₂_(I.toRight)`. -/
@[simp]
theorem footprint_prod (I : Finset (A₁ ⊕ A₂)) :
    (𝒜₁.prod 𝒜₂).footprint I = 𝒜₁.footprint I.toLeft ×ˢ 𝒜₂.footprint I.toRight := by
  ext ⟨y₁, y₂⟩
  simp only [mem_footprint, mem_prod]
  constructor
  · rintro ⟨x, hx, hxy⟩
    rw [footprintMap_prod, baseHomeomorph_prod] at hxy
    exact ⟨⟨_, hx.1, congrArg Prod.fst hxy⟩, _, hx.2, congrArg Prod.snd hxy⟩
  · rintro ⟨⟨x₁, hx₁, hy₁⟩, x₂, hx₂, hy₂⟩
    refine ⟨⟨(x₁.val, x₂.val), (𝒜₁.kuranishiZeroSet_prod 𝒜₂ ∅ I).symm.subset
      ⟨x₁.property, x₂.property⟩⟩, ⟨hx₁, hx₂⟩, ?_⟩
    rw [footprintMap_prod, baseHomeomorph_prod]
    exact Prod.ext hy₁ hy₂

end Core

/-! ### The product atlas -/

variable {d₁ d₂ : ℤ}

/-- The **product** of implicit atlases `𝒜₁` of virtual dimension `d₁` on `X₁`, indexed by `A₁`,
and `𝒜₂` of virtual dimension `d₂` on `X₂`, indexed by `A₂`: an implicit atlas of virtual
dimension `d₁ + d₂` on `X₁ × X₂`, indexed by `A₁ ⊕ A₂` (Pardon, Definition 6.3.1). Its data and
all axioms but the local product models are `TauCeti.ImplicitAtlas.Core.prod`; the local product
model of the product is the product of the local product models of the factors. -/
noncomputable def prod (𝒜₁ : ImplicitAtlas Γ₁ E₁ ρ₁ T₁ act₁ X₁ d₁)
    (𝒜₂ : ImplicitAtlas Γ₂ E₂ ρ₂ T₂ act₂ X₂ d₂) :
    ImplicitAtlas (Sum.elim Γ₁ Γ₂) (Sum.elim E₁ E₂) (sumElimRep ρ₁ ρ₂)
      (fun I ↦ T₁ I.toLeft × T₂ I.toRight) (prodAct act₁ act₂) (X₁ × X₂) (d₁ + d₂) where
  toCore := 𝒜₁.toCore.prod 𝒜₂.toCore
  exists_openPartialHomeomorph I J h x hx := by
    have hx' := (𝒜₁.toCore.kuranishiZeroSet_prod 𝒜₂.toCore I J).subset x.property
    obtain ⟨n₁, hn₁, e₁, hxe₁, he₁⟩ :=
      𝒜₁.exists_openPartialHomeomorph (toLeft_subset_toLeft h) ⟨x.val.1, hx'.1⟩ hx.1
    obtain ⟨n₂, hn₂, e₂, hxe₂, he₂⟩ :=
      𝒜₂.exists_openPartialHomeomorph (toRight_subset_toRight h) ⟨x.val.2, hx'.2⟩ hx.2
    -- The model is `ℝ^(n₁) × E₁_(J₁ \ I₁) × ℝ^(n₂) × E₂_(J₂ \ I₂)`, regrouped as
    -- `ℝ^(n₁ + n₂) × E_(J \ I)` by `F`.
    let F : (EuclideanSpace ℝ (Fin n₁) × ∀ a : ↥(J.toLeft \ I.toLeft), E₁ a) ×
        EuclideanSpace ℝ (Fin n₂) × (∀ b : ↥(J.toRight \ I.toRight), E₂ b) ≃ₜ
        EuclideanSpace ℝ (Fin (n₁ + n₂)) × ∀ α : ↥(J \ I), Sum.elim E₁ E₂ α :=
      (Homeomorph.prodProdProdComm _ _ _ _).trans
        (EuclideanSpace.finAddEquivProd.symm.toHomeomorph.prodCongr
          (Homeomorph.piFinsetSum (Sum.elim E₁ E₂) (J \ I) (J.toLeft \ I.toLeft)
            (J.toRight \ I.toRight)).symm)
    -- The obstruction component of `F`: `Homeomorph.prodProdProdComm` exchanges the middle
    -- factors and `Homeomorph.prodCongr` acts factorwise. This is stated once here, with the
    -- pair typed as the domain of `Homeomorph.piFinsetSum`, because that domain mentions
    -- `Sum.elim E₁ E₂ (.inl a)` where `F` mentions `E₁ a`: the apply lemmas of the wrappers
    -- (`Homeomorph.coe_prodCongr`) do not rewrite inside `F` across this difference.
    have hF (p) : (F p).2 =
        (Homeomorph.piFinsetSum (Sum.elim E₁ E₂) (J \ I) (J.toLeft \ I.toLeft)
          (J.toRight \ I.toRight)).symm
          ((p.1.2, p.2.2) : (∀ a : ↥(J.toLeft \ I.toLeft), Sum.elim E₁ E₂ (.inl a)) ×
            ∀ b : ↥(J.toRight \ I.toRight), Sum.elim E₁ E₂ (.inr b)) :=
      (rfl)
    refine ⟨n₁ + n₂, ?_, (e₁.prod e₂).transHomeomorph F, ⟨hxe₁, hxe₂⟩, fun y hy ↦ ?_⟩
    · have hsum : ∑ α ∈ I, (Module.finrank ℝ (Sum.elim E₁ E₂ α) : ℤ) =
          ∑ a ∈ I.toLeft, (Module.finrank ℝ (E₁ a) : ℤ) +
            ∑ b ∈ I.toRight, (Module.finrank ℝ (E₂ b) : ℤ) :=
        Finset.sum_sum_eq_sum_toLeft_add_sum_toRight _ _
      rw [hsum]
      push_cast
      rw [hn₁, hn₂]
      ring
    · simp only [OpenPartialHomeomorph.transHomeomorph_apply, Function.comp_apply,
        OpenPartialHomeomorph.prod_apply, hF]
      refine funext fun ⟨α, hα⟩ ↦ ?_
      cases α with
      | inl a =>
        rw [Homeomorph.coe_piFinsetSum_symm, Equiv.piFinsetSum_symm_apply_inl]
        simp [he₁ y.1 hy.1, kuranishiSdiff_apply]
      | inr b =>
        rw [Homeomorph.coe_piFinsetSum_symm, Equiv.piFinsetSum_symm_apply_inr]
        simp [he₂ y.2 hy.2, kuranishiSdiff_apply]

@[simp]
theorem toCore_prod (𝒜₁ : ImplicitAtlas Γ₁ E₁ ρ₁ T₁ act₁ X₁ d₁)
    (𝒜₂ : ImplicitAtlas Γ₂ E₂ ρ₂ T₂ act₂ X₂ d₂) :
    (𝒜₁.prod 𝒜₂).toCore = 𝒜₁.toCore.prod 𝒜₂.toCore :=
  (rfl)

end TauCeti.ImplicitAtlas

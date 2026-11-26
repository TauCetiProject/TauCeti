/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Induced
import TauCeti.RepresentationTheory.FiniteIndex

/-!
# General facts about induced representations

Mathlib's `Rep.ind φ` induces a representation along an arbitrary homomorphism of groups
`φ : G →* H`, and `Rep.indMap φ` induces an intertwiner along it. This file collects the
general properties of that construction that Mathlib does not record and that the rest of
`TauCeti/RepresentationTheory/Induction/` needs, independently of any finiteness assumption
on the groups or on the representations.

## Main definitions

* `Representation.IndV.lift`: universe-polymorphic Frobenius reciprocity descent of a
  `G`-equivariant linear map `A →ₗ[k] B` to an `H`-equivariant linear map `IndV φ ρ →ₗ[k] B`.
* `Representation.IntertwiningMap.ind`: induction of an intertwining map along `φ`, the unbundled
  form of `Rep.indMap`.
* `Representation.Equiv.ind`: induction of an equivalence of representations along `φ`.

## Main statements

* `Rep.indMap_hom_mk`: an induced intertwiner acts on the coefficient of each generator.
* `Rep.indMap_add`: inducing an intertwiner along `φ` is additive, and `Rep.indFunctor_additive`:
  the same fact as a `CategoryTheory.Functor.Additive` instance for `Rep.indFunctor`.
* `Rep.indMap_smul` and `Rep.indFunctor_linear`: induction is linear over the coefficient ring.
* `Representation.IndV.mk_one_injective`: the generator map `a ↦ ⟦1 ⊗ a⟧` is injective for a
  subgroup.
* `Representation.ind_apply_map_mk_one`: on `IndV.mk φ ρ 1 a`, the induced action of `φ g`
  coincides with the original action of `g`.
* `Representation.IndV.lift_mk` and `Representation.IndV.lift_comp_ind`: evaluation on generators
  and `H`-equivariance of `Representation.IndV.lift`.
* `Representation.iSup_range_indV_mk_eq_top`: the images of the generator maps `a ↦ ⟦h ⊗ a⟧`
  span an induced representation.
* `Representation.indV_mk_apply_eq_ind`: the generator map at `h` turns the action of `g` on the
  coefficient into the induced action of `h⁻¹ φ(g) h`, and `Representation.indV_mk_comp_conjNormal`
  is the resulting `N`-equivariance for subgroups `N ≤ H` of `G` with `N` normal, twisted by
  conjugation `n ↦ s n s⁻¹`.
* `Rep.indMap_injective` and `Rep.indFunctor_faithful`: induction from a subgroup is faithful.
* `Representation.IntertwiningMap.ind_id`, `Representation.IntertwiningMap.ind_comp`: induction
  of intertwining maps is functorial.

## Implementation notes

As in `TauCeti/RepresentationTheory/Induction/Projection.lean`, the generator lemmas
`Representation.ind_apply_map_mk_one`, `Representation.indV_mk_apply_eq_ind`,
`Representation.IndV.lift_mk`, `Representation.IntertwiningMap.ind_mk`,
`Representation.Equiv.ind_mk`, and `Representation.Equiv.ind_symm_mk` are stated with the
reducible abbreviation `Representation.IndV.mk`, which `simp` unfolds, so they are not `simp`
lemmas and are applied by `rw`.
-/

public section

open CategoryTheory Representation

universe u v w w' t

namespace Rep

/-- An induced intertwiner applies the original intertwiner to each generator's coefficient. -/
@[simp↓]
theorem indMap_hom_mk {k : Type u} {G : Type v} {H : Type w}
    [CommRing k] [Group G] [Group H] (φ : G →* H)
    {A B : Rep.{w'} k G} (f : A ⟶ B) (h : H) (a : A) :
    (indMap φ f).hom (IndV.mk φ A.ρ h a) = IndV.mk φ B.ρ h (f.hom a) := by
  simp [indMap]

/-- Induction–restriction reciprocity evaluates a morphism on the tensor generator at `1`. -/
theorem indResHomEquiv_hom_apply {k : Type u} {G : Type v} {H : Type w}
    [CommRing k] [Group G] [Group H] (φ : G →* H)
    (A : Rep.{max t w u} k G) (B : Rep.{max t w u} k H)
    (f : ind φ A ⟶ B) (a : A) :
    (indResHomEquiv.{t, u, v, w} φ A B f).hom a = f.hom (IndV.mk φ A.ρ 1 a) :=
  rfl

/-- **Induction of intertwiners is additive**: for any homomorphism of groups `φ : G →* H`,
`Rep.indMap φ (f + g) = Rep.indMap φ f + Rep.indMap φ g`. -/
theorem indMap_add {k : Type u} {G : Type v} {H : Type w} [CommRing k] [Group G] [Group H]
    (φ : G →* H) {A B : Rep.{w'} k G} (f g : A ⟶ B) :
    indMap φ (f + g) = indMap φ f + indMap φ g := by
  ext h a
  simp [indMap, add_hom]

/-- **Induction along a homomorphism of groups is an additive functor**, the functorial form of
`Rep.indMap_add`. -/
instance indFunctor_additive {k : Type u} {G : Type v} {H : Type w} [CommRing k] [Group G]
    [Group H] (φ : G →* H) :
    ((indFunctor k φ : Rep.{w'} k G ⥤ Rep k H)).Additive where
  map_add {_ _} f g := indMap_add φ f g

/-- Inducing an intertwiner commutes with scalar multiplication. -/
@[simp]
theorem indMap_smul {k : Type u} {G : Type v} {H : Type w} [CommRing k] [Group G]
    [Group H] (φ : G →* H) {A B : Rep.{w'} k G} (r : k) (f : A ⟶ B) :
    indMap φ (r • f) = r • indMap φ f := by
  ext h a
  simp [indMap, smul_hom]

/-- Induction along a group homomorphism is linear over the coefficient ring. -/
instance indFunctor_linear {k : Type u} {G : Type v} {H : Type w} [CommRing k] [Group G]
    [Group H] (φ : G →* H) :
    Functor.Linear k (indFunctor k φ : Rep.{w'} k G ⥤ Rep k H) where
  map_smul f r := indMap_smul φ r f

end Rep

namespace Representation

/-- The generator map `a ↦ ⟦1 ⊗ a⟧` from a representation `A` of a subgroup `S` into the carrier
`(k[G] ⊗ A)_S` of its induced representation is injective. -/
theorem IndV.mk_one_injective {k : Type u} {G : Type v} [CommRing k] [Group G] (S : Subgroup G)
    {A : Type w} [AddCommGroup A] [Module k A] (ρ : Representation k S A) :
    Function.Injective (IndV.mk S.subtype ρ 1) := by
  classical
  -- Mathlib's induction-to-coinduction map, evaluated at `1`, is a left inverse.
  have key (x : A) : (Rep.indToCoind (Rep.of ρ) (IndV.mk S.subtype ρ 1 x)).val 1 = x :=
    congrFun (TauCeti.indToCoind_mk (A := Rep.of ρ) 1 x) 1 |>.trans
      (Rep.indToCoindAux_self (A := Rep.of ρ) 1 x)
  intro a b h
  rw [← key a, ← key b, h]

section Ind

variable {k G H A B : Type*} [CommRing k] [Group G] [Group H] (φ : G →* H)
  [AddCommGroup A] [Module k A] [AddCommGroup B] [Module k B]
  {ρ : Representation k G A} {σ : Representation k G B}

/-- On the canonical generator `IndV.mk φ ρ 1 a`, the induced action of `φ g` coincides with the
original action of `g`. -/
theorem ind_apply_map_mk_one (ρ : Representation k G A) (g : G) (a : A) :
    ind φ ρ (φ g) (IndV.mk φ ρ 1 a) = IndV.mk φ ρ 1 (ρ g a) := by
  simp [← Coinvariants.mk_inv_tmul, ofMulAction_single]

/-- **Universal property (Frobenius reciprocity) of `Representation.IndV`.** Any `G`-equivariant
`k`-linear map `f : A →ₗ[k] B` into an `H`-representation `(B, τ)` (restricted along `φ`) descends
to an `H`-equivariant `k`-linear map `IndV φ ρ →ₗ[k] B` sending `IndV.mk φ ρ h a` to `τ h⁻¹ (f a)`.
Unlike `Rep.indResHomEquiv`, the coefficient ring `k`, groups `G`, `H`, and module carriers `A`,
`B` may lie in independent universes. -/
noncomputable def IndV.lift {τ : Representation k H B} (f : A →ₗ[k] B)
    (hf : ∀ g : G, f ∘ₗ ρ g = τ (φ g) ∘ₗ f) : IndV φ ρ →ₗ[k] B :=
  Coinvariants.lift _
    (TensorProduct.lift <| (Finsupp.lift _ _ _ fun h ↦ τ h⁻¹ ∘ₗ f) ∘ₗ
      (MonoidAlgebra.coeffLinearEquiv k).toLinearMap)
    fun g ↦ by
      ext h x
      simp only [LinearMap.coe_comp, Function.comp_apply, MonoidAlgebra.lsingle_apply]
      have hgx : f (ρ g x) = τ (φ g) (f x) := LinearMap.congr_fun (hf g) x
      simp [ofMulAction_single, mul_inv_rev, hgx]

/-- Evaluating `Representation.IndV.lift` on a generator `IndV.mk φ ρ h a` yields `τ h⁻¹ (f a)`. -/
theorem IndV.lift_mk {τ : Representation k H B} (f : A →ₗ[k] B)
    (hf : ∀ g : G, f ∘ₗ ρ g = τ (φ g) ∘ₗ f) (h : H) (a : A) :
    IndV.lift φ f hf (IndV.mk φ ρ h a) = τ h⁻¹ (f a) := by
  simp [IndV.lift]

/-- `Representation.IndV.lift` intertwines the induced representation `Representation.ind φ ρ`
with `τ`. -/
theorem IndV.lift_comp_ind {τ : Representation k H B} (f : A →ₗ[k] B)
    (hf : ∀ g : G, f ∘ₗ ρ g = τ (φ g) ∘ₗ f) (h : H) :
    IndV.lift φ f hf ∘ₗ ind φ ρ h = τ h ∘ₗ IndV.lift φ f hf := by
  refine IndV.hom_ext φ ρ fun h' ↦ LinearMap.ext fun a ↦ ?_
  simp [IndV.lift]

namespace IntertwiningMap

/-- **Induction of an intertwining map** along `φ : G →* H`: the map `⟦h ⊗ₜ a⟧ ↦ ⟦h ⊗ₜ f a⟧`.
This is the unbundled form of `Rep.indMap`. -/
noncomputable def ind (f : IntertwiningMap ρ σ) :
    IntertwiningMap (Representation.ind φ ρ) (Representation.ind φ σ) where
  toLinearMap := Coinvariants.map _ _ ⟨f.toLinearMap.lTensor _, by
    simp [LinearMap.lTensor_comp_map, f.isIntertwining', LinearMap.map_comp_lTensor]⟩
  isIntertwining' _ := by ext; simp

theorem ind_mk (f : IntertwiningMap ρ σ) (h : H) (a : A) :
    f.ind φ (IndV.mk φ ρ h a) = IndV.mk φ σ h (f a) :=
  (rfl)

@[simp]
theorem ind_id : (IntertwiningMap.id ρ).ind φ = IntertwiningMap.id (Representation.ind φ ρ) :=
  IntertwiningMap.ext <| IndV.hom_ext φ _ fun _ => rfl

theorem ind_comp {C : Type*} [AddCommGroup C] [Module k C] {τ : Representation k G C}
    (f : IntertwiningMap σ τ) (g : IntertwiningMap ρ σ) :
    (f.comp g).ind φ = (f.ind φ).comp (g.ind φ) :=
  IntertwiningMap.ext <| IndV.hom_ext φ _ fun _ => rfl

end IntertwiningMap

namespace Equiv

/-- **Induction of an equivalence of representations** along `φ : G →* H`: the equivalence
`⟦h ⊗ₜ a⟧ ↦ ⟦h ⊗ₜ e a⟧`, with inverse induced by `e.symm`. -/
noncomputable def ind (e : Equiv ρ σ) : Equiv (Representation.ind φ ρ) (Representation.ind φ σ) :=
  .mk (LinearEquiv.ofLinearMap (e.toIntertwiningMap.ind φ).toLinearMap
      (e.symm.toIntertwiningMap.ind φ).toLinearMap
      (by ext; simp [IntertwiningMap.ind])
      (by ext; simp [IntertwiningMap.ind]))
    (e.toIntertwiningMap.ind φ).isIntertwining'

theorem ind_mk (e : Equiv ρ σ) (h : H) (a : A) :
    e.ind φ (IndV.mk φ ρ h a) = IndV.mk φ σ h (e a) :=
  (rfl)

theorem ind_symm_mk (e : Equiv ρ σ) (h : H) (b : B) :
    (e.ind φ).symm (IndV.mk φ σ h b) = IndV.mk φ ρ h (e.symm b) :=
  (rfl)

end Equiv

end Ind

section Generators

variable {k G G' U : Type*} [CommRing k] [Group G] [Group G'] [AddCommGroup U] [Module k U]

/-- The images of the generator maps `a ↦ ⟦s ⊗ a⟧`, for `s` ranging over the target group, span an
induced representation. -/
theorem iSup_range_indV_mk_eq_top (φ : G' →* G) (ρ : Representation k G' U) :
    ⨆ s : G, LinearMap.range (IndV.mk φ ρ s) = ⊤ := by
  set P := ⨆ s : G, LinearMap.range (IndV.mk φ ρ s)
  have h : P.mkQ = 0 := IndV.hom_ext _ _ fun s ↦ LinearMap.ext fun a ↦ by
    simpa using (le_iSup (fun s : G ↦ LinearMap.range (IndV.mk φ ρ s)) s)
      (LinearMap.mem_range_self _ a)
  rw [← Submodule.ker_mkQ P, h, LinearMap.ker_zero]

/-- The generator map at `s` turns the action of `h` on the coefficient into the induced action of
the conjugate `s⁻¹ φ(h) s`: `⟦s ⊗ h a⟧ = (s⁻¹ φ(h) s) ⟦s ⊗ a⟧`. -/
theorem indV_mk_apply_eq_ind (φ : G' →* G) (ρ : Representation k G' U) (h : G') (s : G)
    (a : U) : IndV.mk φ ρ s (ρ h a) = ind φ ρ (s⁻¹ * φ h * s) (IndV.mk φ ρ s a) := by
  rw [ind_mk]
  simpa [ofMulAction_single, mul_assoc] using Coinvariants.mk_tmul_inv
    (ρ := (leftRegular k G).comp φ) (τ := ρ) (MonoidAlgebra.single s (1 : k)) a h⁻¹

variable {H N : Subgroup G} [N.Normal]

/-- For `s ∈ G` and a representation `ρ` of `H ≥ N`, the generator map `a ↦ ⟦s ⊗ a⟧` into
`Ind_H^G ρ` is `N`-equivariant from `ρ` restricted along `n ↦ s n s⁻¹ : N → H`. -/
theorem indV_mk_comp_conjNormal (ρ : Representation k H U) (hNH : N ≤ H) (s : G) (n : N) :
    IndV.mk H.subtype ρ s ∘ₗ
        ρ ((Subgroup.inclusion hNH).comp (MulAut.conjNormal s).toMonoidHom n) =
      ind H.subtype ρ (n : G) ∘ₗ IndV.mk H.subtype ρ s := by
  refine LinearMap.ext fun a ↦ ?_
  rw [LinearMap.comp_apply, indV_mk_apply_eq_ind, LinearMap.comp_apply]
  simp [MulAut.conjNormal_apply, mul_assoc]

end Generators

end Representation

namespace Rep

/-- Induction from a subgroup is injective on intertwining spaces. -/
theorem indMap_injective {k : Type u} {G : Type v} [CommRing k] [Group G] {S : Subgroup G}
    {V W : Rep.{w'} k S} : Function.Injective (indMap S.subtype : (V ⟶ W) → _) := by
  intro f g h
  apply hom_ext
  ext x
  apply IndV.mk_one_injective S W.ρ
  simpa using congrArg (fun m : ind S.subtype V ⟶ ind S.subtype W ↦
    m.hom (IndV.mk S.subtype V.ρ 1 x)) h

/-- Induction from a subgroup is a faithful functor, the functorial form of
`Rep.indMap_injective`. -/
instance indFunctor_faithful {k : Type u} {G : Type v} [CommRing k] [Group G] (S : Subgroup G) :
    (indFunctor k S.subtype : Rep.{w'} k S ⥤ Rep k G).Faithful where
  map_injective h := indMap_injective h

end Rep

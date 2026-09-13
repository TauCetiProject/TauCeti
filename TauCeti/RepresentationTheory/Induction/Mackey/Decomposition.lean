/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DirectSum.Module
public import TauCeti.RepresentationTheory.Induction.Mackey.Basic
public import TauCeti.RepresentationTheory.Induction.Transitivity

/-!
# The Mackey decomposition as an isomorphism of representations

Let `H` and `K` be subgroups of a group `G` and let `A` be a representation of `H` over a
commutative ring `k`.  Restricting the induced representation `Ind_H^G A` to `K` splits it as a
direct sum over the double cosets `K \ G / H`:

`Res_K (Ind_H^G A) ≅ ⨁_{KsH ∈ K \ G / H} Ind_{K ⊓ sHs⁻¹}^K (Res ({}^s A))`,

where `s` is the chosen representative `Quotient.out` of each double coset.  This file proves
that decomposition as a natural isomorphism in `Rep k K`, refining the character form
`TauCeti.character_resFDRep_indFDRep_mackey`.  No finiteness is assumed: Mathlib's induced
representation is compactly supported, so the decomposition holds for arbitrary `G`, `H` and `K`.

The summands are `Rep.mackeySummand`, which are Mathlib's `Rep.ind` of the restriction of
`A` along `TauCeti.mackeyToH : K ⊓ sHs⁻¹ → H, y ↦ s⁻¹ y s`; as for the finite-dimensional
`TauCeti.mackeySummand`, this is the restriction of the conjugate representation `{}^s A` to the
Mackey subgroup (`Rep.mackeySummand_eq_ind_res_conjRep`).

In Mathlib's convention `Ind_H^G A` is the space of coinvariants `(k[G] ⊗ A)_H`, with
`⟦h g ⊗ₜ h a⟧ = ⟦g ⊗ₜ a⟧` for `h ∈ H`, and `x ∈ G` acts by `⟦g ⊗ₜ a⟧ ↦ ⟦g x⁻¹ ⊗ₜ a⟧`.  The summand
of the representative `s` embeds by `⟦u ⊗ₜ a⟧ ↦ ⟦s⁻¹ u ⊗ₜ a⟧` (`Rep.mackeyInclusion`),
and these embeddings assemble to the inverse of the decomposition.  The forward map sends
`⟦h s⁻¹ u ⊗ₜ a⟧` to `⟦u ⊗ₜ h⁻¹ a⟧` in the summand of `KsH`; every element of `G` can be written as
`h s⁻¹ u` because `g⁻¹` lies in the double coset `K s H` of its representative, and the value does
not depend on the chosen factorization because two of them differ by an element of the Mackey
subgroup.

The double coset quotient carries no canonical decidable equality, so the direct-sum inclusions
`DirectSum.lof` appearing below use the classical one; it is the only choice available and
`DecidableEq` is a subsingleton, so nothing in the statements depends on it.

## Main definitions

* `Rep.mackeySummand`: the summand `Ind_{K ⊓ sHs⁻¹}^K (Res ({}^s A))` in `Rep k K`.
* `Rep.mackeyInclusion`: its embedding into `Res_K (Ind_H^G A)`.
* `Rep.mackeyDirectSum`: the direct sum of the summands over `K \ G / H`, and
  `Rep.mackeySummandFunctor`, `Rep.mackeyDirectSumFunctor`, the same
  constructions as functors of `A`.
* `Rep.mackeyDecomposition`: **the Mackey decomposition**
  `Res_K (Ind_H^G A) ≅ ⨁_{KsH} Ind_{K ⊓ sHs⁻¹}^K (Res ({}^s A))`.
* `Rep.mackeyDecompositionNatIso`: the decomposition as a natural isomorphism of functors
  `Rep k H ⥤ Rep k K`.

## Main statements

* `Rep.mackeySummand_eq_ind_res_conjRep`: the summand is induced from the restriction of
  the conjugate representation `{}^s A`.
* `Rep.mackeyDecomposition_hom_hom_apply_mk` and
  `Rep.mackeyDecomposition_inv_hom_apply_lof`: the two directions of the decomposition on
  generators.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, Section 7.3.
* C. W. Curtis, I. Reiner, *Methods of Representation Theory, Vol. I*, Section 10.
-/

public section

open CategoryTheory DirectSum Representation
open scoped Pointwise

namespace Rep

universe u

variable {k G : Type u} [CommRing k] [Group G] {H K : Subgroup G}

/-- A double coset quotient carries no canonical decidable equality; `DirectSum.lof` and
`DirectSum.linearMap_ext` need one, so the classical instance is used throughout this file. -/
noncomputable local instance decidableEqDoubleCosetQuotient :
    DecidableEq (DoubleCoset.Quotient (K : Set G) (H : Set G)) :=
  Classical.decEq _

section Summand

variable (H K) in
/-- **The Mackey summand** attached to `s : G`, as a representation of `K`: the representation
`A` of `H`, pulled back to the Mackey subgroup `K ⊓ sHs⁻¹` along `y ↦ s⁻¹ y s`, and induced up to
`K`.  This is `Ind_{K ⊓ sHs⁻¹}^K (Res ({}^s A))`
(`Rep.mackeySummand_eq_ind_res_conjRep`); `TauCeti.mackeySummand` is its
finite-dimensional counterpart. -/
noncomputable abbrev mackeySummand (s : G) (A : Rep.{u} k H) : Rep.{u} k K :=
  Rep.ind ((TauCeti.mackeySubgroup s H K).subgroupOf K).subtype
    (Rep.res (TauCeti.mackeyToH s H K) A)

/-- The Mackey summand is the conjugate representation `{}^s A`, restricted along the inclusion
of the Mackey subgroup into `sHs⁻¹` and induced up to `K`.  The remaining restriction is along the
identification of `K ⊓ sHs⁻¹` with its copy inside `K`. -/
theorem mackeySummand_eq_ind_res_conjRep (s : G) (A : Rep.{u} k H) :
    mackeySummand H K s A =
      Rep.ind ((TauCeti.mackeySubgroup s H K).subgroupOf K).subtype
        (Rep.res (Subgroup.subgroupOfEquivOfLe
            (TauCeti.mackeySubgroup_le_right (s := s) (H := H) (K := K))).toMonoidHom
          (Rep.res (TauCeti.mackeyToConjH s H K) (TauCeti.conjRep s A))) := by
  have e : TauCeti.mackeyToH s H K =
      ((TauCeti.conjSubgroupEquiv s H).toMonoidHom.comp (TauCeti.mackeyToConjH s H K)).comp
        (Subgroup.subgroupOfEquivOfLe TauCeti.mackeySubgroup_le_right).toMonoidHom :=
    MonoidHom.ext fun y => Subtype.ext (by simp)
  rw [← TauCeti.res_obj_eq_conjRep, mackeySummand, e]
  rfl

variable (K) in
/-- The embedding of the Mackey summand at `s` into `Res_K (Ind_H^G A)`,
`⟦u ⊗ₜ a⟧ ↦ ⟦s⁻¹ u ⊗ₜ a⟧` (`Rep.mackeyInclusion_hom_apply_mk`).  It is the morphism
corresponding under the induction--restriction adjunction to `a ↦ ⟦s⁻¹ ⊗ₜ a⟧`. -/
noncomputable def mackeyInclusion (s : G) (A : Rep.{u} k H) :
    mackeySummand H K s A ⟶ Rep.res K.subtype (Rep.ind H.subtype A) :=
  (Rep.indResHomEquiv _ _ _).symm <| Rep.ofHom
    ⟨IndV.mk H.subtype A.ρ s⁻¹, fun m => LinearMap.ext fun a => by
      have h := TauCeti.indV_mk_apply_inv H.subtype A.ρ (TauCeti.mackeyToH s H K m)⁻¹ s⁻¹ a
      rw [inv_inv] at h
      -- The two sides are the restricted actions on `mackeySummand` and on `Rep.res K.subtype`,
      -- both of which are `Representation.ind` by definition of `Rep.res` and `Rep.ind`; `rw`
      -- cannot reach inside those sealed wrappers, so the goal is restated definitionally.
      change IndV.mk H.subtype A.ρ s⁻¹ (A.ρ (TauCeti.mackeyToH s H K m) a) =
        Representation.ind H.subtype A.ρ ((m : K) : G) (IndV.mk H.subtype A.ρ s⁻¹ a)
      rw [Representation.ind_mk, h]
      congr 1
      simp only [Subgroup.coe_subtype, InvMemClass.coe_inv, TauCeti.coe_mackeyToH_apply]
      group⟩

/-- The embedding of the Mackey summand on generators: `⟦u ⊗ₜ a⟧ ↦ ⟦s⁻¹ u ⊗ₜ a⟧`. -/
theorem mackeyInclusion_hom_apply_mk (s : G) (A : Rep.{u} k H) (u : K) (a : A) :
    (mackeyInclusion K s A).hom (IndV.mk _ _ u a) = IndV.mk H.subtype A.ρ (s⁻¹ * u) a := by
  simp [mackeyInclusion]

variable (H K) in
/-- The direct sum of the Mackey summands over the double cosets `K \ G / H`, each built from the
chosen representative `Quotient.out`. -/
noncomputable abbrev mackeyDirectSum (A : Rep.{u} k H) : Rep.{u} k K :=
  Rep.of (directSum fun D : DoubleCoset.Quotient (K : Set G) (H : Set G) =>
    (mackeySummand H K D.out A).ρ)

variable (H K) in
/-- The Mackey summand at `s` as a functor of the representation of `H`: restriction along
`TauCeti.mackeyToH` followed by induction up to `K`. -/
noncomputable abbrev mackeySummandFunctor (s : G) : Rep.{u} k H ⥤ Rep.{u} k K :=
  Rep.resFunctor (TauCeti.mackeyToH s H K) ⋙
    Rep.indFunctor k ((TauCeti.mackeySubgroup s H K).subgroupOf K).subtype

variable (H K) in
/-- The direct sum of the Mackey summands, as a functor of the representation of `H`: on
morphisms it applies `Rep.mackeySummandFunctor` in each summand
(`Rep.mackeyDirectSumFunctor_map_hom_lof`).  The body is exposed because the type
`(mackeyDirectSumFunctor H K).obj A` is otherwise opaque, so no lemma about the functor could even
be stated. -/
@[expose]
noncomputable def mackeyDirectSumFunctor : Rep.{u} k H ⥤ Rep.{u} k K where
  obj A := mackeyDirectSum H K A
  map f := Rep.ofHom ⟨DirectSum.lmap fun D =>
      ((mackeySummandFunctor H K D.out).map f).hom.toLinearMap,
    fun x => by
      refine DirectSum.linearMap_ext k fun D => LinearMap.ext fun y => ?_
      simp only [LinearMap.coe_comp, Function.comp_apply, directSum_apply, DirectSum.lmap_lof]
      exact congrArg (DirectSum.lof k _ _ D) (Rep.hom_comm_apply _ x y)⟩
  map_id A := by
    have h (s : G) :
        ((mackeySummandFunctor H K s).map (𝟙 A)).hom.toLinearMap = LinearMap.id := by
      rw [CategoryTheory.Functor.map_id]
      rfl
    refine Rep.hom_ext (IntertwiningMap.ext ?_)
    -- The `map` field above is being defined, so no `_map` lemma exists yet; unfold the `Rep.ofHom`
    -- and `IntertwiningMap` wrappers around it definitionally to expose the `DirectSum.lmap`.
    change DirectSum.lmap _ = LinearMap.id
    -- Compare summand by summand; `h` is stated for an arbitrary `s` rather than for `D.out`, since
    -- rewriting inside a term whose type mentions `D.out` fails.
    refine DirectSum.linearMap_ext k fun D => LinearMap.ext fun y => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, DirectSum.lmap_lof, LinearMap.id_apply]
    exact congrArg (DirectSum.lof k _ _ D) (LinearMap.congr_fun (h D.out) y)
  map_comp {A B C} f g := by
    have h (s : G) :
        ((mackeySummandFunctor H K s).map (f ≫ g)).hom.toLinearMap =
          ((mackeySummandFunctor H K s).map g).hom.toLinearMap ∘ₗ
            ((mackeySummandFunctor H K s).map f).hom.toLinearMap := by
      rw [CategoryTheory.Functor.map_comp]
      rfl
    refine Rep.hom_ext (IntertwiningMap.ext ?_)
    -- As for `map_id`: the `map` field is under definition, so the `Rep.ofHom` and
    -- `IntertwiningMap` wrappers can only be removed definitionally.
    change DirectSum.lmap _ = DirectSum.lmap _ ∘ₗ DirectSum.lmap _
    refine DirectSum.linearMap_ext k fun D => LinearMap.ext fun y => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, DirectSum.lmap_lof]
    exact congrArg (DirectSum.lof k _ _ D) (LinearMap.congr_fun (h D.out) y)

/-- The direct sum of the Mackey summands acts summandwise on morphisms: on the generator
`⟦u ⊗ₜ a⟧` of the summand of `D` it is `⟦u ⊗ₜ f a⟧` in the summand of `D`. -/
theorem mackeyDirectSumFunctor_map_hom_lof {A B : Rep.{u} k H} (f : A ⟶ B)
    (D : DoubleCoset.Quotient (K : Set G) (H : Set G)) (u : K) (a : A) :
    ((mackeyDirectSumFunctor H K).map f).hom
        (DirectSum.lof k (DoubleCoset.Quotient (K : Set G) (H : Set G))
          (fun D => (mackeySummand H K D.out A : Type u)) D
          (IndV.mk _ (A.ρ.comp (TauCeti.mackeyToH D.out H K)) u a)) =
      DirectSum.lof k (DoubleCoset.Quotient (K : Set G) (H : Set G))
        (fun D => (mackeySummand H K D.out B : Type u)) D
        (IndV.mk _ (B.ρ.comp (TauCeti.mackeyToH D.out H K)) u (f.hom a)) := by
  exact (DirectSum.lmap_lof _ _ _).trans rfl

end Summand

section Decomposition

/-- Every `g : G` factors as `h s⁻¹ u` with `h ∈ H`, `u ∈ K`, and `s` the chosen representative of
the double coset `K g⁻¹ H`. -/
private theorem exists_eq_mul_out_inv_mul (g : G) :
    ∃ h : H, ∃ u : K, g = h * ((DoubleCoset.mk K H g⁻¹).out)⁻¹ * u := by
  obtain ⟨u, hu, h, hh, e⟩ :=
    DoubleCoset.eq.mp (DoubleCoset.out_eq' (DoubleCoset.mk K H g⁻¹))
  refine ⟨⟨h, hh⟩⁻¹, ⟨u, hu⟩⁻¹, ?_⟩
  generalize (DoubleCoset.mk K H g⁻¹).out = s at e ⊢
  rw [← inv_inv g, e]
  simp only [InvMemClass.coe_inv]
  group

variable (A : Rep.{u} k H)

/-- The component in the summand of `D` of an element `g = h s⁻¹ u` (with `s = D.out`), as a
linear map `a ↦ ⟦u ⊗ₜ h⁻¹ a⟧`, computed from a chosen factorization. -/
private noncomputable def mackeyComponent (D : DoubleCoset.Quotient (K : Set G) (H : Set G))
    (g : G) (hg : ∃ h : H, ∃ u : K, g = h * D.out⁻¹ * u) :
    A →ₗ[k] mackeySummand H K D.out A :=
  IndV.mk _ _ hg.choose_spec.choose ∘ₗ A.ρ hg.choose⁻¹

/-- The component does not depend on the chosen factorization `g = h s⁻¹ u`: two factorizations
differ by an element of the Mackey subgroup, which the coinvariants relation absorbs. -/
private theorem mackeyComponent_eq (D : DoubleCoset.Quotient (K : Set G) (H : Set G))
    (g : G) (hg : ∃ h : H, ∃ u : K, g = h * D.out⁻¹ * u) (h : H) (u : K)
    (e : g = h * D.out⁻¹ * u) (a : A) :
    mackeyComponent A D g hg a =
      IndV.mk _ (A.ρ.comp (TauCeti.mackeyToH D.out H K)) u (A.ρ h⁻¹ a) := by
  set h' := hg.choose
  set u' := hg.choose_spec.choose
  have e' : g = h' * D.out⁻¹ * u' := hg.choose_spec.choose_spec
  have hconj : (h' : G)⁻¹ * h = D.out⁻¹ * ((u' : G) * (u : G)⁻¹) * D.out := by
    have e'' : (h : G) * D.out⁻¹ * u = h' * D.out⁻¹ * u' := e.symm.trans e'
    calc (h' : G)⁻¹ * h = (h' : G)⁻¹ * (h * D.out⁻¹ * u) * (u : G)⁻¹ * D.out := by group
      _ = (h' : G)⁻¹ * (h' * D.out⁻¹ * u') * (u : G)⁻¹ * D.out := by rw [e'']
      _ = _ := by group
  have hm : u' * u⁻¹ ∈ (TauCeti.mackeySubgroup D.out H K).subgroupOf K := by
    rw [Subgroup.mem_subgroupOf, TauCeti.mem_mackeySubgroup_iff, Subgroup.coe_mul,
      InvMemClass.coe_inv]
    exact ⟨K.mul_mem u'.2 (K.inv_mem u.2), hconj ▸ H.mul_mem (H.inv_mem h'.2) h.2⟩
  have key := TauCeti.indV_mk_apply_inv
    ((TauCeti.mackeySubgroup D.out H K).subgroupOf K).subtype
    (A.ρ.comp (TauCeti.mackeyToH D.out H K)) ⟨_, hm⟩ u (A.ρ h'⁻¹ a)
  have hu : ((TauCeti.mackeySubgroup D.out H K).subgroupOf K).subtype ⟨_, hm⟩ * u = u' := by
    simp
  have hH : TauCeti.mackeyToH D.out H K ⟨_, hm⟩⁻¹ * h'⁻¹ = h⁻¹ := by
    ext
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv, map_inv, TauCeti.coe_mackeyToH_apply]
    rw [← hconj]
    group
  rw [hu] at key
  simp only [MonoidHom.coe_comp, Function.comp_apply, ← Module.End.mul_apply, ← map_mul,
    hH] at key
  rw [key]
  rfl

/-- The forward map of the Mackey decomposition on the generators `⟦g ⊗ₜ a⟧`, as a family of
linear maps indexed by `g`. -/
private noncomputable def mackeyDecompAux (g : G) :
    A →ₗ[k] mackeyDirectSum H K A :=
  (DirectSum.lof k (DoubleCoset.Quotient (K : Set G) (H : Set G))
    (fun D => (mackeySummand H K D.out A : Type u)) (DoubleCoset.mk K H g⁻¹)).comp
    (mackeyComponent A (DoubleCoset.mk K H g⁻¹) g (exists_eq_mul_out_inv_mul g))

private theorem mackeyDecompAux_eq (D : DoubleCoset.Quotient (K : Set G) (H : Set G))
    (h : H) (u : K) (a : A) :
    mackeyDecompAux A ((h : G) * D.out⁻¹ * u) a =
      DirectSum.lof k (DoubleCoset.Quotient (K : Set G) (H : Set G))
        (fun D => (mackeySummand H K D.out A : Type u)) D
        (IndV.mk _ (A.ρ.comp (TauCeti.mackeyToH D.out H K)) u (A.ρ h⁻¹ a)) := by
  have hD : DoubleCoset.mk K H ((h : G) * D.out⁻¹ * u)⁻¹ = D :=
    ((DoubleCoset.eq.mpr ⟨(u : G)⁻¹, K.inv_mem u.2, (h : G)⁻¹, H.inv_mem h.2, by group⟩).symm).trans
      (DoubleCoset.out_eq' D)
  -- Generalize the double coset of `g⁻¹` so that it can be identified with `D`.
  have key : ∀ (D' : DoubleCoset.Quotient (K : Set G) (H : Set G)) (_ : D' = D)
      (hg : ∃ h' : H, ∃ u' : K, (h : G) * D.out⁻¹ * u = h' * D'.out⁻¹ * u'),
      DirectSum.lof k (DoubleCoset.Quotient (K : Set G) (H : Set G))
          (fun D => (mackeySummand H K D.out A : Type u)) D'
          (mackeyComponent A D' _ hg a) =
        DirectSum.lof k (DoubleCoset.Quotient (K : Set G) (H : Set G))
          (fun D => (mackeySummand H K D.out A : Type u)) D
          (IndV.mk _ (A.ρ.comp (TauCeti.mackeyToH D.out H K)) u (A.ρ h⁻¹ a)) := by
    rintro _ rfl hg
    rw [mackeyComponent_eq A _ _ hg h u rfl]
  exact key _ hD _

private theorem mackeyDecompAux_mul (h₀ : H) (g : G) (a : A) :
    mackeyDecompAux (K := K) A (h₀ * g) (A.ρ h₀ a) = mackeyDecompAux (K := K) A g a := by
  obtain ⟨h, u, e⟩ := exists_eq_mul_out_inv_mul (H := H) (K := K) g
  generalize DoubleCoset.mk K H g⁻¹ = D at e
  subst e
  rw [← mul_assoc, ← mul_assoc, ← Subgroup.coe_mul, mackeyDecompAux_eq, mackeyDecompAux_eq,
    ← Module.End.mul_apply, ← map_mul, mul_inv_rev, inv_mul_cancel_right]

/-- Evaluating the linear map out of `k[G] ⊗ A` assembled from a family `f : G → (A →ₗ[k] W)`. The
codomain is generic, so that rewriting does not have to see through `DoubleCoset.Quotient`. -/
private theorem lift_single_tmul {W : Type*} [AddCommGroup W] [Module k W] (f : G → A →ₗ[k] W)
    (g : G) (a : A) :
    TensorProduct.lift ((Finsupp.lift _ k G f) ∘ₗ (MonoidAlgebra.coeffLinearEquiv k).toLinearMap)
      (MonoidAlgebra.single g 1 ⊗ₜ a) = f g a := by
  simp

/-- The forward map of the Mackey decomposition, as a linear map. -/
private noncomputable def indToMackeySum :
    IndV H.subtype A.ρ →ₗ[k] mackeyDirectSum H K A :=
  Coinvariants.lift _ (TensorProduct.lift <|
    (Finsupp.lift _ k G fun g => mackeyDecompAux A g) ∘ₗ
      (MonoidAlgebra.coeffLinearEquiv k).toLinearMap) fun h₀ => by
    refine TensorProduct.ext (MonoidAlgebra.lhom_ext' fun g =>
      LinearMap.ext_ring (LinearMap.ext fun a => ?_))
    simp only [LinearMap.compr₂ₛₗ_apply, LinearMap.comp_apply, TensorProduct.mk_apply,
      MonoidAlgebra.lsingle_apply, tprod_apply, TensorProduct.map_tmul, MonoidHom.comp_apply,
      ofMulAction_single]
    rw [lift_single_tmul, lift_single_tmul]
    exact mackeyDecompAux_mul A h₀ g a

private theorem indToMackeySum_mk (g : G) (a : A) :
    indToMackeySum (K := K) A (IndV.mk _ _ g a) = mackeyDecompAux A g a :=
  lift_single_tmul A _ g a

/-- The inverse map of the Mackey decomposition, as a linear map. -/
private noncomputable def mackeySumToInd : mackeyDirectSum H K A →ₗ[k] IndV H.subtype A.ρ :=
  DirectSum.toModule k _ _ fun D => (mackeyInclusion K D.out A).hom.toLinearMap

private theorem mackeySumToInd_lof (D : DoubleCoset.Quotient (K : Set G) (H : Set G)) (u : K)
    (a : A) :
    mackeySumToInd A (DirectSum.lof k (DoubleCoset.Quotient (K : Set G) (H : Set G))
        (fun D => (mackeySummand H K D.out A : Type u)) D
        (IndV.mk _ (A.ρ.comp (TauCeti.mackeyToH D.out H K)) u a)) =
      IndV.mk H.subtype A.ρ (D.out⁻¹ * u) a := by
  rw [mackeySumToInd, DirectSum.toModule_lof]
  exact mackeyInclusion_hom_apply_mk _ _ _ _

private theorem mackeySumToInd_comp_ρ (x : K) :
    mackeySumToInd A ∘ₗ (mackeyDirectSum H K A).ρ x =
      (Rep.res K.subtype (Rep.ind H.subtype A)).ρ x ∘ₗ mackeySumToInd A := by
  refine DirectSum.linearMap_ext k fun D => LinearMap.ext fun y => ?_
  simp only [LinearMap.coe_comp, Function.comp_apply, directSum_apply,
    DirectSum.lmap_lof, mackeySumToInd, DirectSum.toModule_lof]
  exact Rep.hom_comm_apply (mackeyInclusion K D.out A) x y

private theorem indToMackeySum_comp_mackeySumToInd :
    indToMackeySum (K := K) A ∘ₗ mackeySumToInd A = LinearMap.id := by
  refine DirectSum.linearMap_ext k fun D => IndV.hom_ext _ _ fun u => LinearMap.ext fun a => ?_
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_comp]
  have e : (D.out⁻¹ * u : G) = ((1 : H) : G) * D.out⁻¹ * u := by simp
  -- `rw` cannot abstract terms whose type mentions `D.out`, so the steps are chained by hand.
  exact (congrArg (indToMackeySum A) ((mackeySumToInd_lof A D u a).trans
    (congrArg (fun x => IndV.mk H.subtype A.ρ x a) e))).trans
    ((indToMackeySum_mk A _ a).trans ((mackeyDecompAux_eq A D 1 u a).trans
      (by rw [inv_one, map_one, Module.End.one_apply]; rfl)))

private theorem mackeySumToInd_comp_indToMackeySum :
    mackeySumToInd A ∘ₗ indToMackeySum (K := K) A = LinearMap.id := by
  refine IndV.hom_ext _ _ fun g => LinearMap.ext fun a => ?_
  obtain ⟨h, u, e⟩ := exists_eq_mul_out_inv_mul (H := H) (K := K) g
  generalize DoubleCoset.mk K H g⁻¹ = D at e
  subst e
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_comp]
  -- `rw` cannot abstract terms whose type mentions `D.out`, so the steps are chained by hand.
  exact (congrArg (mackeySumToInd A)
    ((indToMackeySum_mk A _ a).trans (mackeyDecompAux_eq A D h u a))).trans
    ((mackeySumToInd_lof A D u _).trans ((TauCeti.indV_mk_apply_inv H.subtype A.ρ h _ a).trans
      (congrArg (fun x => IndV.mk H.subtype A.ρ x a) (mul_assoc _ _ _).symm)))

/-- **The Mackey decomposition formula.**  For subgroups `H` and `K` of `G` and a representation
`A` of `H`, restricting the induced representation `Ind_H^G A` to `K` gives the direct sum, over
the double cosets `K \ G / H`, of the Mackey summands
`Ind_{K ⊓ sHs⁻¹}^K (Res ({}^s A))` at the chosen representatives `s`.

On generators, `⟦h s⁻¹ u ⊗ₜ a⟧ ↦ ⟦u ⊗ₜ h⁻¹ a⟧` in the summand of `KsH`
(`Rep.mackeyDecomposition_hom_hom_apply_mk`), and backwards `⟦u ⊗ₜ a⟧ ↦ ⟦s⁻¹ u ⊗ₜ a⟧`
(`Rep.mackeyDecomposition_inv_hom_apply_lof`).  It is natural in `A`
(`Rep.mackeyDecompositionNatIso`). -/
noncomputable def mackeyDecomposition :
    Rep.res K.subtype (Rep.ind H.subtype A) ≅ mackeyDirectSum H K A :=
  (Rep.mkIso (Representation.Equiv.mk
    (LinearEquiv.ofLinearMap (mackeySumToInd A) (indToMackeySum A)
      (mackeySumToInd_comp_indToMackeySum A) (indToMackeySum_comp_mackeySumToInd A))
    (mackeySumToInd_comp_ρ A))).symm

/-- The Mackey decomposition on generators: `⟦h s⁻¹ u ⊗ₜ a⟧ ↦ ⟦u ⊗ₜ h⁻¹ a⟧` in the summand of the
double coset `D`, where `s = D.out`, `h ∈ H` and `u ∈ K`.  Every element of `G` can be written in
this form for a unique `D`. -/
theorem mackeyDecomposition_hom_hom_apply_mk (D : DoubleCoset.Quotient (K : Set G) (H : Set G))
    (h : H) (u : K) (a : A) :
    (mackeyDecomposition A).hom.hom (IndV.mk H.subtype A.ρ (h * D.out⁻¹ * u) a) =
      DirectSum.lof k (DoubleCoset.Quotient (K : Set G) (H : Set G))
        (fun D => (mackeySummand H K D.out A : Type u)) D
        (IndV.mk _ (A.ρ.comp (TauCeti.mackeyToH D.out H K)) u (A.ρ h⁻¹ a)) :=
  (indToMackeySum_mk A _ a).trans (mackeyDecompAux_eq A D h u a)

/-- The inverse of the Mackey decomposition on generators: `⟦u ⊗ₜ a⟧ ↦ ⟦s⁻¹ u ⊗ₜ a⟧` from the
summand of the double coset `D`, where `s = D.out`.  It is `Rep.mackeyInclusion` on each
summand. -/
theorem mackeyDecomposition_inv_hom_apply_lof
    (D : DoubleCoset.Quotient (K : Set G) (H : Set G)) (u : K) (a : A) :
    (mackeyDecomposition A).inv.hom
        (DirectSum.lof k (DoubleCoset.Quotient (K : Set G) (H : Set G))
          (fun D => (mackeySummand H K D.out A : Type u)) D
          (IndV.mk _ (A.ρ.comp (TauCeti.mackeyToH D.out H K)) u a)) =
      IndV.mk H.subtype A.ρ (D.out⁻¹ * u) a :=
  mackeySumToInd_lof A D u a

variable (H K) in
/-- **The Mackey decomposition, naturally in the representation**: the functor
`A ↦ Res_K (Ind_H^G A)` is naturally isomorphic to the direct sum of the Mackey summands. -/
noncomputable def mackeyDecompositionNatIso :
    Rep.indFunctor k H.subtype ⋙ Rep.resFunctor K.subtype ≅
      mackeyDirectSumFunctor H K :=
  (NatIso.ofComponents (fun A => (mackeyDecomposition A).symm) fun {A B} f => by
    refine Rep.hom_ext (IntertwiningMap.ext (DirectSum.linearMap_ext k fun D =>
      IndV.hom_ext _ _ fun u => LinearMap.ext fun a => ?_))
    -- Both composites are `LinearMap.comp`s of the `IntertwiningMap` underlying a morphism of
    -- `Rep k K`; since `Rep.comp`, `Rep.res` and `Iso.symm` are sealed, no rewrite strips those
    -- wrappers, so the goal is restated definitionally as an equation between the maps applied to
    -- the generator `⟦u ⊗ₜ a⟧` of the summand of `D`.
    change (mackeyDecomposition B).inv.hom (((mackeyDirectSumFunctor H K).map f).hom
        (DirectSum.lof k (DoubleCoset.Quotient (K : Set G) (H : Set G))
          (fun D => (mackeySummand H K D.out A : Type u)) D
          (IndV.mk _ (A.ρ.comp (TauCeti.mackeyToH D.out H K)) u a))) =
      ((Rep.indFunctor k H.subtype ⋙ Rep.resFunctor K.subtype).map f).hom
        ((mackeyDecomposition A).inv.hom
          (DirectSum.lof k (DoubleCoset.Quotient (K : Set G) (H : Set G))
            (fun D => (mackeySummand H K D.out A : Type u)) D
            (IndV.mk _ (A.ρ.comp (TauCeti.mackeyToH D.out H K)) u a)))
    rw [mackeyDecomposition_inv_hom_apply_lof, mackeyDirectSumFunctor_map_hom_lof,
      mackeyDecomposition_inv_hom_apply_lof]
    rfl).symm

/-- The components of `Rep.mackeyDecompositionNatIso` are the Mackey decompositions. -/
theorem mackeyDecompositionNatIso_app (A : Rep.{u} k H) :
    (mackeyDecompositionNatIso H K).app A = mackeyDecomposition A :=
  (rfl)

end Decomposition

end Rep

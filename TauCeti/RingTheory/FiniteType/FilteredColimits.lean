/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import TauCeti.RingTheory.TensorProduct.DirectLimit
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import Mathlib.RingTheory.FiniteType
public import TauCeti.RingTheory.TensorProduct.Maps
public import TauCeti.RingTheory.TensorProduct.IsIntegral
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-!
# Finiteness at a finite stage

Integrality of finitely many generators descends along directed ring colimits.
Consequently a finite type algebra map that becomes finite after base change
to a directed colimit is finite after base change to some finite stage.
-/


public section

noncomputable section
universe u v t

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace CategoryTheory.Functor

/-- Generators integral after tensoring with a directed colimit are integral at one stage. -/
theorem exists_integral_tensor_generators_of_colimit
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ CommRingCat.{u}) (i₀ : I)
    (B₀ : Type v) (C₀ : Type t) [CommRing B₀] [Ring C₀]
    [Algebra (F.obj i₀) B₀] [Algebra (F.obj i₀) C₀]
    (φ₀ : B₀ →ₐ[F.obj i₀] C₀) (s : Finset C₀) :
    letI : Algebra (F.obj i₀) (colimit F : CommRingCat.{u}) :=
      (CommRingCat.Hom.hom (colimit.ι F i₀)).toAlgebra
    (∀ x ∈ s,
      (Algebra.TensorProduct.map
        (AlgHom.id (F.obj i₀) (colimit F : CommRingCat.{u})) φ₀).toRingHom.IsIntegralElem
          ((1 : (colimit F : CommRingCat.{u})) ⊗ₜ[F.obj i₀] x)) →
      ∃ (i : I) (h : i₀ ≤ i), ∀ (j : I) (hij : i ≤ j),
        letI : Algebra (F.obj i₀) (F.obj j) :=
          (CommRingCat.Hom.hom (F.map (homOfLE (h.trans hij)))).toAlgebra
        ∀ x ∈ s,
          (Algebra.TensorProduct.map (AlgHom.id (F.obj i₀) (F.obj j)) φ₀).toRingHom.IsIntegralElem
            ((1 : F.obj j) ⊗ₜ[F.obj i₀] x) := by
  classical
  have : Nonempty I := ⟨i₀⟩
  let S := F.obj i₀
  let R := colimit F
  let : Algebra S R := (colimit.ι F i₀).hom.toAlgebra
  intro hint
  let J := {i : I // i₀ ≤ i}
  let : Nonempty J := ⟨⟨i₀, le_rfl⟩⟩
  let : IsDirectedOrder J := ⟨fun i j ↦ by
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i.val j.val
    exact ⟨⟨k, i.property.trans hik⟩, hik, hjk⟩⟩
  let T : J → Type u := fun j ↦ F.obj j.val
  let : ∀ j, CommRing (T j) := fun j ↦ inferInstance
  let : ∀ j, Algebra S (T j) := fun j ↦ (F.map (homOfLE j.property)).hom.toAlgebra
  obtain ⟨trans, htrans, ⟨e⟩⟩ := F.exists_directLimit_tail_algEquiv_colimit i₀
  have : DirectedSystem T (trans · · ·) := htrans
  have hsingle (x : C₀) (hx : x ∈ s) :
      ∃ j, (Algebra.TensorProduct.map (AlgHom.id S (T j)) φ₀).IsIntegralElem
        ((1 : T j) ⊗ₜ[S] x) :=
    AlgEquiv.exists_integral_tensor_element e φ₀ x (hint x hx)
  choose stage hstage using fun x : s ↦ hsingle x.val x.property
  obtain ⟨j, hj⟩ := (Finset.univ.image stage).exists_le
  refine ⟨j.val, j.property, ?_⟩
  intro l hjl x hx
  let x' : s := ⟨x, hx⟩
  let l' : J := ⟨l, j.property.trans hjl⟩
  have hle : stage x' ≤ l' :=
    (hj _ (Finset.mem_image.mpr ⟨x', Finset.mem_univ _, rfl⟩)).trans hjl
  exact AlgHom.isIntegralElem_tensorProductMap_one_tmul (trans (stage x') l' hle) φ₀ x (hstage x')

end CategoryTheory.Functor
end

section
universe u v t

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

/-- A finite type map becoming finite over a directed colimit is finite at a finite stage. -/
theorem exists_finite_tensorProductMap_of_colimit
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ CommRingCat.{u}) (i₀ : I)
    (B₀ : Type v) (C₀ : Type t) [CommRing B₀] [CommRing C₀]
    [Algebra (F.obj i₀) B₀] [Algebra (F.obj i₀) C₀]
    (φ₀ : B₀ →ₐ[F.obj i₀] C₀) (hft : φ₀.FiniteType) :
    letI : Algebra (F.obj i₀) (colimit F : CommRingCat.{u}) :=
      (CommRingCat.Hom.hom (colimit.ι F i₀)).toAlgebra
    (Algebra.TensorProduct.map
      (AlgHom.id (F.obj i₀) (colimit F : CommRingCat.{u})) φ₀).Finite →
      ∃ (i : I) (h : i₀ ≤ i), ∀ (j : I) (hij : i ≤ j),
        letI : Algebra (F.obj i₀) (F.obj j) :=
          (CommRingCat.Hom.hom (F.map (homOfLE (h.trans hij)))).toAlgebra
        (Algebra.TensorProduct.map (AlgHom.id (F.obj i₀) (F.obj j)) φ₀).Finite := by
  classical
  let : Algebra (F.obj i₀) (colimit F : CommRingCat.{u}) :=
    (CommRingCat.Hom.hom (colimit.ι F i₀)).toAlgebra
  intro hfinite
  let : Algebra B₀ C₀ := φ₀.toRingHom.toAlgebra
  obtain ⟨s, hs⟩ := hft.out
  have hint : ∀ x ∈ s,
      (Algebra.TensorProduct.map
        (AlgHom.id (F.obj i₀) (colimit F : CommRingCat.{u})) φ₀).toRingHom.IsIntegralElem
          (TensorProduct.tmul (F.obj i₀) (1 : (colimit F : CommRingCat.{u})) x) := by
    intro x _
    exact hfinite.to_isIntegral _
  obtain ⟨i, h, hi⟩ := exists_integral_tensor_generators_of_colimit F i₀ B₀ C₀ φ₀ s hint
  refine ⟨i, h, ?_⟩
  intro l hil
  let : Algebra (F.obj i₀) (F.obj l) :=
    (CommRingCat.Hom.hom (F.map (homOfLE (h.trans hil)))).toAlgebra
  let ψ := Algebra.TensorProduct.map (AlgHom.id (F.obj i₀) (F.obj l)) φ₀
  let := ψ.toRingHom.toAlgebra
  have hgen := AlgHom.adjoin_one_tmul_image_eq_top_of_map
    (T := F.obj l) φ₀ (fun _ _ ↦ mul_comm _ _) (s : Set C₀) hs
  have hm : Module.Finite (TensorProduct (F.obj i₀) (F.obj l) B₀)
      (Algebra.adjoin (TensorProduct (F.obj i₀) (F.obj l) B₀)
        ((fun c ↦ TensorProduct.tmul (F.obj i₀) (1 : F.obj l) c) '' (s : Set C₀))) :=
    Algebra.finite_adjoin_of_finite_of_isIntegral (s.finite_toSet.image _) (by
      rintro _ ⟨x, hx, rfl⟩
      exact hi l hil x hx)
  rw [hgen] at hm
  exact Module.Finite.of_surjective (Subalgebra.topEquiv.toLinearMap) (by
    exact Subalgebra.topEquiv.surjective)

end CategoryTheory.Functor
end

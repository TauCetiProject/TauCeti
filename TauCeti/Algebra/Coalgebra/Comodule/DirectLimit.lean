/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Descent
public import TauCeti.Algebra.Coalgebra.DirectLimit
public import TauCeti.Algebra.Colimit.Module

/-!
# Finite comodules over a directed colimit of coalgebras descend to a stage

Let `L = colim Cᵢ` be the directed colimit of a directed system of `R`-coalgebras along
coalgebra morphisms `fᵢⱼ`, which need not be injective. This file shows that finite comodules
over `L` and the maps between them come from a stage:

* a right `L`-comodule `M` that is finitely presented over the ring `R` has a coaction which
  factors through `M ⊗ Cᵢ` for some `i` as a `Cᵢ`-coaction;
* two such factorizations at the same stage agree at a later stage;
* a comodule morphism `M → N` between comodules with factorizations at stage `i`, with `M`
  finite, is a morphism of the corestricted `Cⱼ`-comodules for some later `j`.

Over a field, or any Noetherian ring, every finite module is finitely presented
(`Module.finitePresentation_of_finite`), so every finite `L`-comodule, its
coaction equations and finitely many maps between such comodules descend to a sufficiently
large stage. A lift of the coaction to a stage need not be coassociative there, since a
transition map can identify coefficients; the coassociativity equation holds after passing to a
later stage. This is the filtered descent used to identify a category with a fibre functor with
the finite comodules over the colimit of the duals of its finite endomorphism algebras; see
Huber–Müller-Stach, *Periods and Nori motives*, §7.3, and Deligne–Milne, *Tannakian
categories*, proof of Proposition 2.14.

## Main results

* `TauCeti.Comodule.exists_comoduleFactor_ofCoalgHom`: a finitely presented comodule over the
  colimit descends to a stage.
* `TauCeti.Comodule.exists_lTensor_comp_coact_eq_of_factor`: two descents to the same stage
  agree at a later stage.
* `TauCeti.Comodule.Hom.exists_map_lTensor_comp_coact_eq`: a comodule morphism out of a finite
  comodule descends to a later stage.
-/

public section

open TensorProduct Module.DirectLimit

namespace TauCeti.Comodule

section Ring

variable {R : Type*} [CommRing R] {ι : Type*} [Preorder ι] [DecidableEq ι]
  [IsDirectedOrder ι] {C : ι → Type*} [∀ i, AddCommGroup (C i)] [∀ i, Module R (C i)]
  [∀ i, Coalgebra R (C i)] {f : ∀ i j, i ≤ j → C i →ₗc[R] C j}
  [DirectedSystem C fun i j h ↦ (f i j h : C i →ₗ[R] C j)]
  {M : Type*} [AddCommGroup M] [Module R M]
  [Comodule R (Module.DirectLimit C fun i j h ↦ (f i j h : C i →ₗ[R] C j)) M]

/-- A finitely presented comodule over a directed colimit of coalgebras descends to a stage: its
coaction factors through a coaction of some stage. -/
theorem exists_comoduleFactor_ofCoalgHom [Nonempty ι] [Module.FinitePresentation R M] :
    ∃ i, ∃ σ : Comodule R (C i) M, (ofCoalgHom f i).toLinearMap.lTensor M ∘ₗ σ.coact =
      coact (R := R) (C := Module.DirectLimit C fun i j h ↦ (f i j h : C i →ₗ[R] C j))
        (M := M) := by
  -- Lift the coaction to some stage `i`, as a linear map.
  obtain ⟨i, ρ, hρ⟩ := TauCeti.DirectLimit.exists_comp_eq_of_finitePresentation
    (f := fun i j h ↦ (f i j h : C i →ₗ[R] C j).lTensor M)
    (φ := fun i ↦ (of R ι C (fun i j h ↦ (f i j h : C i →ₗ[R] C j)) i).lTensor M)
    (fun _ _ ↦ lTensor_of_lTensor_f M) (exists_lTensor_of_eq M)
    (fun _ _ _ h ↦ exists_lTensor_eq_of_lTensor_of_eq
      (f := fun i j h ↦ (f i j h : C i →ₗ[R] C j)) h) coact
  replace hρ : (ofCoalgHom f i).toLinearMap.lTensor M ∘ₗ ρ = coact := by
    simpa only [CoalgHom.toLinearMap_eq_ofClass, toLinearMap_ofCoalgHom] using hρ
  -- The two sides of coassociativity of the lift agree in `M ⊗ (colim Cₖ ⊗ colim Cₖ)`, so they
  -- agree in `M ⊗ (Cⱼ ⊗ Cⱼ)` for some later stage `j`.
  have hc := CoalgHom.lTensor_map_comp_coassoc_of_factor (ofCoalgHom f i) ρ hρ
  simp only [CoalgHom.toLinearMap_eq_ofClass, toLinearMap_ofCoalgHom] at hc
  obtain ⟨j, hij, hj⟩ := TauCeti.DirectLimit.exists_comp_eq_comp (M := M)
    (G := fun i ↦ M ⊗[R] (C i ⊗[R] C i))
    (f := fun i j h ↦
      (TensorProduct.map (f i j h : C i →ₗ[R] C j) (f i j h : C i →ₗ[R] C j)).lTensor M)
    (φ := fun i ↦ (TensorProduct.map (of R ι C (fun i j h ↦ (f i j h : C i →ₗ[R] C j)) i)
      (of R ι C (fun i j h ↦ (f i j h : C i →ₗ[R] C j)) i)).lTensor M)
    (fun _ _ _ h ↦ exists_lTensor_map_eq_of_lTensor_map_of_eq
      (f := fun i j h ↦ (f i j h : C i →ₗ[R] C j)) h)
    hc
  refine ⟨j, ⟨(f i j hij : C i →ₗ[R] C j).lTensor M ∘ₗ ρ, ?_, ?_⟩, ?_⟩
  · ext m
    have hm := LinearMap.congr_fun hj m
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at hm ⊢
    rw [LinearMap.assoc_rTensor_lTensor_comp, ← LinearMap.lTensor_def, hm,
      ← LinearMap.lTensor_comp_apply, CoalgHomClass.map_comp_comul, LinearMap.lTensor_comp_apply]
  · rw [← LinearMap.comp_assoc, ← LinearMap.lTensor_comp, CoalgHomClass.counit_comp]
    exact CoalgHom.lTensor_counit_comp_of_factor (ofCoalgHom f i) ρ hρ
  · rw [← hρ]
    simp only [CoalgHom.toLinearMap_eq_ofClass, toLinearMap_ofCoalgHom]
    exact LinearMap.ext fun m ↦ lTensor_of_lTensor_f M hij (ρ m)

end Ring

section Semiring

variable {R : Type*} [CommSemiring R] {ι : Type*} [Preorder ι] [DecidableEq ι]
  [IsDirectedOrder ι] {C : ι → Type*} [∀ i, AddCommMonoid (C i)] [∀ i, Module R (C i)]
  [∀ i, Coalgebra R (C i)] {f : ∀ i j, i ≤ j → C i →ₗc[R] C j}
  [DirectedSystem C fun i j h ↦ (f i j h : C i →ₗ[R] C j)]
  {M : Type*} [AddCommMonoid M] [Module R M]
  [Comodule R (Module.DirectLimit C fun i j h ↦ (f i j h : C i →ₗ[R] C j)) M]

/-- Two descents of a finite comodule over a directed colimit of coalgebras to the same stage
agree at a later stage: their corestricted coactions coincide. -/
theorem exists_lTensor_comp_coact_eq_of_factor [Module.Finite R M] {i : ι}
    (σ σ' : Comodule R (C i) M)
    (hσ : (ofCoalgHom f i).toLinearMap.lTensor M ∘ₗ σ.coact =
      coact (R := R) (C := Module.DirectLimit C fun i j h ↦ (f i j h : C i →ₗ[R] C j)) (M := M))
    (hσ' : (ofCoalgHom f i).toLinearMap.lTensor M ∘ₗ σ'.coact =
      coact (R := R) (C := Module.DirectLimit C fun i j h ↦ (f i j h : C i →ₗ[R] C j)) (M := M)) :
    ∃ j, ∃ hij : i ≤ j, (f i j hij).toLinearMap.lTensor M ∘ₗ σ.coact =
      (f i j hij).toLinearMap.lTensor M ∘ₗ σ'.coact :=
  TauCeti.DirectLimit.exists_comp_eq_comp
    (φ := fun i ↦ (ofCoalgHom f i).toLinearMap.lTensor M)
    (fun _ _ _ h ↦ exists_lTensor_eq_of_lTensor_of_eq
      (f := fun i j h ↦ (f i j h : C i →ₗ[R] C j))
      (by simpa only [CoalgHom.toLinearMap_eq_ofClass, toLinearMap_ofCoalgHom] using h))
    (hσ.trans hσ'.symm)

variable {N : Type*} [AddCommMonoid N] [Module R N]
  [Comodule R (Module.DirectLimit C fun i j h ↦ (f i j h : C i →ₗ[R] C j)) N]

/-- A morphism of comodules over a directed colimit of coalgebras, out of a finite comodule,
descends to a stage: if both comodules descend to a stage `i`, then the morphism commutes with
the corestricted coactions of some later stage `j`. -/
theorem Hom.exists_map_lTensor_comp_coact_eq [Module.Finite R M]
    (g : Hom R (Module.DirectLimit C fun i j h ↦ (f i j h : C i →ₗ[R] C j)) M N) {i : ι}
    (σ : Comodule R (C i) M) (τ : Comodule R (C i) N)
    (hσ : (ofCoalgHom f i).toLinearMap.lTensor M ∘ₗ σ.coact =
      coact (R := R) (C := Module.DirectLimit C fun i j h ↦ (f i j h : C i →ₗ[R] C j)) (M := M))
    (hτ : (ofCoalgHom f i).toLinearMap.lTensor N ∘ₗ τ.coact =
      coact (R := R) (C := Module.DirectLimit C fun i j h ↦ (f i j h : C i →ₗ[R] C j)) (M := N)) :
    ∃ j, ∃ hij : i ≤ j, TensorProduct.map g.toLinearMap LinearMap.id ∘ₗ
        (f i j hij).toLinearMap.lTensor M ∘ₗ σ.coact =
      (f i j hij).toLinearMap.lTensor N ∘ₗ τ.coact ∘ₗ g.toLinearMap := by
  have hcomm (k : ι) (u : C i →ₗ[R] C k) :
      u.lTensor N ∘ₗ TensorProduct.map g.toLinearMap LinearMap.id =
        TensorProduct.map g.toLinearMap LinearMap.id ∘ₗ u.lTensor M :=
    TensorProduct.ext' fun _ _ ↦ rfl
  have hcomm' : (ofCoalgHom f i).toLinearMap.lTensor N ∘ₗ
      TensorProduct.map g.toLinearMap LinearMap.id =
        TensorProduct.map g.toLinearMap LinearMap.id ∘ₗ (ofCoalgHom f i).toLinearMap.lTensor M :=
    TensorProduct.ext' fun _ _ ↦ rfl
  obtain ⟨j, hij, hj⟩ := TauCeti.DirectLimit.exists_comp_eq_comp
    (φ := fun i ↦ (ofCoalgHom f i).toLinearMap.lTensor N)
    (fun _ _ _ h ↦ exists_lTensor_eq_of_lTensor_of_eq
      (f := fun i j h ↦ (f i j h : C i →ₗ[R] C j))
      (by simpa only [CoalgHom.toLinearMap_eq_ofClass, toLinearMap_ofCoalgHom] using h))
    (u := TensorProduct.map g.toLinearMap LinearMap.id ∘ₗ σ.coact) (v := τ.coact ∘ₗ g.toLinearMap)
    (by
      rw [← LinearMap.comp_assoc, hcomm', LinearMap.comp_assoc, hσ, g.map_coact,
        ← LinearMap.comp_assoc, hτ])
  refine ⟨j, hij, ?_⟩
  rw [← LinearMap.comp_assoc, ← hcomm, LinearMap.comp_assoc]
  exact hj

end Semiring

end TauCeti.Comodule

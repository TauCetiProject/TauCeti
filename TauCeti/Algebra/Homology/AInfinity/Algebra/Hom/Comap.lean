/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.Map
public import TauCeti.Algebra.Homology.AInfinity.Algebra.Unit
public import TauCeti.Algebra.Homology.AInfinity.Algebra.Hom.Iso

/-!
# Strict inclusions of pulled-back A-infinity algebras

The injective linear map defining `AInfinityAlgebra.comap` intertwines all operations,
so it defines a strict `A∞` morphism from the pullback to the original algebra.
Its underlying linear map is the given map. This construction supplies the inclusion
of the total algebra of a full `A∞` subcategory; when the map is bijective, the strict
morphism is an `A∞` isomorphism, and any preimage of a strict unit is a strict unit of
the pullback.
-/

public section

universe uR uA uB

namespace TauCeti.AInfinityAlgebra

variable {R : Type uR} {A : Type uA} {B : Type uB} [CommRing R]
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  (ℬ : AInfinityAlgebra R B) (G : InternalGrading R A ℤ) (f : A →ₗ[R] B)
  (hf : Function.Injective f) (hG : ∀ (p : ℤ) (a : A), f a ∈ ℬ.grading.piece p ↔ a ∈ G.piece p)
  (hm : ∀ n, 0 < n → ∀ x : Fin n → A, ℬ.m n (fun i ↦ f (x i)) ∈ LinearMap.range f)

/-- The injective map along which an `A∞` algebra is pulled back, as a strict `A∞` morphism. -/
noncomputable def comapStrictHom : AInfinityStrictHom (ℬ.comap G f hf hG hm) ℬ where
  toLinearMap := f
  map_mem' ha := (hG _ _).2 (by rwa [comap_grading] at ha)
  map_m' n := MultilinearMap.ext fun x ↦ by simp

/-- The underlying linear map of the strict pullback inclusion is the given map. -/
@[simp]
theorem comapStrictHom_toLinearMap :
    (ℬ.comapStrictHom G f hf hG hm).toLinearMap = f := by
  simp [comapStrictHom]

/-- The strict `A∞` morphism `comapStrictHom` is the injective map along which the algebra is
pulled back. -/
@[simp]
theorem coe_comapStrictHom : ⇑(ℬ.comapStrictHom G f hf hG hm) = f :=
  congrArg (fun g : A →ₗ[R] B ↦ ⇑g) (comapStrictHom_toLinearMap ℬ G f hf hG hm)

/-- When the pullback map is bijective, `comapStrictHom` is an `A∞` isomorphism. -/
theorem isIso_toAInfinityHom_comapStrictHom (hbij : Function.Bijective f) :
    (ℬ.comapStrictHom G f hf hG hm).toAInfinityHom.IsIso := by
  rw [AInfinityHom.isIso_iff_linearPart_bijective, AInfinityStrictHom.linearPart_toAInfinityHom,
    comapStrictHom_toLinearMap]
  exact hbij

/-- A preimage of a strict unit along the injective pullback map is a strict unit of the
pulled-back `A∞` algebra. -/
theorem StrictUnit.comap {e : A} (hℬ : ℬ.StrictUnit (f e)) :
    (ℬ.comap G f hf hG hm).StrictUnit e where
  degree_zero := by
    rw [comap_grading]
    exact (hG 0 e).1 hℬ.degree_zero
  binary_left x := hf <| by
    have hfun : (fun i : Fin 2 ↦ f (![e, x] i)) = ![f e, f x] :=
      funext fun i ↦ by fin_cases i <;> rfl
    rw [map_m_comap, hfun, hℬ.binary_left]
  binary_right x := hf <| by
    have hfun : (fun i : Fin 2 ↦ f (![x, e] i)) = ![f x, f e] :=
      funext fun i ↦ by fin_cases i <;> rfl
    rw [map_m_comap, hfun, hℬ.binary_right]
  higher n hn x := by
    rintro ⟨i, rfl⟩
    exact hf (by rw [map_m_comap, hℬ.m_eq_zero_of_eq_unit hn _ rfl, map_zero])

end TauCeti.AInfinityAlgebra

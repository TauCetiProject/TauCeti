/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Coinduced
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# The Galois action on a semi-local algebra

Let `L/K` be an extension and `A` a commutative `K`-algebra, in practice the completion `K_v`
of a number field `K` at a finite or an infinite place `v`. An automorphism `σ` of `L/K` acts
on the semi-local algebra `A ⊗[K] L` through the second factor, by `id ⊗ σ`; this is
`semilocalGaloisHom`. The semi-local decompositions `K_v ⊗[K] L ≃ ∏_{w ∣ v} L_w` at finite
places (`TauCeti.semilocalEquiv_semilocalGaloisHom`) and at infinite places
(`TauCeti.GlobalNumberFields.infiniteSemilocalEquiv_semilocalGaloisHom`) show that it permutes
the factors.

This file also contains the part of the proof that the semi-local units are coinduced from a
decomposition group which does not depend on the kind of place. Let a group `G` act on a type
`X` that decomposes as a product `∏_{i : ι} M i`, with the indices lying over a `G`-set `P`
along `p : ι → P`, and suppose `g` carries the factor at `i` to the factor at `j` along a
bijection `T g : M i ≃ M j` whenever `p j = g • p i`. If every index is carried to a fixed index
`w`, an element of `X` is determined by the components at `w` of its translates
(`semilocal_eq_of_forall_component_eq`). If moreover every element of `G` carries some index to
`w`, every function `G → M w` that is equivariant for the stabilizer of `p w` arises in this way
(`semilocal_exists_forall_component_eq`).

## Main definitions

* `TauCeti.semilocalGaloisHom`: the action `σ ↦ id ⊗ σ` of `Aut(L/K)` on `A ⊗[K] L`.

## Main results

* `TauCeti.semilocal_eq_of_forall_component_eq`,
  `TauCeti.semilocal_exists_forall_component_eq`: injectivity and surjectivity of the map
  `x ↦ (g ↦ (g • x)_w)` into the stabilizer-equivariant functions.
* `TauCeti.semilocal_resCoindToHom_bijective`: the map into the representation coinduced from
  the stabilizer of `p w`, adjoint to the projection to the factor at `w`, is bijective.
-/

public section

open scoped TensorProduct

namespace TauCeti

section GaloisHom

variable {K : Type*} [CommSemiring K] (A L : Type*) [CommSemiring A] [Algebra K A] [Semiring L]
  [Algebra K L]

/-- The action of `Aut(L/K)` on the semi-local algebra `A ⊗[K] L` through the second factor:
`σ` acts by `id ⊗ σ`. -/
noncomputable def semilocalGaloisHom : (L ≃ₐ[K] L) →* (A ⊗[K] L ≃ₐ[A] A ⊗[K] L) where
  toFun σ := Algebra.TensorProduct.congr AlgEquiv.refl σ
  map_one' := Algebra.TensorProduct.congr_refl
  map_mul' _ _ := AlgEquiv.coe_toAlgHom_injective (Algebra.TensorProduct.ext' fun _ _ ↦ rfl)

variable {A L}

/-- The Galois action on the semi-local algebra on a pure tensor. -/
@[simp]
theorem semilocalGaloisHom_tmul (σ : L ≃ₐ[K] L) (a : A) (x : L) :
    semilocalGaloisHom A L σ (a ⊗ₜ x) = a ⊗ₜ σ x :=
  (rfl)

end GaloisHom

section Coinduction

variable {G P ι X : Type*} [Group G] [MulAction G P] {p : ι → P} {act : G → X → X}
  {M : ι → Type*} (e : X ≃ ∀ i, M i) (T : ∀ (g : G) {i j : ι}, p j = g • p i → M i ≃ M j)
  (he : ∀ (g : G) (x : X) {i j : ι} (h : p j = g • p i), e (act g x) j = T g h (e x i))
  {w : ι}

include he in
/-- If `G` carries every factor to the factor at `w`, an element of `X` is determined by the
components at `w` of its translates. -/
theorem semilocal_eq_of_forall_component_eq (htrans : ∀ i, ∃ g : G, p w = g • p i) {x x' : X}
    (h : ∀ g, e (act g x) w = e (act g x') w) : x = x' :=
  e.injective <| funext fun i ↦ by
    obtain ⟨g, hg⟩ := htrans i
    simpa only [he g _ hg, (T g hg).apply_eq_iff_eq] using h g

include he in
/-- If `G` carries every factor to the factor at `w`, every element of `G` carries some factor
to it, and the transport maps compose, then every function `G → M w` that is equivariant for the
stabilizer of `p w` is `g ↦ (g • x)_w` for some `x : X`. -/
theorem semilocal_exists_forall_component_eq
    (hT : ∀ (g g' : G) {i j k : ι} (h : p j = g • p i) (h' : p k = g' • p j) (a : M i),
      T g' h' (T g h a) = T (g' * g) (by rw [h', h, mul_smul]) a)
    (htrans : ∀ i, ∃ g : G, p w = g • p i) (hsurj : ∀ g : G, ∃ i, p w = g • p i)
    (f : G → M w) (hf : ∀ (d : G) (hd : p w = d • p w) (g : G), f (d * g) = T d hd (f g)) :
    ∃ x : X, ∀ g, e (act g x) w = f g := by
  choose g hg using htrans
  -- the component at `i` is the value of `f` at an element `g i` carrying `i` to `w`,
  -- transported back to `M i`; equivariance of `f` for the stabilizer of `p w` makes the
  -- result independent of the choice of `g i`
  refine ⟨e.symm fun i ↦ (T (g i) (hg i)).symm (f (g i)), fun σ ↦ ?_⟩
  obtain ⟨i, hi⟩ := hsurj σ
  have hd : p w = (σ * (g i)⁻¹) • p w := by rw [mul_smul, inv_smul_eq_iff.mpr (hg i), ← hi]
  have hcongr {g₁ g₂ : G} (h₁ : p w = g₁ • p i) (h₂ : p w = g₂ • p i) (hg : g₁ = g₂) (b : M i) :
      T g₁ h₁ b = T g₂ h₂ b := by
    subst hg
    rfl
  rw [he σ _ hi, e.apply_symm_apply,
    hcongr hi (by rw [mul_smul, ← hg i, ← hd]) (inv_mul_cancel_right σ (g i)).symm,
    ← hT _ _ (hg i) hd, Equiv.apply_symm_apply, ← hf, inv_mul_cancel_right]

/-- **Coinduction from a stabilizer.** Let `B` be a representation of `G` that decomposes as a
product `∏_{i : ι} M i` on which `g` carries the factor at `i` to the factor at `j` along
`T g : M i ≃ M j` whenever `p j = g • p i`, and let `A` be a representation of the stabilizer of
`p w` whose underlying type is identified with `M w`, the action of the stabilizer being given by
`T`. If `G` permutes the factors transitively, every element of `G` carries some factor to `w`,
and the transport maps compose, then the map `B ⟶ Coind A` adjoint to the projection
`f : B ⟶ A` to the factor at `w` is bijective. -/
theorem semilocal_resCoindToHom_bijective {k : Type*} [CommRing k] {B : Rep k G}
    {A : Rep k (MulAction.stabilizer G (p w))}
    (f : Rep.res (MulAction.stabilizer G (p w)).subtype B ⟶ A) (e : B ≃ ∀ i, M i)
    (he : ∀ (g : G) (x : B) {i j : ι} (h : p j = g • p i), e (B.ρ g x) j = T g h (e x i))
    (eA : A ≃ M w) (hf : ∀ x, eA (f.hom x) = e x w)
    (hA : ∀ (d : MulAction.stabilizer G (p w)) (a : A),
      eA (A.ρ d a) = T d (MulAction.mem_stabilizer_iff.mp d.2).symm (eA a))
    (hT : ∀ (g g' : G) {i j k : ι} (h : p j = g • p i) (h' : p k = g' • p j) (a : M i),
      T g' h' (T g h a) = T (g' * g) (by rw [h', h, mul_smul]) a)
    (htrans : ∀ i, ∃ g : G, p w = g • p i) (hsurj : ∀ g : G, ∃ i, p w = g • p i) :
    Function.Bijective (Rep.resCoindToHom _ B A f).hom := by
  refine ⟨fun x x' h ↦ semilocal_eq_of_forall_component_eq e T he htrans fun g ↦ ?_, fun F ↦ ?_⟩
  · rw [← hf, ← hf]
    exact congrArg (fun F ↦ eA (F.1 g)) h
  obtain ⟨x, hx⟩ := semilocal_exists_forall_component_eq e T he hT htrans hsurj
    (fun g ↦ eA (F.1 g)) fun d hd g ↦ by
      have hF := F.2 ⟨d, MulAction.mem_stabilizer_iff.mpr hd.symm⟩ g
      simp only [Subgroup.subtype_apply] at hF
      rw [hF, hA]
  exact ⟨x, Subtype.ext <| funext fun g ↦ eA.injective <| (hf _).trans (hx g)⟩

end Coinduction

end TauCeti

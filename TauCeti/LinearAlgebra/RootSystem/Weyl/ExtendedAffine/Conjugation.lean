/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.CoweightLattice.Automorphism
public import TauCeti.LinearAlgebra.RootSystem.Weyl.BasedAut
public import TauCeti.LinearAlgebra.RootSystem.Weyl.ExtendedAffine.Alcove

/-!
# Based automorphisms acting on `Ω` by conjugation

Let `P` be a root pairing with coweight space `N`, coweight lattice `P∨` and coroot lattice `Q∨`.
An automorphism `g` of `P` acts on `N` by the contragredient `g.coweightEquiv.symm` of its action
on weights (`RootPairing.coweightAffineHom`), preserving `P∨` and `Q∨` and inducing an action on
`P∨ / Q∨` (`RootPairing.coweightQuotientHom`). It normalizes the extended affine Weyl group
`W_ext = P∨ ⋊ W`: conjugation by `g` carries the coreflection in `αᵢ^∨` to the coreflection in
`α_{g i}^∨`, and the translation by `λ` to the translation by `g λ`.

Now let `b` be a base of a finite, reduced, irreducible, crystallographic pairing. A based
automorphism `δ` permutes the simple roots and fixes the highest root `θ`
(`RootPairing.Base.indexEquiv_highestRoot`), so it preserves the fundamental alcove

`A = {x | αᵢ(x) > 0 for every simple root αᵢ, and θ(x) < 1}`,

and hence normalizes its stabilizer `Ω = Stab_{W_ext}(A)`. This gives the conjugation action
`Γ_root → Aut(Ω)`, `δ • ω = δ ω δ⁻¹` (`RootPairing.Base.conjFundamentalAlcoveStabilizer`), the
action that enters the semidirect product `Ω ⋊ Γ_root`. Since `δ` is linear, the translation part
of `δ ω δ⁻¹` is `δ (ω 0)`, so the map `Ω → P∨ / Q∨` sending `ω` to the class of `ω 0` (an
isomorphism over an archimedean field, `RootPairing.fundamentalAlcoveStabilizerEquivQuotient`)
intertwines the conjugation action with the action of `Γ_root` on `P∨ / Q∨`
(`RootPairing.fundamentalAlcoveStabilizerToQuotient_conjFundamentalAlcoveStabilizer`).

## Main definitions

* `RootPairing.Base.conjFundamentalAlcoveStabilizer`: the action of the based automorphisms on
  `Ω` by conjugation.

## Main results

* `RootPairing.range_coweightAffineHom_le_normalizer_extendedAffineWeylGroup`: the automorphisms
  of `P` normalize the extended affine Weyl group.
* `RootPairing.image_coweightAffineHom_fundamentalAlcove`: a based automorphism preserves the
  fundamental alcove.
* `RootPairing.map_basedAut_le_normalizer_fundamentalAlcoveStabilizer`: the based automorphisms
  normalize `Ω`.
* `RootPairing.fundamentalAlcoveStabilizerToQuotient_conjFundamentalAlcoveStabilizer`: **the map
  `Ω → P∨ / Q∨` is equivariant for the actions of the based automorphisms.**

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4–6*, Ch. VI, §2.3 and §4 (the group `Ω`,
  its isomorphism with `P(R∨) / Q(R∨)`, and the automorphisms of the extended Dynkin diagram).
* N. Iwahori and H. Matsumoto, *On some Bruhat decomposition and the structure of the Hecke rings
  of p-adic Chevalley groups*, Publ. Math. IHÉS 25 (1965), §1.
-/

public section

open Set

namespace RootPairing

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] (P : RootPairing ι R M N)

/-! ### Automorphisms normalize the extended affine Weyl group -/

/-- **The automorphisms of a root pairing normalize the extended affine Weyl group** `P∨ ⋊ W`:
conjugation by `g` carries an element with linear part `w` and translation part `f 0` to the
element with linear part `g w g⁻¹` and translation part `g (f 0)`. -/
theorem range_coweightAffineHom_le_normalizer_extendedAffineWeylGroup :
    P.coweightAffineHom.range ≤
      Subgroup.normalizer (P.extendedAffineWeylGroup : Set (N ≃ᵃ[R] N)) := by
  rw [Subgroup.le_normalizer_iff]
  rintro _ ⟨g, rfl⟩ f hf
  rw [mem_extendedAffineWeylGroup_iff] at hf ⊢
  refine ⟨?_, ?_⟩
  · rw [← AffineEquiv.linearHom_apply, map_mul, map_mul, map_inv, AffineEquiv.linearHom_apply,
      AffineEquiv.linearHom_apply, linear_coweightAffineHom]
    exact g.conj_mem_closure_range_coreflection hf.1
  · -- The automorphism `g` acts linearly, so `(g f g⁻¹) 0 = g (f 0)`.
    simp only [AffineEquiv.coe_mul, Function.comp_apply, ← map_inv, coweightAffineHom_apply,
      map_zero]
    exact g.coweightEquiv_symm_apply_mem_coweightLattice hf.2

/-! ### Based automorphisms normalize `Ω` -/

section Alcove

variable [CharZero R] [Finite ι] [Nonempty ι] [Preorder R] [IsDomain R] [P.IsCrystallographic]
  [P.IsReduced] [P.IsIrreducible] {P} {b : P.Base}

/-- A based automorphism carries the fundamental alcove into itself: it permutes the simple roots
and fixes the highest root. -/
private lemma coweightAffineHom_apply_mem_fundamentalAlcove {g : P.Aut} (hg : g ∈ b.basedAut)
    {x : N} (hx : x ∈ fundamentalAlcove P b) : P.coweightAffineHom g x ∈ fundamentalAlcove P b := by
  have hθ : g.indexEquiv.symm b.highestRoot = b.highestRoot := g.indexEquiv.symm_apply_eq.mpr
    (b.indexEquiv_highestRoot g (Base.mem_basedAut_iff_forall_mem_support.mp hg)).symm
  rw [mem_fundamentalAlcove] at hx
  refine (mem_fundamentalAlcove P b).2 ⟨fun i hi ↦ ?_, ?_⟩
  · rw [← Finset.mem_coe, ← Base.mem_basedAut_iff.mp hg] at hi
    obtain ⟨j, hj, rfl⟩ := hi
    rw [coweightAffineHom_apply, Equiv.root'_coweightEquiv_symm_apply,
      _root_.Equiv.symm_apply_apply]
    exact hx.1 j hj
  · rw [coweightAffineHom_apply, Equiv.root'_coweightEquiv_symm_apply, hθ]
    exact hx.2

/-- **A based automorphism preserves the fundamental alcove.** -/
theorem image_coweightAffineHom_fundamentalAlcove {g : P.Aut} (hg : g ∈ b.basedAut) :
    P.coweightAffineHom g '' fundamentalAlcove P b = fundamentalAlcove P b := by
  refine (image_subset_iff.2 fun x hx ↦
    coweightAffineHom_apply_mem_fundamentalAlcove hg hx).antisymm fun y hy ↦
      ⟨P.coweightAffineHom g⁻¹ y, coweightAffineHom_apply_mem_fundamentalAlcove (inv_mem hg) hy, ?_⟩
  rw [map_inv, AffineEquiv.inv_def]
  exact AffineEquiv.apply_symm_apply _ y

variable (P b) in
/-- **The based automorphisms normalize the stabilizer `Ω` of the fundamental alcove**, since
they normalize the extended affine Weyl group and preserve the fundamental alcove. -/
theorem map_basedAut_le_normalizer_fundamentalAlcoveStabilizer :
    b.basedAut.map P.coweightAffineHom ≤
      Subgroup.normalizer (P.fundamentalAlcoveStabilizer b : Set (N ≃ᵃ[R] N)) := by
  rw [Subgroup.le_normalizer_iff]
  rintro _ ⟨g, hg, rfl⟩ f hf
  rw [mem_fundamentalAlcoveStabilizer] at hf ⊢
  obtain ⟨hf, hfA⟩ := hf
  refine ⟨(P.range_coweightAffineHom_le_normalizer_extendedAffineWeylGroup ⟨g, rfl⟩ f).mp hf, ?_⟩
  rw [AffineEquiv.coe_mul, AffineEquiv.coe_mul, image_comp, image_comp, ← map_inv,
    image_coweightAffineHom_fundamentalAlcove (inv_mem hg), hfA,
    image_coweightAffineHom_fundamentalAlcove hg]

variable (b) in
/-- The action of the based automorphisms on the stabilizer `Ω` of the fundamental alcove by
conjugation, `δ • ω = δ ω δ⁻¹`, where `δ` acts on the coweight space through
`RootPairing.coweightAffineHom`. This is the action defining the semidirect product
`Ω ⋊ Γ_root`. -/
noncomputable def Base.conjFundamentalAlcoveStabilizer :
    b.basedAut →* MulAut (P.fundamentalAlcoveStabilizer b) :=
  (P.fundamentalAlcoveStabilizer b).normalizerMonoidHom.comp
    ((P.coweightAffineHom.comp b.basedAut.subtype).codRestrict _ fun δ ↦
      map_basedAut_le_normalizer_fundamentalAlcoveStabilizer P b ⟨δ, δ.2, rfl⟩)

/-- A based automorphism `δ` acts on `Ω` by `ω ↦ δ ω δ⁻¹`. -/
@[simp]
theorem Base.coe_conjFundamentalAlcoveStabilizer_apply (δ : b.basedAut)
    (ω : P.fundamentalAlcoveStabilizer b) :
    (b.conjFundamentalAlcoveStabilizer δ ω : N ≃ᵃ[R] N) =
      P.coweightAffineHom δ * ω * (P.coweightAffineHom δ)⁻¹ :=
  (rfl)

/-- The translation part of `δ ω δ⁻¹` is `δ (ω 0)`, since `δ` acts linearly. -/
theorem Base.conjFundamentalAlcoveStabilizer_apply_zero (δ : b.basedAut)
    (ω : P.fundamentalAlcoveStabilizer b) :
    (b.conjFundamentalAlcoveStabilizer δ ω : N ≃ᵃ[R] N) 0 =
      (δ : P.Aut).coweightEquiv.symm (ω.1 0) := by
  simp only [coe_conjFundamentalAlcoveStabilizer_apply, AffineEquiv.coe_mul, Function.comp_apply,
    ← map_inv, coweightAffineHom_apply, map_zero]

/-- **The map `Ω → P∨ / Q∨` is equivariant for the based automorphisms**: the class of the
translation part of `δ ω δ⁻¹` is the image under `δ` of the class of the translation part of `ω`.
Over an archimedean field this map is the isomorphism
`RootPairing.fundamentalAlcoveStabilizerEquivQuotient`. -/
theorem fundamentalAlcoveStabilizerToQuotient_conjFundamentalAlcoveStabilizer (δ : b.basedAut)
    (ω : P.fundamentalAlcoveStabilizer b) :
    P.fundamentalAlcoveStabilizerToQuotient b (b.conjFundamentalAlcoveStabilizer δ ω) =
      .ofAdd (P.coweightQuotientHom δ (P.fundamentalAlcoveStabilizerToQuotient b ω).toAdd) := by
  simp only [fundamentalAlcoveStabilizerToQuotient_apply, toAdd_ofAdd, coweightQuotientHom_mk,
    Base.conjFundamentalAlcoveStabilizer_apply_zero]

end Alcove

end RootPairing

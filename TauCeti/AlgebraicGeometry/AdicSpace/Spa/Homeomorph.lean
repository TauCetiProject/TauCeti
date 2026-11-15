/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.RationalSubset.Basis

/-!
# Homeomorphisms of adic spectra from isomorphisms of topological rings

An isomorphism of topological rings `e : A ≃+* B` carrying a subring `A⁺ ⊆ A` onto `B⁺ ⊆ B`
induces a homeomorphism of sub-unit valuation loci

```text
spaHomeomorphOfRingEquiv e … : Spa(B, B⁺) ≃ₜ Spa(A, A⁺)
```

whose forward map pulls valuations on `B` back along `e` and whose inverse pulls valuations on
`A` back along `e.symm`. Preimage and image along this homeomorphism match the rational families
`spaRationalFamily A⁺` and `spaRationalFamily B⁺`.

Neither a Huber hypothesis nor `[IsTopologicalRing]` is required: `A` and `B` need only be
commutative rings equipped with topologies, in possibly distinct universes, and `A⁺`, `B⁺` are
arbitrary subrings related by `A⁺.map e = B⁺`.

## Main definitions

* `TauCeti.ValuationSpectrum.spaHomeomorphOfRingEquiv`: the homeomorphism
  `Spa(B, B⁺) ≃ₜ Spa(A, A⁺)` induced by a homeomorphic ring equivalence `e : A ≃+* B` with
  `A⁺.map e = B⁺`.

## Main results

* `TauCeti.ValuationSpectrum.spaHomeomorphOfRingEquiv_apply`,
  `TauCeti.ValuationSpectrum.coe_spaHomeomorphOfRingEquiv`,
  `TauCeti.ValuationSpectrum.spaHomeomorphOfRingEquiv_val`,
  `TauCeti.ValuationSpectrum.spaHomeomorphOfRingEquiv_symm`: characteristic equations for the
  homeomorphism and its inverse, together with identity and composition laws
  `spaHomeomorphOfRingEquiv_refl` and `spaHomeomorphOfRingEquiv_trans`.
* `TauCeti.ValuationSpectrum.spaHomeomorphOfRingEquiv_preimage_mem_spaRationalFamily`,
  `TauCeti.ValuationSpectrum.spaHomeomorphOfRingEquiv_image_mem_spaRationalFamily`,
  `TauCeti.ValuationSpectrum.spaHomeomorphOfRingEquiv_preimage_mem_spaRationalFamily_iff`,
  `TauCeti.ValuationSpectrum.bijOn_preimage_spaHomeomorphOfRingEquiv_spaRationalFamily`:
  preimage and image along `spaHomeomorphOfRingEquiv` biject `spaRationalFamily A⁺` onto
  `spaRationalFamily B⁺`.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Definition 7.23 and Remark 7.30.
-/

public section

namespace TauCeti.ValuationSpectrum

universe u v w

variable {A : Type u} [CommRing A] [TopologicalSpace A]
  {B : Type v} [CommRing B] [TopologicalSpace B]

omit [TopologicalSpace A] [TopologicalSpace B] in
private theorem map_symm_eq_of_map_eq (e : A ≃+* B) {Aplus : Subring A} {Bplus : Subring B}
    (hplus : Aplus.map (e : A →+* B) = Bplus) :
    Bplus.map (e.symm : B →+* A) = Aplus := by
  subst hplus
  ext a
  simp

/-- **Homeomorphism of adic spectra induced by an isomorphism of topological rings.** For a ring
isomorphism `e : A ≃+* B` that is continuous in both directions and carries `A⁺` onto `B⁺`,
pullback along `e` is a homeomorphism `Spa(B, B⁺) ≃ₜ Spa(A, A⁺)` whose inverse is pullback
along `e.symm`. -/
def spaHomeomorphOfRingEquiv (e : A ≃+* B) (he : Continuous e) (he' : Continuous e.symm)
    {Aplus : Subring A} {Bplus : Subring B} (hplus : Aplus.map (e : A →+* B) = Bplus) :
    spa Bplus ≃ₜ spa Aplus where
  toFun := spaComap (e : A →+* B) ((RingEquiv.coe_toRingHom e).symm ▸ he) Aplus Bplus
    fun a ha ↦ hplus ▸ ⟨a, ha, rfl⟩
  invFun := spaComap (e.symm : B →+* A) ((RingEquiv.coe_toRingHom e.symm).symm ▸ he') Bplus Aplus
    fun b hb ↦ (congr_fun (RingEquiv.coe_toRingHom e.symm) b).symm ▸
      Subring.mem_map_equiv.mp (hplus ▸ hb)
  left_inv := spaComap_spaComap (e.symm : B →+* A) ((RingEquiv.coe_toRingHom e.symm).symm ▸ he')
    (fun b hb ↦ (congr_fun (RingEquiv.coe_toRingHom e.symm) b).symm ▸
      Subring.mem_map_equiv.mp (hplus ▸ hb))
    (e : A →+* B) ((RingEquiv.coe_toRingHom e).symm ▸ he) e.apply_symm_apply
    fun a ha ↦ hplus ▸ ⟨a, ha, rfl⟩
  right_inv := spaComap_spaComap (e : A →+* B) ((RingEquiv.coe_toRingHom e).symm ▸ he)
    (fun a ha ↦ hplus ▸ ⟨a, ha, rfl⟩)
    (e.symm : B →+* A) ((RingEquiv.coe_toRingHom e.symm).symm ▸ he') e.symm_apply_apply
    fun b hb ↦ (congr_fun (RingEquiv.coe_toRingHom e.symm) b).symm ▸
      Subring.mem_map_equiv.mp (hplus ▸ hb)
  continuous_toFun := continuous_spaComap (e : A →+* B) ((RingEquiv.coe_toRingHom e).symm ▸ he)
    Aplus Bplus _
  continuous_invFun := continuous_spaComap (e.symm : B →+* A)
    ((RingEquiv.coe_toRingHom e.symm).symm ▸ he') Bplus Aplus _

/-- `spaHomeomorphOfRingEquiv` evaluates on points as `spaComap` along `e`. -/
@[simp]
theorem spaHomeomorphOfRingEquiv_apply (e : A ≃+* B) (he : Continuous e)
    (he' : Continuous e.symm) {Aplus : Subring A} {Bplus : Subring B}
    (hplus : Aplus.map (e : A →+* B) = Bplus) (v : spa Bplus) :
    spaHomeomorphOfRingEquiv e he he' hplus v =
      spaComap (e : A →+* B) ((RingEquiv.coe_toRingHom e).symm ▸ he) Aplus Bplus
        (fun a ha ↦ hplus ▸ ⟨a, ha, rfl⟩) v :=
  (rfl)

/-- As a function, `spaHomeomorphOfRingEquiv` is `spaComap` along `e`. -/
@[simp]
theorem coe_spaHomeomorphOfRingEquiv (e : A ≃+* B) (he : Continuous e)
    (he' : Continuous e.symm) {Aplus : Subring A} {Bplus : Subring B}
    (hplus : Aplus.map (e : A →+* B) = Bplus) :
    ⇑(spaHomeomorphOfRingEquiv e he he' hplus) =
      spaComap (e : A →+* B) ((RingEquiv.coe_toRingHom e).symm ▸ he) Aplus Bplus
        fun a ha ↦ hplus ▸ ⟨a, ha, rfl⟩ :=
  (rfl)

/-- The underlying valuation of `spaHomeomorphOfRingEquiv e … v` is `comap e v`. -/
theorem spaHomeomorphOfRingEquiv_val (e : A ≃+* B) (he : Continuous e)
    (he' : Continuous e.symm) {Aplus : Subring A} {Bplus : Subring B}
    (hplus : Aplus.map (e : A →+* B) = Bplus) (v : spa Bplus) :
    (spaHomeomorphOfRingEquiv e he he' hplus v).1 = comap (e : A →+* B) v.1 := by
  rw [spaHomeomorphOfRingEquiv_apply, spaComap_val]

/-- The inverse of `spaHomeomorphOfRingEquiv` for `e` is `spaHomeomorphOfRingEquiv` for `e.symm`. -/
theorem spaHomeomorphOfRingEquiv_symm (e : A ≃+* B) (he : Continuous e)
    (he' : Continuous e.symm) {Aplus : Subring A} {Bplus : Subring B}
    (hplus : Aplus.map (e : A →+* B) = Bplus)
    (hplus' : Bplus.map (e.symm : B →+* A) = Aplus) :
    (spaHomeomorphOfRingEquiv e he he' hplus).symm =
      spaHomeomorphOfRingEquiv e.symm he' he hplus' :=
  Homeomorph.ext fun _ ↦ rfl

/-- `(spaHomeomorphOfRingEquiv e …).symm` evaluates on points as `spaComap` along `e.symm`. -/
@[simp]
theorem spaHomeomorphOfRingEquiv_symm_apply (e : A ≃+* B) (he : Continuous e)
    (he' : Continuous e.symm) {Aplus : Subring A} {Bplus : Subring B}
    (hplus : Aplus.map (e : A →+* B) = Bplus) (w : spa Aplus) :
    (spaHomeomorphOfRingEquiv e he he' hplus).symm w =
      spaComap (e.symm : B →+* A) ((RingEquiv.coe_toRingHom e.symm).symm ▸ he') Bplus Aplus
        (fun b hb ↦ (congr_fun (RingEquiv.coe_toRingHom e.symm) b).symm ▸
          Subring.mem_map_equiv.mp (hplus ▸ hb)) w :=
  (rfl)

/-- The underlying valuation of `(spaHomeomorphOfRingEquiv e …).symm w` is `comap e.symm w`. -/
theorem spaHomeomorphOfRingEquiv_symm_val (e : A ≃+* B) (he : Continuous e)
    (he' : Continuous e.symm) {Aplus : Subring A} {Bplus : Subring B}
    (hplus : Aplus.map (e : A →+* B) = Bplus) (w : spa Aplus) :
    ((spaHomeomorphOfRingEquiv e he he' hplus).symm w).1 = comap (e.symm : B →+* A) w.1 := by
  rw [spaHomeomorphOfRingEquiv_symm_apply, spaComap_val]

/-- `spaHomeomorphOfRingEquiv` of the identity ring equivalence is the identity homeomorphism. -/
@[simp]
theorem spaHomeomorphOfRingEquiv_refl {Aplus : Subring A}
    (he : Continuous (RingEquiv.refl A)) (he' : Continuous (RingEquiv.refl A).symm)
    (hplus : Aplus.map (RingEquiv.refl A : A →+* A) = Aplus) :
    spaHomeomorphOfRingEquiv (RingEquiv.refl A) he he' hplus =
      Homeomorph.refl (spa Aplus) := by
  ext ⟨v, hv⟩ : 1
  apply Subtype.ext
  rw [spaHomeomorphOfRingEquiv_val, RingEquiv.toRingHom_refl]
  exact congr_fun comap_id v

/-- `spaHomeomorphOfRingEquiv` is contravariantly functorial with respect to `RingEquiv.trans`. -/
theorem spaHomeomorphOfRingEquiv_trans {C : Type w} [CommRing C] [TopologicalSpace C]
    (e₁ : A ≃+* B) (he₁ : Continuous e₁) (he₁' : Continuous e₁.symm)
    (e₂ : B ≃+* C) (he₂ : Continuous e₂) (he₂' : Continuous e₂.symm)
    (he₁₂ : Continuous (e₁.trans e₂)) (he₁₂' : Continuous (e₁.trans e₂).symm)
    {Aplus : Subring A} {Bplus : Subring B} {Cplus : Subring C}
    (h₁ : Aplus.map (e₁ : A →+* B) = Bplus) (h₂ : Bplus.map (e₂ : B →+* C) = Cplus)
    (h₁₂ : Aplus.map (e₁.trans e₂ : A →+* C) = Cplus) :
    spaHomeomorphOfRingEquiv (e₁.trans e₂) he₁₂ he₁₂' h₁₂ =
      (spaHomeomorphOfRingEquiv e₂ he₂ he₂' h₂).trans
        (spaHomeomorphOfRingEquiv e₁ he₁ he₁' h₁) := by
  ext ⟨v, hv⟩ : 1
  apply Subtype.ext
  rw [spaHomeomorphOfRingEquiv_val, Homeomorph.trans_apply, spaHomeomorphOfRingEquiv_val,
    spaHomeomorphOfRingEquiv_val, RingEquiv.toRingHom_trans]
  exact congr_fun (comap_comp (e₁ : A →+* B) (e₂ : B →+* C)) v

/-- **Preimages of rational subsets along a topological ring isomorphism are rational.** -/
theorem spaHomeomorphOfRingEquiv_preimage_mem_spaRationalFamily (e : A ≃+* B) (he : Continuous e)
    (he' : Continuous e.symm) {Aplus : Subring A} {Bplus : Subring B}
    (hplus : Aplus.map (e : A →+* B) = Bplus) {U : Set (spa Aplus)}
    (hU : U ∈ spaRationalFamily Aplus) :
    spaHomeomorphOfRingEquiv e he he' hplus ⁻¹' U ∈ spaRationalFamily Bplus := by
  rw [coe_spaHomeomorphOfRingEquiv]
  refine spaComap_preimage_mem_spaRationalFamily (e : A →+* B) he Aplus Bplus _
    (fun J hJ ↦ ?_) hU
  rw [Ideal.map_eq_image_of_surjective (e : A →+* B) e.surjective]
  exact (IsOpenMap.of_inverse he' e.apply_symm_apply e.symm_apply_apply) J hJ

/-- **Images of rational subsets along a topological ring isomorphism are rational.** -/
theorem spaHomeomorphOfRingEquiv_image_mem_spaRationalFamily (e : A ≃+* B) (he : Continuous e)
    (he' : Continuous e.symm) {Aplus : Subring A} {Bplus : Subring B}
    (hplus : Aplus.map (e : A →+* B) = Bplus) {V : Set (spa Bplus)}
    (hV : V ∈ spaRationalFamily Bplus) :
    spaHomeomorphOfRingEquiv e he he' hplus '' V ∈ spaRationalFamily Aplus := by
  rw [Homeomorph.image_eq_preimage_symm,
    spaHomeomorphOfRingEquiv_symm e he he' hplus (map_symm_eq_of_map_eq e hplus)]
  exact spaHomeomorphOfRingEquiv_preimage_mem_spaRationalFamily e.symm he' he _ hV

-- Not tagged `@[simp]`: `mem_spaRationalFamily_iff` is `@[simp]`, so the left-hand side would
-- fail `simpNF`.
/-- **A subset of `Spa(A, A⁺)` is rational if and only if its preimage under
`spaHomeomorphOfRingEquiv` is rational in `Spa(B, B⁺)`.** -/
theorem spaHomeomorphOfRingEquiv_preimage_mem_spaRationalFamily_iff (e : A ≃+* B)
    (he : Continuous e) (he' : Continuous e.symm) {Aplus : Subring A} {Bplus : Subring B}
    (hplus : Aplus.map (e : A →+* B) = Bplus) {U : Set (spa Aplus)} :
    spaHomeomorphOfRingEquiv e he he' hplus ⁻¹' U ∈ spaRationalFamily Bplus ↔
      U ∈ spaRationalFamily Aplus := by
  refine ⟨fun h ↦ ?_, spaHomeomorphOfRingEquiv_preimage_mem_spaRationalFamily e he he' hplus⟩
  simpa only [Set.image_preimage_eq _ (spaHomeomorphOfRingEquiv e he he' hplus).surjective] using
    spaHomeomorphOfRingEquiv_image_mem_spaRationalFamily e he he' hplus h

/-- **Preimage along `spaHomeomorphOfRingEquiv` bijects `spaRationalFamily A⁺` onto
`spaRationalFamily B⁺`.** -/
theorem bijOn_preimage_spaHomeomorphOfRingEquiv_spaRationalFamily (e : A ≃+* B)
    (he : Continuous e) (he' : Continuous e.symm) {Aplus : Subring A} {Bplus : Subring B}
    (hplus : Aplus.map (e : A →+* B) = Bplus) :
    Set.BijOn (fun U : Set (spa Aplus) ↦ spaHomeomorphOfRingEquiv e he he' hplus ⁻¹' U)
      (spaRationalFamily Aplus) (spaRationalFamily Bplus) := by
  refine ⟨fun _ hU ↦ spaHomeomorphOfRingEquiv_preimage_mem_spaRationalFamily e he he' hplus hU,
    (spaHomeomorphOfRingEquiv e he he' hplus).surjective.preimage_injective.injOn, fun V hV ↦ ?_⟩
  refine ⟨spaHomeomorphOfRingEquiv e he he' hplus '' V,
    spaHomeomorphOfRingEquiv_image_mem_spaRationalFamily e he he' hplus hV, ?_⟩
  exact Set.preimage_image_eq V (spaHomeomorphOfRingEquiv e he he' hplus).injective

/-- **Preimage along `(spaHomeomorphOfRingEquiv e …).symm` bijects `spaRationalFamily B⁺` onto
`spaRationalFamily A⁺`.** -/
theorem bijOn_preimage_spaHomeomorphOfRingEquiv_symm_spaRationalFamily (e : A ≃+* B)
    (he : Continuous e) (he' : Continuous e.symm) {Aplus : Subring A} {Bplus : Subring B}
    (hplus : Aplus.map (e : A →+* B) = Bplus) :
    Set.BijOn (fun V : Set (spa Bplus) ↦ (spaHomeomorphOfRingEquiv e he he' hplus).symm ⁻¹' V)
      (spaRationalFamily Bplus) (spaRationalFamily Aplus) := by
  refine ⟨fun V hV ↦ ?_,
    (spaHomeomorphOfRingEquiv e he he' hplus).symm.surjective.preimage_injective.injOn,
    fun U hU ↦ ⟨spaHomeomorphOfRingEquiv e he he' hplus ⁻¹' U,
      spaHomeomorphOfRingEquiv_preimage_mem_spaRationalFamily e he he' hplus hU, ?_⟩⟩
  · dsimp only
    rw [← Homeomorph.image_eq_preimage_symm]
    exact spaHomeomorphOfRingEquiv_image_mem_spaRationalFamily e he he' hplus hV
  · dsimp only
    rw [← Homeomorph.image_eq_preimage_symm]
    exact Set.image_preimage_eq U (spaHomeomorphOfRingEquiv e he he' hplus).surjective

end TauCeti.ValuationSpectrum

end

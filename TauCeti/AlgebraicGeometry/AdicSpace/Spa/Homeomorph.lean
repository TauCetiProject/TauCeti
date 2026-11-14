/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homeomorph.Defs
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.RationalSubset.Basis
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Homeomorphisms of sub-unit valuation loci from topological ring equivalences

A ring isomorphism `e : A ≃+* B` that is continuous in both directions and carries a subring
`A⁺ ⊆ A` into `B⁺ ⊆ B` while `e.symm` carries `B⁺` into `A⁺` induces a contravariant
homeomorphism of sub-unit valuation loci

```text
spaHomeomorphOfRingEquiv e … : spa B⁺ ≃ₜ spa A⁺
```

whose underlying map is `TauCeti.ValuationSpectrum.spaComap` of `e.toRingHom` and whose inverse is
`spaComap` of `e.symm.toRingHom`. Because `e` is a homeomorphic ring isomorphism, pushing an open
ideal of `A` forward along `e` agrees with pulling it back along `e.symm`, so preimage under the
induced homeomorphism restricts to a bijection between `spaRationalFamily A⁺` and
`spaRationalFamily B⁺`.

No `[IsTopologicalRing]` or `[IsHuberRing]` hypothesis is needed anywhere in this file.

## Main definitions

* `TauCeti.ValuationSpectrum.spaHomeomorphOfRingEquiv`: the contravariant homeomorphism
  `spa B⁺ ≃ₜ spa A⁺` induced by a topological ring equivalence `e : A ≃+* B` identifying `A⁺`
  with `B⁺`.

## Main results

* `TauCeti.ValuationSpectrum.spaHomeomorphOfRingEquiv_apply`,
  `TauCeti.ValuationSpectrum.coe_spaHomeomorphOfRingEquiv`,
  `TauCeti.ValuationSpectrum.spaHomeomorphOfRingEquiv_symm`: underlying maps and symmetry.
* `TauCeti.ValuationSpectrum.spaHomeomorphOfRingEquiv_refl`,
  `TauCeti.ValuationSpectrum.spaHomeomorphOfRingEquiv_trans`: contravariant functoriality with
  respect to identity and composition of ring equivalences.
* `TauCeti.ValuationSpectrum.spaHomeomorphOfRingEquiv_preimage_rationalSubset`: preimage of a
  rational subset `R(T/s)` is `R(e(T)/e(s))`.
* `TauCeti.ValuationSpectrum.spaHomeomorphOfRingEquiv_preimage_mem_spaRationalFamily_iff`,
  `TauCeti.ValuationSpectrum.bijOn_preimage_spaHomeomorphOfRingEquiv_spaRationalFamily`:
  preimage under the homeomorphism preserves and reflects membership in `spaRationalFamily`, giving
  a bijection `spaRationalFamily A⁺ → spaRationalFamily B⁺`.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Remark 7.30(5) and
  Proposition 7.35.
-/

public section

namespace TauCeti.ValuationSpectrum

variable {A B C : Type*} [CommRing A] [TopologicalSpace A] [CommRing B] [TopologicalSpace B]
  [CommRing C] [TopologicalSpace C]

/-- The contravariant homeomorphism `spa B⁺ ≃ₜ spa A⁺` induced by a ring equivalence `e : A ≃+* B`
that is continuous in both directions and identifies `A⁺` with `B⁺`. -/
def spaHomeomorphOfRingEquiv (e : A ≃+* B) (he : Continuous e) (hes : Continuous e.symm)
    (Aplus : Subring A) (Bplus : Subring B) (hplus : ∀ a ∈ Aplus, e a ∈ Bplus)
    (hplus_symm : ∀ b ∈ Bplus, e.symm b ∈ Aplus) :
    spa Bplus ≃ₜ spa Aplus where
  toFun := spaComap e.toRingHom he Aplus Bplus hplus
  invFun := spaComap e.symm.toRingHom hes Bplus Aplus hplus_symm
  left_inv := spaComap_spaComap e.symm.toRingHom hes hplus_symm e.toRingHom he
    e.apply_symm_apply hplus
  right_inv := spaComap_spaComap e.toRingHom he hplus e.symm.toRingHom hes
    e.symm_apply_apply hplus_symm
  continuous_toFun := continuous_spaComap e.toRingHom he Aplus Bplus hplus
  continuous_invFun := continuous_spaComap e.symm.toRingHom hes Bplus Aplus hplus_symm

/-- `spaHomeomorphOfRingEquiv` acts on points as `spaComap` along `e.toRingHom`. -/
@[simp]
theorem spaHomeomorphOfRingEquiv_apply (e : A ≃+* B) (he : Continuous e) (hes : Continuous e.symm)
    (Aplus : Subring A) (Bplus : Subring B) (hplus : ∀ a ∈ Aplus, e a ∈ Bplus)
    (hplus_symm : ∀ b ∈ Bplus, e.symm b ∈ Aplus) (v : spa Bplus) :
    spaHomeomorphOfRingEquiv e he hes Aplus Bplus hplus hplus_symm v =
      spaComap e.toRingHom he Aplus Bplus hplus v := (rfl)

/-- As a function, `spaHomeomorphOfRingEquiv` is `spaComap` along `e.toRingHom`. -/
@[simp]
theorem coe_spaHomeomorphOfRingEquiv (e : A ≃+* B) (he : Continuous e) (hes : Continuous e.symm)
    (Aplus : Subring A) (Bplus : Subring B) (hplus : ∀ a ∈ Aplus, e a ∈ Bplus)
    (hplus_symm : ∀ b ∈ Bplus, e.symm b ∈ Aplus) :
    ⇑(spaHomeomorphOfRingEquiv e he hes Aplus Bplus hplus hplus_symm) =
      spaComap e.toRingHom he Aplus Bplus hplus := (rfl)

/-- The inverse of `spaHomeomorphOfRingEquiv e` is `spaHomeomorphOfRingEquiv e.symm`. -/
@[simp]
theorem spaHomeomorphOfRingEquiv_symm (e : A ≃+* B) (he : Continuous e) (hes : Continuous e.symm)
    (Aplus : Subring A) (Bplus : Subring B) (hplus : ∀ a ∈ Aplus, e a ∈ Bplus)
    (hplus_symm : ∀ b ∈ Bplus, e.symm b ∈ Aplus) :
    (spaHomeomorphOfRingEquiv e he hes Aplus Bplus hplus hplus_symm).symm =
      spaHomeomorphOfRingEquiv e.symm hes he Bplus Aplus hplus_symm hplus := (rfl)

/-- The underlying valuation in `Spv A` of `spaHomeomorphOfRingEquiv e … v` is `comap e.toRingHom`
of `v.1`. -/
theorem spaHomeomorphOfRingEquiv_val (e : A ≃+* B) (he : Continuous e) (hes : Continuous e.symm)
    (Aplus : Subring A) (Bplus : Subring B) (hplus : ∀ a ∈ Aplus, e a ∈ Bplus)
    (hplus_symm : ∀ b ∈ Bplus, e.symm b ∈ Aplus) (v : spa Bplus) :
    (spaHomeomorphOfRingEquiv e he hes Aplus Bplus hplus hplus_symm v).1 =
      comap e.toRingHom v.1 :=
  spaComap_val e.toRingHom he Aplus Bplus hplus v

/-- `spaHomeomorphOfRingEquiv` of `RingEquiv.refl` is `Homeomorph.refl`. -/
@[simp]
theorem spaHomeomorphOfRingEquiv_refl (Aplus : Subring A)
    (he : Continuous (RingEquiv.refl A)) (hes : Continuous (RingEquiv.refl A).symm)
    (hplus : ∀ a ∈ Aplus, RingEquiv.refl A a ∈ Aplus)
    (hplus_symm : ∀ a ∈ Aplus, (RingEquiv.refl A).symm a ∈ Aplus) :
    spaHomeomorphOfRingEquiv (RingEquiv.refl A) he hes Aplus Aplus hplus hplus_symm =
      Homeomorph.refl (spa Aplus) := by
  refine Homeomorph.ext fun v ↦ Subtype.ext ?_
  rw [spaHomeomorphOfRingEquiv_val, Homeomorph.refl_apply]
  exact congr_fun comap_id v.1

/-- `spaHomeomorphOfRingEquiv` is contravariantly functorial for composition of ring
equivalences. -/
theorem spaHomeomorphOfRingEquiv_trans (e : A ≃+* B) (e' : B ≃+* C) (he : Continuous e)
    (hes : Continuous e.symm) (he' : Continuous e') (he's : Continuous e'.symm)
    (he_trans : Continuous (e.trans e')) (hes_trans : Continuous (e.trans e').symm)
    (Aplus : Subring A) (Bplus : Subring B) (Cplus : Subring C)
    (hAB : ∀ a ∈ Aplus, e a ∈ Bplus) (hBA : ∀ b ∈ Bplus, e.symm b ∈ Aplus)
    (hBC : ∀ b ∈ Bplus, e' b ∈ Cplus) (hCB : ∀ c ∈ Cplus, e'.symm c ∈ Bplus)
    (hAC : ∀ a ∈ Aplus, e.trans e' a ∈ Cplus)
    (hCA : ∀ c ∈ Cplus, (e.trans e').symm c ∈ Aplus) :
    spaHomeomorphOfRingEquiv (e.trans e') he_trans hes_trans Aplus Cplus hAC hCA =
      (spaHomeomorphOfRingEquiv e' he' he's Bplus Cplus hBC hCB).trans
        (spaHomeomorphOfRingEquiv e he hes Aplus Bplus hAB hBA) := by
  refine Homeomorph.ext fun v ↦ Subtype.ext ?_
  rw [spaHomeomorphOfRingEquiv_val, Homeomorph.trans_apply, spaHomeomorphOfRingEquiv_val,
    spaHomeomorphOfRingEquiv_val]
  exact congr_fun (comap_comp e.toRingHom e'.toRingHom) v.1

open scoped Classical in
/-- Preimage of a rational subset `R(T/s)` under `spaHomeomorphOfRingEquiv e` is
`R(e(T)/e(s))`. -/
theorem spaHomeomorphOfRingEquiv_preimage_rationalSubset (e : A ≃+* B) (he : Continuous e)
    (hes : Continuous e.symm) (Aplus : Subring A) (Bplus : Subring B)
    (hplus : ∀ a ∈ Aplus, e a ∈ Bplus) (hplus_symm : ∀ b ∈ Bplus, e.symm b ∈ Aplus)
    (T : Finset A) (s : A) :
    spaHomeomorphOfRingEquiv e he hes Aplus Bplus hplus hplus_symm ⁻¹'
        (Subtype.val ⁻¹' rationalSubset Aplus T s) =
      Subtype.val ⁻¹' rationalSubset Bplus (T.image e.toRingHom) (e s) :=
  spaComap_preimage_rationalSubset e.toRingHom he Aplus Bplus hplus T s

/-- Preimage under `spaHomeomorphOfRingEquiv` carries members of `spaRationalFamily A⁺` to
members of `spaRationalFamily B⁺`. -/
theorem spaHomeomorphOfRingEquiv_preimage_mem_spaRationalFamily (e : A ≃+* B) (he : Continuous e)
    (hes : Continuous e.symm) (Aplus : Subring A) (Bplus : Subring B)
    (hplus : ∀ a ∈ Aplus, e a ∈ Bplus) (hplus_symm : ∀ b ∈ Bplus, e.symm b ∈ Aplus)
    {U : Set (spa Aplus)} (hU : U ∈ spaRationalFamily Aplus) :
    spaHomeomorphOfRingEquiv e he hes Aplus Bplus hplus hplus_symm ⁻¹' U ∈
      spaRationalFamily Bplus := by
  refine spaComap_preimage_mem_spaRationalFamily e.toRingHom he Aplus Bplus hplus
    (fun J hJ ↦ ?_) hU
  rw [RingEquiv.toRingHom_eq_coe, Ideal.map_comap_of_equiv, Ideal.coe_comap]
  exact hJ.preimage hes

/-- Preimage under `spaHomeomorphOfRingEquiv` preserves and reflects membership in
`spaRationalFamily`. -/
theorem spaHomeomorphOfRingEquiv_preimage_mem_spaRationalFamily_iff (e : A ≃+* B)
    (he : Continuous e) (hes : Continuous e.symm) (Aplus : Subring A) (Bplus : Subring B)
    (hplus : ∀ a ∈ Aplus, e a ∈ Bplus) (hplus_symm : ∀ b ∈ Bplus, e.symm b ∈ Aplus)
    {U : Set (spa Aplus)} :
    spaHomeomorphOfRingEquiv e he hes Aplus Bplus hplus hplus_symm ⁻¹' U ∈
        spaRationalFamily Bplus ↔
      U ∈ spaRationalFamily Aplus := by
  refine ⟨fun hV ↦ ?_,
    spaHomeomorphOfRingEquiv_preimage_mem_spaRationalFamily e he hes Aplus Bplus hplus hplus_symm⟩
  have hU := spaHomeomorphOfRingEquiv_preimage_mem_spaRationalFamily e.symm hes he Bplus Aplus
    hplus_symm hplus hV
  rwa [← spaHomeomorphOfRingEquiv_symm, ← Set.preimage_comp, Homeomorph.self_comp_symm,
    Set.preimage_id] at hU

/-- Image under `spaHomeomorphOfRingEquiv` preserves and reflects membership in
`spaRationalFamily`. -/
theorem spaHomeomorphOfRingEquiv_image_mem_spaRationalFamily_iff (e : A ≃+* B)
    (he : Continuous e) (hes : Continuous e.symm) (Aplus : Subring A) (Bplus : Subring B)
    (hplus : ∀ a ∈ Aplus, e a ∈ Bplus) (hplus_symm : ∀ b ∈ Bplus, e.symm b ∈ Aplus)
    {V : Set (spa Bplus)} :
    spaHomeomorphOfRingEquiv e he hes Aplus Bplus hplus hplus_symm '' V ∈
        spaRationalFamily Aplus ↔
      V ∈ spaRationalFamily Bplus := by
  rw [(spaHomeomorphOfRingEquiv e he hes Aplus Bplus hplus hplus_symm).image_eq_preimage_symm,
    spaHomeomorphOfRingEquiv_symm]
  exact spaHomeomorphOfRingEquiv_preimage_mem_spaRationalFamily_iff e.symm hes he Bplus Aplus
    hplus_symm hplus

/-- Preimage under `spaHomeomorphOfRingEquiv` is a bijection from `spaRationalFamily A⁺` onto
`spaRationalFamily B⁺`. -/
theorem bijOn_preimage_spaHomeomorphOfRingEquiv_spaRationalFamily (e : A ≃+* B) (he : Continuous e)
    (hes : Continuous e.symm) (Aplus : Subring A) (Bplus : Subring B)
    (hplus : ∀ a ∈ Aplus, e a ∈ Bplus) (hplus_symm : ∀ b ∈ Bplus, e.symm b ∈ Aplus) :
    Set.BijOn
      (fun U : Set (spa Aplus) ↦
        spaHomeomorphOfRingEquiv e he hes Aplus Bplus hplus hplus_symm ⁻¹' U)
      (spaRationalFamily Aplus) (spaRationalFamily Bplus) := by
  set H := spaHomeomorphOfRingEquiv e he hes Aplus Bplus hplus hplus_symm
  refine ⟨fun U hU ↦ spaHomeomorphOfRingEquiv_preimage_mem_spaRationalFamily e he hes Aplus Bplus
      hplus hplus_symm hU,
    H.surjective.preimage_injective.injOn, fun V hV ↦ ⟨H.symm ⁻¹' V, ?_, ?_⟩⟩
  · exact spaHomeomorphOfRingEquiv_preimage_mem_spaRationalFamily e.symm hes he Bplus Aplus
      hplus_symm hplus hV
  · dsimp only
    rw [← Set.preimage_comp, H.symm_comp_self, Set.preimage_id]

end TauCeti.ValuationSpectrum

end

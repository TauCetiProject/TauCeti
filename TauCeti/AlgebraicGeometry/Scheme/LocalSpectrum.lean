/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.AlgebraicGeometry.Properties

/-!
# Local rings on the spectrum of a stalk

The canonical map `Spec 𝒪_{X,x} ⟶ X` identifies local rings at corresponding points.
Consequently the height of a prime of `𝒪_{X,x}` is the local dimension at its image in `X`.
Together with `Scheme.range_fromSpecStalk`, this identifies height-one primes of a stalk
with codimension-one generizations of its point, as needed to pass between local algebra
and pointwise ramification conditions.

The local-ring comparison uses Mathlib's
`isIso_specMap_stalkMap_localization` on an affine neighbourhood.

If a morphism `f` maps every point to `x`, every open neighbourhood of `x` pulls back to the whole
source (`Scheme.Hom.top_le_preimage`), and a section whose basic open misses `x` pulls back to a
global section with empty basic open (`Scheme.Hom.basicOpen_appLE_eq_bot`).
Pulling sections back along `Spec 𝒪_{Y,y} ⟶ Y` takes germs at `y`
(`Scheme.Hom.fromSpecStalk_comp_appLE`). Hence if a morphism `f` is constant on the generizations
of `y`, the germ at `y` of the pullback of a section vanishing at `f y` is nilpotent
(`Scheme.Hom.isNilpotent_germ_app`), and a section with nilpotent germ at `y` vanishes on a
neighbourhood of `y` (`Scheme.notMem_closure_basicOpen_of_isNilpotent_germ`).
-/

public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

/-- The spectrum of a stalk has the same local rings as the ambient scheme at corresponding
points. No Noetherianity hypothesis is needed. -/
instance isIso_stalkMap_fromSpecStalk (X : Scheme.{u}) (x : X)
    (q : Spec (X.presheaf.stalk x)) : IsIso ((X.fromSpecStalk x).stalkMap q) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  replace hU : IsAffineOpen U := hU
  let := X.presheaf.algebra_section_stalk ⟨x, hxU⟩
  have := hU.isLocalization_stalk ⟨x, hxU⟩
  let p := (hU.primeIdealOf ⟨x, hxU⟩).asIdeal
  let e := IsLocalization.algEquiv p.primeCompl (Localization p.primeCompl)
    (X.presheaf.stalk x)
  have hg : X.presheaf.germ U x hxU =
      CommRingCat.ofHom (algebraMap Γ(X, U) (Localization p.primeCompl)) ≫
        e.toRingEquiv.toCommRingCatIso.hom := by
    ext r
    exact (e.commutes r).symm
  have heq : X.fromSpecStalk x = Spec.map (X.presheaf.germ U x hxU) ≫ hU.fromSpec :=
    (hU.fromSpecStalk_eq_fromSpecStalk hxU).symm
  rw [heq, hg, Spec.map_comp, Scheme.Hom.stalkMap_comp]
  have hloc : IsIso ((Spec.map (CommRingCat.ofHom
      (algebraMap Γ(X, U) (Localization p.primeCompl)))).stalkMap
        (Spec.map e.toRingEquiv.toCommRingCatIso.hom q)) :=
    isIso_specMap_stalkMap_localization _ _ _
  rw [Scheme.Hom.stalkMap_comp]
  apply IsIso.comp_isIso'
  · -- The composition step unfolds stalk-map wrappers; instance search needs the
    -- scheme-level form to recognize the open immersion `hU.fromSpec`.
    exact inferInstanceAs (IsIso (hU.fromSpec.stalkMap _))
  · exact IsIso.comp_isIso' hloc inferInstance

/-- The height of a prime in a stalk equals the local dimension of its image in the scheme. -/
theorem height_eq_ringKrullDim_fromSpecStalk (X : Scheme.{u}) (x : X)
    (q : Spec (X.presheaf.stalk x)) :
    (q.asIdeal.height : WithBot ℕ∞) =
      ringKrullDim (X.presheaf.stalk (X.fromSpecStalk x q)) := by
  rw [idealHeight_eq_coheight, ← ringKrullDim_stalk_eq_coheight]
  exact (ringKrullDim_eq_of_ringEquiv
    (asIso ((X.fromSpecStalk x).stalkMap q)).commRingCatIsoToRingEquiv).symm

/-- If the germ at `y` of a section `t` is nilpotent, then `t` vanishes on a neighbourhood of `y`,
so `y` is not in the closure of the basic open of `t`. -/
theorem notMem_closure_basicOpen_of_isNilpotent_germ {Y : Scheme.{u}} {W : Y.Opens} {y : Y}
    (hy : y ∈ W) {t : Γ(Y, W)} (h : IsNilpotent (Y.presheaf.germ W y hy t)) :
    y ∉ closure (Y.basicOpen t : Set Y) := by
  obtain ⟨n, hn⟩ := h
  -- Some power `t ^ (n + 1)` restricts to zero on an open neighbourhood `V ⊆ W` of `y`.
  obtain ⟨V, hyV, iVW, _, hV⟩ := Y.presheaf.germ_eq y hy hy (t ^ (n + 1)) 0
    (by rw [map_pow, pow_succ, hn, zero_mul, map_zero])
  rw [mem_closure_iff]
  push Not
  -- On `V`, the basic open of `t` agrees with that of the zero section, which is empty.
  refine ⟨V, V.isOpen, hyV, Set.eq_empty_iff_forall_notMem.mpr fun z ⟨hzV, hz⟩ ↦ ?_⟩
  have : z ∈ Y.basicOpen (Y.presheaf.map iVW.op (t ^ (n + 1))) := by
    rw [Scheme.basicOpen_res, Scheme.basicOpen_pow _ _ n.succ_pos]
    exact ⟨hzV, hz⟩
  rw [hV, map_zero, Scheme.basicOpen_zero] at this
  simp at this

namespace Hom

variable {X Y : Scheme.{u}} (f : Y ⟶ X)

/-- If `f` maps every point to `x`, the preimage of any open neighbourhood of `x` is everything. -/
theorem top_le_preimage {x : X} (hf : ∀ y, f y = x) {U : X.Opens} (hxU : x ∈ U) :
    ⊤ ≤ f ⁻¹ᵁ U :=
  fun y _ ↦ f.mem_preimage.mpr (hf y ▸ hxU)

/-- If `f` maps every point to `x` and the basic open of `s` misses `x`, the pullback of `s` to
the global sections of `Y` has empty basic open. -/
theorem basicOpen_appLE_eq_bot {x : X} (hf : ∀ y, f y = x) {U : X.Opens} (e : ⊤ ≤ f ⁻¹ᵁ U)
    {s : Γ(X, U)} (hs : x ∉ X.basicOpen s) : Y.basicOpen (f.appLE U ⊤ e s) = ⊥ := by
  rw [Scheme.basicOpen_appLE, eq_bot_iff]
  rintro y ⟨-, hy⟩
  exact hs (hf y ▸ hy)

/-- The pullback of a section `s` along `Spec 𝒪_{Y,y} ⟶ Y ⟶ X` is the image of the germ at `y`
of the pullback of `s` under `Γ(Spec 𝒪_{Y,y}, ⊤) ≅ 𝒪_{Y,y}`. -/
theorem fromSpecStalk_comp_appLE {y : Y} {U : X.Opens} (hy : y ∈ f ⁻¹ᵁ U)
    (e : ⊤ ≤ (Y.fromSpecStalk y ≫ f) ⁻¹ᵁ U) :
    (Y.fromSpecStalk y ≫ f).appLE U ⊤ e =
      f.app U ≫ Y.presheaf.germ (f ⁻¹ᵁ U) y hy ≫ (Scheme.ΓSpecIso _).inv := by
  rw [comp_appLE]
  simp only [Hom.appLE, fromSpecStalk_app hy, Category.assoc, ← Functor.map_comp]
  -- The two restrictions compose to an endomorphism of an open of `Spec 𝒪_{Y,y}`; as the opens
  -- form a poset, it is the identity.
  rw [Subsingleton.elim (_ ≫ _) (𝟙 _), CategoryTheory.Functor.map_id, Category.comp_id]

/-- If `f` maps every generization of `y` to `f y`, then for a section `s` near `f y` whose basic
open misses `f y`, the germ at `y` of the pullback of `s` is nilpotent. -/
theorem isNilpotent_germ_app {y : Y} (hgen : ∀ y', y' ⤳ y → f y' = f y) {U : X.Opens}
    (hy : y ∈ f ⁻¹ᵁ U) {s : Γ(X, U)} (hs : f y ∉ X.basicOpen s) :
    IsNilpotent (Y.presheaf.germ (f ⁻¹ᵁ U) y hy (f.app U s)) := by
  -- The composite `Spec 𝒪_{Y,y} ⟶ Y ⟶ X` maps every point to `f y`.
  have hg (z : Spec (Y.presheaf.stalk y)) : (Y.fromSpecStalk y ≫ f) z = f y := by
    rw [Scheme.Hom.comp_apply]
    refine hgen _ ?_
    have := Set.mem_range_self (f := Y.fromSpecStalk y) z
    rwa [range_fromSpecStalk] at this
  have e := top_le_preimage _ hg (f.mem_preimage.mp hy)
  -- Hence the pullback of `s` to `Spec 𝒪_{Y,y}` has empty basic open.
  have h0 := basicOpen_appLE_eq_bot _ hg e hs
  rw [fromSpecStalk_comp_appLE f hy, CommRingCat.comp_apply, CommRingCat.comp_apply,
    basicOpen_eq_of_affine] at h0
  exact (PrimeSpectrum.basicOpen_eq_bot_iff _).mp h0

end Hom

end AlgebraicGeometry.Scheme

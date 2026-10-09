/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.SchemeTheoreticallyDominant
public import TauCeti.RingTheory.GradedAlgebra.HomogeneousLocalization.Basic
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper

/-!
# Global sections of `Proj` from a weakly regular sequence of two homogeneous elements

Let `A` be an `ℕ`-graded ring and let `f` and `g` be homogeneous elements of positive degree that
form a weakly regular sequence `[f, g]` in `A`. Then every global section of the structure sheaf of
`Proj A` comes from the degree-zero part `A₀`: the structure morphism `Proj A ⟶ Spec A₀` induces
an isomorphism `A₀ ≅ Γ(Proj A, 𝒪)` on global sections.

A global section restricts to `a / fⁿ` on the standard chart `D₊(f)` and to `b / gᵏ` on `D₊(g)`.
The two restrictions agree on `D₊(fg)`, which forces `fⁿ ∣ a` by the weak regularity of `[f, g]`
(`HomogeneousLocalization.Away.mem_range_fromZeroRingHom_of_awayMap_eq`), so the restriction to
`D₊(f)` comes from `A₀`. As `f` is a nonzerodivisor, `D₊(f)` is scheme-theoretically dense in
`Proj A` (`AlgebraicGeometry.Proj.isSchemeTheoreticallyDominant_awayι`), and a global section is
determined by its restriction to `D₊(f)`. No assumption is made that `D₊(f)` and `D₊(g)` cover
`Proj A`.

For instance, the projective Weierstrass cubic over a ring `R` satisfies the hypothesis with
`f = Z` and `g = Y`, so its only global functions are the constants in `R`.

## Main results

* `AlgebraicGeometry.Proj.isIso_appTop_toSpecZero`: if `[f, g]` is a weakly regular sequence of
  homogeneous elements of positive degree, then `Proj.toSpecZero` induces an isomorphism on global
  sections.
-/

public section

open CategoryTheory HomogeneousLocalization

namespace AlgebraicGeometry.Proj

variable {σ A : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- On the standard chart `D₊(f)`, read through `Γ(Spec A_{(f)}) ≅ A_{(f)}`, the global sections of
`Proj A` pulled back from `Spec A₀` are the fractions with denominator `1`. -/
theorem appTop_toSpecZero_awayι_appTop_ΓSpecIso_hom {f : A} {d : ℕ} (hf : f ∈ 𝒜 d) (hd : 0 < d) :
    (toSpecZero 𝒜).appTop ≫ (awayι 𝒜 f hf hd).appTop ≫ (Scheme.ΓSpecIso _).hom =
      (Scheme.ΓSpecIso _).hom ≫ CommRingCat.ofHom (fromZeroRingHom 𝒜 _) := by
  rw [← Category.assoc, ← Scheme.Hom.comp_appTop, awayι_toSpecZero, Scheme.ΓSpecIso_naturality]

/-- Restricting a global section of `Proj A` to `D₊(f)` and then to `D₊(fg)` is restricting it to
`D₊(fg)`, read through `Γ(Spec A_{(f)}) ≅ A_{(f)}` and `Γ(Spec A_{(fg)}) ≅ A_{(fg)}`. -/
theorem awayMap_ΓSpecIso_hom_awayι_appTop {f g x : A} {d e : ℕ} (hf : f ∈ 𝒜 d) (hd : 0 < d)
    (hg : g ∈ 𝒜 e) (hx : x = f * g) (s : Γ(Proj 𝒜, ⊤)) :
    awayMap 𝒜 hg hx ((Scheme.ΓSpecIso _).hom ((awayι 𝒜 f hf hd).appTop s)) =
      (Scheme.ΓSpecIso _).hom ((awayι 𝒜 x (hx ▸ SetLike.mul_mem_graded hf hg)
        (hd.trans_le (d.le_add_right e))).appTop s) := by
  rw [← SpecMap_awayMap_awayι 𝒜 hf hd hg hx, Scheme.Hom.comp_appTop]
  exact congr($(Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (awayMap 𝒜 hg hx)))
    ((awayι 𝒜 f hf hd).appTop s)).symm

/-- **The global sections of `Proj A` are `A₀`** when `A` has a weakly regular sequence `[f, g]` of
homogeneous elements of positive degree: the structure morphism `Proj A ⟶ Spec A₀` induces an
isomorphism `A₀ ≅ Γ(Proj A, 𝒪)` on global sections. -/
theorem isIso_appTop_toSpecZero {f g : A} {d e : ℕ} (hf : f ∈ 𝒜 d) (hg : g ∈ 𝒜 e) (hd : 0 < d)
    (he : 0 < e) (hfg : RingTheory.Sequence.IsWeaklyRegular A [f, g]) :
    IsIso (toSpecZero 𝒜).appTop := by
  have hf₀ := (RingTheory.Sequence.isWeaklyRegular_pair_iff.mp hfg).1
  have := isSchemeTheoreticallyDominant_awayι 𝒜 hf hd hf₀
  -- a global section is determined by its restriction to the dense chart `D₊(f)`
  have hinj : Function.Injective fun s ↦ (Scheme.ΓSpecIso _).hom ((awayι 𝒜 f hf hd).appTop s) :=
    (Scheme.ΓSpecIso _).commRingCatIsoToRingEquiv.injective.comp
      ((awayι 𝒜 f hf hd).app_injective ⊤)
  have key (c) : (Scheme.ΓSpecIso _).hom ((awayι 𝒜 f hf hd).appTop ((toSpecZero 𝒜).appTop c)) =
      fromZeroRingHom 𝒜 _ ((Scheme.ΓSpecIso _).hom c) :=
    congr($(appTop_toSpecZero_awayι_appTop_ΓSpecIso_hom 𝒜 hf hd) c)
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨fun c c' hcc' ↦ ?_, fun s ↦ ?_⟩
  · -- `A₀ → A_{(f)}` is injective, as `f` is a nonzerodivisor
    have := congrArg (fun s ↦ (Scheme.ΓSpecIso _).hom ((awayι 𝒜 f hf hd).appTop s)) hcc'
    simp only [key] at this
    exact (Scheme.ΓSpecIso _).commRingCatIsoToRingEquiv.injective
      (fromZeroRingHom_injective 𝒜 (Submonoid.powers_le.mpr hf₀) this)
  · -- the restrictions of `s` to `D₊(f)` and `D₊(g)` agree on `D₊(fg)`, so the first comes
    -- from `A₀`
    have h := (awayMap_ΓSpecIso_hom_awayι_appTop 𝒜 hf hd hg rfl s).trans
      (awayMap_ΓSpecIso_hom_awayι_appTop 𝒜 hg he hf (mul_comm f g) s).symm
    obtain ⟨c, hc⟩ := Away.mem_range_fromZeroRingHom_of_awayMap_eq 𝒜 hf hg hfg h
    refine ⟨(Scheme.ΓSpecIso _).inv c, hinj ?_⟩
    simp only [key, Iso.inv_hom_id_apply, hc]

end AlgebraicGeometry.Proj

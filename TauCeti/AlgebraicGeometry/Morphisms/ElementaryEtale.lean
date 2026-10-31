/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.Tactic.Algebraize
import TauCeti.AlgebraicGeometry.Morphisms.Finite.AffineChart
import TauCeti.AlgebraicGeometry.ResidueField
import TauCeti.RingTheory.Etale.QuasiFinite

/-!
# Elementary étale neighbourhoods of a quasi-finite point

An *elementary étale neighbourhood* of a point `s` of a scheme `S` is an étale morphism
`φ : U ⟶ S` together with a point `u` of `U` such that `φ u = s` and `φ` induces an isomorphism
of residue fields `κ(s) ≅ κ(u)`.

Let `f : X ⟶ S` be locally of finite type and quasi-finite at `x`, that is, `x` is isolated in its
fibre. After base change to a suitable elementary étale neighbourhood `(U, u)` of `f x`, the point
`x` splits off: there is an open `V` of `X ×[S] U`, finite over `U`, containing exactly one point
`v` over `u`; this point lies over `x`, and `κ(x) ≅ κ(v)`
(`AlgebraicGeometry.Scheme.Hom.exists_elementaryEtale_finite_of_isolated`, Stacks, Lemma 37.41.1
(02LK)). This is the form of étale localization through which a statement about a quasi-finite
morphism at a point is reduced to one about a finite morphism with a single point over the base
point, as in the proof of purity of the branch locus (Stacks, Lemma 58.21.4 (0BMB)).

## Implementation notes

The construction is that of Mathlib's `AlgebraicGeometry.exists_etale_isCompl_of_quasiFiniteAt`
(Andrew Yang), which proves the finiteness statement on its way to Zariski's main theorem. There
`f` is assumed separated so that the open is also closed; that conclusion is not needed here, and
neither is separatedness. The chart is
`AlgebraicGeometry.exists_isOpenImmersion_tensor_isFinite`, and the affine input is
Mathlib's `Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq` (Stacks 00UJ), whose
additional conclusions give the residue field isomorphism at `u`, the uniqueness of `v`, and,
through `Ideal.ResidueField.bijective_map_includeRight`, the residue field isomorphism at `v`.

The Stacks lemma adds that the conclusion persists under further elementary étale neighbourhoods
of `(U, u)`; that persistence is not proved here.

## References

* [Stacks Project, Lemma 37.41.1](https://stacks.math.columbia.edu/tag/02LK)
* [Stacks Project, Tag 00UJ](https://stacks.math.columbia.edu/tag/00UJ)
-/

public section

open CategoryTheory Limits TensorProduct

namespace AlgebraicGeometry

universe u

/-- **Elementary étale localization of a quasi-finite point** (Stacks, Lemma 37.41.1 (02LK)).
Let `f : X ⟶ S` be locally of finite type and quasi-finite at `x` (so `x` is isolated in its
fibre). Then there are an étale `φ : U ⟶ S` and `u : U` with `φ u = f x` and `κ(f x) ≅ κ(u)`, and
an open `V` of `X ×[S] U`, finite over `U`, containing a point `v` over `x` and `u` with
`κ(x) ≅ κ(v)`, which is the only point of `V` over `u`.

The persistence clause of 02LK, that the conclusion survives further elementary étale
neighbourhoods of `(U, u)`, is not included. -/
@[stacks 02LK "without the persistence clause"]
theorem Scheme.Hom.exists_elementaryEtale_finite_of_isolated {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] {x : X} (hx : f.QuasiFiniteAt x) :
    ∃ (U : Scheme.{u}) (φ : U ⟶ S) (u : U), Etale φ ∧ φ u = f x ∧ IsIso (φ.residueFieldMap u) ∧
      ∃ (V : (pullback f φ).Opens) (v : V), IsFinite (V.ι ≫ pullback.snd f φ) ∧
        pullback.fst f φ v = x ∧ pullback.snd f φ v = u ∧
        IsIso ((pullback.fst f φ).residueFieldMap v) ∧
        ∀ w : V, pullback.snd f φ w = u → w = v := by
  -- Step 1: affine charts `x ∈ V ⊆ f⁻¹ U`, and Stacks 00UJ for `Γ(S, U) → Γ(X, V)` at `x`. It gives
  -- an étale `Γ(S, U)`-algebra `R` with a prime `P` over `f x` and `κ(f x) = κ(P)`, and an
  -- idempotent `e` of `R ⊗ Γ(X, V)` cutting out a factor finite over `R` with a unique prime `P'`
  -- over `P`, which lies over `x`.
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hUV : V ≤ f ⁻¹ᵁ U⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxU (f ⁻¹ᵁ U).2
  replace hU : IsAffineOpen U := hU
  replace hV : IsAffineOpen V := hV
  have : (f.appLE U V hUV).hom.FiniteType := f.finiteType_appLE hU hV hUV
  algebraize [(f.appLE U V hUV).hom]
  have : (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.LiesOver (hU.primeIdealOf ⟨f x, hxU⟩).asIdeal :=
    ⟨congr(($(IsAffineOpen.comap_primeIdealOf_appLE U hU V hV hUV hxV)).asIdeal).symm⟩
  have : Algebra.QuasiFiniteAt Γ(S, U) (hV.primeIdealOf ⟨x, hxV⟩).asIdeal :=
    hx.quasiFiniteAt hV hU hUV hxV
  obtain ⟨R, _, _, _, P, _, _, e, _, P', _, _, hP', heP', hres, _, huniq⟩ :=
    Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq
    (hU.primeIdealOf ⟨f x, hxU⟩).asIdeal (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
  -- Step 2: the étale neighbourhood `Spec R ⟶ S` and the open immersion
  -- `g : Spec (R ⊗ Γ(X, V)) ⟶ X ×[S] Spec R`, with its two projections. The open
  -- `W₁ = g(D(e))` is `Spec (R ⊗ Γ(X, V))[1/e]`, which is finite over `Spec R`.
  let φ : Γ(S, U) ⟶ ↧R := CommRingCat.ofHom <| algebraMap Γ(S, U) R
  have hφ : φ.hom.Etale := RingHom.etale_algebraMap.mpr ‹_›
  have : Etale (Spec.map φ) := HasRingHomProperty.Spec_iff.mpr hφ
  obtain ⟨g, _, hgfst, hgsnd, hfin⟩ := exists_isOpenImmersion_tensor_isFinite f hU hV hUV R
  let W₁ := g ''ᵁ PrimeSpectrum.basicOpen e
  have : IsFinite (W₁.ι ≫ pullback.snd f _) := hfin e (RingHom.finite_algebraMap.mpr ‹_›)
  -- Step 3: the points `u = P` and `v = g P'`. They are introduced as points of the spectra, not
  -- as primes, so that rewriting with morphisms of schemes applied to them is type correct.
  obtain ⟨u, rfl⟩ : ∃ u : Spec ↧R, u.asIdeal = P := ⟨⟨P, ‹_›⟩, rfl⟩
  obtain ⟨v, rfl⟩ : ∃ v : Spec ↧(R ⊗[Γ(S, U)] Γ(X, V)), v.asIdeal = P' := ⟨⟨P', ‹_›⟩, rfl⟩
  have hu : (Spec.map φ ≫ hU.fromSpec) u = f x := by
    rw [Scheme.Hom.comp_apply]
    refine Eq.trans ?_ (hU.fromSpec_primeIdealOf ⟨f x, hxU⟩)
    congr 1
    exact PrimeSpectrum.ext <| (congrArg PrimeSpectrum.asIdeal (Spec.map_apply φ u)).trans
      (Ideal.over_def u.asIdeal _).symm
  refine ⟨Spec ↧R, Spec.map φ ≫ hU.fromSpec, u, inferInstance, hu, ?_, W₁,
    ⟨g v, v, heP', rfl⟩, ‹_›, ?_, ?_, ?_, ?_⟩
  · -- `κ(f x) ≅ κ(u)`: the residue field map of the open immersion `hU.fromSpec`, then 00UJ.
    have := (isIso_SpecMap_residueFieldMap_iff (algebraMap Γ(S, U) R) u _
      (u.asIdeal.over_def _)).mpr hres
    rw [Scheme.residueFieldMap_comp]
    have h₁ : IsIso (hU.fromSpec.residueFieldMap ((Spec.map φ) u)) := inferInstance
    exact IsIso.comp_isIso' h₁ this
  · rw [← Scheme.Hom.comp_apply, hgfst, Scheme.Hom.comp_apply]
    refine Eq.trans ?_ (hV.fromSpec_primeIdealOf ⟨x, hxV⟩)
    congr 1
    exact PrimeSpectrum.ext <| (congrArg PrimeSpectrum.asIdeal (Spec.map_apply _ v)).trans hP'
  · rw [← Scheme.Hom.comp_apply, hgsnd]
    exact PrimeSpectrum.ext <| (congrArg PrimeSpectrum.asIdeal (Spec.map_apply _ v)).trans
      (Ideal.over_def v.asIdeal u.asIdeal).symm
  · -- `κ(x) ≅ κ(v)`: compute the residue field map of `g ≫ pullback.fst` along `hgfst`, and
    -- cancel that of the open immersion `g`.
    have hb := Ideal.ResidueField.bijective_map_includeRight
      (hU.primeIdealOf ⟨f x, hxU⟩).asIdeal u.asIdeal (hV.primeIdealOf ⟨x, hxV⟩).asIdeal v.asIdeal
      hP'.symm hres
    -- Elaborating the equivalence before applying it to `hb` avoids an expensive unification.
    have h₂' := isIso_SpecMap_residueFieldMap_iff
      Algebra.TensorProduct.includeRight.toRingHom v _ hP'.symm
    have h₂ := h₂'.mpr hb
    have h₃ : IsIso ((g ≫ pullback.fst _ _).residueFieldMap v) := by
      rw [Scheme.Hom.residueFieldMap_congr hgfst, Scheme.residueFieldMap_comp]
      have h₁ : IsIso (hV.fromSpec.residueFieldMap
        ((Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom)) v)) :=
        inferInstance
      exact IsIso.comp_isIso' inferInstance (IsIso.comp_isIso' h₁ h₂)
    rw [Scheme.residueFieldMap_comp] at h₃
    exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ (g.residueFieldMap v) inferInstance h₃
  · -- Uniqueness: a point `g z` of `W₁` over `u` has `z` over `P` with `e ∉ z`, so `z = P'`.
    intro w hw
    obtain ⟨z, hz, hzw⟩ := w.2
    have hzu : Spec.map (CommRingCat.ofHom (algebraMap R (R ⊗[Γ(S, U)] Γ(X, V)))) z = u := by
      rw [← hgsnd, Scheme.Hom.comp_apply]
      exact hzw.symm ▸ hw
    have : z.asIdeal.LiesOver u.asIdeal :=
      ⟨congr(($hzu).asIdeal).symm.trans (congrArg PrimeSpectrum.asIdeal (Spec.map_apply _ z))⟩
    obtain rfl : z = v := PrimeSpectrum.ext (huniq z.asIdeal z.isPrime this hz)
    exact Subtype.ext hzw.symm

end AlgebraicGeometry

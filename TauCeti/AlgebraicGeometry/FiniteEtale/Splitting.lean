/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FiniteEtale.Basic
public import TauCeti.AlgebraicGeometry.Pullback.SpecMap
public import TauCeti.RingTheory.Etale.Splitting

/-!
# Splitting finite étale schemes

A finite étale morphism `f : X ⟶ S` splits étale locally on `S`: every point `s` of `S` has an
étale neighbourhood `φ : Spec T ⟶ S` over which the base change of `X` is `Spec (ι → T)` for a
finite type `ι`, that is, a disjoint union of copies of `Spec T` indexed by `ι`, each mapping
isomorphically to `Spec T`.
Over a field, a finite étale scheme becomes the spectrum of a finite product of `n` copies of
a finite Galois extension of the base field whose degree divides `n!`. The isomorphism is over
the extended base, so it labels all points as rational points, including their scheme
structures. The empty scheme corresponds to the product indexed by `Fin 0`.

Both statements are scheme forms of algebraic splitting results:
`TauCeti.Algebra.Etale.exists_isFiniteSplit_tensorProduct` over a field and
`Algebra.IsFiniteSplit.exists_liesOver_tensorProduct_of_etale` over a ring. They are transported
through `AlgebraicGeometry.Scheme.Hom.exists_overIso_spec_of_isFinite_of_etale`, which presents a
finite étale scheme over an affine base as a spectrum, and
`TauCeti.AlgebraicGeometry.Over.pullbackSndSpecIsoOfAlgEquiv`, built on Mathlib's affine pullback
comparison `AlgebraicGeometry.pullbackSpecIso`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.exists_split_of_isFinite_of_etale`: over a field, a finite étale
  scheme splits after a finite Galois extension of degree dividing `n!`.
* `AlgebraicGeometry.Scheme.Hom.exists_etale_split_of_isFinite_of_etale`: a finite étale
  morphism becomes `Spec (ι → T) ⟶ Spec T`, for a finite type `ι`, after base change to an étale
  neighbourhood `Spec T ⟶ S` of a given point.
* `AlgebraicGeometry.Scheme.Hom.exists_etale_sigma_split_of_isFinite_of_etale`: the same
  splitting as a finite coproduct of copies of the neighbourhood, Stacks, Lemma 41.18.3.

## References

* The Stacks Project, Tag 03QR (schemes étale over a point).
* The Stacks Project, Tag 04HN (finite étale morphisms split étale locally).
-/

public section

open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

namespace Scheme.Hom

/-- A finite étale scheme becomes a disjoint union of `n` rational points after a finite
Galois field extension of degree dividing `n!`. The splitting is an isomorphism over the
extended base. -/
theorem exists_split_of_isFinite_of_etale {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [IsFinite f] [Etale f] :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L)
      (_ : Module.Finite K L) (_ : IsGalois K L) (n : ℕ),
      Module.finrank K L ∣ n.factorial ∧
        Nonempty (Over.mk (pullback.snd f (Spec.algebraMap K L)) ≅
          Over.mk (Spec.algebraMap L (Fin n → L))) := by
  obtain ⟨A, _, _, _, _, ⟨e₀⟩⟩ := f.exists_overIso_spec_of_isFinite_of_etale
  obtain ⟨L, _, _, _, _, hdeg, hL⟩ := TauCeti.Algebra.Etale.exists_isFiniteSplit_tensorProduct K A
  obtain ⟨n, ⟨a⟩⟩ := hL.nonempty_algEquiv_fun
  have hn : Module.finrank K A = n := by
    rw [← Module.finrank_baseChange (R := L), a.toLinearEquiv.finrank_eq]
    simp
  exact ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, n, hn ▸ hdeg,
    ⟨(Over.pullback (Spec.algebraMap K L)).mapIso e₀ ≪≫
      TauCeti.AlgebraicGeometry.Over.pullbackSndSpecIsoOfAlgEquiv a⟩⟩

/-- **A finite étale morphism splits étale locally.** For `f : X ⟶ S` finite étale and a point
`s` of `S`, there are an étale morphism `φ : Spec T ⟶ S` and a point `t` with `φ t = s` such that
the base change of `f` along `φ` is isomorphic over `Spec T` to `Spec (ι → T) ⟶ Spec T` for a
finite type `ι`, the disjoint union of copies of `Spec T` indexed by `ι`. -/
@[stacks 04HN "with the decomposition given by `Spec (ι → T)`"]
theorem exists_etale_split_of_isFinite_of_etale {X S : Scheme.{u}} (f : X ⟶ S) [IsFinite f]
    [Etale f] (s : S) :
    ∃ (T : Type u) (_ : CommRing T) (φ : Spec (.of T) ⟶ S) (_ : Etale φ) (t : Spec (.of T))
      (ι : Type u) (_ : Finite ι), φ t = s ∧
        Nonempty (Over.mk (pullback.snd f φ) ≅ Over.mk (Spec.algebraMap T (ι → T))) := by
  -- Reduce to the base change of `f` to the spectrum of an affine open around `s`.
  obtain ⟨V, hV, hsV, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := s) trivial
  obtain ⟨x, rfl⟩ : s ∈ Set.range hV.fromSpec := by rwa [hV.range_fromSpec]
  let g := pullback.snd f hV.fromSpec
  obtain ⟨A, _, _, _, _, ⟨e₀⟩⟩ := g.exists_overIso_spec_of_isFinite_of_etale
  have : x.asIdeal.IsPrime := x.isPrime
  obtain ⟨T, _, _, _, P, _, hP, hT⟩ :=
    Algebra.IsFiniteSplit.exists_liesOver_tensorProduct_of_etale A x.asIdeal
  obtain ⟨n, ⟨a⟩⟩ := hT.nonempty_algEquiv_fun
  let e := TauCeti.AlgebraicGeometry.Over.pullbackSndSpecIsoOfAlgEquiv
    (a.trans (AlgEquiv.piCongrLeft' T (fun _ ↦ T) Equiv.ulift.{u}.symm))
  let ψ : Spec (.of T) ⟶ Spec Γ(S, V) := Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V) T))
  have : Etale ψ := (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
    (RingHom.etale_algebraMap.mpr inferInstance)
  let t : Spec (.of T) := ⟨P, inferInstance⟩
  refine ⟨T, inferInstance, ψ ≫ hV.fromSpec, inferInstance, t, ULift.{u} (Fin n), inferInstance,
    ?_, ⟨(Over.isoMk (pullbackLeftPullbackSndIso f hV.fromSpec ψ).symm (by simp [g]) :
      Over.mk (pullback.snd f (ψ ≫ hV.fromSpec)) ≅ Over.mk (pullback.snd g ψ)) ≪≫
        (Over.pullback ψ).mapIso e₀ ≪≫ e⟩⟩
  rw [Scheme.Hom.comp_apply, Spec.map_apply]
  exact congrArg hV.fromSpec (PrimeSpectrum.ext hP.over.symm)

/-- **A finite étale morphism splits étale locally**, in the form of Stacks, Lemma 41.18.3: for
`f : X ⟶ S` finite étale and a point `s` of `S`, there are an étale morphism `φ : Spec T ⟶ S`
and a point `t` with `φ t = s` such that the base change of `f` along `φ` is isomorphic over
`Spec T` to a finite coproduct of copies of `Spec T`, each mapping to `Spec T` by the
identity. -/
@[stacks 04HN]
theorem exists_etale_sigma_split_of_isFinite_of_etale {X S : Scheme.{u}} (f : X ⟶ S)
    [IsFinite f] [Etale f] (s : S) :
    ∃ (T : Type u) (_ : CommRing T) (φ : Spec (.of T) ⟶ S) (_ : Etale φ) (t : Spec (.of T))
      (ι : Type u) (_ : Finite ι), φ t = s ∧
        Nonempty (Over.mk (pullback.snd f φ) ≅ Over.mk (Sigma.desc fun _ : ι ↦ 𝟙 _)) := by
  obtain ⟨T, _, φ, _, t, ι, _, hts, ⟨e⟩⟩ := f.exists_etale_split_of_isFinite_of_etale s
  refine ⟨T, inferInstance, φ, inferInstance, t, ι, inferInstance, hts, ⟨e ≪≫ (Over.isoMk
    (asIso (sigmaSpec fun _ : ι ↦ CommRingCat.of T)).symm ?_)⟩⟩
  refine (Iso.inv_comp_eq _).mpr (Sigma.hom_ext _ _ fun i ↦ ?_)
  have hi : (Pi.evalRingHom (fun _ : ι ↦ T) i).comp (algebraMap T (ι → T)) = RingHom.id T :=
    RingHom.ext fun _ ↦ rfl
  simp [Spec.algebraMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hi]

end Scheme.Hom

end AlgebraicGeometry

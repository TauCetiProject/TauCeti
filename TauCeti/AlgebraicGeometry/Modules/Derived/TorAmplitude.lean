/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Monoidal.TorAmplitude
public import TauCeti.AlgebraicGeometry.Modules.Derived.Tensor

/-!
# Flat representatives for complexes of module sheaves

An object of `D(𝒪_X)` has Tor-amplitude in `[a, b]` if and only if it has a representative
by flat `𝒪_X`-modules whose terms vanish outside `[a, b]`.
The lower truncation of a bounded-above flat resolution works because the Tor-amplitude
hypothesis makes the quotient in its new lowest degree flat.

## References

* [The Stacks Project, Lemma 20.48.2](https://stacks.math.columbia.edu/tag/08CH)
* [The Stacks Project, Lemma 20.48.3](https://stacks.math.columbia.edu/tag/08CI)
-/

public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u v

namespace DerivedCategory

variable {X : AlgebraicGeometry.Scheme.{u}} [HasDerivedCategory.{v} X.Modules]

/-- An object of the unbounded derived category of `𝒪_X`-modules has Tor-amplitude in
`[a, b]` if and only if it is represented by flat module sheaves in degrees `a` through `b`. -/
theorem hasTorAmplitude_iff_exists_flat_model {K : DerivedCategory X.Modules} {a b : ℤ} :
    K.HasTorAmplitude a b ↔
      ∃ P : CochainComplex X.Modules ℤ, P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧
        (∀ i, PreservesFiniteLimits (tensorLeft (P.X i))) ∧ Nonempty (Q.obj P ≅ K) := by
  constructor
  · intro hK
    have := hK.isLE
    obtain ⟨L, hL, ⟨e⟩⟩ := K.exists_iso_Q_obj_of_isLE b
    obtain ⟨P', π', hπ, hflat, hKFlat, hPb⟩ :=
      @CochainComplex.exists_quasiIso_isKFlat_sheafOfModules_of_isStrictlyLE
        _ _ _ _ _ _ X.sheaf L b hL
    -- The resolution theorem is stated on the underlying category of sheaves of modules.
    -- Rebind its output so that derived-category instances are found on `X.Modules`.
    let P : CochainComplex X.Modules ℤ := P'
    let π : P ⟶ L := π'
    have : QuasiIso π := hπ
    have : P.IsKFlat := hKFlat
    have : P.IsStrictlyLE b := hPb
    have (i : ℤ) : PreservesFiniteLimits (tensorLeft (P.X i)) := hflat i
    let eP : Q.obj P ≅ K := asIso (Q.map π) ≪≫ e.symm
    have hP := hK.of_iso eP.symm
    have : P.IsGE a := (isGE_Q_obj_iff P a).mp hP.isGE
    have h (M : X.Modules) :
        (((tensorLeft M).mapHomologicalComplex (.up ℤ)).obj P).ExactAt (a - 1) :=
      (CochainComplex.isGE_iff _ a).mp ((hasTorAmplitude_Q_obj_iff P a b).mp hP M).1
        (a - 1) (by omega)
    exact ⟨P.truncGE a, inferInstance, inferInstance,
      fun i ↦ P.preservesFiniteLimits_tensorLeft_truncGE_X a i h,
      ⟨(asIso (Q.map (P.πTruncGE a))).symm ≪≫ eP⟩⟩
  · rintro ⟨P, hPa, hPb, hflat, ⟨e⟩⟩
    have := P.isKFlat_of_bounded_flat a b
    exact (hasTorAmplitude_Q_obj P a b).of_iso e

end DerivedCategory

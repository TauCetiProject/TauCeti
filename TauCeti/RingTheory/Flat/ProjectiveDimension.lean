/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import TauCeti.Algebra.Category.ModuleCat.Projective.Dimension

/-!
# Projective dimension under flat and faithfully flat base change

Let `S` be an `R`-algebra and `M` an `R`-module. If `S` is flat over `R`, base change carries a
projective resolution of `M` to a projective resolution of `S ⊗[R] M`, so

```text
pd_S (S ⊗[R] M) ≤ pd_R M.
```

If moreover `S` is faithfully flat, `R` is Noetherian and `M` is finite, the two projective
dimensions are equal. The point is that projectivity of a finitely presented module descends
along a faithfully flat map: projective modules are flat, flatness descends by Mathlib's
`Module.Flat.of_flat_tensorProduct`, and a finitely presented flat module is projective. Over a
Noetherian ring the syzygies of a finite module are again finite, so dimension shifting along a
finite free presentation `0 → K → P → M → 0`, which stays exact after base change, reduces the
comparison in every degree to this descent of projectivity.

This is the module-theoretic step in the descent of regularity along flat local homomorphisms
(Matsumura, Theorem 23.7 (i)): if `R → S` is a flat local homomorphism of Noetherian local rings
and `S` is regular, every finite `R`-module, in particular the residue field of `R`, has
projective dimension at most `dim S`, and Serre's characterization of regular local rings by
finite global dimension then makes `R` regular.

## Main results

* `Module.Projective.of_projective_tensorProduct`: projectivity of a finitely presented module
  descends along a faithfully flat algebra.
* `ModuleCat.hasProjectiveDimensionLT_tensorProduct`: flat base change does not increase
  projective dimension.
* `ModuleCat.hasProjectiveDimensionLT_of_tensorProduct`: for a finite module over a Noetherian
  ring, a bound on the projective dimension descends along a faithfully flat algebra.
* `ModuleCat.projectiveDimension_tensorProduct`: faithfully flat base change preserves the
  projective dimension of a finite module over a Noetherian ring.

## References

* H. Matsumura, *Commutative Ring Theory*, Theorem 23.7.
* [Stacks Project, Tag 00NX](https://stacks.math.columbia.edu/tag/00NX): finitely presented flat
  modules are projective.
-/

public section

universe u v w

open CategoryTheory TensorProduct

namespace Module.Projective

variable (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M]
  (S : Type*) [CommRing S] [Algebra R S] [Module.FaithfullyFlat R S]

/-- Projectivity of a finitely presented module descends along a faithfully flat algebra. -/
theorem of_projective_tensorProduct [Module.FinitePresentation R M]
    [Module.Projective S (S ⊗[R] M)] : Module.Projective R M :=
  have : Module.Flat R M := .of_flat_tensorProduct R M S
  Module.Flat.projective_of_finitePresentation

variable {R M} in
/-- A finitely presented module is projective exactly when its base change to a faithfully flat
algebra is. -/
theorem iff_projective_tensorProduct [Module.FinitePresentation R M] :
    Module.Projective S (S ⊗[R] M) ↔ Module.Projective R M :=
  ⟨fun _ ↦ of_projective_tensorProduct R M S, fun _ ↦ inferInstance⟩

end Module.Projective

namespace ModuleCat

variable {R : Type u} [CommRing R] [Small.{w} R] {S : Type v} [CommRing S] [Algebra R S]

omit [Small.{w} R] in
/-- Dimension shifting after flat base change: for a surjection `f : P → M` from a projective
module, `S ⊗[R] M` has projective dimension at most `n + 1` exactly when `S ⊗[R] ker f` has
projective dimension at most `n`, as base change carries `ker f` onto the kernel of the
surjection `S ⊗[R] P → S ⊗[R] M`. -/
private theorem hasProjectiveDimensionLE_tensorProduct_succ_iff_ker [Module.Flat R S]
    {P M : Type w} [AddCommGroup P] [Module R P] [Module.Projective R P] [AddCommGroup M]
    [Module R M] {f : P →ₗ[R] M} (hf : Function.Surjective f) {n : ℕ} :
    HasProjectiveDimensionLE (ModuleCat.of S (S ⊗[R] M)) (n + 1) ↔
      HasProjectiveDimensionLE (ModuleCat.of S (S ⊗[R] LinearMap.ker f)) n := by
  have : Small.{max v w} S := small_max S
  rw [(AlgebraTensorModule.lTensor S S f).hasProjectiveDimensionLE_succ_iff_ker
    (LinearMap.lTensor_surjective S hf)]
  exact ⟨fun _ ↦ hasProjectiveDimensionLT_of_iso (f.tensorKerEquiv S S).toModuleIso.symm _,
    fun _ ↦ hasProjectiveDimensionLT_of_iso (f.tensorKerEquiv S S).toModuleIso _⟩

/-- The degree-wise form of `ModuleCat.hasProjectiveDimensionLT_tensorProduct`, by induction on
the bound along projective presentations. -/
private theorem hasProjectiveDimensionLE_tensorProduct [Module.Flat R S] (n : ℕ) :
    ∀ (M : Type w) [AddCommGroup M] [Module R M], HasProjectiveDimensionLE (ModuleCat.of R M) n →
      HasProjectiveDimensionLE (ModuleCat.of S (S ⊗[R] M)) n := by
  have : Small.{max v w} S := small_max S
  induction n with
  | zero =>
    intro M _ _ h
    rw [← projective_iff_hasProjectiveDimensionLE_zero, ← IsProjective.iff_projective] at h ⊢
    infer_instance
  | succ n ih =>
    intro M _ _ h
    -- Shift along a projective presentation `ker f → P → M`, on both sides of the base change.
    let f := (Projective.π (ModuleCat.of R M)).hom
    have hf : Function.Surjective f := (ModuleCat.epi_iff_surjective _).mp inferInstance
    rw [f.hasProjectiveDimensionLE_succ_iff_ker hf] at h
    exact (hasProjectiveDimensionLE_tensorProduct_succ_iff_ker hf).mpr (ih _ h)

/-- The degree-wise form of `ModuleCat.hasProjectiveDimensionLT_of_tensorProduct`, by induction on
the bound along finite free presentations. -/
private theorem hasProjectiveDimensionLE_of_tensorProduct [Module.FaithfullyFlat R S]
    [IsNoetherianRing R] (n : ℕ) :
    ∀ (M : Type w) [AddCommGroup M] [Module R M] [Module.Finite R M],
      HasProjectiveDimensionLE (ModuleCat.of S (S ⊗[R] M)) n →
        HasProjectiveDimensionLE (ModuleCat.of R M) n := by
  have : Small.{max v w} S := small_max S
  induction n with
  | zero =>
    intro M _ _ _ h
    rw [← projective_iff_hasProjectiveDimensionLE_zero, ← IsProjective.iff_projective] at h ⊢
    have := Module.finitePresentation_of_finite R M
    exact Module.Projective.of_projective_tensorProduct R M S
  | succ n ih =>
    intro M _ _ _ h
    -- Shift along a finite free presentation; over a Noetherian ring its kernel is finite.
    obtain ⟨P, _, _, _, _, f, hf⟩ := Module.exists_finite_presentation R M
    rw [hasProjectiveDimensionLE_tensorProduct_succ_iff_ker hf] at h
    exact (f.hasProjectiveDimensionLE_succ_iff_ker hf n).mpr (ih _ h)

variable (S) (M : Type w) [AddCommGroup M] [Module R M]

/-- **Flat base change does not increase projective dimension.** If `S` is a flat `R`-algebra and
`M` has projective dimension less than `n` over `R`, then `S ⊗[R] M` has projective dimension
less than `n` over `S`. -/
theorem hasProjectiveDimensionLT_tensorProduct [Module.Flat R S] {n : ℕ}
    (h : HasProjectiveDimensionLT (ModuleCat.of R M) n) :
    HasProjectiveDimensionLT (ModuleCat.of S (S ⊗[R] M)) n := by
  cases n with
  | zero =>
    rw [hasProjectiveDimensionLT_zero_iff_isZero, ModuleCat.isZero_iff_subsingleton] at h ⊢
    infer_instance
  | succ n => exact hasProjectiveDimensionLE_tensorProduct n M h

/-- **Faithfully flat descent of projective dimension.** Let `S` be a faithfully flat algebra over
a Noetherian ring `R` and `M` a finite `R`-module. If `S ⊗[R] M` has projective dimension less
than `n` over `S`, then `M` has projective dimension less than `n` over `R`. -/
theorem hasProjectiveDimensionLT_of_tensorProduct [Module.FaithfullyFlat R S] [IsNoetherianRing R]
    [Module.Finite R M] {n : ℕ} (h : HasProjectiveDimensionLT (ModuleCat.of S (S ⊗[R] M)) n) :
    HasProjectiveDimensionLT (ModuleCat.of R M) n := by
  cases n with
  | zero =>
    rw [hasProjectiveDimensionLT_zero_iff_isZero, ModuleCat.isZero_iff_subsingleton] at h ⊢
    exact (Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right R S).mp h
  | succ n => exact hasProjectiveDimensionLE_of_tensorProduct n M h

variable {M} in
/-- For a finite module over a Noetherian ring and a faithfully flat algebra `S`, a bound on the
projective dimension holds before base change to `S` exactly when it holds after. -/
theorem hasProjectiveDimensionLT_tensorProduct_iff [Module.FaithfullyFlat R S]
    [IsNoetherianRing R] [Module.Finite R M] {n : ℕ} :
    HasProjectiveDimensionLT (ModuleCat.of S (S ⊗[R] M)) n ↔
      HasProjectiveDimensionLT (ModuleCat.of R M) n :=
  ⟨hasProjectiveDimensionLT_of_tensorProduct S M, hasProjectiveDimensionLT_tensorProduct S M⟩

/-- Flat base change does not increase projective dimension:
`pd_S (S ⊗[R] M) ≤ pd_R M` for every `R`-module `M`. -/
theorem projectiveDimension_tensorProduct_le [Module.Flat R S] :
    projectiveDimension (ModuleCat.of S (S ⊗[R] M)) ≤ projectiveDimension (ModuleCat.of R M) := by
  simp only [projectiveDimension]
  exact sInf_le_sInf fun _ hd i hi ↦ hasProjectiveDimensionLT_tensorProduct S M (hd i hi)

/-- **Faithfully flat base change preserves projective dimension** of a finite module over a
Noetherian ring: `pd_S (S ⊗[R] M) = pd_R M`. -/
theorem projectiveDimension_tensorProduct [Module.FaithfullyFlat R S] [IsNoetherianRing R]
    [Module.Finite R M] :
    projectiveDimension (ModuleCat.of S (S ⊗[R] M)) = projectiveDimension (ModuleCat.of R M) := by
  refine (projectiveDimension_tensorProduct_le S M).antisymm ?_
  simp only [projectiveDimension]
  exact sInf_le_sInf fun _ hd i hi ↦ hasProjectiveDimensionLT_of_tensorProduct S M (hd i hi)

end ModuleCat

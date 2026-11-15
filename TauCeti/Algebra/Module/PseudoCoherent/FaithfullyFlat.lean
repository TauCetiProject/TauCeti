/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import TauCeti.Algebra.Module.PseudoCoherent.FiniteProjectiveDimension
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.Finiteness.Descent
import Mathlib.RingTheory.Flat.EquationalCriterion
import TauCeti.Algebra.Module.PseudoCoherent.BaseChange

/-!
# Finite projective dimension under flat base change and faithfully flat descent

Let `S` be an `R`-algebra. Extension of scalars along `S` preserves finite projective dimension
when `S` is flat, and reflects it when `S` is faithfully flat: for every `R`-module `M`,

```text
M is m-fpd over R  ↔  S ⊗[R] M is m-fpd over S.
```

For a pseudocoherent module, for instance a finite module over a noetherian ring, this says that
`M` and `S ⊗[R] M` have the same projective dimension. Consequently a noetherian ring has global
dimension at most that of any faithfully flat algebra over it; see
`TauCeti.globalDimension_le_of_faithfullyFlat`.

This is the homological half of the descent of regularity along faithfully flat homomorphisms of
noetherian local rings: if `R → S` is such a homomorphism and `S` is regular, then the residue
field of `R` has finite projective dimension over `R`, which by Serre's criterion makes `R`
regular.

## Main results

* `TauCeti.Module.IsFPD.baseChange`: flat base change preserves finite projective dimension.
* `TauCeti.Module.IsFPD.of_baseChange`: faithfully flat base change reflects finite projective
  dimension.
* `TauCeti.Module.isFPD_baseChange_iff`: the two combined.
* `ModuleCat.hasProjectiveDimensionLE_baseChange_iff`: a pseudocoherent module has projective
  dimension at most `n` exactly when its faithfully flat base change does.

## References

* H. Matsumura, *Commutative Ring Theory*, Theorem 23.7, for the descent of regularity along flat
  local homomorphisms, which this descent of projective dimension feeds.
-/

public section

namespace TauCeti.Module

open LinearMap TensorProduct

universe u v w

variable {R : Type u} [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
  {M : Type w} [AddCommGroup M] [Module R M]

/- Both directions are proved by induction on `m`, one syzygy at a time
(`TauCeti.Module.IsFPD.succ_iff_ker`). For a surjection `f : P → M` from a finite free module,
flatness identifies the kernel of `S ⊗ f` with `S ⊗[R] ker f` (`LinearMap.tensorKerEquiv`). In
degree zero of the descent, finite generation of `M` and of `ker f` descends along the faithfully
flat `S`, so `M` is finitely presented; as `S ⊗[R] M` is projective, Mathlib's
`Module.Flat.of_flat_tensorProduct` makes `M` flat, hence projective. -/

/-- Along a surjection `f : P → M` from a finitely generated projective module, `S ⊗[R] M` is
`(m + 1)`-fpd over a flat `R`-algebra `S` exactly when `S ⊗[R] ker f` is `m`-fpd. -/
private theorem isFPD_succ_baseChange_iff_ker [Module.Flat R S] {m : ℕ} {P : Type*}
    [AddCommGroup P] [Module R P] [Module.Finite R P] [Module.Projective R P] {f : P →ₗ[R] M}
    (hf : Function.Surjective f) :
    IsFPD S (S ⊗[R] M) (m + 1) ↔ IsFPD S (S ⊗[R] ker f) m := by
  have hf' : Function.Surjective (AlgebraTensorModule.lTensor S S f) :=
    LinearMap.lTensor_surjective S hf
  rw [IsFPD.succ_iff_ker hf']
  exact ⟨IsFPD.of_equiv (tensorKerEquiv S S f).symm, IsFPD.of_equiv (tensorKerEquiv S S f)⟩

/-- `IsFPD.baseChange` for modules in the universe of `R`, where the syzygies live. -/
private theorem IsFPD.baseChange_aux [Module.Flat R S] :
    ∀ (m : ℕ) (N : Type u) [AddCommGroup N] [Module R N], IsFPD R N m → IsFPD S (S ⊗[R] N) m
  | 0, N, _, _, h => by
    obtain ⟨_, _⟩ := IsFPD.zero_iff.mp h
    exact IsFPD.of_projective
  | m + 1, N, _, _, h => by
    have := h.isPseudoCoherentOver.finite
    obtain ⟨k, f, hf⟩ := Module.Finite.exists_fin' R N
    exact (isFPD_succ_baseChange_iff_ker S hf).mpr
      (IsFPD.baseChange_aux m _ ((IsFPD.succ_iff_ker hf).mp h))

/-- `IsFPD.of_baseChange` for modules in the universe of `R`, where the syzygies live. -/
private theorem IsFPD.of_baseChange_aux [Module.FaithfullyFlat R S] :
    ∀ (m : ℕ) (N : Type u) [AddCommGroup N] [Module R N], IsFPD S (S ⊗[R] N) m → IsFPD R N m
  | 0, N, _, _, h => by
    obtain ⟨_, _⟩ := IsFPD.zero_iff.mp h
    have : Module.Finite R N := .of_finite_tensorProduct_of_faithfullyFlat S
    obtain ⟨k, f, hf⟩ := Module.Finite.exists_fin' R N
    -- The kernel of `S ⊗ f` is finite since `S ⊗[R] N` is finitely presented, so `ker f` is
    -- finite and `N` is finitely presented.
    have := Module.finitePresentation_of_projective S (S ⊗[R] N)
    have : Module.Finite S (ker (AlgebraTensorModule.lTensor S S f)) :=
      Module.Finite.iff_fg.mpr (Module.FinitePresentation.fg_ker _ (lTensor_surjective S hf))
    have : Module.Finite S (S ⊗[R] ker f) := .equiv (tensorKerEquiv S S f).symm
    have : Module.Finite R (ker f) := .of_finite_tensorProduct_of_faithfullyFlat S
    have := Module.finitePresentation_of_surjective f hf (Module.Finite.iff_fg.mp inferInstance)
    have := Module.Flat.of_flat_tensorProduct R N S
    have := Module.Flat.projective_of_finitePresentation (R := R) (M := N)
    exact IsFPD.of_projective
  | m + 1, N, _, _, h => by
    have := h.isPseudoCoherentOver.finite
    have : Module.Finite R N := .of_finite_tensorProduct_of_faithfullyFlat S
    obtain ⟨k, f, hf⟩ := Module.Finite.exists_fin' R N
    exact (IsFPD.succ_iff_ker hf).mpr
      (IsFPD.of_baseChange_aux m _ ((isFPD_succ_baseChange_iff_ker S hf).mp h))

/-- **Flat base change preserves finite projective dimension.** If `M` is `m`-fpd over `R` and `S`
is a flat `R`-algebra, then `S ⊗[R] M` is `m`-fpd over `S`. -/
theorem IsFPD.baseChange [Module.Flat R S] {m : ℕ} (h : IsFPD R M m) :
    IsFPD S (S ⊗[R] M) m := by
  -- Replace `M` by an equivalent quotient of `Rᵏ`, which lies in the universe of `R`.
  have := h.isPseudoCoherentOver.finite
  obtain ⟨k, f, hf⟩ := Module.Finite.exists_fin' R M
  let e := f.quotKerEquivOfSurjective hf
  exact (IsFPD.baseChange_aux S m _ (h.of_equiv e.symm)).of_equiv
    (LinearEquiv.baseChange R S _ _ e)

/-- **Faithfully flat base change reflects finite projective dimension.** If `S` is a faithfully
flat `R`-algebra and `S ⊗[R] M` is `m`-fpd over `S`, then `M` is `m`-fpd over `R`. -/
theorem IsFPD.of_baseChange [Module.FaithfullyFlat R S] {m : ℕ} (h : IsFPD S (S ⊗[R] M) m) :
    IsFPD R M m := by
  -- Replace `M` by an equivalent quotient of `Rᵏ`, which lies in the universe of `R`.
  have := h.isPseudoCoherentOver.finite
  have : Module.Finite R M := .of_finite_tensorProduct_of_faithfullyFlat S
  obtain ⟨k, f, hf⟩ := Module.Finite.exists_fin' R M
  let e := f.quotKerEquivOfSurjective hf
  exact (IsFPD.of_baseChange_aux S m _
    (h.of_equiv (LinearEquiv.baseChange R S _ _ e.symm))).of_equiv e

/-- **Faithfully flat base change detects finite projective dimension.** An `R`-module `M` is
`m`-fpd exactly when `S ⊗[R] M` is `m`-fpd over a faithfully flat `R`-algebra `S`. -/
theorem isFPD_baseChange_iff [Module.FaithfullyFlat R S] {m : ℕ} :
    IsFPD S (S ⊗[R] M) m ↔ IsFPD R M m :=
  ⟨IsFPD.of_baseChange S, IsFPD.baseChange S⟩

end TauCeti.Module

namespace ModuleCat

open CategoryTheory TauCeti TensorProduct

universe u

variable {R S M : Type u} [CommRing R] [CommRing S] [Algebra R S] [AddCommGroup M] [Module R M]

/-- **Faithfully flat base change preserves and detects projective dimension.** A pseudocoherent
`R`-module `M`, for instance a finite module over a noetherian ring, has projective dimension at
most `n` exactly when `S ⊗[R] M` has projective dimension at most `n` over a faithfully flat
`R`-algebra `S`. -/
theorem hasProjectiveDimensionLE_baseChange_iff [Module.FaithfullyFlat R S]
    (hM : Huber.IsPseudoCoherentOver R M ⊤) {n : ℕ} :
    HasProjectiveDimensionLE (ModuleCat.of S (S ⊗[R] M)) n ↔
      HasProjectiveDimensionLE (ModuleCat.of R M) n := by
  simpa only [Module.isFPD_iff_hasProjectiveDimensionLE, hM, hM.baseChange S, true_and] using
    Module.isFPD_baseChange_iff (R := R) (M := M) (m := n) S

end ModuleCat

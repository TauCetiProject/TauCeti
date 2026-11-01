/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import TauCeti.Algebra.Module.PseudoCoherent.Basic
import Mathlib.RingTheory.Finiteness.Descent
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.Finiteness
import TauCeti.Algebra.Module.PseudoCoherent.BaseChange

/-!
# Descent of pseudocoherence

Pseudocoherence (`TauCeti.Huber.IsPseudoCoherentOver`) descends along faithfully flat ring maps
and is local on `Spec R`, in every degree `m ∈ ℕ ∪ {∞}`:

* if `S` is a faithfully flat `R`-algebra and `S ⊗[R] M` is `m`-pseudocoherent over `S`, then `M`
  is `m`-pseudocoherent over `R`;
* if `s ⊆ R` generates the unit ideal and every localization `M_g`, `g ∈ s`, is
  `m`-pseudocoherent over `R_g`, then `M` is `m`-pseudocoherent over `R`.

Together with flat base change (`TauCeti.Huber.IsPseudoCoherentOver.baseChange`) these say that
pseudocoherence of a module can be checked after a faithfully flat extension, or on a cover of
`Spec R` by standard opens. To show that the sections of a pseudocoherent sheaf over an affine
open are pseudocoherent, the second statement supplies the descent step from a standard-open
cover, once the sections over each member of the cover are known to be pseudocoherent.

## Main results

* `TauCeti.Huber.IsPseudoCoherentOver.of_baseChange`: faithfully flat base change reflects
  `m`-pseudocoherence.
* `TauCeti.Huber.isPseudoCoherentOver_baseChange_iff`: `M` is `m`-pseudocoherent exactly when
  `S ⊗[R] M` is, for a faithfully flat `R`-algebra `S`.
* `TauCeti.Huber.IsPseudoCoherentOver.of_localizationSpan'` and
  `TauCeti.Huber.IsPseudoCoherentOver.of_localizationSpan`: `m`-pseudocoherence is local on
  `Spec R`.

## References

* The Stacks Project, Tag 068R (faithfully flat descent of pseudo-coherence) and Tag 066D
  (pseudo-coherence is local on `Spec R`), for complexes; here for modules.
* The syzygy induction and the reduction to modules in the universe of `R` follow
  `TauCeti.Module.IsFPD.of_baseChange` in
  `TauCeti/Algebra/Module/PseudoCoherent/FaithfullyFlat.lean`.
-/

public section

/- Both descent statements are proved by induction on the degree, one syzygy at a time
(`TauCeti.Huber.IsPseudoCoherentOver.succ_iff_ker`), for a family of flat algebras that jointly
detect finite generation. For a surjection `f : Rᵏ → M`, flatness identifies the kernel of
`S ⊗ f` with `S ⊗[R] ker f` (`LinearMap.tensorKerEquiv`), and finite generation descends by
Mathlib's `Module.Finite.of_finite_tensorProduct_of_faithfullyFlat` and
`Module.Finite.of_localizationSpan'`. -/

namespace TauCeti.Huber

open LinearMap TensorProduct

universe u v

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M] {m : ℕ∞}

namespace IsPseudoCoherentOver

/-- Over a flat `R`-algebra `S`, if `S ⊗[R] N` is `(m + 1)`-pseudocoherent then so is `S ⊗[R] ker f`
in degree `m`, for every surjection `f : P → N` from a finitely generated projective module. -/
private theorem baseChange_ker {S : Type*} [CommRing S] [Algebra R S] [Module.Flat R S]
    {N P : Type*} [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P] [Module.Finite R P]
    [Module.Projective R P] {f : P →ₗ[R] N} (hf : Function.Surjective f)
    (h : IsPseudoCoherentOver S (S ⊗[R] N) (m + 1)) :
    IsPseudoCoherentOver S (S ⊗[R] ker f) m :=
  (h.ker_of_projective (f := AlgebraTensorModule.lTensor S S f)
    (lTensor_surjective S hf)).of_equiv (tensorKerEquiv S S f).symm

/-- Descent of `n`-pseudocoherence along a family of flat algebras that jointly detect finite
generation, for modules in the universe of `R`, where the syzygies live. -/
private theorem of_baseChange_family_aux {ι : Type*} (S : ι → Type*) [∀ i, CommRing (S i)]
    [∀ i, Algebra R (S i)] [∀ i, Module.Flat R (S i)]
    (hfin : ∀ (N : Type u) [AddCommGroup N] [Module R N],
      (∀ i, Module.Finite (S i) (S i ⊗[R] N)) → Module.Finite R N) :
    ∀ (n : ℕ) (N : Type u) [AddCommGroup N] [Module R N],
      (∀ i, IsPseudoCoherentOver (S i) (S i ⊗[R] N) n) → IsPseudoCoherentOver R N n
  | 0, N, _, _, h => zero_iff.mpr (hfin N fun i ↦ (h i).finite)
  | n + 1, N, _, _, h => by
    have : Module.Finite R N := hfin N fun i ↦ (h i).finite
    obtain ⟨k, f, hf⟩ := Module.Finite.exists_fin' R N
    rw [Nat.cast_succ] at h ⊢
    exact (succ_iff_ker hf).mpr
      (of_baseChange_family_aux S hfin n _ fun i ↦ baseChange_ker hf (h i))

/-- Descent of `m`-pseudocoherence along a family of flat algebras that jointly detect finite
generation of modules in the universe of `R`, for a finitely generated module `M`. -/
private theorem of_baseChange_family {ι : Type*} (S : ι → Type*) [∀ i, CommRing (S i)]
    [∀ i, Algebra R (S i)] [∀ i, Module.Flat R (S i)]
    (hfin : ∀ (N : Type u) [AddCommGroup N] [Module R N],
      (∀ i, Module.Finite (S i) (S i ⊗[R] N)) → Module.Finite R N)
    [Module.Finite R M] (h : ∀ i, IsPseudoCoherentOver (S i) (S i ⊗[R] M) m) :
    IsPseudoCoherentOver R M m := by
  -- Replace `M` by an equivalent quotient of `Rᵏ`, which lies in the universe of `R`.
  obtain ⟨k, f, hf⟩ := Module.Finite.exists_fin' R M
  let e := f.quotKerEquivOfSurjective hf
  have hnat (n : ℕ) (hn : ∀ i, IsPseudoCoherentOver (S i) (S i ⊗[R] M) n) :
      IsPseudoCoherentOver R M n :=
    (of_baseChange_family_aux S hfin n _ fun i ↦
      (hn i).of_equiv (LinearEquiv.baseChange R (S i) _ _ e.symm)).of_equiv e
  induction m using ENat.recTopCoe with
  | top => exact top_iff.mpr fun n ↦ hnat n fun i ↦ top_iff.mp (h i) n
  | coe n => exact hnat n h

/-- **Faithfully flat base change reflects pseudocoherence.** If `S` is a faithfully flat
`R`-algebra and `S ⊗[R] M` is `m`-pseudocoherent over `S`, then `M` is `m`-pseudocoherent over
`R` (Stacks, Tag 068R). -/
theorem of_baseChange (S : Type*) [CommRing S] [Algebra R S] [Module.FaithfullyFlat R S]
    (h : IsPseudoCoherentOver S (S ⊗[R] M) m) : IsPseudoCoherentOver R M m :=
  have := h.finite
  have : Module.Finite R M := .of_finite_tensorProduct_of_faithfullyFlat S
  of_baseChange_family (fun _ : Unit ↦ S)
    (fun _ _ _ hN ↦ have := hN (); .of_finite_tensorProduct_of_faithfullyFlat S) fun _ ↦ h

end IsPseudoCoherentOver

/-- **Faithfully flat base change detects pseudocoherence.** An `R`-module `M` is
`m`-pseudocoherent exactly when `S ⊗[R] M` is `m`-pseudocoherent over a faithfully flat
`R`-algebra `S`. -/
theorem isPseudoCoherentOver_baseChange_iff (S : Type*) [CommRing S] [Algebra R S]
    [Module.FaithfullyFlat R S] :
    IsPseudoCoherentOver S (S ⊗[R] M) m ↔ IsPseudoCoherentOver R M m :=
  ⟨IsPseudoCoherentOver.of_baseChange S, fun h ↦ h.baseChange S⟩

namespace IsPseudoCoherentOver

/-- **Pseudocoherence is local on `Spec R`.** If `s ⊆ R` generates the unit ideal and, for every
`g ∈ s`, the localization `Mₚ g` of `M` away from `g` is `m`-pseudocoherent over the localization
`Rₚ g` of `R` away from `g`, then `M` is `m`-pseudocoherent over `R` (Stacks, Tag 066D).

General version for any modules `Mₚ g` and rings `Rₚ g` satisfying the universal properties of
the localizations; see `TauCeti.Huber.IsPseudoCoherentOver.of_localizationSpan` for the
specialized version. -/
theorem of_localizationSpan' (s : Set R) (hs : Ideal.span s = ⊤)
    {Mₚ : ∀ (_ : s), Type*} [∀ g : s, AddCommGroup (Mₚ g)] [∀ g : s, Module R (Mₚ g)]
    {Rₚ : ∀ (_ : s), Type*} [∀ g : s, CommRing (Rₚ g)] [∀ g : s, Algebra R (Rₚ g)]
    [∀ g : s, IsLocalization.Away g.val (Rₚ g)]
    [∀ g : s, Module (Rₚ g) (Mₚ g)] [∀ g : s, IsScalarTower R (Rₚ g) (Mₚ g)]
    (ϕ : ∀ g : s, M →ₗ[R] Mₚ g) [∀ g : s, IsLocalizedModule (Submonoid.powers g.val) (ϕ g)]
    (h : ∀ g : s, IsPseudoCoherentOver (Rₚ g) (Mₚ g) m) : IsPseudoCoherentOver R M m :=
  have (g : s) : Module.Flat R (Rₚ g) := IsLocalization.flat (Rₚ g) (Submonoid.powers g.val)
  have : Module.Finite R M := .of_localizationSpan' s hs ϕ fun g ↦ (h g).finite
  of_baseChange_family Rₚ
    (fun N _ _ hN ↦ .of_localizationSpan' s hs (fun g ↦ TensorProduct.mk R (Rₚ g) N 1) hN)
    fun g ↦ (h g).of_equiv
      (IsLocalizedModule.isBaseChange (Submonoid.powers g.val) (Rₚ g) (ϕ g)).equiv.symm

/-- **Pseudocoherence is local on `Spec R`.** If `s ⊆ R` generates the unit ideal and, for every
`g ∈ s`, the localized module `M_g` is `m`-pseudocoherent over `R_g`, then `M` is
`m`-pseudocoherent over `R` (Stacks, Tag 066D). -/
theorem of_localizationSpan (s : Set R) (hs : Ideal.span s = ⊤)
    (h : ∀ g : s, IsPseudoCoherentOver (Localization.Away g.val) (LocalizedModule.Away g.val M) m) :
    IsPseudoCoherentOver R M m :=
  of_localizationSpan' s hs (fun g ↦ LocalizedModule.mkLinearMap (Submonoid.powers g.val) M) h

end IsPseudoCoherentOver

end TauCeti.Huber

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.PseudoCoherent.Basic
public import TauCeti.RingTheory.Huber.LocalizationTopology.RatLoc
public import TauCeti.RingTheory.Huber.ModuleTopology.NaturallyComplete
public import TauCeti.RingTheory.Huber.StronglyNoetherian
import TauCeti.RingTheory.Huber.FiniteModuleTopology
import TauCeti.RingTheory.Huber.LocalizationTopology.StronglyNoetherian
import TauCeti.RingTheory.Huber.OpenIdeal

/-!
# Stably pseudocoherent modules

Let `A` be a topological ring. An `A`-module `M` is *stably `m`-pseudocoherent* if it is
`m`-pseudocoherent and, for every rational localisation `A → A⟨T/s⟩` (numerators `T` generating
an open ideal), the algebraic base change `A⟨T/s⟩ ⊗[A] M` is complete and Hausdorff for its
natural topology as an `A⟨T/s⟩`-module (Kedlaya–Liu II, Definition 2.4.1). No completed tensor
product is formed: completeness of the algebraic one is the condition. The definition involves no
plus ring, which would only select which rational subsets occur. These are the modules for which
Kedlaya–Liu prove Tate acyclicity over a sheafy complete Tate ring: the presheaf
`U ↦ M ⊗[A] 𝒪(U)` on the rational subsets of `Spa(A, A⁺)` has exact Čech complexes for finite
rational coverings (Kedlaya–Liu II, Theorem 2.5.1).

Two sources of examples are recorded here. Finite projective modules are stably pseudocoherent
over any topological ring: their base changes are finite projective over the complete Hausdorff
ring `A⟨T/s⟩`, hence naturally complete. Over a noetherian, strongly noetherian Tate ring every
finite module is stably pseudocoherent (Kedlaya–Liu II, remark after Definition 2.4.1): each
`A⟨T/s⟩` is again strongly noetherian, hence a complete noetherian Tate ring, over which every
finite module is naturally complete.

## Main definitions

* `TauCeti.Huber.IsStablyPseudoCoherent A M m`: `M` is stably `m`-pseudocoherent over `A`.

## Main results

* `TauCeti.Huber.IsStablyPseudoCoherent.mono`: stable `m`-pseudocoherence implies stable
  `m'`-pseudocoherence for `m' ≤ m`.
* `TauCeti.Huber.IsStablyPseudoCoherent.of_equiv`: it is invariant under linear equivalence.
* `TauCeti.Huber.IsStablyPseudoCoherent.of_projective`: finite projective modules are stably
  pseudocoherent.
* `TauCeti.Huber.IsStablyPseudoCoherent.of_isStronglyNoetherian`: over a noetherian, strongly
  noetherian Tate ring, finite modules are stably pseudocoherent.

## References

* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory, II: Imperfect period rings*, §2.4,
  Definition 2.4.1 and the remark following it, and §2.5, Theorem 2.5.1.
-/

public section

open scoped TensorProduct

namespace TauCeti.Huber

section Definition

variable (A : Type*) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  (M : Type*) [AddCommGroup M] [Module A M]

/-- The `A`-module `M` is *stably `m`-pseudocoherent* if it is `m`-pseudocoherent and, for every
rational localisation `A⟨T/s⟩` whose numerators `T` generate an open ideal, the algebraic base
change `A⟨T/s⟩ ⊗[A] M` is complete and Hausdorff for its natural topology (Kedlaya–Liu II,
Definition 2.4.1). -/
structure IsStablyPseudoCoherent (m : ℕ∞) : Prop where
  /-- `M` is `m`-pseudocoherent. -/
  isPseudoCoherentOver : IsPseudoCoherentOver A M m
  /-- Every base change of `M` to a rational localisation `A⟨T/s⟩` is naturally complete. -/
  isNaturallyComplete_tensor (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hden : P.HasDenominatorPower T s (Localization.Away s))
    (hT : IsOpen ((Ideal.span (T : Set A) : Ideal A) : Set A)) :
    IsNaturallyComplete (ratLoc P T s hden) (ratLoc P T s hden ⊗[A] M)

end Definition

namespace IsStablyPseudoCoherent

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  {M : Type*} [AddCommGroup M] [Module A M] {m : ℕ∞}

/-- Stable `m`-pseudocoherence implies stable `m'`-pseudocoherence for `m' ≤ m`: the analytic
condition does not involve `m`. -/
theorem mono {m' : ℕ∞} (h : IsStablyPseudoCoherent A M m) (hm : m' ≤ m) :
    IsStablyPseudoCoherent A M m' :=
  ⟨h.isPseudoCoherentOver.mono hm, h.isNaturallyComplete_tensor⟩

/-- **Stable pseudocoherence is invariant under linear equivalence.** -/
theorem of_equiv {N : Type*} [AddCommGroup N] [Module A N] (e : M ≃ₗ[A] N)
    (h : IsStablyPseudoCoherent A M m) : IsStablyPseudoCoherent A N m := by
  refine ⟨h.isPseudoCoherentOver.of_equiv e, fun P T s hden hT ↦ ?_⟩
  have : Module.Finite A M := h.isPseudoCoherentOver.finite
  have : Module.Finite A N := Module.Finite.equiv e
  -- `A⟨T/s⟩ ⊗ N` embeds into the naturally complete `A⟨T/s⟩ ⊗ M` by the base change of `e⁻¹`
  exact (h.isNaturallyComplete_tensor P T s hden hT).of_injective
    (f := (e.symm.baseChange A (ratLoc P T s hden) N M).toLinearMap)
    (e.symm.baseChange A (ratLoc P T s hden) N M).injective

/-- **Finite projective modules are stably pseudocoherent** (Kedlaya–Liu II, Definition 2.4.1 and
Remark 1.2.4): each base change `A⟨T/s⟩ ⊗[A] M` is finite projective over the complete Hausdorff
ring `A⟨T/s⟩`, hence naturally complete. -/
theorem of_projective [Module.Finite A M] [Module.Projective A M] :
    IsStablyPseudoCoherent A M ⊤ :=
  ⟨.of_projective, fun _ _ _ _ _ ↦ .of_projective⟩

/-- **Over a noetherian, strongly noetherian Tate ring, finite modules are stably
pseudocoherent** (Kedlaya–Liu II, remark after Definition 2.4.1). A finite module over a
noetherian ring is pseudocoherent. Every rational localisation `A⟨T/s⟩` is again strongly
noetherian (`TauCeti.Huber.PairOfDefinition.isStronglyNoetherian_completion`), so as a complete
Hausdorff strongly noetherian Tate ring it is noetherian, and a finite module over a complete
noetherian Tate ring is Hausdorff, hence naturally complete, for its natural topology. -/
theorem of_isStronglyNoetherian [IsTateRing A] [IsStronglyNoetherian A] [IsNoetherianRing A]
    [Module.Finite A M] : IsStablyPseudoCoherent A M ⊤ := by
  refine ⟨.of_isNoetherianRing, fun P T s hden hT ↦ ?_⟩
  set B := ratLoc P T s hden
  -- the numerators span the unit ideal, so `A⟨T/s⟩` is strongly noetherian
  have hspan : Ideal.span (insert s (T : Set A)) = ⊤ :=
    eq_top_mono (Ideal.span_mono (Set.subset_insert s _)) (IsTateRing.eq_top_of_isOpen hT)
  have : IsStronglyNoetherian B := P.isStronglyNoetherian_completion T s _ hden hspan
  -- as a complete Hausdorff ring, `A⟨T/s⟩` is then noetherian
  have : IsNoetherianRing B := isNoetherianRing_of_isStronglyNoetherian <| by
    rw [IsUniformAddGroup.rightUniformSpace_eq]
    infer_instance
  exact isNaturallyComplete_iff_t2Space.2 IsTateRing.t2Space_moduleTopology

end IsStablyPseudoCoherent

end TauCeti.Huber

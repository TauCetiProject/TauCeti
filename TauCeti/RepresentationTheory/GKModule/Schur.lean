/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.InfinitesimalCharacter.Basic
public import TauCeti.RepresentationTheory.GKModule.Hom
public import TauCeti.RepresentationTheory.GKModule.Irreducible
import TauCeti.LinearAlgebra.Eigenspace.JointEigenvector.Basic

/-!
# Schur's lemma for admissible `(𝔤, K)`-modules and infinitesimal characters

Let `M` be an irreducible admissible `(𝔤, K)`-module over an algebraically closed field `k`. Every
endomorphism of `M` as a `(𝔤, K)`-module is a scalar. The proof uses admissibility in place of a
countability hypothesis: every vector is `K`-finite, so `M` contains an irreducible
`K`-subrepresentation `σ`, and `Hom_K(σ, M)` is a nonzero finite-dimensional space on which the
endomorphism acts by composition. An eigenvector `φ` for an eigenvalue `c` gives a nonzero vector
in the eigenspace of `f` for `c`, which is a `(𝔤, K)`-submodule, hence everything.

The centre `Z(U(𝔤))` of the enveloping algebra acts on `M` by endomorphisms of the Lie module
(`TauCeti.UniversalEnvelopingAlgebra.centralAction_lie`). When these also commute with `K`, which
holds when `Ad(K)` fixes `Z(U(𝔤))`, the centre acts by scalars, so an irreducible admissible
`(𝔤, K)`-module has an infinitesimal character.

## Main statements

* `TauCeti.GKModule.IsIrreducible.exists_forall_apply_eq_smul`: **Schur's lemma** for irreducible
  admissible `(𝔤, K)`-modules over an algebraically closed field.
* `TauCeti.GKModule.IsIrreducible.exists_hasInfinitesimalCharacter`: an irreducible admissible
  `(𝔤, K)`-module on which `K` commutes with the centre has an infinitesimal character.

## References

* J. Bernstein and B. Krötz, *Smooth Fréchet globalizations of Harish-Chandra modules*, Israel J.
  Math. 199 (2014), 45–111, §4.1.
-/

public section

namespace TauCeti.GKModule

open Representation _root_.TauCeti.UniversalEnvelopingAlgebra

variable {k 𝔤 K : Type*} [Field k] [LieRing 𝔤] [LieAlgebra k 𝔤] [Monoid K]
  {Ad : Representation k K 𝔤} [IsLieAction Ad] {V : Type*} [AddCommGroup V] [Module k V]
  [LieRingModule 𝔤 V] [LieModule k 𝔤 V] {M : GKModule Ad V}

/-- **Schur's lemma for admissible `(𝔤, K)`-modules.** Over an algebraically closed field, an
endomorphism of an irreducible admissible `(𝔤, K)`-module is a scalar. -/
theorem IsIrreducible.exists_forall_apply_eq_smul [IsAlgClosed k] (hM : M.IsIrreducible)
    (hadm : M.ρ.HasFiniteMultiplicities) (f : Hom M M) : ∃ c : k, ∀ v, f v = c • v := by
  have := hM.nontrivial
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  obtain ⟨σ, hσ0, hσ⟩ := exists_isIrreducible_subrepresentation_of_isGFinite (M.isGFinite v) hv
  have := (hasFiniteMultiplicities_iff _).1 hadm σ hσ
  -- `f` acts on the nonzero finite-dimensional space `Hom_K(σ, M)` by composition.
  let F := IntertwiningMap.llcomp σ.toRepresentation M.ρ M.ρ f.toIntertwiningMap
  have : Nontrivial (IntertwiningMap σ.toRepresentation M.ρ) :=
    ⟨⟨σ.subtype, 0, (Subrepresentation.subtype_eq_zero_iff σ).not.2 hσ0⟩⟩
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue F
  obtain ⟨φ, hφ⟩ := hc.exists_hasEigenvector
  obtain ⟨w, hw⟩ : ∃ w, φ w ≠ 0 := by
    by_contra! h
    exact hφ.2 (IntertwiningMap.ext (LinearMap.ext h))
  have hfφ : f (φ w) = c • φ w := by
    simpa [F, ← IntertwiningMap.comp_def] using congrArg (fun ψ : IntertwiningMap _ _ ↦ ψ w)
      (Module.End.mem_eigenspace_iff.1 hφ.1)
  -- The eigenspace of `f` for `c` is a `(𝔤, K)`-submodule containing `φ w ≠ 0`, hence everything.
  have hN : f.eigenspace c = ⊤ :=
    (IsSimpleOrder.eq_bot_or_eq_top _).resolve_left fun h ↦
      hw (GKSubmodule.mem_bot.1 (h ▸ Hom.mem_eigenspace.2 hfφ))
  exact ⟨c, fun v ↦ Hom.mem_eigenspace.1 (hN ▸ GKSubmodule.mem_top v)⟩

/-- **An irreducible admissible `(𝔤, K)`-module has an infinitesimal character** when `K` commutes
with the action of the centre `Z(U(𝔤))`, as it does when `Ad(K)` fixes `Z(U(𝔤))`. Every central
element acts by a scalar by Schur's lemma, and these scalars form an algebra character. -/
theorem IsIrreducible.exists_hasInfinitesimalCharacter [IsAlgClosed k] (hM : M.IsIrreducible)
    (hadm : M.ρ.HasFiniteMultiplicities)
    (hZ : ∀ (g : K) (z : Subalgebra.center k (UniversalEnvelopingAlgebra k 𝔤)) (v : V),
      M.ρ g (centralAction k 𝔤 V z v) = centralAction k 𝔤 V z (M.ρ g v)) :
    ∃ χ : Subalgebra.center k (UniversalEnvelopingAlgebra k 𝔤) →ₐ[k] k,
      HasInfinitesimalCharacter k 𝔤 V χ := by
  have := hM.nontrivial
  have h (z) : ∃ c : k, ∀ v, centralAction k 𝔤 V z v = c • v := hM.exists_forall_apply_eq_smul hadm
    ⟨{ centralAction k 𝔤 V z with map_lie' := centralAction_lie z _ _ }, fun g v ↦ (hZ g z v).symm⟩
  choose c hc using h
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  exact ⟨(centralAction k 𝔤 V).eigenvalueHomOfJointEigenvector c v hv
    fun z ↦ Module.End.mem_eigenspace_iff.2 (hc z v),
    hasInfinitesimalCharacter_iff.2 fun z m ↦ by simpa using hc z m⟩

end TauCeti.GKModule

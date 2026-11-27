/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.InfinitesimalCharacter.Basic
public import TauCeti.RepresentationTheory.GKModule.Irreducible

/-!
# Schur's lemma for admissible `(𝔤, K)`-modules and infinitesimal characters

Let `M` be an irreducible admissible `(𝔤, K)`-module over an algebraically closed field `k`. Every
linear endomorphism of `M` commuting with the actions of `𝔤` and of `K` is a scalar. The proof
uses admissibility in place of a countability hypothesis: every vector is `K`-finite, so `M`
contains an irreducible `K`-subrepresentation `σ`, and `Hom_K(σ, M)` is a nonzero
finite-dimensional space on which the endomorphism acts by composition. An eigenvector `φ` for an
eigenvalue `c` gives a nonzero vector in the kernel of `f - c`, which is a `(𝔤, K)`-submodule, hence
everything.

The centre `Z(U(𝔤))` of the enveloping algebra acts on `M` by endomorphisms of the Lie module
(`TauCeti.UniversalEnvelopingAlgebra.centralAction_lie`). When these also commute with `K`, which
holds when `Ad(K)` fixes `Z(U(𝔤))`, the centre acts by scalars, so an irreducible admissible
`(𝔤, K)`-module has an infinitesimal character.

## Main statements

* `TauCeti.GKModule.exists_isIrreducible_subrepresentation`: a nonzero `(𝔤, K)`-module contains an
  irreducible `K`-subrepresentation.
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
  [LieRingModule 𝔤 V] [LieModule k 𝔤 V] (M : GKModule Ad V)

/-- **A nonzero `(𝔤, K)`-module contains an irreducible `K`-subrepresentation**: a nonzero vector
is `K`-finite, so it lies in a nonzero finite-dimensional subrepresentation, which contains a
minimal nonzero one. -/
theorem exists_isIrreducible_subrepresentation [Nontrivial V] :
    ∃ σ : Subrepresentation M.ρ, σ ≠ ⊥ ∧ σ.toRepresentation.IsIrreducible := by
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  obtain ⟨W, hW, hvW⟩ := (M.ρ.isGFinite_iff_exists_subrepresentation v).1 (M.isGFinite v)
  have hW0 : W ≠ ⊥ := by
    rintro rfl
    exact hv (by simpa using hvW)
  obtain ⟨σ, -, hσ⟩ := exists_isAtom_le hW0
  exact ⟨σ, hσ.1, isIrreducible_toRepresentation_of_isAtom hσ⟩

variable {M}

/-- **Schur's lemma for admissible `(𝔤, K)`-modules.** Over an algebraically closed field, a linear
endomorphism of an irreducible admissible `(𝔤, K)`-module commuting with `𝔤` and `K` is a scalar. -/
theorem IsIrreducible.exists_forall_apply_eq_smul [IsAlgClosed k] (hM : M.IsIrreducible)
    (hadm : M.ρ.HasFiniteMultiplicities) (f : V →ₗ[k] V)
    (hlie : ∀ (x : 𝔤) (v : V), f ⁅x, v⁆ = ⁅x, f v⁆)
    (hK : ∀ (g : K) (v : V), f (M.ρ g v) = M.ρ g (f v)) :
    ∃ c : k, ∀ v, f v = c • v := by
  have := hM.nontrivial
  obtain ⟨σ, hσ0, hσ⟩ := M.exists_isIrreducible_subrepresentation
  have := (hasFiniteMultiplicities_iff _).1 hadm σ hσ
  -- `f` acts on the nonzero finite-dimensional space `Hom_K(σ, M)` by composition.
  let F := IntertwiningMap.llcomp σ.toRepresentation M.ρ M.ρ
    (f.intertwiningMap_of_isIntertwiningMap M.ρ M.ρ hK)
  have : Nontrivial (IntertwiningMap σ.toRepresentation M.ρ) :=
    ⟨⟨σ.subtype, 0, (Subrepresentation.subtype_eq_zero_iff σ).not.2 hσ0⟩⟩
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue F
  obtain ⟨φ, hφ⟩ := hc.exists_hasEigenvector
  obtain ⟨w, hw⟩ : ∃ w, φ w ≠ 0 := by
    by_contra! h
    exact hφ.2 (IntertwiningMap.ext (LinearMap.ext h))
  have hfφ : f (φ w) = c • φ w := congrArg (fun ψ : IntertwiningMap _ _ ↦ ψ w)
    (Module.End.mem_eigenspace_iff.1 hφ.1)
  -- The kernel of `f - c` is a `(𝔤, K)`-submodule containing `φ w ≠ 0`, hence everything.
  let N : GKSubmodule M :=
    { toLieSubmodule :=
        { toSubmodule := LinearMap.ker (f - c • LinearMap.id)
          lie_mem := fun {x v} hv ↦ by
            simp only [AddSubsemigroup.mem_carrier, AddSubmonoid.mem_toSubsemigroup,
              Submodule.mem_toAddSubmonoid, LinearMap.mem_ker, LinearMap.sub_apply,
              LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at hv ⊢
            rw [hlie, hv, lie_smul] }
      apply_mem := fun g v hv ↦ by
        simp only [LieSubmodule.mem_mk_iff', LinearMap.mem_ker, LinearMap.sub_apply,
          LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at hv ⊢
        rw [hK, hv, map_smul] }
  have hN : N = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top N).resolve_left fun h ↦ hw <| by
    have : φ w ∈ N := by
      change φ w ∈ LinearMap.ker (f - c • LinearMap.id)
      simp [hfφ]
    rw [h] at this
    exact GKSubmodule.mem_bot.1 this
  refine ⟨c, fun v ↦ ?_⟩
  have : v ∈ N := hN ▸ GKSubmodule.mem_top v
  change v ∈ LinearMap.ker (f - c • LinearMap.id) at this
  simpa [sub_eq_zero] using this

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
  choose c hc using fun z ↦ hM.exists_forall_apply_eq_smul hadm (centralAction k 𝔤 V z)
    (centralAction_lie z) fun g v ↦ (hZ g z v).symm
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have key {a b : k} (h : a • v = b • v) : a = b := smul_left_injective k hv h
  refine ⟨{ toFun := c
            map_one' := key (by rw [← hc, map_one, one_apply_eq_self, one_smul])
            map_mul' := fun z w ↦ key (by
              rw [← hc, map_mul, mul_apply_eq_comp, hc w, map_smul, hc z, smul_smul, mul_comm])
            map_zero' := key (by rw [← hc, map_zero, LinearMap.zero_apply, zero_smul])
            map_add' := fun z w ↦ key (by rw [← hc, map_add, LinearMap.add_apply, hc, hc, add_smul])
            commutes' := fun r ↦ key (by
              rw [← hc, AlgHom.commutes, Module.algebraMap_end_apply, Algebra.algebraMap_self,
                RingHom.id_apply]) }, ?_⟩
  exact hasInfinitesimalCharacter_iff.2 fun z m ↦ hc z m

end TauCeti.GKModule

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.GaloisSet.Relabelling
public import TauCeti.RingTheory.Etale.Galois
import TauCeti.FieldTheory.KrullTopology

/-!
# The labelled Galois sets of étale algebras

An étale algebra `A` over a field `K` has finitely many points `A →ₐ[K] SeparableClosure K`, on
which the absolute Galois group acts by postcomposition. A labelling `ℓ` of these points by
`Fin n` turns this action into a labelled Galois set, `TauCeti.GaloisSet.ofAlgebra A ℓ`.

By Grothendieck's Galois theory for a field (`TauCeti.exists_mulActionHom_algHom_bijective` and
`Algebra.Etale.algEquivEquivEquivariant`), this accounts for all labelled Galois sets up to
relabelling:

* every labelled Galois set is the Galois set of an étale algebra in the universe of `K`
  (`TauCeti.GaloisSet.exists_eq_ofAlgebra`);
* relabelling the Galois set of `A` relabels the points of `A`
  (`TauCeti.GaloisSet.smul_ofAlgebra`), and the Galois sets of `A` and `B` lie in one
  relabelling orbit exactly when `A` and `B` are isomorphic
  (`TauCeti.GaloisSet.ofAlgebra_mem_orbit_ofAlgebra_iff`);
* the relabellings fixing the Galois set of `A` correspond to the automorphisms of `A`
  (`TauCeti.GaloisSet.natCard_stabilizer_ofAlgebra`).

So the relabelling orbits of labelled Galois sets of size `n` are the isomorphism classes of étale
algebras of degree `n`, and the class of `A` contains `n! / #Aut_K(A)` labelled Galois sets. This is
how a sum over labelled Galois sets divided by `n!` becomes a sum over étale algebras weighted by
the reciprocals of their automorphism counts, as in Bhargava's mass formula.

## References

* M. Bhargava, *Mass formulae for extensions of local fields, and conjectures on the density
  of number field discriminants*, IMRN 2007, rnm052, §2.
* K. S. Kedlaya, *Mass formulas for local Galois representations*, IMRN 2007, rnm021.
-/

public section

noncomputable section

namespace TauCeti.GaloisSet

universe u

variable {K : Type u} [Field K] {n : ℕ}

section ofAlgebra

variable (A : Type*) [CommRing A] [Algebra K A] [Algebra.Etale K A]

/-- The labelled Galois set of an étale algebra `A`: the action of the absolute Galois group on
the points `A →ₐ[K] SeparableClosure K` by postcomposition, transported to `Fin n` along a
labelling `ℓ` of the points. Its kernel is open because the stabilizer of each of the finitely many
points is open (`AlgHom.stabilizer_isOpen`). -/
def ofAlgebra (ℓ : Fin n ≃ (A →ₐ[K] SeparableClosure K)) : GaloisSet K n :=
  ⟨ℓ.symm.permCongrHom.toMonoidHom.comp (MulAction.toPermHom _ _), by
    have : Module.Finite K A := Algebra.FormallyUnramified.finite_of_free K A
    rw [MonoidHom.ker_comp_of_injective _ _ ℓ.symm.permCongrHom.injective,
      ker_toPermHom_eq_iInf_stabilizer, Subgroup.coe_iInf]
    exact isOpen_iInter_of_finite fun φ ↦ φ.stabilizer_isOpen⟩

/-- The Galois set of `A` moves the label of a point `φ` to the label of `σ • φ`. -/
@[simp]
theorem ofAlgebra_val_apply (ℓ : Fin n ≃ (A →ₐ[K] SeparableClosure K))
    (σ : Gal(SeparableClosure K/K)) (i : Fin n) :
    (ofAlgebra A ℓ).val σ i = ℓ.symm (σ • ℓ i) :=
  (rfl)

/-- Relabelling the Galois set of `A` amounts to relabelling the points of `A`. -/
@[simp]
theorem smul_ofAlgebra (e : Equiv.Perm (Fin n)) (ℓ : Fin n ≃ (A →ₐ[K] SeparableClosure K)) :
    e • ofAlgebra A ℓ = ofAlgebra A (e.symm.trans ℓ) := by
  ext σ i
  simp

/-- **Every labelled Galois set is the Galois set of an étale algebra**, which may be taken in the
universe of `K`. -/
theorem exists_eq_ofAlgebra (ρ : GaloisSet K n) :
    ∃ (A : Type u) (_ : CommRing A) (_ : Algebra K A) (_ : Algebra.Etale K A)
      (ℓ : Fin n ≃ (A →ₐ[K] SeparableClosure K)), ρ = ofAlgebra A ℓ := by
  let := ρ.mulAction
  obtain ⟨A, _, _, _, _, f, hf⟩ :=
    exists_mulActionHom_algHom_bijective (Ω := SeparableClosure K) ρ.isOpen_stabilizer
  refine ⟨A, inferInstance, inferInstance, inferInstance, Equiv.ofBijective f hf, ext fun σ i ↦ ?_⟩
  rw [ofAlgebra_val_apply, Equiv.eq_symm_apply]
  exact map_smul f σ i

variable {A} {B : Type*} [CommRing B] [Algebra K B] [Algebra.Etale K B]

/-- The relabellings carrying the Galois set of `A` to that of `B` correspond to the isomorphisms
`A ≃ₐ[K] B`: conjugated by the labellings, such a relabelling is an equivariant bijection of
points, and these are the isomorphisms (`Algebra.Etale.algEquivEquivEquivariant`). -/
private def smulEqEquivAlgEquiv (ℓ : Fin n ≃ (A →ₐ[K] SeparableClosure K))
    (ℓ' : Fin n ≃ (B →ₐ[K] SeparableClosure K)) :
    {e : Equiv.Perm (Fin n) // e • ofAlgebra A ℓ = ofAlgebra B ℓ'} ≃ (A ≃ₐ[K] B) :=
  ((Equiv.subtypeEquivRight fun e ↦ smul_eq_iff _ _ e).trans <|
    (ℓ.equivCongr ℓ').subtypeEquiv fun e ↦ by
      simp only [ofAlgebra_val_apply, Equiv.equivCongr_apply_apply]
      refine ⟨fun h σ φ ↦ ?_, fun h σ i ↦ ?_⟩
      · simpa [Equiv.eq_symm_apply] using h σ (ℓ.symm φ)
      · simpa [← Equiv.eq_symm_apply] using h σ (ℓ i)).trans
    (Algebra.Etale.algEquivEquivEquivariant (SeparableClosure K)).symm

/-- **The Galois sets of two étale algebras lie in one relabelling orbit exactly when the algebras
are isomorphic.** -/
theorem ofAlgebra_mem_orbit_ofAlgebra_iff (ℓ : Fin n ≃ (A →ₐ[K] SeparableClosure K))
    (ℓ' : Fin n ≃ (B →ₐ[K] SeparableClosure K)) :
    ofAlgebra B ℓ' ∈ MulAction.orbit (Equiv.Perm (Fin n)) (ofAlgebra A ℓ) ↔
      Nonempty (A ≃ₐ[K] B) := by
  rw [MulAction.mem_orbit_iff, ← (smulEqEquivAlgEquiv ℓ ℓ').nonempty_congr]
  exact ⟨fun ⟨e, he⟩ ↦ ⟨⟨e, he⟩⟩, fun ⟨⟨e, he⟩⟩ ↦ ⟨e, he⟩⟩

/-- **The relabellings fixing the Galois set of an étale algebra are its automorphisms**, in
number. -/
theorem natCard_stabilizer_ofAlgebra (ℓ : Fin n ≃ (A →ₐ[K] SeparableClosure K)) :
    Nat.card (MulAction.stabilizer (Equiv.Perm (Fin n)) (ofAlgebra A ℓ)) =
      Nat.card (A ≃ₐ[K] A) :=
  Nat.card_congr <| (Equiv.subtypeEquivRight fun _ ↦ MulAction.mem_stabilizer_iff).trans
    (smulEqEquivAlgEquiv ℓ ℓ)

end ofAlgebra

end TauCeti.GaloisSet

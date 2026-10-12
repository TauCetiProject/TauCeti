/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Selmer

/-!
# Independence of the embeddings of separable closures

For a field extension `L/K`, restriction on the first Galois cohomology of a Weierstrass curve
is independent of the embedding `Kˢ → Lˢ`. Two embeddings differ by an automorphism of `Kˢ`;
the resulting conjugation of the group map and action on coefficients induce the same
cohomology map. Both `pointRes` and `torsionRes` are therefore independent of this choice.
Consequently, the Shafarevich–Tate and Selmer subgroups defined from any family of extensions
are equal for any two families of embeddings.

The coordinate maps themselves do depend on the embedding: the equations
`pointCoeffBaseChange_comp` and `torsionCoeffBaseChange_comp` describe their transformation.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], X.4.
* J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Chapter I, §5.
-/

public section

noncomputable section

namespace WeierstrassCurve

open TauCeti TauCeti.ContCohomology

variable {K : Type*} [Field K] {L : Type*} [Field L] [Algebra K L]
  (W : WeierstrassCurve K) (τ : SeparableClosure K →ₐ[K] SeparableClosure L)

/-- Restriction on `H¹(G_K, E(Kˢ))` is independent of the embedding of separable closures. -/
theorem pointRes_eq_pointRes (τ' : SeparableClosure K →ₐ[K] SeparableClosure L) :
    W.pointRes τ = W.pointRes τ' := by
  obtain ⟨σ, rfl⟩ := τ.exists_comp_eq_of_normal τ'
  rw [pointRes_eq_explicitMap1, pointRes_eq_explicitMap1]
  exact (explicitMap1_eq_of_conj _ _ _ _ _ _ _ _ _ _ _ _ σ
    (absoluteGaloisGroupMap_comp τ σ) (W.pointCoeffBaseChange_comp τ σ)).symm

/-- Restriction on `H¹(G_K, E(Kˢ)[m])` is independent of the embedding of separable closures,
for every natural number `m`. -/
theorem torsionRes_eq_torsionRes (τ' : SeparableClosure K →ₐ[K] SeparableClosure L) (m : ℕ) :
    W.torsionRes τ m = W.torsionRes τ' m := by
  obtain ⟨σ, rfl⟩ := τ.exists_comp_eq_of_normal τ'
  rw [torsionRes_eq_explicitMap1, torsionRes_eq_explicitMap1]
  exact (explicitMap1_eq_of_conj _ _ _ _ _ _ _ _ _ _ _ _ σ
    (absoluteGaloisGroupMap_comp τ σ) (W.torsionCoeffBaseChange_comp τ σ m)).symm

section Families

variable {ι : Type*} {F : ι → Type*} [∀ i, Field (F i)] [∀ i, Algebra K (F i)]
  (τ τ' : ∀ i, SeparableClosure K →ₐ[K] SeparableClosure (F i))

/-- The Shafarevich–Tate subgroup relative to a family of field extensions is independent
of all choices of embeddings of separable closures. -/
theorem shafarevichTateGroup_eq_shafarevichTateGroup :
    W.shafarevichTateGroup τ = W.shafarevichTateGroup τ' := by
  ext c
  simp only [mem_shafarevichTateGroup_iff, W.pointRes_eq_pointRes (τ _) (τ' _)]

/-- The Selmer subgroup relative to a family of field extensions is independent of all
choices of embeddings of separable closures, for every natural number `m`. -/
theorem selmerGroup_eq_selmerGroup (m : ℕ) : W.selmerGroup τ m = W.selmerGroup τ' m := by
  ext c
  simp only [mem_selmerGroup_iff, W.shafarevichTateGroup_eq_shafarevichTateGroup τ τ']

end Families

end WeierstrassCurve
